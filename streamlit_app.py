# streamlit_app.py
# -----------------------------------------------------------
# Contrôle d'accès (RBAC / DAC / China-Wall) – Streamlit
# Affichage plein écran / pleine largeur + rendu PyVis en HTML
# -----------------------------------------------------------

import io
import pandas as pd
import networkx as nx
import streamlit as st
from pyvis.network import Network
from streamlit.components.v1 import html as st_html

# ===================== CONFIG UI ===========================
st.set_page_config(page_title="Contrôle d'accès – RBAC / DAC / China-Wall", layout="wide")

# ===================== ÉTAT GLOBAL =========================
def init_state():
    if "global_data" not in st.session_state:
        st.session_state.global_data = pd.DataFrame(
            columns=["Source", "Permission", "Target", "Role", "Heritage"]
        )
    defaults = {
        "roles_definis": set(),
        "role_permissions": {},     # {role: set((perm, obj))}
        "subject_roles": {},        # {subject: set(roles)}
        "sujets_definis": set(),
        "objets_definis": set(),
        "interdictions_globales": [],
        "interdictions_entites": {},
        "history": [],
    }
    for k, v in defaults.items():
        if k not in st.session_state:
            st.session_state[k] = v

init_state()

# ================= ALGORITHMES (Tarjan & co) ================
def tarjan(V, adj):
    index = [0]
    stack = []
    indices = {v: -1 for v in V}
    lowlink = {v: -1 for v in V}
    on_stack = {v: False for v in V}
    scc, component_map = [], {}

    def strongconnect(v):
        indices[v] = index[0]
        lowlink[v] = index[0]
        index[0] += 1
        stack.append(v)
        on_stack[v] = True
        for w in adj.get(v, []):
            if indices.get(w, -1) == -1:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif on_stack.get(w, False):
                lowlink[v] = min(lowlink[v], indices[w])
        if lowlink[v] == indices[v]:
            comp = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                comp.append(w)
                if w == v:
                    break
            scc.append(comp)
            for node in comp:
                component_map[node] = comp

    for v in V:
        if indices[v] == -1:
            strongconnect(v)
    return scc, component_map

def propagate_labels(components, adj, component_map):
    labels = {frozenset(comp): set(comp) for comp in components}
    def dfs(node, visited):
        if node in visited: return
        visited.add(node)
        for neighbor in adj.get(node, []):
            if neighbor in component_map:
                neighbor_comp = frozenset(component_map[neighbor])
                current_comp = frozenset(component_map[node])
                labels[neighbor_comp].update(labels[current_comp])
                dfs(neighbor, visited)
    for comp in components:
        for node in comp:
            dfs(node, set())
    return [labels[frozenset(comp)] for comp in components]

def simplify_relations(labels):
    reduced = nx.DiGraph()
    label_map = {i: label_set for i, label_set in enumerate(labels)}
    for i, s1 in enumerate(labels):
        for j, s2 in enumerate(labels):
            if i != j and s1.issubset(s2):
                reduced.add_edge(i, j)
    # suppression des arêtes transitives
    transitive_edges = set()
    for i in range(len(labels)):
        for j in range(len(labels)):
            if i != j and reduced.has_edge(i, j):
                for path in nx.all_simple_paths(reduced, i, j):
                    if len(path) > 2:
                        transitive_edges.add((i, j))
    for e in transitive_edges:
        reduced.remove_edge(*e)
    return [(label_map[u], label_map[v]) for u, v in reduced.edges()]

# =============== CONSTRUCTION DU GRAPHE =====================
def apply_permissions(df: pd.DataFrame):
    """
    Adjacence à partir des permissions :
    - R : Target -> Source  (X lit Y => Y->X)
    - W : Source -> Target  (X écrit Y => X->Y)
    (Owner est ignoré dans le graphe)
    """
    adj = {}
    def add_edge(a, b):
        if pd.isna(a) or pd.isna(b): return
        adj.setdefault(a, [])
        adj.setdefault(b, [])
        adj[a].append(b)

    for _, row in df.iterrows():
        s, p, t = row.get("Source"), row.get("Permission"), row.get("Target")
        if pd.isna(p) or pd.isna(t):  # pas de permission => rien
            continue
        for perm in str(p).split(","):
            perm = perm.strip()
            if perm == "R":
                add_edge(t, s)  # Y -> X
            elif perm == "W":
                add_edge(s, t)  # X -> Y

    for k in list(adj.keys()):
        adj[k] = list(sorted(set(adj[k])))
    return adj

# =============== TABLES (Streamlit) ========================
def display_entities_table(components, labels):
    data = {
        "Entities": [", ".join(sorted(c)) for c in components],
        "Their labels": ["{" + ", ".join(sorted(lbl | set(comp))) + "}" for comp, lbl in zip(components, labels)],
    }
    df = pd.DataFrame(data)
    st.markdown("### Table des entités et étiquettes")
    st.dataframe(df, use_container_width=True)

def display_role_table_streamlit(df: pd.DataFrame):
    if "Role" not in df.columns: return
    roles = sorted({r for r in df["Role"].dropna().unique() if str(r).strip()})
    objects = sorted({t for t in df["Target"].dropna().unique() if str(t).strip()})
    if not roles or not objects: return
    role_perms_map = {r: {o: "" for o in objects} for r in roles}
    for _, row in df.iterrows():
        role, obj, perm = row.get("Role"), row.get("Target"), row.get("Permission")
        if pd.notna(role) and pd.notna(obj) and pd.notna(perm):
            current = set(role_perms_map[role][obj].split(",")) if role_perms_map[role][obj] else set()
            for p in str(perm).split(","):
                p = p.strip()
                if p: current.add(p)
            role_perms_map[role][obj] = ",".join(sorted(current))
    df_role = pd.DataFrame([{"Role": r, **role_perms_map[r]} for r in roles], columns=["Role"] + objects)
    st.markdown("### Table des rôles et permissions")
    st.dataframe(df_role, use_container_width=True)

# =============== PYVIS (Streamlit) =========================
def draw_combined_graph(components_1, adj_1, labels_1,
                        components_2, labels_2, simplified_edges_2, role_data):

    # ── IMPORTANT : on ne dessine QUE les nœuds impliqués dans R/W ──
    nodes_with_edges = set(adj_1.keys())
    for lst in adj_1.values():
        nodes_with_edges.update(lst)

    net = Network(notebook=False, height='1000px', width='100%', directed=True, cdn_resources='in_line')

    sorted_components_1 = sorted(components_1, key=len, reverse=True)
    sorted_components_2 = sorted(components_2, key=len, reverse=True)

    x_gap, y_gap = 300, 250
    current_y_subject = 0
    current_y_object = 0
    node_indices = {}
    G1 = nx.DiGraph()

    role_to_subject = {subject: role_data.get(subject, "None") for subject in nodes_with_edges}

    # colonne gauche : sujets ; colonne droite : objets
    for component, label in zip(sorted_components_1, labels_1):
        # on filtre le composant aux nœuds actifs
        comp_active = [n for n in component if n in nodes_with_edges]
        if not comp_active:
            continue

        subjects = [s for s in comp_active if str(s).startswith("S")]
        objects  = [o for o in comp_active if str(o).startswith("O")]

        for subj in subjects:
            roles = role_to_subject.get(subj, "None")
            combined_labels = '{' + ', '.join(sorted(label | {subj})) + '}'
            text = f'{subj}({roles}):\n{combined_labels}'
            net.add_node(subj, label=text, shape='ellipse', x=-x_gap, y=-current_y_subject * y_gap)
            node_indices[subj] = subj
            current_y_subject += 1

        for obj in objects:
            combined_labels = '{' + ', '.join(sorted(label | {obj})) + '}'
            net.add_node(obj, label=f'{obj}:\n{combined_labels}', shape='box', x=x_gap, y=-current_y_object * y_gap)
            node_indices[obj] = obj
            current_y_object += 1

    # Arêtes (uniquement sur le graphe R/W)
    for src, dest_list in adj_1.items():
        for dest in dest_list:
            if src in node_indices and dest in node_indices:
                G1.add_edge(src, dest)

    if nx.is_directed_acyclic_graph(G1):
        G1 = nx.transitive_reduction(G1)

    for src, dest in G1.edges():
        net.add_edge(src, dest, arrows="to")

    # Boîtes classes d'équivalence (sur nœuds actifs uniquement)
    positions = {0: (-x_gap, 450), 1: (0, 0), 2: (x_gap, 800)}
    offset_y = y_gap
    base_idx = len(net.get_nodes())

    idx_map = []
    for i, (component, label) in enumerate(zip(sorted_components_2, labels_2)):
        comp_active = [n for n in component if n in nodes_with_edges]
        if not comp_active:
            idx_map.append(None)
            continue
        entity_name = ', '.join(comp_active)
        combined_labels = '{' + ', '.join(sorted((label | set(comp_active)))) + '}'
        text = f'| {entity_name}: {combined_labels} |'
        col_index = i % 3
        row_index = i // 3
        x, y = positions[col_index]
        y += row_index * offset_y
        net.add_node(base_idx + i, label=text, shape='box', x=x, y=y, width_constraint=300, height_constraint=100)
        idx_map.append(base_idx + i)

    def find_idx(target_set):
        # retourne l'index visuel seulement si ce set contient au moins un nœud actif
        for i, lbl in enumerate(labels_2):
            if lbl == target_set:
                return idx_map[i]
        return None

    for src_set, dst_set in simplified_edges_2:
        si, di = find_idx(src_set), find_idx(dst_set)
        if si is not None and di is not None:
            net.add_edge(si, di, arrows="to")

    net.set_options("""
    var options = {
      "nodes": {"font": {"size": 50}, "shapeProperties": {"borderRadius": 5}, "size": 40, "fixed": {"x": false, "y": false}},
      "edges": {"width": 4, "arrows": {"to": {"enabled": true, "scaleFactor": 1.5}}, "length": 150, "smooth": {"enabled": false}},
      "physics": {"enabled": false},
      "interaction": {"dragNodes": true, "dragView": true, "zoomView": true}
    }
    """)
    st_html(net.generate_html(), height=1000, width=1800, scrolling=True)

# =============== RBAC : propagation depuis Excel ===========
def propagate_rbac_from_excel(df: pd.DataFrame) -> pd.DataFrame:
    df = df.copy()
    if "Role" not in df.columns: df["Role"] = None
    if "Heritage" not in df.columns: df["Heritage"] = None

    role_perms, subject_roles = {}, {}
    for _, row in df.iterrows():
        role = str(row.get("Role", "")).strip()
        subj = str(row.get("Source", "")).strip()
        perm = str(row.get("Permission", "")).strip()
        obj  = str(row.get("Target", "")).strip()
        if role:
            subject_roles.setdefault(subj, set()).add(role)
        if role and perm and obj:
            role_perms.setdefault(role, set()).add((perm, obj))

    new_rows = []
    for subj, roles in subject_roles.items():
        if not subj: continue
        for r in roles:
            for perm, obj in role_perms.get(r, set()):
                mask = ((df["Source"] == subj) & (df["Permission"] == perm) & (df["Target"] == obj))
                if not mask.any():
                    new_rows.append({"Source": subj, "Permission": perm, "Target": obj, "Role": r, "Heritage": "Role"})
    if new_rows:
        df = pd.concat([df, pd.DataFrame(new_rows)], ignore_index=True)
    return df

# =============== CHINA-WALL (vérif) ========================
def violates_china_wall(labels):
    for comp in labels:
        for interdit in st.session_state.interdictions_globales:
            if set(interdit).issubset(comp):
                return True, f"Combinaison globale interdite: {interdit}"
        for ent, combos in st.session_state.interdictions_entites.items():
            if ent in comp:
                for interdit in combos:
                    if set(interdit).issubset(comp):
                        return True, f"Combinaison interdite pour {ent}: {interdit}"
    return False, ""

# =============== CHARGEMENT ENTITÉS (E1,E2) ================
def load_entities_excel(file_bytes: bytes) -> pd.DataFrame:
    df_raw = pd.read_excel(io.BytesIO(file_bytes))
    cols = {c.strip().lower(): c for c in df_raw.columns}
    if not {"entity1", "entity2"} <= set(cols.keys()):
        raise ValueError("Le fichier 'entités' doit contenir les colonnes Entity1 et Entity2.")
    col_e1, col_e2 = cols["entity1"], cols["entity2"]
    rows = []
    for _, row in df_raw.iterrows():
        e1 = str(row[col_e1]).strip()
        e2 = str(row[col_e2]).strip()
        if e1 and e1.lower() != "nan" and e2 and e2.lower() != "nan":
            rows.append({"Source": e2, "Permission": "R", "Target": e1, "Role": None, "Heritage": None})
    if not rows:
        raise ValueError("Aucune paire valide (Entity1, Entity2) trouvée.")
    return pd.DataFrame(rows, columns=["Source", "Permission", "Target", "Role", "Heritage"])

# =============== VISUALISATION COMPLÈTE ====================
def process_data_display(df: pd.DataFrame):
    if df is None or df.empty:
        st.info("Aucune donnée à afficher.")
        return

    df_expanded = propagate_rbac_from_excel(df)
    adj = apply_permissions(df_expanded)
    V = sorted(set(adj.keys()) | {v for lst in adj.values() for v in lst})
    scc, cmap = tarjan(V, adj)
    labels = propagate_labels(scc, adj, cmap)

    violated, msg = violates_china_wall(labels)
    if violated:
        st.error(f"⛔ CHINA-WALL: {msg}")
        return

    col1, col2 = st.columns([1, 1], gap="large")
    with col1:
        display_entities_table(scc, labels)
    with col2:
        display_role_table_streamlit(df_expanded)

    st.markdown("---")
    simplified_edges = simplify_relations(labels)
    draw_combined_graph(
        scc, adj, labels,
        scc, labels, simplified_edges,
        role_data=df_expanded.set_index("Source")["Role"].to_dict() if "Role" in df_expanded.columns else {}
    )

# =============== TERMINAL : COMMANDES ======================
def apply_prompt(global_data: pd.DataFrame, prompt: str):
    def ensure_cols(df):
        for c in ["Source", "Permission", "Target", "Role", "Heritage"]:
            if c not in df.columns: df[c] = None
        return df

    def ok(x): return x
    def err(x): return x

    df = ensure_cols(global_data.copy())
    parts = prompt.strip().split()
    if not parts:
        return df, "💬 Empty command"

    cmd, args = parts[0], parts[1:]
    out = [f"💬 Command executed: C:\\> {' '.join(parts)}"]

    # Reset
    if cmd == "Reset":
        st.session_state.global_data = pd.DataFrame(columns=["Source","Permission","Target","Role","Heritage"])
        st.session_state.roles_definis.clear()
        st.session_state.role_permissions.clear()
        st.session_state.subject_roles.clear()
        st.session_state.sujets_definis.clear()
        st.session_state.objets_definis.clear()
        st.session_state.interdictions_globales.clear()
        st.session_state.interdictions_entites.clear()
        return st.session_state.global_data, "\n".join(out + [ok("✅ Reset done.")])

    # RBAC: simple AddObj (sans propriétaire)
    if cmd == "AddObj" and len(args) == 1:
        obj = args[0]
        if obj in st.session_state.objets_definis:
            return df, "\n".join(out + [ok(f"ℹ️ The object '{obj}' already exists.")])
        st.session_state.objets_definis.add(obj)
        df = pd.concat([df, pd.DataFrame([{"Source": None, "Permission": None, "Target": obj, "Role": None, "Heritage": None}])], ignore_index=True)
        return df, "\n".join(out + [ok(f"✅ Object '{obj}' created.")])

    # RBAC: rôles / sujets / permissions
    if cmd == "AddRole":
        if len(args) != 1:
            return df, "\n".join(out + ["❌ Usage: AddRole R1"])
        role = args[0]
        if role in st.session_state.roles_definis:
            return df, "\n".join(out + [ok(f"ℹ️ Role '{role}' already exists.")])
        st.session_state.roles_definis.add(role)
        st.session_state.role_permissions.setdefault(role, set())
        return df, "\n".join(out + [ok(f"✅ Role '{role}' added.")])

    if cmd == "AddSub":
        if len(args) < 1:
            return df, "\n".join(out + ["❌ Usage: AddSub S1 [R1]"])
        subject = args[0]
        role = args[1] if len(args) > 1 else None
        if subject in st.session_state.sujets_definis:
            return df, "\n".join(out + [ok(f"ℹ️ The Subject '{subject}' already exists.")])
        if role and role not in st.session_state.roles_definis:
            return df, "\n".join(out + [err(f"⛔ Error: Role '{role}' does not exist.")])
        st.session_state.sujets_definis.add(subject)
        st.session_state.subject_roles.setdefault(subject, set())
        if role:
            st.session_state.subject_roles[subject].add(role)
        df = pd.concat([df, pd.DataFrame([{"Source": subject, "Permission": None, "Target": None, "Role": role, "Heritage": None}])], ignore_index=True)
        if role:
            for (perm, obj) in st.session_state.role_permissions.get(role, set()):
                mask = (df["Source"] == subject) & (df["Permission"] == perm) & (df["Target"] == obj) & (df["Role"] == role)
                if not mask.any():
                    df = pd.concat([df, pd.DataFrame([{"Source": subject, "Permission": perm, "Target": obj, "Role": role, "Heritage": "Role"}])], ignore_index=True)
        return df, "\n".join(out + [ok(f"✅ Subject '{subject}' added" + (f" with role '{role}'" if role else ""))])

    if cmd == "GrantPermission":
        if len(args) != 3:
            return df, "\n".join(out + ["❌ Usage: GrantPermission R1 R O1"])
        role, perm, obj = args
        if role not in st.session_state.roles_definis:
            return df, "\n".join(out + [err(f"❌ Role '{role}' is not defined.")])
        if obj not in st.session_state.objets_definis:
            return df, "\n".join(out + [err(f"❌ Object '{obj}' does not exist. Use AddObj first.")])
        st.session_state.role_permissions.setdefault(role, set()).add((perm, obj))
        for subj, roles in st.session_state.subject_roles.items():
            if role in roles:
                mask = ((df["Source"] == subj) & (df["Permission"] == perm) & (df["Target"] == obj) & (df["Role"] == role))
                if not mask.any():
                    df = pd.concat([df, pd.DataFrame([{"Source": subj, "Permission": perm, "Target": obj, "Role": role, "Heritage": "Role"}])], ignore_index=True)
        return df, "\n".join(out + [ok(f"✅ Permission '{perm}' on '{obj}' granted to role '{role}' and propagated.")])

    # DAC: création d'objet avec propriétaire (Owner) – PAS de lecture auto
    if len(parts) >= 3 and parts[1] == "AddObj":
        owner, obj = parts[0], parts[2]
        if owner not in st.session_state.sujets_definis:
            return df, "\n".join(out + [err(f"⛔ Error: Subject '{owner}' does not exist. Use AddSub first.")])
        if obj in st.session_state.objets_definis:
            return df, "\n".join(out + [ok(f"ℹ️ The object '{obj}' already exists.")])
        st.session_state.objets_definis.add(obj)
        entry_owner = {"Source": owner, "Permission": "Owner", "Target": obj, "Role": None, "Heritage": None}
        df = pd.concat([df, pd.DataFrame([entry_owner], columns=df.columns)], ignore_index=True)
        # sécurité : aucune lecture implicite du propriétaire
        df = df[~((df["Source"] == owner) & (df["Target"] == obj) & (df["Permission"] == "R"))]
        return df, "\n".join(out + [ok(f"✅ Object '{obj}' created with owner '{owner}' (no read right).")])

    # DAC: Grant (seul le propriétaire peut accorder)
    if len(parts) >= 5 and parts[1] == "Grant":
        owner, _, subject, obj, perm = parts[:5]
        if owner not in st.session_state.sujets_definis:
            return df, "\n".join(out + [err(f"⛔ Error: Subject '{owner}' does not exist.")])
        if subject not in st.session_state.sujets_definis:
            return df, "\n".join(out + [err(f"⛔ Error: Target subject '{subject}' does not exist.")])
        if obj not in st.session_state.objets_definis:
            return df, "\n".join(out + [err(f"⛔ Error: Object '{obj}' does not exist.")])
        is_owner = ((df["Source"] == owner) & (df["Target"] == obj) & (df["Permission"] == "Owner")).any()
        if not is_owner:
            return df, "\n".join(out + [err(f"⛔ Error: '{owner}' is not the owner of '{obj}'.")])
        new_entry = {"Source": subject, "Permission": perm, "Target": obj, "Role": None, "Heritage": None}
        df = pd.concat([df, pd.DataFrame([new_entry], columns=df.columns)], ignore_index=True)
        return df, "\n".join(out + [ok(f"✅ Permission '{perm}' granted to '{subject}' on '{obj}' by '{owner}'.")])

    # China-Wall
    if cmd == "Never":
        if "for" in args:
            i = args.index("for")
            etiquettes = [e.strip("{} ,") for e in args[:i]]
            entites = [e.strip("{} ,") for e in args[i+1:]]
            for ent in entites:
                st.session_state.interdictions_entites.setdefault(ent, []).append(etiquettes)
            return df, "\n".join(out + [ok(f"🚧 Forbidden combination {etiquettes} for entities: {entites}")])
        else:
            etiquettes = [e.strip("{} ,") for e in args]
            st.session_state.interdictions_globales.append(etiquettes)
            return df, "\n".join(out + [ok(f"🚧 Globally forbidden combination: {etiquettes}")])

    if cmd == "AddCh":
        if len(args) == 2:
            source, target = args
            temp = pd.concat([df, pd.DataFrame([{"Source": source, "Permission": "R", "Target": target, "Role": None, "Heritage": None}])], ignore_index=True)
        elif len(args) >= 3:
            source, permission, target = args[:3]
            role = args[3] if len(args) > 3 else None
            temp = pd.concat([df, pd.DataFrame([{"Source": source, "Permission": permission, "Target": target, "Role": role, "Heritage": None}])], ignore_index=True)
        else:
            return df, "\n".join(out + ["❌ Usage: AddCh E1 E2  |  AddCh S1 R O1 [Role]"])

        # vérif China-Wall
        adj = apply_permissions(temp)
        V = sorted(set(adj.keys()) | {v for lst in adj.values() for v in lst})
        scc, cmap = tarjan(V, adj)
        labels = propagate_labels(scc, adj, cmap)
        for comp in labels:
            for interdit in st.session_state.interdictions_globales:
                if set(interdit).issubset(comp):
                    return df, "\n".join(out + [f"⛔ CHINA WALL ERROR: Global restriction violated for {interdit}"])
            for ent, combos in st.session_state.interdictions_entites.items():
                if ent in comp:
                    for interdit in combos:
                        if set(interdit).issubset(comp):
                            return df, "\n".join(out + [f"⛔ CHINA WALL ERROR: Restriction violated for {ent}: {interdit}"])
        df = temp
        if len(args) == 2:
            return df, "\n".join(out + [ok(f"✅ Channel added: {args[0]} --R--> {args[1]}")])
        else:
            return df, "\n".join(out + [ok(f"✅ Channel added: {source} --{permission}/{role}--> {target}")])

    if cmd == "RemoveCh":
        if len(args) == 3:
            source, permission, target = args
            before = len(df)
            df = df[~((df["Source"] == source) & (df["Permission"] == permission) & (df["Target"] == target))]
            removed = before - len(df)
            if removed == 0:
                return df, "\n".join(out + [ok(f"⚠️ No channel found matching '{source} {permission} {target}'.")])
            return df, "\n".join(out + [ok(f"🗑️ Channel removed: {source} --{permission}--> {target}")])
        elif len(args) == 2:
            source, target = args
            before = len(df)
            df = df[~((df["Source"] == source) & (df["Target"] == target))]
            removed = before - len(df)
            if removed == 0:
                return df, "\n".join(out + [ok(f"⚠️ No channel found between '{source}' and '{target}'.")])
            return df, "\n".join(out + [ok(f"🗑️ All channels removed between '{source}' and '{target}'.")])
        else:
            return df, "\n".join(out + ["❌ Usage: RemoveCh Source [Permission] Target"])

    if cmd == "show":
        process_data_display(df)
        return df, "\n".join(out + ["🚀 Génération des graphes…"])

    return df, "\n".join(out + ["❌ Unknown command."])

# ======================= UI / CALLBACK =====================
def _run_command_callback():
    cmd = st.session_state.get("cmd_input", "").strip()
    if not cmd:
        return
    st.session_state.global_data, message = apply_prompt(st.session_state.global_data, cmd)
    st.session_state.history.append(f"C:\\> {cmd}\n{message}")
    st.session_state.cmd_input = ""
    st.rerun()  # régénère tout (graphes inclus)

def main():
    st.title("🔐 Contrôle d'accès – RBAC / DAC / China-Wall")

    tabs = st.tabs(["📂 Fichier Excel", "⌨️ Terminal de commandes"])

    # ------- Onglet Excel -------
    with tabs[0]:
        st.write("Vous pouvez charger soit un fichier **RBAC** (colonnes: Source, Permission, Target, Role), "
                 "soit un fichier **Entités** (colonnes: Entity1, Entity2).")
        up = st.file_uploader("Importer un fichier Excel", type=["xlsx"])
        if up:
            try:
                content = up.getvalue()
                probe = pd.read_excel(io.BytesIO(content))
                cols_lower = {c.strip().lower() for c in probe.columns}
                if {"entity1", "entity2"} <= cols_lower:
                    df = load_entities_excel(content)
                else:
                    df = pd.read_excel(io.BytesIO(content))
                    required = {"Source", "Permission", "Target"}
                    missing = required - set(df.columns)
                    if missing:
                        raise ValueError(f"Colonnes manquantes: {missing}")
                    if "Role" not in df.columns: df["Role"] = None
                    if "Heritage" not in df.columns: df["Heritage"] = None
                st.session_state.global_data = df
                st.success("✅ Fichier chargé.")
                with st.expander("Voir les données chargées"):
                    st.dataframe(df, use_container_width=True)
                st.markdown("---")
                process_data_display(df)
            except Exception as e:
                st.error(f"Erreur de lecture du fichier: {e}")

    # ------- Onglet Terminal -------
    with tabs[1]:
        st.markdown(
            "Tape une commande puis **Entrée** (ex: `AddObj O1`, `AddRole R1`, `GrantPermission R1 R O1`, "
            "`AddSub S1 R1`, `S2 AddObj O2`, `S2 Grant S3 O2 R`, `AddCh E1 E2`, "
            "`Never {A,B} for E1`, `show`, `Reset` …)"
        )
        st.text_input("C:\\>", key="cmd_input", placeholder="Ex: AddSub S1 R1", on_change=_run_command_callback)
        st.text_area("Historique", "\n\n".join(st.session_state.history), height=340)

        if not st.session_state.global_data.empty:
            st.markdown("---")
            st.subheader("Graphes (issus des commandes)")
            process_data_display(st.session_state.global_data)

if __name__ == "__main__":
    main()
