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
def apply_permissions(df_effective: pd.DataFrame):
    """
    Construit l'adjacence **uniquement** depuis les lignes R/W.
    Aucune prise en compte de Owner/None.
    """
    adj = {}

    def add_edge(a, b):
        if pd.isna(a) or pd.isna(b):
            return
        adj.setdefault(a, [])
        adj.setdefault(b, [])
        adj[a].append(b)

    # ⚠️ on ne lit QUE les lignes R et W
    for _, row in df_effective.iterrows():
        s, p, t = row.get("Source"), row.get("Permission"), row.get("Target")
        if p == "R":
            add_edge(t, s)  # Y -> X (lecture)
        elif p == "W":
            add_edge(s, t)  # X -> Y (écriture)

    # dédoublonnage
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
    """
    Affiche uniquement les nœuds qui participent à une arête issue d'une
    permission R/W. Les propriétaires (Owner) non autorisés ne sont pas rendus.
    """
    # Graphe des arêtes R/W seulement
    G1 = nx.DiGraph()
    for src, dests in adj_1.items():
        for dst in dests:
            G1.add_edge(src, dst)

    if nx.is_directed_acyclic_graph(G1):
        G1 = nx.transitive_reduction(G1)

    # Nœuds effectivement reliés par une arête
    nodes_with_edges = set(G1.nodes())

    net = Network(notebook=False, height="1000px", width="100%", directed=True, cdn_resources="in_line")

    role_to_subject = {}
    try:
        role_to_subject = dict(role_data) if role_data is not None else {}
    except Exception:
        role_to_subject = {}

    x_gap, y_gap = 300, 250
    cur_y_subject, cur_y_object = 0, 0
    placed = set()

    # On ajoute uniquement les nœuds présents dans nodes_with_edges
    for component, label in zip(components_1, labels_1):
        subjects = [s for s in component if str(s).startswith("S") and s in nodes_with_edges]
        objects  = [o for o in component if str(o).startswith("O") and o in nodes_with_edges]

        for subj in subjects:
            if subj in placed: 
                continue
            roles = role_to_subject.get(subj, "None")
            combined = "{" + ", ".join(sorted(label | {subj})) + "}"
            net.add_node(subj, label=f"{subj}({roles}):\n{combined}", shape="ellipse",
                         x=-x_gap, y=-cur_y_subject * y_gap)
            placed.add(subj)
            cur_y_subject += 1

        for obj in objects:
            if obj in placed: 
                continue
            combined = "{" + ", ".join(sorted(label | {obj})) + "}"
            net.add_node(obj, label=f"{obj}:\n{combined}", shape="box",
                         x=x_gap, y=-cur_y_object * y_gap)
            placed.add(obj)
            cur_y_object += 1

    # Arêtes entre nœuds effectivement placés
    for u, v in G1.edges():
        if u in placed and v in placed:
            net.add_edge(u, v, arrows="to")

    # Boîtes du bas : ne montrer que les composantes qui contiennent au moins un nœud rendu
    positions = {0: (-x_gap, 450), 1: (0, 0), 2: (x_gap, 800)}
    offset_y = y_gap
    base_idx = len(net.get_nodes())
    box_i = 0

    def comp_has_rendered_node(comp):
        return any(n in placed for n in comp)

    for comp, label in zip(components_2, labels_2):
        if not comp_has_rendered_node(comp):
            continue
        entity_name = ", ".join(comp)
        combined = "{" + ", ".join(sorted(label | set(comp))) + "}"
        text = f"| {entity_name}: {combined} |"

        col = box_i % 3
        row = box_i // 3
        x, y = positions[col]
        y += row * offset_y

        net.add_node(base_idx + box_i, label=text, shape="box",
                     x=x, y=y, width_constraint=300, height_constraint=100)
        box_i += 1

    net.set_options("""
      var options = {
        nodes: { font: { size: 50 }, shapeProperties: { borderRadius: 5 }, size: 40, fixed: { x:false, y:false } },
        edges: { width: 4, arrows: { to: { enabled: true, scaleFactor: 1.5 } }, length: 150, smooth: { enabled:false } },
        physics: { enabled:false }, interaction: { dragNodes:true, dragView:true, zoomView:true }
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

    # Propagation RBAC éventuelle
    df_expanded = propagate_rbac_from_excel(df)

    # ⚠️ lignes effectives utilisées pour le graphe = uniquement R/W
    df_effective = df_expanded[df_expanded["Permission"].isin(["R", "W"])].copy()
    if df_effective.empty:
        st.info("Aucune relation R/W à afficher.")
        return

    # Construire l'adjacence **sur df_effective**
    adj = apply_permissions(df_effective)

    # ⚠️ nœuds actifs = ceux qui ont une arête entrante/sortante (pas d’apparition des “Owner” seuls)
    active_nodes = set(adj.keys())
    for lst in adj.values():
        active_nodes.update(lst)

    V = sorted(active_nodes)
    scc, cmap = tarjan(V, adj)
    labels = propagate_labels(scc, adj, cmap)

    # Tables
    col1, col2 = st.columns([1, 1], gap="large")
    with col1:
        display_entities_table(scc, labels)
    with col2:
        display_role_table_streamlit(df_expanded)

    # Graphe
    st.markdown("---")
    simplified = simplify_relations(labels)
    role_map = df_expanded.set_index("Source")["Role"].to_dict() if "Role" in df_expanded.columns else {}
    draw_combined_graph(
        scc, adj, labels,
        scc, labels, simplified,
        role_data=role_map,
        active_nodes=active_nodes,  # <-- passé au renderer
    )

# =============== TERMINAL : COMMANDES ======================
def apply_prompt(global_data: pd.DataFrame, prompt: str):
    """Interprète une commande, met à jour le DF et renvoie (df, message)."""
    # --- helpers ---
    def ensure_cols(df):
        cols = ["Source", "Target", "Permission", "Role", "Heritage"]
        for c in cols:
            if c not in df.columns:
                df[c] = None
        return df

    df = ensure_cols(global_data.copy())

    line = (prompt or "").strip()
    if not line:
        return df, "💬 Empty command"

    parts = line.split()
    command, args = parts[0], parts[1:]

    # Toujours initialiser le journal des messages ICI
    out_msgs = [f"💬 Command executed: C:\\> {line}"]

    # ========== PERF ==========
    if command == "EvalPerf":
        try:
            total = len(st.session_state.sujets_definis | st.session_state.objets_definis)
            if total == 0:
                out_msgs.append("⚠️ No entities defined. Please create subjects or objects first.")
                return df, "\n".join(out_msgs)
            evaluer_performance_interface(total)
            out_msgs.append("✅ Performance chart generated.")
            return df, "\n".join(out_msgs)
        except Exception as e:
            out_msgs.append(f"❌ Error EvalPerf: {e}")
            return df, "\n".join(out_msgs)

    # ========== RBAC ==========
    if command == "AddObj" and len(args) == 1:
        # RBAC: déclare un objet (sans propriétaire)
        obj = args[0]
        if obj in st.session_state.objets_definis:
            out_msgs.append(f"ℹ️ The object '{obj}' already exists.")
            return df, "\n".join(out_msgs)
        st.session_state.objets_definis.add(obj)
        df = pd.concat([df, pd.DataFrame([{
            "Source": None, "Target": obj, "Permission": None, "Role": None, "Heritage": None
        }], columns=df.columns)], ignore_index=True)
        out_msgs.append(f"✅ Object '{obj}' created.")
        return df, "\n".join(out_msgs)

    if command == "AddRole":
        if len(args) != 1:
            out_msgs.append("❌ Usage: AddRole R1")
            return df, "\n".join(out_msgs)
        role = args[0]
        if role in st.session_state.roles_definis:
            out_msgs.append(f"ℹ️ Role '{role}' already exists.")
            return df, "\n".join(out_msgs)
        st.session_state.roles_definis.add(role)
        st.session_state.role_permissions.setdefault(role, set())
        out_msgs.append(f"✅ Role '{role}' added.")
        return df, "\n".join(out_msgs)

    if command == "AddSub":
        if len(args) < 1:
            out_msgs.append("❌ Usage: AddSub S1 [R1]")
            return df, "\n".join(out_msgs)
        subject = args[0]
        role = args[1] if len(args) > 1 else None
        if subject in st.session_state.sujets_definis:
            out_msgs.append(f"ℹ️ The Subject '{subject}' already exists.")
            return df, "\n".join(out_msgs)
        if role and role not in st.session_state.roles_definis:
            out_msgs.append(f"⛔ Error: Role '{role}' does not exist.")
            return df, "\n".join(out_msgs)

        st.session_state.sujets_definis.add(subject)
        st.session_state.subject_roles.setdefault(subject, set())
        if role:
            st.session_state.subject_roles[subject].add(role)

        df = pd.concat([df, pd.DataFrame([{
            "Source": subject, "Target": None, "Permission": None, "Role": role, "Heritage": None
        }], columns=df.columns)], ignore_index=True)

        if role:
            # héritage immédiat des permissions du rôle
            for (perm, obj) in st.session_state.role_permissions.get(role, set()):
                mask = (df["Source"] == subject) & (df["Permission"] == perm) & (df["Target"] == obj) & (df["Role"] == role)
                if not mask.any():
                    df = pd.concat([df, pd.DataFrame([{
                        "Source": subject, "Permission": perm, "Target": obj, "Role": role, "Heritage": "Role"
                    }], columns=df.columns)], ignore_index=True)

        out_msgs.append(f"✅ Subject '{subject}' added" + (f" with role '{role}'" if role else ""))
        return df, "\n".join(out_msgs)

    if command == "GrantPermission":
        if len(args) != 3:
            out_msgs.append("❌ Usage: GrantPermission R1 R O1")
            return df, "\n".join(out_msgs)
        role, perm, obj = args
        if role not in st.session_state.roles_definis:
            out_msgs.append(f"❌ Role '{role}' is not defined.")
            return df, "\n".join(out_msgs)
        if obj not in st.session_state.objets_definis:
            out_msgs.append(f"❌ Object '{obj}' does not exist. Use AddObj first.")
            return df, "\n".join(out_msgs)

        st.session_state.role_permissions.setdefault(role, set()).add((perm, obj))
        for subj, roles in st.session_state.subject_roles.items():
            if role in roles:
                mask = ((df["Source"] == subj) & (df["Permission"] == perm) & (df["Target"] == obj) & (df["Role"] == role))
                if not mask.any():
                    df = pd.concat([df, pd.DataFrame([{
                        "Source": subj, "Permission": perm, "Target": obj, "Role": role, "Heritage": "Role"
                    }], columns=df.columns)], ignore_index=True)
        out_msgs.append(f"✅ Permission '{perm}' on '{obj}' granted to role '{role}' and propagated.")
        return df, "\n".join(out_msgs)

    if command == "RevokePermission":
        if len(args) != 3:
            out_msgs.append("❌ Usage: RevokePermission R1 R O1")
            return df, "\n".join(out_msgs)
        role, perm, obj = args
        if role not in st.session_state.roles_definis:
            out_msgs.append(f"⛔ Error: Role '{role}' does not exist.")
            return df, "\n".join(out_msgs)
        if obj not in st.session_state.objets_definis:
            out_msgs.append(f"⛔ Error: Object '{obj}' does not exist.")
            return df, "\n".join(out_msgs)

        st.session_state.role_permissions.setdefault(role, set()).discard((perm, obj))
        before = len(df)
        df = df[~((df["Permission"] == perm) & (df["Target"] == obj) & (df["Role"] == role))]
        deleted = before - len(df)
        out_msgs.append(f"🗑️ Permission '{perm}' on '{obj}' revoked from role '{role}' ({deleted} propagation(s) removed).")
        return df, "\n".join(out_msgs)

    if command == "DeassignUser":
        if len(args) != 2:
            out_msgs.append("❌ Usage: DeassignUser S1 R1")
            return df, "\n".join(out_msgs)
        subject, role = args
        if subject not in st.session_state.sujets_definis:
            out_msgs.append(f"⛔ Error: Subject '{subject}' does not exist.")
            return df, "\n".join(out_msgs)
        if role not in st.session_state.roles_definis:
            out_msgs.append(f"⛔ Error: Role '{role}' does not exist.")
            return df, "\n".join(out_msgs)
        if role not in st.session_state.subject_roles.get(subject, set()):
            out_msgs.append(f"ℹ️ Subject '{subject}' does not have role '{role}'.")
            return df, "\n".join(out_msgs)

        st.session_state.subject_roles[subject].remove(role)
        before = len(df)
        df = df[~((df["Source"] == subject) & (df["Role"] == role))]
        deleted = before - len(df)
        out_msgs.append(f"🗑️ Role '{role}' removed from subject '{subject}' ({deleted} propagated permission(s) removed).")
        return df, "\n".join(out_msgs)

    if command == "RemoveRole":
        if len(args) != 1:
            out_msgs.append("❌ Usage: RemoveRole R1")
            return df, "\n".join(out_msgs)
        role = args[0]
        if role not in st.session_state.roles_definis:
            out_msgs.append(f"⛔ Error: Role '{role}' does not exist.")
            return df, "\n".join(out_msgs)
        st.session_state.roles_definis.remove(role)
        st.session_state.role_permissions.pop(role, None)
        for s in list(st.session_state.subject_roles.keys()):
            st.session_state.subject_roles[s].discard(role)
        df = df[df["Role"] != role]
        out_msgs.append(f"🗑️ Role '{role}' successfully deleted and its permissions removed.")
        return df, "\n".join(out_msgs)

    if command == "ModifyRole":
        if len(args) != 2:
            out_msgs.append("❌ Usage: ModifyRole OldRole NewRole")
            return df, "\n".join(out_msgs)
        old_role, new_role = args
        if old_role not in st.session_state.roles_definis:
            out_msgs.append(f"⛔ Error: Role '{old_role}' does not exist.")
            return df, "\n".join(out_msgs)
        if new_role in st.session_state.roles_definis:
            out_msgs.append(f"⛔ Error: Role '{new_role}' already exists.")
            return df, "\n".join(out_msgs)

        st.session_state.roles_definis.remove(old_role)
        st.session_state.roles_definis.add(new_role)
        st.session_state.role_permissions[new_role] = st.session_state.role_permissions.pop(old_role, set())
        for subj in st.session_state.subject_roles:
            if old_role in st.session_state.subject_roles[subj]:
                st.session_state.subject_roles[subj].remove(old_role)
                st.session_state.subject_roles[subj].add(new_role)
        df.loc[df["Role"] == old_role, "Role"] = new_role
        out_msgs.append(f"✏️ Role renamed: '{old_role}' ➝ '{new_role}'")
        return df, "\n".join(out_msgs)

    if command == "ModifyPermission":
        if len(args) != 4:
            out_msgs.append("❌ Usage: ModifyPermission R1 OldPerm Target NewPerm")
            return df, "\n".join(out_msgs)
        role, old_perm, target, new_perm = args
        if role not in st.session_state.roles_definis:
            out_msgs.append(f"⛔ Error: Role '{role}' does not exist.")
            return df, "\n".join(out_msgs)
        if (old_perm, target) not in st.session_state.role_permissions.get(role, set()):
            out_msgs.append(f"⚠️ Permission '{old_perm}' on '{target}' not found in role '{role}'.")
            return df, "\n".join(out_msgs)

        st.session_state.role_permissions[role].remove((old_perm, target))
        st.session_state.role_permissions[role].add((new_perm, target))
        mask = (df["Role"] == role) & (df["Permission"] == old_perm) & (df["Target"] == target)
        count = df[mask].shape[0]
        df.loc[mask, "Permission"] = new_perm
        out_msgs.append(f"🔁 Permission modified: Role '{role}' – {old_perm} ➝ {new_perm} on '{target}' ({count} entries updated).")
        return df, "\n".join(out_msgs)

    # ========== DAC ==========
    # S2 AddObj O2  => crée l'objet O2 avec propriétaire S2, **sans** lecture auto
    if len(parts) >= 3 and parts[1] == "AddObj":
        owner, obj = parts[0], parts[2]
        if owner not in st.session_state.sujets_definis:
            out_msgs.append(f"⛔ Error: Subject '{owner}' does not exist. Use AddSub first.")
            return df, "\n".join(out_msgs)
        if obj in st.session_state.objets_definis:
            out_msgs.append(f"ℹ️ The object '{obj}' already exists.")
            return df, "\n".join(out_msgs)

        st.session_state.objets_definis.add(obj)
        entry_owner = {"Source": owner, "Target": obj, "Permission": "Owner", "Role": None, "Heritage": None}
        df = pd.concat([df, pd.DataFrame([entry_owner], columns=df.columns)], ignore_index=True)
        out_msgs.append(f"✅ Object '{obj}' created with owner '{owner}'")
        return df, "\n".join(out_msgs)

    # S2 Grant S3 O2 R
    if len(parts) >= 5 and parts[1] == "Grant":
        owner, _, subject, obj, perm = parts[:5]
        if owner not in st.session_state.sujets_definis:
            out_msgs.append(f"⛔ Error: Subject '{owner}' does not exist.")
            return df, "\n".join(out_msgs)
        if subject not in st.session_state.sujets_definis:
            out_msgs.append(f"⛔ Error: Target subject '{subject}' does not exist.")
            return df, "\n".join(out_msgs)
        if obj not in st.session_state.objets_definis:
            out_msgs.append(f"⛔ Error: Object '{obj}' does not exist.")
            return df, "\n".join(out_msgs)

        # Vérifier que 'owner' est bien propriétaire de 'obj'
        is_owner = ((df["Source"] == owner) & (df["Target"] == obj) & (df["Permission"] == "Owner")).any()
        if not is_owner:
            out_msgs.append(f"⛔ Error: '{owner}' is not the owner of '{obj}'.")
            return df, "\n".join(out_msgs)

        new_entry = {"Source": subject, "Permission": perm, "Target": obj, "Role": None, "Heritage": None}
        df = pd.concat([df, pd.DataFrame([new_entry], columns=df.columns)], ignore_index=True)
        out_msgs.append(f"✅ Permission '{perm}' granted to '{subject}' on '{obj}' by '{owner}'.")
        return df, "\n".join(out_msgs)

    # ========== CHINA-WALL ==========
    if command == "Never":
        if "for" in args:
            idx = args.index("for")
            etiquettes = [e.strip("{} ,") for e in args[:idx]]
            entites = [e.strip("{} ,") for e in args[idx + 1:]]
            for ent in entites:
                st.session_state.interdictions_entites.setdefault(ent, []).append(etiquettes)
            out_msgs.append(f"🚧 Forbidden combination {etiquettes} for entities: {entites}")
            return df, "\n".join(out_msgs)
        etiquettes = [e.strip("{} ,") for e in args]
        st.session_state.interdictions_globales.append(etiquettes)
        out_msgs.append(f"🚧 Globally forbidden combination: {etiquettes}")
        return df, "\n".join(out_msgs)

    if command == "AddCh":
        if len(args) == 2:
            source, target = args
            temp = pd.concat([df, pd.DataFrame([{
                "Source": source, "Target": target, "Permission": "R", "Role": None, "Heritage": None
            }], columns=df.columns)], ignore_index=True)
        elif len(args) >= 3:
            source, permission, target = args[:3]
            role = args[3] if len(args) > 3 else None
            temp = pd.concat([df, pd.DataFrame([{
                "Source": source, "Target": target, "Permission": permission, "Role": role, "Heritage": None
            }], columns=df.columns)], ignore_index=True)
        else:
            out_msgs.append("❌ Usage: AddCh E1 E2  |  AddCh S1 R O1 [Role]")
            return df, "\n".join(out_msgs)

        # Vérif China-Wall
        adj = apply_permissions(temp)
        V = sorted(set(adj.keys()) | {v for lst in adj.values() for v in lst})
        scc, cmap = tarjan(V, adj)
        labels = propagate_labels(scc, adj, cmap)

        for comp in labels:
            for interdit in st.session_state.interdictions_globales:
                if set(interdit).issubset(comp):
                    out_msgs.append(f"⛔ CHINA WALL ERROR: Global restriction violated for {interdit}")
                    return df, "\n".join(out_msgs)
            for ent, combos in st.session_state.interdictions_entites.items():
                if ent in comp:
                    for interdit in combos:
                        if set(interdit).issubset(comp):
                            out_msgs.append(f"⛔ CHINA WALL ERROR: Restriction violated for {ent}: {interdit}")
                            return df, "\n".join(out_msgs)

        df = temp
        if len(args) == 2:
            out_msgs.append(f"✅ Channel added: {source} --R--> {target}")
        else:
            out_msgs.append(f"✅ Channel added: {source} --{permission}/{role}--> {target}")
        return df, "\n".join(out_msgs)

    if command == "RemoveCh":
        if len(args) == 3:
            source, permission, target = args
            before = len(df)
            df = df[~((df["Source"] == source) & (df["Permission"] == permission) & (df["Target"] == target))]
            removed = before - len(df)
            out_msgs.append("🗑️ Channel removed: {} --{}--> {}"
                            .format(source, permission, target) if removed else
                            f"⚠️ No channel found matching '{source} {permission} {target}'.")
            return df, "\n".join(out_msgs)
        if len(args) == 2:
            source, target = args
            before = len(df)
            df = df[~((df["Source"] == source) & (df["Target"] == target))]
            removed = before - len(df)
            out_msgs.append("🗑️ All channels removed between '{}' and '{}'"
                            .format(source, target) if removed else
                            f"⚠️ No channel found between '{source}' and '{target}'.")
            return df, "\n".join(out_msgs)
        out_msgs.append("❌ Usage: RemoveCh Source [Permission] Target")
        return df, "\n".join(out_msgs)

    if command == "RemoveSub":
        if len(args) != 1:
            out_msgs.append("❌ Usage: RemoveSub S1")
            return df, "\n".join(out_msgs)
        s = args[0]
        st.session_state.sujets_definis.discard(s)
        st.session_state.subject_roles.pop(s, None)
        df = df[df["Source"] != s]
        out_msgs.append(f"🗑️ Subject '{s}' removed and its associated permissions cleared.")
        return df, "\n".join(out_msgs)

    if command == "RemoveObj":
        if len(args) != 1:
            out_msgs.append("❌ Usage: RemoveObj O1")
            return df, "\n".join(out_msgs)
        o = args[0]
        st.session_state.objets_definis.discard(o)
        df = df[(df["Source"] != o) & (df["Target"] != o)]
        out_msgs.append(f"🗑️ Object '{o}' removed and its associated channels cleared.")
        return df, "\n".join(out_msgs)

    if command == "modifyCh":
        if len(args) != 6:
            out_msgs.append("❌ Usage: modifyCh oldS oldP oldT newS newP newT")
            return df, "\n".join(out_msgs)
        old_s, old_p, old_t, new_s, new_p, new_t = args
        df.loc[(df["Source"] == old_s) & (df["Permission"] == old_p) & (df["Target"] == old_t),
               ["Source", "Permission", "Target"]] = [new_s, new_p, new_t]
        out_msgs.append(f"🔁 Path modified: {old_s} {old_p} {old_t} ➜ {new_s} {new_p} {new_t}")
        return df, "\n".join(out_msgs)

    if command == "modifySub":
        if len(args) != 2:
            out_msgs.append("❌ Usage: modifySub OldSub NewSub")
            return df, "\n".join(out_msgs)
        old_s, new_s = args
        if old_s in st.session_state.sujets_definis:
            st.session_state.sujets_definis.remove(old_s)
            st.session_state.sujets_definis.add(new_s)
        if old_s in st.session_state.subject_roles:
            st.session_state.subject_roles[new_s] = st.session_state.subject_roles.pop(old_s)
        df.loc[df["Source"] == old_s, "Source"] = new_s
        df.loc[df["Target"] == old_s, "Target"] = new_s
        out_msgs.append(f"✏️ Subject renamed: {old_s} → {new_s}")
        return df, "\n".join(out_msgs)

    if command == "modifyObj":
        if len(args) != 2:
            out_msgs.append("❌ Usage: modifyObj OldObj NewObj")
            return df, "\n".join(out_msgs)
        old_o, new_o = args
        if old_o in st.session_state.objets_definis:
            st.session_state.objets_definis.remove(old_o)
            st.session_state.objets_definis.add(new_o)
        df.loc[df["Source"] == old_o, "Source"] = new_o
        df.loc[df["Target"] == old_o, "Target"] = new_o
        out_msgs.append(f"✏️ Object renamed : {old_o} → {new_o}")
        return df, "\n".join(out_msgs)

    if command == "show":
        process_data_display(df)
        out_msgs.append("🚀 Génération des graphes…")
        return df, "\n".join(out_msgs)

    out_msgs.append("❌ Unknown command.")
    return df, "\n".join(out_msgs)


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
