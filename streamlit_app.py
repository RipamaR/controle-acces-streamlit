# streamlit_app.py
# -----------------------------------------------------------
# Contrôle d'accès (RBAC / DAC / China-Wall) – Streamlit
# Affichage plein écran + rendu PyVis, commandes terminal
# -----------------------------------------------------------

import io
import pandas as pd
import networkx as nx
import streamlit as st
from pyvis.network import Network
from streamlit.components.v1 import html as st_html

# ===================== CONFIG UI ===========================
st.set_page_config(
    page_title="Contrôle d'accès – RBAC / DAC / China-Wall",
    layout="wide",
)

# ===================== ÉTAT GLOBAL =========================
def init_state():
    if "global_data" not in st.session_state:
        st.session_state.global_data = pd.DataFrame(
            columns=["Source", "Permission", "Target", "Role", "Heritage"]
        )

    defaults = {
        "roles_definis": set(),
        "role_permissions": {},
        "subject_roles": {},
        "sujets_definis": set(),
        "objets_definis": set(),
        "interdictions_globales": [],
        "interdictions_entites": {},
        "history": [],
        "cmd_input": "",
    }
    for k, v in defaults.items():
        if k not in st.session_state:
            st.session_state[k] = v

def reset_state():
    st.session_state.global_data = pd.DataFrame(
        columns=["Source", "Permission", "Target", "Role", "Heritage"]
    )
    st.session_state.roles_definis = set()
    st.session_state.role_permissions = {}
    st.session_state.subject_roles = {}
    st.session_state.sujets_definis = set()
    st.session_state.objets_definis = set()
    st.session_state.interdictions_globales = []
    st.session_state.interdictions_entites = {}
    st.session_state.history = []
    st.session_state.cmd_input = ""

init_state()

# ================= ALGORITHMES (Tarjan & co) ================
def tarjan(V, adj):
    index = [0]
    stack = []
    indices = {v: -1 for v in V}
    lowlink = {v: -1 for v in V}
    on_stack = {v: False for v in V}
    scc = []
    component_map = {}

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
            component = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                component.append(w)
                if w == v:
                    break
            scc.append(component)
            for node in component:
                component_map[node] = component

    for v in V:
        if indices[v] == -1:
            strongconnect(v)
    return scc, component_map

def propagate_labels(components, adj, component_map):
    labels = {frozenset(comp): set(comp) for comp in components}

    def dfs(node, visited):
        if node in visited:
            return
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
def apply_permissions(df: pd.DataFrame):
    """
    - R : Target -> Source  (X lit Y => arête Y->X)
    - W : Source -> Target  (X écrit Y => arête X->Y)
    """
    adj = {}

    def add_edge(a, b):
        if pd.isna(a) or pd.isna(b):
            return
        adj.setdefault(a, [])
        adj.setdefault(b, [])
        adj[a].append(b)

    for _, row in df.iterrows():
        s, p, t = row.get("Source"), row.get("Permission"), row.get("Target")
        if pd.isna(p) or pd.isna(t):
            continue
        for perm in str(p).split(","):
            perm = perm.strip()
            if perm == "R":
                add_edge(t, s)
            elif perm == "W":
                add_edge(s, t)

    for k in list(adj.keys()):
        adj[k] = list(sorted(set(adj[k])))
    return adj

# =============== TABLES (Streamlit) ========================
def display_entities_table(components, labels):
    data = {
        "Entities": [", ".join(sorted(c)) for c in components],
        "Their labels": [
            "{" + ", ".join(sorted(lbl | set(comp))) + "}"
            for comp, lbl in zip(components, labels)
        ],
    }
    df = pd.DataFrame(data)
    st.markdown("### Table des entités et étiquettes")
    st.dataframe(df, use_container_width=True)

def display_role_table_streamlit(df: pd.DataFrame):
    if "Role" not in df.columns:
        return
    roles = sorted({r for r in df["Role"].dropna().unique() if str(r).strip()})
    objects = sorted({t for t in df["Target"].dropna().unique() if str(t).strip()})
    if not roles or not objects:
        return

    role_perms_map = {r: {o: "" for o in objects} for r in roles}
    for _, row in df.iterrows():
        role = row.get("Role")
        obj = row.get("Target")
        perm = row.get("Permission")
        if pd.notna(role) and pd.notna(obj) and pd.notna(perm):
            current = set(role_perms_map.get(role, {}).get(obj, "").split(",")) if role_perms_map.get(role, {}).get(obj) else set()
            for p in str(perm).split(","):
                p = p.strip()
                if p:
                    current.add(p)
            role_perms_map[role][obj] = ",".join(sorted(current))

    table = []
    for r in roles:
        row = {"Role": r}
        for o in objects:
            row[o] = role_perms_map[r][o]
        table.append(row)
    df_role = pd.DataFrame(table, columns=["Role"] + objects)

    st.markdown("### Table des rôles et permissions")
    st.dataframe(df_role, use_container_width=True)

# =============== PYVIS (Streamlit) =========================
def draw_combined_graph(components_1, adj_1, labels_1,
                        components_2, labels_2, simplified_edges_2, role_data):
    net = Network(notebook=False, height='1000px', width='100%', directed=True, cdn_resources='in_line')

    sorted_components_1 = sorted(components_1, key=len, reverse=True)
    sorted_components_2 = sorted(components_2, key=len, reverse=True)

    x_gap = 300
    y_gap = 250
    current_y_subject = 0
    current_y_object = 0
    node_indices = {}
    G1 = nx.DiGraph()

    role_to_subject = {subject: role_data.get(subject, "None") for subject in adj_1.keys()}

    for component, label in zip(sorted_components_1, labels_1):
        subjects = [s for s in component if str(s).startswith("S")]
        objects = [o for o in component if str(o).startswith("O")]

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

    for src, dest_list in adj_1.items():
        for dest in dest_list:
            if src in node_indices and dest in node_indices:
                G1.add_edge(src, dest)

    if nx.is_directed_acyclic_graph(G1):
        G1 = nx.transitive_reduction(G1)

    for src, dest in G1.edges():
        net.add_edge(src, dest, arrows="to")

    positions = {0: (-x_gap, 450), 1: (0, 0), 2: (x_gap, 800)}
    offset_y = y_gap
    base_idx = len(net.get_nodes())

    for i, (component, label) in enumerate(zip(sorted_components_2, labels_2)):
        entity_name = ', '.join(component)
        combined_labels = '{' + ', '.join(sorted(label | set(component))) + '}'
        text = f'| {entity_name}: {combined_labels} |'
        col_index = i % 3
        row_index = i // 3
        x, y = positions[col_index]
        y += row_index * offset_y
        net.add_node(base_idx + i, label=text, shape='box', x=x, y=y, width_constraint=300, height_constraint=100)

    def find_idx_by_labelset(target_set):
        for i, lbl in enumerate(labels_2):
            if lbl == target_set:
                return i
        return None

    for src_set, dest_set in simplified_edges_2:
        si = find_idx_by_labelset(src_set)
        di = find_idx_by_labelset(dest_set)
        if si is not None and di is not None:
            net.add_edge(base_idx + si, base_idx + di, arrows="to")

    net.set_options("""
    var options = {
      "nodes": {"font": {"size": 50}, "shapeProperties": {"borderRadius": 5}, "size": 40, "fixed": {"x": false, "y": false}},
      "edges": {"width": 4, "arrows": {"to": {"enabled": true, "scaleFactor": 1.5}}, "length": 150, "smooth": {"enabled": false}},
      "physics": {"enabled": false},
      "interaction": {"dragNodes": true, "dragView": true, "zoomView": true}
    }
    """)

    html_str = net.generate_html()
    st_html(html_str, height=1000, width=1800, scrolling=True)

# =============== RBAC : propagation depuis Excel ===========
def propagate_rbac_from_excel(df: pd.DataFrame) -> pd.DataFrame:
    df = df.copy()
    if "Role" not in df.columns:
        df["Role"] = None
    if "Heritage" not in df.columns:
        df["Heritage"] = None

    role_perms = {}
    subject_roles = {}

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
        if not subj:
            continue
        for r in roles:
            for perm, obj in role_perms.get(r, set()):
                mask = ((df["Source"] == subj) & (df["Permission"] == perm) & (df["Target"] == obj))
                if not mask.any():
                    new_rows.append({
                        "Source": subj, "Permission": perm, "Target": obj, "Role": r, "Heritage": "Role"
                    })
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

# =============== LECTURE EXCEL (entités simples) ===========
def load_entities_excel(file_bytes: bytes) -> pd.DataFrame:
    df_raw = pd.read_excel(io.BytesIO(file_bytes))
    cols = {c.strip().lower() for c in df_raw.columns}
    if not ({"entity1", "entity2"} <= cols):
        raise ValueError("Le fichier 'entités' doit contenir les colonnes Entity1 et Entity2.")
    col_map = {c.lower(): c for c in df_raw.columns}
    col_e1 = col_map["entity1"]
    col_e2 = col_map["entity2"]

    rows = []
    for _, row in df_raw.iterrows():
        e1 = str(row[col_e1]).strip()
        e2 = str(row[col_e2]).strip()
        if e1 and e1.lower() != "nan" and e2 and e2.lower() != "nan":
            rows.append({"Source": e2, "Permission": "R", "Target": e1, "Role": None, "Heritage": None})

    if not rows:
        raise ValueError("Aucune paire valide (Entity1, Entity2) trouvée dans le fichier.")

    return pd.DataFrame(rows, columns=["Source", "Permission", "Target", "Role", "Heritage"])

# =============== VISUALISATION COMPLÈTE ====================
def process_data_display(df: pd.DataFrame):
    if df is None or df.empty:
        st.info("Aucune donnée à afficher.")
        return

    df_expanded = propagate_rbac_from_excel(df)

    # ✅ Ne garder que les vraies arêtes (R/W)
    df_edges = df_expanded[df_expanded["Permission"].isin(["R", "W"])].copy()
    if df_edges.empty:
        st.info("Aucune permission R/W à afficher pour le graphe.")
        return

    adj = apply_permissions(df_edges)
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
        scc, adj, labels, scc, labels, simplified_edges,
        role_data=df_expanded.set_index("Source")["Role"].to_dict()
        if "Role" in df_expanded.columns else {}
    )

# =============== UTILITAIRE DF =============================
def _normalize_df(df: pd.DataFrame) -> pd.DataFrame:
    """Déduplique et remet les colonnes manquantes si besoin."""
    for c in ["Source", "Permission", "Target", "Role", "Heritage"]:
        if c not in df.columns:
            df[c] = None
    df = df.drop_duplicates(subset=["Source", "Permission", "Target", "Role"], keep="last").reset_index(drop=True)
    return df

# =============== TERMINAL : commandes ======================
def apply_prompt(global_data: pd.DataFrame, prompt: str):
    df = _normalize_df(global_data.copy())
    parts = prompt.strip().split()
    if not parts:
        return df, "💬 Empty command"

    command = parts[0]
    args = parts[1:]
    out_msgs = [f"💬 Command executed: C:\\> {' '.join(parts)}"]

    # ---------- RBAC : OBJET seul ----------
    if command == "AddObj" and len(args) == 1:
        obj = args[0]
        if obj in st.session_state.objets_definis:
            return df, "\n".join(out_msgs + [f"ℹ️ The object '{obj}' already exists."])
        st.session_state.objets_definis.add(obj)
        # (aucune permission R/W ajoutée ici)
        return df, "\n".join(out_msgs + [f"✅ Object '{obj}' created."])

    # ---------- RBAC : ROLES / SUBS ----------
    if command == "AddRole":
        if len(args) != 1:
            return df, "\n".join(out_msgs + ["❌ Usage: AddRole R1"])
        role = args[0]
        if role in st.session_state.roles_definis:
            return df, "\n".join(out_msgs + [f"ℹ️ Role '{role}' already exists."])
        st.session_state.roles_definis.add(role)
        st.session_state.role_permissions.setdefault(role, set())
        return df, "\n".join(out_msgs + [f"✅ Role '{role}' added."])

    if command == "AddSub":
        if len(args) < 1:
            return df, "\n".join(out_msgs + ["❌ Usage: AddSub S1 [R1]"])
        subject = args[0]
        role = args[1] if len(args) > 1 else None
        if subject in st.session_state.sujets_definis:
            return df, "\n".join(out_msgs + [f"ℹ️ The Subject '{subject}' already exists."])
        if role and role not in st.session_state.roles_definis:
            return df, "\n".join(out_msgs + [f"⛔ Error: Role '{role}' does not exist."])

        st.session_state.sujets_definis.add(subject)
        st.session_state.subject_roles.setdefault(subject, set())
        if role:
            st.session_state.subject_roles[subject].add(role)

        # profil
        df = pd.concat(
            [df, pd.DataFrame([{"Source": subject, "Permission": None, "Target": None, "Role": role, "Heritage": None}])],
            ignore_index=True,
        )

        # héritage
        if role:
            for (perm, obj) in st.session_state.role_permissions.get(role, set()):
                mask = (
                    (df["Source"] == subject)
                    & (df["Permission"] == perm)
                    & (df["Target"] == obj)
                    & (df["Role"] == role)
                )
                if not mask.any():
                    df = pd.concat(
                        [df, pd.DataFrame([{"Source": subject, "Permission": perm, "Target": obj, "Role": role, "Heritage": "Role"}])],
                        ignore_index=True,
                    )

        return _normalize_df(df), "\n".join(out_msgs + [f"✅ Subject '{subject}' added" + (f" with role '{role}'" if role else "")])

    if command == "GrantPermission":
        if len(args) != 3:
            return df, "\n".join(out_msgs + ["❌ Usage: GrantPermission R1 R O1"])
        role, perm, obj = args
        if role not in st.session_state.roles_definis:
            return df, "\n".join(out_msgs + [f"❌ Role '{role}' is not defined."])
        if obj not in st.session_state.objets_definis:
            return df, "\n".join(out_msgs + [f"❌ Object '{obj}' does not exist. Use AddObj first."])
        st.session_state.role_permissions.setdefault(role, set()).add((perm, obj))
        for subj, roles in st.session_state.subject_roles.items():
            if role in roles:
                mask = (
                    (df["Source"] == subj)
                    & (df["Permission"] == perm)
                    & (df["Target"] == obj)
                    & (df["Role"] == role)
                )
                if not mask.any():
                    df = pd.concat(
                        [df, pd.DataFrame([{"Source": subj, "Permission": perm, "Target": obj, "Role": role, "Heritage": "Role"}])],
                        ignore_index=True,
                    )
        return _normalize_df(df), "\n".join(out_msgs + [f"✅ Permission '{perm}' on '{obj}' granted to role '{role}' and propagated."])

    if command == "RevokePermission":
        if len(args) != 3:
            return df, "\n".join(out_msgs + ["❌ Usage: RevokePermission R1 R O1"])
        role, perm, obj = args
        if role not in st.session_state.roles_definis:
            return df, "\n".join(out_msgs + [f"⛔ Error: Role '{role}' does not exist."])
        if obj not in st.session_state.objets_definis:
            return df, "\n".join(out_msgs + [f"⛔ Error: Object '{obj}' does not exist."])
        st.session_state.role_permissions.setdefault(role, set()).discard((perm, obj))
        before = len(df)
        df = df[~((df["Permission"] == perm) & (df["Target"] == obj) & (df["Role"] == role))]
        deleted = before - len(df)
        return _normalize_df(df), "\n".join(out_msgs + [f"🗑️ Permission '{perm}' on '{obj}' revoked from role '{role}' ({deleted} propagation(s) removed)."])

    if command == "DeassignUser":
        if len(args) != 2:
            return df, "\n".join(out_msgs + ["❌ Usage: DeassignUser S1 R1"])
        subject, role = args
        if subject not in st.session_state.sujets_definis:
            return df, "\n".join(out_msgs + [f"⛔ Error: Subject '{subject}' does not exist."])
        if role not in st.session_state.roles_definis:
            return df, "\n".join(out_msgs + [f"⛔ Error: Role '{role}' does not exist."])
        if role not in st.session_state.subject_roles.get(subject, set()):
            return df, "\n".join(out_msgs + [f"ℹ️ Subject '{subject}' does not have role '{role}'."])
        st.session_state.subject_roles[subject].remove(role)
        before = len(df)
        df = df[~((df["Source"] == subject) & (df["Role"] == role))]
        deleted = before - len(df)
        return _normalize_df(df), "\n".join(out_msgs + [f"🗑️ Role '{role}' removed from subject '{subject}' ({deleted} propagated permission(s) removed)."])

    if command == "RemoveRole":
        if len(args) != 1:
            return df, "\n".join(out_msgs + ["❌ Usage: RemoveRole R1"])
        role = args[0]
        if role not in st.session_state.roles_definis:
            return df, "\n".join(out_msgs + [f"⛔ Error: Role '{role}' does not exist."])
        st.session_state.roles_definis.remove(role)
        st.session_state.role_permissions.pop(role, None)
        for subj in list(st.session_state.subject_roles.keys()):
            st.session_state.subject_roles[subj].discard(role)
        df = df[df["Role"] != role]
        return _normalize_df(df), "\n".join(out_msgs + [f"🗑️ Role '{role}' successfully deleted and its permissions removed."])

    if command == "ModifyRole":
        if len(args) != 2:
            return df, "\n".join(out_msgs + ["❌ Usage: ModifyRole OldRole NewRole"])
        old_role, new_role = args
        if old_role not in st.session_state.roles_definis:
            return df, "\n".join(out_msgs + [f"⛔ Error: Role '{old_role}' does not exist."])
        if new_role in st.session_state.roles_definis:
            return df, "\n".join(out_msgs + [f"⛔ Error: Role '{new_role}' already exists."])
        st.session_state.roles_definis.remove(old_role)
        st.session_state.roles_definis.add(new_role)
        st.session_state.role_permissions[new_role] = st.session_state.role_permissions.pop(old_role, set())
        for subj in st.session_state.subject_roles:
            if old_role in st.session_state.subject_roles[subj]:
                st.session_state.subject_roles[subj].remove(old_role)
                st.session_state.subject_roles[subj].add(new_role)
        df.loc[df["Role"] == old_role, "Role"] = new_role
        return _normalize_df(df), "\n".join(out_msgs + [f"✏️ Role renamed: '{old_role}' ➝ '{new_role}'"])

    if command == "ModifyPermission":
        if len(args) != 4:
            return df, "\n".join(out_msgs + ["❌ Usage: ModifyPermission R1 OldPerm Target NewPerm"])
        role, old_perm, target, new_perm = args
        if role not in st.session_state.roles_definis:
            return df, "\n".join(out_msgs + [f"⛔ Error: Role '{role}' does not exist."])
        if (old_perm, target) not in st.session_state.role_permissions.get(role, set()):
            return df, "\n".join(out_msgs + [f"⚠️ Permission '{old_perm}' on '{target}' not found in role '{role}'."])
        st.session_state.role_permissions[role].remove((old_perm, target))
        st.session_state.role_permissions[role].add((new_perm, target))
        mask = (df["Role"] == role) & (df["Permission"] == old_perm) & (df["Target"] == target)
        df.loc[mask, "Permission"] = new_perm
        return _normalize_df(df), "\n".join(out_msgs + [f"🔁 Permission modified: Role '{role}' – {old_perm} ➝ {new_perm} on '{target}'."])

    # ---------- DAC ----------
    if len(parts) >= 3 and parts[1] == "AddObj":
        owner, obj = parts[0], parts[2]
        if owner not in st.session_state.sujets_definis:
            return df, "\n".join(out_msgs + [f"⛔ Error: Subject '{owner}' does not exist. Use AddSub first."])
        if obj in st.session_state.objets_definis:
            return df, "\n".join(out_msgs + [f"ℹ️ The object '{obj}' already exists."])
        st.session_state.objets_definis.add(obj)
        entry_owner = {"Source": owner, "Permission": "Owner", "Target": obj, "Role": None, "Heritage": None}
        df = pd.concat([df, pd.DataFrame([entry_owner], columns=df.columns)], ignore_index=True)
        return _normalize_df(df), "\n".join(out_msgs + [f"✅ Object '{obj}' created with owner '{owner}'"])

    if len(parts) >= 5 and parts[1] == "Grant":
        owner, _, subject, obj, perm = parts[:5]
        if owner not in st.session_state.sujets_definis:
            return df, "\n".join(out_msgs + [f"⛔ Error: Subject '{owner}' does not exist."])
        if subject not in st.session_state.sujets_definis:
            return df, "\n".join(out_msgs + [f"⛔ Error: Target subject '{subject}' does not exist."])
        if obj not in st.session_state.objets_definis:
            return df, "\n".join(out_msgs + [f"⛔ Error: Object '{obj}' does not exist."])
        is_owner = ((df["Source"] == owner) & (df["Target"] == obj) & (df["Permission"] == "Owner")).any()
        if not is_owner:
            return df, "\n".join(out_msgs + [f"⛔ Error: '{owner}' is not the owner of '{obj}'."])
        new_entry = {"Source": subject, "Permission": perm, "Target": obj, "Role": None, "Heritage": None}
        df = pd.concat([df, pd.DataFrame([new_entry], columns=df.columns)], ignore_index=True)
        return _normalize_df(df), "\n".join(out_msgs + [f"✅ Permission '{perm}' granted to '{subject}' on '{obj}' by '{owner}'."])


    # ---------- CHINA-WALL ----------
    if command == "Never":
        if "for" in args:
            idx_for = args.index("for")
            etiquettes = [e.strip("{} ,") for e in args[:idx_for]]
            entites = [e.strip("{} ,") for e in args[idx_for + 1:]]
            for ent in entites:
                st.session_state.interdictions_entites.setdefault(ent, []).append(etiquettes)
            return df, "\n".join(out_msgs + [f"🚧 Forbidden combination {etiquettes} for entities: {entites}"])
        else:
            etiquettes = [e.strip("{} ,") for e in args]
            st.session_state.interdictions_globales.append(etiquettes)
            return df, "\n".join(out_msgs + [f"🚧 Globally forbidden combination: {etiquettes}"])

    if command == "AddCh":
        if len(args) == 2:
            source, target = args
            temp = pd.concat(
                [df, pd.DataFrame([{"Source": source, "Permission": "R", "Target": target, "Role": None, "Heritage": None}])],
                ignore_index=True,
            )
        elif len(args) >= 3:
            source, permission, target = args[:3]
            role = args[3] if len(args) > 3 else None
            temp = pd.concat(
                [df, pd.DataFrame([{"Source": source, "Permission": permission, "Target": target, "Role": role, "Heritage": None}])],
                ignore_index=True,
            )
        else:
            return df, "\n".join(out_msgs + ["❌ Usage: AddCh E1 E2  |  AddCh S1 R O1 [Role]"])

        adj = apply_permissions(temp[temp["Permission"].isin(["R", "W"])])
        V = sorted(set(adj.keys()) | {v for lst in adj.values() for v in lst})
        scc, cmap = tarjan(V, adj)
        labels = propagate_labels(scc, adj, cmap)

        for comp in labels:
            for interdit in st.session_state.interdictions_globales:
                if set(interdit).issubset(comp):
                    return df, "\n".join(out_msgs + [f"⛔ CHINA WALL ERROR: Global restriction violated for {interdit}"])
            for ent, combos in st.session_state.interdictions_entites.items():
                if ent in comp:
                    for interdit in combos:
                        if set(interdit).issubset(comp):
                            return df, "\n".join(out_msgs + [f"⛔ CHINA WALL ERROR: Restriction violated for {ent}: {interdit}"])

        df = temp
        if len(args) == 2:
            return _normalize_df(df), "\n".join(out_msgs + [f"✅ Channel added: {args[0]} --R--> {args[1]}"])
        else:
            return _normalize_df(df), "\n".join(out_msgs + [f"✅ Channel added: {source} --{permission}/{role}--> {target}"])

    if command == "RemoveCh":
        if len(args) == 3:
            source, permission, target = args
            before = len(df)
            df = df[~((df["Source"] == source) & (df["Permission"] == permission) & (df["Target"] == target))]
            removed = before - len(df)
            if removed == 0:
                return _normalize_df(df), "\n".join(out_msgs + [f"⚠️ No channel found matching '{source} {permission} {target}'."])
            return _normalize_df(df), "\n".join(out_msgs + [f"🗑️ Channel removed: {source} --{permission}--> {target}"])
        elif len(args) == 2:
            source, target = args
            before = len(df)
            df = df[~((df["Source"] == source) & (df["Target"] == target))]
            removed = before - len(df)
            if removed == 0:
                return _normalize_df(df), "\n".join(out_msgs + [f"⚠️ No channel found between '{source}' and '{target}'."])
            return _normalize_df(df), "\n".join(out_msgs + [f"🗑️ All channels removed between '{source}' and '{target}'."])
        else:
            return df, "\n".join(out_msgs + ["❌ Usage: RemoveCh Source [Permission] Target"])

    if command == "RemoveSub":
        if len(args) != 1:
            return df, "\n".join(out_msgs + ["❌ Usage: RemoveSub S1"])
        s = args[0]
        st.session_state.sujets_definis.discard(s)
        st.session_state.subject_roles.pop(s, None)
        df = df[df["Source"] != s]
        return _normalize_df(df), "\n".join(out_msgs + [f"🗑️ Subject '{s}' removed and its associated permissions cleared."])

    if command == "RemoveObj":
        if len(args) != 1:
            return df, "\n".join(out_msgs + ["❌ Usage: RemoveObj O1"])
        o = args[0]
        st.session_state.objets_definis.discard(o)
        df = df[(df["Source"] != o) & (df["Target"] != o)]
        return _normalize_df(df), "\n".join(out_msgs + [f"🗑️ Object '{o}' removed and its associated channels cleared."])

    if command == "modifyCh":
        if len(args) != 6:
            return df, "\n".join(out_msgs + ["❌ Usage: modifyCh oldS oldP oldT newS newP newT"])
        old_s, old_p, old_t, new_s, new_p, new_t = args
        df.loc[(df["Source"] == old_s) & (df["Permission"] == old_p) & (df["Target"] == old_t),
               ["Source", "Permission", "Target"]] = [new_s, new_p, new_t]
        return _normalize_df(df), "\n".join(out_msgs + [f"🔁 Path modified: {old_s} {old_p} {old_t} ➜ {new_s} {new_p} {new_t}"])

    if command == "modifySub":
        if len(args) != 2:
            return df, "\n".join(out_msgs + ["❌ Usage: modifySub OldSub NewSub"])
        old_s, new_s = args
        if old_s in st.session_state.sujets_definis:
            st.session_state.sujets_definis.remove(old_s)
            st.session_state.sujets_definis.add(new_s)
        if old_s in st.session_state.subject_roles:
            st.session_state.subject_roles[new_s] = st.session_state.subject_roles.pop(old_s)
        df.loc[df["Source"] == old_s, "Source"] = new_s
        df.loc[df["Target"] == old_s, "Target"] = new_s
        return _normalize_df(df), "\n".join(out_msgs + [f"✏️ Subject renamed: {old_s} → {new_s}"])

    if command == "modifyObj":
        if len(args) != 2:
            return df, "\n".join(out_msgs + ["❌ Usage: modifyObj OldObj NewObj"])
        old_o, new_o = args
        if old_o in st.session_state.objets_definis:
            st.session_state.objets_definis.remove(old_o)
            st.session_state.objets_definis.add(new_o)
        df.loc[df["Source"] == old_o, "Source"] = new_o
        df.loc[df["Target"] == old_o, "Target"] = new_o
        return _normalize_df(df), "\n".join(out_msgs + [f"✏️ Object renamed : {old_o} → {new_o}"])

    if command == "show":
        process_data_display(df)
        return _normalize_df(df), "\n".join(out_msgs + ["🚀 Génération des graphes…"])

    return df, "\n".join(out_msgs + ["❌ Unknown command."])

# ======================= UI ================================
def _run_command_callback():
    cmd = st.session_state.get("cmd_input", "").strip()
    if not cmd:
        return
    st.session_state.global_data, message = apply_prompt(st.session_state.global_data, cmd)
    st.session_state.history.append(f"C:\\> {cmd}\n{message}")
    st.session_state.cmd_input = ""   # vider le champ
    st.rerun()

def main():
    st.title("🔐 Contrôle d'accès – RBAC / DAC / China-Wall")

    # Bouton reset (utile quand on change de version)
    if st.button("🧹 Réinitialiser la session", help="Efface les données et l'historique"):
        reset_state()
        st.success("Session réinitialisée.")
        st.stop()

    tabs = st.tabs(["📂 Fichier Excel", "⌨️ Terminal de commandes"])

    # ------- Onglet Excel -------
    with tabs[0]:
        st.write(
            "Charge un fichier **RBAC** (Source, Permission, Target, Role) "
            "ou **Entités** (Entity1, Entity2)."
        )
        up = st.file_uploader(
            "Importer un fichier Excel",
            type=["xlsx"],
            help="Formats acceptés : (1) Source, Permission, Target, Role ; (2) Entity1, Entity2"
        )
        if up:
            try:
                content = up.getvalue()
                df_probe = pd.read_excel(io.BytesIO(content))
                cols_lower = {c.strip().lower() for c in df_probe.columns}

                if {"entity1", "entity2"} <= cols_lower:
                    df = load_entities_excel(content)
                else:
                    df = pd.read_excel(io.BytesIO(content))
                    required = {"Source", "Permission", "Target"}
                    missing = required - set(df.columns)
                    if missing:
                        raise ValueError(f"Colonnes manquantes: {missing}")
                    if "Role" not in df.columns:
                        df["Role"] = None
                    if "Heritage" not in df.columns:
                        df["Heritage"] = None

                st.session_state.global_data = _normalize_df(df)
                st.success("✅ Fichier chargé.")
                with st.expander("Voir les données chargées"):
                    st.dataframe(st.session_state.global_data, use_container_width=True)

                st.markdown("---")
                process_data_display(st.session_state.global_data)

            except Exception as e:
                st.error(f"Erreur de lecture du fichier: {e}")

    # ------- Onglet Terminal -------
    with tabs[1]:
        st.markdown(
            "Tape une commande puis **Entrée** (ex: `AddObj O1`, `AddRole R1`, `GrantPermission R1 R O1`, "
            "`AddSub S1 [R1]`, `S2 AddObj O2`, `S2 Grant S3 O2 R`, "
            "`RemoveCh S1 R O1`, `Never {A,B} for E1`, `show`, …)"
        )

        st.text_input(
            "C:\\>",
            key="cmd_input",
            placeholder="Ex: AddSub S1 R1",
            on_change=_run_command_callback,
        )

        st.text_area("Historique", "\n\n".join(st.session_state.history), height=300)

        # 👀 Table de debug pour voir les données réellement utilisées
        with st.expander("Données courantes (après commandes)"):

            st.dataframe(st.session_state.global_data, use_container_width=True)

        if not st.session_state.global_data.empty:
            st.markdown("---")
            st.subheader("Graphes (issus des commandes)")
            process_data_display(st.session_state.global_data)

if __name__ == "__main__":
    main()
