# streamlit_app.py
# -----------------------------------------------------------
# Application Streamlit pour contrôle d'accès (RBAC, DAC, China-Wall)
# Affichage plein écran / pleine largeur + rendu PyVis en HTML
# -----------------------------------------------------------

import io
import time
import random
import pandas as pd
import networkx as nx
import streamlit as st
from pyvis.network import Network
from streamlit.components.v1 import html as st_html


# ===================== CONFIG UI ===========================
st.set_page_config(page_title="Contrôle d'accès – RBAC / DAC / China-Wall",
                   layout="wide")

# ===================== ÉTAT GLOBAL =========================
def init_state():
    if "global_data" not in st.session_state:
        st.session_state.global_data = pd.DataFrame(
            columns=["Source", "Permission", "Target", "Role", "Heritage"]
        )

    defaults = {
        "roles_definis": set(),        # {role}
        "role_permissions": {},        # {role: set((perm, obj))}
        "subject_roles": {},           # {subject: set(roles)}
        "sujets_definis": set(),       # {S1, S2, ...}
        "objets_definis": set(),       # {O1, O2, ...}
        "interdictions_globales": [],  # [[A,B], ...]
        "interdictions_entites": {},   # {E1: [[A,B]], ...}
        "history": [],                 # lignes d'historique du terminal
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
    Construit l'adjacence à partir des permissions :
    - R : Target -> Source  (X peut lire Y => arête Y->X)
    - W : Source -> Target  (X peut écrire Y => arête X->Y)
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

    # dédoublonnage
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

    # role -> obj -> perms string
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
    # Important: notebook=False + rendu via st_html
    net = Network(notebook=False, height='1000px', width='100%', directed=True, cdn_resources='in_line')

    sorted_components_1 = sorted(components_1, key=len, reverse=True)
    sorted_components_2 = sorted(components_2, key=len, reverse=True)

    x_gap = 300
    y_gap = 250
    current_y_subject = 0
    current_y_object = 0
    node_indices = {}
    G1 = nx.DiGraph()

    role_to_subject = {subject: role_data.get(subject, "No role") for subject in adj_1.keys()}

    # Colonne gauche: Sujets (ellipse) ; Colonne droite: Objets (box)
    for component, label in zip(sorted_components_1, labels_1):
        subjects = [s for s in component if str(s).startswith("S")]
        objects = [o for o in component if str(o).startswith("O")]

        for subj in subjects:
            roles = role_to_subject.get(subj, "No role")
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

    # Arêtes (DAG => réduction transitive)
    for src, dest_list in adj_1.items():
        for dest in dest_list:
            if src in node_indices and dest in node_indices:
                G1.add_edge(src, dest)

    if nx.is_directed_acyclic_graph(G1):
        G1 = nx.transitive_reduction(G1)

    for src, dest in G1.edges():
        net.add_edge(src, dest, arrows="to")

    # Boîtes classes d'équivalence
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

    # Rendu Streamlit (clé du problème)
    html_str = net.generate_html()
    st_html(html_str, height=1000,width=1800, scrolling=True)

# =============== RBAC : propagation depuis Excel ===========
def propagate_rbac_from_excel(df: pd.DataFrame) -> pd.DataFrame:
    """
    - Si plusieurs sujets partagent un même rôle, chacun hérite des permissions
      (R/W) de ce rôle sur les mêmes objets.
    - Les lignes héritées reçoivent Heritage='Role' (facultatif).
    """
    df = df.copy()
    if "Role" not in df.columns:
        df["Role"] = None
    if "Heritage" not in df.columns:
        df["Heritage"] = None

    role_perms = {}     # role -> set((perm, obj))
    subject_roles = {}  # subject -> set(roles)

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
        # global
        for interdit in st.session_state.interdictions_globales:
            if set(interdit).issubset(comp):
                return True, f"Combinaison globale interdite: {interdit}"
        # par entité
        for ent, combos in st.session_state.interdictions_entites.items():
            if ent in comp:
                for interdit in combos:
                    if set(interdit).issubset(comp):
                        return True, f"Combinaison interdite pour {ent}: {interdit}"
    return False, ""

# =============== VISUALISATION COMPLÈTE ====================
def process_data_display(df: pd.DataFrame):
    if df is None or df.empty:
        st.info("Aucune donnée à afficher.")
        return

    # 1) Appliquer RBAC (héritage) si nécessaire
    df_expanded = propagate_rbac_from_excel(df)

    # 2) Construire l'adjacence
    adj = apply_permissions(df_expanded)
    V = sorted(set(adj.keys()) | {v for lst in adj.values() for v in lst})

    # 3) SCC + labels
    scc, cmap = tarjan(V, adj)
    labels = propagate_labels(scc, adj, cmap)

    # 4) Vérif China-Wall
    violated, msg = violates_china_wall(labels)
    if violated:
        st.error(f"⛔ CHINA-WALL: {msg}")
        return

    # 5) Tables + Graphes (plein écran/largeur)
    col1, col2 = st.columns([1, 1], gap="large")
    with col1:
        display_entities_table(scc, labels)
    with col2:
        display_role_table_streamlit(df_expanded)

    st.markdown("---")
    simplified_edges = simplify_relations(labels)
    draw_combined_graph(scc, adj, labels, scc, labels, simplified_edges,
                        role_data=df_expanded.set_index("Source")["Role"].to_dict() if "Role" in df_expanded.columns else {})

# =============== TERMINAL DE COMMANDES =====================
def apply_prompt(df: pd.DataFrame, prompt: str):
    parts = prompt.strip().split()
    if not parts:
        return df, "❌ Empty command."

    cmd = parts[0]
    args = parts[1:]
    msg = ""

    # — ENTITÉS (modèle entité simple) —
    if cmd == "AddEnt":
        if len(args) != 1:
            return df, "❌ Usage: AddEnt E1"
        ent = args[0]
        if ((df["Source"] == ent) | (df["Target"] == ent)).any():
            return df, f"⚠️ Entity '{ent}' already exists."
        df = pd.concat([df, pd.DataFrame([{"Source": ent, "Permission": None, "Target": None, "Role": None}])], ignore_index=True)
        return df, f"✅ Entity '{ent}' added."

    if cmd == "AddCh":
        # AddCh E1 E2  => canal entité simple (lecture par défaut)
        if len(args) == 2:
            src, dst = args
            df = pd.concat([df, pd.DataFrame([{"Source": src, "Permission": "R", "Target": dst, "Role": None}])], ignore_index=True)
            return df, f"✅ Channel added: {src} ➜ {dst}"
        # AddCh S1 R O1 [Role] => modèle S/O, permission explicite
        if len(args) >= 3:
            source, permission, target = args[:3]
            role = args[3] if len(args) > 3 else None
            new_row = {"Source": source, "Permission": permission, "Target": target, "Role": role}
            df = pd.concat([df, pd.DataFrame([new_row])], ignore_index=True)
            return df, f"✅ Channel added: {source} --{permission}/{role}--> {target}"
        return df, "❌ Usage: AddCh E1 E2  |  AddCh S1 R O1 [Role]"

    if cmd == "RemoveCh":
        # RemoveCh E1 E2  (entités simples)
        if len(args) == 2:
            src, dst = args
            before = len(df)
            df = df[~((df["Source"] == src) & (df["Target"] == dst))]
            removed = before - len(df)
            return df, f"🗑️ {removed} channel(s) removed between '{src}' and '{dst}'."
        # RemoveCh S1 R O1  (S/O)
        if len(args) == 3:
            src, perm, dst = args
            before = len(df)
            df = df[~((df["Source"] == src) & (df["Permission"] == perm) & (df["Target"] == dst))]
            removed = before - len(df)
            if removed == 0:
                return df, f"⚠️ No channel found matching '{src} {perm} {dst}'."
            return df, f"🗑️ Channel removed: {src} --{perm}--> {dst}"
        return df, "❌ Usage: RemoveCh Source Target  |  RemoveCh Source Permission Target"

    if cmd == "Never":
        # Never {A,B}  ou  Never {A,B} for E1 E2
        if "for" in args:
            idx = args.index("for")
            etiquette = [e.strip("{} ,") for e in args[:idx]]
            entites = [e.strip("{} ,") for e in args[idx + 1:]]
            for ent in entites:
                st.session_state.interdictions_entites.setdefault(ent, []).append(etiquette)
            return df, f"🚧 Forbidden combination {etiquette} for entities {entites}"
        else:
            etiquette = [e.strip("{} ,") for e in args]
            st.session_state.interdictions_globales.append(etiquette)
            return df, f"🚧 Globally forbidden combination: {etiquette}"

    # — RBAC —
    if cmd == "AddRole":
        if len(args) != 1:
            return df, "❌ Usage: AddRole R1"
        role = args[0]
        st.session_state.roles_definis.add(role)
        st.session_state.role_permissions.setdefault(role, set())
        return df, f"✅ Role '{role}' added."

    if cmd == "AddSub":
        # AddSub S1 [R1]
        if len(args) < 1:
            return df, "❌ Usage: AddSub S1 [R1]"
        subj = args[0]
        role = args[1] if len(args) > 1 else None
        st.session_state.sujets_definis.add(subj)
        st.session_state.subject_roles.setdefault(subj, set())
        if role:
            st.session_state.roles_definis.add(role)
            st.session_state.subject_roles[subj].add(role)
        row = {"Source": subj, "Permission": None, "Target": None, "Role": role}
        df = pd.concat([df, pd.DataFrame([row])], ignore_index=True)
        return df, f"✅ Subject '{subj}' added" + (f" with role '{role}'" if role else "")

    if cmd == "GrantPermission":
        # GrantPermission R1 R O1
        if len(args) != 3:
            return df, "❌ Usage: GrantPermission R1 R O1"
        role, perm, obj = args
        if role not in st.session_state.roles_definis:
            return df, f"❌ Role '{role}' is not defined."
        st.session_state.role_permissions.setdefault(role, set()).add((perm, obj))
        # Propagation aux sujets ayant ce rôle
        for subj, roles in st.session_state.subject_roles.items():
            if role in roles:
                df = pd.concat([df, pd.DataFrame([{
                    "Source": subj, "Permission": perm, "Target": obj, "Role": role, "Heritage": "Role"
                }])], ignore_index=True)
        return df, f"✅ Permission '{perm}' on '{obj}' granted to role '{role}' and propagated."

    if cmd == "RevokePermission":
        # RevokePermission R1 R O1
        if len(args) != 3:
            return df, "❌ Usage: RevokePermission R1 R O1"
        role, perm, obj = args
        if role not in st.session_state.roles_definis:
            return df, f"⛔ Error: Role '{role}' does not exist."
        if role in st.session_state.role_permissions:
            st.session_state.role_permissions[role].discard((perm, obj))
        before = len(df)
        df = df[~((df["Permission"] == perm) & (df["Target"] == obj) & (df["Role"] == role))]
        deleted = before - len(df)
        return df, f"🗑️ Permission '{perm}' on '{obj}' revoked from role '{role}' ({deleted} propagation(s) removed)."

    if cmd == "DeassignUser":
        # DeassignUser S1 R1
        if len(args) != 2:
            return df, "❌ Usage: DeassignUser S1 R1"
        subject, role = args
        if subject not in st.session_state.sujets_definis:
            return df, f"⛔ Error: Subject '{subject}' does not exist."
        if role not in st.session_state.roles_definis:
            return df, f"⛔ Error: Role '{role}' does not exist."
        if role not in st.session_state.subject_roles.get(subject, set()):
            return df, f"ℹ️ Subject '{subject}' does not have role '{role}'."
        st.session_state.subject_roles[subject].remove(role)
        before = len(df)
        df = df[~((df["Source"] == subject) & (df["Role"] == role))]
        deleted = before - len(df)
        return df, f"🗑️ Role '{role}' removed from subject '{subject}' ({deleted} propagated permission(s) removed)."

    if cmd == "ModifyRole":
        # ModifyRole OldRole NewRole
        if len(args) != 2:
            return df, "❌ Usage: ModifyRole OldRole NewRole"
        old_role, new_role = args
        if old_role not in st.session_state.roles_definis:
            return df, f"⛔ Error: Role '{old_role}' does not exist."
        if new_role in st.session_state.roles_definis:
            return df, f"⛔ Error: Role '{new_role}' already exists."
        # switch sets
        st.session_state.roles_definis.remove(old_role)
        st.session_state.roles_definis.add(new_role)
        st.session_state.role_permissions[new_role] = st.session_state.role_permissions.pop(old_role, set())
        # pour les sujets
        for subj in st.session_state.subject_roles:
            if old_role in st.session_state.subject_roles[subj]:
                st.session_state.subject_roles[subj].remove(old_role)
                st.session_state.subject_roles[subj].add(new_role)
        # DataFrame
        df.loc[df["Role"] == old_role, "Role"] = new_role
        return df, f"✏️ Role renamed: '{old_role}' ➝ '{new_role}'"

    if cmd == "ModifyPermission":
        # ModifyPermission R1 OldPerm Target NewPerm
        if len(args) != 4:
            return df, "❌ Usage: ModifyPermission R1 OldPerm Target NewPerm"
        role, old_perm, target, new_perm = args
        if role not in st.session_state.roles_definis:
            return df, f"⛔ Error: Role '{role}' does not exist."
        if (old_perm, target) not in st.session_state.role_permissions.get(role, set()):
            return df, f"⚠️ Permission '{old_perm}' on '{target}' not found in role '{role}'."
        # switch dans role_permissions
        st.session_state.role_permissions[role].remove((old_perm, target))
        st.session_state.role_permissions[role].add((new_perm, target))
        # update DataFrame
        mask = (df["Role"] == role) & (df["Permission"] == old_perm) & (df["Target"] == target)
        count = df[mask].shape[0]
        df.loc[mask, "Permission"] = new_perm
        return df, f"🔁 Permission modified: Role '{role}' – {old_perm} ➝ {new_perm} on '{target}' ({count} entries updated)."

    if cmd == "RemoveRole":
        # RemoveRole R1 (supprime le rôle + permissions propagées, pas les sujets)
        if len(args) != 1:
            return df, "❌ Usage: RemoveRole R1"
        role = args[0]
        if role not in st.session_state.roles_definis:
            return df, f"⛔ Error: Role '{role}' does not exist."
        st.session_state.roles_definis.remove(role)
        st.session_state.role_permissions.pop(role, None)
        for subj in st.session_state.subject_roles:
            if role in st.session_state.subject_roles[subj]:
                st.session_state.subject_roles[subj].remove(role)
        df = df[df["Role"] != role]
        return df, f"🗑️ Role '{role}' successfully deleted and its permissions removed."

    # — DAC —
    # S2 AddObj O2  => crée l'objet O2 dont S2 est propriétaire (Owner), pas de lecture auto
    if len(parts) >= 3 and parts[1] == "AddObj":
        owner, obj = parts[0], parts[2]
        if owner not in st.session_state.sujets_definis:
            return df, f"⛔ Error: Subject '{owner}' does not exist. Use AddSub first."
        if obj in st.session_state.objets_definis:
            return df, f"ℹ️ The object '{obj}' already exists."
        st.session_state.objets_definis.add(obj)
        entry_owner = {"Source": owner, "Permission": "Owner", "Target": obj, "Role": None}
        df = pd.concat([df, pd.DataFrame([entry_owner])], ignore_index=True)
        return df, f"✅ Object '{obj}' created with owner '{owner}'"

    # S2 Grant S3 O2 R  => Le propriétaire S2 accorde R à S3 sur O2
    if len(parts) >= 5 and parts[1] == "Grant":
        owner, _, subject, obj, perm = parts[:5]
        if owner not in st.session_state.sujets_definis:
            return df, f"⛔ Error: Subject '{owner}' does not exist."
        if subject not in st.session_state.sujets_definis:
            return df, f"⛔ Error: Target subject '{subject}' does not exist."
        if obj not in st.session_state.objets_definis:
            return df, f"⛔ Error: Object '{obj}' does not exist."
        # Vérifier la propriété
        is_owner = ((df["Source"] == owner) & (df["Target"] == obj) & (df["Permission"] == "Owner")).any()
        if not is_owner:
            return df, f"⛔ Error: '{owner}' is not the owner of '{obj}'."
        new_entry = {"Source": subject, "Permission": perm, "Target": obj, "Role": None}
        df = pd.concat([df, pd.DataFrame([new_entry])], ignore_index=True)
        return df, f"✅ Permission '{perm}' granted to '{subject}' on '{obj}' by '{owner}'."

    if cmd == "show":
        process_data_display(df)
        return df, "🚀 Génération des graphes…"

    return df, "❌ Unknown command."

# ======================= UI ================================
def main():
    st.title("🔐 Contrôle d'accès – RBAC / DAC / China-Wall")

    tabs = st.tabs(["📂 Fichier Excel", "⌨️ Terminal de commandes"])

    # ------- Onglet Excel -------
    with tabs[0]:
        up = st.file_uploader("Importer un fichier Excel (colonnes: Source, Permission, Target, Role, Heritage optionnelle)", type=["xlsx"])
        if up:
            try:
                df = pd.read_excel(io.BytesIO(up.read()))
                required = {"Source", "Permission", "Target"}
                missing = required - set(df.columns)
                if missing:
                    st.error(f"Colonnes manquantes: {missing}")
                else:
                    if "Role" not in df.columns:
                        df["Role"] = None
                    if "Heritage" not in df.columns:
                        df["Heritage"] = None
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
        st.markdown("Tape une commande puis **Entrée** (ex: `AddSub S1 R1`, `AddRole R1`, `GrantPermission R1 R O1`, `AddCh E1 E2`, `S2 AddObj O2`, `S2 Grant S3 O2 R`, `show`, `Never {A,B} for E1`, …)")
        cmd = st.text_input("C:\\>", value="", placeholder="Ex: AddSub S1 R1")
        if cmd:
            st.session_state.global_data, message = apply_prompt(st.session_state.global_data, cmd)
            st.session_state.history.append(f"C:\\> {cmd}\n{message}")
            st.experimental_rerun()

        st.text_area("Historique", "\n\n".join(st.session_state.history), height=320)

if __name__ == "__main__":
    main()
