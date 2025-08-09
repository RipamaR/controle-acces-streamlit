# streamlit_app.py
# ============================================================
# Adaptation Streamlit de TON code (RBAC, DAC, China-Wall, Terminal)
# - Affichage PyVis PLEIN ÉCRAN (100% largeur + hauteur viewport)
# - Lecture Excel (openpyxl) + Propagation RBAC depuis Excel
# - Conservation de TOUTES les commandes existantes
# ============================================================

import io
import time
import random
import pandas as pd
import networkx as nx
import matplotlib.pyplot as plt
import streamlit as st
from pyvis.network import Network
from streamlit.components.v1 import html as st_html

# ============== CONFIG PAGE (largeur max pour plein écran) ==============
st.set_page_config(page_title="Contrôle d'accès – Streamlit", layout="wide")

# ========================= ÉTAT GLOBAL =========================
def init_state():
    # DataFrame principal
    if "global_data" not in st.session_state:
        st.session_state.global_data = pd.DataFrame(
            columns=['Source', 'Permission', 'Target', 'Role']
        )
    # Structures (reprise 1:1 de ton code)
    defaults = {
        "entity_types": {},
        "entity_instances": {},
        "command_history": [],
        "interdictions_globales": [],
        "interdictions_entites": {},
        "roles_definis": set(),
        "role_permissions": {},
        "subject_roles": {},
        "ownership": {},
        "objet_proprietaire": {},
        "sujets_definis": set(),
        "objets_definis": set(),
    }
    for k, v in defaults.items():
        if k not in st.session_state:
            st.session_state[k] = v

init_state()

# ====================== OUTILS AFFICHAGE HTML ======================
def _css_tables_once():
    st.markdown(
        """
        <style>
        .custom-table {
            border-collapse: collapse;
            width: 100%;
            font-size: 16px;
        }
        .custom-table th, .custom-table td {
            border: 1px solid black;
            padding: 8px;
        }
        .custom-table th {
            background-color: #f2f2f2;
            font-weight: bold;
        }
        </style>
        """,
        unsafe_allow_html=True,
    )

_css_tables_once()

# ======================= ALGO TARJAN & LABELS =======================
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
                current_component = frozenset(component_map[node])
                labels[neighbor_comp].update(labels[current_component])
                dfs(neighbor, visited)

    for comp in components:
        for node in comp:
            dfs(node, set())

    return [labels[frozenset(comp)] for comp in components]

def simplify_relations(labels):
    reduced_graph = nx.DiGraph()
    label_map = {i: label_set for i, label_set in enumerate(labels)}

    for i, label_set in enumerate(labels):
        for j, other_label_set in enumerate(labels):
            if i != j and label_set.issubset(other_label_set):
                reduced_graph.add_edge(i, j)

    transitive_edges = set()
    for i in range(len(labels)):
        for j in range(len(labels)):
            if i != j and reduced_graph.has_edge(i, j):
                for path in nx.all_simple_paths(reduced_graph, source=i, target=j):
                    if len(path) > 2:
                        transitive_edges.add((i, j))

    for edge in transitive_edges:
        reduced_graph.remove_edge(*edge)

    simplified_edges = [(label_map[src], label_map[dest]) for src, dest in reduced_graph.edges]
    return simplified_edges

# ======================= TABLES (Streamlit) =======================
def display_table(components, labels, role_data):
    data = {
        'Entities': [', '.join(sorted(comp)) for comp in components],
        'Their labels': ['{' + ', '.join(sorted(label | set(comp))) + '}' for comp, label in zip(components, labels)],
        'Nombre d\'étiquettes': [len(label) for label in labels]
    }
    df = pd.DataFrame(data)
    df = df.sort_values(by='Nombre d\'étiquettes', ascending=False).drop(columns='Nombre d\'étiquettes')
    st.markdown("#### Table of entities and labels")
    st.dataframe(df, use_container_width=True)
    return df

def display_role_table(data: pd.DataFrame):
    if 'Role' not in data.columns:
        return
    role_permissions_map = {}
    all_objects = sorted(set(data['Target'].dropna().unique()))
    roles = sorted(set(data['Role'].dropna().unique()))

    for role in roles:
        role_permissions_map[role] = {obj: '' for obj in all_objects}

    for _, row in data.iterrows():
        role = row['Role']
        obj = row['Target']
        perm = row['Permission']
        if pd.notna(role) and pd.notna(obj) and pd.notna(perm):
            perms = role_permissions_map[role].get(obj, '')
            perms_set = set(perms.split(',')) if perms else set()
            for p in str(perm).split(','):
                perms_set.add(p.strip())
            role_permissions_map[role][obj] = ','.join(sorted(perms_set))

    table_data = []
    for role in roles:
        row = [role] + [role_permissions_map[role].get(obj, '') for obj in all_objects]
        table_data.append(row)

    df_role = pd.DataFrame(table_data, columns=['Roles'] + all_objects)
    st.markdown("#### Table of roles and permissions")
    st.dataframe(df_role, use_container_width=True)

# ======================= PYVIS PLEIN ÉCRAN =======================
def render_pyvis_fullscreen(net: Network, height_vh: int = 86):
    html_str = net.generate_html()
    custom_css = f"""
    <style>
      .block-container {{
        padding-top: 0.5rem; padding-bottom: 0rem;
      }}
      #fullwidth-container {{
        width: 100vw;
        margin-left: calc(-50vw + 50%);
      }}
      .pyvis-fullscreen {{
        height: {height_vh}vh;
      }}
      .pyvis-fullscreen iframe {{
        width: 100% !important;
        height: 100% !important;
        border: none;
      }}
    </style>
    """
    wrapped = f"""
    {custom_css}
    <div id="fullwidth-container">
      <div class="pyvis-fullscreen">
        {html_str}
      </div>
    </div>
    """
    st_html(wrapped, height=height_vh * 12, scrolling=True)

# ======================= GRAPHE COMBINÉ =======================
def draw_combined_graph(components_1, adj_1, labels_1, components_2, labels_2, simplified_edges_2, role_data):
    net = Network(notebook=False, height='100%', width='100%', directed=True, cdn_resources='in_line')

    sorted_components_1 = sorted(components_1, key=len, reverse=True)
    sorted_components_2 = sorted(components_2, key=len, reverse=True)

    x_gap = 300
    y_gap = 250
    current_y_subject = 0
    current_y_object = 0
    node_indices = {}
    G1 = nx.DiGraph()

    role_to_subject = {subject: role_data.get(subject, "No role") for subject in adj_1.keys()}

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

    for src_set, dest_set in simplified_edges_2:
        src_index = next(i for i, label in enumerate(labels_2) if label == src_set)
        dest_index = next(i for i, label in enumerate(labels_2) if label == dest_set)
        net.add_edge(base_idx + src_index, base_idx + dest_index, arrows="to")

    # plein écran
    render_pyvis_fullscreen(net, height_vh=86)

# ======================= APPLY PERMISSIONS =======================
def apply_permissions(data: pd.DataFrame):
    roles = set()
    objects = set()
    subject_roles = {}

    for _, row in data.iterrows():
        source = row['Source']
        target = row['Target']
        role_field = row['Role']

        if pd.notna(source):
            subject_roles[source] = [r.strip() for r in str(role_field).split(",") if r.strip() != '']

        if pd.notna(target):
            objects.add(target)

    adj = {v: [] for v in list(subject_roles.keys()) + list(objects)}

    for _, row in data.iterrows():
        source = row['Source']
        permission_value = row['Permission']
        target = row['Target']

        if pd.isna(permission_value) or pd.isna(target):
            continue

        permissions = str(permission_value).split(",")

        for permission in permissions:
            permission = permission.strip()
            if permission == 'R':
                adj[target].append(source)
            elif permission == 'W':
                adj[source].append(target)

    # héritage RBAC lecture par rôle (comme ton code)
    for subject, roles_list in subject_roles.items():
        for role in roles_list:
            role_rows = data[(data['Role'].astype(str).str.contains(role, na=False)) &
                             (data['Permission'].astype(str).str.contains('R', na=False))]
            for _, role_row in role_rows.iterrows():
                target = role_row['Target']
                if pd.notna(target) and subject != role_row['Source']:
                    adj[target].append(subject)

    for key in adj.keys():
        adj[key] = list(set(adj[key]))
    return adj

# ======================= PROCESS (affiche tout) =======================
def process_data(data: pd.DataFrame):
    if data is None or data.empty:
        st.info("Aucune donnée fournie")
        return

    data = data.copy()
    data = data.dropna(subset=['Source'])

    role_data = data[['Source', 'Role']].dropna().set_index('Source')['Role'].to_dict() if 'Role' in data.columns else {}

    adj = apply_permissions(data)

    all_nodes = set(adj.keys())
    for _, row in data.iterrows():
        if pd.notna(row["Target"]) and row["Target"] not in all_nodes:
            all_nodes.add(row["Target"])
            adj[row["Target"]] = []

    vertices = list(all_nodes)

    scc, component_map = tarjan(vertices, adj)

    # filtre (ici idem : tu gardes tout)
    scc_filtered = scc

    component_map_filtered = {node: comp for comp in scc_filtered for node in comp}
    labels = {frozenset(comp): set(comp) for comp in scc_filtered}

    def dfs(node, visited):
        if node in visited:
            return
        visited.add(node)
        for neighbor in adj.get(node, []):
            if neighbor in component_map_filtered:
                neighbor_component = frozenset(component_map_filtered[neighbor])
                current_component = frozenset(component_map_filtered[node])
                labels[neighbor_component].update(labels[current_component])
                dfs(neighbor, visited)

    for comp in scc_filtered:
        for node in comp:
            dfs(node, set())

    labels_filtered = [labels[frozenset(comp)] for comp in scc_filtered]
    simplified_edges = simplify_relations(labels_filtered)

    col1, col2 = st.columns([1, 1])
    with col1:
        display_table(scc_filtered, labels_filtered, role_data)
    with col2:
        display_role_table(data)

    draw_combined_graph(scc_filtered, adj, labels_filtered, scc_filtered, labels_filtered, simplified_edges, role_data)

# ======================= AIDES China-Wall & Perf =======================
def combinaison_interdite(etiquette, source):
    etiquette_set = set(etiquette)
    for interdit in st.session_state.interdictions_globales:
        if set(interdit).issubset(etiquette_set):
            return True
    for entite, combinaisons in st.session_state.interdictions_entites.items():
        for interdit in combinaisons:
            if entite in etiquette_set and set(interdit).issubset(etiquette_set):
                return True
    return False

def evaluer_performance_interface(nb_entites):
    temps_tarjan = []
    temps_labels = []

    G = nx.DiGraph()
    G.add_nodes_from([f"E{i}" for i in range(nb_entites)])
    for i in range(nb_entites):
        for j in range(nb_entites):
            if i != j and random.random() < 0.01:
                G.add_edge(f"E{i}", f"E{j}")

    V = list(G.nodes)
    adj = {node: list(G.successors(node)) for node in G.nodes}

    start = time.time()
    scc = list(nx.strongly_connected_components(G))
    temps_tarjan.append(time.time() - start)

    component_map = {node: comp for comp in scc for node in comp}
    labels = {frozenset(comp): set(comp) for comp in scc}

    def dfs(node, visited, current_label):
        if node in visited:
            return
        visited.add(node)
        for neighbor in adj.get(node, []):
            neighbor_comp = frozenset(component_map.get(neighbor, []))
            current_label.update(labels.get(neighbor_comp, set()))
            dfs(neighbor, visited, current_label)

    start = time.time()
    for comp in scc:
        for node in comp:
            dfs(node, set(), labels[frozenset(comp)])
    temps_labels.append(time.time() - start)

    fig, ax = plt.subplots(figsize=(8, 5))
    bar_width = 0.35
    indices = range(len(temps_tarjan))

    ax.bar(list(indices), temps_tarjan, bar_width, label='SCC Detection (Tarjan)')
    ax.bar([i + bar_width for i in indices], temps_labels, bar_width, label='Label Propagation')
    ax.set_xlabel("Entity Count")
    ax.set_ylabel("Time (s)")
    ax.set_title(f"Performance for {nb_entites} entities")
    ax.set_xticks([i + bar_width / 2 for i in indices])
    ax.set_xticklabels([str(nb_entites)])
    ax.legend()
    st.pyplot(fig)

# ======================= TERMINAL (commandes) =======================
def apply_prompt(global_data: pd.DataFrame, prompt: str):
    try:
        parts = prompt.split()
        if len(parts) == 0:
            return global_data, "💬 Empty command"

        command = parts[0]
        args = parts[1:]
        messages = [f"💬 Command executed: C:\\> {' '.join(parts)}"]

        # -------- Perf ----------
        if command == "EvalPerf":
            total_entites = len(st.session_state.sujets_definis | st.session_state.objets_definis)
            if total_entites == 0:
                return global_data, "\n".join(messages + ["⚠️ No entities defined. Please create subjects or objects first."])
            evaluer_performance_interface(total_entites)
            return global_data, "\n".join(messages)

        # -------- OBJETS / DAC ----------
        if command == "AddObj":
            if len(parts) == 2:
                obj = parts[1]
                st.session_state.objets_definis.add(obj)
                new_entry = pd.DataFrame([[obj, None, None, None]], columns=['Source', 'Permission', 'Target', 'Role'])
                global_data = pd.concat([global_data, new_entry], ignore_index=True)
                messages.append(f"✅ Object '{obj}' is added\n")
                return global_data, "\n".join(messages)
            elif len(parts) == 3:
                owner, obj = parts[1], parts[2]
                st.session_state.sujets_definis.add(owner)
                st.session_state.objets_definis.add(obj)
                st.session_state.objet_proprietaire[obj] = owner
                new_entries = pd.DataFrame([
                    [obj, None, None, None],
                    # ⚠️ pas de lecture auto pour propriétaire (DAC strict)
                    [owner, 'Owner', obj, None],
                ], columns=['Source', 'Permission', 'Target', 'Role'])
                global_data = pd.concat([global_data, new_entries], ignore_index=True)
                messages.append(f"✅ Object '{obj}' is added with owner '{owner}'\n")
                return global_data, "\n".join(messages)

        # -------- RBAC ----------
        if command == "AddRole":
            if len(args) != 1:
                return global_data, "❌ Usage: AddRole R1"
            role = args[0]
            st.session_state.roles_definis.add(role)
            st.session_state.role_permissions.setdefault(role, set())
            messages.append(f"✅ Role '{role}' added.")
            return global_data, "\n".join(messages)

        elif command == "AddSub":
            if len(args) < 1:
                return global_data, "❌ Usage: AddSub S1 [R1]"
            subject = args[0]
            role = args[1] if len(args) > 1 else None
            st.session_state.sujets_definis.add(subject)
            st.session_state.subject_roles.setdefault(subject, set())
            role_text = f" with role '{role}'" if role else ""
            new_entry = pd.DataFrame([[subject, None, None, role]], columns=global_data.columns)
            global_data = pd.concat([global_data, new_entry], ignore_index=True)
            if role:
                st.session_state.roles_definis.add(role)
                st.session_state.subject_roles[subject].add(role)
                # Propagation des permissions déjà assignées à ce rôle
                for perm, obj in st.session_state.role_permissions.get(role, set()):
                    entry = pd.DataFrame([[subject, perm, obj, role]], columns=global_data.columns)
                    global_data = pd.concat([global_data, entry], ignore_index=True)
            messages.append(f"✅ Subject '{subject}' added{role_text}.")
            return global_data, "\n".join(messages)

        elif command == "GrantPermission":
            if len(args) != 3:
                return global_data, "❌ Usage: GrantPermission R1 R O1"
            role, perm, obj = args
            if role not in st.session_state.roles_definis:
                return global_data, f"❌ Role '{role}' is not defined."
            st.session_state.role_permissions.setdefault(role, set()).add((perm, obj))
            # Propagation à tous les sujets ayant ce rôle
            for subj in st.session_state.subject_roles:
                if role in st.session_state.subject_roles[subj]:
                    entry = pd.DataFrame([[subj, perm, obj, role]], columns=global_data.columns)
                    global_data = pd.concat([global_data, entry], ignore_index=True)
            messages.append(f"✅ Permission '{perm}' on '{obj}' granted to role '{role}' and propagated.")
            return global_data, "\n".join(messages)

        elif command == "RevokePermission":
            if len(args) != 3:
                return global_data, "❌ Usage: RevokePermission R1 R O1"
            role, perm, obj = args
            if role not in st.session_state.roles_definis:
                return global_data, f"⛔ Error: Role '{role}' does not exist."
            if role in st.session_state.role_permissions:
                st.session_state.role_permissions[role].discard((perm, obj))
            before_count = len(global_data)
            global_data = global_data[~(
                (global_data['Permission'] == perm) &
                (global_data['Target'] == obj) &
                (global_data['Role'] == role)
            )]
            deleted_count = before_count - len(global_data)
            messages.append(f"🗑️ Permission '{perm}' on '{obj}' revoked from role '{role}' ({deleted_count} propagation(s) removed).")
            return global_data, "\n".join(messages)

        elif command == "DeassignUser":
            if len(args) != 2:
                return global_data, "❌ Usage: DeassignUser S1 R1"
            subject, role = args
            if subject not in st.session_state.sujets_definis:
                return global_data, f"⛔ Error: Subject '{subject}' does not exist."
            if role not in st.session_state.roles_definis:
                return global_data, f"⛔ Error: Role '{role}' does not exist."
            if role not in st.session_state.subject_roles.get(subject, set()):
                return global_data, f"ℹ️ Subject '{subject}' does not have role '{role}'."
            st.session_state.subject_roles[subject].remove(role)
            before_count = len(global_data)
            global_data = global_data[~(
                (global_data['Source'] == subject) &
                (global_data['Role'] == role)
            )]
            deleted_count = before_count - len(global_data)
            messages.append(f"🗑️ Role '{role}' removed from subject '{subject}' ({deleted_count} propagated permission(s) removed).")
            return global_data, "\n".join(messages)

        if command == "RemoveRole":
            if len(parts) != 2:
                messages.append("Usage : RemoveRole nom_du_rôle")
                return global_data, "\n".join(messages)
            role = parts[1]
            if role not in st.session_state.roles_definis:
                messages.append(f"⛔ Error: Role '{role}'  does not exist.")
                return global_data, "\n".join(messages)
            st.session_state.roles_definis.remove(role)
            st.session_state.role_permissions.pop(role, None)

        elif command == "ModifyRole":
            if len(args) != 2:
                return global_data, "❌ Usage: ModifyRole OldRole NewRole"
            old_role, new_role = args
            if old_role not in st.session_state.roles_definis:
                return global_data, f"⛔ Error: Role '{old_role}' does not exist."
            if new_role in st.session_state.roles_definis:
                return global_data, f"⛔ Error: Role '{new_role}' already exists."
            st.session_state.roles_definis.remove(old_role)
            st.session_state.roles_definis.add(new_role)
            st.session_state.role_permissions[new_role] = st.session_state.role_permissions.pop(old_role, set())
            for subj in st.session_state.subject_roles:
                if old_role in st.session_state.subject_roles[subj]:
                    st.session_state.subject_roles[subj].remove(old_role)
                    st.session_state.subject_roles[subj].add(new_role)
            global_data.loc[global_data['Role'] == old_role, 'Role'] = new_role
            messages.append(f"✏️ Role renamed: '{old_role}' ➝ '{new_role}'")
            return global_data, "\n".join(messages)

        elif command == "ModifyPermission":
            if len(parts) != 5:
                messages.append("❌ Usage: ModifyPermission R1 OldPerm Target NewPerm")
                return global_data, "\n".join(messages)
            role, old_perm, target, new_perm = parts[1:5]
            if role not in st.session_state.roles_definis:
                messages.append(f"⛔ Error: Role '{role}' does not exist.")
                return global_data, "\n".join(messages)
            if (old_perm, target) not in st.session_state.role_permissions.get(role, set()):
                messages.append(f"⚠️ Permission '{old_perm}' on '{target}' not found in role '{role}'.")
                return global_data, "\n".join(messages)
            st.session_state.role_permissions[role].remove((old_perm, target))
            st.session_state.role_permissions[role].add((new_perm, target))
            condition = (
                (global_data['Role'] == role) &
                (global_data['Permission'] == old_perm) &
                (global_data['Target'] == target)
            )
            modified_count = global_data[condition].shape[0]
            global_data.loc[condition, 'Permission'] = new_perm
            messages.append(f"🔁 Permission modified: Role '{role}' – {old_perm} ➝ {new_perm} on '{target}' ({modified_count} entries updated).")
            return global_data, "\n".join(messages)

        # -------- DAC : Grant du propriétaire ----------
        if command == "AddSub" and len(parts) == 2:
            subject = parts[1]
            if subject in st.session_state.sujets_definis:
                messages.append(f"ℹ️ The Subject  '{subject}' already exists.")
            else:
                st.session_state.sujets_definis.add(subject)
                messages.append(f"✅ Subject '{subject}' created.")
            return global_data, "\n".join(messages)

        elif len(parts) >= 3 and parts[1] == "AddObj":
            owner, obj = parts[0], parts[2]
            if owner not in st.session_state.sujets_definis:
                messages.append(f"⛔ Error: Subject '{owner}' does not exist. Use AddSub first.")
            if obj in st.session_state.objets_definis:
                messages.append(f"ℹ️ The object '{obj}' already exists.")
                return global_data, "\n".join(messages)
            st.session_state.objets_definis.add(obj)
            entry_owner = pd.DataFrame([[owner, 'Owner', obj, None]], columns=['Source', 'Permission', 'Target', 'Role'])
            global_data = pd.concat([global_data, entry_owner], ignore_index=True)
            messages.append(f"✅ Object '{obj}' created with owner '{owner}'")
            return global_data, "\n".join(messages)

        elif len(parts) >= 5 and parts[1] == "Grant":
            owner, _, subject, obj, perm = parts[:5]
            if owner not in st.session_state.sujets_definis:
                messages.append(f"⛔ Error: Subject '{owner}' does not exist.")
                return global_data, "\n".join(messages)
            if subject not in st.session_state.sujets_definis:
                messages.append(f"⛔ Error: Target subject '{subject}' does not exist.")
                return global_data, "\n".join(messages)
            if obj not in st.session_state.objets_definis:
                messages.append(f"⛔ Error: Object '{obj}' does not exist.")
                return global_data, "\n".join(messages)
            is_owner = ((global_data['Source'] == owner) &
                        (global_data['Target'] == obj) &
                        (global_data['Permission'] == 'Owner')).any()
            if is_owner:
                new_entry = pd.DataFrame([[subject, perm, obj, None]], columns=['Source', 'Permission', 'Target', 'Role'])
                global_data = pd.concat([global_data, new_entry], ignore_index=True)
                messages.append(f"✅ Permission '{perm}' granted to '{subject}' on '{obj}' by '{owner}'.")
            else:
                messages.append(f"⛔Error: '{owner}' is not the owner of '{obj}'.")
            return global_data, "\n".join(messages)

        # -------- China-Wall ----------
        elif command == "AddCh":
            source, permission, target = parts[1], parts[2], parts[3]
            role = parts[4] if len(parts) > 4 else None
            temp_data = pd.concat([global_data, pd.DataFrame([[source, permission, target, role]], columns=['Source', 'Permission', 'Target', 'Role'])], ignore_index=True)
            adj = apply_permissions(temp_data)
            vertices = list(adj.keys())
            scc, component_map = tarjan(vertices, adj)
            labels = {frozenset(comp): set(comp) for comp in scc}

            def dfs(node, visited):
                if node in visited:
                    return
                visited.add(node)
                for neighbor in adj.get(node, []):
                    if neighbor in component_map:
                        neighbor_component = frozenset(component_map[neighbor])
                        labels[neighbor_component].update(labels[frozenset(component_map[node])])
                        dfs(neighbor, visited)

            for comp in scc:
                for node in comp:
                    dfs(node, set())

            for comp in labels.values():
                for interdit in st.session_state.interdictions_globales:
                    if set(interdit).issubset(comp):
                        messages.append(f"⛔ CHINA WALL ERROR: Global restriction violated for {interdit}\n")
                        return global_data, "\n".join(messages)
                for entite, combinaisons in st.session_state.interdictions_entites.items():
                    if entite in comp:
                        for interdit in combinaisons:
                            if set(interdit).issubset(comp):
                                messages.append(f"⛔ CHINA WALL ERROR: Restriction violated for {entite}: {interdit}\n")
                                return global_data, "\n".join(messages)
            new_entry = pd.DataFrame([[source, permission, target, role]], columns=['Source', 'Permission', 'Target', 'Role'])
            global_data = pd.concat([global_data, new_entry], ignore_index=True)
            messages.append(f"✅ Channel added: {source} --{permission}/{role}--> {target}\n")
            return global_data, "\n".join(messages)

        elif command == "Never":
            if 'for' in parts:
                idx_for = parts.index('for')
                etiquettes = [e.strip("{} ,") for e in parts[1:idx_for]]
                entites = [e.strip("{} ,") for e in parts[idx_for + 1:]]
                for entite in entites:
                    st.session_state.interdictions_entites.setdefault(entite, []).append(etiquettes)
                messages.append(f"🚧 Forbidden combination {etiquettes} for entities: {entites}\n")
            else:
                etiquettes = [e.strip("{} ,") for e in parts[1:]]
                st.session_state.interdictions_globales.append(etiquettes)
                messages.append(f"🚧 Globally forbidden combination: {etiquettes}\n")
            return global_data, "\n".join(messages)

        elif command == "RemoveCh":
            if len(parts) == 4:
                source, permission, target = parts[1:4]
                before_rows = len(global_data)
                global_data = global_data[
                    ~(
                        (global_data['Source'] == source) &
                        (global_data['Permission'] == permission) &
                        (global_data['Target'] == target)
                    )
                ]
                removed = before_rows - len(global_data)
                if removed == 0:
                    messages.append(f"⚠️ No channel found matching '{source} {permission} {target}'.")
                else:
                    messages.append(f"🗑️ Channel removed: {source} --{permission}--> {target}")
                return global_data, "\n".join(messages)

            elif len(parts) == 3:
                source, target = parts[1:3]
                before_rows = len(global_data)
                global_data = global_data[
                    ~(
                        (global_data['Source'] == source) &
                        (global_data['Target'] == target)
                    )
                ]
                removed = before_rows - len(global_data)
                if removed == 0:
                    messages.append(f"⚠️ No channel found between '{source}' and '{target}'.")
                else:
                    messages.append(f"🗑️ All channels removed between '{source}' and '{target}'.")
                return global_data, "\n".join(messages)

            else:
                messages.append("❌ Usage: RemoveCh Source [Permission] Target")
                return global_data, "\n".join(messages)

        elif command == "RemoveSub":
            if len(parts) != 2:
                messages.append("❌ Usage: RemoveSub S1")
                return global_data, "\n".join(messages)
            subject = parts[1]
            st.session_state.sujets_definis.discard(subject)
            st.session_state.subject_roles.pop(subject, None)
            global_data = global_data[global_data['Source'] != subject]
            messages.append(f"🗑️ Subject '{subject}' removed and its associated permissions cleared.")
            return global_data, "\n".join(messages)

        elif command == "RemoveObj":
            if len(parts) != 2:
                messages.append("❌ Usage: RemoveObj O1")
                return global_data, "\n".join(messages)
            obj = parts[1]
            st.session_state.objets_definis.discard(obj)
            st.session_state.objet_proprietaire.pop(obj, None)
            global_data = global_data[
                (global_data['Source'] != obj) &
                (global_data['Target'] != obj)
            ]
            messages.append(f"🗑️ Object '{obj}' removed and its associated channels cleared.")
            return global_data, "\n".join(messages)

        elif command == "modifyCh":
            old_source, old_perm, old_target, new_source, new_perm, new_target = parts[1:7]
            global_data.loc[(global_data['Source'] == old_source) &
                            (global_data['Target'] == old_target) &
                            (global_data['Permission'] == old_perm),
                            ['Source', 'Target', 'Permission']] = [new_source, new_target, new_perm]
            messages.append(f"🔁Path modified: {old_source} → {old_target} becomes {new_source} → {new_target}")
            return global_data, "\n".join(messages)

        elif command == "modifySub":
            old_subject, new_subject = parts[1], parts[2]
            if old_subject in st.session_state.sujets_definis:
                st.session_state.sujets_definis.remove(old_subject)
                st.session_state.sujets_definis.add(new_subject)
            global_data.loc[global_data['Source'] == old_subject, 'Source'] = new_subject
            global_data.loc[global_data['Target'] == old_subject, 'Target'] = new_subject
            messages.append(f"✏️ Subject renamed: {old_subject} → {new_subject}")
            return global_data, "\n".join(messages)

        elif command == "modifyObj":
            old_obj, new_obj = parts[1], parts[2]
            if old_obj in st.session_state.objets_definis:
                st.session_state.objets_definis.remove(old_obj)
                st.session_state.objets_definis.add(new_obj)
            global_data.loc[global_data['Source'] == old_obj, 'Source'] = new_obj
            global_data.loc[global_data['Target'] == old_obj, 'Target'] = new_obj
            messages.append(f"✏️ Object renamed : {old_obj} → {new_obj}")
            return global_data, "\n".join(messages)

        elif command == "show":
            st.success("🚀 Execution des permissions et génération des graphes...")
            process_data(global_data)
            return global_data, "\n".join(messages)

        else:
            messages.append("Command not recognized.")
            return global_data, "\n".join(messages)

    except Exception as e:
        messages.append(f"❌ Error executing command : {e}")
        return global_data, "\n".join(messages)

# ======================= UI STREAMLIT =======================
st.title("🔐 Contrôle d'accès – RBAC / DAC / China-Wall (Streamlit)")

tabs = st.tabs(["📂 Fichier Excel", "⌨️ Terminal de commandes"])

# -------- Onglet Excel --------
with tabs[0]:
    st.write("Importe un fichier **.xlsx** avec colonnes : `Source, Permission, Target, Role`.")
    up = st.file_uploader("Choisir un fichier Excel", type=["xlsx"])
    if up:
        try:
    df = pd.read_excel(io.BytesIO(up.read()), engine="openpyxl")
    # Forcer les colonnes manquantes
    for col in ["Source", "Permission", "Target", "Role", "Heritage"]:
        if col not in df.columns:
            df[col] = None
except Exception as e:
    st.error(f"Erreur de lecture du fichier: {e}")


# -------- Onglet Terminal --------
with tabs[1]:
    st.markdown("Tape une commande puis **Entrée** (ex: `AddSub S1 R1`, `AddRole R1`, `GrantPermission R1 R O1`, `AddCh S1 R O1`, `RemoveCh S1 O1`, `ModifyPermission R1 R O1 W`, `show`, …)")
    cmd = st.text_input("C:\\>", value="", placeholder="Ex: AddSub S1 R1")
    if cmd:
        st.session_state.global_data, message = apply_prompt(st.session_state.global_data, cmd)
        st.session_state.command_history.append(f"{message}")
        st.experimental_rerun()

    st.text_area("Historique", "\n".join(st.session_state.command_history), height=300)
