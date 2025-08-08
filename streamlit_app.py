# Bloc 1 : Importations, Tarjan, propagation, affichage des graphes et tableau

import pandas as pd
import networkx as nx
from pyvis.network import Network
from IPython.display import display, HTML, Markdown
from ipywidgets import FileUpload, Output, Textarea
from ipywidgets import FileUpload, Text, Button, VBox, Output, Textarea
from tabulate import tabulate
from ipywidgets import VBox, Textarea, Output, FileUpload

import io
import time
import random
import matplotlib.pyplot as plt



from IPython.core.display import HTML

display(HTML("""
<style>
.custom-table {
    border-collapse: collapse;
    width: 100%;
    font-size: 16px;

}

.custom-table th, .custom-table td {
    border: 1px solid black;  /* ✅ Lignes pleines noires */
    padding: 8px;
}

.custom-table th {
    background-color: #f2f2f2;
    font-weight: bold;
}
</style>
"""))


entity_types = {}
entity_instances = {}
global_data = pd.DataFrame(columns=['Source', 'Permission', 'Target'])
output = Output()
command_history = []

# 🔹 Tarjan et propagation

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
                neighbor_component = frozenset(component_map[neighbor])
                current_component = frozenset(component_map[node])
                labels[neighbor_component].update(labels[current_component])
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

def display_table(components, labels, role_data):
    data = {
        'Entities': [', '.join(sorted(comp)) for comp in components],
        'Their labels': ['{' + ', '.join(sorted(label | set(comp))) + '}' for comp, label in zip(components, labels)],
        'Nombre d\'étiquettes': [len(label) for label in labels]
    }
    df = pd.DataFrame(data)
    df = df.sort_values(by='Nombre d\'étiquettes', ascending=False).drop(columns='Nombre d\'étiquettes')
    display(HTML('<h4>Table of entities and labels</h4>'))
    display(HTML(df.to_html(index=False, border=1, classes='styled-table')))

    return df

def display_role_table(data):
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
            for p in perm.split(','):
                perms_set.add(p.strip())
            role_permissions_map[role][obj] = ','.join(sorted(perms_set))

    table_data = []
    for role in roles:
        row = [role] + [role_permissions_map[role].get(obj, '') for obj in all_objects]
        table_data.append(row)

    df_role = pd.DataFrame(table_data, columns=['Roles'] + all_objects)

    # ✅ HTML avec style pour ligne pleine
    html_table = df_role.to_html(index=False, border=1, classes="styled-table")


    style = """
        <style>
        .table-container {
            display: flex;
            gap: 60px;
            flex-wrap: wrap;
        }
        table {
            border-collapse: collapse;
            width: auto;
            font-size: 15px;
            margin- top: 200;
        }
        th, td {
            border: 2px solid black;
            padding: 6px 14px;
            text-align: center;
        }
        th {
            background-color: blue;
            font-weight: bold;
        }


      .styled-table tr {
            background-color: black;
            font-weight: bold;
            border: 1px solid black;
        }


        </style>
        """

    display(HTML(style + "<h4>Table of roles and permissions</h4>" + html_table))


def draw_combined_graph(components_1, adj_1, labels_1, components_2, labels_2, simplified_edges_2, role_data):
    net = Network(notebook=True, height='750px', width='100%', directed=True, cdn_resources='in_line')

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
        subjects = [s for s in component if s.startswith("S")]
        objects = [o for o in component if o.startswith("O")]

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

    positions = {
        0: (-x_gap, 450),
        1: (0, 0),
        2: (x_gap, 800)
    }
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

    net.set_options("""
    var options = {
      "nodes": {
        "font": {"size": 50},
        "shapeProperties": {"borderRadius": 5},
        "size": 40,
        "fixed": {"x": false, "y": false}
      },
      "edges": {
        "width": 4,
        "arrows": {"to": {"enabled": true, "scaleFactor": 1.5}},
        "length": 150,
        "smooth": {"enabled": false}
      },
      "physics": {"enabled": false},
      "interaction": {"dragNodes": true, "dragView": true, "zoomView": true}
    }
    """)

    net.show("combined_graph.html")
    display(HTML("combined_graph.html"))


# ✅ Bloc 2 : apply_permissions, process_data, etc.
def apply_permissions(data):
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

        permissions = permission_value.split(",")

        for permission in permissions:
            permission = permission.strip()
            if permission == 'R':
                adj[target].append(source)
            elif permission == 'W':
                adj[source].append(target)

    for subject, roles_list in subject_roles.items():
        for role in roles_list:
            role_rows = data[(data['Role'].str.contains(role, na=False)) & (data['Permission'].str.contains('R', na=False))]
            for _, role_row in role_rows.iterrows():
                target = role_row['Target']
                if pd.notna(target) and subject != role_row['Source']:
                    adj[target].append(subject)

    for key in adj.keys():
        adj[key] = list(set(adj[key]))

    return adj


def process_data(data):
    output.clear_output()
    with output:
        if data is None or data.empty:
           
            return

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

        connected_nodes = set()
        for node, neighbors in adj.items():
            if neighbors:
                connected_nodes.add(node)
                connected_nodes.update(neighbors)

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

        from ipywidgets import HBox, Output

        table_output = Output()
        role_output = Output()

        with table_output:
            display_table(scc_filtered, labels_filtered, role_data)

        with role_output:
            display_role_table(data)

        display(HBox([table_output, role_output]))
        draw_combined_graph(scc_filtered, adj, labels_filtered, scc_filtered, labels_filtered, simplified_edges, role_data)




interdictions_globales = []
interdictions_entites = {}


def combinaison_interdite(etiquette, source):
    etiquette_set = set(etiquette)
    for interdit in interdictions_globales:
        if set(interdit).issubset(etiquette_set):
            return True
    for entite, combinaisons in interdictions_entites.items():
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

    plt.figure(figsize=(8, 5))
    bar_width = 0.35
    indices = range(len(temps_tarjan))

    plt.bar(indices, temps_tarjan, bar_width, label='SCC Detection (Tarjan)')
    plt.bar([i + bar_width for i in indices], temps_labels, bar_width, label='Label Propagation')
    plt.xlabel("Entity Count")
    plt.ylabel("Time (s)")
    plt.title(f"Performance for {nb_entites} entities")
    plt.xticks([i + bar_width / 2 for i in indices], [str(nb_entites)])
    plt.legend()
    plt.tight_layout()
    plt.show()

# Structures globales
roles_definis = set()
role_permissions = {}
subject_roles = {}
ownership = {}
objet_proprietaire = {}
sujets_definis = set()
objets_definis = set()

def apply_prompt(global_data, prompt):
    try:
        parts = prompt.split()
        if len(parts) == 0:
            return "💬 Empty command"

        command = parts[0]
        args = parts[1:]
        messages = [f"💬 Command executed: C:\\> {' '.join(parts)}"]

        if command == "EvalPerf":
            total_entites = len(sujets_definis | objets_definis)
            if total_entites == 0:
                return "\n".join(messages + ["⚠️ No entities defined. Please create subjects or objects first."])
            evaluer_performance_interface(total_entites)
            return "\n".join(messages)

        if command == "AddObj":
            if len(parts) == 2:
                obj = parts[1]
                objets_definis.add(obj)
                new_entry = pd.DataFrame([[obj, None, None, None]], columns=['Source', 'Target', 'Permission', 'Role'])
                global_data = pd.concat([global_data, new_entry], ignore_index=True)
                messages.append(f"✅ Object '{obj}' is added\n")
                return global_data, "\n".join(messages)
            elif len(parts) == 3:
                owner, obj = parts[1], parts[2]
                sujets_definis.add(owner)
                objets_definis.add(obj)
                objet_proprietaire[obj] = owner
                new_entries = pd.DataFrame([
                    [obj, None, None, None],
                    [owner, obj, 'R', None]
                ], columns=['Source', 'Target', 'Permission', 'Role'])
                global_data = pd.concat([global_data, new_entries], ignore_index=True)
                messages.append(f"✅ Object '{obj}' is added with owner '{owner}' and read permission\n")
                return global_data, "\n".join(messages)

        # ✅ RBAC : Ajouter un rôle
        if command == "AddRole":
            if len(args) != 1:
                return global_data, "❌ Usage: AddRole R1"
            role = args[0]
            roles_definis.add(role)
            role_permissions.setdefault(role, set())
            messages.append(f"✅ Role '{role}' added.")
            return global_data, "\n".join(messages)

        elif command == "AddSub":
            if len(args) < 1:
                return global_data, "❌ Usage: AddSub S1 [R1]"
            subject = args[0]
            role = args[1] if len(args) > 1 else None
            sujets_definis.add(subject)
            subject_roles.setdefault(subject, set())
            role_text = f" with role '{role}'" if role else ""
            new_entry = pd.DataFrame([[subject, None, None, role]], columns=global_data.columns)
            global_data = pd.concat([global_data, new_entry], ignore_index=True)
            if role:
                roles_definis.add(role)
                subject_roles[subject].add(role)
                # 🔁 Propagation : ajouter toutes les permissions déjà assignées à ce rôle
                for perm, obj in role_permissions.get(role, set()):
                    entry = pd.DataFrame([[subject, perm, obj, role]], columns=global_data.columns)
                    global_data = pd.concat([global_data, entry], ignore_index=True)
            messages.append(f"✅ Subject '{subject}' added{role_text}.")
            return global_data, "\n".join(messages)

        elif command == "GrantPermission":
            if len(args) != 3:
                return global_data, "❌ Usage: GrantPermission R1 R O1"
            role, perm, obj = args
            if role not in roles_definis:
                return global_data, f"❌ Role '{role}' is not defined."
            role_permissions.setdefault(role, set()).add((perm, obj))
            # 🔁 Propagation à tous les sujets ayant ce rôle
            for subj in subject_roles:
                if role in subject_roles[subj]:
                    entry = pd.DataFrame([[subj, perm, obj, role]], columns=global_data.columns)
                    global_data = pd.concat([global_data, entry], ignore_index=True)
            messages.append(f"✅ Permission '{perm}' on '{obj}' granted to role '{role}' and propagated.")
            return global_data, "\n".join(messages)

        elif command == "RevokePermission":
          if len(args) != 3:
              return global_data, "❌ Usage: RevokePermission R1 R O1"

          role, perm, obj = args
          if role not in roles_definis:
              return global_data, f"⛔ Error: Role '{role}' does not exist."

          # Supprimer de role_permissions
          if role in role_permissions:
              role_permissions[role].discard((perm, obj))

          # Supprimer de global_data toutes les permissions propagées par ce rôle
          before_count = len(global_data)
          global_data = global_data[~(
              (global_data['Permission'] == perm) &
              (global_data['Target'] == obj) &
              (global_data['Role'] == role)
          )]
          after_count = len(global_data)
          deleted_count = before_count - after_count

          messages.append(f"🗑️ Permission '{perm}' on '{obj}' revoked from role '{role}' ({deleted_count} propagation(s) removed).")
          return global_data, "\n".join(messages)

        elif command == "DeassignUser":
          if len(args) != 2:
              return global_data, "❌ Usage: DeassignUser S1 R1"

          subject, role = args
          if subject not in sujets_definis:
              return global_data, f"⛔ Error: Subject '{subject}' does not exist."
          if role not in roles_definis:
              return global_data, f"⛔ Error: Role '{role}' does not exist."
          if role not in subject_roles.get(subject, set()):
              return global_data, f"ℹ️ Subject '{subject}' does not have role '{role}'."

          # Retirer le rôle
          subject_roles[subject].remove(role)

          # Supprimer les permissions propagées de ce rôle vers ce sujet
          before_count = len(global_data)
          global_data = global_data[~(
              (global_data['Source'] == subject) &
              (global_data['Role'] == role)
          )]
          after_count = len(global_data)
          deleted_count = before_count - after_count

          messages.append(f"🗑️ Role '{role}' removed from subject '{subject}' ({deleted_count} propagated permission(s) removed).")
          return global_data, "\n".join(messages)



                 # ✅ RBAC : Supprimer un rôle
        if command == "RemoveRole":
            if len(parts) != 2:
                messages.append("Usage : RemoveRole nom_du_rôle")
                return global_data, "\n".join(messages)
            role = parts[1]
            if role not in roles_definis:
              messages.append(f"⛔ Error: Role '{role}'  does not exist.")
              return global_data, "\n".join(messages)

            roles_definis.remove(role)
            role_permissions.pop(role, None)
          
        elif command == "ModifyRole":
            if len(args) != 2:
                return global_data, "❌ Usage: ModifyRole OldRole NewRole"

            old_role, new_role = args
            if old_role not in roles_definis:
                return global_data, f"⛔ Error: Role '{old_role}' does not exist."
            if new_role in roles_definis:
                return global_data, f"⛔ Error: Role '{new_role}' already exists."

            roles_definis.remove(old_role)
            roles_definis.add(new_role)

            role_permissions[new_role] = role_permissions.pop(old_role)

            for subj in subject_roles:
                if old_role in subject_roles[subj]:
                    subject_roles[subj].remove(old_role)
                    subject_roles[subj].add(new_role)

            global_data.loc[global_data['Role'] == old_role, 'Role'] = new_role

            messages.append(f"✏️ Role renamed: '{old_role}' ➝ '{new_role}'")
            return global_data, "\n".join(messages)

        elif command == "ModifyPermission":
            if len(parts) != 5:
                messages.append("❌ Usage: ModifyPermission R1 OldPerm Target NewPerm")
                return global_data, "\n".join(messages)

            role, old_perm, target, new_perm = parts[1:5]

            if role not in roles_definis:
                messages.append(f"⛔ Error: Role '{role}' does not exist.")
                return global_data, "\n".join(messages)

            # Mise à jour dans role_permissions si la permission existe
            if (old_perm, target) not in role_permissions.get(role, set()):
                messages.append(f"⚠️ Permission '{old_perm}' on '{target}' not found in role '{role}'.")
                return global_data, "\n".join(messages)

            role_permissions[role].remove((old_perm, target))
            role_permissions[role].add((new_perm, target))

            # Mise à jour dans global_data
            condition = (
                (global_data['Role'] == role) &
                (global_data['Permission'] == old_perm) &
                (global_data['Target'] == target)
            )
            modified_count = global_data[condition].shape[0]
            global_data.loc[condition, 'Permission'] = new_perm

            messages.append(f"🔁 Permission modified: Role '{role}' – {old_perm} ➝ {new_perm} on '{target}' ({modified_count} entries updated).")
            return global_data, "\n".join(messages)



            # Supprimer uniquement le rôle de subject_roles (ne pas supprimer les sujets eux-mêmes)
            for subject in subject_roles:
                if role in subject_roles[subject]:
                    subject_roles[subject].remove(role)

            # Supprimer uniquement les permissions liées à ce rôle
            global_data = global_data[global_data['Role'] != role]

            messages.append(f"🗑️ Role '{role}' successfully deleted and its permissions removed.")
            return global_data, "\n".join(messages)

            roles_definis.remove(role)
            role_permissions.pop(role, None)
            # Supprimer ce rôle de tous les sujets
            for subject in list(subject_roles.keys()):
                if role in subject_roles[subject]:
                    subject_roles[subject].remove(role)
            global_data = global_data[global_data['Role'] != role]
            messages.append(f"🗑️ Role '{role}' successfully deleted.")
            return global_data, "\n".join(messages)

        # ✅ MAC : Grant d’un propriétaire à un autre sujet
        # 🔸 Ajout de sujet
       # ✅ Création de sujet
        if command == "AddSub" and len(parts) == 2:
            subject = parts[1]
            if subject in sujets_definis:
                messages.append(f"ℹ️ The Subject  '{subject}' already exists.")
            else:
                sujets_definis.add(subject)
                messages.append(f"✅ Subject '{subject}' created.")
            return global_data, "\n".join(messages)

        # ✅ DAC – Création d'objet avec propriétaire et canal de lecture (ex : S2 AddObj O2)
        elif len(parts) >= 3 and parts[1] == "AddObj":
            owner, obj = parts[0], parts[2]

            if owner not in sujets_definis:
                messages.append(f"⛔ Error: Subject '{owner}' does not exist. Use AddSub first.")
            if obj in objets_definis:
                messages.append(f"ℹ️ The object '{obj}' already exists.")
                return global_data, "\n".join(messages)

            objets_definis.add(obj)

            entry_owner = pd.DataFrame([[owner, obj, 'Owner', None]], columns=['Source', 'Target', 'Permission', 'Role'])
            

            global_data = pd.concat([global_data, entry_owner], ignore_index=True)

            messages.append(f"✅ Object '{obj}' created with owner '{owner}'")
            return global_data, "\n".join(messages)

        # ✅ DAC – Attribution de permission par le propriétaire (ex : S2 Grant S3 O2 R)
        elif len(parts) >= 5 and parts[1] == "Grant":
            owner, _, subject, obj, perm = parts[:5]

            if owner not in sujets_definis:
               output.append_stdout(f"⛔ Error: Subject '{owner}' does not exist.")
               return global_data, "\n".join(messages)
            if subject not in sujets_definis:
                messages.append(f"⛔ Error: Target subject '{subject}' does not exist.")
                return global_data, "\n".join(messages)
            if obj not in objets_definis:
               messages.append(f"⛔ Error: Object '{obj}' does not exist.")
               return global_data, "\n".join(messages)

            # Vérification de la propriété
            is_owner = ((global_data['Source'] == owner) &
                        (global_data['Target'] == obj) &
                        (global_data['Permission'] == 'Owner')).any()

            if is_owner:
                new_entry = pd.DataFrame([[subject, obj, perm, None]], columns=['Source', 'Target', 'Permission', 'Role'])
                global_data = pd.concat([global_data, new_entry], ignore_index=True)
                messages.append(f"✅ Permission '{perm}' granted to '{subject}' on '{obj}' by '{owner}'.")
            else:
                messages.append(f"⛔Error: '{owner}' is not the owner of '{obj}'.")
            return global_data, "\n".join(messages)

      # ✅ CHINA WALL: AddCh with propagation and restriction check
        elif command == "AddCh":
            source, permission, target = parts[1], parts[2], parts[3]
            role = parts[4] if len(parts) > 4 else None
            temp_data = pd.concat([global_data, pd.DataFrame([[source, target, permission, role]], columns=['Source', 'Target', 'Permission', 'Role'])], ignore_index=True)
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
                for interdit in interdictions_globales:
                    if set(interdit).issubset(comp):
                        messages.append(f"⛔ CHINA WALL ERROR: Global restriction violated for {interdit}\n")
                        return global_data, "\n".join(messages)
                for entite, combinaisons in interdictions_entites.items():
                    if entite in comp:
                        for interdit in combinaisons:
                            if set(interdit).issubset(comp):
                                messages.append(f"⛔ CHINA WALL ERROR: Restriction violated for {entite}: {interdit}\n")
                                return global_data, "\n".join(messages)
            new_entry = pd.DataFrame([[source, target, permission, role]], columns=['Source', 'Target', 'Permission', 'Role'])
            global_data = pd.concat([global_data, new_entry], ignore_index=True)
            messages.append(f"✅ Channel added: {source} --{permission}/{role}--> {target}\n")
            return global_data, "\n".join(messages)

        # ✅ CHINA WALL: Never
        elif command == "Never":
            if 'for' in parts:
                idx_for = parts.index('for')
                etiquettes = [e.strip("{} ,") for e in parts[1:idx_for]]
                entites = [e.strip("{} ,") for e in parts[idx_for + 1:]]
                for entite in entites:
                    interdictions_entites.setdefault(entite, []).append(etiquettes)
                messages.append(f"🚧 Forbidden combination {etiquettes} for entities: {entites}\n")
            else:
                etiquettes = [e.strip("{} ,") for e in parts[1:]]
                interdictions_globales.append(etiquettes)
                messages.append(f"🚧 Globally forbidden combination: {etiquettes}\n")
            return global_data, "\n".join(messages)

        elif command == "RemoveCh":
            if len(parts) == 4:
                # RemoveCh S1 R O1
                source, permission, target = parts[1:4]
                before_rows = len(global_data)
                global_data = global_data[
                    ~(
                        (global_data['Source'] == source) &
                        (global_data['Permission'] == permission) &
                        (global_data['Target'] == target)
                    )
                ]
                after_rows = len(global_data)
                removed = before_rows - after_rows
                if removed == 0:
                    messages.append(f"⚠️ No channel found matching '{source} {permission} {target}'.")
                else:
                    messages.append(f"🗑️ Channel removed: {source} --{permission}--> {target}")
                return global_data, "\n".join(messages)

            elif len(parts) == 3:
                # RemoveCh S1 O1
                source, target = parts[1:3]
                before_rows = len(global_data)
                global_data = global_data[
                    ~(
                        (global_data['Source'] == source) &
                        (global_data['Target'] == target)
                    )
                ]
                after_rows = len(global_data)
                removed = before_rows - after_rows
                if removed == 0:
                    messages.append(f"⚠️ No channel found between '{source}' and '{target}'.")
                else:
                    messages.append(f"🗑️ All channels removed between '{source}' and '{target}'.")
                return global_data, "\n".join(messages)

            else:
                messages.append("❌ Usage: RemoveCh Source [Permission] Target")
                return global_data, "\n".join(messages)


        # ✅ Supprimer un sujet
        elif command == "RemoveSub":
          if len(parts) != 2:
              messages.append("❌ Usage: RemoveSub S1")
              return global_data, "\n".join(messages)
          subject = parts[1]

          sujets_definis.discard(subject)
          subject_roles.pop(subject, None)

          # Supprimer uniquement les lignes où ce sujet est source (mais pas les objets ou autres sujets)
          global_data = global_data[global_data['Source'] != subject]

          messages.append(f"🗑️ Subject '{subject}' removed and its associated permissions cleared.")
          return global_data, "\n".join(messages)


        # ✅ Supprimer un objet
        elif command == "RemoveObj":
            if len(parts) != 2:
                messages.append("❌ Usage: RemoveObj O1")
                return global_data, "\n".join(messages)
            obj = parts[1]

            objets_definis.discard(obj)
            objet_proprietaire.pop(obj, None)

            # Supprimer uniquement les lignes où cet objet est Source ou Target
            global_data = global_data[
                (global_data['Source'] != obj) &
                (global_data['Target'] != obj)
            ]

            messages.append(f"🗑️ Object '{obj}' removed and its associated channels cleared.")
            return global_data, "\n".join(messages)


        # ✅ Modifier un chemin
        elif command == "modifyCh":
            old_source, old_perm, old_target, new_source, new_perm, new_target = parts[1:7]
            global_data.loc[(global_data['Source'] == old_source) &
                            (global_data['Target'] == old_target) &
                            (global_data['Permission'] == old_perm),
                            ['Source', 'Target', 'Permission']] = [new_source, new_target, new_perm]
            messages.append(f"🔁Path modified: {old_source} → {old_target} becomes {new_source} → {new_target}")
            return global_data, "\n".join(messages)

        # ✅ Modifier un sujet
        elif command == "modifySub":
            old_subject, new_subject = parts[1], parts[2]
            if old_subject in sujets_definis:
                sujets_definis.remove(old_subject)
                sujets_definis.add(new_subject)
            global_data.loc[global_data['Source'] == old_subject, 'Source'] = new_subject
            global_data.loc[global_data['Target'] == old_subject, 'Target'] = new_subject
            messages.append(f"✏️ Subject renamed: {old_subject} → {new_subject}")
            return global_data, "\n".join(messages)

        # ✅ Modifier un objet
        elif command == "modifyObj":
            old_obj, new_obj = parts[1], parts[2]
            if old_obj in objets_definis:
                objets_definis.remove(old_obj)
                objets_definis.add(new_obj)
            global_data.loc[global_data['Source'] == old_obj, 'Source'] = new_obj
            global_data.loc[global_data['Target'] == old_obj, 'Target'] = new_obj
            messages.append(f"✏️ Object renamed : {old_obj} → {new_obj}")
            return global_data, "\n".join(messages)

        # ✅ Exécution finale
        elif command == "show":
          result_msg = "\n🚀 Execution des permissions et génération des graphes..."
          history_display.value += result_msg
          output.clear_output()
          with output:
              process_data(global_data)  # ✅ Ceci affiche les graphes et tableau dans la page blanche
          return global_data, "\n".join(messages)


        else:
            messages.append("Command not recognized.")
            return global_data, "\n".join(messages)

    except Exception as e:
        messages.append(f"❌ Error executing command : {e}")
        return global_data, "\n".join(messages)

def handle_command(event):
    global global_data, command_history
    prompt = event.new.strip()
    if not prompt:
        return
        command_history.append(prompt)
        global_data = apply_prompt(global_data, prompt)
        command_input.value = ""
        history_display.value = "\n".join(command_history)
from ipywidgets import RadioButtons, Button, VBox, Output, Textarea

# ✅ Zone globale
global_data = pd.DataFrame(columns=['Source', 'Permission', 'Target', 'Role'])
terminal_output = Output()
command_input = Textarea()
history_display = Textarea()

def setup_terminal_interface():
    global command_input, history_display, global_data

  
    # ✅ Champ de saisie : exécution uniquement après Entrée
    command_input = Textarea(
        value='',
        placeholder="Type your command here and press Enter...",
        description='C:\\>',
        layout={'width': '100%'}
    )

    history_display = Textarea(
        value='',
        layout={'width': '100%', 'height': '350px'},
        description='Historical:',
        disabled=True
    )

    # ✅ Fonction exécutée à chaque appui sur Enter
    def on_enter(change):
        if change['name'] == 'value' and change['new'].endswith('\n'):
            prompt = change['new'].strip()
            if prompt:
                global global_data
                global_data, message = apply_prompt(global_data, prompt)
                history_display.value += f"\n{message}"
                command_input.value = ''  # Vider la zone de saisie

    # 🔁 Observer les modifications de la zone de commande
    command_input.observe(on_enter, names='value')

    # ✅ Afficher les deux zones
    display(VBox([output, history_display, command_input]))



def main():
    global global_data, command_input, terminal_output

    output_zone = Output()
    choix = RadioButtons(
        options=[('📂 Load Excel file', '1'), ('⌨️ Terminal commands', '2')],
        description='Choose:',
        disabled=False
    )

    bouton_valider = Button(description="✅ Confirm Choice")

    def on_choice_submit(_):
        output_zone.clear_output()
        with output_zone:
            if choix.value == '1':
                print("📥 Please upload your Excel file.")
                uploader = FileUpload(accept='.xlsx', multiple=False)
                display(VBox([output, uploader]))

                def on_upload_change(change):
                    if uploader.value:
                        uploaded_file = next(iter(uploader.value.values()))
                        content = uploaded_file['content']
                        df = pd.read_excel(io.BytesIO(content))

                        expected_columns = {'Source', 'Permission', 'Target', 'Role'}
                        missing = expected_columns - set(df.columns)
                        if missing:
                            print(f"⚠️ Missing columns in the file: {missing}")
                            return

                        print("✅ Excel file loaded successfully.")
                        global global_data
                        global_data = df

                        # 🔁 Propagation des permissions RBAC pour fichier Excel
                        subject_roles = {}
                        role_permissions = {}

                        for _, row in df.iterrows():
                            source = row['Source']
                            permission = row['Permission']
                            target = row['Target']
                            role = row['Role']

                            if pd.notna(source) and pd.notna(role):
                                subject_roles.setdefault(source, set()).add(role)

                            if pd.notna(role) and pd.notna(permission) and pd.notna(target):
                                role_permissions.setdefault(role, set()).add((permission, target))

                        for subject, roles in subject_roles.items():
                            for role in roles:
                                for perm, obj in role_permissions.get(role, set()):
                                    condition = (
                                        (global_data['Source'] == subject) &
                                        (global_data['Permission'] == perm) &
                                        (global_data['Target'] == obj)
                                    )
                                    if not condition.any():
                                        row_data = [subject, perm, obj, role]
                                        while len(row_data) < len(global_data.columns):
                                            row_data.append(None)
                                        new_entry = pd.DataFrame([row_data], columns=global_data.columns)
                                        global_data = pd.concat([global_data, new_entry], ignore_index=True)

                        process_data(global_data)

                uploader.observe(on_upload_change, names='value')
                display(VBox([output, uploader]))

            elif choix.value == '2':
                setup_terminal_interface()

    bouton_valider.on_click(on_choice_submit)
    display(VBox([choix, bouton_valider, output_zone]))

# ✅ Lancement automatique
main()