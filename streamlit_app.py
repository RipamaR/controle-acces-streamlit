# streamlit_app.py
# -----------------------------------------------------------
# Application Streamlit pour contrôle d'accès (RBAC, DAC, China-Wall)
# Affichage plein écran + héritage RBAC (Excel + commandes)
# -----------------------------------------------------------

import io
import time
import random
import pandas as pd
import networkx as nx
import streamlit as st
from pyvis.network import Network
from streamlit.components.v1 import html as st_html
import matplotlib.pyplot as plt


# ================== ÉTAT GLOBAL (Streamlit) ==================
def init_state():
    if "global_data" not in st.session_state:
        st.session_state.global_data = pd.DataFrame(
            columns=["Source", "Permission", "Target", "Role", "Heritage"]
        )

    # Structures RBAC/DAC/China-Wall & historique terminal
    defaults = {
        "roles_definis": set(),
        "role_permissions": {},       # {role: set((perm, obj))}
        "subject_roles": {},          # {subject: set(roles)}
        "sujets_definis": set(),
        "objets_definis": set(),
        "interdictions_globales": [], # China-Wall
        "interdictions_entites": {},  # China-Wall
        "history": [],                # Terminal
    }
    for k, v in defaults.items():
        if k not in st.session_state:
            st.session_state[k] = v


# ================== ALGORITHMES (Tarjan & co) ==================
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
    idx_to_set = {i: label_set for i, label_set in enumerate(labels)}

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

    return [(idx_to_set[u], idx_to_set[v]) for u, v in reduced.edges()]


# ================== CONSTRUCTION DU GRAPHE ====================
def apply_permissions(df: pd.DataFrame):
    """
    Construit l'adjacence à partir des permissions :
    - R : Target -> Source (le lecteur "vient" de l'objet)
    - W : Source -> Target
    """
    adj = {}

    def add_edge(a, b):
        if pd.isna(a) or pd.isna(b):
            return
        adj.setdefault(a, [])
        adj.setdefault(b, [])
        adj[a].append(b)

    for _, row in df.iterrows():
        s, p, t = row["Source"], row["Permission"], row["Target"]
        if pd.isna(p) or pd.isna(t):
            continue
        for perm in str(p).split(","):
            perm = perm.strip()
            if perm == "R":
                add_edge(t, s)   # lecture : O -> S
            elif perm == "W":
                add_edge(s, t)   # écriture : S -> O

    # dédoublonnage
    for k in list(adj.keys()):
        adj[k] = list(sorted(set(adj[k])))

    return adj


def display_table(components, labels):
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


def display_role_table(df: pd.DataFrame):
    """
    Affiche la matrice Rôle x Objets avec permissions cumulées (R/W),
    y compris les lignes héritées (Heritage='Role').
    """
    if "Role" not in df.columns:
        return

    all_objects = sorted(set(df["Target"].dropna().unique()))
    roles = sorted(set(df["Role"].dropna().unique()))
    if not roles:
        return

    # role -> obj -> "R,W"
    role_perm_map = {r: {o: "" for o in all_objects} for r in roles}

    for _, row in df.iterrows():
        role = row["Role"]
        obj  = row["Target"]
        perm = row["Permission"]
        if pd.notna(role) and pd.notna(obj) and pd.notna(perm):
            current = set(p.strip() for p in str(role_perm_map[role].get(obj, "")).split(",") if p)
            for p in str(perm).split(","):
                p = p.strip()
                if p:
                    current.add(p)
            role_perm_map[role][obj] = ",".join(sorted(current))

    table = pd.DataFrame(
        [[r] + [role_perm_map[r][o] for o in all_objects] for r in roles],
        columns=["Roles"] + all_objects
    )
    st.markdown("### Table des rôles et permissions (héritées incluses)")
    st.dataframe(table, use_container_width=True)


def draw_combined_graph(components, adj, labels, simplified_edges, role_data):
    """
    Mise en page :
    - Sujets (préfixe 'S') à gauche, objets (préfixe 'O') à droite
    - Rôles affichés à côté des sujets
    - Physique désactivée, police lisible, plein écran
    """
    net = Network(height="950px", width="100%", directed=True, notebook=False)

    x_gap = 300
    y_gap = 220
    cur_y_S = 0
    cur_y_O = 0

    sorted_components = sorted(components, key=len, reverse=True)
    added = set()

    for comp, label in zip(sorted_components, labels):
        subjects = [n for n in comp if str(n).startswith("S")]
        objects  = [n for n in comp if str(n).startswith("O")]

        for s in subjects:
            if s not in added:
                roles = role_data.get(s, "No role")
                combined = "{" + ", ".join(sorted(label | {s})) + "}"
                net.add_node(
                    s,
                    label=f"{s} ({roles})\n{combined}",
                    shape="ellipse",
                    x=-x_gap,
                    y=-cur_y_S * y_gap
                )
                added.add(s)
                cur_y_S += 1

        for o in objects:
            if o not in added:
                combined = "{" + ", ".join(sorted(label | {o})) + "}"
                net.add_node(
                    o,
                    label=f"{o}\n{combined}",
                    shape="box",
                    x= x_gap,
                    y=-cur_y_O * y_gap
                )
                added.add(o)
                cur_y_O += 1

    # Arêtes (réduction transitive si DAG)
    G = nx.DiGraph()
    for src, lst in adj.items():
        for dst in lst:
            if src in added and dst in added:
                G.add_edge(src, dst)
    if nx.is_directed_acyclic_graph(G):
        G = nx.transitive_reduction(G)
    for u, v in G.edges():
        net.add_edge(u, v, arrows="to")

    net.set_options("""
    var options = {
      nodes: {
        font: { size: 48 },
        shapeProperties: { borderRadius: 6 },
        size: 40,
        fixed: { x: true, y: true }
      },
      edges: {
        width: 4,
        arrows: { to: { enabled: true, scaleFactor: 1.3 } },
        smooth: { enabled: false }
      },
      physics: { enabled: false },
      interaction: { dragNodes: false, dragView: true, zoomView: true }
    }
    """)

    html_str = net.generate_html()
    st_html(html_str, height=980, scrolling=True)


# ================== RBAC : héritage depuis Excel ==================
def propagate_rbac_from_excel(df: pd.DataFrame) -> pd.DataFrame:
    """
    - Si plusieurs sujets partagent un même rôle, chacun hérite des permissions
      (R/W) de ce rôle sur les mêmes objets.
    - Les lignes héritées reçoivent Heritage='Role'.
    """
    df = df.copy()

    if "Role" not in df.columns:
        return df

    # role -> set((perm, obj))
    role_perms = {}
    # subject -> set(roles)
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
        for r in roles:
            for perm, obj in role_perms.get(r, set()):
                mask = (
                    (df["Source"] == subj)
                    & (df["Permission"] == perm)
                    & (df["Target"] == obj)
                )
                if not mask.any():
                    new_rows.append(
                        {"Source": subj, "Permission": perm, "Target": obj, "Role": r, "Heritage": "Role"}
                    )

    if new_rows:
        df = pd.concat([df, pd.DataFrame(new_rows)], ignore_index=True)

    return df


# ================== CHINA-WALL (vérif) ==================
def violates_china_wall(labels):
    # global + par entité (session_state)
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


# ================== VISUALISATION COMPLÈTE ==================
def process_data_display(df: pd.DataFrame):
    if df is None or df.empty:
        st.info("Aucune donnée à afficher.")
        return

    # 1) Appliquer RBAC (héritage) si nécessaire
    df_expanded = propagate_rbac_from_excel(df)

    # 1.b) Mapping subject -> rôles concaténés (pour les labels des S)
    role_data = {}
    if "Role" in df_expanded.columns:
        tmp = df_expanded[["Source", "Role"]].dropna()
        for s, subdf in tmp.groupby("Source"):
            roles = sorted(set(str(r).strip() for r in subdf["Role"] if pd.notna(r) and str(r).strip()))
            role_data[s] = ",".join(roles) if roles else "No role"

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

    # 5) Tables + Graphes
    display_table(scc, labels)
    display_role_table(df_expanded)
    simplified_edges = simplify_relations(labels)
    draw_combined_graph(scc, adj, labels, simplified_edges, role_data)


# ================== ÉVALUATION (optionnelle) ==================
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
    ax.bar([0], temps_tarjan, bar_width, label='SCC Detection (Tarjan)')
    ax.bar([0 + bar_width], temps_labels, bar_width, label='Label Propagation')
    ax.set_xlabel("Taille")
    ax.set_ylabel("Temps (s)")
    ax.set_title(f"Performance pour {nb_entites} entités")
    ax.set_xticks([0 + bar_width/2])
    ax.set_xticklabels([str(nb_entites)])
    ax.grid(True, axis="y", alpha=0.3)
    ax.legend()
    st.pyplot(fig)


# ================== TERMINAL DE COMMANDES ==================
def apply_prompt(df: pd.DataFrame, prompt: str):
    """
    Terminal compatible avec :
    - Modèle entité simple: AddEnt, AddCh, RemoveCh (2 ou 3 args), Never
    - RBAC: AddRole, AddSub [R1], GrantPermission, RevokePermission, DeassignUser,
            ModifyRole, ModifyPermission, RemoveRole
    - DAC: "AddObj O1" | "S2 AddObj O2", "S2 Grant S3 O2 R"
    - Suppressions: RemoveSub, RemoveObj
    - Modifs: modifyCh, modifySub, modifyObj
    - show, EvalPerf
    """
    parts = prompt.strip().split()
    if not parts:
        return df, "❌ Empty command."

    cmd = parts[0]
    args = parts[1:]
    msg = ""

    # ====== ÉVALUATION ======
    if cmd == "EvalPerf":
        total_ent = len(st.session_state.sujets_definis | st.session_state.objets_definis)
        if total_ent == 0:
            return df, "⚠️ No entities defined. Please create subjects or objects first."
        evaluer_performance_interface(total_ent)
        return df, f"✅ EvalPerf run for {total_ent} entities."

    # ====== MODÈLE ENTITÉ SIMPLE ======
    if cmd == "AddEnt":
        if len(args) != 1:
            return df, "❌ Usage: AddEnt E1"
        ent = args[0]
        if ((df["Source"] == ent) | (df["Target"] == ent)).any():
            return df, f"⚠️ Entity '{ent}' already exists."
        df = pd.concat([df, pd.DataFrame([{"Source": ent, "Permission": None, "Target": None, "Role": None}])], ignore_index=True)
        return df, f"✅ Entity '{ent}' added."

    if cmd == "AddCh":
        # AddCh E1 E2  (canal simple en lecture par défaut côté entités)
        if len(args) == 2:
            src, dst = args
            df = pd.concat([df, pd.DataFrame([{"Source": src, "Permission": "R", "Target": dst, "Role": None}])], ignore_index=True)
            return df, f"✅ Channel added: {src} ➜ {dst}"
        return df, "❌ Usage: AddCh E1 E2"

    if cmd == "RemoveCh":
        # RemoveCh Source Permission Target
        # RemoveCh Source Target
        if len(args) == 3:
            src, perm, dst = args
            before = len(df)
            df = df[~((df["Source"] == src) & (df["Permission"] == perm) & (df["Target"] == dst))]
            removed = before - len(df)
            if removed == 0:
                return df, f"⚠️ No channel found matching '{src} {perm} {dst}'."
            return df, f"🗑️ Channel removed: {src} --{perm}--> {dst}"
        elif len(args) == 2:
            src, dst = args
            before = len(df)
            df = df[~((df["Source"] == src) & (df["Target"] == dst))]
            removed = before - len(df)
            if removed == 0:
                return df, f"⚠️ No channel found between '{src}' and '{dst}'."
            return df, f"🗑️ All channels removed between '{src}' and '{dst}'."
        else:
            return df, "❌ Usage: RemoveCh Source [Permission] Target"

    if cmd == "Never":
        # ex: Never {A,B}  ou  Never {A,B} for E1 E2
        if "for" in args:
            idx = args.index("for")
            etiquette = [e.strip("{} ,") for e in args[:idx]]
            entites = [e.strip("{} ,") for e in args[idx + 1 :]]
            for ent in entites:
                st.session_state.interdictions_entites.setdefault(ent, []).append(etiquette)
            return df, f"🚧 Forbidden combination {etiquette} for entities {entites}"
        else:
            etiquette = [e.strip("{} ,") for e in args]
            st.session_state.interdictions_globales.append(etiquette)
            return df, f"🚧 Globally forbidden combination: {etiquette}"

    # ====== RBAC ======
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
        df = pd.concat([df, pd.DataFrame([{"Source": subj, "Permission": None, "Target": None, "Role": role}])], ignore_index=True)
        # Propager les permissions déjà existantes de ce rôle si fourni
        if role:
            for perm, obj in st.session_state.role_permissions.get(role, set()):
                df = pd.concat([df, pd.DataFrame([{"Source": subj, "Permission": perm, "Target": obj, "Role": role, "Heritage": "Role"}])], ignore_index=True)
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
                df = pd.concat([df, pd.DataFrame([{"Source": subj, "Permission": perm, "Target": obj, "Role": role, "Heritage": "Role"}])], ignore_index=True)
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
        subj, role = args
        if subj not in st.session_state.sujets_definis:
            return df, f"⛔ Error: Subject '{subj}' does not exist."
        if role not in st.session_state.roles_definis:
            return df, f"⛔ Error: Role '{role}' does not exist."
        if role not in st.session_state.subject_roles.get(subj, set()):
            return df, f"ℹ️ Subject '{subj}' does not have role '{role}'."
        st.session_state.subject_roles[subj].remove(role)
        before = len(df)
        df = df[~((df["Source"] == subj) & (df["Role"] == role))]
        deleted = before - len(df)
        return df, f"🗑️ Role '{role}' removed from subject '{subj}' ({deleted} propagated permission(s) removed)."

    if cmd == "ModifyRole":
        # ModifyRole OldRole NewRole
        if len(args) != 2:
            return df, "❌ Usage: ModifyRole OldRole NewRole"
        old_role, new_role = args
        if old_role not in st.session_state.roles_definis:
            return df, f"⛔ Error: Role '{old_role}' does not exist."
        if new_role in st.session_state.roles_definis:
            return df, f"⛔ Error: Role '{new_role}' already exists."
        # bascule
        st.session_state.roles_definis.remove(old_role)
        st.session_state.roles_definis.add(new_role)
        st.session_state.role_permissions[new_role] = st.session_state.role_permissions.pop(old_role, set())
        for subj in st.session_state.subject_roles:
            if old_role in st.session_state.subject_roles[subj]:
                st.session_state.subject_roles[subj].remove(old_role)
                st.session_state.subject_roles[subj].add(new_role)
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
        # Remplacer
        st.session_state.role_permissions[role].remove((old_perm, target))
        st.session_state.role_permissions[role].add((new_perm, target))
        cond = (df["Role"] == role) & (df["Permission"] == old_perm) & (df["Target"] == target)
        n = df[cond].shape[0]
        df.loc[cond, "Permission"] = new_perm
        return df, f"🔁 Permission modified: Role '{role}' – {old_perm} ➝ {new_perm} on '{target}' ({n} entries updated)."

    # ====== DAC ======
    # "AddObj O1"  OU  "S2 AddObj O2"
    if cmd == "AddObj":
        # AddObj O1
        if len(args) == 1:
            obj = args[0]
            st.session_state.objets_definis.add(obj)
            df = pd.concat([df, pd.DataFrame([{"Source": obj, "Permission": None, "Target": None, "Role": None}])], ignore_index=True)
            return df, f"✅ Object '{obj}' is added"
        # AddObj Owner Obj (legacy)
        if len(args) == 2:
            owner, obj = args
            st.session_state.sujets_definis.add(owner)
            st.session_state.objets_definis.add(obj)
            # ❗Pas de R auto pour le propriétaire (DAC)
            entry_owner = pd.DataFrame([{"Source": owner, "Permission": "Owner", "Target": obj, "Role": None}])
            df = pd.concat([df, entry_owner], ignore_index=True)
            return df, f"✅ Object '{obj}' is added with owner '{owner}'"
        return df, "❌ Usage: AddObj O1  |  AddObj Owner O1"

    # Cas "S2 AddObj O2"
    if len(parts) >= 3 and parts[1] == "AddObj":
        owner, obj = parts[0], parts[2]
        if owner not in st.session_state.sujets_definis:
            return df, f"⛔ Error: Subject '{owner}' does not exist. Use AddSub first."
        if obj in st.session_state.objets_definis:
            return df, f"ℹ️ The object '{obj}' already exists."
        st.session_state.objets_definis.add(obj)
        entry_owner = pd.DataFrame([{"Source": owner, "Permission": "Owner", "Target": obj, "Role": None}])
        df = pd.concat([df, entry_owner], ignore_index=True)
        return df, f"✅ Object '{obj}' created with owner '{owner}'"

    # "S2 Grant S3 O2 R"
    if len(parts) >= 5 and parts[1] == "Grant":
        owner, _, subject, obj, perm = parts[:5]
        if owner not in st.session_state.sujets_definis:
            return df, f"⛔ Error: Subject '{owner}' does not exist."
        if subject not in st.session_state.sujets_definis:
            return df, f"⛔ Error: Target subject '{subject}' does not exist."
        if obj not in st.session_state.objets_definis:
            return df, f"⛔ Error: Object '{obj}' does not exist."
        # Vérifier propriétaire
        is_owner = ((df["Source"] == owner) & (df["Target"] == obj) & (df["Permission"] == "Owner")).any()
        if not is_owner:
            return df, f"⛔Error: '{owner}' is not the owner of '{obj}'."
        new_entry = pd.DataFrame([{"Source": subject, "Permission": perm, "Target": obj, "Role": None}])
        df = pd.concat([df, new_entry], ignore_index=True)
        return df, f"✅ Permission '{perm}' granted to '{subject}' on '{obj}' by '{owner}'."

    # ====== SUPPRESSIONS & MODIFS ======
    if cmd == "RemoveSub":
        # RemoveSub S1
        if len(args) != 1:
            return df, "❌ Usage: RemoveSub S1"
        subject = args[0]
        st.session_state.sujets_definis.discard(subject)
        st.session_state.subject_roles.pop(subject, None)
        df = df[df["Source"] != subject]  # ne supprime pas les objets portant le même ID
        return df, f"🗑️ Subject '{subject}' removed and its associated permissions cleared."

    if cmd == "RemoveObj":
        # RemoveObj O1
        if len(args) != 1:
            return df, "❌ Usage: RemoveObj O1"
        obj = args[0]
        st.session_state.objets_definis.discard(obj)
        df = df[(df["Source"] != obj) & (df["Target"] != obj)]
        return df, f"🗑️ Object '{obj}' removed and its associated channels cleared."

    if cmd == "modifyCh":
        # modifyCh oldS oldP oldT newS newP newT
        if len(args) != 6:
            return df, "❌ Usage: modifyCh oldS oldP oldT newS newP newT"
        old_s, old_p, old_t, new_s, new_p, new_t = args
        cond = (df["Source"] == old_s) & (df["Permission"] == old_p) & (df["Target"] == old_t)
        df.loc[cond, ["Source", "Permission", "Target"]] = [new_s, new_p, new_t]
        return df, f"🔁 Path modified: {old_s} {old_p} {old_t} ➝ {new_s} {new_p} {new_t}"

    if cmd == "modifySub":
        # modifySub oldSub newSub
        if len(args) != 2:
            return df, "❌ Usage: modifySub oldSubject newSubject"
        old_s, new_s = args
        if old_s in st.session_state.sujets_definis:
            st.session_state.sujets_definis.remove(old_s)
            st.session_state.sujets_definis.add(new_s)
        df.loc[df["Source"] == old_s, "Source"] = new_s
        df.loc[df["Target"] == old_s, "Target"] = new_s
        return df, f"✏️ Subject renamed: {old_s} ➝ {new_s}"

    if cmd == "modifyObj":
        # modifyObj oldObj newObj
        if len(args) != 2:
            return df, "❌ Usage: modifyObj oldObj newObj"
        old_o, new_o = args
        if old_o in st.session_state.objets_definis:
            st.session_state.objets_definis.remove(old_o)
            st.session_state.objets_definis.add(new_o)
        df.loc[df["Source"] == old_o, "Source"] = new_o
        df.loc[df["Target"] == old_o, "Target"] = new_o
        return df, f"✏️ Object renamed: {old_o} ➝ {new_o}"

    if cmd == "show":
        process_data_display(df)
        return df, "🚀 Génération des graphes…"

    return df, "❌ Unknown command."


# ================== UI STREAMLIT ==================
def main():
    st.set_page_config(page_title="Contrôle d'accès – RBAC / DAC / China-Wall", layout="wide")

    # Forcer largeur max 100%
    st.markdown(
        """
        <style>
        .block-container {max-width: 100% !important; padding: 1rem 1.2rem;}
        </style>
        """,
        unsafe_allow_html=True
    )

    init_state()

    st.title("🔐 Contrôle d'accès – RBAC / DAC / China-Wall")

    tabs = st.tabs(["📂 Fichier Excel", "⌨️ Terminal de commandes"])

    # --- Onglet Excel ---
    with tabs[0]:
        up = st.file_uploader(
            "Importer un fichier Excel (colonnes: Source, Permission, Target, Role, Heritage optionnelle)",
            type=["xlsx"]
        )
        if up:
            try:
                df = pd.read_excel(io.BytesIO(up.read()))  # nécessite openpyxl
                missing = {"Source", "Permission", "Target"} - set(df.columns)
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

    # --- Onglet Terminal ---
    with tabs[1]:
        st.markdown("Tape une commande puis **Entrée** (ex: `AddSub S1 R1`, `AddRole R1`, `GrantPermission R1 R O1`, `AddCh E1 E2`, `RemoveCh S1 R O1`, `S2 AddObj O2`, `S2 Grant S3 O2 R`, `show`, …)")
        cmd = st.text_input("C:\\>", value="", placeholder="Ex: AddSub S1 R1")
        if cmd:
            st.session_state.global_data, message = apply_prompt(st.session_state.global_data, cmd)
            st.session_state.history.append(f"C:\\> {cmd}\n{message}")
            st.experimental_rerun()

        st.text_area("Historique", "\n\n".join(st.session_state.history), height=360, label_visibility="visible")


if __name__ == "__main__":
    main()
