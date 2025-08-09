# streamlit_app.py
# -----------------------------------------------------------
# Application Streamlit pour contrôle d'accès (RBAC, DAC, China-Wall)
# Version plein-écran + lecture Excel robuste (openpyxl)
# -----------------------------------------------------------

import io
import time
import random
import pandas as pd
import networkx as nx
import streamlit as st
from pyvis.network import Network
from streamlit.components.v1 import html as st_html

# ==================== CONFIG UI =====================
st.set_page_config(page_title="Contrôle d'accès – Streamlit", layout="wide")
# Pleine largeur pour tout le contenu
st.markdown(
    """
    <style>
      .block-container {padding-top: 1rem; padding-bottom: 1rem; max-width: 100% !important;}
      .stTabs [role="tablist"] { gap: 12px; }
      .stTabs [role="tab"] { padding: 10px 16px; border-radius: 8px; }
    </style>
    """,
    unsafe_allow_html=True
)

# ================== ÉTAT GLOBAL =====================
def init_state():
    if "global_data" not in st.session_state:
        st.session_state.global_data = pd.DataFrame(
            columns=["Source", "Permission", "Target", "Role", "Heritage"]
        )
    for key, default in [
        ("roles_definis", set()),
        ("role_permissions", {}),   # {role: set((perm, obj))}
        ("subject_roles", {}),      # {subject: set(roles)}
        ("sujets_definis", set()),
        ("objets_definis", set()),
        ("interdictions_globales", []),   # China Wall global
        ("interdictions_entites", {}),    # China Wall par entité
        ("history", []),                  # Terminal
    ]:
        if key not in st.session_state:
            st.session_state[key] = default

init_state()

# =============== ALGORITHMES (Tarjan & co) =================
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

# =============== CONSTRUCTION DU GRAPHE ====================
def apply_permissions(df: pd.DataFrame):
    """
    Construit l'adjacence à partir des permissions :
    - R : Target -> Source  (lecture = data flow de l'objet vers le lecteur)
    - W : Source -> Target  (écriture = data flow de l'auteur vers l'objet)
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
                add_edge(t, s)
            elif perm == "W":
                add_edge(s, t)

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


def draw_combined_graph(components, adj, labels, simplified_edges):
    net = Network(height="900px", width="100%", directed=True, notebook=False)

    # Noeuds (un par entité)
    added = set()
    for comp, label in zip(components, labels):
        for ent in comp:
            if ent not in added:
                combined = "{" + ", ".join(sorted(label | {ent})) + "}"
                net.add_node(ent, label=f"{ent}:\n{combined}", shape="ellipse")
                added.add(ent)

    # Arêtes (réduction transitive si DAG)
    G = nx.DiGraph()
    for src, lst in adj.items():
        for dst in lst:
            G.add_edge(src, dst)
    if nx.is_directed_acyclic_graph(G):
        G = nx.transitive_reduction(G)

    for u, v in G.edges():
        net.add_edge(u, v, arrows="to")

    # Sous-graphe des classes d'équivalence (boîtes) + relations réduites
    base_id = 10_000_000
    for i, (comp, label) in enumerate(zip(components, labels)):
        name = ", ".join(comp)
        combined = "{" + ", ".join(sorted(label | set(comp))) + "}"
        text = f"| {name}: {combined} |"
        nid = base_id + i
        net.add_node(nid, label=text, shape="box")

    def find_index_by_set(target_set):
        for i, (_, _, lbl) in enumerate(zip(components, components, labels)):
            if lbl == target_set:
                return i
        return None

    for src_set, dst_set in simplified_edges:
        si = find_index_by_set(src_set)
        di = find_index_by_set(dst_set)
        if si is not None and di is not None:
            net.add_edge(base_id + si, base_id + di, arrows="to")

    # Affichage dans Streamlit (plein écran)
    html_str = net.generate_html()
    st_html(html_str, height=950, scrolling=True)

# =============== RBAC : propagation depuis Excel ===========
def propagate_rbac_from_excel(df: pd.DataFrame) -> pd.DataFrame:
    """
    - Si plusieurs sujets partagent un même rôle, chacun hérite des permissions
      (R/W) de ce rôle sur les mêmes objets.
    - Les lignes héritées reçoivent Heritage='Role' (facultatif).
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
        obj = str(row.get("Target", "")).strip()
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

    # 5) Table + Graphes
    display_table(scc, labels)
    simplified_edges = simplify_relations(labels)
    draw_combined_graph(scc, adj, labels, simplified_edges)

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
        if len(args) == 2:
            src, dst = args
            df = pd.concat([df, pd.DataFrame([{"Source": src, "Permission": "R", "Target": dst, "Role": None}])], ignore_index=True)
            return df, f"✅ Channel added: {src} ➜ {dst}"
        return df, "❌ Usage: AddCh E1 E2"

    if cmd == "RemoveCh":
        if len(args) != 2:
            return df, "❌ Usage: RemoveCh Source Target"
        src, dst = args
        before = len(df)
        df = df[~((df["Source"] == src) & (df["Target"] == dst))]
        removed = before - len(df)
        return df, f"🗑️ {removed} channel(s) removed between '{src}' and '{dst}'."

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
        df = pd.concat([df, pd.DataFrame([{"Source": subj, "Permission": None, "Target": None, "Role": role}])], ignore_index=True)
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

    # — DAC —
    if len(parts) >= 3 and parts[1] == "AddObj":
        # S2 AddObj O2 (DAC)
        owner, obj = parts[0], parts[2]
        if owner not in st.session_state.sujets_definis:
            return df, f"⛔ Error: Subject '{owner}' does not exist. Use AddSub first."
        if obj in st.session_state.objets_definis:
            return df, f"ℹ️ The object '{obj}' already exists."
        st.session_state.objets_definis.add(obj)
        entry_owner = pd.DataFrame([{"Source": owner, "Permission": "Owner", "Target": obj, "Role": None}])
        df = pd.concat([df, entry_owner], ignore_index=True)
        return df, f"✅ Object '{obj}' created with owner '{owner}'"

    if len(parts) >= 5 and parts[1] == "Grant":
        # S2 Grant S3 O2 R
        owner, _, subject, obj, perm = parts[:5]
        if owner not in st.session_state.sujets_definis:
            return df, f"⛔ Error: Subject '{owner}' does not exist."
        if subject not in st.session_state.sujets_definis:
            return df, f"⛔ Error: Target subject '{subject}' does not exist."
        if obj not in st.session_state.objets_definis:
            return df, f"⛔ Error: Object '{obj}' does not exist."

        is_owner = ((df["Source"] == owner) & (df["Target"] == obj) & (df["Permission"] == "Owner")).any()
        if is_owner:
            new_entry = pd.DataFrame([{"Source": subject, "Permission": perm, "Target": obj, "Role": None}])
            df = pd.concat([df, new_entry], ignore_index=True)
            return df, f"✅ Permission '{perm}' granted to '{subject}' on '{obj}' by '{owner}'."
        else:
            return df, f"⛔Error: '{owner}' is not the owner of '{obj}'."

    if cmd == "show":
        process_data_display(df)
        return df, "🚀 Génération des graphes…"

    return df, "❌ Unknown command."

# ================== UI STREAMLIT ===========================
st.title("🔐 Contrôle d'accès – RBAC / DAC / China-Wall")
tabs = st.tabs(["📂 Fichier Excel", "⌨️ Terminal de commandes"])

# --- Onglet Excel ---
with tabs[0]:
    up = st.file_uploader(
        "Importer un fichier Excel (.xlsx) avec colonnes: Source, Permission, Target, (Role, Heritage optionnelles)",
        type=["xlsx"]
    )
    if up:
        try:
            # 🔒 Lecture robuste via openpyxl + colonnes garanties
            df = pd.read_excel(io.BytesIO(up.read()), engine="openpyxl")
            for col in ["Source", "Permission", "Target", "Role", "Heritage"]:
                if col not in df.columns:
                    df[col] = None

            # garder en session
            st.session_state.global_data = df
            st.success("✅ Fichier chargé.")
            with st.expander("Voir les données chargées"):
                st.dataframe(df, use_container_width=True)

            st.markdown("---")
            process_data_display(df)
        except Exception as e:
            st.error(f"Erreur de lecture du fichier: {e}\n\n👉 Assure-toi que `openpyxl` est bien listé dans requirements.txt.")

# --- Onglet Terminal ---
with tabs[1]:
    st.markdown("Tape une commande puis **Entrée** (ex: `AddSub S1 R1`, `AddRole R1`, `GrantPermission R1 R O1`, `S2 AddObj O2`, `S2 Grant S3 O2 R`, `AddCh E1 E2`, `show`, …)")
    cmd = st.text_input("C:\\>", value="", placeholder="Ex: AddSub S1 R1")
    if cmd:
        st.session_state.global_data, message = apply_prompt(st.session_state.global_data, cmd)
        st.session_state.history.append(f"C:\\> {cmd}\n{message}")
        st.experimental_rerun()

    st.text_area("Historique", "\n\n".join(st.session_state.history), height=320)
