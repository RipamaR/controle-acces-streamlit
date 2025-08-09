# streamlit_app.py
# -----------------------------------------------------------
# Contrôle d'accès (RBAC / DAC / China-Wall) – version Streamlit
# Affichage PyVis PLEIN ÉCRAN (largeur 100% + hauteur viewport)
# et upload Excel (openpyxl)
# -----------------------------------------------------------

import io
import time
import random
import pandas as pd
import networkx as nx
import streamlit as st

# IMPORTANT : installer pyvis + openpyxl dans requirements.txt
from pyvis.network import Network
from streamlit.components.v1 import html as st_html

# ================== ÉTAT GLOBAL ==================
def init_state():
    if "global_data" not in st.session_state:
        st.session_state.global_data = pd.DataFrame(
            columns=["Source", "Permission", "Target", "Role", "Heritage"]
        )
    defaults = {
        "roles_definis": set(),
        "role_permissions": {},   # {role: set((perm, obj))}
        "subject_roles": {},      # {subject: set(roles)}
        "sujets_definis": set(),
        "objets_definis": set(),
        "interdictions_globales": [],  # China-wall (global)
        "interdictions_entites": {},   # China-wall (par entité)
        "history": [],                 # Terminal
    }
    for k, v in defaults.items():
        if k not in st.session_state:
            st.session_state[k] = v

# ================== ALGO TARJAN ==================
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
        stack.append(v); on_stack[v] = True

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
        if node in visited: return
        visited.add(node)
        for nb in adj.get(node, []):
            if nb in component_map:
                nb_comp = frozenset(component_map[nb])
                cur_comp = frozenset(component_map[node])
                labels[nb_comp].update(labels[cur_comp])
                dfs(nb, visited)
    for comp in components:
        for node in comp:
            dfs(node, set())
    return [labels[frozenset(comp)] for comp in components]

def simplify_relations(labels):
    G = nx.DiGraph()
    idx_to_set = {i: s for i, s in enumerate(labels)}
    for i, s1 in enumerate(labels):
        for j, s2 in enumerate(labels):
            if i != j and s1.issubset(s2):
                G.add_edge(i, j)
    # supprime arêtes transitives
    to_remove = set()
    for i in range(len(labels)):
        for j in range(len(labels)):
            if i != j and G.has_edge(i, j):
                for path in nx.all_simple_paths(G, i, j):
                    if len(path) > 2:
                        to_remove.add((i, j))
    for e in to_remove:
        G.remove_edge(*e)
    return [(idx_to_set[u], idx_to_set[v]) for u, v in G.edges()]

# ================== CONSTRUCTION ADJ ==================
def apply_permissions(df: pd.DataFrame):
    """
    R = Target -> Source (lecture)
    W = Source -> Target (écriture)
    """
    adj = {}
    def add(a, b):
        if pd.isna(a) or pd.isna(b): return
        adj.setdefault(a, []); adj.setdefault(b, [])
        adj[a].append(b)

    for _, row in df.iterrows():
        s, p, t = row["Source"], row["Permission"], row["Target"]
        if pd.isna(p) or pd.isna(t): continue
        for perm in str(p).split(","):
            perm = perm.strip()
            if perm == "R": add(t, s)
            elif perm == "W": add(s, t)

    for k in list(adj.keys()):
        adj[k] = list(sorted(set(adj[k])))
    return adj

# ================== TABLE ==================
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

# ================== RENDER PyVis PLEIN ÉCRAN ==================
def render_pyvis_fullscreen(net: Network, height_vh: int = 86):
    """
    Injecte l'HTML PyVis dans un conteneur plein écran.
    height_vh = hauteur du graphe en % de la hauteur de la fenêtre.
    """
    html_str = net.generate_html()

    custom_css = f"""
    <style>
      .block-container {{
        padding-top: 1rem; padding-bottom: 0rem;
      }}
      #fullwidth-container {{
        width: 100vw;     /* largeur fenêtre */
        margin-left: calc(-50vw + 50%);  /* étend hors des marges Streamlit */
      }}
      .pyvis-fullscreen {{
        height: {height_vh}vh;     /* hauteur viewport */
      }}
      .pyvis-fullscreen iframe {{
        width: 100% !important;
        height: 100% !important;
        border: none;
      }}
    </style>
    """

    # On place la page PyVis dans un <div> qui occupe toute la largeur.
    wrapped = f"""
    {custom_css}
    <div id="fullwidth-container">
      <div class="pyvis-fullscreen">
        {html_str}
      </div>
    </div>
    """
    st_html(wrapped, height=height_vh * 12, scrolling=True)

# ================== DESSIN DU GRAPHE ==================
def draw_combined_graph(components, adj, labels, simplified_edges):
    net = Network(height="100%", width="100%", directed=True, notebook=False)

    # Noeuds par entité
    added = set()
    for comp, label in zip(components, labels):
        for ent in comp:
            if ent not in added:
                combined = "{" + ", ".join(sorted(label | {ent})) + "}"
                net.add_node(ent, label=f"{ent}:\n{combined}", shape="ellipse")
                added.add(ent)

    # Arêtes (réduction transitive si DAG)
    G = nx.DiGraph()
    for u, lst in adj.items():
        for v in lst: G.add_edge(u, v)
    if nx.is_directed_acyclic_graph(G):
        G = nx.transitive_reduction(G)
    for u, v in G.edges():
        net.add_edge(u, v, arrows="to")

    # Sous-graphe classes d’équivalence (boîtes)
    base = 10_000_000
    def idx_of_set(target):
        for i, s in enumerate(labels):
            if s == target:
                return i
        return None

    for i, (comp, label) in enumerate(zip(components, labels)):
        name = ", ".join(comp)
        combined = "{" + ", ".join(sorted(label | set(comp))) + "}"
        net.add_node(base + i, label=f"| {name}: {combined} |", shape="box")

    for src_set, dst_set in simplified_edges:
        si = idx_of_set(src_set); di = idx_of_set(dst_set)
        if si is not None and di is not None:
            net.add_edge(base + si, base + di, arrows="to")

    # >>> AFFICHAGE PLEIN ÉCRAN <<<
    render_pyvis_fullscreen(net, height_vh=86)

# ================== RBAC depuis Excel ==================
def propagate_rbac_from_excel(df: pd.DataFrame) -> pd.DataFrame:
    df = df.copy()
    if "Role" not in df.columns:
        return df
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
        for r in roles:
            for perm, obj in role_perms.get(r, set()):
                mask = (
                    (df["Source"] == subj) &
                    (df["Permission"] == perm) &
                    (df["Target"] == obj)
                )
                if not mask.any():
                    new_rows.append({
                        "Source": subj, "Permission": perm, "Target": obj,
                        "Role": r, "Heritage": "Role"
                    })
    if new_rows:
        df = pd.concat([df, pd.DataFrame(new_rows)], ignore_index=True)
    return df

# ================== China Wall ==================
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

# ================== Orchestration ==================
def process_data_display(df: pd.DataFrame):
    if df is None or df.empty:
        st.info("Aucune donnée à afficher."); return

    df_expanded = propagate_rbac_from_excel(df)
    adj = apply_permissions(df_expanded)
    V = sorted(set(adj.keys()) | {v for lst in adj.values() for v in lst})
    scc, cmap = tarjan(V, adj)
    labels = propagate_labels(scc, adj, cmap)

    bad, msg = violates_china_wall(labels)
    if bad:
        st.error(f"⛔ CHINA-WALL: {msg}")
        return

    display_table(scc, labels)
    simplified = simplify_relations(labels)
    draw_combined_graph(scc, adj, labels, simplified)

# ================== Terminal ==================
def apply_prompt(df: pd.DataFrame, prompt: str):
    parts = prompt.strip().split()
    if not parts:
        return df, "❌ Empty command."
    cmd, args = parts[0], parts[1:]

    # Modèle entité simple
    if cmd == "AddEnt":
        if len(args) != 1: return df, "❌ Usage: AddEnt E1"
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
        if len(args) != 2: return df, "❌ Usage: RemoveCh Source Target"
        src, dst = args
        before = len(df)
        df = df[~((df["Source"] == src) & (df["Target"] == dst))]
        return df, f"🗑️ {before - len(df)} channel(s) removed between '{src}' and '{dst}'."

    if cmd == "Never":
        if "for" in args:
            idx = args.index("for")
            etiquette = [e.strip("{} ,") for e in args[:idx]]
            entites = [e.strip("{} ,") for e in args[idx+1:]]
            for ent in entites:
                st.session_state.interdictions_entites.setdefault(ent, []).append(etiquette)
            return df, f"🚧 Forbidden combination {etiquette} for {entites}"
        etiquette = [e.strip("{} ,") for e in args]
        st.session_state.interdictions_globales.append(etiquette)
        return df, f"🚧 Globally forbidden combination: {etiquette}"

    # RBAC minimal (AddRole, AddSub [Role], GrantPermission)
    if cmd == "AddRole":
        if len(args) != 1: return df, "❌ Usage: AddRole R1"
        role = args[0]
        st.session_state.roles_definis.add(role)
        st.session_state.role_permissions.setdefault(role, set())
        return df, f"✅ Role '{role}' added."

    if cmd == "AddSub":
        if len(args) < 1: return df, "❌ Usage: AddSub S1 [R1]"
        subj = args[0]; role = args[1] if len(args) > 1 else None
        st.session_state.sujets_definis.add(subj)
        st.session_state.subject_roles.setdefault(subj, set())
        if role:
            st.session_state.roles_definis.add(role)
            st.session_state.subject_roles[subj].add(role)
        df = pd.concat([df, pd.DataFrame([{"Source": subj, "Permission": None, "Target": None, "Role": role}])], ignore_index=True)
        return df, f"✅ Subject '{subj}' added" + (f" with role '{role}'" if role else "")

    if cmd == "GrantPermission":
        if len(args) != 3: return df, "❌ Usage: GrantPermission R1 R O1"
        role, perm, obj = args
        if role not in st.session_state.roles_definis:
            return df, f"❌ Role '{role}' is not defined."
        st.session_state.role_permissions.setdefault(role, set()).add((perm, obj))
        for subj, roles in st.session_state.subject_roles.items():
            if role in roles:
                df = pd.concat([df, pd.DataFrame([{
                    "Source": subj, "Permission": perm, "Target": obj, "Role": role, "Heritage": "Role"
                }])], ignore_index=True)
        return df, f"✅ Permission '{perm}' on '{obj}' granted to role '{role}' and propagated."

    if cmd == "show":
        process_data_display(df)
        return df, "🚀 Génération des graphes…"

    return df, "❌ Unknown command."

# ================== UI ==================
def main():
    st.set_page_config(page_title="Contrôle d'accès – Streamlit", layout="wide")
    init_state()

    st.title("🔐 Contrôle d'accès – RBAC / DAC / China-Wall")

    tabs = st.tabs(["📂 Fichier Excel (openpyxl)", "⌨️ Terminal de commandes"])

    # ---- Onglet Excel ----
    with tabs[0]:
        up = st.file_uploader(
            "Importer un fichier Excel (colonnes: Source, Permission, Target, Role, Heritage)",
            type=["xlsx"]
        )
        if up:
            try:
                # ⚠️ Nécessite openpyxl côté serveur (requirements.txt)
                df = pd.read_excel(io.BytesIO(up.read()))
                missing = {"Source", "Permission", "Target"} - set(df.columns)
                if missing:
                    st.error(f"Colonnes manquantes: {missing}")
                else:
                    for c in ["Role", "Heritage"]:
                        if c not in df.columns: df[c] = None
                    st.session_state.global_data = df
                    st.success("✅ Fichier chargé.")
                    with st.expander("Voir les données chargées"):
                        st.dataframe(df, use_container_width=True)
                    st.markdown("---")
                    process_data_display(df)
            except Exception as e:
                st.error(
                    "Erreur de lecture du fichier: "
                    + str(e)
                    + " — Si c'est un .xlsx, ajoute `openpyxl` dans requirements.txt"
                )

    # ---- Onglet Terminal ----
    with tabs[1]:
        st.markdown("Tape une commande puis **Entrée** (ex: `AddSub S1 R1`, `AddRole R1`, `GrantPermission R1 R O1`, `AddCh E1 E2`, `show`, …)")
        cmd = st.text_input("C:\\>", value="", placeholder="Ex: AddSub S1 R1")
        if cmd:
            st.session_state.global_data, message = apply_prompt(st.session_state.global_data, cmd)
            st.session_state.history.append(f"C:\\> {cmd}\n{message}")
            st.experimental_rerun()
        st.text_area("Historique", "\n\n".join(st.session_state.history), height=280)

if __name__ == "__main__":
    main()
