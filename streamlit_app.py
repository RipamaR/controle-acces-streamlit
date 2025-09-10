# streamlit_app.py
# -----------------------------------------------------------
# Interface graphique : Contrôle de flux de données – DAC / MAC / RBAC / ABAC / China-Wall
# Intègre :
#  - Graphe principal + graphe par composant (SCC)
#  - Tableau entités/étiquettes trié
#  - Terminal de commandes (FR/EN)
#  - EvalPerf (benchmark Tarjan / propagation)
#  - Chargement Excel (RBAC ou Entités)
#  - Commandes AssignRole / UnassignRole / édition entités/objets/rôles
# -----------------------------------------------------------

import io
import re
import time
import random
import pandas as pd
import networkx as nx
import matplotlib.pyplot as plt
import streamlit as st
from pyvis.network import Network
from streamlit.components.v1 import html as st_html

# ===================== CONFIG UI ===========================
st.set_page_config(
    page_title="Interface graphique pour la représentation de contrôle de flux de données sécuritaires – RBAC / DAC / China-Wall",
    layout="wide"
)

# --- Pleine largeur + titres alignés à gauche (pas centrés) ---
FULL_WIDTH_CSS = """
<style>
section.main > div.block-container {
    max-width: 100% !important;
    padding-left: 2rem;
    padding-right: 2rem;
    padding-top: 1rem;
    padding-bottom: 1rem;
}
h1, h2, h3, h4, h5, h6 { text-align: left !important; }
</style>
"""
st.markdown(FULL_WIDTH_CSS, unsafe_allow_html=True)

# ===================== i18n (FR/EN) ========================
# Langue en session
if "lang" not in st.session_state:
    st.session_state.lang = "fr"  # défaut: français

def tr(fr: str, en: str, **kw) -> str:
    """Retourne la version FR ou EN et applique .format(**kw) si présent."""
    s = fr if st.session_state.lang == "fr" else en
    try:
        return s.format(**kw)
    except Exception:
        return s

# Sélecteur global de langue (valeurs stables "fr"/"en")
_lang_labels = {"fr": "Français", "en": "English"}
lang_selected = st.sidebar.radio(
    tr("🌐 Choisir la langue", "🌐 Choose language"),
    options=["fr", "en"],
    index=0 if st.session_state.lang == "fr" else 1,
    format_func=lambda code: _lang_labels[code],
)
st.session_state.lang = lang_selected

# Titre
st.title(tr(
    "🔐 Interface graphique pour la représentation de contrôle de flux de données sécuritaires – DAC / MAC / RBAC / ABAC",
    "🔐 Graphical interface for secure data flow control representation – DAC / MAC / RBAC / ABAC"
))

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
        "selected_component": None,   # index SCC sélectionné
    }
    for k, v in defaults.items():
        if k not in st.session_state:
            st.session_state[k] = v

init_state()

# ===================== NORMALISATION =======================
_NAN_SET = {"", "nan", "none", "null"}

def _norm_entity(x: object) -> str | None:
    if x is None or (isinstance(x, float) and pd.isna(x)):
        return None
    s = str(x).strip()
    if s.lower() in _NAN_SET:
        return None
    s = re.sub(r"\s+", "", s)
    m = re.fullmatch(r"([a-zA-Z]+)0*([0-9]+)", s)
    if m:
        return f"{m.group(1).upper()}{int(m.group(2))}"
    return s.upper()

def _norm_perm(x: object) -> str | None:
    if x is None or (isinstance(x, float) and pd.isna(x)):
        return None
    s = str(x).strip()
    if s.lower() in _NAN_SET:
        return None
    return s.upper()

def normalize_df(df: pd.DataFrame) -> pd.DataFrame:
    df = df.copy()
    for col in ["Source", "Target"]:
        if col in df.columns:
            df[col] = df[col].map(_norm_entity)
    if "Role" in df.columns:
        df["Role"] = df["Role"].apply(lambda v: None if pd.isna(v) else str(v).strip() or None)
    if "Permission" in df.columns:
        df["Permission"] = df["Permission"].map(_norm_perm)
    if "Heritage" in df.columns:
        df["Heritage"] = df["Heritage"].apply(lambda v: None if pd.isna(v) else str(v).strip() or None)
    return df

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

# ---- Propagation sur le DAG de composantes (condensation) ----
def propagate_labels(components, adj, component_map):
    comp_index = {frozenset(c): i for i, c in enumerate(components)}
    labels = [set(c) for c in components]
    Gc = nx.DiGraph()
    Gc.add_nodes_from(range(len(components)))
    for u in component_map:
        cu = comp_index[frozenset(component_map[u])]
        for v in adj.get(u, []):
            if v not in component_map:
                continue
            cv = comp_index[frozenset(component_map[v])]
            if cu != cv:
                Gc.add_edge(cu, cv)
    for u in nx.topological_sort(Gc):
        for v in Gc.successors(u):
            labels[v] |= labels[u]
    return labels

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

# =============== CONSTRUCTION DE L’ADJACENCE =================
def apply_permissions(df_effective: pd.DataFrame):
    adj = {}
    def add_edge(a, b):
        if a is None or b is None:
            return
        adj.setdefault(a, []); adj.setdefault(b, [])
        adj[a].append(b)
    for _, row in df_effective.iterrows():
        s, p, t = row.get("Source"), row.get("Permission"), row.get("Target")
        if p == "R":
            add_edge(t, s)  # lecture: O -> S
        elif p == "W":
            add_edge(s, t)  # écriture: S -> O
    for k in list(adj.keys()):
        adj[k] = sorted(set(adj[k]))
    return adj

# =============== UTILITAIRES TABLES =========================
def _fmt_set(ss: set[str]) -> str:
    return "{" + ", ".join(sorted(ss)) + "}"

def display_entities_table(components, labels):
    data = {
        "Entities": [", ".join(sorted(c)) for c in components],
        "Their labels": [_fmt_set(lbl | set(comp)) for comp, lbl in zip(components, labels)],
        tr("Nombre d'étiquettes", "Number of labels"): [len(lbl) for lbl in labels],
    }
    df = pd.DataFrame(data).sort_values(
        by=tr("Nombre d'étiquettes", "Number of labels"), ascending=False
    ).drop(columns=[tr("Nombre d'étiquettes", "Number of labels")])
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
    st.dataframe(df_role, use_container_width=True)

# =============== PYVIS (rendu HTML dans Streamlit) ==========
PYVIS_OPTIONS = """
var options = {
  "nodes": {"font": {"size": 50}, "shapeProperties": {"borderRadius": 5}, "size": 40, "fixed": {"x": false, "y": false}},
  "edges": {"width": 4, "arrows": {"to": {"enabled": true, "scaleFactor": 1.5}}, "length": 150, "smooth": {"enabled": false}},
  "physics": {"enabled": false},
  "interaction": {"dragNodes": true, "dragView": true, "zoomView": true}
}
"""

def _pyvis_show(net: Network, height=900, width=1600):
    net.set_options(PYVIS_OPTIONS)
    html = net.generate_html()
    st_html(html, height=height, width=width, scrolling=True)

# =============== GRAPHE PRINCIPAL ===========================
def draw_main_graph(df: pd.DataFrame):
    if df.empty:
        st.info(tr("Aucune donnée pour générer le graphe.", "No data to draw the graph."))
        return
    df_eff = df[df["Permission"].isin(["R", "W"])].copy()
    if df_eff.empty:
        st.info(tr("Aucune relation R/W à afficher.", "No R/W relationship to display."))
        return
    adj = apply_permissions(df_eff)
    G_adj = nx.DiGraph()
    for u, vs in adj.items():
        for v in vs:
            G_adj.add_edge(u, v)
    scc = list(nx.strongly_connected_components(G_adj))
    scc_sorted = sorted(scc, key=len)
    x_step, y_step = 400, 300
    x_positions = [-2*x_step, -x_step, 0, x_step, 2*x_step]
    node_pos = {}
    current_y = 0
    for comp in scc_sorted:
        xi = 0
        for n in comp:
            node_pos[n] = (x_positions[xi % len(x_positions)], -current_y)
            xi += 1
        current_y += y_step
    net = Network(notebook=False, height="900px", width="100%", directed=True, cdn_resources="in_line")
    all_nodes = set(adj.keys()) | {v for lst in adj.values() for v in lst}
    for n in sorted(all_nodes):
        shape = "ellipse" if isinstance(n, str) and n.startswith("S") else "box"
        x, y = node_pos.get(n, (0, 0))
        net.add_node(n, label=n, shape=shape, color="lightblue", x=x, y=y)
    for src, dests in adj.items():
        for d in dests:
            net.add_edge(src, d, arrows="to")
    _pyvis_show(net)

# =============== GRAPHE D’UN COMPOSANT ======================
def draw_component_graph(df: pd.DataFrame, component_nodes: set):
    df_eff = df[df["Permission"].isin(["R", "W"])].copy()
    if df_eff.empty:
        st.info(tr("Aucune relation R/W à afficher.", "No R/W relationship to display."))
        return
    adj = apply_permissions(df_eff)
    net = Network(notebook=False, height="750px", width="100%", directed=True, cdn_resources="in_line")
    for n in sorted(component_nodes):
        shape = "ellipse" if isinstance(n, str) and n.startswith("S") else "box"
        net.add_node(n, label=n, shape=shape, color="lightcoral")
    for s, dests in adj.items():
        for d in dests:
            if s in component_nodes and d in component_nodes:
                net.add_edge(s, d, arrows="to")
    _pyvis_show(net, height=750)

# =============== SECTION « TABLE + GRAPHE COMBINÉ » =========
def draw_combined_graph(components_1, adj_1, labels_1,
                        components_2, labels_2, simplified_edges_2, role_data):
    all_nodes_c1 = set().union(*[set(c) for c in components_1]) if components_1 else set()
    looks_like_rbac = any(isinstance(n, str) and (n.startswith("S") or n.startswith("O")) for n in all_nodes_c1)
    if looks_like_rbac:
        allowed_subjects = {n for n in all_nodes_c1 if isinstance(n, str) and n.startswith("S")}
        allowed_objects  = {n for n in all_nodes_c1 if isinstance(n, str) and n.startswith("O")}
    else:
        allowed_subjects = set(all_nodes_c1)
        allowed_objects  = set()

    sorted_components_1 = sorted(components_1, key=len, reverse=True)
    labels_1_sorted     = [lbl for _, lbl in sorted(zip(components_1, labels_1), key=lambda t: len(t[0]), reverse=True)]

    x_gap, y_gap = 320, 240
    cur_y_left = 0
    cur_y_right = 0
    node_indices = {}
    G1 = nx.DiGraph()
    role_to_subject = {s: role_data.get(s, tr("Aucun rôle", "No role")) for s in allowed_subjects}

    net = Network(notebook=False, height="1000px", width="100%", directed=True, cdn_resources="in_line")

    for component, label in zip(sorted_components_1, labels_1_sorted):
        if looks_like_rbac:
            subjects = [s for s in component if s in allowed_subjects]
            objects  = [o for o in component if o in allowed_objects]
            for subj in subjects:
                roles = role_to_subject.get(subj, tr("Aucun rôle", "No role"))
                combined = _fmt_set(label | {subj})
                text = f'{subj}({roles}):\n{combined}'
                net.add_node(subj, label=text, shape='ellipse', x=-x_gap, y=-cur_y_left*y_gap)
                node_indices[subj] = subj
                cur_y_left += 1
            for obj in objects:
                combined = _fmt_set(label | {obj})
                net.add_node(obj, label=f'{obj}:\n{combined}', shape='box', x=x_gap, y=-cur_y_right*y_gap)
                node_indices[obj] = obj
                cur_y_right += 1
        else:
            for ent in sorted(component):
                combined = _fmt_set(label | {ent})
                net.add_node(ent, label=f'{ent}:\n{combined}', shape='box', x=-x_gap, y=-cur_y_left*y_gap)
                node_indices[ent] = ent
                cur_y_left += 1

    for src, dests in adj_1.items():
        for dest in dests:
            if src in node_indices and dest in node_indices:
                G1.add_edge(src, dest)

    if nx.is_directed_acyclic_graph(G1):
        G1 = nx.transitive_reduction(G1)
    for s, d in G1.edges():
        net.add_edge(s, d, arrows="to")

    positions = {0: (-x_gap, 450), 1: (0, 0), 2: (x_gap, 800)}
    offset_y = y_gap
    base_idx = len(net.get_nodes())

    sorted_components_2 = sorted(components_2, key=len, reverse=True)
    labels_2_sorted     = [lbl for _, lbl in sorted(zip(components_2, labels_2), key=lambda t: len(t[0]), reverse=True)]

    def comp_allowed(c):
        return any(n in all_nodes_c1 for n in c) if looks_like_rbac else True

    for i, (component, label) in enumerate(zip(sorted_components_2, labels_2_sorted)):
        if not comp_allowed(component):
            continue
        entity_name = ', '.join(component)
        combined = _fmt_set(label | set(component))
        text = f'| {entity_name}: {combined} |'
        col = i % 3
        row = i // 3
        x, y = positions[col]
        y += row * offset_y
        net.add_node(base_idx + i, label=text, shape='box', x=x, y=y,
                     width_constraint=320, height_constraint=110)

    def index_in_sorted(target_set):
        for idx, lbl in enumerate(labels_2_sorted):
            if lbl == target_set:
                return idx
        return None

    for src_set, dest_set in simplified_edges_2:
        si = index_in_sorted(src_set)
        di = index_in_sorted(dest_set)
        if si is not None and di is not None:
            net.add_edge(base_idx + si, base_idx + di, arrows="to")

    _pyvis_show(net, height="1000px", width="100%")

# =============== PROPAGATION RBAC (fichiers) =================
def propagate_rbac_from_excel(df: pd.DataFrame) -> pd.DataFrame:
    df = normalize_df(df)
    if "Role" not in df.columns: df["Role"] = None
    if "Heritage" not in df.columns: df["Heritage"] = None

    role_perms, subject_roles = {}, {}
    for _, row in df.iterrows():
        role = row.get("Role")
        subj = row.get("Source")
        perm = row.get("Permission")
        obj  = row.get("Target")
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
    return normalize_df(df)

# =============== CHARGEMENT ENTITÉS (E1,E2) =================
def load_entities_excel(file_bytes: bytes) -> pd.DataFrame:
    df_raw = pd.read_excel(io.BytesIO(file_bytes))
    cols = {c.strip().lower(): c for c in df_raw.columns}
    if not {"entity1", "entity2"} <= set(cols.keys()):
        raise ValueError(tr(
            "Le fichier 'entités' doit contenir les colonnes Entity1 et Entity2.",
            "The 'entities' file must include columns Entity1 and Entity2."
        ))
    col_e1, col_e2 = cols["entity1"], cols["entity2"]
    rows = []
    for _, row in df_raw.iterrows():
        e1 = _norm_entity(row[col_e1])
        e2 = _norm_entity(row[col_e2])
        if e1 and e2:
            rows.append({"Source": e2, "Permission": "R", "Target": e1, "Role": None, "Heritage": None})
    if not rows:
        raise ValueError(tr(
            "Aucune paire valide (Entity1, Entity2) trouvée.",
            "No valid (Entity1, Entity2) pair found."
        ))
    return normalize_df(pd.DataFrame(rows, columns=["Source", "Permission", "Target", "Role", "Heritage"]))

# =============== PERF (Tarjan vs Propagation) ===============
def evaluer_performance_interface(nb_entites: int):
    G = nx.DiGraph()
    G.add_nodes_from([f"E{i}" for i in range(nb_entites)])
    for i in range(nb_entites):
        for j in range(nb_entites):
            if i != j and random.random() < 0.01:
                G.add_edge(f"E{i}", f"E{j}")
    V = list(G.nodes)
    adj = {n: list(G.successors(n)) for n in G.nodes}

    start = time.time()
    scc = list(nx.strongly_connected_components(G))
    t_tarjan = time.time() - start

    component_map = {node: comp for comp in scc for node in comp}
    labels = {frozenset(comp): set(comp) for comp in scc}
    def dfs(node, visited, current_label):
        if node in visited: return
        visited.add(node)
        for nb in adj.get(node, []):
            nb_comp = frozenset(component_map.get(nb, []))
            current_label.update(labels.get(nb_comp, set()))
            dfs(nb, visited, current_label)

    start = time.time()
    for comp in scc:
        for node in comp:
            dfs(node, set(), labels[frozenset(comp)])
    t_labels = time.time() - start

    fig, ax = plt.subplots(figsize=(6,4))
    ax.bar([0,1], [t_tarjan, t_labels])
    ax.set_xticks([0,1]); ax.set_xticklabels(["SCC (Tarjan)","Propagation"])
    ax.set_ylabel(tr("Temps (s)", "Time (s)"))
    ax.set_title(tr(f"Performance pour {nb_entites} entités", f"Performance for {nb_entites} entities"))
    st.pyplot(fig)

# =============== VISUALISATION COMPLÈTE ====================
def process_data_display(df: pd.DataFrame, key_prefix: str = "default"):
    if df is None or df.empty:
        st.info(tr("Aucune donnée à afficher.", "No data to display."))
        return

    df_expanded = propagate_rbac_from_excel(df)
    df_effective = df_expanded[df_expanded["Permission"].isin(["R", "W"])].copy()
    if df_effective.empty:
        st.info(tr("Aucune relation R/W à afficher.", "No R/W relationship to display."))
        return

    adj = apply_permissions(df_effective)
    active_nodes = set(adj.keys())
    for lst in adj.values(): active_nodes.update(lst)

    V = sorted(active_nodes)
    scc, cmap = tarjan(V, adj)
    labels = propagate_labels(scc, adj, cmap)
    simplified = simplify_relations(labels)

    st.subheader(tr("Table des entités et étiquettes", "Entities & labels table"))
    display_entities_table(scc, labels)

    st.subheader(tr("Table RBAC (si rôles)", "RBAC table (if roles)"))
    display_role_table_streamlit(df_expanded)

    st.markdown("---")
    st.subheader(tr("Graphe combiné (entités & classes d'équivalence)", "Combined graph (entities & equivalence classes)"))
    role_map = df_expanded.set_index("Source")["Role"].to_dict() if "Role" in df_expanded.columns else {}
    draw_combined_graph(scc, adj, labels, scc, labels, simplified, role_map)

    st.markdown("---")
    st.subheader(tr("Vue principale (toutes arêtes R/W)", "Main view (all R/W edges)"))
    draw_main_graph(df_expanded)

    st.markdown("---")
    st.subheader(tr("Composants fortement connexes", "Strongly connected components"))
    if not scc:
        st.info(tr("Aucun composant.", "No component."))
        return

    cols = st.columns(4)
    for i, comp in enumerate(scc):
        label = ", ".join(sorted(comp))
        if cols[i % 4].button(tr("Voir", "View") + f": {label}", key=f"{key_prefix}_sccbtn_{i}"):
            st.session_state.selected_component = i

    if st.session_state.selected_component is not None:
        st.success(tr("Composant sélectionné", "Selected component") + f": {', '.join(sorted(scc[st.session_state.selected_component]))}")
        draw_component_graph(df_expanded, set(scc[st.session_state.selected_component]))
        if st.button("↩️ " + tr("Revenir au graphe principal", "Back to main graph"), key=f"{key_prefix}_back_to_main_graph"):
            st.session_state.selected_component = None

# ===================== CHINA-WALL CHECK =====================
def _would_violate_china_wall(df_candidate: pd.DataFrame) -> tuple[bool, str | None]:
    dfe = df_candidate[df_candidate["Permission"].isin(["R", "W"])].copy()
    if dfe.empty:
        return False, None
    adj = apply_permissions(dfe)
    V = sorted(set(adj.keys()) | {v for vs in adj.values() for v in vs})
    if not V:
        return False, None
    scc, cmap = tarjan(V, adj)
    labels = propagate_labels(scc, adj, cmap)

    for comp in labels:
        for interdit in st.session_state.interdictions_globales:
            if set(interdit).issubset(comp):
                return True, tr(
                    f"⛔ CHINA WALL : restriction globale violée pour {interdit}",
                    f"⛔ CHINA WALL: global restriction violated for {interdit}"
                )
        for ent, combos in st.session_state.interdictions_entites.items():
            if ent in comp:
                for interdit in combos:
                    if set(interdit).issubset(comp):
                        return True, tr(
                            f"⛔ CHINA WALL : restriction violée pour {ent}: {interdit}",
                            f"⛔ CHINA WALL: restriction violated for {ent}: {interdit}"
                        )
    return False, None

# =============== TERMINAL : COMMANDES ======================
def apply_prompt(global_data: pd.DataFrame, prompt: str):
    def ensure_cols(df):
        for c in ["Source","Permission","Target","Role","Heritage"]:
            if c not in df.columns: df[c] = None
        return df

    df = ensure_cols(global_data.copy())
    line = (prompt or "").strip()
    if not line: return df, tr("💬 Commande vide", "💬 Empty command")

    parts = line.split()
    command, args = parts[0], parts[1:]
    out = [tr("💬 Commande exécutée", "💬 Command executed") + f": C:\\> {line}"]

    # -------- PERF --------
    if command == "EvalPerf":
        total = len(st.session_state.sujets_definis | st.session_state.objets_definis)
        if total == 0:
            out.append(tr("⚠️ Aucune entité définie. Créez des sujets/objets d’abord.", "⚠️ No entities defined. Please create subjects or objects first."))
            return df, "\n".join(out)
        evaluer_performance_interface(total)
        out.append(tr("✅ Graphique de performance généré.", "✅ Performance chart generated."))
        return df, "\n".join(out)

    # ==================== ENTITÉS (générique) ====================
    if command == "AddEnt" and len(args) == 1:
        e = _norm_entity(args[0])
        if not e:
            out.append(tr("❌ Entité invalide.", "❌ Invalid entity.")); return df, "\n".join(out)
        exists = ((df["Source"] == e) | (df["Target"] == e)).any()
        if exists:
            out.append(tr(f"ℹ️ L'entité '{e}' existe déjà.", f"ℹ️ Entity '{e}' already exists.")); return df, "\n".join(out)
        df = pd.concat([df, pd.DataFrame([{"Source": e, "Permission": None, "Target": None, "Role": None, "Heritage": None}])], ignore_index=True)
        out.append(tr(f"✅ Entité '{e}' créée.", f"✅ Entity '{e}' created.")); return df, "\n".join(out)

    if command == "RenameEnt" and len(args) == 2:
        old, new = _norm_entity(args[0]), _norm_entity(args[1])
        if not old or not new:
            out.append(tr("❌ Usage: RenameEnt EOLD ENEW", "❌ Usage: RenameEnt EOLD ENEW")); return df, "\n".join(out)
        if not ((df["Source"] == old) | (df["Target"] == old)).any():
            out.append(tr(f"❌ Entité '{old}' introuvable.", f"❌ Entity '{old}' not found.")); return df, "\n".join(out)
        df.loc[df["Source"] == old, "Source"] = new
        df.loc[df["Target"] == old, "Target"] = new
        if old in st.session_state.sujets_definis:
            st.session_state.sujets_definis.discard(old); st.session_state.sujets_definis.add(new)
        if old in st.session_state.objets_definis:
            st.session_state.objets_definis.discard(old); st.session_state.objets_definis.add(new)
        if old in st.session_state.interdictions_entites:
            st.session_state.interdictions_entites[new] = st.session_state.interdictions_entites.pop(old)
        for i, combo in enumerate(st.session_state.interdictions_globales):
            st.session_state.interdictions_globales[i] = [new if x == old else x for x in combo]
        out.append(tr(f"✅ Entité renommée: {old} → {new}", f"✅ Entity renamed: {old} → {new}")); return df, "\n".join(out)

    if command == "AddCh" and len(args) == 2:
        e1, e2 = _norm_entity(args[0]), _norm_entity(args[1])
        if not e1 or not e2:
            out.append(tr("❌ Usage: AddCh E1 E2", "❌ Usage: AddCh E1 E2")); return df, "\n".join(out)
        temp = pd.concat([df, pd.DataFrame([{"Source": e2, "Permission": "R", "Target": e1, "Role": None, "Heritage": None}])], ignore_index=True)
        violated, msg = _would_violate_china_wall(temp)
        if violated:
            out.append(tr("⛔ Bloqué :", "⛔ Blocked:") + f" {msg}"); return df, "\n".join(out)
        df = temp
        out.append(tr(f"✅ Canal ajouté: {e1} ←R– {e2}", f"✅ Channel added: {e2} --R--> {e1}")); return df, "\n".join(out)

    if command == "DelCh" and len(args) == 2:
        e1, e2 = _norm_entity(args[0]), _norm_entity(args[1])
        before = len(df)
        df = df[~((df["Source"] == e2) & (df["Permission"] == "R") & (df["Target"] == e1))]
        out.append(tr(f"🗑️ Canaux supprimés: {before - len(df)}", f"🗑️ Channels removed: {before - len(df)}")); return df, "\n".join(out)

    if command == "DelEnt" and len(args) == 1:
        e = _norm_entity(args[0])
        before = len(df)
        df = df[~((df["Source"] == e) | (df["Target"] == e))]
        st.session_state.sujets_definis.discard(e)
        st.session_state.objets_definis.discard(e)
        st.session_state.subject_roles.pop(e, None)
        st.session_state.interdictions_entites.pop(e, None)
        st.session_state.interdictions_globales = [
            [x for x in combo if x != e] for combo in st.session_state.interdictions_globales
        ]
        out.append(tr(f"🗑️ Entité '{e}' supprimée ({before - len(df)} ligne(s)).",
                      f"🗑️ Entity '{e}' removed ({before - len(df)} row(s)).")); return df, "\n".join(out)

    # ======================= RBAC / DAC / MAC =======================
    if command == "AddObj" and len(args) == 1:
        obj = _norm_entity(args[0])
        if obj in st.session_state.objets_definis:
            out.append(tr(f"ℹ️ L'objet '{obj}' existe déjà.", f"ℹ️ Object '{obj}' already exists."))
            return df, "\n".join(out)
        st.session_state.objets_definis.add(obj)
        df = pd.concat([df, pd.DataFrame([{"Source": None,"Permission":None,"Target":obj,"Role":None,"Heritage":None}], columns=df.columns)], ignore_index=True)
        out.append(tr(f"✅ Objet '{obj}' créé.", f"✅ Object '{obj}' created."))
        return df, "\n".join(out)

    if command == "AddRole":
        if len(args)!=1:
            out.append(tr("❌ Usage: AddRole R1", "❌ Usage: AddRole R1")); return df, "\n".join(out)
        role = args[0].strip()
        if role in st.session_state.roles_definis:
            out.append(tr(f"ℹ️ Le rôle '{role}' existe déjà.", f"ℹ️ Role '{role}' already exists.")); return df, "\n".join(out)
        st.session_state.roles_definis.add(role)
        st.session_state.role_permissions.setdefault(role, set())
        out.append(tr(f"✅ Rôle '{role}' ajouté.", f"✅ Role '{role}' added.")); return df, "\n".join(out)

    # ---- AJOUT/RETRAIT DE RÔLES SUR SUJET EXISTANT ----
    if command in {"AssignRole", "AddRoleToSub", "AddSubRole", "AddRoleSub", "AddRoleToSubject"} and len(args) >= 2:
        subj = _norm_entity(args[0])
        roles = [r.strip() for r in args[1:] if r.strip()]
        if subj not in st.session_state.sujets_definis:
            out.append(tr(f"❌ Sujet '{subj}' introuvable. Utilisez AddSub d’abord.", f"❌ Subject '{subj}' not found. Use AddSub first.")); return df, "\n".join(out)
        unknown = [r for r in roles if r not in st.session_state.roles_definis]
        if unknown:
            out.append(tr(f"❌ Rôle(s) inconnu(s): {', '.join(unknown)}", f"❌ Unknown role(s): {', '.join(unknown)}")); return df, "\n".join(out)
        st.session_state.subject_roles.setdefault(subj, set())
        added = []
        for role in roles:
            if role not in st.session_state.subject_roles[subj]:
                st.session_state.subject_roles[subj].add(role)
                added.append(role)
                for perm, obj in st.session_state.role_permissions.get(role, set()):
                    if not ((df["Source"]==subj)&(df["Permission"]==perm)&(df["Target"]==obj)&(df["Role"]==role)).any():
                        df = pd.concat([df, pd.DataFrame([{"Source":subj,"Permission":perm,"Target":obj,"Role":role,"Heritage":"Role"}])], ignore_index=True)
        out.append(tr(
            f"✅ Rôle(s) assigné(s) à '{subj}': {', '.join(added) if added else '(aucun nouveau)'}",
            f"✅ Role(s) assigned to '{subj}': {', '.join(added) if added else '(none)'}"
        ))
        return df, "\n".join(out)

    if command == "UnassignRole" and len(args) >= 2:
        subj = _norm_entity(args[0])
        roles = [r.strip() for r in args[1:] if r.strip()]
        st.session_state.subject_roles.setdefault(subj, set())
        removed_any = 0
        for role in roles:
            if role in st.session_state.subject_roles[subj]:
                st.session_state.subject_roles[subj].discard(role)
                before = len(df)
                df = df[~((df["Source"]==subj) & (df["Role"]==role))]
                removed_any += before - len(df)
        out.append(tr(
            f"🗑️ Rôle(s) retiré(s) de '{subj}'. Lignes supprimées: {removed_any}.",
            f"🗑️ Role(s) removed from '{subj}'. Rows deleted: {removed_any}."
        ))
        return df, "\n".join(out)

    if command == "DelRole" and len(args) == 1:
        r = args[0].strip()
        if r not in st.session_state.roles_definis:
            out.append(tr(f"❌ Rôle '{r}' introuvable.", f"❌ Role '{r}' not found.")); return df, "\n".join(out)
        st.session_state.roles_definis.remove(r)
        st.session_state.role_permissions.pop(r, None)
        for s in list(st.session_state.subject_roles.keys()):
            st.session_state.subject_roles[s].discard(r)
        before = len(df)
        df = df[~(df["Role"] == r)]
        out.append(tr(f"🗑️ Rôle '{r}' supprimé ({before - len(df)} ligne(s)).",
                      f"🗑️ Role '{r}' removed ({before - len(df)} row(s)).")); return df, "\n".join(out)

    if command == "RenameRole" and len(args) == 2:
        old, new = args[0].strip(), args[1].strip()
        if old not in st.session_state.roles_definis:
            out.append(tr(f"❌ Rôle '{old}' introuvable.", f"❌ Role '{old}' not found.")); return df, "\n".join(out)
        if new in st.session_state.roles_definis:
            out.append(tr(f"❌ Le rôle '{new}' existe déjà.", f"❌ Role '{new}' already exists.")); return df, "\n".join(out)
        st.session_state.roles_definis.remove(old); st.session_state.roles_definis.add(new)
        st.session_state.role_permissions[new] = st.session_state.role_permissions.pop(old, set())
        for s in st.session_state.subject_roles:
            if old in st.session_state.subject_roles[s]:
                st.session_state.subject_roles[s].remove(old)
                st.session_state.subject_roles[s].add(new)
        df.loc[df["Role"] == old, "Role"] = new
        out.append(tr(f"✅ Rôle renommé: {old} → {new}", f"✅ Role renamed: {old} → {new}")); return df, "\n".join(out)

    # RBAC existants : AddSub / GrantPermission / RevokePermission
    if command == "AddSub":
        if len(args)<1:
            out.append(tr("❌ Usage: AddSub S1 [R1]", "❌ Usage: AddSub S1 [R1]")); return df, "\n".join(out)
        subject = _norm_entity(args[0])
        role = args[1].strip() if len(args)>1 else None
        if subject in st.session_state.sujets_definis:
            out.append(tr(f"ℹ️ Le sujet '{subject}' existe déjà.", f"ℹ️ Subject '{subject}' already exists.")); return df, "\n".join(out)
        if role and role not in st.session_state.roles_definis:
            out.append(tr(f"⛔ Erreur: rôle '{role}' inexistant.", f"⛔ Error: role '{role}' does not exist.")); return df, "\n".join(out)
        st.session_state.sujets_definis.add(subject)
        st.session_state.subject_roles.setdefault(subject, set())
        if role: st.session_state.subject_roles[subject].add(role)
        df = pd.concat([df, pd.DataFrame([{"Source":subject,"Permission":None,"Target":None,"Role":role,"Heritage":None}], columns=df.columns)], ignore_index=True)
        if role:
            for (perm,obj) in st.session_state.role_permissions.get(role,set()):
                mask = (df["Source"]==subject)&(df["Permission"]==perm)&(df["Target"]==obj)&(df["Role"]==role)
                if not mask.any():
                    df = pd.concat([df, pd.DataFrame([{"Source":subject,"Permission":perm,"Target":obj,"Role":role,"Heritage":"Role"}], columns=df.columns)], ignore_index=True)
        out.append(tr(f"✅ Sujet '{subject}' ajouté" + (f" avec rôle '{role}'" if role else ""),
                      f"✅ Subject '{subject}' added" + (f" with role '{role}'" if role else "")))
        return df, "\n".join(out)

    if command == "GrantPermission":
        if len(args)!=3:
            out.append(tr("❌ Usage: GrantPermission R1 R O1", "❌ Usage: GrantPermission R1 R O1")); return df, "\n".join(out)
        role, perm, obj = args[0].strip(), _norm_perm(args[1]), _norm_entity(args[2])
        if role not in st.session_state.roles_definis:
            out.append(tr(f"❌ Rôle '{role}' non défini.", f"❌ Role '{role}' is not defined.")); return df, "\n".join(out)
        if obj not in st.session_state.objets_definis:
            out.append(tr(f"❌ Objet '{obj}' inexistant. Utilisez AddObj d’abord.", f"❌ Object '{obj}' does not exist. Use AddObj first.")); return df, "\n".join(out)
        st.session_state.role_permissions.setdefault(role,set()).add((perm,obj))
        for subj, roles in st.session_state.subject_roles.items():
            if role in roles:
                mask = (df["Source"]==subj)&(df["Permission"]==perm)&(df["Target"]==obj)&(df["Role"]==role)
                if not mask.any():
                    df = pd.concat([df, pd.DataFrame([{"Source":subj,"Permission":perm,"Target":obj,"Role":role,"Heritage":"Role"}], columns=df.columns)], ignore_index=True)
        out.append(tr(f"✅ Permission '{perm}' sur '{obj}' attribuée au rôle '{role}' et propagée.",
                      f"✅ Permission '{perm}' on '{obj}' granted to role '{role}' and propagated."))
        return df, "\n".join(out)

    if command == "RevokePermission":
        if len(args)!=3:
            out.append(tr("❌ Usage: RevokePermission R1 R O1", "❌ Usage: RevokePermission R1 R O1")); return df, "\n".join(out)
        role, perm, obj = args[0].strip(), _norm_perm(args[1]), _norm_entity(args[2])
        if role not in st.session_state.roles_definis:
            out.append(tr(f"⛔ Erreur: rôle '{role}' inexistant.", f"⛔ Error: role '{role}' does not exist.")); return df, "\n".join(out)
        if obj not in st.session_state.objets_definis:
            out.append(tr(f"⛔ Erreur: objet '{obj}' inexistant.", f"⛔ Error: object '{obj}' does not exist.")); return df, "\n".join(out)
        st.session_state.role_permissions.setdefault(role,set()).discard((perm,obj))
        before = len(df)
        df = df[~((df["Permission"]==perm)&(df["Target"]==obj)&(df["Role"]==role))]
        out.append(tr(f"🗑️ Permission '{perm}' sur '{obj}' retirée du rôle '{role}' ({before-len(df)} propagation(s) supprimée(s)).",
                      f"🗑️ Permission '{perm}' on '{obj}' revoked from role '{role}' ({before-len(df)} propagation(s) removed)."))
        return df, "\n".join(out)

    # -------- DAC --------
    if len(parts)>=3 and parts[1]=="AddObj":
        owner, obj = _norm_entity(parts[0]), _norm_entity(parts[2])
        if owner not in st.session_state.sujets_definis:
            out.append(tr(f"⛔ Erreur: sujet '{owner}' inexistant. Utilisez AddSub d’abord.", f"⛔ Error: subject '{owner}' does not exist. Use AddSub first.")); return df, "\n".join(out)
        if obj in st.session_state.objets_definis:
            out.append(tr(f"ℹ️ L'objet '{obj}' existe déjà.", f"ℹ️ Object '{obj}' already exists.")); return df, "\n".join(out)
        st.session_state.objets_definis.add(obj)
        df = pd.concat([df, pd.DataFrame([{"Source":owner,"Permission":"Owner","Target":obj,"Role":None,"Heritage":None}], columns=df.columns)], ignore_index=True)
        out.append(tr(f"✅ Objet '{obj}' créé avec propriétaire '{owner}'", f"✅ Object '{obj}' created with owner '{owner}'"))
        return df, "\n".join(out)

    if len(parts)>=5 and parts[1]=="Grant":
        owner, _, subject, obj, perm = _norm_entity(parts[0]), parts[1], _norm_entity(parts[2]), _norm_entity(parts[3]), _norm_perm(parts[4])
        if owner not in st.session_state.sujets_definis:
            out.append(tr(f"⛔ Erreur: sujet '{owner}' inexistant.", f"⛔ Error: subject '{owner}' does not exist.")); return df, "\n".join(out)
        if subject not in st.session_state.sujets_definis:
            out.append(tr(f"⛔ Erreur: sujet cible '{subject}' inexistant.", f"⛔ Error: target subject '{subject}' does not exist.")); return df, "\n".join(out)
        if obj not in st.session_state.objets_definis:
            out.append(tr(f"⛔ Erreur: objet '{obj}' inexistant.", f"⛔ Error: object '{obj}' does not exist.")); return df, "\n".join(out)
        is_owner = ((df["Source"]==owner) & (df["Target"]==obj) & (df["Permission"]=="Owner")).any()
        if not is_owner:
            out.append(tr(f"⛔ Erreur: '{owner}' n'est pas le propriétaire de '{obj}'.", f"⛔ Error: '{owner}' is not the owner of '{obj}'.")); return df, "\n".join(out)
        df = pd.concat([df, pd.DataFrame([{"Source":subject,"Permission":perm,"Target":obj,"Role":None,"Heritage":None}], columns=df.columns)], ignore_index=True)
        out.append(tr(f"✅ Permission '{perm}' accordée à '{subject}' sur '{obj}' par '{owner}'.",
                      f"✅ Permission '{perm}' granted to '{subject}' on '{obj}' by '{owner}'."))
        return df, "\n".join(out)

    # -------- China Wall --------
    if command == "AddCh" and len(args) == 3:
        s, perm, o = _norm_entity(args[0]), _norm_perm(args[1]), _norm_entity(args[2])
        if perm not in {"R","W"}:
            out.append(tr("❌ La permission doit être R ou W.", "❌ Permission must be R or W.")); return df, "\n".join(out)
        temp = pd.concat([df, pd.DataFrame([{"Source":s,"Permission":perm,"Target":o,"Role":None,"Heritage":None}])], ignore_index=True)
        violated, msg = _would_violate_china_wall(temp)
        if violated:
            out.append(tr("⛔ Bloqué :", "⛔ Blocked:") + f" {msg}"); return df, "\n".join(out)
        df = temp
        out.append(tr(f"✅ Canal ajouté: {s} --{perm}--> {o}", f"✅ Channel added: {s} --{perm}--> {o}")); return df, "\n".join(out)

    if command == "Never":
        if "for" in args:
            idx = args.index("for")
            etiquettes = [e.strip("{} ,") for e in args[:idx]]
            entites = [e.strip("{} ,") for e in args[idx+1:]]
            for ent in entites:
                st.session_state.interdictions_entites.setdefault(ent, []).append(etiquettes)
            out.append(tr(f"🚧 Combinaison interdite {etiquettes} pour entités: {entites}",
                          f"🚧 Forbidden combination {etiquettes} for entities: {entites}"))
            return df, "\n".join(out)
        etiquettes = [e.strip("{} ,") for e in args]
        st.session_state.interdictions_globales.append(etiquettes)
        out.append(tr(f"🚧 Combinaison globalement interdite: {etiquettes}",
                      f"🚧 Globally forbidden combination: {etiquettes}"))
        return df, "\n".join(out)

    if command == "RemoveGlobalBlock" and args:
        target = [e.strip("{} ,") for e in args]
        before = len(st.session_state.interdictions_globales)
        st.session_state.interdictions_globales = [
            combo for combo in st.session_state.interdictions_globales
            if combo != target
        ]
        out.append(tr(f"🗑️ Blocage global retiré ({before - len(st.session_state.interdictions_globales)}).",
                      f"🗑️ Global block removed ({before - len(st.session_state.interdictions_globales)})."))
        return df, "\n".join(out)

    if command == "ClearGlobalBlocks":
        count = len(st.session_state.interdictions_globales)
        st.session_state.interdictions_globales.clear()
        out.append(tr(f"🧹 Blocages globaux effacés ({count}).", f"🧹 Global blocks cleared ({count})."))
        return df, "\n".join(out)

    if command == "RemoveEntityBlock" and "for" in args:
        idx = args.index("for")
        etiquettes = [e.strip("{} ,") for e in args[:idx]]
        ent = args[idx+1].strip("{} ,")
        removed = 0
        combos = st.session_state.interdictions_entites.get(ent, [])
        newc = []
        for c in combos:
            if c == etiquettes:
                removed += 1
            else:
                newc.append(c)
        if removed:
            st.session_state.interdictions_entites[ent] = newc
        out.append(tr(f"🗑️ Blocage retiré pour {ent} ({removed}).", f"🗑️ Entity block removed for {ent} ({removed})."))
        return df, "\n".join(out)

    if command == "ClearEntityBlocks" and len(args) == 1:
        ent = args[0]
        count = len(st.session_state.interdictions_entites.get(ent, []))
        st.session_state.interdictions_entites.pop(ent, None)
        out.append(tr(f"🧹 Blocages effacés pour {ent} ({count}).", f"🧹 Blocks cleared for {ent} ({count})."))
        return df, "\n".join(out)

    if command == "show":
        process_data_display(df, key_prefix="terminal_show")
        out.append(tr("🚀 Génération des graphes…", "🚀 Generating graphs…"))
        return df, "\n".join(out)

    out.append(tr("❌ Commande inconnue.", "❌ Unknown command."))
    return df, "\n".join(out)

# ======================= UI / CALLBACK =====================
def _run_command_callback():
    cmd = st.session_state.get("cmd_input", "").strip()
    if not cmd: return
    st.session_state.global_data, message = apply_prompt(st.session_state.global_data, cmd)
    st.session_state.history.append(f"{message}")
    st.session_state.cmd_input = ""
    st.rerun()

# ======== Texte d'aide TERMINAL (FR/EN) ========
def terminal_help_text() -> str:
    if st.session_state.lang == "fr":
        return (
            "### Aide des commandes (FR)\n"
            "**Utilisation :** entrez la commande puis appuyez sur **Entrée**.\n\n"

            "**VERSION ENTITÉ**\n"
            "Étape 1 : Création des entités → `AddEnt E1`  \n"
            "Étape 2 : Création des entités → `AddEnt E2`  \n"
            "Étape 3 : Création des canaux → `AddCh E1 E2`  \n"
            "Modifs : `RenameEnt E1 E1X`  \n"
            "Suppression : `DelEnt E1` · `DelCh E1 E2`\n\n"

            "**MODÈLE DAC**\n"
            "Étape 1 : Création des sujets → `AddSub S2`  \n"
            "Étape 2 : Création des sujets → `AddSub S3`  \n"
            "Étape 3 : Création d’un objet avec propriétaire → `S2 AddObj O2`  \n"
            "Étape 4 : Attribuer une permission du propriétaire → `S2 Grant S3 O2 R`  \n"
            "Modifs : `DelSub S2` · `RenameSub S2 S2X` · `DelObj O2` · `RenameObj O2 O2X`\n\n"

            "**MODÈLE MAC**\n"
            "Étape 1 : Création des sujets → `AddSub S1`  \n"
            "Étape 2 : Création des objets → `AddObj O1`  \n"
            "Étape 3 : Création des canaux → `AddCh S1 R O1`\n\n"

            "**CHINA-WALL**\n"
            "Étape 1 : Création des sujets → `AddSub S1`  \n"
            "Étape 2 : Création des objets → `AddObj O1`  \n"
            "Étape 3 : Définir la restriction → `Never {S1, O1}`  \n"
            "Étape 4 : Tester un canal → `AddCh S1 R O1`  \n"
            "Modifs des règles : `RemoveGlobalBlock S1 O1` · `ClearGlobalBlocks` · `RemoveEntityBlock A B for E1` · `ClearEntityBlocks E1`\n\n"

            "**MODÈLE RBAC**\n"
            "Étape 1 : Création des objets → `AddObj O1`  \n"
            "Étape 2 : Création des rôles → `AddRole R1`  \n"
            "Étape 3 : Permission du rôle → `GrantPermission R1 R O1`  \n"
            "Étape 4 : Création d’un sujet avec rôle → `AddSub S1 R1`  \n"
            "Ajouter un rôle à un sujet existant → `AssignRole S1 R2` (multi : `AssignRole S1 R2 R3`)  \n"
            "Retirer un rôle d’un sujet → `UnassignRole S1 R2`  \n"
            "Modifs : `DelRole R1` · `RenameRole R1 R1X` · `RevokePermission R1 R O1`\n"
        )
    else:
        return (
            "### Commands help (EN)\n"
            "**Usage:** type a command and press **Enter**.\n\n"

            "**ENTITY VERSION**\n"
            "Step 1: Create entities → `AddEnt E1`  \n"
            "Step 2: Create entities → `AddEnt E2`  \n"
            "Step 3: Create channels → `AddCh E1 E2`  \n"
            "Edits: `RenameEnt E1 E1X`  \n"
            "Delete: `DelEnt E1` · `DelCh E1 E2`\n\n"

            "**DAC MODEL**\n"
            "Step 1: Create subjects → `AddSub S2`  \n"
            "Step 2: Create subjects → `AddSub S3`  \n"
            "Step 3: Create an owned object → `S2 AddObj O2`  \n"
            "Step 4: Grant owner's permission → `S2 Grant S3 O2 R`  \n"
            "Edits: `DelSub S2` · `RenameSub S2 S2X` · `DelObj O2` · `RenameObj O2 O2X`\n\n"

            "**MAC MODEL**\n"
            "Step 1: Create subjects → `AddSub S1`  \n"
            "Step 2: Create objects → `AddObj O1`  \n"
            "Step 3: Create channels → `AddCh S1 R O1`\n\n"

            "**CHINA-WALL**\n"
            "Step 1: Create subjects → `AddSub S1`  \n"
            "Step 2: Create objects → `AddObj O1`  \n"
            "Step 3: Set restriction → `Never {S1, O1}`  \n"
            "Step 4: Test a channel → `AddCh S1 R O1`  \n"
            "Rule edits: `RemoveGlobalBlock S1 O1` · `ClearGlobalBlocks` · `RemoveEntityBlock A B for E1` · `ClearEntityBlocks E1`\n\n"

            "**RBAC MODEL**\n"
            "Step 1: Create objects → `AddObj O1`  \n"
            "Step 2: Create roles → `AddRole R1`  \n"
            "Step 3: Grant role permission → `GrantPermission R1 R O1`  \n"
            "Step 4: Create a subject with role → `AddSub S1 R1`  \n"
            "Add a role to an existing subject → `AssignRole S1 R2` (multi: `AssignRole S1 R2 R3`)  \n"
            "Remove a role from a subject → `UnassignRole S1 R2`  \n"
            "Edits: `DelRole R1` · `RenameRole R1 R1X` · `RevokePermission R1 R O1`\n"
        )

# ======== Aide Excel (FR/EN) ========
def excel_help_text() -> str:
    if st.session_state.lang == "fr":
        return (
            "### 📂 Aide Excel (comment structurer vos fichiers)\n"
            "Deux formats sont supportés :\n"
            "1) **RBAC** avec les colonnes **`Source`**, **`Permission`**, **`Target`**, **`Role`** *(et optionnel `Heritage`)*.\n"
            "2) **Entités** avec les colonnes **`Entity1`**, **`Entity2`** (canaux entre entités génériques).\n\n"
            "#### Exemple RBAC\n"
            "```\n"
            "   Exemple :\n"
            "   | Source | Permission | Target | Role |\n"
            "   |--------|------------|--------|------|\n"
            "   | S1     | R          | O1     | R1   |\n"
            "   | S2     | W          | O2     | R2   |\n\n"
            "- **Entités** → colonnes `Entity1`, `Entity2`.\n"
            
            "```\n"
            "➡️ Les rôles sont propagés automatiquement (si un sujet a `R1`, il hérite des permissions de `R1`).\n\n"
            "#### Exemple Entités\n"
            "```\n"
            "Entity1,Entity2\n"
            "   Exemple :\n"
            "   | Entity1 | Entity2 |\n"
            "   |---------|---------|\n"
            "   | E1      | E2      |\n"
            "   | E2      | E3      |\n\n"
            "```\n"
            "➡️ Ces paires créent des **canaux** (E2 --R--> E1, etc.) et permettent d’afficher **le graphe d’entités** même sans sujets/objets.\n\n"
            "#### Normalisation automatique\n"
            "- Les identifiants sont **nettoyés** et **normalisés** (ex: `e01` → `E1`, `s0003` → `S3`).\n"
            "- Les permissions sont mises en majuscules (`r` → `R`, `w` → `W`).\n\n"
            "#### Conseils\n"
            "- Vérifiez l’orthographe exacte des noms de colonnes.\n"
            "- Évitez les cellules vides. Une ligne incomplète sera ignorée.\n"
            "- Pour le **graphe combiné**, un minimum de relations (R/W ou paires Entity1/Entity2) est requis.\n"
        )
    else:
        return (
            "### 📂 Excel help (how to structure files)\n"
            "Two formats are supported:\n"
            "1) **RBAC** with columns **`Source`**, **`Permission`**, **`Target`**, **`Role`** *(optional `Heritage`)*.\n"
            "2) **Entities** with columns **`Entity1`**, **`Entity2`** (generic entity channels).\n\n"
            "#### RBAC example\n"
            "```\n"
            "   Example:\n"
            "   | Source | Permission | Target | Role |\n"
            "   |--------|------------|--------|------|\n"
            "   | S1     | R          | O1     | R1   |\n"
            "   | S2     | W          | O2     | R2   |\n\n"

            "```\n"
            "➡️ Roles are propagated automatically (if a subject has `R1`, it inherits `R1` permissions).\n\n"
            "#### Entities example\n"
            "```\n"
            "   | Entity1 | Entity2 |\n"
            "   |---------|---------|\n"
            "   | E1      | E2      |\n"
            "   | E2      | E3      |\n\n"
            "```\n"
            "➡️ These pairs create **channels** (E2 --R--> E1, etc.) and allow the **entity graph** even without subjects/objects.\n\n"
            "#### Auto-normalization\n"
            "- Identifiers are **cleaned** and **normalized** (e.g., `e01` → `E1`, `s0003` → `S3`).\n"
            "- Permissions are upper-cased (`r` → `R`, `w` → `W`).\n\n"
            "#### Tips\n"
            "- Check column names exactly.\n"
            "- Avoid empty cells. Incomplete rows are ignored.\n"
            "- The **combined graph** needs at least a few relations (R/W or Entity1/Entity2 pairs).\n"
        )

# ============================== MAIN ==============================
def main():

    tabs = st.tabs([tr("📂 Fichier Excel", "📂 Excel File"),
                    tr("⌨️ Terminal", "⌨️ Terminal"),
                    tr("📊 Perf", "📊 Perf")])

    # ------- Onglet Excel -------
    with tabs[0]:
        st.write(tr(
            "Charge un fichier **RBAC** (Source, Permission, Target, Role) ou **Entités** (Entity1, Entity2).",
            "Upload a **RBAC** file (Source, Permission, Target, Role) or **Entities** file (Entity1, Entity2)."
        ))
        up = st.file_uploader(tr("Importer un fichier Excel", "Upload an Excel file"), type=["xlsx"])
        if up:
            try:
                content = up.getvalue()
                probe = pd.read_excel(io.BytesIO(content))
                cols_lower = {c.strip().lower() for c in probe.columns}
                if {"entity1","entity2"} <= cols_lower:
                    df = load_entities_excel(content)
                else:
                    df = pd.read_excel(io.BytesIO(content))
                    req = {"Source","Permission","Target"}
                    missing = req - set(df.columns)
                    if missing: raise ValueError(tr(f"Colonnes manquantes: {missing}", f"Missing columns: {missing}"))
                    if "Role" not in df.columns: df["Role"] = None
                    if "Heritage" not in df.columns: df["Heritage"] = None
                    df = normalize_df(df)
                st.session_state.global_data = df
                st.success(tr("✅ Fichier chargé.", "✅ File loaded."))
                with st.expander(tr("Voir les données chargées", "View loaded data")):
                    st.dataframe(df, use_container_width=True)
            except Exception as e:
                st.error(tr(f"Erreur de lecture du fichier: {e}", f"File read error: {e}"))

        with st.expander(tr("Aide Excel", "Excel help"), expanded=False):
            st.markdown(excel_help_text())

        st.markdown("---")
        st.subheader(tr("Visualisations", "Visualizations"))
        process_data_display(st.session_state.global_data, key_prefix="excel")

    # ------- Onglet Terminal -------
    with tabs[1]:
        st.markdown(terminal_help_text())
        st.text_input("C:\\>", key="cmd_input", placeholder=tr("Ex: AssignRole S1 R2 R3", "Ex: AssignRole S1 R2 R3"), on_change=_run_command_callback)
        st.text_area(tr("Historique", "History"), "\n\n".join(st.session_state.history), height=340)

        st.markdown("---")
        st.subheader(tr("Graphes (issus des commandes)", "Graphs (from commands)"))
        process_data_display(st.session_state.global_data, key_prefix="terminal")

    # ------- Onglet Perf -------
    with tabs[2]:
        st.write(tr("Mesure des temps (SCC vs propagation) sur un graphe aléatoire clairsemé.",
                    "Timing (SCC vs propagation) on a sparse random graph."))
        n = st.slider(tr("Nombre d'entités", "Number of entities"), 20, 2000, 200, step=20)
        if st.button(tr("Lancer EvalPerf", "Run EvalPerf")):
            evaluer_performance_interface(n)

if __name__ == "__main__":
    main()
