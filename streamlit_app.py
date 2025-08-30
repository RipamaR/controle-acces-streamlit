# streamlit_app.py
# -----------------------------------------------------------
# Interface graphique pour la représentation de contrôle de flux de données sécuritaires – DAC / MAC / RBAC / ABAC
# Version intégrée avec:
#  - Graphe principal + graphe par composant (SCC)
#  - Tableau entités/étiquettes trié
#  - Terminal de commandes
#  - EvalPerf (benchmark Tarjan / propagation)
#  - Chargement Excel (RBAC ou Entités)
#  - China Wall (règles d’incompatibilité)
#  - i18n (Français / English)
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
    page_title="Interface graphique – DAC / MAC / RBAC / ABAC",
    layout="wide"
)

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

# ---- Propagation CORRIGÉE : sur le DAG de composantes ----
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
# ----------------------------------------------------------

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
        tr("Entités", "Entities"): [", ".join(sorted(c)) for c in components],
        tr("Leurs étiquettes", "Their labels"): [_fmt_set(lbl | set(comp)) for comp, lbl in zip(components, labels)],
        "_NBL_": [len(lbl) for lbl in labels],
    }
    df = pd.DataFrame(data).sort_values(by="_NBL_", ascending=False).drop(columns=["_NBL_"])
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
        st.info(tr("Aucune relation R/W à afficher.", "No R/W relation to display."))
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
        st.info(tr("Aucune relation R/W à afficher.", "No R/W relation to display."))
        return
    adj = apply_permissions(df_eff)
    net = Network(notebook=False, height="750px", width="100%", directed=True, cdn_resources="in_line")
    for n in sorted(component_nodes):
        shape = "ellipse" if n.startswith("S") else "box"
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
    role_to_subject = {s: role_data.get(s, tr("Sans rôle", "No role")) for s in allowed_subjects}

    net = Network(notebook=False, height="1000px", width="100%", directed=True, cdn_resources="in_line")

    for component, label in zip(sorted_components_1, labels_1_sorted):
        if looks_like_rbac:
            subjects = [s for s in component if s in allowed_subjects]
            objects  = [o for o in component if o in allowed_objects]
            for subj in subjects:
                roles = role_to_subject.get(subj, tr("Sans rôle", "No role"))
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

    _pyvis_show(net, height=1000, width=1800)

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
            "The 'entities' file must contain columns Entity1 and Entity2."
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
    ax.set_xticks([0,1]); ax.set_xticklabels([tr("SCC (Tarjan)","SCC (Tarjan)"), tr("Propagation","Propagation")])
    ax.set_ylabel(tr("Temps (s)", "Time (s)"))
    ax.set_title(tr("Performance pour {n} entités", "Performance for {n} entities").format(n=nb_entites))
    st.pyplot(fig)

# =============== Vérification China Wall ====================
def check_china_wall(df_after: pd.DataFrame):
    """
    Retourne (ok, message). ok=False si une règle est violée.
    """
    try:
        df_expanded = propagate_rbac_from_excel(df_after)
        df_effective = df_expanded[df_expanded["Permission"].isin(["R", "W"])].copy()
        if df_effective.empty:
            return True, None

        adj = apply_permissions(df_effective)
        active_nodes = set(adj.keys())
        for lst in adj.values(): active_nodes.update(lst)
        V = sorted(active_nodes)
        scc, cmap = tarjan(V, adj)
        labels = propagate_labels(scc, adj, cmap)

        comp_sets = [lbl | set(comp) for comp, lbl in zip(scc, labels)]

        for comp in comp_sets:
            for interdit in st.session_state.interdictions_globales:
                if set(interdit).issubset(comp):
                    return False, tr(
                        "⛔ CHINA WALL ERROR: Violation globale pour {x}",
                        "⛔ CHINA WALL ERROR: Global restriction violated for {x}",
                        x=interdit
                    )

        for comp in comp_sets:
            for ent, combos in st.session_state.interdictions_entites.items():
                if ent in comp:
                    for interdit in combos:
                        if set(interdit).issubset(comp):
                            return False, tr(
                                "⛔ CHINA WALL ERROR: Violation pour {e} : {x}",
                                "⛔ CHINA WALL ERROR: Restriction violated for {e}: {x}",
                                e=ent, x=interdit
                            )

        return True, None
    except Exception as e:
        return True, tr(
            "⚠️ Vérification China Wall ignorée (erreur: {err})",
            "⚠️ China Wall check skipped (error: {err})",
            err=e
        )

# =============== VISUALISATION COMPLÈTE ====================
def process_data_display(df: pd.DataFrame, key_prefix: str = "default"):
    if df is None or df.empty:
        st.info(tr("Aucune donnée à afficher.", "Nothing to display."))
        return

    df_expanded = propagate_rbac_from_excel(df)
    df_effective = df_expanded[df_expanded["Permission"].isin(["R", "W"])].copy()
    if df_effective.empty:
        st.info(tr("Aucune relation R/W à afficher.", "No R/W relation to display."))
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
        if cols[i % 4].button(tr("Voir: {x}", "View: {x}").format(x=label), key=f"{key_prefix}_sccbtn_{i}"):
            st.session_state.selected_component = i

    if st.session_state.selected_component is not None:
        st.success(tr(
            "Composant sélectionné: {x}",
            "Selected component: {x}"
        ).format(x=', '.join(sorted(scc[st.session_state.selected_component]))))
        draw_component_graph(df_expanded, set(scc[st.session_state.selected_component]))

    st.markdown("---")
    st.subheader(tr("Graphe combiné (entités & classes d'équivalence)", "Combined graph (entities & equivalence classes)"))
    role_map = df_expanded.set_index("Source")["Role"].to_dict() if "Role" in df_expanded.columns else {}
    draw_combined_graph(scc, adj, labels, scc, labels, simplified, role_map)

# =============== TERMINAL : COMMANDES ======================
def apply_prompt(global_data: pd.DataFrame, prompt: str):
    def ensure_cols(df):
        for c in ["Source","Permission","Target","Role","Heritage"]:
            if c not in df.columns: df[c] = None
        return df

    df = ensure_cols(global_data.copy())
    line = (prompt or "").strip()
    if not line: 
        return df, tr("💬 Commande vide", "💬 Empty command")

    parts = line.split()
    command, args = parts[0], parts[1:]
    out = [tr("💬 Commande exécutée: C:\\> {x}", "💬 Command executed: C:\\> {x}").format(x=line)]

    if command == "EvalPerf":
        total = len(st.session_state.sujets_definis | st.session_state.objets_definis)
        if total == 0:
            out.append(tr(
                "⚠️ Aucune entité définie. Créez d'abord des sujets ou des objets.",
                "⚠️ No entities defined. Please create subjects or objects first."
            ))
            return df, "\n".join(out)
        evaluer_performance_interface(total)
        out.append(tr("✅ Graphique de performance généré.", "✅ Performance chart generated."))
        return df, "\n".join(out)

    if command == "AddObj" and len(args) == 1:
        obj = _norm_entity(args[0])
        if obj in st.session_state.objets_definis:
            out.append(tr("ℹ️ L'objet '{x}' existe déjà.", "ℹ️ The object '{x}' already exists.").format(x=obj))
            return df, "\n".join(out)
        st.session_state.objets_definis.add(obj)
        df = pd.concat([df, pd.DataFrame([{"Source": None,"Permission":None,"Target":obj,"Role":None,"Heritage":None}], columns=df.columns)], ignore_index=True)
        out.append(tr("✅ Objet '{x}' créé.", "✅ Object '{x}' created.").format(x=obj))
        return df, "\n".join(out)

    if command == "AddRole":
        if len(args)!=1:
            out.append(tr("❌ Usage: AddRole R1", "❌ Usage: AddRole R1")); return df, "\n".join(out)
        role = args[0].strip()
        if role in st.session_state.roles_definis:
            out.append(tr("ℹ️ Le rôle '{x}' existe déjà.", "ℹ️ Role '{x}' already exists.").format(x=role)); return df, "\n".join(out)
        st.session_state.roles_definis.add(role)
        st.session_state.role_permissions.setdefault(role, set())
        out.append(tr("✅ Rôle '{x}' ajouté.", "✅ Role '{x}' added.").format(x=role)); return df, "\n".join(out)

    if command == "AddSub":
        if len(args)<1:
            out.append(tr("❌ Usage: AddSub S1 [R1]", "❌ Usage: AddSub S1 [R1]")); return df, "\n".join(out)
        subject = _norm_entity(args[0])
        role = args[1].strip() if len(args)>1 else None
        if subject in st.session_state.sujets_definis:
            out.append(tr("ℹ️ Le sujet '{x}' existe déjà.", "ℹ️ The subject '{x}' already exists.").format(x=subject)); return df, "\n".join(out)
        if role and role not in st.session_state.roles_definis:
            out.append(tr("⛔ Erreur: le rôle '{x}' n'existe pas.", "⛔ Error: Role '{x}' does not exist.").format(x=role)); return df, "\n".join(out)
        st.session_state.sujets_definis.add(subject)
        st.session_state.subject_roles.setdefault(subject, set())
        if role: st.session_state.subject_roles[subject].add(role)
        df = pd.concat([df, pd.DataFrame([{"Source":subject,"Permission":None,"Target":None,"Role":role,"Heritage":None}], columns=df.columns)], ignore_index=True)
        if role:
            for (perm,obj) in st.session_state.role_permissions.get(role,set()):
                mask = (df["Source"]==subject)&(df["Permission"]==perm)&(df["Target"]==obj)&(df["Role"]==role)
                if not mask.any():
                    df = pd.concat([df, pd.DataFrame([{"Source":subject,"Permission":perm,"Target":obj,"Role":role,"Heritage":"Role"}], columns=df.columns)], ignore_index=True)
        out.append(tr("✅ Sujet '{s}' ajouté{r}.", "✅ Subject '{s}' added{r}.").format(
            s=subject, r=tr(" avec le rôle '{x}'", " with role '{x}'").format(x=role) if role else ""))
        return df, "\n".join(out)

    if command == "GrantPermission":
        if len(args)!=3:
            out.append(tr("❌ Usage: GrantPermission R1 R O1", "❌ Usage: GrantPermission R1 R O1")); return df, "\n".join(out)
        role, perm, obj = args[0].strip(), _norm_perm(args[1]), _norm_entity(args[2])
        if role not in st.session_state.roles_definis:
            out.append(tr("❌ Rôle '{x}' non défini.", "❌ Role '{x}' is not defined.").format(x=role)); return df, "\n".join(out)
        if obj not in st.session_state.objets_definis:
            out.append(tr("❌ L'objet '{x}' n'existe pas. Utilisez AddObj d'abord.", "❌ Object '{x}' does not exist. Use AddObj first.").format(x=obj)); return df, "\n".join(out)
        st.session_state.role_permissions.setdefault(role,set()).add((perm,obj))
        for subj, roles in st.session_state.subject_roles.items():
            if role in roles:
                mask = (df["Source"]==subj)&(df["Permission"]==perm)&(df["Target"]==obj)&(df["Role"]==role)
                if not mask.any():
                    df = pd.concat([df, pd.DataFrame([{"Source":subj,"Permission":perm,"Target":obj,"Role":role,"Heritage":"Role"}], columns=df.columns)], ignore_index=True)
        out.append(tr("✅ Permission '{p}' sur '{o}' accordée au rôle '{r}' et propagée.",
                      "✅ Permission '{p}' on '{o}' granted to role '{r}' and propagated.").format(p=perm, o=obj, r=role))
        return df, "\n".join(out)

    if command == "RevokePermission":
        if len(args)!=3:
            out.append(tr("❌ Usage: RevokePermission R1 R O1", "❌ Usage: RevokePermission R1 R O1")); return df, "\n".join(out)
        role, perm, obj = args[0].strip(), _norm_perm(args[1]), _norm_entity(args[2])
        if role not in st.session_state.roles_definis:
            out.append(tr("⛔ Erreur: le rôle '{x}' n'existe pas.", "⛔ Error: Role '{x}' does not exist.").format(x=role)); return df, "\n".join(out)
        if obj not in st.session_state.objets_definis:
            out.append(tr("⛔ Erreur: l'objet '{x}' n'existe pas.", "⛔ Error: Object '{x}' does not exist.").format(x=obj)); return df, "\n".join(out)
        st.session_state.role_permissions.setdefault(role,set()).discard((perm,obj))
        before = len(df)
        df = df[~((df["Permission"]==perm)&(df["Target"]==obj)&(df["Role"]==role))]
        out.append(tr("🗑️ Permission '{p}' sur '{o}' retirée du rôle '{r}' ({n} propagation(s) supprimée(s)).",
                      "🗑️ Permission '{p}' on '{o}' revoked from role '{r}' ({n} propagation(s) removed).").format(
            p=perm, o=obj, r=role, n=before-len(df)))
        return df, "\n".join(out)

    if len(parts)>=3 and parts[1]=="AddObj":
        owner, obj = _norm_entity(parts[0]), _norm_entity(parts[2])
        if owner not in st.session_state.sujets_definis:
            out.append(tr("⛔ Erreur: le sujet '{x}' n'existe pas. Utilisez AddSub d'abord.",
                          "⛔ Error: Subject '{x}' does not exist. Use AddSub first.").format(x=owner)); return df, "\n".join(out)
        if obj in st.session_state.objets_definis:
            out.append(tr("ℹ️ L'objet '{x}' existe déjà.", "ℹ️ The object '{x}' already exists.").format(x=obj)); return df, "\n".join(out)
        st.session_state.objets_definis.add(obj)
        df = pd.concat([df, pd.DataFrame([{"Source":owner,"Permission":"Owner","Target":obj,"Role":None,"Heritage":None}], columns=df.columns)], ignore_index=True)
        out.append(tr("✅ Objet '{o}' créé avec le propriétaire '{s}'", "✅ Object '{o}' created with owner '{s}'").format(o=obj, s=owner))
        return df, "\n".join(out)

    if len(parts)>=5 and parts[1]=="Grant":
        owner, _, subject, obj, perm = _norm_entity(parts[0]), parts[1], _norm_entity(parts[2]), _norm_entity(parts[3]), _norm_perm(parts[4])
        if owner not in st.session_state.sujets_definis:
            out.append(tr("⛔ Erreur: le sujet '{x}' n'existe pas.", "⛔ Error: Subject '{x}' does not exist.").format(x=owner)); return df, "\n".join(out)
        if subject not in st.session_state.sujets_definis:
            out.append(tr("⛔ Erreur: le sujet cible '{x}' n'existe pas.", "⛔ Error: Target subject '{x}' does not exist.").format(x=subject)); return df, "\n".join(out)
        if obj not in st.session_state.objets_definis:
            out.append(tr("⛔ Erreur: l'objet '{x}' n'existe pas.", "⛔ Error: Object '{x}' does not exist.").format(x=obj)); return df, "\n".join(out)
        is_owner = ((df["Source"]==owner) & (df["Target"]==obj) & (df["Permission"]=="Owner")).any()
        if not is_owner:
            out.append(tr("⛔ Erreur: '{o}' n'est pas propriétaire de '{x}'.", "⛔ Error: '{o}' is not the owner of '{x}'.").format(o=owner, x=obj)); return df, "\n".join(out)
        df = pd.concat([df, pd.DataFrame([{"Source":subject,"Permission":perm,"Target":obj,"Role":None,"Heritage":None}], columns=df.columns)], ignore_index=True)
        out.append(tr("✅ Permission '{p}' accordée à '{s}' sur '{o}' par '{w}'.",
                      "✅ Permission '{p}' granted to '{s}' on '{o}' by '{w}'.").format(p=perm, s=subject, o=obj, w=owner))
        return df, "\n".join(out)

    if command == "Never":
        if "for" in args:
            idx = args.index("for")
            etiquettes = [e.strip("{} ,") for e in args[:idx]]
            entites = [e.strip("{} ,") for e in args[idx+1:]]
            for ent in entites:
                st.session_state.interdictions_entites.setdefault(ent, []).append(etiquettes)
            out.append(tr("🚧 Combinaison interdite {x} pour: {e}",
                          "🚧 Forbidden combination {x} for entities: {e}").format(x=etiquettes, e=entites))
            return df, "\n".join(out)
        etiquettes = [e.strip("{} ,") for e in args]
        st.session_state.interdictions_globales.append(etiquettes)
        out.append(tr("🚧 Combinaison globale interdite: {x}", "🚧 Globally forbidden combination: {x}").format(x=etiquettes))
        return df, "\n".join(out)

    # -------- AddCh (avec contrôle China-Wall) ----------
    if command == "AddCh":
        # Formes: AddCh E1 E2 | AddCh S1 R O1 | AddCh S1 R R1 O1
        if len(args) == 2:
            source = _norm_entity(args[0]); permission = "R"; role = None; target = _norm_entity(args[1])
        elif len(args) == 3:
            source = _norm_entity(args[0]); permission = _norm_perm(args[1]); role = None; target = _norm_entity(args[2])
        elif len(args) == 4:
            source = _norm_entity(args[0]); permission = _norm_perm(args[1]); role = args[2].strip(); target = _norm_entity(args[3])
        else:
            out.append(tr("❌ Usage: AddCh E1 E2  |  AddCh S1 R O1  |  AddCh S1 R R1 O1",
                          "❌ Usage: AddCh E1 E2  |  AddCh S1 R O1  |  AddCh S1 R R1 O1"))
            return df, "\n".join(out)

        temp = pd.concat([df, pd.DataFrame([{
            "Source": source, "Permission": permission, "Target": target, "Role": role, "Heritage": None
        }], columns=df.columns)], ignore_index=True)

        ok, msg = check_china_wall(temp)
        if not ok:
            return df, "\n".join(out + [msg])

        df = normalize_df(temp)
        if len(args) == 2:
            out.append(tr("✅ Canal ajouté: {a} --R--> {b}", "✅ Channel added: {a} --R--> {b}").format(a=source, b=target))
        else:
            out.append(tr("✅ Canal ajouté: {a} --{p}/{r}--> {b}",
                          "✅ Channel added: {a} --{p}/{r}--> {b}").format(a=source, p=permission, r=role, b=target))
        return df, "\n".join(out)

    # --- AddEnt (entités neutres) ---------------------------------------
    if command == "AddEnt":
        if len(args) != 1:
            out.append(tr("❌ Usage: AddEnt E1", "❌ Usage: AddEnt E1"))
            return df, "\n".join(out)
        ent = _norm_entity(args[0])
        df = pd.concat([df, pd.DataFrame([{
            "Source": ent, "Permission": None, "Target": None, "Role": None, "Heritage": None
        }], columns=df.columns)], ignore_index=True)
        out.append(tr("✅ Entité '{e}' ajoutée (sans lien). Utilisez 'AddCh E1 E2' pour créer un lien.",
                      "✅ Entity '{e}' added (no link). Use 'AddCh E1 E2' to create a link.").format(e=ent))
        return df, "\n".join(out)

    if command == "show":
        process_data_display(df, key_prefix="terminal_show")
        out.append(tr("🚀 Génération des graphes…", "🚀 Rendering graphs…"))
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

def main():
    # --- Sidebar: language switch ---
    st.sidebar.markdown("## 🌐 Language / Langue")
    choice = st.sidebar.selectbox("Language / Langue", ["Français", "English"],
                                  index=0 if st.session_state.lang=="fr" else 1)
    st.session_state.lang = "fr" if choice == "Français" else "en"

    st.title(tr(
        "🔐 Interface graphique pour la représentation de contrôle de flux de données sécuritaires – DAC / MAC / RBAC / ABAC",
        "🔐 Visual interface for secure data-flow control – DAC / MAC / RBAC / ABAC"
    ))

    tabs = st.tabs([
        tr("📂 Fichier Excel", "📂 Excel file"),
        tr("⌨️ Terminal", "⌨️ Terminal"),
    ])

    # ------- Onglet Excel -------
    with tabs[0]:
        st.write(tr(
            "Charge un fichier **RBAC** (Source, Permission, Target, Role) ou **Entités** (Entity1, Entity2).",
            "Upload a **RBAC** file (Source, Permission, Target, Role) or **Entities** (Entity1, Entity2)."
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
                    if missing:
                        raise ValueError(tr("Colonnes manquantes: {x}", "Missing columns: {x}").format(x=missing))
                    if "Role" not in df.columns: df["Role"] = None
                    if "Heritage" not in df.columns: df["Heritage"] = None
                    df = normalize_df(df)
                st.session_state.global_data = df
                st.success(tr("✅ Fichier chargé.", "✅ File loaded."))
                with st.expander(tr("Voir les données chargées", "View loaded data")):
                    st.dataframe(df, use_container_width=True)
            except Exception as e:
                st.error(tr("Erreur de lecture du fichier: {e}", "File read error: {e}").format(e=e))

        st.markdown("---")
        st.subheader(tr("Visualisations", "Visualizations"))
        process_data_display(st.session_state.global_data, key_prefix="excel")

    # ------- Onglet Terminal -------
    with tabs[1]:
         st.markdown(
            tr(
                "Entre une commande puis **Entrée**  \n"
                "----------Version Entité------------ : `AddEnt E1` · `AddEnt E2` · `AddCh E1 E2` · \n"
                "DAC : `AddSub S2` · `AddSub S3` · `S2 AddObj O2`· `S2 Grant S3 O2 R` · \n"
                "MAC: `AddSub S1` · `AddObj O1` · `AddCh S1 R O1`·  \n"
                "China-Wall : `AddSub S1` · `AddObj O1` · `Never {S1, O1}`· `AddCh S1 R O1`·  \n"
                "RBAC: `AddObj O1` · `AddRole R1` · `GrantPermission R1 R O1`· `AddSub S1 R1` · \n",
                "Type a command then **Enter**  \n"
                "Entity version: `AddEnt E1` · `AddEnt E2` · `AddCh E1 E2` · \n"
                "DAC: `AddSub S2` · `AddSub S3` · `S2 AddObj O2` · `S2 Grant S3 O2 R` · \n"
                "MAC: `AddSub S1` · `AddObj O1` · `AddCh S1 R O1` ·  \n"
                "China-Wall: `AddSub S1` · `AddObj O1` · `Never {S1, O1}` · `AddCh S1 R O1` ·  \n"
                "RBAC: `AddObj O1` · `AddRole R1` · `GrantPermission R1 R O1` · `AddSub S1 R1` · \n"
        )
    )
    st.text_input("C:\\>", key="cmd_input",
                  placeholder=tr("Ex: AddSub S1 R1", "Ex: AddSub S1 R1"),
                  on_change=_run_command_callback)
    st.text_area(tr("Historique", "History"),
                 "\n\n".join(st.session_state.history), height=340)

    st.markdown("---")
    st.subheader(tr("Graphes (issus des commandes)", "Graphs (from commands)"))
    process_data_display(st.session_state.global_data, key_prefix="terminal")

if __name__ == "__main__":
    main()
