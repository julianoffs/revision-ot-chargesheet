"""Comparador OT de carguío (PDF) vs Charge Sheet de BlastLogic (PDF).

Uso:  python comparador.py "OT Carguío X.pdf" "ChargeSheet X.pdf" [mas charge sheets...]
      python comparador.py --lote ot_carguio charge_sheets resultados

La OT se lee de forma vectorial (sin OCR): cada pozo es un punto de color con su
etiqueta; el color lo asocia al cuadro de perfil de carga con borde del mismo color;
los polígonos "AUMENTAR TACO x m" suman taco a los pozos que encierran.
"""
import csv
import glob
import math
import os
import re
import statistics
import sys

try:
    import pymupdf as fitz  # PyMuPDF >= 1.24
except ImportError:  # versiones antiguas
    import fitz

TOL_TACO = 0.30   # m
TOL_AIRE = 0.30   # m (taco intermedio de aire)
TOL_KGM = 0.05    # 5 % en densidad lineal (kg/m)
TOL_KG_TOTAL = 0.05   # 5 % en kg totales de explosivo de la malla

HOLE_RE = re.compile(r"^\d{2,4}[A-Z]{0,2}$")


def num(s):
    try:
        return float(str(s).replace(",", "").replace("kg", "").replace("m", "").replace("°", ""))
    except ValueError:
        return None


def norm_prod(s):
    """Normaliza nombre de producto: 'PIREX50 1.30' / 'Pirex 50' -> 'pirex50'."""
    if not s:
        return ""
    t = s.lower().replace("®", "").replace("_", " ")
    if "aire" in t:
        return "aire"
    if "gravilla" in t or "detrito" in t:
        return "gravilla"
    if "densiex" in t:
        return "densiex"
    m = re.search(r"pirex\s*(\d+|s)", t)
    if m:
        return "pirex" + m.group(1)
    m = re.search(r"([a-z]+)\s*(\d+)?", t)
    return (m.group(1) + (m.group(2) or "")) if m else t.strip()


def cdist(a, b):
    return math.sqrt(sum((x - y) ** 2 for x, y in zip(a, b)))


# ---------------------------------------------------------------- Charge Sheet
def parse_charge_sheet(path):
    doc = fitz.open(path)
    holes, order = {}, []
    meta = {"archivo": os.path.basename(path)}
    t0 = doc[0].get_text()
    m = re.search(r"Charge Sheet (\d+)", t0)
    meta["charge_sheet"] = m.group(1) if m else "?"
    m = re.search(r"\b((?:DON|INF)\d+[-‑]\d+[-‑]\d+)", t0)
    meta["malla"] = m.group(1).replace("‑", "-") if m else "?"
    m = re.search(r"Holes in sheet:\s*(\d+)", t0)
    meta["pozos_hoja"] = int(m.group(1)) if m else None
    m = re.search(r"Holes charged:\s*(\d+)", t0)
    meta["pozos_cargados"] = int(m.group(1)) if m else None
    m = re.search(r"Total bulk explosives\s+(\d+)\s+[\d.,]+m\s+([\d,]+)kg", t0)
    meta["kg_total_hoja"] = num(m.group(2)) if m else None
    cur = None
    for pg in doc:
        words = pg.get_text("words")
        hdr = [w for w in words if w[4] == "Hole"]
        if not hdr:
            continue
        sub = [w for w in words if w[4] in ("T.O.P", "Product") and 0 <= w[1] - hdr[0][1] < 30]
        y0 = max([hdr[0][3]] + [w[3] for w in sub]) - 1
        data = sorted((w for w in words if w[1] >= y0), key=lambda w: (w[1], w[0]))
        rows, cur_y = [], None
        for w in data:                       # agrupa palabras en filas por cercanía vertical
            if cur_y is None or w[1] - cur_y > 4:
                rows.append([])
                cur_y = w[1]
            rows[-1].append(w)
        is_m = lambda t: re.fullmatch(r"-?[\d.,]+m", t) is not None
        is_kg = lambda t: re.fullmatch(r"-?[\d.,]+kg", t) is not None
        for ws in rows:
            ws = sorted(ws, key=lambda w: w[0])
            if not (ws[0][0] < 40 and re.fullmatch(r"\d+", ws[0][4])):
                continue
            rest = ws[1:]
            hole = " ".join(w[4] for w in rest if w[0] < 100)
            depth = next((w[4] for w in rest if 100 <= w[0] < 150 and is_m(w[4])), "")
            prod = " ".join(w[4] for w in rest if 150 <= w[0] < 250)
            pmass = next((w[4] for w in rest if 240 <= w[0] and w[2] < 293 and is_kg(w[4])), "")
            ptop = next((w[4] for w in rest if 290 <= w[0] < 338 and is_m(w[4])), "")
            amass = next((w[4] for w in rest if 338 <= w[0] and w[2] < 380 and is_kg(w[4])), "")
            atop = next((w[4] for w in rest if 378 <= w[0] < 413 and is_m(w[4])), "")
            comment = " ".join(w[4] for w in rest if w[0] >= 413)
            if hole:
                cur = {"pozo": hole, "prof": num(depth), "decks": [], "coment": comment}
                holes[hole] = cur
                order.append(hole)
            elif cur is not None and comment:
                cur["coment"] = (cur["coment"] + " " + comment).strip()
            if prod and cur is not None:
                cur["decks"].append({"prod": prod, "masa": num(pmass), "top": num(ptop),
                                     "masa_real": num(amass), "top_real": num(atop)})
    for h in holes.values():
        d = h["decks"]
        h["sin_plan"] = not d
        h["taco"] = h["aire"] = h["kg"] = h["largo_carga"] = None
        h["explosivo"] = ""
        if not d:
            continue
        if any(x["top"] is None for x in d) or h["prof"] is None:
            h["ilegible"] = True
            continue
        tops = [x["top"] for x in d] + [h["prof"]]
        expl = [(i, x) for i, x in enumerate(d) if norm_prod(x["prod"]) not in ("gravilla", "aire")]
        aire = [(i, x) for i, x in enumerate(d) if norm_prod(x["prod"]) == "aire"]
        # taco = largo del primer tramo inerte (hasta el techo del siguiente deck)
        if norm_prod(d[0]["prod"]) == "gravilla" and len(d) > 1:
            h["taco"] = round(tops[1] - tops[0], 2)
        elif norm_prod(d[0]["prod"]) == "gravilla":
            h["taco"] = round((h["prof"] or 0) - (d[0]["top"] or 0), 2)
        else:
            h["taco"] = 0.0
        h["aire"] = round(sum(tops[i + 1] - tops[i] for i, _ in aire), 2) if aire else 0.0
        if expl:
            h["explosivo"] = " + ".join(dict.fromkeys(norm_prod(x["prod"]) for _, x in expl))
            h["kg"] = sum(x["masa"] or 0 for _, x in expl)
            h["largo_carga"] = round(sum(tops[i + 1] - tops[i] for i, _ in expl), 2)
    return meta, holes, order


# ------------------------------------------------------------------------- OT
def _poly_points(g):
    pts = []
    for it in g["items"]:
        if it[0] == "l":
            pts += [it[1], it[2]]
        elif it[0] == "c":
            pts += [it[1], it[4]]
        elif it[0] == "re":
            r = it[1]
            pts += [fitz.Point(r.x0, r.y0), fitz.Point(r.x1, r.y0), fitz.Point(r.x1, r.y1), fitz.Point(r.x0, r.y1)]
        elif it[0] == "qu":
            q = it[1]
            pts += [q.ul, q.ur, q.lr, q.ll]
    out = []
    for p in pts:
        if not out or abs(p.x - out[-1][0]) + abs(p.y - out[-1][1]) > 0.01:
            out.append((p.x, p.y))
    return out


def _inside(pt, poly):
    x, y = pt
    c = False
    n = len(poly)
    for i in range(n):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % n]
        if (y1 > y) != (y2 > y) and x < (x2 - x1) * (y - y1) / (y2 - y1) + x1:
            c = not c
    return c


def _parse_box(pg, rect):
    """Lee un cuadro de perfil de carga -> dict con taco, aire, explosivo, kg..."""
    spans = []
    for b in pg.get_text("dict", clip=rect)["blocks"]:
        for ln in b.get("lines", []):
            for sp in ln["spans"]:
                if sp["text"].strip():
                    spans.append(sp)
    if not spans:
        return None
    med = statistics.median(sp["size"] for sp in spans)
    spans = [sp for sp in spans if sp["size"] >= 0.8 * med]   # descarta el gráfico de barras
    rows = {}
    for sp in spans:
        rows.setdefault(round(sp["bbox"][1] / (med * 0.6)), []).append(sp)
    lines = [" ".join(s["text"].strip() for s in sorted(rows[k], key=lambda s: s["bbox"][0])) for k in sorted(rows)]
    box = {"titulo": "", "largo_pozo": None, "taco": None, "taco_tipo": "", "aire": 0.0,
           "expl_fondo": "", "largo_fondo": None, "kg_fondo": None,
           "expl_inter": "", "largo_inter": None, "kg_inter": None, "n_pozos": None, "texto": lines}
    # encabezado = todo lo que está antes de "Longitud Pozo"
    idx = next((i for i, l in enumerate(lines) if "longitud pozo" in l.lower()), 0)
    head = " ".join(lines[:idx]).strip()
    solos = [l.strip() for l in lines[:idx] if re.fullmatch(r"\d+", l.strip())]
    tit = " ".join(l for l in lines[:idx] if not re.fullmatch(r"\d+", l.strip())).strip()
    m = re.match(r"(.*?)((?:\s+\d+)+)\s*$", tit)
    nums = []
    if m and re.search(r'["”]|Parte|[A-Za-z]\s*$', m.group(1)):
        tit, nums = m.group(1).strip(), m.group(2).split()
    elif re.fullmatch(r"[\d\s]+", tit or " "):
        nums, tit = tit.split(), ""
    box["titulo"] = tit
    if solos:
        box["n_pozos"] = int(solos[-1])
    elif len(nums) >= 2:
        box["n_pozos"] = int(nums[-1])
    sec, pend = "", None

    def put(key, raw):
        if key == "tipo_taco":
            if sec == "taco1":
                box["taco_tipo"] = raw
            elif sec == "taco2":
                box["taco2_tipo"] = raw
        elif key == "tipo_expl":
            if raw and raw != "-" and sec in ("inter", "fondo"):
                box["expl_" + sec] = raw
        else:
            v = num(raw.split()[-1]) if raw else None
            if v is None:
                return False
            if key == "largo_pozo":
                box["largo_pozo"] = v
            elif key == "long_taco":
                if sec == "taco1":
                    box["taco"] = v
                elif sec == "taco2":
                    box["aire"] = v
            elif key == "long_carga" and sec in ("inter", "fondo"):
                box["largo_" + sec] = v
            elif key == "kg" and sec in ("inter", "fondo"):
                box["kg_" + sec] = v
        return True

    keys = [("longitud pozo", "largo_pozo"), ("tipo taco", "tipo_taco"), ("longitud taco", "long_taco"),
            ("tipo explosivo", "tipo_expl"), ("longitud carga", "long_carga"), ("kilogramos explosivo", "kg")]
    for ln in lines[idx:]:
        l = re.sub(r"\s+", " ", ln).strip()
        low = l.lower()
        if "carga explosivo intermedia" in low:
            sec, pend = "inter", None
        elif "carga explosivo fondo" in low:
            sec, pend = "fondo", None
        elif re.match(r"^1\s*(er)?\s*taco", low):
            sec, pend = "taco1", None
        elif re.match(r"^2\s*(do)?\s*taco", low):
            sec, pend = "taco2", None
        else:
            for pref, key in keys:
                if low.startswith(pref):
                    raw = re.sub(r"^.*?(\(m\)|taco|explosivo|pozo)\s*", "", l, count=1, flags=re.I) if key in ("tipo_taco", "tipo_expl") else l[len(pref):]
                    raw = raw.replace("Intermedio", "").replace("(m)", "").strip()
                    if raw in ("", "-") or not put(key, raw):
                        pend = key if raw == "" else None
                    else:
                        pend = None
                    break
            else:
                if pend and re.fullmatch(r"[\d.,]+", l):
                    put(pend, l)
                pend = None
    return box


def parse_ot(path):
    doc = fitz.open(path)
    pg = next((p for p in reversed(list(doc)) if "Longitud Taco" in p.get_text()), None)
    if pg is None:
        raise ValueError("No se encontró la página de carguío (cuadros 'Longitud Taco') en la OT")
    txt = pg.get_text()
    m = re.search(r"\b((?:DON|INF)\d+-\d+-\d+)", txt)
    meta = {"archivo": os.path.basename(path), "malla": m.group(1) if m else "?", "pagina": pg.number + 1, "avisos": []}
    drawings = pg.get_drawings()
    W = pg.rect.width
    todas = pg.get_text("words")

    def _valor(etiqueta):
        """Número a la derecha de una etiqueta de la tabla resumen de la OT."""
        rs = pg.search_for(etiqueta)
        if not rs:
            return None
        r = rs[0]
        yc = (r.y0 + r.y1) / 2
        cand = [w for w in todas if w[0] > r.x1 and w[0] - r.x1 < 0.2 * W
                and abs((w[1] + w[3]) / 2 - yc) < (r.y1 - r.y0) * 0.6 and re.fullmatch(r"[\d.,]+", w[4])]
        return num(min(cand, key=lambda w: w[0])[4]) if cand else None

    meta["resumen"] = {"n_pozos": _valor("Pozos Total"), "kg_explosivo": _valor("Consumo de explosivo"),
                       "gravilla_ton": _valor("Consumo de Gravilla"), "tonelaje": _valor("Tonaleje"),
                       "fc": _valor("FC Global")}
    meta["pagina_wh"] = (pg.rect.width, pg.rect.height)

    # 1) cuadros de perfil: rectángulos grandes de borde grueso y color
    boxes = []
    for g in drawings:
        r = g["rect"]
        if g.get("color") and (g.get("width") or 0) >= 2.0 and r.width > 0.12 * W and r.height > 0.1 * pg.rect.height \
                and not g.get("fill"):
            if any(abs(r.x0 - b["rect"].x0) < 3 and abs(r.y0 - b["rect"].y0) < 3 for b in boxes):
                continue
            if "Longitud Taco" not in pg.get_text(clip=r):
                continue
            info = _parse_box(pg, r)
            if info:
                info["nombre"] = f"{len(boxes) + 1}. {info['titulo'] or 'Cuadro sin título'}"
                boxes.append({"rect": r, "color": tuple(g["color"]), **info})
    # respaldo: cuadros sin borde detectable -> se localizan por el título "Pozos ..."
    if not boxes:
        meta["avisos"].append("No se detectaron bordes de color en los cuadros de perfil; revisar manualmente.")

    # 2) leyenda y polígonos de AUMENTAR TACO
    legend = []
    for g in drawings:
        r = g["rect"]
        if g.get("fill") and r.width > 60 and r.height > 12:
            t = pg.get_text(clip=r).strip()
            mm = re.search(r"AUMENTAR\s+TACO\s+([\d.,]+)", t, re.I)
            if mm and len(t) < 60:
                legend.append({"color": tuple(g["fill"]), "delta": float(mm.group(1).replace(",", ".").rstrip(".")),
                               "rect": r})
    polys, huerf = [], []
    for g in drawings:
        r = g["rect"]
        if g.get("fill") or not g.get("color") or r.width < 25 or r.height < 25 or not legend:
            continue
        col = tuple(g["color"])
        if max(col) - min(col) < 0.3:            # negro / gris / azul oscuro: no es zona de taco
            continue
        if any(abs(r.x0 - b["rect"].x0) < 3 and abs(r.y0 - b["rect"].y0) < 3 for b in boxes):
            continue
        pts = _poly_points(g)
        if len(pts) < 3 or len(g["items"]) < 3 or all(it[0] == "re" for it in g["items"]):
            continue
        lg = min(legend, key=lambda L: cdist(L["color"], col))
        if cdist(lg["color"], col) <= 0.25:
            lg["usada"] = True
            polys.append({"pts": pts, "delta": lg["delta"], "color": col})
        else:
            huerf.append({"pts": pts, "delta": None, "color": col})
    libres = [L for L in legend if not L.get("usada")]
    colores_h = []
    for h_ in huerf:
        if not any(cdist(h_["color"], c) < 0.1 for c in colores_h):
            colores_h.append(h_["color"])
    if huerf and len(libres) == 1 and len(colores_h) == 1:
        for h_ in huerf:
            h_["delta"] = libres[0]["delta"]
            polys.append(h_)
        meta["avisos"].append(f"El color del polígono de aumento no coincide con el de la leyenda; se asumió "
                              f"'AUMENTAR TACO {libres[0]['delta']} m' para el polígono de otro color (verificar).")
        huerf = []
    elif huerf:
        meta["avisos"].append(f"{len(huerf)} polígono(s) de color sin leyenda de aumento de taco coincidente (revisar).")
    for L in legend:
        if not L.get("usada") and not (len(libres) == 1 and len(colores_h) == 1):
            meta["avisos"].append(f"Leyenda 'AUMENTAR TACO {L['delta']} m' sin polígono del mismo color (revisar).")
    meta["zonas_sin_leyenda"] = huerf
    meta["poligonos"] = [{"pts": p["pts"], "delta": p["delta"], "color": p["color"]} for p in polys + huerf]
    for mm in re.finditer(r"(USAR TACO RECOMENDADO|(?<!AUMENTAR )TACO\s+\d+(?:[.,]\d+)?\s*M\b|SIN AJUSTE DE TACO[^\n]*)", txt, re.I):
        meta["avisos"].append("Nota en la OT: '" + mm.group(1).strip() + "' (revisar manualmente)")

    # 3) pozos = puntos pequeños rellenos; etiqueta = texto numérico más cercano
    excl = [b["rect"] for b in boxes] + [L["rect"] for L in legend]
    dots = []
    for g in drawings:
        r = g["rect"]
        if g.get("fill") and 2.5 < r.width < 0.012 * W and abs(r.width - r.height) < 1.5 \
                and any(it[0] == "c" for it in g["items"]):
            c = ((r.x0 + r.x1) / 2, (r.y0 + r.y1) / 2)
            if any(rr.contains(fitz.Point(*c)) for rr in excl):
                continue
            dots.append({"c": c, "color": tuple(g["fill"]), "r": r.width / 2})
    box_colors = [b["color"] for b in boxes]
    # puntos duplicados en la misma posición: conservar el de color más parecido a un cuadro
    uniq = []
    for d in dots:
        d["bd"] = min((cdist(d["color"], bc) for bc in box_colors), default=9)
        for u in uniq:
            if cdist(u["c"], d["c"]) < 1.5:
                if d["bd"] < u["bd"]:
                    u.update(d)
                break
        else:
            uniq.append(d)
    dots = uniq
    labels = []
    for w in pg.get_text("words"):
        if HOLE_RE.match(w[4]):
            c = ((w[0] + w[2]) / 2, (w[1] + w[3]) / 2)
            if any(rr.contains(fitz.Point(*c)) for rr in excl):
                continue
            labels.append({"t": w[4], "c": c, "ll": (w[0], w[3])})
    off = (0.0, 0.0)
    if dots and labels:
        near = []
        for d in dots:
            l = min(labels, key=lambda l: cdist(d["c"], l["c"]))
            if cdist(d["c"], l["c"]) < 0.03 * W:
                near.append((l["c"][0] - d["c"][0], l["c"][1] - d["c"][1]))
        if near:
            off = (statistics.median(n[0] for n in near), statistics.median(n[1] for n in near))
    meta["desfase_etiqueta"] = (round(off[0], 1), round(off[1], 1))
    pairs = sorted(((cdist((d["c"][0] + off[0], d["c"][1] + off[1]), l["c"]), i, j)
                    for i, d in enumerate(dots) for j, l in enumerate(labels)), key=lambda p: p[0])
    maxd = 0.02 * W
    used_d, used_l, holes = set(), set(), {}
    for dist, i, j in pairs:
        if dist > maxd:
            break
        if i in used_d or j in used_l:
            continue
        used_d.add(i)
        used_l.add(j)
        d = dots[i]
        name = labels[j]["t"]
        b = min(boxes, key=lambda b: cdist(b["color"], d["color"])) if boxes else None
        if b and cdist(b["color"], d["color"]) > 0.45:
            b = None
        delta = sum(p["delta"] for p in polys if _inside(d["c"], p["pts"]))
        en_huerf = any(_inside(d["c"], p["pts"]) for p in huerf)
        h = {"pozo": name, "xy": d["c"], "color": d["color"], "grupo": b["nombre"] if b else "(sin cuadro)",
             "aumento": delta, "zona_sin_leyenda": en_huerf, "taco": None, "aire": None, "explosivo": "", "kg": None, "largo_carga": None,
             "largo_pozo": None}
        if b:
            h["taco"] = round((b["taco"] or 0) + delta, 2) if b["taco"] is not None else None
            h["aire"] = b["aire"] or 0.0
            ex = [norm_prod(b[k]) for k in ("expl_inter", "expl_fondo") if b[k]]
            h["explosivo"] = " + ".join(dict.fromkeys(ex))
            h["kg"] = (b["kg_inter"] or 0) + (b["kg_fondo"] or 0)
            h["largo_carga"] = (b["largo_inter"] or 0) + (b["largo_fondo"] or 0)
            h["largo_pozo"] = b["largo_pozo"]
        if name in holes:
            meta["avisos"].append(f"Etiqueta de pozo repetida en la OT: {name}")
        holes[name] = h
    sin = [labels[j]["t"] for j in range(len(labels)) if j not in used_l]
    if len(dots) - len(used_d):
        meta["avisos"].append(f"{len(dots) - len(used_d)} punto(s) de la OT sin etiqueta asociada")
    meta["etiquetas_sin_punto"] = sin
    meta["cuadros"] = boxes
    meta["zonas_aumento"] = [(p["delta"], len([h for h in holes.values() if _inside(h["xy"], p["pts"])])) for p in polys]
    for b in boxes:
        n = sum(1 for h in holes.values() if h["grupo"] == b["nombre"])
        if b["n_pozos"] is not None and n != b["n_pozos"]:
            meta["avisos"].append(f"Cuadro '{b['nombre']}' declara {b['n_pozos']} pozos pero el plano tiene {n} de ese color")
    return meta, holes


# ------------------------------------------------------------------ Comparación
def compare(ot_holes, cs_holes):
    rows = []
    for name in sorted(set(ot_holes) | set(cs_holes), key=lambda s: (len(re.sub(r"\D", "", s)), s)):
        o, c = ot_holes.get(name), cs_holes.get(name)
        r = {"pozo": name, "grupo_OT": o["grupo"] if o else "", "aumento_OT": o["aumento"] if o else "",
             "taco_OT": o["taco"] if o else "", "taco_CS": c["taco"] if c else "",
             "aire_OT": o["aire"] if o else "", "aire_CS": c["aire"] if c else "",
             "explosivo_OT": o["explosivo"] if o else "", "explosivo_CS": c["explosivo"] if c else "",
             "kg_OT_nominal": o["kg"] if o else "", "kg_CS": c["kg"] if c else "",
             "prof_CS": c["prof"] if c else "", "estado": "OK", "detalle": ""}
        prob = []
        if o is None:
            r["estado"] = "SOLO EN CHARGE SHEET"
        elif c is None:
            r["estado"] = "SOLO EN OT"
        elif c["sin_plan"]:
            r["estado"] = "SIN PLAN EN CS"
            r["detalle"] = c["coment"]
        elif c.get("ilegible"):
            r["estado"] = "REVISAR"
            r["detalle"] = "fila de la charge sheet no legible"
        elif not c["explosivo"]:
            r["estado"] = "CS SIN EXPLOSIVO"
            r["detalle"] = "en la charge sheet el pozo solo tiene " + ", ".join(x["prod"] for x in c["decks"]) + \
                           f" (OT: {o['explosivo']}, taco {o['taco']})"
        elif o["taco"] is None or c["taco"] is None:
            r["estado"] = "REVISAR"
            r["detalle"] = "no se pudo leer el taco en " + ("la OT" if o["taco"] is None else "la charge sheet")
        else:
            if round(abs(o["taco"] - c["taco"]), 2) > TOL_TACO:
                prob.append(f"taco OT {o['taco']} vs CS {c['taco']}")
            if round(abs((o["aire"] or 0) - (c["aire"] or 0)), 2) > TOL_AIRE:
                prob.append(f"aire OT {o['aire']} vs CS {c['aire']}")
            if o["explosivo"] != c["explosivo"]:
                prob.append(f"explosivo OT {o['explosivo']} vs CS {c['explosivo']}")
            elif o["largo_carga"] and c["largo_carga"] and o["kg"] and c["kg"]:
                ko, kc = o["kg"] / o["largo_carga"], c["kg"] / c["largo_carga"]
                r["kgm_OT"], r["kgm_CS"] = round(ko, 1), round(kc, 1)
                if abs(ko - kc) / ko > TOL_KGM:
                    prob.append(f"kg/m OT {ko:.1f} vs CS {kc:.1f}")
            if prob:
                r["estado"] = "DIFERENCIA"
                r["detalle"] = "; ".join(prob)
                if o.get("zona_sin_leyenda"):
                    r["detalle"] += " (pozo dentro de un polígono de color sin leyenda)"
        rows.append(r)
    return rows


COLS = ["pozo", "estado", "detalle", "grupo_OT", "aumento_OT", "taco_OT", "taco_CS", "aire_OT", "aire_CS",
        "explosivo_OT", "explosivo_CS", "kg_OT_nominal", "kg_CS", "kgm_OT", "kgm_CS", "prof_CS"]


def run_pair(ot_path, cs_paths, out_csv=None):
    ot_meta, ot_holes = parse_ot(ot_path)
    cs_holes, cs_metas = {}, []
    for p in cs_paths:
        m, h, _ = parse_charge_sheet(p)
        cs_metas.append(m)
        for k, v in h.items():      # si un pozo está en 2 hojas, gana la que tiene plan
            if k not in cs_holes or cs_holes[k]["sin_plan"]:
                cs_holes[k] = v
    rows = compare(ot_holes, cs_holes)
    if out_csv:
        with open(out_csv, "w", newline="", encoding="utf-8-sig") as f:
            w = csv.DictWriter(f, fieldnames=COLS, extrasaction="ignore", delimiter=";")
            w.writeheader()
            w.writerows(rows)
    cnt = {}
    for r in rows:
        cnt[r["estado"]] = cnt.get(r["estado"], 0) + 1
    res = ot_meta.get("resumen", {})
    kg_cs = round(sum(h["kg"] or 0 for h in cs_holes.values()))
    tot = {"pozos_OT_tabla": int(res["n_pozos"]) if res.get("n_pozos") is not None else None,
           "pozos_OT_plano": len(ot_holes), "pozos_CS": len(cs_holes),
           "pozos_CS_con_plan": sum(1 for h in cs_holes.values() if not h["sin_plan"]),
           "kg_OT": res.get("kg_explosivo"), "kg_CS": kg_cs,
           "kg_CS_hojas": [m_["kg_total_hoja"] for m_ in cs_metas], "dif_kg_pct": None,
           "ok_pozos": None, "ok_kg": None, "tol_kg_pct": TOL_KG_TOTAL * 100}
    if tot["pozos_OT_tabla"] is not None:
        tot["ok_pozos"] = tot["pozos_OT_tabla"] == tot["pozos_CS"]
        if not tot["ok_pozos"]:
            ot_meta["avisos"].insert(0, f"DESVIACIÓN: la tabla de la OT indica {tot['pozos_OT_tabla']} pozos y la "
                                        f"charge sheet tiene {tot['pozos_CS']}.")
        if tot["pozos_OT_plano"] != tot["pozos_OT_tabla"]:
            ot_meta["avisos"].append(f"En el plano de la OT se identificaron {tot['pozos_OT_plano']} pozos con etiqueta, "
                                     f"pero su tabla indica {tot['pozos_OT_tabla']}.")
    else:
        ot_meta["avisos"].append("No se pudo leer 'N° Pozos Total' en la tabla de la OT.")
    if tot["kg_OT"]:
        tot["dif_kg_pct"] = round((kg_cs - tot["kg_OT"]) / tot["kg_OT"] * 100, 1)
        tot["ok_kg"] = abs(tot["dif_kg_pct"]) <= TOL_KG_TOTAL * 100
        if not tot["ok_kg"]:
            ot_meta["avisos"].insert(0, f"DESVIACIÓN: la OT indica {tot['kg_OT']:,.0f} kg de explosivo y la charge sheet "
                                        f"planifica {kg_cs:,.0f} kg ({tot['dif_kg_pct']:+.1f} %).".replace(",", "."))
    else:
        ot_meta["avisos"].append("No se pudo leer 'Consumo de explosivo (kg)' en la tabla de la OT.")
    ot_meta["totales"] = tot
    ot_meta["_ot_holes"] = ot_holes
    return ot_meta, cs_metas, rows, cnt


def run_json(ot_path, cs_paths):
    """Entrada para la página web: devuelve el resultado completo como texto JSON."""
    import json
    om, cm, rows, cnt = run_pair(ot_path, cs_paths)
    avisos = list(om["avisos"])
    for c in cm:
        if c["malla"] != om["malla"]:
            avisos.insert(0, f"ATENCIÓN: la OT es de la malla {om['malla']} pero la charge sheet "
                             f"{c['charge_sheet']} es de {c['malla']}.")
    cuadros = [{"nombre": b["nombre"], "n_pozos": b["n_pozos"], "largo_pozo": b["largo_pozo"], "taco": b["taco"],
                "aire": b["aire"], "explosivo": " + ".join(x for x in (b["expl_inter"], b["expl_fondo"]) if x),
                "kg": (b["kg_inter"] or 0) + (b["kg_fondo"] or 0),
                "color": "#%02x%02x%02x" % tuple(int(round(v * 255)) for v in b["color"][:3])}
               for b in om["cuadros"]]
    hexc = lambda col: "#%02x%02x%02x" % tuple(int(round(v * 255)) for v in col[:3])
    plano = {"w": om["pagina_wh"][0], "h": om["pagina_wh"][1],
             "pozos": [{"pozo": h["pozo"], "x": round(h["xy"][0], 1), "y": round(h["xy"][1], 1), "color": hexc(h["color"])}
                       for h in om["_ot_holes"].values()],
             "zonas": [{"pts": [[round(x, 1), round(y, 1)] for x, y in z["pts"]], "delta": z["delta"],
                        "color": hexc(z["color"])} for z in om["poligonos"]]}
    return json.dumps({"totales": om["totales"], "plano": plano,
                       "tolerancias": {"taco": TOL_TACO, "aire": TOL_AIRE, "kgm_pct": TOL_KGM * 100,
                                       "kg_total_pct": TOL_KG_TOTAL * 100},
                       "malla": om["malla"], "pagina_ot": om["pagina"],
                       "charge_sheets": [c["charge_sheet"] for c in cm], "cuadros": cuadros,
                       "zonas_aumento": om["zonas_aumento"], "avisos": avisos, "conteo": cnt,
                       "columnas": COLS, "filas": rows}, ensure_ascii=False)


def main(argv):
    sys.stdout.reconfigure(encoding="utf-8")
    if argv and argv[0] == "--lote":
        ot_dir, cs_dir, out_dir = argv[1:4]
        os.makedirs(out_dir, exist_ok=True)
        for ot in sorted(glob.glob(os.path.join(ot_dir, "*.pdf"))):
            m = re.search(r"(\d{4}-\d{3})", os.path.basename(ot))
            cs = sorted(glob.glob(os.path.join(cs_dir, f"*{m.group(1)}_ChargeSheet_*.pdf"))) if m else []
            if not cs:
                print(f"{os.path.basename(ot)}: sin charge sheet")
                continue
            try:
                om, cm, rows, cnt = run_pair(ot, cs, os.path.join(out_dir, f"comparacion_{m.group(1)}.csv"))
            except Exception as e:  # noqa
                print(f"{os.path.basename(ot)}: ERROR {e}")
                continue
            print(f"\n=== {om['malla']}  (OT pág. {om['pagina']}, CS {', '.join(c['charge_sheet'] for c in cm)})")
            print("   cuadros:", [(b["nombre"], b["n_pozos"], b["taco"], b["aire"], b["expl_fondo"], b["kg_fondo"]) for b in om["cuadros"]])
            print("   zonas aumento (delta, pozos):", om["zonas_aumento"])
            print("   resultado:", cnt)
            t_ = om["totales"]
            print(f"   totales: pozos OT {t_['pozos_OT_tabla']} / CS {t_['pozos_CS']} -> {'OK' if t_['ok_pozos'] else 'DESVIACION'};"
                  f" kg OT {t_['kg_OT']} / CS {t_['kg_CS']} ({t_['dif_kg_pct']} %) -> {'OK' if t_['ok_kg'] else 'DESVIACION'}")
            for a in om["avisos"]:
                print("   aviso:", a)
            for r in rows:
                if r["estado"] != "OK":
                    print(f"     {r['pozo']:>6} {r['estado']}: {r['detalle']}")
        return
    ot, cs = argv[0], argv[1:]
    om, cm, rows, cnt = run_pair(ot, cs, "comparacion.csv")
    print(om["malla"], cnt)
    for a in om["avisos"]:
        print("aviso:", a)
    for r in rows:
        if r["estado"] != "OK":
            print(f"{r['pozo']:>6} {r['estado']}: {r['detalle']}")


if __name__ == "__main__":
    main(sys.argv[1:])
