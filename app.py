"""Tactical Pathfinder SSS+++ — Python 3.11+, streamlit run app.py.
All application logic is in this file. Online planning; GPX is usable offline.
No service credentials, fabricated routes, or simulated audit results.
"""
from __future__ import annotations

import hashlib
import html
import io
import json
import math
import re
from datetime import datetime, timezone
from urllib.parse import urlparse

import folium
import gpxpy
import gpxpy.gpx
import requests
import streamlit as st
from PIL import Image
from pyproj import CRS, Geod, Transformer
from pyproj.aoi import AreaOfInterest
from pyproj.transformer import TransformerGroup
from shapely import make_valid
from shapely.geometry import LineString, Point, Polygon, mapping
from shapely.ops import nearest_points, polygonize, substring, transform, unary_union
from streamlit_folium import st_folium
from folium.plugins import Fullscreen, LocateControl
from branca.element import MacroElement
from jinja2 import Template

APP = "Tactical Pathfinder SSS+++"
GEOD = Geod(ellps="WGS84")
HEADERS = {"User-Agent": "TacticalPathfinder/1.0 (personal walking route planner)"}
OVERPASS = ("https://overpass-api.de/api/interpreter",
            "https://overpass.kumi.systems/api/interpreter")
LOOKUPS = "https://raw.githubusercontent.com/abrensch/brouter/master/misc/profiles2/lookups.dat"
WATER_TITLE = "⚠️ ПРОВЕРИТЬ МОСТ / БОБРОВЫЙ РАЗЛИВ"
WET_TITLE = "⚠️ РИСК ЗАВАЛА / ТОПЬ"
DISCLAIMER = ("OSM-аудит не подтверждает физическую проходимость, прочность моста, "
              "отсутствие разлива, лед, право доступа или актуальность дороги. "
              "Птичка — только ориентир, не рекомендация идти напрямик.")


def https_url(value: str) -> str:
    """Public HTTPS only: restrict user-supplied endpoints to reduce SSRF risk."""
    value = value.strip().rstrip("/")
    u = urlparse(value)
    if u.scheme != "https" or not u.hostname or u.username or u.password:
        raise ValueError("Нужен публичный HTTPS-адрес без логина и пароля.")
    import ipaddress
    if u.hostname.lower() == "localhost" or u.hostname.lower().endswith((".local", ".internal")):
        raise ValueError("Локальные адреса запрещены.")
    try:
        ip = ipaddress.ip_address(u.hostname)
    except ValueError:
        ip = None
    if ip is not None and not ip.is_global:
        raise ValueError("Нужен публичный адрес.")
    return value


def http_json(url, *, params=None, data=None, timeout=90, headers=None):
    h = dict(HEADERS)
    h.update(headers or {})
    # Redirects disabled: an endpoint must not silently send route coordinates elsewhere.
    r = requests.request("POST" if data is not None else "GET", url,
                         params=params, data=data, headers=h,
                         timeout=(8, timeout), allow_redirects=False)
    if 300 <= r.status_code < 400:
        raise ValueError("Сервис перенаправляет запрос. Укажите его конечный HTTPS-адрес.")
    if not r.ok:
        raise ValueError(f"HTTP {r.status_code}: {r.text[:240]}")
    try:
        result = r.json()
    except ValueError as exc:
        raise ValueError(f"Сервис вернул не JSON: {r.text[:240]}") from exc
    if isinstance(result, dict) and result.get("error"):
        raise ValueError(str(result["error"])[:500])
    return result


@st.cache_resource(show_spinner=False)
def sk_transformers(zone):
    if zone not in (5, 6):
        raise ValueError("Для этого приложения выберите зону 5 или 6.")
    crs = CRS.from_epsg(28400 + zone)
    group = TransformerGroup(crs, CRS.from_epsg(4326), always_xy=True,
                             area_of_interest=AreaOfInterest(23.0, 51.0, 33.0, 56.5),
                             allow_ballpark=False)
    if not group.transformers:
        raise ValueError("Нет доступного преобразования СК-42 → WGS-84 без ballpark.")
    tx = group.transformers[0]
    # Inverse of the SAME selected operation, not an independently selected datum shift.
    return tx


def sk_to_wgs(x, y, zone):
    if not (4_000_000 < x < 7_000_000):
        raise ValueError("X — северное смещение в метрах, обычно семизначное.")
    prefix = int(y // 1_000_000)
    if prefix != zone:
        raise ValueError(f"Y должен содержать миллионный префикс зоны {zone}; получен {prefix}.")
    tx = sk_transformers(zone)
    lon, lat = tx.transform(y, x, errcheck=True)  # EPSG: easting, northing!
    validate_point(lat, lon)
    return lat, lon, tx.accuracy, tx.description


def wgs_to_sk(lat, lon, zone):
    from pyproj.enums import TransformDirection
    y, x = sk_transformers(zone).transform(lon, lat,
                direction=TransformDirection.INVERSE, errcheck=True)
    return x, y


def validate_point(lat, lon):
    if not (math.isfinite(lat) and math.isfinite(lon) and -85 < lat < 85 and -180 <= lon <= 180):
        raise ValueError("Недопустимые координаты Lat, Lon.")
    # Algorithms and selected datum transforms are intentionally region-limited.
    if not (50 <= lat <= 58 and 21 <= lon <= 35):
        raise ValueError("Приложение настроено на Беларусь и приграничье: 50–58°N, 21–35°E.")


def local_projection(coords):
    lon = sum(c[0] for c in coords) / len(coords)
    lat = sum(c[1] for c in coords) / len(coords)
    crs = CRS.from_proj4(f"+proj=aeqd +lat_0={lat} +lon_0={lon} +datum=WGS84 +units=m")
    fwd = Transformer.from_crs(4326, crs, always_xy=True).transform
    inv = Transformer.from_crs(crs, 4326, always_xy=True).transform
    return fwd, inv


def geodesic_length(coords):
    return sum(GEOD.inv(a[0], a[1], b[0], b[1])[2]
               for a, b in zip(coords, coords[1:]))


def chainages(coords):
    out = [0.0]
    for a, b in zip(coords, coords[1:]):
        out.append(out[-1] + GEOD.inv(a[0], a[1], b[0], b[1])[2])
    return out


def geodesic_at(coords, distances, metres):
    import bisect
    i = max(0, min(len(coords) - 2, bisect.bisect_right(distances, metres) - 1))
    a, b = coords[i:i+2]
    az, _, d = GEOD.inv(a[0], a[1], b[0], b[1])
    lon, lat, _ = GEOD.fwd(a[0], a[1], az, min(d, max(0, metres - distances[i])))
    return lon, lat


def parse_lookup(text):
    out, context = {"way": {}, "node": {}}, None
    for line in text.splitlines():
        if line.startswith("---context:"):
            context = line.split(":", 1)[1].strip()
        elif context in out and ";" in line and not line.startswith("#"):
            key, rhs = line.split(";", 1)
            fields = rhs.split()
            if len(fields) >= 2:
                # Only primary values compile; aliases are not lookup matches.
                out[context].setdefault(key, set()).add(fields[1])
    return out


@st.cache_data(ttl=21600, show_spinner=False)
def lookup_metadata(url):
    r = requests.get(https_url(url), headers=HEADERS, timeout=(8, 20), allow_redirects=False)
    r.raise_for_status()
    data = parse_lookup(r.text)
    if "highway" not in data["way"]:
        raise ValueError("Ответ не содержит таблицу lookup BRouter.")
    return data


def make_profile(meta=None):
    """Standalone pedestrian cost model inspired by trekking/gravel priorities.
    Not a copied cycling profile: bicycle oneway restrictions must not apply.
    Polygon-only tags cannot be made visible by simply mentioning them here.
    """
    notes = []
    way_extra, node_extra = [], []
    if meta:
        for key, values in (("natural", ["wetland"]), ("wetland", ["bog", "marsh", "swamp", "fen"]),
                            ("surface", ["peat"])):
            accepted = [v for v in values if v in meta["way"].get(key, set())]
            if accepted:
                way_extra.append(f" else if {key}={'|'.join(accepted)} then 9999")
            else:
                notes.append(f"Нет {key}={'|'.join(values)} в lookup: проверка через Overpass.")
        if "ford" in meta["node"]:
            vals = [v for v in ("yes", "stepping_stones") if v in meta["node"]["ford"]]
            if vals:
                node_extra.append(f" if ford={'|'.join(vals)} then 1000000")
    else:
        notes.append("Lookup сервера не получен: используется совместимое ядро профиля; болота и торф — Overpass.")
    # Known standard lookup keys used by the public BRouter pedestrian profiles.
    script = """# Tactical Pathfinder — anti-mud pedestrian profile
---context:global
assign validForFoot = true
assign validForBikes = false
assign validForCars = false
assign considerTurnRestrictions = false
assign turnInstructionMode = 0
assign processUnusedTags = true
assign uphillcost = 60
assign uphillcutoff = 1.5
assign downhillcost = 30
assign downhillcutoff = 1.5
---context:way
assign defaultaccess = if access= then true else access=yes|permissive|designated
assign footaccess = if foot= then defaultaccess else foot=yes|designated|permissive
assign nodeaccessgranted = foot=yes|designated|permissive
assign turncost = 0
assign initialcost = 0
assign costfactor =
 if not footaccess then 10000
 else if highway=motorway|motorway_link|trunk|trunk_link|construction|proposed|abandoned then 10000
 else if highway= then 10000
 else if motorroad=yes then 10000
 else if route=ferry then 10000
 else if ford=yes|stepping_stones then 9999
 else if surface=mud then 9999
 else if tracktype=grade4|grade5 then 9999
 else if smoothness=impassable then 9999
{EXTRA}
 else if highway=track then
   if tracktype=grade1 then 1.0
   else if tracktype=grade2 then 1.05
   else if tracktype=grade3 then 1.25
   else 2.0
 else if highway=path|footway|bridleway then
   if surface=asphalt|paved|compacted|fine_gravel then 1.15 else 1.6
 else if highway=unclassified|service|residential|living_street then 1.2
 else if highway=tertiary|tertiary_link then 1.8
 else if highway=secondary|secondary_link then 3.0
 else if highway=primary|primary_link then 5.0
 else if highway=steps then 4.0
 else 2.0
---context:node
assign defaultaccess = if access= then true else access=yes|permissive|designated
assign footaccess = if foot= then defaultaccess else foot=yes|designated|permissive
assign initialcost =
{NODE_EXTRA}
 if footaccess then 0 else 1000000
"""
    return script.replace("{EXTRA}", "\n".join(way_extra)).replace("{NODE_EXTRA}", "\n".join(node_extra) + "\n else" if node_extra else ""), notes


@st.cache_data(ttl=600, show_spinner=False)
def upload_profile(base, profile):
    result = http_json(https_url(base) + "/profile", data=profile.encode("utf-8"),
                       headers={"Content-Type": "text/plain; charset=utf-8"}, timeout=40)
    pid = result.get("profileid", "")
    if not re.fullmatch(r"custom_[A-Za-z0-9_-]+", pid):
        raise ValueError(f"Не получен ID загруженного профиля: {str(result)[:240]}")
    return pid


@st.cache_data(ttl=600, show_spinner=False)
def route_request(base, pid, points, nogos, alt):
    params = {"lonlats": "|".join(f"{p[1]:.7f},{p[0]:.7f}" for p in points),
              "profile": pid, "alternativeidx": str(alt), "format": "geojson"}
    if nogos:
        params["nogos"] = "|".join(f"{lon:.7f},{lat:.7f},150" for lon, lat in nogos)
    data = http_json(https_url(base), params=params, timeout=120)
    for feature in data.get("features", []):
        if feature.get("geometry", {}).get("type") == "LineString":
            coords = feature["geometry"]["coordinates"]
            if len(coords) < 2:
                break
            for c in coords:
                validate_point(float(c[1]), float(c[0]))
            if geodesic_length(coords) > 180_000:
                raise ValueError("Маршрут длиннее 180 км: сократите запрос.")
            props = feature.get("properties", {})
            if nogos:
                fwd, _ = local_projection(coords)
                line = transform(fwd, LineString([c[:2] for c in coords]))
                if any(line.distance(transform(fwd, Point(n))) < 145 for n in nogos):
                    raise ValueError("Ответ BRouter нарушает no-go. Такой обход не принят.")
            return {"coords": coords, "properties": props, "alternative": alt,
                    "signature": hashlib.sha256(json.dumps(coords).encode()).hexdigest(),
                    "created": datetime.now(timezone.utc).isoformat()}
    raise ValueError("BRouter не вернул линию маршрута; нельзя подменять её птичкой.")


def build_routes(base, profile, points, nogos):
    pid = upload_profile(base, profile)
    routes, errors = [], []
    for alt in range(3):
        try:
            route = route_request(base, pid, tuple(points), tuple(nogos), alt)
            if any(r["signature"] == route["signature"] for r in routes):
                errors.append(f"Вариант {alt}: совпадает с уже полученным, не показан повторно.")
            else:
                routes.append(route)
        except (requests.RequestException, ValueError, KeyError, TypeError) as exc:
            errors.append(f"Вариант {alt}: {exc}")
    if not routes:
        raise ValueError("Не построено ни одного варианта. " + " | ".join(errors))
    # Select the fastest returned corridor under our explicit walking model.
    routes.sort(key=lambda r: sum(d / 1000 / v for d, v, _, _ in route_segments(r)[0]))
    return routes, errors


def corridor_query(coords):
    fwd, inv = local_projection(coords)
    line = transform(fwd, LineString([c[:2] for c in coords])).simplify(4)
    ll = list(transform(inv, line).coords)
    path = ",".join(f"{lat:.6f},{lon:.6f}" for lon, lat in ll)
    # +15m accommodates simplification and geometry errors; exact 30m filter is local.
    around = f"(around:45,{path})"
    sampled = [line.interpolate(d) for d in range(0, int(line.length) + 1, 250)]
    sampled.append(line.interpolate(line.length))
    area_lines, refs = [], []
    for i, p in enumerate(sampled):
        lon, lat = inv(p.x, p.y)
        area_lines.append(f"is_in({lat:.6f},{lon:.6f})->.p{i};")
        refs.append(f'area.p{i}["natural"="wetland"];')
    return ('[out:json][timeout:40][maxsize:67108864];\n' + "\n".join(area_lines)
            + "\n(" + "".join(refs) + ")->.wetareas;\n("
            + f'way["waterway"~"^(river|stream|canal|drain|ditch)$"]{around};'
            + f'way["highway"]{around};'
            + f'nwr["ford"]{around};'
            + f'nwr["natural"="wetland"]{around};'
            + f'way["surface"~"^(mud|peat)$"]{around};'
            + 'way(pivot.wetareas);rel(pivot.wetareas););out body geom;')


@st.cache_data(ttl=1800, show_spinner=False)
def overpass_chunk(query, primary):
    endpoints = list(dict.fromkeys([https_url(primary)] + list(OVERPASS)))
    errors = []
    for endpoint in endpoints:
        try:
            result = http_json(endpoint, data={"data": query}, timeout=55)
            if result.get("remark"):
                raise ValueError("Неполный ответ Overpass: " + result["remark"][:220])
            if not isinstance(result.get("elements"), list):
                raise ValueError("Нет списка elements.")
            return result["elements"], endpoint
        except (requests.RequestException, ValueError) as exc:
            errors.append(f"{urlparse(endpoint).hostname}: {exc}")
    raise ValueError(" | ".join(errors))


def collect_osm(coords, primary, progress=None):
    fwd, inv = local_projection(coords)
    line = transform(fwd, LineString([c[:2] for c in coords]))
    n = max(1, math.ceil(line.length / 8000))
    elements, errors, sources = {}, [], set()
    for i in range(n):
        segment = substring(line, max(0, i * 8000 - 60), min(line.length, (i + 1) * 8000 + 60))
        try:
            chunk, source = overpass_chunk(corridor_query(list(transform(inv, segment).coords)), primary)
            sources.add(source)
            for e in chunk:
                elements[(e["type"], e["id"])] = e
        except (requests.RequestException, ValueError) as exc:
            errors.append(f"Коридор {i+1}/{n}: {exc}")
        if progress:
            progress((i + 1) / n, text=f"OSM-аудит: коридор {i+1}/{n}")
    return list(elements.values()), errors, sorted(sources)


def element_geometry(e):
    def as_line(points):
        ll = [(v["lon"], v["lat"]) for v in points if "lon" in v and "lat" in v]
        return LineString(ll) if len(ll) > 1 else None
    if e["type"] == "node":
        return Point(e["lon"], e["lat"]) if "lat" in e else None
    if e["type"] == "way":
        pts = e.get("geometry", [])
        line = as_line(pts)
        if line is not None and e.get("tags", {}).get("natural") == "wetland" and line.is_ring:
            return make_valid(Polygon(line.coords))
        return line
    if e["type"] == "relation":
        outers, inners = [], []
        for member in e.get("members", []):
            line = as_line(member.get("geometry", []))
            if line is not None:
                (inners if member.get("role") == "inner" else outers).append(line)
        if not outers:
            return None
        polys = list(polygonize(unary_union(outers)))
        holes = list(polygonize(unary_union(inners))) if inners else []
        if polys:
            area = unary_union(polys)
            return make_valid(area.difference(unary_union(holes))) if holes else make_valid(area)
        return unary_union(outers)
    return None


def point_parts(geometry):
    if geometry.is_empty:
        return []
    if geometry.geom_type == "Point":
        return [geometry]
    if geometry.geom_type in ("LineString", "LinearRing"):
        return [geometry.interpolate(0.5, normalized=True)]
    if hasattr(geometry, "geoms"):
        return [p for child in geometry.geoms for p in point_parts(child)]
    return [geometry.representative_point()]


def analyse_osm(coords, elements):
    fwd, inv = local_projection(coords)
    route = transform(fwd, LineString([c[:2] for c in coords]))
    corridor = route.buffer(30)
    features, warnings, geometry_errors = [], [], []
    for e in elements:
        try:
            g = element_geometry(e)
            if g is not None and not g.is_empty:
                g = transform(fwd, g)
                if g.intersects(corridor):
                    features.append((e, g))
        except (ValueError, TypeError, KeyError) as exc:
            geometry_errors.append(f"OSM {e.get('type')}/{e.get('id')}: {exc}")
    bridges = []
    for e, g in features:
        t = e.get("tags", {})
        if t.get("highway") and t.get("bridge", "no") not in ("", "no", "false", "0"):
            # A bridge on a nearby parallel road must not validate this route.
            if g.length > 0 and route.intersection(g.buffer(4)).length >= min(12, g.length * .7):
                bridges.append(g)

    def add(p, title, kind, e, detail, avoid=False):
        along = route.project(p)
        q = route.interpolate(along)
        if any(w["kind"] == kind and abs(w["metres"] - along) < 25 for w in warnings):
            return
        lon, lat = inv(q.x, q.y)
        warnings.append({"lat": lat, "lon": lon, "name": title, "kind": kind,
                         "metres": along, "detail": detail,
                         "osm": f"https://www.openstreetmap.org/{e['type']}/{e['id']}",
                         "avoid": avoid})

    for e, g in features:
        tags = e.get("tags", {})
        water = tags.get("waterway") in ("river", "stream", "canal", "drain", "ditch")
        if water:
            cross = route.intersection(g)
            near = cross.is_empty and route.distance(g) <= 3
            points = [nearest_points(route, g)[0]] if near else point_parts(cross)
            for p in points:
                bridge = any(b.distance(p) <= 5 for b in bridges)
                culvert = tags.get("tunnel") == "culvert"
                if bridge or culvert:
                    add(p, "ℹ️ ПЕРЕХОД ПО OSM — ПРОВЕРИТЬ НА МЕСТЕ", "mapped_crossing", e,
                        "Есть дорожная геометрия bridge рядом с пересечением." if bridge
                        else "Водоток отмечен tunnel=culvert; состояние трубы неизвестно.")
                else:
                    add(p, WATER_TITLE, "water", e,
                        f"waterway={tags['waterway']}; мост на совпадающем участке дороги не найден. "
                        + ("Сближение ≤3 м, пересечение не подтверждено." if near else "Пересечение геометрий OSM."),
                        avoid=True)
        if tags.get("ford") not in (None, "no", "false", "0"):
            if g.distance(route) <= 8:
                add(nearest_points(route, g)[0], WATER_TITLE, "ford", e,
                    "OSM: брод/переход по камням. С грузом не считается безопасным.", True)
        bad = (tags.get("natural") == "wetland" or tags.get("surface") in ("mud", "peat")
               or tags.get("tracktype") in ("grade4", "grade5"))
        if bad:
            # Mark each contiguous corridor contact, not merely the object's centroid.
            contact = route.intersection(g.buffer(30))
            for p in point_parts(contact):
                add(p, WET_TITLE, "terrain", e, "; ".join(f"{k}={tags[k]}" for k in
                    ("natural", "wetland", "surface", "tracktype") if k in tags))
    return sorted(warnings, key=lambda w: w["metres"]), geometry_errors


def audit_route(route, primary, progress=None):
    elements, errors, sources = collect_osm(route["coords"], primary, progress)
    warnings, geometry_errors = analyse_osm(route["coords"], elements)
    errors += geometry_errors
    return {"warnings": warnings, "errors": errors, "complete": not errors,
            "sources": sources, "count": len(elements), "features": osm_features(elements),
            "at": datetime.now(timezone.utc).isoformat()}


def tag_pairs(text):
    return dict(re.findall(r"([\w:]+)=([^\s]+)", str(text)))


def segment_class(tags):
    if tags.get("tracktype") in ("grade1", "grade2"):
        return 6.2, 1.1, "Дороги grade1–2"
    if tags.get("tracktype") == "grade3":
        return 5.2, 1.2, "Дороги grade3"
    if tags.get("surface") in ("mud", "peat") or tags.get("tracktype") in ("grade4", "grade5"):
        return 2.0, 1.8, "Тяжёлое покрытие"
    if tags.get("highway") in ("path", "footway", "bridleway", "steps"):
        return 4.5, 1.2, "Тропы"
    if tags.get("highway") in ("residential", "unclassified", "service", "tertiary", "secondary", "primary", "cycleway", "pedestrian", "living_street"):
        return 6.2, 1.0, "Дороги"
    return 3.0, 1.5, "Покрытие неизвестно"


def route_segments(route):
    total = geodesic_length(route["coords"])
    messages = route.get("properties", {}).get("messages", [])
    result = []
    if messages:
        headers = [str(h).lower().replace(" ", "").replace("-", "") for h in messages[0]]
        def find(*names):
            return next((headers.index(n) for n in names if n in headers), None)
        li, ti = find("length", "distance"), find("waytags")
        if li is not None and ti is not None:
            for row in messages[1:]:
                try:
                    length = float(row[li])
                    tags = tag_pairs(row[ti])
                    if length > 0 and math.isfinite(length):
                        result.append((length, *segment_class(tags)))
                except (ValueError, TypeError, IndexError):
                    continue
    # Messages may use slightly different distance rounding; never invent full coverage.
    coverage = min(1.0, sum(s[0] for s in result if s[3] != "Покрытие неизвестно") / total) if total else 0.0
    classified = sum(s[0] for s in result)
    if classified > total and classified > 0:
        result = [(d * total / classified, v, eta, label) for d, v, eta, label in result]
    elif classified < total:
        result.append((total - classified, 3.0, 1.5, "Покрытие неизвестно"))
    return result, coverage


def pandolf_watts(body, load, speed_kmh, eta, grade):
    v = speed_kmh / 3.6
    # Original equation is not reliable for steep/downhill or very long marches.
    # Conservative scenario: no energy credit for descents.
    g = max(0.0, grade)
    return 1.5 * body + 2.0 * (body + load) * (load / body)**2 + eta * (body + load) * (1.5 * v*v + .35 * v * g)


def estimate(segments, body, load, grade, pause_ratio, water_rate, reserve):
    hours, kcal, distance = 0.0, 0.0, 0.0
    for metres, speed, eta, _ in segments:
        h = metres / 1000 / speed
        hours += h
        kcal += pandolf_watts(body, load, speed, eta, grade) * h * 3600 / 4184
        distance += metres
    elapsed = hours * (1 + pause_ratio)
    # Resting component is not zero; approximate rest with same standing-load term.
    kcal += pandolf_watts(body, load, 0, 1, 0) * (elapsed-hours) * 3600 / 4184
    return {"Длина, км": round(distance/1000, 2), "Ходовое, ч": round(hours, 1),
            "С привалами, ч": round(elapsed, 1), "Pandolf, ккал": round(kcal),
            "Вода, л (план)": round(elapsed * water_rate * (1 + reserve), 1)}


def tile_position(lon, lat, z=14):
    n = 2**z
    lat = max(-85.05112878, min(85.05112878, lat))
    x = (lon + 180) / 360 * n
    y = (1 - math.asinh(math.tan(math.radians(lat))) / math.pi) / 2 * n
    return int(x), int(y), (x % 1) * 256, (y % 1) * 256


def check_template(template):
    https_url(template)
    if not all("{" + k + "}" in template for k in ("z", "x", "y")):
        raise ValueError("В XYZ-шаблоне нужны {z}, {x}, {y}.")
    # Only the three documented replacements; no arbitrary format expressions.
    extra = re.findall(r"\{([^}]+)\}", template)
    if set(extra) - {"z", "x", "y"}:
        raise ValueError("Поддерживаются только {z}, {x}, {y}.")
    return template.strip()


@st.cache_data(ttl=1800, max_entries=512, show_spinner=False)
def get_heat_tile(template, z, x, y):
    url = check_template(template).replace("{z}", str(z)).replace("{x}", str(x)).replace("{y}", str(y))
    r = requests.get(url, timeout=(5, 12), headers=HEADERS, allow_redirects=False)
    if r.status_code in (401, 403):
        raise ValueError("Источник требует авторизации/не разрешает доступ.")
    r.raise_for_status()
    if not r.headers.get("Content-Type", "").lower().startswith("image/"):
        raise ValueError("Вместо тайла получен не image/* (возможно, страница входа).")
    if len(r.content) > 4_000_000:
        raise ValueError("Слишком большой тайл.")
    with Image.open(io.BytesIO(r.content)) as image:
        if image.size != (256, 256):
            raise ValueError("Для этого анализатора нужен XYZ-тайл 256×256.")
        image.load()
        return image.convert("RGBA").tobytes()


def heat_analysis(coords, template, threshold, step=100, mode="grayscale", progress=None):
    """Length-weighted heat intensity coverage, NOT trail existence probability."""
    check_template(template)
    cum = chainages(coords)
    total = cum[-1]
    groups = {}
    count = max(1, math.ceil(total / step))
    for i in range(count):
        start, end = i * step, min(total, (i + 1) * step)
        lon, lat = geodesic_at(coords, cum, (start + end)/2)
        x, y, px, py = tile_position(lon, lat)
        groups.setdefault((x, y), []).append((px, py, end-start))
    if len(groups) > 80:
        raise ValueError("Более 80 тайлов: сократите маршрут. Массовая выгрузка отключена.")
    obtained, hot, errs = 0.0, 0.0, []
    for i, ((x, y), samples) in enumerate(groups.items()):
        try:
            raw = get_heat_tile(template, 14, x, y)
            image = Image.frombytes("RGBA", (256, 256), raw)
            for px, py, weight in samples:
                values = []
                for dx in range(-2, 3):
                    for dy in range(-2, 3):
                        xx, yy = max(0, min(255, int(px)+dx)), max(0, min(255, int(py)+dy))
                        r, g, b, a = image.getpixel((xx, yy))
                        signal = (.2126*r + .7152*g + .0722*b) if mode == "grayscale" else max(r, g, b)
                        values.append(signal * a / 255)
                obtained += weight
                if max(values) >= threshold:
                    hot += weight
        except (requests.RequestException, ValueError, OSError) as exc:
            errs.append(f"14/{x}/{y}: {exc}")
        if progress:
            progress((i+1)/len(groups), text=f"Теплокарта: тайл {i+1}/{len(groups)}")
        # Authorization failures apply to the whole source; do not hammer it.
        if errs and ("авторизац" in errs[-1] or "страница входа" in errs[-1]):
            break
    return {"coverage": obtained / total * 100 if total else 0,
            "index": hot / obtained * 100 if obtained else None,
            "hot_km": hot/1000, "errors": errs, "threshold": threshold,
            "step": step, "tiles": len(groups), "at": datetime.now(timezone.utc).isoformat()}


def deduplicate_nogos(existing, warnings):
    result = list(existing)
    for w in warnings:
        if w["avoid"]:
            p = (w["lon"], w["lat"])
            if not any(GEOD.inv(p[0], p[1], q[0], q[1])[2] < 40 for q in result):
                result.append(p)
    if len(result) > 40:
        raise ValueError("Более 40 no-go: разбейте маршрут на участки.")
    return result


def export_gpx(route, points, audit, heat=None):
    gpx = gpxpy.gpx.GPX()
    gpx.creator = APP
    gpx.name = "Tactical Pathfinder — маршрут и ориентир"
    status = "OSM-аудит завершён" if audit["complete"] else "OSM-аудит НЕПОЛНЫЙ"
    gpx.description = f"{status}, {audit['at']}. {DISCLAIMER} "
    gpx.description += "Предупреждений: " + str(len(audit["warnings"]))
    if heat and heat.get("index") is not None:
        gpx.description += f". Heat index {heat['index']:.1f}%, покрытие данных {heat['coverage']:.1f}%."
    for name, coords in (("01 — ОСНОВНОЙ МАРШРУТ", route["coords"]),
                        ("02 — ПТИЧКА А–Б / НЕ МАРШРУТ", [(points[0][1], points[0][0]), (points[-1][1], points[-1][0])])):
        trk = gpxpy.gpx.GPXTrack(name=name)
        trk.description = status + ". " + DISCLAIMER
        segment = gpxpy.gpx.GPXTrackSegment()
        for c in coords:
            ele = float(c[2]) if len(c) > 2 and c[2] is not None and math.isfinite(float(c[2])) else None
            segment.points.append(gpxpy.gpx.GPXTrackPoint(c[1], c[0], elevation=ele))
        trk.segments.append(segment)
        gpx.tracks.append(trk)
    for i, p in enumerate(points):
        name = "А — СТАРТ" if i == 0 else "Б — ФИНИШ" if i == len(points)-1 else f"ПРОМЕЖУТОЧНАЯ {i}"
        gpx.waypoints.append(gpxpy.gpx.GPXWaypoint(p[0], p[1], name=name, symbol="Flag"))
    for w in audit["warnings"]:
        wp = gpxpy.gpx.GPXWaypoint(w["lat"], w["lon"], name=w["name"], symbol="Danger Area")
        wp.description = f"{w['detail']} OSM: {w['osm']}. Примерно {w['metres']/1000:.2f} км от начала."
        gpx.waypoints.append(wp)
    coords = route["coords"]
    cum = chainages(coords)
    for distance in range(5000, int(cum[-1]) + 1, 5000):
        lon, lat = geodesic_at(coords, cum, distance)
        gpx.waypoints.append(gpxpy.gpx.GPXWaypoint(lat, lon, name=f"КМ {distance//1000:02d}", symbol="Flag"))
    # UTF-8 preserves Cyrillic and warning symbols; standard GPX 1.1.
    return gpx.to_xml(version="1.1").encode("utf-8")



# ----- v2: map-first interface and visible environmental overlays -----
TOPO_XYZ = "https://tiles.nakarte.me/topomapper/{z}/{x}/{y}"
GGC_TMS = "https://a.tiles.nakarte.me/ggc1000/{z}/{x}/{y}"
STRAVA_XYZ = "https://content-a.strava.com/identified/globalheat/run/hot/{z}/{x}/{y}.png?px=256"
OSM_TRACES = "https://a.gps-tile.openstreetmap.org/lines/{z}/{x}/{y}.png"
EMPTY_FEATURES = {"type": "FeatureCollection", "features": []}


def osm_features(elements):
    features, seen = [], set()
    for e in elements:
        tags = e.get("tags", {})
        kind = ("wetland" if tags.get("natural") == "wetland" else
                "water" if tags.get("waterway") in ("river", "stream", "canal", "drain", "ditch") else
                "bad_ground" if tags.get("surface") in ("mud", "peat") or tags.get("tracktype") in ("grade4", "grade5") else
                "restricted" if tags.get("foot") in ("no", "private", "permit") or
                    tags.get("access") in ("private", "no", "military", "permit") else None)
        if not kind:
            continue
        uid = f"{e['type']}/{e['id']}"
        if uid in seen:
            continue
        try:
            g = element_geometry(e)
            if g is None or g.is_empty:
                continue
            props = {"kind": kind, "osm": uid,
                     "description": html.escape(" · ".join(f"{k}={tags[k]}" for k in
                        ("natural", "wetland", "waterway", "tracktype", "surface", "access", "foot") if k in tags))}
            features.append({"type": "Feature", "geometry": mapping(g), "properties": props})
            seen.add(uid)
        except (ValueError, TypeError, KeyError):
            continue
    return {"type": "FeatureCollection", "features": features}


def merge_features(*collections):
    result = {}
    for coll in collections:
        for f in (coll or EMPTY_FEATURES).get("features", []):
            result[f["properties"]["osm"]] = f
    return {"type": "FeatureCollection", "features": list(result.values())}


def viewport_query(bounds):
    sw, ne = bounds["_southWest"], bounds["_northEast"]
    south, west, north, east = float(sw["lat"]), float(sw["lng"]), float(ne["lat"]), float(ne["lng"])
    validate_point(south, west)
    validate_point(north, east)
    width = GEOD.inv(west, south, east, south)[2]
    height = GEOD.inv(west, south, west, north)[2]
    if not (0 < width < 22000 and 0 < height < 22000 and width*height <= 180_000_000):
        raise ValueError("Приблизьте карту: область загрузки должна быть меньше 180 км² и 22 км по стороне.")
    box = f"({south:.6f},{west:.6f},{north:.6f},{east:.6f})"
    # is_in at viewport centre also retrieves large wetlands surrounding the viewport.
    lat, lon = (south+north)/2, (west+east)/2
    return (f'[out:json][timeout:40][maxsize:67108864];is_in({lat:.6f},{lon:.6f})->.a;'
            f'area.a["natural"="wetland"]->.wetareas;('
            f'nwr["natural"="wetland"]{box};'
            f'way["waterway"~"^(river|stream|canal|drain|ditch)$"]{box};'
            f'way["highway"]["tracktype"~"^grade[45]$"]{box};'
            f'way["highway"]["surface"~"^(mud|peat)$"]{box};'
            f'way["highway"]["access"~"^(no|private|military|permit)$"]{box};'
            'way(pivot.wetareas);rel(pivot.wetareas););out body geom;')


@st.cache_data(ttl=300, show_spinner=False)
def probe_tile(template, lat, lon, zoom, tms=False):
    x, y, _, _ = tile_position(lon, lat, zoom)
    if tms:
        y = 2**zoom - 1 - y
    url = check_template(template).replace("{z}", str(zoom)).replace("{x}", str(x)).replace("{y}", str(y))
    try:
        r = requests.get(url, timeout=(5, 12), headers=HEADERS, allow_redirects=False)
        if r.status_code in (401, 403):
            return False, f"HTTP {r.status_code}: требуется разрешение/авторизация."
        if not r.ok:
            return False, f"HTTP {r.status_code}: для выбранной точки тайл недоступен."
        if not r.headers.get("Content-Type", "").lower().startswith("image/"):
            return False, "Сервис вернул не изображение (возможна страница входа)."
        with Image.open(io.BytesIO(r.content)) as im:
            im.verify()
        return True, "Сервер вернул изображение для выбранной точки; отображение в браузере зависит от провайдера."
    except (requests.RequestException, ValueError, OSError) as exc:
        return False, str(exc)[:220]


class TileStatusControl(MacroElement):
    """Browser-side tile errors: do not leave a failed layer silently invisible."""
    def __init__(self):
        super().__init__()
        self._name = "TileStatusControl"
        self._template = Template(r"""{% macro script(this, kwargs) %}
        (function(){
          const map = {{this._parent.get_name()}};
          const status = L.control({position:'bottomleft'});
          status.onAdd = function(){
            const box = L.DomUtil.create('div');
            box.style.cssText='display:none;max-width:240px;background:#fff;color:#9f1239;padding:8px 10px;border:1px solid #fda4af;border-radius:8px;font:14px/1.4 system-ui;box-shadow:0 1px 5px #0003';
            this.box=box; L.DomEvent.disableClickPropagation(box);return box;
          };status.addTo(map);
          function bind(layer){
            if(!layer.on || !layer._url || layer.__tfBound)return;
            layer.__tfBound=true;
            layer.on('tileerror',function(){
              if(map.hasLayer(layer)){
                status.box.textContent='Слой не загрузился: '+(layer.options.tfLabel||'карта')+'. Откройте «Слои» и проверьте источник.';
                status.box.style.display='block';
              }
            });
          }
          map.eachLayer(bind);
          map.on('layeradd',function(e){bind(e.layer);});
          map.on('baselayerchange overlayremove',function(){status.box.style.display='none';});
        })();
        {% endmacro %}""")


def map_v2(points, routes, selected, audit, features, nogos, config, center, zoom, fit=False):
    m = folium.Map(location=center, zoom_start=zoom, tiles=None, control_scale=True,
                   prefer_canvas=True, zoom_control=True, max_zoom=20)
    folium.map.CustomPane("paper", z_index=240).add_to(m)
    folium.map.CustomPane("heat", z_index=360).add_to(m)
    folium.map.CustomPane("terrain", z_index=430).add_to(m)
    folium.map.CustomPane("route", z_index=610).add_to(m)
    bases = {
        "OSM": ("https://tile.openstreetmap.org/{z}/{x}/{y}.png", "© OpenStreetMap contributors", 19),
        "Спутник": ("https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}", "Esri · Maxar · Earthstar Geographics", 19),
        "CyclOSM": ("https://a.tile-cyclosm.openstreetmap.fr/cyclosm/{z}/{x}/{y}.png", "© OSM contributors · CyclOSM", 20),
        "Генштаб": (TOPO_XYZ, "Soviet topo maps · AtloMaps / Nakarte", 13),
    }
    name = config["base"]
    url, attr, native = bases[name]
    if name == "Генштаб" and config["custom_topo"]:
        url = config["custom_topo"]
    folium.TileLayer(url, attr=attr, name=name, max_native_zoom=native, max_zoom=20,
                     tf_label=name).add_to(m)
    if config["ggc"]:
        folium.TileLayer(GGC_TMS, attr="ГГЦ · Nakarte", name="ГГЦ 1 км", tms=True,
                         overlay=True, pane="paper", max_native_zoom=13, max_zoom=20,
                         opacity=config["paper_opacity"], tf_label="ГГЦ 1 км").add_to(m)
    if config["heat"]:
        folium.TileLayer(config["heat_url"], attr="© Strava Global Heatmap" if config["heat_type"] == "Strava" else "© OpenStreetMap public GPS traces (не Strava)",
                         name=config["heat_type"], overlay=True, pane="heat", opacity=config["heat_opacity"],
                         max_native_zoom=14, max_zoom=20, tf_label=config["heat_type"]).add_to(m)
    styles = {
        "wetland": {"color": "#075985", "fillColor": "#06b6d4", "fillOpacity": .30, "weight": 2.5, "dashArray": "5 4"},
        "water": {"color": "#0067da", "weight": 3.5, "opacity": .95},
        "bad_ground": {"color": "#9a3412", "weight": 5, "dashArray": "6 5"},
        "restricted": {"color": "#be123c", "weight": 4, "dashArray": "2 6"},
    }
    allowed = {k for k in styles if config[k]}
    visible = {"type": "FeatureCollection", "features": [f for f in features.get("features", []) if f["properties"]["kind"] in allowed]}
    if visible["features"]:
        folium.GeoJson(visible, name="Болота / вода / грунт", pane="terrain",
                       style_function=lambda f: styles[f["properties"]["kind"]],
                       tooltip=folium.GeoJsonTooltip(fields=["description"], labels=False, sticky=False)).add_to(m)
    if len(points) >= 2 and config["beeline"]:
        for color, weight in (("#fff", 5), ("#dc2626", 3)):
            folium.PolyLine([points[0], points[-1]], color=color, weight=weight,
                            dash_array="10 8", pane="route", tooltip="Птичка А–Б · не маршрут").add_to(m)
    # Draw selected route last and with casing: it remains readable over every base.
    ordering = [i for i in range(len(routes)) if i != selected] + ([selected] if routes else [])
    for i in ordering:
        r = routes[i]
        active = i == selected
        if not active and not config["alternatives"]:
            continue
        ll = [(c[1], c[0]) for c in r["coords"]]
        title = f"{'Основной' if active else 'Запасной'} · {geodesic_length(r['coords'])/1000:.1f} км"
        for color, weight in ((("#172554", 10), ("#fff", 8), ("#14d160", 5)) if active else (("#fff", 6), ("#2563eb", 3))):
            folium.PolyLine(ll, color=color, weight=weight, opacity=1 if active else .8,
                            pane="route", tooltip=title).add_to(m)
    for i, p in enumerate(points):
        text = config["point_labels"][i]
        color = "#1761c7" if text == "А" else "#bc2437" if text == "Б" else "#6941b9"
        icon = folium.DivIcon(html=f'<div style="width:32px;height:32px;border:3px solid white;border-radius:50%;background:{color};color:white;font:bold 17px/27px system-ui;text-align:center;box-shadow:0 1px 6px #0009">{text}</div>', icon_size=(38,38), icon_anchor=(19,19))
        folium.Marker(p, icon=icon, tooltip="Старт" if text == "А" else "Финиш" if text == "Б" else f"Точка {text}").add_to(m)
    for w in (audit or {}).get("warnings", []):
        info = w["kind"] == "mapped_crossing"
        popup = html.escape(w["name"]) + "<br>" + html.escape(w["detail"])
        icon = folium.DivIcon(html=f'<div style="width:30px;height:30px;border:2px solid white;border-radius:6px;background:{"#1761c7" if info else "#b52d16"};color:white;font:bold 22px/26px system-ui;text-align:center;box-shadow:0 1px 5px #0008">{"i" if info else "!"}</div>', icon_size=(34,34), icon_anchor=(17,17))
        folium.Marker([w["lat"], w["lon"]], icon=icon, tooltip=w["name"], popup=folium.Popup(popup, max_width=280)).add_to(m)
    for lon, lat in nogos:
        folium.Circle([lat, lon], radius=150, color="#dc2626", weight=2, fill=True,
                      fill_opacity=.12, pane="route", tooltip="Запрет обхода · 150 м").add_to(m)
    if routes and config["km_marks"]:
        coords = routes[selected]["coords"]
        cum = chainages(coords)
        for d in range(5000, int(cum[-1])+1, 5000):
            lon, lat = geodesic_at(coords, cum, d)
            folium.CircleMarker([lat,lon], radius=5, color="#fff", weight=2, fill=True,
                                fill_color="#111827", fill_opacity=1,
                                tooltip=f"{d//1000} км").add_to(m)
    Fullscreen(position="topleft", title="Во весь экран", title_cancel="Вернуться").add_to(m)
    LocateControl(position="topleft", strings={"title": "Моё местоположение"},
                  locateOptions={"enableHighAccuracy": True}).add_to(m)
    TileStatusControl().add_to(m)
    if fit:
        bounds = [(c[1],c[0]) for r in routes for c in r["coords"]] or points
        if len(bounds) > 1:
            m.fit_bounds(bounds, padding=(35,35))
        elif bounds:
            m.location = bounds[0]
    return m


def ordered_points():
    s = st.session_state
    return ([s.start] if s.start else []) + list(s.vias) + ([s.finish] if s.finish else [])


def invalidate():
    s = st.session_state
    for k in ("routes", "nogos", "route_points", "routing_config"):
        s[k] = []
    s.audits, s.heat_results = {}, {}


def set_point(point, role):
    validate_point(*point)
    s = st.session_state
    if role == "А":
        s.start = point
    elif role == "Б":
        s.finish = point
    else:
        if not s.start or not s.finish:
            raise ValueError("Сначала задайте А и Б.")
        if len(s.vias) >= 8:
            raise ValueError("Максимум 8 промежуточных точек.")
        s.vias.append(point)
    invalidate()


def ensure_audit(route, primary):
    key = route["signature"] + "|" + primary
    if key not in st.session_state.audits:
        with st.spinner("Проверка воды, болот и переходов…"):
            try:
                result = audit_route(route, primary)
                st.session_state.audits[key] = result
            except Exception as exc:
                st.session_state.audits[key] = {"warnings": [], "errors": [str(exc)], "complete": False,
                    "features": EMPTY_FEATURES, "at": datetime.now(timezone.utc).isoformat(), "count": 0, "sources": []}
    return st.session_state.audits[key]


def main():
    st.set_page_config(page_title="Pathfinder · Карта", page_icon="🧭", layout="wide", initial_sidebar_state="collapsed")
    st.markdown('''<style>
    .block-container{max-width:1120px;padding:1rem 1.2rem 2rem}
    h1{font-size:24px!important;letter-spacing:-.7px;margin-bottom:0!important}
    h2{font-size:22px!important} h3{font-size:19px!important}
    .stButton button,.stDownloadButton button{min-height:46px;border-radius:8px;font-weight:600}
    [data-testid="stMetricValue"]{font-size:24px}
    .tf-legend{display:flex;gap:8px 14px;flex-wrap:wrap;font:14px/1.5 system-ui;color:#475569;padding:4px 0 10px}
    .tf-legend span{white-space:nowrap}.tf-line{display:inline-block;width:18px;height:4px;vertical-align:middle;margin-right:4px}
    .tf-stats{display:flex;flex-wrap:wrap;gap:8px 20px;border:1px solid #dbe2ea;border-radius:8px;padding:10px 14px;margin:8px 0;font:15px/1.6 system-ui;background:#f8fafc;color:#1e293b}
    @media(max-width:600px){.block-container{padding:.6rem .7rem 1.5rem}.stButton button{font-size:14px;padding:.35rem .5rem}h1{font-size:22px!important}}
    </style>''', unsafe_allow_html=True)
    s = st.session_state
    defaults = {"start": None, "finish": None, "vias": [], "routes": [], "audits": {},
                "heat_results": {}, "nogos": [], "route_points": [], "routing_config": [],
                "map_center": [55.19,30.20], "map_zoom": 12, "map_bounds": None,
                "map_features": EMPTY_FEATURES, "consumed_click": None, "fit_next": False,
                "map_epoch": 0, "ui_version": "2.0", "tap_mode": "А", "route_choice": 0}
    for k,v in defaults.items():
        if k not in s:
            s[k] = v
    if s.get("pending_mode"):
        s.tap_mode = s.pop("pending_mode")
    if s.get("reset_choice"):
        s.route_choice = 0
        s.reset_choice = False
    st.title("🧭 Pathfinder")
    st.caption("Карта → точки А / Б → маршрут → GPX")
    map_tab, route_tab, settings_tab = st.tabs(["Карта", "Маршрут", "Настройки"])
    with settings_tab:
        st.subheader("Сервисы")
        base = st.text_input("BRouter", "https://brouter.de/brouter")
        overpass = st.selectbox("Overpass", OVERPASS)
        lookup_url = st.text_input("Таблица lookup", LOOKUPS)
        st.caption("В v2 разрешения foot/access обрабатываются белым списком отдельно для дорог и узлов. Неизвестное значение доступа не становится разрешением.")
        st.subheader("Источники слоёв")
        st.write("Генштаб и ГГЦ подключены по опубликованным адресам слоёв Nakarte. Покрытие и доступность зависят от поставщика. ГГЦ использует TMS, Генштаб — XYZ.")
        custom_topo = st.text_input("Свой Генштаб XYZ (необязательно)", "")
        custom_heat = st.text_input("Свой разрешённый Strava XYZ (необязательно)", "")
        heat_permission = st.checkbox("У меня есть право доступа к выбранному источнику Strava")
        st.caption("Без входа Strava может отвечать 401/403. Обход авторизации не выполняется; обычная OSM GPS-трассировка доступна как отдельный, честно подписанный слой.")
        st.subheader("Нагрузка")
        c1,c2 = st.columns(2)
        body = c1.number_input("Вес человека, кг", 35.0,200.0,90.0,1.0)
        load = c2.number_input("Груз, кг",0.0,65.0,25.0,1.0)
        pauses = st.slider("Привалы, % к ходовому времени",0,80,20)/100
        water_rate = st.slider("План воды, л/ч",.2,1.2,.5,.1)
        reserve = st.slider("Резерв воды, %",0,50,20)/100
        grade = st.slider("Сценарный уклон, %",0.0,12.0,0.0,.5)
        with st.expander("Тепловой анализ — дополнительно"):
            threshold = st.slider("Порог сигнала",1,255,45)
            heat_mode = st.selectbox("Кодировка",["colored","grayscale"])
        st.warning("Планирование требует интернета. Координаты передаются картографическим сервисам. OSM не подтверждает проходимость, право прохода, состояние моста или текущий разлив.")
        st.caption("Моё местоположение на карте работает только после вашего разрешения браузеру. Никакого фонового GPS-трекинга нет.")
    # Defaults for rendering are fixed above; widgets execute even in inactive tabs.
    with map_tab:
        with st.expander("Слои карты", expanded=False):
            base_layer = st.radio("Подложка",["OSM","Спутник","CyclOSM","Генштаб"],horizontal=True)
            c1,c2 = st.columns(2)
            ggc = c1.checkbox("ГГЦ 1 км поверх карты")
            heat_enabled = c2.checkbox("GPS / теплокарта")
            if heat_enabled:
                heat_type = st.radio("Источник активности",["GPS OSM","Strava"],horizontal=True)
            else:
                heat_type = "GPS OSM"
            c1,c2 = st.columns(2)
            wetland = c1.checkbox("Болота",True)
            water = c2.checkbox("Каналы и ручьи",True)
            bad_ground = c1.checkbox("Плохой грунт",True)
            restricted = c2.checkbox("Ограничения OSM",True)
            alternatives = c1.checkbox("Запасные маршруты",True)
            beeline = c2.checkbox("Птичка А–Б",True)
            km_marks = c1.checkbox("Засечки 5 км",True)
            paper_opacity = st.slider("Непрозрачность ГГЦ",.1,1.0,.65,.05)
            heat_opacity = st.slider("Непрозрачность GPS / Strava",.1,1.0,.85,.05)
            if st.button("Проверить растровые слои здесь"):
                targets = []
                if base_layer == "Генштаб": targets.append(("Генштаб",custom_topo or TOPO_XYZ,13,False))
                if ggc: targets.append(("ГГЦ",GGC_TMS,13,True))
                if heat_enabled:
                    if heat_type == "Strava" and not heat_permission:
                        st.warning("Сначала подтвердите право доступа к Strava в настройках.")
                    else:
                        targets.append((heat_type,(custom_heat or STRAVA_XYZ) if heat_type == "Strava" else OSM_TRACES,14,False))
                for name,url,z,tms in targets:
                    try:
                        ok,message = probe_tile(url,*s.map_center,z,tms)
                        (st.info if ok else st.warning)(name+": "+message)
                    except ValueError as exc:
                        st.error(str(exc))
                if not targets:
                    st.info("Включите Генштаб, ГГЦ или GPS-слой для проверки.")
        if heat_enabled and heat_type == "Strava" and not heat_permission:
            st.info("Strava не включена: подтвердите право доступа во вкладке «Настройки». GPS OSM — отдельный доступный вариант.")
            heat_enabled = False
        heat_url = ((custom_heat or STRAVA_XYZ) if heat_type == "Strava" else OSM_TRACES)
        for label,url in (("Генштаб",custom_topo),("GPS / Strava",heat_url if heat_enabled else "")):
            if url:
                try:
                    check_template(url)
                except ValueError as exc:
                    st.error(label+": "+str(exc))
                    if label == "Генштаб": custom_topo=""
                    else: heat_enabled=False
        st.radio("Тап по карте",["Осмотр","А","Б","+ точка"],horizontal=True,key="tap_mode")
        points = ordered_points()
        ready = s.start is not None and s.finish is not None
        c1,c2,c3 = st.columns([1.3,1,1])
        calculate = c1.button("Построить",type="primary",disabled=not ready,use_container_width=True)
        fit = c2.button("Весь путь",use_container_width=True)
        scan = c3.button("Болота здесь",disabled=s.map_bounds is None,use_container_width=True)
        if fit:
            s.fit_next = True
            s.map_epoch += 1
        if calculate:
            if geodesic_length([(p[1],p[0]) for p in points]) > 150000:
                st.error("Слишком длинный запрос: разбейте путь на части до 150 км.")
            else:
                try:
                    with st.spinner("BRouter: расчёт вариантов…"):
                        try:
                            meta = lookup_metadata(lookup_url)
                        except (requests.RequestException,ValueError):
                            meta = None
                        profile,notes = make_profile(meta)
                        try:
                            new_routes,errors = build_routes(base,profile,points,[])
                        except ValueError as exc:
                            # Optional polygon/peat values can differ between published and deployed lookup.
                            # Never silently switch to a standard, less restrictive routing profile.
                            if meta and "unknown lookup" in str(exc).lower():
                                profile,core_notes = make_profile(None)
                                new_routes,errors = build_routes(base,profile,points,[])
                                notes += core_notes + ["Опциональные lookup-теги не совпали с сервером; применено то же антигрязевое ядро, болота проверяются Overpass."]
                            else:
                                raise
                    invalidate()
                    s.routes,s.route_points,s.routing_config = new_routes,points,[base,profile]
                    s.profile_text,s.profile_notes,s.route_errors = profile,notes,errors
                    s.fit_next,s.reset_choice = True,True
                    s.map_epoch += 1
                    s.pending_mode="Осмотр"
                    st.rerun()
                except (requests.RequestException,ValueError,TypeError,KeyError) as exc:
                    st.error("Не удалось построить: "+str(exc)[:600])
        if scan:
            try:
                with st.spinner("Загрузка болот и водотоков видимой области…"):
                    elements,source = overpass_chunk(viewport_query(s.map_bounds),overpass)
                    # Replace this viewport result: do not accumulate unlimited objects while panning.
                    s.map_features = osm_features(elements)
                    s.scan_info = f"Область OSM: {len(s.map_features['features'])} объектов. {datetime.now(timezone.utc).strftime('%H:%M UTC')}"
            except (requests.RequestException,ValueError,KeyError) as exc:
                st.warning(str(exc))
        route,audit = None,None
        selected = min(int(s.route_choice),len(s.routes)-1) if s.routes else 0
        if s.routes:
            selected = st.selectbox("Вариант",list(range(len(s.routes))),key="route_choice",
                format_func=lambda i:f"{'Основной' if i==0 else 'Запасной '+str(i)} · {geodesic_length(s.routes[i]['coords'])/1000:.1f} км · {sum(d/1000/v for d,v,_,_ in route_segments(s.routes[i])[0]):.1f} ч")
            route=s.routes[selected]
            audit=ensure_audit(route,overpass)
        features=merge_features(s.map_features,(audit or {}).get("features"))
        config=dict(point_labels=(["А"] if s.start else []) + [str(i+1) for i in range(len(s.vias))] + (["Б"] if s.finish else []),base=base_layer,custom_topo=custom_topo,ggc=ggc,heat=heat_enabled,
                    heat_type=heat_type,heat_url=heat_url,paper_opacity=paper_opacity,
                    heat_opacity=heat_opacity,wetland=wetland,water=water,bad_ground=bad_ground,
                    restricted=restricted,alternatives=alternatives,beeline=beeline,km_marks=km_marks)
        st.markdown('<div class="tf-legend"><span><i class="tf-line" style="background:#14a34a"></i>маршрут</span><span><i class="tf-line" style="background:#2563eb"></i>запасной</span><span>🟦 болота / вода</span><span>🟫 плохой грунт</span><span>❗ проверить</span></div>',unsafe_allow_html=True)
        frame=map_v2(points,s.routes,selected,audit,features,s.nogos,config,s.map_center,s.map_zoom,s.fit_next)
        s.fit_next=False
        view=st_folium(frame,height=560,use_container_width=True,key=f"tf_map_{s.map_epoch}",
            returned_objects=["last_clicked","bounds","zoom","center"])
        if view:
            if view.get("bounds"): s.map_bounds=view["bounds"]
            if view.get("zoom") is not None: s.map_zoom=int(view["zoom"])
            if view.get("center"):
                center=view["center"]
                if isinstance(center,dict) and "lat" in center:
                    s.map_center=[float(center["lat"]),float(center.get("lng",center.get("lon")))]
            click=view.get("last_clicked")
            if click:
                tap=(round(float(click["lat"]),7),round(float(click["lng"]),7))
                if tap != s.consumed_click:
                    s.consumed_click=tap
                    if s.tap_mode != "Осмотр":
                        try:
                            mode=s.tap_mode
                            set_point(tap,mode)
                            s.pending_mode="Б" if mode=="А" and s.finish is None else "Осмотр" if mode=="Б" else mode
                            st.rerun()
                        except ValueError as exc:
                            st.warning(str(exc))
        if not ready:
            st.caption("Выберите А и тапните по карте. Затем Б → тап → «Построить». Координаты можно ввести во вкладке «Маршрут».")
        if route:
            stats=estimate(route_segments(route)[0],body,load,grade,pauses,water_rate,reserve)
            st.markdown(f'<div class="tf-stats"><span><b>{stats["Длина, км"]} км</b></span><span>{stats["С привалами, ч"]} ч с привалами</span><span>{len(audit["warnings"])} отметок OSM</span></div>',unsafe_allow_html=True)
            if not audit["complete"]:
                st.warning("Аудит частичный: не все участки удалось проверить. Подробности — «Маршрут».")
            hazards=[w for w in audit["warnings"] if w["avoid"]]
            if st.button("Обойти воду · радиус 150 м",disabled=not hazards,use_container_width=True):
                try:
                    ng=deduplicate_nogos(s.nogos,hazards)
                    with st.spinner("Поиск обхода…"):
                        new_routes,errors=build_routes(s.routing_config[0],s.routing_config[1],s.route_points,ng)
                    s.routes,s.nogos,s.route_errors=new_routes,ng,errors
                    s.reset_choice,s.fit_next=True,True
                    s.map_epoch+=1
                    st.rerun()
                except (requests.RequestException,ValueError) as exc:
                    st.error("Обход не принят: "+str(exc)[:500])
            export_ack=st.checkbox("Понимаю: OSM не гарантирует безопасный проход")
            partial_ok=audit["complete"] or st.checkbox("Скачать с пометкой «аудит неполный»")
            st.download_button("📥 GPX для AlpineQuest",export_gpx(route,s.route_points,audit),
                "pathfinder.gpx","application/gpx+xml",type="primary",use_container_width=True,
                disabled=not(export_ack and partial_ok))
        st.caption(s.get("scan_info","Болота вдоль выбранного маршрута загружаются при аудите. Для окрестностей приблизьте карту и нажмите «Болота здесь»."))
        st.caption("Генштаб/ГГЦ — исторические карты. GPS OSM ≠ Strava. Болота OSM и спутник не отражают текущую воду и все препятствия.")

    with route_tab:
        st.subheader("Точки")
        coord_type=st.radio("Формат",["WGS-84","СК-42"],horizontal=True)
        zone=6
        with st.form("coordinates_v2"):
            role=st.radio("Добавить",["А","Б","+ точка"],horizontal=True)
            if coord_type=="WGS-84":
                c1,c2=st.columns(2)
                lat=c1.number_input("Lat",50.0,58.0,55.19,format="%.7f")
                lon=c2.number_input("Lon",21.0,35.0,30.20,format="%.7f")
            else:
                zone=st.selectbox("Зона СК-42",[5,6],index=1)
                c1,c2=st.columns(2)
                x=c1.number_input("X · север, м",value=5921783.0,format="%.2f")
                y=c2.number_input("Y · восток с зоной, м",value=6583475.0,format="%.2f")
            if st.form_submit_button("Применить координаты"):
                try:
                    if coord_type=="СК-42":
                        lat,lon,accuracy,desc=sk_to_wgs(x,y,zone)
                        s.coord_info=f"Операция СК-42: точность {accuracy} м. {desc}"
                    set_point((lat,lon),role)
                    s.map_center=[lat,lon]
                    s.map_epoch+=1
                    st.rerun()
                except (ValueError,RuntimeError) as exc:
                    st.error(str(exc))
        if s.get("coord_info"): st.caption(s.coord_info)
        points=ordered_points()
        if points:
            st.dataframe([{"Точка":((["А"] if s.start else [])+[str(j+1) for j in range(len(s.vias))]+(["Б"] if s.finish else []))[i],"Lat":p[0],"Lon":p[1]} for i,p in enumerate(points)],hide_index=True,use_container_width=True)
        c1,c2=st.columns(2)
        if c1.button("Удалить последнюю +точку",disabled=not s.vias,use_container_width=True):
            s.vias.pop();invalidate();st.rerun()
        if c2.button("Сбросить всё",use_container_width=True):
            s.start,s.finish,s.vias=None,None,[]
            s.pending_mode="А"
            invalidate();st.rerun()
        if s.start and s.finish:
            az,_,direct=GEOD.inv(s.start[1],s.start[0],s.finish[1],s.finish[0])
            st.write(f"Птичка А–Б: **{direct/1000:.2f} км** · истинный азимут **{az%360:.1f}°**")
            with st.expander("СК-42 и дирекционный угол"):
                zone=st.selectbox("Зона сетки",[5,6],index=1)
                try:
                    a_x,a_y=wgs_to_sk(*s.start,zone)
                    b_x,b_y=wgs_to_sk(*s.finish,zone)
                    angle=math.degrees(math.atan2(b_y-a_y,b_x-a_x))%360
                    st.write(f"От севера сетки зоны {zone}: {angle:.1f}°. Магнитное склонение не учтено.")
                    st.dataframe([{"Точка":i+1,"X":round(wgs_to_sk(*p,zone)[0],2),"Y":round(wgs_to_sk(*p,zone)[1],2)} for i,p in enumerate(points)],hide_index=True)
                except (ValueError,RuntimeError) as exc: st.error(str(exc))
        if s.routes:
            route=s.routes[min(int(s.route_choice),len(s.routes)-1)]
            audit=ensure_audit(route,overpass)
            st.subheader("Аудит маршрута")
            st.write("Завершён по OSM, не аттестация проходимости." if audit["complete"] else "НЕПОЛНЫЙ — есть ошибки загрузки.")
            if audit["warnings"]:
                st.dataframe([{"Км ≈":round(w["metres"]/1000,2),"Отметка":w["name"],"Основание":w["detail"]} for w in audit["warnings"]],hide_index=True,use_container_width=True)
            else:
                st.caption("Отметок в полученных данных нет. Это не доказательство отсутствия препятствий.")
            st.subheader("Время и нагрузка")
            segments,coverage=route_segments(route)
            rows=[{"Путь":"Обход",**estimate(segments,body,load,grade,pauses,water_rate,reserve)}]
            if s.start and s.finish:
                direct=GEOD.inv(s.start[1],s.start[0],s.finish[1],s.finish[0])[2]
                rows.insert(0,{"Путь":"Птичка · только сценарий",**estimate([(direct,2.0,1.8,"offroad")],body,load,grade,pauses,water_rate,reserve)})
            st.dataframe(rows,hide_index=True,use_container_width=True)
            st.caption(f"Теги покрытия: {coverage*100:.0f}% длины. 6.2 км/ч по grade1–2 — сценарий, не обещание темпа на 70 км. Pandolf не учитывает рост; вода — отдельный план л/ч, не медицинская норма.")
            if heat_enabled and heat_type=="Strava" and heat_permission:
                if st.button("Оценить сигнал Strava вдоль пути"):
                    try:
                        with st.spinner("Анализ разрешённой теплокарты…"):
                            hr=heat_analysis(route["coords"],heat_url,threshold,mode=heat_mode)
                        s.heat_results[route["signature"]]=hr
                    except (requests.RequestException,ValueError,OSError) as exc: st.warning(str(exc))
                hr=s.heat_results.get(route["signature"])
                if hr:
                    if hr["index"] is None: st.warning("Strava: нет данных, а не 0% активности.")
                    else: st.write(f"Сигнал: {hr['index']:.1f}% исследованной длины; получено {hr['coverage']:.1f}% данных маршрута.")
                    if hr["errors"]: st.caption("; ".join(hr["errors"][:3]))
            with st.expander("Диагностика и профиль"):
                st.write("Варианты могут перекрываться; самый быстрый — по модели среди полученных, не глобальная гарантия.")
                for msg in s.get("profile_notes",[])+s.get("route_errors",[])+audit["errors"]: st.write(msg)
                st.caption("Аудит UTC: "+audit["at"])
                st.download_button("Профиль BRF",s.get("profile_text",s.routing_config[1]),"anti_bog_v2.brf","text/plain")
                if st.button("Повторить аудит"):
                    # A nonce would defeat caching; explicitly clear the selected route's chunk queries.
                    fwd,inv=local_projection(route["coords"])
                    line=transform(fwd,LineString([c[:2] for c in route["coords"]]))
                    for i in range(max(1,math.ceil(line.length/8000))):
                        seg=substring(line,max(0,i*8000-60),min(line.length,(i+1)*8000+60))
                        overpass_chunk.clear(corridor_query(list(transform(inv,seg).coords)),overpass)
                    s.audits.pop(route["signature"]+"|"+overpass,None)
                    st.rerun()


if __name__ == "__main__":
    main()
