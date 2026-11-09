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
from shapely.geometry import LineString, Point, Polygon
from shapely.ops import nearest_points, polygonize, substring, transform, unary_union
from streamlit_folium import st_folium

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
assign footaccess = if foot=no|private then false
 else if foot=yes|designated|permissive then true
 else if access=no|private|military|permit then false else true
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
assign initialcost =
{NODE_EXTRA}
 if foot=no|private then 1000000
 else if foot=yes|designated|permissive then 0
 else if access=no|private|military|permit then 1000000
 else 0
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
            "sources": sources, "count": len(elements),
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


def make_map(points, routes, selected, audit, nogos, topo, heat):
    center = [55.19, 30.20] if not points else points[0]
    m = folium.Map(location=center, zoom_start=10, tiles=None, control_scale=True,
                   prefer_canvas=True)
    folium.TileLayer("https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}",
                     attr="Esri, Maxar, Earthstar Geographics and imagery contributors",
                     name="Спутник · Esri", max_zoom=19).add_to(m)
    folium.TileLayer("https://a.tile-cyclosm.openstreetmap.fr/cyclosm/{z}/{x}/{y}.png",
                     attr="© OpenStreetMap contributors · CyclOSM", name="CyclOSM", max_zoom=20).add_to(m)
    folium.TileLayer("https://tile.openstreetmap.org/{z}/{x}/{y}.png",
                     attr="© OpenStreetMap contributors", name="OpenStreetMap", max_zoom=19).add_to(m)
    for template, label, attr in ((topo, "Генштаб / ГГЦ · источник пользователя", "Источник топокарты пользователя"),
                                   (heat, "Strava · источник пользователя", "© Strava · authorised source")):
        if template.strip():
            folium.TileLayer(check_template(template), attr=attr, name=label, overlay=True,
                             opacity=.55, show=False, max_native_zoom=14 if template == heat else 16,
                             max_zoom=20).add_to(m)
    if len(points) >= 2:
        az, _, d = GEOD.inv(points[0][1], points[0][0], points[-1][1], points[-1][0])
        folium.PolyLine([points[0], points[-1]], color="#ef4444", dash_array="9 7", weight=3,
                        tooltip=f"Птичка: {d/1000:.2f} км · истинный азимут {az%360:.1f}°").add_to(m)
    for i, p in enumerate(points):
        label = "А · Старт" if i == 0 else "Б · Финиш" if i == len(points)-1 else f"Промежуточная {i}"
        folium.Marker(p, tooltip=label, icon=folium.Icon(color="red" if i == len(points)-1 else "blue", icon="flag")).add_to(m)
    for i, r in enumerate(routes):
        active = i == selected
        folium.PolyLine([(c[1], c[0]) for c in r["coords"]],
                        color="#22c55e" if active else "#3b82f6", weight=5 if active else 3,
                        opacity=.95 if active else .65,
                        tooltip=f"{'Основной' if active else 'Альтернатива'} · BRouter {r['alternative']} · {geodesic_length(r['coords'])/1000:.1f} км").add_to(m)
    for w in (audit or {}).get("warnings", []):
        popup = f"<b>{html.escape(w['name'])}</b><br>{html.escape(w['detail'])}<br><a href='{html.escape(w['osm'], quote=True)}' target='_blank' rel='noopener'>Объект OSM</a>"
        folium.Marker([w["lat"], w["lon"]], tooltip=w["name"], popup=folium.Popup(popup, max_width=280),
                      icon=folium.Icon(color="orange" if w["kind"] != "mapped_crossing" else "blue", icon="warning-sign")).add_to(m)
    for lon, lat in nogos:
        folium.Circle([lat, lon], radius=150, color="#ef4444", fill=True,
                      fill_opacity=.12, tooltip="No-go · 150 м").add_to(m)
    folium.LayerControl(collapsed=True).add_to(m)
    bounds = [(c[1], c[0]) for r in routes for c in r["coords"]] or list(points)
    if len(bounds) > 1:
        m.fit_bounds(bounds, padding=(24, 24))
    return m


def ordered_points():
    s = st.session_state
    return ([s.start] if s.start else []) + list(s.vias) + ([s.finish] if s.finish else [])


def invalidate():
    for k in ("routes", "audits", "heat_results", "nogos", "route_points", "routing_config"):
        st.session_state[k] = {} if k in ("audits", "heat_results") else []


def set_point(point, role):
    validate_point(*point)
    s = st.session_state
    if role == "А — старт":
        s.start = point
    elif role == "Б — финиш":
        s.finish = point
    else:
        if len(s.vias) >= 8:
            raise ValueError("Не более 8 промежуточных точек.")
        s.vias.append(point)
    invalidate()


def main():
    st.set_page_config(page_title=APP, page_icon="🧭", layout="wide", initial_sidebar_state="collapsed")
    st.markdown("""<style>
    .block-container{max-width:1120px;padding-top:1.8rem;padding-bottom:2rem}
    h1{font-size:clamp(1.65rem,4.5vw,2.5rem)!important;letter-spacing:-.035em}
    .stButton button,.stDownloadButton button{min-height:46px;border-radius:8px}
    [data-testid="stMetricValue"]{font-size:1.7rem}
    @media(max-width:600px){.block-container{padding:1rem}.stButton button{width:100%}}
    </style>""", unsafe_allow_html=True)
    s = st.session_state
    defaults = {"start": None, "finish": None, "vias": [], "routes": [], "audits": {},
                "heat_results": {}, "nogos": [], "last_tap": None, "route_points": [], "routing_config": []}
    for k, v in defaults.items():
        if k not in s:
            s[k] = v
    st.caption("ПЕШИЙ МАРШРУТИЗАТОР  /  БЕЛАРУСЬ  /  OSM-АУДИТ")
    st.title("🧭 Tactical Pathfinder SSS+++")
    st.write("Точки → три варианта → аудит воды и грунта → GPX для AlpineQuest.")
    st.caption("Настройки сервисов и слоёв — в боковой панели ☰ слева сверху.")
    st.warning("Не аттестация безопасности. " + DISCLAIMER)

    with st.sidebar:
        st.header("Настройки")
        base = st.text_input("BRouter /brouter", "https://brouter.de/brouter")
        lookup_url = st.text_input("Lookup именно вашего сервера", LOOKUPS,
                                   help="Для собственного сервера укажите опубликованный lookups.dat той же версии.")
        overpass = st.selectbox("Основной Overpass", OVERPASS)
        st.caption("Запросы передают координаты выбранным сервисам. Зеркало Overpass используется при ошибке. Публичная версия приложения не должна хранить чувствительные маршруты.")
        st.subheader("Дополнительные тайлы")
        topo = st.text_input("Генштаб / ГГЦ · HTTPS XYZ", "", help="Разрешённый источник с {z}/{x}/{y}. Историческая топокарта не подтверждает нынешние мосты.")
        heat = st.text_input("Strava · разрешённый HTTPS XYZ", "", help="Нужна отдельная теплокарта без картографической подложки, 256×256. Секреты в URL не вводите.")
        st.caption("Адрес nakarte.me{z}/{x}/{y}.png не является универсальным прокси Strava. Обход авторизации не выполняется.")
        heat_ok = st.checkbox("Источник тайлов разрешает такой доступ")
        heat_mode = st.selectbox("Кодировка интенсивности", ["grayscale", "colored"],
                                 format_func=lambda x: "Светлый сигнал / чёрный фон" if x == "grayscale" else "Цветной сигнал / прозрачный фон")
        threshold = st.slider("Порог сигнала 0–255", 1, 255, 45)
        st.subheader("Модель марша")
        body = st.number_input("Собственный вес, кг", 35.0, 200.0, 90.0, 1.0)
        load = st.number_input("Груз, кг", 0.0, 65.0, 25.0, 1.0)
        st.caption("Рост 196 см: в оригинальную формулу Pandolf не входит.")
        grade = st.slider("Сценарный уклон, %", 0.0, 12.0, 0.0, .5,
                          help="Это явное допущение для всего пути, не измеренный профиль высот.")
        pauses = st.slider("Привалы, % к ходовому времени", 0, 80, 20) / 100
        water_rate = st.slider("План воды, л/ч общего времени", .2, 1.2, .5, .1)
        reserve = st.slider("Резерв воды, %", 0, 50, 20) / 100

    with st.expander("1 · Координаты и точки маршрута", expanded=not bool(s.routes)):
        role = st.radio("Куда добавить точку", ["А — старт", "Б — финиш", "Промежуточная"], horizontal=True)
        tab1, tab2 = st.tabs(["WGS-84 · Lat, Lon", "СК-42 · X, Y"])
        with tab1:
            with st.form("wgs"):
                c1, c2 = st.columns(2)
                lat = c1.number_input("Широта Lat", 50.0, 58.0, 55.19, format="%.7f")
                lon = c2.number_input("Долгота Lon", 21.0, 35.0, 30.20, format="%.7f")
                if st.form_submit_button("Добавить WGS-84"):
                    try:
                        set_point((lat, lon), role)
                        st.rerun()
                    except ValueError as exc:
                        st.error(str(exc))
        with tab2:
            with st.form("sk42"):
                zone = st.selectbox("6-градусная зона Гаусса–Крюгера", [5, 6])
                x = st.number_input("X · северное смещение, м", value=5921783.0, format="%.2f")
                y = st.number_input("Y · восточное смещение с номером зоны, м", value=5583475.0, format="%.2f")
                if st.form_submit_button("Преобразовать и добавить СК-42"):
                    try:
                        la, lo, accuracy, desc = sk_to_wgs(x, y, zone)
                        set_point((la, lo), role)
                        s.crs_info = f"{la:.7f}, {lo:.7f}; заявленная точность операции: {accuracy if accuracy >= 0 else 'неизвестна'} м. {desc}"
                        st.rerun()
                    except (ValueError, RuntimeError) as exc:
                        st.error(str(exc))
            if s.get("crs_info"):
                st.info(s.crs_info)
            st.caption("X=northing, Y=easting. Семизначный Y обязателен. Точность datum shift зависит от операции и исходной карты; это не сантиметровая привязка.")
        if s.start:
            st.write(f"А: {s.start[0]:.6f}, {s.start[1]:.6f}")
        for i, p in enumerate(s.vias):
            st.write(f"Промежуточная {i+1}: {p[0]:.6f}, {p[1]:.6f}")
        if s.finish:
            st.write(f"Б: {s.finish[0]:.6f}, {s.finish[1]:.6f}")
        c1, c2 = st.columns(2)
        if c1.button("Убрать последнюю промежуточную", disabled=not s.vias):
            s.vias.pop()
            invalidate()
            st.rerun()
        if c2.button("Очистить точки и расчёты"):
            s.start, s.finish, s.vias, s.last_tap = None, None, [], None
            invalidate()
            st.rerun()

    points = ordered_points()
    ready = s.start is not None and s.finish is not None
    for label, value in (("Топокарта", topo), ("Теплокарта", heat)):
        if value.strip():
            try:
                check_template(value)
            except ValueError as exc:
                st.error(f"{label}: {exc}")
                if label == "Топокарта":
                    topo = ""
                else:
                    heat = ""
    if st.button("2 · Рассчитать 3 варианта и запустить аудит", type="primary", disabled=not ready, use_container_width=True):
        if geodesic_length([(p[1], p[0]) for p in points]) > 150_000:
            st.error("Суммарная птичка через точки длиннее 150 км. Разбейте план.")
        else:
            try:
                with st.spinner("Загрузка профиля и расчёт вариантов BRouter…"):
                    meta = None
                    try:
                        meta = lookup_metadata(lookup_url)
                    except (requests.RequestException, ValueError) as exc:
                        st.warning(f"Lookup недоступен: {exc}")
                    profile, notes = make_profile(meta)
                    new_routes, errors = build_routes(base, profile, points, [])
                invalidate()
                s.routes, s.route_points, s.routing_config = new_routes, points, [base, profile]
                s.profile_notes, s.route_errors, s.profile_text = notes, errors, profile
            except (requests.RequestException, ValueError) as exc:
                st.error(f"Расчёт не выполнен: {exc}. Ранее построенный маршрут, если есть, сохранён.")

    selected = 0
    route, audit = None, None
    if s.routes:
        selected = st.selectbox("Основной маршрут для аудита и GPX", list(range(len(s.routes))),
            format_func=lambda i: f"BRouter {s.routes[i]['alternative']} · {geodesic_length(s.routes[i]['coords'])/1000:.1f} км · {sum(d/1000/v for d,v,_,_ in route_segments(s.routes[i])[0]):.1f} ч хода")
        route = s.routes[selected]
        key = route["signature"] + "|" + overpass
        if key not in s.audits:
            bar = st.progress(0.0, text="Запуск OSM-аудита…")
            try:
                s.audits[key] = audit_route(route, overpass, bar.progress)
            except Exception as exc:
                # An audit failure never becomes a green/no-hazard result.
                s.audits[key] = {"warnings": [], "errors": [str(exc)], "complete": False,
                                 "at": datetime.now(timezone.utc).isoformat(), "sources": [], "count": 0}
            finally:
                bar.empty()
        audit = s.audits[key]
        if audit["complete"]:
            st.info(f"OSM-аудит завершён · объектов: {audit['count']} · отметок: {len(audit['warnings'])}. Это не подтверждение безопасности.")
        else:
            st.error("Аудит НЕПОЛНЫЙ — маршрут не проверен на всём протяжении.")
        with st.expander("Диагностика профиля и сервисов"):
            st.write("Профиль пешеходный с приоритетами trekking/gravel. BRouter минимизирует взвешенную стоимость, не гарантирует минимальное время; варианты могут совпадать и перекрываться.")
            for msg in s.get("profile_notes", []) + s.get("route_errors", []) + audit["errors"]:
                st.write(msg)
            st.caption("Полигональные болота проверяются отдельно: по границам коридора и содержащим областям с шагом 250 м; небольшие полностью неотмеченные объекты могут быть пропущены. Мост — тег и геометрия дороги, не водотока.")
            st.caption("Аудит UTC: " + audit["at"])
            st.download_button("Скачать использованный профиль .brf", s.get("profile_text", s.routing_config[1]), "anti_bog.brf", "text/plain")
        hazards = [w for w in audit["warnings"] if w["avoid"]]
        c1, c2 = st.columns(2)
        if c1.button("Обойти опасные узлы", disabled=not hazards, use_container_width=True):
            try:
                nogos = deduplicate_nogos(s.nogos, hazards)
                with st.spinner("Пересчёт с no-go 150 м…"):
                    new_routes, errors = build_routes(s.routing_config[0], s.routing_config[1], s.route_points, nogos)
                s.routes, s.nogos, s.route_errors = new_routes, nogos, errors
                st.rerun()  # New geometry is always audited again before export.
            except (requests.RequestException, ValueError) as exc:
                st.error(f"Обход не принят: {exc}. Предыдущий маршрут сохранён.")
        if c2.button("Повторить OSM-аудит", use_container_width=True):
            # Clear only this route's query cache entries, not other users' cached data.
            fwd, inv = local_projection(route["coords"])
            line = transform(fwd, LineString([c[:2] for c in route["coords"]]))
            for i in range(max(1, math.ceil(line.length/8000))):
                seg = substring(line, max(0, i*8000-60), min(line.length, (i+1)*8000+60))
                overpass_chunk.clear(corridor_query(list(transform(inv, seg).coords)), overpass)
            del s.audits[key]
            st.rerun()
        st.caption("Обход не гарантирует капитальный мост. Если граф не содержит подходящего перехода, сервис может отказать; новые опасности снова отмечаются.")

    st.subheader("3 · Карта и визуальная проверка")
    st.caption("Зелёная — выбранный маршрут · синяя — альтернативы · красный пунктир — ориентир А–Б. Тапните по карте, затем подтвердите добавление точки.")
    view = st_folium(make_map(points, s.routes, selected, audit, s.nogos, topo, heat if heat_ok else ""),
                     height=510, use_container_width=True,
                     returned_objects=["last_clicked"], key="route_map")
    if view and view.get("last_clicked"):
        tap = view["last_clicked"]
        s.last_tap = (float(tap["lat"]), float(tap["lng"]))
    if s.last_tap:
        st.caption(f"Последний тап: {s.last_tap[0]:.7f}, {s.last_tap[1]:.7f}")
        if st.button(f"Добавить выбранную точку → {role}"):
            try:
                set_point(s.last_tap, role)
                s.last_tap = None
                st.rerun()
            except ValueError as exc:
                st.error(str(exc))
    if ready:
        az, _, direct = GEOD.inv(s.start[1], s.start[0], s.finish[1], s.finish[0])
        c1, c2, c3 = st.columns(3)
        c1.metric("Птичка А–Б", f"{direct/1000:.2f} км")
        c2.metric("Истинный азимут", f"{az%360:.1f}°")
        grid_zone = st.selectbox("Зона для дирекционного угла", [5, 6], index=1)
        try:
            ax, ay = wgs_to_sk(*s.start, grid_zone)
            bx, by = wgs_to_sk(*s.finish, grid_zone)
            angle = math.degrees(math.atan2(by-ay, bx-ax)) % 360
            c3.metric("Дирекционный угол СК-42", f"{angle:.1f}°")
            with st.expander("Обратный пересчёт WGS-84 → СК-42"):
                converted = []
                for i, p in enumerate(points):
                    xx, yy = wgs_to_sk(*p, grid_zone)
                    converted.append({"Точка": "А" if i == 0 else "Б" if i == len(points)-1 else str(i),
                                      "Зона": grid_zone, "X, м": round(xx, 2), "Y, м": round(yy, 2)})
                st.dataframe(converted, hide_index=True, use_container_width=True)
        except (ValueError, RuntimeError) as exc:
            c3.write("СК-42: " + str(exc))
        st.caption("Азимут истинный, угол — от севера сетки выбранной зоны. Магнитное склонение не учтено. Вынос в соседнюю зону увеличивает искажения.")

    if not route:
        st.info("Добавьте А и Б, затем рассчитайте маршрут. Меню настроек доступно слева; на телефоне откройте боковую панель.")
        return
    if audit["warnings"]:
        with st.expander("4 · Найденные точки внимания", expanded=True):
            st.dataframe([{"км ≈": round(w["metres"]/1000, 2), "Отметка": w["name"],
                           "Основание": w["detail"], "OSM": w["osm"]} for w in audit["warnings"]],
                         hide_index=True, use_container_width=True)

    st.subheader("5 · Сигнал активности Strava")
    st.caption("Это доля длины с сигналом на разрешённой теплокарте, не вероятность проходимости и не число посетителей. Пустые/недоступные тайлы не равны «мёртвой» дороге.")
    hkey = route["signature"] + "|" + heat + f"|{threshold}|{heat_mode}"
    heat_requested = st.button("Повторить анализ теплокарты", disabled=not (heat and heat_ok))
    if heat and heat_ok and (hkey not in s.heat_results or heat_requested):
        bar = st.progress(0.0)
        try:
            s.heat_results[hkey] = heat_analysis(route["coords"], heat, threshold, mode=heat_mode, progress=bar.progress)
        except (requests.RequestException, ValueError, OSError) as exc:
            st.error(str(exc))
        finally:
            bar.empty()
    hr = s.heat_results.get(hkey)
    if hr:
        if hr["index"] is None:
            st.warning("Индекс: НЕТ ДАННЫХ. Получено 0% длины маршрута.")
        else:
            st.write(f"Сигнал на {hr['index']:.1f}% исследованной длины · данные получены для {hr['coverage']:.1f}% всего маршрута · активный сигнал: {hr['hot_km']:.2f} км.")
        if hr["errors"]:
            with st.expander("Недоступные тайлы"):
                st.write("\n".join(hr["errors"]))
    else:
        st.info("Индекс не вычислен. Задайте разрешённый XYZ-источник в настройках и запустите анализ.")

    st.subheader("6 · Нагрузка и экспорт")
    segments, coverage = route_segments(route)
    rows = [{"Вариант": "По птичке напрямик · только сценарий", **estimate([(direct, 2.0, 1.8, "Бездорожье")], body, load, grade, pauses, water_rate, reserve)},
            {"Вариант": "Выбранный обход BRouter", **estimate(segments, body, load, grade, pauses, water_rate, reserve)}]
    st.dataframe(rows, hide_index=True, use_container_width=True)
    st.caption(f"Теги покрытия получены для {coverage*100:.0f}% длины по сообщениям BRouter; неизвестное покрытие — 3 км/ч. grade1–2: 6.2; grade3: 5.2; тропы: 4.5; тяжёлое/птичка: 2.0 км/ч. Темп не гарантирован на 45–70 км с 25 кг.")
    with st.expander("Допущения Pandolf и воды"):
        st.code("M(W) = 1.5W + 2(W+L)(L/W)^2 + η(W+L)(1.5V² + 0.35VG)\nW,L: кг; V: м/с; G: уклон в процентах; M: ватт\nkcal = Σ M × seconds / 4184\nВода: общее время × выбранные л/ч × (1 + резерв)", language="text")
        st.write("Сценарные η: дорога 1.0; grade1–2 1.1; grade3/тропа 1.2; неизвестное 1.5; тяжёлое/птичка 1.8. Реальные грунт, снег, сырость и усталость могут резко увеличить расход. Рост в Pandolf не используется. Вода — отдельный плановый коэффициент, НЕ вывод из Pandolf и не медицинская рекомендация. Значения не учитывают температуру, индивидуальное потоотделение и электролиты.")
    acknowledge = st.checkbox("Я проверю переходы на местности; понимаю ограничения OSM и расчётов.")
    allow_partial = audit["complete"] or st.checkbox("Экспортировать НЕПОЛНО проверенный маршрут с явной пометкой в GPX")
    st.download_button("📥 СКАЧАТЬ БОЕВОЙ GPX ДЛЯ ALPINEQUEST",
                       export_gpx(route, s.route_points, audit, hr),
                       file_name="tactical_pathfinder.gpx", mime="application/gpx+xml",
                       disabled=not (acknowledge and allow_partial), type="primary", use_container_width=True)
    st.caption("В GPX: выбранный трек, отдельная птичка А–Б, исходные точки, предупреждения, засечки 5 км. Сначала сохраните офлайн-карту в AlpineQuest. Планировщик требует интернет; бесплатное облако может засыпать. Для личного доступа включите ограничение аудитории в настройках публикации.")


if __name__ == "__main__":
    main()
