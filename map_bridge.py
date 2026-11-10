"""Exactly-once handling of browser map messages; independent of Streamlit/GIS."""
from __future__ import annotations
import math
import re


def apply_map_event(state, event, set_point):
    """Consume before mutating; repeated Streamlit values are acknowledgements only.

    Called BEFORE widgets are constructed. No rerun calls, timers or network work.
    Each iframe has its own client id and monotonic sequence. Role is captured at
    the instant of the tap, not inferred from whichever widget later reruns.
    """
    if not isinstance(event, dict) or event.get('session') != state['map_session']:
        return False
    client, seq = event.get('client'), event.get('seq')
    if not isinstance(client, str) or not re.fullmatch(r'[A-Za-z0-9_-]{1,80}', client):
        return False
    if type(seq) is not int or not 0 < seq <= 2**53-1:
        return False
    seen = dict(state.get('map_seen', {}))
    if seq <= seen.get(client, 0):
        return False
    # ACK even a rejected point: a validation error must not become a retry loop.
    seen[client] = seq
    state['map_seen'] = seen
    try:
        action = event.get('action')
        if action not in ('point', 'scan'):
            raise ValueError('Неизвестное действие карты.')
        viewport = event.get('viewport') or {}
        center = viewport.get('center') or {}
        lat, lon = float(center['lat']), float(center['lng'])
        zoom = int(viewport['zoom'])
        if not (math.isfinite(lat) and math.isfinite(lon) and -85 <= lat <= 85 and -180 <= lon <= 180 and 0 <= zoom <= 20):
            raise ValueError('Некорректная область карты.')
        if action == 'point':
            role = event.get('role')
            if role not in ('А', 'Б', '+ точка') or role != state.get('tap_mode'):
                return False
            point = float(event['lat']), float(event['lng'])
            if not all(math.isfinite(v) for v in point):
                raise ValueError('Некорректные координаты точки.')
            set_point(point, role)
            state['pending_mode'] = ('Б' if role == 'А' and state.get('finish') is None
                                     else 'Осмотр' if role == 'Б' else role)
        state['map_center'], state['map_zoom'] = [lat, lon], zoom
        if isinstance(viewport.get('bounds'), dict):
            state['map_bounds'] = viewport['bounds']
        if action == 'scan':
            # Correlate the response to an explicit button press, not an old iframe.
            if event.get('request') == state.get('viewport_request'):
                state['scan_requested'] = True
                state['viewport_done'] = event['request']
        state['map_notice'] = None
        return True
    except (KeyError, TypeError, ValueError, OverflowError) as exc:
        state['map_notice'] = str(exc)[:240]
        return False
