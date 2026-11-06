#!/usr/bin/env python3
"""dphash.py (the relink kit's tool, with hash_trace and D_TAB_WORDS = YG0f.v:222 d_tab_words added; this copy differs
from dphash.py 7eae670c5b27 in this docstring only).  PC0 [RAS] : the StackDepot murmur hash DPN.hashz (AN/Dp.v) of a 1- or 2-frame trace and its bucket cell  TAB + 4 * (H mod 2^20)."""
import sys
M64 = (1 << 64) - 1
MM = 0xc6a4a7935bd1e995; SEED = 0x9747b28c9747b28c; C8 = 0x35253c9ade8f4ca8
def mix(h, k):
    k1 = (k * MM) & M64; k2 = (k1 >> 47) ^ k1; k3 = (k2 * MM) & M64
    return ((k3 ^ h) * MM) & M64
def fin(h):
    a1 = 0; a1 = (a1 >> 47) ^ a1; a1 = (a1 * MM) & M64
    a1 = ((a1 ^ h) * MM) & M64
    a1 = (a1 >> 47) ^ a1; a0 = (a1 * MM) & M64
    return (a0 >> 47) ^ a0
D_TAB_WORDS = 2 ** 20
def hash_trace(t):
    return hashz(list(t))
def hashz(ws):
    h = ((len(ws) * C8) & M64) ^ SEED
    for w in ws: h = mix(h, w)
    return fin(h)
if __name__ == '__main__':
    tab = 0x183b18
    assert hashz([0x53fec, 0x81618]) == 3165658969234837200 and hashz([0x53fec]) == 12270556283911244715
    assert tab + 4 * (hashz([0x53fec, 0x81618]) % 2 ** 20) == 3044952 and tab + 4 * (hashz([0x53fec]) % 2 ** 20) == 3566020
    print('old constants reproduced')
    for pcs, tabn in (([0x5d9b0, 0x8b6ac], 0x1af258), ([0x5d9b0], 0x1af258)):
        H = hashz(pcs); print([hex(p) for p in pcs], 'H =', H, 'cell =', tabn + 4 * (H % 2 ** 20), hex(tabn + 4 * (H % 2 ** 20)))
