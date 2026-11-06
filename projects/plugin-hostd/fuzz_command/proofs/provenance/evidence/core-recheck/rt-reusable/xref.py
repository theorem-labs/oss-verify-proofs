"""Addresses formed by auipc + (addi | load | store) pairs inside a code range of an image (rv64, no compressed
instructions: the images are built without C)."""


def sx(v, bits):
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def formed(img, lo, nwords, window=6):
    """[(pc_of_use, target, kind)] for every auipc rd at pc in [lo, lo+4*nwords) followed within WINDOW words by an
    I-type addi/load or S-type store whose base register is rd (rd not redefined in between)."""
    out = []
    words = [img.word(lo + 4 * i, 4) for i in range(nwords)]
    for i, w in enumerate(words):
        if w is None or (w & 0x7f) != 0x17:
            continue
        rd = (w >> 7) & 31
        hi = sx(w & 0xfffff000, 32)
        pc = lo + 4 * i
        for j in range(i + 1, min(i + 1 + window, len(words))):
            u = words[j]
            if u is None:
                break
            op, rs1, f3 = u & 0x7f, (u >> 15) & 31, (u >> 12) & 7
            if op in (0x13, 0x03, 0x67) and rs1 == rd:
                kind = {0x13: 'addi', 0x03: 'load', 0x67: 'jalr'}[op]
                if op == 0x13 and f3 != 0:
                    continue
                out.append((lo + 4 * j, pc + hi + sx(u >> 20, 12), kind))
            elif op == 0x23 and rs1 == rd:
                imm = ((u >> 25) << 5) | ((u >> 7) & 31)
                out.append((lo + 4 * j, pc + hi + sx(imm, 12), 'store'))
            if op not in (0x23, 0x63) and ((u >> 7) & 31) == rd and j > i:
                break  # rd redefined
    return out
