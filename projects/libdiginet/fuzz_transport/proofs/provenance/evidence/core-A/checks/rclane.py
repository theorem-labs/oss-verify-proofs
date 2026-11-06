#!/usr/bin/env python3
"""rclane.py WORK OUT.full.tsv.gz [--plant OUT.plant.full.tsv.gz]: the lane's own report of every numeral of the
relocated core in port_addr_check's FULL-TSV columns, for roundconst-gate v2 32b39f3b34e9 with --all-verdicts (its
README, 'Input': "convert your report into those columns and pass --all-verdicts"). Read-only.

One row per numeral of a code line of WORK/stage-out/{A,Reusable}/*.v aligned with its donor token in WORK/stage
(decval.py's alignment, numerals masked); comment numerals and instruction words / decoded fields are left out (their
roles are not counts). Columns: verdict (LANE-KEPT / LANE-MOVED), kernel_checked (no), image (A), src_file, src_line
(stage/), dst_file, dst_line (stage-out/), sentence (the line, 80 chars), idx, kind (hex / dec), src_value, dst_value (hex).

--plant P: also write P, the same rows with the two planted controls of roundconst-A.sh applied (a kept donor value
written back in place of the port's): PR1 A/AB1w.v tfib_at_rw_len (0x55c000, the donor's rw_len), and PR2 the first
moved row below 0x100 (in file order) whose donor value roundconst calls MISMATCH when kept (chosen by roundconst-A.sh
and passed as --pr2 FILE:LINE:IDX).
"""
import gzip
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import decval as DV  # noqa: E402


def lane_rows(work):
    cfg = DV.setup([work])
    for t, dp in DV.file_list(cfg):
        d, c, pr = DV.align(dp, os.path.join(cfg["core"], t))
        depth = 0
        for j, line in enumerate(c):
            incom = depth > 0
            depth = max(0, depth + line.count("(*") - line.count("*)"))
            role = DV.role(line)
            if incom or role in ("comment", "fetch", "word", "decode") or j not in pr:
                continue
            tk, dtk = DV.toks(line), DV.toks(d[pr[j]])
            if not tk or len(tk) != len(dtk):
                continue
            for i, (s, ds) in enumerate(zip(tk, dtk)):
                sv, tv = DV.val(ds), DV.val(s)
                yield ["LANE-KEPT" if sv == tv else "LANE-MOVED", "no", "A", t, str(pr[j] + 1), t, str(j + 1),
                       line.strip()[:80].replace("\t", " "), str(i), "hex" if s.startswith("0x") else "dec", hex(sv), hex(tv)]


def main():
    a = sys.argv[1:]
    work, out = a[0], a[1]
    plant = a[a.index("--plant") + 1] if "--plant" in a else None
    pr2 = a[a.index("--pr2") + 1] if "--pr2" in a else None
    rows = list(lane_rows(work))
    hdr = "verdict\tkernel_checked\timage\tsrc_file\tsrc_line\tdst_file\tdst_line\tsentence\tidx\tkind\tsrc_value\tdst_value\n"
    with gzip.open(out, "wt") as f:
        f.write(hdr)
        for r in rows:
            f.write("\t".join(r) + "\n")
    print("rclane: %d rows (%d kept, %d moved) -> %s" % (len(rows), sum(r[0] == "LANE-KEPT" for r in rows),
                                                        sum(r[0] == "LANE-MOVED" for r in rows), out))
    synth = lambda v: ["LANE-KEPT", "no", "A", "SYNTH", str(v), "SYNTH", str(v), "synthetic kept donor value %d" % v, "0",
                       "dec", hex(v), hex(v)]
    if plant:
        done = []
        with gzip.open(plant, "wt") as f:
            f.write(hdr)
            for r in rows:
                r = list(r)
                key = "%s:%s:%s" % (r[5], r[6], r[8])
                if (r[5] == "A/AB1w.v" and r[7].startswith("Definition tfib_at_rw_len") and r[0] == "LANE-MOVED") or key == pr2:
                    done.append("%s %s -> %s (kept donor value)" % (key, r[11], r[10]))
                    r[0], r[11] = "LANE-KEPT", r[10]
                f.write("\t".join(r) + "\n")
            if pr2 and pr2.startswith("SYNTH:"):
                v = int(pr2.split(":")[1])
                f.write("\t".join(synth(v)) + "\n")
                done.append("%s: a synthetic row, the kept donor value %d (no core position: every moved row below 0x100 "
                            "is SAME when kept)" % (pr2, v))
        print("rclane: plants: %s" % "; ".join(done))
    if "--low-moved" in a:
        # the moved rows below 0x100, written as kept (roundconst-A.sh picks PR2 from roundconst's verdict on these)
        p = a[a.index("--low-moved") + 1]
        with gzip.open(p, "wt") as f:
            f.write(hdr)
            for r in rows:
                if r[0] == "LANE-MOVED" and int(r[10], 16) < 0x100:
                    r = list(r)
                    r[0], r[11] = "LANE-KEPT", r[10]
                    f.write("\t".join(r) + "\n")
    if "--probe" in a:
        # one synthetic kept row per value 2..255 (roundconst-A.sh picks a NAMED donor quantity below 0x100 the gate flags)
        with gzip.open(a[a.index("--probe") + 1], "wt") as f:
            f.write(hdr)
            for v in range(2, 256):
                f.write("\t".join(synth(v)) + "\n")

if __name__ == "__main__":
    main()
