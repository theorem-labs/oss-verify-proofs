# k2/

The relocation that made the plain / UBSan kit of this unit (`lib/`, `lib/U/`) from libreac/fuzz_decode's released lib.

The script, `k2_relocate.py` (sha256 967abd6019c3c487afc3a6e79363e50afce17d17b1d11be8de82eaede6e4a3eb), is not shipped
here because its source names internal tool paths; it is kept in the lane's history at commit e573857e92ac, path
`proofs/libdiginet/fuzz_decode/provenance/evidence/k2/k2_relocate.py`. It copies libreac/fuzz_decode's released plain /
UBSan lib (K1), moves every image value to this unit's binaries by symbol and offset (K2), adds second-donor libc walks
when linked (K3), and gives every copied file it changed one month-dated notice `(* Modified by Theorem Labs, YYYY-MM:
ported from ... *)`. Its output for this unit equals that of the previous version (52e5bc690855) byte for byte.

Run for this unit: `k2_relocate.py --month 2026-10 --project libdiginet --unit fuzz_decode --donor-ref
bf7779f81ed764787b77895d2f5c0db2627f33f3 --kit-ref 25e3d17bdb5059606131377a3722d585415ab5d6 --plain <fuzz_decode.plain
pin>:<unstripped twin> --ubsan <fuzz_decode.ubsan pin>:<unstripped twin> --out lib --work <dir> --git <hub> --pac
<port_addr_check 5033540ba83b> --decode-bin <libreac fuzz_decode pins> --donor-bin <second donors' pins>`. The donor
ref is libreac/fuzz_decode as released after PR #413; the kit ref limits the copied files to the plain / UBSan kit of
25e3d17bdb50 (the files added since are the ASan kit).

In the tables, `*` in a definition name stands for a project-internal prefix removed from this evidence; the kit
file carries the full name at the line given (e.g. `lib/Reusable/YH03.v:44`).
