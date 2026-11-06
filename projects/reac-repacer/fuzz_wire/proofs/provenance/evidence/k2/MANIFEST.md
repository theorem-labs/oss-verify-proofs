# k2/

| file | role |
|---|---|
| k2_relocate.py | the script of record: copies libreac/fuzz_decode's released lib (K1), moves every image value to this unit's binaries (K2), adds second-donor libc walks when linked (K3); its docstring states each step and control |
| k2-values.tsv | every value it changed: file, line, old, new, how (and each file it did not copy, with the reason) |
| k2-conflicts.tsv | hex values the address tool also classes NON-ADDRESS, left to the decimal table (see gate/GATE.md) |
| k2-cells.tsv | the 100 code cells set by symbol or by measurement (YH03's): file, line, value, rule, measurement |

k2_relocate.py is the version of record of the relocation script (sha256 9bb41757a964acc926625b529b6522cd2d39846323cce1cdac6757ca722d3415),
run on this unit's recorded inputs (the same plain and UBSan images, the same decode release and donor binaries, the same
address tool) to regenerate every output here and the lib files it writes. The earlier run for this unit used the script with
sha256 df0e51712933b707883822ce110208a9cf852cad897eeb6c8ccfbd8319e76bcb; its value table (8f49e4dc71b5, 1595 rows) is kept in
the internal record of the series. Against that run's outputs: k2-conflicts.tsv (612d1d3b02f0) is byte-equal; k2-values.tsv
(aba4b0e45e0e, 1637 rows) has 1591 of the earlier rows, row for row with the same (file, old, new), and 129 of them differ only
in form: 96, the YH03 cell rows, in their line, which was 0, and their how column, and 33, files it did not copy, in their
reason, reworded. 42 rows are new: the values of the K3 memmove walk (Prog/memmove.v, Prog/memmove_c.v and their U/ copies,
second donor libreac/fuzz_pcap), which the earlier table did not list. The other 4 earlier rows, YH03's src0_A_stdio_read and
src0_A_stdio_seek in both copies, gave the address tool's mapped values (0x16584 / 0x1682c plain, 0x16998 / 0x16c40 UBSan);
this run sets src0_A_stdio_read to 0 (no such symbol in this image, measured) and src0_A_stdio_seek by name to __stdio_seek
(0x16858 plain, 0x16c6c UBSan), which are the values this unit's released lib holds. k2-cells.tsv (4121833d359c) is new.
Of the 1112 lib files it writes, 1110 are byte-equal to this unit's released lib; the other two, lib/Reusable/YH03.v and
lib/U/Reusable/YH03.v, differ only at line 29, where the trailing comment on src0_A_stdio_read moved into k2-cells.tsv (that
row carries its text). With comments stripped, their code is byte-equal to the released files.

## The reason string of step (f), corrected

The run above used the script with sha256 93d0a778f7f4ac088d6e29ef38ac3c52fb0046d874bc4641263d63a7380e172b, whose step (f)
labelled every row it wrote for calloc `no calloc linked`. That label is false: step (f) tests whether the image's symbol
table holds a symbol named exactly `calloc` (`U.one('calloc')`), and each of this unit's plain and UBSan images links
musl's `__libc_calloc` (312 bytes, at 0x14348 plain and 0x1475c UBSan) while holding no symbol named `calloc`. The script of
record here changes only those five label strings, to `no symbol named calloc`. Re-run on the same inputs as above (the
four images by their pins, decode's pins from the share mirror, fuzz_pcap's second-donor pins, port_addr_check
5033540ba83b): first the earlier script, as a control, which reproduced all three recorded tables byte for byte
(k2-values.tsv aba4b0e45e0e, k2-conflicts.tsv 612d1d3b02f0, k2-cells.tsv 4121833d359c); then this script, whose
k2-values.tsv (185850ca360b) differs from the control's in exactly 26 rows, each only in its reason column
(`no calloc linked` -> `no symbol named calloc`, two of them with their `x2` count kept), while k2-conflicts.tsv,
k2-cells.tsv and every lib file it writes are byte-equal to the control's. The notice text step (f) writes into lib files
is unchanged, so the comparison with the released lib above still holds; this unit's own shipped lib states the measured
calloc fact in those notices.

The same step also drops R_memchr.v's unused module R_memcmp when the image has no symbol named `memcmp`, and its
strings said `the unit links no memcmp` / `no memcmp linked`. For this unit that step does not fire: the plain and UBSan
images hold a symbol named `memcmp` (FUNC, 48 bytes, at 0x1b2c4 plain and 0x1b6d8 UBSan), so no row and no lib
file carries those words. The script of record changes those strings, and step (f)'s description in its docstring, to
say what the step tests (`no symbol named memcmp`, `no symbol named calloc`); re-run on the same inputs, its three tables
and every lib file it writes are byte-equal to the run above.
