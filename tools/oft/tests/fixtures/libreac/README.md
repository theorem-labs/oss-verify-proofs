# The libreac fixture of test_classify.py

Two symbol facts of libreac's `fuzz_pcap` plain build, cut to six functions. `fuzz_pcap-1.8.0.plain.tsv` is of the
binary that `projects/libreac/fuzz_pcap/harness.yaml` pinned for libreac 1.8.0 (commit `f37a23c5`), and
`fuzz_pcap-1.9.0.plain.tsv` of the binary it pins for libreac 1.9.0 (commit `d16f3f4e`).  The `sha256=` header of each
fact is the SHA-256 of its binary:

| fact | binary | bytes | sha256 |
|---|---|---|---|
| `fuzz_pcap-1.8.0.plain.tsv` | `fuzz_pcap.plain` of libreac 1.8.0 | 49456 | `6f9893e21aad66635e7ab41cca47835cd7066ed285ece06f267fbc1626d382e8` |
| `fuzz_pcap-1.9.0.plain.tsv` | `fuzz_pcap.plain` of libreac 1.9.0 | 49336 | `1e8e7da32456ca11f5e70cba9413adf96bbeb09fb14d1c68e2a3c29a6cb0de01` |

The binaries are stripped, and their unstripped twins were not kept, so `oft symbols` cannot read them.  A measurement
of the two builds found each function's address and size in the code and named it from the source; its table,
`pcap-plain-functions.tsv`, has a row for each function, with the columns `class`, `name` (a function's aliases joined
by `,`), `contract`, `addr_before`, `size_before`, `addr_after` and `size_after`.  [`make.py`](make.py) takes the rows
of six functions from it, cuts each function's bytes out of each binary's `.text` with `elf.Elf`, and hashes them as
`symbols.read` does, exact and through `symbols.mask` with the binary's Image (`symbols.build_image`); with no symbol
table it knows no function that never returns.  It reads no line table, so the lines of every function are `-`,
and no symbol table, so every row is a function (kind `func`) and the facts list no data object.
Run in `tools/`, with the 1.8.0 binary, the 1.9.0 binary and the table:

```sh
PYTHONPATH=. python3 -B oft/tests/fixtures/libreac/make.py BEFORE AFTER pcap-plain-functions.tsv
```

The six functions are `main`, `libreac_fuzz_fopen`, `pcap_source_open`, `pcap_source_next`, `pcap_source_close` and
musl's `libc_start_init` with its alias `__libc_start_init`: seven names.  libreac 1.9.0 changed `pcap_source_next`
(788 bytes, then 732), and every other function moved: the bytes of `main`, `libreac_fuzz_fopen` and
`pcap_source_open` differ only in their address immediates, and those of `pcap_source_close` and `libc_start_init`
are the same.
