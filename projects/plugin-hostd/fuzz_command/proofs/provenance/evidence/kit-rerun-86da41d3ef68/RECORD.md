# Code-equality claims of plugin-hostd/fuzz_command, measured again with cmpkit 86da41d3ef68

## What this record is

Comments in this unit's proofs say that two copies of code are the same: "word for word modulo pc-relative fields",
"code equal modulo pc-relative fields", "the same code", "instruction for instruction", "B's instruction stream is
A's with only the pc-relative offsets changed". Most of these claims were made with comparison tools that are now
known to be faulty (a byte comparer of the superseded bytecmp class, bytecmp 7daa0e2a03d9, repin_check 768e33f1f425,
an elfdis.py listing compare that masks every immediate, the masking comparers rvelf.py / imgmap.py / bonly.py /
cmpfn.py, a masked-key difflib map). This record measures every claim again with the comparison kit of record,
cmpkit 86da41d3ef68, and gives the verdict per claim.

The kit id is the first 12 hex digits of the sha256 of its SHA256SUMS
(86da41d3ef68abf071a843e599786e5eb0a6ed77c4a6b6eb645e7498bffbee60). Its members (sha256):

| member | sha256 |
|---|---|
| ambiscan.py | `9f61b4cee42207e6ae77f33c6ca2d9a9b8f938c38cff50b8c71c057b1e955d8d` |
| bytecmp-1480ca2faea0.py | `1480ca2faea075e866800faab4e18aea5fb4a96dcea17ef1fe8981f1bdd0f98f` |
| closure_strict3.py | `a98d2b3e88574d09d4aee478ba4fed060a3c1577e2229f47affb116c3ccded4e` |
| drvcmp.py | `4d70e90bc1fa4d70fe1ea53e0208593ee5e87ff53c3b80c8b767ffdff4eaa3a6` |
| jtcheck.py | `8b0ea3862423e3941fd9d70ccc9bcb89cfd89b824fa348140e168880c9745fb7` |
| luiscan.py | `9ae61e4a0e018677862566a53e3b9a6c0f1a89c9f71a9012bf1893f8ec93edad` |
| paircl.py | `926a9a88afcdc233aa5cd0451a0a8965217e1e08dbc09ffb4e7e8c3bd61017e1` |
| repin_check.py | `e6883477399df80d35e1810dd93f2d5c85aa4d07cb16fbc887ad625851d98a66` |
| strictcmp3.py | `65688e94214a74664ffa83a21c283412a64b81f8a7eaa40f970a91f4eb1319b7` |

`kitrange.py` (this directory) calls the kit's own compare (`strictcmp3.tcmp` and `strictcmp3.verdict`, the code
behind `strictcmp3.py cmp`) by address. It is used where `strictcmp3.py cmp` cannot pair the code: two functions of
one image, a part of a function, or the parts before and after an inserted word. It checks the kit id and every
member's sha256 before it runs, and it lists the words that bytecmp counts as real differences.

## Inventory of the claims (shipped tree 781f46bc05cd, series base plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record))

Lines of `proofs/plugin-hostd/fuzz_command` matched: `modulo pc-relative` 39 lines in 26 files; `same code` 9 lines;
`byte for byte` or `byte-identical` 3 lines; `word for word` 125 lines in 104 files; other code-equality wordings
(`instruction for instruction`, `only the pc-relative offsets changed`, `only in pc-relative fields`, `same
instructions`, `A's code`, `same bytes as`, `pc-relative immediates`, `B's code is A's`, `A's 26 instructions`) 32
lines. Together 176 distinct lines.

- 103 lines are not code-equality claims (class N): 86 say that a Coq statement, contract or hypothesis is copied
  word for word, 2 more are Coq or proof text copied word for word, 2 are memory claims, 1 is a statement file that
  is byte-identical, 4 describe A's code with no equality claim, 7 state that B differs from A (registers,
  frame, new checks), 1 names another walk of the same call.
- 73 lines are code-equality claims (`claims.tsv`, ids C00 to C72). Their makers: a faulty comparer (class F) 57,
  another method (class O: listing diffs, hand reads of both images, an instruction alignment) 10, not recorded 6.

## Images

Each claim is measured on the unstripped twins of the pinned images (`images.tsv`). `drvcmp.py twins` proves each
twin (`twins.out`): the PT_LOAD layout is equal and the only differing loadable bytes are in the ELF header
[0x10000, 0x10040) and `.note.gnu.build-id` [0x102a8, 0x102cc). The pins are the release builds that each unit's
`harness.yaml` names.

## Commands

Run from one directory that holds the kit in `kit/` (exactly its nine files and SHA256SUMS; `sha256sum -c
SHA256SUMS` gives 9 x OK) and the images in `img/` (each pin `<name>` and its twin `<name>.debug`):

```sh
for p in fuzz_command.asan fuzz_command.asan-ubsan fuzz_grant.asan fuzz_disco.asan fuzz_reply.asan \
         fuzz_reply.asan-ubsan cgif_file_fuzzer.asan cgif_file_fuzzer.asan-ubsan; do
  python3 kit/drvcmp.py twins img/$p img/$p.debug; done > twins.out
A=img/fuzz_command.asan.debug; B=img/fuzz_command.asan-ubsan.debug
python3 kit/strictcmp3.py cmp ___interceptor_strcmp,__interceptor_trampoline_strcmp,__sanitizer_weak_hook_strcmp,_ZN6__asan18TryAsanInitFromRtlEv,__asan_region_is_poisoned,_ZN11__sanitizer11mem_is_zeroEPKcm G=img/fuzz_grant.asan.debug A=$A B=$B G:A,G:B > g1-strcmp-grant.cmp.tsv
python3 kit/strictcmp3.py cmp ___interceptor_strcmp,__interceptor_trampoline_strcmp,__sanitizer_weak_hook_strcmp,_ZN6__asan18TryAsanInitFromRtlEv,__asan_region_is_poisoned,___interceptor_malloc,_ZN11__sanitizer18BufferedStackTrace10UnwindImplEmmPvbj,_ZN11__sanitizer18BufferedStackTrace10UnwindFastEmmmmj,___interceptor_strdup,memcpy,___interceptor_strndup,__interceptor_trampoline_strndup,__asan_memcpy,__asan_memset,memset,___interceptor_strcspn,__interceptor_trampoline_strcspn,strcspn,strtok_r A=$A B=$B B:A > g2-rt.cmp.tsv
python3 kit/strictcmp3.py cmp reply,verb_is,rec_clear,rec_code_declared,rec_shape_of,is_instance_verb,number,answer,check_refusal,send_message A=$A B=$B B:A > g2-prog.cmp.tsv
python3 kitrange.py kit g2-prog-ranges.spec.tsv > g2-prog-ranges.kitrange.tsv
python3 kitrange.py kit g2-answer-settle.spec.tsv > g2-answer-settle.kitrange.tsv
python3 kitrange.py kit g2-verbs-receive.spec.tsv > g2-verbs-receive.kitrange.tsv
python3 kit/strictcmp3.py cmp __asan_stack_malloc_3,_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE,___interceptor___tls_get_addr,__tls_get_addr,_ZN6__asan16GetCurrentThreadEv,_ZN6__asan10AsanTSDGetEv,__pthread_getspecific,_ZN11__sanitizer20DTLS_on_tls_get_addrEPvS0_mm,_ZN6__asanL11MemToShadowEm{asan_fake_stack.cpp} D=img/fuzz_disco.asan.debug A=$A D:A > g3-sm3-disco.cmp.tsv
python3 kit/strictcmp3.py cmp __asan_memcpy,__asan_region_is_poisoned,memcpy,__asan_memset,memset C=img/cgif_file_fuzzer.asan.debug CB=img/cgif_file_fuzzer.asan-ubsan.debug A=$A B=$B C:A,C:B,CB:B > g4-cgif.cmp.tsv
python3 kit/strictcmp3.py cmp _ZL13printf_commonPvPKcS_ R=img/fuzz_reply.asan.debug RB=img/fuzz_reply.asan-ubsan.debug A=$A B=$B R:A,RB:B,R:B > g5-printf-common.cmp.tsv
python3 kit/strictcmp3.py cmp memchr A=$A B=$B B:A > g9-memchr.cmp.tsv
python3 kit/luiscan.py --all --fns <the items of the runs above for that image> img/<image>.debug > luiscan-<image>.tsv
python3 kit/ambiscan.py <X twin> <Y twin> <the earlier compare outputs> > amb-<pair>.tsv
```

Every command exited 0. The C-string rule is ON (the default).

## Verdicts

Per claim: `claims.tsv` (what the re-run compares, the kit output rows, the kit verdict, the settled verdict).
Settled rows, side by side with the kit verdict: `settled.tsv` (S1 to S8).

- **Verdict changed, 1 claim: lib/B/Prog/send_message_k.v:5** (C34, class F). The comment says that B's instruction
  stream is A's "with only the pc-relative offsets changed (the program points keep their offsets from the entry)".
  The kit says SIZE: send_message is 620 bytes in fuzz_command.asan-ubsan and 616 bytes in fuzz_command.asan
  (g2-prog.cmp.tsv). B has one added word, `unimp` (0xc0001073) at 0x86e48 after `jal abort` (0x86e44). The
  two-part compare (g2-prog-ranges.kitrange.tsv, rows `send_message[+0..+0x250)` and
  `send_message[B+0x254..end|A+0x250..end]`, spec in g2-prog-ranges.spec.tsv) gives DIFFERENT with 1 real word in
  each part, and each real word is the same branch with its offset moved by the inserted word (S5). So the 6 words
  after 0x86e48 are 4 bytes later in B, and "the program points keep their offsets from the entry" is false after
  0x86e48. By use (`send_message-byuse.tsv`, all 72 address literals and entry offsets in
  lib/B/Prog/send_message*.v): the largest is +0x250 (0x86e48); the walk's program points end at SM_RET_FREE =
  +0x170 (0x86d68); the only literals at or after 0x86e40 are the not-taken branch target 0x86e40
  (send_message_s2.v:46, a comment) and 0x86e44 / 0x86e48 in send_message_c.v:33, the comment that names the
  unimp. No statement and no walk step depends on the false part. The sibling claim send_message_c.v:34 already
  names the unimp and is true.
- **Same, 68 claims** (56 of class F, 10 of class O, 2 not recorded): every function, range and pair the claims
  name is EQUAL or EQUAL-mod-pcrel with target-differ 0, or settled to that by a named measurement (S1 to S5, S8),
  or differs in exactly the words the comment names (S5). One of them (C45, lib/B/Rt/RtDStrdupM.v:6) is in the
  shipped tree only; the series removes the file.
- **A wrong address in a true claim: lib/B/RT_pf_Tbl.v:9** (C40). The code is the same as fuzz_reply.asan's
  printf_common, but that function starts at 0x45964, not at 0x459b0 (S6).
- **Not certified, 4 claims** (C00, C18, C26, C36; makers not recorded): the openssl/echconfiglist_parser image of
  lib/A/Bz/A/I_strspnw.v:30-31 and lib/B/Bz/A/I_strspnw.v:30-31 was not available with a symbol table (no pin, no
  twin); the template of lib/B/Prog/rec_clear.v:9 and lib/B/Prog/sup_worker_env.v:29 is an earlier
  fuzz_command.asan-ubsan build (sha256 3e5129c8d0a058b98f4ff0e23e16ebbd7e74d907e5a13814e57e5d04ba9ea4f9) with no
  unstripped twin. The kit needs `.symtab` on both sides, so these claims stay unmeasured. lib/B/Bz/A/I_strspnw.v:30
  also gives the donor's addresses wrong (body 0x1aea48, stub 0x1ad368; the donor's N6_strspn.v has
  ASTRSPN_ICPT 0x1aeec8 and ASTRSPN_STUB 0x1ad7e8).

## Exposure scans and names

- luiscan 9ae61e4a0e01 (`luiscan-*.tsv`): exposure 0, insec 0, memfed 0 and luiconst 0 for every compared function
  in all eight images.
- The kit's lui fail-open limit (a lui value in a section that feeds logical ALU ops and then a load / store base
  settles as `lui-const (dataflow)` and prints EQUAL): no output of this record has a `lui-const` acceptance, and
  no lui value of a compared function (or lui + addi / addiw value) lies in an allocated section of any of the
  eight images. `lui-checks.tsv` lists every lui word with its uses and the hand check.
- ambiscan 9f61b4cee422 over the earlier compare outputs (`amb-*.tsv`): 0 ambiguous hits. The fuzz_grant outputs
  had no line ambiscan reads as a by-name compare, so `names.tsv` settles the names directly: of the 50 items
  compared, only `_ZN6__asanL11MemToShadowEm` has several copies (5 in each image); it was compared as
  `_ZN6__asanL11MemToShadowEm{asan_fake_stack.cpp}`, which names exactly the walked copy (fuzz_command.asan
  0x40410, fuzz_disco.asan 0x3dca4).
- The kit's second lui fail-open (two or more lui values joined by add / sub / sh*add into a load / store / jalr /
  AMO base are not compared as an address, and luiscan's memfed count does not see them): `luipairs.py` (this
  directory) runs a may-dataflow over the control-flow graph of every function behind an EQUAL or EQUAL-mod-pcrel
  verdict of this record, on both sides, and reads the base register of every load, store, jalr and AMO. 108 function
  bodies, 125 bases that carry a lui value, **0 with two or more** (`lui-pairs.tsv`). Every value that reaches a base
  is 0x1000 or -0x1000, the page constant of the frame arithmetic (the chain is `lui; sub sp` or an alignment mask),
  so each such base is a stack address and names no image object; neither value lies in an allocated section of any
  of the eight images. The two sides of all 82 compared pairs have the same sequence of base sites
  (`lui-pairs-sides.tsv`). None of the bodies holds a 2-byte parcel. The dataflow never drops a path, so the empty
  result is a proof, not a sample.
- No row has a `lui-in-section` difference, a NAME-ONLY acceptance, an UNREADABLE or UNMEASURED word left
  unsettled, or a switch table (every `unmeasured` count is 0 apart from the answer range end of S4).
- The C-string acceptances (one CSTR row each in the outputs) are interceptor names given to the report path,
  assertion file names and condition texts given to the CHECK failure path, flag names and descriptions given to
  the flag parser, ASan frame descriptions, printf_common's conversion-character sets read with strchr, and warning
  formats given to Printf: each consumer reads its argument as a C string.

## The kit's known fail-opens: hand traces (fail-open-traces.tsv)

cmpkit 86da41d3ef68 stays the kit of record with known fail-opens (the tool registry README at README.md (sha256 5cab2211832e; internal record)): it does
not judge a lui-derived address that reaches a load / store / jalr / AMO base through the load / store immediate, an
addi / addiw chain, ori / xori / slli, a stack spill, an FP move or a CSR round trip, a jump-table arm reached only by
fall-through, an in-function callee or c.lui, and it does not see addresses built without lui. An EQUAL* verdict on a
function where an address value reaches a base through one of these shapes needs a hand trace that names the target
on both sides.

`failopen.py` (this directory, sha256 `1c4ca02b446dcb3c36107f754c1fa4b1798ca2ae427dc51710392160fda48413`) finds the
sites and writes `fail-open-traces.tsv`, one row per site pair: the claims, the compare row, the function and the
site on each side, the shapes, the target on each side, how it was traced, the verdict. Run from the directory of the
commands above:

```sh
python3 failopen.py --selftest
python3 failopen.py kit img fail-open-traces.tsv g1-strcmp-grant.cmp.tsv g2-rt.cmp.tsv g2-prog.cmp.tsv \
  g2-prog-ranges.kitrange.tsv g2-answer-settle.kitrange.tsv g2-verbs-receive.kitrange.tsv g3-sm3-disco.cmp.tsv \
  g4-cgif.cmp.tsv g5-printf-common.cmp.tsv g9-memchr.cmp.tsv
```

Both exit 0. The self-test plants one function per shape of the list (load / store immediate, addi chain, ori / xori
/ slli, stack spill, FP move, CSR round trip, jump-table arm reached by fall-through, in-function callee, c.lui, an
address built with li and slli); each one gives a site with its shape (10 of 10).

Method (the script's docstring has it in full). A may-dataflow over each function's control-flow graph, on both sides,
carries every constant (lui, c.lui, an OP-IMM word on x0, a load from a .got slot or a constant-pool word, and an
auipc value past the pair the kit judges) through registers, stack slots, other memory cells with a known address, FP
registers and CSRs, with its exact value and the shapes it goes through. A site is a base that may carry a value of
magnitude 0x10000 or more (the lowest PT_LOAD address of every image), a value that the dataflow does not know
exactly, or one exact constant. It leaves out only the edge after a call that does not return (abort, the
`__asan_report_*` calls), the edge after unimp, the edges of the 5 indirect jumps (each a tail call through a REAL()
function pointer with sp back at its entry value) and the tokens that a branch against x0 contradicts.

Counts for the 62 claims whose kit verdict is EQUAL* and whose settled verdict is same:

- Claims checked: 62. Their 62 compare rows have 92 function bodies behind them, both sides (108 bodies scanned in
  all). 2-byte parcels: 0, so c.lui: 0. In-function calls: 0. Allocator::Allocate is not one of the bodies, so its
  five immediate-case rows per asan image are not part of this record.
- Site pairs inside the compared ranges: 207 (263 distinct words). Per shape (one pair can have several): built
  without lui 195 (189 from a .got slot through the load / store immediate; 6 from the constant-pool word
  0xaaaaaaaaaaaaaaaa, printf_common's directive fill, through a stack spill); immediate 189; ori / xori / slli 15;
  stack spill 6; addi chain 11 and auipc pair 12 (auipc values, not in the list: TryAsanInitFromRtl's lr.w / sc.w on
  the word of asan_inited, and the rec_codes and g_shapes table walks); FP move 0; CSR 0; jump-table arm 0;
  in-function callee 0; c.lui 0. Sites where a lui value is the address: 0 (the only lui words whose values reach a
  base are 0x1000 and -0x1000, frame and page constants).
- Sites traced: 207 of 207. 189 from the bytes of the .got slot (the slot, the value in it, the symbol and offset of
  value + immediate on each side); 18 by hand, after reading both listings (the trace is in the row).
- Verdicts changed: 0. Every pair names the same target on both sides: the same symbol and offset, or the ASan shadow
  byte of the same object.
- 439 bases carry only constants below 0x10000 in magnitude; they are counted, not traced (no such value names an
  image object).

The 7 claims whose kit verdict is DIFFERENT or SIZE (C01, C02, C22, C23, C33, C34, C35; settled by S5, outside the
rule) were traced too: 42 site pairs, 0 targets that differ (the rows after those of the 62).

## The earlier compare outputs that ambiscan read

They hold host paths, so they are not in this directory; each is named here by its sha256.

| scan | earlier output (what it compared) | sha256 |
|---|---|---|
| amb-intrin.tsv | cgif_file_fuzzer.asan vs fuzz_command.asan: __asan_memcpy, __asan_memset, region_is_poisoned, memcpy, memset | `801a69fe546ab0dd184da88daccfa111c4abd204f9f6cf65b977a5cd3d8399ed` |
| amb-grant.tsv | fuzz_grant.asan vs fuzz_command.asan: the strcmp interceptor and its callees | `e96e5551b5fcf7794647c42c5a7034a025e1df7c57927f7bdbdde84b006d4762` |
| amb-grant.tsv | fuzz_grant.asan vs fuzz_command.asan: the numeral audit of the strcmp files | `28f45ada570de4686623f9a92325ecb5cf40bbd1382a0deed40865ca99934cd3` |
| amb-AB.tsv | fuzz_command.asan vs fuzz_command.asan-ubsan: the memcpy / memset closures | `e98b2379bc27e23e80b5eadd6e124983dc320e6eb2fd52ab592374e63c9393b9` |
| amb-AB.tsv | fuzz_command.asan vs fuzz_command.asan-ubsan: the strcmp interceptor | `257b5e72e7643dd4a209f1c3dc1e06968f48ca73e8b4213ac1be7560522e0fd6` |
| amb-AB.tsv | fuzz_command.asan vs fuzz_command.asan-ubsan: the image map verdicts (string runtime) | `1aac4eb69e000a8805afe61cb767afbfdd468e53855fa69af840129cdc9ee786` |
| amb-AB.tsv | the same, malloc / strndup / strtok walks | `759abddcacb611a7b4b73863e7c59a569ca84b2c2c2c312cf18b1eb7f8bf7ba1` |
| amb-AB.tsv | the same, strdup / strcspn walks | `3c5a95a1c25419e67e7de4842639deda829a44cb42e84c7573a315be1aa3a9a4` |
| amb-AB.tsv | the same 169 A/B pairs, re-checked with bytecmp 8ed351b56fbe and repin_check 3c6de3f0d13e | `34e2ab2c678b58197c7f6f64b01a665880af8e8ba87327272497c4bebff10a94` |

## Citation changes

`measured-rows.tsv`: 57 rows, one per changed citation at the series base. 52 rows cover the class-F claims (a claim
over two lines has its row on the line where it ends): each new text adds `(cmpkit 86da41d3ef68;
provenance/evidence/kit-rerun-86da41d3ef68)`; send_message_k.v:5 also writes what is true, and RT_pf_Tbl.v:9 drops
the wrong address. 5 rows cover the 4 not-certified claims (their evidence ends `note: not certified: no image / no
twin`): they mark each claim as not measured with the kit of record, and lib/B/Bz/A/I_strspnw.v:30 drops the wrong
donor addresses. An uncertified "same code" claim does not stand as shipped.
