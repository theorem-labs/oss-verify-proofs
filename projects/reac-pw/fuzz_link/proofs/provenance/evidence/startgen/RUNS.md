# Start-up runs of image A: what each run gave

This statement replaces the run logs and check outputs of the start-up files of reac-pw/fuzz_link image A. Each log
is kept, unchanged, in an internal record; the line after each heading cites it by path and sha256. The
facts below are copied from the logs. Paths such as lib/A/AB01.v are relative to the unit's proofs folder.

- Image: fuzz_link.asan sha256 059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d (unstripped twin sha256 66cd0f159895f119b29a44eb3760cfda78506402a019729057dba69562af9d9f).
- Tools: the start-up set 2026-10-30b (tool sha256 values: `startup-set-2026-10-30b.sha256`;
  check: `startup-set-2026-10-30b.SHA256SUMS-check.out`), except itabranges 6bd6b8036747 (`deviation-tools.sha256`),
  and, for the last gen_ad2 run below, the start-up set 2026-10-30d (tool sha256 values:
  `runs-30d/startup-set-2026-10-30d.sha256`; check: `runs-30d/startup-set-2026-10-30d.SHA256SUMS-check.out`).
  The two checks at the end are the scripts in this directory.

## hsform hs eb5d13059ca8: lib/A/AB01.v

internal record, path startgen/runs/hsform-hs.AB01.out, sha256 eea83a762eb42ed2ddd10cb022bcbd732f079e2ba4b1b8639b9fe51b865e4ab5

- KImg gate over the 50 collected states: PASS. `malloc_context_size` (0xab13c) = 30 and `asan_inited` (0xab118) = 1
  in all 50 hand-off states. Arrival gate PASS: all 50 hand-off states at main 0x81d2c. Descriptor-array gate PASS:
  344 cells of 0xf9 at 0x8000cc54 (the shadow of asan_globals 0xa62a0, n = 43) in all 50 states.
- Gates run: pin, KImg, malloc_context_size, arrival, descriptor-array; skipped: none.
- Wrote AB01.v: 50 hand-off states, 50 reached by the checker, 0 filled; kn lengths 976..1167.

## itabranges 6bd6b8036747 (rule text): lib/A/AB05.v

internal record, path startgen/runs/itabranges.AB05.out, sha256 6e895f5f5207ba18265cb16cc3de900acc7174d66a8fc40221f57d38de039757

- `startup_plan_tfib_ranges`: the donor's 14 ranges (68584 words) become 1 range, the executable sections whole:
  0x3126c + 113716 words (0x3126c..0xa033c) = .text.

## plantail f8aa639d5cc7: lib/A/AB05.v

internal record, path startgen/runs/plantail-insert.AB05.out, sha256 749eae6e26e948e0cceda3ee8d9aea7e84719d963d84a2c3f9e750737aab4080

- The 50 tails of lib/A/AB05.v replaced: before, 50 x [XMemset*5]; after, [XMemset*44].

## af0m 3681a21ca430: AF0m (output AF0m.r5.v)

internal record, path startgen/runs/af0m.AF0m.out, sha256 72336b017e03fedc711b6561832c1540ebff17688dca21e3d9fe55d752aa0c91

- Self-test: 29 known answers. Globals 43, metadata 0xa62a0 / 0xac0, shadow cells 9151, zero-shadow ranges 31,
  states 50.
- const_abs: 228 base rows kept in place (40 values corrected), 344 descriptor words (32 in the base's slots, 312
  appended), 3 slots filled with a duplicate, 31 cells appended. owned_static: 77 entries (the descriptor array
  (0xa62a0, 0xac0) and 43 per-global redzones).
- Redzone-tail self-check PASS (35 read-only tails, 987 bytes); 161 cells appended for the 987 owned read-only bytes,
  each equal to the image byte and to every state.
- The base's TFIB_DEPOT, TFIB_ERRNO, TFIB_GP, TFIB_IAL_FLAG, TFIB_INST, TFIB_MAIN, TFIB_MAIN_RA, TFIB_OOM, TFIB_STORE,
  TFIB_TP and TFIB_TSD equal the values derived from the image. TFIB_TR0 and TFIB_HASH written from tr0.py on this
  image: TFIB_TR0 [0x3fc68; 0x40fb8] / [0x3fc68], TFIB_HASH 15706673611551676535 / 3361024770578257722, buckets
  661623 / 726842.
- Gates PASS: index (228 kept base rows at their base index; 767 output rows); xowned (719 const_abs cells, 9151
  shadow cells, all inside Tfib_owned_static or its shadow); am_const (every byte of all 767 Tfib_const_abs cells
  pinned by all 50 states); symbol gates `malloc_context_size` = 30 and `asan_inited` = 1 in all 50 states.
- Keyed against the image's asan_globals (43 descriptors at 0xa62a0): PASS Tfib_const_shadow 9151 rows, Tfib_zero_shadow
  31 rows, Tfib_owned_static descriptor rows 44, Tfib_const_abs descriptor words 344, depot-trace rows 2. The REAL()
  interceptor rows are not measured by this single-file check.

## ifchk f5cde600cc18: lib/A/AF0m.v in the 50 states of lib/A/AB01.v

internal record, path startgen/runs/ifchk.AF0m-AB01.out, sha256 7e4bac087d61db4ee7f5ddb84a1fcde28716195e14637d71548c04d5563e1dac

- Image sha256 059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d.
- 9940 cells (sym 22, abs 767, shadow 9151) x 50 states: 497000 as stated, 0 different, 0 undetermined, 0
  inexpressible. Sources: 464450 pairs by the certificate (1500 of them KImg over NOBITS, the KIMG-BSS rule), 32550 by
  the image. Self-test: 2/2 KIMG-BSS cases.

## gen_ad2 8a509576b937: lib/A/AD2i.v and lib/A/AD2j.v

internal record, path startgen/runs/gen_ad2.cgif-pair.out, sha256 d2af4cd8608a20493ecfa3c5e74c7d6f86ef3a14983b4c691655d3ffcbf8142a (on cgif_file_fuzzer c8557374ad2e's AD2i / AD2j pair)

internal record, path startgen/runs/gen_ad2.pcap-AD2i.out, sha256 e35def8f3d101873808e8a3f13d0041e9feefd2c43171944aa696c401ca24800 (on libreac/fuzz_pcap's AD2i text; its AD2j output is not used)

- Both runs: image sha256 059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d; states lib/A/AB01.v
  (HS_tfib, 50); TFIB_MAIN 0x81d2c, TIDV 43, CANV 60, CANARY_ATOM 41; image 0x10000..0x654000, rw window
  0xa1000..0x654000, .data 0xa36c8, asan_globals 0xa62a0, .bss 0xa6d80..0x6534f0; 68 regions.
- PRECHECK ok: every chunk justified in all 50 states. GATE ok: 68 regions ordered and disjoint, chunks inside their
  region and inside the page-extended PT_LOADs. 17 TWIN checks ok against the unstripped twin. PASS AD2j regions (68
  rows) and anchor roles (16 rows).
- lib/A/AD2j.v is this run's output. lib/A/AD2i.v was later written again by the 2026-10-30d run (next
  section).

## gen_ad2 3665ff2a7926 (start-up set 2026-10-30d): lib/A/AD2i.v and lib/A/AWH8.v

internal record, path startgen/runs-30d/gen_ad2.AD2i-AWH8.run.sh, sha256 4673e36bb6860fe7f019b2bc8555f99c7977c7f866cf6cce4298554663d61ba0 (the command of record)

internal record, path startgen/runs-30d/gen_ad2.AD2i-AWH8.out, sha256 82b1dfc7e1aa6e46346956deb5641fdb33e71039b13b1772adb131cdaeb6161b (its output)

internal record, path startgen/runs-30d/gen_ad2.AD2i-AWH8.report.txt, sha256 a9fea049e53c6898f9d83d3313131e750f8d8d05003caf495fc0ed57d6b64b8b (its report: the output without the first two lines)

internal record, path startgen/runs-30d/gen_ad2.cgif-pair.AD2j-check.out, sha256 e396d3eb46562f3f9e5d8a39e3683e1630e01dfc961c7737db775cea145c7323 (the same tool on cgif_file_fuzzer c8557374ad2e's AD2i / AD2j pair)

internal record, path startgen/runs-30d/inputs-outputs.sha256, sha256 48e32b300099a2342ec2232178e24450aaff441712562cd1a799d34ade9fbb3f (the inputs and outputs)

- Command: `gen_ad2.py --side A` through the set's `frozen-run.sh`, with `--month 2026-10`, `--states lib/A/AB01.v`,
  `--atable lib/A/AB12.v`, `--tsegs lib/A/AB1h.v`, `--owned provenance/startgen/AF0m.owned-with-bss-globals.v`, the image
  and its twin, the templates (libreac/fuzz_pcap's AD2i text at 88154566652a, cgif_file_fuzzer's AD2j.v and image),
  `--world-core lib/Reusable/YA0n.v --wh8 --ad1g lib/A/AD1g.v --argh0 lib/Reusable/YA02.v`, and the module renames
  from libreac/fuzz_pcap and cgif_file_fuzzer to reac-pw/fuzz_link. Outputs: AD2i.v, AWH8.v and an AD2j that is not used.
- Output: image sha256 059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d; states lib/A/AB01.v (HS_tfib,
  50); TFIB_MAIN 0x81d2c, TIDV 43, CANV 60, CANARY_ATOM 41; the same image bounds and 68 regions as the run above.
  lib/Reusable/YA0n.v: mkW takes 6 arguments, w_H8 last, so AD2i gets Hypothesis H1_8 and W1 passes it to mkW as its
  sixth argument; AWH8.H1_H8 discharges it. W_H8 PRECHECK ok: 50 states, 660 non-stack a_vis entries all
  page-aligned. AWH8's band maps read from lib/A/AD1g.v: dLow [0x7fff7000, 0x8fff7000), dHigh [0x2008fff7000,
  0x10007fff8000). PRECHECK ok (every chunk, 50 states); GATE ok (68 regions); 17 TWIN checks ok; PASS regions (68
  rows) and anchor roles (16 rows).
- The cgif-pair run gives the same lines and PASS AD2j.v regions (68 rows) and anchor roles (16 rows). Its AD2j
  (`<scratch>/startup/cgif/A/AD2j.v`, sha256 ff356cba568f, recorded in full below) differs from lib/A/AD2j.v only in
  notice lines 3-5, so lib/A/AD2j.v was not changed.
- Inputs and outputs (sha256 as recorded; `<scratch>/` is the start-up scratch directory; since the run, one comment line each of lib/A/AD2i.v (:511) and lib/A/AWH8.v (:14) cites wh8.py by its sha256, so the sha256 of those two files today differ from the ones below):
  - proofs/reac-pw/fuzz_link/lib/A/AD2i.v: sha256 06b042073ef7b397b36d80fb4c1265c3ef665c2d6fb55b49aebe1569e261f08d
  - proofs/reac-pw/fuzz_link/lib/A/AWH8.v: sha256 cf7973b542e194c6c50233c6e4e5744128ced2d5854b589f6a1bc9eddaf23711
  - proofs/reac-pw/fuzz_link/lib/A/AD2j.v: sha256 1fde45bebcb9c631be1707e1bd9f033aa78f8977e83c7116d18e0dd49514fedd
  - proofs/reac-pw/fuzz_link/lib/A/AB01.v: sha256 d8384d5da4013cf96dbaddff9905d6dfbdddebf53230f0e1b8e393ea1a03191a
  - proofs/reac-pw/fuzz_link/lib/A/AB12.v: sha256 6fdac3fed3ab4d709261149d85257a26f8a7399e5ffe13fd82930ece7420ecab
  - proofs/reac-pw/fuzz_link/lib/A/AB1h.v: sha256 083614568e8073b5e3542dbd048b2cb38b6dc348cdda303d64b972484fae42d2
  - proofs/reac-pw/fuzz_link/lib/A/AD1g.v: sha256 231648573dceb084b8da4193fb5b6aca02d010137a0467459ab3c30f7de620fe
  - proofs/reac-pw/fuzz_link/lib/Reusable/YA0n.v: sha256 0b2721141345d9485b3c3b2da7fa37c67f0f43757c97d56f6789ed9a6b854da5
  - proofs/reac-pw/fuzz_link/lib/Reusable/YWH8.v: sha256 7179303d4d5ab3e3a8e4fbf29d0b11da4dae7a49b8544ff9b8b89682da578d91
  - proofs/reac-pw/fuzz_link/lib/Reusable/YA02.v: sha256 86a840b79cdb4156d10095f2226b6f7d9dd3015fc74791ea96ebeab5a9eadaa7
  - proofs/reac-pw/fuzz_link/provenance/startgen/AF0m.owned-with-bss-globals.v: sha256 ab0e0e1cb877f6f8f89113a58d44746d469b6cb63ee6a614977c22a0d8e37725
  - <scratch>/startup/tmpl/AD2i.v: sha256 0425f8aa565ee0b72cd4f58f638e9a18aa79244d70839e52a42eaad462530327
  - <scratch>/startup/cgif/A/AD2j.v: sha256 ff356cba568fba3cd68bc4b827059dfd4566cd6afd5886f05ad244cc7fc2bd3b
- pins 4778073f01be stamped the new lib/A/AD2i.v with the same Read-from line (self-test 3/3; no keyed table):
  internal record, path startgen/runs-30d/pins-stamp.AD2i.out, sha256 ce173b06b00109b800a80f0e1c9e6f5a674ab955f5da3ce5d5e301c06400ac7e
- codeptr 12348302dfd2: AD2i.v 2 code, 4 data, 0 FINDINGS, 0 STALE against libreac/fuzz_pcap's AD2i.v; AWH8.v 0 code,
  0 data, 0 FINDINGS, 0 STALE against libreac/fuzz_boxreg's AWH8.v.
  internal record, path startgen/runs-30d/codeptr.AD2i.out, sha256 c4f0b07adc17327f6d798a711f00c4a32a864213bcc3bd96aaf7f39f707ad361
  internal record, path startgen/runs-30d/codeptr.AWH8.out, sha256 462b2f6161ecafe25985c1f8ccfc779f64518facc80edcf5ff1740a87e8f5862

## gen_ad1k a93a5ff60645: AD1k

internal record, path startgen/runs/gen_ad1k.AD1k.out, sha256 22bdc0c853d7ca9c1635f1dfab6e13058bc172f6bde8e904754fa464243c4b6c

- The donor's (cgif AE39.v) mc_bounds band [0x10350, 0x10370) is found at 0x10360, inside R_A1d [0x10340, 0x103b0):
  this unit's AE39 mc_bounds must say MC_LO = 0x10360. Hull bound 0x20f80 (the asan_globals descriptor with the
  lowest beg, 0x20fa0, floored to 64 bytes).
- Wrote AD1k.v (23 sites) and the site table `runs/gen_ad1k.sites.md`.

## pins 4778073f01be (keyset f050b43e480e): the Read-from line

- Self-test 3/3 paired cases in every run. Stamped with the line `(* Read from: fuzz_link.asan (reac-pw/fuzz_link
  asan) sha256 059dae63...; unstripped twin sha256 66cd0f15... *)`: lib/A/AB01.v, AB03.v, AB05.v, AB12.v, ACej.v,
  AD2i.v, AD2j.v, AE3i.v and the staged AD1k.stamped.v.
- Keyed tables: AB12.v PASS image fields (3 rows), x_* fields (11 rows), stops_more (13 rows: the 13 self-loops of
  .text); AD2j.v PASS regions (68 rows), anchor roles (16 rows). AB01, AB03, AB05, ACej, AD2i, AE3i, AD1k: no keyed
  table.
- lib/A/AF0m.v: REFUSED, not stamped (keyset cannot evaluate `YImgTop.IMG_LO`).

internal record, path startgen/runs/pins-stamp.AB01.out, sha256 704ce963ba74edc5ca06ebec599f4a0b7a648704829272d72c891654d822034f
internal record, path startgen/runs/pins-stamp.AB03.out, sha256 0b8c82d69674b6c00ebecf8bbf80b2fa1e65864dd69a2933dbfbd692a5d055b7
internal record, path startgen/runs/pins-stamp.AB05.out, sha256 dca1fae4def18210ebd90f765af56ced36037b05c06f396c6ee784e373289faf
internal record, path startgen/runs/pins-stamp.AB12.out, sha256 86dbb98adff59d73e8eeb02d9f58009a40b6cb4442167af1926b9603e5e5c4d6
internal record, path startgen/runs/pins-stamp.ACej.out, sha256 c1ac753f45c0329813eff6a7ef1b1867210b3fc8709f38ba5d52294a4b372dcd
internal record, path startgen/runs/pins-stamp.AD1k.out, sha256 56cc6fec2572c251ce3c4955d3eb73daf99ca9350c65d295971abefb5834b99a
internal record, path startgen/runs/pins-stamp.AD2i.out, sha256 ce173b06b00109b800a80f0e1c9e6f5a674ab955f5da3ce5d5e301c06400ac7e
internal record, path startgen/runs/pins-stamp.AD2j.out, sha256 a03dd04cdb96ea5d101f98aa9fa6b3dd6841d3b5a6f508cf4afe0aba1485bb3b
internal record, path startgen/runs/pins-stamp.AE3i.out, sha256 21ae53c457cffdde14d62bc4638a2b06639a669b85dd96055ece04d60a67f8d1
internal record, path startgen/runs/pins-stamp.AF0m.out, sha256 2bca4c5607aeb2998919c7ebb9a14b873e72bf12a64968b16b87feceda9992f3

## codeptr 12348302dfd2: address literals (declarations: codeptr-decl.sh)

- Self-test: 27 known answers in every run.
- pcap form, against libreac/fuzz_pcap's files: 0 FINDINGS and 0 STALE in AB01.v (15 code, 449 data), AB03.v (19,
  295), AB05.v (37, 4), AB12.v (25, 5), AF0m.v (31, 824), AE3i.v (0, 94), ACej.v (102, 0).
  internal record, path startgen/runs/codeptr.pcap-form.out, sha256 f18ddd4b7708ab02b6ba0a74c8e92d3547841b855823e2c4f7f0da59a8e32157
- AF0m.v as regenerated: 56 code, 855 data, 0 FINDINGS, 0 STALE.
  internal record, path startgen/runs/codeptr.AF0m.out, sha256 ceaaf1317d96b6a853a0875de80ad7b019c50b139a671d2df9843771e5c10289
- AD2i.v: 2 code, 4 data, 0 FINDINGS, 0 STALE.
  internal record, path startgen/runs/codeptr.AD2i.out, sha256 c4f0b07adc17327f6d798a711f00c4a32a864213bcc3bd96aaf7f39f707ad361
- cgif form, against cgif_file_fuzzer's files: AD2i.v (2 code, 4 data), AD2j.v (3, 183), AD1k.v (0, 59): 0 FINDINGS,
  0 STALE.
  internal record, path startgen/runs/codeptr.cgif-form.out, sha256 71aeb972e0ff48786defcc0cf04f1b232ccd91f35ae824c2a7575eb65b84e419
- Positive control, libreac/fuzz_pcap's own AF0m.v and AB12.v read against this image: 339 FINDINGS (339 STALE) and
  29 FINDINGS (29 STALE).
  internal record, path startgen/runs/codeptr.positive-control.pcap-files-on-link.out, sha256 27c97a11c583c5bfaef63dec7bc2c2796703a47c1e3301f3df32b6aa2c9a6e8e

## imgread_check.py: lib/A/AB1v.v, AB1h.v, AB1k.v

internal record, path startgen/imgread_check.AB1v-AB1h-AB1k.out, sha256 317f1fd4bd682fc17d084f69f6df252a0f9998b75430d2e8f62b3e1edb78974d

- AB1v.v: 0 fetch facts; tfibmusl [0x90140, 0xa0348) 16514 words, in the executable segment, 12 bytes past its p_memsz
  end; tfibguard [0x82154, 0x82164) 4 words, 0 bytes past.
- AB1h.v: 8 fetch facts checked against the image bytes; segments_reserved, sum_sizes 0x644000 and the writable window
  [0xa1000, 0x654000) EQUAL to the image's.
- AB1k.v: 45 fetch facts checked; tfibst [0x66cb8, 0x66db0) 62 words, 0 bytes past.
- VERDICT: PASS.

## asan_globals_check.py: lib/A/AF0m.v

internal record, path startgen/asan_globals_check.AF0m.out, sha256 335cd1b1542b26f2363c45faf46e0720ad569a520615b4d6b5f6dfdb75ccf0b3

- Image and twin sha256 as above. asan_globals at 0xa62a0, size 2752 (43 descriptors of 64 bytes), as expected; 0
  descriptors with an odr_indicator; 9151 shadow rows (8807 redzone or partial + 344 descriptor-array).
- lib/A/AF0m.v: Tfib_const_shadow 9151 bytes, 0 mismatched or missing, 0 extra; Tfib_owned_static 77 rows, the 44
  expected owned ranges (43 redzones + the descriptor array) present as exact rows and covered byte for byte.
- VERDICT: PASS.
