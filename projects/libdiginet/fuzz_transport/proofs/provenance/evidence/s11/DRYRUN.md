# S11 dry run: the 19 src/ walks of libdiginet/fuzz_frame and libdiginet/fuzz_decode relocated onto fuzz_transport's ASan images

proves no function (kind: measurement). A dry run: no proof is written, patched or built here, and no relocated file
enters lib/. Design: the integration owner's design ASAN-WALKS.md (sha256 22663f22d53c, internal record) sections 1.2-1.4, 2 and 3; the walker brief's "Relocated rows"
paragraph says how a walker uses this output. Step 2 (the integration owner's decisions of 2026-10-31 04:08Z) re-ran the relocation
on the base with the image-A kit (S06 + S10 A) and added the trans_src_ok mapping and frame_build's G lift.

## Inputs (all read by sha; no working copy)

| what | id |
|---|---|
| frame source | `02fe409d4ae` (`02fe409d4aedd004fa028b5815c9f0fa8868ced5`), proofs/libdiginet/fuzz_frame/lib/{A,B}/Prog/ |
| decode source | `7b6185922a1` (`7b6185922a15c0a042393f270448dd8af24a7ce4`), proofs/libdiginet/fuzz_decode/lib/{A,B}/Prog/ |
| target base | `66fa526ea390` (the ASan integration branch: c8ebc3afb25 + S06 + S10 A, KitA 31331854be3d and 68912113c990), merged into this branch; the listing files DgnTransport{Syms,Addr,List}.v / DgnTransportB{Syms,Addr,List}.v are c8ebc3afb25's, unchanged. The first run (f3bc3d17832) used c8ebc3afb25 |
| fuzz_frame.asan | pin `34f028d3dec4`, unstripped twin `67d7e481d74e` |
| fuzz_frame.asan-ubsan | pin `2574b26fc98e`, unstripped twin `ee3ea72a063b` |
| fuzz_decode.asan | pin `47bd808e8cb9`, unstripped twin `a7133a6c74e5` |
| fuzz_decode.asan-ubsan | pin `1c8e7ec20682`, unstripped twin `50d7282d5a4b` |
| fuzz_transport.asan | pin `e89be137db17`, unstripped twin `86efc3a80314` |
| fuzz_transport.asan-ubsan | pin `41113a03c82f`, unstripped twin `e217cb0a84f1` |
| comparison kit | cmpkit 86da41d3ef68 (the comparison kit of record, registry tools/cmpkit/86da41d3ef68/, `sha256sum -c SHA256SUMS`: 9 x OK), strictcmp3.py 65688e94214a |

Twin check (the script, before any use): each unstripped twin's PT_LOAD bytes equal its pin's outside the ELF header's
section-header fields (0x28-0x2f, 0x3c-0x3f) and the 20-byte .note.gnu.build-id descriptor: 25 bytes differ there, 0
elsewhere, for all six pairs. The kit's own `drvcmp.py twins` gives the same for all six.

Regenerate (REPO = a clone with the three commits, IMG = a directory of role-named images, see the script's usage):
`python3 s11_reloc.py --repo REPO --img IMG --out OUT --tables TAB --cmpkit KIT --keep-going` (exit 0). The 129
relocated files are NOT committed (not in lib/, not under this directory): they are in the run's OUT only; files.tsv
gives the sha256 of each source file and of each relocated file, so a rerun is checked against it.

## Result per function and image

Every function RELOCATES: no numeral stopped. bycmp = strictcmp3 `cmp` of the source twin against the target twin by
the function's .symtab name (bycmp_<f>_<image>.txt). Names pending = names of the relocated code that base 66fa526ea390
does not define yet, by the piece that brings them (names-A.tsv / names-B.tsv). comments = image numerals left in
comments (kreloc.py's rule).

| image | function | source | files | numerals mapped (code / data / .got / object index / listing position) | stopped | bycmp | modules / names pending (S07 / S10 / core B) | comments |
|---|---|---|---|---|---|---|---|---|
| A | diginet_mac_is_digidesign | frame A | 5 | 13 (1 / 7 / 5 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 4/0/0 target-differ 0, cstr 0 | none | 92 |
| A | diginet_frame_is_keepalive | frame A | 5 | 4 (1 / 2 / 1 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 6/0/0 target-differ 0, cstr 0 | none | 74 |
| A | diginet_frame_parse | frame A | 8 | 31 (28 / 2 / 1 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 36/0/0 target-differ 0, cstr 0 | none | 387 |
| A | diginet_frame_build | frame A | 9 | 35 (35 / 0 / 0 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 30/0/0 target-differ 0, cstr 0 | none | 253 |
| A | diginet_announce_parse | frame A | 5 | 21 (21 / 0 / 0 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 13/0/0 target-differ 0, cstr 0 | none | 126 |
| A | diginet_cursor_init | decode A | 4 | 10 (1 / 5 / 4 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 6/0/0 target-differ 0, cstr 0 | none | 76 |
| A | diginet_msg_next | decode A | 8 | 28 (19 / 5 / 4 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 36/0/0 target-differ 0, cstr 0 | none | 465 |
| A | diginet_body_check | decode A | 10 | 64 (1 / 0 / 0 / 60 / 3) | none | EQUAL-mod-pcrel pcrel/real/unm 12/0/0 target-differ 0, cstr 1 | none | 70 |
| B | diginet_mac_is_digidesign | frame B | 5 | 13 (1 / 7 / 5 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 4/0/0 target-differ 0, cstr 0 | 5 / 19 (19 / 0 / 0) | 130 |
| B | diginet_frame_is_keepalive | frame B | 5 | 4 (1 / 2 / 1 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 5/0/0 target-differ 0, cstr 0 | 5 / 19 (19 / 0 / 0) | 133 |
| B | diginet_frame_parse | frame B | 9 | 22 (19 / 2 / 1 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 27/0/0 target-differ 0, cstr 0 | 15 / 41 (27 / 12 / 2) | 455 |
| B | diginet_frame_build | frame B | 15 | 28 (28 / 0 / 0 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 29/0/0 target-differ 0, cstr 0 | 14 / 60 (47 / 8 / 5) | 428 |
| B | diginet_announce_parse | frame B | 2 | 20 (0 / 0 / 0 / 20 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 7/0/0 target-differ 0, cstr 0 | 19 / 67 (56 / 9 / 2) | 84 |
| B | diginet_cursor_init | decode B | 6 | 10 (1 / 5 / 4 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 6/0/0 target-differ 0, cstr 0 | 7 / 20 (19 / 1 / 0) | 98 |
| B | diginet_msg_next | decode B | 8 | 24 (15 / 5 / 4 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 38/0/0 target-differ 0, cstr 0 | 12 / 40 (29 / 8 / 3) | 580 |
| B | diginet_body_check | decode B | 10 | 64 (1 / 0 / 0 / 60 / 3) | none | EQUAL-mod-pcrel pcrel/real/unm 12/0/0 target-differ 0, cstr 1 | 17 / 84 (74 / 8 / 2) | 83 |
| B | diginet_sum16 | frame B | 5 | 15 (3 / 7 / 5 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 2/0/0 target-differ 0, cstr 0 | 5 / 19 (19 / 0 / 0) | 135 |
| B | rd32 | frame B | 5 | 13 (1 / 7 / 5 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 5/0/0 target-differ 0, cstr 0 | 5 / 20 (20 / 0 / 0) | 161 |
| B | copy_strz | frame B | 5 | 10 (10 / 0 / 0 / 0 / 0) | none | EQUAL-mod-pcrel pcrel/real/unm 4/0/0 target-differ 0, cstr 0 | 5 / 13 (13 / 0 / 0) | 173 |

Totals: 129 files (A 54, B 75), 429 numerals (A 206, B 223), 0 stopped; 19 of 19 bycmp EQUAL-mod-pcrel with real 0,
unmeasured 0, target-differ 0. The two diginet_body_check records carry one C-string acceptance each, the side-stack
frame description "2 32 32 4 c:49 96 40 4 m:50" (decode 0x16e3d, transport A 0x16f72, B 0x16f4c), as in arel's record.
Every mapped code numeral points at an instruction whose word is equal in both images (no pc-relative row was needed).
**Image A: nothing is pending** (names-A.tsv is empty: every module and name the 54 relocated image-A files use is
defined on 66fa526ea390). Image B: everything pending is S07 (kit B), S10 B (DgnTransportBCg.v) or TCB's core B.

## The exact file lists

Patterns of the design's table, listed from the trees. Added: `<f>_c.v` for the footprint rows, because their
_F_c / _cg / .v Require it; decode B diginet_cursor_init also has `.v` and `_cgW.v`. `_c`, `_F_c` and `_cg` are
statement files (TCA / TCB write them on the base): relocated as drafts. diginet_body_check is decode's on both images.

- A diginet_mac_is_digidesign (frame A, 5): diginet_mac_is_digidesign_c.v diginet_mac_is_digidesign_F_c.v diginet_mac_is_digidesign_F.v diginet_mac_is_digidesign_cg.v diginet_mac_is_digidesign.v
- A diginet_frame_is_keepalive (frame A, 5): diginet_frame_is_keepalive_c.v diginet_frame_is_keepalive_F_c.v diginet_frame_is_keepalive_F.v diginet_frame_is_keepalive_cg.v diginet_frame_is_keepalive.v
- A diginet_frame_parse (frame A, 8): diginet_frame_parse_cg.v diginet_frame_parse_kit.v diginet_frame_parse_seg_hdr1.v diginet_frame_parse_seg_hdr2.v diginet_frame_parse_seg_head.v diginet_frame_parse_seg_tail.v diginet_frame_parse_segs.v diginet_frame_parse_walk.v
- A diginet_frame_build (frame A, 9): diginet_frame_build_cg.v diginet_frame_build_iface.v diginet_frame_build_kit.v diginet_frame_build_seg_a.v diginet_frame_build_seg_h1.v diginet_frame_build_seg_h2a.v diginet_frame_build_seg_h2b.v diginet_frame_build_seg_loop.v diginet_frame_build_walk.v
- A diginet_announce_parse (frame A, 5): diginet_announce_parse_c.v diginet_announce_parse_F_c.v diginet_announce_parse_F.v diginet_announce_parse_cg.v diginet_announce_parse.v
- A diginet_cursor_init (decode A, 4): diginet_cursor_init_c.v diginet_cursor_init_F_c.v diginet_cursor_init_F.v diginet_cursor_init_cg.v
- A diginet_msg_next (decode A, 8): diginet_msg_next_cg.v diginet_msg_next_walk_lib.v diginet_msg_next_seg_body.v diginet_msg_next_seg_chan.v diginet_msg_next_seg_entry.v diginet_msg_next_seg_sys.v diginet_msg_next_segs.v diginet_msg_next_walk.v
- A diginet_body_check (decode A, 10): diginet_body_check_cg.v diginet_body_check_cgW.v DgnBcCut.v DgnBcHead.v DgnBcLoop.v DgnBcLoopCall.v DgnBcLoopCut.v DgnBcLoopTest.v DgnBcRel.v DgnBcScan.v
- B diginet_mac_is_digidesign (frame B, 5): diginet_mac_is_digidesign_c.v diginet_mac_is_digidesign_F_c.v diginet_mac_is_digidesign_F.v diginet_mac_is_digidesign_cg.v diginet_mac_is_digidesign.v
- B diginet_frame_is_keepalive (frame B, 5): diginet_frame_is_keepalive_c.v diginet_frame_is_keepalive_F_c.v diginet_frame_is_keepalive_F.v diginet_frame_is_keepalive_cg.v diginet_frame_is_keepalive.v
- B diginet_frame_parse (frame B, 9): diginet_frame_parse_cg.v diginet_frame_parse_kit.v diginet_frame_parse_seg_hdr1.v diginet_frame_parse_seg_hdr2.v diginet_frame_parse_seg_hdr3.v diginet_frame_parse_seg_head.v diginet_frame_parse_seg_tail.v diginet_frame_parse_segs.v diginet_frame_parse_walk.v
- B diginet_frame_build (frame B, 15): diginet_frame_build_cg.v diginet_frame_build_cgW.v diginet_frame_build_cuts.v diginet_frame_build_iface.v diginet_frame_build_seg_a.v diginet_frame_build_seg_b.v diginet_frame_build_seg_h1.v diginet_frame_build_seg_h2a.v diginet_frame_build_seg_h2b.v diginet_frame_build_w_bc.v diginet_frame_build_w_entry.v diginet_frame_build_w_epi.v diginet_frame_build_w_h2.v diginet_frame_build_w_hdr.v diginet_frame_build_w_tail.v
- B diginet_announce_parse (frame B, 2): diginet_announce_parse_cg.v diginet_announce_parse_cgW.v
- B diginet_cursor_init (decode B, 6): diginet_cursor_init_c.v diginet_cursor_init_F_c.v diginet_cursor_init_F.v diginet_cursor_init_cg.v diginet_cursor_init.v diginet_cursor_init_cgW.v
- B diginet_msg_next (decode B, 8): diginet_msg_next_cg.v diginet_msg_next_cgW.v diginet_msg_next_walk_lib.v diginet_msg_next_seg_body.v diginet_msg_next_seg_chan.v diginet_msg_next_seg_entry.v diginet_msg_next_seg_sys.v diginet_msg_next_segs.v
- B diginet_body_check (decode B, 10): diginet_body_check_cg.v diginet_body_check_cgW.v DgnBcCut.v DgnBcHead.v DgnBcLoop.v DgnBcLoopCall.v DgnBcLoopCut.v DgnBcLoopTest.v DgnBcRel.v DgnBcScan.v
- B diginet_sum16 (frame B, 5): diginet_sum16_c.v diginet_sum16_F_c.v diginet_sum16_F.v diginet_sum16_cg.v diginet_sum16.v
- B rd32 (frame B, 5): rd32_c.v rd32_F_c.v rd32_F.v rd32_cg.v rd32.v
- B copy_strz (frame B, 5): copy_strz_c.v copy_strz_F_c.v copy_strz_F.v copy_strz_cg.v copy_strz.v

## Names

The map (namemap-A.tsv / namemap-B.tsv: every rename with its rule and count) is built from the files:

- listing (from the six listing files): dfsym / ddsym -> tsym, fbsym / ddbsym -> tbsym; constructors by the exact
  constructor sets (DF_ / DD_ -> TS_, FB_ / DDB_ -> TB_; frame_build's own FB_AT, FB_EPI, ... stay); dgnframe_ /
  dgndec_ -> transport_, frameb_ / dgndecb_ -> transportb_ for the names the listing files define.
- kit modules: DgnFrame* / DgnDecode* -> DgnTransport* (A), FrameB* / DgnDecodeB* / B's DgnFrameCg / DgnFrameLeafb ->
  DgnTransportB* (B), FrameFevt / DecodeFevt -> TransportFevt: frame -> decode by the counterpart decode's tree has,
  then kreloc.py's decode -> transport (agrees with kreloc.py on every name both touch).
- kit names: frame_ / FRAME_ -> the decode_ / DECODE_ counterpart decode's kit of the same image defines (arel's rule),
  then kreloc.py's seven renames (decode_cells -> transport_cells, decode_leaf_at / decode_leaf_wr_at ->
  transport_leaf_at / transport_leaf_wr_at, DECODE_RO_RD -> TRANS_RO_RD, ...); every other decode_ kit name is kept
  (decode_cg_post, decode_twr_ok, decode_rd_ok, decode_off_win, decode_in_block, decode_in_fake, ...). A frame_ kit name
  that decode's kit defines under the same name is kept (frame_zone: decode's DgnDecodeCJ.v:113 / DgnDecodeBCJ.v:114, so
  transport's DgnTransportCJ.v:113); a frame_ / FRAME_ kit name the base defines under the same name is kept
  (FRAME_F_SIZE, frame_f_cells, frame_f_bytes: DgnTransportCg.v on 66fa526ea390). Listing-prefix kit names (PI_dgndec,
  dgndec_tpi, frameb_segs_low, ...) go dgndec -> transport, dgndecb -> transportb.
- own names: a frame_ / decode_ name that a relocated file of the same image defines -> transport_ (statements
  transport_diginet_<f>_cg / _cg_holds_stmt, design 1.2). Uppercase own constants (FRAME_FP_STK, ...) stay, as arel left
  them.

**Names pending (names-A.tsv, names-B.tsv: only what base 66fa526ea390 does not define yet).** A name counts as a
reference only if a file the walk file Requires (transitively, in the source tree) defines it, so a local binder that
shares a global's name does not count. Image A: none. Image B, over the 11 walks:

| piece | modules | names |
|---|---|---|
| S07 kit B | B.AsanCells, B.Img0, B.Prog.AsanKA, B.Prog.AsanKAProof, B.Prog.CanKit, B.Prog.CanLeafb, B.Prog.DgnTransportBCJ, B.Prog.DgnTransportBImg, B.Prog.DgnTransportBLeafb, B.Prog.DgnTransportBPa, B.Prog.DgnTransportBPaLib, B.Prog.LeafCgClose, B.Prog.LeafCgFacts, B.Prog.LeafCgGlue, B.Prog.LeafCgKit, B.Prog.PaJournal, B.Prog.TransportFevt | APPMEM_END, ASAN_K, A_LIM_text, CELL_K, Eimg, Eimg_env, Eimg_img, Eimg_low, GOT_CELL_K, GOT_UAR, HIGHMEM_BEG, HIGHSHADOW_BEG, LOWMEM_END, LOWSHADOW_END, PI_dgndecb -> PI_transportb, PI_frameb -> PI_transportb ... (153 in all) |
| S10 | B.Prog.DgnTransportBCg | FRAME_F_SIZE, decode_asan_cell_ranges, decode_cells -> transport_cells, decode_cg_post, decode_in_block, decode_in_fake, decode_leaf_wr_at -> transport_leaf_wr_at, decode_off_win, decode_rd_ok, decode_twr_ok, frame_cells -> transport_cells, frame_cg_post -> decode_cg_post, frame_f_bytes, frame_f_cells, frame_in_block -> decode_in_block, frame_in_fake -> decode_in_fake, frame_leaf_at -> transport_leaf_at, frame_leaf_wr_at -> transport_leaf_wr_at, frame_off_win -> decode_off_win, frame_rd_ok -> decode_rd_ok, frame_seg_covers -> decode_seg_covers, frame_twr_ok -> decode_twr_ok |
| core B, TCB | B.DecodeTFIB, B.T06_FrameB_env, B.YB1v, B.YC5d, B.YCbq, B.YD2l, B.YE2k, B.YF0x, B.YImgTop | FrameB, SB, TfibB, decodesegsB0, t06be_api_env, t06be_model_laws, tfibsegs, val_mem_rdword |

The S10 B names include the image-free FRAME_F_SIZE / frame_f_cells / frame_f_bytes (image A's DgnTransportCg.v
defines them; DgnTransportBCg.v will carry the same names) and frame_zone (S07's DgnTransportBCJ.v). The core B modules
and names have no transport name yet: B.YB1v, YC5d, YCbq, YD2l, YE2k, YF0x, YImgTop, frame B's B.T06_FrameB_env
(frame_build_cgW) and decode B's B.DecodeTFIB (msg_next, body_check); the record names YD2l.FrameB / YD2l.TfibB and the
segment lists tfibsegs / decodesegsB0. Image B's G twins are on the base already (lib/B/TransportGB.v G_HARNESS_B,
lib/B/Prog/TransportGRwB.v G_HARNESS_B_rw); image B's twins of the kit and S10 come with S07.

**Image B diginet_body_check: decode's version is the one of record** (the integration owner's decision of 2026-10-31 04:08Z: TCB's core B is
decode's lineage). Frame B's text of diginet_body_check_cg.v is a cross-check only and is not in the relocated set
(the script never writes it). The cross-check (relocated with each unit's map, code compared):
- image A: EQUAL (code)
- image B: DIFFERS (code): 3 of 63 code lines differ:
  `-From OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib.B Require Import YCbq YC5d.`
  `+From OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq YC5d.`
  `-From OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.`
  `+From OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib.B Require Import DecodeTFIB.`
  `-Local Abbreviation segs := tfibsegs.`
  `+Local Abbreviation segs := decodesegsB0.`
  The statement is the same; only the segment list (frame B: `tfibsegs` of B/YB1v; decode B: `decodesegsB0` of
  B/DecodeTFIB) and the home of YCbq / YC5d (lib/B vs lib/Reusable) differ. Frame B's diginet_frame_build files were
  proved against frame's text; with decode's of record, their body_check call sites read decode's segment list.

## Comments and notices

Every comment and every Copyright / SPDX / Modified-by line is byte for byte the source's, no line is added or removed
(the script asserts it per file), and no Modified-by line is added. A scan of all comments finds 0 that name a lane, a
worker, a host or a host path. Comments do name the donor units' repo paths and keep the source images' addresses
(the comments column above); the walker who patches a file updates its comments under the unit's comment rules.
Hypothesis names that carry an object number (V16, E16, R16 of DgnBcHead.v) are kept: they are binder names, and in
decode B's DgnBcHead.v R18 / V18 also name register 18. The object indices themselves (A_OBJ, bch_ew_obj's argument and
its bound 18 / 19 -> 95 / 97) are moved by symbol.

## Where transport's callers put the input bytes (read from the base's listing files, both images)

The design asked S11 to confirm frame_build's dmac / smac from the listing (ASAN-WALKS.md section 3). Decoded from
lib/A/Prog/DgnTransportList.v and lib/B/Prog/DgnTransportBList.v (instruction words; offsets from AF_<caller>):

| call | image A | image B | a0 out | a2 dst (dmac) | a3 src (smac) | a4 hp | a5 body, a6 len |
|---|---|---|---|---|---|---|---|
| send_control -> diginet_frame_build | +0x1a4 | +0x1ac | s9 + 32, cap 60: send_control's class-2 frame from __asan_stack_malloc_2 (+0x78), or the realigned machine stack when that returns 0 | s + 120 | s + 0 | s9 + 128 (same frame) | 0, 0 |
| send_data -> diginet_frame_build | +0x17c | +0x184 | s + 216, cap 1514 (g_s.inflight_frame) | s + 120 | s + 0 | s8 (send_data's frame) | send_data's a1, a2 |

s = the caller's a0 (send_control +0x6c / send_data +0x70: `addi s3,a0,0`), and the plain contracts state a0 = s = &g_s
(the integration owner's plain contracts send_control.md:16, send_data.md:16, internal record). So:

- dmac and smac are members of g_s, a harness global: confirmed. Their premise takes trans_src_ok's `inG G_T` branch.
- **frame_build WRITES a harness global from send_data**: out = g_s.inflight_frame (send_data.md:12 "builds a data frame
  with the body into g_s.inflight_frame"). The design's "none of the src functions writes a harness global" (section 3)
  does not hold for diginet_frame_build: its written range `out` is a heap block in frame (frame_in_block + twr_ok, not
  an out-struct side-stack frame), and in transport it is a side-stack / machine frame (send_control) or a G range
  (send_data). Its statement needs a G form for out (or a written-range lift into G); "out structs stay" does not cover it.
  The integration owner decided (2026-10-31 04:08Z): diginet_frame_build takes the G form on both images (Task 4 below).
- diginet_frame_parse's buf (a0 = diginet_session_rx's a1, image A +0x14c): receive's block from
  `__interceptor_trampoline_malloc` (receive +0x44, passed at +0x270), or diginet_session_poll's s2 + 32, its class-5
  frame from __asan_stack_malloc_5 (or the machine stack fallback; poll +0x278 / +0x2f0). Heap or frame branch, never G.
- diginet_body_check's body: diginet_session_submit's a1 (submit +0x6c), take's s7 (take +0x184) and diginet_frame_build's
  body argument (frame_build +0xa4); the design names LLVMFuzzerTestOneInput's local c and tick's body[] for these.
  No heap block in transport; a frame (side-stack, or the machine stack when the stack_malloc call returns 0).

## The input premises: trans_src_ok case and lemma per use site (step 2, base 66fa526ea390)

Not patched here. Each relocated input premise `frame_in_block B lyc Sc q n` / `decode_in_block B lyc Sc q n` becomes
`trans_src_ok B STK sp0 lyc Sc W memc q n` (lib/A/Prog/DgnTransportCg.v:337-342 on 66fa526ea390: HEAP, or with
decode_rd_ok one of FAKE, G (per byte: `forall a, q <= a < q + n -> inG G_HARNESS a`, the range form), WIN, RO).
`trans_src_ok_G_range` (:345-352) BUILDS the G case from a range inside one payload; the walks need the other
direction, from the premise to each fact a site uses: the "Lemmas needed" below are those, with exact statements, all
for lib/A/Prog/DgnTransportCg.v (one writer: not written here) or TransportGCg.v. Every use site of step 1 is listed
with the cases the transport callers supply (the listing table above) and the lemma that serves each case. Line
numbers in columns 1-6 are the source files' (the relocation keeps every line); base citations are file:line at
66fa526ea390 under proofs/libdiginet/fuzz_transport/lib/. The mapping was traced by a read-only subagent and spot-checked here (DgnTransportCg.v:291, :337; TransportGCg.v:291, :472, :506; YCbq.v:335, :451,
:1947, :2014, :2689; YG0d.v:427: all as cited).

### Tags of step 1 (the `uses` and `replacement` columns)
Step 1 = the first S11 run (f3bc3d17832). These codes name what a use site derives from the block fact.


Block facts (kit): `frame_in_block` frame A DgnFrameCg.v:261-262, B :265-266; `decode_in_block` decode A
DgnDecodeCg.v:259-260, B DgnDecodeBCg.v:262-263. Read facts: `frame_rd_ok` A :251-254, B :255-258; `decode_rd_ok` A
:249-252, B :252-255.

Target premise (ASAN-WALKS.md:265-266): `trans_src_ok STK sp0 B lyc Sc W memc q n := decode_in_block B lyc Sc q n \/
((decode_in_fake lyc Sc q n \/ inG G_T q n \/ (sp0 - STK <= q /\ q + n <= sp0)) /\ decode_rd_ok W memc q n)`.
Its non-heap branch = a location L (frame / G / window) and `decode_rd_ok`, whose six conjuncts are named here:

| code | conjunct of decode_rd_ok (DgnDecodeBCg.v:253-255) |
|---|---|
| R1 | every byte of [q, q + n) visible: `aview segs (w_H W) memc a <> None` |
| R2 | `range_addressable (aview ...) SHADOW_OFF q n` (the shadow bytes say every byte is usable) |
| R3 | `shadow_hull_vis (aview ...) q n` (the shadow bytes of the range's granules are visible) |
| R4 | `amem_range q n` (YG0d.v:318: q + n <= 0x7fff7fff, or 0x10007fff8000 <= q and q + n <= 2^47 - 1) |
| R5 | `0 <= q` |
| R6 | `q + n <= 2 ^ 63` |

Codes for a use that decode_rd_ok does not replace:

| code | what the use needs that the non-heap branch does not state |
|---|---|
| OFF | the range is outside this call's stack window (or a callee's window below it). The block gave it by q + n <= alloc_ceiling < sp - FSTK (journal: alloc_ceiling + FSTK <= sp). Needs `decode_off_win regs FSTK q n`, which the design's table puts beside trans_src_ok (ASAN-WALKS.md:258, :268) but which no relocated statement has for these ranges today. |
| POS | 0 < q. R5 gives 0 <= q; the statement's `q <> 0` premise gives the rest, where the statement has one. |
| LO | 4096 <= q. Not in decode_rd_ok; per location: frames_bounds (frame), the G range's own bounds (G) [INFERENCE: S02/S03 ranges], alloc_ceiling <= q (window). |
| HI | q + n <= alloc_ceiling, or a constant at the ceiling's top (bcs_PTRHI = 0x7fffff800000). Not in decode_rd_ok; FALSE for the window branch (the journal window lies above alloc_ceiling). |
| INAPP | `in_app q n` / `app_addr a` (YG0f.v:278, :283: 4096 <= q and q + n <= kLowShadowBeg or in [kHighMemBeg, alloc_ceiling)). No replacement; R4 + R5 give the app_mem bytes the consumer needs, so the consuming lemma must take amem_range (decode's mw_rd does: decode A msg_next_walk_lib.v:222-231). |
| KEEP | the bytes are needed at a later memory m (after a callee or across an inner journal). A block's bytes are kept by the block clause (ajournal YCbq.v:361-362, acall_kept YCbq.v:831-832). Non-heap: frame clause (ajournal :365-367, acall_kept :835-837) for a frame; image clause (:363-364 / :833-834) for G if it is not an owned static or errno; >= alloc_ceiling clause (:359-360 / :830) for the window, only outside the callee's window (needs OFF). |
| KEEPSH | the shadow bytes are needed at a later memory m (range_addressable / shadow_hull_vis at m). A block re-derives them at any state from AR_shadow_law (YG0d.v:431-435). Non-heap: decode_rd_ok holds at memc only. Frame: the frame clause also keeps the frame's shadow bytes (YCbq.v:366, :836). G and window: NO ajournal / acall_kept clause keeps their shadow bytes (they lie below alloc_ceiling, outside the image, in no block or frame); G may use AR_zshadow_law (YG0d.v:436-439) if its rows are zero_shadow_ranges [INFERENCE: design S09/S10 "zshadow rows"]; the window has nothing. Within one walk's own runs the walk's keep facts carry them (named per row). |
| DISJ | disjointness from a frame of this call or a callee's written range, from the block (sep_block_frame, AR_sep_law). Per location from L, not from decode_rd_ok. |
| CALLEE | the block fact is handed to a callee whose premise is `*_in_block`; in transport that premise is trans_src_ok at the callee's (inner) journal: L and decode_rd_ok must be re-established at the inner state and memory. The window disjunct is relative to (STK, sp0) and does not carry to an inner journal whose window lies below the range. |
| HEAP | keeps: only the heap branch needs it (case split on trans_src_ok). |
| PASS | the hypothesis is passed on unchanged (rename / retype only). |
| STMT | the statement premise itself: becomes trans_src_ok (+ decode_off_win where OFF rows exist). |

Counting rule: one row = one patch site (a statement premise, a Hypothesis, a lemma that takes the block fact, or one
tactic site that consumes it or a fact derived from it). Rows of a written block range (`out` of diginet_frame_build)
are in a separate table per walk and counted separately. Comment lines that restate the block reasoning are listed
under each section (not counted).

Out-struct side-stack frames (`frame_in_fake` / `decode_in_fake` + `*_twr_ok`) are not listed.

### Legend of step 2

trans_src_ok (`tso`, A/Prog/DgnTransportCg.v:337-342) has five cases: **H** = HEAP (decode_in_block :321-322), **F** =
FAKE (decode_in_fake :329-331), **G** = a G_HARNESS byte range (A/TransportG.v:12-31), **W** = WIN (in the journal's
window [sp0 - STK, sp0)), **RO** = TRANS_RO_RD (:110-115); F / G / W / RO carry decode_rd_ok (:311-314). `offw` =
decode_off_win (:317-318), the premise each input needs beside tso (step 1, open item 1).

`rdK` = `destruct` of the tso non-heap disjunct, then decode_rd_ok's conjunct K: rd1 every byte visible (:312), rd2
range_addressable (:313), rd3 shadow_hull_vis, rd4 amem_range, rd5 `0 <= q`, rd6 `q + n <= 2^63` (:314).

`case` column: the cases the transport callers supply for that input (the listing facts of the brief):
- diginet_frame_parse buf: H (receive's malloc block), F (diginet_session_poll's class-5 side-stack frame), W (poll's
  machine stack when __asan_stack_malloc_5 returns 0).
- diginet_body_check body, and diginet_msg_next body (passed on by body_check): F, W; never H.
- diginet_frame_build dst / src = g_s + 120 / g_s + 0: G (g_s = (0x5df9c0, 18264), A/TransportG.v:22). body:
  send_data's body (F / W), or 0 with length 0 (send_control).
- diginet_announce_parse (image B) body = f->body = buf + 30 of the frame diginet_frame_parse filled (frame_parse
  stores `buf + 30` at f + 32, frame A diginet_frame_parse_cg.v:26-27; on_announce's f is rx's parsed frame,
  the integration owner's plain contract on_announce.md:16, :51, internal record): H, F, W as frame_parse's buf [INFERENCE: on_announce
  passes f->body unchanged].
- RO is supplied to none of these inputs. The walk proof still discharges every disjunct of tso (the statement allows
  them): the H branch keeps the sibling text; RO, like G, needs L9b's RO case only where a callee intervenes.

`lemma` column: per step-1 tag, the route per case (`H/F: ...` groups cases with the same route). Tags of step 1 (R1-R6,
POS, LO, HI, OFF, INAPP, KEEP, KEEPSH, DISJ, CALLEE, HEAP, STMT, PASS) plus: HIR (a bound `q + n <= alloc_ceiling` that
only serves window separation or 2^47 arithmetic: restate), HIB (body_check's bcs_PTRHI), KEEPFB (frame_build's keeps in
the G form, Task 4), KEEPW (announce_parse's own keeps), WALKSH (a carry of shadow facts by the walk's own keep fact,
case-free), MWRD (msg_next's mw_blk -> mw_rd), SUB (a sub-range), STMTG (frame_build's G premises), CALLEEFB (frame_build's
body_check call in the G form), EMPTY (frame_build's empty unaligned body), HEAPW (the block witness), POSM (`0 < body`
without a `body <> 0` premise), AS (as another row), OUT / OUTONLY (frame_build's out, Task 4).

Status used in the counts: E = an existing lemma or definition at 66fa526ea390 serves the case; M = it needs a MISSING
lemma below (L1-L14, G1-G5); X = the case FAILS as stated (a statement or design change is needed, named in the cell).

Image B: there is no lib/B/Prog/DgnTransportBCg.v (S10 B) and no image-B kit (S07) on 66fa526ea390
(`git ls-tree` of B/Prog lists DgnTransportBAddr / BList / BSyms, TImgB, TWorldB, TransportGRwB). Every B row cites the
image-A lemma; its B twin is pending S07 / S10 B (G twins: G_HARNESS_B B/TransportGB.v:19-39, G_HARNESS_B_in_hull
:44-45, G_HARNESS_B_rw B/Prog/TransportGRwB.v:13). Reusable/YCe5.v holds a second copy of the YCbq lemmas at other lines
(e.g. range_addressable_of_block YCe5.v:2195, frames_bounds :353) [INFERENCE: the B kit picks one of the two].

### Counts per case per walk (rows; E / M / X)

| image | function | rows | HEAP | FAKE | G | WIN |
|---|---|---|---|---|---|---|
| A | diginet_mac_is_digidesign | 0 | - | - | - | - |
| A | diginet_frame_is_keepalive | 0 | - | - | - | - |
| A | diginet_frame_parse | 25 | 25 / 0 / 0 | 19 / 6 / 0 | - | 18 / 7 / 0 |
| A | diginet_frame_build | 30 | - | 17 / 5 / 0 | 14 / 5 / 0 | 16 / 6 / 0 |
| A | diginet_announce_parse | 0 | - | - | - | - |
| A | diginet_cursor_init | 0 | - | - | - | - |
| A | diginet_msg_next | 13 | - | 12 / 1 / 0 | - | 12 / 1 / 0 |
| A | diginet_body_check | 17 | - | 13 / 4 / 0 | - | 11 / 1 / 5 |
| B | diginet_mac_is_digidesign | 0 | - | - | - | - |
| B | diginet_frame_is_keepalive | 0 | - | - | - | - |
| B | diginet_frame_parse | 37 | 37 / 0 / 0 | 23 / 14 / 0 | - | 22 / 15 / 0 |
| B | diginet_frame_build | 28 | - | 20 / 3 / 0 | 7 / 15 / 0 | 11 / 12 / 0 |
| B | diginet_announce_parse | 10 | 10 / 0 / 0 | 6 / 4 / 0 | - | 5 / 5 / 0 |
| B | diginet_cursor_init | 0 | - | - | - | - |
| B | diginet_msg_next | 9 | - | 7 / 2 / 0 | - | 7 / 2 / 0 |
| B | diginet_body_check | 15 | - | 11 / 4 / 0 | - | 9 / 1 / 5 |
| B | diginet_sum16 | 0 | - | - | - | - |
| B | rd32 | 0 | - | - | - | - |
| B | copy_strz | 0 | - | - | - | - |

(B frame_build row 149 is out only: it is counted in the Task 4 table, not in any case.)

### Findings beside the mapping

1. **send_control's empty body.** diginet_frame_build's statement has `body <> 0` (frame A diginet_frame_build_cg.v:146, B
   :162), and its code returns -1 only for `body = 0 with body_len <> 0` (frame A diginet_frame_build_cg.v:33-36). send_control
   passes body 0 with length 0 (listing fact), so the premise must become `0 < length bb -> body <> 0`; frame_build then
   calls diginet_body_check (0, 0), whose statement also has `body <> 0` (decode A diginet_body_check_cg.v:114). For n = 0, tso holds by
   its G (or RO) disjunct for any q (every pointwise disjunct and every decode_rd_ok conjunct is vacuous or numeric at
   q = 0, n = 0; the hull of [0, 0) is empty since SHADOW_OFF mod 8 = 0) [INFERENCE: checked by hand, not by Rocq];
   body_check must then drop `body <> 0` for len = 0 [INFERENCE: it reads no body byte when len = 0;
   diginet_cursor_init stores len 0 for body 0, decode A diginet_cursor_init_cg.v:88].
2. **WIN through an inner journal (L11).** tso's WIN disjunct is relative to (STK, sp0); body_check's walk calls
   msg_next at its own inner journal (FRAME_BC_STK, spZ regs) (decode A DgnBcLoopCall.v:313), whose window is below a
   caller-frame body. 5 of body_check's WIN cells are X for this and for L12.
3. **WIN shadow is decided by AR.** zero_shadow_ranges' first row is the machine stack (YG0n.v:189-190) and ARm keeps it
   0 at every AR state (am_zshadow YG0n.v:219): this answers step 1's open item 3 for W (L5), and g_s's payload row in
   Tfib_zero_shadow answers it for G (L6 + L7). F needs the frame-zone keep (L8).
4. **G bytes need no presence** (gx_rw_vis / gx_rw_writable, TransportGCg.v:83-99, decided by TransportGRwA.v:11), but
   their VALUES are not kept by acall_kept_g (image clause guarded by `~ inG G a`, TransportGCg.v:118-119): G3.
5. **frame_build's statement premise `frame_in_block out` was a heap block in the siblings** (step 1 open item 2): the
   G lift below replaces it by transport_twr_ok_g (TransportGCg.v:472-479) + trans_out_ok (G1); the decision text must
   say frame_in_block (frame A diginet_frame_build_cg.v:149, B :168), not frame_in_fake.

### Task 3: per-walk use sites -> case + lemma

#### A diginet_mac_is_digidesign

0 uses; nothing to map. Frame A, files _F_c _F _cg .v. **0 uses** (no `frame_in_block` in any of the four files). Leaf footprint walk; the input range [mac, mac + 3) is stated by: cg.v:69 `mac <> 0`, :71 `bytes_at rsegs m mac l`, :74 `off_stk sp ... mac 3`, :79 `addressable m mac 3`, :83-84 `ExecF.rng RNG mac 3` and its shadow range; the same premises in footprint form _F_c.v:33-48. READ only; no written block range.

#### A diginet_frame_is_keepalive

0 uses; nothing to map. Frame A, files _F_c _F _cg .v. **0 uses**. Input ranges stated by: cg.v:66 `0 <= body < 2^64`, :67-68 `bytes_at` of f + 30 and f + 32, :69 `bytes_at rsegs m body bb`, :76-77, :79, :81-82 `off_stk` / `addressable` of f + 30, f + 40, f + 32 and of `body 1`, :86-93 the `ExecF.rng` premises; footprint form _F_c.v:33-60. READ only.

#### A diginet_frame_parse


| file | line | lemma / proof | uses | derives | replacement from trans_src_ok | case | lemma (file:line) / MISSING |
|---|---|---|---|---|---|---|---|
| cg.v | 110 | frame_diginet_frame_parse_cg (:102-120) | premise `frame_in_block B lyc Sc buf (Z.of_nat (length b))` | where buf lives (the statement has frame_off_win only for f, :116) | STMT; add decode_off_win regs FRAME_FP_STK buf LEN (OFF rows below) | HEAP, FAKE, WIN | STMT: tso (DgnTransportCg.v:337-342) + offw (:317-318) |
| walk.v | 266 | Section Entry | Hypothesis Hblk | carries the premise | retype Hblk; add the off_win hypothesis | HEAP, FAKE, WIN | RETYPE: tso (DgnTransportCg.v:337-342) |
| walk.v | 967-968 | fp_walk | intros ... Hblk ...; eapply fp_entry; eassumption | - | PASS | HEAP, FAKE, WIN | PASS: none (no lemma) |
| walk.v | 296-303 | fp_blk | destruct Hblk (:299); al_blocks (:300) | block (bA, nA) in ablocks lyc Sc around buf; 4096 <= bA; bA + req_size nA <= alloc_ceiling; in_app bA | HEAP (only the heap branch has a block); the non-heap branch needs its own fp_nums (next row) | HEAP, FAKE, WIN | HEAPW — H: sibling text (YG0d.v:424-430); F/W: row absent in this branch; consumers as mapped |
| walk.v | 315-323 | fp_nums | destruct fp_blk (:318); in_app_sub (:322) | 4096 <= buf; buf + LEN <= alloc_ceiling; in_app buf LEN | 4096 <= buf: LO (consumers need only 0 < buf: R5 + Hbuf0); buf + LEN <= alloc_ceiling: R4/R6 for the numeric bounds, OFF for the window separation; in_app: INAPP | HEAP, FAKE, WIN | LO — H: YG0d.v:427; F: YCbq.v:451; W: YCbq.v:370 + :335; HIR — H: YG0d.v:427; F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw; INAPP — H: YG0d.v:427 (in_app); F: TransportFevt.v:462 (rd2, rd4, rd5); W: TransportFevt.v:462 (rd2, rd4, rd5); in_app FALSE |
| walk.v | 366-367 | fp_rng_buf | fp_nums; fp_rng [lia / lia /] | 0 <= buf, buf + LEN <= 2^64 (kit.v:133); visibility from Hgb (not the block) | R5, R6 | HEAP, FAKE, WIN | R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6 |
| walk.v | 378-386 | fp_shrng_buf | fp_nums N1 N2 (:380); fp_blk (:381); shadow_hull_vis_of_block (:382-383); fp_rng_hull bounds (:384) | shadow hull of [buf, buf + LEN) visible at memc (AR_shadow_law); 0 <= buf; buf + LEN <= 2^48 | R3 at memc; R5; R4 (q + n <= 2^47 - 1) | HEAP, FAKE, WIN | R3 — H: YCbq.v:1947; F/W: rd3; R5 — H: YG0d.v:427; F/W: rd5; R4 — H: YCbq.v:2014; F/W: rd4 |
| walk.v | 599, 601, 607-610 | fp_at_ret2 HBM | fp_nums, destruct fp_blk; HK4 (buf + i) with lia | buf + i not in fp_inwin [SP - FRAME_FP_STK, SP) (alloc_ceiling below it); not in [f, f + 12) (Hdisj, not the block) | OFF | HEAP, FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317) |
| walk.v | 613 | fp_at_ret2 PRE | lia | 0 < buf; buf + LEN <= 2^47 (fp_body_pre, segs.v:175) | POS (R5 + Hbuf0); R4 | HEAP, FAKE, WIN | POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427); R4 — H: YCbq.v:2014; F/W: rd4 |
| walk.v | 614 | fp_at_ret2 | fp_bytes_at_of_aview [lia / lia / HBM] | 0 <= buf; buf + LEN <= 2^64 | R5, R6 | HEAP, FAKE, WIN | R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6 |
| walk.v | 641-642 | fp_at_ret2 | fp_addressable W m4 buf LEN [range_addressable_of_block ... m4 md4 bA nA HAR4 HinA / lia / N5] | range_addressable of buf at m4 (the block shadow, AR at m4); in_app (N5) | R2 at memc carried to m4 by HK4 + KX as fp_ra_f (:426-435) does for f (KEEPSH inside the walk: satisfied); INAPP for N5 | HEAP, FAKE, WIN | R2 — H: YCbq.v:2689; F/W: rd2; WALKSH: walk carry (case-free; keep fact excludes [kLowMemEnd, kHighShadowEnd)); INAPP — H: YG0d.v:427 (in_app); F: TransportFevt.v:462 (rd2, rd4, rd5); W: TransportFevt.v:462 (rd2, rd4, rd5); in_app FALSE |
| walk.v | 646 | fp_at_ret2 | exact fp_rng_buf; exact (fp_shrng_buf L30) | rows fp_rng_buf, fp_shrng_buf | as those rows | HEAP, FAKE, WIN | AS: as the referenced row(s) |
| walk.v | 741, 743, 755-756 | fp_memcpy_call HBUF | fp_nums, fp_blk; HK3 with lia | [buf + j, buf + j + 6) not in fp_inwin; not in [f, f + j) (Hdisj) | OFF | HEAP, FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317); SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 776 | fp_memcpy_call | split; [lia/]. split; [lia/] | 0 <= buf + j; buf + j + 6 <= 2^63 (aj_intrin_at OCpy, YCbq.v:1970) | R5, R6 | HEAP, FAKE, WIN | R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6; SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 778-780 | fp_memcpy_call src_ok | fp_buf_memc (visible); rewrite SPM; lia | source bytes outside __asan_memcpy's window [SP - 48 - ESTACK, SP - 48) | OFF (visibility comes from Hgb, not the block) | HEAP, FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317); SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 782 | fp_memcpy_call | amem_range_of_block ... m3 bA nA (buf + j) 6 HAR3 HinA | amem_range (buf + j) 6 | R4 | HEAP, FAKE, WIN | R4 — H: YCbq.v:2014; F/W: rd4; SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 783 | fp_memcpy_call | range_addressable_of_block ... m3 ... HAR3 HinA | range_addressable of the source at m3 | R2 at memc + HK3/KX carry as fp_ra_f at :774 | HEAP, FAKE, WIN | R2 — H: YCbq.v:2689; F/W: rd2; WALKSH: walk carry (case-free; keep fact excludes [kLowMemEnd, kHighShadowEnd)); SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 784 | fp_memcpy_call | shadow_hull_vis_of_block ... m3 ... HAR3 HinA | shadow hull of the source at m3 | R3 at memc + HK3/KX carry as fp_hull_f at :775 | HEAP, FAKE, WIN | R3 — H: YCbq.v:1947; F/W: rd3; WALKSH: walk carry (case-free; keep fact excludes [kLowMemEnd, kHighShadowEnd)); SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 811, 834 | fp_at_ret1 | fp_nums; rewrite fp_u64 by lia | buf + 6 < 2^64 (register a1 of the second copy) | R5, R6 | HEAP, FAKE, WIN | R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6 |
| walk.v | 855-856, 866 | fp_entry | fp_nums, fp_blk; HEAD premise lia | 0 < buf (segs.v:105) | POS | HEAP, FAKE, WIN | POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427) |
| walk.v | 867 | fp_entry | lia | buf + LEN <= 2^47 (segs.v:105) | R4 | HEAP, FAKE, WIN | R4 — H: YCbq.v:2014; F/W: rd4 |
| walk.v | 869 | fp_entry | fp_bytes_at_of_aview [lia / lia / ...] | 0 <= buf; buf + LEN <= 2^64 | R5, R6 | HEAP, FAKE, WIN | R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6 |
| walk.v | 872-873 | fp_entry | off_stk sp FP_FRAME buf LEN: left; lia | buf + LEN <= SP - 48 (segs.v:108) | OFF | HEAP, FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317) |
| walk.v | 884-885 | fp_entry | fp_addressable W memc buf LEN [range_addressable_of_block ... memc ... fp_HAR0 HinA / lia / N5] | addressable memc buf LEN (segs.v:112) | R2 at memc; R5; INAPP for N5 (fp_addressable, kit.v:360-363, asks in_app form: restate over R4) | HEAP, FAKE, WIN | R2 — H: YCbq.v:2689; F/W: rd2; R5 — H: YG0d.v:427; F/W: rd5; INAPP — H: YG0d.v:427 (in_app); F: TransportFevt.v:462 (rd2, rd4, rd5); W: TransportFevt.v:462 (rd2, rd4, rd5); in_app FALSE |
| walk.v | 895-896 | fp_entry | exact fp_rng_buf; exact fp_shrng_buf | rows above | as those rows | HEAP, FAKE, WIN | AS: as the referenced row(s) |

#### A diginet_frame_build

Read inputs only (dst / src: G; body: F / W). The out rows are in the Task 4 table. In the G form the walk has no inner journal (Task 4), so its keeps are the KEEPFB routes and its body_check call needs no L11.

| file | line | lemma / proof | uses | derives | replacement from trans_src_ok | case | lemma (file:line) / MISSING |
|---|---|---|---|---|---|---|---|
| cg.v | 152 | frame_diginet_frame_build_cg (:135-169) | premise `frame_in_block B lyc Sc dst 6` | where the 6 bytes dmac live | STMT (+ decode_off_win regs FRAME_FB_STK dst 6) | G | STMTG: tso + offw; callers: DgnTransportCg.v:345 trans_src_ok_G_range |
| cg.v | 154 | same | premise `frame_in_block B lyc Sc src 6` | where smac lives | STMT (+ off_win) | G | STMTG: tso + offw; callers: DgnTransportCg.v:345 trans_src_ok_G_range |
| cg.v | 156 | same | premise `frame_in_block B lyc Sc body (length bb)` | where the body lives | STMT (+ off_win) | FAKE, WIN (+ len 0, body 0: send_control) | STMT: tso (DgnTransportCg.v:337-342) + offw (:317-318) |
| walk.v | 170, 173, 175 | Section Entry | Hypothesis Bdst, Bsrc, Bbody | carry the premises | retype | G, FAKE, WIN | RETYPE: tso (DgnTransportCg.v:337-342) |
| walk.v | 1384 | fb_walk | intros ... Bdst ... Bsrc ... Bbody ...; eapply fb_entry; eassumption | - | PASS | G, FAKE, WIN | PASS: none (no lemma) |
| walk.v | 290-309 | fb_blk_facts (takes frame_in_block q n) | destruct (:299); Permutation_in (:300); al_blocks (:301); range_addressable_of_block (:304); shadow_hull_vis_of_block (:305); amem_range_of_block (:306) | at any state (ly1, S1, W1, m1) whose blocks are a permutation of the call state's: bytes present (:303), range_addressable (:304), shadow hull (:305), amem_range (:306), 4096 <= q, q + n <= alloc_ceiling (:307), a 16-aligned block witness (:308) | non-heap twin: R1 + KEEP (to m1), R2 + KEEPSH, R3 + KEEPSH, R4, R5 (for 0 <= q), LO / HI (for :307); the witness: HEAP | G, FAKE, WIN | R1 — G: rd1 (or TransportGCg.v:91 gx_rw_vis, any memory); F/W: rd1; KEEPFB — G: G form: G3 (gx_kept_ex) / TransportGCg.v:291 gx_kept across body_check; F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw; R2: rd2; R3: rd3; KEEPSH — G: L6 + L7; F: L8; W: L5; R4: rd4; R5: rd5; LO — G: L2; F: YCbq.v:451; W: YCbq.v:370 + :335; HIR — G: L2 + YCbq.v:468; F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw; HEAPW: row absent in this branch; consumers as mapped |
| walk.v | 320-331 | fb_rfacts (takes frame_in_block q n) | fb_blk_facts (:326); frame_addressable_of (:327); frame_rng_vis (:329); fbk_rng_shadow (:330) | FC.addressable m1 q n; ExecF.rng of [q, q + n) and of its shadow bytes at W1 | as fb_blk_facts: R2 + R4 + R5 + KEEPSH; R1 + KEEP | G, FAKE, WIN | R2: rd2; R4: rd4; R5: rd5; KEEPSH — G: L6 + L7; F: L8; W: L5; R1 — G: rd1 (or TransportGCg.v:91 gx_rw_vis, any memory); F/W: rd1; KEEPFB — G: G form: G3 (gx_kept_ex) / TransportGCg.v:291 gx_kept across body_check; F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw |
| walk.v | 335-346 | fb_keep_blk (takes frame_in_block q n) | destruct; JI conjunct F2 (:341, :344) = the block clause of the inner journal (YCbq.v:361-362) | a byte of the block outside out's range keeps its view at every state of the inner journal JI | KEEP: JI's frame clause (YCbq.v:365-367) for a frame; image clause (:363-364) for G; >= alloc_ceiling clause (:359-360) for the window (above spZ regs, so outside JI's window: needs OFF) | G, FAKE, WIN | KEEPFB — G: G form: G3 (gx_kept_ex) / TransportGCg.v:291 gx_kept across body_check; F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw |
| walk.v | 348-362 | fb_val_at (takes frame_in_block q (length l)) | fb_blk_facts at memc (:357-358); fb_keep_blk (:359); fbk_garr8_aview [lia / lia / present] (:360-361) | the view of l at q at any JI state: bytes visible at memc, 0 <= q, q + n <= 2^64, kept by JI | R1, R5, R6; KEEP (fb_keep_blk row) | G, FAKE, WIN | R1 — G: rd1 (or TransportGCg.v:91 gx_rw_vis, any memory); F/W: rd1; R5: rd5; R6: rd6; KEEPFB — G: G form: G3 (gx_kept_ex) / TransportGCg.v:291 gx_kept across body_check; F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw |
| walk.v | 448-460 | fb_body_run | fb_blk_facts body (:454-455); fbk_bytes_of_aview (:456); frame_addressable_of (:457); frame_rng_vis (:458); fb_rfacts (:460) | bytes_at m1 body bb; FC.addressable m1 body blen; rng of body and of its shadow bytes at W1 | R1 + KEEP; R2 + R4 + R5 + KEEPSH; R6 | FAKE, WIN (+ len 0, body 0: send_control) | R1: rd1; KEEPFB — F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw; R2: rd2; R4: rd4; R5: rd5; KEEPSH — F: L8; W: L5; R6: rd6 |
| walk.v | 461-480 | fb_body_run (blen = 0) | block witness bA <> body (:467); range_addressable_of_block, amem_range_of_block of [body - 1, body) (:468-471) | for an empty body at an unaligned address, the shadow byte of body's granule is visible (taken from the byte before body, inside the block) | no replacement: decode_rd_ok of an empty range states nothing; needs the shadow byte of body's granule visible at m1 (new fact) | FAKE, WIN (+ len 0, body 0: send_control) | EMPTY — F: YG0d.v:454-456 (frame shadow bytes present) when body is inside the frame; W: L5 |
| walk.v | 595, 612 | fb_memcpy (takes frame_in_block x (length w)) | premise Hxb (:595); fb_blk_facts x (:612) | Xp Xra Xhull Xam Xlo Xhi of the copy source at m1 | retype premise to trans_src_ok + off_win; then the rows below | G, FAKE, WIN | RETYPE: tso (DgnTransportCg.v:337-342) |
| walk.v | 639 | fb_memcpy | split; [lia/]. split; [lia/] | 0 <= x; x + n <= 2^63 (YCbq.v:1970) | R5, R6 | G, FAKE, WIN | R5: rd5; R6: rd6 |
| walk.v | 640-643 | fb_memcpy src_ok | Hxv (visible: not the block); rewrite SPR; lia (Xlo, Xhi) | source outside __asan_memcpy's window [sp - 96 - ESTACK, sp - 96) | OFF | G, FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317) |
| walk.v | 644 | fb_memcpy | exact Xam; exact Xra; exact Xhull | amem_range, range_addressable, shadow hull of the source at m1 | R4; R2 + KEEPSH; R3 + KEEPSH (m1 is after the body_check call when x = body: FB_TAIL) | G, FAKE, WIN | R4: rd4; R2: rd2; R3: rd3; KEEPSH — G: L6 + L7; F: L8; W: L5 |
| walk.v | 879 | fb_at_tail | fb_blk_facts body (Bb1, Bb2) consumed by SEG4 lia (:896) | 0 < body < 2^64 (iface.v:476) | POS (Hbody0 + R5); R6 | FAKE, WIN (+ len 0, body 0: send_control) | POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427); R6: rd6 |
| walk.v | 915 | fb_at_tail | exact Bbody (fb_memcpy's :595) | - | PASS (as trans_src_ok + off_win) | FAKE, WIN (+ len 0, body 0: send_control) | PASS: none (no lemma) |
| walk.v | 917 | fb_at_tail | fb_val_at ... body bb J1 HP Bbody Dbody Gbb | row fb_val_at | as fb_val_at | FAKE, WIN (+ len 0, body 0: send_control) | AS: as the referenced row(s) |
| walk.v | 1037 | fb_at_sum | fb_blk_facts body (Bb1, Bb2) consumed by LOOPS lia (:1043-1044) | 0 < body; body + len <= 2^63 (iface.v:379) | POS; R6 | FAKE, WIN (+ len 0, body 0: send_control) | POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427); R6: rd6 |
| walk.v | 1038 | fb_at_sum | fb_body_run | row fb_body_run | as fb_body_run | FAKE, WIN (+ len 0, body 0: send_control) | AS: as the referenced row(s) |
| walk.v | 1111 | fb_at_retc1 | fb_blk_facts src (Bs1, Bs2) consumed by SEG3 lia (:1114) | 0 < src < 2^64 (iface.v:337) | POS; R6 | G | POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427); R6: rd6 |
| walk.v | 1133 | fb_at_retc1 | rewrite Lsmac; exact Bsrc (fb_memcpy's :595) | - | PASS | G | PASS: none (no lemma) |
| walk.v | 1135 | fb_at_retc1 | fb_val_at ... src smac ... Bsrc | row fb_val_at | as fb_val_at | G | AS: as the referenced row(s) |
| walk.v | 1152 | fb_at_retbc | fb_blk_facts dst (Bd1, Bd2) consumed by SEG2C lia (:1189) | 0 < dst < 2^64 (iface.v:319) | POS; R6 | G | POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427); R6: rd6 |
| walk.v | 1209 | fb_at_retbc | rewrite Ldmac; exact Bdst (fb_memcpy's :595) | - | PASS | G | PASS: none (no lemma) |
| walk.v | 1211 | fb_at_retbc | fb_val_at ... dst dmac ... Bdst | row fb_val_at | as fb_val_at | G | AS: as the referenced row(s) |
| walk.v | 1227-1228, 1249 | fb_bc_call | fb_blk_facts body (Bb1, Bb2); fbk_aview_garr8 [lia / lia /] | 0 <= body; body + len <= 2^64 | R5, R6 | FAKE, WIN (+ len 0, body 0: send_control) | R5: rd5; R6: rd6 |
| walk.v | 1248 | fb_bc_call | exact Bbody to ABC (frame A diginet_body_check_cg's frame_in_block premise) | - | CALLEE (inner journal FRAME_FB_STK (spZ regs), state lyc Sc W m1) | FAKE, WIN (+ len 0, body 0: send_control) | CALLEEFB: G form: same journal, TransportGCg.v:291 + L9a |
| walk.v | 1250 | fb_bc_call | fb_val_at lyc Sc W m1 md1 0 body bb ... Bbody | row fb_val_at | as fb_val_at | FAKE, WIN (+ len 0, body 0: send_control) | AS: as the referenced row(s) |
| walk.v | 1280-1283 | fb_entry | fb_blk_facts body, dst, src (bounds) consumed by SEG1 lia (:1312-1318) and SEG1L lia (:1351-1358) | 0 < q < 2^64 for dst, src, body (iface.v:234) | POS; R6 | G, FAKE, WIN | POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427); R6: rd6 |

#### A diginet_announce_parse

0 uses; nothing to map. Frame A, files _F_c _F _cg .v. **0 uses** (image A's text is a leaf statement). Input ranges stated by: cg.v:71 `0 < body < 2^64`, :72-73 `bytes_at` of f + 30 and f + 32 (body and length fields), :74 `bytes_at rsegs m body bb`, :76-77 `off_stk ... (f + 30) 18` / `(body + 15) 18`, :81 ap / body disjointness, :86-89 `addressable` of f + 30, f + 40, f + 32 and `(body + 15) 18`, :96-108 the `ExecF.rng` premises; footprint form _F_c.v:36-85. Body and f are READ only; ap is written (cg.v:79, :82, :90, :109-111, :114: a caller range, rw_cells + in_wr, not a block).

#### A diginet_cursor_init

0 uses; nothing to map. Decode A, files _F_c _F _cg (no .v in decode A). **0 uses**. The function reads no input range: body and len are values it stores into the cursor (cg.v:63-64 `a1 = body`, `0 <= body < 2^64`, `0 <= len < 2^64`). Its one range is the written cursor c: cg.v:66 `wr_at rsegs m c 25`, :67 `off_stk`, :71 `addressable m c 25`, :77-79 rng, :85 `~ aowned /\ ~ in_img` (a caller side-stack frame, not a block); _F_c.v:28, :51.

#### A diginet_msg_next


| file | line | lemma / proof | uses | derives | replacement from trans_src_ok | case | lemma (file:line) / MISSING |
|---|---|---|---|---|---|---|---|
| cg.v | 142 | decode_diginet_msg_next_cg (:128-153) | premise `(0 < length bb)%nat -> decode_in_block B lyc Sc body (length bb)` | where the body lives (c and m have decode_off_win at :147; body has none) | STMT (keep the `0 < length bb ->` guard); add `0 < length bb -> decode_off_win regs FRAME_MN_STK body L` | FAKE, WIN | STMT: tso (DgnTransportCg.v:337-342) + offw (:317-318) |
| walk_lib.v | 160 | Section Walk | Hypothesis Hblk | carries the premise | retype | FAKE, WIN | RETYPE: tso (DgnTransportCg.v:337-342) |
| walk.v | 34-37 | decode_diginet_msg_next_cg_holds | intros ... Hblk ...; eassumption into mw_main | - | PASS | FAKE, WIN | PASS: none (no lemma) |
| walk_lib.v | 261-282 | mw_blk | destruct (Hblk HL) (:267); al_blocks (:268); al_shadow (:269); Ham from in_app (:272-273); FF.decode_block_range_addressable (:274); FF.decode_addressable_of (:275); al_client_img (:279-280) | 4096 <= body; body + L <= alloc_ceiling; amem_range; bytes present; not in the image; FC.addressable memc body L; shadow bytes visible | non-heap twin = mw_rd (:222-231), which already derives R5, R6, R4, FC.addressable, shadow visible, R2, R3 from decode_rd_ok; present: R1; 4096 / alloc_ceiling: LO, OFF (consumers below); not-in-image (B5): no consumer (destructured at :642 only), drop | FAKE, WIN | MWRD: mw_rd (decode A walk_lib.v:222-231 / B :210-219) on rd; 4096 / ceiling via L3; R1: rd1; LO — F: YCbq.v:451; W: YCbq.v:370 + :335; HIR — F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw |
| walk_lib.v | 308-313 | mw_body_bytes | mw_blk B1 B2 B4 (:310); FF.decode_garr8_bytes [lia / lia / B4] (:311-312) | 0 <= body; body + L <= 2^64; bytes visible | R5, R6, R1 | FAKE, WIN | R5: rd5; R6: rd6; R1: rd1 |
| walk_lib.v | 356-364 | mw_rng_body | mw_blk B1 B2 B4 B7 (:360); FF.decode_rng_vis (:362); mw_shadow_rng_vis (:363) | rng of [body, body + L) (bounds, visible); rng of its shadow bytes (0 <= q, q + n <= 2^47, shadow visible) | R5, R6, R1; R4; shadow visible from mw_rd (R2) | FAKE, WIN | R5: rd5; R6: rd6; R1: rd1; R4: rd4; R2: rd2 |
| walk_lib.v | 378-383 | mw_off_body | mw_blk B1 B2 + mw_sp (:380); lia | off_stk (gr 2) MN_FRAME body L | OFF (as mw_off_c :366-370 does from Hoc) | FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317) |
| walk_lib.v | 426-430 | mw_entry_run | mw_blk B6 (:427); mw_body_bytes; mw_off_body (:428) | the body premises of mn_entry_F: bytes_at, FC.addressable memc body L, off_stk | via mw_rd (R2 + R4 + R5), R1, OFF | FAKE, WIN | R2: rd2; R4: rd4; R5: rd5; R1: rd1; OFF: offw (new premise, DgnTransportCg.v:317) |
| walk_lib.v | 438 | mw_entry_run | mw_rng_body | row mw_rng_body | as that row | FAKE, WIN | AS: as the referenced row(s) |
| walk_lib.v | 642, 813-814 | mw_call | mw_blk B1..B7 (:642); FF.decode_bytes_at_eq ... Rraw [lia / lia / lia / B4] | body bytes at mem2 (after __asan_memset) = at memc: body + i not in [sp - 128 - 4096, sp) (B2 + S1), not in [mp, mp + 40) (Hmb), present (B4) | OFF; R1 (Hmb is a statement premise) | FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317); R1: rd1 |
| walk_lib.v | 817 | mw_call | SHR body L B6 B7 | FC.addressable mem2 body L (its shadow bytes lie in the shadow region, kept by Rraw) | via mw_rd (FC.addressable, shadow visible); the carry to mem2 needs no block | FAKE, WIN | R2: rd2; R4: rd4; WALKSH: walk carry (case-free; keep fact excludes [kLowMemEnd, kHighShadowEnd)) |
| walk_lib.v | 818-820 | mw_call | mw_off_body | off_stk for mn_body_F | OFF | FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317) |
| walk_lib.v | 825-826 | mw_call | mw_rng_body | row mw_rng_body | as that row | FAKE, WIN | AS: as the referenced row(s) |

#### A diginet_body_check

The cut record bc_fix carries the premise (DgnBcCut.v:86 A / :90 B).

| file | line | lemma / proof | uses | derives | replacement from trans_src_ok | case | lemma (file:line) / MISSING |
|---|---|---|---|---|---|---|---|
| cg.v | 115 | decode_diginet_body_check_cg (:107-120) | premise `decode_in_block B lyc Sc body (length bb)` (with `body <> 0` :114) | where the body lives | STMT (+ decode_off_win regs FRAME_BC_STK body L) | FAKE, WIN | STMT: tso (DgnTransportCg.v:337-342) + offw (:317-318) |
| DgnBcCut.v | 86 | bc_fix (:78-91) | conjunct `decode_in_block B lyc Sc body (length bb)` | carries the premise into every piece | retype the conjunct | FAKE, WIN | RETYPE: tso (DgnTransportCg.v:337-342) |
| DgnBcHead.v | 428, 443-446 | bc_holds_of | intros ... Hblk; destruct Hblk (:443); al_blocks (:444); req_size_pos (:445); Hblen (:446) | 4096 <= body; body + len < 2^47; 0 < body | LO; R4/R6; POS (Hbody + R5) | FAKE, WIN | LO — F: YCbq.v:451; W: YCbq.v:370 + :335; R4: rd4; R6: rd6; POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427) |
| DgnBcHead.v | 765, 768, 815, 821-824 | bc_holds_of (cursor_init call) | Q11 = body, Q12 = len; LCI.decode_diginet_cursor_init_cg premises (lia) | 0 <= body, 0 <= len, each < 2^64 (cursor_init writes the cursor; body is a value here) | R5, R6 (body only as a stored value, not a read range) | FAKE, WIN | R5: rd5; R6: rd6 |
| DgnBcHead.v | 1001-1005 | bc_holds_of (Hgarr6) | garr8_frame; KBL = the inner journal block clause (:1003-1005) with HinA | the body bytes keep their view at the loop's state (ms6) | KEEP (inner journal block clause -> frame / image / window clause per L) | FAKE, WIN | KEEP — F: YCbq.v:365-367 / :833-835; W: YCbq.v:359-360 / :828 + offw |
| DgnBcHead.v | 1016-1017 | bc_holds_of | refine ... Hblk ... (builds bc_fix for the loop piece) | - | PASS | FAKE, WIN | PASS: none (no lemma) |
| DgnBcLoopCall.v | 191-192, 217-219 | bl_call | destruct HFIX (Hblk, :191); destruct Hblk (:217); Permutation_in (:218) | the body's block at the cut state (ly2, S2) | HEAP for the witness; the rest below | FAKE, WIN | HEAPW: row absent in this branch; consumers as mapped |
| DgnBcLoopCall.v | 220, 226 | bl_call | sep_block_frame (block vs the class-2 frame) | the body is disjoint from the frame F (the cursor c and message m live there) | DISJ (from L: the body is a block / G / outer frame, F is this call's own frame) | FAKE, WIN | DISJ — F: DgnTransportKept.v:204; W: YCbq.v:451 + :335 |
| DgnBcLoopCall.v | 265-266 | bl_call | Pblk := fun _ => exists bA nA ... HinA2 | re-establishes decode_in_block body at ly2 S2 for the msg_next callee | CALLEE: trans_src_ok body at the inner journal FRAME_BC_STK (spZ regs); the window disjunct does not carry (the outer window is above) | FAKE, WIN | CALLEE — F: L11; W: L11 does not apply: inner window [spZ regs - FRAME_BC_STK, spZ regs) is below the range |
| DgnBcLoopCall.v | 315 | bl_call | passes Pblk to MN (decode_diginet_msg_next_cg) | - | as CALLEE | FAKE, WIN | AS: as the referenced row(s) |
| DgnBcLoopCall.v | 359-362 | bl_call (after the call) | garr8_frame; K2 = acall_kept block clause (:362) with HinA2 | the body bytes kept across the msg_next call | KEEP (acall_kept frame / image / >= alloc_ceiling clause per L) | FAKE, WIN | KEEP — F: YCbq.v:365-367 / :833-835; W: YCbq.v:359-360 / :828 + offw |
| DgnBcLoopTest.v | 540, 544-547 | bl_test | HFIX Hblk (:540); destruct (:544); al_blocks (:546); req_size_pos (:547) | block at ly3 S3; 4096 <= body; body + len <= alloc_ceiling (Hl47 :549) | LO; HI (body + len <= bcs_PTRHI: FALSE for a window range); R4 | FAKE, WIN | LO — F: YCbq.v:451; W: YCbq.v:370 + :335; HIB — F: YCbq.v:451; W: FALSE for bcs_PTRHI = 0x7fffff800000: L12 (raise to 2^47 - 1, rd4); R4: rd4 |
| DgnBcLoopTest.v | 597-604 | bl_test | range_addressable_of_block [body + S cp] 3 (:597-598); HAapp -> HAPP (:599-601); bt_t2 (:602-604) | range_addressable of 3 body bytes at mem3; the 3 bytes outside the shadow region; 4096 <= body + S cp, + 3 <= bcs_PTRHI | R2 + KEEPSH (carried from memc across the msg_next call and loop); R4 (R4 implies outside the shadow region); LO, HI | FAKE, WIN | R2: rd2; KEEPSH — F: L8; W: L5; R4: rd4; LO — F: YCbq.v:451; W: YCbq.v:370 + :335; HIB — F: YCbq.v:451; W: FALSE for bcs_PTRHI = 0x7fffff800000: L12 (raise to 2^47 - 1, rd4); SUB: L4 (or YG0v.v:44 on rd2) |
| DgnBcScan.v | 690, 694-696 | bc_scan | HFIX Hblk (:690); destruct (:694); al_blocks (:696) | block at ly2 S2 | HEAP for witness; LO, HI, R4 below | FAKE, WIN | HEAPW: row absent in this branch; consumers as mapped; LO — F: YCbq.v:451; W: YCbq.v:370 + :335; HIB — F: YCbq.v:451; W: FALSE for bcs_PTRHI = 0x7fffff800000: L12 (raise to 2^47 - 1, rd4); R4: rd4 |
| DgnBcScan.v | 699-703 | bc_scan | range_addressable_of_block body L (:699-700); HAapp -> HAPP (:701-703) | range_addressable of the whole body at mem2; body outside the shadow region | R2 + KEEPSH; R4 | FAKE, WIN | R2: rd2; KEEPSH — F: L8; W: L5; R4: rd4 |
| DgnBcScan.v | 712 | bc_scan | bcs_head [4096 <= body / body + len <= bcs_PTRHI / HRA / HAPP] | the scan reads body bytes | LO; HI; R2 + KEEPSH; R4 | FAKE, WIN | LO — F: YCbq.v:451; W: YCbq.v:370 + :335; HIB — F: YCbq.v:451; W: FALSE for bcs_PTRHI = 0x7fffff800000: L12 (raise to 2^47 - 1, rd4); R2: rd2; KEEPSH — F: L8; W: L5; R4: rd4 |
| DgnBcRel.v | 223 | bc_rel | destruct HFIX (Hblk) | Hblk destructured, not used (the release reads no body byte) | PASS (drop the binder) | FAKE, WIN | PASS: none (no lemma) |

#### B diginet_mac_is_digidesign

0 uses; nothing to map. Frame B, files _F_c _F _cg .v. **0 uses**. Input range [mac, mac + 3) stated by cg.v:70 `mac <> 0`, :72 `bytes_at`, :75 `off_stk`, :80 `addressable`, :84-85 rng; _F_c.v:36-51. READ only.

#### B diginet_frame_is_keepalive

0 uses; nothing to map. Frame B, files _F_c _F _cg .v. **0 uses**. Input ranges stated by cg.v:72 `0 < body < 2^64`, :73-75 `bytes_at`, :82-88 `off_stk` / `addressable`, :92-99 rng (B adds the UBSan `f mod 8 = 0`, :71, and `0 < body`); _F_c.v:37-66. READ only.

#### B diginet_frame_parse

Image-A lemmas cited; B twins pending S07 / S10 B.

| file | line | lemma / proof | uses | derives | replacement from trans_src_ok | case | lemma (file:line) / MISSING |
|---|---|---|---|---|---|---|---|
| cg.v | 143 | frame_diginet_frame_parse_cg (:132-...) | premise `frame_in_block B lyc Sc buf (length b)` | where buf lives (f has frame_off_win :149; buf none) | STMT (+ decode_off_win regs FRAME_FP_STK buf LEN) | HEAP, FAKE, WIN | STMT: tso (DgnTransportCg.v:337-342) + offw (:317-318) |
| walk.v | 345 | Section Entry | Hypothesis Hblk | carries the premise | retype | HEAP, FAKE, WIN | RETYPE: tso (DgnTransportCg.v:337-342) |
| walk.v | 1402-1404 | fp_walk | intros ... Hblk ...; eapply fp_entry | - | PASS | HEAP, FAKE, WIN | PASS: none (no lemma) |
| walk.v | 375-382 | fp_blk | destruct Hblk (:378); al_blocks (:379) | the block around buf; 4096 <= bA; alloc_ceiling bound; in_app | HEAP for the witness; non-heap via fp_nums | HEAP, FAKE, WIN | HEAPW — H: sibling text (YG0d.v:424-430); F/W: row absent in this branch; consumers as mapped |
| walk.v | 394-402 | fp_nums | destruct fp_blk (:397); in_app_sub (:401) | 4096 <= buf; buf + LEN <= alloc_ceiling; in_app buf LEN | LO; R4/R6 + OFF; INAPP | HEAP, FAKE, WIN | LO — H: YG0d.v:427; F: YCbq.v:451; W: YCbq.v:370 + :335; HIR — H: YG0d.v:427; F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw; INAPP — H: YG0d.v:427 (in_app); F: TransportFevt.v:462 (rd2, rd4, rd5); W: TransportFevt.v:462 (rd2, rd4, rd5); in_app FALSE |
| walk.v | 445-446 | fp_rng_buf | fp_nums; fp_rng | 0 <= buf; buf + LEN <= 2^64 | R5, R6 | HEAP, FAKE, WIN | R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6 |
| walk.v | 457-464 | fp_shrng_buf | fp_nums (:459); fp_blk (:460); shadow_hull_vis_of_block (:461); fp_rng_hull (:463) | shadow hull of buf visible at memc; bounds | R3 + R5 + R4 | HEAP, FAKE, WIN | R3 — H: YCbq.v:1947; F/W: rd3; R5 — H: YG0d.v:427; F/W: rd5; R4 — H: YCbq.v:2014; F/W: rd4 |
| walk.v | 663-672 | fp_sh_vis_buf | fp_nums (:665); fp_blk (:666); range_addressable_of_block buf LEN (:667-668) | the shadow byte of each buf + i is visible at memc (from the block's range_addressable) | R2 | HEAP, FAKE, WIN | R2 — H: YCbq.v:2689; F/W: rd2 |
| walk.v | 691, 699-713 | fp_pre_keep | fp_nums N1..N7 (:691); fp_bytes_at_keep (buf, :699-700); fp_addressable_keep (buf, :709-710) | across a memory change outside this call's window, buf's bytes and shadow keep their view | the facts carried are R1/R2 (from the prior state); the exclusion `~ fp_inwin` uses N1 N2 = buf + LEN <= alloc_ceiling < window: OFF | HEAP, FAKE, WIN | R1 — H: YG0d.v:428 + YCbq.v:136; F/W: rd1; R2 — H: YCbq.v:2689; F/W: rd2; WALKSH: walk carry (case-free; keep fact excludes [kLowMemEnd, kHighShadowEnd)); OFF: offw (new premise, DgnTransportCg.v:317) |
| walk.v | 834-835, 852-855 | fp_rd32_call | fp_nums (:834); PRE (AB, R1-R3, :835); fp_bytes_at_skipn (:854) | the leaf rd32 reads [buf + p, buf + p + 4): bytes (R1), addressable (R2), rng | R1, R2 (carried in PRE / fp_mid); R4/R5 | HEAP, FAKE, WIN | R1 — H: YG0d.v:428 + YCbq.v:136; F/W: rd1; R2 — H: YCbq.v:2689; F/W: rd2; R4 — H: YCbq.v:2014; F/W: rd4; R5 — H: YG0d.v:427; F/W: rd5; SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 856-857 | fp_rd32_call | off_stk: rewrite USP; lia | buf + p outside the leaf rd32's 16-byte frame below SP - 80 | OFF | HEAP, FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317); SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 863 | fp_rd32_call | fp_addressable_sub m buf LEN (buf + p) 4 AB | a sub-range of buf is addressable | R2 (restated over the sub-range) | HEAP, FAKE, WIN | R2 — H: YCbq.v:2689; F/W: rd2; SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 867-868 | fp_rd32_call | ExecF.rng_sub' R1 (buf rng); R3 (buf shrng) | rng and shadow rng of the sub-range | R5/R6; R3 | HEAP, FAKE, WIN | R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6; R3 — H: YCbq.v:1947; F/W: rd3; SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 898-907, 920-924 | fp_sum16_call | fp_nums (:898); PRE (:899); fp_bytes_at_firstn/skipn (:905-907) | the leaf diginet_sum16 reads [buf + 30, buf + 30 + body_len): bytes, length, addressable | R1, R2; R6 | HEAP, FAKE, WIN | R1 — H: YG0d.v:428 + YCbq.v:136; F/W: rd1; R2 — H: YCbq.v:2689; F/W: rd2; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6; SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 925-926 | fp_sum16_call | off_stk: rewrite USP; lia | buf + 30 outside the sum16 frame | OFF | HEAP, FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317); SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 932-933 | fp_sum16_call | fp_addressable_sub m buf LEN (buf + 30) ... | sub-range of buf addressable | R2 | HEAP, FAKE, WIN | R2 — H: YCbq.v:2689; F/W: rd2; SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 937-940 | fp_sum16_call | ExecF.rng_sub' R1; R3 | rng and shadow rng of the body sub-range | R5/R6; R3 | HEAP, FAKE, WIN | R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6; R3 — H: YCbq.v:1947; F/W: rd3; SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 960 | fp_at_sumr | fp_nums N1..N7 | introduced; TAIL reads only the frame and f (buf parts unused here) | R5/R6 (the N's that bound buf are not consumed by TAIL) | HEAP, FAKE, WIN | R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6 |
| walk.v | 1091, 1093, 1099-1102 | fp_at_ret2 HBM | fp_nums, fp_blk; HK4 buf + i with lia | buf + i outside the window and [f, f + 12) (Hdisj) | OFF | HEAP, FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317) |
| walk.v | 1105 | fp_at_ret2 PRE | lia | 0 < buf; buf + LEN <= 2^47 | POS; R4 | HEAP, FAKE, WIN | POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427); R4 — H: YCbq.v:2014; F/W: rd4 |
| walk.v | 1106 | fp_at_ret2 | fp_bytes_at_of_aview | 0 <= buf; buf + LEN <= 2^64 | R5, R6 | HEAP, FAKE, WIN | R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6 |
| walk.v | 1133-1134 | fp_at_ret2 | fp_addressable W m4 buf LEN [range_addressable_of_block ... m4 / lia / N5] | range_addressable of buf at m4; in_app | R2 + KEEPSH (fp_ra_f-style carry); INAPP | HEAP, FAKE, WIN | R2 — H: YCbq.v:2689; F/W: rd2; WALKSH: walk carry (case-free; keep fact excludes [kLowMemEnd, kHighShadowEnd)); INAPP — H: YG0d.v:427 (in_app); F: TransportFevt.v:462 (rd2, rd4, rd5); W: TransportFevt.v:462 (rd2, rd4, rd5); in_app FALSE |
| walk.v | 1138 | fp_at_ret2 | fp_rng_buf; fp_shrng_buf L30 | rows above | as those rows | HEAP, FAKE, WIN | AS: as the referenced row(s) |
| walk.v | 1179, 1181, 1189-1190 | fp_memcpy_call HBUF | fp_nums, fp_blk; HK3 with lia | [buf + j, buf + j + 6) outside the window and [f, f + j) | OFF | HEAP, FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317); SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 1207 | fp_memcpy_call | destruct Hrd (amem_range of f, not buf); lia | n bound | R4 (for the f side; the buf side at :1210-1218) | HEAP, FAKE, WIN | R4 — H: YCbq.v:2014; F/W: rd4 |
| walk.v | 1210 | fp_memcpy_call | split; [lia/]. split; [lia/] | 0 <= buf + j; buf + j + 6 <= 2^63 | R5, R6 | HEAP, FAKE, WIN | R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6; SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 1211-1214 | fp_memcpy_call src_ok | fp_buf_memc (visible); rewrite SPM; lia | source outside __asan_memcpy's window | OFF | HEAP, FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317); SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 1216 | fp_memcpy_call | amem_range_of_block ... m3 (buf + j) 6 | amem_range of the source | R4 | HEAP, FAKE, WIN | R4 — H: YCbq.v:2014; F/W: rd4; SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 1217 | fp_memcpy_call | range_addressable_of_block ... m3 (buf + j) 6 | range_addressable at m3 | R2 + KEEPSH (fp_ra_f carry, :1208) | HEAP, FAKE, WIN | R2 — H: YCbq.v:2689; F/W: rd2; WALKSH: walk carry (case-free; keep fact excludes [kLowMemEnd, kHighShadowEnd)); SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 1218 | fp_memcpy_call | shadow_hull_vis_of_block ... m3 (buf + j) 6 | shadow hull at m3 | R3 + KEEPSH (fp_hull_f, :1209) | HEAP, FAKE, WIN | R3 — H: YCbq.v:1947; F/W: rd3; WALKSH: walk carry (case-free; keep fact excludes [kLowMemEnd, kHighShadowEnd)); SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| walk.v | 1245, 1268 | fp_at_ret1 | fp_nums; rewrite fp_u64 | buf + 6 < 2^64 (K18 = buf + 14 register? the second copy's a1) | R5, R6 | HEAP, FAKE, WIN | R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6 |
| walk.v | 1289-1290 | fp_entry | fp_nums, fp_blk | into HEAD | HEAP / non-heap as above | HEAP, FAKE, WIN | HEAPW — H: sibling text (YG0d.v:424-430); F/W: row absent in this branch; consumers as mapped |
| walk.v | 1300-1302 | fp_entry | HEAD premises lia | 0 < buf; buf + LEN <= 2^47 (segs.v:131) | POS; R4 | HEAP, FAKE, WIN | POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427); R4 — H: YCbq.v:2014; F/W: rd4 |
| walk.v | 1304 | fp_entry | fp_bytes_at_of_aview | 0 <= buf, buf + LEN <= 2^64 | R5, R6 | HEAP, FAKE, WIN | R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6 |
| walk.v | 1307-1308 | fp_entry | off_stk sp FP_FRAME buf LEN | buf + LEN <= SP - 80 | OFF | HEAP, FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317) |
| walk.v | 1319-1320 | fp_entry | fp_addressable W memc buf LEN [range_addressable_of_block ... / lia / N5] | addressable memc buf LEN | R2; R5; INAPP | HEAP, FAKE, WIN | R2 — H: YCbq.v:2689; F/W: rd2; R5 — H: YG0d.v:427; F/W: rd5; INAPP — H: YG0d.v:427 (in_app); F: TransportFevt.v:462 (rd2, rd4, rd5); W: TransportFevt.v:462 (rd2, rd4, rd5); in_app FALSE |
| walk.v | 1330-1331 | fp_entry | fp_rng_buf; fp_shrng_buf | rows above | as those rows | HEAP, FAKE, WIN | AS: as the referenced row(s) |

#### B diginet_frame_build

Image-A lemmas cited; B twins pending S07 / S10 B.
Read inputs only (dst / src: G; body: F / W). The out rows are in the Task 4 table. In the G form the walk has no inner journal (Task 4), so its keeps are the KEEPFB routes and its body_check call needs no L11.

| file | line | lemma / proof | uses | derives | replacement from trans_src_ok | case | lemma (file:line) / MISSING |
|---|---|---|---|---|---|---|---|
| cg.v | 171 | frame_diginet_frame_build_cg (:151-...) | premise `frame_in_block B lyc Sc dst 6` | where dmac lives | STMT (+ off_win) | G | STMTG: tso + offw; callers: DgnTransportCg.v:345 trans_src_ok_G_range |
| cg.v | 173 | same | premise `frame_in_block B lyc Sc src 6` | where smac lives | STMT (+ off_win) | G | STMTG: tso + offw; callers: DgnTransportCg.v:345 trans_src_ok_G_range |
| cg.v | 175 | same | premise `frame_in_block B lyc Sc body (length bb)` | where the body lives | STMT (+ off_win) | FAKE, WIN (+ len 0, body 0: send_control) | STMT: tso (DgnTransportCg.v:337-342) + offw (:317-318) |
| cuts.v | 111, 113, 115 | fbc_pre (:92-125) | conjuncts frame_in_block dst / src / body | carries the premises into the six pieces | retype the conjuncts | G, FAKE, WIN | RETYPE: tso (DgnTransportCg.v:337-342) |
| cuts.v | 350 | fb_holds_of_pieces | intros ... Hdblk Hsblk Hbblk ...; builds fbc_pre by tauto (:352-354) | - | PASS | G, FAKE, WIN | PASS: none (no lemma) |
| w_bc.v | 267-278 | fbwb_pre_facts | destruct PRE (:273-275); repackages Hdblk Hsblk Hbblk | the three block facts for the bc / copy pieces | PASS | G, FAKE, WIN | PASS: none (no lemma) |
| w_bc.v | 294-308 | fbwb_blk_of (takes frame_in_block q n) | destruct; Permutation_in (:301-302); al_blocks (:303) | block at (ly1, S1); 4096 <= p; alloc_ceiling; in_app; present | R1 + KEEP, LO, HI, INAPP (the witness: HEAP) | G, FAKE, WIN | R1 — G: rd1 (or TransportGCg.v:91 gx_rw_vis, any memory); F/W: rd1; KEEPFB — G: G form: G3 (gx_kept_ex) / TransportGCg.v:291 gx_kept across body_check; F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw; LO — G: L2; F: YCbq.v:451; W: YCbq.v:370 + :335; HIR — G: L2 + YCbq.v:468; F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw; INAPP — G/F: TransportFevt.v:462 (rd2, rd4, rd5); W: TransportFevt.v:462 (rd2, rd4, rd5); in_app FALSE; HEAPW: row absent in this branch; consumers as mapped |
| w_bc.v | 451-453, 507, 514-517, 569, 573-575 | fbwb_cpy / fbwb_fin / fbwb_path_c | fbwb_blk_of for out / dst / src / body | bounds and present bytes of each range | as fbwb_blk_of per range | G, FAKE, WIN | AS: as the referenced row(s) |
| w_bc.v | 487-489 | fbwb_cpy (source = dst/src) | amem_range_of_block, range_addressable_of_block, shadow_hull_vis_of_block of x (:487-489) | the __asan_memcpy source at m: R4, R2, R3 | R4; R2 + KEEPSH; R3 + KEEPSH | G | R4: rd4; R2: rd2; R3: rd3; KEEPSH: L6 + L7 |
| w_bc.v | 482-485 | fbwb_cpy src_ok | aview_some_of_apresent (present); rewrite SPM; lia | source visible and outside the copy window | R1; OFF | G | R1: rd1 (or TransportGCg.v:91 gx_rw_vis, any memory); OFF: offw (new premise, DgnTransportCg.v:317) |
| w_bc.v | 546-550 | fbwb_fin | KP (acall_kept-derived keep) with lia on dst / src / body bounds | dst, src, body bytes kept across the two copies | KEEP (the two copies write only out, so these are kept by the walk's own HV; bounds OFF/LO) | G, FAKE, WIN | KEEPFB — G: G form: G3 (gx_kept_ex) / TransportGCg.v:291 gx_kept across body_check; F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw; OFF: offw (new premise, DgnTransportCg.v:317); LO — G: L2; F: YCbq.v:451; W: YCbq.v:370 + :335 |
| w_entry.v | 210-234 | fbwe_block_bounds / fbwe_block_kept | al_blocks (:216); acall_kept block clause (:229, :232) | 4096 <= q, q + n <= alloc_ceiling; a block byte kept across an empty-write call | LO, HI; KEEP (frame / image / window clause per L) | G, FAKE, WIN | LO — G: L2; F: YCbq.v:451; W: YCbq.v:370 + :335; HIR — G: L2 + YCbq.v:468; F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw; KEEPFB — G: G form: G3 (gx_kept_ex) / TransportGCg.v:291 gx_kept across body_check; F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw |
| w_entry.v | 288, 306-311 | fbc_entry_of_segs | destruct PRE (:288); fbwe_block_bounds out/dst/src/body (:306-311) | the four ranges' bounds for the seg1 premises | LO, HI (the seg1 / seg1L premises need 0 < q < 2^64: POS + R6) | G, FAKE, WIN | LO — G: L2; F: YCbq.v:451; W: YCbq.v:370 + :335; HIR — G: L2 + YCbq.v:468; F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw; POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427); R6: rd6 |
| w_entry.v | 400-402, 455-460, 461-478 | fbc_entry_of_segs | fbwe_garr8_view of body (:400); fbwe_block_kept of out/dst/src/body (:459-478) across the body_check call | body bytes before and after the call keep their view | R1; KEEP per L | G, FAKE, WIN | R1 — G: rd1 (or TransportGCg.v:91 gx_rw_vis, any memory); F/W: rd1; KEEPFB — G: G form: G3 (gx_kept_ex) / TransportGCg.v:291 gx_kept across body_check; F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw |
| w_entry.v | 420 | fbc_entry_of_segs | exact Hbblk to RBC (frame A diginet_body_check_cg frame_in_block premise) | - | CALLEE (inner journal FRAME_FB_STK (spZ regs)) | FAKE, WIN (+ len 0, body 0: send_control) | CALLEEFB: G form: same journal, TransportGCg.v:291 + L9a |
| w_entry.v | 562, 572-573, 633-643 | fbc_entry_of_segs (seg1L -4 exit) | fbwe_block_bounds (lia); VOUT1 of out/dst/src/body (:633-643) | bounds and kept bytes on the early-exit path | POS/R6; KEEP (OFF for VOUT1's < alloc_ceiling bound) | G, FAKE, WIN | POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427); R6: rd6; KEEPFB — G: G form: G3 (gx_kept_ex) / TransportGCg.v:291 gx_kept across body_check; F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw; OFF: offw (new premise, DgnTransportCg.v:317) |
| w_hdr.v | 213-230 | fbwh_blk (takes frame_in_block q n) | Permutation_in; al_blocks | block at (ly1, S1); bounds; app_addr and present per byte | R1 + KEEP; LO, HI, INAPP | G, FAKE, WIN | R1 — G: rd1 (or TransportGCg.v:91 gx_rw_vis, any memory); F/W: rd1; KEEPFB — G: G form: G3 (gx_kept_ex) / TransportGCg.v:291 gx_kept across body_check; F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw; LO — G: L2; F: YCbq.v:451; W: YCbq.v:370 + :335; HIR — G: L2 + YCbq.v:468; F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw; INAPP — G/F: TransportFevt.v:462 (rd2, rd4, rd5); W: TransportFevt.v:462 (rd2, rd4, rd5); in_app FALSE |
| w_hdr.v | 281-298, 311-314, 320-331 | fbwh_state_leaf | destruct PRE (:297); fbwh_blk dst/src/body (:311-314); HAPP (:309-310); keep across the sum16 leaf | dst, src, body addresses in [4096, sp - FRAME_FB_STK) so kept outside the leaf window | KEEP; the `< sp - FRAME_FB_STK` uses app_addr_below_ceil: OFF + HI | G, FAKE, WIN | KEEPFB — G: G form: G3 (gx_kept_ex) / TransportGCg.v:291 gx_kept across body_check; F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw; OFF: offw (new premise, DgnTransportCg.v:317); HIR — G: L2 + YCbq.v:468; F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw |
| w_hdr.v | 357, 370-371, 427-442 | fbwh_h1 | destruct PRE; fbwh_blk out (:370-371); fbwh_blk dst/src/body (:427-429); keep across the fb_h1 run (:434-442) | out's block for the h1 stores; dst/src/body kept across the run | the dst/src/body rows: KEEP; out: written (see note) | G, FAKE, WIN | KEEPFB — G: G form: G3 (gx_kept_ex) / TransportGCg.v:291 gx_kept across body_check; F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw; OUT: out: Task 4 table |
| w_hdr.v | 497, 539-540, 562-585 | fbwh_sum | destruct PRE; fbwh_blk body at mem2 (:539-540); dgn_leafb leaf premises for body (:562-585) | the leaf diginet_sum16 reads the body: 0 < body (:563), bytes (:564), off_stk (:569), addressable block (:575-576), rng block (:583), shadow rng block (:585) | POS; R1; OFF; R2 + R4 + KEEPSH; R5/R6; R3 + KEEPSH | FAKE, WIN (+ len 0, body 0: send_control) | POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427); R1: rd1; OFF: offw (new premise, DgnTransportCg.v:317); R2: rd2; R4: rd4; KEEPSH — F: L8; W: L5; R5: rd5; R6: rd6; R3: rd3 |
| w_h2.v | 133-142 | fbw2_in_block_bounds | al_blocks | 4096 <= q; q + n <= alloc_ceiling | LO, HI | G, FAKE, WIN | LO — G: L2; F: YCbq.v:451; W: YCbq.v:370 + :335; HIR — G: L2 + YCbq.v:468; F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw |
| w_h2.v | 154, 176-179 | fbc_h2_of_segs | destruct PRE (:154); fbw2_in_block_bounds dst/src/body (:176-179) | the three ranges' bounds (used in the lia of the kept-garr8 steps) | LO, HI, R5/R6 | G, FAKE, WIN | LO — G: L2; F: YCbq.v:451; W: YCbq.v:370 + :335; HIR — G: L2 + YCbq.v:468; F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw; R5: rd5; R6: rd6 |
| w_h2.v | 349-356 | fbc_h2_of_segs | fbw2_garr8_keep of dst/src/body across the h2 stores (lia uses the bounds) | dst, src, body bytes kept (the stores write only out + 16 .. out + 30) | KEEP (the walk's own munch; bounds R5/R6) | G, FAKE, WIN | KEEPFB — G: G form: G3 (gx_kept_ex) / TransportGCg.v:291 gx_kept across body_check; F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw; R5: rd5; R6: rd6 |
| w_tail.v | 430-433, 470-474 | fbwt_write_step | destruct PRE (:459); HBLK from al_blocks (:470-474) | 4096 <= q, q + n <= alloc_ceiling for out / dst / src / body | LO, HI | G, FAKE, WIN | LO — G: L2; F: YCbq.v:451; W: YCbq.v:370 + :335; HIR — G: L2 + YCbq.v:468; F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw |
| w_tail.v | 442, 537-555 | fbwt_write_step (source = body) | premise frame_in_block x (:442); al_blocks (:540-541); amem_range / range_addressable / shadow_hull of x (:549-554); present + outside window (:544-547) | the body __asan_memcpy source at mem1 | R4; R2 + KEEPSH; R3 + KEEPSH; R1; OFF | FAKE, WIN (+ len 0, body 0: send_control) | R4: rd4; R2: rd2; R3: rd3; KEEPSH — F: L8; W: L5; R1: rd1; OFF: offw (new premise, DgnTransportCg.v:317) |
| w_tail.v | 574-581 | fbwt_write_step (after) | fbwt_garr8_kept of dst/src/body (lia HKEPT) | kept across the write | KEEP (HKEPT below alloc_ceiling: LO/HI) | G, FAKE, WIN | KEEPFB — G: G form: G3 (gx_kept_ex) / TransportGCg.v:291 gx_kept across body_check; F: G form: tracker cl.4 (TransportGCg.v:113-125 via :569-860); W: G form: tracker cl.1 (TransportGCg.v:113-115) + offw; LO — G: L2; F: YCbq.v:451; W: YCbq.v:370 + :335; HIR — G: L2 + YCbq.v:468; F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw |
| w_tail.v | 639-660 | fbwt_from_c3 | destruct PRE; al_blocks out only | out's bounds for the padding run | written (see note) | out (written; Task 4) | out: Task 4 table (G2) |
| w_tail.v | 845-846, 857-863, 938, 964-967 | fbc_tail_of_segs | HBB2 body (:846, :857); al_blocks (:859-860); S4 lia (:938); fbwt_write_step premise (:964) rebuilding frame_in_block body; fbwt_view_of_bytes (:966-967) | the body __asan_memcpy: bounds, source visibility | R5/R6 (938); retype premise (964) + R1 (967) | FAKE, WIN (+ len 0, body 0: send_control) | R5: rd5; R6: rd6; RETYPE: tso (DgnTransportCg.v:337-342); R1: rd1 |

#### B diginet_announce_parse

Image-A lemmas cited; B twins pending S07 / S10 B.

| file | line | lemma / proof | uses | derives | replacement from trans_src_ok | case | lemma (file:line) / MISSING |
|---|---|---|---|---|---|---|---|
| cg.v | 170 | frame_diginet_announce_parse_cg (:152-181) | premise `frame_in_block B lyc Sc body (length bb)` (with `0 < body` :165) | where the body lives (f and ap read as frame_rd_ok/off_win :169, :176; body has none) | STMT (+ decode_off_win regs FRAME_ANP_STK body L) | HEAP, FAKE, WIN [INFERENCE] | STMT: tso (DgnTransportCg.v:337-342) + offw (:317-318) |
| cgW.v | 617 | anp_holds (:611-...) | intros ... Hblk ... | carries the premise | retype | HEAP, FAKE, WIN [INFERENCE] | RETYPE: tso (DgnTransportCg.v:337-342) |
| cgW.v | 633-637 | anp_holds | destruct Hblk (:633); al_blocks (:634); req_size_pos (:636); Hbbc (:637) | block (bA, nA); 4096 <= body; body + len <= alloc_ceiling | HEAP for witness; LO; HI/R4/R6 | HEAP, FAKE, WIN [INFERENCE] | HEAPW — H: sibling text (YG0d.v:424-430); F/W: row absent in this branch; consumers as mapped; LO — H: YG0d.v:427; F: YCbq.v:451; W: YCbq.v:370 + :335; HIR — H: YG0d.v:427; F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw; R4 — H: YCbq.v:2014; F/W: rd4; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6 |
| cgW.v | 725-728 | anp_holds (anp_entry_b) | anp_f32_vals (:725); anp_entry_b with lia (:726-728) | 1 <= body <= 2^47; 0 <= len <= 2^47 (keeps the UBSan body=0 and wrap checks not taken, cg.v:162-164) | POS (0 < body is a statement premise); R4/R6 | HEAP, FAKE, WIN [INFERENCE] | POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427); R4 — H: YCbq.v:2014; F/W: rd4; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6 |
| cgW.v | 953-959 | anp_holds (GB15) | GB (body slices, :953-956); anp_garr8_kept of body + 15 (:957-959) with KCc | the version-field source body + 15 bytes visible, kept across the runs | R1; KEEP (walk's KCc; frame/image/window per L outside this file) | HEAP, FAKE, WIN [INFERENCE] | R1 — H: YG0d.v:428 + YCbq.v:136; F/W: rd1; KEEPW: walk keep (KCc/KDd, copy_strz post) + offw for W |
| cgW.v | 1012 | anp_holds (copy 1) | can_leafb_addressable_block ... msC bA nA (:1012) | addressable of the body source at msC | R2 + R4 + KEEPSH | HEAP, FAKE, WIN [INFERENCE] | R2 — H: YCbq.v:2689; F/W: rd2; R4 — H: YCbq.v:2014; F/W: rd4; KEEPSH — H: YCbq.v:2689 / :1947 at the later AR state; F: L8; W: L5; SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| cgW.v | 1019-1020 | anp_holds (copy 1) | can_leafb_rng_block / rng_shadow_block ... msC | rng and shadow rng of the body source at msC | R1 + R5/R6; R3 + KEEPSH | HEAP, FAKE, WIN [INFERENCE] | R1 — H: YG0d.v:428 + YCbq.v:136; F/W: rd1; R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6; R3 — H: YCbq.v:1947; F/W: rd3; KEEPSH — H: YCbq.v:2689 / :1947 at the later AR state; F: L8; W: L5; SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| cgW.v | 1109-1111 | anp_holds (GB24) | GB; anp_garr8_kept of body + 24 with KDd | the name-field source body + 24 bytes visible | R1; KEEP | HEAP, FAKE, WIN [INFERENCE] | R1 — H: YG0d.v:428 + YCbq.v:136; F/W: rd1; KEEPW: walk keep (KCc/KDd, copy_strz post) + offw for W |
| cgW.v | 1167 | anp_holds (copy 2) | can_leafb_addressable_block ... msD bA nA | addressable of body + 24 at msD | R2 + R4 + KEEPSH | HEAP, FAKE, WIN [INFERENCE] | R2 — H: YCbq.v:2689; F/W: rd2; R4 — H: YCbq.v:2014; F/W: rd4; KEEPSH — H: YCbq.v:2689 / :1947 at the later AR state; F: L8; W: L5; SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |
| cgW.v | 1174-1175 | anp_holds (copy 2) | can_leafb_rng_block / rng_shadow_block ... msD | rng and shadow rng at msD | R1 + R5/R6; R3 + KEEPSH | HEAP, FAKE, WIN [INFERENCE] | R1 — H: YG0d.v:428 + YCbq.v:136; F/W: rd1; R5 — H: YG0d.v:427; F/W: rd5; R6 — H: YG0d.v:427 + YCbq.v:468; F/W: rd6; R3 — H: YCbq.v:1947; F/W: rd3; KEEPSH — H: YCbq.v:2689 / :1947 at the later AR state; F: L8; W: L5; SUB — H: sibling text (the block lemmas take the sub-range); F/W: L4 (or YG0v.v:44 on rd2) |

#### B diginet_cursor_init

0 uses; nothing to map. Decode B, files _F_c _F _cg .v _cgW. **0 uses**. Reads no input range; body and len are stored values (cg.v:63-64). Written cursor c: cg.v:69 `wr_at`, :70 `off_stk`, :74 `addressable`, :80-82 rng, :87 `~ aowned /\ ~ in_img` (B adds UBSan `c mod 8 = 0`, :67). _cgW.v is the record wrapper (no block). A caller side-stack frame, not a block.

#### B diginet_msg_next

Image-A lemmas cited; B twins pending S07 / S10 B.

| file | line | lemma / proof | uses | derives | replacement from trans_src_ok | case | lemma (file:line) / MISSING |
|---|---|---|---|---|---|---|---|
| cg.v | 160 | decode_diginet_msg_next_cg (:143-171) | premise `(0 < length bb)%nat -> decode_in_block B lyc Sc body (length bb)` | where the body lives (c, m have off_win :165; body none) | STMT (+ `0 < length bb -> decode_off_win regs FRAME_MN_STK body L`) | FAKE, WIN | STMT: tso (DgnTransportCg.v:337-342) + offw (:317-318) |
| walk_lib.v | 148 | Section Walk | Hypothesis Hblk | carries the premise | retype | FAKE, WIN | RETYPE: tso (DgnTransportCg.v:337-342) |
| cgW.v | 52, 55 | decode_diginet_msg_next_cg_holds_any | intros ... Hblk ...; passes it to mw_main (:54-55) | - | PASS | FAKE, WIN | PASS: none (no lemma) |
| walk_lib.v | 247-268 | mw_blk | destruct (Hblk HL) (:253); al_blocks (:254); al_shadow (:255); Ham (:258-259); decode_block_range_addressable (:260); decode_addressable_of (:261); al_client_img (:265-266) | 4096 <= body; body + L <= alloc_ceiling; amem_range; present; not in image; FC.addressable memc body L; shadow visible | mw_rd twin (:210-219): R4 R5 R6 FC.addressable R2 R3; R1 for present; LO/OFF; not-in-image (B5) unused, drop | FAKE, WIN | MWRD: mw_rd (decode A walk_lib.v:222-231 / B :210-219) on rd; 4096 / ceiling via L3; R1: rd1; LO — F: YCbq.v:451; W: YCbq.v:370 + :335; HIR — F: YCbq.v:451; W: FALSE (q >= alloc_ceiling, YCbq.v:335): restate the lemma as L3's disjunction; its window consumers use offw |
| walk_lib.v | 294-299 | mw_body_bytes | mw_blk B1 B2 B4; decode_garr8_bytes | 0 <= body; body + L <= 2^64; visible | R5, R6, R1 | FAKE, WIN | R5: rd5; R6: rd6; R1: rd1 |
| walk_lib.v | 342-350 | mw_rng_body | mw_blk B1 B2 B4 B7; decode_rng_vis; mw_shadow_rng_vis | rng of body and of its shadow bytes | R5/R6/R1; R4; R2 | FAKE, WIN | R5: rd5; R6: rd6; R1: rd1; R4: rd4; R2: rd2 |
| walk_lib.v | 364-369 | mw_off_body | mw_blk B1 B2 + mw_sp; lia | off_stk body | OFF | FAKE, WIN | OFF: offw (new premise, DgnTransportCg.v:317) |
| walk_lib.v | 411-413 | mw_entry_run | mw_blk B1 (:411); `0 < body` (:412); mw_body_bytes; B6; mw_off_body (:413) | mn_entry_F body premises, including `0 < body` (B's UBSan, segs.v:101) | POS (B1 = 4096 <= body gives it: LO); R1; R2+R4; OFF | FAKE, WIN | POSM: L3 (no `body <> 0` premise in the statement); R1: rd1; R2: rd2; R4: rd4; OFF: offw (new premise, DgnTransportCg.v:317) |
| walk_lib.v | 423 | mw_entry_run | mw_rng_body | row mw_rng_body | as that row | FAKE, WIN | AS: as the referenced row(s) |

#### B diginet_body_check

Image-A lemmas cited; B twins pending S07 / S10 B.
The cut record bc_fix carries the premise (DgnBcCut.v:86 A / :90 B).

| file | line | lemma / proof | uses | derives | replacement from trans_src_ok | case | lemma (file:line) / MISSING |
|---|---|---|---|---|---|---|---|
| cg.v | 126 | decode_diginet_body_check_cg (:118-...) | premise `decode_in_block B lyc Sc body (length bb)` (`body <> 0` :114/:123) | where the body lives | STMT (+ off_win) | FAKE, WIN | STMT: tso (DgnTransportCg.v:337-342) + offw (:317-318) |
| DgnBcCut.v | 90 | bc_fix | conjunct decode_in_block body | carries into each piece | retype | FAKE, WIN | RETYPE: tso (DgnTransportCg.v:337-342) |
| DgnBcHead.v | 434, 449-452 | bc_holds_of | intros Hblk; destruct (:449); al_blocks (:450); req_size_pos (:451); Hblen (:452) | 4096 <= body; body + len < 2^47; 0 < body | LO; R4/R6; POS | FAKE, WIN | LO — F: YCbq.v:451; W: YCbq.v:370 + :335; R4: rd4; R6: rd6; POS: the statement's `q <> 0` + rd5 (H: YG0d.v:427) |
| DgnBcHead.v | 1008-1012 | bc_holds_of (Hgarr6) | garr8_frame; KBL block clause (:1012) | body bytes kept at the loop state | KEEP per L | FAKE, WIN | KEEP — F: YCbq.v:365-367 / :833-835; W: YCbq.v:359-360 / :828 + offw |
| DgnBcHead.v | 1023-1024 | bc_holds_of | refine ... Hblk | - | PASS | FAKE, WIN | PASS: none (no lemma) |
| DgnBcLoopCall.v | 197, 223-226 | bl_call | destruct HFIX Hblk (:197); destruct (:223); Permutation_in (:224); sep_block_frame (:226) | block at ly2 S2; disjoint from frame F | HEAP witness; DISJ | FAKE, WIN | HEAPW: row absent in this branch; consumers as mapped; DISJ — F: DgnTransportKept.v:204; W: YCbq.v:451 + :335 |
| DgnBcLoopCall.v | 271-272 | bl_call | Pblk := exists bA nA ... HinA2 | re-establishes decode_in_block body for the msg_next callee | CALLEE (inner journal) | FAKE, WIN | CALLEE — F: L11; W: L11 does not apply: inner window [spZ regs - FRAME_BC_STK, spZ regs) is below the range |
| DgnBcLoopCall.v | 324 | bl_call | passes Pblk to MN | - | as CALLEE | FAKE, WIN | AS: as the referenced row(s) |
| DgnBcLoopCall.v | 368-371 | bl_call (after call) | garr8_frame; K2 acall_kept block clause (:371) | body bytes kept across the call | KEEP per L | FAKE, WIN | KEEP — F: YCbq.v:365-367 / :833-835; W: YCbq.v:359-360 / :828 + offw |
| DgnBcLoopTest.v | 548, 552-554 | bl_test | HFIX Hblk (:548); destruct (:552); al_blocks (:554); Hl47 (:557) | block at ly3 S3; 4096 <= body; body + len <= bcs_PTRHI | LO; R4; HI (FALSE for window) | FAKE, WIN | LO — F: YCbq.v:451; W: YCbq.v:370 + :335; R4: rd4; HIB — F: YCbq.v:451; W: FALSE for bcs_PTRHI = 0x7fffff800000: L12 (raise to 2^47 - 1, rd4) |
| DgnBcLoopTest.v | 605-612 | bl_test | range_addressable_of_block [body + S cp] 3 (:605-606); HAPP (:607-609); bt_t2 (:610-612) | range_addressable of 3 body bytes at mem3; outside shadow; 4096 <= body + S cp, + 3 <= bcs_PTRHI | R2 + KEEPSH; R4; LO, HI | FAKE, WIN | R2: rd2; KEEPSH — F: L8; W: L5; R4: rd4; LO — F: YCbq.v:451; W: YCbq.v:370 + :335; HIB — F: YCbq.v:451; W: FALSE for bcs_PTRHI = 0x7fffff800000: L12 (raise to 2^47 - 1, rd4); SUB: L4 (or YG0v.v:44 on rd2) |
| DgnBcScan.v | 773, 777-779 | bc_scan | HFIX Hblk (:773); destruct (:777); al_blocks (:779) | block at ly2 S2 | HEAP witness; LO/HI/R4 below | FAKE, WIN | HEAPW: row absent in this branch; consumers as mapped; LO — F: YCbq.v:451; W: YCbq.v:370 + :335; HIB — F: YCbq.v:451; W: FALSE for bcs_PTRHI = 0x7fffff800000: L12 (raise to 2^47 - 1, rd4); R4: rd4 |
| DgnBcScan.v | 782-786 | bc_scan | range_addressable_of_block body L (:782-783); HAPP (:784-786) | range_addressable of the body at mem2; outside shadow | R2 + KEEPSH; R4 | FAKE, WIN | R2: rd2; KEEPSH — F: L8; W: L5; R4: rd4 |
| DgnBcScan.v | 794 | bc_scan | bcs_head [4096 <= body / body + len <= bcs_PTRHI / HRA / HAPP] | the scan reads body bytes | LO; HI; R2 + KEEPSH; R4 | FAKE, WIN | LO — F: YCbq.v:451; W: YCbq.v:370 + :335; HIB — F: YCbq.v:451; W: FALSE for bcs_PTRHI = 0x7fffff800000: L12 (raise to 2^47 - 1, rd4); R2: rd2; KEEPSH — F: L8; W: L5; R4: rd4 |
| DgnBcRel.v | 229 | bc_rel | destruct HFIX (Hblk) | destructured, not used | PASS (drop binder) | FAKE, WIN | PASS: none (no lemma) |

#### B diginet_sum16

0 uses; nothing to map. Frame B, files _F_c _F _cg .v. **0 uses**. Input range [p, p + length bb) stated by cg.v:72 `p <> 0`, :73 `bytes_at rsegs m p bb`, :76 `bb <> [] -> off_stk ... p (length bb)`, :81 `bb <> [] -> addressable m p (length bb)`, :88-90 the conditional rng premises; _F_c.v:33-51. READ only. (diginet_sum16 is a leaf; transport reaches it only through frame_build / frame_parse, which supply these from the buffer's facts.)

#### B rd32

0 uses; nothing to map. Frame B, files _F_c _F _cg .v. **0 uses**. Input range [p, p + 4) stated by cg.v:71 `4 <= length l`, :72 `bytes_at rsegs m p l`, :75 `off_stk ... p 4`, :80 `addressable m p 4`, :84-85 rng; _F_c.v:31-45. READ only.

#### B copy_strz

0 uses; nothing to map. Frame B, files _F_c _F _cg .v. **0 uses**. Input range [src, src + 9) stated by cg.v:68 `src <> 0`, :69 `bytes_at rsegs m src s`, :73 `off_stk ... src 9`, :78 `addressable m src 9`, :85-86 rng; _F_c.v:36-54. src READ; dst written (cg.v:70, :74, :79, :88-89, :94: a caller range, rw_cells + in_wr, not a block). (A leaf; transport reaches it through announce_parse.)

## Lemmas needed (Task 3)

All new lemmas of DgnTransportCg.v go in Section cj (A/Prog/DgnTransportCg.v:291-373: `Context {fx} {rc}`, `Variable B`,
`segs := tfibsegs`, `tfib_sink_head := AE2k.tfib_sink_head`) unless the text says otherwise; record facts are
Definitions over `B : asyms` beside trans_ro_rd_unowned (A/Prog/DgnTransportCg.v:171-174), decided at the closing record.
Image B: each twin goes in lib/B/Prog/DgnTransportBCg.v (S10 B) over TransportGB.v G_HARNESS_B; pending S07 / S10 B.

### L1 `trans_src_ok_rd` (A/Prog/DgnTransportCg.v) — decode_rd_ok from every case
```coq
Lemma trans_src_ok_rd : AR_laws segs B -> forall STK sp0 lyc Sc (W : world segs) memc mdc q n,
  @AR rc segs B lyc Sc W memc mdc -> trans_src_ok STK sp0 lyc Sc W memc q n -> 0 < n ->
  decode_rd_ok W memc q n.
```
Proof: the non-heap disjunct carries decode_rd_ok (:342); the heap disjunct: al_blocks (YG0d.v:427-428) for R1 (with
aview_some_of_apresent YCbq.v:136), R5, R6 (asan_consts YCbq.v:468); range_addressable_of_block (YCbq.v:2689),
shadow_hull_vis_of_block (YCbq.v:1947), amem_range_of_block (YCbq.v:2014) (nA <= req_size nA).
Sites: optional for every R1-R6 row (the per-case cells name the direct route); needed where a lemma is restated over
decode_rd_ok only (fp_nums, mw_blk -> mw_rd, fbwb_blk_of, fbwh_blk, bc_holds_of).

### L2 `inG_G_HARNESS_hull` (A/Prog/DgnTransportCg.v) — bounds of a G byte
```coq
Lemma inG_G_HARNESS_hull : forall a, W_journalG.inG TransportG.G_HARNESS a ->
  TransportG.G_HARNESS_LO <= a < TransportG.G_HARNESS_HI.
```
From G_HARNESS_in_hull (A/TransportG.v:37-38). B twin over G_HARNESS_B_in_hull (B/TransportGB.v:44-45).
Sites: every LO / HI cell with case G (frame_build dst, src: rows 31, 129, 134, 135, 139, 143, 144, 146, 148).

### L3 `trans_src_ok_place` (A/Prog/DgnTransportCg.v) — LO / HI / POS for every case
```coq
Lemma trans_src_ok_place : AR_laws segs B ->
  forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k q n,
  @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  trans_src_ok STK sp0 lyc Sc W memc q n -> 0 < n ->
  (4096 <= q /\ q + n <= alloc_ceiling) \/ (alloc_ceiling <= sp0 - STK <= q /\ q + n <= sp0).
```
Proof per case: HEAP al_blocks (YG0d.v:427); FAKE frames_bounds (YCbq.v:451); G L2 + asan_consts (YCbq.v:468);
WIN astk_ok (YCbq.v:335, the journal's conjunct :370); RO every TRANS_RO_RD range lies in [0x10350, 0xa3ed0)
(DgnTransportCg.v:110, by vm_compute). Sites: every HIR / POSM cell and the WIN restatements (fp_nums rows 5, 90;
mw_blk rows 59, 164; the frame_build bound lemmas rows 31, 129, 134, 139, 143, 146; announce row 153).

### L4 `trans_src_ok_sub` (A/Prog/DgnTransportCg.v) — sub-range
```coq
Lemma trans_src_ok_sub : forall STK sp0 lyc Sc (W : world segs) memc q n q' n',
  trans_src_ok STK sp0 lyc Sc W memc q n -> q <= q' -> 0 < n' -> q' + n' <= q + n ->
  trans_src_ok STK sp0 lyc Sc W memc q' n'.
```
Proof: each location disjunct shrinks; decode_rd_ok shrinks (range_addressable_sub YG0v.v:44; the hull of the
sub-range lies in the hull; amem_range, 0 <= q', q' + n' <= 2^63 by lia). Also the off-window twin
`decode_off_win regs FSTK q n -> q <= q' -> q' + n' <= q + n -> decode_off_win regs FSTK q' n'` (by lia).
Sites: every SUB cell (frame_parse A rows 13-18, B rows 95-102, 109-115; announce rows 156-160; body_check rows 81, 180).

### L5 `stack_zshadow_ra` (A/Prog/DgnTransportCg.v) — WIN: the shadow at any AR state
```coq
Lemma stack_zshadow_ra : forall ly S (W : world segs) mem md q n,
  @AR rc segs B ly S W mem md -> 0 < n -> ly_stk_lo ly mod 8 = 0 ->
  ly_stk_lo ly <= q / 64 * 64 -> (q + n - 1) / 64 * 64 + 64 <= ly_stk_hi ly ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q n /\ shadow_hull_vis (aview segs (w_H W) mem) q n.
```
Proof: ARm's am_zshadow (Reusable/YG0n.v:219) at the first row of zero_shadow_ranges, the machine stack
(Reusable/YG0n.v:189-190), read granule by granule as decode_zshadow_rd does (DgnTransportCg.v:191-207). Callers get
the two rounding premises from astk_ok (YCbq.v:335) and decode_off_win [INFERENCE: ly_stk_lo page-aligned].
Sites: every KEEPSH cell with case W (rows 31, 32, 35, 40, 81, 83, 84, 131, 142, 147, 156-160, 180, 182, 183) and row 36.

### L6 `decode_zshadow_ra` (A/Prog/DgnTransportCg.v, beside decode_zshadow_rd) — G / RO: the shadow at any AR state
```coq
Lemma decode_zshadow_ra {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md (lo hi q n : Z) :
  @AR rc tfibsegs B ly S W mem md -> decode_zshadow_at B lo hi -> 0 < n ->
  lo <= q / 64 * 64 -> (q + n - 1) / 64 * 64 + 64 <= hi ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF q n /\ shadow_hull_vis (aview tfibsegs (w_H W) mem) q n.
```
Proof: decode_zshadow_rd (DgnTransportCg.v:191-207) at each granule T of the hull. Sites: KEEPSH cells with case G
(frame_build dst / src: rows 31, 32, 40, 131) and the out shadow of Task 4 (G out).

### L7 `trans_gs_zshadow` (A/Prog/DgnTransportCg.v record fact) — g_s's payload has 0 shadow
```coq
Definition trans_gs_zshadow (B : asyms) : Prop := decode_zshadow_at B 0x5df9c0 (0x5df9c0 + 18264).
```
(or a conjunct of transport_cells, DgnTransportCg.v:216-260). Decided at the record: ts_zsh (A/AF0m.v:3138) and the
row (0x5df9c0, 0x5e4118 - 0x5df9c0) of Tfib_zero_shadow (A/AF0m.v:3104-3105) (checked here: g_s = (0x5df9c0, 18264),
A/TransportG.v:22; 18264 = 8 * 2283). dmac / smac = g_s + 120 / g_s + 0 and their 64-byte hulls lie inside it.
Image B: the g_s row of G_HARNESS_B (B/TransportGB.v:19-39) against image B's record, pending S07.

### L8 `decode_rd_ok_fake_kept` (A/Prog/DgnTransportCg.v) — FAKE: rd across a memory change that keeps the frame zone
```coq
Lemma decode_rd_ok_fake_kept : AR_laws segs B -> forall lyc Sc (W W' : world segs) memc mem' mdc q n,
  @AR rc segs B lyc Sc W memc mdc -> decode_in_fake lyc Sc q n -> decode_rd_ok W memc q n -> 0 < n ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) memc a) ->
  decode_rd_ok W' mem' q n.
```
Proof: hull_inside (Reusable/YG0s.v:753) with the frame 64-aligned (dk_frame_al64 DgnTransportKept.v:38 /
dkg_frame_al64 TransportGCg.v:691), the pattern of fuzz_frame B diginet_frame_build_w_entry.v:165-171 fbwe_rd_ok_win. The keep premise is
acall_kept's frame clause (YCbq.v:833-835) when E misses the zone, or ajournal's (YCbq.v:365-367).
Sites: every KEEPSH cell with case F.

### L9a `trans_src_ok_view` (A/Prog/DgnTransportCg.v) — the same placement at a later memory (own runs)
```coq
Lemma trans_src_ok_view : forall STK sp0 lyc Sc (W W2 : world segs) memc mem2 q n,
  trans_src_ok STK sp0 lyc Sc W memc q n ->
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s) ->
  trans_src_ok STK sp0 lyc Sc W2 mem2 q n.
```
Proof: the location disjuncts do not mention memory; decode_rd_ok's R1 by the first keep, R2 / R3 by the second
(shadow_addr_bounds YCbq.v:466; R4 keeps every shadow byte of the range in the band). Sites: frame_build's
body_check call in the G form (rows 53, 137): the prologue writes only [sp - 96, sp).

### L9b `trans_src_ok_acall` (A/Prog/DgnTransportCg.v) — every case across a donor callee (acall_kept)
```coq
Lemma trans_src_ok_acall : AR_laws segs B -> trans_g_unowned B -> trans_g_no_errno B ->
  trans_ro_rd_unowned B -> trans_rom_no_errno B -> transport_cells B -> trans_gs_zshadow B ->
  forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k
         ly2 S2 (W2 : world segs) mem2 md2 slo shi (E : Z -> Prop) q n,
  @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  @acall_kept rc segs B lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, q <= a < q + n -> ~ E a) -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok STK sp0 lyc Sc W memc q n -> 0 < n ->
  trans_src_ok STK sp0 ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
```
Proof per case: HEAP acall_kept cl.2 (YCbq.v:829-830) + AR_shadow_law at ly2 S2 (YCbq.v:2689, :1947); FAKE cl.4
(:833-835) + L8; G cl.3 (:831-832) with L10 + L6 / L7 (the G range must lie in g_s; a read of another global needs its
row); WIN cl.1 (:828) + L5; RO cl.3 with trans_ro_rd_scoped (DgnTransportCg.v:178) + the zshadow / const rows of
transport_cells. The G-form twin `trans_src_ok_acall_g` (same text with `acall_kept_g G_HARNESS ...`
(TransportGCg.v:113) in place of acall_kept and the premise `gx_kept G_HARNESS W memc W2 mem2` (TransportGCg.v:164)
for the G case) belongs where both files are visible (DgnTransportCg.v with `Require TransportGCg`) [INFERENCE].
Sites: every KEEP cell (rows 33, 34, 73, 79, 133, 134, 136, 138, 140, 141, 145, 148, 173, 178) and the KEEPSH cells
after a callee.

### L10 `trans_g_unowned`, `trans_g_no_errno`, `G_HARNESS_gx_ok` (A/Prog/DgnTransportCg.v) — the G instance facts
```coq
Definition trans_g_unowned (B : asyms) : Prop :=
  forall a, W_journalG.inG TransportG.G_HARNESS a -> ~ Exists (in_zr a) (as_owned_static B).
Definition trans_g_no_errno (B : asyms) : Prop :=
  forall a, W_journalG.inG TransportG.G_HARNESS a -> ~ (as_errno B <= a < as_errno B + 4).
Lemma G_HARNESS_gx_ok : trans_g_unowned B -> W_journalG.gx_ok tfibsegs B TransportG.G_HARNESS.
```
gx_ok (W_journalG.v:88-89) asks in_img and not owned; in_img from G_HARNESS_rw (TransportGRwA.v:11, gx_rwb reads the
byte from a loaded segment, TransportGCg.v:52-55); trans_g_no_errno is gx_noerrno B G_HARNESS (TransportGCg.v:167).
Decided at the record: ts_owned (A/AF0m.v:3133, Tfib_owned_static :3106-3113 holds the globals' redzones, not their
payloads) and ts_errno (A/AF0m.v:3124, TFIB_ERRNO = 0x5f3a4c, A/AF0m.v:25, above G_HARNESS_HI = 0x5f3190).
Sites: every KEEP cell with case G; gx_call_cg (TransportGCg.v:291) and gx_intrin_at (:506) in Task 4.

### L11 `trans_src_ok_inner` (A/Prog/DgnTransportCg.v) — CALLEE: to a callee whose caller journal is an inner journal
```coq
Lemma trans_src_ok_inner : forall STK sp0 lyc Sc (W : world segs) memc STK1 sp1 ly2 S2 (W2 : world segs) mem2 q n,
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  (forall cid pos, In (cid, pos) (frames Sc) -> In (cid, pos) (frames S2) /\ frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  (decode_in_block lyc Sc q n \/ decode_rd_ok W2 mem2 q n) ->
  trans_src_ok STK sp0 lyc Sc W memc q n ->
  ~ (sp0 - STK <= q /\ q + n <= sp0) \/ (sp1 - STK1 <= q /\ q + n <= sp1) ->
  trans_src_ok STK1 sp1 ly2 S2 W2 mem2 q n.
```
Sites: rows 77, 78 (A body_check -> msg_next), 176, 177 (B). The WIN case does not transfer: body_check's inner journal
(DgnBcCut.v:100-101 A, FRAME_BC_STK at spZ regs) has its window below the body, which lies in the caller's frame
(decode_off_win). MISSING (design), one of: (a) the WIN disjunct of trans_src_ok (DgnTransportCg.v:341) becomes
`(ly_stk_lo lyc <= q /\ q + n <= ly_stk_hi lyc)` (the machine stack of the current layout; it transfers to an inner
journal, acall_kept cl.1 keeps it off the callee window, L5 gives its shadow); or (b) body_check's walk passes msg_next
its caller's journal (no inner journal: the G-form pattern of Task 4). frame_build's call of body_check needs no L11 in
the G form (rows 53, 137: same journal, L9a).

### L12 `bcs_PTRHI` (walk text, decode A / B DgnBcScan.v:69 / :79) — WIN body above the allocator ceiling
The scan's pointer fact `bcs_PTR := mkAF 4096 bcs_PTRHI 0` (A DgnBcScan.v:69-70) bounds body by 0x7fffff800000 (the top
of alloc_ceiling); a WIN body may lie up to ly_stk_hi <= 2^47 (YCbq.v:335-336). Change bcs_PTRHI to 2^47 - 1
(= kHighMemEnd - 1, what rd4 gives) and re-run the scan / loop-test token checks (bcs_Bspan (SHADOW_OFF, SHADOW_OFF +
2^44 - 1), DgnBcScan.v:65, still covers x / 8 for x < 2^47) [INFERENCE: the fact only bounds the shadow-address
arithmetic]. Sites: rows 80, 81, 82, 84 (A), 179, 180, 181, 183 (B).

### L14 `trans_src_ok_disj_own` (A/Prog/DgnTransportCg.v) — a read range apart from the callee's own new frame
```coq
Lemma trans_src_ok_disj_own : AR_laws segs B ->
  forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k ly2 S2 (W2 : world segs) mem2 md2
         cid pos q n,
  @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  @AR rc segs B ly2 S2 W2 mem2 md2 -> frames S2 = (cid, pos) :: frames Sc ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> (forall c p, frame_addr ly2 c p = frame_addr lyc c p) ->
  trans_src_ok STK sp0 lyc Sc W memc q n -> 0 < n ->
  q + n <= frame_addr ly2 cid pos \/ frame_addr ly2 cid pos + fs_frame_bytes cid <= q.
```
Optional (each case has an existing route, rows 76, 175): HEAP sep_block_frame (YCbq.v:430); FAKE dk_own_sep
(DgnTransportKept.v:204); G frm_img (YCbq.v:215) with gx_ok; WIN frames_bounds (YCbq.v:451) + astk_ok (:335).

## Task 4: diginet_frame_build in the G form (both images)

Target: the statement premises become `ajournal_gx tfibsegs B G_HARNESS 0 [] STK sp0 ...` (W_journalG.v:203-209), `transport_twr_ok_g B G_HARNESS STK sp0 FP ly S lyc Sc own W memc (spZ regs - FRAME_FB_FRAME) out cap` (TransportGCg.v:472-479) and `trans_out_ok lyc Sc W memc out cap` (G1); the post is `transport_cg_post MT G_HARNESS ... regs FRAME_FB_STK FRAME_FB_EV 0 (fun a => out <= a < out + cap) X` (TransportGCg.v:228-240). The walk keeps no inner journal: it runs in the caller's G journal (each own run by ajournal_gx_exec, W_journalG.v:297-306; each copy / fill by gx_intrin_at, TransportGCg.v:506; body_check by gx_call_cg, :291; B's diginet_sum16 by gx_call_leaf, :317) and carries the post's keep as a tracker KP : `acall_kept_g G_HARNESS lyc Sc W memc W m (spZ regs - FRAME_FB_STK) (spZ regs) Eout` (TransportGCg.v:113-125; dk_kept_refl_g :569, dk_kept_trans_g :578, dk_kept_step_g :601, dk_kept_run_g :643) plus G3 for G.

**The footprint question.** The sibling's inner journal has footprint [(out, out + cap)], a caller block, and composes back by ajournal_sub (YCbq.v:726-731) / ajournal_sub_awr (DgnTransportCJ.v:173-178), whose condition is that each footprint byte is a caller-block byte (fuzz_frame B diginet_frame_build_w_epi.v:68-101 fbwp_fp_ok). In the G form out is G (send_data) or a caller frame (send_control): ajournal_gx_sub (W_journalG.v:478-487) asks the same block condition of the inner footprint (:485-486), so an inner journal with footprint [(out, ..)] does not compose, and an inner journal with footprint [] cannot write a caller frame (its awr_byte has own = [], YCbq.v:461-465). So no inner journal: G out bytes are written under awr_ok_x's / ajournal_gx_exec's `inG G a` branch (W_journalG.v:263, :304-305), caller-frame out bytes under the caller's awr_byte (`in_frames own`, YCbq.v:465) that transport_twr_ok_g gives; the prologue frame under awr_byte's window branch (YCbq.v:462). A machine-stack out (send_control fallback) is the window branch of awr_byte, writable, but acall_kept_g forbids it in the post: G4.

### Image A (frame A: _cg _iface _kit _seg_a _seg_h1 _seg_h2a _seg_h2b _seg_loop _walk)

| file | line | lemma / proof | out fact used | replacement (S08 / W_journalG file:line) or MISSING |
|---|---|---|---|---|
| cg.v | 118-128 | frame_fb_post (via frame_cg_post :123) | the post: frame_cg_post, acall_kept with E = [out, out + cap) | transport_cg_post (TransportGCg.v:228-240) with E := fun a => out <= a < out + cap; X += gx_kept_ex G_HARNESS E (G3, MISSING) |
| cg.v | 146 | frame_diginet_frame_build_cg | `out <> 0` | keep |
| cg.v | 149 | frame_diginet_frame_build_cg | `frame_in_block B lyc Sc out (length oj)` | MISSING G1 `trans_out_ok lyc Sc W memc out cap` (placement FAKE \/ G + decode_rd_ok of out) |
| cg.v | 150 | frame_diginet_frame_build_cg | `frame_twr_ok ... (spZ regs - FRAME_FB_FRAME) out cap` | transport_twr_ok_g B G_HARNESS STK sp0 FP ly S lyc Sc own W memc (spZ regs - FRAME_FB_FRAME) out cap (TransportGCg.v:472-479) |
| cg.v | 135-169 (journal premise) | frame_diginet_frame_build_cg | `ajournal STK sp0 ...` (DgnFrameCg journal) | ajournal_gx tfibsegs B G_HARNESS 0 [] STK sp0 ... (W_journalG.v:203-209) |
| cg.v | 158-159, 163 | frame_diginet_frame_build_cg | hp + 4: frame_in_fake, frame_rd_ok, off_win; Dhdr (out vs hp + 4) | decode_in_fake / decode_rd_ok / decode_off_win (DgnTransportCg.v:329, :311, :317), unchanged; out and h may share send_control's class-2 frame: Dhdr keeps them apart |
| cg.v | 171-181 | frame_diginet_frame_build_cg_holds_stmt | premises AR_laws, aintrin_realizes x2, the body_check contract | add gx_ok tfibsegs B G_HARNESS and gx_noerrno B G_HARNESS (L10, MISSING), G_HARNESS_rw (TransportGRwA.v:11); body_check's contract in decode_cg_post form taken by gx_call_cg (TransportGCg.v:291) through G5 |
| kit.v | 168-180 | fbk_aj_md | ajournal_exec at Wr = empty on the inner journal | ajournal_gx_materialize (W_journalG.v:341) on the caller's G journal |
| kit.v | 182-195 | fbk_aj_write | ajournal_exec, written bytes awr_byte of the inner journal | ajournal_gx_exec (W_journalG.v:297-306): each written byte awr_byte of the caller's journal and not in [sp0, sp0 + 0), or inG G |
| iface.v, seg_a.v, seg_h1.v, seg_h2a.v, seg_h2b.v, seg_loop.v | - | footprint statements | no out block fact (they take rw_cells / addressable / rng of out ranges as premises, e.g. iface.v:349-371) | none |
| walk.v | 130-131 | Hypothesis ABC | body_check contract in frame's cg form (PBC.frame_diginet_body_check_cg) | decode's body_check statement (decode_cg_post, DgnTransportCg.v:360) through gx_call_cg (TransportGCg.v:291); G5 |
| walk.v | 165 | Hypothesis Hbo | frame_in_block out | Hout : trans_out_ok (G1, MISSING) |
| walk.v | 166-167 | Hypothesis Htwr | frame_twr_ok out | transport_twr_ok_g (TransportGCg.v:472) |
| walk.v | 192-193 | Local Abbreviation POST | frame_fb_post | transport_cg_post (TransportGCg.v:228) |
| walk.v | 194-195 | Local Abbreviation JI | inner ajournal FRAME_FB_STK (spZ regs) [(out, out + cap)] | none: the walk holds the caller's ajournal_gx G 0 [] STK sp0 (W_journalG.v:203) plus the tracker KP : acall_kept_g G lyc Sc W memc W1 m1 (spZ regs - FRAME_FB_STK) (spZ regs) Eout (TransportGCg.v:113-125) and gx_kept_ex G Eout (G3) |
| walk.v | 204-206 | fb_st | JI /\ frames /\ Permutation /\ mo_le /\ fb_frame | ajournal_gx ... ly1 S1 W1 m1 md1 k /\ KP /\ G3 /\ frames /\ Permutation /\ mo_le /\ fb_frame (new definition in walk.v) |
| walk.v | 260-271 | fb_JI0 | ajournal_sub_init (YCbq.v:1829) with FP [(out, out + cap)] | HJ itself; KP by dk_kept_refl_g (TransportGCg.v:569); G3 refl |
| walk.v | 273-277 | fb_sp | bounds from JI's astk_ok | gx_open (TransportGCg.v:257) then YCbq.v:370 with Hwlo, Hwhi |
| walk.v | 279-283 | fb_win | JI presence of [spZ regs - FRAME_FB_STK, spZ regs) | gx_open (TransportGCg.v:257) then YCbq.v:369 (the caller window contains it by Hwlo, Hwhi) |
| walk.v | 285-287 (uses :610, :673, :934, :985, :1073) | fb_in_block_sub | a sub-range of out's block | G2s trans_out_ok_sub (MISSING); the write right is pointwise (TransportGCg.v:472) |
| walk.v | 311-317 (uses :386, :515, :534, :568, :605, :668, :728, :825, :877, :929, :980, :1070, :1109, :1150, :1226, :1279) | fb_out_far | Hbo + al_blocks: 4096 <= out, out + cap <= alloc_ceiling, out + cap <= kLowShadowBeg \/ kHighMemBeg <= out | G2 trans_out_ok_far (MISSING) |
| walk.v | 379-397 | fb_keep_hdr | JI frame clause (F4) for hp + 4 and its shadow; fb_out_far | KP clause 4 (TransportGCg.v:120-122) with ~ Eout (Dhdr; shadow zone not in out by G2) |
| walk.v | 485-498 | fb_frame_kept | JI presence (fb_win) | caller presence (YCbq.v:369 via gx_open) |
| walk.v | 500-506 | fb_st_md | fbk_aj_md | ajournal_gx_materialize (W_journalG.v:341) |
| walk.v | 509-528 | fb_st_write | fb_blk_facts out (present); fbk_aj_write with awr_byte block branch (:521-523) | ajournal_gx_exec (W_journalG.v:297) with the write right from transport_twr_ok_g (awr_byte of the caller's journal, or inG G); KP by dk_kept_step_g (TransportGCg.v:601) at Zs = [lo, hi) within Eout; G3 step; presence: transport_twr_ok_g (frame out) / gx_rw_vis, gx_rw_writable (TransportGCg.v:91, :83) (G out) |
| walk.v | 532-539 | fb_outv0 | fb_blk_facts out: out's bytes present at memc | transport_twr_ok_g apresent (frame out); gx_rw_vis (TransportGCg.v:91) (G out) |
| walk.v | 565-576 | fb_outv_rw | fb_out_far; presence | G2; presence as above |
| walk.v | 589-653 | fb_memcpy (destination out + kk) | fb_blk_facts out (:607-608), fb_in_block_sub (:609-610), Dp Dra Dhull Dam (:611), aj_intrin_at with JI (:617-619), awr_byte block branch (:631-635) | gx_intrin_at (TransportGCg.v:506) at the caller's journal, o = spZ regs - 96 - sp0; dest right transport_twr_ok_g at spZ rg (= the statement's sp); dest amem_range / range_addressable / hull from trans_out_ok's rd4 / rd2 / rd3 (G1, G2s), carried across body_check (F: L8; G: L6 + L7); gx_ok (L10), gx_rw (TransportGRwA.v:11); KP by dk_kept_step_g (Zs = dest + ESTACK below sp - 96) |
| walk.v | 656-710 | fb_memset (destination) | as fb_memcpy (:670-674, :679-681, :693-700) | as fb_memcpy, op OSet |
| walk.v | 721-787 | fb_at_epi | fbk_aj_md (:745); unfold frame_fb_post / frame_cg_post (:746); DgnFrameCJ.ajournal_sub_awr with Htwr (:751-754); acall_kept_of_journal on JI (:778-782) | ajournal_gx_materialize; transport_cg_post (TransportGCg.v:228); ajournal_sub_awr: none (the walk's journal is the caller's, count k + 0); acall_kept_of_journal: none (KP is the post's acall_kept_g) |
| walk.v | 819-1139 | fb_at_retc3 / tail / h2b / h2 / sum / retc2 / retc1 | fb_out_far; fb_blk_facts out Op (:933, :984, :1072); fb_rfacts (out + 12) via fb_in_block_sub (:934-935, :985-986, :1073-1074); fb_st_write (:965, :1020, :1093) | G2; presence as fb_outv0; FC.addressable / rng / shadow rng of out + 12 from trans_out_ok rd (decode_leafb_addressable DgnTransportLeafb.v:366, decode_leafb_rng_vis :420, decode_leafb_rng_shadow :426) after G2s, with KEEPSH across body_check (L8 / L6 + L7); fb_st_write as above |
| walk.v | 1143-1214 | fb_at_retbc | fb_out_far (:1150) | G2 |
| walk.v | 1217-1271 | fb_bc_call | JI premise (:1217); fb_out_far (:1226); ABC with JI (:1235); out kept by Hbo + acall_kept block clause (:1266-1270) | caller's ajournal_gx at m1; G2; gx_call_cg (TransportGCg.v:291) with (STK, sp0), FSTK = FRAME_BC_STK, window by Hwlo and fb_stk (walk.v:54); out kept: frame out by the dcg_post acall_kept frame clause (YCbq.v:833-835, E empty), G out by gx_kept of gx_call_cg (TransportGCg.v:291-299); KP across the call: acall_kept_g_of (TransportGCg.v:126) + dk_kept_trans_g (:578) |
| walk.v | 1274-1376 | fb_entry | fb_JI0 (:1277); fb_win (:1278); fb_out_far (:1279); Hfw awr_byte stack branch on JI (:1295-1297); fbk_aj_write (:1330, :1366) | HJ; caller presence; G2; awr_byte stack branch of the caller's journal (YCbq.v:461-462, Hwlo, Hwhi); ajournal_gx_exec + dk_kept_step_g (Zs = [sp - 96, sp), inside the callee window) |
| walk.v | 1379-1393 | fb_walk / fb_cg_holds_of_segs | intros Hbo Htwr; ABC | retyped premises; + gx_ok, gx_noerrno (L10), gx_rw (TransportGRwA.v:11) |

### Image B (frame B: _cg _cgW _cuts _iface _seg_a _seg_b _seg_h1 _seg_h2a _seg_h2b _w_bc _w_entry _w_epi _w_h2 _w_hdr _w_tail)

Image-A S08 lemmas cited (TransportGCg.v is image-free and B Requires it, ASAN-WALKS.md:293); the B kit twins of the decode_leafb_* / TransportFevt lemmas are pending S07.

| file | line | lemma / proof | out fact used | replacement (S08 / W_journalG file:line) or MISSING |
|---|---|---|---|---|
| cg.v | 133-140 | frame_fb_post | frame_cg_post post | transport_cg_post (TransportGCg.v:228); X += G3 |
| cg.v | 168 | frame_diginet_frame_build_cg | `frame_in_block B lyc Sc out (length oj)` | G1 trans_out_ok (MISSING) |
| cg.v | 169 | frame_diginet_frame_build_cg | `frame_twr_ok ... out` | transport_twr_ok_g (TransportGCg.v:472) |
| cg.v | 186-188 (+ journal premise) | frame_diginet_frame_build_cg | ajournal, post | ajournal_gx G 0 [] (W_journalG.v:203); transport_cg_post |
| cgW.v | 48-60 | frame_diginet_frame_build_cg_holds | composes the six pieces; t06be_api_env, t06be_model_laws | + gx_ok / gx_noerrno of G_HARNESS_B (L10 B twin, pending S07), G_HARNESS_B_rw (TransportGRwB.v:13) |
| cuts.v | 108-109 | fbc_pre | frame_in_block out; frame_twr_ok out | G1; transport_twr_ok_g |
| cuts.v | 131-137 | fbc_mid | inner ajournal FRAME_FB_STK (spZ regs) [(out, out + n)] | caller's ajournal_gx G 0 [] STK sp0 at (ly1 S1 W1 mem1 md1 k) + KP (acall_kept_g, TransportGCg.v:113) + G3 |
| cuts.v | 178-195, 200-325 | fbc_state, fbc_at_* | fbc_mid; frame_fb_post | G-form fbc_mid; transport_cg_post |
| cuts.v | 330-357 | fb_holds_of_pieces | intros Hblk Htwr (:350); fbc_pre | retyped; + G instances |
| iface.v, seg_a.v, seg_b.v, seg_h1.v, seg_h2a.v, seg_h2b.v | - | footprint statements | no out block fact | none |
| w_entry.v | 210-218 (out: :306-307) | fbwe_block_bounds | al_blocks of out | G2 |
| w_entry.v | 221-234 (out: :455-460) | fbwe_block_kept | acall_kept block clause keeps out across body_check | frame out: fbwe_fake_kept (w_entry.v:262) / YCbq.v:833-835; G out: gx_kept of gx_call_cg (TransportGCg.v:291) |
| w_entry.v | 299-304 | fbc_entry_of_segs HJI | ajournal_sub_init with FP [(out, ..)]; HPRI presence | HJ (caller's G journal); dk_kept_refl_g (TransportGCg.v:569); presence YCbq.v:369 via gx_open |
| w_entry.v | 326-334 | fbc_entry_of_segs ST0 / RF0 | dgn_leafb_stk_journal / rng_journal on HJI | decode_leafb_stk_journal / decode_leafb_rng_journal (DgnTransportLeafb.v:568, :578) on the donor journal of gx_open (TransportGCg.v:257) |
| w_entry.v | 379-394, 583-597 | fbc_entry_of_segs HJA | ajournal_exec on HJI, awr_byte stack branch | ajournal_gx_exec (W_journalG.v:297) + dk_kept_step_g (TransportGCg.v:601) |
| w_entry.v | 405-423 | fbc_entry_of_segs (body_check call) | RBC with HJA (inner journal) | gx_call_cg (TransportGCg.v:291) at the caller's (STK, sp0); G5 |
| w_entry.v | 608-613 | fbc_entry_of_segs (-4 exit) | EPI at fbc_mid | G-form fbc_mid |
| w_bc.v | 225 | J | inner journal abbreviation | caller's ajournal_gx |
| w_bc.v | 294-308 (out: :397, :453, :514, :573) | fbwb_blk_of | al_blocks of out: bounds, present | G2; presence (transport_twr_ok_g / gx_rw_vis TransportGCg.v:91) |
| w_bc.v | 311-321 | fbwb_j_md | ajournal_exec, no write | ajournal_gx_materialize (W_journalG.v:341) |
| w_bc.v | 435-494 | fbwb_cpy | aj_intrin_at with J (:460-462); awr_byte footprint branch (:474-478); amem / range / hull of out's block (:479-481) | gx_intrin_at (TransportGCg.v:506); transport_twr_ok_g; rd4 / rd2 / rd3 of trans_out_ok (G1) with KEEPSH (L8 / L6 + L7); KP step |
| w_bc.v | 497-562 | fbwb_fin | out bounds HA5 (in_app) for fbwb_rd_kept of hp + 4 (:557-558) | G2 (out apart from the shadow region) |
| w_hdr.v | 213-230 (out: :311, :370-371) | fbwh_blk | al_blocks of out: bounds, app_addr, present | G2; presence as above |
| w_hdr.v | 233-252 | fbwh_j_run | ajournal_exec, awr_byte | ajournal_gx_exec (W_journalG.v:297) |
| w_hdr.v | 278-332 | fbwh_state_leaf | AJ inner journal (:285); out app_addr (:311, :329-331) | G-form state; G2 |
| w_hdr.v | 336-470 | fbwh_h1 | out + 12 addressable / rng / shadow rng by dgn_leafb_*_block (:382-389); HJ2 ajournal_exec with awr_byte footprint branch (:408-415) | decode_leafb_addressable / decode_leafb_rng_vis / decode_leafb_rng_shadow (DgnTransportLeafb.v:366, :420, :426) on trans_out_ok rd (G2s, KEEPSH L8 / L6 + L7); ajournal_gx_exec with transport_twr_ok_g |
| w_hdr.v | 475-638 | fbwh_sum (diginet_sum16 call) | dgn_leafb_journal with the inner journal [(out, ..)] (:547-550); stk / rng journal (:565-580) | gx_call_leaf (TransportGCg.v:317) over decode_leafb_journal (DgnTransportLeafb.v:589) at the donor journal of gx_open |
| w_h2.v | 169-206 | fbc_h2_of_segs | al_blocks of out; dgn_leafb_*_block of out + 12 | G2; decode_leafb_addressable / rng / rng_shadow on trans_out_ok rd |
| w_h2.v | 314-318 | fbc_h2_of_segs | ajournal_exec with awr_byte footprint branch | ajournal_gx_exec + transport_twr_ok_g; KP step |
| w_tail.v | 350-380 | fbwt_run_const | ajournal_exec at Wr = empty | ajournal_gx_exec / ajournal_gx_materialize |
| w_tail.v | 423-603 | fbwt_write_step | fbc_mid (:432, :449); HBO bounds (:476, :487, :503-507); aj_intrin_at (:511-535: footprint branch :525-529, amem / range / hull of out's block :530-535); amem_range_of_block of out in fbwt_rd_ok_kept (:589-590) | G-form fbc_mid; G2; gx_intrin_at (TransportGCg.v:506) + transport_twr_ok_g + trans_out_ok rd; rd4 of trans_out_ok |
| w_tail.v | 606-660, 825-863 | fbwt_from_c3, fbc_tail_of_segs | HBO + al_blocks of out: bounds | G2 |
| w_epi.v | 68-101 | fbwp_fp_ok | each out byte a caller-block byte in FP (for ajournal_sub) | none: no inner journal to compose (the footprint question is gone) |
| w_epi.v | 104-206 | fbc_epi_of_segs | Hblk (:126, 4096 <= out); HJ2' ajournal_exec (:162-175); ajournal_sub with fbwp_fp_ok (:176-180); acall_kept_of_journal (:193-...); frame_fb_post | G2; ajournal_gx_materialize; none; KP is the post's acall_kept_g; transport_cg_post |

Totals: image A 35 sites (no out fact / removed: 2, existing S08 / W_journalG lemma: 14, needs a MISSING lemma: 19); image B 34 sites (2 / 15 / 17).

### Missing S08 / DgnTransportCg lemmas for the lift

### G1 `trans_out_ok` (A/Prog/DgnTransportCg.v, Section cj) — where out lies and what the stores and copies read of it
```coq
Definition trans_out_ok (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (q n : Z) : Prop :=
  (decode_in_fake lyc Sc q n \/ (forall a, q <= a < q + n -> W_journalG.inG TransportG.G_HARNESS a)) /\
  decode_rd_ok W memc q n.
```
Replaces `frame_in_block B lyc Sc out (length oj)` (frame A diginet_frame_build_cg.v:149, B :168, B diginet_frame_build_cuts.v:108). The out bytes are a
caller's side-stack frame (send_control's class-2 frame) or G (send_data); the 18 stores and the copies check their
shadow bytes, which the block's AR_shadow_law gave before (frame A diginet_frame_build_cg.v:55-56). A machine-stack out (send_control's fallback
when __asan_stack_malloc_2 returns 0) is not covered: see G4.

### G2 `trans_out_ok_far` and G2s `trans_out_ok_sub` (A/Prog/DgnTransportCg.v)
```coq
Lemma trans_out_ok_far : AR_laws segs B -> forall lyc Sc (W : world segs) memc mdc q n,
  @AR rc segs B lyc Sc W memc mdc -> trans_out_ok lyc Sc W memc q n -> 0 < n ->
  4096 <= q /\ q + n <= alloc_ceiling /\ (q + n <= kLowShadowBeg \/ kHighMemBeg <= q).
Lemma trans_out_ok_sub : forall lyc Sc (W : world segs) memc q n q' n',
  trans_out_ok lyc Sc W memc q n -> q <= q' -> 0 < n' -> q' + n' <= q + n -> trans_out_ok lyc Sc W memc q' n'.
```
far: FAKE frames_bounds (YCbq.v:451) and AR_frames_law's in_app (YG0d.v:451); G L2 (G_HARNESS_HI = 0x5f3190 <
kLowShadowBeg). Replace fb_out_far (A walk.v:311-317 and its 16 uses), fbwe_block_bounds / fbwb_blk_of / fbwh_blk /
the HBO bounds of B.

### G3 `gx_kept_ex` (A/Prog/TransportGCg.v, Section b) — G outside the written range kept
```coq
Definition gx_kept_ex (G : list (Z * Z)) (E : Z -> Prop) (W : world segs) (memc : word -> option byte)
  (W2 : world segs) (mem2 : word -> option byte) : Prop :=
  forall a, inG G a -> ~ E a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a.
Lemma gx_kept_ex_refl : forall G E W memc, gx_kept_ex G E W memc W memc.
Lemma gx_kept_ex_trans : forall G E W1 m1 W2 m2 W3 m3,
  gx_kept_ex G E W1 m1 W2 m2 -> gx_kept_ex G E W2 m2 W3 m3 -> gx_kept_ex G E W1 m1 W3 m3.
Lemma gx_kept_ex_of_kept : forall G E W memc W2 mem2, gx_kept G W memc W2 mem2 -> gx_kept_ex G E W memc W2 mem2.
Lemma gx_kept_ex_step : forall G E (W : world segs) memc memX memY (Zs : Z -> Prop),
  gx_ok segs B G -> (forall a, Zs a -> inG G a -> E a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) memY a = aview segs (w_H W) memX a) ->
  gx_kept_ex G E W memc W memX -> gx_kept_ex G E W memc W memY.
```
acall_kept_g's image clause excludes G (TransportGCg.v:118-119), so the tracker KP says nothing of G: dmac / smac (G,
read after the out writes) and the post's promise about G need G3. step uses inG_low (W_journalG.v:111).

### G4 (design) a machine-stack out under acall_kept_g (A/Prog/TransportGCg.v)
acall_kept_g clause 1 (TransportGCg.v:115) keeps every byte at or above alloc_ceiling outside the call's window
whatever E is (the remark of DgnTransportCg.v:324-328), so a written out in the caller's machine frame cannot meet
transport_cg_post. Either the statement excludes it (the caller takes the stack-malloc frame:
`count_cid 2 (frames Sc) < fs_frames 2`, as body_check does, decode A diginet_body_check_cg.v:117) or:
```coq
Definition acall_kept_gE (G : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
  (W2 : world segs) (mem2 : word -> option byte) (slo shi : Z) (E : Z -> Prop) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ E a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
 aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
(forall a, in_img segs a -> ~ inG G a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
 (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
 ~ E a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
(forall a, slo <= a < shi -> apresent (w_H W2) mem2 a).
```
with transport_cg_postE (transport_cg_post, TransportGCg.v:228-240, at acall_kept_gE) and the twins of
dk_kept_refl_g / trans_g / step_g (TransportGCg.v:569, :578, :601). The listing facts give this out for
send_control's fallback only.

### G5 `decode_cg_post_dcg` (A/Prog/TransportGCg.v or the frame_build kit) — body_check's post in gx_call_cg's form
```coq
Lemma decode_cg_post_dcg : forall MT STK sp0 FP ly S (W0 : world tfibsegs) mem0 md0 own lyc Sc (W : world tfibsegs) memc k
    regs FSTK EV COST (E : Z -> Prop) X W2 c2,
  @decode_cg_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs FSTK EV COST E X W2 c2 ->
  @dcg_post fx rc AE2k.tfib_sink_head tfibsegs B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs FSTK EV COST E X W2 c2.
```
decode_cg_post (DgnTransportCg.v:360-372) and dcg_post (TransportGCg.v:213-226) state the same conjuncts at
`@ajournal rc tfib_sink_head`, so the lemma is `fun _ H => H` [INFERENCE: convertible; written out because gx_call_cg
(TransportGCg.v:291-299) quantifies the callee post over its Context SK].

## Open items of step 1 (for the record; step 2 answers 2-5 above)


1. **decode_off_win is missing from the relocated statements.** Every input range's `OFF` use needs `decode_off_win regs FSTK q n`. The sibling statements carry it for the out-struct side-stack ranges (c, m, f, hp + 4, ap) but NOT for the block inputs (buf, body, dst, src) — the block gave `q + n <= alloc_ceiling < sp - FSTK` for free. The design's translation table pairs trans_src_ok with decode_off_win (ASAN-WALKS.md:258, :268), so each `*_in_block q n` premise must become `trans_src_ok ... q n` AND `decode_off_win regs FSTK q n`.
2. **diginet_frame_build's `out` is a written heap block, not covered by "out structs stay".** In the siblings out is `frame_in_block` (a heap block the function writes); the design's rule (ASAN-WALKS.md:364-366) only keeps out-struct *side-stack frames* (frame_in_fake + twr_ok). In transport send_control / send_data pass a local of their own frame (send_control.md:43; ASAN text takes a stack_malloc frame, ASAN-WALKS.md:551-552) [INFERENCE: out is that side-stack frame]. If so, out's premise becomes frame_in_fake + twr_ok, the inner journal's footprint and awr_byte branch change from the block case to the frame case, and `fbwp_fp_ok` (B w_epi.v:68-101) — which needs each out byte to be a caller-block byte in the footprint for `ajournal_sub` — must be reproved for a frame range. This is a structural change, not a trans_src_ok substitution. A writer must confirm from the transport listing what out is.
3. **KEEPSH for the window and G branches.** The block re-derives range_addressable / shadow_hull at any state from AR_shadow_law. For the non-heap branch, decode_rd_ok holds only at memc; a frame's shadow is kept by the journal/acall_kept frame clause, but NO ajournal or acall_kept clause keeps the shadow bytes of a harness-global (inG) range or a caller-machine-frame (window) range (they lie below alloc_ceiling, outside the image, in no block or frame). G may be covered by AR_zshadow_law if its range is a zero_shadow_range [INFERENCE, design S09/S10]; the window branch has no such fact. Affects fp_at_ret2 / fp_memcpy_call (buf at a later m), body_check scan/loop-test (body at mem2/mem3 after the msg_next call), frame_build fb_rfacts/fbwh_sum/fbwt_write_step (dst/src/body source shadow at m1).
4. **HI is false for the window branch.** body_check's scan and loop-test need `body + len <= bcs_PTRHI = 0x7fffff800000` (DgnBcScan.v:390, DgnBcLoopTest.v:prem), and frame_build w_hdr needs `app_addr` (`< ASAN_CEIL`). The block gave these from `q + n <= alloc_ceiling`. A window range lies ABOVE alloc_ceiling (`alloc_ceiling + FSTK <= sp`), so these bounds fail for it: the window disjunct of trans_src_ok is only sound for a callee that does not do the pointer-arithmetic the scan/hdr does. For these walks the input must land in the heap, frame (in_fake), or G branch, not the window branch. [INFERENCE] Needs a writer to confirm the body / buf of transport's body_check / frame_parse is never a caller machine frame.
5. **CALLEE: the window disjunct does not carry to an inner journal.** body_check (bl_call) and frame_build (fb_bc_call) re-establish `*_in_block body` for the diginet_msg_next / diginet_body_check callee at an INNER journal (STK = FRAME_BC_STK / FRAME_FB_STK, sp = spZ regs). trans_src_ok's window disjunct `sp0 - STK <= q /\ q + n <= sp0` is relative to the OUTER (STK, sp0); a range in the outer window need not sit in the inner window. So a window-branch input cannot be relayed as a window-branch premise to the callee; it must be re-derived as decode_rd_ok at the inner state (R1-R6 carry, since memc is shared) plus an inner location.
6. **frame_build empty-body shadow byte.** B/A w fb_body_run (walk.v:461-480) reads the shadow byte of body's granule when `length bb = 0`, taken from the byte before body inside the block. decode_rd_ok of an empty range states nothing; a new premise (the shadow byte of body's granule visible) is needed for the non-heap branch when the body can be empty.
7. **msg_next `0 < body`.** image B's mn_entry_F needs `0 < body` (UBSan, decode B msg_next_segs.v:100-101); the statement has no `body <> 0`, and mw_blk supplies it from `4096 <= body` (B1). The non-heap branch gives only `0 <= body` (R5), so for the frame/G/window branch a `body <> 0` premise (or the `0 < body` the heap case derives from 4096) must be added. image A's mn_entry_F does not need it.

## Step 3: image B's rule table (base 41cf46de4c30)

The image-B walks of 10 rows were written on the image-B kit (S07, S10 B), and a few names were patched by hand that
no rule of step 2 mapped. Step 3 puts those name edits into the tool's rule table (s11_reloc.py: CORE_B, MOD_HOME_B,
LEAFB_B and the dgn_leafb_ rule; the docstring's item 2 lists them), moves BASE_REV to 41cf46de4c30 (the image-B
ASan integration branch: the image-B kit, S10 B, the image-B statements and the ASan line with image A's S11 walks;
the listing files are c8ebc3afb25's, unchanged) and re-runs the tool. The rules, image B only:

| rule | source | target | where |
|---|---|---|---|
| CORE_B | DecodeTFIB (module), decodesegsB0 | YB1v, tfibsegs | decode B's lib/B/DecodeTFIB.v; a Require line that then names YB1v twice keeps it once |
| CORE_B | FrameB (frame B), TfibB (decode B) | TransportB | the image-B core record, lib/B/YD2l.v |
| MOD_HOME_B | lib.B YCbq / YC5d | lib.Reusable | frame B's Require lines (decode B's already read lib.Reusable) |
| MOD_HOME_B | lib.B.Prog PaJournal | lib.A.Prog | frame B's Require line (the base's PaJournal is image-free) |
| dgn_leafb_ | frame B dgn_leafb_<x> | decode B decode_leafb_<x> | when decode B's kit defines it (DgnTransportBLeafb on the base) |
| LEAFB_B | dgn_leafb_segs_low | decode_segs_low | the same statement (in_img tfibsegs a -> 0 <= a < kLowMemEnd), TransportFevt on the base |

Every rule application is a row of namemap-B.tsv (rule `... (rule table, step 3 ...)`).

Re-run (`s11_reloc.py --repo REPO --img IMG --out OUT --tables TAB --cmpkit KIT --keep-going`): exit 0, 0 stops; the
bycmp records are byte-identical to step 2's (11 image-B functions EQUAL-mod-pcrel with real 0, unmeasured 0,
target-differ 0); reloc-numerals-A/B.tsv and namemap-A.tsv are byte-identical; image A's 54 relocated files are
byte-identical (files.tsv); 25 image-B files change, by the rules only. The body_check_cg cross-check of image B now
reads EQUAL (code) (step 2: 3 lines differed, the segment list and YCbq's home). names-A.tsv is empty. names-B.tsv
lists 3 rows, all diginet_frame_build's and all names no rule should map: the module B.T06_FrameB_env and its names
t06be_api_env / t06be_model_laws, frame B's environment of the inner-journal form, which transport B has no twin of
and the G form does not use (it takes the image-B kit's run files TransportGRunB.v / DgnTransportBCgRun.v and the
trans_* record facts).

The re-run's output against the 10 committed image-B rows (33 walk files on lib/B/Prog):
- step 2's relocated text with the hand name edits applied (the six rules above) equals the step-3 output, file for
  file (0 differences in 33 files): every hand name edit is now made by the tool.
- the step-3 output against the committed files: equal for diginet_mac_is_digidesign (2 files), diginet_cursor_init
  (3), rd32 (2) and copy_strz (2). The other rows differ by their proof patches only, which no name rule makes:
  diginet_frame_is_keepalive (10 lines, the image-B statement's `0 <= body` and guarded `body <> 0`), diginet_sum16
  (10 lines, the guarded `p <> 0`), diginet_msg_next (148), diginet_frame_parse (280), diginet_body_check (648) and
  diginet_announce_parse (165). Within those counts: the statement names the image-B statements chose
  (TRANS_MN_* / trans_mn_*, TRANS_FP_* / trans_fp_* and TRANS_FP_F_SIZE, TRANS_BC_* / trans_bc_post, TRANS_ANP_* /
  trans_anp_*; 68, 136, 258 and 42 lines) depend on the statement file, not on a name map; the comment lines updated
  where a patch changed the names they cite; and the donor theorems at the records YD2l.TfibB / YD2l.FrameB, dropped
  in msg_next, frame_parse and announce_parse because lib/B/YD2l.v does not compile on this base (its as_got_shadow /
  as_got_uar fields 0xa3cf0 / 0xa3d48 against lib/B/YF0m.v's rows 0xa3d10 / 0xa3d68); each of those walks proves its
  statement for every record B.
