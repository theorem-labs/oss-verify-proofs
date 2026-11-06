(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 579 of its 604 lines of code are new or changed and 493 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the walk-internal
   piece statements of reac_segconf_parse_file (0x87e38, 5312 bytes, 1328 instructions; reac_segconf.c:120-296).
   proves no function (kind: statement text). No segment and no walk is proved here, and pf_pieces_give_contract
   (the whole function from its 16 segments) is stated, not proved. The image-B piece-statement lane of the image-B G3 walk owner, 2026-10-30.
   ADAPTED from the image-A G3 walk owner's image-A file lib/A/Prog/pf_pieces.v (commit 25613ab0b927, the
   image-A piece-statement lane): the same form, the same cut names and plain invariants where the meaning is the same; every
   register, slot and shadow conjunct is re-derived from image B's code and cites its B pc; each cut also carries
   the facts that the UBSan trap branches of the segments leaving it need (pf_tf, below).

   THE FORM (the A file's; fuzz_command's released segment form, origin/ossv/recipes 501c0d516c69,
   proofs/plugin-hostd/fuzz_command/lib/A/Prog/ and its lib/B/Prog twin): a bundle of the contract's variables
   (check_reply_m.v crv), the state at each cut as a predicate over the machine state (chain_words_d.v INV_K* /
   cw_fi, check_round_trip.v crt_J / crt_fr / crt_regs / crt_slots for the class-5 frame), and per cut "from this
   state the walk reaches the post" (chain_words_d.v cw_from, check_reply_m.v CR_*_stmt). Each segment statement
   S_B<k> says: its exit cuts imply its entry cut(s) (continuation form, chain_words_d.v cw_S*P). The exit cuts are
   taken at EVERY FP state (`HA_<CUT>`), because snprintf (7 sites) and refuse (8 sites, vsnprintf inside) return
   at another FP state (apost_baseF's relation; the segment lifts with PaFx's srr_apost_baseF_lift); the entry cut
   is at the ambient FP state. The functional invariant is the plain one, by Require of lib/Prog/pf_pieces_spec.v
   (pf_line, pf_next, pf_tline, pf_lctx, pf_cnt, pf_cur_ptr, pf_cur_ok, pf_inb, pf_prov_mid / pf_prov_fin,
   pf_role_step, pf_start); the loop is by the plain measure n, a bound on the text left.

   SOURCES. Machine code: the neutral excerpt reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s
   (every register / slot / shadow conjunct below cites the pc that sets it; the writes of every callee-saved
   register and of every N(s1) slot were listed by script over the excerpt, 2026-10-30). Cut plan:
   PLAN-pf-asanubsan.md (section 1 frames and the 29 slots, 2 the 41 checks, 3 the 34 traps, 4 the 53
   calls, 5 the 16-segment cover). UBSan trap facts: lib/U/Prog/reac_segconf_parse_file_pieces_c.v on
   a working branch. Corrections to the B plan found while stating:
   (1) DONE0 (0x89144, the text-NULL return) is not a cut: reader_pre gives t <> 0, so `bnez s11` at 0x88104 is
       decided and 0x89144-0x89158 (check B#41 and its slow path / stub 0x89210-0x89220) is dead, as A's 0x88be4.
       So are the real-stack fallback 0x87ec0-0x87ed8 (the kit's astack_malloc_realizes returns the frame) and the
       release's meta_fill_00 arm 0x89178-0x89180 (slot 0x88 holds F, not 0).
   (2) SEG carries s3 = 32 (0x887a8, B7): NEW's trap T32 `bltu s3,a2` (0x88e68) reads s3, and B8a's `blez` path
       0x88cb8 -> NEW skips B8a's own `li s3,32` (0x88d28).
   (3) HREF (0x885ec) serves after (0x883f4), notclosed (0x884a8) and B9's outside (0x885e8 falls in): a3 = s7 is
       set at 0x885f4, inside the cut's code. unknown enters the call itself (0x8851c `j 0x885f8`, a3 = s3 = body),
       inside B7.
   (4) CLR (0x885fc) is entered only from B7's code (HREF's call returns into it, REFTL's `j` 0x887dc, noname's
       `j` 0x88c9c); it stays a cut, owned by B7, so the three refusal paths share one statement.
   (5) PROV2's cut is B12's entry (0x88e48 falls in); B8b's own entry (0x88f50 `j`, cur_name's snprintf) walks
       B8b's own code, as A8b's.
   (6) KREFM: of B11b's three exits only 0x88bb8 (ti = ntok) is reached under reac_box_catalogue's post (ntok =
       11) and the join's kn <= 77 [INFERENCE from plan section 5.3 and pf_pieces_spec.L_known; B11b's lane shows
       it]; at KREFM known holds SegModel.known.

   THE CUTS (pc = BASE + PF_<CUT>; segment that owns the cut's code; who enters it):
     ENTRY  0x87e38 B1  the contract              FTAKEN 0x87edc B2  B1 (`bnez a0` 0x87ebc taken)
     FRAME  0x88074 B3  B2 (falls in)             DONE   0x89114 B4  B3 (`*t == 0`, 0x8815c), B5 (0x8862c)
     HEAD   0x881f8 B5  B3 (falls in), B5's latch TAIL   0x88600 B5  B5 (0x883a8), B6, B7 (CLR), B8b, B9,
                                                                    B10b, B11c
     LONG   0x88258 B6  B5 (0x88254)              REF3   0x882b4 B6  B6's LONG path, B9 (neither, 0x884c0)
     HDR    0x883b4 B7  B5 (0x883b0)              KEY    0x883f8 B9  B5 (0x883b0)
     HREF   0x885ec B7  B7 (0x883f4, 0x884a8), B9 (outside, 0x885e8)
     CLR    0x885fc B7  B7 (HREF's call, 0x887dc, 0x88c9c)
     REFTL  0x887cc B7  B7 (toolong, 0x887c8), B8a (bound, 0x88d64)
     SEG    0x88ca0 B8a B7 (0x887bc)              NEW    0x88e54 B8b B8a (0x88cb8, 0x88d38)
     FOUND  0x88eb0 B8b B8a (0x88d08)             PROV2  0x88e4c B8b B12 (falls in from 0x88e48)
     ROLE   0x88630 B10a B9 (0x88588)             MODEL  0x886d4 B11a B9 (0x8859c)
     IGN    0x887e0 B12 B9 (0x885b0)              INTENT 0x888e4 B10b B10a (falls in)
     KREF   0x889a0 B9  B9 (knock 0x8899c, nokey 0x885e0), B12 (bad ignore, 0x888b8)
     MISS   0x88a50 B11b B11a (0x889dc)           KREFM  0x88bd0 B11c B11b (0x88bb8)
     LOWOUT 0x88c70 B11c B11a (0x88a44), B11c (falls in from 0x88c6c)
   A's RS3 has no B twin (B12's bad ignore joins KREF); HREF, REFTL, KREF and KREFM are B's.

   WHAT EVERY CUT FROM FTAKEN ON CARRIES (pf_fi, pf_obj): the journal from the entry with the class-5 frame
   (5, pos) as this call's own frame and 0 events; the entry's layout and the entry's state up to st_fs; the 13
   saved registers at sp0 - 8 .. sp0 - 0x68 (0x87e40-0x87e70, ra highest, s11 lowest: A's order); the frame's flag
   pointer at F + fs_frame_bytes 5 - 8; the rounding mode 0; sp = s1 = (sp0 - 0x160) & -32 (0x87e38, 0x87e78,
   0x87e7c; the fake path never moves sp), s0 = sp0 (0x87e74), gp, tp, s4 = SHADOW_OFF (0x87e9c, through the GOT
   word 0xa3210, which holds the cell 0xac7b8; overwritten only at 0x89118, after DONE), c in slot 0xc8 (0x87ea0;
   c lives nowhere else); the trap facts pf_tf; and the caller's objects at the cut's reader: the text and the
   block c (bytes, shadow, live block), the catalogue and the literals (sa_cat / sa_lit), the read-only view and
   the stack-protector cells. F = frame_addr ly 5 pos, SH = shadow_addr F (= s5 from 0x87f1c to the end), the
   objects at F + 0x20 cur_name[16], F + 0x40 buf[512], F + 0x280 low[64], F + 0x2e0 model low[24] (B's compiler
   name low202, A's low146), F + 0x320 known[240], F + 0x450 ntok (.rodata 0x11b81's description string, read from
   the pin: the same offsets and sizes as A's 0x17667). The frame's 144 shadow cells per scope: pf_shb.

   THE 34 UBSAN TRAP BRANCHES (all to the `unimp` at 0x891c8; plan section 3), by the fact that keeps each one not
   taken and where the segment leaving the cut finds it:
     F1, c's placement (pf_tf: c <> 0, c mod 16 = 0; cur = c + 356 i by pf_st's slot 0xc0, 356 = 4 * 89):
       T01 0x8807c, T02 0x8808c (B3, FRAME); T22 0x889e8 (B11a, MODEL); T30 0x88d74 (B10b, INTENT);
       T31 0x88dfc (B12, IGN); T34 0x88f08 (B8b, NEW / FOUND).
     F2, no pointer wraps (each pointer stays inside an object that ends below 2 ^ 63): the text by pf_obj's
       sa_addr t (length s + 1): T03 0x8820c, T04 0x8822c (B5, HEAD), T06 0x88270 (B6, LONG); the frame by pf_tf
       (4096 <= F, F + fs_frame_bytes 5 <= 2 ^ 47; buf / low / model low and the trimmed pointers into buf):
       T07 0x882d0, T08 0x88320, T09 0x88344 (B5, HEAD), T10 0x883cc, T13 0x884e0, T19 0x88768 (B7, HDR),
       T11 0x88428, T12 0x88478, T14 0x88528, T15 0x8854c, T16 0x88568 (B9, KEY), T17 0x8869c, T20 0x888c4 (B10a,
       ROLE), T18 0x8872c, T21 0x889b0 (B11a, MODEL); the block c by pf_obj's sa_addr c SEG_C_SIZE with i, n <= 32:
       T29 0x88cf8 (B8a, SEG), T33 0x88e78 (B8b, NEW).
     F3, the line counter (pf_lctx's ln <= o, pf_tf's length s <= 65535): T05 0x88240 (B5, HEAD).
     F4, loop and array bounds: T28 0x88cf0 (B8a: i < n <= 32, sa_rconf's rconf_enc bound), T32 0x88e68 (B8b:
       INV_NEW's n < 32 and s3 = 32), T23 0x88b14 and T26 0x88b60 (B11b's join loop: kn <= 77, ti <= 10).
     F5, the table parameter (reac_box_catalogue's post: a0 = cat = catA = 0xa20a0): T24 0x88b44, T25 0x88b48,
       T27 0x88b68 (B11b, MISS).
   6 + 20 + 1 + 4 + 3 = 34. The trap facts are plain Props over the bundle: B1 derives pf_tf once (from pf_cx's
   reader_pre and the take's frame), every later segment hands it on unchanged.

   POSITIONAL NAMES carried from the A file, checked against image B: the frame offsets PF_O_* (B's description
   string 0x11b81: 6 objects at +32, +64, +640, +736, +800, +1104, the same as A's); the shadow cell map pf_shb
   (plan section 1.3: the 144 cells B's entry writes, 0x87f20-0x88070 and meta_fill_f8 0x87f4c, have A's values);
   PF_SAVED (B's prologue stores ra .. s11 at sp0 - 8 .. sp0 - 0x68, A's order); AF_<F> and SS_<name> are B's
   SegList / SegSyms names (BASE + AF_reac_segconf_parse_file = 0x84dc0 + 0x3078 = 0x87e38; pf_cut_pcs below checks
   every cut pc by computation against B's seg_text). No region letter, listing object number or STK row of an A
   table is used.

   IMAGE B'S PARAMETER VALUES: SegInstB.v (the image-B harness owner, lib/B/Prog/SegInstB.v 1f771e2f2066, in base
   commit 2ba03f668177), which keeps the image-A owner's SegInstA names at image B's values: RLO_A
   0xa1c60, RHI_A 0xa3f08, catA 0xa20a0, gotwA 0xa3e98, guardA 0x5ff838, seg_litA_rc (and seg_litA_rc_facts),
   STK_trim 4128, STK_refuse 12464, STK_reac_segconf_parse_file 12832; this file uses them as the A file uses
   SegInstA's. pf_B_values below checks the ones the cuts name. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa
  SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** The image values the cuts name (SegInstB.v) *)
Lemma pf_B_values :
  RLO_A = 0xa1c60 /\ RHI_A = 0xa3f08 /\ catA = 0xa20a0 /\ gotwA = 0xa3e98 /\ guardA = 0x5ff838 /\
  STK_trim = 4128 /\ STK_refuse = 12464 /\ STK_reac_segconf_parse_file = 12832 /\
  seg_litA_rc F_long = 0x213a0 /\ seg_litA_rc [SP; TAB; CR] = 0x21380 /\ seg_litA_rc F_s = 0x21340.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ** The cut pcs, as listing offsets (BASE + AF_reac_segconf_parse_file = 0x87e38, B's SegList / SegAddr) *)
Definition PF_ENTRY : Z := AF_reac_segconf_parse_file.            (* 0x87e38 *)
Definition PF_FTAKEN : Z := AF_reac_segconf_parse_file + 0xa4.    (* 0x87edc *)
Definition PF_FRAME : Z := AF_reac_segconf_parse_file + 0x23c.    (* 0x88074 *)
Definition PF_HEAD : Z := AF_reac_segconf_parse_file + 0x3c0.     (* 0x881f8 *)
Definition PF_LONG : Z := AF_reac_segconf_parse_file + 0x420.     (* 0x88258 *)
Definition PF_REF3 : Z := AF_reac_segconf_parse_file + 0x47c.     (* 0x882b4 *)
Definition PF_HDR : Z := AF_reac_segconf_parse_file + 0x57c.      (* 0x883b4 *)
Definition PF_KEY : Z := AF_reac_segconf_parse_file + 0x5c0.      (* 0x883f8 *)
Definition PF_HREF : Z := AF_reac_segconf_parse_file + 0x7b4.     (* 0x885ec *)
Definition PF_CLR : Z := AF_reac_segconf_parse_file + 0x7c4.      (* 0x885fc *)
Definition PF_TAIL : Z := AF_reac_segconf_parse_file + 0x7c8.     (* 0x88600 *)
Definition PF_ROLE : Z := AF_reac_segconf_parse_file + 0x7f8.     (* 0x88630 *)
Definition PF_MODEL : Z := AF_reac_segconf_parse_file + 0x89c.    (* 0x886d4 *)
Definition PF_REFTL : Z := AF_reac_segconf_parse_file + 0x994.    (* 0x887cc *)
Definition PF_IGN : Z := AF_reac_segconf_parse_file + 0x9a8.      (* 0x887e0 *)
Definition PF_INTENT : Z := AF_reac_segconf_parse_file + 0xaac.   (* 0x888e4 *)
Definition PF_KREF : Z := AF_reac_segconf_parse_file + 0xb68.     (* 0x889a0 *)
Definition PF_MISS : Z := AF_reac_segconf_parse_file + 0xc18.     (* 0x88a50 *)
Definition PF_KREFM : Z := AF_reac_segconf_parse_file + 0xd98.    (* 0x88bd0 *)
Definition PF_LOWOUT : Z := AF_reac_segconf_parse_file + 0xe38.   (* 0x88c70 *)
Definition PF_SEG : Z := AF_reac_segconf_parse_file + 0xe68.      (* 0x88ca0 *)
Definition PF_PROV2 : Z := AF_reac_segconf_parse_file + 0x1014.   (* 0x88e4c *)
Definition PF_NEW : Z := AF_reac_segconf_parse_file + 0x101c.     (* 0x88e54 *)
Definition PF_FOUND : Z := AF_reac_segconf_parse_file + 0x1078.   (* 0x88eb0 *)
Definition PF_DONE : Z := AF_reac_segconf_parse_file + 0x12dc.    (* 0x89114 *)
(* each cut's pc at B's base seg_text (the excerpt's addresses) *)
Lemma pf_cut_pcs :
  seg_text + PF_ENTRY = 0x87e38 /\ seg_text + PF_FTAKEN = 0x87edc /\ seg_text + PF_FRAME = 0x88074 /\
  seg_text + PF_HEAD = 0x881f8 /\ seg_text + PF_LONG = 0x88258 /\ seg_text + PF_REF3 = 0x882b4 /\
  seg_text + PF_HDR = 0x883b4 /\ seg_text + PF_KEY = 0x883f8 /\ seg_text + PF_HREF = 0x885ec /\
  seg_text + PF_CLR = 0x885fc /\ seg_text + PF_TAIL = 0x88600 /\ seg_text + PF_ROLE = 0x88630 /\
  seg_text + PF_MODEL = 0x886d4 /\ seg_text + PF_REFTL = 0x887cc /\ seg_text + PF_IGN = 0x887e0 /\
  seg_text + PF_INTENT = 0x888e4 /\ seg_text + PF_KREF = 0x889a0 /\ seg_text + PF_MISS = 0x88a50 /\
  seg_text + PF_KREFM = 0x88bd0 /\ seg_text + PF_LOWOUT = 0x88c70 /\ seg_text + PF_SEG = 0x88ca0 /\
  seg_text + PF_PROV2 = 0x88e4c /\ seg_text + PF_NEW = 0x88e54 /\ seg_text + PF_FOUND = 0x88eb0 /\
  seg_text + PF_DONE = 0x89114.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ** The class-5 frame's objects (offsets from F; .rodata 0x11b81, plan section 1.2) *)
Definition PF_O_CN : Z := 0x20.      (* cur_name[16], R:127 *)
Definition PF_O_BUF : Z := 0x40.     (* buf[512], R:142 *)
Definition PF_O_LOW : Z := 0x280.    (* role low[64], R:234 *)
Definition PF_O_L146 : Z := 0x2e0.   (* model low[24] (B: low202), R:252 *)
Definition PF_O_KNOWN : Z := 0x320.  (* known[240], R:258 *)
Definition PF_O_NTOK : Z := 0x450.   (* ntok, R:259 *)

(** ** The frame's shadow, cell by cell (plan sections 1.3 and 1.4)
    Cell i is the shadow byte of F + 8 i. The entry lays all 144 cells (0x87f20-0x88070 inline, 0x87f4c
    meta_fill_f8 for buf's 64): 0xf1 left redzone (cells 0-3, a0 = -0xf at 0x87f18), 0xf2 middle redzones
    (s2 = -0xe at 0x87ef4), 0xf3 right redzone (cells 0x8b-0x8f, a0 = -0xd at 0x88050), 0xf8 an object out of
    scope (s6 = -8 at 0x87ef8). An object in scope has cells 0x00. The scope events after the entry: cur_name in at
    0x8811c-0x88120 (out at 0x89130, in B4); buf in at 0x8824c (meta_fill_00, every line before the length test),
    out at 0x88608 (meta_fill_f8, the tail; TAIL 0x88600 is two instructions before it); low in at 0x88630-0x8864c,
    out at 0x88dcc-0x88de8; model low in at 0x886d4-0x886dc, out at 0x88c70-0x88c78; known and ntok in at
    0x88a50-0x88ac8, out at 0x88bf4-0x88c6c. *)
Record pf_scope := PFSc { sc_cn : bool; sc_buf : bool; sc_low : bool; sc_l146 : bool; sc_known : bool }.
Definition pf_io (b : bool) : Z := if b then 0 else 0xf8.
Definition pf_shb (sc : pf_scope) (i : Z) : Z :=
  if i <? 4 then 0xf1                              (* 0x00-0x03 left redzone *)
  else if i <? 6 then pf_io (sc_cn sc)             (* 0x04-0x05 cur_name *)
  else if i <? 8 then 0xf2                         (* 0x06-0x07 *)
  else if i <? 72 then pf_io (sc_buf sc)           (* 0x08-0x47 buf *)
  else if i <? 80 then 0xf2                        (* 0x48-0x4f *)
  else if i <? 88 then pf_io (sc_low sc)           (* 0x50-0x57 low *)
  else if i <? 92 then 0xf2                        (* 0x58-0x5b *)
  else if i <? 95 then pf_io (sc_l146 sc)          (* 0x5c-0x5e model low *)
  else if i <? 100 then 0xf2                       (* 0x5f-0x63 *)
  else if i <? 130 then pf_io (sc_known sc)        (* 0x64-0x81 known *)
  else if i <? 138 then 0xf2                       (* 0x82-0x89 *)
  else if i <? 139 then pf_io (sc_known sc)        (* 0x8a ntok, with known *)
  else 0xf3.                                       (* 0x8b-0x8f right redzone *)
(* FRAME: all out; HEAD and DONE: cur_name in; inside a line (and TAIL): cur_name, buf; INTENT: and low;
   MISS / LOWOUT: and model low; KREFM: and model low, known, ntok *)
Definition PF_SC0 : pf_scope := PFSc false false false false false.
Definition PF_SC_HEAD : pf_scope := PFSc true false false false false.
Definition PF_SC_LINE : pf_scope := PFSc true true false false false.
Definition PF_SC_LOW : pf_scope := PFSc true true true false false.
Definition PF_SC_L146 : pf_scope := PFSc true true false true false.
Definition PF_SC_KNOWN : pf_scope := PFSc true true false true true.

(** ** Register, slot and shadow forms (check_round_trip.v crt_regs / crt_slots / crt_frame) *)
(* the registers the prologue saves, slot j at sp0 - 8 - 8 j: ra, s0, s1, s2 .. s11 (0x87e40-0x87e70) *)
Definition PF_SAVED : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition pf_rg (rX : bvmap 5 word) (L : list (Z * Z)) : Prop :=
  Forall (fun rv => getr rX (Z_to_bv 5 (fst rv)) = w64 (snd rv)) L.
Definition pf_sl (rd : reader) (b : Z) (L : list (Z * Z)) : Prop :=
  Forall (fun ov => rdword rd (b + fst ov) = Some (snd ov)) L.
Definition pf_saved (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
  forall j r, nth_error PF_SAVED j = Some r ->
  rdword rd (sp0 - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr regs (Z_to_bv 5 r))).
Definition pf_fsh (rd : reader) (sh : Z) (sc : pf_scope) : Prop :=
  forall i, 0 <= i < 144 -> rd (sh + i) = Some (pf_shb sc i).
(* cur_name holds the C string nm (seg_spec.cstr_enc; the plain pf_nm_at) *)
Definition pf_nm (rd : reader) (a : Z) (nm : list Z) : Prop :=
  exists f, sa_bytes rd a f /\ seg_spec.cstr_enc 16 nm f.
(* the 64-bit `not` of x (0 <= x < 2 ^ 64), as rdword reads it: the no-wrap operands B's setup spills (0x88190,
   0x881d8, 0x881e4, 0x881f0) for the trap tests T07, T20, T21, T29, T33 *)
Definition pf_nt (x : Z) : Z := 2 ^ 64 - 1 - x.

(** ** The tail of the header step (r_header from seg_get on, SegModel R:197-211): the state after an accepted
    name; SEG, NEW and FOUND state their post with it (B7 rewrites r_header to it under the header's tests). *)
Definition pf_seg_step (c : rconf) (nm : list Z) (ln : Z) (name : list Z) : rconf * option nat * list Z :=
  match seg_get c name with
  | (c1, None) => (refuse c1 ln F_bound [AS name; AI 32], None, nm)
  | (c1, Some (i, is_new)) =>
    let c2 := if negb is_new && (rs_seen_gen (nth i (rc_seg c1) rseg_d) =? rc_gen c1)
              then refuse c1 ln F_twice [AS name] else c1 in
    (r_upd c2 i (rs_with_gen (rc_gen c2)), Some i, snprintf_s 16 F_s [AS name])
  end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the variables of reac_segconf_parse_file_contract (lib/B/Prog/reac_segconf_parse_file_c.v) *)
Record pfv := mkPFV {
  p_ly : alayout; p_S : astate; p_W : world SEGS; p_regs : bvmap 5 word; p_mem : word -> option byte;
  p_md : Model; p_ch : list (Z * Z * Z); p_c : Z; p_t : Z; p_lp : Z; p_rcs : rconf; p_s : list Z;
  p_lab : option (list Z) }.
(* the entry sp; s1 = the realigned locals base (0x87e38 addi sp,sp,-352; 0x87e78 andi sp,sp,-32; 0x87e7c
   mv s1,sp) *)
Definition pf_sp0 (v : pfv) : Z := spZ (p_regs v).
Definition pf_s1 (v : pfv) : Z := (pf_sp0 v - 0x160) - (pf_sp0 v - 0x160) mod 32.
(* the class-5 frame F (frame_alloc_5's a0, 0x87eac / 0x87eb8), its flag cell, its shadow SH (s5, 0x87ef0 /
   0x87f1c) *)
Definition pf_F (v : pfv) (pos : Z) : Z := frame_addr (p_ly v) 5 pos.
Definition pf_FL (v : pfv) (pos : Z) : Z := flag_addr (p_ly v) 5 pos.
Definition pf_SH (v : pfv) (pos : Z) : Z := shadow_addr (pf_F v pos).
(* the text's bytes and NUL *)
Definition pf_len (v : pfv) : Z := Z.of_nat (length (p_s v)) + 1.
(* THE TRAP FACTS (head comment, F1 - F3; F2's text and block halves are pf_obj's sa_addr, F4 is sa_rconf's bound
   and the cuts' own loop facts, F5 is catA's value): c's placement (T01, T02, T22, T30, T31, T34), where the
   class-5 frame lies (T07 - T21: every buf / low / model low pointer), the text's length (T05, with pf_lctx's
   ln <= o) *)
Definition pf_tf (v : pfv) (pos : Z) : Prop :=
  p_c v <> 0 /\ p_c v mod 16 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + fs_frame_bytes 5 <= 2 ^ 47 /\
  (length (p_s v) <= 65535)%nat.

Section e.
Variable B : asyms.

(** *** The entry, the post *)
(* reac_segconf_parse_file_contract's premises at image B (the values above; A = BASE + AF_<F>). The SAME Prop at
   every FP state: reac_segconf_parse_file_pre's only FP conjunct is reader_pre's sa_frm0 (the entry's rounding
   mode), so it is held at SOME FP state fe (the entry's), and each cut carries the rounding mode of its own FP
   state in pf_fi. A segment that calls snprintf / refuse thus hands pf_cx v on unchanged to the cut it reaches at
   the callee's FP state. *)
Definition pf_cx (v : pfv) : Prop :=
  afn_pre SEGS B STK_reac_segconf_parse_file (p_ly v) (p_S v) (p_W v) (p_regs v) (p_mem v) (p_md v) (p_ch v) /\
  arodata_okP SEGS RLO_A RHI_A B (rdW (p_W v) (p_mem v)) /\
  getr (p_regs v) 10 = w64 (p_c v) /\ 0 <= p_c v < 2 ^ 64 /\
  getr (p_regs v) 11 = w64 (p_t v) /\ 0 <= p_t v < 2 ^ 64 /\
  getr (p_regs v) 12 = w64 (p_lp v) /\ 0 <= p_lp v < 2 ^ 64 /\
  (exists fe : YK11.FPState,
     reac_segconf_parse_file_pre (fx := fe) SEGS B seg_litA_rc catA gotwA guardA (p_ly v) (p_S v)
       (rdW (p_W v) (p_mem v)) (p_c v) (p_t v) (p_lp v) (p_rcs v) (p_s v) (p_lab v)) /\
  sa_room_n 2 (p_S v) /\
  st_nev (p_S v) + EV_reac_segconf_parse_file <= EV_MAX.
(* the contract's post *)
Definition PF_POST (v : pfv) : world SEGS -> config -> Prop :=
  apost_baseF SEGS B STK_reac_segconf_parse_file (seg_spec.RC_PARSE_W (p_c v)) (p_regs v) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) EV_reac_segconf_parse_file
    (fun ly' S' W' regs' mem' md' =>
     getr regs' 10 = w64 (snd (SegModel.r_parse_file (p_rcs v) (p_s v) (p_lab v))) /\
     sa_rconf (rdW W' mem') (p_c v) (fst (SegModel.r_parse_file (p_rcs v) (p_s v) (p_lab v))) /\
     sa_noalloc B (p_ly v) (p_S v) ly' S').
(* the same post for a final state cf of the block (the plain pf_ret): a0 = c->n = the number of entries, c
   holds cf. PF_POST v is PF_POSTr v (fst (r_parse_file ..)) once r_parse_file's let is destructed. *)
Definition PF_POSTr (v : pfv) (cf : rconf) : world SEGS -> config -> Prop :=
  apost_baseF SEGS B STK_reac_segconf_parse_file (seg_spec.RC_PARSE_W (p_c v)) (p_regs v) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) EV_reac_segconf_parse_file
    (fun ly' S' W' regs' mem' md' =>
     getr regs' 10 = w64 (Z.of_nat (length (rc_seg cf))) /\ sa_rconf (rdW W' mem') (p_c v) cf /\
     sa_noalloc B (p_ly v) (p_S v) ly' S').

(** *** The parts every cut after the frame take shares *)
(* the frame part (see the head comment): journal, layout and state, live blocks, saved registers, flag
   pointer, rounding mode, the trap facts, c's slot 0xc8 (0x87ea0), sp / gp / tp / s0 / s1 / s4 *)
Definition pf_fi (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) : Prop :=
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 /\
  lyc = p_ly v /\ (exists f, Sc = set_fs f (p_S v)) /\
  Permutation (ablocks B lyc Sc) (ablocks B (p_ly v) (p_S v)) /\
  pf_saved (rdW Wc memc) (pf_sp0 v) (p_regs v) /\
  rdword (rdW Wc memc) (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) /\
  sa_frm0 /\ pf_tf v pos /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xc8, p_c v)] /\
  pf_rg rX [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF)].
(* the caller's objects at the cut's reader rd: the text (strchr / strlen / strspn / memcpy and checks B#2, B#3,
   B#15), the block c (every c / cur / seg[i] check), the catalogue (B#28, reac_box_catalogue[_by_token]), the
   literals (every interceptor / refuse format), the read-only view (rt_rom_view), printf's guard cells *)
Definition pf_obj (v : pfv) (lyc : alayout) (Sc : astate) (rd : reader) : Prop :=
  sa_str rd (p_t v) (p_s v) /\ sa_addr rd (p_t v) (pf_len v) /\ sa_heap B lyc Sc (p_t v) (pf_len v) /\
  sa_addr rd (p_c v) seg_spec.SEG_C_SIZE /\ sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE /\
  sa_cat SEGS B rd catA /\ (forall x, In x PARSE_FILE_LITS -> sa_lit SEGS B rd (seg_litA_rc x) x) /\
  arodata_okP SEGS RLO_A RHI_A B rd /\ sa_ssp rd gotwA guardA.
(* the label, which the snprintf of 0x880cc reads (FTAKEN and FRAME only): where it lies (the contract's three
   places) and its bytes' shadow at rd; its addressability at every AR state in the image case stays in pf_cx
   (reac_segconf_parse_file_pre) *)
Definition pf_lab (v : pfv) (lyc : alayout) (Sc : astate) (rd : reader) : Prop :=
  sa_ostr rd (p_lp v) (p_lab v) /\
  match p_lab v with
  | Some l =>
      (sa_heap B lyc Sc (p_lp v) (Z.of_nat (length l) + 1) \/ sa_fframe lyc Sc (p_lp v) (Z.of_nat (length l) + 1) \/
       sa_img SEGS B (p_lp v) (Z.of_nat (length l) + 1)) /\
      sa_addr rd (p_lp v) (Z.of_nat (length l) + 1)
  | None => True
  end.
(* the spine's state at a cut (the plain pf_state): c holds cf, cur is an entry of it and lives in slot 0xc0
   (B keeps cur in no register: 0x88164 NULL, 0x882a0 the long line's mask, 0x885fc NULL, 0x88f00 the header's
   entry), cur_name holds nm, and the counters have room for the k text bytes left *)
Definition pf_st (v : pfv) (pos : Z) (rd : reader) (cf : rconf) (cur : option nat) (nm : list Z) (k : nat)
  : Prop :=
  sa_rconf rd (p_c v) cf /\ pf_cur_ok cf cur /\ pf_nm rd (pf_F v pos + PF_O_CN) nm /\ pf_cnt cf k /\
  rdword rd (pf_s1 v + 0xc0) = Some (pf_cur_ptr (p_c v) cur).
(* the same where cur is dead or its slot about to be written (HREF, CLR, REFTL: 0x885fc stores NULL; SEG, NEW,
   FOUND: B8a stores the name there at 0x88cc0, B8b the entry at 0x88f00) *)
Definition pf_st0 (v : pfv) (pos : Z) (rd : reader) (cf : rconf) (nm : list Z) (k : nat) : Prop :=
  sa_rconf rd (p_c v) cf /\ pf_nm rd (pf_F v pos + PF_O_CN) nm /\ pf_cnt cf k.
(* the loop's constant registers (the write list of each register, script over the excerpt): s2 = '#' (0x881a8;
   strip_comment's mark, 0x8830c; borrowed in the join loop at 0x88b7c, restored at 0x88bb4), s5 = SH (0x87f1c,
   never written again), s10 = -1 (0x881ac, never written again; the trap tests' all-ones operand) *)
Definition PF_RL (v : pfv) (pos : Z) : list (Z * Z) :=
  [(18, 0x23); (21, pf_SH v pos); (26, -1)].
(* inside a line that starts at o: s9 = p' = t + pf_next s o (0x88214 nl + 1, or 0x88234 p + len: the next
   line), s6 = lineno = ln + 1 (0x88238, addiw; ln + 1 <= 65536); neither is written again before TAIL *)
Definition PF_RM (v : pfv) (o : nat) (ln : Z) : list (Z * Z) :=
  [(25, p_t v + Z.of_nat (pf_next (p_s v) o)); (22, ln + 1)].
(* the 23 spill slots s1 + N the setup writes (0x87edc .. 0x881f4) that no line changes (plan section 1.1 and the
   slot-write list: the loop writes only 0x60, 0x68, 0x70 and 0xc0); 0xc8 (c) is pf_fi's, 0xf0 (0x87ee0) is never
   read and left out *)
Definition PF_SL (v : pfv) (pos : Z) : list (Z * Z) :=
  [(0x00, 0x2c80);                                           (* 0x881d0 32 * 356 = sizeof c->seg, read 0x88cec *)
   (0x08, p_c v + seg_spec.RS_SEEN_GEN);                     (* 0x8819c &seg[0].seen_gen, read 0x88ce4 *)
   (0x10, pf_nt (pf_F v pos + PF_O_L146));                   (* 0x881e8 ~model low, read 0x889ac (T21) *)
   (0x18, shadow_addr (p_c v + seg_spec.RC_GEN));            (* 0x8810c, read 0x88ebc / 0x88f0c *)
   (0x20, p_c v + seg_spec.RC_GEN);                          (* 0x88114 *)
   (0x28, p_c v + seg_spec.RC_OVERFLOW);                     (* 0x881b8, read 0x88d1c *)
   (0x30, pf_nt (pf_F v pos + PF_O_LOW));                    (* 0x881f4 ~low, read 0x888c0 (T20) *)
   (0x38, pf_nt (p_c v));                                    (* 0x88194 ~c, read 0x88cf4 (T29) / 0x88e74 (T33) *)
   (0x40, pf_F v pos + PF_O_CN);                             (* 0x88128 *)
   (0x48, p_c v + seg_spec.RC_READING);                      (* 0x88110 *)
   (0x50, (p_c v + seg_spec.RC_N) / 8);                      (* 0x88154, read 0x88ca0 / 0x89114 *)
   (0x58, p_c v + seg_spec.RC_N);                            (* 0x8814c *)
   (0x78, pf_F v pos + PF_O_KNOWN);                          (* 0x88180 *)
   (0x80, pf_F v pos + PF_O_NTOK);                           (* 0x88188 *)
   (0x88, pf_F v pos);                                       (* 0x87edc frame_alloc_5's result, read 0x89138 *)
   (0x90, pf_F v pos + PF_O_L146);                           (* 0x881e0 *)
   (0x98, pf_F v pos);                                       (* 0x87f10, read 0x88100 / 0x8816c / 0x8913c *)
   (0xa0, pf_F v pos + PF_O_LOW);                            (* 0x881ec *)
   (0xa8, seg_litA_rc F_long);                               (* 0x881c8 (0x213a0), read 0x882b0 *)
   (0xb0, pf_nt (pf_F v pos + PF_O_BUF));                    (* 0x881dc ~buf, read 0x882cc (T07) *)
   (0xb8, seg_litA_rc [SP; TAB; CR]);                        (* 0x881c0 (0x21380), read 0x8825c *)
   (0xd0, pf_F v pos + PF_O_BUF);                            (* 0x881d4 *)
   (0xd8, pf_SH v pos + 8)].                                 (* 0x87f48, read 0x88248 / 0x88604 *)
(* every cut from HEAD on: the entry facts, the frame part, the objects, the slots, the frame's shadow *)
Definition pf_base (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (sc : pf_scope) : Prop :=
  pf_cx v /\ pf_fi v pos lyc Sc Wc rX memc mdc /\ pf_obj v lyc Sc (rdW Wc memc) /\
  pf_sl (rdW Wc memc) (pf_s1 v) (PF_SL v pos) /\ pf_fsh (rdW Wc memc) (pf_SH v pos) sc.
(* inside a line that starts at o (the plain pf_ctx): o < length s, the rest is at most n bytes, and the
   account at the next line's offset counts this line (lineno = ln + 1) *)
Definition pf_mid (v : pfv) (o : nat) (ln : Z) (d : list (list Z)) (n : nat) : Prop :=
  (o < length (p_s v))%nat /\ (length (skipn o (p_s v)) <= n)%nat /\
  pf_lctx (p_s v) (pf_next (p_s v) o) (ln + 1) d.
(* the post from a state st of the line's step (the plain pf_fin of r_lines st (ln + 1) (lines rest')) *)
Definition pf_postm (v : pfv) (st : rconf * option nat * list Z) (o : nat) (ln : Z) : world SEGS -> config -> Prop :=
  PF_POSTr v (fst (fst (r_lines st (ln + 1) (lines (skipn (pf_next (p_s v) o) (p_s v)))))).
(* a split key line (R:215-223, the plain pf_kv) with key and val C strings in buf *)
Definition pf_kv (rd : reader) (v : pfv) (pos : Z) (line : list Z) (kp vp : Z) (key val : list Z) : Prop :=
  (exists ei : nat, strchr line EQ = Some ei /\ key = r_trim (firstn ei line) /\
                    val = r_unquote (r_trim (skipn (S ei) line))) /\
  sa_str rd kp key /\ pf_inb (pf_F v pos + PF_O_BUF) kp key /\
  sa_str rd vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val.
(* the two refusals of the shared refuse call 0x882b4: F_long (from LONG: a3 = 0x1ff at 0x882a4, a2 from slot
   0xa8 at 0x882b0) and F_neither (B9, 0x884ac-0x884c0: a2 = 0x216a0, a3 = s7 = line) *)
Definition pf_ref3 (rd : reader) (v : pfv) (pos : Z) (f : list Z) (fa : Z) (args : list arg) (a3 : Z) : Prop :=
  (f = F_long /\ fa = seg_litA_rc F_long /\ args = [AI 511] /\ a3 = 511) \/
  (f = F_neither /\ fa = seg_litA_rc F_neither /\
   exists x, args = [AS x] /\ sa_str rd a3 x /\ pf_inb (pf_F v pos + PF_O_BUF) a3 x).
(* the three refusals that enter the shared header call at 0x885ec (a2 set before, a3 = s7 at 0x885f4): F_after
   (0x883ec-0x883f4, the line), F_notclosed (0x884a0-0x884a8, the line), F_outside (B9, 0x885e4-0x885e8, the key) *)
Definition pf_href (rd : reader) (v : pfv) (pos : Z) (f : list Z) (fa : Z) (args : list arg) (xp : Z) : Prop :=
  (f = F_after \/ f = F_notclosed \/ f = F_outside) /\ fa = seg_litA_rc f /\
  exists x, args = [AS x] /\ sa_str rd xp x /\ pf_inb (pf_F v pos + PF_O_BUF) xp x.
(* the two refusals of the toolong / bound call 0x887d8 (entered at 0x887cc, a3 = s7 = name at 0x887d4):
   F_toolong (0x887c0-0x887c8: a4 = 15), F_bound (B8a, 0x88d58-0x88d64: a4 = 32) *)
Definition pf_reftl (f : list Z) (fa k : Z) : Prop :=
  ((f = F_toolong /\ k = 15) \/ (f = F_bound /\ k = 32)) /\ fa = seg_litA_rc f.
(* the three refusals of the shared key call 0x889a0 (a0 = c, a1 = s6, a3 = slot 0x40 = cur_name): F_knock (B9,
   0x88988-0x8899c: a4 = slot 0x70 = val), F_nokey (B9, 0x885c8-0x885e0: a4 = s7 = key), F_badignore (B12,
   0x888a4-0x888b8: a4 = val) *)
Definition pf_kref (rd : reader) (v : pfv) (pos : Z) (nm : list Z) (f : list Z) (fa : Z) (args : list arg)
  (xp : Z) : Prop :=
  (f = F_knock \/ f = F_nokey \/ f = F_badignore) /\ fa = seg_litA_rc f /\
  exists x, args = [AS nm; AS x] /\ sa_str rd xp x /\ pf_inb (pf_F v pos + PF_O_BUF) xp x.

(** *** The cuts: the state INV_<CUT>, and H_<CUT>: from that state the walk reaches the post *)

(* ENTRY (0x87e38, B1): the contract over the bundle (check_reply_m.v CR_ENTRY_stmt); sa_frm0 is the ambient FP
   state's rounding mode (the contract's reader_pre conjunct) *)
Definition H_ENTRY : Prop :=
  forall v, pf_cx v -> sa_frm0 ->
  SRr SEGS (p_W v) (cfg_at SEGS (BASE + PF_ENTRY) (p_regs v) (p_mem v) (p_md v)) (PF_POST v).

(* FTAKEN (0x87edc, B2; `sd a0,136(s1)`): frame_alloc_5 returned the class-5 frame F (aj_stack_malloc_atS's post:
   the journal with (5, pos) own, the flag pointer, the frame's whole shadow 0), `bnez a0` (0x87ebc) taken.
   a0 = a3 = F (0x87eb8), s3 = label (0x87e80), s11 = t (0x87e84); c in slot 0xc8 (pf_fi), untouched. *)
Definition INV_FTAKEN (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) : Prop :=
  pf_cx v /\ pf_fi v pos lyc Sc Wc rX memc mdc /\ pf_obj v lyc Sc (rdW Wc memc) /\ pf_lab v lyc Sc (rdW Wc memc) /\
  sa_rconf (rdW Wc memc) (p_c v) (p_rcs v) /\
  zero_shadow (rdW Wc memc) SHADOW_OFF (pf_F v pos) (fs_frame_bytes 5) /\
  pf_rg rX [(10, pf_F v pos); (13, pf_F v pos); (19, p_lp v); (27, p_t v)].
Definition H_FTAKEN : Prop :=
  forall v pos lyc Sc Wc rX memc mdc, INV_FTAKEN v pos lyc Sc Wc rX memc mdc ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_FTAKEN) rX memc mdc) (PF_POST v).

(* FRAME (0x88074, B3; `ld a0,200(s1)`, the first instruction of the c trap tests T01 / T02): the frame header
   (0x87f08-0x87f14) and the 144 shadow cells laid (0x87f20-0x88070), every object out of scope; slots 0x88 (F,
   0x87edc), 0x98 (F, 0x87f10), 0xd8 (SH + 8, 0x87f48); s5 = SH (0x87f1c), s3 = label, s11 = t *)
Definition INV_FRAME (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) : Prop :=
  pf_cx v /\ pf_fi v pos lyc Sc Wc rX memc mdc /\ pf_obj v lyc Sc (rdW Wc memc) /\ pf_lab v lyc Sc (rdW Wc memc) /\
  sa_rconf (rdW Wc memc) (p_c v) (p_rcs v) /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x88, pf_F v pos); (0x98, pf_F v pos); (0xd8, pf_SH v pos + 8)] /\
  pf_fsh (rdW Wc memc) (pf_SH v pos) PF_SC0 /\
  pf_rg rX [(21, pf_SH v pos); (19, p_lp v); (27, p_t v)].
Definition H_FRAME : Prop :=
  forall v pos lyc Sc Wc rX memc mdc, INV_FRAME v pos lyc Sc Wc rX memc mdc ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_FRAME) rX memc mdc) (PF_POST v).

(* DONE (0x89114, B4): the loop has ended (B3's empty text, `bnez` 0x88158 not taken -> 0x8815c; the tail's
   `*p == 0`, 0x88628 not taken -> 0x8862c). B4 builds sh(&c->n) from slot 0x50 into s4 (0x89118, the one write
   of s4 after the entry), checks and reads c->n through slot 0x58 (B#40), puts cur_name out of scope (0x89130,
   s5), reloads F from slots 0x88 / 0x98, stores the retired magic at F (0x89164), releases the frame by
   frame_release_5 (0x89170, a0 = slot 0x88, a1 = 0x480) and returns (sp = s0 - 352, 0x89188). Post: the function's
   post from c's state cf (the plain H_DONE). *)
Definition INV_DONE (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (cf : rconf) : Prop :=
  pf_cx v /\ pf_fi v pos lyc Sc Wc rX memc mdc /\ pf_obj v lyc Sc (rdW Wc memc) /\
  sa_rconf (rdW Wc memc) (p_c v) cf /\
  pf_sl (rdW Wc memc) (pf_s1 v)
    [(0x50, (p_c v + seg_spec.RC_N) / 8); (0x58, p_c v + seg_spec.RC_N); (0x88, pf_F v pos); (0x98, pf_F v pos)] /\
  pf_fsh (rdW Wc memc) (pf_SH v pos) PF_SC_HEAD /\
  pf_rg rX [(21, pf_SH v pos)].
Definition H_DONE : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf, INV_DONE v pos lyc Sc Wc rX memc mdc cf ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_DONE) rX memc mdc) (PF_POSTr v cf).

(* HEAD (0x881f8, B5; `li a1,10; mv a0,s11; jal strchr`): the line-loop head (the plain H_HEAD). A line starts at
   o (o < length s), p = s11 = t + o (0x87e84 for o = 0; the latch's `mv s11,s9` 0x88624), ln = lineno = s8 lines
   consumed (0x88160 for 0; the latch's `mv s8,s6` 0x88620), cur in slot 0xc0 (pf_st), c holds cf, cur_name holds
   nm; buf out of scope (entry state, or 0x88608). Post: the function's post from r_lines (cf, cur, nm) ln
   (lines rest), rest = skipn o s; n bounds length rest. *)
Definition INV_HEAD (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_HEAD /\
  pf_lctx (p_s v) o ln d /\ (o < length (p_s v))%nat /\ (length (skipn o (p_s v)) <= n)%nat /\
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ [(27, p_t v + Z.of_nat o); (24, ln)]).
Definition H_HEAD (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_HEAD n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_HEAD) rX memc mdc)
    (PF_POSTr v (fst (fst (r_lines (cf, cur, nm) ln (lines (skipn o (p_s v))))))).

(* TAIL (0x88600, B5; `li a1,64; ld a0,216(s1); jal meta_fill_f8`): a line has been read (the plain H_TAIL). o is
   the next line's offset, p' = s9 = t + o, ln = s6 the lines read; the meta_fill_f8 at 0x88608 puts buf out of
   scope: at TAIL buf is still IN scope. The rest is shorter than n: the head it loops to is H_HEAD (pred n). *)
Definition INV_TAIL (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\
  pf_lctx (p_s v) o ln d /\ (length (skipn o (p_s v)) < n)%nat /\
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ [(25, p_t v + Z.of_nat o); (22, ln)]).
Definition H_TAIL (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_TAIL n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_TAIL) rX memc mdc)
    (PF_POSTr v (fst (fst (r_lines (cf, cur, nm) ln (lines (skipn o (p_s v))))))).

(* LONG (0x88258, B6; `bltu s7,a0` (a0 = 512) at 0x88254 not taken): at = s11 = t + o, len = s7 (0x88210 /
   0x88230), buf in scope (0x8824c). The step is r_line's long branch. *)
Definition INV_LONG (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) /\
  (512 <= length (pf_line (p_s v) o))%nat /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(27, p_t v + Z.of_nat o); (23, Z.of_nat (length (pf_line (p_s v) o)))]).
Definition H_LONG (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d, INV_LONG n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_LONG) rX memc mdc)
    (pf_postm v (r_line cf cur nm (ln + 1) (pf_line (p_s v) o)) o ln).

(* REF3 (0x882b4, B6's shared refuse call `jal refuse`; entered from LONG's path (falls in from 0x882b0) and from
   B9 by `j 0x882b4` at 0x884c0): refuse(c, lineno, f, a3) with a0 = c (slot 0xc8), a1 = s6 = lineno, a2 = f's
   literal, a3 per pf_ref3; slot 0xc0 = the step's cur' (the masked cur of 0x88288-0x882a0, or the key line's
   cur), then `j` TAIL (0x882b8). *)
Definition INV_REF3 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur' : option nat)
  (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)) (f : list Z) (fa : Z) (args : list arg) (a3 : Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf cur' nm (length (skipn o (p_s v))) /\
  pf_ref3 (rdW Wc memc) v pos f fa args a3 /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(10, p_c v); (11, ln + 1); (12, fa); (13, a3)]).
Definition H_REF3 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d f fa args a3,
  INV_REF3 n v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d f fa args a3 ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_REF3) rX memc mdc)
    (pf_postm v (refuse cf (ln + 1) f args, cur', nm) o ln).

(* HDR (0x883b4, B7; `bne a0,'['` at 0x883b0 not taken): the line (len < 512) copied into buf (0x882c8), its
   comment cut (0x882f8 loop), trimmed (0x8838c); s7 = lp = the trimmed line pf_tline s o in buf (0x88390), first
   byte '[' (0x883a4). The step is r_header. *)
Definition INV_HDR (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (lp : Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) /\
  (length (pf_line (p_s v) o) < 512)%nat /\
  sa_str (rdW Wc memc) lp (pf_tline (p_s v) o) /\ pf_inb (pf_F v pos + PF_O_BUF) lp (pf_tline (p_s v) o) /\
  hd0 (pf_tline (p_s v) o) = LBR /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(23, lp)]).
Definition H_HDR (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp,
  INV_HDR n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_HDR) rX memc mdc)
    (pf_postm v (r_header cf nm (ln + 1) (pf_tline (p_s v) o)) o ln).

(* KEY (0x883f8, B9; `bne a0,'['` at 0x883b0 taken): as HDR, but the trimmed line is neither empty (`beqz`
   0x883a8) nor a header. The step is r_key. *)
Definition INV_KEY (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (lp : Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) /\
  (length (pf_line (p_s v) o) < 512)%nat /\
  sa_str (rdW Wc memc) lp (pf_tline (p_s v) o) /\ pf_inb (pf_F v pos + PF_O_BUF) lp (pf_tline (p_s v) o) /\
  hd0 (pf_tline (p_s v) o) <> 0 /\ hd0 (pf_tline (p_s v) o) <> LBR /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(23, lp)]).
Definition H_KEY (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp,
  INV_KEY n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_KEY) rX memc mdc)
    (pf_postm v (r_key cf cur nm (ln + 1) (pf_tline (p_s v) o)) o ln).

(* HREF (0x885ec, B7; `ld a0,200(s1); mv a1,s6; mv a3,s7; jal refuse` then CLR): the shared header refusal,
   a2 = f's literal set before the cut, s7 = the string argument (pf_href); c holds cf. The step's cur is NULL
   (CLR stores it). *)
Definition INV_HREF (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (f : list Z) (fa : Z) (args : list arg) (xp : Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) /\
  pf_href (rdW Wc memc) v pos f fa args xp /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(12, fa); (23, xp)]).
Definition H_HREF (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d f fa args xp,
  INV_HREF n v pos lyc Sc Wc rX memc mdc cf nm o ln d f fa args xp ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_HREF) rX memc mdc)
    (pf_postm v (refuse cf (ln + 1) f args, None, nm) o ln).

(* CLR (0x885fc, B7; `sd zero,192(s1)` then falls into TAIL): after a header refusal (HREF's call 0x885f8, which
   also serves unknown from 0x8851c; REFTL's call, `j 0x885fc` at 0x887dc; noname's call 0x88c98, `j` at 0x88c9c)
   c holds cf; the step's cur is NULL. *)
Definition INV_CLR (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn (pf_next (p_s v) o) (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln).
Definition H_CLR (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d, INV_CLR n v pos lyc Sc Wc rX memc mdc cf nm o ln d ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_CLR) rX memc mdc) (pf_postm v (cf, None, nm) o ln).

(* REFTL (0x887cc, B7; `ld a0,200(s1); mv a1,s6; mv a3,s7; jal refuse` (0x887d8), `j` CLR): the toolong / bound
   refusal, a2 = f's literal and a4 = k set before the cut (pf_reftl), s7 = the name (0x88790; B8a reloads it from
   slot 0xc0 at 0x88d2c); c holds cf (for bound: c->overflow already incremented, 0x88d54). The counters' room is
   that after this line (the rest from pf_next s o, as CLR's), with one more for refused (this call's refusal):
   the bound path has spent one overflow before the cut, so the room of the line start does not hold here. *)
Definition INV_REFTL (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (f : list Z) (fa k np : Z) (name : list Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn (pf_next (p_s v) o) (p_s v))) /\
  rc_refused cf + Z.of_nat (length (skipn (pf_next (p_s v) o) (p_s v))) + 1 + 2 ^ 16 < 2 ^ 32 /\
  pf_reftl f fa k /\
  sa_str (rdW Wc memc) np name /\ pf_inb (pf_F v pos + PF_O_BUF) np name /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(12, fa); (14, k); (23, np)]).
Definition H_REFTL (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d f fa k np name,
  INV_REFTL n v pos lyc Sc Wc rX memc mdc cf nm o ln d f fa k np name ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_REFTL) rX memc mdc)
    (pf_postm v (refuse cf (ln + 1) f [AS name; AI k], None, nm) o ln).

(* SEG (0x88ca0, B8a; `bltu a0,16` at 0x887bc taken): the header's name (1 to 15 bytes: `beqz` 0x887ac not taken,
   strlen 0x887b4) is in buf at np = s7 (trim at 0x8878c), s3 = 32 (0x887a8; NEW's T32 reads it on the `blez`
   path). B8a builds sh(&c->n) from slot 0x50 (B#29), loads n, runs the strcmp search (0x88d04) and the bound
   test. The post is the header step from seg_get on. *)
Definition INV_SEG (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (np : Z) (name : list Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) np name /\ pf_inb (pf_F v pos + PF_O_BUF) np name /\ (1 <= length name <= 15)%nat /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(19, 32); (23, np)]).
Definition H_SEG (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d np name,
  INV_SEG n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_SEG) rX memc mdc) (pf_postm v (pf_seg_step cf nm (ln + 1) name) o ln).

(* NEW (0x88e54, B8b; from `blez a2` 0x88cb8 (n = 0: a3 = 0x88ca4's sh(&c->n), a2 = 0x88cb4's n) or `blt a2,s3`
   0x88d38 (a2 = slot 0x68 = n, a3 = slot 0x60 = sh(&c->n), 0x88d30 / 0x88d34)): no entry has the name and there
   is room; s3 = 32 (0x887a8 / 0x88d28), s7 = name (0x88d2c on the search path). B8b checks and stores n + 1
   (B#35, T32), forms &seg[n] (T33), memsets it (0x88e90), names it (0x88ea8), then the seen_gen store and
   cur_name's snprintf (0x88e4c). *)
Definition INV_NEW (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (np : Z) (name : list Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) np name /\ pf_inb (pf_F v pos + PF_O_BUF) np name /\ (1 <= length name <= 15)%nat /\
  r_find_go (rc_seg cf) name 0 = None /\ (length (rc_seg cf) < 32)%nat /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(12, Z.of_nat (length (rc_seg cf))); (13, shadow_addr (p_c v + seg_spec.RC_N)); (19, 32); (23, np)]).
Definition H_NEW (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d np name,
  INV_NEW n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_NEW) rX memc mdc) (pf_postm v (pf_seg_step cf nm (ln + 1) name) o ln).

(* FOUND (0x88eb0, B8b; strcmp == 0, `beqz` at 0x88d08): entry i has the name; s3 = &seg[i], s7 =
   &seg[i].seen_gen (two of the search's four induction values, 0x88d10 / 0x88d18; B#36 tests s7), slot 0xc0 =
   the name (0x88cc0; B8b reloads it at 0x88edc). *)
Definition INV_FOUND (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (np : Z) (name : list Z) (i : nat) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st0 v pos (rdW Wc memc) cf nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) np name /\ pf_inb (pf_F v pos + PF_O_BUF) np name /\ (1 <= length name <= 15)%nat /\
  r_find_go (rc_seg cf) name 0 = Some i /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0xc0, np)] /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(19, seg_spec.rseg_addr (p_c v) i); (23, seg_spec.rseg_addr (p_c v) i + seg_spec.RS_SEEN_GEN)]).
Definition H_FOUND (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i,
  INV_FOUND n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_FOUND) rX memc mdc) (pf_postm v (pf_seg_step cf nm (ln + 1) name) o ln).

(* PROV2 (0x88e4c, B8b's shared snprintf `jal wrapper_snprintf`; entered from B12, which falls in from 0x88e48):
   the ignore branch has stored ignore = b and ignore_set = 1 (B#33, B#34): c holds pf_prov_mid (PIgn b) cf gi;
   a0 = &seg[gi].ignore_file (0x88e38), a1 = 0x60, a2 = "%s" (0x88e40), a3 = c->reading (slot 0x48, 0x88e48).
   snprintf gives pf_prov_fin (PIgn b) cf gi, then `j` TAIL (0x88e50). *)
Definition INV_PROV2 (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (b : bool) (gi : nat) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) (pf_prov_mid (PIgn b) cf gi) (Some gi) nm (length (skipn (pf_next (p_s v) o) (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(10, seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE); (11, 0x60); (12, seg_litA_rc F_s);
             (13, p_c v + seg_spec.RC_READING)]).
Definition H_PROV2 (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d b gi, INV_PROV2 n v pos lyc Sc Wc rX memc mdc cf nm o ln d b gi ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_PROV2) rX memc mdc) (pf_postm v (pf_prov_fin (PIgn b) cf gi, Some gi, nm) o ln).

(* ROLE / MODEL / IGN (0x88630 B10a, 0x886d4 B11a, 0x887e0 B12; the strcasecmp dispatch 0x88584 / 0x88598 /
   0x885ac): the key line is split (pf_kv; key in s7 at 0x8842c, val in s3 at 0x88438 / 0x8856c), cur = Some gi in
   slot 0xc0 (`beqz a5` at 0x88570 not taken), val spilled to slot 0x70 (0x88574; every later read of val is from
   there: 0x88650, 0x886e0, 0x887e8, 0x88880, 0x88974, 0x8899c, 0x88be4). The step is r_key. *)
Definition INV_KV (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (kp vp : Z) (key val : list Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  pf_kv (rdW Wc memc) v pos (pf_tline (p_s v) o) kp vp key val /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x70, vp)] /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln).
Definition H_ROLE (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val,
  INV_KV n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val ->
  strcasecmp key S_role = 0 ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_ROLE) rX memc mdc)
    (pf_postm v (r_key cf (Some gi) nm (ln + 1) (pf_tline (p_s v) o)) o ln).
Definition H_MODEL (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val,
  INV_KV n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val ->
  strcasecmp key S_role <> 0 -> strcasecmp key S_model = 0 ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_MODEL) rX memc mdc)
    (pf_postm v (r_key cf (Some gi) nm (ln + 1) (pf_tline (p_s v) o)) o ln).
Definition H_IGN (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val,
  INV_KV n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val ->
  strcasecmp key S_role <> 0 -> strcasecmp key S_model <> 0 -> strcasecmp key S_ignore = 0 ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_IGN) rX memc mdc)
    (pf_postm v (r_key cf (Some gi) nm (ln + 1) (pf_tline (p_s v) o)) o ln).

(* INTENT (0x888e4, B10b; after the fold loop and low[li] = 0 at 0x888e0, B#25): low (in scope since
   0x88630-0x8864c) holds the 64 bytes LB with r_low val 0 64 and its NUL first (the plain H_INTENT's O1 form;
   bcmp reads up to 7 of them); s7 = low (slot 0xa0, 0x888c8), val in slot 0x70 (the bad-role refusal reads it at
   0x88974). The step is pf_role_step. *)
Definition INV_INTENT (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LOW /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  (exists LB : list byte, length LB = 64%nat /\ sa_bytes (rdW Wc memc) (pf_F v pos + PF_O_LOW) LB /\
     firstn (S (length (r_low val 0 64))) (seg_spec.zs LB) = r_low val 0 64 ++ [0]) /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x70, vp)] /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(23, pf_F v pos + PF_O_LOW)]).
Definition H_INTENT (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_INTENT n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_INTENT) rX memc mdc) (pf_postm v (pf_role_step cf gi nm (ln + 1) val) o ln).

(* KREF (0x889a0, B9's shared key refusal `jal refuse`, then `j` TAIL 0x889a4; entered from B9's knock path
   (falls in from 0x8899c), its nokey path (`j` at 0x885e0) and B12's bad ignore (`j` at 0x888b8)):
   refuse(c, lineno, f, cur_name, x) per pf_kref; cur unchanged in slot 0xc0. *)
Definition INV_KREF (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (cur : option nat) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (f : list Z) (fa : Z) (args : list arg) (xp : Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_LINE /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf cur nm (length (skipn o (p_s v))) /\
  pf_kref (rdW Wc memc) v pos nm f fa args xp /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(10, p_c v); (11, ln + 1); (12, fa); (13, pf_F v pos + PF_O_CN); (14, xp)]).
Definition H_KREF (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf cur nm o ln d f fa args xp,
  INV_KREF n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d f fa args xp ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_KREF) rX memc mdc)
    (pf_postm v (refuse cf (ln + 1) f args, cur, nm) o ln).

(* MISS (0x88a50, B11b; reac_box_catalogue_by_token returned NULL, `beqz` at 0x889dc): model low in scope
   (0x886d4-0x886dc), known / ntok out; val in slot 0x70, cur in slot 0xc0. B11b lays known's scope, sets ntok = 0,
   calls reac_box_catalogue (0x88ad8), joins the 11 tokens into known (0x88b14 loop, B#28, T23-T27) and leaves at
   KREFM. *)
Definition INV_MISS (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_L146 /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  by_token (r_low val 0 24) = None /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x70, vp)] /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln).
Definition H_MISS (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_MISS n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_MISS) rX memc mdc)
    (pf_postm v (refuse cf (ln + 1) F_badmodel [AS nm; AS val; AS known], Some gi, nm) o ln).

(* KREFM (0x88bd0, B11c; the join loop's exit, `bgeu s3,a1` at 0x88bb8 taken): known (in scope with ntok since
   0x88a50-0x88ac8) holds SegModel.known and its NUL; s2 = '#' again (0x88bb4). B11c refuses with F_badmodel
   (0x88bec: a3 = slot 0x40 = cur_name, a4 = slot 0x70 = val, a5 = slot 0x78 = known), puts known / ntok out
   (0x88bf4-0x88c6c, a0 = -8 at 0x88bf0) and falls into LOWOUT's code. *)
Definition INV_KREFM (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_KNOWN /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  sa_str (rdW Wc memc) (pf_F v pos + PF_O_KNOWN) known /\
  pf_sl (rdW Wc memc) (pf_s1 v) [(0x70, vp)] /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln).
Definition H_KREFM (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_KREFM n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_KREFM) rX memc mdc)
    (pf_postm v (refuse cf (ln + 1) F_badmodel [AS nm; AS val; AS known], Some gi, nm) o ln).

(* LOWOUT (0x88c70, B11c; from the hit path `j 0x88c70` at 0x88a44, and the miss path's fall-through from
   0x88c6c): the model step is done, c holds cf; model low still in scope (its out-stores begin here), known /
   ntok out; a0 = -8 (0x88a40 / 0x88bf0), cur in slot 0xc0. *)
Definition INV_LOWOUT (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) : Prop :=
  pf_base v pos lyc Sc Wc rX memc mdc PF_SC_L146 /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn (pf_next (p_s v) o) (p_s v))) /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ [(10, -8)]).
Definition H_LOWOUT (n : nat) : Prop :=
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi, INV_LOWOUT n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_LOWOUT) rX memc mdc) (pf_postm v (cf, Some gi, nm) o ln).

End e.
End f.
End d.

(** ** The segments (cover and counts: PLAN-pf-asanubsan section 5.2, `seg.py`: 1328 instructions, no gap, no
    overlap). Each holds at every ambient FP state (the f0 binder); its exit cuts are taken at every FP state (the
    HA_ forms). A statement names no callee: each segment FILE takes, as Section hypotheses, the runtime entries
    and program callees of its own calls, each at every FP state (`forall fx0 : YK11.FPState, ...`). Entries and
    call targets are LISTING terms: a runtime entry or trampoline is `pa_sigma SS_<name>` (B's SegSyms.v; B's
    address = A's + 0x8c), a program callee is `BASE + AF_<F>` (B's SegList.v). The wrapper texts are image B's
    carriers (the image-B wrapper-layer owner, a working branch: lib/B/Rt/RtSeg.v, SegRtPC.v; RtString / RtFormat /
    RtStack as they land, until then a local verbatim copy marked pending under the carrier's module-qualified
    name):
      strchr        RtSeg.astrchr_realizes at pa_sigma SS___interceptor_trampoline_strchr            B5, B7, B9
      strncasecmp   RtSeg.astrncasecmp_realizes at pa_sigma SS___interceptor_trampoline_strncasecmp  B7
      strcasecmp    RtSeg.astrcasecmp_realizes at pa_sigma SS___interceptor_trampoline_strcasecmp    B9, B12
      strlen        RtString.astrlen_realizes at pa_sigma SS___interceptor_trampoline_strlen         B5, B7, B9
      strspn        RtString.astrspn_realizes at pa_sigma SS___interceptor_trampoline_strspn, gotwA,
                      guardA                                                                    B6
      strcmp        RtString.astrcmp_realizes at pa_sigma SS___interceptor_trampoline_strcmp         B8a
      snprintf      RtFormat.asnprintf_realizes at pa_sigma SS___interceptor_trampoline_snprintf, gotwA,
                      guardA                                       B3, B8b (2 sites), B10b, B11a (2 sites), B11b
      bcmp          the kit's abcmp_realizes (lib/B/YG0d.v) at pa_sigma SS___interceptor_trampoline_bcmp  B10b
      memcpy        aintrin_realizes OCpy at pa_sigma SS___asan_memcpy (lib/B/YG0d.v)          B5
      memset        aintrin_realizes OSet at pa_sigma SS___asan_memset                         B3, B8b
      set_shadow    aset_shadow_realizes at pa_sigma SS___asan_set_shadow_f8, 0xf8 (B2, B5) and
                      pa_sigma SS___asan_set_shadow_00, 0x00 (B5; B4's call 0x89180 is dead)
      frame take    astack_malloc_realizes 5 (pa_sigma SS___asan_stack_malloc_5), stack_malloc_progressP  B1
      frame release RtStack.astack_free_cls_realizes at pa_sigma SS___asan_stack_free_5, 5            B4
      refuse        refuse_contract at BASE + AF_refuse, STK_refuse, RLO_A, RHI_A, seg_litA_rc, gotwA, guardA
                      B6, B7 (3 sites), B8b, B9, B10b, B11c
      trim          trim_contract at BASE + AF_trim, STK_trim, RLO_A, RHI_A                    B5, B7 (2), B9 (2)
      by_token      reac_box_catalogue_by_token_contract at BASE + AF_reac_box_catalogue_by_token,
                      STK_reac_box_catalogue_by_token, RLO_A, RHI_A, catA                       B11a
      catalogue     reac_box_catalogue_contract at BASE + AF_reac_box_catalogue, STK_reac_box_catalogue, catA
                                                                                                B11b
    plus the image facts the walks share (SegInstB's seg_litA_rc_facts / seg_litA_rc_S_base over RC_LITS and
    STK_values; B's SegObj seg_val_objs / seg_sig_prog; the walk records of the listing). The walk theorem is at
    BASE + AF_reac_segconf_parse_file (the brief's form); SegInstB's A_reac_segconf_parse_file_A_AF ties it to
    A_reac_segconf_parse_file_A when the closing file pins BASE = seg_text. *)
Section s.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.
Definition HA_FTAKEN : Prop := forall f1 : YK11.FPState, H_FTAKEN (fx := f1) B.
Definition HA_FRAME : Prop := forall f1 : YK11.FPState, H_FRAME (fx := f1) B.
Definition HA_DONE : Prop := forall f1 : YK11.FPState, H_DONE (fx := f1) B.
Definition HA_HEAD (n : nat) : Prop := forall f1 : YK11.FPState, H_HEAD (fx := f1) B n.
Definition HA_TAIL (n : nat) : Prop := forall f1 : YK11.FPState, H_TAIL (fx := f1) B n.
Definition HA_LONG (n : nat) : Prop := forall f1 : YK11.FPState, H_LONG (fx := f1) B n.
Definition HA_REF3 (n : nat) : Prop := forall f1 : YK11.FPState, H_REF3 (fx := f1) B n.
Definition HA_HDR (n : nat) : Prop := forall f1 : YK11.FPState, H_HDR (fx := f1) B n.
Definition HA_KEY (n : nat) : Prop := forall f1 : YK11.FPState, H_KEY (fx := f1) B n.
Definition HA_HREF (n : nat) : Prop := forall f1 : YK11.FPState, H_HREF (fx := f1) B n.
Definition HA_CLR (n : nat) : Prop := forall f1 : YK11.FPState, H_CLR (fx := f1) B n.
Definition HA_REFTL (n : nat) : Prop := forall f1 : YK11.FPState, H_REFTL (fx := f1) B n.
Definition HA_SEG (n : nat) : Prop := forall f1 : YK11.FPState, H_SEG (fx := f1) B n.
Definition HA_NEW (n : nat) : Prop := forall f1 : YK11.FPState, H_NEW (fx := f1) B n.
Definition HA_FOUND (n : nat) : Prop := forall f1 : YK11.FPState, H_FOUND (fx := f1) B n.
Definition HA_PROV2 (n : nat) : Prop := forall f1 : YK11.FPState, H_PROV2 (fx := f1) B n.
Definition HA_ROLE (n : nat) : Prop := forall f1 : YK11.FPState, H_ROLE (fx := f1) B n.
Definition HA_MODEL (n : nat) : Prop := forall f1 : YK11.FPState, H_MODEL (fx := f1) B n.
Definition HA_IGN (n : nat) : Prop := forall f1 : YK11.FPState, H_IGN (fx := f1) B n.
Definition HA_INTENT (n : nat) : Prop := forall f1 : YK11.FPState, H_INTENT (fx := f1) B n.
Definition HA_KREF (n : nat) : Prop := forall f1 : YK11.FPState, H_KREF (fx := f1) B n.
Definition HA_MISS (n : nat) : Prop := forall f1 : YK11.FPState, H_MISS (fx := f1) B n.
Definition HA_KREFM (n : nat) : Prop := forall f1 : YK11.FPState, H_KREFM (fx := f1) B n.
Definition HA_LOWOUT (n : nat) : Prop := forall f1 : YK11.FPState, H_LOWOUT (fx := f1) B n.

(* B1 (A1), 0x87e38-0x87edc, 41 instructions: the prologue, c to slot 0xc8, the GOT loads of the shadow base and
   the use-after-return flag, frame_alloc_5 (0x87eac). ENTRY -> FTAKEN. *)
Definition S_B1 : Prop := forall f0 : YK11.FPState, HA_FTAKEN -> H_ENTRY (fx := f0) B.
(* B2 (A2), 0x87edc-0x88074, 102: slots 0x88 / 0xf0 / 0x98 / 0xd8, the frame header, the 144 shadow cells
   (meta_fill_f8 0x87f4c). FTAKEN -> FRAME. *)
Definition S_B2 : Prop := forall f0 : YK11.FPState, HA_FRAME -> H_FTAKEN (fx := f0) B.
(* B3 (A3), 0x88074-0x881f8 + cold 0x891cc-0x891f8, 108: T01 / T02, snprintf(c->reading) (0x880cc), c->gen++
   (B#1), the text-NULL test (decided: t <> 0), cur_name in scope and memset (0x88130), *p (B#2), the setup slots.
   FRAME -> DONE (empty text) or HEAD (o = 0, ln = 0, d = [], cf = pf_start rcs lab, cur = None, nm = []). *)
Definition S_B3 : Prop := forall f0 : YK11.FPState, (forall n, HA_HEAD n) -> HA_DONE -> H_FRAME (fx := f0) B.
(* B4 (A4), 0x89114-0x891cc (with the `unimp` 0x891c8) + cold 0x891f8-0x89224, 57 (of which 0x89144-0x89158,
   0x89178-0x89180 and 0x89210-0x89224 dead): B#40, cur_name out, the retired magic, frame_release_5 (0x89170),
   the epilogue. DONE -> the return. *)
Definition S_B4 : Prop := forall f0 : YK11.FPState, H_DONE (fx := f0) B.
(* B5 (A5), 116: the line driver (strchr / strlen, T03 - T05, meta_fill_00, memcpy, T07, strip_comment (T08,
   T09), trim, the tail's meta_fill_f8 and *p). Its head half: HEAD -> LONG, HDR, KEY or TAIL (empty line,
   0x883a8); its tail half: TAIL -> HEAD (pred n) or DONE. The two halves are separate statements so that they can
   be proved apart; S_B5 is both. *)
Definition S_B5h : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_LONG n -> HA_HDR n -> HA_KEY n -> HA_TAIL n -> H_HEAD (fx := f0) B n.
Definition S_B5t : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_HEAD (pred n) -> HA_DONE -> H_TAIL (fx := f0) B n.
Definition S_B5 : Prop := S_B5h /\ S_B5t.
(* B6 (A6, and B9's neither through the shared call), 29: strspn, T06, at[lead] (B#3), refuse (0x882b4).
   LONG -> TAIL; REF3 -> TAIL. *)
Definition S_B6 : Prop :=
  forall (f0 : YK11.FPState) (n : nat),
    (HA_TAIL n -> H_LONG (fx := f0) B n) /\ (HA_TAIL n -> H_REF3 (fx := f0) B n).
(* B7 (A7), 101: strchr ']', close[1] (B#8, T10), *close = 0 (B#12, T13), trim, strncasecmp "segment", body[7]
   (B#20, T19), trim, *name (B#21), strlen, the refusals after / notclosed / unknown / outside (HREF), noname,
   toolong / bound (REFTL), CLR. HDR -> TAIL (through CLR) or SEG; HREF -> TAIL; REFTL -> TAIL; CLR -> TAIL. *)
Definition S_B7 : Prop :=
  forall (f0 : YK11.FPState) (n : nat),
    (HA_TAIL n -> HA_SEG n -> H_HDR (fx := f0) B n) /\ (HA_TAIL n -> H_HREF (fx := f0) B n) /\
    (HA_TAIL n -> H_REFTL (fx := f0) B n) /\ (HA_TAIL n -> H_CLR (fx := f0) B n).
(* B8a (A8a), 61: B#29, the `blez` pre-test, the strcmp loop (0x88cf0, T28 / T29 each pass), c->overflow++
   (B#30), the bound refusal's arguments. SEG -> NEW, FOUND or REFTL. *)
Definition S_B8a : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_NEW n -> HA_FOUND n -> HA_REFTL n -> H_SEG (fx := f0) B n.
(* B8b (A8b), 98: n + 1 (B#35, T32), &seg[n] (T33), memset, snprintf(name), seen_gen vs gen (B#36, B#37),
   F_twice, cur (T34), the seen_gen store (B#38, B#39), the shared snprintf PROV2 (0x88e4c). NEW -> TAIL;
   FOUND -> TAIL; PROV2 -> TAIL. *)
Definition S_B8b : Prop :=
  forall (f0 : YK11.FPState) (n : nat),
    (HA_TAIL n -> H_NEW (fx := f0) B n) /\ (HA_TAIL n -> H_FOUND (fx := f0) B n) /\
    (HA_TAIL n -> H_PROV2 (fx := f0) B n).
(* B9 (A9), 131: strchr '=', *eq = 0 (B#9), two trims (T11), strlen, unquote (B#10, B#11, B#13, B#14, T12, T14 -
   T16), the cur test, the strcasecmp dispatch, knock / nokey and the shared key refusal KREF (0x889a0).
   KEY -> ROLE, MODEL, IGN, REF3 (no '='), HREF (cur = NULL) or TAIL (through KREF); KREF -> TAIL. *)
Definition S_B9 : Prop :=
  forall (f0 : YK11.FPState) (n : nat),
    (HA_ROLE n -> HA_MODEL n -> HA_IGN n -> HA_REF3 n -> HA_HREF n -> HA_TAIL n -> H_KEY (fx := f0) B n) /\
    (HA_TAIL n -> H_KREF (fx := f0) B n).
(* B10a (A10a), 61: low in scope, the fold loop (0x88674, B#16, B#17, T17), T20, low[li] = 0 (B#25).
   ROLE -> INTENT. *)
Definition S_B10a : Prop := forall (f0 : YK11.FPState) (n : nat), HA_INTENT n -> H_ROLE (fx := f0) B n.
(* B10b (A10b), 89: five bcmp, F_badrole (own call 0x88978), T30, role stores (B#31, B#32), snprintf(role_file),
   low out. INTENT -> TAIL. *)
Definition S_B10b : Prop := forall (f0 : YK11.FPState) (n : nat), HA_TAIL n -> H_INTENT (fx := f0) B n.
(* B11a (A11a), 91: model low in scope, the fold (0x88704, B#18, B#19, T18), T21, low[li] = 0 (B#26), by_token
   (0x889d8), T22, the model stores (B#27) and two snprintf. MODEL -> MISS or LOWOUT. *)
Definition S_B11a : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_MISS n -> HA_LOWOUT n -> H_MODEL (fx := f0) B n.
(* B11b (A11b's first half), 98: known / ntok scope, ntok = 0, reac_box_catalogue (0x88ad8), the join loop
   (0x88b14: T23 - T27, B#28, snprintf "%s%s"). MISS -> KREFM. *)
Definition S_B11b : Prop := forall (f0 : YK11.FPState) (n : nat), HA_KREFM n -> H_MISS (fx := f0) B n.
(* B11c (A11b's second half), 44: F_badmodel (0x88bec), known / ntok out, model low out (LOWOUT's code).
   KREFM -> TAIL; LOWOUT -> TAIL. *)
Definition S_B11c : Prop :=
  forall (f0 : YK11.FPState) (n : nat),
    (HA_TAIL n -> H_KREFM (fx := f0) B n) /\ (HA_TAIL n -> H_LOWOUT (fx := f0) B n).
(* B12 (A12), 101: four strcasecmp, "1" / "0" (B#22 - B#24), the bad ignore's arguments (to KREF), T31, the ignore
   stores (B#33, B#34) and PROV2's arguments. IGN -> KREF or PROV2. *)
Definition S_B12 : Prop :=
  forall (f0 : YK11.FPState) (n : nat), HA_KREF n -> HA_PROV2 n -> H_IGN (fx := f0) B n.
End s.

(** ** The whole function from its segments (NOT proved here). The loop by induction on n (the plain F3):
    H_TAIL 0 holds outright (its rest would be shorter than 0); S_B5t gives H_TAIL (S n) from H_HEAD n and H_DONE
    (S_B4); within one n the mid-line cuts follow from H_TAIL n in the order LOWOUT, KREFM (S_B11c), MISS (S_B11b),
    MODEL (S_B11a); PROV2 (S_B8b), KREF (S_B9), IGN (S_B12); INTENT (S_B10b), ROLE (S_B10a); REF3, LONG (S_B6);
    CLR, HREF, REFTL (S_B7), NEW, FOUND (S_B8b), SEG (S_B8a), HDR (S_B7); KEY (S_B9); then H_HEAD n (S_B5h). S_B3
    takes H_HEAD at every n, S_B2 and S_B1 close the entry, and H_ENTRY at the ambient FP state is the contract
    after the bundle is unpacked. *)
Section g.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Variable B : asyms.
Definition pf_pieces_give_contract : Prop :=
  S_B1 B -> S_B2 B -> S_B3 B -> S_B4 B -> S_B5 B -> S_B6 B -> S_B7 B -> S_B8a B -> S_B8b B -> S_B9 B ->
  S_B10a B -> S_B10b B -> S_B11a B -> S_B11b B -> S_B11c B -> S_B12 B ->
  reac_segconf_parse_file_contract SEGS B (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file
    RLO_A RHI_A seg_litA_rc catA gotwA guardA.
End g.
