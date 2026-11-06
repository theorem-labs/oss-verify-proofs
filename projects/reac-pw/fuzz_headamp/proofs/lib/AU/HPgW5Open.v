(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at (lines 2155-2206) restated for image A's code with the callee's same_but_materialized kept as same_io in the post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8Call.v at 888d1ffb4c3 for reac-pw/fuzz_headamp image A: module paths changed, w_intrin_at renamed hd_intrin_at, role's RPgCfgChanges.cfg_segs_low replaced by HPgSteps.img_segs_low over headamp's segments; the two instances hd_memset_at / hd_memcpy_at are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgIntrin.v at 021dba8dbbd; hd_intrin_at renamed cb_intrin_at and stated over image B's segments (lib/AU/Img0U.v rsegs, lib/AU/HPgSteps.v img_segs_low, AR_laws from YG0q.AR_laws_ok), hd_memset_at / hd_memcpy_at renamed cb_memset_at / cb_memcpy_at with the entry pc made a parameter (image B's entries CB_ASAN_MEMSET 0x52228 and CB_ASAN_MEMCPY 0x51d8c stated as constants). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6cKit.v at 80bf14ccf11 (PART 1, a segment's start facts at a cut); rs_ -> cb_, restated over lib/AU/HPgSeg.v (hsu_pre, hsu_core, hsu_E1, hsu_in, hsu_fsh_at) at image B's record headamp_himg_B: the frame for locals of class 4 (1024 bytes, 128 shadow bytes), the 116-byte prologue pattern in place of role's 52, R + 0x220 in place of 0x1a0, image B's three write ranges of hi_w1, the image fact segs_low taken from lib/AU/HPgSteps.v img_segs_low instead of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aBase.v at 80bf14ccf11 (w6_ctx, w6_caller_saved and Section seq only; w6_in as cb_in); w6_ -> cb_, the frame (4, pos) and R + 0x220 of image B, R's cells [R, R + 0x198), and the block post w6_post replaced by the shared layer's hdu_blk_postE (lib/AU/HPgSteps.v), rl_blk_post by hdu_blk_post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6a.v at 80bf14ccf11 (its generic helpers only: the list tactics, the register and location-list lemmas, the geometry of a cut, the image's first write range, the suffix and cursor lemmas, pp's image length, the cut's geometry and context, the core step, the input kept, the block step and the side tactics); w6_ -> cb_, over lib/AU/HPgSeg.v at image B: w6_geo with image B's frame (1024 / 128 bytes, R + 0x220) and the conjuncts F mod 32 = 0 and in_app pp, its head- and tail-specific cell lemmas replaced by write-set-free disjointness lemmas, w6_in_kept and the side tactics generalised over the write set, cb_blkE_step added for a block that writes. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at 80bf14ccf11 (w6h_div, w6h_sh_e, w6h_e_mod8, w6h_bounds, w6h_callee, w6h_val_kept, w6h_chunk0, w6h_region_nth, w6h_chunks); w6h_ -> cb_, the shadow and alignment lemmas generalised over the offset, the bounds at class 4 (1024 bytes, 128 shadow bytes) and e62's 104 bytes at F + 0x210. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at f3898085bda (w7_post,
   w7_post_of_run), RPgW7bKit.v at f3898085bda (w7_kept, w7_hull, w7_ra_kept, w7_hull_kept, w7_strok, w7_strz and
   their lemmas), RPgCfgChanges.v at f3898085bda (kept_run), RPgW6aTail.v at f3898085bda (tl_byte, tl_val_of_chunk,
   tl_val_at), RPgW6aC2h.v at f3898085bda (c2_all256, c2_envz, c2_nz, c2_notin, c2_kio) and RPgW7bIter.v at
   f3898085bda (w7_cs_bv, w7_cs_out, w7_reg_eq), by way of lib/AU/HPgW6bC1k.v's and
   HPgW6bC1.v's hb1_* copies for reac-pw/fuzz_headamp's image B: moved here and renamed cb_* by the dedup, one copy
   kept for the equal helpers of 17 lib/AU files (HPgE0Base, HPgW7bBase, HPgW7bIter, HPgW6aTail, HPgW6aC2 and
   others); cb_val_at_rng is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgCaseB.v; 1254 of its 1360 lines of code are new or changed and 983 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Open.v, RPgW5OpenP.v and RPgW6cKit.v
   (rs_in_now, rs_rom_now) at 164759458cd, in one file; module paths changed, the w5_ / rm_ / rl_ / rs_ prefixes
   renamed to hw5o_ / hm_ / hd_ / hsu_, the code, its registers, the real-frame cells and the constant's address
   walked again on image B of fuzz_headamp (the cursor and what is left of the input in registers, the pod-loop
   cells R+0x80 .. R+0x98 and R+0x128 written, pp, ~pp and pp->len's shadow address read from real-frame cells),
   the cut states read at image B (lib/AU/HPgSeg.v), the segment's write set, frame and shadow pattern of image B's
   record (class-4 frame, hi_w1 of HPgImgB.v), and the AR_laws Section hypothesis replaced by the kernel theorem
   YG0q.AR_laws_ok. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the piece lemma of the
   params Struct's header and its pod count in LLVMFuzzerTestOneInput (0x80c40; pod.h:421-425, fuzz.h:37-43),
   SELS 0x816fc -> C 0x81888 / CL 0x82a18, as lib/AU/HPgSeg.v states it (hw5_piece_open: hsu_piece_W5_open_stmt
   at headamp_himg_B and headamp_bld_B), and its three core walks, one per exit: hw5o_core_nil (no input left, to
   0x82a18 through 0x829d0), hw5o_core_zero (count = fuzz_u8 % 33 = 0, to 0x82a18) and hw5o_core_pos (count <> 0,
   to 0x81888). Proves no function (kind: segment lemma).

   REGISTERS READ: s1 = R (x9), s2 = pp + 0x4000 (x18, the len cell's address), t0 (x5, the property index),
   t1 = -0x4001 (x6, the capacity bound), t2 = the cursor (x7), t3 = what is left of the input (x28), a4 = 1
   (x14, `seen`), s10 = 1 (x26, the cursor test's bound), s11 = K = 0x7fff8000 (x27), sp = R (x2).
   REGISTERS WRITTEN: a0, a1, a2, a3, a5, a6 (x10 .. x16 without a4), s4 := R+0x130 = &e62 (x20), s5 := the cursor
   after the count byte (x21), s10 := what is left after it (x26); a1 := 0 on the exit to C.
   REAL-FRAME CELLS READ: R+0xf0 (~pp), R+0x108 (-0x3ffd), R+0x130 (&e62), R+0x148 (pp), R+0x150 (the shadow
   address of pp + 0x4000). WRITTEN: R+0x80 := a4 (seen = 1), R+0x88 := a6 (at = len at the start), R+0x90 := a5
   (pp + at), R+0x98 := t0, R+0x128 := the count (not on the no-input arm).
   BLOCK BYTES: pp->len at pp + 0x4000 read three times (each with its covered check of R+0x150's shadow byte) and
   written twice (len + 4, len + 8); the eight bytes at pp + at (size word 0, type word 14 = POD_STRUCT, each put
   with its two covered checks of the first and last byte).

   THE CODE
     0x816fc  ld a0,0x150(s1); lbu a0,0(a0); ld s4,0x130(s1); beqz a0 (the check of pp->len)
     0x81710  ld a6,0(s2); a0 := a6 + R+0x108; a5 := R+0x148 + a6 (pp + at); bltu a0,t1 (the capacity test, not
              taken: the condition op_cap1); the UBSan tests `bltu a6,0x4001`, `bgeu ~pp,a6` (decided by ranges)
     0x81744-0x8178c  the checks of a5 and a5 + 3, four `sb zero`, the check of pp->len
     0x81790-0x81818  len += 4; the capacity test again (op_cap2); the UBSan tests; the checks of pp + len and
              pp + len + 3; `sb` of 14, 0, 0, 0; the check of pp->len; len += 4
     0x81820  sd t0,0x98(s1); sd a4,0x80(s1); sd a5,0x90(s1); sd a6,0x88(s1); bnez t3: if 0, 0x81834 `j 0x829d0`,
              0x829d0 `mv s5,t2; li s10,0; j 0x82a18`
     0x81838  s5 := t2 + 1; `bltu s10,s5` (the cursor test of fuzz.h:42, decided by ranges)
     0x81844-0x81854  the check of the 1-byte load at t2: `lb a1,0(sh); beqz a1,+8; j 0x82b44`, with the slow block
              0x82b44 `andi a2,t2,7; bge a2,a1,report; j 0x81858`
     0x81858  lbu a1,0(t2); 0x8185c-0x81860 auipc/ld a2 of the constant 0x07c1f07c1f07c1f1 at 0x10408;
              0x81864-0x81870 mulhu/slli/or/sub: the count = b mod 33; s10 := t3 - 1; sd a1,0x128(s1);
              0x8187c bnez a1: if 0 `j 0x82a18`, else 0x81884 `li a1,0` and 0x81888.
   Every check on pp is covered by the shadow entries (33, 0x4000, 0x4008) and (35, 0, 16) (hw5_shent_blk): pp->len's
   shadow address, loaded from R+0x150, is the engine's own form hw5_sh 33 0x4000.

   THE INPUT READ. As role's: the token path cannot follow the input check (its slow block is reached only by the
   `j`), so the shadow byte s of the cursor is a read-only region at atom 38 (the shadow address SHADOW_OFF +
   cur / 8, named by an f_alias entry), the `lb` is a region load, and the start facts carry the conditions the two
   branches need: s = 0 (the `beqz` is taken) or 0 < s < 8 and cur mod 8 < s (the slow block's `bge` is not
   taken), both from saddr_ok cur s, which range_addressable cur 1 gives (hm_ra_cell, hm_ra_slow_bv). The count's
   `bnez` is decided by the condition b mod 33 = 0 or <> 0 of the exit. The input byte b is a read-only region at
   atom 7 (the cursor register), the constant a base-free region of the image's bytes (HPgSteps.img_region_ok_rom
   from rom_view); the two must be apart, so the case 0x10408 <= cur < 0x10410 (the input inside the constant) is
   walked on its own with the cursor a literal: there b is the constant's byte, which is never 0 mod 33, so the
   zero exit is vacuous there and the other reads b from the constant's region.

   HOW. The cut SELS gives the code's facts (registers, real-frame cells, pp->len from the block's image, and the
   input byte at the cursor with its shadow, carried from the segment's start to the cut by hw5o_in_now and
   hw5o_rom_now); one of the three core walks runs from them (no input left: count 0 -> CL; a count byte c with
   c mod 33 = 0 -> CL; c mod 33 <> 0 -> C with the pod index 0); the end cut is rebuilt from its post: the journal
   and frame part (hw5_core_post), the (location, value) facts, the frame's shadow (kept), the first block's image
   (Model.pc_buf_open: the Struct's size word 0 and its type appended) and the tie of the count to the input
   (Model.prop_step's Struct arm, fuzz_u8). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgW5Kit.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the start states at 0x816fc ========================================
   atoms: 5 = t0, 7 = the cursor, 9 = R, 28 = what is left, 32 = K, 33 = pp, 34 = at (pp->len at the start),
   35 = pp + at, 36 = ~pp, 37 = &e62, 38 = SHADOW_OFF + cur / 8, 39 = b, 40 = s. *)
Definition OP_C1 : Z := 18446744073709535231.  (* (-0x4001) mod 2^64 *)
Definition OP_C2 : Z := 18446744073709535235.  (* (-0x3ffd) mod 2^64 *)
Definition OP_K33 : Z := 558992244657865201.   (* 0x07c1f07c1f07c1f1, the 8 bytes at 0x10408 *)
Definition op_ov : list (bv 5 * sv) :=
  [((2%bv : bv 5), SOff 9 0); ((6%bv : bv 5), SLit OP_C1); ((14%bv : bv 5), SLit 1);
   ((18%bv : bv 5), SOff 33 0x4000); ((26%bv : bv 5), SLit 1); ((27%bv : bv 5), hw5_Bx)].
(* no input left: t3 = 0; the input inside the constant: the cursor is the literal cj *)
Definition op_ov0 : list (bv 5 * sv) := op_ov ++ [((28%bv : bv 5), SLit 0)].
Definition op_ovB (cj : Z) : list (bv 5 * sv) := op_ov ++ [((7%bv : bv 5), SLit cj)].
(* the real frame's cells R+0x80 .. R+0x98 (written), and R+0xf0 .. R+0x150 (read; R+0x128 written when the count
   is computed) *)
Definition op_rlo : YP09.region := YP09.mkRegion (Some 9%nat) 0x80 0xa0 0x80 0xa0 [].
Definition op_rhi (w : bool) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xf0 0x158 (if w then 0x128 else 0) (if w then 0x130 else 0)
   [YP09.mkChunk 0xf0 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x108 (CVal 8 (SLit OP_C2));
    YP09.mkChunk 0x130 (CVal 8 (SOff 37 0)); YP09.mkChunk 0x148 (CVal 8 (SOff 33 0));
    YP09.mkChunk 0x150 (CVal 8 (hw5_sh 33 0x4000))].
Definition op_len : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CVal 8 (SOff 34 0))].
Definition op_at : YP09.region := YP09.mkRegion (Some 35%nat) 0 8 0 8 [].
Definition op_cell : YP09.region := YP09.mkRegion (Some 38%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 40 0))].
Definition op_in : YP09.region := YP09.mkRegion (Some 7%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 39 0))].
Definition op_k : YP09.region := YP09.mkRegion None 0x10408 0x10410 0 0 [YP09.mkChunk 0x10408 (CImg 8)].
(* the input inside the constant (cur = 0x10408 + j): the shadow byte at K + 0x2081 *)
Definition op_cellB : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0x2081 0x2082 0 0 [YP09.mkChunk 0x2081 (CVal 1 (SOff 40 0))].
(* the two capacity tests: len - 0x3ffd >= -0x4001 and len + 4 - 0x3ffd >= -0x4001, unsigned *)
Definition op_cap1 : acond := mkAC BC_GEU (SOff 34 (-16381)) (SLit OP_C1).
Definition op_cap2 : acond := mkAC BC_GEU (SOff 34 (-16377)) (SLit OP_C1).
(* the shadow byte: 0, or the slow block's `bge cur & 7, s` not taken *)
Definition op_slow : acond := mkAC BC_LT (SAlu ALU_AND (SOff 7 0) (SLit 7)) (SOff 40 0).
Definition op_s0 (s0 : bool) : afact := if s0 then mkAF 0 0 0 else mkAF 1 7 0.
Definition op_sc (s0 : bool) : acond := if s0 then mkAC BC_EQ (SOff 40 0) (SLit 0) else op_slow.
Definition op_scB (cj : Z) (s0 : bool) : acond :=
  if s0 then mkAC BC_EQ (SOff 40 0) (SLit 0) else mkAC BC_LT (SLit (cj mod 8)) (SOff 40 0).
(* count = b - ((q << 5) | q), q = mulhu(b, K33), as the engine forms it *)
Definition op_M : sv :=
  SAlu ALU_SUB (SOff 39 0)
    (SAlu ALU_OR (SAlu ALU_SLL (SMd M_MULHU (SOff 39 0) (SLit OP_K33)) (SLit 5)) (SMd M_MULHU (SOff 39 0) (SLit OP_K33))).
Definition op_mz (z : bool) : acond := mkAC (if z then BC_EQ else BC_NE) op_M (SLit 0).
Definition op_atoms0 : list (nat * afact) :=
  [(7%nat, mkAF 1 140737488355328 0); (9%nat, mkAF 70368744177664 140737488355328 5);
   (32%nat, mkAF HW5_SB HW5_SB 0); (33%nat, mkAF 4096 140737488335584 4); (34%nat, mkAF 16 5432 0);
   (35%nat, mkAF 4096 140737488341016 0); (36%nat, mkAF 18446603336221196288 18446744073709547519 0)].
Definition op_atoms1 (s0 : bool) : list (nat * afact) :=
  op_atoms0 ++ [(28%nat, mkAF 1 140737488355328 0); (39%nat, mkAF 0 255 0); (40%nat, op_s0 s0)].
Definition op_atomsB (s0 : bool) : list (nat * afact) :=
  op_atoms0 ++ [(28%nat, mkAF 1 140737488355328 0); (40%nat, op_s0 s0)].
Definition op_alias0 : list (sv * sv) := [(SAlu ALU_ADD (SOff 33 0) (SOff 34 0), SOff 35 0)].
Definition op_alias1 : list (sv * sv) :=
  op_alias0 ++ [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 7 0) (SLit 3)) (SOff 32 0), SOff 38 0)].
Definition ss_op_nil : sstate :=
  mkSS 0x816fc (hw5_sr op_ov0) [op_rlo; op_rhi false; op_len; op_at] None
    (mkFacts op_atoms0 [op_cap1; op_cap2] op_alias0).
Definition ss_op_in (s0 z : bool) : sstate :=
  mkSS 0x816fc (hw5_sr op_ov) [op_rlo; op_rhi true; op_len; op_at; op_cell; op_in; op_k] None
    (mkFacts (op_atoms1 s0) [op_cap1; op_cap2; op_sc s0; op_mz z] op_alias1).
Definition ss_op_rom (cj : Z) (s0 : bool) : sstate :=
  mkSS 0x816fc (hw5_sr (op_ovB cj)) [op_rlo; op_rhi true; op_len; op_at; op_cellB; op_k] None
    (mkFacts (op_atomsB s0) [op_cap1; op_cap2; op_scB cj s0] op_alias0).
Definition op_SH : list shent := [mkSHE 33 0x4000 0x4008; mkSHE 35 0 16].
Definition op_extra0 (pp atv npp fe : Z) : list word := [w64 HW5_SB; w64 pp; w64 atv; w64 (pp + atv); w64 npp; w64 fe].
Definition op_extra1 (pp atv npp fe sa b s : Z) : list word := op_extra0 pp atv npp fe ++ [w64 sa; w64 b; w64 s].
(* the registers a run may change, and the bytes it may write *)
Definition op_clob : list (bv 5) := [10; 11; 12; 13; 15; 16; 20; 21; 26]%bv.
Definition op_E (R pp atv : Z) : Z -> Prop :=
  fun a => (pp + atv <= a < pp + atv + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0x80 <= a < R + 0xa0) \/
           (R + 0x128 <= a < R + 0x130).

(* ======================================== arithmetic ======================================== *)
Lemma op_zc : forall x q r, 0 <= r < 18446744073709551616 -> x = 18446744073709551616 * q + r -> zcanon x = r.
Proof.
intros x q r Hr Hx. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
symmetry. apply (Z.mod_unique_pos x 18446744073709551616 q r Hr Hx).
Qed.
Lemma op_npp : forall pp, 0 <= pp < 18446744073709551615 -> (- pp - 1) mod 2 ^ 64 = 18446744073709551615 - pp.
Proof.
intros pp Hp. change (2 ^ 64) with 18446744073709551616.
symmetry. apply (Z.mod_unique_pos (- pp - 1) 18446744073709551616 (-1)); lia.
Qed.
Lemma op_lit_eq : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact H.
Qed.
Definition op_mod_fn (x : Z) : Z :=
  zcanon (zalu_raw 63 64 ALU_SUB x
    (zcanon (zalu_raw 63 64 ALU_OR
      (zcanon (zalu_raw 63 64 ALU_SLL (zcanon (zmd_raw 64 M_MULHU x (zcanon OP_K33))) (zcanon 5)))
      (zcanon (zmd_raw 64 M_MULHU x (zcanon OP_K33)))))).
Lemma op_mod_fn_ok : forall x, 0 <= x < 256 -> op_mod_fn x = x mod 33.
Proof.
intros x Hx.
assert (H : forallb (fun n => op_mod_fn (Z.of_nat n) =? Z.of_nat n mod 33) (seq 0 256) = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H (Z.to_nat x) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in H by lia. apply Z.eqb_eq. exact H.
Qed.
Lemma op_U_M : forall E b, ew E 39 = Z_to_bv 64 b -> 0 <= b < 256 -> U E op_M = b mod 33.
Proof.
intros E b H39 Hb. unfold op_M. rewrite !U_SAlu, !U_SMd, !U_SLit.
rewrite (U_atom E 39 b H39) by lia. exact (op_mod_fn_ok b Hb).
Qed.
Lemma op_cap_ok : forall E atv c, bv_unsigned (ew E 34) = atv -> 16 <= atv <= 5432 -> -16381 <= c <= -16377 ->
acond_ok E (mkAC BC_GEU (SOff 34 c) (SLit OP_C1)).
Proof.
intros E atv c H34 Ha Hc. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_geu_U, U_SOff, H34, U_SLit.
rewrite (op_zc (atv + c) (-1) (atv + c + 18446744073709551616)) by lia.
rewrite (op_zc OP_C1 0 OP_C1) by (unfold OP_C1; lia).
apply negb_true_iff, Z.ltb_ge. unfold OP_C1. lia.
Qed.
Lemma op_mz_ok : forall E b (z : bool), ew E 39 = Z_to_bv 64 b -> 0 <= b < 256 ->
(if z then b mod 33 = 0 else b mod 33 <> 0) -> acond_ok E (op_mz z).
Proof.
intros E b z H39 Hb Hz. unfold acond_ok, op_mz. destruct z; cbn [ac_c ac_a ac_b].
- change (b mod 33 = 0) in Hz. rewrite branch_eq_U, (op_U_M E b H39 Hb), U_SLit, Hz. reflexivity.
- change (b mod 33 <> 0) in Hz. rewrite branch_ne_U, (op_U_M E b H39 Hb), U_SLit.
  change (zcanon 0) with 0. apply negb_true_iff, Z.eqb_neq. exact Hz.
Qed.
Lemma op_sc_ok : forall E cur s (s0 : bool), ew E 7 = Z_to_bv 64 cur -> ew E 40 = Z_to_bv 64 s ->
0 <= cur < 2 ^ 64 -> saddr_ok cur s -> (if s0 then s = 0 else s <> 0) -> acond_ok E (op_sc s0).
Proof.
intros E cur s s0 H7 H40 Hc Hok Hs. unfold acond_ok. destruct s0; cbn [op_sc ac_c ac_a ac_b].
- change (s = 0) in Hs. subst s. rewrite branch_eq_U, U_SOff, H40, U_SLit. reflexivity.
- change (s <> 0) in Hs. unfold op_slow. cbn [ac_c ac_a ac_b].
  destruct (hm_ra_slow cur s Hok Hs) as [Hs1 Hs2].
  assert (A1 : sv_denot E (SAlu ALU_AND (SOff 7 0) (SLit 7)) = Z_to_bv 64 (cur mod 8)).
  { change (sv_denot E (SAlu ALU_AND (SOff 7 0) (SLit 7))) with
      (alu64 ALU_AND (sv_denot E (SOff 7 0)) (sv_denot E (SLit 7))).
    rewrite (hw5_den_off E 7 cur 0 H7) by lia. rewrite Z.add_0_r. apply alu_and7. unfold M64. lia. }
  rewrite A1, (hw5_den_off E 40 s 0 H40) by lia. rewrite Z.add_0_r.
  exact (hm_ra_slow_bv cur s Hok Hs).
Qed.
Lemma op_scB_ok : forall E cj s (s0 : bool), ew E 40 = Z_to_bv 64 s ->
saddr_ok cj s -> (if s0 then s = 0 else s <> 0) -> acond_ok E (op_scB cj s0).
Proof.
intros E cj s s0 H40 Hok Hs. unfold acond_ok. destruct s0; cbn [op_scB ac_c ac_a ac_b].
- change (s = 0) in Hs. subst s. rewrite branch_eq_U, U_SOff, H40, U_SLit. reflexivity.
- change (s <> 0) in Hs. destruct (hm_ra_slow cj s Hok Hs) as [Hs1 Hs2].
  rewrite (hw5_den_off E 40 s 0 H40) by lia. rewrite Z.add_0_r.
  exact (hm_ra_slow_bv cj s Hok Hs).
Qed.
(* the constant's eight bytes lie in the image's read-only segment *)
Lemma op_in_rom : forall a, 0x10408 <= a < 0x10410 -> in_rom rsegs a.
Proof.
intros a Ha. apply HPgSteps.in_rom_b_ok.
assert (Hi8 : a = 66568 \/ a = 66569 \/ a = 66570 \/ a = 66571 \/ a = 66572 \/ a = 66573 \/ a = 66574 \/ a = 66575)
by lia.
destruct Hi8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma op_img : forall a, 0x10408 <= a < 0x10410 -> in_img rsegs a.
Proof. intros a Ha. destruct (op_in_rom a Ha) as (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.
Lemma op_kbyte_mod : forall i, 0 <= i < 8 -> (Z.shiftr OP_K33 (8 * i) mod 256) mod 33 <> 0.
Proof.
intros i Hi. assert (Hi8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct Hi8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; intro H; discriminate H.
Qed.
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* an input byte inside the constant is the constant's byte *)
Lemma op_rom_byte : forall (W : world rsegs) memc cur b,
rom_view rsegs W memc -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
0x10408 <= cur < 0x10410 -> b = Z.shiftr OP_K33 (8 * (cur - 0x10408)) mod 256.
Proof.
intros W memc cur b HR V Hb Hk.
pose proof (hm_val1_aview rsegs _ _ _ _ V Hb) as A.
pose proof (HR cur (op_in_rom cur Hk)) as Hv. rewrite A in Hv.
assert (Hall : forall i, 0 <= i < 8 ->
  option_map (fun x : byte => bv_unsigned x) (seg_rom rsegs (Z_to_bv 64 (0x10408 + i))) =
  Some (Z.shiftr OP_K33 (8 * i) mod 256)).
{ intros i Hi. assert (Hi8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct Hi8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity. }
specialize (Hall (cur - 0x10408) ltac:(lia)). replace (0x10408 + (cur - 0x10408)) with cur in Hall by lia.
rewrite Hall in Hv. injection Hv as Hv. exact Hv.
Qed.
End r.

(* ======================================== tactics of the posts ======================================== *)
(* the eight bytes pod_put32(0), pod_put32(14) wrote at pp + at, from the end state's one-byte chunks *)
Ltac op_bytes8 E Cat :=
  apply hm_bytes_aview; intros i Hi; rewrite length_app, !length_Z_to_le_bytes in Hi; unfold aview;
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [| | | | | | | | lia];
  lazymatch goal with |- option_map _ (mbyte _ ?m (?base + Z.of_nat ?n)) = Some (bv_unsigned (nth _ ?l _)) =>
    let o := eval cbv in (Z.of_nat n) in
    let v := eval vm_compute in (bv_unsigned (nth n l (Z_to_bv 8 0))) in
    let HB := fresh "HB" in
    assert (HB : mbyte rsegs m (base + o) = Some (Z_to_bv 8 (U E (SLit v))));
    [ apply (hw5_mbyte_chunk1 rsegs E); apply Cat; cbn [In]; repeat (first [left; reflexivity | right]) |];
    change (base + Z.of_nat n) with (base + o); rewrite HB, U_SLit; reflexivity
  end.
(* the write windows of a start state: the real frame's cells on the stack, pp->len and pp + at in pp *)
Ltac op_awr R sp0 pp atv U9 U33 U35 Hpp Hfresh :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
    [ reflexivity | rewrite U9; lia | cbn [r_wlo r_whi]; lia | cbn [r_wlo r_whi]; lia | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat pp);
    [ reflexivity | exact U33
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (hd_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 35%nat (pp + atv));
    [ reflexivity | exact U35
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [r_wlo r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (hd_fresh_awr _ _ _ _ _ _ _ pp 19744); [exact Hpp | exact Hfresh | cbn; lia] | ] ].
(* the post up to its last clause: the cfg, the journal, the registers outside the clobber list, frames, blocks,
   I/O, meter, and every byte outside the start state's write windows *)
Ltac op_post_frame E W memc HJ HR0 U9 U33 U35 MTL :=
  apply SRr_ret; unfold hw5_post;
  lazymatch type of HR0 with regs_ok _ ?sr0 _ =>
  lazymatch goal with HSf : st_ok _ ?Ef ?ssf (restrict _ ?msf) |- _ =>
  do 2 eexists; exists (ms_regs msf), (ms_mem msf); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HSf eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split;
  [ let r := fresh "r" in let Hr0 := fresh "Hr0" in let Hr := fresh "Hr" in intros r Hr0 Hr;
    let HRf := fresh "HRf" in pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _);
    exact (hw5_regs_kept E Ef 41 sr0 (ss_regs ssf) _ (ms_regs msf) op_clob HR0 HRf
             (env_agree_refl 41 E) ltac:(vm_compute; reflexivity) r Hr0 Hr)
  |];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [first [apply same_io_refl | apply hw5_same_io_wvb]|];
  split; [apply mo_le_refl; exact MTL|];
  split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hst := fresh "Hst" in let Hn := fresh "Hn" in
    intros a Ha Hst Hn;
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      apply (hw5_kept_run rsegs E _ (w_H W) memc (ms_mem msf) a HFr Ha) end;
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [r_base r_wlo r_whi base_val] in Hb; rewrite ?U9, ?U33, ?U35 in Hb; apply Hn; unfold op_E; lia | ]);
    destruct Hr
  | ]
  end end.
(* the chunks of the end state's first four regions (the real frame's two, pp->len, pp + at) *)
Ltac op_chunks U9 U33 U35 :=
  lazymatch goal with HSf : st_ok _ _ ?ssf (restrict _ ?msf) |- _ =>
  let HM := fresh "HM" in pose proof HSf as (_ & _ & _ & _ & _ & _ & _ & (_ & HM & _) & _);
  cbn [ss_mem restrict ms_mem] in HM;
  let Rlo := fresh "Rlo" in let Rhi := fresh "Rhi" in let Rln := fresh "Rln" in let Rat := fresh "Rat" in
  apply Forall_cons_iff in HM as [Rlo HM]; apply Forall_cons_iff in HM as [Rhi HM];
  apply Forall_cons_iff in HM as [Rln HM]; apply Forall_cons_iff in HM as [Rat _];
  destruct Rlo as (_ & _ & _ & Clo); destruct Rhi as (_ & _ & _ & Chi);
  destruct Rln as (_ & _ & _ & Cln); destruct Rat as (_ & _ & _ & Cat);
  cbn [r_chunks r_base base_val] in Clo, Chi, Cln, Cat;
  rewrite U9 in Clo, Chi; rewrite U33 in Cln; rewrite U35 in Cat;
  rewrite Forall_forall in Clo, Chi, Cln, Cat;
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _)
  end.
Ltac op_inl := cbn [In]; repeat (first [left; reflexivity | right]).
(* the shared clauses of every post: the eight bytes, pp->len, the four cells R+0x80 .. R+0x98, &e62 in s4 *)
Ltac op_post_common E E5 E34 E37 Cat Cln Clo HRf :=
  split; [op_bytes8 E Cat|];
  split;
  [ apply (val_of_chunk_ok rsegs E _ _ 0x4000 8 (SOff 34 8));
    [ apply Cln; op_inl | rewrite (hw5_den_off E 34 _ 8 E34) by lia; reflexivity
    | change (8 * Z.of_N 8) with 64; lia | lia ] |];
  split;
  [ apply (val_of_chunk_ok rsegs E _ _ 0x80 8 (SLit 1) 1);
    [ apply Clo; op_inl | reflexivity | change (8 * Z.of_N 8) with 64; lia | lia ] |];
  split;
  [ apply (val_of_chunk_ok rsegs E _ _ 0x88 8 (SOff 34 0));
    [ apply Clo; op_inl | rewrite (hw5_den_off E 34 _ 0 E34) by lia; rewrite Z.add_0_r; reflexivity
    | change (8 * Z.of_N 8) with 64; lia | lia ] |];
  split;
  [ lazymatch goal with E35 : ew E 35 = w64 ?v |- _ =>
    apply (val_of_chunk_ok rsegs E _ _ 0x90 8 (SOff 35 0) v);
    [ apply Clo; op_inl | rewrite (hw5_den_off E 35 v 0 E35) by lia; rewrite Z.add_0_r; reflexivity
    | change (8 * Z.of_N 8) with 64; lia | lia ] end |];
  split;
  [ apply (val_of_chunk_ok rsegs E _ _ 0x98 8 (SOff 5 0));
    [ apply Clo; op_inl | rewrite (hw5_den_off E 5 _ 0 E5) by lia; rewrite Z.add_0_r; reflexivity
    | change (8 * Z.of_N 8) with 64; lia | lia ] |];
  split;
  [ transitivity (sv_denot E (SOff 37 0));
    [ exact (HRf 20%bv) | rewrite (hw5_den_off E 37 _ 0 E37) by lia; rewrite Z.add_0_r; reflexivity ] |].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* pp is a block of the harness, apart from the image, so apart from the constant at 0x10408 *)
Lemma op_pp_k : forall ly S W mem md pp, AR rsegs B ly S W mem md -> In (pp, 19744) (ablocks B ly S) ->
pp + 19744 <= 0x10408 \/ 0x10410 <= pp.
Proof.
intros ly S W mem md pp HAR Hin.
destruct (Z_le_gt_dec (pp + 19744) 0x10408) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec 0x10410 pp) as [H'|H']; [right; exact H'|]. exfalso.
apply (blk_img rsegs B (YG0q.AR_laws_ok rsegs B) ly S W mem md pp 19744 (Z.max pp 0x10408) HAR Hin).
- change (req_size 19744) with 19744. lia.
- apply op_img. lia.
Qed.

(* ======================================== (a) no input left ======================================== *)
Lemma hw5o_core_nil : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp atv cur fe t0v : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 5 = w64 t0v -> getr regs 6 = w64 (-0x4001) -> getr regs 7 = w64 cur ->
  getr regs 9 = w64 R -> getr regs 14 = w64 1 -> getr regs 18 = w64 (pp + 0x4000) -> getr regs 26 = w64 1 ->
  getr regs 27 = w64 SHADOW_OFF -> getr regs 28 = w64 0 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 ((- pp - 1) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 fe ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (shadow_addr (pp + 0x4000)) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  R mod 32 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x220 <= sp0 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 < cur <= 2 ^ 47 -> 0 <= fe < 2 ^ 64 -> 0 <= t0v < 2 ^ 64 ->
  SRr rsegs W (cfg_at rsegs 0x816fc regs memc mdc)
    (hw5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x82a18 op_clob (op_E R pp atv)
      (fun W2 regs2 mem2 =>
        hm_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x80) 8 1 /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x88) 8 atv /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x90) 8 (pp + atv) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x98) 8 t0v /\
        getr regs2 20 = w64 fe /\ getr regs2 21 = w64 cur /\ getr regs2 26 = w64 0)).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur fe t0v
  HJ Hpp Hfresh H2 H5 H6 H7 H9 H14 H18 H26 H27 H28 Vf0 V108 V130 V148 V150 Vlen HR32 HRlo HRhi Hat Hal Hcur Hfe Ht0.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof hw5_wx as Hwx. pose proof hw5_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres. rewrite HPS in Hpp, Hfresh. clear Happ.
change (2 ^ 47) with 140737488355328 in H47, Hcur.
replace ((-0x3ffd) mod 2 ^ 64) with OP_C2 in V108 by reflexivity.
rewrite (op_npp pp) in Vf0 by lia. set (npp := 18446744073709551615 - pp) in Vf0.
assert (Hsh8 : 0 <= (pp + 0x4000) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
set (E := Ereg regs (op_extra0 pp atv npp fe)).
assert (E2 : ew E 2 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E5 : ew E 5 = w64 t0v) by (subst E; rewrite (ew_Ereg_nat regs _ 5 5%bv eq_refl); exact H5).
assert (E7 : ew E 7 = w64 cur) by (subst E; rewrite (ew_Ereg_nat regs _ 7 7%bv eq_refl); exact H7).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 HW5_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 atv) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (pp + atv)) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 npp) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = w64 fe) by (subst E; exact (ew_Ereg_extra regs _ 5)).
assert (HE : E = Ereg regs (op_extra0 pp atv npp fe)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs hw5_Bx op_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor; [|constructor]].
  - apply (hw5_shent_blk B lyc Sc W memc mdc pp 19744 E 33 0x4000 0x4008 pp); try assumption;
    try rewrite Hrq'; lia.
  - apply (hw5_shent_blk B lyc Sc W memc mdc pp 19744 E 35 0 16 (pp + atv)); try assumption;
    try rewrite Hrq'; lia. }
assert (U7 : bv_unsigned (ew E 7) = cur) by (rewrite E7; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = HW5_SB) by (rewrite E32; apply unsigned_lit_small; unfold HW5_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = atv) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = pp + atv) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = npp) by (rewrite E36; apply unsigned_lit_small; subst npp; lia).
assert (HR0 : regs_ok E (hw5_sr op_ov0) regs).
{ apply (hw5_regs_ok E regs (op_extra0 pp atv npp fe)); [exact HE|]. unfold op_ov0, op_ov. cbn [app].
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (hw5_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite H6. apply op_lit_eq. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite H14. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (hw5_den_off E 33 pp 0x4000 E33) by lia. rewrite H18. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite H26. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold hw5_Bx. rewrite (hw5_den_off E 32 HW5_SB 0 E32) by (unfold HW5_SB; lia).
    rewrite Z.add_0_r, H27. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite H28. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E (mkFacts op_atoms0 [op_cap1; op_cap2] op_alias0)).
{ split; [| split].
  - cbn [f_atoms op_atoms0 atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U7, U9, U32, U33, U34, U35, U36. subst npp.
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption)
                        | (change (2 ^ 5) with 32; assumption) ].
  - cbn [f_conds conds_ok]. split; [exact (op_cap_ok E atv (-16381) U34 ltac:(lia) ltac:(lia)) |].
    split; [exact (op_cap_ok E atv (-16377) U34 ltac:(lia) ltac:(lia)) | exact I].
  - cbn [f_alias op_alias0 alias_ok]. split; [|exact I].
    rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 33 pp E33), (U_atom E 34 atv E34), (U_atom E 35 (pp + atv) E35) by lia.
    apply zcanon_id. unfold M64. lia. }
assert (HS : st_ok rsegs E ss_op_nil (restrict (w_H W) (mkst regs (Z_to_bv 64 0x816fc) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_op_nil.
  apply (hw5_entry rsegs _ _ regs (op_extra0 pp atv npp fe) E); [exact HE | exact HR0 | vm_compute; reflexivity | | | exact HFK].
  - unfold op_rlo, op_rhi, op_len, op_at.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + apply (hm_rw_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia | intros o Ho; apply Hpres; lia |].
      apply Forall_nil.
    + apply (hm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
      * apply (chunk_ok_val rsegs E _ R 0xf0 8 (SOff 36 0) npp);
          [ rewrite (hw5_den_off E 36 npp 0 E36) by (subst npp; lia); rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; subst npp; lia | lia | exact Vf0 ].
      * apply (chunk_ok_val rsegs E _ R 0x108 8 (SLit OP_C2) OP_C2);
          [ reflexivity | unfold OP_C2; change (8 * Z.of_N 8) with 64; lia | lia | exact V108 ].
      * apply (chunk_ok_val rsegs E _ R 0x130 8 (SOff 37 0) fe);
          [ rewrite (hw5_den_off E 37 fe 0 E37) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V130 ].
      * apply (chunk_ok_val rsegs E _ R 0x148 8 (SOff 33 0) pp);
          [ rewrite (hw5_den_off E 33 pp 0 E33) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V148 ].
      * apply (chunk_ok_val rsegs E _ R 0x150 8 (hw5_sh 33 0x4000) (shadow_addr (pp + 0x4000)));
          [ rewrite (hw5_den_sh E 33 pp 0x4000 E33 E32) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; unfold shadow_addr, SHADOW_OFF; lia | lia | exact V150 ].
    + apply (hm_rw_region rsegs E (w_H W) memc 33 pp);
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 34 0) atv);
        [ rewrite (hw5_den_off E 34 atv 0 E34) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
    + apply (hm_rw_region rsegs E (w_H W) memc 35 (pp + atv));
        [ exact U35 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + atv + o) ltac:(lia))) | apply Forall_nil ].
  - unfold op_rlo, op_rhi, op_len, op_at. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [r_base r_lo r_hi base_val]. rewrite U9, U33, U35. repeat split; try exact I; lia. }
unfold cfg_at. change (w64 0x816fc) with (Z_to_bv 64 0x816fc).
aj_run_to_tok hw5_tbl_ok HS HJ Hsh hw5_Bspan 0x82a18.
all: try (op_awr R sp0 pp atv U9 U33 U35 Hpp Hfresh).
all: op_post_frame E W memc HJ HR0 U9 U33 U35 MTL.
all: op_chunks U9 U33 U35.
all: op_post_common E E5 E34 E37 Cat Cln Clo HRf.
all: split;
  [ transitivity (sv_denot E (SOff 7 0));
    [ exact (HRf 21%bv) | rewrite (hw5_den_off E 7 cur 0 E7) by lia; rewrite Z.add_0_r; reflexivity ] |].
all: transitivity (sv_denot E (SLit 0)); [ exact (HRf 26%bv) | reflexivity ].
Qed.

(* ===================== (b), (c) with the input outside the constant: one lemma, z the count's case ===================== *)
Lemma op_core_app : forall (z : bool) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp atv cur nl fe t0v : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 5 = w64 t0v -> getr regs 6 = w64 (-0x4001) -> getr regs 7 = w64 cur ->
  getr regs 9 = w64 R -> getr regs 14 = w64 1 -> getr regs 18 = w64 (pp + 0x4000) -> getr regs 26 = w64 1 ->
  getr regs 27 = w64 SHADOW_OFF -> getr regs 28 = w64 nl ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 ((- pp - 1) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 fe ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (shadow_addr (pp + 0x4000)) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  rom_view rsegs W memc ->
  R mod 32 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x220 <= sp0 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 < cur <= 2 ^ 47 -> 0 <= fe < 2 ^ 64 -> 0 <= t0v < 2 ^ 64 ->
  0 < nl <= 2 ^ 47 ->
  ~ (pp <= cur < pp + Layout.PP_SIZE) -> ~ (R <= cur < R + 0x198) ->
  amem_range cur 1 -> ~ (0x10408 <= cur < 0x10410) ->
  forall b, val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 ->
  (if z then b mod 33 = 0 else b mod 33 <> 0) ->
  SRr rsegs W (cfg_at rsegs 0x816fc regs memc mdc)
    (hw5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if z then 0x82a18 else 0x81888)
      op_clob (op_E R pp atv)
      (fun W2 regs2 mem2 =>
        hm_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x80) 8 1 /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x88) 8 atv /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x90) 8 (pp + atv) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x98) 8 t0v /\
        getr regs2 20 = w64 fe /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x128) 8 (b mod 33) /\
        getr regs2 21 = w64 (cur + 1) /\ getr regs2 26 = w64 (nl - 1) /\ (z = false -> getr regs2 11 = w64 0))).
Proof using MTL.
intros z STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl fe t0v
  HJ Hpp Hfresh H2 H5 H6 H7 H9 H14 H18 H26 H27 H28 Vf0 V108 V130 V148 V150 Vlen Hrom HR32 HRlo HRhi Hat Hal Hcur
  Hfe Ht0 Hnl Hc1 Hc2 Hamem Hrk b Vb Hb Hra Hz.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof hw5_wx as Hwx. pose proof hw5_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres, Happ. rewrite HPS in Hpp, Hfresh, Hc1.
change (2 ^ 47) with 140737488355328 in H47, Hcur, Hnl.
replace ((-0x3ffd) mod 2 ^ 64) with OP_C2 in V108 by reflexivity.
rewrite (op_npp pp) in Vf0 by lia. set (npp := 18446744073709551615 - pp) in Vf0.
assert (Hsh8 : 0 <= (pp + 0x4000) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
destruct (hm_ra_cell _ _ _ Hra) as (s & Hs & Hok).
assert (Hs0e : exists s0 : bool, if s0 then s = 0 else s <> 0)
by (destruct (Z.eq_dec s 0); [exists true | exists false]; assumption).
destruct Hs0e as (s0 & Hs0).
assert (Hs8 : 0 <= s < 8).
{ destruct s0; [change (s = 0) in Hs0; lia | change (s <> 0) in Hs0; destruct (hm_ra_slow cur s Hok Hs0); lia]. }
pose proof (Z.mod_pos_bound b 33 ltac:(lia)) as Hb33.
assert (Hcur' : cur < 140737488355328)
  by (clear - Hamem C3 C4 C5; unfold amem_range in Hamem; rewrite C3, C4, C5 in Hamem; lia).
assert (Hdiv : 0 <= cur / 8 < 17592186044416)
by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
set (E := Ereg regs (op_extra1 pp atv npp fe (shadow_of_addr SHADOW_OFF cur) b s)).
assert (E2 : ew E 2 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E5 : ew E 5 = w64 t0v) by (subst E; rewrite (ew_Ereg_nat regs _ 5 5%bv eq_refl); exact H5).
assert (E7 : ew E 7 = w64 cur) by (subst E; rewrite (ew_Ereg_nat regs _ 7 7%bv eq_refl); exact H7).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E28 : ew E 28 = w64 nl) by (subst E; rewrite (ew_Ereg_nat regs _ 28 28%bv eq_refl); exact H28).
assert (E32 : ew E 32 = Z_to_bv 64 HW5_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 atv) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (pp + atv)) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 npp) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = w64 fe) by (subst E; exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = w64 (shadow_of_addr SHADOW_OFF cur)) by (subst E; exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = w64 b) by (subst E; exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = w64 s) by (subst E; exact (ew_Ereg_extra regs _ 8)).
assert (HE : E = Ereg regs (op_extra1 pp atv npp fe (shadow_of_addr SHADOW_OFF cur) b s)) by reflexivity. clearbody E.
set (sa := shadow_of_addr SHADOW_OFF cur) in *.
assert (Hsa : HW5_SB <= sa < HW5_SB + 17592186044416) by (subst sa; unfold shadow_of_addr, HW5_SB, SHADOW_OFF; lia).
assert (HshA : sa = shadow_of_addr SHADOW_OFF cur) by reflexivity. clearbody sa.
assert (Hsh : sh_ok rsegs hw5_Bx op_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor; [|constructor]].
  - apply (hw5_shent_blk B lyc Sc W memc mdc pp 19744 E 33 0x4000 0x4008 pp); try assumption;
    try rewrite Hrq'; lia.
  - apply (hw5_shent_blk B lyc Sc W memc mdc pp 19744 E 35 0 16 (pp + atv)); try assumption;
    try rewrite Hrq'; lia. }
assert (U7 : bv_unsigned (ew E 7) = cur) by (rewrite E7; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U28 : bv_unsigned (ew E 28) = nl) by (rewrite E28; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = HW5_SB) by (rewrite E32; apply unsigned_lit_small; unfold HW5_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = atv) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = pp + atv) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = npp) by (rewrite E36; apply unsigned_lit_small; subst npp; lia).
assert (U38 : bv_unsigned (ew E 38) = sa) by (rewrite E38; apply unsigned_lit_small; unfold HW5_SB in Hsa; lia).
assert (U39 : bv_unsigned (ew E 39) = b) by (rewrite E39; apply unsigned_lit_small; lia).
assert (U40 : bv_unsigned (ew E 40) = s) by (rewrite E40; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (hw5_sr op_ov) regs).
{ apply (hw5_regs_ok E regs (op_extra1 pp atv npp fe sa b s)); [exact HE|]. unfold op_ov.
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (hw5_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite H6. apply op_lit_eq. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite H14. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (hw5_den_off E 33 pp 0x4000 E33) by lia. rewrite H18. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite H26. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold hw5_Bx. rewrite (hw5_den_off E 32 HW5_SB 0 E32) by (unfold HW5_SB; lia).
    rewrite Z.add_0_r, H27. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E (mkFacts (op_atoms1 s0) [op_cap1; op_cap2; op_sc s0; op_mz z] op_alias1)).
{ split; [| split].
  - unfold op_atoms1. cbn [f_atoms op_atoms0 app atoms_ok]. unfold afact_ok.
    destruct s0; [change (s = 0) in Hs0 | change (s <> 0) in Hs0]; cbn [op_s0 af_lo af_hi af_al2];
    rewrite U7, U9, U28, U32, U33, U34, U35, U36, U39, U40; subst npp;
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption)
                        | (change (2 ^ 5) with 32; assumption) ].
  - cbn [f_conds conds_ok]. split; [exact (op_cap_ok E atv (-16381) U34 ltac:(lia) ltac:(lia)) |].
    split; [exact (op_cap_ok E atv (-16377) U34 ltac:(lia) ltac:(lia)) |].
    split; [exact (op_sc_ok E cur s s0 E7 E40 ltac:(lia) Hok Hs0) |].
    split; [exact (op_mz_ok E b z E39 Hb Hz) | exact I].
  - cbn [f_alias op_alias1 op_alias0 app alias_ok]. split; [| split; [| exact I]].
    + rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 33 pp E33), (U_atom E 34 atv E34), (U_atom E 35 (pp + atv) E35) by lia.
      apply zcanon_id. unfold M64. lia.
    + apply (shadow_decl_ok E 7 32 38 cur HW5_SB E7 ltac:(lia) E32).
      rewrite E38, HshA. reflexivity. }
assert (HS : st_ok rsegs E (ss_op_in s0 z) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x816fc) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_op_in.
  apply (hw5_entry rsegs _ _ regs (op_extra1 pp atv npp fe sa b s) E);
    [exact HE | exact HR0 | vm_compute; reflexivity | | | exact HFK].
  - unfold op_rlo, op_rhi, op_len, op_at, op_cell, op_in, op_k.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]]].
    + apply (hm_rw_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia | intros o Ho; apply Hpres; lia |].
      apply Forall_nil.
    + apply (hm_rw_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia | intros o Ho; apply Hpres; lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
      * apply (chunk_ok_val rsegs E _ R 0xf0 8 (SOff 36 0) npp);
          [ rewrite (hw5_den_off E 36 npp 0 E36) by (subst npp; lia); rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; subst npp; lia | lia | exact Vf0 ].
      * apply (chunk_ok_val rsegs E _ R 0x108 8 (SLit OP_C2) OP_C2);
          [ reflexivity | unfold OP_C2; change (8 * Z.of_N 8) with 64; lia | lia | exact V108 ].
      * apply (chunk_ok_val rsegs E _ R 0x130 8 (SOff 37 0) fe);
          [ rewrite (hw5_den_off E 37 fe 0 E37) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V130 ].
      * apply (chunk_ok_val rsegs E _ R 0x148 8 (SOff 33 0) pp);
          [ rewrite (hw5_den_off E 33 pp 0 E33) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V148 ].
      * apply (chunk_ok_val rsegs E _ R 0x150 8 (hw5_sh 33 0x4000) (shadow_addr (pp + 0x4000)));
          [ rewrite (hw5_den_sh E 33 pp 0x4000 E33 E32) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; unfold shadow_addr, SHADOW_OFF; lia | lia | exact V150 ].
    + apply (hm_rw_region rsegs E (w_H W) memc 33 pp);
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 34 0) atv);
        [ rewrite (hw5_den_off E 34 atv 0 E34) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
    + apply (hm_rw_region rsegs E (w_H W) memc 35 (pp + atv));
        [ exact U35 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + atv + o) ltac:(lia))) | apply Forall_nil ].
    + apply (hm_cell_region rsegs E (w_H W) memc 38 sa s (SOff 40 0) U38 Hs);
        [ rewrite (hw5_den_off E 40 s 0 E40) by lia; rewrite Z.add_0_r; reflexivity
        | unfold HW5_SB in Hsa; lia | unfold HW5_SB in Hsa; lia ].
    + apply (hm_cell_region rsegs E (w_H W) memc 7 cur b (SOff 39 0) U7 (hm_val1_aview rsegs _ _ _ _ Vb Hb));
        [ rewrite (hw5_den_off E 39 b 0 E39) by lia; rewrite Z.add_0_r; reflexivity | lia | lia ].
    + apply (HPgSteps.img_region_ok_rom E W memc 0x10408 8); [exact Hrom | lia | lia | lia | vm_compute; reflexivity].
  - assert (Fpp_sa : pp + 19744 <= sa \/ sa + 1 <= pp).
    { clear - Happ Hsa C3. unfold in_app in Happ. rewrite C3 in Happ. unfold kLowShadowBeg in Happ.
      unfold HW5_SB in Hsa. lia. }
    assert (Fcur_sa : cur + 1 <= sa \/ sa + 1 <= cur).
    { clear - Hamem Hsa C3 C5. unfold amem_range in Hamem. rewrite C3, C5 in Hamem. unfold HW5_SB in Hsa. lia. }
    assert (Fpp_k : pp + 19744 <= 0x10408 \/ 0x10410 <= pp) by exact (op_pp_k lyc Sc W memc mdc pp HAR Hpp).
    clear Happ Hamem Hz Hs0 Hok.
    unfold op_rlo, op_rhi, op_len, op_at, op_cell, op_in, op_k. cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U7, U9, U33, U35, U38.
    unfold HW5_SB in *. repeat split; try exact I; lia. }
destruct s0, z.
all: unfold cfg_at; change (w64 0x816fc) with (Z_to_bv 64 0x816fc).
all: [> aj_run_to_tok hw5_tbl_ok HS HJ Hsh hw5_Bspan 0x82a18 | aj_run_to_tok hw5_tbl_ok HS HJ Hsh hw5_Bspan 0x81888
 | aj_run_to_tok hw5_tbl_ok HS HJ Hsh hw5_Bspan 0x82a18 | aj_run_to_tok hw5_tbl_ok HS HJ Hsh hw5_Bspan 0x81888 ].
all: try (op_awr R sp0 pp atv U9 U33 U35 Hpp Hfresh).
all: op_post_frame E W memc HJ HR0 U9 U33 U35 MTL.
all: op_chunks U9 U33 U35.
all: op_post_common E E5 E34 E37 Cat Cln Clo HRf.
all: split;
  [ apply (val_of_chunk_ok rsegs E _ R 0x128 8 op_M (b mod 33));
    [ apply Chi; op_inl | rewrite denot_lit_U, (op_U_M E b E39 Hb); reflexivity
    | change (8 * Z.of_N 8) with 64; lia | lia ] |].
all: split;
  [ transitivity (sv_denot E (SOff 7 1));
    [ exact (HRf 21%bv) | rewrite (hw5_den_off E 7 cur 1 E7) by lia; reflexivity ] |].
all: split;
  [ transitivity (sv_denot E (SOff 28 (-1)));
    [ exact (HRf 26%bv) | rewrite (hw5_den_off E 28 nl (-1) E28) by lia; unfold w64; f_equal; lia ] |].
all: intros Hzf; first [ discriminate Hzf | transitivity (sv_denot E (SLit 0)); [exact (HRf 11%bv) | reflexivity] ].
Qed.

(* ===================== (c) with the input inside the constant: cur = 0x10408 + j, eight literal walks ===================== *)
Lemma op_core_rom : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp atv cur nl fe t0v : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 5 = w64 t0v -> getr regs 6 = w64 (-0x4001) -> getr regs 7 = w64 cur ->
  getr regs 9 = w64 R -> getr regs 14 = w64 1 -> getr regs 18 = w64 (pp + 0x4000) -> getr regs 26 = w64 1 ->
  getr regs 27 = w64 SHADOW_OFF -> getr regs 28 = w64 nl ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 ((- pp - 1) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 fe ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (shadow_addr (pp + 0x4000)) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  rom_view rsegs W memc ->
  R mod 32 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x220 <= sp0 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 <= fe < 2 ^ 64 -> 0 <= t0v < 2 ^ 64 ->
  0 < nl <= 2 ^ 47 -> 0x10408 <= cur < 0x10410 ->
  forall b, val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 ->
  SRr rsegs W (cfg_at rsegs 0x816fc regs memc mdc)
    (hw5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x81888 op_clob (op_E R pp atv)
      (fun W2 regs2 mem2 =>
        hm_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x80) 8 1 /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x88) 8 atv /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x90) 8 (pp + atv) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x98) 8 t0v /\
        getr regs2 20 = w64 fe /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x128) 8 (b mod 33) /\
        getr regs2 21 = w64 (cur + 1) /\ getr regs2 26 = w64 (nl - 1) /\ getr regs2 11 = w64 0)).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl fe t0v
  HJ Hpp Hfresh H2 H5 H6 H7 H9 H14 H18 H26 H27 H28 Vf0 V108 V130 V148 V150 Vlen Hrom HR32 HRlo HRhi Hat Hal
  Hfe Ht0 Hnl Hkin b Vb Hb Hra.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof hw5_wx as Hwx. pose proof hw5_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp Layout.PP_SIZE HAR Hpp) as (Hp16 & Hp4096 & Hpceil & Happ & Hppres & _).
rewrite Hrq, HPS in Hpceil, Hppres, Happ. rewrite HPS in Hpp, Hfresh.
change (2 ^ 47) with 140737488355328 in H47, Hnl.
replace ((-0x3ffd) mod 2 ^ 64) with OP_C2 in V108 by reflexivity.
rewrite (op_npp pp) in Vf0 by lia. set (npp := 18446744073709551615 - pp) in Vf0.
assert (Hsh8 : 0 <= (pp + 0x4000) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (op_rom_byte W memc cur b Hrom Vb Hb Hkin) as Hbv.
destruct (hm_ra_cell _ _ _ Hra) as (s & Hs & Hok).
assert (Hs0e : exists s0 : bool, if s0 then s = 0 else s <> 0)
by (destruct (Z.eq_dec s 0); [exists true | exists false]; assumption).
destruct Hs0e as (s0 & Hs0).
assert (Hs8 : 0 <= s < 8).
{ destruct s0; [change (s = 0) in Hs0; lia | change (s <> 0) in Hs0; destruct (hm_ra_slow cur s Hok Hs0); lia]. }
pose proof (Z.mod_pos_bound b 33 ltac:(lia)) as Hb33.
assert (Hc8 : cur / 8 = 8321) by (symmetry; apply (Z.div_unique cur 8 8321 (cur - 66568)); [left; lia | lia]).
assert (HsaB : shadow_of_addr SHADOW_OFF cur = HW5_SB + 0x2081) by (unfold shadow_of_addr; rewrite Hc8; reflexivity).
rewrite HsaB in Hs.
set (E := Ereg regs (op_extra1 pp atv npp fe 0 b s)).
assert (E2 : ew E 2 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E5 : ew E 5 = w64 t0v) by (subst E; rewrite (ew_Ereg_nat regs _ 5 5%bv eq_refl); exact H5).
assert (E7 : ew E 7 = w64 cur) by (subst E; rewrite (ew_Ereg_nat regs _ 7 7%bv eq_refl); exact H7).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E28 : ew E 28 = w64 nl) by (subst E; rewrite (ew_Ereg_nat regs _ 28 28%bv eq_refl); exact H28).
assert (E32 : ew E 32 = Z_to_bv 64 HW5_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 atv) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (pp + atv)) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 npp) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = w64 fe) by (subst E; exact (ew_Ereg_extra regs _ 5)).
assert (E40 : ew E 40 = w64 s) by (subst E; exact (ew_Ereg_extra regs _ 8)).
assert (HE : E = Ereg regs (op_extra1 pp atv npp fe 0 b s)) by reflexivity. clearbody E.
assert (Hsh : sh_ok rsegs hw5_Bx op_SH E (mrestrict (w_H W) memc)).
{ assert (Hrq' : req_size 19744 = 19744) by reflexivity.
  constructor; [|constructor; [|constructor]].
  - apply (hw5_shent_blk B lyc Sc W memc mdc pp 19744 E 33 0x4000 0x4008 pp); try assumption;
    try rewrite Hrq'; lia.
  - apply (hw5_shent_blk B lyc Sc W memc mdc pp 19744 E 35 0 16 (pp + atv)); try assumption;
    try rewrite Hrq'; lia. }
assert (U7 : bv_unsigned (ew E 7) = cur) by (rewrite E7; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U28 : bv_unsigned (ew E 28) = nl) by (rewrite E28; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = HW5_SB) by (rewrite E32; apply unsigned_lit_small; unfold HW5_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = atv) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = pp + atv) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = npp) by (rewrite E36; apply unsigned_lit_small; subst npp; lia).
assert (U40 : bv_unsigned (ew E 40) = s) by (rewrite E40; apply unsigned_lit_small; lia).
assert (HR0 : regs_ok E (hw5_sr (op_ovB cur)) regs).
{ apply (hw5_regs_ok E regs (op_extra1 pp atv npp fe 0 b s)); [exact HE|]. unfold op_ovB, op_ov. cbn [app].
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (hw5_den_off E 9 R 0 E9) by lia. rewrite Z.add_0_r, H2. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite H6. apply op_lit_eq. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite H14. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite (hw5_den_off E 33 pp 0x4000 E33) by lia. rewrite H18. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite H26. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. unfold hw5_Bx. rewrite (hw5_den_off E 32 HW5_SB 0 E32) by (unfold HW5_SB; lia).
    rewrite Z.add_0_r, H27. reflexivity. }
  apply Forall_cons; [split; [apply hw5_nz; vm_compute; lia|] |].
  { cbn [fst snd]. rewrite H7. reflexivity. }
  apply Forall_nil. }
assert (HFK : facts_ok E (mkFacts (op_atomsB s0) [op_cap1; op_cap2; op_scB cur s0] op_alias0)).
{ split; [| split].
  - unfold op_atomsB. cbn [f_atoms op_atoms0 app atoms_ok]. unfold afact_ok.
    destruct s0; [change (s = 0) in Hs0 | change (s <> 0) in Hs0]; cbn [op_s0 af_lo af_hi af_al2];
    rewrite U7, U9, U28, U32, U33, U34, U35, U36, U40; subst npp;
    repeat split; first [ lia | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) | (change (2 ^ 4) with 16; assumption)
                        | (change (2 ^ 5) with 32; assumption) ].
  - cbn [f_conds conds_ok]. split; [exact (op_cap_ok E atv (-16381) U34 ltac:(lia) ltac:(lia)) |].
    split; [exact (op_cap_ok E atv (-16377) U34 ltac:(lia) ltac:(lia)) |].
    split; [exact (op_scB_ok E cur s s0 E40 Hok Hs0) | exact I].
  - cbn [f_alias op_alias0 alias_ok]. split; [|exact I].
    rewrite !denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 33 pp E33), (U_atom E 34 atv E34), (U_atom E 35 (pp + atv) E35) by lia.
    apply zcanon_id. unfold M64. lia. }
assert (HS : st_ok rsegs E (ss_op_rom cur s0) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x816fc) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_op_rom.
  apply (hw5_entry rsegs _ _ regs (op_extra1 pp atv npp fe 0 b s) E);
    [exact HE | exact HR0 | vm_compute; reflexivity | | | exact HFK].
  - unfold op_rlo, op_rhi, op_len, op_at, op_cellB, op_k.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]].
    + apply (hm_rw_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia | intros o Ho; apply Hpres; lia |].
      apply Forall_nil.
    + apply (hm_rw_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia | intros o Ho; apply Hpres; lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
      * apply (chunk_ok_val rsegs E _ R 0xf0 8 (SOff 36 0) npp);
          [ rewrite (hw5_den_off E 36 npp 0 E36) by (subst npp; lia); rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; subst npp; lia | lia | exact Vf0 ].
      * apply (chunk_ok_val rsegs E _ R 0x108 8 (SLit OP_C2) OP_C2);
          [ reflexivity | unfold OP_C2; change (8 * Z.of_N 8) with 64; lia | lia | exact V108 ].
      * apply (chunk_ok_val rsegs E _ R 0x130 8 (SOff 37 0) fe);
          [ rewrite (hw5_den_off E 37 fe 0 E37) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V130 ].
      * apply (chunk_ok_val rsegs E _ R 0x148 8 (SOff 33 0) pp);
          [ rewrite (hw5_den_off E 33 pp 0 E33) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V148 ].
      * apply (chunk_ok_val rsegs E _ R 0x150 8 (hw5_sh 33 0x4000) (shadow_addr (pp + 0x4000)));
          [ rewrite (hw5_den_sh E 33 pp 0x4000 E33 E32) by lia; reflexivity
          | change (8 * Z.of_N 8) with 64; unfold shadow_addr, SHADOW_OFF; lia | lia | exact V150 ].
    + apply (hm_rw_region rsegs E (w_H W) memc 33 pp);
        [ exact U33 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + o) ltac:(lia))) | ].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 34 0) atv);
        [ rewrite (hw5_den_off E 34 atv 0 E34) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact Vlen ].
    + apply (hm_rw_region rsegs E (w_H W) memc 35 (pp + atv));
        [ exact U35 | lia | lia | intros o Ho; exact (proj1 (Hppres (pp + atv + o) ltac:(lia))) | apply Forall_nil ].
    + apply (hm_ro_region rsegs E (w_H W) memc 32 HW5_SB 0x2081 0x2082); [exact U32 | unfold HW5_SB; lia | unfold HW5_SB; lia |].
      apply Forall_cons; [|apply Forall_nil].
      destruct (hm_aview_val1 rsegs _ _ _ _ Hs) as [Vs _].
      apply (chunk_ok_val rsegs E _ HW5_SB 0x2081 1 (SOff 40 0) s);
        [ rewrite (hw5_den_off E 40 s 0 E40) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | lia | exact Vs ].
    + apply (HPgSteps.img_region_ok_rom E W memc 0x10408 8); [exact Hrom | lia | lia | lia | vm_compute; reflexivity].
  - assert (Fpp_sa : pp + 19744 <= HW5_SB + 0x2081 \/ HW5_SB + 0x2082 <= pp).
    { clear - Happ C3. unfold in_app in Happ. rewrite C3 in Happ. unfold kLowShadowBeg in Happ. unfold HW5_SB. lia. }
    assert (Fpp_k : pp + 19744 <= 0x10408 \/ 0x10410 <= pp) by exact (op_pp_k lyc Sc W memc mdc pp HAR Hpp).
    clear Happ Hs0 Hok.
    unfold op_rlo, op_rhi, op_len, op_at, op_cellB, op_k. cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite U9, U32, U33, U35.
    unfold HW5_SB in *. repeat split; try exact I; lia. }
assert (Hcj : cur = 66568 \/ cur = 66569 \/ cur = 66570 \/ cur = 66571 \/ cur = 66572 \/ cur = 66573 \/
              cur = 66574 \/ cur = 66575) by lia.
destruct Hcj as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; destruct s0.
all: unfold cfg_at; change (w64 0x816fc) with (Z_to_bv 64 0x816fc).
all: aj_run_to_tok hw5_tbl_ok HS HJ Hsh hw5_Bspan 0x81888.
all: try (op_awr R sp0 pp atv U9 U33 U35 Hpp Hfresh).
all: op_post_frame E W memc HJ HR0 U9 U33 U35 MTL.
all: op_chunks U9 U33 U35.
all: op_post_common E E5 E34 E37 Cat Cln Clo HRf.
all: split;
  [ lazymatch type of Chi with context [YP09.mkChunk 0x128 (CVal 8 ?e)] =>
      apply (val_of_chunk_ok rsegs E _ R 0x128 8 e (b mod 33));
      [ apply Chi; op_inl | rewrite Hbv; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia ] end |].
all: split; [ etransitivity; [exact (HRf 21%bv) | reflexivity] |].
all: split;
  [ transitivity (sv_denot E (SOff 28 (-1)));
    [ exact (HRf 26%bv) | rewrite (hw5_den_off E 28 nl (-1) E28) by lia; unfold w64; f_equal; lia ] |].
all: etransitivity; [exact (HRf 11%bv) | reflexivity].
Qed.

(* ======================================== (b) count = 0 ======================================== *)
Lemma hw5o_core_zero : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp atv cur nl fe t0v : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 5 = w64 t0v -> getr regs 6 = w64 (-0x4001) -> getr regs 7 = w64 cur ->
  getr regs 9 = w64 R -> getr regs 14 = w64 1 -> getr regs 18 = w64 (pp + 0x4000) -> getr regs 26 = w64 1 ->
  getr regs 27 = w64 SHADOW_OFF -> getr regs 28 = w64 nl ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 ((- pp - 1) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 fe ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (shadow_addr (pp + 0x4000)) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  rom_view rsegs W memc ->
  R mod 32 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x220 <= sp0 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 < cur <= 2 ^ 47 -> 0 <= fe < 2 ^ 64 -> 0 <= t0v < 2 ^ 64 ->
  0 < nl <= 2 ^ 47 ->
  ~ (pp <= cur < pp + Layout.PP_SIZE) -> ~ (R <= cur < R + 0x198) -> amem_range cur 1 ->
  forall b, val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 -> b mod 33 = 0 ->
  SRr rsegs W (cfg_at rsegs 0x816fc regs memc mdc)
    (hw5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x82a18 op_clob (op_E R pp atv)
      (fun W2 regs2 mem2 =>
        hm_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x80) 8 1 /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x88) 8 atv /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x90) 8 (pp + atv) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x98) 8 t0v /\
        getr regs2 20 = w64 fe /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x128) 8 0 /\
        getr regs2 21 = w64 (cur + 1) /\ getr regs2 26 = w64 (nl - 1))).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl fe t0v
  HJ Hpp Hfresh H2 H5 H6 H7 H9 H14 H18 H26 H27 H28 Vf0 V108 V130 V148 V150 Vlen Hrom HR32 HRlo HRhi Hat Hal Hcur
  Hfe Ht0 Hnl Hc1 Hc2 Hamem b Vb Hb Hra Hm.
destruct (Z_lt_le_dec cur 0x10408) as [Hlo|Hlo]; [|destruct (Z_lt_le_dec cur 0x10410) as [Hhi|Hhi]].
2: { exfalso. apply (op_kbyte_mod (cur - 0x10408) ltac:(lia)).
     rewrite <- (op_rom_byte W memc cur b Hrom Vb Hb ltac:(lia)). exact Hm. }
all: eapply SRr_mono;
  [ exact (op_core_app true STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl fe t0v
      HJ Hpp Hfresh H2 H5 H6 H7 H9 H14 H18 H26 H27 H28 Vf0 V108 V130 V148 V150 Vlen Hrom HR32 HRlo HRhi Hat Hal
      Hcur Hfe Ht0 Hnl Hc1 Hc2 Hamem ltac:(lia) b Vb Hb Hra Hm) |].
all: intros W' c' _ (ly2 & S2 & regs2 & mem2 & md2 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & (R1 & R2 & R3 & R4 & R5 &
  R6 & R7 & R8 & R9 & R10 & _)).
all: exists ly2, S2, regs2, mem2, md2; rewrite Hm in R8.
all: exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8
       (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj R8 (conj R9 R10))))))))))))))))).
Qed.

(* ======================================== (c) count <> 0 ======================================== *)
Lemma hw5o_core_pos : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp atv cur nl fe t0v : Z),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
  getr regs 2 = w64 R -> getr regs 5 = w64 t0v -> getr regs 6 = w64 (-0x4001) -> getr regs 7 = w64 cur ->
  getr regs 9 = w64 R -> getr regs 14 = w64 1 -> getr regs 18 = w64 (pp + 0x4000) -> getr regs 26 = w64 1 ->
  getr regs 27 = w64 SHADOW_OFF -> getr regs 28 = w64 nl ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 ((- pp - 1) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 ((-0x3ffd) mod 2 ^ 64) ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 fe ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (shadow_addr (pp + 0x4000)) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 atv ->
  rom_view rsegs W memc ->
  R mod 32 = 0 -> sp0 - STK <= R - T_SEG_STK -> R + 0x220 <= sp0 ->
  16 <= atv -> atv + 8 <= 5440 -> 0 < cur <= 2 ^ 47 -> 0 <= fe < 2 ^ 64 -> 0 <= t0v < 2 ^ 64 ->
  0 < nl <= 2 ^ 47 ->
  ~ (pp <= cur < pp + Layout.PP_SIZE) -> ~ (R <= cur < R + 0x198) -> amem_range cur 1 ->
  forall b, val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 -> b mod 33 <> 0 ->
  SRr rsegs W (cfg_at rsegs 0x816fc regs memc mdc)
    (hw5_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x81888 op_clob (op_E R pp atv)
      (fun W2 regs2 mem2 =>
        hm_bytes rsegs (w_H W2) mem2 (pp + atv) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (atv + 8) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x80) 8 1 /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x88) 8 atv /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x90) 8 (pp + atv) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x98) 8 t0v /\
        getr regs2 20 = w64 fe /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x128) 8 (b mod 33) /\
        getr regs2 21 = w64 (cur + 1) /\ getr regs2 26 = w64 (nl - 1) /\ getr regs2 11 = w64 0)).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl fe t0v
  HJ Hpp Hfresh H2 H5 H6 H7 H9 H14 H18 H26 H27 H28 Vf0 V108 V130 V148 V150 Vlen Hrom HR32 HRlo HRhi Hat Hal Hcur
  Hfe Ht0 Hnl Hc1 Hc2 Hamem b Vb Hb Hra Hm.
destruct (Z_lt_le_dec cur 0x10408) as [Hlo|Hlo]; [|destruct (Z_lt_le_dec cur 0x10410) as [Hhi|Hhi]].
2: { exact (op_core_rom STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl fe t0v
       HJ Hpp Hfresh H2 H5 H6 H7 H9 H14 H18 H26 H27 H28 Vf0 V108 V130 V148 V150 Vlen Hrom HR32 HRlo HRhi Hat Hal
       Hfe Ht0 Hnl ltac:(lia) b Vb Hb Hra). }
all: eapply SRr_mono;
  [ exact (op_core_app false STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp atv cur nl fe t0v
      HJ Hpp Hfresh H2 H5 H6 H7 H9 H14 H18 H26 H27 H28 Vf0 V108 V130 V148 V150 Vlen Hrom HR32 HRlo HRhi Hat Hal
      Hcur Hfe Ht0 Hnl Hc1 Hc2 Hamem ltac:(lia) b Vb Hb Hra Hm) |].
all: intros W' c' _ (ly2 & S2 & regs2 & mem2 & md2 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & (R1 & R2 & R3 & R4 & R5 &
  R6 & R7 & R8 & R9 & R10 & R11)).
all: exists ly2, S2, regs2, mem2, md2.
all: exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8
       (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj R8 (conj R9 (conj R10 (R11 eq_refl))))))))))))))))))).
Qed.
End c.

(* ======================================================================================================
   THE PIECE: the cut SELS read, one core walk run, the end cut rebuilt
   ====================================================================================================== *)
Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ---- the model at the Struct's header ---- *)
(* the Struct's size word (0 until the close) and its type *)
Definition hw5o_shdr : list byte := le32 0 ++ le32 POD_STRUCT.
Lemma hw5o_img_open_eq : forall sh ps,
pc_image (PbCut sh ps (Some [])) =
pp_image ((pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) ++ hw5o_shdr)
  (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
  (pc_ents (PbCut sh ps None)) false.
Proof.
intros sh ps. unfold pc_image. cbn [pc_shape pc_props pc_open].
rewrite <- pc_buf_open. unfold hw5o_shdr. rewrite <- !app_assoc.
unfold pc_ents. cbn [pc_props pc_open]. destruct (first_params ps) as [[]|]; reflexivity.
Qed.
Lemma hw5o_skipn_cons : forall (l : list byte) j x t, skipn j l = x :: t ->
(j < length l)%nat /\ nth j l (Z_to_bv 8 0) = x /\ skipn (S j) l = t.
Proof.
intros l j. revert l. induction j as [|j IH]; intros [|y l] x t H; cbn in H; try discriminate.
- injection H as -> ->. cbn. split; [lia | split; reflexivity].
- destruct (IH l x t H) as (H1 & H2 & H3). cbn. split; [lia | split; assumption].
Qed.
Lemma hw5o_tie_open : forall sh ps sel rest r c r',
(sel, r) = fuzz_u8 (snd (props_loop sh (length ps) (hsu_r0 rest))) ->
sel mod 4 <> 0 -> Z.testbit sel 4 = false -> (c, r') = fuzz_u8 r -> hsu_pod_tie sh ps (c mod 33) [] rest r'.
Proof.
intros sh ps sel rest r c r' H1 H2 H3 H4. exists sel, c, r, r'.
split; [exact H1|]. split; [exact H4|]. split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. reflexivity.
Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* ===================================== a segment's start facts at a cut ===================================== *)
(* what a cut may have changed since the segment's start: outside [0, 2^64), the callees' stack, hsu_E1 *)
Definition hw5o_wr (cx : hsu_scx rsegs) (a : Z) : Prop :=
(a < 0 \/ 2 ^ 64 <= a) \/ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) \/ hsu_E1 rsegs headamp_himg_B cx a.

Lemma hw5o_core_kept : forall cx sh ly2 S2 W2 regs2 mem2 md2,
hsu_pre rsegs B headamp_himg_B cx sh ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 ->
forall a, ~ hw5o_wr cx a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a.
Proof.
intros cx sh ly2 S2 W2 regs2 mem2 md2 HP HC a Ha.
pose proof (hw5_pre_facts B cx sh HP) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hsp : spZ (x_regs cx) = e_R (x_e cx)).
{ unfold spZ. rewrite RB4. unfold w64. apply unsigned_lit_small. unfold T_SEG_STK, ASTACK in *. lia. }
destruct HC as (_ & _ & _ & _ & _ & _ & HK). unfold hw5o_wr in Ha.
apply HK; [lia | rewrite Hsp; intros X; apply Ha; right; left; exact X | intros X; apply Ha; right; right; exact X].
Qed.

(* a shadow byte of an application address is never in hsu_E1 or the callees' stack *)
Lemma hw5o_wr_shadow : forall cx x, hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) ->
0 <= x < kHighMemEnd ->
range_addressable (aview rsegs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF x 1 ->
~ hw5o_wr cx (shadow_of_addr SHADOW_OFF x).
Proof.
intros cx x HP Hx Hra.
pose proof (hw5_pre_facts B cx _ HP) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp & FApp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (hm_shadow_band x Hx) as Hb.
assert (Hfsh : hd_fsh rsegs (w_H (x_W cx)) (x_memc cx) (e_F (x_e cx)) (hi_shA headamp_himg_B)).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
pose proof (hm_ra_not_fsh rsegs _ _ _ _ x 1 Hra Hfsh hmu_sh_P0_big x ltac:(lia)) as Hnf.
change (Z.of_nat (length (hi_shA headamp_himg_B))) with 116 in Hnf.
unfold hw5o_wr, hsu_E1, hd_inw. cbn [hi_w1 headamp_himg_B].
intros [H|[H|[H|H]]].
- unfold kLowMemEnd, kHighMemBeg in Hb. lia.
- unfold kHighMemBeg in Hb. unfold T_SEG_STK, ASTACK in *. lia.
- apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_nil in H; destruct H]]];
  cbn [fst snd hd_xv] in H.
  + apply (hm_shadow_not_app x (e_F (x_e cx)) 1024 Hx FApp). lia.
  + apply Hnf. lia.
  + unfold kHighMemBeg in Hb. unfold T_SEG_STK, ASTACK in *. lia.
- apply (hm_shadow_not_app x (e_pp (x_e cx)) Layout.PP_SIZE Hx PApp). exact H.
Qed.

Lemma hw5o_in_now : forall cx rest ly2 S2 W2 regs2 mem2 md2,
hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) -> hsu_in rsegs headamp_himg_B cx rest ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 ->
hm_bytes rsegs (w_H W2) mem2 (e_src (x_e cx)) rest /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (e_src (x_e cx)) (e_left (x_e cx)).
Proof.
intros cx rest ly2 S2 W2 regs2 mem2 md2 HP HI HC.
pose proof (hw5o_core_kept cx _ ly2 S2 W2 regs2 mem2 md2 HP HC) as HK.
destruct HI as (Hleft & Hbytes & Hra & Hhull & Hamr & Hsrc0 & Hsrc63 & Hdisj).
set (src := e_src (x_e cx)) in *. set (n := e_left (x_e cx)) in *.
assert (Hx : forall x, src <= x < src + n -> 0 <= x < kHighMemEnd).
{ intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
split.
- apply (hm_bytes_kept_wr rsegs (hw5o_wr cx) _ _ _ _ src rest Hbytes HK).
  intros x Hx'. rewrite <- Hleft in Hx'. fold n in Hx'. destruct (Hdisj x Hx') as (D1 & D2 & D3).
  unfold hw5o_wr, hsu_E1. intros [H|[H|[H|H]]]; [lia | exact (D1 H) | exact (D2 H) | exact (D3 H)].
- apply (hm_ra_kept_wr rsegs (hw5o_wr cx) _ _ _ _ SHADOW_OFF src n Hra HK).
  intros x Hx'. apply hw5o_wr_shadow; [exact HP | exact (Hx x Hx') |].
  apply (range_addressable_sub _ _ src n); [exact Hra | lia | lia].
Qed.

(* rom_view at a cut: the image lies below the shadow band, outside every block and frame *)
Lemma hw5o_rom_now : forall cx sh ly2 S2 W2 regs2 mem2 md2,
hsu_pre rsegs B headamp_himg_B cx sh ->
hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 -> rom_view rsegs W2 mem2.
Proof.
intros cx sh ly2 S2 W2 regs2 mem2 md2 HP HC.
pose proof (hw5o_core_kept cx sh ly2 S2 W2 regs2 mem2 md2 HP HC) as HK.
pose proof (hw5_pre_facts B cx sh HP) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp & FApp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hrom : rom_view rsegs (x_W cx) (x_memc cx)).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
assert (HAR : AR rsegs B (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx)).
{ destruct HP as (HJ & _). exact (proj1 HJ). }
assert (HF : e_F (x_e cx) = frame_addr (x_lyc cx) 4 (x_pos cx)).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
assert (Hin4 : In (4, x_pos cx) (frames (x_Sc cx))).
{ destruct HP as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & _).
  pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. apply in_or_app. left. exact Hown. }
apply (hm_rom_kept_wr rsegs (hw5o_wr cx) (x_W cx) W2 (x_memc cx) mem2 Hrom HK).
intros a (sg & Hsg & _ & Ha). assert (Himg : in_img rsegs a) by (exists sg; split; [exact Hsg | exact Ha]).
pose proof (hw5_segs_low a Himg) as Hlow.
pose proof (al_client_img _ _ (YG0q.AR_laws_ok rsegs B) _ _ _ _ _ a HAR) as Hcl.
unfold hw5o_wr, hsu_E1, hd_inw. cbn [hi_w1 headamp_himg_B].
intros [H|[H|[H|H]]].
- unfold kLowMemEnd in Hlow. lia.
- unfold kLowMemEnd, T_SEG_STK, ASTACK in *. lia.
- apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_cons in H as [H|H]; [|apply Exists_nil in H; destruct H]]];
  cbn [fst snd hd_xv] in H.
  + assert (HinF : frame_addr (x_lyc cx) 4 (x_pos cx) <= a < frame_addr (x_lyc cx) 4 (x_pos cx) + fs_frame_bytes 4)
      by (rewrite <- HF; change (fs_frame_bytes 4) with 1024; lia).
    apply (proj2 (Hcl (or_intror (or_introl (ex_intro _ 4 (ex_intro _ (x_pos cx) (conj Hin4 HinF))))))).
    exact Himg.
  + unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. pose proof (Z.div_pos (e_F (x_e cx)) 8). lia.
  + unfold kLowMemEnd, T_SEG_STK, ASTACK in *. lia.
- assert (Hinp : e_pp (x_e cx) <= a < e_pp (x_e cx) + req_size Layout.PP_SIZE)
    by (change (req_size Layout.PP_SIZE) with Layout.PP_SIZE; lia).
  apply (proj2 (Hcl (or_introl (ex_intro _ (e_pp (x_e cx)) (ex_intro _ Layout.PP_SIZE (conj Ppin Hinp)))))).
  exact Himg.
Qed.

(* ===================================== the end of the three runs ===================================== *)
(* shared: the frame's shadow kept, the image with the Struct's header *)
Lemma hw5o_after : forall cx rest sh np sel ps r ly2 S2 W2 regs2 mem2 md2 W3 ly3 S3 regs3 mem3 md3,
  hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) ->
  hsu_cut_SELS rsegs B MT headamp_himg_B cx sh np sel ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly3 S3 W3 regs3 mem3 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) ->
     ~ op_E (e_R (x_e cx)) (e_pp (x_e cx)) (hsu_at_of sh ps) a ->
     aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx) + hsu_at_of sh ps) (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 14) ->
  val_mem rsegs (mrestrict (w_H W3) mem3) (e_pp (x_e cx) + 0x4000) 8 (hsu_at_of sh ps + 8) ->
  hsu_fsh_at rsegs cx W3 mem3 (hsu_P0 headamp_himg_B) /\ hsu_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps (Some []))).
Proof.
intros cx rest sh np sel ps r ly2 S2 W2 regs2 mem2 md2 W3 ly3 S3 regs3 mem3 md3 Hpre Hcut Hcore3 Hmem Rb Rl.
pose proof (hw5_pre_facts B cx _ Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp & FApp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity. assert (HPS : PP_SIZE = 19744) by reflexivity.
destruct Hcut as (Hb & Hat & Hpp & Hsh7 & Hsel & Hsel4 & Hselb & Hselr).
destruct Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hlen1 & Hps & Hsh & Hnp & Hpsnp & Hnp3).
pose proof Hwf as (_ & Hk & He & _).
assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ X]; exact X).
destruct (pc_buf_len_none sh ps Hv He) as [Hblen _].
assert (Hat16 : 16 <= hsu_at_of sh ps)
  by (unfold hsu_at_of; pose proof (hw5_plen_lo sh ps Hsh7); unfold hsu_plen in *; lia).
assert (H5440 : hsu_at_of sh ps + 16 <= 5440) by (unfold hsu_at_of, hsu_plen; lia).
(* every byte the run did not write *)
assert (Kp : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) ->
  ~ (e_pp (x_e cx) + hsu_at_of sh ps <= a < e_pp (x_e cx) + hsu_at_of sh ps + 8) ->
  ~ (e_pp (x_e cx) + 0x4000 <= a < e_pp (x_e cx) + 0x4008) ->
  ~ (e_R (x_e cx) + 0x80 <= a < e_R (x_e cx) + 0xa0) -> ~ (e_R (x_e cx) + 0x128 <= a < e_R (x_e cx) + 0x130) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3 H4 H5. apply Hmem; [exact Ha | exact H1 |]. unfold op_E. intros [X|[X|[X|X]]]; auto. }
split.
- unfold hsu_fsh_at in *. eapply hm_fsh_kept; [exact Hfsh|]. intros j Hj.
  change (length (hsu_P0 headamp_himg_B)) with 116%nat in Hj.
  pose proof (Z.mul_div_le (e_F (x_e cx)) 8 ltac:(lia)) as D1.
  pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)) as D2.
  unfold shadow_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in PApp.
  unfold T_SEG_STK, ASTACK in *. apply Kp; lia.
- pose proof (hw5_ents_bounds sh ps None Hwf I) as (EB1 & EB2).
  assert (Hb0 : Z.of_nat (length (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0)) = hsu_at_of sh ps).
  { rewrite !length_app, !length_le32. unfold hsu_at_of, hsu_plen. lia. }
  assert (Old : hm_bytes rsegs (w_H W2) mem2 (e_pp (x_e cx))
    (pp_image (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) (is_props (PodRec sh ps None))
      (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false))
    by exact Hpp.
  unfold hsu_pp_at.
  change (hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx)) (pc_image (PbCut sh ps (Some [])))).
  rewrite (hw5o_img_open_eq sh ps).
  set (LA := length_app (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) hw5o_shdr).
  assert (LS : length hw5o_shdr = 8%nat) by reflexivity.
  assert (Nb : hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e cx))
      ((pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) ++ hw5o_shdr)).
  { apply hm_bytes_app. split.
    - eapply hm_bytes_kept; [exact (hw5_img_buf _ _ _ _ _ _ _ _ _ Old)|]. intros y Hy. rewrite Hb0 in Hy.
      unfold T_SEG_STK, ASTACK in *. apply Kp; lia.
    - rewrite Hb0. exact Rb. }
  apply (hw5_img_gen (w_H W2) mem2 (w_H W3) mem3 (e_pp (x_e cx))
    (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) _ _
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))); try exact Old; try exact Nb.
  + rewrite LA. lia.
  + rewrite LA, Nat2Z.inj_add, Hb0, LS. unfold POD_BUF_MAX. lia.
  + exact EB1.
  + exact EB2.
  + rewrite LA, Nat2Z.inj_add, Hb0, LS. exact Rl.
  + refine (proj1 (hw5_img_flags _ _ _ _ _ _ _ _ _ _ _ _ EB1 EB2 Old _)); [unfold POD_BUF_MAX; lia|].
    intros y Hy. unfold OFF_HAS_PARAMS, OFF_ENT in Hy. unfold T_SEG_STK, ASTACK in *. apply Kp; lia.
  + refine (proj2 (hw5_img_flags _ _ _ _ _ _ _ _ _ _ _ _ EB1 EB2 Old _)); [unfold POD_BUF_MAX; lia|].
    intros y Hy. unfold OFF_HAS_PARAMS, OFF_ENT in Hy. unfold T_SEG_STK, ASTACK in *. apply Kp; lia.
  + intros y Hy. rewrite LA, Nat2Z.inj_add, Hb0, LS in Hy.
    unfold OFF_LEN, OFF_IS_PROPS, OFF_HAS_PARAMS, OFF_ENT, PP_SIZE in Hy.
    unfold T_SEG_STK, ASTACK in *. apply Kp; lia.
Qed.

(* ===================================== the piece ===================================== *)
Lemma hw5_piece_open : hsu_piece_W5_open_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof using MTL.
unfold hsu_piece_W5_open_stmt. intros cx POST rest i Hst HC HCL.
destruct Hst as (Hpre & Hc1 & Hlen0 & Hin0).
pose proof (hw5_pre_facts B cx _ Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & Ppin & Ppout & PB1 & PB2 & FB1 & FB2 & PApp & FApp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_SEG_STK = 16384) by reflexivity. assert (HPS : PP_SIZE = 19744) by reflexivity.
unfold hsu_from_SELS. intros ly2 S2 W2 regs2 mem2 md2 sh np sel ps r Hlen Hcut.
pose proof Hcut as Hcut0.
destruct Hcut as (Hb & Hat & Hpp & Hsh7 & Hsel & Hsel4 & Hselb & Hselr).
pose proof Hb as (Hcore & Hfsh & Hin & Hsuf & Hwf & Hlen1 & Hps & Hsh & Hnp & Hpsnp & Hnp3).
unfold hsu_at_cx in Hat. unfold hsu_L_KEY in Hat.
assert (E4 : (sel mod 4 =? 0) = false) by (apply Z.eqb_neq; exact Hsel4).
rewrite E4 in Hat. cbv beta iota in Hat.
pose proof Hcore as (HJ & Hr234 & _ & Hperm & _).
(* ---- the facts the core walks take ---- *)
assert (A2 : getr regs2 2 = w64 (e_R (x_e cx))).
{ rewrite <- (hw5_getr5 regs2 2%bv 2 eq_refl). rewrite (Hr234 2 (or_introl eq_refl)).
  rewrite (hw5_getr5 (x_regs cx) 2%bv 2 eq_refl). exact RB4. }
pose proof (hw5_at_reg _ _ _ _ _ 5 (Z.of_nat (length ps)) Hat ltac:(hw5_in)) as A5.
pose proof (hw5_at_reg _ _ _ _ _ 6 (-0x4001) Hat ltac:(hw5_in)) as A6.
pose proof (hw5_at_reg _ _ _ _ _ 7 (hsu_cur rsegs cx rest r) Hat ltac:(hw5_in)) as A7.
pose proof (hw5_at_reg _ _ _ _ _ 9 (e_R (x_e cx)) Hat ltac:(hw5_in)) as A9.
pose proof (hw5_at_reg _ _ _ _ _ 14 1 Hat ltac:(hw5_in)) as A14.
pose proof (hw5_at_reg _ _ _ _ _ 18 (e_pp (x_e cx) + Layout.OFF_LEN) Hat ltac:(hw5_in)) as A18.
pose proof (hw5_at_reg _ _ _ _ _ 26 1 Hat ltac:(hw5_in)) as A26.
pose proof (hw5_at_reg _ _ _ _ _ 27 SHADOW_OFF Hat ltac:(hw5_in)) as A27.
pose proof (hw5_at_reg _ _ _ _ _ 28 (Z.of_nat (length r)) Hat ltac:(hw5_in)) as A28.
pose proof (hw5_at_cell _ _ _ _ _ 0xf0 (- e_pp (x_e cx) - 1) Hat ltac:(hw5_in)) as Vf0.
pose proof (hw5_at_cell _ _ _ _ _ 0x108 (-0x3ffd) Hat ltac:(hw5_in)) as V108.
pose proof (hw5_at_cell _ _ _ _ _ 0x130 (e_F (x_e cx) + HSU_E62) Hat ltac:(hw5_in)) as V130.
pose proof (hw5_at_cell _ _ _ _ _ 0x148 (e_pp (x_e cx)) Hat ltac:(hw5_in)) as V148.
pose proof (hw5_at_cell _ _ _ _ _ 0x150 (shadow_addr (e_pp (x_e cx) + Layout.OFF_LEN)) Hat ltac:(hw5_in)) as V150.
change Layout.OFF_LEN with 0x4000 in A18, V150.
pose proof Hwf as (_ & Hk & He & _).
assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ X]; exact X).
destruct (pc_buf_len_none sh ps Hv He) as [Hblen _].
assert (Hps2 : (length ps <= 2)%nat) by lia.
assert (Hat16 : 16 <= hsu_at_of sh ps)
  by (unfold hsu_at_of; pose proof (hw5_plen_lo sh ps Hsh7); unfold hsu_plen in *; lia).
assert (H5440 : hsu_at_of sh ps + 8 <= 5440) by (unfold hsu_at_of, hsu_plen; lia).
assert (Hdiv : 0 <= (e_pp (x_e cx) + 0x4000) / 8 < 2 ^ 60)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite Z.mod_small in V130 by (unfold HSU_E62; lia).
rewrite Z.mod_small in V148 by lia.
rewrite Z.mod_small in V150 by (unfold shadow_addr, SHADOW_OFF; lia).
(* the input: what is left of it, its byte at the cursor and the shadow, at the cut *)
pose proof Hin as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & Hdisj).
destruct (hw5o_in_now cx rest ly2 S2 W2 regs2 mem2 md2 Hpre Hin Hcore) as (Ibytes & Ira).
pose proof (hw5o_rom_now cx _ ly2 S2 W2 regs2 mem2 md2 Hpre Hcore) as Hrom.
destruct Hsuf as (j & Hj & Hr).
assert (Hcurv : hsu_cur rsegs cx rest r = e_src (x_e cx) + Z.of_nat j)
  by (unfold hsu_cur; rewrite Hr, length_skipn; lia).
assert (Hnl : Z.of_nat (length r) = Z.of_nat (length rest) - Z.of_nat j) by (rewrite Hr, length_skipn; lia).
pose proof (hw5_ents_bounds sh ps None Hwf I) as (EB1 & EB2).
assert (Hb0 : Z.of_nat (length (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0)) = hsu_at_of sh ps).
{ rewrite !length_app, !length_le32. unfold hsu_at_of, hsu_plen. lia. }
assert (Old : hm_bytes rsegs (w_H W2) mem2 (e_pp (x_e cx))
  (pp_image (pc_buf (PbCut sh ps None) ++ le32 POD_PROP_PARAMS ++ le32 0) (is_props (PodRec sh ps None))
    (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps None)) false))
  by exact Hpp.
assert (Vlen : val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e cx) + 0x4000) 8 (hsu_at_of sh ps)).
{ rewrite <- Hb0. refine (hm_pp_len rsegs _ _ _ _ _ _ _ EB1 EB2 _ _ _ Old). unfold POD_BUF_MAX; lia. }
assert (Ppin2 : In (e_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Ppin).
assert (Hsp : spZ regs2 = e_R (x_e cx)) by (unfold spZ; rewrite A2; apply unsigned_lit_small; unfold T_SEG_STK, ASTACK in *; lia).
assert (HinR : forall a, e_src (x_e cx) <= a < e_src (x_e cx) + e_left (x_e cx) ->
  ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE) /\ ~ (e_R (x_e cx) <= a < e_R (x_e cx) + 0x198)).
{ intros a Ha. destruct (Hdisj a Ha) as (D1 & D2 & D3). split; [exact D3|].
  intros X. apply D2. unfold hd_inw. cbn [hi_w1 headamp_himg_B].
  apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd hd_xv]. lia. }
(* the registers and cells every exit keeps *)
assert (Hclob : forall r0, (r0 = 2 \/ r0 = 3 \/ r0 = 4) -> ~ In (Z_to_bv 5 r0) op_clob).
{ unfold op_clob. intros r0 [-> | [-> | ->]]; hw5_notin. }
assert (HEp : forall a, op_E (e_R (x_e cx)) (e_pp (x_e cx)) (hsu_at_of sh ps) a -> hsu_E1 rsegs headamp_himg_B cx a).
{ intros a Ha. unfold op_E in Ha. destruct Ha as [Ha|[Ha|Ha]]; [right; lia | right; lia |].
  left. unfold hd_inw. cbn [hi_w1 headamp_himg_B].
  apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd hd_xv]. lia. }
destruct r as [|x t].
- (* no input left: the count is 0, CL *)
  assert (Hcur0 : 0 < hsu_cur rsegs cx rest [] <= 2 ^ 47)
    by (rewrite Hcurv; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; cbn [length] in Hnl; lia).
  eapply SRr_bind.
  { change (cfg_at rsegs (bi_SELS headamp_bld_B) regs2 mem2 md2) with (cfg_at rsegs 0x816fc regs2 mem2 md2).
    refine (hw5o_core_nil B MT MTL (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
      (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (e_R (x_e cx)) (e_pp (x_e cx)) (hsu_at_of sh ps)
      (hsu_cur rsegs cx rest []) (e_F (x_e cx) + HSU_E62) (Z.of_nat (length ps)) HJ Ppin2 Ppout A2 A5 A6 A7 A9 A14 A18
      A26 A27 A28 Vf0 V108 V130 V148 V150 Vlen RB3 RB1 RB2 Hat16 ltac:(lia) Hcur0 ltac:(unfold HSU_E62; lia)
      ltac:(lia)). }
  intros W3 c3 Hle Hpost.
  destruct (hw5_core_post B MT MTL cx (hsu_E1 rsegs headamp_himg_B cx) _ ly2 S2 W2 regs2 mem2 md2 0x82a18 _ _ W3 c3
    Hcore HEp Hclob Hpost) as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem &
    (Rb & Rl & R80 & R88 & R90 & R98 & R20 & R21 & R26)).
  rewrite Hsp in Hmem. unfold op_clob in Hkeep.
  destruct (hw5o_after cx rest sh np sel ps [] ly2 S2 W2 regs2 mem2 md2 W3 ly3 S3 regs3 mem3 md3
    Hpre Hcut0 Hcore3 Hmem Rb Rl) as (Hfsh3 & Hpp3).
  assert (Kc : forall a, e_R (x_e cx) <= a < e_R (x_e cx) + 0x80 \/ e_R (x_e cx) + 0xa0 <= a < e_R (x_e cx) + 0x128 \/
      e_R (x_e cx) + 0x130 <= a < e_R (x_e cx) + 0x158 ->
    aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha. apply Hmem; [unfold T_SEG_STK, ASTACK in *; lia | lia | unfold op_E; unfold T_SEG_STK, ASTACK in *; lia]. }
  change (cfg_at rsegs 0x82a18 regs3 mem3 md3) with (cfg_at rsegs (bi_CL headamp_bld_B) regs3 mem3 md3).
  apply (HCL ly3 S3 W3 regs3 mem3 md3 sh np ps 0 [] [] Hlen).
  split; [exact Hcore3|]. split.
  { unfold hsu_at_cx, hsu_at. cbn [hsu_Rc0 hsu_Kc app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: first [ hw5_kept Hat Hkeep Kc
               | (cbn [hd_at hd_xv]; rewrite (Z.mod_small _ (2 ^ 64)) by lia; first [exact R80 | exact R88 | exact R90 | exact R98])
               | (cbn [hd_at hd_xv]; exact R21)
               | (cbn [hd_at hd_xv length Z.of_nat]; exact R26) ]. }
  split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exists j; split; [exact Hj | exact Hr]|].
  split; [exact Hwf|]. split; [exact Hlen1|]. split; [exact Hps|].
  split; [exact (hw5o_tie_open sh ps sel rest [] 0 [] Hselr Hsel4 Hselb eq_refl)|].
  split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hpsnp|]. split; [exact Hnp3|]. split; [exact Hsh7|].
  split; [exact Hps2|]. split; [lia|]. split; [constructor | reflexivity].
- (* a count byte b at the cursor *)
  destruct (hw5o_skipn_cons rest j x t (eq_sym Hr)) as (Hjl & Hnth & Ht).
  assert (Vb : val_mem rsegs (mrestrict (w_H W2) mem2) (hsu_cur rsegs cx rest (x :: t)) 1 (bv_unsigned x)).
  { rewrite Hcurv, <- Hnth. exact (hm_bytes_byte rsegs (w_H W2) mem2 (e_src (x_e cx)) rest j Ibytes Hjl). }
  assert (Vbr : 0 <= bv_unsigned x < 256) by (pose proof (bv_unsigned_in_range 8 x) as X; exact X).
  assert (Rab : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (hsu_cur rsegs cx rest (x :: t)) 1).
  { apply (range_addressable_sub _ _ (e_src (x_e cx)) (e_left (x_e cx))); [exact Ira | lia | lia]. }
  assert (Hamc : amem_range (hsu_cur rsegs cx rest (x :: t)) 1)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  assert (Hcur0 : 0 < hsu_cur rsegs cx rest (x :: t) <= 2 ^ 47)
    by (rewrite Hcurv; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
  assert (Hnl0 : 0 < Z.of_nat (length (x :: t)) <= 2 ^ 47)
    by (rewrite Hnl; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
  destruct (HinR (hsu_cur rsegs cx rest (x :: t)) ltac:(lia)) as [Hc1' Hc2'].
  assert (Ht' : hsu_suffix rest t) by (exists (S j); split; [lia | symmetry; exact Ht]).
  assert (Hcur1 : hsu_cur rsegs cx rest t = hsu_cur rsegs cx rest (x :: t) + 1)
    by (unfold hsu_cur; cbn [length]; lia).
  assert (Hnl1 : Z.of_nat (length t) = Z.of_nat (length (x :: t)) - 1) by (cbn [length]; lia).
  destruct (Z.eqb_spec (bv_unsigned x mod 33) 0) as [Ez|Ez].
  + (* the count is 0: CL *)
    eapply SRr_bind.
    { change (cfg_at rsegs (bi_SELS headamp_bld_B) regs2 mem2 md2) with (cfg_at rsegs 0x816fc regs2 mem2 md2).
      refine (hw5o_core_zero B MT MTL (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
        (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (e_R (x_e cx)) (e_pp (x_e cx)) (hsu_at_of sh ps)
        (hsu_cur rsegs cx rest (x :: t)) (Z.of_nat (length (x :: t))) (e_F (x_e cx) + HSU_E62) (Z.of_nat (length ps))
        HJ Ppin2 Ppout A2 A5 A6 A7 A9 A14 A18 A26 A27 A28 Vf0 V108 V130 V148 V150 Vlen Hrom RB3 RB1 RB2 Hat16
        ltac:(lia) Hcur0 ltac:(unfold HSU_E62; lia) ltac:(lia) Hnl0 Hc1' Hc2' Hamc (bv_unsigned x) Vb Vbr Rab Ez). }
    intros W3 c3 Hle Hpost.
    destruct (hw5_core_post B MT MTL cx (hsu_E1 rsegs headamp_himg_B cx) _ ly2 S2 W2 regs2 mem2 md2 0x82a18 _ _ W3 c3
      Hcore HEp Hclob Hpost) as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem &
      (Rb & Rl & R80 & R88 & R90 & R98 & R20 & R128 & R21 & R26)).
    rewrite Hsp in Hmem. unfold op_clob in Hkeep.
    destruct (hw5o_after cx rest sh np sel ps (x :: t) ly2 S2 W2 regs2 mem2 md2 W3 ly3 S3 regs3 mem3 md3
      Hpre Hcut0 Hcore3 Hmem Rb Rl) as (Hfsh3 & Hpp3).
    assert (Kc : forall a, e_R (x_e cx) <= a < e_R (x_e cx) + 0x80 \/ e_R (x_e cx) + 0xa0 <= a < e_R (x_e cx) + 0x128 \/
        e_R (x_e cx) + 0x130 <= a < e_R (x_e cx) + 0x158 ->
      aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
    { intros a Ha. apply Hmem; [unfold T_SEG_STK, ASTACK in *; lia | lia | unfold op_E; unfold T_SEG_STK, ASTACK in *; lia]. }
    change (cfg_at rsegs 0x82a18 regs3 mem3 md3) with (cfg_at rsegs (bi_CL headamp_bld_B) regs3 mem3 md3).
    apply (HCL ly3 S3 W3 regs3 mem3 md3 sh np ps 0 [] t Hlen).
    split; [exact Hcore3|]. split.
    { unfold hsu_at_cx, hsu_at. cbn [hsu_Rc0 hsu_Kc app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      all: first [ hw5_kept Hat Hkeep Kc
                 | (cbn [hd_at hd_xv]; rewrite (Z.mod_small _ (2 ^ 64)) by lia; first [exact R80 | exact R88 | exact R90 | exact R98])
                 | (cbn [hd_at hd_xv]; rewrite Hcur1; exact R21)
                 | (cbn [hd_at hd_xv]; rewrite Hnl1; exact R26) ]. }
    split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Ht'|].
    split; [exact Hwf|]. split; [exact Hlen1|]. split; [exact Hps|].
    split; [rewrite <- Ez; exact (hw5o_tie_open sh ps sel rest (x :: t) (bv_unsigned x) t Hselr Hsel4 Hselb eq_refl)|].
    split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hpsnp|]. split; [exact Hnp3|]. split; [exact Hsh7|].
    split; [exact Hps2|]. split; [lia|]. split; [constructor | reflexivity].
  + (* a count in 1 .. 32: the pod loop's head C, pod index 0 *)
    eapply SRr_bind.
    { change (cfg_at rsegs (bi_SELS headamp_bld_B) regs2 mem2 md2) with (cfg_at rsegs 0x816fc regs2 mem2 md2).
      refine (hw5o_core_pos B MT MTL (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
        (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (e_R (x_e cx)) (e_pp (x_e cx)) (hsu_at_of sh ps)
        (hsu_cur rsegs cx rest (x :: t)) (Z.of_nat (length (x :: t))) (e_F (x_e cx) + HSU_E62) (Z.of_nat (length ps))
        HJ Ppin2 Ppout A2 A5 A6 A7 A9 A14 A18 A26 A27 A28 Vf0 V108 V130 V148 V150 Vlen Hrom RB3 RB1 RB2 Hat16
        ltac:(lia) Hcur0 ltac:(unfold HSU_E62; lia) ltac:(lia) Hnl0 Hc1' Hc2' Hamc (bv_unsigned x) Vb Vbr Rab Ez). }
    intros W3 c3 Hle Hpost.
    destruct (hw5_core_post B MT MTL cx (hsu_E1 rsegs headamp_himg_B cx) _ ly2 S2 W2 regs2 mem2 md2 0x81888 _ _ W3 c3
      Hcore HEp Hclob Hpost) as (ly3 & S3 & regs3 & mem3 & md3 & -> & Hcore3 & Hkeep & Hmem &
      (Rb & Rl & R80 & R88 & R90 & R98 & R20 & R128 & R21 & R26 & R11)).
    rewrite Hsp in Hmem. unfold op_clob in Hkeep.
    destruct (hw5o_after cx rest sh np sel ps (x :: t) ly2 S2 W2 regs2 mem2 md2 W3 ly3 S3 regs3 mem3 md3
      Hpre Hcut0 Hcore3 Hmem Rb Rl) as (Hfsh3 & Hpp3).
    assert (Kc : forall a, e_R (x_e cx) <= a < e_R (x_e cx) + 0x80 \/ e_R (x_e cx) + 0xa0 <= a < e_R (x_e cx) + 0x128 \/
        e_R (x_e cx) + 0x130 <= a < e_R (x_e cx) + 0x158 ->
      aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
    { intros a Ha. apply Hmem; [unfold T_SEG_STK, ASTACK in *; lia | lia | unfold op_E; unfold T_SEG_STK, ASTACK in *; lia]. }
    assert (Hcnt : 0 < bv_unsigned x mod 33 <= 32) by (pose proof (Z.mod_pos_bound (bv_unsigned x) 33 ltac:(lia)); lia).
    change (cfg_at rsegs 0x81888 regs3 mem3 md3) with (cfg_at rsegs (bi_C headamp_bld_B) regs3 mem3 md3).
    apply (HC ly3 S3 W3 regs3 mem3 md3 sh np ps (bv_unsigned x mod 33) [] t Hlen eq_refl).
    split.
    { split; [exact Hcore3|]. split; [exact Hin|]. split; [exact Ht'|]. split; [exact Ht'|].
      split; [exact Hwf|]. split; [exact Hlen1|]. split; [exact Hps|].
      split; [exact (hw5o_tie_open sh ps sel rest (x :: t) (bv_unsigned x) t Hselr Hsel4 Hselb eq_refl)|].
      split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hpsnp|]. split; [exact Hnp3|]. split; [exact Hsh7|].
      split; [exact Hps2|]. split; [lia|]. split; [constructor|]. split; [cbn; lia | cbn [length Z.of_nat]; lia]. }
    split.
    { unfold hsu_at_cx, hsu_at. cbn [hsu_L_pod hsu_Rc0 hsu_Kc app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      all: first [ hw5_kept Hat Hkeep Kc
                 | (cbn [hd_at hd_xv]; rewrite (Z.mod_small _ (2 ^ 64)) by lia;
                    first [exact R80 | exact R88 | exact R90 | exact R98 | exact R128])
                 | (cbn [hd_at hd_xv]; exact R20)
                 | (cbn [hd_at hd_xv]; rewrite Hcur1; exact R21)
                 | (cbn [hd_at hd_xv]; rewrite Hnl1; exact R26)
                 | (cbn [hd_at hd_xv length Z.of_nat]; exact R11) ]. }
    split; [exact Hfsh3 | exact Hpp3].
Qed.
End p.

Print Assumptions hw5o_core_nil.
Print Assumptions hw5o_core_zero.
Print Assumptions hw5o_core_pos.
Print Assumptions hw5_piece_open.
