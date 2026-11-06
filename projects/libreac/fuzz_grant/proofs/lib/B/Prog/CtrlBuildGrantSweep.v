(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE2d.v, proofs/cgif/cgif_file_fuzzer/lib/UI2d.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on image B (fuzz_grant.asan-ubsan, bin fde52226dc48, 0x8363c = BASE + 0x2c00, 367 slots), ported from lib/A/Prog/CtrlBuildGrantSweep.v at a working branch 5aae1e8a0ce (its Require closure: 196 files, 0 Admitted / admit / Axiom / Parameter), with the steps of the class-6 side-stack frame adapted from lib/A/Prog/CtrlStampHeadamp.v at the same commit (whose own cgif sources are proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, ACam.v, ACbf.v, ACf6.v, AChd.v); every address, constant and byte is image B's. *)
(* reac_ctrl_build_grant_sweep (0x8363c) on fuzz_grant's ASan+UBSan build (image B).

   It fills the caller's row buffer with the enrolment burst SWEEP base w vals (lib/Prog/GrantSweepModel.v) and returns
   bgs_rows w, or returns -1 having changed no byte of its caller's when bgs_ok fails. Unlike image A, it takes a
   class-6 frame F on the side stack for frames (__asan_stack_malloc_6 at 0x836c0) holding two 1492-byte scratches
   (F + 32, F + 1664), marks F's shadow itself and through __asan_set_shadow_f8 / _00, builds each head-amp row in a
   scratch with reac_ctrl_stamp_headamp, and releases F with __asan_stack_free_6 (0x83b9c) on every path.

   The proof: `binv` is the invariant between steps (the caller's journal with F owned, tcj_kept relative to the call's
   entry, the saved registers, the prologue's locals, F's flag pointer and the rows laid so far); the lemmas below are
   the frame facts, one lemma per runtime / program call (call_ss, call_memset, call_cpy, call_stamp), and one lemma per
   stretch of code between fixed register files (entry, seg_shadow, seg_admit, row1, seg_mark, gb, outer, row2, epi). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YG0s YG0p.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import StackFreeDef.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import StackFreeJournal.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC4b YC81 YC88 YCbw YCkd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib YC1g YC1h YC1i YC45 YC85 GrantFrame GrantRo.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import ACj1 ACbf GrantACja GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* zify's euclidean-division flag: false in this file (image A's walk sets it so too); a few lemmas set it to true
   around themselves and back to false; every setting is Local. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope. Open Scope Z_scope.
(* rs_hold A is A, but lia sees an atom: a hypothesis behind it stays one of the lemma (Section w hides HVALS so from lia) *)
Definition rs_hold (A : Prop) : Prop := A. Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
(* ---- the rows, address-free (image-free twins of lib/Prog/BgsLoop.v's prefixB lemmas) ------------------ *)
Definition bgs_prefixB (base : Z) (vl : list byte) (c : nat) : list byte :=
  HEAD_ACK34 ++ ga_chan base vl 0 ++ HEAD_MARK34 ++ GBall ++ concat (map (ga_chan base vl) (seq 1 (c - 1))).
Lemma bgs_prefixB_SWEEP : forall base vl w, bgs_prefixB base vl w = SWEEP base w vl.
Proof. reflexivity. Qed.
Lemma bgs_prefixB_step : forall base vl c, (1 <= c)%nat ->
  ((bgs_prefixB base vl c ++ ga_row base vl c 0) ++ ga_row base vl c 1) ++ ga_row base vl c 2 = bgs_prefixB base vl (S c).
Proof.
  intros base vl c Hc. unfold bgs_prefixB, ga_chan.
  replace (S c - 1)%nat with (S (c - 1)) by lia. rewrite seq_S.
  replace (1 + (c - 1))%nat with c by lia. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r.
  rewrite !app_assoc. reflexivity.
Qed.
Lemma bgs_ga_row_eq : forall base vl c p, 0 <= c -> 0 <= p < 3 -> base + c < 256 -> 0 <= base ->
  GA (base + c) p (vz vl (Z.to_nat (3 * c + p))) = ga_row base vl (Z.to_nat c) (Z.to_nat p).
Proof.
  intros base vl c p Hc Hp Hb Hb0. unfold ga_row.
  rewrite Z2Nat.id by lia. rewrite (Z.mod_small (base + c)) by lia. rewrite Z2Nat.id by lia.
  f_equal. f_equal. lia.
Qed.
Lemma bgs_prefixB1 : forall base vl, 0 <= base < 256 ->
  bgs_prefixB base vl 1 =
  ((((HEAD_ACK34 ++ GA base 0 (vz vl 0)) ++ GA base 1 (vz vl 1)) ++ GA base 2 (vz vl 2)) ++ HEAD_MARK34) ++ GBall.
Proof.
  intros base vl Hb. unfold bgs_prefixB, ga_chan, ga_row. cbn [seq map concat Nat.sub]. rewrite app_nil_r.
  change (Z.of_nat 0) with 0. change (Z.of_nat 1) with 1. change (Z.of_nat 2) with 2.
  change (3 * 0 + 0)%nat with 0%nat. change (3 * 0 + 1)%nat with 1%nat. change (3 * 0 + 2)%nat with 2%nat.
  rewrite Z.add_0_r, Z.mod_small by lia. rewrite !app_assoc. reflexivity.
Qed.
Lemma bgs_legal_legalb : forall p v, legal p v -> legalb p v = true.
Proof.
  intros p v H. unfold legal in H. unfold legalb.
  destruct H as [[Hp Hv] | [Hp Hv]]; apply Bool.orb_true_iff; [left | right];
  apply Bool.andb_true_iff; split; [apply Z.ltb_lt | apply Z.leb_le | apply Z.eqb_eq | apply Z.leb_le]; lia.
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Variable B : asyms.

Section w.
(* ---- hyps_reac_ctrl_build_grant_sweep (GrantBContracts.v), one by one, and the stamp's contract ---------- *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASM6 : astack_malloc_realizes SEGS B 6.
Hypothesis ASF6 : StackFreeDef.astack_free_realizes SEGS B (SIGMA GS___asan_stack_free_6) 6.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TPFS : RT_TP_FS B.
Hypothesis SS00 : SetShadowDef.aset_shadow_realizes SEGS B (SIGMA GS___asan_set_shadow_00) 0x00.
Hypothesis SSF8 : SetShadowDef.aset_shadow_realizes SEGS B (SIGMA GS___asan_set_shadow_f8) 0xf8.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA GS___asan_memcpy).
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset).
Hypothesis HIMGSH : img_shadow_vis SEGS B.
Hypothesis HGL : globs_marked SEGS B GRANT_GLOBS_B.
Hypothesis HRO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi.
Hypothesis HIMGROWS : IMG_BGS_ROWS B.
Hypothesis TSTAMP : tb_reac_ctrl_stamp_headamp_spec B.

(* ---- the call's fixed data: tb_reac_ctrl_build_grant_sweep_spec's binders and premises, in its order ------ *)
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(s mx base w V : Z) (vals : list byte) (cl : list (Z * Z * Z)).
Hypothesis HJc : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis HROD : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc).
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : getr regs 3 = w64 (as_gp B).
Hypothesis Htp : getr regs 4 = w64 (as_tp B).
Hypothesis H10 : getr regs 10 = w64 s.
Hypothesis H11 : getr regs 11 = w64 mx.
Hypothesis H12 : getr regs 12 = w64 base.
Hypothesis H13 : getr regs 13 = w64 w.
Hypothesis H14 : getr regs 14 = w64 V.
Hypothesis Rs : 0 <= s < 2 ^ 63.
Hypothesis Rmx : - 2 ^ 31 <= mx < 2 ^ 31.
Hypothesis Rbase : 0 <= base < 256.
Hypothesis Rw : - 2 ^ 31 <= w < 2 ^ 31.
Hypothesis RV : 0 <= V < 2 ^ 63.
Hypothesis Hbw31 : base + w < 2 ^ 31.
Hypothesis Hch : achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) cl.
Hypothesis Hal16 : spZ regs mod 16 = 0.
Hypothesis Hwlo : sp0 - STK <= spZ regs - STK_reac_ctrl_build_grant_sweep.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hfr8 : Z.of_nat (length (frames Sc)) <= 8.
Hypothesis HVALS : 1 <= w -> V <> 0 ->
  length vals = Z.to_nat (3 * w) /\ vals_legal (Z.to_nat w) vals /\
  garr8 SEGS (mrestrict (w_H W) memc) V (map bv_unsigned vals) /\
  tsrc_ok W memc (spZ regs) V (3 * w) /\
  afobj SEGS B lyc Sc W memc V (3 * w) /\
  (spZ regs <= V \/ V + 3 * w <= spZ regs - STK_reac_ctrl_build_grant_sweep).
Hypothesis HROWS : bgs_ok s V mx base w ->
  amem_range s (34 * bgs_rows w) /\ s + 34 * bgs_rows w <= 2 ^ 47 - 8 /\
  (s + 34 * bgs_rows w <= IMG_LO_B \/ IMG_TOP_B <= s) /\
  twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) s (34 * bgs_rows w) /\
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s (34 * bgs_rows w) /\
  shadow_hull_vis (aview SEGS (w_H W) memc) s (34 * bgs_rows w) /\
  (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= s /\ s + 34 * bgs_rows w <= b + req_size m) /\
  (spZ regs <= s \/ s + 34 * bgs_rows w <= spZ regs - STK_reac_ctrl_build_grant_sweep) /\
  (V + 3 * w <= s \/ s + 34 * bgs_rows w <= V).
#[local] Notation SP := (spZ regs). #[local] Notation STKB := STK_reac_ctrl_build_grant_sweep.
#[local] Notation TBP := (tb_reac_ctrl_build_grant_sweep_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs s mx base w V vals).
(* lia: its cleanup hides HVALS (lia case-split on it at every call) and names Rs, Rbase, RV (LiaTwx2 re-split them each call) *)
Local Ltac Z.euclidean_division_equations_cleanup ::= try apply rs_hide in HVALS; try pose proof Rs; try pose proof Rbase; try pose proof RV.

(* ---- the frame of the call ---------------------------------------------------------------------------------
   Machine stack: 256 bytes at SP - 256 (ra at SP - 8, s0 at SP - 16, ..., s11 at SP - 104), s0 = SP, then
   `andi sp,sp,-32` (0x8367c): sp = s1 = sp1 for the whole body. Locals at sp1 + 0x10 .. sp1 + 0x98.
   Side stack: the class-6 frame F = frame_addr lyc 6 fpos (4096 bytes; its flag pointer at F + 4088), its 512
   shadow bytes at SHF = SBV + F / 8, and its flag byte FL. *)
Definition SBV : Z := 0x7fff8000.
Definition sp1 : Z := 32 * ((spZ regs - 256) / 32).
Definition RowsE (a : Z) : Prop := s <= a < s + 34 * bgs_rows w.
Definition Fa (fpos : Z) : Z := frame_addr lyc 6 fpos.
Definition FLa (fpos : Z) : Z := flag_addr lyc 6 fpos.
Definition SHa (fpos : Z) : Z := SBV + Fa fpos / 8.
Definition own6 (fpos : Z) (a : Z) : Prop :=
  Fa fpos <= a < Fa fpos + 4096 \/ SHa fpos <= a < SHa fpos + 512 \/ a = FLa fpos.
(* the bytes a step may change without disturbing what the call keeps for its caller (A's own_ok) *)
Definition own_ok (Q : Z -> Prop) : Prop :=
  forall a, Q a -> a < alloc_ceiling /\ ~ in_img SEGS a /\
  (forall b n i, In (b, n) (ablocks B lyc Sc) -> 0 <= i < req_size n -> b + i <> a) /\
  (forall cid pos, In (cid, pos) (frames Sc) ->
     ~ in_zr a (frame_rng lyc (cid, pos)) /\ ~ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)).
(* the caller's callee-saved registers, which the prologue stores at SP - 256 + off *)
Definition SAVED : list (Z * nat) :=
  [(248, 1%nat); (240, 8%nat); (232, 9%nat); (224, 18%nat); (216, 19%nat); (208, 20%nat); (200, 21%nat);
   (192, 22%nat); (184, 23%nat); (176, 24%nat); (168, 25%nat); (160, 26%nat); (152, 27%nat)].
Definition bgs_saved (m : word -> option byte) : Prop :=
  Forall (fun p => val_mem SEGS m (spZ regs - 256 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat (snd p)))))) SAVED.
(* the locals the prologue stores (0x83684 .. 0x836b0) *)
Definition loc0 (m : word -> option byte) : Prop :=
  val_mem SEGS m (sp1 + 0x60) 8 base /\ val_mem SEGS m (sp1 + 0x68) 8 SBV /\
  val_mem SEGS m (sp1 + 0x70) 8 V /\ val_mem SEGS m (sp1 + 0x78) 8 s.
(* the locals of the accepting path (0x83808, 0x83814, 0x8385c, 0x83864) *)
Definition loc_acc (fpos : Z) (m : word -> option byte) : Prop :=
  val_mem SEGS m (sp1 + 0x40) 8 (Fa fpos) /\ val_mem SEGS m (sp1 + 0x20) 8 w /\
  val_mem SEGS m (sp1 + 0x50) 8 (SHa fpos + 4) /\ val_mem SEGS m (sp1 + 0x58) 8 (Fa fpos + 32).
(* the outer loop's locals (0x839d0, 0x839e8 and 0x83b48) for channel c *)
Definition loc_out (fpos : Z) (m : word -> option byte) (c : Z) : Prop :=
  val_mem SEGS m (sp1 + 0x28) 8 (Fa fpos + 48) /\ val_mem SEGS m (sp1 + 0x48) 8 (2 ^ 31 - 9 - 3 * c).
(* the inner loop's locals (0x83a0c, 0x83a1c, 0x83a30, 0x83a38) for channel c *)
Definition loc_in (m : word -> option byte) (c : Z) : Prop :=
  val_mem SEGS m (sp1 + 0x10) 8 c /\ val_mem SEGS m (sp1 + 0x18) 8 (3 * c + 11) /\
  val_mem SEGS m (sp1 + 0x30) 8 (base + c) /\ val_mem SEGS m (sp1 + 0x38) 8 0.

(* What holds at every point of the body after the class-6 frame is taken. E is what the call has written of its
   caller's (empty before the admission, RowsE after it); rows are the rows laid down so far. *)
Definition binv (fpos : Z) (E : Z -> Prop) (W2 : world SEGS) (ly2 : alayout) (S2 : astate)
  (mem2 : word -> option byte) (md2 : Model) (rows : list Z) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((6, fpos) :: own) ly2 S2 W2 mem2 md2 k /\
  frames S2 = (6, fpos) :: frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ (exists f, S2 = set_fs f Sc) /\
  tcj_kept B STKB lyc Sc W memc W2 mem2 (spZ regs) E /\
  bgs_saved (mrestrict (w_H W2) mem2) /\ loc0 (mrestrict (w_H W2) mem2) /\
  rdword (aview SEGS (w_H W2) mem2) (Fa fpos + 4088) = Some (FLa fpos) /\
  garr8 SEGS (mrestrict (w_H W2) mem2) s rows.

(* ---- the register files at the boundaries between the pieces --------------------------------------------- *)
Definition rB (R : bvmap 5 word) : Prop :=
  getr R 2 = w64 sp1 /\ getr R 3 = w64 (as_gp B) /\ getr R 4 = w64 (as_tp B) /\
  getr R 8 = w64 (spZ regs) /\ getr R 9 = w64 sp1.
(* 0x83730 (BASE + 0x2cf4): F's header is written, s7 = SHF, before the shadow byte stores *)
Definition shregs (fpos : Z) (R : bvmap 5 word) : Prop :=
  rB R /\ getr R 10 = w64 (-15) /\ getr R 18 = w64 (Fa fpos) /\ getr R 19 = w64 w /\
  getr R 23 = w64 (SHa fpos) /\ getr R 24 = w64 (Fa fpos) /\ getr R 25 = w64 mx.
(* 0x837a8 (BASE + 0x2d6c): the return of the second __asan_set_shadow_f8 *)
Definition adregs (fpos : Z) (R : bvmap 5 word) : Prop :=
  rB R /\ getr R 18 = w64 (Fa fpos) /\ getr R 19 = w64 w /\ getr R 20 = w64 (SHa fpos + 4) /\
  getr R 23 = w64 (SHa fpos) /\ getr R 24 = w64 (Fa fpos) /\ getr R 25 = w64 mx /\ getr R 27 = w64 (SHa fpos + 208).
(* 0x8389c (BASE + 0x2e60): the first channel's loop head, row p; and 0x83954 (BASE + 0x2f18) with p = 3 *)
Definition l1regs (fpos : Z) (R : bvmap 5 word) (p : Z) : Prop :=
  rB R /\ getr R 19 = w64 (-1 - V) /\ getr R 20 = w64 (Fa fpos + 1680) /\
  getr R 21 = w64 (s + 34 * (1 + p)) /\ getr R 22 = w64 (s + 34 * (1 + p)) /\ getr R 23 = w64 (SHa fpos) /\
  getr R 24 = w64 (Fa fpos) /\ getr R 25 = w64 (Fa fpos + 1664) /\ getr R 26 = w64 p /\
  getr R 27 = w64 (SHa fpos + 208).
(* 0x8398c (BASE + 0x2f50): the GRANT_GROUPB loop head, row i; and 0x839bc (BASE + 0x2f80) with i = 6 *)
Definition gbregs (fpos : Z) (R : bvmap 5 word) (i : Z) : Prop :=
  rB R /\ getr R 18 = w64 (s + 170 + 34 * i) /\ getr R 19 = w64 (6 - i) /\
  getr R 20 = w64 (VAL (A_OBJ B_GROUPB) + 34 * i) /\ getr R 21 = w64 (s + 170 + 34 * i) /\
  getr R 23 = w64 (SHa fpos) /\ getr R 24 = w64 (Fa fpos).
(* 0x839f4 (BASE + 0x2fb8): the outer loop head, channel c *)
Definition oregs (fpos : Z) (R : bvmap 5 word) (c : Z) : Prop :=
  rB R /\ getr R 11 = w64 34 /\ getr R 13 = w64 c /\ getr R 19 = w64 (SHa fpos + 4) /\
  getr R 22 = w64 (Fa fpos + 32) /\ getr R 23 = w64 (SHa fpos) /\ getr R 24 = w64 (Fa fpos) /\
  getr R 26 = w64 (3 * c + 8).
(* 0x83a40 (BASE + 0x3004): the inner loop head, channel c, row p; and 0x83b38 (BASE + 0x30fc) with p = 3 *)
Definition i2regs (fpos : Z) (R : bvmap 5 word) (c p : Z) : Prop :=
  rB R /\ getr R 19 = w64 (SHa fpos + 4) /\ getr R 20 = w64 (3 * c) /\ getr R 21 = w64 p /\
  getr R 22 = w64 (Fa fpos + 32) /\ getr R 23 = w64 (SHa fpos) /\ getr R 24 = w64 (Fa fpos) /\
  getr R 25 = w64 (s + 34 * (3 * c + 8 + p)) /\ getr R 26 = w64 (3 * c + 8 + p) /\
  getr R 27 = w64 (s + 34 * (3 * c + 8 + p)).
(* 0x83b80 (BASE + 0x3144): the release of F, with the result res in s10 *)
Definition eregs (fpos : Z) (R : bvmap 5 word) (res : Z) : Prop :=
  rB R /\ getr R 18 = w64 (Fa fpos) /\ getr R 24 = w64 (Fa fpos) /\ getr R 26 = w64 res.

(* the rows laid down after the first channel and after channel c - 1 *)
Definition prefix3 : list Z :=
  ((HEAD_ACK34z ++ GAz base 0 (vz vals (Z.to_nat 0))) ++ GAz base 1 (vz vals (Z.to_nat 1))) ++ GAz base 2 (vz vals (Z.to_nat 2)).
Definition prefixZ (c : Z) : list Z := map bv_unsigned (bgs_prefixB base vals (Z.to_nat c)).

(* the continuations of the loop pieces *)
Definition L1post (fpos p : Z) (rows : list Z) : world SEGS -> config -> Prop :=
  fun W3 c3 => exists ly3 S3 regs3 mem3 md3,
    c3 = mkCfg (mkst regs3 (Z_to_bv 64 (BASE + (if p =? 3 then 0x2f18 else 0x2e60))) mem3 (seg_rom SEGS)) md3 /\
    binv fpos RowsE W3 ly3 S3 mem3 md3 rows /\ l1regs fpos regs3 p /\ loc_acc fpos (mrestrict (w_H W3) mem3).
Definition GBpost (fpos i : Z) (rows : list Z) : world SEGS -> config -> Prop :=
  fun W3 c3 => exists ly3 S3 regs3 mem3 md3,
    c3 = mkCfg (mkst regs3 (Z_to_bv 64 (BASE + (if i =? 6 then 0x2f80 else 0x2f50))) mem3 (seg_rom SEGS)) md3 /\
    binv fpos RowsE W3 ly3 S3 mem3 md3 rows /\ gbregs fpos regs3 i /\ loc_acc fpos (mrestrict (w_H W3) mem3).
Definition I2post (fpos c p : Z) (rows : list Z) : world SEGS -> config -> Prop :=
  fun W3 c3 => exists ly3 S3 regs3 mem3 md3,
    c3 = mkCfg (mkst regs3 (Z_to_bv 64 (BASE + (if p =? 3 then 0x30fc else 0x3004))) mem3 (seg_rom SEGS)) md3 /\
    binv fpos RowsE W3 ly3 S3 mem3 md3 rows /\ i2regs fpos regs3 c p /\
    loc_acc fpos (mrestrict (w_H W3) mem3) /\ loc_out fpos (mrestrict (w_H W3) mem3) c /\
    loc_in (mrestrict (w_H W3) mem3) c.

(* ==== THE LEMMAS OF THE WALK, in dependency order ========================================================= *)
(* ---- H1: frame and invariant facts -------------------------------------------------------------------- *)
Lemma stk_bounds : alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STKB <= spZ regs /\
  spZ regs <= ly_stk_hi ly /\ ly_stk_hi ly <= 2 ^ 47 /\ sp0 mod 16 = 0 /\ ly_stk_lo ly + STK <= sp0 /\
  sp0 <= ly_stk_hi ly.
Proof.
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof Hwlo as Hlo. pose proof Hwhi as Hhi. lia.
Qed.
Lemma sp1_facts : sp1 mod 32 = 0 /\ spZ regs - 272 <= sp1 <= spZ regs - 256.
Proof.
  unfold sp1. pose proof (Z.div_mod (spZ regs - 256) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 256) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hal16, Z.add_0_r in D16.
  split; [rewrite Z.mul_comm; apply Z_mod_mult | lia].
Qed.
(* the layout facts every state of the caller's journal shares with the call's entry *)
Lemma h1_jlayout : forall own2 W2 ly2 S2 mem2 md2 kk,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own2 ly2 S2 W2 mem2 md2 kk ->
  ly_stk_lo ly2 = ly_stk_lo ly /\ ly_stk_hi ly2 = ly_stk_hi ly /\ ly_top ly2 = ly_top lyc /\
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) /\ (forall c p, flag_addr ly2 c p = flag_addr lyc c p).
Proof.
  intros own2 W2 ly2 S2 mem2 md2 kk (_ & Hly & _).
  pose proof HJc as (_ & Hlyc & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _).
  destruct Hlyc as (_ & _ & _ & _ & _ & EFc & _ & _ & Etopc & _).
  split; [exact Eslo|]. split; [exact Eshi|]. split; [congruence|].
  split; intros c p; [unfold frame_addr | unfold flag_addr]; congruence.
Qed.
(* image A's own_frame_ok (CtrlStampHeadamp.v) for the class-6 frame: F's 4096 bytes, its 512 shadow bytes and its
   flag byte lie outside everything tcj_kept protects for the caller *)
Lemma h1_own6_ok : forall fpos ly2 S2 W2 mem2 md2,
  AR SEGS B ly2 S2 W2 mem2 md2 -> frames S2 = (6, fpos) :: frames Sc -> ablocks B ly2 S2 = ablocks B lyc Sc ->
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) -> (forall c p, flag_addr ly2 c p = flag_addr lyc c p) ->
  own_ok (own6 fpos).
Proof.
  intros fpos ly2 S2 W2 m2 md2 HAR Hfrs Eab EF EFL.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof pa_segs_low as Hsegs.
  assert (Hfin : In (6, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 6 fpos HAR Hfin) as (F4 & Fc & Fapp).
  destruct (frame_al64 SEGS B _ _ _ _ _ 6 fpos HAR Hfin) as (F64 & _ & _).
  destruct (FFL _ _ _ _ _ 6 fpos HAR Hfin) as (_ & FLown & (_ & FLimg) & (_ & _ & FLc)).
  assert (Fimg : forall a, frame_addr ly2 6 fpos <= a < frame_addr ly2 6 fpos + fs_frame_bytes 6 -> ~ in_img SEGS a)
    by (intros a; exact (frm_img SEGS B LAWS _ _ _ _ _ 6 fpos a HAR Hfin)).
  assert (Fblk : forall b n, In (b, n) (ablocks B lyc Sc) ->
    zdisjoint (b, req_size n) (frame_addr lyc 6 fpos, 4096) /\
    (forall a, b <= a < b + req_size n -> ~ aowned B ly2 S2 a) /\ in_app b (req_size n)).
  { intros b n Hb. rewrite <- Eab in Hb.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & _ & _ & Bapp & Bpres & _).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b n 6 fpos HAR Hb Hfin) as Hd.
    rewrite EF in Hd. change (fs_frame_bytes 6) with 4096 in Hd.
    split; [exact Hd|]. split; [intros a Ha; exact (proj2 (Bpres a Ha)) | exact Bapp]. }
  assert (Gfr : forall cid pos, In (cid, pos) (frames Sc) ->
    zdisjoint (frame_addr lyc 6 fpos, 4096) (frame_addr lyc cid pos, fs_frame_bytes cid) /\
    frame_addr lyc cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 4096 <= frame_addr lyc cid pos /\
    frame_addr lyc cid pos + fs_frame_bytes cid <= alloc_ceiling /\
    in_app (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
    (forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> ~ aowned B ly2 S2 a) /\
    (forall i, 0 <= i < fs_frame_bytes cid / 8 -> ~ aowned B ly2 S2 (shadow_addr (frame_addr lyc cid pos) + i))).
  { intros cid pos Hf.
    assert (Hf2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; right; exact Hf).
    destruct (in_split _ _ Hf) as (l2 & l3 & El).
    pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (6, fpos) (cid, pos) [] l2 l3 HAR
      ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
    unfold frame_rng in Hd. cbn [fst snd] in Hd. rewrite !EF in Hd. change (fs_frame_bytes 6) with 4096 in Hd.
    destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HAR Hf2) as (G64 & Gb64 & _).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hf2) as (G4 & Gc & Gapp).
    destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hf2) as (_ & _ & Gpres & GSpres).
    rewrite EF in G64, G4, Gc, Gapp, Gpres, GSpres.
    split; [exact Hd|]. split; [exact G64|]. split; [exact Gb64|]. split; [exact G4|]. split; [exact Gc|].
    split; [exact Gapp|].
    split; [intros a Ha; exact (proj2 (Gpres a Ha)) | intros i Hi; exact (proj2 (GSpres i Hi))]. }
  rewrite EF in F4, Fc, Fapp, F64, Fimg. rewrite EFL in FLown, FLimg, FLc.
  change (fs_frame_bytes 6) with 4096 in Fc, Fapp, Fimg.
  unfold own_ok, own6, SHa, SBV, Fa, FLa.
  intros a Ha.
  pose proof (Z.div_mod (frame_addr lyc 6 fpos) 64 ltac:(lia)) as DF0. rewrite F64, Z.add_0_r in DF0.
  assert (HF8 : frame_addr lyc 6 fpos / 8 = 8 * (frame_addr lyc 6 fpos / 64)).
  { rewrite DF0 at 1. replace (64 * (frame_addr lyc 6 fpos / 64)) with (8 * (frame_addr lyc 6 fpos / 64) * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp.
  split; [destruct Ha as [Ha|[Ha|Ha]]; [lia | lia | subst a; exact FLc]|].
  split.
  { destruct Ha as [Ha|[Ha|Ha]].
    - exact (Fimg a Ha).
    - intros Hi. pose proof (Hsegs a Hi) as Hl. rewrite C5 in Hl. lia.
    - subst a. exact FLimg. }
  split.
  { intros b n i Hb Hi Heq.
    destruct (Fblk b n Hb) as (Hd & Bown & Bapp).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bapp. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    destruct Ha as [Ha|[Ha|Ha]].
    - lia.
    - lia.
    - subst a. apply (Bown (b + i) ltac:(lia)). rewrite Heq. exact FLown. }
  intros cid pos Hf.
  destruct (Gfr cid pos Hf) as (Hd & G64 & Gb64 & G4 & Gc & Gapp & Gown & GSown).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Gapp. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  unfold frame_rng, in_zr. cbn [fst snd].
  pose proof (Z.div_mod (frame_addr lyc cid pos) 64 ltac:(lia)) as DG. rewrite G64, Z.add_0_r in DG.
  pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as Dg. rewrite Gb64, Z.add_0_r in Dg.
  assert (HG8 : frame_addr lyc cid pos / 8 = 8 * (frame_addr lyc cid pos / 64)).
  { rewrite DG at 1. replace (64 * (frame_addr lyc cid pos / 64)) with (8 * (frame_addr lyc cid pos / 64) * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  assert (Hg8 : fs_frame_bytes cid / 8 = 8 * (fs_frame_bytes cid / 64)).
  { rewrite Dg at 1. replace (64 * (fs_frame_bytes cid / 64)) with (8 * (fs_frame_bytes cid / 64) * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  assert (Hsh : shadow_addr (frame_addr lyc cid pos) = 2147450880 + frame_addr lyc cid pos / 8)
    by (unfold shadow_addr, SHADOW_OFF; reflexivity).
  rewrite Hsh. rewrite Hsh in GSown.
  destruct Ha as [Ha|[Ha|Ha]].
  - split; lia.
  - split; lia.
  - subst a. split.
    + intros Hz. exact (Gown (flag_addr lyc 6 fpos) Hz FLown).
    + intros Hz. apply (GSown (flag_addr lyc 6 fpos - (2147450880 + frame_addr lyc cid pos / 8)) ltac:(lia)).
      replace (2147450880 + frame_addr lyc cid pos / 8 + (flag_addr lyc 6 fpos - (2147450880 + frame_addr lyc cid pos / 8)))
        with (flag_addr lyc 6 fpos) by lia.
      exact FLown.
Qed.
Lemma binv_frame : forall fpos E W2 ly2 S2 mem2 md2 rows, binv fpos E W2 ly2 S2 mem2 md2 rows ->
  Fa fpos mod 64 = 0 /\ 4096 <= Fa fpos /\ Fa fpos + 4096 <= alloc_ceiling /\
  (Fa fpos + 4096 <= IMG_LO_B \/ IMG_TOP_B <= Fa fpos) /\ Fa fpos + 4096 <= 2 ^ 47 - 8 /\
  amem_range (Fa fpos) 4096 /\
  (forall a, Fa fpos <= a < Fa fpos + 4096 -> apresent (w_H W2) mem2 a /\ ~ aowned B ly2 S2 a) /\
  (forall a, SHa fpos <= a < SHa fpos + 512 -> apresent (w_H W2) mem2 a /\ ~ aowned B ly2 S2 a) /\
  own_ok (own6 fpos).
Proof.
  intros fpos E W2 ly2 S2 mem2 md2 rows HI.
  pose proof HI as (HJ & Hfrs & Eab & _).
  destruct (h1_jlayout _ _ _ _ _ _ _ HJ) as (_ & _ & _ & EF & EFL).
  pose proof (proj1 HJ) as HAR.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hfin : In (6, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 6 fpos HAR Hfin) as (F4 & Fc & Fapp).
  destruct (frame_al64 SEGS B _ _ _ _ _ 6 fpos HAR Hfin) as (F64 & _ & _).
  pose proof (frm_off_imgB B ly2 S2 W2 mem2 md2 6 fpos HAR Hfin) as Foff.
  destruct (al_frames _ _ LAWS _ _ _ _ _ 6 fpos HAR Hfin) as (_ & _ & Fpres & FSpres).
  rewrite EF in F4, Fc, Fapp, F64, Foff, Fpres, FSpres.
  change (fs_frame_bytes 6) with 4096 in Fc, Fapp, Foff, Fpres, FSpres.
  change (4096 / 8) with 512 in FSpres.
  unfold SHa, SBV, Fa.
  split; [exact F64|]. split; [exact F4|]. split; [exact Fc|]. split; [exact Foff|].
  split; [lia|].
  split; [exact (amem_range_sub_app (frame_addr lyc 6 fpos) 4096 (frame_addr lyc 6 fpos) 4096 Fapp Fc
    ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [exact Fpres|].
  split.
  { intros a Ha.
    assert (Hsh : shadow_addr (frame_addr lyc 6 fpos) = 2147450880 + frame_addr lyc 6 fpos / 8)
      by (unfold shadow_addr, SHADOW_OFF; reflexivity).
    assert (Hi : 0 <= a - shadow_addr (frame_addr lyc 6 fpos) < 512) by (rewrite Hsh; lia).
    specialize (FSpres _ Hi).
    replace (shadow_addr (frame_addr lyc 6 fpos) + (a - shadow_addr (frame_addr lyc 6 fpos))) with a in FSpres by lia.
    exact FSpres. }
  exact (h1_own6_ok fpos ly2 S2 W2 mem2 md2 HAR Hfrs Eab EF EFL).
Qed.
Lemma binv_layout : forall fpos E W2 ly2 S2 mem2 md2 rows, binv fpos E W2 ly2 S2 mem2 md2 rows ->
  ly_stk_lo ly2 = ly_stk_lo ly /\ ly_stk_hi ly2 = ly_stk_hi ly /\ ly_top ly2 = ly_top lyc /\
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) /\ (forall c p, flag_addr ly2 c p = flag_addr lyc c p).
Proof. intros fpos E W2 ly2 S2 mem2 md2 rows (HJ & _). exact (h1_jlayout _ _ _ _ _ _ _ HJ). Qed.
Lemma arod_binv : forall fpos E W2 ly2 S2 mem2 md2 rows, binv fpos E W2 ly2 S2 mem2 md2 rows ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
  intros fpos E W2 ly2 S2 mem2 md2 rows (_ & _ & _ & _ & (_ & _ & K3 & _) & _) a Hro Hns He.
  rewrite (K3 a); [exact (HROD a Hro Hns He) | | exact Hns | exact He].
  destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)].
Qed.
(* the values: their bytes and their shadow are the caller's at every point *)
Lemma h1_fsb8 : forall c, 0 <= c -> fs_frame_bytes c mod 8 = 0.
Proof.
  intros c Hc. unfold fs_frame_bytes.
  rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ c) with ((8 * 2 ^ c) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma vals_at : forall fpos E W2 ly2 S2 mem2 md2 rows, bgs_ok s V mx base w ->
  binv fpos E W2 ly2 S2 mem2 md2 rows -> (forall a, E a -> RowsE a) ->
  garr8 SEGS (mrestrict (w_H W2) mem2) V (map bv_unsigned vals) /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF V (3 * w) /\
  0 <= V /\ V + 3 * w <= 2 ^ 47 - 1 /\ length vals = Z.to_nat (3 * w) /\ vals_legal (Z.to_nat w) vals.
Proof.
  intros fpos E W2 ly2 S2 mem2 md2 rows HOK HI HE.
  pose proof HI as (_ & _ & _ & _ & (K1 & K2 & K3 & K4 & K5 & K6) & _).
  pose proof HOK as (Hs0 & HV0 & Hw1 & Hbw & Hmx).
  destruct (HVALS Hw1 HV0) as (Hlen & Hleg & HG & (_ & HraV & _ & Ham & HVz & _) &
    ((cid & pos & Hin & Hcid & Hal & Hlo & Hhi) & _ & _) & _).
  destruct (HROWS HOK) as (Hsam & _ & _ & _ & _ & _ & _ & _ & Hdis).
  assert (H47 : V + 3 * w <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
  assert (HnE : forall a, a < s \/ s + 34 * bgs_rows w <= a -> ~ E a)
    by (intros a Ha He; pose proof (HE a He) as Hr; unfold RowsE in Hr; lia).
  split; [|split; [|split; [lia | split; [exact H47 | split; [exact Hlen | exact Hleg]]]]].
  - eapply (garr8_aview_kept SEGS (w_H W) (w_H W2) memc mem2); [|exact HG].
    rewrite length_map, Hlen. intros a Ha. apply (K4 cid pos a Hin).
    + left. unfold frame_rng, in_zr. cbn [fst snd]. lia.
    + apply HnE. lia.
  - eapply range_addressable_agree; [|exact HraV].
    intros x Hx. apply (K4 cid pos _ Hin).
    + right. unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd].
      pose proof (h1_fsb8 cid Hcid) as Hb8. pose proof (fs_frame_bytes_nonneg cid) as Hbn.
      pose proof (Z.div_mod (frame_addr lyc cid pos) 8 ltac:(lia)) as Df.
      pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as Db.
      assert (Hq : frame_addr lyc cid pos / 8 <= x / 8) by (apply Z.div_le_mono; lia).
      assert (Hq2 : x / 8 < frame_addr lyc cid pos / 8 + fs_frame_bytes cid / 8) by (apply Z.div_lt_upper_bound; lia).
      lia.
    + apply HnE. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hsam. unfold shadow_of_addr, SHADOW_OFF.
      assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
      pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). lia.
Qed.
(* A step inside one world, layout and state (a run of the body or a runtime call): it keeps the invariant when it
   changes only this call's window, the bytes of E' and F's own bytes, and keeps the saved registers, loc0, F's
   flag pointer and the rows. *)
Lemma h1_tcj_mono : forall W2 m2 (E E' : Z -> Prop),
  tcj_kept B STKB lyc Sc W memc W2 m2 (spZ regs) E -> (forall a, E a -> E' a) ->
  tcj_kept B STKB lyc Sc W memc W2 m2 (spZ regs) E'.
Proof.
  intros W2 m2 E E' (K1 & K2 & K3 & K4 & K5 & K6) HE.
  split; [intros a Ha Hw He; apply K1; [exact Ha | exact Hw | intros H; exact (He (HE a H))]|].
  split; [intros b m i Hb Hi He; apply (K2 b m i Hb Hi); intros H; exact (He (HE _ H))|].
  split; [exact K3|].
  split; [intros cid pos a Hf Hz He; apply (K4 cid pos a Hf Hz); intros H; exact (He (HE _ H))|].
  split; [exact K5 | exact K6].
Qed.
(* image A's tcj_step (CtrlStampHeadamp.v) at the call's entry: a step that changes only the window, E and Q, with
   Q outside what tcj_kept protects, keeps tcj_kept *)
Lemma h1_tcj_step : forall W1 m1 W2 m2 (E Q : Z -> Prop),
  tcj_kept B STKB lyc Sc W memc W1 m1 (spZ regs) E ->
  (forall a, E a -> ~ in_img SEGS a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STKB <= a < spZ regs) -> ~ E a -> ~ Q a ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
  own_ok Q ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - STKB <= a < spZ regs) ->
     apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) ->
  (forall a, spZ regs - STKB <= a < spZ regs -> apresent (w_H W2) m2 a) ->
  tcj_kept B STKB lyc Sc W memc W2 m2 (spZ regs) E.
Proof.
  intros W1 m1 W2 m2 E Q (T1 & T2 & T3 & T4 & T5 & T6) HEi Hst HQ Hp Hw.
  pose proof (proj1 HJc) as HAR.
  pose proof stk_bounds as (B1 & B2 & B3 & B4 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof pa_segs_low as Hsegs.
  split.
  { intros a Ha Hn He. rewrite (Hst a ltac:(lia) Hn He); [exact (T1 a Ha Hn He)|].
    intros Hq. destruct (HQ a Hq) as (Hl & _). lia. }
  split.
  { intros b m i Hb Hi He. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4 & Hc & _).
    rewrite (Hst (b + i)); [exact (T2 b m i Hb Hi He) | lia | lia | exact He |].
    intros Hq. destruct (HQ _ Hq) as (_ & _ & Hbl & _). exact (Hbl b m i Hb Hi eq_refl). }
  split.
  { intros a Hi Ho Her. pose proof (Hsegs a Hi) as Hlo. rewrite C5 in Hlo.
    rewrite (Hst a); [exact (T3 a Hi Ho Her) | lia | lia | intros He; exact (HEi a He Hi) |].
    intros Hq. destruct (HQ a Hq) as (_ & Hni & _). exact (Hni Hi). }
  split.
  { intros cid pos a Hf Hz He. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hf) as (F4 & Fc & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hnn.
    pose proof (Z.mul_div_le (frame_addr lyc cid pos) 8 ltac:(lia)) as D1.
    pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)) as D2.
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)) as D3.
    pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as D4.
    assert (Hr : 0 <= a < alloc_ceiling).
    { unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF in Hz. cbn [fst snd] in Hz. lia. }
    rewrite (Hst a); [exact (T4 cid pos a Hf Hz He) | lia | lia | exact He |].
    intros Hq. destruct (HQ a Hq) as (_ & _ & _ & Hfr). destruct (Hfr cid pos Hf) as [N1 N2].
    destruct Hz as [Hz|Hz]; [exact (N1 Hz) | exact (N2 Hz)]. }
  split.
  { intros a Ha Hn Hp0. apply Hp; [exact Ha | exact Hn | exact (T5 a Ha Hn Hp0)]. }
  exact Hw.
Qed.
Lemma h1_saved_off : forall o r, In (o, r) SAVED -> 152 <= o <= 248.
Proof. intros o r Hin. unfold SAVED in Hin. repeat (destruct Hin as [Hq | Hin]; [inversion Hq; subst; lia |]). destruct Hin. Qed.
Lemma binv_kept : forall fpos E E' W2 ly2 S2 mem2 md2 rows mem3 md3,
  binv fpos E W2 ly2 S2 mem2 md2 rows ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((6, fpos) :: own) ly2 S2 W2 mem3 md3 k ->
  (forall a, E a -> E' a) -> (forall a, E' a -> ~ in_img SEGS a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STKB <= a < spZ regs) -> ~ E' a -> ~ own6 fpos a ->
     aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, spZ regs - 104 <= a < spZ regs -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, sp1 + 0x60 <= a < sp1 + 0x80 -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, Fa fpos + 4088 <= a < Fa fpos + 4096 -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, s <= a < s + Z.of_nat (length rows) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  binv fpos E' W2 ly2 S2 mem3 md3 rows.
Proof.
  intros fpos E E' W2 ly2 S2 mem2 md2 rows mem3 md3 HI HJ3 HEE HEi Hout Hsave Hloc Hflp Hrows Hpres.
  pose proof (binv_frame fpos E W2 ly2 S2 mem2 md2 rows HI) as (_ & _ & _ & _ & _ & _ & _ & _ & HQ).
  destruct HI as (HJ & Hfr & Hbl & Hfs & HK & Hsv & Hl0 & Hfl & Hrw).
  split; [exact HJ3|]. split; [exact Hfr|]. split; [exact Hbl|]. split; [exact Hfs|].
  split.
  { apply (h1_tcj_step W2 mem2 W2 mem3 E' (own6 fpos) (h1_tcj_mono W2 mem2 E E' HK HEE) HEi Hout HQ).
    - intros a Ha _ Hp. exact (Hpres a Ha Hp).
    - intros a Ha. pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP3 & _).
      apply HP3. pose proof Hwlo as Hlo. pose proof Hwhi as Hhi. lia. }
  split.
  { unfold bgs_saved in *. apply Forall_forall. intros [o r] Hin.
    pose proof (proj1 (Forall_forall _ _) Hsv _ Hin) as Hv.
    pose proof (h1_saved_off o r Hin) as Ho. cbn [fst snd] in *.
    eapply (val_mem_aview_kept_x SEGS (w_H W2) (w_H W2) mem2 mem3); [|exact Hv].
    intros x Hx. apply Hsave. lia. }
  split.
  { destruct Hl0 as (L1 & L2 & L3 & L4). unfold loc0.
    split; [|split; [|split]];
    (eapply (val_mem_aview_kept_x SEGS (w_H W2) (w_H W2) mem2 mem3); [|eassumption]);
    intros x Hx; apply Hloc; lia. }
  split.
  { rewrite (rdword_ext (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3)); [exact Hfl|].
    intros k0 Hk. apply Hflp. lia. }
  eapply (garr8_aview_kept SEGS (w_H W2) (w_H W2) mem2 mem3); [|exact Hrw].
  intros a Ha. exact (Hrows a Ha).
Qed.
(* the shadow a scratch needs before __asan_memset and before the stamp writes into it *)
Lemma h1_xdiv : forall F X x, F mod 64 = 0 -> (X = 32 \/ X = 1664) ->
  F / 8 * 8 = F /\ X / 8 * 8 = X /\ x / 8 = F / 8 + X / 8 + (x - F - X) / 8.
Proof.
  intros F X x H64 HX.
  pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite H64, Z.add_0_r in D.
  assert (HF : F / 8 * 8 = F).
  { rewrite D at 1. replace (64 * (F / 64)) with ((F / 64 * 8) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (HX8 : X / 8 * 8 = X) by (destruct HX as [-> | ->]; reflexivity).
  split; [exact HF|]. split; [exact HX8|].
  replace x with ((x - F - X) + (F / 8 + X / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia.
Qed.
Lemma ra_scratch : forall fpos (rd : Z -> option Z) X, (X = 32 \/ X = 1664) -> Fa fpos mod 64 = 0 ->
  (forall i, 0 <= i < 186 -> rd (SHa fpos + X / 8 + i) = Some 0) -> rd (SHa fpos + X / 8 + 186) = Some 4 ->
  range_addressable rd SHADOW_OFF (Fa fpos + X) 1492.
Proof.
  intros fpos rd X HX H64 H0 H4 x Hx.
  destruct (h1_xdiv (Fa fpos) X x H64 HX) as (HF & HX8 & Hq).
  unfold SHa, SBV in H0, H4. unfold shadow_of_addr, SHADOW_OFF.
  destruct (Z_lt_ge_dec (x - Fa fpos - X) 1488) as [Hlt | Hge].
  - exists 0. split; [|left; reflexivity].
    assert (Hr : 0 <= (x - Fa fpos - X) / 8 < 186)
      by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    replace (2147450880 + x / 8) with (2147450880 + Fa fpos / 8 + X / 8 + (x - Fa fpos - X) / 8) by lia.
    exact (H0 _ Hr).
  - assert (H186 : (x - Fa fpos - X) / 8 = 186)
      by (symmetry; apply (Z.div_unique (x - Fa fpos - X) 8 186 (x - Fa fpos - X - 1488)); [left; lia | lia]).
    exists 4. split.
    + replace (2147450880 + x / 8) with (2147450880 + Fa fpos / 8 + X / 8 + 186) by lia. exact H4.
    + right. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. lia.
Qed.
Lemma sh_zero_stamp : forall fpos (rd : Z -> option Z) X, (X = 32 \/ X = 1664) -> Fa fpos mod 64 = 0 ->
  (forall i, 0 <= i < 186 -> rd (SHa fpos + X / 8 + i) = Some 0) ->
  forall x, Fa fpos + X + 16 <= x < Fa fpos + X + 50 -> rd (shadow_addr x) = Some 0.
Proof.
  intros fpos rd X HX H64 H0 x Hx.
  destruct (h1_xdiv (Fa fpos) X x H64 HX) as (HF & HX8 & Hq).
  unfold SHa, SBV in H0. unfold shadow_addr, SHADOW_OFF.
  assert (Hr : 0 <= (x - Fa fpos - X) / 8 < 186)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  replace (2147450880 + x / 8) with (2147450880 + Fa fpos / 8 + X / 8 + (x - Fa fpos - X) / 8) by lia.
  exact (H0 _ Hr).
Qed.
(* the rows, as bgs_prefixB counts them *)
Lemma len_GAz : forall ch p v, length (GAz ch p v) = 34%nat.
Proof. reflexivity. Qed.
Lemma vz_range : forall j, 0 <= vz vals j < 256.
Proof. intros j. unfold vz. exact (bv_unsigned_in_range 8 (nth j vals (Z_to_bv 8 0))). Qed.
Lemma h1_len_chans : forall l, length (concat (map (ga_chan base vals) l)) = (102 * length l)%nat.
Proof.
  induction l as [|x l IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, IH.
  assert (Hl : length (ga_chan base vals x) = 102%nat)
    by (unfold ga_chan, ga_row; rewrite !length_app, !length_GA; reflexivity).
  rewrite Hl. lia.
Qed.
Lemma len_prefixZ : forall c, 1 <= c -> Z.of_nat (length (prefixZ c)) = 34 * (3 * c + 8).
Proof.
  intros c Hc. unfold prefixZ, bgs_prefixB. rewrite length_map, !length_app, h1_len_chans, length_seq.
  assert (L1 : length HEAD_ACK34 = 34%nat) by reflexivity.
  assert (L2 : length (ga_chan base vals 0) = 102%nat)
    by (unfold ga_chan, ga_row; rewrite !length_app, !length_GA; reflexivity).
  assert (L3 : length HEAD_MARK34 = 34%nat) by reflexivity. assert (L4 : length GBall = 204%nat) by reflexivity.
  rewrite L1, L2, L3, L4. lia.
Qed.
Lemma h1_gaz_row : forall c p, 0 <= c -> 0 <= p < 3 -> base + c < 256 ->
  map bv_unsigned (ga_row base vals (Z.to_nat c) (Z.to_nat p)) = GAz (base + c) p (vz vals (Z.to_nat (3 * c + p))).
Proof.
  intros c p Hc Hp Hb. rewrite <- bgs_ga_row_eq by lia. unfold GA. apply map_unsigned_bl.
  apply GA_bytes_range; [lia | lia | apply vz_range].
Qed.
Lemma prefix_step : forall c, 1 <= c -> base + c < 256 ->
  ((prefixZ c ++ GAz (base + c) 0 (vz vals (Z.to_nat (3 * c + 0)))) ++ GAz (base + c) 1 (vz vals (Z.to_nat (3 * c + 1))))
  ++ GAz (base + c) 2 (vz vals (Z.to_nat (3 * c + 2))) = prefixZ (c + 1).
Proof.
  intros c Hc Hb. unfold prefixZ. replace (Z.to_nat (c + 1)) with (Datatypes.S (Z.to_nat c)) by lia.
  rewrite <- bgs_prefixB_step by lia. rewrite !map_app.
  rewrite <- (h1_gaz_row c 0), <- (h1_gaz_row c 1), <- (h1_gaz_row c 2) by lia. reflexivity.
Qed.
Lemma prefix_one :
  ((((((prefix3 ++ HEAD_MARK34z) ++ GBz 0) ++ GBz 1) ++ GBz 2) ++ GBz 3) ++ GBz 4) ++ GBz 5 = prefixZ 1.
Proof.
  unfold prefixZ, prefix3. change (Z.to_nat 1) with 1%nat. rewrite bgs_prefixB1 by lia. rewrite !map_app.
  unfold HEAD_ACK34, HEAD_MARK34, GBall, GA.
  rewrite !map_unsigned_bl.
  1: { unfold GBallz. rewrite <- !app_assoc. reflexivity. }
  all: first [ apply GA_bytes_range; [lia | lia | apply vz_range]
             | unfold HEAD_ACK34z, HEAD_MARK34z, GBallz, GBz, gb_tail; cbn; repeat constructor; lia ].
Qed.
Lemma prefix_sweep : map bv_unsigned (SWEEP base (Z.to_nat w) vals) = prefixZ w.
Proof. unfold prefixZ. rewrite bgs_prefixB_SWEEP. reflexivity. Qed.

(* ---- H2: the calls, from one invariant to the next ---------------------------------------------------- *)
(* ---- piece rt: helpers of call_ss / call_memset / call_cpy ------------------------------------------------ *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma rt_apresent_of_aview : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> aview SEGS H m a <> None -> apresent H m a.
Proof.
intros H m a Ha Hn Hv. unfold apresent. unfold aview, mbyte, mrestrict in Hv.
pose proof (seg_rom_none SEGS a Ha Hn) as Hr. rewrite Hr in Hv.
revert Hv. destruct (H (Z_to_bv 64 a)); intros Hv; [exfalso; apply Hv; reflexivity|].
split; [reflexivity|]. revert Hv. destruct (m (Z_to_bv 64 a)) as [b|]; intros Hv;
[exists b; reflexivity | exfalso; apply Hv; reflexivity].
Qed.
(* the journal rule of a call to __asan_set_shadow_XX over a range of one of the journal's own frames' shadow *)
Lemma rt_aj_set_shadow_at : forall pc v, SetShadowDef.aset_shadow_realizes SEGS B pc v ->
  forall W1 regsT memT STK1 sp01 FP1 ly1 S1 W01 m01 d01 own1 lyc1 Sc1 mdc1 k1 cid pos q n (o : Z) raw,
  ajournal SEGS B STK1 sp01 FP1 ly1 S1 W01 m01 d01 own1 lyc1 Sc1 W1 memT mdc1 k1 ->
  In (cid, pos) own1 ->
  getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
  shadow_addr (frame_addr lyc1 cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc1 cid pos) + fs_frame_bytes cid / 8 ->
  spZ regsT = sp01 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK1 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr SEGS W1 (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc1)
  (fun W3 c3 => W3 = W1 /\ exists regs3 mem3 md3,
     c3 = mkCfg (mkst regs3 raw mem3 (seg_rom SEGS)) md3 /\
     ajournal SEGS B STK1 sp01 FP1 ly1 S1 W01 m01 d01 own1 lyc1 Sc1 W1 mem3 md3 k1 /\
     aregs_preserved regsT regs3 /\
     (forall i, 0 <= i < n -> aview SEGS (w_H W1) mem3 (q + i) = Some v) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) memT a) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> apresent (w_H W1) memT a -> apresent (w_H W1) mem3 a)).
Proof.
intros pc v SSR W1 regsT memT STK1 sp01 FP1 ly1 S1 W01 m01 d01 own1 lyc1 Sc1 mdc1 k1 cid pos q n o raw
  HJ Hin Ha0 Ha1 Hn Hq1 Hq2 Hsp' Hal Hneg Hbud Hgp1 Htp1 Hra1 Hraw1.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
pose proof Hstatic as (Hal160 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HPRE : ecall_pre SEGS B lyc1 Sc1 W1 regsT memT mdc1).
{ eapply (ecall_pre_at SEGS B STK1 sp01 FP1 ly1 S1 W01 m01 d01 own1 lyc1 Sc1 W1 memT mdc1 k1 regsT o); try eassumption.
  rewrite Hra1. exact Hraw1. }
assert (HinS : In (cid, pos) (frames Sc1)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
destruct (frames_bounds SEGS B LAWS lyc1 Sc1 W1 memT mdc1 cid pos HAR HinS) as (Hf0 & Hfc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc1 cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc1 cid pos) (fs_frame_bytes cid) Hfb0) as Hse.
assert (Hqhi : q + n < alloc_ceiling) by lia.
eapply SRr_mono.
{ exact (SSR lyc1 Sc1 W1 regsT memT mdc1 cid pos q n HPRE HinS Ha0 Ha1 Hn Hq1 Hq2). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & HP & Hsame & Heff & Hout & _).
split; [reflexivity|]. exists regs3, mem3, md3.
split; [unfold cfg_at, raZ; rewrite Hra1; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> apresent (w_H W1) memT a -> apresent (w_H W1) mem3 a).
{ intros a Ha Hni Hp. destruct (Z_lt_ge_dec a q) as [Hlo | Hlo]; [|destruct (Z_lt_ge_dec a (q + n)) as [Hhi | Hhi]].
  - apply (apresent_transfer SEGS (w_H W1) (w_H W1) memT mem3 a Ha Hni); [apply Hout; [exact Ha | lia] | exact Hp].
  - apply rt_apresent_of_aview; [exact Ha | exact Hni |]. replace a with (q + (a - q)) by lia.
    rewrite Heff by lia. discriminate.
  - apply (apresent_transfer SEGS (w_H W1) (w_H W1) memT mem3 a Ha Hni); [apply Hout; [exact Ha | lia] | exact Hp]. }
split.
{ eapply (ajournal_after_write_win SEGS B LAWS pa_segs_low STK1 sp01 FP1 ly1 S1 W01 m01 d01 own1 lyc1 Sc1 W1 memT mdc1 k1
    mem3 md3 (fun a => q <= a < q + n) Sc1 own1 HJ).
  - intros a Ha Hna. exact (Hout a Ha Hna).
  - intros a Ha Hp. apply Hkeep; [lia | intros Hi; pose proof (pa_segs_low a Hi); lia | exact Hp].
  - exact Hsame.
  - intros a Ha. left. unfold awr_byte, in_frames. right; right; right. exists cid, pos.
    split; [exact Hin | right; unfold in_zr; cbn [fst snd]; lia].
  - exact HAR3.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split; [exact Heff|]. split; [exact Hout | exact Hkeep].
Qed.
Lemma rt_saved_off : forall o r, In (o, r) SAVED -> 152 <= o /\ o + 8 <= 256.
Proof.
intros o r H. unfold SAVED in H.
repeat (destruct H as [H | H]; [injection H as <- <-; lia |]). destruct H.
Qed.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* a step that changes only this call's window and F's own bytes, and keeps the saved registers, loc0, F's flag
   pointer, the rows and the presence above alloc_ceiling, keeps the invariant with the same E *)
Lemma rt_binv_keep : forall fpos E W2 ly2 S2 mem2 md2 rows mem3 md3,
  binv fpos E W2 ly2 S2 mem2 md2 rows ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((6, fpos) :: own) ly2 S2 W2 mem3 md3 k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STKB <= a < spZ regs) -> ~ own6 fpos a ->
     aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, spZ regs - 104 <= a < spZ regs -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, sp1 + 0x60 <= a < sp1 + 0x80 -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, Fa fpos + 4088 <= a < Fa fpos + 4096 -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, s <= a < s + Z.of_nat (length rows) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  binv fpos E W2 ly2 S2 mem3 md3 rows.
Proof.
intros fpos E W2 ly2 S2 mem2 md2 rows mem3 md3 HI HJ3 Hout Hsave Hloc Hflag Hrows Hpres.
pose proof HI as (HJ & Hfr & Hbl & Hf & HKe & Hsv & Hl0 & Hfl & Hrw).
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
destruct (binv_frame _ _ _ _ _ _ _ _ HI) as (_ & _ & _ & _ & _ & _ & _ & _ & HOK6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKB : STKB = 4624) by reflexivity.
pose proof (proj1 HJc) as HARc.
split; [exact HJ3|]. split; [exact Hfr|]. split; [exact Hbl|]. split; [exact Hf|].
destruct HKe as (K1 & K2 & K3 & K4 & K5 & K6).
split; [split; [|split; [|split; [|split; [|split]]]]|].
- intros a Ha Hw HE.
  rewrite Hout; [exact (K1 a Ha Hw HE) | lia | exact Hw | intros X; destruct (HOK6 a X) as (Hc & _); lia].
- intros b m i Hin Hi HE.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hin) as (_ & Hb4096 & Hbceil & _).
  rewrite Hout; [exact (K2 b m i Hin Hi HE) | lia | lia |].
  intros X. exact (proj1 (proj2 (proj2 (HOK6 _ X))) b m i Hin Hi eq_refl).
- intros a Hi Hns He. pose proof (pa_img_range a Hi) as HIa. rewrite IMG_LO_B_val, IMG_TOP_B_val in HIa.
  rewrite Hout; [exact (K3 a Hi Hns He) | lia | lia |]. intros X. exact (proj1 (proj2 (HOK6 a X)) Hi).
- intros cid pos a Hin Hr HE.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hin) as (Hf0 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
  pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb1.
  pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfb0) as Hse.
  assert (Hrng : frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid \/
    shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8)
    by (unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr; exact Hr).
  rewrite Hout; [exact (K4 cid pos a Hin Hr HE) | clear Hr; destruct Hrng as [Hq | Hq]; lia
    | clear Hr; destruct Hrng as [Hq | Hq]; lia |].
  intros X. destruct (proj2 (proj2 (proj2 (HOK6 a X))) cid pos Hin) as [N1 N2].
  destruct Hr as [Hr | Hr]; [exact (N1 Hr) | exact (N2 Hr)].
- intros a Ha Hw Hp. apply Hpres; [lia | exact (K5 a Ha Hw Hp)].
- intros a Ha. pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP3 & _). apply HP3. lia.
- split; [|split; [|split]].
  + unfold bgs_saved in *. apply Forall_forall. intros [o r] Hin.
    pose proof (proj1 (Forall_forall _ _) Hsv _ Hin) as Hv. pose proof (rt_saved_off o r Hin) as Ho.
    cbn [fst snd] in Hv |- *.
    eapply (val_mem_aview_kept_x SEGS (w_H W2) (w_H W2) mem2 mem3); [|exact Hv].
    intros x Hx. apply Hsave. change (Z.of_nat 8) with 8 in Hx. lia.
  + destruct Hl0 as (L1 & L2 & L3 & L4).
    split; [|split; [|split]]; eapply (val_mem_aview_kept_x SEGS (w_H W2) (w_H W2) mem2 mem3); try eassumption;
    intros x Hx; apply Hloc; change (Z.of_nat 8) with 8 in Hx; lia.
  + rewrite (rdword_ext (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3) (Fa fpos + 4088)); [exact Hfl|].
    intros i Hi. apply Hflag. lia.
  + eapply (garr8_aview_kept SEGS (w_H W2) (w_H W2) mem2 mem3); [|exact Hrw]. exact Hrows.
Qed.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma rt_awr_lift : forall l1 l2 bl0 blc c a, (forall c' p, frame_addr l1 c' p = frame_addr l2 c' p) ->
  awr_byte STK sp0 FP bl0 blc l1 own a -> awr_byte STK sp0 FP bl0 blc l2 (c :: own) a.
Proof.
intros l1 l2 bl0 blc c a EF [H|[H|[H|(cid & pos & Hin & H)]]];
[left; exact H | right; left; exact H | right; right; left; exact H|].
right; right; right. exists cid, pos. rewrite <- !EF. split; [right; exact Hin | exact H].
Qed.
(* __asan_set_shadow_00 / _f8 over a range of F's shadow *)
Lemma call_ss : forall fpos E v pc W2 ly2 S2 mem2 md2 rows (regsT : bvmap 5 word) ret q n Q,
  SetShadowDef.aset_shadow_realizes SEGS B pc v ->
  binv fpos E W2 ly2 S2 mem2 md2 rows ->
  (rows = [] \/ bgs_ok s V mx base w /\ Z.of_nat (length rows) <= 34 * bgs_rows w) ->
  getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n -> SHa fpos <= q -> q + n <= SHa fpos + 512 ->
  spZ regsT = sp1 -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall mem3 md3 regs3, binv fpos E W2 ly2 S2 mem3 md3 rows ->
     (forall i, 0 <= i < n -> aview SEGS (w_H W2) mem3 (q + i) = Some v) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
     aregs_preserved regsT regs3 ->
     SRr SEGS W2 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + ret)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W2 (mkCfg (mkst regsT (Z_to_bv 64 pc) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros fpos E v pc W2 ly2 S2 mem2 md2 rows regsT ret q n Q SSR HI Hrw0 H10' H11' Hn Hq1 Hq2 Hsp H3 H4 H1 Hret Hret2 HK.
pose proof HI as (HJ & Hfr & Hbl & Hf & HKe & Hsv & Hl0 & Hfl & Hrw).
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof sp1_facts as (P1 & P2 & P3).
destruct (binv_frame _ _ _ _ _ _ _ _ HI) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & HOK6).
destruct (binv_layout _ _ _ _ _ _ _ _ HI) as (Elo & Ehi & Etop & EF & EFL).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKB : STKB = 4624) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hfb : fs_frame_bytes 6 = 4096) by reflexivity.
assert (HSHv : SHa fpos = 0x7fff8000 + Fa fpos / 8) by reflexivity.
assert (HSH : shadow_addr (frame_addr ly2 6 fpos) = SHa fpos) by (rewrite EF; reflexivity).
assert (HFH : SHa fpos + 512 < alloc_ceiling) by lia.
eapply SRr_bind.
{ eapply (rt_aj_set_shadow_at pc v SSR W2 regsT mem2 STK sp0 FP ly S W0 mem0 md0 ((6, fpos) :: own) ly2 S2 md2 k
    6 fpos q n (sp1 - sp0) (Z_to_bv 64 (BASE + ret)) HJ ltac:(left; reflexivity) H10' H11' Hn).
  - rewrite HSH. exact Hq1.
  - rewrite HSH, Hfb. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact H3.
  - exact H4.
  - exact H1.
  - apply ret_ok_codeptr_v; [lia | exact Hret2]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Heff & Hout & Hpres3).
apply (HK mem3 md3 regs3); [| exact Heff | exact Hout | exact Hpres3 | exact HP3].
apply (rt_binv_keep fpos E W2 ly2 S2 mem2 md2 rows mem3 md3 HI HJ3).
- intros a Ha _ Hno. apply Hout; [exact Ha|]. intros Hq. apply Hno. unfold own6. right; left. lia.
- intros a Ha. apply Hout; lia.
- intros a Ha. apply Hout; lia.
- intros a Ha. apply Hout; [lia|]. unfold amem_range in F6. destruct F6 as [F6 | F6]; lia.
- intros a Ha. destruct Hrw0 as [-> | [HOK Hlen]]; [cbn [length Z.of_nat] in Ha; lia|].
  destruct (HROWS HOK) as (_ & R47 & _ & _ & _ & _ & (b & m & Hbm & Hb1 & Hb2) & _).
  apply Hout; [lia|]. intros Hq.
  apply (proj1 (proj2 (proj2 (HOK6 a ltac:(unfold own6; right; left; lia)))) b m (a - b) Hbm); lia.
- intros a Ha Hp. apply Hpres3; [lia | | exact Hp].
  intros Hi. pose proof (pa_img_range a Hi) as HIa. rewrite IMG_LO_B_val, IMG_TOP_B_val in HIa. lia.
Qed.
(* __asan_memset (F + X, 0, 1492) over a scratch *)
Lemma call_memset : forall fpos W2 ly2 S2 mem2 md2 rows (regsT : bvmap 5 word) ret X Q,
  bgs_ok s V mx base w -> Z.of_nat (length rows) <= 34 * bgs_rows w ->
  binv fpos RowsE W2 ly2 S2 mem2 md2 rows -> (X = 32 \/ X = 1664) ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (Fa fpos + X) 1492 ->
  getr regsT 10 = w64 (Fa fpos + X) -> getr regsT 11 = w64 0 -> getr regsT 12 = w64 1492 ->
  spZ regsT = sp1 -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall mem3 md3 regs3, binv fpos RowsE W2 ly2 S2 mem3 md3 rows ->
     (forall i, 0 <= i < 1492 -> aview SEGS (w_H W2) mem3 (Fa fpos + X + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (Fa fpos + X <= a < Fa fpos + X + 1492) -> ~ (sp1 - ESTACK <= a < sp1) ->
        aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
     aregs_preserved regsT regs3 ->
     SRr SEGS W2 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + ret)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W2 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA GS___asan_memset)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros fpos W2 ly2 S2 mem2 md2 rows regsT ret X Q HOK Hlen HI HX Hrad H10' H11' H12' Hsp H3 H4 H1 Hret Hret2 HK.
assert (HX' : 32 <= X <= 1664) by (destruct HX as [-> | ->]; lia).
pose proof HI as (HJ & Hfr & Hbl & Hf & HKe & Hsv & Hl0 & Hfl & Hrw).
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof sp1_facts as (P1 & P2 & P3).
destruct (binv_frame _ _ _ _ _ _ _ _ HI) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & HOK6).
destruct (binv_layout _ _ _ _ _ _ _ _ HI) as (Elo & Ehi & Etop & EF & EFL).
destruct (HROWS HOK) as (_ & R47 & _ & _ & _ & _ & (b & m & Hbm & Hb1 & Hb2) & Rwin & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKB : STKB = 4624) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hfb : fs_frame_bytes 6 = 4096) by reflexivity.
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIGMA GS___asan_memset) AMEMSET W2 regsT mem2 STK sp0 FP ly S W0
    mem0 md0 ((6, fpos) :: own) ly2 S2 md2 k (Fa fpos + X) 0 1492 (sp1 - sp0) (Z_to_bv 64 (BASE + ret)) HJ H10' H11' H12').
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact H3.
  - exact H4.
  - exact H1.
  - apply ret_ok_codeptr_v; [lia | exact Hret2].
  - intros a Ha. split.
    + unfold awr_byte, in_frames. right; right; right. exists 6, fpos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite EF, Hfb. unfold Fa in Ha. lia.
    + lia.
  - unfold amem_range. unfold amem_range in F6. destruct F6 as [F6 | F6]; [left | right]; lia.
  - exact Hrad.
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 mem2 md2 6 fpos);
    [exact (proj1 HJ) | rewrite Hfr; left; reflexivity | rewrite EF; unfold Fa; lia | rewrite EF, Hfb; unfold Fa; lia | lia].
  - exact I. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Heff & Hout & Hpres3 & _).
apply (HK mem3 md3 regs3).
- apply (rt_binv_keep fpos RowsE W2 ly2 S2 mem2 md2 rows mem3 md3 HI HJ3).
  + intros a Ha Hw Hno. apply Hout; [exact Ha | intros X1; apply Hno; unfold own6; left; lia | intros X2; apply Hw; lia].
  + intros a Ha. apply Hout; [lia | intros X1; lia | intros X2; lia].
  + intros a Ha. apply Hout; [lia | intros X1; lia | intros X2; lia].
  + intros a Ha. apply Hout; [lia | intros X1; lia | intros X2; lia].
  + intros a Ha. apply Hout; [lia | intros X1 | intros X2; destruct Rwin as [Rw1 | Rw1]; lia].
    apply (proj1 (proj2 (proj2 (HOK6 a ltac:(unfold own6; left; lia)))) b m (a - b) Hbm); lia.
  + intros a _ Hp. exact (Hpres3 a Hp).
- intros i Hi. rewrite Heff by exact Hi. reflexivity.
- intros a Ha H1' H2'. apply Hout; [exact Ha | exact H1' | intros X2; apply H2'; lia].
- exact HP3.
Qed.
(* __asan_memcpy of L (n bytes) from x into the next row s + |rows| *)
Lemma call_cpy : forall fpos W2 ly2 S2 mem2 md2 rows (regsT : bvmap 5 word) ret x (L : list Z) Q,
  bgs_ok s V mx base w ->
  binv fpos RowsE W2 ly2 S2 mem2 md2 rows ->
  0 < Z.of_nat (length L) < 2 ^ 32 -> Z.of_nat (length rows) + Z.of_nat (length L) <= 34 * bgs_rows w ->
  garr8 SEGS (mrestrict (w_H W2) mem2) x L ->
  0 <= x -> x + Z.of_nat (length L) <= 2 ^ 63 ->
  (s + Z.of_nat (length rows) + Z.of_nat (length L) <= x \/ x + Z.of_nat (length L) <= s + Z.of_nat (length rows)) ->
  amem_range x (Z.of_nat (length L)) ->
  (forall a, x <= a < x + Z.of_nat (length L) -> ~ (sp1 - ESTACK <= a < sp1)) ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF x (Z.of_nat (length L)) ->
  shadow_hull_vis (aview SEGS (w_H W2) mem2) x (Z.of_nat (length L)) ->
  getr regsT 10 = w64 (s + Z.of_nat (length rows)) -> getr regsT 11 = w64 x ->
  getr regsT 12 = w64 (Z.of_nat (length L)) ->
  spZ regsT = sp1 -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall mem3 md3 regs3, binv fpos RowsE W2 ly2 S2 mem3 md3 (rows ++ L) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (s + Z.of_nat (length rows) <= a < s + Z.of_nat (length rows) + Z.of_nat (length L)) ->
        ~ (sp1 - ESTACK <= a < sp1) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
     aregs_preserved regsT regs3 ->
     SRr SEGS W2 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + ret)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W2 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA GS___asan_memcpy)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros fpos W2 ly2 S2 mem2 md2 rows regsT ret x L Q HOK HI Hn Hlen2 HL Hx0 Hx63 Hdx Hxam Hxw Hxra Hxhl
  H10' H11' H12' Hsp H3 H4 H1 Hret Hret2 HK.
pose proof HI as (HJ & Hfr & Hbl & Hf & HKe & Hsv & Hl0 & Hfl & Hrw).
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof sp1_facts as (P1 & P2 & P3).
destruct (binv_frame _ _ _ _ _ _ _ _ HI) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & HOK6).
destruct (binv_layout _ _ _ _ _ _ _ _ HI) as (Elo & Ehi & Etop & EF & EFL).
destruct (HROWS HOK) as (Ram & R47 & Rimg & Rwr & _ & _ & (b & m & Hbm & Hb1 & Hb2) & Rwin & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKB : STKB = 4624) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hbm2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Hbl; exact Hbm).
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA GS___asan_memcpy) AMEMCPY W2 regsT mem2 STK sp0 FP ly S W0
    mem0 md0 ((6, fpos) :: own) ly2 S2 md2 k (s + Z.of_nat (length rows)) x (Z.of_nat (length L)) (sp1 - sp0)
    (Z_to_bv 64 (BASE + ret)) HJ H10' H11' H12').
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact H3.
  - exact H4.
  - exact H1.
  - apply ret_ok_codeptr_v; [lia | exact Hret2].
  - intros a Ha. destruct (Rwr a ltac:(lia)) as (Haw & _ & _ & _). split; [|destruct Rwin as [Rw1 | Rw1]; lia].
    rewrite Hbl. exact (rt_awr_lift lyc ly2 _ _ (6, fpos) a (fun c p => eq_sym (EF c p)) Haw).
  - unfold amem_range. unfold amem_range in Ram. destruct Ram as [Ram | Ram]; [left | right]; lia.
  - apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 b m); [exact (proj1 HJ) | exact Hbm2 | lia | lia].
  - intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 b m);
    [exact (proj1 HJ) | exact Hbm2 | lia | lia | exact Hn0].
  - split; [exact Hx0|]. split; [exact Hx63|]. split.
    { intros a Ha. split; [|rewrite Hsp; exact (Hxw a Ha)].
      destruct (garr8_nthZ SEGS _ x L (a - x) HL ltac:(lia) ltac:(lia)) as [Hv Hvr].
      replace (x + (a - x)) with a in Hv by lia. eapply aview_of_val_mem1 in Hv; [| exact Hvr]. rewrite Hv. discriminate. }
    split; [exact Hdx|]. split; [exact Hxam|]. split; [exact Hxra | intros _; exact Hxhl]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Heff & Hout & Hpres3 & _).
apply (HK mem3 md3 regs3); [| intros a Ha H1' H2'; apply Hout; [exact Ha | exact H1' | intros X2; apply H2'; lia] | exact HP3].
assert (HI3 : binv fpos RowsE W2 ly2 S2 mem3 md3 rows).
{ apply (binv_kept fpos RowsE RowsE W2 ly2 S2 mem2 md2 rows mem3 md3 HI HJ3).
  - intros a Ha. exact Ha.
  - intros a Ha Hi. pose proof (pa_img_range a Hi) as HIa. unfold RowsE in Ha.
    rewrite IMG_LO_B_val, IMG_TOP_B_val in HIa, Rimg. destruct Rimg as [Ri | Ri]; lia.
  - intros a Ha Hw HE _. apply Hout; [exact Ha | intros X1; apply HE; unfold RowsE; lia | intros X2; apply Hw; lia].
  - intros a Ha. apply Hout; [lia | intros X1; destruct Rwin as [Rw1 | Rw1]; lia | intros X2; lia].
  - intros a Ha. apply Hout; [lia | intros X1; destruct Rwin as [Rw1 | Rw1]; lia | intros X2; lia].
  - intros a Ha. apply Hout; [lia | intros X1 | intros X2; lia].
    apply (proj1 (proj2 (proj2 (HOK6 a ltac:(unfold own6; left; lia)))) b m (a - b) Hbm); lia.
  - intros a Ha. apply Hout; [lia | intros X1; lia | intros X2; destruct Rwin as [Rw1 | Rw1]; lia].
  - intros a _ Hp. exact (Hpres3 a Hp). }
destruct HI3 as (HJ4 & Hfr4 & Hbl4 & Hf4 & HK4 & Hsv4 & Hl04 & Hfl4 & Hrw4).
split; [exact HJ4|]. split; [exact Hfr4|]. split; [exact Hbl4|]. split; [exact Hf4|]. split; [exact HK4|].
split; [exact Hsv4|]. split; [exact Hl04|]. split; [exact Hfl4|].
apply garr8_app. split; [exact Hrw4|].
apply (garr8_aview SEGS (w_H W2) (w_H W2) mem2 mem3 x (s + Z.of_nat (length rows)) L); [|exact HL].
intros i Hi. rewrite Heff by lia. reflexivity.
Qed.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* reac_ctrl_stamp_headamp (F + X, ch, pm, v) on a scratch whose [16, 50) has shadow 0 *)
(* piece st: helpers of call_stamp *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma st_mod16_of_32 : forall z, z mod 32 = 0 -> z mod 16 = 0.
Proof. intros z H. clear - H. lia. Qed.
Lemma st_mod8_of_16 : forall z, z mod 16 = 0 -> z mod 8 = 0.
Proof. intros z H. clear - H. lia. Qed.
(* F's shadow (SBV + F / 8, 512 bytes) lies outside F when F is application memory *)
Lemma st_sh_apart : forall F a, amem_range F 4096 -> 4096 <= F -> SBV + F / 8 <= a < SBV + F / 8 + 512 ->
  a < F \/ F + 4096 <= a.
Proof.
intros F a HF H0 Ha. clear - HF H0 Ha.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HF. unfold SBV in Ha. lia.
Qed.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma st_bv64_range : forall x : bv 64, 0 <= bv_unsigned x < 2 ^ 64.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H. Qed.
Definition st_imgP (p : Z) : Prop := p + 50 <= IMG_LO_B \/ IMG_TOP_B <= p + 16.
Lemma st_saved_off : forall o r, In (o, r) SAVED -> 152 <= o <= 248.
Proof. intros o r H. clear - H. unfold SAVED in H. repeat (destruct H as [H|H]; [inversion H; lia|]). destruct H. Qed.
(* image A's tcj_compose (CtrlStampHeadamp.v), where the callee may also write bytes of an own_ok set Q *)
Lemma st_tcj_compose_own : forall Kc Kq ly' S' (Wc W1 W2 : world SEGS) (mc m1 m2 : word -> option byte) sp sp'
  (E E' Q : Z -> Prop),
  tcj_kept B Kc lyc Sc Wc mc W1 m1 sp E ->
  tcj_kept B Kq ly' S' W1 m1 W2 m2 sp' E' ->
  sp - Kc <= sp' - Kq -> sp' <= sp -> alloc_ceiling <= sp - Kc -> sp <= 2 ^ 64 ->
  (forall a, E' a -> E a \/ Q a) -> own_ok Q ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly' S')) ->
  (forall f, In f (frames Sc) -> In f (frames S')) ->
  (forall c q, frame_addr ly' c q = frame_addr lyc c q) ->
  tcj_kept B Kc lyc Sc Wc mc W2 m2 sp E.
Proof.
intros Kc Kq ly' S' Wc W1 W2 mc m1 m2 sp sp' E E' Q
  (T1 & T2 & T3 & T4 & T5 & T6) (U1 & U2 & U3 & U4 & U5 & U6) H1 H2 H3 H4 HE HQ Hb Hf Hfa.
clear - T1 T2 T3 T4 T5 T6 U1 U2 U3 U4 U5 U6 H1 H2 H3 H4 HE HQ Hb Hf Hfa.
split.
{ intros a Ha Hw He. rewrite (U1 a Ha); [exact (T1 a Ha Hw He) | lia |].
  intros H'. destruct (HE a H') as [H|H]; [exact (He H)|]. destruct (HQ a H) as (Hl & _). lia. }
split.
{ intros b m i Hin Hi He. rewrite (U2 b m i (Hb _ Hin) Hi); [exact (T2 b m i Hin Hi He)|].
  intros H'. destruct (HE _ H') as [H|H]; [exact (He H)|].
  destruct (HQ _ H) as (_ & _ & Hbl & _). exact (Hbl b m i Hin Hi eq_refl). }
split.
{ intros a Hi Ho Her. rewrite (U3 a Hi Ho Her). exact (T3 a Hi Ho Her). }
split.
{ intros cid pos a Hin Hz He. rewrite (U4 cid pos a (Hf _ Hin)).
  - exact (T4 cid pos a Hin Hz He).
  - unfold frame_rng in *. cbn [fst snd] in *. rewrite !Hfa. exact Hz.
  - intros H'. destruct (HE a H') as [H|H]; [exact (He H)|].
    destruct (HQ a H) as (_ & _ & _ & Hfr). destruct (Hfr cid pos Hin) as [N1 N2].
    destruct Hz as [Hz|Hz]; [exact (N1 Hz) | exact (N2 Hz)]. }
split.
{ intros a Ha Hw Hp. apply (U5 a Ha); [lia | exact (T5 a Ha Hw Hp)]. }
intros a Ha. destruct (Z_le_gt_dec (sp' - Kq) a) as [Hl|Hl]; [destruct (Z_lt_ge_dec a sp') as [Hh|Hh]|].
- exact (U6 a (conj Hl Hh)).
- apply (U5 a); [lia | lia | exact (T6 a Ha)].
- apply (U5 a); [lia | lia | exact (T6 a Ha)].
Qed.
Lemma call_stamp : forall fpos W2 ly2 S2 mem2 md2 rows (regsT : bvmap 5 word) ret X ch pm v Q,
  bgs_ok s V mx base w ->
  binv fpos RowsE W2 ly2 S2 mem2 md2 rows -> (X = 32 \/ X = 1664) -> Z.of_nat (length rows) <= 34 * bgs_rows w ->
  (forall x, Fa fpos + X + 16 <= x < Fa fpos + X + 50 -> aview SEGS (w_H W2) mem2 (shadow_addr x) = Some 0) ->
  getr regsT 10 = w64 (Fa fpos + X) -> getr regsT 11 = w64 ch -> getr regsT 12 = w64 pm -> getr regsT 13 = w64 v ->
  0 <= ch < 256 -> 0 <= pm < 256 -> 0 <= v < 256 -> legalb pm v = true ->
  spZ regsT = sp1 -> getr regsT 8 = w64 (spZ regs) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  (forall W3 ly3 S3 mem3 md3 regs3, binv fpos RowsE W3 ly3 S3 mem3 md3 rows ->
     (forall a, sp1 <= a < spZ regs -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
     (forall a, SHa fpos <= a < SHa fpos + 512 -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
     (forall a, Fa fpos <= a < Fa fpos + 4096 -> ~ (Fa fpos + X + 16 <= a < Fa fpos + X + 50) ->
        aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
     aregs_preserved regsT regs3 -> getr regs3 10 = w64 0 ->
     garr8 SEGS (mrestrict (w_H W3) mem3) (Fa fpos + X + 16) (GAz ch pm v) ->
     SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + ret)) mem3 (seg_rom SEGS)) md3) Q) ->
  SRr SEGS W2 (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_reac_ctrl_stamp_headamp)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros fpos W2 ly2 S2 mem2 md2 rows regsT ret X ch pm v Q HOK HI HX Hlen Hsh0 H10' H11' H12' H13' Rch Rpm Rv Hleg
  Hsp H8' H3 H4 H1 Hret Hret2 HK.
pose proof HI as (HJ & Hfr & Hbl & Hfs & HKe & Hsv & Hl0 & Hflp & Hrw).
pose proof (arod_binv _ _ _ _ _ _ _ _ HI) as Harod.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop0 & _).
destruct Hastk as (_ & _ & _ & _ & _ & _ & _ & _ & Htop1).
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof sp1_facts as (P1 & P2 & P3).
destruct (binv_frame _ _ _ _ _ _ _ _ HI) as (Fal & F4 & Fce & Fimg & F47 & Fam & Fpr & Spr & Hown).
destruct (binv_layout _ _ _ _ _ _ _ _ HI) as (Elo & Ehi & Etop & EF & EFL).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_ctrl_build_grant_sweep = 272 + STK_reac_ctrl_stamp_headamp) by reflexivity.
assert (WS2 : STK_reac_ctrl_stamp_headamp = 4352) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hfb6 : fs_frame_bytes 6 = 4096) by reflexivity.
pose proof pa_base_lo as HBLO. rewrite IMG_LO_B_val in HBLO. pose proof pa_B_ok as HBASE.
destruct (HROWS HOK) as (_ & _ & _ & _ & _ & _ & (b & m & Hbm & Hb1 & Hb2) & _ & _).
assert (Hbm2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Hbl; exact Hbm).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hbm2) as (_ & Hb4096 & Hbceil & _).
(* the disjunctive facts, used once each, then dropped so that lia does not split on them *)
assert (HXb : 32 <= X <= 1664) by (clear - HX; lia).
assert (Himg : st_imgP (Fa fpos + X)) by (unfold st_imgP; clear - Fimg HXb; lia).
assert (Ham : amem_range (Fa fpos + X + 16) 34) by (clear - Fam HXb; unfold amem_range in *; lia).
assert (Hshd : forall a, SHa fpos <= a < SHa fpos + 512 -> a < Fa fpos \/ Fa fpos + 4096 <= a)
  by (intros a Ha; exact (st_sh_apart (Fa fpos) a Fam F4 Ha)).
clear HX Fimg HVALS HROWS Rmx Rbase Rw RV Hbw31.
assert (Hs0T : s0Z regsT = spZ regs).
{ unfold s0Z. rewrite H8'. unfold w64. apply unsigned_lit_small. lia. }
(* the stamp's frame chain: this call's frame record (SP, ra, s0) on top of the caller's chain *)
assert (Hch2 : exists cl', achain ly2 (aview SEGS (w_H W2) mem2) sp1 (spZ regs) cl').
{ destruct (Z_lt_ge_dec (spZ regs) (ly_top ly2 - 16)) as [Htl|Htl].
  - exists ((spZ regs, raZ regs, s0Z regs) :: cl).
    assert (Hv1 : val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs - 8) 8 (raZ regs)).
    { pose proof (proj1 (Forall_forall _ _) Hsv (248, 1%nat) ltac:(unfold SAVED; left; reflexivity)) as Hv.
      cbn [fst snd] in Hv. replace (spZ regs - 8) with (spZ regs - 256 + 248) by lia. exact Hv. }
    assert (Hv8 : val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs - 16) 8 (s0Z regs)).
    { pose proof (proj1 (Forall_forall _ _) Hsv (240, 8%nat) ltac:(unfold SAVED; right; left; reflexivity)) as Hv.
      cbn [fst snd] in Hv. replace (spZ regs - 16) with (spZ regs - 256 + 240) by lia. exact Hv. }
    apply (achain_push ly2 (aview SEGS (w_H W) memc) (aview SEGS (w_H W2) mem2) (spZ regs) (s0Z regs) (raZ regs) cl sp1).
    + exact (achain_ly_top lyc ly2 _ _ _ _ Etop Hch).
    + lia.
    + intros a Ha. destruct HKe as (K1 & _). apply K1; [lia | lia | unfold RowsE; lia].
    + apply rdword_of_val_mem; [exact Hv1 | unfold raZ; apply st_bv64_range].
    + apply rdword_of_val_mem; [exact Hv8 | unfold s0Z; apply st_bv64_range].
    + exact Hra4.
    + lia.
    + apply st_mod8_of_16. exact Hal16.
    + exact Htl.
    + lia.
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct Hch2 as (cl' & Hch2).
eapply SRr_bind.
{ change (Z_to_bv 64 (BASE + AF_reac_ctrl_stamp_headamp)) with (w64 (BASE + AF_reac_ctrl_stamp_headamp)).
  apply (TSTAMP STK sp0 FP ly S W0 mem0 md0 ((6, fpos) :: own) ly2 S2 W2 mem2 md2 k regsT (Fa fpos + X) ch pm v 6 fpos
    cl' HJ).
  - exact Harod.
  - rewrite H1. apply ret_ok_codeptr_v; [lia | exact Hret2].
  - unfold raZ. rewrite H1, unsigned_lit_small by lia. lia.
  - exact H3. - exact H4. - exact H10'. - exact H11'. - exact H12'. - exact H13'.
  - exact Rch. - exact Rpm. - exact Rv.
  - rewrite Hs0T, Hsp. exact Hch2.
  - rewrite Hsp. exact (st_mod16_of_32 _ P1).
  - rewrite Hsp. lia.
  - rewrite Hsp. lia.
  - rewrite Hfr. cbn [length]. lia.
  - lia. - lia. - lia.
  - exact Ham.
  - exact Himg.
  - rewrite Hfr. left. reflexivity.
  - rewrite EF. change (frame_addr lyc 6 fpos) with (Fa fpos). lia.
  - rewrite EF, Hfb6. change (frame_addr lyc 6 fpos) with (Fa fpos). lia.
  - exact Hsh0.
  - right. rewrite Hsp. lia.
  - intros _ a Ha. destruct (Fpr a ltac:(lia)) as (Hpa & Hna).
    split; [|split; [exact Hpa | split; [exact Hna | rewrite Hsp; lia]]].
    right. right. right. exists 6, fpos. split; [left; reflexivity | left].
    unfold in_zr. cbn [fst snd]. rewrite EF, Hfb6. change (frame_addr lyc 6 fpos) with (Fa fpos). lia. }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & res & -> & HJ3 & HP3 & Hfr3 & Hbl3 & Hfs3 & Hres & HK3 & Hcase).
rewrite Hleg in Hcase. destruct Hcase as (-> & Hga).
rewrite H1. rewrite Hsp in HK3.
pose proof HK3 as (U1 & U2 & U3 & U4 & U5 & U6). cbv beta in U1, U2, U4.
(* what the stamp keeps of its caller: the machine frame above sp1, F's shadow, F outside [X + 16, X + 50) *)
assert (KS : forall a, sp1 <= a < spZ regs -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply U1; lia. }
assert (KF : forall a, Fa fpos <= a < Fa fpos + 4096 -> ~ (Fa fpos + X + 16 <= a < Fa fpos + X + 50) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn. apply (U4 6 fpos a); [rewrite Hfr; left; reflexivity | left | exact Hn].
  unfold frame_rng, in_zr. cbn [fst snd]. rewrite EF, Hfb6. change (frame_addr lyc 6 fpos) with (Fa fpos). lia. }
assert (KSh : forall a, SHa fpos <= a < SHa fpos + 512 -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. pose proof (Hshd a Ha) as Hd.
  apply (U4 6 fpos a); [rewrite Hfr; left; reflexivity | right | clear - Hd HXb; lia].
  unfold in_zr. cbn [fst snd]. rewrite EF, Hfb6. change (frame_addr lyc 6 fpos) with (Fa fpos).
  change (4096 / 8) with 512. exact Ha. }
apply (HK W3 ly3 S3 mem3 md3 regs3); [| exact KS | exact KSh | exact KF | exact HP3 | exact Hres | exact Hga].
split; [exact HJ3|].
split; [rewrite Hfr3; exact Hfr|].
split; [rewrite Hbl3; exact Hbl|].
split; [destruct Hfs3 as (f3 & ->); destruct Hfs as (f & ->); exists f3; reflexivity|].
split.
{ apply (st_tcj_compose_own STK_reac_ctrl_build_grant_sweep STK_reac_ctrl_stamp_headamp ly2 S2 W W2 W3 memc mem2 mem3
    (spZ regs) sp1 RowsE (fun a => Fa fpos + X + 16 <= a < Fa fpos + X + 50) (own6 fpos) HKe HK3).
  - lia. - lia. - lia. - lia.
  - intros a Ha. cbv beta in Ha. right. unfold own6. left. lia.
  - exact Hown.
  - intros bm Hin. rewrite Hbl. exact Hin.
  - intros f Hin. rewrite Hfr. right. exact Hin.
  - exact EF. }
split.
{ unfold bgs_saved in Hsv |- *. apply Forall_forall. intros [o r] Hin.
  pose proof (proj1 (Forall_forall _ _) Hsv _ Hin) as Hv. pose proof (st_saved_off o r Hin) as Ho.
  cbn [fst snd] in Hv, Ho |- *.
  eapply (val_mem_aview_kept_x SEGS (w_H W2) (w_H W3) mem2 mem3); [|exact Hv].
  intros xx Hx. apply KS. lia. }
split.
{ destruct Hl0 as (L1 & L2 & L3 & L4).
  split; [|split; [|split]]; eapply (val_mem_aview_kept_x SEGS (w_H W2) (w_H W3) mem2 mem3);
  [intros xx Hx; apply KS; lia | exact L1 | intros xx Hx; apply KS; lia | exact L2
  | intros xx Hx; apply KS; lia | exact L3 | intros xx Hx; apply KS; lia | exact L4]. }
split.
{ rewrite <- Hflp. apply rdword_ext. intros kk Hkk. apply KF; lia. }
eapply (garr8_aview_kept SEGS (w_H W2) (w_H W3) mem2 mem3); [|exact Hrw].
intros a Ha. replace a with (b + (a - b)) by lia. apply (U2 b m (a - b) Hbm2); [lia|].
intros HE'. destruct (Hown (b + (a - b)) ltac:(unfold own6; left; lia)) as (_ & _ & Hb' & _).
exact (Hb' b m (a - b) Hbm ltac:(lia) eq_refl).
Qed.

(* ---- S6: the release of F and the return (0x83b80 .. 0x83bf0) ----------------------------------------- *)
(* ep: the state at 0x83b80, fresh from eregs: F's first word (s8, atom 24) is writable for the retired magic; the
   facts on s2 / s8 (atoms 18 / 24, F >= 4096) decide `beqz s2` (0x83b8c). No shadow check runs here, so the shadow
   span is empty and F's window is apart from it. *)
Definition ep_ss1 : sstate := mkSS 0x3144 sr_atoms [YP09.mkRegion (Some 24%nat) 0 8 0 8 []] None
  (mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 0); (24%nat, mkAF 4096 (2 ^ 47) 0)] [] []).
Definition ep_Bx : sv := SOff 25 0.
Definition ep_Bspan : Z * Z := (0, 0).
Let ep_RUN := paj_run B LAWS.
Let ep_RET := paj_ret_at (PL := PL_grant) (PI := PI).
Ltac ep_winout := let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros (r & Hr & Hw); lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
  cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
    repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- _ => rewrite H in Hw end; rewrite ?unsigned_lit_small in Hw by lia; lia |]); try destruct Hr.
Lemma ep_ap_eq : forall (R1 R2 : bvmap 5 word) (r : bv 5), aregs_preserved R1 R2 -> acallee_saved (bv_unsigned r) -> getr R2 r = getr R1 r.
Proof. intros R1 R2 r HP Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
(* ep: the state at 0x83ba0, after __asan_stack_free_6, fresh from the call's registers: the caller's saved registers
   at s0 - 104 .. s0 (s0 = SP, atom 8) are the extra atoms 32 .. 44, in SAVED's order. *)
Definition ep_saved_extra : list word := map (fun p => getr regs (Z_to_bv 5 (Z.of_nat (snd p)))) SAVED.
Definition ep_ss2 : sstate := mkSS 0x3164 sr_atoms
[YP09.mkRegion (Some 8%nat) (-104) 0 0 0
 [YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk (-16) (CVal 8 (SOff 33 0)); YP09.mkChunk (-24) (CVal 8 (SOff 34 0));
  YP09.mkChunk (-32) (CVal 8 (SOff 35 0)); YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-48) (CVal 8 (SOff 37 0));
  YP09.mkChunk (-56) (CVal 8 (SOff 38 0)); YP09.mkChunk (-64) (CVal 8 (SOff 39 0)); YP09.mkChunk (-72) (CVal 8 (SOff 40 0));
  YP09.mkChunk (-80) (CVal 8 (SOff 41 0)); YP09.mkChunk (-88) (CVal 8 (SOff 42 0)); YP09.mkChunk (-96) (CVal 8 (SOff 43 0));
  YP09.mkChunk (-104) (CVal 8 (SOff 44 0))]] None (mkFacts [] [] []).
Ltac ep_cs := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?r] => let x := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with x end; lia.
Lemma ep_tcj_mono : forall W2 m2 (E1 E2 : Z -> Prop),
  tcj_kept B STKB lyc Sc W memc W2 m2 (spZ regs) E1 -> (forall a, E1 a -> E2 a) ->
  tcj_kept B STKB lyc Sc W memc W2 m2 (spZ regs) E2.
Proof.
intros W2 m2 E1 E2 (K1 & K2 & K3 & K4 & K5 & K6) HE.
split; [intros a Ha Hw He; apply K1; [exact Ha | exact Hw | intros H; exact (He (HE a H))]|].
split; [intros b m i Hb Hi He; apply (K2 b m i); [exact Hb | exact Hi | intros H; exact (He (HE _ H))]|].
split; [exact K3|].
split; [intros cid pos a Hin Hr He; apply (K4 cid pos a); [exact Hin | exact Hr | intros H; exact (He (HE a H))]|].
split; [exact K5 | exact K6].
Qed.
(* What the call keeps for its caller survives a step that changes only F's own bytes (own6) and the ESTACK window
   below sp1, and leaves that window present. *)
Lemma ep_tcj_step : forall fpos E W2 m1 m2,
  own_ok (own6 fpos) ->
  tcj_kept B STKB lyc Sc W memc W2 m1 (spZ regs) E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ own6 fpos a -> ~ (sp1 - ESTACK <= a < sp1) ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W2) m1 a) ->
  (forall a, sp1 - ESTACK <= a < sp1 -> apresent (w_H W2) m2 a) ->
  tcj_kept B STKB lyc Sc W memc W2 m2 (spZ regs) E.
Proof.
intros fpos E W2 m1 m2 HO (K1 & K2 & K3 & K4 & K5 & K6) KP HP.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof sp1_facts as (_ & Hsp1b).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs.
assert (Hes : ESTACK = 4096) by reflexivity. assert (WS : STKB = 4624) by reflexivity.
pose proof (proj1 HJc) as HAR.
assert (HNO : forall a, own6 fpos a -> a < alloc_ceiling) by (intros a Ha; exact (proj1 (HO a Ha))).
split.
{ intros a Ha Hw He. rewrite (KP a ltac:(lia)); [exact (K1 a Ha Hw He) | intros Ho; pose proof (HNO a Ho); lia | lia]. }
split.
{ intros b m i Hb Hi He. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hceil & _).
  rewrite (KP (b + i)); [exact (K2 b m i Hb Hi He) | lia | intros Ho; exact (proj1 (proj2 (proj2 (HO _ Ho))) b m i Hb Hi eq_refl) | lia]. }
split.
{ intros a Hi Hs He. pose proof (Hsegs a Hi) as Hlo.
  rewrite (KP a); [exact (K3 a Hi Hs He) | lia | intros Ho; exact (proj1 (proj2 (HO a Ho)) Hi) | lia]. }
split.
{ intros cid pos a Hin Hr He.
  destruct (YCbq.frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
  pose proof (proj2 (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) ltac:(lia)) as Hsb.
  pose proof (proj1 (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia))) as Hsb0. unfold SHADOW_OFF in Hsb0.
  assert (Ha : 0 <= a < alloc_ceiling).
  { unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. destruct Hr as [Hr | Hr]; lia. }
  rewrite (KP a); [exact (K4 cid pos a Hin Hr He) | lia | | lia].
  intros Ho. destruct (proj2 (proj2 (proj2 (HO a Ho))) cid pos Hin) as [Hn1 Hn2]. destruct Hr as [Hr | Hr]; contradiction. }
split.
{ intros a Ha Hw Hp. apply (apresent_transfer SEGS (w_H W2) (w_H W2) m1 m2 a); [lia | intros Hi; pose proof (Hsegs a Hi); lia | | exact (K5 a Ha Hw Hp)].
  apply KP; [lia | intros Ho; pose proof (HNO a Ho); lia | lia]. }
{ intros a Ha. destruct (Z_lt_ge_dec a (sp1 - ESTACK)) as [Hlo|Hlo]; [|destruct (Z_lt_ge_dec a sp1) as [Hhi|Hhi]].
  - apply (apresent_transfer SEGS (w_H W2) (w_H W2) m1 m2 a); [lia | intros Hi; pose proof (Hsegs a Hi); lia | | exact (K6 a Ha)].
    apply KP; [lia | intros Ho; pose proof (HNO a Ho); lia | lia].
  - apply HP. lia.
  - apply (apresent_transfer SEGS (w_H W2) (w_H W2) m1 m2 a); [lia | intros Hi; pose proof (Hsegs a Hi); lia | | exact (K6 a Ha)].
    apply KP; [lia | intros Ho; pose proof (HNO a Ho); lia | lia]. }
Qed.
Lemma ep_sfs : forall c q S2 S0 f, S2 = set_fs f S0 -> exists f', stack_free_state c q S2 = set_fs f' S0.
Proof. intros c q S2 S0 f ->. unfold stack_free_state. eexists. destruct S0; reflexivity. Qed.
Lemma epi : forall fpos E W2 ly2 S2 regs2 mem2 md2 rows res,
  binv fpos E W2 ly2 S2 mem2 md2 rows -> eregs fpos regs2 res ->
  (bgs_ok s V mx base w /\ res = bgs_rows w /\ rows = map bv_unsigned (SWEEP base (Z.to_nat w) vals) /\
     (forall a, E a -> RowsE a))
  \/ (~ bgs_ok s V mx base w /\ res = -1 /\ (forall a, ~ E a)) ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x3144)) mem2 (seg_rom SEGS)) md2) TBP.
Proof.
intros fpos E W2 ly2 S2 regs2 mem2 md2 rows res HI HR HC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof sp1_facts as (Hsp1a & Hsp1b).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (binv_frame _ _ _ _ _ _ _ _ HI) as (HF64 & HF4096 & HFceil & HFimg & HF47 & HFam & HFpres & HSHpres & HOWN).
pose proof (binv_layout _ _ _ _ _ _ _ _ HI) as (HL1 & HL2 & HL3 & HLF & HLFL).
pose proof HI as (HJ & Hfr & Hbl & HfS & HK & Hsv & Hl0 & HFLp & Hrw).
pose proof HR as ((R2 & R3 & R4 & R8 & R9) & R18 & R24 & R26).
remember (Eimg (Ereg regs2 [])) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (subst Ev; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ev n = getr regs2 r) by (intros n r Hn; rewrite HEv; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite R18 in E18.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite R24 in E24.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite R26 in E26.
unfold w64 in E2, E3, E4, E8, E18, E24, E26.
assert (HS : st_ok_pi SEGS VAL Ev ep_ss1 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x3144)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ep_ss1. apply pa_entry_st_ok_full.
- rewrite HEv. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E24, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply (HFpres (Fa fpos + o)). lia.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok].
  split; [|split; [|exact I]]; unfold afact_ok; cbn [af_lo af_hi af_al2]; first [rewrite E18 | rewrite E24];
  rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia. }
assert (SHOK : sh_ok SEGS ep_Bx [] Ev (mrestrict (w_H W2) mem2)) by constructor.
clear HEv EE.
paj_run_tok ep_RUN HS HJ SHOK ep_Bspan.

{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own => let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
  eapply awr_ok_cons_gen; [reflexivity | reflexivity | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. rewrite E24, unsigned_lit_small by lia. intros a Ha.
  right; right; right. exists 6, fpos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  rewrite HLF. change (fs_frame_bytes 6) with 4096. unfold Fa in Ha. lia. }

pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0. prreg HS (26%bv : bv 5) Rs10.

rewrite E18 in Ra0. rewrite E2 in Rsp. rewrite E3 in Rgp. rewrite E4 in Rtp. rewrite E8 in Rs0. rewrite E26 in Rs10.
assert (Hsp1_16 : sp1 mod 16 = 0) by (unfold sp1; replace (32 * ((SP - 256) / 32)) with ((2 * ((SP - 256) / 32)) * 16) by ring; apply Z_mod_mult).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS : STKB = 4624) by reflexivity.
eapply SRr_bind.
{ eapply (aj_stack_free_at SEGS B LAWS Hsegs ML (SIGMA GS___asan_stack_free_6) 6 ASF6 ltac:(lia) W2 (ms_regs ms) (ms_mem ms)
    STK sp0 FP ly S W0 mem0 md0 own ly2 S2 _ k fpos 3296 (sp1 - sp0) (Z_to_bv 64 (BASE + 12644)) HJ).
  - rewrite Ra0, HLF. reflexivity.
  - rewrite Ra1. reflexivity.
  - change (fs_frame_bytes 6) with 4096. lia.
  - reflexivity.
  - rewrite HLF, HLFL. change (fs_frame_bytes 6) with 4096. replace (frame_addr lyc 6 fpos + 4096 - 8) with (Fa fpos + 4088) by (unfold Fa; lia).
    transitivity (rdword (aview SEGS (w_H W2) mem2) (Fa fpos + 4088)); [|exact HFLp].
    apply rdword_ext. intros i Hi. apply (aview_kept_out _ _ _ _ _ HFr); [lia|]. ep_winout.
  - unfold spZ. rewrite Rsp, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1_16, B5. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - rewrite Rgp. reflexivity.
  - rewrite Rtp. reflexivity.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HSH4 & HK4 & HW4).

assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ own6 fpos a -> ~ (sp1 - ESTACK <= a < sp1) ->
  aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Ho Hw. rewrite (HK4 a Ha).
  - apply (aview_kept_out _ _ _ _ _ HFr a Ha). intros (r & Hr & Hw').
    change (In r [YP09.mkRegion (Some 24%nat) 0 8 0 8 []]) in Hr. destruct Hr as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw'. rewrite E24, unsigned_lit_small in Hw' by lia. apply Ho. left. lia.
  - intros Hsh. apply Ho. right. left. rewrite HLF in Hsh. change (sf_span 6 3296) with 512 in Hsh.
    unfold shadow_addr, SHADOW_OFF in Hsh. unfold SHa, SBV, Fa. lia.
  - intros ->. apply Ho. right. right. rewrite HLFL. reflexivity.
  - lia. }
assert (Hsv4 : bgs_saved (mrestrict (w_H W2) mem4)).
{ unfold bgs_saved in Hsv |- *. rewrite Forall_forall in Hsv |- *. intros [o r] Hin. pose proof (Hsv _ Hin) as Hv. cbn [fst snd] in Hv |- *.
  assert (Ho : 152 <= o <= 248) by (unfold SAVED in Hin; repeat (destruct Hin as [Hq | Hin]; [inversion Hq; subst; lia |]); destruct Hin).
  eapply val_mem_aview_kept_x; [|exact Hv]. intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
  apply KEEP; [lia | | lia]. intros Ho'. pose proof (proj1 (HOWN x Ho')). lia. }
remember (Eimg (Ereg regs4 ep_saved_extra)) as Ev2 eqn:HEv2.
assert (HEI2 : img_env VAL A_LIM Ev2) by (subst Ev2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ev2 n = getr regs4 r) by (intros n r Hn; rewrite HEv2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX2 : forall j, (j < 13)%nat -> ew Ev2 (32 + j) = nth j ep_saved_extra (Z_to_bv 64 0)) by (intros j Hj; subst Ev2; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (F3 : ew Ev2 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE2 3%nat 3%bv eq_refl), (ep_ap_eq _ _ 3%bv HP4) by ep_cs; exact Rgp).
assert (F4 : ew Ev2 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE2 4%nat 4%bv eq_refl), (ep_ap_eq _ _ 4%bv HP4) by ep_cs; exact Rtp).
assert (F8 : ew Ev2 8 = Z_to_bv 64 SP) by (rewrite (EE2 8%nat 8%bv eq_refl), (ep_ap_eq _ _ 8%bv HP4) by ep_cs; exact Rs0).
assert (F26 : ew Ev2 26 = Z_to_bv 64 res) by (rewrite (EE2 26%nat 26%bv eq_refl), (ep_ap_eq _ _ 26%bv HP4) by ep_cs; exact Rs10).
assert (HS2 : st_ok_pi SEGS VAL Ev2 ep_ss2 (restrict (w_H W2) (mkst regs4 (Z_to_bv 64 (BASE + 0x3164)) mem4 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ep_ss2. apply pa_entry_st_ok_full.
- rewrite HEv2. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite F8, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  unfold bgs_saved in Hsv4.
  repeat (apply Forall_cons; [|]); [..|apply Forall_nil];
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
    let j := eval vm_compute in (n - 32)%nat in
    let r := eval vm_compute in (snd (nth j SAVED (0, 0%nat))) in
    let o := eval vm_compute in (off + 256) in
    pose proof (proj1 (Forall_forall _ _) Hsv4 (o, r) ltac:(cbn; tauto)) as Hv; cbn [fst snd] in Hv;
    apply (chunk_ok_val SEGS Ev2 _ SP off 8 (SOff n 0) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r)))));
    [ cbn [sv_denot]; change n with (32 + j)%nat; rewrite EX2 by lia; rewrite Z.add_0_r; reflexivity
    | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (Z.of_nat r)))) as Hq; exact Hq
    | cbn; lia
    | replace (SP + off) with (SP - 256 + o) by lia; exact Hv ] end.
- cbn. tauto.
- split; [exact I | split; exact I]. }
assert (SHOK2 : sh_ok SEGS ep_Bx [] Ev2 (mrestrict (w_H W2) mem4)) by constructor.
clear HEv2 EE2.
paj_run_tok ep_RUN HS2 HJ4 SHOK2 ep_Bspan. { awr_ok_tac. }

assert (KEEP5 : forall a, 0 <= a < 2 ^ 64 -> ~ own6 fpos a -> ~ (sp1 - ESTACK <= a < sp1) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Ho Hw. rewrite (aview_kept_out _ _ _ _ _ HFr0 a Ha); [exact (KEEP a Ha Ho Hw)|]. ep_winout. }
assert (PRES5 : forall a, sp1 - ESTACK <= a < sp1 -> apresent (w_H W2) (ms_mem ms0) a).
{ intros a Ha. apply (apresent_transfer SEGS (w_H W2) (w_H W2) mem4 (ms_mem ms0) a); [lia | intros Hi; pose proof (Hsegs a Hi); lia | | apply HW4; lia].
  apply (aview_kept_out _ _ _ _ _ HFr0 a ltac:(lia)). ep_winout. }
pose proof (ep_tcj_step fpos E W2 mem2 (ms_mem ms0) HOWN HK KEEP5 PRES5) as TK5.
prreg HS2 (1%bv : bv 5) R1f.
eapply (ep_RET W2 _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)). intros matr.
unfold tb_reac_ctrl_build_grant_sweep_post. cbv beta.
lazymatch goal with |- exists _ _ _ _ _ _, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
  exists ly2, (stack_free_state 6 fpos S2), rg, mm, mdx, res end.
split.
{ rewrite R1f. pose proof (EX2 0%nat ltac:(lia)) as H2. cbn [Nat.add] in H2. rewrite H2. cbn [nth ep_saved_extra SAVED map snd].
  replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Hra. reflexivity. }
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ4|].
split.
{ apply aregs_preserved_eqs.
  all: lazymatch goal with |- getr _ ?r = getr regs ?r =>
    let H := fresh "Rr" in prreg HS2 r H; rewrite H; clear H;
    first [ rewrite F3; exact (eq_sym Hgp)
          | rewrite F4; exact (eq_sym Htp)
          | rewrite F8; apply Z_to_bv_bv_unsigned
          | lazymatch goal with |- ew _ ?n = _ =>
              let j := eval vm_compute in (n - 32)%nat in
              pose proof (EX2 j ltac:(cbv; lia)) as H2; cbn [Nat.add] in H2; rewrite H2; clear H2;
              cbn [nth ep_saved_extra SAVED map snd]; f_equal; apply bv_eq; reflexivity end ] end. }
split.
{ pose proof HJ4 as (_ & _ & _ & _ & _ & Hfrsf & _). pose proof HJc as (_ & _ & _ & _ & _ & Hfrc & _). rewrite Hfrsf, Hfrc. reflexivity. }
split; [unfold ablocks; rewrite blocks_stack_free_state; unfold ablocks in Hbl; exact Hbl|].
split; [destruct HfS as [f Ef]; exact (ep_sfs 6 fpos S2 Sc f Ef)|].
split; [prreg HS2 (10%bv : bv 5) R10f; rewrite R10f, F26; reflexivity|].
split.
{ apply (ep_tcj_mono _ _ E); [exact TK5|].
  destruct HC as [(Hok0 & _ & _ & HE) | (_ & _ & HE)]; intros a Ha; [exact (conj Hok0 (HE a Ha)) | exfalso; exact (HE a Ha)]. }
destruct HC as [(Hok & Hres & Hrows & HE) | (Hnok & Hres & HE)].
- left. split; [exact Hok|]. split; [exact Hres|]. rewrite <- Hrows.
  pose proof (HROWS Hok) as (Hamr & Hs47 & Himg & Htwr & Hrad & Hhull & (bb & mm & Hbb & Hbs & Hbe) & Hwin & Hvs).
  pose proof Hok as (_ & _ & Hw1 & _).
  eapply garr8_aview_kept; [|exact Hrw]. intros a Ha.
  rewrite Hrows, prefix_sweep, len_prefixZ in Ha by lia. unfold bgs_rows in *.
  apply KEEP5; [lia | | lia].
  intros Ho. exact (proj1 (proj2 (proj2 (HOWN a Ho))) bb mm (a - bb) Hbb ltac:(lia) ltac:(lia)).
- right. split; [exact Hnok|]. split; [exact Hres|]. pose proof TK5 as (K1 & K2 & _). split.
  + intros a Ha Hw. apply K1; [exact Ha | exact Hw | exact (HE a)].
  + intros b m i Hb Hi. apply (K2 b m i); [exact Hb | exact Hi | exact (HE _)].
Qed.

(* ---- S3: one row of the first channel (0x8389c .. 0x83934), over the scratch F + 1664 ------------------- *)
(* ==== piece r1: row1, one row of the first channel (0x8389c .. 0x83938) ======================================= *)
Lemma r1_nth_mapu : forall (l : list byte) j, nth j (map bv_unsigned l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof. induction l as [|x l IH]; intros [|j]; cbn; try reflexivity. apply IH. Qed.
Lemma r1_bv_wrap : forall z q, Z_to_bv 64 z = Z_to_bv 64 (z + q * 2 ^ 64).
Proof.
intros z q. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma r1_ap_eq : forall (R1 R2 : bvmap 5 word) (r : bv 5), aregs_preserved R1 R2 -> acallee_saved (bv_unsigned r) -> getr R2 r = getr R1 r.
Proof. intros R1 R2 r HP Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
(* F's shadow is not F: F is application memory (low or high), its shadow is in the shadow band *)
Lemma r1_sh_F : forall F a, amem_range F 4096 -> 0 <= F -> 0x7fff8000 + F / 8 <= a < 0x7fff8000 + F / 8 + 512 ->
  ~ (F <= a < F + 4096).
Proof.
intros F a HF H0 Ha Hb. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HF.
pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)). lia.
Qed.
Lemma r1_region_kept : forall E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma r1_loc_acc_kept : forall fpos H H' (m m' : word -> option byte),
  (forall a, sp1 + 0x20 <= a < sp1 + 0x60 -> aview SEGS H' m' a = aview SEGS H m a) ->
  loc_acc fpos (mrestrict H m) -> loc_acc fpos (mrestrict H' m').
Proof.
intros fpos H H' m m' Hk (A1 & A2 & A3 & A4).
split; [|split; [|split]]; (eapply (val_mem_aview_kept_x SEGS H H' m m'); [|eassumption]); intros x Hx; apply Hk; lia.
Qed.
(* a step that changes at most bytes of F's shadow (P) keeps the invariant with E = RowsE *)
Lemma r1_binv_step : forall fpos W2 ly2 S2 mem2 md2 rows mem3 md3 (P : Z -> Prop),
  bgs_ok s V mx base w -> Z.of_nat (length rows) <= 34 * bgs_rows w ->
  binv fpos RowsE W2 ly2 S2 mem2 md2 rows ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((6, fpos) :: own) ly2 S2 W2 mem3 md3 k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, P a -> SHa fpos <= a < SHa fpos + 512) ->
  mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) mem3) ->
  binv fpos RowsE W2 ly2 S2 mem3 md3 rows.
Proof.
intros fpos W2 ly2 S2 mem2 md2 rows mem3 md3 P HOK Hlen HI HJ3 Hout HP Hgr.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof sp1_facts as (Hsp1a & Hsp1b).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_ctrl_build_grant_sweep = 4624) by reflexivity.
destruct (binv_frame _ _ _ _ _ _ _ _ HI) as (Fal & F4096 & Fceil & Fimg & F47 & Fam & Fpres & SHpres & Fown).
destruct (HROWS HOK) as (Ram & Hs47 & Himg & Htwr & Hsra & Hshv & (bb & mm & Hbm & Hb1 & Hb2) & Hrwin & Hrv).
unfold bgs_rows in *.
assert (HPo : forall a, P a -> a < alloc_ceiling /\ (forall b n i, In (b, n) (ablocks B lyc Sc) -> 0 <= i < req_size n -> b + i <> a)).
{ intros a Ha. destruct (Fown a ltac:(right; left; exact (HP a Ha))) as (X1 & _ & X3 & _). split; assumption. }
apply (binv_kept fpos RowsE RowsE W2 ly2 S2 mem2 md2 rows mem3 md3 HI HJ3).
- intros a Ha. exact Ha.
- intros a Ha Hi. pose proof (pa_img_range a Hi) as Hia. unfold RowsE, bgs_rows in Ha.
  pose proof IMG_LO_B_val as I1. pose proof IMG_TOP_B_val as I2. lia.
- intros a Ha _ _ Hno. apply Hout; [exact Ha|]. intros HPa. apply Hno. right; left. exact (HP a HPa).
- intros a Ha. apply Hout; [lia|]. intros HPa. destruct (HPo a HPa). lia.
- intros a Ha. apply Hout; [lia|]. intros HPa. destruct (HPo a HPa). lia.
- intros a Ha. apply Hout; [lia|]. intros HPa. pose proof (HP a HPa) as X.
  apply (r1_sh_F (Fa fpos) a Fam ltac:(lia)); [unfold SHa, SBV in X; exact X | lia].
- intros a Ha. apply Hout; [lia|]. intros HPa. destruct (HPo a HPa) as [_ X]. apply (X bb mm (a - bb) Hbm); lia.
- intros a _ Hp. exact (apresent_grows _ _ _ a Hgr Hp).
Qed.
Ltac r1_mkshok HS := lazymatch type of HS with st_ok_pi ?sg _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
  let SH := fresh "SHOK" in assert (SH : sh_ok sg (SOff 32 0) [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by (apply Forall_nil);
  cbn [ms_mem mkst] in SH end.
Ltac r1_rebase HS AG := let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv;
  try (lazymatch type of HS with st_ok_pi _ _ _ _ _ => repeat (match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end); r1_mkshok HS end).
Ltac r1_Uin AG Hc :=
  repeat match type of Hc with context [U ?Ev (SOff ?n ?c)] =>
    match goal with Hn : ew _ n = Z_to_bv 64 ?v |- _ =>
      let F := fresh "F" in assert (F : ew Ev n = Z_to_bv 64 v) by (first [exact Hn | rewrite AG by lia; exact Hn]);
      first [ rewrite (U_atom Ev n v F) in Hc by lia | rewrite (U_atom_off Ev n v c F) in Hc by lia ]; clear F end end;
  rewrite ?U_lit in Hc by lia.
Ltac r1_Ugoal AG :=
  repeat match goal with |- context [U ?Ev (SOff ?n ?c)] =>
    match goal with Hn : ew _ n = Z_to_bv 64 ?v |- _ =>
      let F := fresh "F" in assert (F : ew Ev n = Z_to_bv 64 v) by (first [exact Hn | rewrite AG by lia; exact Hn]);
      first [ rewrite (U_atom Ev n v F) by lia | rewrite (U_atom_off Ev n v c F) by lia ]; clear F end end.
Ltac r1_bad AG := exfalso;
  lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
    rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in Hc; r1_Uin AG Hc;
    first [ apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc
          | apply Bool.negb_true_iff, Z.eqb_neq in Hc | apply Bool.negb_false_iff, Z.eqb_eq in Hc
          | apply Bool.negb_true_iff, Z.ltb_ge in Hc | apply Bool.negb_false_iff, Z.ltb_lt in Hc ]; lia end.
Ltac r1_rfact AG H := repeat (rewrite AG in H by lia);
  repeat match type of H with context [ew ?Ex ?n] => match goal with En : ew Ex n = _ |- _ => rewrite En in H end end.
Ltac r1_close HS AG := lazymatch goal with |- getr _ ?r = w64 _ =>
  let H := fresh "Rx" in prreg HS r H; r1_rfact AG H; rewrite H; clear H; unfold w64;
  rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia] end.
Ltac r1_apclose HP HS AG := lazymatch goal with |- getr _ ?r = w64 _ =>
  rewrite (r1_ap_eq _ _ r HP) by (unfold acallee_saved; let x := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with x; lia);
  r1_close HS AG end.
(* the value of an atom, from the fact about it (through AG when the env was rebased) *)
Ltac r1_ewv AG H := repeat match type of H with context [bv_unsigned (ew ?Ev ?n)] =>
    match goal with Hn : ew _ n = Z_to_bv 64 ?v |- _ =>
      let F := fresh "F" in assert (F : ew Ev n = Z_to_bv 64 v) by (first [exact Hn | rewrite AG by lia; exact Hn]);
      rewrite F, unsigned_lit_small in H by lia; clear F end end.
Ltac r1_ewvg AG := repeat match goal with |- context [bv_unsigned (ew ?Ev ?n)] =>
    match goal with Hn : ew _ n = Z_to_bv 64 ?v |- _ =>
      let F := fresh "F" in assert (F : ew Ev n = Z_to_bv 64 v) by (first [exact Hn | rewrite AG by lia; exact Hn]);
      rewrite F, unsigned_lit_small by lia; clear F end end.
(* the write windows of a run's regions, read off the state *)
Ltac r1_win AG := let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros (r & Hr & Hw); lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
  cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; r1_ewv AG Hw; lia |]);
  try destruct Hr.
Ltac r1_inwin AG := let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros a (r & Hr & Hw); lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
  cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; r1_ewv AG Hw; lia |]);
  try destruct Hr.
(* after a run of the body: the invariant and the accepting path's locals at the new memory *)
Ltac r1_updn AG HOK Hlen HI HLA :=
  lazymatch type of HI with binv ?fp RowsE ?Wx ?lyx ?Sx ?m0 ?md0 ?rws =>
  lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ m0) (mrestrict _ (ms_mem ?m1)),
    HG : mem_grows (mrestrict _ m0) (mrestrict _ (ms_mem ?m1)),
    HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m1) ?mdx _ |- _ =>
  let HI2 := fresh "HI" in
  assert (HI2 : binv fp RowsE Wx lyx Sx (ms_mem m1) mdx rws)
    by (apply (r1_binv_step fp Wx lyx Sx m0 md0 rws (ms_mem m1) mdx (in_wrange Eo rs) HOK Hlen HI HJx);
        [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
          intros a Ha Hn; exact (aview_kept_out Eo rs _ _ _ HFr a Ha Hn) | r1_inwin AG | exact HG ]);
  let HLA2 := fresh "HLA" in
  assert (HLA2 : loc_acc fp (mrestrict (w_H Wx) (ms_mem m1)))
    by (apply (r1_loc_acc_kept fp (w_H Wx) (w_H Wx) m0 (ms_mem m1)); [|exact HLA];
        let a := fresh "a" in let Ha := fresh "Ha" in
        intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); r1_win AG);
  clear HI HLA; rename HI2 into HI; rename HLA2 into HLA
  end end.
(* after a run of the body: the invariant, the accepting path's locals and F's shadow 208 .. 393 at the new memory *)
Ltac r1_upd AG HOK Hlen HI HLA HZ :=
  lazymatch type of HI with binv ?fp RowsE ?Wx ?lyx ?Sx ?m0 ?md0 ?rws =>
  lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ m0) (mrestrict _ (ms_mem ?m1)),
    HG : mem_grows (mrestrict _ m0) (mrestrict _ (ms_mem ?m1)),
    HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m1) ?mdx _ |- _ =>
  let HI2 := fresh "HI" in
  assert (HI2 : binv fp RowsE Wx lyx Sx (ms_mem m1) mdx rws)
    by (apply (r1_binv_step fp Wx lyx Sx m0 md0 rws (ms_mem m1) mdx (in_wrange Eo rs) HOK Hlen HI HJx);
        [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
          intros a Ha Hn; exact (aview_kept_out Eo rs _ _ _ HFr a Ha Hn) | r1_inwin AG | exact HG ]);
  let HLA2 := fresh "HLA" in
  assert (HLA2 : loc_acc fp (mrestrict (w_H Wx) (ms_mem m1)))
    by (apply (r1_loc_acc_kept fp (w_H Wx) (w_H Wx) m0 (ms_mem m1)); [|exact HLA];
        let a := fresh "a" in let Ha := fresh "Ha" in
        intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); r1_win AG);
  let HZ2 := fresh "HZ" in
  assert (HZ2 : forall i, 0 <= i < 186 -> aview SEGS (w_H Wx) (ms_mem m1) (SHa fp + 208 + i) = Some 0)
    by (let i := fresh "i" in let Hi := fresh "Hi" in
        intros i Hi; rewrite (aview_kept_out Eo rs _ _ _ HFr (SHa fp + 208 + i) ltac:(lia)) by (r1_win AG); exact (HZ i Hi));
  clear HI HLA HZ; rename HI2 into HI; rename HLA2 into HLA; rename HZ2 into HZ
  end end.
(* After __asan_set_shadow_00 (F's shadow 208 .. 393 is 0): the rest of the row, from 0x838d8 (BASE + 0x2e9c). *)
Definition r1_sst : sstate := mkSS 0x2e9c sr_atoms
  [YP09.mkRegion (Some 9%nat) 0x60 0x68 0 0 [YP09.mkChunk 0x60 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 23%nat) 394 395 394 395 []] None (mkFacts [] [] []).
Lemma r1_tail : forall fpos p rows W2 ly2 S2 regs2 mem2 md2, bgs_ok s V mx base w -> 0 <= p < 3 ->
  binv fpos RowsE W2 ly2 S2 mem2 md2 rows -> Z.of_nat (length rows) = 34 * (1 + p) ->
  l1regs fpos regs2 p -> getr regs2 18 = w64 (vz vals (Z.to_nat p)) -> loc_acc fpos (mrestrict (w_H W2) mem2) ->
  (forall i, 0 <= i < 186 -> aview SEGS (w_H W2) mem2 (SHa fpos + 208 + i) = Some 0) ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x2e9c)) mem2 (seg_rom SEGS)) md2)
    (L1post fpos (p + 1) (rows ++ GAz base p (vz vals (Z.to_nat p)))).
Proof.
intros fpos p rows W2 ly2 S2 regs2 mem2 md2 HOK Hp HI Hlen
  ((R2 & R3 & R4 & R8 & R9) & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27) R18 HLA HZ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof sp1_facts as (Hsp1a & Hsp1b).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_ctrl_build_grant_sweep = 4624) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HOK as (Hs0 & HVn0 & Hw1 & Hbw & Hmx). unfold bgs_rows in Hmx.
destruct (HROWS HOK) as (Ram & Hs47 & Himg & Htwr & Hsra & Hshv & (bb & mm & Hbm & Hb1 & Hb2) & Hrwin & Hrv).
unfold bgs_rows in *.
destruct (binv_frame _ _ _ _ _ _ _ _ HI) as (Fal & F4096 & Fceil & Fimg & F47 & Fam & Fpres & SHpres & Fown).
assert (HSHc : SHa fpos + 512 <= alloc_ceiling) by (destruct (Fown (SHa fpos + 511) ltac:(right; left; lia)) as (X & _); lia).
assert (HSH0 : 0x7fff8000 <= SHa fpos) by (unfold SHa, SBV; pose proof (Z.div_pos (Fa fpos) 8 ltac:(lia) ltac:(lia)); lia).
assert (HSHF : forall a, SHa fpos <= a < SHa fpos + 512 -> ~ (Fa fpos <= a < Fa fpos + 4096))
  by (intros a Ha; apply (r1_sh_F (Fa fpos) a Fam ltac:(lia)); unfold SHa, SBV in Ha; exact Ha).
assert (Hown_rows : forall a, own6 fpos a -> ~ (s <= a < s + 34 * (8 + 3 * w)))
  by (intros a Ha Hr; destruct (Fown a Ha) as (_ & _ & X & _); apply (X bb mm (a - bb) Hbm ltac:(lia)); lia).
assert (Hlen' : Z.of_nat (length rows) <= 34 * bgs_rows w) by (unfold bgs_rows; lia).
set (vb := vz vals (Z.to_nat p)) in *.
assert (Rvb : 0 <= vb < 256) by (apply vz_range).
destruct (vals_at fpos RowsE W2 ly2 S2 mem2 md2 rows HOK HI (fun a H => H)) as (_ & _ & HV0 & HV47 & Hvlen & Hvleg).
assert (Hleg : legalb p vb = true).
{ apply bgs_legal_legalb. pose proof (Hvleg (Z.to_nat p) ltac:(lia)) as L.
  replace (Z.of_nat (Z.to_nat p mod 3)) with p in L by (rewrite Nat.mod_small by lia; lia). exact L. }
pose proof HI as (HJ & _ & _ & _ & _ & _ & (L60 & L68 & L70 & L78) & _).
remember (Eimg (Ereg regs2 [Z_to_bv 64 base])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite R18 in E18.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite R19 in E19.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite R20 in E20.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite R21 in E21.
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite R22 in E22.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite R23 in E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite R24 in E24.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite R25 in E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite R26 in E26.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite R27 in E27.
assert (E32 : ew E 32 = Z_to_bv 64 base) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
unfold w64 in E2, E3, E4, E8, E9, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
assert (HS : st_ok_pi SEGS VAL E r1_sst (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x2e9c)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold r1_sst. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ sp1 0x60 8 (SOff 32 0) base);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact L60].
  + rewrite E23, unsigned_lit_small by lia. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (SHpres (SHa fpos + o) ltac:(lia))) | constructor].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E23, !unsigned_lit_small by lia.
  split; [split; [lia | exact I] | split; exact I].
- split; [exact I | split; exact I]. }
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
clear HE EE.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP. pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC. pose proof (paj_branch (PI := PI)) as BR.
destruct (binv_layout _ _ _ _ _ _ _ _ HI) as (Elo & Ehi & Etop & EF & EFL).
(* run: `sb 4` to F's shadow byte 394, the arguments of __asan_memset (F + 1664, 0, 1492) *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sq ?fp ?b0 ?bc ?lq ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sq fp b0 bc lq ow) end.
  apply awr_ok_cons_ro; [azlit_tac|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat (SHa fpos)); [reflexivity | rewrite E23; apply unsigned_lit_small; lia | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 6, fpos. split; [left; reflexivity|].
  right. unfold in_zr. cbn [fst snd]. rewrite EF. change (frame_addr lyc 6 fpos) with (Fa fpos).
  change (fs_frame_bytes 6 / 8) with 512. unfold shadow_addr, SHADOW_OFF. unfold SHa, SBV in Ha. lia. }
assert (H394 : aview SEGS (w_H W2) (ms_mem ms) (SHa fpos + 394) = Some 4).
{ lazymatch type of HS with st_ok ?sg ?Ex ?ssx ?msx => pose proof (st_ok_region_nth Ex ssx msx 1 _ HS eq_refl) as HR1 end.
  cbn [ms_mem restrict] in HR1.
  pose proof (field_of_region E _ 23 (SHa fpos) _ 394 395 394 395 394 1%N (SLit 4) 4 HR1
    ltac:(rewrite E23; apply unsigned_lit_small; lia) ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V4.
  apply (aview_of_val_mem1 SEGS); [exact V4 | lia]. }
r1_upd AG HOK Hlen' HI HLA HZ. clear_frames.
(* __asan_memset (F + 1664, 0, 1492): the scratch's shadow is 0 .. 0 4 *)
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
r1_rfact AG Ra0. r1_rfact AG Rsp. r1_rfact AG Rgp. r1_rfact AG Rtp.
eapply (call_memset fpos W2 ly2 S2 _ _ rows _ 11956 1664 _ HOK Hlen' HI (or_intror eq_refl)).
{ apply (ra_scratch fpos (aview SEGS (w_H W2) (ms_mem ms)) 1664 (or_intror eq_refl) Fal); change (1664 / 8) with 208.
  - exact HZ.
  - replace (SHa fpos + 208 + 186) with (SHa fpos + 394) by lia. exact H394. }
{ exact Ra0. } { exact Ra1. } { exact Ra2. }
{ unfold spZ. rewrite Rsp, unsigned_lit_small by lia. reflexivity. }
{ exact Rgp. } { exact Rtp. } { exact Rra. } { lia. } { reflexivity. }
intros mem3 md3 regs3 HI3 HZm Hout3 HP3. clear Ra0 Ra1 Ra2 Rsp Rgp Rtp Rra H394.
pose proof (proj1 HI3) as HJ3.
reseat HS HJ3 HP3 [0]%nat AG ltac:(apply (r1_region_kept _ _ _ _ _ 9 sp1);
  [ r1_ewvg AG; reflexivity
  | intros a Ha; apply Hout3; [lia | lia | rewrite Hes; lia]
  | intros a Ha; lia ]).
assert (HLA3 : loc_acc fpos (mrestrict (w_H W2) mem3)).
{ apply (r1_loc_acc_kept fpos (w_H W2) (w_H W2) (ms_mem ms) mem3); [|exact HLA].
  intros a Ha. apply Hout3; [lia | lia | rewrite Hes; lia]. }
assert (HZ3 : forall i, 0 <= i < 186 -> aview SEGS (w_H W2) mem3 (SHa fpos + 208 + i) = Some 0).
{ intros i Hi. rewrite Hout3; [exact (HZ i Hi) | lia | | rewrite Hes; lia].
  intros Hx. apply (HSHF (SHa fpos + 208 + i)); lia. }
clear HI HLA HZ Hout3 HZm HP3. rename HI3 into HI. rename HLA3 into HLA. rename HZ3 into HZ.
(* run: the arguments of reac_ctrl_stamp_headamp (F + 1664, base, p, V[p]) *)
paj_run_shc RUNP RUNC HS HJ3. { awr_ok_tac. }
r1_upd AG HOK Hlen' HI HLA HZ. clear_frames.
pmkst HS. rewrite pa_sigma_reac_ctrl_stamp_headamp.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
prreg HS (8%bv : bv 5) Rs0.
r1_rfact AG Ra0. r1_rfact AG Ra1. r1_rfact AG Ra2. r1_rfact AG Ra3. r1_rfact AG Rsp. r1_rfact AG Rgp. r1_rfact AG Rtp.
r1_rfact AG Rs0.
eapply (call_stamp fpos W2 ly2 S2 _ _ rows _ 11976 1664 base p vb _ HOK HI (or_intror eq_refl) Hlen').
{ intros x Hx. apply (sh_zero_stamp fpos _ 1664 (or_intror eq_refl) Fal); [|exact Hx].
  change (1664 / 8) with 208. exact HZ. }
{ exact Ra0. } { exact Ra1. } { exact Ra2. } { exact Ra3. } { lia. } { lia. } { lia. } { exact Hleg. }
{ unfold spZ. rewrite Rsp, unsigned_lit_small by lia. reflexivity. }
{ exact Rs0. } { exact Rgp. } { exact Rtp. } { exact Rra. } { lia. } { reflexivity. }
intros W4 ly4 S4 mem4 md4 regs4 HI4 Hsp4 HSH4 HF4 HP4 R10z HGA.
clear Ra0 Ra1 Ra2 Ra3 Rsp Rgp Rtp Rra Rs0.
pose proof (proj1 HI4) as HJ4.
reseat HS HJ4 HP4 [0]%nat AG ltac:(apply (r1_region_kept _ _ _ _ _ 9 sp1);
  [ r1_ewvg AG; reflexivity
  | intros a Ha; apply Hsp4; lia
  | intros a Ha; lia ]).
assert (HLA4 : loc_acc fpos (mrestrict (w_H W4) mem4)).
{ eapply (r1_loc_acc_kept fpos (w_H W2) (w_H W4) _ mem4); [|exact HLA]. intros a Ha. apply Hsp4. lia. }
assert (HZ4 : forall i, 0 <= i < 186 -> aview SEGS (w_H W4) mem4 (SHa fpos + 208 + i) = Some 0).
{ intros i Hi. rewrite HSH4 by lia. exact (HZ i Hi). }
clear HI HLA HZ Hsp4 HSH4 HF4. rename HI4 into HI. rename HLA4 into HLA. rename HZ4 into HZ.
(* the stamp returned 0: `bnez a0` (0x83904) is not taken *)
prreg HS (10%bv : bv 5) Rz. rewrite R10z in Rz. symmetry in Rz. unfold w64 in Rz.
psrr_branch_pi RUNP BR HS.
{ r1_bad AG. }
clear Hc Rz R10z.
(* run: the arguments of __asan_memcpy (s + 34 (1 + p), F + 1680, 34) *)
paj_run_shc RUNP RUNC HS HJ4. { awr_ok_tac. }
lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ mem4) (mrestrict _ (ms_mem ?m1)) |- _ =>
  assert (HGA1 : garr8 SEGS (mrestrict (w_H W4) (ms_mem m1)) (Fa fpos + 1664 + 16) (GAz base p vb))
  by (apply (garr8_aview_kept SEGS (w_H W4) (w_H W4) mem4 (ms_mem m1)); [|exact HGA];
      intros a Ha; rewrite len_GAz in Ha; change (Z.of_nat 34) with 34 in Ha;
      apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); r1_win AG) end.
r1_upd AG HOK Hlen' HI HLA HZ. clear_frames. clear HGA.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
r1_rfact AG Ra0. r1_rfact AG Ra1. r1_rfact AG Rsp. r1_rfact AG Rgp. r1_rfact AG Rtp.
destruct (binv_layout _ _ _ _ _ _ _ _ HI) as (_ & _ & _ & EF4 & _).
pose proof HI as (HJ5 & Hfr5 & _).
eapply (call_cpy fpos W4 ly4 S4 _ _ rows _ 11996 (Fa fpos + 1680) (GAz base p vb) _ HOK HI);
  rewrite ?len_GAz; change (Z.of_nat 34) with 34.
{ lia. }
{ unfold bgs_rows. lia. }
{ replace (Fa fpos + 1680) with (Fa fpos + 1664 + 16) by lia. exact HGA1. }
{ lia. } { lia. }
{ destruct (Z_le_gt_dec (s + Z.of_nat (length rows) + 34) (Fa fpos + 1680)); [left; lia|].
  destruct (Z_le_gt_dec (Fa fpos + 1680 + 34) (s + Z.of_nat (length rows))); [right; lia|]. exfalso.
  apply (Hown_rows (Z.max (Fa fpos + 1680) (s + Z.of_nat (length rows)))); [left; lia | lia]. }
{ unfold amem_range in *. lia. }
{ intros a Ha. rewrite Hes. lia. }
{ intros x Hx. exists 0. split; [|left; reflexivity]. change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
  apply (sh_zero_stamp fpos _ 1664 (or_intror eq_refl) Fal); [change (1664 / 8) with 208; exact HZ | lia]. }
{ apply (shadow_hull_vis_of_frame SEGS B LAWS ly4 S4 W4 _ _ 6 fpos _ _ (proj1 HJ5)); [rewrite Hfr5; left; reflexivity | | | lia];
  rewrite EF4; change (frame_addr lyc 6 fpos) with (Fa fpos); change (fs_frame_bytes 6) with 4096; lia. }
{ rewrite Ra0, Hlen. reflexivity. }
{ exact Ra1. } { exact Ra2. }
{ unfold spZ. rewrite Rsp, unsigned_lit_small by lia. reflexivity. }
{ exact Rgp. } { exact Rtp. } { exact Rra. } { lia. } { reflexivity. }
intros mem5 md5 regs5 HI5 Hout5 HP5. clear Ra0 Ra1 Ra2 Rsp Rgp Rtp Rra HGA1 EF4 HJ5 Hfr5.
reseat HS (proj1 HI5) HP5 [0]%nat AG ltac:(apply (r1_region_kept _ _ _ _ _ 9 sp1);
  [ r1_ewvg AG; reflexivity
  | intros a Ha; apply Hout5; [lia | lia | rewrite Hes; lia]
  | intros a Ha; lia ]).
assert (HLA5 : loc_acc fpos (mrestrict (w_H W4) mem5)).
{ eapply (r1_loc_acc_kept fpos (w_H W4) (w_H W4) _ mem5); [|exact HLA]. intros a Ha. apply Hout5; [lia | lia | rewrite Hes; lia]. }
assert (HZ5 : forall i, 0 <= i < 186 -> aview SEGS (w_H W4) mem5 (SHa fpos + 208 + i) = Some 0).
{ intros i Hi. rewrite Hout5; [exact (HZ i Hi) | lia | | rewrite Hes; lia].
  intros Hx. apply (Hown_rows (SHa fpos + 208 + i)); [right; left; lia | lia]. }
clear HI HLA HZ Hout5 HP5. rename HI5 into HI. rename HLA5 into HLA. rename HZ5 into HZ.
assert (Hlen2 : Z.of_nat (length (rows ++ GAz base p vb)) <= 34 * bgs_rows w) by (rewrite length_app, len_GAz; unfold bgs_rows; lia).
(* run: the arguments of __asan_set_shadow_f8 (SHF + 208, 187) *)
pose proof (proj1 HI) as HJ5.
paj_run_shc RUNP RUNC HS HJ5. { awr_ok_tac. }
r1_upd AG HOK Hlen2 HI HLA HZ. clear_frames.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
r1_rfact AG Ra0. r1_rfact AG Rsp. r1_rfact AG Rgp. r1_rfact AG Rtp.
eapply (call_ss fpos RowsE 248 (SIGMA GS___asan_set_shadow_f8) W4 ly4 S4 _ _ (rows ++ GAz base p vb) _ 12008 (SHa fpos + 208) 187 _
  SSF8 HI (or_intror (conj HOK Hlen2))).
{ exact Ra0. } { exact Ra1. } { lia. } { lia. } { lia. }
{ unfold spZ. rewrite Rsp, unsigned_lit_small by lia. reflexivity. }
{ exact Rgp. } { exact Rtp. } { exact Rra. } { lia. } { reflexivity. }
intros mem6 md6 regs6 HI6 Hv6 Hout6 Hpres6 HP6. clear Ra0 Ra1 Rsp Rgp Rtp Rra.
reseat HS (proj1 HI6) HP6 [0]%nat AG ltac:(apply (r1_region_kept _ _ _ _ _ 9 sp1);
  [ r1_ewvg AG; reflexivity
  | intros a Ha; apply Hout6; lia
  | intros a Ha; lia ]).
assert (HLA6 : loc_acc fpos (mrestrict (w_H W4) mem6)).
{ eapply (r1_loc_acc_kept fpos (w_H W4) (w_H W4) _ mem6); [|exact HLA]. intros a Ha. apply Hout6; lia. }
clear HI HLA HZ Hout6 Hv6 Hpres6 HP6. rename HI6 into HI. rename HLA6 into HLA.
(* run: the counters, and `bne s10, 3` (0x83934) *)
pose proof (proj1 HI) as HJ6.
paj_run_shc RUNP RUNC HS HJ6. { awr_ok_tac. }
r1_updn AG HOK Hlen2 HI HLA. clear_frames.
psrr_branch_pi RUNP BR HS.
- rewrite branch_ne_U in Hc. r1_Uin AG Hc.
  assert (Hp1 : (p + 1 =? 3) = false) by (apply Bool.negb_true_iff in Hc; exact Hc). clear Hc.
  pose proof (proj1 HI) as HJ7.
  paj_run_to_shc RUNTOP HS HJ7 11872. { awr_ok_tac. }
  r1_updn AG HOK Hlen2 HI HLA. clear_frames.
  pmkst HS. apply SRr_ret. unfold L1post.
  lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m1) ?mdx _ |- _ =>
    exists ly4, S4, (ms_regs m1), (ms_mem m1), mdx end.
  split; [rewrite Hp1; reflexivity|]. split; [exact HI|]. split; [|exact HLA].
  unfold l1regs, rB. repeat split; r1_close HS AG.
- rewrite branch_ne_U in Hc. r1_Uin AG Hc.
  assert (Hp1 : (p + 1 =? 3) = true) by (apply Bool.negb_false_iff in Hc; exact Hc). clear Hc.
  pose proof (proj1 HI) as HJ7.
  paj_run_to_shc RUNTOP HS HJ7 12056. { awr_ok_tac. }
  r1_updn AG HOK Hlen2 HI HLA. clear_frames.
  pmkst HS. apply SRr_ret. unfold L1post.
  lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m1) ?mdx _ |- _ =>
    exists ly4, S4, (ms_regs m1), (ms_mem m1), mdx end.
  split; [rewrite Hp1; reflexivity|]. split; [exact HI|]. split; [|exact HLA].
  unfold l1regs, rB. repeat split; r1_close HS AG.
Qed.
Definition r1_Bspan : Z * Z := (SBV, SBV + 2 ^ 44 - 1).
Definition r1_ssh (p : Z) : sstate := mkSS 0x2e60 (sr_set sr_atoms 26%bv (SLit p))
  [YP09.mkRegion (Some 9%nat) 0x68 0x80 0 0
     [YP09.mkChunk 0x68 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x70 (CVal 8 (SOff 34 0));
      YP09.mkChunk 0x78 (CVal 8 (SOff 21 (- (34 * (1 + p)))))];
   YP09.mkRegion (Some 34%nat) p (p + 1) 0 0 [YP09.mkChunk p (CVal 1 (SOff 33 0))]] None
  (mkFacts [(32%nat, mkAF SBV SBV 0); (34%nat, mkAF 0 (2 ^ 47 - 4) 0)] [] []).
Lemma row1 : forall fpos p rows W2 ly2 S2 regs2 mem2 md2, bgs_ok s V mx base w -> 0 <= p < 3 ->
  binv fpos RowsE W2 ly2 S2 mem2 md2 rows -> Z.of_nat (length rows) = 34 * (1 + p) ->
  l1regs fpos regs2 p -> loc_acc fpos (mrestrict (w_H W2) mem2) ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x2e60)) mem2 (seg_rom SEGS)) md2)
    (L1post fpos (p + 1) (rows ++ GAz base p (vz vals (Z.to_nat p)))).
Proof.
intros fpos p rows W2 ly2 S2 regs2 mem2 md2 HOK Hp HI Hlen ((R2 & R3 & R4 & R8 & R9) & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27) HLA.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof sp1_facts as (Hsp1a & Hsp1b).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_ctrl_build_grant_sweep = 4624) by reflexivity.
destruct (vals_at fpos RowsE W2 ly2 S2 mem2 md2 rows HOK HI (fun a H => H)) as (HGV & HRV & HV0 & HV47 & Hvlen & Hvleg).
pose proof HOK as (Hs0 & HVn0 & Hw1 & Hbw & Hmx). unfold bgs_rows in Hmx.
destruct (HROWS HOK) as (Ram & Hs47 & Himg & Htwr & Hsra & Hshv & Hblk & Hrwin & Hrv). unfold bgs_rows in *.
destruct (HVALS Hw1 HVn0) as (_ & _ & _ & _ & _ & HVwin).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hlen' : Z.of_nat (length rows) <= 34 * bgs_rows w) by (unfold bgs_rows; lia).
destruct (binv_frame _ _ _ _ _ _ _ _ HI) as (Fal & F4096 & Fceil & Fimg & F47 & Fam & Fpres & SHpres & Fown).
assert (HSHc : SHa fpos + 512 <= alloc_ceiling) by (destruct (Fown (SHa fpos + 511) ltac:(right; left; lia)) as (X & _); lia).
assert (HSH0 : 0x7fff8000 <= SHa fpos) by (unfold SHa, SBV; pose proof (Z.div_pos (Fa fpos) 8 ltac:(lia) ltac:(lia)); lia).
set (vb := vz vals (Z.to_nat p)).
destruct (garr8_nthZ SEGS _ V (map bv_unsigned vals) p HGV ltac:(lia) ltac:(rewrite length_map, Hvlen; lia)) as [Mvb Rvb].
rewrite r1_nth_mapu in Mvb, Rvb. change (bv_unsigned (nth (Z.to_nat p) vals (Z_to_bv 8 0))) with vb in Mvb, Rvb.
pose proof HI as (HJ & Hfr & Hbl & Hfs & HKe & Hsv & (L60 & L68 & L70 & L78) & Hfl & Hrw).
remember (Eimg (Ereg regs2 [Z_to_bv 64 0x7fff8000; Z_to_bv 64 vb; Z_to_bv 64 V])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite R19 in E19.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite R20 in E20.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite R21 in E21.
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite R22 in E22.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite R23 in E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite R24 in E24.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite R25 in E25.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite R27 in E27.
assert (E32 : ew E 32 = Z_to_bv 64 0x7fff8000) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 vb) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 V) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
unfold w64 in E2, E3, E4, E8, E9, E19, E20, E21, E22, E23, E24, E25, E27.
assert (E19w : ew E 19 = Z_to_bv 64 (2 ^ 64 - 1 - V)) by (rewrite E19, (r1_bv_wrap (-1 - V) 1); f_equal; lia).
assert (HS : st_ok_pi SEGS VAL E (r1_ssh p) (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x2e60)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold r1_ssh. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite R26; reflexivity].
- assert (Hp' : p = 0 \/ p = 1 \/ p = 2) by lia. destruct Hp' as [-> | [-> | ->]]; vm_compute; reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp1 0x68 8 (SOff 32 0) SBV);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; unfold SBV; lia | lia | exact L68].
    * apply (chunk_ok_val SEGS E _ sp1 0x70 8 (SOff 34 0) V);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact L70].
    * apply (chunk_ok_val SEGS E _ sp1 0x78 8 (SOff 21 (- (34 * (1 + p)))) s);
      [cbn [sv_denot]; rewrite E21, unsigned_lit_small by lia; f_equal; lia | cbn; lia | lia | exact L78].
  + rewrite E34, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ V p 1 (SOff 33 0) vb);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Mvb].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E34, !unsigned_lit_small by lia.
  split; [split; [lia | exact I] | split; exact I].
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E32, E34, !unsigned_lit_small by (unfold SBV; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SBV. repeat split; lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
clear HE EE.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_branch (PI := PI)) as BR.
assert (Hp' : p = 0 \/ p = 1 \/ p = 2) by lia.
(* the three trap guards (0x8389c, 0x838a4, 0x838a8), the check of V[p]'s shadow and the load of V[p] *)
destruct Hp' as [-> | [-> | ->]].
all: paj_run_tok RUN HS HJ SHOK r1_Bspan.
all: try awr_ok_tac.
all: r1_rebase HS AG. all: r1_updn AG HOK Hlen' HI HLA. all: clear_frames.
all: psrr_branch_tok RUN BR HS SHOK r1_Bspan.
all: [> r1_bad AG | | r1_bad AG | | r1_bad AG | ].
all: clear Hc.
all: paj_run_tok RUN HS HJ SHOK r1_Bspan.
all: try awr_ok_tac.
all: r1_rebase HS AG. all: r1_updn AG HOK Hlen' HI HLA. all: clear_frames.
all: psrr_branch_tok RUN BR HS SHOK r1_Bspan.
all: [> r1_bad AG | | r1_bad AG | | r1_bad AG | ].
all: clear Hc.
all: paj_run_tok RUN HS HJ SHOK r1_Bspan.
all: try awr_ok_tac.
all: r1_rebase HS AG. all: r1_updn AG HOK Hlen' HI HLA. all: clear_frames.
all: psrr_branch_tok RUN BR HS SHOK r1_Bspan.
all: [> r1_bad AG | | r1_bad AG | | r1_bad AG | ].
all: clear Hc E19w.
all: paj_run_tok RUN HS HJ SHOK r1_Bspan.
all: try (lazymatch goal with |- range_addressable _ _ _ _ =>
  cbn [ms_mem]; rewrite <- (aview_rd_of SEGS); r1_Ugoal AG;
  lazymatch goal with HIx : binv _ _ _ _ _ _ _ _ |- _ => destruct (vals_at _ _ _ _ _ _ _ _ HOK HIx (fun a H => H)) as (_ & HRVx & _) end;
  apply (range_addressable_sub _ _ V (3 * w)); [exact HRVx | lia | lia] end).
all: try awr_ok_tac.
all: r1_rebase HS AG. all: r1_updn AG HOK Hlen' HI HLA. all: clear_frames.
(* __asan_set_shadow_00 (SHF + 208, 186), then the rest of the row *)
all: pmkst HS.
all: prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1;
  prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp; prreg HS (1%bv : bv 5) Rra.
all: r1_rfact AG Ra0; r1_rfact AG Rsp; r1_rfact AG Rgp; r1_rfact AG Rtp.
all: rregU HS (18%bv : bv 5) vb ltac:(rewrite U_zext; r1_Ugoal AG; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia) R18v.
all: eapply (call_ss fpos RowsE 0 (SIGMA GS___asan_set_shadow_00) W2 ly2 S2 _ _ rows _ 11932 (SHa fpos + 208) 186 _
  SS00 HI (or_intror (conj HOK Hlen'))).
all: [> exact Ra0 | exact Ra1 | lia | lia | lia | unfold spZ; rewrite Rsp, unsigned_lit_small by lia; reflexivity
  | exact Rgp | exact Rtp | exact Rra | lia | reflexivity | | exact Ra0 | exact Ra1 | lia | lia | lia
  | unfold spZ; rewrite Rsp, unsigned_lit_small by lia; reflexivity
  | exact Rgp | exact Rtp | exact Rra | lia | reflexivity | | exact Ra0 | exact Ra1 | lia | lia | lia
  | unfold spZ; rewrite Rsp, unsigned_lit_small by lia; reflexivity
  | exact Rgp | exact Rtp | exact Rra | lia | reflexivity | ].
all: intros mem3 md3 regs3 HI3 Hv3 Hout3 Hpres3 HP3.
all: lazymatch goal with |- SRr _ _ _ (L1post _ (?q + 1) _) =>
  apply (r1_tail fpos q rows W2 ly2 S2 regs3 mem3 md3 HOK ltac:(lia) HI3 Hlen) end.
all: lazymatch goal with |- l1regs _ _ _ => solve [unfold l1regs, rB; repeat split; r1_apclose HP3 HS AG]
  | |- getr _ _ = _ => solve [rewrite (r1_ap_eq _ _ (18%bv : bv 5) HP3) by (unfold acallee_saved; change (bv_unsigned (18%bv : bv 5)) with 18; lia); exact R18v]
  | |- loc_acc _ _ => solve [eapply (r1_loc_acc_kept fpos (w_H W2) (w_H W2) _ mem3); [intros a Ha; apply Hout3; lia | exact HLA]]
  | |- forall i, _ => solve [intros i Hi; exact (Hv3 i Hi)]
  | |- _ => lia end.
Qed.

(* ---- S5: one row of channel c >= 1 (0x83a40 .. 0x83b24), over the scratch F + 32, and the outer loop ----- *)
(* piece o2: row2 and outer. The symbolic states name the shadow base SBV by atom 33 (the chunk at sp1 + 0x68). *)
Definition o2_Bx : sv := SOff 33 0.
Definition o2_Bspan : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).
Definition o2_Bspan0 : Z * Z := (0, 0).
(* F's shadow byte 190, written by the body at 0x83ac8 (base atom 23 = s7 = SHF) *)
Definition o2_rsh : YP09.region := YP09.mkRegion (Some 23%nat) 190 191 190 191 [].
Lemma o2_nth_mapu : forall (l : list byte) j, nth j (map bv_unsigned l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof. induction l as [|x l IH]; intros [|j]; cbn; try reflexivity. apply IH. Qed.
Lemma o2_sltu_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  alu64 ALU_SLTU (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (if x <? y then 1 else 0).
Proof. intros x y Hx Hy. cbn [alu64 alu]. unfold bv_ltu. rewrite !unsigned_lit_small by lia. destruct (x <? y); reflexivity. Qed.
Lemma o2_and255 : forall p, 0 <= p < 256 -> alu64 ALU_AND (Z_to_bv 64 p) (Z_to_bv 64 255) = Z_to_bv 64 p.
Proof.
  intros p Hp. apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned, !unsigned_lit_small by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma o2_xor_self : forall x : word, alu64 ALU_XOR x x = Z_to_bv 64 0.
Proof. intros x. apply bv_eq. cbn [alu64 alu]. rewrite bv_xor_unsigned, Z.lxor_nilpotent. reflexivity. Qed.
Lemma o2_rows_noimg : bgs_ok s V mx base w -> forall a, RowsE a -> ~ in_img SEGS a.
Proof.
  intros HOK a Ha Hi. destruct (HROWS HOK) as (_ & _ & Himg & _). pose proof (pa_img_range a Hi) as HR.
  unfold RowsE in Ha. destruct Himg; lia.
Qed.
(* F's bytes and its shadow are apart, and both lie in no block of the caller, hence not in the rows *)
Lemma o2_fsh : forall fpos, 4096 <= Fa fpos -> Fa fpos + 4096 <= 2 ^ 47 - 8 -> amem_range (Fa fpos) 4096 ->
  SBV <= SHa fpos /\ (SHa fpos + 512 <= Fa fpos \/ Fa fpos + 4096 <= SHa fpos).
Proof.
  intros fpos H1 H2 H3. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold SHa, SBV. unfold amem_range in H3.
  pose proof (Z.div_mod (Fa fpos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Fa fpos) 8 ltac:(lia)). lia.
Qed.
Lemma o2_own6_rows : forall fpos a, bgs_ok s V mx base w -> own_ok (own6 fpos) -> own6 fpos a -> ~ RowsE a.
Proof.
  intros fpos a HOK HOWN H6 HR. destruct (HOWN a H6) as (_ & _ & Hblk & _).
  destruct (HROWS HOK) as (_ & _ & _ & _ & _ & _ & (b & m & Hin & Hb1 & Hb2) & _). unfold RowsE in HR.
  apply (Hblk b m (a - b) Hin); lia.
Qed.
Ltac o2_mkshok HS SHOK := lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) => assert (SHOK : sh_ok SEGS o2_Bx [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by (apply Forall_nil)
  | st_ok _ ?Ex _ (restrict (w_H ?Wx) ?msx) => assert (SHOK : sh_ok SEGS o2_Bx [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by (apply Forall_nil) end.
Ltac o2_rebase HS AG := let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv;
  repeat (match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end);
  let SH := fresh "SHOK" in o2_mkshok HS SH; cbn [ms_mem mkst] in SH.
Ltac o2_rfact AG H :=
  repeat (progress (rewrite AG in H by nat_side));
  repeat match type of H with context [ew ?Ex ?n] => match goal with En : ew Ex n = _ |- _ => rewrite En in H end end.
(* the trap side of a guard whose condition is xori (xor (sltu x y) 0) 1 with y <= x *)
Ltac o2_refute_sltu Hc AG :=
  exfalso; cbn [sv_denot] in Hc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc; o2_rfact AG Hc;
  rewrite o2_sltu_lit in Hc by lia; rewrite (proj2 (Z.ltb_ge _ _)) in Hc by lia; vm_compute in Hc; discriminate Hc.
(* an address a outside every write window of a run: the windows are the stack window (atom 9) and F's shadow byte
   190 (atom 23); a is in the stack, F, the rows, or is not own6 *)
Ltac o2_wclose AG Hw :=
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; o2_rfact AG Hw; rewrite ?unsigned_lit_small in Hw by lia_nd;
  first [ lia_nd
        | lazymatch goal with HSHF : SHa ?f + 512 <= Fa ?f \/ _ |- _ => destruct HSHF; lia_nd end
        | lazymatch goal with Hn6 : ~ own6 ?f _ |- _ => apply Hn6; unfold own6; lia_nd end
        | lazymatch goal with Hrw : spZ regs <= s \/ _ |- _ => destruct Hrw; lia_nd end
        | lazymatch goal with HOK : bgs_ok _ _ _ _ _, OWN : own_ok (own6 ?f) |- _ =>
          lazymatch type of Hw with _ <= ?x < _ =>
            exfalso; apply (o2_own6_rows f x HOK OWN); [unfold own6; lia_nd | unfold RowsE, bgs_rows; lia_nd] end end ].
Ltac o2_nowin AG := let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros (r & Hr & Hw); lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
  cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [o2_wclose AG Hw |]); try destruct Hr.
(* a run keeps the invariant: before the rebase, AG speaks of the run's start environment *)
Ltac o2_upd HOK AG HIold HInew :=
  lazymatch type of HIold with binv ?fp ?Ex ?Wx ?lyx ?Sx ?m0 ?mdo ?rws =>
  lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ m0) (mrestrict _ (ms_mem ?m1)) |- _ =>
  lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem m1) ?mdx _, HG : mem_grows (mrestrict _ m0) _ |- _ =>
  assert (HInew : binv fp Ex Wx lyx Sx (ms_mem m1) mdx rws) by
   (apply (binv_kept fp Ex Ex Wx lyx Sx m0 mdo rws (ms_mem m1) mdx HIold HJx (fun a H => H));
    [ exact (o2_rows_noimg HOK)
    | intros o2a o2Ha o2Hs o2HE o2H6; apply (aview_kept_out Eo rs _ _ _ HFr o2a o2Ha); o2_nowin AG
    | intros o2a o2Ha; apply (aview_kept_out Eo rs _ _ _ HFr o2a ltac:(lia_nd)); o2_nowin AG
    | intros o2a o2Ha; apply (aview_kept_out Eo rs _ _ _ HFr o2a ltac:(lia_nd)); o2_nowin AG
    | intros o2a o2Ha; apply (aview_kept_out Eo rs _ _ _ HFr o2a ltac:(lia_nd)); o2_nowin AG
    | intros o2a o2Ha; rewrite ?length_app, ?len_GAz in o2Ha; apply (aview_kept_out Eo rs _ _ _ HFr o2a ltac:(lia_nd)); o2_nowin AG
    | intros o2a _ o2Hp; exact (apresent_grows _ _ _ o2a HG o2Hp) ])
  end end end.
(* the stack region (atom 9, [16, 128), no window) is kept by a call that keeps [sp1 + 16, sp1 + 128) *)
Ltac o2_kept AG HK :=
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; o2_rfact AG Ha; rewrite unsigned_lit_small in Ha by lia_nd;
    apply (mbyte_of_aview SEGS); HK a Ha
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; lia ].
Ltac o2_cr := first [change (8 * Z.of_N 8) with 64 | change (8 * Z.of_N 1) with 8]; lia_nd.
Ltac o2_awr AG E9 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc lyx ownx) end;
  repeat (eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat sp1);
          [ reflexivity | try (rewrite (AG 9%nat) by nat_side); rewrite E9; apply unsigned_lit_small; lia_nd
          | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; left; lia_nd | ]);
  apply awr_ok_nil.
Ltac o2_regs_close HS AG :=
  lazymatch goal with |- getr _ ?r = w64 _ =>
  let H := fresh "Rx" in prreg HS r H; o2_rfact AG H; rewrite H; clear H; unfold w64;
  rewrite ?unsigned_lit_small by lia_nd; first [reflexivity | f_equal; lia_nd] end.
(* the end of row2: the invariant, the registers and the locals at 0x83a40 or 0x83b38 *)
Ltac o2_denclose AG :=
  repeat match goal with |- context [ew ?Ex ?n] =>
    first [ match goal with H : ew Ex n = _ |- _ => rewrite H end | progress (rewrite (AG n) by nat_side) ] end;
  rewrite ?unsigned_lit_small by lia_nd; rewrite ?o2_and255, ?o2_xor_self, ?o2_sltu_lit by lia_nd;
  first [reflexivity | f_equal; lia_nd].
Ltac o2_fclose AG E9 := lazymatch goal with
  | |- bv_unsigned (ew _ 9) = _ => try (rewrite (AG 9%nat) by nat_side); rewrite E9; apply unsigned_lit_small; lia_nd
  | |- In _ _ => cbn; tauto
  | |- sv_denot _ _ = _ => cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; o2_denclose AG
  | |- 0 <= _ < _ => o2_cr
  | |- Z.of_N _ <= 8 => cbn; lia
  end.
Ltac o2_fld AG E9 RG off e := apply (field_of_region _ _ 9 sp1 _ 16 128 0 0 off 8 e _ RG); o2_fclose AG E9.
Ltac o2_r2_fin Hp1 :=
  lazymatch goal with HOK : bgs_ok _ _ _ _ _, AG : forall n, _ -> ew _ n = _, HI14 : binv _ _ _ _ _ _ _ _,
                      HS : st_ok_pi _ _ _ _ (restrict (w_H ?Wx) _), E9 : ew _ 9 = _ |- _ =>
  let HIn := fresh "HIn" in let RG := fresh "RG" in
  o2_upd HOK AG HI14 HIn; clear_frames; clear HI14; o2_rebase HS AG;
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ss) o2_rsh) in
    pose proof (st_ok_pi_region_nth Ev ss (restrict (w_H Wx) msx) 0 r HS ltac:(vm_compute; reflexivity)) as RG end;
  cbn [ms_mem restrict] in RG;
  pmkst HS; apply SRr_ret; unfold I2post;
  lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ (ms_mem ?m1) ?mdx _ |- _ =>
    exists lyx, Sx, (ms_regs m1), (ms_mem m1), mdx end;
  split; [rewrite Hp1; reflexivity|];
  split; [exact HIn|];
  split; [unfold i2regs, rB; repeat split; o2_regs_close HS AG|];
  split; [unfold loc_acc; repeat split; [o2_fld AG E9 RG 64 (SOff 44 0) | o2_fld AG E9 RG 32 (SOff 43 0)
                                        | o2_fld AG E9 RG 80 (SOff 45 0) | o2_fld AG E9 RG 88 (SOff 46 0)]|];
  split; [unfold loc_out; split; [o2_fld AG E9 RG 40 (SOff 38 0) | o2_fld AG E9 RG 72 (SOff 36 0)]|];
  unfold loc_in; repeat split; [o2_fld AG E9 RG 16 (SOff 41 0) | o2_fld AG E9 RG 24 (SOff 42 0)
                               | o2_fld AG E9 RG 48 (SOff 37 0) | o2_fld AG E9 RG 56 (SLit 0)]
  end.
(* row2's entry 0x83a40: the stack locals (base atom 9 = s1 = sp1) and the value V[3c+p] (base atom 40) *)
Definition o2_ss_r2 : sstate := mkSS 0x3004 sr_atoms
  [YP09.mkRegion (Some 9%nat) 16 128 0 0
     [YP09.mkChunk 16 (CVal 8 (SOff 41 0)); YP09.mkChunk 24 (CVal 8 (SOff 42 0)); YP09.mkChunk 32 (CVal 8 (SOff 43 0));
      YP09.mkChunk 40 (CVal 8 (SOff 38 0)); YP09.mkChunk 48 (CVal 8 (SOff 37 0)); YP09.mkChunk 56 (CVal 8 (SLit 0));
      YP09.mkChunk 64 (CVal 8 (SOff 44 0)); YP09.mkChunk 72 (CVal 8 (SOff 36 0)); YP09.mkChunk 80 (CVal 8 (SOff 45 0));
      YP09.mkChunk 88 (CVal 8 (SOff 46 0)); YP09.mkChunk 104 (CVal 8 (SOff 33 0));
      YP09.mkChunk 112 (CVal 8 (SOff 34 0)); YP09.mkChunk 120 (CVal 8 (SOff 35 0))];
   YP09.mkRegion (Some 40%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF 3 141 0); (21%nat, mkAF 0 2 0); (25%nat, mkAF 1 (2 ^ 47) 0);
            (26%nat, mkAF 11 151 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0x7fff8000 0x7fff8000 0);
            (36%nat, mkAF (2 ^ 31 - 150) (2 ^ 31 - 12) 0); (39%nat, mkAF 3 143 0); (40%nat, mkAF 4 (2 ^ 47 - 2) 0)] []
           [(SAlu ALU_ADD (SOff 20 0) (SOff 21 0), SOff 39 0); (SAlu ALU_ADD (SOff 39 0) (SOff 34 0), SOff 40 0)]).
Lemma row2 : forall fpos c p rows W2 ly2 S2 regs2 mem2 md2, bgs_ok s V mx base w -> 1 <= c < w -> 0 <= p < 3 ->
  binv fpos RowsE W2 ly2 S2 mem2 md2 rows -> Z.of_nat (length rows) = 34 * (3 * c + 8 + p) ->
  i2regs fpos regs2 c p -> loc_acc fpos (mrestrict (w_H W2) mem2) -> loc_out fpos (mrestrict (w_H W2) mem2) c ->
  loc_in (mrestrict (w_H W2) mem2) c ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x3004)) mem2 (seg_rom SEGS)) md2)
    (I2post fpos c (p + 1) (rows ++ GAz (base + c) p (vz vals (Z.to_nat (3 * c + p))))).
Proof.
intros fpos c p rows W2 ly2 S2 regs2 mem2 md2 HOK Hcw Hp HI Hlen
  ((R2 & R3 & R4 & R8 & R9) & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27) HLA HLO HLI.
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO. pose proof (paj_branch (PI := PI)) as BR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof sp1_facts as (Q1 & Q2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STKB = 4624) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (binv_frame _ _ _ _ _ _ _ _ HI) as (F64 & F4096 & Fceil & _ & F47 & Famr & _ & _ & OWN).
destruct (o2_fsh fpos F4096 F47 Famr) as (HSH0 & HSHF). unfold SBV in HSH0.
assert (HSHc : SHa fpos + 512 <= alloc_ceiling) by (destruct (OWN (SHa fpos + 511) ltac:(unfold own6; lia_nd)) as (H & _); lia_nd).
destruct (vals_at _ _ _ _ _ _ _ _ HOK HI (fun a H => H)) as (HGV & _ & HV0 & HV47 & Hvlen & Hvleg).
pose proof HOK as (Hs0 & HVn0 & Hw1 & Hbw & Hmx). unfold bgs_rows in Hmx.
destruct (HROWS HOK) as (_ & Hs47 & _ & _ & _ & _ & _ & Hrwin & _). unfold bgs_rows in *.
destruct (HVALS ltac:(lia) HVn0) as (_ & _ & _ & _ & _ & HVwin).
pose proof HI as (HJ & Hfr & _ & _ & _ & _ & HL0 & _).
destruct HL0 as (L60 & L68 & L70 & L78).
destruct HLA as (L40 & L20 & L50 & L58). destruct HLO as (L28 & L48). destruct HLI as (L10 & L18 & L30 & L38).
set (vb := vz vals (Z.to_nat (3 * c + p))).
destruct (garr8_nthZ SEGS _ V (map bv_unsigned vals) (3 * c + p) HGV ltac:(lia_nd) ltac:(rewrite length_map, Hvlen; lia_nd)) as [Mvb Rvb].
rewrite o2_nth_mapu in Mvb, Rvb. change (bv_unsigned (nth (Z.to_nat (3 * c + p)) vals (Z_to_bv 8 0))) with vb in Mvb, Rvb.
clear HGV.
assert (Hleg : legalb p vb = true).
{ apply bgs_legal_legalb. pose proof (Hvleg (Z.to_nat (3 * c + p)) ltac:(lia_nd)) as L.
  replace (Z.of_nat (Z.to_nat (3 * c + p) mod 3)) with p in L; [exact L|].
  replace (Z.to_nat (3 * c + p)) with (Z.to_nat p + Z.to_nat c * 3)%nat by lia_nd.
  rewrite Nat.Div0.mod_add, Nat.mod_small by lia_nd. lia_nd. }
remember (Eimg (Ereg regs2 [Z_to_bv 64 vb; Z_to_bv 64 SBV; Z_to_bv 64 V; Z_to_bv 64 s; Z_to_bv 64 (2 ^ 31 - 9 - 3 * c);
  Z_to_bv 64 (base + c); Z_to_bv 64 (Fa fpos + 48); Z_to_bv 64 (3 * c + p); Z_to_bv 64 (V + (3 * c + p));
  Z_to_bv 64 c; Z_to_bv 64 (3 * c + 11); Z_to_bv 64 w; Z_to_bv 64 (Fa fpos); Z_to_bv 64 (SHa fpos + 4);
  Z_to_bv 64 (Fa fpos + 32)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 15)%nat -> ew E (32 + j) = nth j [Z_to_bv 64 vb; Z_to_bv 64 SBV; Z_to_bv 64 V; Z_to_bv 64 s;
  Z_to_bv 64 (2 ^ 31 - 9 - 3 * c); Z_to_bv 64 (base + c); Z_to_bv 64 (Fa fpos + 48); Z_to_bv 64 (3 * c + p); Z_to_bv 64 (V + (3 * c + p));
  Z_to_bv 64 c; Z_to_bv 64 (3 * c + 11); Z_to_bv 64 w; Z_to_bv 64 (Fa fpos); Z_to_bv 64 (SHa fpos + 4);
  Z_to_bv 64 (Fa fpos + 32)] (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ j)).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite R19 in E19.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite R20 in E20.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite R21 in E21.
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite R22 in E22.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite R23 in E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite R24 in E24.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite R25 in E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite R26 in E26.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite R27 in E27.
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39. pose proof (EX 8%nat ltac:(lia)) as E40.
pose proof (EX 9%nat ltac:(lia)) as E41. pose proof (EX 10%nat ltac:(lia)) as E42. pose proof (EX 11%nat ltac:(lia)) as E43.
pose proof (EX 12%nat ltac:(lia)) as E44. pose proof (EX 13%nat ltac:(lia)) as E45. pose proof (EX 14%nat ltac:(lia)) as E46.
cbn [nth Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46.
unfold w64 in E2, E3, E4, E8, E9, E19, E20, E21, E22, E23, E24, E25, E26, E27.
assert (HS : st_ok_pi SEGS VAL E o2_ss_r2 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x3004)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold o2_ss_r2. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E9, unsigned_lit_small by lia_nd. split; [lia_nd|]. split; [lia_nd|]. split; [intros o Ho; lia_nd|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp1 16 8 (SOff 41 0) c);
      [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L10].
    * apply (chunk_ok_val SEGS E _ sp1 24 8 (SOff 42 0) (3 * c + 11));
      [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L18].
    * apply (chunk_ok_val SEGS E _ sp1 32 8 (SOff 43 0) w);
      [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L20].
    * apply (chunk_ok_val SEGS E _ sp1 40 8 (SOff 38 0) (Fa fpos + 48));
      [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L28].
    * apply (chunk_ok_val SEGS E _ sp1 48 8 (SOff 37 0) (base + c));
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L30].
    * apply (chunk_ok_val SEGS E _ sp1 56 8 (SLit 0) 0); [reflexivity | o2_cr | lia_nd | exact L38].
    * apply (chunk_ok_val SEGS E _ sp1 64 8 (SOff 44 0) (Fa fpos));
      [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L40].
    * apply (chunk_ok_val SEGS E _ sp1 72 8 (SOff 36 0) (2 ^ 31 - 9 - 3 * c));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L48].
    * apply (chunk_ok_val SEGS E _ sp1 80 8 (SOff 45 0) (SHa fpos + 4));
      [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L50].
    * apply (chunk_ok_val SEGS E _ sp1 88 8 (SOff 46 0) (Fa fpos + 32));
      [cbn [sv_denot]; rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L58].
    * apply (chunk_ok_val SEGS E _ sp1 104 8 (SOff 33 0) SBV);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBV; o2_cr | lia_nd | exact L68].
    * apply (chunk_ok_val SEGS E _ sp1 112 8 (SOff 34 0) V);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L70].
    * apply (chunk_ok_val SEGS E _ sp1 120 8 (SOff 35 0) s);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L78].
  + rewrite E40, unsigned_lit_small by lia_nd. split; [lia_nd|]. split; [lia_nd|]. split; [intros o Ho; lia_nd|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (V + (3 * c + p)) 0 1 (SOff 32 0) vb);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | rewrite Z.add_0_r; exact Mvb].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E40, !unsigned_lit_small by lia_nd.
  split; [split; [destruct HVwin; lia_nd | exact I] | split; exact I].
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E20, E21, E25, E26, E32, E33, E36, E39, E40, !unsigned_lit_small by (unfold SBV; lia_nd).
    rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. unfold SBV. repeat split; lia_nd.
  + cbn [alias_ok]. split; [|split; [|exact I]]; apply U_inj.
    * rewrite (U_add_small E (SOff 20 0) (SOff 21 0) (3 * c) p); [| apply U_atom; [exact E20 | lia_nd] | apply U_atom; [exact E21 | lia_nd] | lia_nd | lia_nd | lia_nd].
      rewrite (U_atom E 39 (3 * c + p) E39) by lia_nd. reflexivity.
    * rewrite (U_add_small E (SOff 39 0) (SOff 34 0) (3 * c + p) V); [| apply U_atom; [exact E39 | lia_nd] | apply U_atom; [exact E34 | lia_nd] | lia_nd | lia_nd | lia_nd].
      rewrite (U_atom E 40 (V + (3 * c + p)) E40) by lia_nd. lia_nd. }
assert (SHOK : sh_ok SEGS o2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
clear HE EE EX L10 L18 L20 L28 L30 L38 L40 L48 L50 L58 L68 L70 L78 Mvb.
(* run 1: to the guard s9 >= s (0x83a60) *)
paj_run_tok RUN HS HJ SHOK o2_Bspan. { awr_ok_tac. }
o2_upd HOK AG HI HI1. clear_frames. clear HI. o2_rebase HS AG.
psrr_branch_tok RUN BR HS SHOK o2_Bspan.
{ o2_refute_sltu Hc AG. }
clear Hc.
(* run 2: to the guard V + 3c + p >= V (0x83a9c) *)
paj_run_tok RUN HS HJ SHOK o2_Bspan. { awr_ok_tac. }
o2_upd HOK AG HI1 HI2. clear_frames. clear HI1. o2_rebase HS AG.
psrr_branch_tok RUN BR HS SHOK o2_Bspan.
{ o2_refute_sltu Hc AG. }
clear Hc.
(* run 3: the shadow of V[3c+p] and its load, to __asan_set_shadow_00 (SHF + 4, 186) at 0x83ac0 *)
destruct (vals_at _ _ _ _ _ _ _ _ HOK HI2 (fun a H => H)) as (_ & HRV & _).
paj_run_tok RUN HS HJ SHOK o2_Bspan.
{ rewrite <- (aview_rd_of SEGS). unfold o2_Bx. rewrite (U_atom _ 33 SBV E33) by (unfold SBV; lia_nd).
  rewrite (U_atom _ 40 (V + (3 * c + p)) E40) by lia_nd. unfold SBV. change 2147450880 with SHADOW_OFF.
  apply (range_addressable_sub _ _ V (3 * w)); [exact HRV | lia_nd | lia_nd]. }
{ awr_ok_tac. }
o2_upd HOK AG HI2 HI3. clear_frames. clear HI2 HRV. o2_rebase HS AG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (2%bv : bv 5) Rsp.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
o2_rfact AG Ra0. o2_rfact AG Rsp. o2_rfact AG Rgp. o2_rfact AG Rtp.
pmkst HS.
eapply (call_ss fpos RowsE 0 _ W2 ly2 S2 _ _ rows _ 0x3088 (SHa fpos + 4) 186 _ SS00 HI3);
  [ right; split; [exact HOK | unfold bgs_rows; lia_nd] | exact Ra0 | exact Ra1 | lia | lia_nd | lia_nd
  | unfold spZ; rewrite Rsp, unsigned_lit_small by lia_nd; reflexivity | exact Rgp | exact Rtp | exact Rra | lia | reflexivity | ].
intros mem4 md4 regs4 HI4 HZ4 HK4 _ HP4. clear Ra0 Ra1 Rsp Rgp Rtp Rra.
pose proof (proj1 HI4) as HJ4.
reseat HS HJ4 HP4 [0]%nat AG ltac:(o2_kept AG ltac:(fun a Ha => apply HK4; [lia_nd | lia_nd])).
try clear SHOK. o2_mkshok HS SHOK. cbn [ms_mem] in SHOK.
destruct (binv_frame _ _ _ _ _ _ _ _ HI4) as (_ & _ & _ & _ & _ & _ & _ & SPr4 & _).
destruct (binv_layout _ _ _ _ _ _ _ _ HI4) as (_ & _ & _ & EF4 & _).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss ?msx =>
  assert (HS' : st_ok_pi SEGS VAL Ev (mkSS (ss_pc ss) (ss_regs ss) (o2_rsh :: ss_mem ss) (ss_resv ss) (ss_facts ss)) msx)
  by (apply (st_ok_pi_add_region Ev ss msx o2_rsh HS);
      [ vm_compute; reflexivity
      | unfold region_ok, o2_rsh; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite (AG 23%nat) by lia; rewrite E23, unsigned_lit_small by lia_nd;
        split; [lia_nd|]; split; [lia_nd|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable SEGS); apply (proj1 (SPr4 (SHa fpos + o) ltac:(lia_nd)))
      | let sm := eval vm_compute in (ss_mem ss) in change (ss_mem ss) with sm;
        cbn [all_disjoint]; unfold extent_disjoint, o2_rsh; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite (AG 23%nat), (AG 9%nat) by lia; rewrite E23, E9, !unsigned_lit_small by lia_nd; split; [lia_nd | exact I] ])
end.
clear HS. rename HS' into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss ?msx =>
  assert (HS' : st_ok_pi SEGS VAL Ev (add_atom ss 23 (mkAF 0x7fff8000 (2 ^ 47) 0)) msx)
  by (apply (st_ok_pi_add_fact Ev ss msx 23 _ HS); unfold afact_ok; cbn [af_lo af_hi af_al2];
      rewrite (AG 23%nat) by lia; rewrite E23, unsigned_lit_small by lia_nd; rewrite Z.pow_0_r, Z.mod_1_r; lia_nd)
end.
clear HS. rename HS' into HS. norm_ss HS.
(* run 4: SHF + 190 = 4, to __asan_memset (F + 32, 0, 1492) at 0x83ad8; no shadow check here, so the span is empty *)
paj_run_tok RUN HS HJ4 SHOK o2_Bspan0.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc lyx ownx) end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat (SHa fpos));
    [reflexivity | rewrite (AG 23%nat) by lia; rewrite E23; apply unsigned_lit_small; lia_nd | | awr_ok_tac].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 6, fpos. split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite EF4. replace (shadow_addr (frame_addr lyc 6 fpos)) with (SHa fpos) by reflexivity.
  change (fs_frame_bytes 6 / 8) with 512. lia_nd. }
o2_upd HOK AG HI4 HI5.
lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ mem4) (mrestrict _ (ms_mem ?m1)) |- _ =>
  assert (HZ5 : forall i, 0 <= i < 186 -> aview SEGS (w_H W2) (ms_mem m1) (SHa fpos + 4 + i) = Some 0)
    by (intros i Hi; rewrite (aview_kept_out Eo rs _ _ _ HFr (SHa fpos + 4 + i) ltac:(lia_nd)) by o2_nowin AG; exact (HZ4 i Hi))
end.
clear_frames. clear HI4 HZ4 HK4 SPr4. o2_rebase HS AG.
lazymatch type of HS with st_ok _ ?Ev ?ss (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 0 (ss_mem ss) o2_rsh) in
  pose proof (st_ok_region_nth Ev ss (restrict (w_H W2) msx) 0 r HS ltac:(vm_compute; reflexivity)) as RG end.
cbn [ms_mem restrict] in RG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  assert (S190 : aview SEGS (w_H W2) (ms_mem msx) (SHa fpos + 4 + 186) = Some 4) end.
{ apply (aview_of_val_mem1 SEGS); [|lia]. replace (SHa fpos + 4 + 186) with (SHa fpos + 190) by lia.
  apply (field_of_region _ _ 23 (SHa fpos) _ 190 191 190 191 190 1 (SLit 4) 4 RG);
  [rewrite (AG 23%nat) by lia; rewrite E23; apply unsigned_lit_small; lia_nd | cbn; tauto | reflexivity | o2_cr | cbn; lia]. }
clear RG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (2%bv : bv 5) Rsp.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
o2_rfact AG Ra0. o2_rfact AG Rsp. o2_rfact AG Rgp. o2_rfact AG Rtp.
pmkst HS.
eapply (call_memset fpos W2 ly2 S2 _ _ rows _ 0x30a0 32 _ HOK ltac:(unfold bgs_rows; lia_nd) HI5 (or_introl eq_refl));
  [ apply (ra_scratch fpos _ 32 (or_introl eq_refl) F64); [exact HZ5 | exact S190]
  | exact Ra0 | exact Ra1 | exact Ra2 | unfold spZ; rewrite Rsp, unsigned_lit_small by lia_nd; reflexivity
  | exact Rgp | exact Rtp | exact Rra | lia | reflexivity | ].
intros mem6 md6 regs6 HI6 _ HK6 HP6. clear Ra0 Ra1 Ra2 Rsp Rgp Rtp Rra.
assert (HZ6 : forall i, 0 <= i < 186 -> aview SEGS (w_H W2) mem6 (SHa fpos + 4 + i) = Some 0)
  by (intros i Hi; rewrite HK6 by (destruct HSHF; lia_nd); exact (HZ5 i Hi)).
assert (Sh6 : aview SEGS (w_H W2) mem6 (SHa fpos + 4 + 186) = Some 4) by (rewrite HK6 by (destruct HSHF; lia_nd); exact S190).
pose proof (proj1 HI6) as HJ6.
reseat HS HJ6 HP6 [1]%nat AG ltac:(o2_kept AG ltac:(fun a Ha => apply HK6; [lia_nd | lia_nd | lia_nd])).
clear HI5 HZ5 S190 HK6.
try clear SHOK. o2_mkshok HS SHOK. cbn [ms_mem] in SHOK.
(* run 5: to reac_ctrl_stamp_headamp (F + 32, base + c, p, V[3c+p]) at 0x83aec *)
paj_run_tok RUN HS HJ6 SHOK o2_Bspan. { awr_ok_tac. }
o2_upd HOK AG HI6 HI7.
lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ mem6) (mrestrict _ (ms_mem ?m1)) |- _ =>
  assert (HZ7 : forall i, 0 <= i < 186 -> aview SEGS (w_H W2) (ms_mem m1) (SHa fpos + 4 + i) = Some 0)
    by (intros i Hi; rewrite (aview_kept_out Eo rs _ _ _ HFr (SHa fpos + 4 + i) ltac:(lia_nd)) by o2_nowin AG; exact (HZ6 i Hi));
  assert (Sh7 : aview SEGS (w_H W2) (ms_mem m1) (SHa fpos + 4 + 186) = Some 4)
    by (rewrite (aview_kept_out Eo rs _ _ _ HFr (SHa fpos + 4 + 186) ltac:(lia_nd)) by o2_nowin AG; exact Sh6)
end.
clear_frames. clear HI6 HZ6 Sh6. o2_rebase HS AG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3.
prreg HS (2%bv : bv 5) Rsp. prreg HS (8%bv : bv 5) Rs0. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (1%bv : bv 5) Rra.
o2_rfact AG Ra0. o2_rfact AG Ra1. o2_rfact AG Ra2. o2_rfact AG Ra3. o2_rfact AG Rsp. o2_rfact AG Rs0. o2_rfact AG Rgp.
o2_rfact AG Rtp.
pmkst HS. rewrite pa_sigma_reac_ctrl_stamp_headamp.
eapply (call_stamp fpos W2 ly2 S2 _ _ rows _ 0x30b4 32 (base + c) p vb _ HOK HI7 (or_introl eq_refl) ltac:(unfold bgs_rows; lia_nd));
  [ exact (sh_zero_stamp fpos _ 32 (or_introl eq_refl) F64 HZ7)
  | exact Ra0 | exact Ra1 | rewrite Ra2, o2_and255 by lia_nd; reflexivity | exact Ra3 | lia_nd | lia_nd | lia_nd | exact Hleg
  | unfold spZ; rewrite Rsp, unsigned_lit_small by lia_nd; reflexivity | exact Rs0 | exact Rgp | exact Rtp | exact Rra
  | lia | reflexivity | ].
intros W8 ly8 S8 mem8 md8 regs8 HI8 HKs8 HKh8 _ HP8 R10z HGA.
clear Ra0 Ra1 Ra2 Ra3 Rsp Rs0 Rgp Rtp Rra.
assert (HZ8 : forall i, 0 <= i < 186 -> aview SEGS (w_H W8) mem8 (SHa fpos + 4 + i) = Some 0)
  by (intros i Hi; rewrite HKh8 by lia_nd; exact (HZ7 i Hi)).
assert (Sh8 : aview SEGS (w_H W8) mem8 (SHa fpos + 4 + 186) = Some 4) by (rewrite HKh8 by lia_nd; exact Sh7).
pose proof (proj1 HI8) as HJ8.
reseat HS HJ8 HP8 [0]%nat AG ltac:(o2_kept AG ltac:(fun a Ha => apply HKs8; lia_nd)).
clear HI7 HZ7 Sh7 HKs8 HKh8.
(* run 6: the stamp's result is 0 (0x83af0), then to __asan_memcpy (s + 34 (3c + 8 + p), F + 48, 34) at 0x83b00 *)
prreg HS (10%bv : bv 5) Rz. rewrite R10z in Rz. symmetry in Rz. clear R10z.
try clear SHOK. o2_mkshok HS SHOK. cbn [ms_mem] in SHOK.
paj_run_tok RUN HS HJ8 SHOK o2_Bspan. { awr_ok_tac. }
o2_upd HOK AG HI8 HI9.
lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ mem8) (mrestrict _ (ms_mem ?m1)) |- _ =>
  assert (HZ9 : forall i, 0 <= i < 186 -> aview SEGS (w_H W8) (ms_mem m1) (SHa fpos + 4 + i) = Some 0)
    by (intros i Hi; rewrite (aview_kept_out Eo rs _ _ _ HFr (SHa fpos + 4 + i) ltac:(lia_nd)) by o2_nowin AG; exact (HZ8 i Hi));
  assert (Sh9 : aview SEGS (w_H W8) (ms_mem m1) (SHa fpos + 4 + 186) = Some 4)
    by (rewrite (aview_kept_out Eo rs _ _ _ HFr (SHa fpos + 4 + 186) ltac:(lia_nd)) by o2_nowin AG; exact Sh8);
  assert (HGA9 : garr8 SEGS (mrestrict (w_H W8) (ms_mem m1)) (Fa fpos + 32 + 16) (GAz (base + c) p vb))
    by (apply (garr8_aview_kept SEGS (w_H W8) (w_H W8) mem8 (ms_mem m1)); [|exact HGA];
        intros a Ha; rewrite len_GAz in Ha; change (Z.of_nat 34) with 34 in Ha;
        apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia_nd)); o2_nowin AG)
end.
clear_frames. clear HI8 HZ8 Sh8 HGA. o2_rebase HS AG.
psrr_branch_tok RUN BR HS SHOK o2_Bspan.
{ exfalso. cbn [sv_denot] in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc. rewrite Rz in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc Rz.
paj_run_tok RUN HS HJ8 SHOK o2_Bspan. { awr_ok_tac. }
o2_upd HOK AG HI9 HI10.
lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?m1)) |- _ =>
  assert (HZ10 : forall i, 0 <= i < 186 -> aview SEGS (w_H W8) (ms_mem m1) (SHa fpos + 4 + i) = Some 0)
    by (intros i Hi; rewrite (aview_kept_out Eo rs _ _ _ HFr (SHa fpos + 4 + i) ltac:(lia_nd)) by o2_nowin AG; exact (HZ9 i Hi));
  assert (Sh10 : aview SEGS (w_H W8) (ms_mem m1) (SHa fpos + 4 + 186) = Some 4)
    by (rewrite (aview_kept_out Eo rs _ _ _ HFr (SHa fpos + 4 + 186) ltac:(lia_nd)) by o2_nowin AG; exact Sh9);
  assert (HGA10 : garr8 SEGS (mrestrict (w_H W8) (ms_mem m1)) (Fa fpos + 48) (GAz (base + c) p vb))
    by (apply (garr8_aview_kept SEGS (w_H W8) (w_H W8) m0 (ms_mem m1)); [|replace (Fa fpos + 48) with (Fa fpos + 32 + 16) by lia; exact HGA9];
        intros a Ha; rewrite len_GAz in Ha; change (Z.of_nat 34) with 34 in Ha;
        apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia_nd)); o2_nowin AG)
end.
clear_frames. clear HI9 HZ9 Sh9 HGA9. o2_rebase HS AG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (2%bv : bv 5) Rsp.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
o2_rfact AG Ra0. o2_rfact AG Ra1. o2_rfact AG Rsp. o2_rfact AG Rgp. o2_rfact AG Rtp.
pmkst HS.
destruct (binv_layout _ _ _ _ _ _ _ _ HI10) as (_ & _ & _ & EF10 & _).
pose proof HI10 as (HJ10 & Hfr10 & _).
assert (HL34 : Z.of_nat (length (GAz (base + c) p vb)) = 34) by (rewrite len_GAz; reflexivity).
eapply (call_cpy fpos W8 ly8 S8 _ _ rows _ 0x30c8 (Fa fpos + 48) (GAz (base + c) p vb) _ HOK HI10); rewrite ?HL34;
  [ lia | unfold bgs_rows; lia_nd | exact HGA10 | lia_nd | lia_nd
  | destruct (Z_le_gt_dec (s + Z.of_nat (length rows) + 34) (Fa fpos + 48)) as [Hd|Hd]; [left; exact Hd|]; right;
    destruct (Z_le_gt_dec (Fa fpos + 48 + 34) (s + Z.of_nat (length rows))) as [Hd2|Hd2]; [exact Hd2|]; exfalso;
    apply (o2_own6_rows fpos (Z.max (Fa fpos + 48) (s + Z.of_nat (length rows))) HOK OWN);
    [unfold own6; left; lia_nd | unfold RowsE, bgs_rows; lia_nd]
  | unfold amem_range in Famr |- *; destruct Famr; [left | right]; lia_nd
  | intros a Ha; lia_nd
  | apply (range_addressable_sub _ _ (Fa fpos + 32) 1492); [apply (ra_scratch fpos _ 32 (or_introl eq_refl) F64); [exact HZ10 | exact Sh10] | lia_nd | lia_nd]
  | apply (shadow_hull_vis_of_frame SEGS B LAWS ly8 S8 W8 _ _ 6 fpos (Fa fpos + 48) 34 (proj1 HJ10)); [rewrite Hfr10; left; reflexivity
    | rewrite EF10; change (frame_addr lyc 6 fpos) with (Fa fpos); lia_nd
    | rewrite EF10; change (frame_addr lyc 6 fpos) with (Fa fpos); change (fs_frame_bytes 6) with 4096; lia_nd | lia]
  | rewrite Ra0, Hlen; reflexivity | exact Ra1 | exact Ra2
  | unfold spZ; rewrite Rsp, unsigned_lit_small by lia_nd; reflexivity | exact Rgp | exact Rtp | exact Rra | lia | reflexivity | ].
intros mem11 md11 regs11 HI11 HK11 HP11. clear Ra0 Ra1 Ra2 Rsp Rgp Rtp Rra HL34.
pose proof (proj1 HI11) as HJ11.
reseat HS HJ11 HP11 [0]%nat AG ltac:(o2_kept AG ltac:(fun a Ha => apply HK11; [lia_nd | destruct Hrwin; lia_nd | lia_nd])).
clear HI10 HZ10 Sh10 HGA10 HK11 HJ10 Hfr10 EF10.
(* run 7: to __asan_set_shadow_f8 (SHF + 4, 187) at 0x83b0c *)
try clear SHOK. o2_mkshok HS SHOK. cbn [ms_mem] in SHOK.
paj_run_tok RUN HS HJ11 SHOK o2_Bspan. { awr_ok_tac. }
o2_upd HOK AG HI11 HI12. clear_frames. clear HI11. o2_rebase HS AG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (2%bv : bv 5) Rsp.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
o2_rfact AG Ra0. o2_rfact AG Rsp. o2_rfact AG Rgp. o2_rfact AG Rtp.
pmkst HS.
eapply (call_ss fpos RowsE 0xf8 _ W8 ly8 S8 _ _ (rows ++ GAz (base + c) p vb) _ 0x30d4 (SHa fpos + 4) 187 _ SSF8 HI12);
  [ right; split; [exact HOK | rewrite length_app, len_GAz; unfold bgs_rows; lia_nd] | exact Ra0 | exact Ra1 | lia | lia_nd | lia_nd
  | unfold spZ; rewrite Rsp, unsigned_lit_small by lia_nd; reflexivity | exact Rgp | exact Rtp | exact Rra | lia | reflexivity | ].
intros mem13 md13 regs13 HI13 _ HK13 _ HP13. clear Ra0 Ra1 Rsp Rgp Rtp Rra.
pose proof (proj1 HI13) as HJ13.
reseat HS HJ13 HP13 [0]%nat AG ltac:(o2_kept AG ltac:(fun a Ha => apply HK13; [lia_nd | lia_nd])).
clear HI12 HK13.
(* run 8: the counters and `bne s5, 3` (0x83b24) *)
try clear SHOK. o2_mkshok HS SHOK. cbn [ms_mem] in SHOK.
paj_run_tok RUN HS HJ13 SHOK o2_Bspan. { awr_ok_tac. }
o2_upd HOK AG HI13 HI14. clear_frames. clear HI13. o2_rebase HS AG.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (F21 : ew Ev 21 = Z_to_bv 64 p) by (rewrite AG by lia; exact E21) end.
psrr_branch_tok RUN BR HS SHOK o2_Bspan;
  rewrite branch_ne_U, (U_atom_off _ 21 p 1 F21), U_lit in Hc by lia_nd.
- assert (Hp1 : (p + 1 =? 3) = false) by (destruct (p + 1 =? 3); [discriminate Hc | reflexivity]).
  paj_run_to_tok RUNTO HS HJ13 SHOK o2_Bspan 0x3004. { awr_ok_tac. }
  o2_r2_fin Hp1.
- assert (Hp1 : (p + 1 =? 3) = true) by (destruct (p + 1 =? 3); [reflexivity | discriminate Hc]).
  paj_run_to_tok RUNTO HS HJ13 SHOK o2_Bspan 0x30fc. { awr_ok_tac. }
  o2_r2_fin Hp1.
Qed.

Lemma o2_U_mul_lit : forall E n x kk, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= kk -> x * kk < 2 ^ 64 ->
  U E (SMd M_MUL (SOff n 0) (SLit kk)) = x * kk.
Proof.
  intros E n x kk Hn Hx Hk Hxk. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SOff, U_SLit, Hn, unsigned_lit_small by lia.
  unfold zcanon, M64. rewrite Z.add_0_r, Zmult_mod_idemp_r, Zmult_mod_idemp_l. apply Z.mod_small. nia.
Qed.
(* the outer loop's head 0x839f4: the stores at sp1 + 0x10 .. 0x20 and 0x30 .. 0x40 (two windows), base and s *)
Definition o2_ss_oh : sstate := mkSS 0x2fb8 (sr_set sr_atoms 11%bv (SLit 34))
  [YP09.mkRegion (Some 9%nat) 16 32 16 32 []; YP09.mkRegion (Some 9%nat) 48 64 48 64 [];
   YP09.mkRegion (Some 9%nat) 96 128 0 0 [YP09.mkChunk 96 (CVal 8 (SOff 32 0)); YP09.mkChunk 120 (CVal 8 (SOff 33 0))]] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (13%nat, mkAF 1 47 0); (26%nat, mkAF 11 149 0); (32%nat, mkAF 0 47 0);
            (33%nat, mkAF 1 (2 ^ 47) 0); (34%nat, mkAF 1 47 0); (35%nat, mkAF 1 (2 ^ 47) 0); (36%nat, mkAF 3 141 0)] []
           [(SAlu ALU_ADD (SOff 13 0) (SOff 32 0), SOff 34 0);
            (SAlu ALU_ADD (SOff 33 0) (SMd M_MUL (SOff 26 0) (SLit 34)), SOff 35 0);
            (SMd M_MUL (SOff 13 0) (SLit 3), SOff 36 0)]).
(* the end of a channel 0x83b38: c, 3c + 11, w and F read back, and sp1 + 0x48 lowered by 3 *)
Definition o2_ss_ot : sstate := mkSS 0x30fc sr_atoms
  [YP09.mkRegion (Some 9%nat) 16 72 0 0
     [YP09.mkChunk 16 (CVal 8 (SOff 32 0)); YP09.mkChunk 24 (CVal 8 (SOff 33 0)); YP09.mkChunk 32 (CVal 8 (SOff 34 0));
      YP09.mkChunk 64 (CVal 8 (SOff 35 0))];
   YP09.mkRegion (Some 9%nat) 72 80 72 80 [YP09.mkChunk 72 (CVal 8 (SOff 36 0))]] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 1 47 0); (36%nat, mkAF (2 ^ 31 - 150) (2 ^ 31 - 12) 0)] [] []).
Lemma outer : forall fpos n c W2 ly2 S2 regs2 mem2 md2, bgs_ok s V mx base w -> Z.of_nat n = w - c -> 1 <= c < w ->
  binv fpos RowsE W2 ly2 S2 mem2 md2 (prefixZ c) -> oregs fpos regs2 c ->
  loc_acc fpos (mrestrict (w_H W2) mem2) -> loc_out fpos (mrestrict (w_H W2) mem2) c ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x2fb8)) mem2 (seg_rom SEGS)) md2) TBP.
Proof.
intros fpos n; induction n as [|n IH]; intros c W2 ly2 S2 regs2 mem2 md2 HOK Hn Hcw HI
  ((R2 & R3 & R4 & R8 & R9) & R11 & R13 & R19 & R22 & R23 & R24 & R26) HLA HLO; [lia|].
pose proof (paj_run B LAWS) as RUN. pose proof (paj_run_to B LAWS) as RUNTO. pose proof (paj_branch (PI := PI)) as BR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof sp1_facts as (Q1 & Q2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STKB = 4624) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (binv_frame _ _ _ _ _ _ _ _ HI) as (F64 & F4096 & Fceil & _ & F47 & Famr & _ & _ & OWN).
pose proof HOK as (Hs0 & HVn0 & Hw1 & Hbw & Hmx). unfold bgs_rows in Hmx.
destruct (HROWS HOK) as (_ & Hs47 & _ & _ & _ & _ & _ & Hrwin & _). unfold bgs_rows in *.
pose proof (len_prefixZ c ltac:(lia)) as Hl0.
pose proof HI as (HJ & Hfr & _ & _ & _ & _ & HL0 & _).
destruct HL0 as (L60 & L68 & L70 & L78).
remember (Eimg (Ereg regs2 [Z_to_bv 64 base; Z_to_bv 64 s; Z_to_bv 64 (base + c); Z_to_bv 64 (s + 34 * (3 * c + 8));
  Z_to_bv 64 (3 * c)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r) by (intros n0 r Hn0; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j [Z_to_bv 64 base; Z_to_bv 64 s; Z_to_bv 64 (base + c);
  Z_to_bv 64 (s + 34 * (3 * c + 8)); Z_to_bv 64 (3 * c)] (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ j)).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 11%nat 11%bv eq_refl) as E11. rewrite R11 in E11.
pose proof (EE 13%nat 13%bv eq_refl) as E13. rewrite R13 in E13.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite R19 in E19.
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite R22 in E22.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite R23 in E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite R24 in E24.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite R26 in E26.
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [nth Nat.add] in E32, E33, E34, E35, E36.
unfold w64 in E2, E3, E4, E8, E9, E11, E13, E19, E22, E23, E24, E26.
assert (HS : st_ok_pi SEGS VAL E o2_ss_oh (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x2fb8)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold o2_ss_oh. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite R11; reflexivity].
- vm_compute. reflexivity.
- destruct (binv_frame _ _ _ _ _ _ _ _ HI) as (_ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJP & _).
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  rewrite E9, unsigned_lit_small by lia_nd; split; try lia_nd; split; try lia_nd.
  + split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply HJP. lia_nd.
  + split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply HJP. lia_nd.
  + split; [intros o Ho; lia_nd|]. repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp1 96 8 (SOff 32 0) base);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L60].
    * apply (chunk_ok_val SEGS E _ sp1 120 8 (SOff 33 0) s);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L78].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia_nd.
  repeat split; lia_nd.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E13, E26, E32, E33, E34, E35, E36, !unsigned_lit_small by lia_nd.
    rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. repeat split; lia_nd.
  + cbn [alias_ok]. split; [|split; [|split; [|exact I]]]; apply U_inj.
    * rewrite (U_add_small E (SOff 13 0) (SOff 32 0) c base); [| apply U_atom; [exact E13 | lia_nd] | apply U_atom; [exact E32 | lia_nd] | lia_nd | lia_nd | lia_nd].
      rewrite (U_atom E 34 (base + c) E34) by lia_nd. lia_nd.
    * rewrite (U_add_small E (SOff 33 0) (SMd M_MUL (SOff 26 0) (SLit 34)) s ((3 * c + 8) * 34));
        [| apply U_atom; [exact E33 | lia_nd] | apply o2_U_mul_lit; [exact E26 | lia_nd | lia_nd | lia_nd] | lia_nd | lia_nd | lia_nd].
      rewrite (U_atom E 35 (s + 34 * (3 * c + 8)) E35) by lia_nd. lia_nd.
    * rewrite (o2_U_mul_lit E 13 c 3 E13) by lia_nd. rewrite (U_atom E 36 (3 * c) E36) by lia_nd. lia_nd. }
assert (SHOK : sh_ok SEGS o2_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
clear HE EE EX L60 L78.
(* the head, to the inner loop 0x83a40 *)
paj_run_to_tok RUNTO HS HJ SHOK o2_Bspan 0x3004.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?lyx ?ownx =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc lyx ownx) end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat sp1); [reflexivity | rewrite E9; apply unsigned_lit_small; lia_nd | | ].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. lia_nd. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat sp1); [reflexivity | rewrite E9; apply unsigned_lit_small; lia_nd | | awr_ok_tac].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. lia_nd. } }
o2_upd HOK AG HI HI1.
lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ mem2) (mrestrict _ (ms_mem ?m1)) |- _ =>
  assert (HLA1 : loc_acc fpos (mrestrict (w_H W2) (ms_mem m1)))
    by (destruct HLA as (X1 & X2 & X3 & X4); repeat split;
        (eapply (val_mem_aview_kept_x SEGS (w_H W2) (w_H W2) mem2 (ms_mem m1)); [|eassumption]);
        intros x Hx; apply (aview_kept_out Eo rs _ _ _ HFr x ltac:(lia_nd)); o2_nowin AG);
  assert (HLO1 : loc_out fpos (mrestrict (w_H W2) (ms_mem m1)) c)
    by (destruct HLO as (X1 & X2); split;
        (eapply (val_mem_aview_kept_x SEGS (w_H W2) (w_H W2) mem2 (ms_mem m1)); [|eassumption]);
        intros x Hx; apply (aview_kept_out Eo rs _ _ _ HFr x ltac:(lia_nd)); o2_nowin AG)
end.
clear_frames. clear HI HLA HLO. o2_rebase HS AG.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ss) o2_rsh) in
  let r1 := eval vm_compute in (nth 1 (ss_mem ss) o2_rsh) in
  pose proof (st_ok_pi_region_nth Ev ss (restrict (w_H W2) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as RG0;
  pose proof (st_ok_pi_region_nth Ev ss (restrict (w_H W2) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as RG1 end.
cbn [ms_mem restrict] in RG0, RG1.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R _ ?M _) _) _ =>
  assert (HLI1 : loc_in (mrestrict (w_H W2) M) c);
  [ unfold loc_in; repeat split;
    [ apply (field_of_region _ _ 9 sp1 _ 16 32 16 32 16 8 (SOff 13 0) c RG0)
    | apply (field_of_region _ _ 9 sp1 _ 16 32 16 32 24 8 (SOff 26 3) (3 * c + 11) RG0)
    | apply (field_of_region _ _ 9 sp1 _ 48 64 48 64 48 8 (SAlu ALU_AND (SOff 34 0) (SLit 255)) (base + c) RG1)
    | apply (field_of_region _ _ 9 sp1 _ 48 64 48 64 56 8 (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SOff 36 0) (SOff 36 0))) 0 RG1) ];
    o2_fclose AG E9
  | assert (HR : i2regs fpos R c 0) by (unfold i2regs, rB; repeat split; o2_regs_close HS AG) ]
end.
clear RG0 RG1.
(* the three rows of channel c *)
pose proof (len_prefixZ c ltac:(lia)) as Hl1.
eapply SRr_bind.
{ eapply (row2 fpos c 0 (prefixZ c) W2 ly2 S2 _ _ _ HOK Hcw ltac:(lia) HI1 ltac:(lia) HR HLA1 HLO1 HLI1). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HI3 & HR3 & HLA3 & HLO3 & HLI3).
change (0 + 1 =? 3) with false. cbv iota. change (0 + 1) with 1 in HR3.
eapply SRr_bind.
{ eapply (row2 fpos c 1 _ W3 ly3 S3 _ _ _ HOK Hcw ltac:(lia) HI3 ltac:(rewrite length_app, len_GAz; lia) HR3 HLA3 HLO3 HLI3). }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HI4 & HR4 & HLA4 & HLO4 & HLI4).
change (1 + 1 =? 3) with false. cbv iota. change (1 + 1) with 2 in HR4.
eapply SRr_bind.
{ eapply (row2 fpos c 2 _ W4 ly4 S4 _ _ _ HOK Hcw ltac:(lia) HI4 ltac:(rewrite !length_app, !len_GAz; lia) HR4 HLA4 HLO4 HLI4). }
cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HI5 & HR5 & HLA5 & HLO5 & HLI5).
change (2 + 1 =? 3) with true. cbv iota. change (2 + 1) with 3 in HR5.
rewrite prefix_step in HI5 by lia.
clear HI1 HI3 HI4 HR HR3 HR4 HLA1 HLA3 HLA4 HLO1 HLO3 HLO4 HLI1 HLI3 HLI4 HS SHOK AG HEI.
clear E2 E3 E4 E8 E9 E11 E13 E19 E22 E23 E24 E26 E32 E33 E34 E35 E36.
(* the end of the channel 0x83b38 *)
destruct HR5 as ((Y2 & Y3 & Y4 & Y8 & Y9) & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27).
destruct HLA5 as (L40 & L20 & L50 & L58). destruct HLO5 as (L28 & L48). destruct HLI5 as (L10 & L18 & L30 & L38).
pose proof HI5 as (HJ5 & _).
remember (Eimg (Ereg regs5 [Z_to_bv 64 c; Z_to_bv 64 (3 * c + 11); Z_to_bv 64 w; Z_to_bv 64 (Fa fpos);
  Z_to_bv 64 (2 ^ 31 - 9 - 3 * c)])) as Et eqn:HE.
assert (HEI : img_env VAL A_LIM Et) by (subst Et; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Et n = getr regs5 r) by (intros n0 r Hn0; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (EX : forall j, (j < 5)%nat -> ew Et (32 + j) = nth j [Z_to_bv 64 c; Z_to_bv 64 (3 * c + 11); Z_to_bv 64 w;
  Z_to_bv 64 (Fa fpos); Z_to_bv 64 (2 ^ 31 - 9 - 3 * c)] (Z_to_bv 64 0))
  by (intros j Hj; subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ j)).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite Y2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite Y3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite Y4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite Y8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite Y9 in E9.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite Y19 in E19.
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite Y22 in E22.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite Y23 in E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite Y24 in E24.
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [nth Nat.add] in E32, E33, E34, E35, E36.
unfold w64 in E2, E3, E4, E8, E9, E19, E22, E23, E24.
assert (HS : st_ok_pi SEGS VAL Et o2_ss_ot (restrict (w_H W5) (mkst regs5 (Z_to_bv 64 (BASE + 12540)) mem5 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold o2_ss_ot. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJP & _).
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  rewrite E9, unsigned_lit_small by lia_nd; split; try lia_nd; split; try lia_nd.
  + split; [intros o Ho; lia_nd|]. repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS Et _ sp1 16 8 (SOff 32 0) c);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L10].
    * apply (chunk_ok_val SEGS Et _ sp1 24 8 (SOff 33 0) (3 * c + 11));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L18].
    * apply (chunk_ok_val SEGS Et _ sp1 32 8 (SOff 34 0) w);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L20].
    * apply (chunk_ok_val SEGS Et _ sp1 64 8 (SOff 35 0) (Fa fpos));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L40].
  + split; [intros o Ho; apply (apresent_writable SEGS); apply HJP; lia_nd|]. apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS Et _ sp1 72 8 (SOff 36 0) (2 ^ 31 - 9 - 3 * c));
    [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | o2_cr | lia_nd | exact L48].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia_nd.
  repeat split; lia_nd.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E32, E36, !unsigned_lit_small by lia_nd.
  rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. repeat split; lia_nd. }
assert (SHOK : sh_ok SEGS o2_Bx [] Et (mrestrict (w_H W5) mem5)) by constructor.
assert (AG : forall n, (n < 33)%nat -> ew Et n = ew Et n) by reflexivity.
clear HE EE EX L10 L18 L48 L30 L38 Y2 Y3 Y4 Y8 Y9 Y19 Y20 Y21 Y22 Y23 Y24 Y25 Y26 Y27.
pose proof (len_prefixZ (c + 1) ltac:(lia)) as Hl2.
paj_run_tok RUN HS HJ5 SHOK o2_Bspan. { o2_awr AG E9. }
o2_upd HOK AG HI5 HI6.
lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ mem5) (mrestrict _ (ms_mem ?m1)) |- _ =>
  assert (HLA6 : loc_acc fpos (mrestrict (w_H W5) (ms_mem m1)))
    by (repeat split; (eapply (val_mem_aview_kept_x SEGS (w_H W5) (w_H W5) mem5 (ms_mem m1)); [|eassumption]);
        intros x Hx; apply (aview_kept_out Eo rs _ _ _ HFr x ltac:(lia_nd)); o2_nowin AG);
  assert (L28' : val_mem SEGS (mrestrict (w_H W5) (ms_mem m1)) (sp1 + 0x28) 8 (Fa fpos + 48))
    by ((eapply (val_mem_aview_kept_x SEGS (w_H W5) (w_H W5) mem5 (ms_mem m1)); [|eassumption]);
        intros x Hx; apply (aview_kept_out Eo rs _ _ _ HFr x ltac:(lia_nd)); o2_nowin AG)
end.
clear_frames. clear HI5 L28 L50 L58 L20 L40. o2_rebase HS AG.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (F32 : ew Ev 32 = Z_to_bv 64 c) by (rewrite AG by nat_side; exact E32) end.
psrr_branch_tok RUN BR HS SHOK o2_Bspan;
  rewrite branch_ne_U, (U_atom_off _ 32 c 1 F32), (U_atom _ 34 w E34) in Hc by lia_nd.
- assert (Hc1 : c + 1 <> w) by (intros X; rewrite X, Z.eqb_refl in Hc; discriminate Hc).
  paj_run_to_tok RUNTO HS HJ5 SHOK o2_Bspan 0x2fb8. { o2_awr AG E9. }
  o2_upd HOK AG HI6 HI7.
  lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?m1)) |- _ =>
    assert (HLA7 : loc_acc fpos (mrestrict (w_H W5) (ms_mem m1)))
      by (destruct HLA6 as (X1 & X2 & X3 & X4); repeat split; (eapply (val_mem_aview_kept_x SEGS (w_H W5) (w_H W5) m0 (ms_mem m1)); [|eassumption]);
          intros x Hx; apply (aview_kept_out Eo rs _ _ _ HFr x ltac:(lia_nd)); o2_nowin AG);
    assert (L28'' : val_mem SEGS (mrestrict (w_H W5) (ms_mem m1)) (sp1 + 0x28) 8 (Fa fpos + 48))
      by ((eapply (val_mem_aview_kept_x SEGS (w_H W5) (w_H W5) m0 (ms_mem m1)); [|eassumption]);
          intros x Hx; apply (aview_kept_out Eo rs _ _ _ HFr x ltac:(lia_nd)); o2_nowin AG)
  end.
  clear_frames. clear HI6 HLA6 L28'. o2_rebase HS AG.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss (restrict _ ?msx) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ss) o2_rsh) in
    pose proof (st_ok_pi_region_nth Ev ss (restrict (w_H W5) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as RG1 end.
  cbn [ms_mem restrict] in RG1.
  pmkst HS.
  eapply (IH (c + 1)); [exact HOK | lia | lia | exact HI7 | unfold oregs, rB; repeat split; o2_regs_close HS AG | exact HLA7 |].
  split; [exact L28''|].
  apply (field_of_region _ _ 9 sp1 _ 72 80 72 80 72 8 (SOff 36 (-3)) _ RG1); o2_fclose AG E9.
- assert (Hc1 : c + 1 = w) by (apply Z.eqb_eq; destruct (c + 1 =? w); [reflexivity | discriminate Hc]).
  paj_run_to_tok RUNTO HS HJ5 SHOK o2_Bspan 0x3144. { o2_awr AG E9. }
  o2_upd HOK AG HI6 HI7. clear_frames. clear HI6. o2_rebase HS AG.
  pmkst HS.
  eapply (epi fpos RowsE _ _ _ _ _ _ (prefixZ (c + 1)) (3 * c + 11) HI7).
  + unfold eregs, rB. repeat split; o2_regs_close HS AG.
  + left. split; [exact HOK|]. split; [unfold bgs_rows; lia|].
    split; [rewrite prefix_sweep; f_equal; lia | intros a Ha; exact Ha].
Qed.

(* ---- S4: GRANT_HEAD_MARK, the six GRANT_GROUPB rows, and `w < 2` (0x83954 .. 0x83b7c) -------------------- *)
(* ---- mk: shared kit for the two pieces `gb` (0x8398c .. 0x839b8) and `seg_mark` (0x83954 .. 0x839f0) ---- *)
Definition mk_Bx : sv := SLit SBV.
Definition mk_Bspan : Z * Z := (SBV, SBV + 2 ^ 44 - 1).
Lemma mk_gbz_len : forall i, length (GBz i) = 34%nat.
Proof.
  intros i. unfold GBz, gb_tail.
  repeat (match goal with |- context [if ?c then _ else _] => destruct c end); reflexivity.
Qed.
Lemma mk_garr_head : forall (m : word -> option byte) q (l1 l2 : list Z),
  garr8 SEGS m q (l1 ++ l2) -> garr8 SEGS m q l1.
Proof. intros m q l1 l2 H. exact (proj1 (proj1 (garr8_app _ _ _ _ _) H)). Qed.
Lemma mk_garr_cut34 : forall (m : word -> option byte) q (l2 : list Z) j,
  garr8 SEGS m q (GBz j ++ l2) -> garr8 SEGS m (q + 34) l2.
Proof.
  intros m q l2 j H. apply (proj1 (garr8_app _ _ _ _ _)) in H. rewrite mk_gbz_len in H.
  replace (q + Z.of_nat 34) with (q + 34) in H by lia. exact (proj2 H).
Qed.
(* the i-th 34-byte row of the 204-byte GRANT_GROUPB table *)
Lemma mk_gb_row : forall (m : word -> option byte) i, 0 <= i < 6 ->
  garr8 SEGS m (VAL (A_OBJ B_GROUPB)) GBallz -> garr8 SEGS m (VAL (A_OBJ B_GROUPB) + 34 * i) (GBz i).
Proof.
  intros m i Hi HG. unfold GBallz in HG.
  assert (Ei : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
  destruct Ei as [-> | [-> | [-> | [-> | [-> | ->]]]]].
  - replace (VAL (A_OBJ B_GROUPB) + 34 * 0) with (VAL (A_OBJ B_GROUPB)) by lia.
    exact (mk_garr_head _ _ _ _ HG).
  - apply mk_garr_cut34 in HG.
    replace (VAL (A_OBJ B_GROUPB) + 34 * 1) with (VAL (A_OBJ B_GROUPB) + 34) by lia.
    exact (mk_garr_head _ _ _ _ HG).
  - do 2 (apply mk_garr_cut34 in HG).
    replace (VAL (A_OBJ B_GROUPB) + 34 * 2) with (VAL (A_OBJ B_GROUPB) + 34 + 34) by lia.
    exact (mk_garr_head _ _ _ _ HG).
  - do 3 (apply mk_garr_cut34 in HG).
    replace (VAL (A_OBJ B_GROUPB) + 34 * 3) with (VAL (A_OBJ B_GROUPB) + 34 + 34 + 34) by lia.
    exact (mk_garr_head _ _ _ _ HG).
  - do 4 (apply mk_garr_cut34 in HG).
    replace (VAL (A_OBJ B_GROUPB) + 34 * 4) with (VAL (A_OBJ B_GROUPB) + 34 + 34 + 34 + 34) by lia.
    exact (mk_garr_head _ _ _ _ HG).
  - do 5 (apply mk_garr_cut34 in HG).
    replace (VAL (A_OBJ B_GROUPB) + 34 * 5) with (VAL (A_OBJ B_GROUPB) + 34 + 34 + 34 + 34 + 34) by lia.
    exact HG.
Qed.
(* the four locals of the accepting path: sp1 + 0x20, 0x40, 0x50 and 0x58, 8 bytes each *)
Lemma mk_loc_acc_kept : forall fpos (H : word -> bool) (m m' : word -> option byte),
  (forall a, sp1 + 0x20 <= a < sp1 + 0x28 -> aview SEGS H m' a = aview SEGS H m a) ->
  (forall a, sp1 + 0x40 <= a < sp1 + 0x48 -> aview SEGS H m' a = aview SEGS H m a) ->
  (forall a, sp1 + 0x50 <= a < sp1 + 0x60 -> aview SEGS H m' a = aview SEGS H m a) ->
  loc_acc fpos (mrestrict H m) -> loc_acc fpos (mrestrict H m').
Proof.
  intros fpos H m m' K1 K2 K3 (A40 & A20 & A50 & A58). unfold loc_acc. repeat split;
  (eapply (val_mem_aview_kept_x SEGS H H m m');
   [intros x Hx; first [apply K1; lia | apply K2; lia | apply K3; lia] | eassumption]).
Qed.
Lemma mk_rows_noimg : bgs_ok s V mx base w -> forall a, RowsE a -> ~ in_img SEGS a.
Proof.
  intros HOK a Ha Hin. pose proof (pa_img_range a Hin) as Hr.
  destruct (HROWS HOK) as (_ & _ & Hsimg & _). unfold RowsE in Ha. lia.
Qed.
(* a ~ in_wrange goal: the written windows of a run are the regions' [base + wlo, base + whi) *)
Ltac mk_winout := let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros (r & Hr & Hw);
  lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
      repeat match goal with Hq : ew ?Ex ?n = Z_to_bv 64 _ |- _ => rewrite Hq in Hw end;
      rewrite ?unsigned_lit_small in Hw by lia; lia |]);
  try destruct Hr.
Ltac mk_rfact AG E H :=
  repeat (rewrite AG in H by lia);
  repeat match type of H with context [ew ?Ex ?n] => match goal with En : ew Ex n = _ |- _ => rewrite En in H end end.
Ltac mk_regs_close HS AG E :=
  lazymatch goal with |- getr _ ?r = w64 _ =>
  let H := fresh "Rx" in prreg HS r H; mk_rfact AG E H; rewrite H; clear H; unfold w64;
  rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia] end.
Ltac mk_shok HS SHOK := lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
  assert (SHOK : sh_ok SEGS mk_Bx [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by constructor end.
(* a run of the body itself: it writes nothing of the caller's, so binv and loc_acc carry over *)
Ltac mk_keep HOK HIold HLold HInew HLnew :=
lazymatch type of HIold with binv ?fp ?Ex ?Wx ?lyx ?Sx ?m0 ?md0 ?rws =>
lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ m0) (mrestrict _ (ms_mem ?m1)) |- _ =>
lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem m1) ?mdx _,
                    HGr : mem_grows (mrestrict _ m0) _ |- _ =>
assert (HInew : binv fp Ex Wx lyx Sx (ms_mem m1) mdx rws) by
(eapply (binv_kept fp Ex Ex Wx lyx Sx m0 md0 rws);
 [ exact HIold | exact HJx | intros ? HEx; exact HEx | exact (mk_rows_noimg HOK)
 | intros a Ha Hwin _ _; apply (aview_kept_out Eo rs _ _ _ HFr a Ha); mk_winout
 | intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); mk_winout
 | intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); mk_winout
 | intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); mk_winout
 | intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); mk_winout
 | intros a Ha Hp; exact (apresent_grows _ _ _ a HGr Hp) ]);
assert (HLnew : loc_acc fp (mrestrict (w_H Wx) (ms_mem m1))) by
(eapply (mk_loc_acc_kept fp (w_H Wx) m0);
 [ intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); mk_winout
 | intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); mk_winout
 | intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); mk_winout
 | exact HLold ])
end end end.
(* the symbolic state at the GRANT_GROUPB loop head: only the local s at sp1 + 0x78 is read *)
Definition mk_ss_gb : sstate :=
  mkSS 0x2f50 sr_atoms
    [YP09.mkRegion (Some 9%nat) 0x78 0x80 0 0 [YP09.mkChunk 0x78 (CVal 8 (SOff 32 0))]] None
    (mkFacts [] [] []).
(* the rows lie wholly below or wholly above image B, so a row and an image range are apart *)
Lemma mk_img_apart : bgs_ok s V mx base w -> forall q d n, IMG_LO_B <= q -> q + n <= IMG_TOP_B ->
  0 <= d -> 0 <= n -> d + n <= 34 * (8 + 3 * w) -> s + d + n <= q \/ q + n <= s + d.
Proof.
  intros HOK q d n H1 H2 H3 H4 H5. destruct (HROWS HOK) as (_ & _ & Hsimg & _). unfold bgs_rows in Hsimg.
  destruct Hsimg as [HA | HA]; [left | right]; lia.
Qed.
Lemma gb : forall fpos i rows W2 ly2 S2 regs2 mem2 md2, bgs_ok s V mx base w -> 0 <= i < 6 ->
  binv fpos RowsE W2 ly2 S2 mem2 md2 rows -> Z.of_nat (length rows) = 170 + 34 * i ->
  gbregs fpos regs2 i -> loc_acc fpos (mrestrict (w_H W2) mem2) ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x2f50)) mem2 (seg_rom SEGS)) md2)
    (GBpost fpos (i + 1) (rows ++ GBz i)).
Proof.
intros fpos i rows W2 ly2 S2 regs2 mem2 md2 HOK Hi HI Hlen HRG HLA.
pose proof HRG as ((R2 & R3 & R4 & R8 & R9) & R18 & R19 & R20 & R21 & R23 & R24).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof sp1_facts as (P1 & P2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof IMG_LO_B_val as EL. pose proof IMG_TOP_B_val as ET.
assert (ELO : IMG_LO = IMG_LO_B) by reflexivity.
assert (EHI : IMG_HI = IMG_TOP_B) by reflexivity.
assert (WS : 4096 <= STKB) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HOK as (Hs0 & HVn0 & Hw1 & Hbw48 & Hmx). unfold bgs_rows in Hmx.
destruct (HROWS HOK) as (_ & Hs47 & _ & _ & _ & _ & _ & Hrwin & _).
unfold bgs_rows in Hs47, Hrwin.
pose proof (binv_frame fpos RowsE W2 ly2 S2 mem2 md2 rows HI) as (F64 & F4096 & Fceil & _ & F47 & _).
pose proof HIMGROWS as (HTBL & HinACK & HinMARK & HinGB & HackL & HackH & HmarkL & HmarkH & HgbL & HgbH).
assert (Hrowwin : forall a, sp1 <= a < sp1 + 128 -> ~ (s <= a < s + 34 * (8 + 3 * w)))
  by (intros a Ha Hx; destruct Hrwin; lia).
clear Hrwin.
pose proof HI as (HJ & Hfrm & Hblk & Hfs & HKe & Hsv & Hl0 & Hflg & Hrw).
pose proof Hl0 as (L60 & L68 & L70 & L78).
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
remember (Eimg (Ereg regs2 [Z_to_bv 64 s])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite R18 in E18.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite R19 in E19.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite R20 in E20.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite R21 in E21.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite R23 in E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite R24 in E24.
assert (E32 : ew E 32 = Z_to_bv 64 s)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
unfold w64 in E2, E3, E4, E8, E9, E18, E19, E20, E21, E23, E24.
assert (HRA0 : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (HS : st_ok_pi SEGS VAL E mk_ss_gb
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x2f50)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold mk_ss_gb. apply pa_entry_st_ok_full.
  - exact HRA0.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ sp1 120 8%N (SOff 32 0) s);
    [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia | cbn; lia | exact L78 ].
  - cbn. tauto.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS mk_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
clear HE EE.
(* 0x8398c: beqz s2 -> the trap 0x83bf4; s + 170 + 34 i is not 0 *)
psrr_branch_tok RUN BR HS SHOK mk_Bspan.
{ exfalso. rewrite branch_eq_U, (U_atom E 18 (s + 170 + 34 * i) E18), (U_lit E 0) in Hc by lia.
  apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* 0x83990 / 0x83994: ld a0, 0x78(s1); bltu s2, a0 -> the trap; s <= s + 170 + 34 i *)
paj_run_tok RUN HS HJ SHOK mk_Bspan. { awr_ok_tac. }
mk_keep HOK HI HLA HI1 HL1. clear_frames.
psrr_branch_tok RUN BR HS SHOK mk_Bspan.
{ exfalso. rewrite branch_ltu_U, (U_atom E 18 (s + 170 + 34 * i) E18), (U_atom E 32 s E32) in Hc by lia.
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* 0x83998 .. 0x839a4: the arguments and __asan_memcpy (s + 170 + 34 i, GRANT_GROUPB + 34 i, 34) *)
paj_run_tok RUN HS HJ SHOK mk_Bspan. { awr_ok_tac. }
mk_keep HOK HI1 HL1 HI2 HL2. clear_frames. clear HI1 HL1.
destruct (HTBL (w_H W2) _ (arod_binv _ _ _ _ _ _ _ _ HI2)) as (_ & _ & HGBall).
pose proof (mk_gb_row _ i Hi HGBall) as HGBrow.
destruct (ro_read_ok_glob SEGS B GRANT_GLOBS_B ly2 S2 W2 _ _ (VAL (A_OBJ B_GROUPB)) 204
  (VAL (A_OBJ B_GROUPB) + 34 * i) 34 HGL HinGB HIMGSH (proj1 (proj1 HI2))
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [GRa GHl].
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
mk_rfact AG E Ra0. mk_rfact AG E Ra1. mk_rfact AG E Ra2. mk_rfact AG E Rsp. mk_rfact AG E Rgp. mk_rfact AG E Rtp.
pmkst HS.
eapply (call_cpy fpos W2 ly2 S2 _ _ rows _ 0x2f6c (VAL (A_OBJ B_GROUPB) + 34 * i) (GBz i) _ HOK HI2);
  rewrite ?mk_gbz_len; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold bgs_rows; rewrite ?Hlen;
  [ lia | lia | exact HGBrow | lia | lia
  | apply (mk_img_apart HOK); lia
  | unfold amem_range, kLowMemEnd; left; lia
  | intros a Ha Hww; lia
  | exact GRa | exact GHl
  | rewrite Ra0; unfold w64; f_equal; lia
  | rewrite Ra1; unfold w64; f_equal; lia
  | rewrite Ra2; unfold w64; f_equal; lia
  | unfold spZ; rewrite Rsp, unsigned_lit_small by lia; reflexivity
  | exact Rgp | exact Rtp | exact Rra | lia | reflexivity | ].
intros mem3 md3 regs3 HI3 HK3 HP3.
assert (HL3 : loc_acc fpos (mrestrict (w_H W2) mem3)).
{ eapply (mk_loc_acc_kept fpos (w_H W2) _ mem3); [ | | | exact HL2 ].
  all: intros a Ha; apply HK3; [lia | | lia].
  all: intros Hx; rewrite ?Hlen, ?mk_gbz_len in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
       apply (Hrowwin a ltac:(lia)); lia. }
assert (Hlen' : Z.of_nat (length (rows ++ GBz i)) = 204 + 34 * i)
  by (rewrite length_app, Nat2Z.inj_add, Hlen, mk_gbz_len; lia).
clear Ra0 Ra1 Ra2 Rsp Rgp Rtp Rra HI2 HL2 HJ SHOK GRa GHl HGBall HGBrow.
pose proof (proj1 HI3) as HJ3.
reseat HS HJ3 HP3 (@nil nat) AG ltac:(idtac).
try clear SHOK. mk_shok HS SHOK. cbn [ms_mem] in SHOK.
(* 0x839a8 .. 0x839b8: the four counters, then bnez s3 *)
paj_run_tok RUN HS HJ3 SHOK mk_Bspan. { awr_ok_tac. }
mk_keep HOK HI3 HL3 HI4 HL4. clear_frames. clear HI3 HL3.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (F19 : ew Ev 19 = Z_to_bv 64 (6 - i)) by (rewrite AG by lia; exact E19) end.
psrr_branch_tok RUN BR HS SHOK mk_Bspan.
- (* s3 <> 0: back to the loop head 0x8398c *)
  rewrite branch_ne_U in Hc.
  lazymatch type of Hc with context [U ?Ev _] =>
    rewrite (U_atom_off Ev 19 (6 - i) (-1) F19), (U_lit Ev 0) in Hc by lia end.
  apply negb_true_iff, Z.eqb_neq in Hc. assert (Hi5 : i <> 5) by lia.
  paj_run_to_tok RUNTO HS HJ3 SHOK mk_Bspan 0x2f50. { awr_ok_tac. }
  mk_keep HOK HI4 HL4 HI5 HL5. clear_frames.
  pmkst HS. apply SRr_ret. unfold GBpost.
  lazymatch goal with HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m1) ?mdq _ |- _ =>
    exists ly2, S2, (ms_regs m1), (ms_mem m1), mdq end.
  split; [replace (i + 1 =? 6) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity|].
  split; [exact HI5|].
  split; [unfold gbregs, rB; repeat split; mk_regs_close HS AG E | exact HL5].
- (* s3 = 0: on to 0x839bc *)
  rewrite branch_ne_U in Hc.
  lazymatch type of Hc with context [U ?Ev _] =>
    rewrite (U_atom_off Ev 19 (6 - i) (-1) F19), (U_lit Ev 0) in Hc by lia end.
  apply negb_false_iff, Z.eqb_eq in Hc. assert (Hi5 : i = 5) by lia.
  paj_run_to_tok RUNTO HS HJ3 SHOK mk_Bspan 0x2f80. { awr_ok_tac. }
  mk_keep HOK HI4 HL4 HI5 HL5. clear_frames.
  pmkst HS. apply SRr_ret. unfold GBpost.
  lazymatch goal with HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m1) ?mdq _ |- _ =>
    exists ly2, S2, (ms_regs m1), (ms_mem m1), mdq end.
  split; [replace (i + 1 =? 6) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity|].
  split; [exact HI5|].
  split; [unfold gbregs, rB; repeat split; mk_regs_close HS AG E | exact HL5].
Qed.
(* the symbolic state at 0x83954: the local s at sp1 + 0x78 is read *)
Definition mk_ss_m : sstate :=
  mkSS 0x2f18 sr_atoms
    [YP09.mkRegion (Some 9%nat) 0x78 0x80 0 0 [YP09.mkChunk 0x78 (CVal 8 (SOff 32 0))]] None
    (mkFacts [] [] []).
(* the symbolic state at 0x839bc: w (sp1 + 0x20), F (0x40), SHF + 4 (0x50) and F + 32 (0x58) are read; the outer
   loop's two locals are written at sp1 + 0x28 and sp1 + 0x48 *)
Definition mk_ss_w : sstate :=
  mkSS 0x2f80 sr_atoms
    [YP09.mkRegion (Some 9%nat) 0x20 0x30 0x28 0x30 [YP09.mkChunk 0x20 (CVal 8 (SOff 32 0))];
     YP09.mkRegion (Some 9%nat) 0x40 0x60 0x48 0x50
       [YP09.mkChunk 0x40 (CVal 8 (SOff 24 0)); YP09.mkChunk 0x50 (CVal 8 (SOff 23 4));
        YP09.mkChunk 0x58 (CVal 8 (SOff 24 32))]] None
    (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mk_sha_rng : forall fpos, 4096 <= Fa fpos -> Fa fpos + 4096 <= alloc_ceiling ->
  SBV <= SHa fpos /\ SHa fpos + 512 <= SBV + 2 ^ 44.
Proof. intros fpos H1 H2. unfold SHa, SBV. pose proof asan_consts as (C1 & _). lia. Qed.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma mk_signed_lit : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. assert (Hh : bv_half_modulus 64 = 2 ^ 63) by reflexivity.
  assert (Hm : bv_modulus 64 = 2 ^ 64) by reflexivity.
  unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Hh, Hm.
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.
Lemma mk_blt_lit : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. unfold bv_lts. rewrite !mk_signed_lit by lia. reflexivity. Qed.
(* the written windows of a run over mk_ss_w lie in the machine frame, inside the journal's stack window *)
Ltac mk_awr G9 :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0x ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0x fp b0 bc ly0 own0) end;
  repeat first
   [ apply awr_ok_nil
   | apply awr_ok_cons_ro; [cbn; lia|]
   | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat sp1);
     [ reflexivity | rewrite G9; apply unsigned_lit_small; lia
     | let a := fresh "a" in let Ha := fresh "Ha" in
       intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; left; lia | ] ].
Lemma seg_mark : forall fpos W2 ly2 S2 regs2 mem2 md2, bgs_ok s V mx base w ->
  binv fpos RowsE W2 ly2 S2 mem2 md2 prefix3 -> l1regs fpos regs2 3 -> loc_acc fpos (mrestrict (w_H W2) mem2) ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x2f18)) mem2 (seg_rom SEGS)) md2) TBP.
Proof.
intros fpos W2 ly2 S2 regs2 mem2 md2 HOK HI HRL HLA.
pose proof HRL as ((R2 & R3 & R4 & R8 & R9) & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof sp1_facts as (P1 & P2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof IMG_LO_B_val as EL. pose proof IMG_TOP_B_val as ET.
assert (ELO : IMG_LO = IMG_LO_B) by reflexivity.
assert (EHI : IMG_HI = IMG_TOP_B) by reflexivity.
assert (WS : 4096 <= STKB) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (SBVv : SBV = 0x7fff8000) by reflexivity.
pose proof HOK as (Hs0 & HVn0 & Hw1 & Hbw48 & Hmx). unfold bgs_rows in Hmx.
destruct (HROWS HOK) as (_ & Hs47 & _ & _ & _ & _ & _ & Hrwin & _).
unfold bgs_rows in Hs47, Hrwin.
pose proof (binv_frame fpos RowsE W2 ly2 S2 mem2 md2 prefix3 HI) as (F64 & F4096 & Fceil & _ & F47 & _).
pose proof (mk_sha_rng fpos F4096 Fceil) as (SH1 & SH2).
pose proof HIMGROWS as (HTBL & HinACK & HinMARK & HinGB & HackL & HackH & HmarkL & HmarkH & HgbL & HgbH).
assert (Hrowwin : forall a, sp1 <= a < sp1 + 128 -> ~ (s <= a < s + 34 * (8 + 3 * w)))
  by (intros a Ha Hx; destruct Hrwin; lia).
clear Hrwin.
assert (Hl3 : Z.of_nat (length prefix3) = 136)
  by (unfold prefix3; rewrite !length_app, !len_GAz; reflexivity).
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
(* ---- 0x83954 .. 0x83988: GRANT_HEAD_MARK into row 4, then the GRANT_GROUPB loop's registers ---- *)
pose proof HI as (HJ & Hfrm & Hblk & Hfs & HKe & Hsv & Hl0 & Hflg & Hrw).
pose proof Hl0 as (L60 & L68 & L70 & L78).
remember (Eimg (Ereg regs2 [Z_to_bv 64 s])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite R23 in E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite R24 in E24.
assert (E32 : ew E 32 = Z_to_bv 64 s)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
unfold w64 in E2, E3, E4, E8, E9, E23, E24.
assert (EM : ew E 264 = Z_to_bv 64 (VAL (A_OBJ B_MARK)))
  by (change 264%nat with (A_OBJ B_MARK); apply (img_env_atomP E (A_OBJ B_MARK) HEI);
      unfold A_OBJ, B_MARK, A_TEXT, A_LIM; lia).
assert (EG : ew E 260 = Z_to_bv 64 (VAL (A_OBJ B_GROUPB)))
  by (change 260%nat with (A_OBJ B_GROUPB); apply (img_env_atomP E (A_OBJ B_GROUPB) HEI);
      unfold A_OBJ, B_GROUPB, A_TEXT, A_LIM; lia).
assert (HRA0 : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (HS : st_ok_pi SEGS VAL E mk_ss_m
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x2f18)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold mk_ss_m. apply pa_entry_st_ok_full.
  - exact HRA0.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ sp1 120 8%N (SOff 32 0) s);
    [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia | cbn; lia | exact L78 ].
  - cbn. tauto.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS mk_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
clear HE EE.
(* 0x83954 .. 0x8395c: a0 = -137, a1 = s, bltu a0, a1 -> the trap 0x83bf4; s + 136 does not wrap *)
paj_run_tok RUN HS HJ SHOK mk_Bspan. { awr_ok_tac. }
mk_keep HOK HI HLA HI1 HL1. clear_frames.
psrr_branch_tok RUN BR HS SHOK mk_Bspan.
{ exfalso. rewrite branch_ltu_U, (U_atom E 32 s E32) in Hc by lia. apply Z.ltb_lt in Hc.
  lazymatch type of Hc with U ?Ev (SLit ?z) < _ =>
    assert (HUz : U Ev (SLit z) = 2 ^ 64 - 137) by (vm_compute; reflexivity) end.
  lia. }
clear Hc.
(* 0x83960 .. 0x83974: __asan_memcpy (s + 136, GRANT_HEAD_MARK, 34) *)
paj_run_tok RUN HS HJ SHOK mk_Bspan. { awr_ok_tac. }
mk_keep HOK HI1 HL1 HI2 HL2. clear_frames. clear HI1 HL1.
destruct (HTBL (w_H W2) _ (arod_binv _ _ _ _ _ _ _ _ HI2)) as (_ & HGmark & _).
destruct (ro_read_ok_glob SEGS B GRANT_GLOBS_B ly2 S2 W2 _ _ (VAL (A_OBJ B_MARK)) 34
  (VAL (A_OBJ B_MARK)) 34 HGL HinMARK HIMGSH (proj1 (proj1 HI2))
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [MRa MHl].
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
mk_rfact AG E Ra0. mk_rfact AG E Ra1. mk_rfact AG E Ra2. mk_rfact AG E Rsp. mk_rfact AG E Rgp. mk_rfact AG E Rtp.
pmkst HS.
eapply (call_cpy fpos W2 ly2 S2 _ _ prefix3 _ 0x2f3c (VAL (A_OBJ B_MARK)) HEAD_MARK34z _ HOK HI2);
  change (length HEAD_MARK34z) with 34%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold bgs_rows; rewrite ?Hl3;
  [ lia | lia | exact HGmark | lia | lia
  | apply (mk_img_apart HOK); lia
  | unfold amem_range, kLowMemEnd; left; lia
  | intros a Ha Hww; lia
  | exact MRa | exact MHl
  | rewrite Ra0; unfold w64; rewrite ?unsigned_lit_small by lia; f_equal; lia
  | rewrite Ra1; reflexivity
  | rewrite Ra2; unfold w64; rewrite ?unsigned_lit_small by lia; f_equal; lia
  | unfold spZ; rewrite Rsp, unsigned_lit_small by lia; reflexivity
  | exact Rgp | exact Rtp | exact Rra | lia | reflexivity | ].
intros mem3 md3 regs3 HI3 HK3 HP3.
assert (HL3 : loc_acc fpos (mrestrict (w_H W2) mem3)).
{ eapply (mk_loc_acc_kept fpos (w_H W2) _ mem3); [ | | | exact HL2 ].
  all: intros a Ha; apply HK3; [lia | | lia].
  all: intros Hx; rewrite ?Hl3 in Hx; change (length HEAD_MARK34z) with 34%nat in Hx;
       cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; apply (Hrowwin a ltac:(lia)); lia. }
assert (Hl4 : Z.of_nat (length (prefix3 ++ HEAD_MARK34z)) = 170)
  by (rewrite length_app, Nat2Z.inj_add, Hl3; reflexivity).
clear Ra0 Ra1 Ra2 Rsp Rgp Rtp Rra HI2 HL2 HJ SHOK MRa MHl HGmark.
pose proof (proj1 HI3) as HJ3.
reseat HS HJ3 HP3 (@nil nat) AG ltac:(idtac).
try clear SHOK. mk_shok HS SHOK. cbn [ms_mem] in SHOK.
(* 0x83978 .. 0x83988: s2 = s + 170, s4 = GRANT_GROUPB, s3 = 6, s5 = s2 *)
paj_run_to_tok RUNTO HS HJ3 SHOK mk_Bspan 0x2f50. { awr_ok_tac. }
mk_keep HOK HI3 HL3 HI4 HL4. clear_frames. clear HI3 HL3.
pmkst HS.
assert (Hm0 : Z.of_nat (length (prefix3 ++ HEAD_MARK34z)) = 170 + 34 * 0) by (rewrite Hl4; reflexivity).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
  assert (HR4 : gbregs fpos rg 0) by (unfold gbregs, rB; repeat split; mk_regs_close HS AG E) end.
clear HS SHOK HJ3 HP3 HK3.
(* ---- 0x8398c .. 0x839b8: the six GRANT_GROUPB rows ---- *)
eapply SRr_bind; [exact (gb fpos 0 _ _ _ _ _ _ _ HOK ltac:(lia) HI4 Hm0 HR4 HL4) |].
intros Wa ca _ Hpa. destruct Hpa as (lya & Sa & rga & mea & mda & -> & HIa & HRa & HLa).
assert (Hma : Z.of_nat (length ((prefix3 ++ HEAD_MARK34z) ++ GBz 0)) = 170 + 34 * 1)
  by (rewrite length_app, Nat2Z.inj_add, Hl4, mk_gbz_len; lia).
eapply SRr_bind; [exact (gb fpos 1 _ _ _ _ _ _ _ HOK ltac:(lia) HIa Hma HRa HLa) |].
intros Wb cb _ Hpb. destruct Hpb as (lyb & Sb & rgb & meb & mdb & -> & HIb & HRb & HLb).
assert (Hmb : Z.of_nat (length (((prefix3 ++ HEAD_MARK34z) ++ GBz 0) ++ GBz 1)) = 170 + 34 * 2)
  by (rewrite length_app, Nat2Z.inj_add, Hma, mk_gbz_len; lia).
eapply SRr_bind; [exact (gb fpos 2 _ _ _ _ _ _ _ HOK ltac:(lia) HIb Hmb HRb HLb) |].
intros Wc cc _ Hpc. destruct Hpc as (lyc' & Sc' & rgc & mec & mdc' & -> & HIc & HRc & HLc).
assert (Hmc : Z.of_nat (length ((((prefix3 ++ HEAD_MARK34z) ++ GBz 0) ++ GBz 1) ++ GBz 2)) = 170 + 34 * 3)
  by (rewrite length_app, Nat2Z.inj_add, Hmb, mk_gbz_len; lia).
eapply SRr_bind; [exact (gb fpos 3 _ _ _ _ _ _ _ HOK ltac:(lia) HIc Hmc HRc HLc) |].
intros Wd cd _ Hpd. destruct Hpd as (lyd & Sd & rgd & med & mdd & -> & HId & HRd & HLd).
assert (Hmd : Z.of_nat (length (((((prefix3 ++ HEAD_MARK34z) ++ GBz 0) ++ GBz 1) ++ GBz 2) ++ GBz 3))
  = 170 + 34 * 4) by (rewrite length_app, Nat2Z.inj_add, Hmc, mk_gbz_len; lia).
eapply SRr_bind; [exact (gb fpos 4 _ _ _ _ _ _ _ HOK ltac:(lia) HId Hmd HRd HLd) |].
intros We ce _ Hpe. destruct Hpe as (lye & Se & rge & mee & mde & -> & HIe & HRe & HLe).
assert (Hme : Z.of_nat (length ((((((prefix3 ++ HEAD_MARK34z) ++ GBz 0) ++ GBz 1) ++ GBz 2) ++ GBz 3) ++ GBz 4))
  = 170 + 34 * 5) by (rewrite length_app, Nat2Z.inj_add, Hmd, mk_gbz_len; lia).
eapply SRr_bind; [exact (gb fpos 5 _ _ _ _ _ _ _ HOK ltac:(lia) HIe Hme HRe HLe) |].
intros Wf cf _ Hpf. destruct Hpf as (lyf & Sf & rgf & mef & mdf & -> & HIf & HRf & HLf).
lazymatch goal with |- SRr _ ?Wx (mkCfg (mkst ?rg _ ?mm _) ?dd) ?QQ =>
  change (SRr SEGS Wx (mkCfg (mkst rg (Z_to_bv 64 (BASE + 0x2f80)) mm (seg_rom SEGS)) dd) QQ) end.
rewrite prefix_one in HIf.
clear HIa HIb HIc HId HIe HLa HLb HLc HLd HLe HRa HRb HRc HRd HRe HI4 HL4 HR4.
(* ---- 0x839bc: w < 2 ? ---- *)
pose proof (len_prefixZ 1 ltac:(lia)) as Hlp1.
(* the stores below are on the machine stack; the rows are the caller's heap block, apart from it *)
destruct (HROWS HOK) as (_ & _ & _ & _ & _ & _ & _ & Hrwin & _). unfold bgs_rows in Hrwin.
pose proof HRf as ((Q2 & Q3 & Q4 & Q8 & Q9) & Q18 & Q19 & Q20 & Q21 & Q23 & Q24).
pose proof HLf as (A40 & A20 & A50 & A58).
pose proof (proj1 HIf) as HJf.
pose proof HJf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPf & _).
remember (Eimg (Ereg rgf [Z_to_bv 64 w])) as Ew eqn:HEw.
assert (HEIw : img_env VAL A_LIM Ew) by (subst Ew; apply Eimg_env).
assert (EEw : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ew n = getr rgf r)
  by (intros n r Hn; rewrite HEw; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EEw 2%nat 2%bv eq_refl) as G2. rewrite Q2 in G2.
pose proof (EEw 3%nat 3%bv eq_refl) as G3. rewrite Q3 in G3.
pose proof (EEw 4%nat 4%bv eq_refl) as G4. rewrite Q4 in G4.
pose proof (EEw 8%nat 8%bv eq_refl) as G8. rewrite Q8 in G8.
pose proof (EEw 9%nat 9%bv eq_refl) as G9. rewrite Q9 in G9.
pose proof (EEw 23%nat 23%bv eq_refl) as G23. rewrite Q23 in G23.
pose proof (EEw 24%nat 24%bv eq_refl) as G24. rewrite Q24 in G24.
assert (G32 : ew Ew 32 = Z_to_bv 64 w)
  by (subst Ew; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rgf _ 0)).
unfold w64 in G2, G3, G4, G8, G9, G23, G24.
assert (HRAw : regs_ok Ew sr_atoms rgf) by (rewrite HEw; apply regs_ok_Eimg_Ereg).
assert (HSw : st_ok_pi SEGS VAL Ew mk_ss_w
  (restrict (w_H Wf) (mkst rgf (Z_to_bv 64 (BASE + 0x2f80)) mef (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold mk_ss_w. apply pa_entry_st_ok_full.
  - exact HRAw.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite G9, unsigned_lit_small by lia.
    + split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPf; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS Ew _ sp1 32 8%N (SOff 32 0) w);
      [ cbn [sv_denot]; rewrite G32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia | exact A20 ].
    + split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPf; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS Ew _ sp1 64 8%N (SOff 24 0) (Fa fpos));
        [ cbn [sv_denot]; rewrite G24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; lia | cbn; lia | exact A40 ].
      * apply (chunk_ok_val SEGS Ew _ sp1 80 8%N (SOff 23 4) (SHa fpos + 4));
        [ cbn [sv_denot]; rewrite G23, unsigned_lit_small by lia; reflexivity
        | cbn; lia | cbn; lia | exact A50 ].
      * apply (chunk_ok_val SEGS Ew _ sp1 88 8%N (SOff 24 32) (Fa fpos + 32));
        [ cbn [sv_denot]; rewrite G24, unsigned_lit_small by lia; reflexivity
        | cbn; lia | cbn; lia | exact A58 ].
  - cbn [pairwise_disjoint all_disjoint]. repeat split; try exact I.
    unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. left. lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite G9, unsigned_lit_small by lia. change (2 ^ 5) with 32. split; [lia|]. split; [exact P1 | lia]. }
assert (SHOKw : sh_ok SEGS mk_Bx [] Ew (mrestrict (w_H Wf) mef)) by constructor.
assert (AGw : forall n, (n < 33)%nat -> ew Ew n = ew Ew n) by reflexivity.
clear HEw EEw.
(* 0x839bc .. 0x839c4: a0 = 2, a1 = w; blt a1, a0 *)
paj_run_tok RUN HSw HJf SHOKw mk_Bspan. { mk_awr G9. }
mk_keep HOK HIf HLf HI9 HL9. clear_frames.
assert (Dw : sv_denot Ew (SOff 32 0) = Z_to_bv 64 w)
  by (cbn [sv_denot]; rewrite G32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
psrr_branch_tok RUN BR HSw SHOKw mk_Bspan.
- (* w = 1: 0x83b64 .. 0x83b7c, s10 = 11 = bgs_rows 1, s2 = F, on to the release 0x83b80 *)
  rewrite Dw in Hc.
  lazymatch type of Hc with branch_taken BC_LT _ (sv_denot ?Ev (SLit ?z)) = _ =>
    change (sv_denot Ev (SLit z)) with (Z_to_bv 64 z) in Hc end.
  rewrite mk_blt_lit in Hc by lia. apply Z.ltb_lt in Hc. assert (Hw1' : w = 1) by lia.
  paj_run_to_tok RUNTO HSw HJf SHOKw mk_Bspan 0x3144. { mk_awr G9. }
  mk_keep HOK HI9 HL9 HI10 HL10. clear_frames.
  pmkst HSw.
  eapply (epi fpos RowsE _ _ _ _ _ _ (prefixZ 1) 11 HI10).
  + unfold eregs, rB. repeat split; mk_regs_close HSw AGw Ew.
  + left. split; [exact HOK|]. split; [unfold bgs_rows; lia|].
    split; [rewrite prefix_sweep, Hw1'; reflexivity | intros a Ha; exact Ha].
- (* w >= 2: 0x839c8 .. 0x839f0, the outer loop's locals F + 48 and 2^31 - 12, on to the outer loop head 0x839f4, c = 1 *)
  rewrite Dw in Hc.
  lazymatch type of Hc with branch_taken BC_LT _ (sv_denot ?Ev (SLit ?z)) = _ =>
    change (sv_denot Ev (SLit z)) with (Z_to_bv 64 z) in Hc end.
  rewrite mk_blt_lit in Hc by lia. apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HSw HJf SHOKw mk_Bspan 0x2fb8. { mk_awr G9. }
  mk_keep HOK HI9 HL9 HI10 HL10. clear_frames.
  lazymatch type of HSw with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (st_ok_pi_region_nth Ev ssx msx 0%nat _ HSw eq_refl) as HRg1;
    pose proof (st_ok_pi_region_nth Ev ssx msx 1%nat _ HSw eq_refl) as HRg2 end.
  lazymatch type of HRg1 with region_ok _ ?Ev ?mmx (YP09.mkRegion (Some ?n1) ?lo1 ?hi1 ?wlo1 ?whi1 ?cs1) =>
  lazymatch cs1 with context [YP09.mkChunk 40 (CVal ?w1 ?e1)] =>
    pose proof (field_of_region Ev mmx n1 sp1 cs1 lo1 hi1 wlo1 whi1 40 w1 e1 (Fa fpos + 48) HRg1
      ltac:(rewrite G9; apply unsigned_lit_small; lia)
      ltac:(cbn [In]; repeat first [left; reflexivity | right])
      ltac:(cbn [sv_denot]; rewrite ?G24, ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia])
      ltac:(cbn; lia) ltac:(cbn; lia)) as VO1 end end.
  lazymatch type of HRg2 with region_ok _ ?Ev ?mmx (YP09.mkRegion (Some ?n1) ?lo1 ?hi1 ?wlo1 ?whi1 ?cs1) =>
  lazymatch cs1 with context [YP09.mkChunk 72 (CVal ?w1 ?e1)] =>
    pose proof (field_of_region Ev mmx n1 sp1 cs1 lo1 hi1 wlo1 whi1 72 w1 e1 (2 ^ 31 - 9 - 3 * 1) HRg2
      ltac:(rewrite G9; apply unsigned_lit_small; lia)
      ltac:(cbn [In]; repeat first [left; reflexivity | right])
      ltac:(first [reflexivity | vm_compute; reflexivity])
      ltac:(cbn; lia) ltac:(cbn; lia)) as VO2 end end.
  pmkst HSw.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mmy _) _) _ =>
    assert (HLO : loc_out fpos (mrestrict (w_H Wf) mmy) 1) by (split; [exact VO1 | exact VO2]) end.
  eapply (outer fpos (Z.to_nat (w - 1)) 1 _ _ _ _ _ _ HOK ltac:(lia) ltac:(lia) HI10).
  + unfold oregs, rB. repeat split; mk_regs_close HSw AGw Ew.
  + exact HL10.
  + exact HLO.
Qed.

(* ---- S2: F's shadow, the admission and GRANT_HEAD_ACK (0x83730 .. 0x8389c) ------------------------------- *)
(* ---- piece ad: what seg_admit and seg_shadow use ------------------------------------------------------------ *)
Lemma ad_region_kept : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
  intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
  - intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma ad_ap_eq : forall (R1 R2 : bvmap 5 word) (r : bv 5), aregs_preserved R1 R2 -> acallee_saved (bv_unsigned r) ->
  getr R2 r = getr R1 r.
Proof. intros R1 R2 r HP Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma ad_signed_lit : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. assert (Hh : bv_half_modulus 64 = 2 ^ 63) by reflexivity. assert (Hm : bv_modulus 64 = 2 ^ 64) by reflexivity.
  unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Hh, Hm.
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.
Lemma ad_blt_lit : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. unfold bv_lts. rewrite !ad_signed_lit by lia. reflexivity. Qed.
Lemma ad_bge_lit : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. unfold bv_lts. rewrite !ad_signed_lit by lia. reflexivity. Qed.
Lemma ad_amem : forall p n, amem_range p n ->
  p + n <= 0x7fff8000 - 1 \/ (0x10007fff8000 <= p /\ p + n <= 0x800000000000 - 1).
Proof. intros p n H. exact H. Qed.
Lemma ad_amem_lo : forall p n, p + n <= 0x7fff8000 - 1 -> amem_range p n.
Proof. intros p n H. left. exact H. Qed.
Lemma ad_U_not : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SOff n 0) (SLit 18446744073709551615)) = 2 ^ 64 - 1 - x.
Proof. intros E n x Hn Hx. rewrite <- (U_not E n x Hn Hx). rewrite !U_SAlu, !U_SLit. reflexivity. Qed.
Lemma ad_m1 : forall v, Z_to_bv 64 (2 ^ 64 - 1 - v) = w64 (-1 - v).
Proof.
  intros v. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (2 ^ 64 - 1 - v) with ((-1 - v) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma ad_lit_m1 : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1).
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
(* the numbers every step of the two pieces needs: the stack, sp1, the frame F and its shadow *)
Ltac ad_facts HI :=
  let fp := lazymatch type of HI with binv ?f _ _ _ _ _ _ _ => f end in
  pose proof stk_bounds as (KB1 & KB2 & KB3 & KB4 & KB5 & KB6 & KB7);
  pose proof sp1_facts as (KP1 & KP2);
  pose proof asan_consts as (KC1 & KC2 & KC3 & KC4 & KC5);
  assert (KW : 272 <= STKB) by (apply Z.leb_le; vm_compute; reflexivity);
  destruct (binv_frame _ _ _ _ _ _ _ _ HI) as (KF64 & KF4096 & KFceil & KFimg & KF47 & KFam & KFpres & KSpres & KFown);
  pose proof (Z.div_mod (Fa fp) 8 ltac:(lia)) as KD8; pose proof (Z.mod_pos_bound (Fa fp) 8 ltac:(lia)) as KM8;
  assert (KSH : SHa fp = 2147450880 + Fa fp / 8) by reflexivity;
  apply ad_amem in KFam.
(* A run that writes only [sp1 + 32, sp1 + 96) and F's shadow keeps the invariant (E may grow to E'). *)
Lemma ad_binv_step : forall fpos (E E' : Z -> Prop) W2 ly2 S2 mem2 md2 rows mem3 md3,
  binv fpos E W2 ly2 S2 mem2 md2 rows ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((6, fpos) :: own) ly2 S2 W2 mem3 md3 k ->
  (forall a, E a -> E' a) -> (forall a, E' a -> ~ in_img SEGS a) ->
  (forall a, s <= a < s + Z.of_nat (length rows) ->
     0 <= a < 2 ^ 64 /\ ~ (sp1 + 32 <= a < sp1 + 96) /\ ~ (SHa fpos <= a < SHa fpos + 512)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 32 <= a < sp1 + 96) -> ~ (SHa fpos <= a < SHa fpos + 512) ->
     aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) mem3) ->
  binv fpos E' W2 ly2 S2 mem3 md3 rows.
Proof.
  intros fpos E E' W2 ly2 S2 mem2 md2 rows mem3 md3 HI HJ3 HEE HEi Hrw Hout HG.
  ad_facts HI.
  apply (binv_kept fpos E E' W2 ly2 S2 mem2 md2 rows mem3 md3 HI HJ3 HEE HEi).
  - intros a Ha Hw _ Ho. apply Hout; [exact Ha | lia | intros Hs; apply Ho; unfold own6; right; left; exact Hs].
  - intros a Ha. apply Hout; lia.
  - intros a Ha. apply Hout; lia.
  - intros a Ha. apply Hout; lia.
  - intros a Ha. destruct (Hrw a Ha) as (H1 & H2 & H3). apply Hout; assumption.
  - intros a _ Hp. exact (apresent_grows _ _ _ _ HG Hp).
Qed.
Lemma ad_rows_nil : forall fpos a, s <= a < s + Z.of_nat (length (@nil Z)) ->
  0 <= a < 2 ^ 64 /\ ~ (sp1 + 32 <= a < sp1 + 96) /\ ~ (SHa fpos <= a < SHa fpos + 512).
Proof. intros fpos a Ha. cbn [length Z.of_nat] in Ha. lia. Qed.
Lemma ad_nimg_False : forall a : Z, (fun _ : Z => False) a -> ~ in_img SEGS a.
Proof. intros a []. Qed.
(* F's shadow is this call's own to write *)
Lemma ad_awr_sh : forall fpos E W2 ly2 S2 mem2 md2 rows a,
  binv fpos E W2 ly2 S2 mem2 md2 rows -> SHa fpos <= a < SHa fpos + 512 ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 ((6, fpos) :: own) a.
Proof.
  intros fpos E W2 ly2 S2 mem2 md2 rows a HI Ha.
  pose proof (binv_layout _ _ _ _ _ _ _ _ HI) as (_ & _ & _ & LYF & _).
  right; right; right. exists 6, fpos. split; [left; reflexivity|]. right.
  unfold in_zr, shadow_addr. cbn [fst snd]. rewrite LYF. change (fs_frame_bytes 6 / 8) with 512.
  unfold SHa, SBV, Fa in Ha. unfold SHADOW_OFF. lia.
Qed.
Ltac ad_nowin :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros (r & Hr & Hw);
  lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
    repeat match goal with U : bv_unsigned (ew _ _) = _ |- _ => progress rewrite U in Hw end; lia |]);
  try destruct Hr.
(* after a run: the invariant for the run's last memory *)
Ltac ad_upd HI fp E' HEE Hnimg Hrows :=
  lazymatch goal with
  | HFr : frame_of ?Eo ?rs (mrestrict _ _) (mrestrict _ (ms_mem ?m1)),
    HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m1) ?mdx _,
    HG : mem_grows _ (mrestrict _ (ms_mem ?m1)) |- _ =>
    let HI2 := fresh "HI" in
    pose proof (ad_binv_step fp _ E' _ _ _ _ _ _ (ms_mem m1) mdx HI HJx HEE Hnimg Hrows
      ltac:(let a := fresh "a" in let Ha := fresh "Ha" in let H1 := fresh "Hn1" in let H2 := fresh "Hn2" in
            intros a Ha H1 H2; apply (aview_kept_out Eo rs _ _ _ HFr a Ha); ad_nowin) HG) as HI2;
    clear HI HFr HG; rename HI2 into HI
  end.
(* the write rights of the runs: the stack slots through s1 (atom 9) and F's shadow through s7 (atom 23) *)
Ltac ad_awr HI fp :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp0 ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp0 b0 bc ly own);
  repeat first
  [ apply awr_ok_nil
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
    [reflexivity | lazymatch goal with U : bv_unsigned (ew E 9) = _ |- _ => rewrite U end; lia
    | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat (SHa fp));
    [reflexivity | lazymatch goal with U : bv_unsigned (ew E 23) = _ |- _ => exact U end
    | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; apply (ad_awr_sh _ _ _ _ _ _ _ _ a HI); lia |] ] end.
(* after a call and `reseat`: the facts about the old atoms below 33, for the new environment *)
Ltac ad_lift AG :=
  lazymatch type of AG with forall n, _ -> ew ?Ev n = ew ?Eo n =>
  repeat match goal with
  | H : ew Eo ?n = ?v |- _ =>
    lazymatch goal with _ : ew Ev n = _ |- _ => fail | _ =>
      let H2 := fresh "F" in assert (H2 : ew Ev n = v) by (rewrite (AG n) by lia; exact H) end
  | H : bv_unsigned (ew Eo ?n) = ?v |- _ =>
    lazymatch goal with _ : bv_unsigned (ew Ev n) = _ |- _ => fail | _ =>
      let H2 := fresh "U" in assert (H2 : bv_unsigned (ew Ev n) = v) by (rewrite (AG n) by lia; exact H) end
  end end.
(* a callee-saved register across a call *)
Ltac ad_ap HP := lazymatch goal with |- getr _ ?r = _ =>
  rewrite (ad_ap_eq _ _ r HP) by (unfold acallee_saved; let x := eval vm_compute in (bv_unsigned r) in
                                    change (bv_unsigned r) with x; lia) end.
(* the atoms of the goal, by the facts about them *)
Ltac ad_ews :=
  repeat match goal with |- context [ew ?Ex ?n] => match goal with En : ew Ex n = Z_to_bv 64 _ |- _ => rewrite En end end;
  repeat match goal with U : bv_unsigned (ew _ _) = _ |- _ => progress rewrite U end;
  rewrite ?unsigned_lit_small by lia.
(* a register of the state the symbolic run reached, as the boundary predicates state it *)
Ltac ad_rc HS := lazymatch goal with |- getr _ ?r = w64 _ =>
  let H := fresh "Rx" in prreg HS r H; rewrite H; clear H; unfold w64;
  repeat match goal with |- context [ew ?Ex ?n] => match goal with En : ew Ex n = Z_to_bv 64 _ |- _ => rewrite En end end;
  rewrite ?unsigned_lit_small by lia;
  rewrite ?Z.add_0_r; first [reflexivity | exact ad_lit_m1 | f_equal; lia] end.
(* s3 = ~V (0x8388c), as l1regs states it *)
Ltac ad_r19 HS := lazymatch goal with |- getr _ ?r = w64 (-1 - ?v) =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  lazymatch goal with V33 : ew Ex 33 = Z_to_bv 64 v |- _ =>
  let H := fresh "R19" in
  rregU HS r (2 ^ 64 - 1 - v) ltac:(first [apply (U_not Ex 33 v V33); lia | apply (ad_U_not Ex 33 v V33); lia]) H;
  rewrite H; apply ad_m1 end end end.
(* a refusal: on to 0x83b80 (BASE + 0x3144), where epi releases F and returns -1 *)
Ltac ad_refuse RUNTOP HS HJ HI fp Hnb :=
  paj_run_to_sh RUNTOP HS HJ 12612; [ad_awr HI fp |];
  ad_upd HI fp (fun _ : Z => False) (fun (a : Z) (h : (fun _ : Z => False) a) => h) ad_nimg_False (ad_rows_nil fp);
  pmkst HS;
  eapply (epi fp (fun _ => False) _ _ _ _ _ _ [] (-1) HI);
  [ unfold eregs, rB; repeat split; ad_rc HS
  | right; split; [exact Hnb | split; [reflexivity | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact Ha]] ].
Ltac ad_run0 RUNP RUNC HS HJ HI fp :=
  paj_run_shc RUNP RUNC HS HJ; [ad_awr HI fp |];
  ad_upd HI fp (fun _ : Z => False) (fun (a : Z) (h : (fun _ : Z => False) a) => h) ad_nimg_False (ad_rows_nil fp).
(* the state at 0x837a8 (BASE + 0x2d6c): the stack slots s1 + [32, 128) with base, V and s (atoms 32, 33, 34) at
   s1 + 0x60, 0x70, 0x78 and the window [32, 96) the admission writes; F's shadow [395, 412) through s7 *)
Definition ad_ss_ad : sstate := mkSS 0x2d6c sr_atoms
  [YP09.mkRegion (Some 9%nat) 32 128 32 96
     [YP09.mkChunk 96 (CVal 8 (SOff 32 0)); YP09.mkChunk 112 (CVal 8 (SOff 33 0)); YP09.mkChunk 120 (CVal 8 (SOff 34 0))];
   YP09.mkRegion (Some 23%nat) 395 412 395 412 []] None (mkFacts [] [] []).
Lemma seg_admit : forall fpos W2 ly2 S2 regs2 mem2 md2,
  binv fpos (fun _ => False) W2 ly2 S2 mem2 md2 [] -> adregs fpos regs2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x2d6c)) mem2 (seg_rom SEGS)) md2) TBP.
Proof.
intros fpos W2 ly2 S2 regs2 mem2 md2 HI ((R2 & R3 & R4 & R8 & R9) & R18 & R19 & R20 & R23 & R24 & R25 & R27).
pose proof (SRr_run_pi_AJ B LAWS) as RUNP. pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC. pose proof (paj_branch (PI := PI)) as BR.
ad_facts HI.
pose proof HI as (HJ & _ & _ & _ & _ & _ & (L60 & L68 & L70 & L78) & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
remember (Eimg (Ereg regs2 [Z_to_bv 64 base; Z_to_bv 64 V; Z_to_bv 64 s])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite R18 in E18.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite R19 in E19.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite R20 in E20.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite R23 in E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite R24 in E24.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite R25 in E25.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite R27 in E27.
assert (E32 : ew E 32 = Z_to_bv 64 base) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 V) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 s) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
unfold w64 in E2, E3, E4, E8, E9, E18, E19, E20, E23, E24, E25, E27.
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHa fpos) by (rewrite E23; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ad_ss_ad (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x2d6c)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ad_ss_ad. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ sp1 96 8 (SOff 32 0) base);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact L60].
      * apply (chunk_ok_val SEGS E _ sp1 112 8 (SOff 33 0) V);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact L70].
      * apply (chunk_ok_val SEGS E _ sp1 120 8 (SOff 34 0) s);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact L78].
    + rewrite U23. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (KSpres (SHa fpos + o) ltac:(lia)))|].
      apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U23. repeat split; lia.
  - repeat split. }
clear HE EE.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
(* 0x837a8 .. 0x837f4: F's shadow [395, 412) = 0xf3, s10 = -1, then `blez s3` *)
ad_run0 RUNP RUNC HS HJ HI fpos.
psrr_branch_pi RUNP BR HS.
{ (* w <= 0 *)
  cbn [sv_denot] in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E19 in Hc. rewrite ad_bge_lit in Hc by lia.
  assert (Hnb : ~ bgs_ok s V mx base w) by (destruct (Z.ltb_spec 0 w); [discriminate | unfold bgs_ok; lia]).
  ad_refuse RUNTOP HS HJ HI fpos Hnb. }
cbn [sv_denot] in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E19 in Hc. rewrite ad_bge_lit in Hc by lia.
assert (Hw1 : 1 <= w) by (destruct (Z.ltb_spec 0 w); [lia | discriminate]). clear Hc.
(* `beqz s` (0x837fc) *)
ad_run0 RUNP RUNC HS HJ HI fpos.
psrr_branch_pi RUNP BR HS.
{ rewrite branch_eq_U, (U_atom E 34 s E34), U_lit in Hc by lia.
  assert (Hnb : ~ bgs_ok s V mx base w) by (destruct (Z.eqb_spec s 0); [unfold bgs_ok; lia | discriminate]).
  ad_refuse RUNTOP HS HJ HI fpos Hnb. }
rewrite branch_eq_U, (U_atom E 34 s E34), U_lit in Hc by lia.
assert (Hs0 : s <> 0) by (destruct (Z.eqb_spec s 0); [discriminate | lia]). clear Hc.
(* `beqz V` (0x83804) *)
ad_run0 RUNP RUNC HS HJ HI fpos.
psrr_branch_pi RUNP BR HS.
{ rewrite branch_eq_U, (U_atom E 33 V E33), U_lit in Hc by lia.
  assert (Hnb : ~ bgs_ok s V mx base w) by (destruct (Z.eqb_spec V 0); [unfold bgs_ok; lia | discriminate]).
  ad_refuse RUNTOP HS HJ HI fpos Hnb. }
rewrite branch_eq_U, (U_atom E 33 V E33), U_lit in Hc by lia.
assert (HV0 : V <> 0) by (destruct (Z.eqb_spec V 0); [discriminate | lia]). clear Hc.
(* the int check of base + w (0x8381c): its trap is not reached, base + w < 2 ^ 31 *)
ad_run0 RUNP RUNC HS HJ HI fpos.
assert (UW : U E (SAluw ALU_ADD (SOff 32 0) (SOff 19 0)) = base + w)
  by (apply (U_addw_small E); [apply (U_atom E 32 base E32); lia | apply (U_atom E 19 w E19); lia | lia | lia | lia]).
assert (UA : U E (SAlu ALU_ADD (SOff 19 0) (SOff 32 0)) = base + w)
  by (rewrite (U_add_small E _ _ w base); [lia | apply (U_atom E 19 w E19); lia | apply (U_atom E 32 base E32); lia | lia | lia | lia]).
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ne_U, UW, UA, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
(* `blt 48, base + w` (0x83828) *)
ad_run0 RUNP RUNC HS HJ HI fpos.
assert (US : U E (SAluw ALU_ADD (SAlu ALU_ADD (SOff 19 0) (SOff 32 0)) (SLit 0)) = base + w)
  by (rewrite (U_addw_small E _ _ (base + w) 0); [lia | exact UA | apply U_lit; lia | lia | lia | lia]).
psrr_branch_pi RUNP BR HS.
{ rewrite (denot_lit_U E (SAluw _ _ _)), US in Hc. cbn [sv_denot] in Hc. rewrite ad_blt_lit in Hc by lia.
  assert (Hnb : ~ bgs_ok s V mx base w) by (destruct (Z.ltb_spec 48 (base + w)); [unfold bgs_ok; lia | discriminate]).
  ad_refuse RUNTOP HS HJ HI fpos Hnb. }
rewrite (denot_lit_U E (SAluw _ _ _)), US in Hc. cbn [sv_denot] in Hc. rewrite ad_blt_lit in Hc by lia.
assert (Hbw : base + w <= 48) by (destruct (Z.ltb_spec 48 (base + w)); [discriminate | lia]). clear Hc.
(* the int check of 3w (0x8383c) *)
ad_run0 RUNP RUNC HS HJ HI fpos.
assert (UM : U E (SMd M_MUL (SOff 19 0) (SLit 3)) = 3 * w).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E 19 w E19), U_lit by lia. rewrite zcanon_id; [lia | unfold M64; lia]. }
assert (U3W : U E (SAluw ALU_ADD (SAlu ALU_SLL (SOff 19 0) (SLit 1)) (SOff 19 0)) = 3 * w).
{ rewrite (U_addw_small E _ _ (2 * w) w); [lia | | apply (U_atom E 19 w E19); lia | lia | lia | lia].
  apply (U_sll1_small E); [apply (U_atom E 19 w E19); lia | lia | lia]. }
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ne_U, U3W, UM, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
(* the int check of 3w + 8 (0x83848) *)
ad_run0 RUNP RUNC HS HJ HI fpos.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite !(denot_lit_U E) in Hc.
  lazymatch type of Hc with branch_taken _ (Z_to_bv 64 (U E ?a)) (Z_to_bv 64 (U E ?b)) = _ =>
    assert (Ua : U E a = 3 * w + 8) by (rewrite (U_addw_small E _ _ (3 * w) 8); [lia | exact UM | apply U_lit; lia | lia | lia | lia]);
    assert (Ub : U E b = 3 * w) by (rewrite (U_addw_small E _ _ (3 * w) 0); [lia | exact UM | apply U_lit; lia | lia | lia | lia]) end.
  rewrite Ua, Ub, ad_blt_lit in Hc by lia. destruct (Z.ltb_spec (3 * w + 8) (3 * w)); [lia | discriminate]. }
clear Hc.
(* `bge mx, 3w + 8` (0x8384c) *)
ad_run0 RUNP RUNC HS HJ HI fpos.
assert (U38 : U E (SAluw ALU_ADD (SMd M_MUL (SOff 19 0) (SLit 3)) (SLit 8)) = 3 * w + 8)
  by (rewrite (U_addw_small E _ _ (3 * w) 8); [lia | exact UM | apply U_lit; lia | lia | lia | lia]).
psrr_branch_pi RUNP BR HS.
2: { (* mx < 3w + 8 *)
  rewrite (denot_lit_U E (SAluw _ _ _)), U38 in Hc. cbn [sv_denot] in Hc.
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E25, ad_bge_lit in Hc by lia.
  assert (Hnb : ~ bgs_ok s V mx base w) by (destruct (Z.ltb_spec mx (3 * w + 8)); [unfold bgs_ok, bgs_rows; lia | discriminate]).
  ad_refuse RUNTOP HS HJ HI fpos Hnb. }
rewrite (denot_lit_U E (SAluw _ _ _)), U38 in Hc. cbn [sv_denot] in Hc.
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E25, ad_bge_lit in Hc by lia.
assert (Hmx : 3 * w + 8 <= mx) by (destruct (Z.ltb_spec mx (3 * w + 8)); [discriminate | lia]). clear Hc.
(* the call is admitted: GRANT_HEAD_ACK into the first row (0x8385c .. 0x83880) *)
assert (Hok : bgs_ok s V mx base w) by (unfold bgs_ok, bgs_rows; lia).
destruct (HROWS Hok) as (Ram & Rs47 & Rimg & _ & _ & _ & _ & Rwin & _).
unfold bgs_rows in Ram, Rs47, Rimg, Rwin. apply ad_amem in Ram. rewrite IMG_LO_B_val, IMG_TOP_B_val in Rimg.
assert (HnimgR : forall a, RowsE a -> ~ in_img SEGS a).
{ intros a Ha Himg. pose proof (pa_img_range _ Himg) as HR. unfold RowsE, bgs_rows in Ha.
  rewrite IMG_LO_B_val, IMG_TOP_B_val in HR. lia. }
paj_run_shc RUNP RUNC HS HJ; [ad_awr HI fpos |].
ad_upd HI fpos RowsE (fun (a : Z) (h : (fun _ : Z => False) a) => match h return RowsE a with end) HnimgR (ad_rows_nil fpos).
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
pose proof HIMGROWS as (HGA & HinA & _ & _ & HA1 & HA2 & _).
pose proof (proj1 (HGA _ _ (arod_binv _ _ _ _ _ _ _ _ HI))) as HGack.
pose proof (pa_val_range (A_OBJ B_ACK)) as HAR0.
assert (HAk : 0x10000 + 64 <= VAL (A_OBJ B_ACK) /\ VAL (A_OBJ B_ACK) + 34 + 64 <= 0x5fb000)
  by (unfold IMG_LO, IMG_HI in HA1, HA2; rewrite IMG_LO_B_val in HA1; rewrite IMG_TOP_B_val in HA2; lia).
pose proof (img_env_atomP E 263 HEI ltac:(unfold A_TEXT, A_LIM; lia)) as EA.
change (VAL 263) with (VAL (A_OBJ B_ACK)) in EA.
destruct (ro_read_ok_glob SEGS B GRANT_GLOBS_B _ _ W2 _ _ (VAL (A_OBJ B_ACK)) 34 (VAL (A_OBJ B_ACK)) 34 HGL HinA HIMGSH
  (proj1 (proj1 HI)) ltac:(lia) ltac:(lia) ltac:(lia) HA1 ltac:(exact HA2)) as [ARa AHl].
eapply (call_cpy fpos W2 ly2 S2 _ _ [] _ 11848 (VAL (A_OBJ B_ACK)) HEAD_ACK34z _ Hok HI);
change (length HEAD_ACK34z) with 34%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; unfold bgs_rows;
[ lia | lia | exact HGack | lia | lia | lia | apply ad_amem_lo; lia | intros a Ha; unfold ESTACK; lia
| exact ARa | exact AHl | rewrite Ra0, E34; unfold w64; f_equal; lia | rewrite Ra1, EA; reflexivity | rewrite Ra2; reflexivity
| unfold spZ at 1; rewrite Rsp; ad_ews; reflexivity | rewrite Rgp; ad_ews; reflexivity | rewrite Rtp; ad_ews; reflexivity
| exact Rra | lia | reflexivity | ].
intros mem3 md3 regs3 HI3 Hout3 HP3. cbn [app] in HI3.
clear Ra0 Ra1 Ra2 Rsp Rgp Rtp Rra.
pose proof (proj1 HI3) as HJ3.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
(* the call keeps this call's stack slots s1 + [32, 128) *)
reseat HS HJ3 HP3 [0]%nat AG ltac:(eapply (ad_region_kept _ _ _ _ 9%nat sp1);
  [ exact U9 | intros a Ha; apply Hout3; [lia | lia | unfold ESTACK; lia] | intros a Ha; apply Hpres3; lia ]).
ad_lift AG.
clear HI Hout3. rename HI3 into HI.
assert (Hrows34 : forall a, s <= a < s + Z.of_nat (length HEAD_ACK34z) ->
  0 <= a < 2 ^ 64 /\ ~ (sp1 + 32 <= a < sp1 + 96) /\ ~ (SHa fpos <= a < SHa fpos + 512)).
{ intros a Ha. change (length HEAD_ACK34z) with 34%nat in Ha. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. lia. }
(* 0x83884 .. 0x8389c: s10 = 0, s3 = ~V, s4 = F + 1680, s5 = s6 = s + 34: the first channel's loop head *)
paj_run_to_sh RUNTOP HS HJ3 11872; [ad_awr HI fpos |].
ad_upd HI fpos RowsE (fun (a : Z) (h : RowsE a) => h) HnimgR Hrows34.
pmkst HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 0 _ HS eq_refl) as RG end.
lazymatch type of RG with region_ok ?a ?b ?c ?r0 => let r1 := eval vm_compute in r0 in change r0 with r1 in RG end.
cbn [ms_mem restrict] in RG.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
  assert (L1R : l1regs fpos rg 0);
  [ unfold l1regs, rB; repeat split; first [ad_r19 HS | ad_rc HS] |];
  assert (LACC : loc_acc fpos (mrestrict (w_H W2) mm));
  [ lazymatch type of RG with region_ok _ ?Ex _ _ =>
    lazymatch goal with U9x : bv_unsigned (ew Ex 9) = sp1 |- _ =>
    unfold loc_acc; split; [|split; [|split]];
    [ apply (field_of_region _ _ 9%nat sp1 _ _ _ _ _ 64 8%N (SOff 18 0) (Fa fpos) RG U9x)
    | apply (field_of_region _ _ 9%nat sp1 _ _ _ _ _ 32 8%N (SOff 19 0) w RG U9x)
    | apply (field_of_region _ _ 9%nat sp1 _ _ _ _ _ 80 8%N (SOff 20 0) (SHa fpos + 4) RG U9x)
    | apply (field_of_region _ _ 9%nat sp1 _ _ _ _ _ 88 8%N (SOff 24 32) (Fa fpos + 32) RG U9x) ];
    lazymatch goal with
    | |- In _ _ => repeat (first [left; reflexivity | right])
    | |- sv_denot _ _ = _ => cbn [sv_denot]; ad_ews; rewrite ?Z.add_0_r; first [reflexivity | f_equal; lia]
    | |- Z.of_N _ <= _ => cbn; lia
    | |- _ => change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
    end end end |];
  eapply SRr_bind; [exact (row1 fpos 0 HEAD_ACK34z W2 ly2 S2 rg mm mdx Hok ltac:(lia) HI eq_refl L1R LACC) |]
end.
(* the first channel's three rows, then GRANT_HEAD_MARK and on (seg_mark) *)
cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HI5 & HR5 & HL5).
change (0 + 1 =? 3) with false. cbv iota. change (0 + 1) with 1 in HR5.
eapply SRr_bind.
{ eapply (row1 fpos 1 _ W5 ly5 S5 _ _ _ Hok); [lia | exact HI5 | rewrite length_app, len_GAz; reflexivity | exact HR5 | exact HL5]. }
cbv beta. intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & HI6 & HR6 & HL6).
change (1 + 1 =? 3) with false. cbv iota. change (1 + 1) with 2 in HR6.
eapply SRr_bind.
{ eapply (row1 fpos 2 _ W6 ly6 S6 _ _ _ Hok); [lia | exact HI6 | rewrite !length_app, !len_GAz; reflexivity | exact HR6 | exact HL6]. }
cbv beta. intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & -> & HI7 & HR7 & HL7).
change (2 + 1 =? 3) with true. cbv iota. change (2 + 1) with 3 in HR7.
exact (seg_mark fpos W7 ly7 S7 _ _ _ Hok HI7 HR7 HL7).
Qed.
(* the state at 0x83730 (BASE + 0x2cf4): F's shadow [0, 4) and [191, 208) through s7, the two stretches the body
   writes around the first __asan_set_shadow_f8 (which writes [4, 191)) *)
Definition ad_ss_sh : sstate := mkSS 0x2cf4 sr_atoms
  [YP09.mkRegion (Some 23%nat) 0 4 0 4 []; YP09.mkRegion (Some 23%nat) 191 208 191 208 []] None (mkFacts [] [] []).
Lemma seg_shadow : forall fpos W2 ly2 S2 regs2 mem2 md2,
  binv fpos (fun _ => False) W2 ly2 S2 mem2 md2 [] -> shregs fpos regs2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x2cf4)) mem2 (seg_rom SEGS)) md2) TBP.
Proof.
intros fpos W2 ly2 S2 regs2 mem2 md2 HI ((R2 & R3 & R4 & R8 & R9) & R10 & R18 & R19 & R23 & R24 & R25).
pose proof (SRr_run_pi_AJ B LAWS) as RUNP. pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC.
ad_facts HI.
pose proof HI as (HJ & _).
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite R18 in E18.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite R19 in E19.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite R23 in E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite R24 in E24.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite R25 in E25.
unfold w64 in E2, E3, E4, E8, E9, E18, E19, E23, E24, E25.
assert (U23 : bv_unsigned (ew E 23) = SHa fpos) by (rewrite E23; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ad_ss_sh (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x2cf4)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ad_ss_sh. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite U23;
    (split; [lia|]); (split; [lia|]);
    (split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (KSpres (SHa fpos + o) ltac:(lia)))|]);
    apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U23. repeat split; lia.
  - repeat split. }
clear HE EE.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
(* 0x83730 .. 0x8374c: F's shadow [0, 4) = 0xf1, then __asan_set_shadow_f8 (SHF + 4, 187) *)
ad_run0 RUNP RUNC HS HJ HI fpos.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
eapply (call_ss fpos (fun _ => False) 0xf8 (SIGMA GS___asan_set_shadow_f8) W2 ly2 S2 _ _ [] _ 11540 (SHa fpos + 4) 187 _
  SSF8 HI (or_introl eq_refl));
[ rewrite Ra0; ad_ews; reflexivity | rewrite Ra1; reflexivity | lia | lia | lia
| unfold spZ at 1; rewrite Rsp; ad_ews; reflexivity
| rewrite Rgp; ad_ews; reflexivity | rewrite Rtp; ad_ews; reflexivity | exact Rra | lia | reflexivity | ].
intros mem3 md3 regs3 HI3 _ Hout3 Hpres3 HP3.
clear Ra0 Ra1 Rsp Rgp Rtp Rra.
destruct (binv_frame _ _ _ _ _ _ _ _ HI) as (_ & _ & _ & _ & _ & _ & _ & HSp1 & _).
pose proof (proj1 HI3) as HJ3.
(* the call keeps [191, 208), which the next stores write *)
reseat HS HJ3 HP3 [1]%nat AG ltac:(eapply (ad_region_kept _ _ _ _ 23%nat (SHa fpos));
  [ exact U23
  | intros a Ha; apply Hout3; lia
  | intros a Ha; apply Hpres3;
    [lia | exact (proj1 (proj2 (KFown a ltac:(unfold own6; right; left; lia)))) | exact (proj1 (HSp1 a ltac:(lia)))] ]).
ad_lift AG.
clear HI HSp1 Hout3 Hpres3. rename HI3 into HI.
(* 0x83750 .. 0x837a4: F's shadow [191, 208) = 0xf2, then __asan_set_shadow_f8 (SHF + 208, 187) *)
ad_run0 RUNP RUNC HS HJ3 HI fpos.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
eapply (call_ss fpos (fun _ => False) 0xf8 (SIGMA GS___asan_set_shadow_f8) W2 ly2 S2 _ _ [] _ 11628 (SHa fpos + 208) 187 _
  SSF8 HI (or_introl eq_refl));
[ rewrite Ra0; ad_ews; reflexivity | rewrite Ra1; reflexivity | lia | lia | lia
| unfold spZ at 1; rewrite Rsp; ad_ews; reflexivity
| rewrite Rgp; ad_ews; reflexivity | rewrite Rtp; ad_ews; reflexivity | exact Rra | lia | reflexivity | ].
intros mem4 md4 regs4 HI4 _ _ _ HP4.
(* back at 0x837a8 (BASE + 0x2d6c) *)
apply (seg_admit fpos W2 ly2 S2 regs4 mem4 md4 HI4).
unfold adregs, rB. repeat split; ad_ap HP4; ad_rc HS.
Qed.

(* ---- S1: the entry: the machine frame, the class-6 frame and F's header (0x8363c .. 0x8372c) --------------- *)
Let en_RUN := paj_run B LAWS.
Let en_RUNTO := paj_run_to B LAWS.
Let en_RUNTOP := SRr_run_to_pi_AJ B LAWS.
Definition en_extra : list word := [Z_to_bv 64 SBV; Z_to_bv 64 sp1].
Definition en_E : env := Eimg (Ereg regs en_extra).
Definition en_Bx : sv := SOff 32 0.
Definition en_span : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).
(* the locals the body writes through s1 = sp1, the thirteen saves at SP - 104 .. SP, the `sd zero` slot at
   SP - 256, and image B's four image cells (A_OBJ 1 / 35 for the shadow base, A_OBJ 0 / 36 for the flag) *)
Definition en_regions : smem :=
  [ YP09.mkRegion (Some 33%nat) 0x60 0x98 0x60 0x98 [];
    YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [];
    YP09.mkRegion (Some 2%nat) (-256) (-248) (-256) (-248) [];
    got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 36); uar_cell_regionP (A_OBJ 36) ].
Definition en_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SBV SBV 0);
            (33%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 5) ] [] [].
Definition en_ss : sstate := mkSS AF_reac_ctrl_build_grant_sweep sr_atoms en_regions None en_facts.
(* no write window of the runs below reaches outside [SP - 272, SP) *)
Ltac en_winout :=
let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros (r & Hr & Hw);
lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
    repeat match goal with Hq : bv_unsigned (ew _ _) = _ |- _ => rewrite Hq in Hw end; lia |]);
try destruct Hr.
(* carry `every byte outside [SP - 272, SP) is the caller's` across one run *)
Ltac en_upd_out :=
lazymatch goal with
| Ho : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 272 <= a < spZ regs) ->
       aview SEGS (w_H W) ?m0 a = aview SEGS (w_H W) memc a,
  Hg : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) ?m0) |- _ =>
  lazymatch goal with
  | HFr : frame_of ?Eo ?rs (mrestrict _ m0) (mrestrict _ (ms_mem ?m1)),
    HG : mem_grows (mrestrict _ m0) (mrestrict _ (ms_mem ?m1)) |- _ =>
    let Ho2 := fresh "Hout" in let Hg2 := fresh "Hgr" in
    assert (Ho2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 272 <= a < spZ regs) ->
      aview SEGS (w_H W) (ms_mem m1) a = aview SEGS (w_H W) memc a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in let Hw0 := fresh "Hw0" in
          intros a Ha Hw0; rewrite (aview_kept_out Eo rs _ _ _ HFr a Ha) by en_winout; exact (Ho a Ha Hw0));
    assert (Hg2 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem m1)))
      by exact (mem_grows_trans _ _ _ Hg HG);
    clear Ho Hg HFr HG; rename Ho2 into Hout; rename Hg2 into Hgr
  end
end.
(* what this call keeps for its caller, from the entry to the return of __asan_stack_malloc_6 *)
Lemma en_tcj_call : forall (m1 m2 : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 272 <= a < spZ regs) ->
     aview SEGS (w_H W) m1 a = aview SEGS (w_H W) memc a) ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) m1) ->
  acall_kept SEGS B lyc Sc W m1 W m2 (sp1 - ESTACK) sp1 (fun _ => False) ->
  (forall a, spZ regs - STKB <= a < spZ regs -> apresent (w_H W) m2 a) ->
  tcj_kept B STKB lyc Sc W memc W m2 (spZ regs) (fun _ => False).
Proof.
intros m1 m2 Hout Hgr (K1 & K2 & K3 & K4 & K5 & K6) Hpr.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof sp1_facts as (Hsp1m & Hsp1r).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof (proj1 HJc) as HAR.
assert (WS : STKB = 4624) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw _. rewrite K1 by lia. apply Hout; lia.
- intros b m i Hin Hi _.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & Hb4096 & Hbceil & _).
  rewrite (K2 b m i Hin Hi (fun Hq : False => Hq)). apply Hout; lia.
- intros a Hi Ho He. pose proof (Hsegs a Hi) as Hlo.
  rewrite (K3 a Hi Ho He). apply Hout; lia.
- intros cid pos a Hin Hr _.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (Hf0 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfb) as Hse.
  pose proof (proj1 (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia))) as Hs1.
  pose proof (proj2 (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) ltac:(lia)) as Hs2.
  rewrite (K4 cid pos a Hin Hr (fun Hq : False => Hq)).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  apply Hout; unfold SHADOW_OFF, kHighMemBeg, kHighMemEnd in *; destruct Hr as [Hr | Hr]; lia.
- intros a Ha Hw Hp. apply K5; [lia | lia | exact (apresent_grows _ _ _ a Hgr Hp)].
- exact Hpr.
Qed.
(* an address outside every write window of the run after the call *)
Ltac en_win3 tac :=
let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros (r & Hr & Hw);
lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
    repeat match goal with Hq : bv_unsigned (ew _ _) = _ |- _ => rewrite Hq in Hw end; tac |]);
try destruct Hr.
(* collapse the model term after a run: it doubles at every step otherwise *)
Ltac en_mdset :=
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdv) _ =>
  lazymatch mdv with
  | with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := mdv) in *; clearbody m
  | _ => idtac
  end
end.
(* `getr R r = w64 v` from the symbolic state, for the registers the next piece reads.
   No vm_compute here: the goals are open bit-vector equalities. *)
Ltac en_close HS :=
lazymatch goal with |- getr _ ?r = w64 _ =>
  let H := fresh "Rx" in prreg HS r H;
  repeat match goal with Hq : ew _ _ = _ |- _ => rewrite Hq in H end;
  rewrite H; clear H; unfold w64;
  first [ reflexivity | (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity) ]
end.
(* the callee-saved side condition of aregs_preserved, by a closed boolean check *)
Lemma en_csl : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) [2; 3; 4; 8; 9; 19; 25] = true ->
  acallee_saved (bv_unsigned r).
Proof.
intros r H. apply existsb_exists in H as (y & Hy & Hxy). apply Z.eqb_eq in Hxy.
unfold acallee_saved. cbn [In] in Hy. lia.
Qed.
Lemma en_ap : forall (R1 R2 : bvmap 5 word) (r : bv 5), aregs_preserved R1 R2 -> acallee_saved (bv_unsigned r) ->
  getr R2 r = getr R1 r.
Proof. intros R1 R2 r HP Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma en_saved_off : forall p, In p SAVED -> 152 <= fst p <= 248.
Proof. intros p Hp. unfold SAVED in Hp. cbn [In] in Hp. repeat (destruct Hp as [<- | Hp]; [cbn [fst]; lia |]). destruct Hp. Qed.
(* a byte of this call's frame above sp1 survives __asan_stack_malloc_6 *)
Lemma en_vm_kept : forall (m1 m2 : word -> option byte) a n v,
  acall_kept SEGS B lyc Sc W m1 W m2 (sp1 - ESTACK) sp1 (fun _ => False) ->
  sp1 <= a -> a + Z.of_nat n <= spZ regs ->
  val_mem SEGS (mrestrict (w_H W) m1) a n v -> val_mem SEGS (mrestrict (w_H W) m2) a n v.
Proof.
intros m1 m2 a n v (K1 & _) Ha Hn Hv.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof sp1_facts as (Hsp1m & Hsp1r).
assert (WS : STKB = 4624) by reflexivity.
apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) m1 m2 a n v); [|exact Hv].
intros x Hx. apply K1; lia.
Qed.
(* the state seated at 0x836c4, the return of __asan_stack_malloc_6: s1 = sp1 (atom 9) with the shadow-base
   local at s1 + 0x68, and F's header (atom 10 = a0) *)
Definition en_E3 (R : bvmap 5 word) : env := Eimg (Ereg R [Z_to_bv 64 SBV]).
Definition en_regions3 : smem :=
  [ YP09.mkRegion (Some 9%nat) 0x68 0x98 0x90 0x98 [YP09.mkChunk 0x68 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 10%nat) 0 24 0 24 [] ].
Definition en_ss3 : sstate := mkSS 11400 sr_atoms en_regions3 None (mkFacts [(10%nat, HPTR 6)] [] []).
Lemma entry :
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_ctrl_build_grant_sweep)) memc (seg_rom SEGS)) mdc) TBP.
Proof.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof sp1_facts as (Hsp1m & Hsp1r).
pose proof HJc as HJ.
pose proof HJc as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STKB = 4624) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
set (E := en_E) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, en_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs en_extra) E)
by (unfold E, en_E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; unfold E, en_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SBV)
by (unfold E, en_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 sp1)
by (unfold E, en_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs))
by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (EE 1%nat 1%bv eq_refl) as E1.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite Hgp in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite Htp in E4.
pose proof (EE 10%nat 10%bv eq_refl) as E10. rewrite H10 in E10.
pose proof (EE 11%nat 11%bv eq_refl) as E11. rewrite H11 in E11.
pose proof (EE 12%nat 12%bv eq_refl) as E12. rewrite H12 in E12.
pose proof (EE 13%nat 13%bv eq_refl) as E13. rewrite H13 in E13.
pose proof (EE 14%nat 14%bv eq_refl) as E14. rewrite H14 in E14.
unfold w64 in E3, E4, E10, E11, E12, E13, E14.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Usp1 : bv_unsigned (ew E 33) = sp1) by (rewrite E33; apply unsigned_lit_small; lia).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (apply (img_env_atomP E (A_OBJ 0) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (apply (img_env_atomP E (A_OBJ 1) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO35 : ew E (A_OBJ 35) = Z_to_bv 64 (VAL (A_OBJ 35)))
by (apply (img_env_atomP E (A_OBJ 35) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO36 : ew E (A_OBJ 36) = Z_to_bv 64 (VAL (A_OBJ 36)))
by (apply (img_env_atomP E (A_OBJ 36) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 1)) as R1v.
pose proof (pa_val_range (A_OBJ 35)) as R35. pose proof (pa_val_range (A_OBJ 36)) as R36.
pose proof (pa_obj_img 0 ltac:(lia)) as I0. pose proof (pa_obj_img 1 ltac:(lia)) as I1.
pose proof (pa_obj_img 35 ltac:(lia)) as I35. pose proof (pa_obj_img 36 ltac:(lia)) as I36.
rewrite IMG_LO_B_val, IMG_TOP_B_val in I0, I1, I35, I36.
assert (U0 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite EO0; apply unsigned_lit_small; lia).
assert (U1v : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1)) by (rewrite EO1; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E (A_OBJ 35)) = VAL (A_OBJ 35)) by (rewrite EO35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E (A_OBJ 36)) = VAL (A_OBJ 36)) by (rewrite EO36; apply unsigned_lit_small; lia).
pose proof (pal_uar_cell B TL) as Euc. pose proof (palf_uar_al B TLF) as Hual.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep. rewrite Euc in Hsep.
rewrite Euc in Hual.
aconstsF HJ Kgot Kcell Kguar Kuar. rewrite Euc in Kguar, Kuar.
assert (HS : st_ok_pi SEGS VAL E en_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_ctrl_build_grant_sweep)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold en_ss. apply pa_entry_st_ok_full.
- unfold E, en_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold en_regions, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp1. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + cbn [base_val]. rewrite U1v. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
    [cbn [sv_denot]; rewrite EO35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact Kgot.
  + cbn [base_val]. rewrite U35. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF, SBV; lia | lia |].
    rewrite Z.add_0_r. exact Kcell.
  + cbn [base_val]. rewrite U0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 36) 0) (VAL (A_OBJ 36)));
    [cbn [sv_denot]; rewrite EO36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact Kguar.
  + cbn [base_val]. rewrite U36. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 36)) 0 4 (SLit 1) 1); [reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact Kuar.
- apply pairwise_disjoint_of_extents.
  unfold en_regions, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite Usp, Usp1, U0, U1v, U35, U36.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hsep I0 I1 I35 I36 B1 B2 B3 B4 Hsp1r C1 WS Hes. clear. intros. repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]].
  cbn [en_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Usp1, E32, unsigned_lit_small by (unfold SBV; lia).
  change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SBV. repeat split; try lia. }
clear Hsep.
assert (SHOK : sh_ok SEGS en_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (Hsp116 : sp1 mod 16 = 0)
by (unfold sp1; replace (32 * ((spZ regs - 256) / 32)) with (2 * ((spZ regs - 256) / 32) * 16) by lia;
    apply Z_mod_mult).
assert (Hout : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 272 <= a < spZ regs) ->
  aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by (intros; reflexivity).
assert (Hgr : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
unfold TBP.
(* run 1: the machine frame, the saves and `andi sp,sp,-32` (0x8363c .. 0x8367c) *)
paj_run_to_tok en_RUNTO HS HJ SHOK en_span (AF_reac_ctrl_build_grant_sweep + 0x44).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 33%nat (sp1 - sp0));
  [reflexivity | rewrite Usp1; lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
  [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
  [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  do 4 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
en_upd_out. en_mdset.
(* sp1 is atom 33 from here on *)
pose proof (st_ok_pi_restrict_reg (w_H W) E _ _ (2%bv : bv 5) HS) as R2.
lazymatch type of R2 with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
  let e := eval vm_compute in (sr_get (ss_regs ssx) (2%bv : bv 5)) in
  change (sr_get (ss_regs ssx) (2%bv : bv 5)) with e in R2 end.
rewrite (denot_and_m32 E 2 (spZ regs) (-256) E2 ltac:(lia) ltac:(lia) ltac:(lia)) in R2.
cbn [ms_regs restrict mkst] in R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 33 0) HS eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite R2; cbn [sv_denot];
          rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS. clear R2.
(* run 2: s1 = sp1, the four locals, the two image cells and the call of __asan_stack_malloc_6 *)
paj_run_tok en_RUN HS HJ SHOK en_span.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 33%nat (sp1 - sp0));
  [reflexivity | rewrite Usp1; lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
  [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
  [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  do 4 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
en_upd_out. en_mdset.
(* the call site: the registers the body keeps, the four locals (region 0) and the thirteen saves (region 1) *)
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (19%bv : bv 5) R19. prreg HS (25%bv : bv 5) R25.
rewrite E33 in Rsp, R9. rewrite E2 in R8. rewrite E13 in R19. rewrite E11 in R25.
rewrite (EE 3%nat 3%bv eq_refl), Hgp in Rgp. rewrite (EE 4%nat 4%bv eq_refl), Htp in Rtp.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS eq_refl) as RG33;
  pose proof (st_ok_region_nth Ex ssx msx 1 r1 HS eq_refl) as RG2 end.
cbn [ms_mem restrict mkst] in RG33, RG2.
lazymatch type of RG33 with region_ok _ ?Ev ?mm (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
assert (HLOC0 : loc0 mm);
[ unfold loc0; split; [|split; [|split]];
  [ exact (field_of_region Ev mm 33%nat sp1 cs lo hi wlo whi 0x60 8%N (SOff 12 0) base RG33 Usp1
      ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia))
  | exact (field_of_region Ev mm 33%nat sp1 cs lo hi wlo whi 0x68 8%N (SOff 32 0) SBV RG33 Usp1
      ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(unfold SBV; cbn; lia) ltac:(cbn; lia))
  | exact (field_of_region Ev mm 33%nat sp1 cs lo hi wlo whi 0x70 8%N (SOff 14 0) V RG33 Usp1
      ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E14, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia))
  | exact (field_of_region Ev mm 33%nat sp1 cs lo hi wlo whi 0x78 8%N (SOff 10 0) s RG33 Usp1
      ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) ] | ] end.
lazymatch type of RG2 with region_ok _ ?Ev ?mm (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
assert (HSV0 : bgs_saved mm);
[ unfold bgs_saved, SAVED; repeat apply Forall_cons; try apply Forall_nil; cbv beta; cbn [fst snd];
  lazymatch goal with |- val_mem _ _ (_ + ?off) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat ?r)))) =>
    replace (spZ regs - 256 + off) with (spZ regs + (off - 256)) by lia;
    let od := eval vm_compute in (off - 256) in change (off - 256) with od;
    exact (field_of_region Ev mm 2%nat (spZ regs) cs lo hi wlo whi od 8%N (SOff r 0)
      (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r)))) RG2 Usp
      ltac:(cbn [In]; tauto)
      ltac:(cbn [sv_denot]; rewrite (EE r (Z_to_bv 5 (Z.of_nat r)) eq_refl), Z.add_0_r; reflexivity)
      ltac:(exact (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (Z.of_nat r)))))
      ltac:(cbn; lia)) end | ] end.
clear RG33 RG2.
(* the class-6 frame: __asan_stack_malloc_6 (a0 = 3296) at 0x836c0 *)
pmkst HS. rewrite (palf_sm6 B TLF).
pose proof (count_cid_le_length 6 (frames Sc)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) ML SMP 6 ASM6 ltac:(lia) W (ms_regs msX) (ms_mem msX)
  STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ) end.
  - unfold spZ at 1. rewrite Rsp, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp116, B5. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - exact Rgp.
  - exact Rtp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - let v := eval vm_compute in (fs_frames 6) in change (fs_frames 6) with v. lia. }
cbv beta. clear R1 SHOK HS.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin &
Hnev2 & Hbb2 & Hz & Hflag & HK & HJin & (fS2 & ES2)).
(* the frame the runtime gave us: F = Fa fpos, 4096 bytes, flag pointer at F + 4088 *)
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Hfin2 : In (6, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 6 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 6 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
destruct (frame_al64 SEGS B _ _ _ _ _ 6 fpos HAR2 Hfin2) as (HFal64 & _ & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
change (fs_frame_bytes 6) with 4096 in HFpres, HFceil, HFapp, Hflag.
change (frame_addr lyc 6 fpos) with (Fa fpos) in HFal64, HFpres, HF4096, HFceil, HFapp, Hflag, Ha0.
change (flag_addr lyc 6 fpos) with (FLa fpos) in Hflag.
assert (HF8 : 0 <= Fa fpos / 8 <= 2 ^ 44)
by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
replace (Fa fpos + 4096 - 8) with (Fa fpos + 4088) in Hflag by lia.
replace (sp0 + (sp1 - sp0)) with sp1 in HK by lia.
(* the locals and the saves survive the call: they lie above sp1 *)
assert (HLOC : loc0 (mrestrict (w_H W) mem2))
by (destruct HLOC0 as (L1 & L2 & L3 & L4); unfold loc0;
    split; [|split; [|split]]; (eapply en_vm_kept; [exact HK | lia | cbn; lia | eassumption])).
assert (HSV : bgs_saved (mrestrict (w_H W) mem2))
by (unfold bgs_saved in *; rewrite Forall_forall in *; intros p Hp; pose proof (en_saved_off p Hp) as Hop;
    eapply en_vm_kept; [exact HK | lia | cbn; lia | exact (HSV0 p Hp)]).
(* the invariant at the return of __asan_stack_malloc_6 *)
assert (HI2 : binv fpos (fun _ => False) W lyc S2 mem2 md2 [])
by (unfold binv; split; [exact HJ2|]; split; [exact Hfrs2|]; split; [exact Eab|];
    split; [exists fS2; exact ES2|];
    split; [eapply en_tcj_call; [exact Hout | exact Hgr | exact HK | intros a Ha; apply Hpres2; lia]|];
    split; [exact HSV|]; split; [exact HLOC|]; split; [exact Hflag | apply garr8_nil]).
(* the registers the body keeps across the call *)
assert (G2 : getr regs2 2 = Z_to_bv 64 sp1)
by (rewrite (en_ap _ _ (2%bv : bv 5) HP2 (en_csl (2%bv : bv 5) eq_refl)); exact Rsp).
assert (G3 : getr regs2 3 = w64 (as_gp B))
by (rewrite (en_ap _ _ (3%bv : bv 5) HP2 (en_csl (3%bv : bv 5) eq_refl)); exact Rgp).
assert (G4 : getr regs2 4 = w64 (as_tp B))
by (rewrite (en_ap _ _ (4%bv : bv 5) HP2 (en_csl (4%bv : bv 5) eq_refl)); exact Rtp).
assert (G8 : getr regs2 8 = Z_to_bv 64 (spZ regs))
by (rewrite (en_ap _ _ (8%bv : bv 5) HP2 (en_csl (8%bv : bv 5) eq_refl)); exact R8).
assert (G9 : getr regs2 9 = Z_to_bv 64 sp1)
by (rewrite (en_ap _ _ (9%bv : bv 5) HP2 (en_csl (9%bv : bv 5) eq_refl)); exact R9).
assert (G19 : getr regs2 19 = Z_to_bv 64 w)
by (rewrite (en_ap _ _ (19%bv : bv 5) HP2 (en_csl (19%bv : bv 5) eq_refl)); exact R19).
assert (G25 : getr regs2 25 = Z_to_bv 64 mx)
by (rewrite (en_ap _ _ (25%bv : bv 5) HP2 (en_csl (25%bv : bv 5) eq_refl)); exact R25).
clear Rsp Rgp Rtp R8 R9 R19 R25 HJ Hout Hgr HLOC0 HSV0.
(* a fresh state at 0x836c4: s1 = sp1 is atom 9, F = a0 is atom 10, SBV is atom 32 *)
set (Ef := en_E3 regs2).
assert (HEI3 : img_env VAL A_LIM Ef) by (unfold Ef, en_E3; apply Eimg_env).
assert (FE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ef n = getr regs2 r)
by (intros n r Hn; unfold Ef, en_E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (F32 : ew Ef 32 = Z_to_bv 64 SBV)
by (unfold Ef, en_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
pose proof (FE 2%nat 2%bv eq_refl) as F2. rewrite G2 in F2.
pose proof (FE 3%nat 3%bv eq_refl) as F3. rewrite G3 in F3.
pose proof (FE 4%nat 4%bv eq_refl) as F4. rewrite G4 in F4.
pose proof (FE 8%nat 8%bv eq_refl) as F8. rewrite G8 in F8.
pose proof (FE 9%nat 9%bv eq_refl) as F9. rewrite G9 in F9.
pose proof (FE 10%nat 10%bv eq_refl) as F10. rewrite Ha0 in F10.
pose proof (FE 19%nat 19%bv eq_refl) as F19. rewrite G19 in F19.
pose proof (FE 25%nat 25%bv eq_refl) as F25. rewrite G25 in F25.
unfold w64 in F3, F4, F10.
assert (U9 : bv_unsigned (ew Ef 9) = sp1) by (rewrite F9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew Ef 10) = Fa fpos) by (rewrite F10; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL Ef en_ss3 (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + 11400)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold en_ss3. apply pa_entry_st_ok_full.
- unfold Ef, en_E3. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold en_regions3. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable SEGS). apply Hpres2. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val SEGS Ef _ sp1 0x68 8 (SOff 32 0) SBV);
      [cbn [sv_denot]; rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBV; lia | lia |].
      exact (proj1 (proj2 HLOC)).
  + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (Fa fpos + o) ltac:(lia))).
- apply pairwise_disjoint_of_extents. unfold en_regions3, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U10.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert HF4096 HFceil B1 B2 B3 B4 Hsp1r C1 WS. clear. intros. repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
  rewrite U10. change (2 ^ 6) with 64. lia. }
clear HFapp.
(* run 3: the carve is refuted, F's header is written, s7 = SHa fpos (0x836c4 .. 0x8372c) *)
paj_run_to_sh en_RUNTOP HS HJ2 (AF_reac_ctrl_build_grant_sweep + 0xf4).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
  [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat (Fa fpos));
  [reflexivity | exact U10
  | cbn [YP09.r_wlo YP09.r_whi]; intros aq Haq; right; right; right; exists 6, fpos;
    split; [left; reflexivity|]; left; unfold in_zr, frame_rng; cbn [fst snd];
    change (fs_frame_bytes 6) with 4096; change (frame_addr lyc 6 fpos) with (Fa fpos); lia |].
  apply awr_ok_nil. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
  assert (HI3 : binv fpos (fun _ => False) W lyc S2 mm mdx []);
  [ eapply (binv_kept fpos (fun _ => False) (fun _ => False) W lyc S2 mem2 md2 [] mm mdx HI2 HJ2);
    [ intros a Hq; exact Hq
    | intros a Hq; destruct Hq
    | intros a Ha Hw _ Hno; apply (aview_kept_out _ _ _ _ _ HFr a Ha);
      en_win3 ltac:(idtac; lazymatch goal with
        | Hq : Fa fpos + _ <= a < Fa fpos + _ |- _ => apply Hno; unfold own6; left; lia
        | _ => lia end)
    | intros a Ha; apply (aview_kept_out _ _ _ _ _ HFr a ltac:(lia)); en_win3 ltac:(lia)
    | intros a Ha; apply (aview_kept_out _ _ _ _ _ HFr a ltac:(lia)); en_win3 ltac:(lia)
    | intros a Ha; apply (aview_kept_out _ _ _ _ _ HFr a ltac:(lia)); en_win3 ltac:(lia)
    | intros a Ha; cbn [length Z.of_nat] in Ha; exfalso; lia
    | intros a Ha Hp; exact (apresent_grows _ _ _ a HG Hp) ] |];
  assert (HR : shregs fpos rg);
  [ unfold shregs, rB; repeat split;
    [ en_close HS | en_close HS | en_close HS | en_close HS | en_close HS | en_close HS | en_close HS
    | en_close HS
    | lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hh ?msx) =>
        let e := eval vm_compute in (sr_get (ss_regs ssx) (23%bv : bv 5)) in
        refine (eq_trans (st_ok_pi_restrict_reg Hh Ev ssx msx (23%bv : bv 5) HS) _);
        change (sv_denot Ev e = w64 (SHa fpos));
        unfold w64, SHa; rewrite denot_lit_U; f_equal;
        rewrite U_SAlu; cbn [zalu_raw];
        rewrite U_srl3, (U_atom Ev 10%nat (Fa fpos) F10 ltac:(lia)), (U_atom Ev 32%nat SBV F32 ltac:(unfold SBV; lia));
        rewrite (zcanon_id (Fa fpos / 8 + SBV) ltac:(unfold M64, SBV; lia)); lia end
    | en_close HS | en_close HS ] |];
  exact (seg_shadow fpos W lyc S2 rg mm mdx HI3 HR) end.
Qed.

End w.

Theorem pb_reac_ctrl_build_grant_sweep : walk_reac_ctrl_build_grant_sweep B.
Proof.
  unfold walk_reac_ctrl_build_grant_sweep, hyps_reac_ctrl_build_grant_sweep, tb_reac_ctrl_build_grant_sweep_spec.
  unfold RT_LAWS, RT_PALIB, RT_PALIBF, RT_ML, RT_SMP, RT_SM, RT_SF6, RT_FFL, RT_TP_FS, RT_SS00, RT_SSF8,
    RT_MEMCPY, RT_MEMSET, RT_IMGSH, RT_GLOBS, IMG_RO_BELOW.
  intros (HL & HPL & HPLF & HML & HSMP & HSM6 & HSF6 & HFFL & HTP & HSS00 & HSSF8 & HCPY & HSET & HIMGSH & HGLOBS
    & HRO & HIMGROWS) HST.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs s mx base w V vals cl
    HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 H13 H14 Rs Rmx Rbase Rw RV Hbw Hch Hal16 Hwlo Hwhi Hfr8 HVALS HROWS.
  unfold cfg_at, w64.
  eapply entry; eassumption.
Qed.
End W.
