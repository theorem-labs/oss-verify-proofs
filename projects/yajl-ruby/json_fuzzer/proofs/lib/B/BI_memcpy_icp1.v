(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BI_shadow BM_memcpy BI_region_is_poisoned.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition memcpy_icp_entry : Z := 0x53520.
End RC__1.
Ltac showpc := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc end.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition memcpy_icp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S n SB : Z) (src wsS wsD : list byte) (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + n)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' D [CB (Z.to_nat n) src]
    /\ bytes_at bsegs m' S src
    /\ icp_globals bsegs m' SB
    /\ shadow_window bsegs m' SB S n wsS /\ shadow_window bsegs m' SB D n wsD.

Section Walk.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (D S n SB : Z) (src wsS wsD : list byte) (lo : Z).
Hypothesis LOC : (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 2240.
Hypothesis HN : 1 <= n < 2^40.
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis RIMS : range_in_mem SB S n.
Hypothesis RIMD : range_in_mem SB D n.
Hypothesis HSN : S + n < 2^47.
Hypothesis HDN : D + n < 2^47.
Hypothesis SEP : S + n <= D \/ D + n <= S.
Hypothesis HDISJS : S + n <= lo \/ bv_unsigned sp <= S.       (* [comment removed for export] *)
Hypothesis HDISJD : D + n <= lo \/ bv_unsigned sp <= D.       (* [comment removed for export] *)
Hypothesis HGL : D + n <= 0xa5000 \/ 0xaf840 <= D.          (* [comment removed for export] *)
Hypothesis SHLS : Z.of_nat (length wsS) = shw_hi SB S n - shw_lo SB S.
Hypothesis SHLD : Z.of_nat (length wsD) = shw_hi SB D n - shw_lo SB D.
Hypothesis RCS : range_clean SB S n wsS.
Hypothesis RCD : range_clean SB D n wsD.
Hypothesis HSWS : shw_hi SB S n <= D \/ D + n <= shw_lo SB S.  (* [comment removed for export] *)
Hypothesis HSWD : shw_hi SB D n <= D \/ D + n <= shw_lo SB D.
Hypothesis SBR : 2^24 <= SB < 2^32.
(* [comment removed for export] *)
Hypothesis PSHD : forall a k, shw_lo SB D <= a -> a + Z.of_nat k <= shw_hi SB D n -> P (Z_to_bv 64 a, k).
Hypothesis PSHS : forall a k, shw_lo SB S <= a -> a + Z.of_nat k <= shw_hi SB S n -> P (Z_to_bv 64 a, k).
Hypothesis PDST : forall a k, D <= a -> a + Z.of_nat k <= D + n -> P (Z_to_bv 64 a, k).
Hypothesis PSRC : forall a k, S <= a -> a + Z.of_nat k <= S + n -> P (Z_to_bv 64 a, k).
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PSTK : forall a k, bv_unsigned sp - 2240 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Ltac hideD := hideH SEP; hideH HDISJS; hideH HDISJD; hideH HGL; hideH HSWS; hideH HSWD; hideH RIMS; hideH RIMD.
Ltac unhideD := unfold hidden in SEP, HDISJS, HDISJD, HGL, HSWS, HSWD, RIMS, RIMD.
(* [comment removed for export] *)
Lemma BNDS : 0 < S /\ S + n < 2^47 /\ 0 < D /\ D + n < 2^47.
Proof. unfold range_in_mem in RIMS, RIMD. lia. Qed.

Notation POST := (memcpy_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n SB src wsS wsD m lo).
Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -2160)).
Notation gD1 := (Z.shiftr D 3).
Notation gD2 := (Z.shiftr (D + n + -1) 3).
(* [comment removed for export] *)
Notation SP8 := (Z_to_bv 64 (bv_unsigned sp + -2152)).
Notation ST pc mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31 :=
  (MS (mkR x1 SP' gp tp x5 x6 x7 sp x9 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) x13 x14 x15 x16 x17 x18 x19 x20 SP8 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
(* [comment removed for export] *)
Definition MINV (m0 : mem) : Prop :=
  mem_inv bsegs m0 /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp); (D, D + n)] m m0 /\ wmono bsegs m m0 /\
  stk bsegs m0 lo (bv_unsigned sp + -80) /\
  rw_cells bsegs m0 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  (exists junk, rw_cells bsegs m0 D [CB (Z.to_nat n) junk]) /\ bytes_at bsegs m0 S src /\
  icp_globals bsegs m0 SB /\ bytes_at bsegs m0 (shw_lo SB S) wsS /\ bytes_at bsegs m0 (shw_lo SB D) wsD.

Ltac open_minv H := destruct H as (MI & MU & WM & SK & FR & [junk DST] & SRC & G & SHS & SHD).

Lemma GEOD :
  0 <= gD1 /\ gD1 <= gD2 /\ 8 * gD1 <= D < 8 * gD1 + 8 /\ 8 * gD2 <= D + n + -1 < 8 * gD2 + 8 /\
  shw_lo SB D <= SB + gD1 /\ SB + gD1 < shw_lo SB D + 8 /\ shw_lo SB D mod 8 = 0 /\
  shw_hi SB D n - 8 <= SB + gD2 /\ SB + gD2 < shw_hi SB D n /\ shw_hi SB D n mod 8 = 0 /\
  shw_lo SB D + 8 <= shw_hi SB D n.
Proof. unfold range_in_mem in RIMD. exact (shw_geom SB D n ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

Lemma GEOS :
  0 <= Z.shiftr S 3 /\ Z.shiftr S 3 <= Z.shiftr (S + n + -1) 3 /\ 8 * Z.shiftr S 3 <= S < 8 * Z.shiftr S 3 + 8 /\
  8 * Z.shiftr (S + n + -1) 3 <= S + n + -1 < 8 * Z.shiftr (S + n + -1) 3 + 8 /\
  shw_lo SB S <= SB + Z.shiftr S 3 /\ SB + Z.shiftr S 3 < shw_lo SB S + 8 /\ shw_lo SB S mod 8 = 0 /\
  shw_hi SB S n - 8 <= SB + Z.shiftr (S + n + -1) 3 /\ SB + Z.shiftr (S + n + -1) 3 < shw_hi SB S n /\ shw_hi SB S n mod 8 = 0 /\
  shw_lo SB S + 8 <= shw_hi SB S n.
Proof. unfold range_in_mem in RIMS. exact (shw_geom SB S n ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

Lemma SPR : 0 <= bv_unsigned sp < 2^64.
Proof. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

(* [comment removed for export] *)
Lemma mci_tail : forall m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31,
  MINV m0 ->
  evtA bsegs P POST (ST 0x53614 m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. open_minv IV.
  pose proof GEOD as GE. pose proof BNDS as BN. hideD.
  pose proof G as G'. icp_globals_open G.
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  assert (UD : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (US : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unhideH SEP. unhideH HDISJD. unhideH HSWS. unhideH HSWD. unhideH HGL.
  callA memcpy_spec.
  1:{ intros a k H1 H2. rewrite ?UD, ?US, ?UN in H1. rewrite ?UD, ?US, ?UN in H2. apply PSRC; lia. }
  1:{ intros a k H1 H2. rewrite ?UD, ?US, ?UN in H1. rewrite ?UD, ?US, ?UN in H2. apply PDST; lia. }
  1:{ rewrite US. exact SRC. }
  1:{ rewrite UN. exact LEN. }
  1:{ rewrite UD, UN. exact DST. }
  1:{ rewrite US, UD, UN. exact SEP. }
  1:{ exact MI. }
  ret_pc_lit. rewrite ?UD, ?US, ?UN in *. hideD.
  lazymatch goal with H : rw_cells bsegs ?mx D _ |- _ => rename H into DST2 end.
  lazymatch goal with H : bytes_at bsegs ?mx S src |- _ => rename H into SRC2 end.
  stepA. (* [comment removed for export] *)
  do 10 stepA. (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp).
  apply evtA_done. unfold memcpy_icp_post.
  do 15 eexists. split; [reflexivity|].
  unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
    A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL, shadow_window.
  repeat match goal with |- _ /\ _ => split end; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma mci_dloop : forall k (Q : machine_state -> Prop) m0 j x1 x5 x6 x7 x9 x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31,
  Z.to_nat (gD2 - j) = k -> gD1 <= j < gD2 ->
  bytes_at bsegs m0 (shw_lo SB D) wsD ->
  evtA bsegs P Q (ST 0x539b0 m0 x1 x5 x6 x7 x9 (Z_to_bv 64 (SB + gD2)) (Z_to_bv 64 (SB + gD2)) (Z_to_bv 64 0) (Z_to_bv 64 0) x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31) ->
  evtA bsegs P Q (ST 0x539a0 m0 x1 x5 x6 x7 x9 (Z_to_bv 64 (SB + j)) (Z_to_bv 64 (SB + gD2)) (Z_to_bv 64 0) x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31).
Proof.
  induction k as [|k IH]; intros until x31; intros Hk Hj SHB CONT; pose proof GEOD as GE; [lia|]. pose proof BNDS as BN. hideD.
  pose proof (range_clean_inner SB D n wsD j RCD ltac:(lia)) as Hb.
  pose proof (u8ro_read bsegs m0 (shw_lo SB D) wsD (SB + j - shw_lo SB D) _ (Z_to_bv 64 (SB + j)) SHB Hb ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. (* [comment removed for export] *) clear RD.
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K; zify_cond K.
  - replace (SB + j + 1) with (SB + (j + 1)) by lia. eapply (IH Q m0 (j + 1)); try lia; try assumption.
  - replace (SB + j + 1) with (SB + gD2) by lia. exact CONT.
Qed.

(* [comment removed for export] *)
Lemma mci_djoin : forall m0 x1 x5 x6 x7 x9 x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31,
  MINV m0 ->
  evtA bsegs P POST (ST 0x539b0 m0 x1 x5 x6 x7 x9 (Z_to_bv 64 (SB + gD2)) (Z_to_bv 64 (SB + gD2)) (Z_to_bv 64 0) x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. hideD.
  zstepA. zstepA. (* [comment removed for export] *)
  eapply mci_tail; eassumption.
Qed.

(* [comment removed for export] *)
Lemma mci_dslow : forall m0 x1 x5 x6 x7 x9 x15 x16 x17 x18 x19 x22 x23 x24 x28 x29 x30 x31,
  MINV m0 ->
  evtA bsegs P POST (ST 0x53984 m0 x1 x5 x6 x7 x9 (Z_to_bv 64 (SB + gD1)) (Z_to_bv 64 (SB + gD2)) x15 x16 x17 x18 x19 (Z_to_bv 64 (D + n + -1)) x22 x23 x24 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. pose proof IV as IV'. open_minv IV.
  pose proof GEOD as GE. pose proof BNDS as BN. hideD.
  destruct (RCD gD2 ltac:(lia)) as (k2 & Hk2 & K2).
  pose proof (u8ro_read bsegs m0 (shw_lo SB D) wsD (SB + gD2 - shw_lo SB D) _ (Z_to_bv 64 (SB + gD2)) SHD Hk2 ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. (* [comment removed for export] *) clear RD.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  lazymatch goal with |- context [Z_to_bv 64 (Z.land (Z.b2z ?t) ?u)] =>
    change (Z.land (Z.b2z t) u) with (aip_expr (bv_unsigned (sxb k2)) (Z.land (D + n + -1) 7)) end.
  rewrite (aip_last_clean k2 (D + n + -1)) by (first [lia | destruct K2 as [K2|[_ K2]]; [left; exact K2| right; lia]]).
  zstepA. (* [comment removed for export] *)
  clear MI MU WM SK FR DST SRC G SHS.
  if_cases KG; zify_cond KG.
  - replace (SB + gD1) with (SB + gD2) by lia. eapply mci_djoin; exact IV'.
  - eapply (mci_dloop (Z.to_nat (gD2 - gD1)) _ m0 gD1); [reflexivity | lia | exact SHD |].
    eapply mci_djoin; exact IV'.
Qed.

(* [comment removed for export] *)
Lemma mci_dsmall : forall m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x28 x29 x30 x31,
  MINV m0 -> n <= 64 ->
  evtA bsegs P POST (ST 0x535dc m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (D + n)) x22 x23 x24 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV Hn64. pose proof IV as IV'. open_minv IV.
  pose proof GEOD as GE. pose proof BNDS as BN. hideD.
  icp_globals_open G.
  stepA. stepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  rewrite ?land_m8, ?land_m8' by lia.
  change (al8 (SB + D ≫ 3)) with (shw_lo SB D).
  replace (al8 (SB + (D + n + -1) ≫ 3)) with (shw_hi SB D n - 8) by (unfold shw_hi; lia).
  pose proof (bytes_at_read bsegs _ _ _ 0 8 SHD ltac:(lia) ltac:(lia)) as RD1. rewrite Z.add_0_r in RD1.
  stepA. clear RD1.
  pose proof (bytes_at_read bsegs _ _ _ (shw_hi SB D n - 8 - shw_lo SB D) 8 SHD ltac:(lia) ltac:(lia)) as RD2.
  replace (shw_lo SB D + (shw_hi SB D n - 8 - shw_lo SB D)) with (shw_hi SB D n - 8) in RD2 by lia.
  stepA. clear RD2.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  clear MI MU WM SK FR DST SRC SHS SHD GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI.
  if_cases KW.
  - eapply mci_dslow; exact IV'.
  - eapply mci_tail; exact IV'.
Qed.

(* [comment removed for export] *)
Lemma mci_dbig : forall m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31,
  MINV m0 -> 65 <= n ->
  evtA bsegs P POST (ST 0x539b8 m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV Hn65. open_minv IV.
  pose proof GEOD as GE. pose proof GEOS as GES. pose proof SPR as SR. pose proof BNDS as BN. hideD.
  zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2160)) = bv_unsigned sp + -2160) by (apply unsigned_lit; lia).
  destruct (stk_split bsegs m0 lo (bv_unsigned sp + -2160) (bv_unsigned sp + -80) SK ltac:(lia)) as [SKlo SKhi]. clear SK.
  pose proof G as Gc. icp_globals_open Gc.
  unhideH HDISJS. unhideH HDISJD.
  callA (region_is_poisoned_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D n SB wsD lo P).
  1:{ rewrite USP. exact SKlo. }
  1:{ unfold alloc_ceiling, sp_window_lo, stack_max_size. lia. }
  1:{ rewrite USP. lia. }
  1:{ exact MI. }
  1:{ reflexivity. } 1:{ reflexivity. }
  1:{ lia. } 1:{ lia. } 1:{ exact RIMD. } 1:{ exact G. }
  1:{ split; [exact SHD | exact SHLD]. } 1:{ exact RCD. }
  1:{ intros a k H1 H2. rewrite USP in H1, H2. apply PSTK; lia. }
  1:{ exact PIMG. } 1:{ exact PSHD. }
  ret_pc_lit. hideD.
  lazymatch goal with H : stk bsegs ?mx lo _ |- _ => rename H into SKlo2; rewrite USP in SKlo2 end.
  lazymatch goal with H : stk bsegs ?mx _ (bv_unsigned sp + -80) |- _ =>
    pose proof (stk_merge bsegs _ _ _ _ SKlo2 H ltac:(lia)) as SK2; clear H SKlo2 end.
  zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  eapply mci_tail. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact SK2|].
  split; [eassumption|]. split; [eexists; eassumption|]. split; [eassumption|].
  split. { unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
             A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL.
           repeat (split; [assumption|]). lia. }
  split; eassumption.
Qed.

(* [comment removed for export] *)
Lemma mci_D : forall m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x23 x24 x28 x29 x30 x31,
  MINV m0 ->
  evtA bsegs P POST (ST 0x535cc m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (n + -65)) x23 x24 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. pose proof BNDS as BN. hideD.
  zstepA. (* [comment removed for export] *) rewrite not64 by lia.
  zstepA. (* [comment removed for export] *) if_cases K1; zify_cond K1. { exfalso. lia. }
  zstepA. zstepA. (* [comment removed for export] *)
  if_cases K2; zify_cond K2.
  - (* [comment removed for export] *)
    assert (65 <= n). { destruct (Z.leb_spec 65 n); [assumption|]. exfalso. revert K2. rewrite mod64_neg_small by lia. lia. }
    zstepA. (* [comment removed for export] *) if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
    eapply mci_dbig; [exact IV | lia].
  - assert (n <= 64). { destruct (Z.leb_spec n 64); [assumption|]. exfalso. revert K2. rewrite Z.mod_small by lia. lia. }
    eapply mci_dsmall; [exact IV | lia].
Qed.
End Walk.
End RC__2.
