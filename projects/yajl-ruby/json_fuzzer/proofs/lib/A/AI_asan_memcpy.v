(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AI_shadow AM_memcpy AI_region_is_poisoned.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Export AI_asan_memcpy1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Walk.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (D S n SB : Z) (src wsS wsD : list byte) (lo : Z).
Hypothesis LOC : (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 2224.
Hypothesis HN : 1 <= n < 2^40.
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis RIMS : range_in_mem SB S n.
Hypothesis RIMD : range_in_mem SB D n.
Hypothesis HSN : S + n < 2^47.
Hypothesis HDN : D + n < 2^47.
Hypothesis SEP : S + n <= D \/ D + n <= S.
Hypothesis HDISJS : S + n <= lo \/ bv_unsigned sp <= S.
Hypothesis HDISJD : D + n <= lo \/ bv_unsigned sp <= D.
Hypothesis HGL : D + n <= 0xa4000 \/ 0xaee00 <= D.
Hypothesis SHLS : Z.of_nat (length wsS) = shw_hi SB S n - shw_lo SB S.
Hypothesis SHLD : Z.of_nat (length wsD) = shw_hi SB D n - shw_lo SB D.
Hypothesis RCS : range_clean SB S n wsS.
Hypothesis RCD : range_clean SB D n wsD.
Hypothesis HSWS : shw_hi SB S n <= D \/ D + n <= shw_lo SB S.
Hypothesis HSWD : shw_hi SB D n <= D \/ D + n <= shw_lo SB D.
Hypothesis SBR : 2^24 <= SB < 2^32.
(* [comment removed for export] *)
Hypothesis PSHD : forall a k, shw_lo SB D <= a -> a + Z.of_nat k <= shw_hi SB D n -> P (Z_to_bv 64 a, k).
Hypothesis PSHS : forall a k, shw_lo SB S <= a -> a + Z.of_nat k <= shw_hi SB S n -> P (Z_to_bv 64 a, k).
Hypothesis PDST : forall a k, D <= a -> a + Z.of_nat k <= D + n -> P (Z_to_bv 64 a, k).
Hypothesis PSRC : forall a k, S <= a -> a + Z.of_nat k <= S + n -> P (Z_to_bv 64 a, k).
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PSTK : forall a k, bv_unsigned sp - 2224 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Ltac hideD := hideH SEP; hideH HDISJS; hideH HDISJD; hideH HGL; hideH HSWS; hideH HSWD; hideH RIMS; hideH RIMD.
Ltac unhideD := unfold hidden in SEP, HDISJS, HDISJD, HGL, HSWS, HSWD, RIMS, RIMD.
(* [comment removed for export] *)
Lemma BNDS : 0 < S /\ S + n < 2^47 /\ 0 < D /\ D + n < 2^47.
Proof. unfold range_in_mem in RIMS, RIMD. lia. Qed.

Notation POST := (asan_memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n SB src wsS wsD m lo).
Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -2144)).
Notation gS1 := (Z.shiftr S 3).
Notation gS2 := (Z.shiftr (S + n + -1) 3).
Notation ST pc mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31 :=
  (MS (mkR x1 SP' gp tp x5 x6 x7 sp x9 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) x13 x14 x15 x16 x17 x18 x19 SP' x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
Notation MINV := (AI_asan_memcpy1.MINV ra sp s0 s1 s2 s3 s4 s5 s6 s7 m D S n SB src wsS wsD lo).

Ltac open_minv H := destruct H as (MI & MU & WM & SK & FR & [junk DST] & SRC & G & SHS & SHD).

Lemma GEOS :
  0 <= gS1 /\ gS1 <= gS2 /\ 8 * gS1 <= S < 8 * gS1 + 8 /\ 8 * gS2 <= S + n + -1 < 8 * gS2 + 8 /\
  shw_lo SB S <= SB + gS1 /\ SB + gS1 < shw_lo SB S + 8 /\ shw_lo SB S mod 8 = 0 /\
  shw_hi SB S n - 8 <= SB + gS2 /\ SB + gS2 < shw_hi SB S n /\ shw_hi SB S n mod 8 = 0 /\
  shw_lo SB S + 8 <= shw_hi SB S n.
Proof. unfold range_in_mem in RIMS. exact (shw_geom SB S n ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

(* [comment removed for export] *)
Lemma amc_sloop : forall k (Q : machine_state -> Prop) m0 j x1 x5 x6 x7 x9 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31,
  Z.to_nat (gS2 - j) = k -> gS1 <= j < gS2 ->
  bytes_at asegs m0 (shw_lo SB S) wsS ->
  evtA asegs P Q (ST 0x530cc m0 x1 x5 x6 x7 x9 (Z_to_bv 64 (SB + gS2)) (Z_to_bv 64 (SB + gS2)) (Z_to_bv 64 0) (Z_to_bv 64 0) x17 x18 x19 x21 x22 x23 x28 x29 x30 x31) ->
  evtA asegs P Q (ST 0x530bc m0 x1 x5 x6 x7 x9 (Z_to_bv 64 (SB + j)) (Z_to_bv 64 (SB + gS2)) (Z_to_bv 64 0) x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31).
Proof.
  induction k as [|k IH]; intros until x31; intros Hk Hj SHB CONT; pose proof GEOS as GE; [lia|]. pose proof BNDS as BN. hideD.
  pose proof (range_clean_inner SB S n wsS j RCS ltac:(lia)) as Hb.
  pose proof (u8ro_read asegs m0 (shw_lo SB S) wsS (SB + j - shw_lo SB S) _ (Z_to_bv 64 (SB + j)) SHB Hb ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. (* [comment removed for export] *) clear RD.
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K; zify_cond K.
  - replace (SB + j + 1) with (SB + (j + 1)) by lia. eapply (IH Q m0 (j + 1)); try lia; try assumption.
  - replace (SB + j + 1) with (SB + gS2) by lia. exact CONT.
Qed.

(* [comment removed for export] *)
Lemma amc_sjoin : forall m0 j8 x1 x5 x6 x7 x9 x16 x17 x18 x23 x28 x29 x30 x31,
  MINV m0 j8 ->
  evtA asegs P POST (ST 0x530cc m0 x1 x5 x6 x7 x9 (Z_to_bv 64 (SB + gS2)) (Z_to_bv 64 (SB + gS2)) (Z_to_bv 64 0) x16 x17 x18
                        (Z_to_bv 64 (D + n)) (Z_to_bv 64 (S + n + -1)) (Z_to_bv 64 (n + -65)) x23 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. hideD.
  zstepA. zstepA. (* [comment removed for export] *)
  eapply (AI_asan_memcpy1.amc_D P); try eassumption.
Qed.

(* [comment removed for export] *)
Lemma amc_sslow : forall m0 j8 x1 x5 x6 x7 x9 x15 x16 x17 x18 x23 x28 x29 x30 x31,
  MINV m0 j8 ->
  evtA asegs P POST (ST 0x530a0 m0 x1 x5 x6 x7 x9 (Z_to_bv 64 (SB + gS1)) (Z_to_bv 64 (SB + gS2)) x15 x16 x17 x18
                        (Z_to_bv 64 (D + n)) (Z_to_bv 64 (S + n + -1)) (Z_to_bv 64 (n + -65)) x23 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. pose proof IV as IV'. open_minv IV.
  pose proof GEOS as GE. pose proof BNDS as BN. hideD.
  destruct (RCS gS2 ltac:(lia)) as (k2 & Hk2 & K2).
  pose proof (u8ro_read asegs m0 (shw_lo SB S) wsS (SB + gS2 - shw_lo SB S) _ (Z_to_bv 64 (SB + gS2)) SHS Hk2 ltac:(lia)
                ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. (* [comment removed for export] *) clear RD.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  lazymatch goal with |- context [Z_to_bv 64 (Z.land (Z.b2z ?t) ?u)] =>
    change (Z.land (Z.b2z t) u) with (aip_expr (bv_unsigned (sxb k2)) (Z.land (S + n + -1) 7)) end.
  rewrite (aip_last_clean k2 (S + n + -1)) by (first [lia | destruct K2 as [K2|[_ K2]]; [left; exact K2| right; lia]]).
  zstepA. (* [comment removed for export] *)
  clear MI MU WM SK FR DST SRC G SHD.
  if_cases KG; zify_cond KG.
  - replace (SB + gS1) with (SB + gS2) by lia. eapply amc_sjoin; exact IV'.
  - eapply (amc_sloop (Z.to_nat (gS2 - gS1)) _ m0 gS1); [reflexivity | lia | exact SHS |].
    eapply amc_sjoin; exact IV'.
Qed.

(* [comment removed for export] *)
Lemma amc_ssmall : forall m0 j8 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x23 x28 x29 x30 x31,
  MINV m0 j8 -> n <= 64 ->
  evtA asegs P POST (ST 0x52db8 m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18
                        (Z_to_bv 64 (D + n)) (Z_to_bv 64 (S + n)) (Z_to_bv 64 (n + -65)) x23 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV Hn64. pose proof IV as IV'. open_minv IV.
  pose proof GEOS as GE. pose proof BNDS as BN. hideD.
  icp_globals_open G.
  stepA. stepA. (* [comment removed for export] *) stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  rewrite ?land_m8, ?land_m8' by lia.
  change (al8 (SB + S ≫ 3)) with (shw_lo SB S).
  replace (al8 (SB + (S + n + -1) ≫ 3)) with (shw_hi SB S n - 8) by (unfold shw_hi; lia).
  pose proof (bytes_at_read asegs _ _ _ 0 8 SHS ltac:(lia) ltac:(lia)) as RD1. rewrite Z.add_0_r in RD1.
  stepA. clear RD1.
  pose proof (bytes_at_read asegs _ _ _ (shw_hi SB S n - 8 - shw_lo SB S) 8 SHS ltac:(lia) ltac:(lia)) as RD2.
  replace (shw_lo SB S + (shw_hi SB S n - 8 - shw_lo SB S)) with (shw_hi SB S n - 8) in RD2 by lia.
  stepA. clear RD2.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  clear MI MU WM SK FR DST SRC SHS SHD GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI.
  if_cases KW.
  - eapply amc_sslow; exact IV'.
  - eapply (AI_asan_memcpy1.amc_D P); try eassumption.
Qed.

(* [comment removed for export] *)
Lemma amc_sbig : forall m0 j8 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x28 x29 x30 x31,
  MINV m0 j8 -> 65 <= n ->
  evtA asegs P POST (ST 0x530d4 m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18
                        (Z_to_bv 64 (D + n)) x21 (Z_to_bv 64 (n + -65)) x23 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV Hn65. open_minv IV.
  pose proof GEOS as GE. pose proof (shw_geom SB D n ltac:(lia) ltac:(unfold range_in_mem in RIMD; lia) ltac:(lia)) as GED; cbv zeta in GED. pose proof BNDS as BN.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR. hideD.
  zstepA. zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2144)) = bv_unsigned sp + -2144) by (apply unsigned_lit; lia).
  destruct (stk_split asegs m0 lo (bv_unsigned sp + -2144) (bv_unsigned sp + -80) SK ltac:(lia)) as [SKlo SKhi]. clear SK.
  pose proof G as Gc. icp_globals_open Gc.
  unhideH HDISJS. unhideH HDISJD.
  callA (region_is_poisoned_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S n SB wsS lo P).
  1:{ rewrite USP. exact SKlo. }
  1:{ unfold alloc_ceiling, sp_window_lo, stack_max_size. lia. }
  1:{ rewrite USP. lia. }
  1:{ exact MI. }
  1:{ reflexivity. } 1:{ reflexivity. }
  1:{ lia. } 1:{ lia. } 1:{ exact RIMS. } 1:{ exact G. }
  1:{ split; [exact SHS | exact SHLS]. } 1:{ exact RCS. }
  1:{ intros a k H1 H2. rewrite USP in H1, H2. apply PSTK; lia. }
  1:{ exact PIMG. } 1:{ exact PSHS. }
  ret_pc_lit. hideD.
  lazymatch goal with H : stk asegs ?mx lo _ |- _ => rename H into SKlo2; rewrite USP in SKlo2 end.
  lazymatch goal with H : stk asegs ?mx _ (bv_unsigned sp + -80) |- _ =>
    pose proof (stk_merge asegs _ _ _ _ SKlo2 H ltac:(lia)) as SK2; clear H SKlo2 end.
  zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  eapply (AI_asan_memcpy1.amc_D P); try eassumption. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact SK2|].
  split; [eassumption|]. split; [eexists; eassumption|]. split; [eassumption|].
  split. { unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
             A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL.
           repeat (split; [assumption|]). lia. }
  split; eassumption.
Qed.

(* [comment removed for export] *)
Lemma amc_S : forall m0 j8 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x22 x23 x28 x29 x30 x31,
  MINV m0 j8 ->
  evtA asegs P POST (ST 0x52da4 m0 x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (D + n)) (Z_to_bv 64 (S + n)) x22 x23 x28 x29 x30 x31).
Proof.
  intros until x31. intros IV. pose proof BNDS as BN. hideD.
  zstepA. (* [comment removed for export] *) rewrite not64 by lia.
  zstepA. (* [comment removed for export] *) if_cases K1; zify_cond K1. { exfalso. lia. }
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K2; zify_cond K2.
  - assert (65 <= n). { destruct (Z.leb_spec 65 n); [assumption|]. exfalso. revert K2. rewrite mod64_neg_small by lia. lia. }
    zstepA. (* [comment removed for export] *) if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
    eapply amc_sbig; [exact IV | lia].
  - assert (n <= 64). { destruct (Z.leb_spec n 64); [assumption|]. exfalso. revert K2. rewrite Z.mod_small by lia. lia. }
    eapply amc_ssmall; [exact IV | lia].
Qed.

Lemma asan_memcpy_body : forall (t0' : word) x10 x11 x12 a3 a4 a5 a6 a7 (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
  x10 = Z_to_bv 64 D -> x11 = Z_to_bv 64 S -> x12 = Z_to_bv 64 n -> t0' = t0 ->
  rw_cells asegs m D [CB (Z.to_nat n) junk] -> bytes_at asegs m S src ->
  icp_globals asegs m SB -> bytes_at asegs m (shw_lo SB S) wsS -> bytes_at asegs m (shw_lo SB D) wsD ->
  evtA asegs P POST
    (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 x10 x11 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 asan_memcpy_entry) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros SK MI -> -> -> -> DST SRC G SHS SHD. unfold asan_memcpy_entry.
  pose proof GEOS as GE. pose proof (shw_geom SB D n ltac:(lia) ltac:(unfold range_in_mem in RIMD; lia) ltac:(lia)) as GE2; cbv zeta in GE2. pose proof BNDS as BN.
  assert (MU : munch [(bv_unsigned sp - 2224, bv_unsigned sp); (D, D + n)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  (* [comment removed for export] *)
  pose proof (conj DST (conj SRC (conj SHS SHD))) as RO. clear DST SRC SHS SHD.
  assert (MU0 : munch [(bv_unsigned sp - 2224, bv_unsigned sp)] m m) by apply munch_refl.
  hideD. carve_frame 80%nat SK.
  do 12 stepA.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  unfold hidden in RIMS, RIMD, HDISJS, HDISJD.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply (icp_globals_transport asegs) in G; [ | exact MU0 | exact WM | cbn; lia ];
    destruct RO as (DST & SRC & SHS & SHD);
    eapply (rw_cells_transport asegs) in DST; [ | exact MU0 | exact WM | cbn; lia ]; clear MU0
  end.
  unhideD.
  eapply (bytes_at_transport asegs) in SRC; [ | exact MU | cbn; lia ].
  eapply (bytes_at_transport asegs) in SHS; [ | exact MU | cbn; lia ].
  eapply (bytes_at_transport asegs) in SHD; [ | exact MU | cbn; lia ].
  hideD. pose proof G as G'. icp_globals_open G.
  stepA. stepA. stepA. (* [comment removed for export] *)
  cbv beta. stepA. if_false.  (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  clear GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI.
  eassert (IV : MINV m0 _).
  { split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact SK|]. split; [exact FR|].
    split; [eexists; exact DST|]. split; [exact SRC|]. split; [exact G'|]. split; [exact SHS| exact SHD]. }
  zstepA. (* [comment removed for export] *) if_cases KE; zify_cond KE.
  { (* [comment removed for export] *) eapply amc_S; exact IV. }
  zstepA. (* [comment removed for export] *) if_cases KO1; zify_cond KO1.
  { eapply amc_S; exact IV. }
  zstepA. (* [comment removed for export] *) if_cases KO2; zify_cond KO2. { exfalso. unhideD. lia. }
  eapply amc_S; exact IV.
Qed.
End Walk.

Lemma asan_memcpy_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D S n SB : Z) (src wsS wsD junk : list byte) (lo : Z) (P : acc -> Prop),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 2224 -> mem_inv asegs m ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
  1 <= n < 2^40 -> range_in_mem SB S n -> range_in_mem SB D n -> S + n < 2^47 -> D + n < 2^47 ->
  (S + n <= D \/ D + n <= S) ->
  (S + n <= lo \/ bv_unsigned sp <= S) -> (D + n <= lo \/ bv_unsigned sp <= D) -> (D + n <= 0xa4000 \/ 0xaee00 <= D) ->
  rw_cells asegs m D [CB (Z.to_nat n) junk] -> bytes_at asegs m S src -> length src = Z.to_nat n ->
  icp_globals asegs m SB ->
  shadow_window asegs m SB S n wsS -> range_clean SB S n wsS -> (shw_hi SB S n <= D \/ D + n <= shw_lo SB S) ->
  shadow_window asegs m SB D n wsD -> range_clean SB D n wsD -> (shw_hi SB D n <= D \/ D + n <= shw_lo SB D) ->
  (forall a k, bv_unsigned sp - 2224 <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, S <= a -> a + Z.of_nat k <= S + n -> P (Z_to_bv 64 a, k)) ->
  (forall a k, D <= a -> a + Z.of_nat k <= D + n -> P (Z_to_bv 64 a, k)) ->
  (forall a k, shw_lo SB S <= a -> a + Z.of_nat k <= shw_hi SB S n -> P (Z_to_bv 64 a, k)) ->
  (forall a k, shw_lo SB D <= a -> a + Z.of_nat k <= shw_hi SB D n -> P (Z_to_bv 64 a, k)) ->
  evtA asegs P (asan_memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n SB src wsS wsD m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 asan_memcpy_entry) fc None m (seg_rom asegs)).
Proof.
  intros until P. intros SK LOC LO MI HA0 HA1 HA2 HN RIMS RIMD HSN HDN SEP HJS HJD HGL DST SRC LEN G SWS RCS HWS SWD RCD HWD
         PSTK PIMG PSRC PDST PSHS PSHD.
  unfold alloc_ceiling, sp_window_lo, stack_max_size in LOC.
  assert (SBR : 2^24 <= SB < 2^32) by (unfold icp_globals in G; tauto).
  destruct SWS as [SHS SHLS]. destruct SWD as [SHD SHLD].
  eapply asan_memcpy_body; try eassumption; try reflexivity.
Qed.
End RC__1.
