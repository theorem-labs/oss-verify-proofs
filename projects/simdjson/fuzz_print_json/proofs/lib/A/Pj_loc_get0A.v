(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImageA RzCPS StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim StrFun.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_kit.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface RT_iface2 IcptSpec D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new
     Sj_num_akit Sj_num_amem Pj_mciA Pj_loc_akitA Pj_defsA Pj_loc_getA Pj_loc_impA.
From OSSVerify.simdjson.fuzz_print_json.images Require Import Asan.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Section AevtPieces.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
Hypothesis MCI : memcmp_inner_icontract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Definition classic_postA (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) j1 j2 j3 j4 j5 j6 (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6a52c0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(0x6a50e8, 0x6a52ca); (0x6a52e0, 0x6a5f98)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ ART RT Σ m'
    /\ (stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x6a50e8 [CB 472 j1]
    /\ rw_cells asegs m' 0x6a52c0 [C8 (Z_to_bv 64 0x6a56e8); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m' 0x6a52e0 (impb_B j2 j3 j4 j5 j6)).

Lemma classic_aevt : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk asegs m lo (bv_unsigned sp) -> (lo + 576 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells asegs m 0x6a50e8 imp0_A ->
  rw_cells asegs m 0x6a52c0 [C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x6a52e0 imp0_B ->
  ro_cells asegs m 0x16aa40 [C8 (Z_to_bv 64 0x6c68e8)] -> ro_cells asegs m 0x6c68e8 [C8 canary] ->
  ro_cells asegs m 0x6c6b3b [C1 (Z_to_bv 8 0)] -> rw_cells asegs m 0x6c6c18 [C4 (Z_to_bv 64 0)] -> mem_inv asegs m -> ART RT Σ m ->
  (forall ms', classic_postA Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12ba14) fc None m (seg_rom asegs)).
Proof using AF RTC MCI FDO MST.
  intros until canary. intros ST LO LOR SPT SPA HI RA CLS RB GOT CAN NL LK MI ART0 HK.
  unfold imp0_A in RA. unfold imp0_B in RB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 576, bv_unsigned sp); (0x6a50e8, 0x6a52ca); (0x6a52e0, 0x6a5f98)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  astart (bv_unsigned sp) [(0x6a50e8, 0x6a52ca); (0x6a52e0, 0x6a5f98)]%Z.
  apply (aevt_evt RT AF PMc MST).
  carve_frame 32%nat ST.
  do 10 lstep.
  if_true.
  do 6 lstep.
  if_true.
  do 3 lstep.
  if_false.
  do 2 lstep.
  if_false.
  do 7 lstep.
  if_false.
  do 3 lstep.
  lstep.
  acall_sp (imp_ctor_aevt RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact RA | exact RB | exact GOT | exact CAN | exact NL | exact LK | assumption | exact ARTX | apost_call].
  rename PC into ST. rename PC0 into RA. rename POST into RB.
  do 16 lstep.
  release_frame FR ST (bv_unsigned sp).
  afinish.
Qed.

Definition locale_ctor_postA (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (lo D : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(D, D + 8); (0x6a50e8, 0x6a5f98)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ART RT Σ m'
    /\ (stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' D [C8 (Z_to_bv 64 0x6a56e8)] /\ LOCBA m').

Lemma locale_ctor0_aevt : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo D : Z) (j : list byte) (canary : word),
  stk asegs m lo (bv_unsigned sp) -> (lo + 608 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  LOC0A m -> rw_cells asegs m D [CB 8 j] -> (0 <= D)%Z -> (D + 8 <= lo \/ bv_unsigned sp <= D)%Z -> (D + 8 <= 0x6a50e8 \/ 0x6c6c1c <= D)%Z ->
  (forall i, 0 <= i < 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (D + i))%Z ->
  ro_cells asegs m 0x16aa40 [C8 (Z_to_bv 64 0x6c68e8)] -> ro_cells asegs m 0x6c68e8 [C8 canary] ->
  ro_cells asegs m 0x6c6b3b [C1 (Z_to_bv 8 0)] -> rw_cells asegs m 0x6c6c18 [C4 (Z_to_bv 64 0)] -> mem_inv asegs m -> ART RT Σ m ->
  (forall ms', locale_ctor_postA Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo D m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x131828) fc None m (seg_rom asegs)).
Proof using AF RTC MCI FDO MST.
  intros until canary. intros ST LO LOR SPT SPA HI L0 DST D0 DLO DBL DCL GOT CAN NL LK MI ART0 HK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.

  pose proof (munch_refl [(bv_unsigned sp - 608, bv_unsigned sp); (0x6a50e8, 0x6a5f98)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  astart (bv_unsigned sp) [(0x6a50e8, 0x6a5f98)]%Z.
  a_hide DST.
  assert (DHI : (D + 8 <= USTACK_TOP)%Z) by (pose proof (aclient_bounds RT AF Σ m (bv_unsigned sp) (D + 7)%Z ART0 ltac:(lia) (DCL 7%Z ltac:(lia))); lia).
  apply (aevt_evt RT AF PMc MST).
  unfold LOC0A, loc0_cellsA, PJ_LOC_LO_A in L0.
  retype L0 [CB 472 (repeat (Z_to_bv 8 0) 472);
             C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6);
             C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6);
             CB 3256 (repeat (Z_to_bv 8 0) 3256)].
  take L0 1%nat 0x6a52c0%Z RA. take L0 3%nat 0x6a52ca%Z CLS. take L0 1%nat 0x6a52d0%Z P1.
  take L0 3%nat 0x6a52da%Z GLB. take L0 1%nat 0x6a52e0%Z P2. rename L0 into RB.
  carve_frame 32%nat ST.
  do 11 lstep.
  if_true.
  do 6 lstep.
  if_true.
  do 3 lstep.
  if_false.
  do 2 lstep.
  if_false.
  do 7 lstep.
  if_false.
  lstep.
  acall_sp (classic_aevt Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact RA | exact CLS | exact RB | exact GOT | exact CAN | exact NL | exact LK | assumption | exact ARTX | apost_call].
  rename PC into ST. rename PC0 into RA. rename PC1 into CLS. rename POST into RB. unfold impb_B in RB.
  a_revive DST.
  lazymatch goal with MU' : munch _ ?m2 _ |- _ => clear MU; pose proof (munch_refl [(bv_unsigned sp - 608, bv_unsigned sp); (D, D + 8); (0x6a50e8, 0x6a5f98)]%Z m2) as MU end.
  do 4 lstep.
  if_true.
  do 12 lstep.
  if_true.
  do 6 lstep.
  release_frame FR ST (bv_unsigned sp).

  glue RA CLS. glue RA P1. glue RA GLB. glue RA P2. glue RA RB.
  merge_at RA 0%nat 5%nat. merge_at RA 3%nat 3%nat.
  a_widen [(D, D + 8); (0x6a50e8, 0x6a5f98)]%Z.
  afinish.
  unfold LOCBA, locb_cellsA, PJ_LOC_LO_A, PJ_LOC_IMP_A, PJ_CTYPE_VPTR_A. do 6 eexists. eassumption.
Qed.

Theorem locale_ctor_aevt : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo D : Z) (j : list byte) (canary : word),
  stk asegs m lo (bv_unsigned sp) -> (lo + 608 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  pj_locA m -> rw_cells asegs m D [CB 8 j] -> (0 <= D)%Z -> (D + 8 <= lo \/ bv_unsigned sp <= D)%Z -> (D + 8 <= 0x6a50e8 \/ 0x6c6c1c <= D)%Z ->
  (forall i, 0 <= i < 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (D + i))%Z ->
  ro_cells asegs m 0x16aa40 [C8 (Z_to_bv 64 0x6c68e8)] -> ro_cells asegs m 0x6c68e8 [C8 canary] ->
  ro_cells asegs m 0x6c6b3b [C1 (Z_to_bv 8 0)] -> rw_cells asegs m 0x6c6c18 [C4 (Z_to_bv 64 0)] -> mem_inv asegs m -> ART RT Σ m ->
  (forall ms', locale_ctor_postA Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo D m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x131828) fc None m (seg_rom asegs)).
Proof using AF RTC MCI FDO MST.
  intros until canary. intros ST LO LOR SPT SPA HI [L0|LB] DST D0 DLO DBL DCL GOT CAN NL LK MI ART0 HK.
  - eapply locale_ctor0_aevt; eassumption.
  - pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (D, D + 8)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    astart (bv_unsigned sp) [(D, D + 8); (0x6a50e8, 0x6a5f98)]%Z.
    pose proof (aclient_bounds RT AF Σ m (bv_unsigned sp) (D + 7)%Z ART0 ltac:(lia) (DCL 7%Z ltac:(lia))) as DHI.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_mono; [ eapply locale_ctor_specB; [exact ST | a_ul | exact LOLO | exact LB | exact DST | lia | a_ul | exact DLO | exact DBL | exact MI] | ].
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU' & WM' & MI' & ST' & D' & LB'). subst ms'.
    clear MU WMS. pose proof MU' as MU. pose proof WM' as WMS.
    cbv beta. apply HK. unfold locale_ctor_postA.
    assert (ARTC : ART RT Σ m').
    { eapply (art_after_munch RT AF Σ (bv_unsigned sp - 32)%Z _ m m' ART0); [a_ul | exact MU | exact WMS | a_in_client]. }
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F, m'.
    split; [reflexivity|]. split; [| split; [exact WM'| split; [exact MI'| split; [exact ARTC| split; [exact ST'| split; [exact D'| exact LB']]]]]].
    apply (pres_fp_fold_munch RT AF Σ m m m m' (bv_unsigned sp) lo _ _ ART0 LOR (pres_fp_refl' RT Σ _ _ m) MU). a_outside_sub.
Qed.

End AevtPieces.
