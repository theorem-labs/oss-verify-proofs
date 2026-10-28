(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_ContStmt LbB_ContV4 LbB_ContVot.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablOS LbB_TablPT1 LbB_TablPT2 LbB_TablPT4 LbB_TablPT5 LbB_TablPT6.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section PT8.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HB : asan_rt_hyps H.

  Lemma pslots_parts : forall (e : ptent H) m, pslotsP e m -> pn e <> 0 ->
       rw_cells asegs m (pS1 e + 16) [C8 (Z_to_bv 64 (sh (p_v e))); C8 (Z_to_bv 64 (sh (p_v e + 16))); C8 (Z_to_bv 64 (p_v e + 16))]
    /\ rw_cells asegs m (pS1 e + 40) [C8 (Z_to_bv 64 (p_v e))]
    /\ rw_cells asegs m (pS1 e + 48) [C8 (Z_to_bv 64 (2 ^ 61)); C8 (Z_to_bv 64 (sh (p_ps e)))].
  Proof.
    intros e m [_ C'] NZ. pose proof (C' NZ) as C. unfold pslots in C.
    apply (rw_cells_app asegs m _ [C8 (Z_to_bv 64 (sh (p_v e))); C8 (Z_to_bv 64 (sh (p_v e + 16))); C8 (Z_to_bv 64 (p_v e + 16))]) in C as [C1 C].
    cbn [cells_size csize Nat.add] in C. change (Z.of_nat 24) with 24 in C. replace (pS1 e + 16 + 24) with (pS1 e + 40) in C by lia.
    apply (rw_cells_app asegs m _ [C8 (Z_to_bv 64 (p_v e))]) in C as [C2 C3].
    cbn [cells_size csize Nat.add] in C3. change (Z.of_nat 8) with 8 in C3. replace (pS1 e + 40 + 8) with (pS1 e + 48) in C3 by lia.
    split; [exact C1|]. split; [exact C2 | exact C3].
  Qed.

  Lemma pgrown_tail : forall e LBi bi capi pidi, ppre H e ->
    LBi = v4_newLB H (p_LB e) (p_b e) (p_pid e) pidi bi (4 * capi) ->
    exists LBt, LBi = (pidi, bi, 4 * capi) :: LBt
      /\ (forall bb, In bb (p_LB e) -> In bb LBt \/ (bb = (p_pid e, p_b e, 4 * p_cap e) /\ 0 < p_cap e /\ p_b e <> 0)).
  Proof.
    intros e LBi bi capi pidi P EQ.
    destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OLD & ND & _).
    unfold v4_newLB in EQ. destruct (Z.eqb_spec (p_b e) 0) as [B0|B0].
    - exists (p_LB e). split; [exact EQ|]. intros bb Hb. left. exact Hb.
    - exists (as_lb_remove H (p_pid e) (p_LB e)). split; [exact EQ|]. intros bb Hb.
      destruct OLD as [(E0 & _)|(C0 & HIn)]; [contradiction|].
      destruct (Z.eq_dec (blk_id bb) (p_pid e)) as [E|NE].
      + right. destruct bb as [[pb Ab] nb]. cbn [blk_id fst] in E. subst pb.
        pose proof (LbB_ContV4.nodup_id_same _ _ _ _ _ _ ND HIn Hb) as EQ2. rewrite <- EQ2. split; [reflexivity|]. split; [exact C0 | exact B0].
      + left. exact (LbB_ContV4.lb_remove_keep H HB _ _ _ ND Hb NE).
  Qed.

  Lemma pXE_old : forall e a, 0 < p_cap e -> p_b e <> 0 ->
    (p_b e <= a < p_b e + 4 * p_cap e \/ sh (p_b e) <= a < sh (p_b e) + nsh (4 * p_cap e)) -> rin_ivs (pXE H e) a.
  Proof.
    intros e a C0 B0 Ha. unfold pXE, v4_oldx. destruct (Z.eqb_spec (p_b e) 0) as [E|_]; [contradiction|].
    cbn [rin_ivs app fst snd]. right. destruct Ha as [Ha|Ha]; [left; exact Ha | right; left; exact Ha].
  Qed.

  Lemma pt_xp_step : forall e LBi bi capi pidi sL mL m1 m2 W,
    ppre H e -> pgrown H e LBi bi capi pidi -> as_RHEAP H sL LBi mL -> 0 < capi ->
    munch W m1 m2 -> wmono asegs m1 m2 ->
    Forall (fun iv : Z * Z => (bi <= fst iv /\ snd iv <= bi + 4 * capi) \/ (sh bi <= fst iv /\ snd iv <= sh bi + nsh (4 * capi))
                              \/ (aceil <= fst iv /\ snd iv <= pSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (pXE H e) a)) W ->
    xpres H (p_LB e) (pSP e) (pXE H e) m1 m2.
  Proof.
    intros e LBi bi capi pidi sL mL m1 m2 W P GR RH C0 MU WM FW.
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OLD & ND & RH0 & _).
    destruct GR as [(E1 & E2 & E3 & E4)|(G1 & G2 & G3)].
    - subst capi bi LBi pidi.
      assert (B0 : p_b e <> 0).
      { destruct OLD as [(X & Y)|(X & Y)]; [lia|].
        pose proof (ah_blocks H HB _ _ _ _ RH0 Y) as (A0 & _). unfold blk_addr in A0. cbn [fst snd] in A0. lia. }
      eapply (xpres_of_munch H (p_s e) (p_LB e) (pSP e) (pXE H e) W (p_m e) m1 m2); [exact HB | exact RH0 | exact MU | exact WM |].
      eapply Forall_impl; [|exact FW]. intros [l h] K. cbn [fst snd] in *.
      destruct K as [K|[K|[K|K]]]; [right | right | left; exact K | right; exact K].
      + intros a Ha. apply pXE_old; [exact C0 | exact B0 | left; lia].
      + intros a Ha. apply pXE_old; [exact C0 | exact B0 | right; lia].
    - destruct (pgrown_tail e LBi bi capi pidi P G2) as (LBt & EL & BL).
      rewrite EL in RH.
      assert (NI : ~ In pidi (map blk_id LBt)).
      { pose proof (ah_nodup H HB _ _ _ RH) as NDi. cbn [map] in NDi. apply NoDup_cons_iff in NDi as [X _]. exact X. }
      pose proof (aceil_facts) as ACF.
      assert (SPc : aceil <= pSP e).
      { pose proof P as (_ & _ & _ & _ & _ & _ & _ & CE & LO & _). unfold PT_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO. lia. }
      pose proof (pt_xp_munch H HB sL LBt pidi bi (4 * capi) (pSP e) (pXE H e) W mL m1 m2 RH NI SPc MU WM FW) as XP.
      eapply (pt_xp_lift H LBt (pSP e) (pXE H e) (p_LB e) (pSP e) (pXE H e) m1 m2 XP ltac:(lia)); [|intros a Ha; exact Ha].
      intros bb Hb. destruct (BL bb Hb) as [IN|(EQ & Cc & Bc)]; [left; exact IN|].
      right. intros a Ha. subst bb. cbn [blk_addr blk_size fst snd] in Ha. apply pXE_old; [exact Cc | exact Bc | exact Ha].
  Qed.

  Lemma pt_vec_push : forall LBi m m' v b xs cap x,
    vec32A LBi m v b xs cap -> Zlen xs < cap -> 0 < b -> (v + 24 <= b \/ b + 4 * cap <= v) -> AIMG_TOP <= v ->
    munch [(b + 4 * Zlen xs, b + 4 * Zlen xs + 4); (v + 8, v + 16)] m m' ->
    rw_cells asegs m' (b + 4 * Zlen xs) [C4 (Z_to_bv 64 x)] -> rw_cells asegs m' (v + 8) [C8 (Z_to_bv 64 (b + 4 * Zlen xs + 4))] ->
    0 <= x < 2 ^ 32 ->
    vec32A LBi m' v b (xs ++ [x]) cap.
  Proof.
    intros LBi m m' v b xs cap x VEC LC B0 DJ VT MU CX CE XR.
    pose proof VEC as (Hv & Hv' & HD & Hlen & Hb & F0 & F8 & F16 & FE).
    destruct Hb as [(E0 & _)|(_ & B16 & Cp & BC & _)]; [lia|].
    assert (AG : forall lo n, 0 <= lo -> 0 <= n -> lo + n <= 2 ^ 63 ->
                 disjoint_from [(b + 4 * Zlen xs, b + 4 * Zlen xs + 4); (v + 8, v + 16)] lo n ->
                 agree_on (zwin lo (lo + n)) m m').
    { intros lo n H1 H2 H3 D a Ha. unfold zwin in Ha. apply MU. rewrite unsigned_lit by lia. cbn in D |- *. lia. }
    eapply (vec32A_push LBi m m' v b xs cap x VEC LC).
    - intros i Hi. destruct (Z_lt_le_dec i 8) as [L|L]; [|destruct (Z_lt_le_dec i 16) as [L'|L']].
      + rewrite (MU (Z_to_bv 64 (v + i))); [apply HD; lia|]. rewrite unsigned_lit by lia. cbn. lia.
      + pose proof (mdef_of_rw_cells_hi _ _ _ CE ltac:(unfold AIMG_TOP in *; lia)) as MD8. cbn [cells_size csize] in MD8.
        replace (v + i) with (v + 8 + (i - 8)) by lia. apply MD8. lia.
      + rewrite (MU (Z_to_bv 64 (v + i))); [apply HD; lia|]. rewrite unsigned_lit by lia. cbn. lia.
    - unfold fldA. eapply fld_agree; [lia | cbn; lia | exact F0 | apply (AG v 8); cbn; lia].
    - replace (b + 4 * (Zlen xs + 1)) with (b + 4 * Zlen xs + 4) by lia. apply fld_of_rw_cells8; [exact CE | lia].
    - unfold fldA. eapply fld_agree; [lia | cbn; lia | exact F16 | apply (AG (v + 16) 8); cbn; lia].
    - intros i Hi. destruct (FE i Hi) as [_ Fi]. unfold fldA. eapply fld_agree; [lia | cbn; lia | exact Fi | apply (AG (b + 4 * i) 4); cbn; lia].
    - apply fld_of_rw_cells4; [exact CX | lia].
    - exact XR.
  Qed.
End PT8.
