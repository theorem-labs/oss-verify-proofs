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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablPT8 LbB_TablPT10.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma pt_fold_perm : forall (A : Type) (f : A -> Z) l l', Permutation l l' ->
  fold_right (fun x acc => f x + acc) 0 l = fold_right (fun x acc => f x + acc) 0 l'.
Proof. intros A f l l' P. induction P; cbn [fold_right]; lia. Qed.
Lemma pt_small_perm : forall L L', Permutation L L' -> lb_small L = lb_small L'.
Proof. intros L L' P. unfold lb_small. exact (pt_fold_perm _ (fun b => nsmall (blk_size b)) _ _ P). Qed.
Lemma pt_large_perm : forall L L', Permutation L L' -> nlarge L = nlarge L'.
Proof. intros L L' P. unfold nlarge. exact (pt_fold_perm _ (fun b => nlg (blk_size b)) _ _ P). Qed.

Lemma vgrow_ge : forall x, 0 <= x -> x + 1 <= vgrow x /\ x <= vgrow x <= 2 * x + 1.
Proof. intros x H. unfold vgrow. lia. Qed.

Section PT11.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HB : asan_rt_hyps H.

  Lemma pt_lb_remove_perm : forall p A n LB, List.NoDup (map blk_id LB) -> In (p, A, n) LB ->
    Permutation LB ((p, A, n) :: as_lb_remove H p LB).
  Proof.
    intros p A n LB ND IN. pose proof (ah_lb_remove H HB) as (L1 & L2 & L3).
    induction LB as [|b LB IH]; [destruct IN|]. cbn [map] in ND. apply NoDup_cons_iff in ND as [ND1 ND2].
    destruct (Z.eq_dec (blk_id b) p) as [E|E].
    - destruct b as [[p' A'] n']. cbn in E. subst p'. rewrite L1 by exact ND1.
      destruct IN as [EQ|IN]; [rewrite EQ; reflexivity|].
      exfalso. apply ND1. apply in_map_iff. exists (p, A, n). split; [reflexivity | exact IN].
    - rewrite L2 by exact E. destruct IN as [EQ|IN]; [subst b; cbn in E; congruence|].
      specialize (IH ND2 IN). eapply perm_trans; [apply perm_skip; exact IH|]. apply perm_swap.
  Qed.

  Lemma pt_newLB_meas : forall e pidi bi n, ppre H e ->
    lb_small (v4_newLB H (p_LB e) (p_b e) (p_pid e) pidi bi n) <= nsmall n + lb_small (p_LB e)
    /\ (length (v4_newLB H (p_LB e) (p_b e) (p_pid e) pidi bi n) <= S (length (p_LB e)))%nat
    /\ nlarge (v4_newLB H (p_LB e) (p_b e) (p_pid e) pidi bi n) <= nlg n + nlarge (p_LB e).
  Proof.
    intros e pidi bi n P.
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OLD & ND & RH0 & _).
    unfold v4_newLB. rewrite lb_small_cons, nlarge_cons. cbn [length blk_size snd].
    destruct (Z.eqb_spec (p_b e) 0) as [B0|B0]; [split; [lia|]; split; [lia | lia]|].
    destruct OLD as [(E0 & _)|(C0 & HIn)]; [contradiction|].
    pose proof (pt_lb_remove_perm _ _ _ _ ND HIn) as PM.
    pose proof (pt_small_perm _ _ PM) as S. pose proof (pt_large_perm _ _ PM) as L. pose proof (Permutation_length PM) as N.
    rewrite lb_small_cons in S. rewrite nlarge_cons in L. cbn [length blk_size snd] in S, L, N.
    pose proof (nsmall_bounds (4 * p_cap e) ltac:(lia)) as B1. pose proof (nlg_bounds (4 * p_cap e)) as B2.
    split; [lia|]. split; [lia | lia].
  Qed.

  Lemma pt_nsmall_max : forall n, 0 <= n -> 0 <= nsmall n <= 64512.
  Proof. intros n Hn. unfold nsmall. destruct (Z.leb_spec n 64512); lia. Qed.

  Lemma pt_budget : forall e LBi bi capi pidi, ppre H e -> pgrown H e LBi bi capi pidi -> 0 <= capi ->
    lb_small LBi + nsmall (4 * vgrow capi) <= RT_SMALL_MAX /\ Z.of_nat (length LBi) + 1 <= RT_CNT_MAX
    /\ nlarge LBi + nlg (4 * vgrow capi) <= RT_LARGE_MAX.
  Proof.
    intros e LBi bi capi pidi P GR C0.
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BS & BC & BL & _).
    pose proof (vgrow_ge capi C0) as VG.
    pose proof (pt_nsmall_max (4 * vgrow capi) ltac:(lia)) as NS. pose proof (nlg_bounds (4 * vgrow capi)) as NL.
    destruct GR as [(E1 & E2 & E3 & E4)|(G1 & G2 & G3)].
    - subst LBi. split; [lia|]. split; [lia | lia].
    - subst LBi.
      destruct (pt_newLB_meas e pidi bi (4 * capi) P) as (T1 & T2 & T3).
      pose proof (pt_nsmall_max (4 * capi) ltac:(lia)) as NS2. pose proof (nlg_bounds (4 * capi)) as NL2.
      split; [lia|]. split; [lia | lia].
  Qed.

  Lemma pt_src_keep : forall e LBi SPc m t, ppre H e ->
    rw_cells asegs m (p_ff e + 32) [C4 (Z_to_bv 64 t)] -> rw_cells asegs m (sh (p_ff e) + 4) [C1 (b8 4)] -> 0 <= t < 2 ^ 32 ->
    src4_keep H LBi SPc m (p_ff e + 32) t.
  Proof.
    intros e LBi SPc m t P CL CK TR m' AC' MI' AP'.
    pose proof (pgeo_of H e P) as G.
    destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SHF0 & SHF1 & SHF2 & SHF3 & _).
    assert (CLx : forall a, p_ff e + 32 <= a < p_ff e + 36 -> aclient_addr H LBi SPc a).
    { intros a Ha. right; right; right; right; left. unfold AFS_SIZE in *. lia. }
    assert (SHx : aclient_addr H LBi SPc (sh (p_ff e) + 4)).
    { right; right; right; right; right; left.
      assert (sh (as_FSB H) <= sh (p_ff e)) by (apply sh_mono; lia).
      assert (sh (p_ff e + 64) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; unfold AFS_SIZE in *; lia). lia. }
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    split.
    - unfold fldA. apply fld_of_rw_cells4 in CL; [|lia]. unfold fldA in CL.
      eapply fld_agree; [lia | cbn; lia | exact CL |].
      intros a Ha. unfold zwin in Ha. cbn in Ha. exact (proj1 (AP' a ltac:(lia) (CLx a ltac:(lia)))).
    - split; [lia|]. split; [unfold AAPP_HI; lia|].
      intros x Hx. exists 4. split; [lia|].
      assert (E : sh x = sh (p_ff e) + 4) by (unfold sh; Z.div_mod_to_equations; lia).
      rewrite E. split.
      + destruct CK as [[_ (_ & _ & B)] _]. specialize (B 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in B.
        unfold mrd in *. unfold wa in *.
        destruct (AP' (sh (p_ff e) + 4) ltac:(unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia) SHx) as [EQ _].
        unfold wa in EQ. rewrite EQ. exact B.
      + unfold byte_ok. right. assert (x mod 8 <= 3) by (Z.div_mod_to_equations; lia). lia.
  Qed.

  Lemma pt_newLB_eq : forall e LBi bi capi pidi pid' b' n', ppre H e -> pgrown H e LBi bi capi pidi ->
    List.NoDup (map blk_id LBi) ->
    v4_newLB H LBi bi pidi pid' b' n' = v4_newLB H (p_LB e) (p_b e) (p_pid e) pid' b' n'.
  Proof.
    intros e LBi bi capi pidi pid' b' n' P GR NDi.
    destruct GR as [(E1 & E2 & E3 & E4)|(G1 & G2 & G3)]; [subst; reflexivity|].
    pose proof G3 as (A0 & _).
    unfold v4_newLB at 1. destruct (Z.eqb_spec bi 0) as [B0|B0]; [lia|].
    rewrite G2. unfold v4_newLB at 1.
    pose proof (ah_lb_remove H HB) as (L1 & _ & _).
    rewrite G2 in NDi. unfold v4_newLB in NDi. cbn [map] in NDi. apply NoDup_cons_iff in NDi as [NI _].
    rewrite L1 by exact NI. unfold v4_newLB. reflexivity.
  Qed.
End PT11.
