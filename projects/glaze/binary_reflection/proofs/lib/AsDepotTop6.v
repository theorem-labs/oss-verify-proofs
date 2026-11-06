(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDepotGrantEx.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS1.

Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section GrantEx.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  Hypothesis BOK : boot_ok bt.
  Hypothesis BTOT : boot_totals bt.

  Theorem grant_ex_pf : forall st Lc FF M0 mdl mdlm nZ, WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
    a_kact st <= KCAP -> 0 < nZ <= 2 ^ 23 -> nZ mod 4096 = 0 -> eager_used mdl + nZ + A_bytes (a_aa st) <= vm_limit (m_vmmaps mdl) ->
    exists a : word, grant_ok (Z_to_bv 64 0) mdlm a nZ = true.
  Proof using BTOT BOK.
    intros st Lc FF M0 mdl mdlm nZ W RP SBM MI KC HN _ BUD.
    destruct (sbm_vmmaps _ _ SBM) as [EV EL].
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (AW & _) & _).
    pose proof (AsKSys6.AsanNodesMmLib.mat_pages_le_A_bytes (a_aa st) mdlm MI AW) as MP.
    pose proof (eager_used_ext mdlm mdl EV EL) as EE.
    apply (grant_exists bt st Lc FF (2 ^ 20) (2 ^ 28) M0 mdl W ltac:(lia) (qroom_WF bt st Lc FF W) RP KC BOK BTOT (Z_to_bv 64 0) mdlm nZ EV).
    - (lazymatch goal with |- ?G => let G' := eval unfold NZEX in G in change_no_check G' end). lia.
    - rewrite vm_backing_used_split, EE, EV. lia.
  Qed.
  (* [comment removed for export] *)
  Theorem grant_nr_ex_pf : forall st Lc FF M0 mdl mdlm (nn : option Z), WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> a_kact st <= KCAP ->
    vm_reserved (m_vmmaps mdlm) = vm_reserved (m_vmmaps mdl) -> vm_maps (m_vmmaps mdlm) = nnpart nn ++ vm_maps (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdlm) = vm_init_sp (m_vmmaps mdl) ->
    exists a : word, AsanAcctShape.NoReserve.grant_ok_nr (Z_to_bv 64 0) mdlm a (2 ^ 23) = true.
  Proof using BTOT BOK.
    intros st Lc FF M0 mdl mdlm nn W RP KC ER EM ES.
    apply (grant_nr_exists_x bt st Lc FF (2 ^ 20) (2 ^ 28) M0 mdl W ltac:(lia) (qroom_WF bt st Lc FF W) RP KC BOK BTOT (nnpart nn) (Z_to_bv 64 0) mdlm (2 ^ 23) ER).
    - rewrite EM. intros x Hx. exact Hx.
    - (lazymatch goal with |- ?G => let G' := eval unfold alloc_top in G in change_no_check G' end). rewrite ES. reflexivity.
    - (lazymatch goal with |- ?G => let G' := eval unfold XCNT, nnpart in G in change_no_check G' end). destruct nn; (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt List.map length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end); lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold XSZ, nnpart in G in change_no_check G' end). destruct nn; (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt List.map BackingAlgebra.AsanPlacement.gw_sizes snd] in G in change_no_check G' end); [rewrite Spec4.AgentLib.u64_lit by lia; lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold NZEX in G in change_no_check G' end). lia.
  Qed.
End GrantEx.
End AsDepotGrantEx.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop5. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvDepotObl3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop3.AsDepotTop1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopN1b.AsDepotTopN1a OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTopS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotTop5 AsDepotGrantEx.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section TOP6.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.

  Theorem hyp_depot_closed : boot_facts bt -> boot_totals bt -> bt_segs bt = ASEGS -> bt_ia bt = asan_addrs -> depot_cells bt -> depot_cells2 bt ->
    forall KD, 576 <= KD -> AsAllocFHyp.HYP_DEPOT_stmt bt FXOK KD.
  Proof using.
    intros BF BTOT BT_segs BT_ia DC DC2 KD HKD.
    pose proof (boot_facts_ok bt BF) as BOK. pose proof (boot_facts_geom bt BF) as BG.
    destruct (dep0_bounds bt BOK) as [DEP0 [_ DFR0]].
    apply (hyp_depot_pf bt FXOK BT_segs BT_ia DC DC2 (depot_obls_pf bt)).
    - intros st Lc FF W ROOM KC. exact (depot_frames_room bt st Lc FF W ROOM KC DFR0).
    - exact DEP0.
    - exact BG.
    - exact (grant_ex_pf bt BOK BTOT).
    - exact (grant_nr_ex_pf bt BOK BTOT).
    - exact HKD.
  Qed.
End TOP6.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac wd_in_nat i := lazymatch i with O => idtac | S ?j => wd_in_nat j end.
Ltac wd_in_fast :=
  let G := match goal with |- ?G => eval cbv beta in G end in
  lazymatch G with In (?a, ?n, ?v) ?L =>
    let i := eval lazy in ((fix f (l : list (Z * nat * Z)) : nat := match l with [] => O | (a', n', _) :: l' =>
                              if (Z.eqb a a' && Nat.eqb n n')%bool then O else S (f l') end) L) in
    wd_in_nat i; exact (nth_error_In L i eq_refl)
  end.

Lemma depot_cells_asan : forall bt a1 a2 a3 a4, bt_consts bt = asan_consts a1 a2 a3 a4 -> depot_cells bt /\ depot_cells2 bt.
Proof.
  intros bt a1 a2 a3 a4 E. (lazymatch goal with |- ?G => let G' := eval unfold depot_cells, depot_cells2 in G in change_no_check G' end). rewrite E.
  repeat split; first [ wd_in_fast | (lazymatch goal with |- ?G => let G' := eval unfold asan_consts in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]) ].
Qed.
