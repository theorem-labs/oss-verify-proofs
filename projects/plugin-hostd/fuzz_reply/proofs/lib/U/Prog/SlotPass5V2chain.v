From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack AllocBound AllocPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement StatementKept
  send_line_c gesture_end_c relay_event_c RelayFrame RelayRunT RelayRunF ListTr RelayModel RelayKeys send_line_b_c
  gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep HarnessRep ListRep CheckRep drain_b_c
  relay_remove_b_c SlotInv SlotReads printf_facts_c snprintf_c relay_instance_gone_b_c RelayCap
  check_shape_done_c check_no_loss_c check_shape_ends_c SlotPass2Check SlotPass4C SlotPass5Run relay_remove_b_aux
  SlotPass5Check relay_instance_gone_b_lem SlotCaps3 SlotSteps SlotRes SlotRI3 SlotRun3 SlotP5R3G SlotP5Res3
  TrModel SlotPass5M.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotPass5V.
Import ListNotations.
Local Open Scope Z_scope.

Lemma chain_in_ent : forall G OUT es hj e x,
  In e es -> In x (entry_nc e) -> In x (rv_nc (view_of G OUT es hj)).
Proof.
  intros G OUT es hj e x He Hx. unfold view_of. cbn [rv_nc]. right. right.
  apply in_or_app. left. apply in_concat. exists (entry_nc e). split; [apply in_map; exact He|exact Hx].
Qed.

Lemma chain_in_src : forall G OUT es hj p x,
  In p hj -> In x (src_nc (fst p)) -> In x (rv_nc (view_of G OUT es hj)).
Proof.
  intros G OUT es hj p x Hp Hx. unfold view_of. cbn [rv_nc]. right. right.
  apply in_or_app. right. apply in_concat. exists (src_nc (fst p)).
  split; [apply (in_map (fun p0 => src_nc (fst p0))); exact Hp|exact Hx].
Qed.

Lemma chain_p5c_in : forall es hj hs' i,
  (i < length es)%nat -> re_eof (nth i es no_entry) = 0 -> length hs' = length es ->
  In (nth i hs' (fst (nth i hj no_hj)), snd (nth i hj no_hj)) (p5c_hj es hj hs').
Proof.
  intros es hj hs' i Hi He Hl. unfold p5c_hj. apply in_map_iff. exists i.
  split; [|apply in_seq; lia].
  cbv beta. unfold g5_src.
  destruct (Z.eqb_spec (re_eof (nth i es no_entry)) 0) as [_|N]; [|contradiction].
  f_equal. apply nth_indep. lia.
Qed.

Theorem p5v_chain_pf : p5v_chain_S.
Proof.
  unfold p5v_chain_S.
  intros rc Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP'
    es' hs' kss qs H.
  cbv zeta. intros i Hi He.
  unfold p5v_ctx in H. cbv zeta in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLK & _ & HLE' & HOK' &
    _ & HLH' & HST & _).
  destruct (HLK i Hi) as (HEL & HSL). specialize (HSL He).
  unfold entry_links, live_at in HEL. unfold src_links, expected_links, live_at in HSL.
  destruct (HST i Hi) as (_ & _ & _ & _ & _ & _ & HCAP & _ & _ & HKA & HSRC & _).
  destruct (HSRC He) as (HSA & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEC & _).
  assert (HIE : In (nth i es' no_entry) es') by (apply nth_In; rewrite HLE'; exact Hi).
  assert (EOK : RelayRep.entry_ok Bm L' A' mem' (nth i es' no_entry))
    by (rewrite Forall_forall in HOK'; exact (HOK' _ HIE)).
  destruct EOK as (_ & _ & _ & _ & _ & HC & _).
  destruct HEL as (HB & HH & _).
  split; [|split].
  - intros Hc.
    assert (Hp : 0 < re_cap (nth i es' no_entry)) by (clear - HC HCAP Hc; destruct HC as [E0|[E0|E0]]; lia).
    destruct (HB Hp) as (_ & HA). rewrite HA.
    apply (chain_in_ent _ _ _ _ (nth i es' no_entry)); [exact HIE|].
    unfold entry_nc. apply in_or_app. left.
    destruct (Z.eqb_spec (re_cap (nth i es' no_entry)) 0) as [E0|_]; [clear - Hp E0; lia|left; reflexivity].
  - intros Hk.
    assert (Hp : re_hp (nth i es' no_entry) <> 0).
    { intros E0. unfold ent_ka in HKA. rewrite E0, Z.eqb_refl in HKA. exact (Hk (eq_sym HKA)). }
    destruct (HH Hp) as (_ & HA). rewrite HA.
    apply (chain_in_ent _ _ _ _ (nth i es' no_entry)); [exact HIE|].
    unfold entry_nc. apply in_or_app. right.
    destruct (Z.eqb_spec (re_hp (nth i es' no_entry)) 0) as [E0|_]; [contradiction|left; reflexivity].
  - intros Hx.
    unfold src_at, list_at in HSA.
    destruct HSA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLX & _).
    destruct HLX as (_ & _ & HZ & _).
    assert (Hp : 0 < hl_cap (hs_expected (nth i hs' (fst (nth i hj no_hj))))).
    { clear - HZ HEC Hx. destruct HZ as [(E0 & _)|(E0 & _)]; lia. }
    destruct HSL as (_ & _ & _ & (HEV & _) & _).
    destruct (HEV Hp) as (_ & HA). rewrite HA.
    apply (chain_in_src _ _ _ _ _ _ (chain_p5c_in es hj hs' i Hi He HLH')).
    cbn [fst]. unfold src_nc, arr_nc. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    destruct (Z.eqb_spec (hl_cap (hs_expected (nth i hs' (fst (nth i hj no_hj))))) 0) as [E0|_];
      [clear - Hp E0; lia|left; reflexivity].
Qed.
