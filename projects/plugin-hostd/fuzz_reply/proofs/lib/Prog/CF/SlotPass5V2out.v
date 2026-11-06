From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack AllocBound AllocPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayRunT RelayRunF ListTr RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c relay_remove_b_c SlotInv SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import relay_instance_gone_b_c RelayCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import check_no_loss_c check_shape_ends_c SlotPass2Check SlotPass4C SlotPass5Run relay_remove_b_aux SlotPass5Check relay_instance_gone_b_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotSteps SlotRes SlotRI3 SlotRun3 SlotP5R3G SlotP5Res3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotPass5M.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotPass5V.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma out_ker_dead : forall mx xks no cap j o, snd (snd (keys_end_run false mx no cap xks j o)) = o.
Proof.
  intros mx xks. induction xks as [|[xl ka] r IH]; intros no cap j o; [reflexivity|].
  cbn [keys_end_run]. cbv zeta. cbn [snd]. rewrite IH. reflexivity.
Qed.

Lemma out_gone_dead : forall mx pre ps no cap nm j o, fst (snd (gone_run false mx no cap pre ps nm j o)) = o.
Proof.
  intros mx pre ps. induction ps as [|[e hj] r IH]; intros no cap nm j o; [reflexivity|].
  cbn [gone_run]. cbv zeta.
  match goal with |- context [gone_run false mx ?n ?c pre r nm ?j1 ?o1] =>
    pose proof (IH n c nm j1 o1) as IHr; destruct (gone_run false mx n c pre r nm j1 o1) as [[[t c'] ss] [o2 das]] end.
  cbn [fst snd] in IHr |- *. rewrite IHr, out_ker_dead.
  unfold after_drain_adr. destruct (re_eof e =? 0); [|reflexivity].
  unfold drain_adr, drain_go. exact (proj2 (drain_dead _ mx _ j (drain_start nm o e (fst hj)))).
Qed.

Lemma out_gone_out_dead : forall mx NO CAP pre es hs nm j o, gone_out false mx NO CAP pre es hs nm j o = o.
Proof. intros mx NO CAP pre es hs nm j o. unfold gone_out. apply out_gone_dead. Qed.

Lemma out_live_split : forall cl br dd n, send_live cl br dd n = false -> send_live cl br dd 1 = false \/ n = 0.
Proof.
  intros cl br dd n. unfold send_live, send_off.
  destruct (cl <? 0), (br =? 1), (dd =? 0); cbn; try (intros; left; reflexivity).
  destruct (n =? 0) eqn:E; cbn; intros H; [right; apply Z.eqb_eq; exact E | discriminate].
Qed.

Lemma out_quiet : forall (rc : RunCeil) (Bm : malloc_syms) (L : layout) (A : astate) (mem : word -> option byte)
    (t cl br dd mx NO CAP : Z) (pre : list Z) (es : list rentry) (hj : list (hsrc * nat))
    (kss : list (list (list Z))) (nm : Z -> adrF) (o : adrF),
  Forall (CF.RelayRep.entry_ok Bm L A mem) es -> Forall2 (pair_ok Bm L A mem t) es hj -> length hj = length es ->
  (forall i, (i < length es)%nat ->
     nth i kss [] = ds_H (nth i (gone_states (send_live cl br dd 1) mx NO CAP pre es hj)
                            (drain_init NO CAP (nth i es no_entry) (fst (nth i hj no_hj))))) ->
  send_live cl br dd (Z.of_nat (length (concat (map (fun i => gone_segment pre (entry_lines (nth i es no_entry)
    (nth i hj no_hj)) (nth i kss [])) (seq 0 (length es)))))) = false ->
  gone_cap (send_live cl br dd 1) mx NO CAP pre es hj = CAP /\
  gone_out (send_live cl br dd 1) mx NO CAP pre es hj nm 0 o = o.
Proof.
  intros rc Bm L A mem t cl br dd mx NO CAP pre es hj kss nm o HES HPA Lh HK EL.
  destruct (out_live_split cl br dd _ EL) as [LV|T0].
  - rewrite LV. split; [apply gone_cap_dead | apply out_gone_out_dead].
  - apply (gone_tot0_holds (send_live cl br dd 1) mx NO CAP pre es hj kss nm 0%nat o Lh
             (g5m_tot0_drain Bm L A mem t es hj HES HPA) HK).
    apply length_zero_iff_nil. clear - T0. lia.
Qed.

Lemma out_notF : forall G O es hj, NoDup (target_addrs G O es hj) ->
  ~ In O (concat (map entry_blocks es)) /\ ~ In O (drained_blocks es hj).
Proof.
  intros G O es hj HN. apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HN. unfold target_addrs in HN.
  apply List.NoDup_cons_iff in HN as [_ HN]. apply List.NoDup_cons_iff in HN as [HO _].
  split; intros HI; apply HO; apply in_or_app.
  - left. exact HI.
  - right. unfold drained_blocks in HI. apply in_concat in HI as (l & Hl & Hq).
    apply in_map_iff in Hl as ([e [h n]] & <- & Hin). cbn [fst snd] in Hq |- *.
    apply in_concat. exists (hs_blocks h). split.
    + exact (in_map (fun p => hs_blocks (fst p)) hj (h, n) (Stdlib.Lists.List.in_combine_r _ _ _ _ Hin)).
    + revert Hq. destruct (re_eof e =? 0); [exact (fun X => X) | intros []].
Qed.

Theorem p5v_out_pf : p5v_out_S.
Proof.
  intros rc Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP' es' hs'
    kss qs H.
  cbv zeta. intros Hc.
  unfold p5v_ctx in H. cbv zeta in H.
  destruct H as (HMR & HND & HO & HG & HES & HPA & HTA & Lh & _ & _ & _ & _ & _ & _ & _ & _ & HP & _ & HLV &
    _ & _ & _ & _ & _ & _ & HI & _ & _ & _ & _ & HDEAD & _).
  unfold view_of. cbn [rv_nc]. apply in_cons.
  match type of HLV with ?l = true -> _ => destruct (Bool.bool_dec l true) as [EL|EL] end.
  - destruct (HLV EL) as [_ HA]. rewrite HA. apply in_eq.
  - pose proof (Bool.not_true_is_false _ EL) as EF.
    assert (HK : forall i, (i < length es)%nat ->
      nth i kss [] = ds_H (nth i (gone_states (send_live cl br dd 1) (bv_unsigned mx) (bv_unsigned nout)
                                   (bv_unsigned cap) pre es hj)
                            (drain_init (bv_unsigned nout) (bv_unsigned cap) (nth i es no_entry) (fst (nth i hj no_hj))))).
    { intros i Hi. destruct (HI i Hi) as (_ & _ & _ & _ & _ & X & _). exact X. }
    destruct (out_quiet rc Bm L A mem t cl br dd (bv_unsigned mx) (bv_unsigned nout) (bv_unsigned cap) pre es hj kss
                (known_at L A) (known_at L A (bv_unsigned out)) HES HPA Lh HK EF) as [GC GO].
    rewrite GC in Hc. rewrite GO.
    destruct (HDEAD EF) as (EO & _ & _).
    unfold output_at in HO. cbv zeta in HO.
    destruct HO as ((O & junk & [(C0 & _)|(CP & _ & IN & _)]) & _); [exfalso; exact (Hc C0)|].
    destruct (sptr_of_spec L A (bv_unsigned out) (bv_unsigned cap) (proj2 (stdpp.base.NoDup_ListNoDup _) HND) IN)
      as [Hin Hpa].
    destruct (out_notF G (bv_unsigned out) es hj HTA) as [NE ND].
    unfold relay_post in HP. destruct HP as (_ & _ & _ & _ & _ & HKEEP & HLIVE0 & _).
    assert (Hin' : In (sptr_of L A (bv_unsigned out), bv_unsigned cap) (user_blocks A')).
    { apply (HLIVE0 _ _ Hin CP). cbv beta. rewrite Hpa. intros [[X _]|[X|X]]; [exact (EL X) | exact (NE X) | exact (ND X)]. }
    assert (HA : ptr_addr L' (sptr_of L A (bv_unsigned out)) = ptr_addr L (sptr_of L A (bv_unsigned out))).
    { apply (HKEEP _ _ Hin Hin'). cbv beta. rewrite Hpa.
      intros [[X _]|[X|X]]; [exact (EL X) | exact (NE X) | exact (ND X)]. }
    unfold known_at. cbn [resolve]. rewrite HA, Hpa, EO. apply in_eq.
Qed.
