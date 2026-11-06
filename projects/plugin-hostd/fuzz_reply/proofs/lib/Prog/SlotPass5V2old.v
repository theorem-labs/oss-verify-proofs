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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement StatementKept
  send_line_c gesture_end_c relay_event_c RelayFrame RelayRunT RelayRunF ListTr RelayModel RelayKeys send_line_b_c
  gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep HarnessRep ListRep CheckRep drain_b_c
  relay_remove_b_c SlotInv SlotReads printf_facts_c snprintf_c relay_instance_gone_b_c RelayCap
  check_shape_done_c check_no_loss_c check_shape_ends_c SlotPass2Check SlotPass4C SlotPass5Run relay_remove_b_aux
  SlotPass5Check relay_instance_gone_b_lem SlotCaps3 SlotSteps SlotRes SlotRI3 SlotRun3 SlotP5R3G SlotP5Res3
  TrModel SlotPass5M.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotPass5V.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListFrame.
Import ListNotations.
Local Open Scope Z_scope.

Lemma old_run_hp : forall lv mx pre (ps : list (rentry * (hsrc * nat))) no cap nm j o i d,
  (i < length ps)%nat -> re_eof (fst (nth i ps (no_entry, no_hj))) <> 0 ->
  da_hp (nth i (snd (snd (gone_run lv mx no cap pre ps nm j o))) d) = nm (re_hp (fst (nth i ps (no_entry, no_hj)))).
Proof.
  intros lv mx pre ps. induction ps as [|[e hj] r IH]; intros no cap nm j o i d Hi He; [cbn [length] in Hi; lia|].
  cbn [gone_run]. cbv zeta.
  match goal with |- context [gone_run lv mx ?n ?c pre r nm ?j1 ?o1] =>
    pose proof (IH n c nm j1 o1) as IHr; destruct (gone_run lv mx n c pre r nm j1 o1) as [[[t c'] ss] [o2 das]] end.
  cbn [fst snd] in IHr |- *. destruct i as [|i]; cbn [nth fst snd da_hp] in He |- *.
  - unfold after_drain_adr. rewrite (proj2 (Z.eqb_neq _ _) He). reflexivity.
  - cbn [length] in Hi. exact (IHr i d ltac:(lia) He).
Qed.

Lemma old_pair_in (es : list rentry) (hj : list (hsrc * nat)) i : length hj = length es -> (i < length es)%nat ->
  In (nth i es no_entry, nth i hj no_hj) (combine es hj).
Proof.
  intros Hl Hi. rewrite <- combine_nth by (symmetry; exact Hl). apply nth_In.
  rewrite length_combine, Hl, Nat.min_id. exact Hi.
Qed.

Lemma old_ka lv mx pre (es : list rentry) (hj : list (hsrc * nat)) no cap nm j o i d :
  length hj = length es -> (i < length es)%nat -> re_eof (nth i es no_entry) <> 0 ->
  ds_ka (nth i (snd (fst (gone_run lv mx no cap pre (combine es hj) nm j o))) d) = ent_ka (nth i es no_entry).
Proof.
  intros Hl Hi He.
  destruct (g5m_gs_after lv mx pre (combine es hj) no cap nm j o i d
    ltac:(rewrite length_combine, Hl, Nat.min_id; exact Hi)) as (no' & cap' & EQ).
  rewrite EQ, combine_nth by (symmetry; exact Hl). cbn [fst snd]. unfold after_drain.
  rewrite (proj2 (Z.eqb_neq _ _) He). reflexivity.
Qed.

Lemma old_hp lv mx pre (es : list rentry) (hj : list (hsrc * nat)) no cap nm j o i d :
  length hj = length es -> (i < length es)%nat -> re_eof (nth i es no_entry) <> 0 ->
  da_hp (nth i (snd (snd (gone_run lv mx no cap pre (combine es hj) nm j o))) d) = nm (re_hp (nth i es no_entry)).
Proof.
  intros Hl Hi He.
  rewrite (old_run_hp lv mx pre (combine es hj) no cap nm j o i d);
    [| rewrite length_combine, Hl, Nat.min_id; exact Hi | rewrite combine_nth by (symmetry; exact Hl); exact He].
  rewrite combine_nth by (symmetry; exact Hl). reflexivity.
Qed.

Lemma old_g5_0 e h h' : re_eof e = 0 -> g5_src e h h' = h'.
Proof. intros E. unfold g5_src. rewrite E. reflexivity. Qed.

Lemma old_g5_1 e h h' : re_eof e <> 0 -> g5_src e h h' = h.
Proof. intros E. unfold g5_src. rewrite (proj2 (Z.eqb_neq _ _) E). reflexivity. Qed.

Lemma old_tch_in OUT CAP (es : list rentry) (hj : list (hsrc * nat)) i x :
  length hj = length es -> (i < length es)%nat -> re_eof (nth i es no_entry) = 0 ->
  In x ((if re_cap (nth i es no_entry) =? 0 then [] else [re_buf (nth i es no_entry)]) ++
        (if ent_ka (nth i es no_entry) =? 0 then [] else [re_hp (nth i es no_entry)]) ++
        (if hl_cap (hs_expected (fst (nth i hj no_hj))) =? 0 then []
         else [hl_v (hs_expected (fst (nth i hj no_hj)))])) ->
  In x (gone_tch OUT CAP es hj).
Proof.
  intros Hl Hi E0 Hx. unfold gone_tch. apply in_or_app. right. apply in_concat.
  eexists. split; [apply in_map; exact (old_pair_in es hj i Hl Hi)|]. cbn [fst snd]. rewrite E0. exact Hx.
Qed.

Theorem p5v_old_pf : p5v_old_S.
Proof.
  intros rc Bm API L A regs mem md t k G es hj cl br dd mx nout cap out pre L' A' regs' mem' md' OUT' CAP' es' hs'
    kss qs HC.
  cbv zeta. intros p n Hp Hin Hnt.
  unfold p5v_ctx in HC. cbv zeta in HC.
  destruct HC as (HMR & HND & HO & _ & HE & _ & _ & Hlen & _ & _ & _ & _ & _ & _ & _ & _ & HRP & _ & _ & HLK & _ &
    Hlen' & _ & _ & Hhs' & HI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPA).
  assert (EA : ptr_addr L' p = ptr_addr L p).
  { unfold relay_post in HRP. destruct HRP as (_ & _ & _ & HLE & _).
    exact (ListFrame.lf_addr A L L' p n (mr_wf _ _ (aa_laws API) _ _ _ _ HMR) HLE Hp). }
  rewrite EA. unfold view_of in Hin |- *. cbn [rv_nc] in Hin |- *.
  destruct Hin as [Hx|[Hx|Hx]].
  - left. exact Hx.
  - exfalso. destruct (Z.eqb_spec (bv_unsigned cap) 0) as [C0|C0].
    + destruct HO as ((O & junk & [(_ & O0 & _)|(X & _)]) & _); [|clear - C0 X; lia].
      pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HMR Hp) as [R _].
      clear - Hx O0 R. lia.
    + apply Hnt. unfold gone_tch. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) C0). left. exact Hx.
  - apply in_app_or in Hx as [Hx|Hx].
    + apply in_concat in Hx as (l & Hl & Hxl). apply in_map_iff in Hl as (e & <- & He).
      destruct (In_nth es e no_entry He) as (i & Hi & Ei). subst e.
      pose proof (proj1 (Forall_forall _ _) HE _ He) as EOK.
      destruct EOK as (Heof & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhp & _).
      pose proof (HI i Hi) as HIi. cbv zeta in HIi.
      destruct HIi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HKA & _ & H1).
      unfold entry_nc in Hxl. apply in_app_or in Hxl as [Hxl|Hxl].
      * destruct (Z.eqb_spec (re_cap (nth i es no_entry)) 0) as [C|C]; [destruct Hxl|]. destruct Hxl as [Hxl|[]].
        destruct Heof as [E0|E1].
        -- exfalso. apply Hnt. apply (old_tch_in _ _ es hj i _ Hlen Hi E0).
           apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) C). left. exact Hxl.
        -- destruct (H1 E1) as (_ & _ & Eb & _ & Ec).
           right. right. apply in_or_app. left. apply in_concat. exists (entry_nc (nth i es' no_entry)).
           split; [apply in_map, nth_In; rewrite Hlen'; exact Hi|].
           unfold entry_nc. rewrite Ec, Eb. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) C). left.
           exact Hxl.
      * destruct (Z.eqb_spec (re_hp (nth i es no_entry)) 0) as [C|C]; [destruct Hxl|]. destruct Hxl as [Hxl|[]].
        assert (Kh : re_kh (nth i es no_entry) <> 0)
          by (destruct Hhp as [(X & _)|(_ & _ & _ & X & _)]; [exfalso; exact (C X)|clear - X; lia]).
        assert (Ka : ent_ka (nth i es no_entry) = re_kh (nth i es no_entry))
          by (unfold ent_ka; rewrite (proj2 (Z.eqb_neq _ _) C); reflexivity).
        destruct Heof as [E0|E1].
        -- exfalso. apply Hnt. apply (old_tch_in _ _ es hj i _ Hlen Hi E0).
           apply in_or_app. right. apply in_or_app. left. rewrite Ka, (proj2 (Z.eqb_neq _ _) Kh). left. exact Hxl.
        -- assert (He1 : re_eof (nth i es no_entry) <> 0) by (rewrite E1; discriminate).
           unfold gone_states in HKA. rewrite (old_ka _ _ _ es hj _ _ _ _ _ i _ Hlen Hi He1), Ka in HKA.
           assert (Hh' : re_hp (nth i es' no_entry) <> 0).
           { intros Z0. apply Kh. rewrite <- HKA. unfold ent_ka. rewrite Z0. reflexivity. }
           destruct (HLK i Hi) as ((_ & Lh & _) & _).
           unfold gone_adrs in Lh. rewrite (old_hp _ _ _ es hj _ _ _ _ _ i _ Hlen Hi He1) in Lh.
           destruct (Lh Hh') as (_ & Ep). unfold known_at in Ep. cbn [resolve] in Ep.
           rewrite Hxl, (SlotP5Res3.sptr_at L A p n (ptr_addr L p) HND Hp eq_refl), EA in Ep.
           right. right. apply in_or_app. left. apply in_concat. exists (entry_nc (nth i es' no_entry)).
           split; [apply in_map, nth_In; rewrite Hlen'; exact Hi|].
           unfold entry_nc. apply in_or_app. right. rewrite (proj2 (Z.eqb_neq _ _) Hh'). left. exact (eq_sym Ep).
    + apply in_concat in Hx as (l & Hl & Hxl). apply in_map_iff in Hl as (y & <- & Hy).
      destruct (In_nth hj y no_hj Hy) as (i & Hi & Ei). subst y. rewrite Hlen in Hi.
      assert (He : In (nth i es no_entry) es) by (apply nth_In; exact Hi).
      pose proof (proj1 (Forall_forall _ _) HE _ He) as EOK. destruct EOK as (Heof & _).
      pose proof (HI i Hi) as HIi. cbv zeta in HIi.
      destruct HIi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H0 & _).
      right. right. apply in_or_app. right. apply in_concat.
      exists (src_nc (g5_src (nth i es no_entry) (fst (nth i hj no_hj)) (nth i hs' (fst no_hj)))). split.
      * apply in_map_iff.
        exists (g5_src (nth i es no_entry) (fst (nth i hj no_hj)) (nth i hs' (fst no_hj)), snd (nth i hj no_hj)).
        split; [reflexivity|]. unfold p5c_hj. apply in_map_iff. exists i. split; [reflexivity|].
        apply in_seq. clear - Hi. lia.
      * destruct Heof as [E0|E1].
        -- rewrite (old_g5_0 _ _ _ E0).
           rewrite (nth_indep hs' (fst no_hj) (fst (nth i hj no_hj))) by (rewrite Hhs'; exact Hi).
           pose proof (HPA i Hi E0) as Hpa.
           destruct (H0 E0) as (_ & _ & _ & _ & _ & Pc & Pv & _ & _ & _ & _ & Hh & _).
           unfold src_nc, arr_nc in Hxl |- *. rewrite Pc, Pv, Hh, Hpa.
           rewrite !in_app_iff in Hxl |- *.
           destruct Hxl as [X|[X|[X|X]]]; [left; exact X|right; left; exact X| |right; right; right; exact X].
           exfalso. apply Hnt. apply (old_tch_in _ _ es hj i _ Hlen Hi E0).
           rewrite !in_app_iff. right. right. exact X.
        -- assert (N1 : re_eof (nth i es no_entry) <> 0) by (rewrite E1; discriminate).
           rewrite (old_g5_1 _ _ _ N1). exact Hxl.
Qed.
