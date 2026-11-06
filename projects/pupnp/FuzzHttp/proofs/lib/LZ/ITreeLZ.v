(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require AsanAcct CatSim.
Import ListNotations.
Import ITree.Exc.

Notation restrict := AsanAcct.restrict.
Notation unrestrict := AsanAcct.unrestrict.
Notation hclean := AsanAcct.hclean.
Notation MInv := AsanAcct.MInv.
Notation lazy_cover := AsanAcct.lazy_cover.
Notation A_wf := AsanAcct.A_wf.
Notation H_off_segments := AsanAcct.H_off_segments.
Notation wx_segs_nowrap := AsanAcct.wx_segs_nowrap.
Notation same_but_materialized := AsanAcct.same_but_materialized.

Definition perase (P : list word) (mo : Model) : Model := with_vm_backing (m_vm_lazy mo) P mo.

Definition ivl (P : list word) : list (Z * Z) :=
  map (fun p => (bv_unsigned p, bv_unsigned p + page_size))%Z P.

Definition P_aligned (P : list word) : Prop := Forall (fun p => bv_unsigned p mod page_size = 0)%Z P.

Lemma A_bytes_ivl : forall P, AsanAcct.A_bytes (ivl P) = (Z.of_nat (length P) * page_size)%Z.
Proof. induction P as [|p P IH]; cbn [ivl map AsanAcct.A_bytes length]; [reflexivity|]. cbn [fst snd]. fold (ivl P). rewrite IH. lia. Qed.

Lemma A_wf_ivl : forall P, P_aligned P -> A_wf (ivl P).
Proof.
  intros P HP. unfold AsanAcct.A_wf, ivl. apply Forall_map. eapply Forall_impl; [|exact HP].
  intros p Hp. cbn [fst snd]. split; [unfold page_size; lia|]. split; [exact Hp|].
  rewrite <- Zplus_mod_idemp_l, Hp. reflexivity.
Qed.

Lemma page_allowedb_ivl : forall P p,
  (bv_unsigned p mod page_size = 0)%Z -> P_aligned P ->
  AsanAcct.page_allowedb (ivl P) p = true <-> In p P.
Proof.
  intros P p Hp HP. unfold AsanAcct.page_allowedb, ivl. rewrite existsb_exists. split.
  - intros (iv & Hin & Hb). apply in_map_iff in Hin. destruct Hin as (q & <- & Hq). cbn [fst snd] in Hb.
    apply andb_prop in Hb. destruct Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    assert (E : bv_unsigned q = bv_unsigned p) by (unfold page_size in *; lia).
    assert (q = p) by (apply bv_eq; exact E). subst q. exact Hq.
  - intros Hin. exists (bv_unsigned p, (bv_unsigned p + page_size)%Z). split.
    + apply in_map_iff. exists p. split; [reflexivity| exact Hin].
    + cbn [fst snd]. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

Lemma perase_same : forall P mo mo', same_but_materialized mo mo' -> perase P mo' = perase P mo.
Proof.
  intros P mo mo' E. unfold AsanAcct.same_but_materialized in E. rewrite E.
  destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
Qed.

Lemma same_perase : forall P mo, same_but_materialized mo (perase P mo).
Proof. intros P mo. unfold perase. apply AsanAcct.with_vm_backing_same. Qed.

Lemma perase_perase : forall P Q mo, perase P (perase Q mo) = perase P mo.
Proof. intros P Q [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma perase_nolazy : forall mo, m_vm_lazy mo = [] -> m_vm_materialized mo = [] -> perase [] mo = mo.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] Hl Hm. cbn in *. subst. reflexivity. Qed.

Lemma m_halted_perase : forall P mo, m_halted (perase P mo) = m_halted mo.
Proof. intros P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_fs_perase : forall P mo, m_fs (perase P mo) = m_fs mo.
Proof. intros P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_fds_perase : forall P mo, m_fds (perase P mo) = m_fds mo.
Proof. intros P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_vmmaps_perase : forall P mo, m_vmmaps (perase P mo) = m_vmmaps mo.
Proof. intros P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_vm_lazy_perase : forall P mo, m_vm_lazy (perase P mo) = m_vm_lazy mo.
Proof. intros P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_vm_materialized_perase : forall P mo, m_vm_materialized (perase P mo) = P.
Proof. intros P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_tid_perase : forall P mo, m_tid (perase P mo) = m_tid mo.
Proof. intros P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_stdin_perase : forall P mo, m_stdin (perase P mo) = m_stdin mo.
Proof. intros P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma m_killed_perase : forall P mo, m_killed (perase P mo) = m_killed mo.
Proof. intros P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma perase_with_fds : forall P f mo, perase P (with_fds f mo) = with_fds f (perase P mo).
Proof. intros P f [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma perase_with_fs : forall P f mo, perase P (with_fs f mo) = with_fs f (perase P mo).
Proof. intros P f [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma perase_with_tid : forall P t mo, perase P (with_tid t mo) = with_tid t (perase P mo).
Proof. intros P t [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma perase_with_halted : forall P c mo, perase P (with_halted c mo) = with_halted c (perase P mo).
Proof. intros P c [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma perase_with_vmmaps : forall P h mo, perase P (with_vmmaps h mo) = with_vmmaps h (perase P mo).
Proof. intros P h [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma perase_vm_forget_range : forall P lo hi mo,
  perase (List.filter (page_outside_range lo hi) P) (vm_forget_range lo hi mo) = vm_forget_range lo hi (perase P mo).
Proof. intros P lo hi [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma perase_with_vm_backing : forall P l X mo, perase P (with_vm_backing l X mo) = with_vm_backing l P (perase P mo).
Proof. intros P l X [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma perase_vm_add_lazy : forall P a n mo, perase P (vm_add_lazy a n mo) = vm_add_lazy a n (perase P mo).
Proof. intros P a n [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma perase_app : forall W P mo, perase (W ++ P) mo = with_vm_backing (m_vm_lazy mo) (W ++ m_vm_materialized (perase P mo)) (perase P mo).
Proof. intros W P [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma vm_backing_used_perase : forall P mo,
  vm_backing_used (perase P mo) = (AsanAcct.eager_used mo + Z.of_nat (length P) * page_size)%Z.
Proof.
  intros P mo. rewrite AsanAcct.vm_backing_used_split. rewrite m_vm_materialized_perase.
  unfold AsanAcct.eager_used. rewrite m_vmmaps_perase, m_vm_lazy_perase. reflexivity.
Qed.

Lemma vm_backing_used_perase_ge : forall P mo,
  MInv (ivl P) mo -> P_aligned P -> (vm_backing_used mo <= vm_backing_used (perase P mo))%Z.
Proof.
  intros P mo HI HP. rewrite vm_backing_used_perase, AsanAcct.vm_backing_used_split.
  enough (length (m_vm_materialized mo) <= length P)%nat by (unfold page_size; nia).
  apply NoDup_incl_length; [exact (AsanAcct.minv_nodup _ _ HI)|].
  intros p Hp. apply (page_allowedb_ivl P p (AsanAcct.minv_aligned _ _ HI p Hp) HP). exact (AsanAcct.minv_allowed _ _ HI p Hp).
Qed.

Lemma MInv_budget_perase : forall P mo,
  MInv (ivl P) mo -> (vm_backing_used (perase P mo) <= vm_limit (m_vmmaps mo))%Z.
Proof. intros P mo HI. rewrite vm_backing_used_perase, <- A_bytes_ivl. exact (AsanAcct.minv_budget _ _ HI). Qed.

Definition zb (a : word) : bool :=
  ((0x7fff8000 <=? bv_unsigned a)%Z && (bv_unsigned a <? 0x8fff7000)%Z)
  || ((0x2008fff7000 <=? bv_unsigned a)%Z && (bv_unsigned a <? 0x10007fff8000)%Z).

Section ITreeLZ.
Variable node : Type.
Variable segs : list Segment.
Variable at_node : node -> machine_state -> Prop.

Variable hide : node -> resp -> (word -> bool) -> (word -> bool).

Notation itree := (itree node).
Notation epost := (@epost node).

Definition mreveal (S : word -> bool) (m : word -> option byte) : word -> option byte :=
  fun a => if S a then Some (Z_to_bv 8 0) else m a.
Definition reveal (S : word -> bool) (ms : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := mreveal S (ms_mem ms); ms_rom := ms_rom ms |}.

Definition unhidden (H H' : word -> bool) : word -> bool := fun a => H a && negb (H' a).

Definition hzero (H : word -> bool) (msF : machine_state) : Prop :=
  forall a, H a = true -> zb a = true -> ms_mem msF a = Some (Z_to_bv 8 0).

Definition nretL (n : node) (rsp : resp) (H : word -> bool) (ms1 : machine_state) : machine_state :=
  restrict (hide n rsp H) (nret (reveal (unhidden H (hide n rsp H)) ms1) rsp).

Fixpoint implL {R} (H : word -> bool) (t : itree R) (Q : R -> (word -> bool) -> machine_state -> Prop)
    (ms : machine_state) : Prop :=
  match t with
  | Ret r => evt segs (Q r H) ms
  | Vis n k => evt segs (fun ms1 => at_node n ms1 /\
                 forall rsp, implL (hide n rsp H) (k rsp) Q (nretL n rsp H ms1)) ms
  end.

#[using="Type"] Lemma implL_ret_intro : forall {R} H (r : R) Q ms, evt segs (Q r H) ms -> implL H (Ret r) Q ms.
Proof. intros. exact H0. Qed.

#[using="Type"] Lemma implL_mono : forall {R} (t : itree R) H (Q Q' : R -> (word -> bool) -> machine_state -> Prop) ms,
  implL H t Q ms -> (forall r H' ms', Q r H' ms' -> Q' r H' ms') -> implL H t Q' ms.
Proof.
  induction t as [r|n k IH]; intros H Q Q' ms HI HQ; cbn in *.
  - eapply evt_mono; eauto.
  - eapply evt_mono; [exact HI|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. eapply IH; eauto.
Qed.

#[using="Type"] Lemma implL_evt : forall {R} (t : itree R) H Q P ms,
  evt segs P ms -> (forall ms', P ms' -> implL H t Q ms') -> implL H t Q ms.
Proof.
  intros R t H Q P ms HE K. destruct t; cbn in *; eapply evt_cut; eauto; intros ms' HP; apply (K _ HP).
Qed.

#[using="Type"] Lemma implL_bind : forall {A B} (t : itree A) (f : A -> itree B) H Q1 Q ms,
  implL H t Q1 ms -> (forall r H' ms', Q1 r H' ms' -> implL H' (f r) Q ms') -> implL H (bind node t f) Q ms.
Proof.
  induction t as [r|n k IH]; intros f H Q1 Q ms HI Hf; cbn [bind].
  - cbn in HI. eapply implL_evt; [exact HI|]. intros ms' HQ. exact (Hf _ _ _ HQ).
  - cbn in HI |- *. eapply evt_mono; [exact HI|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Definition epostL {A} (Q : A -> (word -> bool) -> machine_state -> Prop) : exc A -> (word -> bool) -> machine_state -> Prop :=
  fun r H ms => match r with Unr => True | Ok a => Q a H ms end.

#[using="Type"] Lemma implL_ret_unr : forall {A} H (Q : A -> (word -> bool) -> machine_state -> Prop) ms, implL H (Ret Unr) (epostL Q) ms.
Proof. intros A H Q ms. cbn. apply evt_done. exact I. Qed.

#[using="Type"] Lemma implL_ebind : forall {A B} (t : itree (exc A)) (f : A -> itree (exc B)) H Q1 Q ms,
  implL H t (epostL Q1) ms -> (forall a H' ms', Q1 a H' ms' -> implL H' (f a) (epostL Q) ms') ->
  implL H (ebind t f) (epostL Q) ms.
Proof.
  intros A B t f H Q1 Q ms Ht Hf. unfold ebind. eapply implL_bind; [exact Ht|].
  intros [|a] H' ms' H1; cbn in H1.
  - apply implL_ret_unr.
  - apply Hf. exact H1.
Qed.

#[using="Type"] Lemma implL_epost_mono : forall {A} (t : itree (exc A)) H (Q Q' : A -> (word -> bool) -> machine_state -> Prop) ms,
  implL H t (epostL Q) ms -> (forall a H' ms', Q a H' ms' -> Q' a H' ms') -> implL H t (epostL Q') ms.
Proof.
  intros A t H Q Q' ms HI HQ. eapply implL_mono; [exact HI|]. intros [|a] H' ms'; cbn; auto.
Qed.

#[using="Type"] Lemma implL_ret_ok : forall {A} H (Q : A -> (word -> bool) -> machine_state -> Prop) a ms,
  evt segs (Q a H) ms -> implL H (Ret (Ok a)) (epostL Q) ms.
Proof. intros A H Q a ms HE. exact HE. Qed.

#[using="Type"] Lemma implL_enode : forall {A} H n (pl : resp -> option A) (Q : A -> (word -> bool) -> machine_state -> Prop) ms,
  evt segs (fun ms1 => at_node n ms1 /\
             forall rsp a, pl rsp = Some a -> evt segs (Q a (hide n rsp H)) (nretL n rsp H ms1)) ms ->
  implL H (enode n pl) (epostL Q) ms.
Proof.
  intros A H n pl Q ms HE. cbn. eapply evt_mono; [exact HE|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn.
  - apply Hk. reflexivity.
  - apply evt_done. exact I.
Qed.

#[using="Type"] Lemma msteps_cat : forall ms ms', msteps segs ms ms' -> CatSim.msteps segs ms ms'.
Proof.
  intros ms ms' HM. induction HM as [ms|ms ms1 ms2 [Hsvc Hst] HM IH].
  - apply CatSim.mst_refl.
  - eapply CatSim.mst_step; eauto.
Qed.

Section Lift.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="HH Hwx"] Lemma mstep_restricted_sstep : forall A msF msr' mo,
  lazy_cover H (m_vm_lazy mo) A -> A_wf A -> MInv A mo -> m_halted mo = None ->
  mstep segs (restrict H msF) msr' ->
  exists mo',
    sstep_cfg segs ACFG (mkCfg msF mo) [] (SNext (mkCfg (unrestrict H (ms_mem msF) msr') mo'))
    /\ (forall e st, sstep_cfg segs ACFG (mkCfg msF mo) e st -> e = [] /\ st = SNext (mkCfg (unrestrict H (ms_mem msF) msr') mo'))
    /\ MInv A mo' /\ same_but_materialized mo mo' /\ hclean H msr'
    /\ restrict H (unrestrict H (ms_mem msF) msr') = msr'.
Proof.
  intros A msF msr' mo Hcov Hwf Hinv Hh [Hsvc Hst].
  assert (HsvcF : ms_svc_pending msF = None) by (rewrite <- (AsanAcct.restrict_svc_pending H msF); exact Hsvc).
  destruct (AsanAcct.node_instr_restricted segs H HH Hwx A msF msr' mo Hcov Hwf Hinv Hh HsvcF Hst)
    as (mo' & Hinv' & Hsame & Hcl & Hacc & [Hok1 Hok2]).
  exists mo'. split; [exact (Hok1 tt)|]. split.
  { intros e st Hss. destruct (Hok2 e st Hss) as ([] & -> & ->). split; reflexivity. }
  split; [exact Hinv'|]. split; [exact Hsame|]. split; [exact Hcl|].
  apply AsanAcct.restrict_unrestrict_clean. exact Hcl.
Qed.

#[using="HH Hwx"] Lemma msteps_restricted_star : forall A msF msr' mo,
  lazy_cover H (m_vm_lazy mo) A -> A_wf A -> MInv A mo -> m_halted mo = None ->
  msteps segs (restrict H msF) msr' ->
  exists msF' mo',
    star_cfg segs ACFG (mkCfg msF mo) [] (mkCfg msF' mo')
    /\ restrict H msF' = msr' /\ MInv A mo' /\ same_but_materialized mo mo' /\ m_halted mo' = None.
Proof.
  intros A msF msr' mo Hcov Hwf Hinv Hh HM.
  remember (restrict H msF) as msr eqn:E. revert msF mo E Hcov Hinv Hh.
  induction HM as [ms|ms ms1 ms2 Hm HM IH]; intros msF mo -> Hcov Hinv Hh.
  - exists msF, mo. split; [apply star_cfg_refl|]. split; [reflexivity|]. split; [exact Hinv|].
    split; [apply AsanAcct.same_but_materialized_refl| exact Hh].
  - destruct (mstep_restricted_sstep A msF ms1 mo Hcov Hwf Hinv Hh Hm) as (mo1 & Hss & _ & Hinv1 & Hsame1 & Hcl1 & Hr1).
    pose proof (AsanAcct.same_but_materialized_frame _ _ Hsame1) as FR.
    assert (Hlz1 : m_vm_lazy mo1 = m_vm_lazy mo) by (destruct FR as (_ & _ & F & _); exact F).
    assert (Hh1 : m_halted mo1 = None) by (destruct FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F & _); rewrite F; exact Hh).
    destruct (IH (unrestrict H (ms_mem msF) ms1) mo1 (eq_sym Hr1) ltac:(rewrite Hlz1; exact Hcov) Hinv1 Hh1)
      as (msF' & mo' & Hstar & Hr' & Hinv' & Hsame' & Hh').
    exists msF', mo'. split.
    + change ([] : list event) with ([] ++ [] : list event). eapply star_cfg_step; [exact Hss| exact Hstar].
    + split; [exact Hr'|]. split; [exact Hinv'|]. split; [| exact Hh'].
      eapply AsanAcct.same_but_materialized_trans; eassumption.
Qed.

#[using="HH Hwx"] Lemma sstep_restricted_inv : forall A msF msr' mo e st,
  lazy_cover H (m_vm_lazy mo) A -> A_wf A -> MInv A mo -> m_halted mo = None ->
  mstep segs (restrict H msF) msr' ->
  sstep_cfg segs ACFG (mkCfg msF mo) e st ->
  exists mo', e = [] /\ st = SNext (mkCfg (unrestrict H (ms_mem msF) msr') mo')
    /\ MInv A mo' /\ same_but_materialized mo mo' /\ restrict H (unrestrict H (ms_mem msF) msr') = msr'.
Proof.
  intros A msF msr' mo e st Hcov Hwf Hinv Hh Hm Hss.
  destruct (mstep_restricted_sstep A msF msr' mo Hcov Hwf Hinv Hh Hm) as (mo' & _ & Hdet & Hinv' & Hsame & _ & Hr).
  destruct (Hdet e st Hss) as [-> ->]. exists mo'. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hinv'|]. split; [exact Hsame| exact Hr].
Qed.
End Lift.

#[using="Type"] Lemma apply_zeros_pw : forall m zs a,
  apply_zeros m zs a = if zeros_cover zs a then Some (Z_to_bv 8 0) else m a.
Proof. intros m zs a. unfold apply_zeros. destruct zs; [cbn; reflexivity| reflexivity]. Qed.

#[using="Type"] Lemma apply_unmaps_pw : forall m us a,
  apply_unmaps m us a = if zeros_cover us a then None else m a.
Proof. intros m us a. unfold apply_unmaps. destruct us; [cbn; reflexivity| reflexivity]. Qed.

#[using="Type"] Lemma write_to_mem_pw : forall bs m m' addr x,
  m x = m' x -> write_to_mem m addr bs x = write_to_mem m' addr bs x.
Proof.
  induction bs as [|b bs IH]; intros m m' addr x E; cbn [write_to_mem]; [exact E|].
  apply IH. cbn beta. destruct (bv_eqb x addr); [reflexivity| exact E].
Qed.

#[using="Type"] Lemma apply_writes_pw : forall ws m m' x,
  m x = m' x -> apply_writes m ws x = apply_writes m' ws x.
Proof.
  induction ws as [|[a bs] ws IH]; intros m m' x E; cbn [apply_writes]; [exact E|].
  apply IH. apply write_to_mem_pw. exact E.
Qed.

#[using="Type"] Lemma ms_mem_set_reg : forall st r v, ms_mem (set_reg st r v) = ms_mem st.
Proof. intros st r v. unfold set_reg. destruct (bv_eqb r 0); reflexivity. Qed.

#[using="Type"] Lemma nret_mem_pw : forall ms ms' eff x,
  eff_copies eff = [] -> ms_mem ms x = ms_mem ms' x -> ms_mem (nret ms eff) x = ms_mem (nret ms' eff) x.
Proof.
  intros ms ms' eff x HC E. unfold nret, advance_past_svc, apply_effect. cbn -[set_reg].
  rewrite !ms_mem_set_reg, HC. cbn [apply_copies].
  apply apply_writes_pw. rewrite !apply_zeros_pw, !apply_unmaps_pw. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma restrict_nretL_gen : forall n rsp H msF,
  eff_copies rsp = [] ->
  (forall x, H x = true -> hide n rsp H x = false ->
     ms_mem msF x = Some (Z_to_bv 8 0) \/ zeros_cover (eff_zeros rsp) x = true \/ zeros_cover (eff_unmaps rsp) x = true) ->
  restrict (hide n rsp H) (nret msF rsp) = nretL n rsp H (restrict H msF).
Proof.
  intros n rsp H msF HC HU. unfold nretL. set (H' := hide n rsp H) in *.
  unfold AsanAcct.restrict, nret, advance_past_svc, apply_effect, reveal.
  cbn -[set_reg apply_writes apply_copies apply_zeros apply_unmaps]. unfold set_reg.
  destruct (bv_eqb 10 0); cbn -[apply_writes apply_copies apply_zeros apply_unmaps]; f_equal;
    apply functional_extensionality; intros x; unfold AsanAcct.mrestrict;
    (destruct (H' x) eqn:EX'; [reflexivity|]); rewrite HC; cbn [apply_copies]; apply apply_writes_pw;
    rewrite !apply_zeros_pw, !apply_unmaps_pw; unfold mreveal, unhidden; rewrite EX'; cbn [negb andb];
    (destruct (H x) eqn:EX; [| reflexivity]); cbn;
    (destruct (zeros_cover (eff_zeros rsp) x) eqn:EZ; [reflexivity|]);
    (destruct (zeros_cover (eff_unmaps rsp) x) eqn:EU; [reflexivity|]);
    (destruct (HU x EX EX') as [E0|[C|C]]; [exact E0| congruence| congruence]).
Qed.

#[using="Type"] Lemma restrict_nretL : forall n rsp H msF,
  eff_copies rsp = [] -> hzero H msF ->
  (forall x, H x = true -> hide n rsp H x = false ->
     zb x = true \/ zeros_cover (eff_zeros rsp) x = true \/ zeros_cover (eff_unmaps rsp) x = true) ->
  restrict (hide n rsp H) (nret msF rsp) = nretL n rsp H (restrict H msF).
Proof.
  intros n rsp H msF HC HZ HU. apply restrict_nretL_gen; [exact HC|].
  intros x Hx Hx'. destruct (HU x Hx Hx') as [ZB|C]; [left; exact (HZ x Hx ZB)| right; exact C].
Qed.

#[using="Type"] Lemma restrict_nretL_same : forall n rsp H msF,
  eff_copies rsp = [] -> hide n rsp H = H ->
  restrict (hide n rsp H) (nret msF rsp) = nretL n rsp H (restrict H msF).
Proof.
  intros n rsp H msF HC E. apply restrict_nretL_gen; [exact HC|]. intros x Hx Hx'. rewrite E in Hx'. congruence.
Qed.

#[using="Type"] Lemma reveal_none : forall H ms, reveal (unhidden H H) ms = ms.
Proof.
  intros H [R F pc sv rv fc m ro]. unfold reveal. cbn. f_equal.
  apply functional_extensionality. intros a. unfold mreveal, unhidden. destruct (H a); reflexivity.
Qed.

#[using="Type"] Lemma nretL_same : forall n rsp H ms1,
  hide n rsp H = H -> nretL n rsp H ms1 = restrict H (nret ms1 rsp).
Proof. intros n rsp H ms1 E. unfold nretL. rewrite E, reveal_none. reflexivity. Qed.

#[using="Type"] Lemma hzero_unrestrict : forall H msF msr', hzero H msF -> hzero H (unrestrict H (ms_mem msF) msr').
Proof.
  intros H msF msr' HZ a Ha Za. rewrite AsanAcct.unrestrict_mem. unfold AsanAcct.munrestrict. rewrite Ha. exact (HZ a Ha Za).
Qed.

End ITreeLZ.

Arguments implL {node} segs at_node hide {R} H t Q ms.
Arguments epostL {A} Q r H ms.
Arguments implL_mono {node} segs at_node hide {R} t H Q Q' ms.
Arguments implL_evt {node} segs at_node hide {R} t H Q P ms.
Arguments implL_bind {node} segs at_node hide {A B} t f H Q1 Q ms.
Arguments implL_ebind {node} segs at_node hide {A B} t f H Q1 Q ms.
Arguments implL_enode {node} segs at_node hide {A} H n pl Q ms.
Arguments implL_ret_ok {node} segs at_node hide {A} H Q a ms.
Arguments implL_ret_unr {node} segs at_node hide {A} H Q ms.
Arguments implL_epost_mono {node} segs at_node hide {A} t H Q Q' ms.
