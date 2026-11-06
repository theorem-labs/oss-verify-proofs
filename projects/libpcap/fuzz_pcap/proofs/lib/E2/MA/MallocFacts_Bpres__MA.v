(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MSecret.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Image ZBridge SysStep Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_ntf_D.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_bigw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module MallocFacts_Bpres.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Definition data_of (r : meta) : meta := m_set_prev None (m_set_next None r).
End PORT.
End WithCeil.


Ltac msimp := cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
                   m_set_prev m_set_next m_set_mem m_set_avail m_set_freed m_set_last_idx m_set_freeable m_set_sizeclass m_set_maplen
                   data_of meta0] in *.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma aptr_eqb_spec' (a b : aptr) : reflect (a = b) (aptr_eqb a b).
Proof.
  destruct (aptr_eqb a b) eqn:E; constructor.
  - apply aptr_eqb_eq. exact E.
  - intros ->. rewrite aptr_eqb_refl in E. discriminate.
Qed.
End PORT.
End WithCeil.


Ltac case_ptr x y := destruct (aptr_eqb_spec' x y) as [?EQ|?NE]; [subst x|].

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma rec_upd st g f x :
  get_meta_rec (upd_meta g f st) x = if aptr_eqb x g then f (get_meta_rec st g) else get_meta_rec st x.
Proof. apply get_meta_rec_upd. Qed.

#[using="Type"] Lemma rec_put st g mr x :
  get_meta_rec (put_meta g mr st) x = if aptr_eqb x g then mr else get_meta_rec st x.
Proof. apply get_meta_rec_put. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma data_of_eq r r' :
  data_of r = data_of r' <->
  (m_mem r = m_mem r' /\ m_avail r = m_avail r' /\ m_freed r = m_freed r' /\ m_last_idx r = m_last_idx r'
   /\ m_freeable r = m_freeable r' /\ m_sizeclass r = m_sizeclass r' /\ m_maplen r = m_maplen r').
Proof.
  destruct r, r'; unfold data_of; msimp; split.
  - intros H. inversion H. repeat split; reflexivity.
  - intros (-> & -> & -> & -> & -> & -> & ->). reflexivity.
Qed.

#[using="Type"] Lemma get_stride_data r r' : data_of r = data_of r' -> get_stride r = get_stride r'.
Proof. intros H. apply data_of_eq in H. unfold get_stride. destruct H as (_ & _ & _ & -> & _ & -> & ->). reflexivity. Qed.
#[using="Type"] Lemma slot_start'_data r r' i : data_of r = data_of r' -> slot_start' r i = slot_start' r' i.
Proof. intros H. unfold slot_start'. rewrite (get_stride_data r r' H). apply data_of_eq in H. destruct H as (-> & _). reflexivity. Qed.
#[using="Type"] Lemma sstart_of_data r r' i : data_of r = data_of r' -> sstart_of r i = sstart_of r' i.
Proof. intros H. unfold sstart_of. rewrite (get_stride_data r r' H). apply data_of_eq in H. destruct H as (-> & _). reflexivity. Qed.
#[using="Type"] Lemma slot_free_data r r' i : data_of r = data_of r' -> slot_free r i <-> slot_free r' i.
Proof. intros H. apply data_of_eq in H. unfold slot_free. destruct H as (_ & -> & -> & _). tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kctx (st : mstate) : Prop :=
  0 <= c_seq (ctx st) < 256
  /\ (forall i, 0 <= bounces st i < 256) /\ (forall i, 0 <= unmap_seq st i < 256)
  /\ 0 <= c_secret (ctx st) < 2^64.

Definition usage_ok (st : mstate) (c : Z) : Prop := forall sc, c <= sc -> 0 <= usage st sc < 2^64.

Record KINV (st : mstate) (LB : list block) (c : Z) : Prop := mkKI {
  ki_links : ci_links_t st;
  ki_heads : ci_heads_t st;
  ki_hom : ci_homog st;
  ki_gmetas : ci_gmeta st;
  ki_grps : ci_groups st;
  ki_ginj : ci_group_inj st;
  ki_slts : ci_slots st;
  ki_sltt : ci_slots_total st;
  ki_unk : ci_ghdr_unk st;
  ki_h0 : ci_hdr0 st;
  ki_blks : Forall (blk_ok st) LB;
  ki_nodup : List.NoDup (map blk_slot LB);
  ki_cx : kctx st;
  ki_usage : usage_ok st c;
  ki_bk : ci_brk st;
  ki_ticks : ticks_ok st
  (* [comment removed for export] *)
}.

#[using="Type"] Lemma KINV_of_CINV st LB : CINV st LB -> KINV st LB 0.
Proof.
  intros C. pose proof (ci_cx _ _ C) as (S1 & S2 & S3 & S4 & S5).
  constructor; try (destruct C; assumption).
  - unfold kctx. repeat split; try apply S1; try apply S2; try apply S3; try apply S5.
  - intros sc _. apply S4.
Qed.

#[using="Type"] Lemma KINV_mono st LB c c' : KINV st LB c -> c <= c' -> KINV st LB c'.
Proof. intros K Hc. pose proof (ki_usage _ _ _ K) as U. destruct K; constructor; auto. intros sc Hsc. apply U. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section EXT.
Variables st st' : mstate.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis ES : s_shadow st' = s_shadow st.

#[using="EA"] Lemma meta_slot_ext g : meta_slot st g <-> meta_slot st' g.
Proof. unfold meta_slot. rewrite EA. tauto. Qed.
#[using="ES"] Lemma get_shadow_ext rid : get_shadow st' rid = get_shadow st rid.
Proof. unfold get_shadow. rewrite ES. reflexivity. Qed.
#[using="ER"] Lemma conc_ext q : conc st' q = conc st q.
Proof. unfold conc, get_region. rewrite ER. reflexivity. Qed.

(* [comment removed for export] *)
Hypothesis EL : forall x, m_next (get_meta_rec st' x) = m_next (get_meta_rec st x) /\ m_prev (get_meta_rec st' x) = m_prev (get_meta_rec st x).

#[using="EA EL"] Lemma links_ext : ci_links_t st -> ci_links_t st'.
Proof.
  intros [N P NN SF]. constructor.
  - intros m nx H. destruct (EL m) as [E1 _]. rewrite E1 in H. destruct (N m nx H) as [H1 H2].
    destruct (EL nx) as [_ E2]. rewrite E2. split; [exact H1| apply meta_slot_ext; exact H2].
  - intros m pv H. destruct (EL m) as [_ E1]. rewrite E1 in H. destruct (P m pv H) as [H1 H2].
    destruct (EL pv) as [E2 _]. rewrite E2. split; [exact H1| apply meta_slot_ext; exact H2].
  - intros m. destruct (EL m) as [E1 E2]. rewrite E1, E2. apply NN.
  - intros m H. destruct (EL m) as [E1 _]. rewrite E1 in H. apply meta_slot_ext. apply SF. exact H.
Qed.
End EXT.

(* [comment removed for export] *)
#[using="Type"] Lemma hosts_ext st st' b g : s_groups st' = s_groups st -> hosts st' b g <-> hosts st b g.
Proof. intros E. unfold hosts. rewrite E. tauto. Qed.
#[using="Type"] Lemma is_gm_ext st st' g : s_groups st' = s_groups st -> is_gm st' g <-> is_gm st g.
Proof. intros E. unfold is_gm. split; intros [b H]; exists b; [rewrite <- (hosts_ext st st')|rewrite (hosts_ext st st')]; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Record LPRE (st : mstate) (LB : list block) (c : Z) (g p : aptr) (i : Z) : Prop := mkLP {
  lp_hosts : hosts st p g;
  lp_i : 0 <= i <= m_last_idx (get_meta_rec st g);
  lp_nonfree : ~ slot_free (get_meta_rec st g) i;
  lp_nogroup : (s_groups st) !! (slot_start' (get_meta_rec st g) i) = None;
  lp_noblock : Forall (fun blk => blk_slot blk <> slot_start' (get_meta_rec st g) i) LB;
  lp_class : c <= m_sizeclass (get_meta_rec st g)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)












(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma lpre_gmeta st LB c g p i : KINV st LB c -> LPRE st LB c g p i -> gmeta_ok st g p.
Proof. intros K L. apply (ki_gmetas _ _ _ K). apply (lp_hosts _ _ _ _ _ _ L). Qed.

#[using="Type"] Lemma kinv_next st LB c g nx : KINV st LB c -> m_next (get_meta_rec st g) = Some nx ->
  meta_slot st nx /\ m_prev (get_meta_rec st nx) = Some g /\ m_next (get_meta_rec st nx) <> None
  /\ exists pv, m_prev (get_meta_rec st g) = Some pv /\ meta_slot st pv /\ m_next (get_meta_rec st pv) = Some g /\ (nx <> g -> pv <> g).
Proof.
  intros K NX. pose proof (ki_links _ _ _ K) as [N P NN SF].
  destruct (N g nx NX) as [P1 S1]. split; [exact S1|]. split; [exact P1|]. split.
  { intros E. apply (proj1 (NN nx)) in E. rewrite E in P1. discriminate. }
  destruct (m_prev (get_meta_rec st g)) as [pv|] eqn:PV.
  2:{ apply (proj2 (NN g)) in PV. rewrite PV in NX. discriminate. }
  destruct (P g pv PV) as [N2 S2]. exists pv. repeat split; auto.
  intros NE ->. rewrite N2 in NX. inversion NX. subst. apply NE. reflexivity.
Qed.

#[using="Type"] Lemma kinv_active st LB c sc a : KINV st LB c -> active st sc = Some a ->
  0 <= sc < 48 /\ meta_slot st a /\ m_next (get_meta_rec st a) <> None /\ is_gm st a /\ m_sizeclass (get_meta_rec st a) = sc
  /\ exists pv, m_prev (get_meta_rec st a) = Some pv /\ meta_slot st pv /\ m_next (get_meta_rec st pv) = Some a.
Proof.
  intros K HA. pose proof (ki_heads _ _ _ K) as [_ CA]. destruct (CA sc a HA) as (SC & NX & GM & SCa).
  pose proof (ki_links _ _ _ K) as [N P NN SF].
  split; [exact SC|]. split; [apply SF; exact NX|]. split; [exact NX|]. split; [exact GM|]. split; [exact SCa|].
  destruct (m_prev (get_meta_rec st a)) as [pv|] eqn:PV.
  2:{ apply (proj2 (NN a)) in PV. exfalso. exact (NX PV). }
  exists pv. destruct (P a pv PV) as [N2 S2]. auto.
Qed.

#[using="Type"] Lemma kinv_free_head st LB c h : KINV st LB c -> c_free_meta_head (ctx st) = Some h ->
  meta_slot st h /\ m_next (get_meta_rec st h) <> None /\ ~ is_gm st h
  /\ exists pv, m_prev (get_meta_rec st h) = Some pv /\ meta_slot st pv /\ m_next (get_meta_rec st pv) = Some h.
Proof.
  intros K HF. pose proof (ki_heads _ _ _ K) as [CF _]. destruct (CF h HF) as (NX & MM).
  pose proof (ki_links _ _ _ K) as [N P NN SF].
  split; [apply SF; exact NX|]. split; [exact NX|]. split.
  { intros [b [ai Hb]]. pose proof (go_mem _ _ _ (ki_gmetas _ _ _ K b h (ex_intro _ ai Hb))) as MEM. congruence. }
  destruct (m_prev (get_meta_rec st h)) as [pv|] eqn:PV.
  2:{ apply (proj2 (NN h)) in PV. exfalso. exact (NX PV). }
  exists pv. destruct (P h pv PV) as [N2 S2]. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kinv_fm_facts_raw st LB c g : KINV st LB c -> m_next (get_meta_rec st g) = None ->
  forall h, c_free_meta_head (ctx st) = Some h ->
    h <> g /\ meta_slot st h /\ exists pv, m_prev (get_meta_rec st h) = Some pv /\ pv <> g /\ meta_slot st pv.
Proof.
  intros K GN h HF. destruct (kinv_free_head st LB c h K HF) as (S1 & N1 & _ & pv & P1 & S2 & N2).
  split; [congruence|]. split; [exact S1|]. exists pv. repeat split; auto. congruence.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hosts_is_gm st b g : hosts st b g -> is_gm st g.
Proof. intros H. exists b. exact H. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LG (st : mstate) (q : aptr) : Prop := m_next (get_meta_rec st q) <> None \/ is_gm st q.

(* [comment removed for export] *)
Definition amc (c : mctx) :=
  (c_avail_meta c, c_meta_area_head c, c_meta_area_tail c, c_avail_meta_areas c, c_init_done c,
   c_mmap_counter c, c_avail_meta_count c, c_avail_meta_area_count c, c_meta_alloc_shift c).

Record ntf_frame (st st' : mstate) : Prop := mkNF {
  nf_amc : amc (ctx st') = amc (ctx st);
  nf_regions : s_regions st' = s_regions st;
  nf_shadow : s_shadow st' = s_shadow st;
  nf_areas : s_areas st' = s_areas st;
  nf_reserved : s_reserved st' = s_reserved st;
  nf_tick : s_tick st' = s_tick st;
  nf_brk : c_brk (ctx st') = c_brk (ctx st);
  nf_secret : c_secret (ctx st') = c_secret (ctx st);
  nf_groups : forall b gh, (s_groups st') !! b = Some gh -> (s_groups st) !! b = Some gh;
  nf_slots : forall s x, (s_slots st') !! s = Some x -> (s_slots st) !! s = Some x;
  nf_linked : forall q, m_next (get_meta_rec st' q) <> None -> LG st q;
  nf_metas : forall q, ~ LG st q -> get_meta_rec st' q = get_meta_rec st q
}.

#[using="Type"] Lemma frame_refl st : ntf_frame st st.
Proof. constructor; auto. intros q H. left. exact H. Qed.

#[using="Type"] Lemma LG_frame st stA q : ntf_frame st stA -> LG stA q -> LG st q.
Proof.
  intros FR [H|[b [ai Hb]]]. { apply (nf_linked _ _ FR). exact H. }
  right. exists b, ai. apply (nf_groups _ _ FR). exact Hb.
Qed.

#[using="Type"] Lemma frame_upd_meta st stA q f : ntf_frame st stA -> LG st q -> ntf_frame st (upd_meta q f stA).
Proof.
  intros FR Hq. destruct FR. constructor; auto.
  - intros q' H. rewrite rec_upd in H. destruct (aptr_eqb_spec' q' q); [subst; exact Hq| auto].
  - intros q' H. rewrite rec_upd. destruct (aptr_eqb_spec' q' q); [subst; tauto| auto].
Qed.

#[using="Type"] Lemma frame_put_meta st stA q r : ntf_frame st stA -> LG st q -> ntf_frame st (put_meta q r stA).
Proof. intros. rewrite <- (upd_meta_put stA q (fun _ => r)). apply frame_upd_meta; auto. Qed.

#[using="Type"] Lemma frame_ctx st stA f : ntf_frame st stA ->
  c_brk (f (s_ctx stA)) = c_brk (s_ctx stA) -> c_secret (f (s_ctx stA)) = c_secret (s_ctx stA) ->
  amc (f (s_ctx stA)) = amc (s_ctx stA) ->
  ntf_frame st (upd_ctx f stA).
Proof.
  intros FR E1 E2 E3. destruct FR. constructor; auto.
  - unfold ctx in *. cbn. congruence.
  - unfold ctx in *. cbn. congruence.
  - unfold ctx in *. cbn. congruence.
Qed.

#[using="Type"] Lemma frame_set_active st stA sc v : ntf_frame st stA -> ntf_frame st (set_active sc v stA).
Proof. intros FR. unfold set_active. apply frame_ctx; auto; reflexivity. Qed.

#[using="Type"] Lemma frame_set_head st stA h v : ntf_frame st stA -> ntf_frame st (set_head h v stA).
Proof. intros FR. destruct h; cbn; [apply frame_set_active| apply frame_ctx]; auto; reflexivity. Qed.

#[using="Type"] Lemma frame_grp_del st stA g p : ntf_frame st stA -> ntf_frame st (grp_del stA g p).
Proof.
  intros FR. destruct FR. unfold grp_del, del_slots, del_group. constructor; cbn; auto.
  - intros b gh Hb. apply nf_groups0. apply lookup_delete_Some in Hb. tauto.
  - intros s x Hs. apply nf_slots0.
    revert Hs. generalize (s_slots stA). intros tb.
    match goal with |- context [Z.iter ?n ?F (0, tb)] => set (f := F) end.
    assert (GEN : forall acc, (snd (Z.iter (m_last_idx (get_meta_rec stA g) + 1) f acc)) !! s = Some x -> (snd acc) !! s = Some x).
    { intros acc. unfold Z.iter. destruct (m_last_idx (get_meta_rec stA g) + 1); cbn; auto.
      revert acc. induction p0 using Pos.peano_ind; intros acc.
      - cbn. unfold f at 1. destruct acc as [j t]. cbn. rewrite lookup_delete_Some. tauto.
      - rewrite Pos.iter_succ. unfold f at 1. destruct (Pos.iter f acc p0) as [j t] eqn:E. cbn.
        rewrite lookup_delete_Some. intros [_ H]. apply IHp0. rewrite E. exact H. }
    apply (GEN (0, tb)).
Qed.

#[using="Type"] Lemma frame_aor st stA g i : ntf_frame st stA -> LG st g -> ntf_frame st (aor_st stA g i).
Proof. intros. unfold aor_st. apply frame_upd_meta; auto. Qed.

#[using="Type"] Lemma frame_act st stA a act : ntf_frame st stA -> LG st a -> ntf_frame st (act_st stA a act).
Proof. intros. unfold act_st. apply frame_upd_meta; auto. Qed.

#[using="Type"] Lemma frame_dequeue st stA h g : ntf_frame st stA -> ci_links_t stA -> LG st g ->
  ntf_frame st (dequeue h g stA).
Proof.
  intros FR CL Hg. unfold dequeue.
  apply frame_upd_meta; [|exact Hg].
  destruct (negb (optr_eqb (m_next (get_meta_rec stA g)) (Some g))); [|apply frame_set_head; exact FR].
  set (st1 := match m_prev (get_meta_rec stA g) with Some pv => _ | None => stA end).
  assert (F1 : ntf_frame st st1).
  { subst st1. destruct (m_prev (get_meta_rec stA g)) as [pv|] eqn:PV; [|exact FR].
    apply frame_upd_meta; [exact FR|]. apply (LG_frame st stA pv FR). left.
    destruct (cl_prev _ CL g pv PV) as [N _]. rewrite N. discriminate. }
  set (st2 := match m_next (get_meta_rec stA g) with Some nx => _ | None => st1 end).
  assert (F2 : ntf_frame st st2).
  { subst st2. destruct (m_next (get_meta_rec stA g)) as [nx|] eqn:NX; [|exact F1].
    apply frame_upd_meta; [exact F1|]. apply (LG_frame st stA nx FR). left.
    destruct (cl_next _ CL g nx NX) as [P _]. intros E. apply (proj1 (cl_none _ CL nx)) in E. rewrite E in P. discriminate. }
  destruct (optr_eqb (get_head st2 h) (Some g)); [apply frame_set_head|]; exact F2.
Qed.

#[using="Type"] Lemma frame_queue st stA h g : ntf_frame st stA -> ci_links_t stA ->
  (forall hd, get_head stA h = Some hd -> m_next (get_meta_rec stA hd) <> None) -> LG st g ->
  ntf_frame st (queue_st h g stA).
Proof.
  intros FR CL HH Hg. unfold queue_st, fm_link, fm_single.
  destruct (get_head stA h) as [hd|] eqn:HD.
  - specialize (HH hd eq_refl).
    apply frame_upd_meta.
    + destruct (m_prev (get_meta_rec stA hd)) as [pv|] eqn:PV.
      * apply frame_upd_meta; [apply frame_upd_meta; [exact FR| exact Hg]|].
        apply (LG_frame st stA pv FR). left. destruct (cl_prev _ CL hd pv PV) as [N _]. rewrite N. discriminate.
      * apply frame_upd_meta; [exact FR| exact Hg].
    + apply (LG_frame st stA hd FR). left. exact HH.
  - apply frame_set_head. apply frame_upd_meta; [exact FR| exact Hg].
Qed.

#[using="Type"] Lemma frame_fm st stA g : ntf_frame st stA -> ci_links_t (put_meta g meta0 stA) ->
  (forall hd, c_free_meta_head (ctx stA) = Some hd -> m_next (get_meta_rec (put_meta g meta0 stA) hd) <> None) -> LG st g ->
  ntf_frame st (fm_st stA g).
Proof.
  intros FR CL HH Hg. unfold fm_st. apply frame_queue; auto. apply frame_put_meta; auto.
Qed.

#[using="Type"] Lemma frame_seq st stA sc : ntf_frame st stA -> ntf_frame st (record_seq sc (step_seq stA)).
Proof.
  intros FR.
  assert (F1 : ntf_frame st (step_seq stA)).
  { unfold step_seq. destruct (c_seq (ctx stA) =? 255); apply frame_ctx; auto; reflexivity. }
  unfold record_seq. destruct (sc_in_seq_range sc); [apply frame_ctx; auto; reflexivity| exact F1].
Qed.

#[using="Type"] Lemma frame_fg_usage st stA g : ntf_frame st stA -> ntf_frame st (fg_usage_st stA g).
Proof. intros FR. unfold fg_usage_st. destruct (m_sizeclass _ <? 48); [unfold set_usage; apply frame_ctx|]; auto; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record same_but_links (st st' : mstate) : Prop := mkSBL {
  sbl_data : forall q, data_of (get_meta_rec st' q) = data_of (get_meta_rec st q);
  sbl_regions : s_regions st' = s_regions st;
  sbl_shadow : s_shadow st' = s_shadow st;
  sbl_areas : s_areas st' = s_areas st;
  sbl_groups : s_groups st' = s_groups st;
  sbl_slots : s_slots st' = s_slots st;
  sbl_tick : s_tick st' = s_tick st;
  sbl_reserved : s_reserved st' = s_reserved st;
  sbl_brk : c_brk (ctx st') = c_brk (ctx st);
  sbl_secret : c_secret (ctx st') = c_secret (ctx st);
  sbl_seq : c_seq (ctx st') = c_seq (ctx st);
  sbl_usage : forall sc, usage st' sc = usage st sc;
  sbl_bounces : forall j, bounces st' j = bounces st j;
  sbl_unmap : forall j, unmap_seq st' j = unmap_seq st j;
  sbl_fmh_or : True
}.

#[using="Type"] Lemma sbl_refl st : same_but_links st st.
Proof. constructor; auto. Qed.

#[using="Type"] Lemma sbl_trans a b c : same_but_links a b -> same_but_links b c -> same_but_links a c.
Proof. intros [] []; constructor; intros; try congruence. Qed.

#[using="Type"] Lemma data_of_links f r : (forall r, data_of (f r) = data_of r) -> data_of (f r) = data_of r.
Proof. auto. Qed.

#[using="Type"] Lemma sbl_upd_links st q f : (forall r, data_of (f r) = data_of r) -> same_but_links st (upd_meta q f st).
Proof.
  intros Hf. constructor; try reflexivity.
  intros q'. rewrite rec_upd. destruct (aptr_eqb_spec' q' q); [subst; apply Hf| reflexivity].
Qed.

#[using="Type"] Lemma sbl_set_head st h v : same_but_links st (set_head h v st).
Proof. destruct h; cbn; constructor; try reflexivity. Qed.

#[using="Type"] Lemma data_set_prev v r : data_of (m_set_prev v r) = data_of r. Proof. reflexivity. Qed.
#[using="Type"] Lemma data_set_next v r : data_of (m_set_next v r) = data_of r. Proof. reflexivity. Qed.

#[using="Type"] Lemma sbl_upd_links'' st st0 q f : same_but_links st0 st -> (forall r, data_of (f r) = data_of r) -> same_but_links st0 (upd_meta q f st).
Proof. intros S Hf. eapply sbl_trans; [exact S| apply sbl_upd_links; exact Hf]. Qed.

#[using="Type"] Lemma sbl_set_head'' st st0 h v : same_but_links st0 st -> same_but_links st0 (set_head h v st).
Proof. intros S. eapply sbl_trans; [exact S| apply sbl_set_head]. Qed.

#[using="Type"] Lemma sbl_queue st h g : same_but_links st (queue_st h g st).
Proof.
  unfold queue_st, fm_link, fm_single.
  destruct (get_head st h) as [hd|]; [destruct (m_prev (get_meta_rec st hd)) as [pv|]|];
    repeat first [ apply sbl_set_head'' | apply sbl_upd_links''; [| intros; rewrite ?data_set_prev, ?data_set_next; reflexivity] | apply sbl_refl ].
Qed.

#[using="Type"] Lemma sbl_deq_mid st h g : same_but_links st (deq_mid h g st).
Proof.
  unfold deq_mid.
  destruct (negb (optr_eqb (m_next (get_meta_rec st g)) (Some g))); [| apply sbl_set_head].
  destruct (m_prev (get_meta_rec st g)) as [pv|]; destruct (m_next (get_meta_rec st g)) as [nx|];
    match goal with |- same_but_links st (if ?c then _ else _) => destruct c end;
    repeat first [ apply sbl_set_head'' | apply sbl_upd_links''; [| intros; rewrite ?data_set_prev, ?data_set_next; reflexivity] | apply sbl_refl ].
Qed.

#[using="Type"] Lemma sbl_dequeue st h g : same_but_links st (dequeue h g st).
Proof.
  rewrite dequeue_mid. apply sbl_upd_links''; [apply sbl_deq_mid|]. intros; reflexivity.
Qed.

#[using="Type"] Lemma data_of_fields st st' q : data_of (get_meta_rec st' q) = data_of (get_meta_rec st q) ->
  m_mem (get_meta_rec st' q) = m_mem (get_meta_rec st q) /\ m_avail (get_meta_rec st' q) = m_avail (get_meta_rec st q)
  /\ m_freed (get_meta_rec st' q) = m_freed (get_meta_rec st q) /\ m_last_idx (get_meta_rec st' q) = m_last_idx (get_meta_rec st q)
  /\ m_freeable (get_meta_rec st' q) = m_freeable (get_meta_rec st q) /\ m_sizeclass (get_meta_rec st' q) = m_sizeclass (get_meta_rec st q)
  /\ m_maplen (get_meta_rec st' q) = m_maplen (get_meta_rec st q).
Proof. intros H. apply data_of_eq. exact H. Qed.

#[using="Type"] Lemma LPRE_sbl st st' LB c g p i : same_but_links st st' -> LPRE st LB c g p i -> LPRE st' LB c g p i.
Proof.
  intros S L. pose proof (sbl_data _ _ S g) as D. destruct L. constructor.
  - unfold hosts in *. rewrite (sbl_groups _ _ S). exact lp_hosts0.
  - rewrite (proj1 (proj2 (proj2 (proj2 (data_of_fields st st' g D))))). exact lp_i0.
  - rewrite (slot_free_data _ _ i D). exact lp_nonfree0.
  - rewrite (sbl_groups _ _ S), (slot_start'_data _ _ i D). exact lp_nogroup0.
  - rewrite (slot_start'_data _ _ i D). exact lp_noblock0.
  - destruct (data_of_fields st st' g D) as (_ & _ & _ & _ & _ & -> & _). exact lp_class0.
Qed.

#[using="Type"] Lemma meta_slot_sbl st st' q : same_but_links st st' -> meta_slot st q -> meta_slot st' q.
Proof. intros S H. eapply meta_slot_same_areas; [apply (sbl_areas _ _ S)| exact H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma frame_trans st stA stB : ntf_frame st stA -> ntf_frame stA stB -> ntf_frame st stB.
Proof.
  intros F1 F2. pose proof (LG_frame st stA) as LGF.
  destruct F1, F2; constructor; try congruence; auto.
  - intros q H. apply LGF; [constructor; auto|]. apply nf_linked1. exact H.
  - intros q H. rewrite nf_metas1; [apply nf_metas0; exact H|]. intros H'. apply H. apply LGF; [constructor; auto| exact H'].
Qed.

#[using="Type"] Lemma LPRE_ctx st f LB c g p i : LPRE st LB c g p i -> LPRE (upd_ctx f st) LB c g p i.
Proof. intros L. destruct L; constructor; auto. Qed.

#[using="Type"] Lemma LPRE_fg_usage st LB c g p i : LPRE st LB c g p i -> LPRE (fg_usage_st st g) LB c g p i.
Proof. intros L. unfold fg_usage_st. destruct (_ <? 48); [apply LPRE_ctx|]; exact L. Qed.

#[using="Type"] Lemma LPRE_upd_other st q f LB c g p i : q <> g -> LPRE st LB c g p i -> LPRE (upd_meta q f st) LB c g p i.
Proof.
  intros NE L. destruct L; constructor; auto; rewrite ?rec_upd, ?(aptr_eqb_neq g q) by congruence; auto.
Qed.

#[using="Type"] Lemma LPRE_mono_c st LB c c' g p i : LPRE st LB c g p i -> c' <= c -> LPRE st LB c' g p i.
Proof. intros L Hc. destruct L; constructor; auto. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma grp_del_groups st g p : s_groups (grp_del st g p) = delete p (s_groups st). Proof. reflexivity. Qed.
#[using="Type"] Lemma grp_del_rec st g p q : get_meta_rec (grp_del st g p) q = get_meta_rec st q. Proof. reflexivity. Qed.
#[using="Type"] Lemma grp_del_regions st g p : s_regions (grp_del st g p) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma grp_del_shadow st g p : s_shadow (grp_del st g p) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma grp_del_areas st g p : s_areas (grp_del st g p) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma grp_del_ctx st g p : s_ctx (grp_del st g p) = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_grp_del st g p q : conc (grp_del st g p) q = conc st q. Proof. reflexivity. Qed.

#[using="Type"] Lemma fg_usage_rec st g q : get_meta_rec (fg_usage_st st g) q = get_meta_rec st q.
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
#[using="Type"] Lemma fg_usage_groups st g : s_groups (fg_usage_st st g) = s_groups st.
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
#[using="Type"] Lemma fg_usage_regions st g : s_regions (fg_usage_st st g) = s_regions st.
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
#[using="Type"] Lemma fg_usage_shadow st g : s_shadow (fg_usage_st st g) = s_shadow st.
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
#[using="Type"] Lemma fg_usage_areas st g : s_areas (fg_usage_st st g) = s_areas st.
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
#[using="Type"] Lemma fg_usage_slots st g : s_slots (fg_usage_st st g) = s_slots st.
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
#[using="Type"] Lemma conc_fg_usage st g q : conc (fg_usage_st st g) q = conc st q.
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
#[using="Type"] Lemma fmh_fg_usage st g : c_free_meta_head (ctx (fg_usage_st st g)) = c_free_meta_head (ctx st).
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
#[using="Type"] Lemma seq_fg_usage st g : c_seq (ctx (fg_usage_st st g)) = c_seq (ctx st).
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.
#[using="Type"] Lemma brk_fg_usage st g : c_brk (ctx (fg_usage_st st g)) = c_brk (ctx st).
Proof. unfold fg_usage_st. destruct (_ <? 48); reflexivity. Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma hosts_grp_del st g p b q : hosts (grp_del st g p) b q <-> b <> p /\ hosts st b q.
Proof.
  unfold hosts. rewrite grp_del_groups. split.
  - intros [ai H]. apply lookup_delete_Some in H. destruct H as [NE H]. split; [congruence| exists ai; exact H].
  - intros [NE [ai H]]. exists ai. apply lookup_delete_Some. split; [congruence| exact H].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma links_put_meta0 st g : ci_links_t st -> m_next (get_meta_rec st g) = None -> ci_links_t (put_meta g meta0 st).
Proof.
  intros [N P NN SF] GN. pose proof (proj1 (NN g) GN) as GP.
  constructor.
  - intros m nx H. rewrite rec_put in H. rewrite rec_put.
    destruct (aptr_eqb_spec' m g); [subst; cbn in H; discriminate|].
    destruct (N m nx H) as [H1 H2]. destruct (aptr_eqb_spec' nx g); [subst; rewrite GP in H1; discriminate|].
    split; [exact H1|]. unfold meta_slot in *. exact H2.
  - intros m pv H. rewrite rec_put in H. rewrite rec_put.
    destruct (aptr_eqb_spec' m g); [subst; cbn in H; discriminate|].
    destruct (P m pv H) as [H1 H2]. destruct (aptr_eqb_spec' pv g); [subst; rewrite GN in H1; discriminate|].
    split; [exact H1|]. exact H2.
  - intros m. rewrite rec_put. destruct (aptr_eqb_spec' m g); [subst; cbn; tauto| apply NN].
  - intros m H. rewrite rec_put in H. destruct (aptr_eqb_spec' m g); [subst; cbn in H; congruence|]. apply SF. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma seq_shape X sc : let st' := record_seq sc (step_seq X) in
  s_regions st' = s_regions X /\ s_shadow st' = s_shadow X /\ s_groups st' = s_groups X /\ s_slots st' = s_slots X
  /\ s_areas st' = s_areas X /\ s_metas st' = s_metas X /\ c_brk (ctx st') = c_brk (ctx X) /\ c_free_meta_head (ctx st') = c_free_meta_head (ctx X).
Proof.
  unfold record_seq, step_seq. destruct (c_seq (ctx X) =? 255); destruct (sc_in_seq_range sc); cbn; repeat split; reflexivity.
Qed.

#[using="Type"] Lemma fm_shape X g : let st' := fm_st X g in
  s_regions st' = s_regions X /\ s_shadow st' = s_shadow X /\ s_groups st' = s_groups X /\ s_slots st' = s_slots X
  /\ s_areas st' = s_areas X /\ c_brk (ctx st') = c_brk (ctx X).
Proof.
  pose proof (sbl_queue (put_meta g meta0 X) LFree g) as S. unfold fm_st. cbn zeta.
  rewrite (sbl_regions _ _ S), (sbl_shadow _ _ S), (sbl_groups _ _ S), (sbl_slots _ _ S), (sbl_areas _ _ S), (sbl_brk _ _ S).
  repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma deq_mid_shape st h g : same_but_links st (deq_mid h g st).
Proof. apply sbl_deq_mid. Qed.

#[using="Type"] Lemma conc_sbl st st' q : same_but_links st st' -> conc st' q = conc st q.
Proof. intros S. unfold conc, get_region. rewrite (sbl_regions _ _ S). reflexivity. Qed.

#[using="Type"] Lemma pd_st_cases an st1 sc :
  pd_st an st1 sc = st1 \/ exists a, an = true /\ active st1 sc = Some a /\ pd_st an st1 sc = act_st st1 a (act_of st1 a).
Proof.
  unfold pd_st. destruct an; [|left; reflexivity]. destruct (active st1 sc) as [a|]; [right; exists a; auto| left; reflexivity].
Qed.

#[using="Type"] Lemma act_st_rec_other st a act q : q <> a -> get_meta_rec (act_st st a act) q = get_meta_rec st q.
Proof. intros NE. unfold act_st. rewrite rec_upd, (aptr_eqb_neq q a NE). reflexivity. Qed.
#[using="Type"] Lemma act_st_groups st a act : s_groups (act_st st a act) = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma act_st_regions st a act : s_regions (act_st st a act) = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma act_st_shadow st a act : s_shadow (act_st st a act) = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma act_st_areas st a act : s_areas (act_st st a act) = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma act_st_ctx st a act : s_ctx (act_st st a act) = s_ctx st. Proof. reflexivity. Qed.

#[using="Type"] Lemma act_of_nonneg st a : 0 <= act_of st a.
Proof.
  unfold act_of. destruct (m_mem (get_meta_rec st a)) as [b|]; [|lia]. cbn [default id].
  unfold mask_upto.
  assert (H : 0 <= group_active_idx st b).
  { unfold group_active_idx. destruct (get_group st b); [apply Z.land_nonneg; right; lia| lia]. }
  assert (0 < 2 ^ (group_active_idx st b + 1)) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_start'_eq r i : slot_start' r i = (fst (default (0%N, 0) (m_mem r)), sstart_of r i).
Proof. unfold slot_start', sstart_of, aadd. destruct (m_mem r) as [[? ?]|]; cbn; f_equal; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

#[using="Type"] Lemma bits_lt_pow2 n a m : 0 <= a < 2^n -> n <= m -> Z.testbit a m = false.
Proof.
  intros Ha Hm. assert (Hn : 0 <= n) by (destruct (Z_lt_le_dec n 0); [rewrite Z.pow_neg_r in Ha by lia; lia| lia]).
  apply (proj1 (Z.bounded_iff_bits_nonneg n a Hn ltac:(lia))); lia.
Qed.
#[using="Type"] Lemma lt_pow2_bits n a : 0 <= n -> 0 <= a -> (forall m, n <= m -> Z.testbit a m = false) -> a < 2^n.
Proof. intros Hn Ha H. apply (proj2 (Z.bounded_iff_bits_nonneg n a Hn Ha)). exact H. Qed.
#[using="Type"] Lemma lor_range n a b : 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros Ha Hb. assert (Hn : 0 <= n) by (destruct (Z_lt_le_dec n 0); [rewrite Z.pow_neg_r in Ha by lia; lia| lia]).
  split; [apply Z.lor_nonneg; lia|].
  apply lt_pow2_bits; [lia| apply Z.lor_nonneg; lia|]. intros m Hm. rewrite Z.lor_spec, (bits_lt_pow2 n a m), (bits_lt_pow2 n b m) by lia. reflexivity.
Qed.
#[using="Type"] Lemma land_range n a b : 0 <= a < 2^n -> 0 <= b -> 0 <= Z.land a b < 2^n.
Proof.
  intros Ha Hb. assert (Hn : 0 <= n) by (destruct (Z_lt_le_dec n 0); [rewrite Z.pow_neg_r in Ha by lia; lia| lia]).
  split; [apply Z.land_nonneg; lia|].
  apply lt_pow2_bits; [lia| apply Z.land_nonneg; lia|]. intros m Hm. rewrite Z.land_spec, (bits_lt_pow2 n a m) by lia. reflexivity.
Qed.
#[using="Type"] Lemma ldiff_range n a b : 0 <= a < 2^n -> 0 <= Z.ldiff a b < 2^n.
Proof.
  intros Ha. assert (Hn : 0 <= n) by (destruct (Z_lt_le_dec n 0); [rewrite Z.pow_neg_r in Ha by lia; lia| lia]).
  assert (H0 : 0 <= Z.ldiff a b) by (apply (proj2 (Z.ldiff_nonneg a b)); lia).
  split; [exact H0|].
  apply lt_pow2_bits; [lia| exact H0|]. intros m Hm. rewrite Z.ldiff_spec, (bits_lt_pow2 n a m) by lia. reflexivity.
Qed.
#[using="Type"] Lemma bit_range i : 0 <= i <= 31 -> 0 <= bit i < 2^32.
Proof. intros Hi. unfold bit. split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]. Qed.
#[using="Type"] Lemma testbit_bit i j : 0 <= i -> Z.testbit (bit i) j = (i =? j).
Proof. intros. unfold bit. apply Z.pow2_bits_eqb. lia. Qed.
#[using="Type"] Lemma testbit_mask_upto li j : 0 <= li -> 0 <= j -> Z.testbit (mask_upto li) j = (j <=? li).
Proof.
  intros. unfold mask_upto. replace (2 ^ (li + 1) - 1) with (Z.ones (li + 1)).
  2:{ unfold Z.ones. rewrite Z.shiftl_1_l. lia. }
  rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec j (li + 1)); destruct (Z.leb_spec j li); try reflexivity; lia.
Qed.

#[using="Type"] Lemma all_free_of_mask : forall freed avail i li,
  0 <= freed < 2^32 -> 0 <= avail < 2^32 -> 0 <= i <= li -> li <= 31 ->
  Z.testbit freed i = false -> Z.testbit avail i = false ->
  Z.lor freed avail + bit i = mask_upto li ->
  forall j, 0 <= j <= li -> j <> i -> Z.testbit freed j = true \/ Z.testbit avail j = true.
Proof.
  intros freed avail i li HF HA Hi Hli Fi Ai HM j Hj NE.
  assert (L0 : Z.land (Z.lor freed avail) (bit i) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lor_spec, testbit_bit, Z.testbit_0_l by lia.
    destruct (Z.eqb_spec i n); [subst; rewrite Fi, Ai; reflexivity| apply andb_false_r]. }
  rewrite (Z.add_nocarry_lxor _ _ L0), (Z.lxor_lor _ _ L0) in HM.
  assert (T : Z.testbit (Z.lor (Z.lor freed avail) (bit i)) j = true).
  { rewrite HM, testbit_mask_upto by lia. apply Z.leb_le. lia. }
  rewrite !Z.lor_spec, testbit_bit in T by lia.
  destruct (Z.eqb_spec i j); [lia|]. rewrite orb_false_r in T.
  destruct (Z.testbit freed j); [left; reflexivity|]. destruct (Z.testbit avail j); [right; reflexivity|]. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma Z_iter_ind {A} (f : A -> A) (P : Z -> A -> Prop) x :
  P 0 x -> (forall n y, 0 <= n -> P n y -> P (n + 1) (f y)) ->
  forall n, 0 <= n -> P n (Z.iter n f x).
Proof.
  intros H0 HS n Hn. rewrite iter_nat_of_Z by exact Hn.
  rewrite <- (Z2Nat.id n) at 1 by exact Hn. rewrite <- Zabs2Nat.abs_nat_nonneg by exact Hn.
  induction (Z.abs_nat n) as [|k IH]; [exact H0|].
  cbn [nat_rect]. rewrite Nat2Z.inj_succ, <- Z.add_1_r. apply HS; [lia| exact IH].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma del_slots_lookup p stride cnt st s x : 0 <= cnt ->
  (s_slots (del_slots p stride cnt st)) !! s = Some x <->
  (s_slots st) !! s = Some x /\ forall i, 0 <= i < cnt -> s <> aadd p (UNIT + stride * i).
Proof.
  intros Hc. unfold del_slots. cbn [s_slots].
  match goal with |- context [Z.iter cnt ?f ?x0] =>
    enough (IND : fst (Z.iter cnt f x0) = cnt /\ forall s' x', snd (Z.iter cnt f x0) !! s' = Some x' <->
             ((s_slots st) !! s' = Some x' /\ forall i, 0 <= i < cnt -> s' <> aadd p (UNIT + stride * i)))
      by (apply (proj2 IND));
    apply (Z_iter_ind f (fun n acc => fst acc = n /\ forall s' x', snd acc !! s' = Some x' <->
             ((s_slots st) !! s' = Some x' /\ forall i, 0 <= i < n -> s' <> aadd p (UNIT + stride * i)))); [| | exact Hc]
  end.
  - split; [reflexivity|]. intros s' x'. cbn [snd]. split; [intros H; split; [exact H| intros; lia]| intros [H _]; exact H].
  - intros n [i tb] Hn [Hi IH]. cbn [fst snd] in Hi, IH |- *. subst i. split; [reflexivity|].
    intros s' x'. rewrite lookup_delete_Some, IH. split.
    + intros [NE [H1 H2]]. split; [exact H1|]. intros j Hj.
      destruct (Z.eq_dec j n) as [->|]; [congruence| apply H2; lia].
    + intros [H1 H2]. split; [| split; [exact H1| intros j Hj; apply H2; lia]].
      intros E. apply (H2 n); [lia| congruence].
Qed.

#[using="Type"] Lemma del_slots_lookup_None p stride cnt st s : 0 <= cnt ->
  (s_slots st) !! s = None -> (s_slots (del_slots p stride cnt st)) !! s = None.
Proof.
  intros Hc H. destruct (s_slots (del_slots p stride cnt st) !! s) as [x|] eqn:E; [|reflexivity].
  apply (del_slots_lookup p stride cnt st s x Hc) in E. destruct E as [E _]. congruence.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_start'_mem r p j : m_mem r = Some p -> slot_start' r j = aadd p (UNIT + get_stride r * j).
Proof. intros H. unfold slot_start'. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)

Definition geom_eq (r r' : meta) : Prop :=
  m_mem r' = m_mem r /\ m_last_idx r' = m_last_idx r /\ m_freeable r' = m_freeable r
  /\ m_sizeclass r' = m_sizeclass r /\ m_maplen r' = m_maplen r.

#[using="Type"] Lemma geom_eq_refl r : geom_eq r r. Proof. repeat split; reflexivity. Qed.
#[using="Type"] Lemma geom_of_data r r' : data_of r' = data_of r -> geom_eq r r'.
Proof. intros H. apply data_of_eq in H. destruct H as (A1 & _ & _ & A4 & A5 & A6 & A7). repeat split; auto. Qed.
#[using="Type"] Lemma get_stride_geom r r' : geom_eq r r' -> get_stride r' = get_stride r.
Proof. intros (A1 & A2 & A3 & A4 & A5). unfold get_stride. rewrite A2, A4, A5. reflexivity. Qed.
#[using="Type"] Lemma slot_start'_geom r r' i : geom_eq r r' -> slot_start' r' i = slot_start' r i.
Proof. intros G. unfold slot_start'. rewrite (get_stride_geom r r' G). destruct G as (-> & _). reflexivity. Qed.
#[using="Type"] Lemma sstart_of_geom r r' i : geom_eq r r' -> sstart_of r' i = sstart_of r i.
Proof. intros G. unfold sstart_of. rewrite (get_stride_geom r r' G). destruct G as (-> & _). reflexivity. Qed.

(* [comment removed for export] *)

Section XFER.
Variables (st st' : mstate) (LB : list block).
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ESL : s_slots st' = s_slots st.
Hypothesis ET : s_tick st' = s_tick st.
Hypothesis EB : c_brk (ctx st') = c_brk (ctx st).
Hypothesis GEO : forall q, is_gm st q -> geom_eq (get_meta_rec st q) (get_meta_rec st' q).
Hypothesis MASK : forall q b, hosts st b q ->
  0 <= m_avail (get_meta_rec st' q) < 2^32 /\ 0 <= m_freed (get_meta_rec st' q) < 2^32
  /\ forall i, 0 <= i ->
       (Z.testbit (m_avail (get_meta_rec st' q)) i = true -> i <= m_last_idx (get_meta_rec st q))
       /\ (Z.testbit (m_freed (get_meta_rec st' q)) i = true -> i <= m_last_idx (get_meta_rec st q)).
Hypothesis NF : forall q b j, hosts st b q -> 0 <= j <= m_last_idx (get_meta_rec st q) ->
  ~ slot_free (get_meta_rec st q) j -> slot_free (get_meta_rec st' q) j ->
  (s_groups st) !! (slot_start' (get_meta_rec st q) j) = None
  /\ Forall (fun blk => blk_slot blk <> slot_start' (get_meta_rec st q) j) LB.

#[using="EG"] Lemma hosts_x b q : hosts st' b q <-> hosts st b q.
Proof. unfold hosts. rewrite EG. tauto. Qed.
#[using="EG"] Lemma is_gm_x q : is_gm st' q <-> is_gm st q.
Proof. unfold is_gm. split; intros [b H]; exists b; apply hosts_x; exact H. Qed.
#[using="EA"] Lemma meta_slot_x q : meta_slot st' q <-> meta_slot st q.
Proof. unfold meta_slot. rewrite EA. tauto. Qed.
#[using="ES"] Lemma get_shadow_x rid : get_shadow st' rid = get_shadow st rid.
Proof. unfold get_shadow. rewrite ES. reflexivity. Qed.
#[using="ER"] Lemma conc_x q : conc st' q = conc st q.
Proof. unfold conc, get_region. rewrite ER. reflexivity. Qed.
#[using="ES"] Lemma hdr_known_x p b1 i1 : hdr_known st p b1 i1 -> hdr_known st' p b1 i1.
Proof. unfold hdr_known. rewrite !get_shadow_x. exact (fun H => H). Qed.

#[using="LB ER ES EA EG ESL GEO MASK NF"] Lemma gmeta_x b g : ci_slots st -> ci_gmeta st -> hosts st b g -> gmeta_ok st' g b.
Proof.
  intros CS CG HB. pose proof (CG b g HB) as GO. pose proof (GEO g (ex_intro _ b HB)) as Gg.
  pose proof Gg as (M1 & M2 & M3 & M4 & M5).
  destruct (MASK g b HB) as (RA & RF & BITS).
  constructor.
  - apply meta_slot_x. exact (go_slot _ _ _ GO).
  - exact RA.
  - exact RF.
  - rewrite M2. exact (go_li _ _ _ GO).
  - rewrite M3. exact (go_freeable _ _ _ GO).
  - rewrite M4, M2, M5. exact (go_sc _ _ _ GO).
  - rewrite M5. exact (go_maplen _ _ _ GO).
  - intros i Hi. rewrite M2. exact (BITS i Hi).
  - rewrite M1. exact (go_mem _ _ _ GO).
  - destruct (go_region _ _ _ GO) as (r & Hr & Kr & S0 & S16 & SP & TOP). exists r.
    rewrite ER, (sstart_of_geom _ _ _ Gg), M2, M5. repeat split; auto; apply TOP; auto.
  - rewrite (get_stride_geom _ _ Gg). exact (go_stride _ _ _ GO).
  - intros ML. rewrite M5 in ML. destruct (go_nest _ _ _ GO ML) as (g1 & i1 & b1 & SL & HB1 & FB & EQB & I1 & NF1 & LT & HK).
    pose proof (GEO g1 (ex_intro _ b1 HB1)) as G1. pose proof G1 as (N1 & N2 & N3 & N4 & N5).
    exists g1, i1, b1. rewrite ESL, (slot_start'_geom _ _ _ G1), N2, N4, M4.
    split; [exact SL|]. split; [apply hosts_x; exact HB1|]. split; [exact FB|]. split; [exact EQB|]. split; [exact I1|].
    split.
    { intros FR'. destruct (NF g1 b1 i1 HB1 I1 NF1 FR') as [NG _]. rewrite <- EQB in NG.
      destruct HB as [ai Hai]. rewrite Hai in NG. discriminate. }
    split; [exact LT|]. apply hdr_known_x. exact HK.
Qed.

#[using="ER ES EG ESL GEO NF"] Lemma blks_x : ci_slots st -> Forall (blk_ok st) LB -> Forall (blk_ok st') LB.
Proof.
  intros CS H. apply Forall_forall. intros blk Hin. pose proof (proj1 (Forall_forall _ _) H blk Hin) as BK.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  pose proof (GEO g (ex_intro _ b HB)) as Gg. pose proof Gg as (M1 & M2 & M3 & M4 & M5).
  constructor.
  - exists g, i, b. rewrite ESL, M2, (get_stride_geom _ _ Gg), get_shadow_x, conc_x.
    split; [exact SL|]. split; [apply hosts_x; exact HB|]. split; [exact FB|]. split; [exact I|]. split.
    + intros FR'. destruct (NF g b i HB I NFR FR') as [_ NB].
      pose proof (proj1 (Forall_forall _ _) NB blk Hin) as NE. apply NE.
      destruct (CS _ _ _ SL) as (_ & E & _). exact E.
    + exists off. split; [exact O0|]. split; [exact OA|]. split; [exact OS|]. split; [exact OK|]. apply hdr_known_x. exact HK.
  - rewrite EG. exact NG.
  - exact SZ.
Qed.

#[using="ER ES EA EG ESL ET EB GEO MASK NF"] Lemma KINV_xfer c c' : KINV st LB c -> ci_links_t st' -> ci_heads_t st' -> ci_homog st' -> kctx st' -> usage_ok st' c' -> KINV st' LB c'.
Proof.
  intros K L H HO KC US.
  pose proof (ki_slts _ _ _ K) as CS. pose proof (ki_gmetas _ _ _ K) as CG.
  constructor; auto.
  - intros b g HB. apply gmeta_x; auto. apply hosts_x. exact HB.
  - intros b gh Hb. rewrite EG in Hb. destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & Hai). exists g. split; [exact Hg|].
    assert (HB : hosts st b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
    destruct (GEO g (ex_intro _ b HB)) as (_ & -> & _). exact Hai.
  - intros b1 b2 g H1 H2. apply (ki_ginj _ _ _ K b1 b2 g); apply hosts_x; auto.
  - intros s g i Hs. rewrite ESL in Hs. destruct (CS s g i Hs) as (GM & E & I).
    pose proof (GEO g GM) as Gg. rewrite (slot_start'_geom _ _ _ Gg). destruct Gg as (_ & -> & _).
    split; [apply is_gm_x; exact GM| auto].
  - intros b g i HB Hi. apply hosts_x in HB. pose proof (GEO g (ex_intro _ b HB)) as Gg.
    rewrite ESL, (slot_start'_geom _ _ _ Gg). destruct Gg as (_ & M2 & _). rewrite M2 in Hi. exact (ki_sltt _ _ _ K b g i HB Hi).
  - intros b gh o Hb Ho. rewrite EG in Hb. rewrite get_shadow_x. exact (ki_unk _ _ _ K b gh o Hb Ho).
  - intros g b i HB Hi. apply hosts_x in HB. pose proof (GEO g (ex_intro _ b HB)) as Gg.
    rewrite get_shadow_x, (sstart_of_geom _ _ _ Gg). destruct Gg as (_ & M2 & _). rewrite M2 in Hi. exact (ki_h0 _ _ _ K g b i HB Hi).
  - apply blks_x; auto. exact (ki_blks _ _ _ K).
  - exact (ki_nodup _ _ _ K).
  - intros rid off Hb. rewrite EB in Hb. rewrite ER. exact (ki_bk _ _ _ K rid off Hb).
  - pose proof (ki_ticks _ _ _ K) as [T1 T2]. split; intros until 0; rewrite ES, ET; [apply T1| apply T2].
Qed.
End XFER.

(* [comment removed for export] *)
Section LINKX.
Variables (st st' : mstate).
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis EL : forall q, m_next (get_meta_rec st' q) = m_next (get_meta_rec st q) /\ m_prev (get_meta_rec st' q) = m_prev (get_meta_rec st q).
Hypothesis EH : forall sc, active st' sc = active st sc.
Hypothesis EF : c_free_meta_head (ctx st') = c_free_meta_head (ctx st).
Hypothesis ED : forall q, m_next (get_meta_rec st q) <> None ->
  m_mem (get_meta_rec st' q) = m_mem (get_meta_rec st q) /\ m_sizeclass (get_meta_rec st' q) = m_sizeclass (get_meta_rec st q).

#[using="EG EL EH EF ED"] Lemma heads_lx : ci_heads_t st -> ci_heads_t st'.
Proof.
  intros [CF CA]. constructor.
  - intros h Hh. rewrite EF in Hh. destruct (CF h Hh) as [N M]. destruct (EL h) as [E1 _]. rewrite E1.
    destruct (ED h N) as [-> _]. auto.
  - intros sc a Ha. rewrite EH in Ha. destruct (CA sc a Ha) as (SC & N & GM & SCa). destruct (EL a) as [E1 _]. rewrite E1.
    destruct (ED a N) as [_ ->]. pose proof (proj2 (is_gm_ext st st' a EG) GM). auto.
Qed.

#[using="EG EL ED"] Lemma homog_lx : ci_links_t st -> ci_homog st -> ci_homog st'.
Proof.
  intros [LN LP LNN LS] HO m nx Hn. destruct (EL m) as [E1 _]. rewrite E1 in Hn. destruct (HO m nx Hn) as [H1 H2].
  assert (Nm : m_next (get_meta_rec st m) <> None) by congruence.
  assert (Nx : m_next (get_meta_rec st nx) <> None).
  { intros E. apply (proj1 (LNN nx)) in E. destruct (LN m nx Hn) as [P _]. congruence. }
  destruct (ED m Nm) as [_ ->]. destruct (ED nx Nx) as [_ ->].
  pose proof (is_gm_ext st st' m EG). pose proof (is_gm_ext st st' nx EG). tauto.
Qed.
End LINKX.

(* [comment removed for export] *)
#[using="Type"] Lemma KINV_xfer_recs st st' LB c c' :
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_areas st' = s_areas st ->
  s_groups st' = s_groups st -> s_slots st' = s_slots st -> s_tick st' = s_tick st -> s_reserved st' = s_reserved st ->
  c_brk (ctx st') = c_brk (ctx st) -> (forall q, get_meta_rec st' q = get_meta_rec st q) ->
  (forall sc, active st' sc = active st sc) -> c_free_meta_head (ctx st') = c_free_meta_head (ctx st) ->
  KINV st LB c -> kctx st' -> usage_ok st' c' -> KINV st' LB c'.
Proof.
  intros ER ES EA EG ESL ET ERS EB EM EH EF K KC US.
  eapply (KINV_xfer st st' LB ER ES EA EG ESL ET EB); try exact K; try exact KC; try exact US.
  - intros q _. rewrite EM. apply geom_eq_refl.
  - intros q b HB. rewrite EM. pose proof (ki_gmetas _ _ _ K b q HB) as GO.
    split; [exact (go_avail _ _ _ GO)|]. split; [exact (go_freed _ _ _ GO)|]. exact (go_bits _ _ _ GO).
  - intros q b j _ _ NFR FR. rewrite EM in FR. tauto.
  - apply (links_ext st st' EA); [| exact (ki_links _ _ _ K)]. intros q. rewrite EM. auto.
  - apply (heads_lx st st' EG); [intros q; rewrite EM; auto | exact EH | exact EF | intros q _; rewrite EM; auto | exact (ki_heads _ _ _ K)].
  - apply (homog_lx st st' EG); [intros q; rewrite EM; auto | intros q _; rewrite EM; auto | exact (ki_links _ _ _ K) | exact (ki_hom _ _ _ K)].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma KINV_xfer_sbl st st' LB c : same_but_links st st' -> KINV st LB c ->
  ci_links_t st' -> ci_heads_t st' -> ci_homog st' -> KINV st' LB c.
Proof.
  intros S K L H HO.
  eapply (KINV_xfer st st' LB (sbl_regions _ _ S) (sbl_shadow _ _ S) (sbl_areas _ _ S) (sbl_groups _ _ S) (sbl_slots _ _ S)
            (sbl_tick _ _ S) (sbl_brk _ _ S)); try exact K; try exact L; try exact H; try exact HO.
  - intros q _. apply geom_of_data. apply (sbl_data _ _ S).
  - intros q b HB. pose proof (ki_gmetas _ _ _ K b q HB) as GO.
    destruct (data_of_fields st st' q (sbl_data _ _ S q)) as (_ & -> & -> & _).
    split; [exact (go_avail _ _ _ GO)|]. split; [exact (go_freed _ _ _ GO)|]. exact (go_bits _ _ _ GO).
  - intros q b j _ _ NFR FR. exfalso. apply NFR. apply (proj1 (slot_free_data _ _ j (sbl_data _ _ S q))). exact FR.
  - pose proof (ki_cx _ _ _ K) as (X1 & X2 & X3 & X4). unfold kctx.
    rewrite (sbl_seq _ _ S), (sbl_secret _ _ S). split; [exact X1|]. split; [intros i; rewrite (sbl_bounces _ _ S); apply X2|].
    split; [intros i; rewrite (sbl_unmap _ _ S); apply X3| exact X4].
  - intros sc Hsc. rewrite (sbl_usage _ _ S). exact (ki_usage _ _ _ K sc Hsc).
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma rec_set_head st h v q : get_meta_rec (set_head h v st) q = get_meta_rec st q.
Proof. destruct h; reflexivity. Qed.
#[using="Type"] Lemma active_set_active_eq st sc v : active (set_active sc v st) sc = v.
Proof.
  unfold active, set_active, upd_ctx, ctx. cbn [s_ctx c_active set_active_map].
  destruct v as [p|]; [apply lookup_insert_eq| apply lookup_delete_eq].
Qed.
#[using="Type"] Lemma active_set_active_ne st sc sc' v : sc' <> sc -> active (set_active sc v st) sc' = active st sc'.
Proof.
  intros NE. unfold active, set_active, upd_ctx, ctx. cbn [s_ctx c_active set_active_map].
  destruct v as [p|]; [rewrite lookup_insert_ne by lia| rewrite lookup_delete_ne by lia]; reflexivity.
Qed.
#[using="Type"] Lemma get_head_set_head st h v : get_head (set_head h v st) h = v.
Proof. destruct h as [sc|]; cbn [get_head set_head]; [apply active_set_active_eq| reflexivity]. Qed.
End PORT.
End WithCeil.


Ltac crush_ptr :=
  repeat (match goal with |- context [aptr_eqb ?x ?y] => destruct (aptr_eqb_spec' x y); try subst end);
  cbn [m_next m_prev m_set_prev m_set_next]; try reflexivity; try congruence.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma fm_single_next st h g q :
  m_next (get_meta_rec (fm_single st h g) q) = if aptr_eqb q g then Some g else m_next (get_meta_rec st q).
Proof. unfold fm_single. rewrite !rec_set_head, !rec_upd. crush_ptr. Qed.
#[using="Type"] Lemma fm_single_prev st h g q :
  m_prev (get_meta_rec (fm_single st h g) q) = if aptr_eqb q g then Some g else m_prev (get_meta_rec st q).
Proof. unfold fm_single. rewrite !rec_set_head, !rec_upd. crush_ptr. Qed.
#[using="Type"] Lemma fm_link_next st g hd pv q : m_prev (get_meta_rec st hd) = Some pv ->
  m_next (get_meta_rec (fm_link st g hd) q) = if aptr_eqb q pv then Some g else if aptr_eqb q g then Some hd else m_next (get_meta_rec st q).
Proof. intros PV. unfold fm_link. rewrite PV. rewrite !rec_upd. crush_ptr. Qed.
#[using="Type"] Lemma fm_link_prev st g hd pv q : m_prev (get_meta_rec st hd) = Some pv ->
  m_prev (get_meta_rec (fm_link st g hd) q) = if aptr_eqb q hd then Some g else if aptr_eqb q g then Some pv else m_prev (get_meta_rec st q).
Proof. intros PV. unfold fm_link. rewrite PV. rewrite !rec_upd. crush_ptr. Qed.

#[using="Type"] Lemma queue_ctx_some st h g hd : get_head st h = Some hd -> ctx (queue_st h g st) = ctx st.
Proof. intros H. unfold queue_st. rewrite H. unfold fm_link. destruct (m_prev (get_meta_rec st hd)); reflexivity. Qed.
#[using="Type"] Lemma queue_head_none st h g : get_head st h = None -> get_head (queue_st h g st) h = Some g.
Proof. intros H. unfold queue_st. rewrite H. unfold fm_single. apply get_head_set_head. Qed.
#[using="Type"] Lemma queue_active_none st h g sc : get_head st h = None -> h <> LActive sc -> active (queue_st h g st) sc = active st sc.
Proof.
  intros H NE. unfold queue_st. rewrite H. unfold fm_single. destruct h as [sc0|]; cbn [set_head].
  - rewrite active_set_active_ne by congruence. reflexivity.
  - reflexivity.
Qed.
#[using="Type"] Lemma queue_fmh_none st sc g : get_head st (LActive sc) = None ->
  c_free_meta_head (ctx (queue_st (LActive sc) g st)) = c_free_meta_head (ctx st).
Proof. intros H. unfold queue_st. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma dequeue_next_self st h g q : m_next (get_meta_rec st g) = Some g ->
  m_next (get_meta_rec (dequeue h g st) q) = if aptr_eqb q g then None else m_next (get_meta_rec st q).
Proof.
  intros NX. unfold dequeue. lazy zeta. rewrite NX. cbn [optr_eqb negb]. rewrite aptr_eqb_refl. cbn [negb].
  rewrite !rec_upd, !rec_set_head. crush_ptr.
Qed.
#[using="Type"] Lemma dequeue_prev_self st h g q : m_next (get_meta_rec st g) = Some g ->
  m_prev (get_meta_rec (dequeue h g st) q) = if aptr_eqb q g then None else m_prev (get_meta_rec st q).
Proof.
  intros NX. unfold dequeue. lazy zeta. rewrite NX. cbn [optr_eqb negb]. rewrite aptr_eqb_refl. cbn [negb].
  rewrite !rec_upd, !rec_set_head. crush_ptr.
Qed.
#[using="Type"] Lemma dequeue_next st h g nx pv q : m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv -> nx <> g ->
  m_next (get_meta_rec (dequeue h g st) q) = if aptr_eqb q g then None else if aptr_eqb q pv then Some nx else m_next (get_meta_rec st q).
Proof.
  intros NX PV NE. unfold dequeue. lazy zeta. rewrite NX, PV. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NE). cbn [negb].
  rewrite rec_upd.
  match goal with |- context [if ?c then set_head ?hh ?v ?s else _] => destruct c end; rewrite ?rec_set_head, !rec_upd; crush_ptr.
Qed.
#[using="Type"] Lemma dequeue_prev st h g nx pv q : m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv -> nx <> g ->
  m_prev (get_meta_rec (dequeue h g st) q) = if aptr_eqb q g then None else if aptr_eqb q nx then Some pv else m_prev (get_meta_rec st q).
Proof.
  intros NX PV NE. unfold dequeue. lazy zeta. rewrite NX, PV. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NE). cbn [negb].
  rewrite rec_upd.
  match goal with |- context [if ?c then set_head ?hh ?v ?s else _] => destruct c end; rewrite ?rec_set_head, !rec_upd; crush_ptr.
Qed.

#[using="Type"] Lemma dequeue_active st sc g nx pv sc' : m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv ->
  active (dequeue (LActive sc) g st) sc' =
    if sc' =? sc then (if aptr_eqb nx g then None else if optr_eqb (active st sc) (Some g) then Some nx else active st sc)
    else active st sc'.
Proof.
  intros NX PV. unfold dequeue. lazy zeta. rewrite NX, PV. cbn [optr_eqb negb].
  change (active (upd_meta g ?f ?s) sc') with (active s sc').
  destruct (aptr_eqb_spec' nx g).
  - cbn [negb set_head]. destruct (Z.eqb_spec sc' sc) as [->|NE]; [apply active_set_active_eq| apply active_set_active_ne; exact NE].
  - cbn [negb get_head set_head].
    change (active (upd_meta nx ?f1 (upd_meta pv ?f2 st)) sc) with (active st sc).
    destruct (active st sc) as [a|] eqn:HA; cbn [optr_eqb].
    + destruct (aptr_eqb_spec' a g).
      * destruct (Z.eqb_spec sc' sc) as [->|NE]; [apply active_set_active_eq| rewrite active_set_active_ne by exact NE; reflexivity].
      * change (active (upd_meta nx ?f1 (upd_meta pv ?f2 st)) sc') with (active st sc'). destruct (Z.eqb_spec sc' sc) as [->|NE]; [exact HA| reflexivity].
    + change (active (upd_meta nx ?f1 (upd_meta pv ?f2 st)) sc') with (active st sc'). destruct (Z.eqb_spec sc' sc) as [->|NE]; [exact HA| reflexivity].
Qed.

#[using="Type"] Lemma dequeue_fmh st sc g : c_free_meta_head (ctx (dequeue (LActive sc) g st)) = c_free_meta_head (ctx st).
Proof.
  unfold dequeue. lazy zeta.
  destruct (negb (optr_eqb (m_next (get_meta_rec st g)) (Some g))); [| reflexivity].
  destruct (m_prev (get_meta_rec st g)); destruct (m_next (get_meta_rec st g));
    match goal with |- context [if ?c then set_head _ _ _ else _] => destruct c end; reflexivity.
Qed.

#[using="Type"] Lemma dequeue_shape : forall st g sc nx pv,
  m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv ->
  let st' := dequeue (LActive sc) g st in
  (forall x, data_of (get_meta_rec st' x) = data_of (get_meta_rec st x))
  /\ m_next (get_meta_rec st' g) = None /\ m_prev (get_meta_rec st' g) = None
  /\ s_regions st' = s_regions st /\ s_shadow st' = s_shadow st /\ s_areas st' = s_areas st
  /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st /\ s_tick st' = s_tick st /\ s_reserved st' = s_reserved st
  /\ active st' sc = (if aptr_eqb nx g then None else if optr_eqb (active st sc) (Some g) then Some nx else active st sc)
  /\ (forall sc', sc' <> sc -> active st' sc' = active st sc')
  /\ c_free_meta_head (ctx st') = c_free_meta_head (ctx st)
  /\ (forall sc', usage st' sc' = usage st sc') /\ (forall j, bounces st' j = bounces st j) /\ (forall j, unmap_seq st' j = unmap_seq st j)
  /\ c_seq (ctx st') = c_seq (ctx st) /\ c_brk (ctx st') = c_brk (ctx st) /\ c_secret (ctx st') = c_secret (ctx st).
Proof.
  intros st g sc nx pv NX PV. pose proof (sbl_dequeue st (LActive sc) g) as S. cbn zeta.
  split; [exact (sbl_data _ _ S)|].
  split. { rewrite dequeue_mid, rec_upd, aptr_eqb_refl. reflexivity. }
  split. { rewrite dequeue_mid, rec_upd, aptr_eqb_refl. reflexivity. }
  split; [exact (sbl_regions _ _ S)|]. split; [exact (sbl_shadow _ _ S)|]. split; [exact (sbl_areas _ _ S)|].
  split; [exact (sbl_groups _ _ S)|]. split; [exact (sbl_slots _ _ S)|]. split; [exact (sbl_tick _ _ S)|]. split; [exact (sbl_reserved _ _ S)|].
  split. { rewrite (dequeue_active st sc g nx pv sc NX PV), Z.eqb_refl. reflexivity. }
  split. { intros sc' NE. rewrite (dequeue_active st sc g nx pv sc' NX PV). destruct (Z.eqb_spec sc' sc); [lia| reflexivity]. }
  split; [apply dequeue_fmh|].
  split; [exact (sbl_usage _ _ S)|]. split; [exact (sbl_bounces _ _ S)|]. split; [exact (sbl_unmap _ _ S)|].
  split; [exact (sbl_seq _ _ S)|]. split; [exact (sbl_brk _ _ S)| exact (sbl_secret _ _ S)].
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma KINV_set_usage : forall st LB c sc v,
  KINV st LB c -> c <= sc -> KINV (set_usage sc v st) LB (sc + 1).
Proof.
  intros st LB c sc v K Hc.
  apply (KINV_xfer_recs st (set_usage sc v st) LB c); try reflexivity; try exact K.
  - exact (ki_cx _ _ _ K).
  - intros sc' Hsc'. unfold usage, set_usage, upd_ctx, ctx. cbn [s_ctx c_usage set_usage_map].
    rewrite lookup_insert_ne by lia. exact (ki_usage _ _ _ K sc' ltac:(lia)).
Qed.

#[using="Type"] Lemma KINV_seq : forall st LB c sc, KINV st LB c -> KINV (record_seq sc (step_seq st)) LB c.
Proof.
  intros st LB c sc K. pose proof (ki_cx _ _ _ K) as (X1 & X2 & X3 & X4).
  apply (KINV_xfer_recs st _ LB c); try exact K;
    try (unfold record_seq, step_seq; destruct (c_seq (ctx st) =? 255); destruct (sc_in_seq_range sc); reflexivity).
  - unfold kctx, bounces, unmap_seq in *. unfold record_seq, step_seq, upd_ctx, ctx in *.
    destruct (Z.eqb_spec (c_seq (s_ctx st)) 255) as [E|NE]; destruct (sc_in_seq_range sc);
      cbn [s_ctx c_seq c_bounces c_unmap_seq c_secret set_seq set_unmap_seq_map]; unfold ctx; cbn [s_ctx c_seq c_bounces c_unmap_seq c_secret set_seq set_unmap_seq_map].
    all: split; [lia|]; split; [exact X2|]; split; [| exact X4].
    all: intros i.
    + destruct (Z.eq_dec i (sc - 7)) as [->|NE']; [rewrite lookup_insert_eq; cbn; lia| rewrite lookup_insert_ne by congruence; rewrite lookup_empty; cbn; lia].
    + rewrite lookup_empty; cbn; lia.
    + destruct (Z.eq_dec i (sc - 7)) as [->|NE']; [rewrite lookup_insert_eq; cbn; lia| rewrite lookup_insert_ne by congruence; apply X3].
    + apply X3.
  - intros sc0 Hsc0. unfold usage. replace (c_usage (ctx (record_seq sc (step_seq st)))) with (c_usage (ctx st)).
    + exact (ki_usage _ _ _ K sc0 Hsc0).
    + unfold record_seq, step_seq; destruct (c_seq (ctx st) =? 255); destruct (sc_in_seq_range sc); reflexivity.
Qed.

#[using="Type"] Lemma KINV_fg_usage st LB c g p i : KINV st LB c -> LPRE st LB c g p i -> KINV (fg_usage_st st g) LB (m_sizeclass (get_meta_rec st g) + 1).
Proof.
  intros K L. unfold fg_usage_st. destruct (_ <? 48).
  - apply (KINV_set_usage st LB c); [exact K| exact (lp_class _ _ _ _ _ _ L)].
  - eapply KINV_mono; [exact K|]. pose proof (lp_class _ _ _ _ _ _ L). lia.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma KINV_aor : forall st LB c g p i,
  KINV st LB c -> LPRE st LB c g p i -> KINV (aor_st st g i) LB c.
Proof.
  intros st LB c g p i K L. pose proof (lpre_gmeta _ _ _ _ _ _ K L) as GO.
  pose proof (lp_i _ _ _ _ _ _ L) as Hi. pose proof (go_li _ _ _ GO) as LI.
  assert (RQ : forall q, get_meta_rec (aor_st st g i) q =
            if aptr_eqb q g then m_set_freed (Z.lor (m_freed (get_meta_rec st g)) (bit i)) (get_meta_rec st g) else get_meta_rec st q).
  { intros q. unfold aor_st. rewrite rec_upd. reflexivity. }
  apply (KINV_xfer st (aor_st st g i) LB) with (c := c); try reflexivity.
  - intros q _. rewrite RQ. case_ptr q g; [| apply geom_eq_refl]. repeat split; reflexivity.
  - intros q b HB. pose proof (ki_gmetas _ _ _ K b q HB) as GQ. rewrite RQ. case_ptr q g.
    + cbn [m_avail m_freed m_set_freed].
      split; [exact (go_avail _ _ _ GQ)|].
      split; [apply (lor_range 32); [exact (go_freed _ _ _ GQ)| apply bit_range; lia]|].
      intros k Hk. split; [intros T; exact (proj1 (go_bits _ _ _ GQ k Hk) T)|].
      rewrite Z.lor_spec, testbit_bit by lia. intros T. apply orb_true_iff in T.
      destruct T as [T|T]; [exact (proj2 (go_bits _ _ _ GQ k Hk) T)| apply Z.eqb_eq in T; lia].
    + exact (conj (go_avail _ _ _ GQ) (conj (go_freed _ _ _ GQ) (go_bits _ _ _ GQ))).
  - intros q b j HB Hj NFR FR. rewrite RQ in FR. case_ptr q g; [| tauto].
    assert (b = p) as -> by (exact (ki_ginj _ _ _ K b p g HB (lp_hosts _ _ _ _ _ _ L))).
    unfold slot_free in NFR, FR. cbn [m_freed m_avail m_set_freed] in FR. rewrite Z.lor_spec, testbit_bit in FR by lia.
    assert (j = i) as ->.
    { destruct (Z.eqb_spec i j); [lia|]. rewrite orb_false_r in FR. tauto. }
    split; [exact (lp_nogroup _ _ _ _ _ _ L)| exact (lp_noblock _ _ _ _ _ _ L)].
  - exact K.
  - apply (links_ext st (aor_st st g i)); [reflexivity | intros q; rewrite RQ; case_ptr q g; split; reflexivity | exact (ki_links _ _ _ K)].
  - apply (heads_lx st (aor_st st g i)); [reflexivity | intros q; rewrite RQ; case_ptr q g; split; reflexivity | intros sc; reflexivity | reflexivity | intros q _; rewrite RQ; case_ptr q g; split; reflexivity | exact (ki_heads _ _ _ K)].
  - apply (homog_lx st (aor_st st g i)); [reflexivity | intros q; rewrite RQ; case_ptr q g; split; reflexivity | intros q _; rewrite RQ; case_ptr q g; split; reflexivity | exact (ki_links _ _ _ K) | exact (ki_hom _ _ _ K)].
  - exact (ki_cx _ _ _ K).
  - exact (ki_usage _ _ _ K).
Qed.

#[using="Type"] Lemma KINV_act : forall st LB c a act,
  KINV st LB c -> is_gm st a -> m_avail (get_meta_rec st a) = 0 -> 0 <= act ->
  KINV (act_st st a act) LB c.
Proof.
  intros st LB c a act K GM AV Hact. destruct GM as [b HB]. pose proof (ki_gmetas _ _ _ K b a HB) as GO.
  assert (RQ : forall q, get_meta_rec (act_st st a act) q =
            if aptr_eqb q a then m_set_avail (Z.land (m_freed (get_meta_rec st a)) act) (m_set_freed (Z.ldiff (m_freed (get_meta_rec st a)) act) (get_meta_rec st a)) else get_meta_rec st q).
  { intros q. unfold act_st. rewrite rec_upd. reflexivity. }
  apply (KINV_xfer st (act_st st a act) LB) with (c := c); try reflexivity.
  - intros q _. rewrite RQ. case_ptr q a; [| apply geom_eq_refl]. repeat split; reflexivity.
  - intros q b' HB'. pose proof (ki_gmetas _ _ _ K b' q HB') as GQ. rewrite RQ. case_ptr q a.
    + cbn [m_avail m_freed m_set_freed m_set_avail].
      split; [apply (land_range 32); [exact (go_freed _ _ _ GQ)| exact Hact]|].
      split; [apply (ldiff_range 32); exact (go_freed _ _ _ GQ)|].
      intros k Hk. rewrite Z.land_spec, Z.ldiff_spec.
      split; intros T; apply andb_true_iff in T; destruct T as [T _]; exact (proj2 (go_bits _ _ _ GQ k Hk) T).
    + exact (conj (go_avail _ _ _ GQ) (conj (go_freed _ _ _ GQ) (go_bits _ _ _ GQ))).
  - intros q b' j HB' Hj NFR FR. exfalso. apply NFR. rewrite RQ in FR. case_ptr q a; [| exact FR].
    unfold slot_free in FR |- *. cbn [m_avail m_freed m_set_freed m_set_avail] in FR. rewrite Z.land_spec, Z.ldiff_spec in FR.
    left. destruct FR as [T|T]; apply andb_true_iff in T; tauto.
  - exact K.
  - apply (links_ext st (act_st st a act)); [reflexivity | intros q; rewrite RQ; case_ptr q a; split; reflexivity | exact (ki_links _ _ _ K)].
  - apply (heads_lx st (act_st st a act)); [reflexivity | intros q; rewrite RQ; case_ptr q a; split; reflexivity | intros sc; reflexivity | reflexivity | intros q _; rewrite RQ; case_ptr q a; split; reflexivity | exact (ki_heads _ _ _ K)].
  - apply (homog_lx st (act_st st a act)); [reflexivity | intros q; rewrite RQ; case_ptr q a; split; reflexivity | intros q _; rewrite RQ; case_ptr q a; split; reflexivity | exact (ki_links _ _ _ K) | exact (ki_hom _ _ _ K)].
  - exact (ki_cx _ _ _ K).
  - exact (ki_usage _ _ _ K).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hkind (st : mstate) (h : lhead) (x : aptr) : Prop :=
  match h with
  | LActive sc => is_gm st x /\ m_sizeclass (get_meta_rec st x) = sc
  | LFree => ~ is_gm st x
  end.

#[using="Type"] Lemma free_head_not_gm st LB c h : KINV st LB c -> c_free_meta_head (ctx st) = Some h -> ~ is_gm st h.
Proof. intros K H. exact (proj1 (proj2 (proj2 (kinv_free_head st LB c h K H)))). Qed.

#[using="Type"] Lemma KINV_queue_gen st LB c g h :
  KINV st LB c -> meta_slot st g ->
  m_next (get_meta_rec st g) = None -> m_prev (get_meta_rec st g) = None ->
  match h with
  | LActive sc => is_gm st g /\ m_sizeclass (get_meta_rec st g) = sc /\ 0 <= sc < 48
  | LFree => ~ is_gm st g /\ m_mem (get_meta_rec st g) = None
  end ->
  KINV (queue_st h g st) LB c.
Proof.
  intros K MSg N0 P0 HH.
  pose proof (ki_links _ _ _ K) as L. pose proof L as [LN LP LNN LS].
  pose proof (ki_heads _ _ _ K) as CH. pose proof CH as [CF CA]. pose proof (ki_hom _ _ _ K) as HO.
  pose proof (sbl_queue st h g) as S. set (st' := queue_st h g st) in *.
  assert (GK : hkind st h g) by (destruct h; cbn; tauto).
  assert (EGM : forall x, is_gm st' x <-> is_gm st x) by (intros x; apply is_gm_ext; exact (sbl_groups _ _ S)).
  assert (ESC : forall x, m_sizeclass (get_meta_rec st' x) = m_sizeclass (get_meta_rec st x)).
  { intros x. destruct (data_of_fields st st' x (sbl_data _ _ S x)) as (_ & _ & _ & _ & _ & E & _). exact E. }
  assert (EMM : forall x, m_mem (get_meta_rec st' x) = m_mem (get_meta_rec st x)).
  { intros x. destruct (data_of_fields st st' x (sbl_data _ _ S x)) as (E & _). exact E. }
  assert (MSx : forall x, meta_slot st x -> meta_slot st' x) by (intros x; apply (meta_slot_sbl st st' x S)).
  (* [comment removed for export] *)
  assert (HD : forall hd, get_head st h = Some hd ->
             m_next (get_meta_rec st hd) <> None /\ hd <> g /\ hkind st h hd /\
             exists pv, m_prev (get_meta_rec st hd) = Some pv /\ pv <> g /\ m_next (get_meta_rec st pv) = Some hd /\ hkind st h pv).
  { intros hd Hhd.
    assert (N : m_next (get_meta_rec st hd) <> None /\ hkind st h hd).
    { destruct h as [sc|]; cbn in Hhd |- *.
      - destruct (CA _ _ Hhd) as (_ & N & GM & SC). auto.
      - split; [exact (proj1 (CF _ Hhd))| exact (free_head_not_gm st LB c hd K Hhd)]. }
    destruct N as [N HK]. split; [exact N|]. split; [congruence|]. split; [exact HK|].
    destruct (m_prev (get_meta_rec st hd)) as [pv|] eqn:PV; [| exfalso; apply N; apply (proj2 (LNN hd)); exact PV].
    exists pv. destruct (LP hd pv PV) as [NP _]. split; [reflexivity|]. split; [congruence|]. split; [exact NP|].
    destruct (HO pv hd NP) as [G1 G2]. destruct h as [sc|]; cbn in HK |- *.
    - destruct HK as [GMh SCh]. assert (GMp : is_gm st pv) by tauto. split; [exact GMp|]. rewrite <- (G2 GMp). exact SCh.
    - tauto. }
  apply (KINV_xfer_sbl st st' LB c S K).
  - (* [comment removed for export] *)
    destruct (get_head st h) as [hd|] eqn:Hhd.
    + destruct (HD hd eq_refl) as (Nhd & NEhd & HKhd & pv & PV & NEpv & Npv & HKpv).
      assert (FN : forall q, m_next (get_meta_rec st' q) = if aptr_eqb q pv then Some g else if aptr_eqb q g then Some hd else m_next (get_meta_rec st q)).
      { intros q. unfold st', queue_st. rewrite Hhd. apply fm_link_next. exact PV. }
      assert (FP : forall q, m_prev (get_meta_rec st' q) = if aptr_eqb q hd then Some g else if aptr_eqb q g then Some pv else m_prev (get_meta_rec st q)).
      { intros q. unfold st', queue_st. rewrite Hhd. apply fm_link_prev. exact PV. }
      constructor.
      * intros m nx Hn. rewrite FN in Hn. rewrite FP.
        destruct (aptr_eqb_spec' m pv) as [->|NEmp]; [| destruct (aptr_eqb_spec' m g) as [->|NEmg]].
        -- assert (nx = g) as -> by congruence. rewrite (aptr_eqb_neq g hd) by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; exact MSg].
        -- assert (nx = hd) as -> by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; apply LS; exact Nhd].
        -- destruct (LN m nx Hn) as [P1 S1].
           destruct (aptr_eqb_spec' nx hd); [subst; exfalso; rewrite PV in P1; assert (m = pv) by congruence; tauto|].
           destruct (aptr_eqb_spec' nx g); [subst; rewrite P0 in P1; discriminate|].
           split; [exact P1| apply MSx; exact S1].
      * intros m pv0 Hp. rewrite FP in Hp. rewrite FN.
        destruct (aptr_eqb_spec' m hd) as [->|NEmh]; [| destruct (aptr_eqb_spec' m g) as [->|NEmg]].
        -- assert (pv0 = g) as -> by congruence. rewrite (aptr_eqb_neq g pv) by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; exact MSg].
        -- assert (pv0 = pv) as -> by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; apply LS; congruence].
        -- destruct (LP m pv0 Hp) as [N1 S1].
           destruct (aptr_eqb_spec' pv0 pv); [subst; exfalso; rewrite Npv in N1; assert (m = hd) by congruence; tauto|].
           destruct (aptr_eqb_spec' pv0 g); [subst; rewrite N0 in N1; discriminate|].
           split; [exact N1| apply MSx; exact S1].
      * intros m. rewrite FN, FP.
        destruct (aptr_eqb_spec' m pv); [subst| destruct (aptr_eqb_spec' m g); [subst|]].
        -- destruct (aptr_eqb_spec' pv hd); [split; discriminate|]. rewrite (aptr_eqb_neq pv g) by congruence.
           assert (m_prev (get_meta_rec st pv) <> None) by (intros E; apply (proj2 (LNN pv)) in E; congruence).
           split; [discriminate| intros E; exfalso; exact (H E)].
        -- rewrite (aptr_eqb_neq g hd) by congruence. split; discriminate.
        -- destruct (aptr_eqb_spec' m hd); [subst; split; [intros E; exfalso; exact (Nhd E)| discriminate]| apply LNN].
      * intros m Hn. rewrite FN in Hn. apply MSx.
        destruct (aptr_eqb_spec' m pv); [subst; apply LS; congruence|]. destruct (aptr_eqb_spec' m g); [subst; exact MSg| apply LS; exact Hn].
    + assert (FN : forall q, m_next (get_meta_rec st' q) = if aptr_eqb q g then Some g else m_next (get_meta_rec st q)).
      { intros q. unfold st', queue_st. rewrite Hhd. apply fm_single_next. }
      assert (FP : forall q, m_prev (get_meta_rec st' q) = if aptr_eqb q g then Some g else m_prev (get_meta_rec st q)).
      { intros q. unfold st', queue_st. rewrite Hhd. apply fm_single_prev. }
      constructor.
      * intros m nx Hn. rewrite FN in Hn. rewrite FP. destruct (aptr_eqb_spec' m g) as [->|NEmg].
        -- assert (nx = g) as -> by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; exact MSg].
        -- destruct (LN m nx Hn) as [P1 S1]. destruct (aptr_eqb_spec' nx g); [subst; rewrite P0 in P1; discriminate|]. split; [exact P1| apply MSx; exact S1].
      * intros m pv0 Hp. rewrite FP in Hp. rewrite FN. destruct (aptr_eqb_spec' m g) as [->|NEmg].
        -- assert (pv0 = g) as -> by congruence. rewrite aptr_eqb_refl. split; [reflexivity| apply MSx; exact MSg].
        -- destruct (LP m pv0 Hp) as [N1 S1]. destruct (aptr_eqb_spec' pv0 g); [subst; rewrite N0 in N1; discriminate|]. split; [exact N1| apply MSx; exact S1].
      * intros m. rewrite FN, FP. destruct (aptr_eqb_spec' m g); [split; discriminate| apply LNN].
      * intros m Hn. rewrite FN in Hn. apply MSx. destruct (aptr_eqb_spec' m g); [subst; exact MSg| apply LS; exact Hn].
  - (* [comment removed for export] *)
    assert (NXT : forall x, m_next (get_meta_rec st x) <> None -> m_next (get_meta_rec st' x) <> None).
    { intros x Hx. unfold st', queue_st. destruct (get_head st h) as [hd|] eqn:Hhd.
      - destruct (HD hd eq_refl) as (_ & _ & _ & pv & PV & _). rewrite (fm_link_next st g hd pv x PV).
        destruct (aptr_eqb x pv); [discriminate|]. destruct (aptr_eqb x g); [discriminate| exact Hx].
      - rewrite fm_single_next. destruct (aptr_eqb x g); [discriminate| exact Hx]. }
    assert (NXg : m_next (get_meta_rec st' g) <> None).
    { unfold st', queue_st. destruct (get_head st h) as [hd|] eqn:Hhd.
      - destruct (HD hd eq_refl) as (_ & _ & _ & pv & PV & NEpv & _). rewrite (fm_link_next st g hd pv g PV).
        rewrite (aptr_eqb_neq g pv) by congruence. rewrite aptr_eqb_refl. discriminate.
      - rewrite fm_single_next, aptr_eqb_refl. discriminate. }
    constructor.
    + intros h0 Hh0.
      destruct (get_head st h) as [hd|] eqn:Hhd.
      * unfold st' in Hh0. rewrite (queue_ctx_some st h g hd Hhd) in Hh0. destruct (CF h0 Hh0) as [N M]. rewrite EMM. split; [apply NXT; exact N| exact M].
      * destruct h as [sc|].
        -- unfold st' in Hh0. rewrite (queue_fmh_none st sc g Hhd) in Hh0. destruct (CF h0 Hh0) as [N M]. rewrite EMM. split; [apply NXT; exact N| exact M].
        -- pose proof (queue_head_none st LFree g Hhd) as E. cbn [get_head] in E. fold st' in E. rewrite E in Hh0. assert (h0 = g) as -> by congruence.
           rewrite EMM. split; [exact NXg| exact (proj2 HH)].
    + intros sc a Ha.
      assert (OLD : active st sc = Some a -> 0 <= sc < 48 /\ m_next (get_meta_rec st' a) <> None /\ is_gm st' a /\ m_sizeclass (get_meta_rec st' a) = sc).
      { intros Ho. destruct (CA sc a Ho) as (R & N & GM & SC). rewrite ESC. split; [exact R|]. split; [apply NXT; exact N|]. split; [apply EGM; exact GM| exact SC]. }
      destruct (get_head st h) as [hd|] eqn:Hhd.
      * apply OLD. unfold st' in Ha. unfold active in Ha |- *. rewrite (queue_ctx_some st h g hd Hhd) in Ha. exact Ha.
      * destruct h as [sc0|].
        -- destruct (Z.eq_dec sc sc0) as [->|NE].
           ++ pose proof (queue_head_none st (LActive sc0) g Hhd) as E. cbn [get_head] in E. fold st' in E. rewrite E in Ha. assert (a = g) as -> by congruence.
              destruct HH as (GM & SC & R). rewrite ESC. split; [exact R|]. split; [exact NXg|]. split; [apply EGM; exact GM| exact SC].
           ++ apply OLD. unfold st' in Ha. rewrite (queue_active_none st (LActive sc0) g sc Hhd) in Ha by congruence. exact Ha.
        -- apply OLD. unfold st' in Ha. rewrite (queue_active_none st LFree g sc Hhd) in Ha by congruence. exact Ha.
  - (* [comment removed for export] *)
    assert (HKx : forall x y, hkind st h x -> hkind st h y -> (is_gm st x <-> is_gm st y) /\ (is_gm st x -> m_sizeclass (get_meta_rec st y) = m_sizeclass (get_meta_rec st x))).
    { intros x y Hx Hy. destruct h as [sc|]; cbn in Hx, Hy; [| tauto]. destruct Hx as [Gx Sx], Hy as [Gy Sy]. split; [tauto| intros _; congruence]. }
    intros m nx Hn. rewrite !EGM, !ESC.
    destruct (get_head st h) as [hd|] eqn:Hhd.
    + destruct (HD hd eq_refl) as (Nhd & NEhd & HKhd & pv & PV & NEpv & Npv & HKpv).
      unfold st', queue_st in Hn. rewrite Hhd, (fm_link_next st g hd pv m PV) in Hn.
      destruct (aptr_eqb_spec' m pv) as [->|NEmp]; [assert (nx = g) as -> by congruence; apply HKx; auto|].
      destruct (aptr_eqb_spec' m g) as [->|NEmg]; [assert (nx = hd) as -> by congruence; apply HKx; auto|].
      exact (HO m nx Hn).
    + unfold st', queue_st in Hn. rewrite Hhd, fm_single_next in Hn.
      destruct (aptr_eqb_spec' m g) as [->|NEmg]; [assert (nx = g) as -> by congruence; split; [tauto| reflexivity]|].
      exact (HO m nx Hn).
Qed.

#[using="Type"] Lemma KINV_queue : forall st LB c g p sc,
  KINV st LB c -> hosts st p g -> sc = m_sizeclass (get_meta_rec st g) -> 0 <= sc < 48 ->
  m_next (get_meta_rec st g) = None -> m_prev (get_meta_rec st g) = None ->
  active st sc <> Some g ->
  KINV (queue_st (LActive sc) g st) LB c.
Proof.
  intros st LB c g p sc K HB SC R N0 P0 _.
  apply (KINV_queue_gen st LB c g (LActive sc) K (go_slot _ _ _ (ki_gmetas _ _ _ K p g HB)) N0 P0).
  split; [exists p; exact HB|]. split; [symmetry; exact SC| exact R].
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma KINV_dequeue : forall st LB c g p sc nx,
  KINV st LB c -> hosts st p g -> sc = m_sizeclass (get_meta_rec st g) ->
  m_next (get_meta_rec st g) = Some nx ->
  KINV (dequeue (LActive sc) g st) LB c.
Proof.
  intros st LB c g p sc nx K HB SC NX.
  pose proof (ki_links _ _ _ K) as L. pose proof L as [LN LP LNN LS].
  pose proof (ki_heads _ _ _ K) as CH. pose proof CH as [CF CA]. pose proof (ki_hom _ _ _ K) as HO.
  pose proof (ki_gmetas _ _ _ K p g HB) as GO. pose proof (go_mem _ _ _ GO) as MEM.
  assert (GMg : is_gm st g) by (exists p; exact HB).
  pose proof (sbl_dequeue st (LActive sc) g) as S. set (st' := dequeue (LActive sc) g st) in *.
  assert (EGM : forall x, is_gm st' x <-> is_gm st x) by (intros x; apply is_gm_ext; exact (sbl_groups _ _ S)).
  assert (ESC : forall x, m_sizeclass (get_meta_rec st' x) = m_sizeclass (get_meta_rec st x)).
  { intros x. destruct (data_of_fields st st' x (sbl_data _ _ S x)) as (_ & _ & _ & _ & _ & E & _). exact E. }
  assert (EMM : forall x, m_mem (get_meta_rec st' x) = m_mem (get_meta_rec st x)).
  { intros x. destruct (data_of_fields st st' x (sbl_data _ _ S x)) as (E & _). exact E. }
  assert (MSx : forall x, meta_slot st x -> meta_slot st' x) by (intros x; apply (meta_slot_sbl st st' x S)).
  destruct (LN g nx NX) as [Pnx Snx].
  destruct (m_prev (get_meta_rec st g)) as [pv|] eqn:PV; [| apply (proj2 (LNN g)) in PV; congruence].
  destruct (LP g pv PV) as [Npv Spv].
  pose proof (dequeue_fmh st sc g) as EF. fold st' in EF.
  pose proof (fun sc' => dequeue_active st sc g nx pv sc' NX PV) as EH. fold st' in EH.
  (* [comment removed for export] *)
  assert (NEfree : forall h0, c_free_meta_head (ctx st) = Some h0 -> h0 <> g).
  { intros h0 Hh0 ->. destruct (CF g Hh0) as [_ M]. congruence. }
  destruct (aptr_eqb_spec' nx g) as [Enx|NEnx].
  - (* [comment removed for export] *)
    subst nx. assert (pv = g) as -> by congruence.
    assert (FN : forall q, m_next (get_meta_rec st' q) = if aptr_eqb q g then None else m_next (get_meta_rec st q)).
    { intros q. unfold st'. apply dequeue_next_self. exact NX. }
    assert (FP : forall q, m_prev (get_meta_rec st' q) = if aptr_eqb q g then None else m_prev (get_meta_rec st q)).
    { intros q. unfold st'. apply dequeue_prev_self. exact NX. }
    assert (NXo : forall m x, m_next (get_meta_rec st m) = Some x -> m <> g -> x <> g).
    { intros m x Hm NE ->. destruct (LN m g Hm) as [P1 _]. congruence. }
    assert (PVo : forall m x, m_prev (get_meta_rec st m) = Some x -> m <> g -> x <> g).
    { intros m x Hm NE ->. destruct (LP m g Hm) as [P1 _]. congruence. }
    apply (KINV_xfer_sbl st st' LB c S K).
    + constructor.
      * intros m x Hn. rewrite FN in Hn. rewrite FP. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
        rewrite (aptr_eqb_neq x g) by (exact (NXo m x Hn NEmg)). destruct (LN m x Hn) as [P1 S1]. split; [exact P1| apply MSx; exact S1].
      * intros m x Hp. rewrite FP in Hp. rewrite FN. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
        rewrite (aptr_eqb_neq x g) by (exact (PVo m x Hp NEmg)). destruct (LP m x Hp) as [P1 S1]. split; [exact P1| apply MSx; exact S1].
      * intros m. rewrite FN, FP. destruct (aptr_eqb_spec' m g); [tauto| apply LNN].
      * intros m Hn. rewrite FN in Hn. destruct (aptr_eqb_spec' m g); [congruence|]. apply MSx. apply LS. exact Hn.
    + constructor.
      * intros h0 Hh0. rewrite EF in Hh0. destruct (CF h0 Hh0) as [N M]. rewrite FN, EMM, (aptr_eqb_neq h0 g) by (exact (NEfree h0 Hh0)). auto.
      * intros sc' a Ha. rewrite EH in Ha. rewrite ?aptr_eqb_refl in Ha.
        destruct (Z.eqb_spec sc' sc); [discriminate|].
        destruct (CA sc' a Ha) as (R & N & GM & SCa).
        assert (NEa : a <> g) by (intros ->; apply n; rewrite SC; symmetry; exact SCa).
        rewrite FN, ESC, (aptr_eqb_neq a g NEa). split; [exact R|]. split; [exact N|]. split; [apply EGM; exact GM| exact SCa].
    + intros m x Hn. rewrite !EGM, !ESC. rewrite FN in Hn. destruct (aptr_eqb_spec' m g); [discriminate|]. exact (HO m x Hn).
  - (* [comment removed for export] *)
    assert (NEpv : pv <> g) by (intros ->; rewrite Npv in NX; apply NEnx; congruence).
    assert (FN : forall q, m_next (get_meta_rec st' q) = if aptr_eqb q g then None else if aptr_eqb q pv then Some nx else m_next (get_meta_rec st q)).
    { intros q. unfold st'. apply dequeue_next; assumption. }
    assert (FP : forall q, m_prev (get_meta_rec st' q) = if aptr_eqb q g then None else if aptr_eqb q nx then Some pv else m_prev (get_meta_rec st q)).
    { intros q. unfold st'. apply dequeue_prev; assumption. }
    assert (Nnx : m_next (get_meta_rec st nx) <> None) by (intros E; apply (proj1 (LNN nx)) in E; congruence).
    assert (Ppv : m_prev (get_meta_rec st pv) <> None) by (intros E; apply (proj2 (LNN pv)) in E; congruence).
    assert (NXT : forall x, x <> g -> m_next (get_meta_rec st x) <> None -> m_next (get_meta_rec st' x) <> None).
    { intros x NE Hx. rewrite FN, (aptr_eqb_neq x g NE). destruct (aptr_eqb x pv); [discriminate| exact Hx]. }
    apply (KINV_xfer_sbl st st' LB c S K).
    + constructor.
      * intros m x Hn. rewrite FN in Hn. rewrite FP. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
        destruct (aptr_eqb_spec' m pv) as [->|NEmp].
        -- assert (x = nx) as -> by congruence. rewrite (aptr_eqb_neq nx g NEnx), aptr_eqb_refl. split; [reflexivity| apply MSx; exact Snx].
        -- destruct (LN m x Hn) as [P1 S1].
           destruct (aptr_eqb_spec' x g); [subst; exfalso; rewrite PV in P1; assert (m = pv) by congruence; tauto|].
           destruct (aptr_eqb_spec' x nx); [subst; exfalso; rewrite Pnx in P1; assert (m = g) by congruence; tauto|].
           split; [exact P1| apply MSx; exact S1].
      * intros m y Hp. rewrite FP in Hp. rewrite FN. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
        destruct (aptr_eqb_spec' m nx) as [->|NEmn].
        -- assert (y = pv) as -> by congruence. rewrite (aptr_eqb_neq pv g NEpv), aptr_eqb_refl. split; [reflexivity| apply MSx; exact Spv].
        -- destruct (LP m y Hp) as [N1 S1].
           destruct (aptr_eqb_spec' y g); [subst; exfalso; rewrite NX in N1; assert (m = nx) by congruence; tauto|].
           destruct (aptr_eqb_spec' y pv); [subst; exfalso; rewrite Npv in N1; assert (m = g) by congruence; tauto|].
           split; [exact N1| apply MSx; exact S1].
      * intros m. rewrite FN, FP. destruct (aptr_eqb_spec' m g); [tauto|].
        destruct (aptr_eqb_spec' m pv); [subst| destruct (aptr_eqb_spec' m nx); [subst|]].
        -- destruct (aptr_eqb_spec' pv nx); [split; discriminate|]. split; [discriminate| intros E; exfalso; exact (Ppv E)].
        -- split; [intros E; exfalso; exact (Nnx E)| discriminate].
        -- apply LNN.
      * intros m Hn. rewrite FN in Hn. destruct (aptr_eqb_spec' m g); [congruence|]. apply MSx.
        destruct (aptr_eqb_spec' m pv); [subst; exact Spv| apply LS; exact Hn].
    + constructor.
      * intros h0 Hh0. rewrite EF in Hh0. destruct (CF h0 Hh0) as [N M]. rewrite EMM. split; [apply NXT; [exact (NEfree h0 Hh0)| exact N]| exact M].
      * intros sc' a Ha. rewrite EH, ?(aptr_eqb_neq nx g NEnx) in Ha. rewrite ESC.
        assert (OLD : active st sc' = Some a -> a <> g -> 0 <= sc' < 48 /\ m_next (get_meta_rec st' a) <> None /\ is_gm st' a /\ m_sizeclass (get_meta_rec st a) = sc').
        { intros Ho NE. destruct (CA sc' a Ho) as (R & N & GM & SCa). split; [exact R|]. split; [apply NXT; auto|]. split; [apply EGM; exact GM| exact SCa]. }
        destruct (Z.eqb_spec sc' sc).
        -- subst sc'. destruct (active st sc) as [a0|] eqn:A0; cbn [optr_eqb] in Ha; [|discriminate].
           destruct (aptr_eqb_spec' a0 g).
           ++ assert (a = nx) as -> by congruence. destruct (CA _ _ A0) as (R & _ & _ & _). destruct (HO g nx NX) as [G1 G2].
              split; [exact R|]. split; [apply NXT; [exact NEnx| exact Nnx]|]. split; [apply EGM; tauto| rewrite (G2 GMg); symmetry; exact SC].
           ++ apply OLD; [exact Ha| congruence].
        -- apply OLD; [exact Ha|]. intros ->. destruct (CA sc' g Ha) as (_ & _ & _ & SCg). apply n. rewrite SC. symmetry. exact SCg.
    + intros m x Hn. rewrite !EGM, !ESC. rewrite FN in Hn. destruct (aptr_eqb_spec' m g) as [?|NEmg]; [discriminate|].
      destruct (aptr_eqb_spec' m pv) as [->|NEmp].
      * assert (x = nx) as -> by congruence. destruct (HO pv g Npv) as [A1 A2]. destruct (HO g nx NX) as [B1 B2].
        split; [tauto|]. intros Gp. rewrite (B2 GMg). exact (A2 Gp).
      * exact (HO m x Hn).
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma KINV_grp_del : forall st LB c g p,
  KINV st LB c -> hosts st p g -> m_next (get_meta_rec st g) = None ->
  (forall j, 0 <= j <= m_last_idx (get_meta_rec st g) ->
     (s_groups st) !! (slot_start' (get_meta_rec st g) j) = None
     /\ Forall (fun blk => blk_slot blk <> slot_start' (get_meta_rec st g) j) LB) ->
  KINV (grp_del st g p) LB c
  /\ ~ is_gm (grp_del st g p) g
  /\ (forall s j, (s_slots (grp_del st g p)) !! s <> Some (g, j)).
Proof.
  intros st LB c g p K HB GN CLR.
  pose proof (ki_links _ _ _ K) as L. pose proof L as [LN LP LNN LS].
  pose proof (ki_heads _ _ _ K) as [CF CA]. pose proof (ki_hom _ _ _ K) as HO.
  pose proof (ki_gmetas _ _ _ K) as CG. pose proof (CG p g HB) as GO. pose proof (go_mem _ _ _ GO) as MEM. pose proof (go_li _ _ _ GO) as LI.
  pose proof (ki_slts _ _ _ K) as CS. pose proof (ki_sltt _ _ _ K) as CT. pose proof (ki_ginj _ _ _ K) as GI.
  set (st' := grp_del st g p).
  assert (CNT : 0 <= m_last_idx (get_meta_rec st g) + 1) by lia.
  (* [comment removed for export] *)
  assert (SL : forall s x, (s_slots st') !! s = Some x <->
            (s_slots st) !! s = Some x /\ forall j, 0 <= j <= m_last_idx (get_meta_rec st g) -> s <> slot_start' (get_meta_rec st g) j).
  { intros s x. unfold st', grp_del. rewrite (del_slots_lookup p _ _ (del_group p st) s x CNT). cbn [s_slots del_group set_groups].
    split; intros [H1 H2]; split; auto; intros j Hj; rewrite ?(slot_start'_mem _ p j MEM); [apply H2; lia|].
    rewrite <- (slot_start'_mem _ p j MEM). apply H2. lia. }
  (* [comment removed for export] *)
  assert (GR : forall b gh, (s_groups st') !! b = Some gh <-> b <> p /\ (s_groups st) !! b = Some gh).
  { intros b gh. unfold st'. rewrite grp_del_groups, lookup_delete_Some. split; intros [A B]; split; auto; congruence. }
  assert (HX : forall b q, hosts st' b q <-> b <> p /\ hosts st b q) by (intros; apply hosts_grp_del).
  assert (Hg : forall b, hosts st b g -> b = p) by (intros b Hb; exact (GI b p g Hb HB)).
  assert (Hp : forall q, hosts st p q -> q = g).
  { intros q [ai Hq]. destruct HB as [ai' Hb']. rewrite Hb' in Hq. congruence. }
  assert (GMX : forall q, q <> g -> (is_gm st' q <-> is_gm st q)).
  { intros q NE. split; intros [b Hb]; exists b; [apply HX in Hb; tauto|]. apply HX. split; [| exact Hb]. intros ->. apply NE. apply Hp. exact Hb. }
  assert (NGM : ~ is_gm st' g).
  { intros [b Hb]. apply HX in Hb. destruct Hb as [NE Hb]. apply NE. apply Hg. exact Hb. }
  (* [comment removed for export] *)
  assert (KEEP : forall s, (exists gh, (s_groups st) !! s = Some gh) \/ (exists blk, blk ∈ LB /\ blk_slot blk = s) ->
            forall j, 0 <= j <= m_last_idx (get_meta_rec st g) -> s <> slot_start' (get_meta_rec st g) j).
  { intros s Hs j Hj ->. destruct (CLR j Hj) as [C1 C2]. destruct Hs as [[gh Hgh]|[blk [Hin Hbs]]]; [rewrite C1 in Hgh; discriminate|].
    exact (proj1 (Forall_forall _ _) C2 blk Hin Hbs). }
  assert (LINKED_NE : forall q, m_next (get_meta_rec st q) <> None -> q <> g) by (intros q Hq ->; exact (Hq GN)).
  split; [| split; [exact NGM|]].
  2:{ intros s j Hs. apply SL in Hs. destruct Hs as [H1 H2]. destruct (CS _ _ _ H1) as (_ & E & J). exact (H2 j J E). }
  constructor.
  - apply (links_ext st st'); [reflexivity| intros; split; reflexivity| exact L].
  - constructor.
    + intros h Hh. exact (CF h Hh).
    + intros sc a Ha. destruct (CA sc a Ha) as (R & N & GM & SC). split; [exact R|]. split; [exact N|]. split; [apply GMX; [apply LINKED_NE; exact N| exact GM]| exact SC].
  - intros m nx Hn. change (get_meta_rec st' m) with (get_meta_rec st m) in Hn.
    change (m_sizeclass (get_meta_rec st' nx)) with (m_sizeclass (get_meta_rec st nx)).
    change (m_sizeclass (get_meta_rec st' m)) with (m_sizeclass (get_meta_rec st m)).
    destruct (HO m nx Hn) as [A B].
    assert (NEm : m <> g) by (apply LINKED_NE; rewrite Hn; discriminate).
    assert (NEn : nx <> g).
    { apply LINKED_NE. intros E. apply (proj1 (LNN nx)) in E. destruct (LN m nx Hn) as [P _]. rewrite E in P. discriminate. }
    pose proof (GMX m NEm). pose proof (GMX nx NEn). tauto.
  - intros b q HBq. apply HX in HBq. destruct HBq as [NEb HBq].
    assert (NEq : q <> g) by (intros ->; apply NEb; apply Hg; exact HBq).
    pose proof (CG b q HBq) as GQ.
    constructor; try (change (get_meta_rec st' ?x) with (get_meta_rec st x)); try exact (go_avail _ _ _ GQ); try exact (go_freed _ _ _ GQ);
      try exact (go_li _ _ _ GQ); try exact (go_freeable _ _ _ GQ); try exact (go_sc _ _ _ GQ); try exact (go_maplen _ _ _ GQ);
      try exact (go_bits _ _ _ GQ); try exact (go_mem _ _ _ GQ); try exact (go_region _ _ _ GQ); try exact (go_stride _ _ _ GQ).
    + exact (go_slot _ _ _ GQ).
    + intros ML. destruct (go_nest _ _ _ GQ ML) as (g1 & i1 & b1 & S1 & HB1 & FB & EQB & I1 & NF1 & LT & HK).
      exists g1, i1, b1. change (get_meta_rec st' ?x) with (get_meta_rec st x).
      split. { apply SL. split; [exact S1|]. apply KEEP. left. destruct HBq as [ai Hai]. eexists; exact Hai. }
      split. { apply HX. split; [| exact HB1]. intros ->. pose proof (Hp g1 HB1) as ->.
               destruct (CLR i1 I1) as [C1 _]. rewrite <- EQB in C1. destruct HBq as [ai Hai]. rewrite C1 in Hai. discriminate. }
      change (get_meta_rec st' g1) with (get_meta_rec st g1). change (get_meta_rec st' q) with (get_meta_rec st q).
      split; [exact FB|]. split; [exact EQB|]. split; [exact I1|]. split; [exact NF1|]. split; [exact LT|]. exact HK.
  - intros b gh Hb. apply GR in Hb. destruct Hb as [_ Hb]. exact (ki_grps _ _ _ K b gh Hb).
  - intros b1 b2 q H1 H2. apply HX in H1. apply HX in H2. exact (GI b1 b2 q (proj2 H1) (proj2 H2)).
  - intros s q i Hs. apply SL in Hs. destruct Hs as [Hs NK]. destruct (CS s q i Hs) as (GM & E & I).
    change (get_meta_rec st' q) with (get_meta_rec st q).
    assert (NEq : q <> g) by (intros ->; exact (NK i I E)).
    split; [apply GMX; auto| auto].
  - intros b q i HBq Hi. change (get_meta_rec st' q) with (get_meta_rec st q) in Hi |- *.
    apply HX in HBq. destruct HBq as [NEb HBq].
    assert (NEq : q <> g) by (intros ->; apply NEb; apply Hg; exact HBq).
    apply SL. split; [exact (CT b q i HBq Hi)|].
    intros j Hj E. pose proof (CT p g j HB Hj) as Tg. rewrite <- E, (CT b q i HBq Hi) in Tg. exfalso. apply NEq. congruence.
  - intros b gh o Hb Ho. apply GR in Hb. exact (ki_unk _ _ _ K b gh o (proj2 Hb) Ho).
  - intros q b i HBq Hi. apply HX in HBq. exact (ki_h0 _ _ _ K q b i (proj2 HBq) Hi).
  - apply Forall_forall. intros blk Hin. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ K) blk Hin) as BK.
    destruct BK as [(q & i & b & S1 & HBq & FB & I & NFR & REST) NG SZ].
    constructor; [| unfold st'; rewrite grp_del_groups, lookup_delete_None; right; exact NG | exact SZ].
    exists q, i, b. change (get_meta_rec st' ?x) with (get_meta_rec st x). change (conc st' ?x) with (conc st x). change (get_shadow st' ?x) with (get_shadow st x).
    split. { apply SL. split; [exact S1|]. apply KEEP. right. exists blk. auto. }
    split. { apply HX. split; [| exact HBq]. intros ->. pose proof (Hp q HBq) as ->.
             destruct (CS _ _ _ S1) as (_ & E & _). exact (KEEP (blk_slot blk) (or_intror (ex_intro _ blk (conj Hin eq_refl))) i I E). }
    split; [exact FB|]. split; [exact I|]. split; [exact NFR|]. exact REST.
  - exact (ki_nodup _ _ _ K).
  - exact (ki_cx _ _ _ K).
  - exact (ki_usage _ _ _ K).
  - exact (ki_bk _ _ _ K).
  - exact (ki_ticks _ _ _ K).
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma KINV_put_meta0 st LB c g :
  KINV st LB c -> ~ is_gm st g -> m_next (get_meta_rec st g) = None ->
  (forall s j, (s_slots st) !! s <> Some (g, j)) ->
  KINV (put_meta g meta0 st) LB c.
Proof.
  intros K NGM GN NS.
  pose proof (ki_links _ _ _ K) as L. pose proof L as [LN LP LNN LS]. pose proof (proj1 (LNN g) GN) as GP.
  assert (RQ : forall q, get_meta_rec (put_meta g meta0 st) q = if aptr_eqb q g then meta0 else get_meta_rec st q) by (intros q; apply rec_put).
  assert (GMne : forall q, is_gm st q -> q <> g) by (intros q Hq ->; exact (NGM Hq)).
  assert (LKne : forall q, m_next (get_meta_rec st q) <> None -> q <> g) by (intros q Hq ->; exact (Hq GN)).
  apply (KINV_xfer st (put_meta g meta0 st) LB) with (c := c); try reflexivity.
  - intros q Hq. rewrite RQ, (aptr_eqb_neq q g (GMne q Hq)). apply geom_eq_refl.
  - intros q b HB. pose proof (ki_gmetas _ _ _ K b q HB) as GQ. rewrite RQ, (aptr_eqb_neq q g (GMne q (ex_intro _ b HB))).
    exact (conj (go_avail _ _ _ GQ) (conj (go_freed _ _ _ GQ) (go_bits _ _ _ GQ))).
  - intros q b j HB _ NFR FR. rewrite RQ, (aptr_eqb_neq q g (GMne q (ex_intro _ b HB))) in FR. tauto.
  - exact K.
  - apply links_put_meta0; [exact L| exact GN].
  - apply (heads_lx st (put_meta g meta0 st)); [reflexivity | | intros sc; reflexivity | reflexivity | | exact (ki_heads _ _ _ K)].
    + intros q. rewrite RQ. case_ptr q g; [rewrite GN, GP; split; reflexivity| split; reflexivity].
    + intros q Hq. rewrite RQ, (aptr_eqb_neq q g (LKne q Hq)). split; reflexivity.
  - apply (homog_lx st (put_meta g meta0 st)); [reflexivity | | | exact L | exact (ki_hom _ _ _ K)].
    + intros q. rewrite RQ. case_ptr q g; [rewrite GN, GP; split; reflexivity| split; reflexivity].
    + intros q Hq. rewrite RQ, (aptr_eqb_neq q g (LKne q Hq)). split; reflexivity.
  - exact (ki_cx _ _ _ K).
  - exact (ki_usage _ _ _ K).
Qed.

#[using="Type"] Lemma KINV_fm : forall st LB c g,
  KINV st LB c -> meta_slot st g -> ~ is_gm st g ->
  m_next (get_meta_rec st g) = None ->
  (forall s j, (s_slots st) !! s <> Some (g, j)) ->
  KINV (fm_st st g) LB c.
Proof.
  intros st LB c g K MSg NGM GN NS. unfold fm_st.
  apply (KINV_queue_gen (put_meta g meta0 st) LB c g LFree).
  - apply KINV_put_meta0; assumption.
  - exact MSg.
  - rewrite rec_put, aptr_eqb_refl. reflexivity.
  - rewrite rec_put, aptr_eqb_refl. reflexivity.
  - cbn. split; [| rewrite rec_put, aptr_eqb_refl; reflexivity]. intros [b [ai Hb]]. apply NGM. exists b, ai. exact Hb.
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma snd_slot_start' st g p j : gmeta_ok st g p -> 0 <= j -> snd p + 16 <= snd (slot_start' (get_meta_rec st g) j).
Proof.
  intros GO Hj. rewrite (slot_start'_mem _ p j (go_mem _ _ _ GO)). cbn [aadd snd].
  pose proof (go_stride _ _ _ GO) as [S16 _]. unfold UNIT in *.
  assert (0 <= get_stride (get_meta_rec st g) * j) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.

#[using="Type"] Lemma fst_slot_start' st g p j : gmeta_ok st g p -> fst (slot_start' (get_meta_rec st g) j) = fst p.
Proof. intros GO. rewrite (slot_start'_mem _ p j (go_mem _ _ _ GO)). reflexivity. Qed.

#[using="Type"] Lemma free_slot_clear : forall st LB c g p j,
  KINV st LB c -> hosts st p g -> 0 <= j <= m_last_idx (get_meta_rec st g) ->
  slot_free (get_meta_rec st g) j ->
  (s_groups st) !! (slot_start' (get_meta_rec st g) j) = None
  /\ Forall (fun blk => blk_slot blk <> slot_start' (get_meta_rec st g) j) LB.
Proof.
  intros st LB c g p j K HB Hj FR.
  pose proof (ki_gmetas _ _ _ K) as CG. pose proof (CG p g HB) as GO. pose proof (ki_sltt _ _ _ K p g j HB Hj) as Tj.
  set (s := slot_start' (get_meta_rec st g) j) in *.
  split.
  - destruct (s_groups st !! s) as [gh|] eqn:Hs; [| reflexivity]. exfalso.
    destruct (ki_grps _ _ _ K s gh Hs) as (g' & Hg' & _).
    assert (HB' : hosts st s g') by (exists (g_active_idx gh); rewrite Hs; destruct gh; cbn in Hg' |- *; subst; reflexivity).
    pose proof (CG s g' HB') as GO'.
    destruct (Z.eq_dec (m_maplen (get_meta_rec st g')) 0) as [ML|ML].
    + destruct (go_nest _ _ _ GO' ML) as (g1 & i1 & b1 & S1 & HB1 & FB & EQB & I1 & NF1 & _).
      rewrite Tj in S1. assert (g1 = g) as -> by congruence. assert (i1 = j) as -> by congruence. exact (NF1 FR).
    + destruct (go_region _ _ _ GO') as (r & _ & _ & _ & _ & _ & TOP). destruct (TOP ML) as [S0 _].
      destruct (go_region _ _ _ GO) as (r0 & _ & _ & P0 & _).
      pose proof (snd_slot_start' st g p j GO ltac:(lia)) as LE. fold s in LE. lia.
  - apply Forall_forall. intros blk Hin E.
    pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ K) blk Hin) as BK.
    destruct BK as [(q & i & b & S1 & HBq & FB & I & NFR & _) _ _].
    rewrite E, Tj in S1. assert (q = g) as -> by congruence. assert (i = j) as -> by congruence. exact (NFR FR).
Qed.

#[using="Type"] Lemma top_region_clear : forall st LB c g p i,
  KINV st LB c -> LPRE st LB c g p i -> m_maplen (get_meta_rec st g) <> 0 ->
  (forall j, 0 <= j <= m_last_idx (get_meta_rec st g) -> j <> i -> slot_free (get_meta_rec st g) j) ->
  forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> b = p.
Proof.
  intros st LB c g p i K L ML ALLF.
  pose proof (ki_gmetas _ _ _ K) as CG. pose proof (lp_hosts _ _ _ _ _ _ L) as HB. pose proof (CG p g HB) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & _ & _ & _ & _ & TOP). destruct (TOP ML) as [P0 _].
  assert (REC : forall n, forall b gh, 0 <= snd b < Z.of_nat n -> (s_groups st) !! b = Some gh -> fst b = fst p -> b = p).
  { induction n as [|n IH]; intros b gh Hn Hb Hf; [lia|].
    destruct (ki_grps _ _ _ K b gh Hb) as (g' & Hg' & _).
    assert (HB' : hosts st b g') by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg' |- *; subst; reflexivity).
    pose proof (CG b g' HB') as GO'.
    destruct (Z.eq_dec (m_maplen (get_meta_rec st g')) 0) as [ML'|ML'].
    - destruct (go_nest _ _ _ GO' ML') as (g1 & i1 & b1 & S1 & HB1 & FB & EQB & I1 & NF1 & _).
      pose proof (CG b1 g1 HB1) as GO1.
      destruct (go_region _ _ _ GO1) as (r1 & _ & _ & B10 & _).
      pose proof (snd_slot_start' st g1 b1 i1 GO1 ltac:(lia)) as LE. rewrite <- EQB in LE.
      assert (E1 : b1 = p).
      { destruct HB1 as [ai1 Hb1]. apply (IH b1 _ ltac:(lia) Hb1). rewrite FB. exact Hf. }
      subst b1. assert (g1 = g) as ->.
      { destruct HB1 as [ai1 Hb1]. destruct HB as [ai Hb0]. rewrite Hb0 in Hb1. congruence. }
      exfalso. destruct (Z.eq_dec i1 i) as [->|NE].
      + pose proof (lp_nogroup _ _ _ _ _ _ L) as NG. rewrite <- EQB in NG. rewrite NG in Hb. discriminate.
      + exact (NF1 (ALLF i1 I1 NE)).
    - destruct (go_region _ _ _ GO') as (r' & _ & _ & _ & _ & _ & TOP'). destruct (TOP' ML') as [B0 _].
      apply injective_projections; [exact Hf| rewrite B0, P0; reflexivity]. }
  intros b gh Hb Hf.
  destruct (ki_grps _ _ _ K b gh Hb) as (g' & Hg' & _).
  assert (HB' : hosts st b g') by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg' |- *; subst; reflexivity).
  destruct (go_region _ _ _ (CG b g' HB')) as (rb & _ & _ & B0 & _).
  apply (REC (S (Z.to_nat (snd b))) b gh); [| exact Hb| exact Hf]. rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ZINV (st : mstate) (Zs : list aptr) : Prop :=
  forall q b, m_mem (get_meta_rec st q) = Some b -> hosts st b q \/ In q Zs.

#[using="Type"] Lemma ZINV_of_CINV st LB : CINV st LB -> ZINV st [].
Proof. intros C q b H. left. exact (ci_memh _ _ C q b H). Qed.

#[using="Type"] Lemma ZINV_ext st st' Zs : (forall q, m_mem (get_meta_rec st' q) = m_mem (get_meta_rec st q)) ->
  s_groups st' = s_groups st -> ZINV st Zs -> ZINV st' Zs.
Proof.
  intros EM EG Z q b H. rewrite EM in H. destruct (Z q b H) as [HB|HI]; [left| right; exact HI].
  unfold hosts in *. rewrite EG. exact HB.
Qed.

#[using="Type"] Lemma ZINV_sbl st st' Zs : same_but_links st st' -> ZINV st Zs -> ZINV st' Zs.
Proof.
  intros S. apply ZINV_ext; [| exact (sbl_groups _ _ S)].
  intros q. destruct (data_of_fields st st' q (sbl_data _ _ S q)) as (E & _). exact E.
Qed.

#[using="Type"] Lemma ZINV_aor st g i Zs : ZINV st Zs -> ZINV (aor_st st g i) Zs.
Proof. apply ZINV_ext; [| reflexivity]. intros q. unfold aor_st. rewrite rec_upd. destruct (aptr_eqb_spec' q g); [subst; reflexivity| reflexivity]. Qed.

#[using="Type"] Lemma ZINV_act st a act Zs : ZINV st Zs -> ZINV (act_st st a act) Zs.
Proof. apply ZINV_ext; [| reflexivity]. intros q. unfold act_st. rewrite rec_upd. destruct (aptr_eqb_spec' q a); [subst; reflexivity| reflexivity]. Qed.

#[using="Type"] Lemma ZINV_pd an st sc Zs : ZINV st Zs -> ZINV (pd_st an st sc) Zs.
Proof. intros Z. destruct (pd_st_cases an st sc) as [-> | (a & _ & _ & ->)]; [exact Z| apply ZINV_act; exact Z]. Qed.

#[using="Type"] Lemma ZINV_ctx st f Zs : ZINV st Zs -> ZINV (upd_ctx f st) Zs.
Proof. apply ZINV_ext; reflexivity. Qed.

#[using="Type"] Lemma ZINV_fg_usage st g Zs : ZINV st Zs -> ZINV (fg_usage_st st g) Zs.
Proof. intros Z. unfold fg_usage_st. destruct (_ <? 48); [apply ZINV_ctx|]; exact Z. Qed.

#[using="Type"] Lemma ZINV_seq st sc Zs : ZINV st Zs -> ZINV (record_seq sc (step_seq st)) Zs.
Proof.
  intros Z. unfold record_seq, step_seq.
  destruct (c_seq (ctx st) =? 255); destruct (sc_in_seq_range sc); repeat apply ZINV_ctx; exact Z.
Qed.

#[using="Type"] Lemma ZINV_dequeue st h g Zs : ZINV st Zs -> ZINV (dequeue h g st) Zs.
Proof. apply ZINV_sbl. apply sbl_dequeue. Qed.

#[using="Type"] Lemma ZINV_queue st h g Zs : ZINV st Zs -> ZINV (queue_st h g st) Zs.
Proof. apply ZINV_sbl. apply sbl_queue. Qed.

#[using="Type"] Lemma ZINV_grp_del st g p Zs : ZINV st Zs -> hosts st p g -> ZINV (grp_del st g p) (g :: Zs).
Proof.
  intros Z HB q b H. change (get_meta_rec (grp_del st g p) q) with (get_meta_rec st q) in H.
  destruct (Z q b H) as [Hq|HI]; [| right; right; exact HI].
  destruct (aptr_eqb_spec' b p).
  - subst. right. left. destruct Hq as [ai Hq]. destruct HB as [ai' HB]. rewrite HB in Hq. congruence.
  - left. apply hosts_grp_del. split; [exact n| exact Hq].
Qed.

#[using="Type"] Lemma ZINV_fm st g Zs : ZINV st (g :: Zs) -> ZINV (fm_st st g) Zs.
Proof.
  intros Z. unfold fm_st. apply ZINV_queue.
  intros q b H. rewrite rec_put in H. destruct (aptr_eqb_spec' q g); [subst; cbn in H; discriminate|].
  destruct (Z q b H) as [Hq|[E|HI]]; [left; exact Hq| exfalso; exact (n (eq_sym E))| right; exact HI].
Qed.

#[using="Type"] Lemma ZINV_mono st Zs Zs' : ZINV st Zs -> incl Zs Zs' -> ZINV st Zs'.
Proof. intros Z HI q b H. destruct (Z q b H) as [Hq|Hin]; [left; exact Hq| right; exact (HI _ Hin)]. Qed.

End PORT.

End WithCeil.
End MallocFacts_Bpres.

(* [comment removed for export] *)
Module F_free_K.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma cell_read_wr8 st p v rid o :
  ticks_ok st -> 0 <= v < 256 ->
  cell_read (get_shadow (wr8 p v st) rid) o =
  if (N.eqb rid (fst p) && Z.eqb o (snd p))%bool then Known v else cell_read (get_shadow st rid) o.
Proof.
  intros TK Hv. destruct (N.eqb_spec rid (fst p)) as [->|NE]; cbn [andb].
  - destruct (Z.eqb_spec o (snd p)) as [->|NEo]; [apply cell_read_wr8_same; assumption| apply cell_read_wr8_other; exact NEo].
  - rewrite get_shadow_wr8_other by exact NE. reflexivity.
Qed.

#[using="Type"] Lemma wr8_tables st p v :
  s_regions (wr8 p v st) = s_regions st /\ s_areas (wr8 p v st) = s_areas st /\ s_groups (wr8 p v st) = s_groups st
  /\ s_slots (wr8 p v st) = s_slots st /\ s_reserved (wr8 p v st) = s_reserved st /\ s_ctx (wr8 p v st) = s_ctx st
  /\ s_tick (wr8 p v st) = s_tick st /\ (forall q, get_meta_rec (wr8 p v st) q = get_meta_rec st q).
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PROT (st : mstate) (LB : list block) (rid : N) (o : Z) : Prop :=
  (exists b gh, (s_groups st) !! b = Some gh /\ fst b = rid /\ snd b - IB <= o < snd b + 12)
  \/ (exists b g i, hosts st b g /\ fst b = rid /\ 0 <= i <= m_last_idx (get_meta_rec st g) /\ o = sstart_of (get_meta_rec st g) i - IB)
  \/ (exists blk, In blk LB /\ fst (blk_slot blk) = rid
        /\ snd (blk_slot blk) + (blk_addr blk - conc st (blk_slot blk)) - IB <= o < snd (blk_slot blk) + (blk_addr blk - conc st (blk_slot blk))).

Section KSH.
Variables (st st' : mstate) (LB : list block).
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ESL : s_slots st' = s_slots st.
Hypothesis EC : s_ctx st' = s_ctx st.
Hypothesis EM : forall q, get_meta_rec st' q = get_meta_rec st q.
Hypothesis TK' : ticks_ok st'.
Hypothesis SHP : forall rid o, PROT st LB rid o -> cell_read (get_shadow st' rid) o = cell_read (get_shadow st rid) o.

#[using="EG"] Lemma hosts_sh b q : hosts st' b q <-> hosts st b q.
Proof. unfold hosts. rewrite EG. tauto. Qed.
#[using="EG"] Lemma is_gm_sh q : is_gm st' q <-> is_gm st q.
Proof. unfold is_gm. split; intros [b H]; exists b; apply hosts_sh; exact H. Qed.
#[using="ER"] Lemma conc_sh q : conc st' q = conc st q.
Proof. unfold conc, get_region. rewrite ER. reflexivity. Qed.

#[using="SHP"] Lemma hdr_known_sh p b1 i1 rid :
  fst p = rid -> (forall k, 1 <= k <= 3 -> PROT st LB rid (snd p - k)) ->
  hdr_known st p b1 i1 -> hdr_known st' p b1 i1.
Proof.
  intros <- HP (v3 & lo & hi & H3 & I3 & H2 & H1 & E). exists v3, lo, hi.
  rewrite !SHP by (apply HP; lia). auto 10.
Qed.

#[using="ER EA EG ESL EC EM TK' SHP"] Lemma KINV_shadow c : KINV st LB c -> KINV st' LB c.
Proof.
  intros K. pose proof (ki_gmetas _ _ _ K) as CG. pose proof (ki_slts _ _ _ K) as CS.
  assert (GMO : forall b g, hosts st b g -> gmeta_ok st' g b).
  { intros b g HB. pose proof (CG b g HB) as GO. constructor; rewrite ?EM, ?ER, ?ESL; try (destruct GO; assumption).
    - unfold meta_slot. rewrite EA. exact (go_slot _ _ _ GO).
    - intros ML. destruct (go_nest _ _ _ GO ML) as (g1 & i1 & b1 & SL & HB1 & FB & EQB & I1 & NF1 & LT & HK).
      exists g1, i1, b1. rewrite ?EM. split; [exact SL|]. split; [apply hosts_sh; exact HB1|]. split; [exact FB|]. split; [exact EQB|].
      split; [exact I1|]. split; [exact NF1|]. split; [exact LT|].
      eapply hdr_known_sh; [reflexivity| | exact HK].
      intros k Hk. left. destruct HB as [ai Hai]. exists b, (mkGhdr (Some g) ai). split; [exact Hai|]. split; [reflexivity|]. unfold IB. lia. }
  constructor.
  - apply (links_ext st st' EA); [intros q; rewrite EM; auto| exact (ki_links _ _ _ K)].
  - apply (heads_lx st st' EG); [intros q; rewrite EM; auto| intros sc; unfold active, ctx; rewrite EC; reflexivity| unfold ctx; rewrite EC; reflexivity| intros q _; rewrite EM; auto| exact (ki_heads _ _ _ K)].
  - apply (homog_lx st st' EG); [intros q; rewrite EM; auto| intros q _; rewrite EM; auto| exact (ki_links _ _ _ K)| exact (ki_hom _ _ _ K)].
  - intros b g HB. apply GMO. apply hosts_sh. exact HB.
  - intros b gh Hb. rewrite EG in Hb. destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & Hai). exists g. rewrite EM. auto.
  - intros b1 b2 g H1 H2. apply (ki_ginj _ _ _ K b1 b2 g); apply hosts_sh; assumption.
  - intros s g i Hs. rewrite ESL in Hs. rewrite EM. destruct (CS s g i Hs) as (GM & E & I). split; [apply is_gm_sh; exact GM| auto].
  - intros b g i HB Hi. rewrite ESL, EM. apply hosts_sh in HB. rewrite EM in Hi. exact (ki_sltt _ _ _ K b g i HB Hi).
  - intros b gh o Hb Ho. rewrite EG in Hb. rewrite SHP; [exact (ki_unk _ _ _ K b gh o Hb Ho)|].
    left. exists b, gh. split; [exact Hb|]. split; [reflexivity|]. unfold IB. lia.
  - intros g b i HB Hi. apply hosts_sh in HB. rewrite EM in Hi |- *. rewrite SHP; [exact (ki_h0 _ _ _ K g b i HB Hi)|].
    right; left. exists b, g, i. auto.
  - apply Forall_forall. intros blk Hin. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ K) blk Hin) as BK.
    destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
    assert (Hin' : In blk LB) by (first [exact Hin | apply (proj1 (list_elem_of_In _ _)); exact Hin]).
    constructor; [| rewrite EG; exact NG| exact SZ].
    exists g, i, b. rewrite ESL, EM, conc_sh. split; [exact SL|]. split; [apply hosts_sh; exact HB|]. split; [exact FB|]. split; [exact I|]. split; [exact NFR|].
    exists off. split; [exact O0|]. split; [exact OA|]. split; [exact OS|]. split.
    + rewrite SHP; [exact OK|]. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|]. rewrite OA. unfold UNIT, IB in *. lia.
    + eapply hdr_known_sh; [reflexivity| | exact HK]. intros k Hk. right; right. exists blk. split; [exact Hin'|]. split; [reflexivity|].
      cbn [aadd snd]. rewrite OA. unfold UNIT, IB in *. lia.
  - exact (ki_nodup _ _ _ K).
  - pose proof (ki_cx _ _ _ K) as X. unfold kctx, bounces, unmap_seq, ctx in *. rewrite EC. exact X.
  - intros sc Hsc. unfold usage, ctx. rewrite EC. exact (ki_usage _ _ _ K sc Hsc).
  - intros rid off Hb. unfold ctx in Hb. rewrite EC in Hb. rewrite ER. exact (ki_bk _ _ _ K rid off Hb).
  - exact TK'.
Qed.
End KSH.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hdr_st (st : mstate) (pf : aptr) : mstate := wr16 (aadd pf (-2)) 0 (wr8 (aadd pf (-3)) 255 st).

#[using="Type"] Lemma hdr_st_tables st pf :
  s_regions (hdr_st st pf) = s_regions st /\ s_areas (hdr_st st pf) = s_areas st /\ s_groups (hdr_st st pf) = s_groups st
  /\ s_slots (hdr_st st pf) = s_slots st /\ s_reserved (hdr_st st pf) = s_reserved st /\ s_ctx (hdr_st st pf) = s_ctx st
  /\ s_tick (hdr_st st pf) = s_tick st /\ (forall q, get_meta_rec (hdr_st st pf) q = get_meta_rec st q)
  /\ s_metas (hdr_st st pf) = s_metas st /\ s_next_rid (hdr_st st pf) = s_next_rid st.
Proof. repeat split; reflexivity. Qed.

#[using="Type"] Lemma ticks_ok_hdr_st st pf : ticks_ok st -> ticks_ok (hdr_st st pf).
Proof. intros TK. unfold hdr_st, wr16. repeat apply ticks_ok_wr8. exact TK. Qed.

#[using="Type"] Lemma hdr_st_cell_read st pf rid o : ticks_ok st ->
  cell_read (get_shadow (hdr_st st pf) rid) o =
    if (N.eqb rid (fst pf) && ((o =? snd pf - 1) || (o =? snd pf - 2) || (o =? snd pf - 3)))%bool
    then Known (if o =? snd pf - 3 then 255 else 0)
    else cell_read (get_shadow st rid) o.
Proof.
  intros TK. unfold hdr_st, wr16. change (Z.shiftr 0 8) with 0.
  rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
  rewrite (cell_read_wr8 _ _ 0 rid o) by (first [repeat apply ticks_ok_wr8; exact TK | lia]).
  rewrite (cell_read_wr8 _ _ 255 rid o) by (first [exact TK | lia]).
  cbn [aadd fst snd].
  destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
  destruct (Z.eqb_spec o (snd pf + -2 + 1)); destruct (Z.eqb_spec o (snd pf - 1)); try lia;
  destruct (Z.eqb_spec o (snd pf + -2)); destruct (Z.eqb_spec o (snd pf - 2)); try lia;
  destruct (Z.eqb_spec o (snd pf + -3)); destruct (Z.eqb_spec o (snd pf - 3)); try lia; cbn [orb]; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hdr_st_cell_read_other st pf rid o : ticks_ok st ->
  (rid <> fst pf \/ o < snd pf - 3 \/ snd pf <= o) ->
  cell_read (get_shadow (hdr_st st pf) rid) o = cell_read (get_shadow st rid) o.
Proof.
  intros TK H. rewrite hdr_st_cell_read by exact TK.
  destruct (N.eqb_spec rid (fst pf)); cbn [andb]; [| reflexivity].
  destruct (Z.eqb_spec o (snd pf - 1)); [lia|]. destruct (Z.eqb_spec o (snd pf - 2)); [lia|]. destruct (Z.eqb_spec o (snd pf - 3)); [lia|].
  reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hdr_st_known_back st pf rid o v : ticks_ok st ->
  (forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
  cell_read (get_shadow (hdr_st st pf) rid) o = Known v -> exists w, cell_read (get_shadow st rid) o = Known w.
Proof.
  intros TK HK H. rewrite hdr_st_cell_read in H by exact TK.
  destruct (N.eqb_spec rid (fst pf)); cbn [andb] in H; [| exists v; exact H].
  destruct (Z.eqb_spec o (snd pf - 1)); [subst; apply (HK 1); lia|].
  destruct (Z.eqb_spec o (snd pf - 2)); [subst; apply (HK 2); lia|].
  destruct (Z.eqb_spec o (snd pf - 3)); [subst; apply (HK 3); lia|].
  cbn [orb] in H. exists v; exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ZINV_hdr_st st pf Zs : ZINV st Zs -> ZINV (hdr_st st pf) Zs.
Proof. apply ZINV_ext; reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma KINV_hdr_st st LB LB' c (pf : aptr) (blk : block) r :
  CINV st LB -> In blk LB -> KINV st LB' c ->
  (forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk) ->
  fst pf = fst (blk_slot blk) -> (s_regions st) !! (fst pf) = Some r -> r_base r + snd pf = blk_addr blk -> snd pf mod 16 = 0 ->
  KINV (hdr_st st pf) LB' c.
Proof.
  intros C Hin K HLB Hfst Hr Hpo PM.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin)) as SZ.
  destruct BC as [(r0 & Hr0 & Kr0 & A16 & AEND & AL & UNK) HD BB].
  rewrite <- Hfst, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  destruct (hdr_st_tables st pf) as (ER & EA & EG & ESL & ERS & EC & ET & EM & _).
  apply (KINV_shadow st (hdr_st st pf) LB' ER EA EG ESL EC EM (ticks_ok_hdr_st st pf TK)); [| exact K].
  intros rid o HP. apply hdr_st_cell_read_other; [exact TK|].
  destruct (N.eq_dec rid (fst pf)) as [->|NE]; [right| left; exact NE].
  pose proof (ki_gmetas _ _ _ K) as CG.
  destruct HP as [HP|[HP|HP]].
  - destruct HP as (b & gh & Hb & Fb & Ho).
    specialize (HD b gh Hb ltac:(rewrite Fb, Hfst; reflexivity)).
    rewrite (conc_region' st b r) in HD by (rewrite Fb; exact Hr). unfold IB in *. lia.
  - destruct HP as (b & g & i & HB & Fb & Hi & ->).
    pose proof (CG b g HB) as GO. destruct (go_region _ _ _ GO) as (rb & Hrb & _ & B0 & B16 & _). pose proof (go_stride _ _ _ GO) as [S16 SM].
    pose proof (go_mem _ _ _ GO) as MEM. unfold sstart_of. rewrite MEM. cbn [default id].
    assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
    { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
    set (si := get_stride (get_meta_rec st g) * i) in *. clearbody si.
    unfold UNIT, IB in *. Z.div_mod_to_equations. lia.
  - destruct HP as (blk' & Hin' & Fb' & Ho). destruct (HLB blk' Hin') as [HinL NEs].
    specialize (BB blk' HinL NEs ltac:(rewrite Fb', Hfst; reflexivity)).
    pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as BC'.
    pose proof (bk_size _ _ (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk' HinL)) as SZ'.
    destruct BC' as [(r1 & Hr1 & _ & A16' & _ & _ & _) _ _]. rewrite Fb', Hr in Hr1. assert (r1 = r) by congruence. subst r1.
    rewrite (conc_region' st (blk_slot blk') r) in Ho by (rewrite Fb'; exact Hr).
    unfold IB in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma In_filter_iff {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) x :
  In x (filter P l) <-> In x l /\ P x.
Proof.
  rewrite <- list_elem_of_In, list_elem_of_filter.
  pose proof (list_elem_of_In l x) as E. tauto.
Qed.

#[using="Type"] Lemma NoDup_list_filter {A} (P : A -> Prop) `{forall x, Decision (P x)} (l : list A) :
  List.NoDup l -> List.NoDup (filter P l).
Proof.
  induction l as [|x l IH]; intros ND; [constructor|].
  rewrite filter_cons. inversion ND; subst. destruct (decide (P x)); [| apply IH; assumption].
  constructor; [| apply IH; assumption]. intros Hin. apply In_filter_iff in Hin. tauto.
Qed.

#[using="Type"] Lemma map_filter_slot (f : aptr -> bool) (LB : list block) :
  map blk_slot (filter (fun b => f (blk_slot b)) LB) = filter f (map blk_slot LB).
Proof.
  induction LB as [|b LB IH]; [reflexivity|]. cbn [map]. rewrite !filter_cons.
  destruct (decide (f (blk_slot b))); cbn [map]; rewrite IH; reflexivity.
Qed.

#[using="Type"] Lemma KINV_filter_slot st LB c (f : aptr -> bool) : KINV st LB c -> KINV st (filter (fun b => f (blk_slot b)) LB) c.
Proof.
  intros K. pose proof (ki_blks _ _ _ K) as BL. pose proof (ki_nodup _ _ _ K) as ND. destruct K; constructor; auto.
  - apply List.Forall_forall. intros blk Hin. apply In_filter_iff in Hin. destruct Hin as [Hin _].
    exact (proj1 (List.Forall_forall _ _) BL blk Hin).
  - rewrite map_filter_slot. apply NoDup_list_filter. exact ND.
Qed.

#[using="Type"] Lemma LPRE_intro st LB c g p i (blk : block) :
  ci_slots st -> hosts st p g -> (s_slots st) !! (blk_slot blk) = Some (g, i) ->
  ~ slot_free (get_meta_rec st g) i -> (s_groups st) !! (blk_slot blk) = None -> c <= m_sizeclass (get_meta_rec st g) ->
  LPRE st (filter (fun b => negb (aptr_eqb (blk_slot b) (blk_slot blk))) LB) c g p i.
Proof.
  intros CS HB SL NF NG HC. destruct (CS _ _ _ SL) as (GM & E & I).
  constructor; auto.
  - rewrite <- E. exact NG.
  - apply List.Forall_forall. intros b' Hin. apply In_filter_iff in Hin. destruct Hin as [_ Hb'].
    rewrite <- E. intros EQ. rewrite EQ, aptr_eqb_refl in Hb'. exact Hb'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

#[using="Type"] Lemma drop_regions : s_regions st' = delete rid (s_regions st). Proof. reflexivity. Qed.
#[using="Type"] Lemma drop_shadow : s_shadow st' = delete rid (s_shadow st). Proof. reflexivity. Qed.
#[using="Type"] Lemma conc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma pw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite conc_drop by exact H. reflexivity. Qed.
#[using="Type"] Lemma get_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rec_drop q : get_meta_rec st' q = get_meta_rec st q. Proof. reflexivity. Qed.

#[using="PTR"] Lemma meta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). destruct (PM q) as (P1 & P2 & P3).
  unfold meta_cells. rewrite !pw_drop by assumption. reflexivity.
Qed.

#[using="PTR"] Lemma ctx_head_cells_drop : ctx_head_cells st' = ctx_head_cells st.
Proof.
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
  rewrite !pw_drop by assumption. reflexivity.
Qed.
#[using="PTR"] Lemma actives_drop : actives st' = actives st.
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
  change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply pw_drop. apply PA.
Qed.
#[using="PTR"] Lemma ctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
  destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (conc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

End DROP.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ci_mptrs_frame st st2 : ci_mptrs st -> amc (ctx st2) = amc (ctx st) -> s_areas st2 = s_areas st -> s_regions st2 = s_regions st ->
  ci_mptrs st2.
Proof.
  intros (M1 & M2 & M3 & M4 & M5) EC EA ER.
  assert (NG : forall p, ng_ptr st p -> ng_ptr st2 p) by (intros [q|]; cbn; [rewrite ER|]; auto).
  unfold amc in EC. inversion EC.
  unfold ci_mptrs. rewrite H0, H1, H2, H3, EA. repeat split; auto. intros a ar Ha. apply NG. exact (M5 a ar Ha).
Qed.

End PORT.

End WithCeil.
End F_free_K.

(* [comment removed for export] *)
Module F_ntf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_C.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_ntf_D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_ntf_D OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_E OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_F OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_G OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_H.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma gmeta_mw st g p : gmeta_ok st g p -> mw_ok (get_meta_rec st g).
Proof.
  intros GO. pose proof (go_li _ _ _ GO). pose proof (go_freeable _ _ _ GO). pose proof (go_sc _ _ _ GO). pose proof (go_maplen _ _ _ GO).
  unfold mw_ok. repeat split; lia.
Qed.

#[using="Type"] Lemma ntf_unfold {R} (dec : decoder R) f st g i (k : mstate -> mapinfo -> Malloc.M R) bail :
  nontrivial_free dec (S f) st g i k bail =
  let mr := get_meta_rec st g in
  let sc := m_sizeclass mr in
  if ntf_cond st g i then
    match m_next mr with
    | Some _ =>
      guard 50 (sc <? 48) (
        let activate_new := optr_eqb (active st sc) (Some g) in
        let st1 := dequeue (LActive sc) g st in
        match activate_new, active st1 sc with
        | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec (nontrivial_free dec f) st2 g k bail) bail
        | _, _ => free_group R dec (nontrivial_free dec f) st1 g k bail
        end) bail
    | None => free_group R dec (nontrivial_free dec f) st g k bail
    end
  else if Z.lor (m_freed mr) (m_avail mr) =? 0 then
    guard 51 (sc <? 48) (
      if negb (optr_eqb (active st sc) (Some g)) then queue (LActive sc) g st (fun st0 => k (aor_st st0 g i) None) bail
      else k (aor_st st g i) None) bail
  else k (aor_st st g i) None.
Proof. reflexivity. Qed.

#[using="Type"] Lemma free_group_unfold {R} (dec : decoder R) rec st g (k : mstate -> mapinfo -> Malloc.M R) bail :
  free_group R dec rec st g k bail =
  let mr := get_meta_rec st g in
  let st1 := fg_usage_st st g in
  match m_mem mr with
  | None => SVis (EUndef UBadPtr) (fun _ => bail)
  | Some p =>
    let st1 := del_slots p (get_stride mr) (m_last_idx mr + 1) (del_group p st1) in
    if negb (m_maplen mr =? 0) then
      free_meta g (record_seq (m_sizeclass mr) (step_seq st1)) (fun st3 => k st3 (Some (p, m_maplen mr * 4096))) bail
    else
      dec st1 p (fun m idx => rec st1 m idx (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail
  end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ntf_result (st' : mstate) (mi : mapinfo) (a0v a1v : word) : Prop :=
  match mi with
  | None => a1v = wz 0
  | Some (b, len) =>
      a0v = wz (conc st' b) /\ a1v = wz len /\ 0 < len < 2^64 /\ snd b = 0
      /\ (exists r, (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup /\ len = round_up_pg (r_len r))
      /\ (forall b' gh, (s_groups st') !! b' = Some gh -> fst b' <> fst b)
  end.

(* [comment removed for export] *)
Definition oracle_ok (o m : word -> option byte) (st : mstate) : Prop :=
  forall rid r q h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= q < round_up_pg (r_len r) ->
    8 <= (r_base r + q) mod 16 ->
    cell_read (get_shadow st rid) q = Unknown h ->
    o (wa (r_base r + q)) = m (wa (r_base r + q)).

#[using="Type"] Lemma oracle_ok_frame o m st st' : oracle_ok o m st -> s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> oracle_ok o m st'.
Proof.
  intros OK ER ES rid r q h Hr Hk Hq M8 Hc. rewrite ER in Hr. unfold get_shadow in Hc. rewrite ES in Hc.
  exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.

#[using="Type"] Lemma rdv_known o st q v : cell_read (get_shadow st (fst q)) (snd q) = Known v -> rdv pans_mem o st q = v.
Proof. intros H. unfold rdv. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)

End PORT.

End WithCeil.
End F_ntf.

(* [comment removed for export] *)
Module ASlot_W0.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Definition ctx_ta_same (c c1 : mctx) : Prop :=
  c_secret c1 = c_secret c /\ c_init_done c1 = c_init_done c /\ c_mmap_counter c1 = c_mmap_counter c
  /\ c_free_meta_head c1 = c_free_meta_head c /\ c_avail_meta c1 = c_avail_meta c /\ c_avail_meta_count c1 = c_avail_meta_count c
  /\ c_avail_meta_area_count c1 = c_avail_meta_area_count c /\ c_meta_alloc_shift c1 = c_meta_alloc_shift c
  /\ c_meta_area_head c1 = c_meta_area_head c /\ c_meta_area_tail c1 = c_meta_area_tail c /\ c_avail_meta_areas c1 = c_avail_meta_areas c
  /\ c_usage c1 = c_usage c /\ c_unmap_seq c1 = c_unmap_seq c /\ c_seq c1 = c_seq c /\ c_brk c1 = c_brk c.

(* [comment removed for export] *)
Definition geom_same (r r1 : meta) : Prop :=
  m_mem r1 = m_mem r /\ m_last_idx r1 = m_last_idx r /\ m_freeable r1 = m_freeable r /\ m_sizeclass r1 = m_sizeclass r /\ m_maplen r1 = m_maplen r.

Record ta_rel (sc : Z) (st st1 : mstate) : Prop := mkTR {
  tr_regions : s_regions st1 = s_regions st;
  tr_shadow : s_shadow st1 = s_shadow st;
  tr_next : s_next_rid st1 = s_next_rid st;
  tr_areas : s_areas st1 = s_areas st;
  tr_slots : s_slots st1 = s_slots st;
  tr_tick : s_tick st1 = s_tick st;
  tr_secret : s_secret st1 = s_secret st;
  tr_reserved : s_reserved st1 = s_reserved st;
  tr_ctx : ctx_ta_same (ctx st) (ctx st1);
  tr_active : forall c, c <> sc -> active st1 c = active st c;
  tr_bounces : forall i, 0 <= bounces st i -> 0 <= bounces st1 i <= bounces st i;
  tr_geom : forall q, geom_same (get_meta_rec st q) (get_meta_rec st1 q);
  (* [comment removed for export] *)
  tr_bits : forall q i, 0 <= i ->
      Z.testbit (m_avail (get_meta_rec st1 q)) i || Z.testbit (m_freed (get_meta_rec st1 q)) i = true ->
      Z.testbit (m_avail (get_meta_rec st q)) i || Z.testbit (m_freed (get_meta_rec st q)) i = true;
  tr_mrange : forall q, 0 <= m_avail (get_meta_rec st q) < 2^32 -> 0 <= m_freed (get_meta_rec st q) < 2^32 ->
      0 <= m_avail (get_meta_rec st1 q) < 2^32 /\ 0 <= m_freed (get_meta_rec st1 q) < 2^32;
  (* [comment removed for export] *)
  tr_groups : forall b, (exists gh1, (s_groups st1) !! b = Some gh1) <-> (exists gh, (s_groups st) !! b = Some gh);
  tr_gmeta : forall b gh1, (s_groups st1) !! b = Some gh1 ->
      exists gh, (s_groups st) !! b = Some gh /\ g_meta gh1 = g_meta gh
                 /\ (g_active_idx gh1 = g_active_idx gh
                     \/ (0 <= g_active_idx gh1 <= 31 /\ forall g, g_meta gh = Some g -> m_sizeclass (get_meta_rec st g) <> 0))
}.

#[using="Type"] Lemma ctx_ta_same_refl c : ctx_ta_same c c.
Proof. repeat split; reflexivity. Qed.
#[using="Type"] Lemma geom_same_refl r : geom_same r r.
Proof. repeat split; reflexivity. Qed.
End PORT.
End WithCeil.


Ltac ta_auto :=
  first [ reflexivity
        | apply ctx_ta_same_refl
        | (cbn; repeat split; reflexivity)
        | (intros; apply geom_same_refl)
        | (intros ? ? ? Hb__; exact Hb__)
        | (intros ? Ha__ Hf__; split; [exact Ha__| exact Hf__])
        | (intros ? ? Hq__; eexists; split; [exact Hq__|]; split; [reflexivity| left; reflexivity])
        | (intros; unfold bounces, ctx in *; cbn in *; lia)
        | idtac ].

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma ta_rel_refl sc st : ta_rel sc st st.
Proof. constructor; ta_auto. Qed.

#[using="Type"] Lemma ta_rel_trans sc st st1 st2 : ta_rel sc st st1 -> ta_rel sc st1 st2 -> ta_rel sc st st2.
Proof.
  intros A B. destruct A as [R1 S1 N1 A1 L1 T1 E1 V1 C1 AC1 B1 G1 BI1 MR1 GR1 GM1].
  destruct B as [R2 S2 N2 A2 L2 T2 E2 V2 C2 AC2 B2 G2 BI2 MR2 GR2 GM2].
  constructor; try congruence.
  - unfold ctx_ta_same in *. destruct C1 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?). destruct C2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
    repeat split; congruence.
  - intros c Hc. rewrite AC2 by exact Hc. apply AC1. exact Hc.
  - intros i Hi. pose proof (B1 i Hi). pose proof (B2 i ltac:(lia)). lia.
  - intros q. destruct (G1 q) as (?&?&?&?&?). destruct (G2 q) as (?&?&?&?&?). repeat split; congruence.
  - intros q i Hi Hb. apply (BI1 q i Hi). apply (BI2 q i Hi). exact Hb.
  - intros q Ha Hf. destruct (MR1 q Ha Hf) as [Ha1 Hf1]. exact (MR2 q Ha1 Hf1).
  - intros b. rewrite GR2. apply GR1.
  - intros b gh2 H2. destruct (GM2 b gh2 H2) as (gh1 & H1 & M1 & AI1). destruct (GM1 b gh1 H1) as (gh & H & M & AI).
    exists gh. split; [exact H|]. split; [congruence|].
    destruct AI1 as [Q1|[RR1 P1]]; destruct AI as [Q0|[R0 P0]]; [left; congruence| right; split; [lia| exact P0] | right | right; split; [lia| exact P0]].
    split; [lia|]. intros g Hg E0. apply (P1 g); [congruence|]. destruct (G1 g) as (_ & _ & _ & SC1 & _). rewrite SC1. exact E0.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ta_rel_set_active sc st v : ta_rel sc st (set_active sc v st).
Proof.
  constructor; ta_auto.
  intros c Hc. rewrite active_set_active. destruct (Z.eqb_spec c sc); [lia| reflexivity].
Qed.

#[using="Type"] Lemma ta_rel_put_meta sc st g r :
  geom_same (get_meta_rec st g) r ->
  (forall i, 0 <= i -> Z.testbit (m_avail r) i || Z.testbit (m_freed r) i = true ->
             Z.testbit (m_avail (get_meta_rec st g)) i || Z.testbit (m_freed (get_meta_rec st g)) i = true) ->
  (0 <= m_avail (get_meta_rec st g) < 2^32 -> 0 <= m_freed (get_meta_rec st g) < 2^32 -> 0 <= m_avail r < 2^32 /\ 0 <= m_freed r < 2^32) ->
  ta_rel sc st (put_meta g r st).
Proof.
  intros GS BS RS. constructor; ta_auto.
  - intros q. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; exact GS| apply geom_same_refl].
  - intros q i Hi. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; apply BS; exact Hi| auto].
  - intros q. rewrite get_meta_rec_put. destruct (aptr_eqb q g) eqn:E; [apply aptr_eqb_eq in E; subst; exact RS| auto].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ta_rel_put_links sc st g p n :
  ta_rel sc st (put_meta g (m_set_prev p (m_set_next n (get_meta_rec st g))) st).
Proof. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.
#[using="Type"] Lemma ta_rel_put_next sc st g n :
  ta_rel sc st (put_meta g (m_set_next n (get_meta_rec st g)) st).
Proof. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.
#[using="Type"] Lemma ta_rel_put_prev sc st g p :
  ta_rel sc st (put_meta g (m_set_prev p (get_meta_rec st g)) st).
Proof. apply ta_rel_put_meta; [repeat split; reflexivity| cbn; auto| cbn; auto]. Qed.

#[using="Type"] Lemma ta_rel_set_bounce sc st i v : 0 <= v <= bounces st i -> ta_rel sc st (set_bounce i v st).
Proof.
  intros Hv. constructor; ta_auto.
  intros j Hj. rewrite bounces_set. destruct (Z.eqb_spec j i); [subst; lia| lia].
Qed.

#[using="Type"] Lemma ta_rel_decay sc st c : 0 <= bounces st (c - 7) -> ta_rel sc st (decay_bounces c st).
Proof.
  intros Hb. unfold decay_bounces. destruct (_ && _) eqn:E; [|apply ta_rel_refl].
  apply andb_prop in E. destruct E as [_ E]. apply negb_true_iff in E. apply Z.eqb_neq in E.
  apply ta_rel_set_bounce. lia.
Qed.

#[using="Type"] Lemma ta_rel_set_gai sc st b ai : 0 <= Z.land ai 31 <= 31 ->
  (forall h g, (s_groups st) !! b = Some h -> g_meta h = Some g -> m_sizeclass (get_meta_rec st g) <> 0) ->
  ta_rel sc st (set_group_active_idx b ai st).
Proof.
  intros Hai HSC. unfold set_group_active_idx. destruct (get_group st b) as [h|] eqn:Hb; [|apply ta_rel_refl].
  unfold get_group in Hb.
  constructor; ta_auto.
  - intros b'. cbn [s_groups set_groups]. destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq. split; intros _; eauto.
    + rewrite lookup_insert_ne by congruence. split; intros X; exact X.
  - intros b' gh1 H. cbn [s_groups set_groups] in H. destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in H. inversion H; subst. exists h. split; [exact Hb|]. cbn. split; [reflexivity| right; split; [exact Hai| intros g Hg; exact (HSC h g Hb Hg)]].
    + rewrite lookup_insert_ne in H by congruence. exists gh1. auto.
Qed.

#[using="Type"] Lemma tr_get_shadow sc st st1 rid : ta_rel sc st st1 -> get_shadow st1 rid = get_shadow st rid.
Proof. intros TR. unfold get_shadow. rewrite (tr_shadow _ _ _ TR). reflexivity. Qed.
#[using="Type"] Lemma tr_conc sc st st1 q : ta_rel sc st st1 -> conc st1 q = conc st q.
Proof. intros TR. unfold conc, get_region. rewrite (tr_regions _ _ _ TR). reflexivity. Qed.
#[using="Type"] Lemma rec_set_gai b ai st q : get_meta_rec (set_group_active_idx b ai st) q = get_meta_rec st q.
Proof. unfold set_group_active_idx. destruct (get_group st b); reflexivity. Qed.
#[using="Type"] Lemma active_set_gai b ai st i : active (set_group_active_idx b ai st) i = active st i.
Proof. unfold set_group_active_idx. destruct (get_group st b); reflexivity. Qed.

End PORT.

End WithCeil.
End ASlot_W0.

(* [comment removed for export] *)
Module ASlot_W12.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.ASlot_W1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.ASlot_W10.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Section STC.
Variables (szc cnt : Z).
Hypothesis SZC : 1 <= szc <= 8191.
Hypothesis CR : 1 <= cnt <= 32.
Hypothesis SMALL : szc * 16 * cnt + 16 <= 2048.
Let n' := szc * 16 * cnt + 12.
Let j := size_to_class n'.

#[using="SZC CR SMALL"] Lemma stc_q_eq : j = stc_q (szc * cnt).
Proof.
  unfold j, n'. rewrite size_to_class_q by nia. f_equal. Z.div_mod_to_equations. nia.
Qed.

End STC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nest_frame (j gm cnt size sc : Z) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 (wz j); C8 (Z_to_bv 64 gm); C8 (wz cnt); C8 (wz cnt); C8 (wz size); C8 (Z_to_bv 64 (sc + 58)); C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

End PORT.

End WithCeil.
End ASlot_W12.

(* [comment removed for export] *)
Module ASlot_W13.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.ASlot_W1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.ASlot_W10 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.ASlot_W12.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.

#[using="SO"] Lemma enf_facts : m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b mod 16 = 0
  /\ 0 <= idx <= m_last_idx mr /\ m_last_idx mr < 32
  /\ snd b + 16 + stride * (m_last_idx mr + 1) <= round_up_pg (r_len r) /\ 16 <= stride /\ stride mod 16 = 0
  /\ (forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b')
  /\ cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0
  /\ (forall off, 0 <= off -> 16 * off + N + 4 <= stride -> (stride * idx + 16 * off) / 16 < 65536).
Proof.
  destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL' AVr FRr FBr MPL SCr].
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16 |- *. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16 |- *.
  repeat (split; [assumption|]). exact Q16.
Qed.

(* [comment removed for export] *)
Definition enf0_st : mstate :=
  wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
    (wr8 (fst b, snd b + (16 + stride * idx) + -3) idx
      (wr16 (fst b, snd b + (16 + stride * idx) + -2) ((snd b + (16 + stride * idx) - (snd b + 16)) / 16) st)).

#[using="r B P STR SO"] Lemma enf0_st_eq : fst (enframe_at st g idx N 0) = enf0_st /\ snd (enframe_at st g idx N 0) = (fst b, snd b + (16 + stride * idx)).
Proof.
  pose proof enf_facts as (Hmem & _).
  assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
  unfold enframe_at. change (get_meta_rec st g) with mr. rewrite Hmem. cbn [default from_option id]. fold stride.
  change (negb (0 =? 0)) with false. cbv iota beta. unfold aadd. cbn [fst snd].
  unfold set_size. cbn [fst snd].
  replace (snd b + (UNIT + stride * idx) + (stride - IB) - (snd b + (UNIT + stride * idx)) - N) with 0 by (unfold UNIT, IB; lia).
  cbn [Z.eqb negb Z.leb]. unfold enf0_st, UNIT. split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="st g b idx j mr stride B P N"] Lemma meta_word_mod4096 r0 : mw_ok r0 -> meta_word r0 mod 4096 = meta_word (m_set_maplen 0 r0).
Proof.
  intros (LI & FB & SC & ML). unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen m_set_maplen].
  rewrite Z.land_0_l. Z.div_mod_to_equations. lia.
Qed.

#[using="st g b idx j mr stride B P N"] Lemma le1_lor_m64 a : 0 <= a < 32 -> le1 (Z_to_bv 64 (Z.lor a 18446744073709551552)) = [b8 (Z.lor a 192)].
Proof.
  intros Ha. unfold le1. cbn [Z_to_le_bytes]. f_equal. unfold b8. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8). change (bv_modulus 64) with (2^64).
  rewrite <- !(Z.land_ones _ 8) by lia. change (Z.ones 8) with 255.
  rewrite <- (Z.land_ones (Z.lor a 18446744073709551552) 64) by lia.
  change (Z.ones 64) with 18446744073709551615.
  rewrite !Z.land_lor_distr_l. rewrite <- !Z.land_assoc.
  change (Z.land 18446744073709551615 255) with 255. change (Z.land 18446744073709551552 255) with 192.
  change (Z.land 192 255) with 192. reflexivity.
Qed.

Definition pp : aptr := (fst b, snd b + (16 + stride * idx)).

End ENF.

End PORT.

End WithCeil.
End ASlot_W13.

(* [comment removed for export] *)
Module ASlot_W15.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_bigw. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_bigw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma lxor_b2z_1 b : Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. destruct b; reflexivity. Qed.

#[using="Type"] Lemma signed_lit_small z : -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  destruct (Z.ltb_spec (z mod 2^64) (2^63)); Z.div_mod_to_equations; lia.
Qed.

#[using="Type"] Lemma ltb99_leb100 b : (99 <? b) = (100 <=? b).
Proof. destruct (Z.ltb_spec 99 b), (Z.leb_spec 100 b); try reflexivity; lia. Qed.

End PORT.

End WithCeil.
End ASlot_W15.

(* [comment removed for export] *)
Module ASlot_W16.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Definition mm_usage1 (st1 : mstate) (sc usage0 : Z) : Z :=
  if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0.

Definition mm_cnt_red (sc size cnt usage1 : Z) (nosmall : bool) : Z :=
  if (usage1 <? 4 * cnt) && negb nosmall then
    if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
    else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
    else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
    else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
    else cnt
  else cnt.

Definition mm_small (size req usage1 cnt needed : Z) : Z * Z :=
  let req := round_up_pg (req + IB + UNIT) in
  if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed).

Definition mm_final (size req usage1 cnt : Z) (nosmall : bool) : Z * Z :=
  let needed := round_up_pg (size * cnt + UNIT) in
  if negb nosmall && (cnt <=? 7) then mm_small size req usage1 cnt needed else (cnt, needed).

(* [comment removed for export] *)
#[using="Type"] Lemma land_4095_wrap x : 0 <= x -> x + 16 <= 2^64 ->
  Z.land (18446744073709551600 - x) 4095 = Z.land (- (x + 16)) 4095.
Proof.
  intros H0 H1. change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia.
  replace (18446744073709551600 - x) with (- (x + 16) + 2^52 * 2^12) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

#[using="Type"] Lemma land_4095_wrap20 x : 0 <= x -> x + 20 <= 2^64 ->
  Z.land (18446744073709551596 - x) 4095 = Z.land (- (x + 20)) 4095.
Proof.
  intros H0 H1. change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia.
  replace (18446744073709551596 - x) with (- (x + 20) + 2^52 * 2^12) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

#[using="Type"] Lemma land_4095_word z : Z.land (bv_unsigned (Z_to_bv 64 z)) 4095 = Z.land z 4095.
Proof.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^52 * 2^12).
  change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia.
  apply Z.mod_mod_divide. exists (2^52). reflexivity.
Qed.

#[using="Type"] Lemma land3_range x : 0 <= Z.land x 3 <= 3.
Proof. change (Z.land x 3) with (Z.land x (Z.ones 2)). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound x (2^2) ltac:(lia)). lia. Qed.

#[using="Type"] Lemma land_4095_range y : 0 <= Z.land y 4095 < 4096.
Proof. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

#[using="Type"] Lemma round_up_pg_alt x : Z.land (- x) 4095 + x = round_up_pg x.
Proof. unfold round_up_pg. change (PGSZ - 1) with 4095. lia. Qed.

#[using="Type"] Lemma round_up_pg_range x : 0 <= x -> x <= round_up_pg x < x + 4096.
Proof. intros. unfold round_up_pg. change (PGSZ - 1) with 4095. pose proof (land_4095_range (- x)). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End PORT.
End WithCeil.

Ltac bool_hyp b K := destruct b; cbn in K; first [reflexivity | discriminate | congruence | (exfalso; apply K; reflexivity)].
End ASlot_W16.

(* [comment removed for export] *)
Module ASlot_W9.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocNat OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_AS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.ASlot_W0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.ASlot_W1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.ASlot_W2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.ASlot_W3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.ASlot_W4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.ASlot_W5 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.ASlot_W6 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.ASlot_W7 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.ASlot_W8.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Record gmf (st : mstate) (sc : Z) (g : aptr) : Prop := mkGMF {
  gmf_slot : meta_slot st g;
  gmf_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  gmf_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  gmf_mw : mw_ok (get_meta_rec st g);
  gmf_sc48 : m_sizeclass (get_meta_rec st g) < 48;
  gmf_cls : m_sizeclass (get_meta_rec st g) = sc;
  gmf_grp : exists b gh, m_mem (get_meta_rec st g) = Some b /\ (s_groups st) !! b = Some gh /\ g_meta gh = Some g
             /\ 0 <= g_active_idx gh <= m_last_idx (get_meta_rec st g)
             /\ (m_sizeclass (get_meta_rec st g) = 0 -> g_active_idx gh = m_last_idx (get_meta_rec st g))
             /\ (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h);
  gmf_fbits : forall i, 0 <= i -> Z.testbit (m_freed (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g);
  gmf_abits : forall i, 0 <= i -> Z.testbit (m_avail (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g);
  gmf_links : exists n p, m_next (get_meta_rec st g) = Some n /\ m_prev (get_meta_rec st g) = Some p
}.

(* [comment removed for export] *)
Record taf (st : mstate) (sc : Z) : Prop := mkTAF {
  taf_head : forall g, active st sc = Some g -> gmf st sc g /\ m_sizeclass (get_meta_rec st g) = sc;
  taf_next : forall g n, gmf st sc g -> m_next (get_meta_rec st g) = Some n ->
               gmf st sc n /\ m_sizeclass (get_meta_rec st n) = m_sizeclass (get_meta_rec st g) /\ m_prev (get_meta_rec st n) = Some g;
  taf_prev : forall g p, gmf st sc g -> m_prev (get_meta_rec st g) = Some p ->
               gmf st sc p /\ m_next (get_meta_rec st p) = Some g;
  taf_bnc : forall i, 0 <= bounces st i < 256
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma gmf_geom st st1 sc g : ta_rel sc st st1 -> gmf st sc g ->
  meta_slot st1 g /\ 0 <= m_avail (get_meta_rec st1 g) < 2^32 /\ 0 <= m_freed (get_meta_rec st1 g) < 2^32
  /\ mw_ok (get_meta_rec st1 g)
  /\ m_mem (get_meta_rec st1 g) = m_mem (get_meta_rec st g)
  /\ m_last_idx (get_meta_rec st1 g) = m_last_idx (get_meta_rec st g)
  /\ m_sizeclass (get_meta_rec st1 g) = m_sizeclass (get_meta_rec st g)
  /\ m_freeable (get_meta_rec st1 g) = m_freeable (get_meta_rec st g)
  /\ conc st1 g = conc st g.
Proof.
  intros TR GM. destruct (tr_geom _ _ _ TR g) as (E1 & E2 & E3 & E4 & E5).
  destruct (tr_mrange _ _ _ TR g (gmf_avail _ _ _ GM) (gmf_freed _ _ _ GM)) as [RA RF].
  pose proof (gmf_mw _ _ _ GM) as MW. unfold mw_ok in *. rewrite E2, E3, E4, E5.
  split; [eapply meta_slot_same_areas; [apply (tr_areas _ _ _ TR)| apply (gmf_slot _ _ _ GM)]|].
  repeat (split; [first [assumption| lia| reflexivity]|]).
  unfold conc, get_region. rewrite (tr_regions _ _ _ TR). reflexivity.
Qed.

#[using="Type"] Lemma disjoint_high W A n : (forall lo hi, In (lo, hi) W -> hi <= alloc_ceiling) -> alloc_ceiling <= A -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros HW HA; cbn; [exact I|].
  split; [pose proof (HW lo hi ltac:(left; reflexivity)); lia|]. apply IH; [|exact HA]. intros lo' hi' Hin. apply (HW lo' hi'). right. exact Hin.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma decay_cases c st : decay_bounces c st = st \/ exists v, decay_bounces c st = set_bounce (c - 7) v st.
Proof. unfold decay_bounces. destruct (_ && _); [right; eexists; reflexivity| left; reflexivity]. Qed.
#[using="Type"] Lemma active_decay c st i : active (decay_bounces c st) i = active st i.
Proof. destruct (decay_cases c st) as [-> | [v ->]]; reflexivity. Qed.
#[using="Type"] Lemma rec_decay c st q : get_meta_rec (decay_bounces c st) q = get_meta_rec st q.
Proof. destruct (decay_cases c st) as [-> | [v ->]]; reflexivity. Qed.
#[using="Type"] Lemma active_upd_meta g f st i : active (upd_meta g f st) i = active st i.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).
Variables (ra sp gp tp t0 t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 96.
Let spv := bv_unsigned sp.

(* [comment removed for export] *)
Definition nclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
  forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.

End PHASE.

End PORT.

End WithCeil.
End ASlot_W9.

(* [comment removed for export] *)
Module ASlot_W11.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.ASlot_W1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.ASlot_W10.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

#[using="Type"] Lemma small_cnt_range sc i : 0 <= sc < 9 -> 0 <= i < 3 -> 4 <= small_cnt sc i <= 31.
Proof.
  intros Hsc Hi.
  assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). destruct Hs as (n & -> & Hn).
  assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). destruct Hi' as (k & -> & Hk).
  unfold small_cnt. rewrite !Nat2Z.id.
  do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [cbn [nth small_cnt_tab]; lia|]); lia |]). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

(* [comment removed for export] *)
Definition cnt_regs (ra sp gp tp t0 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 (wz size) t2 s0 s1 (wz 4096) (Z_to_bv 64 8) (wz usage) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

End HALVE.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma med_cnt_range i : 0 <= i < 4 -> 20 <= med_cnt i <= 32 /\ med_cnt i mod 4 = 0.
Proof.
  intros Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct C as [->|[->|[->| ->]]]; [change (med_cnt 0) with 28| change (med_cnt 1) with 24| change (med_cnt 2) with 20| change (med_cnt 3) with 32]; (split; [lia| reflexivity]).
Qed.

#[using="Type"] Lemma halve_even_range F : forall cnt u, 1 <= cnt -> 1 <= halve_even F cnt u <= cnt.
Proof.
  induction F as [|F IH]; intros cnt u Hc; cbn [halve_even]; [lia|].
  destruct (Z.even cnt && (u <? 4 * cnt)) eqn:E; [|lia].
  apply andb_prop in E. destruct E as [E _]. rewrite even_of_land1 in E. apply Z.eqb_eq in E. rewrite land1_mod2 in E.
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  pose proof (IH (cnt / 2) u ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma halve_big_range F : forall cnt sz, 0 <= cnt -> 0 <= halve_big F cnt sz <= cnt.
Proof.
  induction F as [|F IH]; intros cnt sz Hc; cbn [halve_big]; [lia|].
  destruct (_ <=? _); [|lia]. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  pose proof (IH (cnt / 2) sz ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma land3_range x : 0 <= Z.land x 3 <= 3.
Proof.
  split; [apply Z.land_nonneg; right; lia|].
  apply Z.ldiff_le; [lia|]. apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
  destruct (Z.testbit x n), (Z.testbit 3 n); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.

#[using="SC"] Lemma cnt0_range : 0 <= cnt0 <= 32.
Proof.
  unfold cnt0. destruct (Z.ltb_spec sc 9).
  - unfold small_cnt_pick. pose proof (small_cnt_range sc 0). pose proof (small_cnt_range sc 1). pose proof (small_cnt_range sc 2).
    destruct (negb _); [lia|]. destruct (negb _); lia.
  - pose proof (med_cnt_range (Z.land sc 3) ltac:(pose proof (land3_range sc); lia)) as [X _].
    pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)).
    pose proof (halve_big_range 8 (halve_even 8 (med_cnt (Z.land sc 3)) u) size ltac:(lia)). lia.
Qed.

End COUNT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.

#[using="C0"] Lemma cnt1_range : 0 <= cnt1 <= 32.
Proof. unfold cnt1. destruct (_ && _); lia. Qed.

End CNT2.

End PORT.

End WithCeil.
End ASlot_W11.

(* [comment removed for export] *)
Module ASlot_I.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.AllocSlot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocNat OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_AS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.ASlot_W1.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState}.

Record ENTRY_REL (st0 st : mstate) : Prop := mkER {
  er_shadow : s_shadow st = s_shadow st0;
  er_groups : forall b, is_Some ((s_groups st) !! b) <-> is_Some ((s_groups st0) !! b);
  er_gregions : forall rid r, r_kind r = RKGroup -> ((s_regions st) !! rid = Some r <-> (s_regions st0) !! rid = Some r);
  er_mrel : mrel st0 st;
  er_mem : forall q, m_mem (get_meta_rec st q) = m_mem (get_meta_rec st0 q);
  er_geom : forall q, m_mem (get_meta_rec st0 q) <> None ->
      get_stride (get_meta_rec st q) = get_stride (get_meta_rec st0 q)
      /\ m_last_idx (get_meta_rec st q) = m_last_idx (get_meta_rec st0 q)
      /\ m_sizeclass (get_meta_rec st q) = m_sizeclass (get_meta_rec st0 q);
  er_bits : forall q i, 0 <= i ->
      Z.testbit (m_avail (get_meta_rec st q)) i || Z.testbit (m_freed (get_meta_rec st q)) i = true ->
      Z.testbit (m_avail (get_meta_rec st0 q)) i || Z.testbit (m_freed (get_meta_rec st0 q)) i = true;
  er_areas : forall a, is_Some ((s_areas st0) !! a) -> is_Some ((s_areas st) !! a)
}.

(* [comment removed for export] *)
Definition ALLC (st : mstate) : Prop :=
  forall rid sh o v t, (s_shadow st) !! rid = Some sh -> (r_cells sh) !! o = Some (v, t) -> (t < s_tick st)%N.

(* [comment removed for export] *)
Definition ret_span (st1 : mstate) (sc idx : Z) (rid : N) (S len : Z) : Prop :=
  exists g b, active st1 sc = Some g /\ m_mem (get_meta_rec st1 g) = Some b /\ rid = fst b
    /\ S = snd b + 16 + get_stride (get_meta_rec st1 g) * idx /\ len = get_stride (get_meta_rec st1 g) - 4.

Record as_inv2 (st0 st st1 : mstate) (sc idx : Z) : Prop := mkAI {
  ai_act : forall c, 0 <= c < sc -> active st1 c = active st c;
  ai_areas : forall a, is_Some ((s_areas st) !! a) -> is_Some ((s_areas st1) !! a);
  ai_tick : s_tick st1 = s_tick st;
  (* [comment removed for export] *)
  ai_fresh : 0 <= idx -> forall rid S len, ret_span st1 sc idx rid S len ->
      forall o v t, S <= o < S + len -> (r_cells (get_shadow st1 rid)) !! o = Some (v, t) -> (t < s_tick st1)%N;
  (* [comment removed for export] *)
  ai_virgin : s_regions st0 = ∅ -> 0 <= idx -> forall rid S len, ret_span st1 sc idx rid S len ->
      forall o, S <= o < S + len ->
        (r_cells (get_shadow st1 rid)) !! o = None /\ (r_hav (get_shadow st1 rid)) !! (o / 16) = None
        /\ (r_havp (get_shadow st1 rid)) !! (o / 4096) = None
}.

Section AGB.
Context {R : Type}.
Variables (f : nat) (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

(* [comment removed for export] *)
Definition as_kq (st2 : mstate) (go : optr) : Malloc.M R :=
  match go with
  | None => k st2 (-1)
  | Some g =>
    let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
    queue (LActive sc) g st3 (fun st4 => k st4 0) bail
  end.

(* [comment removed for export] *)
Definition ag_body (st : mstate) (m : aptr) : Malloc.M R :=
  let size := UNIT * size_class sc in
    let usage0 := usage st sc in
    let cnt :=
      if sc <? 9 then small_cnt_pick sc usage0
      else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) usage0) size in
    let cnt := if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt in
    let tail (st : mstate) (p : aptr) (cnt active_idx : Z) : Malloc.M R := ag_tail full_lay st sc m p cnt active_idx as_kq in
    if PGSZ / 2 <? size * cnt + UNIT then
      let nosmall := is_bouncing sc st in
      let st1 := step_seq (account_bounce sc st) in
      let usage1 := if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0 in
      let cnt :=
        if (usage1 <? 4 * cnt) && negb nosmall then
          if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
          else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
          else cnt
        else cnt in
      let needed := round_up_pg (size * cnt + UNIT) in
      let '(cnt, needed) :=
        if negb nosmall && (cnt <=? 7) then
          let req := round_up_pg (req + IB + UNIT) in
          if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed)
        else (cnt, needed) in
      SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
        if negb (mmap_answer_ok (live_ranges st1) needed r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => as_kq st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r needed st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if cnt - 1 <? ai then cnt - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          tail st4 (rid, 0) cnt ai)
    else
      let j := size_to_class (UNIT + cnt * size - IB) in
      alloc_slot full_lay f st j (UNIT + cnt * size - IB) (fun st1 idx =>
        if idx <? 0 then free_meta m st1 (fun st2 => as_kq st2 None) bail
        else
          match active st1 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g =>
            let p := slot_of st1 g idx in
            let st2 := lh_nest full_lay st1 g idx j size cnt in
            let st3 := upd_meta m (m_set_maplen 0) st2 in
            tail st3 p cnt (cnt - 1)
          end) bail.

(* [comment removed for export] *)
Definition ag_cnt1 (st : mstate) : Z :=
  let size := UNIT * size_class sc in
  let usage0 := usage st sc in
  let cnt :=
    if sc <? 9 then small_cnt_pick sc usage0
    else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) usage0) size in
  if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt.

Definition ag_mmap (st : mstate) (m : aptr) (cnt : Z) : Malloc.M R :=
  let size := UNIT * size_class sc in
  let usage0 := usage st sc in
      let nosmall := is_bouncing sc st in
      let st1 := step_seq (account_bounce sc st) in
      let usage1 := if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0 in
      let cnt :=
        if (usage1 <? 4 * cnt) && negb nosmall then
          if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
          else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
          else cnt
        else cnt in
      let needed := round_up_pg (size * cnt + UNIT) in
      let '(cnt, needed) :=
        if negb nosmall && (cnt <=? 7) then
          let req := round_up_pg (req + IB + UNIT) in
          if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed)
        else (cnt, needed) in
      SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
        if negb (mmap_answer_ok (live_ranges st1) needed r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => as_kq st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r needed st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if cnt - 1 <? ai then cnt - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          ag_tail full_lay st4 sc m (rid, 0) cnt ai as_kq).

Definition ag_nest (st : mstate) (m : aptr) (cnt : Z) : Malloc.M R :=
  let size := UNIT * size_class sc in
      let j := size_to_class (UNIT + cnt * size - IB) in
      alloc_slot full_lay f st j (UNIT + cnt * size - IB) (fun st1 idx =>
        if idx <? 0 then free_meta m st1 (fun st2 => as_kq st2 None) bail
        else
          match active st1 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g =>
            let p := slot_of st1 g idx in
            let st2 := lh_nest full_lay st1 g idx j size cnt in
            let st3 := upd_meta m (m_set_maplen 0) st2 in
            ag_tail full_lay st3 sc m p cnt (cnt - 1) as_kq
          end) bail.

#[using="Type"] Lemma ag_body_eq st m :
  ag_body st m = if PGSZ / 2 <? UNIT * size_class sc * ag_cnt1 st + UNIT then ag_mmap st m (ag_cnt1 st) else ag_nest st m (ag_cnt1 st).
Proof. reflexivity. Qed.

#[using="Type"] Lemma as_grp_eq st1 :
  as_grp full_lay f sc req k bail st1 = alloc_meta st1 (fun st mo => match mo with None => k st (-1) | Some m => ag_body st m end) bail.
Proof.
  unfold as_grp, alloc_group, ag_body, as_kq. f_equal.
Qed.
End AGB.

End PORT.

End WithCeil.
End ASlot_I.
