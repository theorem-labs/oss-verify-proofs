(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull StdioCore Stdio Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import SimW HeapSim NodeSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation PS := (PState fheap hptr).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEG CEC : CEIL}.
Definition htrue : PS -> Model -> Prop := fun _ _ => True.
#[using="Type"] Lemma hframe_htrue : hframe_ok htrue.
Proof. intros s h mo mo' _ _. exact I. Qed.

(* [comment removed for export] *)
Definition sizes (tm : gmap N Z) : list Z := map snd (map_to_list tm).

#[using="Type"] Lemma tok_sizes_sizes h : tok_sizes h = sizes (tok_szmap h).
Proof. exact (tok_sizes_eq h). Qed.

Section ProgSim.
Variable segs : list Segment.            (* [comment removed for export] *)
Variable P : Z -> Z.                     (* [comment removed for export] *)
Variable LCI : libc_st hptr -> Prop.     (* [comment removed for export] *)
#[local] Notation npk := (npeek segs).

Definition RQ (tm : gmap N Z) (nx : N) : @rel PS PS := fun sG moG sC moC =>
  HR (CEG:=CEG) (CEC:=CEC) P htrue htrue sG moG sC moC /\ tok_szmap (ps_heap sG) = tm /\ fh_next (ps_heap sG) = nx
  /\ ps_libc sC = ps_libc sG /\ ps_outfile sC = ps_outfile sG /\ mq moG moC /\ LCI (ps_libc sG).

(* [comment removed for export] *)
Definition eqpost {A} (R1 : A -> @rel PS PS) : A -> A -> @rel PS PS :=
  fun a b sG moG sC moC => a = b /\ R1 a sG moG sC moC.

#[using="Type"] Lemma RQ_libc tm nx sG moG sC moC : RQ tm nx sG moG sC moC -> ps_libc sC = ps_libc sG.
Proof. intros H. exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.
#[using="Type"] Lemma RQ_outfile tm nx sG moG sC moC : RQ tm nx sG moG sC moC -> ps_outfile sC = ps_outfile sG.
Proof. intros H. exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))). Qed.
#[using="Type"] Lemma RQ_mq tm nx sG moG sC moC : RQ tm nx sG moG sC moC -> mq moG moC.
Proof. intros H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.
#[using="Type"] Lemma RQ_lci tm nx sG moG sC moC : RQ tm nx sG moG sC moC -> LCI (ps_libc sG).
Proof. intros H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.
#[using="Type"] Lemma RQ_sizes tm nx sG moG sC moC : RQ tm nx sG moG sC moC -> tok_sizes (ps_heap sG) = sizes tm.
Proof. intros (_ & E & _). rewrite tok_sizes_sizes, E. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rq_ret {A} (R : @rel PS PS) (R1 : A -> @rel PS PS) (a : A) :
  (forall sG moG sC moC, R sG moG sC moC -> R1 a sG moG sC moC) -> fsimw npk R (mret a) (mret a) (eqpost R1).
Proof. intros H. apply fsimw_ret. intros. split; [reflexivity| apply H; assumption]. Qed.

#[using="Type"] Lemma rq_bind {A B} (R : @rel PS PS) (R1 : A -> @rel PS PS) (Q : B -> @rel PS PS) (m m' : Monad.M PS A) (k k' : A -> Monad.M PS B) :
  fsimw npk R m m' (eqpost R1) -> (forall a, fsimw npk (R1 a) (k a) (k' a) (eqpost Q)) ->
  fsimw npk R (mbind m k) (mbind m' k') (eqpost Q).
Proof. intros H1 H2. eapply fsimw_bind_eq; [exact H1| exact H2]. Qed.

#[using="Type"] Lemma rq_munr {A} (R : @rel PS PS) (m' : Monad.M PS A) (Q : A -> A -> @rel PS PS) : fsimw npk R munr m' Q.
Proof. apply fsimw_munr. Qed.

#[using="Type"] Lemma rq_post {A} (R : @rel PS PS) (R1 R2 : A -> @rel PS PS) (m m' : Monad.M PS A) :
  fsimw npk R m m' (eqpost R1) -> (forall a sG moG sC moC, R1 a sG moG sC moC -> R2 a sG moG sC moC) -> fsimw npk R m m' (eqpost R2).
Proof. intros H HI. eapply fsimw_post; [exact H|]. intros a b ? ? ? ? [-> H1]. split; [reflexivity| apply HI; exact H1]. Qed.

#[using="Type"] Lemma rq_pre {A} (R R' : @rel PS PS) (m m' : Monad.M PS A) Q :
  fsimw npk R' m m' Q -> (forall sG moG sC moC, R sG moG sC moC -> R' sG moG sC moC) -> fsimw npk R m m' Q.
Proof. intros H HI. eapply fsimw_pre; [exact H| exact HI]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma ps_heap_set_libc (l : libc_st hptr) (s : PS) : ps_heap (set_libc l s) = ps_heap s.
Proof. destruct s; reflexivity. Qed.
#[using="Type"] Lemma ps_heap_set_outfile (o : option hptr) (s : PS) : ps_heap (set_outfile o s) = ps_heap s.
Proof. destruct s; reflexivity. Qed.

#[using="Type"] Lemma HQ_same_heap {CE : CEIL} (s s' : PS) mo : ps_heap s' = ps_heap s -> HQ P htrue s mo -> HQ P htrue s' mo.
Proof.
  intros E [HF HB]. split; [| rewrite E; exact HB]. rewrite E.
  eapply FQ_other; [exact HF| cbn; rewrite E; reflexivity| cbn; rewrite E; reflexivity| exact I].
Qed.

#[using="Type"] Lemma RQ_same_heap tm nx (sG sC sG' sC' : PS) moG moC :
  ps_heap sG' = ps_heap sG -> ps_heap sC' = ps_heap sC -> ps_libc sC' = ps_libc sG' -> ps_outfile sC' = ps_outfile sG' ->
  LCI (ps_libc sG') ->
  RQ tm nx sG moG sC moC -> RQ tm nx sG' moG sC' moC.
Proof.
  intros EG EC EL' EO' HL ((HQG & HQC & HT) & E1 & E2 & EL & EO & MQ & _).
  split; [| rewrite EG; exact (conj E1 (conj E2 (conj EL' (conj EO' (conj MQ HL)))))].
  split; [| split]; [eapply HQ_same_heap; eauto| eapply HQ_same_heap; eauto| rewrite EG, EC; exact HT].
Qed.

#[using="Type"] Lemma RQ_libc_upd tm nx g sG moG sC moC :
  (forall l, LCI l -> LCI (g l)) ->
  RQ tm nx sG moG sC moC -> RQ tm nx (set_libc (g (ps_libc sG)) sG) moG (set_libc (g (ps_libc sC)) sC) moC.
Proof.
  intros Hg HR. pose proof (RQ_libc _ _ _ _ _ _ HR) as EL. pose proof (RQ_outfile _ _ _ _ _ _ HR) as EO. pose proof (RQ_lci _ _ _ _ _ _ HR) as HL.
  eapply RQ_same_heap; [apply ps_heap_set_libc| apply ps_heap_set_libc| destruct sG, sC; cbn in *; congruence| destruct sG, sC; cbn in *; congruence| destruct sG; cbn in *; apply Hg; exact HL| exact HR].
Qed.

#[using="Type"] Lemma RQ_outfile_upd tm nx o sG moG sC moC :
  RQ tm nx sG moG sC moC -> RQ tm nx (set_outfile o sG) moG (set_outfile o sC) moC.
Proof.
  intros HR. pose proof (RQ_libc _ _ _ _ _ _ HR) as EL. pose proof (RQ_outfile _ _ _ _ _ _ HR) as EO. pose proof (RQ_lci _ _ _ _ _ _ HR) as HL.
  eapply RQ_same_heap; [apply ps_heap_set_outfile| apply ps_heap_set_outfile| destruct sG, sC; cbn in *; congruence| destruct sG, sC; cbn in *; congruence| destruct sG; exact HL| exact HR].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rq_rd_lc tm nx :
  fsimw npk (RQ tm nx) (rd_lc ps_libc) (rd_lc ps_libc) (eqpost (fun l => fun sG moG sC moC => LCI l /\ l = ps_libc sG /\ RQ tm nx sG moG sC moC)).
Proof.
  unfold rd_lc. eapply fsimw_bind; [apply fsimw_get|]. intros a b. apply fsimw_ret.
  intros sG moG sC moC (-> & -> & HR). split; [symmetry; exact (RQ_libc _ _ _ _ _ _ HR)|]. split; [exact (RQ_lci _ _ _ _ _ _ HR)|]. split; [reflexivity| exact HR].
Qed.

#[using="Type"] Lemma rq_upd_lc tm nx g :
  (forall l, LCI l -> LCI (g l)) ->
  fsimw npk (RQ tm nx) (upd_lc ps_libc set_libc g) (upd_lc ps_libc set_libc g) (eqpost (fun _ => RQ tm nx)).
Proof.
  intros Hg. unfold upd_lc. apply fsimw_upd. intros sG moG sC moC HR. split; [reflexivity| apply RQ_libc_upd; [exact Hg| exact HR]].
Qed.

#[using="Type"] Lemma rq_get tm nx :
  fsimw npk (RQ tm nx) mget mget
        (fun a b sG moG sC moC => a = sG /\ b = sC /\ ps_libc b = ps_libc a /\ ps_outfile b = ps_outfile a /\ RQ tm nx sG moG sC moC).
Proof.
  eapply fsimw_post; [apply fsimw_get|]. intros a b sG moG sC moC (-> & -> & HR).
  split; [reflexivity|]. split; [reflexivity|]. split; [exact (RQ_libc _ _ _ _ _ _ HR)|]. split; [exact (RQ_outfile _ _ _ _ _ _ HR)| exact HR].
Qed.

#[using="Type"] Lemma rq_upd_outfile tm nx o :
  fsimw npk (RQ tm nx) (mupd (set_outfile o)) (mupd (set_outfile o)) (eqpost (fun _ => RQ tm nx)).
Proof. apply fsimw_upd. intros sG moG sC moC HR. split; [reflexivity| apply RQ_outfile_upd; exact HR]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma HQ_xstep {CE : CEIL} s mo n rsp mo' evs :
  node_static_ok n -> HQ P htrue s mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> HQ P htrue s mo'.
Proof.
  intros Hs [HF HB] Hst Hvm. split; [| exact HB].
  eapply FQ_after_node; [exact HF| exact Hs| exact Hst| exact Hvm| exact I].
Qed.

#[using="Type"] Lemma nstep_static_ok n mo rsp mo' evs : fdnode n -> nstep n mo rsp mo' evs -> node_static_ok n.
Proof. intros Hn Hst. destruct n; cbn in Hn |- *; try exact I; try destruct Hn. exact (proj1 (proj2 Hst)). Qed.

#[using="Type"] Lemma RQ_xstep tm nx sG moG sC moC n n' rspG rspC moG' moC' evs evs' :
  node_static_ok n -> node_static_ok n' ->
  RQ tm nx sG moG sC moC -> nstep n moG rspG moG' evs -> nstep n' moC rspC moC' evs' -> xstep moG moC moG' moC' ->
  RQ tm nx sG moG' sC moC'.
Proof.
  intros Hs Hs' ((HQG & HQC & HT) & E1 & E2 & EL & EO & MQ & HL) HstG HstC (MQ' & VG & VC).
  split; [| exact (conj E1 (conj E2 (conj EL (conj EO (conj MQ' HL)))))]. split; [| split; [| exact HT]].
  - exact (HQ_xstep sG moG n rspG moG' evs Hs HQG HstG VG).
  - exact (HQ_xstep sC moC n' rspC moC' evs' Hs' HQC HstC VC).
Qed.

#[using="Type"] Lemma npk_fdnode n : fdnode n -> npk n = None.
Proof. destruct n; cbn; intros H; try destruct H; reflexivity. Qed.

(* [comment removed for export] *)
Definition decoded {A} (dec : resp -> option A) (a : A) : Prop := exists rsp, dec rsp = Some a.

(* [comment removed for export] *)
#[using="Type"] Theorem rq_msys {A} tm nx n (dec : resp -> option A) :
  fdnode n -> fsimw npk (RQ tm nx) (msys n dec) (msys n dec) (eqpost (fun a => fun sG moG sC moC => decoded dec a /\ RQ tm nx sG moG sC moC)).
Proof.
  intros Hn. apply fsimw_sys; [apply npk_fdnode; exact Hn|].
  intros sG moG sC moC HR. split.
  - intros rspG moG' evs a HstG Hd.
    destruct (nstep_cross n moG moC rspG moG' evs Hn (RQ_mq _ _ _ _ _ _ HR) HstG) as (moC' & HstC & X).
    exists rspG, moC', a. split; [exact HstC|]. split; [exact Hd|]. split; [reflexivity|]. split; [exists rspG; exact Hd|].
    pose proof (nstep_static_ok n moG rspG moG' evs Hn HstG) as Hs.
    eapply RQ_xstep; eauto.
  - intros code moG' Hx. destruct (nexit_only _ _ _ _ Hx) as [c ->]. destruct Hn.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem rq_read tm nx fd bufG bufC count :
  fsimw npk (RQ tm nx) (msys (NRead fd bufG count) (dec_read bufG count)) (msys (NRead fd bufC count) (dec_read bufC count))
        (eqpost (fun a => fun sG moG sC moC => decoded (dec_read bufG count) a /\ RQ tm nx sG moG sC moC)).
Proof.
  apply fsimw_sys; [reflexivity|].
  intros sG moG sC moC HR. split.
  - intros rspG moG' evs a HstG Hd.
    destruct (nstep_cross_read fd bufG bufC count moG moC rspG moG' evs (RQ_mq _ _ _ _ _ _ HR) HstG) as (rspC & moC' & HstC & X & Ed).
    exists rspC, moC', a. split; [exact HstC|]. split; [rewrite Ed; exact Hd|]. split; [reflexivity|]. split; [exists rspG; exact Hd|].
    eapply (RQ_xstep tm nx sG moG sC moC (NRead fd bufG count) (NRead fd bufC count)); eauto; exact I.
  - intros code moG' Hx. destruct Hx.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem rq_readv tm nx fd dstsG dstsC :
  map snd dstsC = map snd dstsG -> lens_ok dstsG ->
  fsimw npk (RQ tm nx) (msys (NReadv fd dstsG) (dec_readv dstsG)) (msys (NReadv fd dstsC) (dec_readv dstsC))
        (eqpost (fun a => fun sG moG sC moC => decoded (dec_readv dstsG) a /\ RQ tm nx sG moG sC moC)).
Proof.
  intros Hl HG. apply fsimw_sys; [reflexivity|].
  intros sG moG sC moC HR. split.
  - intros rspG moG' evs a HstG Hd.
    destruct (nstep_cross_readv fd dstsG dstsC moG moC rspG moG' evs Hl HG (RQ_mq _ _ _ _ _ _ HR) HstG) as (rspC & moC' & HstC & X & Ed).
    exists rspC, moC', a. split; [exact HstC|]. split; [rewrite Ed; exact Hd|]. split; [reflexivity|]. split; [exists rspG; exact Hd|].
    eapply (RQ_xstep tm nx sG moG sC moC (NReadv fd dstsG) (NReadv fd dstsC)); eauto; exact I.
  - intros code moG' Hx. destruct Hx.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem rq_exit tm nx c (Q : Empty_set -> Empty_set -> @rel PS PS) :
  fsimw npk (RQ tm nx) (msys (NExit c) dec_exit) (msys (NExit c) dec_exit) Q.
Proof.
  apply fsimw_sys; [reflexivity|].
  intros sG moG sC moC HR. split.
  - intros rspG moG' evs a HstG _. destruct HstG.
  - intros code moG' Hx. exact (nexit_cross c moG moC code moG' (RQ_mq _ _ _ _ _ _ HR) Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma RQ_after tm nx tm' nx' (sG0 sC0 sG sC : PS) moG0 moC0 moG moC :
  RQ tm nx sG0 moG0 sC0 moC0 ->
  HR (CEG:=CEG) (CEC:=CEC) P htrue htrue sG moG sC moC -> tok_szmap (ps_heap sG) = tm' -> fh_next (ps_heap sG) = nx' ->
  (forall h, set_heap h sG = set_heap h sG0) -> (forall h, set_heap h sC = set_heap h sC0) ->
  vm_only moG0 moG -> vm_only moC0 moC ->
  RQ tm' nx' sG moG sC moC.
Proof.
  intros (_ & _ & _ & EL & EO & MQ & HL) HR' ET EN SG SC VG VC.
  pose proof (f_equal ps_libc (SG (ps_heap sG))) as LG. pose proof (f_equal ps_libc (SC (ps_heap sC))) as LC.
  pose proof (f_equal ps_outfile (SG (ps_heap sG))) as OG. pose proof (f_equal ps_outfile (SC (ps_heap sC))) as OC.
  rewrite !set_heap_eta in LG, LC, OG, OC. cbn in LG, LC, OG, OC.
  split; [exact HR'|]. split; [exact ET|]. split; [exact EN|]. split; [congruence|]. split; [congruence|].
  split; [| rewrite LG; exact HL].
  eapply mq_vm_r; [exact VC|]. eapply mq_vm_l; [exact VG|]. exact MQ.
Qed.

#[using="Type"] Theorem rq_malloc tm nx n :
  0 <= n -> size_overflows n = false -> bigb n <= QMAX -> ROOMN (sizes tm) P n -> PHI P + R63N (sizes tm) + bigb n <= BLIVE ->
  fsimw npk (RQ tm nx) (hf_malloc (CE:=CEG) n) (hf_malloc (CE:=CEC) n)
        (fun a b sG moG sC moC => a = Some nx /\ b = Some nx /\ RQ (<[nx := n]> tm) (N.succ nx) sG moG sC moC).
Proof.
  intros Hn Hov HQ HR HB. apply fsimw_pointwise. intros sG0 moG0 sC0 moC0 HRQ.
  pose proof HRQ as (HHR & ET & EN & EL & EO & MQ). pose proof (RQ_sizes _ _ _ _ _ _ HRQ) as ES.
  eapply fsimw_post; [apply (hf_malloc_sim_pt segs P htrue htrue hframe_htrue hframe_htrue n sG0 moG0 sC0 moC0 Hn Hov HQ HHR); rewrite ES; assumption|].
  intros a b sG moG sC moC (-> & -> & HR' & ET' & EN' & SG & SC & VG & VC). rewrite EN. split; [reflexivity|]. split; [reflexivity|].
  eapply (RQ_after tm nx); [exact HRQ| exact HR'| rewrite ET', ET, EN; reflexivity| rewrite EN', EN; reflexivity| exact SG| exact SC| exact VG| exact VC].
Qed.

#[using="Type"] Theorem rq_calloc tm nx m n :
  0 <= m -> 0 <= n -> (negb (n =? 0) && (SIZE_MAX / n <? m)) = false -> size_overflows (m * n) = false -> bigb (m * n) <= QMAX ->
  ROOMN (sizes tm) P (m * n) -> PHI P + R63N (sizes tm) + bigb (m * n) <= BLIVE ->
  fsimw npk (RQ tm nx) (hf_calloc (CE:=CEG) m n) (hf_calloc (CE:=CEC) m n)
        (fun a b sG moG sC moC => a = Some nx /\ b = Some nx /\ RQ (<[nx := m * n]> tm) (N.succ nx) sG moG sC moC).
Proof.
  intros Hm Hn Hmax Hov HQ HR HB. apply fsimw_pointwise. intros sG0 moG0 sC0 moC0 HRQ.
  pose proof HRQ as (HHR & ET & EN & EL & EO & MQ). pose proof (RQ_sizes _ _ _ _ _ _ HRQ) as ES.
  eapply fsimw_post; [apply (hf_calloc_sim_pt segs P htrue htrue hframe_htrue hframe_htrue m n sG0 moG0 sC0 moC0 Hm Hn Hmax Hov HQ HHR); rewrite ES; assumption|].
  intros a b sG moG sC moC (-> & -> & HR' & ET' & EN' & SG & SC & VG & VC). rewrite EN. split; [reflexivity|]. split; [reflexivity|].
  eapply (RQ_after tm nx); [exact HRQ| exact HR'| rewrite ET', ET, EN; reflexivity| rewrite EN', EN; reflexivity| exact SG| exact SC| exact VG| exact VC].
Qed.

#[using="Type"] Theorem rq_realloc tm nx k n n' :
  tm !! k = Some n -> 0 <= n' -> size_overflows n' = false -> n' + 3 * PGSZ < LEN_MAX -> bigb n' <= QMAX ->
  ROOMN (sizes tm) P n' -> PHI P + R63N (sizes tm) + bigb n' <= BLIVE ->
  fsimw npk (RQ tm nx) (hf_realloc (CE:=CEG) k n') (hf_realloc (CE:=CEC) k n')
        (fun a b sG moG sC moC => a = Some nx /\ b = Some nx /\ RQ (<[nx := n']> (delete k tm)) (N.succ nx) sG moG sC moC).
Proof.
  intros Hk Hn Hov Hnx HQ HR HB. apply fsimw_pointwise. intros sG0 moG0 sC0 moC0 HRQ.
  pose proof HRQ as (HHR & ET & EN & EL & EO & MQ). pose proof (RQ_sizes _ _ _ _ _ _ HRQ) as ES.
  eapply fsimw_post; [apply (hf_realloc_sim_pt segs P htrue htrue hframe_htrue hframe_htrue k n n' sG0 moG0 sC0 moC0 Hn Hov Hnx HQ HHR); rewrite ?ES, ?ET; assumption|].
  intros a b sG moG sC moC (-> & -> & HR' & ET' & EN' & SG & SC & VG & VC). rewrite EN. split; [reflexivity|]. split; [reflexivity|].
  eapply (RQ_after tm nx); [exact HRQ| exact HR'| rewrite ET', ET, EN; reflexivity| rewrite EN', EN; reflexivity| exact SG| exact SC| exact VG| exact VC].
Qed.

#[using="Type"] Theorem rq_free tm nx k n :
  tm !! k = Some n -> PHI P + R63N (sizes tm) <= BLIVE ->
  fsimw npk (RQ tm nx) (hf_free (CE:=CEG) k) (hf_free (CE:=CEC) k) (eqpost (fun _ => RQ (delete k tm) nx)).
Proof.
  intros Hk HB. apply fsimw_pointwise. intros sG0 moG0 sC0 moC0 HRQ.
  pose proof HRQ as (HHR & ET & EN & EL & EO & MQ). pose proof (RQ_sizes _ _ _ _ _ _ HRQ) as ES.
  eapply fsimw_post; [apply (hf_free_sim_pt segs P htrue htrue hframe_htrue hframe_htrue k n sG0 moG0 sC0 moC0 HHR); rewrite ?ES, ?ET; assumption|].
  intros [] [] sG moG sC moC (HR' & ET' & EN' & SG & SC & VG & VC). split; [reflexivity|].
  eapply (RQ_after tm nx); [exact HRQ| exact HR'| rewrite ET', ET; reflexivity| rewrite EN', EN; reflexivity| exact SG| exact SC| exact VG| exact VC].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem rq_pmalloc tm nx n :
  0 <= n -> size_overflows n = false -> bigb n <= QMAX -> ROOMN (sizes tm) P n -> PHI P + R63N (sizes tm) + bigb n <= BLIVE ->
  fsimw npk (RQ tm nx) (pmalloc (full_ops (CE:=CEG)) n) (pmalloc (full_ops (CE:=CEC)) n)
        (eqpost (fun a => fun sG moG sC moC => a = Some nx /\ RQ (<[nx := n]> tm) (N.succ nx) sG moG sC moC)).
Proof.
  intros Hn Hov HQ HR HB. unfold pmalloc. cbn [ho_malloc full_ops].
  eapply fsimw_bind; [exact (rq_malloc tm nx n Hn Hov HQ HR HB)|].
  intros a b. apply fsimw_pointwise. intros sG moG sC moC (-> & -> & HRQ). cbn [enomem_on_null].
  apply fsimw_ret. intros ? ? ? ? (-> & -> & -> & ->). split; [reflexivity|]. split; [reflexivity| exact HRQ].
Qed.

#[using="Type"] Theorem rq_pcalloc tm nx m n :
  0 <= m -> 0 <= n -> (negb (n =? 0) && (SIZE_MAX / n <? m)) = false -> size_overflows (m * n) = false -> bigb (m * n) <= QMAX ->
  ROOMN (sizes tm) P (m * n) -> PHI P + R63N (sizes tm) + bigb (m * n) <= BLIVE ->
  fsimw npk (RQ tm nx) (pcalloc (full_ops (CE:=CEG)) m n) (pcalloc (full_ops (CE:=CEC)) m n)
        (eqpost (fun a => fun sG moG sC moC => a = Some nx /\ RQ (<[nx := m * n]> tm) (N.succ nx) sG moG sC moC)).
Proof.
  intros Hm Hn Hmax Hov HQ HR HB. unfold pcalloc. cbn [ho_calloc full_ops].
  eapply fsimw_bind; [exact (rq_calloc tm nx m n Hm Hn Hmax Hov HQ HR HB)|].
  intros a b. apply fsimw_pointwise. intros sG moG sC moC (-> & -> & HRQ). cbn [enomem_on_null].
  apply fsimw_ret. intros ? ? ? ? (-> & -> & -> & ->). split; [reflexivity|]. split; [reflexivity| exact HRQ].
Qed.

#[using="Type"] Theorem rq_prealloc tm nx k n n' :
  tm !! k = Some n -> 0 <= n' -> size_overflows n' = false -> n' + 3 * PGSZ < LEN_MAX -> bigb n' <= QMAX ->
  ROOMN (sizes tm) P n' -> PHI P + R63N (sizes tm) + bigb n' <= BLIVE ->
  fsimw npk (RQ tm nx) (prealloc (full_ops (CE:=CEG)) k n') (prealloc (full_ops (CE:=CEC)) k n')
        (eqpost (fun a => fun sG moG sC moC => a = Some nx /\ RQ (<[nx := n']> (delete k tm)) (N.succ nx) sG moG sC moC)).
Proof.
  intros Hk Hn Hov Hnx HQ HR HB. unfold prealloc. cbn [ho_realloc full_ops].
  eapply fsimw_bind; [exact (rq_realloc tm nx k n n' Hk Hn Hov Hnx HQ HR HB)|].
  intros a b. apply fsimw_pointwise. intros sG moG sC moC (-> & -> & HRQ). cbn [enomem_on_null].
  apply fsimw_ret. intros ? ? ? ? (-> & -> & -> & ->). split; [reflexivity|]. split; [reflexivity| exact HRQ].
Qed.

#[using="Type"] Theorem rq_pfree tm nx k n :
  tm !! k = Some n -> PHI P + R63N (sizes tm) <= BLIVE ->
  fsimw npk (RQ tm nx) (pfree (full_ops (CE:=CEG)) k) (pfree (full_ops (CE:=CEC)) k) (eqpost (fun _ => RQ (delete k tm) nx)).
Proof. intros Hk HB. unfold pfree. cbn [ho_free full_ops]. exact (rq_free tm nx k n Hk HB). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma RQ_toks_below tm nx sG moG sC moC k n : RQ tm nx sG moG sC moC -> tm !! k = Some n -> (k < nx)%N.
Proof.
  intros (((_ & TB) & _) & ET & EN & _) Hk. subst tm nx. apply TB. unfold tok_szmap in Hk. rewrite lookup_fmap in Hk.
  destruct (fh_blk (ps_heap sG) !! k); [discriminate| cbn in Hk; discriminate].
Qed.

#[using="Type"] Lemma RQ_fresh tm nx sG moG sC moC : RQ tm nx sG moG sC moC -> tm !! nx = None.
Proof.
  intros HR. destruct (tm !! nx) as [n|] eqn:E; [| reflexivity]. pose proof (RQ_toks_below _ _ _ _ _ _ _ _ HR E). lia.
Qed.

#[using="Type"] Lemma sizes_insert tm k n : tm !! k = None -> Permutation (sizes (<[k := n]> tm)) (n :: sizes tm).
Proof. intros Hk. unfold sizes. etransitivity; [apply Permutation_map; apply map_to_list_insert; exact Hk|]. apply Permutation_refl. Qed.

#[using="Type"] Lemma sizes_delete tm k n : tm !! k = Some n -> Permutation (sizes tm) (n :: sizes (delete k tm)).
Proof. intros Hk. unfold sizes. etransitivity; [apply Permutation_map; symmetry; apply (map_to_list_delete tm k n Hk)|]. apply Permutation_refl. Qed.

#[using="Type"] Lemma R63N_insert tm k n : tm !! k = None -> R63N (sizes (<[k := n]> tm)) = bigb n + R63N (sizes tm).
Proof. intros Hk. rewrite (R63N_perm _ _ (sizes_insert tm k n Hk)). apply R63N_cons. Qed.

#[using="Type"] Lemma R63N_delete tm k n : tm !! k = Some n -> R63N (sizes tm) = bigb n + R63N (sizes (delete k tm)).
Proof. intros Hk. rewrite (R63N_perm _ _ (sizes_delete tm k n Hk)). apply R63N_cons. Qed.

#[using="Type"] Lemma zlen_sizes_insert tm k n : tm !! k = None -> zlen (sizes (<[k := n]> tm)) = 1 + zlen (sizes tm).
Proof. intros Hk. rewrite (zlen_perm _ _ (sizes_insert tm k n Hk)). apply zlen_cons. Qed.

#[using="Type"] Lemma zlen_sizes_delete tm k n : tm !! k = Some n -> zlen (sizes tm) = 1 + zlen (sizes (delete k tm)).
Proof. intros Hk. rewrite (zlen_perm _ _ (sizes_delete tm k n Hk)). apply zlen_cons. Qed.

#[using="Type"] Lemma sizes_empty : sizes (∅ : gmap N Z) = [].
Proof. unfold sizes. rewrite map_to_list_empty. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ROOMN_of_len tm n : (forall c, zlen (sizes tm) + 1 <= P c) -> ROOMN (sizes tm) P n.
Proof.
  intros HP. split; intros _.
  - unfold LRN. pose proof (zcount_le_len (fun n0 => negb (MMAP_THRESHOLD <=? n0) && (size_to_class n0 =? size_to_class n)) (sizes tm)). pose proof (HP (size_to_class n)). lia.
  - unfold n63N. pose proof (zcount_le_len (fun n0 => MMAP_THRESHOLD <=? n0) (sizes tm)). pose proof (HP 63). lia.
Qed.

#[using="Type"] Lemma bigb_le n : 0 <= n -> bigb n <= n + 2 * PGSZ + 20.
Proof.
  intros Hn. unfold bigb. destruct (MMAP_THRESHOLD <=? n); [| unfold PGSZ; lia].
  pose proof (round_up_pg_spec (n + IB + UNIT)) as [[_ B] _]. unfold IB, UNIT, PGSZ in *. lia.
Qed.

End ProgSim.

End WithCeil.
