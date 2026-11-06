(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_ReallocQ HeapFull StdioCore Stdio Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KPin__Spec.MI_Calloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_ReallocQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapDrive HeapSim NodeSim ProgSim USim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.USim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile.
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
Lemma npk_inh segs : forall n f mo1, npeek segs n = Some f -> exists rsp, nstep n mo1 rsp mo1 [].
Proof.
  intros n f mo1 H. destruct n; cbn in H; try discriminate. exists (peek_rsp 0). apply nstep_peek. split; [reflexivity|]. split; [reflexivity|]. exists 0. split; [lia| reflexivity].
Qed.

(* [comment removed for export] *)
Section UBase.
Context {CEG CEC : CEIL}.
Variable segs : list Segment.
#[local] Notation npk := (npeek segs).
#[local] Notation RQ := (ProgSim.RQ (CEG:=CEG) (CEC:=CEC) P9 LCI).
#[local] Notation usimS := (usim npk).

(* [comment removed for export] *)
Definition RX (tm : gmap N Z) (nx : N) (U : PS -> Model -> Prop) : @rel PS PS :=
  fun sG moG sC moC => RQ tm nx sG moG sC moC /\ U sG moG.

(* [comment removed for export] *)
Definition ustable (U : PS -> Model -> Prop) : Prop :=
  forall (s s' : PS) mo mo', ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> vm_only mo mo' -> U s mo -> U s' mo'.

(* [comment removed for export] *)
Definition UF (nx : N) (K : list kfe) (C : list (list byte * list byte)) : PS -> Model -> Prop := fun s mo => FI nx K C (ps_libc s) mo.
#[using="Type"] Lemma UF_stable nx K C : ustable (UF nx K C).
Proof. intros s s' mo mo' EL _ VM H. unfold UF in *. rewrite EL. exact (FI_vm_only _ _ _ _ _ _ VM H). Qed.

Definition RU tm nx K C := RX tm nx (UF nx K C).

#[using="Type"] Lemma RX_RQ tm nx U sG moG sC moC : RX tm nx U sG moG sC moC -> RQ tm nx sG moG sC moC.
Proof. intros [H _]. exact H. Qed.
#[using="Type"] Lemma RQ_minvG tm nx sG moG sC moC : RQ tm nx sG moG sC moC -> minv moG.
Proof. intros H. exact (proj1 (FQ_minv _ _ _ _ _ (proj1 (proj1 (proj1 H))))). Qed.
#[using="Type"] Lemma RX_U tm nx U sG moG sC moC : RX tm nx U sG moG sC moC -> U sG moG.
Proof. intros [_ H]. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ru_bind {A B} := @usim_bind_eq PS PS npk (npk_inh segs) A B.
Definition ru_seq {A B A' B'} := @usim_seq PS PS npk (npk_inh segs) A B A' B'.
Definition ru_bind2 {A B A' B'} := @usim_bind PS PS npk (npk_inh segs) A B A' B'.

#[using="Type"] Lemma ru_ret {A} (R : @rel PS PS) (R1 : A -> @rel PS PS) (a : A) :
  (forall sG moG sC moC, R sG moG sC moC -> R1 a sG moG sC moC) -> usimS R (mret a) (mret a) (eqpost R1).
Proof. intros H. apply usim_ret. intros. split; [reflexivity| apply H; assumption]. Qed.

#[using="Type"] Lemma ru_post {A} (R : @rel PS PS) (R1 R2 : A -> @rel PS PS) (m m' : Monad.M PS A) :
  usimS R m m' (eqpost R1) -> (forall a sG moG sC moC, R1 a sG moG sC moC -> R2 a sG moG sC moC) -> usimS R m m' (eqpost R2).
Proof. intros H HI. eapply usim_post; [exact H|]. intros a b ? ? ? ? [-> H1]. split; [reflexivity| apply HI; exact H1]. Qed.

#[using="Type"] Lemma ru_pre {A} (R R' : @rel PS PS) (m m' : Monad.M PS A) Q :
  usimS R' m m' Q -> (forall sG moG sC moC, R sG moG sC moC -> R' sG moG sC moC) -> usimS R m m' Q.
Proof. intros H HI. eapply usim_pre; [exact H| exact HI]. Qed.

#[using="Type"] Lemma ru_munr {A} (R : @rel PS PS) (m' : Monad.M PS A) (Q : A -> A -> @rel PS PS) :
  (forall sG moG sC moC, R sG moG sC moC -> False) -> usimS R munr m' Q.
Proof. apply usim_munr. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ru_use {A} (R : @rel PS PS) (m m' : Monad.M PS A) Q :
  (forall sG moG sC moC, R sG moG sC moC -> usimS R m m' Q) -> usimS R m m' Q.
Proof.
  intros H. split.
  - intros sG moG sC moC HR. exact (usim_fsimw _ _ _ _ _ (H _ _ _ _ HR) _ _ _ _ HR).
  - intros sG moG sC moC HR. exact (usim_usafe _ _ _ _ _ (H _ _ _ _ HR) _ _ _ _ HR).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ru_bind_retl {A B} (R : @rel PS PS) (a : A) (k k' : A -> Monad.M PS B) Q :
  usimS R (k a) (k' a) Q -> usimS R (mbind (mret a) k) (mbind (mret a) k') Q.
Proof. intros H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ru_get tm nx U :
  usimS (RX tm nx U) mget mget
        (fun a b sG moG sC moC => a = sG /\ b = sC /\ ps_libc b = ps_libc a /\ ps_outfile b = ps_outfile a /\ RX tm nx U sG moG sC moC).
Proof.
  eapply usim_post; [apply usim_get|]. intros a b sG moG sC moC (-> & -> & HR).
  split; [reflexivity|]. split; [reflexivity|]. split; [exact (RQ_libc _ _ _ _ _ _ _ _ (RX_RQ _ _ _ _ _ _ _ HR))|].
  split; [exact (RQ_outfile _ _ _ _ _ _ _ _ (RX_RQ _ _ _ _ _ _ _ HR))| exact HR].
Qed.

#[using="Type"] Lemma ru_rd_lc tm nx U :
  usimS (RX tm nx U) (rd_lc ps_libc) (rd_lc ps_libc)
        (eqpost (fun l => fun sG moG sC moC => l = ps_libc sG /\ LCI l /\ RX tm nx U sG moG sC moC)).
Proof.
  unfold rd_lc. eapply ru_bind2; [apply usim_get|]. intros a b. apply usim_ret.
  intros sG moG sC moC (-> & -> & HR). split; [symmetry; exact (RQ_libc _ _ _ _ _ _ _ _ (RX_RQ _ _ _ _ _ _ _ HR))|].
  split; [reflexivity|]. split; [exact (RQ_lci _ _ _ _ _ _ _ _ (RX_RQ _ _ _ _ _ _ _ HR))| exact HR].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ru_upd_lc tm nx U U' g :
  (forall l, LCI l -> LCI (g l)) ->
  (forall (s : PS) mo, U s mo -> LCI (ps_libc s) -> U' (set_libc (g (ps_libc s)) s) mo) ->
  usimS (RX tm nx U) (upd_lc ps_libc set_libc g) (upd_lc ps_libc set_libc g) (eqpost (fun _ => RX tm nx U')).
Proof.
  intros Hg HU. unfold upd_lc. apply usim_upd. intros sG moG sC moC [HR HUs]. split; [reflexivity|]. split.
  - apply RQ_libc_upd; [exact Hg| exact HR].
  - apply HU; [exact HUs| exact (RQ_lci _ _ _ _ _ _ _ _ HR)].
Qed.

#[using="Type"] Lemma ru_upd_outfile tm nx U o :
  (forall (s : PS) mo, U s mo -> U (set_outfile o s) mo) ->
  usimS (RX tm nx U) (mupd (set_outfile o)) (mupd (set_outfile o)) (eqpost (fun _ => RX tm nx U)).
Proof. intros HU. apply usim_upd. intros sG moG sC moC [HR HUs]. split; [reflexivity|]. split; [apply RQ_outfile_upd; exact HR| apply HU; exact HUs]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition unode {A} (n : node) (dec : resp -> option A) (U : PS -> Model -> Prop) (U' : A -> PS -> Model -> Prop) : Prop :=
  forall (s : PS) mo, U s mo -> minv mo ->
    nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ U' a s mo'.

#[using="Type"] Theorem ru_sys {A} tm nx U U' n (dec : resp -> option A) :
  fdnode n -> unode n dec U U' ->
  usimS (RX tm nx U) (msys n dec) (msys n dec) (eqpost (fun a => RX tm nx (U' a))).
Proof.
  intros Hn HU. apply usim_sys; [apply npk_fdnode; exact Hn|].
  intros sG moG sC moC [HR HUs]. pose proof (RQ_minvG _ _ _ _ _ _ HR) as MI.
  destruct (HU sG moG HUs MI) as [Hs Hk]. split; [exact Hs|]. split; [intros rspG moG' evs Hst; destruct (Hk _ _ _ Hst) as (a & Ha & _); exists a; exact Ha|]. split.
  - intros rspG moG' evs a HstG Hd.
    destruct (nstep_cross n moG moC rspG moG' evs Hn (RQ_mq _ _ _ _ _ _ _ _ HR) HstG) as (moC' & HstC & X).
    exists rspG, moC', a. split; [exact HstC|]. split; [exact Hd|]. split; [reflexivity|]. split.
    + pose proof (nstep_static_ok n moG rspG moG' evs Hn HstG) as Hso. eapply RQ_xstep; eauto.
    + destruct (Hk _ _ _ HstG) as (a' & Ha' & HU'). assert (a' = a) as -> by congruence. exact HU'.
  - intros code moG' Hx. destruct (nexit_only _ _ _ _ Hx) as [c ->]. destruct Hn.
Qed.

#[using="Type"] Theorem ru_read tm nx U U' fd bufG bufC count :
  unode (NRead fd bufG count) (dec_read bufG count) U U' ->
  usimS (RX tm nx U) (msys (NRead fd bufG count) (dec_read bufG count)) (msys (NRead fd bufC count) (dec_read bufC count))
        (eqpost (fun a => RX tm nx (U' a))).
Proof.
  intros HU. apply usim_sys; [reflexivity|].
  intros sG moG sC moC [HR HUs]. pose proof (RQ_minvG _ _ _ _ _ _ HR) as MI.
  destruct (HU sG moG HUs MI) as [Hs Hk]. split; [exact Hs|]. split; [intros rspG moG' evs Hst; destruct (Hk _ _ _ Hst) as (a & Ha & _); exists a; exact Ha|]. split.
  - intros rspG moG' evs a HstG Hd.
    destruct (nstep_cross_read fd bufG bufC count moG moC rspG moG' evs (RQ_mq _ _ _ _ _ _ _ _ HR) HstG) as (rspC & moC' & HstC & X & Ed).
    exists rspC, moC', a. split; [exact HstC|]. split; [rewrite Ed; exact Hd|]. split; [reflexivity|]. split.
    + eapply (RQ_xstep P9 LCI tm nx sG moG sC moC (NRead fd bufG count) (NRead fd bufC count)); eauto; exact I.
    + destruct (Hk _ _ _ HstG) as (a' & Ha' & HU'). assert (a' = a) as -> by congruence. exact HU'.
  - intros code moG' Hx. destruct Hx.
Qed.

#[using="Type"] Theorem ru_readv tm nx U U' fd dstsG dstsC :
  map snd dstsC = map snd dstsG -> lens_ok dstsG ->
  unode (NReadv fd dstsG) (dec_readv dstsG) U U' ->
  usimS (RX tm nx U) (msys (NReadv fd dstsG) (dec_readv dstsG)) (msys (NReadv fd dstsC) (dec_readv dstsC))
        (eqpost (fun a => RX tm nx (U' a))).
Proof.
  intros Hl HG HU. apply usim_sys; [reflexivity|].
  intros sG moG sC moC [HR HUs]. pose proof (RQ_minvG _ _ _ _ _ _ HR) as MI.
  destruct (HU sG moG HUs MI) as [Hs Hk]. split; [exact Hs|]. split; [intros rspG moG' evs Hst; destruct (Hk _ _ _ Hst) as (a & Ha & _); exists a; exact Ha|]. split.
  - intros rspG moG' evs a HstG Hd.
    destruct (nstep_cross_readv fd dstsG dstsC moG moC rspG moG' evs Hl HG (RQ_mq _ _ _ _ _ _ _ _ HR) HstG) as (rspC & moC' & HstC & X & Ed).
    exists rspC, moC', a. split; [exact HstC|]. split; [rewrite Ed; exact Hd|]. split; [reflexivity|]. split.
    + eapply (RQ_xstep P9 LCI tm nx sG moG sC moC (NReadv fd dstsG) (NReadv fd dstsC)); eauto; exact I.
    + destruct (Hk _ _ _ HstG) as (a' & Ha' & HU'). assert (a' = a) as -> by congruence. exact HU'.
  - intros code moG' Hx. destruct Hx.
Qed.

#[using="Type"] Theorem ru_exit tm nx U c (Q : Empty_set -> Empty_set -> @rel PS PS) :
  usimS (RX tm nx U) (msys (NExit c) dec_exit) (msys (NExit c) dec_exit) Q.
Proof.
  apply usim_sys; [reflexivity|]. intros sG moG sC moC [HR _]. split; [exact I|]. split; [intros ? ? ? Hst; destruct Hst|]. split.
  - intros rspG moG' evs a HstG _. destruct HstG.
  - intros code moG' Hx. exact (nexit_cross c moG moC code moG' (RQ_mq _ _ _ _ _ _ _ _ HR) Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma mspec_etwf {A} (P : assn PS) (m : Monad.M PS A) Q (s : PS) mo : mspec P m Q -> P s mo -> etwf (m s) mo (fun _ _ => True).
Proof. intros Hm HP. eapply etwf_mono; [exact (Hm s mo HP)| intros; exact I]. Qed.

#[using="Type"] Lemma tok_fresh_mspec (P : assn PS) p n : mspec P (tok_fresh p n) (fun _ _ _ => True).
Proof. unfold tok_fresh. eapply mspec_bind; [apply mspec_get|]. intros s0. eapply mspec_bind; [apply mspec_upd' with (Q := fun _ _ _ => True); intros; exact I|]. intros []. apply mspec_ret. intros; exact I. Qed.

#[local] Notation MQP := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc.malloc_core_fq_proof.   (* [comment removed for export] *)

#[using="Type"] Lemma hf_malloc_safe tm nx U n sG moG sC moC :
  0 <= n -> bigb n <= QMAX -> ROOMN (sizes tm) P9 n ->
  RX tm nx U sG moG sC moC -> etwf (hf_malloc (CE:=CEG) n sG) moG (fun _ _ => True).
Proof.
  intros Hn HQ HR [HRQ HU0]. pose proof HRQ as [HHR HRest]. destruct HHR as (HQG & HQC & HT). destruct HQG as [FQG TBG].
  pose proof (RQ_sizes _ _ _ _ _ _ _ _ HRQ) as ES.
  unfold hf_malloc. eapply (mspec_etwf (fun s mo => FQ (CE:=CEG) (tok_blocks (ps_heap sG)) P9 htrue s mo /\ ROOMN (map snd (tok_blocks (ps_heap sG))) P9 n) _ (fun _ _ _ => True)).
  - eapply mspec_bind; [apply (raw_mallocF_Q MQP); [exact (hframe_frame htrue hframe_htrue)| exact Hn| exact HQ]|].
    intros [q|]; [eapply mspec_bind; [apply tok_fresh_mspec| intros; apply mspec_ret; intros; exact I]| apply mspec_ret; intros; exact I].
  - split; [exact FQG|]. change (map snd (tok_blocks (ps_heap sG))) with (tok_sizes (ps_heap sG)). rewrite ES. exact HR.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem ru_pmalloc tm nx U U' n :
  (forall (s s' : PS) mo mo', ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> vm_only mo mo' -> U s mo -> U' s' mo') ->
  0 <= n -> size_overflows n = false -> bigb n <= QMAX -> ROOMN (sizes tm) P9 n -> PHI P9 + R63N (sizes tm) + bigb n <= BLIVE ->
  usimS (RX tm nx U) (pmalloc (full_ops (CE:=CEG)) n) (pmalloc (full_ops (CE:=CEC)) n)
        (eqpost (fun a => fun sG moG sC moC => a = Some nx /\ RX (<[nx := n]> tm) (N.succ nx) U' sG moG sC moC)).
Proof.
  intros HU Hn Hov HQ HR HB. unfold pmalloc. cbn [ho_malloc full_ops].
  eapply ru_bind2.
  - apply usim_of_parts.
    + apply fsimw_pointwise. intros sG0 moG0 sC0 moC0 [HRQ HUs].
      pose proof HRQ as (HHR & ET & EN & EL & EO & MQ & HL). pose proof (RQ_sizes _ _ _ _ _ _ _ _ HRQ) as ES.
      eapply fsimw_post; [apply (hf_malloc_sim_pt segs P9 htrue htrue hframe_htrue hframe_htrue n sG0 moG0 sC0 moC0 Hn Hov HQ HHR); rewrite ES; assumption|].
      intros a b sG moG sC moC (-> & -> & HR' & ET' & EN' & SG & SC & VG & VC).
      instantiate (1 := fun a b sG moG sC moC => a = Some nx /\ b = Some nx /\ RX (<[nx := n]> tm) (N.succ nx) U' sG moG sC moC).
      cbn beta. rewrite EN. split; [reflexivity|]. split; [reflexivity|]. split.
      * eapply (RQ_after P9 LCI tm nx); [exact HRQ| exact HR'| rewrite ET', ET, EN; reflexivity| rewrite EN', EN; reflexivity| exact SG| exact SC| exact VG| exact VC].
      * pose proof (f_equal ps_libc (SG (ps_heap sG))) as E1. pose proof (f_equal ps_outfile (SG (ps_heap sG))) as E2.
        rewrite !set_heap_eta in E1, E2. cbn in E1, E2. exact (HU sG0 sG moG0 moG E1 E2 VG HUs).
    + intros sG moG sC moC HRX. exact (hf_malloc_safe tm nx U n sG moG sC moC Hn HQ HR HRX).
  - intros a b. apply usim_pure; intros ->. apply usim_pure; intros ->. cbn [enomem_on_null].
    apply usim_ret. intros ? ? ? ? H. split; [reflexivity|]. split; [reflexivity| exact H].
Qed.

#[using="Type"] Lemma hf_calloc_safe tm nx U m n sG moG sC moC :
  0 <= m -> 0 <= n -> bigb (m * n) <= QMAX -> ROOMN (sizes tm) P9 (m * n) ->
  RX tm nx U sG moG sC moC -> etwf (hf_calloc (CE:=CEG) m n sG) moG (fun _ _ => True).
Proof.
  intros Hm Hn HQ HR [HRQ HU0]. pose proof HRQ as [HHR HRest]. destruct HHR as (HQG & HQC & HT). destruct HQG as [FQG TBG].
  pose proof (RQ_sizes _ _ _ _ _ _ _ _ HRQ) as ES.
  unfold hf_calloc. eapply (mspec_etwf (fun s mo => FQ (CE:=CEG) (tok_blocks (ps_heap sG)) P9 htrue s mo /\ ROOMN (map snd (tok_blocks (ps_heap sG))) P9 (m * n)) _ (fun _ _ _ => True)).
  - eapply mspec_bind; [apply (raw_callocF_Q MQP); [exact (hframe_frame htrue hframe_htrue)| exact Hm| exact Hn| exact HQ]|].
    intros [q|]; [eapply mspec_bind; [apply tok_fresh_mspec| intros; apply mspec_ret; intros; exact I]| apply mspec_ret; intros; exact I].
  - split; [exact FQG|]. change (map snd (tok_blocks (ps_heap sG))) with (tok_sizes (ps_heap sG)). rewrite ES. exact HR.
Qed.

#[using="Type"] Theorem ru_pcalloc tm nx U U' m n :
  (forall (s s' : PS) mo mo', ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> vm_only mo mo' -> U s mo -> U' s' mo') ->
  0 <= m -> 0 <= n -> (negb (n =? 0) && (SIZE_MAX / n <? m)) = false -> size_overflows (m * n) = false -> bigb (m * n) <= QMAX ->
  ROOMN (sizes tm) P9 (m * n) -> PHI P9 + R63N (sizes tm) + bigb (m * n) <= BLIVE ->
  usimS (RX tm nx U) (pcalloc (full_ops (CE:=CEG)) m n) (pcalloc (full_ops (CE:=CEC)) m n)
        (eqpost (fun a => fun sG moG sC moC => a = Some nx /\ RX (<[nx := m * n]> tm) (N.succ nx) U' sG moG sC moC)).
Proof.
  intros HU Hm Hn Hmax Hov HQ HR HB. unfold pcalloc. cbn [ho_calloc full_ops].
  eapply ru_bind2.
  - apply usim_of_parts.
    + apply fsimw_pointwise. intros sG0 moG0 sC0 moC0 [HRQ HUs].
      pose proof HRQ as (HHR & ET & EN & EL & EO & MQ & HL). pose proof (RQ_sizes _ _ _ _ _ _ _ _ HRQ) as ES.
      eapply fsimw_post; [apply (hf_calloc_sim_pt segs P9 htrue htrue hframe_htrue hframe_htrue m n sG0 moG0 sC0 moC0 Hm Hn Hmax Hov HQ HHR); rewrite ES; assumption|].
      intros a b sG moG sC moC (-> & -> & HR' & ET' & EN' & SG & SC & VG & VC).
      instantiate (1 := fun a b sG moG sC moC => a = Some nx /\ b = Some nx /\ RX (<[nx := m * n]> tm) (N.succ nx) U' sG moG sC moC).
      cbn beta. rewrite EN. split; [reflexivity|]. split; [reflexivity|]. split.
      * eapply (RQ_after P9 LCI tm nx); [exact HRQ| exact HR'| rewrite ET', ET, EN; reflexivity| rewrite EN', EN; reflexivity| exact SG| exact SC| exact VG| exact VC].
      * pose proof (f_equal ps_libc (SG (ps_heap sG))) as E1. pose proof (f_equal ps_outfile (SG (ps_heap sG))) as E2.
        rewrite !set_heap_eta in E1, E2. cbn in E1, E2. exact (HU sG0 sG moG0 moG E1 E2 VG HUs).
    + intros sG moG sC moC HRX. exact (hf_calloc_safe tm nx U m n sG moG sC moC Hm Hn HQ HR HRX).
  - intros a b. apply usim_pure; intros ->. apply usim_pure; intros ->. cbn [enomem_on_null].
    apply usim_ret. intros ? ? ? ? H. split; [reflexivity|]. split; [reflexivity| exact H].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tok_live (h : fheap) tm k n : tok_szmap h = tm -> tm !! k = Some n -> exists p, fh_blk h !! k = Some (p, n).
Proof.
  intros <- Hk. unfold tok_szmap in Hk. rewrite lookup_fmap in Hk. destruct (fh_blk h !! k) as [[p n']|]; cbn in Hk; [| discriminate]. injection Hk as ->. exists p. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hf_lookup_safe {A} tm nx U k n (raw : aptr -> Monad.M PS A) (kont : A -> Monad.M PS (option hptr)) sG moG sC moC :
  tm !! k = Some n ->
  (forall p, fh_blk (ps_heap sG) !! k = Some (p, n) ->
     mspec (fun s mo => s = sG /\ mo = moG) (raw p) (fun _ _ _ => True)) ->
  (forall a P, mspec P (kont a) (fun _ _ _ => True)) ->
  RX tm nx U sG moG sC moC ->
  etwf ((b <- tok_lookup k ;; match b with None => munr | Some (p, _) => a <- raw p ;; kont a end) sG) moG (fun _ _ => True).
Proof.
  intros Hk Hraw Hkont [HRQ _]. pose proof HRQ as [_ [ET _]].
  destruct (tok_live _ _ _ _ ET Hk) as [p Hp].
  eapply (mspec_etwf (fun s mo => s = sG /\ mo = moG) _ (fun _ _ _ => True)); [| split; reflexivity].
  unfold tok_lookup. eapply mspec_bind with (Q1 := fun b s mo => b = fh_blk (ps_heap sG) !! k /\ s = sG /\ mo = moG).
  { eapply mspec_bind; [apply mspec_get|]. intros s0. apply mspec_ret. intros s mo [-> [-> ->]]. repeat split; reflexivity. }
  intros b. cbv beta. apply mspec_pointwise. intros ? ? (-> & -> & ->). rewrite Hp.
  eapply mspec_bind; [eapply mspec_pre; [apply (Hraw p Hp)| intros ? ? [-> ->]; split; reflexivity]|]. intros a. apply Hkont.
Qed.

#[using="Type"] Lemma hf_realloc_safe tm nx U k n n' sG moG sC moC :
  tm !! k = Some n -> 0 <= n' -> size_overflows n' = false -> n' + 3 * PGSZ < LEN_MAX -> bigb n' <= QMAX -> ROOMN (sizes tm) P9 n' ->
  RX tm nx U sG moG sC moC -> etwf (hf_realloc (CE:=CEG) k n' sG) moG (fun _ _ => True).
Proof.
  intros Hk Hn Hov Hnx HQ HR HRX. pose proof HRX as [HRQ _]. pose proof HRQ as [HHR HRest]. destruct HHR as (HQG & HQC & HT). destruct HQG as [FQG TBG].
  pose proof (RQ_sizes _ _ _ _ _ _ _ _ HRQ) as ES.
  unfold hf_realloc. apply (hf_lookup_safe tm nx U k n _ _ sG moG sC moC Hk); [| | exact HRX].
  - intros p Hp. pose proof (tok_blocks_delete (ps_heap sG) k p n Hp) as PD.
    eapply mspec_conseq; [apply (raw_reallocF_Q MQP (tok_blocks (hdel k (ps_heap sG))) P9 htrue p n n' (hframe_frame htrue hframe_htrue) Hn Hov Hnx HQ)| | intros; exact I].
    intros s mo [-> ->]. split; [eapply FQ_perm; [exact PD| exact FQG]|].
    destruct HR as [R1 R2]. rewrite <- ES in R1, R2. unfold tok_sizes in R1, R2.
    rewrite (LRN_perm _ _ (size_to_class n') (Permutation_map snd PD)) in R1. rewrite (n63N_perm _ _ (Permutation_map snd PD)) in R2. exact (conj R1 R2).
  - intros [q|] P; [| apply mspec_ret; intros; exact I].
    unfold tok_drop. eapply mspec_bind; [apply mspec_upd' with (Q := fun _ _ _ => True); intros; exact I|]. intros [].
    eapply mspec_bind; [apply tok_fresh_mspec| intros; apply mspec_ret; intros; exact I].
Qed.

#[using="Type"] Lemma hf_free_safe tm nx U k n sG moG sC moC :
  tm !! k = Some n -> RX tm nx U sG moG sC moC -> etwf (hf_free (CE:=CEG) k sG) moG (fun _ _ => True).
Proof.
  intros Hk HRX. pose proof HRX as [HRQ _]. pose proof HRQ as [HHR HRest]. destruct HHR as (HQG & HQC & HT). destruct HQG as [FQG TBG].
  unfold hf_free.
  pose proof HRQ as [_ [ET _]]. destruct (tok_live _ _ _ _ ET Hk) as [p Hp]. pose proof (tok_blocks_delete (ps_heap sG) k p n Hp) as PD.
  eapply (mspec_etwf (fun s mo => s = sG /\ mo = moG) _ (fun _ _ _ => True)); [| split; reflexivity].
  unfold tok_lookup. eapply mspec_bind with (Q1 := fun b s mo => b = fh_blk (ps_heap sG) !! k /\ s = sG /\ mo = moG).
  { eapply mspec_bind; [apply mspec_get|]. intros s0. apply mspec_ret. intros s mo [-> [-> ->]]. repeat split; reflexivity. }
  intros b. cbv beta. apply mspec_pointwise. intros ? ? (-> & -> & ->). rewrite Hp.
  eapply mspec_bind.
  { eapply mspec_conseq; [apply (raw_freeF_Q (tok_blocks (hdel k (ps_heap sG))) P9 htrue p n (hframe_frame htrue hframe_htrue))| | intros; exact I].
    intros s mo [-> ->]. eapply FQ_perm; [exact PD| exact FQG]. }
  intros []. unfold tok_drop. apply mspec_upd' with (Q := fun _ _ _ => True). intros; exact I.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem ru_prealloc tm nx U U' k n n' :
  (forall (s s' : PS) mo mo', ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> vm_only mo mo' -> U s mo -> U' s' mo') ->
  tm !! k = Some n -> 0 <= n' -> size_overflows n' = false -> n' + 3 * PGSZ < LEN_MAX -> bigb n' <= QMAX ->
  ROOMN (sizes tm) P9 n' -> PHI P9 + R63N (sizes tm) + bigb n' <= BLIVE ->
  usimS (RX tm nx U) (prealloc (full_ops (CE:=CEG)) k n') (prealloc (full_ops (CE:=CEC)) k n')
        (eqpost (fun a => fun sG moG sC moC => a = Some nx /\ RX (<[nx := n']> (delete k tm)) (N.succ nx) U' sG moG sC moC)).
Proof.
  intros HU Hk Hn Hov Hnx HQ HR HB. unfold prealloc. cbn [ho_realloc full_ops].
  eapply ru_bind2.
  - apply usim_of_parts.
    + apply fsimw_pointwise. intros sG0 moG0 sC0 moC0 [HRQ HUs].
      pose proof HRQ as (HHR & ET & EN & EL & EO & MQ & HL). pose proof (RQ_sizes _ _ _ _ _ _ _ _ HRQ) as ES.
      eapply fsimw_post; [apply (hf_realloc_sim_pt segs P9 htrue htrue hframe_htrue hframe_htrue k n n' sG0 moG0 sC0 moC0 Hn Hov Hnx HQ HHR); rewrite ?ES, ?ET; assumption|].
      intros a b sG moG sC moC (-> & -> & HR' & ET' & EN' & SG & SC & VG & VC).
      instantiate (1 := fun a b sG moG sC moC => a = Some nx /\ b = Some nx /\ RX (<[nx := n']> (delete k tm)) (N.succ nx) U' sG moG sC moC).
      cbn beta. rewrite EN. split; [reflexivity|]. split; [reflexivity|]. split.
      * eapply (RQ_after P9 LCI tm nx); [exact HRQ| exact HR'| rewrite ET', ET, EN; reflexivity| rewrite EN', EN; reflexivity| exact SG| exact SC| exact VG| exact VC].
      * pose proof (f_equal ps_libc (SG (ps_heap sG))) as E1. pose proof (f_equal ps_outfile (SG (ps_heap sG))) as E2.
        rewrite !set_heap_eta in E1, E2. cbn in E1, E2. exact (HU sG0 sG moG0 moG E1 E2 VG HUs).
    + intros sG moG sC moC HRX. exact (hf_realloc_safe tm nx U k n n' sG moG sC moC Hk Hn Hov Hnx HQ HR HRX).
  - intros a b. apply usim_pure; intros ->. apply usim_pure; intros ->. cbn [enomem_on_null].
    apply usim_ret. intros ? ? ? ? H. split; [reflexivity|]. split; [reflexivity| exact H].
Qed.

#[using="Type"] Theorem ru_pfree tm nx U U' k n :
  (forall (s s' : PS) mo mo', ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> vm_only mo mo' -> U s mo -> U' s' mo') ->
  tm !! k = Some n -> PHI P9 + R63N (sizes tm) <= BLIVE ->
  usimS (RX tm nx U) (pfree (full_ops (CE:=CEG)) k) (pfree (full_ops (CE:=CEC)) k) (eqpost (fun _ => RX (delete k tm) nx U')).
Proof.
  intros HU Hk HB. unfold pfree. cbn [ho_free full_ops]. apply usim_of_parts.
  - apply fsimw_pointwise. intros sG0 moG0 sC0 moC0 [HRQ HUs].
    pose proof HRQ as (HHR & ET & EN & EL & EO & MQ & HL). pose proof (RQ_sizes _ _ _ _ _ _ _ _ HRQ) as ES.
    eapply fsimw_post; [apply (hf_free_sim_pt segs P9 htrue htrue hframe_htrue hframe_htrue k n sG0 moG0 sC0 moC0 HHR); rewrite ?ES, ?ET; assumption|].
    intros [] [] sG moG sC moC (HR' & ET' & EN' & SG & SC & VG & VC). split; [reflexivity|]. split.
    + eapply (RQ_after P9 LCI tm nx); [exact HRQ| exact HR'| rewrite ET', ET; reflexivity| rewrite EN', EN; reflexivity| exact SG| exact SC| exact VG| exact VC].
    + pose proof (f_equal ps_libc (SG (ps_heap sG))) as E1. pose proof (f_equal ps_outfile (SG (ps_heap sG))) as E2.
      rewrite !set_heap_eta in E1, E2. cbn in E1, E2. exact (HU sG0 sG moG0 moG E1 E2 VG HUs).
  - intros sG moG sC moC HRX. exact (hf_free_safe tm nx U k n sG moG sC moC Hk HRX).
Qed.

End UBase.
