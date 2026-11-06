(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv ProgFullQ HeapFull StdioCore Stdio Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW NodeSim ProgSim USim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.USim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Import MSafeX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.NodeSimX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Lemma npk_inh segs : forall n f mo1, npeek segs n = Some f -> exists rsp, nstep n mo1 rsp mo1 [].
Proof.
  intros n f mo1 H. destruct n; cbn in H; try discriminate. exists (peek_rsp 0). apply nstep_peek. split; [reflexivity|]. split; [reflexivity|]. exists 0. split; [lia| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma minvX_vm_only mo mo' : vm_only mo mo' -> minvX mo -> minvX mo'.
Proof.
  intros HV HM. unfold minvX in *. apply (minv_vm_only (lf mo) (lf mo')); [| split; reflexivity | exact HM].
  destruct HV as (E1 & E2 & E3 & E4 & E5). unfold vm_only. repeat split; assumption.
Qed.

Lemma fdnode_xnode n : fdnode n -> xnode n.
Proof. destruct n; cbn; auto. Qed.
Lemma fdnodeX_xnode n : fdnodeX n -> xnode n.
Proof. destruct n; cbn; auto. Qed.
Lemma fdnodeX_fdnode n : fdnodeX n -> fdnode n.
Proof. destruct n; cbn; auto. Qed.

Section RelX.
(* [comment removed for export] *)
Context {G : Type}.
Variable nsafeP : node -> G -> Model -> Prop.
Variable gstepP : node -> resp -> G -> G.
Hypothesis GK_step : forall n rsp g, xnode n -> gstepP n rsp g = g.
(* [comment removed for export] *)
Context {HG HC : Type}.
Variable HOG : HeapOps HG hptr.
Variable HOC : HeapOps HC hptr.
(* [comment removed for export] *)
Variable segs : list Segment.
Variable hi : HeapSimI nsafeP gstepP HOG HOC (npeek segs).
(* [comment removed for export] *)
Hypothesis GK_safe : forall tm nx P n g s mo, xnode n -> hi_G hi tm nx P g s mo -> nsafe n mo -> nsafeP n g mo.

#[local] Notation PSG := (PState HG hptr).
#[local] Notation PSC := (PState HC hptr).
#[local] Notation npk := (npeek segs).
#[local] Notation relX := (USimX.relX G PSG PSC).
#[local] Notation usimS := (usimX nsafeP gstepP npk).
#[local] Abbreviation etwfX := (MSafeX.etwfX nsafeP gstepP).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RQ (tm : gmap N Z) (nx : N) (P : Z) : relX := fun g sG moG sC moC =>
  hi_G hi tm nx P g sG moG /\ hi_C hi tm nx P sC moC /\ minvX moG /\ m_halted moG = None
  /\ ps_libc sC = ps_libc sG /\ ps_outfile sC = ps_outfile sG /\ mqX moG moC /\ LCI (ps_libc sG).

(* [comment removed for export] *)
Definition RX (tm : gmap N Z) (nx : N) (P : Z) (U : PSG -> Model -> Prop) : relX :=
  fun g sG moG sC moC => RQ tm nx P g sG moG sC moC /\ U sG moG.

(* [comment removed for export] *)
Definition ustable (U : PSG -> Model -> Prop) : Prop :=
  forall (s s' : PSG) mo mo', ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> vm_only mo mo' -> U s mo -> U s' mo'.

(* [comment removed for export] *)
Definition UF (nx : N) (K : list kfe) (C : list (list byte * list byte)) : PSG -> Model -> Prop := fun s mo => FI nx K C (ps_libc s) mo.
#[using="Type"] Lemma UF_stable nx K C : ustable (UF nx K C).
Proof. intros s s' mo mo' EL _ VM H. unfold UF in *. rewrite EL. exact (FI_vm_only _ _ _ _ _ _ VM H). Qed.

Definition RU tm nx P K C := RX tm nx P (UF nx K C).

#[using="Type"] Lemma RX_RQ tm nx P U g sG moG sC moC : RX tm nx P U g sG moG sC moC -> RQ tm nx P g sG moG sC moC.
Proof. intros [H _]. exact H. Qed.
#[using="Type"] Lemma RX_U tm nx P U g sG moG sC moC : RX tm nx P U g sG moG sC moC -> U sG moG.
Proof. intros [_ H]. exact H. Qed.
#[using="Type"] Lemma RQ_G tm nx P g sG moG sC moC : RQ tm nx P g sG moG sC moC -> hi_G hi tm nx P g sG moG.
Proof. intros H. exact (proj1 H). Qed.
#[using="Type"] Lemma RQ_C tm nx P g sG moG sC moC : RQ tm nx P g sG moG sC moC -> hi_C hi tm nx P sC moC.
Proof. intros H. exact (proj1 (proj2 H)). Qed.
#[using="Type"] Lemma RQ_minvX tm nx P g sG moG sC moC : RQ tm nx P g sG moG sC moC -> minvX moG.
Proof. intros H. exact (proj1 (proj2 (proj2 H))). Qed.
#[using="Type"] Lemma RQ_halted tm nx P g sG moG sC moC : RQ tm nx P g sG moG sC moC -> m_halted moG = None.
Proof. intros H. exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.
#[using="Type"] Lemma RQ_libc tm nx P g sG moG sC moC : RQ tm nx P g sG moG sC moC -> ps_libc sC = ps_libc sG.
Proof. intros H. exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))). Qed.
#[using="Type"] Lemma RQ_outfile tm nx P g sG moG sC moC : RQ tm nx P g sG moG sC moC -> ps_outfile sC = ps_outfile sG.
Proof. intros H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.
#[using="Type"] Lemma RQ_mq tm nx P g sG moG sC moC : RQ tm nx P g sG moG sC moC -> mqX moG moC.
Proof. intros H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))). Qed.
#[using="Type"] Lemma RQ_lci tm nx P g sG moG sC moC : RQ tm nx P g sG moG sC moC -> LCI (ps_libc sG).
Proof. intros H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma RQ_fresh tm nx P g sG moG sC moC : RQ tm nx P g sG moG sC moC -> tm !! nx = None.
Proof. intros H. exact (hi_G_fresh hi _ _ _ _ _ _ (RQ_G _ _ _ _ _ _ _ _ H)). Qed.
#[using="Type"] Lemma RQ_toks_below tm nx P g sG moG sC moC k n : RQ tm nx P g sG moG sC moC -> tm !! k = Some n -> (k < nx)%N.
Proof. intros H Hk. exact (hi_G_below hi _ _ _ _ _ _ _ _ (RQ_G _ _ _ _ _ _ _ _ H) Hk). Qed.
#[using="Type"] Lemma RQ_pot tm nx P g sG moG sC moC : RQ tm nx P g sG moG sC moC -> pot_ok P.
Proof. intros H. exact (hi_G_pot hi _ _ _ _ _ _ (RQ_G _ _ _ _ _ _ _ _ H)). Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma blk_addr_range tm nx P g sG moG sC moC k n :
  RQ tm nx P g sG moG sC moC -> tm !! k = Some n -> 0 <= blk_addr HOG sG k /\ blk_addr HOG sG k + n <= 2^62 /\ 0 <= n.
Proof. intros H Hk. unfold blk_addr. exact (hi_G_addr hi _ _ _ _ _ _ _ _ (RQ_G _ _ _ _ _ _ _ _ H) Hk). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma RQ_same_heap tm nx P g (sG sG' : PSG) (sC sC' : PSC) moG moC :
  ps_heap sG' = ps_heap sG -> ps_heap sC' = ps_heap sC -> ps_libc sC' = ps_libc sG' -> ps_outfile sC' = ps_outfile sG' ->
  LCI (ps_libc sG') ->
  RQ tm nx P g sG moG sC moC -> RQ tm nx P g sG' moG sC' moC.
Proof.
  intros EG EC EL' EO' HL (HGa & HCa & MX & HH & EL & EO & MQ & _).
  split; [exact (hi_G_heap hi _ _ _ _ _ _ _ EG HGa)|]. split; [exact (hi_C_heap hi _ _ _ _ _ _ EC HCa)|].
  exact (conj MX (conj HH (conj EL' (conj EO' (conj MQ HL))))).
Qed.

#[using="Type"] Lemma ps_heap_set_libcX {H} (l : libc_st hptr) (s : PState H hptr) : ps_heap (set_libc l s) = ps_heap s.
Proof. destruct s; reflexivity. Qed.
#[using="Type"] Lemma ps_heap_set_outfileX {H} (o : option hptr) (s : PState H hptr) : ps_heap (set_outfile o s) = ps_heap s.
Proof. destruct s; reflexivity. Qed.

#[using="Type"] Lemma RQ_libc_upd tm nx P g f sG moG sC moC :
  (forall l, LCI l -> LCI (f l)) ->
  RQ tm nx P g sG moG sC moC -> RQ tm nx P g (set_libc (f (ps_libc sG)) sG) moG (set_libc (f (ps_libc sC)) sC) moC.
Proof.
  intros Hf HR. pose proof (RQ_libc _ _ _ _ _ _ _ _ HR) as EL. pose proof (RQ_outfile _ _ _ _ _ _ _ _ HR) as EO. pose proof (RQ_lci _ _ _ _ _ _ _ _ HR) as HL.
  eapply RQ_same_heap; [apply ps_heap_set_libcX| apply ps_heap_set_libcX| destruct sG, sC; cbn in *; congruence| destruct sG, sC; cbn in *; congruence| destruct sG; cbn in *; apply Hf; exact HL| exact HR].
Qed.

#[using="Type"] Lemma RQ_outfile_upd tm nx P g o sG moG sC moC :
  RQ tm nx P g sG moG sC moC -> RQ tm nx P g (set_outfile o sG) moG (set_outfile o sC) moC.
Proof.
  intros HR. pose proof (RQ_libc _ _ _ _ _ _ _ _ HR) as EL. pose proof (RQ_outfile _ _ _ _ _ _ _ _ HR) as EO. pose proof (RQ_lci _ _ _ _ _ _ _ _ HR) as HL.
  eapply RQ_same_heap; [apply ps_heap_set_outfileX| apply ps_heap_set_outfileX| destruct sG, sC; cbn in *; congruence| destruct sG, sC; cbn in *; congruence| destruct sG; exact HL| exact HR].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma RQ_xstep tm nx P g sG moG sC moC n n' rspG rspC moG' moC' evs evs' :
  xnode n -> node_static_ok n -> xnode n' ->
  RQ tm nx P g sG moG sC moC -> nstep n moG rspG moG' evs -> nstep n' moC rspC moC' evs' -> mqX moG' moC' ->
  RQ tm nx P (gstepP n rspG g) sG moG' sC moC'.
Proof.
  intros Hn Hso Hn' (HGa & HCa & MX & HH & EL & EO & MQ & HL) HstG HstC MQ'.
  destruct (minvX_preserved n moG rspG moG' evs Hn Hso MX HH HstG) as [HH' MX'].
  pose proof (mq_haltedX _ _ MQ') as HC'.
  split; [exact (hi_G_step hi _ _ _ _ _ _ _ _ _ _ Hn HstG HH' HGa)|].
  split; [eapply (hi_C_step hi); [exact Hn'| exact HstC| rewrite HC'; exact HH'| exact HCa]|].
  exact (conj MX' (conj HH' (conj EL (conj EO (conj MQ' HL))))).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma RQ_after tm nx P g tm' nx' P' g' (sG sG' : PSG) (sC sC' : PSC) moG moC moG' moC' :
  RQ tm nx P g sG moG sC moC ->
  hi_G hi tm' nx' P' g' sG' moG' -> hi_C hi tm' nx' P' sC' moC' ->
  ps_libc sG' = ps_libc sG -> ps_outfile sG' = ps_outfile sG -> ps_libc sC' = ps_libc sC -> ps_outfile sC' = ps_outfile sC ->
  vm_only moG moG' -> vm_only moC moC' ->
  RQ tm' nx' P' g' sG' moG' sC' moC'.
Proof.
  intros (HGa & HCa & MX & HH & EL & EO & MQ & HL) HG' HC' E1 E2 E3 E4 VG VC.
  split; [exact HG'|]. split; [exact HC'|]. split; [exact (minvX_vm_only _ _ VG MX)|].
  split; [destruct VG as (_ & _ & EH & _); rewrite EH; exact HH|].
  split; [congruence|]. split; [congruence|]. split; [| rewrite E1; exact HL].
  eapply mq_vm_rX; [exact VC|]. eapply mq_vm_lX; [exact VG| exact MQ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ru_bind {A B} := @usimX_bind_eq G nsafeP gstepP PSG PSC npk (npk_inh segs) A B.
Definition ru_bind2 {A B A' B'} := @usimX_bind G nsafeP gstepP PSG PSC npk (npk_inh segs) A B A' B'.
Definition ru_seq {A B A' B'} := @usimX_seq G nsafeP gstepP PSG PSC npk (npk_inh segs) A B A' B'.

#[using="Type"] Lemma ru_ret {A} (R : relX) (R1 : A -> relX) (a : A) :
  (forall g sG moG sC moC, R g sG moG sC moC -> R1 a g sG moG sC moC) -> usimS R (mret a) (mret a) (eqpost R1).
Proof. intros H. apply usimX_ret. intros. split; [reflexivity| apply H; assumption]. Qed.

#[using="Type"] Lemma ru_post {A} (R : relX) (R1 R2 : A -> relX) (m : Monad.M PSG A) (m' : Monad.M PSC A) :
  usimS R m m' (eqpost R1) -> (forall a g sG moG sC moC, R1 a g sG moG sC moC -> R2 a g sG moG sC moC) -> usimS R m m' (eqpost R2).
Proof. intros H HI. eapply usimX_post; [exact H|]. intros a b ? ? ? ? ? [-> H1]. split; [reflexivity| apply HI; exact H1]. Qed.

#[using="Type"] Lemma ru_pre {A B} (R R' : relX) (m : Monad.M PSG A) (m' : Monad.M PSC B) Q :
  usimS R' m m' Q -> (forall g sG moG sC moC, R g sG moG sC moC -> R' g sG moG sC moC) -> usimS R m m' Q.
Proof. intros H HI. eapply usimX_pre; [exact H| exact HI]. Qed.

#[using="Type"] Lemma ru_munr {A B} (R : relX) (m' : Monad.M PSC B) (Q : A -> B -> relX) :
  (forall g sG moG sC moC, R g sG moG sC moC -> False) -> usimS R munr m' Q.
Proof. apply usimX_munr. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ru_use {A B} (R : relX) (m : Monad.M PSG A) (m' : Monad.M PSC B) Q :
  (forall g sG moG sC moC, R g sG moG sC moC -> usimS R m m' Q) -> usimS R m m' Q.
Proof. intros H g sG moG sC moC HR. exact (H _ _ _ _ _ HR _ _ _ _ _ HR). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ru_bind_retl {A B} (R : relX) (a : A) (k : A -> Monad.M PSG B) (k' : A -> Monad.M PSC B) Q :
  usimS R (k a) (k' a) Q -> usimS R (mbind (mret a) k) (mbind (mret a) k') Q.
Proof. intros H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ru_get tm nx P U :
  usimS (RX tm nx P U) mget mget
        (fun a b g sG moG sC moC => a = sG /\ b = sC /\ ps_libc b = ps_libc a /\ ps_outfile b = ps_outfile a /\ RX tm nx P U g sG moG sC moC).
Proof.
  eapply usimX_post; [apply usimX_get|]. intros a b g sG moG sC moC (-> & -> & HR).
  split; [reflexivity|]. split; [reflexivity|]. split; [exact (RQ_libc _ _ _ _ _ _ _ _ (RX_RQ _ _ _ _ _ _ _ _ _ HR))|].
  split; [exact (RQ_outfile _ _ _ _ _ _ _ _ (RX_RQ _ _ _ _ _ _ _ _ _ HR))| exact HR].
Qed.

#[using="Type"] Lemma ru_rd_lc tm nx P U :
  usimS (RX tm nx P U) (rd_lc ps_libc) (rd_lc ps_libc)
        (eqpost (fun l => fun g sG moG sC moC => l = ps_libc sG /\ LCI l /\ RX tm nx P U g sG moG sC moC)).
Proof.
  unfold rd_lc. eapply ru_bind2; [apply usimX_get|]. intros a b. apply usimX_ret.
  intros g sG moG sC moC (-> & -> & HR). split; [symmetry; exact (RQ_libc _ _ _ _ _ _ _ _ (RX_RQ _ _ _ _ _ _ _ _ _ HR))|].
  split; [reflexivity|]. split; [exact (RQ_lci _ _ _ _ _ _ _ _ (RX_RQ _ _ _ _ _ _ _ _ _ HR))| exact HR].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ru_upd_lc tm nx P U U' f :
  (forall l, LCI l -> LCI (f l)) ->
  (forall (s : PSG) mo, U s mo -> LCI (ps_libc s) -> U' (set_libc (f (ps_libc s)) s) mo) ->
  usimS (RX tm nx P U) (upd_lc ps_libc set_libc f) (upd_lc ps_libc set_libc f) (eqpost (fun _ => RX tm nx P U')).
Proof.
  intros Hf HU. unfold upd_lc. apply usimX_upd. intros g sG moG sC moC [HR HUs]. split; [reflexivity|]. split.
  - apply RQ_libc_upd; [exact Hf| exact HR].
  - apply HU; [exact HUs| exact (RQ_lci _ _ _ _ _ _ _ _ HR)].
Qed.

#[using="Type"] Lemma ru_upd_outfile tm nx P U o :
  (forall (s : PSG) mo, U s mo -> U (set_outfile o s) mo) ->
  usimS (RX tm nx P U) (mupd (set_outfile o)) (mupd (set_outfile o)) (eqpost (fun _ => RX tm nx P U)).
Proof. intros HU. apply usimX_upd. intros g sG moG sC moC [HR HUs]. split; [reflexivity|]. split; [apply RQ_outfile_upd; exact HR| apply HU; exact HUs]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition unode {A} (n : node) (dec : resp -> option A) (U : PSG -> Model -> Prop) (U' : A -> PSG -> Model -> Prop) : Prop :=
  forall (s : PSG) mo, U s mo -> minvX mo ->
    nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ U' a s mo'.

#[using="Type"] Lemma npk_fdnode n : fdnodeX n -> npk n = None.
Proof. destruct n; cbn; intros H; try destruct H; reflexivity. Qed.

#[using="GK_safe"] Theorem ru_sys {A} tm nx P U U' n (dec : resp -> option A) :
  fdnodeX n -> unode n dec U U' ->
  usimS (RX tm nx P U) (msys n dec) (msys n dec) (eqpost (fun a => RX tm nx P (U' a))).
Proof.
  intros Hn HU. pose proof (fdnodeX_xnode n Hn) as Hx. apply usimX_sys; [apply npk_fdnode; exact Hn|].
  intros g sG moG sC moC [HR HUs]. pose proof (RQ_minvX _ _ _ _ _ _ _ _ HR) as MI.
  destruct (HU sG moG HUs MI) as [Hs Hk]. split; [apply (GK_safe tm nx P _ g sG moG); [exact Hx| exact (RQ_G _ _ _ _ _ _ _ _ HR)| exact Hs]|].
  split; [intros rspG moG' evs Hst; destruct (Hk _ _ _ Hst) as (a & Ha & _); exists a; exact Ha|]. split.
  - intros rspG moG' evs a HstG Hd.
    destruct (nstep_crossX n moG moC rspG moG' evs Hn (RQ_mq _ _ _ _ _ _ _ _ HR) HstG) as (moC' & HstC & X).
    exists rspG, moC', a. split; [exact HstC|]. split; [exact Hd|]. split; [reflexivity|]. split.
    + eapply RQ_xstep; [exact Hx| exact (nstep_static_ok n moG rspG moG' evs (fdnodeX_fdnode n Hn) HstG)| exact Hx| exact HR| exact HstG| exact HstC| exact (proj1 X)].
    + destruct (Hk _ _ _ HstG) as (a' & Ha' & HU'). assert (a' = a) as -> by congruence. exact HU'.
  - intros code moG' Hex. destruct (nexit_onlyX _ _ _ _ Hex) as [c ->]. destruct Hn.
Qed.

#[using="GK_safe"] Theorem ru_read tm nx P U U' fd bufG bufC count :
  unode (NRead fd bufG count) (dec_read bufG count) U U' ->
  usimS (RX tm nx P U) (msys (NRead fd bufG count) (dec_read bufG count)) (msys (NRead fd bufC count) (dec_read bufC count))
        (eqpost (fun a => RX tm nx P (U' a))).
Proof.
  intros HU. apply usimX_sys; [reflexivity|].
  intros g sG moG sC moC [HR HUs]. pose proof (RQ_minvX _ _ _ _ _ _ _ _ HR) as MI.
  destruct (HU sG moG HUs MI) as [Hs Hk]. split; [apply (GK_safe tm nx P _ g sG moG); [exact I| exact (RQ_G _ _ _ _ _ _ _ _ HR)| exact Hs]|].
  split; [intros rspG moG' evs Hst; destruct (Hk _ _ _ Hst) as (a & Ha & _); exists a; exact Ha|]. split.
  - intros rspG moG' evs a HstG Hd.
    destruct (nstep_cross_readX fd bufG bufC count moG moC rspG moG' evs (RQ_mq _ _ _ _ _ _ _ _ HR) HstG) as (rspC & moC' & HstC & X & Ed).
    exists rspC, moC', a. split; [exact HstC|]. split; [rewrite Ed; exact Hd|]. split; [reflexivity|]. split.
    + eapply (RQ_xstep tm nx P g sG moG sC moC (NRead fd bufG count) (NRead fd bufC count)); try exact I; eauto. exact (proj1 X).
    + destruct (Hk _ _ _ HstG) as (a' & Ha' & HU'). assert (a' = a) as -> by congruence. exact HU'.
  - intros code moG' Hex. destruct Hex.
Qed.

#[using="GK_safe"] Theorem ru_readv tm nx P U U' fd dstsG dstsC :
  map snd dstsC = map snd dstsG -> lens_okX dstsG ->
  unode (NReadv fd dstsG) (dec_readv dstsG) U U' ->
  usimS (RX tm nx P U) (msys (NReadv fd dstsG) (dec_readv dstsG)) (msys (NReadv fd dstsC) (dec_readv dstsC))
        (eqpost (fun a => RX tm nx P (U' a))).
Proof.
  intros Hl HLo HU. apply usimX_sys; [reflexivity|].
  intros g sG moG sC moC [HR HUs]. pose proof (RQ_minvX _ _ _ _ _ _ _ _ HR) as MI.
  destruct (HU sG moG HUs MI) as [Hs Hk]. split; [apply (GK_safe tm nx P _ g sG moG); [exact I| exact (RQ_G _ _ _ _ _ _ _ _ HR)| exact Hs]|].
  split; [intros rspG moG' evs Hst; destruct (Hk _ _ _ Hst) as (a & Ha & _); exists a; exact Ha|]. split.
  - intros rspG moG' evs a HstG Hd.
    destruct (nstep_cross_readvX fd dstsG dstsC moG moC rspG moG' evs Hl HLo (RQ_mq _ _ _ _ _ _ _ _ HR) HstG) as (rspC & moC' & HstC & X & Ed).
    exists rspC, moC', a. split; [exact HstC|]. split; [rewrite Ed; exact Hd|]. split; [reflexivity|]. split.
    + eapply (RQ_xstep tm nx P g sG moG sC moC (NReadv fd dstsG) (NReadv fd dstsC)); try exact I; eauto. exact (proj1 X).
    + destruct (Hk _ _ _ HstG) as (a' & Ha' & HU'). assert (a' = a) as -> by congruence. exact HU'.
  - intros code moG' Hex. destruct Hex.
Qed.

#[using="GK_safe"] Theorem ru_exit tm nx P U c (Q : Empty_set -> Empty_set -> relX) :
  usimS (RX tm nx P U) (msys (NExit c) dec_exit) (msys (NExit c) dec_exit) Q.
Proof.
  apply usimX_sys; [reflexivity|]. intros g sG moG sC moC [HR _]. split; [apply (GK_safe tm nx P _ g sG moG); [exact I| exact (RQ_G _ _ _ _ _ _ _ _ HR)| exact I]|].
  split; [intros ? ? ? Hst; destruct Hst|]. split.
  - intros rspG moG' evs a HstG _. destruct HstG.
  - intros code moG' Hex. exact (nexit_crossX c moG moC code moG' (RQ_mq _ _ _ _ _ _ _ _ HR) Hex).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma ru_heap_op {A} tm nx P U U' tm' nx' P' (res : A) (mG : Monad.M PSG (option A)) (mC : Monad.M PSC (option A)) :
  (forall (s s' : PSG) mo mo', ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> vm_only mo mo' -> U s mo -> U' s' mo') ->
  (forall g sG moG, hi_G hi tm nx P g sG moG -> gop nsafeP gstepP mG res sG g moG (gpost (hi_G hi) tm' nx' P' sG moG)) ->
  (forall sC moC, hi_C hi tm nx P sC moC -> cop npk mC res sC moC (cpost (hi_C hi) tm' nx' P' sC moC)) ->
  usimS (RX tm nx P U) mG mC (fun a b g sG moG sC moC => a = Some res /\ b = Some res /\ RX tm' nx' P' U' g sG moG sC moC).
Proof.
  intros HU HGop HCop. apply usimX_of_paths. intros g sG moG sC moC [HR HUs].
  pose proof HR as (HGa & HCa & MX & HH & EL & EO & MQ & HL).
  destruct (HGop g sG moG HGa) as (ET & SIL & NOX). split; [| split; [exact NOX|]].
  { eapply etwfX_mono; [exact ET| intros; exact I]. }
  intros trG a sG' g' moG' Hp.
  pose proof (twfX_tpathX _ _ _ _ _ _ _ _ _ _ ET Hp) as LF. cbn [fst snd] in LF. destruct LF as (-> & HG' & E1 & E2 & E3 & VG).
  pose proof (SIL _ _ _ (tpathX_tpath _ _ _ _ _ _ _ _ Hp)) as ->.
  eapply wreach_mono; [exact (HCop sC moC HCa)|]. intros tr r moC' (-> & sC' & -> & HC' & E4 & E5 & E6 & VC).
  exists (Some res), sC'. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - eapply RQ_after; [exact HR| exact HG'| exact HC'| exact E1| exact E2| exact E4| exact E5| exact VG| exact VC].
  - exact (HU sG sG' moG moG' E1 E2 VG HUs).
Qed.

#[using="Type"] Lemma ru_heap_opu tm nx P U U' tm' nx' P' (mG : Monad.M PSG unit) (mC : Monad.M PSC unit) :
  (forall (s s' : PSG) mo mo', ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> vm_only mo mo' -> U s mo -> U' s' mo') ->
  (forall g sG moG, hi_G hi tm nx P g sG moG -> gopu nsafeP gstepP mG sG g moG (gpost (hi_G hi) tm' nx' P' sG moG)) ->
  (forall sC moC, hi_C hi tm nx P sC moC -> copu npk mC sC moC (cpost (hi_C hi) tm' nx' P' sC moC)) ->
  usimS (RX tm nx P U) mG mC (eqpost (fun _ => RX tm' nx' P' U')).
Proof.
  intros HU HGop HCop. apply usimX_of_paths. intros g sG moG sC moC [HR HUs].
  pose proof HR as (HGa & HCa & MX & HH & EL & EO & MQ & HL).
  destruct (HGop g sG moG HGa) as (ET & SIL & NOX). split; [| split; [exact NOX|]].
  { eapply etwfX_mono; [exact ET| intros; exact I]. }
  intros trG [] sG' g' moG' Hp.
  pose proof (twfX_tpathX _ _ _ _ _ _ _ _ _ _ ET Hp) as LF. cbn [fst snd] in LF. destruct LF as (HG' & E1 & E2 & E3 & VG).
  pose proof (SIL _ _ _ (tpathX_tpath _ _ _ _ _ _ _ _ Hp)) as ->.
  eapply wreach_mono; [exact (HCop sC moC HCa)|]. intros tr r moC' (-> & sC' & -> & HC' & E4 & E5 & E6 & VC).
  exists tt, sC'. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - eapply RQ_after; [exact HR| exact HG'| exact HC'| exact E1| exact E2| exact E4| exact E5| exact VG| exact VC].
  - exact (HU sG sG' moG moG' E1 E2 VG HUs).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem ru_pmalloc tm nx P U U' n :
  (forall (s s' : PSG) mo mo', ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> vm_only mo mo' -> U s mo -> U' s' mo') ->
  pre_malloc tm P n ->
  usimS (RX tm nx P U) (pmalloc HOG n) (pmalloc HOC n)
        (eqpost (fun a => fun g sG moG sC moC => a = Some nx /\ RX (<[nx := n]> tm) (N.succ nx) (P + n1 n) U' g sG moG sC moC)).
Proof.
  intros HU PRE. unfold pmalloc.
  eapply ru_bind2.
  - apply (ru_heap_op tm nx P U U' (<[nx := n]> tm) (N.succ nx) (P + n1 n) nx (ho_malloc HOG n) (ho_malloc HOC n) HU).
    + intros g sG moG HGa. exact (hi_mallocG hi _ _ _ _ _ _ n HGa PRE).
    + intros sC moC HCa. exact (hi_mallocC hi _ _ _ _ _ n HCa PRE).
  - intros a b. apply usimX_pure; intros ->. apply usimX_pure; intros ->. cbn [enomem_on_null].
    apply usimX_ret. intros ? ? ? ? ? H. split; [reflexivity|]. split; [reflexivity| exact H].
Qed.

#[using="Type"] Theorem ru_pcalloc tm nx P U U' m n :
  (forall (s s' : PSG) mo mo', ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> vm_only mo mo' -> U s mo -> U' s' mo') ->
  pre_calloc tm P m n ->
  usimS (RX tm nx P U) (pcalloc HOG m n) (pcalloc HOC m n)
        (eqpost (fun a => fun g sG moG sC moC => a = Some nx /\ RX (<[nx := m * n]> tm) (N.succ nx) (P + n1 (m * n)) U' g sG moG sC moC)).
Proof.
  intros HU PRE. unfold pcalloc.
  eapply ru_bind2.
  - apply (ru_heap_op tm nx P U U' (<[nx := m * n]> tm) (N.succ nx) (P + n1 (m * n)) nx (ho_calloc HOG m n) (ho_calloc HOC m n) HU).
    + intros g sG moG HGa. exact (hi_callocG hi _ _ _ _ _ _ m n HGa PRE).
    + intros sC moC HCa. exact (hi_callocC hi _ _ _ _ _ m n HCa PRE).
  - intros a b. apply usimX_pure; intros ->. apply usimX_pure; intros ->. cbn [enomem_on_null].
    apply usimX_ret. intros ? ? ? ? ? H. split; [reflexivity|]. split; [reflexivity| exact H].
Qed.

#[using="Type"] Theorem ru_prealloc tm nx P U U' k n n' :
  (forall (s s' : PSG) mo mo', ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> vm_only mo mo' -> U s mo -> U' s' mo') ->
  pre_realloc tm P k n n' ->
  usimS (RX tm nx P U) (prealloc HOG k n') (prealloc HOC k n')
        (eqpost (fun a => fun g sG moG sC moC => a = Some nx /\ RX (<[nx := n']> (delete k tm)) (N.succ nx) (P + n') U' g sG moG sC moC)).
Proof.
  intros HU PRE. unfold prealloc.
  eapply ru_bind2.
  - apply (ru_heap_op tm nx P U U' (<[nx := n']> (delete k tm)) (N.succ nx) (P + n') nx (ho_realloc HOG k n') (ho_realloc HOC k n') HU).
    + intros g sG moG HGa. exact (hi_reallocG hi _ _ _ _ _ _ k n n' HGa PRE).
    + intros sC moC HCa. exact (hi_reallocC hi _ _ _ _ _ k n n' HCa PRE).
  - intros a b. apply usimX_pure; intros ->. apply usimX_pure; intros ->. cbn [enomem_on_null].
    apply usimX_ret. intros ? ? ? ? ? H. split; [reflexivity|]. split; [reflexivity| exact H].
Qed.

#[using="Type"] Theorem ru_pfree tm nx P U U' k n :
  (forall (s s' : PSG) mo mo', ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> vm_only mo mo' -> U s mo -> U' s' mo') ->
  pre_free tm k n ->
  usimS (RX tm nx P U) (pfree HOG k) (pfree HOC k) (eqpost (fun _ => RX (delete k tm) nx P U')).
Proof.
  intros HU PRE. unfold pfree.
  apply (ru_heap_opu tm nx P U U' (delete k tm) nx P (ho_free HOG k) (ho_free HOC k) HU).
  - intros g sG moG HGa. exact (hi_freeG hi _ _ _ _ _ _ k n HGa PRE).
  - intros sC moC HCa. exact (hi_freeC hi _ _ _ _ _ k n HCa PRE).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma live1_insert tm k n : tm !! k = None -> live1 (<[k := n]> tm) = n1 n + live1 tm.
Proof. intros Hk. unfold live1. rewrite (zsum_perm _ _ (Permutation_map n1 (sizes_insert tm k n Hk))). reflexivity. Qed.

#[using="Type"] Lemma live1_delete tm k n : tm !! k = Some n -> live1 tm = n1 n + live1 (delete k tm).
Proof. intros Hk. unfold live1. rewrite (zsum_perm _ _ (Permutation_map n1 (sizes_delete tm k n Hk))). reflexivity. Qed.

#[using="Type"] Lemma live1_empty : live1 (∅ : gmap N Z) = 0.
Proof. unfold live1. rewrite sizes_empty. reflexivity. Qed.

#[using="Type"] Lemma live1_nonneg tm : 0 <= live1 tm.
Proof. unfold live1. induction (sizes tm) as [|x l IH]; [reflexivity|]. cbn [map]. rewrite zsum_cons. unfold n1 at 1. lia. Qed.

#[using="Type"] Lemma n1_pos n : 1 <= n1 n. Proof. unfold n1. lia. Qed.
#[using="Type"] Lemma n1_le n : 0 <= n -> n1 n <= n + 1. Proof. unfold n1. lia. Qed.
#[using="Type"] Lemma n1_id n : 1 <= n -> n1 n = n. Proof. unfold n1. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frames.
Variable FOG : FrameOps (H:=HG) (hptr:=hptr).
Variable FOC : FrameOps (H:=HC) (hptr:=hptr).
Variable fi : FrameSimI hi FOG FOC.

(* [comment removed for export] *)
Definition finsens (R : relX) : Prop :=
  (forall g sG moG sC moC sG' sC', fi_eqG fi sG sG' -> fi_eqC fi sC sC' -> R g sG moG sC moC -> R g sG' moG sC' moC)
  /\ (forall g sG moG sC moC, R g sG moG sC moC -> exists tm nx P, hi_G hi tm nx P g sG moG).

#[using="Type"] Lemma usimX_fenter {A B} (R : relX) f (mG : Monad.M PSG A) (mC : Monad.M PSC B) (Q : A -> B -> relX) :
  finsens R -> usimS R mG mC Q -> usimS R (fo_enter FOG A f mG) (fo_enter FOC B f mC) Q.
Proof.
  intros [HI HH] H g sG moG sC moC HR. split; [| split].
  - intros trG a sG' g' moG' Hp. destruct (fi_enterG_path fi A f mG sG g moG trG _ g' moG' Hp) as (sG1 & E1 & Hp1).
    apply (fi_enterC_reach fi). intros sC1 E2.
    destruct (H g sG1 moG sC1 moC (HI _ _ _ _ _ _ _ E1 E2 HR)) as (HP & _ & _). exact (HP _ _ _ _ _ Hp1).
  - intros trG Hx. destruct (fi_enterG_exit fi A f mG sG moG trG Hx) as (sG1 & E1 & Hx1).
    apply (fi_enterC_exit fi). intros sC1 E2.
    destruct (H g sG1 moG sC1 moC (HI _ _ _ _ _ _ _ E1 E2 HR)) as (_ & HE & _). exact (HE _ Hx1).
  - unfold MSafeX.etwfX. destruct (HH _ _ _ _ _ HR) as (tm0 & nx0 & P0 & HG0). apply (fi_enterG_safe fi A f mG tm0 nx0 P0 sG g moG _ HG0). intros sG1 E1.
    destruct (H g sG1 moG sC moC (HI _ _ _ _ _ _ _ E1 (fi_eqC_refl fi sC) HR)) as (_ & _ & HS). exact HS.
Qed.

#[using="Type"] Lemma usimX_fret {A} (R : relX) f (x : A) :
  finsens R -> usimS R (fo_ret FOG A f x) (fo_ret FOC A f x) (eqpost (fun _ => R)).
Proof.
  intros [HI _] g sG moG sC moC HR.
  destruct (fi_retG fi A f x sG) as (sG1 & E1 & EG). destruct (fi_retC fi A f x sC) as (sC1 & E2 & EC). rewrite EG, EC.
  split; [| split].
  - intros trG a sG' g' moG' Hp. cbn in Hp. destruct Hp as (E & -> & -> & ->). injection E as <- <-.
    apply wreach_ret. exists x, sC1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact (HI _ _ _ _ _ _ _ E1 E2 HR).
  - intros trG Hx. destruct Hx.
  - exact I.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma usimX_fret_of_ret {A B} (R : relX) f (x : A) (y : B) (Q : A -> B -> relX) :
  finsens R -> usimS R (mret x) (mret y) Q -> usimS R (fo_ret FOG A f x) (fo_ret FOC B f y) Q.
Proof.
  intros [HI _] H g sG moG sC moC HR.
  destruct (fi_retG fi A f x sG) as (sG1 & E1 & EG). destruct (fi_retC fi B f y sC) as (sC1 & E2 & EC). rewrite EG, EC.
  destruct (H g sG1 moG sC1 moC (HI _ _ _ _ _ _ _ E1 E2 HR)) as (HP & _ & _).
  split; [| split].
  - intros trG a sG' g' moG' Hp. cbn in Hp. destruct Hp as (E & -> & -> & ->). injection E as <- <-.
    exact (HP [] x sG1 g moG ltac:(cbn; repeat split; reflexivity)).
  - intros trG Hx. destruct Hx.
  - exact I.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma finsens_RQ tm nx P : finsens (RQ tm nx P).
Proof.
  split.
  - intros g sG moG sC moC sG' sC' E1 E2 (HGa & HCa & MX & HH & EL & EO & MQ & HL).
    destruct (fi_eqG_libc fi _ _ E1) as [L1 O1]. destruct (fi_eqC_libc fi _ _ E2) as [L2 O2].
    split; [exact (fi_hiG fi _ _ _ _ _ _ _ E1 HGa)|]. split; [exact (fi_hiC fi _ _ _ _ _ _ E2 HCa)|].
    split; [exact MX|]. split; [exact HH|]. split; [rewrite L1, L2; exact EL|]. split; [rewrite O1, O2; exact EO|]. split; [exact MQ|]. rewrite L1. exact HL.
  - intros g sG moG sC moC HR. exists tm, nx, P. exact (RQ_G _ _ _ _ _ _ _ _ HR).
Qed.

(* [comment removed for export] *)
Definition ulibc (U : PSG -> Model -> Prop) : Prop :=
  forall (s s' : PSG) mo, ps_libc s' = ps_libc s -> ps_outfile s' = ps_outfile s -> U s mo -> U s' mo.
#[using="Type"] Lemma ulibc_of_ustable U : ustable U -> ulibc U.
Proof. intros H s s' mo EL EO HU. apply (H s s' mo mo EL EO); [| exact HU]. repeat split; reflexivity. Qed.

#[using="Type"] Lemma finsens_RX tm nx P U : ulibc U -> finsens (RX tm nx P U).
Proof.
  intros HU. destruct (finsens_RQ tm nx P) as [F1 F2]. split.
  - intros g sG moG sC moC sG' sC' E1 E2 [HR HUs]. split; [exact (F1 _ _ _ _ _ _ _ E1 E2 HR)|].
    destruct (fi_eqG_libc fi _ _ E1) as [L1 O1]. exact (HU _ _ _ L1 O1 HUs).
  - intros g sG moG sC moC [HR _]. exact (F2 _ _ _ _ _ HR).
Qed.
#[using="Type"] Lemma finsens_pure (phi : Prop) (R : relX) : finsens R -> finsens (fun g sG moG sC moC => phi /\ R g sG moG sC moC).
Proof.
  intros [F1 F2]. split.
  - intros g sG moG sC moC sG' sC' E1 E2 [Hp HR]. exact (conj Hp (F1 _ _ _ _ _ _ _ E1 E2 HR)).
  - intros g sG moG sC moC [_ HR]. exact (F2 _ _ _ _ _ HR).
Qed.
#[using="Type"] Lemma finsens_ex {X} (R : X -> relX) : (forall x, finsens (R x)) -> finsens (fun g sG moG sC moC => exists x, R x g sG moG sC moC).
Proof.
  intros H. split.
  - intros g sG moG sC moC sG' sC' E1 E2 [x HR]. exists x. exact (proj1 (H x) _ _ _ _ _ _ _ E1 E2 HR).
  - intros g sG moG sC moC [x HR]. exact (proj2 (H x) _ _ _ _ _ HR).
Qed.
#[using="Type"] Lemma finsens_mo (I : Model -> Prop) (R : relX) : finsens R -> finsens (fun g sG moG sC moC => R g sG moG sC moC /\ I moG).
Proof.
  intros [F1 F2]. split.
  - intros g sG moG sC moC sG' sC' E1 E2 [HR Hi]. exact (conj (F1 _ _ _ _ _ _ _ E1 E2 HR) Hi).
  - intros g sG moG sC moC [HR _]. exact (F2 _ _ _ _ _ HR).
Qed.

(* [comment removed for export] *)
#[using="FOC fi"] Lemma RQ_siteG tm nx P g sG moG sC moC site a :
  RQ tm nx P g sG moG sC moC -> fo_site FOG sG site = Some a -> 0 <= a /\ a + 8192 <= 2^62.
Proof. intros HR E. exact (fi_siteG fi _ _ _ _ _ _ _ _ (RQ_G _ _ _ _ _ _ _ _ HR) E). Qed.
End Frames.

(* [comment removed for export] *)
#[using="Type"] Lemma n1_small n : 0 <= n <= NMAXA -> n1 n <= NMAXA. Proof. unfold n1, NMAXA. lia. Qed.

End RelX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record UKit := mkUKit {
  uk_G : Type;
  uk_nsafeP : node -> uk_G -> Model -> Prop;
  uk_gstepP : node -> resp -> uk_G -> uk_G;
  uk_GK_step : forall n rsp g, xnode n -> uk_gstepP n rsp g = g;
  uk_HG : Type;
  uk_HC : Type;
  uk_HOG : HeapOps uk_HG hptr;
  uk_HOC : HeapOps uk_HC hptr;
  uk_eqbG : ho_eqb uk_HOG = N.eqb;
  uk_eqbC : ho_eqb uk_HOC = N.eqb;
  uk_segs : list Segment;
  uk_hi : HeapSimI uk_nsafeP uk_gstepP uk_HOG uk_HOC (npeek uk_segs);
  uk_GK_safe : forall tm nx P n g s mo, xnode n -> hi_G uk_hi tm nx P g s mo -> nsafe n mo -> uk_nsafeP n g mo;
  (* [comment removed for export] *)
  uk_FOG : FrameOps (H:=uk_HG) (hptr:=hptr);
  uk_FOC : FrameOps (H:=uk_HC) (hptr:=hptr);
  uk_fi : FrameSimI uk_hi uk_FOG uk_FOC
}.
