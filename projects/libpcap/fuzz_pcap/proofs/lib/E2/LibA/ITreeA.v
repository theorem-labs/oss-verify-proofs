(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition alw := word -> Prop.
Definition alw_le (A A' : alw) : Prop := forall p, A p -> A' p.
Lemma alw_le_refl : forall A, alw_le A A. Proof. intros A p H; exact H. Qed.
Lemma alw_le_trans : forall A B C, alw_le A B -> alw_le B C -> alw_le A C.
Proof. intros A B C H1 H2 p H. apply H2, H1, H. Qed.

(* [comment removed for export] *)
Definition fp_le (R R' : footprint) : Prop := forall b j, R b j -> R' b j.
Lemma fp_le_refl : forall R, fp_le R R. Proof. intros R b j H; exact H. Qed.
Lemma fp_le_trans : forall A B C, fp_le A B -> fp_le B C -> fp_le A C.
Proof. intros A B C H1 H2 b j H. apply H2, H1, H. Qed.
Lemma rng_fp_le : forall R R' lo len, fp_le R R' -> rng R lo len -> rng R' lo len.
Proof. intros R R' lo len HL (A & B & H). split; [exact A|]. split; [exact B|]. intros b j Hb Hj. apply HL, H; assumption. Qed.

(* [comment removed for export] *)
Lemma fp_ok_mono : forall lz lz' (A A' : alw),
  (forall p, page_in_ranges p lz' = true -> page_in_ranges p lz = true) ->
  alw_le A A' ->
  fp_le (fp_ok lz A) (fp_ok lz' A').
Proof.
  intros lz lz' A A' SUB LE b j H k Hk Hb.
  destruct (H k Hk Hb) as [NL | AL].
  - left. destruct (page_in_ranges _ lz') eqn:E; [|reflexivity]. apply SUB in E. congruence.
  - right. apply LE, AL.
Qed.

Section ITreeA.

Variable node : Type.
Variable segs : list Segment.

(* [comment removed for export] *)
Variable at_node : node -> footprint -> machine_state -> Prop.
(* [comment removed for export] *)
Variable sil : footprint -> machine_state -> machine_state -> Prop.
(* [comment removed for export] *)
Variable npeek : node -> option (machine_state -> resp).
(* [comment removed for export] *)
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nexit : node -> Model -> word -> Model -> Prop.
Variable minv : Model -> Prop.
Variable nsafe : node -> Model -> Prop.
(* [comment removed for export] *)
Variable fstep : node -> resp -> footprint -> footprint -> Prop.
(* [comment removed for export] *)
Variable NMAX : nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mrel (A : alw) (mo mo_ : Model) : Prop :=
  same_but_mat mo mo_ /\ m_vm_materialized mo = [] /\
  List.NoDup (m_vm_materialized mo_) /\ (forall p, List.In p (m_vm_materialized mo_) -> A p).

(* [comment removed for export] *)
Definition acct_ok (RNG : footprint) (A : alw) (mo : Model) : Prop :=
  footprint_ok (m_vm_lazy mo) A RNG /\
  (exists L, List.NoDup L /\ (List.length L <= NMAX)%nat /\ forall p, A p -> List.In p L) /\
  (nonlazy_bytes mo + Z.of_nat NMAX * page_size <= vm_limit (m_vmmaps mo))%Z.

#[using="Type"] Lemma mrel_ainv : forall RNG A mo mo_,
  acct_ok RNG A mo -> mrel A mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_.
Proof.
  intros RNG A mo mo_ (FOK & FIN & ROOM) (SB & CAN & ND & AL).
  pose proof (same_but_mat_frame _ _ SB) as (_ & VM & LZ & _).
  constructor; auto.
  - rewrite (same_but_mat_nonlazy _ _ SB), VM. exact ROOM.
Qed.

#[using="Type"] Lemma mrel_halted : forall A mo mo_, mrel A mo mo_ -> m_halted mo_ = m_halted mo.
Proof. intros A mo mo_ (SB & _). apply same_but_mat_halted. exact SB. Qed.

#[using="Type"] Lemma mrel_fs : forall A mo mo_, mrel A mo mo_ -> m_fs mo_ = m_fs mo.
Proof.
  intros A mo mo_ (SB & _). pose proof (same_but_mat_frame _ _ SB) as (_ & _ & _ & _ & FS & _).
  unfold m_fs. rewrite FS. reflexivity.
Qed.

#[using="Type"] Lemma mrel_le : forall A A' mo mo_, mrel A mo mo_ -> alw_le A A' -> mrel A' mo mo_.
Proof. intros A A' mo mo_ (SB & CAN & ND & AL) LE. split; [exact SB|]. split; [exact CAN|]. split; [exact ND|]. intros p Hp. apply LE, AL, Hp. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mrel_after : forall A mo mo_ mo_',
  mrel A mo mo_ -> same_but_mat mo_ mo_' -> ainv (m_vm_lazy mo) A NMAX mo_' -> mrel A mo mo_'.
Proof.
  intros A mo mo_ mo_' (SB & CAN & _ & _) SB' INV. split; [eapply same_but_mat_trans; eauto|].
  split; [exact CAN|]. destruct INV as [_ ND AL _ _]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mpost (A : alw) (mo' mo_' : Model) : Prop := mrel A mo' mo_'.

Record node_soundA : Prop := {
  (* [comment removed for export] *)
  nsA_pending : forall n RNG ms, at_node n RNG ms -> ms_svc_pending ms <> None;
  (* [comment removed for export] *)
  nsA_complete : forall n RNG A ms mo mo_ evs X,
      at_node n RNG ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      footprint_ok (m_vm_lazy mo) A RNG -> mrel A mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_ ->
      sstep_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG (mkCfg ms mo_) evs X ->
        (exists rsp mo' mo_', X = SNext (mkCfg (nret ms rsp) mo_') /\ nstep n mo rsp mo' evs /\ mpost A mo' mo_')
     \/ (exists code mo' mo_', X = SNext (mkCfg ms mo_') /\ nexit n mo code mo' /\
                              evs = [ExitEv code (m_fs mo')] /\ m_halted mo_' = Some code);
  (* [comment removed for export] *)
  nsA_sound : forall n RNG A ms mo mo_ rsp mo' evs,
      at_node n RNG ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      footprint_ok (m_vm_lazy mo) A RNG -> mrel A mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_ ->
      nstep n mo rsp mo' evs ->
      m_halted mo' = None /\ minv mo' /\
      exists mo_', sstep_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG (mkCfg ms mo_) evs (SNext (mkCfg (nret ms rsp) mo_')) /\ mpost A mo' mo_';
  nsA_exit : forall n RNG A ms mo mo_ code mo',
      at_node n RNG ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      mrel A mo mo_ ->
      nexit n mo code mo' ->
      m_halted mo' = Some code /\
      exists mo_', sstep_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG (mkCfg ms mo_) [ExitEv code (m_fs mo')] (SNext (mkCfg ms mo_')) /\ m_halted mo_' = Some code;
  (* [comment removed for export] *)
  nsA_progress : forall n RNG A ms mo mo_, at_node n RNG ms -> m_halted mo = None -> minv mo -> nsafe n mo ->
      footprint_ok (m_vm_lazy mo) A RNG -> mrel A mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_ ->
      (exists rsp mo' evs, nstep n mo rsp mo' evs) \/ (exists code mo', nexit n mo code mo');
  (* [comment removed for export] *)
  nsA_peek : forall n f ms mo, npeek n = Some f -> nstep n mo (f ms) mo [];
  (* [comment removed for export] *)
  nsA_peek_at : forall n f RNG ms, npeek n = Some f -> ~ at_node n RNG ms
}.

(* [comment removed for export] *)
Definition sil_soundA : Prop := forall RNG A ms ms' mo mo_,
  sil RNG ms ms' -> m_halted mo = None -> minv mo ->
  footprint_ok (m_vm_lazy mo) A RNG -> mrel A mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_ ->
  exists mo_', OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.cnode_ok segs (mkCfg ms mo_) unit (fun _ => []) (fun _ => mkCfg ms' mo_') /\ mrel A mo mo_'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive mstepsS (RNG : footprint) : machine_state -> machine_state -> Prop :=
| mstepsS_refl : forall ms, mstepsS RNG ms ms
| mstepsS_instr : forall ms ms1 ms2, mstepF segs RNG ms ms1 -> mstepsS RNG ms1 ms2 -> mstepsS RNG ms ms2
| mstepsS_sil : forall ms ms1 ms2, sil RNG ms ms1 -> mstepsS RNG ms1 ms2 -> mstepsS RNG ms ms2.

Definition evtS (RNG : footprint) (Q : machine_state -> Prop) (ms : machine_state) : Prop :=
  exists ms', mstepsS RNG ms ms' /\ Q ms'.

#[using="Type"] Lemma mstepsS_trans : forall RNG a b c, mstepsS RNG a b -> mstepsS RNG b c -> mstepsS RNG a c.
Proof. intros RNG a b c H; induction H; intros; [assumption| eapply mstepsS_instr; eauto | eapply mstepsS_sil; eauto]. Qed.

#[using="Type"] Lemma mstepsS_of_mstepsF : forall RNG a b, mstepsF segs RNG a b -> mstepsS RNG a b.
Proof. intros RNG a b H; induction H; [constructor| eapply mstepsS_instr; eauto]. Qed.

#[using="Type"] Lemma evtS_done : forall RNG (Q : machine_state -> Prop) ms, Q ms -> evtS RNG Q ms.
Proof. intros RNG Q ms H. exists ms. split; [constructor| exact H]. Qed.

#[using="Type"] Lemma evtS_of_evtF : forall RNG Q ms, evtF segs RNG Q ms -> evtS RNG Q ms.
Proof. intros RNG Q ms (ms' & H & HQ). exists ms'. split; [apply mstepsS_of_mstepsF; exact H| exact HQ]. Qed.

#[using="Type"] Lemma evtS_cut : forall RNG (P Q : machine_state -> Prop) ms,
  evtS RNG P ms -> (forall ms', P ms' -> evtS RNG Q ms') -> evtS RNG Q ms.
Proof.
  intros RNG P Q ms (ms1 & H1 & HP) K. destruct (K ms1 HP) as (ms2 & H2 & HQ).
  exists ms2. split; [eapply mstepsS_trans; eauto| exact HQ].
Qed.

#[using="Type"] Lemma evtS_mono : forall RNG (P Q : machine_state -> Prop) ms,
  evtS RNG P ms -> (forall ms', P ms' -> Q ms') -> evtS RNG Q ms.
Proof. intros RNG P Q ms H K. eapply evtS_cut; [exact H|]. intros ms' HP. apply evtS_done, K, HP. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evtS_sil : forall RNG Q ms ms1, sil RNG ms ms1 -> evtS RNG Q ms1 -> evtS RNG Q ms.
Proof. intros RNG Q ms ms1 H (ms' & Hs & HQ). exists ms'. split; [eapply mstepsS_sil; eauto| exact HQ]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evtS_evtF_sil : forall RNG Q ms,
  evtF segs RNG (fun ms1 => exists ms2, sil RNG ms1 ms2 /\ evtS RNG Q ms2) ms -> evtS RNG Q ms.
Proof.
  intros RNG Q ms H. eapply evtS_cut; [apply evtS_of_evtF; exact H|].
  intros ms1 (ms2 & Hs & K). eapply evtS_sil; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint implF {R} (RNG : footprint) (t : itree node R)
    (Q : R -> footprint -> machine_state -> Prop) (ms : machine_state) : Prop :=
  match t with
  | Ret r => evtS RNG (Q r RNG) ms
  | Vis n k => evtS RNG (fun ms1 =>
                 (at_node n RNG ms1 /\
                  forall rsp RNG', fstep n rsp RNG RNG' -> implF RNG' (k rsp) Q (nret ms1 rsp))
              \/ (exists f, npeek n = Some f /\
                  forall RNG', fstep n (f ms1) RNG RNG' -> implF RNG' (k (f ms1)) Q ms1)) ms
  end.

#[using="Type"] Lemma implF_ret_intro : forall {R} RNG (r : R) Q ms, evtF segs RNG (Q r RNG) ms -> implF RNG (Ret r) Q ms.
Proof. intros. apply evtS_of_evtF. exact H. Qed.

#[using="Type"] Lemma implF_mono : forall {R} RNG (t : itree node R) (Q Q' : R -> footprint -> machine_state -> Prop) ms,
  implF RNG t Q ms -> (forall r RNG' ms', Q r RNG' ms' -> Q' r RNG' ms') -> implF RNG t Q' ms.
Proof.
  intros R RNG t; revert RNG. induction t as [r|n k IH]; intros RNG Q Q' ms H HQ; cbn in *.
  - eapply evtS_mono; [exact H|]. cbn. intros ms' H'. apply HQ. exact H'.
  - eapply evtS_mono; [exact H|]. intros ms1 [[Hat Hk]|(f & Hf & Hk)].
    + left. split; [exact Hat|]. intros rsp RNG' HF. eapply IH; eauto.
    + right. exists f. split; [exact Hf|]. intros RNG' HF. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implF_vis : forall {R} RNG n (k : resp -> itree node R) Q ms,
  evtS RNG (fun ms1 => at_node n RNG ms1 /\
              forall rsp RNG', fstep n rsp RNG RNG' -> implF RNG' (k rsp) Q (nret ms1 rsp)) ms ->
  implF RNG (Vis n k) Q ms.
Proof. intros R RNG n k Q ms H. cbn [implF]. eapply evtS_mono; [exact H|]. intros ms1 H1. left. exact H1. Qed.

#[using="Type"] Lemma implF_peek : forall {R} RNG n f (k : resp -> itree node R) Q ms,
  npeek n = Some f ->
  evtS RNG (fun ms1 => forall RNG', fstep n (f ms1) RNG RNG' -> implF RNG' (k (f ms1)) Q ms1) ms ->
  implF RNG (Vis n k) Q ms.
Proof.
  intros R RNG n f k Q ms Hn H. cbn [implF]. eapply evtS_mono; [exact H|]. intros ms1 H1. right. exists f. split; [exact Hn| exact H1].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implF_peek_now : forall {R} RNG n f (k : resp -> itree node R) Q ms,
  npeek n = Some f ->
  (forall RNG', fstep n (f ms) RNG RNG' -> implF RNG' (k (f ms)) Q ms) ->
  implF RNG (Vis n k) Q ms.
Proof. intros R RNG n f k Q ms Hn H. eapply implF_peek; [exact Hn|]. apply evtS_done. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implF_evtS : forall {R} RNG (t : itree node R) Q P ms,
  evtS RNG P ms -> (forall ms', P ms' -> implF RNG t Q ms') -> implF RNG t Q ms.
Proof.
  intros R RNG t Q P ms H K. destruct t; cbn in *; eapply evtS_cut; eauto; intros ms' HP; apply (K _ HP).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implF_sil : forall {R} RNG (t : itree node R) Q ms ms1,
  sil RNG ms ms1 -> implF RNG t Q ms1 -> implF RNG t Q ms.
Proof.
  intros R RNG t Q ms ms1 Hs K. eapply (implF_evtS RNG t Q (fun ms' => ms' = ms1)).
  - eapply evtS_sil; [exact Hs|]. apply evtS_done. reflexivity.
  - intros ms' ->. exact K.
Qed.

#[using="Type"] Lemma implF_evtF : forall {R} RNG (t : itree node R) Q P ms,
  evtF segs RNG P ms -> (forall ms', P ms' -> implF RNG t Q ms') -> implF RNG t Q ms.
Proof.
  intros R RNG t Q P ms H K. eapply implF_evtS; [apply evtS_of_evtF; exact H| exact K].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implF_bind : forall {A B} RNG (t : itree node A) (f : A -> itree node B) Q1 Q ms,
  implF RNG t Q1 ms -> (forall r RNG' ms', Q1 r RNG' ms' -> implF RNG' (f r) Q ms') -> implF RNG (bind node t f) Q ms.
Proof.
  intros A B RNG t; revert RNG. induction t as [r|n k IH]; intros RNG f Q1 Q ms H Hf; cbn [bind].
  - cbn in H. eapply implF_evtS; [exact H|]. intros ms' HQ. exact (Hf _ _ _ HQ).
  - cbn in H |- *. eapply evtS_mono; [exact H|]. intros ms1 [[Hat Hk]|(g & Hg & Hk)].
    + left. split; [exact Hat|]. intros rsp RNG' HF. eapply IH; eauto.
    + right. exists g. split; [exact Hg|]. intros RNG' HF. eapply IH; eauto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint tsafeA {R} (RNG : footprint) (A : alw) (t : itree node R) (mo : Model) : Prop :=
  acct_ok RNG A mo /\
  match t with
  | Ret _ => True
  | Vis n k => nsafe n mo /\
      forall rsp mo' evs, nstep n mo rsp mo' evs ->
        exists RNG' A', fstep n rsp RNG RNG' /\ alw_le A A' /\ tsafeA RNG' A' (k rsp) mo'
  end.

#[using="Type"] Lemma tsafeA_acct : forall {R} RNG A (t : itree node R) mo, tsafeA RNG A t mo -> acct_ok RNG A mo.
Proof. intros R RNG A [r|n k] mo H; exact (proj1 H). Qed.

(* [comment removed for export] *)
Definition ptraces {R} (t : itree node R) (mo : Model) : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.TSet :=
  fun tr => exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tree_atA {R} (RNG : footprint) (A : alw) (t : itree node R) Q
    (ms : machine_state) (mo mo_ : Model) : Prop :=
  implF RNG t Q ms /\ leaves_unreachable_m nstep t mo /\ m_halted mo = None /\ minv mo /\
  tsafeA RNG A t mo /\ mrel A mo mo_.

#[using="Type"] Lemma tree_atA_ainv : forall {R} RNG A (t : itree node R) Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> ainv (m_vm_lazy mo) A NMAX mo_.
Proof. intros R RNG A t Q ms mo mo_ (_ & _ & _ & _ & TS & MR). eapply mrel_ainv; [eapply tsafeA_acct; exact TS| exact MR]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tree_atA_step : node_soundA -> forall {R} RNG A n (k : resp -> itree node R) Q ms1 mo mo_ rsp mo' evs,
  at_node n RNG ms1 -> (forall rsp RNG', fstep n rsp RNG RNG' -> implF RNG' (k rsp) Q (nret ms1 rsp)) ->
  leaves_unreachable_m nstep (Vis n k) mo -> m_halted mo = None -> minv mo -> tsafeA RNG A (Vis n k) mo ->
  mrel A mo mo_ ->
  nstep n mo rsp mo' evs ->
  exists RNG' A' mo_',
    tree_atA RNG' A' (k rsp) Q (nret ms1 rsp) mo' mo_'
    /\ sstep_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG (mkCfg ms1 mo_) evs (SNext (mkCfg (nret ms1 rsp) mo_')).
Proof.
  intros NS R RNG A n k Q ms1 mo mo_ rsp mo' evs Hat Hk Hl Hh Hinv Hsf MR Hst.
  pose proof Hsf as (ACC & Hns & Hk').
  destruct (Hk' rsp mo' evs Hst) as (RNG' & A' & HF & HLE & Hsf').
  pose proof (mrel_ainv RNG A mo mo_ ACC MR) as INV.
  destruct (nsA_sound NS n RNG A ms1 mo mo_ rsp mo' evs Hat Hh Hinv Hns (proj1 ACC) MR INV Hst)
    as (Hh' & Hinv' & mo_' & Hss & MP).
  exists RNG', A', mo_'. split; [|exact Hss].
  split; [apply Hk; exact HF|]. split; [eapply leaves_unreachable_m_step; eassumption|].
  split; [exact Hh'|]. split; [exact Hinv'|]. split; [exact Hsf'|].
  eapply mrel_le; [exact MP| exact HLE].
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma cstep_cnode_ok : forall ms mo ms' mo',
  cstep segs (ms, mo) (ms', mo') ->
  OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.cnode_ok segs (mkCfg ms mo) unit (fun _ => []) (fun _ => mkCfg ms' mo').
Proof.
  intros ms mo ms' mo' (Hh & Hs & Ha). cbn in Hh, Hs, Ha. apply SpinAlg.cnode_lift_unit. split.
  - intros _. eapply sstep_instr; eauto.
  - intros e st Hss. exists tt. inversion Hss; subst; try congruence.
    all: try (rewrite Ha in *; congruence).
    match goal with H : mi_account_step segs ms mo = MachineOk _ |- _ => rewrite Ha in H; inversion H; subst; auto end.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evtS_lift : sil_soundA -> forall RNG A (Q : machine_state -> Prop) ms mo mo_,
  acct_ok RNG A mo -> m_halted mo = None -> minv mo -> mrel A mo mo_ ->
  evtS RNG Q ms ->
  exists ms1 mo1_, Q ms1 /\ mrel A mo mo1_ /\
    forall T, SpinAlg.srealizes segs (mkCfg ms1 mo1_) T -> SpinAlg.srealizes segs (mkCfg ms mo_) T.
Proof.
  intros SS RNG A Q ms mo mo_ ACC Hh Hinv MR (msf & RUN & HQ).
  revert mo_ MR. induction RUN as [ms0|ms0 ms1 ms2 ST RUN IH|ms0 ms1 ms2 SL RUN IH]; intros mo_ MR.
  - exists ms0, mo_. split; [exact HQ|]. split; [exact MR|]. intros T H; exact H.
  - pose proof (mrel_ainv RNG A mo mo_ ACC MR) as INV.
    destruct (mstepF_lift segs (m_vm_lazy mo) A NMAX RNG ms0 ms1 mo_ (proj1 ACC) INV
                ltac:(rewrite (mrel_halted _ _ _ MR); exact Hh) ST) as (mo1 & C1 & INV1 & SB1).
    assert (MR1 : mrel A mo mo1) by (eapply mrel_after; eauto).
    destruct (IH HQ mo1 MR1) as (msx & mox & HQx & MRx & K).
    exists msx, mox. split; [exact HQx|]. split; [exact MRx|].
    intros T H. eapply SpinAlg.srz_silent1; [apply cstep_cnode_ok; exact C1| apply K; exact H].
  - pose proof (mrel_ainv RNG A mo mo_ ACC MR) as INV.
    destruct (SS RNG A ms0 ms1 mo mo_ SL Hh Hinv (proj1 ACC) MR INV) as (mo1 & CN & MR1).
    destruct (IH HQ mo1 MR1) as (msx & mox & HQx & MRx & K).
    exists msx, mox. split; [exact HQx|]. split; [exact MRx|].
    intros T H. eapply SpinAlg.srz_silent1; [exact CN| apply K; exact H].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tree_atA_peek : node_soundA -> forall {R} RNG A n f (k : resp -> itree node R) Q ms1 mo mo_,
  npeek n = Some f ->
  (forall RNG', fstep n (f ms1) RNG RNG' -> implF RNG' (k (f ms1)) Q ms1) ->
  leaves_unreachable_m nstep (Vis n k) mo -> m_halted mo = None -> minv mo -> tsafeA RNG A (Vis n k) mo ->
  mrel A mo mo_ ->
  exists RNG' A', tree_atA RNG' A' (k (f ms1)) Q ms1 mo mo_.
Proof.
  intros NS R RNG A n f k Q ms1 mo mo_ Hf Hk Hl Hh Hinv Hsf MR.
  pose proof (nsA_peek NS n f ms1 mo Hf) as Hst.
  pose proof Hsf as (ACC & Hns & Hk').
  destruct (Hk' _ _ _ Hst) as (RNG' & A' & HF & HLE & Hsf').
  exists RNG', A'. split; [apply Hk; exact HF|]. split; [eapply leaves_unreachable_m_step; eassumption|].
  split; [exact Hh|]. split; [exact Hinv|]. split; [exact Hsf'|]. eapply mrel_le; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ttrace_exists : node_soundA -> sil_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> exists full, ttrace nstep nexit t mo full.
Proof.
  intros NS SS R t. induction t as [r|n k IH]; intros RNG A Q ms mo mo_ HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret _ nstep r mo Hl).
  - pose proof HT as (Ht & Hl & Hh & Hinv & Hsf & MR).
    cbn [implF] in Ht.
    (* [comment removed for export] *)
    destruct (evtS_lift SS RNG A _ ms mo mo_ (tsafeA_acct _ _ _ _ Hsf) Hh Hinv MR Ht)
      as (ms1 & mo1_ & [[Hat1 Hk1]|(f & Hf & Hk1)] & MR1 & _).
    + pose proof (mrel_ainv RNG A mo mo1_ (tsafeA_acct _ _ _ _ Hsf) MR1) as INV1.
      destruct (nsA_progress NS n RNG A ms1 mo mo1_ Hat1 Hh Hinv (proj1 (proj2 Hsf)) (proj1 (tsafeA_acct _ _ _ _ Hsf)) MR1 INV1)
        as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
      * destruct (tree_atA_step NS RNG A n k Q ms1 mo mo1_ rsp mo' evs Hat1 Hk1 Hl Hh Hinv Hsf MR1 Hst) as (RNG' & A' & mo_' & HT' & _).
        destruct (IH rsp RNG' A' Q (nret ms1 rsp) mo' mo_' HT') as (full' & Hfull').
        exists (evs ++ full'). cbn. right. exists rsp, mo', evs, full'. repeat split; assumption.
      * exists [ExitEv code (m_fs mo')]. cbn. left. exists code, mo'. split; [assumption|reflexivity].
    + destruct (tree_atA_peek NS RNG A n f k Q ms1 mo mo1_ Hf Hk1 Hl Hh Hinv Hsf MR1) as (RNG' & A' & HT').
      destruct (IH (f ms1) RNG' A' Q ms1 mo mo1_ HT') as (full' & Hfull').
      exists full'. cbn. right. exists (f ms1), mo, [], full'.
      split; [exact (nsA_peek NS n f ms1 mo Hf)|]. split; [exact Hfull'| reflexivity].
Qed.

#[using="Type"] Lemma ptraces_nonempty : node_soundA -> sil_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> ptraces t mo [].
Proof.
  intros NS SS R t RNG A Q ms mo mo_ HT. destruct (ttrace_exists NS SS t RNG A Q ms mo mo_ HT) as (full & Hf).
  exists full. split; [exact Hf| apply is_prefix_nil].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition obsc (c : config) : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.TSet := fun tr => obs_trace_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG c tr.

#[using="Type"] Lemma obsc_eq : forall c T, SpinAlg.srealizes segs c T -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.t_eq (obsc c) T.
Proof. intros c T H tr. apply (SpinAlg.srealizes_obs_iff segs c T H). Qed.

#[using="Type"] Lemma srz_obsc : forall c T, SpinAlg.srealizes segs c T -> SpinAlg.srealizes segs c (obsc c).
Proof. intros c T H. eapply SpinAlg.srz_conseq; [exact H|]. intros tr. symmetry. apply (obsc_eq c T H). Qed.

(* [comment removed for export] *)
Definition adequate {R} (t : itree node R) (mo : Model) (c : config) : Prop :=
  SpinAlg.srealizes segs c (obsc c)
  /\ (forall tr, obsc c tr -> ptraces t mo tr)
  /\ (forall W : list event -> Prop, wins npeek nstep nexit t mo W -> exists tr, obsc c tr /\ W tr).

#[using="Type"] Lemma adequate_lift : forall {R} (t : itree node R) mo c1 c,
  (forall T, SpinAlg.srealizes segs c1 T -> SpinAlg.srealizes segs c T) ->
  adequate t mo c1 -> adequate t mo c.
Proof.
  intros R t mo c1 c K (H1 & H2 & H3).
  pose proof (K _ H1) as Hc.
  pose proof (obsc_eq c _ Hc) as E.
  split; [eapply srz_obsc; exact Hc|]. split.
  - intros tr Htr. apply H2. apply E. exact Htr.
  - intros W HW. destruct (H3 W HW) as (tr & Htr & HWtr). exists tr. split; [apply E; exact Htr| exact HWtr].
Qed.

(* [comment removed for export] *)

Section NodeCase.
  Context {R : Type}.
  Variables (n : node) (k : resp -> itree node R) (Q : R -> footprint -> machine_state -> Prop).
  Variables (RNG : footprint) (A : alw) (ms1 : machine_state) (mo mo1_ : Model).
  Hypothesis NS : node_soundA.
  Hypothesis SS : sil_soundA.
  Hypothesis Hat : at_node n RNG ms1.
  Hypothesis Hk : forall rsp RNG', fstep n rsp RNG RNG' -> implF RNG' (k rsp) Q (nret ms1 rsp).
  Hypothesis Hl : leaves_unreachable_m nstep (Vis n k) mo.
  Hypothesis Hh : m_halted mo = None.
  Hypothesis Hinv : minv mo.
  Hypothesis Hsf : tsafeA RNG A (Vis n k) mo.
  Hypothesis MR : mrel A mo mo1_.
  (* [comment removed for export] *)
  Hypothesis IH : forall rsp RNG' A' ms' mo' mo_',
    tree_atA RNG' A' (k rsp) Q ms' mo' mo_' -> adequate (k rsp) mo' (mkCfg ms' mo_').

  Let c1 : config := mkCfg ms1 mo1_.

  (* [comment removed for export] *)
  Definition succ : Type := { ce : config * list event | sstep_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG c1 (snd ce) (SNext (fst ce)) }.
  Definition s_evs (i : succ) : list event := snd (proj1_sig i).
  Definition s_nx (i : succ) : config := fst (proj1_sig i).

  #[using="node nstep nsafe fstep R n k RNG Hsf MR"] Lemma INV1 : ainv (m_vm_lazy mo) A NMAX mo1_.
  Proof. eapply mrel_ainv; [eapply tsafeA_acct; exact Hsf| exact MR]. Qed.

  #[using="node nstep nsafe fstep NMAX R n k Hsf"] Lemma FOK : footprint_ok (m_vm_lazy mo) A RNG.
  Proof. exact (proj1 (tsafeA_acct _ _ _ _ Hsf)). Qed.

  #[using="nstep fstep NMAX R k RNG A Hsf"] Lemma NSF : nsafe n mo.
  Proof. exact (proj1 (proj2 Hsf)). Qed.

  #[using="node at_node npeek nstep nexit minv nsafe fstep NMAX R n k RNG A mo NS Hat Hh Hinv Hsf MR"] Lemma succ_node_ok : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.cnode_ok segs c1 succ s_evs s_nx.
  Proof.
    split.
    - intros [[c e] Hs]. exact Hs.
    - intros e st Hss.
      destruct (nsA_complete NS n RNG A ms1 mo mo1_ e st Hat Hh Hinv NSF FOK MR INV1 Hss)
        as [(rsp & mo' & mo_' & -> & _) | (code & mo' & mo_' & -> & _)].
      + exists (exist _ (mkCfg (nret ms1 rsp) mo_', e) Hss). split; reflexivity.
      + exists (exist _ (mkCfg ms1 mo_', e) Hss). split; reflexivity.
  Qed.

  #[using="nexit RNG mo1_ NS Hat Hk Hl Hh Hinv Hsf MR"] Lemma step_tree_atA : forall rsp mo' evs mo_',
    nstep n mo rsp mo' evs -> mpost A mo' mo_' ->
    exists RNG' A', tree_atA RNG' A' (k rsp) Q (nret ms1 rsp) mo' mo_'.
  Proof.
    intros rsp mo' evs mo_' Hst MP.
    pose proof Hsf as (ACC & Hns & Hk').
    destruct (Hk' rsp mo' evs Hst) as (RNG' & A' & HF & HLE & Hsf').
    destruct (nsA_sound NS n RNG A ms1 mo mo1_ rsp mo' evs Hat Hh Hinv Hns FOK MR INV1 Hst) as (Hh' & Hinv' & _).
    exists RNG', A'. split; [apply Hk; exact HF|]. split; [eapply leaves_unreachable_m_step; eassumption|].
    split; [exact Hh'|]. split; [exact Hinv'|]. split; [exact Hsf'|]. eapply mrel_le; eauto.
  Qed.

  #[using="node at_node sil npeek nstep nexit minv nsafe fstep NMAX R n k Q RNG A mo NS Hat Hk Hl Hh Hinv Hsf MR IH"] Lemma succ_srealizes : forall i, SpinAlg.srealizes segs (s_nx i) (obsc (s_nx i)).
  Proof.
    intros [[c e] Hss]. unfold s_nx. cbn [proj1_sig fst snd].
    destruct (nsA_complete NS n RNG A ms1 mo mo1_ e (SNext c) Hat Hh Hinv NSF FOK MR INV1 Hss)
      as [(rsp & mo' & mo_' & E & Hst & MP) | (code & mo' & mo_' & E & Hex & -> & Hh')]; inversion E; subst.
    - destruct (step_tree_atA rsp mo' e mo_' Hst MP) as (RNG' & A' & HT').
      exact (proj1 (IH rsp RNG' A' _ _ _ HT')).
    - eapply srz_obsc. apply SpinAlg.srz_halt. cbn. congruence.
  Qed.

  #[using="node at_node sil npeek nstep nexit minv nsafe fstep NMAX R n k Q RNG A mo NS Hat Hk Hl Hh Hinv Hsf MR IH"] Lemma node_srz : SpinAlg.srealizes segs c1 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.t_alt (fun i => OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.t_emit (s_evs i) (obsc (s_nx i)))).
  Proof.
    (* [comment removed for export] *)
    destruct (nsA_progress NS n RNG A ms1 mo mo1_ Hat Hh Hinv NSF FOK MR INV1) as [(rsp & mo' & evs & Hst)|(code & mo' & Hex)].
    - destruct (nsA_sound NS n RNG A ms1 mo mo1_ rsp mo' evs Hat Hh Hinv NSF FOK MR INV1 Hst) as (_ & _ & mo_' & Hss & _).
      apply (SpinAlg.srz_node segs c1 succ s_evs s_nx (fun i => obsc (s_nx i)) (exist _ (mkCfg (nret ms1 rsp) mo_', evs) Hss)
               succ_node_ok succ_srealizes).
    - destruct (nsA_exit NS n RNG A ms1 mo mo1_ code mo' Hat Hh Hinv NSF MR Hex) as (_ & mo_' & Hss & _).
      apply (SpinAlg.srz_node segs c1 succ s_evs s_nx (fun i => obsc (s_nx i)) (exist _ (mkCfg ms1 mo_', [ExitEv code (m_fs mo')]) Hss)
               succ_node_ok succ_srealizes).
  Qed.

  #[using="at_node sil minv nsafe fstep NMAX Q RNG A NS SS Hat Hk Hl Hh Hinv Hsf MR IH"] Lemma node_adequate : adequate (Vis n k) mo c1.
  Proof.
    pose proof node_srz as SRZ. pose proof (obsc_eq c1 _ SRZ) as E.
    split; [eapply srz_obsc; exact SRZ|]. split.
    - (* [comment removed for export] *)
      intros tr Htr. apply E in Htr. destruct Htr as ([[c e] Hss] & Hi). unfold s_nx, s_evs in Hi. cbn [proj1_sig fst snd] in Hi.
      unfold ptraces.
      destruct (nsA_complete NS n RNG A ms1 mo mo1_ e (SNext c) Hat Hh Hinv NSF FOK MR INV1 Hss)
        as [(rsp & mo' & mo_' & E1 & Hst & MP) | (code & mo' & mo_' & E1 & Hex & -> & Hh')]; inversion E1; subst.
      + destruct (step_tree_atA rsp mo' e mo_' Hst MP) as (RNG' & A' & HT').
        destruct Hi as [Hp | (tr' & -> & Hobs)].
        * destruct (ttrace_exists NS SS (k rsp) RNG' A' Q _ _ _ HT') as (full' & Hf').
          exists (e ++ full'). split; [| eapply is_prefix_trans; [exact Hp| apply is_prefix_app]].
          cbn. right. exists rsp, mo', e, full'. repeat split; assumption.
        * destruct (proj1 (proj2 (IH rsp RNG' A' _ _ _ HT')) tr' Hobs) as (full2 & Hf2 & Hp2).
          exists (e ++ full2). split; [| apply is_prefix_app_l; exact Hp2].
          cbn. right. exists rsp, mo', e, full2. repeat split; assumption.
      + destruct Hi as [Hp | (tr' & -> & Hobs)].
        * exists [ExitEv code (m_fs mo')]. split; [| exact Hp]. cbn. left. exists code, mo'. auto.
        * assert (Hnil : tr' = []).
          { refine (proj1 (obsc_eq (mkCfg ms1 mo_') OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.t_nil _ tr') Hobs). apply SpinAlg.srz_halt. cbn. congruence. }
          subst tr'. exists [ExitEv code (m_fs mo')]. split. { cbn. left. exists code, mo'. auto. }
          rewrite app_nil_r. apply is_prefix_refl.
    - (* [comment removed for export] *)
      intros W HW. inversion HW as [t0 mo0 T0 HT0|n0 k0 mo0 T0 code mo' Hn Hex HT0|n0 k0 mo0 T0 rsp mo' evs Hn Hst Hw|n0 k0 mo0 T0 f Hn Hall]; subst.
      + exists []. split; [| exact HT0]. apply (SpinAlg.srealizes_nonempty segs c1 _ (srz_obsc c1 _ SRZ)).
      + destruct (nsA_exit NS n RNG A ms1 mo mo1_ code mo' Hat Hh Hinv NSF MR Hex) as (_ & mo_' & Hss & _).
        exists [ExitEv code (m_fs mo')]. split; [| exact HT0]. apply E.
        exists (exist _ (mkCfg ms1 mo_', [ExitEv code (m_fs mo')]) Hss). unfold s_evs, s_nx. cbn [proj1_sig fst snd].
        left. apply is_prefix_refl.
      + destruct (nsA_sound NS n RNG A ms1 mo mo1_ rsp mo' evs Hat Hh Hinv NSF FOK MR INV1 Hst) as (_ & _ & mo_' & Hss & MP).
        destruct (step_tree_atA rsp mo' evs mo_' Hst MP) as (RNG' & A' & HT').
        destruct (proj2 (proj2 (IH rsp RNG' A' _ _ _ HT')) _ Hw) as (tr' & Hobs' & HW').
        exists (evs ++ tr'). split; [| exact HW']. apply E.
        exists (exist _ (mkCfg (nret ms1 rsp) mo_', evs) Hss). unfold s_evs, s_nx. cbn [proj1_sig fst snd].
        right. exists tr'. split; [reflexivity| exact Hobs'].
      + exfalso. exact (nsA_peek_at NS n f RNG ms1 Hn Hat).
  Qed.
End NodeCase.

(* [comment removed for export] *)

#[using="Type"] Theorem implF_adequate : node_soundA -> sil_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> adequate t mo (mkCfg ms mo_).
Proof.
  intros NS SS R t. induction t as [r|n k IHk]; intros RNG A Q ms mo mo_ HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret _ nstep r mo Hl).
  - pose proof HT as (Ht & Hl & Hh & Hinv & Hsf & MR).
    cbn [implF] in Ht.
    destruct (evtS_lift SS RNG A _ ms mo mo_ (tsafeA_acct _ _ _ _ Hsf) Hh Hinv MR Ht)
      as (ms1 & mo1_ & [[Hat1 Hk1]|(f & Hf & Hk1)] & MR1 & LIFT).
    + eapply adequate_lift; [exact LIFT|].
      apply (node_adequate n k Q RNG A ms1 mo mo1_ NS SS Hat1 Hk1 Hl Hh Hinv Hsf MR1).
      intros rsp RNG' A' ms' mo' mo_' HT'. eapply IHk. exact HT'.
    + eapply adequate_lift; [exact LIFT|].
      destruct (tree_atA_peek NS RNG A n f k Q ms1 mo mo1_ Hf Hk1 Hl Hh Hinv Hsf MR1) as (RNG' & A' & HT').
      pose proof (IHk (f ms1) RNG' A' Q ms1 mo mo1_ HT') as (A1 & A2 & A3).
      pose proof (nsA_peek NS n f ms1 mo Hf) as Hst.
      split; [exact A1|]. split.
      * intros tr Htr. destruct (A2 tr Htr) as (full & Hfull & Hp). exists full. split; [| exact Hp].
        cbn. right. exists (f ms1), mo, [], full. split; [exact Hst|]. split; [exact Hfull| reflexivity].
      * intros W HW. inversion HW as [t0 mo0 T0 HT0|n0 k0 mo0 T0 code mo' Hn Hex HT0|n0 k0 mo0 T0 rsp mo' evs Hn Hst' Hw|n0 k0 mo0 T0 f0 Hn Hall]; subst.
        -- exists []. split; [| exact HT0]. apply (SpinAlg.srealizes_nonempty segs _ _ A1).
        -- congruence.
        -- congruence.
        -- exact (A3 _ (Hall (f ms1) mo [] Hst)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem implF_obs_sound : node_soundA -> sil_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ ->
  forall tr, obs_trace_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG (mkCfg ms mo_) tr -> ptraces t mo tr.
Proof. intros NS SS R t RNG A Q ms mo mo_ HT. exact (proj1 (proj2 (implF_adequate NS SS t RNG A Q ms mo mo_ HT))). Qed.

#[using="Type"] Theorem implF_obs_complete : node_soundA -> sil_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ ->
  forall W : list event -> Prop, wins npeek nstep nexit t mo W ->
    exists tr, obs_trace_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG (mkCfg ms mo_) tr /\ W tr.
Proof. intros NS SS R t RNG A Q ms mo mo_ HT. exact (proj2 (proj2 (implF_adequate NS SS t RNG A Q ms mo mo_ HT))). Qed.

#[using="Type"] Theorem implF_no_error : node_soundA -> sil_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> ~ reaches_error_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG (mkCfg ms mo_).
Proof.
  intros NS SS R t RNG A Q ms mo mo_ HT. eapply SpinAlg.srealizes_no_error.
  exact (proj1 (implF_adequate NS SS t RNG A Q ms mo mo_ HT)).
Qed.

#[using="Type"] Theorem implF_modeled : node_soundA -> sil_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  tree_atA RNG A t Q ms mo mo_ -> ~ reaches_unmodeled_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG (mkCfg ms mo_).
Proof.
  intros NS SS R t RNG A Q ms mo mo_ HT Hu. apply (reaches_unmodeled_cfg_reaches_error_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG) in Hu.
  revert Hu. eapply implF_no_error; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem implF_srealizes : node_soundA -> sil_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  npfree npeek t ->
  tree_atA RNG A t Q ms mo mo_ -> SpinAlg.srealizes segs (mkCfg ms mo_) (ptraces t mo).
Proof.
  intros NS SS R t RNG A Q ms mo mo_ NP HT.
  destruct (implF_adequate NS SS t RNG A Q ms mo mo_ HT) as (A1 & A2 & A3).
  eapply SpinAlg.srz_conseq; [exact A1|]. intros tr. split; [apply A2|].
  intros (full & Hfull & Hp).
  destruct (A3 _ (ttrace_wins node npeek nstep nexit t mo full NP Hfull)) as (tr0 & Hobs & <-).
  exact (SpinAlg.srealizes_pclosed segs _ _ A1 full tr Hobs Hp).
Qed.

#[using="Type"] Theorem implF_obs_trace : node_soundA -> sil_soundA -> forall {R} (t : itree node R) RNG A Q ms mo mo_,
  npfree npeek t ->
  tree_atA RNG A t Q ms mo mo_ ->
  forall tr, obs_trace_cfg segs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.CFG (mkCfg ms mo_) tr <-> ptraces t mo tr.
Proof. intros NS SS R t RNG A Q ms mo mo_ NP HT. apply SpinAlg.srealizes_obs_iff. eapply implF_srealizes; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition epostF {X} (Q : X -> footprint -> machine_state -> Prop) : exc X -> footprint -> machine_state -> Prop :=
  fun r RNG ms => match r with Unr => True | Ok a => Q a RNG ms end.

#[using="Type"] Lemma implF_ret_unr : forall {X} RNG (Q : X -> footprint -> machine_state -> Prop) ms,
  implF RNG (Ret Unr) (epostF Q) ms.
Proof. intros X RNG Q ms. cbn. apply evtS_done. exact I. Qed.

#[using="Type"] Lemma implF_ret_ok : forall {X} RNG (Q : X -> footprint -> machine_state -> Prop) a ms,
  evtF segs RNG (Q a RNG) ms -> implF RNG (Ret (Ok a)) (epostF Q) ms.
Proof. intros X RNG Q a ms H. apply evtS_of_evtF. exact H. Qed.

#[using="Type"] Lemma implF_ebind : forall {X Y} RNG (t : itree node (exc X)) (f : X -> itree node (exc Y)) Q1 Q ms,
  implF RNG t (epostF Q1) ms -> (forall a RNG' ms', Q1 a RNG' ms' -> implF RNG' (f a) (epostF Q) ms') ->
  implF RNG (ebind t f) (epostF Q) ms.
Proof.
  intros X Y RNG t f Q1 Q ms Ht Hf. unfold ebind. eapply implF_bind; [exact Ht|].
  intros [|a] RNG' ms' H'; cbn in H'.
  - apply implF_ret_unr.
  - apply Hf. exact H'.
Qed.

#[using="Type"] Lemma implF_epost_mono : forall {X} RNG (t : itree node (exc X)) (Q Q' : X -> footprint -> machine_state -> Prop) ms,
  implF RNG t (epostF Q) ms -> (forall a RNG' ms', Q a RNG' ms' -> Q' a RNG' ms') -> implF RNG t (epostF Q') ms.
Proof.
  intros X RNG t Q Q' ms H HQ. eapply implF_mono; [exact H|]. intros [|a] RNG' ms'; cbn; auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma implF_enode : forall {X} RNG n (pl : resp -> option X) (Q : X -> footprint -> machine_state -> Prop) ms,
  evtF segs RNG (fun ms1 => at_node n RNG ms1 /\
                   forall rsp RNG' a, fstep n rsp RNG RNG' -> pl rsp = Some a -> evtF segs RNG' (Q a RNG') (nret ms1 rsp)) ms ->
  implF RNG (enode n pl) (epostF Q) ms.
Proof.
  intros X RNG n pl Q ms H. cbn. eapply evtS_mono; [apply evtS_of_evtF; exact H|]. intros ms1 [Hat Hk]. left. split; [exact Hat|].
  intros rsp RNG' HF. specialize (Hk rsp RNG'). destruct (pl rsp) as [a|]; cbn.
  - apply evtS_of_evtF. apply Hk; [exact HF| reflexivity].
  - apply evtS_done. exact I.
Qed.

End ITreeA.

Arguments mrel A mo mo_ /.
Arguments implF {node} segs at_node sil npeek fstep {R} RNG t Q ms.
Arguments evtS segs sil RNG Q ms.
Arguments tsafeA {node} nstep nsafe fstep NMAX {R} RNG A t mo.
Arguments ptraces {node} nstep nexit {R} t mo _.
Arguments tree_atA {node} segs at_node sil npeek nstep minv nsafe fstep NMAX {R} RNG A t Q ms mo mo_.
Arguments adequate {node} segs npeek nstep nexit {R} t mo c.
Arguments implF_adequate {node} segs at_node sil npeek nstep nexit minv nsafe fstep NMAX _ _ {R} t RNG A Q ms mo mo_ _.
Arguments implF_obs_sound {node} segs at_node sil npeek nstep nexit minv nsafe fstep NMAX _ _ {R} t RNG A Q ms mo mo_ _ tr _.
Arguments implF_obs_complete {node} segs at_node sil npeek nstep nexit minv nsafe fstep NMAX _ _ {R} t RNG A Q ms mo mo_ _ W _.
Arguments implF_srealizes {node} segs at_node sil npeek nstep nexit minv nsafe fstep NMAX _ _ {R} t RNG A Q ms mo mo_ _ _.
Arguments implF_obs_trace {node} segs at_node sil npeek nstep nexit minv nsafe fstep NMAX _ _ {R} t RNG A Q ms mo mo_ _ _.
Arguments implF_no_error {node} segs at_node sil npeek nstep nexit minv nsafe fstep NMAX _ _ {R} t RNG A Q ms mo mo_ _.
