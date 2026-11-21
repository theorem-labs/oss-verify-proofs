(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader premise of impl_realizes_f, passed on to impl_realizes, with ASTA_PM_reader for it; recorded (KReplay) proofs re-proved by tactics). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import CatSim ShapeAlg AsanAcct AsanAcctShape.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode RelSpec RzCPS NodesA NodesA_wv FP.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import X_bridge.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import FrmExec FrmRun RT_iface.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma nret_fcsr : forall ms eff, ms_fcsr (nret ms eff) = ms_fcsr ms.
Proof. intros ms eff. reflexivity. Qed.

Section Bridge.
Variable segs : list Segment.
Variable segtop : Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_below_b segs segtop = true.
Hypothesis Hrom : rom_frm_ok segs = true.

(* [comment removed for export] *)
Lemma impl_frm : forall {nd : Type} (atn : nd -> machine_state -> Prop) {R} (t : itree nd R) Q ms,
  impl segs atn t Q ms -> frm0 (ms_fcsr ms) -> impl segs atn t (fun r ms' => Q r ms' /\ frm0 (ms_fcsr ms')) ms.
Proof using Hrom.
  intros nd atn R t. induction t as [r|n k IH]; intros Q ms H F0; cbn [impl] in *.
  - exact (evt_frm0 segs Hrom _ ms H F0).
  - pose proof (evt_frm0 segs Hrom _ ms H F0) as H'. eapply evt_mono; [exact H'|].
    intros ms1 ((Hat & Hk) & F1). split; [exact Hat|]. intros rsp. apply IH; [exact (Hk rsp) | rewrite nret_fcsr; exact F1].
Qed.

Theorem impl_realizes_f : forall {X : Type} (chans : list Z) (t : itree node (exc X)) A PM (Q : X -> machine_state -> Prop)
    (T : X -> TSet) ms c,
  mat_stable PM ->
  (forall mo fd, PM mo -> In fd chans -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd))) ->
  (* LPS 08b1429: a nonempty writev needs the channel's reader, as in [impl_realizes] *)
  (forall mo, PM mo -> m_channel_reader mo = true) ->
  tok chans t -> AST segtop A (frmW (eq ms)) PM c -> impl segs (at_node segs) t (epost Q) ms ->
  (forall x ms' c', Q x ms' -> AST segtop A (frmW (eq ms')) PM c' -> realizes segs c' (T x)) ->
  realizes segs c (TT t T).
Proof using Hwx Hsegs Hrom.
  intros X chans t A PM Q T ms c HPM HFD HRD Htok Hc Him HK.
  assert (F0 : frm0 (ms_fcsr ms)).
  { destruct Hc as (_ & [E HF] & _ & _). rewrite E. exact HF. }
  apply (impl_realizes segs segtop Hwx Hsegs chans t A PM (fun x ms' => Q x ms' /\ frm0 (ms_fcsr ms')) T ms c HPM HFD HRD Htok).
  - eapply AST_conseq; [exact Hc | | intros mo Hmo; exact Hmo]. intros ms0 [H _]. exact H.
  - eapply impl_mono; [exact (impl_frm (at_node segs) t (epost Q) ms Him F0)|].
    intros [|x] ms' [H1 H2]; cbn [epost] in *; [exact I | exact (conj H1 H2)].
  - intros x ms' c' [HQ HF] Hc'. apply (HK x ms' c' HQ).
    eapply AST_conseq; [exact Hc' | | intros mo Hmo; exact Hmo]. intros ms0 E. split; [exact E | subst ms0; exact HF].
Qed.

End Bridge.

(* the channel-reader conjunct of [PMfd], for [impl_realizes_f]'s premise *)
Lemma ASTA_PM_reader : forall (RT : rt_sig) (Σ : rts RT) F0 fs0 mo, ARTM RT Σ mo /\ PMfd F0 fs0 mo -> m_channel_reader mo = true.
Proof. intros RT Σ F0 fs0 mo (_ & _ & _ & H). exact H. Qed.
