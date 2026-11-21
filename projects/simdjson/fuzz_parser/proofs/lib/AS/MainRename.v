(* SPDX-License-Identifier: MIT *)
(* A renaming of the variables of the main-entry facts (AS/MainExport.v's [zexp], [mfact], [pfact]).
   The main-phase facts were recorded against the start-up hand-off state of the model the plans
   were written for; at LPS 727298f3 the start-up run allocates its fresh variables at other
   numbers.  [V o f] read through the old numbering is [V] read through the renamed facts, so a
   recorded fact list in the old numbering holds exactly when its renaming by [f] holds. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import MainExport.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Import ListNotations.
Open Scope Z_scope.

Section Rename.
  Variable f : nat -> nat.

  Fixpoint zsh (e : zexp) : zexp :=
    match e with
    | ZLit z => ZLit z
    | ZV n => ZV (f n)
    | ZAdd a b => ZAdd (zsh a) (zsh b)
    | ZMul a b => ZMul (zsh a) (zsh b)
    | ZAnd a b => ZAnd (zsh a) (zsh b)
    | ZLtu a b => ZLtu (zsh a) (zsh b)
    end.

  Lemma zv_zsh : forall V e, zv V (zsh e) = zv (fun n => V (f n)) e.
  Proof. intros V e. induction e; simpl; try rewrite IHe1, IHe2; reflexivity. Qed.

  Definition mfsh (F : mfact) : mfact :=
    match F with
    | MCell a w v => MCell (zsh a) w (zsh v)
    | MZeroC a n => MZeroC (zsh a) n
    | MRo a w v => MRo (zsh a) w (zsh v)
    | MZero a n => MZero (zsh a) n
    | MFill a n c => MFill (zsh a) n c
    | MImg lo hi => MImg lo hi
    | MWr a n => MWr (zsh a) n
    | MZeroS a n => MZeroS (zsh a) (zsh n)
    | MWrS a n => MWrS (zsh a) (zsh n)
    | MBlobD a n => MBlobD (zsh a) n
    | MDefS a n => MDefS (zsh a) (zsh n)
    end.

  Definition pfsh (F : pfact) : pfact :=
    match F with
    | PVar n lo hi => PVar (f n) lo hi
    | PRange e lo hi => PRange (zsh e) lo hi
    | PDisj a1 n1 a2 n2 => PDisj (zsh a1) n1 (zsh a2) n2
    | PDisjS a1 n1 a2 n2 => PDisjS (zsh a1) (zsh n1) (zsh a2) (zsh n2)
    end.

  Lemma mfact_ok_mfsh : forall segs V m F, mfact_ok segs V m (mfsh F) <-> mfact_ok segs (fun n => V (f n)) m F.
  Proof. intros segs V m F. destruct F; cbn [mfsh mfact_ok]; rewrite ?zv_zsh; reflexivity. Qed.

  Lemma pfact_ok_pfsh : forall V F, pfact_ok V (pfsh F) <-> pfact_ok (fun n => V (f n)) F.
  Proof. intros V F. destruct F; cbn [pfsh pfact_ok]; rewrite ?zv_zsh; reflexivity. Qed.

  Lemma Forall_mfsh : forall segs V m l,
    Forall (mfact_ok segs V m) (map mfsh l) -> Forall (mfact_ok segs (fun n => V (f n)) m) l.
  Proof.
    intros segs V m l H. rewrite Forall_map in H. eapply Forall_impl; [|exact H].
    intros F HF. apply mfact_ok_mfsh. exact HF.
  Qed.

  Lemma Forall_pfsh : forall V l, Forall (pfact_ok V) (map pfsh l) -> Forall (pfact_ok (fun n => V (f n))) l.
  Proof.
    intros V l H. rewrite Forall_map in H. eapply Forall_impl; [|exact H].
    intros F HF. apply pfact_ok_pfsh. exact HF.
  Qed.

  (** the visibility list and the ledger, renamed *)
  Definition zpsh (p : zexp * zexp) : zexp * zexp := (zsh (fst p), zsh (snd p)).
  Definition lsh (e : lentry) : lentry :=
    match e with LMap b n k => LMap (zsh b) n k | LFog n => LFog n end.

  Lemma allow_of_zpsh : forall off V l, allow_of off V (map zpsh l) = allow_of off (fun n => V (f n)) l.
  Proof.
    intros off V l. induction l as [|[b n] l IH]; [reflexivity|].
    cbn [map allow_of flat_map zpsh fst snd]. unfold allow_of in IH. rewrite IH, !zv_zsh. reflexivity.
  Qed.

  Lemma ledger_den_lsh : forall V l maps, ledger_den V (map lsh l) maps -> ledger_den (fun n => V (f n)) l maps.
  Proof.
    intros V l. induction l as [|[b n k|n] l IH]; intros maps H; cbn [map lsh ledger_den] in H |- *; [exact H| |].
    - destruct H as (maps' & -> & H). exists maps'. rewrite <- zv_zsh. split; [reflexivity| exact (IH _ H)].
    - destruct H as [H|(iv & maps' & -> & Hs & H)];
        [left; exact (IH _ H)| right; exists iv, maps'; split; [reflexivity|]; split; [exact Hs| exact (IH _ H)]].
  Qed.

  Lemma lentry_kind_ok_lsh : forall V mo e, lentry_kind_ok V mo (lsh e) -> lentry_kind_ok (fun n => V (f n)) mo e.
  Proof. intros V mo [b n k|n] H; [destruct k|]; cbn [lsh lentry_kind_ok] in *; rewrite ?zv_zsh in H; exact H. Qed.

  Lemma Forall_lsh_kind : forall V mo l,
    Forall (lentry_kind_ok V mo) (map lsh l) -> Forall (lentry_kind_ok (fun n => V (f n)) mo) l.
  Proof.
    intros V mo l H. rewrite Forall_map in H. eapply Forall_impl; [|exact H].
    intros e He. apply lentry_kind_ok_lsh. exact He.
  Qed.
End Rename.
