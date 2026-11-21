(* SPDX-License-Identifier: MIT *)
(* Written for this unit's LPS 727298f3 port (OSSV-653).
   The main phase's recorded facts (AMainEntry.MainFactsAsan and the ASan+UBSan twin) name the
   start-up's fresh variables by the numbers the start-up run gave them before the launch grew
   (V_G and V_GID, and the longer auxv walk).  The start-up chain at 727298f3 is renumbered by a
   table read off probe runs (AS/PlanRegen.v, tshift); the hand-off gives the main phase the
   valuation composed with that renumbering, so the main phase's facts, indices and proofs keep
   their numbers.  These are the renamings of the fact forms and the lemmas that move a fact
   across them: a fact renamed by [f] holds under [V] exactly when the fact holds under
   [fun n => V (f n)]. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import MainExport.
Import ListNotations.
Open Scope Z_scope.

Section Shift.
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
  Proof. intros V e. induction e; cbn [zsh zv]; congruence. Qed.

  Definition mfsh (x : mfact) : mfact :=
    match x with
    | MCell a w v => MCell (zsh a) w (zsh v)
    | MZeroC a n => MZeroC (zsh a) n
    | MRo a w v => MRo (zsh a) w (zsh v)
    | MZero a n => MZero (zsh a) n
    | MFill a n c => MFill (zsh a) n c
    | MImg lo hi => MImg lo hi
    | MWr a n => MWr (zsh a) n
    | MZeroS a n => MZeroS (zsh a) (zsh n)
    | MWrS a n => MWrS (zsh a) (zsh n)
    end.

  Definition pfsh (x : pfact) : pfact :=
    match x with
    | PVar n lo hi => PVar (f n) lo hi
    | PRange e lo hi => PRange (zsh e) lo hi
    | PDisj a1 n1 a2 n2 => PDisj (zsh a1) n1 (zsh a2) n2
    | PDisjS a1 n1 a2 n2 => PDisjS (zsh a1) (zsh n1) (zsh a2) (zsh n2)
    end.

  Definition pzsh (p : zexp * zexp) : zexp * zexp := (zsh (fst p), zsh (snd p)).

  Definition lesh (x : lentry) : lentry :=
    match x with
    | LMap b n k => LMap (zsh b) n k
    | LFog n => LFog n
    end.

  Lemma mfact_ok_mfsh : forall segs V m x,
    mfact_ok segs V m (mfsh x) <-> mfact_ok segs (fun n => V (f n)) m x.
  Proof. intros segs V m x. destruct x; cbn [mfsh mfact_ok]; rewrite ?zv_zsh; reflexivity. Qed.

  Lemma pfact_ok_pfsh : forall V x, pfact_ok (V) (pfsh x) <-> pfact_ok (fun n => V (f n)) x.
  Proof. intros V x. destruct x; cbn [pfsh pfact_ok]; rewrite ?zv_zsh; reflexivity. Qed.

  Lemma Forall_mfsh : forall segs V m l,
    Forall (mfact_ok segs V m) (map mfsh l) -> Forall (mfact_ok segs (fun n => V (f n)) m) l.
  Proof.
    intros segs V m l H. rewrite Forall_map in H. eapply Forall_impl; [|exact H].
    intros x Hx. apply mfact_ok_mfsh. exact Hx.
  Qed.

  Lemma Forall_pfsh : forall V l,
    Forall (pfact_ok V) (map pfsh l) -> Forall (pfact_ok (fun n => V (f n))) l.
  Proof.
    intros V l H. rewrite Forall_map in H. eapply Forall_impl; [|exact H].
    intros x Hx. apply pfact_ok_pfsh. exact Hx.
  Qed.

  Lemma allow_of_pzsh : forall shoff V vis,
    allow_of shoff V (map pzsh vis) = allow_of shoff (fun n => V (f n)) vis.
  Proof.
    intros shoff V vis. unfold allow_of. induction vis as [|[b n] vis IH]; [reflexivity|].
    cbn [map flat_map pzsh fst snd]. rewrite !zv_zsh, IH. reflexivity.
  Qed.

  Lemma ledger_den_lesh : forall V l maps,
    ledger_den V (map lesh l) maps <-> ledger_den (fun n => V (f n)) l maps.
  Proof.
    intros V l. induction l as [|[b n k|n] l IH]; intros maps; cbn [map lesh ledger_den]; [reflexivity| |].
    - rewrite zv_zsh. split; intros (maps' & E & H); exists maps'; split; try exact E; apply IH; exact H.
    - split; (intros [H|(iv & maps' & E & B & H)]; [left; apply IH; exact H | right; exists iv, maps'; split; [exact E|]; split; [exact B| apply IH; exact H]]).
  Qed.

  Lemma lentry_kind_ok_lesh : forall V mo x,
    lentry_kind_ok V mo (lesh x) <-> lentry_kind_ok (fun n => V (f n)) mo x.
  Proof. intros V mo x. destruct x as [b n k|n]; cbn [lesh]; [destruct k|]; cbn [lentry_kind_ok]; rewrite ?zv_zsh; reflexivity. Qed.
End Shift.
