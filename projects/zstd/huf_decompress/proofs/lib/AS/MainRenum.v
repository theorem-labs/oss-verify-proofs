(* SPDX-License-Identifier: MIT *)
(* Renumbering the main entry's recorded facts (LPS 727298f3).  The facts MainFactsAsan/Both
   state about the main entry name the start-up run's variables by number; at LPS 727298f3 the
   start-up run numbers its fresh variables differently (more launch variables, more of the auxv
   read), so the hand-off state the run computes names them at other numbers.  [zsh f] renames a
   fact's variables by a map [f] read off the run; [zv_zsh] says a renamed fact read under an
   environment [V] is the original fact read under [V o f].  So the facts are justified against the
   computed state after renaming, and stated about [fun n => V (f n)] in their recorded numbering:
   nothing that reads them changes.  Copied from projects/zstd/simple_decompress/proofs/lib/AS/MainRenum.v
   (projects/zstd/fse_read_ncount/proofs/lib/AS/MainRenum.v with the two lemmas below on visible ranges). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan MainExport.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Section Ren.
  Variable f : nat -> nat.
  Definition Vf (V : nat -> Z) : nat -> Z := fun n => V (f n).

  Fixpoint zsh (e : zexp) : zexp :=
    match e with
    | ZLit z => ZLit z
    | ZV n => ZV (f n)
    | ZAdd a b => ZAdd (zsh a) (zsh b)
    | ZMul a b => ZMul (zsh a) (zsh b)
    | ZAnd a b => ZAnd (zsh a) (zsh b)
    | ZLtu a b => ZLtu (zsh a) (zsh b)
    end.

  Lemma zv_zsh : forall V e, zv V (zsh e) = zv (Vf V) e.
  Proof. intros V e. induction e; cbn; rewrite ?IHe1, ?IHe2; reflexivity. Qed.

  Definition msh (x : mfact) : mfact :=
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

  Definition bnsh (bn : zexp * zexp) : zexp * zexp := (zsh (fst bn), zsh (snd bn)).

  Definition lsh (e : lentry) : lentry :=
    match e with
    | LMap b n k => LMap (zsh b) n k
    | LFog n => LFog n
    end.

  Lemma mfact_ok_msh : forall segs V m x, mfact_ok segs V m (msh x) <-> mfact_ok segs (Vf V) m x.
  Proof. intros segs V m []; cbn [mfact_ok msh]; rewrite ?zv_zsh; try reflexivity;
    split; intros H; intros; rewrite ?zv_zsh in *; auto. Qed.

  Lemma pfact_ok_pfsh : forall V x, pfact_ok V (pfsh x) <-> pfact_ok (Vf V) x.
  Proof. intros V []; cbn [pfact_ok pfsh]; rewrite ?zv_zsh; reflexivity. Qed.

  Lemma Forall_mfact_ok_msh : forall segs V m l,
    Forall (mfact_ok segs V m) (map msh l) -> Forall (mfact_ok segs (Vf V) m) l.
  Proof.
    intros segs V m l H. rewrite Forall_map in H. eapply Forall_impl; [|exact H].
    intros x Hx. apply mfact_ok_msh. exact Hx.
  Qed.

  Lemma Forall_pfact_ok_pfsh : forall V l,
    Forall (pfact_ok V) (map pfsh l) -> Forall (pfact_ok (Vf V)) l.
  Proof.
    intros V l H. rewrite Forall_map in H. eapply Forall_impl; [|exact H].
    intros x Hx. apply pfact_ok_pfsh. exact Hx.
  Qed.

  Lemma ledger_den_lsh : forall V l maps, ledger_den V (map lsh l) maps -> ledger_den (Vf V) l maps.
  Proof.
    intros V l. induction l as [|e l IH]; intros maps H; cbn in H |- *; [exact H|].
    destruct e as [b n k|n]; cbn in H.
    - destruct H as (maps' & -> & H). exists maps'. rewrite <- zv_zsh. split; [reflexivity| apply IH; exact H].
    - destruct H as [H|(iv & maps' & -> & Hn & H)]; [left; apply IH; exact H|].
      right. exists iv, maps'. split; [reflexivity|]. split; [exact Hn| apply IH; exact H].
  Qed.

  Lemma lentry_kind_ok_lsh : forall V mo e, lentry_kind_ok V mo (lsh e) -> lentry_kind_ok (Vf V) mo e.
  Proof. intros V mo [b n [] | n]; cbn [lentry_kind_ok lsh]; rewrite ?zv_zsh; auto. Qed.

  (* the visible-range list renumbered: [vis_match_sound]'s pairing, and [allow_of], read in the
     recorded numbering (msgpack-c/unpack_pack_fuzzer's AS/MainRenum.v adds the same two) *)
  Lemma Forall2_map_bnsh : forall (V : nat -> Z) (R : expr * expr -> Z -> Z -> Prop) ps vis,
    Forall2 (fun (p : expr * expr) (bn : zexp * zexp) => R p (zv V (fst bn)) (zv V (snd bn))) ps (map bnsh vis) ->
    Forall2 (fun (p : expr * expr) (bn : zexp * zexp) => R p (zv (Vf V) (fst bn)) (zv (Vf V) (snd bn))) ps vis.
  Proof.
    intros V R ps vis. revert ps. induction vis as [|bn vis IH]; intros ps H; cbn [map] in H.
    - inversion H; subst. constructor.
    - inversion H as [|p bn' ps' vis' Hp Hr]; subst. constructor; [|apply IH; exact Hr].
      cbn [bnsh fst snd] in Hp. rewrite !zv_zsh in Hp. exact Hp.
  Qed.

  Lemma allow_of_bnsh : forall shoff V vis, allow_of shoff V (map bnsh vis) = allow_of shoff (Vf V) vis.
  Proof.
    intros shoff V vis. unfold allow_of. induction vis as [|bn vis IH]; cbn [map flat_map]; [reflexivity|].
    rewrite IH. cbn [bnsh fst snd]. rewrite !zv_zsh. reflexivity.
  Qed.
End Ren.
