(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from this unit's ASN/MainExport.v (its Section's variables and imports) to carry the exported facts across the start-up run's renumbering of the plan variables at LPS 727298f3. *)
(* The main phase's exported facts ([MainExport]) under a renumbering of the plan variables.

   At LPS 727298f3 the start-up run allocates its plan variables at other numbers than the run the
   main phase's fact lists ([MainFactsAsan], [MainFactsBoth]) and register file were exported
   from.  The main phase reads those through a valuation [V]; [MainEntry] gives
   [V n := uev E (g n)] for the run's own map [g] (old numbering -> new, read from a probe), so a
   fact [f] holds of [V] when its renumbered copy [mfsh g f] holds of the run's [uev E].  The
   lemmas below carry each kind of fact across; the justification itself is [MainExport]'s,
   re-run on the renumbered copy against the state the run reaches.

   A fact the new run no longer gives (the launch block's layout changed) is replaced in place by
   a filler that holds of every memory ([mfill], [pfill]), so the positions of the others stay. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
(* [MainExport]'s own imports, in its order, so that [seg_rom] and [mrestrict] name its constants *)
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import PropExec AxSymExec3 AxSymExec3Sound AsanAcct AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport.
Import ListNotations. Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Section Ren.
  Variable g : nat -> nat.

  Fixpoint zsh (e : zexp) : zexp :=
    match e with
    | ZLit _ => e
    | ZV n => ZV (g n)
    | ZAdd a b => ZAdd (zsh a) (zsh b)
    | ZMul a b => ZMul (zsh a) (zsh b)
    | ZAnd a b => ZAnd (zsh a) (zsh b)
    | ZLtu a b => ZLtu (zsh a) (zsh b)
    end.
  Definition mfsh (f : mfact) : mfact :=
    match f with
    | MCell a w v => MCell (zsh a) w (zsh v)
    | MZeroC a n => MZeroC (zsh a) n
    | MRo a w v => MRo (zsh a) w (zsh v)
    | MZero a n => MZero (zsh a) n
    | MFill a n c => MFill (zsh a) n c
    | MImg _ _ => f
    | MWr a n => MWr (zsh a) n
    | MZeroS a n => MZeroS (zsh a) (zsh n)
    | MWrS a n => MWrS (zsh a) (zsh n)
    end.
  Definition pfsh (f : pfact) : pfact :=
    match f with
    | PVar n lo hi => PVar (g n) lo hi
    | PRange e lo hi => PRange (zsh e) lo hi
    | PDisj a1 n1 a2 n2 => PDisj (zsh a1) n1 (zsh a2) n2
    | PDisjS a1 n1 a2 n2 => PDisjS (zsh a1) (zsh n1) (zsh a2) (zsh n2)
    end.
  Definition bnsh (q : zexp * zexp) : zexp * zexp := (zsh (fst q), zsh (snd q)).
  Definition lesh (e : lentry) : lentry := match e with LMap b n k => LMap (zsh b) n k | LFog _ => e end.

  Lemma zv_zsh : forall V e, zv V (zsh e) = zv (fun n => V (g n)) e.
  Proof. intros V e. induction e; cbn [zsh zv]; congruence. Qed.

  Lemma mfact_ok_mfsh : forall segs V m f, mfact_ok segs V m (mfsh f) <-> mfact_ok segs (fun n => V (g n)) m f.
  Proof.
    intros segs V m f. destruct f; cbn [mfsh mfact_ok]; rewrite ?zv_zsh; split; intro H; exact H.
  Qed.

  Lemma pfact_ok_pfsh : forall V f, pfact_ok V (pfsh f) <-> pfact_ok (fun n => V (g n)) f.
  Proof. intros V f. destruct f; cbn [pfsh pfact_ok]; rewrite ?zv_zsh; split; intro H; exact H. Qed.

  Lemma ledger_den_lesh : forall V l maps, ledger_den V (map lesh l) maps <-> ledger_den (fun n => V (g n)) l maps.
  Proof.
    intros V l. induction l as [|e l IH]; intros maps; [split; intro H; exact H|].
    destruct e as [b n k|n]; cbn [map lesh ledger_den]; rewrite ?zv_zsh.
    - split; intros (maps' & E & H); exists maps'; (split; [exact E| apply IH; exact H]).
    - split; (intros [H|(iv & maps' & E & B & H)];
              [left; apply IH; exact H| right; exists iv, maps'; split; [exact E| split; [exact B| apply IH; exact H]]]).
  Qed.

  Lemma lentry_kind_ok_lesh : forall V mo e, lentry_kind_ok V mo (lesh e) <-> lentry_kind_ok (fun n => V (g n)) mo e.
  Proof.
    intros V mo [b n k|n]; [destruct k|]; cbn [lesh lentry_kind_ok]; rewrite ?zv_zsh; split; intro H; exact H.
  Qed.

  Lemma Forall_lentry_kind_ok_lesh : forall V mo l,
    Forall (lentry_kind_ok V mo) (map lesh l) -> Forall (lentry_kind_ok (fun n => V (g n)) mo) l.
  Proof.
    intros V mo l H. induction l as [|e l IH]; [constructor|].
    cbn [map] in H. apply Forall_cons_iff in H as [He Hl]. constructor.
    - exact (proj1 (lentry_kind_ok_lesh V mo e) He).
    - exact (IH Hl).
  Qed.

  Lemma allow_of_cons : forall shoff V bn vis, allow_of shoff V (bn :: vis) =
    [(pagedown (zv V (fst bn)), pageup (zv V (fst bn) + zv V (snd bn)));
     (pagedown (shoff + zv V (fst bn) / 8), pageup (shoff + (zv V (fst bn) + zv V (snd bn)) / 8))]
    ++ allow_of shoff V vis.
  Proof. reflexivity. Qed.

  Lemma allow_of_bnsh : forall shoff V vis, allow_of shoff V (map bnsh vis) = allow_of shoff (fun n => V (g n)) vis.
  Proof.
    intros shoff V vis. induction vis as [|[b n] vis IH]; [reflexivity|].
    cbn [map]. rewrite !allow_of_cons, IH. cbn [bnsh fst snd]. rewrite !zv_zsh. reflexivity.
  Qed.

  Lemma vis_rel_bnsh : forall E (ps : list (expr * expr)) vis,
    Forall2 (fun (p : expr * expr) (bn : zexp * zexp) =>
               bv_unsigned (edenot E (fst p)) = zv (uev E) (fst bn) /\ bv_unsigned (edenot E (snd p)) = zv (uev E) (snd bn)
               /\ 0 <= zv (uev E) (snd bn)) ps (map bnsh vis) ->
    Forall2 (fun (p : expr * expr) (bn : zexp * zexp) =>
               bv_unsigned (edenot E (fst p)) = zv (fun n => uev E (g n)) (fst bn)
               /\ bv_unsigned (edenot E (snd p)) = zv (fun n => uev E (g n)) (snd bn)
               /\ 0 <= zv (fun n => uev E (g n)) (snd bn)) ps vis.
  Proof.
    intros E ps vis. revert ps. induction vis as [|[b n] vis IH]; intros ps H; cbn [map] in H.
    - inversion H. constructor.
    - inversion H as [|x y l l' Hxy Hl]; subst. constructor; [|apply IH; exact Hl].
      cbn [bnsh fst snd] in Hxy |- *. rewrite !zv_zsh in Hxy. exact Hxy.
  Qed.
End Ren.

(* the filler that stands where a recorded fact no longer holds: it says nothing *)
Definition mfill : mfact := MZero (ZLit 0) 0.
Definition pfill : pfact := PRange (ZLit 0) 0 0.
Definition is_mfill (f : mfact) : bool := match f with MZero (ZLit 0) 0 => true | _ => false end.
Definition is_pfill (f : pfact) : bool := match f with PRange (ZLit 0) 0 0 => true | _ => false end.

Lemma mfill_ok : forall segs V m f, is_mfill f = true -> mfact_ok segs V m f.
Proof.
  intros segs V m [a w v|a n|a w v|a n|a n c|lo hi|a n|a n|a n] H; cbn [is_mfill] in H; try discriminate H.
  destruct a as [z| | | | |]; cbn in H; try discriminate H.
  destruct z; cbn in H; try discriminate H. destruct n; cbn in H; try discriminate H.
  cbn [mfact_ok]. intros i Hi. lia.
Qed.

Lemma pfill_ok : forall V f, is_pfill f = true -> pfact_ok V f.
Proof.
  intros V [n lo hi|e lo hi|a1 n1 a2 n2|a1 n1 a2 n2] H; cbn [is_pfill] in H; try discriminate H.
  destruct e as [z| | | | |]; cbn in H; try discriminate H. destruct z; cbn in H; try discriminate H.
  destruct lo; cbn in H; try discriminate H. destruct hi; cbn in H; try discriminate H.
  cbn [pfact_ok zv]. rewrite Z.mod_0_l by (unfold two64; cbn; discriminate). lia.
Qed.

(* a fact's justification against a state's knowledge, fillers allowed *)
Definition mjust (KN : list kentry) (HLO HHI : Z) (f : mfact) : bool :=
  is_mfill f || mjustify KN (var_ranges KN) HLO HHI f.
Definition pjust (KN : list kentry) (f : pfact) : bool := is_pfill f || pjustify KN (var_ranges KN) f.

(* the recorded list with each fact no state of [KNs] justifies under [g] replaced by the filler *)
Definition mkeep (g : nat -> nat) (KNs : list (list kentry)) (HLO HHI : Z) (l : list mfact) : list mfact :=
  map (fun f => if forallb (fun KN => mjust KN HLO HHI (mfsh g f)) KNs then f else mfill) l.
Definition pkeep (g : nat -> nat) (KNs : list (list kentry)) (l : list pfact) : list pfact :=
  map (fun f => if forallb (fun KN => pjust KN (pfsh g f)) KNs then f else pfill) l.

Section Export.
  Variable g : nat -> nat.
  Variable segs : list Segment.
  Variable E : env.
  Variable hidp : word -> bool.
  Variable FULL : word -> option byte.
  Variable KN : list kentry.
  Variables HLO HHI : Z.
  Hypothesis KOK : know_ok segs E (mrestrict hidp FULL) KN.
  Hypothesis HID_rom : forall a, hidp a = true -> seg_rom segs a = None.
  Hypothesis HULL_vis : forall a, HLO <= bv_unsigned a < HHI -> hidp a = false.

  Lemma mjust_sound : forall f, mjust KN HLO HHI (mfsh g f) = true -> mfact_ok segs (fun n => uev E (g n)) FULL f.
  Proof.
    intros f H. apply (proj1 (mfact_ok_mfsh g segs (uev E) FULL f)).
    unfold mjust in H. apply orb_prop in H as [H|H].
    - apply mfill_ok. exact H.
    - assert (X : forallb (mjustify KN (var_ranges KN) HLO HHI) [mfsh g f] = true).
      { cbn [forallb]. rewrite H. reflexivity. }
      destruct (export_sound segs E hidp FULL KN HLO HHI KOK HID_rom HULL_vis [mfsh g f] [] X eq_refl) as [Y _].
      exact (Forall_inv Y).
  Qed.

  Lemma pjust_sound : forall f, pjust KN (pfsh g f) = true -> pfact_ok (fun n => uev E (g n)) f.
  Proof.
    intros f H. apply (proj1 (pfact_ok_pfsh g (uev E) f)).
    unfold pjust in H. apply orb_prop in H as [H|H].
    - apply pfill_ok. exact H.
    - assert (X : forallb (pjustify KN (var_ranges KN)) [pfsh g f] = true).
      { cbn [forallb]. rewrite H. reflexivity. }
      destruct (export_sound segs E hidp FULL KN HLO HHI KOK HID_rom HULL_vis [] [pfsh g f] eq_refl X) as [_ Y].
      exact (Forall_inv Y).
  Qed.

  Theorem export_sound_g : forall MF PF,
    forallb (fun f => mjust KN HLO HHI (mfsh g f)) MF = true ->
    forallb (fun f => pjust KN (pfsh g f)) PF = true ->
    Forall (mfact_ok segs (fun n => uev E (g n)) FULL) MF /\ Forall (pfact_ok (fun n => uev E (g n))) PF.
  Proof.
    intros MF PF HM HP. split.
    - apply Forall_forall. intros f Hf. apply mjust_sound. exact (proj1 (forallb_forall _ _) HM f Hf).
    - apply Forall_forall. intros f Hf. apply pjust_sound. exact (proj1 (forallb_forall _ _) HP f Hf).
  Qed.
End Export.
