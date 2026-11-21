(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import PropExec MState Mem Exec ITree Nodes CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.


Fixpoint hmap {R R'} (g : R -> hist -> R') (t : itree node R) (h : hist) : itree node R' :=
  match t with
  | Ret r => Ret (g r h)
  | Vis n k => Vis n (fun rsp => hmap g (k rsp) (h ++ [HR rsp]))
  end.

Section HmapPaths.
Variable step : node -> Model -> resp -> Model -> list event -> Prop.
Variable exit_ : node -> Model -> word -> Model -> Prop.

Lemma tpath_hmap : forall {R R'} (g : R -> hist -> R') (t : itree node R) h mo tr r' mo',
  tpath step (hmap g t h) mo tr r' mo' -> exists r h', r' = g r h' /\ tpath step t mo tr r mo'.
Proof.
  intros R R' g t. induction t as [r|n k IH]; intros h mo tr r' mo' Hp; cbn in Hp.
  - destruct Hp as (E1 & E2 & E3). exists r, h. split; [symmetry; exact E1|]. cbn. auto.
  - destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & E).
    destruct (IH rsp _ _ _ _ _ Hp) as (r & h' & Er & Hp'). exists r, h'. split; [exact Er|].
    cbn. exists rsp, mo1, evs, tr'. auto.
Qed.

Lemma tpath_hmap_inv : forall {R R'} (g : R -> hist -> R') (t : itree node R) h mo tr r mo',
  tpath step t mo tr r mo' -> exists h', tpath step (hmap g t h) mo tr (g r h') mo'.
Proof.
  intros R R' g t. induction t as [r0|n k IH]; intros h mo tr r mo' Hp; cbn in Hp.
  - destruct Hp as (E1 & E2 & E3). exists h. cbn. subst. auto.
  - destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & E).
    destruct (IH rsp (h ++ [HR rsp]) _ _ _ _ Hp) as (h' & Hp'). exists h'.
    cbn. exists rsp, mo1, evs, tr'. auto.
Qed.

Lemma texit_hmap : forall {R R'} (g : R -> hist -> R') (t : itree node R) h mo tr,
  texit step exit_ (hmap g t h) mo tr <-> texit step exit_ t mo tr.
Proof.
  intros R R' g t. induction t as [r|n k IH]; intros h mo tr; cbn; [tauto|].
  split.
  - intros [H|(rsp & mo1 & evs & tr' & Hst & Hx & E)]; [left; exact H|].
    right. exists rsp, mo1, evs, tr'. split; [exact Hst|]. split; [apply (IH rsp) in Hx; exact Hx| exact E].
  - intros [H|(rsp & mo1 & evs & tr' & Hst & Hx & E)]; [left; exact H|].
    right. exists rsp, mo1, evs, tr'. split; [exact Hst|]. split; [apply (IH rsp); exact Hx| exact E].
Qed.
End HmapPaths.


Section CMonad.
Context {St : Type}.

Definition MC (A : Type) : Type := St -> ctree node (exc (A * St)).

Definition cebind {A B} (c : ctree node (exc A)) (f : A -> ctree node (exc B)) : ctree node (exc B) :=
  cbind c (fun r => match r with Unr => CRet Unr | Ok a => f a end).

Definition cmret {A} (a : A) : MC A := fun s => CRet (Ok (a, s)).
Definition cmbind {A B} (m : MC A) (f : A -> MC B) : MC B := fun s => cebind (m s) (fun p => f (fst p) (snd p)).
Definition clift {A} (m : M St A) : MC A := fun s => cinj (m s).
Definition cchoice {A} (a b : MC A) : MC A := fun s => CChoice (a s) (b s).


Definition tagr {A} (r : exc (A * St)) (h : hist) : exc ((A * hist) * St) :=
  match r with Unr => Unr | Ok p => Ok ((fst p, h), snd p) end.

Fixpoint resX {A} (D : hist -> bool) (h : hist) (c : ctree node (exc (A * St))) : itree node (exc ((A * hist) * St)) :=
  match c with
  | CRet r => Ret (tagr r h)
  | CVis n k => Vis n (fun rsp => resX D (h ++ [HR rsp]) (k rsp))
  | CChoice a b => if D h then resX D (h ++ [HD true]) a else resX D (h ++ [HD false]) b
  end.

Definition RES {A} (D : hist -> bool) (h : hist) (m : MC A) : M St A := fun s => res D h (m s).
Definition RESX {A} (D : hist -> bool) (h : hist) (m : MC A) : M St (A * hist) := fun s => resX D h (m s).
Definition mtag {A} (m : M St A) (h : hist) : M St (A * hist) := fun s => hmap tagr (m s) h.

Lemma resX_cinj : forall {A} D (t : itree node (exc (A * St))) h, resX D h (cinj t) = hmap tagr t h.
Proof.
  intros A D t. induction t as [r|n k IH]; intros h; cbn; [reflexivity|].
  f_equal. apply functional_extensionality. intros rsp. apply IH.
Qed.

Lemma resX_cebind : forall {A B} D (c : ctree node (exc (A * St))) (f : A * St -> ctree node (exc (B * St))) h,
  resX D h (cebind c f) = ebind (resX D h c) (fun q => resX D (snd (fst q)) (f (fst (fst q), snd q))).
Proof.
  intros A B D c f. induction c as [r|n k IH|a IHa b IHb]; intros h.
  - destruct r as [|[x s]]; reflexivity.
  - cbn. f_equal. apply functional_extensionality. intros rsp. apply IH.
  - cbn. destruct (D h); [apply IHa| apply IHb].
Qed.

Lemma res_cebind : forall {A B} D (c : ctree node (exc (A * St))) (f : A * St -> ctree node (exc (B * St))) h,
  res D h (cebind c f) = ebind (resX D h c) (fun q => res D (snd (fst q)) (f (fst (fst q), snd q))).
Proof.
  intros A B D c f. induction c as [r|n k IH|a IHa b IHb]; intros h.
  - destruct r as [|[x s]]; reflexivity.
  - cbn. f_equal. apply functional_extensionality. intros rsp. apply IH.
  - cbn. destruct (D h); [apply IHa| apply IHb].
Qed.

Lemma res_resX : forall {A} D (c : ctree node (exc (A * St))) h,
  res D h c = ebind (resX D h c) (fun q => Ret (Ok (fst (fst q), snd q))).
Proof.
  intros A D c. induction c as [r|n k IH|a IHa b IHb]; intros h.
  - destruct r as [|[x s]]; reflexivity.
  - cbn. f_equal. apply functional_extensionality. intros rsp. apply IH.
  - cbn. destruct (D h); [apply IHa| apply IHb].
Qed.

Lemma RESX_ret : forall {A} D h (a : A), RESX D h (cmret a) = mret (a, h).
Proof. intros. reflexivity. Qed.

Lemma RESX_lift : forall {A} D h (m : M St A), RESX D h (clift m) = mtag m h.
Proof. intros A D h m. apply functional_extensionality. intros s. unfold RESX, clift, mtag. apply resX_cinj. Qed.

Lemma RESX_bind : forall {A B} D h (m : MC A) (f : A -> MC B),
  RESX D h (cmbind m f) = mbind (RESX D h m) (fun ah => RESX D (snd ah) (f (fst ah))).
Proof.
  intros A B D h m f. apply functional_extensionality. intros s. unfold RESX, cmbind, mbind.
  rewrite resX_cebind. reflexivity.
Qed.

Lemma RESX_choice : forall {A} D h (a b : MC A),
  RESX D h (cchoice a b) = if D h then RESX D (h ++ [HD true]) a else RESX D (h ++ [HD false]) b.
Proof. intros A D h a b. apply functional_extensionality. intros s. unfold RESX, cchoice. cbn. destruct (D h); reflexivity. Qed.

Lemma RES_RESX : forall {A} D h (m : MC A), RES D h m = mbind (RESX D h m) (fun ah => mret (fst ah)).
Proof. intros A D h m. apply functional_extensionality. intros s. unfold RES, RESX, mbind, mret. apply res_resX. Qed.

Lemma RES_lift : forall {A} D h (m : M St A), RES D h (clift m) = m.
Proof. intros A D h m. apply functional_extensionality. intros s. unfold RES, clift. apply res_cinj. Qed.

Section Machine.
Variable segs : list Segment.

Definition implMC {A} (c : MC A) (s : St) (Q : A -> St -> machine_state -> Prop) (ms : machine_state) : Prop :=
  implC segs (at_node segs) (c s) (epost (fun p => Q (fst p) (snd p))) ms.

Lemma implMC_lift : forall {A} (m : M St A) s Q ms, implM segs m s Q ms -> implMC (clift m) s Q ms.
Proof. intros A m s Q ms H. unfold implMC, clift. apply implC_cinj. exact H. Qed.

Lemma implMC_ret : forall {A} (a : A) s Q ms, evt segs (Q a s) ms -> implMC (cmret a) s Q ms.
Proof. intros A a s Q ms H. exact H. Qed.

Lemma implMC_bind : forall {A B} (m : MC A) (f : A -> MC B) s Q1 Q ms,
  implMC m s Q1 ms ->
  (forall a s' ms', Q1 a s' ms' -> implMC (f a) s' Q ms') ->
  implMC (cmbind m f) s Q ms.
Proof.
  intros A B m f s Q1 Q ms Hm Hf. unfold implMC, cmbind, cebind in *.
  eapply implC_bind; [exact Hm|]. intros [|[a s']] ms' H; cbn in H |- *.
  - apply evt_done. exact I.
  - apply Hf. exact H.
Qed.

Lemma implMC_mono : forall {A} (m : MC A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
  implMC m s Q ms -> (forall a s' ms', Q a s' ms' -> Q' a s' ms') -> implMC m s Q' ms.
Proof.
  intros A m s Q Q' ms H HQ. unfold implMC in *. eapply implC_mono; [exact H|].
  intros [|[a s']] ms'; cbn; auto.
Qed.

Lemma implMC_evt : forall {A} (c : MC A) s Q P ms,
  evt segs P ms -> (forall ms', P ms' -> implMC c s Q ms') -> implMC c s Q ms.
Proof. intros A c s Q P ms H K. unfold implMC in *. eapply implC_evt; eauto. Qed.

Lemma implMC_choice_l : forall {A} (a b : MC A) s Q ms, implMC a s Q ms -> implMC (cchoice a b) s Q ms.
Proof. intros A a b s Q ms H. unfold implMC, cchoice. apply implC_choice_l. exact H. Qed.
Lemma implMC_choice_r : forall {A} (a b : MC A) s Q ms, implMC b s Q ms -> implMC (cchoice a b) s Q ms.
Proof. intros A a b s Q ms H. unfold implMC, cchoice. apply implC_choice_r. exact H. Qed.

Theorem implMC_RES : forall {A} (c : MC A) s Q ms, implMC c s Q ms -> exists D, implM segs (RES D [] c) s Q ms.
Proof. intros A c s Q ms H. unfold implMC in H. destruct (implC_res node segs (at_node segs) (c s) _ ms H) as [D HD]. exists D. exact HD. Qed.

End Machine.
End CMonad.

Arguments MC St A : clear implicits.

