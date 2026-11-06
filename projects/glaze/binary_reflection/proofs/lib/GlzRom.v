(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool PString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Inductive rtree : Type := RLeaf | RNode (l : rtree) (o : option Z) (r : rtree).
Fixpoint rt_get (t : rtree) (k : positive) {struct k} : option Z :=
  match t with
  | RLeaf => None
  | RNode l o r => match k with xH => o | xO k' => rt_get l k' | xI k' => rt_get r k' end
  end.
Fixpoint rt_set (k : positive) (v : Z) (t : rtree) {struct k} : rtree :=
  match k, t with
  | xH, RLeaf => RNode RLeaf (Some v) RLeaf
  | xH, RNode l _ r => RNode l (Some v) r
  | xO k', RLeaf => RNode (rt_set k' v RLeaf) None RLeaf
  | xO k', RNode l o r => RNode (rt_set k' v l) o r
  | xI k', RLeaf => RNode RLeaf None (rt_set k' v RLeaf)
  | xI k', RNode l o r => RNode l o (rt_set k' v r)
  end.
(* [comment removed for export] *)
Fixpoint rt_all (f : positive -> Z -> bool) (ctx : positive -> positive) (t : rtree) : bool :=
  match t with
  | RLeaf => true
  | RNode l o r =>
      if (match o with Some v => f (ctx xH) v | None => true end)
      then (if rt_all f (fun k => ctx (xO k)) l then rt_all f (fun k => ctx (xI k)) r else false)
      else false
  end.
Lemma rt_all_get : forall f t ctx, rt_all f ctx t = true -> forall k v, rt_get t k = Some v -> f (ctx k) v = true.
Proof.
  intros f t. induction t as [|l IHl o r IHr]; intros ctx H k v G; [destruct k; discriminate|].
  cbn [rt_all] in H.
  destruct (match o with Some v0 => f (ctx xH) v0 | None => true end) eqn:Ho; [|discriminate].
  destruct (rt_all f (fun k0 => ctx (xO k0)) l) eqn:Hl; [|discriminate].
  destruct k as [k'|k'|]; cbn [rt_get] in G.
  - exact (IHr (fun k0 => ctx (xI k0)) H k' v G).
  - exact (IHl (fun k0 => ctx (xO k0)) Hl k' v G).
  - subst o. exact Ho.
Qed.

(* [comment removed for export] *)
Definition msize_ix (sz : msize) : nat := match sz with SZ1 => 0 | SZ2 => 1 | SZ4 => 2 | SZ8 => 3 end%nat.
Definition class_eqb (sz : msize) (sx : bool) (c : msize * bool) : bool :=
  if Nat.eqb (msize_ix sz) (msize_ix (fst c)) then Bool.eqb sx (snd c) else false.
Lemma class_eqb_eq : forall sz sx c, class_eqb sz sx c = true -> c = (sz, sx).
Proof.
  intros sz sx [sz' sx'] H. unfold class_eqb in H. cbn [fst snd] in H.
  destruct (Nat.eqb (msize_ix sz) (msize_ix sz')) eqn:E; [|discriminate].
  apply Bool.eqb_prop in H. subst sx'. destruct sz, sz'; try discriminate; reflexivity.
Qed.
Definition romtab := list ((msize * bool) * rtree).
Fixpoint romtab_get (tab : romtab) (sz : msize) (sx : bool) (j : Z) : option Z :=
  match tab with
  | [] => None
  | (c, t) :: rest =>
      if class_eqb sz sx c then match j with Zpos k => rt_get t k | _ => None end
      else romtab_get rest sz sx j
  end.

Section Reader.
Variable rd : msize -> bool -> Z -> option Z.
Definition entry_ok (sz : msize) (sx : bool) (k : positive) (v : Z) : bool :=
  match rd sz sx (Zpos k) with Some v' => Z.eqb v' v | None => false end.
Fixpoint romtab_check (tab : romtab) : bool :=
  match tab with
  | [] => true
  | ((sz, sx), t) :: rest => if rt_all (entry_ok sz sx) (fun k => k) t then romtab_check rest else false
  end.
Lemma romtab_get_ok : forall tab, romtab_check tab = true ->
  forall sz sx j v, romtab_get tab sz sx j = Some v -> rd sz sx j = Some v.
Proof.
  induction tab as [|[[sz' sx'] t] rest IH]; intros H sz sx j v G; [discriminate|].
  cbn [romtab_check] in H. destruct (rt_all (entry_ok sz' sx') (fun k => k) t) eqn:Ht; [|discriminate].
  cbn [romtab_get] in G. destruct (class_eqb sz sx (sz', sx')) eqn:Ec.
  - apply class_eqb_eq in Ec. injection Ec as -> ->. destruct j as [|k|k]; try discriminate.
    pose proof (rt_all_get _ _ _ Ht k v G) as E. unfold entry_ok in E.
    destruct (rd sz sx (Zpos k)) as [v'|]; [|discriminate]. apply Z.eqb_eq in E. subst v'. reflexivity.
  - exact (IH H sz sx j v G).
Qed.
Definition rom_fast (tab : romtab) (sz : msize) (sx : bool) (j : Z) : option Z :=
  match romtab_get tab sz sx j with Some v => Some v | None => rd sz sx j end.
Lemma rom_fast_eq : forall tab, romtab_check tab = true -> forall sz sx j, rom_fast tab sz sx j = rd sz sx j.
Proof.
  intros tab H sz sx j. unfold rom_fast. destruct (romtab_get tab sz sx j) as [v|] eqn:G; [|reflexivity].
  symmetry. exact (romtab_get_ok tab H sz sx j v G).
Qed.
(* [comment removed for export] *)
Fixpoint rt_gen (sz : msize) (sx : bool) (j step : Z) (cnt : nat) (t : rtree) : rtree :=
  match cnt with
  | O => t
  | S c => rt_gen sz sx (j + step) step c
             (match j, rd sz sx j with Zpos k, Some v => rt_set k v t | _, _ => t end)
  end.
End Reader.

(* [comment removed for export] *)
Definition pstr_eqb (a b : PrimString.string) : bool := match PrimString.compare a b with Eq => true | _ => false end.
Lemma pstr_eqb_eq : forall a b, pstr_eqb a b = true -> a = b.
Proof. intros a b H. unfold pstr_eqb in H. destruct (PrimString.compare a b) eqn:E; try discriminate. apply PString.compare_eq_correct. exact E. Qed.
Fixpoint pstrs_eqb (a b : list PrimString.string) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => if pstr_eqb x y then pstrs_eqb a' b' else false
  | _, _ => false
  end.
Lemma pstrs_eqb_eq : forall a b, pstrs_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [pstrs_eqb] in H; try discriminate; [reflexivity|].
  destruct (pstr_eqb x y) eqn:E; [|discriminate]. apply pstr_eqb_eq in E. subst y. rewrite (IH b H). reflexivity.
Qed.
Definition seg_eqb (a b : Segment) : bool :=
  if N.eqb (seg_base a) (seg_base b) then
    if N.eqb (seg_size a) (seg_size b) then
      if String.eqb (seg_perms a) (seg_perms b) then pstrs_eqb (seg_bytes a) (seg_bytes b) else false
    else false
  else false.
Lemma seg_eqb_eq : forall a b, seg_eqb a b = true -> a = b.
Proof.
  intros [ba sa pa ya] [bb sb pb yb] H. unfold seg_eqb in H. cbn [seg_base seg_size seg_perms seg_bytes] in H.
  destruct (N.eqb ba bb) eqn:E1; [|discriminate]. destruct (N.eqb sa sb) eqn:E2; [|discriminate].
  destruct (String.eqb pa pb) eqn:E3; [|discriminate].
  apply N.eqb_eq in E1. apply N.eqb_eq in E2. apply String.eqb_eq in E3. apply pstrs_eqb_eq in H. subst. reflexivity.
Qed.
Fixpoint segs_eqb (a b : list Segment) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => if seg_eqb x y then segs_eqb a' b' else false
  | _, _ => false
  end.
Lemma segs_eqb_eq : forall a b, segs_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [segs_eqb] in H; try discriminate; [reflexivity|].
  destruct (seg_eqb x y) eqn:E; [|discriminate]. apply seg_eqb_eq in E. subst y. rewrite (IH b H). reflexivity.
Qed.

(* [comment removed for export] *)
Class rom_cache (RD : list Segment -> msize -> bool -> Z -> option Z) : Type := {
  rc_segs : list Segment;
  rc_tab : romtab;
  rc_ok : romtab_check (RD rc_segs) rc_tab = true
}.
#[global] Instance rom_cache_none (RD : list Segment -> msize -> bool -> Z -> option Z) : rom_cache RD | 100 :=
  {| rc_segs := []; rc_tab := []; rc_ok := eq_refl |}.

(* [comment removed for export] *)
Definition rom_reader (RD : list Segment -> msize -> bool -> Z -> option Z) {RCX : rom_cache RD} (segs : list Segment)
  : msize -> bool -> Z -> option Z :=
  if segs_eqb segs rc_segs then rom_fast (RD segs) rc_tab else RD segs.
Lemma rom_reader_eq : forall RD (RCX : rom_cache RD) segs sz sx j, rom_reader RD segs sz sx j = RD segs sz sx j.
Proof.
  intros RD RCX segs sz sx j. unfold rom_reader. destruct (segs_eqb segs rc_segs) eqn:E; [|reflexivity].
  apply segs_eqb_eq in E. apply rom_fast_eq. rewrite E. exact rc_ok.
Qed.
