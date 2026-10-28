(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsDrvDefs ECH_Iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition TRCAP : nat := 4000%nat.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition DRV_DEMANDS : list (Z * list Z) :=
  [(APC0_MALLOC, [0x1eed74]); (APC0_MALLOC, [0x1eedc8]); (APC0_FREE, [0x1eedec]); (APC0_FREE, [0x1eef20]);
   (APC0_MALLOC, [0x1ef05c]); (APC0_FREE, [0x1ef0f4])].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition prefixes1 (l : list Z) : list (list Z) := map (fun j => firstn j l) (seq 1 (length l)).

Fixpoint zl_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb x y && zl_eqb a' b'
  | _, _ => false
  end.
Lemma zl_eqb_eq : forall a b, zl_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] Hb; cbn in Hb; try discriminate; [reflexivity|].
  apply andb_prop in Hb as [Hx Hr]. apply Z.eqb_eq in Hx. subst. f_equal. apply IH. exact Hr.
Qed.
Lemma zl_eqb_refl : forall a, zl_eqb a a = true.
Proof. induction a as [|x a IH]; [reflexivity|]. cbn. rewrite Z.eqb_refl, IH. reflexivity. Qed.
Definition zl_inb (l : list Z) (L : list (list Z)) : bool := existsb (zl_eqb l) L.
Lemma zl_inb_In : forall l L, zl_inb l L = true -> In l L.
Proof.
  intros l L Hb. unfold zl_inb in Hb. apply existsb_exists in Hb as (x & Hin & Hx). apply zl_eqb_eq in Hx. subst. exact Hin.
Qed.
Lemma In_zl_inb : forall l L, In l L -> zl_inb l L = true.
Proof. intros l L Hin. unfold zl_inb. apply existsb_exists. exists l. split; [exact Hin| apply zl_eqb_refl]. Qed.
Fixpoint zll_nodup (L : list (list Z)) : list (list Z) :=
  match L with [] => [] | l :: r => if zl_inb l r then zll_nodup r else l :: zll_nodup r end.
Lemma zll_nodup_In : forall L l, In l L -> In l (zll_nodup L).
Proof.
  induction L as [|x L IH]; intros l Hin; [destruct Hin|]. cbn. destruct Hin as [->|Hin].
  - destruct (zl_inb l L) eqn:E; [apply IH; apply zl_inb_In; exact E| left; reflexivity].
  - destruct (zl_inb x L); [apply IH; exact Hin| right; apply IH; exact Hin].
Qed.

Definition trlist_of (D : list (Z * list Z)) : list (list Z) :=
  zll_nodup (flat_map (fun pp : Z * list Z => prefixes1 (fst pp :: snd pp)) D).

Lemma prefixes1_In : forall (l : list Z) j, l <> [] -> (1 <= j)%nat -> In (firstn j l) (prefixes1 l).
Proof.
  intros l j NE Hj. unfold prefixes1. destruct (Nat.le_gt_cases j (length l)) as [LE|GT].
  - apply in_map_iff. exists j. split; [reflexivity| apply in_seq; lia].
  - rewrite firstn_all2 by lia. apply in_map_iff. exists (length l). split; [apply firstn_all|].
    apply in_seq. destruct l; [congruence| cbn [length]; lia].
Qed.

(* [comment removed for export] *)
Lemma trlist_demand : forall D pc0 t, In (pc0, t) D -> ~ In pc0 t -> trace_ok (trlist_of D) pc0 t.
Proof.
  intros D pc0 t Hin NS. split; [exact NS|]. intros j Hj. unfold trlist_of. apply zll_nodup_In.
  apply in_flat_map. exists (pc0, t). split; [exact Hin|]. cbn [fst snd]. apply prefixes1_In; [discriminate| exact Hj].
Qed.

(* [comment removed for export] *)
Definition demands_okb (D : list (Z * list Z)) : bool :=
  forallb (fun pp : Z * list Z => negb (existsb (Z.eqb (fst pp)) (snd pp))) D.
Lemma demands_okb_sound : forall D pc0 t, demands_okb D = true -> In (pc0, t) D -> ~ In pc0 t.
Proof.
  intros D pc0 t OK Hin NS. unfold demands_okb in OK. rewrite forallb_forall in OK. specialize (OK _ Hin). cbn [fst snd] in OK.
  apply negb_true_iff in OK. assert (E : existsb (Z.eqb pc0) t = true) by (apply existsb_exists; exists pc0; split; [exact NS| apply Z.eqb_refl]).
  congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition all_demands (L : alib) (LD : list (Z * list Z)) : list (Z * list Z) :=
  DRV_DEMANDS ++ pf_shift P_FUZZ_RA (al_PF L) ++ LD.

Section ForInstance.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable L : alib.
  Variable LD : list (Z * list Z).
  Hypothesis HTR : as_TR H = trlist_of (all_demands L LD).
  Hypothesis DOK : demands_okb (all_demands L LD) = true.

  Lemma inst_demand : forall pc0 t, In (pc0, t) (all_demands L LD) -> trace_ok (as_TR H) pc0 t.
  Proof. intros pc0 t Hin. rewrite HTR. apply trlist_demand; [exact Hin| exact (demands_okb_sound _ _ _ DOK Hin)]. Qed.

  (* [comment removed for export] *)
  Lemma inst_lib_demand : forall pc0 t, In (pc0, t) LD -> trace_ok (as_TR H) pc0 t.
  Proof. intros pc0 t Hin. apply inst_demand. unfold all_demands. apply in_or_app. right. apply in_or_app. right. exact Hin. Qed.

  Local Ltac drv k := apply inst_demand; unfold all_demands; apply in_or_app; left; unfold DRV_DEMANDS; cbn [In]; tauto.

  Theorem inst_K_tr : al_tr_ok L H -> adrv_traces H L.
  Proof.
    intros LT. unfold adrv_traces.
    split; [drv 0|]. split; [drv 1|]. split; [drv 2|]. split; [drv 3|]. split; [drv 4|]. split; [drv 5|].
    split; [| exact LT].
    unfold pf_ok. apply Forall_forall. intros [pc0 p] Hin. cbn [fst snd map].
    apply inst_demand. unfold all_demands. apply in_or_app. right. apply in_or_app. left.
    unfold pf_shift. apply in_map_iff. exists (pc0, p). split; [reflexivity| exact Hin].
  Qed.
End ForInstance.
