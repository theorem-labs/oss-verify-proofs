(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import PropExec AxSyioe AxSyclu Asanz3l Booteo9.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module BFXE.
Import AX2. Import APC.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zpos (z : Z) : positive := match Z.land z 1048575 with Zpos p => xO p | _ => xH end.
Fixpoint ehash (e : expr) : Z :=
  match e with
  | ELit z => z
  | EVar n => Z.of_nat n
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => ehash a + ehash b
  | EExt _ _ _ a => ehash a
  | EBlob _ _ i _ => i
  end.
Definition ahash (a : saddr) : Z := a_off a + ehash (a_base a).
Definition key (K : kentry) : positive :=
  match K with
  | KWord a _ _ => xO (xO (xO (xO (zpos (ahash a)))))
  | KZero a _ => xI (xO (xO (xO (zpos (ahash a)))))
  | KBlob a _ _ => xO (xI (xO (xO (zpos (ahash a)))))
  | KImg lo hi => xI (xI (xO (xO (zpos lo))))
  | KAlign e m => xO (xO (xI (xO (zpos (m + ehash e)))))
  | KRange e lo hi => xI (xO (xI (xO (zpos (lo + hi + ehash e)))))
  | KWr a _ => xO (xI (xI (xO (zpos (ahash a)))))
  | KDisj a1 n1 a2 n2 => xI (xI (xI (xO (zpos (ahash a1 + ahash a2 + ehash n1 + ehash n2)))))
  | KFill a _ _ => xO (xO (xO (xI (zpos (ahash a)))))
  | KUnk a _ => xI (xO (xO (xI (zpos (ahash a)))))
  end.

Lemma ehash_eqb : forall x y, expr_eqb x y = true -> ehash x = ehash y.
Proof.
  induction x as [a|a|o a IHa b IHb|o a IHa b IHb|o a IHa b IHb|o a IHa b IHb|sx l n a IHa|sx k i n];
    intros [a'|a'|o' a' b'|o' a' b'|o' a' b'|o' a' b'|sx' l' n' a'|sx' k' i' n'] H; cbn [expr_eqb] in H; try discriminate H; cbn [ehash];
    repeat match goal with
           | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
           end;
    repeat match goal with
           | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
           | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
           | IH : forall y, expr_eqb ?a y = true -> _, H : expr_eqb ?a _ = true |- _ => apply IH in H
           end; congruence.
Qed.
Lemma saddr_eqb_hash : forall a b, saddr_eqb a b = true -> ahash a = ahash b.
Proof.
  intros a b H. unfold saddr_eqb in H. apply andb_true_iff in H. destruct H as [H1 H2].
  apply Z.eqb_eq in H2. apply ehash_eqb in H1. unfold ahash. congruence.
Qed.

Lemma key_eqb : forall X K, kentry_eqb X K = true -> key X = key K.
Proof.
  intros X K H.
  destruct X as [a w v|a n|a n kk|lo hi|e m|e lo hi|a n|a1 n1 a2 n2|a n c|a n];
  destruct K as [a' w' v'|a' n'|a' n' kk'|lo' hi'|e' m'|e' lo' hi'|a' n'|a1' n1' a2' n2'|a' n' c'|a' n'];
  cbn [kentry_eqb] in H; try discriminate H; cbn [key];
  repeat match goal with
         | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
         end;
  repeat match goal with
         | H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_hash in H
         | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
         | H : expr_eqb _ _ = true |- _ => apply ehash_eqb in H
         end; congruence.
Qed.

(* [comment removed for export] *)
Definition build (l : list kentry) : ptree (list kentry) :=
  fold_right (fun K T => BLKF.pt_cons (key K) K T) PTLeaf l.
Definition bucket (T : ptree (list kentry)) (k : positive) : list kentry :=
  match pt_get T k with Some b => b | None => [] end.
(* [comment removed for export] *)
Definition mem (T : ptree (list kentry)) (K : kentry) : bool := existsb (fun X => kentry_eqb X K) (bucket T (key K)).
(* [comment removed for export] *)
Definition mem' (T : ptree (list kentry)) (K : kentry) : bool := existsb (kentry_eqb K) (bucket T (key K)).

Lemma bucket_cons : forall X l k,
  bucket (build (X :: l)) k = if Pos.eqb (key X) k then X :: bucket (build l) k else bucket (build l) k.
Proof.
  intros X l k. unfold bucket. cbn [build fold_right]. fold (build l). rewrite BLKF.pt_cons_eq.
  destruct (Pos.eqb_spec (key X) k) as [->|NE].
  - rewrite pt_gss. reflexivity.
  - rewrite pt_gso by congruence. reflexivity.
Qed.

Lemma mem_eq : forall l K, mem (build l) K = existsb (fun X => kentry_eqb X K) l.
Proof.
  intros l K. unfold mem. induction l as [|X l IH].
  - unfold bucket. cbn [build fold_right]. rewrite pt_get_leaf. reflexivity.
  - rewrite bucket_cons. cbn [existsb]. destruct (Pos.eqb_spec (key X) (key K)) as [E|NE].
    + cbn [existsb]. rewrite IH. reflexivity.
    + rewrite IH. destruct (kentry_eqb X K) eqn:EQ; [|reflexivity]. exfalso. apply NE. apply key_eqb. exact EQ.
Qed.
Lemma mem'_eq : forall l K, mem' (build l) K = existsb (kentry_eqb K) l.
Proof.
  intros l K. unfold mem'. induction l as [|X l IH].
  - unfold bucket. cbn [build fold_right]. rewrite pt_get_leaf. reflexivity.
  - rewrite bucket_cons. cbn [existsb]. destruct (Pos.eqb_spec (key X) (key K)) as [E|NE].
    + cbn [existsb]. rewrite IH. reflexivity.
    + rewrite IH. destruct (kentry_eqb K X) eqn:EQ; [|reflexivity]. exfalso. apply NE. symmetry. apply key_eqb. exact EQ.
Qed.

Lemma forallb_ext' : forall (T : Type) (f g : T -> bool) l, (forall x, f x = g x) -> forallb f l = forallb g l.
Proof. intros T f g l H. induction l as [|a l IH]; [reflexivity|]. cbn [forallb]. rewrite H, IH. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition entails_f (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && list_eqb expr_eqb (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && (let T := build (kn cs) in forallb (mem' T) (kn ch))
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.

Lemma entails_f_eq : forall cs ch, entails_f cs ch = entails cs ch.
Proof.
  intros cs ch. unfold entails_f, entails. cbv zeta.
  rewrite (forallb_ext' _ (mem' (build (kn cs))) (fun K => existsb (kentry_eqb K) (kn cs)) (kn ch)) by (intros K; apply mem'_eq).
  reflexivity.
Qed.
Lemma entails_f_fe : entails_f = entails.
Proof. apply functional_extensionality; intros cs. apply functional_extensionality; intros ch. apply entails_f_eq. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section H.
Variable A : atable.
Definition kn_incl1_h_f (T : ptree (list kentry)) (k : list kentry) (K : kentry) : bool :=
  if mem T K then true
  else if (if kflat_h k K then existsb (fun X => kentry_eqb_h X K) k else false) then true
  else if kimg_sub_covered k K then true
  else kunk_covered A k K.
Definition kn_incl_h_f (k : list kentry) (tk : list kentry) : bool :=
  let T := build k in forallb (kn_incl1_h_f T k) tk.
Lemma kn_incl_h_f_eq : forall k tk, kn_incl_h_f k tk = kn_incl_h A k tk.
Proof.
  intros k tk. unfold kn_incl_h_f, kn_incl_h. cbv zeta. apply forallb_ext'. intros K.
  unfold kn_incl1_h_f, kn_incl1_h. rewrite mem_eq. reflexivity.
Qed.
End H.
Lemma kn_incl_h_f_fe : kn_incl_h_f = kn_incl_h.
Proof. apply functional_extensionality; intros A. apply functional_extensionality; intros k. apply functional_extensionality; intros tk. apply kn_incl_h_f_eq. Qed.

Definition entails_h_g :=
  ltac:(let t := eval cbv delta [APC.entails_h] in @APC.entails_h in
        let t1 := eval pattern (@APC.kn_incl_h) in t in
        lazymatch t1 with ?G _ => exact G end).
Definition entails_h_f := entails_h_g kn_incl_h_f.
Lemma entails_h_f_fe : entails_h_f = @APC.entails_h.
Proof. unfold entails_h_f. rewrite kn_incl_h_f_fe. reflexivity. Qed.
End BFXE.
