(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mremap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode SysStep.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc MProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition wpair_eqb (p q : word * word) : bool := bv_eqb (fst p) (fst q) && bv_eqb (snd p) (snd q).
Fixpoint list_eqb {A} (f : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: l1', y :: l2' => f x y && list_eqb f l1' l2'
  | _, _ => false
  end.
Definition bytes_eqb (a b : list byte) : bool := list_eqb (fun x y => bv_eqb x y) a b.
Definition write_eqb (p q : word * list byte) : bool := bv_eqb (fst p) (fst q) && bytes_eqb (snd p) (snd q).
Definition copy_eqb (c d : MemCopy) : bool :=
  bv_eqb (copy_src c) (copy_src d) && bv_eqb (copy_dst c) (copy_dst d) && bv_eqb (copy_len c) (copy_len d).
Definition cin_eqb (p q : word * nat) : bool := bv_eqb (fst p) (fst q) && Nat.eqb (snd p) (snd q).
Definition eff_eqb (a b : SyscallEffect) : bool :=
  bv_eqb (eff_ret a) (eff_ret b)
  && list_eqb write_eqb (eff_writes a) (eff_writes b)
  && list_eqb wpair_eqb (eff_zeros a) (eff_zeros b)
  && list_eqb wpair_eqb (eff_unmaps a) (eff_unmaps b)
  && list_eqb copy_eqb (eff_copies a) (eff_copies b)
  && list_eqb cin_eqb (eff_copyins a) (eff_copyins b).

Lemma bv_eqb_true_iff {n} (x y : bv n) : bv_eqb x y = true <-> x = y.
Proof.
  split; [| intros ->; apply bv_eqb_refl].
  unfold bv_eqb. intros H. apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Lemma list_eqb_eq {A} (f : A -> A -> bool) : (forall x y, f x y = true -> x = y) -> forall l1 l2, list_eqb f l1 l2 = true -> l1 = l2.
Proof.
  intros Hf. induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (Hf _ _ H1), (IH _ H2). reflexivity.
Qed.

Lemma wpair_eqb_eq p q : wpair_eqb p q = true -> p = q.
Proof. destruct p, q; unfold wpair_eqb; cbn; intros H; apply andb_prop in H as [H1 H2]; apply bv_eqb_true_iff in H1; apply bv_eqb_true_iff in H2; congruence. Qed.
Lemma write_eqb_eq p q : write_eqb p q = true -> p = q.
Proof.
  destruct p, q; unfold write_eqb; cbn; intros H; apply andb_prop in H as [H1 H2]; apply bv_eqb_true_iff in H1.
  apply (list_eqb_eq _ (fun x y H => proj1 (bv_eqb_true_iff x y) H)) in H2. congruence.
Qed.
Lemma copy_eqb_eq c d : copy_eqb c d = true -> c = d.
Proof.
  destruct c, d; unfold copy_eqb; cbn; intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply bv_eqb_true_iff in H1; apply bv_eqb_true_iff in H2; apply bv_eqb_true_iff in H3. congruence.
Qed.
Lemma cin_eqb_eq p q : cin_eqb p q = true -> p = q.
Proof. destruct p, q; unfold cin_eqb; cbn; intros H; apply andb_prop in H as [H1 H2]; apply bv_eqb_true_iff in H1; apply Nat.eqb_eq in H2; congruence. Qed.

Lemma eff_eqb_eq a b : eff_eqb a b = true -> a = b.
Proof.
  destruct a, b; unfold eff_eqb; cbn; intros H.
  repeat (apply andb_prop in H as [H ?]).
  apply bv_eqb_true_iff in H.
  apply (list_eqb_eq _ write_eqb_eq) in H4. apply (list_eqb_eq _ wpair_eqb_eq) in H3. apply (list_eqb_eq _ wpair_eqb_eq) in H2.
  apply (list_eqb_eq _ copy_eqb_eq) in H1. apply (list_eqb_eq _ cin_eqb_eq) in H0. congruence.
Qed.

Lemma list_eqb_refl {A} (f : A -> A -> bool) : (forall x, f x x = true) -> forall l, list_eqb f l l = true.
Proof. intros Hf. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite Hf, IH. reflexivity. Qed.
Lemma bv_eqb_refl' {n} (x : bv n) : bv_eqb x x = true. Proof. apply bv_eqb_refl. Qed.
Lemma eff_eqb_refl a : eff_eqb a a = true.
Proof.
  destruct a; unfold eff_eqb; cbn. rewrite bv_eqb_refl'.
  rewrite (list_eqb_refl write_eqb) by (intros [u v]; unfold write_eqb; cbn; rewrite bv_eqb_refl', (list_eqb_refl _ bv_eqb_refl'); reflexivity).
  rewrite !(list_eqb_refl wpair_eqb) by (intros [u v]; unfold wpair_eqb; cbn; rewrite !bv_eqb_refl'; reflexivity).
  rewrite (list_eqb_refl copy_eqb) by (intros [u v l]; unfold copy_eqb; cbn; rewrite !bv_eqb_refl'; reflexivity).
  rewrite (list_eqb_refl cin_eqb) by (intros [u v]; unfold cin_eqb; cbn; rewrite bv_eqb_refl', Nat.eqb_refl; reflexivity).
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition mw (z : Z) : word := Z_to_bv 64 z.
Definition mrlen (len : Z) : Z := page_round_up_Z (bv_unsigned (mw len)).
Definition mwlen (len : Z) : word := Z_to_bv 64 (mrlen len).

(* [comment removed for export] *)
Definition mremap_expected (old old_len new_len : Z) (r : word) : SyscallEffect :=
  let oZ := mrlen old_len in let nZ := mrlen new_len in
  if oZ =? nZ then mkEffect (mw old) [] []
  else if bv_eqb r (mw old) then mremap_inplace_effect (mw old) (mwlen old_len) (mwlen new_len) oZ nZ
  else mremap_move_effect (mw old) (mwlen old_len) r oZ nZ.

(* [comment removed for export] *)
Definition mspan (old_len new_len : Z) : Z := Z.max (mrlen old_len) (mrlen new_len).
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition mremap_dst_ok (avoid : list (Z * Z)) (old_len new_len : Z) (r : word) : bool :=
  let nZ := mspan old_len new_len in let d := bv_unsigned r in
  (d mod 4096 =? 0) && (0 <? d) && (d + nZ <=? alloc_ceiling) && avoids d nZ avoid.

Lemma mremap_dst_ok_sound avoid old_len new_len r :
  mremap_dst_ok avoid old_len new_len r = true ->
  bv_unsigned r mod 4096 = 0 /\ 0 < bv_unsigned r /\ bv_unsigned r + mspan old_len new_len <= alloc_ceiling
  /\ forall iv, In iv avoid -> bv_unsigned r + mspan old_len new_len <= fst iv \/ snd iv <= bv_unsigned r.
Proof.
  unfold mremap_dst_ok, avoids. intros H.
  apply andb_prop in H as [H A]. apply andb_prop in H as [H C]. apply andb_prop in H as [M P].
  apply Z.eqb_eq in M. apply Z.ltb_lt in P. apply Z.leb_le in C.
  split; [exact M|]. split; [exact P|]. split; [exact C|].
  intros iv Hiv. rewrite forallb_forall in A. specialize (A iv Hiv). apply orb_prop in A as [A|A]; [left| right]; apply Z.leb_le; exact A.
Qed.

Lemma mremap_dst_ok_intro avoid old_len new_len r :
  bv_unsigned r mod 4096 = 0 -> 0 < bv_unsigned r -> bv_unsigned r + mspan old_len new_len <= alloc_ceiling ->
  (forall iv, In iv avoid -> bv_unsigned r + mspan old_len new_len <= fst iv \/ snd iv <= bv_unsigned r) ->
  mremap_dst_ok avoid old_len new_len r = true.
Proof.
  intros M P C A. unfold mremap_dst_ok, avoids.
  rewrite (proj2 (Z.eqb_eq _ _) M), (proj2 (Z.ltb_lt _ _) P), (proj2 (Z.leb_le _ _) C). cbn [andb].
  apply forallb_forall. intros iv Hiv. destruct (A iv Hiv) as [X|X]; apply Z.leb_le in X; rewrite X; [reflexivity| apply orb_true_r].
Qed.

Definition dec_mremap (avoid : list (Z * Z)) (old old_len new_len : Z) (rsp : resp) : option Z :=
  match errno_of (eff_ret rsp) with
  | Some e => if eff_eqb rsp (mkEffect (eff_ret rsp) [] []) then Some (neg_errno e) else None
  | None => if eff_eqb rsp (mremap_expected old old_len new_len (eff_ret rsp)) && mremap_dst_ok avoid old_len new_len (eff_ret rsp)
            then Some (bv_unsigned (eff_ret rsp)) else None
  end.

Lemma dec_mremap_err avoid old old_len new_len r e :
  errno_of r = Some e -> dec_mremap avoid old old_len new_len (mkEffect r [] []) = Some (neg_errno e).
Proof. intros H. unfold dec_mremap. cbn [eff_ret]. rewrite H, eff_eqb_refl. reflexivity. Qed.

Lemma dec_mremap_expected avoid old old_len new_len rsp z :
  dec_mremap avoid old old_len new_len rsp = Some z ->
  (exists e, errno_of (eff_ret rsp) = Some e /\ rsp = mkEffect (eff_ret rsp) [] [] /\ z = neg_errno e)
  \/ (errno_of (eff_ret rsp) = None /\ rsp = mremap_expected old old_len new_len (eff_ret rsp) /\ z = bv_unsigned (eff_ret rsp)
      /\ mremap_dst_ok avoid old_len new_len (eff_ret rsp) = true).
Proof.
  unfold dec_mremap. destruct (errno_of (eff_ret rsp)) as [e|] eqn:E.
  - destruct (eff_eqb rsp _) eqn:Q; [| discriminate]. intros H. inversion H; subst. left. exists e.
    split; [reflexivity|]. split; [exact (eff_eqb_eq _ _ Q)| reflexivity].
  - destruct (eff_eqb rsp _) eqn:Q; [| discriminate]. destruct (mremap_dst_ok avoid old_len new_len (eff_ret rsp)) eqn:D; [| discriminate].
    intros H. inversion H; subst. right.
    split; [reflexivity|]. split; [exact (eff_eqb_eq _ _ Q)|]. split; [reflexivity| reflexivity].
Qed.

Lemma dec_mremap_of_expected avoid old old_len new_len r :
  errno_of r = None -> eff_ret (mremap_expected old old_len new_len r) = r ->
  mremap_dst_ok avoid old_len new_len r = true ->
  dec_mremap avoid old old_len new_len (mremap_expected old old_len new_len r) = Some (bv_unsigned r).
Proof. intros H E D. unfold dec_mremap. rewrite E, H, eff_eqb_refl, D. reflexivity. Qed.

End CEIL.
