(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition gm (L : mled) : Z :=
  fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) (ld_groups L))
  + fold_right Z.add 0 (map (fun m : Z * Z * Z => mmap_len (snd (fst m))) (ld_metas L)).

(* [comment removed for export] *)
Definition BB (L : mled) : Z :=
  match ld_brk L with
  | BPGuard _ => 2 * PGSZ
  | _ => match ld_brkreg L with Some (_, l) => l | None => 0 end
  end.

(* [comment removed for export] *)
Definition kcnt (L : mled) : Z :=
  Z.of_nat (length (ld_groups L)) + Z.of_nat (length (ld_metas L)) + BB L / PGSZ.

(* [comment removed for export] *)
Definition KCAP : Z := 12288.
Definition BCAP : Z := 2 ^ 32.

Lemma gm_set_brkph ph L : gm (set_brkph ph L) = gm L. Proof. reflexivity. Qed.
Lemma gm_set_brkreg v L : gm (set_brkreg v L) = gm L. Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gm_add_group a len L : gm (set_groups ((a, len) :: ld_groups L) L) = gm L + mmap_len len.
Proof. unfold gm. cbn. lia. Qed.
Lemma gm_add_meta a len L : gm (set_metas ((a, len, 0) :: ld_metas L) L) = gm L + mmap_len len.
Proof. unfold gm. cbn. lia. Qed.
Lemma BB_set_groups v L : BB (set_groups v L) = BB L. Proof. reflexivity. Qed.
Lemma BB_set_metas v L : BB (set_metas v L) = BB L. Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma gm_bump a L : gm (set_metas (map (bump_meta a) (ld_metas L)) L) = gm L.
Proof.
  unfold gm. cbn [ld_groups ld_metas set_metas]. f_equal.
  induction (ld_metas L) as [|[[b l] k] ms IH]; cbn; [reflexivity|]. rewrite IH. unfold bump_meta. destruct (b + (1 + k) * PGSZ =? a); reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.

Definition BOUND (L : mled) (e : ev) (B : Z) : Prop :=
  forall z, answer_ok L e z = true -> gm (event_post L e z) + BB (event_post L e z) <= B.

Definition XB (L : mled) (e : ev) (B : Z) : Prop :=
  match e with
  | EMmap _ len _ flags =>
      if Z.land flags MAP_FIXED =? 0 then mmap_len len <= B + 3 * PGSZ /\ kcnt L + 3 <= KCAP else True
  | _ => True
  end.

Definition BOUNDX (L : mled) (e : ev) (B : Z) : Prop := BOUND L e B /\ XB L e B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma BOUND_mmap_now L len prot B : BOUND L (EMmap 0 len prot MAPF) B -> gm L + BB L <= B.
Proof.
  intros HB. specialize (HB (TWO64 - ENOMEM)).
  unfold answer_ok, event_post in HB. change (Z.land MAPF MAP_FIXED =? 0) with true in HB. cbn iota in HB.
  unfold mmap_answer_ok in HB. replace (is_errno_form (TWO64 - ENOMEM)) with true in HB by reflexivity.
  replace (is_err (TWO64 - ENOMEM)) with true in HB by reflexivity. cbn [orb] in HB. exact (HB eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint qtree {R} (B : Z) (L : mled) (t : stree ev Z R) (Post : mled -> R -> Prop) : Prop :=
  match t with
  | SRet r => Post L r
  | SVis e k => event_pre L e /\ BOUNDX L e B /\ forall z, answer_ok L e z = true -> qtree B (event_post L e z) (k z) Post
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

End CEIL.
