(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import String Ascii ZArith Bool List Lia.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim SjModel AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require SjAlloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition od_action (d : list Z) : Z := match d with [] => 0 | b :: _ => b mod 13 end.

Definition od_rest (d : list Z) : list Z := tl d.
Definition od_parts (d : list Z) : list (list Z) := atp_parts (od_rest d).

Definition od_P (d : list Z) : nat := Nat.max (length (od_parts d)) 1.

Definition od_s0 (d : list Z) : list Z := nth 0 (od_parts d) [].

Definition od_copied (d : list Z) : bool := zlength (od_s0 d) <=? SJ_PADMAX.
Definition od_doc (d : list Z) : list Z := if od_copied d then SjAlloc.strip_bom (od_s0 d) else [].

Definition OD_SBUF (L : Z) : Z := roundup64 (5 * (L / 3) + 64).
Definition OD_IDX (L : Z) : Z := 4 * (roundup64 L + 9).

Section Target.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : target_ops M ptr.
Variable d : list Z.

Local Notation "x <- m ;; k" := (bind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bind ops m (fun _ => k)) (at level 61, right associativity).

Definition fuzz_one : M Z :=
  let len0 := zlength (od_s0 d) in
  let L := zlength (od_doc d) in
  v <- vpushes ops (od_P d) vec0 ;;
  cpo <- (if len0 <=? SJ_PADMAX then p <- newnt ops (SJ_COPY len0) ;; ret ops (Some p) else ret ops None) ;;
  sb <- newnt ops (OD_SBUF L) ;;
  im <- newnt ops SJ_IMPL ;;
  ix <- newnt ops (OD_IDX L) ;;
  oc <- newnt ops SJ_OC ;;
  ia <- newnt ops SJ_IA ;;
  (match cpo with Some p => del ops p | None => ret ops tt end) ;;;
  del ops sb ;;; del ops ia ;;; del ops oc ;;; del ops ix ;;; del ops im ;;;
  vfree ops v ;;;
  ret ops 0.

Fixpoint run_calls (n : nat) (rc : Z) : M Z :=
  match n with
  | O => ret ops rc
  | S n' =>
      rc' <- fuzz_one ;;
      out_stdout ops (Zdecimal rc' ++ [10]) ;;;
      run_calls n' rc'
  end.

Definition target_run (cfg : list Z) : M Z :=
  let c := match cfg with [] => 0 | b :: _ => b end in
  let calls := Z.to_nat (Z.land c 3 + 1) in
  let plen := zlength d in

  a <- (if plen =? 0 then ret ops (Some None)
        else r <- lib_malloc ops plen ;;
             ret ops (match r with None => None | Some p => Some (Some p) end)) ;;
  match a with
  | None => ret ops 2
  | Some owned =>
      rc <- run_calls calls 0 ;;
      lib_free ops owned ;;;
      ret ops (if rc =? 0 then 0 else 1)
  end.

End Target.

Lemma od_rest_len : forall d, zlength (od_rest d) <= zlength d.
Proof. intros [|c d]; unfold od_rest, zlength; cbn [tl length]; lia. Qed.

Lemma od_P_ge1 : forall d, (1 <= od_P d)%nat.
Proof. intros d. unfold od_P. lia. Qed.

Lemma od_s0_len : forall d, zlength (od_s0 d) <= zlength d.
Proof.
  intros d. unfold od_s0, od_parts. pose proof (od_rest_len d) as HR.
  destruct (nth_In_or_default (atp_parts (od_rest d)) 0 []) as [->|H]; [unfold zlength in *; cbn [length]; lia|].
  apply atp_parts_len in H. unfold zlength in *. lia.
Qed.

Lemma zlength_strip_bom : forall l, zlength (SjAlloc.strip_bom l) <= zlength l.
Proof. intros l. exact (SjAlloc.blen_strip_bom l). Qed.

Lemma od_doc_len : forall d, 0 <= zlength (od_doc d) /\ zlength (od_doc d) <= zlength (od_s0 d)
                             /\ zlength (od_doc d) <= zlength d /\ zlength (od_doc d) <= SJ_PADMAX.
Proof.
  intros d. unfold od_doc, od_copied. pose proof (od_s0_len d) as H0.
  destruct (Z.leb_spec (zlength (od_s0 d)) SJ_PADMAX) as [Hle|Hgt].
  - pose proof (zlength_strip_bom (od_s0 d)). unfold zlength in *. lia.
  - unfold zlength in *. cbn [length]. unfold SJ_PADMAX in *. lia.
Qed.

Lemma od_P_bound : forall d, (4 * (od_P d - 1) <= length d)%nat.
Proof.
  intros d. unfold od_P, od_parts, od_rest, atp_parts. destruct d as [|c0 [|c d']]; cbn [tl]; [cbn; lia| cbn; lia|].
  pose proof (split_go_count (S (length (c :: d'))) (c :: d')). cbn [length] in *. lia.
Qed.

Lemma od_sizes_small : forall L, 0 <= L <= 2^32 -> 0 <= OD_SBUF L < 2^62 /\ 0 <= OD_IDX L < 2^62.
Proof.
  intros L H. unfold OD_SBUF, OD_IDX.
  pose proof (roundup64_ge (5 * (L / 3) + 64)). pose proof (roundup64_lt (5 * (L / 3) + 64)).
  pose proof (roundup64_ge L). pose proof (roundup64_lt L).
  assert (0 <= L / 3 <= 2^32) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  change (2^32) with 4294967296 in *. change (2^62) with 4611686018427387904. lia.
Qed.

Lemma OD_SBUF_room : forall L, 0 <= L -> L + 62 <= OD_SBUF L.
Proof.
  intros L H. unfold OD_SBUF. pose proof (roundup64_ge (5 * (L / 3) + 64)).
  pose proof (Z.div_mod L 3 ltac:(lia)). pose proof (Z.mod_pos_bound L 3 ltac:(lia)).
  assert (0 <= L / 3) by (apply Z.div_pos; lia). lia.
Qed.

Lemma OD_IDX_room : forall L, 0 <= L -> 4 * (L + 9) <= OD_IDX L /\ OD_IDX L mod 4 = 0.
Proof.
  intros L H. unfold OD_IDX. pose proof (roundup64_ge L). split; [lia|].
  rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.
