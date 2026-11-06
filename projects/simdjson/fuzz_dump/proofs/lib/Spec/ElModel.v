(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import String Ascii ZArith Bool List Lia.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim SjModel AtpModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition EL_HDR : Z := 10.

Definition el_fd_ok (d : list Z) : bool := EL_HDR <=? zlength d.

Definition el_action (d : list Z) : Z := match d with a :: _ => a mod 32 | [] => 0 end.
Definition el_sel (d : list Z) : Z := match d with _ :: s :: _ => s mod 8 | _ => 0 end.

Fixpoint le_bytes (l : list Z) : Z := match l with [] => 0 | b :: l' => b + 256 * le_bytes l' end.
Definition el_index (d : list Z) : Z := if el_fd_ok d then le_bytes (firstn 8 (skipn 2 d)) else 0.

Definition el_rem (d : list Z) : list Z := if el_fd_ok d then skipn 10 d else [].

Definition el_parts (d : list Z) : list (list Z) := atp_parts (el_rem d).
Definition el_P (d : list Z) : nat := Nat.max (length (el_parts d)) 2.

Definition el_str (d : list Z) : list Z := nth 0 (el_parts d) [].
Definition el_s1 (d : list Z) : list Z := nth 1 (el_parts d) [].

Definition el_doc (d : list Z) : list Z := if zlength (el_s1 d) <=? SJ_PADMAX then el_s1 d else [].

Definition EL_EXC : Z := 144.

Definition el_throwing (a : Z) : bool := (a =? 22) || (a =? 23) || (a =? 24).

Definition el_throws (a sel c v : Z) : bool :=
  if a =? 22 then
    (if sel =? 0 then negb ((c =? 116) || (c =? 102))
     else if sel =? 1 then negb ((c =? 100) || (c =? 117) || (c =? 108))
     else if sel =? 2 then ((c =? 108) && (2^63 <=? v)) || negb ((c =? 117) || (c =? 108))
     else if sel =? 3 then ((c =? 117) && (2^63 <=? v)) || negb ((c =? 108) || (c =? 117))
     else if (sel =? 4) || (sel =? 5) then negb (c =? 34)
     else if sel =? 6 then negb (c =? 91)
     else negb (c =? 123))
  else if (a =? 23) || (a =? 24) then negb (c =? 91)
  else false.

Section Target.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : target_ops M ptr.
Variable d : list Z.

Local Notation "x <- m ;; k" := (bind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bind ops m (fun _ => k)) (at level 61, right associativity).

Definition el_free_nulls : M unit :=
  lib_free ops None ;;; lib_free ops None ;;; lib_free ops None ;;; lib_free ops None.

Definition el_act : M unit :=
  let a := el_action d in
  if el_throwing a then
    thr <- cho ops ;;
    if thr =? 0 then ret ops tt
    else e <- newnt ops EL_EXC ;; del ops e
  else if a =? 26 then atp_walk ops (ptr_segs (el_str d))
  else if a =? 31 then el_free_nulls
  else ret ops tt.

Definition el_parse_phase (rc : option Z) : M unit :=
  let len1 := zlength (el_s1 d) in
  let L := zlength (el_doc d) in
  cpo <- (if len1 <=? SJ_PADMAX then p <- newnt ops (SJ_COPY len1) ;; ret ops (Some p) else ret ops None) ;;
  sb <- newnt ops (SJ_SBUF L) ;;
  tp <- newnt ops (SJ_TAPE L) ;;
  im <- newnt ops SJ_IMPL ;;
  ix <- newnt ops (SJ_IDX L) ;;
  oc <- newnt ops SJ_OC ;;
  ia <- newnt ops SJ_IA ;;
  (match rc with Some c => r <- newnt ops c ;; del ops r | None => ret ops tt end) ;;;
  (match cpo with Some p => del ops p | None => ret ops tt end) ;;;
  ok <- cho ops ;;
  (if ok =? 0 then ret ops tt else el_act) ;;;
  del ops sb ;;; del ops tp ;;; del ops ia ;;; del ops oc ;;; del ops ix ;;; del ops im.

Definition fuzz_one_with (rc : option Z) : M Z :=
  v <- vpushes ops (el_P d) vec0 ;;
  (if el_fd_ok d then el_parse_phase rc else ret ops tt) ;;;
  vfree ops v ;;;
  ret ops 0.

Definition fuzz_one : M Z := fuzz_one_with (sj_root_copy (el_doc d)).

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

Lemma el_rem_len : forall d, (length (el_rem d) <= length d)%nat.
Proof. intros d. unfold el_rem. destruct (el_fd_ok d); [rewrite length_skipn| cbn]; lia. Qed.

Lemma el_rem_fd : forall d, el_fd_ok d = true -> el_rem d = skipn 10 d /\ zlength (el_rem d) = zlength d - 10.
Proof.
  intros d H. unfold el_rem. rewrite H. split; [reflexivity|].
  unfold el_fd_ok, EL_HDR in H. apply Z.leb_le in H. unfold zlength in *. rewrite length_skipn. lia.
Qed.

Lemma el_rem_nofd : forall d, el_fd_ok d = false -> el_rem d = [] /\ el_parts d = [] /\ el_P d = 2%nat.
Proof. intros d H. unfold el_P, el_parts, el_rem. rewrite H. cbn. auto. Qed.

Lemma el_P_ge2 : forall d, (2 <= el_P d)%nat.
Proof. intros d. unfold el_P. lia. Qed.

Lemma el_P_bound : forall d, (4 * (el_P d - 1) <= length d + 4)%nat.
Proof.
  intros d. unfold el_P, el_parts. pose proof (el_rem_len d).
  pose proof (atp_P_bound (el_rem d)) as B. unfold atp_P in B. lia.
Qed.

Lemma el_parts_len : forall d p, In p (el_parts d) -> (length p <= length d)%nat.
Proof. intros d p H. unfold el_parts in H. apply atp_parts_len in H. pose proof (el_rem_len d). lia. Qed.

Lemma el_str_len : forall d, zlength (el_str d) <= zlength d.
Proof.
  intros d. unfold el_str, zlength. destruct (nth_In_or_default (el_parts d) 0 []) as [->|H]; [cbn; lia|].
  apply el_parts_len in H. lia.
Qed.

Lemma el_s1_len : forall d, zlength (el_s1 d) <= zlength d.
Proof.
  intros d. unfold el_s1, zlength. destruct (nth_In_or_default (el_parts d) 1 []) as [->|H]; [cbn; lia|].
  apply el_parts_len in H. lia.
Qed.

Lemma el_doc_len : forall d, zlength (el_doc d) <= zlength d /\ zlength (el_doc d) <= SJ_PADMAX.
Proof.
  intros d. unfold el_doc. pose proof (el_s1_len d). destruct (Z.leb_spec (zlength (el_s1 d)) SJ_PADMAX); [lia|].
  unfold zlength in *. cbn. unfold SJ_PADMAX. lia.
Qed.

Lemma el_str_s0 : forall d, el_str d = atp_s0 (el_rem d).
Proof. reflexivity. Qed.
Lemma el_s1_ptr : forall d, el_s1 d = atp_ptr (el_rem d).
Proof. reflexivity. Qed.

Lemma le_bytes_range : forall l, Forall (fun b => 0 <= b < 256) l -> 0 <= le_bytes l < 256 ^ (Z.of_nat (length l)).
Proof.
  induction l as [|b l IH]; intros H; cbn [le_bytes length]; [lia|].
  inversion H as [|x y Hb Hl]; subst. specialize (IH Hl). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma el_index_range : forall d, Forall (fun b => 0 <= b < 256) d -> 0 <= el_index d < 2^64.
Proof.
  intros d H. unfold el_index. destruct (el_fd_ok d) eqn:E; [|lia].
  assert (HL : length (firstn 8 (skipn 2 d)) = 8%nat).
  { rewrite length_firstn, length_skipn. unfold el_fd_ok, EL_HDR, zlength in E. apply Z.leb_le in E. lia. }
  pose proof (le_bytes_range (firstn 8 (skipn 2 d))) as R. rewrite HL in R.
  change (256 ^ Z.of_nat 8) with (2^64) in R. apply R.
  apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ d) H x).
  rewrite <- (firstn_skipn 2 d), <- (firstn_skipn 8 (skipn 2 d)). rewrite !in_app_iff. tauto.
Qed.

Lemma el_action_range : forall d, Forall (fun b => 0 <= b < 256) d -> 0 <= el_action d < 32.
Proof. intros [|a d] H; cbn; [lia|]. inversion H; subst. apply Z.mod_pos_bound. lia. Qed.

Lemma el_sel_range : forall d, Forall (fun b => 0 <= b < 256) d -> 0 <= el_sel d < 8.
Proof. intros [|a [|s d]] H; cbn; [lia|lia|]. apply Z.mod_pos_bound. lia. Qed.

Example el_hdr_ex : el_action [54; 9; 1; 0; 0; 0; 0; 0; 0; 0; 107; 10] = 22 /\ el_sel [54; 9] = 1
  /\ el_index [54; 9; 1; 2; 0; 0; 0; 0; 0; 0] = 513 /\ el_fd_ok [54; 9; 1; 2; 0; 0; 0; 0; 0] = false.
Proof. vm_compute. repeat split; reflexivity. Qed.
Example el_parts_ex : el_parts ([26; 0; 0; 0; 0; 0; 0; 0; 0; 0] ++ [107] ++ SEP ++ [91; 49; 93]) = [[107]; [91; 49; 93]]
  /\ el_P ([26; 0; 0; 0; 0; 0; 0; 0; 0; 0]) = 2%nat /\ el_doc ([26; 0; 0; 0; 0; 0; 0; 0; 0; 0] ++ [107] ++ SEP ++ [91; 49; 93]) = [91; 49; 93].
Proof. vm_compute. repeat split; reflexivity. Qed.
Example el_throws_ex : el_throws 22 0 123 0 = true /\ el_throws 22 7 123 0 = false /\ el_throws 22 2 108 (2^63) = true
  /\ el_throws 22 2 108 5 = false /\ el_throws 23 0 91 0 = false /\ el_throws 24 3 108 0 = true /\ el_throws 8 0 123 0 = false.
Proof. vm_compute. repeat split; reflexivity. Qed.
