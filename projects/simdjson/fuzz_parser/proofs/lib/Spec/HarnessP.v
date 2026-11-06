(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad SjStage1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Definition ROUNDUP64 (x : Z) : Z := (x + 63) / 64 * 64.            (* [comment removed for export] *)
Definition CAP (len : Z) : Z := Z.max len 32.                       (* [comment removed for export] *)
Definition SB_BYTES (len : Z) : Z := ROUNDUP64 (5 * (CAP len / 3) + 64).     (* [comment removed for export] *)
Definition TAPE_BYTES (len : Z) : Z := 8 * ROUNDUP64 (CAP len + 3).           (* [comment removed for export] *)
Definition IMPL_BYTES : Z := 96.                                              (* [comment removed for export] *)
Definition SIDX_BYTES (len : Z) : Z := 4 * (ROUNDUP64 (CAP len) + 9).         (* [comment removed for export] *)
Definition MAX_DEPTH : Z := 1024.                                             (* [comment removed for export] *)
Definition OC_BYTES : Z := 8 * MAX_DEPTH.                                     (* [comment removed for export] *)
Definition ISARR_BYTES : Z := MAX_DEPTH.                                      (* [comment removed for export] *)
Definition PADDING : Z := 64.                                                 (* [comment removed for export] *)
Definition COPY_BYTES (len : Z) : Z := len + PADDING.                         (* [comment removed for export] *)
Definition COPY_LIMIT : Z := 2^20.                                            (* [comment removed for export] *)
(* [comment removed for export] *)
Definition copy_made (len : Z) : bool := COPY_BYTES len <=? COPY_LIMIT.

Section HarnessP.
Context {St ptr : Type}.
Variable raw_malloc : Z -> M St (option ptr).      (* [comment removed for export] *)
Variable raw_free : ptr -> M St unit.              (* [comment removed for export] *)
Variable new_handler : M St Empty_set.             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition opnew (sz : Z) : M St ptr :=
  let sz' := if sz =? 0 then 1 else sz in
  r <- raw_malloc sz' ;;
  match r with
  | Some p => mret p
  | None => e <- new_handler ;; match (e : Empty_set) with end
  end.
Definition opdelete (p : ptr) : M St unit := raw_free p.

(* [comment removed for export] *)
Definition odelete (b : option ptr) : M St unit := match b with Some p => opdelete p | None => mret tt end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition doc_allocate (len : Z) : M St (ptr * ptr) :=
  sb <- opnew (SB_BYTES len) ;; tp <- opnew (TAPE_BYTES len) ;; mret (sb, tp).
(* [comment removed for export] *)
Definition impl_set_capacity (len : Z) : M St ptr := opnew (SIDX_BYTES len).
(* [comment removed for export] *)
Definition impl_set_max_depth : M St (ptr * ptr) :=
  oc <- opnew OC_BYTES ;; ia <- opnew ISARR_BYTES ;; mret (oc, ia).
(* [comment removed for export] *)
Definition impl_create (len : Z) : M St (ptr * ptr * ptr * ptr) :=
  im <- opnew IMPL_BYTES ;; si <- impl_set_capacity len ;; ' (oc, ia) <- impl_set_max_depth ;; mret (im, si, oc, ia).
(* [comment removed for export] *)
Definition padded_alloc (len : Z) : M St (option ptr) :=
  if copy_made len then p <- opnew (COPY_BYTES len) ;; mret (Some p) else mret None.
(* [comment removed for export] *)
Definition root_copy (data : list Z) : M St unit :=
  match root_number_alloc data with
  | Some n => c <- opnew n ;; opdelete c
  | None => mret tt
  end.
(* [comment removed for export] *)
Definition parse_impl (data : list Z) : M St unit := root_copy data.

(* [comment removed for export] *)
Definition pblocks : Type := (ptr * ptr * (ptr * ptr * ptr * ptr) * option ptr)%type.

Definition parse_into_doc (data : list Z) : M St pblocks :=
  let len := zlength data in
  dd <- doc_allocate len ;;
  ii <- impl_create len ;;
  lb <- padded_alloc len ;;
  (match lb with Some _ => parse_impl data | None => mret tt end) ;;;
  mret (fst dd, snd dd, ii, lb).

(* [comment removed for export] *)
Definition doc_dtor (sb tp : ptr) : M St unit := opdelete sb ;;; opdelete tp.
(* [comment removed for export] *)
Definition impl_dtor (ii : ptr * ptr * ptr * ptr) : M St unit :=
  let '(im, si, oc, ia) := ii in opdelete ia ;;; opdelete oc ;;; opdelete si ;;; opdelete im.
(* [comment removed for export] *)
Definition parser_dtor (b : pblocks) : M St unit :=
  let '(sb, tp, ii, lb) := b in odelete lb ;;; doc_dtor sb tp ;;; impl_dtor ii.

(* [comment removed for export] *)
Definition fuzz_one (data : list Z) : M St Z := b <- parse_into_doc data ;; parser_dtor b ;;; mret 0.

(* [comment removed for export] *)
Definition client_exit : M St unit := mret tt.

Lemma client_exit_ret : forall s, client_exit s = Ret (ITree.Exc.Ok (tt, s)).
Proof. reflexivity. Qed.
End HarnessP.

(* [comment removed for export] *)
Lemma ROUNDUP64_bounds : forall x, 0 <= x -> x <= ROUNDUP64 x < x + 64 /\ ROUNDUP64 x mod 64 = 0.
Proof.
  intros x Hx. unfold ROUNDUP64. split; [split|].
  - pose proof (Z.div_mod (x + 63) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 63) 64 ltac:(lia)). lia.
  - pose proof (Z.div_mod (x + 63) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 63) 64 ltac:(lia)). lia.
  - apply Z.mod_mul. lia.
Qed.

Lemma sizes_pos : forall len, 0 <= len ->
  0 < SB_BYTES len /\ 0 < TAPE_BYTES len /\ 0 < IMPL_BYTES /\ 0 < SIDX_BYTES len /\ 0 < OC_BYTES /\ 0 < ISARR_BYTES /\ 0 < COPY_BYTES len.
Proof.
  intros len H. unfold SB_BYTES, TAPE_BYTES, IMPL_BYTES, SIDX_BYTES, OC_BYTES, ISARR_BYTES, COPY_BYTES, PADDING, MAX_DEPTH, CAP.
  pose proof (ROUNDUP64_bounds (5 * (Z.max len 32 / 3) + 64) ltac:(pose proof (Z.div_pos (Z.max len 32) 3); lia)).
  pose proof (ROUNDUP64_bounds (Z.max len 32 + 3) ltac:(lia)).
  pose proof (ROUNDUP64_bounds (Z.max len 32) ltac:(lia)).
  pose proof (Z.div_pos (Z.max len 32) 3). lia.
Qed.

(* [comment removed for export] *)
Lemma sizes_upper : forall len, 0 <= len ->
  SB_BYTES len < 5 * (CAP len / 3) + 128 /\ TAPE_BYTES len < 8 * CAP len + 536 /\ SIDX_BYTES len < 4 * CAP len + 292
  /\ COPY_BYTES len = len + 64 /\ OC_BYTES = 8192 /\ ISARR_BYTES = 1024 /\ IMPL_BYTES = 96.
Proof.
  intros len H. unfold SB_BYTES, TAPE_BYTES, IMPL_BYTES, SIDX_BYTES, OC_BYTES, ISARR_BYTES, COPY_BYTES, PADDING, MAX_DEPTH.
  assert (C : 32 <= CAP len) by (unfold CAP; lia).
  pose proof (ROUNDUP64_bounds (5 * (CAP len / 3) + 64) ltac:(pose proof (Z.div_pos (CAP len) 3); lia)).
  pose proof (ROUNDUP64_bounds (CAP len + 3) ltac:(lia)).
  pose proof (ROUNDUP64_bounds (CAP len) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma tape_le_2p29 : forall len, 0 <= len <= 2^26 - 7 -> TAPE_BYTES len <= 2^29.
Proof.
  intros len H. unfold TAPE_BYTES, CAP, ROUNDUP64.
  assert (E : (Z.max len 32 + 3 + 63) / 64 <= (2^26 + 63) / 64) by (apply Z.div_le_mono; lia).
  change ((2^26 + 63) / 64) with (2^20) in E. lia.
Qed.

Lemma sizes_le_2p29 : forall len, 0 <= len <= 2^26 - 7 ->
  SB_BYTES len <= 2^29 /\ TAPE_BYTES len <= 2^29 /\ IMPL_BYTES <= 2^29 /\ SIDX_BYTES len <= 2^29 /\ OC_BYTES <= 2^29
  /\ ISARR_BYTES <= 2^29 /\ COPY_BYTES len <= 2^29.
Proof.
  intros len H. pose proof (tape_le_2p29 len H). pose proof (sizes_upper len ltac:(lia)) as U.
  assert (C : CAP len <= 2^26) by (unfold CAP; lia). pose proof (Z.div_le_upper_bound (CAP len) 3 (2^26) ltac:(lia) ltac:(lia)). lia.
Qed.
