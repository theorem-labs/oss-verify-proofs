(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/mbedtls/fuzz_pkcs7/lib/Lib/Asn1Aux.v; 1278 of its 1342 lines of code are new or changed and 385 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Prog/classify_core.v, with its module paths and module names changed; 100 of its 145 lines of code are new or changed and 1297 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_frame/lib/Prog/crt_m2_bytes.v, with its module paths and module names changed; 37 of its 68 lines of code are new or changed and 114 lines of the source are left out. *)
(* list, byte, register and code facts for the segment crt_m2 of check_round_trip in fuzz_frame.ubsan (0x1333c .. 0x133c4). *)
(* The facts that U/Prog/crt_m2.v uses: memcmp_model of a list with itself; build_out with a
   cap of the frame length is build_frame; the parts of the frame bytes at buf; the values of
   sltiu, sext.w, lhu and lbu on the registers of the segment; build_code when crt_ok b holds
   and when it does not. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import diginet_frame_build_c crt_defs.
Import ListNotations.
Open Scope Z_scope.

(** * Lists *)

(* memcmp_model of a list with itself, over at most its length, is 0. *)
Lemma m2_memcmp_self : forall n l, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  induction n as [|n IH]; intros l H; [reflexivity|].
  destruct l as [|a l]; cbn [length] in H; [lia|].
  cbn [memcmp_model]. rewrite Z.eqb_refl. apply IH. lia.
Qed.

(* With a cap of exactly the code it answers, diginet_frame_build leaves build_frame. *)
Lemma m2_build_out_eq : forall dmac smac send ack retry cmd ncmds bb mode oj,
  build_code bb (Z.of_nat (length oj)) = Z.of_nat (length oj) ->
  build_out dmac smac send ack retry cmd ncmds bb mode oj =
  build_frame dmac smac send ack retry cmd ncmds bb (mode =? 1).
Proof.
  intros dmac smac send ack retry cmd ncmds bb mode oj H. unfold build_out. cbv zeta. rewrite H.
  replace (0 <=? Z.of_nat (length oj)) with true by (symmetry; apply Z.leb_le; lia).
  rewrite Nat2Z.id, skipn_all. apply app_nil_r.
Qed.

(** * Memory *)

Lemma m2_rw_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ B] _]. exact B. Qed.

Lemma m2_cb_len : forall m A n j, rw_cells rsegs m A [CB n j] -> length j = n.
Proof. intros m A n j [[[Hl _] _] _]. exact Hl. Qed.

(* The bytes firstn n (skipn k l) at A + k, for the bytes l at A. *)
Lemma m2_bytes_sub : forall m A l k n, bytes_at rsegs m A l -> (k <= length l)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m A l k n H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by exact Hk.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

(** * Register values *)

Lemma m2_sltiu_t : forall z k, 0 <= z < k -> k < 2^64 -> v_sltiu (Z_to_bv 64 z) k = Z_to_bv 64 1.
Proof.
  intros z k Hz Hk. unfold v_sltiu. rewrite unsigned_lit by lia. unfold bv_wrap.
  change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
  replace (z <? k) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma m2_sltiu_f : forall z k, 0 <= k <= z -> z < 2^64 -> v_sltiu (Z_to_bv 64 z) k = Z_to_bv 64 0.
Proof.
  intros z k Hz Hk. unfold v_sltiu. rewrite unsigned_lit by lia. unfold bv_wrap.
  change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
  replace (z <? k) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* sext.w of a value below 2^31. *)
Lemma m2_swrap : forall z, 0 <= z < 2^31 -> bv_swrap 32 (z + 0) = z.
Proof. intros z Hz. rewrite Z.add_0_r. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

(* lhu of a uint16_t field. *)
Lemma m2_zx16 : forall r, 0 <= r < 2^16 -> zx16 (Z_to_bv 64 r) = Z_to_bv 64 r.
Proof. intros r Hr. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* lbu of a uint8_t field. *)
Lemma m2_zxb : forall c, 0 <= c < 2^8 -> zxb (b8 c) = Z_to_bv 64 c.
Proof. intros c Hc. unfold zxb. change (bv_unsigned (b8 c)) with (bz (b8 c)). rewrite bz_b8 by lia. reflexivity. Qed.

(** * The answer of diginet_frame_build *)

Lemma m2_code_true : forall b, crt_ok b = true ->
  build_code (fr_body b) (frame_len (length (fr_body b))) = frame_len (length (fr_body b)).
Proof.
  intros b H. unfold crt_ok in H. apply andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply negb_true_iff in H2. unfold build_code. rewrite H2.
  replace (1484 <? Z.of_nat (length (fr_body b))) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Z.ltb_irrefl. reflexivity.
Qed.

Lemma m2_code_false : forall b c, crt_ok b = false -> build_code (fr_body b) c = -4 \/ build_code (fr_body b) c = -10.
Proof.
  intros b c H. unfold crt_ok in H. unfold build_code.
  destruct (1484 <? Z.of_nat (length (fr_body b))) eqn:E1; [left; reflexivity|]. apply Z.ltb_ge in E1.
  destruct (system_at (fr_body b)) eqn:E2; [right; reflexivity|].
  rewrite (proj2 (Z.leb_le _ _) E1) in H. discriminate.
Qed.
