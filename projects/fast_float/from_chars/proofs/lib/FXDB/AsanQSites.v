(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation ASEGSQ := AsanUbsan.M.loaded_segments.

Definition rr (k : Z) : reg := Z_to_bv 5 k.
(* [comment removed for export] *)
Definition QS_PRINTF : qsite := QS 0x5329c (rr 10) (rr 12) (rr 22) (rr 11) (rr 13) (rr 14) true (Z_to_bv 13 (0x531d8 - 0x532c8)) true.
(* [comment removed for export] *)
Definition QS_MEMCHR : qsite := QS 0x51c2c (rr 11) (rr 13) (rr 18) (rr 12) (rr 14) (rr 15) true (Z_to_bv 13 (0x51d50 - 0x51c58)) false.
(* [comment removed for export] *)
Definition QS_STRNLEN : qsite := QS 0x5077c (rr 11) (rr 13) (rr 18) (rr 12) (rr 14) (rr 15) true (Z_to_bv 13 (0x50864 - 0x507a8)) false.
(* [comment removed for export] *)
Definition QS_MEMCPY_S : qsite := QS 0x61420 (rr 13) (rr 19) (rr 11) (rr 14) (rr 15) (rr 16) false (Z_to_bv 13 (0x61708 - 0x6144c)) false.
Definition QS_MEMCPY_D : qsite := QS 0x61468 (rr 13) (rr 20) (rr 10) (rr 14) (rr 15) (rr 16) false (Z_to_bv 13 (0x61808 - 0x61494)) false.

Ltac bveq_tac := repeat match goal with
  | |- @eq (bv _) _ _ => apply bv_eq; vm_compute; reflexivity
  | |- @eq Z _ _ => reflexivity
  | |- @eq bool _ _ => reflexivity
  | |- _ = _ => f_equal
  end.
Ltac qins_tac := unfold qins; eexists; split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | vm_compute; bveq_tac]].
Ltac qsite_tac := cbn [qsite_ok];
  repeat split; try (let Hc := fresh "Hc" in intro Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate); try qins_tac.

Lemma QS_PRINTF_ok : qsite_ok ASEGSQ QS_PRINTF. Proof. qsite_tac. Qed.
Lemma QS_MEMCHR_ok : qsite_ok ASEGSQ QS_MEMCHR. Proof. qsite_tac. Qed.
Lemma QS_STRNLEN_ok : qsite_ok ASEGSQ QS_STRNLEN. Proof. qsite_tac. Qed.
Lemma QS_MEMCPY_S_ok : qsite_ok ASEGSQ QS_MEMCPY_S. Proof. qsite_tac. Qed.
Lemma QS_MEMCPY_D_ok : qsite_ok ASEGSQ QS_MEMCPY_D. Proof. qsite_tac. Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import FxMchr FxMNode.
Definition MC_PCW : Z := 0xd4478.
Lemma MC_SITE_ok : msite_ok ASEGSQ MC_PCW.
Proof. unfold msite_ok. repeat split; qins_tac. Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import FxSNodes.
Definition NS_PCORE : nsite := NS 0xcd1e0 (rr 12) (rr 11).
Lemma NS_PCORE_ok : nsite_ok ASEGSQ NS_PCORE.
Proof. unfold nsite_ok, NS_PCORE; cbn [ns_pc ns_rd ns_rs]. split; [intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|].
  split; [lia|]. split; [lia|]. qins_tac. Qed.
(* [comment removed for export] *)
