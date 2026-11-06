(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr Mem TacX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma amo_aligned_intro : forall a : Z, 0 <= a < 2^64 -> a mod 4 = 0 -> amo_aligned AW (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.

(* [comment removed for export] *)
Lemma amo_aligned_intro_w : forall a : word, bv_unsigned a mod 4 = 0 -> amo_aligned AW a = true.
Proof. intros a Hm. unfold amo_aligned, amo_bytes. rewrite Hm. reflexivity. Qed.

Ltac amo_align AMO :=
  try (rewrite AMO; cbv beta iota delta [negb]);
  try (rewrite Z.eqb_refl; cbv iota).

(* [comment removed for export] *)
Ltac amo_step AMO :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply evt_step;
      [ split; [reflexivity|];
        rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_regs; amo_align AMO; exec_cbv; amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_le_bytes_4_congr : forall a b, a mod 2^32 = b mod 2^32 -> Z_to_le_bytes 4 a = Z_to_le_bytes 4 b.
Proof.
  intros a b E. rewrite <- (Z_to_le_bytes_mod 4 a 32) by (cbn; lia). rewrite <- (Z_to_le_bytes_mod 4 b 32) by (cbn; lia).
  rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma amoadd32_store_bytes : forall (v : word) (s : bv 32),
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 v))) s))
  = Z_to_le_bytes 4 ((bv_unsigned v + bv_unsigned s) mod 2^32).
Proof.
  intros v s. unfold amo_val. rewrite bv_add_unsigned.
  rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4.
  apply Z_to_le_bytes_4_congr.
  unfold bv_wrap. change (bv_modulus 32) with (2^32). change (2 ^ Z.of_N 32) with (2^32).
  rewrite !Z.mod_mod by lia. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma amoadd32_old : forall v : word, sext 64 (bv_extract 0 32 (le_bytes_to_word (le4 v))) = sx32 v.
Proof. exact sext_extract_le4. Qed.

(* [comment removed for export] *)
Ltac amo_fold_bytes :=
  try match goal with
      | |- context [Z_to_le_bytes 4 ?z] =>
          lazymatch z with
          | Z0 => fail | Zpos _ => fail
          | _ => let z' := eval vm_compute in z in change z with z'
          end
      end.

(* [comment removed for export] *)
Ltac amoadd_step AMO :=
  amo_step AMO;
  rewrite ?amoadd32_store_bytes;
  rewrite ?wz_unsigned by lia;
  amo_fold_bytes;
  fix_lit_store.
