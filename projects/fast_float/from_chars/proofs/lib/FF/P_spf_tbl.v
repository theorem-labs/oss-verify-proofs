(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Export P_spd_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation PSEGS := Plain.M.loaded_segments.

Fixpoint image_u32s (A : Z) (n : nat) : list Z :=
  match n with O => [] | S n' =>
    match image_bytes PSEGS A 4 with Some xs => bv_unsigned (le_bytes_to_word xs) | None => 0%Z end
    :: image_u32s (A + 4) n' end.

(* [comment removed for export] *)
Definition TBLF : list Z := Eval vm_compute in (image_u32s 0x15d20 11).
Lemma TBLF_ok : table_b PSEGS 0x15d20 4 (fun v => le4 (Z_to_bv 64 v)) TBLF = true.
Proof. vm_compute. reflexivity. Qed.
Lemma TBLF_length : length TBLF = 11%nat. Proof. reflexivity. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma swrap32_small : forall z, (- 2^31 <= z < 2^31)%Z -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31)%Z by reflexivity.
  replace (bv_modulus 32) with (2^32)%Z by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.
Lemma swrap32_unsigned : forall q : word, (- 2^31 <= bv_signed q < 2^31)%Z -> bv_swrap 32 (bv_unsigned q) = bv_signed q.
Proof.
  intros q Hq. pose proof (zb_signed q) as SQ.
  pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
  unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31)%Z by reflexivity.
  replace (bv_modulus 32) with (2^32)%Z by reflexivity.
  destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
Lemma pce_A_range : forall q : word, (-342 <= bv_signed q <= 308)%Z ->
  (-1137 <= bv_swrap 32 (Z.shiftr (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_unsigned q * 217706)))) 16) <= 1023)%Z.
Proof. intros q Hq. apply ce_A_range. exact Hq. Qed.
