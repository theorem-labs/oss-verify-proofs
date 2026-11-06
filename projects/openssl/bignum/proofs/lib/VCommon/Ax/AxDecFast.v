(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxState.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition wsext (m h z : Z) : w64 :=
  if z <? h then W false (Uint63.of_Z z) else W true (PrimInt63.sub 9223372036854775807%uint63 (Uint63.of_Z (m - 1 - z))).

Definition dec_fast (i : instr) : dinstr :=
  match i with
  | Lui rd imm => DLui (ri rd) (wsext 4294967296 2147483648 (4096 * bv_unsigned imm))
  | Auipc rd imm => DAuipc (ri rd) (wsext 4294967296 2147483648 (4096 * bv_unsigned imm))
  | Jal rd imm => DJal (ri rd) (wsext 2097152 1048576 (bv_unsigned imm))
  | Jalr rd rs1 imm => DJalr (ri rd) (ri rs1) (wsext 4096 2048 (bv_unsigned imm))
  | Branch bc rs1 rs2 imm => DBranch bc (ri rs1) (ri rs2) (wsext 8192 4096 (bv_unsigned imm))
  | Load sz sg rd rs1 imm => DLoad sz sg (ri rd) (ri rs1) (wsext 4096 2048 (bv_unsigned imm))
  | Store sz rs1 rs2 imm => DStore sz (ri rs1) (ri rs2) (wsext 4096 2048 (bv_unsigned imm))
  | OpImm op rd rs1 imm => DOpImm op (ri rd) (ri rs1) (wsext 4096 2048 (bv_unsigned imm))
  | ShiftImm op rd rs1 sh => DShiftImm op (ri rd) (ri rs1) (W false (Uint63.of_Z (bv_unsigned sh)))
  | Op op rd rs1 rs2 => DOp op (ri rd) (ri rs1) (ri rs2)
  | OpImm32 rd rs1 imm => DOpImm32 (ri rd) (ri rs1) (wsext 4096 2048 (bv_unsigned imm))
  | ShiftImm32 op rd rs1 sh => DShiftImm32 op (ri rd) (ri rs1) (W false (Uint63.of_Z (bv_unsigned sh)))
  | Op32 op rd rs1 rs2 => DOp32 op (ri rd) (ri rs1) (ri rs2)
  | Mul op rd rs1 rs2 => DMul op (ri rd) (ri rs1) (ri rs2)
  | Mul32 op rd rs1 rs2 => DMul32 op (ri rd) (ri rs1) (ri rs2)
  | Fence _ _ _ _ _ => DFence
  | FenceI _ _ _ => DFence
  | Lr wd _ _ rd rs1 => DLr wd (ri rd) (ri rs1)
  | Sc wd _ _ rd rs1 rs2 => DSc wd (ri rd) (ri rs1) (ri rs2)
  | Amo op wd _ _ rd rs1 rs2 => DAmo op wd (ri rd) (ri rs1) (ri rs2)
  | _ => DUnsupported
  end.

Lemma wB_63' : Uint63Axioms.wB = 2 ^ 63.
Proof. reflexivity. Qed.

Lemma wsext_ok (n : N) (x : bv n) : (1 <= n <= 62)%N ->
  w_of_bv (sext 64 x) = wsext (2 ^ Z.of_N n) (2 ^ (Z.of_N n - 1)) (bv_unsigned x).
Proof.
  intros Hn. apply wZ_inj. rewrite wZ_w_of_bv. unfold sext. rewrite bv_sign_extend_unsigned.
  pose proof (bv_unsigned_in_range n x) as Hx. unfold bv_modulus in Hx.
  unfold bv_signed, bv_swrap, bv_half_modulus, bv_wrap, bv_modulus.
  set (z := bv_unsigned x) in *.
  assert (Hm : 2 ^ Z.of_N n = 2 * 2 ^ (Z.of_N n - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  assert (Hh : 1 <= 2 ^ (Z.of_N n - 1) <= 2 ^ 61).
  { split; [apply (Z.pow_le_mono_r 2 0); lia | apply Z.pow_le_mono_r; lia]. }
  replace (2 ^ Z.of_N n `div` 2) with (2 ^ (Z.of_N n - 1)) by (rewrite Hm, Z.mul_comm, Z.div_mul; lia).
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  unfold wsext, wZ. cbn [wh wl].
  pose proof (Uint63.to_Z_bounded 9223372036854775807%uint63) as B. rewrite ?wB_63' in B.
  destruct (Z.ltb_spec z (2 ^ (Z.of_N n - 1))) as [Hz|Hz]; cbn [wh wl].
  - rewrite (Z.mod_small (z + _)) by lia. replace (z + 2 ^ (Z.of_N n - 1) - 2 ^ (Z.of_N n - 1)) with z by lia.
    rewrite Z.mod_small by lia. rewrite Uint63.of_Z_spec, wB_63', Z.mod_small by lia. lia.
  - replace ((z + 2 ^ (Z.of_N n - 1)) mod 2 ^ Z.of_N n) with (z + 2 ^ (Z.of_N n - 1) - 2 ^ Z.of_N n).
    2:{ apply Z.mod_unique with 1; lia. }
    rewrite Uint63Axioms.sub_spec, Uint63.of_Z_spec, wB_63'.
    change (Uint63Axioms.to_Z 9223372036854775807%uint63) with 9223372036854775807.
    rewrite (Z.mod_small (2 ^ Z.of_N n - 1 - z)) by lia.
    rewrite (Z.mod_small (9223372036854775807 - _)) by lia.
    replace (z + 2 ^ (Z.of_N n - 1) - 2 ^ Z.of_N n - 2 ^ (Z.of_N n - 1)) with (z - 2 ^ Z.of_N n) by lia.
    symmetry. apply Z.mod_unique with (-1); unfold two63; lia.
Qed.

Lemma wzext_ok (n : N) (x : bv n) : (n <= 62)%N -> w_of_bv (zext 64 x) = W false (Uint63.of_Z (bv_unsigned x)).
Proof.
  intros Hn. apply wZ_inj. rewrite wZ_w_of_bv. unfold zext. rewrite bv_zero_extend_unsigned by lia.
  pose proof (bv_unsigned_in_range n x) as Hx. unfold bv_modulus in Hx.
  assert (2 ^ Z.of_N n <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia).
  unfold wZ. cbn [wh wl]. rewrite Uint63.of_Z_spec, wB_63', Z.mod_small by lia. lia.
Qed.

Lemma lui_val (imm : bv 20) : bv_unsigned (bv_concat 32 imm (Z_to_bv 12 0)) = 4096 * bv_unsigned imm.
Proof.
  rewrite (bv_concat_unsigned 32 12) by reflexivity. rewrite Z_to_bv_unsigned.
  change (bv_wrap 12 0) with 0. rewrite Z.lor_0_r. change (Z.of_N 12) with 12.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 12) with 4096. lia.
Qed.

Lemma lui_ok (imm : bv 20) :
  w_of_bv (sext 64 (bv_concat 32 imm (Z_to_bv 12 0))) = wsext 4294967296 2147483648 (4096 * bv_unsigned imm).
Proof. rewrite wsext_ok by lia. rewrite lui_val. reflexivity. Qed.

Theorem dec_fast_eq (i : instr) : dec_fast i = dec i.
Proof.
  destruct i; cbn [dec_fast dec]; try reflexivity.
  all: first [ rewrite lui_ok; reflexivity
             | rewrite wsext_ok by lia; reflexivity
             | rewrite wzext_ok by lia; reflexivity ].
Qed.
