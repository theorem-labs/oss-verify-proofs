(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_stage2_numkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac gshow_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "STUCK AT PC =" pc end.
Ltac ngexp_dbg cuts fin := ngrun_cut cuts; first [ fin | (ngbranch; ngexp_dbg cuts fin) | gshow_pc ].
Ltac ngexp_f_dbg cuts fin keep := ngrun_cut_f cuts keep; first [ fin | (ngbranch; ngexp_f_dbg cuts fin keep) | gshow_pc ].

Ltac intro_words := repeat lazymatch goal with |- forall y : ?T, _ => lazymatch T with bv 64 => intro | word => intro end end.

Ltac ntape_norm :=
  repeat match goal with
  | H : context [(e_TAPE ?E + 8 * W ?s + 16)%Z] |- _ => replace (e_TAPE E + 8 * W s + 16)%Z with (e_TAPE E + 8 * (W s + 2))%Z in H by lia
  end.
Ltac nclose := ntape_norm; s2_close_mem0.

Ltac nz_lt_by tac := apply B_nz_lt; tac.
Ltac nopen H := s2_open_mem H.
Ltac nexit0 KX := gexit KX.
Ltac nexit KX := ngrun_to 0xcd104%Z; nexit0 KX.

Lemma dval_step_wz : forall bs q c, (0 <= c)%Z -> (48 <= B bs (q + c) <= 57)%Z ->
  Z_to_bv 64 (dval bs q c mod 18446744073709551616 * 10 + Z.land (B bs (q + c) + -48) 255) = Z_to_bv 64 (dval bs q (c + 1)).
Proof.
  intros bs q c Hc HB. apply wz_eq_mod. rewrite dval_S by lia.
  rewrite (land255_small (B bs (q + c) + -48)) by lia.
  rewrite Z.add_mod by lia. rewrite Z.mul_mod_idemp_l by lia. rewrite <- Z.add_mod by lia.
  reflexivity.
Qed.

Local Open Scope Z_scope.

Lemma land_bit63_small : forall y, 0 <= y < 9223372036854775808 -> Z.land y 9223372036854775808 = 0.
Proof.
  intros y Hy. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  change 9223372036854775808 with (2 ^ 63). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 n) as [<-|NE]; [|apply andb_false_r].
  rewrite andb_true_r. destruct (Z.eq_dec y 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lxor_bias_small : forall y, 0 <= y < 9223372036854775808 -> Z.lxor y 9223372036854775808 = y + 9223372036854775808.
Proof. intros y Hy. symmetry. apply Z.add_nocarry_lxor. apply land_bit63_small. exact Hy. Qed.
Lemma lxor_bias_signed : forall e, -9223372036854775808 <= e < 9223372036854775808 ->
  Z.lxor (e mod 18446744073709551616) 9223372036854775808 = e + 9223372036854775808.
Proof.
  intros e He. destruct (Z_lt_dec e 0) as [N|P].
  - replace (e mod 18446744073709551616) with (e + 9223372036854775808 + 9223372036854775808)
      by (rewrite <- (Z.mod_add e 1) by lia; symmetry; rewrite Z.mod_small by lia; lia).
    rewrite <- (lxor_bias_small (e + 9223372036854775808)) by lia.
    rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity.
  - rewrite Z.mod_small by lia. apply lxor_bias_small. lia.
Qed.

Ltac b_lia := lia.
Ltac g_bias :=
  repeat match goal with
  | |- context [Z.lxor (?e mod 18446744073709551616) 9223372036854775808] => rewrite (lxor_bias_signed e) by b_lia
  | |- context [Z.lxor ?y 9223372036854775808] =>
      lazymatch y with
      | Z.modulo _ _ => fail
      | _ => rewrite (lxor_bias_small y) by b_lia
      end
  end.
Lemma land255_any : forall x, Z.land x 255 = x mod 256.
Proof. intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma p5u_sw : forall e d, -342 <= e <= 308 -> 684 <= d <= 685 ->
  bv_swrap 32 (Z.shiftl (e mod 18446744073709551616) 1 mod 18446744073709551616 + d) mod 18446744073709551616 = 2 * e + d.
Proof.
  intros e d HE Hd. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  lia.
Qed.
Lemma p5u_sw' : forall e d, -342 <= e <= 308 -> 684 <= d <= 685 ->
  bv_swrap 32 (Z.shiftl (e mod 18446744073709551616) 1 + d) mod 18446744073709551616 = 2 * e + d.
Proof.
  intros e d HE Hd. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  lia.
Qed.
Local Close Scope Z_scope.
