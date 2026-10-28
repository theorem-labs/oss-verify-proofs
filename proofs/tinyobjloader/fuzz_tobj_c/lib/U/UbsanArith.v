(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "SLit"; "sv"; "valuation"; "SMdW"; "SAlu"; "holds"; "SPBranch"; "SPNot"; "SAluW"; "SPUle"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "M_MUL"; "ALU_SUB"; "BC_EQ"; "ALU_SRA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "sub"; "modulo"; "div"; "lt"; "@Corelib.Init.Logic"; "eq"; "False"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.UbsanArith"; "m1u"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "M64v"; "zsext"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymSoundW
  SymComplete SymFrame SymEntail SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma U_mulw_m1 : ltac2:(tb__ "0|3|
S3S2S17S1aSbQ40M0S0R2S4SdS1N1A1R1A3A2A2S1dZ20M1S14S13S12Z2G1A2M2S14SbG0S0R2R1A2A2G2A2A2G2A2A2A3Fa;Frho;").
Proof.
  intros rho a. cbn [eval]. unfold mul_div.
  set (x := eval rho a). pose proof (urange x) as Rx.
  assert (M : bv_unsigned (low32 (Z_to_bv 64 (-1)) * low32 x)%bv = (2 ^ 32 - bv_unsigned x mod 2 ^ 32) mod 2 ^ 32).
  { rewrite bv_mul_unsigned, !low32_umod, Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
    change ((-1) mod 2 ^ 64 mod 2 ^ 32) with (2 ^ 32 - 1).
    set (m := bv_unsigned x mod 2 ^ 32). assert (Hm : 0 <= m < 2 ^ 32) by (subst m; apply Z.mod_pos_bound; lia).
    replace ((2 ^ 32 - 1) * m) with ((2 ^ 32 - m) + (m - 1) * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. reflexivity. }
  set (p := (low32 (Z_to_bv 64 (-1)) * low32 x)%bv) in *.
  pose proof (U_sext_w 32 (sext 64 p) ltac:(lia) ltac:(cbv; discriminate)) as S.

  clear S. unfold sext, zsext. rewrite bv_sign_extend_unsigned. unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31). rewrite two64, M.
  set (m := (2 ^ 32 - bv_unsigned x mod 2 ^ 32) mod 2 ^ 32). assert (Hm : 0 <= m < 2 ^ 32) by (subst m; apply Z.mod_pos_bound; lia).
  change (2 ^ (32 - 1)) with (2 ^ 31). unfold M64v.
  destruct (Z.ltb_spec m (2 ^ 31)).
  - rewrite (Z.mod_small (m + 2 ^ 31)) by lia. rewrite Z.mod_small by lia. lia.
  - replace (m + 2 ^ 31) with ((m - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
    rewrite (Z.mod_small (m - 2 ^ 31)) by lia.
    replace (m - 2 ^ 31 - 2 ^ 31) with ((m + 18446744073709551616 - 2 ^ 32) + (-1) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma U_sraw1_small : ltac2:(tb__ "0|3|
S3S2S11SbQ40M0S0R2R1A2A2S13S12Z2M1Z1fA2Z1M2A2A2S17S1aSbG0S0R3S9S10R2S1G2A1A3A2A2S15SbG0S0R3R2A2A2G1A2A3F_;Fa;Frho;").
Proof.
  intros rho a Ha. cbn [eval]. unfold alu32, alu.
  pose proof (urange (eval rho a)) as R1.
  assert (M : bv_unsigned (bv_and (low32 (Z_to_bv 64 1)) (Z_to_bv 32 31)) = 1).
  { rewrite bv_and_unsigned, low32_umod. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). reflexivity. }
  assert (L : bv_unsigned (low32 (eval rho a)) = bv_unsigned (eval rho a)).
  { rewrite low32_umod. apply Z.mod_small. lia. }
  assert (Ls : bv_signed (low32 (eval rho a)) = bv_unsigned (eval rho a)).
  { unfold bv_signed. rewrite L. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia. }
  assert (R : bv_unsigned (bv_ashiftr (low32 (eval rho a)) (bv_and (low32 (Z_to_bv 64 1)) (Z_to_bv 32 31))) = bv_unsigned (eval rho a) / 2).
  { rewrite bv_ashiftr_unsigned, M, Ls. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
    apply bv_wrap_small. change (bv_modulus 32) with (2 ^ 32). split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite sext64_32_small by (rewrite R; apply Z.div_lt_upper_bound; lia). exact R.
Qed.

Lemma ule_lit' : ltac2:(tb__ "0|0|
S3S2S1aS6R3SaR2S1R1A1A2A2S19S11Z0R2A2S16R2S1cA2A2S11SbQ40S0R5R4A2A2R3A2F_;F_;Fc;Fx;Frho;").
Proof. intros rho x c H Hc. cbn [holds] in H. rewrite U_lit in H. rewrite Z.mod_small in H by lia. exact H. Qed.

Lemma mulw_m1_small : ltac2:(tb__ "0|1|
S3S2S11SbQ40M0S0R2R1A2A2S13S12Z2Z1fA2Z1A2A2S17S1aSbG0S0R3S4SdS1N1A1R2A3A2A2SbG0S0R3S5SeS1Z0A1R2A3A2A2A3F_;Fa;Frho;").
Proof.
  intros rho a Ha. rewrite U_mulw_m1, U_sub, U_lit. unfold zsext, M64v. pose proof (urange (eval rho a)) as R.
  rewrite (Z.mod_small (bv_unsigned (eval rho a)) (2 ^ 32)) by lia.
  change (0 mod 18446744073709551616) with 0. change (2 ^ (32 - 1)) with (2 ^ 31).
  destruct (Z.eq_dec (bv_unsigned (eval rho a)) 0) as [Z0|NZ].
  - rewrite Z0. reflexivity.
  - rewrite (Z.mod_small (2 ^ 32 - _)) by lia.
    destruct (Z.ltb_spec (2 ^ 32 - bv_unsigned (eval rho a)) (2 ^ 31)); [lia|].
    replace (0 - bv_unsigned (eval rho a)) with ((18446744073709551616 - bv_unsigned (eval rho a)) + (-1) * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma trap_ne_false : ltac2:(tb__ "0|0|
S3S2S11SbQ40S0R2R1A2A2S13S12Z2Z1fA2Z1A2A2S6R3S8S7SfS4SdS1N1A1R2A3S5SeS1Z0A1R2A3A3A1A2S18F_;F_;Fa;Frho;").
Proof.
  intros rho a Ha H. apply (proj1 (holds_nbeq rho _ _)) in H. apply H. apply (mulw_m1_small rho a Ha).
Qed.

Definition m1u : Z := 18446744073709551615.
Lemma bv_m1u : Z_to_bv 64 m1u = Z_to_bv 64 (-1).
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
Lemma eval_mulw_m1u : ltac2:(tb__ "0|0|
S3S2S17ScQ40A1S0R2S4SdS1S1bA1R1A3A2S0R2S4SdS1N1A1R1A3A2A3Fa;Frho;").
Proof. intros rho a. cbn [eval]. rewrite bv_m1u. reflexivity. Qed.
Lemma trap_ne_false_u : ltac2:(tb__ "0|0|
S3S2S11SbQ40S0R2R1A2A2S13S12Z2Z1fA2Z1A2A2S6R3S8S7SfS4SdS1S1bA1R2A3S5SeS1Z0A1R2A3A3A1A2S18F_;F_;Fa;Frho;").
Proof.
  intros rho a Ha H. apply (trap_ne_false rho a Ha).
  apply (proj2 (holds_nbeq rho _ _)). apply (proj1 (holds_nbeq rho _ _)) in H.
  intros E. apply H. rewrite eval_mulw_m1u. exact E.
Qed.
