(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib Require Import SFModel Arr FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require Import Prelim SoftFloat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require FloatScan.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec.FloatScan.DoubleOps.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require Import FloatScan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require F_scan_calls.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require Import F_scan_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.G_fmt_fp_lib.G_multf3_tail.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.G_fmt_fp_lib.G_multf3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require G_pop_arg.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.G_pop_arg.G_extenddftf2.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require F_sf_helpers2.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P.F_sf_helpers2.SF_buildtac.

(* [comment removed for export] *)
From Stdlib Require Import Zify Lia. From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc Require Import RProgNotJ.

(* [comment removed for export] *)
Definition scalbnl_prog (B K_103d8 B_multf3 B_extenddftf2 : Z) : RStep.ptree :=
  PNode 168%Z
  (PNode 84%Z
    (PNode 40%Z
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 0 2 2 4064 4
          (PJ_Store_SZ8_nnn 4 2 1 24 4
          (PJ_Store_SZ8_nnn 8 2 8 16 4
          (PJ_Store_SZ8_nnn 12 2 9 8 4
          (PJ_Store_SZ8_nnn 16 2 18 0 4
          (PJ_OpImm_ALU_ADD_nnn 20 8 12 0 4
          (PJ_Lui_nn 24 12 4 4
          (PJ_Branch_BC_LT_nnn 28 8 12 84 4
          (PJ_Lui_nn 32 9 16383 4
          (PJ_ShiftImm_ALU_SLL_nnn 36 9 9 37 4 nil)))))))))))
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 40 12 0 0 4
          (PJ_OpImm_ALU_ADD_nnn 44 13 9 0 4
          (PJ_Jal_nt 48 1 (jimm21 (B_multf3 - (B + 48))) 4
          (PJ_Lui_nn 52 12 8 4
          (PJ_OpImm32_nnn 56 12 12 4095 4
          (PJ_Branch_BC_LTU_nnn 60 8 12 144 4
          (PJ_OpImm_ALU_ADD_nnn 64 12 0 0 4
          (PJ_OpImm_ALU_ADD_nnn 68 13 9 0 4
          (PJ_Jal_nt 72 1 (jimm21 (B_multf3 - (B + 72))) 4
          (PJ_OpImm_ALU_ADD_nnn 76 18 10 0 4
          (PJ_Lui_nn 80 12 12 4 nil)))))))))))))
    (PNode 124%Z
      (PLeaf
          (PJ_OpImm32_nnn 84 12 12 4093 4
          (PJ_OpImm_ALU_ADD_nnn 88 9 11 0 4
          (PJ_Branch_BC_LTU_nnn 92 8 12 8 4
          (PJ_OpImm_ALU_ADD_nnn 96 8 12 0 4
          (PJ_Lui_nn 100 10 1048568 4
          (PJ_OpImm_ALU_ADD_nnn 104 10 10 2 4
          (PJ_Jal_nn 108 0 144 4
          (PJ_Lui_nn 112 12 1048572 4
          (PJ_OpImm32_nnn 116 12 12 1 4
          (PJ_Branch_BC_LT_nnn 120 12 8 104 4 nil)))))))))))
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 124 9 0 57 4
          (PJ_ShiftImm_ALU_SLL_nnn 128 9 9 49 4
          (PJ_OpImm_ALU_ADD_nnn 132 12 0 0 4
          (PJ_OpImm_ALU_ADD_nnn 136 13 9 0 4
          (PJ_Jal_nt 140 1 (jimm21 (B_multf3 - (B + 140))) 4
          (PJ_Lui_nn 144 12 1048568 4
          (PJ_OpImm32_nnn 148 12 12 116 4
          (PJ_Branch_BC_LTU_nnn 152 12 8 84 4
          (PJ_OpImm_ALU_ADD_nnn 156 12 0 0 4
          (PJ_OpImm_ALU_ADD_nnn 160 13 9 0 4
          (PJ_Jal_nt 164 1 (jimm21 (B_multf3 - (B + 164))) 4 nil))))))))))))))
  (PNode 252%Z
    (PNode 208%Z
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 168 18 10 0 4
          (PJ_Lui_nn 172 12 1048564 4
          (PJ_OpImm32_nnn 176 12 12 232 4
          (PJ_OpImm_ALU_ADD_nnn 180 9 11 0 4
          (PJ_Branch_BC_LTU_nnn 184 12 8 8 4
          (PJ_OpImm_ALU_ADD_nnn 188 8 12 0 4
          (PJ_Lui_nn 192 10 8 4
          (PJ_OpImm_ALU_ADD_nnn 196 10 10 3866 4
          (PJ_Jal_nn 200 0 52 4
          (PJ_OpImm_ALU_ADD_nnn 204 9 11 0 4 nil)))))))))))
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 208 18 10 0 4
          (PJ_Lui_nn 212 10 1048572 4
          (PJ_OpImm_ALU_ADD_nnn 216 10 10 1 4
          (PJ_Jal_nn 220 0 32 4
          (PJ_OpImm_ALU_ADD_nnn 224 9 11 0 4
          (PJ_OpImm_ALU_ADD_nnn 228 18 10 0 4
          (PJ_Jal_nn 232 0 24 4
          (PJ_OpImm_ALU_ADD_nnn 236 9 11 0 4
          (PJ_OpImm_ALU_ADD_nnn 240 18 10 0 4
          (PJ_Lui_nn 244 10 4 4
          (PJ_OpImm_ALU_ADD_nnn 248 10 10 3981 4 nil)))))))))))))
    (PNode 292%Z
      (PLeaf
          (PJ_Op_ALU_ADD_nnn 252 8 8 10 4
          (PJ_Auipc_nt 256 10 (hi20 (K_103d8 - (B + 256))) 4
          (PJ_FLoad_FMT_D_nnt 260 10 10 (lo12 (K_103d8 - (B + 256))) 4
          (PJ_Jal_nt 264 1 (jimm21 (B_extenddftf2 - (B + 264))) 4
          (PJ_OpImm_ALU_ADD_nnn 268 12 10 0 4
          (PJ_ShiftImm_ALU_SLL_nnn 272 8 8 48 4
          (PJ_ShiftImm_ALU_SLL_nnn 276 11 11 16 4
          (PJ_ShiftImm_ALU_SRL_nnn 280 11 11 16 4
          (PJ_Op_ALU_OR_nnn 284 11 8 11 4
          (PJ_Lui_nn 288 10 16383 4 nil)))))))))))
      (PLeaf
          (PJ_ShiftImm_ALU_SLL_nnn 292 10 10 36 4
          (PJ_Op_ALU_ADD_nnn 296 13 11 10 4
          (PJ_OpImm_ALU_ADD_nnn 300 10 18 0 4
          (PJ_OpImm_ALU_ADD_nnn 304 11 9 0 4
          (PJ_Jal_nt 308 1 (jimm21 (B_multf3 - (B + 308))) 4
          (PJ_Load_SZ8_true_nnn 312 1 2 24 4
          (PJ_Load_SZ8_true_nnn 316 8 2 16 4
          (PJ_Load_SZ8_true_nnn 320 9 2 8 4
          (PJ_Load_SZ8_true_nnn 324 18 2 0 4
          (PJ_OpImm_ALU_ADD_nnn 328 2 2 32 4
          (PJ_Jalr_nnn 332 0 1 0 4 nil)))))))))))))).

(* [comment removed for export] *)
Definition scalbnl_prog_r1 (B : Z) : RStep.ptree :=
  PLeaf
    (PJ_ShiftImm_ALU_SRL_nnn 0 13 13 63 4
    (PJ_ShiftImm_ALU_SLL_nnn 4 12 11 1 4
    (PJ_ShiftImm_ALU_SLL_nnn 8 11 11 16 4
    (PJ_ShiftImm_ALU_SLL_nnn 12 13 13 15 4
    (PJ_ShiftImm_ALU_SRL_nnn 16 12 12 49 4
    (PJ_Op_ALU_OR_nnn 20 12 13 12 4
    (PJ_ShiftImm_ALU_SLL_nnn 24 12 12 48 4
    (PJ_ShiftImm_ALU_SRL_nnn 28 11 11 16 4
    (PJ_Op_ALU_OR_nnn 32 11 12 11 4
    (PJ_Jalr_nnn 36 0 1 0 4 nil)))))))))).

(* [comment removed for export] *)
Definition scalbnl_prog_r2 (B : Z) : RStep.ptree :=
  PLeaf
    (PJ_ShiftImm_ALU_SLL_nnn 0 11 11 1 4
    (PJ_ShiftImm_ALU_SRL_nnn 4 11 11 1 4
    (PJ_Jalr_nnn 8 0 1 0 4 nil))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_scalbnl (IMG : RImg) := scalbnl_prog (sym 0x20548) (sym 0x103d8) (sym 0x1b3d0) (sym 0x1af98).
Definition PROGAT_CODE_scalbnl_1 (IMG : RImg) := scalbnl_prog_r1 (sym 0x20238).
Definition PROGAT_CODE_scalbnl_2 (IMG : RImg) := scalbnl_prog_r2 (sym 0x2053c).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_scalbnl : CodeAtT img_segs (sym 0x20548) (PROGAT_CODE_scalbnl IMG)}.
  Context {RB_scalbnl : RelCode (sym 0x20548) 336}.
  Context {CODE_scalbnl_1 : CodeAtT img_segs (sym 0x20238) (PROGAT_CODE_scalbnl_1 IMG)}.
  Context {RB_scalbnl_1 : RelCode (sym 0x20238) 40}.
  Context {CODE_scalbnl_2 : CodeAtT img_segs (sym 0x2053c) (PROGAT_CODE_scalbnl_2 IMG)}.
  Context {RB_scalbnl_2 : RelCode (sym 0x2053c) 12}.
  Context {RO_103d8 : RoB img_segs (sym 0x103d8) ([BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 240; BV 8 63])}.
  Context {RN_B_multf3_20548 : RelNear (sym 0x20548) (sym 0x1b3d0)}.
  Context {RN_B_extenddftf2_20548 : RelNear (sym 0x20548) (sym 0x1af98)}.
  Context {RS_K_103d8 : RelSym (sym 0x103d8)}.
  Context {SPEC_multf3_callq : multf3_callq_c}.
  Context {SPEC_extenddftf2_callv : extenddftf2_callv_c}.
  Collection ImgHyps := IMG CODE_scalbnl RB_scalbnl CODE_scalbnl_1 RB_scalbnl_1 CODE_scalbnl_2 RB_scalbnl_2 RO_103d8 RN_B_multf3_20548 RN_B_extenddftf2_20548 RS_K_103d8 SPEC_multf3_callq SPEC_extenddftf2_callv.


Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.
(* [comment removed for export] *)

Definition SCALBNL : Z := (sym 0x20548).
Definition COPYSIGNL : Z := (sym 0x20238).
Definition FABSL : Z := (sym 0x2053c).

Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma testbit_small_high : forall x k i, (0 <= x < 2^k)%Z -> (0 <= k <= i)%Z -> Z.testbit x i = false.
Proof.
  intros x k i Hx Hk. destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with k; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Lemma lor_low_high : forall x y k, (0 <= x < 2^k)%Z -> (0 <= y)%Z -> (0 <= k)%Z -> Z.lor x (y * 2^k) = (x + y * 2^k)%Z.
Proof.
  intros x y k Hx Hy Hk. apply lor_disjoint_add.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k).
  - rewrite Z.mul_pow2_bits_low by lia. apply Bool.andb_false_r.
  - rewrite (testbit_small_high x k i) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_highmask : forall x k, (0 <= x < 2^64)%Z -> (0 <= k < 64)%Z ->
  Z.land x (2^64 - 2^k) = (x - x mod 2^k)%Z.
Proof.
  intros x k Hx Hk. rewrite <- (zb_shr_shl x k) by lia.
  replace (2^64 - 2^k)%Z with (Z.shiftl (Z.ones (64 - k)) k).
  2:{ rewrite Z.shiftl_mul_pow2, Z.ones_equiv by lia. rewrite Z.mul_pred_l, <- Z.pow_add_r by lia. replace (64 - k + k)%Z with 64%Z by lia. lia. }
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i k).
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - k + k)%Z with i by lia.
    destruct (Z.lt_ge_cases i 64).
    + rewrite Z.ones_spec_low by lia. apply Bool.andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry. apply (testbit_small_high x 64 i); lia.
Qed.

Lemma land_bit63 : forall x, (0 <= x < 2^64)%Z -> Z.land x 9223372036854775808 = (x - x mod 2^63)%Z.
Proof. intros x Hx. change 9223372036854775808%Z with (2^64 - 2^63)%Z. apply land_highmask; lia. Qed.
Lemma land_m63 : forall x, Z.land x 9223372036854775807 = (x mod 2^63)%Z.
Proof. intros. change 9223372036854775807%Z with (2^63 - 1)%Z. apply zb_land_mask. lia. Qed.
Lemma land_m48 : forall x, Z.land x 281474976710655 = (x mod 2^48)%Z.
Proof. intros. change 281474976710655%Z with (2^48 - 1)%Z. apply zb_land_mask. lia. Qed.

(* [comment removed for export] *)
Lemma copysign_hi_eq : forall xh yh, (0 <= xh < 2^64)%Z -> (0 <= yh < 2^64)%Z ->
  Z.lor (Z.land (Z.shiftl (Z.lor (Z.land (Z.shiftl (Z.shiftr yh 63) 15) 18446744073709551615)
                                 (Z.shiftr (Z.land (Z.shiftl xh 1) 18446744073709551615) 49)) 48) 18446744073709551615)
        (Z.land xh 281474976710655)
  = Z.lor (Z.land xh 9223372036854775807) (Z.land yh 9223372036854775808).
Proof.
  intros xh yh Hx Hy.
  rewrite !land_W64, land_m48, land_m63, land_bit63 by lia.
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  set (s := (yh / 2^63)%Z). assert (Hs : (0 <= s <= 1)%Z) by (subst s; Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (s * 2^15)) by lia.
  set (b := ((xh * 2 ^ 1) mod 2 ^ 64 / 2 ^ 49)%Z). assert (Hb : (0 <= b < 2^15)%Z) by (subst b; Z.div_mod_to_equations; lia).
  rewrite (Z.lor_comm (s * 2^15) b), lor_low_high by lia.
  rewrite (Z.mod_small ((b + s * 2^15) * 2^48)) by lia.
  rewrite (Z.lor_comm ((b + s * 2^15) * 2^48)), lor_low_high by (try (Z.div_mod_to_equations; lia); lia).
  replace (yh - yh mod 2^63)%Z with (s * 2^63)%Z by (subst s; Z.div_mod_to_equations; lia).
  rewrite lor_low_high by (try (Z.div_mod_to_equations; lia); lia).
  subst b s. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition leafq_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom img_segs)
    /\ munch [] m m /\ wmono img_segs m m /\ mem_inv img_segs m.

Lemma land63_range : forall x, (0 <= x < 2^64)%Z -> (0 <= Z.land x 0x7fffffffffffffff < 2^64)%Z.
Proof. intros x Hx. apply Bytes.land_lt_pow2; lia. Qed.

Lemma fabsl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv img_segs m ->
  evt img_segs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_fabsl X) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FABSL) fc None m (seg_rom img_segs)).
Proof.
  intros until X. intros MI. unfold FABSL.
  pose proof (lo64_range X) as RL. pose proof (hi64_range X) as RH. pose proof (land63_range (hi64 X) ltac:(lia)) as R63.
  zs. zs. zs.
  apply evt_done. unfold leafq_post. repeat (lazymatch goal with |- ex _ => eexists end).
  unfold m_fabsl. rewrite lo64_mk128, hi64_mk128 by lia.
  split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

(* [comment removed for export] *)
Definition fabsl_spec_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
  mem_inv img_segs m ->
  evt img_segs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_fabsl X) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FABSL) fc None m (seg_rom img_segs)).
Lemma fabsl_spec_c_ok : fabsl_spec_c.
Proof. exact fabsl_spec. Qed.


Lemma copysignl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X Y : Z),
  mem_inv img_segs m ->
  evt img_segs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_copysignl X Y) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 COPYSIGNL) fc None m (seg_rom img_segs)).
Proof.
  intros until Y. intros MI. unfold COPYSIGNL.
  pose proof (lo64_range X) as RL. pose proof (hi64_range X) as RH. pose proof (lo64_range Y) as RLY. pose proof (hi64_range Y) as RHY.
  do 9 zs. zs.
  apply evt_done. unfold leafq_post. repeat (lazymatch goal with |- ex _ => eexists end).
  unfold m_copysignl. rewrite copysign_hi_eq by lia.
  assert (R1 : (0 <= Z.lor (Z.land (hi64 X) 9223372036854775807) (Z.land (hi64 Y) 9223372036854775808) < 2^64)%Z).
  { apply Bytes.lor_lt_pow2; apply Bytes.land_lt_pow2; lia. }
  rewrite lo64_mk128, hi64_mk128 by lia.
  split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | hyp].
Qed.

(* [comment removed for export] *)
Definition copysignl_spec_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (X Y : Z),
  mem_inv img_segs m ->
  evt img_segs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_copysignl X Y) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 COPYSIGNL) fc None m (seg_rom img_segs)).
Lemma copysignl_spec_c_ok : copysignl_spec_c.
Proof. exact copysignl_spec. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_m16 : forall x, Z.land x 65535 = (x mod 2^16)%Z.
Proof. intros. change 65535%Z with (2^16 - 1)%Z. apply zb_land_mask. lia. Qed.

(* [comment removed for export] *)
Lemma scal_hi_eq : forall n h, (-2^20 <= n < 2^20)%Z -> (0 <= h < 2^64)%Z ->
  Z_to_bv 64 (Z.lor (Z.land (Z.shiftl (Z.land n 18446744073709551615) 48) 18446744073709551615) (Z.land h 281474976710655) + 4611404543450677248)
  = Z_to_bv 64 (Z.lor (Z.land h 281474976710655) (Z.shiftl (Z.land (16383 + n) 65535) 48)).
Proof.
  intros n h Hn Hh. apply Z_to_bv_eqm.
  rewrite !land_W64, !land_m48, land_m16, !Z.shiftl_mul_pow2 by lia.
  rewrite (Z.lor_comm _ (h mod 2^48)).
  replace ((n mod 2 ^ 64 * 2 ^ 48) mod 2 ^ 64)%Z with ((n mod 2^16) * 2^48)%Z by (Z.div_mod_to_equations; nia).
  rewrite !lor_low_high by (Z.div_mod_to_equations; lia).
  Z.div_mod_to_equations. nia.
Qed.
Definition scal_reduce (x n : Z) : Z * Z :=
  (if 16383 <? n then
    let x := f128_mul x C_2P16383 in let n := n - 16383 in
    if 16383 <? n then
      let x := f128_mul x C_2P16383 in let n := n - 16383 in (x, if 16383 <? n then 16383 else n)
    else (x, n)
  else if n <? -16382 then
    let x := f128_mul x C_2PM16269 in let n := n + (16382 - 113) in
    if n <? -16382 then
      let x := f128_mul x C_2PM16269 in let n := n + (16382 - 113) in (x, if n <? -16382 then -16382 else n)
    else (x, n)
  else (x, n))%Z.
Definition U1 : Z := f128_of_d (bv_unsigned D_ONE).
Definition scal_u (n : Z) : Z :=
  mk128 (Z.lor (Z.land (hi64 U1) 0x0000ffffffffffff) (Z.shiftl (Z.land (0x3fff + n)%Z 0xffff) 48)) (lo64 U1).
Lemma m_scalbnl_eq : forall x n, m_scalbnl x n = f128_mul (fst (scal_reduce x n)) (scal_u (snd (scal_reduce x n))).
Proof.
  intros x n. unfold m_scalbnl, scal_reduce, scal_u, U1.
  destruct (16383 <? n); [destruct (16383 <? n - 16383); reflexivity|].
  destruct (n <? -16382)%Z; [destruct (n + (16382 - 113) <? -16382)%Z; reflexivity|]. reflexivity.
Qed.

Definition scalbnl_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             (bvmap_set 10 D_ONE F) (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(q - 112, q)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (q - 112) q.

Definition scalbnl_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X n : Z),
  stk img_segs m (q - 112) q -> (4096 <= q - 112)%Z -> (q < 2^63)%Z ->
  (-2^31 <= n < 2^31)%Z ->
  mem_inv img_segs m ->
  evt img_segs (scalbnl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_scalbnl X n) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCALBNL) fc None m (seg_rom img_segs)).

Lemma scalbnl_spec : scalbnl_stmt.
Proof.
  unfold scalbnl_stmt. intros until n. intros ST Q0 Q1 Hn MI.
  pose proof (munch_refl [(q - 112, q)]%Z m) as MU. pose proof (wmono_refl img_segs m) as WM.
  pose proof (lo64_range X) as RL. pose proof (hi64_range X) as RH.
  rewrite m_scalbnl_eq. unfold SCALBNL.
  zs. carve_frame 32%nat ST.
  zs. zs. zs. zs. zs. zs.
  (* [comment removed for export] *)
  assert (FIN : forall mf (x1 x10 x11 x12 x13 x14 x15 x16 x17 x5 x6 x7 x28 x29 x30 x31 : word) x' n',
    mem_inv img_segs mf -> munch [(q - 112, q)]%Z m mf -> wmono img_segs m mf ->
    stk img_segs mf (q - 112) (q + -32) ->
    rw_cells img_segs mf (q + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    (-2^20 <= n' < 2^20)%Z ->
    fst (scal_reduce X n) = x' -> snd (scal_reduce X n) = n' ->
    evt img_segs (scalbnl_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_mul (fst (scal_reduce X n)) (scal_u (snd (scal_reduce X n)))) m)
      (MS (mkR x1 (Z_to_bv 64 (q + -32)) gp tp x5 x6 x7 (Z_to_bv 64 n') (Z_to_bv 64 (hi64 x')) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (lo64 x')) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x20548 + 256)) fc None mf (seg_rom img_segs))).
  { clear MU WM MI ST FR. intros mf x1 x10 x11 x12 x13 x14 x15 x16 x17 x5 x6 x7 x28 x29 x30 x31 x' n' MI MU WM ST FR Rn Ex En.
    rewrite Ex, En. pose proof (lo64_range x') as RL'. pose proof (hi64_range x') as RH'.
    zs. zs.
    zs. callw (eapply SPEC_extenddftf2_callv; [hyp | lia]).
    change 4607182418800017408%Z with (bv_unsigned D_ONE). fold U1.
    pose proof (lo64_range U1) as RLU. pose proof (hi64_range U1) as RHU.
    do 10 zs.
    rewrite (scal_hi_eq n' (hi64 U1)) by lia.
    assert (RU : (0 <= Z.lor (Z.land (hi64 U1) 281474976710655) (Z.shiftl (Z.land (16383 + n') 65535) 48) < 2^64)%Z).
    { apply Bytes.lor_lt_pow2; [apply Bytes.land_lt_pow2; lia|]. rewrite Z.shiftl_mul_pow2, land_m16 by lia. Z.div_mod_to_equations. lia. }
    replace (Z_to_bv 64 (lo64 U1)) with (Z_to_bv 64 (lo64 (scal_u n'))) by (unfold scal_u; rewrite lo64_mk128 by lia; reflexivity).
    replace (Z_to_bv 64 (Z.lor (Z.land (hi64 U1) 281474976710655) (Z.shiftl (Z.land (16383 + n') 65535) 48))) with (Z_to_bv 64 (hi64 (scal_u n')))
      by (unfold scal_u; rewrite hi64_mk128 by lia; reflexivity).
    zs. callw (eapply SPEC_multf3_callq; [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
    do 6 zs.
    match goal with H : stk _ _ _ _ |- _ => rename H into ST2 end. replace (q + -32 - 80)%Z with (q - 112)%Z in ST2 by lia.
    release_frame FR ST2 q.
    apply evt_done. unfold scalbnl_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [hyp | exact ST2]. }
  (* [comment removed for export] *)
  Ltac mlia2 := rewrite ?land_W64 in *; Z.div_mod_to_equations; lia.
  Ltac decb := repeat match goal with |- context [Z.ltb ?a ?b] =>
    first [replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; mlia2) | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; mlia2)] end.
  Ltac fin F x n := eapply (F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x n); [hyp | hyp | hyp | hyp | hyp | | unfold scal_reduce; decb; cbn [fst snd]; reflexivity | unfold scal_reduce; decb; cbn [fst snd]; lia]; try mlia2.
  zs. br K1.
  - (* [comment removed for export] *)
    zs. zs. zs. br K2.
    + (* [comment removed for export] *) zs. zs. zs. fin FIN X n.
    + (* [comment removed for export] *)
      zs. zs. zs. zs.
      zs. callw (eapply SPEC_multf3_callq with (X := X) (Y := C_2PM16269); [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
      match goal with H : stk _ _ _ _ |- _ => replace (q + -32 - 80)%Z with (q - 112)%Z in H by lia end.
      set (X1 := f128_mul X C_2PM16269) in *. pose proof (lo64_range X1) as RL1. pose proof (hi64_range X1) as RH1.
      zs. zs. zs. br K3.
      * (* [comment removed for export] *) zs. zs. zs. zs. zs. fin FIN X1 (n + 16269)%Z.
      * zs. zs. zs. callw (eapply SPEC_multf3_callq with (X := X1) (Y := C_2PM16269); [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
        match goal with H : stk _ _ _ _ |- _ => replace (q + -32 - 80)%Z with (q - 112)%Z in H by lia end.
        set (X2 := f128_mul X1 C_2PM16269) in *. pose proof (lo64_range X2) as RL2. pose proof (hi64_range X2) as RH2.
        zs. zs. zs. zs. zs. br K4.
        -- zs. zs. zs. zs. fin FIN X2 (n + 32538)%Z.
        -- zs. zs. zs. zs. zs. eapply (FIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 (-48920 + 32538)%Z); [hyp | hyp | hyp | hyp | hyp | lia | unfold scal_reduce; decb | unfold scal_reduce; decb];
             destruct (Z.ltb_spec0 (n + (16382 - 113) + (16382 - 113)) (-16382)); cbn [fst snd]; first [reflexivity | mlia2].
  - (* [comment removed for export] *)
    zs. zs. zs. zs.
    zs. callw (eapply SPEC_multf3_callq with (X := X) (Y := C_2P16383); [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
    match goal with H : stk _ _ _ _ |- _ => replace (q + -32 - 80)%Z with (q - 112)%Z in H by lia end.
    set (X1 := f128_mul X C_2P16383) in *. pose proof (lo64_range X1) as RL1. pose proof (hi64_range X1) as RH1.
    zs. zs. zs. br K3.
    + (* [comment removed for export] *) zs. zs. zs. zs. zs. zs. fin FIN X1 (n - 16383)%Z.
    + zs. zs. zs. callw (eapply SPEC_multf3_callq with (X := X1) (Y := C_2P16383); [replace (q + -32 - 80)%Z with (q - 112)%Z by lia; hyp | hyp | lia]).
      match goal with H : stk _ _ _ _ |- _ => replace (q + -32 - 80)%Z with (q - 112)%Z in H by lia end.
      set (X2 := f128_mul X1 C_2P16383) in *. pose proof (lo64_range X2) as RL2. pose proof (hi64_range X2) as RH2.
      zs. zs. zs. zs. zs. br K4.
      * zs. zs. zs. zs. fin FIN X2 (n - 32766)%Z.
      * zs. zs. zs. zs. zs. eapply (FIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 (49149 - 32766)%Z); [hyp | hyp | hyp | hyp | hyp | lia | unfold scal_reduce; decb | unfold scal_reduce; decb];
             destruct (Z.ltb_spec0 16383 (n - 16383 - 16383)); cbn [fst snd]; first [reflexivity | mlia2].
Qed.

(* [comment removed for export] *)
Definition scalbnl_spec_c : Prop := scalbnl_stmt.
Lemma scalbnl_spec_c_ok : scalbnl_spec_c.
Proof. exact scalbnl_spec. Qed.


End Img.
(* [comment removed for export] *)
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.

(* [comment removed for export] *)
Existing Class scalbnl_spec_c.
Existing Class fabsl_spec_c.
Existing Class copysignl_spec_c.
