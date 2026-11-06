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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P Require F_sf_helpers2.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P.F_sf_helpers2.SF_buildtac.

(* [comment removed for export] *)
From Stdlib Require Import Zify Lia. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require Import RProgNotJ.

(* [comment removed for export] *)
Definition floatunsitf_prog (B : Z) : RStep.ptree :=
  PNode 116%Z
  (PNode 56%Z
    (PLeaf
        (PJ_Branch_BC_EQ_nnn 0 10 0 172 4
        (PJ_ShiftImm32_ALU_SRL_nnn 4 11 10 1 4
        (PJ_Lui_nn 8 12 349525 4
        (PJ_Lui_nn 12 13 209715 4
        (PJ_Op_ALU_OR_nnn 16 14 10 11 4
        (PJ_OpImm32_nnn 20 12 12 1365 4
        (PJ_ShiftImm32_ALU_SRL_nnn 24 15 14 2 4
        (PJ_Op_ALU_OR_nnn 28 14 14 15 4
        (PJ_ShiftImm32_ALU_SRL_nnn 32 15 14 4 4
        (PJ_Op_ALU_OR_nnn 36 14 14 15 4
        (PJ_ShiftImm32_ALU_SRL_nnn 40 15 14 8 4
        (PJ_Op_ALU_OR_nnn 44 14 14 15 4
        (PJ_ShiftImm32_ALU_SRL_nnn 48 15 14 16 4
        (PJ_Op_ALU_OR_nnn 52 14 14 15 4 nil)))))))))))))))
    (PLeaf
        (PJ_OpImm_ALU_XOR_nnn 56 14 14 4095 4
        (PJ_ShiftImm_ALU_SRL_nnn 60 15 14 1 4
        (PJ_Op_ALU_AND_nnn 64 12 15 12 4
        (PJ_Lui_nn 68 15 61681 4
        (PJ_OpImm32_nnn 72 13 13 819 4
        (PJ_Op_ALU_SUB_nnn 76 14 14 12 4
        (PJ_Op_ALU_AND_nnn 80 12 14 13 4
        (PJ_ShiftImm_ALU_SRL_nnn 84 14 14 2 4
        (PJ_Op_ALU_AND_nnn 88 13 14 13 4
        (PJ_Lui_nn 92 14 4112 4
        (PJ_ShiftImm_ALU_SLL_nnn 96 16 10 32 4
        (PJ_OpImm_ALU_ADD_nnn 100 10 15 3855 4
        (PJ_OpImm_ALU_ADD_nnn 104 14 14 257 4
        (PJ_Op_ALU_ADD_nnn 108 12 12 13 4
        (PJ_ShiftImm_ALU_SRL_nnn 112 13 12 4 4 nil)))))))))))))))))
  (PNode 176%Z
    (PLeaf
        (PJ_Op_ALU_ADD_nnn 116 12 12 13 4
        (PJ_Op_ALU_AND_nnn 120 10 12 10 4
        (PJ_Mul_M_MUL_nnn 124 10 10 14 4
        (PJ_ShiftImm32_ALU_SRL_nnn 128 12 10 24 4
        (PJ_OpImm_ALU_XOR_nnn 132 10 12 31 4
        (PJ_OpImm_ALU_ADD_nnn 136 13 0 112 4
        (PJ_Op32_ALU_SUB_nnn 140 10 13 10 4
        (PJ_ShiftImm_ALU_SLL_nnn 144 15 10 32 4
        (PJ_ShiftImm_ALU_SRL_nnn 148 15 15 32 4
        (PJ_OpImm_ALU_ADD_nnn 152 13 15 4032 4
        (PJ_ShiftImm_ALU_SRL_nnn 156 14 16 32 4
        (PJ_Branch_BC_LT_nnn 160 13 0 20 4
        (PJ_Op_ALU_SLL_nnn 164 11 14 15 4
        (PJ_Jal_nn 168 0 20 4
        (PJ_OpImm_ALU_ADD_nnn 172 11 0 0 4 nil))))))))))))))))
    (PLeaf
        (PJ_Jalr_nnn 176 0 1 0 4
        (PJ_OpImm_ALU_XOR_nnn 180 15 15 4095 4
        (PJ_Op_ALU_SRL_nnn 184 11 11 15 4
        (PJ_Op_ALU_SLL_nnn 188 10 14 10 4
        (PJ_ShiftImm_ALU_SRA_nnn 192 13 13 63 4
        (PJ_OpImm_ALU_ADD_nnn 196 14 0 1 4
        (PJ_Op_ALU_AND_nnn 200 10 13 10 4
        (PJ_Lui_nn 204 13 4 4
        (PJ_ShiftImm_ALU_SLL_nnn 208 14 14 48 4
        (PJ_OpImm_ALU_ADD_nnn 212 13 13 30 4
        (PJ_Op_ALU_XOR_nnn 216 11 11 14 4
        (PJ_Op32_ALU_SUB_nnn 220 13 13 12 4
        (PJ_ShiftImm_ALU_SLL_nnn 224 13 13 48 4
        (PJ_Op_ALU_ADD_nnn 228 11 11 13 4
        (PJ_Jalr_nnn 232 0 1 0 4 nil))))))))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_floatunsitf (IMG : RImg) := floatunsitf_prog (sym 0x1c51c).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_floatunsitf : CodeAtT img_segs (sym 0x1c51c) (PROGAT_CODE_floatunsitf IMG)}.
  Context {RB_floatunsitf : RelCode (sym 0x1c51c) 236}.
  Collection ImgHyps := IMG CODE_floatunsitf RB_floatunsitf.


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

Definition floatunsitf_entry := (sym 0x1c51c)%Z.

Definition floatunsitf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'.

(* [comment removed for export] *)
Local Ltac unsitf_tail nM64 clz :=
  zstep; zstep; rewrite (srai63_word nM64) by lia; decide_tests_b;
  do 7 zstep; rewrite Z_to_bv_swrap32; rewrite (sext32_land64 (16414 - clz));
  name_as_by expW (sext32 (16414 - clz)) (apply sext32_range);
  do 3 zstep.


(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

Lemma floatunsitf_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (u : Z),
  mem_inv img_segs m ->
  bv_unsigned a0 = sext32 u ->
  evt img_segs (floatunsitf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 u) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c51c)) fc None m (seg_rom img_segs)).
Proof.
  intros until u. intros MI U.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  assert (Ra0 : (0 <= bv_unsigned a0 < 2^64)%Z) by apply (zr_word a0).
  unfold f128_of_u32. rewrite <- U.
  cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lo64 hi64 wrap64 b2z ONES64 IMPLICIT_HI]. zb_fold_lits.
  zstep. if_cases K0; zify_cond K0; decide_test1 ((bv_unsigned a0) =? 0%Z)%Z.
  - (* [comment removed for export] *) zstep. zstep. sf_finish.
  - (* [comment removed for export] *)
    wstep. model_reg_w 11%Z half (srliw (bv_unsigned a0) 1).
    do 3 wstep. model_reg 14%Z x1 (Z.lor (bv_unsigned a0) half).
    do 3 wstep. model_reg_w 14%Z x2 (Z.lor x1 (srliw x1 2)).
    do 2 wstep. model_reg_w 14%Z x3 (Z.lor x2 (srliw x2 4)).
    do 2 wstep. model_reg_w 14%Z x4 (Z.lor x3 (srliw x3 8)).
    do 2 wstep. model_reg_w 14%Z x5 (Z.lor x4 (srliw x4 16)).
    wstep. model_reg 14%Z y (Z.lxor x5 W64).
    do 5 wstep. model_reg 14%Z c1 (Z.land (y - Z.land (Z.shiftr y 1) 1431655765) W64).
    do 8 wstep. model_reg 12%Z c2 (Z.land (Z.land c1 858993459 + Z.land (Z.shiftr c1 2) 858993459) W64).
    do 3 wstep. model_reg 10%Z c3 (Z.land (Z.land (c2 + Z.shiftr c2 4) W64) 252645135).
    do 2 wstep. model_reg_w 12%Z c4 (srliw (Z.land (c3 * 16843009) W64) 24).
    replace (Z_to_bv 64 c4) with (Z_to_bv 64 (clz32_mirror (bv_unsigned a0))) by (f_equal; model_eval; reflexivity).
    name_as_by clz (clz32_mirror (bv_unsigned a0)) (apply clz32_mirror_range).
    (* [comment removed for export] *)
    zstep. model_reg 10%Z e (Z.lxor clz 31).
    zstep. zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (112 - e)).
    name_as_by shW (sext32 (112 - e)) (apply sext32_range).
    zstep. zstep. replace (Z_to_bv 64 (Z.land shW 4294967295)) with (Z_to_bv 64 (zext32 shW)) by reflexivity.
    name_as_by n (zext32 shW) (rewrite zext32_eq; pose proof (Z.mod_pos_bound shW 4294967296 ltac:(lia)); lia).
    zstep. model_reg 13%Z nM64 (Z.land (n - 64) W64).
    zstep. replace (Z_to_bv 64 (Z.land (bv_unsigned a0) 4294967295)) with (Z_to_bv 64 (zext32 (bv_unsigned a0))) by reflexivity.
    name_as_by aZ (zext32 (bv_unsigned a0)) (rewrite zext32_eq; pose proof (Z.mod_pos_bound (bv_unsigned a0) 4294967296 ltac:(lia)); lia).
    zstep. if_cases K1; zify_cond K1; decide_test1 ((nM64 ≫ 63)%Z =? 0%Z)%Z.
    + (* [comment removed for export] *)
      zstep. zstep.
      name_as_by hi0 (Z.shiftr half (Z.land (Z.lxor n W64) 63))
        (change (inr64 (Z.shiftr half (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      unsitf_tail nM64 clz. sf_finish.
    + (* [comment removed for export] *)
      zstep. zstep.
      unsitf_tail nM64 clz. sf_finish.
Qed.

(* [comment removed for export] *)
Definition floatunsitf_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (u : Z),
  mem_inv img_segs m ->
  bv_unsigned a0 = sext32 u ->
  evt img_segs (floatunsitf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 u) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c51c)) fc None m (seg_rom img_segs)).
Lemma floatunsitf_contract_ok : floatunsitf_contract.
Proof. exact floatunsitf_spec. Qed.


End Img.
(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

(* [comment removed for export] *)
Existing Class floatunsitf_contract.
