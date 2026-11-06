(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgNot.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_sf_helpers2.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgNotJ.
Module G_extenddftf2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac. Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgNot.   
Import ListNotations.
Open Scope bv_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_sf_helpers2.SF_buildtac.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia. Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgNotJ.

(* [comment removed for export] *)
Definition extenddftf2_prog (B : Z) : RStep.ptree :=
  PNode 200%Z
  (PNode 100%Z
    (PNode 48%Z
      (PLeaf
          (PJ_Fmv_FMV_X_F_FMT_D_nn 0 11 10 4
          (PJ_ShiftImm_ALU_SLL_nnn 4 12 11 1 4
          (PJ_ShiftImm_ALU_SRL_nnn 8 12 12 53 4
          (PJ_ShiftImm_ALU_SLL_nnn 12 10 11 12 4
          (PJ_ShiftImm_ALU_SRL_nnn 16 10 10 12 4
          (PJ_Branch_BC_EQ_nnn 20 12 0 52 4
          (PJ_OpImm_ALU_ADD_nnn 24 13 0 2047 4
          (PJ_Branch_BC_NE_nnn 28 12 13 240 4
          (PJ_ShiftImm_ALU_SRL_nnn 32 13 10 4 4
          (PJ_ShiftImm_ALU_SLL_nnn 36 10 10 60 4
          (PJ_Lui_nn 40 12 8 4
          (PJ_OpImm_ALU_ADD_nnn 44 12 12 4095 4 nil)))))))))))))
      (PLeaf
          (PJ_ShiftImm_ALU_SRL_nnn 48 11 11 63 4
          (PJ_ShiftImm_ALU_SLL_nnn 52 12 12 48 4
          (PJ_ShiftImm_ALU_SLL_nnn 56 11 11 63 4
          (PJ_Op_ALU_OR_nnn 60 12 12 13 4
          (PJ_Op_ALU_OR_nnn 64 11 12 11 4
          (PJ_Jalr_nnn 68 0 1 0 4
          (PJ_Branch_BC_EQ_nnn 72 10 0 240 4
          (PJ_ShiftImm_ALU_SRL_nnn 76 12 10 1 4
          (PJ_Lui_nn 80 13 349525 4
          (PJ_Lui_nn 84 14 209715 4
          (PJ_Lui_nn 88 15 61681 4
          (PJ_Lui_nn 92 16 4112 4
          (PJ_Op_ALU_OR_nnn 96 17 10 12 4 nil)))))))))))))))
    (PNode 148%Z
      (PLeaf
          (PJ_OpImm32_nnn 100 13 13 1365 4
          (PJ_OpImm32_nnn 104 14 14 819 4
          (PJ_OpImm32_nnn 108 15 15 3855 4
          (PJ_OpImm32_nnn 112 16 16 257 4
          (PJ_ShiftImm_ALU_SRL_nnn 116 5 17 2 4
          (PJ_Op_ALU_OR_nnn 120 17 17 5 4
          (PJ_ShiftImm_ALU_SLL_nnn 124 5 13 32 4
          (PJ_Op_ALU_ADD_nnn 128 13 13 5 4
          (PJ_ShiftImm_ALU_SLL_nnn 132 5 14 32 4
          (PJ_Op_ALU_ADD_nnn 136 14 14 5 4
          (PJ_ShiftImm_ALU_SLL_nnn 140 5 15 32 4
          (PJ_Op_ALU_ADD_nnn 144 15 15 5 4 nil)))))))))))))
      (PLeaf
          (PJ_ShiftImm_ALU_SLL_nnn 148 5 16 32 4
          (PJ_Op_ALU_ADD_nnn 152 16 16 5 4
          (PJ_ShiftImm_ALU_SRL_nnn 156 5 17 4 4
          (PJ_Op_ALU_OR_nnn 160 17 17 5 4
          (PJ_ShiftImm_ALU_SRL_nnn 164 5 17 8 4
          (PJ_Op_ALU_OR_nnn 168 17 17 5 4
          (PJ_ShiftImm_ALU_SRL_nnn 172 5 17 16 4
          (PJ_Op_ALU_OR_nnn 176 17 17 5 4
          (PJ_ShiftImm_ALU_SRL_nnn 180 5 17 32 4
          (PJ_Op_ALU_OR_nnn 184 17 17 5 4
          (PJ_OpImm_ALU_XOR_nnn 188 17 17 4095 4
          (PJ_ShiftImm_ALU_SRL_nnn 192 5 17 1 4
          (PJ_Op_ALU_AND_nnn 196 13 5 13 4 nil))))))))))))))))
  (PNode 300%Z
    (PNode 248%Z
      (PLeaf
          (PJ_Op_ALU_SUB_nnn 200 13 17 13 4
          (PJ_Op_ALU_AND_nnn 204 17 13 14 4
          (PJ_ShiftImm_ALU_SRL_nnn 208 13 13 2 4
          (PJ_Op_ALU_AND_nnn 212 13 13 14 4
          (PJ_Op_ALU_ADD_nnn 216 13 17 13 4
          (PJ_ShiftImm_ALU_SRL_nnn 220 14 13 4 4
          (PJ_Op_ALU_ADD_nnn 224 13 13 14 4
          (PJ_Lui_nn 228 14 4 4
          (PJ_Op_ALU_AND_nnn 232 13 13 15 4
          (PJ_Mul_M_MUL_nnn 236 13 13 16 4
          (PJ_ShiftImm_ALU_SRL_nnn 240 13 13 56 4
          (PJ_OpImm_ALU_ADD_nnn 244 14 14 3084 4 nil)))))))))))))
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 248 16 13 4081 4
          (PJ_OpImm_ALU_ADD_nnn 252 15 13 49 4
          (PJ_Branch_BC_LT_nnn 256 16 0 80 4
          (PJ_Op_ALU_SLL_nnn 260 17 10 16 4
          (PJ_Jal_nn 264 0 84 4
          (PJ_OpImm_ALU_ADD_nnn 268 13 0 15 4
          (PJ_ShiftImm_ALU_SLL_nnn 272 13 13 10 4
          (PJ_Op_ALU_ADD_nnn 276 12 12 13 4
          (PJ_ShiftImm_ALU_SRL_nnn 280 13 10 4 4
          (PJ_ShiftImm_ALU_SLL_nnn 284 10 10 60 4
          (PJ_ShiftImm_ALU_SRL_nnn 288 11 11 63 4
          (PJ_ShiftImm_ALU_SLL_nnn 292 12 12 48 4
          (PJ_ShiftImm_ALU_SLL_nnn 296 11 11 63 4 nil)))))))))))))))
    (PNode 348%Z
      (PLeaf
          (PJ_Op_ALU_OR_nnn 300 12 12 13 4
          (PJ_Op_ALU_OR_nnn 304 11 12 11 4
          (PJ_Jalr_nnn 308 0 1 0 4
          (PJ_ShiftImm_ALU_SRL_nnn 312 11 11 63 4
          (PJ_ShiftImm_ALU_SLL_nnn 316 12 0 48 4
          (PJ_ShiftImm_ALU_SLL_nnn 320 11 11 63 4
          (PJ_Op_ALU_OR_nnn 324 12 12 0 4
          (PJ_Op_ALU_OR_nnn 328 11 12 11 4
          (PJ_Jalr_nnn 332 0 1 0 4
          (PJ_OpImm_ALU_ADD_nnn 336 17 0 14 4
          (PJ_Op32_ALU_SUB_nnn 340 17 17 13 4
          (PJ_Op_ALU_SRL_nnn 344 17 12 17 4 nil)))))))))))))
      (PLeaf
          (PJ_Op_ALU_SUB_nnn 348 12 14 13 4
          (PJ_ShiftImm_ALU_SRA_nnn 352 13 16 63 4
          (PJ_Op_ALU_SLL_nnn 356 10 10 15 4
          (PJ_OpImm_ALU_ADD_nnn 360 14 0 1 4
          (PJ_Op_ALU_AND_nnn 364 10 13 10 4
          (PJ_ShiftImm_ALU_SLL_nnn 368 14 14 48 4
          (PJ_Op_ALU_XOR_nnn 372 13 17 14 4
          (PJ_ShiftImm_ALU_SRL_nnn 376 11 11 63 4
          (PJ_ShiftImm_ALU_SLL_nnn 380 12 12 48 4
          (PJ_ShiftImm_ALU_SLL_nnn 384 11 11 63 4
          (PJ_Op_ALU_OR_nnn 388 12 12 13 4
          (PJ_Op_ALU_OR_nnn 392 11 12 11 4
          (PJ_Jalr_nnn 396 0 1 0 4 nil)))))))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_extenddftf2 (IMG : RImg) := extenddftf2_prog (sym 0x1af98).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_extenddftf2 : CodeAtT img_segs (sym 0x1af98) (PROGAT_CODE_extenddftf2 IMG)}.
  Context {RB_extenddftf2 : RelCode (sym 0x1af98) 400}.
  Collection ImgHyps := IMG CODE_extenddftf2 RB_extenddftf2.


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

Definition extenddftf2_entry := (sym 0x1af98)%Z.

Definition extenddftf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'.

(* [comment removed for export] *)
Local Ltac extend_tail shM64 :=
  zstep; zstep; rewrite (srai63_word shM64) by lia; decide_tests_b;
  do 11 zstep.


(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

Lemma extenddftf2_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (extenddftf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (f128_of_d (bv_unsigned (reg_get F 10))) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1af98)) fc None m (seg_rom img_segs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  unfold f128_of_d.
  cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lo64 hi64 wrap64 b2z ONES64 IMPLICIT_HI INF_HI]. zb_fold_lits.
  zstep. remember (reg_get F 10) as dw eqn:Edw.
  assert (Rdw : (0 <= bv_unsigned dw < 2^64)%Z) by apply (zr_word dw).
  rewrite (land_W64_small (bv_unsigned dw)) by lia.
  do 4 zstep. name_reg 12%Z aExp. name_reg 10%Z aSig.
  zstep. if_cases K0; zify_cond K0; decide_test1_try (aExp =? 0%Z)%Z; decide_test1_try (aExp =? 2047%Z)%Z.
  - (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2; decide_test1 (aSig =? 0%Z)%Z.
    + (* [comment removed for export] *) do 6 zstep. sf_finish.
    + (* [comment removed for export] *)
      zstep. model_reg 12%Z half (Z.shiftr aSig 1).
      do 5 zstep. model_reg 17%Z x1 (Z.lor aSig half).
      do 6 zstep. model_reg 17%Z x2 (Z.lor x1 (Z.shiftr x1 2)).
      do 10 zstep. model_reg 17%Z x3 (Z.lor x2 (Z.shiftr x2 4)).
      do 2 zstep. model_reg 17%Z x4 (Z.lor x3 (Z.shiftr x3 8)).
      do 2 zstep. model_reg 17%Z x5 (Z.lor x4 (Z.shiftr x4 16)).
      do 2 zstep. model_reg 17%Z x6 (Z.lor x5 (Z.shiftr x5 32)).
      zstep. model_reg 17%Z y (Z.lxor x6 W64).
      do 3 zstep. model_reg 13%Z c1 (Z.land (y - Z.land (Z.shiftr y 1) 6148914691236517205) W64).
      do 4 zstep. model_reg 13%Z c2 (Z.land (Z.land c1 3689348814741910323 + Z.land (Z.shiftr c1 2) 3689348814741910323) W64).
      do 4 zstep. model_reg 13%Z c3 (Z.land (Z.land (c2 + Z.shiftr c2 4) W64) 1085102592571150095).
      do 2 zstep. model_reg 13%Z c4 (Z.shiftr (Z.land (c3 * 72340172838076673) W64) 56).
      replace (Z_to_bv 64 c4) with (Z_to_bv 64 (clz64_mirror aSig)) by (f_equal; model_eval; reflexivity).
      name_as_by clz (clz64_mirror aSig) (apply clz64_mirror_range).
      zstep. zstep. model_reg 16%Z shM64 (Z.land (clz - 15) W64).
      zstep. model_reg 15%Z sh (Z.land (clz + 49) W64).
      zstep. if_cases K3; zify_cond K3; decide_test1 ((shM64 ≫ 63)%Z =? 0%Z)%Z.
      * (* [comment removed for export] *)
        zstep. zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (14 - clz)).
        name_as_by t14 (sext32 (14 - clz)) (apply sext32_range).
        zstep. name_as_by hi0 (Z.shiftr half (Z.land t14 63))
          (change (inr64 (Z.shiftr half (Z.land t14 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
        extend_tail shM64. sf_finish.
      * (* [comment removed for export] *)
        zstep. zstep.
        extend_tail shM64. sf_finish.
  - (* [comment removed for export] *)
    zstep. zstep. if_cases K1; zify_cond K1; decide_test1 (aExp =? 2047%Z)%Z.
    + (* [comment removed for export] *) do 11 zstep. sf_finish.
    + (* [comment removed for export] *) do 10 zstep. sf_finish.
Qed.

(* [comment removed for export] *)
Definition extenddftf2_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (extenddftf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (f128_of_d (bv_unsigned (reg_get F 10))) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1af98)) fc None m (seg_rom img_segs)).
Lemma extenddftf2_contract_ok : extenddftf2_contract.
Proof. exact extenddftf2_spec. Qed.


End Img.
(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

(* [comment removed for export] *)
Existing Class extenddftf2_contract.
End G_extenddftf2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset.
Import G_extenddftf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import GRoTab. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition pop_arg_prog (B K_10984 B_extenddftf2 : Z) : RStep.ptree :=
  PNode 152%Z
  (PNode 76%Z
    (PNode 36%Z
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 0 11 11 4087 4
          (PJ_OpImm_ALU_ADD_nnn 4 13 0 17 4
          (PJ_Branch_BC_LTU_nnn 8 13 11 248 4
          (PJ_ShiftImm_ALU_SLL_nnn 12 11 11 2 4
          (PJ_Auipc_nt 16 13 (hi20 (K_10984 - (B + 16))) 4
          (PJ_OpImm_ALU_ADD_nnt 20 13 13 (lo12 (K_10984 - (B + 16))) 4
          (PJ_Op_ALU_ADD_nnn 24 11 11 13 4
          (PJ_Load_SZ4_true_nnn 28 11 11 0 4
          (PJ_Op_ALU_ADD_nnn 32 11 11 13 4 nil))))))))))
      (PLeaf
          (PJ_Jalr_nnn 36 0 11 0 4
          (PJ_Load_SZ8_true_nnn 40 11 12 0 4
          (PJ_OpImm_ALU_ADD_nnn 44 13 11 8 4
          (PJ_Store_SZ8_nnn 48 12 13 0 4
          (PJ_Load_SZ8_true_nnn 52 11 11 0 4
          (PJ_Store_SZ8_nnn 56 10 11 0 4
          (PJ_Jalr_nnn 60 0 1 0 4
          (PJ_OpImm_ALU_ADD_nnn 64 2 2 4080 4
          (PJ_Store_SZ8_nnn 68 2 1 8 4
          (PJ_Store_SZ8_nnn 72 2 8 0 4 nil))))))))))))
    (PNode 112%Z
      (PLeaf
          (PJ_Load_SZ8_true_nnn 76 11 12 0 4
          (PJ_OpImm_ALU_ADD_nnn 80 13 11 8 4
          (PJ_Store_SZ8_nnn 84 12 13 0 4
          (PJ_FLoad_FMT_D_nnn 88 10 11 0 4
          (PJ_OpImm_ALU_ADD_nnn 92 8 10 0 4
          (PJ_Jal_nt 96 1 (jimm21 (B_extenddftf2 - (B + 96))) 4
          (PJ_Store_SZ8_nnn 100 8 10 0 4
          (PJ_Store_SZ8_nnn 104 8 11 8 4
          (PJ_Load_SZ8_true_nnn 108 1 2 8 4 nil))))))))))
      (PLeaf
          (PJ_Load_SZ8_true_nnn 112 8 2 0 4
          (PJ_OpImm_ALU_ADD_nnn 116 2 2 16 4
          (PJ_Jalr_nnn 120 0 1 0 4
          (PJ_Load_SZ8_true_nnn 124 11 12 0 4
          (PJ_OpImm_ALU_ADD_nnn 128 13 11 8 4
          (PJ_Store_SZ8_nnn 132 12 13 0 4
          (PJ_Load_SZ1_true_nnn 136 11 11 0 4
          (PJ_Store_SZ8_nnn 140 10 11 0 4
          (PJ_Jalr_nnn 144 0 1 0 4
          (PJ_Load_SZ8_true_nnn 148 11 12 0 4 nil)))))))))))))
  (PNode 228%Z
    (PNode 188%Z
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 152 13 11 8 4
          (PJ_Store_SZ8_nnn 156 12 13 0 4
          (PJ_Load_SZ4_false_nnn 160 11 11 0 4
          (PJ_Store_SZ8_nnn 164 10 11 0 4
          (PJ_Jalr_nnn 168 0 1 0 4
          (PJ_Load_SZ8_true_nnn 172 11 12 0 4
          (PJ_OpImm_ALU_ADD_nnn 176 13 11 8 4
          (PJ_Store_SZ8_nnn 180 12 13 0 4
          (PJ_Load_SZ2_true_nnn 184 11 11 0 4 nil))))))))))
      (PLeaf
          (PJ_Store_SZ8_nnn 188 10 11 0 4
          (PJ_Jalr_nnn 192 0 1 0 4
          (PJ_Load_SZ8_true_nnn 196 11 12 0 4
          (PJ_OpImm_ALU_ADD_nnn 200 13 11 8 4
          (PJ_Store_SZ8_nnn 204 12 13 0 4
          (PJ_Load_SZ1_false_nnn 208 11 11 0 4
          (PJ_Store_SZ8_nnn 212 10 11 0 4
          (PJ_Jalr_nnn 216 0 1 0 4
          (PJ_Load_SZ8_true_nnn 220 11 12 0 4
          (PJ_OpImm_ALU_ADD_nnn 224 11 11 15 4 nil))))))))))))
    (PNode 268%Z
      (PLeaf
          (PJ_OpImm_ALU_AND_nnn 228 11 11 4080 4
          (PJ_OpImm_ALU_ADD_nnn 232 13 11 16 4
          (PJ_Store_SZ8_nnn 236 12 13 0 4
          (PJ_Load_SZ8_true_nnn 240 12 11 0 4
          (PJ_Load_SZ8_true_nnn 244 11 11 8 4
          (PJ_Store_SZ8_nnn 248 10 12 0 4
          (PJ_Store_SZ8_nnn 252 10 11 8 4
          (PJ_Jalr_nnn 256 0 1 0 4
          (PJ_Load_SZ8_true_nnn 260 11 12 0 4
          (PJ_OpImm_ALU_ADD_nnn 264 13 11 8 4 nil)))))))))))
      (PLeaf
          (PJ_Store_SZ8_nnn 268 12 13 0 4
          (PJ_Load_SZ2_false_nnn 272 11 11 0 4
          (PJ_Store_SZ8_nnn 276 10 11 0 4
          (PJ_Jalr_nnn 280 0 1 0 4
          (PJ_Load_SZ8_true_nnn 284 11 12 0 4
          (PJ_OpImm_ALU_ADD_nnn 288 13 11 8 4
          (PJ_Store_SZ8_nnn 292 12 13 0 4
          (PJ_Load_SZ4_true_nnn 296 11 11 0 4
          (PJ_Store_SZ8_nnn 300 10 11 0 4
          (PJ_Jalr_nnn 304 0 1 0 4 nil))))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m. (* [comment removed for export] *) Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mem_after_store ::= mem_after_store_cached. Local Ltac addr_eq_tac ::= addr_eq_tac_cached. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM. Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_pop_arg (IMG : RImg) := pop_arg_prog (sym 0x19534) (sym 0x10984) (sym 0x1af98).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_pop_arg : CodeAtT img_segs (sym 0x19534) (PROGAT_CODE_pop_arg IMG)}.
  Context {RB_pop_arg : RelCode (sym 0x19534) 308}.
  Context {RO_10984 : RoB img_segs (sym 0x10984) ROT_0x10984}.
  Context {RN_B_extenddftf2_19534 : RelNear (sym 0x19534) (sym 0x1af98)}.
  Context {RS_K_10984 : RelSym (sym 0x10984)}.
  Context {SPEC_extenddftf2 : extenddftf2_contract}.
  Collection ImgHyps := IMG CODE_pop_arg RB_pop_arg RO_10984 RN_B_extenddftf2_19534 RS_K_10984 SPEC_extenddftf2.




Definition pop_arg_entry := (sym 0x19534)%Z.
Definition T_PTR := 9%Z. Definition T_INT := 10%Z. Definition T_UINT := 11%Z. Definition T_DBL := 25%Z.

(* [comment removed for export] *)
Definition va_area (m : word -> option byte) (VA : Z) (slots : list word) : Prop :=
  bytes_at img_segs m VA (u64s slots).

(* [comment removed for export] *)
Definition pop_arg_lo (ty : Z) (slot : word) : word :=
  if (ty =? T_PTR)%Z then slot
  else if (ty =? T_INT)%Z then sx32 slot
  else if (ty =? T_UINT)%Z then zx32 slot
  else Z_to_bv 64 (lo64 (f128_of_d (bv_unsigned slot))).
Definition pop_arg_hi (ty : Z) (slot y : word) : word :=
  if (ty =? T_DBL)%Z then Z_to_bv 64 (hi64 (f128_of_d (bv_unsigned slot))) else y.

Definition pop_arg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ARG AP VA : Z) (slots : list word) (i ty : Z) (slot y : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - 16) (bv_unsigned sp)
    /\ rw_cells img_segs m' AP [C8 (Z_to_bv 64 (VA + 8 * (i + 1)))]
    /\ rw_cells img_segs m' ARG [C8 (pop_arg_lo ty slot); C8 (pop_arg_hi ty slot y)]
    /\ va_area m' VA slots
    /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k).

Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Lemma va_read8 : forall m VA slots (i : Z) w a,
  bytes_at img_segs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes img_segs m a 8 = Some (le8 w).
Proof.
  intros m VA slots i w a Hb Hn Hi ->.
  (nelim (u64s_split _ _ _ Hn) 6%nat; intros pre post E Hlen Eu Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read img_segs m VA (u64s slots) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma va_read4 : forall m VA slots (i : Z) w a,
  bytes_at img_segs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes img_segs m a 4 = Some (le4 w).
Proof.
  intros m VA slots i w a Hb Hn Hi ->.
  (nelim (u64s_split _ _ _ Hn) 6%nat; intros pre post E Hlen Eu Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read img_segs m VA (u64s slots) (8 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app. rewrite length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r.
  rewrite firstn4_le8. reflexivity.
Qed.

Lemma va_area_bound : forall m VA slots, va_area m VA slots -> (0 <= VA /\ VA + 8 * Z.of_nat (length slots) <= 2^64)%Z.
Proof. intros m VA slots H. pose proof (bytes_at_bound _ _ _ _ H) as B. rewrite u64s_length in B. lia. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

Lemma pop_arg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (VA : Z) (slots : list word) (i ty : Z) (slot x y : word),
  rw_cells img_segs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
  va_area m VA slots -> nth_error slots (Z.to_nat i) = Some slot -> (0 <= i)%Z ->
  rw_cells img_segs m (bv_unsigned a0) [C8 x; C8 y] ->
  stk img_segs m (bv_unsigned sp - 16) (bv_unsigned sp) ->
  mem_inv img_segs m ->
  a1 = Z_to_bv 64 ty -> (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL) ->
  (16 <= bv_unsigned sp)%Z ->
  (bv_unsigned sp <= bv_unsigned a2)%Z -> (bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned a2)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= VA)%Z ->
  evt img_segs (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) (bv_unsigned a2) VA slots i ty slot y m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x19534)) fc None m (seg_rom img_segs)).
Proof.
  intros until y. intros APC VAA NTH Hi ARGC ST MI -> TY SPLO A2 A0 SEP1 SEP2 SEP3 SEP4.
  pose_word_ranges.
  pose proof (va_area_bound _ _ _ VAA) as VB. unfold va_area in VAA.
  assert (IL : (Z.to_nat i < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
  set (AP := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 AP) by (unfold AP; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (ARG := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 ARG) by (unfold ARG; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  destruct TY as [-> | [-> | [-> | ->]]]; unfold T_PTR, T_INT, T_UINT, T_DBL.
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { intros k Hk. reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { intros k Hk. reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { intros k Hk. reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    carve_frame 16%nat ST.
    zstep. zstep. zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep.
    zstep. call SPEC_extenddftf2. 1:{ exact MI. }
    idtac. idtac .
    rewrite freg_get_same by reflexivity.
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    release_frame FR ST (bv_unsigned sp).
    finish.
    { intros k Hk. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq. change (bv_unsigned 10) with 10%Z. lia. }
Qed.

(* [comment removed for export] *)
Definition pop_arg_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (VA : Z) (slots : list word) (i ty : Z) (slot x y : word),
  rw_cells img_segs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
  va_area m VA slots -> nth_error slots (Z.to_nat i) = Some slot -> (0 <= i)%Z ->
  rw_cells img_segs m (bv_unsigned a0) [C8 x; C8 y] ->
  stk img_segs m (bv_unsigned sp - 16) (bv_unsigned sp) ->
  mem_inv img_segs m ->
  a1 = Z_to_bv 64 ty -> (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL) ->
  (16 <= bv_unsigned sp)%Z ->
  (bv_unsigned sp <= bv_unsigned a2)%Z -> (bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned a2)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= VA)%Z ->
  evt img_segs (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) (bv_unsigned a2) VA slots i ty slot y m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x19534)) fc None m (seg_rom img_segs)).
Lemma pop_arg_contract_ok : pop_arg_contract.
Proof. exact pop_arg_spec. Qed.


End Img.
(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Existing Class pop_arg_contract.
