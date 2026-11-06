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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require F_sf_helpers2.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_sf_helpers2.SF_buildtac.

(* [comment removed for export] *)
From Stdlib Require Import Zify Lia. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RProgNotJ.

(* [comment removed for export] *)
Definition floatsitf_prog (B : Z) : RStep.ptree :=
  PNode 132%Z
  (PNode 64%Z
    (PLeaf
        (PJ_Branch_BC_EQ_nnn 0 10 0 196 4
        (PJ_ShiftImm32_ALU_SRA_nnn 4 11 10 31 4
        (PJ_Lui_nn 8 12 524288 4
        (PJ_Lui_nn 12 13 349525 4
        (PJ_Lui_nn 16 14 209715 4
        (PJ_Op_ALU_XOR_nnn 20 15 10 11 4
        (PJ_Op_ALU_AND_nnn 24 12 10 12 4
        (PJ_OpImm32_nnn 28 13 13 1365 4
        (PJ_Op32_ALU_SUB_nnn 32 15 15 11 4
        (PJ_ShiftImm32_ALU_SRL_nnn 36 10 15 1 4
        (PJ_Op_ALU_OR_nnn 40 11 15 10 4
        (PJ_ShiftImm32_ALU_SRL_nnn 44 16 11 2 4
        (PJ_Op_ALU_OR_nnn 48 11 11 16 4
        (PJ_ShiftImm32_ALU_SRL_nnn 52 16 11 4 4
        (PJ_Op_ALU_OR_nnn 56 11 11 16 4
        (PJ_ShiftImm32_ALU_SRL_nnn 60 16 11 8 4 nil)))))))))))))))))
    (PNode 96%Z
      (PLeaf
          (PJ_Op_ALU_OR_nnn 64 11 11 16 4
          (PJ_ShiftImm32_ALU_SRL_nnn 68 16 11 16 4
          (PJ_Op_ALU_OR_nnn 72 11 11 16 4
          (PJ_OpImm_ALU_XOR_nnn 76 11 11 4095 4
          (PJ_ShiftImm_ALU_SRL_nnn 80 16 11 1 4
          (PJ_Op_ALU_AND_nnn 84 13 16 13 4
          (PJ_Lui_nn 88 16 61681 4
          (PJ_OpImm32_nnn 92 14 14 819 4 nil)))))))))
      (PLeaf
          (PJ_Op_ALU_SUB_nnn 96 11 11 13 4
          (PJ_Op_ALU_AND_nnn 100 13 11 14 4
          (PJ_ShiftImm_ALU_SRL_nnn 104 11 11 2 4
          (PJ_Op_ALU_AND_nnn 108 11 11 14 4
          (PJ_Lui_nn 112 14 4112 4
          (PJ_Op_ALU_ADD_nnn 116 11 13 11 4
          (PJ_ShiftImm_ALU_SRL_nnn 120 13 11 4 4
          (PJ_Op_ALU_ADD_nnn 124 13 11 13 4
          (PJ_OpImm_ALU_ADD_nnn 128 17 0 112 4 nil))))))))))))
  (PNode 196%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 132 16 16 3855 4
        (PJ_OpImm_ALU_ADD_nnn 136 14 14 257 4
        (PJ_ShiftImm_ALU_SLL_nnn 140 11 12 32 4
        (PJ_Op_ALU_AND_nnn 144 12 13 16 4
        (PJ_Mul_M_MUL_nnn 148 12 12 14 4
        (PJ_ShiftImm32_ALU_SRL_nnn 152 12 12 24 4
        (PJ_OpImm_ALU_XOR_nnn 156 13 12 31 4
        (PJ_Op32_ALU_SUB_nnn 160 13 17 13 4
        (PJ_ShiftImm_ALU_SLL_nnn 164 16 15 32 4
        (PJ_ShiftImm_ALU_SLL_nnn 168 14 13 32 4
        (PJ_ShiftImm_ALU_SRL_nnn 172 14 14 32 4
        (PJ_OpImm_ALU_ADD_nnn 176 15 14 4032 4
        (PJ_ShiftImm_ALU_SRL_nnn 180 16 16 32 4
        (PJ_Branch_BC_LT_nnn 184 15 0 20 4
        (PJ_Op_ALU_SLL_nnn 188 14 16 14 4
        (PJ_Jal_nn 192 0 20 4 nil)))))))))))))))))
    (PNode 228%Z
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 196 11 0 0 4
          (PJ_Jalr_nnn 200 0 1 0 4
          (PJ_OpImm_ALU_XOR_nnn 204 14 14 4095 4
          (PJ_Op_ALU_SRL_nnn 208 14 10 14 4
          (PJ_Op_ALU_SLL_nnn 212 10 16 13 4
          (PJ_ShiftImm_ALU_SRA_nnn 216 15 15 63 4
          (PJ_OpImm_ALU_ADD_nnn 220 13 0 1 4
          (PJ_Op_ALU_AND_nnn 224 10 15 10 4 nil)))))))))
      (PLeaf
          (PJ_Lui_nn 228 15 4 4
          (PJ_ShiftImm_ALU_SLL_nnn 232 13 13 48 4
          (PJ_OpImm_ALU_ADD_nnn 236 15 15 30 4
          (PJ_Op_ALU_XOR_nnn 240 13 14 13 4
          (PJ_Op32_ALU_SUB_nnn 244 15 15 12 4
          (PJ_ShiftImm_ALU_SLL_nnn 248 15 15 48 4
          (PJ_Op_ALU_ADD_nnn 252 13 13 15 4
          (PJ_Op_ALU_OR_nnn 256 11 13 11 4
          (PJ_Jalr_nnn 260 0 1 0 4 nil)))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_floatsitf (IMG : RImg) := floatsitf_prog (sym 0x1bad0).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_floatsitf : CodeAtT img_segs (sym 0x1bad0) (PROGAT_CODE_floatsitf IMG)}.
  Context {RB_floatsitf : RelCode (sym 0x1bad0) 264}.
  Collection ImgHyps := IMG CODE_floatsitf RB_floatsitf.


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

Definition floatsitf_entry := (sym 0x1bad0)%Z.

Definition floatsitf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'.

(* [comment removed for export] *)
Local Ltac sitf_tail nM64 clz :=
  zstep; zstep; rewrite (srai63_word nM64) by lia; decide_tests_b;
  do 7 zstep; rewrite Z_to_bv_swrap32; rewrite (sext32_land64 (16414 - clz));
  name_as_by expW (sext32 (16414 - clz)) (apply sext32_range);
  zstep;
  match goal with |- context [Z_to_bv 64 (Z.shiftl ?x 48)] =>
    model_reg 15%Z expSh (Z.land (Z.shiftl x 48) W64) end;
  do 3 zstep.


(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

Lemma floatsitf_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (i : Z),
  mem_inv img_segs m ->
  bv_unsigned a0 = sext32 i ->
  evt img_segs (floatsitf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1bad0)) fc None m (seg_rom img_segs)).
Proof.
  intros until i. intros MI U.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  assert (Ra0 : (0 <= bv_unsigned a0 < 2^64)%Z) by apply (zr_word a0).
  unfold f128_of_i32. rewrite <- U.
  cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lo64 hi64 wrap64 b2z ONES64 IMPLICIT_HI]. zb_fold_lits.
  zstep. if_cases K0; zify_cond K0; decide_test1 ((bv_unsigned a0) =? 0%Z)%Z.
  - (* [comment removed for export] *) zstep. zstep. sf_finish.
  - (* [comment removed for export] *)
    zstep. rewrite (sraiw31_word (bv_unsigned a0)) by lia.
    model_reg 11%Z s (Z.land (0 - Z.land (Z.shiftr (bv_unsigned a0) 31) 1) W64).
    do 7 zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (Z.lxor (bv_unsigned a0) s - s)).
    name_as_by absW (sext32 (Z.lxor (bv_unsigned a0) s - s)) (apply sext32_range).
    (* [comment removed for export] *)
    wstep. model_reg_w 10%Z half (srliw absW 1).
    wstep. model_reg 11%Z x1 (Z.lor absW half).
    do 2 wstep. model_reg_w 11%Z x2 (Z.lor x1 (srliw x1 2)).
    do 2 wstep. model_reg_w 11%Z x3 (Z.lor x2 (srliw x2 4)).
    do 2 wstep. model_reg_w 11%Z x4 (Z.lor x3 (srliw x3 8)).
    do 2 wstep. model_reg_w 11%Z x5 (Z.lor x4 (srliw x4 16)).
    wstep. model_reg 11%Z y (Z.lxor x5 W64).
    do 5 wstep. model_reg 11%Z c1 (Z.land (y - Z.land (Z.shiftr y 1) 1431655765) W64).
    do 5 wstep. model_reg 11%Z c2 (Z.land (Z.land c1 858993459 + Z.land (Z.shiftr c1 2) 858993459) W64).
    do 7 wstep. model_reg 12%Z c3 (Z.land (Z.land (c2 + Z.shiftr c2 4) W64) 252645135).
    do 2 wstep. model_reg_w 12%Z c4 (srliw (Z.land (c3 * 16843009) W64) 24).
    replace (Z_to_bv 64 c4) with (Z_to_bv 64 (clz32_mirror absW)) by (f_equal; model_eval; reflexivity).
    name_as_by clz (clz32_mirror absW) (apply clz32_mirror_range).
    (* [comment removed for export] *)
    zstep. model_reg 13%Z e (Z.lxor clz 31).
    zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (112 - e)).
    name_as_by shW (sext32 (112 - e)) (apply sext32_range).
    do 3 zstep. replace (Z_to_bv 64 (Z.land shW 4294967295)) with (Z_to_bv 64 (zext32 shW)) by reflexivity.
    name_as_by n (zext32 shW) (rewrite zext32_eq; pose proof (Z.mod_pos_bound shW 4294967296 ltac:(lia)); lia).
    zstep. model_reg 15%Z nM64 (Z.land (n - 64) W64).
    zstep. replace (Z_to_bv 64 (Z.land absW 4294967295)) with (Z_to_bv 64 (zext32 absW)) by reflexivity.
    name_as_by aZ (zext32 absW) (rewrite zext32_eq; pose proof (Z.mod_pos_bound absW 4294967296 ltac:(lia)); lia).
    zstep. if_cases K1; zify_cond K1; decide_test1 ((nM64 ≫ 63)%Z =? 0%Z)%Z.
    + (* [comment removed for export] *)
      zstep. zstep.
      name_as_by hi0 (Z.shiftr half (Z.land (Z.lxor n W64) 63))
        (change (inr64 (Z.shiftr half (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      sitf_tail nM64 clz. sf_finish.
    + (* [comment removed for export] *)
      zstep. zstep.
      sitf_tail nM64 clz. sf_finish.
Qed.

(* [comment removed for export] *)
Definition floatsitf_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (i : Z),
  mem_inv img_segs m ->
  bv_unsigned a0 = sext32 i ->
  evt img_segs (floatsitf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1bad0)) fc None m (seg_rom img_segs)).
Lemma floatsitf_contract_ok : floatsitf_contract.
Proof. exact floatsitf_spec. Qed.


End Img.
(* [comment removed for export] *)
Ltac decide_test1 t :=
  first [ replace t with false by (symmetry; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; blia)
        | replace t with true  by (symmetry; first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; blia) ];
  cbn [andb orb negb].
Ltac decide_test1_try t := try decide_test1 t.

(* [comment removed for export] *)
Existing Class floatsitf_contract.
