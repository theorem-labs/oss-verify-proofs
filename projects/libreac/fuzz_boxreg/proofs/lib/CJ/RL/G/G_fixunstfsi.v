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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.P Require F_sf_helpers2.
Import OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.P.F_sf_helpers2.SF_buildtac. From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc Require Import RProgNotJ.

(* [comment removed for export] *)
Definition fixunstfsi_prog (B : Z) : RStep.ptree :=
  PNode 72%Z
  (PNode 36%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 12 0 0 4
        (PJ_Branch_BC_LT_nnn 4 11 0 108 4
        (PJ_ShiftImm_ALU_SLL_nnn 8 13 11 1 4
        (PJ_Lui_nn 12 14 4 4
        (PJ_ShiftImm_ALU_SRL_nnn 16 13 13 49 4
        (PJ_OpImm32_nnn 20 14 14 4095 4
        (PJ_Branch_BC_LTU_nnn 24 13 14 88 4
        (PJ_Lui_nn 28 12 1048572 4
        (PJ_OpImm32_nnn 32 12 12 4065 4 nil))))))))))
    (PLeaf
        (PJ_Op_ALU_ADD_nnn 36 12 13 12 4
        (PJ_OpImm_ALU_ADD_nnn 40 14 0 4064 4
        (PJ_Branch_BC_GEU_nnn 44 12 14 16 4
        (PJ_OpImm_ALU_ADD_nnn 48 12 0 4095 4
        (PJ_OpImm32_nnn 52 10 12 0 4
        (PJ_Jalr_nnn 56 0 1 0 4
        (PJ_ShiftImm_ALU_SLL_nnn 60 11 11 16 4
        (PJ_OpImm_ALU_ADD_nnn 64 12 0 1 4
        (PJ_Lui_nn 68 14 4 4 nil)))))))))))
  (PNode 108%Z
    (PLeaf
        (PJ_ShiftImm_ALU_SRL_nnn 72 15 11 16 4
        (PJ_ShiftImm_ALU_SLL_nnn 76 16 12 48 4
        (PJ_OpImm_ALU_ADD_nnn 80 12 14 111 4
        (PJ_Op32_ALU_SUB_nnn 84 12 12 13 4
        (PJ_ShiftImm_ALU_SLL_nnn 88 11 12 32 4
        (PJ_ShiftImm_ALU_SRL_nnn 92 11 11 32 4
        (PJ_OpImm_ALU_ADD_nnn 96 14 11 4032 4
        (PJ_Op_ALU_OR_nnn 100 13 15 16 4
        (PJ_Branch_BC_LT_nnn 104 14 0 16 4 nil))))))))))
    (PLeaf
        (PJ_Op_ALU_SRL_nnn 108 12 13 11 4
        (PJ_OpImm32_nnn 112 10 12 0 4
        (PJ_Jalr_nnn 116 0 1 0 4
        (PJ_Op_ALU_SRL_nnn 120 10 10 12 4
        (PJ_OpImm_ALU_XOR_nnn 124 11 11 4095 4
        (PJ_ShiftImm_ALU_SLL_nnn 128 13 13 1 4
        (PJ_Op_ALU_SLL_nnn 132 12 13 11 4
        (PJ_Op_ALU_OR_nnn 136 12 10 12 4
        (PJ_OpImm32_nnn 140 10 12 0 4
        (PJ_Jalr_nnn 144 0 1 0 4 nil)))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_fixunstfsi (IMG : RImg) := fixunstfsi_prog (sym 0x1c488).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_fixunstfsi : CodeAtT img_segs (sym 0x1c488) (PROGAT_CODE_fixunstfsi IMG)}.
  Context {RB_fixunstfsi : RelCode (sym 0x1c488) 148}.
  Collection ImgHyps := IMG CODE_fixunstfsi RB_fixunstfsi.


(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast. Local Ltac stepz ::= stepz_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition fixunstfsi_entry := (sym 0x1c488)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof.
  intros lo hi H. unfold lo64. rewrite wrap64_mod.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof.
  intros lo hi Hl Hh. unfold hi64. rewrite wrap64_mod, Z.shiftr_div_pow2 by lia.
  rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. apply Z.mod_small. lia.
Qed.

Lemma fixunstfsi_a0_split : forall a_lo a_hi,
  (0 <= a_lo < 2^64)%Z -> (0 <= a_hi < 2^64)%Z ->
  fixunstfsi_a0 (a_lo + 2^64 * a_hi) = sext32 (fixunstfsi_a2 a_hi a_lo).
Proof. intros. unfold fixunstfsi_a0. rewrite lo64_words, hi64_words by assumption. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fixunstfsi_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'.

Lemma fixunstfsi_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (fixunstfsi_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (fixunstfsi_a0 (bv_unsigned a0 + 2^64 * bv_unsigned a1)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c488)) fc None m (seg_rom img_segs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl img_segs m) as WM.
  pose_word_ranges.
  rewrite fixunstfsi_a0_split by lia.
  unfold fixunstfsi_a2.
  cbv beta delta [add64 sub64 shl64 not64 is_neg64 lo64 hi64 wrap64 b2z ONES64 IMPLICIT_HI]. zb_fold_lits.
  do 2 zstep. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    decide_tests_b. rewrite (sext32_small 0) by lia. zstep. zstep. finish.
  - do 3 zstep. name_reg 13%Z e.
    assert (He15 : (0 <= e < 2^(64-49))%Z)
      by (apply shiftr_bound; [change (inr64 (Z.land (Z.shiftl (bv_unsigned a1) 1) 18446744073709551615)); zrange| lia]).
    do 2 zstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      decide_tests_b. rewrite (sext32_small 0) by lia. zstep. zstep. finish.
    + do 5 zstep. if_cases K3; zify_cond K3; decide_tests_b.
      * (* [comment removed for export] *)
        assert (He : (16383 <= e <= 16414)%Z) by (clear -K2 K3 He15; revert K3; zb_masks; intros K3; mlia).
        clear K2 K3.
        (* [comment removed for export] *)
        rewrite (land_W64_small (16495 - e)) by lia. rewrite (sext32_small (16495 - e)) by lia.
        rewrite (zext32_small (16495 - e)) by lia. rewrite (land_W64_small (16495 - e - 64)) by lia.
        rewrite (shiftr63_small (16495 - e - 64)) by lia. cbn [Z.eqb negb].
        rewrite (land63_64_128 (16495 - e)) by lia.
        do 7 zstep. rewrite (swrap32_small (16495 - e)) by lia.
        do 2 zstep. rewrite (land_M32_small (16495 - e)) by lia.
        do 3 zstep. if_cases K4; zify_cond K4.
        -- (* [comment removed for export] *)
          exfalso. clear -K4 He. lia.
        -- zstep. rewrite (land63_64_128 (16495 - e)) by lia.
           zstep. rewrite ?Z.add_0_r. rewrite Z_to_bv_swrap32.
           zstep. finish.
      * (* [comment removed for export] *)
        do 2 zstep.
        replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (sext32 18446744073709551615)) by (apply Z_to_bv_eqm; vm_compute; reflexivity).
        zstep. finish.
Qed.

(* [comment removed for export] *)
Definition fixunstfsi_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv img_segs m ->
  evt img_segs (fixunstfsi_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (fixunstfsi_a0 (bv_unsigned a0 + 2^64 * bv_unsigned a1)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x1c488)) fc None m (seg_rom img_segs)).
Lemma fixunstfsi_contract_ok : fixunstfsi_contract.
Proof. exact fixunstfsi_spec. Qed.


End Img.

(* [comment removed for export] *)
Existing Class fixunstfsi_contract.
