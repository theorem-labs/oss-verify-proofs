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
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Arr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require ITree.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Nodes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Decode.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require RegsEquiv.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P Require Exit_tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RProgAt.
Module GExit_tac.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Tac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Arr OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Bytes OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.ITree OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Nodes OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Decode OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SysStep OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.RegsEquiv.
Export OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P.Exit_tac.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Ltac amo_decide_orig :=
  repeat match goal with
  | |- context [amo_aligned ?wd ?a] =>
      let b := eval vm_compute in (amo_aligned wd a) in
      replace (amo_aligned wd a) with b by (vm_compute; reflexivity); cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
      let b := eval vm_compute in (Z.eqb (bv_unsigned x) (bv_unsigned y)) in
      replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with b by (vm_compute; reflexivity); cbv iota
  end.

Lemma amo_aligned_sym : forall wd z, (0 <= z < 2^64)%Z -> (z mod amo_bytes wd = 0)%Z -> amo_aligned wd (Z_to_bv 64 z) = true.
Proof. intros wd z Hz Hm. unfold amo_aligned. rewrite unsigned_lit by exact Hz. apply Z.eqb_eq. exact Hm. Qed.

Ltac aamo_decide :=
  repeat match goal with
  | |- context [amo_aligned ?wd (Z_to_bv 64 ?z)] =>
      has_sym z;
      rewrite (amo_aligned_sym wd z) by (cbn [amo_bytes]; arel_side);
      cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?x)] => rewrite Z.eqb_refl; cbv iota
  | |- context [amo_aligned ?wd ?a] =>
      tryif has_sym a then fail 100 "amo_decide: cannot decide alignment of symbolic address" a "(give an alignment fact: gport2 --align HEX:N)" else
      let b := eval vm_compute in (amo_aligned wd a) in
      replace (amo_aligned wd a) with b by (vm_compute; reflexivity); cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
      first [ has_sym x; replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with false
                by (symmetry; apply Z.eqb_neq; rewrite ?unsigned_lit by arel_side; arel_side); cbv iota
            | tryif first [has_sym x | has_sym y] then fail 100 "amo_decide: symbolic reservation test" x y else
              let b := eval vm_compute in (Z.eqb (bv_unsigned x) (bv_unsigned y)) in
              replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with b by (vm_compute; reflexivity); cbv iota ]
  end.

Ltac amo_step_orig :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    concrete_segs segs;
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply evt_step;
      [ split; [reflexivity|];
        rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

Ltac aamo_step :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?E) ?fc ?rv ?m ?ro) =>
      tryif (let B := apc_base E in first [ lazymatch goal with CODE : code_at segs B _ |- _ => idtac end
                                             | lazymatch goal with CODE : CodeAt segs B _ |- _ => idtac end
                                             | lazymatch goal with CODE : CodeAtT segs B _ |- _ => idtac end ])
      then (let FD0 := afetch segs E in
            let FD := fresh "FD" in pose proof FD0 as FD;
            lazymatch type of FD with
            | fetch_dec _ _ = Some (?i, ?sz) =>
                eapply evt_step;
                [ split; [reflexivity|];
                  rewrite (step_gen_dec segs R F (Z_to_bv 64 E) fc rv m ro i sz FD ltac:(discriminate));
                  exec_cbv; simp_is_x0; simp_regs; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i; arel;
                  try solve_load; try solve_store; reflexivity
                | simp_regs; vnorm_for i; arel; mem_after_store_opt ];
                try clear FD
            end)
      else amo_step_orig
  end.
End GExit_tac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P Require Exit_tac.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P Require Exit_tac.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P.Exit_tac.Startup_tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P Require Import Exit_tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G Require Import G_memset.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.
Import GExit_tac.
(* [comment removed for export] *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.StoreCache.StoreFast.
From Stdlib Require Import Zify Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Import NElim. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require JunkAbs.
(* [comment removed for export] *)

Import ListNotations.
Import ITree.Exc.

(* [comment removed for export] *)
Definition Exit_prog (B K_34280 B_15ce0 B_15ce4 B_stdio_exit B_15da4 : Z) : RStep.ptree :=
  PNode 56%Z
  (PLeaf
      (PJ_OpImm_ALU_ADD_nnn 0 2 2 4080 4
      (PJ_Store_SZ8_nnn 4 2 1 8 4
      (PJ_Store_SZ8_nnn 8 2 8 0 4
      (PJ_OpImm_ALU_ADD_nnn 12 11 0 0 4
      (PJ_OpImm_ALU_ADD_nnn 16 12 4 0 4
      (PJ_Load_SZ4_true_nnn 20 12 12 3928 4
      (PJ_Auipc_nt 24 13 (hi20 (K_34280 - (B + 24))) 4
      (PJ_OpImm_ALU_ADD_nnt 28 13 13 (lo12 (K_34280 - (B + 24))) 4
      (PJ_Lr_AW_true_true_nn 32 14 13 4
      (PJ_Branch_BC_NE_nnn 36 14 11 12 4
      (PJ_Sc_AW_true_true_nnn 40 15 13 12 4
      (PJ_Branch_BC_NE_nnn 44 15 0 8180 4
      (PJ_OpImm32_nnn 48 11 14 0 4
      (PJ_Branch_BC_EQ_nnn 52 11 12 36 4 nil)))))))))))))))
  (PLeaf
      (PJ_Branch_BC_EQ_nnn 56 11 0 36 4
      (PJ_OpImm_ALU_ADD_nnn 60 17 0 73 4
      (PJ_OpImm_ALU_ADD_nnn 64 11 0 0 4
      (PJ_OpImm_ALU_ADD_nnn 68 12 0 0 4
      (PJ_OpImm_ALU_ADD_nnn 72 13 0 0 4
      (PJ_OpImm_ALU_ADD_nnn 76 10 0 0 4
      (PJ_Ecall_ 80  4
      (PJ_Jal_nn 84 0 2097144 4
      (PJ_Store_SZ1_nnn 88 0 0 0 4
      (PJ_OpImm_ALU_ADD_nnn 92 8 10 0 4
      (PJ_Jal_nt 96 1 (jimm21 (B_15ce0 - (B + 96))) 4
      (PJ_Jal_nt 100 1 (jimm21 (B_15ce4 - (B + 100))) 4
      (PJ_Jal_nt 104 1 (jimm21 (B_stdio_exit - (B + 104))) 4
      (PJ_OpImm_ALU_ADD_nnn 108 10 8 0 4
      (PJ_Jal_nt 112 1 (jimm21 (B_15da4 - (B + 112))) 4 nil)))))))))))))))).

(* [comment removed for export] *)
Definition Exit_prog_r1 (B : Z) : RStep.ptree :=
  PLeaf
    (PJ_OpImm_ALU_ADD_nnn 0 11 10 0 4
    (PJ_OpImm_ALU_ADD_nnn 4 17 0 94 4
    (PJ_Ecall_ 8  4
    (PJ_OpImm_ALU_ADD_nnn 12 17 0 93 4
    (PJ_OpImm_ALU_ADD_nnn 16 10 11 0 4
    (PJ_Ecall_ 20  4
    (PJ_Jal_nn 24 0 2097144 4 nil))))))).

(* [comment removed for export] *)
Definition Exit_prog_r2 (B K_22e20 B_15ce0 : Z) : RStep.ptree :=
  PNode 36%Z
  (PLeaf
      (PJ_OpImm_ALU_ADD_nnn 0 2 2 4064 4
      (PJ_Store_SZ8_nnn 4 2 1 24 4
      (PJ_Store_SZ8_nnn 8 2 8 16 4
      (PJ_Store_SZ8_nnn 12 2 9 8 4
      (PJ_Auipc_nt 16 10 (hi20 (K_22e20 - (B + 16))) 4
      (PJ_Auipc_nt 20 11 (hi20 (K_22e20 + 8 - (B + 20))) 4
      (PJ_Load_SZ8_true_nnt 24 10 10 (lo12 (K_22e20 - (B + 16))) 4
      (PJ_Load_SZ8_true_nnt 28 8 11 (lo12 (K_22e20 + 8 - (B + 20))) 4
      (PJ_Branch_BC_GEU_nnn 32 8 10 24 4 nil))))))))))
  (PLeaf
      (PJ_Load_SZ8_true_nnn 36 11 10 4088 4
      (PJ_OpImm_ALU_ADD_nnn 40 9 10 4088 4
      (PJ_Jalr_nnn 44 1 11 0 4
      (PJ_OpImm_ALU_ADD_nnn 48 10 9 0 4
      (PJ_Branch_BC_LTU_nnn 52 8 9 8176 4
      (PJ_Load_SZ8_true_nnn 56 1 2 24 4
      (PJ_Load_SZ8_true_nnn 60 8 2 16 4
      (PJ_Load_SZ8_true_nnn 64 9 2 8 4
      (PJ_OpImm_ALU_ADD_nnn 68 2 2 32 4
      (PJ_Jal_nt 72 0 (jimm21 (B_15ce0 - (B + 72))) 4 nil))))))))))).

(* [comment removed for export] *)
Definition Exit_prog_r3 (B : Z) : RStep.ptree :=
  PLeaf
    (PJ_Jalr_nnn 0 0 1 0 4 nil).

(* [comment removed for export] *)
Definition Exit_prog_r4 (B K_240a8 K_22dd0 K_23e30 K_11988 B_cxa : Z) : RStep.ptree :=
  PNode 72%Z
  (PNode 36%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 2 2 4080 4
        (PJ_Store_SZ8_nnn 4 2 1 8 4
        (PJ_Store_SZ8_nnn 8 2 8 0 4
        (PJ_OpImm_ALU_ADD_nnn 12 8 2 16 4
        (PJ_Auipc_nt 16 10 (hi20 (K_240a8 - (B + 16))) 4
        (PJ_OpImm_ALU_ADD_nnt 20 10 10 (lo12 (K_240a8 - (B + 16))) 4
        (PJ_Load_SZ1_false_nnn 24 10 10 0 4
        (PJ_OpImm_ALU_AND_nnn 28 10 10 1 4
        (PJ_Branch_BC_EQ_nnn 32 10 0 12 4 nil))))))))))
    (PLeaf
        (PJ_Jal_nn 36 0 4 4
        (PJ_Jal_nn 40 0 88 4
        (PJ_Auipc_nt 44 10 (hi20 (K_240a8 - (B + 44))) 4
        (PJ_OpImm_ALU_ADD_nnt 48 11 10 (lo12 (K_240a8 - (B + 44))) 4
        (PJ_OpImm_ALU_ADD_nnn 52 10 0 1 4
        (PJ_Store_SZ1_nnn 56 11 10 0 4
        (PJ_Auipc_nt 60 10 (hi20 (K_22dd0 - (B + 60))) 4
        (PJ_Load_SZ8_true_nnt 64 10 10 (lo12 (K_22dd0 - (B + 60))) 4
        (PJ_Branch_BC_EQ_nnn 68 10 0 28 4 nil)))))))))))
  (PNode 108%Z
    (PLeaf
        (PJ_Jal_nn 72 0 4 4
        (PJ_Auipc_nt 76 10 (hi20 (K_23e30 - (B + 76))) 4
        (PJ_OpImm_ALU_ADD_nnt 80 10 10 (lo12 (K_23e30 - (B + 76))) 4
        (PJ_Load_SZ8_true_nnn 84 10 10 0 4
        (PJ_Jal_nt 88 1 (jimm21 (B_cxa - (B + 88))) 4
        (PJ_Jal_nn 92 0 4 4
        (PJ_Auipc_nt 96 10 (hi20 (K_22dd0 + 8 - (B + 96))) 4
        (PJ_Load_SZ8_true_nnt 100 10 10 (lo12 (K_22dd0 + 8 - (B + 96))) 4
        (PJ_Branch_BC_EQ_nnn 104 10 0 24 4 nil))))))))))
    (PLeaf
        (PJ_Jal_nn 108 0 4 4
        (PJ_Auipc_nt 112 10 (hi20 (K_11988 - (B + 112))) 4
        (PJ_OpImm_ALU_ADD_nnt 116 10 10 (lo12 (K_11988 - (B + 112))) 4
        (PJ_Jal_nn 120 1 0 4
        (PJ_Jal_nn 124 0 4 4
        (PJ_Load_SZ8_true_nnn 128 1 2 8 4
        (PJ_Load_SZ8_true_nnn 132 8 2 0 4
        (PJ_OpImm_ALU_ADD_nnn 136 2 2 16 4
        (PJ_Jalr_nnn 140 0 1 0 4 nil))))))))))).
(* [comment removed for export] *)
Definition Exit_prog_fox (B K_ATEX B_lock B_unlock : Z) : RStep.ptree :=
  PNode 100%Z
  (PNode 48%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 2 2 4048 4
        (PJ_Store_SZ8_nnn 4 2 1 40 4
        (PJ_Store_SZ8_nnn 8 2 8 32 4
        (PJ_Store_SZ8_nnn 12 2 9 24 4
        (PJ_Store_SZ8_nnn 16 2 18 16 4
        (PJ_Store_SZ8_nnn 20 2 19 8 4
        (PJ_Auipc_nt 24 10 (hi20 (K_ATEX - (B + 24))) 4
        (PJ_OpImm_ALU_ADD_nnt 28 18 10 (lo12 (K_ATEX - (B + 24))) 4
        (PJ_OpImm_ALU_ADD_nnn 32 8 18 4 4
        (PJ_OpImm_ALU_ADD_nnn 36 10 8 0 4
        (PJ_Jal_nt 40 1 (jimm21 (B_lock - (B + 40))) 4
        (PJ_Load_SZ8_true_nnn 44 10 18 16 4 nil)))))))))))))
    (PLeaf
        (PJ_Branch_BC_EQ_nnn 48 10 0 112 4
        (PJ_Load_SZ4_true_nnn 52 11 18 8 4
        (PJ_Jal_nn 56 0 24 4
        (PJ_Load_SZ8_true_nnn 60 10 10 0 4
        (PJ_OpImm_ALU_ADD_nnn 64 11 0 32 4
        (PJ_Store_SZ4_nnn 68 18 11 8 4
        (PJ_Store_SZ8_nnn 72 18 10 16 4
        (PJ_Branch_BC_EQ_nnn 76 10 0 84 4
        (PJ_OpImm32_nnn 80 12 11 4095 4
        (PJ_Store_SZ4_nnn 84 18 12 8 4
        (PJ_Branch_BC_GE_nnn 88 0 11 8164 4
        (PJ_Load_SZ8_true_nnn 92 10 18 16 4
        (PJ_ShiftImm_ALU_SLL_nnn 96 12 12 3 4 nil)))))))))))))))
  (PNode 148%Z
    (PLeaf
        (PJ_Op_ALU_ADD_nnn 100 10 10 12 4
        (PJ_Load_SZ8_true_nnn 104 19 10 8 4
        (PJ_Load_SZ8_true_nnn 108 9 10 264 4
        (PJ_OpImm_ALU_ADD_nnn 112 10 8 0 4
        (PJ_Jal_nt 116 1 (jimm21 (B_unlock - (B + 116))) 4
        (PJ_OpImm_ALU_ADD_nnn 120 10 9 0 4
        (PJ_Jalr_nnn 124 1 19 0 4
        (PJ_OpImm_ALU_ADD_nnn 128 10 8 0 4
        (PJ_Jal_nt 132 1 (jimm21 (B_lock - (B + 132))) 4
        (PJ_Load_SZ4_true_nnn 136 10 18 8 4
        (PJ_OpImm32_nnn 140 12 10 4095 4
        (PJ_Store_SZ4_nnn 144 18 12 8 4 nil)))))))))))))
    (PLeaf
        (PJ_Branch_BC_LT_nnn 148 0 10 8136 4
        (PJ_Load_SZ8_true_nnn 152 10 18 16 4
        (PJ_Jal_nn 156 0 2097056 4
        (PJ_OpImm_ALU_ADD_nnn 160 10 0 1 4
        (PJ_Store_SZ1_nnn 164 18 10 0 4
        (PJ_OpImm_ALU_ADD_nnn 168 10 8 0 4
        (PJ_Load_SZ8_true_nnn 172 1 2 40 4
        (PJ_Load_SZ8_true_nnn 176 8 2 32 4
        (PJ_Load_SZ8_true_nnn 180 9 2 24 4
        (PJ_Load_SZ8_true_nnn 184 18 2 16 4
        (PJ_Load_SZ8_true_nnn 188 19 2 8 4
        (PJ_OpImm_ALU_ADD_nnn 192 2 2 48 4
        (PJ_Jal_nt 196 0 (jimm21 (B_unlock - (B + 196))) 4 nil))))))))))))))).
(* [comment removed for export] *)
Definition Exit_prog_cxa (B : Z) : RStep.ptree :=
  PLeaf
    (PJ_Jalr_nnn 0 0 1 0 4 nil).
(* [comment removed for export] *)
Definition Exit_prog_call (B : Z) : RStep.ptree :=
  PLeaf
    (PJ_Jalr_nnn 0 0 10 0 4 nil).
(* [comment removed for export] *)
Definition Exit_prog_guard (B K_INCB : Z) : RStep.ptree :=
  PLeaf
    (PJ_Auipc_nt 0 10 (hi20 (K_INCB - B)) 4
    (PJ_Load_SZ1_false_nnt 4 10 10 (lo12 (K_INCB - B)) 4
    (PJ_Branch_BC_NE_nnn 8 10 0 8 4
    (PJ_Jalr_nnn 12 0 1 0 4 nil)))).
(* [comment removed for export] *)
Definition Exit_prog_lock (B K_342a8 : Z) : RStep.ptree :=
  PNode 252%Z
  (PNode 124%Z
    (PNode 60%Z
      (PLeaf
          (PJ_Auipc_nt 0 11 (hi20 (K_342a8 + 3 - B)) 4
          (PJ_Load_SZ1_true_nnt 4 13 11 (lo12 (K_342a8 + 3 - B)) 4
          (PJ_Branch_BC_EQ_nnn 8 13 0 496 4
          (PJ_OpImm_ALU_ADD_nnn 12 12 0 0 4
          (PJ_Lui_nn 16 14 524288 4
          (PJ_OpImm32_nnn 20 14 14 1 4
          (PJ_Lr_AW_true_true_nn 24 15 10 4
          (PJ_Branch_BC_NE_nnn 28 15 12 12 4
          (PJ_Sc_AW_true_true_nnn 32 16 10 14 4
          (PJ_Branch_BC_NE_nnn 36 16 0 8180 4
          (PJ_OpImm32_nnn 40 12 15 0 4
          (PJ_Branch_BC_GE_nnn 44 13 0 8 4
          (PJ_Store_SZ1_nnt 48 11 0 (lo12 (K_342a8 + 3 - B)) 4
          (PJ_Branch_BC_EQ_nnn 52 12 0 452 4
          (PJ_Lui_nn 56 15 524288 4 nil))))))))))))))))
      (PLeaf
          (PJ_ShiftImm_ALU_SLL_nnn 60 11 12 2 4
          (PJ_OpImm_ALU_ADD_nnn 64 15 15 4095 4
          (PJ_ShiftImm_ALU_SRL_nnn 68 11 11 33 4
          (PJ_Op32_ALU_ADD_nnn 72 12 12 11 4
          (PJ_Op_ALU_ADD_nnn 76 11 12 15 4
          (PJ_OpImm32_nnn 80 11 11 2 4
          (PJ_Lr_AW_true_true_nn 84 13 10 4
          (PJ_Branch_BC_NE_nnn 88 13 12 12 4
          (PJ_Sc_AW_true_true_nnn 92 14 10 11 4
          (PJ_Branch_BC_NE_nnn 96 14 0 8180 4
          (PJ_OpImm32_nnn 100 11 13 0 4
          (PJ_Branch_BC_EQ_nnn 104 11 12 400 4
          (PJ_ShiftImm_ALU_SRL_nnn 108 12 11 31 4
          (PJ_Op_ALU_AND_nnn 112 12 12 15 4
          (PJ_Op32_ALU_ADD_nnn 116 12 11 12 4
          (PJ_Op_ALU_ADD_nnn 120 11 15 12 4 nil))))))))))))))))))
    (PNode 188%Z
      (PLeaf
          (PJ_OpImm32_nnn 124 11 11 2 4
          (PJ_Lr_AW_true_true_nn 128 13 10 4
          (PJ_Branch_BC_NE_nnn 132 13 12 12 4
          (PJ_Sc_AW_true_true_nnn 136 14 10 11 4
          (PJ_Branch_BC_NE_nnn 140 14 0 8180 4
          (PJ_OpImm32_nnn 144 11 13 0 4
          (PJ_Branch_BC_EQ_nnn 148 11 12 356 4
          (PJ_ShiftImm_ALU_SRL_nnn 152 12 11 31 4
          (PJ_Op_ALU_AND_nnn 156 12 12 15 4
          (PJ_Op32_ALU_ADD_nnn 160 12 11 12 4
          (PJ_Op_ALU_ADD_nnn 164 11 15 12 4
          (PJ_OpImm32_nnn 168 11 11 2 4
          (PJ_Lr_AW_true_true_nn 172 13 10 4
          (PJ_Branch_BC_NE_nnn 176 13 12 12 4
          (PJ_Sc_AW_true_true_nnn 180 14 10 11 4
          (PJ_Branch_BC_NE_nnn 184 14 0 8180 4 nil)))))))))))))))))
      (PLeaf
          (PJ_OpImm32_nnn 188 11 13 0 4
          (PJ_Branch_BC_EQ_nnn 192 11 12 312 4
          (PJ_ShiftImm_ALU_SRL_nnn 196 12 11 31 4
          (PJ_Op_ALU_AND_nnn 200 12 12 15 4
          (PJ_Op32_ALU_ADD_nnn 204 12 11 12 4
          (PJ_Op_ALU_ADD_nnn 208 11 15 12 4
          (PJ_OpImm32_nnn 212 11 11 2 4
          (PJ_Lr_AW_true_true_nn 216 13 10 4
          (PJ_Branch_BC_NE_nnn 220 13 12 12 4
          (PJ_Sc_AW_true_true_nnn 224 14 10 11 4
          (PJ_Branch_BC_NE_nnn 228 14 0 8180 4
          (PJ_OpImm32_nnn 232 11 13 0 4
          (PJ_Branch_BC_EQ_nnn 236 11 12 268 4
          (PJ_ShiftImm_ALU_SRL_nnn 240 12 11 31 4
          (PJ_Op_ALU_AND_nnn 244 12 12 15 4
          (PJ_Op32_ALU_ADD_nnn 248 12 11 12 4 nil)))))))))))))))))))
  (PNode 380%Z
    (PNode 316%Z
      (PLeaf
          (PJ_Op_ALU_ADD_nnn 252 11 15 12 4
          (PJ_OpImm32_nnn 256 11 11 2 4
          (PJ_Lr_AW_true_true_nn 260 13 10 4
          (PJ_Branch_BC_NE_nnn 264 13 12 12 4
          (PJ_Sc_AW_true_true_nnn 268 14 10 11 4
          (PJ_Branch_BC_NE_nnn 272 14 0 8180 4
          (PJ_OpImm32_nnn 276 11 13 0 4
          (PJ_Branch_BC_EQ_nnn 280 11 12 224 4
          (PJ_ShiftImm_ALU_SRL_nnn 284 12 11 31 4
          (PJ_Op_ALU_AND_nnn 288 12 12 15 4
          (PJ_Op32_ALU_ADD_nnn 292 12 11 12 4
          (PJ_Op_ALU_ADD_nnn 296 11 15 12 4
          (PJ_OpImm32_nnn 300 11 11 2 4
          (PJ_Lr_AW_true_true_nn 304 13 10 4
          (PJ_Branch_BC_NE_nnn 308 13 12 12 4
          (PJ_Sc_AW_true_true_nnn 312 14 10 11 4 nil)))))))))))))))))
      (PLeaf
          (PJ_Branch_BC_NE_nnn 316 14 0 8180 4
          (PJ_OpImm32_nnn 320 11 13 0 4
          (PJ_Branch_BC_EQ_nnn 324 11 12 180 4
          (PJ_ShiftImm_ALU_SRL_nnn 328 12 11 31 4
          (PJ_Op_ALU_AND_nnn 332 12 12 15 4
          (PJ_Op32_ALU_ADD_nnn 336 12 11 12 4
          (PJ_Op_ALU_ADD_nnn 340 11 15 12 4
          (PJ_OpImm32_nnn 344 11 11 2 4
          (PJ_Lr_AW_true_true_nn 348 13 10 4
          (PJ_Branch_BC_NE_nnn 352 13 12 12 4
          (PJ_Sc_AW_true_true_nnn 356 14 10 11 4
          (PJ_Branch_BC_NE_nnn 360 14 0 8180 4
          (PJ_OpImm32_nnn 364 11 13 0 4
          (PJ_Branch_BC_EQ_nnn 368 11 12 136 4
          (PJ_ShiftImm_ALU_SRL_nnn 372 12 11 31 4
          (PJ_Op_ALU_AND_nnn 376 12 12 15 4 nil))))))))))))))))))
    (PNode 444%Z
      (PLeaf
          (PJ_Op32_ALU_ADD_nnn 380 12 11 12 4
          (PJ_Op_ALU_ADD_nnn 384 11 15 12 4
          (PJ_OpImm32_nnn 388 11 11 2 4
          (PJ_Lr_AW_true_true_nn 392 13 10 4
          (PJ_Branch_BC_NE_nnn 396 13 12 12 4
          (PJ_Sc_AW_true_true_nnn 400 14 10 11 4
          (PJ_Branch_BC_NE_nnn 404 14 0 8180 4
          (PJ_OpImm32_nnn 408 11 13 0 4
          (PJ_Branch_BC_EQ_nnn 412 11 12 92 4
          (PJ_ShiftImm_ALU_SRL_nnn 416 12 11 31 4
          (PJ_Op_ALU_AND_nnn 420 12 12 15 4
          (PJ_Op32_ALU_ADD_nnn 424 12 11 12 4
          (PJ_Op_ALU_ADD_nnn 428 11 15 12 4
          (PJ_OpImm32_nnn 432 11 11 2 4
          (PJ_Lr_AW_true_true_nn 436 13 10 4
          (PJ_Branch_BC_NE_nnn 440 13 12 12 4 nil)))))))))))))))))
      (PLeaf
          (PJ_Sc_AW_true_true_nnn 444 14 10 11 4
          (PJ_Branch_BC_NE_nnn 448 14 0 8180 4
          (PJ_OpImm32_nnn 452 11 13 0 4
          (PJ_Branch_BC_EQ_nnn 456 11 12 48 4
          (PJ_ShiftImm_ALU_SRL_nnn 460 12 11 31 4
          (PJ_Op_ALU_AND_nnn 464 12 12 15 4
          (PJ_Op32_ALU_ADD_nnn 468 11 11 12 4
          (PJ_Op_ALU_ADD_nnn 472 12 15 11 4
          (PJ_OpImm32_nnn 476 12 12 2 4
          (PJ_Lr_AW_true_true_nn 480 13 10 4
          (PJ_Branch_BC_NE_nnn 484 13 11 12 4
          (PJ_Sc_AW_true_true_nnn 488 14 10 12 4
          (PJ_Branch_BC_NE_nnn 492 14 0 8180 4
          (PJ_OpImm32_nnn 496 13 13 0 4
          (PJ_Branch_BC_NE_nnn 500 13 11 8 4
          (PJ_Jalr_nnn 504 0 1 0 4 nil))))))))))))))))))).
(* [comment removed for export] *)
Definition Exit_prog_unlock (B : Z) : RStep.ptree :=
  PLeaf
    (PJ_Load_SZ4_true_nnn 0 11 10 0 4
    (PJ_Branch_BC_LT_nnn 4 11 0 8 4
    (PJ_Jalr_nnn 8 0 1 0 4 nil))).

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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G Require G_memcpy.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P.Exit_tac.STRW_tac.cur_mem_addr ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G.G_memcpy.GSTRW_tac.acur_mem_addr.

Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P.Exit_tac.amo_decide ::= GExit_tac.aamo_decide.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P.Exit_tac.amo_step ::= GExit_tac.aamo_step.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_Exit (IMG : RImg) := Exit_prog (sym 0x15d30) (sym 0x34280) (sym 0x100015d84) (sym 0x15ce4) (sym 0x17f94) (sym 0x15da4).
Definition PROGAT_CODE_Exit_1 (IMG : RImg) := Exit_prog_r1 (sym 0x15da4).
Definition PROGAT_CODE_Exit_2 (IMG : RImg) := Exit_prog_r2 (sym 0x15ce4) (sym 0x22e20) (sym 0x15ce0).
Definition PROGAT_CODE_Exit_3 (IMG : RImg) := Exit_prog_r3 (sym 0x15ce0).
Definition PROGAT_CODE_Exit_4 (IMG : RImg) := Exit_prog_r4 (sym 0x1303c) (sym 0x240a8) (sym 0x22dd0) (sym 0x23e30) (sym 0x11988) (sym 0x100015e4c).
Definition PROGAT_CODE_Exit_5 (IMG : RImg) := Exit_prog_fox (sym 0x100015d84) (sym 0x100034900) (sym 0x21964) (sym 0x21bec).
Definition PROGAT_CODE_Exit_6 (IMG : RImg) := Exit_prog_cxa (sym 0x100015e4c).
Definition PROGAT_CODE_Exit_7 (IMG : RImg) := Exit_prog_call (sym 0x100015f14).
Definition PROGAT_CODE_Exit_8 (IMG : RImg) := Exit_prog_guard (sym 0x10001351c) (sym 0x100034734).
Definition PROGAT_CODE_Exit_9 (IMG : RImg) := Exit_prog_lock (sym 0x21964) (sym 0x342a8).
Definition PROGAT_CODE_Exit_10 (IMG : RImg) := Exit_prog_unlock (sym 0x21bec).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_Exit : CodeAtT img_segs (sym 0x15d30) (PROGAT_CODE_Exit IMG)}.
  Context {RB_Exit : RelCode (sym 0x15d30) 116}.
  Context {CODE_Exit_1 : CodeAtT img_segs (sym 0x15da4) (PROGAT_CODE_Exit_1 IMG)}.
  Context {RB_Exit_1 : RelCode (sym 0x15da4) 28}.
  Context {CODE_Exit_2 : CodeAtT img_segs (sym 0x15ce4) (PROGAT_CODE_Exit_2 IMG)}.
  Context {RB_Exit_2 : RelCode (sym 0x15ce4) 76}.
  Context {CODE_Exit_3 : CodeAtT img_segs (sym 0x15ce0) (PROGAT_CODE_Exit_3 IMG)}.
  Context {RB_Exit_3 : RelCode (sym 0x15ce0) 4}.
  Context {CODE_Exit_4 : CodeAtT img_segs (sym 0x1303c) (PROGAT_CODE_Exit_4 IMG)}.
  Context {RB_Exit_4 : RelCode (sym 0x1303c) 144}.
  Context {CODE_Exit_5 : CodeAtT img_segs (sym 0x100015d84) (PROGAT_CODE_Exit_5 IMG)}.
  Context {RB_Exit_5 : RelCode (sym 0x100015d84) 200}.
  Context {CODE_Exit_6 : CodeAtT img_segs (sym 0x100015e4c) (PROGAT_CODE_Exit_6 IMG)}.
  Context {RB_Exit_6 : RelCode (sym 0x100015e4c) 4}.
  Context {CODE_Exit_7 : CodeAtT img_segs (sym 0x100015f14) (PROGAT_CODE_Exit_7 IMG)}.
  Context {RB_Exit_7 : RelCode (sym 0x100015f14) 4}.
  Context {CODE_Exit_8 : CodeAtT img_segs (sym 0x10001351c) (PROGAT_CODE_Exit_8 IMG)}.
  Context {RB_Exit_8 : RelCode (sym 0x10001351c) 16}.
  Context {CODE_Exit_9 : CodeAtT img_segs (sym 0x21964) (PROGAT_CODE_Exit_9 IMG)}.
  Context {RB_Exit_9 : RelCode (sym 0x21964) 508}.
  Context {CODE_Exit_10 : CodeAtT img_segs (sym 0x21bec) (PROGAT_CODE_Exit_10 IMG)}.
  Context {RB_Exit_10 : RelCode (sym 0x21bec) 12}.
  Local Notation GLRN a b := (RelNear (sym a) (sym b)) (only parsing). Local Notation GLRS a := (RelSym (sym a)) (only parsing). Context {RN_B_fox_15d30 : GLRN 0x15d30 0x100015d84}.
  Context {RN_B_lock_fox : GLRN 0x100015d84 0x21964}.
  Context {RN_B_unlock_fox : GLRN 0x100015d84 0x21bec}.
  Context {RN_B_cxa_1303c : GLRN 0x1303c 0x100015e4c}.
  Context {RN_B_15ce4_15d30 : GLRN 0x15d30 0x15ce4}.
  Context {RN_B_stdio_exit_15d30 : GLRN 0x15d30 0x17f94}.
  Context {RN_B_15da4_15d30 : GLRN 0x15d30 0x15da4}.
  Context {RN_B_15ce0_15ce4 : GLRN 0x15ce4 0x15ce0}.
  Context {RS_K_34280 : GLRS 0x34280}.
  Context {RS_K_22e20 : GLRS 0x22e20}.
  Context {RS_K_240a8 : GLRS 0x240a8}.
  Context {RS_K_22dd0 : GLRS 0x22dd0}.
  Context {RS_K_23e30 : GLRS 0x23e30}.
  Context {RS_K_11988 : GLRS 0x11988}.
  Context {RS_K_ATEX : GLRS 0x100034900}.
  Let rp_ATEX : (0 <= sym 0x100034900 /\ sym 0x100034900 < 2^30)%Z := @rel_sym_pf _ RS_K_ATEX.
  Context {RS_K_INCB : GLRS 0x100034734}.
  Let rp_INCB : (0 <= sym 0x100034734 /\ sym 0x100034734 < 2^30)%Z := @rel_sym_pf _ RS_K_INCB.
  Context {RS_K_CALL : GLRS 0x100015f14}.
  Let rp_CALL : (0 <= sym 0x100015f14 /\ sym 0x100015f14 < 2^30)%Z := @rel_sym_pf _ RS_K_CALL.
  Context {RS_K_GUARD : GLRS 0x10001351c}.
  Let rp_GUARD : (0 <= sym 0x10001351c /\ sym 0x10001351c < 2^30)%Z := @rel_sym_pf _ RS_K_GUARD.
  Context {RS_K_CXA : GLRS 0x100015e4c}.
  Let rp_CXA : (0 <= sym 0x100015e4c /\ sym 0x100015e4c < 2^30)%Z := @rel_sym_pf _ RS_K_CXA.
  Context {RS_23e30 : GLRS 0x23e30}.
  Let rp_23e30 : (0 <= sym 0x23e30 /\ sym 0x23e30 < 2^30)%Z := @rel_sym_pf _ RS_23e30.
  Context {RS_341f8 : GLRS 0x341f8}.
  Let rp_341f8 : (0 <= sym 0x341f8 /\ sym 0x341f8 < 2^30)%Z := @rel_sym_pf _ RS_341f8.
  Context {RS_34280 : GLRS 0x34280}.
  Let rp_34280 : (0 <= sym 0x34280 /\ sym 0x34280 < 2^30)%Z := @rel_sym_pf _ RS_34280.
  Context {RS_22d30 : GLRS 0x22d30}.
  Let rp_22d30 : (0 <= sym 0x22d30 /\ sym 0x22d30 < 2^30)%Z := @rel_sym_pf _ RS_22d30.
  Context {RS_240a8 : GLRS 0x240a8}.
  Let rp_240a8 : (0 <= sym 0x240a8 /\ sym 0x240a8 < 2^30)%Z := @rel_sym_pf _ RS_240a8.
  Context {RS_342a8 : GLRS 0x342a8}.
  Let rp_342a8 : (0 <= sym 0x342a8 /\ sym 0x342a8 < 2^30)%Z := @rel_sym_pf _ RS_342a8.
  Context {RS_346d0 : GLRS 0x346d0}.
  Let rp_346d0 : (0 <= sym 0x346d0 /\ sym 0x346d0 < 2^30)%Z := @rel_sym_pf _ RS_346d0.
  Context {RS_346c0 : GLRS 0x346c0}.
  Let rp_346c0 : (0 <= sym 0x346c0 /\ sym 0x346c0 < 2^30)%Z := @rel_sym_pf _ RS_346c0.
  Context {RS_24048 : GLRS 0x24048}.
  Let rp_24048 : (0 <= sym 0x24048 /\ sym 0x24048 < 2^30)%Z := @rel_sym_pf _ RS_24048.
  Context {RS_23f58 : GLRS 0x23f58}.
  Let rp_23f58 : (0 <= sym 0x23f58 /\ sym 0x23f58 < 2^30)%Z := @rel_sym_pf _ RS_23f58.
  Context {RS_23f60 : GLRS 0x23f60}.
  Let rp_23f60 : (0 <= sym 0x23f60 /\ sym 0x23f60 < 2^30)%Z := @rel_sym_pf _ RS_23f60.
  Context {RS_23e70 : GLRS 0x23e70}.
  Let rp_23e70 : (0 <= sym 0x23e70 /\ sym 0x23e70 < 2^30)%Z := @rel_sym_pf _ RS_23e70.
  Context {RS_346e8 : GLRS 0x346e8}.
  Let rp_346e8 : (0 <= sym 0x346e8 /\ sym 0x346e8 < 2^30)%Z := @rel_sym_pf _ RS_346e8.
  Context {RS_346e0 : GLRS 0x346e0}.
  Let rp_346e0 : (0 <= sym 0x346e0 /\ sym 0x346e0 < 2^30)%Z := @rel_sym_pf _ RS_346e0.
  Context {RS_18390 : GLRS 0x18390}.
  Let rp_18390 : (0 <= sym 0x18390 /\ sym 0x18390 < 2^30)%Z := @rel_sym_pf _ RS_18390.
  Context {RS_1854c : GLRS 0x1854c}.
  Let rp_1854c : (0 <= sym 0x1854c /\ sym 0x1854c < 2^30)%Z := @rel_sym_pf _ RS_1854c.
  Context {RS_1cfd0 : GLRS 0x1cfd0}.
  Let rp_1cfd0 : (0 <= sym 0x1cfd0 /\ sym 0x1cfd0 < 2^30)%Z := @rel_sym_pf _ RS_1cfd0.
  Context {RS_183bc : GLRS 0x183bc}.
  Let rp_183bc : (0 <= sym 0x183bc /\ sym 0x183bc < 2^30)%Z := @rel_sym_pf _ RS_183bc.
  Context {RS_22e18 : GLRS 0x22e18}.
  Let rp_22e18 : (0 <= sym 0x22e18 /\ sym 0x22e18 < 2^30)%Z := @rel_sym_pf _ RS_22e18.
  Context {RS_34288 : GLRS 0x34288}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {RS_35000 : GLRS 0x35000}.
  Let rp_35000 : (0 <= sym 0x35000 /\ sym 0x35000 < 2^30)%Z := @rel_sym_pf _ RS_35000.
  Context {RL0_0 : ZFact ((sym 0x22d30) + 8 <= (sym 0x22d30 + 8))%Z}.
  Let rl0_0 : ((sym 0x22d30) + 8 <= (sym 0x22d30 + 8))%Z := @zfact_pf _ RL0_0.
  Context {RL0_1 : ZFact ((sym 0x22d30 + 8) + 0 <= (sym 0x22dd0))%Z}.
  Let rl0_1 : ((sym 0x22d30 + 8) + 0 <= (sym 0x22dd0))%Z := @zfact_pf _ RL0_1.
  Context {RL0_2 : ZFact ((sym 0x22dd0) + 16 <= (sym 0x22e18))%Z}.
  Let rl0_2 : ((sym 0x22dd0) + 16 <= (sym 0x22e18))%Z := @zfact_pf _ RL0_2.
  Context {RL0_3 : ZFact ((sym 0x22e18) + 8 <= (sym 0x22e20))%Z}.
  Let rl0_3 : ((sym 0x22e18) + 8 <= (sym 0x22e20))%Z := @zfact_pf _ RL0_3.
  Context {RL0_4 : ZFact ((sym 0x22e20) + 16 <= (sym 0x23e70))%Z}.
  Let rl0_4 : ((sym 0x22e20) + 16 <= (sym 0x23e70))%Z := @zfact_pf _ RL0_4.
  Context {RL0_5 : ZFact ((sym 0x23e70) + 232 <= (sym 0x23f58))%Z}.
  Let rl0_5 : ((sym 0x23e70) + 232 <= (sym 0x23f58))%Z := @zfact_pf _ RL0_5.
  Context {RL0_6 : ZFact ((sym 0x23f58) + 8 <= (sym 0x23f60))%Z}.
  Let rl0_6 : ((sym 0x23f58) + 8 <= (sym 0x23f60))%Z := @zfact_pf _ RL0_6.
  Context {RL0_7 : ZFact ((sym 0x23f60) + 232 <= (sym 0x24048))%Z}.
  Let rl0_7 : ((sym 0x23f60) + 232 <= (sym 0x24048))%Z := @zfact_pf _ RL0_7.
  Context {RL0_8 : ZFact ((sym 0x24048) + 8 <= (sym 0x240a8))%Z}.
  Let rl0_8 : ((sym 0x24048) + 8 <= (sym 0x240a8))%Z := @zfact_pf _ RL0_8.
  Context {RL0_9 : ZFact ((sym 0x240a8) + 1 <= (sym 0x341f8 + -200))%Z}.
  Let rl0_9 : ((sym 0x240a8) + 1 <= (sym 0x341f8 + -200))%Z := @zfact_pf _ RL0_9.
  Context {RL0_10 : ZFact ((sym 0x341f8 + -200) + 204 <= (sym 0x34280))%Z}.
  Let rl0_10 : ((sym 0x341f8 + -200) + 204 <= (sym 0x34280))%Z := @zfact_pf _ RL0_10.
  Context {RL0_11 : ZFact ((sym 0x34280) + 4 <= (sym 0x34288))%Z}.
  Let rl0_11 : ((sym 0x34280) + 4 <= (sym 0x34288))%Z := @zfact_pf _ RL0_11.
  Context {RL0_12 : ZFact ((sym 0x34288) + 8 <= (sym 0x342a8))%Z}.
  Let rl0_12 : ((sym 0x34288) + 8 <= (sym 0x342a8))%Z := @zfact_pf _ RL0_12.
  Context {RL0_13 : ZFact ((sym 0x342a8) + 8 <= (sym 0x346c0))%Z}.
  Let rl0_13 : ((sym 0x342a8) + 8 <= (sym 0x346c0))%Z := @zfact_pf _ RL0_13.
  Context {RL0_14 : ZFact ((sym 0x346c0) + 8 <= (sym 0x346d0))%Z}.
  Let rl0_14 : ((sym 0x346c0) + 8 <= (sym 0x346d0))%Z := @zfact_pf _ RL0_14.
  Context {RL0_15 : ZFact ((sym 0x346d0) + 8 <= (sym 0x346e0))%Z}.
  Let rl0_15 : ((sym 0x346d0) + 8 <= (sym 0x346e0))%Z := @zfact_pf _ RL0_15.
  Context {RL0_16 : ZFact ((sym 0x346e0) + 8 <= (sym 0x346e8))%Z}.
  Let rl0_16 : ((sym 0x346e0) + 8 <= (sym 0x346e8))%Z := @zfact_pf _ RL0_16.
  Context {RL0_17 : ZFact ((sym 0x346e8) + 1024 <= (sym 0x35000))%Z}.
  Let rl0_17 : ((sym 0x346e8) + 1024 <= (sym 0x35000))%Z := @zfact_pf _ RL0_17.
  Context {RL1_0 : ZFact ((sym 0x22e20) + 16 <= (sym 0x23e30))%Z}.
  Let rl1_0 : ((sym 0x22e20) + 16 <= (sym 0x23e30))%Z := @zfact_pf _ RL1_0.
  Context {RL1_1 : ZFact ((sym 0x23e30) + 8 <= (sym 0x23e70))%Z}.
  Let rl1_1 : ((sym 0x23e30) + 8 <= (sym 0x23e70))%Z := @zfact_pf _ RL1_1.
  Context {RL1_2 : ZFact ((sym 0x240a8) + 1 <= (sym 0x100034734))%Z}.
  Let rl1_2 : ((sym 0x240a8) + 1 <= (sym 0x100034734))%Z := @zfact_pf _ RL1_2.
  Context {RL1_3 : ZFact ((sym 0x100034734) + 1 <= (sym 0x341f8 + -200))%Z}.
  Let rl1_3 : ((sym 0x100034734) + 1 <= (sym 0x341f8 + -200))%Z := @zfact_pf _ RL1_3.
  Context {RL1_4 : ZFact ((sym 0x341f8 + -200) + 204 <= (sym 0x100034900))%Z}.
  Let rl1_4 : ((sym 0x341f8 + -200) + 204 <= (sym 0x100034900))%Z := @zfact_pf _ RL1_4.
  Context {RL1_5 : ZFact ((sym 0x100034900) + 296 <= (sym 0x34280))%Z}.
  Let rl1_5 : ((sym 0x100034900) + 296 <= (sym 0x34280))%Z := @zfact_pf _ RL1_5.
  Context {RL1_6 : ZFact (0 < sym 0x100015e4c)%Z}.
  Let rl1_6 : (0 < sym 0x100015e4c)%Z := @zfact_pf _ RL1_6.
  Context {RA_34280 : ZFact (sym 0x34280 mod 4 = 0)%Z}.
  Let ra_34280 : (sym 0x34280 mod 4 = 0)%Z := @zfact_pf _ RA_34280.
  Collection ImgHyps := IMG CODE_Exit RB_Exit CODE_Exit_1 RB_Exit_1 CODE_Exit_2 RB_Exit_2 CODE_Exit_3 RB_Exit_3 CODE_Exit_4 RB_Exit_4 CODE_Exit_5 RB_Exit_5 CODE_Exit_6 RB_Exit_6 CODE_Exit_7 RB_Exit_7 CODE_Exit_8 RB_Exit_8 CODE_Exit_9 RB_Exit_9 CODE_Exit_10 RB_Exit_10 RN_B_fox_15d30 RN_B_lock_fox RN_B_unlock_fox RN_B_cxa_1303c RS_K_ATEX rp_ATEX RS_K_INCB rp_INCB RS_K_CALL rp_CALL RS_K_GUARD rp_GUARD RS_K_CXA rp_CXA RS_23e30 rp_23e30 RL1_0 rl1_0 RL1_1 rl1_1 RL1_2 rl1_2 RL1_3 rl1_3 RL1_4 rl1_4 RL1_5 rl1_5 RL1_6 rl1_6 RN_B_15ce4_15d30 RN_B_stdio_exit_15d30 RN_B_15da4_15d30 RN_B_15ce0_15ce4 RS_K_34280 RS_K_22e20 RS_K_240a8 RS_K_22dd0 RS_K_23e30 RS_K_11988 RS_341f8 rp_341f8 RS_34280 rp_34280 RS_22d30 rp_22d30 RS_240a8 rp_240a8 RS_342a8 rp_342a8 RS_346d0 rp_346d0 RS_346c0 rp_346c0 RS_24048 rp_24048 RS_23f58 rp_23f58 RS_23f60 rp_23f60 RS_23e70 rp_23e70 RS_346e8 rp_346e8 RS_346e0 rp_346e0 RS_18390 rp_18390 RS_1854c rp_1854c RS_1cfd0 rp_1cfd0 RS_183bc rp_183bc RS_22e18 rp_22e18 RS_34288 rp_34288 RS_35000 rp_35000 RL0_0 rl0_0 RL0_1 rl0_1 RL0_2 rl0_2 RL0_3 rl0_3 RL0_4 rl0_4 RL0_5 rl0_5 RL0_6 rl0_6 RL0_7 rl0_7 RL0_8 rl0_8 RL0_9 rl0_9 RL0_10 rl0_10 RL0_11 rl0_11 RL0_12 rl0_12 RL0_13 rl0_13 RL0_14 rl0_14 RL0_15 rl0_15 RL0_16 rl0_16 RL0_17 rl0_17 RA_34280 ra_34280.


(* [comment removed for export] *)
Notation RTD := (sym 0x341f8 + -200)%Z (only parsing).
Notation RTP := (sym 0x341f8)%Z (only parsing).
(* [comment removed for export] *)
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
Open Scope bv_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 (sym 0x18390));
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 (sym 0x1854c)); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 z64;
   CB 80 tail].

Notation RSTDOUT := (sym 0x23f60)%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := (sym 0x346e8)%Z (only parsing).   (* [comment removed for export] *)
Notation RSTDERR := (sym 0x23e70)%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := (sym 0x1cfd0)%Z (only parsing).
Notation F_STDIO_WRITE := (sym 0x183bc)%Z (only parsing).

(* [comment removed for export] *)
Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
  exists (flags mode : word) (tail bufbytes : list byte),
    rw_cells img_segs m RSTDOUT
      (file_cells flags
         (if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
         (if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
         (if so_active so then RSTDOUT_BUF else 0)%Z
         (if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
         RSTDOUT_BUF 1024 1 mode
         (if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
    /\ Z.land (bv_unsigned flags) 72 = 0%Z
    /\ rw_cells img_segs m RSTDOUT_BUF [CB 1024 bufbytes]
    /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
    /\ (zlength (so_buf so) <= 1024)%Z
    /\ (so_active so = false -> so_buf so = []).

(* [comment removed for export] *)
Definition stderr_file (m : word -> option byte) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells img_segs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE (sym 0x346e0) 0 2 mode 0xffffffff tail).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdioExitStatement.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Definition stdio_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : word -> option byte) (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 so' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom img_segs)
      /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, (sym 0x24048)); (RSTDOUT_BUF, (sym 0x346e8 + 1024))]%Z m m'
      /\ wmono img_segs m m' /\ mem_inv img_segs m'
      /\ stk img_segs m' lo (bv_unsigned sp)
      /\ s' = set_so so' s
      /\ stdout_file m' so' /\ so_buf so' = [] 
      /\ stderr_file m'
      /\ rw_cells img_segs m' (sym 0x22e18) [C8 (Z_to_bv 64 (sym 0x34288))] /\ rw_cells img_segs m' (sym 0x34288) [C8 guard].

  Definition stdio_exit_spec_stmt : Prop :=
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk img_segs m lo (bv_unsigned sp) ->
      rw_cells img_segs m (sym 0x342a8) [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
      rw_cells img_segs m (sym 0x346d0) [C8 z64] ->                                            (* [comment removed for export] *)
      rw_cells img_segs m (sym 0x346c0) [C8 z64] ->                                            (* [comment removed for export] *)
      rw_cells img_segs m (sym 0x24048) [C8 (Z_to_bv 64 RSTDOUT)] ->                          (* [comment removed for export] *)
      rw_cells img_segs m (sym 0x23f58) [C8 (Z_to_bv 64 RSTDERR)] ->                          (* [comment removed for export] *)
      stdout_file m (get_so s) -> stderr_file m ->
      rw_cells img_segs m (sym 0x22e18) [C8 (Z_to_bv 64 (sym 0x34288))] -> rw_cells img_segs m (sym 0x34288) [C8 guard] ->   (* [comment removed for export] *)
      mem_inv img_segs m ->
      tp = Z_to_bv 64 RTP ->
      (lo <= bv_unsigned sp - 160)%Z -> ((sym 0x35000) <= lo)%Z ->
      implM img_segs (stdout_exit_flush get_so set_so) s
            (stdio_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (sym 0x17f94)) fc None m (seg_rom img_segs)).
End StdioExitStatement.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition atex_cells (ph : bool) : list cell :=
  [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C4 z64; C4 (Z_to_bv 64 (if ph then 1 else 0)); C4 z64;
   C8 (Z_to_bv 64 (if ph then sym 0x100034900 + 24 else 0)); C8 z64; C8 (Z_to_bv 64 (if ph then sym 0x100015f14 else 0))].
Definition ATEX (ph : bool) (m : word -> option byte) : Prop :=
  rw_cells img_segs m (sym 0x100034900) (atex_cells ph)
  /\ rw_cells img_segs m (sym 0x100034900 + 288) [C8 (Z_to_bv 64 (if ph then sym 0x10001351c else 0))].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code t : Z) (td0 td1 td2 td3 ra : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 (sym 0x15d30 + 108)) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 (sym 0x17f94)) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); ((sym 0x34280), (sym 0x34280 + 4)); ((sym 0x240a8), (sym 0x240a8 + 1));
              ((sym 0x100034900), (sym 0x100034900 + 24))]%Z m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' lo (bv_unsigned sp + -16)
    /\ rw_cells img_segs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells img_segs m' RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
    /\ rw_cells img_segs m' (sym 0x34280) [C4 (Z_to_bv 64 t)]
    /\ rw_cells img_segs m' (sym 0x240a8) [C1 (Z_to_bv 8 1)].

Lemma rexit_prefix_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 : word)
    (ph : bool) (cdt thr sec : byte) (tm1 : word),
  stk img_segs m lo (bv_unsigned sp) ->
  rw_cells img_segs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->      (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x34280) [C4 z64] ->                                              (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x22e20) [C8 (Z_to_bv 64 (sym 0x22d30 + 8)); C8 (Z_to_bv 64 (sym 0x22d30))] ->    (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x22d30) [C8 (Z_to_bv 64 (sym 0x1303c))] ->                            (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x240a8) [C1 (Z_to_bv 8 0)] ->                                    (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x22dd0) [C8 (Z_to_bv 64 (sym 0x100015e4c)); C8 z64] ->         (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x23e30) [C8 (Z_to_bv 64 (sym 0x23e30))] ->                     (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x342a8) [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->  (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x100034734) [C1 (Z_to_bv 8 0)] ->                             (* [comment removed for export] *)
  ATEX ph m ->                                                                              (* [comment removed for export] *)
  mem_inv img_segs m ->
  tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
  (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 64)%Z -> ((sym 0x35000) <= lo)%Z ->
  evt img_segs (rexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x15d30)) fc None m (seg_rom img_segs)).
Proof.
  intros until tm1. intros ST TDa EXL GF FA FIN GCX DSO LCH INCB (ATX & ATXA) MI -> -> Ht LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); ((sym 0x34280), (sym 0x34280 + 4)); ((sym 0x240a8), (sym 0x240a8 + 1));
              ((sym 0x100034900), (sym 0x100034900 + 24))]%Z m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  unfold atex_cells in ATX.
  carve_frame 16%nat ST.
  do 6 lstep.
  replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
    by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
  lstep. lstep.
  (* [comment removed for export] *)
  amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
  lstep. if_false. amo_step. lstep. if_false.
  lstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
  lstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. lstep. if_true.
  steps_to (sym 0x100015d84)%Z.
  (* [comment removed for export] *)
  carve_frame 48%nat ST.
  destruct ph.
  - (* [comment removed for export] *)
    steps_to (sym 0x21964)%Z. steps_to (sym 0x100015d84 + 44)%Z.        (* [comment removed for export] *)
    astep. astep.                                                         (* [comment removed for export] *)
    lstep. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).   (* [comment removed for export] *)
    astep. lstep.                                                         (* [comment removed for export] *)
    steps_to (sym 0x21bec)%Z.                                             (* [comment removed for export] *)
    lstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. astep.            (* [comment removed for export] *)
    steps_to (sym 0x10001351c)%Z.                                         (* [comment removed for export] *)
    lstep. lstep. cbv beta. replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 0))) with z64 by (vm_compute; reflexivity).
    astep. astep.                                                         (* [comment removed for export] *)
    steps_to (sym 0x21964)%Z. steps_to (sym 0x100015d84 + 136)%Z.       (* [comment removed for export] *)
    lstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). lstep.   (* [comment removed for export] *)
    lstep. astep.                                                         (* [comment removed for export] *)
    steps_to (sym 0x100015d84 + 192)%Z.                                   (* [comment removed for export] *)
    release_frame FR0 ST (bv_unsigned sp + -16)%Z. astep. astep.         (* [comment removed for export] *)
    lstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. astep.            (* [comment removed for export] *)
    steps_to (sym 0x15ce4)%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. steps_to (sym 0x1303c)%Z.
    carve_frame 16%nat ST. steps_to (sym 0x1303c + 140)%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. astep.
    steps_to (sym 0x15ce4 + 72)%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z. astep. astep.
    astep.
    unfold rexit_prefix_post. sys_finish.
  - (* [comment removed for export] *)
    steps_to (sym 0x21964)%Z. steps_to (sym 0x100015d84 + 44)%Z.
    astep. astep.                                                         (* [comment removed for export] *)
    steps_to (sym 0x100015d84 + 192)%Z.                                   (* [comment removed for export] *)
    release_frame FR0 ST (bv_unsigned sp + -16)%Z. astep. astep.
    lstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. astep.
    steps_to (sym 0x15ce4)%Z.
    carve_frame 32%nat ST. steps_to (sym 0x1303c)%Z.
    carve_frame 16%nat ST. steps_to (sym 0x1303c + 140)%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. astep.
    steps_to (sym 0x15ce4 + 72)%Z. release_frame FR0 ST (bv_unsigned sp + -16)%Z. astep. astep.
    astep.
    unfold rexit_prefix_post. sys_finish.
Time Qed.

(* [comment removed for export] *)
Definition rexit_prefix_spec_c : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 : word)
    (ph : bool) (cdt thr sec : byte) (tm1 : word),
  stk img_segs m lo (bv_unsigned sp) ->
  rw_cells img_segs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->      (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x34280) [C4 z64] ->                                              (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x22e20) [C8 (Z_to_bv 64 (sym 0x22d30 + 8)); C8 (Z_to_bv 64 (sym 0x22d30))] ->    (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x22d30) [C8 (Z_to_bv 64 (sym 0x1303c))] ->                            (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x240a8) [C1 (Z_to_bv 8 0)] ->                                    (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x22dd0) [C8 (Z_to_bv 64 (sym 0x100015e4c)); C8 z64] ->         (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x23e30) [C8 (Z_to_bv 64 (sym 0x23e30))] ->                     (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x342a8) [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->  (* [comment removed for export] *)
  rw_cells img_segs m (sym 0x100034734) [C1 (Z_to_bv 8 0)] ->                             (* [comment removed for export] *)
  ATEX ph m ->                                                                              (* [comment removed for export] *)
  mem_inv img_segs m ->
  tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
  (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 64)%Z -> ((sym 0x35000) <= lo)%Z ->
  evt img_segs (rexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t td0 td1 td2 td3 ra m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (sym 0x15d30)) fc None m (seg_rom img_segs)).
Lemma rexit_prefix_spec_c_ok : rexit_prefix_spec_c.
Proof. exact rexit_prefix_spec. Qed.


Section ExitProof.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  (* [comment removed for export] *)
  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt get_so set_so.

  Lemma exit_spec : forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard : word)
      (cdt thr sec : byte) (tm1 : word) (ph : bool),
    stk img_segs m lo (bv_unsigned sp) ->
    rw_cells img_segs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->      (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x34280) [C4 z64] ->                                              (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x22e20) [C8 (Z_to_bv 64 (sym 0x22d30 + 8)); C8 (Z_to_bv 64 (sym 0x22d30))] ->    (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x22d30) [C8 (Z_to_bv 64 (sym 0x1303c))] ->                            (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x240a8) [C1 (Z_to_bv 8 0)] ->                                    (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x22dd0) [C8 (Z_to_bv 64 (sym 0x100015e4c)); C8 z64] ->         (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x23e30) [C8 (Z_to_bv 64 (sym 0x23e30))] ->                     (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x100034734) [C1 (Z_to_bv 8 0)] ->                             (* [comment removed for export] *)
    ATEX ph m ->                                                                              (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x342a8) [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells img_segs m (sym 0x346d0) [C8 z64] -> rw_cells img_segs m (sym 0x346c0) [C8 z64] ->
    rw_cells img_segs m (sym 0x24048) [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells img_segs m (sym 0x23f58) [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells img_segs m (sym 0x22e18) [C8 (Z_to_bv 64 (sym 0x34288))] -> rw_cells img_segs m (sym 0x34288) [C8 guard] ->
    mem_inv img_segs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 176)%Z -> ((sym 0x35000) <= lo)%Z ->
    implM img_segs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 (sym 0x15d30)) fc None m (seg_rom img_segs)).
  Proof.
    intros until ph. intros ST TDa EXL GF FA FIN GCX DSO INCB ATX LCH OFL SIN SOU SEU SOF SEF GG GU MI -> -> Ht LO LOLO.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    (* [comment removed for export] *)
    (nelim SOF 10%nat; intros flg mode tail bufb SOF1 SOF2 SOF3 SOF4 SOF5 SOF6).
    (nelim SEF 6%nat; intros flg' mode' ee wend' tail' SEF1).
    unfold file_cells in SOF1, SEF1.
    unfold Driver.exit_model.
    eapply (implM_bind img_segs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 (sym 0x15d30 + 108)) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 (sym 0x15d30 + 108)) fc None m' (seg_rom img_segs))).
    - (* [comment removed for export] *)
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      unfold implM. iprefix.
      call rexit_prefix_spec; [exact ST | exact TDa | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact DSO | exact LCH | exact INCB | exact ATX | exact MI
                              | reflexivity | reflexivity | lia | lia | lia | ].
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt, implM in SE.
      apply evt_done. eapply impl_epost_mono; [eapply SE|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 (sym 0x15d30 + 108))) with (Z_to_bv 64 (sym 0x15d30 + 108)) by (symmetry; apply ret_pc_sym; arel_side);
               repeat eexists; cbv delta [mkR]; reflexivity
           | |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
           | |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
           | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia ]
           end.
    - (* [comment removed for export] *)
      clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
      intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
  Time Qed.

(* [comment removed for export] *)
Definition exit_spec_c : Prop := forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z) (td0 td1 td2 td3 guard : word)
      (cdt thr sec : byte) (tm1 : word) (ph : bool),
    stk img_segs m lo (bv_unsigned sp) ->
    rw_cells img_segs m RTD [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->      (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x34280) [C4 z64] ->                                              (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x22e20) [C8 (Z_to_bv 64 (sym 0x22d30 + 8)); C8 (Z_to_bv 64 (sym 0x22d30))] ->    (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x22d30) [C8 (Z_to_bv 64 (sym 0x1303c))] ->                            (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x240a8) [C1 (Z_to_bv 8 0)] ->                                    (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x22dd0) [C8 (Z_to_bv 64 (sym 0x100015e4c)); C8 z64] ->         (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x23e30) [C8 (Z_to_bv 64 (sym 0x23e30))] ->                     (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x100034734) [C1 (Z_to_bv 8 0)] ->                             (* [comment removed for export] *)
    ATEX ph m ->                                                                              (* [comment removed for export] *)
    rw_cells img_segs m (sym 0x342a8) [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells img_segs m (sym 0x346d0) [C8 z64] -> rw_cells img_segs m (sym 0x346c0) [C8 z64] ->
    rw_cells img_segs m (sym 0x24048) [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells img_segs m (sym 0x23f58) [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells img_segs m (sym 0x22e18) [C8 (Z_to_bv 64 (sym 0x34288))] -> rw_cells img_segs m (sym 0x34288) [C8 guard] ->
    mem_inv img_segs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 176)%Z -> ((sym 0x35000) <= lo)%Z ->
    implM img_segs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 (sym 0x15d30)) fc None m (seg_rom img_segs)).
Lemma exit_spec_c_ok : exit_spec_c.
Proof. exact exit_spec. Qed.

End ExitProof.

End Img.
(* [comment removed for export] *)
Notation RTD := (sym 0x341f8 + -200)%Z (only parsing).
Notation RTP := (sym 0x341f8)%Z (only parsing).
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.
Notation RSTDOUT := (sym 0x23f60)%Z (only parsing).
Notation RSTDOUT_BUF := (sym 0x346e8)%Z (only parsing).
Notation RSTDERR := (sym 0x23e70)%Z (only parsing).
Notation F_STDOUT_WRITE := (sym 0x1cfd0)%Z (only parsing).
Notation F_STDIO_WRITE := (sym 0x183bc)%Z (only parsing).

(* [comment removed for export] *)
Existing Class rexit_prefix_spec_c.
Existing Class exit_spec_c.
