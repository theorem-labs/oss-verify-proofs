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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Arr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require Exit_tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RProgAt.
Module GSTRW_tac.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Tac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Arr OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Bytes.
Export OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.

Ltac cur_dec segs pc :=
  let B := apc_base pc in
  match goal with
  | CODE : CodeAtT segs B ?t |- _ => let k := apc_off pc in find_t_eval k t
  | CODE : CodeAt segs B ?p |- _ => let k := apc_off pc in find_off_eval k p
  | CODE : code_at segs B ?p |- _ => let k := apc_off pc in find_off_eval k p
  | _ => concrete_segs segs; let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
         lazymatch fw with Some ?w => eval vm_compute in (decode_any w) end
  end.

Ltac acur_mem_addr :=
  lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let d := cur_dec segs pc in
    lazymatch d with
    | Some (Load _ _ _ ?rs ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    | Some (Store _ ?rs _ ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    end end.
End GSTRW_tac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require Exit_tac.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.Exit_tac.STRW_tac.
Import GSTRW_tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import StoreCache. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import NElim. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require JunkAbs.
(* [comment removed for export] *)
Import ListNotations.

(* [comment removed for export] *)
Definition memcpy_prog (B : Z) : RStep.ptree :=
  PNode 512%Z
  (PNode 256%Z
    (PNode 128%Z
      (PNode 64%Z
        (PLeaf
            (PJ_OpImm_ALU_AND_nnn 0 13 11 3 4
            (PJ_Branch_BC_EQ_nnn 4 13 0 272 4
            (PJ_Branch_BC_EQ_nnn 8 12 0 60 4
            (PJ_OpImm_ALU_ADD_nnn 12 14 11 1 4
            (PJ_OpImm_ALU_ADD_nnn 16 15 0 1 4
            (PJ_OpImm_ALU_ADD_nnn 20 13 10 0 4
            (PJ_Load_SZ1_false_nnn 24 17 11 0 4
            (PJ_OpImm_ALU_ADD_nnn 28 16 12 0 4
            (PJ_OpImm_ALU_ADD_nnn 32 11 11 1 4
            (PJ_OpImm_ALU_AND_nnn 36 5 14 3 4
            (PJ_Store_SZ1_nnn 40 13 17 0 4
            (PJ_OpImm_ALU_ADD_nnn 44 13 13 1 4
            (PJ_OpImm_ALU_ADD_nnn 48 12 12 4095 4
            (PJ_Branch_BC_EQ_nnn 52 5 0 20 4
            (PJ_OpImm_ALU_ADD_nnn 56 14 14 1 4
            (PJ_Branch_BC_NE_nnn 60 16 15 8156 4 nil)))))))))))))))))
        (PLeaf
            (PJ_Jal_nn 64 0 8 4
            (PJ_OpImm_ALU_ADD_nnn 68 13 10 0 4
            (PJ_OpImm_ALU_AND_nnn 72 15 13 3 4
            (PJ_Branch_BC_EQ_nnn 76 15 0 212 4
            (PJ_OpImm_ALU_ADD_nnn 80 14 0 32 4
            (PJ_Branch_BC_GEU_nnn 84 12 14 32 4
            (PJ_OpImm_ALU_ADD_nnn 88 14 0 16 4
            (PJ_Branch_BC_GEU_nnn 92 12 14 592 4
            (PJ_OpImm_ALU_AND_nnn 96 14 12 8 4
            (PJ_Branch_BC_NE_nnn 100 14 0 732 4
            (PJ_OpImm_ALU_AND_nnn 104 14 12 4 4
            (PJ_Branch_BC_NE_nnn 108 14 0 808 4
            (PJ_Jal_nn 112 0 848 4
            (PJ_Load_SZ4_true_nnn 116 14 11 0 4
            (PJ_OpImm_ALU_ADD_nnn 120 16 0 3 4
            (PJ_Branch_BC_EQ_nnn 124 15 16 284 4 nil))))))))))))))))))
      (PNode 192%Z
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 128 16 0 2 4
            (PJ_Branch_BC_NE_nnn 132 15 16 408 4
            (PJ_ShiftImm_ALU_SRL_nnn 136 15 14 8 4
            (PJ_OpImm_ALU_ADD_nnn 140 12 12 4094 4
            (PJ_Store_SZ1_nnn 144 13 14 0 4
            (PJ_Store_SZ1_nnn 148 13 15 1 4
            (PJ_OpImm_ALU_ADD_nnn 152 13 13 2 4
            (PJ_OpImm_ALU_ADD_nnn 156 11 11 16 4
            (PJ_OpImm_ALU_ADD_nnn 160 15 0 17 4
            (PJ_ShiftImm32_ALU_SRL_nnn 164 16 14 16 4
            (PJ_Load_SZ4_true_nnn 168 17 11 4084 4
            (PJ_Load_SZ4_true_nnn 172 5 11 4088 4
            (PJ_Load_SZ4_true_nnn 176 6 11 4092 4
            (PJ_Load_SZ4_true_nnn 180 14 11 0 4
            (PJ_ShiftImm_ALU_SLL_nnn 184 7 17 16 4
            (PJ_ShiftImm32_ALU_SRL_nnn 188 17 17 16 4 nil)))))))))))))))))
        (PLeaf
            (PJ_Op_ALU_OR_nnn 192 16 7 16 4
            (PJ_ShiftImm_ALU_SLL_nnn 196 7 5 16 4
            (PJ_ShiftImm32_ALU_SRL_nnn 200 5 5 16 4
            (PJ_Op_ALU_OR_nnn 204 17 7 17 4
            (PJ_ShiftImm_ALU_SLL_nnn 208 7 6 16 4
            (PJ_ShiftImm32_ALU_SRL_nnn 212 6 6 16 4
            (PJ_Op_ALU_OR_nnn 216 5 7 5 4
            (PJ_ShiftImm_ALU_SLL_nnn 220 7 14 16 4
            (PJ_Op_ALU_OR_nnn 224 6 7 6 4
            (PJ_OpImm_ALU_ADD_nnn 228 12 12 4080 4
            (PJ_Store_SZ4_nnn 232 13 16 0 4
            (PJ_Store_SZ4_nnn 236 13 17 4 4
            (PJ_Store_SZ4_nnn 240 13 5 8 4
            (PJ_Store_SZ4_nnn 244 13 6 12 4
            (PJ_OpImm_ALU_ADD_nnn 248 13 13 16 4
            (PJ_OpImm_ALU_ADD_nnn 252 11 11 16 4 nil)))))))))))))))))))
    (PNode 384%Z
      (PNode 320%Z
        (PLeaf
            (PJ_Branch_BC_LTU_nnn 256 15 12 8100 4
            (PJ_OpImm_ALU_ADD_nnn 260 11 11 4082 4
            (PJ_OpImm_ALU_ADD_nnn 264 14 0 16 4
            (PJ_Branch_BC_LTU_nnn 268 12 14 8020 4
            (PJ_Jal_nn 272 0 412 4
            (PJ_OpImm_ALU_ADD_nnn 276 13 10 0 4
            (PJ_OpImm_ALU_AND_nnn 280 15 10 3 4
            (PJ_Branch_BC_NE_nnn 284 15 0 7988 4
            (PJ_OpImm_ALU_ADD_nnn 288 14 0 16 4
            (PJ_Branch_BC_LTU_nnn 292 12 14 56 4
            (PJ_OpImm_ALU_ADD_nnn 296 14 0 15 4
            (PJ_Load_SZ4_true_nnn 300 15 11 0 4
            (PJ_Load_SZ4_true_nnn 304 16 11 4 4
            (PJ_Load_SZ4_true_nnn 308 17 11 8 4
            (PJ_Load_SZ4_true_nnn 312 5 11 12 4
            (PJ_OpImm_ALU_ADD_nnn 316 11 11 16 4 nil)))))))))))))))))
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 320 12 12 4080 4
            (PJ_Store_SZ4_nnn 324 13 15 0 4
            (PJ_Store_SZ4_nnn 328 13 16 4 4
            (PJ_Store_SZ4_nnn 332 13 17 8 4
            (PJ_Store_SZ4_nnn 336 13 5 12 4
            (PJ_OpImm_ALU_ADD_nnn 340 13 13 16 4
            (PJ_Branch_BC_LTU_nnn 344 14 12 8148 4
            (PJ_OpImm_ALU_ADD_nnn 348 14 0 8 4
            (PJ_Branch_BC_LTU_nnn 352 12 14 28 4
            (PJ_Load_SZ4_true_nnn 356 14 11 0 4
            (PJ_Load_SZ4_true_nnn 360 15 11 4 4
            (PJ_Store_SZ4_nnn 364 13 14 0 4
            (PJ_Store_SZ4_nnn 368 13 15 4 4
            (PJ_OpImm_ALU_ADD_nnn 372 13 13 8 4
            (PJ_OpImm_ALU_ADD_nnn 376 11 11 8 4
            (PJ_OpImm_ALU_AND_nnn 380 14 12 4 4 nil))))))))))))))))))
      (PNode 448%Z
        (PLeaf
            (PJ_Branch_BC_EQ_nnn 384 14 0 576 4
            (PJ_Load_SZ4_true_nnn 388 14 11 0 4
            (PJ_OpImm_ALU_ADD_nnn 392 11 11 4 4
            (PJ_Store_SZ4_nnn 396 13 14 0 4
            (PJ_OpImm_ALU_ADD_nnn 400 13 13 4 4
            (PJ_Jal_nn 404 0 556 4
            (PJ_Store_SZ1_nnn 408 13 14 0 4
            (PJ_OpImm_ALU_ADD_nnn 412 13 13 1 4
            (PJ_OpImm_ALU_ADD_nnn 416 12 12 4095 4
            (PJ_OpImm_ALU_ADD_nnn 420 11 11 16 4
            (PJ_OpImm_ALU_ADD_nnn 424 15 0 18 4
            (PJ_ShiftImm32_ALU_SRL_nnn 428 16 14 8 4
            (PJ_Load_SZ4_true_nnn 432 17 11 4084 4
            (PJ_Load_SZ4_true_nnn 436 5 11 4088 4
            (PJ_Load_SZ4_true_nnn 440 6 11 4092 4
            (PJ_Load_SZ4_true_nnn 444 14 11 0 4 nil)))))))))))))))))
        (PLeaf
            (PJ_ShiftImm_ALU_SLL_nnn 448 7 17 24 4
            (PJ_ShiftImm32_ALU_SRL_nnn 452 17 17 8 4
            (PJ_Op_ALU_OR_nnn 456 16 7 16 4
            (PJ_ShiftImm_ALU_SLL_nnn 460 7 5 24 4
            (PJ_ShiftImm32_ALU_SRL_nnn 464 5 5 8 4
            (PJ_Op_ALU_OR_nnn 468 17 7 17 4
            (PJ_ShiftImm_ALU_SLL_nnn 472 7 6 24 4
            (PJ_ShiftImm32_ALU_SRL_nnn 476 6 6 8 4
            (PJ_Op_ALU_OR_nnn 480 5 7 5 4
            (PJ_ShiftImm_ALU_SLL_nnn 484 7 14 24 4
            (PJ_Op_ALU_OR_nnn 488 6 7 6 4
            (PJ_OpImm_ALU_ADD_nnn 492 12 12 4080 4
            (PJ_Store_SZ4_nnn 496 13 16 0 4
            (PJ_Store_SZ4_nnn 500 13 17 4 4
            (PJ_Store_SZ4_nnn 504 13 5 8 4
            (PJ_Store_SZ4_nnn 508 13 6 12 4 nil))))))))))))))))))))
  (PNode 768%Z
    (PNode 640%Z
      (PNode 576%Z
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 512 13 13 16 4
            (PJ_OpImm_ALU_ADD_nnn 516 11 11 16 4
            (PJ_Branch_BC_LTU_nnn 520 15 12 8100 4
            (PJ_OpImm_ALU_ADD_nnn 524 11 11 4081 4
            (PJ_OpImm_ALU_ADD_nnn 528 14 0 16 4
            (PJ_Branch_BC_LTU_nnn 532 12 14 7756 4
            (PJ_Jal_nn 536 0 148 4
            (PJ_ShiftImm_ALU_SRL_nnn 540 15 14 8 4
            (PJ_ShiftImm_ALU_SRL_nnn 544 16 14 16 4
            (PJ_OpImm_ALU_ADD_nnn 548 12 12 4093 4
            (PJ_Store_SZ1_nnn 552 13 14 0 4
            (PJ_Store_SZ1_nnn 556 13 15 1 4
            (PJ_Store_SZ1_nnn 560 13 16 2 4
            (PJ_OpImm_ALU_ADD_nnn 564 13 13 3 4
            (PJ_OpImm_ALU_ADD_nnn 568 11 11 16 4
            (PJ_OpImm_ALU_ADD_nnn 572 15 0 16 4 nil)))))))))))))))))
        (PLeaf
            (PJ_ShiftImm32_ALU_SRL_nnn 576 16 14 24 4
            (PJ_Load_SZ4_true_nnn 580 17 11 4084 4
            (PJ_Load_SZ4_true_nnn 584 5 11 4088 4
            (PJ_Load_SZ4_true_nnn 588 6 11 4092 4
            (PJ_Load_SZ4_true_nnn 592 14 11 0 4
            (PJ_ShiftImm_ALU_SLL_nnn 596 7 17 8 4
            (PJ_ShiftImm32_ALU_SRL_nnn 600 17 17 24 4
            (PJ_Op_ALU_OR_nnn 604 16 7 16 4
            (PJ_ShiftImm_ALU_SLL_nnn 608 7 5 8 4
            (PJ_ShiftImm32_ALU_SRL_nnn 612 5 5 24 4
            (PJ_Op_ALU_OR_nnn 616 17 7 17 4
            (PJ_ShiftImm_ALU_SLL_nnn 620 7 6 8 4
            (PJ_ShiftImm32_ALU_SRL_nnn 624 6 6 24 4
            (PJ_Op_ALU_OR_nnn 628 5 7 5 4
            (PJ_ShiftImm_ALU_SLL_nnn 632 7 14 8 4
            (PJ_Op_ALU_OR_nnn 636 6 7 6 4 nil))))))))))))))))))
      (PNode 704%Z
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 640 12 12 4080 4
            (PJ_Store_SZ4_nnn 644 13 16 0 4
            (PJ_Store_SZ4_nnn 648 13 17 4 4
            (PJ_Store_SZ4_nnn 652 13 5 8 4
            (PJ_Store_SZ4_nnn 656 13 6 12 4
            (PJ_OpImm_ALU_ADD_nnn 660 13 13 16 4
            (PJ_OpImm_ALU_ADD_nnn 664 11 11 16 4
            (PJ_Branch_BC_LTU_nnn 668 15 12 8100 4
            (PJ_OpImm_ALU_ADD_nnn 672 11 11 4083 4
            (PJ_OpImm_ALU_ADD_nnn 676 14 0 16 4
            (PJ_Branch_BC_LTU_nnn 680 12 14 7608 4
            (PJ_Load_SZ1_false_nnn 684 14 11 0 4
            (PJ_Load_SZ1_false_nnn 688 15 11 1 4
            (PJ_Load_SZ1_false_nnn 692 16 11 2 4
            (PJ_Load_SZ1_false_nnn 696 17 11 3 4
            (PJ_Load_SZ1_false_nnn 700 5 11 4 4 nil)))))))))))))))))
        (PLeaf
            (PJ_Load_SZ1_false_nnn 704 6 11 5 4
            (PJ_Load_SZ1_false_nnn 708 7 11 6 4
            (PJ_Load_SZ1_false_nnn 712 28 11 7 4
            (PJ_Store_SZ1_nnn 716 13 14 0 4
            (PJ_Store_SZ1_nnn 720 13 15 1 4
            (PJ_Store_SZ1_nnn 724 13 16 2 4
            (PJ_Store_SZ1_nnn 728 13 17 3 4
            (PJ_Load_SZ1_false_nnn 732 14 11 8 4
            (PJ_Load_SZ1_false_nnn 736 15 11 9 4
            (PJ_Load_SZ1_false_nnn 740 16 11 10 4
            (PJ_Load_SZ1_false_nnn 744 17 11 11 4
            (PJ_Store_SZ1_nnn 748 13 5 4 4
            (PJ_Store_SZ1_nnn 752 13 6 5 4
            (PJ_Store_SZ1_nnn 756 13 7 6 4
            (PJ_Store_SZ1_nnn 760 13 28 7 4
            (PJ_Load_SZ1_false_nnn 764 5 11 12 4 nil)))))))))))))))))))
    (PNode 896%Z
      (PNode 832%Z
        (PLeaf
            (PJ_Load_SZ1_false_nnn 768 6 11 13 4
            (PJ_Load_SZ1_false_nnn 772 7 11 14 4
            (PJ_Load_SZ1_false_nnn 776 28 11 15 4
            (PJ_OpImm_ALU_ADD_nnn 780 11 11 16 4
            (PJ_Store_SZ1_nnn 784 13 14 8 4
            (PJ_Store_SZ1_nnn 788 13 15 9 4
            (PJ_Store_SZ1_nnn 792 13 16 10 4
            (PJ_Store_SZ1_nnn 796 13 17 11 4
            (PJ_OpImm_ALU_ADD_nnn 800 14 13 16 4
            (PJ_Store_SZ1_nnn 804 13 5 12 4
            (PJ_Store_SZ1_nnn 808 13 6 13 4
            (PJ_Store_SZ1_nnn 812 13 7 14 4
            (PJ_Store_SZ1_nnn 816 13 28 15 4
            (PJ_OpImm_ALU_ADD_nnn 820 13 14 0 4
            (PJ_OpImm_ALU_AND_nnn 824 14 12 8 4
            (PJ_Branch_BC_EQ_nnn 828 14 0 7468 4 nil)))))))))))))))))
        (PLeaf
            (PJ_Load_SZ1_false_nnn 832 14 11 0 4
            (PJ_Load_SZ1_false_nnn 836 15 11 1 4
            (PJ_Load_SZ1_false_nnn 840 16 11 2 4
            (PJ_Load_SZ1_false_nnn 844 17 11 3 4
            (PJ_Load_SZ1_false_nnn 848 5 11 4 4
            (PJ_Load_SZ1_false_nnn 852 6 11 5 4
            (PJ_Load_SZ1_false_nnn 856 7 11 6 4
            (PJ_Load_SZ1_false_nnn 860 28 11 7 4
            (PJ_OpImm_ALU_ADD_nnn 864 11 11 8 4
            (PJ_Store_SZ1_nnn 868 13 14 0 4
            (PJ_Store_SZ1_nnn 872 13 15 1 4
            (PJ_Store_SZ1_nnn 876 13 16 2 4
            (PJ_Store_SZ1_nnn 880 13 17 3 4
            (PJ_OpImm_ALU_ADD_nnn 884 14 13 8 4
            (PJ_Store_SZ1_nnn 888 13 5 4 4
            (PJ_Store_SZ1_nnn 892 13 6 5 4 nil))))))))))))))))))
      (PNode 960%Z
        (PLeaf
            (PJ_Store_SZ1_nnn 896 13 7 6 4
            (PJ_Store_SZ1_nnn 900 13 28 7 4
            (PJ_OpImm_ALU_ADD_nnn 904 13 14 0 4
            (PJ_OpImm_ALU_AND_nnn 908 14 12 4 4
            (PJ_Branch_BC_EQ_nnn 912 14 0 48 4
            (PJ_Load_SZ1_false_nnn 916 14 11 0 4
            (PJ_Load_SZ1_false_nnn 920 15 11 1 4
            (PJ_Load_SZ1_false_nnn 924 16 11 2 4
            (PJ_Load_SZ1_false_nnn 928 17 11 3 4
            (PJ_OpImm_ALU_ADD_nnn 932 11 11 4 4
            (PJ_OpImm_ALU_ADD_nnn 936 5 13 4 4
            (PJ_Store_SZ1_nnn 940 13 14 0 4
            (PJ_Store_SZ1_nnn 944 13 15 1 4
            (PJ_Store_SZ1_nnn 948 13 16 2 4
            (PJ_Store_SZ1_nnn 952 13 17 3 4
            (PJ_OpImm_ALU_ADD_nnn 956 13 5 0 4 nil)))))))))))))))))
        (PNode 992%Z
          (PLeaf
              (PJ_OpImm_ALU_AND_nnn 960 14 12 2 4
              (PJ_Branch_BC_NE_nnn 964 14 0 16 4
              (PJ_OpImm_ALU_AND_nnn 968 12 12 1 4
              (PJ_Branch_BC_NE_nnn 972 12 0 44 4
              (PJ_Jalr_nnn 976 0 1 0 4
              (PJ_Load_SZ1_false_nnn 980 14 11 0 4
              (PJ_Load_SZ1_false_nnn 984 15 11 1 4
              (PJ_OpImm_ALU_ADD_nnn 988 11 11 2 4 nil)))))))))
          (PLeaf
              (PJ_OpImm_ALU_ADD_nnn 992 16 13 2 4
              (PJ_Store_SZ1_nnn 996 13 14 0 4
              (PJ_Store_SZ1_nnn 1000 13 15 1 4
              (PJ_OpImm_ALU_ADD_nnn 1004 13 16 0 4
              (PJ_OpImm_ALU_AND_nnn 1008 12 12 1 4
              (PJ_Branch_BC_EQ_nnn 1012 12 0 8156 4
              (PJ_Load_SZ1_false_nnn 1016 11 11 0 4
              (PJ_Store_SZ1_nnn 1020 13 11 0 4
              (PJ_Jalr_nnn 1024 0 1 0 4 nil)))))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m. (* [comment removed for export] *) Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mem_after_store ::= mem_after_store_cached. Local Ltac addr_eq_tac ::= addr_eq_tac_cached. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM. Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.

Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.Exit_tac.STRW_tac.cur_mem_addr ::= GSTRW_tac.acur_mem_addr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_memcpy (IMG : RImg) := memcpy_prog (sym 0x21334).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_memcpy : CodeAtT img_segs (sym 0x21334) (PROGAT_CODE_memcpy IMG)}.
  Context {RB_memcpy : RelCode (sym 0x21334) 1028}.
  Collection ImgHyps := IMG CODE_memcpy RB_memcpy.


Local Ltac step ::= astep2_fast. Local Ltac stepz ::= astep2_fast.
Open Scope bv_scope.

Definition memcpy_entry := (sym 0x21334)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ rw_cells img_segs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at img_segs m' (bv_unsigned a1) src.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis LEN : length src = Z.to_nat n.
  Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
  Hypothesis SEP : (S + n <= D \/ D + n <= S)%Z.

  Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom img_segs)).

  (* [comment removed for export] *)
  Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
    bytes_at img_segs m1 S src /\ u8arr img_segs m1 D bs /\ copied src bs (Z.to_nat P) /\
    mem_inv img_segs m1 /\ munch W m m1 /\ wmono img_segs m m1.

  Ltac open_inv H := (nelim H 6%nat; intros SRC DST CP MI MU WM).
  Ltac inv_tac :=
    lazymatch goal with
    | |- INV _ _ _ => split; [eassumption | split; [eassumption | split; [ | split; [eassumption | split; eassumption] ]]];   (* [comment removed for export] *)
        lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
          first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
    end.

  (* [comment removed for export] *)
  Ltac fin :=
    lazymatch goal with
    | DST : u8arr _ ?m1 _ ?bs, CP : copied _ ?bs (Z.to_nat ?P) |- _ =>
        let E := fresh "E" in
        pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
        apply rw_cells_of_u8arr in DST; rewrite LEN in DST
    end;
    finish2.

  (* [comment removed for export] *)
  Tactic Notation "use" uconstr(L) :=
    eapply L; first [ inv_tac | idtac ]; try (f_equal; lia); try lia;
    try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
    try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).

  (* [comment removed for export] *)
  Lemma mc_a8c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 4 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 960) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_2 by lia.
    zstep. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [exfalso; cbn in K2; lia|]; apply (proj1 (Z.nlt_ge _ _)) in Hl4.
      window P 2%nat HW.
      ld1 HW 0%nat. ld1 HW 1%nat. zstep. zstep.
      st1 HW 0%nat. st1 HW 1%nat.
      zstep. zstep. rewrite land_1.
      zstep. if_cases K1; zify_cond K1.
      + zstep. fin.
      + window (P + 2)%Z 1%nat HW1.
        ld1 HW1 0%nat. st1 HW1 0%nat. zstep. fin.
    - destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [|exfalso; cbn in K2; lia].
      zstep. rewrite land_1.
      zstep. if_cases K1; zify_cond K1.
      + window P 1%nat HW. ld1 HW 0%nat. st1 HW 0%nat. zstep. fin.
      + zstep. fin.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_a60 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + 4 + bv_unsigned r mod 4 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 916) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    window P 4%nat HW.
    ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. zstep. zstep.
    st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
    use (mc_a8c _ _ (P + 4)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_a58 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 908) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_4 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a8c m1 bs P).
    - use (mc_a60 m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_a0c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + 8 + bv_unsigned r mod 8 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 832) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    window P 8%nat HW.
    ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
    zstep.
    st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat. zstep.
    st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat. zstep.
    use (mc_a58 _ _ (P + 8)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_734 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 104) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_4 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a60 m1 bs P).
    - zstep. use (mc_a8c m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_a04 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 824) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_8 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_734 m1 bs P).
    - use (mc_a0c m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_72c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 96) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_8 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a0c m1 bs P).
    - use (mc_734 m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_978 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + 16 + bv_unsigned r mod 16 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 684) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    window P 16%nat HW.
    ld1 HW 0%nat. ld1 HW 1%nat. ld1 HW 2%nat. ld1 HW 3%nat. ld1 HW 4%nat. ld1 HW 5%nat. ld1 HW 6%nat. ld1 HW 7%nat.
    st1 HW 0%nat. st1 HW 1%nat. st1 HW 2%nat. st1 HW 3%nat.
    ld1 HW 8%nat. ld1 HW 9%nat. ld1 HW 10%nat. ld1 HW 11%nat.
    st1 HW 4%nat. st1 HW 5%nat. st1 HW 6%nat. st1 HW 7%nat.
    ld1 HW 12%nat. ld1 HW 13%nat. ld1 HW 14%nat. ld1 HW 15%nat.
    zstep.
    st1 HW 8%nat. st1 HW 9%nat. st1 HW 10%nat. st1 HW 11%nat.
    zstep.
    st1 HW 12%nat. st1 HW 13%nat. st1 HW 14%nat. st1 HW 15%nat.
    zstep.
    use (mc_a04 _ _ (P + 16)%Z).
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma mc_848 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 380) m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_4 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (mc_a8c m1 bs P).
    - window P 4%nat HW. ld4 HW 0%nat q0. zstep. st4 HW 0%nat. zstep. zstep.
      use (mc_a8c _ _ (P + 4)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_828 : forall m1 bs (P r : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + r = n)%Z -> (0 <= r < 16)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 r -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 348) m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P r xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr Rr -> -> ->; open_inv I.
    zstep. zstep. if_cases K8; zify_cond K8.
    - use (mc_848 m1 bs P (Z_to_bv 64 r)).
    - window P 8%nat HW. ld4 HW 0%nat q0. ld4 HW 4%nat q1. st4 HW 0%nat. st4 HW 4%nat. zstep. zstep.
      use (mc_848 _ _ (P + 8)%Z (Z_to_bv 64 r)).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_7f8 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P)%Z -> (16 <= n - P)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 300) m1 x5 x6 x7 xa1 xa2 xa3 (Z_to_bv 64 15) x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 HK I HP Hr -> -> ->; open_inv I.
    window P 16%nat HW.
    ld4 HW 0%nat q0. ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3.
    zstep. zstep.
    st4 HW 0%nat. st4 HW 4%nat. st4 HW 8%nat. st4 HW 12%nat.
    zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z).
    - use (mc_828 _ _ (P + 16)%Z (n - (P + 16))%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_7ec : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P <= n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 288) m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
    zstep. zstep. if_cases K16; zify_cond K16.
    - use (mc_828 m1 bs P (n - P)%Z).
    - zstep. use (mc_7f8 (Z.to_nat (n - P)) m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Notation LW w := (sext 64 (bv_extract 0 32 (le_bytes_to_word w))).

  (* [comment removed for export] *)
  Lemma mc_770 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (2 <= P)%Z -> (18 <= n - P)%Z ->
    w = firstn 4 (skipn (Z.to_nat (P - 2)) src) ->
    xa1 = Z_to_bv 64 (S + P + 14) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 164) m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 17) x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
    window (P - 2)%Z 20%nat HW.
    pose proof (window_sub src _ (P - 2)%Z 20 0 4 (P - 2)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep.
    ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
    do 11 zstep. zstep.
    st HW 2%nat 4%nat ltac:(by_le 16%Z). st HW 6%nat 4%nat ltac:(by_le 16%Z).
    st HW 10%nat 4%nat ltac:(by_le 16%Z). st HW 14%nat 4%nat ltac:(by_le 16%Z).
    zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
    - zstep. zstep. zstep. if_cases K16; zify_cond K16.
      + use (mc_72c _ _ (P + 16)%Z).
      + zstep. use (mc_978 _ _ (P + 16)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_754 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
    w = firstn 4 (skipn (Z.to_nat P) src) ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 136) m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
    window P 4%nat HW.
    pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep. zstep.
    st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z).
    zstep. zstep. zstep.
    use (mc_770 (Z.to_nat (n - (P + 2))) _ _ (P + 2)%Z w). by_win HW 0%nat.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_878 : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (1 <= P)%Z -> (19 <= n - P)%Z ->
    w = firstn 4 (skipn (Z.to_nat (P - 1)) src) ->
    xa1 = Z_to_bv 64 (S + P + 15) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 428) m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 18) x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
    window (P - 1)%Z 20%nat HW.
    pose proof (window_sub src _ (P - 1)%Z 20 0 4 (P - 1)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep.
    ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
    do 11 zstep. zstep.
    st HW 1%nat 4%nat ltac:(by_le 24%Z). st HW 5%nat 4%nat ltac:(by_le 24%Z).
    st HW 9%nat 4%nat ltac:(by_le 24%Z). st HW 13%nat 4%nat ltac:(by_le 24%Z).
    zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
    - zstep. zstep. zstep. if_cases K16; zify_cond K16.
      + use (mc_72c _ _ (P + 16)%Z).
      + zstep. use (mc_978 _ _ (P + 16)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_864 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
    w = firstn 4 (skipn (Z.to_nat P) src) ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 408) m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
    window P 4%nat HW.
    pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    st HW 0%nat 1%nat ltac:(by_le 0%Z).
    zstep. zstep. zstep. zstep.
    use (mc_878 (Z.to_nat (n - (P + 1))) _ _ (P + 1)%Z w). by_win HW 0%nat.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_90c : forall (K : nat) m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x16 x17 x28,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (3 <= P)%Z -> (17 <= n - P)%Z ->
    w = firstn 4 (skipn (Z.to_nat (P - 3)) src) ->
    xa1 = Z_to_bv 64 (S + P + 13) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 576) m1 x5 x6 x7 xa1 xa2 xa3 (LW w) (Z_to_bv 64 16) x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x16 x17 x28 HK I HP Hr Hw -> -> ->; open_inv I.
    window (P - 3)%Z 20%nat HW.
    pose proof (window_sub src _ (P - 3)%Z 20 0 4 (P - 3)%Z HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep.
    ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3. ld4 HW 16%nat q4.
    do 11 zstep. zstep.
    st HW 3%nat 4%nat ltac:(by_le 8%Z). st HW 7%nat 4%nat ltac:(by_le 8%Z).
    st HW 11%nat 4%nat ltac:(by_le 8%Z). st HW 15%nat 4%nat ltac:(by_le 8%Z).
    zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z q4). by_win HW 16%nat.
    - zstep. zstep. zstep. if_cases K16; zify_cond K16.
      + use (mc_72c _ _ (P + 16)%Z).
      + use (mc_978 _ _ (P + 16)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_8e8 : forall m1 bs (P : Z) (w : list byte) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
    w = firstn 4 (skipn (Z.to_nat P) src) ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 540) m1 x5 x6 x7 xa1 xa2 xa3 (LW w) x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P w xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 I HP Hr Hw -> -> ->; open_inv I.
    window P 4%nat HW.
    pose proof (window_sub src _ P 4 0 4 P HW ltac:(lia) ltac:(lia) ltac:(lia)) as Ew.
    cbn [firstn skipn] in Ew. rewrite <- Hw in Ew. clear Hw.
    assert (Lw : length w = 4%nat) by (rewrite Ew; reflexivity).
    zstep. zstep. zstep.
    st HW 0%nat 1%nat ltac:(by_le 0%Z). st HW 1%nat 1%nat ltac:(by_le 0%Z). st HW 2%nat 1%nat ltac:(by_le 0%Z).
    zstep. zstep. zstep.
    use (mc_90c (Z.to_nat (n - (P + 3))) _ _ (P + 3)%Z w). by_win HW 0%nat.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_740 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (32 <= n - P)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 116) m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> -> ->; open_inv I.
    window P 4%nat HW. ld4 HW 0%nat q0.
    zstep. zstep. if_cases K3; zify_cond K3.
    - use (mc_864 m1 bs P q0). by_win HW 0%nat.
    - zstep. zstep. if_cases K2; zify_cond K2.
      + use (mc_8e8 m1 bs P q0). by_win HW 0%nat.
      + use (mc_754 m1 bs P q0). by_win HW 0%nat.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_71c : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P <= n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 80) m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
    zstep. zstep. if_cases K32; zify_cond K32.
    - use (mc_740 m1 bs P).
    - zstep. zstep. if_cases K16; zify_cond K16.
      + use (mc_978 m1 bs P).
      + use (mc_72c m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_714 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P <= n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt img_segs POST (ST (sym 0x21334 + 72) m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
    zstep. zstep. if_cases Kal; zify_cond Kal.
    - use (mc_7ec m1 bs P).
    - use (mc_71c m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma mc_6e4 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P < n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    xa4 = Z_to_bv 64 (S + P + 1) ->
    evt img_segs POST (ST (sym 0x21334 + 24) m1 x5 x6 x7 xa1 xa2 xa3 xa4 (Z_to_bv 64 1) x16 x17 x28).
  Proof using AB LEN SEP ImgHyps.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28 HK I HP -> -> -> ->; open_inv I.
    window P 1%nat HW.
    ld1 HW 0%nat. zstep. zstep. zstep. rewrite land_3.
    st1 HW 0%nat. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
    - use (mc_714 _ _ (P + 1)%Z).
    - zstep. zstep. if_cases K1; zify_cond K1.
      + use (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ _ (P + 1)%Z).
      + zstep. use (mc_714 _ _ (P + 1)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma memcpy_body : forall junk,
    rw_cells img_segs m D [CB (Z.to_nat n) junk] -> bytes_at img_segs m S src -> mem_inv img_segs m ->
    evt img_segs POST (ST (sym 0x21334) m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3).
  Proof using AB LEN SEP ImgHyps.
    intros junk DST0 SRC MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl img_segs m) as WM.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST.
    pose proof (copied_0 src junk ltac:(rewrite (rw_cells_CB_length _ _ _ _ _ DST0); lia)) as CP.
    change 0%nat with (Z.to_nat 0) in CP. clear DST0.
    zstep. rewrite land_3. zstep. if_cases Ksal; zify_cond Ksal.
    - (* [comment removed for export] *)
      zstep. zstep. rewrite land_3. zstep. if_cases Kdal; zify_cond Kdal.
      + use (mc_71c m junk 0%Z).
      + use (mc_7ec m junk 0%Z).
    - zstep. if_cases K0; zify_cond K0.
      + zstep. use (mc_714 m junk 0%Z).
      + zstep. zstep. zstep. use (mc_6e4 (Z.to_nat n) m junk 0%Z).
  Qed.
End Proofs.

Lemma memcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at img_segs m (bv_unsigned a1) src ->
  length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells img_segs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  mem_inv img_segs m ->
  evt img_segs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21334)) fc None m (seg_rom img_segs)).
Proof.
  intros until junk. intros SRC LEN DST SEP MI.
  eapply memcpy_body; try eassumption.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bytes_at_bound _ _ _ _ SRC) as B2.
  pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition memcpy_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at img_segs m (bv_unsigned a1) src ->
  length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells img_segs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  mem_inv img_segs m ->
  evt img_segs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21334)) fc None m (seg_rom img_segs)).
Lemma memcpy_contract_ok : memcpy_contract.
Proof. exact memcpy_spec. Qed.


End Img.

(* [comment removed for export] *)
Existing Class memcpy_contract.
