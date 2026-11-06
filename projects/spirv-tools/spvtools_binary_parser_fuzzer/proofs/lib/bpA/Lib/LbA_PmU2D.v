(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmCall LbA_PmHdr LbA_PmLeaf LbA_PmLH LbA_PmVops LbA_PmU2K LbA_PmVC1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac u2_sc A w E33 EA RD0 F H E HE :=
  lazymatch goal with
  | |- sc_denot _ _ _ (SCReadBase (SA (EVar 32) _) 4 true _) => sc_fld4 H w E HE F
  | |- sc_denot _ _ _ (SCReadBase (SA (EAlu ALU_ADD (EMd M_MUL _ _) _) 0) 4 true _) =>
      eapply sc_rd_w4s; [rewrite (adenot_of_estart _ _ A); [reflexivity | unfold estart; cbn [a_base a_off]; rewrite EA, u64_of_Z by lia; lia | lia] | exact RD0 | reflexivity]
  | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_ADD (EMd M_MUL _ _) _) 0) (ELit ?l)) =>
      eapply (sc_flat_lit asegs _ _ _ _ A l); [unfold estart; cbn [a_base a_off]; rewrite EA, u64_of_Z by lia; lia | apply elit_u; lia | lia | lia | lia]
  | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL _ _) _) (ELit 3)) _) (ELit ?l)) =>
      eapply (sc_flat_lit asegs _ _ _ _ (A / 8 + SHBASE) l); [apply (estart_sh _ _ A EA); lia | apply elit_u; lia | lia | lia | lia]
  | |- sc_denot _ _ _ (SCDisj (SA (EAlu ALU_ADD (EMd M_MUL _ _) _) 0) (ELit ?l1) (SA (EAlu ALU_SRL (EVar 33) (ELit 3)) ?o2) (ELit ?l2)) =>
      eapply (sc_disj_lit asegs _ _ _ _ _ _ A l1 (wa_ff w / 8 + o2) l2);
      [unfold estart; cbn [a_base a_off]; rewrite EA, u64_of_Z by lia; lia | apply elit_u; lia
      | unfold estart; cbn [a_base a_off]; rewrite (srl3_val _ (EVar 33) (wa_ff w) E33) by lia; lia | apply elit_u; lia
      | lia | lia | lia | lia | lia | lia | lia]
  | |- _ => idtac
  end.

Definition TBL_EE770 : list (Z * expr) := TBL_EE648 ++ [(840, EAlu ALU_ADD (EAlu ALU_SRL (WADD WV_P 80) (ELit 3)) (ELit SHBASE)); (880, EAlu ALU_ADD (EAlu ALU_SRL (WADD WV_P 240) (ELit 3)) (ELit SHBASE)); (1032, EAlu ALU_ADD (EAlu ALU_SRL (WADD WV_P 248) (ELit 3)) (ELit SHBASE))].
Definition FTBL_EE770 : list (Z * expr) := zwords 10416 5.
Definition RT_EE770 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, ELit 2147450880); (20%bv, SH_FF); (21%bv, ELit 2147450880); (22%bv, ELit 18446744073709551608); (24%bv, WADD WV_P 240); (25%bv, WADD WV_P 248); (26%bv, WADD WV_FF 11488); (27%bv, WADD WV_FF 10496)].

Definition RT_EE7A0 : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, ELit 2147450880); (19%bv, EAlu ALU_SRL (WADD WV_P 256) (ELit 3)); (20%bv, SH_FF);
   (21%bv, ELit 2147450880); (22%bv, ELit 18446744073709551608); (24%bv, WADD WV_P 240); (25%bv, WADD WV_P 248); (26%bv, WADD WV_FF 11488); (27%bv, WADD WV_FF 10496)].

Definition TBL_EE84C : list (Z * expr) := TBL_EE770 ++ [(904, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 256)) (ELit 3)) (ELit 2147450880))].
Definition RT_EE84C : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, ELit 2147450880); (19%bv, EVar 32); (20%bv, SH_FF);
   (21%bv, WADD WV_FF 10512); (22%bv, ELit 18446744073709551608); (25%bv, WADD WV_P 248); (26%bv, WADD WV_FF 11488); (27%bv, WADD WV_FF 10496)].

Definition TBL_EE8CC : list (Z * expr) := vc1_tbl TBL_EE84C.
Definition RT_EE8CC : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, ELit 2147450880); (19%bv, EVar 32); (20%bv, SH_FF);
   (21%bv, WADD WV_FF 10512); (22%bv, ELit 18446744073709551608); (24%bv, ELit 2147450880); (25%bv, WADD WV_FF 10426);
   (26%bv, WADD WV_FF 11488); (27%bv, WADD WV_FF 10496)].

Definition FTBL_EE8E8 : list (Z * expr) := [(10416, ELit 0); (10432, ELit 0); (10440, ELit 0); (10448, ELit 0)].

Definition RT_EE904 : list (reg * expr) := RT_EE8CC ++ [(10%bv, ELit 0)].

Definition TBL_EEE9C : list (Z * expr) := TBL_EE8CC ++ [(816, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 40)) (ELit 3)); (824, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (1096, EAlu ALU_ADD (EVar 33) (ELit 10416)); (1088, EAlu ALU_ADD (EVar 33) (ELit 10496)); (1080, EVar 32); (1072, EAlu ALU_ADD (EVar 33) (ELit 10512)); (1064, EAlu ALU_ADD (EVar 33) (ELit 11488))].
Definition RT_EEE9C : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (11%bv, ELit 0); (12%bv, WADD WV_P 72);
   (13%bv, EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 40)) (ELit 3)); (18%bv, EVar 33); (19%bv, EVar 32); (20%bv, SH_FF);
   (21%bv, WADD WV_FF 10512); (22%bv, ELit 18446744073709551608); (24%bv, ELit 2147450880); (25%bv, WADD WV_FF 10426);
   (26%bv, WADD WV_FF 11488); (27%bv, WADD WV_FF 10496)].

Definition RT_EEED4 : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EVar 33); (19%bv, EVar 32); (20%bv, SH_FF);
   (21%bv, WADD WV_FF 10512); (22%bv, ELit 18446744073709551608); (24%bv, ELit 2147450880); (25%bv, WADD WV_FF 10426);
   (26%bv, WADD WV_FF 11488); (27%bv, WADD WV_FF 10496)].

Definition RT_EEF98 : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (13%bv, WADD WV_P 264); (18%bv, EVar 33); (19%bv, EVar 32); (20%bv, SH_FF);
   (21%bv, WADD WV_FF 10512); (22%bv, ELit 18446744073709551608); (26%bv, WADD WV_FF 11488); (27%bv, WADD WV_FF 10496)].

Definition RT_EEFB0 : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EVar 33); (19%bv, EVar 32); (20%bv, SH_FF);
   (21%bv, WADD WV_FF 10512); (22%bv, ELit 18446744073709551608); (26%bv, WADD WV_FF 11488); (27%bv, WADD WV_FF 10496)].

Definition RT_EF07C : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EVar 33); (19%bv, EVar 32); (20%bv, SH_FF);
   (21%bv, WADD WV_FF 10512); (22%bv, ELit 18446744073709551608); (25%bv, WADD WV_FF 944); (27%bv, WADD WV_FF 10496)].

Definition RT_EF07Cc : list (reg * expr) := (1%bv, ELit 0xef210) :: RT_EF07C.
