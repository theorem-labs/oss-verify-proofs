(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HArr HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsStack0 RtA_Iface RtA_IMemset.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FakeStackRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_Own.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_MILB LbA_DiagStmt LbA_DStat LbA_DRep LbA_DKit LbA_DKitN.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_PrsStmt LbA_TablStmt LbA_SnStmt.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_DCtorK LbA_DPdK LbA_SnK LbA_SnFind.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_SnTB.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbA_SnAb () := "C46Stdlib5Lists4List2InC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib3bpA3Lib8LbA_DKit4fentC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C69OSSVerify5KrLib3bpA3Lib:LbA_Bridge5rfullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK2WpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit4rtblC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib3bpA3Lib8LbA_DKit4ftblC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list01C69OSSVerify5KrLib3bpA3Lib7LbA_SnK2PwC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib4HMem7mem_invC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib3bpA2Rt7AsIface6as_RFSC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib3bpA3Lib7LbA_SnK2W3C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame5munchC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C79OSSVerify5KrLib3bpA2HF3Lib:HLPropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK9sn_rangesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C69OSSVerify5KrLib3bpA2Rt8AsShadow5aceilC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib3bpA2Rt7AsIface6as_FSBC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2or00C69OSSVerify5KrLib3bpA3Lib<LbA_DiagStmt7app_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK2tSC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib3bpA3Lib7LbA_SnK2tFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK2tHC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib3bpA3Lib7LbA_SnK8tabs_wf3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK8Pw_step3C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK59OSSVerify5KrLib8SymExec33SX27scripts01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec33SX24expr03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX29sym_state01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit6wboundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit8rtbl_okbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit3finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK8tabs_ok3C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib7LibHash4HLib5EseedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK9kst_pd_okC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib=SymExec3Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib3srsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN4fknTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX28sym_execC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib=SymExec3Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN6swinsTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_FKit:sym_insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25s_logC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC59OSSVerify5KrLib8SymExec33SX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit8rtbl_chkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN4tupdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN5ftblsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN5winsTC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffC59OSSVerify5KrLib8SymExec33SX24s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK9RFS_step3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK9winsT3_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK2kTC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX28sidecond02C1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib3bpA3Lib7LbA_SnK5kT_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK8scT_flatC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib3bpA2HF3Lib7HMState<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib8SymExec33SX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S5elenZC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib=SymExec3Sound4SX2S9scs_denotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame;munch_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN:rtbl_keptkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN5keptkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK8sn_keepUC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep6nval32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_Kit2gzC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib8SymExec33SX28expr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib3bpA3Lib:LbA_DCtorK7inb_In'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit7rtbl_InC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit4wenvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK2rgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib<LbA_TablStmt5sx32AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib3sxwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs:PrsGrammar4sx32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib:LbA_SnFind8sxw_sx32C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib8PropExec7FPState01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib3bpA3Lib:LbA_SnFind;snfind_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_Kit6aonlyTC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib3bpA3Lib8LbA_DKit4rsubC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit9rtbl_keepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HMState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib:LbA_Bridge7mkst_MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_Call8blk_thenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN7dk_runNC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib3bpA2HF3Lib5HExec3evtC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26sentry01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05I59OSSVerify5KrLib7LibHash4HRep5umapx00C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib6CatSim6msteps00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02I47Corelib7Numbers7BinNums1Z00K47Corelib4Init5Logic4True01C69OSSVerify5KrLib3bpA2Rt5ASegs5asegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN3tabC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26sentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26kentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C69OSSVerify5KrLib3bpA3Lib8LbA_MILB4AC_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_MILB4LY_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_MILB4MI_AC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib3bpA2Rt7AsIface3memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Lib8LbA_SnAb3RT2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Lib8LbA_SnAb3SF2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Lib8LbA_SnAb3FT2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_SnTB4RTK4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_SnTB3SF4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_SnTB3FT4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_SnTB3HT4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib:LbA_SnFind9SNF_FOUNDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib:LbA_SnFind<SNF_NOTFOUNDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib<LbA_DiagStmt9ADS_STACKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AsShadow7AAPP_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7AsIface7AFS_HDRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7AsIface8AFS_SIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7AsIface9AFS_FLAGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt5ASegs8AIMG_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AsShadow9ALOWSH_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AsShadow6AHI_LOC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib3bpA3Lib7LbA_SnK6kst_snC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I59OSSVerify5KrLib8SymExec33SX28sidecond00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_Kit6SHBASEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25sr_idC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K47Corelib4Init9Datatypes4bool02I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic4True00C69OSSVerify5KrLib3bpA3Lib:LbA_SnFind9SNF_ENTRYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit4KEPTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_Kit8non_argTC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 33) (ELit k).

Definition RT2 : list (reg * expr) :=
  [(1%bv, ELit 0xf8d90); (2%bv, spx (-144)); (3%bv, EVar 50); (4%bv, EVar 51); (8%bv, EVar 33); (9%bv, spx (-144));
   (10%bv, EVar 52); (18%bv, EVar 40); (19%bv, EVar 41); (20%bv, EVar 36); (21%bv, EVar 32); (22%bv, EVar 35);
   (23%bv, ELit 2147450880); (24%bv, EVar 46); (25%bv, EVar 47); (26%bv, EVar 48); (27%bv, EVar 49)].
Definition SF2 : list fent :=
  [(-128, 8%nat, ELit 0); (-8, 8%nat, EVar 34); (-16, 8%nat, EVar 38); (-24, 8%nat, EVar 39); (-32, 8%nat, EVar 40);
   (-40, 8%nat, EVar 41); (-48, 8%nat, EVar 42); (-56, 8%nat, EVar 43); (-64, 8%nat, EVar 44); (-72, 8%nat, EVar 45);
   (-80, 8%nat, EVar 46); (-88, 8%nat, EVar 47); (-96, 8%nat, EVar 48); (-104, 8%nat, EVar 49)].
Definition FT2 : list fent := [(2040, 8%nat, EVar 53)].

Section SnAb.
  Local Notation PD_SHB := LbA_DPdK.PD_SHB (only parsing).

  Local Notation PO_SIZE := LbA_SnK.PO_SIZE (only parsing).
  Local Notation kst_sn := LbA_SnK.kst_sn (only parsing).
  Local Notation dj2 := LbA_SnK.dj2 (only parsing).
  Local Notation rg := LbA_SnK.rg (only parsing).
  Local Notation shT := LbA_SnK.shT (only parsing).
  Local Notation kT := LbA_SnK.kT (only parsing).
  Local Notation kwin := LbA_SnK.kwin (only parsing).
  Local Notation shN := LbA_SnK.shN (only parsing).
  Local Notation shP := LbA_SnK.shP (only parsing).
  Local Notation POA := LbA_SnK.POA (only parsing).
  Local Notation kP := LbA_SnK.kP (only parsing).
  Local Notation kN := LbA_SnK.kN (only parsing).
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m1 : mem) (this po tid pcons icount lo ff fp : Z) (LF : list fframe).

  Variables (bl bc nd nk bw enc : Z).
  Variables (LBl : list (Z * Z)) (ents : list (Z * (Z * (Z * Z * Z)))).

  Hypothesis DSA : addressable m1 po PO_SIZE.
  Hypothesis DSW : wr_at asegs m1 po PO_SIZE.
  Hypothesis DSO : app_obj po PO_SIZE.
  Hypothesis DS8 : po mod 8 = 0.
  Hypothesis DSV : shvis m1 po (po + PO_SIZE).
  Hypothesis DSH : po + PO_SIZE + 64 <= AAPP_HI.
  Hypothesis DSM : po + PO_SIZE <= aceil.
  Hypothesis DSin : obj_inframe LF po PO_SIZE.

  Hypothesis PCA : addressable m1 pcons 48.
  Hypothesis PCO : app_obj pcons 48.
  Hypothesis PC8 : pcons mod 8 = 0.
  Hypothesis PCC : rw_cells asegs m1 (pcons + 32) [C8 (Z_to_bv 64 0)].
  Hypothesis DISJ : forall a, po <= a < po + PO_SIZE -> ~ (pcons <= a < pcons + 48).
  Hypothesis ICN : 0 <= icount < 2 ^ 63.

  Hypothesis STK : stk asegs m1 lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - ADS_STACK.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPHI : bv_unsigned sp <= AAPP_HI.
  Hypothesis SPOBJ : forall O n, O = po /\ n = PO_SIZE \/ O = pcons /\ n = 48 ->
                     O + n <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= O.

  Hypothesis FFR : aframe_range H 5 ff fp.
  Hypothesis FSB_OK : afsb_ok H.
  Hypothesis FFDS : ff + 2048 <= po \/ po + PO_SIZE <= ff.
  Hypothesis FFPC : ff + 2048 <= pcons \/ pcons + 48 <= ff.
  Hypothesis FPPC : fp + 1 <= pcons \/ pcons + 48 <= fp.
  Hypothesis FPDS : fp + 1 <= po \/ po + PO_SIZE <= fp.
  Hypothesis HULL : hull_hi (po + PO_SIZE) <= ff \/ ff + 2048 <= hull_lo po.
  Hypothesis FRW : wr_at asegs m1 ff 2048.
  Hypothesis FSV : shvis m1 ff (ff + 2048).
  Hypothesis FSW : wr_at asegs m1 (sh ff) 256.
  Hypothesis FLW : wr_at asegs m1 fp 1.

  Hypothesis MI1 : mem_inv asegs m1.
  Hypothesis AC1 : ACONST m1.
  Hypothesis LV1 : LINV_P5 m1.

  Hypothesis THA : addressable m1 this 288.
  Hypothesis THO : app_obj this 288.
  Hypothesis TH8 : this mod 8 = 0.
  Hypothesis THS : dj2 (this + 288) (bv_unsigned sp - ADS_STACK) (bv_unsigned sp) this.
  Hypothesis THF : dj2 (ff + 2048) this (this + 288) ff.
  Hypothesis THP : dj2 (fp + 1) this (this + 288) fp.

  Hypothesis THD : dj2 (this + 272) po (po + PO_SIZE) this.
  Hypothesis THC1 : rw_cells asegs m1 (this + 8) [C8 (Z_to_bv 64 pcons)].
  Hypothesis THC2 : rw_cells asegs m1 (this + 80) [C8 (Z_to_bv 64 icount)].
  Hypothesis TIDR : rg 0 tid (2 ^ 32).
  Hypothesis BLR : rg 0 bl (2 ^ 64).
  Hypothesis BCR : rg 0 bc (2 ^ 64).
  Hypothesis NDR : rg 0 nd (2 ^ 64) /\ rg 0 nk (2 ^ 32) /\ rg 0 bw (2 ^ 32) /\ rg 0 enc (2 ^ 32).

  Hypothesis UM1 : umapx MI_A 32 (nval32 ASEGS) LBl m1 (this + 136) bl bc ents.
  Hypothesis UG1 : gz m1 (this + 136) 40.
  Hypothesis UG2 : bc <> 0 -> gz m1 bl (8 * bc).
  Hypothesis UG3 : forall p k v, In (p, (k, v)) ents -> gz m1 p 32.
  Hypothesis UFO : forall a, umap_foot 32 (this + 136) bl bc ents a ->
    outside [(bv_unsigned sp - 16384, bv_unsigned sp); (po, po + PO_SIZE); (ff, ff + 2048); (sh ff, sh ff + 256); (fp, fp + 1)] a
    /\ outside [(bv_unsigned sp - 16384, bv_unsigned sp); (po, po + PO_SIZE); (ff, ff + 2048); (sh ff, sh ff + 256); (fp, fp + 1)] (a / 8 + SHBASE)
    /\ 0 <= a < 2 ^ 47.

  Local Notation Wp := (@LbA_SnK.Wp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc) (only parsing).
  Local Notation PW := (@LbA_SnK.PW sp po ff fp) (only parsing).
  Local Notation PWF := (@LbA_SnK.PWF sp po ff fp) (only parsing).
  Local Notation Pw := (@LbA_SnK.Pw sp m1 po ff fp) (only parsing).
  Local Notation Pw_cz := (@LbA_SnK.Pw_cz sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation Pw_m1 := (@LbA_SnK.Pw_m1 sp m1 po ff fp) (only parsing).
  Local Notation sn_ranges := (@LbA_SnK.sn_ranges HCEIL H sp m1 this po pcons icount lo ff fp ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation sh_mono8 := (@LbA_SnK.sh_mono8 sp this po pcons icount ICN) (only parsing).
  Local Notation pw_aconst := (@LbA_SnK.pw_aconst HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pw_out_img := (@LbA_SnK.pw_out_img HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pw_sh_apart := (@LbA_SnK.pw_sh_apart HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation pw_hull_apart := (@LbA_SnK.pw_hull_apart HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation sn_keep := (@LbA_SnK.sn_keep HCEIL H sp m1 this po pcons icount lo ff fp DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation sn_keepT := (@LbA_SnK.sn_keepT HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK THA THO TH8 THS THF THP THD THC1 THC2) (only parsing).
  Local Notation evWp := (@LbA_SnK.evWp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc ICN) (only parsing).
  Local Notation sn_vals := (@LbA_SnK.sn_vals HCEIL H sp m1 this po pcons icount lo ff fp DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation kst_pd_ok := (@LbA_SnK.kst_pd_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation sn_keepU := (@LbA_SnK.sn_keepU sp m1 this po pcons icount ff fp bl bc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation evT := (@LbA_SnK.evT ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc THO) (only parsing).
  Local Notation shT_start := (@LbA_SnK.shT_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc THO) (only parsing).
  Local Notation shT_apart := (@LbA_SnK.shT_apart HCEIL H sp m1 this po pcons icount lo ff fp ICN STK CEIL LO SPHI FFR FSB_OK TH8 THF) (only parsing).
  Local Notation kT_ok := (@LbA_SnK.kT_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK THA THO TH8 THS THF THP THD THC1 THC2) (only parsing).
  Local Notation scT_flat := (@LbA_SnK.scT_flat ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc THO) (only parsing).
  Local Notation tS := (@LbA_SnK.tS sp) (only parsing).
  Local Notation tF := (@LbA_SnK.tF ff) (only parsing).
  Local Notation tH := (@LbA_SnK.tH ff) (only parsing).
  Local Notation tL := (@LbA_SnK.tL fp) (only parsing).
  Local Notation sn_wins := (@LbA_SnK.sn_wins HCEIL H sp m1 this po pcons icount lo ff fp ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tab_vals := (@LbA_SnK.tab_vals HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tabs_wf3 := (@LbA_SnK.tabs_wf3 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tabs_wf4 := (@LbA_SnK.tabs_wf4 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation wk_stk := (@LbA_SnK.wk_stk sp this po pcons icount lo ICN LO) (only parsing).
  Local Notation wk_win := (@LbA_SnK.wk_win sp this po pcons icount ICN) (only parsing).
  Local Notation inPW := (@LbA_SnK.inPW sp po ff fp) (only parsing).
  Local Notation Pw_ext := (@LbA_SnK.Pw_ext sp m1 po ff fp) (only parsing).
  Local Notation in_stk := (@LbA_SnK.in_stk sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_p2 := (@LbA_SnK.in_p2 sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_p8 := (@LbA_SnK.in_p8 sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_fr := (@LbA_SnK.in_fr sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_sh := (@LbA_SnK.in_sh sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation in_fl := (@LbA_SnK.in_fl sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation shb_eq := (@LbA_SnK.shb_eq sp this po pcons icount ff ICN) (only parsing).
  Local Notation W3 := (@LbA_SnK.W3 sp ff) (only parsing).
  Local Notation winsT3_eq := (@LbA_SnK.winsT3_eq sp ff) (only parsing).
  Local Notation Pw_step3 := (@LbA_SnK.Pw_step3 sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation Pw_step4 := (@LbA_SnK.Pw_step4 sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation HHb := (@LbA_SnK.HHb HCEIL H HHbp) (only parsing).
  Local Notation afs_ok_frame := (@LbA_SnK.afs_ok_frame H sp this po pcons icount ff fp LF ICN) (only parsing).
  Local Notation afs_ok_stack := (@LbA_SnK.afs_ok_stack HCEIL H sp m1 this po pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation afs_ok_shadow := (@LbA_SnK.afs_ok_shadow HCEIL H sp m1 this po pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tabs_ok3 := (@LbA_SnK.tabs_ok3 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation tabs_ok4 := (@LbA_SnK.tabs_ok4 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation tP2 := (@LbA_SnK.tP2 po) (only parsing).
  Local Notation tP8 := (@LbA_SnK.tP8 po) (only parsing).
  Local Notation po_wins := (@LbA_SnK.po_wins sp po pcons SPOBJ) (only parsing).
  Local Notation po_sh_wins := (@LbA_SnK.po_sh_wins HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation tabs_wf5p := (@LbA_SnK.tabs_wf5p HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO DSH PCO ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS) (only parsing).
  Local Notation Pw_step5p := (@LbA_SnK.Pw_step5p sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation tabs_ok5p := (@LbA_SnK.tabs_ok5p HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation afs_ok_po := (@LbA_SnK.afs_ok_po H po ff fp LF DSin) (only parsing).
  Local Notation RFS_step5p := (@LbA_SnK.RFS_step5p HCEIL H HHbp sp m1 this po pcons icount lo ff fp LF DSin ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation RFS_step3 := (@LbA_SnK.RFS_step3 HCEIL H HHbp sp m1 this po pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation po_rng := (@LbA_SnK.po_rng po DSO) (only parsing).
  Local Notation evP := (@LbA_SnK.evP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation shP_start := (@LbA_SnK.shP_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation POA_start := (@LbA_SnK.POA_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation po_sh_self := (@LbA_SnK.po_sh_self po DSO DS8) (only parsing).
  Local Notation flatP := (@LbA_SnK.flatP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation flat_shP := (@LbA_SnK.flat_shP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw this po tid pcons icount ff fp bl bc nd nk bw enc DSO) (only parsing).
  Local Notation kP_ok := (@LbA_SnK.kP_ok HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation nd_facts := (@LbA_SnK.nd_facts sp m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation nd_out := (@LbA_SnK.nd_out sp this po tid ff fp bl bc nd nk bw enc ents UFO) (only parsing).
  Local Notation evN := (@LbA_SnK.evN ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation ndA_start := (@LbA_SnK.ndA_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation shN_start := (@LbA_SnK.shN_start ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation flatN := (@LbA_SnK.flatN ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation flat_shN := (@LbA_SnK.flat_shN ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation kN_ok := (@LbA_SnK.kN_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount ff fp bl bc nd nk bw enc LBl ents DSO ICN UM1 UG1 UG2 UG3 UFO) (only parsing).
  Local Notation SF5 := (@LbA_SnK.SF5 HCEIL H HHbp ra sp gp tp) (only parsing).
  Local Notation tabs_wf1 := (@LbA_SnK.tabs_wf1 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSO PCO ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation Pw_step1 := (@LbA_SnK.Pw_step1 sp m1 this po pcons icount ff fp ICN) (only parsing).
  Local Notation tabs_ok1 := (@LbA_SnK.tabs_ok1 HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc DSA DSW DSO DS8 DSV DSH DSM PCA PCO PC8 PCC DISJ ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FFPC FPPC FPDS HULL FRW FSV FSW FLW AC1 LV1) (only parsing).
  Local Notation RFS_L_step1 := (@LbA_SnK.RFS_L_step1 HCEIL H HHbp sp m1 this po pcons icount lo ff fp LF ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation nopo := (@LbA_SnK.nopo sp ff fp) (only parsing).
  Local Notation po_cells_keep := (@LbA_SnK.po_cells_keep HCEIL H sp m1 this po pcons icount lo ff fp DSO ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FPDS) (only parsing).
  Local Notation po4 := (@LbA_SnK.po4 po nk bw enc) (only parsing).
  Local Notation po4_keep := (@LbA_SnK.po4_keep HCEIL H sp m1 this po pcons icount lo ff fp nk bw enc DSO ICN STK CEIL LO SPHI SPOBJ FFR FSB_OK FFDS FPDS) (only parsing).
  Local Notation nopo_w3 := (@LbA_SnK.nopo_w3 sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation nopo_w1 := (@LbA_SnK.nopo_w1 sp ff fp) (only parsing).
  Local Notation nopo_sf := (@LbA_SnK.nopo_sf sp ff fp) (only parsing).
  Local Notation inPW_sf := (@LbA_SnK.inPW_sf sp this po pcons icount ff fp ICN) (only parsing).
  Local Notation sf_stack_keep := (@LbA_SnK.sf_stack_keep HCEIL H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aw m1 this po tid pcons icount lo ff fp bl bc nd nk bw enc ICN STK CEIL LO SPHI FFR FSB_OK) (only parsing).
  Local Notation sn_Pok := (@LbA_SnK.sn_Pok H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 po ff fp LF nk bw enc) (only parsing).
  Local Notation sn_fin_ok := (@LbA_SnK.sn_fin_ok H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 po ff fp LF nk bw enc) (only parsing).

  Notation spz := (bv_unsigned sp) (only parsing).

  Ltac evwp := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wp;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Ltac tnormp H :=
    lazymatch type of H with
    | ftbl ?W ?B ?m ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    | rtbl ?W ?R ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    end.

  Ltac dkrunP3 HRT HSF HFT HHT HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []]) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) (kst_sn ++ fknT L0)) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] ((kst_sn ++ kf) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3]
                    (tabs_wf3 SF FT HT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step3 SF FT HT ks1 ks2 ks3)
                    Q R F pc fc m ro RT [] (kst_sn ++ kf) fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok3; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end
    end.

  Ltac dkrunP4 HRT HSF HFT HHT HLT HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HLT with ftbl _ _ _ ?LT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []; tL LT []]) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) (kst_sn ++ fknT L0)) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] ((kst_sn ++ kf) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          let ks4 := eval vm_compute in (nkeys (EVar 53) (s_log SSr) LT) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3; tL LT ks4]
                    (tabs_wf4 SF FT HT LT ks1 ks2 ks3 ks4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step4 SF FT HT LT ks1 ks2 ks3 ks4)
                    Q R F pc fc m ro RT [] (kst_sn ++ kf) fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok4; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | exact HLT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end
    end.

  Ltac tcomp HTS :=
    lazymatch type of HTS with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS; clear E
    end.
  Ltac tsplit HTS H1 H2 H3 :=
    tcomp HTS;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; clear HTS; cbn [fst snd] in H1, H2, H3.
  Ltac tsplit4 HTS H1 H2 H3 H4 :=
    tcomp HTS;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; apply Forall_cons_iff in HTS as [H4 HTS]; clear HTS; cbn [fst snd] in H1, H2, H3, H4.

  Ltac rgetp HRT r H :=
    lazymatch type of HRT with
    | rtbl ?W ?R ?RT =>
        let e := eval vm_compute in (match List.find (fun re => bv_eqb (fst re) r) RT with Some re => snd re | None => ELit 0 end) in
        assert (H : PropExec.getr R r = edenot (wenv W) e)
          by (apply (rtbl_In W R RT r e HRT); apply LbA_DCtorK.inb_In'; vm_compute; reflexivity);
        unfold wenv in H; cbn [edenot] in H; unfold HLib.Eseed, reg_ev, Wp in H;
        lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
              Init.Nat.add Nat.sub nth app] in H;
        rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z in H by (pose proof sn_vals; lia)
    end.
  Ltac dkrunP1 HRT HSF HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] (kst_sn ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          eapply (dk_runN Wp [tS SF ks1] (tabs_wf1 SF ks1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step1 SF ks1) Q R F pc fc m ro RT [] kst_sn fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok1; [exact HP | exact HMI | exact HSF | vm_compute; reflexivity]
          | exact HP | exact HMI | apply kst_pd_ok; [exact HP | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end
    end.
  Ltac dkrunP5p HRT HSF HFT HHT HP2 HP8 HP HMI fuel stops kx scr0 :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HP2 with ftbl _ _ _ ?P2 =>
      lazymatch type of HP8 with ftbl _ _ _ ?P8 =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []; tP2 P2 []; tP8 P8 []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops scr0 (SS pc (HLib.srs sr_id RT) [] ((kst_sn ++ kx) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          let ks4 := eval vm_compute in (kwin 2 4 (nkeys (EVar 35) (s_log SSr) P2)) in
          let ks5 := eval vm_compute in (kwin 8 20 (nkeys (EVar 35) (s_log SSr) P8)) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3; tP2 P2 ks4; tP8 P8 ks5]
                    (tabs_wf5p SF FT HT P2 P8 ks1 ks2 ks3 ks4 ks5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step5p SF FT HT P2 P8 ks1 ks2 ks3 ks4 ks5)
                    Q R F pc fc m ro RT [] (kst_sn ++ kx) fuel stops scr0 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok5p; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | exact HP2 | exact HP8 | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end end
    end.
  Ltac tsplit5 HTS H1 H2 H3 H4 H5 :=
    tcomp HTS;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS];
    apply Forall_cons_iff in HTS as [H3 HTS]; apply Forall_cons_iff in HTS as [H4 HTS]; apply Forall_cons_iff in HTS as [H5 HTS];
    clear HTS; cbn [fst snd] in H1, H2, H3, H4, H5.

  Ltac dkrunP3k HRT HSF HFT HHT HP HMI fuel stops kx :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tF FT []; tH HT []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] ((kst_sn ++ kx) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wp) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          eapply (dk_runN Wp [tS SF ks1; tF FT ks2; tH HT ks3]
                    (tabs_wf3 SF FT HT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    Pw (Pw_step3 SF FT HT ks1 ks2 ks3)
                    Q R F pc fc m ro RT [] (kst_sn ++ kx) fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok3; [exact HP | exact HMI | exact HSF | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HP | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply kst_pd_ok; [exact HP | exact HMI] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end
    end.

  Ltac scT := unfold scs_denot; repeat (apply Forall_cons; [cbn [sc_denot]; unfold elenZ; cbn [edenot]; rewrite ?unsigned_lit by (clear; lia);
                                           first [apply scT_flat; clear; lia] |]); apply Forall_nil.

  Lemma sn_pre : forall Q R m, rfull R -> rtbl Wp R RT2 -> ftbl Wp spz m SF2 -> ftbl Wp ff m FT2 -> ftbl Wp (ff / 8) m [] ->
    Pw m -> mem_inv asegs m -> as_RFS H ((5, ff, fp) :: LF) m ->
    (forall R' m' p v, rfull R' -> In (p, (tid, v)) ents -> PropExec.getr R' 10 = Z_to_bv 64 p ->
       rtbl Wp R' RTK4 -> ftbl Wp spz m' SF4 -> ftbl Wp ff m' FT4 -> ftbl Wp (ff / 8) m' HT4 ->
       Pw m' -> mem_inv asegs m' -> as_RFS H ((5, ff, fp) :: LF) m' -> munch W3 m m' ->
       evt asegs Q (MS R' F (Z_to_bv 64 LbA_SnFind.SNF_FOUND) fc None m' (seg_rom asegs))) ->
    (forall R' m', rfull R' ->
       rtbl Wp R' RTK4 -> ftbl Wp spz m' SF4 -> ftbl Wp ff m' FT4 -> ftbl Wp (ff / 8) m' HT4 ->
       Pw m' -> mem_inv asegs m' -> as_RFS H ((5, ff, fp) :: LF) m' -> munch W3 m m' ->
       evt asegs Q (MS R' F (Z_to_bv 64 LbA_SnFind.SNF_NOTFOUND) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS R F (Z_to_bv 64 0xf8d90) fc None m (seg_rom asegs)).
Proof.
ltac2:(KReplay.run1 (kr_t_LbA_SnAb ()) ["SnAb"] "p'0h02H0h11ph21xi001xh32Hrh41vh51Hh64HTS3h74HTS4h81kh93Hmsh:1lh;1Ah<1Ph=2R'h>7__arithh?4__ffh@8__varmaphA5__withB1mhC1EhD1ahE1rhF1yhG4HRK4hH2HahI3MU3hJ3MU4hK3RF5hL6__sat1hM4__x1hN1bhO2l1hP2l2hQ2m'hR2AOhS2G1hT3G10hU2G2hV3G20hW4G20'hX3G21hY3G23hZ2G3h[2HFh\4HFT2h]4HFT3h^4HFT4h_4HHT2h`4HHT3ha4HHT4hb4HMI2hc4HMI3hd4HMI4he3HP2hf3HP3hg3HP4hh4HRF2hi4HRF3hj4HRF4hk4HRT2hl4HRT3hm4HRT4hn4HRT5ho4HSF2hp4HSF3hq4HSF4hr3Hinhs2KFht2KNhu2KPhv4MU24hw3PR1hx4PR10hy4PR11hz4PR12h{3PR2h|3PR3h}3PR4h~3PR5i013PR6i023PR7i033PR8i043PR9i051Qi062R2i072R3i082R4i092R5i0:3RF2i0;3RF3i0<3RF4i0=3TO1i0>3TO2i0?3TO3i0@2TRi0A2U4i0B3WM3i0C3WM4i0D6__sat0i0E1ei0F2m2i0G2m3i0H2m4i0I1zi0J4Ffixi0K8bv_is_wfi0L;bv_unsignedi0M1cp%0p%1p%2p%3p%4p%5p%6p%7p%8p&0p&1p&2p;1p;2p;Np;3p;4p;6p;Bp;gp;5p;?p;vp;7p;Op;8p;kp;Sp;Dp;Ip;>p;=p-1g0000R0p4p710p8g000GR1p4p7210g0013R2p4p710R3p8g001OR4p4p70R5P3p8P5g002Ip4p710R5p8g002fj17Tg003Kj18Tg0040k10HTg004NS00k10vTP1k221Tg0051k10KTg005nmN1aTg006ej3oTg007_k20_Tg008Ij4CTg009Cj1JTg009ak21BTg00:>j1UTg00:^k60ek51RTg00;Uk20bTg00<QS01j2]Tg00=1j4RTg00=Qj3ATg00>1k30YTg00>kj2PTg00?Qk21MTg00@Hj3gTg00AEk10wTg00Agk11GTg00BimB1ETg00Cgk20uTg00DDk201Tg00D`R1j2BTg00E;k11@Tg00F5j2sTg00FRj2QTg00Fnk11?Tg00Ghk21>Tg00HHS02j23Tg00Hbk21pTg00Ick310Tg00JZj1?Tg00K9k30~Tg00L0k30}Tg00Lgj2cTg00MAmg0|Tg00N>m?0{Tg00O;j3nTg00OXk31OTg00PSk10]Tg00QKj1dTg00RCj1MTg00Rak309Tg00SYj26Tg00TRk21HTg00ULk20ETg00VFk30QTg00W@j4wTg00X:k30=Tg00Y4k50DTg00Z1k11CTg00Zmk20tTg00[kk30:Tg00\dp<1@0sTg00]aj1fTg00^Aj3GTg00^bk41ATg00_Ak20CTg00`8k30rTg00a9mv0qTg00b7k20NTg00bXk40pTg00c3k40oTg00d2k20nTg00dgk10mTg00ebk70lTg00f\j30Tg00g6k30kk41jTg00h6k10jTg00i3k10iTg00j3k10hTg00jjk30gTg00kFk10fTg00l>k31=Tg00m<k31<Tg00n7k30BTg00o3k11;Tg00ook31:TP2j6KTg010lk420Tg011Pk118Tg012FmO17Tg013Dk816Tg014Bk11~Tg0159k21}Tg0165k11|Tg016Sk11{Tg0171k11zTg017\k213Tg018?k40`Tg018jk21xTg019Lk21wTg01:8k31vTg01:Wk41uTg01;Imk1tTg01<Ck30^Tg01=?mS1sTg01><k21rTg01>dk31qTg01?Hk21oTg01?ik31nTg01@Lk21mTg01APk60\Tg01Ank20LTg01Bfk21kTg01Cck61iTg01DDk41hTg01EEk61fTg01FHk41eTg01GIk11dTg01HEmD1cTg01IBk11bTg01J:j3OTg01K1k11`Tg01KJk21_Tg01Kgk30>Tg01LDk30PTg01M1k30<Tg01MNk20WTg01NHk20OTg01Nfk30VTg01OBk30STg01PAk70RTg01Q>k11^Tg01R8k31]Tg01Rok11\Tg01Snk11[Tg01Tck11ZTg01U^k21YTg01V^k20ITg01WPk21XTg01XGk21WTg01Xek21VTg01YHk81UTg01YlmI1STg01Zok20?Tg01[jk11TTg01\_j5ITg01]QS03j2aTP0k304Tg01]kk21NTg01^ek81lTg01_dj7hTg01`^k60JTg01a]m>0yTg01b[mS0xTg01cYk311Tg01d<k31LTg01e5k30FTg01eok71KTg01fSk71yTg01g7m=1JTg01h0k30ATg01hdk314Tg01i>k30TTg01iXR0P0f1R2f0R3CRp>02P0f2R6P2P3CRp=Vf4R7P0f3R8P6P2CR<043p=j%J3g01j6R96112p=L20I62=083p=yg01jRR:f7R;f6R<f5R=P7P8P6P2P3Fh41Lp=Dg01kIR>/Q3p=l%73#7p>00A003>p>0d%83#8p=Z%83#8#8#8p>0a%83#8#8#8#8#8#8#8p>06%73#7#7#7p>0M%73#7#7#7#7#7#7#7p=\%73#7#7#Jp=b%83#8#7#7p=v%73#8p=X%83#7p=[%73#Jp=9%?3#?p>1g%?3#?#?#?p>0[P0g01kgR?P2P3CRp=5AA6239A78p=1%83#Jp=;g01lFR@?A23p>03%?3#?#?#?#?#?#?#?p>1Q%?3#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?p>1P%?3#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?p=E%83#7#7#7p=}&0H3$0]p=F%J3#dp=mg01m@RAAAA239AA69AA87A7p=^g01n8S04B0F862;A3p>1IQ04B0F<=7Q04B0F862;A33Ap=<1686@0=23p=Tg01o2RB?A23p>1FAAB239AB6p>1DAAB239AB69AB89AB7p=WB11239p>0;P6PAP2P3CRp=4P8PAP6P2CR=A73p=eg01olR9g020LS05703p=SP8PAP0P?P6P2CRP3CRp=YP0P0P3P>CRp>19AA423p>0cAA4239A469A489A47p=:B0>023p>07B0<023p>08Q041678@0F62;A3p={B0=862=AB3p>15B0=<=7B0=862=AB35ABp==21303p=tP0P2g020lP3H0`p>0@P2g021SS06g0222S07Q07g022RS08P3g0232K1Kp=~P6Q06Q07Q07Q08P2P3K1yp>12g023RS09g024LS0:g025jS0;g026dS0<P3P2P6P8P7P=P<P;f8RCN=1Jp>0Z1B23,B6p>0X20I86=072/B3p=`Q0:P<P=P7P8P6DI<0A2/B3p=i1a03p=xQ0:P=P7P8P6P2DI<0A3p=pQ0:P=P7P8P6P2DI80A</B3p>0zQ0:P7P8P6P2P3DI80A=p>0UA0=78A0623g027^S0='3'3p=NA0<=7A0862/33'3p=2A0623Q0='3p=H1323,36,38,37p=@1c23:1486p=kQ0=,33p=q1323,36p=zA0862/33,37,3=p=|A0=781323,36'3p=_A0862/33,37p>0G1c23:1486:0T=7p=rQ0=,33,32p=uB0T623:0T78p=>Q0:@0A23p>05g028;S0>p-0S0?[g029BRD#7S0@#8S0A$0HREQ0@#7RF#7S0B#7RG#7S0C#7RH$0HRI$0vRJ+21S0Dg029gS0E&0K2S0Fp,2raS0Gp,2spRKp,2gpS0Hp,2tpS0Ip,2s0S0Jp,2s1S0Kp,2s2S0Lp,2s3S0Mp,2s4S0Np,2s5S0Op,2s6S0Pp,2s7S0Qp,2s8S0Rp,2s9S0Sp,3s10S0Tp,3s11S0Up,2awS0Vp,4thisRLp,2poRMp,3tidRNp,5pconsS0Wp,6icountS0Xp,2ffROp,2fpRPp,2blRQp,2bcS0Yp,2ndS0Zp,2nkS0[p,2bwS0\p,3encS0]NN1aRRg02:^RS7o6PR20_IKRTP6g02;WS0^CCPRPOP8g02<PS0_CCPRQ0B#JS0`-1BORUP7%U4S0aCCPKp,2m1S0bPMPOPPP=J0eRV20b:<RWp,1HS0c1]00S0d/]0RXQ0dP0Q0A#J002OPPCRp,2LFS0e3AS0f<0Y;RYQ0DQ0E&0K81]0XS0g,]0S0hQ0gP6AVXN2S0ip,4entsS0jDjPJP=Q0A#7RZ,LES0k1PI8Cyg02=IS0l9oR<S0mPRPTP<g02>CR[CCPRPOP;g02?<R\CCPRPUPCg02@5R]CCPKQ0bPMPOPPf9R^J0ef:R_-0b:Q0cQ0ff;R`40Y21MKOS0nfFS0of<Ra3gfIRbf>S0pp,1FRcg02@n,PIS0qp,2fcRd&0wJRef=Rf&1G:RgGD[[[[[[[[[[[^4X^10]Q]=Q0DQ0EQ0FQ0l9oR6PRPTP6P[CCPRPOP8P\CCPRPUP7P]CCQ0nfCR];gCQ0oP_Pcg02Ao,PIS0rPdPeP^PgGD[\Y\W\V[[[[[]Q]=p,5HCEILS0sQ0cPKQ0bPLPMQ0WQ0Xp,2loS0tPOPPp,3ICNS0up,3STKS0vp,4CEILS0wp,2LOS0xp,4SPHIS0yp,3FFRS0zp,6FSB_OKS0{NB1E%lTQ0@#JS0|%JHS0}+0uS0~-01T'BS10Q0s$1@RVg02C3's/QTS11g02D6RW,QTS12Q0c$1?RTg02E2'sRY/QOS13%7HS14#7S15#7$00RU#JS16,sOg02Em,sTR\'QS17Q0}-1>O$0dS18g02Fi,sT/QP201PY'BS19g02GfRY/QTS1:1Q\VS1;%7US1<#J-1>T$0dS1=g02H`RU,Q\g02I^R\/QT'3S1>%8DS1?#8S1@#8S1A#8S1B#8#ZS1C#8#Z$0aRT#7$06$0M#\#\#b/QV%8TRT$06R[$0M#\#\#b,QV'BS1D'BS1E'BS1F'BS1G'BS1H'BS1I'BS1J'BS1K'BS1L'BS1M'BS1N'BP1Q10Q1NQ0pPfPc%ZD#v#X#[#v#[#bS1O,PIRVPdPePaPgGDP3Q10Q1NP1Q11Q1MfBS1PfARhPcPVPdPef@S1QPgGDP3Q11Q1MP1Q12Q1LQ0ofERiPcPVPdPefDS1RPgGDP3Q12Q1LP1Q13Q1KfJS1SPbPcPVPdPefHS1TPgGDP3Q13Q1KP1Q17Q1JfNS1UfMRjPcPVPdPefLS1VPgGDP3Q17Q1JP1Q18Q1IfRS1WfQRkPcPVPdPefPS1XPgGDP3Q18Q1IP1Q19Q1HfVS1YfUS1ZPcPVPdPefTS1[PgGDP3Q19Q1HP1Q1:Q1GfZS1\fYS1]PcPVPdPefXS1^PgGDP3Q1:Q1GP1Q1;Q1Ff^S1_f]S1`PcPVPdPef\S1aPgGDP3Q1;Q1FP1Q1=Q1EfbfaS1bPcPVPdPef`S1cPgGDP3Q1=Q1EP1Q1>Q1DffS1dfeS1ePcPVPdPefdS1fPgGDP3Q1>Q1Dp,3THOS1g%8FS1h#7S1i#7S1j#7S1k#7Rl#9S1l-1pLP11QYLS1mQ1l,sLRY/QU1Q\L'3S1n1QYWS1o'BS1pfkS1qfjS1rPcPVPdPefiS1sPgGDP3Q1mQ1pP1Q1nQ1ofoS1tfnS1uPcPVPdPefmS1vPgGDP3Q1nQ1oPRQ0^1]0?RV#URY610KQ0_PVP0P?P>g02JY#?R?#?$1gS1w$0[RWCRS1xPVQ0`/5WS1y%JGS1z/5WS1{=AVYD1S1|60~OQ0aPV%7T$00$0MRT#7R\#7RU#7Rm#7Rn#7Ro#7Rp#7Rq#9S1}/5?S1~PV%;qS20/5?S21PV%8pRp#9S22/5?S23PV%;pS24/5?S25PV%8oRo#7Rp#9S26/5?S27PV%;pS28/5?S29PV%8oRo#9S2:/5?S2;PV%;oS2</5?S2=PV%8nRn#8Ro#7Rp#9S2>/5?S2?PV%;pS2@/5?S2APV%8oRo#9S2B/5?S2CPV%;oS2D/5?S2EPV%7nRn#7Ro#9S2F/5?S2GPV%;oS2H/5?S2IPV%8nRn#9S2J/5?S2KPV%;nS2L/5?S2MPV%8mRm#7Rn#8Ro#7Rp#9S2N/5?S2OPV%;pS2P/5?S2QPV%8oRo#9S2R/5?S2SPV%;oS2T/5?S2UPV%7nRn#7Ro#9S2V/5?S2WPV%;oS2X/5?S2YPV%8nRn#9S2Z/5?S2[PV%;nS2\/5?S2]PV%8mRm#8Rn#7Ro#9S2^/5?S2_PV%;oS2`/5?S2aPV%8nRn#9S2b/5?S2cPV%;nS2d/5?S2ePV%7mRm#7Rn#9S2f/5?S2gPV%;nS2h/5?S2iPV%8mRm#9S2j/5?S2kPV%;mS2l/5?S2mPV%8URU#7Rm#7Rn#8Ro#7Rp#9S2n/5?S2oPV%;pS2p/5?S2qPV%8oRo#9S2r/5?S2sPV%;oS2t/5?S2uPV%7nRn#7Ro#9S2v/5?S2wPV%;oS2x/5?S2yPV%8nRn#9S2z/5?S2{PV%;nS2|/5?S2}PV%8mRm#8Rn#7Ro#9S2~/5?S30PV%;oS31/5?S32PV%8nRn#9S33/5?S34PV%;nS35/5?S36PV%7mRm#7Rn#9S37/5?S38PV%;nS39/5?S3:PV%8mRm#9S3;/5?S3<PV%;mS3=/5?S3>PV%8URU#7Rm#8Rn#7Ro#9S3?/5?S3@PV%;oS3A/5?S3BPV%8nRn#9S3C/5?S3DPV%;nS3E/5?S3FPV%7mRm#7Rn#9S3G/5?S3HPV%;nS3I/5?S3JPV%8mRm#9S3K/5?S3LPV%;mS3M/5?S3NPV%8URU#8Rm#7Rn#9S3O/5?S3PPV%;nS3Q/5?S3RPV%8mRm#9S3S/5?S3TPV%;mS3U/5?S3VPV%7URU#7Rm#9S3W/5?S3XPV%;mS3Y/5?S3ZPV%8URU#9S3[/5?S3\PV%;US3]/5?S3^PV%8\R\#7RU#7Rm#7Rn#8Ro#7Rp#9S3_/5?S3`PV%;pS3a/5?S3bPV%8oRo#9S3c/5?S3dPV%;oS3e/5?S3fPV%7nRn#7Ro#9S3g/5?S3hPV%;oS3i/5?S3jPV%8nRn#9S3k/5?S3lPV%;nS3m/5?S3nPV%8mRm#8Rn#7Ro#9S3o/5?S3pPV%;oS3q/5?S3rPV%8nRn#9S3s/5?S3tPV%;nS3u/5?S3vPV%7mRm#7Rn#9S3w/5?S3xPV%;nS3y/5?S3zPV%8mRm#9S3{/5?S3|PV%;mS3}/5?S3~PV%8URU#7Rm#8Rn#7Ro#9S40/5?S41PV%;oS42/5?S43PV%8nRn#9S44/5?S45PV%;nS46/5?S47PV%7mRm#7Rn#9S48/5?S49PV%;nS4:/5?S4;PV%8mRm#9S4</5?S4=PV%;mS4>/5?S4?PV%8URU#8Rm#7Rn#9S4@/5?S4APV%;nS4B/5?S4CPV%8mRm#9S4D/5?S4EPV%;mS4F/5?S4GPV%7URU#7Rm#9S4H/5?S4IPV%;mS4J/5?S4KPV%8URU#9S4L/5?S4MPV%;US4N/5?S4OPV%8\R\#7RU#7Rm#8Rn#7Ro#9S4P/5?S4QPV%;oS4R/5?S4SPV%8nRn#9S4T/5?S4UPV%;nS4V/5?S4WPV%7mRm#7Rn#9S4X/5?S4YPV%;nS4Z/5?S4[PV%8mRm#9S4\/5?S4]PV%;mS4^/5?S4_PV%8URU#7Rm#7Rn#9S4`/5?S4aPV%;nS4b/5?S4cPV%8mRm#9S4d/5?S4ePV%;mS4f/5?S4gPV%8URU#7Rm#9S4h/5?S4iPV%;mS4j/5?S4kPV%8URU#9S4l/5?S4mPV%;US4n/5?S4oPV%8\R\#7RU#8Rm#7Rn#9S4p/5?S4qPV%;nS4r/5?S4sPV%8mRm#9S4t/5?S4uPV%;mS4v/5?S4wPV%7URU#7Rm#9S4x/5?S4yPV%;mS4z/5?S4{PV%8URU#9S4|/5?S4}PV%;US4~/5?S50PV%8\R\#8RU#7Rm#9S51/5?S52PV%;mS53/5?S54PV%8URU#9S55/5?S56PV%;US57/5?S58PV%7\R\#7RU#9S59/5?S5:PV%;US5;/5?S5<PV%8\R\#9S5=/5?S5>PV%;\S5?/5?S5@PV%[TS5A#7RT#7R\#7RU#8Rm#7Rn#9S5B/5?S5CPV%;nS5D/5?S5EPV%8mRm#9S5F/5?S5GPV%;mS5H/5?S5IPV%7URU#7Rm#9S5J/5?S5KPV%;mS5L/5?S5MPV%8URU#9S5N/5?S5OPV%;US5P/5?S5QPV%8\R\#8RU#7Rm#9S5R/5?S5SPV%;mS5T/5?S5UPV%8URU#9S5V/5?S5WPV%;US5X/5?S5YPV%7\R\#7RU#9S5Z/5?S5[PV%;US5\/5?S5]PV%8\R\#9S5^/5?S5_PV%;\S5`/5?S5aPV%8TRT#7R\#8RU#7Rm#9S5b/5?S5cPV%;mS5d/5?S5ePV%8URU#9S5f/5?S5gPV%;US5h/5?S5iPV%7\R\#7RU#9S5j/5?S5kPV%;US5l/5?S5mPV%8\R\#9S5n/5?S5oPV%;\R\/5?S5pPV%8TRT#8RU#7Rm#9Rn/5?S5qPV%;mRm/5?S5rPV%8URU#9Ro/5?S5sPV%;URU/5?S5tPV%7TRT#7Rp#9Rq/5?S5uPV%;pRp/5?S5vPV%8TRT#9Rr/5?S5wPV%;TRT/5?S5xPYD1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1S5y60}O%U@S5z+03+03+03R@Q0sQ0cQ0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0bPLPMPNQ0WQ0XQ0tPOPPPQQ0YQ0ZQ0[Q0\Q0]p,3DSOS5{p,3PCOS5|Q0uQ0vQ0wQ0xQ0yQ0zQ0{Q0^Q0_Q0aPYQ1|Q5yQ05,c9RsPsPsPsPsPsNg0|PKQ0bPMPOPPI1RS5}PKQ0bPLPMQ0WQ0XPOPPQ0uQ0^Q0_Q0aPYQ1|Q5yN?0{frS5~fqS60PcQ1OPdfpS61PgPS%UJS62g02K8S63%UBS645nBS65&0[W$1Q$1P#E#ES66$0[#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#ES67%ZD#v#}#X$00#X#bS68%U0S695A0S6:%U9Rt%UAS6;<1OtS6<Q0B#8Rt#8Ru#7$0HS6=Q68g02L3$0]S6>Q1O#dS6?g02LQRv%8G#FRw%Ml#d409S6@Q1?#7S6A#7Rl#8S6B#7#FS6CQ6B#8#FS6D&0]ES6EQ6A#FS6FQ1@#FS6GPwQ6@Q0C#FS6H%7tS6I#7#9S6J#d609vS6K&0a[$06S6L$06$06$06R[#}#mRx&00[S6M#8R[#7#mRy%8[#mR[Q0A#8Rz#8R{#7R|#7#Z#[#X#X#Z#mS6N%8D#Z#}#Z#X$00#X#}#mS6O%FG%FtQ6A#8Rt#7R}#7S6P#FS6Qg02M=S6RQ6QQ1?#JS6S#dS6T409R~Q1}#dS6U609vS6VQ1j#FS1jQ6H%FuS6WQ6U%F|S6X%8{R|#FS6YQ6Q%7lRu#8S6Z#FS6[Q1@#7Rv#7S6\#F%8vS6]#FQ1A#7S6^#FQ1B#FQ6;D^D^D^D^D^S6;D^D^D^16~TS6_P?Px16~rS6`P?Px16~pS6aP?Px16~qS6bP?Px16~US6cP?Px16~oS6dP?Px16~mS6eP?Px16~nS6fP?Px16~\S6gP?PxQ5n,6~S5nP?PxQ5l,6~S5lP?PxQ5j,6~S5jP?PxQ5h,6~S5hP?PxQ5f,6~S5fP?PxQ5d,6~S5dP?PxQ5b,6~S5bP?PxQ5`,6~S5`P?PxQ5^,6~S5^P?PxQ5\,6~S5\P?PxQ5Z,6~S5ZP?PxQ5X,6~S5XP?PxQ5V,6~S5VP?PxQ5T,6~S5TP?PxQ5R,6~S5RP?PxQ5P,6~S5PP?PxQ5N,6~S5NP?PxQ5L,6~S5LP?PxQ5J,6~S5JP?PxQ5H,6~S5HP?PxQ5F,6~S5FP?PxQ5D,6~S5DP?PxQ5B,6~S5BP?PxQ5?,6~S5?P?PxQ5=,6~S5=P?PxQ5;,6~S5;P?PxQ59,6~S59P?PxQ57,6~S57P?PxQ55,6~S55P?PxQ53,6~S53P?PxQ51,6~S51P?PxQ4~,6~S4~P?PxQ4|,6~S4|P?PxQ4z,6~S4zP?PxQ4x,6~S4xP?PxQ4v,6~S4vP?PxQ4t,6~S4tP?PxQ4r,6~S4rP?PxQ4p,6~S4pP?PxQ4n,6~S4nP?PxQ4l,6~S4lP?PxQ4j,6~S4jP?PyQ4h,6~S4hP?PyQ4f,6~S4fP?PyQ4d,6~S4dP?PyQ4b,6~S4bP?PyQ4`,6~S4`P?PyQ4^,6~S4^P?PxQ4\,6~S4\P?PxQ4Z,6~S4ZP?PxQ4X,6~S4XP?PxQ4V,6~S4VP?PyQ4T,6~S4TP?PyQ4R,6~S4RP?PxQ4P,6~S4PP?PxQ4N,6~S4NP?PxQ4L,6~S4LP?PxQ4J,6~S4JP?PxQ4H,6~S4HP?PxQ4F,6~S4FP?PxQ4D,6~S4DP?PxQ4B,6~S4BP?PxQ4@,6~S4@P?PxQ4>,6~S4>P?PxQ4<,6~S4<P?PxQ4:,6~S4:P?PxQ48,6~S48P?PxQ46,6~S46P?PxQ44,6~S44P?PxQ42,6~S42P?PxQ40,6~S40P?PxQ3},6~S3}P?PxQ3{,6~S3{P?PxQ3y,6~S3yP?PxQ3w,6~S3wP?PxQ3u,6~S3uP?PxQ3s,6~S3sP?PxQ3q,6~S3qP?PxQ3o,6~S3oP?PxQ3m,6~S3mP?PxQ3k,6~S3kP?PxQ3i,6~S3iP?PxQ3g,6~S3gP?PxQ3e,6~S3eP?PxQ3c,6~S3cP?PxQ3a,6~S3aP?PxQ3_,6~S3_P?PxQ3],6~S3]P?PxQ3[,6~S3[P?PxQ3Y,6~S3YP?PxQ3W,6~S3WP?PxQ3U,6~S3UP?PxQ3S,6~S3SP?PxQ3Q,6~S3QP?PxQ3O,6~S3OP?PxQ3M,6~S3MP?PyQ3K,6~S3KP?PyQ3I,6~S3IP?PyQ3G,6~S3GP?PyQ3E,6~S3EP?PxQ3C,6~S3CP?PxQ3A,6~S3AP?PxQ3?,6~S3?P?PxQ3=,6~S3=P?PyQ3;,6~S3;P?PyQ39,6~S39P?PyQ37,6~S37P?PyQ35,6~S35P?PyQ33,6~S33P?PxQ31,6~S31P?PxQ2~,6~S2~P?PxQ2|,6~S2|P?PyQ2z,6~S2zP?PyQ2x,6~S2xP?PyQ2v,6~S2vP?PyQ2t,6~S2tP?PyQ2r,6~S2rP?PxQ2p,6~S2pP?PxQ2n,6~S2nP?PxQ2l,6~S2lP?PyQ2j,6~S2jP?PyQ2h,6~S2hP?PyQ2f,6~S2fP?PyQ2d,6~S2dP?PyQ2b,6~S2bP?PxQ2`,6~S2`P?PxQ2^,6~S2^P?PxQ2\,6~S2\P?PyQ2Z,6~S2ZP?PyQ2X,6~S2XP?PyQ2V,6~S2VP?PyQ2T,6~S2TP?PyQ2R,6~S2RP?PxQ2P,6~S2PP?PxQ2N,6~S2NP?PxQ2L,6~S2LP?PyQ2J,6~S2JP?PyQ2H,6~S2HP?PyQ2F,6~S2FP?PyQ2D,6~S2DP?PyQ2B,6~S2BP?PxQ2@,6~S2@P?PxQ2>,6~S2>P?PxQ2<,6~S2<P?PyQ2:,6~S2:P?PxQ28,6~S28P?PxQ26,6~S26P?PxQ24,6~S24P?Q6M#X#mS6MQ22,6~S22P?Q6MQ20,6~S20P?Q6MQ1},6~S6hP?Q6MQ6QQ1z'6S1zPWQ6OQ6QQ0`'6S6iPWQ6NQ6Q/6>S6jPWQ0C#8#[#Z#X#X#}#[#[#[#v#Z#mS6kQ04#US6lH1IF<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<%}|#\#b%7uR|#[#[#\#b+1HS6m%d>S6nQ6Z#Z#[#ZR\#X$0a#bPWQ6UCTS6ZQ6n%[\$0M#bQ1w%JDR\#dS1wCTS6oQ1<#7Rn#MS1<,6wRm%mnRo+0ES6p%\n#\#\#\Rn#J%7n#9Rn60QwS6qQ6jQ16#dRU+0ES6rQ6Q%8D#X#v#v#\#bS6sQ6L#\#b40QS6LQ6hQ15#JS15#dS6t+0ES6u%8}#FRq/6>RpQ1w+0ES6vQ6s>0QqnS6wQ6jPUPmPoCwS6xQ6hQ6tPmPoCwS6yQ6hQ6tQ6jPUCwS6zPpQ1wPmPoCwS6{PpQ1wQ6jPUCwS6|PpQ1wQ6hQ6tCwS6}Q14#MS14,6wS6~Q6n80=WS70PwQ0B#MS71PWQ6I#FS6ICTS72Pw%MGS73PWQ1h#8RG#7#FS74CTS75Pw%MuS76PW%8G#FS77CTS78PwQ0C#MS79PW%7ZRp#7S7:#FS7;CTS7<PwQ7:#MS7=PW%8p#FS7>CTS7?Pw%M|S7@PW%8ZRZ#7#FS7ACTS7BPwQ6\#7#MS7CPW%8Z#FS7DCTS7EPw%MHS7FPW%7zRH#7RU#FS7GCTS7HPwQ1k#MS1kPW%8H#FS7ICTS7JPwQ7:#7#MS7KPWQ6XCTS7LPw%7U#MS7MPWQ6YCTS7NPw%7|#MS7OPW%F|S7PCTS7QPwQ6P#7#MS6PPWQ6[CTS7RQ6QQ1C#bS1CPWPqCTS7SQ64+1F41DDWDWDWDWDWDWDWQ6=I0DS7Tg02MiS7U#US7VQ6<&0vER|/]ARU20;E\RoQ6?54|S7WPUQ0|-0;ERmQ6@54|S7XPUQ6S-0;ERnQ6C54|S6SPU1LEFRFQ6D54|S7YPUQ0`-0;ERr=4|wS7ZPUQ1h,LERTQ6@54|S7[PUQ0kQ6K54|S7\PU1LEzS7]=4|xPUP|1LElPyPUP|1LEtP[PUP|1LEvQ6NPUP|Q1A,LEQ6OPUP|Q1i,LERvQ6QPUP|1LEGRGQ6VPU1LEpRpQ1j54|S6VPU1LEZRZQ6H54|S1iPUP|1LEHRHQ6WPU1LE{R{Q6U54|S6WPU%JuS1A-0;ERuQ6X54|PUP|Q6B,LERlQ6YPUP|1LE}R}Q6QPUP|%8t,LERtQ6[%UUDeDeDeD1DeD1DeDeS6BDeDeDeDeS7^D1D1D1D1S7_Q1tQ1uPs&1CRS7`00tS#SdQ0sQ0cQ0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0bPLPMPNQ0WQ0XQ0tPOPPPQQ0YQ0ZQ0[Q0\Q0]p,3DSAS7ap,3DSWS7bQ5{p,3DS8S7cp,3DSVS7dp,3DSHS7ep,3DSMS7fp,3PCAS7gQ5|p,3PC8S7hp,3PCCS7ip,4DISJS7jQ0uQ0vQ0wQ0xQ0yp,5SPOBJS7kQ0zQ0{p,4FFDSS7lp,4FFPCS7mp,4FPPCS7np,4FPDSS7op,4HULLS7pp,3FRWS7qp,3FSVS7rp,3FSWS7sp,3FLWS7tp,3AC1S7up,3LV1S7vQ61Q0^Q0_Q0aPYQ1|Q5yQ1rQ1sQ1vflS7wQ1qPsQ1<@0:>Y#SdS1<PsQ16Q1|60:>#SdPsg02NeS7xQ7xQ15'sS15Q5y40:#Sdp#1@0sQ1rQ1sQ0?\3S0?%f2S7y%f6S7zP1An8239G86AG786AG782S7{'BRz[AG862AG863S7|'BAn7629G78[S7}An=869G=7\zP8P6P2P3H1AP3n2001000000120000000WPWOW<X;5S7~Q0?Q7yQ7zQ7}]P]O]<^;5S7yP3PBQ5~Q629nJRS7}+0CQ6060r:RzQ63Q64Q639GBzQ649GBzQ0sQ0cQ0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0bPLPMPNQ0WQ0XQ0tPOPPPQQ0YQ0ZQ0[Q0\Q0]Q7aQ7bQ5{Q7cQ7dQ7eQ7fQ7gQ5|Q7hQ7iQ7jQ0uQ0vQ0wQ0xQ0yQ7kQ0zQ0{Q7lQ7mQ7nQ7oQ7pQ7qQ7rQ7sQ7tQ7uQ7vQ5~Q62Q60Q1qQ1rNv0q20NBzH0pO5b0P:Q60Q7}+0CS80Q61Q65H0oeg02O`S81Q7U#fS82']S83g02P]S84']S85Q83Q84Q81Q82Q7TQ7VCRQ6<CRRz'cQ85P:Q67Q05Q6:Q6<Q1Og02QXS1O00nSQ6lQ65&0m@5nBQ6=I0DQ7VK0l;0zdQ7UQ61Q8060k:+0NPsQ04&0j@$0iQ7T$0hRz40g#SdPsQ7`Q7T$0fQ7_41=#SdQ0DQ0EQ0FQ7_9oR6Q7`>1<z@S80:0BR6PKQ0bPMPOPPP8J0eS6520b:7S6:&1;@S67fwS86;g=fxS87>1::<1]VAR@#fS88,]0S89#fS8:Q89Q88Q00PIP0PKP2n10110M00012010L10KS00Q14/5WS14Q6n54VS8;P@PVQ71PWQ6ICYS6IP@PVQ73PWQ74CYS74P@PVQ76PWQ77CYS77P@PVQ79PWQ7;CYS7;P@PVQ7=PWQ7>CYS7>P@PVQ7@PWQ7ACYS7AP@PVQ7CPWQ7DCYS7DP@PVQ7FPWQ7GCYS7GP@PVQ1kPWQ7ICYS7IP@PVQ7KPWQ6XCYS6XP@PVQ7MPWQ6YCYS6YP@PVQ7OPWQ7PCYS7PPVQ6PPWQ6[CYS6[%U@S6P5A@D1D1D1D1D1D1S7O5A@3VQ89Q88P@PVQ1CPWPqCYS1CP@Q1xQ6k54VS1xP@Q1yQ6N54VS1yP@Q1{Q6O54VS1{Q6PD1D17VOS7MQ89Q88Q01P0P0P0P0Q0dPOP0P0P>P>CRg02RORqQ0d^20]2PqQ0dP2Q01P0P0Q0dP8P3P2O2S7KP9Q0dg02S4RzP9P0PzP0P0P0P0P3P>%73S1k#JS7FQ1k#MS7Cn0110M0003001000010000S7@P\Pq^2qS7=^2qS79PqPqP2PqPqP2P7P2P3O2S76#7S73P=P2P3O2S71#8S8<Q7=PqPqP3P6P3O1S8=#7%83RSQ0@n0110M0003100001000000X2qp?100010JP3O1S8>#7S8?n0110M0003100001000000S8@PqPqP2Q8<Q71#7PSn0110M0003100001000000PqPqP3Q8?PSQ0@n0110M0003100001000000S71n0110M0003100001000000X2qX2qQ79PqPqP2PqPqP2Q76#8Q73Q8>#8S8>n0110M0003100001000000Q8@PqPqP3Q8>Q8?Q1?n0110M0003100001000000n0110M0003100001000000X2qX2qp?200010J0010JS8?P3PDO2#JS8>P0^2q^2qPqP0P2PqP0P2P0P0Q76P>Q7FQ7Cn0110M0003001000010000S8@P0P0Q76P\%JSQ7=PqPqP3Q1k#8Q8=#8PDn0110M0003100001000000X2qp?100010JP3O1S8=#MS1kn0110M0003001000010000Q7Fn0110M0003100001000000PqP0P2P0P0Q76%MDQ8=#JS8=%MSn0110M0003001000010000Q8@Q8=n0110M0003100001000000PqP0P3Q7CQ1kP>n0110M0003100001000000n0110M0003100001000000X2qX2qp?100110JS1kPDP3O2S8=n0110M0003001000010000S8@P0PzP8g02SZS76g02T@S7=g02TfRSn0110M0003001000010000S73P0PzP7PSPz^2q^2q^2zPqPzP2PqPzP2P=P7P2P3O3S79P=PSP2P3O3PSn0110M0003100001000000PqPzP2P=Q7=P2P3O3Q79PSn0110M0003100001000000PqPzP3Q7=Q7=P6n0110M0003100001000000n0110M0003100001000000X2qX2qX2zp?100210JS79Q76P2P3O3S8<PSn0110M0003001000010000S8AP0PzP7Q7=Q7=PzPzQ8<Q76PSQ7=n0110M0003000000n0110M0003001000010000S7=n0110M0003001000010000g02ULS8<Q05Q8<n0110M0003000000P0P0P2P>Q7FQ7Cn0110M0003001000010000S7CQ8@+02P0P0Q7CP\Q8>Q8=n0110M0003001000010000S7FP0P0Q8@P0P0P8P>%M3S8@%J3S8Bn0110M0003001000010000S8CP0P0P0P0P7P>Q8@Q8Bn0110M0003001000010000S8DQ7FQ8?P2P3O2S8?#JS8EQ1kP2P3O2S8Fn0110M0003011000010000P0P0Q8DQ7FQ1kP3P2O2S8GQ8?#MS8?n0110M0003011000010000n0110M0003001100011000+02n0110M00020101n200110M000121000000Q01P0P0Q0dQ7KP9Q0dPzP9P0PzQ7@Q73Q8AQ7=n0110M0003001000010000Q8<Q05Q8<n0110M0003000000Q7CQ7@+02Q7FP0P0Q7@Q8CP0P0Q8DQ7CQ8EQ8Fn0110M0003001000010000P0P0Q8DQ7CQ8GQ8?n0110M0003001000010000n0110M0003001100011000+02n0110M00020001n200110M000121000000P9Q0dPzP9P0PzP3PSQ79Q76Q0@P3O3PSn0110M0003001000010000Q05Q05Q8<n0110M0003000000P0P0P>P\CR&19\n0110M00020000n0110M0003110001100000X20X2qp?100010JP3Q0`O2RSQ01P0P0Q0dPSP0Q0dP3P0P0P2P>Q8@Q8Bn0110M0003001000010000RS$19P0P0P0P0P6P\Q8>Q8=n0110M0003001000010000P>Q8@Q8Bn0110M0003001000010000P0P0PSQ0`PqPqP3PqPqP3PqPqP3Q71#8Q71#7Q1?n0110M0003100001000000Rq#8%7qQ0An0110M0003100001000000Rq#8%7qQ1hn0110M0003100001000000#JQ1kQ0BP3O2n0110M0003001100010000+02RqPqn0110M0003001100011000n200110M000121000000n0110M0003001100011000P2n200110M000120000000S0BP@Q1~Q6M54VS1~P@Q21Q6M54VS21P@Q23Q6M54VS23P@Q25Q6M54VS25P@Q27=4VxS27P@Q29=4VxS29P@Q2;=4VxS2;P@Q2==4VyS2=P@Q2?=4VxS2?P@Q2A=4VxS2AP@Q2C=4VxS2CP@Q2E=4VyS2EP@Q2G=4VyS2GP@Q2I=4VyS2IP@Q2K=4VyS2KP@Q2M=4VyS2MP@Q2O=4VxS2OP@Q2Q=4VxS2QP@Q2S=4VxS2SP@Q2U=4VyS2UP@Q2W=4VyS2WP@Q2Y=4VyS2YP@Q2[=4VyS2[P@Q2]=4VyS2]P@Q2_=4VxS2_P@Q2a=4VxS2aP@Q2c=4VxS2cP@Q2e=4VyS2eP@Q2g=4VyS2gP@Q2i=4VyS2iP@Q2k=4VyS2kP@Q2m=4VyS2mP@Q2o=4VxS2oP@Q2q=4VxS2qP@Q2s=4VxS2sP@Q2u=4VyS2uP@Q2w=4VyS2wP@Q2y=4VyS2yP@Q2{=4VyS2{P@Q2}=4VyS2}P@Q30=4VxS30P@Q32=4VxS32P@Q34=4VxS34P@Q36=4VyS36P@Q38=4VyS38P@Q3:=4VyS3:P@Q3<=4VyS3<P@Q3>=4VyS3>P@Q3@=4VxS3@P@Q3B=4VxS3BP@Q3D=4VxS3DP@Q3F=4VxS3FP@Q3H=4VyS3HP@Q3J=4VyS3JP@Q3L=4VyS3LP@Q3N=4VyS3NP@Q3P=4VxS3PP@Q3R=4VxS3RP@Q3T=4VxS3TP@Q3V=4VxS3VP@Q3X=4VxS3XP@Q3Z=4VxS3ZP@Q3\=4VxS3\P@Q3^=4VxS3^P@Q3`=4VxS3`P@Q3b=4VxS3bP@Q3d=4VxS3dP@Q3f=4VxS3fP@Q3h=4VxS3hP@Q3j=4VxS3jP@Q3l=4VxS3lP@Q3n=4VxS3nP@Q3p=4VxS3pP@Q3r=4VxS3rP@Q3t=4VxS3tP@Q3v=4VxS3vP@Q3x=4VxS3xP@Q3z=4VxS3zP@Q3|=4VxS3|P@Q3~=4VxS3~P@Q41=4VxS41P@Q43=4VxS43P@Q45=4VxS45P@Q47=4VxS47P@Q49=4VxS49P@Q4;=4VxS4;P@Q4==4VxS4=P@Q4?=4VxS4?P@Q4A=4VxS4AP@Q4C=4VxS4CP@Q4E=4VxS4EP@Q4G=4VxS4GP@Q4I=4VxS4IP@Q4K=4VxS4KP@Q4M=4VxS4MP@Q4O=4VxS4OP@Q4Q=4VxS4QP@Q4S=4VxS4SP@Q4U=4VyS4UP@Q4W=4VyS4WP@Q4Y=4VxS4YP@Q4[=4VxS4[P@Q4]=4VxS4]P@Q4_=4VxS4_P@Q4a=4VyS4aP@Q4c=4VyS4cP@Q4e=4VyS4eP@Q4g=4VyS4gP@Q4i=4VyS4iP@Q4k=4VyS4kP@Q4m=4VxS4mP@Q4o=4VxS4oP@Q4q=4VxS4qP@Q4s=4VxS4sP@Q4u=4VxS4uP@Q4w=4VxS4wP@Q4y=4VxS4yP@Q4{=4VxS4{P@Q4}=4VxS4}P@Q50=4VxS50P@Q52=4VxS52P@Q54=4VxS54P@Q56=4VxS56P@Q58=4VxS58P@Q5:=4VxS5:P@Q5<=4VxS5<P@Q5>=4VxS5>P@Q5@=4VxS5@P@Q5C=4VxS5CP@Q5E=4VxS5EP@Q5G=4VxS5GP@Q5I=4VxS5IP@Q5K=4VxS5KP@Q5M=4VxS5MP@Q5O=4VxS5OP@Q5Q=4VxS5QP@Q5S=4VxS5SP@Q5U=4VxS5UP@Q5W=4VxS5WP@Q5Y=4VxS5YP@Q5[=4VxS5[P@Q5]=4VxS5]P@Q5_=4VxS5_P@Q5a=4VxS5aP@Q5c=4VxS5cP@Q5e=4VxS5eP@Q5g=4VxS5gP@Q5i=4VxS5iP@Q5k=4VxS5kP@Q5m=4VxS5mP@Q5o=4VxS5oP@Q5p=4VxS5pP@Q5q=4VxS5qP@Q5r=4VxS5rP@Q5s=4VxS5sP@Q5t=4VxS5tP@Q5u=4VxS5uP@Q5v=4VxS5vP@Q5w=4VxS5wP@Q5x=4VxS5xQ6PD1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D13VQ89#US1k3AD1'c%f4R4,]0Rq#fS1hQ80Q00Q8;Q6IQ74Q77Q7;Q7>Q7AQ7DQ7GQ7IQ6XQ6YQ7PQ6[Q0a+0cD:D:D:S6[+0cS8;5V4RSQ1CQ1xQ1yQ1{Q0aD:S1{9V4OS1yQ0BQ1~Q21Q23Q25Q27Q29Q2;Q2=Q2?Q2AQ2CQ2EQ2GQ2IQ2KQ2MQ2OQ2QQ2SQ2UQ2WQ2YQ2[Q2]Q2_Q2aQ2cQ2eQ2gQ2iQ2kQ2mQ2oQ2qQ2sQ2uQ2wQ2yQ2{Q2}Q30Q32Q34Q36Q38Q3:Q3<Q3>Q3@Q3BQ3DQ3FQ3HQ3JQ3LQ3NQ3PQ3RQ3TQ3VQ3XQ3ZQ3\Q3^Q3`Q3bQ3dQ3fQ3hQ3jQ3lQ3nQ3pQ3rQ3tQ3vQ3xQ3zQ3|Q3~Q41Q43Q45Q47Q49Q4;Q4=Q4?Q4AQ4CQ4EQ4GQ4IQ4KQ4MQ4OQ4QQ4SQ4UQ4WQ4YQ4[Q4]Q4_Q4aQ4cQ4eQ4gQ4iQ4kQ4mQ4oQ4qQ4sQ4uQ4wQ4yQ4{Q4}Q50Q52Q54Q56Q58Q5:Q5<Q5>Q5@Q5CQ5EQ5GQ5IQ5KQ5MQ5OQ5QQ5SQ5UQ5WQ5YQ5[Q5]Q5_Q5aQ5cQ5eQ5gQ5iQ5kQ5mQ5oQ5pQ5qQ5rQ5sQ5tQ5uQ5vQ5wQ5xQ0aD:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:S1x5V4S1C%UqS7P5AqS6Y5AqR95AqS6X30S7IdQ7IQ1hQ80Q1hB0BR^3W:S80P=Q6XP3EKQ6X:0BRCQ0?Q7zP1AA8239G86P8P6O1Q7{'B[S7{P6P2O1Q7|'BAA7629G78S7|[Q7|P7P8O1AG=76'B[P8P6P2P3H20P2n2001000000120000000W:XD2W<X;5S7|Q0?Q7zQ7{]:^D2]<^;5S0?P3PqPR20743R5P`20843S7zCCX1qS7{PSP9P2O5PR2074SS6XP_2084SRSCCQ7{=Gq9'BP1PRQ6XP`PSCCPRP5PaQ7zCCX1qS7I=Gq9p+01AS7GPfPcQ7T$18,PIS7TPdPePaPgGDP3PRQ6XPfPSCCPRP5f?RSQ7zCCX1qS6X=Gq9Q7|Q0?P3PqPRP5PhQ7zCCX1qS7DQ1yQ6YP2O5PRQ1y-074S7AQ1QQ1y-084R9CCS7>Q7DQ6Y5Gq'BP1PRQ7APhP9CCS7;PRP5Q1PQ7zCCX1qS77Q6Y5Gqp+01GP]PcQ7TPdPeQ1PPgGDP3PRQ7AP]P9CCS7APRP5PiQ7zCCX1qS74Q6Y5GqQ7|Q0?P3PqPRP5fGR9Q7zCCX1qS6YQ1CQ7PP2O5PRQ1C-074S6IQ0oQ1C-084S1CCCQ6YQ7P5GqS0A'BP1PRQ6IP9Q1CCCPRP5Q1TQ7zCCX1qQ7P5GqS1?p+01MPbPcQ7TPdPeQ1TPgGDP3PRQ6IPbQ1CCCPRP5fKR5Q7zCCX1qQ7P5GqS7zQ0sQ0cp,4HHbpS1CPKQ0bPLPMQ0WQ0XQ0tPOPPQ0eQ0uQ0vQ0wQ0xQ0yQ0zQ0{Q0^Q0_Q0aPYQ1|Q5yp+01NP5p+01FPiQ1RNO17Q0cQ0f<0Y5S0fQ0d#fS0dQ67Q0dp+01PS67=g3jW:Q0oQ0nPKPOQ0^Q0_Q0aPYQ1|Q5yL16EKQ0np+01OQ1V3gPRQ8;>10KYQ1{>0~OYQ1xPVQ5A#8$00S5A#8S5y#7S1|#9S0_/5?S0^PVQ1|#;S1|/5?S6IPVQ5y#8S5y#9S71/5?S8BPVQ5y#;S5y/5?S8@PVQ5A#7S5A#7S8=#9S8>/5?S01PVQ8=#;S8=/5?S8<PVQ5A#8S5A#9S0@/5?S76PVQ5A#;S5A/5?S79PYD1D1D1D1S7F60}OQ5z+03+03+03S5zQ0sQ0cQ0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0bPLPMPNQ0WQ0XQ0tPOPPPQQ0YQ0ZQ0[Q0\Q0]Q5{Q5|Q0uQ0vQ0wQ0xQ0yQ0zQ0{Q8;Q1{Q1xPYPYQ7FPsPsPsPsPsPsNg0|Q5}PKQ0bPLPMQ0WQ0XPOPPQ0uQ8;Q1{Q1xPYPYQ7FN?0{p+01RQ1UPcQ68PdPjPgQ7_Q62Q63Q6J$1~S5}5nBS8?Q66%ZD#v#}#X#X#Z#[#9S8GQ695A0S69Q6<Q6=Q8GQ6>Q6?Q6@Q6CQ6DQ6EQ6FQ6GPwQ6@Q6KQ6nQ6;D^D^D^Q6~PWQ6QQ5A,6~P?P[P~Q0@P?P[P~Q8=P?P[P~Q8>P?P[P~Q5yP?P[P~Q71P?P[P~Q1|P?P[P~Q0_P?P[Q6lD{D{D{D{D{D{D{F<Q6mQ6ZQ6oQ6pQ6qQ6rQ6LQ6uQ6vQ6wQ6xQ6yQ6zQ6{Q6|Q6}Q6RQ6KQ6T409Q1}'6R~P?Q6nP~Q1wQ6hQ6tCwQ70Q72Q75Q78Q7<Q7?Q7BQ7EQ7HQ7JQ7LQ7NQ7QQ7RQ7SQ6jPWQ6kQ6iPWQ6NQ1zPWQ6OQ6hP?Q6MQ20P?Q6MQ22P?Q6MQ24P?Q6MQ26P?PxQ28P?PxQ2:P?PxQ2<P?PyQ2>P?PxQ2@P?PxQ2BP?PxQ2DP?PyQ2FP?PyQ2HP?PyQ2JP?PyQ2LP?PyQ2NP?PxQ2PP?PxQ2RP?PxQ2TP?PyQ2VP?PyQ2XP?PyQ2ZP?PyQ2\P?PyQ2^P?PxQ2`P?PxQ2bP?PxQ2dP?PyQ2fP?PyQ2hP?PyQ2jP?PyQ2lP?PyQ2nP?PxQ2pP?PxQ2rP?PxQ2tP?PyQ2vP?PyQ2xP?PyQ2zP?PyQ2|P?PyQ2~P?PxQ31P?PxQ33P?PxQ35P?PyQ37P?PyQ39P?PyQ3;P?PyQ3=P?PyQ3?P?PxQ3AP?PxQ3CP?PxQ3EP?PxQ3GP?PyQ3IP?PyQ3KP?PyQ3MP?PyQ3OP?PxQ3QP?PxQ3SP?PxQ3UP?PxQ3WP?PxQ3YP?PxQ3[P?PxQ3]P?PxQ3_P?PxQ3aP?PxQ3cP?PxQ3eP?PxQ3gP?PxQ3iP?PxQ3kP?PxQ3mP?PxQ3oP?PxQ3qP?PxQ3sP?PxQ3uP?PxQ3wP?PxQ3yP?PxQ3{P?PxQ3}P?PxQ40P?PxQ42P?PxQ44P?PxQ46P?PxQ48P?PxQ4:P?PxQ4<P?PxQ4>P?PxQ4@P?PxQ4BP?PxQ4DP?PxQ4FP?PxQ4HP?PxQ4JP?PxQ4LP?PxQ4NP?PxQ4PP?PxQ4RP?PxQ4TP?PyQ4VP?PyQ4XP?PxQ4ZP?PxQ4\P?PxQ4^P?PxQ4`P?PyQ4bP?PyQ4dP?PyQ4fP?PyQ4hP?PyQ4jP?PyQ4lP?PxQ4nP?PxQ4pP?PxQ4rP?PxQ4tP?PxQ4vP?PxQ4xP?PxQ4zP?PxQ4|P?PxQ4~P?PxQ51P?PxQ53P?PxQ55P?PxQ57P?PxQ59P?PxQ5;P?PxQ5=P?PxQ5?P?PxQ5BP?PxQ5DP?PxQ5FP?PxQ5HP?PxQ5JP?PxQ5LP?PxQ5NP?PxQ5PP?PxQ5RP?PxQ5TP?PxQ5VP?PxQ5XP?PxQ5ZP?PxQ5\P?PxQ5^P?PxQ5`P?PxQ5bP?PxQ5dP?PxQ5fP?PxQ5hP?PxQ5jP?PxQ5lP?PxQ5nP?PxQ6gP?PxQ6fP?PxQ6eP?PxQ6dP?PxQ6cP?PxQ6bP?PxQ6aP?PxQ6`P?PxQ6_P?PxQ64H15F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=DWDWDWDWH15DWDWDWDWQ6=I0DRxQ7UQ1w-1}~S64Q7V3AS6_Q6<PUQ7WPUQ7XPUQ6SPUQ7YPUQ7ZPUQ7[PUQ7\PUQ7]Q6n54|Q7^D1D1D1D1R?Q1VP5PsQ7`Q7_+0t#SdQ0sQ0cQ0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0bPLPMPNQ0WQ0XQ0tPOPPPQQ0YQ0ZQ0[Q0\Q0]Q7aQ7bQ5{Q7cQ7dQ7eQ7fQ7gQ5|Q7hQ7iQ7jQ0uQ0vQ0wQ0xQ0yQ7kQ0zQ0{Q7lQ7mQ7nQ7oQ7pQ7qQ7rQ7sQ7tQ7uQ7vPjQ8;Q1{Q1xPYPYQ7FPbQ1TPSP^P8Q1<PsQ16>0:>Y#SdPsQ7xQ15Q7F40:#Sdp#1@0sPbQ1TQ7~Q7yP3PBfORyQ7}+0CS7yQ1U60r:RWQ63Q5}Q639GBWQ5}9GBWQ0sQ0cQ0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0bPLPMPNQ0WQ0XQ0tPOPPPQQ0YQ0ZQ0[Q0\Q0]Q7aQ7bQ5{Q7cQ7dQ7eQ7fQ7gQ5|Q7hQ7iQ7jQ0uQ0vQ0wQ0xQ0yQ7kQ0zQ0{Q7lQ7mQ7nQ7oQ7pQ7qQ7rQ7sQ7tQ7uQ7vPyQ62Q1UQ1SPbNv0qQ0sQ0cQ0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0bPLPMPNQ0WQ0XQ0tPOPPPQQ0YQ0ZQ0[Q0\Q0]Q5{Q5|Q0uQ0vQ0wQ0xQ0yQ0zQ0{p,3THAQ1gp,3TH8p,3THSp,3THFp,3THPp,3THDp,4THC1p,4THC2PyQ62Q1UQ6JQ1SPbg02UlRW#US5|%fWS5{&1|0S7v&1{0S7u&1z0RW2130>S7tQ6J#tRw+0@,~WP0Pwg02VXS7sQ1l#tH0`,~W412Q08-1xWS7rP3P6Ps21w36#SdB1v0>2H1uS7qb?b@bAQ6J#lQ6JQ1l+01'BP3b>S1lNk1tH0pO5b0P:Q1UQ7}+0CRwPjQ8?H0oeQ85Q83Q84Q81Q82PxQ6_CRQ6<CRS82'cQ85P:Q66Q05Q69Q6<Q68Q1OQ7_+0nQ6lQ8?Q5z$0m5nBQ6=I0DQ7VK0lQ8230dQ7UB0k:jwS82Q64Q7VP0P\Q7y@0^~3Z0I0Q0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VPLPMPNQ0WQ0XPOPPPQQ0YQ0ZQ0[Q0\Q0]Q1gQ1UQ62Q6JQ1lNS1s1PI\-0_IQ0|Q0}+1rQ0|-01>S1lQ0}#lQ0~-01>[S62[Q0|#lS1gg02W?RBQ0|Q0}<1q2UWHQ1gQ0~#l\B]HP2Q0|-1o>,czQ1leO1Q62Q5|Q5{Q7vQ7uQ7t%t\Rz+0@,~WP0PzQ7sQ0|#t>1n0IH0`,~W612WQ7rQ7qb?b@bA%l\Q0~-01\'BP3b>bLc0DbL-1m\J0\Q1w-0Lw-0_I:0^w~eQ1w-1kw:0^w~eP:PjPwQ64H1jeQ7UQ82+0NJ1iP:PjPwQ6_H1hePsQ04Q5z$0j$0i&0hxRw40g#SdPsQ7`&0fx<1=?#SdQ0DQ0EQ0FAoR6?Q7`Q5z61<wRw:0BR6Q65Q6:Q5z$1;S5zQ1[;g=Q1Z>1::<Q8:Q89Q88Q00Q14Q6Q54VR~Q7O5A@3VQ89Q7MQ89Q88Q0BP@Q1~P@Q21P@Q23P@Q25P@Q27P@Q29P@Q2;P@Q2=P@Q2?P@Q2AP@Q2CP@Q2EP@Q2GP@Q2IP@Q2KP@Q2MP@Q2OP@Q2QP@Q2SP@Q2UP@Q2WP@Q2YP@Q2[P@Q2]P@Q2_P@Q2aP@Q2cP@Q2eP@Q2gP@Q2iP@Q2kP@Q2mP@Q2oP@Q2qP@Q2sP@Q2uP@Q2wP@Q2yP@Q2{P@Q2}P@Q30P@Q32P@Q34P@Q36P@Q38P@Q3:P@Q3<P@Q3>P@Q3@P@Q3BP@Q3DP@Q3FP@Q3HP@Q3JP@Q3LP@Q3NP@Q3PP@Q3RP@Q3TP@Q3VP@Q3XP@Q3ZP@Q3\P@Q3^P@Q3`P@Q3bP@Q3dP@Q3fP@Q3hP@Q3jP@Q3lP@Q3nP@Q3pP@Q3rP@Q3tP@Q3vP@Q3xP@Q3zP@Q3|P@Q3~P@Q41P@Q43P@Q45P@Q47P@Q49P@Q4;P@Q4=P@Q4?P@Q4AP@Q4CP@Q4EP@Q4GP@Q4IP@Q4KP@Q4MP@Q4OP@Q4QP@Q4SP@Q4UP@Q4WP@Q4YP@Q4[P@Q4]P@Q4_P@Q4aP@Q4cP@Q4eP@Q4gP@Q4iP@Q4kP@Q4mP@Q4oP@Q4qP@Q4sP@Q4uP@Q4wP@Q4yP@Q4{P@Q4}P@Q50P@Q52P@Q54P@Q56P@Q58P@Q5:P@Q5<P@Q5>P@Q5@P@Q5CP@Q5EP@Q5GP@Q5IP@Q5KP@Q5MP@Q5OP@Q5QP@Q5SP@Q5UP@Q5WP@Q5YP@Q5[P@Q5]P@Q5_P@Q5aP@Q5cP@Q5eP@Q5gP@Q5iP@Q5kP@Q5mP@Q5oP@Q5pP@Q5qP@Q5rP@Q5sP@Q5tP@Q5uP@Q5vP@Q5wP@Q5xP@Q0^=4V[S0^P@Q6I=4V[S6IP@Q8B=4V[S8BP@Q8@=4V[S8@P@Q01=4V[R\P@Q8<=4V[RzP@Q76=4V[RBP@Q79=4V[R[Q6PD1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D13VQ1k3AD1'cQ1hQ00Q6[-0c~5V4R~Q1yQ0BQ1~Q21Q23Q25Q27Q29Q2;Q2=Q2?Q2AQ2CQ2EQ2GQ2IQ2KQ2MQ2OQ2QQ2SQ2UQ2WQ2YQ2[Q2]Q2_Q2aQ2cQ2eQ2gQ2iQ2kQ2mQ2oQ2qQ2sQ2uQ2wQ2yQ2{Q2}Q30Q32Q34Q36Q38Q3:Q3<Q3>Q3@Q3BQ3DQ3FQ3HQ3JQ3LQ3NQ3PQ3RQ3TQ3VQ3XQ3ZQ3\Q3^Q3`Q3bQ3dQ3fQ3hQ3jQ3lQ3nQ3pQ3rQ3tQ3vQ3xQ3zQ3|Q3~Q41Q43Q45Q47Q49Q4;Q4=Q4?Q4AQ4CQ4EQ4GQ4IQ4KQ4MQ4OQ4QQ4SQ4UQ4WQ4YQ4[Q4]Q4_Q4aQ4cQ4eQ4gQ4iQ4kQ4mQ4oQ4qQ4sQ4uQ4wQ4yQ4{Q4}Q50Q52Q54Q56Q58Q5:Q5<Q5>Q5@Q5CQ5EQ5GQ5IQ5KQ5MQ5OQ5QQ5SQ5UQ5WQ5YQ5[Q5]Q5_Q5aQ5cQ5eQ5gQ5iQ5kQ5mQ5oQ5pQ5qQ5rQ5sQ5tQ5uQ5vQ5wQ5xQ0^Q6IQ8BQ8@P\PzPBP[Q0aD:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:D:5V4R[Q7P5AqRB5AqRz5AqR\70wRVdPVQ1hPwQ80P=P\P3EKB0BRC\Q7|Q0?P3PqQ7{P~PzP2O5PR2074~R\P_2084~R~CCQ7{=Gqz'BP1PRP\P`P~CCQ7I=Gqzp+01`PfPc&18x,PIRxPdPePaPgGDP3PRP\PfP~CCQ6X=GqzQ7|Q0?P3PqQ7DQ1yPBP2O5Q7>Q7D=GqB'BP1Q7;Q77=GqBp+01fP]PcPxPdPeQ1PPgGDP3Q7AQ74=GqBQ7|Q0?P3PqQ6YP[Q7PP2O5PR2074[RqQ0o2084[R[CCQ0A'BP1PRPqP9P[CCQ1?p+01lPbPcPxPdPeQ1TPgGDP3PRPqPbP[CCQ7zQ0sQ0cQ1CPKQ0bPLPMQ0WQ0XQ0tPOPPQ0eQ0uQ0vQ0wQ0xQ0yQ0zQ0{Q8;Q1{Q1xPYPYQ7FQ1rP5Q1UPiQ1RNO17Q0fQ0dQ5zQ0dQ7w=g3jW:Q0oQ0nPKPOQ8;Q1{Q1xPYPYQ7FL16EKQ0nQ1qQ1V3gQ0np+01oRYQ7wPjPyP3J1fQ0n?gYjPRPyP?Q1VH1e&1d?R[9oRy%fURqPUQ7WPUQ7XPUQ6SPUQ7YPUQ7ZPUQ7[Q6BD1D1D1R4'cA0q[4RBdPBPqP[Q1W=oR3X:qP2P4P3EKAoRk4PKQ0bPLPMQ0WQ0XPOPPPQQ0Yp,3LBlRPQ0jQ0up,3UM1p,3UG1p,3UG2p,3UG3p,3UFOPkPjND1cQ0C#JROPXQ0:$1bRMPPPkQ6J,sLRKPQQ0YQ0jN90ZQ7:#JR49OkKQ0Y$0d$1`RqQ1WQ0`Q0Y+1_R[7OQ[Q0hQ0gP6AVX23Q0jDjRBQ1Z?O8O[^4X^80^10'B40XP1POPXPMPPQ1WPKPQQ0YQ0jN90ZQ1W?OK4fSRz?OQ[\qQ1Y?O8O\B^4X^80^1040Xp+027Q1[PcQ8G,PIR~PdPePzPgGDP3POPXPMPPQ1[PKPQQ0YQ0jN90ZQ1Z?OK4Q1Y?OQ[\qQ1]?O8O\B^4X^80^1040XP1Q1Y?OK4fWS1Y?OQ[\qQ1\?O8O\B^4X^80^10'Bp+02;Q1^PcP~PdPeQ1YPgGDP3Q1^?OK4Q1\?OQ[\qQ1`?O8O\B^4X^80^10'BP1f[R4?OQ[\qQ1_?O8O\B^4X^80^10p+02?Q1aPcP~PdPeP4PgGDP3Q1`?OQ[\qQ1b?O8O\B^4X^80^10PRf_S1\P?PZQ6HQ1aQ1iPsB0>|A3RBQ1i:0>|A60PEB0<|A3RqQ1i:0<|A+0W+0OXFU>0VU?#Sd80S?K0RPJQ1\PZP|e&1^RR[Q6H+0LCyPRQ1cP?PpQ1jQ1`Q6VPsQ6V:0>|A:0PEBQ6V:0<|A-0Wq+0OXFU>0VU?#Sd80S?K0RPJQ1cPpP|eQ1j-0L[CyPRQ1bP?P{Q6UQ1_Q6WPsQ6W:0>|A:0PEBQ6W:0<|A-0Wq+0OXFU>0VU?#Sd80S?K0RPJQ1bP{P|eQ6U-0L[Cyp,4TIDRQ0|00uO:1]>NPJ&1\N,PIR>&1[NR[90J3XNJPJ&1ZN,PIR?A0J>3XNJ1cJ?P[21YN3J0\fcR?00IpR>P6J0\A0J>[Q09Q0;Q0<POPXPM21XcdRMPPQ1fP?PLPQQ0YPNQ0jQ0pQ5|Q5{Q7vQ7uQ1A#t%tO+0@,~WQ7rQ7qb?b@bAQ1A/QOP3b>P2Q5|Q5{21W02Q7uPWQ06Q07Q07Q08Q6s#t21V0DRD+0@,~WQ07$0wQ7t00@D,~WL1UQ7rQ7qb?b@bAXM0Q6s/Q3%l2[^M0P3PLp+01KO2b>%lLeP_P<P=P7P3P6NI1SQ0DQ0DQ1e00?3PMfgRLg02W[,PIRWQ1dQ0:$1TRDPMP6Q0qQ1dPDDIPJP6Q0k1PI2ROQ0hQ0gP2AVXN3S0:Q0jDjRQD`R?FiX4X,aXX10#xPMQ1ePWQ1fPDPMP3Q0rQ1fPDDIEp'3'BW='aQ03Q0DQ0DQ1d00?3PMfhRPPWPLPDDIR>PMP6Q0qPLPDP?K0zX4X,aXX10#xPMQ1dPWQ1ePDPMP3Q0rQ1ePDDIEp'3'BW=p+02IQ1dPcP~PdPeQ1ePgGDP3Q0D20?P3PMQ1rPWQ1sPDPMP6Q0qQ1sPDDIP?FiX4X,aXX10#xP>PMP3Q0rPLPDJ0U'3'BP1Q1s00?2PMQ1qPWQ1rPDPMP8Q0qQ1rPDDIPJP8Q0kPOPQD`FiX4X,aXX10#xPMQ1sPWPPPDPMP2Q0rPPPDDIEp'3p+02MQ1rPcP~PdPeQ1sPgGDP3Q1q00?8PMQ1uPWQ1vPDPMP<Q0qQ1vPDDIPJP<Q0kPOPQD`FiX4X,aXX10#xPMQ7wPWQ1qPDPMP7Q0rQ1qPDDIEp'3g02X\RP:04|3S1qP8P2P|PoP2P|PmP2P|PnP2P|PFP2P|PrP2P|PTP2P|PvP2P|PGP2P|PpP2P|PZP2P|PHP2P|P{P2P|PuP2P|PlP2P|P}P2P|PtP2ENF2F2F2F2F2F2F2Q02A0|o6P|PmP6P|PnP6P|PFP6P|PrP6P|PTP6P|PvP6P|PGP6P|PpP6P|PZP6P|PHP6P|P{P6P|PuP6P|PlP6P|P}P6AH|t6F2F2F2F2F2F2F2A0|o8R>A0|m8S7wA0|n8S1vA0|F8S1rP|Q6A,LER?P8P|Q1@,LER[P8A0|r8S1@A0|T8S6AA0|v8S1dA0|G8S1fA0|p8S6sA0|Z8S7qA0|H8S7rA0|{8S7tA0|u8RUA0|l8RqA0|}8RAA0|t8RBP|Q6\,LER4P8P|Q6],LERKP8P|Q6^,LER\P8P|Q1B,LEREP8ENF2D@D@D@F2D@P3P|PoP|PoP3P|PmP3P|PnP3P|PFP3P|P?P3P|P[P3P|PrP3P|PTP3P|PvP3P|PGP3P|PpP3P|PZP3P|PHP3P|P{P3P|PuP3P|PlP3P|P}P3P|PtP3P|P4P3P|PKP3P|P\P3P|PEP3ENF2F2F2F2F2F2F2F2F2F2XE|RwA0|ooRVP|PmPoP|PnPoP|PFPoP|P?PoP|P[PoP|PrPoP|PTPoP|PvPoP|PGPoP|PpPoP|PZPoP|PHPoP|P{PoP|PuPoP|PlPoP|P}PoP|PtPoP|P4PoP|PKPoP|P\PoAH|EoF2F2F2F2F2F2F2F2F2F2R@P|PoCk13V@eP7P3EKX5>P3O1Q7wQ1vQ1rQ1@Q6AQ1dQ1fQ6sQ7qQ7rQ7tPU%qB9zqAD@D@D@Q02A0|m7P|PnP7P|PFP7P|PrP7P|PTP7P|PvP7P|PGP7P|PpP7P|PZP7P|PHP7P|P{P7P|PuP7P|PlP7P|P}P7P|PtP7ENF2F2F2F2F2F2P|PoP=A0|m=RAA0|n=S7tA0|F=S7rP|P?P=P|P[P=A0|r=S7qA0|T=S6sA0|v=S1fA0|G=S1dA0|p=S6AA0|Z=S1@A0|H=S1rA0|{=S1vA0|u=S7wA0|l=S1BA0|}=RqA0|t=RBP|P4P=P|PKP=P|P\P=AH|E=F2E|D@D@E_I0GE_P3P|PmPwA0|omRUA0|mmR>P|PnPmP|PFPmP|P?PmP|P[PmP|PrPmP|PTPmP|PvPmP|PGPmP|PpPmP|PZPmP|PHPmP|P{PmP|PuPmP|PlPmP|P}PmP|PtPmP|P4PmP|PKPmP|P\PmP|PEPmENF2F2F2F2F2F2F2F2F2R@'3RVP>P@P|PmEr13UVeP<P3EKX5AP3O1Q7tQ7rQ7qQ6sQ1fQ1dQ6AQ1@Q1rQ1vQ7wQ1B1uqBD@D@D@Q02A0|n<P|PFP<P|PrP<P|PTP<P|PvP<P|PGP<P|PpP<P|PZP<P|PHP<P|P{P<P|PuP<P|PlP<P|P}P<AH|t<F2F2F2F2F2F2P|PoP;P|PmP;A0|n;RBA0|F;S1BP|P?P;P|P[P;A0|r;S7wA0|T;S1vA0|v;S1rA0|G;S1@A0|p;S6AA0|Z;S1dA0|H;S1fA0|{;S6sA0|u;S7qA0|l;S7rA0|};S7tA0|t;RqP|P4P;P|PKP;P|P\P;AH|E;F2E|D@D@E_E|F2P3P|PnPwA0|onRAA0|mnS6^A0|nnRVP|PFPnP|P?PnP|P[PnP|PrPnP|PTPnP|PvPnP|PGPnP|PpPnP|PZPnP|PHPnP|P{PnP|PuPnP|PlPnP|P}PnP|PtPnP|P4PnP|PKPnP|P\PnAH|EnF2F2F2F2F2F2F2F2F2RU'3R@'3R>Q6^P@PVPUP|PnCkD>13A>ePCP3EKX5BP3O1Q1BQ7wQ1vQ1rQ1@Q6AQ1dQ1fQ6sQ7qQ7rQ7t%qqD@D@D@Q02A0|FCP|PrPCP|PTPCP|PvPCP|PGPCP|PpPCP|PZPCP|PHPCP|P{PCP|PuPCP|PlPCP|P}PCP|PtPCENF2F2F2F2F2P|PoP^P|PmP^P|PnP^A0|F^RqA0|?^P|P[P^A0|r^S7tA0|T^S7rA0|v^S7qA0|G^S6sA0|p^S1fA0|Z^S1dA0|H^S6AA0|{^S1@A0|u^RBA0|l^R>A0|}^RAA0|t^RUP|P4P^P|PKP^P|P\P^AH|E^F2E|D@D@E_E_F2P3P|PFPwA0|oFRVA0|mFS1rA0|nFS1vA0|FFS7wP|P?PFP|P[PFP|PrPFP|PTPFP|PvPFP|PGPFP|PpPFP|PZPFP|PHPFP|P{PFP|PuPFP|PlPFP|P}PFP|PtPFP|P4PFP|PKPFP|P\PFP|PEPFENF2F2F2F2F2F2F2F2S1B'3S6^'3S6]'3R@Q1rQ6]Q1vQ6^Q7wQ1BP|PFErD>13V@eP_P3EKX5qP3O1Q7tQ7rQ7qQ6sQ1fQ1dQ6AQ1@1uAU9zB>D@D@Q02A0|r_P|PTP_P|PvP_P|PGP_P|PpP_P|PZP_P|PHP_P|P{P_P|PuP_P|PlP_P|P}P_AH|t_F2F2F2F2F2P|PoP`P|PmP`P|PnP`P|PFP`P|P?P`P|P[P`A0|r`R>A0|T`S1@A0|v`S6AA0|G`S1dA0|p`S1fA0|Z`S6sA0|H`S7qA0|{`S7rA0|u`S7tA0|l`RBA0|}`RUA0|t`RAP|P4P`P|PKP`P|P\P`P|PEP`ENF2D@D@D@F2F2F2P3P|PrPwA0|orRqA0|mrS1BA0|nrS7wA0|FrS6^A0|?rS1vA0|[rS6]A0|rrS1rP|PTPrP|PvPrP|PGPrP|PpPrP|PZPrP|PHPrP|P{PrP|PuPrP|PlPrP|P}PrP|PtPrP|P4PrP|PKPrP|P\PrAH|ErF2F2F2F2F2F2F2S6\'3S07'3S08'3S06'3S7u'3R@'3RVQ1BP@Q7wQ7uQ6^Q06Q1vQ08Q6]Q07Q1rQ6\P|PrCkD>D>D>13qVePaP3EKX5>P3O1Q1@Q6AQ1dQ1fQ6sQ7qQ7rQ7t%qA9zBUD@D@Q02A0|TaP|PvPaP|PGPaP|PpPaP|PZPaP|PHPaP|P{PaP|PuPaP|PlPaP|P}PaP|PtPaENF2F2F2F2P|PoPfP|PmPfP|PnPfP|PFPfP|P?PfP|P[PfP|PrPfA0|TfRUA0|vfS7tA0|GfS7rA0|pfS7qA0|ZfS6sA0|HfS1fA0|{fS1dA0|ufS6AA0|lfS1@A0|}fRBA0|tfRAP|P4PfP|PKPfP|P\PfAH|EfF2I0GD@D@E_F2F2F2P3P|PTPwA0|oTR>A0|mTS6\A0|nTS1rA0|FTS07A0|?TS6]A0|[TS08A0|rTS1vA0|TTS06P|PvPTP|PGPTP|PpPTP|PZPTP|PHPTP|P{PTP|PuPTP|PlPTP|P}PTP|PtPTP|P4PTP|PKPTP|P\PTP|PEPTENF2F2F2F2F2F2S6^'3S7u'3S7w'3S1B'3S5{'3RV'3Rq'3R@Q6\PqQ1rPVQ07Q5{Q6]Q1BQ08Q7wQ1vQ7uQ06Q6^P|PTErD>D>D>13>@eQ0pP3EKX5UP3O1Q7tQ7rQ7qQ6sQ1fQ1dQ6AQ1@1uBAD@D@Q02Q0p90|vP|PGQ0pP|PpQ0pP|PZQ0pP|PHQ0pP|P{Q0pP|PuQ0pP|PlQ0pP|P}Q0pQ0p9H|tF2F2F2F2P|PoPSP|PmPSP|PnPSP|PFPSP|P?PSP|P[PSP|PrPSP|PTPSA0|vSRAA0|GSS1@A0|pSS6AA0|ZSS1dA0|HSS1fA0|{SS6sA0|uSS7qA0|lSS7rA0|}SS7tA0|tSRBP|P4PSP|PKPSP|P\PSAH|ESF2E|D@D@F2F2F2F2P3P|PvPwA0|ovRSA0|mvS6^A0|nvS06A0|FvS7uA0|?vS1vA0|[vS7wA0|rvS08A0|TvS1BA0|vvS6]P|PGPvP|PpPvP|PZPvP|PHPvP|P{PvP|PuPvP|PlPvP|P}PvP|PtPvP|P4PvP|PKPvP|P\PvAH|EvF2F2F2F2F2F2S5{'3S07'3S1r'3S6\'3RU'3R@'3R>'3RV'3RqQ6^PVQ06P>Q7uP@Q1vPUQ7wQ6\Q08Q1rQ1BQ07Q6]Q5{P|PvCkD>D>D>D>13SqeQ1QP3EKX5AP3O1Q1@Q6AQ1dQ1fQ6sQ7qQ7rQ7t%qBD@D@Q02Q1Q90|GP|PpQ1QP|PZQ1QP|PHQ1QP|P{Q1QP|PuQ1QP|PlQ1QP|P}Q1QP|PtQ1QENF2F2F2P|PoPhP|PmPhP|PnPhP|PFPhP|P?PhP|P[PhP|PrPhP|PTPhP|PvPhA0|GhRBA0|phS7tA0|ZhS7rA0|HhS7qA0|{hS6sA0|uhRAA0|lhRqA0|}hRSA0|thRUA0|4hP|PKPhP|P\PhAH|EhF2D@D@E_F2F2F2F2P3P|PGPwA0|oGR@A0|mGS1fA0|nGS1dA0|FGS6AA0|?GS1@A0|[GS5{A0|rGS6]A0|TGS07A0|vGS1BA0|GGS1rP|PpPGP|PZPGP|PHPGP|P{PGP|PuPGP|PlPGP|P}PGP|PtPGP|P4PGP|PKPGP|P\PGP|PEPGENF2F2F2F2F2S08'3S6\'3S7w'3S1v'3S7u'3S06'3S6^'3S5|'3R>'3RVQ1fP>Q1dQ5|Q6AQ6^Q1@Q06Q5{Q7uQ6]Q1vQ07Q7wQ1BQ6\Q1rQ08P|PGErD>D>D>D>13@VeQ1PP3EKX5BP3O1Q7tQ7rQ7qQ6s1uSU9zAqD@Q02Q1P90|pP|PZQ1PP|PHQ1PP|P{Q1PP|PuQ1PP|PlQ1PP|P}Q1PQ1P9H|tF2F2F2P|PoP]P|PmP]P|PnP]P|PFP]P|P?P]P|P[P]P|PrP]P|PTP]P|PvP]P|PGP]A0|p]RqA0|Z]S1PA0|H]S6sA0|{]S7qA0|u]S7rA0|l]RAA0|}]RUA0|t]RSP|P4P]P|PKP]P|P\P]P|PEP]ENF2D@D@F2F2F2F2F2P3P|PpPwA0|opRBA0|mpS7tA0|npS08A0|FpS1rA0|?pS6\A0|[pS1BA0|rpS7wA0|TpS07A0|vpS1vA0|GpS6]A0|ppS7uP|PZPpP|PHPpP|P{PpP|PuPpP|PlPpP|P}PpP|PtPpP|P4PpP|PKPpP|P\PpAH|EpF2F2F2F2F2S5{'3S06'3S1@'3S6^'3S6A'3S5|'3S1d'3S1f'3RV'3R@'3R>Q7tP@Q08PVQ1rQ1fQ6\Q1dQ1BQ5|Q7wQ6AQ07Q6^Q1vQ1@Q6]Q06Q7uQ5{P|PpCkD>D>D>D>D>13B>eQ1RP3EKX5qP3O1Q1PQ6sQ7qQ7r%qS9zAUD@Q02Q1R90|ZP|PHQ1RP|P{Q1RP|PuQ1RP|PlQ1RP|P}Q1RP|PtQ1RENF2F2P|PoPiP|PmPiP|PnPiP|PFPiP|P?PiP|P[PiP|PrPiP|PTPiP|PvPiP|PGPiP|PpPiA0|ZiRUA0|HiS7rA0|{iS7qA0|uiS6sA0|liS1PA0|}iRAA0|tiRSP|P4PiP|PKPiP|P\PiAH|EiF2I0GD@E_F2F2F2F2F2P3P|PZPwA0|oZRqA0|mZS5{A0|nZS7uA0|FZS06A0|?ZS6]A0|[ZS1@A0|rZS1vA0|TZS6^A0|vZS07A0|GZS6AA0|pZS7wA0|ZZS5|P|PHPZP|P{PZP|PuPZP|PlPZP|P}PZP|PtPZP|P4PZP|PKPZP|P\PZP|PEPZENF2F2F2F2S1B'3S1d'3S6\'3S1f'3S1r'3S08'3S7t'3S1A'3R>'3RB'3RV'3R@Q5{PVQ7uPBQ06P>Q6]Q1AQ1@Q7tQ1vQ08Q6^Q1rQ07Q1fQ6AQ6\Q7wQ1dQ5|Q1BP|PZErD>D>D>D>D>13q@eQ0oP3EKX5UP3O1Q7rQ7qQ6sQ1P1uASD@Q02Q0o90|HP|P{Q0oP|PuQ0oP|PlQ0oP|P}Q0oQ0o9H|tF2F2P|PoP9P|PmP9P|PnP9P|PFP9P|P?P9P|P[P9P|PrP9P|PTP9P|PvP9P|PGP9P|PpP9P|PZP9A0|H9RSA0|{9S0oA0|u9S1PA0|l9S6sA0|}9S7qA0|t9RAP|P4P9P|PKP9P|P\P9AH|E9F2E|D@F2F2F2F2F2F2P3P|PHPwA0|oHRUA0|mHS7rA0|nHS1BA0|FHS5|A0|?HS1dA0|[HS7wA0|rHS6\A0|THS6AA0|vHS1fA0|GHS07A0|pHS1rA0|ZHS6^A0|HHS08P|P{PHP|PuPHP|PlPHP|P}PHP|PtPHP|P4PHP|PKPHP|P\PHAH|EHF2F2F2F2S1v'3S7t'3S1@'3S1A'3S6]'3S06'3S7u'3S5{'3R@'3Rq'3R>'3RB'3RVQ7rPBQ1BP>Q5|PqQ1dP@Q7wQ5{Q6\Q7uQ6AQ06Q1fQ6]Q07Q1AQ1rQ1@Q6^Q7tQ08Q1vP|PHCkD>D>D>D>D>D>13UVeQ1TP3EKX5SP3O1Q0oQ1PQ6sQ7q%qAD@Q02Q1T90|{P|PuQ1TP|PlQ1TP|P}Q1TP|PtQ1TENF2P|PoPbP|PmPbP|PnPbP|PFPbP|P?PbP|P[PbP|PrPbP|PTPbP|PvPbP|PGPbP|PpPbP|PZPbP|PHPbA0|{bRAA0|ubRSA0|lbRVA0|}bRUA0|tbR@A0|4bP|PKPbP|P\PbAH|EbF2D@E_F2F2F2F2F2F2P3P|P{PwA0|o{RqA0|m{S1TA0|n{S7qA0|F{S6sA0|?{S1PA0|[{S0oA0|r{S1vA0|T{S08A0|v{S7tA0|G{S6^A0|p{S1@A0|Z{S1rA0|H{S1AA0|{{S07P|PuP{P|PlP{P|P}P{P|PtP{P|P4P{P|PKP{P|P\P{P|PEP{ENF2F2F2S6]'3S1f'3S06'3S6A'3S7u'3S6\'3S5{'3S7w'3S1d'3S5|'3S1B'3S7r'3R>'3RBQ1TP>Q7qQ7rQ6sQ1BQ1PQ5|Q0oQ1dQ1vQ7wQ08Q5{Q7tQ6\Q6^Q7uQ1@Q6AQ1rQ06Q1AQ1fQ07Q6]P|P{ErD>D>D>D>D>D>13qBeQ1SP3EKX5AP3O11uU@9zSVQ02Q1S90|uP|PlQ1SP|P}Q1SQ1S9H|tF2P|PoP5P|PmP5P|PnP5P|PFP5P|P?P5P|P[P5P|PrP5P|PTP5P|PvP5P|PGP5P|PpP5P|PZP5P|PHP5P|P{P5A0|u5RVA0|l5RSA0|}5R@A0|t5RUP|P4P5P|PKP5P|P\P5P|PEP5ENF2D@F2F2F2F2F2F2F2P3P|PuPwA0|ouRAA0|muS6]A0|nuS07A0|FuS1fA0|?uS1AA0|[uS06A0|ruS1rA0|TuS6AA0|vuS1@A0|GuS7uA0|puS6^A0|ZuS6\A0|HuS7tA0|{uS5{A0|uuS08P|PlPuP|P}PuP|PtPuP|P4PuP|PKPuP|P\PuAH|EuF2F2F2S7w'3S1v'3S1d'3S0o'3S5|'3S1P'3S1B'3S6s'3S7r'3S7q'3S1T'3S7v'3RB'3Rq'3R>Q6]PqQ07PBQ1fQ7vQ1AQ1TQ06Q7qQ1rQ7rQ6AQ6sQ1@Q1BQ7uQ1PQ6^Q5|Q6\Q0oQ7tQ1dQ5{Q1vQ08Q7wP|PuCkD>D>D>D>D>D>D>13A>eQ1VP3EKX5VP3O1%qU9zS@Q02Q1V90|lP|P}Q1VP|PtQ1VENP|PoPjP|PmPjP|PnPjP|PFPjP|P?PjP|P[PjP|PrPjP|PTPjP|PvPjP|PGPjP|PpPjP|PZPjP|PHPjP|P{PjP|PuPjA0|ljR@A0|}jRSA0|tjRUP|P4PjP|PKPjP|P\PjAH|EjF2I0GE_F2F2F2F2F2F2F2P3P|PlPwA0|olRjA0|mlS7wA0|nlS08A0|FlS1vA0|?lS5{A0|[lS1dA0|rlS7tA0|TlS0oA0|vlS6\A0|GlS5|A0|plS6^A0|ZlS1PA0|HlS7uA0|{lS1BA0|ulS1@A0|llS6sP|P}PlP|PtPlP|P4PlP|PKPlP|P\PlP|PEPlENF2F2S6A'3S7r'3S1r'3S7q'3S06'3S1T'3S1A'3S7v'3S1f'3S07'3S6]'3RV'3R>'3RA'3RB'3RqQ7wPBQ08PAQ1vP>Q5{PVQ1dQ6]Q7tQ07Q0oQ1fQ6\Q7vQ5|Q1AQ6^Q1TQ1PQ06Q7uQ7qQ1BQ1rQ1@Q7rQ6sQ6AP|PlErD>D>D>D>D>D>D>13jqeQ1UP3EKX5@P3O11uSUQ02Q1U90|}Q1U9H|tP|PoPyP|PmPyP|PnPyP|PFPyP|P?PyP|P[PyP|PrPyP|PTPyP|PvPyP|PGPyP|PpPyP|PZPyP|PHPyP|P{PyP|PuPyP|PlPyA0|}yRUA0|tyRSP|P4PyP|PKPyP|P\PyAH|EyF2E|F2F2F2F2F2F2F2F2P3P|P}PwA0|o}RyA0|m}S1UA0|n}S6AA0|F}S6sA0|?}S7rA0|[}S1@A0|r}S1rA0|T}S1BA0|v}S7qA0|G}S7uA0|p}S06A0|Z}S1PA0|H}S1TA0|{}S6^A0|u}S1AA0|l}S5|A0|}}S7vP|PtP}P|P4P}P|PKP}P|P\P}AH|E}F2F2S6\'3S1f'3S0o'3S07'3S7t'3S6]'3S1d'3S5{'3S1v'3S08'3R@'3Rq'3Rj'3RV'3R>'3RA'3RBQ1UPAQ6AP>Q6sPVQ7rPjQ1@PqQ1rP@Q1BQ08Q7qQ1vQ7uQ5{Q06Q1dQ1PQ6]Q1TQ7tQ6^Q07Q1AQ0oQ5|Q1fQ7vQ6\P|P}CkD>D>D>D>D>D>D>D>13yBeQ1XP3EKX5UP3O1%qSQ02Q1X90|tQ0=P|PoPkP|PmPkP|PnPkP|PFPkP|P?PkP|P[PkP|PrPkP|PTPkP|PvPkP|PGPkP|PpPkP|PZPkP|PHPkP|P{PkP|PuPkP|PlPkP|P}PkA0|tkRSA0|4kP|PKPkP|P\PkAH|EkF2E_F2F2F2F2F2F2F2F2P3P|PtPwA0|otRwA0|mtS1XA0|ntS6\A0|FtS7vA0|?tS1fA0|[tS5|A0|rtS0oA0|TtS1AA0|vtS07A0|GtS6^A0|ptS7tA0|ZtS1TA0|HtS6]A0|{tS1PA0|utS1dA0|ltS06A0|}tS5{A0|ttS7uP|P4PtP|PKPtP|P\PtP|PEPtENF2S1v'3S7q'3S08'3S1B'3S1r'3S1@'3S7r'3S6s'3Rk'3RU'3RB'3Ry'3R@'3Rq'3Rj'3RV'3R>'3RAQ1XP>Q6\PVQ7vPjQ1fPqQ5|P@Q0oPyQ1APBQ07PUQ6^PkQ7tQ6sQ1TQ7rQ6]Q1@Q1PQ1rQ1dQ1BQ06Q08Q5{Q7qQ7uQ1vP|PtErD>D>D>D>D>D>D>D>13wAeQ1WP3EKX5SP3O1Q0=Q0=P|PoPzP|PmPzP|PnPzP|PFPzP|P?PzP|P[PzP|PrPzP|PTPzP|PvPzP|PGPzP|PpPzP|PZPzP|PHPzP|P{PzP|PuPzP|PlPzP|P}PzP|PtPzP|P4PzP|PKPzP|P\PzP|PEPzENF2F2F2F2F2F2F2F2F2F2P3n010000100W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n201100001021100011000W3P3O1n201100001021100011000W3P3O1n201100001021100011000W3P3O1n201100001021100011000W3P3O1n201100001021100011000W3P3O1n201100001021100011000W3P3O1n201100001021100011000W3P|PoP|PmP|PnP|PFP|PrP|PTP|PvP|PGP|PpP|PZP|PHP|P{P|PuP|PlP|P}P|Pt%U|RzD1D1D1D1D1D1D1D1:04|2P|PoP|PmP|PnP|PFP|P?P|P[P|PrP|PTP|PvP|PGP|PpP|PZP|PHP|P{P|PuP|PlP|P}P|PtP|P4P|PKP|P\P|PEPzD1D1D1D1D1D1D1D1D1D1D1:04|6]3eB04|2Pg02YV:04|6]3eP3O1O2W3XE|Q1qPJP;P2Q1t00I2Cy[^E|PRQ1uP<Q0lPPQ1VPsQ0l-1NP#SdP3L1lQ0mQ02PMQ60PWQ61PDDIRPPMP^Q0qQ61PDPJP^Q0kPOPQD`K0zX4X,aXX10#xPMQ1tPWQ1uPDPMP;Q0rQ1uPDDIEpp+02SQ61PcP~PdPeQ1tPgGDP6PMQ5~PWQ60PDPMP_Q0qQ60PDDIPJP_Q0kPOPQD`FiX4X,aXX10#xQ03P0PMfsR;PWQ5~PDPMP`Q0qQ5~PDDIPJP`Q0kPOPQD`FiX4X,aXX10p+02UQ5~PcP~PdPeQ60PgGDP3PMfuRsPWftR<PDPMPfQ0qP<PDDIPJPfQ0kPOPQD`FiX4X,aXQ03PXPMfvRQPWPsPDPMQ0pQ0qPsPDDIPJQ0pQ0k1PI6Q0hQ0gP6Q0:Q0jDjD`FiX4Xp+02YPQPcP~PdPePsPgGDP3PMQ87PWQ86PDPMQ1QQ0qQ86PDDIPJQ1QQ0k1PI7Q0hQ0gP7Q0:Q0jDjD`FiP1PMfyRQPWQ87PDPMPhQ0qQ87PDDIEpPJPhQ0k1PI=Q0hQ0gP=Q0iQ0jDjD`p+02]fzRhPcP~PdPePQPgGDP3PMf{PWPhPDPMP]Q0qPhPDDIEpPJQ1RQ0k1PICQ0hQ0gPCAVXN7Q0jDjD`P1PJPiQ0k1PI^CyQ0hQ0gP^AVXN=Q0jDjp+02af~R1PcP~PdPef}PgGDP3PJP9Q0k1PI`CyQ0hQ0gPaAVXNCQ0jDjQ0>PMp+01BRNPWQ7GPDDIQ0>PMQ1SQ0qPNPDDIRI-053WBP=PNPcPWPdPeQ7GPDFhR9PcPdPNPWQ7GPDJ0JEKP9PMPbQ0qQ7GPDJ0UQ0>PIQ0>p+01DRIPcPWPdPep+01CRbPDFh0053WBP3Q1SPcQ0qPdPePNPDFhR9PcPdQ1SQ0qPNPDJ0JEKPbPcPWPdPePNPDFh0059P:p+02fPIPcPdP~PbPgP5Q0qPbP3PN&0K5p+02\Q1VPIQ1QPaP3P8P7PiPsQ1tQ1sp+01@P1PLQ1eO?WKN>0yb9b9WrWTP2P3O2n2001000000121000000W0W9P2P3O2n2001000000121000000W0X4XP2P3O2n2001000000121100000W0X10P2P3O2n2001000000121100000W0P3O1PMQ61PWQ1tPDPMPCQ0rQ1tPDDIEpQ0>PPQ0>PMP_Q0rQ60PDDIRP-053WBP3Q60PcPWPdPeQ61PDFhRCPcPdQ60PWQ61PDJ0JEKPCPMP^Q0rQ61PDJ0UQ0>PPQ0>P;PcPWPdPeQ5~PDFh0053WBP3P_PcQ0rPdPeQ60PDFhRPPcPdP_Q0rQ60PDJ0JEKQ5~PcPWPdPeQ60PDFh005PP:p+02VP;PcPdP~Q5~PgP`Q0rQ5~P3Q60&0K`p+02KPaP;P3P=Q1eQ1\Q1]Q1tQ1uQ1YQ1ZO;WKN>0yb9b9W9P3O1n200100000021100011000bnbuW[WRP2P3O2n2001000000121000000W0Y09P2P3O2n2001000000121100000c0EbWc0@bYbVbXWZWUP2P3O2n2001000000121000000W0WSP2P3O2n2001000000121000000W0Y0AP2P3O2n2001000000121000000bDbGbCbGbvbJbjPYQ1VPcPxPdPeP5PgGDeW7WaP2P3O2n2101000010121000000b7b0W7W^P2P3O2n2111000010121000000b7b0W7WqP2P3O2n2111000010121000000b7b0b7bCY0CWJWdWgW7WmY0<Y0HY08NS0xbIbiQ67Q1VPcQ7TPdPeP5PgGDeW6W`P2P3O2n2101000010121000000b6b0W6W]P2P3O2n2111000010121000000b6b0W6WpP2P3O2n2111000010121000000b6b0b6bCY0BWIWcWfW6WlY0;Y0GY07NS0xY0?Y0>P2P3O2n2001000000121000000W0Y0=P2P3O2n2001000000121000000b0WzWyP2P3O2n2001000000121000000W0WxP2P3O2n2001000000121000000W0Y04P2P3O2n2001000000121000000W0Y03P2P3O2n2001000000121000000W0Y02P2P3O2n2001000000121000000W0Y01P2P3O2n2011000000121000000W0W~P2P3O2n2011000000121000000W0W}P2P3O2n2011000000121000000W0W|P2P3O2n2011000000121000000W0W{P2P3O2n2011000000121000000W0WwP2P3O2n2011000000121000000b0WtWsWhWbWeW_W\WoWkY0:Y0FY06Y05o"). Qed.
End SnAb.
