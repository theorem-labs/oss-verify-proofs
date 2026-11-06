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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_SnTA.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbA_SnA () := "C46Stdlib5Lists4List2InC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC69OSSVerify5KrLib3bpA3Lib8LbA_DKit4fentC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C69OSSVerify5KrLib3bpA3Lib:LbA_Bridge5rfullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK2WpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit4rtblC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib3bpA3Lib8LbA_DKit4ftblC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list01C69OSSVerify5KrLib3bpA3Lib7LbA_SnK2PwC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib4HMem7mem_invC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib3bpA2Rt7AsIface6as_RFSC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib3bpA3Lib7LbA_SnK2W3C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame5munchC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C79OSSVerify5KrLib3bpA2HF3Lib:HLPropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK9sn_rangesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C69OSSVerify5KrLib3bpA2Rt8AsShadow5aceilC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib3bpA2Rt7AsIface6as_FSBC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2or00C69OSSVerify5KrLib3bpA3Lib<LbA_DiagStmt7app_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK2tSC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib3bpA3Lib7LbA_SnK2tFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK2tHC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib3bpA3Lib7LbA_SnK8tabs_wf3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK8Pw_step3C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK59OSSVerify5KrLib8SymExec33SX27scripts01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec33SX24expr03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX29sym_state01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit6wboundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit8rtbl_okbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit3finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK8tabs_ok3C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib7LibHash4HLib5EseedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK9kst_pd_okC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib=SymExec3Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib3srsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN4fknTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX28sym_execC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib=SymExec3Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN6swinsTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_FKit:sym_insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25s_logC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC59OSSVerify5KrLib8SymExec33SX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit8rtbl_chkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN4tupdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN5ftblsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN5winsTC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame5wmonoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffC59OSSVerify5KrLib8SymExec33SX24s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK9RFS_step3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK9winsT3_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK2kTC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX28sidecond02C1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib3bpA3Lib7LbA_SnK5kT_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK8scT_flatC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib3bpA2HF3Lib7HMState<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib8SymExec33SX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S5elenZC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib=SymExec3Sound4SX2S9scs_denotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame;munch_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN:rtbl_keptkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN5keptkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK8sn_keepUC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep6nval32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_Kit2gzC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib8SymExec33SX28expr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib3bpA3Lib:LbA_DCtorK7inb_In'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit7rtbl_InC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit4wenvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_SnK2rgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib<LbA_TablStmt5sx32AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib3sxwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6LibPrs:PrsGrammar4sx32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib:LbA_SnFind8sxw_sx32C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib8PropExec7FPState01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib3bpA3Lib:LbA_SnFind;snfind_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_Kit6aonlyTC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib3bpA3Lib8LbA_DKit4rsubC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit9rtbl_keepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HMState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib:LbA_Bridge7mkst_MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_Call8blk_thenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN7dk_runNC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib3bpA2HF3Lib5HExec3evtC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26sentry01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05I59OSSVerify5KrLib7LibHash4HRep5umapx00C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib6CatSim6msteps00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02I47Corelib7Numbers7BinNums1Z00K47Corelib4Init5Logic4True01C69OSSVerify5KrLib3bpA2Rt5ASegs5asegsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib3bpA3Lib9LbA_DKitN3tabC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26sentry00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26kentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C69OSSVerify5KrLib3bpA3Lib8LbA_MILB4AC_AC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_MILB4LY_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_MILB4MI_AC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib3bpA2Rt7AsIface3memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Lib7LbA_SnA3RT2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Lib7LbA_SnA3SF2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Lib7LbA_SnA3FT2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_SnTA4RTK4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_SnTA3SF4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_SnTA3FT4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_SnTA3HT4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib:LbA_SnFind9SNF_FOUNDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib:LbA_SnFind<SNF_NOTFOUNDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib<LbA_DiagStmt9ADS_STACKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AsShadow7AAPP_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7AsIface7AFS_HDRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7AsIface8AFS_SIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7AsIface9AFS_FLAGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt5ASegs8AIMG_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AsShadow9ALOWSH_LOC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AsShadow6AHI_LOC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib3bpA3Lib7LbA_SnK6kst_snC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I59OSSVerify5KrLib8SymExec33SX28sidecond00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_Kit6SHBASEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX27scripts00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25sr_idC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03K47Corelib4Init9Datatypes4bool02I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic4True00C69OSSVerify5KrLib3bpA3Lib:LbA_SnFind9SNF_ENTRYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib8LbA_DKit4KEPTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib7LbA_Kit8non_argTC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 33) (ELit k).

Definition RT2 : list (reg * expr) :=
  [(1%bv, ELit 0xf8d90); (2%bv, spx (-128)); (3%bv, EVar 50); (4%bv, EVar 51); (8%bv, EVar 33); (9%bv, spx (-128));
   (10%bv, EVar 52); (18%bv, EVar 40); (19%bv, EVar 41); (20%bv, EVar 36); (21%bv, EVar 32); (22%bv, EVar 35);
   (23%bv, ELit 2147450880); (24%bv, EVar 46); (25%bv, EVar 47); (26%bv, EVar 48); (27%bv, EVar 49)].
Definition SF2 : list fent :=
  [(-128, 8%nat, ELit 0); (-8, 8%nat, EVar 34); (-16, 8%nat, EVar 38); (-24, 8%nat, EVar 39); (-32, 8%nat, EVar 40);
   (-40, 8%nat, EVar 41); (-48, 8%nat, EVar 42); (-56, 8%nat, EVar 43); (-64, 8%nat, EVar 44); (-72, 8%nat, EVar 45);
   (-80, 8%nat, EVar 46); (-88, 8%nat, EVar 47); (-96, 8%nat, EVar 48); (-104, 8%nat, EVar 49)].
Definition FT2 : list fent := [(2040, 8%nat, EVar 53)].

Section SnA.
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
ltac2:(KReplay.run1 (kr_t_LbA_SnA ()) ["SnA"] "p'0h02H0h11ph21xi001xh32Hrh41vh51Hh64HTS3h74HTS4h81kh93Hmsh:1lh;1Ah<1Ph=2R'h>7__arithh?4__ffh@8__varmaphA5__withB1mhC1EhD1ahE1rhF1yhG4HRK4hH2HahI3MU3hJ3MU4hK3RF5hL6__sat1hM4__x1hN1bhO2l1hP2l2hQ2m'hR2AOhS2G1hT3G10hU2G2hV3G20hW4G20'hX3G21hY3G23hZ2G3h[2HFh\4HFT2h]4HFT3h^4HFT4h_4HHT2h`4HHT3ha4HHT4hb4HMI2hc4HMI3hd4HMI4he3HP2hf3HP3hg3HP4hh4HRF2hi4HRF3hj4HRF4hk4HRT2hl4HRT3hm4HRT4hn4HRT5ho4HSF2hp4HSF3hq4HSF4hr3Hinhs2KFht2KNhu2KPhv4MU24hw3PR1hx4PR10hy4PR11hz4PR12h{3PR2h|3PR3h}3PR4h~3PR5i013PR6i023PR7i033PR8i043PR9i051Qi062R2i072R3i082R4i092R5i0:3RF2i0;3RF3i0<3RF4i0=3TO1i0>3TO2i0?3TO3i0@2TRi0A2U4i0B3WM3i0C3WM4i0D6__sat0i0E1ei0F2m2i0G2m3i0H2m4i0I1zi0J4Ffixi0K8bv_is_wfi0L;bv_unsignedi0M1cp%0p%1p%2p%3p%4p%5p%6p%7p%8p&0p&1p&2p;1p;2p;Np;3p;4p;6p;Bp;gp;5p;?p;vp;7p;Op;8p;kp;Sp;Dp;Ip;>p;=p-1g0000R0p4p710p8g000GR1p4p7210g0013R2p4p710R3p8g001OR4p4p70R5P3p8P5g002Ip4p710R5p8g002fj17Tg003Kj18Tg0040k10HTg004NS00k10vTP1k222Tg0051k10LTg005nmN1aTg006ej3qTg007_k20_Tg008Ij4CTg009Cj1JTg009ak21BTg00:>j1UTg00:^k60dk51RTg00;Uk20bTg00<QS01j2]Tg00=1j4TTg00=Qj3@Tg00>1k30YTg00>kj2PTg00?Qk21MTg00@Hj3kTg00AEk10wTg00Agk11GTg00BimB1DTg00Cgk20uTg00DDk201Tg00D`R1j2BTg00E;k11@Tg00F5j2sTg00FRj2QTg00Fnk11?Tg00Ghk21>Tg00HHS02j23Tg00Hbk21pTg00Ick311Tg00JZj1?Tg00K9k310Tg00L0k30~Tg00Lgj2eTg00MAmg0}Tg00N>m?0|Tg00O;j3nTg00OXk31OTg00PSk10\Tg00QKj1dTg00RCj1NTg00Rak30:Tg00SYj26Tg00TRk21HTg00ULk20DTg00VFk30QTg00W@j4xTg00X:k50CTg00Y7k11CTg00Z3k20tTg00[1k302Tg00[jp<1@0sTg00\gj1cTg00]Gj3GTg00]hk41ATg00^Gk20BTg00_>k30rTg00`?mv0qTg00a=k20NTg00a^k40pTg00b9k40oTg00c8k20nTg00cmk10mTg00dhk70lTg00ebj30Tg00f<k30kk41kTg00g<k10jTg00h9k10iTg00i9k10hTg00j0k30gTg00jLk10fTg00kDk30eTg00lBk31=Tg00m=k30ATg00n9k11<Tg00o5k31;TP2j6KTg0102k421Tg010Vk118Tg011LmO17Tg012Jk816Tg013Hk120Tg014?k21~Tg015;k11}Tg015Yk11|Tg0167k11{Tg016bk214Tg017Ek40`Tg0180k21yTg018Rk21xTg019>k31wTg019]k41vTg01:Omk1uTg01;Ik30^Tg01<EmS1tTg01=Bk21sTg01=jk31rTg01>Nk21qTg01>ok31oTg01?Rk21nTg01@Vk60]Tg01A4k20JTg01Alk21lTg01Bik61jTg01CJk41iTg01DKk61fTg01ENk41eTg01FOk11dTg01GKmD1cTg01HHk11bTg01I@j3OTg01J7k11`Tg01JPk21_Tg01Jmk30=Tg01KJk30PTg01L7k30<Tg01LTk20WTg01MNk20OTg01Mlk30VTg01NHk30STg01OGk70RTg01PDk11^Tg01Q>k31]Tg01R5k11\Tg01S4k11[Tg01Sik11ZTg01Tdk21YTg01Udk20ITg01VVk21XTg01WMk21WTg01Wkk21VTg01XNk81UTg01Y2mI1STg01Z5k20>Tg01[0k11TTg01[ej5ITg01\WS03j2aTP0k305Tg01]1k21NTg01]kk81mTg01^jj7jTg01_dk60KTg01`cm>0zTg01aamS0yTg01b_k312Tg01cBk31LTg01d;k30FTg01e5k30ETg01eok71KTg01fSk71JTg01g7m=1zTg01h0k30@Tg01hdk30xTg01i>k30TTg01iXR0P0f1R2f0R3CTp>06P0f2R6P2P3CTp=Vf4R7P0f3R8P6P2CT<053p=i%J3g01j6R96122p=L20I62=083p=zg01jRR:f7R;f6R<f5R=P7P8P6P2P3Fj41Lp=Dg01kIR>/Q3p=m%73#7p>00A003>p>0c%83#8p=Z%83#8#8#8p>0a%83#8#8#8#8#8#8#8p>07%73#7#7#7p>0M%73#7#7#7#7#7#7#7p=\%73#7#7#Jp=b%83#8#7#7p=w%73#8p=Y%83#7p=[%73#Jp=:%?3#?p>1g%?3#?#?#?p>0[P0g01kgR?P2P3CTp=5A@6239@78p=1%83#Jp=;g01lFR@?@23p>04%?3#?#?#?#?#?#?#?p>1Q%?3#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?p>1P%?3#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?#?p=E%83#7#7#7p=}&0H3$0\p=F%J3#dp=pg01m@RAA@A239@A69@A87@7p=_g01n8S04B0F862;@3p>1IQ04B0F<=7Q04B0F862;@33@p=<1686@0E23p=Sg01o2RB?@23p>1FA@B239@B6p>1EA@B239@B69@B89@B7p=WB12239p>0;P6PAP2P3CTp=4P8PAP6P2CT=@73p=fg01olR9g020LS05703p=RP8PAP0P?P6P2CTP3CTp=XP0P0P3P>CTp>1:A@4239@46p>19A@4239@469@489@47p=9B0=023p>09B0<023p>08Q041678@0F62;@3p=gB0E862=@B3p>15B0E<=7B0E862=@B35@Bp==21403p=uP0P2g020lP3H0`p>0?P2g021SS06g0222S07Q07g022RS08P3g0232K1Kp=vP6Q06Q07Q07Q08P2P3K1Jp>13A@423p>1hg023RS09g024LS0:g025jS0;g026dS0<P3P2P6P8P7P=P<P;f8RCN=1zp>0Z1B23,B6p>0X20I86=072/B3p=`Q0:P<P=P7P8P6DI<0@2/B3p=h1a03p=yQ0:P=P7P8P6P2DI<0@3p=rQ0:P=P7P8P6P2DI80@</B3p>0{Q0:P7P8P6P2P3DI80@=p>0UA0=78A0623g027^S0='3'3p=MA0<=7A0862/33'3p=2A0623Q0='3p=H1323,36,38,37p=A1e23:0x86p=lQ0=,33p=t1323,36p={A0862/33,37,3=p=|A0=781323,36'3p=^A0862/33,37p>0G1e23:0x86:0T=7p=oQ0=,33,32p=~B0T623:0T78p=>Q0:@0@23p>03g028;S0>p-0S0?[g029BRD#7S0@#8S0A$0HREQ0@#7RF#7S0B#7RG#7S0C#7RH$0HRI$0vRJ+22S0Dg029gS0E&0L2S0Fp,2raS0Gp,2spRKp,2gpS0Hp,2tpS0Ip,2s0S0Jp,2s1S0Kp,2s2S0Lp,2s3S0Mp,2s4S0Np,2s5S0Op,2s6S0Pp,2s7S0Qp,2s8S0Rp,2s9S0Sp,3s10S0Tp,3s11S0Up,2awS0Vp,4thisRLp,2poRMp,3tidRNp,5pconsS0Wp,6icountS0Xp,2ffROp,2fpRPp,2blRQp,2bcS0Yp,2ndS0Zp,2nkS0[p,2bwS0\p,3encS0]NN1aRRg02:^RS7q6PR20_IKRTP6g02;VS0^CCPRPOP8g02<NS0_CCPRQ0B#JS0`-1BORUP7%U4S0aCCPKp,2m1S0bPMPOPPP=J0dRV20b:<RWp,1HS0c1]00S0d/]0RXQ0dP0Q0A#J006OPPCTp,2LFS0e3@S0f<0Y;RYQ0DQ0E&0L81]0XS0g,]0S0hQ0gP6AVXN2S0ip,4entsS0jDiPJP=Q0A#7RZ,LES0k1PI8Czg02=FS0l9qR<S0mPRPTP<g02>@R[CCPRPOP;g02?9R\CCPRPUPCg02@2R]CCPKQ0bPMPOPPf9R^J0df:R_-0b:Q0cQ0ff;R`40Y21MKOS0nfFS0of<Ra3kfIRbf>S0pp,1FRcg02@k,PIS0qp,2fcRd&0wJRef=Rf&1G:RgGD[[[[[[[[[[[^4X^10]Q]=Q0DQ0EQ0FQ0l9qR6PRPTP6P[CCPRPOP8P\CCPRPUP7P]CCQ0nfCR];kCQ0oP_Pcg02Al,PIS0rPdPeP^PgGD[\Y\W\V[[[[[]Q]=p,5HCEILS0sQ0cPKQ0bPLPMQ0WQ0Xp,2loS0tPOPPp,3ICNS0up,3STKS0vp,4CEILS0wp,2LOS0xp,4SPHIS0yp,3FFRS0zp,6FSB_OKS0{NB1D%mTQ0@#JS0|%JHS0}+0uS0~-01T'BS10Q0s$1@RVg02C0's/QTS11g02D3RW,QTS12Q0c$1?RTg02Do'sRY/QOS13%7HRU#7S14#7$00R\#JS15,sOg02Ej,sTR['QS16Q0}-1>O$0cS17g02Ff,sT/QP201PY'BS18g02GcRY/QTS191Q[VS1:%7\S1;#J-1>T$0cS1<g02H]R\,Q[g02I[R[/QT'3S1=%8DS1>#8S1?#8S1@#8S1A#8#ZS1B#8#Z$0aRT#7$07$0M#\#\#b/QV%8TRT$07Rh$0M#\#\#b,QV'BS1C'BS1D'BS1E'BS1F'BS1G'BS1H'BS1I'BS1J'BS1K'BS1L'BS1M'BP1Q10Q1MQ0pPfPc%ZD#w#Y#[#w#[#bS1N,PIRVPdPePaPgGDP3Q10Q1MP1Q11Q1LfBS1OfARiPcPVPdPef@S1PPgGDP3Q11Q1LP1Q12Q1KQ0ofERjPcPVPdPefDS1QPgGDP3Q12Q1KP1Q13Q1JfJS1RPbPcPVPdPefHS1SPgGDP3Q13Q1JP1Q16Q1IfNS1TfMRkPcPVPdPefLS1UPgGDP3Q16Q1IP1Q17Q1HfRS1VfQRlPcPVPdPefPS1WPgGDP3Q17Q1HP1Q18Q1GfVS1XfUS1YPcPVPdPefTS1ZPgGDP3Q18Q1GP1Q19Q1FfZS1[fYS1\PcPVPdPefXS1]PgGDP3Q19Q1FP1Q1:Q1Ef^S1^f]S1_PcPVPdPef\S1`PgGDP3Q1:Q1EP1Q1<Q1DfbfaS1aPcPVPdPef`S1bPgGDP3Q1<Q1DP1Q1=Q1CffS1cfeS1dPcPVPdPefdS1ePgGDP3Q1=Q1Cp,3THOS1f%8FS1g#7S1h#7S1i#7S1j#7#:S1k-1pLP11QYLS1lQ1k,sLRY/Q\1Q[L'3S1m1QYWS1n'BS1ofkS1pfjS1qPcPVPdPefiS1rPgGDP3Q1lQ1oP1Q1mQ1nfoS1sfnS1tPcPVPdPefmS1uPgGDP3Q1mQ1nPRQ0^1]0?RV#URY611KQ0_PVP0P?P>g02JV#?R?#?$1gS1v$0[RWCTS1wPVQ0`/5WS1x%JGS1y/5WS1z=@VYD1S1{610OQ0aPV%7T$00$0MRT#7R[#7R\#7Rm#7Rn#7Ro#7Rp#7Rq#:S1|/5?S1}PV%;qS1~/5?S20PV%8pRp#:S21/5?S22PV%;pS23/5?S24PV%8oRo#7Rp#:S25/5?S26PV%;pS27/5?S28PV%8oRo#:S29/5?S2:PV%;oS2;/5?S2<PV%8nRn#8Ro#7Rp#:S2=/5?S2>PV%;pS2?/5?S2@PV%8oRo#:S2A/5?S2BPV%;oS2C/5?S2DPV%7nRn#7Ro#:S2E/5?S2FPV%;oS2G/5?S2HPV%8nRn#:S2I/5?S2JPV%;nS2K/5?S2LPV%8mRm#7Rn#8Ro#7Rp#:S2M/5?S2NPV%;pS2O/5?S2PPV%8oRo#:S2Q/5?S2RPV%;oS2S/5?S2TPV%7nRn#7Ro#:S2U/5?S2VPV%;oS2W/5?S2XPV%8nRn#:S2Y/5?S2ZPV%;nS2[/5?S2\PV%8mRm#8Rn#7Ro#:S2]/5?S2^PV%;oS2_/5?S2`PV%8nRn#:S2a/5?S2bPV%;nS2c/5?S2dPV%7mRm#7Rn#:S2e/5?S2fPV%;nS2g/5?S2hPV%8mRm#:S2i/5?S2jPV%;mS2k/5?S2lPV%8\R\#7Rm#7Rn#8Ro#7Rp#:S2m/5?S2nPV%;pS2o/5?S2pPV%8oRo#:S2q/5?S2rPV%;oS2s/5?S2tPV%7nRn#7Ro#:S2u/5?S2vPV%;oS2w/5?S2xPV%8nRn#:S2y/5?S2zPV%;nS2{/5?S2|PV%8mRm#8Rn#7Ro#:S2}/5?S2~PV%;oS30/5?S31PV%8nRn#:S32/5?S33PV%;nS34/5?S35PV%7mRm#7Rn#:S36/5?S37PV%;nS38/5?S39PV%8mRm#:S3:/5?S3;PV%;mS3</5?S3=PV%8\R\#7Rm#8Rn#7Ro#:S3>/5?S3?PV%;oS3@/5?S3APV%8nRn#:S3B/5?S3CPV%;nS3D/5?S3EPV%7mRm#7Rn#:S3F/5?S3GPV%;nS3H/5?S3IPV%8mRm#:S3J/5?S3KPV%;mS3L/5?S3MPV%8\R\#8Rm#7Rn#:S3N/5?S3OPV%;nS3P/5?S3QPV%8mRm#:S3R/5?S3SPV%;mS3T/5?S3UPV%7\R\#7Rm#:S3V/5?S3WPV%;mS3X/5?S3YPV%8\R\#:S3Z/5?S3[PV%;\S3\/5?S3]PV%8[R[#7R\#7Rm#7Rn#8Ro#7Rp#:S3^/5?S3_PV%;pS3`/5?S3aPV%8oRo#:S3b/5?S3cPV%;oS3d/5?S3ePV%7nRn#7Ro#:S3f/5?S3gPV%;oS3h/5?S3iPV%8nRn#:S3j/5?S3kPV%;nS3l/5?S3mPV%8mRm#8Rn#7Ro#:S3n/5?S3oPV%;oS3p/5?S3qPV%8nRn#:S3r/5?S3sPV%;nS3t/5?S3uPV%7mRm#7Rn#:S3v/5?S3wPV%;nS3x/5?S3yPV%8mRm#:S3z/5?S3{PV%;mS3|/5?S3}PV%8\R\#7Rm#8Rn#7Ro#:S3~/5?S40PV%;oS41/5?S42PV%8nRn#:S43/5?S44PV%;nS45/5?S46PV%7mRm#7Rn#:S47/5?S48PV%;nS49/5?S4:PV%8mRm#:S4;/5?S4<PV%;mS4=/5?S4>PV%8\R\#8Rm#7Rn#:S4?/5?S4@PV%;nS4A/5?S4BPV%8mRm#:S4C/5?S4DPV%;mS4E/5?S4FPV%7\R\#7Rm#:S4G/5?S4HPV%;mS4I/5?S4JPV%8\R\#:S4K/5?S4LPV%;\S4M/5?S4NPV%8[R[#7R\#7Rm#8Rn#7Ro#:S4O/5?S4PPV%;oS4Q/5?S4RPV%8nRn#:S4S/5?S4TPV%;nS4U/5?S4VPV%7mRm#7Rn#:S4W/5?S4XPV%;nS4Y/5?S4ZPV%8mRm#:S4[/5?S4\PV%;mS4]/5?S4^PV%8\R\#7Rm#7Rn#:S4_/5?S4`PV%;nS4a/5?S4bPV%8mRm#:S4c/5?S4dPV%;mS4e/5?S4fPV%8\R\#7Rm#:S4g/5?S4hPV%;mS4i/5?S4jPV%8\R\#:S4k/5?S4lPV%;\S4m/5?S4nPV%8[R[#7R\#8Rm#7Rn#:S4o/5?S4pPV%;nS4q/5?S4rPV%8mRm#:S4s/5?S4tPV%;mS4u/5?S4vPV%7\R\#7Rm#:S4w/5?S4xPV%;mS4y/5?S4zPV%8\R\#:S4{/5?S4|PV%;\S4}/5?S4~PV%8[R[#8R\#7Rm#:S50/5?S51PV%;mS52/5?S53PV%8\R\#:S54/5?S55PV%;\S56/5?S57PV%7[R[#7R\#:S58/5?S59PV%;\S5:/5?S5;PV%8[R[#:S5</5?S5=PV%;[S5>/5?S5?PV%[TS5@#7RT#7R[#7R\#8Rm#7Rn#:S5A/5?S5BPV%;nS5C/5?S5DPV%8mRm#:S5E/5?S5FPV%;mS5G/5?S5HPV%7\R\#7Rm#:S5I/5?S5JPV%;mS5K/5?S5LPV%8\R\#:S5M/5?S5NPV%;\S5O/5?S5PPV%8[R[#8R\#7Rm#:S5Q/5?S5RPV%;mS5S/5?S5TPV%8\R\#:S5U/5?S5VPV%;\S5W/5?S5XPV%7[R[#7R\#:S5Y/5?S5ZPV%;\S5[/5?S5\PV%8[R[#:S5]/5?S5^PV%;[S5_/5?S5`PV%8TRT#7R[#8R\#7Rm#:S5a/5?S5bPV%;mS5c/5?S5dPV%8\R\#:S5e/5?S5fPV%;\S5g/5?S5hPV%7[R[#7R\#:S5i/5?S5jPV%;\S5k/5?S5lPV%8[R[#:S5m/5?S5nPV%;[R[/5?S5oPV%8TRT#8R\#7Rm#:Rn/5?S5pPV%;mRm/5?S5qPV%8\R\#:Ro/5?S5rPV%;\R\/5?S5sPV%7TRT#7Rp#:Rq/5?S5tPV%;pRp/5?S5uPV%8TRT#:Rr/5?S5vPV%;TRT/5?S5wPYD1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1S5x60~O%U@S5y+04+04+04R@Q0sQ0cQ0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0bPLPMPNQ0WQ0XQ0tPOPPPQQ0YQ0ZQ0[Q0\Q0]p,3DSOS5zp,3PCOS5{Q0uQ0vQ0wQ0xQ0yQ0zQ0{Q0^Q0_Q0aPYQ1{Q5xQ05,e9RsPsPsPsPsPsNg0}PKQ0bPMPOPPI1RS5|PKQ0bPLPMQ0WQ0XPOPPQ0uQ0^Q0_Q0aPYQ1{Q5xN?0|frS5}fqS5~PcQ1NPdfpS60PgPS%UJS61g02K5S62%UBS635nBS64&0[W$1Q$1P#E#ES65$0[#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#E#ES66%ZD#w#}#Y$00#Y#bS67%U0S685@0S69%U9Rt%UAS6:<1OtS6;Q0B#8Rt#8Ru#7$0HS6<Q67g02L0$0\S6=Q1N#dS6>g02LNRv%8G#FRw%NUS6?#d40:S6@Q1>#7S6A#7RU#8S6B#7#FS6CQ6B#8#FS6D&0\ES6EQ6A#FS6FQ1?#FS6GPwQ6@Q0C#FS6H%7tS6I#7#:S6J#d60:vS6K&0ah$07S6L$07$07$07Rh#}#pRx&00hS6M#8Rh#7#pRy%8h#pRhQ0A#8Rz#8R{#7R|#7#Z#[#Y#Y#Z#pS6N%8D#Z#}#Z#Y$00#Y#}#pS6O%FG%FtQ6A#8Rt#7R}#7S6P#FS6Qg02M:S6RQ6QQ1>#JS6S#dS6T40:R~Q1|#dS6U60:vS6VQ1i#FS1iQ6H%FuS6WQ6U%F|S6X%8{R|#FS6YQ6Q%7URu#8S6Z#FS6[Q1?#7Rv#7S6\#F%8vS6]#FQ1@#7S6^#FQ1A#FQ6:D_D_D_D_D_S6:D_D_D_16~TS6_P?Px16~rS6`P?Px16~pS6aP?Px16~qS6bP?Px16~\S6cP?Px16~oS6dP?Px16~mS6eP?Px16~nS6fP?Px16~[S6gP?PxQ5m,6~S5mP?PxQ5k,6~S5kP?PxQ5i,6~S5iP?PxQ5g,6~S5gP?PxQ5e,6~S5eP?PxQ5c,6~S5cP?PxQ5a,6~S5aP?PxQ5_,6~S5_P?PxQ5],6~S5]P?PxQ5[,6~S5[P?PxQ5Y,6~S5YP?PxQ5W,6~S5WP?PxQ5U,6~S5UP?PxQ5S,6~S5SP?PxQ5Q,6~S5QP?PxQ5O,6~S5OP?PxQ5M,6~S5MP?PxQ5K,6~S5KP?PxQ5I,6~S5IP?PxQ5G,6~S5GP?PxQ5E,6~S5EP?PxQ5C,6~S5CP?PxQ5A,6~S5AP?PxQ5>,6~S5>P?PxQ5<,6~S5<P?PxQ5:,6~S5:P?PxQ58,6~S58P?PxQ56,6~S56P?PxQ54,6~S54P?PxQ52,6~S52P?PxQ50,6~S50P?PxQ4},6~S4}P?PxQ4{,6~S4{P?PxQ4y,6~S4yP?PxQ4w,6~S4wP?PxQ4u,6~S4uP?PxQ4s,6~S4sP?PxQ4q,6~S4qP?PxQ4o,6~S4oP?PxQ4m,6~S4mP?PxQ4k,6~S4kP?PxQ4i,6~S4iP?PyQ4g,6~S4gP?PyQ4e,6~S4eP?PyQ4c,6~S4cP?PyQ4a,6~S4aP?PyQ4_,6~S4_P?PyQ4],6~S4]P?PxQ4[,6~S4[P?PxQ4Y,6~S4YP?PxQ4W,6~S4WP?PxQ4U,6~S4UP?PyQ4S,6~S4SP?PyQ4Q,6~S4QP?PxQ4O,6~S4OP?PxQ4M,6~S4MP?PxQ4K,6~S4KP?PxQ4I,6~S4IP?PxQ4G,6~S4GP?PxQ4E,6~S4EP?PxQ4C,6~S4CP?PxQ4A,6~S4AP?PxQ4?,6~S4?P?PxQ4=,6~S4=P?PxQ4;,6~S4;P?PxQ49,6~S49P?PxQ47,6~S47P?PxQ45,6~S45P?PxQ43,6~S43P?PxQ41,6~S41P?PxQ3~,6~S3~P?PxQ3|,6~S3|P?PxQ3z,6~S3zP?PxQ3x,6~S3xP?PxQ3v,6~S3vP?PxQ3t,6~S3tP?PxQ3r,6~S3rP?PxQ3p,6~S3pP?PxQ3n,6~S3nP?PxQ3l,6~S3lP?PxQ3j,6~S3jP?PxQ3h,6~S3hP?PxQ3f,6~S3fP?PxQ3d,6~S3dP?PxQ3b,6~S3bP?PxQ3`,6~S3`P?PxQ3^,6~S3^P?PxQ3\,6~S3\P?PxQ3Z,6~S3ZP?PxQ3X,6~S3XP?PxQ3V,6~S3VP?PxQ3T,6~S3TP?PxQ3R,6~S3RP?PxQ3P,6~S3PP?PxQ3N,6~S3NP?PxQ3L,6~S3LP?PyQ3J,6~S3JP?PyQ3H,6~S3HP?PyQ3F,6~S3FP?PyQ3D,6~S3DP?PxQ3B,6~S3BP?PxQ3@,6~S3@P?PxQ3>,6~S3>P?PxQ3<,6~S3<P?PyQ3:,6~S3:P?PyQ38,6~S38P?PyQ36,6~S36P?PyQ34,6~S34P?PyQ32,6~S32P?PxQ30,6~S30P?PxQ2},6~S2}P?PxQ2{,6~S2{P?PyQ2y,6~S2yP?PyQ2w,6~S2wP?PyQ2u,6~S2uP?PyQ2s,6~S2sP?PyQ2q,6~S2qP?PxQ2o,6~S2oP?PxQ2m,6~S2mP?PxQ2k,6~S2kP?PyQ2i,6~S2iP?PyQ2g,6~S2gP?PyQ2e,6~S2eP?PyQ2c,6~S2cP?PyQ2a,6~S2aP?PxQ2_,6~S2_P?PxQ2],6~S2]P?PxQ2[,6~S2[P?PyQ2Y,6~S2YP?PyQ2W,6~S2WP?PyQ2U,6~S2UP?PyQ2S,6~S2SP?PyQ2Q,6~S2QP?PxQ2O,6~S2OP?PxQ2M,6~S2MP?PxQ2K,6~S2KP?PyQ2I,6~S2IP?PyQ2G,6~S2GP?PyQ2E,6~S2EP?PyQ2C,6~S2CP?PyQ2A,6~S2AP?PxQ2?,6~S2?P?PxQ2=,6~S2=P?PxQ2;,6~S2;P?PyQ29,6~S29P?PxQ27,6~S27P?PxQ25,6~S25P?PxQ23,6~S23P?Q6M#Y#pS6MQ21,6~S21P?Q6MQ1~,6~S1~P?Q6MQ1|,6~S6hP?Q6MQ6QQ1y'6S1yPWQ6OQ6QQ0`'6S6iPWQ6NQ6Q/6>S6jPWQ0C#8#[#Z#Y#Y#}#[#[#[#w#Z#pS6kQ04#US6lH1IF<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<F<%}|#\#b%7uR|#[#[#\#b+1HS6m%d>S6nQ6Z#Z#[#ZR[#Y$0a#bPWQ6UCSS6ZQ6n%[[$0M#bQ1v%JDR[#dS1vCSS6oQ1;#7Rn#NS1;,6wRm%pnRo+0DS6p%\n#\#\#\Rn#J%7n#:Rn60QwS6qQ6jQ15#dR\+0DS6rQ6Q%8D#Y#w#w#\#bS6sQ6L#\#b40QS6LQ6hQ14#JS14#dS6t+0DS6u%8}#FRq/6>RpQ1v+0DS6vQ6s>0QqnS6wQ6jP\PmPoCxS6xQ6hQ6tPmPoCxS6yQ6hQ6tQ6jP\CxS6zPpQ1vPmPoCxS6{PpQ1vQ6jP\CxS6|PpQ1vQ6hQ6tCxS6}PwQ6?PWQ6nCSS6~PwQ0B#NS70PWQ6I#FS6ICSS71Pw%NGS72PWQ1g#8RG#7#FS73CSS74Pw%NuS75PW%8G#FS76CSS77PwQ0C#NS78PW%7ZRp#7S79#FS7:CSS7;PwQ79#NS7<PW%8p#FS7=CSS7>Pw%N|S7?PW%8ZRZ#7#FS7@CSS7APwQ6\#7S7B#NS7CPW%8Z#FS7DCSS7EPw%NHS7FPW%7zRH#7R\#FS7GCSS7HPwQ1j#NS1jPW%8H#FS7ICSS7JPwQ79#7#NS7KPWQ6XCSS7LPw%7\#NS7MPWQ6YCSS7NPw%7|#NS7OPW%F|S7PCSS7QPwQ6P#7#NS6PPWQ6[CSS7RQ6QQ1B#bS1BPWPqCSS7SQ63+1F41EDWDWDWDWDWDWDWQ6<I0CS7Tg02MfS7U#US7VQ6;&0vER|/]AR\20;E[RoQ6>54|S7WP\Q0|-0;ERmQ6@54|S7XP\Q6S-0;ERnQ6C54|S6SP\1LEFRFQ6D54|S7YP\Q0`-0;ERr=4|wS7ZP\Q1g,LERTQ6@54|S7[P\Q0kQ6K54|S7\P\1LEzS7]=4|xP\P|1LEUPyP\P|1LEtPhP\P|1LEvQ6NP\P|Q1@,LEQ6OP\P|Q1h,LERvQ6QP\P|1LEGRGQ6VP\1LEpRpQ1i54|S6VP\1LEZRZQ6H54|S1hP\P|1LEHRHQ6WP\1LE{R{Q6U54|S6WP\%JuS1@-0;ERuQ6X54|P\P|Q6B,LERUQ6YP\P|1LE}R}Q6QP\P|%8t,LERtQ6[%U\DfDfDfD1DfD1DfDfS6BDfDfDfDfS7^D1D1D1D1S7_Q1sQ1tPs&1CRS7`00tS#RdQ0sQ0cQ0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0bPLPMPNQ0WQ0XQ0tPOPPPQQ0YQ0ZQ0[Q0\Q0]p,3DSAS7ap,3DSWS7bQ5zp,3DS8S7cp,3DSVS7dp,3DSHS7ep,3DSMS7fp,3PCAS7gQ5{p,3PC8S7hp,3PCCS7ip,4DISJS7jQ0uQ0vQ0wQ0xQ0yp,5SPOBJS7kQ0zQ0{p,4FFDSS7lp,4FFPCS7mp,4FPPCS7np,4FPDSS7op,4HULLS7pp,3FRWS7qp,3FSVS7rp,3FSWS7sp,3FLWS7tp,3AC1S7up,3LV1S7vQ60Q0^Q0_Q0aPYQ1{Q5xQ1qQ1rQ1uflS7wQ1pPsQ1;@02>Y#RdPsQ15Q1{602>#RdPsg02NbS7xQ7xQ14'sS14Q5x402#Rdp#1@0sQ1qQ1rQ0?\3S0?%c2S7y%c6S7zP1An8239G86AG786AG782S7{'BRz[AG862AG863S7|'BAn7629G78[S7}An=869G=7\zP8P6P2P3H1AP3n2001000000120000000WPWOW<X;5S7~Q0?Q7yQ7zQ7}]P]O]<^;5S7yP3PBQ5}Q619nJRS7}+0BQ5~60r:RzQ62Q63Q629GBzQ639GBzQ0sQ0cQ0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0bPLPMPNQ0WQ0XQ0tPOPPPQQ0YQ0ZQ0[Q0\Q0]Q7aQ7bQ5zQ7cQ7dQ7eQ7fQ7gQ5{Q7hQ7iQ7jQ0uQ0vQ0wQ0xQ0yQ7kQ0zQ0{Q7lQ7mQ7nQ7oQ7pQ7qQ7rQ7sQ7tQ7uQ7vQ5}Q61Q5~Q1pQ1qNv0q20NBzH0pO5b0P:Q5~Q7}+0BS80Q60Q64H0oeg02O]S81Q7U#cS82']S83g02PZS84']S85Q83Q84Q81Q82Q7TQ7VCTQ6;CTRz'eQ85P:Q66Q05Q69Q6;Q1Ng02QUS1N00nSQ6lQ64&0m@5nBQ6<I0CQ7VK0l;0zdQ7UQ60Q8060k:+0NPsQ04&0j@$0iQ7T$0hRz40g#RdPsQ7`Q7T$0fQ7_40e#RdQ0DQ0EQ0FQ7_9qR6Q7`>1=z@S80:0AR6PKQ0bPMPOPPP8J0dS6420b:7S69&1<@S66fwS86;k=fxS87>1;:<1]VAR@#cS88,]0S89#cS8:Q89Q88Q00PIP0PKP2n10110M00012010L10KS00P@PVQ6?PWQ6nCXS6?P@PVQ70PWQ6ICXS6IP@PVQ72PWQ73CXS73P@PVQ75PWQ76CXS76P@PVQ78PWQ7:CXS7:P@PVQ7<PWQ7=CXS7=P@PVQ7?PWQ7@CXS7@P@PVQ7CPWQ7DCXS7DP@PVQ7FPWQ7GCXS7GP@PVQ1jPWQ7ICXS7IP@PVQ7KPWQ6XCXS6XP@PVQ7MPWQ6YCXS6YP@PVQ7OPWQ7PCXS7PP@PVQ6PPWQ6[CXS6[%U@S6PD1D1D1D1D1D1D13VQ89Q88P@PVQ1BPWPqCXS1BP@Q1wQ6k54VS1wP@Q1xQ6N54VS1xP@Q1zQ6O54VS1zQ6PD1D17VOS7OQ89Q88Q01P0P0P0P0Q0dPOP0P0P>P>CTg02RLRqQ0d^20]2PqQ0dP2Q01P0P0Q0dP8P3P2O2S7MP9Q0dg02S1RzP9P0PzP0P0P0P0P3P>%73S7K#JS1jQ7K#NS7Fn0110M0003001000010000S7CP[Pq^2qS7?^2qS7<PqPqP2PqPqP2P7P2P3O2S78#7S75P=P2P3O2S72#8S70Q7?PqPqP3P6P3O1S8;#7%83RSQ0@n0110M0003100001000000X2qp?100010JP3O1S8<#7S8=n0110M0003100001000000S8>PqPqP2Q70Q72#7PSn0110M0003100001000000PqPqP3Q8=PSQ0@n0110M0003100001000000S72n0110M0003100001000000X2qX2qQ7<PqPqP2PqPqP2Q78#8Q75Q8<#8S8<n0110M0003100001000000Q8>PqPqP3Q8<Q8=Q1>n0110M0003100001000000n0110M0003100001000000X2qX2qp?200010J0010JS8=P3PDO2#JS8<P0^2q^2qPqP0P2PqP0P2P0P0Q78P>Q1jQ7Fn0110M0003001000010000S8>P0P0Q78P[%JSQ7?PqPqP3Q7K#8Q8;#8PDn0110M0003100001000000X2qp?100010JP3O1S8;#NS7Kn0110M0003001000010000Q1jn0110M0003100001000000PqP0P2P0P0Q78%NDQ8;#JS8;%NSn0110M0003001000010000Q8>Q8;n0110M0003100001000000PqP0P3Q7FQ7KP>n0110M0003100001000000n0110M0003100001000000X2qX2qp?100110JS7KPDP3O2S8;n0110M0003001000010000S8>P0PzP8g02SWS78g02T=S7?g02TcRSn0110M0003001000010000S75P0PzP7PSPz^2q^2q^2zPqPzP2PqPzP2P=P7P2P3O3S7<P=PSP2P3O3PSn0110M0003100001000000PqPzP2P=Q7?P2P3O3Q7<PSn0110M0003100001000000PqPzP3Q7?Q7?P6n0110M0003100001000000n0110M0003100001000000X2qX2qX2zp?100210JS7<Q78P2P3O3S70PSn0110M0003001000010000S8?P0PzP7Q7?Q7?PzPzQ70Q78PSQ7?n0110M0003000000n0110M0003001000010000S7?n0110M0003001000010000g02UIS70Q05Q70n0110M0003000000P0P0P2P>Q1jQ7Fn0110M0003001000010000S7FQ8>+06P0P0Q7FP[Q8<Q8;n0110M0003001000010000S1jP0P0Q8>P0P0P8P>%N3S8>%J3S8@n0110M0003001000010000S8AP0P0P0P0P7P>Q8>Q8@n0110M0003001000010000S8BQ1jQ8=P2P3O2S8=#JS8CQ7KP2P3O2S8Dn0110M0003011000010000P0P0Q8BQ1jQ7KP3P2O2S8EQ8=#NS8=n0110M0003011000010000n0110M0003001100011000+06n0110M00020101n200110M000121000000Q01P0P0Q0dQ7MP9Q0dPzP9P0PzQ7CQ75Q8?Q7?n0110M0003001000010000Q70Q05Q70n0110M0003000000Q7FQ7C+06Q1jP0P0Q7CQ8AP0P0Q8BQ7FQ8CQ8Dn0110M0003001000010000P0P0Q8BQ7FQ8EQ8=n0110M0003001000010000n0110M0003001100011000+06n0110M00020001n200110M000121000000P9Q0dPzP9P0PzP3PSQ7<Q78Q0@P3O3PSn0110M0003001000010000Q05Q05Q70n0110M0003000000P0P0P>P[CT&1:[n0110M00020000n0110M0003110001100000X20X2qp?100010JP3Q0`O2RSQ01P0P0Q0dPSP0Q0dP3P0P0P2P>Q8>Q8@n0110M0003001000010000RS$1:P0P0P0P0P6P[Q8<Q8;n0110M0003001000010000P>Q8>Q8@n0110M0003001000010000P0P0PSQ0`PqPqP3PqPqP3PqPqP3Q72#8Q72#7Q1>n0110M0003100001000000Rq#8%7qQ0An0110M0003100001000000Rq#8%7qQ1gn0110M0003100001000000#JQ7KQ0BP3O2n0110M0003001100010000+06RqPqn0110M0003001100011000n200110M000121000000n0110M0003001100011000P2n200110M000120000000S0BP@Q1}Q6M54VS1}P@Q20Q6M54VS20P@Q22Q6M54VS22P@Q24Q6M54VS24P@Q26=4VxS26P@Q28=4VxS28P@Q2:=4VxS2:P@Q2<=4VyS2<P@Q2>=4VxS2>P@Q2@=4VxS2@P@Q2B=4VxS2BP@Q2D=4VyS2DP@Q2F=4VyS2FP@Q2H=4VyS2HP@Q2J=4VyS2JP@Q2L=4VyS2LP@Q2N=4VxS2NP@Q2P=4VxS2PP@Q2R=4VxS2RP@Q2T=4VyS2TP@Q2V=4VyS2VP@Q2X=4VyS2XP@Q2Z=4VyS2ZP@Q2\=4VyS2\P@Q2^=4VxS2^P@Q2`=4VxS2`P@Q2b=4VxS2bP@Q2d=4VyS2dP@Q2f=4VyS2fP@Q2h=4VyS2hP@Q2j=4VyS2jP@Q2l=4VyS2lP@Q2n=4VxS2nP@Q2p=4VxS2pP@Q2r=4VxS2rP@Q2t=4VyS2tP@Q2v=4VyS2vP@Q2x=4VyS2xP@Q2z=4VyS2zP@Q2|=4VyS2|P@Q2~=4VxS2~P@Q31=4VxS31P@Q33=4VxS33P@Q35=4VyS35P@Q37=4VyS37P@Q39=4VyS39P@Q3;=4VyS3;P@Q3==4VyS3=P@Q3?=4VxS3?P@Q3A=4VxS3AP@Q3C=4VxS3CP@Q3E=4VxS3EP@Q3G=4VyS3GP@Q3I=4VyS3IP@Q3K=4VyS3KP@Q3M=4VyS3MP@Q3O=4VxS3OP@Q3Q=4VxS3QP@Q3S=4VxS3SP@Q3U=4VxS3UP@Q3W=4VxS3WP@Q3Y=4VxS3YP@Q3[=4VxS3[P@Q3]=4VxS3]P@Q3_=4VxS3_P@Q3a=4VxS3aP@Q3c=4VxS3cP@Q3e=4VxS3eP@Q3g=4VxS3gP@Q3i=4VxS3iP@Q3k=4VxS3kP@Q3m=4VxS3mP@Q3o=4VxS3oP@Q3q=4VxS3qP@Q3s=4VxS3sP@Q3u=4VxS3uP@Q3w=4VxS3wP@Q3y=4VxS3yP@Q3{=4VxS3{P@Q3}=4VxS3}P@Q40=4VxS40P@Q42=4VxS42P@Q44=4VxS44P@Q46=4VxS46P@Q48=4VxS48P@Q4:=4VxS4:P@Q4<=4VxS4<P@Q4>=4VxS4>P@Q4@=4VxS4@P@Q4B=4VxS4BP@Q4D=4VxS4DP@Q4F=4VxS4FP@Q4H=4VxS4HP@Q4J=4VxS4JP@Q4L=4VxS4LP@Q4N=4VxS4NP@Q4P=4VxS4PP@Q4R=4VxS4RP@Q4T=4VyS4TP@Q4V=4VyS4VP@Q4X=4VxS4XP@Q4Z=4VxS4ZP@Q4\=4VxS4\P@Q4^=4VxS4^P@Q4`=4VyS4`P@Q4b=4VyS4bP@Q4d=4VyS4dP@Q4f=4VyS4fP@Q4h=4VyS4hP@Q4j=4VyS4jP@Q4l=4VxS4lP@Q4n=4VxS4nP@Q4p=4VxS4pP@Q4r=4VxS4rP@Q4t=4VxS4tP@Q4v=4VxS4vP@Q4x=4VxS4xP@Q4z=4VxS4zP@Q4|=4VxS4|P@Q4~=4VxS4~P@Q51=4VxS51P@Q53=4VxS53P@Q55=4VxS55P@Q57=4VxS57P@Q59=4VxS59P@Q5;=4VxS5;P@Q5==4VxS5=P@Q5?=4VxS5?P@Q5B=4VxS5BP@Q5D=4VxS5DP@Q5F=4VxS5FP@Q5H=4VxS5HP@Q5J=4VxS5JP@Q5L=4VxS5LP@Q5N=4VxS5NP@Q5P=4VxS5PP@Q5R=4VxS5RP@Q5T=4VxS5TP@Q5V=4VxS5VP@Q5X=4VxS5XP@Q5Z=4VxS5ZP@Q5\=4VxS5\P@Q5^=4VxS5^P@Q5`=4VxS5`P@Q5b=4VxS5bP@Q5d=4VxS5dP@Q5f=4VxS5fP@Q5h=4VxS5hP@Q5j=4VxS5jP@Q5l=4VxS5lP@Q5n=4VxS5nP@Q5o=4VxS5oP@Q5p=4VxS5pP@Q5q=4VxS5qP@Q5r=4VxS5rP@Q5s=4VxS5sP@Q5t=4VxS5tP@Q5u=4VxS5uP@Q5v=4VxS5vP@Q5w=4VxS5wQ6PD1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D13VQ89#US7K3@D1'e%c4R4,]0Rq#cS1gQ80Q00Q6?Q6IQ73Q76Q7:Q7=Q7@Q7DQ7GQ7IQ6XQ6YQ7PQ6[Q0a419D9D9D9S0A5V4RSQ1BQ1wQ1xQ1zQ0aD9S1z9V4OS1xQ0BQ1}Q20Q22Q24Q26Q28Q2:Q2<Q2>Q2@Q2BQ2DQ2FQ2HQ2JQ2LQ2NQ2PQ2RQ2TQ2VQ2XQ2ZQ2\Q2^Q2`Q2bQ2dQ2fQ2hQ2jQ2lQ2nQ2pQ2rQ2tQ2vQ2xQ2zQ2|Q2~Q31Q33Q35Q37Q39Q3;Q3=Q3?Q3AQ3CQ3EQ3GQ3IQ3KQ3MQ3OQ3QQ3SQ3UQ3WQ3YQ3[Q3]Q3_Q3aQ3cQ3eQ3gQ3iQ3kQ3mQ3oQ3qQ3sQ3uQ3wQ3yQ3{Q3}Q40Q42Q44Q46Q48Q4:Q4<Q4>Q4@Q4BQ4DQ4FQ4HQ4JQ4LQ4NQ4PQ4RQ4TQ4VQ4XQ4ZQ4\Q4^Q4`Q4bQ4dQ4fQ4hQ4jQ4lQ4nQ4pQ4rQ4tQ4vQ4xQ4zQ4|Q4~Q51Q53Q55Q57Q59Q5;Q5=Q5?Q5BQ5DQ5FQ5HQ5JQ5LQ5NQ5PQ5RQ5TQ5VQ5XQ5ZQ5\Q5^Q5`Q5bQ5dQ5fQ5hQ5jQ5lQ5nQ5oQ5pQ5qQ5rQ5sQ5tQ5uQ5vQ5wQ0aD9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9S1w5V4S1B%UqS1>5@qS725@qR95@qS8@30S8>dQ8>Q1gQ80Q1gB0AR^3W:S80P=Q8@P3EKQ8@:0ARCQ0?Q7zP1A@8239G86P8P6O1Q7{'B[S7{P6P2O1Q7|'BA@7629G78S7|[Q7|P7P8O1AG=76'B[P8P6P2P3H21P2n2001000000120000000W:XD2W<X;5S7|Q0?Q7zQ7{]:^D2]<^;5S0?P3PqPR20943R5P`20843S7zCCX1qS7{PSP9P2O5PR2094SS8@P_2084SRSCCQ7{=Gq9'BP1PRQ8@P`PSCCPRP5PaQ7zCCX1qS8>=Gq9p+01AS8;PfPcQ7T$18,PIS7TPdPePaPgGDP3PRQ8@PfPSCCPRP5f?RSQ7zCCX1qS8@=Gq9Q7|Q0?P3PqPRP5PiQ7zCCX1qS8<Q1xQ72P2O5PRQ1x-094S01Q1PQ1x-084R9CCS70Q8<Q725Gq'BP1PRQ01PiP9CCS0@PRP5Q1OQ7zCCX1qS78Q725Gqp+01GP]PcQ7TPdPeQ1OPgGDP3PRQ01P]P9CCS01PRP5PjQ7zCCX1qS7<Q725GqQ7|Q0?P3PqPRP5fGR9Q7zCCX1qS72Q1BQ1>P2O5PRQ1B-094S1jQ0oQ1B-084S1BCCQ72Q1>5GqS8='BP1PRQ1jP9Q1BCCPRP5Q1SQ7zCCX1qQ1>5GqS8Ep+01MPbPcQ7TPdPeQ1SPgGDP3PRQ1jPbQ1BCCPRP5fKR5Q7zCCX1qQ1>5GqS7zQ0sQ0cp,4HHbpS1BPKQ0bPLPMQ0WQ0XQ0tPOPPQ0eQ0uQ0vQ0wQ0xQ0yQ0zQ0{Q0^Q0_Q0aPYQ1{Q5xp+01NP5p+01FPjQ1QNO17Q0cQ0f<0Y5S0fQ0d#cS0dQ66Q0dp+01PS66=k3kW:Q0oQ0nPKPOQ0^Q0_Q0aPYQ1{Q5xL16EKQ0np+01OQ1U3kPRQ0AQ7B#7#NS7B/5WS5x=@VYS1{611KQ1z>10OYQ1wPVQ5@#8$00S5@#8S0_#7S0^#:S1j/5?S7FPVQ0^#;S0^/5?S8BPVQ0_#8S0_#:S8D/5?S8CPVQ0_#;S0_/5?S8APVQ5@#7S5@#7S7C#:S7?/5?S8?PVQ7C#;S7C/5?S75PVQ5@#8S5@#:S7M/5?S8FPVQ5@#;S5@/5?S8GPYD1D1D1D1S8H60~OQ5y+04+04+04S5yQ0sQ0cQ0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0bPLPMPNQ0WQ0XQ0tPOPPPQQ0YQ0ZQ0[Q0\Q0]Q5zQ5{Q0uQ0vQ0wQ0xQ0yQ0zQ0{Q0AQ1zQ1wQ1{PYQ8HPsPsPsPsPsPsNg0}Q5|PKQ0bPLPMQ0WQ0XPOPPQ0uQ0AQ1zQ1wQ1{PYQ8HN?0|p+01RQ1TPcQ67PdPkPgQ7_Q61Q62Q6J$20S5|5nBS8IQ65%ZD#w#}#Y#Y#Z#[#:S8JQ685@0S68Q6;Q6<Q8JQ6=Q6>Q6@Q6CQ6DQ6EQ6FQ6GPwQ6@Q6KQ6nQ6:D_D_D_PwQ7BPWQ6QP~Q5@P?PhP~Q7MP?PhP~Q7CP?PhP~Q7?P?PhP~Q0_P?PhP~Q8DP?PhP~Q0^P?PhP~Q1jP?PhQ6lDgDgDgDgDgDgDgDgDgQ6mQ6ZQ6oQ6pQ6qQ6rQ6LQ6uQ6vQ6wQ6xQ6yQ6zQ6{Q6|Q6}Q6RQ6KQ6T40:Q1|'6R~P?Q6nP~Q1vQ6hQ6tCxQ6~Q71Q74Q77Q7;Q7>Q7AQ7EQ7HQ7JQ7LQ7NQ7QQ7RQ7SQ6jPWQ6kQ6iPWQ6NQ1yPWQ6OQ6hP?Q6MQ1~P?Q6MQ21P?Q6MQ23P?Q6MQ25P?PxQ27P?PxQ29P?PxQ2;P?PyQ2=P?PxQ2?P?PxQ2AP?PxQ2CP?PyQ2EP?PyQ2GP?PyQ2IP?PyQ2KP?PyQ2MP?PxQ2OP?PxQ2QP?PxQ2SP?PyQ2UP?PyQ2WP?PyQ2YP?PyQ2[P?PyQ2]P?PxQ2_P?PxQ2aP?PxQ2cP?PyQ2eP?PyQ2gP?PyQ2iP?PyQ2kP?PyQ2mP?PxQ2oP?PxQ2qP?PxQ2sP?PyQ2uP?PyQ2wP?PyQ2yP?PyQ2{P?PyQ2}P?PxQ30P?PxQ32P?PxQ34P?PyQ36P?PyQ38P?PyQ3:P?PyQ3<P?PyQ3>P?PxQ3@P?PxQ3BP?PxQ3DP?PxQ3FP?PyQ3HP?PyQ3JP?PyQ3LP?PyQ3NP?PxQ3PP?PxQ3RP?PxQ3TP?PxQ3VP?PxQ3XP?PxQ3ZP?PxQ3\P?PxQ3^P?PxQ3`P?PxQ3bP?PxQ3dP?PxQ3fP?PxQ3hP?PxQ3jP?PxQ3lP?PxQ3nP?PxQ3pP?PxQ3rP?PxQ3tP?PxQ3vP?PxQ3xP?PxQ3zP?PxQ3|P?PxQ3~P?PxQ41P?PxQ43P?PxQ45P?PxQ47P?PxQ49P?PxQ4;P?PxQ4=P?PxQ4?P?PxQ4AP?PxQ4CP?PxQ4EP?PxQ4GP?PxQ4IP?PxQ4KP?PxQ4MP?PxQ4OP?PxQ4QP?PxQ4SP?PyQ4UP?PyQ4WP?PxQ4YP?PxQ4[P?PxQ4]P?PxQ4_P?PyQ4aP?PyQ4cP?PyQ4eP?PyQ4gP?PyQ4iP?PyQ4kP?PxQ4mP?PxQ4oP?PxQ4qP?PxQ4sP?PxQ4uP?PxQ4wP?PxQ4yP?PxQ4{P?PxQ4}P?PxQ50P?PxQ52P?PxQ54P?PxQ56P?PxQ58P?PxQ5:P?PxQ5<P?PxQ5>P?PxQ5AP?PxQ5CP?PxQ5EP?PxQ5GP?PxQ5IP?PxQ5KP?PxQ5MP?PxQ5OP?PxQ5QP?PxQ5SP?PxQ5UP?PxQ5WP?PxQ5YP?PxQ5[P?PxQ5]P?PxQ5_P?PxQ5aP?PxQ5cP?PxQ5eP?PxQ5gP?PxQ5iP?PxQ5kP?PxQ5mP?PxQ6gP?PxQ6fP?PxQ6eP?PxQ6dP?PxQ6cP?PxQ6bP?PxQ6aP?PxQ6`P?PxQ6_P?PxQ63H15F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=F=DWDWDWDWH15DWDWDWDWQ6<I0CRxQ7UQ1v-1~~S63Q7V3@S6_Q6;P\Q7WP\Q7XP\Q6SP\Q7YP\Q7ZP\Q7[P\Q7\P\Q7]Q6n54|Q7^D1D1D1D1R?Q1UP5PsQ7`Q7_+0t#RdQ0sQ0cQ0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0bPLPMPNQ0WQ0XQ0tPOPPPQQ0YQ0ZQ0[Q0\Q0]Q7aQ7bQ5zQ7cQ7dQ7eQ7fQ7gQ5{Q7hQ7iQ7jQ0uQ0vQ0wQ0xQ0yQ7kQ0zQ0{Q7lQ7mQ7nQ7oQ7pQ7qQ7rQ7sQ7tQ7uQ7vPkQ0AQ1zQ1wQ1{PYQ8HPbQ1SPSP^P8PsQ1;Q1{802>#RdPsQ15>02>Y#RdPsQ7xQ14Q8H402#Rdp#1@0sPbQ1SQ7~Q7yP3PBfORyQ7}+0BS7yQ1T60r:RWQ62Q5|Q629GBWQ5|9GBWQ0sQ0cQ0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0bPLPMPNQ0WQ0XQ0tPOPPPQQ0YQ0ZQ0[Q0\Q0]Q7aQ7bQ5zQ7cQ7dQ7eQ7fQ7gQ5{Q7hQ7iQ7jQ0uQ0vQ0wQ0xQ0yQ7kQ0zQ0{Q7lQ7mQ7nQ7oQ7pQ7qQ7rQ7sQ7tQ7uQ7vPyQ61Q1TQ1RPbNv0qQ0sQ0cQ0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0bPLPMPNQ0WQ0XQ0tPOPPPQQ0YQ0ZQ0[Q0\Q0]Q5zQ5{Q0uQ0vQ0wQ0xQ0yQ0zQ0{p,3THAQ1fp,3TH8p,3THSp,3THFp,3THPp,3THDp,4THC1p,4THC2PyQ61Q1TQ6JQ1RPbg02UiRW#US5{%cWS5z&1}0S7v&1|0S7u&1{0RW2140>S7tQ6J#uRw+0?,vWP0Pwg02VUS7sQ1k#uH0`,vW413Q08-1yWS7rP3P6Ps21x36#RdB1w0>2H1vS7qb?b@bAQ6J#mQ6JQ1k+01'BP3b>S1kNk1uH0pO5b0P:Q1TQ7}+0BRwPkQ8IH0oeQ85Q83Q84Q81Q82PxQ6_CTQ6;CTS82'eQ85P:Q65Q05Q68Q6;Q67Q1NQ7_+0nQ6lQ8IQ5y$0m5nBQ6<I0CQ7VK0lQ8230dQ7UB0k:kwS82Q63Q7VP0P[Q7y@0^~3Z0I0Q0GPKQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VPLPMPNQ0WQ0XPOPPPQQ0YQ0ZQ0[Q0\Q0]Q1fQ1TQ61Q6JQ1kNS1t1PI[-0_IQ0|Q0}+1sQ0|-01>S1kQ0}#mQ0~-01>[S61[Q0|#mS1fg02W<RBQ0|Q0}<1r2UWHQ1fQ0~#m\B]HP2Q0|-1q>,ezQ1keO1Q61Q5{Q5zQ7vQ7uQ7t%u[Rz+0?,vWP0PzQ7sQ0|#u>1o0IH0`,vW613WQ7rQ7qb?b@bA%m[Q0~-01['BP3b>bLc0DbL-1n[J0]Q1v-0Jw-0_I:0^w~eQ1v-1lw:0^w~eP:PkPwQ63H1keQ7UQ82+0NJ1jP:PkPwQ6_H1iePsQ04Q5y$0j$0i&0hxRw40g#RdPsQ7`&0fx<0e?#RdQ0DQ0EQ0FAqR6?Q7`Q5y61=wRw:0AR6Q64Q69Q5y$1<S5yQ1Z;k=Q1Y>1;:<Q8:Q89Q88Q00P@Q6?P@Q6IP@Q73P@Q76P@Q7:P@Q7=P@Q7@P@Q7DP@Q7GP@Q7IP@Q6XP@Q6YP@Q7PP@Q6[Q5xQ6Q54VR~Q6P5@@D1D1D1D1D1D1D13VQ89Q7OQ89Q88Q0BP@Q1}P@Q20P@Q22P@Q24P@Q26P@Q28P@Q2:P@Q2<P@Q2>P@Q2@P@Q2BP@Q2DP@Q2FP@Q2HP@Q2JP@Q2LP@Q2NP@Q2PP@Q2RP@Q2TP@Q2VP@Q2XP@Q2ZP@Q2\P@Q2^P@Q2`P@Q2bP@Q2dP@Q2fP@Q2hP@Q2jP@Q2lP@Q2nP@Q2pP@Q2rP@Q2tP@Q2vP@Q2xP@Q2zP@Q2|P@Q2~P@Q31P@Q33P@Q35P@Q37P@Q39P@Q3;P@Q3=P@Q3?P@Q3AP@Q3CP@Q3EP@Q3GP@Q3IP@Q3KP@Q3MP@Q3OP@Q3QP@Q3SP@Q3UP@Q3WP@Q3YP@Q3[P@Q3]P@Q3_P@Q3aP@Q3cP@Q3eP@Q3gP@Q3iP@Q3kP@Q3mP@Q3oP@Q3qP@Q3sP@Q3uP@Q3wP@Q3yP@Q3{P@Q3}P@Q40P@Q42P@Q44P@Q46P@Q48P@Q4:P@Q4<P@Q4>P@Q4@P@Q4BP@Q4DP@Q4FP@Q4HP@Q4JP@Q4LP@Q4NP@Q4PP@Q4RP@Q4TP@Q4VP@Q4XP@Q4ZP@Q4\P@Q4^P@Q4`P@Q4bP@Q4dP@Q4fP@Q4hP@Q4jP@Q4lP@Q4nP@Q4pP@Q4rP@Q4tP@Q4vP@Q4xP@Q4zP@Q4|P@Q4~P@Q51P@Q53P@Q55P@Q57P@Q59P@Q5;P@Q5=P@Q5?P@Q5BP@Q5DP@Q5FP@Q5HP@Q5JP@Q5LP@Q5NP@Q5PP@Q5RP@Q5TP@Q5VP@Q5XP@Q5ZP@Q5\P@Q5^P@Q5`P@Q5bP@Q5dP@Q5fP@Q5hP@Q5jP@Q5lP@Q5nP@Q5oP@Q5pP@Q5qP@Q5rP@Q5sP@Q5tP@Q5uP@Q5vP@Q5wP@Q7F=4VhS7FP@Q8B=4VhS8BP@Q8C=4VhS8CP@Q8A=4VhS8AP@Q8?=4VhR[P@Q75=4VhRzP@Q8F=4VhRBP@Q8G=4VhRhQ6PD1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D13VQ7K3@D1'eQ1gQ00Q6?Q6IQ73Q76Q7:Q7=Q7@Q7DQ7GQ7IQ6XQ6YQ7PQ6[Q0a-1h~419D9D9D95V4R~Q1xQ0BQ1}Q20Q22Q24Q26Q28Q2:Q2<Q2>Q2@Q2BQ2DQ2FQ2HQ2JQ2LQ2NQ2PQ2RQ2TQ2VQ2XQ2ZQ2\Q2^Q2`Q2bQ2dQ2fQ2hQ2jQ2lQ2nQ2pQ2rQ2tQ2vQ2xQ2zQ2|Q2~Q31Q33Q35Q37Q39Q3;Q3=Q3?Q3AQ3CQ3EQ3GQ3IQ3KQ3MQ3OQ3QQ3SQ3UQ3WQ3YQ3[Q3]Q3_Q3aQ3cQ3eQ3gQ3iQ3kQ3mQ3oQ3qQ3sQ3uQ3wQ3yQ3{Q3}Q40Q42Q44Q46Q48Q4:Q4<Q4>Q4@Q4BQ4DQ4FQ4HQ4JQ4LQ4NQ4PQ4RQ4TQ4VQ4XQ4ZQ4\Q4^Q4`Q4bQ4dQ4fQ4hQ4jQ4lQ4nQ4pQ4rQ4tQ4vQ4xQ4zQ4|Q4~Q51Q53Q55Q57Q59Q5;Q5=Q5?Q5BQ5DQ5FQ5HQ5JQ5LQ5NQ5PQ5RQ5TQ5VQ5XQ5ZQ5\Q5^Q5`Q5bQ5dQ5fQ5hQ5jQ5lQ5nQ5oQ5pQ5qQ5rQ5sQ5tQ5uQ5vQ5wQ7FQ8BQ8CQ8AP[PzPBPhQ0aD9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D9D95V4RhQ1>5@qRB5@qRz5@qR[70wRVdPVQ1gPwQ80P=P[P3EKB0ARC[Q7|Q0?P3PqQ7{P~PzP2O5PR2094~R[P_2084~R~CCQ7{=Gqz'BP1PRP[P`P~CCQ8>=Gqzp+01`PfPc&18x,PIRxPdPePaPgGDP3PRP[PfP~CCQ8@=GqzQ7|Q0?P3PqQ8<Q1xPBP2O5Q70Q8<=GqB'BP1Q0@Q78=GqBp+01fP]PcPxPdPeQ1OPgGDP3Q01Q7<=GqBQ7|Q0?P3PqQ72PhQ1>P2O5PR2094hRqQ0o2084hRhCCQ8='BP1PRPqP9PhCCQ8Ep+01lPbPcPxPdPeQ1SPgGDP3PRPqPbPhCCQ7zQ0sQ0cQ1BPKQ0bPLPMQ0WQ0XQ0tPOPPQ0eQ0uQ0vQ0wQ0xQ0yQ0zQ0{Q0AQ1zQ1wQ1{PYQ8HQ1qP5Q1TPjQ1QNO17Q0fQ0dQ5yQ0dQ7w=k3kW:Q0oQ0nPKPOQ0AQ1zQ1wQ1{PYQ8HL16EKQ0nQ1pQ1U3kQ0np+01oRYQ7wPkPyP3J1fQ0n?kYkPRPyP?Q1UH1e&1d?Rh9qRy%c\RqP\Q7WP\Q7XP\Q6SP\Q7YP\Q7ZP\Q7[Q6BD1D1D1R4'eA0qh4RBdPBPqPhQ1V=qR3X:qP2P4P3EKAqRl4PKQ0bPLPMQ0WQ0XPOPPPQQ0Yp,3LBlRPQ0jQ0up,3UM1p,3UG1p,3UG2p,3UG3p,3UFOPlPkND1cQ0C#JROPXQ0:$1bRMPPPlQ6J,sLRKPQQ0YQ0jN90ZQ79#JR49OlKQ0Y$0c$1`RqQ1VQ0`Q0Y+1_Rh7OQ[Q0hQ0gP6AVX23Q0jDiRBQ1Y?O8O[^4X^80^10'B40XP1POPXPMPPQ1VPKPQQ0YQ0jN90ZQ1V?OK4fSRz?OQh\qQ1X?O8O\B^4X^80^1040Xp+027Q1ZPcQ8J,PIR~PdPePzPgGDP3POPXPMPPQ1ZPKPQQ0YQ0jN90ZQ1Y?OK4Q1X?OQh\qQ1\?O8O\B^4X^80^1040XP1Q1X?OK4fWS1X?OQh\qQ1[?O8O\B^4X^80^10'Bp+02;Q1]PcP~PdPeQ1XPgGDP3Q1]?OK4Q1[?OQh\qQ1_?O8O\B^4X^80^10'BP1f[R4?OQh\qQ1^?O8O\B^4X^80^10p+02?Q1`PcP~PdPeP4PgGDP3Q1_?OQh\qQ1a?O8O\B^4X^80^10PRf_S1[P?PZQ6HQ1`Q1hPsB0=|A3RBQ1h:0=|A60PEB0<|A3RqQ1h:0<|A+0W+0OXF\>0V\?#Rd80S?K0RPJQ1[PZP|e&1^RRhQ6H+0JCzPRQ1bP?PpQ1iQ1_Q6VPsQ6V:0=|A:0PEBQ6V:0<|A-0Wq+0OXF\>0V\?#Rd80S?K0RPJQ1bPpP|eQ1i-0JhCzPRQ1aP?P{Q6UQ1^Q6WPsQ6W:0=|A:0PEBQ6W:0<|A-0Wq+0OXF\>0V\?#Rd80S?K0RPJQ1aP{P|eQ6U-0JhCzp,4TIDRQ0|00uO:1]>NPJ&1\N,PIR>&1[NRh90J3XNJPJ&1ZN,PIR?A0J>3XNJ1eJ?Ph21YN3J0]fcR?00IpR>P6J0]A0J>hQ09Q0;Q0<POPXPM21XcdRMPPQ1eP?PLPQQ0YPNQ0jQ0pQ5{Q5zQ7vQ7uQ1@#u%uO+0?,vWQ7rQ7qb?b@bAQ1@/QOP3b>P2Q5{Q5z21W02Q7uPWQ06Q07Q07Q08Q6s#u21V0DRD+0?,vWQ07$0wQ7t00?D,vWL1UQ7rQ7qb?b@bAXM0Q6s/Q3%m2[^M0P3PLp+01KO2b>%mLeP_P<P=P7P3P6NI1SQ0DQ0DQ1d00>3PMfgRLg02WX,PIRWQ1cQ0:$1TRDPMP6Q0qQ1cPDDIPJP6Q0k1PI2ROQ0hQ0gP2AVXN3S0:Q0jDiRQD`R?FhX4X,aXX10#yPMQ1dPWQ1ePDPMP3Q0rQ1ePDDIEr'3'BW='aQ03Q0DQ0DQ1c00>3PMfhRPPWPLPDDIR>PMP6Q0qPLPDP?K0{X4X,aXX10#yPMQ1cPWQ1dPDPMP3Q0rQ1dPDDIEr'3'BW=p+02IQ1cPcP~PdPeQ1dPgGDP3Q0D20>P3PMQ1qPWQ1rPDPMP6Q0qQ1rPDDIP?FhX4X,aXX10#yP>PMP3Q0rPLPDJ0U'3'BP1Q1r00>2PMQ1pPWQ1qPDPMP8Q0qQ1qPDDIPJP8Q0kPOPQD`FhX4X,aXX10#yPMQ1rPWPPPDPMP2Q0rPPPDDIEr'3p+02MQ1qPcP~PdPeQ1rPgGDP3Q1p00>8PMQ1tPWQ1uPDPMP<Q0qQ1uPDDIPJP<Q0kPOPQD`FhX4X,aXX10#yPMQ7wPWQ1pPDPMP7Q0rQ1pPDDIEr'3g02XYRP:05|3S1pP8P2P|PoP2P|PmP2P|PnP2P|PFP2P|PrP2P|PTP2P|PvP2P|PGP2P|PpP2P|PZP2P|PHP2P|P{P2P|PuP2P|PUP2P|P}P2P|PtP2EMF2F2F2F2F2F2F2Q02A0|o6P|PmP6P|PnP6P|PFP6P|PrP6P|PTP6P|PvP6P|PGP6P|PpP6P|PZP6P|PHP6P|P{P6P|PuP6P|PUP6P|P}P6AH|t6F2F2F2F2F2F2F2A0|o8R>A0|m8S7wA0|n8S1uA0|F8S1qP|Q6A,LER?P8P|Q1?,LERhP8A0|r8S1?A0|T8S6AA0|v8S1cA0|G8S1eA0|p8S6sA0|Z8S7qA0|H8S7rA0|{8S7tA0|u8R\A0|U8RqA0|}8RAA0|t8RBP|Q6\,LER4P8P|Q6],LERKP8P|Q6^,LER[P8P|Q1A,LEREP8EMF2DADADAF2DAP3P|PoP|PoP3P|PmP3P|PnP3P|PFP3P|P?P3P|PhP3P|PrP3P|PTP3P|PvP3P|PGP3P|PpP3P|PZP3P|PHP3P|P{P3P|PuP3P|PUP3P|P}P3P|PtP3P|P4P3P|PKP3P|P[P3P|PEP3EMF2F2F2F2F2F2F2F2F2F2XE|RwA0|ooRVP|PmPoP|PnPoP|PFPoP|P?PoP|PhPoP|PrPoP|PTPoP|PvPoP|PGPoP|PpPoP|PZPoP|PHPoP|P{PoP|PuPoP|PUPoP|P}PoP|PtPoP|P4PoP|PKPoP|P[PoAH|EoF2F2F2F2F2F2F2F2F2F2R@P|PoCl13V@eP7P3EKX5>P3O1Q7wQ1uQ1qQ1?Q6AQ1cQ1eQ6sQ7qQ7rQ7tP\%tB9{qADADADAQ02A0|m7P|PnP7P|PFP7P|PrP7P|PTP7P|PvP7P|PGP7P|PpP7P|PZP7P|PHP7P|P{P7P|PuP7P|PUP7P|P}P7P|PtP7EMF2F2F2F2F2F2P|PoP=A0|m=RAA0|n=S7tA0|F=S7rP|P?P=P|PhP=A0|r=S7qA0|T=S6sA0|v=S1eA0|G=S1cA0|p=S6AA0|Z=S1?A0|H=S1qA0|{=S1uA0|u=S7wA0|U=S1AA0|}=RqA0|t=RBP|P4P=P|PKP=P|P[P=AH|E=F2E|DADAE^I0GE^P3P|PmPwA0|omR\A0|mmR>P|PnPmP|PFPmP|P?PmP|PhPmP|PrPmP|PTPmP|PvPmP|PGPmP|PpPmP|PZPmP|PHPmP|P{PmP|PuPmP|PUPmP|P}PmP|PtPmP|P4PmP|PKPmP|P[PmP|PEPmEMF2F2F2F2F2F2F2F2F2R@'3RVP>P@P|PmEo13\VeP<P3EKX5AP3O1Q7tQ7rQ7qQ6sQ1eQ1cQ6AQ1?Q1qQ1uQ7wQ1A1~qBDADADAQ02A0|n<P|PFP<P|PrP<P|PTP<P|PvP<P|PGP<P|PpP<P|PZP<P|PHP<P|P{P<P|PuP<P|PUP<P|P}P<AH|t<F2F2F2F2F2F2P|PoP;P|PmP;A0|n;RBA0|F;S1AP|P?P;P|PhP;A0|r;S7wA0|T;S1uA0|v;S1qA0|G;S1?A0|p;S6AA0|Z;S1cA0|H;S1eA0|{;S6sA0|u;S7qA0|U;S7rA0|};S7tA0|t;RqP|P4P;P|PKP;P|P[P;AH|E;F2E|DADAE^E|F2P3P|PnPwA0|onRAA0|mnS6^A0|nnRVP|PFPnP|P?PnP|PhPnP|PrPnP|PTPnP|PvPnP|PGPnP|PpPnP|PZPnP|PHPnP|P{PnP|PuPnP|PUPnP|P}PnP|PtPnP|P4PnP|PKPnP|P[PnAH|EnF2F2F2F2F2F2F2F2F2R\'3R@'3R>Q6^P@PVP\P|PnClD>13A>ePCP3EKX5BP3O1Q1AQ7wQ1uQ1qQ1?Q6AQ1cQ1eQ6sQ7qQ7rQ7t%tqDADADAQ02A0|FCP|PrPCP|PTPCP|PvPCP|PGPCP|PpPCP|PZPCP|PHPCP|P{PCP|PuPCP|PUPCP|P}PCP|PtPCEMF2F2F2F2F2P|PoP^P|PmP^P|PnP^A0|F^RqA0|?^P|PhP^A0|r^S7tA0|T^S7rA0|v^S7qA0|G^S6sA0|p^S1eA0|Z^S1cA0|H^S6AA0|{^S1?A0|u^RBA0|U^R>A0|}^RAA0|t^R\P|P4P^P|PKP^P|P[P^AH|E^F2E|DADAE^E^F2P3P|PFPwA0|oFRVA0|mFS1qA0|nFS1uA0|FFS7wP|P?PFP|PhPFP|PrPFP|PTPFP|PvPFP|PGPFP|PpPFP|PZPFP|PHPFP|P{PFP|PuPFP|PUPFP|P}PFP|PtPFP|P4PFP|PKPFP|P[PFP|PEPFEMF2F2F2F2F2F2F2F2S1A'3S6^'3S6]'3R@Q1qQ6]Q1uQ6^Q7wQ1AP|PFEoD>13V@eP_P3EKX5qP3O1Q7tQ7rQ7qQ6sQ1eQ1cQ6AQ1?1~A\9{B>DADAQ02A0|r_P|PTP_P|PvP_P|PGP_P|PpP_P|PZP_P|PHP_P|P{P_P|PuP_P|PUP_P|P}P_AH|t_F2F2F2F2F2P|PoP`P|PmP`P|PnP`P|PFP`P|P?P`P|PhP`A0|r`R>A0|T`S1?A0|v`S6AA0|G`S1cA0|p`S1eA0|Z`S6sA0|H`S7qA0|{`S7rA0|u`S7tA0|U`RBA0|}`R\A0|t`RAP|P4P`P|PKP`P|P[P`P|PEP`EMF2DADADAF2F2F2P3P|PrPwA0|orRqA0|mrS1AA0|nrS7wA0|FrS6^A0|?rS1uA0|hrS6]A0|rrS1qP|PTPrP|PvPrP|PGPrP|PpPrP|PZPrP|PHPrP|P{PrP|PuPrP|PUPrP|P}PrP|PtPrP|P4PrP|PKPrP|P[PrAH|ErF2F2F2F2F2F2F2S6\'3S07'3S08'3S06'3S7u'3R@'3RVQ1AP@Q7wQ7uQ6^Q06Q1uQ08Q6]Q07Q1qQ6\P|PrClD>D>D>13qVePaP3EKX5>P3O1Q1?Q6AQ1cQ1eQ6sQ7qQ7rQ7t%tA9{B\DADAQ02A0|TaP|PvPaP|PGPaP|PpPaP|PZPaP|PHPaP|P{PaP|PuPaP|PUPaP|P}PaP|PtPaEMF2F2F2F2P|PoPfP|PmPfP|PnPfP|PFPfP|P?PfP|PhPfP|PrPfA0|TfR\A0|vfS7tA0|GfS7rA0|pfS7qA0|ZfS6sA0|HfS1eA0|{fS1cA0|ufS6AA0|UfS1?A0|}fRBA0|tfRAP|P4PfP|PKPfP|P[PfAH|EfF2I0GDADAE^F2F2F2P3P|PTPwA0|oTR>A0|mTS6\A0|nTS1qA0|FTS07A0|?TS6]A0|hTS08A0|rTS1uA0|TTS06P|PvPTP|PGPTP|PpPTP|PZPTP|PHPTP|P{PTP|PuPTP|PUPTP|P}PTP|PtPTP|P4PTP|PKPTP|P[PTP|PEPTEMF2F2F2F2F2F2S6^'3S7u'3S7w'3S1A'3S5z'3RV'3Rq'3R@Q6\PqQ1qPVQ07Q5zQ6]Q1AQ08Q7wQ1uQ7uQ06Q6^P|PTEoD>D>D>13>@eQ0pP3EKX5\P3O1Q7tQ7rQ7qQ6sQ1eQ1cQ6AQ1?1~BADADAQ02Q0p90|vP|PGQ0pP|PpQ0pP|PZQ0pP|PHQ0pP|P{Q0pP|PuQ0pP|PUQ0pP|P}Q0pQ0p9H|tF2F2F2F2P|PoPSP|PmPSP|PnPSP|PFPSP|P?PSP|PhPSP|PrPSP|PTPSA0|vSRAA0|GSS1?A0|pSS6AA0|ZSS1cA0|HSS1eA0|{SS6sA0|uSS7qA0|USS7rA0|}SS7tA0|tSRBP|P4PSP|PKPSP|P[PSAH|ESF2E|DADAF2F2F2F2P3P|PvPwA0|ovRSA0|mvS6^A0|nvS06A0|FvS7uA0|?vS1uA0|hvS7wA0|rvS08A0|TvS1AA0|vvS6]P|PGPvP|PpPvP|PZPvP|PHPvP|P{PvP|PuPvP|PUPvP|P}PvP|PtPvP|P4PvP|PKPvP|P[PvAH|EvF2F2F2F2F2F2S5z'3S07'3S1q'3S6\'3R\'3R@'3R>'3RV'3RqQ6^PVQ06P>Q7uP@Q1uP\Q7wQ6\Q08Q1qQ1AQ07Q6]Q5zP|PvClD>D>D>D>13SqeQ1PP3EKX5AP3O1Q1?Q6AQ1cQ1eQ6sQ7qQ7rQ7t%tBDADAQ02Q1P90|GP|PpQ1PP|PZQ1PP|PHQ1PP|P{Q1PP|PuQ1PP|PUQ1PP|P}Q1PP|PtQ1PEMF2F2F2P|PoPiP|PmPiP|PnPiP|PFPiP|P?PiP|PhPiP|PrPiP|PTPiP|PvPiA0|GiRBA0|piS7tA0|ZiS7rA0|HiS7qA0|{iS6sA0|uiRAA0|UiRqA0|}iRSA0|tiR\A0|4iP|PKPiP|P[PiAH|EiF2DADAE^F2F2F2F2P3P|PGPwA0|oGR@A0|mGS1eA0|nGS1cA0|FGS6AA0|?GS1?A0|hGS5zA0|rGS6]A0|TGS07A0|vGS1AA0|GGS1qP|PpPGP|PZPGP|PHPGP|P{PGP|PuPGP|PUPGP|P}PGP|PtPGP|P4PGP|PKPGP|P[PGP|PEPGEMF2F2F2F2F2S08'3S6\'3S7w'3S1u'3S7u'3S06'3S6^'3S5{'3R>'3RVQ1eP>Q1cQ5{Q6AQ6^Q1?Q06Q5zQ7uQ6]Q1uQ07Q7wQ1AQ6\Q1qQ08P|PGEoD>D>D>D>13@VeQ1OP3EKX5BP3O1Q7tQ7rQ7qQ6s1~S\9{AqDAQ02Q1O90|pP|PZQ1OP|PHQ1OP|P{Q1OP|PuQ1OP|PUQ1OP|P}Q1OQ1O9H|tF2F2F2P|PoP]P|PmP]P|PnP]P|PFP]P|P?P]P|PhP]P|PrP]P|PTP]P|PvP]P|PGP]A0|p]RqA0|Z]S1OA0|H]S6sA0|{]S7qA0|u]S7rA0|U]RAA0|}]R\A0|t]RSP|P4P]P|PKP]P|P[P]P|PEP]EMF2DADAF2F2F2F2F2P3P|PpPwA0|opRBA0|mpS7tA0|npS08A0|FpS1qA0|?pS6\A0|hpS1AA0|rpS7wA0|TpS07A0|vpS1uA0|GpS6]A0|ppS7uP|PZPpP|PHPpP|P{PpP|PuPpP|PUPpP|P}PpP|PtPpP|P4PpP|PKPpP|P[PpAH|EpF2F2F2F2F2S5z'3S06'3S1?'3S6^'3S6A'3S5{'3S1c'3S1e'3RV'3R@'3R>Q7tP@Q08PVQ1qQ1eQ6\Q1cQ1AQ5{Q7wQ6AQ07Q6^Q1uQ1?Q6]Q06Q7uQ5zP|PpClD>D>D>D>D>13B>eQ1QP3EKX5qP3O1Q1OQ6sQ7qQ7r%tS9{A\DAQ02Q1Q90|ZP|PHQ1QP|P{Q1QP|PuQ1QP|PUQ1QP|P}Q1QP|PtQ1QEMF2F2P|PoPjP|PmPjP|PnPjP|PFPjP|P?PjP|PhPjP|PrPjP|PTPjP|PvPjP|PGPjP|PpPjA0|ZjR\A0|HjS7rA0|{jS7qA0|ujS6sA0|UjS1OA0|}jRAA0|tjRSP|P4PjP|PKPjP|P[PjAH|EjF2I0GDAE^F2F2F2F2F2P3P|PZPwA0|oZRqA0|mZS5zA0|nZS7uA0|FZS06A0|?ZS6]A0|hZS1?A0|rZS1uA0|TZS6^A0|vZS07A0|GZS6AA0|pZS7wA0|ZZS5{P|PHPZP|P{PZP|PuPZP|PUPZP|P}PZP|PtPZP|P4PZP|PKPZP|P[PZP|PEPZEMF2F2F2F2S1A'3S1c'3S6\'3S1e'3S1q'3S08'3S7t'3S1@'3R>'3RB'3RV'3R@Q5zPVQ7uPBQ06P>Q6]Q1@Q1?Q7tQ1uQ08Q6^Q1qQ07Q1eQ6AQ6\Q7wQ1cQ5{Q1AP|PZEoD>D>D>D>D>13q@eQ0oP3EKX5\P3O1Q7rQ7qQ6sQ1O1~ASDAQ02Q0o90|HP|P{Q0oP|PuQ0oP|PUQ0oP|P}Q0oQ0o9H|tF2F2P|PoP9P|PmP9P|PnP9P|PFP9P|P?P9P|PhP9P|PrP9P|PTP9P|PvP9P|PGP9P|PpP9P|PZP9A0|H9RSA0|{9S0oA0|u9S1OA0|U9S6sA0|}9S7qA0|t9RAP|P4P9P|PKP9P|P[P9AH|E9F2E|DAF2F2F2F2F2F2P3P|PHPwA0|oHR\A0|mHS7rA0|nHS1AA0|FHS5{A0|?HS1cA0|hHS7wA0|rHS6\A0|THS6AA0|vHS1eA0|GHS07A0|pHS1qA0|ZHS6^A0|HHS08P|P{PHP|PuPHP|PUPHP|P}PHP|PtPHP|P4PHP|PKPHP|P[PHAH|EHF2F2F2F2S1u'3S7t'3S1?'3S1@'3S6]'3S06'3S7u'3S5z'3R@'3Rq'3R>'3RB'3RVQ7rPBQ1AP>Q5{PqQ1cP@Q7wQ5zQ6\Q7uQ6AQ06Q1eQ6]Q07Q1@Q1qQ1?Q6^Q7tQ08Q1uP|PHClD>D>D>D>D>D>13\VeQ1SP3EKX5SP3O1Q0oQ1OQ6sQ7q%tADAQ02Q1S90|{P|PuQ1SP|PUQ1SP|P}Q1SP|PtQ1SEMF2P|PoPbP|PmPbP|PnPbP|PFPbP|P?PbP|PhPbP|PrPbP|PTPbP|PvPbP|PGPbP|PpPbP|PZPbP|PHPbA0|{bRAA0|ubRSA0|UbRVA0|}bR\A0|tbR@A0|4bP|PKPbP|P[PbAH|EbF2DAE^F2F2F2F2F2F2P3P|P{PwA0|o{RqA0|m{S1SA0|n{S7qA0|F{S6sA0|?{S1OA0|h{S0oA0|r{S1uA0|T{S08A0|v{S7tA0|G{S6^A0|p{S1?A0|Z{S1qA0|H{S1@A0|{{S07P|PuP{P|PUP{P|P}P{P|PtP{P|P4P{P|PKP{P|P[P{P|PEP{EMF2F2F2S6]'3S1e'3S06'3S6A'3S7u'3S6\'3S5z'3S7w'3S1c'3S5{'3S1A'3S7r'3R>'3RBQ1SP>Q7qQ7rQ6sQ1AQ1OQ5{Q0oQ1cQ1uQ7wQ08Q5zQ7tQ6\Q6^Q7uQ1?Q6AQ1qQ06Q1@Q1eQ07Q6]P|P{EoD>D>D>D>D>D>13qBeQ1RP3EKX5AP3O11~\@9{SVQ02Q1R90|uP|PUQ1RP|P}Q1RQ1R9H|tF2P|PoP5P|PmP5P|PnP5P|PFP5P|P?P5P|PhP5P|PrP5P|PTP5P|PvP5P|PGP5P|PpP5P|PZP5P|PHP5P|P{P5A0|u5RVA0|U5RSA0|}5R@A0|t5R\P|P4P5P|PKP5P|P[P5P|PEP5EMF2DAF2F2F2F2F2F2F2P3P|PuPwA0|ouRAA0|muS6]A0|nuS07A0|FuS1eA0|?uS1@A0|huS06A0|ruS1qA0|TuS6AA0|vuS1?A0|GuS7uA0|puS6^A0|ZuS6\A0|HuS7tA0|{uS5zA0|uuS08P|PUPuP|P}PuP|PtPuP|P4PuP|PKPuP|P[PuAH|EuF2F2F2S7w'3S1u'3S1c'3S0o'3S5{'3S1O'3S1A'3S6s'3S7r'3S7q'3S1S'3S7v'3RB'3Rq'3R>Q6]PqQ07PBQ1eQ7vQ1@Q1SQ06Q7qQ1qQ7rQ6AQ6sQ1?Q1AQ7uQ1OQ6^Q5{Q6\Q0oQ7tQ1cQ5zQ1uQ08Q7wP|PuClD>D>D>D>D>D>D>13A>eQ1UP3EKX5VP3O1%t\9{S@Q02Q1U90|UP|P}Q1UP|PtQ1UEMP|PoPkP|PmPkP|PnPkP|PFPkP|P?PkP|PhPkP|PrPkP|PTPkP|PvPkP|PGPkP|PpPkP|PZPkP|PHPkP|P{PkP|PuPkA0|UkR@A0|}kRSA0|tkR\P|P4PkP|PKPkP|P[PkAH|EkF2I0GE^F2F2F2F2F2F2F2P3P|PUPwA0|oURkA0|mUS7wA0|nUS08A0|FUS1uA0|?US5zA0|hUS1cA0|rUS7tA0|TUS0oA0|vUS6\A0|GUS5{A0|pUS6^A0|ZUS1OA0|HUS7uA0|{US1AA0|uUS1?A0|UUS6sP|P}PUP|PtPUP|P4PUP|PKPUP|P[PUP|PEPUEMF2F2S6A'3S7r'3S1q'3S7q'3S06'3S1S'3S1@'3S7v'3S1e'3S07'3S6]'3RV'3R>'3RA'3RB'3RqQ7wPBQ08PAQ1uP>Q5zPVQ1cQ6]Q7tQ07Q0oQ1eQ6\Q7vQ5{Q1@Q6^Q1SQ1OQ06Q7uQ7qQ1AQ1qQ1?Q7rQ6sQ6AP|PUEoD>D>D>D>D>D>D>13kqeQ1TP3EKX5@P3O11~S\Q02Q1T90|}Q1T9H|tP|PoPyP|PmPyP|PnPyP|PFPyP|P?PyP|PhPyP|PrPyP|PTPyP|PvPyP|PGPyP|PpPyP|PZPyP|PHPyP|P{PyP|PuPyP|PUPyA0|}yR\A0|tyRSP|P4PyP|PKPyP|P[PyAH|EyF2E|F2F2F2F2F2F2F2F2P3P|P}PwA0|o}RyA0|m}S1TA0|n}S6AA0|F}S6sA0|?}S7rA0|h}S1?A0|r}S1qA0|T}S1AA0|v}S7qA0|G}S7uA0|p}S06A0|Z}S1OA0|H}S1SA0|{}S6^A0|u}S1@A0|U}S5{A0|}}S7vP|PtP}P|P4P}P|PKP}P|P[P}AH|E}F2F2S6\'3S1e'3S0o'3S07'3S7t'3S6]'3S1c'3S5z'3S1u'3S08'3R@'3Rq'3Rk'3RV'3R>'3RA'3RBQ1TPAQ6AP>Q6sPVQ7rPkQ1?PqQ1qP@Q1AQ08Q7qQ1uQ7uQ5zQ06Q1cQ1OQ6]Q1SQ7tQ6^Q07Q1@Q0oQ5{Q1eQ7vQ6\P|P}ClD>D>D>D>D>D>D>D>13yBeQ1WP3EKX5\P3O1%tSQ02Q1W90|tQ0=P|PoPlP|PmPlP|PnPlP|PFPlP|P?PlP|PhPlP|PrPlP|PTPlP|PvPlP|PGPlP|PpPlP|PZPlP|PHPlP|P{PlP|PuPlP|PUPlP|P}PlA0|tlRSA0|4lP|PKPlP|P[PlAH|ElF2E^F2F2F2F2F2F2F2F2P3P|PtPwA0|otRwA0|mtS1WA0|ntS6\A0|FtS7vA0|?tS1eA0|htS5{A0|rtS0oA0|TtS1@A0|vtS07A0|GtS6^A0|ptS7tA0|ZtS1SA0|HtS6]A0|{tS1OA0|utS1cA0|UtS06A0|}tS5zA0|ttS7uP|P4PtP|PKPtP|P[PtP|PEPtEMF2S1u'3S7q'3S08'3S1A'3S1q'3S1?'3S7r'3S6s'3Rl'3R\'3RB'3Ry'3R@'3Rq'3Rk'3RV'3R>'3RAQ1WP>Q6\PVQ7vPkQ1ePqQ5{P@Q0oPyQ1@PBQ07P\Q6^PlQ7tQ6sQ1SQ7rQ6]Q1?Q1OQ1qQ1cQ1AQ06Q08Q5zQ7qQ7uQ1uP|PtEoD>D>D>D>D>D>D>D>13wAeQ1VP3EKX5SP3O1Q0=Q0=P|PoPzP|PmPzP|PnPzP|PFPzP|P?PzP|PhPzP|PrPzP|PTPzP|PvPzP|PGPzP|PpPzP|PZPzP|PHPzP|P{PzP|PuPzP|PUPzP|P}PzP|PtPzP|P4PzP|PKPzP|P[PzP|PEPzEMF2F2F2F2F2F2F2F2F2F2P3n010000100W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n200100001021100011000W3P3O1n201100001021100011000W3P3O1n201100001021100011000W3P3O1n201100001021100011000W3P3O1n201100001021100011000W3P3O1n201100001021100011000W3P3O1n201100001021100011000W3P3O1n201100001021100011000W3P|PoP|PmP|PnP|PFP|PrP|PTP|PvP|PGP|PpP|PZP|PHP|P{P|PuP|PUP|P}P|Pt%U|RzD1D1D1D1D1D1D1D1:05|2P|PoP|PmP|PnP|PFP|P?P|PhP|PrP|PTP|PvP|PGP|PpP|PZP|PHP|P{P|PuP|PUP|P}P|PtP|P4P|PKP|P[P|PEPzD1D1D1D1D1D1D1D1D1D1D1:05|6]3eB05|2Pg02YS:05|6]3eP3O1O2W3XE|Q1pPJP;P2Q1s00I2Cz[^E|PRQ1tP<Q0lPPQ1UPsQ0l-1NP#RdP3L1mQ0mQ02PMQ5~PWQ60PDDIRPPMP^Q0qQ60PDPJP^Q0kPOPQD`K0{X4X,aXX10#yPMQ1sPWQ1tPDPMP;Q0rQ1tPDDIErp+02SQ60PcP~PdPeQ1sPgGDP6PMQ5}PWQ5~PDPMP_Q0qQ5~PDDIPJP_Q0kPOPQD`FhX4X,aXX10#yQ03P0PMfsR;PWQ5}PDPMP`Q0qQ5}PDDIPJP`Q0kPOPQD`FhX4X,aXX10p+02UQ5}PcP~PdPeQ5~PgGDP3PMfuRsPWftR<PDPMPfQ0qP<PDDIPJPfQ0kPOPQD`FhX4X,aXQ03PXPMfvRQPWPsPDPMQ0pQ0qPsPDDIPJQ0pQ0k1PI6Q0hQ0gP6Q0:Q0jDiD`FhX4Xp+02YPQPcP~PdPePsPgGDP3PMQ87PWQ86PDPMQ1PQ0qQ86PDDIPJQ1PQ0k1PI7Q0hQ0gP7Q0:Q0jDiD`FhP1PMfyRQPWQ87PDPMPiQ0qQ87PDDIErPJPiQ0k1PI=Q0hQ0gP=Q0iQ0jDiD`p+02]fzRiPcP~PdPePQPgGDP3PMf{PWPiPDPMP]Q0qPiPDDIErPJQ1QQ0k1PICQ0hQ0gPCAVXN7Q0jDiD`P1PJPjQ0k1PI^CzQ0hQ0gP^AVXN=Q0jDip+02af~R1PcP~PdPef}PgGDP3PJP9Q0k1PI`CzQ0hQ0gPaAVXNCQ0jDiQ0>PMp+01BRNPWQ8;PDDIQ0>PMQ1RQ0qPNPDDIRI-033WBP=PNPcPWPdPeQ8;PDFjR9PcPdPNPWQ8;PDJ0KEKP9PMPbQ0qQ8;PDJ0UQ0>PIQ0>p+01DRIPcPWPdPep+01CRbPDFj0033WBP3Q1RPcQ0qPdPePNPDFjR9PcPdQ1RQ0qPNPDJ0KEKPbPcPWPdPePNPDFj0039P:p+02fPIPcPdP~PbPgP5Q0qPbP3PN&0L5p+02\Q1UPIQ1PPaP3P8P7PjPsQ1sQ1rp+01@P1PLQ1dO?WKN>0zb9b9WrWTP2P3O2n2001000000121000000W0W9P2P3O2n2001000000121000000W0X4XP2P3O2n2001000000121100000W0X10P2P3O2n2001000000121100000W0P3O1PMQ60PWQ1sPDPMPCQ0rQ1sPDDIErQ0>PPQ0>PMP_Q0rQ5~PDDIRP-033WBP3Q5~PcPWPdPeQ60PDFjRCPcPdQ5~PWQ60PDJ0KEKPCPMP^Q0rQ60PDJ0UQ0>PPQ0>P;PcPWPdPeQ5}PDFj0033WBP3P_PcQ0rPdPeQ5~PDFjRPPcPdP_Q0rQ5~PDJ0KEKQ5}PcPWPdPeQ5~PDFj003PP:p+02VP;PcPdP~Q5}PgP`Q0rQ5}P3Q5~&0L`p+02KPaP;P3P=Q1dQ1[Q1\Q1sQ1tQ1XQ1YO;WKN>0zb9b9W9P3O1n200100000021100011000bnbuW[WRP2P3O2n2001000000121000000W0Y09P2P3O2n2001000000121100000c0EbWc0@bYbVbXWZWUP2P3O2n2001000000121000000W0WSP2P3O2n2001000000121000000W0Y0AP2P3O2n2001000000121000000bDbGbCbGbvbJbjPYQ1UPcPxPdPeP5PgGDeW7WaP2P3O2n2101000010121000000b7b0W7W^P2P3O2n2111000010121000000b7b0W7WqP2P3O2n2111000010121000000b7b0b7bCY0CWJWdWgW7WmY0<Y0HY08NS0ybIbiQ66Q1UPcQ7TPdPeP5PgGDeW6W`P2P3O2n2101000010121000000b6b0W6W]P2P3O2n2111000010121000000b6b0W6WpP2P3O2n2111000010121000000b6b0b6bCY0BWIWcWfW6WlY0;Y0GY07NS0yY0?Y0>P2P3O2n2001000000121000000W0Y0=P2P3O2n2001000000121000000b0WzWyP2P3O2n2001000000121000000W0WxP2P3O2n2001000000121000000W0Y04P2P3O2n2001000000121000000W0Y03P2P3O2n2001000000121000000W0Y02P2P3O2n2001000000121000000W0Y01P2P3O2n2011000000121000000W0W~P2P3O2n2011000000121000000W0W}P2P3O2n2011000000121000000W0W|P2P3O2n2011000000121000000W0W{P2P3O2n2011000000121000000W0WwP2P3O2n2011000000121000000b0WtWsWhWbWeW_W\WoWkY0:Y0FY06Y05o"). Qed.
End SnA.
