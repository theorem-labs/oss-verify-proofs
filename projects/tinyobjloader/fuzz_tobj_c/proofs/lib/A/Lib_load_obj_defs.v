(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "false"; "length"; "andb"; "app"; "list"; "option"; "S"; "None"; "bool"; "negb"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SPUle"; "sobj"; "cell"; "SAlu"; "mkObj"; "SVar"; "ss_objs"; "DUnknown"; "SPAlign"; "sv_eqb"; "ob_base"; "mkCell"; "ob_hi"; "ob_lo"; "odefault"; "FcsrFrm0"; "SPBranch"; "mkSS"; "sstate"; "DZero"; "ob_cells"; "ob_dflt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "sym_runA"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXRebase"; "AXSplit"; "AXMerge"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vDp"; "vBUF"; "vCFGp"; "vOUT"; "Pre_ms"; "optL"; "vLEN"; "find_idxb"; "FUEL_lo"; "idxB"; "sel2last"; "vF"; "vNBP"; "BAD"; "E_f8a"; "E_ma"; "E_mo1"; "E_mz"; "E_sm0"; "L_ms"; "NP"; "O_Dlo"; "O_Flo"; "O_cfg"; "O_lnk"; "O_out"; "O_txtL"; "Pre_f8"; "Pre_lo"; "Pre_ma"; "Pre_sm"; "R_of"; "W2"; "X_lits17"; "bslot"; "cfg_cells"; "idxC"; "ilast"; "lo_facts"; "objs_lo"; "optR"; "optS"; "sel_last"; "vFL"; "vRAF"; "z24"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs.LOAddr"; "FR"; "DW"; "lo_entry"; "lo_ret"; "memcpy_pc"; "memset_pc"; "sf5_pc"; "sm5_pc"; "ss00_pc"; "ssf8_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "AE_A"; "Pre_malloc"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "c8"; "spm"; "two47"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "leb"; "ltb"; "pow"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "seq"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "A_globals"; "SHB"; "leavesA_at"; "mkA"; "segs"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double.ScanDoubleAddr"; "pow10_tab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.RA.ReallocAddr"; "malloc_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA"; "zero_cells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@Stdlib.Lists.List"; "filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr VRAddr RA.ReallocAddr.

Module LOAddr.
  Definition lo_entry : Z := 0x8c894.
  Definition lo_ret : Z := 0x8e988.
  Definition sm5_pc : Z := 0x47f54.
  Definition sf5_pc : Z := 0x48160.
  Definition ssf8_pc : Z := 0x603a8.
  Definition ss00_pc : Z := 0x60288.
  Definition memset_pc : Z := 0x5cce8.
  Definition memcpy_pc : Z := 0x5c84c.
  Definition FR : Z := 512.
  Definition DW : Z := 6144.
End LOAddr.
Import LOAddr.

Definition NP : positive := 100%positive.
Definition vOUT : sv := SVar 12. Definition vBUF : sv := SVar 13. Definition vLEN : sv := SVar 14. Definition vCFGp : sv := SVar 15.
Definition vDp : sv := SVar 19.

Definition vF : sv := SVar 110. Definition vFL : sv := SVar 120. Definition g5 : positive := 140%positive.

Definition O_Flo (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S17S18PaA1S11S7dS6aA1A1S11Z0A1Vcells;S1aA5").
Definition O_Dlo : sobj := ltac2:(tb__ "0|0|
S17S7aS6aA1S38S11Z0A1S2S15A1S1aA5").
Definition O_out (cells : list cell) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S17S3bS11Z0A1S11Zd0A1Vcells;Vd;A5").
Definition O_txtL : sobj := ltac2:(tb__ "0|0|
S17S39S11Z0A1S3eS2S15A1S1aA5").

Definition vNBP : sv := SVar 16. Definition vRAF : sv := SVar 17.
Definition O_lnk : sobj := ltac2:(tb__ "0|1|
S17S18P1cA1S11N10M0A1S11Z0A1S0S15S79G0S44A2S0S15S79N8S64A2S2S15A1A3A3S1aA5").
Definition cfg_cells : list cell := ltac2:(tb__ "0|1|
S0S15S1eS11Z30A1Z2S11Z101A1A3S0S15S1eS11Z32A1Z1M0S11G0A1A3S0S15S1eS11Z38A1Z4S11ZffffffffA1A3S2S15A1A3A3A3").
Definition O_cfg : sobj := ltac2:(tb__ "0|0|
S17S3aS11Z0A1S11Z90A1S5bS26A5").

Definition lo_facts : list sprop := ltac2:(tb__ "0|c|
S0S12S1bPaM0Z5M1A2S0S12S13S18G0A1M2S11S7bA1M3A2S0S12S13S16S66S18P1eA1M4S11S7cS6aS6bA2M5A1A3G2A2S0S12S13G4S16S66S7aS6aA1M6S38A3A2S0S12S13G4S7aG5A1A2S0S12S13G4G6A2S0S12S13G4G2A2S0S12S23S67S11S7dS6bA1A1S38A3S0S12S23S67S38S11S7dS80Z2Z26A2A1A1A3S0S12S1bPcZ3A2S0S12S13G4S3bA2S0S12S13S16S66S3bS11Z138A1A3G3A2S0S12S13S3bG3A2S0S12S1bPdZ4M7A2S0S12S13S11Z1000A1S39A2S0S12S13S16S66S39S3eA3S11Z7fffff800000A1M8A2S0S12S13S39G8A2S0S12S13S39G3A2S0S12S13S3eS11S8eA1A2S0S12S1bPfG1A2S0S12S13S11S97A1S3aA2S0S12S13S16S66S3aS11Z90A1A3G4A2S0S12S13S3aG3A2S0S12S1bP1cM9G7A2S0S12S13S16S66G2S11Z10A1A3S18G9A1MaA2S0S12S13GaG3A2S0S12S13S44GaA2S0S12S13S11Z7fff7f800000A1MbG4A2S0S12S13G4G8A2S0S12S13GbG2A2S2S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition X_lits17 : list (sv * sv) := Eval vm_compute in removelast OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface.X_lits.
Definition X_lo : list (sv * sv) := ltac2:(tb__ "0|2|
S8S3S10S10A2M0S0G0S1S10S10S3bS11Zd0A1A4S0G0S1S10S10S39S3eA4S0G0S1S10S10S3aS11Z90A1A4S0G0S1S10S10S11S8dA1S11Zb8A1A4S0G0S1S10S10S7aS7cS6aS6bA2M1A1S11G1A1A4S2G0A1A3A3A3A3A3S59A3").
Definition objs_lo : list sobj := ltac2:(tb__ "0|1|
S8S14S0S14S4eS2S15A1M0A1S0S14S4dS0S14S51G0S1aA2S0S14S52S0S14S4fS0S14S50S2S14A1A3A3A3A3A3A3S87A3").
Definition Pre_lo_S : sstate := ltac2:(tb__ "0|1|
S24S6cS94S93S0S3S4S10A2M0S1S4S10UdS3aA4S0G0S1S4S10UeS11Z0A1A4S2G0A1A3A3A2S92S22ScS10A1S5fS5eS4cS5A9").
Definition Pre_lo : axst := mkA Pre_lo_S X_lo.

Definition FUEL_lo : nat := 3000%nat.
Definition cps_pro : list Z := ltac2:(tb__ "0|0|
S0S2fS71S0S2fS70S0S2fS73S0S2fS72S0S2fS6fS0S2fS6eS0S2fS8fS0S2fS6dS2S2fA1A3A3A3A3A3A3A3A3").
Definition optL (x : option axst) : axst := match x with Some s => s | None => Pre_lo end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leafL_at (cuts : list Z) (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S84S2aVk;S89S40Vcuts;VS;Vpc;A4S54A4").
Definition showrun (cuts : list Z) (S : axst) : ltac2:(tb__ "0|0|
S9S3S2fS85A2A1") := ltac2:(tb__ "0|2|
SaS9S2cA1M0A1S9S3S2fS85A2M1A1Lx;S2dS8bS40Vcuts;VS;SfA5G0S83S2cG1S8cR1A4Lls;S2G1A1Xax2").

Definition BAD : axst := ltac2:(tb__ "0|1|
S8aS24Z0S2S10A1M0G0S22ScS10A1S2S14A1S2S12A1P1S5A9S2S3S10S10A2A1A2").
Definition ilast (A : axst) : nat := ltac2:(tb__ "0|0|
S81S6S14S19S29VA;A1A1A2U1A2").
Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S8S4S82U0Vi;A2S8S4S82SbVi;A1M0S81S6S14S19S29VA;A1A1A2G0A2A2S0S4Vi;S2S4A1A3A3A3").
Definition objs_butlast (A : axst) : list sobj := removelast (ss_objs (ax_S A)).
Fixpoint find_idxb {T} (f : T -> bool) (l : list T) (k : nat) : nat :=
  match l with [] => k | x :: r => if f x then k else find_idxb f r (S k) end.

Definition idxB (A : axst) (b : sv) (lo : Z) : nat := ltac2:(tb__ "0|0|
S3fS14S14S7S1cS1dR1A1Vb;A2S1cS20R1A1S11Vlo;A1A2A2Lo;S19S29VA;A1A1U0A4").
Definition idxC (A : axst) (b : sv) (off : Z) : nat := ltac2:(tb__ "0|7|
S3fS14S14S7S1cS1dR1A1Vb;A2S10SdLx;M0S20R1A1S2fG0S1fR2A1S2fS7S7eR2Voff;A2S7fVoff;R1A2A2Lh;S2eS5Li;M1S68S10S10S5Lb0;La;M2Lop;M3G3S69G2Lop;M4G4SdS30S10S5La;Lw;Lsgn;M5S2eS10S2fS5Lk;Li;M6Ll0;X10x8Ll;G1G3G3G4G4G5S2eG6Ll;X10x8A2Lo;S19S29VA;A1A1U0A4").
Definition idxF (A : axst) : nat := idxB A (SVar 110) 0.
Definition sel2last (A : axst) (i j : nat) : list nat := ltac2:(tb__ "0|0|
S8S4S98S4S4S7SeS86R1Vi;A2A1SeS86R1Vj;A2A1A2Lk;S82U0S6S14S19S29VA;A1A1A2A2A3S0S4Vi;S0S4Vj;S2S4A1A3A3A3").
Definition optS (A : axst) (x : option sstate) : axst := ltac2:(tb__ "0|0|
SaS25A1S2aLx;Vx;S25S2bVA;R1A2LS1;S45Xax2").
Definition shapes (A : axst) : ltac2:(tb__ "0|0|
S9S3S3S3S3S10S10A2S10A2S21A2S4A2A1") := ltac2:(tb__ "0|3|
S83S14S3S3S3S3S10S10A2M0S10A2M1S21A2M2S4A2S14S1G2S4S1G1S21S1G0S10S1S10S10S1dR1A1S20R1A1A4S1fR1A1A4S28R1A1A4S6S15S27R1A1A2A4Lo;S19S29VA;A1A1A4").
Definition fpiece (lo hi : Z) (cells : list cell) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S17S18P6eA1S11Vlo;A1S11Vhi;A1Vcells;Vd;A5").
Definition fslot (lo n : Z) (cells : list cell) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S17S16S66S18P6eA1S11Vlo;A1A3S11Z0A1S11Vn;A1Vcells;Vd;A5").

Definition bslot (b : sv) (off n : Z) : sobj := ltac2:(tb__ "0|0|
S17S16S66Vb;S11Voff;A1A3S11Z0A1S11Vn;A1S2S15A1S1aA5").
Definition ms_carve (E0 : axst) (b : sv) (off n : Z) : axst := ltac2:(tb__ "0|0|
S5cVE0;Vb;Voff;A3S4S3dS32VE0;S0S31S35R1S11Voff;A1A2S0S31S35SbR1A1S11S7cVoff;Vn;A2A1A2S2S31A1A3A3A2A1S2aS2bR1S91S29R1A1SbR2A1S5aVb;Voff;Vn;A3A3A2TE1;Ti;").
Definition Pre_ms : axst := Pre_memset memset_pc.
Definition L_ms : axst := L_memset (ae_ret_asan_memset AE_A).
Definition s_msx (E : axst) (xb xn : sv) : wsub := ltac2:(tb__ "0|1|
S0S3S2eS10A2M0S1S2eS10P35Vxb;A4S0G0S1S2eS10P36Vxn;A4S0G0S1S2eS10S75S38A4S74PaS29VE;A1S29S3cA1A3A3A3A3").
Definition R_of (E : axst) (P : axst) (s : wsub) : list sobj := ltac2:(tb__ "0|0|
S60S90VE;VP;Vs;A3A1").
Definition ms_T0 (E : axst) (s : wsub) : axst := ltac2:(tb__ "0|0|
S96S3cVE;Vs;S57VE;S3cVs;A3S4bA5").

Definition z24 : list cell := ltac2:(tb__ "0|2|
S0S15S79Z0M0S11G0A1M1A2S0S15S79Z8G1A2S0S15S79Z10G1A2S2S15A1A3A3A3").
Definition ms_back24 (T0 : axst) (b : sv) (off : Z) : axst := ltac2:(tb__ "0|4|
S61VT0;S95S29VT0;A1U1M0S65A3A2S2aS3dS32R1S0S31S34G0A1S2S31A1M1A3A2A1S2aS3fS14S14S7S1cS1dR1A1Vb;A2S1cS1fR1A1S11Voff;A1A2A2Lo;S19S29R1A1A1M2U0A4S4S3dS32R2S0S31S33S42R2R1G0A3A1G1A3A2A1S2aS41R1Vb;S7cVoff;Z18A2A3S4S3dS32R2S0S31S33S42R2S81S6S14S19S29R2A1A1A2G0A2R1A3A1G1A3A2A1S2aS6S14G2A2S4S3dS32R2S0S31S36S81R1U3A2A1M3S0S31G3G1A3A3A2A1Tn;TT4;TiR;TT3;TiL;TT2;TT1;").

Definition E_sm0 : axst := Eval vm_compute in leafL_at cps_pro Pre_lo sm5_pc 0.
Definition Pre_sm : axst := Pre_stack_malloc AE_A 5.
Definition L_sm : axst := L_stack_malloc AE_A 5.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S0S3S2eS10A2S1S2eS10S75S38A4S74PaS29S4aA1S29S56A1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Definition T_sm : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.

Definition fr_lo : list (sv * Z * sv) := ltac2:(tb__ "0|2|
S0S3S3S10S2fA2M0S10A2M1S1G0S10S1S10S2fS43Z5A4S63A4S2G1A1A3").
Definition T_sm1 : axst := Eval vm_compute in optL (apply_axforms T_sm [AXSelect (sel_last T_sm 3)]).
Definition C_pro0 : axst := Eval vm_compute in frame_open_stateA T_sm1 (objs_butlast T_sm1) X_lo 110 2048.
Definition C_pro : axst := Eval vm_compute in ax_setX C_pro0 ((vF, SLit 0) :: ax_X C_pro0).

Definition Pre_f8 : axst := Pre_set_shadow AE_A 248.
Definition L_f8 : axst := L_set_shadow 248.
Definition Pre_00 : axst := Pre_set_shadow AE_A 0.
Definition L_00 : axst := L_set_shadow 0.
Definition E_f8a0 : axst := Eval vm_compute in leafL_at cps_pro C_pro ssf8_pc 0.

Definition E_f8a1 : axst := Eval vm_compute in shadow_release_stateA E_f8a0 (objs_butlast E_f8a0) 110 [].
Definition E_f8a2 : axst := Eval vm_compute in shadow_reopen_stateA E_f8a1 X_lo g5 68 231.
Definition xf_shcall (A : axst) (k : Z) : list axform := ltac2:(tb__ "0|0|
S0S31S37S5dVA;A1S7cS88Vk;A2A2S2S31A1A3").
Definition E_f8a : axst := Eval vm_compute in optL (apply_axforms E_f8a2 (xf_shcall E_f8a2 68)).
Definition s_f8a : wsub := ltac2:(tb__ "0|0|
S0S3S2eS10A2S1S2eS10S75S38A4S74PaS29S46A1S29S53A1A3A3").
Definition R_f8a : list sobj := Eval vm_compute in optR (entails_frA E_f8a Pre_f8 s_f8a).
Definition T_f8a0 : axst := Eval vm_compute in T_afterA Pre_f8 E_f8a s_f8a R_f8a L_f8.

Definition xf_shback (A : axst) : list axform := ltac2:(tb__ "0|1|
S0S31S34U1M0A1S0S31S33S62VA;G0A2A1S2S31A1A3A3").
Definition T_f8a1 : axst := Eval vm_compute in optL (apply_axforms T_f8a0 (xf_shback T_f8a0)).
Definition T_f8a2 : axst := Eval vm_compute in shadow_release_stateA T_f8a1 (objs_butlast T_f8a1) 110 [].
Definition C_pro2 : axst := Eval vm_compute in shadow_reopen_stateA T_f8a2 (ax_X T_f8a2) g5 231 248.

Definition E_mo0 : axst := Eval vm_compute in leafL_at cps_pro C_pro2 memset_pc 0.
Definition E_mo1 : axst := Eval vm_compute in shadow_release_stateA E_mo0 (objs_butlast E_mo0) 110 [].
Definition s_mo : wsub := ltac2:(tb__ "0|1|
S0S3S2eS10A2M0S1S2eS10P35S3bA4S0G0S1S2eS10P36S11Zd0A1A4S0G0S1S2eS10S75S38A4S74PaS29S48A1S29S3cA1A3A3A3A3").
Definition R_mo : list sobj := Eval vm_compute in optR (entails_frA E_mo1 Pre_ms s_mo).
Definition T_mo0 : axst := Eval vm_compute in T_afterA Pre_ms E_mo1 s_mo R_mo L_ms.

Definition T_mo1 : axst := Eval vm_compute in optL (apply_axforms T_mo0 [AXSelect (sel_last T_mo0 1)]).
Definition C_pro3 : axst := Eval vm_compute in shadow_reopen_stateA T_mo1 (ax_X T_mo1) g5 32 64.

Definition E_mz0 : axst := Eval vm_compute in leafL_at cps_pro C_pro3 memset_pc 0.

Definition E_mz1 : axst := Eval vm_compute in shadow_release_stateA E_mz0 (objs_butlast E_mz0) 110 [(464, 48)].

Definition E_mz2 : axst := Eval vm_compute in optL (apply_axforms E_mz1 [AXSplit (idxF E_mz1) (SLit 496); AXSplit (S (idxF E_mz1)) (SLit 512)]).
Definition E_mz : axst := Eval vm_compute in ax_setS E_mz2 (reshape_obj_at (ax_S E_mz2) (S (idxF E_mz1)) (fslot 496 16 [] DUnknown)).
Definition s_mz : wsub := ltac2:(tb__ "0|1|
S0S3S2eS10A2M0S1S2eS10P35S16S66S43S11Z1d0A1A3A4S0G0S1S2eS10P36S11Z30A1A4S0G0S1S2eS10S75S38A4S74PaS29S49A1S29S3cA1A3A3A3A3").
Definition R_mz : list sobj := Eval vm_compute in optR (entails_frA E_mz Pre_ms s_mz).
Definition T_mz0 : axst := Eval vm_compute in T_afterA Pre_ms E_mz s_mz R_mz L_ms.

Definition T_mz1 : axst := Eval vm_compute in ax_setS T_mz0 (reshape_obj_at (ax_S T_mz0) 1 (fpiece 496 512 [] DZero)).

Definition E_ma0 : axst := Eval vm_compute in leafL_at cps_pro T_mz1 malloc_pc 0.

Definition W2 : list ulink := Wcan 2.
Definition Pre_ma : axst := ltac2:(tb__ "0|0|
S77S76S58S78A3").
Definition idxFlo (A : axst) : nat := ltac2:(tb__ "0|0|
S41VA;S18PaA1S7dS6aA1A3").
Definition E_ma : axst := Eval vm_compute in optL (apply_axforms E_ma0 [AXSplit (idxFlo E_ma0) (SLit (-16))]).
Definition s_ma : wsub := ltac2:(tb__ "0|0|
S0S3S2eS10A2S1S2eS10S75S38A4S74PaS29S47A1S29S55A1A3A3").
Definition R_ma : list sobj := Eval vm_compute in optR (entails_frA E_ma Pre_ma s_ma).
