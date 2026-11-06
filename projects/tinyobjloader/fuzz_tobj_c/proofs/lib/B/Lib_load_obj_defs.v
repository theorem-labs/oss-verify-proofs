(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "prod"; "false"; "length"; "andb"; "app"; "list"; "option"; "S"; "None"; "bool"; "negb"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sprop"; "SPUle"; "sobj"; "cell"; "mkObj"; "SAlu"; "ss_objs"; "SVar"; "DUnknown"; "SPAlign"; "sv_eqb"; "ob_base"; "ob_hi"; "ob_lo"; "odefault"; "FcsrFrm0"; "SPBranch"; "mkCell"; "mkSS"; "sstate"; "DZero"; "ob_cells"; "ob_dflt"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXSplit"; "AXMerge"; "AXRebase"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vBUF"; "vCFGp"; "optL"; "vDp"; "vOUT"; "vLEN"; "Pre_ms"; "find_idxb"; "FUEL_lo"; "sel2last"; "vNBP"; "BAD"; "L_ms"; "NP"; "O_Dlo"; "O_Flo"; "O_cfg"; "O_lnk"; "O_out"; "O_txtL"; "Pre_lo"; "R_of"; "X_lits17"; "bslot"; "cfg_cells"; "idxB"; "idxC"; "lo_facts"; "objs_lo"; "optR"; "optS"; "vRAF"; "z24"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs.LOAddr"; "FR"; "DW"; "lo_entry"; "lo_ret"; "memcpy_pc"; "memset_pc"; "sf5_pc"; "sm5_pc"; "ss00_pc"; "ssf8_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "c8"; "spm"; "two47"; "@Corelib.Init.Nat"; "sub"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "leb"; "ltb"; "pow"; "@Corelib.Lists.ListDef"; "seq"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "A_globals"; "leavesA_at"; "mkA"; "segs"; "show_leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double.ScanDoubleAddr"; "pow10_tab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve.RA.ReallocAddr"; "malloc_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA"; "zero_cells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "@Stdlib.Lists.List"; "filter"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr VRAddr RA.ReallocAddr.

Module LOAddr.
  Definition lo_entry : Z := 0x8cc90.
  Definition lo_ret : Z := 0x8eab0.
  Definition sm5_pc : Z := 0x480e8.
  Definition sf5_pc : Z := 0x482f4.
  Definition ssf8_pc : Z := 0x6053c.
  Definition ss00_pc : Z := 0x6041c.
  Definition memset_pc : Z := 0x5ce7c.
  Definition memcpy_pc : Z := 0x5c9e0.
  Definition FR : Z := 640.
  Definition DW : Z := 6144.
End LOAddr.
Import LOAddr.

Definition NP : positive := 100%positive.
Definition vOUT : sv := SVar 12. Definition vBUF : sv := SVar 13. Definition vLEN : sv := SVar 14. Definition vCFGp : sv := SVar 15.
Definition vDp : sv := SVar 19.

Definition vF : sv := SVar 110. Definition vFL : sv := SVar 120. Definition g5 : positive := 140%positive.

Definition O_Flo (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16S19PaA1S10S6bS5cA1A1S10Z0A1Vcells;S1aA5").
Definition O_Dlo : sobj := ltac2:(tb__ "0|0|
S16S67S5cA1S3eS10Z0A1S1S15A1S1aA5").
Definition O_out (cells : list cell) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S16S3fS10Z0A1S10Zd0A1Vcells;Vd;A5").
Definition O_txtL : sobj := ltac2:(tb__ "0|0|
S16S3bS10Z0A1S40S1S15A1S1aA5").

Definition vNBP : sv := SVar 16. Definition vRAF : sv := SVar 17.
Definition O_lnk : sobj := ltac2:(tb__ "0|1|
S16S19P1cA1S10N10M0A1S10Z0A1S0S15S66G0S45A2S0S15S66N8S5aA2S1S15A1A3A3S1aA5").
Definition cfg_cells : list cell := ltac2:(tb__ "0|1|
S0S15S23S10Z30A1Z4M0S10Z10101A1A3S0S15S23S10Z38A1G0S10ZffffffffA1A3S1S15A1A3A3").
Definition O_cfg : sobj := ltac2:(tb__ "0|0|
S16S3cS10Z0A1S10Z90A1S53S26A5").

Definition lo_facts : list sprop := ltac2:(tb__ "0|c|
S0S12S1bPaM0Z5M1A2S0S12S13S19G0A1M2S10S68A1M3A2S0S12S13S17S37S19P1eA1M4S10S6aS5cS5dA2M5A1A3G2A2S0S12S13G4S17S37S67S5cA1M6S3eA3A2S0S12S13G4S67G5A1A2S0S12S13G4G6A2S0S12S13G4G2A2S0S12S22S38S10S6bS5dA1A1S3eA3S0S12S22S38S3eS10S6bS6eZ2Z26A2A1A1A3S0S12S1bPcZ3A2S0S12S13G4S3fA2S0S12S13S17S37S3fS10Z110A1A3G3A2S0S12S13S3fG3A2S0S12S1bPdZ4M7A2S0S12S13S10Z1000A1S3bA2S0S12S13S17S37S3bS40A3S10Z7fffff800000A1M8A2S0S12S13S3bG8A2S0S12S13S3bG3A2S0S12S13S40S10S7aA1A2S0S12S1bPfG1A2S0S12S13S10S84A1S3cA2S0S12S13S17S37S3cS10Z90A1A3G4A2S0S12S13S3cG3A2S0S12S1bP1cM9G7A2S0S12S13S17S37G2S10Z10A1A3S19G9A1MaA2S0S12S13GaG3A2S0S12S13S45GaA2S0S12S13S10Z7fff7f800000A1MbG4A2S0S12S13G4G8A2S0S12S13GbG2A2S1S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition X_lits17 : list (sv * sv) := Eval vm_compute in removelast OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.X_lits.
Definition X_lo : list (sv * sv) := ltac2:(tb__ "0|2|
S8S4S11S11A2M0S0G0S3S11S11S3fS10Zd0A1A4S0G0S3S11S11S3bS40A4S0G0S3S11S11S3cS10Z90A1A4S0G0S3S11S11S10S79A1S10Zb8A1A4S0G0S3S11S11S67S6aS5cS5dA2M1A1S10G1A1A4S1G0A1A3A3A3A3A3S51A3").
Definition objs_lo : list sobj := ltac2:(tb__ "0|1|
S8S14S0S14S4aS1S15A1M0A1S0S14S49S0S14S4dG0S1aA2S0S14S4eS0S14S4bS0S14S4cS1S14A1A3A3A3A3A3A3S74A3").
Definition Pre_lo_S : sstate := ltac2:(tb__ "0|1|
S24S5eS81S80S0S4S2S11A2M0S3S2S11UdS3cA4S0G0S3S2S11UeS10Z0A1A4S1G0A1A3A3A2S7fS21ScS11A1S57S56S48S5A9").
Definition Pre_lo : axst := mkA Pre_lo_S X_lo.

Definition FUEL_lo : nat := 12000%nat.
Definition cps_pro : list Z := ltac2:(tb__ "0|0|
S0S29S63S0S29S62S0S29S65S0S29S64S0S29S61S0S29S60S0S29S7bS0S29S5fS1S29A1A3A3A3A3A3A3A3A3").
Definition optL (x : option axst) : axst := match x with Some s => s | None => Pre_lo end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leafL_at (cuts : list Z) (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S71S2dVk;S75S43Vcuts;VS;Vpc;A4S4fA4").
Definition showrun (cuts : list Z) (S : axst) : ltac2:(tb__ "0|0|
S9S4S29S72A2A1") := ltac2:(tb__ "0|2|
SaS9S2fA1M0A1S9S4S29S72A2M1A1Lx;S30S77S43Vcuts;VS;SfA5G0S70S2fG1S78R1A4Lls;S1G1A1Xax2").

Definition BAD : axst := ltac2:(tb__ "0|1|
S76S24Z0S1S11A1M0G0S21ScS11A1S1S14A1S1S12A1P1S5A9S1S4S11S11A2A1A2").
Definition ilast (A : axst) : nat := ltac2:(tb__ "0|0|
S69S6S14S18S2cVA;A1A1A2U1A2").
Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S8S2S6fU0Vi;A2S8S2S6fSbVi;A1M0S69S6S14S18S2cVA;A1A1A2G0A2A2S0S2Vi;S1S2A1A3A3A3").
Definition objs_butlast (A : axst) : list sobj := removelast (ss_objs (ax_S A)).
Fixpoint find_idxb {T} (f : T -> bool) (l : list T) (k : nat) : nat :=
  match l with [] => k | x :: r => if f x then k else find_idxb f r (S k) end.

Definition idxB (A : axst) (b : sv) (lo : Z) : nat := ltac2:(tb__ "0|0|
S42S14S14S7S1cS1dR1A1Vb;A2S1cS1fR1A1S10Vlo;A1A2A2Lo;S18S2cVA;A1A1U0A4").
Definition idxC (A : axst) (b : sv) (off : Z) : nat := ltac2:(tb__ "0|7|
S42S14S14S7S1cS1dR1A1Vb;A2S11SdLx;M0S1fR1A1S29G0S1eR2A1S29S7S6cR2Voff;A2S6dVoff;R1A2A2Lh;S2aS5Li;M1S39S11S11S5Lb0;La;M2Lop;M3G3S3aG2Lop;M4G4SdS2bS11S5La;Lw;Lsgn;M5S2aS11S29S5Lk;Li;M6Ll0;X11x8Ll;G1G3G3G4G4G5S2aG6Ll;X11x8A2Lo;S18S2cVA;A1A1U0A4").
Definition idxF (A : axst) : nat := idxB A (SVar 110) 0.
Definition sel2last (A : axst) (i j : nat) : list nat := ltac2:(tb__ "0|0|
S8S2S86S2S2S7SeS73R1Vi;A2A1SeS73R1Vj;A2A1A2Lk;S6fU0S6S14S18S2cVA;A1A1A2A2A3S0S2Vi;S0S2Vj;S1S2A1A3A3A3").
Definition optS (A : axst) (x : option sstate) : axst := ltac2:(tb__ "0|0|
SaS25A1S2dLx;Vx;S25S2eVA;R1A2LS1;S46Xax2").
Definition shapes (A : axst) : ltac2:(tb__ "0|0|
S9S4S4S4S4S11S11A2S11A2S20A2S2A2A1") := ltac2:(tb__ "0|3|
S70S14S4S4S4S4S11S11A2M0S11A2M1S20A2M2S2A2S14S3G2S2S3G1S20S3G0S11S3S11S11S1dR1A1S1fR1A1A4S1eR1A1A4S28R1A1A4S6S15S27R1A1A2A4Lo;S18S2cVA;A1A1A4").
Definition fpiece (lo hi : Z) (cells : list cell) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S16S19P6eA1S10Vlo;A1S10Vhi;A1Vcells;Vd;A5").
Definition fslot (lo n : Z) (cells : list cell) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S16S17S37S19P6eA1S10Vlo;A1A3S10Z0A1S10Vn;A1Vcells;Vd;A5").

Definition bslot (b : sv) (off n : Z) : sobj := ltac2:(tb__ "0|0|
S16S17S37Vb;S10Voff;A1A3S10Z0A1S10Vn;A1S1S15A1S1aA5").
Definition ms_carve (E0 : axst) (b : sv) (off n : Z) : axst := ltac2:(tb__ "0|0|
S55VE0;Vb;Voff;A3S2S3dS32VE0;S0S31S34R1S10Voff;A1A2S0S31S34SbR1A1S10S6aVoff;Vn;A2A1A2S1S31A1A3A3A2A1S2dS2eR1S7eS2cR1A1SbR2A1S52Vb;Voff;Vn;A3A3A2TE1;Ti;").
Definition Pre_ms : axst := Pre_memset memset_pc.
Definition L_ms : axst := L_memset (ae_ret_asan_memset AE_A).
Definition s_msx (E : axst) (xb xn : sv) : wsub := ltac2:(tb__ "0|1|
S0S4S2aS11A2M0S3S2aS11P35Vxb;A4S0G0S3S2aS11P36Vxn;A4S0G0S3S2aS11S85S3eA4S7cPaS2cVE;A1S2cS41A1A3A3A3A3").
Definition R_of (E : axst) (P : axst) (s : wsub) : list sobj := ltac2:(tb__ "0|0|
S58S7dVE;VP;Vs;A3A1").
Definition ms_T0 (E : axst) (s : wsub) : axst := ltac2:(tb__ "0|0|
S83S41VE;Vs;S50VE;S41Vs;A3S47A5").

Definition z24 : list cell := ltac2:(tb__ "0|2|
S0S15S66Z0M0S10G0A1M1A2S0S15S66Z8G1A2S0S15S66Z10G1A2S1S15A1A3A3A3").
Definition ms_back24 (T0 : axst) (b : sv) (off : Z) : axst := ltac2:(tb__ "0|4|
S59VT0;S82S2cVT0;A1U1M0S5bA3A2S2dS3dS32R1S0S31S36G0A1S1S31A1M1A3A2A1S2dS42S14S14S7S1cS1dR1A1Vb;A2S1cS1eR1A1S10Voff;A1A2A2Lo;S18S2cR1A1A1M2U0A4S2S3dS32R2S0S31S33S44R2R1G0A3A1G1A3A2A1S2dS54R1Vb;S6aVoff;Z18A2A3S2S3dS32R2S0S31S33S44R2S69S6S14S18S2cR2A1A1A2G0A2R1A3A1G1A3A2A1S2dS6S14G2A2S2S3dS32R2S0S31S35S69R1U3A2A1M3S0S31G3G1A3A3A2A1Tn;TT4;TiR;TT3;TiL;TT2;TT1;").

