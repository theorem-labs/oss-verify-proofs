(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_scan_double Lib_vec_reserve Asan_set_shadow_iface Lib_tess_polygon_states.

(* [comment removed for export] *)
Module Lib_builder_defs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "pair"; "prod"; "nat"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SPUle"; "cell"; "sv"; "SAlu"; "DUnknown"; "SPAlign"; "mkObj"; "SVar"; "SPBranch"; "sobj"; "ss_objs"; "mkSS"; "ob_base"; "ob_hi"; "ob_lo"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "c8"; "vDp"; "two47"; "B32"; "KLG"; "spm"; "vUD"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "kb4"; "vAL"; "vc"; "vb"; "piece"; "vE"; "PHI4"; "c1"; "c4"; "vLINE"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "batom"; "ASv"; "bitem"; "BI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "vB"; "vL"; "pB"; "two26"; "vI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve.RA.ReallocAddr"; "thunk_alloc"; "thunk_calloc"; "thunk_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "pow"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_vec_reserve.

Definition vE : sv := Lib_scan_double.vE.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition vb : sv := SVar 12.  Definition vc : sv := SVar 13.
Definition vERR : sv := SVar 53. Definition vND : sv := SVar 54. Definition vNC : sv := SVar 55. Definition vNK : sv := SVar 56.
Definition vLINE : sv := SVar 57. Definition vAL : sv := SVar 58.

Definition kb4 (k : sv) : sv := SMd M_MUL (SLit 4) k.
Definition cb4 (c : sv) : sv := SMd M_MUL c (SLit 4).

Definition c4 (o : Z) (v : sv) : cell := mkCell (SLit o) 4 v.
Definition c1 (o : Z) (v : sv) : cell := mkCell (SLit o) 1 v.
Definition piece (lo hi : Z) (cells : list cell) : sobj := ltac2:(tb__ "0|0|
SeS2cS7Vlo;A1S7Vhi;A1Vcells;ScA5").
Definition P_alloc : sobj := ltac2:(tb__ "0|1|
S2dZ0M0Z8S0S9S20G0S2aA2S1S9A1A3A3").
Definition P_st (err : sv) : sobj := ltac2:(tb__ "0|1|
S2dZ60M0Z78S0S9S31G0Verr;A2S0S9S20Z68S32A2S0S9S30Z70S7Z1A1A2S1S9A1A3A3A3A3").
Definition V184 (d c k : sv) : sobj := ltac2:(tb__ "0|1|
S2dZb8M0Zd8S0S9S20G0Vd;A2S0S9S20Zc0Vc;A2S0S9S20Zc8Vk;A2S0S9S20Zd0S7Z4A1A2S1S9A1A3A3A3A3A3").

Definition O_al : sobj := ltac2:(tb__ "0|2|
SeS2aS7Z0M0A1M1S7Z30A1S0S9S20G0S7S40A1A2S0S9S20Z8S7S41A1A2S0S9S20Z10G1A2S0S9S20Z18S7S42A1A2S0S9S20Z20G1A2S0S9S20Z28S26A2S1S9A1A3A3A3A3A3A3ScA5").

Definition O_c0 (cur : sv) : sobj := ltac2:(tb__ "0|1|
SeS2bS7Z0M0A1S7Z8A1S0S9S20G0S3aVcur;A1A2S1S9A1A3ScA5").
Definition O_c8 : sobj := ltac2:(tb__ "0|1|
SeS2bS7Z8M0A1S7Z10A1S0S9S20G0S3aS2eA1A2S1S9A1A3ScA5").

Definition O_dat (d k : sv) : sobj := ltac2:(tb__ "0|0|
SeVd;S7Z0A1S29Vk;A1S1S9A1ScA5").

Definition vec4_facts (d c k : sv) (dv : positive) : list sprop := ltac2:(tb__ "0|3|
S0S6SdVdv;Z4A2S0S6S8Vd;SfP1eA1M0A2S0S6S8SbS27Vd;S29Vk;A1M1A3G0A2S0S6S8Vd;S7S22A1A2S0S6S8Vc;Vk;A2S0S6S8Vk;S7S23A1M2A2S0S6S8G1G2A2S1S6A1A3A3A3A3A3A3A3").

Definition builder_facts (DW : Z) : list sprop := ltac2:(tb__ "0|8|
S0S6SdPaM0Z5A2S0S6S8SfG0A1M1S7S22A1M2A2S0S6S8SbS27SfP1eA1M3S7VDW;A1A3G1A2S0S6S8G3SbS27S25Z80A1M4S21A3A2S0S6S8G3G4A2S0S6S10S28S7N1100A1S21A3S0S6S10S28S21S7S46S47Z2Z26A2A1A1A3S0S6SdPcZ4A2S0S6S8S7S44A1M5S2cA2S0S6S8SbS27S2cS7Z518A1A3G3A2S0S6S8S2cG2A2S0S6SdPdZ3M6A2S0S6S8G3S2bA2S0S6S8SbS27S2bS7Z10A1A3G2A2S0S6S8S2bG2A2S0S6SdP3aG6A2S0S6S8G5S2aA2S0S6S8SbS27S2aS7Z30A1A3G3A2S0S6S8S2aG2A2S0S6S8S3cS2eA2S0S6S8S2eS39A2S0S6S8S39S7S3bA1A2S0S6S8S38G2A2S0S6S8S7Z1A1S38A2S0S6S8SbS27S38S39A3G2A2S0S6S8S7Z7fff7f800000A1M7G3A2S0S6S8G3S7Z7fffff800000A1A2S0S6S8G7G1A2S1S6A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition PHI4 (w k : sv) : bitem := ltac2:(tb__ "0|2|
S37Z1Z0M0S0S3S33S34A2M1S2S33S34Z6S35S29Vw;A1A1A4S0G1S2S33S34N4S35S29Vk;A1A1A4S0G1S2S33S34Z20S35S7Z4A1A1A4S1G1A1A3A3A3G0A4").
Definition bd_cnt (c k : sv) : list bitem := ltac2:(tb__ "0|0|
S0S36S2fVc;Vk;A2S0S36S24Vk;A1S1S36A1A3A3").
Definition tv_vec (d k : sv) : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3SaSaA2M0S2SaSaVd;S29Vk;A1A4S1G0A1A3").

Definition havoc_reg (A : axst) (r : nat) : axst := ltac2:(tb__ "0|2|
S3dVA;A1S1fS3eVA;S13S1cR1A1S43S1dR1A1S0S3S4SaA2M0S2S4SaVr;SfS1bR1A1M1A1A4S1G0A1A3A2S19R1A1S18R1A1S1eR1A1S12R1A1S17R1A1S45G1A1S1aR1A1A9A2TS;").
Definition shape (A : axst) : ltac2:(tb__ "0|0|
S5S3S3SaSaA2SaA2A1") := ltac2:(tb__ "0|1|
S3fS11S3S3SaSaA2M0SaA2S11S2G0SaS2SaSaS14R1A1S16R1A1A4S15R1A1A4Lo;S12S3dVA;A1A1A4").
End Lib_builder_defs.

(* [comment removed for export] *)
Module Lib_tess_polygon_cstates.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "nil"; "prod"; "app"; "length"; "None"; "S"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "SAlu"; "sprop"; "SPUle"; "sobj"; "DUnknown"; "cell"; "mkObj"; "ss_objs"; "FcsrFrm0"; "mkSS"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ANone"; "NDA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates"; "ndF"; "z0"; "nd0"; "vext"; "E_sm0"; "Pre_f8"; "Pre_sf"; "v153"; "vfin"; "vnw"; "BAD"; "C_body0"; "C_fin"; "C_pro"; "C_pro2"; "C_s1"; "E_f8a"; "E_f8a0"; "E_f8b"; "E_f8b0"; "E_ms"; "E_ms0"; "E_r2"; "E_r2_0"; "E_s00"; "E_s00_0"; "E_sc3"; "E_sc3_0"; "E_sc4"; "E_sc4_0"; "E_sfI"; "E_sfI0"; "E_sfK"; "E_sfK0"; "Pre_00"; "Pre_ms"; "Pre_sm"; "T_r2"; "T_sc3"; "T_sc4"; "T_sfI"; "T_sfK"; "ilast"; "sel_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXSelect"; "AXSplit"; "AXRebase"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "ALU_ADD"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_polygon_states"; "vF"; "C_b6cI"; "C_b6cK"; "C_c84"; "FUEL_pg"; "K708"; "K830"; "Kaa4"; "Kb08"; "Kb14"; "Kb64"; "Kbbp"; "Kcm"; "Kd10"; "Kd60"; "Ke1"; "Ke2"; "Ke3"; "Kext"; "Kfin"; "Knw"; "Knw2"; "Kproj"; "Ktail"; "P_inv"; "P_ok"; "Pre_pg"; "X_pg"; "cutpcs_pg"; "pNXT"; "pPRV"; "pRFX"; "pSCR"; "vFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_scale2d"; "Pre_sc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "SHB"; "leavesA_at"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states"; "Pre_r2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@Stdlib.ZArith.BinInt.Z"; "add"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface Lib_tess_scale2d.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import TessPolygonAddr.

Definition BAD : axst := ltac2:(tb__ "0|1|
S7eS16Z0S3SaA1M0G0S15S7SaA1S3S10A1S3SeA1P1S9A9S3S4SaSaA2A1A2").
Definition optAp (x : option axst) : axst := match x with Some s => s | None => BAD end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition leafP_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S57S18Vk;S7dS5cS74VS;Vpc;A4S2aA4").
Definition ilast (A : axst) : nat := ltac2:(tb__ "0|0|
S55S6S10S14S19VA;A1A1A2U1A2").

Definition sel_last (A : axst) (i : nat) : list nat := ltac2:(tb__ "0|1|
S5S2S56U0Vi;A2S5S2S56S8Vi;A1M0S55S6S10S14S19VA;A1A1A2G0A2A2S1S2Vi;S3S2A1A3A3A3").
Definition objs_butlast (A : axst) : list sobj := removelast (ss_objs (ax_S A)).

Definition Pre_sm : axst := Pre_stack_malloc AE_A 6.
Definition L_sm : axst := L_stack_malloc AE_A 6.
Definition Pre_f8 : axst := Pre_set_shadow AE_A 248.
Definition L_f8 : axst := L_set_shadow 248.
Definition Pre_00 : axst := Pre_set_shadow AE_A 0.
Definition L_00 : axst := L_set_shadow 0.
Definition Pre_ms : axst := Pre_memset pg_ms.
Definition L_ms : axst := L_memset asan_memset_ret.
Definition Pre_sf : axst := Pre_stack_free AE_A 6.
Definition L_sf : axst := L_stack_free AE_A 6.

Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S1dS3S4SaSaA2A1S3S4S4SaS1eA2SaA2A1S3S7bA1S1cA4").
Definition ndF : ndesc := ltac2:(tb__ "0|2|
S1dS3S4SaSaA2A1S1S4S4SaS1eA2M0SaA2M1S0G0SaS0SaS1eS58Z6A4S79A4S3G1A1A3S3S7bA1S1cA4").
Definition X_pgF : list (sv * sv) := ltac2:(tb__ "0|0|
S1S4SaSaA2S0SaSaS58SbZ0A1A4S73A3").

Definition E_sm0 : axst := Eval vm_compute in leafP_at Pre_pg pg_sm 0.
Definition s_sm : wsub := ltac2:(tb__ "0|0|
S1S4S1fSaA2S0S1fSaPfScP13A1A4S52PaS19S24A1S19S44A1A3A3").
Definition R_sm : list sobj := Eval vm_compute in optR (entails_frA E_sm0 Pre_sm s_sm).
Definition T_sm0 : axst := Eval vm_compute in T_afterA Pre_sm E_sm0 s_sm R_sm L_sm.

Definition T_sm1 : axst := Eval vm_compute in optAp (apply_axforms T_sm0 [AXSelect (sel_last T_sm0 3)]).
Definition C_pro0 : axst := Eval vm_compute in frame_open_stateA T_sm1 (objs_butlast T_sm1) X_pg 110 4096.
Definition C_pro : axst := ax_setX C_pro0 X_pgF.

Definition E_f8a0 : axst := Eval vm_compute in leafP_at C_pro pg_f8 0.
Definition O_dummy : sobj := ltac2:(tb__ "0|1|
S13SbZ0A1M0G0G0S3S12A1S11A5").
Definition shc_f8a : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S E_f8a0)) O_dummy).
Definition E_f8a1 : axst := Eval vm_compute in shadow_release_stateA E_f8a0 (objs_butlast E_f8a0) 110 [].

Definition E_f8a2 : axst := Eval vm_compute in shadow_reopen_stateA E_f8a1 X_pg gF 4 260.
Definition xf_shcall (A : axst) : list axform := ltac2:(tb__ "0|0|
S1S4cS51S4aVA;A1S83S7cZ4A2A2S3S4cA1A3").
Definition E_f8a : axst := Eval vm_compute in optAp (apply_axforms E_f8a2 (xf_shcall E_f8a2)).
Definition s_f8a : wsub := ltac2:(tb__ "0|0|
S1S4S1fSaA2S0S1fSaPfScP13A1A4S52PaS19S30A1S19S25A1A3A3").
Definition R_f8a : list sobj := Eval vm_compute in optR (entails_frA E_f8a Pre_f8 s_f8a).
Definition T_f8a0 : axst := Eval vm_compute in T_afterA Pre_f8 E_f8a s_f8a R_f8a L_f8.

Definition xf_shback (A : axst) : list axform := ltac2:(tb__ "0|1|
S1S4cS50U1M0A1S1S4cS4eS4bVA;G0A2A1S3S4cA1A3A3").
Definition T_f8a1 : axst := Eval vm_compute in optAp (apply_axforms T_f8a0 (xf_shback T_f8a0)).
Definition T_f8a2 : axst := Eval vm_compute in shadow_release_stateA T_f8a1 (objs_butlast T_f8a1) 110 [].
Definition C_pro2 : axst := Eval vm_compute in shadow_reopen_stateA T_f8a2 (ax_X T_f8a2) gF 260 276.

Definition E_ms0 : axst := Eval vm_compute in leafP_at C_pro2 pg_ms 0.
Definition shc_ms : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S E_ms0)) O_dummy).
Definition E_ms1 : axst := Eval vm_compute in shadow_release_stateA E_ms0 (objs_butlast E_ms0) 110 [].
Definition E_ms : axst := Eval vm_compute in optAp (apply_axforms E_ms1 [AXSplit 7 (SLit 16)]).
Definition s_ms : wsub := ltac2:(tb__ "0|1|
S1S4S1fSaA2M0S0S1fSaP35ScPdA1A4S1G0S0S1fSaP36SbZ18A1A4S1G0S0S1fSaPfScP13A1A4S52PaS19S34A1S19S43A1A3A3A3A3").
Definition R_ms : list sobj := Eval vm_compute in optR (entails_frA E_ms Pre_ms s_ms).
Definition C_body0 : axst := Eval vm_compute in T_afterA Pre_ms E_ms s_ms R_ms L_ms.

Definition E_s00_0 : axst := Eval vm_compute in leafP_at C_c84 pg_s00 0.
Definition E_s00_1 : axst := Eval vm_compute in shadow_reopen_stateA E_s00_0 (ax_X E_s00_0) gF 4 260.
Definition E_s00 : axst := Eval vm_compute in optAp (apply_axforms E_s00_1 (xf_shcall E_s00_1)).
Definition s_s00 : wsub := ltac2:(tb__ "0|0|
S1S4S1fSaA2S0S1fSaPfScP13A1A4S52PaS19S38A1S19S42A1A3A3").
Definition R_s00 : list sobj := Eval vm_compute in optR (entails_frA E_s00 Pre_00 s_s00).
Definition T_s00_0 : axst := Eval vm_compute in T_afterA Pre_00 E_s00 s_s00 R_s00 L_00.
Definition T_s00_1 : axst := Eval vm_compute in optAp (apply_axforms T_s00_0 (xf_shback T_s00_0)).
Definition C_s1 : axst := Eval vm_compute in shadow_release_stateA T_s00_1 (objs_butlast T_s00_1) 110 [].

Definition T_pure (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
S80S17S19VCl;A1A1S81Vs;VPre;VL;VCl;VR;A5A2").
Definition reshapeA (A : axst) (i : nat) (o : sobj) : axst := ltac2:(tb__ "0|0|
S1aVA;S82S19VA;A1Vi;Vo;A3A2").

Definition O_pp2d_lit (k : Z) : sobj := ltac2:(tb__ "0|0|
S13S78SbZ0A1SdS53SbVk;A1SbZ4A1A3S3S12A1S11A5").

Definition xf_wback : list axform := ltac2:(tb__ "0|1|
S1S4cS4eS1S2U5S1S2U0M0S1S2U1S1S2U2S1S2U3S1S2U4S1S2U6S1S2U7S1S2U8S1S2U9S1S2UaS1S2UbS1S2UcS1S2UdS1S2UeS1S2UfS3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S1S4cS4dG0A1S3S4cA1A3A3").

Definition E_sc3_0 : axst := Eval vm_compute in leafP_at K830 pg_scale2d 0.
Definition E_sc3_1 : axst := Eval vm_compute in reshapeA E_sc3_0 7 (O_pp2d_lit 3).
Definition E_sc3 : axst := Eval vm_compute in optAp (apply_axforms E_sc3_1 [AXSplit 1 (SLit (-16))]).
Definition s_sc3 : wsub := ltac2:(tb__ "0|0|
S52PaS19S3aA1S19S7aA1A3").
Definition R_sc3 : list sobj := Eval vm_compute in optR (entails_frA E_sc3 Pre_sc s_sc3).
Definition T_sc3_0 : axst := Eval vm_compute in T_pure Pre_sc E_sc3 s_sc3 R_sc3 P_sc.
Definition T_sc3_1 : axst := Eval vm_compute in reshapeA T_sc3_0 1 (O_pp2d []).
Definition T_sc3 : axst := Eval vm_compute in optAp (apply_axforms T_sc3_1 xf_wback).

Definition E_sc4_0 : axst := Eval vm_compute in leafP_at K708 pg_scale2d 0.
Definition E_sc4_1 : axst := Eval vm_compute in reshapeA E_sc4_0 7 (O_pp2d_lit 4).
Definition E_sc4 : axst := Eval vm_compute in optAp (apply_axforms E_sc4_1 [AXSplit 1 (SLit (-16))]).
Definition s_sc4 : wsub := ltac2:(tb__ "0|0|
S52PaS19S3cA1S19S7aA1A3").
Definition R_sc4 : list sobj := Eval vm_compute in optR (entails_frA E_sc4 Pre_sc s_sc4).
Definition T_sc4_0 : axst := Eval vm_compute in T_pure Pre_sc E_sc4 s_sc4 R_sc4 P_sc.
Definition T_sc4_1 : axst := Eval vm_compute in reshapeA T_sc4_0 1 (O_pp2d []).
Definition T_sc4 : axst := Eval vm_compute in optAp (apply_axforms T_sc4_1 xf_wback).

Definition E_r2_0 : axst := Eval vm_compute in leafP_at K708 pg_run2d 0.
Definition xf_r2call : list axform := ltac2:(tb__ "0|2|
S1S4cS4fU1M0SbN90A1A2S1S4cS4fU0SbNb8M1A1A2S1S4cS4fG0SbN98A1A2S1S4cS51G0G1A2S3S4cA1A3A3A3A3").
Definition E_r2_1 : axst := Eval vm_compute in optAp (apply_axforms E_r2_0 xf_r2call).

Definition r2_ptr_facts : list sprop := ltac2:(tb__ "0|1|
S1SeSfS75SbZ800000000000A1M0A2S1SeSfS76G0A2S1SeSfS77G0A2S3SeA1A3A3A3").
Definition E_r2 : axst := ax_add_facts r2_ptr_facts E_r2_1.
Definition s_r2 : wsub := ltac2:(tb__ "0|0|
S52PaS19S36A1S19S7fA1A3").
Definition R_r2 : list sobj := Eval vm_compute in optR (entails_frA E_r2 Pre_r2 s_r2).
Definition T_r2_0 : axst := Eval vm_compute in T_pure Pre_r2 E_r2 s_r2 R_r2 P_ret.

Definition xf_r2back : list axform := ltac2:(tb__ "0|3|
S1S4cS50U1M0A1S1S4cS4eS1S2U9S1S2G0S1S2UaS1S2UbS1S2U0M1S1S2U2S1S2U3S1S2U4S1S2U5S1S2U6S1S2U7S1S2U8S1S2UcS1S2UdS1S2UeS1S2UfS1S2U10S1S2U11S3S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S1S4cS4dG1A1M2S1S4cG2S1S4cS4dG0A1S3S4cA1A3A3A3A3A3").
Definition T_r2 : axst := Eval vm_compute in optAp (apply_axforms T_r2_0 xf_r2back).

Definition E_f8b0 : axst := Eval vm_compute in leafP_at Ktail pg_f8 0.
Definition E_f8b1 : axst := Eval vm_compute in shadow_reopen_stateA E_f8b0 (ax_X E_f8b0) gF 4 260.
Definition E_f8b : axst := Eval vm_compute in optAp (apply_axforms E_f8b1 (xf_shcall E_f8b1)).
Definition s_f8b : wsub := ltac2:(tb__ "0|0|
S1S4S1fSaA2S0S1fSaPfScP13A1A4S52PaS19S32A1S19S25A1A3A3").
Definition R_f8b : list sobj := Eval vm_compute in optR (entails_frA E_f8b Pre_f8 s_f8b).
Definition T_f8b0 : axst := Eval vm_compute in T_afterA Pre_f8 E_f8b s_f8b R_f8b L_f8.
Definition T_f8b1 : axst := Eval vm_compute in optAp (apply_axforms T_f8b0 (xf_shback T_f8b0)).
Definition C_fin : axst := Eval vm_compute in shadow_release_stateA T_f8b1 (objs_butlast T_f8b1) 110 [].

Definition E_sfI0 : axst := Eval vm_compute in leafP_at C_b6cI pg_sf 0.
Definition E_sfK0 : axst := Eval vm_compute in leafP_at C_b6cK pg_sf 0.

Definition E_sfI : axst := Eval vm_compute in flag_carve_stateA E_sfI0 120.
Definition E_sfK : axst := Eval vm_compute in flag_carve_stateA E_sfK0 120.
Definition s_sfI : wsub := ltac2:(tb__ "0|1|
S1S4S1fSaA2M0S0S1fSaP10ScP78A1A4S1G0S0S1fSaPfScP13A1A4S52PaS19S3eA1S19S26A1A3A3A3").
Definition s_sfK : wsub := ltac2:(tb__ "0|1|
S1S4S1fSaA2M0S0S1fSaP10ScP78A1A4S1G0S0S1fSaPfScP13A1A4S52PaS19S40A1S19S26A1A3A3A3").
Definition R_sfI : list sobj := Eval vm_compute in optR (entails_frA E_sfI Pre_sf s_sfI).
Definition R_sfK : list sobj := Eval vm_compute in optR (entails_frA E_sfK Pre_sf s_sfK).

Definition T_sfI : axst := Eval vm_compute in T_afterA3 Pre_sf E_sfI s_sfI R_sfI L_sf X_pg.
Definition T_sfK : axst := Eval vm_compute in T_afterA3 Pre_sf E_sfK s_sfK R_sfK L_sf X_pg.

Definition z0 : sv := SLit 0.

Definition vfin : sv := SVar 151.
Definition vnw (k : Z) : sv := ltac2:(tb__ "0|0|
SdS54SdS53ScP99A1SbZ1A1A3SbVk;A1A3").
Definition vext (k : Z) : sv := ltac2:(tb__ "0|0|
SdS54SdS53ScP99A1SbZ2A1A3SbVk;A1A3").
Definition v153 : sv := SVar 153.
Definition cutsE : list edescA := ltac2:(tb__ "0|c|
S1S4S4S18S1bA2M0S4S1eSaA2M1A2M2S0G0G1S0S18S1bS72S22A4S0S1eSaZ64S21A4A4S1G2S0G0G1S0S18S1bS2dS20A4S0S1eSaZ60S21A4A4S1G2S0G0G1S0S18S1bS2eS20A4S0S1eSaZ5eS21A4A4S1G2S0G0G1S0S18S1bS2bS20A4S0S1eSaZ5cS21A4A4S1G2S0G0G1S0S18S1bS6bS20A4S0S1eSaZ5aS28A4A4S1G2S0G0G1S0S18S1bS5bS20A4S0S1eSaZ58S21A4A4S1G2S0G0G1S0S18S1bS59S20A4S0S1eSaZ14S21A4M3A4S1G2S0G0G1S0S18S1bS2fS20A4S0S1eSaZ56S21A4A4S1G2S0G0G1S0S18S1bS64S20A4S0S1eSaZ54S28A4A4S1G2S0G0G1S0S18S1bS6cS20A4S0S1eSaZ52M4S29Z0M5A1A4A4S1G2S0G0G1S0S18S1bS6dS20A4S0S1eSaG4S29N1M6A1A4A4S1G2S0G0G1S0S18S1bS6aS20A4S0S1eSaZ50M7S23G5A1A4A4S1G2S0G0G1S0S18S1bS67S20A4S0S1eSaG7S23G6A1A4A4S1G2S0G0G1S0S18S1bS68S20A4S0S1eSaG7S23N2A1A4A4S1G2S0G0G1S0S18S1bS69S20A4S0S1eSaG7S23N3A1A4A4S1G2S0G0G1S0S18S1bS6eS20A4S0S1eSaZ4eS27A4A4S1G2S0G0G1S0S18S1bS63S20A4S0S1eSaZ4cS27A4A4S1G2S0G0G1S0S18S1bS5dS20A4S0S1eSaZ46S21A4A4S1G2S0G0G1S0S18S1bS5eS20A4S0S1eSaZ44S21A4A4S1G2S0G0G1S0S18S1bS46S20A4S0S1eSaZ3cS21A4M8A4S1G2S0G0G1S0S18S1bS47S20A4G8A4S1G2S0G0G1S0S18S1bS45S20A4G8A4S1G2S0G0G1S0S18S1bS5fS20A4S0S1eSaZ3aS21A4A4S1G2S0G0G1S0S18S1bS60S20A4S0S1eSaZ38S21A4A4S1G2S0G0G1S0S18S1bS61S20A4S0S1eSaZ36S21A4M9A4S1G2S0G0G1S0S18S1bS65S20A4G9A4S1G2S0G0G1S0S18S1bS62S20A4S0S1eSaZ34S21A4MaA4S1G2S0G0G1S0S18S1bS66S20A4GaA4S1G2S0G0G1S0S18S1bS6fS20A4S0S1eSaZ32S21A4A4S1G2S0G0G1S0S18S1bS2cS20A4S0S1eSaZ28S21A4A4S1G2S0G0G1S0S18S1bS5aS20A4G3A4S1G2S0G0G1S0S18S1bS48S22A4S0S1eSaZaS21A4MbA4S1G2S0G0G1S0S18S1bS49S22A4GbA4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|6|
S1S4S4S18S1bA2M0S4S1eSaA2M1A2M2S0G0G1S0S18S1bS24S22A4S0S1eSaZ62S21A4A4S1G2S0G0G1S0S18S1bS31S20A4S0S1eSaZ5fS21A4A4S1G2S0G0G1S0S18S1bS35S20A4S0S1eSaZ5dS21A4A4S1G2S0G0G1S0S18S1bS39S20A4S0S1eSaZ57S21A4A4S1G2S0G0G1S0S18S1bS3bS20A4S0S1eSaZ42S21A4M3A4S1G2S0G0G1S0S18S1bS3dS20A4G3A4S1G2S0G0G1S0S18S1bS37S20A4G3A4S1G2S0G0G1S0S18S1bS33S20A4S0S1eSaZ2dS21A4A4S1G2S0G0G1S0S18S1bS3fS20A4S0S1eSaZfS21A4M4A4S1G2S0G0G1S0S18S1bS41S20A4G4A4S1G2S0G0G1S0S18S1bS70S22A4S0S1eSaZ0S21A4M5A4S1G2S0G0G1S0S18S1bS71S22A4G5A4S3G2A1A3A3A3A3A3A3A3A3A3A3A3A3").
End Lib_tess_polygon_cstates.

