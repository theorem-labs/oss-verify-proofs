(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_074.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c2 dc.

(* [comment removed for export] *)
Module SpineCallocRp1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "entailsA"; "ax_X"; "axst"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "SLit"; "ss_facts"; "swf"; "ss_lenient"; "ss_objs"; "SAlu"; "SVar"; "reg_sv"; "SPNot"; "valuation"; "sprop_below"; "SPBranch"; "SPUle"; "rm"; "ss_pc"; "sv_below"; "rw"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "factsR"; "cX"; "GR"; "beg1"; "beg2"; "cE1"; "cE2"; "keepn"; "cP2"; "cXL"; "O_pcm"; "PV4"; "LV0"; "O_ri"; "cL1"; "cT1"; "cD"; "cPa"; "cPb"; "LV2"; "PV6"; "cE3"; "nobj"; "rMS"; "sMS"; "LV3"; "cE3b"; "vMU"; "cFm"; "vK"; "F_x"; "HINT_au"; "HINT_k"; "HINT_map"; "LNX"; "O_pccK"; "PNX"; "cE3a"; "idx_rot"; "k_e"; "relM"; "ri_has"; "rotM"; "vAU"; "vMFA"; "F_new"; "vNEW"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi1"; "e3r"; "FUEL"; "icc"; "W0"; "r_2_0"; "nob"; "e3p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLeOrPc"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dm.SpineCallocRp1"; "r_xF_0"; "r_xU_0"; "cmcF"; "cmcU"; "r_9M_0"; "r_9P_0"; "cl0M"; "cl0P"; "cp2c"; "ct0M"; "ct0P"; "nobFM"; "nobFP"; "r_lM_1"; "r_lP_1"; "r_p1_0"; "r_p1_1"; "r_d_0"; "r_f_0"; "cfm"; "r_f_1"; "r_h_0"; "r_mF_0"; "r_mU_0"; "rf1"; "ru1"; "dmF"; "dmU"; "r_jM_0"; "r_jP_0"; "r_p2a_0"; "r_p2a_1"; "r_p2b_0"; "r_p2b_1"; "s_fbkM"; "s_fbkP"; "s_finM"; "s_finP"; "r_lM_0"; "r_lP_0"; "r_t1M_0"; "r_t1P_0"; "s_bkM"; "s_bkP"; "s_inM"; "s_inP"; "xlM"; "xlP"; "r_t1M_1"; "r_t1P_1"; "cellsfM"; "cellsfP"; "r_flM_0"; "r_flP_0"; "r_t0M_0"; "r_t0P_0"; "r_zM_0"; "r_zP_0"; "sa0"; "sa1"; "sb0"; "sb1"; "s_xM"; "s_xP"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "instr"; "ALU_SLL"; "ALU_XOR"; "Ecall"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "O_pcc0"; "O_st"; "V_SIZE"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "memset_post"; "TRok"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "phase"; "JR"; "entryR"; "gh_new"; "ph0";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocR10"; "cMr"; "a2_e"; "cMc"; "dMSf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR13"; "F_lt"; "O_fcell"; "faend_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7"; "F_mu0"; "F_hi"; "x19_e0"; "x19_e1"; "popfacts"; "size_e_hi"; "size_e_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9"; "O_piece"; "O_shp"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "call_checkA"; "entails_frA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR11"; "a0_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR12"; "F_geu"; "new_e"; "rup_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocR14"; "e16P"; "e32P"; "e48P"; "e_srcP"; "e24M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15"; "fillT"; "phUF3"; "pieceT"; "fmT"; "headT"; "midT"; "phFin"; "phU3"; "runT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4"; "O_rif"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP"; "PF"; "PU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocR14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_p1__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ415c0SbS2cZ41600SeS2cA1A3A3S5S62A1ScA5").
Local Strategy expand [R_p1__R].
Definition r_p1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_p1__R).
Definition r_p1_0 := Eval vm_compute in (nth 0 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition r_p1_1 := Eval vm_compute in (nth 1 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition R_p2a__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41630SeS2cA1A3S3fS2eS5eA1S5S80A1A2ScA5").
Local Strategy expand [R_p2a__R].
Definition r_p2a := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_p2a__R).
Definition r_p2a_0 := Eval vm_compute in (nth 0 r_p2a (mkLeafA (cPa (factsR e3r) (la_state r_p1_0)) RsCut)).
Definition r_p2a_1 := Eval vm_compute in (nth 1 r_p2a (mkLeafA (cPa (factsR e3r) (la_state r_p1_0)) RsCut)).
Definition R_p2b__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41630SeS2cA1A3S40S2eS5eA1S5S81A1A2ScA5").
Local Strategy expand [R_p2b__R].
Definition r_p2b := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_p2b__R).
Definition r_p2b_0 := Eval vm_compute in (nth 0 r_p2b (mkLeafA (cPb (factsR e3r) (la_state r_p1_1)) RsCut)).
Definition r_p2b_1 := Eval vm_compute in (nth 1 r_p2b (mkLeafA (cPb (factsR e3r) (la_state r_p1_1)) RsCut)).
Definition cp2c := Eval vm_compute in (cP2c (factsR e3r) (la_state r_p2a_1)).
Lemma FP_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S26Sb7S5dS4bA3SeS19A1A3S1cS4S5S62A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p1 : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ415c0SbS2cZ41600SeS2cA1A3A3S5S62A1ScA5S11G0SbS6S80SbS6S81SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p1__R <: R_p1__R = Some [r_p1_0; r_p1_1]). Qed.
Lemma LN_p1 : ltac2:(tb__ "0|0|
S0SdS1eS4S5S62A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p1 : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S62A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd8SeS19A1A3S1cS4S5S80A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd8A1SeS19A1A3S1cS4S5S81A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_pa : ltac2:(tb__ "0|0|
S0SdS1dS4S3fS2eS5eA1S5S80A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_pa : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S80A1M4A1S4S3fS2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SdcS21SbbA1A4SeG0A1A3SbS19S4fSbS19S27S49S1bZdffc0000A1A2SeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_pa : ltac2:(tb__ "0|1|
S0SdS68S1aS4S3fS2eS5eA1S5S80A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_pb : ltac2:(tb__ "0|0|
S0SdS1dS4S40S2eS5eA1S5S81A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_pb : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S81A1M4A1S4S40S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SddS21SbbA1A4SeG0A1A3SbS19S4fSbS19S27S49S1bZdffc0000A1A2SeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_pb : ltac2:(tb__ "0|1|
S0SdS68S1aS4S40S2eS5eA1S5S81A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p2a : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41630SeS2cA1A3S3fS2eS5eA1S5S80A1A2ScA5S11G0SbS6S8fSbS6S90SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p2a__R <: R_p2a__R = Some [r_p2a_0; r_p2a_1]). Qed.
Lemma LN_p2a : ltac2:(tb__ "0|0|
S0SdS1eS4S3fS2eS5eA1S5S80A1A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p2a : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S3fS2eS5eA1S5S80A1A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p2b : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41630SeS2cA1A3S40S2eS5eA1S5S81A1A2ScA5S11G0SbS6S91SbS6S92SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p2b__R <: R_p2b__R = Some [r_p2b_0; r_p2b_1]). Qed.
Lemma LN_p2b : ltac2:(tb__ "0|0|
S0SdS1eS4S40S2eS5eA1S5S81A1A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p2b : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S40S2eS5eA1S5S81A1A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa0_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd7SeS19A1A3S1cS4S5S8fA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_a0 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S8fA1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a0 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S8fA1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18Sd9S1bZ40000A1A4SbG0S13S18S18S1bZ0A1S49A4SeG0A1A3A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a0 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S8fA1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sa0 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2a_0))) (ax_S cp2c)).
Lemma ENT_a0 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S8fA1A2S79SabA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_a0 : ltac2:(tb__ "0|0|
S0SdS6cSabS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa1_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd7A1SeS19A1A3S1cS4S5S90A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_a1 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S90A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a1 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S90A1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SdaS1bZ40000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a1 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S90A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sa1 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2a_1))) (ax_S cp2c)).
Lemma ENT_a1 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S90A1A2S79SacA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_a1 : ltac2:(tb__ "0|0|
S0SdS6cSacS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb0_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd7SeS19A1A3S1cS4S5S91A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S91A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S91A1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18Sd9S1bZ40000A1A4SbG0S13S18S18S1bZ0A1S49A4SeG0A1A3A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S91A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sb0 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2b_0))) (ax_S cp2c)).
Lemma ENT_b0 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S91A1A2S79SadA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_b0 : ltac2:(tb__ "0|0|
S0SdS6cSadS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb1_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd7A1SeS19A1A3S1cS4S5S92A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S92A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S92A1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SdaS1bZ40000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S92A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sb1 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2b_1))) (ax_S cp2c)).
Lemma ENT_b1 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S92A1A2S79SaeA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_b1 : ltac2:(tb__ "0|0|
S0SdS6cSaeS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma head_i : ltac2:(tb__ "0|0|
SfcS61S6dS5S62A1S79A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE HC.
  exact (populate_head A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HE FUEL e3r (la_state r_2_0) r_p1_0 r_p1_1 r_p2a_0 r_p2a_1 r_p2b_0 r_p2b_1 cp2c sa0 sa1 sb0 sb1
           (In_of_inclb _ _ FP_inb) R_p1 LN_p1 NX_p1 (In_of_inclb _ _ Fa_inb) (In_of_inclb _ _ Fb_inb) W_pa D_pa NXe_pa W_pb D_pb NXe_pb R_p2a LN_p2a NX_p2a R_p2b LN_p2b NX_p2b
           (In_of_inclb _ _ Fa0_inb) (In_of_inclb _ _ Fa1_inb) (In_of_inclb _ _ Fb0_inb) (In_of_inclb _ _ Fb1_inb) W_a0 W_a1 W_b0 W_b1 D_a0 D_a1 D_b0 D_b1 NXe_a0 NXe_a1 NXe_b0 NXe_b1
           ENT_a0 ENT_a1 ENT_b0 ENT_b1 SID_a0 SID_a1 SID_b0 SID_b1 r tp Q HC).
Qed.
Definition R_xU__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ7050cSeS2cA1A3S79ScA5").
Local Strategy expand [R_xU__R].
Definition r_xU := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_xU__R).
Definition r_xU_0 := Eval vm_compute in (nth 0 r_xU (mkLeafA cp2c RsCut)).
Definition R_mU__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S72A1S31A2S31Z40000A3ScA5").
Local Strategy expand [R_mU__R].
Definition r_mU := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) R_mU__R).
Definition r_mU_0 := Eval vm_compute in (nth 0 r_mU (mkLeafA (commit_post (cX (la_state r_xU_0) beg1) beg1 262144) RsCut)).
Definition cmcU := Eval vm_compute in (cMc (la_state r_mU_0) beg1).
Lemma CMCU_eq : ltac2:(tb__ "0|0|
S0SaScfS5S88A1S31A2S74A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition dmU := Eval vm_compute in (dMSf cmcU).
Lemma DMU_eq : ltac2:(tb__ "0|0|
S0SaSd0S74A1S8cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition ru1 := Eval vm_compute in (relM dmU).
Lemma RU1_eq : ltac2:(tb__ "0|0|
S0SaS56S8cA1S8aA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R_xU : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ7050cSeS2cA1A3S79ScA5S11G0SbS6S72SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_xU__R <: R_xU__R = Some [r_xU_0]). Qed.
Lemma LN_xU : ltac2:(tb__ "0|0|
S0SdS1eS4S79A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_xU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S79A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_xU : ltac2:(tb__ "0|0|
S0SdS1dS4S2fS5S72A1S31A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xU : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S72A1M4A1S4S2fG4S31A2A1A2S11G3S13G1G2SbG0S13S18S18SefS31A1S31A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_xU : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S2fS5S72A1S31A2A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xUb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S2fS5S72A1S31A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_xU : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S2fS5S72A1S31A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXc_xU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S2fS5S72A1S31A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_xU : ltac2:(tb__ "0|0|
S0S12Sb3A1Se9S2dS29S4S2fS5S72A1S31A2A1A1A2S11Sb3Sb6A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1Z11A2S1bZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZaA2S31A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZbA2S1bZ40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZcA2S1bZ3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZdA2S1bZ32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZeA2S1bZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZfA2S1bZ0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_xU : ltac2:(tb__ "0|0|
S0SdS2aS1aS4S2fS5S72A1S31A2A1A1S31A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_mU : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S72A1S31A2S31Z40000A3ScA5S11G0SbS6S88SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_mU__R <: R_mU__R = Some [r_mU_0]). Qed.
Lemma LN_mU : ltac2:(tb__ "0|0|
S0SdS1eS4SbfS2fS5S72A1S31A2S31Z40000A3A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_mU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4SbfS2fS5S72A1S31A2S31Z40000A3A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_mU : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S5S88A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSbS17SdeS31A1SeS17A1A3A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mUb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S5S88A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_mU : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S5S88A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mrU : ltac2:(tb__ "0|0|
S0SdS1dS4ScdS5S88A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mrU : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S88A1M4A1S4ScdG4A1A1A2S11G3S13G1G2SbG0S13S18S18SceS31A1S1bZ8000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mcU : ltac2:(tb__ "0|0|
S0SdS1dS4S74A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_msU : ltac2:(tb__ "0|1|
S0S12SfS17A1M0A1SedS74Sc5S46S74A1A3S11G0S45S74A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_msU : ltac2:(tb__ "0|0|
S0SdSecS74Sc5S46S74A1S45S74A1S69S6SaS5Sc6A4A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_msU : ltac2:(tb__ "0|0|
S0SdS67Sc7S1aS4S74A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_msU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S74A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_msU : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S74A1M0A1A1S1cG0A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_msU : ltac2:(tb__ "0|0|
S0SdSc2S19S25S1aS4Sc0S74S46S74A1S45S74A1A3A1A1A1S1cS4S74A1A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_rU : ltac2:(tb__ "0|0|
S0SdSe8S54S8cA1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rUb : ltac2:(tb__ "0|0|
S0SdS102U1S44S8cA1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rU : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S58S8cA1A1A1M0S14S17S6aS17Sc4S44S8cA1U2A2G0A3SbS17SdeS31A1SbS17SdfS31A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma pieceU_i : ltac2:(tb__ "0|0|
SfaS61S6dS104S31S79S8aA6").
Proof.
  rewrite <- RU1_eq, <- DMU_eq, <- CMCU_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE PU beg1 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cp2c r_xU_0 r_mU_0
           R_xU LN_xU NX_xU W_xU D_xU SK_xU (inclb_incl _ _ XF_xUb) XX_xU NXc_xU IC_xU R17_xU R10_xU BEL_xU R11_xU R12_xU R13_xU R14_xU R15_xU
           R_mU LN_mU NX_mU SK_mU (inclb_incl _ _ XF_mUb) XX_mU W_mrU D_mrU _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCU_eq, ?DMU_eq; [exact W_mcU | exact E_msU | exact CHK_msU | exact NF_msU | exact NX_msU | exact FBC_msU | exact FBT_msU | exact ND_rU | apply Nat.leb_le; exact NO_rUb | exact OB_rU].
Qed.
Definition R_d__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ416f0SeS2cA1A3S8aScA5").
Local Strategy expand [R_d__R].
Definition r_d := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_d__R).
Definition r_d_0 := Eval vm_compute in (nth 0 r_d (mkLeafA ru1 RsCut)).
Definition R_f__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ3f270SbS2cZ4172cSeS2cA1A3A3S3eS2eS5eA1S5S82A1A2ScA5").
Local Strategy expand [R_f__R].
Definition r_f := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_f__R).
Definition r_f_0 := Eval vm_compute in (nth 0 r_f (mkLeafA (cD (factsR e3r) (la_state r_d_0)) RsCut)).
Definition r_f_1 := Eval vm_compute in (nth 1 r_f (mkLeafA (cD (factsR e3r) (la_state r_d_0)) RsCut)).
Lemma R_d : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ416f0SeS2cA1A3S8aScA5S11G0SbS6S82SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_d__R <: R_d__R = Some [r_d_0]). Qed.
Lemma LN_d : ltac2:(tb__ "0|0|
S0SdS1eS4S8aA1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_d : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S8aA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_d : ltac2:(tb__ "0|0|
S0SdS1dS4S3eS2eS5eA1S5S82A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_d : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S82A1M4A1S4S3eS2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18Sf1S5cA4SeG0A1A3S5bA4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_d : ltac2:(tb__ "0|1|
S0SdS68S1aS4S3eS2eS5eA1S5S82A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_f : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3f270SbS2cZ4172cSeS2cA1A3A3S3eS2eS5eA1S5S82A1A2ScA5S11G0SbS6S83SbS6S85SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_f__R <: R_f__R = Some [r_f_0; r_f_1]). Qed.
Lemma LN_f : ltac2:(tb__ "0|0|
S0SdS1eS4S3eS2eS5eA1S5S82A1A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_f : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S3eS2eS5eA1S5S82A1A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma F0_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sf0SeS19A1A3S1cS4S5S83A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fm_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sf0A1SeS19A1A3S1cS4S5S85A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma mid_i : ltac2:(tb__ "0|0|
SfdS61S6dS8aS5S83A1S5S85A1A5").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph r tp Q. cbn zeta.
  exact (populate_mid A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HE PF ph FUEL e3r ru1 r_d_0 r_f_0 r_f_1 R_d LN_d NX_d W_d D_d NXe_d R_f LN_f NX_f (In_of_inclb _ _ F0_inb) (In_of_inclb _ _ Fm_inb) r tp Q).
Qed.
Definition cfm := Eval vm_compute in (cFm (la_state r_f_1)).
Lemma CFM_eq : ltac2:(tb__ "0|0|
S0SaS4aS5S85A1A1S84A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_fm : ltac2:(tb__ "0|0|
S0SdS1dS4S4aS5S85A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_fm : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S85A1M4A1S4S4aG4A1A1A2S11G3S13G1G2SbG0S13S18S18Sf2S20Sb1S5aS1bZ40000A1A3A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma fm_i : ltac2:(tb__ "0|0|
SfbS61S6dS5S85A1S84A4").
Proof.
  rewrite <- CFM_eq. intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph r tp Q. cbn zeta.
  exact (famap_restate A Kc rb tp0 md0 TR KIT W0 UStopLeOrPc rho HE PF (la_state r_f_1) W_fm D_fm ph r tp Q).
Qed.
Definition R_xF__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ7050cSeS2cA1A3S84ScA5").
Local Strategy expand [R_xF__R].
Definition r_xF := Eval vm_compute in ((fun ro8__ : option (list leafA) => (match ro8__ with Some l => l | None => [] end)) R_xF__R).
Definition r_xF_0 := Eval vm_compute in (nth 0 r_xF (mkLeafA cfm RsCut)).
Definition R_mF__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S71A1S32A2S32Z40000A3ScA5").
Local Strategy expand [R_mF__R].
Definition r_mF := Eval vm_compute in ((fun ro9__ : option (list leafA) => (match ro9__ with Some l => l | None => [] end)) R_mF__R).
Definition r_mF_0 := Eval vm_compute in (nth 0 r_mF (mkLeafA (commit_post (cX (la_state r_xF_0) beg2) beg2 262144) RsCut)).
Definition cmcF := Eval vm_compute in (cMc (la_state r_mF_0) beg2).
Lemma CMCF_eq : ltac2:(tb__ "0|0|
S0SaScfS5S87A1S32A2S73A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition dmF := Eval vm_compute in (dMSf cmcF).
Lemma DMF_eq : ltac2:(tb__ "0|0|
S0SaSd0S73A1S8bA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition rf1 := Eval vm_compute in (relM dmF).
Lemma RF1_eq : ltac2:(tb__ "0|0|
S0SaS56S8bA1S89A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R_xF : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ7050cSeS2cA1A3S84ScA5S11G0SbS6S71SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_xF__R <: R_xF__R = Some [r_xF_0]). Qed.
Lemma LN_xF : ltac2:(tb__ "0|0|
S0SdS1eS4S84A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_xF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S84A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_xF : ltac2:(tb__ "0|0|
S0SdS1dS4S2fS5S71A1S32A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xF : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S71A1M4A1S4S2fG4S32A2A1A2S11G3S13G1G2SbG0S13S18S18SefS32A1S32A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_xF : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S2fS5S71A1S32A2A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xFb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S2fS5S71A1S32A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_xF : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S2fS5S71A1S32A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXc_xF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S2fS5S71A1S32A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_xF : ltac2:(tb__ "0|0|
S0S12Sb3A1Se9S2dS29S4S2fS5S71A1S32A2A1A1A2S11Sb3Sb6A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1Z11A2S1bZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZaA2S32A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZbA2S1bZ40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZcA2S1bZ3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZdA2S1bZ32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZeA2S1bZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZfA2S1bZ0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_xF : ltac2:(tb__ "0|0|
S0SdS2aS1aS4S2fS5S71A1S32A2A1A1S32A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_mF : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S71A1S32A2S32Z40000A3ScA5S11G0SbS6S87SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_mF__R <: R_mF__R = Some [r_mF_0]). Qed.
Lemma LN_mF : ltac2:(tb__ "0|0|
S0SdS1eS4SbfS2fS5S71A1S32A2S32Z40000A3A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_mF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4SbfS2fS5S71A1S32A2S32Z40000A3A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_mF : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S5S87A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSbS17SdeS32A1SeS17A1A3A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mFb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S5S87A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_mF : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S5S87A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mrF : ltac2:(tb__ "0|0|
S0SdS1dS4ScdS5S87A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mrF : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S87A1M4A1S4ScdG4A1A1A2S11G3S13G1G2SbG0S13S18S18SceS32A1S1bZ8000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mcF : ltac2:(tb__ "0|0|
S0SdS1dS4S73A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_msF : ltac2:(tb__ "0|1|
S0S12SfS17A1M0A1SedS73Sc5S46S73A1A3S11G0S45S73A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_msF : ltac2:(tb__ "0|0|
S0SdSecS73Sc5S46S73A1S45S73A1S69S6SaS5Sc6A4A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_msF : ltac2:(tb__ "0|0|
S0SdS67Sc7S1aS4S73A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_msF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S73A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_msF : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S73A1M0A1A1S1cG0A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_msF : ltac2:(tb__ "0|0|
S0SdSc2S19S25S1aS4Sc0S73S46S73A1S45S73A1A3A1A1A1S1cS4S73A1A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_rF : ltac2:(tb__ "0|0|
S0SdSe8S54S8bA1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rFb : ltac2:(tb__ "0|0|
S0SdS102U1S44S8bA1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rF : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S58S8bA1A1A1M0S14S17S6aS17Sc4S44S8bA1U2A2G0A3SbS17SdeS32A1SbS17SdfS32A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma pieceF_i : ltac2:(tb__ "0|0|
SfaS61S6dS103S32S84S89A6").
Proof.
  rewrite <- RF1_eq, <- DMF_eq, <- CMCF_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP.PF beg2 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cfm r_xF_0 r_mF_0
           R_xF LN_xF NX_xF W_xF D_xF SK_xF (inclb_incl _ _ XF_xFb) XX_xF NXc_xF IC_xF R17_xF R10_xF BEL_xF R11_xF R12_xF R13_xF R14_xF R15_xF
           R_mF LN_mF NX_mF SK_mF (inclb_incl _ _ XF_mFb) XX_mF W_mrF D_mrF _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCF_eq, ?DMF_eq; [exact W_mcF | exact E_msF | exact CHK_msF | exact NF_msF | exact NX_msF | exact FBC_msF | exact FBT_msF | exact ND_rF | apply Nat.leb_le; exact NO_rFb | exact OB_rF].
Qed.
Definition R_h__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ4172cSeS2cA1A3S89ScA5").
Local Strategy expand [R_h__R].
Definition r_h := Eval vm_compute in ((fun ro10__ : option (list leafA) => (match ro10__ with Some l => l | None => [] end)) R_h__R).
Definition r_h_0 := Eval vm_compute in (nth 0 r_h (mkLeafA rf1 RsCut)).
Lemma R_h : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ4172cSeS2cA1A3S89ScA5S11G0SbS6S86SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_h__R <: R_h__R = Some [r_h_0]). Qed.
Lemma LN_h : ltac2:(tb__ "0|0|
S0SdS1eS4S89A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_h : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S89A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma run_i : ltac2:(tb__ "0|0|
S100S89S5S86A1A2").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc ph r tp Q HC.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc FUEL [0x4172c] rf1 [r_h_0] ph r tp Q R_h LN_h NX_h).
  intros L r1 [<-|[]] _. exact (HC r1).
Qed.
Definition R_fhP__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SeS2cA1A3S5S83A1ScA5").
Local Strategy expand [R_fhP__R].
Definition r_flP := Eval vm_compute in ((fun ro12__ : option (list leafA) => (match ro12__ with Some l => l | None => [] end)) R_fhP__R).
Definition r_flP_0 := Eval vm_compute in (nth 0 r_flP (mkLeafA (la_state r_f_0) RsCut)).
Definition cl0P := Eval vm_compute in (cL0 (factsR e3r) (la_state r_flP_0)).
Definition R_l1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS78A1ScA5").
Local Strategy expand [R_l1P__R].
Definition r_lP := Eval vm_compute in ((fun ro11__ : option (list leafA) => (match ro11__ with Some l => l | None => [] end)) R_l1P__R).
Definition r_lP_0 := Eval vm_compute in (nth 0 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition r_lP_1 := Eval vm_compute in (nth 1 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition nobFP := Eval vm_compute in (length (ss_objs (ax_S cl0P))).
Definition s_fbkP := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lP_0) nobFP)) (ax_S cl0P)).
Definition s_finP := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flP_0)) (ax_S cl0P)).
Definition R_fjP__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7fA1S7dA2A2ScA5").
Local Strategy expand [R_fjP__R].
Definition r_jP := Eval vm_compute in ((fun ro13__ : option (list leafA) => (match ro13__ with Some l => l | None => [] end)) R_fjP__R).
Definition r_jP_0 := Eval vm_compute in (nth 0 r_jP (mkLeafA (cXL (factsR e3r) (keepn (la_state r_lP_1) nobFP)) RsCut)).
Lemma SK_lP : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S78A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_lP : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S78A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_lPb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S78A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_lP : ltac2:(tb__ "0|0|
S0SdS68S1aS4S78A1A1S50A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_l1P : ltac2:(tb__ "0|0|
S0SdS1dS4S3cS78A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_l1P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS78A1ScA5S11G0SbS6S98SbS6S7fSeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_l1P__R <: R_l1P__R = Some [r_lP_0; r_lP_1]). Qed.
Lemma LN_l1P : ltac2:(tb__ "0|0|
S0SdS1eS4S3cS78A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_fbP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S98A1A1A1M0S14S17S6aS17S7dG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_fxP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S7fA1A1A1M0S14S17S6aS17S7dG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fbkP : ltac2:(tb__ "0|0|
S0SdS8S35S5S98A1S7dA2S78S94A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fbkP : ltac2:(tb__ "0|0|
S0SdS6cS94S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk0P : ltac2:(tb__ "0|0|
S0S18S6bS94S3aA2S20Sb1S21S3aA1S1bZ1A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk2P : ltac2:(tb__ "0|0|
S0S18S6bS94S41A2S20Sb1S21S41A1S21SbbA1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk3P : ltac2:(tb__ "0|0|
S0S18S6bS94S47A2S20Sb1Sd3S20Sb4S20Sb5S21S3aA1S1bZffffffffffffffffA1A3S1bZ2A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_fbPb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd1SeS19A1A3S1cS4S5S98A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_fxPb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd1A1SeS19A1A3S1cS4S5S7fA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fhP : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SeS2cA1A3S5S83A1ScA5S11G0SbS6Sa6SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fhP__R <: R_fhP__R = Some [r_flP_0]). Qed.
Lemma LN_fhP : ltac2:(tb__ "0|0|
S0SdS1eS4S5S83A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fhP : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S83A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_finP : ltac2:(tb__ "0|0|
S0SdS8S5Sa6A1S78S96A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_finP : ltac2:(tb__ "0|0|
S0SdS6cS96S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in0P : ltac2:(tb__ "0|0|
S0S18S6bS96S3aA2S1bZ1A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in2P : ltac2:(tb__ "0|0|
S0S18S6bS96S41A2S59A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in3P : ltac2:(tb__ "0|0|
S0S18S6bS96S47A2S20Sb1Sd3S1bN4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_xlP : ltac2:(tb__ "0|0|
S0SdS1dS4S37S2eS5eA1S35S5S7fA1S7dA2A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xlP : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S35S5S7fA1S7dA2M4A1S4S37S2eS5eA1G4A2A1A2S11G3S13G1G2SeG0A1SbS19S4dSbS19S4eSeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_xlP : ltac2:(tb__ "0|1|
S0SdS68S1aS4S37S2eS5eA1S35S5S7fA1S7dA2M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fjP : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7fA1S7dA2A2ScA5S11G0SbS6S8eSeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fjP__R <: R_fjP__R = Some [r_jP_0]). Qed.
Lemma LN_fxlP : ltac2:(tb__ "0|0|
S0SdS1eS4S37S2eS5eA1S35S5S7fA1S7dA2A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fxlP : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S37S2eS5eA1S35S5S7fA1S7dA2A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fillP_i : ltac2:(tb__ "0|0|
Sf8S61S6dS5S83A1S5S8eA1A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph PQ HDEF r tp Q HC.
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE PF ph PQ HDEF FUEL cl0P r_lP_0 r_lP_1 nobFP s_fbkP SK_lP XX_lP (inclb_incl _ _ XF_lPb) NX_lP W_l1P R_l1P LN_l1P
           OB_fbP OB_fxP ENT_fbkP SID_fbkP S_bk0P S_bk2P S_bk3P (In_of_inclb _ _ FB_fbPb) (In_of_inclb _ _ FB_fxPb) e3r (la_state r_f_0) r_flP_0 r_jP_0 s_finP
           R_fhP LN_fhP NX_fhP ENT_finP SID_finP S_in0P S_in2P S_in3P W_xlP D_xlP NXe_xlP R_fjP LN_fxlP NX_fxlP r tp Q HC).
Qed.
Definition R_fhM__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SeS2cA1A3S5S86A1ScA5").
Local Strategy expand [R_fhM__R].
Definition r_flM := Eval vm_compute in ((fun ro15__ : option (list leafA) => (match ro15__ with Some l => l | None => [] end)) R_fhM__R).
Definition r_flM_0 := Eval vm_compute in (nth 0 r_flM (mkLeafA (la_state r_h_0) RsCut)).
Definition cl0M := Eval vm_compute in (cL0 (factsR e3r) (la_state r_flM_0)).
Definition R_l1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS77A1ScA5").
Local Strategy expand [R_l1M__R].
Definition r_lM := Eval vm_compute in ((fun ro14__ : option (list leafA) => (match ro14__ with Some l => l | None => [] end)) R_l1M__R).
Definition r_lM_0 := Eval vm_compute in (nth 0 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition r_lM_1 := Eval vm_compute in (nth 1 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition nobFM := Eval vm_compute in (length (ss_objs (ax_S cl0M))).
Definition s_fbkM := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lM_0) nobFM)) (ax_S cl0M)).
Definition s_finM := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flM_0)) (ax_S cl0M)).
Definition R_fjM__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7eA1S7cA2A2ScA5").
Local Strategy expand [R_fjM__R].
Definition r_jM := Eval vm_compute in ((fun ro16__ : option (list leafA) => (match ro16__ with Some l => l | None => [] end)) R_fjM__R).
Definition r_jM_0 := Eval vm_compute in (nth 0 r_jM (mkLeafA (cXL (factsR e3r) (keepn (la_state r_lM_1) nobFM)) RsCut)).
Lemma SK_lM : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S77A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_lM : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S77A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_lMb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S77A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_lM : ltac2:(tb__ "0|0|
S0SdS68S1aS4S77A1A1S50A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_l1M : ltac2:(tb__ "0|0|
S0SdS1dS4S3cS77A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_l1M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS77A1ScA5S11G0SbS6S97SbS6S7eSeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_l1M__R <: R_l1M__R = Some [r_lM_0; r_lM_1]). Qed.
Lemma LN_l1M : ltac2:(tb__ "0|0|
S0SdS1eS4S3cS77A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_fbM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S97A1A1A1M0S14S17S6aS17S7cG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_fxM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S7eA1A1A1M0S14S17S6aS17S7cG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fbkM : ltac2:(tb__ "0|0|
S0SdS8S35S5S97A1S7cA2S77S93A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fbkM : ltac2:(tb__ "0|0|
S0SdS6cS93S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk0M : ltac2:(tb__ "0|0|
S0S18S6bS93S3aA2S20Sb1S21S3aA1S1bZ1A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk2M : ltac2:(tb__ "0|0|
S0S18S6bS93S41A2S20Sb1S21S41A1S21SbbA1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk3M : ltac2:(tb__ "0|0|
S0S18S6bS93S47A2S20Sb1Sd3S20Sb4S20Sb5S21S3aA1S1bZffffffffffffffffA1A3S1bZ2A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_fbMb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd1SeS19A1A3S1cS4S5S97A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_fxMb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd1A1SeS19A1A3S1cS4S5S7eA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fhM : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SeS2cA1A3S5S86A1ScA5S11G0SbS6Sa5SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fhM__R <: R_fhM__R = Some [r_flM_0]). Qed.
Lemma LN_fhM : ltac2:(tb__ "0|0|
S0SdS1eS4S5S86A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fhM : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S86A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_finM : ltac2:(tb__ "0|0|
S0SdS8S5Sa5A1S77S95A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_finM : ltac2:(tb__ "0|0|
S0SdS6cS95S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in0M : ltac2:(tb__ "0|0|
S0S18S6bS95S3aA2S1bZ1A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in2M : ltac2:(tb__ "0|0|
S0S18S6bS95S41A2S59A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in3M : ltac2:(tb__ "0|0|
S0S18S6bS95S47A2S20Sb1Sd3S1bN4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_xlM : ltac2:(tb__ "0|0|
S0SdS1dS4S37S2eS5eA1S35S5S7eA1S7cA2A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xlM : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S35S5S7eA1S7cA2M4A1S4S37S2eS5eA1G4A2A1A2S11G3S13G1G2SeG0A1SbS19S4dSbS19S4eSeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_xlM : ltac2:(tb__ "0|1|
S0SdS68S1aS4S37S2eS5eA1S35S5S7eA1S7cA2M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fjM : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7eA1S7cA2A2ScA5S11G0SbS6S8dSeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fjM__R <: R_fjM__R = Some [r_jM_0]). Qed.
Lemma LN_fxlM : ltac2:(tb__ "0|0|
S0SdS1eS4S37S2eS5eA1S35S5S7eA1S7cA2A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fxlM : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S37S2eS5eA1S35S5S7eA1S7cA2A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fillM_i : ltac2:(tb__ "0|0|
Sf8S61S6dS5S86A1S5S8dA1A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph PQ HDEF r tp Q HC.
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE PF ph PQ HDEF FUEL cl0M r_lM_0 r_lM_1 nobFM s_fbkM SK_lM XX_lM (inclb_incl _ _ XF_lMb) NX_lM W_l1M R_l1M LN_l1M
           OB_fbM OB_fxM ENT_fbkM SID_fbkM S_bk0M S_bk2M S_bk3M (In_of_inclb _ _ FB_fbMb) (In_of_inclb _ _ FB_fxMb) e3r (la_state r_h_0) r_flM_0 r_jM_0 s_finM
           R_fhM LN_fhM NX_fhM ENT_finM SID_finM S_in0M S_in2M S_in3M W_xlM D_xlM NXe_xlM R_fjM LN_fxlM NX_fxlM r tp Q HC).
Qed.
Definition R_t0P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8eA1ScA5").
Local Strategy expand [R_t0P__R].
Definition r_t0P := Eval vm_compute in ((fun ro18__ : option (list leafA) => (match ro18__ with Some l => l | None => [] end)) R_t0P__R).
Definition r_t0P_0 := Eval vm_compute in (nth 0 r_t0P (mkLeafA (la_state r_jP_0) RsCut)).
Definition ct0P := Eval vm_compute in (cT0 (la_state r_t0P_0)).
Definition R_t1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7bA1ScA5").
Local Strategy expand [R_t1P__R].
Definition r_t1P := Eval vm_compute in ((fun ro17__ : option (list leafA) => (match ro17__ with Some l => l | None => [] end)) R_t1P__R).
Definition r_t1P_0 := Eval vm_compute in (nth 0 r_t1P (mkLeafA (cT1 ct0P) RsCut)).
Definition r_t1P_1 := Eval vm_compute in (nth 1 r_t1P (mkLeafA (cT1 ct0P) RsCut)).
Definition s_inP := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0P_0)) (ax_S ct0P)).
Definition s_bkP := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1P_0) nob)) (ax_S ct0P)).
Lemma SK_tP : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S7bA1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tP : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S7bA1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tPb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S7bA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tP : ltac2:(tb__ "0|0|
S0SdS68S1aS4S7bA1A1S52A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1P : ltac2:(tb__ "0|0|
S0SdS1dS4S3dS7bA1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7bA1ScA5S11G0SbS6S9aSbS6Sa2SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1P__R <: R_t1P__R = Some [r_t1P_0; r_t1P_1]). Qed.
Lemma LN_t1P : ltac2:(tb__ "0|0|
S0SdS1eS4S3dS7bA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S9aA1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5Sa2A1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkP : ltac2:(tb__ "0|0|
S0SdS8S35S5S9aA1S63A2S7bS9cA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkP : ltac2:(tb__ "0|0|
S0SdS6cS9cS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4P : ltac2:(tb__ "0|0|
S0S18S6bS9cS39A2S20Sb1S21S39A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6P : ltac2:(tb__ "0|0|
S0S18S6bS9cS42A2S20Sb1S21S42A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bPb : ltac2:(tb__ "0|0|
S0SdS65SbS19S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3SeS19A1A3S1cS4S5S9aA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xPb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3A1SeS19A1A3S1cS4S5Sa2A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8eA1ScA5S11G0SbS6Sa8SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0P__R <: R_t0P__R = Some [r_t0P_0]). Qed.
Lemma LN_t0P : ltac2:(tb__ "0|0|
S0SdS1eS4S5S8eA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0P : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S8eA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inP : ltac2:(tb__ "0|0|
S0SdS8S5Sa8A1S7bS9eA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inP : ltac2:(tb__ "0|0|
S0SdS6cS9eS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4P : ltac2:(tb__ "0|0|
S0S18S6bS9eS39A2S20Sb1SbcS1bZ10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6P : ltac2:(tb__ "0|0|
S0S18S6bS9eS42A2Sf6A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlP := Eval vm_compute in (keepn (la_state r_t1P_1) nob).
Definition R_9P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ40cc8SeS2cA1A3Sa0ScA5").
Local Strategy expand [R_9P__R].
Definition r_9P := Eval vm_compute in ((fun ro19__ : option (list leafA) => (match ro19__ with Some l => l | None => [] end)) R_9P__R).
Definition r_9P_0 := Eval vm_compute in (nth 0 r_9P (mkLeafA xlP RsCut)).
Definition cellsfP := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9P_0) icc))) O_ri)).
Definition x3P := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9P_0) icc))).
Definition r_zP := Eval vm_compute in (match sym_runA segsA FUEL [0x3c480] x3P true with Some l => l | None => [] end).
Definition r_zP_0 := Eval vm_compute in (nth 0 r_zP (mkLeafA x3P RsCut)).
Lemma R_9P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ40cc8SeS2cA1A3Sa0ScA5S11G0SbS6S76SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9P__R <: R_9P__R = Some [r_9P_0]). Qed.
Lemma LN_9P : ltac2:(tb__ "0|0|
S0SdS1eS4Sa0A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9P : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4Sa0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x1P : ltac2:(tb__ "0|0|
S0SdS1dS4S33S5S76A1S60A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x1P : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S76A1M4A1S4S33G4S60A2A1A2S11G3S13G1G2SbG0S13S18S18S55S4bA4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1P : ltac2:(tb__ "0|1|
S0SdS68S1aS4S33S5S76A1M0S60A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1P : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S33S5S76A1S60A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1P : ltac2:(tb__ "0|0|
S0S12S17A1Sc3S17S1fS4S33S5S76A1S60A2A1A1S60A3S11S17S51A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1P : ltac2:(tb__ "0|2|
S0SfS17A1S1fS4S33S5S76A1S60A2M0A1A1M1S14S17S6aS17Sc4S44G0A1U2A2G1A3SbS17S38SbS17S101Sa4A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1P : ltac2:(tb__ "0|0|
S0SdS57Sa4Sf3S5aSf4Sf5A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2P : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S34S33S5S76A1S60A2A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSeS17A1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2P : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S34S33S5S76A1S60A2A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Pb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S34S33S5S76A1S60A2A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aP : ltac2:(tb__ "0|0|
S0SdS1dS4S53S34S33S5S76A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bP : ltac2:(tb__ "0|0|
S0SdS1dS4S48S34S33S5S76A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3P : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S48S34S33S5S76A1S60A2A1A1A1M0A1A1S14S19S4cS1cG0A1A3A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_zP : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3c480SeS2cA1A3S43S34S33S5S76A1S60A2A1A1ScA5S11G0SbS6SaaSeS6A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_zP : ltac2:(tb__ "0|0|
S0SdS1eS4S43S34S33S5S76A1S60A2A1A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_zP : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S43S34S33S5S76A1S60A2A1A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s_xP := Eval vm_compute in (s_exit (la_state r_zP_0) e3p).
Lemma ENT_xP : ltac2:(tb__ "0|0|
S0SdS8S5SaaA1S64Sb0A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SX_xP : sx_okb s_xP = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S149_xP : wsub_get s_xP 149%positive = vK.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S159_xP : wsub_get s_xP 159%positive = vCHX.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition pop_P A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0P r_t1P_0 r_t1P_1 nob s_bkP
    SK_tP XX_tP (inclb_incl _ _ XF_tPb) NX_tP W_t1P R_t1P LN_t1P OB_bP OB_xP ENT_bkP SID_bkP S_bk4P S_bk6P (In_of_inclb _ _ FB_bPb) (In_of_inclb _ _ FB_xPb)
    (la_state r_jP_0) r_t0P_0 s_inP e_srcP R_t0P LN_t0P NX_t0P ENT_inP SID_inP S_in4P S_in6P.
Definition exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE phX PHX HFILLX Hini e16P vMFA e32P e48P HRIv HLEN HIDC FUEL xlP r_9P_0 r_zP_0 icc cellsfP
    R_9P LN_9P NX_9P W_x1P D_x1P NX_x1P XX_1P IC_1P OB_1P RI_1P SK_2P XX_2P (inclb_incl _ _ XF_2Pb) W_3aP W_3bP FB_3P R_zP LN_zP NX_zP.
Definition back_P CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLeOrPc rho HW HE phF HREB HMK HLEN e3p (la_state r_zP_0) s_xP ENT_xP SX_xP S149_xP S159_xP HPOP.
Definition R_t0M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8dA1ScA5").
Local Strategy expand [R_t0M__R].
Definition r_t0M := Eval vm_compute in ((fun ro21__ : option (list leafA) => (match ro21__ with Some l => l | None => [] end)) R_t0M__R).
Definition r_t0M_0 := Eval vm_compute in (nth 0 r_t0M (mkLeafA (la_state r_jM_0) RsCut)).
Definition ct0M := Eval vm_compute in (cT0 (la_state r_t0M_0)).
Definition R_t1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7aA1ScA5").
Local Strategy expand [R_t1M__R].
Definition r_t1M := Eval vm_compute in ((fun ro20__ : option (list leafA) => (match ro20__ with Some l => l | None => [] end)) R_t1M__R).
Definition r_t1M_0 := Eval vm_compute in (nth 0 r_t1M (mkLeafA (cT1 ct0M) RsCut)).
Definition r_t1M_1 := Eval vm_compute in (nth 1 r_t1M (mkLeafA (cT1 ct0M) RsCut)).
Definition s_inM := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0M_0)) (ax_S ct0M)).
Definition s_bkM := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1M_0) nob)) (ax_S ct0M)).
Lemma SK_tM : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S7aA1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tM : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S7aA1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tMb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S7aA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tM : ltac2:(tb__ "0|0|
S0SdS68S1aS4S7aA1A1S52A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1M : ltac2:(tb__ "0|0|
S0SdS1dS4S3dS7aA1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7aA1ScA5S11G0SbS6S99SbS6Sa1SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1M__R <: R_t1M__R = Some [r_t1M_0; r_t1M_1]). Qed.
Lemma LN_t1M : ltac2:(tb__ "0|0|
S0SdS1eS4S3dS7aA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S99A1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5Sa1A1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkM : ltac2:(tb__ "0|0|
S0SdS8S35S5S99A1S63A2S7aS9bA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkM : ltac2:(tb__ "0|0|
S0SdS6cS9bS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4M : ltac2:(tb__ "0|0|
S0S18S6bS9bS39A2S20Sb1S21S39A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6M : ltac2:(tb__ "0|0|
S0S18S6bS9bS42A2S20Sb1S21S42A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bMb : ltac2:(tb__ "0|0|
S0SdS65SbS19S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3SeS19A1A3S1cS4S5S99A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xMb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3A1SeS19A1A3S1cS4S5Sa1A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8dA1ScA5S11G0SbS6Sa7SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0M__R <: R_t0M__R = Some [r_t0M_0]). Qed.
Lemma LN_t0M : ltac2:(tb__ "0|0|
S0SdS1eS4S5S8dA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0M : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S8dA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inM : ltac2:(tb__ "0|0|
S0SdS8S5Sa7A1S7aS9dA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inM : ltac2:(tb__ "0|0|
S0SdS6cS9dS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4M : ltac2:(tb__ "0|0|
S0S18S6bS9dS39A2S20Sb1SbcS1bZ10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6M : ltac2:(tb__ "0|0|
S0S18S6bS9dS42A2Sf6A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlM := Eval vm_compute in (keepn (la_state r_t1M_1) nob).
Definition R_9M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ40cc8SeS2cA1A3S9fScA5").
Local Strategy expand [R_9M__R].
Definition r_9M := Eval vm_compute in ((fun ro22__ : option (list leafA) => (match ro22__ with Some l => l | None => [] end)) R_9M__R).
Definition r_9M_0 := Eval vm_compute in (nth 0 r_9M (mkLeafA xlM RsCut)).
Definition cellsfM := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9M_0) icc))) O_ri)).
Definition x3M := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9M_0) icc))).
Definition r_zM := Eval vm_compute in (match sym_runA segsA FUEL [0x3c480] x3M true with Some l => l | None => [] end).
Definition r_zM_0 := Eval vm_compute in (nth 0 r_zM (mkLeafA x3M RsCut)).
Lemma R_9M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ40cc8SeS2cA1A3S9fScA5S11G0SbS6S75SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9M__R <: R_9M__R = Some [r_9M_0]). Qed.
Lemma LN_9M : ltac2:(tb__ "0|0|
S0SdS1eS4S9fA1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9M : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S9fA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x1M : ltac2:(tb__ "0|0|
S0SdS1dS4S33S5S75A1S60A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x1M : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S75A1M4A1S4S33G4S60A2A1A2S11G3S13G1G2SbG0S13S18S18S55S4bA4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1M : ltac2:(tb__ "0|1|
S0SdS68S1aS4S33S5S75A1M0S60A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1M : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S33S5S75A1S60A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1M : ltac2:(tb__ "0|0|
S0S12S17A1Sc3S17S1fS4S33S5S75A1S60A2A1A1S60A3S11S17S51A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1M : ltac2:(tb__ "0|2|
S0SfS17A1S1fS4S33S5S75A1S60A2M0A1A1M1S14S17S6aS17Sc4S44G0A1U2A2G1A3SbS17S38SbS17S101Sa3A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1M : ltac2:(tb__ "0|0|
S0SdS57Sa3Sf3Sf7Sf4Sf5A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2M : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S34S33S5S75A1S60A2A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSeS17A1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2M : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S34S33S5S75A1S60A2A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Mb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S34S33S5S75A1S60A2A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aM : ltac2:(tb__ "0|0|
S0SdS1dS4S53S34S33S5S75A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bM : ltac2:(tb__ "0|0|
S0SdS1dS4S48S34S33S5S75A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3M : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S48S34S33S5S75A1S60A2A1A1A1M0A1A1S14S19S4cS1cG0A1A3A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_zM : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3c480SeS2cA1A3S43S34S33S5S75A1S60A2A1A1ScA5S11G0SbS6Sa9SeS6A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_zM : ltac2:(tb__ "0|0|
S0SdS1eS4S43S34S33S5S75A1S60A2A1A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_zM : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S43S34S33S5S75A1S60A2A1A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s_xM := Eval vm_compute in (s_exit (la_state r_zM_0) e3p).
Lemma ENT_xM : ltac2:(tb__ "0|0|
S0SdS8S5Sa9A1S64SafA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SX_xM : sx_okb s_xM = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S149_xM : wsub_get s_xM 149%positive = vK.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S159_xM : wsub_get s_xM 159%positive = vCHX.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition pop_M A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0M r_t1M_0 r_t1M_1 nob s_bkM
    SK_tM XX_tM (inclb_incl _ _ XF_tMb) NX_tM W_t1M R_t1M LN_t1M OB_bM OB_xM ENT_bkM SID_bkM S_bk4M S_bk6M (In_of_inclb _ _ FB_bMb) (In_of_inclb _ _ FB_xMb)
    (la_state r_jM_0) r_t0M_0 s_inM e_srcP R_t0M LN_t0M NX_t0M ENT_inM SID_inM S_in4M S_in6M.
Definition exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE phX PHX HFILLX Hini e16P e24M e32P e48P HRIv HLEN HIDC FUEL xlM r_9M_0 r_zM_0 icc cellsfM
    R_9M LN_9M NX_9M W_x1M D_x1M NX_x1M XX_1M IC_1M OB_1M RI_1M SK_2M XX_2M (inclb_incl _ _ XF_2Mb) W_3aM W_3bM FB_3M R_zM LN_zM NX_zM.
Definition back_M CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLeOrPc rho HW HE phF HREB HMK HLEN e3p (la_state r_zM_0) s_xM ENT_xM SX_xM S149_xM S159_xM HPOP.

Theorem refill_populate_i : ltac2:(tb__ "0|4|
SfS10S2cS2cA2A1M0G0Se3S6eSfS10SaSeeA2A1F_;F_;S108R3R2R1A3SaS0SaR1S64A3Se3S6eS24SfS110Q40M1A1A1M2Se2Se2OF_;F_;Sc1R4R1A2S6fR5A1S0SdSe4R7A1ScA3SebS2dSc7R6R5RcR8R7A2A5Se2S24Se0ScaRbR2R8R1S61S6dR9A7SdbRcR3A2Sc8S3S0Sc8R1SffA3S0Sc8R1Sf9A3A2S111G1S2bR6PcA2A2S2cS109R1A1S2cS10aR11R2A2Se5S2S0Sc8R5Sf9A3S10dSe7R1A1S10eZ4S10cS10fS16S2cSe6R1A1A2A1ScbR12R9A2A2A2A2A2S24G2SfSe1A1Se0Sc9R17R16ReR14RdSfeRaScbR17ReA2S106R7A1A3R4R3R2R1AaS1S105S2dS107R18R8A2M3R5R4R2A5S70R1eR1dR18G3S28RfA1S28R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;Frb;Se3S24G2S24RaSeaS2dS10bS61S6dR4RdR3A5R10R1R2A5SebS2dSc7R3R2R12R4RdA2A5A2FrX;Ftp';Frho';FA';S24Se0S24ScaReR3RbR2S61S6dRcA7RbSeaS2dSc9RfReR4RcR3SccA6S5S62A1R2RcA5R7A2F_;Fr';Fmd0;Frb;F_;F_;TQ;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;FE3P;FHPF;FPFam;FXGL;FCST;").
Proof.
  intros CST XGL PFam HPF E3P ->.
  apply (refill_populate CST XGL PFam W0 UStopLeOrPc (la_state r_2_0) cp2c ru1 (la_state r_f_0) (la_state r_f_1) cfm rf1 (la_state r_h_0)
           (la_state r_jP_0) xlP (la_state r_zP_0) (la_state r_jM_0) xlM (la_state r_zM_0) e3p head_i pieceU_i mid_i fm_i pieceF_i run_i fillP_i fillM_i).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_P A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_M A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_P CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_M CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
Qed.
End SpineCallocRp1.

(* [comment removed for export] *)
Module SpineCallocRp1u.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "entailsA"; "ax_X"; "axst"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "SLit"; "ss_facts"; "swf"; "ss_lenient"; "ss_objs"; "SAlu"; "SVar"; "reg_sv"; "SPNot"; "valuation"; "sprop_below"; "SPBranch"; "SPUle"; "rm"; "ss_pc"; "sv_below"; "rw"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "factsR"; "cX"; "GR"; "beg1"; "beg2"; "cE1"; "cE2"; "keepn"; "cP2"; "cXL"; "O_pcm"; "PV4"; "LV0"; "O_ri"; "cL1"; "cT1"; "cD"; "cPa"; "cPb"; "LV2"; "PV6"; "cE3"; "nobj"; "rMS"; "sMS"; "LV3"; "cE3b"; "vMU"; "cFm"; "vK"; "F_x"; "HINT_au"; "HINT_k"; "HINT_map"; "LNX"; "O_pccK"; "PNX"; "cE3a"; "idx_rot"; "k_e"; "relM"; "ri_has"; "rotM"; "vAU"; "vMFA"; "F_new"; "vNEW"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineCallocRi1u"; "e3r"; "FUEL"; "icc"; "W0"; "r_2_0"; "nob"; "e3p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLeOrPc"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dm.SpineCallocRp1u"; "r_xF_0"; "r_xU_0"; "cmcF"; "cmcU"; "r_9M_0"; "r_9P_0"; "cl0M"; "cl0P"; "cp2c"; "ct0M"; "ct0P"; "nobFM"; "nobFP"; "r_lM_1"; "r_lP_1"; "r_p1_0"; "r_p1_1"; "r_d_0"; "r_f_0"; "cfm"; "r_f_1"; "r_h_0"; "r_mF_0"; "r_mU_0"; "rf1"; "ru1"; "dmF"; "dmU"; "r_jM_0"; "r_jP_0"; "r_p2a_0"; "r_p2a_1"; "r_p2b_0"; "r_p2b_1"; "s_fbkM"; "s_fbkP"; "s_finM"; "s_finP"; "r_lM_0"; "r_lP_0"; "r_t1M_0"; "r_t1P_0"; "s_bkM"; "s_bkP"; "s_inM"; "s_inP"; "xlM"; "xlP"; "r_t1M_1"; "r_t1P_1"; "cellsfM"; "cellsfP"; "r_flM_0"; "r_flP_0"; "r_t0M_0"; "r_t0P_0"; "r_zM_0"; "r_zP_0"; "sa0"; "sa1"; "sb0"; "sb1"; "s_xM"; "s_xP"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "instr"; "ALU_SLL"; "ALU_XOR"; "Ecall"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "O_pcc0"; "O_st"; "V_SIZE"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "memset_post"; "TRok"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "phase"; "JR"; "entryR"; "gh_new"; "ph0";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocR10"; "cMr"; "a2_e"; "cMc"; "dMSf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR13"; "F_lt"; "O_fcell"; "faend_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7"; "F_mu0"; "F_hi"; "x19_e0"; "x19_e1"; "popfacts"; "size_e_hi"; "size_e_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9"; "O_piece"; "O_shp"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "call_checkA"; "entails_frA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR11"; "a0_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR12"; "F_geu"; "new_e"; "rup_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocR14"; "e16P"; "e32P"; "e48P"; "e_srcP"; "e24M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15"; "fillT"; "phUF3"; "pieceT"; "fmT"; "headT"; "midT"; "phFin"; "phU3"; "runT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4"; "O_rif"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP"; "PF"; "PU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineCallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocR14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineCallocRi1u.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_p1__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ415c0SbS2cZ41600SeS2cA1A3A3S5S62A1ScA5").
Local Strategy expand [R_p1__R].
Definition r_p1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_p1__R).
Definition r_p1_0 := Eval vm_compute in (nth 0 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition r_p1_1 := Eval vm_compute in (nth 1 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition R_p2a__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41630SeS2cA1A3S3fS2eS5eA1S5S80A1A2ScA5").
Local Strategy expand [R_p2a__R].
Definition r_p2a := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_p2a__R).
Definition r_p2a_0 := Eval vm_compute in (nth 0 r_p2a (mkLeafA (cPa (factsR e3r) (la_state r_p1_0)) RsCut)).
Definition r_p2a_1 := Eval vm_compute in (nth 1 r_p2a (mkLeafA (cPa (factsR e3r) (la_state r_p1_0)) RsCut)).
Definition R_p2b__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41630SeS2cA1A3S40S2eS5eA1S5S81A1A2ScA5").
Local Strategy expand [R_p2b__R].
Definition r_p2b := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_p2b__R).
Definition r_p2b_0 := Eval vm_compute in (nth 0 r_p2b (mkLeafA (cPb (factsR e3r) (la_state r_p1_1)) RsCut)).
Definition r_p2b_1 := Eval vm_compute in (nth 1 r_p2b (mkLeafA (cPb (factsR e3r) (la_state r_p1_1)) RsCut)).
Definition cp2c := Eval vm_compute in (cP2c (factsR e3r) (la_state r_p2a_1)).
Lemma FP_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S26Sb7S5dS4bA3SeS19A1A3S1cS4S5S62A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p1 : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ415c0SbS2cZ41600SeS2cA1A3A3S5S62A1ScA5S11G0SbS6S80SbS6S81SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p1__R <: R_p1__R = Some [r_p1_0; r_p1_1]). Qed.
Lemma LN_p1 : ltac2:(tb__ "0|0|
S0SdS1eS4S5S62A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p1 : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S62A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd8SeS19A1A3S1cS4S5S80A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd8A1SeS19A1A3S1cS4S5S81A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_pa : ltac2:(tb__ "0|0|
S0SdS1dS4S3fS2eS5eA1S5S80A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_pa : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S80A1M4A1S4S3fS2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SdcS21SbbA1A4SeG0A1A3SbS19S4fSbS19S27S49S1bZdffc0000A1A2SeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_pa : ltac2:(tb__ "0|1|
S0SdS68S1aS4S3fS2eS5eA1S5S80A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_pb : ltac2:(tb__ "0|0|
S0SdS1dS4S40S2eS5eA1S5S81A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_pb : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S81A1M4A1S4S40S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SddS21SbbA1A4SeG0A1A3SbS19S4fSbS19S27S49S1bZdffc0000A1A2SeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_pb : ltac2:(tb__ "0|1|
S0SdS68S1aS4S40S2eS5eA1S5S81A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p2a : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41630SeS2cA1A3S3fS2eS5eA1S5S80A1A2ScA5S11G0SbS6S8fSbS6S90SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p2a__R <: R_p2a__R = Some [r_p2a_0; r_p2a_1]). Qed.
Lemma LN_p2a : ltac2:(tb__ "0|0|
S0SdS1eS4S3fS2eS5eA1S5S80A1A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p2a : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S3fS2eS5eA1S5S80A1A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p2b : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41630SeS2cA1A3S40S2eS5eA1S5S81A1A2ScA5S11G0SbS6S91SbS6S92SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p2b__R <: R_p2b__R = Some [r_p2b_0; r_p2b_1]). Qed.
Lemma LN_p2b : ltac2:(tb__ "0|0|
S0SdS1eS4S40S2eS5eA1S5S81A1A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p2b : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S40S2eS5eA1S5S81A1A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa0_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd7SeS19A1A3S1cS4S5S8fA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_a0 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S8fA1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a0 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S8fA1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18Sd9S1bZ40000A1A4SbG0S13S18S18S1bZ0A1S49A4SeG0A1A3A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a0 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S8fA1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sa0 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2a_0))) (ax_S cp2c)).
Lemma ENT_a0 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S8fA1A2S79SabA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_a0 : ltac2:(tb__ "0|0|
S0SdS6cSabS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fa1_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd7A1SeS19A1A3S1cS4S5S90A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_a1 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S90A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a1 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S90A1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SdaS1bZ40000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a1 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S90A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sa1 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2a_1))) (ax_S cp2c)).
Lemma ENT_a1 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S90A1A2S79SacA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_a1 : ltac2:(tb__ "0|0|
S0SdS6cSacS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb0_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd7SeS19A1A3S1cS4S5S91A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S91A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S91A1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18Sd9S1bZ40000A1A4SbG0S13S18S18S1bZ0A1S49A4SeG0A1A3A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S91A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sb0 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2b_0))) (ax_S cp2c)).
Lemma ENT_b0 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S91A1A2S79SadA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_b0 : ltac2:(tb__ "0|0|
S0SdS6cSadS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fb1_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd7A1SeS19A1A3S1cS4S5S92A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0SdS1dS4S36S2eS5eA1S5S92A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S92A1M4A1S4S36S2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18SdaS1bZ40000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0SdS68S1aS4S36S2eS5eA1S5S92A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sb1 := Eval vm_compute in (infer_sub GR (ax_S (cP2 (factsR e3r) (la_state r_p2b_1))) (ax_S cp2c)).
Lemma ENT_b1 : ltac2:(tb__ "0|0|
S0SdS8S36S2eS5eA1S5S92A1A2S79SaeA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_b1 : ltac2:(tb__ "0|0|
S0SdS6cSaeS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma head_i : ltac2:(tb__ "0|0|
SfcS61S6dS5S62A1S79A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE HC.
  exact (populate_head A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HE FUEL e3r (la_state r_2_0) r_p1_0 r_p1_1 r_p2a_0 r_p2a_1 r_p2b_0 r_p2b_1 cp2c sa0 sa1 sb0 sb1
           (In_of_inclb _ _ FP_inb) R_p1 LN_p1 NX_p1 (In_of_inclb _ _ Fa_inb) (In_of_inclb _ _ Fb_inb) W_pa D_pa NXe_pa W_pb D_pb NXe_pb R_p2a LN_p2a NX_p2a R_p2b LN_p2b NX_p2b
           (In_of_inclb _ _ Fa0_inb) (In_of_inclb _ _ Fa1_inb) (In_of_inclb _ _ Fb0_inb) (In_of_inclb _ _ Fb1_inb) W_a0 W_a1 W_b0 W_b1 D_a0 D_a1 D_b0 D_b1 NXe_a0 NXe_a1 NXe_b0 NXe_b1
           ENT_a0 ENT_a1 ENT_b0 ENT_b1 SID_a0 SID_a1 SID_b0 SID_b1 r tp Q HC).
Qed.
Definition R_xU__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ7050cSeS2cA1A3S79ScA5").
Local Strategy expand [R_xU__R].
Definition r_xU := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_xU__R).
Definition r_xU_0 := Eval vm_compute in (nth 0 r_xU (mkLeafA cp2c RsCut)).
Definition R_mU__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S72A1S31A2S31Z40000A3ScA5").
Local Strategy expand [R_mU__R].
Definition r_mU := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) R_mU__R).
Definition r_mU_0 := Eval vm_compute in (nth 0 r_mU (mkLeafA (commit_post (cX (la_state r_xU_0) beg1) beg1 262144) RsCut)).
Definition cmcU := Eval vm_compute in (cMc (la_state r_mU_0) beg1).
Lemma CMCU_eq : ltac2:(tb__ "0|0|
S0SaScfS5S88A1S31A2S74A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition dmU := Eval vm_compute in (dMSf cmcU).
Lemma DMU_eq : ltac2:(tb__ "0|0|
S0SaSd0S74A1S8cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition ru1 := Eval vm_compute in (relM dmU).
Lemma RU1_eq : ltac2:(tb__ "0|0|
S0SaS56S8cA1S8aA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R_xU : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ7050cSeS2cA1A3S79ScA5S11G0SbS6S72SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_xU__R <: R_xU__R = Some [r_xU_0]). Qed.
Lemma LN_xU : ltac2:(tb__ "0|0|
S0SdS1eS4S79A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_xU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S79A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_xU : ltac2:(tb__ "0|0|
S0SdS1dS4S2fS5S72A1S31A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xU : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S72A1M4A1S4S2fG4S31A2A1A2S11G3S13G1G2SbG0S13S18S18SefS31A1S31A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_xU : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S2fS5S72A1S31A2A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xUb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S2fS5S72A1S31A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_xU : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S2fS5S72A1S31A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXc_xU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S2fS5S72A1S31A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_xU : ltac2:(tb__ "0|0|
S0S12Sb3A1Se9S2dS29S4S2fS5S72A1S31A2A1A1A2S11Sb3Sb6A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1Z11A2S1bZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZaA2S31A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZbA2S1bZ40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZcA2S1bZ3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZdA2S1bZ32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZeA2S1bZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_xU : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S72A1S31A2A1ZfA2S1bZ0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_xU : ltac2:(tb__ "0|0|
S0SdS2aS1aS4S2fS5S72A1S31A2A1A1S31A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_mU : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S72A1S31A2S31Z40000A3ScA5S11G0SbS6S88SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_mU__R <: R_mU__R = Some [r_mU_0]). Qed.
Lemma LN_mU : ltac2:(tb__ "0|0|
S0SdS1eS4SbfS2fS5S72A1S31A2S31Z40000A3A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_mU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4SbfS2fS5S72A1S31A2S31Z40000A3A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_mU : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S5S88A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSbS17SdeS31A1SeS17A1A3A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mUb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S5S88A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_mU : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S5S88A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mrU : ltac2:(tb__ "0|0|
S0SdS1dS4ScdS5S88A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mrU : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S88A1M4A1S4ScdG4A1A1A2S11G3S13G1G2SbG0S13S18S18SceS31A1S1bZ8000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mcU : ltac2:(tb__ "0|0|
S0SdS1dS4S74A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_msU : ltac2:(tb__ "0|1|
S0S12SfS17A1M0A1SedS74Sc5S46S74A1A3S11G0S45S74A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_msU : ltac2:(tb__ "0|0|
S0SdSecS74Sc5S46S74A1S45S74A1S69S6SaS5Sc6A4A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_msU : ltac2:(tb__ "0|0|
S0SdS67Sc7S1aS4S74A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_msU : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S74A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_msU : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S74A1M0A1A1S1cG0A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_msU : ltac2:(tb__ "0|0|
S0SdSc2S19S25S1aS4Sc0S74S46S74A1S45S74A1A3A1A1A1S1cS4S74A1A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_rU : ltac2:(tb__ "0|0|
S0SdSe8S54S8cA1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rUb : ltac2:(tb__ "0|0|
S0SdS102U1S44S8cA1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rU : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S58S8cA1A1A1M0S14S17S6aS17Sc4S44S8cA1U2A2G0A3SbS17SdeS31A1SbS17SdfS31A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma pieceU_i : ltac2:(tb__ "0|0|
SfaS61S6dS104S31S79S8aA6").
Proof.
  rewrite <- RU1_eq, <- DMU_eq, <- CMCU_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE PU beg1 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cp2c r_xU_0 r_mU_0
           R_xU LN_xU NX_xU W_xU D_xU SK_xU (inclb_incl _ _ XF_xUb) XX_xU NXc_xU IC_xU R17_xU R10_xU BEL_xU R11_xU R12_xU R13_xU R14_xU R15_xU
           R_mU LN_mU NX_mU SK_mU (inclb_incl _ _ XF_mUb) XX_mU W_mrU D_mrU _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCU_eq, ?DMU_eq; [exact W_mcU | exact E_msU | exact CHK_msU | exact NF_msU | exact NX_msU | exact FBC_msU | exact FBT_msU | exact ND_rU | apply Nat.leb_le; exact NO_rUb | exact OB_rU].
Qed.
Definition R_d__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ416f0SeS2cA1A3S8aScA5").
Local Strategy expand [R_d__R].
Definition r_d := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_d__R).
Definition r_d_0 := Eval vm_compute in (nth 0 r_d (mkLeafA ru1 RsCut)).
Definition R_f__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ3f270SbS2cZ4172cSeS2cA1A3A3S3eS2eS5eA1S5S82A1A2ScA5").
Local Strategy expand [R_f__R].
Definition r_f := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_f__R).
Definition r_f_0 := Eval vm_compute in (nth 0 r_f (mkLeafA (cD (factsR e3r) (la_state r_d_0)) RsCut)).
Definition r_f_1 := Eval vm_compute in (nth 1 r_f (mkLeafA (cD (factsR e3r) (la_state r_d_0)) RsCut)).
Lemma R_d : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ416f0SeS2cA1A3S8aScA5S11G0SbS6S82SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_d__R <: R_d__R = Some [r_d_0]). Qed.
Lemma LN_d : ltac2:(tb__ "0|0|
S0SdS1eS4S8aA1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_d : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S8aA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_d : ltac2:(tb__ "0|0|
S0SdS1dS4S3eS2eS5eA1S5S82A1A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_d : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S82A1M4A1S4S3eS2eS5eA1G4A2A1A2S11G3S13G1G2SbG0S13S18S18Sf1S5cA4SeG0A1A3S5bA4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_d : ltac2:(tb__ "0|1|
S0SdS68S1aS4S3eS2eS5eA1S5S82A1M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_f : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3f270SbS2cZ4172cSeS2cA1A3A3S3eS2eS5eA1S5S82A1A2ScA5S11G0SbS6S83SbS6S85SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_f__R <: R_f__R = Some [r_f_0; r_f_1]). Qed.
Lemma LN_f : ltac2:(tb__ "0|0|
S0SdS1eS4S3eS2eS5eA1S5S82A1A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_f : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S3eS2eS5eA1S5S82A1A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma F0_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sf0SeS19A1A3S1cS4S5S83A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Fm_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sf0A1SeS19A1A3S1cS4S5S85A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma mid_i : ltac2:(tb__ "0|0|
SfdS61S6dS8aS5S83A1S5S85A1A5").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph r tp Q. cbn zeta.
  exact (populate_mid A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HE PF ph FUEL e3r ru1 r_d_0 r_f_0 r_f_1 R_d LN_d NX_d W_d D_d NXe_d R_f LN_f NX_f (In_of_inclb _ _ F0_inb) (In_of_inclb _ _ Fm_inb) r tp Q).
Qed.
Definition cfm := Eval vm_compute in (cFm (la_state r_f_1)).
Lemma CFM_eq : ltac2:(tb__ "0|0|
S0SaS4aS5S85A1A1S84A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_fm : ltac2:(tb__ "0|0|
S0SdS1dS4S4aS5S85A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_fm : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S85A1M4A1S4S4aG4A1A1A2S11G3S13G1G2SbG0S13S18S18Sf2S20Sb1S5aS1bZ40000A1A3A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma fm_i : ltac2:(tb__ "0|0|
SfbS61S6dS5S85A1S84A4").
Proof.
  rewrite <- CFM_eq. intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph r tp Q. cbn zeta.
  exact (famap_restate A Kc rb tp0 md0 TR KIT W0 UStopLeOrPc rho HE PF (la_state r_f_1) W_fm D_fm ph r tp Q).
Qed.
Definition R_xF__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ7050cSeS2cA1A3S84ScA5").
Local Strategy expand [R_xF__R].
Definition r_xF := Eval vm_compute in ((fun ro8__ : option (list leafA) => (match ro8__ with Some l => l | None => [] end)) R_xF__R).
Definition r_xF_0 := Eval vm_compute in (nth 0 r_xF (mkLeafA cfm RsCut)).
Definition R_mF__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S71A1S32A2S32Z40000A3ScA5").
Local Strategy expand [R_mF__R].
Definition r_mF := Eval vm_compute in ((fun ro9__ : option (list leafA) => (match ro9__ with Some l => l | None => [] end)) R_mF__R).
Definition r_mF_0 := Eval vm_compute in (nth 0 r_mF (mkLeafA (commit_post (cX (la_state r_xF_0) beg2) beg2 262144) RsCut)).
Definition cmcF := Eval vm_compute in (cMc (la_state r_mF_0) beg2).
Lemma CMCF_eq : ltac2:(tb__ "0|0|
S0SaScfS5S87A1S32A2S73A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition dmF := Eval vm_compute in (dMSf cmcF).
Lemma DMF_eq : ltac2:(tb__ "0|0|
S0SaSd0S73A1S8bA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition rf1 := Eval vm_compute in (relM dmF).
Lemma RF1_eq : ltac2:(tb__ "0|0|
S0SaS56S8bA1S89A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R_xF : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ7050cSeS2cA1A3S84ScA5S11G0SbS6S71SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_xF__R <: R_xF__R = Some [r_xF_0]). Qed.
Lemma LN_xF : ltac2:(tb__ "0|0|
S0SdS1eS4S84A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_xF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S84A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_xF : ltac2:(tb__ "0|0|
S0SdS1dS4S2fS5S71A1S32A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xF : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S71A1M4A1S4S2fG4S32A2A1A2S11G3S13G1G2SbG0S13S18S18SefS32A1S32A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK_xF : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S2fS5S71A1S32A2A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_xFb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S2fS5S71A1S32A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_xF : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S2fS5S71A1S32A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXc_xF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S2fS5S71A1S32A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma IC_xF : ltac2:(tb__ "0|0|
S0S12Sb3A1Se9S2dS29S4S2fS5S71A1S32A2A1A1A2S11Sb3Sb6A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R17_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1Z11A2S1bZdeA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R10_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZaA2S32A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R11_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZbA2S1bZ40000A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R12_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZcA2S1bZ3A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R13_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZdA2S1bZ32A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R14_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZeA2S1bZffffffffffffffffA1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma R15_xF : ltac2:(tb__ "0|0|
S0S18S22S4S2fS5S71A1S32A2A1ZfA2S1bZ0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma BEL_xF : ltac2:(tb__ "0|0|
S0SdS2aS1aS4S2fS5S71A1S32A2A1A1S32A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_mF : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZde378SeS2cA1A3SbfS2fS5S71A1S32A2S32Z40000A3ScA5S11G0SbS6S87SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_mF__R <: R_mF__R = Some [r_mF_0]). Qed.
Lemma LN_mF : ltac2:(tb__ "0|0|
S0SdS1eS4SbfS2fS5S71A1S32A2S32Z40000A3A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_mF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4SbfS2fS5S71A1S32A2S32Z40000A3A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_mF : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S5S87A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSbS17SdeS32A1SeS17A1A3A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_mFb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S5S87A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_mF : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S5S87A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mrF : ltac2:(tb__ "0|0|
S0SdS1dS4ScdS5S87A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_mrF : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S87A1M4A1S4ScdG4A1A1A2S11G3S13G1G2SbG0S13S18S18SceS32A1S1bZ8000A1A4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_mcF : ltac2:(tb__ "0|0|
S0SdS1dS4S73A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma E_msF : ltac2:(tb__ "0|1|
S0S12SfS17A1M0A1SedS73Sc5S46S73A1A3S11G0S45S73A1A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma CHK_msF : ltac2:(tb__ "0|0|
S0SdSecS73Sc5S46S73A1S45S73A1S69S6SaS5Sc6A4A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NF_msF : ltac2:(tb__ "0|0|
S0SdS67Sc7S1aS4S73A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_msF : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S73A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBC_msF : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S73A1M0A1A1S1cG0A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT_msF : ltac2:(tb__ "0|0|
S0SdSc2S19S25S1aS4Sc0S73S46S73A1S45S73A1A3A1A1A1S1cS4S73A1A1A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_rF : ltac2:(tb__ "0|0|
S0SdSe8S54S8bA1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_rFb : ltac2:(tb__ "0|0|
S0SdS102U1S44S8bA1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma OB_rF : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S58S8bA1A1A1M0S14S17S6aS17Sc4S44S8bA1U2A2G0A3SbS17SdeS32A1SbS17SdfS32A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma pieceF_i : ltac2:(tb__ "0|0|
SfaS61S6dS103S32S84S89A6").
Proof.
  rewrite <- RF1_eq, <- DMF_eq, <- CMCF_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP.PF beg2 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cfm r_xF_0 r_mF_0
           R_xF LN_xF NX_xF W_xF D_xF SK_xF (inclb_incl _ _ XF_xFb) XX_xF NXc_xF IC_xF R17_xF R10_xF BEL_xF R11_xF R12_xF R13_xF R14_xF R15_xF
           R_mF LN_mF NX_mF SK_mF (inclb_incl _ _ XF_mFb) XX_mF W_mrF D_mrF _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCF_eq, ?DMF_eq; [exact W_mcF | exact E_msF | exact CHK_msF | exact NF_msF | exact NX_msF | exact FBC_msF | exact FBT_msF | exact ND_rF | apply Nat.leb_le; exact NO_rFb | exact OB_rF].
Qed.
Definition R_h__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ4172cSeS2cA1A3S89ScA5").
Local Strategy expand [R_h__R].
Definition r_h := Eval vm_compute in ((fun ro10__ : option (list leafA) => (match ro10__ with Some l => l | None => [] end)) R_h__R).
Definition r_h_0 := Eval vm_compute in (nth 0 r_h (mkLeafA rf1 RsCut)).
Lemma R_h : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ4172cSeS2cA1A3S89ScA5S11G0SbS6S86SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_h__R <: R_h__R = Some [r_h_0]). Qed.
Lemma LN_h : ltac2:(tb__ "0|0|
S0SdS1eS4S89A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_h : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S89A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma run_i : ltac2:(tb__ "0|0|
S100S89S5S86A1A2").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc ph r tp Q HC.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc FUEL [0x4172c] rf1 [r_h_0] ph r tp Q R_h LN_h NX_h).
  intros L r1 [<-|[]] _. exact (HC r1).
Qed.
Definition R_fhP__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SeS2cA1A3S5S83A1ScA5").
Local Strategy expand [R_fhP__R].
Definition r_flP := Eval vm_compute in ((fun ro12__ : option (list leafA) => (match ro12__ with Some l => l | None => [] end)) R_fhP__R).
Definition r_flP_0 := Eval vm_compute in (nth 0 r_flP (mkLeafA (la_state r_f_0) RsCut)).
Definition cl0P := Eval vm_compute in (cL0 (factsR e3r) (la_state r_flP_0)).
Definition R_l1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS78A1ScA5").
Local Strategy expand [R_l1P__R].
Definition r_lP := Eval vm_compute in ((fun ro11__ : option (list leafA) => (match ro11__ with Some l => l | None => [] end)) R_l1P__R).
Definition r_lP_0 := Eval vm_compute in (nth 0 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition r_lP_1 := Eval vm_compute in (nth 1 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition nobFP := Eval vm_compute in (length (ss_objs (ax_S cl0P))).
Definition s_fbkP := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lP_0) nobFP)) (ax_S cl0P)).
Definition s_finP := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flP_0)) (ax_S cl0P)).
Definition R_fjP__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7fA1S7dA2A2ScA5").
Local Strategy expand [R_fjP__R].
Definition r_jP := Eval vm_compute in ((fun ro13__ : option (list leafA) => (match ro13__ with Some l => l | None => [] end)) R_fjP__R).
Definition r_jP_0 := Eval vm_compute in (nth 0 r_jP (mkLeafA (cXL (factsR e3r) (keepn (la_state r_lP_1) nobFP)) RsCut)).
Lemma SK_lP : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S78A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_lP : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S78A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_lPb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S78A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_lP : ltac2:(tb__ "0|0|
S0SdS68S1aS4S78A1A1S50A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_l1P : ltac2:(tb__ "0|0|
S0SdS1dS4S3cS78A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_l1P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS78A1ScA5S11G0SbS6S98SbS6S7fSeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_l1P__R <: R_l1P__R = Some [r_lP_0; r_lP_1]). Qed.
Lemma LN_l1P : ltac2:(tb__ "0|0|
S0SdS1eS4S3cS78A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_fbP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S98A1A1A1M0S14S17S6aS17S7dG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_fxP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S7fA1A1A1M0S14S17S6aS17S7dG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fbkP : ltac2:(tb__ "0|0|
S0SdS8S35S5S98A1S7dA2S78S94A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fbkP : ltac2:(tb__ "0|0|
S0SdS6cS94S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk0P : ltac2:(tb__ "0|0|
S0S18S6bS94S3aA2S20Sb1S21S3aA1S1bZ1A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk2P : ltac2:(tb__ "0|0|
S0S18S6bS94S41A2S20Sb1S21S41A1S21SbbA1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk3P : ltac2:(tb__ "0|0|
S0S18S6bS94S47A2S20Sb1Sd3S20Sb4S20Sb5S21S3aA1S1bZffffffffffffffffA1A3S1bZ2A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_fbPb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd1SeS19A1A3S1cS4S5S98A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_fxPb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd1A1SeS19A1A3S1cS4S5S7fA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fhP : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SeS2cA1A3S5S83A1ScA5S11G0SbS6Sa6SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fhP__R <: R_fhP__R = Some [r_flP_0]). Qed.
Lemma LN_fhP : ltac2:(tb__ "0|0|
S0SdS1eS4S5S83A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fhP : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S83A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_finP : ltac2:(tb__ "0|0|
S0SdS8S5Sa6A1S78S96A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_finP : ltac2:(tb__ "0|0|
S0SdS6cS96S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in0P : ltac2:(tb__ "0|0|
S0S18S6bS96S3aA2S1bZ1A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in2P : ltac2:(tb__ "0|0|
S0S18S6bS96S41A2S59A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in3P : ltac2:(tb__ "0|0|
S0S18S6bS96S47A2S20Sb1Sd3S1bN4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_xlP : ltac2:(tb__ "0|0|
S0SdS1dS4S37S2eS5eA1S35S5S7fA1S7dA2A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xlP : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S35S5S7fA1S7dA2M4A1S4S37S2eS5eA1G4A2A1A2S11G3S13G1G2SeG0A1SbS19S4dSbS19S4eSeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_xlP : ltac2:(tb__ "0|1|
S0SdS68S1aS4S37S2eS5eA1S35S5S7fA1S7dA2M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fjP : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7fA1S7dA2A2ScA5S11G0SbS6S8eSeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fjP__R <: R_fjP__R = Some [r_jP_0]). Qed.
Lemma LN_fxlP : ltac2:(tb__ "0|0|
S0SdS1eS4S37S2eS5eA1S35S5S7fA1S7dA2A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fxlP : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S37S2eS5eA1S35S5S7fA1S7dA2A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fillP_i : ltac2:(tb__ "0|0|
Sf8S61S6dS5S83A1S5S8eA1A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph PQ HDEF r tp Q HC.
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE PF ph PQ HDEF FUEL cl0P r_lP_0 r_lP_1 nobFP s_fbkP SK_lP XX_lP (inclb_incl _ _ XF_lPb) NX_lP W_l1P R_l1P LN_l1P
           OB_fbP OB_fxP ENT_fbkP SID_fbkP S_bk0P S_bk2P S_bk3P (In_of_inclb _ _ FB_fbPb) (In_of_inclb _ _ FB_fxPb) e3r (la_state r_f_0) r_flP_0 r_jP_0 s_finP
           R_fhP LN_fhP NX_fhP ENT_finP SID_finP S_in0P S_in2P S_in3P W_xlP D_xlP NXe_xlP R_fjP LN_fxlP NX_fxlP r tp Q HC).
Qed.
Definition R_fhM__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SeS2cA1A3S5S86A1ScA5").
Local Strategy expand [R_fhM__R].
Definition r_flM := Eval vm_compute in ((fun ro15__ : option (list leafA) => (match ro15__ with Some l => l | None => [] end)) R_fhM__R).
Definition r_flM_0 := Eval vm_compute in (nth 0 r_flM (mkLeafA (la_state r_h_0) RsCut)).
Definition cl0M := Eval vm_compute in (cL0 (factsR e3r) (la_state r_flM_0)).
Definition R_l1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS77A1ScA5").
Local Strategy expand [R_l1M__R].
Definition r_lM := Eval vm_compute in ((fun ro14__ : option (list leafA) => (match ro14__ with Some l => l | None => [] end)) R_l1M__R).
Definition r_lM_0 := Eval vm_compute in (nth 0 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition r_lM_1 := Eval vm_compute in (nth 1 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition nobFM := Eval vm_compute in (length (ss_objs (ax_S cl0M))).
Definition s_fbkM := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lM_0) nobFM)) (ax_S cl0M)).
Definition s_finM := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flM_0)) (ax_S cl0M)).
Definition R_fjM__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7eA1S7cA2A2ScA5").
Local Strategy expand [R_fjM__R].
Definition r_jM := Eval vm_compute in ((fun ro16__ : option (list leafA) => (match ro16__ with Some l => l | None => [] end)) R_fjM__R).
Definition r_jM_0 := Eval vm_compute in (nth 0 r_jM (mkLeafA (cXL (factsR e3r) (keepn (la_state r_lM_1) nobFM)) RsCut)).
Lemma SK_lM : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S77A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_lM : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S77A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_lMb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S77A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_lM : ltac2:(tb__ "0|0|
S0SdS68S1aS4S77A1A1S50A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_l1M : ltac2:(tb__ "0|0|
S0SdS1dS4S3cS77A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_l1M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SbS2cZ4174cSeS2cA1A3A3S3cS77A1ScA5S11G0SbS6S97SbS6S7eSeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_l1M__R <: R_l1M__R = Some [r_lM_0; r_lM_1]). Qed.
Lemma LN_l1M : ltac2:(tb__ "0|0|
S0SdS1eS4S3cS77A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_fbM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S97A1A1A1M0S14S17S6aS17S7cG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_fxM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S7eA1A1A1M0S14S17S6aS17S7cG0A3SbS17Sd2SeS17A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fbkM : ltac2:(tb__ "0|0|
S0SdS8S35S5S97A1S7cA2S77S93A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fbkM : ltac2:(tb__ "0|0|
S0SdS6cS93S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk0M : ltac2:(tb__ "0|0|
S0S18S6bS93S3aA2S20Sb1S21S3aA1S1bZ1A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk2M : ltac2:(tb__ "0|0|
S0S18S6bS93S41A2S20Sb1S21S41A1S21SbbA1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk3M : ltac2:(tb__ "0|0|
S0S18S6bS93S47A2S20Sb1Sd3S20Sb4S20Sb5S21S3aA1S1bZffffffffffffffffA1A3S1bZ2A1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_fbMb : ltac2:(tb__ "0|0|
S0SdS65SbS19Sd1SeS19A1A3S1cS4S5S97A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_fxMb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23Sd1A1SeS19A1A3S1cS4S5S7eA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fhM : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41740SeS2cA1A3S5S86A1ScA5S11G0SbS6Sa5SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fhM__R <: R_fhM__R = Some [r_flM_0]). Qed.
Lemma LN_fhM : ltac2:(tb__ "0|0|
S0SdS1eS4S5S86A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fhM : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S86A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_finM : ltac2:(tb__ "0|0|
S0SdS8S5Sa5A1S77S95A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_finM : ltac2:(tb__ "0|0|
S0SdS6cS95S30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in0M : ltac2:(tb__ "0|0|
S0S18S6bS95S3aA2S1bZ1A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in2M : ltac2:(tb__ "0|0|
S0S18S6bS95S41A2S59A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in3M : ltac2:(tb__ "0|0|
S0S18S6bS95S47A2S20Sb1Sd3S1bN4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma W_xlM : ltac2:(tb__ "0|0|
S0SdS1dS4S37S2eS5eA1S35S5S7eA1S7cA2A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_xlM : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S35S5S7eA1S7cA2M4A1S4S37S2eS5eA1G4A2A1A2S11G3S13G1G2SeG0A1SbS19S4dSbS19S4eSeS19A1A3A3A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_xlM : ltac2:(tb__ "0|1|
S0SdS68S1aS4S37S2eS5eA1S35S5S7eA1S7cA2M0A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_fjM : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413ccSeS2cA1A3S37S2eS5eA1S35S5S7eA1S7cA2A2ScA5S11G0SbS6S8dSeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_fjM__R <: R_fjM__R = Some [r_jM_0]). Qed.
Lemma LN_fxlM : ltac2:(tb__ "0|0|
S0SdS1eS4S37S2eS5eA1S35S5S7eA1S7cA2A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_fxlM : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S37S2eS5eA1S35S5S7eA1S7cA2A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma fillM_i : ltac2:(tb__ "0|0|
Sf8S61S6dS5S86A1S5S8dA1A4").
Proof.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE PF ph PQ HDEF r tp Q HC.
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE PF ph PQ HDEF FUEL cl0M r_lM_0 r_lM_1 nobFM s_fbkM SK_lM XX_lM (inclb_incl _ _ XF_lMb) NX_lM W_l1M R_l1M LN_l1M
           OB_fbM OB_fxM ENT_fbkM SID_fbkM S_bk0M S_bk2M S_bk3M (In_of_inclb _ _ FB_fbMb) (In_of_inclb _ _ FB_fxMb) e3r (la_state r_h_0) r_flM_0 r_jM_0 s_finM
           R_fhM LN_fhM NX_fhM ENT_finM SID_finM S_in0M S_in2M S_in3M W_xlM D_xlM NXe_xlM R_fjM LN_fxlM NX_fxlM r tp Q HC).
Qed.
Definition R_t0P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8eA1ScA5").
Local Strategy expand [R_t0P__R].
Definition r_t0P := Eval vm_compute in ((fun ro18__ : option (list leafA) => (match ro18__ with Some l => l | None => [] end)) R_t0P__R).
Definition r_t0P_0 := Eval vm_compute in (nth 0 r_t0P (mkLeafA (la_state r_jP_0) RsCut)).
Definition ct0P := Eval vm_compute in (cT0 (la_state r_t0P_0)).
Definition R_t1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7bA1ScA5").
Local Strategy expand [R_t1P__R].
Definition r_t1P := Eval vm_compute in ((fun ro17__ : option (list leafA) => (match ro17__ with Some l => l | None => [] end)) R_t1P__R).
Definition r_t1P_0 := Eval vm_compute in (nth 0 r_t1P (mkLeafA (cT1 ct0P) RsCut)).
Definition r_t1P_1 := Eval vm_compute in (nth 1 r_t1P (mkLeafA (cT1 ct0P) RsCut)).
Definition s_inP := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0P_0)) (ax_S ct0P)).
Definition s_bkP := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1P_0) nob)) (ax_S ct0P)).
Lemma SK_tP : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S7bA1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tP : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S7bA1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tPb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S7bA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tP : ltac2:(tb__ "0|0|
S0SdS68S1aS4S7bA1A1S52A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1P : ltac2:(tb__ "0|0|
S0SdS1dS4S3dS7bA1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7bA1ScA5S11G0SbS6S9aSbS6Sa2SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1P__R <: R_t1P__R = Some [r_t1P_0; r_t1P_1]). Qed.
Lemma LN_t1P : ltac2:(tb__ "0|0|
S0SdS1eS4S3dS7bA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S9aA1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xP : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5Sa2A1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkP : ltac2:(tb__ "0|0|
S0SdS8S35S5S9aA1S63A2S7bS9cA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkP : ltac2:(tb__ "0|0|
S0SdS6cS9cS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4P : ltac2:(tb__ "0|0|
S0S18S6bS9cS39A2S20Sb1S21S39A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6P : ltac2:(tb__ "0|0|
S0S18S6bS9cS42A2S20Sb1S21S42A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bPb : ltac2:(tb__ "0|0|
S0SdS65SbS19S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3SeS19A1A3S1cS4S5S9aA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xPb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3A1SeS19A1A3S1cS4S5Sa2A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8eA1ScA5S11G0SbS6Sa8SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0P__R <: R_t0P__R = Some [r_t0P_0]). Qed.
Lemma LN_t0P : ltac2:(tb__ "0|0|
S0SdS1eS4S5S8eA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0P : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S8eA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inP : ltac2:(tb__ "0|0|
S0SdS8S5Sa8A1S7bS9eA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inP : ltac2:(tb__ "0|0|
S0SdS6cS9eS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4P : ltac2:(tb__ "0|0|
S0S18S6bS9eS39A2S20Sb1SbcS1bZ10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6P : ltac2:(tb__ "0|0|
S0S18S6bS9eS42A2Sf6A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlP := Eval vm_compute in (keepn (la_state r_t1P_1) nob).
Definition R_9P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ40cc8SeS2cA1A3Sa0ScA5").
Local Strategy expand [R_9P__R].
Definition r_9P := Eval vm_compute in ((fun ro19__ : option (list leafA) => (match ro19__ with Some l => l | None => [] end)) R_9P__R).
Definition r_9P_0 := Eval vm_compute in (nth 0 r_9P (mkLeafA xlP RsCut)).
Definition cellsfP := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9P_0) icc))) O_ri)).
Definition x3P := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9P_0) icc))).
Definition r_zP := Eval vm_compute in (match sym_runA segsA FUEL [0x3c480] x3P true with Some l => l | None => [] end).
Definition r_zP_0 := Eval vm_compute in (nth 0 r_zP (mkLeafA x3P RsCut)).
Lemma R_9P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ40cc8SeS2cA1A3Sa0ScA5S11G0SbS6S76SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9P__R <: R_9P__R = Some [r_9P_0]). Qed.
Lemma LN_9P : ltac2:(tb__ "0|0|
S0SdS1eS4Sa0A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9P : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4Sa0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x1P : ltac2:(tb__ "0|0|
S0SdS1dS4S33S5S76A1S60A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x1P : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S76A1M4A1S4S33G4S60A2A1A2S11G3S13G1G2SbG0S13S18S18S55S4bA4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1P : ltac2:(tb__ "0|1|
S0SdS68S1aS4S33S5S76A1M0S60A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1P : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S33S5S76A1S60A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1P : ltac2:(tb__ "0|0|
S0S12S17A1Sc3S17S1fS4S33S5S76A1S60A2A1A1S60A3S11S17S51A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1P : ltac2:(tb__ "0|2|
S0SfS17A1S1fS4S33S5S76A1S60A2M0A1A1M1S14S17S6aS17Sc4S44G0A1U2A2G1A3SbS17S38SbS17S101Sa4A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1P : ltac2:(tb__ "0|0|
S0SdS57Sa4Sf3S5aSf4Sf5A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2P : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S34S33S5S76A1S60A2A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSeS17A1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2P : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S34S33S5S76A1S60A2A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Pb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S34S33S5S76A1S60A2A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aP : ltac2:(tb__ "0|0|
S0SdS1dS4S53S34S33S5S76A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bP : ltac2:(tb__ "0|0|
S0SdS1dS4S48S34S33S5S76A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3P : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S48S34S33S5S76A1S60A2A1A1A1M0A1A1S14S19S4cS1cG0A1A3A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_zP : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3c480SeS2cA1A3S43S34S33S5S76A1S60A2A1A1ScA5S11G0SbS6SaaSeS6A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_zP : ltac2:(tb__ "0|0|
S0SdS1eS4S43S34S33S5S76A1S60A2A1A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_zP : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S43S34S33S5S76A1S60A2A1A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s_xP := Eval vm_compute in (s_exit (la_state r_zP_0) e3p).
Lemma ENT_xP : ltac2:(tb__ "0|0|
S0SdS8S5SaaA1S64Sb0A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SX_xP : sx_okb s_xP = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S149_xP : wsub_get s_xP 149%positive = vK.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S159_xP : wsub_get s_xP 159%positive = vCHX.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition pop_P A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0P r_t1P_0 r_t1P_1 nob s_bkP
    SK_tP XX_tP (inclb_incl _ _ XF_tPb) NX_tP W_t1P R_t1P LN_t1P OB_bP OB_xP ENT_bkP SID_bkP S_bk4P S_bk6P (In_of_inclb _ _ FB_bPb) (In_of_inclb _ _ FB_xPb)
    (la_state r_jP_0) r_t0P_0 s_inP e_srcP R_t0P LN_t0P NX_t0P ENT_inP SID_inP S_in4P S_in6P.
Definition exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE phX PHX HFILLX Hini e16P vMFA e32P e48P HRIv HLEN HIDC FUEL xlP r_9P_0 r_zP_0 icc cellsfP
    R_9P LN_9P NX_9P W_x1P D_x1P NX_x1P XX_1P IC_1P OB_1P RI_1P SK_2P XX_2P (inclb_incl _ _ XF_2Pb) W_3aP W_3bP FB_3P R_zP LN_zP NX_zP.
Definition back_P CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLeOrPc rho HW HE phF HREB HMK HLEN e3p (la_state r_zP_0) s_xP ENT_xP SX_xP S149_xP S159_xP HPOP.
Definition R_t0M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8dA1ScA5").
Local Strategy expand [R_t0M__R].
Definition r_t0M := Eval vm_compute in ((fun ro21__ : option (list leafA) => (match ro21__ with Some l => l | None => [] end)) R_t0M__R).
Definition r_t0M_0 := Eval vm_compute in (nth 0 r_t0M (mkLeafA (la_state r_jM_0) RsCut)).
Definition ct0M := Eval vm_compute in (cT0 (la_state r_t0M_0)).
Definition R_t1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7aA1ScA5").
Local Strategy expand [R_t1M__R].
Definition r_t1M := Eval vm_compute in ((fun ro20__ : option (list leafA) => (match ro20__ with Some l => l | None => [] end)) R_t1M__R).
Definition r_t1M_0 := Eval vm_compute in (nth 0 r_t1M (mkLeafA (cT1 ct0M) RsCut)).
Definition r_t1M_1 := Eval vm_compute in (nth 1 r_t1M (mkLeafA (cT1 ct0M) RsCut)).
Definition s_inM := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0M_0)) (ax_S ct0M)).
Definition s_bkM := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1M_0) nob)) (ax_S ct0M)).
Lemma SK_tM : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S7aA1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSbS17S38SbS17S3bSeS17A1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tM : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S7aA1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tMb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S7aA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tM : ltac2:(tb__ "0|0|
S0SdS68S1aS4S7aA1A1S52A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1M : ltac2:(tb__ "0|0|
S0SdS1dS4S3dS7aA1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S3dS7aA1ScA5S11G0SbS6S99SbS6Sa1SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1M__R <: R_t1M__R = Some [r_t1M_0; r_t1M_1]). Qed.
Lemma LN_t1M : ltac2:(tb__ "0|0|
S0SdS1eS4S3dS7aA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5S99A1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xM : ltac2:(tb__ "0|1|
S0SfS17A1S1fS4S5Sa1A1A1A1M0S14S17S6aS17S63G0A3SbS17Sd5SbS17Sd4SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkM : ltac2:(tb__ "0|0|
S0SdS8S35S5S99A1S63A2S7aS9bA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkM : ltac2:(tb__ "0|0|
S0SdS6cS9bS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4M : ltac2:(tb__ "0|0|
S0S18S6bS9bS39A2S20Sb1S21S39A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6M : ltac2:(tb__ "0|0|
S0S18S6bS9bS42A2S20Sb1S21S42A1S1bZ4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bMb : ltac2:(tb__ "0|0|
S0SdS65SbS19S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3SeS19A1A3S1cS4S5S99A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xMb : ltac2:(tb__ "0|0|
S0SdS65SbS19S23S26Sb2S20Sb1S21S39A1S1bZ4A1A3Sd6A3A1SeS19A1A3S1cS4S5Sa1A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ413dcSbS2cZ413f0SeS2cA1A3A3S5S8dA1ScA5S11G0SbS6Sa7SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0M__R <: R_t0M__R = Some [r_t0M_0]). Qed.
Lemma LN_t0M : ltac2:(tb__ "0|0|
S0SdS1eS4S5S8dA1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0M : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S5S8dA1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inM : ltac2:(tb__ "0|0|
S0SdS8S5Sa7A1S7aS9dA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inM : ltac2:(tb__ "0|0|
S0SdS6cS9dS30A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4M : ltac2:(tb__ "0|0|
S0S18S6bS9dS39A2S20Sb1SbcS1bZ10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6M : ltac2:(tb__ "0|0|
S0S18S6bS9dS42A2Sf6A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlM := Eval vm_compute in (keepn (la_state r_t1M_1) nob).
Definition R_9M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ40cc8SeS2cA1A3S9fScA5").
Local Strategy expand [R_9M__R].
Definition r_9M := Eval vm_compute in ((fun ro22__ : option (list leafA) => (match ro22__ with Some l => l | None => [] end)) R_9M__R).
Definition r_9M_0 := Eval vm_compute in (nth 0 r_9M (mkLeafA xlM RsCut)).
Definition cellsfM := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9M_0) icc))) O_ri)).
Definition x3M := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9M_0) icc))).
Definition r_zM := Eval vm_compute in (match sym_runA segsA FUEL [0x3c480] x3M true with Some l => l | None => [] end).
Definition r_zM_0 := Eval vm_compute in (nth 0 r_zM (mkLeafA x3M RsCut)).
Lemma R_9M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ40cc8SeS2cA1A3S9fScA5S11G0SbS6S75SeS6A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9M__R <: R_9M__R = Some [r_9M_0]). Qed.
Lemma LN_9M : ltac2:(tb__ "0|0|
S0SdS1eS4S9fA1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9M : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S9fA1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x1M : ltac2:(tb__ "0|0|
S0SdS1dS4S33S5S75A1S60A2A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x1M : ltac2:(tb__ "0|5|
S0S12S10SfS10S18S18A2M0A1M1SfS19A1M2A2M3A1Sb8S4S5S75A1M4A1S4S33G4S60A2A1A2S11G3S13G1G2SbG0S13S18S18S55S4bA4SeG0A1A3SeS19A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1M : ltac2:(tb__ "0|1|
S0SdS68S1aS4S33S5S75A1M0S60A2A1A1S1aS4G0A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1M : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S33S5S75A1S60A2A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1M : ltac2:(tb__ "0|0|
S0S12S17A1Sc3S17S1fS4S33S5S75A1S60A2A1A1S60A3S11S17S51A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1M : ltac2:(tb__ "0|2|
S0SfS17A1S1fS4S33S5S75A1S60A2M0A1A1M1S14S17S6aS17Sc4S44G0A1U2A2G1A3SbS17S38SbS17S101Sa3A1SeS17A1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1M : ltac2:(tb__ "0|0|
S0SdS57Sa3Sf3Sf7Sf4Sf5A5ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2M : ltac2:(tb__ "0|1|
S0SfS10S10S18S18A2S18A2M0A1S69S17G0S66S1fS4S34S33S5S75A1S60A2A1A1A1A4S69S17G0S66S14S17SbeS61A1SbS17Sb9SbS17SbaSeS17A1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2M : ltac2:(tb__ "0|1|
S0SfS10S18S18A2M0A1S9S34S33S5S75A1S60A2A1A1SeG0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Mb : ltac2:(tb__ "0|0|
S0SdS65SbdS61S6dA2S1cS4S34S33S5S75A1S60A2A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aM : ltac2:(tb__ "0|0|
S0SdS1dS4S53S34S33S5S75A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bM : ltac2:(tb__ "0|0|
S0SdS1dS4S48S34S33S5S75A1S60A2A1A1A1A1ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3M : ltac2:(tb__ "0|1|
S0SdSc2S19S25S1aS4S48S34S33S5S75A1S60A2A1A1A1M0A1A1S14S19S4cS1cG0A1A3A3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_zM : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3c480SeS2cA1A3S43S34S33S5S75A1S60A2A1A1ScA5S11G0SbS6Sa9SeS6A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_zM : ltac2:(tb__ "0|0|
S0SdS1eS4S43S34S33S5S75A1S60A2A1A1A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_zM : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S43S34S33S5S75A1S60A2A1A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s_xM := Eval vm_compute in (s_exit (la_state r_zM_0) e3p).
Lemma ENT_xM : ltac2:(tb__ "0|0|
S0SdS8S5Sa9A1S64SafA3ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SX_xM : sx_okb s_xM = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S149_xM : wsub_get s_xM 149%positive = vK.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S159_xM : wsub_get s_xM 159%positive = vCHX.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition pop_M A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0M r_t1M_0 r_t1M_1 nob s_bkM
    SK_tM XX_tM (inclb_incl _ _ XF_tMb) NX_tM W_t1M R_t1M LN_t1M OB_bM OB_xM ENT_bkM SID_bkM S_bk4M S_bk6M (In_of_inclb _ _ FB_bMb) (In_of_inclb _ _ FB_xMb)
    (la_state r_jM_0) r_t0M_0 s_inM e_srcP R_t0M LN_t0M NX_t0M ENT_inM SID_inM S_in4M S_in6M.
Definition exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE phX PHX HFILLX Hini e16P e24M e32P e48P HRIv HLEN HIDC FUEL xlM r_9M_0 r_zM_0 icc cellsfM
    R_9M LN_9M NX_9M W_x1M D_x1M NX_x1M XX_1M IC_1M OB_1M RI_1M SK_2M XX_2M (inclb_incl _ _ XF_2Mb) W_3aM W_3bM FB_3M R_zM LN_zM NX_zM.
Definition back_M CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLeOrPc rho HW HE phF HREB HMK HLEN e3p (la_state r_zM_0) s_xM ENT_xM SX_xM S149_xM S159_xM HPOP.

Theorem refill_populate_i : ltac2:(tb__ "0|4|
SfS10S2cS2cA2A1M0G0Se3S6eSfS10SaSeeA2A1F_;F_;S108R3R2R1A3SaS0SaR1S64A3Se3S6eS24SfS110Q40M1A1A1M2Se2Se2OF_;F_;Sc1R4R1A2S6fR5A1S0SdSe4R7A1ScA3SebS2dSc7R6R5RcR8R7A2A5Se2S24Se0ScaRbR2R8R1S61S6dR9A7SdbRcR3A2Sc8S3S0Sc8R1SffA3S0Sc8R1Sf9A3A2S111G1S2bR6PcA2A2S2cS109R1A1S2cS10aR11R2A2Se5S2S0Sc8R5Sf9A3S10dSe7R1A1S10eZ4S10cS10fS16S2cSe6R1A1A2A1ScbR12R9A2A2A2A2A2S24G2SfSe1A1Se0Sc9R17R16ReR14RdSfeRaScbR17ReA2S106R7A1A3R4R3R2R1AaS1S105S2dS107R18R8A2M3R5R4R2A5S70R1eR1dR18G3S28RfA1S28R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;Frb;Se3S24G2S24RaSeaS2dS10bS61S6dR4RdR3A5R10R1R2A5SebS2dSc7R3R2R12R4RdA2A5A2FrX;Ftp';Frho';FA';S24Se0S24ScaReR3RbR2S61S6dRcA7RbSeaS2dSc9RfReR4RcR3SccA6S5S62A1R2RcA5R7A2F_;Fr';Fmd0;Frb;F_;F_;TQ;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;FE3P;FHPF;FPFam;FXGL;FCST;").
Proof.
  intros CST XGL PFam HPF E3P ->.
  apply (refill_populate CST XGL PFam W0 UStopLeOrPc (la_state r_2_0) cp2c ru1 (la_state r_f_0) (la_state r_f_1) cfm rf1 (la_state r_h_0)
           (la_state r_jP_0) xlP (la_state r_zP_0) (la_state r_jM_0) xlM (la_state r_zM_0) e3p head_i pieceU_i mid_i fm_i pieceF_i run_i fillP_i fillM_i).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_P A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_M A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_P CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_M CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
Qed.
End SpineCallocRp1u.

(* [comment removed for export] *)
Module CRefillPlug1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "False"; "and"; "iff"; "not"; "or"; "@Corelib.Init.Datatypes"; "list"; "bool"; "length"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "phase"; "gh_new"; "JR"; "entryR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "E3r"; "E3p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "cls_of"; "cst_of"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15"; "phUF3"; "phFin"; "phU3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7"; "popfacts"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP RebuildM SegD_wf SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocR14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.CRebuildRN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.CRebuildRQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cu.CallocHitTail1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dc.CallocHitTail1E.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR5c.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Section PLUG1.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S4S27VCST;R1A2S27S38R2A2S6F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S4S27VCST;R1A2S9S3cR2A1A1F_;Fa;").
Let W0 : list ulink := Wcan 1.
Let st0 : ustop := UStopLeOrPc.

Lemma hreb_Q : ltac2:(tb__ "0|3|
S10S15S1SbS23Q40M0A1A1M1S5ScS11R4A1SfA3S1S2bS21R7R2R4R1VW0;Vst0;R5A7S3eR8R3A2S1eSaS5S1eR1S34A3S5S1eR1S32A3A2S24G0S2R6PcA2A2S4S29R1A1S4S2aRdR2A2S12S8S5S1eR5S32A3S40S14R1A1S41Z4S3fS42SdS4S13R1A1A2A1S1fReR9A2A2A2A2A2S1G1SbS2cA1S2bS20R13R12ReR10RdS33RaS1fR13ReA2S39R7A1A3R4R3R2R1AaS7S37S0S3aR14R8A2M2R5R4R2A5S17VCST;VXGL;R14G2S3RfA1S3R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;Frb;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Hini rb md0 HE PF phX [-> | ->] nv c cs HB r tp' tr md HJ.
  - rewrite phQ_P in HJ. apply (refill_rebuild_Q CST XGL HCST HXGL A Kc rb tp md0 W0 st0 rho HE PF false Hini) with (tr := tr); [|exact HJ].
    split; [discriminate|]. intros HLT. apply HB in HLT. unfold phU3, phUF3 in HLT. discriminate HLT.
  - rewrite phQ_M in HJ. apply (refill_rebuild_Q CST XGL HCST HXGL A Kc rb tp md0 W0 st0 rho HE PF true Hini) with (tr := tr); [|exact HJ].
    split; [intros _; apply HB; reflexivity | reflexivity].
Qed.

Theorem refill_core_1 : ltac2:(tb__ "0|3|
S15S2dS2dOF_;F_;S3bR2R1A2S16R3A1S10S15SbSeS35S1dA2A1F_;F_;S3dVCST;VXGL;R1A3S10S1SbS23Q40M0A1A1M1S1R9S19S0S22VW0;Vst0;R4RaR3A5S26VW0;Vst0;Z3M2A3R1R2A5S1cS0S18R3R2R6R4RaA2A5A2FrX;Ftp';Frho';FA';S10S1G1S5S4S28R3S24G0S2R2PcA2A2A2Z0A3S1RbS19S0S22VW0;Vst0;R5RcR4A5S25VW0;Vst0;G2A3R1R3A5S1cS0S18R4R3R8R5RcA2A5A2FrhoE;F_;Ftp;Frho;FA;F_;FHPF;FPFam;FHKc;FKIT;FTR;FKc;").
Proof.
  intros Kc TR KIT HKc PFam HPF HPOP A rho tp Hcnt.
  destruct (aa_cache_inited A) eqn:Hini.
  -
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi1.refill_N_i CST XGL PFam HPF (E3r W0 st0 3) (E3p W0 st0 3) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi1.E3r_eq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi1.E3p_eq A Kc rho tp TR KIT HKc Hini Hcnt).
    + intros rb md0 HE HNP r tp' tr md HJ. exact (refill_rebuild_N CST XGL HCST HXGL A Kc rb tp md0 W0 st0 rho HE Hini HNP r tp' tr md HJ).
    + exact HPOP.
    + exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dm.SpineCallocRp1.refill_populate_i CST XGL PFam HPF (E3p W0 st0 3) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi1.E3p_eq A Kc rho tp TR KIT HKc Hini (hreb_Q A Kc rho tp Hini) HPOP).
  -
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineCallocRu1.refill_uninit_i CST XGL HCST HXGL PFam HPF (E3r W0 st0 3) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineCallocRu1.e3u OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocRi1.E3r_eq eq_refl A Kc rho tp TR KIT HKc Hini Hcnt).
    intros rho1 rX E1.
    assert (Hcnt1 : cnt_of (initA A) (bv_unsigned (rw rho1 12%positive)) = 0) by (rewrite E1; exact Hcnt).
    assert (Hini1 : aa_cache_inited (initA A) = true) by reflexivity.
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineCallocRi1u.refill_N_i CST XGL PFam HPF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineCallocRu1.e3u (E3p W0 st0 3) eq_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineCallocRi1u.E3p_eq (initA A) Kc rho1 tp TR KIT HKc Hini1 Hcnt1).
    + intros rb md0 HE HNP r tp' tr md HJ. exact (refill_rebuild_N CST XGL HCST HXGL (initA A) Kc rb tp md0 W0 st0 rho1 HE Hini1 HNP r tp' tr md HJ).
    + exact HPOP.
    + exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dm.SpineCallocRp1u.refill_populate_i CST XGL PFam HPF (E3p W0 st0 3) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineCallocRi1u.E3p_eq (initA A) Kc rho1 tp TR KIT HKc Hini1 (hreb_Q (initA A) Kc rho1 tp Hini1) HPOP).
Qed.

Theorem refill_all_1 : ltac2:(tb__ "0|1|
S30OF_;S10S15S1SbS23Q40M0A1A1S16R3A1S1bS0R6S1aR4A1A3S36S0R7S1aR5A1A3S5S4S28R7S24G0S2R5PcA2A2A2Z0A3S1S2fS0RaS19S0S22VW0;Vst0;R9R8R7A5S25VW0;Vst0;Z3A3R1R6A5S1cS0S18R7R6S31VCST;VXGL;VW0;Vst0;R9R8A6A5A4FrhoE;F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokl Hokp Hcnt.
  apply (refill_core_1 Kc (triple segs ok) (TRok_triple Kc ok Hokl Hokp) HKc (PFc CST XGL W0 st0) (posts_conv_c CST XGL W0 st0)); [|exact Hcnt].
  intros A' rho' tp' rX. exact (calloc_hit_tail_1 CST XGL HCST HXGL HCSTM HCSTD ok A' Kc rho' tp' HKc Hokl Hokp rX).
Qed.

Theorem erefill_all_1 : ltac2:(tb__ "0|1|
S10S15S1SbS23Q40M0A1A1S16R3A1S5S4S28R5S24G0S2R3PcA2A2A2Z0A3S1S2eS0S19S0S22VW0;Vst0;R7R6R5A5S25VW0;Vst0;Z3A3R1R4A5S1cS0S18R5R4S31VCST;VXGL;VW0;Vst0;R7R6A6A5A3FrhoE;F_;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc Hcnt.
  apply (refill_core_1 Kc (etriple segs) (TRok_etriple Kc) HKc (PFc CST XGL W0 st0) (posts_conv_c CST XGL W0 st0)); [|exact Hcnt].
  intros A' rho' tp' rX. exact (ecalloc_hit_tail_1 CST XGL HCST HXGL HCSTM HCSTD A' Kc rho' tp' HKc rX).
Qed.
End PLUG1.
End CRefillPlug1.

