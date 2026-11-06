(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_063.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm ch F0A_cLN0 F0A_hbN_cert F0A_cLN1.
From Stdlib Require Permutation FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_env.

(* [comment removed for export] *)
Module SpineCallocSec6IW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "cell"; "sprop"; "ss_next"; "ss_facts"; "ss_objs"; "swf"; "SLit"; "SVar"; "sprop_below"; "DUnknown"; "SPNot"; "mkObj"; "DZero"; "SAlu"; "sstate"; "SPBranch"; "c_off"; "c_val"; "ob_cells"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "ax_setS"; "entailsA"; "xr_below"; "la_state"; "@Corelib.Init.Datatypes"; "true"; "bool"; "nil"; "cons"; "list"; "nat"; "app"; "prod"; "option"; "length"; "pair"; "Some"; "false"; "andb"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1"; "nx0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "find"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7"; "KEPTF"; "KUB"; "idxsF"; "idxsU"; "S2F"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV"; "O_UBs"; "F_par"; "UBs"; "F_A"; "F_B"; "CPC"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "osplit"; "O_3"; "perm7"; "L3"; "O_3b"; "PGST"; "B3"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "a0e7"; "a2e6"; "a2e7"; "a2e8"; "fx8"; "sel7"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.SpineCallocSec6IW1.INST"; "FFfaA"; "FFfaB"; "FFfbA"; "FFfbB"; "FFqaA"; "FFqaB"; "FFqbA"; "FFqbB"; "mcfaA"; "mcfaB"; "mcfbA"; "mcfbB"; "mcqaA"; "mcqaB"; "mcqbA"; "mcqbB"; "CT6a"; "CT6b"; "CT7a"; "CT7b"; "CT8a"; "CT8b"; "CO6a"; "CO6b"; "CO8a"; "CO8b"; "swcfaA"; "swcfaB"; "swcfbA"; "swcfbB"; "swcqaA"; "swcqaB"; "swcqbA"; "swcqbB"; "CM7a"; "CM7b"; "FXPa"; "FXPb"; "E9pa"; "E9pb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "c1faA"; "c1faB"; "c1fbA"; "c1fbB"; "c1qaA"; "c1qaB"; "c1qbA"; "c1qbB"; "n7a"; "n7b"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "E6a"; "E6b"; "S9bfa"; "S9bfb"; "S9bqa"; "S9bqb"; "CO7a"; "CO7b"; "CO9pa"; "CO9pb"; "D6a"; "D6b"; "D7a"; "D7b"; "D8a"; "D8b"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "PXa"; "PXb"; "tybfaA"; "tybfaB"; "tybfbA"; "tybfbB"; "tybqaA"; "tybqaB"; "tybqbA"; "tybqbB"; "C5Aa"; "C5Ab"; "C5Ba"; "C5Bb"; "CR7a"; "CR7b"; "CS7a"; "CS7b"; "D9faA"; "D9faB"; "D9fbA"; "D9fbB"; "D9qaA"; "D9qaB";
"D9qbA"; "D9qbB"; "R6a"; "R6b"; "R7a"; "R7b"; "R8a"; "R8b"; "T6a"; "T6b"; "T7a"; "T7b"; "T8a"; "T8b"; "perm9fa"; "perm9fb"; "perm9qa"; "perm9qb"; "s6a"; "s6b"; "s7a"; "s7b"; "s8a"; "s8b"; "E9fa"; "E9fb"; "E9qa"; "E9qb"; "S9afa"; "S9afb"; "S9aqa"; "S9aqb"; "Y6Aa"; "Y6Ab"; "Y6Ba"; "Y6Bb"; "iMfa"; "iMfb"; "iMqa"; "iMqb"; "s6Aa"; "s6Ab"; "s6Ba"; "s6Bb"; "sFfaA"; "sFfaB"; "sFfbA"; "sFfbB"; "sFqaA"; "sFqaB"; "sFqbA"; "sFqbB"; "c2faA"; "c2faB"; "c2fbA"; "c2fbB"; "c2qaA"; "c2qaB"; "c2qbA"; "c2qbB"; "c4faA"; "c4faB"; "c4fbA"; "c4fbB"; "c4qaA"; "c4qaB"; "c4qbA"; "c4qbB"; "c5faA"; "c5faB"; "c5fbA"; "c5fbB"; "c5qaA"; "c5qaB"; "c5qbA"; "c5qbB"; "run6Aa"; "run6Ab"; "run6Ba"; "run6Bb"; "run7a"; "run7b"; "run8a"; "run8b"; "run9a"; "run9b"; "run9qa"; "run9qb"; "runFfaA"; "runFfaB"; "runFfbA"; "runFfbB"; "runFqaA"; "runFqaB"; "runFqbA"; "runFqbB"; "xcfaA"; "xcfaB"; "xcfbA"; "xcfbB"; "xcqaA"; "xcqaB"; "xcqbA"; "xcqbB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS"; "V_NRES"; "V_NCH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST"; "O_1"; "carveS"; "BR"; "O_2"; "Pret_ms"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "Lc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "SKEL0"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IW1"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4IW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ch.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CertCallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.SpineCallocSec7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition tyb_of (mc : list cell) : Z := ltac2:(tb__ "0|4|
S28S4A1S35Lx;S34S4S4S17S14R1A1SaZ17f1A1A2Lc;Vmc;A3S4S3S35Lx;S15R1A1S35R1Lt;S36Z0M0Li;S169S3S3G0Lb;La;M1Lop;M2G2S16aG1Lop;M3G3S21S37S3G0La;Lw;Lsgn;S36S3S35G0Lk;Li;Ll;X3x8Lc;G0X28x2").
Definition cells_at (i : nat) (F : axst) : list cell := ltac2:(tb__ "0|0|
S16S6cS2Vi;S8S18VF;A1A1S150S2fA1A4A1").

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.

Definition PXa : list sobj := [O_blk].
Definition FXPa : list sprop := ltac2:(tb__ "0|0|
S23S5S13S168SbS14fA1SbS14eA1A3S22S5A1A3").

Definition C5Aa : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5ac).
Definition C5Ba : axst := Eval vm_compute in (ax_add_facts (F_B nx0) C5ac).
Lemma HC5Aa_0 : ltac2:(tb__ "0|0|
S0S19S74S42S2fA1S16eA2Sd6A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Aa)). Qed.
Lemma HC5Ba_0 : ltac2:(tb__ "0|0|
S0S19S74S43S2fA1S16eA2Sd8A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ba)). Qed.
Lemma FBAa_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18S16eA1A1A1S42S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBBa_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18S16eA1A1A1S43S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run6Aa : option (list leafA) := Eval vm_compute in (runT6 C5Aa).
Lemma run6Aa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sd6S22S19A1A3A4S23G0S130S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Aa]). Qed.
Definition Y6Aa : axst := Eval vm_compute in (leafS 0 run6Aa).
Lemma Cert6Aa_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sd6S22S19A1M0A3S23S19S104G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Aa] [Y6Aa] [run6Aa]); [exact run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition run6Ba : option (list leafA) := Eval vm_compute in (runT6 C5Ba).
Lemma run6Ba__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sd8S22S19A1A3A4S23G0S132S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ba]). Qed.
Definition Y6Ba : axst := Eval vm_compute in (leafS 0 run6Ba).
Lemma Cert6Ba_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sd8S22S19A1M0A3S23S19S106G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ba] [Y6Ba] [run6Ba]); [exact run6Ba__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6a : axst := Eval vm_compute in (rmF (F_A nx0) Y6Aa).
Definition s6Aa : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Aa) (ax_S E6a)).
Lemma E6Aa_0 : ltac2:(tb__ "0|0|
S0S21S1dS104Sb8S10cA3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Aa_0 : ltac2:(tb__ "0|0|
S0S21S157S10cVGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6Ba : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ba) (ax_S E6a)).
Lemma E6Ba_0 : ltac2:(tb__ "0|0|
S0S21S1dS106Sb8S10eA3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ba_0 : ltac2:(tb__ "0|0|
S0S21S157S10eVGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6a : axst := Eval vm_compute in (rstS E6a ru6 []).
Definition CO6a : axst := Eval vm_compute in (carveS CT6a (O_3 nx0)).
Lemma WC6a_0 : ltac2:(tb__ "0|0|
S0S21S9S18S8cA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6a_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sb8A1S18S8cA1A2S2bG3S2aG1G2S23G0S2aS3S3S65S2fA1S59A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6a_0 : ltac2:(tb__ "0|0|
S0S36S6S18S8cA1A1S6S18Sb8A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6a))). Qed.
Lemma HC6a_0 : ltac2:(tb__ "0|0|
S0S19S1cSb8S18S8cA1A2S8cA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6a)). Qed.
Lemma SK6a_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18S8cA1A1A4S6aS2G0S7bS26S2S23S2S153S2fA1S23S2S150S2fA1S22S2A1A3A3S26S2S15bU1S2fA2SccA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXa))). Qed.
Lemma FC6a_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S8cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6a_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18S8cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6a_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS8cA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6a_0 : ltac2:(tb__ "0|0|
S0S19S151S8cSfS5cS2fA1SaZ0A1S59S22S4A1SdA5A2S92A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6a)). Qed.
Lemma WCO6a_0 : ltac2:(tb__ "0|0|
S0S21S9S18S92A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6a : wsub := Eval vm_compute in (callsub CO6a Pre_memsetA).
Definition R6a : list sobj := Eval vm_compute in (callR CO6a Pre_memsetA s6a).
Definition T6a : axst := Eval vm_compute in (callT CO6a Pre_memsetA Pret_ms s6a R6a).
Lemma He6a_0 : ltac2:(tb__ "0|1|
S0S28S24S2A1M0A1S164S92S14cSf6A3S2bG0Se6A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6a)). Qed.
Lemma Hchk6a_0 : ltac2:(tb__ "0|0|
S0S21S163S92S14cSf6Se6S6aS1aS19S1fS14dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6a_0 : ltac2:(tb__ "0|0|
S0S19S165Sf6S14cS154S92Se6A5SecA3"). Proof. vm_cast_no_check (@eq_refl _ (T6a)). Qed.
Lemma FBC6a_0 : ltac2:(tb__ "0|1|
S0S21S31S5ScS6S18S92A1M0A1A1S7G0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6a_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18SecA1A1A1S7S18S92A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6a_0 : ltac2:(tb__ "0|0|
S0S21S166VGS0;S6S18S92A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6a : axst := Eval vm_compute in (ax_with_facts T6a (ss_facts (ax_S CO6a))).
Lemma HD6a_0 : ltac2:(tb__ "0|0|
S0S19S162SecS7S18S92A1A1A2Sc2A3"). Proof. vm_cast_no_check (@eq_refl _ (D6a)). Qed.

Definition U7a : axst := Eval vm_compute in (U7p nx0 D6a).
Lemma WU7a_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sa4A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7a_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc2A1S18Sa4A1A2S2bG3S2aG1G2S22G0A1S5fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7a_0 : ltac2:(tb__ "0|0|
S0S36S6S18Sa4A1A1S6S18Sc2A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6a))). Qed.
Lemma HU7a_0 : ltac2:(tb__ "0|0|
S0S19S1cSc2S18Sa4A1A2Sa4A3"). Proof. vm_cast_no_check (@eq_refl _ (U7a)). Qed.
Definition run7a : option (list leafA) := Eval vm_compute in (runT6 U7a).
Lemma run7a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sa4S22S19A1A3A4S23G0S134S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7a]). Qed.
Definition ET7a : axst := Eval vm_compute in (leafS 0 run7a).
Lemma Cert7a_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sa4S22S19A1M0A3S23S19Sc8G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7a] [ET7a] [run7a]); [exact run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7a : axst := Eval vm_compute in (rstS ET7a (ru7 nx0) []).
Definition CO7a : axst := Eval vm_compute in (carveS CT7a (O_3n nx0)).
Definition CR7a : axst := Eval vm_compute in (CDepotCall.oreb CO7a 1).
Definition n7a : nat := Eval vm_compute in (length (ss_objs (ax_S CR7a))).
Definition CS7a : axst := Eval vm_compute in (sel7 CR7a).
Definition CM7a : axst := Eval vm_compute in (CDepotCall.omrg CS7a 1).
Lemma WC7a_0 : ltac2:(tb__ "0|0|
S0S21S9S18S8eA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7a_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc8A1S18S8eA1A2S2bG3S2aG1G2S23G0S2aS3S3S64S2fA1S152S2fA1A4S23G0S2aS3S3S66S2fA1S62A4S22G0A1A3A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S0S36S6S18S8eA1A1S6S18Sc8A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7a))). Qed.
Lemma HC7a_0 : ltac2:(tb__ "0|0|
S0S19S1cSc8S18S8eA1A2S8eA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7a)). Qed.
Lemma SK7a_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18S8eA1A1A4S6aS2G0S7bS26S2S23S2S57S2fA1S23S2S153S2fA1S23S2S150S2fA1S22S2A1A3A3A3S26S2S15bU1S2fA2SccA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXa))). Qed.
Lemma FC7a_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S8eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7a_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18S8eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7a_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS8eA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7a_0 : ltac2:(tb__ "0|0|
S0S19S151S8eSfS152S2fA1SaZ0A1SaZ100A1S22S4A1SdA5A2SbeA3"). Proof. vm_cast_no_check (@eq_refl _ (CO7a)). Qed.
Lemma WCO7a_0 : ltac2:(tb__ "0|0|
S0S21S9S18SbeA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7a_0 : ltac2:(tb__ "0|0|
S0S21S16bS12S171S18SbeA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7a_0 : ltac2:(tb__ "0|0|
S0S19S16dSbeU1A2SdaA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7a)). Qed.
Lemma LEN7a_0 : ltac2:(tb__ "0|0|
S0S25S29S2S8S18SdaA1A1A2Sb2A3"). Proof. vm_cast_no_check (@eq_refl _ (n7a)). Qed.
Lemma PERM_nd7a_0 : ltac2:(tb__ "0|0|
S0S21S71S58Sb2A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7a_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1Sb2A2Li;S58Sb2A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7a_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S58Sb2A1A3Li;S6bU0Sb2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7a_0 : ltac2:(tb__ "0|0|
S0S19S69SdaA1SdcA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7a)). Qed.
Lemma MRG7a_0 : ltac2:(tb__ "0|0|
S0S21S16bS12S170S18SdcA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7a_0 : ltac2:(tb__ "0|0|
S0S19S16cSdcU1A2S9eA3"). Proof. vm_cast_no_check (@eq_refl _ (CM7a)). Qed.
Definition s7a : wsub := Eval vm_compute in (callsub CM7a Pre_memsetA).
Definition R7a : list sobj := Eval vm_compute in (callR CM7a Pre_memsetA s7a).
Definition T7a : axst := Eval vm_compute in (callT CM7a Pre_memsetA Pret_ms s7a R7a).
Lemma He7a_0 : ltac2:(tb__ "0|1|
S0S28S24S2A1M0A1S164S9eS14cSf8A3S2bG0Se8A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7a)). Qed.
Lemma Hchk7a_0 : ltac2:(tb__ "0|0|
S0S21S163S9eS14cSf8Se8S6aS1aS19S1fS14dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7a_0 : ltac2:(tb__ "0|0|
S0S19S165Sf8S14cS154S9eSe8A5SeeA3"). Proof. vm_cast_no_check (@eq_refl _ (T7a)). Qed.
Lemma FBC7a_0 : ltac2:(tb__ "0|1|
S0S21S31S5ScS6S18S9eA1M0A1A1S7G0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7a_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18SeeA1A1A1S7S18S9eA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7a_0 : ltac2:(tb__ "0|0|
S0S21S166VGS0;S6S18S9eA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7a : axst := Eval vm_compute in (ax_with_facts T7a (ss_facts (ax_S CM7a))).
Lemma HD7a_0 : ltac2:(tb__ "0|0|
S0S19S162SeeS7S18S9eA1A1A2Sc4A3"). Proof. vm_cast_no_check (@eq_refl _ (D7a)). Qed.

Definition U8a : axst := Eval vm_compute in (U8p nx0 D7a).
Lemma WU8a_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sa6A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8a_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc4A1S18Sa6A1A2S2bG3S2aG1G2S22G0A1S60S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8a_0 : ltac2:(tb__ "0|0|
S0S36S6S18Sa6A1A1S6S18Sc4A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7a))). Qed.
Lemma HU8a_0 : ltac2:(tb__ "0|0|
S0S19S1cSc4S18Sa6A1A2Sa6A3"). Proof. vm_cast_no_check (@eq_refl _ (U8a)). Qed.
Definition run8a : option (list leafA) := Eval vm_compute in (runT6 U8a).
Lemma run8a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sa6S22S19A1A3A4S23G0S136S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8a]). Qed.
Definition ET8a : axst := Eval vm_compute in (leafS 0 run8a).
Lemma Cert8a_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sa6S22S19A1M0A3S23S19ScaG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8a] [ET8a] [run8a]); [exact run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8a : axst := Eval vm_compute in (CT8p nx0 ET8a).
Definition CO8a : axst := Eval vm_compute in (carveS CT8a (O_4 nx0)).
Lemma WC8a_0 : ltac2:(tb__ "0|0|
S0S21S9S18S90A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8a_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18ScaA1S18S90A1A2S2bG3S2aG1G2S22G0A1S68S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8a_0 : ltac2:(tb__ "0|0|
S0S36S6S18S90A1A1S6S18ScaA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8a))). Qed.
Lemma HC8a_0 : ltac2:(tb__ "0|0|
S0S19S1cScaS18S90A1A2S90A3"). Proof. vm_cast_no_check (@eq_refl _ (CT8a)). Qed.
Lemma SK8a_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18S90A1A1A4S6aS2G0S7bS26S2S23S2S5aS2fA1S23S2S57S2fA1S23S2S150S2fA1S22S2A1A3A3A3S26S2S15bU1S2fA2SccA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXa))). Qed.
Lemma FC8a_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8a_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8a_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS90A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8a_0 : ltac2:(tb__ "0|0|
S0S19S151S90SfS5dS2fA1SaZ0A1S67S2fA1S22S4A1SdA5A2S94A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8a)). Qed.
Lemma WCO8a_0 : ltac2:(tb__ "0|0|
S0S21S9S18S94A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8a : wsub := Eval vm_compute in (callsub CO8a Pre_mszA).
Definition R8a : list sobj := Eval vm_compute in (callR CO8a Pre_mszA s8a).
Definition T8a : axst := Eval vm_compute in (callT CO8a Pre_mszA Pret_mz s8a R8a).
Lemma He8a_0 : ltac2:(tb__ "0|1|
S0S28S24S2A1M0A1S164S94S160SfaA3S2bG0SeaA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8a)). Qed.
Lemma Hchk8a_0 : ltac2:(tb__ "0|0|
S0S21S163S94S160SfaSeaS6aS1aS19S1fS161A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8a_0 : ltac2:(tb__ "0|0|
S0S19S165SfaS160S155S94SeaA5Sf0A3"). Proof. vm_cast_no_check (@eq_refl _ (T8a)). Qed.
Lemma FBC8a_0 : ltac2:(tb__ "0|1|
S0S21S31S5ScS6S18S94A1M0A1A1S7G0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8a_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sf0A1A1A1S7S18S94A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8a_0 : ltac2:(tb__ "0|0|
S0S21S166VGS0;S6S18S94A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8a : axst := Eval vm_compute in (ax_with_facts T8a (ss_facts (ax_S CO8a))).
Lemma HD8a_0 : ltac2:(tb__ "0|0|
S0S19S162Sf0S7S18S94A1A1A2Sc6A3"). Proof. vm_cast_no_check (@eq_refl _ (D8a)). Qed.

Definition U9a : axst := Eval vm_compute in (U9p nx0 D8a).
Lemma WU9a_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sa8A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9a_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc6A1S18Sa8A1A2S2bG3S2aG1G2S22G0A1S61S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9a_0 : ltac2:(tb__ "0|0|
S0S36S6S18Sa8A1A1S6S18Sc6A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8a))). Qed.
Lemma HU9a_0 : ltac2:(tb__ "0|0|
S0S19S1cSc6S18Sa8A1A2Sa8A3"). Proof. vm_cast_no_check (@eq_refl _ (U9a)). Qed.
Definition run9a : option (list leafA) := Eval vm_compute in (runT9 U9a).
Lemma run9a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S44S23S35S5bS22S35A1A3A3S23S19Sa8S22S19A1A3A4S23G0S138S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9a]). Qed.
Definition E9fa : axst := Eval vm_compute in (leafS 0 run9a).
Definition E9pa : axst := Eval vm_compute in (leafS 1 run9a).
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S44S23S35S5bS22S35A1A3A3VGS0;S23S19Sa8S22S19A1M0A3S23S19SfcS23S19Sa2G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC; PGST] GS0 [U9a] [E9fa; E9pa] [run9a]); [exact run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9a_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18Sa2A1A1A4S6aS2G0S7bS26S2S23S2S63S2fA1S23S2S5aS2fA1S23S2S57S2fA1S23S2S150S2fA1S22S2A1A3A3A3A3S26S2S15bU1S2fA2SccA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXa))). Qed.
Lemma FC9a_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18Sa2A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9a_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18Sa2A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9a_0 : ltac2:(tb__ "0|0|
S30S5SeS40A1S7S18Sa2A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9a_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bSa2A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pa : axst := Eval vm_compute in (carveS E9pa (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9a_0 : ltac2:(tb__ "0|0|
S0S19S151Sa2SfS5eS2fA1SaZ0A1SaZ1A1S22S4A1SdA5A2Sc0A3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pa)). Qed.
Lemma WCO9a_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sc0A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qa : option (list leafA) := Eval vm_compute in (runT9q CO9pa).
Lemma run9qa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S44S22S35A1A3S23S19Sc0S22S19A1A3A4S23G0S13aS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qa]). Qed.
Definition E9qa : axst := Eval vm_compute in (leafS 0 run9qa).
Lemma Cert9qa_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S44S22S35A1A3VGS0;S23S19Sc0S22S19A1M0A3S23S19SfeG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC] GS0 [CO9pa] [E9qa] [run9qa]); [exact run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fa)) 0).
Definition S9afa : axst := Eval vm_compute in (osplit E9fa iMfa (SLit 6144)).
Definition S9bfa : axst := Eval vm_compute in (osplit S9afa (S iMfa) (SLit 10240)).
Lemma HS9afa_0 : ltac2:(tb__ "0|0|
S0S19S56SfcS108SaZ1800A1A3S100A3"). Proof. vm_cast_no_check (@eq_refl _ (S9afa)). Qed.
Lemma HS9bfa_0 : ltac2:(tb__ "0|0|
S0S19S56S100S2eS108A1SaZ2800A1A3SbaA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfa)). Qed.
Definition perm9fa : list nat := Eval vm_compute in (S iMfa :: seq 0 (S iMfa) ++ seq (S (S iMfa)) (length (ss_objs (ax_S S9bfa)) - S (S iMfa))).
Definition D9fa : axst := Eval vm_compute in (ax_setS S9bfa (set_objs (ax_S S9bfa) (select (ss_objs (ax_S S9bfa)) perm9fa))).
Lemma HD9fa_0 : ltac2:(tb__ "0|1|
S0S19S1cSbaS72S18SbaA1M0S70S8G0A1Sf2A2A2A2Sb4A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fa)). Qed.
Lemma NDpfa_0 : nodupN perm9fa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpfa_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18SbaA1A1A2A2Li;Sf2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpfa_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1Sf2A3Li;S6bU0S29S2S8S18SbaA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9faA : axst := Eval vm_compute in (ax_add_facts (F_A nx0) D9fa).
Definition D9faB : axst := Eval vm_compute in (ax_add_facts (F_B nx0) D9fa).
Lemma HD9Afa_0 : ltac2:(tb__ "0|0|
S0S19S74S42S2fA1Sb4A2SdeA3"). Proof. vm_cast_no_check (@eq_refl _ (D9faA)). Qed.
Lemma HD9Bfa_0 : ltac2:(tb__ "0|0|
S0S19S74S43S2fA1Sb4A2SdfA3"). Proof. vm_cast_no_check (@eq_refl _ (D9faB)). Qed.
Lemma FBA9fa_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb4A1A1A1S42S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBB9fa_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb4A1A1A1S43S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFfaA : option (list leafA) := Eval vm_compute in (runTF D9faA).
Lemma runFfaA__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19SdeS22S19A1A3A4S23G0S13cS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfaA]). Qed.
Definition FFfaA : axst := Eval vm_compute in (leafS 0 runFfaA).
Lemma CertFfaA_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19SdeS22S19A1M0A3S23S19S7cG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9faA] [FFfaA] [runFfaA]); [exact runFfaA__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfaA : list cell := Eval vm_compute in (cells_at 5 FFfaA).
Definition c1faA : list cell := Eval vm_compute in (cells_at 39 FFfaA).
Definition c2faA : list cell := Eval vm_compute in (cells_at 40 FFfaA).
Definition c4faA : list cell := Eval vm_compute in (cells_at 42 FFfaA).
Definition c5faA : list cell := Eval vm_compute in (cells_at 46 FFfaA).
Definition mcfaA : list cell := Eval vm_compute in (cells_at 47 FFfaA).
Definition xcfaA : list cell := Eval vm_compute in (cells_at 49 FFfaA).
Definition tybfaA : Z := Eval vm_compute in (tyb_of mcfaA).
Lemma SELFfaA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S7cA1A1S3bU1S2cA2A2S26S2S39VW;S96A2S26S2S159S45S2fSaaS118S120S128S84S144Z20000S10S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfaA ++ RT_m1 ++ RSF nx0 c1faA c2faA c4faA c5faA mcfaA xcfaA 131072 DZero false)). Qed.
Lemma NDFfaA_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU1S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfaA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S7cA1A1A2A2Li;S3bU1S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfaA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3bU1S2cA2A3Li;S6bU0S29S2S8S18S7cA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfaA_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS7cA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfaA_0 : ax_base FFfaA = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfaA_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfaA_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfaA_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S2cSeS40A1S40X21x2S7S18S7cA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1faA_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSaaA3S1S30S4S46SaaA3S1S30S4S47SaaA3S1S30S4S4bSaaA3S1S30S4S49S11S167SbS14eA1SaZ4000A1A3A1SaaA3S30S4S48SaaA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1faA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1faA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1faA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1faA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1faA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1faA ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcfaA_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S84A3S1S30S4S50S84A3S1S30S4S51S84A3S1S30S4S4dS84A3S1S30S4S4eS84A3S1S30S4S4cS2fA1S84A3S1S30S4S54S84A3S1S30S4S55SceA1S84A3S1S30S4S53S84A3S30S4S52S84A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfaA) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfaA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfaA ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybfaA_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0SceA2S15eSceZ100A2A2S15cS15fSceZ4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcfaA_0 : In (xc_map nx0) xcfaA. Proof. exact (In_of_cellb (xc_map nx0) xcfaA ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfaA_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S7cA1S26S2S39VW;S96A2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfaA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S96A2S23S2S3fS2fA1S22S2A1A3A3S3cU1A1A2S3aVW;S96S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfaA nx0)). Qed.
Lemma NDUfaA_0 : nodupN (idxsU 1%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfaA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S96A2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfaA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3cU1A1A3Li;S6bU0S29S2S26S2S39VW;S96A2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9faA_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS7cS3aVW;S96S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9faA_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S7cA1S3aVW;S96S2fA3M4A2S3dS7cG4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9faA_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S7cA1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfaA : wsub := Eval vm_compute in (infer_sub NF (S2F FFfaA (KUB W swcfaA nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9faA_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS7cS3aVW;S96S2fA3S2fA3S158VW;Vst;A2S110A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9faA_0 : wsub_idc sFfaA = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110faA_0 : ltac2:(tb__ "0|0|
S0S3S156S110S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
Definition runFfaB : option (list leafA) := Eval vm_compute in (runTF D9faB).
Lemma runFfaB__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19SdfS22S19A1A3A4S23G0S13dS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfaB]). Qed.
Definition FFfaB : axst := Eval vm_compute in (leafS 0 runFfaB).
Lemma CertFfaB_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19SdfS22S19A1M0A3S23S19S7dG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9faB] [FFfaB] [runFfaB]); [exact runFfaB__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfaB : list cell := Eval vm_compute in (cells_at 5 FFfaB).
Definition c1faB : list cell := Eval vm_compute in (cells_at 39 FFfaB).
Definition c2faB : list cell := Eval vm_compute in (cells_at 40 FFfaB).
Definition c4faB : list cell := Eval vm_compute in (cells_at 42 FFfaB).
Definition c5faB : list cell := Eval vm_compute in (cells_at 46 FFfaB).
Definition mcfaB : list cell := Eval vm_compute in (cells_at 47 FFfaB).
Definition xcfaB : list cell := Eval vm_compute in (cells_at 49 FFfaB).
Definition tybfaB : Z := Eval vm_compute in (tyb_of mcfaB).
Lemma SELFfaB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S7dA1A1S3bU1S2cA2A2S26S2S39VW;S97A2S26S2S159S45S2fSabS119S121S129S85S145Z20000S10S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfaB ++ RT_m1 ++ RSF nx0 c1faB c2faB c4faB c5faB mcfaB xcfaB 131072 DZero false)). Qed.
Lemma NDFfaB_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU1S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfaB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S7dA1A1A2A2Li;S3bU1S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfaB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3bU1S2cA2A3Li;S6bU0S29S2S8S18S7dA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfaB_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS7dA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfaB_0 : ax_base FFfaB = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfaB_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfaB_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfaB_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S2cSeS40A1S40X21x2S7S18S7dA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1faB_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSabA3S1S30S4S46SabA3S1S30S4S47SabA3S1S30S4S4bSabA3S1S30S4S49S11S167SbS14eA1SaZ4000A1A3A1SabA3S30S4S48SabA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1faB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1faB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1faB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1faB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1faB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1faB ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcfaB_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S85A3S1S30S4S50S85A3S1S30S4S51S85A3S1S30S4S4dS85A3S1S30S4S4eS85A3S1S30S4S4cS2fA1S85A3S1S30S4S54S85A3S1S30S4S55ScfA1S85A3S1S30S4S53S85A3S30S4S52S85A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfaB) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfaB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfaB ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybfaB_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0ScfA2S15eScfZ100A2A2S15cS15fScfZ4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcfaB_0 : In (xc_map nx0) xcfaB. Proof. exact (In_of_cellb (xc_map nx0) xcfaB ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfaB_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S7dA1S26S2S39VW;S97A2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfaB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S97A2S23S2S3fS2fA1S22S2A1A3A3S3cU1A1A2S3aVW;S97S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfaB nx0)). Qed.
Lemma NDUfaB_0 : nodupN (idxsU 1%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfaB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S97A2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfaB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3cU1A1A3Li;S6bU0S29S2S26S2S39VW;S97A2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9faB_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS7dS3aVW;S97S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9faB_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S7dA1S3aVW;S97S2fA3M4A2S3dS7dG4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9faB_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S7dA1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfaB : wsub := Eval vm_compute in (infer_sub NF (S2F FFfaB (KUB W swcfaB nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9faB_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS7dS3aVW;S97S2fA3S2fA3S158VW;Vst;A2S111A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9faB_0 : wsub_idc sFfaB = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110faB_0 : ltac2:(tb__ "0|0|
S0S3S156S111S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qa)) 0).
Definition S9aqa : axst := Eval vm_compute in (osplit E9qa iMqa (SLit 6144)).
Definition S9bqa : axst := Eval vm_compute in (osplit S9aqa (S iMqa) (SLit 10240)).
Lemma HS9aqa_0 : ltac2:(tb__ "0|0|
S0S19S56SfeS10aSaZ1800A1A3S102A3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqa)). Qed.
Lemma HS9bqa_0 : ltac2:(tb__ "0|0|
S0S19S56S102S2eS10aA1SaZ2800A1A3SbcA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqa)). Qed.
Definition perm9qa : list nat := Eval vm_compute in (S iMqa :: seq 0 (S iMqa) ++ seq (S (S iMqa)) (length (ss_objs (ax_S S9bqa)) - S (S iMqa))).
Definition D9qa : axst := Eval vm_compute in (ax_setS S9bqa (set_objs (ax_S S9bqa) (select (ss_objs (ax_S S9bqa)) perm9qa))).
Lemma HD9qa_0 : ltac2:(tb__ "0|1|
S0S19S1cSbcS72S18SbcA1M0S70S8G0A1Sf4A2A2A2Sb6A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qa)). Qed.
Lemma NDpqa_0 : nodupN perm9qa = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpqa_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18SbcA1A1A2A2Li;Sf4A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpqa_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1Sf4A3Li;S6bU0S29S2S8S18SbcA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qaA : axst := Eval vm_compute in (ax_add_facts (F_A nx0) D9qa).
Definition D9qaB : axst := Eval vm_compute in (ax_add_facts (F_B nx0) D9qa).
Lemma HD9Aqa_0 : ltac2:(tb__ "0|0|
S0S19S74S42S2fA1Sb6A2Se2A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qaA)). Qed.
Lemma HD9Bqa_0 : ltac2:(tb__ "0|0|
S0S19S74S43S2fA1Sb6A2Se3A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qaB)). Qed.
Lemma FBA9qa_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb6A1A1A1S42S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBB9qa_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb6A1A1A1S43S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFqaA : option (list leafA) := Eval vm_compute in (runTF D9qaA).
Lemma runFqaA__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19Se2S22S19A1A3A4S23G0S140S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqaA]). Qed.
Definition FFqaA : axst := Eval vm_compute in (leafS 0 runFqaA).
Lemma CertFqaA_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19Se2S22S19A1M0A3S23S19S80G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qaA] [FFqaA] [runFqaA]); [exact runFqaA__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqaA : list cell := Eval vm_compute in (cells_at 5 FFqaA).
Definition c1qaA : list cell := Eval vm_compute in (cells_at 39 FFqaA).
Definition c2qaA : list cell := Eval vm_compute in (cells_at 40 FFqaA).
Definition c4qaA : list cell := Eval vm_compute in (cells_at 42 FFqaA).
Definition c5qaA : list cell := Eval vm_compute in (cells_at 46 FFqaA).
Definition mcqaA : list cell := Eval vm_compute in (cells_at 47 FFqaA).
Definition xcqaA : list cell := Eval vm_compute in (cells_at 49 FFqaA).
Definition tybqaA : Z := Eval vm_compute in (tyb_of mcqaA).
Lemma SELFqaA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S80A1A1S3bU1S20A2A2S26S2S39VW;S9aA2S26S2S159S45S2fSaeS11cS124S12cS88S148Z20000S10S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqaA ++ RT_m1 ++ RSF nx0 c1qaA c2qaA c4qaA c5qaA mcqaA xcqaA 131072 DZero true)). Qed.
Lemma NDFqaA_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU1S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqaA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S80A1A1A2A2Li;S3bU1S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqaA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3bU1S20A2A3Li;S6bU0S29S2S8S18S80A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqaA_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS80A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqaA_0 : ax_base FFqaA = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqaA_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqaA_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqaA_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S20SeS40A1S40X21x2S7S18S80A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qaA_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSaeA3S1S30S4S46SaeA3S1S30S4S47SaeA3S1S30S4S4bSaeA3S1S30S4S49S11S167SbS14eA1SaZ4000A1A3A1SaeA3S30S4S48SaeA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1qaA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qaA ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcqaA_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S88A3S1S30S4S50S88A3S1S30S4S51S88A3S1S30S4S4dS88A3S1S30S4S4eS88A3S1S30S4S4cS2fA1S88A3S1S30S4S54S88A3S1S30S4S55Sd2A1S88A3S1S30S4S53S88A3S30S4S52S88A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqaA) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqaA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqaA ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybqaA_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0Sd2A2S15eSd2Z100A2A2S15cS15fSd2Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcqaA_0 : In (xc_map nx0) xcqaA. Proof. exact (In_of_cellb (xc_map nx0) xcqaA ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqaA_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S80A1S26S2S39VW;S9aA2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqaA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S9aA2S23S2S3fS2fA1S22S2A1A3A3S3cU1A1A2S3aVW;S9aS2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqaA nx0)). Qed.
Lemma NDUqaA_0 : nodupN (idxsU 1%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqaA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S9aA2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqaA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3cU1A1A3Li;S6bU0S29S2S26S2S39VW;S9aA2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qaA_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS80S3aVW;S9aS2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qaA_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S80A1S3aVW;S9aS2fA3M4A2S3dS80G4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qaA_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S80A1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqaA : wsub := Eval vm_compute in (infer_sub NF (S2F FFqaA (KUB W swcqaA nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9qaA_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS80S3aVW;S9aS2fA3S2fA3S158VW;Vst;A2S114A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qaA_0 : wsub_idc sFqaA = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qaA_0 : ltac2:(tb__ "0|0|
S0S3S156S114S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
Definition runFqaB : option (list leafA) := Eval vm_compute in (runTF D9qaB).
Lemma runFqaB__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19Se3S22S19A1A3A4S23G0S141S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqaB]). Qed.
Definition FFqaB : axst := Eval vm_compute in (leafS 0 runFqaB).
Lemma CertFqaB_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19Se3S22S19A1M0A3S23S19S81G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qaB] [FFqaB] [runFqaB]); [exact runFqaB__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqaB : list cell := Eval vm_compute in (cells_at 5 FFqaB).
Definition c1qaB : list cell := Eval vm_compute in (cells_at 39 FFqaB).
Definition c2qaB : list cell := Eval vm_compute in (cells_at 40 FFqaB).
Definition c4qaB : list cell := Eval vm_compute in (cells_at 42 FFqaB).
Definition c5qaB : list cell := Eval vm_compute in (cells_at 46 FFqaB).
Definition mcqaB : list cell := Eval vm_compute in (cells_at 47 FFqaB).
Definition xcqaB : list cell := Eval vm_compute in (cells_at 49 FFqaB).
Definition tybqaB : Z := Eval vm_compute in (tyb_of mcqaB).
Lemma SELFqaB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S81A1A1S3bU1S20A2A2S26S2S39VW;S9bA2S26S2S159S45S2fSafS11dS125S12dS89S149Z20000S10S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqaB ++ RT_m1 ++ RSF nx0 c1qaB c2qaB c4qaB c5qaB mcqaB xcqaB 131072 DZero true)). Qed.
Lemma NDFqaB_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU1S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqaB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S81A1A1A2A2Li;S3bU1S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqaB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3bU1S20A2A3Li;S6bU0S29S2S8S18S81A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqaB_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS81A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqaB_0 : ax_base FFqaB = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqaB_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S81A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqaB_0 : ltac2:(tb__ "0|0|
S32S5Sa0S7S18S81A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqaB_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S20SeS40A1S40X21x2S7S18S81A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qaB_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSafA3S1S30S4S46SafA3S1S30S4S47SafA3S1S30S4S4bSafA3S1S30S4S49S11S167SbS14eA1SaZ4000A1A3A1SafA3S30S4S48SafA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1qaB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qaB ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcqaB_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S89A3S1S30S4S50S89A3S1S30S4S51S89A3S1S30S4S4dS89A3S1S30S4S4eS89A3S1S30S4S4cS2fA1S89A3S1S30S4S54S89A3S1S30S4S55Sd3A1S89A3S1S30S4S53S89A3S30S4S52S89A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqaB) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqaB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqaB ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybqaB_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0Sd3A2S15eSd3Z100A2A2S15cS15fSd3Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcqaB_0 : In (xc_map nx0) xcqaB. Proof. exact (In_of_cellb (xc_map nx0) xcqaB ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqaB_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S81A1S26S2S39VW;S9bA2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqaB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S9bA2S23S2S3fS2fA1S22S2A1A3A3S3cU1A1A2S3aVW;S9bS2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqaB nx0)). Qed.
Lemma NDUqaB_0 : nodupN (idxsU 1%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqaB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S9bA2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqaB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3cU1A1A3Li;S6bU0S29S2S26S2S39VW;S9bA2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qaB_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS81S3aVW;S9bS2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qaB_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S81A1S3aVW;S9bS2fA3M4A2S3dS81G4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qaB_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S81A1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqaB : wsub := Eval vm_compute in (infer_sub NF (S2F FFqaB (KUB W swcqaB nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9qaB_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS81S3aVW;S9bS2fA3S2fA3S158VW;Vst;A2S115A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qaB_0 : wsub_idc sFqaB = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qaB_0 : ltac2:(tb__ "0|0|
S0S3S156S115S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition PXb : list sobj := [O_w].
Definition FXPb : list sprop := ltac2:(tb__ "0|0|
S23S5SeS13S168SbS14fA1SbS14eA1A3A1S22S5A1A3").

Definition C5Ab : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5bc).
Definition C5Bb : axst := Eval vm_compute in (ax_add_facts (F_B nx0) C5bc).
Lemma HC5Ab_0 : ltac2:(tb__ "0|0|
S0S19S74S42S2fA1S16fA2Sd7A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ab)). Qed.
Lemma HC5Bb_0 : ltac2:(tb__ "0|0|
S0S19S74S43S2fA1S16fA2Sd9A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Bb)). Qed.
Lemma FBAb_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18S16fA1A1A1S42S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBBb_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18S16fA1A1A1S43S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run6Ab : option (list leafA) := Eval vm_compute in (runT6 C5Ab).
Lemma run6Ab__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sd7S22S19A1A3A4S23G0S131S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ab]). Qed.
Definition Y6Ab : axst := Eval vm_compute in (leafS 0 run6Ab).
Lemma Cert6Ab_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sd7S22S19A1M0A3S23S19S105G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ab] [Y6Ab] [run6Ab]); [exact run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition run6Bb : option (list leafA) := Eval vm_compute in (runT6 C5Bb).
Lemma run6Bb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sd9S22S19A1A3A4S23G0S133S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Bb]). Qed.
Definition Y6Bb : axst := Eval vm_compute in (leafS 0 run6Bb).
Lemma Cert6Bb_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sd9S22S19A1M0A3S23S19S107G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Bb] [Y6Bb] [run6Bb]); [exact run6Bb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6b : axst := Eval vm_compute in (rmF (F_A nx0) Y6Ab).
Definition s6Ab : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ab) (ax_S E6b)).
Lemma E6Ab_0 : ltac2:(tb__ "0|0|
S0S21S1dS105Sb9S10dA3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ab_0 : ltac2:(tb__ "0|0|
S0S21S157S10dVGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6Bb : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Bb) (ax_S E6b)).
Lemma E6Bb_0 : ltac2:(tb__ "0|0|
S0S21S1dS107Sb9S10fA3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Bb_0 : ltac2:(tb__ "0|0|
S0S21S157S10fVGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6b : axst := Eval vm_compute in (rstS E6b ru6 []).
Definition CO6b : axst := Eval vm_compute in (carveS CT6b (O_3 nx0)).
Lemma WC6b_0 : ltac2:(tb__ "0|0|
S0S21S9S18S8dA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6b_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sb9A1S18S8dA1A2S2bG3S2aG1G2S23G0S2aS3S3S65S2fA1S59A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6b_0 : ltac2:(tb__ "0|0|
S0S36S6S18S8dA1A1S6S18Sb9A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6b))). Qed.
Lemma HC6b_0 : ltac2:(tb__ "0|0|
S0S19S1cSb9S18S8dA1A2S8dA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6b)). Qed.
Lemma SK6b_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18S8dA1A1A4S6aS2G0S7bS26S2S23S2S153S2fA1S23S2S150S2fA1S22S2A1A3A3S26S2S15bU1S2fA2ScdA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXb))). Qed.
Lemma FC6b_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S8dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6b_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18S8dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6b_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS8dA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6b_0 : ltac2:(tb__ "0|0|
S0S19S151S8dSfS5cS2fA1SaZ0A1S59S22S4A1SdA5A2S93A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6b)). Qed.
Lemma WCO6b_0 : ltac2:(tb__ "0|0|
S0S21S9S18S93A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6b : wsub := Eval vm_compute in (callsub CO6b Pre_memsetA).
Definition R6b : list sobj := Eval vm_compute in (callR CO6b Pre_memsetA s6b).
Definition T6b : axst := Eval vm_compute in (callT CO6b Pre_memsetA Pret_ms s6b R6b).
Lemma He6b_0 : ltac2:(tb__ "0|1|
S0S28S24S2A1M0A1S164S93S14cSf7A3S2bG0Se7A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6b)). Qed.
Lemma Hchk6b_0 : ltac2:(tb__ "0|0|
S0S21S163S93S14cSf7Se7S6aS1aS19S1fS14dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6b_0 : ltac2:(tb__ "0|0|
S0S19S165Sf7S14cS154S93Se7A5SedA3"). Proof. vm_cast_no_check (@eq_refl _ (T6b)). Qed.
Lemma FBC6b_0 : ltac2:(tb__ "0|1|
S0S21S31S5ScS6S18S93A1M0A1A1S7G0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6b_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18SedA1A1A1S7S18S93A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S0S21S166VGS0;S6S18S93A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6b : axst := Eval vm_compute in (ax_with_facts T6b (ss_facts (ax_S CO6b))).
Lemma HD6b_0 : ltac2:(tb__ "0|0|
S0S19S162SedS7S18S93A1A1A2Sc3A3"). Proof. vm_cast_no_check (@eq_refl _ (D6b)). Qed.

Definition U7b : axst := Eval vm_compute in (U7p nx0 D6b).
Lemma WU7b_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sa5A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7b_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc3A1S18Sa5A1A2S2bG3S2aG1G2S22G0A1S5fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7b_0 : ltac2:(tb__ "0|0|
S0S36S6S18Sa5A1A1S6S18Sc3A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6b))). Qed.
Lemma HU7b_0 : ltac2:(tb__ "0|0|
S0S19S1cSc3S18Sa5A1A2Sa5A3"). Proof. vm_cast_no_check (@eq_refl _ (U7b)). Qed.
Definition run7b : option (list leafA) := Eval vm_compute in (runT6 U7b).
Lemma run7b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sa5S22S19A1A3A4S23G0S135S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7b]). Qed.
Definition ET7b : axst := Eval vm_compute in (leafS 0 run7b).
Lemma Cert7b_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sa5S22S19A1M0A3S23S19Sc9G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7b] [ET7b] [run7b]); [exact run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7b : axst := Eval vm_compute in (rstS ET7b (ru7 nx0) []).
Definition CO7b : axst := Eval vm_compute in (carveS CT7b (O_3n nx0)).
Definition CR7b : axst := Eval vm_compute in (CDepotCall.oreb CO7b 1).
Definition n7b : nat := Eval vm_compute in (length (ss_objs (ax_S CR7b))).
Definition CS7b : axst := Eval vm_compute in (sel7 CR7b).
Definition CM7b : axst := Eval vm_compute in (CDepotCall.omrg CS7b 1).
Lemma WC7b_0 : ltac2:(tb__ "0|0|
S0S21S9S18S8fA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7b_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc9A1S18S8fA1A2S2bG3S2aG1G2S23G0S2aS3S3S64S2fA1S152S2fA1A4S23G0S2aS3S3S66S2fA1S62A4S22G0A1A3A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S0S36S6S18S8fA1A1S6S18Sc9A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7b))). Qed.
Lemma HC7b_0 : ltac2:(tb__ "0|0|
S0S19S1cSc9S18S8fA1A2S8fA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7b)). Qed.
Lemma SK7b_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18S8fA1A1A4S6aS2G0S7bS26S2S23S2S57S2fA1S23S2S153S2fA1S23S2S150S2fA1S22S2A1A3A3A3S26S2S15bU1S2fA2ScdA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXb))). Qed.
Lemma FC7b_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S8fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7b_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18S8fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7b_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS8fA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7b_0 : ltac2:(tb__ "0|0|
S0S19S151S8fSfS152S2fA1SaZ0A1SaZ100A1S22S4A1SdA5A2SbfA3"). Proof. vm_cast_no_check (@eq_refl _ (CO7b)). Qed.
Lemma WCO7b_0 : ltac2:(tb__ "0|0|
S0S21S9S18SbfA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7b_0 : ltac2:(tb__ "0|0|
S0S21S16bS12S171S18SbfA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7b_0 : ltac2:(tb__ "0|0|
S0S19S16dSbfU1A2SdbA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7b)). Qed.
Lemma LEN7b_0 : ltac2:(tb__ "0|0|
S0S25S29S2S8S18SdbA1A1A2Sb3A3"). Proof. vm_cast_no_check (@eq_refl _ (n7b)). Qed.
Lemma PERM_nd7b_0 : ltac2:(tb__ "0|0|
S0S21S71S58Sb3A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7b_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1Sb3A2Li;S58Sb3A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7b_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S58Sb3A1A3Li;S6bU0Sb3A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7b_0 : ltac2:(tb__ "0|0|
S0S19S69SdbA1SddA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7b)). Qed.
Lemma MRG7b_0 : ltac2:(tb__ "0|0|
S0S21S16bS12S170S18SddA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7b_0 : ltac2:(tb__ "0|0|
S0S19S16cSddU1A2S9fA3"). Proof. vm_cast_no_check (@eq_refl _ (CM7b)). Qed.
Definition s7b : wsub := Eval vm_compute in (callsub CM7b Pre_memsetA).
Definition R7b : list sobj := Eval vm_compute in (callR CM7b Pre_memsetA s7b).
Definition T7b : axst := Eval vm_compute in (callT CM7b Pre_memsetA Pret_ms s7b R7b).
Lemma He7b_0 : ltac2:(tb__ "0|1|
S0S28S24S2A1M0A1S164S9fS14cSf9A3S2bG0Se9A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7b)). Qed.
Lemma Hchk7b_0 : ltac2:(tb__ "0|0|
S0S21S163S9fS14cSf9Se9S6aS1aS19S1fS14dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7b_0 : ltac2:(tb__ "0|0|
S0S19S165Sf9S14cS154S9fSe9A5SefA3"). Proof. vm_cast_no_check (@eq_refl _ (T7b)). Qed.
Lemma FBC7b_0 : ltac2:(tb__ "0|1|
S0S21S31S5ScS6S18S9fA1M0A1A1S7G0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7b_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18SefA1A1A1S7S18S9fA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7b_0 : ltac2:(tb__ "0|0|
S0S21S166VGS0;S6S18S9fA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7b : axst := Eval vm_compute in (ax_with_facts T7b (ss_facts (ax_S CM7b))).
Lemma HD7b_0 : ltac2:(tb__ "0|0|
S0S19S162SefS7S18S9fA1A1A2Sc5A3"). Proof. vm_cast_no_check (@eq_refl _ (D7b)). Qed.

Definition U8b : axst := Eval vm_compute in (U8p nx0 D7b).
Lemma WU8b_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sa7A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8b_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc5A1S18Sa7A1A2S2bG3S2aG1G2S22G0A1S60S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8b_0 : ltac2:(tb__ "0|0|
S0S36S6S18Sa7A1A1S6S18Sc5A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7b))). Qed.
Lemma HU8b_0 : ltac2:(tb__ "0|0|
S0S19S1cSc5S18Sa7A1A2Sa7A3"). Proof. vm_cast_no_check (@eq_refl _ (U8b)). Qed.
Definition run8b : option (list leafA) := Eval vm_compute in (runT6 U8b).
Lemma run8b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S76S22S35A1A3S23S19Sa7S22S19A1A3A4S23G0S137S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8b]). Qed.
Definition ET8b : axst := Eval vm_compute in (leafS 0 run8b).
Lemma Cert8b_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S76S22S35A1A3VGS0;S23S19Sa7S22S19A1M0A3S23S19ScbG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8b] [ET8b] [run8b]); [exact run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8b : axst := Eval vm_compute in (CT8p nx0 ET8b).
Definition CO8b : axst := Eval vm_compute in (carveS CT8b (O_4 nx0)).
Lemma WC8b_0 : ltac2:(tb__ "0|0|
S0S21S9S18S91A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8b_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18ScbA1S18S91A1A2S2bG3S2aG1G2S22G0A1S68S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8b_0 : ltac2:(tb__ "0|0|
S0S36S6S18S91A1A1S6S18ScbA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8b))). Qed.
Lemma HC8b_0 : ltac2:(tb__ "0|0|
S0S19S1cScbS18S91A1A2S91A3"). Proof. vm_cast_no_check (@eq_refl _ (CT8b)). Qed.
Lemma SK8b_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18S91A1A1A4S6aS2G0S7bS26S2S23S2S5aS2fA1S23S2S57S2fA1S23S2S150S2fA1S22S2A1A3A3A3S26S2S15bU1S2fA2ScdA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXb))). Qed.
Lemma FC8b_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S91A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8b_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18S91A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8b_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS91A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8b_0 : ltac2:(tb__ "0|0|
S0S19S151S91SfS5dS2fA1SaZ0A1S67S2fA1S22S4A1SdA5A2S95A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8b)). Qed.
Lemma WCO8b_0 : ltac2:(tb__ "0|0|
S0S21S9S18S95A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8b : wsub := Eval vm_compute in (callsub CO8b Pre_mszA).
Definition R8b : list sobj := Eval vm_compute in (callR CO8b Pre_mszA s8b).
Definition T8b : axst := Eval vm_compute in (callT CO8b Pre_mszA Pret_mz s8b R8b).
Lemma He8b_0 : ltac2:(tb__ "0|1|
S0S28S24S2A1M0A1S164S95S160SfbA3S2bG0SebA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8b)). Qed.
Lemma Hchk8b_0 : ltac2:(tb__ "0|0|
S0S21S163S95S160SfbSebS6aS1aS19S1fS161A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8b_0 : ltac2:(tb__ "0|0|
S0S19S165SfbS160S155S95SebA5Sf1A3"). Proof. vm_cast_no_check (@eq_refl _ (T8b)). Qed.
Lemma FBC8b_0 : ltac2:(tb__ "0|1|
S0S21S31S5ScS6S18S95A1M0A1A1S7G0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8b_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sf1A1A1A1S7S18S95A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8b_0 : ltac2:(tb__ "0|0|
S0S21S166VGS0;S6S18S95A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8b : axst := Eval vm_compute in (ax_with_facts T8b (ss_facts (ax_S CO8b))).
Lemma HD8b_0 : ltac2:(tb__ "0|0|
S0S19S162Sf1S7S18S95A1A1A2Sc7A3"). Proof. vm_cast_no_check (@eq_refl _ (D8b)). Qed.

Definition U9b : axst := Eval vm_compute in (U9p nx0 D8b).
Lemma WU9b_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sa9A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9b_0 : ltac2:(tb__ "0|4|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS18Sc7A1S18Sa9A1A2S2bG3S2aG1G2S22G0A1S61S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9b_0 : ltac2:(tb__ "0|0|
S0S36S6S18Sa9A1A1S6S18Sc7A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8b))). Qed.
Lemma HU9b_0 : ltac2:(tb__ "0|0|
S0S19S1cSc7S18Sa9A1A2Sa9A3"). Proof. vm_cast_no_check (@eq_refl _ (U9b)). Qed.
Definition run9b : option (list leafA) := Eval vm_compute in (runT9 U9b).
Lemma run9b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S44S23S35S5bS22S35A1A3A3S23S19Sa9S22S19A1A3A4S23G0S139S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9b]). Qed.
Definition E9fb : axst := Eval vm_compute in (leafS 0 run9b).
Definition E9pb : axst := Eval vm_compute in (leafS 1 run9b).
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S44S23S35S5bS22S35A1A3A3VGS0;S23S19Sa9S22S19A1M0A3S23S19SfdS23S19Sa3G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC; PGST] GS0 [U9b] [E9fb; E9pb] [run9b]); [exact run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9b_0 : ltac2:(tb__ "0|1|
S0S24S27S27S3S3A2S3A2M0A1S6aS2G0S7bS8S18Sa3A1A1A4S6aS2G0S7bS26S2S23S2S63S2fA1S23S2S5aS2fA1S23S2S57S2fA1S23S2S150S2fA1S22S2A1A3A3A3A3S26S2S15bU1S2fA2ScdA3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 1%nat nx0 ++ PXb))). Qed.
Lemma FC9b_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18Sa3A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9b_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18Sa3A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9b_0 : ltac2:(tb__ "0|0|
S30S5SeS40A1S7S18Sa3A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9b_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bSa3A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pb : axst := Eval vm_compute in (carveS E9pb (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9b_0 : ltac2:(tb__ "0|0|
S0S19S151Sa3SfS5eS2fA1SaZ0A1SaZ1A1S22S4A1SdA5A2Sc1A3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pb)). Qed.
Lemma WCO9b_0 : ltac2:(tb__ "0|0|
S0S21S9S18Sc1A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qb : option (list leafA) := Eval vm_compute in (runT9q CO9pb).
Lemma run9qb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S23S35S44S22S35A1A3S23S19Sc1S22S19A1A3A4S23G0S13bS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qb]). Qed.
Definition E9qb : axst := Eval vm_compute in (leafS 0 run9qb).
Lemma Cert9qb_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S23S35S44S22S35A1A3VGS0;S23S19Sc1S22S19A1M0A3S23S19SffG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [CPC] GS0 [CO9pb] [E9qb] [run9qb]); [exact run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fb)) 0).
Definition S9afb : axst := Eval vm_compute in (osplit E9fb iMfb (SLit 6144)).
Definition S9bfb : axst := Eval vm_compute in (osplit S9afb (S iMfb) (SLit 10240)).
Lemma HS9afb_0 : ltac2:(tb__ "0|0|
S0S19S56SfdS109SaZ1800A1A3S101A3"). Proof. vm_cast_no_check (@eq_refl _ (S9afb)). Qed.
Lemma HS9bfb_0 : ltac2:(tb__ "0|0|
S0S19S56S101S2eS109A1SaZ2800A1A3SbbA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfb)). Qed.
Definition perm9fb : list nat := Eval vm_compute in (S iMfb :: seq 0 (S iMfb) ++ seq (S (S iMfb)) (length (ss_objs (ax_S S9bfb)) - S (S iMfb))).
Definition D9fb : axst := Eval vm_compute in (ax_setS S9bfb (set_objs (ax_S S9bfb) (select (ss_objs (ax_S S9bfb)) perm9fb))).
Lemma HD9fb_0 : ltac2:(tb__ "0|1|
S0S19S1cSbbS72S18SbbA1M0S70S8G0A1Sf3A2A2A2Sb5A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fb)). Qed.
Lemma NDpfb_0 : nodupN perm9fb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpfb_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18SbbA1A1A2A2Li;Sf3A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpfb_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1Sf3A3Li;S6bU0S29S2S8S18SbbA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9fbA : axst := Eval vm_compute in (ax_add_facts (F_A nx0) D9fb).
Definition D9fbB : axst := Eval vm_compute in (ax_add_facts (F_B nx0) D9fb).
Lemma HD9Afb_0 : ltac2:(tb__ "0|0|
S0S19S74S42S2fA1Sb5A2Se0A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fbA)). Qed.
Lemma HD9Bfb_0 : ltac2:(tb__ "0|0|
S0S19S74S43S2fA1Sb5A2Se1A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fbB)). Qed.
Lemma FBA9fb_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb5A1A1A1S42S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBB9fb_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb5A1A1A1S43S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFfbA : option (list leafA) := Eval vm_compute in (runTF D9fbA).
Lemma runFfbA__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19Se0S22S19A1A3A4S23G0S13eS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfbA]). Qed.
Definition FFfbA : axst := Eval vm_compute in (leafS 0 runFfbA).
Lemma CertFfbA_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19Se0S22S19A1M0A3S23S19S7eG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fbA] [FFfbA] [runFfbA]); [exact runFfbA__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfbA : list cell := Eval vm_compute in (cells_at 5 FFfbA).
Definition c1fbA : list cell := Eval vm_compute in (cells_at 39 FFfbA).
Definition c2fbA : list cell := Eval vm_compute in (cells_at 40 FFfbA).
Definition c4fbA : list cell := Eval vm_compute in (cells_at 42 FFfbA).
Definition c5fbA : list cell := Eval vm_compute in (cells_at 46 FFfbA).
Definition mcfbA : list cell := Eval vm_compute in (cells_at 47 FFfbA).
Definition xcfbA : list cell := Eval vm_compute in (cells_at 49 FFfbA).
Definition tybfbA : Z := Eval vm_compute in (tyb_of mcfbA).
Lemma SELFfbA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S7eA1A1S3bU1S2cA2A2S26S2S39VW;S98A2S26S2S159S45S2fSacS11aS122S12aS86S146Z8SdS2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfbA ++ RT_m1 ++ RSF nx0 c1fbA c2fbA c4fbA c5fbA mcfbA xcfbA 8 DUnknown false)). Qed.
Lemma NDFfbA_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU1S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfbA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S7eA1A1A2A2Li;S3bU1S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfbA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3bU1S2cA2A3Li;S6bU0S29S2S8S18S7eA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfbA_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS7eA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfbA_0 : ax_base FFfbA = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfbA_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfbA_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfbA_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S2cSeS40A1S40X21x2S7S18S7eA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fbA_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSacA3S1S30S4S46SacA3S1S30S4S47SacA3S1S30S4S4bSacA3S1S30S4S49SbS14eA1A1SacA3S30S4S48SacA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1fbA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fbA ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcfbA_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S86A3S1S30S4S50S86A3S1S30S4S51S86A3S1S30S4S4dS86A3S1S30S4S4eS86A3S1S30S4S4cS2fA1S86A3S1S30S4S54S86A3S1S30S4S55Sd0A1S86A3S1S30S4S53S86A3S30S4S52S86A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfbA) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfbA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfbA ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybfbA_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0Sd0A2S15eSd0Z100A2A2S15cS15fSd0Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcfbA_0 : In (xc_map nx0) xcfbA. Proof. exact (In_of_cellb (xc_map nx0) xcfbA ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfbA_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S7eA1S26S2S39VW;S98A2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfbA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S98A2S23S2S3fS2fA1S22S2A1A3A3S3cU1A1A2S3aVW;S98S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfbA nx0)). Qed.
Lemma NDUfbA_0 : nodupN (idxsU 1%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfbA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S98A2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfbA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3cU1A1A3Li;S6bU0S29S2S26S2S39VW;S98A2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fbA_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS7eS3aVW;S98S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fbA_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S7eA1S3aVW;S98S2fA3M4A2S3dS7eG4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fbA_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S7eA1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfbA : wsub := Eval vm_compute in (infer_sub NF (S2F FFfbA (KUB W swcfbA nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9fbA_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS7eS3aVW;S98S2fA3S2fA3S158VW;Vst;A2S112A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fbA_0 : wsub_idc sFfbA = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fbA_0 : ltac2:(tb__ "0|0|
S0S3S156S112S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
Definition runFfbB : option (list leafA) := Eval vm_compute in (runTF D9fbB).
Lemma runFfbB__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19Se1S22S19A1A3A4S23G0S13fS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfbB]). Qed.
Definition FFfbB : axst := Eval vm_compute in (leafS 0 runFfbB).
Lemma CertFfbB_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19Se1S22S19A1M0A3S23S19S7fG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fbB] [FFfbB] [runFfbB]); [exact runFfbB__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfbB : list cell := Eval vm_compute in (cells_at 5 FFfbB).
Definition c1fbB : list cell := Eval vm_compute in (cells_at 39 FFfbB).
Definition c2fbB : list cell := Eval vm_compute in (cells_at 40 FFfbB).
Definition c4fbB : list cell := Eval vm_compute in (cells_at 42 FFfbB).
Definition c5fbB : list cell := Eval vm_compute in (cells_at 46 FFfbB).
Definition mcfbB : list cell := Eval vm_compute in (cells_at 47 FFfbB).
Definition xcfbB : list cell := Eval vm_compute in (cells_at 49 FFfbB).
Definition tybfbB : Z := Eval vm_compute in (tyb_of mcfbB).
Lemma SELFfbB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S7fA1A1S3bU1S2cA2A2S26S2S39VW;S99A2S26S2S159S45S2fSadS11bS123S12bS87S147Z8SdS2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfbB ++ RT_m1 ++ RSF nx0 c1fbB c2fbB c4fbB c5fbB mcfbB xcfbB 8 DUnknown false)). Qed.
Lemma NDFfbB_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU1S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfbB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S7fA1A1A2A2Li;S3bU1S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfbB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3bU1S2cA2A3Li;S6bU0S29S2S8S18S7fA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfbB_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS7fA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfbB_0 : ax_base FFfbB = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfbB_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfbB_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfbB_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S2cSeS40A1S40X21x2S7S18S7fA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fbB_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSadA3S1S30S4S46SadA3S1S30S4S47SadA3S1S30S4S4bSadA3S1S30S4S49SbS14eA1A1SadA3S30S4S48SadA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1fbB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fbB ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcfbB_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S87A3S1S30S4S50S87A3S1S30S4S51S87A3S1S30S4S4dS87A3S1S30S4S4eS87A3S1S30S4S4cS2fA1S87A3S1S30S4S54S87A3S1S30S4S55Sd1A1S87A3S1S30S4S53S87A3S30S4S52S87A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfbB) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfbB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfbB ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybfbB_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0Sd1A2S15eSd1Z100A2A2S15cS15fSd1Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcfbB_0 : In (xc_map nx0) xcfbB. Proof. exact (In_of_cellb (xc_map nx0) xcfbB ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfbB_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S7fA1S26S2S39VW;S99A2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfbB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S99A2S23S2S3fS2fA1S22S2A1A3A3S3cU1A1A2S3aVW;S99S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfbB nx0)). Qed.
Lemma NDUfbB_0 : nodupN (idxsU 1%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfbB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S99A2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfbB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3cU1A1A3Li;S6bU0S29S2S26S2S39VW;S99A2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fbB_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS7fS3aVW;S99S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fbB_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S7fA1S3aVW;S99S2fA3M4A2S3dS7fG4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fbB_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S7fA1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfbB : wsub := Eval vm_compute in (infer_sub NF (S2F FFfbB (KUB W swcfbB nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9fbB_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS7fS3aVW;S99S2fA3S2fA3S158VW;Vst;A2S113A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fbB_0 : wsub_idc sFfbB = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fbB_0 : ltac2:(tb__ "0|0|
S0S3S156S113S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qb)) 0).
Definition S9aqb : axst := Eval vm_compute in (osplit E9qb iMqb (SLit 6144)).
Definition S9bqb : axst := Eval vm_compute in (osplit S9aqb (S iMqb) (SLit 10240)).
Lemma HS9aqb_0 : ltac2:(tb__ "0|0|
S0S19S56SffS10bSaZ1800A1A3S103A3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqb)). Qed.
Lemma HS9bqb_0 : ltac2:(tb__ "0|0|
S0S19S56S103S2eS10bA1SaZ2800A1A3SbdA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqb)). Qed.
Definition perm9qb : list nat := Eval vm_compute in (S iMqb :: seq 0 (S iMqb) ++ seq (S (S iMqb)) (length (ss_objs (ax_S S9bqb)) - S (S iMqb))).
Definition D9qb : axst := Eval vm_compute in (ax_setS S9bqb (set_objs (ax_S S9bqb) (select (ss_objs (ax_S S9bqb)) perm9qb))).
Lemma HD9qb_0 : ltac2:(tb__ "0|1|
S0S19S1cSbdS72S18SbdA1M0S70S8G0A1Sf5A2A2A2Sb7A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qb)). Qed.
Lemma NDpqb_0 : nodupN perm9qb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDpqb_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18SbdA1A1A2A2Li;Sf5A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVpqb_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1Sf5A3Li;S6bU0S29S2S8S18SbdA1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qbA : axst := Eval vm_compute in (ax_add_facts (F_A nx0) D9qb).
Definition D9qbB : axst := Eval vm_compute in (ax_add_facts (F_B nx0) D9qb).
Lemma HD9Aqb_0 : ltac2:(tb__ "0|0|
S0S19S74S42S2fA1Sb7A2Se4A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qbA)). Qed.
Lemma HD9Bqb_0 : ltac2:(tb__ "0|0|
S0S19S74S43S2fA1Sb7A2Se5A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qbB)). Qed.
Lemma FBA9qb_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb7A1A1A1S42S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBB9qb_0 : ltac2:(tb__ "0|0|
S0S21S31S5ScS6S18Sb7A1A1A1S43S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition runFqbA : option (list leafA) := Eval vm_compute in (runTF D9qbA).
Lemma runFqbA__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19Se4S22S19A1A3A4S23G0S142S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqbA]). Qed.
Definition FFqbA : axst := Eval vm_compute in (leafS 0 runFqbA).
Lemma CertFqbA_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19Se4S22S19A1M0A3S23S19S82G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qbA] [FFqbA] [runFqbA]); [exact runFqbA__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqbA : list cell := Eval vm_compute in (cells_at 5 FFqbA).
Definition c1qbA : list cell := Eval vm_compute in (cells_at 39 FFqbA).
Definition c2qbA : list cell := Eval vm_compute in (cells_at 40 FFqbA).
Definition c4qbA : list cell := Eval vm_compute in (cells_at 42 FFqbA).
Definition c5qbA : list cell := Eval vm_compute in (cells_at 46 FFqbA).
Definition mcqbA : list cell := Eval vm_compute in (cells_at 47 FFqbA).
Definition xcqbA : list cell := Eval vm_compute in (cells_at 49 FFqbA).
Definition tybqbA : Z := Eval vm_compute in (tyb_of mcqbA).
Lemma SELFqbA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S82A1A1S3bU1S20A2A2S26S2S39VW;S9cA2S26S2S159S45S2fSb0S11eS126S12eS8aS14aZ8SdS20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqbA ++ RT_m1 ++ RSF nx0 c1qbA c2qbA c4qbA c5qbA mcqbA xcqbA 8 DUnknown true)). Qed.
Lemma NDFqbA_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU1S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqbA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S82A1A1A2A2Li;S3bU1S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqbA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3bU1S20A2A3Li;S6bU0S29S2S8S18S82A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqbA_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS82A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqbA_0 : ax_base FFqbA = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqbA_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S82A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqbA_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18S82A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqbA_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S20SeS40A1S40X21x2S7S18S82A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qbA_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSb0A3S1S30S4S46Sb0A3S1S30S4S47Sb0A3S1S30S4S4bSb0A3S1S30S4S49SbS14eA1A1Sb0A3S30S4S48Sb0A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1qbA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qbA ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcqbA_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S8aA3S1S30S4S50S8aA3S1S30S4S51S8aA3S1S30S4S4dS8aA3S1S30S4S4eS8aA3S1S30S4S4cS2fA1S8aA3S1S30S4S54S8aA3S1S30S4S55Sd4A1S8aA3S1S30S4S53S8aA3S30S4S52S8aA3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqbA) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqbA ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqbA ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybqbA_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0Sd4A2S15eSd4Z100A2A2S15cS15fSd4Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcqbA_0 : In (xc_map nx0) xcqbA. Proof. exact (In_of_cellb (xc_map nx0) xcqbA ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqbA_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S82A1S26S2S39VW;S9cA2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqbA_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S9cA2S23S2S3fS2fA1S22S2A1A3A3S3cU1A1A2S3aVW;S9cS2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqbA nx0)). Qed.
Lemma NDUqbA_0 : nodupN (idxsU 1%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqbA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S9cA2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqbA_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3cU1A1A3Li;S6bU0S29S2S26S2S39VW;S9cA2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qbA_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS82S3aVW;S9cS2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qbA_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S82A1S3aVW;S9cS2fA3M4A2S3dS82G4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qbA_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S82A1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqbA : wsub := Eval vm_compute in (infer_sub NF (S2F FFqbA (KUB W swcqbA nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9qbA_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS82S3aVW;S9cS2fA3S2fA3S158VW;Vst;A2S116A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qbA_0 : wsub_idc sFqbA = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qbA_0 : ltac2:(tb__ "0|0|
S0S3S156S116S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
Definition runFqbB : option (list leafA) := Eval vm_compute in (runTF D9qbB).
Lemma runFqbB__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S1aA1A1M0A1S75S38Ufa0S22S35A1S23S19Se5S22S19A1A3A4S23G0S143S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqbB]). Qed.
Definition FFqbB : axst := Eval vm_compute in (leafS 0 runFqbB).
Lemma CertFqbB_0 : ltac2:(tb__ "0|1|
S0S21S73S38Ufa0S22S35A1VGS0;S23S19Se5S22S19A1M0A3S23S19S83G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qbB] [FFqbB] [runFqbB]); [exact runFqbB__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqbB : list cell := Eval vm_compute in (cells_at 5 FFqbB).
Definition c1qbB : list cell := Eval vm_compute in (cells_at 39 FFqbB).
Definition c2qbB : list cell := Eval vm_compute in (cells_at 40 FFqbB).
Definition c4qbB : list cell := Eval vm_compute in (cells_at 42 FFqbB).
Definition c5qbB : list cell := Eval vm_compute in (cells_at 46 FFqbB).
Definition mcqbB : list cell := Eval vm_compute in (cells_at 47 FFqbB).
Definition xcqbB : list cell := Eval vm_compute in (cells_at 49 FFqbB).
Definition tybqbB : Z := Eval vm_compute in (tyb_of mcqbB).
Lemma SELFqbB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S8S18S83A1A1S3bU1S20A2A2S26S2S39VW;S9dA2S26S2S159S45S2fSb1S11fS127S12fS8bS14bZ8SdS20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqbB ++ RT_m1 ++ RSF nx0 c1qbB c2qbB c4qbB c5qbB mcqbB xcqbB 8 DUnknown true)). Qed.
Lemma NDFqbB_0 : ltac2:(tb__ "0|0|
S0S21S71S3bU1S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqbB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S8S18S83A1A1A2A2Li;S3bU1S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqbB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3bU1S20A2A3Li;S6bU0S29S2S8S18S83A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqbB_0 : ltac2:(tb__ "0|1|
S0S24S27S3S3A2M0A1S1bS83A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqbB_0 : ax_base FFqbB = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqbB_0 : ltac2:(tb__ "0|0|
S32S5S26S5S79VW;Vst;A2S78S77A1A3S7S18S83A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqbB_0 : ltac2:(tb__ "0|0|
S32S5Sa1S7S18S83A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqbB_0 : ltac2:(tb__ "0|0|
S30S5S21S5L_;S20SeS40A1S40X21x2S7S18S83A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qbB_0 : ltac2:(tb__ "0|0|
S1S30S4S4aSb1A3S1S30S4S46Sb1A3S1S30S4S47Sb1A3S1S30S4S4bSb1A3S1S30S4S49SbS14eA1A1Sb1A3S30S4S48Sb1A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1qbB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qbB ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma HmcqbB_0 : ltac2:(tb__ "0|0|
S1S30S4S4fS2fA1S8bA3S1S30S4S50S8bA3S1S30S4S51S8bA3S1S30S4S4dS8bA3S1S30S4S4eS8bA3S1S30S4S4cS2fA1S8bA3S1S30S4S54S8bA3S1S30S4S55Sd5A1S8bA3S1S30S4S53S8bA3S30S4S52S8bA3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqbB) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqbB ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqbB ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma HtybqbB_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS15dZ0Sd5A2S15eSd5Z100A2A2S15cS15fSd5Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HxcqbB_0 : In (xc_map nx0) xcqbB. Proof. exact (In_of_cellb (xc_map nx0) xcqbB ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqbB_0 : ltac2:(tb__ "0|0|
S0S21S9S72S18S83A1S26S2S39VW;S9dA2S23S2S3fS2fA1S22S2A1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqbB_0 : ltac2:(tb__ "0|0|
S0S24S2A1S70S26S2S39VW;S9dA2S23S2S3fS2fA1S22S2A1A3A3S3cU1A1A2S3aVW;S9dS2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqbB nx0)). Qed.
Lemma NDUqbB_0 : nodupN (idxsU 1%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqbB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S6eR1S29S2S26S2S39VW;S9dA2S23S2S3fS2fA1S22S2A1A3A3A2A2Li;S3cU1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqbB_0 : ltac2:(tb__ "0|0|
S0S21S31S25S25S33S25S6dR1A1S3cU1A1A3Li;S6bU0S29S2S26S2S39VW;S9dA2S23S2S3fS2fA1S22S2A1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qbB_0 : ltac2:(tb__ "0|0|
S0S21S9S3dS83S3aVW;S9dS2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qbB_0 : ltac2:(tb__ "0|5|
S0S28S27S24S27S3S3A2M0A1M1S24S5A1M2A2M3A1S6fS72S18S83A1S3aVW;S9dS2fA3M4A2S3dS83G4A2A2S2bG3S2aG1G2S23G0S2aS3S3SaS15aA1SbP18A1A4S22G0A1A3S22S5A1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qbB_0 : ltac2:(tb__ "0|0|
S0S21S1eS6S18S83A1A1S2aS3S3S41S2fA1SbPcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqbB : wsub := Eval vm_compute in (infer_sub NF (S2F FFqbB (KUB W swcqbB nx0)) (ax_S (Lc_ok W st))).
Lemma ENT9qbB_0 : ltac2:(tb__ "0|0|
S0S21S1dS3eS83S3aVW;S9dS2fA3S2fA3S158VW;Vst;A2S117A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qbB_0 : wsub_idc sFqbB = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qbB_0 : ltac2:(tb__ "0|0|
S0S3S156S117S7aA2S41S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
End INST.
End SpineCallocSec6IW1.

(* [comment removed for export] *)
Module F0A_hbLN0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "mkHBV"; "mkHBF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbLN0"; "AM_LN0_0L"; "AM_LN0_0M"; "AU_LN0_0L"; "AU_LN0_0M"; "C5_LN0_0L"; "C5_LN0_0M"; "DUo_LN0_0L"; "DUo_LN0_0M"; "E5_LN0_0L"; "E5_LN0_0M"; "EM_LN0_0L"; "EM_LN0_0M"; "EMd_LN0_0L"; "EMd_LN0_0M"; "EMx_LN0_0L"; "EMx_LN0_0M"; "EU_LN0_0L"; "EU_LN0_0M"; "EUd_LN0_0L"; "EUd_LN0_0M"; "EUs_LN0_0L"; "EUs_LN0_0M"; "EUx_LN0_0L"; "EUx_LN0_0M"; "LA_LN0_0"; "LR_LN0_0L"; "LR_LN0_0M"; "PT_LN0_0L"; "PT_LN0_0M"; "R5_LN0_0L"; "R5_LN0_0M"; "S0_LN0_0"; "SC_LN0_0"; "SX_LN0_0L"; "SX_LN0_0M"; "T5_LN0_0L"; "T5_LN0_0M"; "T5f_LN0_0L"; "T5f_LN0_0M"; "XF_LN0_0L"; "XF_LN0_0M"; "lPA_LN0_0"; "lPB_LN0_0L"; "lPB_LN0_0M"; "lPC_LN0_0L"; "lPC_LN0_0M"; "lPD_LN0_0L"; "lPD_LN0_0M"; "lPE_LN0_0L"; "lPE_LN0_0M"; "lPL_LN0_0"; "lPT_LN0_0L"; "lPT_LN0_0M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln F0A_cLN0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_cert.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cLN0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Ltac vml := match goal with |- ?l = _ => vm_cast_no_check (@eq_refl _ l) end.
Ltac nxr := split; [vmr | vmr].

Definition E_LN0 : axst := Eval vm_compute in Erc_LN0.
Lemma FRESH_LN0 : hb_fresh E_LN0 = true. Proof. vmr. Qed.

Definition S0_LN0_0 : axst := Eval vm_compute in (S0_hb E_LN0 0).
Definition lPA_LN0_0 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_LN0_0).
Definition LA_LN0_0 : axst := Eval vm_compute in (leaf 0 lPA_LN0_0).
Definition SC_LN0_0 : axst := Eval vm_compute in (SC_hb LA_LN0_0).
Definition lPL_LN0_0 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_LN0_0).
Definition FAM_LN0_0 : hbfam := ltac2:(tb__ "0|0|
S1S21S2bS1aS22S34A5").
Lemma FAM_LN0_0_ok : hbfam_ok Erc_LN0 0 FAM_LN0_0.
Proof.
  constructor; cbn [hf_S0 hf_lPA hf_LA hf_SC hf_lPL].
  - Time vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
Qed.

Definition SX_LN0_0L : axst := Eval vm_compute in (SX_hb SC_LN0_0 0 true).
Definition lPB_LN0_0L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_LN0_0L).
Definition E5_LN0_0L : axst := Eval vm_compute in (leaf 0 lPB_LN0_0L).
Definition C5_LN0_0L : axst := Eval vm_compute in (C5_hb E5_LN0_0L).
Definition R5_LN0_0L : list sobj := Eval vm_compute in (R5_hb C5_LN0_0L).
Definition T5_LN0_0L : axst := Eval vm_compute in (T5_hb C5_LN0_0L).
Definition T5f_LN0_0L : axst := Eval vm_compute in (T5f_hb C5_LN0_0L).
Definition lPC_LN0_0L : list leafA := Eval vm_compute in (runA 900 [] T5f_LN0_0L).
Definition EUs_LN0_0L : axst := Eval vm_compute in (leaf 0 lPC_LN0_0L).
Definition EM_LN0_0L : axst := Eval vm_compute in (leaf 1 lPC_LN0_0L).
Definition EMx_LN0_0L : axst := Eval vm_compute in (selX EM_LN0_0L [O_csh vH vMS]).
Definition EMd_LN0_0L : axst := Eval vm_compute in (EMd_hb EM_LN0_0L).
Definition AM_LN0_0L : axst := Eval vm_compute in (A_after EMd_LN0_0L (SLit 0)).
Definition lPD_LN0_0L : list leafA := Eval vm_compute in (runA 900 [] AM_LN0_0L).
Definition EU_LN0_0L : axst := Eval vm_compute in (leaf 0 lPD_LN0_0L).
Definition EUx_LN0_0L : axst := Eval vm_compute in (selX EU_LN0_0L (D_U_hb true)).
Definition EUd_LN0_0L : axst := Eval vm_compute in (EUd_hb EU_LN0_0L true).
Definition DUo_LN0_0L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_LN0_0L))) (ss_objs (ax_S EUx_LN0_0L))).
Definition AU_LN0_0L : axst := Eval vm_compute in (A_after EUd_LN0_0L (SLit 0)).
Definition lPE_LN0_0L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_LN0_0L).
Definition LR_LN0_0L : axst := Eval vm_compute in (leaf 0 lPE_LN0_0L).
Definition PT_LN0_0L : axst := Eval vm_compute in (PT_hb LR_LN0_0L).
Definition lPT_LN0_0L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_LN0_0L).
Definition XF_LN0_0L : axst := Eval vm_compute in (leaf 0 lPT_LN0_0L).
Definition VAR_LN0_0L : hbvar := ltac2:(tb__ "0|0|
S0S23S2cSaS6S1fS25S27S2eS16ScS10SeS2S30S12S18S14S8S4S32S1bS1dS35S29A18").
Lemma VAR_LN0_0L_ok : hbvar_ok SC_LN0_0 0 true VAR_LN0_0L.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition SX_LN0_0M : axst := Eval vm_compute in (SX_hb SC_LN0_0 0 false).
Definition lPB_LN0_0M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_LN0_0M).
Definition E5_LN0_0M : axst := Eval vm_compute in (leaf 0 lPB_LN0_0M).
Definition C5_LN0_0M : axst := Eval vm_compute in (C5_hb E5_LN0_0M).
Definition R5_LN0_0M : list sobj := Eval vm_compute in (R5_hb C5_LN0_0M).
Definition T5_LN0_0M : axst := Eval vm_compute in (T5_hb C5_LN0_0M).
Definition T5f_LN0_0M : axst := Eval vm_compute in (T5f_hb C5_LN0_0M).
Definition lPC_LN0_0M : list leafA := Eval vm_compute in (runA 900 [] T5f_LN0_0M).
Definition EUs_LN0_0M : axst := Eval vm_compute in (leaf 0 lPC_LN0_0M).
Definition EM_LN0_0M : axst := Eval vm_compute in (leaf 1 lPC_LN0_0M).
Definition EMx_LN0_0M : axst := Eval vm_compute in (selX EM_LN0_0M [O_csh vH vMS]).
Definition EMd_LN0_0M : axst := Eval vm_compute in (EMd_hb EM_LN0_0M).
Definition AM_LN0_0M : axst := Eval vm_compute in (A_after EMd_LN0_0M (SLit 0)).
Definition lPD_LN0_0M : list leafA := Eval vm_compute in (runA 900 [] AM_LN0_0M).
Definition EU_LN0_0M : axst := Eval vm_compute in (leaf 0 lPD_LN0_0M).
Definition EUx_LN0_0M : axst := Eval vm_compute in (selX EU_LN0_0M (D_U_hb false)).
Definition EUd_LN0_0M : axst := Eval vm_compute in (EUd_hb EU_LN0_0M false).
Definition DUo_LN0_0M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_LN0_0M))) (ss_objs (ax_S EUx_LN0_0M))).
Definition AU_LN0_0M : axst := Eval vm_compute in (A_after EUd_LN0_0M (SLit 0)).
Definition lPE_LN0_0M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_LN0_0M).
Definition LR_LN0_0M : axst := Eval vm_compute in (leaf 0 lPE_LN0_0M).
Definition PT_LN0_0M : axst := Eval vm_compute in (PT_hb LR_LN0_0M).
Definition lPT_LN0_0M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_LN0_0M).
Definition XF_LN0_0M : axst := Eval vm_compute in (leaf 0 lPT_LN0_0M).
Definition VAR_LN0_0M : hbvar := ltac2:(tb__ "0|0|
S0S24S2dSbS7S20S26S28S2fS17SdS11SfS3S31S13S19S15S9S5S33S1cS1eS36S2aA18").
Lemma VAR_LN0_0M_ok : hbvar_ok SC_LN0_0 0 false VAR_LN0_0M.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.
End F0A_hbLN0.

(* [comment removed for export] *)
Module F0A_hbLN1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "mkHBV"; "mkHBF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbLN1"; "AM_LN1_0L"; "AM_LN1_0M"; "AU_LN1_0L"; "AU_LN1_0M"; "C5_LN1_0L"; "C5_LN1_0M"; "DUo_LN1_0L"; "DUo_LN1_0M"; "E5_LN1_0L"; "E5_LN1_0M"; "EM_LN1_0L"; "EM_LN1_0M"; "EMd_LN1_0L"; "EMd_LN1_0M"; "EMx_LN1_0L"; "EMx_LN1_0M"; "EU_LN1_0L"; "EU_LN1_0M"; "EUd_LN1_0L"; "EUd_LN1_0M"; "EUs_LN1_0L"; "EUs_LN1_0M"; "EUx_LN1_0L"; "EUx_LN1_0M"; "LA_LN1_0"; "LR_LN1_0L"; "LR_LN1_0M"; "PT_LN1_0L"; "PT_LN1_0M"; "R5_LN1_0L"; "R5_LN1_0M"; "S0_LN1_0"; "SC_LN1_0"; "SX_LN1_0L"; "SX_LN1_0M"; "T5_LN1_0L"; "T5_LN1_0M"; "T5f_LN1_0L"; "T5f_LN1_0M"; "XF_LN1_0L"; "XF_LN1_0M"; "lPA_LN1_0"; "lPB_LN1_0L"; "lPB_LN1_0M"; "lPC_LN1_0L"; "lPC_LN1_0M"; "lPD_LN1_0L"; "lPD_LN1_0M"; "lPE_LN1_0L"; "lPE_LN1_0M"; "lPL_LN1_0"; "lPT_LN1_0L"; "lPT_LN1_0M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln F0A_cLN1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_cert.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_cLN1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Ltac vml := match goal with |- ?l = _ => vm_cast_no_check (@eq_refl _ l) end.
Ltac nxr := split; [vmr | vmr].

Definition E_LN1 : axst := Eval vm_compute in Erc_LN1.
Lemma FRESH_LN1 : hb_fresh E_LN1 = true. Proof. vmr. Qed.

Definition S0_LN1_0 : axst := Eval vm_compute in (S0_hb E_LN1 0).
Definition lPA_LN1_0 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_LN1_0).
Definition LA_LN1_0 : axst := Eval vm_compute in (leaf 0 lPA_LN1_0).
Definition SC_LN1_0 : axst := Eval vm_compute in (SC_hb LA_LN1_0).
Definition lPL_LN1_0 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_LN1_0).
Definition FAM_LN1_0 : hbfam := ltac2:(tb__ "0|0|
S1S21S2bS1aS22S34A5").
Lemma FAM_LN1_0_ok : hbfam_ok Erc_LN1 0 FAM_LN1_0.
Proof.
  constructor; cbn [hf_S0 hf_lPA hf_LA hf_SC hf_lPL].
  - Time vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
Qed.

Definition SX_LN1_0L : axst := Eval vm_compute in (SX_hb SC_LN1_0 0 true).
Definition lPB_LN1_0L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_LN1_0L).
Definition E5_LN1_0L : axst := Eval vm_compute in (leaf 0 lPB_LN1_0L).
Definition C5_LN1_0L : axst := Eval vm_compute in (C5_hb E5_LN1_0L).
Definition R5_LN1_0L : list sobj := Eval vm_compute in (R5_hb C5_LN1_0L).
Definition T5_LN1_0L : axst := Eval vm_compute in (T5_hb C5_LN1_0L).
Definition T5f_LN1_0L : axst := Eval vm_compute in (T5f_hb C5_LN1_0L).
Definition lPC_LN1_0L : list leafA := Eval vm_compute in (runA 900 [] T5f_LN1_0L).
Definition EUs_LN1_0L : axst := Eval vm_compute in (leaf 0 lPC_LN1_0L).
Definition EM_LN1_0L : axst := Eval vm_compute in (leaf 1 lPC_LN1_0L).
Definition EMx_LN1_0L : axst := Eval vm_compute in (selX EM_LN1_0L [O_csh vH vMS]).
Definition EMd_LN1_0L : axst := Eval vm_compute in (EMd_hb EM_LN1_0L).
Definition AM_LN1_0L : axst := Eval vm_compute in (A_after EMd_LN1_0L (SLit 0)).
Definition lPD_LN1_0L : list leafA := Eval vm_compute in (runA 900 [] AM_LN1_0L).
Definition EU_LN1_0L : axst := Eval vm_compute in (leaf 0 lPD_LN1_0L).
Definition EUx_LN1_0L : axst := Eval vm_compute in (selX EU_LN1_0L (D_U_hb true)).
Definition EUd_LN1_0L : axst := Eval vm_compute in (EUd_hb EU_LN1_0L true).
Definition DUo_LN1_0L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_LN1_0L))) (ss_objs (ax_S EUx_LN1_0L))).
Definition AU_LN1_0L : axst := Eval vm_compute in (A_after EUd_LN1_0L (SLit 0)).
Definition lPE_LN1_0L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_LN1_0L).
Definition LR_LN1_0L : axst := Eval vm_compute in (leaf 0 lPE_LN1_0L).
Definition PT_LN1_0L : axst := Eval vm_compute in (PT_hb LR_LN1_0L).
Definition lPT_LN1_0L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_LN1_0L).
Definition XF_LN1_0L : axst := Eval vm_compute in (leaf 0 lPT_LN1_0L).
Definition VAR_LN1_0L : hbvar := ltac2:(tb__ "0|0|
S0S23S2cSaS6S1fS25S27S2eS16ScS10SeS2S30S12S18S14S8S4S32S1bS1dS35S29A18").
Lemma VAR_LN1_0L_ok : hbvar_ok SC_LN1_0 0 true VAR_LN1_0L.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition SX_LN1_0M : axst := Eval vm_compute in (SX_hb SC_LN1_0 0 false).
Definition lPB_LN1_0M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_LN1_0M).
Definition E5_LN1_0M : axst := Eval vm_compute in (leaf 0 lPB_LN1_0M).
Definition C5_LN1_0M : axst := Eval vm_compute in (C5_hb E5_LN1_0M).
Definition R5_LN1_0M : list sobj := Eval vm_compute in (R5_hb C5_LN1_0M).
Definition T5_LN1_0M : axst := Eval vm_compute in (T5_hb C5_LN1_0M).
Definition T5f_LN1_0M : axst := Eval vm_compute in (T5f_hb C5_LN1_0M).
Definition lPC_LN1_0M : list leafA := Eval vm_compute in (runA 900 [] T5f_LN1_0M).
Definition EUs_LN1_0M : axst := Eval vm_compute in (leaf 0 lPC_LN1_0M).
Definition EM_LN1_0M : axst := Eval vm_compute in (leaf 1 lPC_LN1_0M).
Definition EMx_LN1_0M : axst := Eval vm_compute in (selX EM_LN1_0M [O_csh vH vMS]).
Definition EMd_LN1_0M : axst := Eval vm_compute in (EMd_hb EM_LN1_0M).
Definition AM_LN1_0M : axst := Eval vm_compute in (A_after EMd_LN1_0M (SLit 0)).
Definition lPD_LN1_0M : list leafA := Eval vm_compute in (runA 900 [] AM_LN1_0M).
Definition EU_LN1_0M : axst := Eval vm_compute in (leaf 0 lPD_LN1_0M).
Definition EUx_LN1_0M : axst := Eval vm_compute in (selX EU_LN1_0M (D_U_hb false)).
Definition EUd_LN1_0M : axst := Eval vm_compute in (EUd_hb EU_LN1_0M false).
Definition DUo_LN1_0M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_LN1_0M))) (ss_objs (ax_S EUx_LN1_0M))).
Definition AU_LN1_0M : axst := Eval vm_compute in (A_after EUd_LN1_0M (SLit 0)).
Definition lPE_LN1_0M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_LN1_0M).
Definition LR_LN1_0M : axst := Eval vm_compute in (leaf 0 lPE_LN1_0M).
Definition PT_LN1_0M : axst := Eval vm_compute in (PT_hb LR_LN1_0M).
Definition lPT_LN1_0M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_LN1_0M).
Definition XF_LN1_0M : axst := Eval vm_compute in (leaf 0 lPT_LN1_0M).
Definition VAR_LN1_0M : hbvar := ltac2:(tb__ "0|0|
S0S24S2dSbS7S20S26S28S2fS17SdS11SfS3S31S13S19S15S9S5S33S1cS1eS36S2aA18").
Lemma VAR_LN1_0M_ok : hbvar_ok SC_LN1_0 0 false VAR_LN1_0M.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.
End F0A_hbLN1.

(* [comment removed for export] *)
Module F0A_hbN_tail.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Stdlib.ZArith.BinInt.Z"; "modulo"; "le"; "add"; "lt"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_tail.TailB"; "TPIN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_sh_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "hbvar_ok"; "hv_C5"; "hv_E5"; "hv_EMd"; "hv_EMx"; "hv_EUs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_env.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_hbN_step OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma mod8_of_4096 : ltac2:(tb__ "0|1|
S4S0S4SaR1Z1000A2Z0M0A3S0S4SaR2Z8A2G0A3F_;Fx;").
Proof. intros x Hx. destruct (proj1 (Z.mod_divide x 4096 ltac:(lia)) Hx) as [k ->]. replace (k * 4096) with (k * 512 * 8) by lia. apply Z.mod_mul. lia. Qed.

Section TailB.
Variables (nW : nat) (Kc : KcA) (A : AA) (rho1 : valuation) (ch : sec_chunk) (TZ : Z -> Prop).
Hypothesis HZT : ltac2:(tb__ "0|0|
S4S15Vch;R1A2VTZ;R2A1F_;Fz;").
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Let JH : jpredA := ltac2:(tb__ "0|0|
S16S6S15Vch;A1VTZ;S1dVnW;S1eS12VA;VKc;Vrho1;A6A4").
Variables (SC : axst) (f : nat) (l : bool) (cv : hbvar).
Hypothesis VOK : ltac2:(tb__ "0|0|
S17VSC;Vf;Vl;Vcv;A4").
Definition CHFh : Prop := ltac2:(tb__ "0|2|
S1S0S4SaVh;Z1000M0A2Z0M1A3S1S0S4SaVmsz;G0A2G1A3S1SbZ12000Vmsz;A2S1SbZ646000Vh;A2SdScVh;Vmsz;A2SeZ2Z2fA2A2A2A2A2A2").
Hypothesis CH : CHFh.
Definition TPIN (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1S0SfQ40M0A1M1S8Vr;PcaA2S10G0Vh;A2A3S0G1S8Vr;PcbA2S10G0Vmsz;A2A3A2").

Lemma G_c5 : ltac2:(tb__ "0|0|
S7S11SfQ40A1A1S13S14R3A1S9S6VJH;S19Vcv;A1R4R3R2A6S9S6VJH;S18Vcv;A1R5R4R3A6F_;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w (EH & EM) Hw. destruct CH as (C1 & C2 & C3 & C4 & C5).
  rewrite <- (v_C5set SC f l cv VOK).
  apply (SPA_restate segsA JH r (hv_E5 cv) (ax_S (hv_C5 cv)) tp w _ _ (v_C5swf SC f l cv VOK) (v_C5diff SC f l cv VOK) (v_C5next SC f l cv VOK)); [|constructor|exact Hw].
  constructor; [|constructor]. cbn [fst snd].
  apply (eval_A2OLD r h msz); [unfold vH; cbn [eval]; exact EH | unfold vMS; cbn [eval]; exact EM | lia | lia | lia | exact (mod8_of_4096 _ C1) | exact (mod8_of_4096 _ C2)].
Qed.

Lemma G_eus : ltac2:(tb__ "0|0|
S7S11SfQ40A1A1S13S14R3A1S9S6VJH;S1cVcv;A1R4R3R2A6S2F_;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w (EH & EM) Hw. destruct CH as (CH1 & CH2 & CH3 & CH4 & CH5).
  pose proof (SPA_facts_hold segsA _ r (hv_EUs cv) tp w Hw) as HFa.
  pose proof (v_EUsfact SC f l cv VOK) as X0. apply existsb_exists in X0 as (g & Hg & Eg). apply sprop_eqb_sound in Eg. subst g.
  pose proof (proj1 (Forall_forall _ _) HFa _ Hg) as HB. cbn [holds branch_taken] in HB. apply negb_true_iff in HB. unfold bv_ltu in HB. apply Z.ltb_ge in HB.
  rewrite (eval_EBEG r h ltac:(unfold vH; cbn [eval]; exact EH) ltac:(lia)), (eval_EEND r h msz ltac:(unfold vH; cbn [eval]; exact EH) ltac:(unfold vMS; cbn [eval]; exact EM) ltac:(lia) ltac:(lia) ltac:(lia)) in HB.
  destruct (mrange_facts h msz ltac:(lia) CH1 CH2 CH3) as (M1 & M2 & M3 & M4 & M5).
  assert (SHB : 0 <= Sh h /\ Sh (h + msz) < 2 ^ 63).
  { unfold Sh, SHADOW_OFF. pose proof (Z.div_pos h 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (h + msz) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  rewrite !u64_lit in HB by lia. lia.
Qed.

Lemma G_shd : ltac2:(tb__ "0|1|
S7S11SfQ40A1M0A1S13S14R3A1S9S6VJH;S1bVcv;A1R4R3R2A6S3S7S7S1S9S6VJH;S1aVcv;A1R1R5R4A6S5S0G0S8R2R1A2S8R7R1A2A3Fv;A2Lr2;A2F_;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp [tr [ms md]] (EH & EM) H. destruct CH as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_pos msz 8 ltac:(lia) ltac:(lia)) as MD0. pose proof (Z.div_lt_upper_bound msz 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as MD1.
  pose proof (Sh_in_band h ltac:(lia)) as SB1. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in SB1.
  assert (SHE : Sh (h + msz) = Sh h + msz / 8) by (apply Sh_add8; [exact (mod8_of_4096 _ C1) | exact (mod8_of_4096 _ C2)]).
  assert (RG : obj_range r (O_csh vH vMS) = (Sh h, Sh h + msz / 8)).
  { unfold O_csh, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
    rewrite (eval_BSHS r vH h ltac:(unfold vH; cbn [eval]; exact EH) ltac:(lia)), (soff_LENS r vMS msz ltac:(unfold vMS; cbn [eval]; exact EM) ltac:(lia)).
    rewrite soff_lit_small by lia. rewrite u64_lit by lia. f_equal. lia. }
  destruct (dissolveZW (chunk_sh_zone ch) TZ (JF nW UStopLe false A Kc rho1) HZT (hv_EMx cv) (ss_objs (ax_S (hv_EMd cv))) [O_csh vH vMS] r tp tr ms md (v_EMxobjs SC f l cv VOK) H) as (H2 & RW & RL).
  - intros x (o & Ho & Hz). destruct Ho as [<-|[]]. rewrite RG in Hz. cbn [fst snd] in Hz. unfold chunk_sh_zone. fold h msz. rewrite SHE. exact Hz.
  - constructor; [left; reflexivity | constructor].
  - rewrite (v_EMdset SC f l cv VOK) in H2. eexists. split; [exact H2 | exact RW].
Qed.
End TailB.
End F0A_hbN_tail.

(* [comment removed for export] *)
Module F0A_hbN_entry.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "list"; "nil"; "bool"; "true"; "Some"; "app"; "false"; "length"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "rw"; "valuation"; "sprop"; "SLit"; "holds"; "sobj"; "ss_objs"; "sprop_below"; "sprop_eqb"; "ss_facts"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "div"; "of_nat"; "opp"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "SEC_INST"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_spacebeg"; "sc_map_beg"; "sc_map_size"; "sec_chunk"; "aa_sec"; "ag_ctx"; "ag_thread"; "ag_pab"; "sc_size"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states"; "XO_hb"; "F1_hb"; "vRISh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "Wcan"; "UStopLe"; "chain_pre"; "free_depth"; "top_high"; "F_depth"; "V_DEPTH"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_sh_zone"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind"; "blind_rel"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_entry.Entry"; "zbH"; "ZUH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_entry"; "N_hb"; "ZUH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env"; "hbenv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones"; "zd_allb"; "zds_of"; "zenv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "LOW_SHADOW_BEG"; "kSpaceSize"; "round_up"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue"; "fam_ok"; "zloS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop"; "zhiX"; "zbX"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib"; "mkST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states"; "vNCH"; "vPAB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_env.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_hbN_step OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N_hb : list carve_spec := ltac2:(tb__ "0|f|
S1S3S3S3S14SdA2M0SdA2M1S4S3S3SdS2A2M2S14A2M3A1M4A2M5S0G1G4S0G0SdS0S14SdS18Z0A1M6Zeddc0M7A4Zeddc4A4S1G3S0G2S14S0SdS2G7U4M8A4S18ZffffffffA1A4S5G3A1M9A3A4S1G5S0G1G4S0G0SdS0S14SdG6Zeddc8MaA4Zeddd1A4S1G3S0G2S14S0SdS2GaU8MbA4S39A4S1G3S0G2S14S0SdS2Zeddd0U1A4G6A4G9A3A3A4S1G5S0G1G4S0G0SdS0S14SdG6S29A4S1fS29Z10A2A4S1G3S0G2S14S0SdS2S29GbA4S18S51A1A4S1G3S0G2S14S0SdS2S1fS29Z8A2GbA4S68A4G9A3A3A4S1G5S0G1G4S0G0SdS0S14SdG6S1fS29Z38A2McA4S1fS29Z40A2MdA4S1G3S0G2S14S0SdS2GcGbA4S67A4G9A3A4S1G5S0G1G4S0G0SdS0S14SdG6GdA4Zee040MeA4G9A4S1G5S0G1G4S0G0SdS0S14SdG6GeA4Zee044A4S1G3S0G2S14S0SdS2GeG8A4G6A4G9A3A4S1G5S0G1G4S0G0SdS0S14SdG6Zee048A4Zee070A4G9A4S5G5A1A3A3A3A3A3A3A3").
Lemma N_hb_objs : ltac2:(tb__ "0|0|
SfS4S1aA1S44S63S1aS62S4aA4S37A3"). Proof. reflexivity. Qed.

Section Entry.
Variables (A : AA) (it : Z * Z) (i : nat) (ch : sec_chunk) (rho : valuation).
Hypothesis QS : ltac2:(tb__ "0|0|
S4cVA;Vit;Vi;Vch;Vrho;A5").

Lemma carve_hb : Forall (carve_okq rho) N_hb.
Proof.
  pose proof QS as [HG HSEP3 HRTC HRIG HSR HI HU HSZ HSEP HIM HSTAT HN HV].
  pose proof (qs_nums A it i ch rho QS) as (T0 & T1 & C0 & C1' & TG & TI & CI & _).
  destruct HRIG as (E151 & E152 & E155 & E195). destruct HV as (E12 & E200 & E201 & _).
  assert (HR : cells_ok (view segsA (rm rho)) (rtc_cells RTC_A (aa_geom A))) by exact HRTC.
  destruct HSR as (_ & _ & _ & _ & _ & S0c & S8 & _ & _ & _ & S56 & _ & SM & _).
  unfold N_hb. repeat apply Forall_cons; try apply Forall_nil; unfold carve_okq; lazy beta iota zeta.
  all: cbn [eval]; rewrite ?u64_lit by lia.
  all: unfold SEC_INST, PG, IMG_HI in *.
  all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
  all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
  all: split.
  all: try match goal with
       | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
       end.
  all: try (unfold cells_in_view; apply Forall_nil).
  - unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; civ_any2 HR.
  - unfold cells_in_view, vRISh; repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E195; civ_any2 HR.
  - unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
    + intros j Hj. apply (civ_cell rho (rm rho) 0 974296 8 4096 (SLit 4096)); [exact S0c | cbn [eval]; reflexivity | lia | lia | exact Hj].
    + intros j Hj. apply (civ_cell rho (rm rho) 0 974304 8 (ag_pab (aa_geom A)) vPAB); [exact S8 | unfold vPAB; cbn [eval]; exact E200 | lia | lia | exact Hj].
  - unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
    intros j Hj. apply (civ_cell rho (rm rho) 0 974352 8 (Z.of_nat (length (aa_sec A))) vNCH); [exact S56 | unfold vNCH; cbn [eval]; exact E201 | lia | lia | exact Hj].
  - unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
    intros j Hj. apply (civ_cell rho (rm rho) 0 974912 4 0 (SLit 0)); [exact SM | cbn [eval]; reflexivity | lia | lia | exact Hj].
Qed.

Lemma facts_hb : ltac2:(tb__ "0|0|
S2S55R1S2cS2bVA;A1A1S2dVch;A1S2eVch;A1A4S43S17S19Vrho;A1S38R2A1A3F_;Ff;").
Proof.
  intros f HFAM. pose proof QS as [HG HSEP3 HRTC HRIG HSR HI HU HSZ HSEP HIM HSTAT HN HV].
  pose proof (qs_nums A it i ch rho QS) as (T0 & T1 & C0 & C1' & TG & _). pose proof (qs_chunk A it i ch rho QS) as (_ & _ & MS & IH & HTG & _).
  pose proof (hb_E A it i ch rho QS) as (_ & _ & EmT & RmT).
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  destruct HRIG as (E151 & E152 & E155 & E195). destruct HV as (E12 & E200 & E201 & _).
  assert (NCpos : 1 <= Z.of_nat (length (aa_sec A)) <= 2 ^ 20).
  { pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LT.
    destruct HSR as (_ & _ & (B1 & B2) & _). unfold kPtrArrayReserve in B2. lia. }
  unfold F1_hb. apply Forall_app. split.
  - unfold Fm_hb. destruct f as [|[|f]]; cbn [fam_ok] in HFAM; repeat apply Forall_cons; try apply Forall_nil; unfold IMG_HI, PG in *.
    + apply (hlt rho mT vSB (fst it - 16) (ag_spacebeg (aa_geom A))); [exact EmT | exact E155 | lia | lia | lia].
    + apply (hlt rho mT vSB (fst it - 16) (ag_spacebeg (aa_geom A))); [exact EmT | exact E155 | lia | lia | lia].
    + apply (hle rho (SAlu ALU_ADD vSB (SLit (2 ^ 37))) mT (ag_spacebeg (aa_geom A) + 2 ^ 37) (fst it - 16)); [apply (ev_add_lit rho vSB); [exact E155 | lia | lia | lia] | exact EmT | lia | lia | lia].
  - unfold HIGH_SHADOW_END, TOPMAX, IMG_HI, PG in *. repeat apply Forall_cons; try apply Forall_nil.
    + apply (hle rho _ vSB 0x10007fff8000 (ag_spacebeg (aa_geom A))); [apply elit | exact E155 | lia | lia | lia].
    + apply (hle rho vSB _ (ag_spacebeg (aa_geom A)) (140737479966720 - 2 ^ 37 - 4096)); [exact E155 | apply elit | lia | lia | lia].
    + apply (hne0 rho vNCH (Z.of_nat (length (aa_sec A)))); [exact E201 | lia].
    + apply (hle rho vNCH _ (Z.of_nat (length (aa_sec A))) (2 ^ 20)); [exact E201 | apply elit | lia | lia | lia].
Qed.

Definition zbH : nat -> Z := ltac2:(tb__ "0|2|
S58S32S2bVA;A1M0A1S31G0A1S35G0A1S2dVch;A1S52Z0M1G1G1G1A9").
Definition ZUH : list nat := ltac2:(tb__ "0|0|
S1S2U0S1S2U1S1S2U2S1S2U3S1S2U4S1S2U5S5S2A1A3A3A3A3A3A3").
Lemma zsepH : ltac2:(tb__ "0|4|
S2S2S59S2R2S49A3M0G0S12SfS2R4R3A3A1S13S20S1fS48R5A1M1S57S2eVch;A1M2R5A2A2S1fS48R4A1M3S56R4A1A2A2S20S1fG3S57G2R4A2A2S1fG1S56R5A1A2A2A2F_;F_;F_;Fz';Fz;").
Proof.
  pose proof QS as [HG HSEP3 HRTC HRIG HSR HI HU HSZ HSEP HIM HSTAT HN HV].
  pose proof (qs_nums A it i ch rho QS) as (T0 & T1 & C0 & C1' & TG & TI & CI & TC). pose proof (qs_chunk A it i ch rho QS) as (_ & _ & MS & IH & HT & HB & _).
  destruct HSEP as (_ & HT' & _ & HC' & _).
  destruct HG as (_ & _ & TD & CD & _). destruct TD as (_ & _ & _ & _ & _ & TB). destruct CD as (_ & _ & _ & _ & CB).
  intros z z' Hz Hz' NE. unfold ZUH in Hz, Hz'. cbn [In] in Hz, Hz'.
  unfold zbH, zbX, zloS, zhiX, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  repeat (destruct Hz as [<-|Hz]); try (exfalso; exact Hz); repeat (destruct Hz' as [<-|Hz']); try (exfalso; exact Hz'); try (exfalso; apply NE; reflexivity); cbn [Nat.eqb]; lia.
Qed.
End Entry.

Section EntryGlue.
Variables (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HUS : ltac2:(tb__ "0|0|
S69S3aVnW;A1S3bA2").
Variables (A : AA) (rho1 : valuation) (p n : Z) (i : nat) (ch : sec_chunk) (f : nat) (TZ : Z -> Prop).
Hypothesis HI : ltac2:(tb__ "0|0|
SfScS2fA1S5cS2fS30VA;A1Vi;A3S8S2fVch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
SfSdVp;S1fS1fS2dVch;A1S51A2Z800A2A3").
Hypothesis HSZ : ltac2:(tb__ "0|0|
SfSdS34Vch;A1S1fS54Vn;Z8A2Z1000A2A3").
Hypothesis HN : 1 <= n.
Hypothesis HNB : ltac2:(tb__ "0|0|
S20S1fZ1800S50Vn;A1A2S2eVch;A1A2").
Hypothesis HFAM : ltac2:(tb__ "0|0|
S55Vf;S2cS2bVA;A1A1S2dVch;A1S2eVch;A1A4").

Hypothesis HPIN : ltac2:(tb__ "0|4|
S10SfS25Q40M0A1M1S15Vrho1;P97A2S24G0S32S2bVA;A1M2A1A2A3S10SfG1S15Vrho1;P98A2S24G0S31G2A1A2A3S10SfG1S15Vrho1;P9bA2S24G0S2cG2A1A2A3S10SfG1S15Vrho1;PcA2S24G0Vp;A2A3S10SfG1S15Vrho1;P69A2S24G0S50Vn;A1M3A2A3SfG1S15Vrho1;P6aA2S24G0S21G3Z8A2A2A3A2A2A2A2A2").
Let JH : jpredA := ltac2:(tb__ "0|0|
S47S27S42Vch;A1VTZ;S61VnW;S3bSaVA;VKc;Vrho1;A6A4").
Variables (E S0 : axst).
Definition T_entry : strans := ltac2:(tb__ "0|1|
S66VE;U0S4aS1SePc8S1SePc9S1SePc3S5SeA1A3A3A3M0S38Vf;A1VS0;S65G0A1S4eVnW;S1bS36VE;A1A1A2S4eVnW;S37A2A9").
Hypothesis TOK : s_ok T_entry = true.
Hypothesis ZOK : ltac2:(tb__ "0|0|
S10SfS6S4dVnW;S4bS1bS36VE;A1A1A3S7A3SfS6S4dVnW;S4bS37A3S7A3A2").
Hypothesis FCH : ltac2:(tb__ "0|1|
S10SfS6S5aS17S17S5bS17S1dR1A1S1eS36VE;A1A1A3Lg;S9S17S3cS3aVnW;A1A1S3fS3dA1A3M0A3S7A3SfS6S5aS17S1cS64A1G0A3S7A3A2").

Lemma JH_parts : ltac2:(tb__ "0|1|
S16S4S25Q40A1M0A1S4S5fA1S5eVJH;R4R3R2R1A4S11S16S16S10S2aS27VA;R1R5R3A5S10VKc;R4R3A2S10S41VA;R1A2S10S3eVA;R1A2S10S46S27S42Vch;A1VTZ;R1R6A5SeS5dR1S28A2SfG0S15R8R2A2S15Vrho1;R2A2A3F_;Fv;A2A2A2A2A2Lrp;A2F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md (rp & (Hag & HA & _ & _ & HK & Htp & _ & Htop) & BR). exists rp.
  split; [exact HA|]. split; [exact HK|]. split; [exact Htp|]. split; [exact Htop|]. split; [exact BR|].
  intros v Hv. rewrite (proj1 BR v). symmetry. exact (proj1 Hag v Hv).
Qed.

Lemma zenv_of : ltac2:(tb__ "0|1|
S16S16S4cVA;S0SdSdVp;Vn;A4Vi;Vch;R1A5S3eVA;R3A2S46S27S42Vch;A1VTZ;R4R3A5SeS5dR1S28A2SfS25Q40M0A1S15R6R2A2S15Vrho1;R2A2A3F_;Fv;S20S26G0S15R5S40A2A2S23S3dA1A2S43S17S19R6A1S3cS3aVnW;A1A1A3S4fVnW;VA;Vp;Vn;Vch;R7A6F_;F_;F_;F_;F_;F_;Fr4;Frp;").
Proof.
  intros rp r4 QS4 Htop BR RW4 HD HC. destruct HPIN as (P151 & P152 & P155 & P12 & P105 & P106).
  pose proof (qs_nums A (p, n) i ch r4 QS4) as (T0 & T1 & C0 & C1' & TG & _). pose proof (qs_chunk A (p, n) i ch r4 QS4) as (CM & _ & MS & IH & HT & _).
  pose proof (N8_facts n HN) as (N1 & N2 & N3 & N4). unfold PG, IMG_HI in *.
  constructor; try (rewrite RW4 by (unfold GW; lia); assumption).
  - unfold top_high in *. unfold V_DEPTH in *. rewrite !(proj1 BR). exact Htop.
  - exact HD.
  - exact HC.
  - lia.
  - repeat split; try assumption; lia.
Qed.

Lemma G_entry : ltac2:(tb__ "0|4|
S16S4S25Q40M0A1M1A1S60S45S27VJH;VE;R3R2R1A6S11S16S16S10S45S27VJH;VS0;R1R4R3A6SeG1S59S3SeG1A2M2S0SeG1R2R1A4S1G2S0SeG1Pc8S24G0S33S2bVA;A1M3A1A2A4S1G2S0SeG1Pc9S24G0S22SbS2fS30VA;A1A2A1A2A4S1G2S0SeG1Pc3S24G0S1fS2cG3A1S53A2A2A4S5G2A1A3A3A3A3SfG1S15R4R3A2R2A3F_;Fx;Fv;A2Lr2;A2F_;Fw;Ftp;FrhoE;").
Proof.
  intros rhoE tp [tr [ms md]] H.
  pose proof (JF_stable nW UStopLe false A Kc rho1 HUS HKc) as HST. change GW with NPRE in HST.
  set (bs := [(200%positive, Z_to_bv 64 (ag_pab (aa_geom A))); (201%positive, Z_to_bv 64 (Z.of_nat (length (aa_sec A)))); (195%positive, Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize))]).
  set (vals := map snd bs).
  pose proof (SPA_facts_hold segsA _ rhoE E tp _ H) as HFa.
  assert (FIN : forall g, In g (chain_pre (Wcan nW) ++ F_depth free_depth) -> holds rhoE g).
  { intros g Hg. pose proof (proj1 (forallb_forall _ _) (proj1 FCH) g Hg) as X. apply existsb_exists in X as (g' & Hg' & Eg). apply sprop_eqb_sound in Eg. subst g'.
    exact (proj1 (Forall_forall _ _) HFa g Hg'). }

  assert (ENVAT : forall r4, (forall v, (v < NPRE)%positive -> rw r4 v = rw rhoE v) -> (forall l, rl r4 l = rl rhoE l) -> (forall v x, In (v, x) bs -> rw r4 v = x) ->
            JH r4 tp tr md -> hbenv A (p, n) i ch r4 /\ zenv nW A p n ch r4).
  { intros r4 RWE RLE RB HJ4. destruct (JH_parts r4 tp tr md HJ4) as (rp & HA & HK & Htp & Htop & BR & RW4).
    destruct HPIN as (P151 & P152 & P155 & P12 & P105 & P106).
    assert (RP : forall v, (v < GW)%positive -> rw rp v = rw rho1 v) by (intros v Hv; rewrite <- (proj1 BR v); exact (RW4 v Hv)).
    pose proof (hbenv_intro Kc HKc A p n i ch HI HU HSZ HN TZ rp r4 tp tr md HA HK Htp Htop
                  ltac:(rewrite RP by (unfold GW; lia); exact P151) ltac:(rewrite RP by (unfold GW; lia); exact P152) ltac:(rewrite RP by (unfold GW; lia); exact P155)
                  BR ltac:(rewrite RW4 by (unfold GW; lia); exact P12) (RB _ _ (or_introl eq_refl)) (RB _ _ (or_intror (or_introl eq_refl))) (RB _ _ (or_intror (or_intror (or_introl eq_refl))))) as QS4.
    split; [exact QS4|].
    assert (AV : agree_vals NPRE rhoE r4) by (split; [intros v Hv; symmetry; exact (RWE v Hv) | intros l; symmetry; exact (RLE l)]).
    assert (F4 : forall g, In g (chain_pre (Wcan nW) ++ F_depth free_depth) -> holds r4 g).
    { intros g Hg. apply (proj1 (holds_agree_vals NPRE rhoE r4 g AV (proj1 (forallb_forall _ _) (proj2 FCH) g Hg))). exact (FIN g Hg). }
    apply (zenv_of rp r4 QS4 Htop BR RW4).
    - assert (D1 : holds r4 (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))) by (apply F4; apply in_or_app; right; left; reflexivity).
      cbn [holds eval branch_taken] in D1. unfold bv_lts in D1. apply negb_true_iff in D1. apply Z.ltb_ge in D1.
      change (bv_signed (Z_to_bv 64 (- free_depth))) with (- free_depth) in D1. exact D1.
    - apply Forall_forall. intros g Hg. apply F4. apply in_or_app. left. exact Hg. }
  set (rhoB := rho_sets rhoE bs).
  assert (HJB : JH rhoB tp tr md).
  { apply (JW_stable segsA NPRE (chunk_sh_zone ch) TZ _ HST rhoE rhoB tp tr md md); [|apply mat_equiv_refl | exact (proj2 H)].
    unfold rhoB. apply agree_below_rho_sets. intros v x Hin. cbn in Hin. unfold NPRE. repeat (destruct Hin as [Ein|Hin]; [injection Ein as <- _; lia|]). destruct Hin. }
  assert (NDB : List.NoDup (map fst bs)) by (cbn; repeat constructor; cbn; intuition discriminate).
  destruct (ENVAT rhoB) as (QSB & _); [| | | exact HJB |].
  { intros v Hv. unfold rhoB. rewrite rho_sets_other; [reflexivity|]. cbn. unfold NPRE in Hv. intros [<-|[<-|[<-|[]]]]; lia. }
  { intros l. unfold rhoB. rewrite rl_rho_sets. reflexivity. }
  { intros v x Hin. unfold rhoB. exact (rho_sets_get bs rhoE v x NDB Hin). }
  destruct (s_stepW (chunk_sh_zone ch) TZ (JF nW UStopLe false A Kc rho1) HST (zbH A ch) zloS (zhiX (sc_map_size ch)) ZUH (zsepH A (p, n) i ch rhoB QSB) T_entry [] vals rhoE tp tr ms md TOK
              (keepN0 E) eq_refl H (Forall_nil _)) as (rho5 & H5 & V5 & RM5 & AG5 & EV).
  { intros EV3 HJ4. set (rho3 := rho_absorb rhoE (map dobj []) (vms md tp ms)) in *. set (rho4 := rho_sets rho3 (combine (s_bs T_entry) vals)) in *.
    assert (EC : combine (s_bs T_entry) vals = bs) by reflexivity.
    destruct (ENVAT rho4) as (QS4 & ZE4); [| | | exact HJ4 |].
    { intros v Hv. unfold rho4. rewrite EC, rho_sets_other; [reflexivity|]. cbn. unfold NPRE in Hv. intros [<-|[<-|[<-|[]]]]; lia. }
    { intros l. unfold rho4. rewrite rl_rho_sets. reflexivity. }
    { intros v x Hin. unfold rho4. rewrite EC. exact (rho_sets_get bs rho3 v x NDB Hin). }
    assert (ZS : forall objs, zd_allb nW ZUH objs = true -> Forall2 (in_zoneW rho4 (zbH A ch) zloS (zhiX (sc_map_size ch)) ZUH) objs (zds_of nW objs)).
    { intros objs HB. apply (zds_sound nW A p n ch rho4 (zbH A ch) zloS (zhiX (sc_map_size ch)) ZUH); try (repeat split; reflexivity); [exact ZE4 | exact HB]. }
    assert (EO : ss_objs (ax_S (s_Cd T_entry)) = ss_objs (ax_S E)).
    { unfold s_Cd, dropN, keepN. cbn [s_C s_k T_entry]. destruct E as [SE XE BE]. cbn [ax_setS ax_S set_objs ss_objs]. rewrite Nat.sub_0_r. apply firstn_all. }
    split; [exact (carve_hb A (p, n) i ch rho4 QS4)|]. split; [exact (ZS _ (proj2 ZOK))|]. split; [rewrite EO; exact (ZS _ (proj1 ZOK))|].
    intros _. exact (facts_hb A (p, n) i ch rho4 QS4 f HFAM). }
  exists rho5. split; [exact H5|]. intros v x Hin. set (rho4 := rho_sets (rho_absorb rhoE (map dobj []) (vms md tp ms)) (combine (s_bs T_entry) vals)) in *.
  rewrite (V5 v (SVar v)); [cbn [eval]; exact (rho_sets_get bs _ v x NDB Hin)|].
  cbn in Hin. destruct Hin as [Ein|[Ein|[Ein|[]]]]; injection Ein as <- _; cbn; tauto.
Qed.
End EntryGlue.
End F0A_hbN_entry.

(* [comment removed for export] *)
Module F0A_hbN_unmap.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "mul"; "pow"; "sub"; "modulo"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "aa_sec"; "sc_map_beg"; "aa_geom"; "ag_pab"; "aa_live"; "ag_ctx"; "ag_spacebeg"; "ag_thread"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "sv"; "valuation"; "rw"; "eval"; "sobj"; "obj_range"; "ranges_disjoint"; "rl"; "reg_sv"; "ss_objs"; "@Corelib.Init.Datatypes"; "bool"; "length"; "list"; "false"; "option"; "true"; "pair"; "Some"; "prod"; "app"; "cons"; "nat"; "None"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "cell_ok"; "mkACell"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "vm_maps"; "map_remove"; "region_free"; "TASK_SIZE"; "map_has"; "page_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayReserve"; "PG"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@Stdlib.Lists.List"; "nth_error"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap.Node"; "JH2"; "JPh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "SEC_INST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_zone"; "chunk_sh_zone"; "sec_junk_zone"; "sec_tbl_zone"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "shadow_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind"; "blind_rel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap"; "DUZh"; "JH2"; "JPh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.InvQ11"; "freeBigA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_gpr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "MI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap.Unmap"; "DUZh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "top_high"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states"; "vH"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import PaidMunmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SysCallA MmapA MmapFixedA MmapNodesA MunmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PaidMunmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_env.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PaidMunmap OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.InvQ11.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Unmap.
Variables (A : AA) (l1 l2 : list (Z * Z)) (p n : Z) (i : nat) (ch lst : sec_chunk) (l : bool).
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Hypothesis HLV : ltac2:(tb__ "0|1|
S0S26S2cSeSeA2M0A1S15VA;A1S2dG0Vl1;S2eG0S2aSeSeVp;Vn;A4Vl2;A3A3A3").
Hypothesis HPR : is_primary n = false.
Hypothesis HI : ltac2:(tb__ "0|0|
S0S28S10A1S4dS10S11VA;A1Vi;A3S2bS10Vch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
S0SeVp;S6S6S12Vch;A1S4aA2Z800A2A3").
Hypothesis Hl : ltac2:(tb__ "0|1|
S0S28S10A1S4dS10S11VA;A1M0S39S25S10G0A2U1A2A3S2bS10Vlst;A2A3").
Hypothesis HLT : ltac2:(tb__ "0|0|
S0S24Vl;S29A3S0S2fVi;S39S25S10S11VA;A1A2U1A2A3F_;").
Hypothesis HLF : ltac2:(tb__ "0|0|
S0S24Vl;S27A3S57Vi;S39S25S10S11VA;A1A2U1A2A2F_;").

Hypothesis CH : ltac2:(tb__ "0|1|
S1S7Z646000Vh;A2S1S8Z0Vmsz;A2S1S8S6Vh;Vmsz;A2M0SbZ2Z2fA2A2S2S7G0S4cA2S7S4bVh;A2A2A2A2A2").
Hypothesis LSTOFF : ltac2:(tb__ "0|1|
S0S24Vl;S27A3S2S7S6S12Vlst;A1M0Z20A2Vh;A2S7S6Vh;Vmsz;A2G0A2A2F_;").
Hypothesis PABOFF : ltac2:(tb__ "0|1|
S2S7S6S14S13VA;A1A1M0S49A2Vh;A2S7S6Vh;Vmsz;A2G0A2A2").
Hypothesis NCB : ltac2:(tb__ "0|0|
S7SaZ8S9S25S10S11VA;A1A2A1A2S49A2").
Definition DUZh (z : Z) : Prop := ltac2:(tb__ "0|0|
S2S53Vch;Vz;A2S2S54Vch;Vz;A2S2S55Vz;A1S56VA;Vi;Vz;A3A2A2A2").

Lemma unmap_inv : ltac2:(tb__ "0|a|
SeOF_;S1bS1bS26S36Q40M0A1A1S3aS51S5VA;R4R2R1A5S60S5S6cR6R5R4A5S34S33S5S19R5A1A2S35S6S52Z38A2U8M1ScS9S25S10S11VA;A1A2A1Z1A2A3A2S34S33S5S19R6A1A2S35Zee040U4Z0A3A2S0S24Vl;S27A3S1S34S33S5S19R8A1A2M2S35S6S14S13VA;A1A1SaZ8M3S9Vi;A1M4A2A2M5G1S12Vlst;A1M6A3A2S34G2S35S6G6Z18A2G1G4A3A2A2F_;S0S24Vl;S29A3SeS1S7G5R1A2S8R1S6G5G3A2A2A2S0S28S36Q8A1A1S33S5S19RbA1M7R2A3S33S5S19RcA1R2A3A3F_;Fz;F_;S6aS5R7R8A3S0S24S3fS3eS3dS3cR8A1A1S38G0Vh;A2M8A2G8S38G0Vmsz;A2M9A3S29A3S51S5S64VA;Vl1;Vl2;Vi;A4S5aRbS59G7G8G9A3A2S5bVh;S6Vh;Vmsz;A2RaA3S58R9G8G9A3A5F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Ftp;Fr;Frp;FTZ;").
Proof.
  intros TZ rp r tp md HA (BW & BL & BOUT & BIN & _) C1 C2 C3 C4 HMI MU3.
  destruct CH as (CH4 & CH3 & CH5 & CH6).
  set (aw := Z_to_bv 64 h). set (nw := Z_to_bv 64 msz). set (r4 := set_rm r (unmap_range (rm r) aw nw)).
  set (v := view segsA (rm rp)). set (v2 := view segsA (rm r)). set (v4 := view segsA (rm r4)).
  assert (INR : forall x : word, SysStep.in_range aw nw x = true <-> chunk_zone ch (bv_unsigned x)).
  { intros x. rewrite SysStep.in_range_spec. unfold aw, nw, chunk_zone. fold h msz. rewrite !u64_lit by lia. tauto. }
  assert (V4OUT : forall z, ~ chunk_zone ch z -> v4 z = v2 z).
  { intros z NZ. unfold v4, v2. apply view_agree. intros Hz. unfold r4. cbn [rm set_rm]. rewrite unmap_range_at.
    destruct (SysStep.in_range aw nw (Z_to_bv 64 z)) eqn:EI; [|reflexivity]. exfalso. apply NZ. pose proof (proj1 (INR _) EI) as X0. rewrite u64_lit in X0 by lia. exact X0. }
  assert (CELL4 : forall c, cell_ok v2 c -> (forall z, c_addr c <= z < c_addr c + Z.of_nat (c_w c) -> ~ chunk_zone ch z) -> cell_ok v4 c).
  { intros [ca cw cv] Hc Hz. apply (cell_ok_frame1 v2 v4 ca cw cv); [|exact Hc]. intros z Hzz. apply V4OUT. apply Hz. cbn [c_addr c_w]. exact Hzz. }
  assert (JOFF : forall z, sec_junk_zone z \/ chunk_sh_zone ch z -> ~ chunk_zone ch z).
  { intros z [HZ|HZ] HC; unfold chunk_zone in HC; fold h msz in HC.
    - unfold sec_junk_zone, SEC_INST in HZ. lia.
    - unfold chunk_sh_zone in HZ. fold h msz in HZ. pose proof (Z.div_pos h 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (h + msz) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
      unfold Sh, SHADOW_OFF, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia. }
  unfold kPtrArrayReserve in *.
  pose proof (AInvA_unmap_live A rp r4 tp md l1 l2 p n i ch HA HLV HPR HI HU) as LAW. cbv zeta in LAW. fold h msz in LAW. apply LAW; clear LAW.
  - intros i0. exact (BW i0).
  - intros l0. exact (BL l0).
  - intros z N2' N3' N4' N5'. transitivity (v2 z); [exact (V4OUT z N4') | apply BOUT; unfold DUZh; tauto].
  - intros z HZ Hd. change (v4 z <> None). rewrite (V4OUT z (JOFF z HZ)). apply BIN; [unfold DUZh; tauto | exact Hd].
  - apply (CELL4 _ C1). intros z Hz. cbn [c_addr c_w] in Hz. unfold chunk_zone, SEC_INST in *. fold h msz. lia.
  - apply (CELL4 _ C2). intros z Hz. cbn [c_addr c_w] in Hz. unfold chunk_zone. fold h msz. lia.
  - intros lst0 Hl0. rewrite Hl in Hl0. injection Hl0 as <-. split.
    + intros Hlt. destruct l; [pose proof (HLT eq_refl) as EI; exfalso; pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)); lia|]. destruct (C3 eq_refl) as [C3a C3b]. split.
      * apply (CELL4 _ C3a). intros z Hz. cbn [c_addr c_w] in Hz. unfold chunk_zone. fold h msz. pose proof (HLF eq_refl). lia.
      * apply (CELL4 _ C3b). intros z Hz. cbn [c_addr c_w] in Hz. unfold chunk_zone. fold h msz. pose proof (LSTOFF eq_refl). lia.
    + intros Heq z Hz. destruct l; [|pose proof (HLF eq_refl); exfalso; lia]. transitivity (v2 z); [apply V4OUT; unfold chunk_zone; fold h msz; pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)); lia | exact (C4 eq_refl z Hz)].
  - exact (paid_munmap_leZ segsA md tp h msz ltac:(lia) ltac:(lia) HMI MU3).
Qed.
End Unmap.

Section Node.
Variables (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Variables (A : AA) (rho1 : valuation) (l1 l2 : list (Z * Z)) (p n : Z) (i : nat) (ch lst : sec_chunk) (l : bool) (TZ : Z -> Prop).
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Let A2 : AA := ltac2:(tb__ "0|0|
S64VA;Vl1;Vl2;Vi;A4").
Let JF0 : jpredA := ltac2:(tb__ "0|0|
S6dVnW;S6eS27VA;VKc;Vrho1;A6").

Definition JPh : jpredA := ltac2:(tb__ "0|7|
S1bS26S36Q40A1A1S26S3bA1S3aS4S1bS1bS1VJF0;R1R4R3R2A4S1S60S5S61VA;Vi;Vch;A3VTZ;R1R5A5S1S34S33S5S19R5A1A2M0S35S6S52Z38A2U8M1ScS9S25S10S11VA;A1A2A1Z1A2A3A2S1S34G0S35Zee040U4Z0A3A2S1S0S24Vl;S27A3S1S34S33S5S19R6A1A2M2S35S6S14S13VA;A1A1SaZ8M3S9Vi;A1M4A2A2M5G1S12Vlst;A1M6A3A2S34G2S35S6G6Z18A2G1G4A3A2A2F_;S0S24Vl;S29A3SeS1S7G5R1A2S8R1S6G5G3A2A2A2S0S28S36Q8A1A1S33S5S19R8A1R2A3S33S5S19R4A1R2A3A3F_;Fz;F_;A2A2A2A2A2Lrp;A2Lmd;Ltr;Ltp;Lr;").

Definition JH2 : jpredA := ltac2:(tb__ "0|6|
S1bS26S36Q40M0A1M1A1S26S3bA1S3aS1S51S5VA2;R4R3R1A5S1VKc;R2R1A2S1S70VA2;R4A2S1S6fVA2;R4A2S1SfS72R1S6bA2S0G1S1cR6R2A2S1cVrho1;R2A2A3F_;Fv;S1SfS0S26S36Q8A1M2A1S21R5R1A2S21Vrho1;R1A2A3Fll;S1G1S3VTZ;S37G0R1A2A1A1S0S28G2A1M3S19R6R2A2S19Vrho1;R2A2A3F_;Fa;S1SeS3S61VA;Vi;Vch;R1A4A1S0G3S33S5S19R6A1R2A3S33S5S19Vrho1;A1R2A3M4A3F_;Fz;SeS3S53Vch;R1A2A1S3S0G3G4S30G2A1M5A3A1S3S0G3S33S5S19R7A1R3A3G5A3A1F_;F_;Fz;A2A2A2A2A2A2A2A2Lmd;Ltr;Ltp;Lr;").

Lemma JPh_stable : ltac2:(tb__ "0|0|
S46S5S65S50A3").
Proof.
  intros r r' tp tr md md' (Aw & Al & Am) Hme (rp & HJ & (Rw & Rl & Rout & Rin & Rrm) & C1 & C2 & C3 & C4).
  pose proof (JF_stable nW UStopLe false A Kc rho1 (stopJ_stable_le _) HKc) as HST.
  assert (Em : rm r' = rm r) by (apply functional_extensionality; intros a; symmetry; apply Am).
  exists (mkVal (rw r') (rl r') (rm rp)). split.
  - apply (HST rp (mkVal (rw r') (rl r') (rm rp)) tp tr md md'); [|exact Hme | exact HJ].
    split; [intros v Hv; cbn [rw]; rewrite <- (Rw v); apply Aw; exact Hv|]. split; [intros ll; cbn [rl]; rewrite <- (Rl ll); apply Al | intros a; reflexivity].
  - unfold blind_rel. cbn [rw rl rm]. rewrite Em. split; [split; [intros v; reflexivity | split; [intros ll; reflexivity | split; [exact Rout | split; [exact Rin | exact Rrm]]]]|]. repeat (split; [assumption|]). exact C4.
Qed.
Lemma JPh_okf : ltac2:(tb__ "0|0|
S43OF_;S45S5R1S44VKc;A1A3S45S5R2S50A3F_;Fok;").
Proof. intros ok H r t tr ms md msv' (rp & (_ & HJ) & _). apply (H r t tr ms md msv'). destruct HJ as (_ & _ & _ & HK & _). exact HK. Qed.
Lemma JPh_okpf : ltac2:(tb__ "0|0|
S43OF_;S47S5R1S44VKc;A1A3S47S5R2S50A3F_;Fok;").
Proof. intros ok H r t tr ms md x8 (rp & (_ & HJ) & _). apply (H r t tr ms md x8). destruct HJ as (_ & _ & _ & HK & _). exact HK. Qed.
Lemma JH2_stable : ltac2:(tb__ "0|0|
S46S5S65S4fA3").
Proof.
  intros r r' tp tr md md' (Aw & Al & Am) Hme (HA & HK & Htp & Htop & RW & RL & KEY & VK & PR).
  assert (Em : rm r' = rm r) by (apply functional_extensionality; intros a; symmetry; apply Am).
  split; [apply (AInvA_mat segsA A2 r' tp md md'); [unfold AInvA in *; rewrite Em; exact HA | exact Hme]|].
  split; [destruct Hme as ((mat' & ->) & _); rewrite with_vm_backing_with_vm; apply HKc; exact HK|].
  split; [unfold tp_ok in *; rewrite <- (Aw 24%positive) by (unfold NPRE; lia); exact Htp|].
  split; [unfold top_high in *; unfold V_DEPTH in *; rewrite <- (Aw 10%positive), <- (Aw 15%positive) by (unfold NPRE; lia); exact Htop|].
  split; [intros v Hv; rewrite <- (Aw v) by (unfold NPRE, GW in *; lia); exact (RW v Hv)|]. split; [intros ll; rewrite <- (Al ll); exact (RL ll)|].
  rewrite Em. exact (conj KEY (conj VK PR)).
Qed.
Lemma JH2_okf : ltac2:(tb__ "0|0|
S43OF_;S45S5R1S44VKc;A1A3S45S5R2S4fA3F_;Fok;").
Proof. intros ok H r t tr ms md msv' (_ & HK & _). exact (H r t tr ms md msv' HK). Qed.
Lemma JH2_okpf : ltac2:(tb__ "0|0|
S43OF_;S47S5R1S44VKc;A1A3S47S5R2S4fA3F_;Fok;").
Proof. intros ok H r t tr ms md x8 (_ & HK & _). exact (H r t tr ms md x8 HK). Qed.
End Node.

Section NodePre.
Variables (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Variables (A : AA) (rho1 : valuation) (l1 l2 : list (Z * Z)) (p n : Z) (i : nat) (ch lst : sec_chunk) (l : bool) (TZ : Z -> Prop).
Hypothesis HZTc : ltac2:(tb__ "0|0|
SeS53Vch;R1A2VTZ;R2A1F_;Fz;").
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Hypothesis HLV : ltac2:(tb__ "0|1|
S0S26S2cSeSeA2M0A1S15VA;A1S2dG0Vl1;S2eG0S2aSeSeVp;Vn;A4Vl2;A3A3A3").
Hypothesis HPR : is_primary n = false.
Hypothesis HI : ltac2:(tb__ "0|0|
S0S28S10A1S4dS10S11VA;A1Vi;A3S2bS10Vch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
S0SeVp;S6S6S12Vch;A1S4aA2Z800A2A3").
Hypothesis Hl : ltac2:(tb__ "0|1|
S0S28S10A1S4dS10S11VA;A1M0S39S25S10G0A2U1A2A3S2bS10Vlst;A2A3").
Hypothesis HLT : ltac2:(tb__ "0|0|
S0S24Vl;S29A3S0S2fVi;S39S25S10S11VA;A1A2U1A2A3F_;").
Hypothesis HLF : ltac2:(tb__ "0|0|
S0S24Vl;S27A3S57Vi;S39S25S10S11VA;A1A2U1A2A2F_;").
Hypothesis CH : ltac2:(tb__ "0|1|
S1S7Z646000Vh;A2S1S8Z0Vmsz;A2S1S8S6Vh;Vmsz;A2M0SbZ2Z2fA2A2S2S7G0S4cA2S7S4bVh;A2A2A2A2A2").
Hypothesis CHM : h mod 4096 = 0.
Hypothesis LSTOFF : ltac2:(tb__ "0|1|
S0S24Vl;S27A3S2S7S6S12Vlst;A1M0Z20A2Vh;A2S7S6Vh;Vmsz;A2G0A2A2F_;").
Hypothesis PABOFF : ltac2:(tb__ "0|1|
S2S7S6S14S13VA;A1A1M0S49A2Vh;A2S7S6Vh;Vmsz;A2G0A2A2").
Hypothesis NCB : ltac2:(tb__ "0|0|
S7SaZ8S9S25S10S11VA;A1A2A1A2S49A2").
Hypothesis HPIN : ltac2:(tb__ "0|3|
S1S0S36Q40M0A1M1S1cVrho1;P97A2S38G0S18S13VA;A1M2A1A2A3S1S0G1S1cVrho1;P98A2S38G0S16G2A1A2A3S0G1S1cVrho1;P9bA2S38G0S17G2A1A2A3A2A2").
Variable EUd : axst.
Hypothesis NA0 : ltac2:(tb__ "0|0|
S0S1aS22S5cVEUd;A1ZaA2S71A3").
Hypothesis NAX : ax_X EUd = [].

Lemma mun_pre : ltac2:(tb__ "0|d|
S1bS26S36Q40M0A1M1A1S0G1S1cR2PcaA2S38G0Vh;A2A3S1eS4eS1eR1S23S5cVEUd;A1A1A3M2S20S1fR5R2A2S2aSeSeVh;S6Vh;Vmsz;A2A4A2F_;Fo;S26S3bA1M3S66S3aS48S5R7R6VEUd;S2aG3S68R3S69R2R1A2A4A5S63VnW;VKc;VA;Vrho1;Vi;Vch;Vlst;Vl;VTZ;R8R7R4R2AdS67R4U0A2G1S1S0SeSdS37G0R1A2M4S42A2Z0A3S1S7S6G4Vmsz;A2M5S40A2S1S0S24S41S3dS3cR4A1A1M6R1S38G0Vmsz;A2M7A3S29A3S1G1S4eS2cG1G1A2S2aG1G1R2R1A4S3dS3cR5A1A1A3S0G1R2G7A3F_;Fs;S1S0S24S3fS3eG6R1A2R1G7A3S29A3S1S1eG2S20S1fRcR2A2S2aSeSeS37G0R3A2M8S6G8Vmsz;A2A4A2F_;Fo;S1S2cS1aS1aA2M9SeS4eG9R2S5dVEUd;A1A3S1S7S37G0S1dRdS31S1aS1aR3A3A2A2MaR2A2S8R2S6GaS37G0S1dRdS32S1aS1aR3A3A2A2A2A2A2S3S1S7S37G0R5A2MbS37G0S5fS37G0S1dReS5eVEUd;A1A2A2R3A2A2McA2S8GcS6GbVmsz;A2A2A2A1F_;F_;Fy;Frr;S62VKc;VA;Vrho1;Vl1;Vl2;Vi;Vch;VTZ;S5aRaS59S19RaA1R1G7A3A2S5bG4G5R9A3R6S58R4R1G7A3AcA2A2A2A2A2A2A2Ta;F_;F_;Fmd;Fms;Ftr;F_;F_;Ftp;Fr;").
Proof.
  intros r tp E202 HDISJ tr ms md Hsp (rp & (Hag & HA & _ & _ & HK & Htp & _ & Htop) & BR & C1 & C2 & C3 & C4). cbv zeta.
  destruct CH as (CH4 & CH3 & CH5 & CH6). destruct HPIN as (P151 & P152 & P155).
  destruct (pending_argsA segsA r tp EUd tr ms md Hsp) as (G0 & _). rewrite NA0 in G0. unfold vH in G0. cbn [eval] in G0. rewrite E202 in G0. rewrite G0. rewrite (u64_lit h) by lia.

  set (rpK := rho_sets rp [(156%positive, Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize))]).
  assert (ERM : rm rpK = rm rp) by (unfold rpK; apply rm_rho_sets).
  assert (OTH : forall v, v <> 156%positive -> rw rpK v = rw rp v) by (intros v Hv; unfold rpK; rewrite rho_sets_other; [reflexivity | cbn; intros [E|[]]; congruence]).
  assert (RP : forall v, (v < GW)%positive -> rw rp v = rw rho1 v) by (intros v Hv; symmetry; exact (proj1 Hag v Hv)).
  assert (HK0 : K0 Kc A rpK tp tr md).
  { split; [|split; [exact HK|split; [|split]]].
    - pose proof (AInvA_Q A rp tp md HA) as HQ. unfold AInvQ in *. rewrite ERM. exact HQ.
    - unfold tp_ok in *. rewrite OTH by discriminate. exact Htp.
    - unfold top_high in *. unfold V_DEPTH in *. rewrite !OTH by discriminate. exact Htop.
    - unfold rigidQ. rewrite !OTH by discriminate. rewrite !RP by (unfold GW; lia). split; [exact P151|]. split; [exact P152|]. split; [exact P155|].
      unfold rpK. apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]. }
  destruct (ks_munmap_ok segsA (K0 Kc) (K0_sec Kc HKc) A rpK tp tr md HK0 ch (nth_error_In _ _ HI)) as (MU1 & MU2 & MU3). fold h msz in MU1, MU2, MU3.
  split; [unfold page_size; exact CHM|]. split; [unfold TASK_SIZE; lia|]. split; [exact MU1|]. split; [exact MU2|]. split; [exact MU3|]. split; [exact HDISJ|].
  split; [intros rr y Hin; rewrite NAX in Hin; destruct Hin|].
  pose proof (unmap_inv A l1 l2 p n i ch lst l HLV HPR HI HU Hl HLT HLF (conj CH4 (conj CH3 (conj CH5 CH6))) LSTOFF PABOFF NCB TZ rp r tp md HA BR C1 C2 C3 C4
                (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) MU3) as HA2. fold h msz in HA2.
  destruct BR as (BW & BL & BOUT & BIN & BRM).
  assert (INR : forall x : word, SysStep.in_range (Z_to_bv 64 h) (Z_to_bv 64 msz) x = true <-> chunk_zone ch (bv_unsigned x)).
  { intros x. rewrite SysStep.in_range_spec. unfold chunk_zone. fold h msz. rewrite !u64_lit by lia. tauto. }
  assert (V4OUT : forall z, ~ chunk_zone ch z -> view segsA (rm (set_rm r (unmap_range (rm r) (Z_to_bv 64 h) (Z_to_bv 64 msz)))) z = view segsA (rm r) z).
  { intros z NZ. apply view_agree. intros Hz. cbn [rm set_rm]. rewrite unmap_range_at.
    destruct (SysStep.in_range (Z_to_bv 64 h) (Z_to_bv 64 msz) (Z_to_bv 64 z)) eqn:EI; [|reflexivity]. exfalso. apply NZ. pose proof (proj1 (INR _) EI) as X0. rewrite u64_lit in X0 by lia. exact X0. }
  assert (VRP : forall z, view segsA (rm rp) z = view segsA (rm rho1) z) by (intros z; apply view_agree; intros _; symmetry; exact (proj2 (proj2 Hag) _)).
  split; [exact HA2|]. split; [exact (HKc tr md (m_vm (munmap_model md (Z_to_bv 64 h) (Z_to_bv 64 msz))) HK)|].
  split; [unfold tp_ok in *; cbn [rw set_rm]; rewrite BW; exact Htp|].
  split; [unfold top_high in *; unfold V_DEPTH in *; cbn [rw set_rm]; rewrite !BW; exact Htop|].
  split; [intros v Hv; cbn [rw set_rm]; rewrite BW; exact (RP v Hv)|]. split; [intros ll; cbn [rl set_rm]; rewrite BL; symmetry; exact (proj1 (proj2 Hag) ll)|].
  split; [|split].
  - intros a0 NT. cbn [rm set_rm]. rewrite unmap_range_at.
    destruct (SysStep.in_range (Z_to_bv 64 h) (Z_to_bv 64 msz) a0) eqn:EI; [exfalso; apply NT; apply HZTc; exact (proj1 (INR a0) EI)|].
    rewrite (BRM a0 NT). symmetry. exact (proj2 (proj2 Hag) a0).
  - intros z NZ. rewrite V4OUT by (intros HC; apply NZ; left; exact HC). rewrite (BOUT z NZ). exact (VRP z).
  - intros z NC Hp. rewrite V4OUT by exact NC. rewrite <- VRP in Hp.
    intros HN. assert (NN : ~ ~ (DUZh A i ch z \/ ~ DUZh A i ch z)) by tauto. apply NN. intros [HZ|NZ]; [exact (BIN z HZ Hp HN) | rewrite (BOUT z NZ) in HN; exact (Hp HN)].
Qed.
End NodePre.
End F0A_hbN_unmap.

