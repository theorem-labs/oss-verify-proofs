(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_060.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca c4 F0A_skeln.
From Stdlib Require Permutation FunctionalExtensionality.
From stdpp Require list.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb dd.

(* [comment removed for export] *)
Module SpineMallocSec6IW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "ax_setS"; "la_state"; "entailsA"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "cell"; "ss_next"; "ss_facts"; "swf"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "DUnknown"; "mkObj"; "SPNot"; "sstate"; "DZero"; "SAlu"; "SPBranch"; "c_off"; "c_val"; "ob_cells"; "sv_eqb"; "@Corelib.Init.Datatypes"; "true"; "bool"; "nil"; "cons"; "list"; "prod"; "app"; "nat"; "option"; "pair"; "Some"; "length"; "false"; "andb"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2"; "nx0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "find"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7"; "KEPTF"; "KUB"; "idxsF"; "idxsU"; "S2F"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV"; "O_UBs"; "F_par"; "UBs"; "osplit"; "O_3"; "perm7"; "F_A"; "F_B"; "L3"; "O_3b"; "PGST"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "B3"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "a0e7"; "a2e6"; "a2e7"; "a2e8"; "fx8"; "sel7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6IW2.INST"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "mcfa"; "mcfb"; "mcqa"; "mcqb"; "CT6a"; "CT6b"; "CT7a"; "CT7b"; "CT8a"; "CT8b"; "CO6a"; "CO6b"; "CO8a"; "CO8b"; "swcfa"; "swcfb"; "swcqa"; "swcqb"; "CM7a"; "CM7b"; "S9bfa"; "S9bfb"; "S9bqa"; "S9bqb"; "E9pa"; "E9pb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "c1fa"; "c1fb"; "c1qa"; "c1qb"; "FXPa"; "FXPb"; "n7a"; "n7b"; "E6a"; "E6b"; "CO7a"; "CO7b"; "CO9pa"; "CO9pb"; "D6a"; "D6b"; "D7a"; "D7b"; "D8a"; "D8b"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "PXa"; "PXb"; "tybfa"; "tybfb"; "tybqa"; "tybqb"; "C5Aa"; "C5Ab"; "C5Ba"; "C5Bb"; "CR7a"; "CR7b"; "CS7a"; "CS7b"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "R6a"; "R6b"; "R7a"; "R7b"; "R8a"; "R8b"; "R9fa"; "R9fb"; "R9qa"; "R9qb"; "T6a"; "T6b"; "T7a"; "T7b"; "T8a"; "T8b"; "T9fa"; "T9fb"; "T9qa"; "T9qb"; "s6a"; "s6b"; "s7a"; "s7b"; "s8a"; "s8b"; "s9fa"; "s9fb"; "s9qa"; "s9qb"; "sFfa"; "sFfb"; "sFqa"; "sFqb"; "E9fa"; "E9fb"; "E9qa"; "E9qb"; "S9afa"; "S9afb"; "S9aqa"; "S9aqb"; "Y6Aa"; "Y6Ab"; "Y6Ba"; "Y6Bb"; "iMfa"; "iMfb"; "iMqa"; "iMqb"; "s6Aa"; "s6Ab"; "s6Ba"; "s6Bb"; "c2fa"; "c2fb"; "c2qa"; "c2qb"; "c4fa"; "c4fb"; "c4qa";
"c4qb"; "c5fa"; "c5fb"; "c5qa"; "c5qb"; "run6Aa"; "run6Ab"; "run6Ba"; "run6Bb"; "run7a"; "run7b"; "run8a"; "run8b"; "run9a"; "run9b"; "run9qa"; "run9qb"; "runFfa"; "runFfb"; "runFqa"; "runFqb"; "xcfa"; "xcfb"; "xcqa"; "xcqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "AE_A"; "L_malloc_ok"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST"; "O_1"; "Pret_ms"; "carveS"; "BR"; "O_2"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "SKEL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_NRES"; "V_NCH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2"; "C5ac"; "C5bc"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "modulo"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition tyb_of (mc : list cell) : Z := ltac2:(tb__ "0|4|
S28SdA1S35Lx;S34SdSdS1fS1cR1A1S11Z17f1A1A2Lc;Vmc;A3SdSbS35Lx;S1dR1A1S35R1Lt;S36Z0M0Li;S143SbSbG0Lb;La;M1Lop;M2G2S144G1Lop;M3G3S21S37SbG0La;Lw;Lsgn;S36SbS35G0Lk;Li;Ll;Xbx8Lc;G0X28x2").
Definition cells_at (i : nat) (F : axst) : list cell := ltac2:(tb__ "0|0|
S1eS3bSaVi;S13S2VF;A1A1S125S2fA1A4A1").

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Definition PXa : list sobj := [O_blk].
Definition FXPa : list sprop := ltac2:(tb__ "0|0|
S23ScS1bS142S14S134A1S14S133A1A3S22ScA1A3").

Definition C5Aa : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5ac).
Definition C5Ba : axst := Eval vm_compute in (ax_add_facts (F_B nx0) C5ac).
Lemma HC5Aa_0 : ltac2:(tb__ "0|0|
S0S3S47S4fS2fA1S13bA2Sb6A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Aa)). Qed.
Lemma HC5Ba_0 : ltac2:(tb__ "0|0|
S0S3S47S50S2fA1S13bA2Sb8A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ba)). Qed.
Lemma FBAa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2S13bA1A1A1S4fS2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBBa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2S13bA1A1A1S50S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run6Aa : option (list leafA) := Eval vm_compute in (runT6 C5Aa).
Lemma run6Aa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sb6S22S3A1A3A4S23G0S104S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Aa]). Qed.
Definition Y6Aa : axst := Eval vm_compute in (leafS 0 run6Aa).
Lemma Cert6Aa_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sb6S22S3A1M0A3S23S3SecG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Aa] [Y6Aa] [run6Aa]); [exact run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition run6Ba : option (list leafA) := Eval vm_compute in (runT6 C5Ba).
Lemma run6Ba__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sb8S22S3A1A3A4S23G0S106S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ba]). Qed.
Definition Y6Ba : axst := Eval vm_compute in (leafS 0 run6Ba).
Lemma Cert6Ba_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sb8S22S3A1M0A3S23S3SeeG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ba] [Y6Ba] [run6Ba]); [exact run6Ba__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6a : axst := Eval vm_compute in (rmF (F_A nx0) Y6Aa).
Definition s6Aa : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Aa) (ax_S E6a)).
Lemma E6Aa_0 : ltac2:(tb__ "0|0|
S0S21S8SecSa0Sf4A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Aa_0 : ltac2:(tb__ "0|0|
S0S21S12dSf4VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6Ba : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ba) (ax_S E6a)).
Lemma E6Ba_0 : ltac2:(tb__ "0|0|
S0S21S8SeeSa0Sf6A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ba_0 : ltac2:(tb__ "0|0|
S0S21S12dSf6VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6a : axst := Eval vm_compute in (rstS E6a ru6 []).
Definition CO6a : axst := Eval vm_compute in (carveS CT6a (O_3 nx0)).
Lemma WC6a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7cA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa0A1S2S7cA1A2S2aG3S29G1G2S23G0S29SbSbS6eS2fA1S51A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7cA1A1SeS2Sa0A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6a))). Qed.
Lemma HC6a_0 : ltac2:(tb__ "0|0|
S0S3S6Sa0S2S7cA1A2S7cA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6a)). Qed.
Lemma SK6a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S7cA1A1A4S39SaG0S73S26SaS23SaS129S2fA1S23SaS125S2fA1S22SaA1A3A3S26SaS130U2S2fA2Sb0A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXa))). Qed.
Lemma FC6a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6a_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S7cA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6a_0 : ltac2:(tb__ "0|0|
S0S3S127S7cS16S65S2fA1S11Z0A1S51S22SdA1S15A5A2S82A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6a)). Qed.
Lemma WCO6a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S82A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6a : wsub := Eval vm_compute in (callsub CO6a Pre_memsetA).
Definition R6a : list sobj := Eval vm_compute in (callR CO6a Pre_memsetA s6a).
Definition T6a : axst := Eval vm_compute in (callT CO6a Pre_memsetA Pret_ms s6a R6a).
Lemma He6a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S82S3cSd6A3S2aG0Sc2A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6a)). Qed.
Lemma Hchk6a_0 : ltac2:(tb__ "0|0|
S0S21S11fS82S3cSd6Sc2S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6a_0 : ltac2:(tb__ "0|0|
S0S3S121Sd6S3cS126S82Sc2A5SccA3"). Proof. vm_cast_no_check (@eq_refl _ (T6a)). Qed.
Lemma FBC6a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S82A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2SccA1A1A1SfS2S82A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6a_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S82A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6a : axst := Eval vm_compute in (ax_with_facts T6a (ss_facts (ax_S CO6a))).
Lemma HD6a_0 : ltac2:(tb__ "0|0|
S0S3S11eSccSfS2S82A1A1A2Sa6A3"). Proof. vm_cast_no_check (@eq_refl _ (D6a)). Qed.

Definition U7a : axst := Eval vm_compute in (U7p nx0 D6a).
Lemma WU7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S92A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa6A1S2S92A1A2S2aG3S29G1G2S22G0A1S68S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S92A1A1SeS2Sa6A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6a))). Qed.
Lemma HU7a_0 : ltac2:(tb__ "0|0|
S0S3S6Sa6S2S92A1A2S92A3"). Proof. vm_cast_no_check (@eq_refl _ (U7a)). Qed.
Definition run7a : option (list leafA) := Eval vm_compute in (runT6 U7a).
Lemma run7a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3S92S22S3A1A3A4S23G0S108S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7a]). Qed.
Definition ET7a : axst := Eval vm_compute in (leafS 0 run7a).
Lemma Cert7a_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3S92S22S3A1M0A3S23S3SacG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7a] [ET7a] [run7a]); [exact run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7a : axst := Eval vm_compute in (rstS ET7a (ru7 nx0) []).
Definition CO7a : axst := Eval vm_compute in (carveS CT7a (O_3n nx0)).
Definition CR7a : axst := Eval vm_compute in (DepotCall.oreb CO7a 1).
Definition n7a : nat := Eval vm_compute in (length (ss_objs (ax_S CR7a))).
Definition CS7a : axst := Eval vm_compute in (sel7 CR7a).
Definition CM7a : axst := Eval vm_compute in (DepotCall.omrg CS7a 1).
Lemma WC7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7eA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SacA1S2S7eA1A2S2aG3S29G1G2S23G0S29SbSbS6dS2fA1S128S2fA1A4S23G0S29SbSbS6fS2fA1S6bA4S22G0A1A3A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7eA1A1SeS2SacA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7a))). Qed.
Lemma HC7a_0 : ltac2:(tb__ "0|0|
S0S3S6SacS2S7eA1A2S7eA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7a)). Qed.
Lemma SK7a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S7eA1A1A4S39SaG0S73S26SaS23SaS4dS2fA1S23SaS129S2fA1S23SaS125S2fA1S22SaA1A3A3A3S26SaS130U2S2fA2Sb0A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXa))). Qed.
Lemma FC7a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7a_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S7eA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7a_0 : ltac2:(tb__ "0|0|
S0S3S127S7eS16S128S2fA1S11Z0A1S11Z100A1S22SdA1S15A5A2Sa2A3"). Proof. vm_cast_no_check (@eq_refl _ (CO7a)). Qed.
Lemma WCO7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2Sa2A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7a_0 : ltac2:(tb__ "0|0|
S0S21S138S18S146S2Sa2A1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7a_0 : ltac2:(tb__ "0|0|
S0S3S13aSa2U1A2SbaA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7a)). Qed.
Lemma LEN7a_0 : ltac2:(tb__ "0|0|
S0S27S2bSaS13S2SbaA1A1A2S9eA3"). Proof. vm_cast_no_check (@eq_refl _ (n7a)). Qed.
Lemma PERM_nd7a_0 : ltac2:(tb__ "0|0|
S0S21S12cS4eS9eA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7a_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S9eA2Li;S4eS9eA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7a_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S122R1A1S4eS9eA1A3Li;S3aU0S9eA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7a_0 : ltac2:(tb__ "0|0|
S0S3S72SbaA1SbcA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7a)). Qed.
Lemma MRG7a_0 : ltac2:(tb__ "0|0|
S0S21S138S18S145S2SbcA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7a_0 : ltac2:(tb__ "0|0|
S0S3S139SbcU1A2S8aA3"). Proof. vm_cast_no_check (@eq_refl _ (CM7a)). Qed.
Definition s7a : wsub := Eval vm_compute in (callsub CM7a Pre_memsetA).
Definition R7a : list sobj := Eval vm_compute in (callR CM7a Pre_memsetA s7a).
Definition T7a : axst := Eval vm_compute in (callT CM7a Pre_memsetA Pret_ms s7a R7a).
Lemma He7a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8aS3cSd8A3S2aG0Sc4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7a)). Qed.
Lemma Hchk7a_0 : ltac2:(tb__ "0|0|
S0S21S11fS8aS3cSd8Sc4S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7a_0 : ltac2:(tb__ "0|0|
S0S3S121Sd8S3cS126S8aSc4A5SceA3"). Proof. vm_cast_no_check (@eq_refl _ (T7a)). Qed.
Lemma FBC7a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8aA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2SceA1A1A1SfS2S8aA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7a_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8aA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7a : axst := Eval vm_compute in (ax_with_facts T7a (ss_facts (ax_S CM7a))).
Lemma HD7a_0 : ltac2:(tb__ "0|0|
S0S3S11eSceSfS2S8aA1A1A2Sa8A3"). Proof. vm_cast_no_check (@eq_refl _ (D7a)). Qed.

Definition U8a : axst := Eval vm_compute in (U8p nx0 D7a).
Lemma WU8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S94A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa8A1S2S94A1A2S2aG3S29G1G2S22G0A1S69S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S94A1A1SeS2Sa8A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7a))). Qed.
Lemma HU8a_0 : ltac2:(tb__ "0|0|
S0S3S6Sa8S2S94A1A2S94A3"). Proof. vm_cast_no_check (@eq_refl _ (U8a)). Qed.
Definition run8a : option (list leafA) := Eval vm_compute in (runT6 U8a).
Lemma run8a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3S94S22S3A1A3A4S23G0S10aS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8a]). Qed.
Definition ET8a : axst := Eval vm_compute in (leafS 0 run8a).
Lemma Cert8a_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3S94S22S3A1M0A3S23S3SaeG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8a] [ET8a] [run8a]); [exact run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8a : axst := Eval vm_compute in (CT8p nx0 ET8a).
Definition CO8a : axst := Eval vm_compute in (carveS CT8a (O_4 nx0)).
Lemma WC8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S80A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SaeA1S2S80A1A2S2aG3S29G1G2S22G0A1S71S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S80A1A1SeS2SaeA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8a))). Qed.
Lemma HC8a_0 : ltac2:(tb__ "0|0|
S0S3S6SaeS2S80A1A2S80A3"). Proof. vm_cast_no_check (@eq_refl _ (CT8a)). Qed.
Lemma SK8a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S80A1A1A4S39SaG0S73S26SaS23SaS52S2fA1S23SaS4dS2fA1S23SaS125S2fA1S22SaA1A3A3A3S26SaS130U2S2fA2Sb0A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXa))). Qed.
Lemma FC8a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8a_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S80A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8a_0 : ltac2:(tb__ "0|0|
S0S3S127S80S16S66S2fA1S11Z0A1S70S2fA1S22SdA1S15A5A2S84A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8a)). Qed.
Lemma WCO8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S84A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8a : wsub := Eval vm_compute in (callsub CO8a Pre_mszA).
Definition R8a : list sobj := Eval vm_compute in (callR CO8a Pre_mszA s8a).
Definition T8a : axst := Eval vm_compute in (callT CO8a Pre_mszA Pret_mz s8a R8a).
Lemma He8a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S84S131SdaA3S2aG0Sc6A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8a)). Qed.
Lemma Hchk8a_0 : ltac2:(tb__ "0|0|
S0S21S11fS84S131SdaSc6S39S4S3S7S132A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8a_0 : ltac2:(tb__ "0|0|
S0S3S121SdaS131S12aS84Sc6A5Sd0A3"). Proof. vm_cast_no_check (@eq_refl _ (T8a)). Qed.
Lemma FBC8a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S84A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd0A1A1A1SfS2S84A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8a_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S84A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8a : axst := Eval vm_compute in (ax_with_facts T8a (ss_facts (ax_S CO8a))).
Lemma HD8a_0 : ltac2:(tb__ "0|0|
S0S3S11eSd0SfS2S84A1A1A2SaaA3"). Proof. vm_cast_no_check (@eq_refl _ (D8a)). Qed.

Definition U9a : axst := Eval vm_compute in (U9p nx0 D8a).
Lemma WU9a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S96A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SaaA1S2S96A1A2S2aG3S29G1G2S22G0A1S6aS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S96A1A1SeS2SaaA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8a))). Qed.
Lemma HU9a_0 : ltac2:(tb__ "0|0|
S0S3S6SaaS2S96A1A2S96A3"). Proof. vm_cast_no_check (@eq_refl _ (U9a)). Qed.
Definition run9a : option (list leafA) := Eval vm_compute in (runT9 U9a).
Lemma run9a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS23S35S53S22S35A1A3A3S23S3S96S22S3A1A3A4S23G0S10cS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9a]). Qed.
Definition E9fa : axst := Eval vm_compute in (leafS 0 run9a).
Definition E9pa : axst := Eval vm_compute in (leafS 1 run9a).
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS23S35S53S22S35A1A3A3VGS0;S23S3S96S22S3A1M0A3S23S3Se4S23S3S90G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [U9a] [E9fa; E9pa] [run9a]); [exact run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S90A1A1A4S39SaG0S73S26SaS23SaS6cS2fA1S23SaS52S2fA1S23SaS4dS2fA1S23SaS125S2fA1S22SaA1A3A3A3A3S26SaS130U2S2fA2Sb0A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXa))). Qed.
Lemma FC9a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9a_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S90A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9a_0 : ltac2:(tb__ "0|0|
S30ScS17S4aA1SfS2S90A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S90A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pa : axst := Eval vm_compute in (carveS E9pa (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9a_0 : ltac2:(tb__ "0|0|
S0S3S127S90S16S67S2fA1S11Z0A1S11Z1A1S22SdA1S15A5A2Sa4A3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pa)). Qed.
Lemma WCO9a_0 : ltac2:(tb__ "0|0|
S0S21S10S2Sa4A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qa : option (list leafA) := Eval vm_compute in (runT6 CO9pa).
Lemma run9qa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sa4S22S3A1A3A4S23G0S10eS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qa]). Qed.
Definition E9qa : axst := Eval vm_compute in (leafS 0 run9qa).
Lemma Cert9qa_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sa4S22S3A1M0A3S23S3Se6G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [CO9pa] [E9qa] [run9qa]); [exact run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fa)) 0).
Definition S9afa : axst := Eval vm_compute in (osplit E9fa iMfa (SLit 6144)).
Definition S9bfa : axst := Eval vm_compute in (osplit S9afa (S iMfa) (SLit 10240)).
Lemma HS9afa_0 : ltac2:(tb__ "0|0|
S0S3S4cSe4Sf0S11Z1800A1A3Se8A3"). Proof. vm_cast_no_check (@eq_refl _ (S9afa)). Qed.
Lemma HS9bfa_0 : ltac2:(tb__ "0|0|
S0S3S4cSe8S2eSf0A1S11Z2800A1A3S8cA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfa)). Qed.
Definition s9fa : wsub := Eval vm_compute in (callsub S9bfa Pre_memsetA).
Definition R9fa : list sobj := Eval vm_compute in (callR S9bfa Pre_memsetA s9fa).
Definition T9fa : axst := Eval vm_compute in (callT S9bfa Pre_memsetA Pret_ms s9fa R9fa).
Lemma He9fa_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8cS3cSdcA3S2aG0Sc8A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9fa)). Qed.
Lemma Hchk9fa_0 : ltac2:(tb__ "0|0|
S0S21S11fS8cS3cSdcSc8S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9fa_0 : ltac2:(tb__ "0|0|
S0S3S121SdcS3cS126S8cSc8A5Sd2A3"). Proof. vm_cast_no_check (@eq_refl _ (T9fa)). Qed.
Lemma FBC9fa_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8cA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9fa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd2A1A1A1SfS2S8cA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9fa_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8cA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9fa : axst := Eval vm_compute in (ax_with_facts T9fa (ss_facts (ax_S S9bfa))).
Lemma HD9fa_0 : ltac2:(tb__ "0|0|
S0S3S11eSd2SfS2S8cA1A1A2SbeA3"). Proof. vm_cast_no_check (@eq_refl _ (D9fa)). Qed.
Definition runFfa : option (list leafA) := Eval vm_compute in (runTF D9fa).
Lemma runFfa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S22S35A1S23S3SbeS22S3A1A3A4S23G0S110S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfa]). Qed.
Definition FFfa : axst := Eval vm_compute in (leafS 0 runFfa).
Lemma CertFfa_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S22S35A1VGS0;S23S3SbeS22S3A1M0A3S23S3S74G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fa] [FFfa] [runFfa]); [exact runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfa : list cell := Eval vm_compute in (cells_at 5 FFfa).
Definition c1fa : list cell := Eval vm_compute in (cells_at 40 FFfa).
Definition c2fa : list cell := Eval vm_compute in (cells_at 41 FFfa).
Definition c4fa : list cell := Eval vm_compute in (cells_at 43 FFfa).
Definition c5fa : list cell := Eval vm_compute in (cells_at 47 FFfa).
Definition mcfa : list cell := Eval vm_compute in (cells_at 48 FFfa).
Definition xcfa : list cell := Eval vm_compute in (cells_at 50 FFfa).
Definition tybfa : Z := Eval vm_compute in (tyb_of mcfa).
Lemma SELFfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS13S2S74A1A1S41U2S2cA2A2S26SaS3fVW;S86A2S26SaS136S54S2fS98Sf8SfcS100S78S114Z20000S19S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfa ++ RT_m1 ++ RSF nx0 c1fa c2fa c4fa c5fa mcfa xcfa 131072 DZero false)). Qed.
Lemma NDFfa_0 : ltac2:(tb__ "0|0|
S0S21S12cS41U2S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS13S2S74A1A1A2A2Li;S41U2S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S122R1A1S41U2S2cA2A3Li;S3aU0S2bSaS13S2S74A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfa_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S74A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfa_0 : ax_base FFfa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfa_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfa_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfa_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S2cS17S4aA1S4aX21x2SfS2S74A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fa_0 : ltac2:(tb__ "0|0|
S1S30SdS59S98A3S1S30SdS55S98A3S1S30SdS56S98A3S1S30SdS5aS98A3S1S30SdS58S1aS141S14S133A1S11Z4000A1A3A1S98A3S30SdS57S98A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1fa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfa_0 : ltac2:(tb__ "0|0|
S1S30SdS5eS2fA1S78A3S1S30SdS5fS78A3S1S30SdS60S78A3S1S30SdS5cS78A3S1S30SdS5dS78A3S1S30SdS5bS2fA1S78A3S1S30SdS63S78A3S1S30SdS64Sb2A1S78A3S1S30SdS62S78A3S30SdS61S78A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfa) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfa_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13eZ0Sb2A2S13fSb2Z100A2A2S13dS140Sb2Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfa_0 : In (xc_map nx0) xcfa. Proof. exact (In_of_cellb (xc_map nx0) xcfa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfa_0 : ltac2:(tb__ "0|0|
S0S21S10S12fS2S74A1S26SaS3fVW;S86A2S23SaS49S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS26SaS3fVW;S86A2S23SaS49S2fA1S22SaA1A3A3S42U2A1A2S40VW;S86S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfa nx0)). Qed.
Lemma NDUfa_0 : nodupN (idxsU 2%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS26SaS3fVW;S86A2S23SaS49S2fA1S22SaA1A3A3A2A2Li;S42U2A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S122R1A1S42U2A1A3Li;S3aU0S2bSaS26SaS3fVW;S86A2S23SaS49S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fa_0 : ltac2:(tb__ "0|0|
S0S21S10S43S74S40VW;S86S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fa_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S12fS2S74A1S40VW;S86S2fA3M4A2S43S74G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S137A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fa_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S74A1A1S29SbSbS4bS2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfa : wsub := Eval vm_compute in (infer_sub NF (S2F FFfa (KUB W swcfa nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9fa_0 : ltac2:(tb__ "0|0|
S0S21S8S44S74S40VW;S86S2fA3S2fA3S11cS11bVW;Vst;A3Se0A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fa_0 : ltac2:(tb__ "0|0|
S0S21S12dSe0S135A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fa_0 : ltac2:(tb__ "0|0|
S0SbS12eSe0S11dA2S4bS2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qa)) 0).
Definition S9aqa : axst := Eval vm_compute in (osplit E9qa iMqa (SLit 6144)).
Definition S9bqa : axst := Eval vm_compute in (osplit S9aqa (S iMqa) (SLit 10240)).
Lemma HS9aqa_0 : ltac2:(tb__ "0|0|
S0S3S4cSe6Sf2S11Z1800A1A3SeaA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqa)). Qed.
Lemma HS9bqa_0 : ltac2:(tb__ "0|0|
S0S3S4cSeaS2eSf2A1S11Z2800A1A3S8eA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqa)). Qed.
Definition s9qa : wsub := Eval vm_compute in (callsub S9bqa Pre_memsetA).
Definition R9qa : list sobj := Eval vm_compute in (callR S9bqa Pre_memsetA s9qa).
Definition T9qa : axst := Eval vm_compute in (callT S9bqa Pre_memsetA Pret_ms s9qa R9qa).
Lemma He9qa_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8eS3cSdeA3S2aG0ScaA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9qa)). Qed.
Lemma Hchk9qa_0 : ltac2:(tb__ "0|0|
S0S21S11fS8eS3cSdeScaS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9qa_0 : ltac2:(tb__ "0|0|
S0S3S121SdeS3cS126S8eScaA5Sd4A3"). Proof. vm_cast_no_check (@eq_refl _ (T9qa)). Qed.
Lemma FBC9qa_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8eA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9qa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd4A1A1A1SfS2S8eA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9qa_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8eA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qa : axst := Eval vm_compute in (ax_with_facts T9qa (ss_facts (ax_S S9bqa))).
Lemma HD9qa_0 : ltac2:(tb__ "0|0|
S0S3S11eSd4SfS2S8eA1A1A2Sc0A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qa)). Qed.
Definition runFqa : option (list leafA) := Eval vm_compute in (runTF D9qa).
Lemma runFqa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S22S35A1S23S3Sc0S22S3A1A3A4S23G0S112S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqa]). Qed.
Definition FFqa : axst := Eval vm_compute in (leafS 0 runFqa).
Lemma CertFqa_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S22S35A1VGS0;S23S3Sc0S22S3A1M0A3S23S3S76G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qa] [FFqa] [runFqa]); [exact runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqa : list cell := Eval vm_compute in (cells_at 5 FFqa).
Definition c1qa : list cell := Eval vm_compute in (cells_at 40 FFqa).
Definition c2qa : list cell := Eval vm_compute in (cells_at 41 FFqa).
Definition c4qa : list cell := Eval vm_compute in (cells_at 43 FFqa).
Definition c5qa : list cell := Eval vm_compute in (cells_at 47 FFqa).
Definition mcqa : list cell := Eval vm_compute in (cells_at 48 FFqa).
Definition xcqa : list cell := Eval vm_compute in (cells_at 50 FFqa).
Definition tybqa : Z := Eval vm_compute in (tyb_of mcqa).
Lemma SELFqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS13S2S76A1A1S41U2S20A2A2S26SaS3fVW;S88A2S26SaS136S54S2fS9aSfaSfeS102S7aS116Z20000S19S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqa ++ RT_m1 ++ RSF nx0 c1qa c2qa c4qa c5qa mcqa xcqa 131072 DZero true)). Qed.
Lemma NDFqa_0 : ltac2:(tb__ "0|0|
S0S21S12cS41U2S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS13S2S76A1A1A2A2Li;S41U2S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S122R1A1S41U2S20A2A3Li;S3aU0S2bSaS13S2S76A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqa_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S76A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqa_0 : ax_base FFqa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqa_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S76A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqa_0 : ltac2:(tb__ "0|0|
S32ScS9cSfS2S76A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqa_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S20S17S4aA1S4aX21x2SfS2S76A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qa_0 : ltac2:(tb__ "0|0|
S1S30SdS59S9aA3S1S30SdS55S9aA3S1S30SdS56S9aA3S1S30SdS5aS9aA3S1S30SdS58S1aS141S14S133A1S11Z4000A1A3A1S9aA3S30SdS57S9aA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1qa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqa_0 : ltac2:(tb__ "0|0|
S1S30SdS5eS2fA1S7aA3S1S30SdS5fS7aA3S1S30SdS60S7aA3S1S30SdS5cS7aA3S1S30SdS5dS7aA3S1S30SdS5bS2fA1S7aA3S1S30SdS63S7aA3S1S30SdS64Sb4A1S7aA3S1S30SdS62S7aA3S30SdS61S7aA3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqa) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqa_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13eZ0Sb4A2S13fSb4Z100A2A2S13dS140Sb4Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqa_0 : In (xc_map nx0) xcqa. Proof. exact (In_of_cellb (xc_map nx0) xcqa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqa_0 : ltac2:(tb__ "0|0|
S0S21S10S12fS2S76A1S26SaS3fVW;S88A2S23SaS49S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS26SaS3fVW;S88A2S23SaS49S2fA1S22SaA1A3A3S42U2A1A2S40VW;S88S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqa nx0)). Qed.
Lemma NDUqa_0 : nodupN (idxsU 2%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS26SaS3fVW;S88A2S23SaS49S2fA1S22SaA1A3A3A2A2Li;S42U2A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S122R1A1S42U2A1A3Li;S3aU0S2bSaS26SaS3fVW;S88A2S23SaS49S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qa_0 : ltac2:(tb__ "0|0|
S0S21S10S43S76S40VW;S88S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qa_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S12fS2S76A1S40VW;S88S2fA3M4A2S43S76G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S137A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qa_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S76A1A1S29SbSbS4bS2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqa : wsub := Eval vm_compute in (infer_sub NF (S2F FFqa (KUB W swcqa nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9qa_0 : ltac2:(tb__ "0|0|
S0S21S8S44S76S40VW;S88S2fA3S2fA3S11cS11bVW;Vst;A3Se2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qa_0 : ltac2:(tb__ "0|0|
S0S21S12dSe2S135A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qa_0 : ltac2:(tb__ "0|0|
S0SbS12eSe2S11dA2S4bS2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition PXb : list sobj := [O_w].
Definition FXPb : list sprop := ltac2:(tb__ "0|0|
S23ScS17S1bS142S14S134A1S14S133A1A3A1S22ScA1A3").

Definition C5Ab : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5bc).
Definition C5Bb : axst := Eval vm_compute in (ax_add_facts (F_B nx0) C5bc).
Lemma HC5Ab_0 : ltac2:(tb__ "0|0|
S0S3S47S4fS2fA1S13cA2Sb7A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ab)). Qed.
Lemma HC5Bb_0 : ltac2:(tb__ "0|0|
S0S3S47S50S2fA1S13cA2Sb9A3"). Proof. vm_cast_no_check (@eq_refl _ (C5Bb)). Qed.
Lemma FBAb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2S13cA1A1A1S4fS2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBBb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2S13cA1A1A1S50S2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run6Ab : option (list leafA) := Eval vm_compute in (runT6 C5Ab).
Lemma run6Ab__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sb7S22S3A1A3A4S23G0S105S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ab]). Qed.
Definition Y6Ab : axst := Eval vm_compute in (leafS 0 run6Ab).
Lemma Cert6Ab_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sb7S22S3A1M0A3S23S3SedG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ab] [Y6Ab] [run6Ab]); [exact run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition run6Bb : option (list leafA) := Eval vm_compute in (runT6 C5Bb).
Lemma run6Bb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sb9S22S3A1A3A4S23G0S107S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Bb]). Qed.
Definition Y6Bb : axst := Eval vm_compute in (leafS 0 run6Bb).
Lemma Cert6Bb_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sb9S22S3A1M0A3S23S3SefG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Bb] [Y6Bb] [run6Bb]); [exact run6Bb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6b : axst := Eval vm_compute in (rmF (F_A nx0) Y6Ab).
Definition s6Ab : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ab) (ax_S E6b)).
Lemma E6Ab_0 : ltac2:(tb__ "0|0|
S0S21S8SedSa1Sf5A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ab_0 : ltac2:(tb__ "0|0|
S0S21S12dSf5VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6Bb : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Bb) (ax_S E6b)).
Lemma E6Bb_0 : ltac2:(tb__ "0|0|
S0S21S8SefSa1Sf7A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Bb_0 : ltac2:(tb__ "0|0|
S0S21S12dSf7VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6b : axst := Eval vm_compute in (rstS E6b ru6 []).
Definition CO6b : axst := Eval vm_compute in (carveS CT6b (O_3 nx0)).
Lemma WC6b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7dA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa1A1S2S7dA1A2S2aG3S29G1G2S23G0S29SbSbS6eS2fA1S51A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7dA1A1SeS2Sa1A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6b))). Qed.
Lemma HC6b_0 : ltac2:(tb__ "0|0|
S0S3S6Sa1S2S7dA1A2S7dA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6b)). Qed.
Lemma SK6b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S7dA1A1A4S39SaG0S73S26SaS23SaS129S2fA1S23SaS125S2fA1S22SaA1A3A3S26SaS130U2S2fA2Sb1A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXb))). Qed.
Lemma FC6b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6b_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S7dA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6b_0 : ltac2:(tb__ "0|0|
S0S3S127S7dS16S65S2fA1S11Z0A1S51S22SdA1S15A5A2S83A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6b)). Qed.
Lemma WCO6b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S83A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6b : wsub := Eval vm_compute in (callsub CO6b Pre_memsetA).
Definition R6b : list sobj := Eval vm_compute in (callR CO6b Pre_memsetA s6b).
Definition T6b : axst := Eval vm_compute in (callT CO6b Pre_memsetA Pret_ms s6b R6b).
Lemma He6b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S83S3cSd7A3S2aG0Sc3A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6b)). Qed.
Lemma Hchk6b_0 : ltac2:(tb__ "0|0|
S0S21S11fS83S3cSd7Sc3S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6b_0 : ltac2:(tb__ "0|0|
S0S3S121Sd7S3cS126S83Sc3A5ScdA3"). Proof. vm_cast_no_check (@eq_refl _ (T6b)). Qed.
Lemma FBC6b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S83A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2ScdA1A1A1SfS2S83A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S83A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6b : axst := Eval vm_compute in (ax_with_facts T6b (ss_facts (ax_S CO6b))).
Lemma HD6b_0 : ltac2:(tb__ "0|0|
S0S3S11eScdSfS2S83A1A1A2Sa7A3"). Proof. vm_cast_no_check (@eq_refl _ (D6b)). Qed.

Definition U7b : axst := Eval vm_compute in (U7p nx0 D6b).
Lemma WU7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S93A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa7A1S2S93A1A2S2aG3S29G1G2S22G0A1S68S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S93A1A1SeS2Sa7A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6b))). Qed.
Lemma HU7b_0 : ltac2:(tb__ "0|0|
S0S3S6Sa7S2S93A1A2S93A3"). Proof. vm_cast_no_check (@eq_refl _ (U7b)). Qed.
Definition run7b : option (list leafA) := Eval vm_compute in (runT6 U7b).
Lemma run7b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3S93S22S3A1A3A4S23G0S109S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7b]). Qed.
Definition ET7b : axst := Eval vm_compute in (leafS 0 run7b).
Lemma Cert7b_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3S93S22S3A1M0A3S23S3SadG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7b] [ET7b] [run7b]); [exact run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7b : axst := Eval vm_compute in (rstS ET7b (ru7 nx0) []).
Definition CO7b : axst := Eval vm_compute in (carveS CT7b (O_3n nx0)).
Definition CR7b : axst := Eval vm_compute in (DepotCall.oreb CO7b 1).
Definition n7b : nat := Eval vm_compute in (length (ss_objs (ax_S CR7b))).
Definition CS7b : axst := Eval vm_compute in (sel7 CR7b).
Definition CM7b : axst := Eval vm_compute in (DepotCall.omrg CS7b 1).
Lemma WC7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7fA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SadA1S2S7fA1A2S2aG3S29G1G2S23G0S29SbSbS6dS2fA1S128S2fA1A4S23G0S29SbSbS6fS2fA1S6bA4S22G0A1A3A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7fA1A1SeS2SadA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7b))). Qed.
Lemma HC7b_0 : ltac2:(tb__ "0|0|
S0S3S6SadS2S7fA1A2S7fA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7b)). Qed.
Lemma SK7b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S7fA1A1A4S39SaG0S73S26SaS23SaS4dS2fA1S23SaS129S2fA1S23SaS125S2fA1S22SaA1A3A3A3S26SaS130U2S2fA2Sb1A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXb))). Qed.
Lemma FC7b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7b_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S7fA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7b_0 : ltac2:(tb__ "0|0|
S0S3S127S7fS16S128S2fA1S11Z0A1S11Z100A1S22SdA1S15A5A2Sa3A3"). Proof. vm_cast_no_check (@eq_refl _ (CO7b)). Qed.
Lemma WCO7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2Sa3A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7b_0 : ltac2:(tb__ "0|0|
S0S21S138S18S146S2Sa3A1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7b_0 : ltac2:(tb__ "0|0|
S0S3S13aSa3U1A2SbbA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7b)). Qed.
Lemma LEN7b_0 : ltac2:(tb__ "0|0|
S0S27S2bSaS13S2SbbA1A1A2S9fA3"). Proof. vm_cast_no_check (@eq_refl _ (n7b)). Qed.
Lemma PERM_nd7b_0 : ltac2:(tb__ "0|0|
S0S21S12cS4eS9fA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7b_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S9fA2Li;S4eS9fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7b_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S122R1A1S4eS9fA1A3Li;S3aU0S9fA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7b_0 : ltac2:(tb__ "0|0|
S0S3S72SbbA1SbdA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7b)). Qed.
Lemma MRG7b_0 : ltac2:(tb__ "0|0|
S0S21S138S18S145S2SbdA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7b_0 : ltac2:(tb__ "0|0|
S0S3S139SbdU1A2S8bA3"). Proof. vm_cast_no_check (@eq_refl _ (CM7b)). Qed.
Definition s7b : wsub := Eval vm_compute in (callsub CM7b Pre_memsetA).
Definition R7b : list sobj := Eval vm_compute in (callR CM7b Pre_memsetA s7b).
Definition T7b : axst := Eval vm_compute in (callT CM7b Pre_memsetA Pret_ms s7b R7b).
Lemma He7b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8bS3cSd9A3S2aG0Sc5A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7b)). Qed.
Lemma Hchk7b_0 : ltac2:(tb__ "0|0|
S0S21S11fS8bS3cSd9Sc5S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7b_0 : ltac2:(tb__ "0|0|
S0S3S121Sd9S3cS126S8bSc5A5ScfA3"). Proof. vm_cast_no_check (@eq_refl _ (T7b)). Qed.
Lemma FBC7b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8bA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2ScfA1A1A1SfS2S8bA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7b_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8bA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7b : axst := Eval vm_compute in (ax_with_facts T7b (ss_facts (ax_S CM7b))).
Lemma HD7b_0 : ltac2:(tb__ "0|0|
S0S3S11eScfSfS2S8bA1A1A2Sa9A3"). Proof. vm_cast_no_check (@eq_refl _ (D7b)). Qed.

Definition U8b : axst := Eval vm_compute in (U8p nx0 D7b).
Lemma WU8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S95A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2Sa9A1S2S95A1A2S2aG3S29G1G2S22G0A1S69S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S95A1A1SeS2Sa9A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7b))). Qed.
Lemma HU8b_0 : ltac2:(tb__ "0|0|
S0S3S6Sa9S2S95A1A2S95A3"). Proof. vm_cast_no_check (@eq_refl _ (U8b)). Qed.
Definition run8b : option (list leafA) := Eval vm_compute in (runT6 U8b).
Lemma run8b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3S95S22S3A1A3A4S23G0S10bS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8b]). Qed.
Definition ET8b : axst := Eval vm_compute in (leafS 0 run8b).
Lemma Cert8b_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3S95S22S3A1M0A3S23S3SafG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8b] [ET8b] [run8b]); [exact run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8b : axst := Eval vm_compute in (CT8p nx0 ET8b).
Definition CO8b : axst := Eval vm_compute in (carveS CT8b (O_4 nx0)).
Lemma WC8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S81A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SafA1S2S81A1A2S2aG3S29G1G2S22G0A1S71S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S81A1A1SeS2SafA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8b))). Qed.
Lemma HC8b_0 : ltac2:(tb__ "0|0|
S0S3S6SafS2S81A1A2S81A3"). Proof. vm_cast_no_check (@eq_refl _ (CT8b)). Qed.
Lemma SK8b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S81A1A1A4S39SaG0S73S26SaS23SaS52S2fA1S23SaS4dS2fA1S23SaS125S2fA1S22SaA1A3A3A3S26SaS130U2S2fA2Sb1A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXb))). Qed.
Lemma FC8b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S81A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8b_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S81A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S81A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8b_0 : ltac2:(tb__ "0|0|
S0S3S127S81S16S66S2fA1S11Z0A1S70S2fA1S22SdA1S15A5A2S85A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8b)). Qed.
Lemma WCO8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S85A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8b : wsub := Eval vm_compute in (callsub CO8b Pre_mszA).
Definition R8b : list sobj := Eval vm_compute in (callR CO8b Pre_mszA s8b).
Definition T8b : axst := Eval vm_compute in (callT CO8b Pre_mszA Pret_mz s8b R8b).
Lemma He8b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S85S131SdbA3S2aG0Sc7A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8b)). Qed.
Lemma Hchk8b_0 : ltac2:(tb__ "0|0|
S0S21S11fS85S131SdbSc7S39S4S3S7S132A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8b_0 : ltac2:(tb__ "0|0|
S0S3S121SdbS131S12aS85Sc7A5Sd1A3"). Proof. vm_cast_no_check (@eq_refl _ (T8b)). Qed.
Lemma FBC8b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S85A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd1A1A1A1SfS2S85A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8b_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S85A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8b : axst := Eval vm_compute in (ax_with_facts T8b (ss_facts (ax_S CO8b))).
Lemma HD8b_0 : ltac2:(tb__ "0|0|
S0S3S11eSd1SfS2S85A1A1A2SabA3"). Proof. vm_cast_no_check (@eq_refl _ (D8b)). Qed.

Definition U9b : axst := Eval vm_compute in (U9p nx0 D8b).
Lemma WU9b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S97A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S2SabA1S2S97A1A2S2aG3S29G1G2S22G0A1S6aS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S97A1A1SeS2SabA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8b))). Qed.
Lemma HU9b_0 : ltac2:(tb__ "0|0|
S0S3S6SabS2S97A1A2S97A3"). Proof. vm_cast_no_check (@eq_refl _ (U9b)). Qed.
Definition run9b : option (list leafA) := Eval vm_compute in (runT9 U9b).
Lemma run9b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS23S35S53S22S35A1A3A3S23S3S97S22S3A1A3A4S23G0S10dS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9b]). Qed.
Definition E9fb : axst := Eval vm_compute in (leafS 0 run9b).
Definition E9pb : axst := Eval vm_compute in (leafS 1 run9b).
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS23S35S53S22S35A1A3A3VGS0;S23S3S97S22S3A1M0A3S23S3Se5S23S3S91G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [U9b] [E9fb; E9pb] [run9b]); [exact run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S73S13S2S91A1A1A4S39SaG0S73S26SaS23SaS6cS2fA1S23SaS52S2fA1S23SaS4dS2fA1S23SaS125S2fA1S22SaA1A3A3A3A3S26SaS130U2S2fA2Sb1A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXb))). Qed.
Lemma FC9b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S91A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9b_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S91A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9b_0 : ltac2:(tb__ "0|0|
S30ScS17S4aA1SfS2S91A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S91A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pb : axst := Eval vm_compute in (carveS E9pb (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9b_0 : ltac2:(tb__ "0|0|
S0S3S127S91S16S67S2fA1S11Z0A1S11Z1A1S22SdA1S15A5A2Sa5A3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pb)). Qed.
Lemma WCO9b_0 : ltac2:(tb__ "0|0|
S0S21S10S2Sa5A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qb : option (list leafA) := Eval vm_compute in (runT6 CO9pb).
Lemma run9qb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S23S35S3eS22S35A1A3S23S3Sa5S22S3A1A3A4S23G0S10fS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qb]). Qed.
Definition E9qb : axst := Eval vm_compute in (leafS 0 run9qb).
Lemma Cert9qb_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S23S35S3eS22S35A1A3VGS0;S23S3Sa5S22S3A1M0A3S23S3Se7G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [CO9pb] [E9qb] [run9qb]); [exact run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fb)) 0).
Definition S9afb : axst := Eval vm_compute in (osplit E9fb iMfb (SLit 6144)).
Definition S9bfb : axst := Eval vm_compute in (osplit S9afb (S iMfb) (SLit 10240)).
Lemma HS9afb_0 : ltac2:(tb__ "0|0|
S0S3S4cSe5Sf1S11Z1800A1A3Se9A3"). Proof. vm_cast_no_check (@eq_refl _ (S9afb)). Qed.
Lemma HS9bfb_0 : ltac2:(tb__ "0|0|
S0S3S4cSe9S2eSf1A1S11Z2800A1A3S8dA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfb)). Qed.
Definition s9fb : wsub := Eval vm_compute in (callsub S9bfb Pre_memsetA).
Definition R9fb : list sobj := Eval vm_compute in (callR S9bfb Pre_memsetA s9fb).
Definition T9fb : axst := Eval vm_compute in (callT S9bfb Pre_memsetA Pret_ms s9fb R9fb).
Lemma He9fb_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8dS3cSddA3S2aG0Sc9A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9fb)). Qed.
Lemma Hchk9fb_0 : ltac2:(tb__ "0|0|
S0S21S11fS8dS3cSddSc9S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9fb_0 : ltac2:(tb__ "0|0|
S0S3S121SddS3cS126S8dSc9A5Sd3A3"). Proof. vm_cast_no_check (@eq_refl _ (T9fb)). Qed.
Lemma FBC9fb_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8dA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9fb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd3A1A1A1SfS2S8dA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9fb_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8dA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9fb : axst := Eval vm_compute in (ax_with_facts T9fb (ss_facts (ax_S S9bfb))).
Lemma HD9fb_0 : ltac2:(tb__ "0|0|
S0S3S11eSd3SfS2S8dA1A1A2SbfA3"). Proof. vm_cast_no_check (@eq_refl _ (D9fb)). Qed.
Definition runFfb : option (list leafA) := Eval vm_compute in (runTF D9fb).
Lemma runFfb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S22S35A1S23S3SbfS22S3A1A3A4S23G0S111S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfb]). Qed.
Definition FFfb : axst := Eval vm_compute in (leafS 0 runFfb).
Lemma CertFfb_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S22S35A1VGS0;S23S3SbfS22S3A1M0A3S23S3S75G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fb] [FFfb] [runFfb]); [exact runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfb : list cell := Eval vm_compute in (cells_at 5 FFfb).
Definition c1fb : list cell := Eval vm_compute in (cells_at 40 FFfb).
Definition c2fb : list cell := Eval vm_compute in (cells_at 41 FFfb).
Definition c4fb : list cell := Eval vm_compute in (cells_at 43 FFfb).
Definition c5fb : list cell := Eval vm_compute in (cells_at 47 FFfb).
Definition mcfb : list cell := Eval vm_compute in (cells_at 48 FFfb).
Definition xcfb : list cell := Eval vm_compute in (cells_at 50 FFfb).
Definition tybfb : Z := Eval vm_compute in (tyb_of mcfb).
Lemma SELFfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS13S2S75A1A1S41U2S2cA2A2S26SaS3fVW;S87A2S26SaS136S54S2fS99Sf9SfdS101S79S115Z8S15S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfb ++ RT_m1 ++ RSF nx0 c1fb c2fb c4fb c5fb mcfb xcfb 8 DUnknown false)). Qed.
Lemma NDFfb_0 : ltac2:(tb__ "0|0|
S0S21S12cS41U2S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS13S2S75A1A1A2A2Li;S41U2S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S122R1A1S41U2S2cA2A3Li;S3aU0S2bSaS13S2S75A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfb_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S75A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfb_0 : ax_base FFfb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfb_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S75A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfb_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S75A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfb_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S2cS17S4aA1S4aX21x2SfS2S75A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fb_0 : ltac2:(tb__ "0|0|
S1S30SdS59S99A3S1S30SdS55S99A3S1S30SdS56S99A3S1S30SdS5aS99A3S1S30SdS58S14S133A1A1S99A3S30SdS57S99A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1fb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfb_0 : ltac2:(tb__ "0|0|
S1S30SdS5eS2fA1S79A3S1S30SdS5fS79A3S1S30SdS60S79A3S1S30SdS5cS79A3S1S30SdS5dS79A3S1S30SdS5bS2fA1S79A3S1S30SdS63S79A3S1S30SdS64Sb3A1S79A3S1S30SdS62S79A3S30SdS61S79A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfb) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfb_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13eZ0Sb3A2S13fSb3Z100A2A2S13dS140Sb3Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfb_0 : In (xc_map nx0) xcfb. Proof. exact (In_of_cellb (xc_map nx0) xcfb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfb_0 : ltac2:(tb__ "0|0|
S0S21S10S12fS2S75A1S26SaS3fVW;S87A2S23SaS49S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS26SaS3fVW;S87A2S23SaS49S2fA1S22SaA1A3A3S42U2A1A2S40VW;S87S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfb nx0)). Qed.
Lemma NDUfb_0 : nodupN (idxsU 2%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS26SaS3fVW;S87A2S23SaS49S2fA1S22SaA1A3A3A2A2Li;S42U2A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S122R1A1S42U2A1A3Li;S3aU0S2bSaS26SaS3fVW;S87A2S23SaS49S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fb_0 : ltac2:(tb__ "0|0|
S0S21S10S43S75S40VW;S87S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fb_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S12fS2S75A1S40VW;S87S2fA3M4A2S43S75G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S137A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fb_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S75A1A1S29SbSbS4bS2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfb : wsub := Eval vm_compute in (infer_sub NF (S2F FFfb (KUB W swcfb nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9fb_0 : ltac2:(tb__ "0|0|
S0S21S8S44S75S40VW;S87S2fA3S2fA3S11cS11bVW;Vst;A3Se1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fb_0 : ltac2:(tb__ "0|0|
S0S21S12dSe1S135A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fb_0 : ltac2:(tb__ "0|0|
S0SbS12eSe1S11dA2S4bS2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qb)) 0).
Definition S9aqb : axst := Eval vm_compute in (osplit E9qb iMqb (SLit 6144)).
Definition S9bqb : axst := Eval vm_compute in (osplit S9aqb (S iMqb) (SLit 10240)).
Lemma HS9aqb_0 : ltac2:(tb__ "0|0|
S0S3S4cSe7Sf3S11Z1800A1A3SebA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqb)). Qed.
Lemma HS9bqb_0 : ltac2:(tb__ "0|0|
S0S3S4cSebS2eSf3A1S11Z2800A1A3S8fA3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqb)). Qed.
Definition s9qb : wsub := Eval vm_compute in (callsub S9bqb Pre_memsetA).
Definition R9qb : list sobj := Eval vm_compute in (callR S9bqb Pre_memsetA s9qb).
Definition T9qb : axst := Eval vm_compute in (callT S9bqb Pre_memsetA Pret_ms s9qb R9qb).
Lemma He9qb_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S120S8fS3cSdfA3S2aG0ScbA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9qb)). Qed.
Lemma Hchk9qb_0 : ltac2:(tb__ "0|0|
S0S21S11fS8fS3cSdfScbS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9qb_0 : ltac2:(tb__ "0|0|
S0S3S121SdfS3cS126S8fScbA5Sd5A3"). Proof. vm_cast_no_check (@eq_refl _ (T9qb)). Qed.
Lemma FBC9qb_0 : ltac2:(tb__ "0|1|
S0S21S31ScS12SeS2S8fA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9qb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS12SeS2Sd5A1A1A1SfS2S8fA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9qb_0 : ltac2:(tb__ "0|0|
S0S21S124VGS0;SeS2S8fA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qb : axst := Eval vm_compute in (ax_with_facts T9qb (ss_facts (ax_S S9bqb))).
Lemma HD9qb_0 : ltac2:(tb__ "0|0|
S0S3S11eSd5SfS2S8fA1A1A2Sc1A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qb)). Qed.
Definition runFqb : option (list leafA) := Eval vm_compute in (runTF D9qb).
Lemma runFqb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S48S38Ufa0S22S35A1S23S3Sc1S22S3A1A3A4S23G0S113S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqb]). Qed.
Definition FFqb : axst := Eval vm_compute in (leafS 0 runFqb).
Lemma CertFqb_0 : ltac2:(tb__ "0|1|
S0S21S46S38Ufa0S22S35A1VGS0;S23S3Sc1S22S3A1M0A3S23S3S77G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qb] [FFqb] [runFqb]); [exact runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqb : list cell := Eval vm_compute in (cells_at 5 FFqb).
Definition c1qb : list cell := Eval vm_compute in (cells_at 40 FFqb).
Definition c2qb : list cell := Eval vm_compute in (cells_at 41 FFqb).
Definition c4qb : list cell := Eval vm_compute in (cells_at 43 FFqb).
Definition c5qb : list cell := Eval vm_compute in (cells_at 47 FFqb).
Definition mcqb : list cell := Eval vm_compute in (cells_at 48 FFqb).
Definition xcqb : list cell := Eval vm_compute in (cells_at 50 FFqb).
Definition tybqb : Z := Eval vm_compute in (tyb_of mcqb).
Lemma SELFqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS13S2S77A1A1S41U2S20A2A2S26SaS3fVW;S89A2S26SaS136S54S2fS9bSfbSffS103S7bS117Z8S15S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqb ++ RT_m1 ++ RSF nx0 c1qb c2qb c4qb c5qb mcqb xcqb 8 DUnknown true)). Qed.
Lemma NDFqb_0 : ltac2:(tb__ "0|0|
S0S21S12cS41U2S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS13S2S77A1A1A2A2Li;S41U2S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S122R1A1S41U2S20A2A3Li;S3aU0S2bSaS13S2S77A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqb_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S5S77A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqb_0 : ax_base FFqb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqb_0 : ltac2:(tb__ "0|0|
S32ScS26ScS11aVW;Vst;A2S119S118A1A3SfS2S77A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqb_0 : ltac2:(tb__ "0|0|
S32ScS9dSfS2S77A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqb_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S20S17S4aA1S4aX21x2SfS2S77A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qb_0 : ltac2:(tb__ "0|0|
S1S30SdS59S9bA3S1S30SdS55S9bA3S1S30SdS56S9bA3S1S30SdS5aS9bA3S1S30SdS58S14S133A1A1S9bA3S30SdS57S9bA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1qb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqb_0 : ltac2:(tb__ "0|0|
S1S30SdS5eS2fA1S7bA3S1S30SdS5fS7bA3S1S30SdS60S7bA3S1S30SdS5cS7bA3S1S30SdS5dS7bA3S1S30SdS5bS2fA1S7bA3S1S30SdS63S7bA3S1S30SdS64Sb5A1S7bA3S1S30SdS62S7bA3S30SdS61S7bA3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqb) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqb_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13eZ0Sb5A2S13fSb5Z100A2A2S13dS140Sb5Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqb_0 : In (xc_map nx0) xcqb. Proof. exact (In_of_cellb (xc_map nx0) xcqb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqb_0 : ltac2:(tb__ "0|0|
S0S21S10S12fS2S77A1S26SaS3fVW;S89A2S23SaS49S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S12bS26SaS3fVW;S89A2S23SaS49S2fA1S22SaA1A3A3S42U2A1A2S40VW;S89S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqb nx0)). Qed.
Lemma NDUqb_0 : nodupN (idxsU 2%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S123R1S2bSaS26SaS3fVW;S89A2S23SaS49S2fA1S22SaA1A3A3A2A2Li;S42U2A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S122R1A1S42U2A1A3Li;S3aU0S2bSaS26SaS3fVW;S89A2S23SaS49S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qb_0 : ltac2:(tb__ "0|0|
S0S21S10S43S77S40VW;S89S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qb_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S45S12fS2S77A1S40VW;S89S2fA3M4A2S43S77G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S137A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qb_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S77A1A1S29SbSbS4bS2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqb : wsub := Eval vm_compute in (infer_sub NF (S2F FFqb (KUB W swcqb nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9qb_0 : ltac2:(tb__ "0|0|
S0S21S8S44S77S40VW;S89S2fA3S2fA3S11cS11bVW;Vst;A3Se3A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qb_0 : ltac2:(tb__ "0|0|
S0S21S12dSe3S135A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qb_0 : ltac2:(tb__ "0|0|
S0SbS12eSe3S11dA2S4bS2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
End INST.
End SpineMallocSec6IW2.

(* [comment removed for export] *)
Module SpineMallocSec6ILW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "ax_X"; "la_state"; "entailsA"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "cell"; "ss_next"; "ss_facts"; "swf"; "SLit"; "ss_objs"; "sprop_below"; "SVar"; "DUnknown"; "mkObj"; "SPNot"; "sstate"; "DZero"; "SAlu"; "SPBranch"; "c_off"; "c_val"; "ob_cells"; "sv_eqb"; "@Corelib.Init.Datatypes"; "true"; "bool"; "nil"; "cons"; "list"; "prod"; "app"; "nat"; "option"; "pair"; "Some"; "length"; "false"; "andb"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2"; "nx0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "find"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7"; "KEPTF"; "KUB"; "idxsF"; "idxsU"; "S2F"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV"; "O_UBs"; "F_par"; "UBs"; "osplit"; "O_3"; "perm7"; "F_A"; "L3"; "O_3b"; "PGST"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "B3"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "a0e7"; "a2e6"; "a2e7"; "a2e8"; "fx8"; "sel7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.SpineMallocSec6ILW2.INST"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "mcfa"; "mcfb"; "mcqa"; "mcqb"; "CT6a"; "CT6b"; "CT7a"; "CT7b"; "CT8a"; "CT8b"; "CO6a"; "CO6b"; "CO8a"; "CO8b"; "swcfa"; "swcfb"; "swcqa"; "swcqb"; "CM7a"; "CM7b"; "D6La"; "D6Lb"; "D7La"; "D7Lb"; "D8La"; "D8Lb"; "S9bfa"; "S9bfb"; "S9bqa"; "S9bqb"; "E9pa"; "E9pb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "c1fa"; "c1fb"; "c1qa"; "c1qb"; "FXPa"; "FXPb"; "n7a"; "n7b"; "D6a"; "D6b"; "D7a"; "D7b"; "D8a"; "D8b"; "CO7a"; "CO7b"; "CO9pa"; "CO9pb"; "E6a"; "E6b"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "PXa"; "PXb"; "tybfa"; "tybfb"; "tybqa"; "tybqb"; "C5Aa"; "C5Ab"; "CR7a"; "CR7b"; "CS7a"; "CS7b"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "R6a"; "R6b"; "R7a"; "R7b"; "R8a"; "R8b"; "R9fa"; "R9fb"; "R9qa"; "R9qb"; "T6a"; "T6b"; "T7a"; "T7b"; "T8a"; "T8b"; "T9fa"; "T9fb"; "T9qa"; "T9qb"; "s6a"; "s6b"; "s7a"; "s7b"; "s8a"; "s8b"; "s9fa"; "s9fb"; "s9qa"; "s9qb"; "sFfa"; "sFfb"; "sFqa"; "sFqb"; "E9fa"; "E9fb"; "E9qa"; "E9qb"; "S9afa"; "S9afb"; "S9aqa"; "S9aqb"; "Y6Aa"; "Y6Ab"; "iMfa"; "iMfb"; "iMqa"; "iMqb"; "s6Aa"; "s6Ab"; "c2fa"; "c2fb"; "c2qa"; "c2qb"; "c4fa"; "c4fb"; "c4qa"; "c4qb";
"c5fa"; "c5fb"; "c5qa"; "c5qb"; "run6Aa"; "run6Ab"; "run7a"; "run7b"; "run8a"; "run8b"; "run9a"; "run9b"; "run9qa"; "run9qb"; "runFfa"; "runFfb"; "runFqa"; "runFqb"; "xcfa"; "xcfb"; "xcqa"; "xcqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "AE_A"; "L_malloc_ok"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST"; "O_1"; "Pret_ms"; "carveS"; "BR"; "O_2"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "SKEL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec6L"; "F_low"; "F_g7L"; "F_g8L"; "F_g9L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_NRES"; "V_NCH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "isSome"; "omrg"; "oreb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2"; "C5ac"; "C5bc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4ILW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSec7.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition tyb_of (mc : list cell) : Z := ltac2:(tb__ "0|4|
S28SdA1S35Lx;S34SdSdS1fS1cR1A1S11Z17f1A1A2Lc;Vmc;A3SdSbS35Lx;S1dR1A1S35R1Lt;S36Z0M0Li;S144SbSbG0Lb;La;M1Lop;M2G2S145G1Lop;M3G3S21S37SbG0La;Lw;Lsgn;S36SbS35G0Lk;Li;Ll;Xbx8Lc;G0X28x2").
Definition cells_at (i : nat) (F : axst) : list cell := ltac2:(tb__ "0|0|
S1eS3bSaVi;S12S2VF;A1A1S122S2fA1A4A1").

Section INST.
Let W : list ulink := Wcan 2. Let st : ustop := UStopLe. Let tmax : Z := 4.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.GS nx0.

Definition PXa : list sobj := [O_blk].
Definition FXPa : list sprop := ltac2:(tb__ "0|0|
S23ScS1bS143S14S135A1S14S134A1A3S22ScA1A3").

Definition C5Aa : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5ac).
Lemma HC5Aa_0 : ltac2:(tb__ "0|0|
S0S3S71S4cS2fA1S140A2SbbA3"). Proof. vm_cast_no_check (@eq_refl _ (C5Aa)). Qed.
Lemma FBAa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2S140A1A1A1S4cS2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FLOWa_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2S140A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition run6Aa : option (list leafA) := Eval vm_compute in (runT6 C5Aa).
Lemma run6Aa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3SbbS22S3A1A3A4S23G0S103S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Aa]). Qed.
Definition Y6Aa : axst := Eval vm_compute in (leafS 0 run6Aa).
Lemma Cert6Aa_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3SbbS22S3A1M0A3S23S3SefG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Aa] [Y6Aa] [run6Aa]); [exact run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6a : axst := Eval vm_compute in (rmF (F_A nx0) Y6Aa).
Definition s6Aa : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Aa) (ax_S E6a)).
Lemma E6Aa_0 : ltac2:(tb__ "0|0|
S0S21S8SefSafSf5A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Aa_0 : ltac2:(tb__ "0|0|
S0S21S132Sf5VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6a : axst := Eval vm_compute in (rstS E6a ru6 []).
Definition CO6a : axst := Eval vm_compute in (carveS CT6a (O_3 nx0)).
Lemma WC6a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7bA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2SafA1S2S7bA1A2S2aG3S29G1G2S23G0S29SbSbS6aS2fA1S4dA4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7bA1A1SeS2SafA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6a))). Qed.
Lemma HC6a_0 : ltac2:(tb__ "0|0|
S0S3S5SafS2S7bA1A2S7bA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6a)). Qed.
Lemma SK6a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7bA1A1A4S39SaG0S6fS26SaS23SaS126S2fA1S23SaS122S2fA1S22SaA1A3A3S26SaS12bU2S2fA2Sb5A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXa))). Qed.
Lemma FC6a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7bA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6a_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S7bA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7bA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6a_0 : ltac2:(tb__ "0|0|
S0S3S124S7bS16S61S2fA1S11Z0A1S4dS22SdA1S15A5A2S81A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6a)). Qed.
Lemma WCO6a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S81A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6a : wsub := Eval vm_compute in (callsub CO6a Pre_memsetA).
Definition R6a : list sobj := Eval vm_compute in (callR CO6a Pre_memsetA s6a).
Definition T6a : axst := Eval vm_compute in (callT CO6a Pre_memsetA Pret_ms s6a R6a).
Lemma He6a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS81S3cSd9A3S2aG0Sc5A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6a)). Qed.
Lemma Hchk6a_0 : ltac2:(tb__ "0|0|
S0S21S11cS81S3cSd9Sc5S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6a_0 : ltac2:(tb__ "0|0|
S0S3S11eSd9S3cS123S81Sc5A5ScfA3"). Proof. vm_cast_no_check (@eq_refl _ (T6a)). Qed.
Lemma FBC6a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S81A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2ScfA1A1A1SfS2S81A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6a_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S81A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6a : axst := Eval vm_compute in (ax_with_facts T6a (ss_facts (ax_S CO6a))).
Lemma HD6a_0 : ltac2:(tb__ "0|0|
S0S3S11bScfSfS2S81A1A1A2Sa5A3"). Proof. vm_cast_no_check (@eq_refl _ (D6a)). Qed.

Definition D6La : axst := Eval vm_compute in (rstS D6a [] (F_g7L nx0)).
Lemma WD6La_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8bA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD6La_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa5A1S2S8bA1A2S2aG3S29G1G2S22G0A1S12dS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7L nx0))). Qed.
Lemma NXD6La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8bA1A1SeS2Sa5A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6a))). Qed.
Lemma HD6La_0 : ltac2:(tb__ "0|0|
S0S3S5Sa5S2S8bA1A2S8bA3"). Proof. vm_cast_no_check (@eq_refl _ (D6La)). Qed.
Lemma FLOW6a_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa5A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U7a : axst := Eval vm_compute in (U7p nx0 D6La).
Lemma WU7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S97A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8bA1S2S97A1A2S2aG3S29G1G2S22G0A1S64S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S97A1A1SeS2S8bA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6La))). Qed.
Lemma HU7a_0 : ltac2:(tb__ "0|0|
S0S3S5S8bS2S97A1A2S97A3"). Proof. vm_cast_no_check (@eq_refl _ (U7a)). Qed.
Definition run7a : option (list leafA) := Eval vm_compute in (runT6 U7a).
Lemma run7a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3S97S22S3A1A3A4S23G0S105S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7a]). Qed.
Definition ET7a : axst := Eval vm_compute in (leafS 0 run7a).
Lemma Cert7a_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3S97S22S3A1M0A3S23S3Sb1G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7a] [ET7a] [run7a]); [exact run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7a : axst := Eval vm_compute in (rstS ET7a (ru7 nx0) []).
Definition CO7a : axst := Eval vm_compute in (carveS CT7a (O_3n nx0)).
Definition CR7a : axst := Eval vm_compute in (DepotCall.oreb CO7a 1).
Definition n7a : nat := Eval vm_compute in (length (ss_objs (ax_S CR7a))).
Definition CS7a : axst := Eval vm_compute in (sel7 CR7a).
Definition CM7a : axst := Eval vm_compute in (DepotCall.omrg CS7a 1).
Lemma WC7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7dA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb1A1S2S7dA1A2S2aG3S29G1G2S23G0S29SbSbS69S2fA1S125S2fA1A4S23G0S29SbSbS6bS2fA1S67A4S22G0A1A3A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7dA1A1SeS2Sb1A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7a))). Qed.
Lemma HC7a_0 : ltac2:(tb__ "0|0|
S0S3S5Sb1S2S7dA1A2S7dA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7a)). Qed.
Lemma SK7a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7dA1A1A4S39SaG0S6fS26SaS23SaS4aS2fA1S23SaS126S2fA1S23SaS122S2fA1S22SaA1A3A3A3S26SaS12bU2S2fA2Sb5A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXa))). Qed.
Lemma FC7a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7a_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S7dA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7dA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7a_0 : ltac2:(tb__ "0|0|
S0S3S124S7dS16S125S2fA1S11Z0A1S11Z100A1S22SdA1S15A5A2SabA3"). Proof. vm_cast_no_check (@eq_refl _ (CO7a)). Qed.
Lemma WCO7a_0 : ltac2:(tb__ "0|0|
S0S21S10S2SabA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7a_0 : ltac2:(tb__ "0|0|
S0S21S139S18S147S2SabA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7a_0 : ltac2:(tb__ "0|0|
S0S3S13bSabU1A2SbdA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7a)). Qed.
Lemma LEN7a_0 : ltac2:(tb__ "0|0|
S0S27S2bSaS12S2SbdA1A1A2Sa3A3"). Proof. vm_cast_no_check (@eq_refl _ (n7a)). Qed.
Lemma PERM_nd7a_0 : ltac2:(tb__ "0|0|
S0S21S129S4bSa3A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7a_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1Sa3A2Li;S4bSa3A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7a_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S11fR1A1S4bSa3A1A3Li;S3aU0Sa3A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7a_0 : ltac2:(tb__ "0|0|
S0S3S6eSbdA1SbfA3"). Proof. vm_cast_no_check (@eq_refl _ (CS7a)). Qed.
Lemma MRG7a_0 : ltac2:(tb__ "0|0|
S0S21S139S18S146S2SbfA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7a_0 : ltac2:(tb__ "0|0|
S0S3S13aSbfU1A2S89A3"). Proof. vm_cast_no_check (@eq_refl _ (CM7a)). Qed.
Definition s7a : wsub := Eval vm_compute in (callsub CM7a Pre_memsetA).
Definition R7a : list sobj := Eval vm_compute in (callR CM7a Pre_memsetA s7a).
Definition T7a : axst := Eval vm_compute in (callT CM7a Pre_memsetA Pret_ms s7a R7a).
Lemma He7a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS89S3cSdbA3S2aG0Sc7A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7a)). Qed.
Lemma Hchk7a_0 : ltac2:(tb__ "0|0|
S0S21S11cS89S3cSdbSc7S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7a_0 : ltac2:(tb__ "0|0|
S0S3S11eSdbS3cS123S89Sc7A5Sd1A3"). Proof. vm_cast_no_check (@eq_refl _ (T7a)). Qed.
Lemma FBC7a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S89A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd1A1A1A1SfS2S89A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7a_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S89A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7a : axst := Eval vm_compute in (ax_with_facts T7a (ss_facts (ax_S CM7a))).
Lemma HD7a_0 : ltac2:(tb__ "0|0|
S0S3S11bSd1SfS2S89A1A1A2Sa7A3"). Proof. vm_cast_no_check (@eq_refl _ (D7a)). Qed.

Definition D7La : axst := Eval vm_compute in (rstS D7a [] (F_g8L nx0)).
Lemma WD7La_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8dA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD7La_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa7A1S2S8dA1A2S2aG3S29G1G2S22G0A1S12eS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8L nx0))). Qed.
Lemma NXD7La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8dA1A1SeS2Sa7A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7a))). Qed.
Lemma HD7La_0 : ltac2:(tb__ "0|0|
S0S3S5Sa7S2S8dA1A2S8dA3"). Proof. vm_cast_no_check (@eq_refl _ (D7La)). Qed.
Lemma FLOW7a_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa7A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U8a : axst := Eval vm_compute in (U8p nx0 D7La).
Lemma WU8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S99A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8dA1S2S99A1A2S2aG3S29G1G2S22G0A1S65S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S99A1A1SeS2S8dA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7La))). Qed.
Lemma HU8a_0 : ltac2:(tb__ "0|0|
S0S3S5S8dS2S99A1A2S99A3"). Proof. vm_cast_no_check (@eq_refl _ (U8a)). Qed.
Definition run8a : option (list leafA) := Eval vm_compute in (runT6 U8a).
Lemma run8a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3S99S22S3A1A3A4S23G0S107S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8a]). Qed.
Definition ET8a : axst := Eval vm_compute in (leafS 0 run8a).
Lemma Cert8a_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3S99S22S3A1M0A3S23S3Sb3G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8a] [ET8a] [run8a]); [exact run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8a : axst := Eval vm_compute in (CT8p nx0 ET8a).
Definition CO8a : axst := Eval vm_compute in (carveS CT8a (O_4 nx0)).
Lemma WC8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7fA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb3A1S2S7fA1A2S2aG3S29G1G2S22G0A1S6dS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7fA1A1SeS2Sb3A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8a))). Qed.
Lemma HC8a_0 : ltac2:(tb__ "0|0|
S0S3S5Sb3S2S7fA1A2S7fA3"). Proof. vm_cast_no_check (@eq_refl _ (CT8a)). Qed.
Lemma SK8a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7fA1A1A4S39SaG0S6fS26SaS23SaS4eS2fA1S23SaS4aS2fA1S23SaS122S2fA1S22SaA1A3A3A3S26SaS12bU2S2fA2Sb5A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXa))). Qed.
Lemma FC8a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8a_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S7fA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7fA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8a_0 : ltac2:(tb__ "0|0|
S0S3S124S7fS16S62S2fA1S11Z0A1S6cS2fA1S22SdA1S15A5A2S83A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8a)). Qed.
Lemma WCO8a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S83A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8a : wsub := Eval vm_compute in (callsub CO8a Pre_mszA).
Definition R8a : list sobj := Eval vm_compute in (callR CO8a Pre_mszA s8a).
Definition T8a : axst := Eval vm_compute in (callT CO8a Pre_mszA Pret_mz s8a R8a).
Lemma He8a_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS83S130SddA3S2aG0Sc9A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8a)). Qed.
Lemma Hchk8a_0 : ltac2:(tb__ "0|0|
S0S21S11cS83S130SddSc9S39S4S3S7S131A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8a_0 : ltac2:(tb__ "0|0|
S0S3S11eSddS130S127S83Sc9A5Sd3A3"). Proof. vm_cast_no_check (@eq_refl _ (T8a)). Qed.
Lemma FBC8a_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S83A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8a_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd3A1A1A1SfS2S83A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8a_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S83A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8a : axst := Eval vm_compute in (ax_with_facts T8a (ss_facts (ax_S CO8a))).
Lemma HD8a_0 : ltac2:(tb__ "0|0|
S0S3S11bSd3SfS2S83A1A1A2Sa9A3"). Proof. vm_cast_no_check (@eq_refl _ (D8a)). Qed.

Definition D8La : axst := Eval vm_compute in (rstS D8a [] (F_g9L nx0)).
Lemma WD8La_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8fA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD8La_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa9A1S2S8fA1A2S2aG3S29G1G2S22G0A1S12fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9L nx0))). Qed.
Lemma NXD8La_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8fA1A1SeS2Sa9A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8a))). Qed.
Lemma HD8La_0 : ltac2:(tb__ "0|0|
S0S3S5Sa9S2S8fA1A2S8fA3"). Proof. vm_cast_no_check (@eq_refl _ (D8La)). Qed.
Lemma FLOW8a_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa9A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U9a : axst := Eval vm_compute in (U9p nx0 D8La).
Lemma WU9a_0 : ltac2:(tb__ "0|0|
S0S21S10S2S9bA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9a_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8fA1S2S9bA1A2S2aG3S29G1G2S22G0A1S66S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9a_0 : ltac2:(tb__ "0|0|
S0S36SeS2S9bA1A1SeS2S8fA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8La))). Qed.
Lemma HU9a_0 : ltac2:(tb__ "0|0|
S0S3S5S8fS2S9bA1A2S9bA3"). Proof. vm_cast_no_check (@eq_refl _ (U9a)). Qed.
Definition run9a : option (list leafA) := Eval vm_compute in (runT9 U9a).
Lemma run9a__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS23S35S4fS22S35A1A3A3S23S3S9bS22S3A1A3A4S23G0S109S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9a]). Qed.
Definition E9fa : axst := Eval vm_compute in (leafS 0 run9a).
Definition E9pa : axst := Eval vm_compute in (leafS 1 run9a).
Lemma Cert9a_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS23S35S4fS22S35A1A3A3VGS0;S23S3S9bS22S3A1M0A3S23S3Se7S23S3S95G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [U9a] [E9fa; E9pa] [run9a]); [exact run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9a_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S95A1A1A4S39SaG0S6fS26SaS23SaS68S2fA1S23SaS4eS2fA1S23SaS4aS2fA1S23SaS122S2fA1S22SaA1A3A3A3A3S26SaS12bU2S2fA2Sb5A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXa))). Qed.
Lemma FC9a_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S95A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9a_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S95A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9a_0 : ltac2:(tb__ "0|0|
S30ScS17S47A1SfS2S95A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9a_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S95A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pa : axst := Eval vm_compute in (carveS E9pa (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9a_0 : ltac2:(tb__ "0|0|
S0S3S124S95S16S63S2fA1S11Z0A1S11Z1A1S22SdA1S15A5A2SadA3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pa)). Qed.
Lemma WCO9a_0 : ltac2:(tb__ "0|0|
S0S21S10S2SadA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qa : option (list leafA) := Eval vm_compute in (runT6 CO9pa).
Lemma run9qa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3SadS22S3A1A3A4S23G0S10bS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qa]). Qed.
Definition E9qa : axst := Eval vm_compute in (leafS 0 run9qa).
Lemma Cert9qa_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3SadS22S3A1M0A3S23S3Se9G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [CO9pa] [E9qa] [run9qa]); [exact run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fa)) 0).
Definition S9afa : axst := Eval vm_compute in (osplit E9fa iMfa (SLit 6144)).
Definition S9bfa : axst := Eval vm_compute in (osplit S9afa (S iMfa) (SLit 10240)).
Lemma HS9afa_0 : ltac2:(tb__ "0|0|
S0S3S49Se7Sf1S11Z1800A1A3SebA3"). Proof. vm_cast_no_check (@eq_refl _ (S9afa)). Qed.
Lemma HS9bfa_0 : ltac2:(tb__ "0|0|
S0S3S49SebS2eSf1A1S11Z2800A1A3S91A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfa)). Qed.
Definition s9fa : wsub := Eval vm_compute in (callsub S9bfa Pre_memsetA).
Definition R9fa : list sobj := Eval vm_compute in (callR S9bfa Pre_memsetA s9fa).
Definition T9fa : axst := Eval vm_compute in (callT S9bfa Pre_memsetA Pret_ms s9fa R9fa).
Lemma He9fa_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS91S3cSdfA3S2aG0ScbA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9fa)). Qed.
Lemma Hchk9fa_0 : ltac2:(tb__ "0|0|
S0S21S11cS91S3cSdfScbS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9fa_0 : ltac2:(tb__ "0|0|
S0S3S11eSdfS3cS123S91ScbA5Sd5A3"). Proof. vm_cast_no_check (@eq_refl _ (T9fa)). Qed.
Lemma FBC9fa_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S91A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9fa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd5A1A1A1SfS2S91A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9fa_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S91A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9fa : axst := Eval vm_compute in (ax_with_facts T9fa (ss_facts (ax_S S9bfa))).
Lemma HD9fa_0 : ltac2:(tb__ "0|0|
S0S3S11bSd5SfS2S91A1A1A2Sc1A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fa)). Qed.
Definition runFfa : option (list leafA) := Eval vm_compute in (runTF D9fa).
Lemma runFfa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S22S35A1S23S3Sc1S22S3A1A3A4S23G0S10dS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfa]). Qed.
Definition FFfa : axst := Eval vm_compute in (leafS 0 runFfa).
Lemma CertFfa_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S22S35A1VGS0;S23S3Sc1S22S3A1M0A3S23S3S73G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fa] [FFfa] [runFfa]); [exact runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfa : list cell := Eval vm_compute in (cells_at 5 FFfa).
Definition c1fa : list cell := Eval vm_compute in (cells_at 40 FFfa).
Definition c2fa : list cell := Eval vm_compute in (cells_at 41 FFfa).
Definition c4fa : list cell := Eval vm_compute in (cells_at 43 FFfa).
Definition c5fa : list cell := Eval vm_compute in (cells_at 47 FFfa).
Definition mcfa : list cell := Eval vm_compute in (cells_at 48 FFfa).
Definition xcfa : list cell := Eval vm_compute in (cells_at 50 FFfa).
Definition tybfa : Z := Eval vm_compute in (tyb_of mcfa).
Lemma SELFfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S12S2S73A1A1S42U2S2cA2A2S26SaS40VW;S85A2S26SaS137S50S2fS9dSf7SfbSffS77S111Z20000S19S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfa ++ RT_m1 ++ RSF nx0 c1fa c2fa c4fa c5fa mcfa xcfa 131072 DZero false)). Qed.
Lemma NDFfa_0 : ltac2:(tb__ "0|0|
S0S21S129S42U2S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS12S2S73A1A1A2A2Li;S42U2S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S11fR1A1S42U2S2cA2A3Li;S3aU0S2bSaS12S2S73A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfa_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S73A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfa_0 : ax_base FFfa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfa_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S73A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfa_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S73A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfa_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S2cS17S47A1S47X21x2SfS2S73A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fa_0 : ltac2:(tb__ "0|0|
S1S30SdS55S9dA3S1S30SdS51S9dA3S1S30SdS52S9dA3S1S30SdS56S9dA3S1S30SdS54S1aS142S14S134A1S11Z4000A1A3A1S9dA3S30SdS53S9dA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1fa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfa_0 : ltac2:(tb__ "0|0|
S1S30SdS5aS2fA1S77A3S1S30SdS5bS77A3S1S30SdS5cS77A3S1S30SdS58S77A3S1S30SdS59S77A3S1S30SdS57S2fA1S77A3S1S30SdS5fS77A3S1S30SdS60Sb7A1S77A3S1S30SdS5eS77A3S30SdS5dS77A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfa) mcfa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfa_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13dZ0Sb7A2S13eSb7Z100A2A2S13cS13fSb7Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfa_0 : In (xc_map nx0) xcfa. Proof. exact (In_of_cellb (xc_map nx0) xcfa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfa_0 : ltac2:(tb__ "0|0|
S0S21S10S12aS2S73A1S26SaS40VW;S85A2S23SaS46S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S26SaS40VW;S85A2S23SaS46S2fA1S22SaA1A3A3S43U2A1A2S41VW;S85S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfa nx0)). Qed.
Lemma NDUfa_0 : nodupN (idxsU 2%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS26SaS40VW;S85A2S23SaS46S2fA1S22SaA1A3A3A2A2Li;S43U2A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S11fR1A1S43U2A1A3Li;S3aU0S2bSaS26SaS40VW;S85A2S23SaS46S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fa_0 : ltac2:(tb__ "0|0|
S0S21S10S44S73S41VW;S85S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fa_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS12aS2S73A1S41VW;S85S2fA3M4A2S44S73G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S138A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fa_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S73A1A1S29SbSbS48S2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfa : wsub := Eval vm_compute in (infer_sub NF (S2F FFfa (KUB W swcfa nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9fa_0 : ltac2:(tb__ "0|0|
S0S21S8S45S73S41VW;S85S2fA3S2fA3S119S118VW;Vst;A3Se3A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fa_0 : ltac2:(tb__ "0|0|
S0S21S132Se3S136A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fa_0 : ltac2:(tb__ "0|0|
S0SbS133Se3S11aA2S48S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqa : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qa)) 0).
Definition S9aqa : axst := Eval vm_compute in (osplit E9qa iMqa (SLit 6144)).
Definition S9bqa : axst := Eval vm_compute in (osplit S9aqa (S iMqa) (SLit 10240)).
Lemma HS9aqa_0 : ltac2:(tb__ "0|0|
S0S3S49Se9Sf3S11Z1800A1A3SedA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqa)). Qed.
Lemma HS9bqa_0 : ltac2:(tb__ "0|0|
S0S3S49SedS2eSf3A1S11Z2800A1A3S93A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqa)). Qed.
Definition s9qa : wsub := Eval vm_compute in (callsub S9bqa Pre_memsetA).
Definition R9qa : list sobj := Eval vm_compute in (callR S9bqa Pre_memsetA s9qa).
Definition T9qa : axst := Eval vm_compute in (callT S9bqa Pre_memsetA Pret_ms s9qa R9qa).
Lemma He9qa_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS93S3cSe1A3S2aG0ScdA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9qa)). Qed.
Lemma Hchk9qa_0 : ltac2:(tb__ "0|0|
S0S21S11cS93S3cSe1ScdS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9qa_0 : ltac2:(tb__ "0|0|
S0S3S11eSe1S3cS123S93ScdA5Sd7A3"). Proof. vm_cast_no_check (@eq_refl _ (T9qa)). Qed.
Lemma FBC9qa_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S93A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9qa_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd7A1A1A1SfS2S93A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9qa_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S93A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qa : axst := Eval vm_compute in (ax_with_facts T9qa (ss_facts (ax_S S9bqa))).
Lemma HD9qa_0 : ltac2:(tb__ "0|0|
S0S3S11bSd7SfS2S93A1A1A2Sc3A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qa)). Qed.
Definition runFqa : option (list leafA) := Eval vm_compute in (runTF D9qa).
Lemma runFqa__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S22S35A1S23S3Sc3S22S3A1A3A4S23G0S10fS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqa]). Qed.
Definition FFqa : axst := Eval vm_compute in (leafS 0 runFqa).
Lemma CertFqa_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S22S35A1VGS0;S23S3Sc3S22S3A1M0A3S23S3S75G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qa] [FFqa] [runFqa]); [exact runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqa : list cell := Eval vm_compute in (cells_at 5 FFqa).
Definition c1qa : list cell := Eval vm_compute in (cells_at 40 FFqa).
Definition c2qa : list cell := Eval vm_compute in (cells_at 41 FFqa).
Definition c4qa : list cell := Eval vm_compute in (cells_at 43 FFqa).
Definition c5qa : list cell := Eval vm_compute in (cells_at 47 FFqa).
Definition mcqa : list cell := Eval vm_compute in (cells_at 48 FFqa).
Definition xcqa : list cell := Eval vm_compute in (cells_at 50 FFqa).
Definition tybqa : Z := Eval vm_compute in (tyb_of mcqa).
Lemma SELFqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S12S2S75A1A1S42U2S20A2A2S26SaS40VW;S87A2S26SaS137S50S2fS9fSf9SfdS101S79S113Z20000S19S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqa ++ RT_m1 ++ RSF nx0 c1qa c2qa c4qa c5qa mcqa xcqa 131072 DZero true)). Qed.
Lemma NDFqa_0 : ltac2:(tb__ "0|0|
S0S21S129S42U2S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS12S2S75A1A1A2A2Li;S42U2S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S11fR1A1S42U2S20A2A3Li;S3aU0S2bSaS12S2S75A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqa_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S75A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqa_0 : ax_base FFqa = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqa_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S75A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqa_0 : ltac2:(tb__ "0|0|
S32ScSa1SfS2S75A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqa_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S20S17S47A1S47X21x2SfS2S75A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qa_0 : ltac2:(tb__ "0|0|
S1S30SdS55S9fA3S1S30SdS51S9fA3S1S30SdS52S9fA3S1S30SdS56S9fA3S1S30SdS54S1aS142S14S134A1S11Z4000A1A3A1S9fA3S30SdS53S9fA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) c1qa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qa ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqa_0 : ltac2:(tb__ "0|0|
S1S30SdS5aS2fA1S79A3S1S30SdS5bS79A3S1S30SdS5cS79A3S1S30SdS58S79A3S1S30SdS59S79A3S1S30SdS57S2fA1S79A3S1S30SdS5fS79A3S1S30SdS60Sb9A1S79A3S1S30SdS5eS79A3S30SdS5dS79A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqa) mcqa ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqa ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqa ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqa_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13dZ0Sb9A2S13eSb9Z100A2A2S13cS13fSb9Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqa_0 : In (xc_map nx0) xcqa. Proof. exact (In_of_cellb (xc_map nx0) xcqa ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqa_0 : ltac2:(tb__ "0|0|
S0S21S10S12aS2S75A1S26SaS40VW;S87A2S23SaS46S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqa_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S26SaS40VW;S87A2S23SaS46S2fA1S22SaA1A3A3S43U2A1A2S41VW;S87S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqa nx0)). Qed.
Lemma NDUqa_0 : nodupN (idxsU 2%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS26SaS40VW;S87A2S23SaS46S2fA1S22SaA1A3A3A2A2Li;S43U2A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqa_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S11fR1A1S43U2A1A3Li;S3aU0S2bSaS26SaS40VW;S87A2S23SaS46S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qa_0 : ltac2:(tb__ "0|0|
S0S21S10S44S75S41VW;S87S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qa_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS12aS2S75A1S41VW;S87S2fA3M4A2S44S75G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S138A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qa_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S75A1A1S29SbSbS48S2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqa : wsub := Eval vm_compute in (infer_sub NF (S2F FFqa (KUB W swcqa nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9qa_0 : ltac2:(tb__ "0|0|
S0S21S8S45S75S41VW;S87S2fA3S2fA3S119S118VW;Vst;A3Se5A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qa_0 : ltac2:(tb__ "0|0|
S0S21S132Se5S136A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qa_0 : ltac2:(tb__ "0|0|
S0SbS133Se5S11aA2S48S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition PXb : list sobj := [O_w].
Definition FXPb : list sprop := ltac2:(tb__ "0|0|
S23ScS17S1bS143S14S135A1S14S134A1A3A1S22ScA1A3").

Definition C5Ab : axst := Eval vm_compute in (ax_add_facts (F_A nx0) C5bc).
Lemma HC5Ab_0 : ltac2:(tb__ "0|0|
S0S3S71S4cS2fA1S141A2SbcA3"). Proof. vm_cast_no_check (@eq_refl _ (C5Ab)). Qed.
Lemma FBAb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2S141A1A1A1S4cS2fA1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FLOWb_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2S141A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition run6Ab : option (list leafA) := Eval vm_compute in (runT6 C5Ab).
Lemma run6Ab__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3SbcS22S3A1A3A4S23G0S104S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run6Ab]). Qed.
Definition Y6Ab : axst := Eval vm_compute in (leafS 0 run6Ab).
Lemma Cert6Ab_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3SbcS22S3A1M0A3S23S3Sf0G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [C5Ab] [Y6Ab] [run6Ab]); [exact run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition E6b : axst := Eval vm_compute in (rmF (F_A nx0) Y6Ab).
Definition s6Ab : wsub := Eval vm_compute in (infer_sub GS0 (ax_S Y6Ab) (ax_S E6b)).
Lemma E6Ab_0 : ltac2:(tb__ "0|0|
S0S21S8Sf0Sb0Sf6A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma I6Ab_0 : ltac2:(tb__ "0|0|
S0S21S132Sf6VGS0;A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition CT6b : axst := Eval vm_compute in (rstS E6b ru6 []).
Definition CO6b : axst := Eval vm_compute in (carveS CT6b (O_3 nx0)).
Lemma WC6b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7cA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF6b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb0A1S2S7cA1A2S2aG3S29G1G2S23G0S29SbSbS6aS2fA1S4dA4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a2e6 nx0, L3)], @nil sprop))). Qed.
Lemma NX6b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7cA1A1SeS2Sb0A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S E6b))). Qed.
Lemma HC6b_0 : ltac2:(tb__ "0|0|
S0S3S5Sb0S2S7cA1A2S7cA3"). Proof. vm_cast_no_check (@eq_refl _ (CT6b)). Qed.
Lemma SK6b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7cA1A1A4S39SaG0S6fS26SaS23SaS126S2fA1S23SaS122S2fA1S22SaA1A3A3S26SaS12bU2S2fA2Sb6A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_2 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXb))). Qed.
Lemma FC6b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX6b_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S7cA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC6b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7cA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO6b_0 : ltac2:(tb__ "0|0|
S0S3S124S7cS16S61S2fA1S11Z0A1S4dS22SdA1S15A5A2S82A3"). Proof. vm_cast_no_check (@eq_refl _ (CO6b)). Qed.
Lemma WCO6b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S82A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s6b : wsub := Eval vm_compute in (callsub CO6b Pre_memsetA).
Definition R6b : list sobj := Eval vm_compute in (callR CO6b Pre_memsetA s6b).
Definition T6b : axst := Eval vm_compute in (callT CO6b Pre_memsetA Pret_ms s6b R6b).
Lemma He6b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS82S3cSdaA3S2aG0Sc6A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R6b)). Qed.
Lemma Hchk6b_0 : ltac2:(tb__ "0|0|
S0S21S11cS82S3cSdaSc6S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT6b_0 : ltac2:(tb__ "0|0|
S0S3S11eSdaS3cS123S82Sc6A5Sd0A3"). Proof. vm_cast_no_check (@eq_refl _ (T6b)). Qed.
Lemma FBC6b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S82A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT6b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd0A1A1A1SfS2S82A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC6b_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S82A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D6b : axst := Eval vm_compute in (ax_with_facts T6b (ss_facts (ax_S CO6b))).
Lemma HD6b_0 : ltac2:(tb__ "0|0|
S0S3S11bSd0SfS2S82A1A1A2Sa6A3"). Proof. vm_cast_no_check (@eq_refl _ (D6b)). Qed.

Definition D6Lb : axst := Eval vm_compute in (rstS D6b [] (F_g7L nx0)).
Lemma WD6Lb_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8cA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD6Lb_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa6A1S2S8cA1A2S2aG3S29G1G2S22G0A1S12dS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7L nx0))). Qed.
Lemma NXD6Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8cA1A1SeS2Sa6A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6b))). Qed.
Lemma HD6Lb_0 : ltac2:(tb__ "0|0|
S0S3S5Sa6S2S8cA1A2S8cA3"). Proof. vm_cast_no_check (@eq_refl _ (D6Lb)). Qed.
Lemma FLOW6b_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa6A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U7b : axst := Eval vm_compute in (U7p nx0 D6Lb).
Lemma WU7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S98A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU7b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8cA1S2S98A1A2S2aG3S29G1G2S22G0A1S64S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g7 nx0))). Qed.
Lemma NXU7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S98A1A1SeS2S8cA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D6Lb))). Qed.
Lemma HU7b_0 : ltac2:(tb__ "0|0|
S0S3S5S8cS2S98A1A2S98A3"). Proof. vm_cast_no_check (@eq_refl _ (U7b)). Qed.
Definition run7b : option (list leafA) := Eval vm_compute in (runT6 U7b).
Lemma run7b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3S98S22S3A1A3A4S23G0S106S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run7b]). Qed.
Definition ET7b : axst := Eval vm_compute in (leafS 0 run7b).
Lemma Cert7b_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3S98S22S3A1M0A3S23S3Sb2G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U7b] [ET7b] [run7b]); [exact run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT7b : axst := Eval vm_compute in (rstS ET7b (ru7 nx0) []).
Definition CO7b : axst := Eval vm_compute in (carveS CT7b (O_3n nx0)).
Definition CR7b : axst := Eval vm_compute in (DepotCall.oreb CO7b 1).
Definition n7b : nat := Eval vm_compute in (length (ss_objs (ax_S CR7b))).
Definition CS7b : axst := Eval vm_compute in (sel7 CR7b).
Definition CM7b : axst := Eval vm_compute in (DepotCall.omrg CS7b 1).
Lemma WC7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S7eA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF7b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb2A1S2S7eA1A2S2aG3S29G1G2S23G0S29SbSbS69S2fA1S125S2fA1A4S23G0S29SbSbS6bS2fA1S67A4S22G0A1A3A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(a0e7 nx0, BR nx0); (a2e7 nx0, L3b)], @nil sprop))). Qed.
Lemma NX7b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S7eA1A1SeS2Sb2A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET7b))). Qed.
Lemma HC7b_0 : ltac2:(tb__ "0|0|
S0S3S5Sb2S2S7eA1A2S7eA3"). Proof. vm_cast_no_check (@eq_refl _ (CT7b)). Qed.
Lemma SK7b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S7eA1A1A4S39SaG0S6fS26SaS23SaS4aS2fA1S23SaS126S2fA1S23SaS122S2fA1S22SaA1A3A3A3S26SaS12bU2S2fA2Sb6A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3 nx0; O_2 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXb))). Qed.
Lemma FC7b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX7b_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S7eA1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC7b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S7eA1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO7b_0 : ltac2:(tb__ "0|0|
S0S3S124S7eS16S125S2fA1S11Z0A1S11Z100A1S22SdA1S15A5A2SacA3"). Proof. vm_cast_no_check (@eq_refl _ (CO7b)). Qed.
Lemma WCO7b_0 : ltac2:(tb__ "0|0|
S0S21S10S2SacA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma RB7b_0 : ltac2:(tb__ "0|0|
S0S21S139S18S147S2SacA1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCR7b_0 : ltac2:(tb__ "0|0|
S0S3S13bSacU1A2SbeA3"). Proof. vm_cast_no_check (@eq_refl _ (CR7b)). Qed.
Lemma LEN7b_0 : ltac2:(tb__ "0|0|
S0S27S2bSaS12S2SbeA1A1A2Sa4A3"). Proof. vm_cast_no_check (@eq_refl _ (n7b)). Qed.
Lemma PERM_nd7b_0 : ltac2:(tb__ "0|0|
S0S21S129S4bSa4A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_lt7b_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1Sa4A2Li;S4bSa4A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma PERM_cov7b_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S11fR1A1S4bSa4A1A3Li;S3aU0Sa4A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCS7b_0 : ltac2:(tb__ "0|0|
S0S3S6eSbeA1Sc0A3"). Proof. vm_cast_no_check (@eq_refl _ (CS7b)). Qed.
Lemma MRG7b_0 : ltac2:(tb__ "0|0|
S0S21S139S18S146S2Sc0A1U1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HCM7b_0 : ltac2:(tb__ "0|0|
S0S3S13aSc0U1A2S8aA3"). Proof. vm_cast_no_check (@eq_refl _ (CM7b)). Qed.
Definition s7b : wsub := Eval vm_compute in (callsub CM7b Pre_memsetA).
Definition R7b : list sobj := Eval vm_compute in (callR CM7b Pre_memsetA s7b).
Definition T7b : axst := Eval vm_compute in (callT CM7b Pre_memsetA Pret_ms s7b R7b).
Lemma He7b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS8aS3cSdcA3S2aG0Sc8A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R7b)). Qed.
Lemma Hchk7b_0 : ltac2:(tb__ "0|0|
S0S21S11cS8aS3cSdcSc8S39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT7b_0 : ltac2:(tb__ "0|0|
S0S3S11eSdcS3cS123S8aSc8A5Sd2A3"). Proof. vm_cast_no_check (@eq_refl _ (T7b)). Qed.
Lemma FBC7b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S8aA1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT7b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd2A1A1A1SfS2S8aA1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC7b_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S8aA1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D7b : axst := Eval vm_compute in (ax_with_facts T7b (ss_facts (ax_S CM7b))).
Lemma HD7b_0 : ltac2:(tb__ "0|0|
S0S3S11bSd2SfS2S8aA1A1A2Sa8A3"). Proof. vm_cast_no_check (@eq_refl _ (D7b)). Qed.

Definition D7Lb : axst := Eval vm_compute in (rstS D7b [] (F_g8L nx0)).
Lemma WD7Lb_0 : ltac2:(tb__ "0|0|
S0S21S10S2S8eA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD7Lb_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sa8A1S2S8eA1A2S2aG3S29G1G2S22G0A1S12eS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8L nx0))). Qed.
Lemma NXD7Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S8eA1A1SeS2Sa8A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7b))). Qed.
Lemma HD7Lb_0 : ltac2:(tb__ "0|0|
S0S3S5Sa8S2S8eA1A2S8eA3"). Proof. vm_cast_no_check (@eq_refl _ (D7Lb)). Qed.
Lemma FLOW7b_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2Sa8A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U8b : axst := Eval vm_compute in (U8p nx0 D7Lb).
Lemma WU8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S9aA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU8b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S8eA1S2S9aA1A2S2aG3S29G1G2S22G0A1S65S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g8 nx0))). Qed.
Lemma NXU8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S9aA1A1SeS2S8eA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D7Lb))). Qed.
Lemma HU8b_0 : ltac2:(tb__ "0|0|
S0S3S5S8eS2S9aA1A2S9aA3"). Proof. vm_cast_no_check (@eq_refl _ (U8b)). Qed.
Definition run8b : option (list leafA) := Eval vm_compute in (runT6 U8b).
Lemma run8b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3S9aS22S3A1A3A4S23G0S108S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run8b]). Qed.
Definition ET8b : axst := Eval vm_compute in (leafS 0 run8b).
Lemma Cert8b_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3S9aS22S3A1M0A3S23S3Sb4G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [U8b] [ET8b] [run8b]); [exact run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition CT8b : axst := Eval vm_compute in (CT8p nx0 ET8b).
Definition CO8b : axst := Eval vm_compute in (carveS CT8b (O_4 nx0)).
Lemma WC8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S80A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DF8b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2Sb4A1S2S80A1A2S2aG3S29G1G2S22G0A1S6dS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), fx8 nx0))). Qed.
Lemma NX8b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S80A1A1SeS2Sb4A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S ET8b))). Qed.
Lemma HC8b_0 : ltac2:(tb__ "0|0|
S0S3S5Sb4S2S80A1A2S80A3"). Proof. vm_cast_no_check (@eq_refl _ (CT8b)). Qed.
Lemma SK8b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S80A1A1A4S39SaG0S6fS26SaS23SaS4eS2fA1S23SaS4aS2fA1S23SaS122S2fA1S22SaA1A3A3A3S26SaS12bU2S2fA2Sb6A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXb))). Qed.
Lemma FC8b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX8b_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S80A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma XC8b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S80A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma HCO8b_0 : ltac2:(tb__ "0|0|
S0S3S124S80S16S62S2fA1S11Z0A1S6cS2fA1S22SdA1S15A5A2S84A3"). Proof. vm_cast_no_check (@eq_refl _ (CO8b)). Qed.
Lemma WCO8b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S84A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition s8b : wsub := Eval vm_compute in (callsub CO8b Pre_mszA).
Definition R8b : list sobj := Eval vm_compute in (callR CO8b Pre_mszA s8b).
Definition T8b : axst := Eval vm_compute in (callT CO8b Pre_mszA Pret_mz s8b R8b).
Lemma He8b_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS84S130SdeA3S2aG0ScaA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R8b)). Qed.
Lemma Hchk8b_0 : ltac2:(tb__ "0|0|
S0S21S11cS84S130SdeScaS39S4S3S7S131A4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT8b_0 : ltac2:(tb__ "0|0|
S0S3S11eSdeS130S127S84ScaA5Sd4A3"). Proof. vm_cast_no_check (@eq_refl _ (T8b)). Qed.
Lemma FBC8b_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S84A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT8b_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd4A1A1A1SfS2S84A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC8b_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S84A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D8b : axst := Eval vm_compute in (ax_with_facts T8b (ss_facts (ax_S CO8b))).
Lemma HD8b_0 : ltac2:(tb__ "0|0|
S0S3S11bSd4SfS2S84A1A1A2SaaA3"). Proof. vm_cast_no_check (@eq_refl _ (D8b)). Qed.

Definition D8Lb : axst := Eval vm_compute in (rstS D8b [] (F_g9L nx0)).
Lemma WD8Lb_0 : ltac2:(tb__ "0|0|
S0S21S10S2S90A1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DD8Lb_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2SaaA1S2S90A1A2S2aG3S29G1G2S22G0A1S12fS2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9L nx0))). Qed.
Lemma NXD8Lb_0 : ltac2:(tb__ "0|0|
S0S36SeS2S90A1A1SeS2SaaA1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8b))). Qed.
Lemma HD8Lb_0 : ltac2:(tb__ "0|0|
S0S3S5SaaS2S90A1A2S90A3"). Proof. vm_cast_no_check (@eq_refl _ (D8Lb)). Qed.
Lemma FLOW8b_0 : ltac2:(tb__ "0|0|
S30ScS12cS2fA1SfS2SaaA1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Definition U9b : axst := Eval vm_compute in (U9p nx0 D8Lb).
Lemma WU9b_0 : ltac2:(tb__ "0|0|
S0S21S10S2S9cA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma DU9b_0 : ltac2:(tb__ "0|4|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS2S90A1S2S9cA1A2S2aG3S29G1G2S22G0A1S66S2fA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some (@nil (sv * sv), F_g9 nx0))). Qed.
Lemma NXU9b_0 : ltac2:(tb__ "0|0|
S0S36SeS2S9cA1A1SeS2S90A1A1A3"). Proof. vm_cast_no_check (@eq_refl _ (ss_next (ax_S D8Lb))). Qed.
Lemma HU9b_0 : ltac2:(tb__ "0|0|
S0S3S5S90S2S9cA1A2S9cA3"). Proof. vm_cast_no_check (@eq_refl _ (U9b)). Qed.
Definition run9b : option (list leafA) := Eval vm_compute in (runT9 U9b).
Lemma run9b__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS23S35S4fS22S35A1A3A3S23S3S9cS22S3A1A3A4S23G0S10aS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9b]). Qed.
Definition E9fb : axst := Eval vm_compute in (leafS 0 run9b).
Definition E9pb : axst := Eval vm_compute in (leafS 1 run9b).
Lemma Cert9b_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS23S35S4fS22S35A1A3A3VGS0;S23S3S9cS22S3A1M0A3S23S3Se8S23S3S96G0A3A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [U9b] [E9fb; E9pb] [run9b]); [exact run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma SK9b_0 : ltac2:(tb__ "0|1|
S0S24S25S25SbSbA2SbA2M0A1S39SaG0S6fS12S2S96A1A1A4S39SaG0S6fS26SaS23SaS68S2fA1S23SaS4eS2fA1S23SaS4aS2fA1S23SaS122S2fA1S22SaA1A3A3A3A3S26SaS12bU2S2fA2Sb6A3A3A4A3"). Proof. vm_cast_no_check (@eq_refl _ (map skel ([O_4z nx0; O_3b nx0; O_3 nx0; O_1 nx0] ++ SKEL0 2%nat nx0 ++ PXb))). Qed.
Lemma FC9b_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S96A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FX9b_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S96A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FP9b_0 : ltac2:(tb__ "0|0|
S30ScS17S47A1SfS2S96A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma XC9b_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S96A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Definition CO9pb : axst := Eval vm_compute in (carveS E9pb (mkObj (BP9 nx0) (SLit 0) (SLit 1) [] DUnknown)).
Lemma HCO9b_0 : ltac2:(tb__ "0|0|
S0S3S124S96S16S63S2fA1S11Z0A1S11Z1A1S22SdA1S15A5A2SaeA3"). Proof. vm_cast_no_check (@eq_refl _ (CO9pb)). Qed.
Lemma WCO9b_0 : ltac2:(tb__ "0|0|
S0S21S10S2SaeA1A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition run9qb : option (list leafA) := Eval vm_compute in (runT6 CO9pb).
Lemma run9qb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S23S35S3fS22S35A1A3S23S3SaeS22S3A1A3A4S23G0S10cS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [run9qb]). Qed.
Definition E9qb : axst := Eval vm_compute in (leafS 0 run9qb).
Lemma Cert9qb_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S23S35S3fS22S35A1A3VGS0;S23S3SaeS22S3A1M0A3S23S3SeaG0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [MSENT] GS0 [CO9pb] [E9qb] [run9qb]); [exact run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Definition iMfb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9fb)) 0).
Definition S9afb : axst := Eval vm_compute in (osplit E9fb iMfb (SLit 6144)).
Definition S9bfb : axst := Eval vm_compute in (osplit S9afb (S iMfb) (SLit 10240)).
Lemma HS9afb_0 : ltac2:(tb__ "0|0|
S0S3S49Se8Sf2S11Z1800A1A3SecA3"). Proof. vm_cast_no_check (@eq_refl _ (S9afb)). Qed.
Lemma HS9bfb_0 : ltac2:(tb__ "0|0|
S0S3S49SecS2eSf2A1S11Z2800A1A3S92A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bfb)). Qed.
Definition s9fb : wsub := Eval vm_compute in (callsub S9bfb Pre_memsetA).
Definition R9fb : list sobj := Eval vm_compute in (callR S9bfb Pre_memsetA s9fb).
Definition T9fb : axst := Eval vm_compute in (callT S9bfb Pre_memsetA Pret_ms s9fb R9fb).
Lemma He9fb_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS92S3cSe0A3S2aG0SccA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9fb)). Qed.
Lemma Hchk9fb_0 : ltac2:(tb__ "0|0|
S0S21S11cS92S3cSe0SccS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9fb_0 : ltac2:(tb__ "0|0|
S0S3S11eSe0S3cS123S92SccA5Sd6A3"). Proof. vm_cast_no_check (@eq_refl _ (T9fb)). Qed.
Lemma FBC9fb_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S92A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9fb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd6A1A1A1SfS2S92A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9fb_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S92A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9fb : axst := Eval vm_compute in (ax_with_facts T9fb (ss_facts (ax_S S9bfb))).
Lemma HD9fb_0 : ltac2:(tb__ "0|0|
S0S3S11bSd6SfS2S92A1A1A2Sc2A3"). Proof. vm_cast_no_check (@eq_refl _ (D9fb)). Qed.
Definition runFfb : option (list leafA) := Eval vm_compute in (runTF D9fb).
Lemma runFfb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S22S35A1S23S3Sc2S22S3A1A3A4S23G0S10eS22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFfb]). Qed.
Definition FFfb : axst := Eval vm_compute in (leafS 0 runFfb).
Lemma CertFfb_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S22S35A1VGS0;S23S3Sc2S22S3A1M0A3S23S3S74G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9fb] [FFfb] [runFfb]); [exact runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcfb : list cell := Eval vm_compute in (cells_at 5 FFfb).
Definition c1fb : list cell := Eval vm_compute in (cells_at 40 FFfb).
Definition c2fb : list cell := Eval vm_compute in (cells_at 41 FFfb).
Definition c4fb : list cell := Eval vm_compute in (cells_at 43 FFfb).
Definition c5fb : list cell := Eval vm_compute in (cells_at 47 FFfb).
Definition mcfb : list cell := Eval vm_compute in (cells_at 48 FFfb).
Definition xcfb : list cell := Eval vm_compute in (cells_at 50 FFfb).
Definition tybfb : Z := Eval vm_compute in (tyb_of mcfb).
Lemma SELFfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S12S2S74A1A1S42U2S2cA2A2S26SaS40VW;S86A2S26SaS137S50S2fS9eSf8SfcS100S78S112Z8S15S2cAaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcfb ++ RT_m1 ++ RSF nx0 c1fb c2fb c4fb c5fb mcfb xcfb 8 DUnknown false)). Qed.
Lemma NDFfb_0 : ltac2:(tb__ "0|0|
S0S21S129S42U2S2cA2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS12S2S74A1A1A2A2Li;S42U2S2cA2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S11fR1A1S42U2S2cA2A3Li;S3aU0S2bSaS12S2S74A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnfb_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S74A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbfb_0 : ax_base FFfb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFfb_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFfb_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S74A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARfb_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S2cS17S47A1S47X21x2SfS2S74A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1fb_0 : ltac2:(tb__ "0|0|
S1S30SdS55S9eA3S1S30SdS51S9eA3S1S30SdS52S9eA3S1S30SdS56S9eA3S1S30SdS54S14S134A1A1S9eA3S30SdS53S9eA3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1fb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1fb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1fb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcfb_0 : ltac2:(tb__ "0|0|
S1S30SdS5aS2fA1S78A3S1S30SdS5bS78A3S1S30SdS5cS78A3S1S30SdS58S78A3S1S30SdS59S78A3S1S30SdS57S2fA1S78A3S1S30SdS5fS78A3S1S30SdS60Sb8A1S78A3S1S30SdS5eS78A3S30SdS5dS78A3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybfb) mcfb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcfb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcfb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybfb_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13dZ0Sb8A2S13eSb8Z100A2A2S13cS13fSb8Z4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcfb_0 : In (xc_map nx0) xcfb. Proof. exact (In_of_cellb (xc_map nx0) xcfb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUfb_0 : ltac2:(tb__ "0|0|
S0S21S10S12aS2S74A1S26SaS40VW;S86A2S23SaS46S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUfb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S26SaS40VW;S86A2S23SaS46S2fA1S22SaA1A3A3S43U2A1A2S41VW;S86S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcfb nx0)). Qed.
Lemma NDUfb_0 : nodupN (idxsU 2%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS26SaS40VW;S86A2S23SaS46S2fA1S22SaA1A3A3A2A2Li;S43U2A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUfb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S11fR1A1S43U2A1A3Li;S3aU0S2bSaS26SaS40VW;S86A2S23SaS46S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9fb_0 : ltac2:(tb__ "0|0|
S0S21S10S44S74S41VW;S86S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9fb_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS12aS2S74A1S41VW;S86S2fA3M4A2S44S74G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S138A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9fb_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S74A1A1S29SbSbS48S2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFfb : wsub := Eval vm_compute in (infer_sub NF (S2F FFfb (KUB W swcfb nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9fb_0 : ltac2:(tb__ "0|0|
S0S21S8S45S74S41VW;S86S2fA3S2fA3S119S118VW;Vst;A3Se4A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9fb_0 : ltac2:(tb__ "0|0|
S0S21S132Se4S136A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110fb_0 : ltac2:(tb__ "0|0|
S0SbS133Se4S11aA2S48S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.

Definition iMqb : nat := Eval vm_compute in (find_map nx0 (ss_objs (ax_S E9qb)) 0).
Definition S9aqb : axst := Eval vm_compute in (osplit E9qb iMqb (SLit 6144)).
Definition S9bqb : axst := Eval vm_compute in (osplit S9aqb (S iMqb) (SLit 10240)).
Lemma HS9aqb_0 : ltac2:(tb__ "0|0|
S0S3S49SeaSf4S11Z1800A1A3SeeA3"). Proof. vm_cast_no_check (@eq_refl _ (S9aqb)). Qed.
Lemma HS9bqb_0 : ltac2:(tb__ "0|0|
S0S3S49SeeS2eSf4A1S11Z2800A1A3S94A3"). Proof. vm_cast_no_check (@eq_refl _ (S9bqb)). Qed.
Definition s9qb : wsub := Eval vm_compute in (callsub S9bqb Pre_memsetA).
Definition R9qb : list sobj := Eval vm_compute in (callR S9bqb Pre_memsetA s9qb).
Definition T9qb : axst := Eval vm_compute in (callT S9bqb Pre_memsetA Pret_ms s9qb R9qb).
Lemma He9qb_0 : ltac2:(tb__ "0|1|
S0S28S24SaA1M0A1S11dS94S3cSe2A3S2aG0SceA2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some R9qb)). Qed.
Lemma Hchk9qb_0 : ltac2:(tb__ "0|0|
S0S21S11cS94S3cSe2SceS39S4S3S7S3dA4A5S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HT9qb_0 : ltac2:(tb__ "0|0|
S0S3S11eSe2S3cS123S94SceA5Sd8A3"). Proof. vm_cast_no_check (@eq_refl _ (T9qb)). Qed.
Lemma FBC9qb_0 : ltac2:(tb__ "0|1|
S0S21S31ScS13SeS2S94A1M0A1A1SfG0A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBT9qb_0 : ltac2:(tb__ "0|0|
S0S21S31ScS13SeS2Sd8A1A1A1SfS2S94A1A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXC9qb_0 : ltac2:(tb__ "0|0|
S0S21S121VGS0;SeS2S94A1A1A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition D9qb : axst := Eval vm_compute in (ax_with_facts T9qb (ss_facts (ax_S S9bqb))).
Lemma HD9qb_0 : ltac2:(tb__ "0|0|
S0S3S11bSd8SfS2S94A1A1A2Sc4A3"). Proof. vm_cast_no_check (@eq_refl _ (D9qb)). Qed.
Definition runFqb : option (list leafA) := Eval vm_compute in (runTF D9qb).
Lemma runFqb__runeq : ltac2:(tb__ "0|1|
S0S24S28S24S4A1A1M0A1S72S38Ufa0S22S35A1S23S3Sc4S22S3A1A3A4S23G0S110S22G0A1A3A3"). Proof. vm_cast_no_check (@eq_refl (list (option (list leafA))) [runFqb]). Qed.
Definition FFqb : axst := Eval vm_compute in (leafS 0 runFqb).
Lemma CertFqb_0 : ltac2:(tb__ "0|1|
S0S21S70S38Ufa0S22S35A1VGS0;S23S3Sc4S22S3A1M0A3S23S3S76G0A3A6S20A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 4000%nat [] GS0 [D9qb] [FFqb] [runFqb]); [exact runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Definition swcqb : list cell := Eval vm_compute in (cells_at 5 FFqb).
Definition c1qb : list cell := Eval vm_compute in (cells_at 40 FFqb).
Definition c2qb : list cell := Eval vm_compute in (cells_at 41 FFqb).
Definition c4qb : list cell := Eval vm_compute in (cells_at 43 FFqb).
Definition c5qb : list cell := Eval vm_compute in (cells_at 47 FFqb).
Definition mcqb : list cell := Eval vm_compute in (cells_at 48 FFqb).
Definition xcqb : list cell := Eval vm_compute in (cells_at 50 FFqb).
Definition tybqb : Z := Eval vm_compute in (tyb_of mcqb).
Lemma SELFqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S12S2S76A1A1S42U2S20A2A2S26SaS40VW;S88A2S26SaS137S50S2fSa0SfaSfeS102S7aS114Z8S15S20AaA3A3A3"). Proof. vm_cast_no_check (@eq_refl _ (KEPTF W swcqb ++ RT_m1 ++ RSF nx0 c1qb c2qb c4qb c5qb mcqb xcqb 8 DUnknown true)). Qed.
Lemma NDFqb_0 : ltac2:(tb__ "0|0|
S0S21S129S42U2S20A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDFqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS12S2S76A1A1A2A2Li;S42U2S20A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVFqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S11fR1A1S42U2S20A2A3Li;S3aU0S2bSaS12S2S76A1A1A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XFnqb_0 : ltac2:(tb__ "0|1|
S0S24S25SbSbA2M0A1S6S76A1S22G0A1A3"). Proof. vm_cast_no_check (@eq_refl _ (@nil (sv * sv))). Qed.
Lemma BFbqb_0 : ax_base FFqb = base_sv. Proof. vm_cast_no_check (@eq_refl _ (base_sv)). Qed.
Lemma FPFqb_0 : ltac2:(tb__ "0|0|
S32ScS26ScS117VW;Vst;A2S116S115A1A3SfS2S76A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FXFqb_0 : ltac2:(tb__ "0|0|
S32ScSa2SfS2S76A1A1A3"). Proof. apply inclb_incl. vm_cast_no_check (eq_refl true). Qed.
Lemma FPARqb_0 : ltac2:(tb__ "0|0|
S30ScS21ScL_;S20S17S47A1S47X21x2SfS2S76A1A1A3"). Proof. apply In_of_inclb. vm_cast_no_check (eq_refl true). Qed.
Lemma Hc1qb_0 : ltac2:(tb__ "0|0|
S1S30SdS55Sa0A3S1S30SdS51Sa0A3S1S30SdS52Sa0A3S1S30SdS56Sa0A3S1S30SdS54S14S134A1A1Sa0A3S30SdS53Sa0A3A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (ic_pg) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c1) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_c2) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_rs) c1qb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (ic_nres (SVar V_NRES)) c1qb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (ic_nch) c1qb ltac:(vm_cast_no_check (eq_refl true)))))))). Qed.
Lemma Hmcqb_0 : ltac2:(tb__ "0|0|
S1S30SdS5aS2fA1S7aA3S1S30SdS5bS7aA3S1S30SdS5cS7aA3S1S30SdS58S7aA3S1S30SdS59S7aA3S1S30SdS57S2fA1S7aA3S1S30SdS5fS7aA3S1S30SdS60SbaA1S7aA3S1S30SdS5eS7aA3S30SdS5dS7aA3A2A2A2A2A2A2A2A2A2").
Proof. exact (conj (In_of_cellb (mc_map nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ms) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_ns) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_idx) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_magic) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_cptr nx0) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_state) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_type tybqb) mcqb ltac:(vm_cast_no_check (eq_refl true))) (conj (In_of_cellb (mc_sizehi) mcqb ltac:(vm_cast_no_check (eq_refl true))) (In_of_cellb (mc_size) mcqb ltac:(vm_cast_no_check (eq_refl true)))))))))))). Qed.
Lemma Htybqb_0 : ltac2:(tb__ "0|0|
S0S21S2dS2dS13dZ0SbaA2S13eSbaZ100A2A2S13cS13fSbaZ4A2Z1A2A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Hxcqb_0 : In (xc_map nx0) xcqb. Proof. exact (In_of_cellb (xc_map nx0) xcqb ltac:(vm_cast_no_check (eq_refl true))). Qed.
Lemma WCUqb_0 : ltac2:(tb__ "0|0|
S0S21S10S12aS2S76A1S26SaS40VW;S88A2S23SaS46S2fA1S22SaA1A3A3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SELUqb_0 : ltac2:(tb__ "0|0|
S0S24SaA1S128S26SaS40VW;S88A2S23SaS46S2fA1S22SaA1A3A3S43U2A1A2S41VW;S88S2fA3A3"). Proof. vm_cast_no_check (@eq_refl _ (KUB W swcqb nx0)). Qed.
Lemma NDUqb_0 : nodupN (idxsU 2%nat) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma BNDUqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S120R1S2bSaS26SaS40VW;S88A2S23SaS46S2fA1S22SaA1A3A3A2A2Li;S43U2A1A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma COVUqb_0 : ltac2:(tb__ "0|0|
S0S21S31S27S27S33S27S11fR1A1S43U2A1A3Li;S3aU0S2bSaS26SaS40VW;S88A2S23SaS46S2fA1S22SaA1A3A3A2A2A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W9qb_0 : ltac2:(tb__ "0|0|
S0S21S10S44S76S41VW;S88S2fA3A2A1S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D9qb_0 : ltac2:(tb__ "0|5|
S0S28S25S24S25SbSbA2M0A1M1S24ScA1M2A2M3A1S3eS12aS2S76A1S41VW;S88S2fA3M4A2S44S76G4A2A2S2aG3S29G1G2S23G0S29SbSbS11S138A1S14P18A1A4S22G0A1A3S22ScA1A4A2A3"). Proof. vm_cast_no_check (@eq_refl _ (Some ([(SLit TP_A, SVar 24)], @nil sprop))). Qed.
Lemma XB9qb_0 : ltac2:(tb__ "0|0|
S0S21S9SeS2S76A1A1S29SbSbS48S2fA1S14PcA1A4A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Definition sFqb : wsub := Eval vm_compute in (infer_sub NF (S2F FFqb (KUB W swcqb nx0)) (ax_S (L_malloc_ok AE_A W st))).
Lemma ENT9qb_0 : ltac2:(tb__ "0|0|
S0S21S8S45S76S41VW;S88S2fA3S2fA3S119S118VW;Vst;A3Se6A3S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID9qb_0 : ltac2:(tb__ "0|0|
S0S21S132Se6S136A2S20A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma G110qb_0 : ltac2:(tb__ "0|0|
S0SbS133Se6S11aA2S48S2fA1A3"). Proof. vm_cast_no_check (@eq_refl _ (UBs nx0)). Qed.
End INST.
End SpineMallocSec6ILW2.

(* [comment removed for export] *)
Module F0A_hbN_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "false"; "pair"; "bool"; "nil"; "app"; "prod"; "list"; "length"; "negb"; "true"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "SLit"; "SPUle"; "SAlu"; "SPUlt"; "SPAlign"; "SPBranch"; "SPNot"; "SVar"; "ob_base"; "ob_lo"; "ss_facts"; "ss_objs"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states"; "vH"; "vMS"; "dropD"; "setpc"; "vNCH"; "vPTR"; "O_secg"; "O_secm"; "O_secn"; "O_secs"; "TOPMAX"; "addos"; "jregs"; "vEND"; "F_h"; "F_len"; "GBEXIT"; "GBSCAN"; "LENS"; "MSENTS"; "OBJ2"; "O_chS"; "O_cidx"; "O_clast"; "O_csh"; "O_hh"; "O_hidx"; "O_lidx"; "O_seci"; "dropk"; "vCHV"; "vIDX"; "vNEAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states"; "mT"; "s5_hb"; "D_U_hb"; "F1_hb"; "F2_hb"; "F_qsz"; "Fm_hb"; "O_qsz"; "R5_hb"; "T5_hb"; "XEX_hb"; "XO_hb"; "exit_perm_hb"; "hb_vars"; "is_botwin"; "vRISh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs"; "idx_where"; "is_image"; "is_link"; "is_winpiece"; "memN"; "n_pieces"; "sort_by"; "win_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "memset_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel"; "addf"; "addo"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXSelect"; "@Corelib.Lists.ListDef"; "map"; "nth"; "repeat"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "O_blkN"; "O_hdr"; "O_sh"; "axf"; "cQ"; "optR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "HIGH_SHADOW_END"; "kQuarantineCacheMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "stack_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue"; "notin_vars"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skeln.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skeln.
Import ListNotations.
Open Scope Z_scope.

Definition RET_PUT : Z := 0x40744.
Definition mT : sv := SAlu ALU_ADD (SVar 12) (SLit (-16)).

Definition vRISh : sv := SVar 195.
Definition XO_hb : list sobj := ltac2:(tb__ "0|6|
S0SfS62S12Z0A1M0Zeddc0M1Zeddc4S0S7S7SdS1A2M2S11A2M3S3G2S11S3SdS1G1U4A4S12ZffffffffA1A4S5G3A1M4A3A4S0SfS62G0Zeddc8M5Zeddd1S0G3S3G2S11S3SdS1G5U8A4S56A4S0G3S3G2S11S3SdS1Zeddd0U1A4G0A4G4A3A3A4S0SfS3bS0SfS27S0SfS28S0SfS26S0SfS25S5SfA1A3A3A3A3A3A3A3").
Definition Fm_hb (f : nat) : list sprop := ltac2:(tb__ "0|3|
S1S8S10A1M0Lf;Vf;S0S10S15S47S5fA2S5S10A1M1A3M2S1S1G0Ln;R1G2S1S0S10S13S14S43S5fS12S65Z2Z25A2A1A3S47A2G1A3Ln0;X1x2Ln;X1x2").
Definition F1_hb (f : nat) : list sprop := ltac2:(tb__ "0|1|
S6S10S4dVf;A1S0S10S13S12S7bA1S5fA2S0S10S13S5fS12S66S66S29S65Z2M0Z25A2A2Z1000A2A1A2S0S10S18S17S44S23S12Z0A1A3A1S0S10S13S23S12S65G0Z14A2A1A2S5S10A1A3A3A3A3A3").
Definition F2_hb (f : nat) (l : bool) : list sprop := ltac2:(tb__ "0|4|
S6S10S0S10S2eS0S10S18S17S44S1fS12Z0A1A3A1S0S10S13S1fS47A2S0S10S15S47S14S43S1fS20A3M0A2S0S10S16PcaZcM1A2S0S10S16PcbG1A2S0S10S13S12Z12000A1S20A2S0S10S13S20S12S29A1M2A2S0S10S13S12Z646000A1S1fA2S0S10S13G0G2A2S0S10S13S14S43S20S1fA3G2A2S5S10A1M3A3A3A3A3A3A3A3A3A3A3A3S6S10S2dVf;A1S4S8S10A1Ll;Vl;G3S0S10S15S3eS14S43S23S12N1A1A3A2G3A3X4x2A3A3").

Definition hb_vars : list positive := ltac2:(tb__ "0|0|
S0ScPc3S0ScPacS0ScPc0S0ScPc1S0ScPc2S0ScPc8S0ScPc9S0ScPcaS0ScPcbS0ScPccS0ScPcdS0ScPceS0ScPcfS0ScPd1S0ScPd2S0ScPd3S0ScPd4S0ScPd5S5ScA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition hb_fresh (E : axst) : bool := ltac2:(tb__ "0|0|
S70S7eS54A1S40VE;A1A2").

Definition S0_hb (E : axst) (f : nat) : axst := ltac2:(tb__ "0|0|
S63S2aVE;S52A2S4aVf;A1A2").
Definition SC_hb (LA : axst) : axst := ltac2:(tb__ "0|1|
S64S22VLA;S30S6S7S1S11A2M0S0G0S3S1S11UcS24A4S0G0S3S1S11UdS3fA4S0G0S3S1S11UeS2cA4S5G0A1A3A3A3S2bA3A3S34S24S3dA2A2").
Definition SX_hb (SC : axst) (f : nat) (l : bool) : axst := ltac2:(tb__ "0|1|
S63S2aS21S3cS22VSC;S2fS6S7S1S11A2M0S0G0S3S1S11UcS24A4S0G0S3S1S11UdS1fA4S0G0S3S1S11UeS2cA4S5G0A1A3A3A3S2bA3A3U1A2S0SfS77S5SfA1A3A2S33Vl;S1fA2A2S4bVf;Vl;A2A2").
Definition C5_hb (E5 : axst) : axst := ltac2:(tb__ "0|1|
S22VE5;S32S0S7S1S11A2M0S3S1S11UcS31S20A1A4S5G0A1A3A3").
Definition s5_hb (C5 : axst) : wsub := ltac2:(tb__ "0|0|
S6fP1S40VC5;A1S40S60A1A3").
Definition R5_hb (C5 : axst) : list sobj := ltac2:(tb__ "0|0|
S7aS72VC5;S60S48VC5;A1A3A1").
Definition T5_hb (C5 : axst) : axst := ltac2:(tb__ "0|0|
S73S48VC5;A1S60S6eS74S61A1A1VC5;S4fVC5;A1A5").
Definition T5f_hb (C5 : axst) : axst := ltac2:(tb__ "0|0|
S71S50VC5;A1S1cS40VC5;A1A1A2").
Definition EMd_hb (EM : axst) : axst := ltac2:(tb__ "0|0|
S21VEM;S0SfS37S1fS20A2S5SfA1A3A2").
Definition D_U_hb (l : bool) : list sobj := ltac2:(tb__ "0|2|
S6SfS0SfS27S0SfS28S0SfS26S0SfS25S0SfS38S1fS20A2S0SfS39S1fS12Z0A1M0A2S0SfS36G0A1S0SfS76S0SfS75S5SfA1M1A3A3A3A3A3A3A3A3A3S4S8SfA1Ll;Vl;G1S0SfS35G0A1S0SfS3aG1A3A3X4x2A3").
Definition EUd_hb (EU : axst) (l : bool) : axst := ltac2:(tb__ "0|0|
S21VEU;S49Vl;A1A2").
Definition O_qsz : sobj := ltac2:(tb__ "0|3|
S62S79Z18M0Z20S0S7S7SdS1A2M1S11A2M2S3G1S11S3SdS1G0U8A4S19P7bA1A4S5G2A1A3A4").
Definition F_qsz : list sprop := ltac2:(tb__ "0|0|
S0S10S13S19P7bA1S12S7cA1A2S5S10A1A3").
Definition PT_hb (LR : axst) : axst := ltac2:(tb__ "0|0|
S63S64VLR;S4eA2S4cA2").

Definition pcs_of (l : list leafA) : list Z := ltac2:(tb__ "0|0|
S6aS41SdS41S1eS40S42R1A1A1A1LL;Vl;A4").
Definition MUNMAP_EC : Z := 0x70518.   Definition MADVISE_EC : Z := 0x70550.

Definition is_botwin (o : sobj) : bool := ltac2:(tb__ "0|9|
S11S4Lx;M0S1aVo;A1SdS2Lz;M1ScScS4Li;R1ScS2Lp;ScScS4Lp;R1ScScS4Lp0;R1ScS2Lp1;ScScS4Lp1;R1ScS2Lp2;M2G2G0S1bVo;A1G1ScScS4Li0;R1ScScS4Lp2;R1ScScS4Lp3;R1ScScS4Lp4;R1ScS2Lp5;M3G3SbXcx3Lp4;ScS2Lp4;S2Xcx3Lp3;ScS2Lp3;S2Xcx3Lp2;G2S2Xcx3Li0;S45S11S11S2Lb;La;M4Lop;M5G5S46G4Lop;M6G6S4SeS11S2La;Lw;Lsgn;M7ScS11SdS2Lk;M8Li0;Ll;X11x8Xcx3Lp1;S2Xcx3Lp0;ScS2Lp0;S2Xcx3Lp;S2Xcx3Li;G5G5G6G6G7ScS11G8Li;Ll;X11x8").
Definition exit_perm_hb (S : sstate) : list nat := ltac2:(tb__ "0|2|
S1dVS;A1S8SfA1S1S5eS6bSfR1R2S7dA4A1Li;S1SdFi;S57S55R2A2S8S1A1M0S5dR2S57S5aR3A2A2G0S57S59R4A2G0S57S58R5A2G0S6S1R4S6S1R3S6S1R2R1A3A3A3G0S6S1R1S80S1G0S82S1A1S1S7fSaS5bR1R2A2A1M1A1Li;S1S81G1A1Lx;S6dU0S9SfR7A2A2A6A3Thead;Tim;Tlk;Twp;Tbw;Tkey;Tobjs;").
Definition XEX_hb (Xf : axst) : list axform := ltac2:(tb__ "0|1|
S0S67S69S53S40VXf;A1M0A1A1S6cS67S68U0A1S5cG0A1A3A3").
Definition XM_hb (Xf : axst) : axst := ltac2:(tb__ "0|0|
S78VXf;S51VXf;A1A2").

End F0A_hbN_states.

(* [comment removed for export] *)
Module InvQ11.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "sub"; "of_nat"; "div"; "modulo"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "sc_map_beg"; "aa_sec"; "aa_live"; "AA"; "sc_map_size"; "aa_geom"; "ag_pab"; "ageom"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cache_inited"; "aa_cls"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "mkAA"; "sc_size"; "@Corelib.Init.Datatypes"; "prod"; "bool"; "false"; "app"; "pair"; "list"; "Some"; "option"; "cons"; "fst"; "nat"; "snd"; "length"; "None"; "negb"; "@Stdlib.Lists.List"; "In"; "nth_error"; "filter"; "NoDup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "is_primary"; "rz"; "Sh"; "round_up"; "kQuarantineMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "cell_ok"; "mkACell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "rl"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_sh_zone"; "chunk_zone"; "sec_junk_zone"; "sec_tbl_zone"; "swap_remove"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "live_ids"; "SEC_INST"; "q_foot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qall"; "qitems"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b"; "RZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.InvQ11"; "freeBigA"; "@Corelib.Init.Nat"; "sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt SoundA SummaryA MmapFixedA MmapFixedA2 MadviseSpecA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws ContractFreeNull SMGlue RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.RebuildS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import PlacementA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.InvQ10a OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.InvQ10b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.InvQ10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition freeBigA (A : AA) (l1 l2 : list (Z * Z)) (i : nat) : AA := ltac2:(tb__ "0|0|
S25S16VA;A1S1dVA;A1S1cVA;A1S4cS10S12VA;A1Vi;A3S22VA;A1S2aS27S0S0A2Vl1;Vl2;A3S24VA;A1S23VA;A1S1eVA;A1S20VA;A1S1fVA;A1S21VA;A1S1bVA;A1S1aVA;A1S19VA;A1Af").

Lemma big_not_primary : ltac2:(tb__ "0|0|
S0S9S3fR1A2S2S28S3bR2A1S29A3F_;Fn;").
Proof.
  intros n Hn. destruct (is_primary n) eqn:E; [exfalso | reflexivity]. unfold is_primary in E. apply Z.leb_le in E.
  unfold needed in E. pose proof (rz_bound n) as RB. unfold kQuarantineMax in Hn.
  assert (R8 : n <= round_up (Z.max n kChunkHeader2Size) 8) by (unfold round_up; pose proof (Z.div_mod (Z.max n kChunkHeader2Size + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Z.max n kChunkHeader2Size + 7) 8 ltac:(lia)); lia).
  unfold kMaxSize in E. lia.
Qed.
Lemma nonprimary_large : ltac2:(tb__ "0|0|
S0S8Z1R1A2S2S28S3bR2A1S29A3S8Zfc01R3A2F_;F_;Fn;").
Proof. intros n H1 HP. destruct (Z_le_dec 64513 n) as [L|L]; [exact L|]. rewrite (primary_small n) in HP by lia. discriminate HP. Qed.

Section PureLive.
Variables (A : AA) (l1 l2 : list (Z * Z)) (p n : Z) (i : nat) (ch : sec_chunk).
Hypothesis HLV : ltac2:(tb__ "0|1|
S2S2cS27S0S0A2M0A1S13VA;A1S2aG0Vl1;S2fG0S2bS0S0Vp;Vn;A4Vl2;A3A3A3").
Hypothesis HPn : is_primary n = false.
Hypothesis Hn1 : 1 <= n.
Hypothesis Hi : ltac2:(tb__ "0|0|
S2S2eS10A1S37S10S12VA;A1Vi;A3S2dS10Vch;A2A3").
Hypothesis Hu : ltac2:(tb__ "0|0|
S2S0Vp;S7S7S11Vch;A1S3aA2Z800A2A3").
Hypothesis HQP : q_pure A.
Hypothesis HI3 : inv3 A.
Local Abbreviation A' := (freeBigA A l1 l2 i).
Local Abbreviation secf := (fun bn : Z * Z => negb (is_primary (snd bn))).

Lemma PL_in : ltac2:(tb__ "0|1|
S27S0S0A2M0S36G0R1S2aG0Vl1;Vl2;A3A3S36G0R2S13VA;A1A3F_;Fbn;").
Proof. intros bn H. rewrite HLV. apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. Qed.

Lemma PL_nodup : ltac2:(tb__ "0|4|
S3S39S0S2aS0S55S27S0S0A2M0S0S30S0S0A2M1S38G0G0S35S3bS32S0S0R1A3A1A1Lbn;M2S2aG0Vl1;Vl2;A3A3A4S55G0S0G1S38G0G2S54S53VA;A1A1A3A4A3M3A2S4S36S0Vp;G3A3A1A2").
Proof.
  destruct HI3 as (_ & _ & _ & _ & _ & ND & _). apply (proj1 (NoDup_ListNoDup _)) in ND.
  rewrite HLV in ND. rewrite !List.filter_app in ND. cbn [List.filter snd] in ND. rewrite HPn in ND. cbn [negb] in ND.
  rewrite !List.filter_app. rewrite !map_app in ND. rewrite !map_app. cbn [map fst] in ND.
  rewrite <- app_assoc in ND. cbn [app] in ND. rewrite <- app_assoc.
  exact (NoDup_remove _ _ _ ND).
Qed.
Lemma PL_live_other : ltac2:(tb__ "0|1|
S0S0S36S27S0S0A2M0S2bS0S0R2R1A4S2aG0Vl1;Vl2;A3A3S2S28S3bR2A1S29A3S4S2S0R4Vp;A3A1F_;F_;Fm;Fb;").
Proof.
  intros b m Hin HP E. destruct PL_nodup as [_ NI]. apply NI. apply in_or_app. left. apply in_map_iff. exists (b, m). split; [exact E|].
  apply filter_In. split; [exact Hin|]. cbn. rewrite HP. reflexivity.
Qed.
Lemma PL_item_other : ltac2:(tb__ "0|1|
S27S0S0A2M0S36G0R1S54S53VA;A1A1A3S2S28S3bS32S0S0R2A3A1S29A3S4S2S0S30S0S0R3A3Vp;A3A1F_;F_;Fit;").
Proof.
  intros it Hin HP E. destruct PL_nodup as [_ NI]. apply NI. apply in_or_app. right. apply in_map_iff. exists it. split; [exact E|].
  apply filter_In. split; [exact Hin|]. rewrite HP. reflexivity.
Qed.
Lemma PL_chunk_stays : ltac2:(tb__ "0|0|
S10S0S36S10R2S12VA;A1A3S2S0R2S7S7S11R3A1S3aA2Z800A2A3S4S2S0R3Vp;A3A1S36S10R5S12S5bVA;Vl1;Vl2;Vi;A4A1A3F_;F_;F_;Fu;Fc;").
Proof.
  intros c u Hc Eu NE. change (aa_sec A') with (swap_remove (aa_sec A) i). destruct (In_nth_error _ _ Hc) as [j Hj].
  apply (swap_remove_In _ i ch j c Hi Hj). intros ->. rewrite Hi in Hj. injection Hj as <-. apply NE. rewrite Eu, Hu. reflexivity.
Qed.
Lemma QP_live : q_pure A'.
Proof.
  destruct HQP as [QF QN]. unfold q_pure. change (qall A') with (qall A). split; [|exact QN].
  apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) QF b Hb) as (B1 & B2 & B3 & B4).
  unfold batch_pure. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
  apply Forall_forall. intros it Hit. pose proof (proj1 (Forall_forall _ _) B4 it Hit) as (I1 & I2 & I3 & I4).
  unfold item_pure. cbv zeta. split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
  intros HP. destruct (I4 HP) as (c & Hc & Eu & Es). exists c. split; [|exact (conj Eu Es)].
  apply (PL_chunk_stays c (fst it) Hc Eu). apply PL_item_other; [|exact HP]. unfold qitems. apply in_flat_map. exists b. split; [exact Hb | exact Hit].
Qed.

Lemma I3_live : inv3 A'.
Proof.
  pose proof HI3 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold inv3. cbv zeta.
  change (aa_geom A') with (aa_geom A). change (aa_live A') with (l1 ++ l2). change (aa_sec A') with (swap_remove (aa_sec A) i).
  change (aa_cls A') with (aa_cls A). change (aa_depot A') with (aa_depot A). change (aa_cache_inited A') with (aa_cache_inited A).
  split; [exact I1|].
  split.
  { intros b m Hin. destruct (I2 b m (PL_in _ Hin)) as [P|(c & Hc & Eb & Es)]; [left; exact P|].
    destruct (is_primary m) eqn:EP; [left; reflexivity | right]. exists c. split; [|exact (conj Eb Es)].
    exact (PL_chunk_stays c b Hc Eb (PL_live_other b m Hin EP)). }
  split.
  { intros j c Hj. destruct (swap_remove_nth _ i ch j c Hi Hj) as (LTj & ORj).
    assert (OLDj : exists j0, nth_error (aa_sec A) j0 = Some c /\ j0 <> i /\ ((j <> i /\ j0 = j) \/ (j = i /\ j0 = (length (aa_sec A) - 1)%nat))).
    { destruct ORj as [[N E]|(E1 & LT & E)]; [exists j; split; [exact E | split; [exact N | left; split; [exact N | reflexivity]]]|].
      exists (length (aa_sec A) - 1)%nat. split; [exact E | split; [lia | right; split; [exact E1 | reflexivity]]]. }
    destruct OLDj as (j0 & Hj0 & Nj0 & Cj). destruct (I3 j0 c Hj0) as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [|exact (conj X6 X7)].
    intros j2 c2 Hj2 Nj. destruct (swap_remove_nth _ i ch j2 c2 Hi Hj2) as (LTj2 & ORj2).
    destruct ORj2 as [[N2 E2]|(E21 & LT2 & E2)].
    - apply (X5 j2 c2 E2). destruct Cj as [[_ ->]|[_ ->]]; [exact Nj | lia].
    - apply (X5 _ c2 E2). destruct Cj as [[Nji ->]|[Eji _]]; [lia | exfalso; apply Nj; rewrite Eji, E21; reflexivity]. }
  split; [exact I4|].
  split.
  { intros bn Hbn. destruct (I5 bn Hbn) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|]. split; [exact D7|].
    intros c Hc. destruct (swap_remove_incl _ i ch c Hi Hc) as (j & _ & Hj). exact (D8 c (nth_error_In _ _ Hj)). }
  split.
  { apply (proj2 (NoDup_ListNoDup _)). exact (proj1 PL_nodup). }
  split.
  { rewrite (swap_remove_length _ i ch Hi). change (qlarge A') with (qlarge A).
    pose proof (large_live_remove A A' l1 l2 p n HLV eq_refl) as LL. pose proof (nonprimary_large n Hn1 HPn) as LN.
    destruct (64513 <=? n) eqn:E; [|apply Z.leb_gt in E; exfalso; lia].
    pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite Hi; discriminate)) as LI. lia. }
  split.
  { pose proof (small_live_remove A A' l1 l2 p n HLV eq_refl) as SL. pose proof (nonprimary_large n Hn1 HPn) as LN.
    destruct (64513 <=? n) eqn:E; [|apply Z.leb_gt in E; exfalso; lia]. lia. }
  exact I9.
Qed.
End PureLive.

Section GeoLive.
Variables (A : AA) (m : bview).
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HLS : live_sep A.
Hypothesis HPR : primary_repr m A.
Hypothesis HSR : secondary_repr m A.
Hypothesis HI3 : inv3 A.
Variables (i : nat) (ch : sec_chunk).
Hypothesis Hi : ltac2:(tb__ "0|0|
S2S2eS10A1S37S10S12VA;A1Vi;A3S2dS10Vch;A2A3").

Lemma blk_in_chunk : ltac2:(tb__ "0|2|
S0S0S36S27S0S0A2S2bS0S0R2R1A4S13VA;A1A3S2S28S3bR2A1S29A3S2S0R4S7S7S11Vch;A1M0S3aA2Z800M1A2A3S3S2S0S3cR4A1G1A3S3S8Z1R4A2S8S7S7R5R4A2G1A2S7G0S15Vch;A1A2A2A2A2F_;F_;F_;Fn;Fp;").
Proof.
  intros p n Hin HP Hu. destruct (live_sec_map A m HLS HSR HI3 p n Hin HP) as (j & c & Hj & Eb & RZn & N1 & BN & _).
  assert (Eji : j = i).
  { destruct (Nat.eq_dec j i) as [E|NE]; [exact E | exfalso]. destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j c Hj) as (_ & _ & _ & _ & X5 & _).
    pose proof (X5 i ch Hi NE) as AP. destruct (ch_nums A m HSR j c Hj) as (_ & C2 & _). destruct (ch_nums A m HSR i ch Hi) as (_ & C2' & _). lia. }
  subst j. rewrite Hi in Hj. injection Hj as <-. split; [exact RZn|]. split; [exact N1 | exact BN].
Qed.

Lemma blk_foot_chunk : ltac2:(tb__ "0|1|
S0S0S0S36S27S0S0A2S2bS0S0R3R2A4S13VA;A1A3S2S28S3bR3A1S29A3S2S0R5S7S7S11Vch;A1S3aA2Z800A2A3S3S3S8SaR6S3cR5A1A2R4A2S9R4S7R6R5A2A2A2S49Vch;R5A2F_;S3S8S3dR6A1M0R4A2S9R4S7G0ScS7R5Z7A2Z8A2A2A2A2S48Vch;R5A2F_;A2F_;F_;F_;Fz;Fn;Fp;").
Proof.
  intros p n z Hin HP Hu. destruct (blk_in_chunk p n Hin HP Hu) as (RZn & N1 & BN). destruct (ch_nums A m HSR i ch Hi) as (C1 & C2 & C3 & _ & C5 & C6 & C7).
  unfold chunk_zone, chunk_sh_zone, PG in *. split; [intros Hz; lia|]. intros Hz. rewrite C7.
  pose proof (Geometry.Sh_mono (sc_map_beg ch) p ltac:(lia)) as M1.
  assert (M2 : Sh p + (n + 7) / 8 <= Sh (sc_map_beg ch) + sc_map_size ch / 8).
  { unfold Sh in *. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as MB.
    pose proof (Z.div_le_mono (p + (n + 7) / 8 * 8) (sc_map_beg ch + sc_map_size ch) 8 ltac:(lia) ltac:(lia)) as X. rewrite Z.div_add in X by lia.
    assert (E : (sc_map_beg ch + sc_map_size ch) / 8 = sc_map_beg ch / 8 + sc_map_size ch / 8).
    { pose proof (Z.div_mod (sc_map_size ch) 8 ltac:(lia)) as D2. rewrite C6 in D2. replace (sc_map_beg ch + sc_map_size ch) with (sc_map_beg ch + sc_map_size ch / 8 * 8) by lia. apply Z.div_add. lia. }
    lia. }
  lia.
Qed.

Section SubLive.
Variable L : list (Z * Z).
Hypothesis HLin : ltac2:(tb__ "0|1|
S27S0S0A2M0S36G0R1VL;A3S36G0R2S13VA;A1A3F_;Fbn;").
Hypothesis HNL : ltac2:(tb__ "0|0|
S0S0S36S27S0S0A2S2bS0S0R2R1A4VL;A3S2S28S3bR2A1S29A3S4S2S0R4S7S7S11Vch;A1S3aA2Z800A2A3A1F_;F_;Fn;Fb;").
Lemma nRZ_liveL : ltac2:(tb__ "0|1|
S0S0S0S36S27S0S0A2S2bS0S0R3R2A4VL;A3S6S3S8SaR4S3cR3A1A2R2A2S9R2S7R4R3A2A2A2S3S8S3dR4A1M0R2A2S9R2S7G0ScS7R3Z7A2Z8A2A2A2A2A2S4S5aVA;Vi;Vch;R3A4A1F_;F_;Fz;Fn;Fb;").
Proof.
  intros b n z HinL Hz. pose proof (HLin _ HinL) as Hin. destruct (space_nums A HG) as (S1 & S2 & _). destruct (is_primary n) eqn:HP.
  - pose proof HI3 as (H3 & _). pose proof (live_prim_czone A HG H3 m HLS HPR b n Hin HP) as LP. cbv zeta in LP.
    destruct LP as (C1 & O0 & OM & OE & _ & _ & CZ).
    destruct (czone_where A HG H3 _ _ z C1 O0 OM OE (CZ z Hz)) as [W|[W _]].
    + apply (nRZ_space A m HG HSR HI3 i ch Hi). clear -W. lia.
    + apply (nRZ_space_sh A m HG HSR HI3 i ch Hi (ag_spacebeg (aa_geom A)) (ag_spacebeg (aa_geom A) + 2 ^ 37) z); [lia | lia | lia | exact W].
  - destruct (live_sec_map A m HLS HSR HI3 b n Hin HP) as (j & c & Hj & Eb & RZn & N1 & BN & _).
    assert (Nji : j <> i) by (intros ->; rewrite Hi in Hj; injection Hj as <-; exact (HNL b n HinL HP Eb)).
    destruct (ch_nums A m HSR j c Hj) as (C1 & C2 & C3 & _). unfold PG in Eb.
    destruct Hz as [Hz|Hz].
    + apply (nRZ_chunk A m HSR HI3 i ch Hi j c z Hj Nji); [rewrite RZn in Hz; lia | intros _; rewrite RZn in Hz; lia].
    + destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j c Hj) as (_ & _ & _ & _ & X5 & _). pose proof (X5 i ch Hi Nji) as AP.
      apply (nRZ_sh A m HSR i ch Hi b n z); [lia | lia | lia | lia | exact Hz].
Qed.
End SubLive.

Hypothesis HQP : q_pure A.
Hypothesis HNI : ltac2:(tb__ "0|1|
S27S0S0A2M0S36G0R1S54S53VA;A1A1A3S2S28S3bS32S0S0R2A3A1S29A3S4S2S0S30S0S0R3A3S7S7S11Vch;A1S3aA2Z800A2A3A1F_;F_;Fit;").
Lemma nRZ_qfoot : ltac2:(tb__ "0|0|
S0S52VA;R1A2S4S5aVA;Vi;Vch;R2A4A1F_;Fz;").
Proof.
  intros z Hz. pose proof HI3 as (H3 & _). destruct (space_nums A HG) as (S1 & S2 & _).
  assert (HAU : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A c) <= kUserSpaceSize).
  { intros c Hc. destruct HPR as (_ & _ & _ & P4). pose proof (P4 c Hc) as HC. unfold class_repr in HC. cbn zeta in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & _). unfold cls_of, kUserMapSize in *. lia. }
  assert (PRIM : qzone A z -> ~ RZ A i ch z).
  { intros QZ. destruct (qzone_czone A HG H3 HQP HAU z QZ) as (c & o & (C1 & O0 & OM & OE & _) & CZ).
    destruct (czone_where A HG H3 _ _ z C1 O0 OM OE CZ) as [W|[W _]].
    - apply (nRZ_space A m HG HSR HI3 i ch Hi). clear -W. lia.
    - apply (nRZ_space_sh A m HG HSR HI3 i ch Hi (ag_spacebeg (aa_geom A)) (ag_spacebeg (aa_geom A) + 2 ^ 37) z); [lia | lia | lia | exact W]. }
  unfold q_foot in Hz. fold (qall A) in Hz. apply Exists_exists in Hz as (b & Hb & Hz). destruct Hz as [Hz|Hz].
  - apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | left; exact Hz].
  - apply Exists_exists in Hz as (it & Hit & Hz). destruct (is_primary (snd it)) eqn:EP.
    + apply PRIM. unfold qzone. apply Exists_exists. exists b. split; [exact Hb | right]. apply Exists_exists. exists it. split; [exact Hit|]. split; [exact EP | exact Hz].
    + destruct HQP as [QP _]. pose proof (proj1 (Forall_forall _ _) QP b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _ & IP4).
      destruct (IP4 EP) as (c & Hc & Eu & Esz). destruct (In_nth_error _ _ Hc) as [j Hj].
      assert (Hitq : In it (qitems (qall A))) by (unfold qitems; apply in_flat_map; exists b; split; [exact Hb | exact Hit]).
      assert (Nji : j <> i) by (intros ->; rewrite Hi in Hj; injection Hj as <-; exact (HNI it Hitq EP Eu)).
      pose proof HSR as (HS1 & _). destruct (HS1 j c Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
      pose proof (rz_sec (snd it) IP2 EP) as RZn. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot.round_up_ge8 (snd it)) as R8. destruct (ch_nums A m HSR j c Hj) as (C1 & C2 & C3 & _). unfold PG in *.
      destruct Hz as [Hz|Hz].
      * apply (nRZ_chunk A m HSR HI3 i ch Hi j c z Hj Nji); [lia | intros _; lia].
      * destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j c Hj) as (_ & _ & _ & _ & X5 & _). pose proof (X5 i ch Hi Nji) as AP.
        apply (nRZ_sh A m HSR i ch Hi (fst it) (snd it) z); [lia | lia | lia | lia | exact Hz].
Qed.
End GeoLive.

Lemma live_ids_remove_sec : ltac2:(tb__ "0|3|
S18S14S14S2cS27S0S0A2M0A1M1G1S0S0S0S2G1S13R7A1M2S2aG0R5S2fG0S2bS0S0R3R2A4R4A3A3A3S2G1G2S2aG0R6R5A3A3S2S28S3bR4A1S29A3S2S2cS0A1S50RbR9R4A3S50RbRaR4A3A3F_;F_;F_;Fc;Fn;Fp;Fl2;Fl1;FA';FA;FG;").
Proof.
  intros G A A' l1 l2 p n c E E' HP. rewrite !F0A_rebuild.live_ids_LI, E, E', !F0A_rebuild.LI_app, F0A_rebuild.LI_cons.
  unfold F0A_rebuild.Pc at 1. cbn [snd]. rewrite HP. reflexivity.
Qed.

Theorem AInvA_unmap_live : ltac2:(tb__ "0|18|
S14S45S45S2cS4eQ40M0A1M1A1S56S2cS27S0S0A2M2A1M3G3S0S0S31S10S4fS40RbRaR8R7A5S2G3S13RcA1S2aG2R7S2fG2S2bS0S0R5R4A4R6A3A3A3S2S28S3bR5A1S29A3S2S2eS10A1M4S37S10S12ReA1R5A3S2dS10R4A2A3S2S0R8S7S7S11R5A1S3aA2Z800A2A3S16R10A1S18SbS33S10S12R11A1A2A1S0S1S2G1S47R11R1A2S47R12R1A2A3Fi0;S1S2S2cS4eQ8A1M5A1S46R12R1A2S46R13R1A2A3Fl;S0S4S4aR1A1M6A1S4S4bR16RdR2A3A1S4S49RdR3A2A1S4S48ReR4A2A1S2S2eG5A1M7S41S40S44R17A1R5A3S41S40S44R18A1R5A3A3F_;F_;F_;F_;Fz;S0S6G6S48RcR1A2A2S4S2G7S41S40S44R16A1M8R2A3S34G5A1M9A3A1S4S2G7S41S40G8R3A3G9A3A1F_;F_;Fz;S42S41S40S44R14A1A2S43S7S51Z38A2U8MaSaR5Z1MbA2A3A2S42S41S40S44R15A1A2S43Zee040U4Z0A3A2S10S2G4S37S10S12R19A1McS5cS33S10GcA2U1A2A3S2dS10R1A2A3S3S9SbR11A1MdSaR9GbA2MeA2S3S42S41S40S44R19A1A2MfS43S7S17RbA1SeZ8M10SbR12A1M11A2A2GaS11R3A1M12A3A2S42GfS43S7G12Z18A2GaG11A3A2A2F_;S2S0GdGeA3S0S3S8S7S17RcA1SeG10SbR13A1A2A2M13R1A2S9R1S7G13G10A2A2A2S2G7S41S40S44R1bA1R2A3S41S40S44R1cA1R2A3A3F_;Fz;F_;A2F_;Flst;S8S59S57R15S4dG0S11RfA1M14A2S4dG0S15RfA1M15A2A3S58G14S7G14G15A2R16A3A2S59R15R16A2A2S4fS40S5bR1aR15R14R11A4R18S58S11R10A1M16S7G16S15R10A1M17A2R17A3S57R16S4dG0G16A2S4dG0G17A2A3A5F_;F_;F_;F_;F_;F_;F_;F_;Tnch;TG;F_;F_;F_;F_;F_;Fch;Fi;Fn;Fp;Fl2;Fl1;Fmd;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp md l1 l2 p n i ch HAA HLV HPn Hi Hu. cbv zeta. intros Hw Hl HOUT0 HIN CN CM CL HPAID.
  set (A' := freeBigA A l1 l2 i).
  set (tp' := tp_forget (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) tp).
  set (md' := munmap_model md (Z_to_bv 64 (sc_map_beg ch)) (Z_to_bv 64 (sc_map_size ch))).
  pose proof (AInvA_Q A rho tp md HAA) as HA.
  pose proof HAA as (HG & _ & _ & HRestA & _). destruct HRestA as (_ & _ & _ & _ & HQR & _).
  pose proof HA as (_ & _ & _ & HRest & HM & HI3 & _). cbv zeta in HRest. destruct HRest as (HLS & R2 & HPR & HSR & (HQP & _) & _).
  set (mm := maskv (fs_footb (aa_geom A)) (view segsA (rm rho))) in *. set (mm' := maskv (fs_footb (aa_geom A)) (view segsA (rm rho'))).
  assert (Hin : In (p, n) (aa_live A)) by (rewrite HLV; apply in_or_app; right; left; reflexivity).
  assert (Hn1 : 1 <= n) by exact (proj1 (HLS p n Hin)).
  assert (HOUT : forall z, ~ RZ A i ch z -> view segsA (rm rho') z = view segsA (rm rho) z).
  { intros z NR. apply HOUT0; intros X; apply NR; [left | right; left | right; right; left | right; right; right]; exact X. }
  assert (HNL : forall b m0, In (b, m0) (l1 ++ l2) -> is_primary m0 = false -> b <> sc_map_beg ch + PG + 2048).
  { intros b m0 Hb HP. rewrite <- Hu. exact (PL_live_other A l1 l2 p n HLV HPn HI3 b m0 Hb HP). }
  assert (HNI : forall it, In it (qitems (qall A)) -> is_primary (snd it) = false -> fst it <> sc_map_beg ch + PG + 2048).
  { intros it Hit HP. rewrite <- Hu. exact (PL_item_other A l1 l2 p n HLV HPn HI3 it Hit HP). }
  assert (OUTM : forall z, ~ RZ A i ch z -> mm' z = mm z) by (intros z NR; exact (X_out A rho rho' i ch (RZ A i ch) (fun _ H => H) HOUT z NR)).
  destruct (blk_in_chunk A mm HLS HSR HI3 i ch Hi p n Hin HPn Hu) as (RZn & _ & BN).
  assert (HCH : forall j c, nth_error (aa_sec A) j = Some c -> 0 < sc_map_size c /\ dyn_in (topG (aa_geom A)) (sc_map_beg c) (sc_map_size c)).
  { intros j c Hj. destruct HSR as (S1 & _). destruct (S1 j c Hj) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & D10 & _). split; [unfold PG in D8; lia | exact D10]. }

  assert (HQ' : AInvQ A' rho' tp' md').
  { unfold AInvQ. cbv zeta. change (aa_geom A') with (aa_geom A). fold mm'.
    split; [exact HG|].
    split; [exact (X_rtc A rho rho' tp md i ch (RZ A i ch) HA Hi (fun _ H => H) HOUT)|].
    split; [exact (X_fs A rho rho' tp md i ch (RZ A i ch) HA Hi (fun _ H => H) HOUT)|].
    split; [|split; [exact (model_unmap A tp md i ch (aa_q_thread A) (aa_q_global A) HM HI3 Hi HCH HPAID) | split]].
    -
      split; [intros b m0 Hb; exact (HLS b m0 (PL_in A l1 l2 p n HLV _ Hb))|].
      split.
      { assert (R2' : live_block_repr mm A') by (intros b m0 Hb; exact (R2 b m0 (PL_in A l1 l2 p n HLV _ Hb))).
        apply (live_block_repr_agree mm mm' A' A' eq_refl); [| | exact R2'].
        - intros b m0 z Hb Hz. apply OUTM. exact (nRZ_liveL A mm HG HLS HPR HSR HI3 i ch Hi (l1 ++ l2) (PL_in A l1 l2 p n HLV) HNL b m0 z Hb Hz).
        - intros b m0 Hb. exact (proj1 (HLS b m0 (PL_in A l1 l2 p n HLV _ Hb))). }
      split.
      { pose proof HPR as (Q1 & Q2 & Q3 & P4). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. intros c Hc.
        apply (class_repr_agree_gen mm mm' (aa_geom A) A A' c _ Hc eq_refl (live_ids_remove_sec (aa_geom A) A A' l1 l2 p n c HLV eq_refl HPn) eq_refl);
          [intros b m0 Hb _ _; exact (PL_in A l1 l2 p n HLV _ Hb) | | | exact (P4 c Hc)].
        - intros z Hz. apply OUTM. apply (nRZ_cls A mm HG HPR HSR HI3 i ch Hi c z Hc). unfold cls_meta in Hz. unfold cls_foot. cbv zeta in *.
          destruct Hz as [H|[H|[H|H]]]; [left | right; left | right; right; right; left | right; right; right; right]; exact H.
        - pose proof (P4 c Hc) as PC. unfold class_repr in PC. destruct PC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PU & _).
          intros z Hz Hn'.
          assert (NRz : ~ RZ A i ch z) by (apply (nRZ_cls A mm HG HPR HSR HI3 i ch Hi c z Hc); unfold cls_foot; cbv zeta; right; right; left; exact Hz).
          rewrite (OUTM z NRz). apply PU; [exact Hz|]. intros (b & m0 & Hb & Hbz). rewrite HLV in Hb. apply in_app_or in Hb as [Hb|[Hb|Hb]].
          + apply Hn'. exists b, m0. split; [apply in_or_app; left; exact Hb | exact Hbz].
          + injection Hb as <- <-. apply NRz. right. right. left. unfold chunk_zone. unfold PG in *. lia.
          + apply Hn'. exists b, m0. split; [apply in_or_app; right; exact Hb | exact Hbz]. }
      split.
      { pose proof (X_sec_unmap A rho rho' tp md i ch (aa_q_thread A) (aa_q_global A) HA Hi HOUT HIN CN CM CL) as VS. fold mm' in VS.
        destruct VS as (S1 & SR). split; [|exact SR].
        intros j c Hj. destruct (S1 j c Hj) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & PB & PS).
        split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact E6|]. split; [exact E7|]. split; [exact E8|].
        split; [exact E9|]. split; [exact E10|]. split; [exact E11|]. split; [exact E12|]. split; [|exact PS].
        intros z Hz Hn'. apply PB; [exact Hz|]. intros (b & m0 & Hb & Hbz). change (aa_live (unmap_sec (set_q A (aa_q_thread A) (aa_q_global A)) i)) with (aa_live A) in Hb.
        rewrite HLV in Hb. apply in_app_or in Hb as [Hb|[Hb|Hb]].
        + apply Hn'. exists b, m0. split; [apply in_or_app; left; exact Hb | exact Hbz].
        + injection Hb as <- <-.
          change (aa_sec A') with (swap_remove (aa_sec A) i) in Hj. destruct (swap_remove_nth _ i ch j c Hi Hj) as (_ & ORj).
          assert (OLD : exists j0, nth_error (aa_sec A) j0 = Some c /\ j0 <> i).
          { destruct ORj as [[N E]|(E1' & LT & E)]; [exists j; split; [exact E | exact N] | exists (length (aa_sec A) - 1)%nat; split; [exact E | lia]]. }
          destruct OLD as (j0 & Hj0 & Nj0). destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 j0 c Hj0) as (_ & _ & _ & _ & X5 & _).
          pose proof (X5 i ch Hi Nj0) as AP. unfold PG in *. lia.
        + apply Hn'. exists b, m0. split; [apply in_or_app; right; exact Hb | exact Hbz]. }
      split; [split; [exact (QP_live A l1 l2 p n i ch HLV HPn Hi Hu HQP HI3) | exact (X_qmin A rho rho' tp md i ch (RZ A i ch) HA Hi (fun _ H => H) HOUT)]|].
      split; [exact (X_depot A rho rho' tp md i ch (RZ A i ch) HA Hi (fun _ H => H) HOUT)|].
      split; [exact (X_ia A rho rho' tp md i ch (RZ A i ch) HA Hi (fun _ H => H) HOUT)|].
      split; [exact (X_thread A rho rho' tp md i ch (RZ A i ch) HA Hi (fun _ H => H) HOUT) | exact (X_misc A rho rho' tp md i ch (RZ A i ch) HA Hi (fun _ H => H) HOUT)].
    - exact (I3_live A l1 l2 p n i ch HLV HPn Hn1 Hi Hu HI3).
    - apply (X_bandtp A rho rho' tp md (RZ A i ch) (fun z => sec_junk_zone z \/ chunk_sh_zone ch z) HA (RZ_dec A i ch) HOUT (fun z _ HP => HIN z HP)
               (fun z HZ HB => or_intror (RZ_band A mm HSR i ch Hi z HZ HB))).
      intros q Hq. unfold tp', tp_forget in Hq. apply filter_In in Hq. exact (proj1 Hq). }

  destruct (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_rebuildW.AInvB_Q kQuarantineCacheMax A rho tp md HAA) as (_ & QM & QB1 & QB2).
  apply (AInvQ_back A' rho' tp' md' HQ'); [| exact QB1 | exact QB2].
  change (q_mem (view segsA (rm rho')) A).
  apply (q_mem_frame A (view segsA (rm rho)) (view segsA (rm rho')) HQP); [| | | exact QM].
  - intros z Hz. apply HOUT. exact (nRZ_qfoot A mm HG HPR HSR HI3 i ch Hi HQP HNI z Hz).
  - intros z Hz. apply HOUT. apply (nRZ_T A mm HG HSR HI3 i ch Hi z). lia.
  - intros z Hz. apply HOUT. apply (nRZ_low A mm HSR i ch Hi z); unfold QG, SEC_INST in *; lia.
Qed.

Theorem live_big_chunk : ltac2:(tb__ "0|8|
S14S45S2cS4eQ40A1A1S56S0S0S4fS40R6R5R4R3A5S36S27S0S0A2S2bS0S0R3R2A4S13R7A1A3S2S28S3bR3A1S29A3S5S31S31S5S10S10S3S2S2eS10A1S37S10S12RbA1R2A3S2dS10R1A2A3S3S2S0R7S7S7S11R1A1M0S3aA2Z800M1A2A3S3S2S0S26R1A1S7S3eR6Z8M2A2Z1000A2M3A3S3S2S0S15R1A1M4S7S3eG3S3aA2S3aA2A3S3S2S0SdG0S3aA2Z0M5A3S3S2S0SdG4S3aA2G5A3S3S3S9G5G4A2S9G4SfZ2Z3eA2A2A2S3S8Z646000G0A2S3S8S7G0G4A2M6Z7fffff800000A2S3S2S0S3cR6A1G1A3S3S8Z1R6A2S3S8S7S7R7R6A2G1A2G6A2S3S0S3S8SaR8S3cR7A1A2R1A2S9R1S7R8R7A2A2A2S49R3R2A2F_;Fz;S0S3S8S3dR8A1M7R1A2S9R1S7G7ScS7R7Z7A2G2A2A2A2A2S48R3R2A2F_;Fz;A2A2A2A2A2A2A2A2A2A2A2A2A2Lch;A2Li;A2F_;F_;F_;Fn;Fp;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md p n HAA Hin HP. pose proof (AInvA_Q A rho tp md HAA) as HA.
  pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _). cbv zeta in HRest. destruct HRest as (HLS & _ & HPR & HSR & _).
  pose proof HI3 as (_ & LIV3 & _). destruct (LIV3 p n Hin) as [E|(ch & Hch & Eb & Esz)]; [rewrite E in HP; discriminate|].
  destruct (In_nth_error _ _ Hch) as (i & Hi). exists i, ch.
  pose proof HSR as (S1 & _). destruct (S1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
  destruct (ch_nums A _ HSR i ch Hi) as (C1 & C2 & C3 & _).
  destruct (blk_in_chunk A _ HLS HSR HI3 i ch Hi p n Hin HP Eb) as (RZn & N1 & BN).
  split; [exact Hi|]. split; [exact Eb|]. split; [exact Esz|]. split; [rewrite <- Esz; exact D11|]. split; [exact D6|]. split; [exact D7|].
  split; [lia|]. split; [exact C1|]. split; [exact C3|]. split; [exact RZn|]. split; [exact N1|]. split; [exact BN|].
  split; intros z Hz; [exact (proj1 (blk_foot_chunk A _ HLS HSR HI3 i ch Hi p n z Hin HP Eb) Hz) | exact (proj2 (blk_foot_chunk A _ HLS HSR HI3 i ch Hi p n z Hin HP Eb) Hz)].
Qed.
End InvQ11.

(* [comment removed for export] *)
Module F0A_mL0A.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "pair"; "false"; "option"; "prod"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0A"; "q_L0A"; "Ebg_L0A"; "ED_L0A_1"; "ED_L0A_2"; "Edr_L0A"; "TD_L0A_1"; "TD_L0A_2"; "Xf_L0A"; "exits1_L0A"; "W_L0A"; "st_L0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_mL0A"; "PMID_L0A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL0A"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "XI";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ck.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_qL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d3.F0A_xiL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ck.F0A_dL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dd.F0A_aL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL0A OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0A.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_L0A : ltac2:(tb__ "0|0|
SbS14S1eS58S1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Dai_L0A : ltac2:(tb__ "0|5|
SbS1aS1bS17S1bS20S20A2M0A1M1S17S22A1M2A2M3A1S6aS12S6S2S1U0A1M4S0A3A1S58G4S0A2A2S1cG3S18G1G2S13G0S18S20S20S23P18A1S21S6dA1A4S15G0A1A3S15S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_L0A : ltac2:(tb__ "0|0|
SbS14S1eS5aS1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Wci_L0A : ltac2:(tb__ "0|0|
SbS14S1eS5bS1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Definition Certi_L0A__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S5eSaUbb8S55S57U0S0A2A4").
Lemma Certi_L0A : ltac2:(tb__ "0|1|
SbS14S3bSaUbb8S55S46S57U0M0S0A2S13S10S56S1G0A1S0A2S15S10A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_L0A__runs); [unfold Certi_L0A__runs; reflexivity | vmr]. Qed.
Lemma ECerti_L0A : ltac2:(tb__ "0|2|
SbS14S3cSaUbb8S55S46S59U0M0S0A2S13S39S3aS56S1G0A1S0A2Z0M1S21G1A1A3S15S39A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_L0A__runs); [unfold Certi_L0A__runs; reflexivity | vmr]. Qed.

Definition PMID_L0A : axst := ltac2:(tb__ "0|0|
S62S19S2dS2eS24A4").
Definition Cert1m_L0A__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S5eSaS5dS13S9S5cS15S9A1A3S13S10S3dS15S10A1A3A4").
Lemma Cert1m_L0A : ltac2:(tb__ "0|0|
SbS14S3bSaS5dS13S9S5cS15S9A1A3S46S13S10S3dS15S10A1A3S2cA6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_L0A] exits1_L0A Cert1m_L0A__runs); [unfold Cert1m_L0A__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_L0A : ltac2:(tb__ "0|2|
SbS14S3cSaS5dS13S9S5cS15S9A1A3S46S13S39S3aS3dZ1S21Z0M0A1M1A3S15S39A1A3S69S10S39S10S3aR1G0G1A3LE;S2cA4A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_L0A 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_L0A) Cert1m_L0A__runs); [unfold Cert1m_L0A__runs; reflexivity | vmr]. Qed.

Lemma Wbm_L0A : ltac2:(tb__ "0|0|
SbS14S1eS63S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wcm_L0A : ltac2:(tb__ "0|0|
SbS14S1eS64S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wdm_L0A : ltac2:(tb__ "0|0|
SbS14S1eS65S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma XIm_L0A : ltac2:(tb__ "0|2|
SbS1aS10A1S6cS66S19S1U0M0A1M1S0S24A4S70G0S24A2A2S1cS10S62S19G1S0S24A4A2A3"). Proof. vmr. Qed.

Section ML0A.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S4cU0S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_L0A : ltac2:(tb__ "0|1|
S9OF_;S52OF_;S4dS4S1dS1dS17S4fQ40A1A1S51S5R5A1S45Vsegs;R8S44R6A1A3S49R6R5A2S4aU0M0S0RbRaR9R8R6S26S29R4AaS4aG0S0RcRbRaR9R7S27S2aR5AaS47RdRcRbRaR8S25R6A7S47ReRdRcRbR9S28R7A7S47RfReRdRcRaS2bR8A7S1dS54Vsegs;R10S43Vsegs;VJFi;S16RfReRcA4S3dR1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L0A rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L0A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_L0A C3_L0A Ems_L0A C4_L0A TM0_L0A run4_L0A RM_L0A D3_L0A W3_L0A EQ3_L0A NX3b_L0A RUN4_L0A L4_L0A D4_L0A W4_L0A EQ4_L0A
             HeM_L0A HchkM_L0A HTM_L0A FBM_L0A ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L0A.
    apply (f0_s5 0%nat st q_L0A false TM_L0A Eq_L0A EQ_L0A TQ0_L0A run5_L0A RQ_L0A NX5_L0A RUN5_L0A L5_L0A AXQ_L0A HeQ_L0A HchkQ_L0A HTQ_L0A FBQ_L0A
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L0A.
    apply (f0_s6 0%nat st false TQ_L0A Edr_L0A Xf_L0A run6_L0A NX6_L0A RUN6_L0A L6_L0A ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 0%nat st true PMID_L0A exits1_L0A Cert1m_L0A ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L0A in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_L0A_1 C2_L0A_1 EfD_L0A_1 ED_L0A_1 run2_L0A_1 D2_L0A_1 W2_L0A_1 NX2_L0A_1 EQ2_L0A_1 RUN2_L0A_1 L2_L0A_1 AXD_L0A_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0A_1 TDr_L0A_1 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_1 ENTD_L0A_1 RUN3_L0A L3_L0A NX3_L0A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_L0A_2 C2_L0A_2 EfD_L0A_2 ED_L0A_2 run2_L0A_2 D2_L0A_2 W2_L0A_2 NX2_L0A_2 EQ2_L0A_2 RUN2_L0A_2 L2_L0A_2 AXD_L0A_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0A_2 TDr_L0A_2 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_2 ENTD_L0A_2 RUN3_L0A L3_L0A NX3_L0A
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_L0A : ltac2:(tb__ "0|1|
S9OF_;S4dS4S1dS1dS17S4fQ40A1A1S52OF_;S5R5A1S49R5R4A2S4bU0M0S0R9R8R7R5S26S29R3A9S4bG0S0RaR9R8R6S27S2aR4A9S48RbRaR9R7S25R5A6S48RcRbRaR8S28R6A6S48RdRcRbR9S2bR7A6S1dS53Vsegs;S43Vsegs;VJFi;S16ReRdRbA4S3dR1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L0A rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L0A rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_L0A C3_L0A Ems_L0A C4_L0A TM0_L0A run4_L0A RM_L0A D3_L0A W3_L0A EQ3_L0A NX3b_L0A RUN4_L0A L4_L0A D4_L0A W4_L0A EQ4_L0A
             HeM_L0A HchkM_L0A HTM_L0A FBM_L0A A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L0A.
    apply (ef0_s5 0%nat st q_L0A false TM_L0A Eq_L0A EQ_L0A TQ0_L0A run5_L0A RQ_L0A NX5_L0A RUN5_L0A L5_L0A AXQ_L0A HeQ_L0A HchkQ_L0A HTQ_L0A FBQ_L0A
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L0A.
    apply (ef0_s6 0%nat st false TQ_L0A Edr_L0A Xf_L0A run6_L0A NX6_L0A RUN6_L0A L6_L0A A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 0%nat st true PMID_L0A exits1_L0A (eq_refl : (GW <=? ss_next (ax_S PMID_L0A))%positive = true) ECert1m_L0A A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L0A in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_L0A_1 C2_L0A_1 EfD_L0A_1 ED_L0A_1 run2_L0A_1 D2_L0A_1 W2_L0A_1 NX2_L0A_1 EQ2_L0A_1 RUN2_L0A_1 L2_L0A_1 AXD_L0A_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0A_1 TDr_L0A_1 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_1 ENTD_L0A_1 RUN3_L0A L3_L0A NX3_L0A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_L0A_2 C2_L0A_2 EfD_L0A_2 ED_L0A_2 run2_L0A_2 D2_L0A_2 W2_L0A_2 NX2_L0A_2 EQ2_L0A_2 RUN2_L0A_2 L2_L0A_2 AXD_L0A_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0A_2 TDr_L0A_2 CD_L0A Eps_L0A Ebg_L0A run3_L0A AXDr_L0A_2 ENTD_L0A_2 RUN3_L0A L3_L0A NX3_L0A
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SfS3eS71R2A2ScS3fS37R2A2S40R2S38A2A2A2SeF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SdS73R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SdS72R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2ScSdScS3fS37R2A2S40R2S38A2A2A1SdScS3fZ180e88R2A2S40R2Z180e8cA2A2A1A2F_;Fa;").

Theorem free_lo_ia0_0A : ltac2:(tb__ "0|7|
S52OF_;S4dS4S1dS17S4fQ40M0A1A1S50G0S1fR2PcA2A2S9S50G0S1fR3PdA2A2S9S30SaS42R4R3S13S1bS10S2fA2M1S18S10S2fS8S2S1U0A1M2S0A3M3S3S36SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S51S5R6A1S45SaR9S44R7A1A3S6bSaRaS44R8A1A3S3fS41R6R5A2S67A2SbS14S4eRbA1S19A3S34S24RcA2S1dS9S33S61R10S31R10ReRcRbR2R1A6R3A3S60S35R11A1R4RdRcR3R2A6SbS9S32R3A1S68A3S49R6S31S35R13A1R6RfReR5R4A6A2S47S5fVCST;VXGL;S35R14A1M6A3R15G6R13S31G6R7R10RfR6R5A6S25S30SaS42R7R11S13G1S18S10S2fG3S3G4VCST;VXGL;G6R13A5A4G5A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S6eRfRdA2S54SaR10S43SaS7G4G2S0RfReA5S6S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 0 Wai_L0A Dai_L0A Wbi_L0A Wci_L0A Certi_L0A ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 0) UStopLe q_L0A (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe q_L0A HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid false 0 UStopLe q_L0A Wbm_L0A Wcm_L0A Wdm_L0A Fb_L0A XIm_L0A A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_L0A (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_L0A_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L0A_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_L0A CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_L0A CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_ia0_0A : ltac2:(tb__ "0|7|
S4dS4S1dS17S4fQ40M0A1A1S50G0S1fR2PcA2A2S9S50G0S1fR3PdA2A2S9S30SaS42R4R3S13S1bS10S2fA2M1S18S10S2fS8S2S1U0A1M2S0A3M3S3S36SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S51S5R6A1S3fS41R4R3A2S67A2SbS14S4eR9A1S19A3S34S24RaA2S1dS9S33S61ReS31ReRcRaR9R2R1A6R3A3S60S35RfA1R4RbRaR3R2A6SbS9S32R3A1S68A3S49R6S31S35R11A1R6RdRcR5R4A6A2S48S5fVCST;VXGL;S35R12A1M6A3G6R11S31G6R7ReRdR6R5A6S25S30SaS42R7RfS13G1S18S10S2fG3S3G4VCST;VXGL;G6R11A5A4G5A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S6fRbA1S53SaS43SaS7G4G2S0RdRcA5S6S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 0 Wai_L0A Dai_L0A Wbi_L0A Wci_L0A ECerti_L0A A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 0) UStopLe q_L0A (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe q_L0A HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid false 0 UStopLe q_L0A Wbm_L0A Wcm_L0A Wdm_L0A Fb_L0A XIm_L0A A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_L0A (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_L0A_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L0A_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_L0A CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_L0A CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ML0A.
End F0A_mL0A.

(* [comment removed for export] *)
Module F0A_mL0Be.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "KcA"; "Kc_ok"; "Pre_freeI"; "J_free_preT"; "L_free"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "list"; "pair"; "false"; "option"; "prod"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "swf"; "rw"; "sv"; "SLit"; "sprop"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0Be"; "q_L0Be"; "Ebg_L0Be"; "ED_L0Be_1"; "ED_L0Be_2"; "Edr_L0Be"; "TD_L0Be_1"; "TD_L0Be_2"; "Xf_L0Be"; "exits1_L0Be"; "W_L0Be"; "st_L0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "qcond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "set_inited"; "AInvA"; "IA_BEG"; "IA_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_mL0Be"; "PMID_L0Be"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL0Be"; "contF"; "econtF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "rigF"; "HDF"; "HDFE"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_internal_inited"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates"; "fi_cutpcs"; "MIDx"; "fi_cuts"; "sa_i"; "fi_vcuts"; "sb_i"; "sc_i"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "CASX"; "FUELF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst"; "PMID_fc"; "sb_m"; "sc_m"; "sd_m"; "se_m"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_LO"; "kQuarantineMin"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "drain_sum"; "drain_sumE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "XI";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild"; "IMG_F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8"; "QRD_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ar.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ar.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ay.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.F0A_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.F0A_minit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ay.F0A_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_masm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_qL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d5.F0A_xiL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cl.F0A_dL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dd.F0A_aL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dz.F0A_iL0Be OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.F0A_cL0Be.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Lemma Wai_L0Be : ltac2:(tb__ "0|0|
SbS14S1eS58S1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Dai_L0Be : ltac2:(tb__ "0|5|
SbS1aS1bS17S1bS20S20A2M0A1M1S17S22A1M2A2M3A1S6aS12S6S2S1U0A1M4S0A3A1S58G4S0A2A2S1cG3S18G1G2S13G0S18S20S20S23P18A1S21S6dA1A4S15G0A1A3S15S22A1A4A2A3"). Proof. vmr. Qed.
Lemma Wbi_L0Be : ltac2:(tb__ "0|0|
SbS14S1eS5aS1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Lemma Wci_L0Be : ltac2:(tb__ "0|0|
SbS14S1eS5bS1U0A1S0A2A1S16A3"). Proof. vmr. Qed.
Definition Certi_L0Be__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S5eSaUbb8S55S57U0S0A2A4").
Lemma Certi_L0Be : ltac2:(tb__ "0|1|
SbS14S3bSaUbb8S55S46S57U0M0S0A2S13S10S56S1G0A1S0A2S15S10A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_cuts 0 UStopLe) [MIDx (Wcan 0) UStopLe] Certi_L0Be__runs); [unfold Certi_L0Be__runs; reflexivity | vmr]. Qed.
Lemma ECerti_L0Be : ltac2:(tb__ "0|2|
SbS14S3cSaUbb8S55S46S59U0M0S0A2S13S39S3aS56S1G0A1S0A2Z0M1S21G1A1A3S15S39A1A3A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 3000%nat fi_cutpcs GW (fi_vcuts 0 UStopLe) [mkVNA (MIDx (Wcan 0) UStopLe) 0 (SLit 0)] Certi_L0Be__runs); [unfold Certi_L0Be__runs; reflexivity | vmr]. Qed.

Definition PMID_L0Be : axst := ltac2:(tb__ "0|0|
S62S19S2dS2eS24A4").
Definition Cert1m_L0Be__runs : ltac2:(tb__ "0|0|
S17S1aS17S11A1A1A1") := ltac2:(tb__ "0|0|
S5eSaS5dS13S9S5cS15S9A1A3S13S10S3dS15S10A1A3A4").
Lemma Cert1m_L0Be : ltac2:(tb__ "0|0|
SbS14S3bSaS5dS13S9S5cS15S9A1A3S46S13S10S3dS15S10A1A3S2cA6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runs segsA FUELF [CASX] GW [PMID_L0Be] exits1_L0Be Cert1m_L0Be__runs); [unfold Cert1m_L0Be__runs; reflexivity | vmr]. Qed.
Lemma ECert1m_L0Be : ltac2:(tb__ "0|2|
SbS14S3cSaS5dS13S9S5cS15S9A1A3S46S13S39S3aS3dZ1S21Z0M0A1M1A3S15S39A1A3S69S10S39S10S3aR1G0G1A3LE;S2cA4A6S16A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA FUELF [CASX] GW [mkVNA PMID_L0Be 1 (SLit 0)] (map (fun E => mkVNA E 0 (SLit 0)) exits1_L0Be) Cert1m_L0Be__runs); [unfold Cert1m_L0Be__runs; reflexivity | vmr]. Qed.

Lemma Wbm_L0Be : ltac2:(tb__ "0|0|
SbS14S1eS63S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wcm_L0Be : ltac2:(tb__ "0|0|
SbS14S1eS64S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma Wdm_L0Be : ltac2:(tb__ "0|0|
SbS14S1eS65S1U0A1S0S24A3A1S16A3"). Proof. vmr. Qed.
Lemma XIm_L0Be : ltac2:(tb__ "0|2|
SbS1aS10A1S6cS66S19S1U0M0A1M1S0S24A4S70G0S24A2A2S1cS10S62S19G1S0S24A4A2A3"). Proof. vmr. Qed.

Section ML0Be.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let W : list ulink := Wcan 0.
Let st : ustop := UStopLe.
Let JFi (b : bool) (A : AA) (Kc : KcA) (rho1 : valuation) : jpredA := ltac2:(tb__ "0|0|
S4cU0S0Vb;VA;VKc;Vrho1;A6").

Theorem free_spine_m_L0Be : ltac2:(tb__ "0|1|
S9OF_;S52OF_;S4dS4S1dS1dS17S4fQ40A1A1S51S5R5A1S45Vsegs;R8S44R6A1A3S49R6R5A2S4aU0M0S0RbRaR9R8R6S26S29R4AaS4aG0S0RcRbRaR9R7S27S2aR5AaS47RdRcRbRaR8S25R6A7S47ReRdRcRbR9S28R7A7S47RfReRdRcRaS2bR8A7S1dS54Vsegs;R10S43Vsegs;VJFi;S16RfReRcA4S3dR1RbA5RaA4FrhoP;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fok;Fkeep;").
Proof.
  intros keep ok A Kc rho rho1 tp Q HKc Hok HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Eps_L0Be rhoX tpX) Q)
            /\ (forall rhoX, triple segs ok (SPA segs (JFi false A' Kc rho1') Ebg_L0Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (f0_s4 0%nat st false Eps_L0Be C3_L0Be Ems_L0Be C4_L0Be TM0_L0Be run4_L0Be RM_L0Be D3_L0Be W3_L0Be EQ3_L0Be NX3b_L0Be RUN4_L0Be L4_L0Be D4_L0Be W4_L0Be EQ4_L0Be
             HeM_L0Be HchkM_L0Be HTM_L0Be FBM_L0Be ok A' Kc rho rho1' tpX Q HUS HKc Hok HR').
    intros rhoM tpM. rewrite ETM_L0Be.
    apply (f0_s5 0%nat st q_L0Be false TM_L0Be Eq_L0Be EQ_L0Be TQ0_L0Be run5_L0Be RQ_L0Be NX5_L0Be RUN5_L0Be L5_L0Be AXQ_L0Be HeQ_L0Be HchkQ_L0Be HTQ_L0Be FBQ_L0Be
             ok A' Kc rho1' tpM Q HUS HKc Hok).
    intros rhoQ. rewrite ETQ_L0Be.
    apply (f0_s6 0%nat st false TQ_L0Be Edr_L0Be Xf_L0Be run6_L0Be NX6_L0Be RUN6_L0Be L6_L0Be ok A' Kc rho1' tpM Q HUS HKc Hok).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (f0_s1c 0%nat st true PMID_L0Be exits1_L0Be Cert1m_L0Be ok A Kc rho1 tp Q HUS HKc Hok).
  intros E rhoE HinE. unfold exits1_L0Be in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (f0_s2 0%nat st true S1c_L0Be_1 C2_L0Be_1 EfD_L0Be_1 ED_L0Be_1 run2_L0Be_1 D2_L0Be_1 W2_L0Be_1 NX2_L0Be_1 EQ2_L0Be_1 RUN2_L0Be_1 L2_L0Be_1 AXD_L0Be_1
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0Be_1 TDr_L0Be_1 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_1 ENTD_L0Be_1 RUN3_L0Be L3_L0Be NX3_L0Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
  - apply (f0_s2 0%nat st true S1c_L0Be_2 C2_L0Be_2 EfD_L0Be_2 ED_L0Be_2 run2_L0Be_2 D2_L0Be_2 W2_L0Be_2 NX2_L0Be_2 EQ2_L0Be_2 RUN2_L0Be_2 L2_L0Be_2 AXD_L0Be_2
             ok A Kc rho rho1 tp Q HUS HKc Hok HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (f0_s3 0%nat st false TD_L0Be_2 TDr_L0Be_2 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_2 ENTD_L0Be_2 RUN3_L0Be L3_L0Be NX3_L0Be
             ok A' Kc rho1' tp' Q HUS HKc Hok KP KB rhoX).
Qed.

Theorem efree_spine_m_L0Be : ltac2:(tb__ "0|1|
S9OF_;S4dS4S1dS1dS17S4fQ40A1A1S52OF_;S5R5A1S49R5R4A2S4bU0M0S0R9R8R7R5S26S29R3A9S4bG0S0RaR9R8R6S27S2aR4A9S48RbRaR9R7S25R5A6S48RcRbRaR8S28R6A6S48RdRcRbR9S2bR7A6S1dS53Vsegs;S43Vsegs;VJFi;S16ReRdRbA4S3dR1RaA5R9A3FrhoP;F_;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho1;Frho;FKc;FA;Fkeep;").
Proof.
  intros keep A Kc rho rho1 tp Q HKc HR HD1 HD2 HBIG HQ3 HXF rhoP.
  assert (HUS : stopJ_stable W st) by (first [apply stopJ_stable_le | apply stopJ_stable_nil]).
  assert (KT : forall A' rho1' tpX, depot_onlyKf A A' -> hd_link keep rho1 rho1' ->
            (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Eps_L0Be rhoX tpX) Q)
            /\ (forall rhoX, etriple segs (SPA segs (JFi false A' Kc rho1') Ebg_L0Be rhoX tpX) Q)).
  { intros A' rho1' tpX HDO HL. pose proof (rigF_hd keep rho rho1 rho1' HR HL) as HR'. split; [|intros rhoX; exact (HBIG A' rho1' rhoX tpX HDO HL)].
    apply (ef0_s4 0%nat st false Eps_L0Be C3_L0Be Ems_L0Be C4_L0Be TM0_L0Be run4_L0Be RM_L0Be D3_L0Be W3_L0Be EQ3_L0Be NX3b_L0Be RUN4_L0Be L4_L0Be D4_L0Be W4_L0Be EQ4_L0Be
             HeM_L0Be HchkM_L0Be HTM_L0Be FBM_L0Be A' Kc rho rho1' tpX Q HUS HKc HR').
    intros rhoM tpM. rewrite ETM_L0Be.
    apply (ef0_s5 0%nat st q_L0Be false TM_L0Be Eq_L0Be EQ_L0Be TQ0_L0Be run5_L0Be RQ_L0Be NX5_L0Be RUN5_L0Be L5_L0Be AXQ_L0Be HeQ_L0Be HchkQ_L0Be HTQ_L0Be FBQ_L0Be
             A' Kc rho1' tpM Q HUS HKc).
    intros rhoQ. rewrite ETQ_L0Be.
    apply (ef0_s6 0%nat st false TQ_L0Be Edr_L0Be Xf_L0Be run6_L0Be NX6_L0Be RUN6_L0Be L6_L0Be A' Kc rho1' tpM Q HUS HKc).
    - intros rhoE. exact (HQ3 A' rho1' rhoE tpM HDO HL).
    - intros rhoE. exact (HXF A' rho1' rhoE tpM HDO HL). }
  apply (ef0_s1c 0%nat st true PMID_L0Be exits1_L0Be (eq_refl : (GW <=? ss_next (ax_S PMID_L0Be))%positive = true) ECert1m_L0Be A Kc rho1 tp Q HUS HKc).
  intros E rhoE HinE. unfold exits1_L0Be in HinE. destruct HinE as [<-|[<-|[]]].
  - apply (ef0_s2 0%nat st true S1c_L0Be_1 C2_L0Be_1 EfD_L0Be_1 ED_L0Be_1 run2_L0Be_1 D2_L0Be_1 W2_L0Be_1 NX2_L0Be_1 EQ2_L0Be_1 RUN2_L0Be_1 L2_L0Be_1 AXD_L0Be_1
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD1. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0Be_1 TDr_L0Be_1 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_1 ENTD_L0Be_1 RUN3_L0Be L3_L0Be NX3_L0Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
  - apply (ef0_s2 0%nat st true S1c_L0Be_2 C2_L0Be_2 EfD_L0Be_2 ED_L0Be_2 run2_L0Be_2 D2_L0Be_2 W2_L0Be_2 NX2_L0Be_2 EQ2_L0Be_2 RUN2_L0Be_2 L2_L0Be_2 AXD_L0Be_2
             A Kc rho rho1 tp Q HUS HKc HR).
    intros rhoD. apply HD2. intros A' rho1' rhoX tp' HDO HL. destruct (KT A' rho1' tp' HDO HL) as [KP KB].
    exact (ef0_s3 0%nat st false TD_L0Be_2 TDr_L0Be_2 CD_L0Be Eps_L0Be Ebg_L0Be run3_L0Be AXDr_L0Be_2 ENTD_L0Be_2 RUN3_L0Be L3_L0Be NX3_L0Be
             A' Kc rho1' tp' Q HUS HKc KP KB rhoX).
Qed.

Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTF : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SfS3eS71R2A2ScS3fS37R2A2S40R2S38A2A2A2SeF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SdS73R2A1A1F_;Fa;").
Hypothesis HCSTQ : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2SdS72R2A1A1F_;Fa;").
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S9S3eVCST;R1A2ScSdScS3fS37R2A2S40R2S38A2A2A1SdScS3fZ180e88R2A2S40R2Z180e8cA2A2A1A2F_;Fa;").

Theorem free_lo_ia0_0Be : ltac2:(tb__ "0|7|
S52OF_;S4dS4S1dS17S4fQ40M0A1A1S50G0S1fR2PcA2A2S9S50G0S1fR3PdA2A2S9S30SaS42R4R3S13S1bS10S2fA2M1S18S10S2fS8S2S1U0A1M2S0A3M3S3S36SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S51S5R6A1S45SaR9S44R7A1A3S6bSaRaS44R8A1A3S3fS41R6R5A2S67A2SbS14S4eRbA1S19A3S34S24RcA2S1dS9S33S61R10S31R10ReRcRbR2R1A6R3A3S60S35R11A1R4RdRcR3R2A6SbS9S32R3A1S68A3S49R6S31S35R13A1R6RfReR5R4A6A2S47S5fVCST;VXGL;S35R14A1M6A3R15G6R13S31G6R7R10RfR6R5A6S25S30SaS42R7R11S13G1S18S10S2fG3S3G4VCST;VXGL;G6R13A5A4G5A3A5A7F_;F_;F_;F_;Fjv;Ft;Frho2;S6eRfRdA2S54SaR10S43SaS7G4G2S0RfReA5S6S2G2S0A3RdRcA5R9A4F_;F_;F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp p n Q HKc Hok Hokp HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (triple_pre_pure segsA ok _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (triple_pre_pure segsA ok _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (fi_prefix 0 Wai_L0Be Dai_L0Be Wbi_L0Be Wci_L0Be Certi_L0Be ok A Kc rho tp Q p n t jv Hii HKc Hok).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (triple_pre_pure segsA ok _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 0) UStopLe q_L0Be (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe q_L0Be HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros k Hg w Hw.
  destruct (f_instantiate_mid false 0 UStopLe q_L0Be Wbm_L0Be Wcm_L0Be Wdm_L0Be Fb_L0Be XIm_L0Be A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (free_spine_m_L0Be (KEEPD CST XGL A1) ok A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc Hok HR
           (hdf_L0Be_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp) (hdf_L0Be_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC ok _ Hok Hokp)
           (HBIG rho2 t jv ML HTJ JM HR)
           (f0_drain_L0Be CST XGL HCST HXGL HCSTQ HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc Hok HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (f0_exit_L0Be CST XGL HCST HXGL HCSTF ok A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) k Hg w Hw1).
Qed.

Theorem efree_lo_ia0_0Be : ltac2:(tb__ "0|7|
S4dS4S1dS17S4fQ40M0A1A1S50G0S1fR2PcA2A2S9S50G0S1fR3PdA2A2S9S30SaS42R4R3S13S1bS10S2fA2M1S18S10S2fS8S2S1U0A1M2S0A3M3S3S36SaA1M4VCST;VXGL;R6R5A5A4S15G1A1M5A3A5S51S5R6A1S3fS41R4R3A2S67A2SbS14S4eR9A1S19A3S34S24RaA2S1dS9S33S61ReS31ReRcRaR9R2R1A6R3A3S60S35RfA1R4RbRaR3R2A6SbS9S32R3A1S68A3S49R6S31S35R11A1R6RdRcR5R4A6A2S48S5fVCST;VXGL;S35R12A1M6A3G6R11S31G6R7ReRdR6R5A6S25S30SaS42R7RfS13G1S18S10S2fG3S3G4VCST;VXGL;G6R11A5A4G5A3A5A6F_;F_;F_;F_;Fjv;Ft;Frho2;S6fRbA1S53SaS43SaS7G4G2S0RdRcA5S6S2G2S0A3RbRaA5R7A3F_;F_;F_;F_;F_;F_;TQ;Tn;Tp;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp p n Q HKc HHI Hii QC HBIG HDS. pose proof (cls_hyp_blk false p n HHI) as HCL.
  apply (etriple_pre_pure segsA _ _ (budget_ok_free A)); [intros w Hw; exact (entry_budget _ _ A Kc rho tp w Hw)|]. intros HBud.
  apply (etriple_pre_pure segsA _ _ (In (p, n) (aa_live A) /\ exists tp0 md0, AInvA segsA A rho tp0 md0)).
  { intros w [_ HJ]. destruct HJ as (HA & _ & HL & _). split; [exact HL | exists tp, (cfg_model (w_cfg w)); exact HA]. }
  intros (HL & tp0 & md0 & HA0).
  destruct (blkF_mem A rho tp0 md0 p n HA0 HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp0 md0 HA0) as (jv & JM & Hjv).
  assert (HTJ0 : tjv_ok A rho p n t jv) by exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv).
  apply (efi_prefix 0 Wai_L0Be Dai_L0Be Wbi_L0Be Wci_L0Be ECerti_L0Be A Kc rho tp Q p n t jv Hii HKc).
  intros rho2 ML. set (A1 := set_inited A).
  pose proof (tjv_ok_mid A rho rho2 tp0 md0 p n t jv HA0 HL ML HTJ0) as HTJ. fold A1 in HTJ.
  pose proof ML as (AG & _ & RMO).
  assert (EID : rhoF_of A1 rho2 p n t jv = rho2) by exact (rhoF_of_id A rho rho2 p n t jv AG).
  assert (E12 : bv_unsigned (rw rho2 12%positive) = p) by (rewrite <- (proj1 AG 12%positive) by (unfold GW; lia); reflexivity).
  assert (E13 : bv_unsigned (rw rho2 13%positive) = n) by (rewrite <- (proj1 AG 13%positive) by (unfold GW; lia); reflexivity).
  assert (AGNF : agree_vals NF rho rho2).
  { pose proof (rhoF_agree A rho p n t jv) as (Rw & Rl & _). destruct AG as [Gw Gl].
    split; [intros i Hi; rewrite (Rw i Hi); apply Gw; unfold NF, GW in *; lia | intros l; rewrite (Rl l); apply Gl]. }
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (post_mid CST XGL HCST HXGL HCST2 0 A Kc rho rho2 tp tp0 md0 w HA0 AGNF RMO Hw) |].
  apply (etriple_pre_pure segsA _ _ (exists tp1 md1, AInvA segsA A1 rho2 tp1 md1)).
  { intros w [_ HJ]. destruct HJ as (HA & _). exists tp, (cfg_model (w_cfg w)). exact HA. }
  intros (tp1 & md1 & HA1).
  assert (IFF : instF_facts false (Wcan 0) UStopLe q_L0Be (rhoF_of A1 rho2 p n t jv) p n (N8 n) (topG (aa_geom A1))).
  { destruct HTJ as [HT HJV]. exact (instF_here A1 rho2 tp1 md1 p n HA1 HL HCL eq_refl E12 E13 t HT jv HJV false (Wcan 0) UStopLe q_L0Be HHI QC). }
  assert (AGB : agree_below NW2 rho2 (rhoF_of A1 rho2 p n t jv)) by (rewrite EID; apply agree_below_refl).
  intros w Hw.
  destruct (f_instantiate_mid false 0 UStopLe q_L0Be Wbm_L0Be Wcm_L0Be Wdm_L0Be Fb_L0Be XIm_L0Be A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp w p n (N8 n)
              ltac:(intros E; discriminate E) (stopJ_stable_le _) AGB IFF Hw) as [HR Hw1].
  exact (efree_spine_m_L0Be (KEEPD CST XGL A1) A1 Kc rho2 (rhoF_of A1 rho2 p n t jv) tp _ HKc HR
           (hdfe_L0Be_1 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _) (hdfe_L0Be_2 CST XGL HCST HXGL HCSTD A1 Kc rho2 tp1 md1 _ _ t jv HKc HA1 HL HCL E12 HTJ QC _)
           (HBIG rho2 t jv ML HTJ JM HR)
           (ef0_drain_L0Be CST XGL HCST HXGL HCSTQ HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) HKc HDS HBud E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (ef0_exit_L0Be CST XGL HCST HXGL HCSTF A1 Kc rho2 tp p n t jv (KEEPD CST XGL A1) E12 E13 HL HCL eq_refl QC HR JM (fun a H => H))
           (rhoF_of A1 rho2 p n t jv) w Hw1).
Qed.
End ML0Be.
End F0A_mL0Be.

