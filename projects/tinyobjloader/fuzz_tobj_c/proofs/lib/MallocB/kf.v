(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz k6 F0A_skeln kj km.

(* [comment removed for export] *)
Module SpineMallocSec6ILW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "ax_X"; "la_state"; "entailsA"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "cell"; "ss_next"; "ss_facts"; "swf"; "SLit"; "ss_objs"; "sprop_below"; "SVar"; "DUnknown"; "mkObj"; "SPNot"; "sstate"; "DZero"; "SAlu"; "SPBranch"; "c_off"; "c_val"; "ob_cells"; "sv_eqb"; "@Corelib.Init.Datatypes"; "true"; "bool"; "nil"; "cons"; "list"; "prod"; "app"; "nat"; "option"; "pair"; "Some"; "length"; "false"; "andb"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3ILW2"; "nx0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "find"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7"; "KEPTF"; "KUB"; "idxsF"; "idxsU"; "S2F"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV"; "O_UBs"; "F_par"; "UBs"; "osplit"; "O_3"; "perm7"; "F_A"; "L3"; "O_3b"; "PGST"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "B3"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "a0e7"; "a2e6"; "a2e7"; "a2e8"; "fx8"; "sel7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.SpineMallocSec6ILW2.INST"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "mcfa"; "mcfb"; "mcqa"; "mcqb"; "CT6a"; "CT6b"; "CT7a"; "CT7b"; "CT8a"; "CT8b"; "CO6a"; "CO6b"; "CO8a"; "CO8b"; "swcfa"; "swcfb"; "swcqa"; "swcqb"; "CM7a"; "CM7b"; "D6La"; "D6Lb"; "D7La"; "D7Lb"; "D8La"; "D8Lb"; "S9bfa"; "S9bfb"; "S9bqa"; "S9bqb"; "E9pa"; "E9pb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "c1fa"; "c1fb"; "c1qa"; "c1qb"; "FXPa"; "FXPb"; "n7a"; "n7b"; "D6a"; "D6b"; "D7a"; "D7b"; "D8a"; "D8b"; "CO7a"; "CO7b"; "CO9pa"; "CO9pb"; "E6a"; "E6b"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "PXa"; "PXb"; "tybfa"; "tybfb"; "tybqa"; "tybqb"; "C5Aa"; "C5Ab"; "CR7a"; "CR7b"; "CS7a"; "CS7b"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "R6a"; "R6b"; "R7a"; "R7b"; "R8a"; "R8b"; "R9fa"; "R9fb"; "R9qa"; "R9qb"; "T6a"; "T6b"; "T7a"; "T7b"; "T8a"; "T8b"; "T9fa"; "T9fb"; "T9qa"; "T9qb"; "s6a"; "s6b"; "s7a"; "s7b"; "s8a"; "s8b"; "s9fa"; "s9fb"; "s9qa"; "s9qb"; "sFfa"; "sFfb"; "sFqa"; "sFqb"; "E9fa"; "E9fb"; "E9qa"; "E9qb"; "S9afa"; "S9afb"; "S9aqa"; "S9aqb"; "Y6Aa"; "Y6Ab"; "iMfa"; "iMfb"; "iMqa"; "iMqb"; "s6Aa"; "s6Ab"; "c2fa"; "c2fb"; "c2qa"; "c2qb"; "c4fa"; "c4fb"; "c4qa"; "c4qb";
"c5fa"; "c5fb"; "c5qa"; "c5qb"; "run6Aa"; "run6Ab"; "run7a"; "run7b"; "run8a"; "run8b"; "run9a"; "run9b"; "run9qa"; "run9qb"; "runFfa"; "runFfb"; "runFqa"; "runFqb"; "xcfa"; "xcfb"; "xcqa"; "xcqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "AE_A"; "L_malloc_ok"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST"; "O_1"; "Pret_ms"; "carveS"; "BR"; "O_2"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "SKEL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec6L"; "F_low"; "F_g7L"; "F_g8L"; "F_g9L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_NRES"; "V_NCH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "isSome"; "omrg"; "oreb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineMallocSec5ILW2"; "C5ac"; "C5bc"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4ILW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineMallocSec5ILW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7.
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
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

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
Module SpineMallocSec6IW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "ax_setS"; "la_state"; "entailsA"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "cell"; "ss_next"; "ss_facts"; "swf"; "SLit"; "sprop_below"; "ss_objs"; "SVar"; "DUnknown"; "mkObj"; "SPNot"; "sstate"; "DZero"; "SAlu"; "SPBranch"; "c_off"; "c_val"; "ob_cells"; "sv_eqb"; "@Corelib.Init.Datatypes"; "true"; "bool"; "nil"; "cons"; "list"; "prod"; "app"; "nat"; "option"; "pair"; "Some"; "length"; "false"; "andb"; "S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IW2"; "nx0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "existsb"; "find"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7"; "KEPTF"; "KUB"; "idxsF"; "idxsU"; "S2F"; "XF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA"; "runsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV"; "O_UBs"; "F_par"; "UBs"; "osplit"; "O_3"; "perm7"; "F_A"; "F_B"; "L3"; "O_3b"; "PGST"; "RSF"; "ic_c1"; "ic_c2"; "ic_nch"; "ic_nres"; "ic_pg"; "ic_rs"; "mc_cptr"; "mc_idx"; "mc_magic"; "mc_map"; "mc_ms"; "mc_ns"; "mc_size"; "mc_sizehi"; "mc_state"; "mc_type"; "B3"; "B4"; "BP9"; "F_g7"; "F_g8"; "F_g9"; "L3b"; "O_4z"; "a0e7"; "a2e6"; "a2e7"; "a2e8"; "fx8"; "sel7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.SpineMallocSec6IW2.INST"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "mcfa"; "mcfb"; "mcqa"; "mcqb"; "CT6a"; "CT6b"; "CT7a"; "CT7b"; "CT8a"; "CT8b"; "CO6a"; "CO6b"; "CO8a"; "CO8b"; "swcfa"; "swcfb"; "swcqa"; "swcqb"; "CM7a"; "CM7b"; "S9bfa"; "S9bfb"; "S9bqa"; "S9bqb"; "E9pa"; "E9pb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "c1fa"; "c1fb"; "c1qa"; "c1qb"; "FXPa"; "FXPb"; "n7a"; "n7b"; "E6a"; "E6b"; "CO7a"; "CO7b"; "CO9pa"; "CO9pb"; "D6a"; "D6b"; "D7a"; "D7b"; "D8a"; "D8b"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "PXa"; "PXb"; "tybfa"; "tybfb"; "tybqa"; "tybqb"; "C5Aa"; "C5Ab"; "C5Ba"; "C5Bb"; "CR7a"; "CR7b"; "CS7a"; "CS7b"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "R6a"; "R6b"; "R7a"; "R7b"; "R8a"; "R8b"; "R9fa"; "R9fb"; "R9qa"; "R9qb"; "T6a"; "T6b"; "T7a"; "T7b"; "T8a"; "T8b"; "T9fa"; "T9fb"; "T9qa"; "T9qb"; "s6a"; "s6b"; "s7a"; "s7b"; "s8a"; "s8b"; "s9fa"; "s9fb"; "s9qa"; "s9qb"; "sFfa"; "sFfb"; "sFqa"; "sFqb"; "E9fa"; "E9fb"; "E9qa"; "E9qb"; "S9afa"; "S9afb"; "S9aqa"; "S9aqb"; "Y6Aa"; "Y6Ab"; "Y6Ba"; "Y6Bb"; "iMfa"; "iMfb"; "iMqa"; "iMqb"; "s6Aa"; "s6Ab"; "s6Ba"; "s6Bb"; "c2fa"; "c2fb"; "c2qa"; "c2qb"; "c4fa"; "c4fb"; "c4qa";
"c4qb"; "c5fa"; "c5fb"; "c5qa"; "c5qb"; "run6Aa"; "run6Ab"; "run6Ba"; "run6Bb"; "run7a"; "run7b"; "run8a"; "run8b"; "run9a"; "run9b"; "run9qa"; "run9qb"; "runFfa"; "runFfb"; "runFqa"; "runFqb"; "xcfa"; "xcfb"; "xcqa"; "xcqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "AE_A"; "L_malloc_ok"; "V_RES"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST"; "O_1"; "Pret_ms"; "carveS"; "BR"; "O_2"; "Pret_mz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "SKEL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "Pre_mszA"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_NRES"; "V_NCH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall"; "isSome"; "omrg"; "oreb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineMallocSec5IW2"; "C5ac"; "C5bc"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "leb"; "ltb"; "modulo"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4IW2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.SpineMallocSec5IW2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7.
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
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

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
Module F0T_skeln.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "rhoF_of"; "j_min"; "junkF"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "list"; "true"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "cls_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot"; "tjv_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "rigF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_skeln"; "QFNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineMax"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "AE_A"; "JL_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "aa_live"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln"; "contN"; "econtN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition QFNT (CST XGL : list (Z * Z)) (A : AA) (Kc : KcA) (rho : valuation) (tp : list word) : assn := ltac2:(tb__ "0|1|
S16S5S29Vrho;Vtp;S10ScS14S15A2M0SbS14S15S2dS21A1S22S2eS5A1VCST;VXGL;VA;VKc;A5A4S11G0A1A3A5").
Definition HBIGNT_stmt (CST XGL : list (Z * Z)) (khi : bool) (E : axst) : Prop := ltac2:(tb__ "0|1|
S28OF_;S23S1dS4SeSaQ40M0A1A1S0S0S0S8S0OF_;S1eR8A1S13S5RbS12R9A1A3S2aS5RcS12RaA1A3S1S0S9G0S3RaPcA2A2R8A3S1S0S9G0S3RbPdA2A2R8A3S26ScS0S0A2SbS0S0RaR9A4S25ReA1A3S17Vkhi;RbRaA3S1SdS24R10A1SfA3S27S1bRcA2S18R12R10ReRdRcRbA6S19R11S6R13R11RfReRdRcA6A2S1S0S7RdA1S1cA3S0S2S1fVCST;R16R1A3S20VCST;VXGL;R16R1A4A2RfR2A1F_;Fa;S2bU0ReR17R16R15S6R16R14R12R11R10RfA6VE;S1aVCST;VXGL;R16R15R14R13A6A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;Fok;").
Definition HBIGNET_stmt (CST XGL : list (Z * Z)) (khi : bool) (E : axst) : Prop := ltac2:(tb__ "0|1|
S23S1dS4SeSaQ40M0A1A1S0S0S0S8S0OF_;S1eR8A1S1S0S9G0S3R8PcA2A2R6A3S1S0S9G0S3R9PdA2A2R6A3S26ScS0S0A2SbS0S0R8R7A4S25RcA1A3S17Vkhi;R9R8A3S1SdS24ReA1SfA3S27S1bRaA2S18R10ReRcRbRaR9A6S19RfS6R11RfRdRcRbRaA6A2S1S0S7RbA1S1cA3S0S2S1fVCST;R14R1A3S20VCST;VXGL;R14R1A4A2RdR2A1F_;Fa;S2cU0RcR14R13S6R14R12R10RfReRdA6VE;S1aVCST;VXGL;R14R13R12R11A6A7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fkeep;Fjv;Ft;Fn;Fp;Ftp;Frho;FKc;FA;").
End F0T_skeln.

(* [comment removed for export] *)
Module F0A_hbN_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "false"; "pair"; "bool"; "nil"; "app"; "prod"; "list"; "length"; "negb"; "true"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sprop"; "sv"; "SLit"; "SPUle"; "SAlu"; "SPUlt"; "SPAlign"; "SPBranch"; "SPNot"; "SVar"; "ob_base"; "ob_lo"; "ss_facts"; "ss_objs"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states"; "vH"; "vMS"; "dropD"; "setpc"; "vNCH"; "vPTR"; "O_secg"; "O_secm"; "O_secn"; "O_secs"; "TOPMAX"; "addos"; "jregs"; "vEND"; "F_h"; "F_len"; "GBEXIT"; "GBSCAN"; "LENS"; "MSENTS"; "OBJ2"; "O_chS"; "O_cidx"; "O_clast"; "O_csh"; "O_hh"; "O_hidx"; "O_lidx"; "O_seci"; "dropk"; "vCHV"; "vIDX"; "vNEAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states"; "mT"; "s5_hb"; "D_U_hb"; "F1_hb"; "F2_hb"; "F_qsz"; "Fm_hb"; "O_qsz"; "R5_hb"; "T5_hb"; "XEX_hb"; "XO_hb"; "exit_perm_hb"; "hb_vars"; "is_botwin"; "vRISh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs"; "idx_where"; "is_image"; "is_link"; "is_winpiece"; "memN"; "n_pieces"; "sort_by"; "win_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "memset_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel"; "addf"; "addo"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXSelect"; "@Corelib.Lists.ListDef"; "map"; "nth"; "repeat"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "O_blkN"; "O_hdr"; "O_sh"; "axf"; "cQ"; "optR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "HIGH_SHADOW_END"; "kQuarantineCacheMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "stack_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue"; "notin_vars"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln.
Import ListNotations.
Open Scope Z_scope.

Definition RET_PUT : Z := 0x408d8.
Definition mT : sv := SAlu ALU_ADD (SVar 12) (SLit (-16)).

Definition vRISh : sv := SVar 195.
Definition XO_hb : list sobj := ltac2:(tb__ "0|6|
S0SfS62S12Z0A1M0Zeaa80M1Zeaa84S0S7S7SdS1A2M2S11A2M3S3G2S11S3SdS1G1U4A4S12ZffffffffA1A4S5G3A1M4A3A4S0SfS62G0Zeaa88M5Zeaa91S0G3S3G2S11S3SdS1G5U8A4S56A4S0G3S3G2S11S3SdS1Zeaa90U1A4G0A4G4A3A3A4S0SfS3bS0SfS27S0SfS28S0SfS26S0SfS25S5SfA1A3A3A3A3A3A3A3").
Definition Fm_hb (f : nat) : list sprop := ltac2:(tb__ "0|3|
S1S8S10A1M0Lf;Vf;S0S10S15S47S5fA2S5S10A1M1A3M2S1S1G0Ln;R1G2S1S0S10S13S14S43S5fS12S65Z2Z25A2A1A3S47A2G1A3Ln0;X1x2Ln;X1x2").
Definition F1_hb (f : nat) : list sprop := ltac2:(tb__ "0|1|
S6S10S4dVf;A1S0S10S13S12S7bA1S5fA2S0S10S13S5fS12S66S66S29S65Z2M0Z25A2A2Z1000A2A1A2S0S10S18S17S44S23S12Z0A1A3A1S0S10S13S23S12S65G0Z14A2A1A2S5S10A1A3A3A3A3A3").
Definition F2_hb (f : nat) (l : bool) : list sprop := ltac2:(tb__ "0|4|
S6S10S0S10S2eS0S10S18S17S44S1fS12Z0A1A3A1S0S10S13S1fS47A2S0S10S15S47S14S43S1fS20A3M0A2S0S10S16PcaZcM1A2S0S10S16PcbG1A2S0S10S13S12Z12000A1S20A2S0S10S13S20S12S29A1M2A2S0S10S13S12Z643000A1S1fA2S0S10S13G0G2A2S0S10S13S14S43S20S1fA3G2A2S5S10A1M3A3A3A3A3A3A3A3A3A3A3A3S6S10S2dVf;A1S4S8S10A1Ll;Vl;G3S0S10S15S3eS14S43S23S12N1A1A3A2G3A3X4x2A3A3").

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
Definition MUNMAP_EC : Z := 0x706ac.   Definition MADVISE_EC : Z := 0x706e4.

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
Module F0T_cLNT.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "andb"; "list"; "false"; "negb"; "Some"; "option"; "prod"; "pair"; "length"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVN"; "VFN"; "BIGF"; "rd_okG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_next"; "swf"; "sobj"; "ss_lenient"; "sprop_eqb"; "ss_facts"; "SVar"; "SLit"; "ss_objs"; "sprop_below"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "entsF"; "BIGX"; "DEPE"; "PSE"; "CASX"; "leaves_at"; "CD_of"; "F_typ"; "XD"; "XDr"; "casx"; "set_factsF"; "vH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "UStopLe"; "AE_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_cLNT"; "C2_LNT"; "ED_LNT"; "LT_LNT"; "Ebg_LNT"; "S1c_LNT"; "l1_LNT"; "CD_LNT"; "EX_LNT"; "P0_LNT"; "run3_LNT"; "Erc_LNT"; "LH0_LNT"; "RD_LNT"; "TDr_LNT"; "l2_LNT"; "l3_LNT"; "l4_LNT"; "run2_LNT"; "EfD_LNT"; "Eps_LNT"; "TD_LNT"; "l1okb_LNT"; "run4_LNT"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "sDv_of"; "LOOPX"; "PreDv"; "atpc"; "FACTS_Tg"; "F_ext"; "P0T_g"; "PostDv"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln"; "RCYE"; "Erc_of"; "small_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG"; "sa_t"; "sb_t"; "sc_t"; "sd_t"; "se_t"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG"; "dchkbT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_link_state"; "carve_plain_state";
"@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition W_LNT : list ulink := Wcan 0.
Definition st_LNT : ustop := UStopLe.
Definition F0_LNT : list sprop := FACTS_Tg false VFN.
Definition P0_LNT : axst := P0T_g false [] VFN.

Definition l1_LNT : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] P0_LNT.
Definition LH0_LNT : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l1_LNT) DUMMY).
Definition l2_LNT : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] LH0_LNT.
Definition LH1_LNT : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l2_LNT) DUMMY).
Definition LT_LNT : axst := Eval vm_compute in LT_ofg LH1_LNT F0_LNT.
Definition EX_LNT : axst := Eval vm_compute in EX_ofg LH1_LNT F0_LNT.
Definition l3_LNT : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state LT_LNT (SVar pFR)).
Definition l4_LNT : list leafA := Eval vm_compute in runA FUELF [CASX] EX_LNT.
Definition S1c_LNT : axst := Eval vm_compute in S1cT_of (la_state (nth 0 l4_LNT DUMMY)) (F0_LNT ++ F_ext).

Lemma RUN1_LNT : ltac2:(tb__ "0|0|
S0S9S14A1S3cS29S6S2S57S6S2S2eS7S2A1A3A3S47A3S44A3"). Proof. Time vmr. Qed.
Lemma RUN2f_LNT : ltac2:(tb__ "0|0|
S0S9S14A1S3cS29S6S2S57S6S2S5aS7S2A1A3A3S4aA3S4dA3"). Proof. Time vmr. Qed.
Lemma RUN3f_LNT : ltac2:(tb__ "0|0|
S0S9S14A1S3cS29S6S2S57S6S2S5aS7S2A1A3A3S87S41S23S58A1A2A3S4eA3"). Proof. Time vmr. Qed.
Lemma RUN4f_LNT : ltac2:(tb__ "0|0|
S0S9S14A1S3cS29S6S2S2eS7S2A1A3S46A3S4fA3"). Proof. Time vmr. Qed.

Definition l1okb_LNT (l : list leafA) : bool := ltac2:(tb__ "0|1|
S61S14S14S11S8aS27S12S15R1A1M0A1A1S57A2S2aG0S43A2A2LL;Vl;A3").
Lemma chk_LNT : ltac2:(tb__ "0|a|
S0S5S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8SbS9S14A1M0S5Lx;M1S44S4S14G0SaLl0;Ll;M2X9x2A1SbG1S4dS4G2X9x2A1A2SbG1S4eS4G2X9x2A1A2SbG1S4fS4G2X9x2A1A2S54S44A1A2S89S10S14S5cS57S44A2A2U1A2A2S61S14S14S11S2aS15R1A1M3S41A2S2aG3S46A2A2LL;S4dA3A2S1eS12S88S41S23S58A1M4A2A1A1A2S28S1dS12S41A1M5A1M6G4A2A2S61S14S86S41S46S58A3S4eA3A2S61S14S14S2aG3S43A2LL;S4fA3A2S56S3aS1dS12S47A1M7A1A2A2S56S3aS1dS12S4aA1M8A1A2A2S56S3aG6A2A2S56S3aS1dS12S46A1M9A1A2A2SbS20G7A1A1A2SbS20G8A1A1A2SbS20G5A1A1A2SbS20G9A1A1A2S4A3").
Proof. Time vmr. Qed.
Lemma LH0eq_LNT : ltac2:(tb__ "0|0|
S0S13S15S65S14U0S5cS57S44A2S3eA4A1S4aA3"). Proof. vmr. Qed.

Lemma SIDE_LNT : ltac2:(tb__ "0|0|
S0S5S7dS47S41A2S4A3"). Proof. Time vmr. Qed.
Lemma OBND_LNT : ltac2:(tb__ "0|1|
S0S9SeSeS1bS1bA2S1bA2M0A1S64S1fG0S7cS25S12S41A1A1A4S64S1fG0S7cS25S12S47A1A1A4A3"). Proof. Time vmr. Qed.

Definition C2_LNT : axst := C2_of S1c_LNT.
Definition run2_LNT : list leafA := ltac2:(tb__ "0|0|
S3cS29S6S2S2cS7S2A1A3S3fA3").
Definition EfD_LNT : axst := leaf 0 run2_LNT.
Definition ED_LNT : axst := ED_of EfD_LNT.
Definition RD_LNT : list sobj := RDv_of ED_LNT.
Definition TD_LNT : axst := TDv_of ED_LNT.
Definition TDr_LNT : axst := TDr_of TD_LNT.

Definition CD_LNT : axst := ltac2:(tb__ "0|0|
S30S4cA1S13S35R1S63S1cS1cSbS62S1cS21R1A1S5eA3A1Lf;S22S12R1A1A1A3A2TC;").
Definition run3_LNT : list leafA := ltac2:(tb__ "0|0|
S3cS29S6S2S2dS6S2S2bS7S2A1A3A3S45A3").
Definition Eps_LNT : axst := leaf 0 run3_LNT.
Definition Ebg_LNT : axst := leaf 1 run3_LNT.
Definition run4_LNT : list leafA := ltac2:(tb__ "0|0|
S3cS29S6S2S6dS7S2A1A3S42A3").
Definition Erc_LNT : axst := ltac2:(tb__ "0|0|
S6eS3dU0S55A2S22S12S42A1A1A2").

Lemma D2_LNT : ltac2:(tb__ "0|4|
S0SdSeS9SeS1bS1bA2M0A1M1S9S1cA1M2A2M3A1S70S12S43A1S12S3fA1A2ScG3SfG1G2S6G0SfS1bS1bS34S36A4S7G0A1A3S31A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LNT : ltac2:(tb__ "0|1|
S1S0S5S1eS12S3fA1M0A1S4A3S1S0S3S1dG0A1S1dS12S43A1A1A3S0S5S20G0A1SaA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LNT : ltac2:(tb__ "0|0|
S0S5S56S3aS1dS12S3fA1A1A2S4A3"). Proof. vmr. Qed.
Lemma EQ2_LNT : ltac2:(tb__ "0|0|
S0S13S16S43S12S3fA1A2S3fA3"). Proof. vmr. Qed.
Lemma RUN2_LNT : ltac2:(tb__ "0|0|
S0S9S14A1S3cS29S6S2S2cS7S2A1A3S3fA3S50A3"). Proof. unfold run2_LNT; reflexivity. Qed.
Lemma L2_LNT : ltac2:(tb__ "0|0|
S1S0S5S2fS50S6S2S2cS7S2A1A3A2S4A3S0S13S3dU0S50A2S51A3A2"). Proof. Time (split; [vmr | unfold EfD_LNT; reflexivity]). Qed.
Lemma AXD_LNT : ltac2:(tb__ "0|0|
S0SdS13A1S66S51S32A2ScS13S40A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LNT : ltac2:(tb__ "0|1|
S0SdS9S1fA1M0A1S7fS40S5bS59S40A1A3ScG0S4bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LNT : ltac2:(tb__ "0|0|
S0S5S7eS40S5bS59S40A1S4bS6S13S60S7S13A1A3A5S4A3"). Proof. Time vmr. Qed.
Lemma AXDr_LNT : ltac2:(tb__ "0|0|
S0SdS13A1S66S53S33A2ScS13S4cA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LNT : ltac2:(tb__ "0|0|
S0S5S85S4cS45A2S4A3"). Proof. Time vmr. Qed.
Lemma RUN3_LNT : ltac2:(tb__ "0|0|
S0S9S14A1S3cS29S6S2S2dS6S2S2bS7S2A1A3A3S45A3S48A3"). Proof. unfold run3_LNT; reflexivity. Qed.
Lemma L3_LNT : ltac2:(tb__ "0|0|
S1S0S5S2fS48S6S2S2dS6S2S2bS7S2A1A3A3A2S4A3S1S0S13S3dU0S48A2S52A3S0S13S3dU1S48A2S42A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_LNT | unfold Ebg_LNT]; reflexivity]). Qed.
Lemma NX3_LNT : ltac2:(tb__ "0|1|
S1S0S5S56S3aS1dS12S45A1M0A1A2S4A3S0S5S20G0A1SaA3A2"). Proof. split; vmr. Qed.
Lemma SMF_LNT : ltac2:(tb__ "0|0|
S0S5S62S1cS21S6fA1S22S12S52A1A1A3S4A3"). Proof. vmr. Qed.
Lemma BGF_LNT : ltac2:(tb__ "0|1|
S1S0S5S62S1cS21S82A1S22S12S49A1A1M0A3S4A3S0S5S62S1cS21S19A1G0A3S4A3A2"). Proof. split; vmr. Qed.
Lemma NXB_LNT : ltac2:(tb__ "0|0|
S0S5S56S3aS1dS12S42A1A1A2S4A3"). Proof. vmr. Qed.
Lemma CertR_LNT : ltac2:(tb__ "0|1|
S0S5S6bS3bS29S6S2S6dS7S2A1A3S3aS6S13S42S7S13A1M0A3S6S13S49G0A3A6S4A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [RCYE] GW Ebg_LNT [Erc_LNT] run4_LNT); [unfold run4_LNT, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECertR_LNT : ltac2:(tb__ "0|3|
S0S5S6cS3bS29S6S2S6dS7S2A1A3S3aS6S69S6aS42Z1S24Z0M0A1M1A3S7S69A1M2A3S6S69S6aS49G0G1A3G2A3A6S4A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [RCYE] GW (mkVNA Ebg_LNT 1 (SLit 0)) [mkVNA Erc_LNT 0 (SLit 0)] run4_LNT); [unfold run4_LNT, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma DCHK_LNT : ltac2:(tb__ "0|1|
S0S5S83U0M0S1aS17G0A2S40S53S59S40A1S4bA6S4A3"). Proof. Time vmr. Qed.

Lemma Wa_LNT : ltac2:(tb__ "0|0|
S0S5S1eS72S37U0A1A1A1S4A3"). Proof. vmr. Qed.
Lemma Da_LNT : ltac2:(tb__ "0|4|
S0SdSeS9SeS1bS1bA2M0A1M1S9S1cA1M2A2M3A1S70S12S84S39A1A1S72S37U0A1A1A2ScG3SfG1G2S6G0SfS1bS1bS23P18A1S24S81A1A4S7G0A1A3S7S1cA1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_LNT : ltac2:(tb__ "0|0|
S0S5S1eS73S37U0A1S17A2A1S4A3"). Proof. vmr. Qed.
Lemma Wc_LNT : ltac2:(tb__ "0|0|
S0S5S1eS74S37U0A1S17A2A1S4A3"). Proof. vmr. Qed.
Lemma Wd_LNT : ltac2:(tb__ "0|0|
S0S5S1eS75S37U0A1S17A2A1S4A3"). Proof. vmr. Qed.
Lemma Fb_LNT : ltac2:(tb__ "0|0|
S0S5S61S1cS26S80A1S5dSaS18A2A3S4A3"). Proof. vmr. Qed.
Lemma XI_LNT : ltac2:(tb__ "0|1|
S0SdS13A1S66S76SaS37U0M0A1S17S18A4S71G0S10S67S17A2A2A2ScS13S5fSaS64S67S1fS68S17A4S18A3A2A3"). Proof. vmr. Qed.

Definition PMID_LNT : axst := ltac2:(tb__ "0|0|
S77SaS37U0A1S38S7S1fA1S18A5").
Lemma Wbm_LNT : ltac2:(tb__ "0|0|
S0S5S1eS78S37U0A1S38S17A3A1S4A3"). Proof. vmr. Qed.
Lemma Wcm_LNT : ltac2:(tb__ "0|0|
S0S5S1eS79S37U0A1S38S17A3A1S4A3"). Proof. vmr. Qed.
Lemma Wdm_LNT : ltac2:(tb__ "0|0|
S0S5S1eS7aS37U0A1S38S17A3A1S4A3"). Proof. vmr. Qed.
Lemma XIm_LNT : ltac2:(tb__ "0|2|
S0SdS13A1S66S7bSaS37U0M0A1M1S38S17S18A5S71G0S10S67S17A2A2A2ScS13S77SaG1S38S64S67S1fS68S17A4S18A5A2A3"). Proof. vmr. Qed.
End F0T_cLNT.

(* [comment removed for export] *)
Module F0T_cNT.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "andb"; "list"; "negb"; "Some"; "option"; "prod"; "pair"; "false"; "length"; "orb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVN"; "VFN"; "BIGF"; "rd_okG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_next"; "swf"; "sobj"; "ss_lenient"; "sprop_eqb"; "ss_facts"; "SVar"; "SLit"; "ss_objs"; "sprop_below"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "entsF"; "BIGX"; "DEPE"; "PSE"; "CASX"; "leaves_at"; "CD_of"; "F_typ"; "XD"; "XDr"; "casx"; "set_factsF"; "vH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "UStopLe"; "AE_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0T_cNT"; "C2_NT"; "ED_NT"; "LT_NT"; "Ebg_NT"; "S1c_NT"; "l1_NT"; "CD_NT"; "EX_NT"; "P0_NT"; "run3_NT"; "Erc_NT"; "LH0_NT"; "RD_NT"; "TDr_NT"; "l2_NT"; "l3_NT"; "l4_NT"; "run2_NT"; "EfD_NT"; "Eps_NT"; "TD_NT"; "l1okb_NT"; "run4_NT"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "sDv_of"; "LOOPX"; "PreDv"; "atpc"; "FACTS_Tg"; "F_ext"; "P0T_g"; "PostDv"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln"; "RCYE"; "Erc_of"; "small_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG"; "sa_t"; "sb_t"; "sc_t"; "sd_t"; "se_t"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG"; "dchkbT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_link_state"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat";
"eqb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition W_NT : list ulink := Wcan 0.
Definition st_NT : ustop := UStopLe.
Definition F0_NT : list sprop := FACTS_Tg true VFN.
Definition P0_NT : axst := P0T_g true [] VFN.

Definition l1_NT : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] P0_NT.
Definition LH0_NT : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l1_NT) DUMMY).
Definition l2_NT : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] LH0_NT.
Definition LH1_NT : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l2_NT) DUMMY).
Definition LT_NT : axst := Eval vm_compute in LT_ofg LH1_NT F0_NT.
Definition EX_NT : axst := Eval vm_compute in EX_ofg LH1_NT F0_NT.
Definition l3_NT : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state LT_NT (SVar pFR)).
Definition l4_NT : list leafA := Eval vm_compute in runA FUELF [CASX] EX_NT.
Definition S1c_NT : axst := Eval vm_compute in S1cT_of (la_state (nth 0 l4_NT DUMMY)) (F0_NT ++ F_ext).

Lemma RUN1_NT : ltac2:(tb__ "0|0|
S0S7S14A1S3cS29S4S10S57S4S10S2eS5S10A1A3A3S47A3S44A3"). Proof. Time vmr. Qed.
Lemma RUN2f_NT : ltac2:(tb__ "0|0|
S0S7S14A1S3cS29S4S10S57S4S10S5aS5S10A1A3A3S4aA3S4dA3"). Proof. Time vmr. Qed.
Lemma RUN3f_NT : ltac2:(tb__ "0|0|
S0S7S14A1S3cS29S4S10S57S4S10S5aS5S10A1A3A3S87S41S23S58A1A2A3S4eA3"). Proof. Time vmr. Qed.
Lemma RUN4f_NT : ltac2:(tb__ "0|0|
S0S7S14A1S3cS29S4S10S2eS5S10A1A3S46A3S4fA3"). Proof. Time vmr. Qed.

Definition l1okb_NT (l : list leafA) : bool := ltac2:(tb__ "0|1|
S61S14S14SfS8aS27S12S15R1A1M0A1A1S57A2S2aG0S43A2A2LL;Vl;A3").
Lemma chk_NT : ltac2:(tb__ "0|a|
S0S3S6S6S6S6S6S6S6S6S6S6S6S6S6S6S6S6S6S6S8S7S14A1M0S3Lx;M1S44S2S14G0SdLl0;Ll;M2X7x2A1S8G1S4dS2G2X7x2A1A2S8G1S4eS2G2X7x2A1A2S8G1S4fS2G2X7x2A1A2S54S44A1A2S89SeS14S5cS57S44A2A2U1A2A2S61S14S14SfS2aS15R1A1M3S41A2S2aG3S46A2A2LL;S4dA3A2S1eS12S88S41S23S58A1M4A2A1A1A2S28S1dS12S41A1M5A1M6G4A2A2S61S14S86S41S46S58A3S4eA3A2S61S14S14S2aG3S43A2LL;S4fA3A2S56S3aS1dS12S47A1M7A1A2A2S56S3aS1dS12S4aA1M8A1A2A2S56S3aG6A2A2S56S3aS1dS12S46A1M9A1A2A2S8S20G7A1A1A2S8S20G8A1A1A2S8S20G5A1A1A2S8S20G9A1A1A2S2A3").
Proof. Time vmr. Qed.
Lemma LH0eq_NT : ltac2:(tb__ "0|0|
S0S13S15S65S14U0S5cS57S44A2S3eA4A1S4aA3"). Proof. vmr. Qed.

Lemma SIDE_NT : ltac2:(tb__ "0|0|
S0S3S7dS47S41A2S2A3"). Proof. Time vmr. Qed.
Lemma OBND_NT : ltac2:(tb__ "0|1|
S0S7SbSbS1bS1bA2S1bA2M0A1S64S1fG0S7cS25S12S41A1A1A4S64S1fG0S7cS25S12S47A1A1A4A3"). Proof. Time vmr. Qed.

Definition C2_NT : axst := C2_of S1c_NT.
Definition run2_NT : list leafA := ltac2:(tb__ "0|0|
S3cS29S4S10S2cS5S10A1A3S3fA3").
Definition EfD_NT : axst := leaf 0 run2_NT.
Definition ED_NT : axst := ED_of EfD_NT.
Definition RD_NT : list sobj := RDv_of ED_NT.
Definition TD_NT : axst := TDv_of ED_NT.
Definition TDr_NT : axst := TDr_of TD_NT.

Definition CD_NT : axst := ltac2:(tb__ "0|0|
S30S4cA1S13S35R1S63S1cS1cS8S62S1cS21R1A1S5eA3A1Lf;S22S12R1A1A1A3A2TC;").
Definition run3_NT : list leafA := ltac2:(tb__ "0|0|
S3cS29S4S10S2dS4S10S2bS5S10A1A3A3S45A3").
Definition Eps_NT : axst := leaf 0 run3_NT.
Definition Ebg_NT : axst := leaf 1 run3_NT.
Definition run4_NT : list leafA := ltac2:(tb__ "0|0|
S3cS29S4S10S6dS5S10A1A3S42A3").
Definition Erc_NT : axst := ltac2:(tb__ "0|0|
S6eS3dU0S55A2S22S12S42A1A1A2").

Lemma D2_NT : ltac2:(tb__ "0|4|
S0SaSbS7SbS1bS1bA2M0A1M1S7S1cA1M2A2M3A1S70S12S43A1S12S3fA1A2S9G3ScG1G2S4G0ScS1bS1bS34S36A4S5G0A1A3S31A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_NT : ltac2:(tb__ "0|1|
S1S0S3S1eS12S3fA1M0A1S2A3S1S0S11S1dG0A1S1dS12S43A1A1A3S0S3S20G0A1SdA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_NT : ltac2:(tb__ "0|0|
S0S3S56S3aS1dS12S3fA1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_NT : ltac2:(tb__ "0|0|
S0S13S16S43S12S3fA1A2S3fA3"). Proof. vmr. Qed.
Lemma RUN2_NT : ltac2:(tb__ "0|0|
S0S7S14A1S3cS29S4S10S2cS5S10A1A3S3fA3S50A3"). Proof. unfold run2_NT; reflexivity. Qed.
Lemma L2_NT : ltac2:(tb__ "0|0|
S1S0S3S2fS50S4S10S2cS5S10A1A3A2S2A3S0S13S3dU0S50A2S51A3A2"). Proof. Time (split; [vmr | unfold EfD_NT; reflexivity]). Qed.
Lemma AXD_NT : ltac2:(tb__ "0|0|
S0SaS13A1S66S51S32A2S9S13S40A2A3"). Proof. Time vmr. Qed.
Lemma HeD_NT : ltac2:(tb__ "0|1|
S0SaS7S1fA1M0A1S7fS40S5bS59S40A1A3S9G0S4bA2A3"). Proof. Time vmr. Qed.
Lemma HchkD_NT : ltac2:(tb__ "0|0|
S0S3S7eS40S5bS59S40A1S4bS4S13S60S5S13A1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_NT : ltac2:(tb__ "0|0|
S0SaS13A1S66S53S33A2S9S13S4cA2A3"). Proof. Time vmr. Qed.
Lemma ENTD_NT : ltac2:(tb__ "0|0|
S0S3S85S4cS45A2S2A3"). Proof. Time vmr. Qed.
Lemma RUN3_NT : ltac2:(tb__ "0|0|
S0S7S14A1S3cS29S4S10S2dS4S10S2bS5S10A1A3A3S45A3S48A3"). Proof. unfold run3_NT; reflexivity. Qed.
Lemma L3_NT : ltac2:(tb__ "0|0|
S1S0S3S2fS48S4S10S2dS4S10S2bS5S10A1A3A3A2S2A3S1S0S13S3dU0S48A2S52A3S0S13S3dU1S48A2S42A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_NT | unfold Ebg_NT]; reflexivity]). Qed.
Lemma NX3_NT : ltac2:(tb__ "0|1|
S1S0S3S56S3aS1dS12S45A1M0A1A2S2A3S0S3S20G0A1SdA3A2"). Proof. split; vmr. Qed.
Lemma SMF_NT : ltac2:(tb__ "0|0|
S0S3S62S1cS21S6fA1S22S12S52A1A1A3S2A3"). Proof. vmr. Qed.
Lemma BGF_NT : ltac2:(tb__ "0|1|
S1S0S3S62S1cS21S82A1S22S12S49A1A1M0A3S2A3S0S3S62S1cS21S19A1G0A3S2A3A2"). Proof. split; vmr. Qed.
Lemma NXB_NT : ltac2:(tb__ "0|0|
S0S3S56S3aS1dS12S42A1A1A2S2A3"). Proof. vmr. Qed.
Lemma CertR_NT : ltac2:(tb__ "0|1|
S0S3S6bS3bS29S4S10S6dS5S10A1A3S3aS4S13S42S5S13A1M0A3S4S13S49G0A3A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_cfgA_of_runl segsA FUELF [RCYE] GW Ebg_NT [Erc_NT] run4_NT); [unfold run4_NT, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma ECertR_NT : ltac2:(tb__ "0|3|
S0S3S6cS3bS29S4S10S6dS5S10A1A3S3aS4S69S6aS42Z1S24Z0M0A1M1A3S5S69A1M2A3S4S69S6aS49G0G1A3G2A3A6S2A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runl segsA FUELF [RCYE] GW (mkVNA Ebg_NT 1 (SLit 0)) [mkVNA Erc_NT 0 (SLit 0)] run4_NT); [unfold run4_NT, runA, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.runlA; reflexivity | vmr]. Qed.
Lemma DCHK_NT : ltac2:(tb__ "0|1|
S0S3S83U0M0S1aS17G0A2S40S53S59S40A1S4bA6S2A3"). Proof. Time vmr. Qed.

Lemma Wa_NT : ltac2:(tb__ "0|0|
S0S3S1eS72S37U0A1A1A1S2A3"). Proof. vmr. Qed.
Lemma Da_NT : ltac2:(tb__ "0|4|
S0SaSbS7SbS1bS1bA2M0A1M1S7S1cA1M2A2M3A1S70S12S84S39A1A1S72S37U0A1A1A2S9G3ScG1G2S4G0ScS1bS1bS23P18A1S24S81A1A4S5G0A1A3S5S1cA1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_NT : ltac2:(tb__ "0|0|
S0S3S1eS73S37U0A1S17A2A1S2A3"). Proof. vmr. Qed.
Lemma Wc_NT : ltac2:(tb__ "0|0|
S0S3S1eS74S37U0A1S17A2A1S2A3"). Proof. vmr. Qed.
Lemma Wd_NT : ltac2:(tb__ "0|0|
S0S3S1eS75S37U0A1S17A2A1S2A3"). Proof. vmr. Qed.
Lemma Fb_NT : ltac2:(tb__ "0|0|
S0S3S61S1cS26S80A1S5dS2S18A2A3S2A3"). Proof. vmr. Qed.
Lemma XI_NT : ltac2:(tb__ "0|1|
S0SaS13A1S66S76S2S37U0M0A1S17S18A4S71G0SeS67S17A2A2A2S9S13S5fS2S64S67S1fS68S17A4S18A3A2A3"). Proof. vmr. Qed.

Definition PMID_NT : axst := ltac2:(tb__ "0|0|
S77S2S37U0A1S38S5S1fA1S18A5").
Lemma Wbm_NT : ltac2:(tb__ "0|0|
S0S3S1eS78S37U0A1S38S17A3A1S2A3"). Proof. vmr. Qed.
Lemma Wcm_NT : ltac2:(tb__ "0|0|
S0S3S1eS79S37U0A1S38S17A3A1S2A3"). Proof. vmr. Qed.
Lemma Wdm_NT : ltac2:(tb__ "0|0|
S0S3S1eS7aS37U0A1S38S17A3A1S2A3"). Proof. vmr. Qed.
Lemma XIm_NT : ltac2:(tb__ "0|2|
S0SaS13A1S66S7bS2S37U0M0A1M1S38S17S18A5S71G0SeS67S17A2A2A2S9S13S77S2G1S38S64S67S1fS68S17A4S18A5A2A3"). Proof. vmr. Qed.
End F0T_cNT.

