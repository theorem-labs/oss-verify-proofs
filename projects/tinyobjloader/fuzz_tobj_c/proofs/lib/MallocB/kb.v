(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k7.
From Stdlib Require FunctionalExtensionality.

(* [comment removed for export] *)
Module SpineCallocRi0u.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "app"; "Some"; "option"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "ss_facts"; "valuation"; "ss_objs"; "ss_lenient"; "swf"; "SAlu"; "SLit"; "SVar"; "rw"; "SPBranch"; "SPNot"; "rm"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "axst"; "ax_X"; "entailsA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kb.SpineCallocRi0u"; "e3r"; "icc"; "r_9N_0"; "W0"; "FUEL"; "ct0N"; "r_1_0"; "r_2_1"; "r_t1N_0"; "s_bkN"; "s_inN"; "xlN"; "e3p"; "nob"; "r_t1N_1"; "cellsfN"; "r_2_0"; "r_t0N_0"; "r_zN_0"; "s_xN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "cE1"; "cE2"; "GR"; "cR1"; "factsR"; "PV4"; "cR0"; "cT1"; "PV6"; "cE3"; "vK"; "O_pcm"; "cE3b"; "k_e"; "F_r0"; "F_r1"; "F_x"; "O_pccK"; "O_ri"; "PNX"; "cE3a"; "cR0a"; "fa_e"; "keepn"; "nobj"; "ri_e"; "ri_has"; "vAU"; "vFA"; "vMFA"; "vMU"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "A_globals"; "Kc_ok"; "malloc_depth"; "mem_keptA"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "O_pcc0"; "O_st"; "E3p"; "F_gen"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "entryR"; "gh_nf"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineCallocR4"; "O_rif"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineCallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineCallocR6"; "e16N"; "e_srcN"; "phFN"; "@Stdlib.ZArith.BinInt.Z"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineCallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineCallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k7.SpineCallocRu0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition W0 : list ulink := Wcan 0.
Definition FUEL : nat := 4000%nat.
Definition e3r : axst := e3u.
Lemma SK3 : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S65SdG0S68S13S1eS26A1A1A4S65SdG0S68S8SdS8SdS2SdS92S8SdS64S29A1S5eA3A3S93A3S2SdS76S2SdS77S5SdA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX3 : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S26A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF3b : ltac2:(tb__ "0|0|
S0S4S67S8SfS8SfS63S29S5cA2S62S60A1A3S79A3S11S1eS26A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX3 : ltac2:(tb__ "0|0|
S0S4S69S10S1eS26A1A1PdcA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma WR0a : ltac2:(tb__ "0|0|
S0S4S15S1eS50S26A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB0 : ltac2:(tb__ "0|0|
S0S4S8fSfS1dS3dA1S8SfS11S1eS26A1A1S8SfS49S4aA3A3A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z4147cS5S25A1A3S41S26A1S3A5").
Local Strategy expand [R_1__R].
Definition r_1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition r_1_0 := Eval vm_compute in (nth 0 r_1 (mkLeafA (cR0 e3r) RsCut)).
Definition cr1 := Eval vm_compute in (cR1 (factsR e3r) (la_state r_1_0)).
Definition r_2 := Eval vm_compute in (match sym_runA segsA FUEL [0x41704; 0x41560] cr1 true with Some l => l | None => [] end).
Definition r_2_0 := Eval vm_compute in (nth 0 r_2 (mkLeafA cr1 RsCut)).
Definition r_2_1 := Eval vm_compute in (nth 1 r_2 (mkLeafA cr1 RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z4147cS5S25A1A3S41S26A1S3A5S9G0S2S20S2cS5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [r_1_0]). Qed.
Lemma LN_0 : ltac2:(tb__ "0|0|
S0S4S14S1eS41S26A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_0 : ltac2:(tb__ "0|0|
S0S4S69S3dS10S1eS41S26A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_r1 : ltac2:(tb__ "0|0|
S0S4S15S1eS3eS3fS26A1S1fS2cA1A2A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_r1 : ltac2:(tb__ "0|5|
S0SaS7S6S7SeSeA2M0A1M1S6SfA1M2A2M3A1S80S1eS1fS2cA1M4A1S1eS3eS3fS26A1G4A2A1A2S9G3ScG1G2S2G0ScSeSeS54S5bA4S2G0ScSeSeS48S45A4S2G0ScSeSeS51S57A4S5G0A1A3A3A3S5SfA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_r1 : ltac2:(tb__ "0|1|
S0S4S6aS10S1eS3eS3fS26A1S1fS2cA1M0A2A1A1S10S1eG0A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_2 : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z41704S2S25Z41560S5S25A1A3A3S3eS3fS26A1S1fS2cA1A2S3A5S9G0S2S20S36S2S20S2dS5S20A1A3A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S4S14S1eS3eS3fS26A1S1fS2cA1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_1 : ltac2:(tb__ "0|0|
S0S4S69S3dS10S1eS3eS3fS26A1S1fS2cA1A2A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition nob := Eval vm_compute in ((length (ss_objs (ax_S e3r)) + 2)%nat).
Definition icc := Eval vm_compute in ((length (ss_objs (ax_S e3r)) - 2)%nat).
Definition R_t0N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S1fS2dA1S3A5").
Local Strategy expand [R_t0N__R].
Definition r_t0N := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_t0N__R).
Definition r_t0N_0 := Eval vm_compute in (nth 0 r_t0N (mkLeafA (la_state r_2_1) RsCut)).
Definition ct0N := Eval vm_compute in (cT0 (la_state r_t0N_0)).
Definition R_t1N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S42S2bA1S3A5").
Local Strategy expand [R_t1N__R].
Definition r_t1N := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_t1N__R).
Definition r_t1N_0 := Eval vm_compute in (nth 0 r_t1N (mkLeafA (cT1 ct0N) RsCut)).
Definition r_t1N_1 := Eval vm_compute in (nth 1 r_t1N (mkLeafA (cT1 ct0N) RsCut)).
Definition s_inN := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0N_0)) (ax_S ct0N)).
Definition s_bkN := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1N_0) nob)) (ax_S ct0N)).
Lemma SK_tN : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S65SdG0S68S13S1eS2bA1A1A4S65SdG0S68S8SdS8aS29A1S2SdS76S2SdS77S2SdS46S2SdS4dS5SdA1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tN : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S2bA1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tNb : ltac2:(tb__ "0|0|
S0S4S67S89S29S5cA2S11S1eS2bA1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tN : ltac2:(tb__ "0|0|
S0S4S6aS10S1eS2bA1A1S4eA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1N : ltac2:(tb__ "0|0|
S0S4S15S1eS42S2bA1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S42S2bA1S3A5S9G0S2S20S2eS2S20S34S5S20A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1N__R <: R_t1N__R = Some [r_t1N_0; r_t1N_1]). Qed.
Lemma LN_t1N : ltac2:(tb__ "0|0|
S0S4S14S1eS42S2bA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bN : ltac2:(tb__ "0|1|
S0S6SdA1S13S1eS1fS2eA1A1A1M0S8SdS66SdS33G0A3S2SdS8cS2SdS8bS5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xN : ltac2:(tb__ "0|1|
S0S6SdA1S13S1eS1fS34A1A1A1M0S8SdS66SdS33G0A3S2SdS8cS2SdS8bS5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkN : ltac2:(tb__ "0|0|
S0S4S24S52S1fS2eA1S33A2S2bS2fA3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkN : ltac2:(tb__ "0|0|
S0S4S6fS2fS3dA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4N : ltac2:(tb__ "0|0|
S0SeS6eS2fS40A2S16S6bS18S40A1S17Z4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6N : ltac2:(tb__ "0|0|
S0SeS6eS2fS43A2S16S6bS18S43A1S17Z4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bNb : ltac2:(tb__ "0|0|
S0S4S67S2SfS1aS6cS16S6bS18S40A1S17Z4A1A3S8dA3S5SfA1A3S11S1eS1fS2eA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xNb : ltac2:(tb__ "0|0|
S0S4S67S2SfS1bS1aS6cS16S6bS18S40A1S17Z4A1A3S8dA3A1S5SfA1A3S11S1eS1fS34A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S1fS2dA1S3A5S9G0S2S20S37S5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0N__R <: R_t0N__R = Some [r_t0N_0]). Qed.
Lemma LN_t0N : ltac2:(tb__ "0|0|
S0S4S14S1eS1fS2dA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0N : ltac2:(tb__ "0|0|
S0S4S69S3dS10S1eS1fS2dA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inN : ltac2:(tb__ "0|0|
S0S4S24S1fS37A1S2bS30A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inN : ltac2:(tb__ "0|0|
S0S4S6fS30S3dA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4N : ltac2:(tb__ "0|0|
S0SeS6eS30S40A2S16S6bS7aS17Z10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6N : ltac2:(tb__ "0|0|
S0SeS6eS30S43A2S99A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlN := Eval vm_compute in (keepn (la_state r_t1N_1) nob).
Definition R_9N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z40e5cS5S25A1A3S31S3A5").
Local Strategy expand [R_9N__R].
Definition r_9N := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_9N__R).
Definition r_9N_0 := Eval vm_compute in (nth 0 r_9N (mkLeafA xlN RsCut)).
Definition cellsfN := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9N_0) icc))) O_ri)).
Definition x3N := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9N_0) icc))).
Definition r_zN := Eval vm_compute in (match sym_runA segsA FUEL [0x3c614] x3N true with Some l => l | None => [] end).
Definition r_zN_0 := Eval vm_compute in (nth 0 r_zN (mkLeafA x3N RsCut)).
Lemma R_9N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z40e5cS5S25A1A3S31S3A5S9G0S2S20S28S5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9N__R <: R_9N__R = Some [r_9N_0]). Qed.
Lemma LN_9N : ltac2:(tb__ "0|0|
S0S4S14S1eS31A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9N : ltac2:(tb__ "0|0|
S0S4S69S3dS10S1eS31A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x1N : ltac2:(tb__ "0|0|
S0S4S15S1eS3bS1fS28A1S27A2A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x1N : ltac2:(tb__ "0|5|
S0SaS7S6S7SeSeA2M0A1M1S6SfA1M2A2M3A1S80S1eS1fS28A1M4A1S1eS3bG4S27A2A1A2S9G3ScG1G2S2G0ScSeSeS48S45A4S5G0A1A3S5SfA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1N : ltac2:(tb__ "0|1|
S0S4S6aS10S1eS3bS1fS28A1M0S27A2A1A1S10S1eG0A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1N : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S3bS1fS28A1S27A2A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1N : ltac2:(tb__ "0|0|
S0SaSdA1S90SdS13S1eS3bS1fS28A1S27A2A1A1S27A3S9SdS4cA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1N : ltac2:(tb__ "0|2|
S0S6SdA1S13S1eS3bS1fS28A1S27A2M0A1A1M1S8SdS66SdS91S53G0A1U2A2G1A3S2SdS46S2SdS96S35A1S5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1N : ltac2:(tb__ "0|0|
S0S4S55S35S98S58S56S59A5S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2N : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S65SdG0S68S13S1eS3cS3bS1fS28A1S27A2A1A1A1A4S65SdG0S68S8SdS8aS29A1S2SdS76S2SdS77S5SdA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2N : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S3cS3bS1fS28A1S27A2A1A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Nb : ltac2:(tb__ "0|0|
S0S4S67S89S29S5cA2S11S1eS3cS3bS1fS28A1S27A2A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aN : ltac2:(tb__ "0|0|
S0S4S15S1eS4fS3cS3bS1fS28A1S27A2A1A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bN : ltac2:(tb__ "0|0|
S0S4S15S1eS47S3cS3bS1fS28A1S27A2A1A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3N : ltac2:(tb__ "0|1|
S0S4S8fSfS1dS10S1eS47S3cS3bS1fS28A1S27A2A1A1A1M0A1A1S8SfS4bS11G0A1A3A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_zN : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z3c614S5S25A1A3S44S3cS3bS1fS28A1S27A2A1A1S3A5S9G0S2S20S38S5S20A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_zN : ltac2:(tb__ "0|0|
S0S4S14S1eS44S3cS3bS1fS28A1S27A2A1A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_zN : ltac2:(tb__ "0|0|
S0S4S69S3dS10S1eS44S3cS3bS1fS28A1S27A2A1A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition e3p := Eval vm_compute in (E3p W0 UStopLe 2).
Lemma E3p_eq : ltac2:(tb__ "0|0|
S0S22S78S29S5cZ2A3S32A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition s_xN := Eval vm_compute in (s_exit (la_state r_zN_0) e3p).
Lemma ENT_xN : ltac2:(tb__ "0|0|
S0S4S24S1fS38A1S32S39A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SX_xN : sx_okb s_xN = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S149_xN : wsub_get s_xN 149%positive = vK.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S159_xN : wsub_get s_xN 159%positive = vCHX.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.

Lemma HW0 : stopJ_w W0 UStopLe. Proof. hw_discharge. Qed.
Definition pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0N r_t1N_0 r_t1N_1 nob s_bkN
    SK_tN XX_tN (inclb_incl _ _ XF_tNb) NX_tN W_t1N R_t1N LN_t1N OB_bN OB_xN ENT_bkN SID_bkN S_bk4N S_bk6N (In_of_inclb _ _ FB_bNb) (In_of_inclb _ _ FB_xNb)
    (la_state r_2_1) r_t0N_0 s_inN e_srcN R_t0N LN_t0N NX_t0N ENT_inN SID_inN S_in4N S_in6N.
Definition entry_i := refill_entry 0 UStopLe e3r SK3 XX3 (inclb_incl _ _ XF3b) NX3 WR0a FB0.
Definition prefix_i A Kc rb tp0 md0 TR KIT HKc := refill_prefix A Kc rb tp0 md0 TR KIT HKc FUEL e3r r_1_0 r_2_0 r_2_1 R_1 LN_0 NX_0 W_r1 D_r1 NX_r1 R_2 LN_1 NX_1.
Definition exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE phX PHX HFILLX Hini e16N vMFA vAU vMU HRIv HLEN HIDC FUEL xlN r_9N_0 r_zN_0 icc cellsfN
    R_9N LN_9N NX_9N W_x1N D_x1N NX_x1N XX_1N IC_1N OB_1N RI_1N SK_2N XX_2N (inclb_incl _ _ XF_2Nb) W_3aN W_3bN FB_3N R_zN LN_zN NX_zN.
Definition back_N CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLe rho HW HE phF HREB HMK HLEN e3p (la_state r_zN_0) s_xN ENT_xN SX_xN S149_xN S159_xN HPOP.
Lemma FJ_Nb : ltac2:(tb__ "0|0|
S0S4S67S2SfS1bS1aS6dS5aS45A3A1S5SfA1A3S11S1eS1fS2dA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem refill_N_i : ltac2:(tb__ "0|5|
S6S7S25S25A2A1M0G0S7bS5dS6S7S22S82A2A1F_;F_;S97R3R2R1A3S22S22S0S22R2S26A3S0S22R2S32A3S7bS5dS12S6S71Q40M1A1A1M2S74S74OF_;F_;S95R4R1A2S5fR5A1S0S4S7cR7A1S3A3S0S25S7eR8S70G1S19R6PcM3A2A2A2Z0A3S81S3aS7fR7R6RfR9R8A2A5S74S12S72S84RcR2R9R1S29S5cRaA7S9bS87S7dS70G1S19R3G3A2A2A1A1S85RdR3A2A2S12G2S6S73A1S72S83R12R11R8RfR7S9aS87S7dS70G1S19R8G3A2A2A1A1A1R4R3R2R1AaS1S94S3aS88R13S7dS70G1S19R9G3A2A2A1A2M4R5R4R2A5S61R1bR1aR13G4S1cR9A1S1cR5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;FHE;Fmd0;Frb;S7bS12G2S12RbS75S3aS8eS29S5cR4ReR3A5R12R1R2A5S81S3aS7fR3R2R15R4ReA2A5A2FrX;Ftp';Frho';FA';S12S72S12S84RfR3RcR2S29S5cRdA7RcS75S3aS83R10RfR4RdR3S86A6S1fS36A1R2RdA5R7A2F_;Fr';Fmd0;Frb;S12RaS75S3aS8eS29S5cReRdRcA5R12R1RbA5R5A2FrhoE;F_;F_;F_;TQ;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;F_;FE3P;FE3;FHPF;FPFam;FXGL;FCST;").
Proof.
  intros CST XGL PFam HPF E3 E3P -> ->.
  apply (refill_N CST XGL PFam W0 UStopLe e3r e3p (la_state r_2_0) (la_state r_2_1) xlN (la_state r_zN_0) (In_of_inclb _ _ FJ_Nb)).
  - intros A Kc rho rhoE tp w Hini Hcnt Hw. exact (entry_i A Kc rho rhoE tp w HW0 Hini Hcnt Hw).
  - intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE. exact (prefix_i A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho r tp Q HE).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_N CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
Qed.
End SpineCallocRi0u.

(* [comment removed for export] *)
Module SpineCallocRi1u.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "app"; "Some"; "option"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "ss_facts"; "valuation"; "ss_objs"; "ss_lenient"; "swf"; "SAlu"; "SLit"; "SVar"; "rw"; "SPBranch"; "SPNot"; "rm"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "axst"; "ax_X"; "entailsA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kb.SpineCallocRi1u"; "e3r"; "icc"; "r_9N_0"; "W0"; "FUEL"; "ct0N"; "r_1_0"; "r_2_1"; "r_t1N_0"; "s_bkN"; "s_inN"; "xlN"; "e3p"; "nob"; "r_t1N_1"; "cellsfN"; "r_2_0"; "r_t0N_0"; "r_zN_0"; "s_xN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "cE1"; "cE2"; "GR"; "cR1"; "factsR"; "PV4"; "cR0"; "cT1"; "PV6"; "cE3"; "vK"; "O_pcm"; "cE3b"; "k_e"; "F_r0"; "F_r1"; "F_x"; "O_pccK"; "O_ri"; "PNX"; "cE3a"; "cR0a"; "fa_e"; "keepn"; "nobj"; "ri_e"; "ri_has"; "vAU"; "vFA"; "vMFA"; "vMU"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLeOrPc"; "KcA"; "A_globals"; "Kc_ok"; "malloc_depth"; "mem_keptA"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "O_pcc0"; "O_st"; "E3p"; "F_gen"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "entryR"; "gh_nf"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineCallocR4"; "O_rif"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineCallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineCallocR6"; "e16N"; "e_srcN"; "phFN"; "@Stdlib.ZArith.BinInt.Z"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineCallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineCallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k7.SpineCallocRu1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition W0 : list ulink := Wcan 1.
Definition FUEL : nat := 4000%nat.
Definition e3r : axst := e3u.
Lemma SK3 : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S65SdG0S68S13S1eS26A1A1A4S65SdG0S68S8SdS8SdS2SdS92S8SdS64S29A1S5eA3A3S93A3S2SdS76S2SdS77S5SdA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX3 : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S26A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF3b : ltac2:(tb__ "0|0|
S0S4S67S8SfS8SfS63S29S5cA2S62S60A1A3S79A3S11S1eS26A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX3 : ltac2:(tb__ "0|0|
S0S4S69S10S1eS26A1A1PdcA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma WR0a : ltac2:(tb__ "0|0|
S0S4S15S1eS50S26A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB0 : ltac2:(tb__ "0|0|
S0S4S8fSfS1dS3dA1S8SfS11S1eS26A1A1S8SfS49S4aA3A3A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z4147cS5S25A1A3S41S26A1S3A5").
Local Strategy expand [R_1__R].
Definition r_1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition r_1_0 := Eval vm_compute in (nth 0 r_1 (mkLeafA (cR0 e3r) RsCut)).
Definition cr1 := Eval vm_compute in (cR1 (factsR e3r) (la_state r_1_0)).
Definition r_2 := Eval vm_compute in (match sym_runA segsA FUEL [0x41704; 0x41560] cr1 true with Some l => l | None => [] end).
Definition r_2_0 := Eval vm_compute in (nth 0 r_2 (mkLeafA cr1 RsCut)).
Definition r_2_1 := Eval vm_compute in (nth 1 r_2 (mkLeafA cr1 RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z4147cS5S25A1A3S41S26A1S3A5S9G0S2S20S2cS5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [r_1_0]). Qed.
Lemma LN_0 : ltac2:(tb__ "0|0|
S0S4S14S1eS41S26A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_0 : ltac2:(tb__ "0|0|
S0S4S69S3dS10S1eS41S26A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_r1 : ltac2:(tb__ "0|0|
S0S4S15S1eS3eS3fS26A1S1fS2cA1A2A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_r1 : ltac2:(tb__ "0|5|
S0SaS7S6S7SeSeA2M0A1M1S6SfA1M2A2M3A1S80S1eS1fS2cA1M4A1S1eS3eS3fS26A1G4A2A1A2S9G3ScG1G2S2G0ScSeSeS54S5bA4S2G0ScSeSeS48S45A4S2G0ScSeSeS51S57A4S5G0A1A3A3A3S5SfA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_r1 : ltac2:(tb__ "0|1|
S0S4S6aS10S1eS3eS3fS26A1S1fS2cA1M0A2A1A1S10S1eG0A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_2 : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z41704S2S25Z41560S5S25A1A3A3S3eS3fS26A1S1fS2cA1A2S3A5S9G0S2S20S36S2S20S2dS5S20A1A3A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S4S14S1eS3eS3fS26A1S1fS2cA1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_1 : ltac2:(tb__ "0|0|
S0S4S69S3dS10S1eS3eS3fS26A1S1fS2cA1A2A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition nob := Eval vm_compute in ((length (ss_objs (ax_S e3r)) + 2)%nat).
Definition icc := Eval vm_compute in ((length (ss_objs (ax_S e3r)) - 2)%nat).
Definition R_t0N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S1fS2dA1S3A5").
Local Strategy expand [R_t0N__R].
Definition r_t0N := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_t0N__R).
Definition r_t0N_0 := Eval vm_compute in (nth 0 r_t0N (mkLeafA (la_state r_2_1) RsCut)).
Definition ct0N := Eval vm_compute in (cT0 (la_state r_t0N_0)).
Definition R_t1N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S42S2bA1S3A5").
Local Strategy expand [R_t1N__R].
Definition r_t1N := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_t1N__R).
Definition r_t1N_0 := Eval vm_compute in (nth 0 r_t1N (mkLeafA (cT1 ct0N) RsCut)).
Definition r_t1N_1 := Eval vm_compute in (nth 1 r_t1N (mkLeafA (cT1 ct0N) RsCut)).
Definition s_inN := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0N_0)) (ax_S ct0N)).
Definition s_bkN := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1N_0) nob)) (ax_S ct0N)).
Lemma SK_tN : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S65SdG0S68S13S1eS2bA1A1A4S65SdG0S68S8SdS8aS29A1S2SdS76S2SdS77S2SdS46S2SdS4dS5SdA1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tN : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S2bA1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tNb : ltac2:(tb__ "0|0|
S0S4S67S89S29S5cA2S11S1eS2bA1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tN : ltac2:(tb__ "0|0|
S0S4S6aS10S1eS2bA1A1S4eA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1N : ltac2:(tb__ "0|0|
S0S4S15S1eS42S2bA1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S42S2bA1S3A5S9G0S2S20S2eS2S20S34S5S20A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1N__R <: R_t1N__R = Some [r_t1N_0; r_t1N_1]). Qed.
Lemma LN_t1N : ltac2:(tb__ "0|0|
S0S4S14S1eS42S2bA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bN : ltac2:(tb__ "0|1|
S0S6SdA1S13S1eS1fS2eA1A1A1M0S8SdS66SdS33G0A3S2SdS8cS2SdS8bS5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xN : ltac2:(tb__ "0|1|
S0S6SdA1S13S1eS1fS34A1A1A1M0S8SdS66SdS33G0A3S2SdS8cS2SdS8bS5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkN : ltac2:(tb__ "0|0|
S0S4S24S52S1fS2eA1S33A2S2bS2fA3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkN : ltac2:(tb__ "0|0|
S0S4S6fS2fS3dA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4N : ltac2:(tb__ "0|0|
S0SeS6eS2fS40A2S16S6bS18S40A1S17Z4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6N : ltac2:(tb__ "0|0|
S0SeS6eS2fS43A2S16S6bS18S43A1S17Z4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bNb : ltac2:(tb__ "0|0|
S0S4S67S2SfS1aS6cS16S6bS18S40A1S17Z4A1A3S8dA3S5SfA1A3S11S1eS1fS2eA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xNb : ltac2:(tb__ "0|0|
S0S4S67S2SfS1bS1aS6cS16S6bS18S40A1S17Z4A1A3S8dA3A1S5SfA1A3S11S1eS1fS34A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z41570S2S25Z41584S5S25A1A3A3S1fS2dA1S3A5S9G0S2S20S37S5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0N__R <: R_t0N__R = Some [r_t0N_0]). Qed.
Lemma LN_t0N : ltac2:(tb__ "0|0|
S0S4S14S1eS1fS2dA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0N : ltac2:(tb__ "0|0|
S0S4S69S3dS10S1eS1fS2dA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inN : ltac2:(tb__ "0|0|
S0S4S24S1fS37A1S2bS30A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inN : ltac2:(tb__ "0|0|
S0S4S6fS30S3dA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4N : ltac2:(tb__ "0|0|
S0SeS6eS30S40A2S16S6bS7aS17Z10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6N : ltac2:(tb__ "0|0|
S0SeS6eS30S43A2S99A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlN := Eval vm_compute in (keepn (la_state r_t1N_1) nob).
Definition R_9N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z40e5cS5S25A1A3S31S3A5").
Local Strategy expand [R_9N__R].
Definition r_9N := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_9N__R).
Definition r_9N_0 := Eval vm_compute in (nth 0 r_9N (mkLeafA xlN RsCut)).
Definition cellsfN := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9N_0) icc))) O_ri)).
Definition x3N := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9N_0) icc))).
Definition r_zN := Eval vm_compute in (match sym_runA segsA FUEL [0x3c614] x3N true with Some l => l | None => [] end).
Definition r_zN_0 := Eval vm_compute in (nth 0 r_zN (mkLeafA x3N RsCut)).
Lemma R_9N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z40e5cS5S25A1A3S31S3A5S9G0S2S20S28S5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9N__R <: R_9N__R = Some [r_9N_0]). Qed.
Lemma LN_9N : ltac2:(tb__ "0|0|
S0S4S14S1eS31A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9N : ltac2:(tb__ "0|0|
S0S4S69S3dS10S1eS31A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x1N : ltac2:(tb__ "0|0|
S0S4S15S1eS3bS1fS28A1S27A2A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x1N : ltac2:(tb__ "0|5|
S0SaS7S6S7SeSeA2M0A1M1S6SfA1M2A2M3A1S80S1eS1fS28A1M4A1S1eS3bG4S27A2A1A2S9G3ScG1G2S2G0ScSeSeS48S45A4S5G0A1A3S5SfA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1N : ltac2:(tb__ "0|1|
S0S4S6aS10S1eS3bS1fS28A1M0S27A2A1A1S10S1eG0A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1N : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S3bS1fS28A1S27A2A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1N : ltac2:(tb__ "0|0|
S0SaSdA1S90SdS13S1eS3bS1fS28A1S27A2A1A1S27A3S9SdS4cA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1N : ltac2:(tb__ "0|2|
S0S6SdA1S13S1eS3bS1fS28A1S27A2M0A1A1M1S8SdS66SdS91S53G0A1U2A2G1A3S2SdS46S2SdS96S35A1S5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1N : ltac2:(tb__ "0|0|
S0S4S55S35S98S58S56S59A5S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2N : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S65SdG0S68S13S1eS3cS3bS1fS28A1S27A2A1A1A1A4S65SdG0S68S8SdS8aS29A1S2SdS76S2SdS77S5SdA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2N : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S3cS3bS1fS28A1S27A2A1A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Nb : ltac2:(tb__ "0|0|
S0S4S67S89S29S5cA2S11S1eS3cS3bS1fS28A1S27A2A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aN : ltac2:(tb__ "0|0|
S0S4S15S1eS4fS3cS3bS1fS28A1S27A2A1A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bN : ltac2:(tb__ "0|0|
S0S4S15S1eS47S3cS3bS1fS28A1S27A2A1A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3N : ltac2:(tb__ "0|1|
S0S4S8fSfS1dS10S1eS47S3cS3bS1fS28A1S27A2A1A1A1M0A1A1S8SfS4bS11G0A1A3A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_zN : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z3c614S5S25A1A3S44S3cS3bS1fS28A1S27A2A1A1S3A5S9G0S2S20S38S5S20A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_zN : ltac2:(tb__ "0|0|
S0S4S14S1eS44S3cS3bS1fS28A1S27A2A1A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_zN : ltac2:(tb__ "0|0|
S0S4S69S3dS10S1eS44S3cS3bS1fS28A1S27A2A1A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition e3p := Eval vm_compute in (E3p W0 UStopLeOrPc 3).
Lemma E3p_eq : ltac2:(tb__ "0|0|
S0S22S78S29S5cZ3A3S32A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition s_xN := Eval vm_compute in (s_exit (la_state r_zN_0) e3p).
Lemma ENT_xN : ltac2:(tb__ "0|0|
S0S4S24S1fS38A1S32S39A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SX_xN : sx_okb s_xN = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S149_xN : wsub_get s_xN 149%positive = vK.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S159_xN : wsub_get s_xN 159%positive = vCHX.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.

Lemma HW0 : stopJ_w W0 UStopLeOrPc. Proof. hw_discharge. Qed.
Definition pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0N r_t1N_0 r_t1N_1 nob s_bkN
    SK_tN XX_tN (inclb_incl _ _ XF_tNb) NX_tN W_t1N R_t1N LN_t1N OB_bN OB_xN ENT_bkN SID_bkN S_bk4N S_bk6N (In_of_inclb _ _ FB_bNb) (In_of_inclb _ _ FB_xNb)
    (la_state r_2_1) r_t0N_0 s_inN e_srcN R_t0N LN_t0N NX_t0N ENT_inN SID_inN S_in4N S_in6N.
Definition entry_i := refill_entry 1 UStopLeOrPc e3r SK3 XX3 (inclb_incl _ _ XF3b) NX3 WR0a FB0.
Definition prefix_i A Kc rb tp0 md0 TR KIT HKc := refill_prefix A Kc rb tp0 md0 TR KIT HKc FUEL e3r r_1_0 r_2_0 r_2_1 R_1 LN_0 NX_0 W_r1 D_r1 NX_r1 R_2 LN_1 NX_1.
Definition exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho HW0 HE phX PHX HFILLX Hini e16N vMFA vAU vMU HRIv HLEN HIDC FUEL xlN r_9N_0 r_zN_0 icc cellsfN
    R_9N LN_9N NX_9N W_x1N D_x1N NX_x1N XX_1N IC_1N OB_1N RI_1N SK_2N XX_2N (inclb_incl _ _ XF_2Nb) W_3aN W_3bN FB_3N R_zN LN_zN NX_zN.
Definition back_N CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLeOrPc rho HW HE phF HREB HMK HLEN e3p (la_state r_zN_0) s_xN ENT_xN SX_xN S149_xN S159_xN HPOP.
Lemma FJ_Nb : ltac2:(tb__ "0|0|
S0S4S67S2SfS1bS1aS6dS5aS45A3A1S5SfA1A3S11S1eS1fS2dA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem refill_N_i : ltac2:(tb__ "0|5|
S6S7S25S25A2A1M0G0S7bS5dS6S7S22S82A2A1F_;F_;S97R3R2R1A3S22S22S0S22R2S26A3S0S22R2S32A3S7bS5dS12S6S71Q40M1A1A1M2S74S74OF_;F_;S95R4R1A2S5fR5A1S0S4S7cR7A1S3A3S0S25S7eR8S70G1S19R6PcM3A2A2A2Z0A3S81S3aS7fR7R6RfR9R8A2A5S74S12S72S84RcR2R9R1S29S5cRaA7S9bS87S7dS70G1S19R3G3A2A2A1A1S85RdR3A2A2S12G2S6S73A1S72S83R12R11R8RfR7S9aS87S7dS70G1S19R8G3A2A2A1A1A1R4R3R2R1AaS1S94S3aS88R13S7dS70G1S19R9G3A2A2A1A2M4R5R4R2A5S61R1bR1aR13G4S1cR9A1S1cR5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;FHE;Fmd0;Frb;S7bS12G2S12RbS75S3aS8eS29S5cR4ReR3A5R12R1R2A5S81S3aS7fR3R2R15R4ReA2A5A2FrX;Ftp';Frho';FA';S12S72S12S84RfR3RcR2S29S5cRdA7RcS75S3aS83R10RfR4RdR3S86A6S1fS36A1R2RdA5R7A2F_;Fr';Fmd0;Frb;S12RaS75S3aS8eS29S5cReRdRcA5R12R1RbA5R5A2FrhoE;F_;F_;F_;TQ;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;F_;FE3P;FE3;FHPF;FPFam;FXGL;FCST;").
Proof.
  intros CST XGL PFam HPF E3 E3P -> ->.
  apply (refill_N CST XGL PFam W0 UStopLeOrPc e3r e3p (la_state r_2_0) (la_state r_2_1) xlN (la_state r_zN_0) (In_of_inclb _ _ FJ_Nb)).
  - intros A Kc rho rhoE tp w Hini Hcnt Hw. exact (entry_i A Kc rho rhoE tp w HW0 Hini Hcnt Hw).
  - intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE. exact (prefix_i A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho r tp Q HE).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_N CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
Qed.
End SpineCallocRi1u.

(* [comment removed for export] *)
Module SpineMallocQ14.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "of_nat"; "lt"; "ltb"; "sub"; "to_nat"; "ge"; "modulo"; "pow"; "@Corelib.Init.Datatypes"; "bool"; "length"; "list"; "None"; "app"; "nil"; "option"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "eval"; "valuation"; "rm"; "SLit"; "SMd"; "SVar"; "sv"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "prim_credit"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "FAb"; "phase"; "committed"; "frozen"; "ghosts"; "ph_f"; "ph_fill"; "ph_pop"; "revealedp"; "rlink"; "mlink"; "ph_u"; "releasedp"; "zoneR"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "ALU_SLL"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "vNEW"; "vK"; "vNF"; "vAU"; "vFA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_limit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "class_state"; "cs_allocated_user"; "cs_cache"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "AA"; "ag_spacebeg"; "ag_thread"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refill_cs"; "cls_pure"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "view"; "cell_ok"; "mkACell"; "@Corelib.Lists.ListDef"; "nth"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kUserMapSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "live_ids"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModelP"; "newZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "q_ids"; "qall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineMallocQ1"; "entryRq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kb.SpineMallocQ14.ARMP"; "e16P"; "e32P"; "e48P"; "e_srcP"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RebuildG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.RebuildD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RefillModelP RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jy.SpineMallocQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineMallocQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k0.SpineMallocQ12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k7.SpineMallocQ13.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Lemma AInvA_credit : ltac2:(tb__ "0|0|
S49S1aS12S21Q40A1A1S3cS59R4R3R2R1A4S0S5S6S3fR2R3A2S22R5A1A2S4cR5A1A2S1S4S3eS3dR2A1A1S36A3A2F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (_ & _ & _ & _ & _ & HD & _). unfold depot_wf in HD.
  destruct HM as (_ & PB & VL & V0 & K0C & F0 & _ & _ & _ & _ & _ & _ & DN & PC & _).
  split; [|exact VL]. eapply Z.le_trans; [exact PB|].
  apply budgetD_le_budget; [| |exact DN|exact PC|exact K0C|exact F0].
  - exact (dep_cost_bound_mem _ _ HD).
  - exact (dm_F_NFBLK _ _ HD).
Qed.

Section ARMP.
Variables (A : AA) (rb : valuation) (tp0 : list word) (md0 : Model) (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S5dVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.
Let k : Z := kchunks c.
Let S : Z := Size c.
Let nf : Z := Z.of_nat (length (cs_free_array cs)).
Let au : Z := cs_allocated_user cs.
Let mu : Z := cs_mapped_user cs.
Let mfa : Z := cs_mapped_free_array cs.
Let new : Z := gh_new A rb.
Let out : list Z := ltac2:(tb__ "0|1|
S14S4S58S42VA;A1M0VA;Vc;A3S5bG0S5cVA;A1Vc;A3A3").
Let fP : list Z := faP c cs.

Lemma P_c : 1 <= c <= 30.
Proof. pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. destruct CF as ((_ & C1 & _) & _). exact C1. Qed.

Lemma entry_pure : ltac2:(tb__ "0|0|
S0S4eVc;Vcs;Vout;A3S0S1S12S4A1S45Vcs;A1S15S4A1A3S0S9Vnf;Vk;A2S5S6Vmu;S57A2S23Vc;A1A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as (_ & _ & _ & _ & (_ & _ & Hc0) & _).
  destruct HE as (_ & HA & _). pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _ & Hq & _). destruct Hprim as (_ & _ & _ & PC).
  destruct PF as (NP & RM & _). fold nv c cs in NP, RM.
  split; [exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.RebuildD.entry_cls_pureQ _ A c P_c (PC c P_c) (proj1 Hq))|]. split; [exact Hc0|]. split; [exact NP | unfold kUserMapSize; exact RM].
Qed.

Lemma P_newZ : ltac2:(tb__ "0|0|
S1S4S5aVc;Vcs;A2Vnew;A3").
Proof. unfold newZ, new, gh_new. fold nv c cs. reflexivity. Qed.

Lemma P_csR : ltac2:(tb__ "0|4|
S4dVc;Vcs;A2S43S0S1S12S4A1S45R1A1M0S55S4ScSbS6Vnf;Vnew;A2M1Vk;A2M2A1VfP;A3A3S0S1S4S8S11S4G0A2A1Vk;A3S0S1S4S8S11S4S46R1A1A2A1G2A3S0S1S4S44R1A1S6Vau;S7Vnew;VS;A2A2A3S0S1S4S48R1A1S6Vmu;Z40000M3A2A3S0S1S4S47R1A1S10S4L_;SaVmfa;S7Z4G1A2A2S6Vmfa;G3A2Vmfa;X10x2A3S0S1S4S8S11S4VfP;A2A1G1A3S4S62S4R1VfP;A3S0S5Z0R2A2S9R2SfZ2Z1cA2A2A2F_;Fx;A2A2A2A2A2A2A2TcsR;").
Proof.
  destruct entry_pure as (HP & Hc0 & NP & RM).
  pose proof (P_fields c cs out P_c HP NP RM) as X. cbn zeta in X. rewrite P_newZ in X. fold nf au mu mfa S k fP in X.
  pose proof (P_faP_len c cs out P_c HP RM) as LP. rewrite P_newZ in LP. fold nf fP in LP.
  destruct X as (X1 & X2 & X3 & _ & X5 & X6 & X7). rewrite LP in X1.
  cbn zeta. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X5|]. split; [exact X6|]. split; [exact X7|]. split; [exact LP|].
  exact (P_ids c cs out P_c HP RM).
Qed.

Lemma pop_credit_eq : ltac2:(tb__ "0|1|
S1S4S6S6S22S4fVA;Vc;A2A1Z48000M0A2S10S4L_;SaVmfa;S7Z4S6Vnf;Vnew;A2A2A2G0Z0X10x2A2S22VA;A1A3").
Proof.
  destruct entry_pure as (HP & Hc0 & NP & RM). pose proof P_csR as (_ & _ & _ & _ & EMU & EMF & _). cbn zeta in EMU, EMF.
  destruct (refill_pure c cs out P_c HP Hc0 ltac:(intros _; exact RM)) as (HPR & _). cbn zeta in HPR.
  destruct HPR as (R1 & _ & _ & R4 & _ & _ & _ & _ & _ & _ & R10 & R11). destruct HP as (P1 & _ & _ & P4 & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof HE as (_ & HA & _).
  pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & (PL & _) & _).
  assert (Hlen : (Z.to_nat c < length (aa_cls A))%nat) by (rewrite PL; pose proof P_c as C1; clear -C1; lia).
  pose proof (prim_credit_populate A (refillA A c) c P_c) as PP. cbn zeta in PP.
  assert (E1 : nth (Z.to_nat c) (aa_cls (refillA A c)) cs_empty = refill_cs c cs).
  { unfold refillA. cbn [aa_cls]. rewrite nth_list_upd_same by exact Hlen. reflexivity. }
  assert (E0 : nth (Z.to_nat c) (aa_cls A) cs_empty = cs) by reflexivity.
  rewrite E1, E0 in PP. fold mu mfa in PP, P1, P4. rewrite EMU in PP, R1, R10. rewrite EMF in PP, R4, R11.
  assert (M8 : mu mod 8 = 0).
  { unfold kUserMapSize in P1. destruct (proj1 (Z.mod_divide mu (2 ^ 18) ltac:(clear; lia)) P1) as [q Hq]. rewrite Hq. replace (q * 2 ^ 18) with (q * 32768 * 8) by (clear; lia). apply Z_mod_mult. }
  assert (F8 : mfa mod 8 = 0).
  { unfold kFreeArrayMapSize in P4. destruct (proj1 (Z.mod_divide mfa (2 ^ 18) ltac:(clear; lia)) P4) as [q Hq]. rewrite Hq. replace (q * 2 ^ 18) with (q * 32768 * 8) by (clear; lia). apply Z_mod_mult. }
  specialize (PP ltac:(intros c' Hc' Hne; unfold refillA; cbn [aa_cls]; apply nth_list_upd_other; pose proof P_c as C1; clear -C1 Hc' Hne; lia) M8).
  destruct (mfa <? 4 * (nf + new)) eqn:E.
  - specialize (PP ltac:(rewrite Z.add_mod, M8 by (clear; lia); reflexivity) ltac:(clear -R10; lia) F8 ltac:(rewrite Z.add_mod, F8 by (clear; lia); reflexivity) ltac:(clear -R11; lia)).
    replace (mu + 262144 - mu) with 262144 in PP by (clear; lia). replace (mfa + 262144 - mfa) with 262144 in PP by (clear; lia). change (262144 / 8) with 32768 in PP. clear -PP. lia.
  - specialize (PP ltac:(rewrite Z.add_mod, M8 by (clear; lia); reflexivity) ltac:(clear -R10; lia) F8 F8 ltac:(clear -R11; lia)).
    replace (mu + 262144 - mu) with 262144 in PP by (clear; lia). replace (mfa - mfa) with 0 in PP by (clear; lia). change (262144 / 8) with 32768 in PP. change (0 / 8) with 0 in PP. clear -PP. lia.
Qed.

Lemma pop_credit : ltac2:(tb__ "0|2|
S0S5S6Z48000M0S10S4L_;SaVmfa;S7Z4S6Vnf;Vnew;A2A2A2G0Z0X10x2A2S22VA;A1M1A2S0S5S6S3fVmd0;Vtp0;A2G1A2S36A2S1S4S3eS3dVmd0;A1A1S36A3A2A2").
Proof.
  pose proof pop_credit_eq as EQ. pose proof (prim_credit_nonneg (refillA A c)) as NN.
  pose proof HE as (_ & HA & _ & _ & HBud & _).
  destruct (AInvA_credit A rb tp0 md0 HA) as (CR & VL).
  split; [clear -EQ NN; lia|]. split; [clear -CR HBud; lia | exact VL].
Qed.

Lemma pop_headroom : ltac2:(tb__ "0|6|
S25S12S21Q40A1A1S3cS2eVA;Vrb;Vtp0;Vmd0;R3R2R1A7SdS40R2R3A2SbS22VA;A1S6S6S10S4L_;M0S26S2fR4A1M1A1Z40000M2Z0M3X10x2G0S26S29R4A1M4A1G2G3X10x2A2S7Z1000S6G0S2cG1A1Z8M5G3X10x2G0S2cG4A1G5G3X10x2A2A2A2A2A2F_;Fmd;Ftp;Fph;").
Proof.
  intros ph tp md HM. destruct pop_credit as (_ & CR & VL).
  unfold mlink in HM. cbn zeta in HM. destruct HM as (_ & _ & M3 & _ & _ & _ & tp1 & _ & _ & _ & M10).
  unfold headroom. rewrite M3, VL. unfold kUserMapSize, kFreeArrayMapSize in M10.
  destruct (committed (ph_u ph)), (committed (ph_f ph)), (revealedp (ph_u ph)), (revealedp (ph_f ph)); clear -CR M10; lia.
Qed.

Lemma pop_geo : ltac2:(tb__ "0|9|
S0S0S5Z1M0Vc;A2S5Vc;Z1eA2A2S0S0S5Z20VS;A2S5VS;Z10000A2A2S0S0S5Z0M1Vau;A2S5Vau;Vmu;A2A2S0S5Vmu;Zdffc0000A2S0S0S5Z4M2Vnew;A2S5Vnew;Z2001A2A2S0S0S5G0Vk;A2S5Vk;Z8A2A2S0S5Vk;Vnew;A2S0S5G1Vnf;A2S0S5S7G2Vnf;A2Vmfa;A2S0S5Vmfa;Z1ffc0000A2S0S1S4SeVmfa;Z40000A2G1A3S0S5Z100080000000S4aS42VA;A1M3A1M4A2S0S5S6S6G4Z2000000000A2Z1000M5A2M6Z7fffff800000A2S0S1S4S24VA;Vrb;A2S6S6G4S7Vc;Z100000000A2A2Ze0000000A2A3S0S5G5S4bG3A1M7A2S0S2S5S6G7G5A2M8G4A2S5G6G7A2A2S2S5G8Z7fff7000A2S5Z10007fff8000G7A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  destruct (new_nums A rb CF PF) as (N1 & N2 & N3 & N4 & N5 & _ & _ & N8 & N9 & N10 & N11 & _). cbn zeta in N1, N2, N3, N4, N5, N8, N9, N10, N11.
  unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & (K1 & _) & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. clear; lia. }
  repeat (split; [first [assumption | exact K1 | clear -G14 TG; lia]|]). exact TB.
Qed.

Lemma old_cell_off : ltac2:(tb__ "0|1|
S25S4S5S2aR2A1Vnew;A2S5S2bR3A1Z10A2S0S5S24VA;Vrb;A2M0R3A2S9R3S6G0S7Z4Vnf;A2A2A2A2S3S31VA;Vrb;R5R4A4A1F_;F_;F_;Fz;Fph;").
Proof.
  intros ph z HFL HPO Hz HZ.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & T1 & PS1 & TB).
  unfold zoneR in HZ. unfold gh_nf in HZ. fold nv c cs nf new in HZ.
  unfold U0, F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize, region_info, kRegionInfoStride, PCE in HZ. fold nv c cs mu mfa in HZ.
  rewrite kSpaceSize_val in HZ. rewrite FAr in Hz, HZ.
  assert (SHB : forall x, 0 <= x <= 140737479966720 -> 2147450880 <= Sh x /\ Sh x + 32768 <= 17594333495296 + 32768) by (intros x Hx; unfold Sh, SHADOW_OFF; clear -Hx; lia).
  pose proof (SHB (ag_spacebeg (aa_geom A) + c * 2 ^ 32 + mu) ltac:(clear -C1 G13 G14 AU0 MU1; lia)) as B1.
  pose proof (SHB (ag_spacebeg (aa_geom A) + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29) + mfa) ltac:(clear -C1 G13 G14 NF0 MF1 MF2; lia)) as B2.
  assert (B1' : Sh (ag_spacebeg (aa_geom A) + c * 2 ^ 32 + mu) + 32768 <= 17594333495296).
  { unfold Sh, SHADOW_OFF. clear -C1 G13 G14 AU0 MU1. lia. }
  assert (B2' : Sh (ag_spacebeg (aa_geom A) + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29) + mfa) + 32768 <= 17594333495296).
  { unfold Sh, SHADOW_OFF. clear -C1 G13 G14 NF0 MF1 MF2. lia. }
  destruct HZ as [[_ X]|[[_ X]|[[_ X]|[[_ X]|[[X _]|[X|[[_ X]|[_ X]]]]]]]]; clear -X Hz C1 AU0 MU1 NF0 MF1 MF2 G13 G14 T1 PS1 TB B1' B2' HFL HPO N4; lia.
Qed.

Lemma P_HSRC : ltac2:(tb__ "0|1|
S25S50S1S4S2aR2A1Vnew;A3S5S2bR3A1Z10A2S2dVA;Vrb;R4S51S41S1bVrb;A1A2R3A5S4S0S5Z0M0R1A2S9R1S8S11S4VfP;A2A1A2A2S52R6S53S6S24VA;Vrb;A2S7Z4R2A2A2U4S54S4ScR2A1VfP;G0A4A3A2F_;Fidx;F_;F_;F_;Fm;Fph;").
Proof.
  intros ph m HFL HPO (L1 & _ & L3 & _) idx Hidx.
  destruct entry_pure as (HP & Hc0 & NP & RM). pose proof P_csR as (_ & _ & _ & _ & _ & _ & LP & _). cbn zeta in LP. rewrite LP in Hidx.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & _).
  destruct (Z_lt_dec idx nf) as [OLD|NEW].
  - unfold fP. rewrite (P_nth_old c cs (Z.to_nat idx)) by (fold nf in OLD; unfold nf in OLD; clear -OLD Hidx; lia).
    eapply cell_ok_agree_range; [|exact (proj1 (entry_fa _ _ _ _ _ _ _ HE) idx ltac:(fold nv c cs nf; clear -OLD Hidx; lia))].
    cbn [c_addr c_w]. change (Z.of_nat 4) with 4. intros z Hz. apply L1. apply (old_cell_off ph z ltac:(rewrite HFL; clear; lia) HPO). clear -Hz OLD Hidx. lia.
  - set (j := nf + new - 1 - idx). assert (Hj : 0 <= j < new) by (unfold j; clear -NEW Hidx; lia).
    pose proof (L3 j ltac:(rewrite HFL; exact Hj)) as CE. unfold gh_nf in CE. fold nv c cs nf new au S in CE.
    replace (nf + new - 1 - j) with idx in CE by (unfold j; clear; lia).
    unfold fP. replace (Z.to_nat idx) with (Z.to_nat (Z.of_nat (length (cs_free_array cs)) + newZ c cs - 1 - j)) by (rewrite P_newZ; fold nf; unfold j; clear -Hidx; lia).
    rewrite (P_nth_new c cs j ltac:(rewrite P_newZ; exact Hj)). fold au S. exact CE.
Qed.

Lemma P_HDEF : ltac2:(tb__ "0|4|
S25S50S2S1S10S30S29R2A1A1S17A3S5S7Z4M0S6Vnf;Vnew;A2A2M1Vmfa;A2A2S2dVA;Vrb;R3S51S41S1bVrb;A1A2R2A5S4S0S5S6S24VA;Vrb;A2M2S7G0Vnf;A2A2R1A2S9R1S6G2G1A2A2A2S3S1S16S21Q8A1M3A1R5R2A1S13G3A1A3A1F_;Fz;F_;F_;Fm;Fph;").
Proof.
  intros ph m HARM (L1 & L2 & _) z Hz.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & _).
  assert (ZD : zoneR A rb ph z \/ ~ zoneR A rb ph z).
  { unfold zoneR. destruct (revealedp (ph_u ph)), (releasedp (ph_u ph)), (revealedp (ph_f ph)), (releasedp (ph_f ph)), (ph_cnt ph), (ph_ri ph); clear; lia. }
  destruct ZD as [ZI|ZO]; [exact (L2 z ZI)|]. rewrite (L1 z ZO).

  assert (LT : z < FAb A rb + mfa).
  { destruct (Z_lt_dec z (FAb A rb + mfa)) as [X|X]; [exact X|]. exfalso. destruct HARM as [REL|FIT]; [|clear -Hz X FIT; lia].
    apply ZO. unfold zoneR. right; right; right; left. split; [exact REL|]. unfold F0, kFreeArrayMapSize. fold nv c cs mfa. unfold FAb in Hz, X. fold nv c in Hz, X. clear -Hz X N4 MF1. lia. }
  destruct HE as (_ & HA & _). pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  unfold class_repr in P4. change (nthZ (aa_cls A) c cs_empty) with cs in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PR & _).
  destruct (PR z ltac:(unfold FAb in Hz, LT; fold nv c in Hz, LT; fold nf mfa; clear -Hz LT; lia)) as [b Hb].
  rewrite maskv_out in Hb; [change (view segs (rm rb) z = Some b) in Hb; rewrite Hb; discriminate|].
  apply fs_footb_space; [exact HG|]. rewrite kSpaceSize_val. rewrite FAr in Hz. clear -Hz C1 NF0 N4 MF1 MF2 G13 G14. lia.
Qed.

Definition e_srcP : sv := ltac2:(tb__ "0|0|
S18S32S3bS18S34S18S33S18S32S39S37A3S38A3S1cZ2A1A3A3").
Definition e16P : sv := ltac2:(tb__ "0|0|
S18S33S18S32S39S37A3S38A3").
Definition e32P : sv := ltac2:(tb__ "0|0|
S18S32S3aS1dS35S37S1eS56A1A3A3").
Definition e48P : sv := SAlu ALU_ADD vMU (SLit 262144).
Definition e24M : sv := SAlu ALU_ADD vMFA (SLit 262144).

Lemma P_HSRCP : ltac2:(tb__ "0|1|
S1aS27Vrb;R1A2S28VA;Vrb;R2A3S1S21Q40M0A1S19R3S61A2S20G0S6S24VA;Vrb;A2S7Z4SbS8S11S4VfP;A2A1Vk;A2A2A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh. pose proof P_csR as (_ & _ & _ & _ & _ & _ & LP & _). cbn zeta in LP. rewrite LP.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & _).
  destruct HGh as (_ & Q221 & _ & _ & _ & _ & Q226 & Q227 & Q228 & _). unfold gh_nf in Q221. fold nv c cs nf in Q221. fold nv c k in Q227. fold new in Q228.
  unfold e_srcP, vFA, vNF, vNEW, vK. cbn [eval]. rewrite Q221, Q226, Q227, Q228. apply bv_eq.
  rewrite add_val, sll_val, sub_val, add_val. rewrite !u64_lit by (rewrite ?FAr; clear -C1 G13 G14 NF0 MF1 MF2 N4 K1; lia).
  change (2 mod 64) with 2. rewrite (Z.mod_small (nf + new)) by (clear -NF0 MF1 MF2 N4; lia).
  rewrite (Z.mod_small (nf + new - k)) by (clear -NF0 MF1 MF2 N4 KN K1; lia).
  rewrite Z.shiftl_mul_pow2 by (clear; lia). rewrite (Z.mod_small (_ * 2 ^ 2)) by (clear -NF0 MF1 MF2 N4 KN K1; lia).
  rewrite Z.mod_small by (rewrite FAr; clear -C1 G13 G14 NF0 MF1 MF2 N4 KN K1; lia). clear; lia.
Qed.

Lemma P_HRIv : ltac2:(tb__ "0|2|
S1fS1aS27Vrb;R1A2S28VA;Vrb;R2A3S1S21Q40M0A1M1S19R3R4A2S20G0S10S4L_;SaVmfa;S7Z4S6Vnf;Vnew;A2A2A2S6Vmfa;Z40000A2Vmfa;X10x2A2A3S4dVc;Vcs;A2S43S0S1G1S19R5S5eA2S20G0S8S11S4S46R1A1A2A1A2A3S0S1G1S19R5R6A2S20G0S47R1A1A2A3S0S1G1S19R5S5fA2S20G0S44R1A1A2A3S1G1S19R5S60A2S20G0S48R1A1A2A3A2A2A2TcsR;F_;F_;F_;Fr;Fe24;").
Proof.
  intros e24 r HFz HGh E24 csR. pose proof P_csR as (_ & _ & X3 & X5 & X6 & X7 & _). cbn zeta in X3, X5, X6, X7. fold csR in X3, X5, X6, X7.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & _).
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. destruct RG as (_ & E148 & _). fold nv c S in E148.
  destruct HGh as (_ & Q221 & _ & Q223 & Q224 & _ & _ & Q227 & Q228 & _). unfold gh_nf in Q221. fold nv c cs nf in Q221. fold nv c cs au in Q223. fold nv c cs mu in Q224. fold nv c k in Q227. fold new in Q228.
  assert (NS : 0 <= new * S <= 3758096384) by (pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF; destruct (new_nums A rb CF PF) as (_ & _ & _ & _ & _ & M6 & _); cbn zeta in M6; fold nv c cs in M6; fold S au mu new in M6; clear -M6 AU0 MU1 N4 S1; nia).
  rewrite X3, X5, X6, X7. split; [|split; [exact E24|split]].
  - unfold e16P, vNF, vNEW, vK. cbn [eval]. rewrite Q221, Q227, Q228. apply bv_eq. rewrite sub_val, add_val, !u64_lit by (clear -NF0 MF1 MF2 N4 K1 KN; lia).
    rewrite (Z.mod_small (nf + new)) by (clear -NF0 MF1 MF2 N4; lia). rewrite Z.mod_small by (clear -NF0 MF1 MF2 N4 KN K1; lia). reflexivity.
  - unfold e32P, vAU, vNEW, V_SIZE. cbn [eval]. rewrite Q223, Q228, E148. apply bv_eq. rewrite add_val, mul_val, !u64_lit by (clear -AU0 MU1 N4 S1 NS; lia).
    rewrite (Z.mod_small (new * S)) by (clear -NS; lia). rewrite Z.mod_small by (clear -NS AU0 MU1; lia). reflexivity.
  - unfold e48P, vMU. cbn [eval]. rewrite Q224. apply bv_eq. rewrite add_val, !u64_lit by (clear -AU0 MU1; lia). rewrite Z.mod_small by (clear -AU0 MU1; lia). reflexivity.
Qed.
End ARMP.
End SpineMallocQ14.

(* [comment removed for export] *)
Module SpineMallocQiu.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "ss_objs"; "SAlu"; "SLit"; "ss_facts"; "ss_lenient"; "SVar"; "rw"; "swf"; "SPBranch"; "valuation"; "SPNot"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "axst"; "ax_X"; "entailsA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kb.SpineMallocQiu"; "e3r"; "icc"; "r_9N_0"; "ct0N"; "FUEL"; "r_1_0"; "r_2_1"; "W0"; "r_t1N_0"; "s_bkN"; "s_inN"; "xlN"; "nob"; "r_t1N_1"; "cellsfN"; "r_2_0"; "r_t0N_0"; "s_fN"; "y4N"; "y3N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "cE1"; "GR"; "cR1"; "PV4"; "cE2"; "cT1"; "nobj"; "PV6"; "vK"; "O_pccK"; "O_pcm"; "k_e"; "keepn"; "O_ri"; "PNX"; "cR0a"; "fa_e"; "ri_e"; "ri_has"; "vAU"; "vFA"; "vMFA"; "vMU"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineMallocQ1"; "factsQ"; "cQ0"; "entryRq"; "BASEFq"; "BASEOq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "ulink"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "pre_facts"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineMallocQ4"; "swM"; "O_rif"; "idx_sw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_pcc0"; "O_st"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "gh_nf"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "L_rf"; "JLRf"; "JRf"; "NXR"; "NXRC"; "rf_depth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineMallocQ3"; "O_dstc"; "O_srcc"; "e_end"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG"; "BASEG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA";
"aa_cache_inited"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jy.SpineMallocQ6"; "e16N"; "e_srcN"; "phFN"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@Stdlib.Lists.List"; "forallb"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ju.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineMallocQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ju.SpineMallocQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jy.SpineMallocQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k7.SpineMallocQu.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition W0 : list ulink := [].
Definition FUEL : nat := 4000%nat.
Definition e3r : axst := e3u.
Lemma SK3 : ltac2:(tb__ "0|1|
S0S5S6S6SdSdA2SdA2M0A1S5fScG0S5bS10S1cS24A1A1A4S5fScG0S5bSaScS8bS1ScS77S1ScS78S4ScA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX3 : ltac2:(tb__ "0|1|
S0S5S6SdSdA2M0A1S21S24A1S4G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF3b : ltac2:(tb__ "0|0|
S0S3S5aS67S84A1S13S1cS24A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX3 : ltac2:(tb__ "0|0|
S0S3S5cSfS1cS24A1A1PdcA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma WR0a : ltac2:(tb__ "0|0|
S0S3S17S1cS48S24A1A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB0 : ltac2:(tb__ "0|0|
S0S3S95SeS1bS3aA1S52S24A1A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S1fS38S28S1S23Z4147cS4S23A1A3S53S24A1S2A5").
Local Strategy expand [R_1__R].
Definition r_1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition r_1_0 := Eval vm_compute in (nth 0 r_1 (mkLeafA (cQ0 e3r) RsCut)).
Definition cr1 := Eval vm_compute in (cR1 (factsQ e3r) (la_state r_1_0)).
Definition r_2 := Eval vm_compute in (match sym_runA segsA FUEL [0x41704; 0x41560] cr1 true with Some l => l | None => [] end).
Definition r_2_0 := Eval vm_compute in (nth 0 r_2 (mkLeafA cr1 RsCut)).
Definition r_2_1 := Eval vm_compute in (nth 1 r_2 (mkLeafA cr1 RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0S8S5S1eA1M0A1S1fS38S28S1S23Z4147cS4S23A1A3S53S24A1S2A5S7G0S1S1eS29S4S1eA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [r_1_0]). Qed.
Lemma LN_0 : ltac2:(tb__ "0|0|
S0S3S14S1cS53S24A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_0 : ltac2:(tb__ "0|0|
S0S3S5cS3aSfS1cS53S24A1A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_r1 : ltac2:(tb__ "0|0|
S0S3S17S1cS3bS52S24A1S1dS29A1A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_r1 : ltac2:(tb__ "0|5|
S0S8S6S5S6SdSdA2M0A1M1S5SeA1M2A2M3A1S73S1cS1dS29A1M4A1S1cS3bS52S24A1G4A2A1A2S7G3S9G1G2S1G0S9SdSdS4aS51A4S1G0S9SdSdS44S41A4S1G0S9SdSdS49S4dA4S4G0A1A3A3A3S4SeA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_r1 : ltac2:(tb__ "0|1|
S0S3S5dSfS1cS3bS52S24A1S1dS29A1M0A2A1A1SfS1cG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_2 : ltac2:(tb__ "0|1|
S0S8S5S1eA1M0A1S1fS38S28S1S23Z41704S1S23Z41560S4S23A1A3A3S3bS52S24A1S1dS29A1A2S2A5S7G0S1S1eS33S1S1eS2aS4S1eA1A3A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S3S14S1cS3bS52S24A1S1dS29A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_1 : ltac2:(tb__ "0|0|
S0S3S5cS3aSfS1cS3bS52S24A1S1dS29A1A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition nob := Eval vm_compute in ((length (ss_objs (ax_S e3r)) + 2)%nat).
Definition icc := Eval vm_compute in ((length (ss_objs (ax_S e3r)) - 2)%nat).
Definition R_t0N__R : option (list leafA) := ltac2:(tb__ "0|0|
S1fS38S28S1S23Z41570S1S23Z41584S4S23A1A3A3S1dS2aA1S2A5").
Local Strategy expand [R_t0N__R].
Definition r_t0N := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_t0N__R).
Definition r_t0N_0 := Eval vm_compute in (nth 0 r_t0N (mkLeafA (la_state r_2_1) RsCut)).
Definition ct0N := Eval vm_compute in (cT0 (la_state r_t0N_0)).
Definition R_t1N__R : option (list leafA) := ltac2:(tb__ "0|0|
S1fS38S28S1S23Z41570S1S23Z41584S4S23A1A3A3S3eS27A1S2A5").
Local Strategy expand [R_t1N__R].
Definition r_t1N := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_t1N__R).
Definition r_t1N_0 := Eval vm_compute in (nth 0 r_t1N (mkLeafA (cT1 ct0N) RsCut)).
Definition r_t1N_1 := Eval vm_compute in (nth 1 r_t1N (mkLeafA (cT1 ct0N) RsCut)).
Definition s_inN := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0N_0)) (ax_S ct0N)).
Definition s_bkN := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1N_0) nob)) (ax_S ct0N)).
Lemma SK_tN : ltac2:(tb__ "0|1|
S0S5S6S6SdSdA2SdA2M0A1S5fScG0S5bS10S1cS27A1A1A4S5fScG0S5bSaScS56S2bA1S1ScS77S1ScS78S1ScS43S1ScS46S4ScA1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tN : ltac2:(tb__ "0|1|
S0S5S6SdSdA2M0A1S21S27A1S4G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tNb : ltac2:(tb__ "0|0|
S0S3S5aS55S2bS62A2S13S1cS27A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tN : ltac2:(tb__ "0|0|
S0S3S5dSfS1cS27A1A1S47A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1N : ltac2:(tb__ "0|0|
S0S3S17S1cS3eS27A1A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1N : ltac2:(tb__ "0|1|
S0S8S5S1eA1M0A1S1fS38S28S1S23Z41570S1S23Z41584S4S23A1A3A3S3eS27A1S2A5S7G0S1S1eS2cS1S1eS31S4S1eA1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1N__R <: R_t1N__R = Some [r_t1N_0; r_t1N_1]). Qed.
Lemma LN_t1N : ltac2:(tb__ "0|0|
S0S3S14S1cS3eS27A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bN : ltac2:(tb__ "0|1|
S0S5ScA1S10S1cS1dS2cA1A1A1M0SaScS5eScS30G0A3S1ScS86S1ScS85S4ScA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xN : ltac2:(tb__ "0|1|
S0S5ScA1S10S1cS1dS31A1A1A1M0SaScS5eScS30G0A3S1ScS86S1ScS85S4ScA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkN : ltac2:(tb__ "0|0|
S0S3S22S45S1dS2cA1S30A2S27S2dA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkN : ltac2:(tb__ "0|0|
S0S3S61S2dS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4N : ltac2:(tb__ "0|0|
S0SdS60S2dS3cA2S11S57S15S3cA1S12Z4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6N : ltac2:(tb__ "0|0|
S0SdS60S2dS40A2S11S57S15S40A1S12Z4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bNb : ltac2:(tb__ "0|0|
S0S3S5aS1SeS18S58S11S57S15S3cA1S12Z4A1A3S87A3S4SeA1A3S13S1cS1dS2cA1A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xNb : ltac2:(tb__ "0|0|
S0S3S5aS1SeS1aS18S58S11S57S15S3cA1S12Z4A1A3S87A3A1S4SeA1A3S13S1cS1dS31A1A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0N : ltac2:(tb__ "0|1|
S0S8S5S1eA1M0A1S1fS38S28S1S23Z41570S1S23Z41584S4S23A1A3A3S1dS2aA1S2A5S7G0S1S1eS34S4S1eA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0N__R <: R_t0N__R = Some [r_t0N_0]). Qed.
Lemma LN_t0N : ltac2:(tb__ "0|0|
S0S3S14S1cS1dS2aA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0N : ltac2:(tb__ "0|0|
S0S3S5cS3aSfS1cS1dS2aA1A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inN : ltac2:(tb__ "0|0|
S0S3S22S1dS34A1S27S2eA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inN : ltac2:(tb__ "0|0|
S0S3S61S2eS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4N : ltac2:(tb__ "0|0|
S0SdS60S2eS3cA2S11S57S79S12Z10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6N : ltac2:(tb__ "0|0|
S0SdS60S2eS40A2S92A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlN := Eval vm_compute in (keepn (la_state r_t1N_1) nob).
Definition R_9N__R : option (list leafA) := ltac2:(tb__ "0|0|
S1fS38S28S1S23Z41354S4S23A1A3S2fS2A5").
Local Strategy expand [R_9N__R].
Definition r_9N := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_9N__R).
Definition r_9N_0 := Eval vm_compute in (nth 0 r_9N (mkLeafA xlN RsCut)).
Definition cellsfN := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9N_0) icc))) O_ri)).
Definition y3N := Eval vm_compute in (swM (cE2 (cE1 (la_state r_9N_0) icc))).
Definition y4N := Eval vm_compute in (keepn y3N (nobj y3N - 1)).
Definition s_fN := Eval vm_compute in (infer_sub NXRC (ax_S y4N) (ax_S L_rf)).
Lemma R_9N : ltac2:(tb__ "0|1|
S0S8S5S1eA1M0A1S1fS38S28S1S23Z41354S4S23A1A3S2fS2A5S7G0S1S1eS26S4S1eA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9N__R <: R_9N__R = Some [r_9N_0]). Qed.
Lemma LN_9N : ltac2:(tb__ "0|0|
S0S3S14S1cS2fA1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9N : ltac2:(tb__ "0|0|
S0S3S5cS3aSfS1cS2fA1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_y1N : ltac2:(tb__ "0|0|
S0S3S17S1cS39S1dS26A1S25A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_y1N : ltac2:(tb__ "0|5|
S0S8S6S5S6SdSdA2M0A1M1S5SeA1M2A2M3A1S73S1cS1dS26A1M4A1S1cS39G4S25A2A1A2S7G3S9G1G2S1G0S9SdSdS44S41A4S4G0A1A3S4SeA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_y1N : ltac2:(tb__ "0|1|
S0S3S5dSfS1cS39S1dS26A1M0S25A2A1A1SfS1cG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_y1N : ltac2:(tb__ "0|1|
S0S5S6SdSdA2M0A1S21S39S1dS26A1S25A2A1S4G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_y1N : ltac2:(tb__ "0|0|
S0S8ScA1S96ScS10S1cS39S1dS26A1S25A2A1A1S25A3S7ScS42A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_y1N : ltac2:(tb__ "0|2|
S0S5ScA1S10S1cS39S1dS26A1S25A2M0A1A1M1SaScS5eScS6cS3fG0A1U2A2G1A3S1ScS43S1ScS71S32A1S4ScA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_y1N : ltac2:(tb__ "0|0|
S0S3S4bS32S91S4eS4cS4fA5S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_y3N : ltac2:(tb__ "0|0|
S0S3S89S72S3dS39S1dS26A1S25A2A1A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_y3N : ltac2:(tb__ "0|0|
S0S3S94U2S3fS3dS39S1dS26A1S25A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Y3_eqN : ltac2:(tb__ "0|0|
S0S20S70S3dS39S1dS26A1S25A2A1A1S37A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma Y4_eqN : ltac2:(tb__ "0|1|
S0S20S45S70S3dS39S1dS26A1S25A2A1A1M0S6cS3fG0A1U1A2A2S36A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_y3N : ltac2:(tb__ "0|2|
S0S5ScA1S10S1cS70S3dS39S1dS26A1S25A2A1A1M0A1A1M1SaScS5eScS6cS3fG0A1U1A2G1A3S1ScS42S4ScA1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fN : ltac2:(tb__ "0|0|
S0S3S22S36S7fS35A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fN : ltac2:(tb__ "0|0|
S0S3S61S35S83A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma HW0 : ltac2:(tb__ "0|0|
S0S68S62S66A3S0S5S63A1S2bS4S63A1A3F_;"). Proof. intros E; discriminate E. Qed.
Definition pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0N r_t1N_0 r_t1N_1 nob s_bkN
    SK_tN XX_tN (inclb_incl _ _ XF_tNb) NX_tN W_t1N R_t1N LN_t1N OB_bN OB_xN ENT_bkN SID_bkN S_bk4N S_bk6N (In_of_inclb _ _ FB_bNb) (In_of_inclb _ _ FB_xNb)
    (la_state r_2_1) r_t0N_0 s_inN e_srcN R_t0N LN_t0N NX_t0N ENT_inN SID_inN S_in4N S_in6N.
Definition entry_i := refill_entry e3r SK3 XX3 (inclb_incl _ _ XF3b) NX3 WR0a FB0.
Definition prefix_i A Kc rb tp0 md0 TR KIT HKc := refill_prefix A Kc rb tp0 md0 TR KIT HKc FUEL e3r r_1_0 r_2_0 r_2_1 R_1 LN_0 NX_0 W_r1 D_r1 NX_r1 R_2 LN_1 NX_1.
Definition exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv :=
  exit_stepsQ A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE phX PHX HFILLX Hini e16N vMFA vAU vMU HRIv FUEL xlN icc LN_9N NX_9N r_9N_0 cellsfN
    R_9N W_y1N D_y1N NX_y1N XX_y1N IC_y1N OB_y1N RI_y1N ND_y3N NO_y3N OB_y3N.
Definition fin_N A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq HREB HZD HPOST :=
  fin_leaf A Kc rb tp0 md0 W0 UStopLe rho HE HKc phF HREB HZD TR KIT y4N s_fN ENT_fN SID_fN rhoQ tpQ JLq HPOST.
Lemma FJ_Nb : ltac2:(tb__ "0|0|
S0S3S5aS1SeS1aS18S59S50S41A3A1S4SeA1A3S13S1cS1dS2aA1A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem refill_N_i : ltac2:(tb__ "0|4|
S8eS64S23S23S19S5S6bQ40M0A1A1M1S6fS6fOF_;F_;S8cR6R1A2S65R7A1S88S90R9A1S8aA2S0S3S8fRaA1S2A3S76S38S82R7R6S1S6S20S75A2M2S9S20S75S7fS80RbRaR9A3A4S4G2A1A3A5S6fS6dS54RdR9R8R1S2bS62R9A7S88S7dS69S6aG0S16RaPcM3A2A2A1A1S7bReRaA2A2S19G1S5S6eA1S6dS7aR13R12RfReR7S93S7dS69S6aG0S16RfG3A2A2A1A1A1R4R3R2R1AaS8dS7eR14S69S6aG0S16R10G3A2A2A1A2R5R4R2A4F_;Fmd;Ftr;Ftp';Fr;F_;FHE;Fmd0;S6dS19S0S23RdS69S6aG0S16RbG3A2A2A1A3S54R10RcRbR3S2bS62RcA7RbS74S38S7aR11R10RdRcR4S7cA6S1dS33A1R3RcA5R6A2F_;F_;Fr';Fmd0;R8S74S38S81ReRdRcRbA4S24RaR9A5R3A2F_;F_;TQ;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;Fnv0;Fc0;FKc;FA;").
Proof.

  apply (refill_N W0 UStopLe e3r (la_state r_2_0) (la_state r_2_1) xlN y4N (In_of_inclb _ _ FJ_Nb)).
  - intros A Kc c0 nv0 rhoE tp w HBUD Hini Hw. exact (entry_i A Kc c0 nv0 rhoE tp w HBUD Hini Hw).
  - intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE. exact (prefix_i A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho r tp Q HE).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq. exact (fin_N A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq).
Qed.
End SpineMallocQiu.

