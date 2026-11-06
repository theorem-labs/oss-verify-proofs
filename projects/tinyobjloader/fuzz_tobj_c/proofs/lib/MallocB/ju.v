(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jr.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.

(* [comment removed for export] *)
Module SpineCallocRi0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "app"; "Some"; "option"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "ss_facts"; "valuation"; "ss_objs"; "ss_lenient"; "swf"; "SAlu"; "SLit"; "SVar"; "rw"; "SPBranch"; "SPNot"; "rm"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "axst"; "ax_X"; "entailsA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ju.SpineCallocRi0"; "e3r"; "icc"; "r_9N_0"; "W0"; "FUEL"; "ct0N"; "r_1_0"; "r_2_1"; "r_t1N_0"; "s_bkN"; "s_inN"; "xlN"; "e3p"; "nob"; "r_t1N_1"; "cellsfN"; "r_2_0"; "r_t0N_0"; "r_zN_0"; "s_xN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "cE1"; "cE2"; "GR"; "cR1"; "factsR"; "PV4"; "cR0"; "cT1"; "PV6"; "cE3"; "vK"; "O_pcm"; "cE3b"; "k_e"; "F_r0"; "F_r1"; "F_x"; "O_pccK"; "O_ri"; "PNX"; "cE3a"; "cR0a"; "fa_e"; "keepn"; "nobj"; "ri_e"; "ri_has"; "vAU"; "vFA"; "vMFA"; "vMU"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "A_globals"; "Kc_ok"; "malloc_depth"; "mem_keptA"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "O_pcc0"; "O_st"; "E3p"; "E3r"; "F_gen"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "entryR"; "gh_nf"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA";
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineCallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineCallocR6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition W0 : list ulink := Wcan 0.
Definition FUEL : nat := 4000%nat.
Definition e3r := Eval vm_compute in (E3r W0 UStopLe 2).
Lemma E3r_eq : ltac2:(tb__ "0|0|
S0S22S79S29S5cZ2A3S26A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK3 : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S65SdG0S68S13S1eS26A1A1A4S65SdG0S68S8SdS8SdS2SdS93S8SdS64S29A1S5eA3A3S94A3S2SdS76S2SdS77S5SdA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX3 : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S26A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF3b : ltac2:(tb__ "0|0|
S0S4S67S8SfS8SfS63S29S5cA2S62S60A1A3S7aA3S11S1eS26A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX3 : ltac2:(tb__ "0|0|
S0S4S69S10S1eS26A1A1PdcA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma WR0a : ltac2:(tb__ "0|0|
S0S4S15S1eS50S26A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB0 : ltac2:(tb__ "0|0|
S0S4S90SfS1dS3dA1S8SfS11S1eS26A1A1S8SfS49S4aA3A3A3S3A3").
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
S0SaS7S6S7SeSeA2M0A1M1S6SfA1M2A2M3A1S81S1eS1fS2cA1M4A1S1eS3eS3fS26A1G4A2A1A2S9G3ScG1G2S2G0ScSeSeS54S5bA4S2G0ScSeSeS48S45A4S2G0ScSeSeS51S57A4S5G0A1A3A3A3S5SfA1A4A2A3").
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
S0S6S7S7SeSeA2SeA2M0A1S65SdG0S68S13S1eS2bA1A1A4S65SdG0S68S8SdS8bS29A1S2SdS76S2SdS77S2SdS46S2SdS4dS5SdA1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tN : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S2bA1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tNb : ltac2:(tb__ "0|0|
S0S4S67S8aS29S5cA2S11S1eS2bA1A1A2S3A3").
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
S0S6SdA1S13S1eS1fS2eA1A1A1M0S8SdS66SdS33G0A3S2SdS8dS2SdS8cS5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xN : ltac2:(tb__ "0|1|
S0S6SdA1S13S1eS1fS34A1A1A1M0S8SdS66SdS33G0A3S2SdS8dS2SdS8cS5SdA1A3A3A3A3").
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
S0S4S67S2SfS1aS6cS16S6bS18S40A1S17Z4A1A3S8eA3S5SfA1A3S11S1eS1fS2eA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xNb : ltac2:(tb__ "0|0|
S0S4S67S2SfS1bS1aS6cS16S6bS18S40A1S17Z4A1A3S8eA3A1S5SfA1A3S11S1eS1fS34A1A1A1A2S3A3").
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
S0SeS6eS30S40A2S16S6bS7bS17Z10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6N : ltac2:(tb__ "0|0|
S0SeS6eS30S43A2S9aA3").
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
S0SaS7S6S7SeSeA2M0A1M1S6SfA1M2A2M3A1S81S1eS1fS28A1M4A1S1eS3bG4S27A2A1A2S9G3ScG1G2S2G0ScSeSeS48S45A4S5G0A1A3S5SfA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1N : ltac2:(tb__ "0|1|
S0S4S6aS10S1eS3bS1fS28A1M0S27A2A1A1S10S1eG0A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1N : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S3bS1fS28A1S27A2A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1N : ltac2:(tb__ "0|0|
S0SaSdA1S91SdS13S1eS3bS1fS28A1S27A2A1A1S27A3S9SdS4cA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1N : ltac2:(tb__ "0|2|
S0S6SdA1S13S1eS3bS1fS28A1S27A2M0A1A1M1S8SdS66SdS92S53G0A1U2A2G1A3S2SdS46S2SdS97S35A1S5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1N : ltac2:(tb__ "0|0|
S0S4S55S35S99S58S56S59A5S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2N : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S65SdG0S68S13S1eS3cS3bS1fS28A1S27A2A1A1A1A4S65SdG0S68S8SdS8bS29A1S2SdS76S2SdS77S5SdA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2N : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S3cS3bS1fS28A1S27A2A1A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Nb : ltac2:(tb__ "0|0|
S0S4S67S8aS29S5cA2S11S1eS3cS3bS1fS28A1S27A2A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aN : ltac2:(tb__ "0|0|
S0S4S15S1eS4fS3cS3bS1fS28A1S27A2A1A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bN : ltac2:(tb__ "0|0|
S0S4S15S1eS47S3cS3bS1fS28A1S27A2A1A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3N : ltac2:(tb__ "0|1|
S0S4S90SfS1dS10S1eS47S3cS3bS1fS28A1S27A2A1A1A1M0A1A1S8SfS4bS11G0A1A3A3S3A3").
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
S6S7S25S25A2A1M0G0S7cS5dS6S7S22S83A2A1F_;F_;S98R3R2R1A3S22S22S0S22R2S26A3S0S22R2S32A3S7cS5dS12S6S71Q40M1A1A1M2S74S74OF_;F_;S96R4R1A2S5fR5A1S0S4S7dR7A1S3A3S0S25S7fR8S70G1S19R6PcM3A2A2A2Z0A3S82S3aS80R7R6RfR9R8A2A5S74S12S72S85RcR2R9R1S29S5cRaA7S9cS88S7eS70G1S19R3G3A2A2A1A1S86RdR3A2A2S12G2S6S73A1S72S84R12R11R8RfR7S9bS88S7eS70G1S19R8G3A2A2A1A1A1R4R3R2R1AaS1S95S3aS89R13S7eS70G1S19R9G3A2A2A1A2M4R5R4R2A5S61R1bR1aR13G4S1cR9A1S1cR5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;FHE;Fmd0;Frb;S7cS12G2S12RbS75S3aS8fS29S5cR4ReR3A5R12R1R2A5S82S3aS80R3R2R15R4ReA2A5A2FrX;Ftp';Frho';FA';S12S72S12S85RfR3RcR2S29S5cRdA7RcS75S3aS84R10RfR4RdR3S87A6S1fS36A1R2RdA5R7A2F_;Fr';Fmd0;Frb;S12RaS75S3aS8fS29S5cReRdRcA5R12R1RbA5R5A2FrhoE;F_;F_;F_;TQ;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;F_;FE3P;FE3;FHPF;FPFam;FXGL;FCST;").
Proof.
  intros CST XGL PFam HPF E3 E3P -> ->.
  apply (refill_N CST XGL PFam W0 UStopLe e3r e3p (la_state r_2_0) (la_state r_2_1) xlN (la_state r_zN_0) (In_of_inclb _ _ FJ_Nb)).
  - intros A Kc rho rhoE tp w Hini Hcnt Hw. exact (entry_i A Kc rho rhoE tp w HW0 Hini Hcnt Hw).
  - intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE. exact (prefix_i A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho r tp Q HE).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_N CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
Qed.
End SpineCallocRi0.

(* [comment removed for export] *)
Module SpineMallocQ5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "true"; "bool"; "None"; "cons"; "nil"; "option"; "pair"; "prod"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "zoneR"; "JR"; "frozen"; "phase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "NXR"; "L_rf"; "JLRf"; "NXRC"; "refill_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ju.SpineMallocQ5.FINQ"; "JRfin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC"; "AInvQC"; "K0C"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_cache_inited"; "aa_geom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineMallocQ1"; "entryRq"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 DepotCall PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.RebuildR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineMallocQ4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma zoneR_dec : ltac2:(tb__ "0|1|
S2aSdS17S11ScS14R4R3R2R1A4M0SbG0A1A2Fz;Fph;Frb;FA;").
Proof.
  intros A rb ph z. unfold zoneR.
  destruct (revealedp (ph_u ph)), (releasedp (ph_u ph)), (revealedp (ph_f ph)), (releasedp (ph_f ph)), (ph_cnt ph), (ph_ri ph); clear; lia.
Qed.

Section FINQ.
Let segs : list Segment := segsA.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S2eVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis HKc : Kc_ok Kc.
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Variable phF : phase.

Definition JRfin : jpredA := ltac2:(tb__ "0|7|
SdS0SfQ40M0A1M1A1S0S13A1S12SaS29VKc;S23VA;Vc;A2R4R3R2R1A6SaG1SbS14VA;Vrb;VphF;S10G0R1A2M2A4A1S9S6SfQ8A1M3A1M4SeR6R2A2SeVrb;R2A2M5A3F_;Fa;SaG1SaS2fS27G2A2S30G2S26A2A2SbS9G4G5S3G3A1M6A3A1SbS9G4SeR7R3A2G6A3A1F_;F_;Fa;S16Vrb;R4A2A2A2A2Lmd;Ltr;Ltp';Lr';").

Hypothesis HREB : ltac2:(tb__ "0|0|
SdS0SfQ40A1A1S0S13A1S12S15VA;VKc;Vrb;Vtp0;Vmd0;VphF;R4R3R2R1AaS28S23VA;Vc;A2R5R4R2A4F_;Fmd;Ftr;Ftp;Fr;").
Hypothesis HZD : ltac2:(tb__ "0|1|
S11ScS14VA;Vrb;VphF;R1A4M0SbG0A1A2Fz;").

Lemma fin_J : ltac2:(tb__ "0|0|
SdS0SfQ40A1A1S0S13A1S12S15VA;VKc;Vrb;Vtp0;Vmd0;VphF;R4R3R2R1AaS1dR5R4R3R2A4F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HJ. pose proof HJ as (HFz & HGh & HK & HM & HR & HRM).
  destruct HE as ((HRQ & _) & _ & Htp & _ & _ & _ & Htop & _).
  destruct HFz as [Fw Fl].
  split.
  { split; [exact (HREB r tp tr md HJ)|]. split; [exact HK|].
    split; [unfold tp_ok in *; cbn [aa_geom refillA]; rewrite <- (Fw 24%positive) by lia; exact Htp|].
    split; [unfold top_high in *; cbn [aa_geom refillA]; rewrite <- (Fw 10%positive) by lia; rewrite <- (Fw V_DEPTH) by (unfold V_DEPTH; lia); exact Htop|].
    destruct HRQ as (E151 & E152 & E155 & E156). unfold rigidQ. cbn [aa_geom refillA].
    rewrite <- (Fw 151%positive), <- (Fw 152%positive), <- (Fw 155%positive), <- (Fw 156%positive) by lia. exact (conj E151 (conj E152 (conj E155 E156))). }
  destruct HR as (L1 & L2 & _).
  assert (VR : forall (f : word -> option byte) z, 0 <= z < 2 ^ 64 -> (z < IMG_LO \/ IMG_HI <= z) -> view OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA f z = f (Z_to_bv 64 z)).
  { intros f z Hz Hoff. exact (view_rm_off f z Hz Hoff). }
  assert (RAW : forall z, 0 <= z < 2 ^ 64 -> ~ zoneR A rb phF z -> rm r (Z_to_bv 64 z) = rm rb (Z_to_bv 64 z)).
  { intros z Hz NZ. destruct (Z_lt_dec z IMG_LO) as [H1|H1]; [|destruct (Z_le_dec IMG_HI z) as [H2|H2]].
    - rewrite <- !(VR _ z Hz (or_introl H1)). exact (L1 z NZ).
    - rewrite <- !(VR _ z Hz (or_intror H2)). exact (L1 z NZ).
    - apply HRM. lia. }
  split.
  { intros a NZ. pose proof (bv_unsigned_in_range _ a) as Ha. unfold bv_modulus in Ha. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ha. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply RAW; [exact Ha | exact NZ]. }
  split; [|exact (conj Fw Fl)].
  intros a Hb Hd. pose proof (bv_unsigned_in_range _ a) as Ha. unfold bv_modulus in Ha. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ha.
  assert (OFF : bv_unsigned a < IMG_LO \/ IMG_HI <= bv_unsigned a) by (unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, IMG_HI in *; right; lia).
  assert (E : Z_to_bv 64 (bv_unsigned a) = a) by apply Z_to_bv_bv_unsigned.
  pose proof (VR (rm rb) _ Ha OFF) as V1. pose proof (VR (rm r) _ Ha OFF) as V2. rewrite E in V1, V2.
  rewrite <- V2. rewrite <- V1 in Hd.
  destruct (HZD (bv_unsigned a)) as [Z1|Z1]; [exact (L2 _ Z1) | rewrite (L1 _ Z1); exact Hd].
Qed.

Lemma fin_post : ltac2:(tb__ "0|0|
S11S9S11R1Vc;A3S9S2S2bVA;A1S1A3S11S14VA;Vrb;VphF;R1A4S1cS2cVA;A1S1Vc;S2dVA;Vnv;A2R2A5F_;Fz;SdS0SfQ40A1A1S0S13A1S12S1dR4R3R2R1A4SaS1eS18Vrb;R5A3S1aVA;VKc;R9Vrb;Vtp0;R5R4R3R2A9A2F_;Fmd;Ftr;Ftp';Fr';F_;F_;F_;Fc0;").
Proof.
  intros c0 -> Hini HZ r' tp' tr md (J1 & J2 & J3 & J4).
  split; [exact J4|].
  unfold JLRf. split; [exact J1|]. split.
  - intros a NZ. apply J2. intros Z1. apply NZ. rewrite Hini. exact (HZ _ Z1).
  - split; [exact J3 | intros l; symmetry; exact (proj2 J4 l)].
Qed.

Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRokD Kc TR.
Variables (X4 : axst) (s : wsub).
Hypothesis HENT : ltac2:(tb__ "0|0|
S9S2S20VX4;S19Vs;A3S1A3").
Hypothesis HSID : ltac2:(tb__ "0|0|
S9S2S24Vs;S1bA2S1A3").
Variables (rhoQ : valuation) (tpQ : list word) (JLq : jpostA).
Hypothesis HPOST : ltac2:(tb__ "0|0|
SdS0SfQ40A1A1S0S13A1S12S1dR4R3R2R1A4SaS1eS18VrhoQ;R5A3VJLq;VrhoQ;VtpQ;R5R4R3R2A6A2F_;Fmd;Ftr;Ftp';Fr';").

Lemma fin_leaf : ltac2:(tb__ "0|1|
SdS0SfQ40A1A1VTR;S25Vsegs;S15VA;VKc;Vrb;Vtp0;Vmd0;VphF;A6VX4;R2R1A5S22Vsegs;S18VrhoQ;VtpQ;S4S8S1fS21A2M0S7S1fS21S19VJLq;A4S5G0A1A3A5A2Ftp;Fr;").
Proof.
  intros r tp.
  apply (tr_pre Kc TR (trd_ok Kc TR KIT) (SPA segs JRfin L_rf (rho_sub r s) tp)).
  { intros w Hw. apply (SPA_entails_J (JR A Kc rb tp0 md0 phF) JRfin X4 L_rf s r tp w HENT); [|exact Hw].
    intros HJ. pose proof (fin_J _ _ _ _ HJ) as (J1 & J2 & J3 & J4). pose proof (rho_sub_agree s NXRC r HSID) as AG.
    split; [|split; [exact J2 | split; [exact J3|]]].
    - eapply (K0C_stable Kc (refillA A c) HKc); [|apply mat_equiv_refl | exact J1]. eapply agree_below_le; [|exact AG]. unfold QNPRE, NXRC. lia.
    - destruct J4 as [F1 F2]. destruct AG as (Aw & Al & _). split; [intros i Hi; rewrite (F1 i Hi); apply Aw; unfold NXRC; lia | intros l; rewrite (F2 l); apply Al]. }
  apply (tr_done Kc TR KIT). intros w [Hsm HJ]. destruct (HPOST _ _ _ _ HJ) as [AV JL].
  exists L_rf, JLq, (rho_sub r s), tp. split; [left; reflexivity|]. split; [exact AV|]. split; [exact Hsm | exact JL].
Qed.
End FINQ.
End SpineMallocQ5.

(* [comment removed for export] *)
Module SpineMallocQ10.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "sprop"; "SAlu"; "eval"; "ss_next"; "ss_facts"; "valuation"; "sprop_below"; "ss_objs"; "swf"; "smatch"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "sym_runA"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "bool"; "true"; "nat"; "prod"; "pair"; "Some"; "app"; "option"; "false"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "modulo"; "lt"; "pow"; "ge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "rMS"; "sMS"; "GR"; "nxt"; "O_pcm"; "O_ri"; "addobjs"; "idx_rot"; "nobj"; "pcof"; "relM"; "updR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "frozen"; "ghosts"; "mlink"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "seq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineMallocQ9"; "O_piece"; "O_shp"; "sh_e"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ju.SpineMallocQ10"; "a2_e"; "cMr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@Stdlib.Lists.List"; "forallb"; "In"; "incl"; "@Corelib.Init.Peano"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP"; "pbase"; "ph_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineMallocQ1"; "BASEFq"; "BASEOq"; "entryRq"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineMallocQ9.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition a2_e (eb : sv) : sv := ltac2:(tb__ "0|1|
S7S48S7S46S7S47S7S46Veb;S5Z3fff8A1A3S5Z3A1M0A3S5Z1A1A3S7S47Veb;G0A3A3").
Definition cMr (E : axst) : axst := ltac2:(tb__ "0|2|
S34S17S6A1M0VE;S32VE;A1S16S1cS1bS4A2M1S1dS1bS4UcS5Z8000A1A4S17G1A1A3S17S3A1S21G0S2cVE;A1A8").
Definition cMc (E : axst) (eb : sv) : axst := ltac2:(tb__ "0|0|
S2fS52VE;A1S16S3S42Veb;A1S17S3A1A3S2cVE;A1A3").
Definition dMSf (C : axst) : axst := ltac2:(tb__ "0|0|
S61S50VC;S2aVC;A1S29VC;A1A3SaS11VC;A1A1A2").

Lemma idx_rot_ok : ltac2:(tb__ "0|1|
S1bS57U1M0R1A2S1bS2S55S1bR1S1fS1bS3eG0S45R3G0A2A2S16S1bU0S17S1bA1A3A3A3S58R1R3A2A2Fi;F_;Fn;").
Proof.
  intros n Hn i. rewrite in_app_iff, in_seq. cbn [In]. lia.
Qed.

Section VALS.
Variables (r : valuation) (eb : sv) (B : Z).
Hypothesis EB : ltac2:(tb__ "0|0|
S0S22S3bQ40S8Vr;Veb;A2A2VB;A3").
Hypothesis HB : ltac2:(tb__ "0|1|
S1S24Z0M0VB;A2S1S26S23VB;Z40000A2S27Z2Z3eA2A2S0S22S25VB;Z10000A2G0A3A2A2").

Lemma a2_val : ltac2:(tb__ "0|0|
S0S3aQ40A1S8Vr;S51Veb;A1A2S8Vr;S5Z8000A1A2A3").
Proof.
  destruct HB as (B0 & B1 & BM). destruct (proj1 (Z.mod_divide B 65536 ltac:(lia)) BM) as [q Hq].
  unfold a2_e. cbn [eval]. apply bv_eq. rewrite sub_val, add_val, !srl_val, add_val, EB, !u64_lit by lia.
  change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (Z.mod_small (B + 262136)) by lia. rewrite Hq.
  replace ((q * 65536 + 262136) / 8) with (q * 8192 + 32767) by (apply Z.div_unique with 0; lia).
  replace (q * 65536 / 8) with (q * 8192) by (apply Z.div_unique with 0; lia).
  rewrite (Z.mod_small (q * 8192 + 32767 + 1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sh_val : ltac2:(tb__ "0|0|
S0S22S3bQ40S8Vr;S43Veb;A1A2A2S4cVB;A1A3").
Proof.
  destruct HB as (B0 & B1 & BM). unfold sh_e, gsv, shb. cbn [eval]. rewrite add_val, srl_val, EB, !u64_lit by (unfold SHADOW_OFF; lia).
  change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold Sh.
  pose proof (Z.div_le_upper_bound B 8 (2 ^ 59) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos B 8 ltac:(lia) ltac:(lia)).
  rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity.
Qed.
End VALS.

Section MEMSET.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S0S4fVst;S4eA3S0S18S4dA1VW;S17S4dA1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S6dVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH1 : ltac2:(tb__ "0|0|
S0S1bS6aVp;Vph;A2U1A3").
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S69VA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
SbS37Vrb;R1A2S38VA;Vrb;R2A3S0S22S3bQ40S8R3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S1S24S23S68S67VA;A1A1M0Z100000000A2VB;A2S1S24S23VB;Z40000A2S23G0Z2000000000A2A2S0S22S25VB;Z10000A2Z0A3A2A2").
Hypothesis HROOM : ltac2:(tb__ "0|0|
S18S3aQ40A1A1S3fS39VA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S28S64R2R3A2Z8000A2F_;Fmd;Ftp;").

Variable F : nat.
Variables (G1 : axst) (LM : leafA).
Let EM : axst := la_state LM.
Let CMR : axst := cMr EM.
Let CMC : axst := cMc EM eb.
Let DM : axst := dMSf CMC.
Let RM : axst := rotM DM.
Hypothesis R_m : ltac2:(tb__ "0|1|
S0S20S18S12A1M0A1S15S35VF;S16S22Zdb004S17S22A1A3VG1;S1aA5S1eG0S16S12VLM;S17S12A1A3A2A3").
Hypothesis LN_g : ltac2:(tb__ "0|0|
S0S19S10S11VG1;A1A1S21A3").
Hypothesis NX_g : ltac2:(tb__ "0|0|
S0S19S44S2bS9S11VG1;A1A1A2S1aA3").
Hypothesis SK_m : ltac2:(tb__ "0|1|
S0S18S1cS1cS4S4A2S4A2M0A1S3cS3G0S53SdS11VEM;A1A1A4S3cS3G0S53S1fS3S6cVW;A1S16S3S65S16S3S66S16S3S2dS16S3S2eS16S3S41Veb;A1S17S3A1A3A3A3A3A3A3A4A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S56S6S6bVW;Vst;A2SaS11VEM;A1A1A3").
Hypothesis XX_m : ax_X EM = [].
Hypothesis W_mr : ltac2:(tb__ "0|0|
S0S19SeS11VCMR;A1A1S1aA3").
Hypothesis D_mr : ltac2:(tb__ "0|4|
S0S20S1cS18S1cS4S4A2M0A1M1S18S6A1M2A2M3A1S5eS11VEM;A1S11VCMR;A1A2S1eG3S1dG1G2S16G0S1dS4S4S51Veb;A1S5Z8000A1A4S17G0A1A3S17S6A1A4A2A3").
Hypothesis W_mc : ltac2:(tb__ "0|0|
S0S19SeS11VCMC;A1A1S1aA3").
Hypothesis E_ms : ltac2:(tb__ "0|1|
S0S20S18S3A1M0A1S63VCMC;S49S2aVCMC;A1A3S1eG0S29VCMC;A1A2A3").
Hypothesis CHK_ms : ltac2:(tb__ "0|0|
S0S19S62VCMC;S49S2aVCMC;A1S29VCMC;A1S3cS12S13S14S4aA4A5S1aA3").
Hypothesis NF_ms : ltac2:(tb__ "0|0|
S0S19S44S5dS9S11VCMC;A1A1A2S1aA3").
Hypothesis NX_ms : ltac2:(tb__ "0|0|
S0S19S44S2bS9S11VCMC;A1A1A2S1aA3").
Hypothesis FBC_ms : ltac2:(tb__ "0|1|
S0S19S54S6ScS9S11VCMC;A1M0A1A1SaG0A1A3S1aA3").
Hypothesis FBT_ms : ltac2:(tb__ "0|0|
S0S19S54S6ScS9S11S50VCMC;S2aVCMC;A1S29VCMC;A1A3A1A1A1SaS11VCMC;A1A1A3S1aA3").
Hypothesis ND_r : ltac2:(tb__ "0|0|
S0S19S5fS30VDM;A1A1S1aA3").
Hypothesis NO_r : (1 <= nobj DM)%nat.
Hypothesis OB_r : ltac2:(tb__ "0|1|
S0S18S3A1SdS11VRM;A1A1M0S1fS3S3dS3S45S31VDM;A1U2A2G0A3S16S3S41Veb;A1S16S3S42Veb;A1S17S3A1A3A3A3A3").

Let ph2 : phase := ph_set p 2 ph.
Let ph3 : phase := ph_set p 3 ph.

Lemma piece_nums : ltac2:(tb__ "0|2|
S1S24Z0M0VB;A2S1S26S23VB;Z40000A2S27Z2Z3eA2A2S1S0S22S25VB;Z10000A2G0A3S1S0S22S25S4cVB;A1M1Z1000A2G0A3S1S24Z2008fff7000G1A2S24S23G1Z8000A2Z10007fff8000A2A2A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0.
  destruct CF0 as (_ & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _). destruct HBn as (HB1 & HB2 & HB3).
  destruct (sh_run_nums (ag_spacebeg (aa_geom A)) B ltac:(clear -G13; lia) HB1 HB2 ltac:(clear -G14 TG; lia) HB3) as (Q1 & Q2 & Q3 & _).
  split; [clear -HB1 G13; lia|]. split; [clear -HB2 G14 TG; lia|]. split; [exact HB3|]. split; [exact Q1|]. split; [exact Q2 | exact Q3].
Qed.

Lemma piece_release : ltac2:(tb__ "0|1|
SbS18S3aQ40A1A1S18S40A1M0S59S3fS3fSfS35R6S11VRM;A1S1dG0S5aR4S5bR3R2A2A4A4S36VA;VKc;Vrb;Vtp0;Vmd0;Vph2;R7R6R5R2AaS36VA;VKc;Vrb;Vtp0;Vmd0;Vph3;S60R8S16S3S41Veb;A1S16S3S42Veb;A1S17S3A1A3A3R5A3R7R6R3AaF_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr ms md mdJ Hsm (HFz & HGh & HK' & HM & HR & HRM).
  destruct piece_nums as (B0 & B1 & BM & Q1 & Q2 & Q3).
  set (R := [O_piece eb; O_shp eb]). set (r3 := rho_absorb r R ms).
  pose proof (HBv r HFz HGh) as EB.
  assert (RNp : obj_range r (O_piece eb) = (B, B + 262144)).
  { unfold O_piece. rewrite obj_range_mk by (clear; lia). rewrite EB. f_equal; clear; lia. }
  assert (RNs : obj_range r (O_shp eb) = (Sh B, Sh B + 32768)).
  { unfold O_shp. rewrite obj_range_mk by (clear; lia). rewrite (sh_val r eb B EB (conj B0 (conj B1 BM))). f_equal; clear; lia. }
  assert (G2 : ph_get p ph2 = 2%nat) by (unfold ph2; apply ph_get_set).
  assert (E3 : ph3 = ph_set p 3 ph2) by (unfold ph3, ph2; rewrite ph_set_set; reflexivity).
  assert (ZR : forall z, zoneR A rb ph3 z <-> (zoneR A rb ph2 z \/ B <= z < B + 262144)) by (intros z; rewrite E3; exact (zone_release A rb p ph2 z G2)).
  assert (ZS : forall z, Sh B <= z < Sh B + 32768 -> zoneR A rb ph2 z).
  { intros z Hz. unfold ph2. apply (zone_reveal A rb p ph z PH1). right. exact Hz. }
  set (m := view segs (rm r)) in *. set (m3 := view segs (rm r3)).
  assert (MO : forall z, ~ (B <= z < B + 262144) -> ~ (Sh B <= z < Sh B + 32768) -> m3 z = m z).
  { intros z H1 H2. unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RNp | rewrite RNs]; cbn [fst snd]; assumption. }
  assert (MIN : forall z, (B <= z < B + 262144 \/ Sh B <= z < Sh B + 32768) -> m3 z <> None).
  { intros z Hz.
    assert (Hz64 : 0 <= z < 2 ^ 64) by (clear -Hz B0 B1 Q2 Q3; lia).
    destruct Hz as [Hz|Hz].
    - destruct (absorb_obj r (ax_S RM) tr ms md _ R (O_piece eb) Hsm OB_r (or_introl eq_refl)) as (_ & _ & ASp & _).
      cbn [ob_base O_piece ob_dflt] in ASp. unfold obj_lo_of, obj_hi_of in ASp. cbn [ob_lo ob_hi O_piece] in ASp. rewrite !soff_lit_small in ASp by (clear; lia). rewrite EB in ASp.
      destruct (ASp (or_intror eq_refl) (z - B) ltac:(clear -Hz; lia)) as [x Hx]. replace (B + (z - B)) with z in Hx by (clear; lia).
      unfold m3. rewrite view_in by exact Hz64. fold r3 in Hx. rewrite Hx. discriminate.
    - destruct (absorb_obj r (ax_S RM) tr ms md _ R (O_shp eb) Hsm OB_r (or_intror (or_introl eq_refl))) as (_ & _ & ASp & _).
      cbn [ob_base O_shp ob_dflt] in ASp. unfold obj_lo_of, obj_hi_of in ASp. cbn [ob_lo ob_hi O_shp] in ASp. rewrite !soff_lit_small in ASp by (clear; lia).
      rewrite (sh_val r eb B EB (conj B0 (conj B1 BM))) in ASp.
      destruct (ASp (or_introl eq_refl) (z - Sh B) ltac:(clear -Hz; lia)) as [x Hx]. replace (Sh B + (z - Sh B)) with z in Hx by (clear; lia).
      unfold m3. rewrite view_in by exact Hz64. fold r3 in Hx. rewrite Hx. discriminate. }
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HK'|].
  split; [rewrite E3; exact (mlink_release A rb tp0 md0 p ph2 tp mdJ HM G2)|].
  split.
  - apply (rlink_quiet_intro A rb ph2 ph3 _ m m3); [unfold ph3; apply ph_quiet_set; exact PQ | | exact HR | |].
    + intros z Hz. apply ZR. left. exact Hz.
    + intros z Hz. apply MO; intros X; apply Hz; apply ZR; [right; exact X | left; exact (ZS z X)].
    + intros z Hz. apply ZR in Hz.
      assert (D : (B <= z < B + 262144 \/ Sh B <= z < Sh B + 32768) \/ ~ (B <= z < B + 262144 \/ Sh B <= z < Sh B + 32768)) by (clear; lia).
      destruct D as [D|D]; [exact (MIN z D)|]. rewrite MO by (clear -D; lia).
      destruct Hz as [Hz|Hz]; [exact (proj1 (proj2 HR) z Hz) | exfalso; apply D; left; exact Hz].
  - apply (rmlink_absorb _ r R ms HRM). intros o [<-|[<-|[]]]; [rewrite RNp | rewrite RNs]; cbn [fst snd]; unfold IMG_LO, IMG_HI.
    + pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. destruct CF0 as (_ & _ & _ & _ & _ & (_ & G13 & _) & _).
      destruct HBn as (HB1 & _). right. clear -HB1 G13. lia.
    + right. clear -Q2. lia.
Qed.

Theorem piece_map : ltac2:(tb__ "0|1|
SbS18S3aQ40A1A1M0S5cSbG0VTR;S4bS35S36VA;VKc;Vrb;Vtp0;Vmd0;Vph3;A6S33VDM;A1R2R1A5R3A2Ftp';Fr';VTR;S4bS35S36VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VG1;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC. destruct piece_nums as (B0 & B1 & BM & Q1 & Q2 & Q3).
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0xdb004] G1 [LM] ph r tp Q R_m LN_g NX_g).
  intros L r1 [<-|[]] _. fold EM.

  apply (tr_cut Kc TR KIT (list word * valuation) _ (fun x => SPA segs (JRp ph2) EM (snd x) (fst x ++ tp)) Q).
  { intros w Hw. destruct (piece_reveal A Kc rb tp0 md0 W st rho HW HE p eb ph PH1 PQ HBv HBn HROOM EM SK_m XF_m r1 tp w Hw) as (tpn & r' & H').
    exists (tpn, r'). exact H'. }
  intros [tpn r2]. cbn [fst snd]. set (tp2 := tpn ++ tp).

  apply (tr_pure Kc TR KIT (Forall (fun o => ranges_disjoint (obj_range r2 o) (Sh B, Sh B + 32768)) (ss_objs (ax_S EM)))).
  { intros w Hw. assert (G2 : ph_get p ph2 = 1%nat -> False) by (unfold ph2; rewrite ph_get_set; discriminate).
    destruct Hw as [HsmA HJ]. pose proof HJ as (HFz & HGh & _).
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
    destruct (arm_extra_ranges A rb r2 CF0 RG HGh) as (EBx & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
    unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
    destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
    pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
    destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S EM) [O_pcc0; O_st; O_pcm; O_ri; O_piece eb] r2 _ HW HE HFz Hsm SK_m XF_m) as (ob & ox & EO & SKx & BZ).
    destruct ox as [|oc [|os [|om [|ori [|opc [|? ?]]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
    assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
    assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
    assert (SKp : skel opc = skel (O_piece eb)) by (clear -SKx; congruence).
    rewrite <- (obj_range_skel r2 oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r2 os O_st SKs) in RNs.
    rewrite <- (obj_range_skel r2 om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r2 ori O_ri SKr) in RNr.
    assert (RNp : obj_range r2 opc = (B, B + 262144)).
    { rewrite (obj_range_skel r2 opc (O_piece eb) SKp). unfold O_piece. rewrite obj_range_mk by (clear; lia). rewrite (HBv r2 HFz HGh). f_equal; clear; lia. }
    assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; clear; lia).
    destruct HBn as (HB1 & HB2 & _).
    rewrite EO. apply Forall_app. split.
    - apply BZ. right; right. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. clear -Q2 Q3. lia.
    - repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr, ?RNp; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr;
        unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; clear -Q2 Q3 HB1 HB2 C1 T1 T2 TB G13; lia. }
  intros OBJD.

  apply (jr_restate A Kc rb tp0 md0 TR KIT EM (ax_S CMR) _ _ ph2 r2 tp2 Q W_mr D_mr ltac:(apply Pos.eqb_refl)).
  { intros tr md (HFz & HGh & _) _. split; [|constructor]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    exact (a2_val r2 eb B (HBv r2 HFz HGh) (conj B0 (conj B1 BM))). }
  change (ax_setS EM (ax_S CMR)) with CMR.

  apply (tr_pre Kc TR KIT (SPA segs (JRp ph2) CMC r2 tp2)).
  { intros w Hw. pose proof (proj2 Hw) as HJ. pose proof HJ as (HFz & HGh & _ & _ & HR & _).
    pose proof (sh_val r2 eb B (HBv r2 HFz HGh) (conj B0 (conj B1 BM))) as ESH.
    apply (SPA_carve_unk segs (JRp ph2) r2 CMR tp2 w (sh_e eb) (SLit 0) (SLit 32768) (nxt EM) Hw W_mc ltac:(apply Pos.le_refl)); rewrite ?ESH, ?soff_lit_small by (clear; lia).
    - clear; lia.
    - clear; lia.
    - clear -Q2; lia.
    - clear -Q3; lia.
    - replace (Sh B + 0) with (Sh B) by (clear; lia). change (ss_objs (ax_S CMR)) with (ss_objs (ax_S EM) ++ []). rewrite app_nil_r. exact OBJD.
    - intros a Ha. assert (Ha64 : 0x643000 <= a < 2 ^ 64) by (clear -Ha Q2 Q3; lia).
      assert (ZN : zoneR A rb ph2 a) by (unfold ph2; apply (zone_reveal A rb p ph a PH1); right; fold B; clear -Ha; lia).
      pose proof (proj1 (proj2 HR) a ZN) as D. rewrite view_in in D by (clear -Ha64; lia).
      pose proof (wok_rd_off_image (rm r2) a) as WK.
      destruct (rd_of segs (rm r2) (Z_to_bv 64 a)) as [x|]; [exact (WK x Ha64 eq_refl) | contradiction].
    - unfold xwords_clear. change (ax_X CMR) with (ax_X EM). rewrite XX_m. intros rr y j []. }

  apply (tr_facts Kc TR KIT). intros HFC.
  apply (tr_memset Kc TR KIT (JRp ph2) CMC (sMS CMC) (rMS CMC) r2 tp2 Q (JR_K A Kc rb tp0 md0 ph2)
           (JR_stable A Kc rb tp0 md0 ph2 _ HKc ltac:(apply Pos.leb_le; exact NX_ms)) ltac:(apply Pos.leb_le; exact NF_ms) E_ms CHK_ms).
  intros r3 tp3 Hag.
  apply (tr_pre Kc TR KIT (SPA segs (JRp ph2) DM r3 tp3)).
  { intros w Hw. apply SPA_refacts; [exact Hw | exact FBT_ms |]. intros _. exact (Forall_holds_agree _ r2 r3 _ Hag FBC_ms HFC). }

  apply (tr_pre Kc TR KIT (SPA segs (JRp ph2) RM r3 tp3)).
  { intros w Hw. apply (SPA_select segs (JRp ph2) r3 DM (idx_rot DM) tp3 w Hw ND_r).
    - intros i Hi. apply (idx_rot_ok (nobj DM) NO_r i). exact Hi.
    - intros i Hi. apply (idx_rot_ok (nobj DM) NO_r i). exact Hi. }
  apply (tr_cut Kc TR KIT valuation _ (fun r4 => SPA segs (JRp ph3) (relM DM) r4 tp3) Q); [|intros r4; exact (HC r4 tp3)].
  intros [tr [ms md]] Hw. exists (rho_absorb r3 [O_piece eb; O_shp eb] (vms md tp3 ms)).
  apply (SPA_unobj_J (JRp ph2) (JRp ph3) r3 RM _ [O_piece eb; O_shp eb] tp3 tr ms md OB_r Hw).
  intros Hsm HJ. exact (piece_release r3 tp3 tr (vms md tp3 ms) (vmd md) md Hsm HJ).
Qed.
End MEMSET.
End SpineMallocQ10.

(* [comment removed for export] *)
Module SpineCallocRi1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "app"; "Some"; "option"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "ss_facts"; "valuation"; "ss_objs"; "ss_lenient"; "swf"; "SAlu"; "SLit"; "SVar"; "rw"; "SPBranch"; "SPNot"; "rm"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "axst"; "ax_X"; "entailsA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ju.SpineCallocRi1"; "e3r"; "icc"; "r_9N_0"; "W0"; "FUEL"; "ct0N"; "r_1_0"; "r_2_1"; "r_t1N_0"; "s_bkN"; "s_inN"; "xlN"; "e3p"; "nob"; "r_t1N_1"; "cellsfN"; "r_2_0"; "r_t0N_0"; "r_zN_0"; "s_xN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "cE1"; "cE2"; "GR"; "cR1"; "factsR"; "PV4"; "cR0"; "cT1"; "PV6"; "cE3"; "vK"; "O_pcm"; "cE3b"; "k_e"; "F_r0"; "F_r1"; "F_x"; "O_pccK"; "O_ri"; "PNX"; "cE3a"; "cR0a"; "fa_e"; "keepn"; "nobj"; "ri_e"; "ri_has"; "vAU"; "vFA"; "vMFA"; "vMU"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLeOrPc"; "KcA"; "A_globals"; "Kc_ok"; "malloc_depth"; "mem_keptA"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "O_pcc0"; "O_st"; "E3p"; "E3r"; "F_gen"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "entryR"; "gh_nf"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA";
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineCallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineCallocR6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition W0 : list ulink := Wcan 1.
Definition FUEL : nat := 4000%nat.
Definition e3r := Eval vm_compute in (E3r W0 UStopLeOrPc 3).
Lemma E3r_eq : ltac2:(tb__ "0|0|
S0S22S79S29S5cZ3A3S26A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK3 : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S65SdG0S68S13S1eS26A1A1A4S65SdG0S68S8SdS8SdS2SdS93S8SdS64S29A1S5eA3A3S94A3S2SdS76S2SdS77S5SdA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX3 : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S26A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF3b : ltac2:(tb__ "0|0|
S0S4S67S8SfS8SfS63S29S5cA2S62S60A1A3S7aA3S11S1eS26A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX3 : ltac2:(tb__ "0|0|
S0S4S69S10S1eS26A1A1PdcA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma WR0a : ltac2:(tb__ "0|0|
S0S4S15S1eS50S26A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB0 : ltac2:(tb__ "0|0|
S0S4S90SfS1dS3dA1S8SfS11S1eS26A1A1S8SfS49S4aA3A3A3S3A3").
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
S0SaS7S6S7SeSeA2M0A1M1S6SfA1M2A2M3A1S81S1eS1fS2cA1M4A1S1eS3eS3fS26A1G4A2A1A2S9G3ScG1G2S2G0ScSeSeS54S5bA4S2G0ScSeSeS48S45A4S2G0ScSeSeS51S57A4S5G0A1A3A3A3S5SfA1A4A2A3").
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
S0S6S7S7SeSeA2SeA2M0A1S65SdG0S68S13S1eS2bA1A1A4S65SdG0S68S8SdS8bS29A1S2SdS76S2SdS77S2SdS46S2SdS4dS5SdA1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tN : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S2bA1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tNb : ltac2:(tb__ "0|0|
S0S4S67S8aS29S5cA2S11S1eS2bA1A1A2S3A3").
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
S0S6SdA1S13S1eS1fS2eA1A1A1M0S8SdS66SdS33G0A3S2SdS8dS2SdS8cS5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xN : ltac2:(tb__ "0|1|
S0S6SdA1S13S1eS1fS34A1A1A1M0S8SdS66SdS33G0A3S2SdS8dS2SdS8cS5SdA1A3A3A3A3").
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
S0S4S67S2SfS1aS6cS16S6bS18S40A1S17Z4A1A3S8eA3S5SfA1A3S11S1eS1fS2eA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xNb : ltac2:(tb__ "0|0|
S0S4S67S2SfS1bS1aS6cS16S6bS18S40A1S17Z4A1A3S8eA3A1S5SfA1A3S11S1eS1fS34A1A1A1A2S3A3").
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
S0SeS6eS30S40A2S16S6bS7bS17Z10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6N : ltac2:(tb__ "0|0|
S0SeS6eS30S43A2S9aA3").
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
S0SaS7S6S7SeSeA2M0A1M1S6SfA1M2A2M3A1S81S1eS1fS28A1M4A1S1eS3bG4S27A2A1A2S9G3ScG1G2S2G0ScSeSeS48S45A4S5G0A1A3S5SfA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1N : ltac2:(tb__ "0|1|
S0S4S6aS10S1eS3bS1fS28A1M0S27A2A1A1S10S1eG0A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1N : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S3bS1fS28A1S27A2A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1N : ltac2:(tb__ "0|0|
S0SaSdA1S91SdS13S1eS3bS1fS28A1S27A2A1A1S27A3S9SdS4cA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1N : ltac2:(tb__ "0|2|
S0S6SdA1S13S1eS3bS1fS28A1S27A2M0A1A1M1S8SdS66SdS92S53G0A1U2A2G1A3S2SdS46S2SdS97S35A1S5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1N : ltac2:(tb__ "0|0|
S0S4S55S35S99S58S56S59A5S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2N : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S65SdG0S68S13S1eS3cS3bS1fS28A1S27A2A1A1A1A4S65SdG0S68S8SdS8bS29A1S2SdS76S2SdS77S5SdA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2N : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S3cS3bS1fS28A1S27A2A1A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Nb : ltac2:(tb__ "0|0|
S0S4S67S8aS29S5cA2S11S1eS3cS3bS1fS28A1S27A2A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aN : ltac2:(tb__ "0|0|
S0S4S15S1eS4fS3cS3bS1fS28A1S27A2A1A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bN : ltac2:(tb__ "0|0|
S0S4S15S1eS47S3cS3bS1fS28A1S27A2A1A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3N : ltac2:(tb__ "0|1|
S0S4S90SfS1dS10S1eS47S3cS3bS1fS28A1S27A2A1A1A1M0A1A1S8SfS4bS11G0A1A3A3S3A3").
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
S6S7S25S25A2A1M0G0S7cS5dS6S7S22S83A2A1F_;F_;S98R3R2R1A3S22S22S0S22R2S26A3S0S22R2S32A3S7cS5dS12S6S71Q40M1A1A1M2S74S74OF_;F_;S96R4R1A2S5fR5A1S0S4S7dR7A1S3A3S0S25S7fR8S70G1S19R6PcM3A2A2A2Z0A3S82S3aS80R7R6RfR9R8A2A5S74S12S72S85RcR2R9R1S29S5cRaA7S9cS88S7eS70G1S19R3G3A2A2A1A1S86RdR3A2A2S12G2S6S73A1S72S84R12R11R8RfR7S9bS88S7eS70G1S19R8G3A2A2A1A1A1R4R3R2R1AaS1S95S3aS89R13S7eS70G1S19R9G3A2A2A1A2M4R5R4R2A5S61R1bR1aR13G4S1cR9A1S1cR5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;FHE;Fmd0;Frb;S7cS12G2S12RbS75S3aS8fS29S5cR4ReR3A5R12R1R2A5S82S3aS80R3R2R15R4ReA2A5A2FrX;Ftp';Frho';FA';S12S72S12S85RfR3RcR2S29S5cRdA7RcS75S3aS84R10RfR4RdR3S87A6S1fS36A1R2RdA5R7A2F_;Fr';Fmd0;Frb;S12RaS75S3aS8fS29S5cReRdRcA5R12R1RbA5R5A2FrhoE;F_;F_;F_;TQ;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;F_;FE3P;FE3;FHPF;FPFam;FXGL;FCST;").
Proof.
  intros CST XGL PFam HPF E3 E3P -> ->.
  apply (refill_N CST XGL PFam W0 UStopLeOrPc e3r e3p (la_state r_2_0) (la_state r_2_1) xlN (la_state r_zN_0) (In_of_inclb _ _ FJ_Nb)).
  - intros A Kc rho rhoE tp w Hini Hcnt Hw. exact (entry_i A Kc rho rhoE tp w HW0 Hini Hcnt Hw).
  - intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE. exact (prefix_i A Kc rb tp0 md0 TR KIT HKc W0 UStopLeOrPc rho r tp Q HE).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_N CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
Qed.
End SpineCallocRi1.

(* [comment removed for export] *)
Module CRebuildRN.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "alloc_top"; "m_vm_lazy"; "vm_maps"; "vm_noaccess"; "vm_limit"; "vm_reserved"; "event"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "true"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_depot"; "aa_ptr_committed"; "aa_sec"; "DG"; "aa_cache_inited"; "ag_spacebeg"; "ageom"; "depot_state"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "model_inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "prim_credit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "depot_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineCallocR6"; "phFN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "JR"; "PCE"; "entryR"; "gh_nf"; "zoneR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "mem_keptA"; "ulink"; "ustop"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineCallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineCallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.RebuildR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Lemma depot_vm_fields : ltac2:(tb__ "0|4|
S21S6S6SeS28Q40A1M0A1S0SeSfG0G0A2A1M1S9S5R2A1A1S9S5R3A1M2A1A3S0G1SaG2A1SaS5R4A1M3A1A3S0S4S7G3A1S7S5R5A1A1A3S0G1S8R5A1S8R6A1A3S30R8R7R5A3S30R9R7R6A3F_;F_;F_;F_;F_;Ftp;Fmd';Fmd;FG;").
Proof. intros G md md' tp E1 E2 E3 E4 [d1 d2 d3 d4 d5 d6]. constructor; rewrite ?E1, ?E2, ?E3, ?E4; assumption. Qed.

Lemma model_inv_fields : ltac2:(tb__ "0|6|
S19S19SeS28Q40A1M0A1S6S6S0S24S1aR4A1S1aR5A1A3S0SeS26A1S20R5A1S20R6A1A3S0S25S1eR6A1S1eR7A1A3S0S4S1fR7A1S1fR8A1A3S0S4S1dR8A1S1dR9A1A3S0S4S1cR9A1S1cRaA1A3S0S4S1bRaA1S1bRbA1A3S0S4S2dRbA1S2dRcA1A3S0SeSfG0G0A2A1M1S9S5R9A1A1S9S5RaA1M2A1A3S0G1ScG2A1ScS5RbA1M3A1A3S0G1SaG3A1SaS5RcA1M4A1A3S0S4SbG4A1SbS5RdA1M5A1A3S0S4S7G5A1S7S5ReA1A1A3S0G1S8ReA1S8RfA1A3S12S2aRfR11A2S2aR10R11A2A2S2bS27R14R12R11A4S2bS27R14R13R11A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd';Fmd;Ftp;FA';FA;").
Proof.
  intros A A' tp md md' EG ES ED EP EV EKm EKf EPC E1 E2 E3 E4 E5 E6 HP HM.
  unfold model_inv, vm_geom, ledger_inv, in_maps, gap_ok, gapN_ok, gapS_ok, blocks_left, ledger, budget_boundD in HM |- *. cbn zeta in HM |- *.
  rewrite EG, ES, ED, EP, EV, EKm, EKf, EPC, E1, E2, E3, E4, E5, E6.
  destruct HM as ((V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9) & PB & LIM & V0 & K0 & F0 & TOPm & (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10)).
  split; [exact (conj V1 (conj V2 (conj V3 (conj V4 (conj V5 (conj V6 (conj V7 (conj V8 V9))))))))|].
  split; [clear -PB HP; lia|]. split; [exact LIM|]. split; [exact V0|]. split; [exact K0|]. split; [exact F0|]. split; [exact TOPm|].
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
  split; [exact (depot_vm_fields _ md md' tp E1 E3 E5 E6 L5)|].
  exact (conj L6 (conj L7 (conj L8 (conj L9 L10)))).
Qed.

Section RN.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Lemma zone_FN : ltac2:(tb__ "0|4|
S19S16S4S4S3S37R4R3S31R2A1R1A4S2S1S12S13S34R4R3A2M0Z10A2M1R1A2S14R1S13G1S15Z4M2R2A2A2A2A2S2S1S12G0R1A2S14R1S13G0G2A2A2A2S1S12S38S23S1aR4A1A1S32S29Q40S18R3PcA2A2A1A2M3R1A2S14R1S13G3Z80A2A2A2A2A2A2Fz;Fk;Frb;FA;").
Proof.
  intros A rb k z. unfold zoneR, phFN, ph_setri, ph_setcnt, phK, ph0, revealedp, releasedp. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb]. split.
  - intros [[X _]|[[X _]|[[X _]|[[X _]|[[_ X]|[X|[[_ X]|[_ X]]]]]]]]; try discriminate X; try (exfalso; lia).
    + left; exact X.
    + right; left; exact X.
    + right; right; exact X.
  - intros [X|[X|X]].
    + right; right; right; right; right; left; exact X.
    + right; right; right; right; right; right; left; split; [reflexivity | exact X].
    + right; right; right; right; right; right; right; split; [reflexivity | exact X].
Qed.

Theorem refill_rebuild_N : ltac2:(tb__ "0|3|
S19S39S16SeS28Q40M0A1A1M1S6SeS3bA1S3cS16S35R8R6R5R4R3R2R1A7S0S10S22R9A1S11A3S29G0S18R8PcA2A2S4S32R1A1S4S12S2eR1A1S36RcRaA2A2S16G1SeSdA1S6S33R11R10RfReRdS31S2eR6A1A1R4R3R2R1AaS1S2cS27S2fR12R7A2M2R5R4R2A5S3aVCST;VXGL;R12G2S17R10A1S17R5A1A6A2F_;Fmd;Ftr;Ftp;Fr;F_;Tc;Tnv;F_;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FKc;FA;").
Proof.
  intros A Kc rb tp0 md0 W st rho HE Hini nv c HNP r tp tr md (HFz & HGh & HK & HM & HR & HRM).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((Hnv & C1 & S1 & S16) & (K1 & K2 & K3) & (MU0 & AU0 & MU1 & AU1 & TI0) & (MF0 & MF1) & (MC0 & FC0 & Hcs0) & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof HE as (_ & HA & _).
  set (cs := cst_of A nv) in *. set (k := kchunks c) in *. unfold gh_nf in HNP. fold nv c cs in HNP.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *. set (T := ag_thread G) in *.
  assert (Hk : (Z.to_nat k <= length (cs_free_array cs))%nat) by (clear -HNP K1; lia).

  pose proof (N_refill_cs A rb HNP) as ECS. fold nv c cs k in ECS.
  pose proof HA as (HG & _ & _ & HRest & HM0 & _ & HB0). destruct HRest as (_ & _ & Hprim & _ & Hq & _). destruct Hprim as (_ & _ & _ & PC).
  pose proof (entry_cls_pure _ A c C1 HG (PC c C1) Hq) as HP0. change (nthZ (aa_cls A) c cs_empty) with cs in HP0.
  destruct (take_pure c cs _ (Z.to_nat k) HP0 Hcs0 Hk) as (HP1 & EFC & LC & LF & EMU & EAU & EMF). cbn zeta in HP1, EFC, LC, LF, EMU, EAU, EMF.

  unfold mlink in HM. cbn zeta in HM. unfold phFN, ph_setri, ph_setcnt, phK, ph0, committed, revealedp, subU, subF in HM. cbn [ph_u ph_f Nat.leb] in HM.
  destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & _ & M10).
  assert (Etp1 : tp1 = []).
  { destruct tp1 as [|p tp1']; [reflexivity|]. exfalso. destruct (M8 p (or_introl eq_refl)) as [_ [[X _]|[X _]]]; discriminate X. }
  subst tp1. cbn [app length Z.of_nat] in M7, M10. subst tp.

  unfold rlink in HR. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6).
  assert (ZI := zone_FN A rb k). fold nv c in ZI. fold G in ZI. fold SB in ZI.
  assert (PCr : PCE A rb = T + 208 + 80 * c) by (unfold PCE; fold nv c; fold G T; clear; lia).
  set (ri := region_info SB c) in *.
  assert (RIr : SB + 137438953472 + 128 <= ri /\ ri + 128 <= SB + 137438953472 + 4096).
  { unfold ri, region_info, kRegionInfoStride. rewrite kSpaceSize_val. clear -C1. lia. }
  assert (FAr : FAb A rb = SB + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. fold G SB. clear; lia. }
  set (m0 := view segs (rm rb)) in *. set (m := view segs (rm r)) in *.
  apply (refill_rebuild CST XGL HCST HXGL A rb r tp0 tp0 md0 md nv (zoneR A rb (phFN k)) HA Hnv Hini).
  -   fold c cs. rewrite ECS. exact HP1.
  - fold c cs. rewrite ECS. rewrite EAU. clear; lia.
  - fold c cs. rewrite ECS. rewrite EMU. clear; lia.
  - fold c cs. rewrite ECS. rewrite EMF. clear; lia.
  - fold c cs. rewrite ECS. rewrite LC. clear -K1 K2. fold k in K1, K2. lia.
  - intros z.
    assert (D : (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)
                \/ ~ (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)) by (clear; lia).
    destruct D as [D|D]; [left; apply ZI; exact D | right; intros HZ; apply D; apply ZI; exact HZ].
  -
    intros z HZ. apply ZI in HZ. fold c cs. fold G. fold T SB. unfold envR.
    destruct HZ as [X|[X|X]].
    + right; right; left. rewrite PCr in X. clear -X K1. fold k in K1. lia.
    + right; left. rewrite PCr in X. clear -X. lia.
    + left. unfold ri, region_info, kRegionInfoStride in X. rewrite kSpaceSize_val in X. clear -X. lia.
  - intros z Hz. exact (L1 z Hz).
  - intros z Hz. pose proof (L2 z Hz) as D. change (exists b, m z = Some b). destruct (m z) as [b|]; [exists b; reflexivity | contradiction].
  - exact HRM.
  - exact (proj1 (L6 eq_refl)).
  - exact (proj1 (proj2 (L6 eq_refl))).
  - exact (proj1 (proj2 (proj2 (L6 eq_refl)))).
  - exact (proj1 (proj2 (proj2 (proj2 (L6 eq_refl))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl))))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))))).
  - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))))).
  -
    fold c cs G. fold SB. rewrite ECS. unfold take_cs. cbn [cs_free_array].
    intros i x Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as Li. rewrite firstn_length_le in Li by (clear -Hk; lia).
    rewrite nth_error_firstn in Hi. replace (i <? length (cs_free_array cs) - Z.to_nat k)%nat with true in Hi by (symmetry; apply Nat.ltb_lt; exact Li).
    pose proof (proj1 (entry_fa _ _ _ _ _ _ _ HE) (Z.of_nat i)) as CE. cbn zeta in CE. fold nv c cs in CE. fold m0 in CE.
    specialize (CE ltac:(clear -Li; lia)). rewrite Nat2Z.id in CE. rewrite (nth_error_nth _ _ 0 Hi) in CE.
    replace (free_array SB c) with (FAb A rb) by (unfold FAb; fold nv c; reflexivity).
    eapply cell_ok_agree_range; [|exact CE]. cbn [c_addr c_w]. intros z Hz. apply L1. intros HZ. apply ZI in HZ.
    change (Z.of_nat 4) with 4 in Hz. rewrite FAr in Hz. rewrite PCr in HZ.
    assert (Li' : Z.of_nat i < 2 ^ 27) by (clear -Li MF1; lia).
    clear -Hz HZ Li' C1 K1 G13 G14 T1 PS1 RIr. fold k in K1. lia.
  -
    fold c cs. rewrite ECS. rewrite LC. rewrite Z2Nat.id by (clear -K1; fold k in K1; lia).
    replace (T + 208 + 80 * c) with (PCE A rb) by (rewrite PCr; reflexivity). exact (L5 eq_refl).
  -
    fold c cs. intros i x Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as Li. rewrite ECS in Li. rewrite LC in Li.
    pose proof (L4 (Z.of_nat i)) as CE. cbn [ph_pop phFN ph_setri ph_setcnt phK] in CE. specialize (CE ltac:(clear -Li K1; fold k in K1; lia)).
    rewrite Nat2Z.id in CE. fold nv c cs in CE. rewrite (nth_error_nth _ _ 0 Hi) in CE.
    replace (T + 208 + 80 * c + 16 + 4 * Z.of_nat i) with (PCE A rb + 16 + 4 * Z.of_nat i) by (rewrite PCr; reflexivity). exact CE.
  - fold c cs. rewrite ECS, EMU. intros z Hz. exfalso. clear -Hz. lia.
  - fold c cs. rewrite ECS, EMU. intros z Hz. exfalso. clear -Hz. lia.
  - fold c cs. rewrite ECS, EMF. intros z Hz. exfalso. clear -Hz. lia.
  -
    apply (model_inv_fields A (refillA A c) tp0 md0 md); try reflexivity; try assumption.
    + apply prim_credit_maps. intros c' Hc'. unfold refillA. cbn [aa_cls].
      destruct (Z.eq_dec c' c) as [->|Hne].
      * rewrite nth_list_upd_same by (destruct HA as (_ & _ & _ & HRest' & _); destruct HRest' as (_ & _ & (PL & _) & _); rewrite PL; clear -C1; lia).
        change (nth (Z.to_nat c) (aa_cls A) cs_empty) with cs. rewrite ECS. split; [exact EMU | exact EMF].
      * rewrite nth_list_upd_other by (clear -Hne Hc' C1; lia). split; reflexivity.
    + clear -M10. lia.
  -
    eapply bandtp_mono; [|exact HB0]. intros z _ Hd. fold m0 in Hd. fold m.
    assert (D : (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)
                \/ ~ (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)) by (clear; lia).
    destruct D as [D|D]; [apply L2; apply ZI; exact D | rewrite L1 by (intros HZ; apply D; apply ZI; exact HZ); exact Hd].
Qed.
End RN.
End CRebuildRN.

(* [comment removed for export] *)
Module RebuildRQ.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "false"; "length"; "nat"; "@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ju.RebuildRQ"; "phQ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "gh_new"; "phase"; "JR"; "entryR"; "mkPh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocR15"; "phFin"; "phU3"; "phUF3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "mem_keptA"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocR7"; "popfacts"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM RefillModel RefillModelP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineMallocR12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocR13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocR14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocR15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.RebuildR.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Definition phQ (b : bool) (new k : Z) : phase := ltac2:(tb__ "0|1|
S14U3M0S1S6Lb;Vb;G0U0X1x2Vnew;Vk;S2S2A6").
Lemma phQ_P : ltac2:(tb__ "0|0|
S0S0S7S11S15S16R2R1A3SdS4R2R1A3A3Fk;Fnew;"). Proof. reflexivity. Qed.
Lemma phQ_M : ltac2:(tb__ "0|0|
S0S0S7S11S15S17R2R1A3SdS2R2R1A3A3Fk;Fnew;"). Proof. reflexivity. Qed.

Section RQ.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Theorem refill_rebuild_Q : ltac2:(tb__ "0|3|
S1eS19SaS3S2cQ40M0A1A1M1SeS3S1bA1S1cSaS13R8R6R5R4R3R2R1A7S27R9R7A2S1S7S1S1fRbA1S2A3S2dG0ScRaPcA2A2S0S25R1A1S0S26ReR2A2S20S9S7S1R5S2A3S29S22R1A1S2aZ4S28S2bS5S0S21R1A1A2A1S10RfRdA2A2A2A2A2SaG1S3SfA1SeS12R14R13R12R11R10SdRaS10R14R12A2S23R7A1A3R4R3R2R1AaS8S1dS18S24R15R8A2M2R5R4R2A5S1aVCST;VXGL;R15G2SbR13A1SbR5A1A6A2F_;Fmd;Ftr;Ftp;Fr;F_;Tcs;Tc;Tnv;F_;Fb;FPF;FHE;Frho;Fst;FW;Fmd0;Ftp0;Frb;FKc;FA;").
Proof.
  intros A Kc rb tp0 md0 W st rho HE PF b Hini nv c cs HB r tp tr md (HFz & HGh & HK & HM & HR & HRM).
  destruct (pop_geo A rb tp0 md0 W st rho HE PF) as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & T1 & PS1 & TB).
  fold nv c cs in C1, S1, AU0, MU1, N4, K1, KN, NF0, MF1, MF2, MF0, FAr.
  destruct (entry_pure A rb tp0 md0 W st rho HE PF) as (HP & Hc0 & NP & RM). fold nv c cs in HP, Hc0, NP, RM.
  pose proof (P_csR A rb tp0 md0 W st rho HE PF) as (X1 & X2 & X3 & X5 & X6 & X7 & LP' & HIDS). cbn zeta in X1, X2, X3, X5, X6, X7, LP', HIDS. fold nv c cs in X1, X2, X3, X5, X6, X7, LP', HIDS.
  pose proof (P_fields c cs _ C1 HP NP RM) as PFL. cbn zeta in PFL. destruct PFL as (_ & _ & _ & XFA & _). pose proof (P_newZ A rb) as ENZ. fold nv c cs in ENZ. pose proof (P_faP_len c cs _ C1 HP RM) as LPz. rewrite ENZ in LPz. rewrite LPz in XFA.
  destruct (refill_pure c cs _ C1 HP Hc0 ltac:(intros _; exact RM)) as (HPR & _). cbn zeta in HPR.
  pose proof (pop_credit_eq A rb tp0 md0 W st rho HE PF) as CEQ. fold nv c cs in CEQ.
  set (k := kchunks c) in *. set (new := gh_new A rb) in *. set (nf := Z.of_nat (length (cs_free_array cs))) in *.
  set (mu := cs_mapped_user cs) in *. set (mfa := cs_mapped_free_array cs) in *. set (au := cs_allocated_user cs) in *. set (fP := faP c cs) in *.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *. set (T := ag_thread G) in *.
  assert (Eb : (mfa <? 4 * (nf + new)) = b).
  { destruct b; [apply Z.ltb_lt; apply (proj1 HB); reflexivity | apply Z.ltb_ge; destruct (Z_lt_dec mfa (4 * (nf + new))) as [X|X]; [discriminate (proj2 HB X) | clear -X; lia]]. }
  rewrite Eb in X7, CEQ.
  pose proof HE as (_ & HA & _ & _ & _ & Hnv & _ & _ & HWF). fold nv in Hnv.
  pose proof HA as (HG & _ & _ & HRest0 & HMI0 & HI3 & HB0). destruct HRest0 as (_ & _ & (PL & _) & _).

  assert (EU0 : U0 A rb = SB + c * 4294967296 + mu) by (unfold U0, region_beg, kRegionSize; fold nv c cs; fold G SB mu; clear; lia).
  assert (EF0 : F0 A rb = SB + c * 4294967296 + 3758096384 + mfa) by (unfold F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; fold nv c cs; fold G SB mfa; clear; lia).
  assert (PCr : PCE A rb = T + 208 + 80 * c) by (unfold PCE; fold nv c; fold G T; clear; lia).
  assert (G12 : SB mod 65536 = 0).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. destruct CF as (_ & _ & _ & _ & _ & (X & _) & _). exact X. }
  assert (MU18 : mu mod 262144 = 0).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF. destruct CF as (_ & _ & (X & _) & _). exact X. }
  assert (UM : U0 A rb mod 65536 = 0).
  { rewrite EU0. destruct (proj1 (Z.mod_divide mu 262144 ltac:(clear; lia)) MU18) as [q Hq]. destruct (proj1 (Z.mod_divide SB 65536 ltac:(clear; lia)) G12) as [q2 Hq2].
    rewrite Hq, Hq2. replace (q2 * 65536 + c * 4294967296 + q * 262144) with ((q2 + c * 65536 + q * 4) * 65536) by (clear; lia). apply Z_mod_mult. }
  assert (FM : F0 A rb mod 65536 = 0).
  { rewrite EF0. destruct (proj1 (Z.mod_divide mfa 262144 ltac:(clear; lia)) MF0) as [q Hq]. destruct (proj1 (Z.mod_divide SB 65536 ltac:(clear; lia)) G12) as [q2 Hq2].
    rewrite Hq, Hq2. replace (q2 * 65536 + c * 4294967296 + 3758096384 + q * 262144) with ((q2 + c * 65536 + 57344 + q * 4) * 65536) by (clear; lia). apply Z_mod_mult. }
  destruct (sh_run_nums SB (U0 A rb) ltac:(clear -G13; lia) ltac:(rewrite EU0; clear -C1 AU0; lia) ltac:(rewrite EU0; clear -C1 MU1; lia) G14 UM) as (QU1 & QU2 & QU3 & QU4).
  destruct (sh_run_nums SB (F0 A rb) ltac:(clear -G13; lia) ltac:(rewrite EF0; clear -C1 NF0 MF1; lia) ltac:(rewrite EF0; clear -C1 MF2; lia) G14 FM) as (QF1 & QF2 & QF3 & QF4).
  set (ri := region_info SB c) in *.
  assert (RIr : SB + 137438953472 + 128 <= ri /\ ri + 128 <= SB + 137438953472 + 4096).
  { unfold ri, region_info, kRegionInfoStride. rewrite kSpaceSize_val. clear -C1. lia. }

  set (ZQ := fun z : Z => (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768) \/ (U0 A rb <= z < U0 A rb + 262144)
                          \/ (b = true /\ Sh (F0 A rb) <= z < Sh (F0 A rb) + 32768) \/ (b = true /\ F0 A rb <= z < F0 A rb + 262144)
                          \/ (FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new))
                          \/ (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k) \/ (PCE A rb <= z < PCE A rb + 4) \/ (ri <= z < ri + 128)).
  assert (ZI : forall z, zoneR A rb (phQ b new k) z <-> ZQ z).
  { intros z. unfold zoneR, phQ, ZQ, revealedp, releasedp, kUserMapSize, kFreeArrayMapSize. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb].
    unfold gh_nf. fold nv c cs nf new. fold G SB ri. replace (nf + new - new) with nf by (clear; lia).
    destruct b; cbn [Nat.leb]; split.
    - intros [[_ H]|[[_ H]|[[_ H]|[[_ H]|[[H _]|[H|[[_ H]|[_ H]]]]]]]].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; split; [reflexivity | exact H].
      + right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; right; exact H.
    - intros [H|[H|[[_ H]|[[_ H]|[H|[H|[H|H]]]]]]].
      + left; split; [reflexivity | exact H].
      + right; left; split; [reflexivity | exact H].
      + right; right; left; split; [reflexivity | exact H].
      + right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; left; split; [exact H | clear -N4; lia].
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; right; right; right; split; [reflexivity | exact H].
    - intros [[_ H]|[[_ H]|[[X _]|[[X _]|[[H _]|[H|[[_ H]|[_ H]]]]]]]]; try discriminate X.
      + left; exact H.
      + right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; right; exact H.
    - intros [H|[H|[[X _]|[[X _]|[H|[H|[H|H]]]]]]]; try discriminate X.
      + left; split; [reflexivity | exact H].
      + right; left; split; [reflexivity | exact H].
      + right; right; right; right; left; split; [exact H | clear -N4; lia].
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; right; right; right; split; [reflexivity | exact H]. }
  assert (ZD : forall z, zoneR A rb (phQ b new k) z \/ ~ zoneR A rb (phQ b new k) z).
  { intros z. assert (D : ZQ z \/ ~ ZQ z).
    { unfold ZQ. destruct b.
      - assert (D' : (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144 \/ Sh (F0 A rb) <= z < Sh (F0 A rb) + 32768 \/ F0 A rb <= z < F0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)
                       \/ ~ (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144 \/ Sh (F0 A rb) <= z < Sh (F0 A rb) + 32768 \/ F0 A rb <= z < F0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)) by (clear; lia).
        destruct D' as [D'|D']; [left | right]; [clear -D'; tauto | intros X; apply D'; clear -X; tauto].
      - assert (D' : (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)
                       \/ ~ (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)) by (clear; lia).
        destruct D' as [D'|D']; [left; clear -D'; tauto|]. right. intros X. apply D'. clear -X. destruct X as [X|[X|[[E _]|[[E _]|X]]]]; try discriminate E; tauto. }
    destruct D as [D|D]; [left; apply ZI; exact D | right; intros X; apply D; apply ZI; exact X]. }
  unfold rlink in HR. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6).
  set (m0 := view segs (rm rb)) in *. set (m := view segs (rm r)) in *.

  unfold mlink in HM. cbn zeta in HM. unfold phQ in HM. cbn [ph_u ph_f] in HM.
  destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
  assert (ECF : committed (if b then 3%nat else 0%nat) = b) by (destruct b; reflexivity).
  assert (ERF : revealedp (if b then 3%nat else 0%nat) = b) by (destruct b; reflexivity).
  rewrite ECF in M5, M6, M10. rewrite ERF in M8, M9, M10. change (committed 3) with true in M5, M6, M10. change (revealedp 3) with true in M8, M9, M10.
  apply (refill_rebuild CST XGL HCST HXGL A rb r tp0 tp md0 md nv (zoneR A rb (phQ b new k)) HA Hnv Hini); fold c cs; fold G; fold SB T; fold nf mu.
  - exact HPR.
  - rewrite X5. fold au. clear -N4 S1. nia.
  - rewrite X6. clear; lia.
  - rewrite X7. fold mfa. destruct b; clear; lia.
  - rewrite X2. destruct (kchunks_facts c C1) as (_ & K2 & _). fold k in K2. clear -K1 K2. lia.
  - exact ZD.
  -
    intros z HZ. apply ZI in HZ. unfold envR. unfold ZQ in HZ. rewrite EU0, EF0, FAr, PCr in HZ. rewrite EU0 in QU3, QU4. rewrite EF0 in QF3, QF4.
    pose proof (Geometry.Sh_mono (SB + c * 4294967296 + mu) (SB + c * 4294967296 + 3758096384 + mfa) ltac:(clear -MU1 NF0 MF1; lia)) as SM1.
    pose proof (Geometry.Sh_mono (SB + c * 4294967296 + mu + 262144) (SB + c * 2 ^ 32 + 2 ^ 32) ltac:(clear -MU1; lia)) as SM2.
    pose proof (Geometry.Sh_mono (SB + c * 4294967296 + 3758096384 + mfa + 262144) (SB + c * 2 ^ 32 + 2 ^ 32) ltac:(clear -MF2; lia)) as SM3.
    replace (SB + c * 2 ^ 32 + mu) with (SB + c * 4294967296 + mu) by (clear; lia).
    destruct HZ as [X|[X|[[_ X]|[[_ X]|[X|[X|[X|X]]]]]]].
    + right; right; right; right; right. clear -X QU4 SM2. lia.
    + right; right; right; right; left. clear -X MU1. lia.
    + right; right; right; right; right. clear -X QF4 SM1 SM3. lia.
    + right; right; right; left. clear -X MF1 MF2. lia.
    + right; right; right; left. clear -X N4 MF1 MF2. lia.
    + right; right; left. clear -X K1. lia.
    + right; left. clear -X. lia.
    + left. unfold ri, region_info, kRegionInfoStride in X. rewrite kSpaceSize_val in X. clear -X. lia.
  - intros z Hz. exact (L1 z Hz).
  - intros z Hz. pose proof (L2 z Hz) as D. change (exists b0, m z = Some b0). destruct (m z) as [b0|]; [exists b0; reflexivity | contradiction].
  - exact HRM.
  - exact (proj1 (L6 eq_refl)).
  - exact (proj1 (proj2 (L6 eq_refl))).
  - exact (proj1 (proj2 (proj2 (L6 eq_refl)))).
  - exact (proj1 (proj2 (proj2 (proj2 (L6 eq_refl))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl))))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))))).
  - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))))).
  -
    rewrite XFA. intros i x Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as Li. rewrite firstn_length_le in Li by (clear -LP' KN NF0 K1; lia).
    rewrite nth_error_firstn in Hi. replace (i <? Z.to_nat (nf + new - k))%nat with true in Hi by (symmetry; apply Nat.ltb_lt; exact Li).
    pose proof (P_HSRC A rb tp0 md0 W st rho HE PF (phQ b new k) m eq_refl ltac:(cbn [ph_pop phQ]; clear -K1; lia) (conj L1 (conj L2 (conj L3 (conj L4 (conj L5 L6))))) (Z.of_nat i)
                  ltac:(fold nv c cs fP; rewrite LP'; clear -Li KN NF0 K1; lia)) as CE.
    fold nv c cs fP in CE. rewrite Nat2Z.id in CE. rewrite (nth_error_nth _ _ 0 Hi) in CE.
    replace (free_array SB c) with (FAb A rb) by (unfold FAb; fold nv c; reflexivity). exact CE.
  - rewrite X2. replace (T + 208 + 80 * c) with (PCE A rb) by (rewrite PCr; reflexivity). exact (L5 eq_refl).
  - intros i x Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as Li. rewrite <- (Nat2Z.id (length (cs_cache (refill_cs c cs)))) in Li. rewrite X2 in Li.
    pose proof (L4 (Z.of_nat i)) as CE. cbn [ph_pop phQ] in CE. specialize (CE ltac:(clear -Li K1; lia)).
    rewrite Nat2Z.id in CE. fold nv c cs in CE. rewrite (nth_error_nth _ _ 0 Hi) in CE.
    replace (T + 208 + 80 * c + 16 + 4 * Z.of_nat i) with (PCE A rb + 16 + 4 * Z.of_nat i) by (rewrite PCr; reflexivity). exact CE.
  - rewrite X6. intros z Hz. apply ZI. right; left. rewrite EU0. unfold region_beg, kRegionSize in Hz. clear -Hz. lia.
  - rewrite X6. intros z Hz. apply ZI. left. rewrite EU0 in QU4 |- *. unfold region_beg, kRegionSize in Hz.
    replace (SB + c * 2 ^ 32 + mu) with (SB + c * 4294967296 + mu) in Hz by (clear; lia).
    replace (SB + c * 2 ^ 32 + (mu + 262144)) with (SB + c * 4294967296 + mu + 262144) in Hz by (clear; lia). clear -Hz QU4. lia.
  - rewrite X7. fold mfa. intros z Hz. destruct b; [|exfalso; clear -Hz; lia]. apply ZI. right; right; right; left. split; [reflexivity|].
    rewrite EF0. unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. clear -Hz. lia.
  -
    change (subF A rb b (subU A rb true (vm_noaccess (m_vmmaps md0))))
      with (sub2 true (U0 A rb) (U0 A rb + kUserMapSize) b (F0 A rb) (F0 A rb + kFreeArrayMapSize) (vm_noaccess (m_vmmaps md0))) in M5.
    change (subF A rb b (subU A rb true (m_vm_lazy md0)))
      with (sub2 true (U0 A rb) (U0 A rb + kUserMapSize) b (F0 A rb) (F0 A rb + kFreeArrayMapSize) (m_vm_lazy md0)) in M6.
    rewrite M7.
    apply (model_inv_sub2 A (refillA A c) tp0 tp1 md0 md true b (U0 A rb) (U0 A rb + kUserMapSize) (F0 A rb) (F0 A rb + kFreeArrayMapSize)); try reflexivity; try assumption.
    + unfold kUserMapSize. clear; lia.
    + unfold kFreeArrayMapSize. clear; lia.
    + fold G SB. rewrite EU0. clear -C1 AU0. lia.
    + fold G SB. rewrite EU0, kSpaceSize_val. unfold kUserMapSize. clear -C1 MU1. lia.
    + fold G SB. rewrite EF0. clear -C1 NF0 MF1. lia.
    + fold G SB. rewrite EF0, kSpaceSize_val. unfold kFreeArrayMapSize. clear -C1 MF2. lia.
    + fold G SB. unfold HIGH_SHADOW_END. clear -G13. lia.
    + intros p Hp. destruct (M8 p Hp) as [_ [[_ (j & Hj & Ej)]|[_ (j & Hj & Ej)]]]; rewrite Ej; unfold band_page; right; unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG.
      * clear -Hj QU2 QU3. lia.
      * clear -Hj QF2 QF3. lia.
    +
      destruct HMI0 as (_ & PB0 & _). rewrite <- M7. unfold kUserMapSize, kFreeArrayMapSize in M10.
      destruct b; clear -PB0 M10 CEQ; lia.
  -
    rewrite M7. apply (bandtp_grow m tp0).
    + eapply bandtp_mono; [|exact HB0]. intros z _ Hd. fold m0 in Hd. destruct (ZD z) as [ZIz|ZOz]; [exact (L2 z ZIz) | rewrite (L1 z ZOz); exact Hd].
    + intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [|left; exact Hp]. right. intros _ z Hz.
      assert (ZIz : zoneR A rb (phQ b new k) z).
      { apply ZI. destruct (M8 p Hp) as [_ [[_ (j & Hj & Ej)]|[Eb' (j & Hj & Ej)]]]; rewrite Ej in Hz; unfold PG in Hz.
        - left. clear -Hz Hj. lia.
        - right; right; left. split; [exact Eb' | clear -Hz Hj; lia]. }
      pose proof (L2 z ZIz) as D. destruct (m z) as [b0|]; [exists b0; reflexivity | contradiction].
Qed.
End RQ.
End RebuildRQ.

