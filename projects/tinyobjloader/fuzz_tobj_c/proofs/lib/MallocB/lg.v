(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ju l9 ka.
From Stdlib Require Permutation FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kw.

(* [comment removed for export] *)
Module SpineMallocRp0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "entailsA"; "ax_X"; "axst"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "SLit"; "ss_facts"; "swf"; "ss_lenient"; "ss_objs"; "SAlu"; "SVar"; "reg_sv"; "SPNot"; "valuation"; "sprop_below"; "SPBranch"; "SPUle"; "rm"; "ss_pc"; "sv_below"; "rw"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "factsR"; "cX"; "GR"; "beg1"; "beg2"; "cE1"; "cE2"; "keepn"; "cP2"; "cXL"; "O_pcm"; "PV4"; "LV0"; "O_ri"; "cL1"; "cT1"; "cD"; "cPa"; "cPb"; "LV2"; "PV6"; "cE3"; "nobj"; "rMS"; "sMS"; "LV3"; "cE3b"; "vMU"; "cFm"; "vK"; "F_x"; "HINT_au"; "HINT_k"; "HINT_map"; "LNX"; "O_pccK"; "PNX"; "cE3a"; "idx_rot"; "k_e"; "relM"; "ri_has"; "rotM"; "vAU"; "vMFA"; "F_new"; "vNEW"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocRi0"; "e3r"; "FUEL"; "icc"; "W0"; "r_2_0"; "nob"; "e3p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lg.SpineMallocRp0"; "r_xF_0"; "r_xU_0"; "cmcF"; "cmcU"; "r_9M_0"; "r_9P_0"; "cl0M"; "cl0P"; "cp2c"; "ct0M"; "ct0P"; "nobFM"; "nobFP"; "r_lM_1"; "r_lP_1"; "r_p1_0"; "r_p1_1"; "r_d_0"; "r_f_0"; "cfm"; "r_f_1"; "r_h_0"; "r_mF_0"; "r_mU_0"; "rf1"; "ru1"; "dmF"; "dmU"; "r_jM_0"; "r_jP_0"; "r_p2a_0"; "r_p2a_1"; "r_p2b_0"; "r_p2b_1"; "s_fbkM"; "s_fbkP"; "s_finM"; "s_finP"; "r_lM_0"; "r_lP_0"; "r_t1M_0"; "r_t1P_0"; "s_bkM"; "s_bkP"; "s_inM"; "s_inP"; "xlM"; "xlP"; "r_t1M_1"; "r_t1P_1"; "cellsfM"; "cellsfP"; "r_flM_0"; "r_flP_0"; "r_t0M_0"; "r_t0P_0"; "r_zM_0"; "r_zP_0"; "sa0"; "sa1"; "sb0"; "sb1"; "s_xM"; "s_xP"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "instr"; "ALU_SLL"; "ALU_XOR"; "Ecall"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_pcc0"; "O_st"; "V_SIZE"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "commit_post"; "memset_post"; "TRok"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "phase"; "JR"; "entryR"; "gh_new"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocR10";
"cMr"; "a2_e"; "cMc"; "dMSf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocR13"; "F_lt"; "O_fcell"; "faend_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocR7"; "F_mu0"; "F_hi"; "x19_e0"; "x19_e1"; "popfacts"; "size_e_hi"; "size_e_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9"; "O_piece"; "O_shp"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "call_checkA"; "entails_frA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR11"; "a0_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineMallocR12"; "F_geu"; "new_e"; "rup_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocR14"; "e16P"; "e32P"; "e48P"; "e_srcP"; "e24M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocR15"; "fillT"; "phUF3"; "pieceT"; "fmT"; "headT"; "midT"; "phFin"; "phU3"; "runT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4"; "O_rif"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP"; "PF"; "PU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineMallocR12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocR13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocR14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocR15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocRi0.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_p1__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41754SbS2cZ41794SeS2cA1A3A3S5S62A1ScA5").
Local Strategy expand [R_p1__R].
Definition r_p1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_p1__R).
Definition r_p1_0 := Eval vm_compute in (nth 0 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition r_p1_1 := Eval vm_compute in (nth 1 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition R_p2a__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ417c4SeS2cA1A3S3fS2eS5eA1S5S80A1A2ScA5").
Local Strategy expand [R_p2a__R].
Definition r_p2a := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_p2a__R).
Definition r_p2a_0 := Eval vm_compute in (nth 0 r_p2a (mkLeafA (cPa (factsR e3r) (la_state r_p1_0)) RsCut)).
Definition r_p2a_1 := Eval vm_compute in (nth 1 r_p2a (mkLeafA (cPa (factsR e3r) (la_state r_p1_0)) RsCut)).
Definition R_p2b__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ417c4SeS2cA1A3S40S2eS5eA1S5S81A1A2ScA5").
Local Strategy expand [R_p2b__R].
Definition r_p2b := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_p2b__R).
Definition r_p2b_0 := Eval vm_compute in (nth 0 r_p2b (mkLeafA (cPb (factsR e3r) (la_state r_p1_1)) RsCut)).
Definition r_p2b_1 := Eval vm_compute in (nth 1 r_p2b (mkLeafA (cPb (factsR e3r) (la_state r_p1_1)) RsCut)).
Definition cp2c := Eval vm_compute in (cP2c (factsR e3r) (la_state r_p2a_1)).
Lemma FP_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S26Sb7S5dS4bA3SeS19A1A3S1cS4S5S62A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p1 : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41754SbS2cZ41794SeS2cA1A3A3S5S62A1ScA5S11G0SbS6S80SbS6S81SeS6A1A3A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ417c4SeS2cA1A3S3fS2eS5eA1S5S80A1A2ScA5S11G0SbS6S8fSbS6S90SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p2a__R <: R_p2a__R = Some [r_p2a_0; r_p2a_1]). Qed.
Lemma LN_p2a : ltac2:(tb__ "0|0|
S0SdS1eS4S3fS2eS5eA1S5S80A1A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p2a : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S3fS2eS5eA1S5S80A1A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p2b : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ417c4SeS2cA1A3S40S2eS5eA1S5S81A1A2ScA5S11G0SbS6S91SbS6S92SeS6A1A3A3A2A3").
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
  exact (populate_head A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE FUEL e3r (la_state r_2_0) r_p1_0 r_p1_1 r_p2a_0 r_p2a_1 r_p2b_0 r_p2b_1 cp2c sa0 sa1 sb0 sb1
           (In_of_inclb _ _ FP_inb) R_p1 LN_p1 NX_p1 (In_of_inclb _ _ Fa_inb) (In_of_inclb _ _ Fb_inb) W_pa D_pa NXe_pa W_pb D_pb NXe_pb R_p2a LN_p2a NX_p2a R_p2b LN_p2b NX_p2b
           (In_of_inclb _ _ Fa0_inb) (In_of_inclb _ _ Fa1_inb) (In_of_inclb _ _ Fb0_inb) (In_of_inclb _ _ Fb1_inb) W_a0 W_a1 W_b0 W_b1 D_a0 D_a1 D_b0 D_b1 NXe_a0 NXe_a1 NXe_b0 NXe_b1
           ENT_a0 ENT_a1 ENT_b0 ENT_b1 SID_a0 SID_a1 SID_b0 SID_b1 r tp Q HC).
Qed.
Definition R_xU__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ706a0SeS2cA1A3S79ScA5").
Local Strategy expand [R_xU__R].
Definition r_xU := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_xU__R).
Definition r_xU_0 := Eval vm_compute in (nth 0 r_xU (mkLeafA cp2c RsCut)).
Definition R_mU__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZdb004SeS2cA1A3SbfS2fS5S72A1S31A2S31Z40000A3ScA5").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ706a0SeS2cA1A3S79ScA5S11G0SbS6S72SeS6A1A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZdb004SeS2cA1A3SbfS2fS5S72A1S31A2S31Z40000A3ScA5S11G0SbS6S88SeS6A1A3A2A3").
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
SfaS61S6dS105S31S79S8aA6").
Proof.
  rewrite <- RU1_eq, <- DMU_eq, <- CMCU_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PU beg1 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cp2c r_xU_0 r_mU_0
           R_xU LN_xU NX_xU W_xU D_xU SK_xU (inclb_incl _ _ XF_xUb) XX_xU NXc_xU IC_xU R17_xU R10_xU BEL_xU R11_xU R12_xU R13_xU R14_xU R15_xU
           R_mU LN_mU NX_mU SK_mU (inclb_incl _ _ XF_mUb) XX_mU W_mrU D_mrU _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCU_eq, ?DMU_eq; [exact W_mcU | exact E_msU | exact CHK_msU | exact NF_msU | exact NX_msU | exact FBC_msU | exact FBT_msU | exact ND_rU | apply Nat.leb_le; exact NO_rUb | exact OB_rU].
Qed.
Definition R_d__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41884SeS2cA1A3S8aScA5").
Local Strategy expand [R_d__R].
Definition r_d := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_d__R).
Definition r_d_0 := Eval vm_compute in (nth 0 r_d (mkLeafA ru1 RsCut)).
Definition R_f__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ3f404SbS2cZ418c0SeS2cA1A3A3S3eS2eS5eA1S5S82A1A2ScA5").
Local Strategy expand [R_f__R].
Definition r_f := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_f__R).
Definition r_f_0 := Eval vm_compute in (nth 0 r_f (mkLeafA (cD (factsR e3r) (la_state r_d_0)) RsCut)).
Definition r_f_1 := Eval vm_compute in (nth 1 r_f (mkLeafA (cD (factsR e3r) (la_state r_d_0)) RsCut)).
Lemma R_d : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41884SeS2cA1A3S8aScA5S11G0SbS6S82SeS6A1A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3f404SbS2cZ418c0SeS2cA1A3A3S3eS2eS5eA1S5S82A1A2ScA5S11G0SbS6S83SbS6S85SeS6A1A3A3A2A3").
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
  exact (populate_mid A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE PF ph FUEL e3r ru1 r_d_0 r_f_0 r_f_1 R_d LN_d NX_d W_d D_d NXe_d R_f LN_f NX_f (In_of_inclb _ _ F0_inb) (In_of_inclb _ _ Fm_inb) r tp Q).
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
  exact (famap_restate A Kc rb tp0 md0 TR KIT W0 UStopLe rho HE PF (la_state r_f_1) W_fm D_fm ph r tp Q).
Qed.
Definition R_xF__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ706a0SeS2cA1A3S84ScA5").
Local Strategy expand [R_xF__R].
Definition r_xF := Eval vm_compute in ((fun ro8__ : option (list leafA) => (match ro8__ with Some l => l | None => [] end)) R_xF__R).
Definition r_xF_0 := Eval vm_compute in (nth 0 r_xF (mkLeafA cfm RsCut)).
Definition R_mF__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZdb004SeS2cA1A3SbfS2fS5S71A1S32A2S32Z40000A3ScA5").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ706a0SeS2cA1A3S84ScA5S11G0SbS6S71SeS6A1A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZdb004SeS2cA1A3SbfS2fS5S71A1S32A2S32Z40000A3ScA5S11G0SbS6S87SeS6A1A3A2A3").
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
SfaS61S6dS104S32S84S89A6").
Proof.
  rewrite <- RF1_eq, <- DMF_eq, <- CMCF_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP.PF beg2 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cfm r_xF_0 r_mF_0
           R_xF LN_xF NX_xF W_xF D_xF SK_xF (inclb_incl _ _ XF_xFb) XX_xF NXc_xF IC_xF R17_xF R10_xF BEL_xF R11_xF R12_xF R13_xF R14_xF R15_xF
           R_mF LN_mF NX_mF SK_mF (inclb_incl _ _ XF_mFb) XX_mF W_mrF D_mrF _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCF_eq, ?DMF_eq; [exact W_mcF | exact E_msF | exact CHK_msF | exact NF_msF | exact NX_msF | exact FBC_msF | exact FBT_msF | exact ND_rF | apply Nat.leb_le; exact NO_rFb | exact OB_rF].
Qed.
Definition R_h__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ418c0SeS2cA1A3S89ScA5").
Local Strategy expand [R_h__R].
Definition r_h := Eval vm_compute in ((fun ro10__ : option (list leafA) => (match ro10__ with Some l => l | None => [] end)) R_h__R).
Definition r_h_0 := Eval vm_compute in (nth 0 r_h (mkLeafA rf1 RsCut)).
Lemma R_h : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ418c0SeS2cA1A3S89ScA5S11G0SbS6S86SeS6A1A3A2A3").
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
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc FUEL [0x418c0] rf1 [r_h_0] ph r tp Q R_h LN_h NX_h).
  intros L r1 [<-|[]] _. exact (HC r1).
Qed.
Definition R_fhP__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ418d4SeS2cA1A3S5S83A1ScA5").
Local Strategy expand [R_fhP__R].
Definition r_flP := Eval vm_compute in ((fun ro12__ : option (list leafA) => (match ro12__ with Some l => l | None => [] end)) R_fhP__R).
Definition r_flP_0 := Eval vm_compute in (nth 0 r_flP (mkLeafA (la_state r_f_0) RsCut)).
Definition cl0P := Eval vm_compute in (cL0 (factsR e3r) (la_state r_flP_0)).
Definition R_l1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ418d4SbS2cZ418e0SeS2cA1A3A3S3cS78A1ScA5").
Local Strategy expand [R_l1P__R].
Definition r_lP := Eval vm_compute in ((fun ro11__ : option (list leafA) => (match ro11__ with Some l => l | None => [] end)) R_l1P__R).
Definition r_lP_0 := Eval vm_compute in (nth 0 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition r_lP_1 := Eval vm_compute in (nth 1 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition nobFP := Eval vm_compute in (length (ss_objs (ax_S cl0P))).
Definition s_fbkP := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lP_0) nobFP)) (ax_S cl0P)).
Definition s_finP := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flP_0)) (ax_S cl0P)).
Definition R_fjP__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41560SeS2cA1A3S37S2eS5eA1S35S5S7fA1S7dA2A2ScA5").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ418d4SbS2cZ418e0SeS2cA1A3A3S3cS78A1ScA5S11G0SbS6S98SbS6S7fSeS6A1A3A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ418d4SeS2cA1A3S5S83A1ScA5S11G0SbS6Sa6SeS6A1A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41560SeS2cA1A3S37S2eS5eA1S35S5S7fA1S7dA2A2ScA5S11G0SbS6S8eSeS6A1A3A2A3").
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
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PF ph PQ HDEF FUEL cl0P r_lP_0 r_lP_1 nobFP s_fbkP SK_lP XX_lP (inclb_incl _ _ XF_lPb) NX_lP W_l1P R_l1P LN_l1P
           OB_fbP OB_fxP ENT_fbkP SID_fbkP S_bk0P S_bk2P S_bk3P (In_of_inclb _ _ FB_fbPb) (In_of_inclb _ _ FB_fxPb) e3r (la_state r_f_0) r_flP_0 r_jP_0 s_finP
           R_fhP LN_fhP NX_fhP ENT_finP SID_finP S_in0P S_in2P S_in3P W_xlP D_xlP NXe_xlP R_fjP LN_fxlP NX_fxlP r tp Q HC).
Qed.
Definition R_fhM__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ418d4SeS2cA1A3S5S86A1ScA5").
Local Strategy expand [R_fhM__R].
Definition r_flM := Eval vm_compute in ((fun ro15__ : option (list leafA) => (match ro15__ with Some l => l | None => [] end)) R_fhM__R).
Definition r_flM_0 := Eval vm_compute in (nth 0 r_flM (mkLeafA (la_state r_h_0) RsCut)).
Definition cl0M := Eval vm_compute in (cL0 (factsR e3r) (la_state r_flM_0)).
Definition R_l1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ418d4SbS2cZ418e0SeS2cA1A3A3S3cS77A1ScA5").
Local Strategy expand [R_l1M__R].
Definition r_lM := Eval vm_compute in ((fun ro14__ : option (list leafA) => (match ro14__ with Some l => l | None => [] end)) R_l1M__R).
Definition r_lM_0 := Eval vm_compute in (nth 0 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition r_lM_1 := Eval vm_compute in (nth 1 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition nobFM := Eval vm_compute in (length (ss_objs (ax_S cl0M))).
Definition s_fbkM := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lM_0) nobFM)) (ax_S cl0M)).
Definition s_finM := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flM_0)) (ax_S cl0M)).
Definition R_fjM__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41560SeS2cA1A3S37S2eS5eA1S35S5S7eA1S7cA2A2ScA5").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ418d4SbS2cZ418e0SeS2cA1A3A3S3cS77A1ScA5S11G0SbS6S97SbS6S7eSeS6A1A3A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ418d4SeS2cA1A3S5S86A1ScA5S11G0SbS6Sa5SeS6A1A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41560SeS2cA1A3S37S2eS5eA1S35S5S7eA1S7cA2A2ScA5S11G0SbS6S8dSeS6A1A3A2A3").
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
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PF ph PQ HDEF FUEL cl0M r_lM_0 r_lM_1 nobFM s_fbkM SK_lM XX_lM (inclb_incl _ _ XF_lMb) NX_lM W_l1M R_l1M LN_l1M
           OB_fbM OB_fxM ENT_fbkM SID_fbkM S_bk0M S_bk2M S_bk3M (In_of_inclb _ _ FB_fbMb) (In_of_inclb _ _ FB_fxMb) e3r (la_state r_h_0) r_flM_0 r_jM_0 s_finM
           R_fhM LN_fhM NX_fhM ENT_finM SID_finM S_in0M S_in2M S_in3M W_xlM D_xlM NXe_xlM R_fjM LN_fxlM NX_fxlM r tp Q HC).
Qed.
Definition R_t0P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S5S8eA1ScA5").
Local Strategy expand [R_t0P__R].
Definition r_t0P := Eval vm_compute in ((fun ro18__ : option (list leafA) => (match ro18__ with Some l => l | None => [] end)) R_t0P__R).
Definition r_t0P_0 := Eval vm_compute in (nth 0 r_t0P (mkLeafA (la_state r_jP_0) RsCut)).
Definition ct0P := Eval vm_compute in (cT0 (la_state r_t0P_0)).
Definition R_t1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S3dS7bA1ScA5").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S3dS7bA1ScA5S11G0SbS6S9aSbS6Sa2SeS6A1A3A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S5S8eA1ScA5S11G0SbS6Sa8SeS6A1A3A2A3").
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
S7S2dS5fSbS2cZ40e5cSeS2cA1A3Sa0ScA5").
Local Strategy expand [R_9P__R].
Definition r_9P := Eval vm_compute in ((fun ro19__ : option (list leafA) => (match ro19__ with Some l => l | None => [] end)) R_9P__R).
Definition r_9P_0 := Eval vm_compute in (nth 0 r_9P (mkLeafA xlP RsCut)).
Definition cellsfP := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9P_0) icc))) O_ri)).
Definition x3P := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9P_0) icc))).
Definition r_zP := Eval vm_compute in (match sym_runA segsA FUEL [0x3c614] x3P true with Some l => l | None => [] end).
Definition r_zP_0 := Eval vm_compute in (nth 0 r_zP (mkLeafA x3P RsCut)).
Lemma R_9P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ40e5cSeS2cA1A3Sa0ScA5S11G0SbS6S76SeS6A1A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3c614SeS2cA1A3S43S34S33S5S76A1S60A2A1A1ScA5S11G0SbS6SaaSeS6A1A3A2A3").
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
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0P r_t1P_0 r_t1P_1 nob s_bkP
    SK_tP XX_tP (inclb_incl _ _ XF_tPb) NX_tP W_t1P R_t1P LN_t1P OB_bP OB_xP ENT_bkP SID_bkP S_bk4P S_bk6P (In_of_inclb _ _ FB_bPb) (In_of_inclb _ _ FB_xPb)
    (la_state r_jP_0) r_t0P_0 s_inP e_srcP R_t0P LN_t0P NX_t0P ENT_inP SID_inP S_in4P S_in6P.
Definition exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE phX PHX HFILLX Hini e16P vMFA e32P e48P HRIv HLEN HIDC FUEL xlP r_9P_0 r_zP_0 icc cellsfP
    R_9P LN_9P NX_9P W_x1P D_x1P NX_x1P XX_1P IC_1P OB_1P RI_1P SK_2P XX_2P (inclb_incl _ _ XF_2Pb) W_3aP W_3bP FB_3P R_zP LN_zP NX_zP.
Definition back_P CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLe rho HW HE phF HREB HMK HLEN e3p (la_state r_zP_0) s_xP ENT_xP SX_xP S149_xP S159_xP HPOP.
Definition R_t0M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S5S8dA1ScA5").
Local Strategy expand [R_t0M__R].
Definition r_t0M := Eval vm_compute in ((fun ro21__ : option (list leafA) => (match ro21__ with Some l => l | None => [] end)) R_t0M__R).
Definition r_t0M_0 := Eval vm_compute in (nth 0 r_t0M (mkLeafA (la_state r_jM_0) RsCut)).
Definition ct0M := Eval vm_compute in (cT0 (la_state r_t0M_0)).
Definition R_t1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S3dS7aA1ScA5").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S3dS7aA1ScA5S11G0SbS6S99SbS6Sa1SeS6A1A3A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S5S8dA1ScA5S11G0SbS6Sa7SeS6A1A3A2A3").
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
S7S2dS5fSbS2cZ40e5cSeS2cA1A3S9fScA5").
Local Strategy expand [R_9M__R].
Definition r_9M := Eval vm_compute in ((fun ro22__ : option (list leafA) => (match ro22__ with Some l => l | None => [] end)) R_9M__R).
Definition r_9M_0 := Eval vm_compute in (nth 0 r_9M (mkLeafA xlM RsCut)).
Definition cellsfM := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9M_0) icc))) O_ri)).
Definition x3M := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9M_0) icc))).
Definition r_zM := Eval vm_compute in (match sym_runA segsA FUEL [0x3c614] x3M true with Some l => l | None => [] end).
Definition r_zM_0 := Eval vm_compute in (nth 0 r_zM (mkLeafA x3M RsCut)).
Lemma R_9M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ40e5cSeS2cA1A3S9fScA5S11G0SbS6S75SeS6A1A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3c614SeS2cA1A3S43S34S33S5S75A1S60A2A1A1ScA5S11G0SbS6Sa9SeS6A1A3A2A3").
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
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0M r_t1M_0 r_t1M_1 nob s_bkM
    SK_tM XX_tM (inclb_incl _ _ XF_tMb) NX_tM W_t1M R_t1M LN_t1M OB_bM OB_xM ENT_bkM SID_bkM S_bk4M S_bk6M (In_of_inclb _ _ FB_bMb) (In_of_inclb _ _ FB_xMb)
    (la_state r_jM_0) r_t0M_0 s_inM e_srcP R_t0M LN_t0M NX_t0M ENT_inM SID_inM S_in4M S_in6M.
Definition exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE phX PHX HFILLX Hini e16P e24M e32P e48P HRIv HLEN HIDC FUEL xlM r_9M_0 r_zM_0 icc cellsfM
    R_9M LN_9M NX_9M W_x1M D_x1M NX_x1M XX_1M IC_1M OB_1M RI_1M SK_2M XX_2M (inclb_incl _ _ XF_2Mb) W_3aM W_3bM FB_3M R_zM LN_zM NX_zM.
Definition back_M CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLe rho HW HE phF HREB HMK HLEN e3p (la_state r_zM_0) s_xM ENT_xM SX_xM S149_xM S159_xM HPOP.

Theorem refill_populate_i : ltac2:(tb__ "0|4|
SfS10S2cS2cA2A1M0G0Se3S6eSfS10SaSeeA2A1F_;F_;S10aR3R2R1A3SaS0SaR1S64A3Se3S6eS24SfS110Q40M1A1A1M2Se2Se2OF_;F_;Sc1R4R1A2S6fR5A1S0SdSe4R7A1ScA3SebS2dSc7R6R5RcR8R7A2A5Se2S24Se0ScaRbR2R8R1S61S6dR9A7SdbRcR3A2Sc8S3S0Sc8R1SffA3S0Sc8R1Sf9A3A2S111G1S2bR6PcA2A2S2cS108R1A1S2cS109R11R2A2Se5S2S0Sc8R5Sf9A3S10dSe7R1A1S10eZ4S10cS10fS16S2cSe6R1A1A2A1ScbR12R9A2A2A2A2A2S24G2SfSe1A1Se0Sc9R17R16ReR14RdSfeRaScbR17ReA2S106R7A1A3R4R3R2R1AaS1S103S2dS107R18R8A2M3R5R4R2A5S70R1eR1dR18G3S28RfA1S28R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;Frb;Se3S24G2S24RaSeaS2dS10bS61S6dR4RdR3A5R10R1R2A5SebS2dSc7R3R2R12R4RdA2A5A2FrX;Ftp';Frho';FA';S24Se0S24ScaReR3RbR2S61S6dRcA7RbSeaS2dSc9RfReR4RcR3SccA6S5S62A1R2RcA5R7A2F_;Fr';Fmd0;Frb;F_;F_;TQ;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;FE3P;FHPF;FPFam;FXGL;FCST;").
Proof.
  intros CST XGL PFam HPF E3P ->.
  apply (refill_populate CST XGL PFam W0 UStopLe (la_state r_2_0) cp2c ru1 (la_state r_f_0) (la_state r_f_1) cfm rf1 (la_state r_h_0)
           (la_state r_jP_0) xlP (la_state r_zP_0) (la_state r_jM_0) xlM (la_state r_zM_0) e3p head_i pieceU_i mid_i fm_i pieceF_i run_i fillP_i fillM_i).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_P A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_M A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_P CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_M CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
Qed.
End SpineMallocRp0.

(* [comment removed for export] *)
Module SpineMallocRp0u.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "entailsA"; "ax_X"; "axst"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "SLit"; "ss_facts"; "swf"; "ss_lenient"; "ss_objs"; "SAlu"; "SVar"; "reg_sv"; "SPNot"; "valuation"; "sprop_below"; "SPBranch"; "SPUle"; "rm"; "ss_pc"; "sv_below"; "rw"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "factsR"; "cX"; "GR"; "beg1"; "beg2"; "cE1"; "cE2"; "keepn"; "cP2"; "cXL"; "O_pcm"; "PV4"; "LV0"; "O_ri"; "cL1"; "cT1"; "cD"; "cPa"; "cPb"; "LV2"; "PV6"; "cE3"; "nobj"; "rMS"; "sMS"; "LV3"; "cE3b"; "vMU"; "cFm"; "vK"; "F_x"; "HINT_au"; "HINT_k"; "HINT_map"; "LNX"; "O_pccK"; "PNX"; "cE3a"; "idx_rot"; "k_e"; "relM"; "ri_has"; "rotM"; "vAU"; "vMFA"; "F_new"; "vNEW"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kh.SpineMallocRi0u"; "e3r"; "FUEL"; "icc"; "W0"; "r_2_0"; "nob"; "e3p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lg.SpineMallocRp0u"; "r_xF_0"; "r_xU_0"; "cmcF"; "cmcU"; "r_9M_0"; "r_9P_0"; "cl0M"; "cl0P"; "cp2c"; "ct0M"; "ct0P"; "nobFM"; "nobFP"; "r_lM_1"; "r_lP_1"; "r_p1_0"; "r_p1_1"; "r_d_0"; "r_f_0"; "cfm"; "r_f_1"; "r_h_0"; "r_mF_0"; "r_mU_0"; "rf1"; "ru1"; "dmF"; "dmU"; "r_jM_0"; "r_jP_0"; "r_p2a_0"; "r_p2a_1"; "r_p2b_0"; "r_p2b_1"; "s_fbkM"; "s_fbkP"; "s_finM"; "s_finP"; "r_lM_0"; "r_lP_0"; "r_t1M_0"; "r_t1P_0"; "s_bkM"; "s_bkP"; "s_inM"; "s_inP"; "xlM"; "xlP"; "r_t1M_1"; "r_t1P_1"; "cellsfM"; "cellsfP"; "r_flM_0"; "r_flP_0"; "r_t0M_0"; "r_t0P_0"; "r_zM_0"; "r_zP_0"; "sa0"; "sa1"; "sb0"; "sb1"; "s_xM"; "s_xP"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "instr"; "ALU_SLL"; "ALU_XOR"; "Ecall"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_pcc0"; "O_st"; "V_SIZE"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "commit_post"; "memset_post"; "TRok"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "phase"; "JR"; "entryR"; "gh_new"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocR10";
"cMr"; "a2_e"; "cMc"; "dMSf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocR13"; "F_lt"; "O_fcell"; "faend_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocR7"; "F_mu0"; "F_hi"; "x19_e0"; "x19_e1"; "popfacts"; "size_e_hi"; "size_e_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9"; "O_piece"; "O_shp"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "call_checkA"; "entails_frA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR11"; "a0_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineMallocR12"; "F_geu"; "new_e"; "rup_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocR14"; "e16P"; "e32P"; "e48P"; "e_srcP"; "e24M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocR15"; "fillT"; "phUF3"; "pieceT"; "fmT"; "headT"; "midT"; "phFin"; "phU3"; "runT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4"; "O_rif"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP"; "PF"; "PU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SpineMallocR12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocR13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocR14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocR15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kh.SpineMallocRi0u.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_p1__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41754SbS2cZ41794SeS2cA1A3A3S5S62A1ScA5").
Local Strategy expand [R_p1__R].
Definition r_p1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_p1__R).
Definition r_p1_0 := Eval vm_compute in (nth 0 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition r_p1_1 := Eval vm_compute in (nth 1 r_p1 (mkLeafA (la_state r_2_0) RsCut)).
Definition R_p2a__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ417c4SeS2cA1A3S3fS2eS5eA1S5S80A1A2ScA5").
Local Strategy expand [R_p2a__R].
Definition r_p2a := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_p2a__R).
Definition r_p2a_0 := Eval vm_compute in (nth 0 r_p2a (mkLeafA (cPa (factsR e3r) (la_state r_p1_0)) RsCut)).
Definition r_p2a_1 := Eval vm_compute in (nth 1 r_p2a (mkLeafA (cPa (factsR e3r) (la_state r_p1_0)) RsCut)).
Definition R_p2b__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ417c4SeS2cA1A3S40S2eS5eA1S5S81A1A2ScA5").
Local Strategy expand [R_p2b__R].
Definition r_p2b := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_p2b__R).
Definition r_p2b_0 := Eval vm_compute in (nth 0 r_p2b (mkLeafA (cPb (factsR e3r) (la_state r_p1_1)) RsCut)).
Definition r_p2b_1 := Eval vm_compute in (nth 1 r_p2b (mkLeafA (cPb (factsR e3r) (la_state r_p1_1)) RsCut)).
Definition cp2c := Eval vm_compute in (cP2c (factsR e3r) (la_state r_p2a_1)).
Lemma FP_inb : ltac2:(tb__ "0|0|
S0SdS65SbS19S26Sb7S5dS4bA3SeS19A1A3S1cS4S5S62A1A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p1 : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41754SbS2cZ41794SeS2cA1A3A3S5S62A1ScA5S11G0SbS6S80SbS6S81SeS6A1A3A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ417c4SeS2cA1A3S3fS2eS5eA1S5S80A1A2ScA5S11G0SbS6S8fSbS6S90SeS6A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_p2a__R <: R_p2a__R = Some [r_p2a_0; r_p2a_1]). Qed.
Lemma LN_p2a : ltac2:(tb__ "0|0|
S0SdS1eS4S3fS2eS5eA1S5S80A1A2A1A1S15A3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_p2a : ltac2:(tb__ "0|0|
S0SdS67S30S1aS4S3fS2eS5eA1S5S80A1A2A1A1A2ScA3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_p2b : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ417c4SeS2cA1A3S40S2eS5eA1S5S81A1A2ScA5S11G0SbS6S91SbS6S92SeS6A1A3A3A2A3").
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
  exact (populate_head A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE FUEL e3r (la_state r_2_0) r_p1_0 r_p1_1 r_p2a_0 r_p2a_1 r_p2b_0 r_p2b_1 cp2c sa0 sa1 sb0 sb1
           (In_of_inclb _ _ FP_inb) R_p1 LN_p1 NX_p1 (In_of_inclb _ _ Fa_inb) (In_of_inclb _ _ Fb_inb) W_pa D_pa NXe_pa W_pb D_pb NXe_pb R_p2a LN_p2a NX_p2a R_p2b LN_p2b NX_p2b
           (In_of_inclb _ _ Fa0_inb) (In_of_inclb _ _ Fa1_inb) (In_of_inclb _ _ Fb0_inb) (In_of_inclb _ _ Fb1_inb) W_a0 W_a1 W_b0 W_b1 D_a0 D_a1 D_b0 D_b1 NXe_a0 NXe_a1 NXe_b0 NXe_b1
           ENT_a0 ENT_a1 ENT_b0 ENT_b1 SID_a0 SID_a1 SID_b0 SID_b1 r tp Q HC).
Qed.
Definition R_xU__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ706a0SeS2cA1A3S79ScA5").
Local Strategy expand [R_xU__R].
Definition r_xU := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_xU__R).
Definition r_xU_0 := Eval vm_compute in (nth 0 r_xU (mkLeafA cp2c RsCut)).
Definition R_mU__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZdb004SeS2cA1A3SbfS2fS5S72A1S31A2S31Z40000A3ScA5").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ706a0SeS2cA1A3S79ScA5S11G0SbS6S72SeS6A1A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZdb004SeS2cA1A3SbfS2fS5S72A1S31A2S31Z40000A3ScA5S11G0SbS6S88SeS6A1A3A2A3").
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
SfaS61S6dS105S31S79S8aA6").
Proof.
  rewrite <- RU1_eq, <- DMU_eq, <- CMCU_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PU beg1 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cp2c r_xU_0 r_mU_0
           R_xU LN_xU NX_xU W_xU D_xU SK_xU (inclb_incl _ _ XF_xUb) XX_xU NXc_xU IC_xU R17_xU R10_xU BEL_xU R11_xU R12_xU R13_xU R14_xU R15_xU
           R_mU LN_mU NX_mU SK_mU (inclb_incl _ _ XF_mUb) XX_mU W_mrU D_mrU _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCU_eq, ?DMU_eq; [exact W_mcU | exact E_msU | exact CHK_msU | exact NF_msU | exact NX_msU | exact FBC_msU | exact FBT_msU | exact ND_rU | apply Nat.leb_le; exact NO_rUb | exact OB_rU].
Qed.
Definition R_d__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41884SeS2cA1A3S8aScA5").
Local Strategy expand [R_d__R].
Definition r_d := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) R_d__R).
Definition r_d_0 := Eval vm_compute in (nth 0 r_d (mkLeafA ru1 RsCut)).
Definition R_f__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ3f404SbS2cZ418c0SeS2cA1A3A3S3eS2eS5eA1S5S82A1A2ScA5").
Local Strategy expand [R_f__R].
Definition r_f := Eval vm_compute in ((fun ro7__ : option (list leafA) => (match ro7__ with Some l => l | None => [] end)) R_f__R).
Definition r_f_0 := Eval vm_compute in (nth 0 r_f (mkLeafA (cD (factsR e3r) (la_state r_d_0)) RsCut)).
Definition r_f_1 := Eval vm_compute in (nth 1 r_f (mkLeafA (cD (factsR e3r) (la_state r_d_0)) RsCut)).
Lemma R_d : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41884SeS2cA1A3S8aScA5S11G0SbS6S82SeS6A1A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3f404SbS2cZ418c0SeS2cA1A3A3S3eS2eS5eA1S5S82A1A2ScA5S11G0SbS6S83SbS6S85SeS6A1A3A3A2A3").
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
  exact (populate_mid A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE PF ph FUEL e3r ru1 r_d_0 r_f_0 r_f_1 R_d LN_d NX_d W_d D_d NXe_d R_f LN_f NX_f (In_of_inclb _ _ F0_inb) (In_of_inclb _ _ Fm_inb) r tp Q).
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
  exact (famap_restate A Kc rb tp0 md0 TR KIT W0 UStopLe rho HE PF (la_state r_f_1) W_fm D_fm ph r tp Q).
Qed.
Definition R_xF__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ706a0SeS2cA1A3S84ScA5").
Local Strategy expand [R_xF__R].
Definition r_xF := Eval vm_compute in ((fun ro8__ : option (list leafA) => (match ro8__ with Some l => l | None => [] end)) R_xF__R).
Definition r_xF_0 := Eval vm_compute in (nth 0 r_xF (mkLeafA cfm RsCut)).
Definition R_mF__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZdb004SeS2cA1A3SbfS2fS5S71A1S32A2S32Z40000A3ScA5").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ706a0SeS2cA1A3S84ScA5S11G0SbS6S71SeS6A1A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZdb004SeS2cA1A3SbfS2fS5S71A1S32A2S32Z40000A3ScA5S11G0SbS6S87SeS6A1A3A2A3").
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
SfaS61S6dS104S32S84S89A6").
Proof.
  rewrite <- RF1_eq, <- DMF_eq, <- CMCF_eq.
  intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 PORD PQ HBv HBn HRc HRr r tp Q HC.
  refine (piece_full A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP.PF beg2 ph PH0 PORD PQ HBv HBn HRc HRr FUEL cfm r_xF_0 r_mF_0
           R_xF LN_xF NX_xF W_xF D_xF SK_xF (inclb_incl _ _ XF_xFb) XX_xF NXc_xF IC_xF R17_xF R10_xF BEL_xF R11_xF R12_xF R13_xF R14_xF R15_xF
           R_mF LN_mF NX_mF SK_mF (inclb_incl _ _ XF_mFb) XX_mF W_mrF D_mrF _ _ _ _ _ _ _ _ _ _ r tp Q HC);
    rewrite ?CMCF_eq, ?DMF_eq; [exact W_mcF | exact E_msF | exact CHK_msF | exact NF_msF | exact NX_msF | exact FBC_msF | exact FBT_msF | exact ND_rF | apply Nat.leb_le; exact NO_rFb | exact OB_rF].
Qed.
Definition R_h__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ418c0SeS2cA1A3S89ScA5").
Local Strategy expand [R_h__R].
Definition r_h := Eval vm_compute in ((fun ro10__ : option (list leafA) => (match ro10__ with Some l => l | None => [] end)) R_h__R).
Definition r_h_0 := Eval vm_compute in (nth 0 r_h (mkLeafA rf1 RsCut)).
Lemma R_h : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ418c0SeS2cA1A3S89ScA5S11G0SbS6S86SeS6A1A3A2A3").
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
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc FUEL [0x418c0] rf1 [r_h_0] ph r tp Q R_h LN_h NX_h).
  intros L r1 [<-|[]] _. exact (HC r1).
Qed.
Definition R_fhP__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ418d4SeS2cA1A3S5S83A1ScA5").
Local Strategy expand [R_fhP__R].
Definition r_flP := Eval vm_compute in ((fun ro12__ : option (list leafA) => (match ro12__ with Some l => l | None => [] end)) R_fhP__R).
Definition r_flP_0 := Eval vm_compute in (nth 0 r_flP (mkLeafA (la_state r_f_0) RsCut)).
Definition cl0P := Eval vm_compute in (cL0 (factsR e3r) (la_state r_flP_0)).
Definition R_l1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ418d4SbS2cZ418e0SeS2cA1A3A3S3cS78A1ScA5").
Local Strategy expand [R_l1P__R].
Definition r_lP := Eval vm_compute in ((fun ro11__ : option (list leafA) => (match ro11__ with Some l => l | None => [] end)) R_l1P__R).
Definition r_lP_0 := Eval vm_compute in (nth 0 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition r_lP_1 := Eval vm_compute in (nth 1 r_lP (mkLeafA (cL1 cl0P) RsCut)).
Definition nobFP := Eval vm_compute in (length (ss_objs (ax_S cl0P))).
Definition s_fbkP := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lP_0) nobFP)) (ax_S cl0P)).
Definition s_finP := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flP_0)) (ax_S cl0P)).
Definition R_fjP__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41560SeS2cA1A3S37S2eS5eA1S35S5S7fA1S7dA2A2ScA5").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ418d4SbS2cZ418e0SeS2cA1A3A3S3cS78A1ScA5S11G0SbS6S98SbS6S7fSeS6A1A3A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ418d4SeS2cA1A3S5S83A1ScA5S11G0SbS6Sa6SeS6A1A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41560SeS2cA1A3S37S2eS5eA1S35S5S7fA1S7dA2A2ScA5S11G0SbS6S8eSeS6A1A3A2A3").
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
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PF ph PQ HDEF FUEL cl0P r_lP_0 r_lP_1 nobFP s_fbkP SK_lP XX_lP (inclb_incl _ _ XF_lPb) NX_lP W_l1P R_l1P LN_l1P
           OB_fbP OB_fxP ENT_fbkP SID_fbkP S_bk0P S_bk2P S_bk3P (In_of_inclb _ _ FB_fbPb) (In_of_inclb _ _ FB_fxPb) e3r (la_state r_f_0) r_flP_0 r_jP_0 s_finP
           R_fhP LN_fhP NX_fhP ENT_finP SID_finP S_in0P S_in2P S_in3P W_xlP D_xlP NXe_xlP R_fjP LN_fxlP NX_fxlP r tp Q HC).
Qed.
Definition R_fhM__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ418d4SeS2cA1A3S5S86A1ScA5").
Local Strategy expand [R_fhM__R].
Definition r_flM := Eval vm_compute in ((fun ro15__ : option (list leafA) => (match ro15__ with Some l => l | None => [] end)) R_fhM__R).
Definition r_flM_0 := Eval vm_compute in (nth 0 r_flM (mkLeafA (la_state r_h_0) RsCut)).
Definition cl0M := Eval vm_compute in (cL0 (factsR e3r) (la_state r_flM_0)).
Definition R_l1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ418d4SbS2cZ418e0SeS2cA1A3A3S3cS77A1ScA5").
Local Strategy expand [R_l1M__R].
Definition r_lM := Eval vm_compute in ((fun ro14__ : option (list leafA) => (match ro14__ with Some l => l | None => [] end)) R_l1M__R).
Definition r_lM_0 := Eval vm_compute in (nth 0 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition r_lM_1 := Eval vm_compute in (nth 1 r_lM (mkLeafA (cL1 cl0M) RsCut)).
Definition nobFM := Eval vm_compute in (length (ss_objs (ax_S cl0M))).
Definition s_fbkM := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_lM_0) nobFM)) (ax_S cl0M)).
Definition s_finM := Eval vm_compute in (infer_sub GR (ax_S (la_state r_flM_0)) (ax_S cl0M)).
Definition R_fjM__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41560SeS2cA1A3S37S2eS5eA1S35S5S7eA1S7cA2A2ScA5").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ418d4SbS2cZ418e0SeS2cA1A3A3S3cS77A1ScA5S11G0SbS6S97SbS6S7eSeS6A1A3A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ418d4SeS2cA1A3S5S86A1ScA5S11G0SbS6Sa5SeS6A1A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41560SeS2cA1A3S37S2eS5eA1S35S5S7eA1S7cA2A2ScA5S11G0SbS6S8dSeS6A1A3A2A3").
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
  exact (fill_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE PF ph PQ HDEF FUEL cl0M r_lM_0 r_lM_1 nobFM s_fbkM SK_lM XX_lM (inclb_incl _ _ XF_lMb) NX_lM W_l1M R_l1M LN_l1M
           OB_fbM OB_fxM ENT_fbkM SID_fbkM S_bk0M S_bk2M S_bk3M (In_of_inclb _ _ FB_fbMb) (In_of_inclb _ _ FB_fxMb) e3r (la_state r_h_0) r_flM_0 r_jM_0 s_finM
           R_fhM LN_fhM NX_fhM ENT_finM SID_finM S_in0M S_in2M S_in3M W_xlM D_xlM NXe_xlM R_fjM LN_fxlM NX_fxlM r tp Q HC).
Qed.
Definition R_t0P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S5S8eA1ScA5").
Local Strategy expand [R_t0P__R].
Definition r_t0P := Eval vm_compute in ((fun ro18__ : option (list leafA) => (match ro18__ with Some l => l | None => [] end)) R_t0P__R).
Definition r_t0P_0 := Eval vm_compute in (nth 0 r_t0P (mkLeafA (la_state r_jP_0) RsCut)).
Definition ct0P := Eval vm_compute in (cT0 (la_state r_t0P_0)).
Definition R_t1P__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S3dS7bA1ScA5").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S3dS7bA1ScA5S11G0SbS6S9aSbS6Sa2SeS6A1A3A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S5S8eA1ScA5S11G0SbS6Sa8SeS6A1A3A2A3").
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
S7S2dS5fSbS2cZ40e5cSeS2cA1A3Sa0ScA5").
Local Strategy expand [R_9P__R].
Definition r_9P := Eval vm_compute in ((fun ro19__ : option (list leafA) => (match ro19__ with Some l => l | None => [] end)) R_9P__R).
Definition r_9P_0 := Eval vm_compute in (nth 0 r_9P (mkLeafA xlP RsCut)).
Definition cellsfP := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9P_0) icc))) O_ri)).
Definition x3P := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9P_0) icc))).
Definition r_zP := Eval vm_compute in (match sym_runA segsA FUEL [0x3c614] x3P true with Some l => l | None => [] end).
Definition r_zP_0 := Eval vm_compute in (nth 0 r_zP (mkLeafA x3P RsCut)).
Lemma R_9P : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ40e5cSeS2cA1A3Sa0ScA5S11G0SbS6S76SeS6A1A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3c614SeS2cA1A3S43S34S33S5S76A1S60A2A1A1ScA5S11G0SbS6SaaSeS6A1A3A2A3").
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
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0P r_t1P_0 r_t1P_1 nob s_bkP
    SK_tP XX_tP (inclb_incl _ _ XF_tPb) NX_tP W_t1P R_t1P LN_t1P OB_bP OB_xP ENT_bkP SID_bkP S_bk4P S_bk6P (In_of_inclb _ _ FB_bPb) (In_of_inclb _ _ FB_xPb)
    (la_state r_jP_0) r_t0P_0 s_inP e_srcP R_t0P LN_t0P NX_t0P ENT_inP SID_inP S_in4P S_in6P.
Definition exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE phX PHX HFILLX Hini e16P vMFA e32P e48P HRIv HLEN HIDC FUEL xlP r_9P_0 r_zP_0 icc cellsfP
    R_9P LN_9P NX_9P W_x1P D_x1P NX_x1P XX_1P IC_1P OB_1P RI_1P SK_2P XX_2P (inclb_incl _ _ XF_2Pb) W_3aP W_3bP FB_3P R_zP LN_zP NX_zP.
Definition back_P CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLe rho HW HE phF HREB HMK HLEN e3p (la_state r_zP_0) s_xP ENT_xP SX_xP S149_xP S159_xP HPOP.
Definition R_t0M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S5S8dA1ScA5").
Local Strategy expand [R_t0M__R].
Definition r_t0M := Eval vm_compute in ((fun ro21__ : option (list leafA) => (match ro21__ with Some l => l | None => [] end)) R_t0M__R).
Definition r_t0M_0 := Eval vm_compute in (nth 0 r_t0M (mkLeafA (la_state r_jM_0) RsCut)).
Definition ct0M := Eval vm_compute in (cT0 (la_state r_t0M_0)).
Definition R_t1M__R : option (list leafA) := ltac2:(tb__ "0|0|
S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S3dS7aA1ScA5").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S3dS7aA1ScA5S11G0SbS6S99SbS6Sa1SeS6A1A3A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ41570SbS2cZ41584SeS2cA1A3A3S5S8dA1ScA5S11G0SbS6Sa7SeS6A1A3A2A3").
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
S7S2dS5fSbS2cZ40e5cSeS2cA1A3S9fScA5").
Local Strategy expand [R_9M__R].
Definition r_9M := Eval vm_compute in ((fun ro22__ : option (list leafA) => (match ro22__ with Some l => l | None => [] end)) R_9M__R).
Definition r_9M_0 := Eval vm_compute in (nth 0 r_9M (mkLeafA xlM RsCut)).
Definition cellsfM := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9M_0) icc))) O_ri)).
Definition x3M := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9M_0) icc))).
Definition r_zM := Eval vm_compute in (match sym_runA segsA FUEL [0x3c614] x3M true with Some l => l | None => [] end).
Definition r_zM_0 := Eval vm_compute in (nth 0 r_zM (mkLeafA x3M RsCut)).
Lemma R_9M : ltac2:(tb__ "0|1|
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ40e5cSeS2cA1A3S9fScA5S11G0SbS6S75SeS6A1A3A2A3").
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
S0S12SfS6A1M0A1S7S2dS5fSbS2cZ3c614SeS2cA1A3S43S34S33S5S75A1S60A2A1A1ScA5S11G0SbS6Sa9SeS6A1A3A2A3").
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
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0M r_t1M_0 r_t1M_1 nob s_bkM
    SK_tM XX_tM (inclb_incl _ _ XF_tMb) NX_tM W_t1M R_t1M LN_t1M OB_bM OB_xM ENT_bkM SID_bkM S_bk4M S_bk6M (In_of_inclb _ _ FB_bMb) (In_of_inclb _ _ FB_xMb)
    (la_state r_jM_0) r_t0M_0 s_inM e_srcP R_t0M LN_t0M NX_t0M ENT_inM SID_inM S_in4M S_in6M.
Definition exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE phX PHX HFILLX Hini e16P e24M e32P e48P HRIv HLEN HIDC FUEL xlM r_9M_0 r_zM_0 icc cellsfM
    R_9M LN_9M NX_9M W_x1M D_x1M NX_x1M XX_1M IC_1M OB_1M RI_1M SK_2M XX_2M (inclb_incl _ _ XF_2Mb) W_3aM W_3bM FB_3M R_zM LN_zM NX_zM.
Definition back_M CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLe rho HW HE phF HREB HMK HLEN e3p (la_state r_zM_0) s_xM ENT_xM SX_xM S149_xM S159_xM HPOP.

Theorem refill_populate_i : ltac2:(tb__ "0|4|
SfS10S2cS2cA2A1M0G0Se3S6eSfS10SaSeeA2A1F_;F_;S10aR3R2R1A3SaS0SaR1S64A3Se3S6eS24SfS110Q40M1A1A1M2Se2Se2OF_;F_;Sc1R4R1A2S6fR5A1S0SdSe4R7A1ScA3SebS2dSc7R6R5RcR8R7A2A5Se2S24Se0ScaRbR2R8R1S61S6dR9A7SdbRcR3A2Sc8S3S0Sc8R1SffA3S0Sc8R1Sf9A3A2S111G1S2bR6PcA2A2S2cS108R1A1S2cS109R11R2A2Se5S2S0Sc8R5Sf9A3S10dSe7R1A1S10eZ4S10cS10fS16S2cSe6R1A1A2A1ScbR12R9A2A2A2A2A2S24G2SfSe1A1Se0Sc9R17R16ReR14RdSfeRaScbR17ReA2S106R7A1A3R4R3R2R1AaS1S103S2dS107R18R8A2M3R5R4R2A5S70R1eR1dR18G3S28RfA1S28R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;Frb;Se3S24G2S24RaSeaS2dS10bS61S6dR4RdR3A5R10R1R2A5SebS2dSc7R3R2R12R4RdA2A5A2FrX;Ftp';Frho';FA';S24Se0S24ScaReR3RbR2S61S6dRcA7RbSeaS2dSc9RfReR4RcR3SccA6S5S62A1R2RcA5R7A2F_;Fr';Fmd0;Frb;F_;F_;TQ;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;FE3P;FHPF;FPFam;FXGL;FCST;").
Proof.
  intros CST XGL PFam HPF E3P ->.
  apply (refill_populate CST XGL PFam W0 UStopLe (la_state r_2_0) cp2c ru1 (la_state r_f_0) (la_state r_f_1) cfm rf1 (la_state r_h_0)
           (la_state r_jP_0) xlP (la_state r_zP_0) (la_state r_jM_0) xlM (la_state r_zM_0) e3p head_i pieceU_i mid_i fm_i pieceF_i run_i fillP_i fillM_i).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_P A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_M A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_P A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_M A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_P CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_M CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
Qed.
End SpineMallocRp0u.

(* [comment removed for export] *)
Module RefillPlug0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "False"; "and"; "iff"; "not"; "or"; "@Corelib.Init.Datatypes"; "list"; "bool"; "length"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "AE_A"; "Posts_malloc"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "phase"; "gh_new"; "JR"; "entryR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E3r"; "E3p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "cls_of"; "cst_of"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocR15"; "phUF3"; "phFin"; "phU3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocR7"; "popfacts"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP RebuildM SegD_wf SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ju.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineMallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocR14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocR15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.RebuildRN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ju.RebuildRQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.MallocHitTail0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l9.MallocHitTail0E.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ka.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kh.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Section PLUG0.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S4S2aVCST;R1A2S2aS39R2A2S6F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S4S2aVCST;R1A2S9S3dR2A1A1F_;Fa;").
Let W0 : list ulink := Wcan 0.
Let st0 : ustop := UStopLe.

Lemma hreb_Q : ltac2:(tb__ "0|3|
S10S15S1SbS25Q40M0A1A1M1S5ScS11R4A1SfA3S1S2eS23R7R2R4R1VW0;Vst0;R5A7S3fR8R3A2S20SaS5S20R1S36A3S5S20R1S34A3A2S26G0S2R6PcA2A2S4S2cR1A1S4S2dRdR2A2S12S8S5S20R5S34A3S41S14R1A1S42Z4S40S43SdS4S13R1A1A2A1S21ReR9A2A2A2A2A2S1G1SbS2fA1S2eS22R13R12ReR10RdS35RaS21R13ReA2S3aR7A1A3R4R3R2R1AaS7S29S0S3bR14R8A2M2R5R4R2A5S19VCST;VXGL;R14G2S3RfA1S3R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;Frb;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Hini rb md0 HE PF phX [-> | ->] nv c cs HB r tp' tr md HJ.
  - rewrite phQ_P in HJ. apply (refill_rebuild_Q CST XGL HCST HXGL A Kc rb tp md0 W0 st0 rho HE PF false Hini) with (tr := tr); [|exact HJ].
    split; [discriminate|]. intros HLT. apply HB in HLT. unfold phU3, phUF3 in HLT. discriminate HLT.
  - rewrite phQ_M in HJ. apply (refill_rebuild_Q CST XGL HCST HXGL A Kc rb tp md0 W0 st0 rho HE PF true Hini) with (tr := tr); [|exact HJ].
    split; [intros _; apply HB; reflexivity | reflexivity].
Qed.

Theorem refill_core_0 : ltac2:(tb__ "0|3|
S15S30S30OF_;F_;S3cR2R1A2S16R3A1S10S15SbSeS37S1fA2A1F_;F_;S3eVCST;VXGL;R1A3S10S1SbS25Q40M0A1A1M1S1R9S1bS0S24VW0;Vst0;R4RaR3A5S28VW0;Vst0;Z2M2A3R1R2A5S1eS0S1aR3R2R6R4RaA2A5A2FrX;Ftp';Frho';FA';S10S1G1S5S4S2bR3S26G0S2R2PcA2A2A2Z0A3S1RbS1bS0S24VW0;Vst0;R5RcR4A5S27VW0;Vst0;G2A3R1R3A5S1eS0S1aR4R3R8R5RcA2A5A2FrhoE;F_;Ftp;Frho;FA;F_;FHPF;FPFam;FHKc;FKIT;FTR;FKc;").
Proof.
  intros Kc TR KIT HKc PFam HPF HPOP A rho tp Hcnt.
  destruct (aa_cache_inited A) eqn:Hini.
  -
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocRi0.refill_N_i CST XGL PFam HPF (E3r W0 st0 2) (E3p W0 st0 2) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocRi0.E3r_eq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocRi0.E3p_eq A Kc rho tp TR KIT HKc Hini Hcnt).
    + intros rb md0 HE HNP r tp' tr md HJ. exact (refill_rebuild_N CST XGL HCST HXGL A Kc rb tp md0 W0 st0 rho HE Hini HNP r tp' tr md HJ).
    + exact HPOP.
    + exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lg.SpineMallocRp0.refill_populate_i CST XGL PFam HPF (E3p W0 st0 2) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocRi0.E3p_eq A Kc rho tp TR KIT HKc Hini (hreb_Q A Kc rho tp Hini) HPOP).
  -
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ka.SpineMallocRu0.refill_uninit_i CST XGL HCST HXGL PFam HPF (E3r W0 st0 2) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ka.SpineMallocRu0.e3u OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineMallocRi0.E3r_eq eq_refl A Kc rho tp TR KIT HKc Hini Hcnt).
    intros rho1 rX E1.
    assert (Hcnt1 : cnt_of (initA A) (bv_unsigned (rw rho1 12%positive)) = 0) by (rewrite E1; exact Hcnt).
    assert (Hini1 : aa_cache_inited (initA A) = true) by reflexivity.
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kh.SpineMallocRi0u.refill_N_i CST XGL PFam HPF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ka.SpineMallocRu0.e3u (E3p W0 st0 2) eq_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kh.SpineMallocRi0u.E3p_eq (initA A) Kc rho1 tp TR KIT HKc Hini1 Hcnt1).
    + intros rb md0 HE HNP r tp' tr md HJ. exact (refill_rebuild_N CST XGL HCST HXGL (initA A) Kc rb tp md0 W0 st0 rho1 HE Hini1 HNP r tp' tr md HJ).
    + exact HPOP.
    + exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lg.SpineMallocRp0u.refill_populate_i CST XGL PFam HPF (E3p W0 st0 2) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kh.SpineMallocRi0u.E3p_eq (initA A) Kc rho1 tp TR KIT HKc Hini1 (hreb_Q (initA A) Kc rho1 tp Hini1) HPOP).
Qed.

Theorem refill_all_0 : ltac2:(tb__ "0|1|
S33OF_;S10S15S1SbS25Q40M0A1A1S16R3A1S1dS0R6S1cR4A1A3S38S0R7S1cR5A1A3S5S4S2bR7S26G0S2R5PcA2A2A2Z0A3S1S32S0RaS1bS0S24VW0;Vst0;R9R8R7A5S27VW0;Vst0;Z2A3R1R6A5S1eS0S1aR7R6S18S17S29S0A1VCST;VXGL;VW0;Vst0;R9R8A8A5A4FrhoE;F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokl Hokp Hcnt.
  apply (refill_core_0 Kc (triple segs ok) (TRok_triple Kc ok Hokl Hokp) HKc (PF_malloc CST XGL W0 st0) (posts_conv_malloc CST XGL W0 st0)); [|exact Hcnt].
  intros A' rho' tp' rX. exact (malloc_hit_tail_0 CST XGL HCST HXGL HCSTM HCSTD ok A' Kc rho' tp' HKc Hokl Hokp rX).
Qed.

Theorem erefill_all_0 : ltac2:(tb__ "0|1|
S10S15S1SbS25Q40M0A1A1S16R3A1S5S4S2bR5S26G0S2R3PcA2A2A2Z0A3S1S31S0S1bS0S24VW0;Vst0;R7R6R5A5S27VW0;Vst0;Z2A3R1R4A5S1eS0S1aR5R4S18S17S29S0A1VCST;VXGL;VW0;Vst0;R7R6A8A5A3FrhoE;F_;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc Hcnt.
  apply (refill_core_0 Kc (etriple segs) (TRok_etriple Kc) HKc (PF_malloc CST XGL W0 st0) (posts_conv_malloc CST XGL W0 st0)); [|exact Hcnt].
  intros A' rho' tp' rX. exact (emalloc_hit_tail_0 CST XGL HCST HXGL HCSTM HCSTD A' Kc rho' tp' HKc rX).
Qed.
End PLUG0.
End RefillPlug0.

(* [comment removed for export] *)
Module F0A_hbN_disj.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "iff"; "or"; "@Corelib.Init.Datatypes"; "nat"; "bool"; "option"; "pair"; "true"; "andb"; "Some"; "length"; "list"; "negb"; "cons"; "fst"; "prod"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "div"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "rw"; "valuation"; "obj_range"; "ranges_disjoint"; "ss_objs"; "rl"; "sprop"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "sec_chunk"; "aa_sec"; "aa_geom"; "ag_ctx"; "ag_spacebeg"; "ag_thread"; "sc_map_beg"; "sc_map_size"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "nth_error"; "combine"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_hbN_zones"; "zenv"; "in_zoneW"; "zd_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lg.F0A_hbN_disj"; "obj_offb"; "zone_of"; "refsX"; "hbdisj_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kw.F0A_hbN_scan"; "ENVXs"; "hbnums"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert"; "hv_EMd"; "hv_EUd"; "hbfam"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kv.F0A_hbN_scand"; "FCHs"; "hbscanF_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop"; "ZUXl"; "zbE"; "ZDNX"; "ZDU"; "zhiX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue"; "same_rng"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue"; "zloS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states"; "OBJ2"; "vH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail"; "MB"; "ME"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_env F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require le.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_hbN_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.F0A_hbN_step OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_entry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_hbN_stepU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kv.F0A_hbN_scand OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kw.F0A_hbN_scan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition zone_of (d : zdesc) : nat := fst (fst d).
Definition obj_offb (nW : nat) (ZU : list nat) (z0 : nat) (refs : list (sobj * zdesc)) (o : sobj) : bool := ltac2:(tb__ "0|2|
S7S22A1S6Lx;S35VnW;Vo;A2S22SaSeS3cS37R1A1M0Vz0;A2A1S2dS5S3cG0A1VZU;A3A2Ld;S2dS11S19S22A2M1G1SaS4dVo;S10S19S22R1A3A2SeS3cS37S12S19S22R1A3A1Vz0;A2A1A2Lrd;Vrefs;A3X7x2").
Definition refsX (l : bool) : list (sobj * zdesc) := ltac2:(tb__ "0|0|
S2fS19S22S4fVl;S50A2SfS22S48S47Vl;A1A3A4").
Definition disj_chk (nW : nat) (l : bool) (cv : hbvar) : bool := ltac2:(tb__ "0|2|
SaS2cS19S36VnW;S45Vl;A1M0U4S38Vl;A1M1A4S1eS32S3eVcv;A1A1A1A3S2cS19S36VnW;G0U5G1A4S1eS32S3fVcv;A1A1A1A3A2").

Record hbdisj_ok (nW : nat) (l : bool) (cv : hbvar) : Prop := mkDJ { dj_chk : disj_chk nW l cv = true }.

Lemma off_zone : ltac2:(tb__ "0|3|
S1bS5S13F_;M0G0G0SdS5A1S5S5S2bS5R2R3A3S2bS5R2R4A3S2S0S5R4R3A3A1S4S16S15R9R5A1M1R7R5A1A2S15R9R4A1M2R8R4A1A2A2S16S15G2R7R4A1A2S15G1R8R5A1A2A2A2F_;F_;F_;Fz';Fz;S5S19S22S34R9R8R7R6R5R2R1A7S2S0S5S37R2A1R4A3A1S2bS5R5R7A3S13S13S16S15RdR8A1RcR8A1A2R2A2S16R2S15ReR9A1RcR9A1A2A2S1dS1cR10R9A2S8S13S13R4R3A4A2F_;F_;Fb;Fa;F_;F_;F_;Fd;Fo;Fz0;F_;FZU;Fzhi;Fzlo;Fzb;Frho;").
Proof.
  intros rho zb zlo zhi ZU Hsep z0 o [[z lo] hi] (U & R) NE U0 a b Ha Hb. unfold zone_of in NE. cbn [fst] in NE.
  unfold SymState.ranges_disjoint. cbn [fst snd]. destruct R as [R|[R1 R2]]; [left; exact R|]. destruct (Hsep z z0 U U0 NE); lia.
Qed.
Lemma Forall2_In_combine : forall (X Y : Type) (P : X -> Y -> Prop) xs ys x y, Forall2 P xs ys -> In (x, y) (combine xs ys) -> P x y.
Proof. intros X Y P xs ys x y H. induction H as [|x0 y0 xs' ys' H0 H IH]; cbn [combine In]; [intros []|]. intros [Eq|Hin]; [injection Eq as <- <-; exact H0 | exact (IH Hin)]. Qed.

Section Disj.
Variables (nW : nat) (A : AA) (p n : Z) (i : nat) (ch : sec_chunk) (l : bool) (lst : sec_chunk) (cv : hbvar).
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Hypothesis HNUM : ltac2:(tb__ "0|0|
S3bVA;Vp;Vn;Vi;Vch;A5").
Hypothesis Hl : ltac2:(tb__ "0|1|
S0S7S23A1S2eS23S24VA;A1M0S3dScS23G0A2U1A2A3SbS23Vlst;A2A3").
Hypothesis HLI : ltac2:(tb__ "0|0|
S3S0S6Vl;S9A3S0S5Vi;S3dScS23S24VA;A1A2U1A2A3A2").
Hypothesis HI : ltac2:(tb__ "0|0|
S0S7S23A1S2eS23S24VA;A1Vi;A3SbS23Vch;A2A3").

Lemma obj_off_sound : ltac2:(tb__ "0|1|
S1bS5S19S13S13S33VnW;VA;Vp;Vn;Vch;R5A6S3aVA;Vi;Vch;Vl;Vlst;R6A6S2bS5R6S45Vl;A1M0A3S0S6S36VnW;G0R7S38Vl;A1R6A5S9A3S16S15S46VA;Vi;Vch;Vlst;R8A5S4eR8A1A2R6A2S16R6S15S46VA;Vi;Vch;Vlst;R9A5S49Vmsz;R9A2A2A2S1dS1cRbR9A2S8S13S13R8R7A4A2F_;F_;F_;F_;F_;F_;Fb;Fa;Fo;Fz0;Fr;").
Proof.
  intros r z0 o a b ZE EX HZ0 HB Ha Hb. unfold obj_offb in HB.
  pose proof (zsepE_hb A p n i ch HI HNUM l lst Hl HLI) as SEP.
  destruct (zd_of nW o) as [d|] eqn:Ed.
  - apply andb_prop in HB as [N1 N2]. apply negb_true_iff in N1. apply Nat.eqb_neq in N1. apply existsb_exists in N2 as (z & Hz & Ez). apply Nat.eqb_eq in Ez.
    assert (IZ : in_zoneW r (zbE A i ch lst) zloS (zhiX msz) (ZUXl l) o d).
    { apply (zd_sound nW A p n ch r (zbE A i ch lst) zloS (zhiX msz) (ZUXl l)); try (repeat split; reflexivity); [exact ZE | exact Ed | unfold zone_of in Ez; rewrite Ez; exact Hz]. }
    exact (off_zone r _ _ _ _ SEP z0 o d IZ N1 HZ0 a b Ha Hb).
  - apply existsb_exists in HB as ([ro rd] & Hin & HB). cbn [fst snd] in HB. apply andb_prop in HB as [S1 N1]. apply negb_true_iff in N1. apply Nat.eqb_neq in N1.
    pose proof (exit_zones_hb2 A p n i ch HI HNUM l lst r Hl HLI EX) as FZ.
    pose proof (Forall2_In_combine _ _ _ _ _ ro rd FZ Hin) as IZ.
    rewrite (SegQ3M_glue.same_rng_range r o ro S1). exact (off_zone r _ _ _ _ SEP z0 ro rd IZ N1 HZ0 a b Ha Hb).
Qed.

Hypothesis DJ : ltac2:(tb__ "0|0|
S39VnW;Vl;Vcv;A3").

Lemma DISJ4_hb : ltac2:(tb__ "0|1|
S1bS33VnW;VA;Vp;Vn;Vch;R1A6S3aVA;Vi;Vch;Vl;Vlst;R2A6S19S2bS19R1S1eS32S3eVcv;A1A1A1A3S1dS1cR5R2A2S8S13S13S51Vh;A1M0S15G0S18S52Vh;Vmsz;A2G0A2A2A4A2F_;Fo;F_;F_;Fr;").
Proof.
  intros r ZE EX o Ho. destruct DJ as [HD]. unfold disj_chk in HD. apply andb_prop in HD as [HD4 _].
  pose proof (proj1 (forallb_forall _ _) HD4 o Ho) as HB.
  destruct HNUM as ((r0 & QS0) & _). pose proof (qs_chunk A (p, n) i ch r0 QS0) as (HP & MP & MS & IH & HTG & _).
  pose proof (qs_nums A (p, n) i ch r0 QS0) as (_ & _ & _ & _ & TG & _).
  pose proof ZE as [_ _ _ _ _ _ _ _ _ (B1 & B2 & B3 & B4 & B5 & B6 & B7)]. unfold PG in *.
  destruct (mrange_facts (sc_map_beg ch) (sc_map_size ch) ltac:(clear -B2; lia) B3 MP MS) as (M1 & M2 & M3 & M4 & M5).
  pose proof (Sh_in_band (sc_map_beg ch) ltac:(clear -B2 HTG TG MS; lia)) as SB1. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in SB1.
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep.Sh_lt_HSE (sc_map_beg ch + sc_map_size ch) ltac:(clear -B2 HTG TG MS; lia)) as SB2. unfold HIGH_SHADOW_END in SB2.
  apply (obj_off_sound r 4%nat o _ _ ZE EX ltac:(destruct l; unfold ZUXl; cbn; tauto) HB); unfold h, msz, zbE, zbX, zloS, zhiX, LOW_SHADOW_BEG; clear -M2 M3 M4 SB1 SB2; lia.
Qed.

Lemma HDISJ_hb : ltac2:(tb__ "0|0|
S1bS33VnW;VA;Vp;Vn;Vch;R1A6S3aVA;Vi;Vch;Vl;Vlst;R2A6S19S2bS19R1S1eS32S3fVcv;A1A1A1A3S1dS1cR5R2A2S8S13S13Vh;S15Vh;Vmsz;A2A4A2F_;Fo;F_;F_;Fr;").
Proof.
  intros r ZE EX o Ho. destruct DJ as [HD]. unfold disj_chk in HD. apply andb_prop in HD as [_ HD5].
  pose proof (proj1 (forallb_forall _ _) HD5 o Ho) as HB.
  apply (obj_off_sound r 5%nat o _ _ ZE EX ltac:(destruct l; unfold ZUXl; cbn; tauto) HB); unfold h, msz, zbE, zbX, zloS, zhiX; clear; lia.
Qed.
End Disj.

Lemma FCHs_below_SF : ltac2:(tb__ "0|0|
S5S40S42R2R1A2S0S6S2cS20S21S44A1S41R3A1A3S9A3F_;Fcf;FnW;").
Proof. intros nW cf SF. exact (proj1 (proj2 (proj2 (proj2 (proj2 (sF_parts nW cf SF)))))). Qed.
Section ZenvRW.
Variables (nW : nat) (A : AA) (rho1 : valuation) (p n : Z) (i : nat) (ch : sec_chunk).
Hypothesis HU : ltac2:(tb__ "0|0|
S0S13Vp;S15S15S29Vch;A1S4bA2Z800A2A3").
Hypothesis HN : 1 <= n.
Hypothesis HNB : ltac2:(tb__ "0|0|
S16S15Z1800S43Vn;A1A2S2aVch;A1A2").
Hypothesis HPIN : ltac2:(tb__ "0|4|
S1S0S31Q40M0A1M1S1aVrho1;P97A2S30G0S28S25VA;A1M2A1A2A3S1S0G1S1aVrho1;P98A2S30G0S26G2A1A2A3S1S0G1S1aVrho1;P9bA2S30G0S27G2A1A2A3S1S0G1S1aVrho1;PcA2S30G0Vp;A2A3S1S0G1S1aVrho1;P69A2S30G0S43Vn;A1M3A2A3S0G1S1aVrho1;P6aA2S30G0S17G3Z8A2A2A3A2A2A2A2A2").
Hypothesis HNUM : ltac2:(tb__ "0|0|
S3bVA;Vp;Vn;Vi;Vch;A5").
Hypothesis FCHB : ltac2:(tb__ "0|0|
S0S6S2cS20S21S44A1S41VnW;A1A3S9A3").
Hypothesis F1 : FCH1 nW rho1.
Lemma zenv_rw : ltac2:(tb__ "0|0|
S1bS14S53R1S4aA2S0S31Q40A1S1aR3R2A2S1aVrho1;R2A2A3F_;Fv;S14S0SdS31Q8A1A1S1fR3R1A2S1fVrho1;R1A2A3Fl0;S4cVA;R3A2S33VnW;VA;Vp;Vn;Vch;R4A6F_;F_;F_;Fr;").
Proof.
  intros r RW4 RLL Htop. destruct HNUM as ((r0 & QS0) & _). destruct HPIN as (P151 & P152 & P155 & P12 & P105 & P106).
  assert (AV : agree_vals NPRE rho1 r) by (split; [intros v Hv; symmetry; apply RW4; exact Hv | intros l0; symmetry; apply RLL]).
  assert (F4 : forall g, In g (FCHs nW) -> holds r g).
  { intros g Hg. apply (proj1 (holds_agree_vals NPRE rho1 r g AV (proj1 (forallb_forall _ _) FCHB g Hg))). exact (proj1 (Forall_forall _ _) F1 g Hg). }
  pose proof (qs_nums A (p, n) i ch r0 QS0) as (T0 & T1 & C0 & C1' & TG & _). pose proof (qs_chunk A (p, n) i ch r0 QS0) as (CM & _ & MS & IH & HT & _).
  pose proof (N8_facts n HN) as (N1 & N2 & N3 & N4). unfold PG, IMG_HI in *.
  constructor; try (rewrite RW4 by (unfold GW; lia); assumption).
  - exact Htop.
  - assert (D1 : holds r (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))) by (apply F4; unfold FCHs; apply in_or_app; right; left; reflexivity).
    cbn [holds eval branch_taken] in D1. unfold bv_lts in D1. apply negb_true_iff in D1. apply Z.ltb_ge in D1.
    change (bv_signed (Z_to_bv 64 (- free_depth))) with (- free_depth) in D1. exact D1.
  - apply Forall_forall. intros g Hg. apply F4. unfold FCHs. apply in_or_app. left. exact Hg.
  - lia.
  - repeat split; try assumption; lia.
Qed.
End ZenvRW.
End F0A_hbN_disj.

