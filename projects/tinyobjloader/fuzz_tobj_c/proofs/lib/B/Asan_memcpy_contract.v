(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "list"; "nat"; "nil"; "Some"; "option"; "bool"; "prod"; "true"; "app"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "iff"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "ACEIL"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "pow"; "modulo"; "opp"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "valuation"; "sobj"; "SVar"; "rw"; "SLit"; "SPUle"; "rm"; "SAlu"; "sprop_below"; "enc_bytes"; "holds"; "SPAlign"; "agree_below"; "eval"; "ss_facts"; "ss_next"; "ss_objs"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_setS"; "la_state"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "acell"; "mkACell"; "view"; "cell_ok"; "cells_ok"; "G0"; "RTC_A"; "bview"; "cells_footb"; "rtc_cells_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSplit"; "AXMerge"; "AXRebase"; "AXSelect"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memcpy.AMCAddr"; "mc_ret"; "mc_entry"; "musl_memcpy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_memcpy_contract"; "C"; "facts_W"; "PreW"; "XF"; "RTCL"; "s_ms"; "R_rtc"; "T0"; "T2"; "W2"; "T4"; "W1"; "rtc3_rng"; "N_rtc"; "PZ"; "T3"; "objs6"; "s_fin"; "T1"; "T5"; "XF_T2"; "XF_T4"; "XF_W1"; "carve_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "ageom"; "aa_geom"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "jpredA"; "smatchA"; "mat_blind"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "J_pure_pre"; "Kc_ok"; "L_memcpy"; "JL_pure"; "J_memcpy_pre"; "band_free"; "alloc_lawsA"; "client_addrA"; "memcpy_contractA"; "memcpy_contractA_ex"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memcpy"; "Pre_mc0"; "Posts_mc"; "P_amc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_memcpy_contract.Contract"; "Jcont"; "Jcore"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "rho_absorb"; "wsub"; "in_ranges"; "wsub_get"; "wsub_id_below"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Asan_memcpy_proof"; "clsZ";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "K_HIGH_MEM_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "O_real"; "O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "KHME"; "O_rtc2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "Zsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL MuslMemcpy ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2 AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nd.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Asan_memcpy_proof.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RegionAddr AMCAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ax_of (o : option axst) (d : axst) : axst := match o with Some a => a | None => d end.

Definition PreW : axst := Pre_memcpy mc_entry.
Definition facts_W : list sprop := Eval vm_compute in ss_facts (ax_S PreW).

Definition XF_W1 : list axform := ltac2:(tb__ "0|1|
S0S50S52U0M0S26N860A1A2S0S50S52G0S26N8b0A1A2S4S50A1A3A3").
Definition W1 : axst := Eval vm_compute in ax_of (apply_axforms PreW XF_W1) PreW.
Lemma W1_eq : ltac2:(tb__ "0|0|
SbS6S3bA1S51S5dS71A2S5S3bS66A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition N_rtc : list carve_spec := ltac2:(tb__ "0|e|
S0S8S8S8S21S1bA2M0S1bA2M1S2S8S8S1bS3A2M2S21A2M3A1M4A2M5S1G1G4S1G0S1bS1S21S1bS26Z0A1M6Zeed98M7A4Zeed9aA4S0G3S1G2S21S1S1bS3G7U1M8A4S26Z1A1M9A4S0G3S1G2S21S1S1bS3Zeed99G8A4G9A4S4G3A1MaA3A3A4S0G5S1G1G4S1G0S1bS1S21S1bG6Zeeda0MbA4Zeedb8A4S0G3S1G2S21S1S1bS3GbU8McA4S26SaeA1A4S0G3S1G2S21S1S1bS3Zeeda8GcA4G6A4S0G3S1G2S21S1S1bS3Zeedb0GcA4G6A4GaA3A3A3A4S0G5S1G1G4S1G0S1bS1S21S1bG6Ze6778MdA4Ze6780A4S0G3S1G2S21S1S1bS3GdGcA4S26S5aA1A4GaA3A4S4G5A1A3A3A3").
Definition R_rtc : list sobj := Eval vm_compute in map carve_obj N_rtc.
Lemma R_rtc_eq : ltac2:(tb__ "0|0|
SbS2S23A1S93Sa9S23Sa8S68A4S61A3"). Proof. reflexivity. Qed.
Lemma R_rtc_objs : ltac2:(tb__ "0|0|
SbS2S23A1S61S0S23SadS0S23SafS0S23SacS4S23A1A3A3A3A3"). Proof. reflexivity. Qed.
Definition carve_S (S : sstate) : sstate := ltac2:(tb__ "0|0|
S33S37VS;A1S38VS;A1S35VS;A1S34VS;A1S39VS;A1SaS23S32VS;A1S93Sa9S23Sa8S68A4A3S30VS;A1S73S36VS;A1A9").
Definition W2 : axst := Eval vm_compute in ax_setS W1 (carve_S (ax_S W1)).
Lemma W2_eq : ltac2:(tb__ "0|0|
SbS3bS3eS66S72S3cS66A1A1A2S64A3"). Proof. reflexivity. Qed.

Definition XF : list sprop := ltac2:(tb__ "0|9|
S0S20S27S29Sa4S29Sa5S24PcA1S24P35M0A1A3M1S24PeA1M2A3S24P36A1M3A2S0S20S27G1G3A2S0S20S27G2G3A2S0S20S2dG0Z3M4A2S0S20S27S29Sa4S29Sa5S24PdA1S24P37M5A1A3M6G2A3S24P38A1M7A2S0S20S27G6G7A2S0S20S27G2G7A2S0S20S2dG5G4A2S0S20S27S26S14S12Z900A2A1S24PaA1M8A2S0S20S27G8S26S17Z2Z3fA2A1A2S4S20A1A3A3A3A3A3A3A3A3A3A3").
Definition C : axst := Eval vm_compute in ax_with_facts W2 (XF ++ facts_W).
Lemma C_eq : ltac2:(tb__ "0|0|
SbS3bSb4S64SaS20S5eS5cA3A2S5bA3"). Proof. reflexivity. Qed.

Definition s_ms : wsub := Eval vm_compute in
  ([(15%positive, SVar 53); (16%positive, SVar 54); (17%positive, SAlu ALU_SUB (SVar 12) (SVar 53));
    (19%positive, SVar 55); (52%positive, SVar 56); (53%positive, SAlu ALU_SUB (SVar 13) (SVar 55)); (95%positive, SVar V_DEPTH)]
   ++ infer_sub 1 (ax_S C) (ax_S Pre_mc0)).
Lemma fr_ms : ltac2:(tb__ "0|1|
SbS6S2S23A1M0A1S85S5bS95S60A3S5G0S4S23A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_ms : ltac2:(tb__ "0|0|
SbS7S84S5bS95S60S4S23A1S93S3dS3bS3fS96A4A5S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T0 : axst := Eval vm_compute in import_postA s_ms Pre_mc0 P_amc C [].
Lemma T0_eq : ltac2:(tb__ "0|0|
SbS3bS86S60S95S97S5bS4S23A1A5S62A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T1 : axst := ltac2:(tb__ "0|0|
Sb2SaS20S5eS5cA3S62A2").

Definition XF_T2 : list axform := ltac2:(tb__ "0|0|
S0S50S55S0S3U2S0S3U1S0S3U0S0S3U3S0S3U4S0S3U8S0S3U9S0S3U5S0S3U6S0S3U7S4S3A1A3A3A3A3A3A3A3A3A3A3A1S4S50A1A3").
Definition T2 : axst := Eval vm_compute in ax_of (apply_axforms T1 XF_T2) T1.
Lemma T2_eq : ltac2:(tb__ "0|0|
SbS6S3bA1S51S6dS6fA2S5S3bS63A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition objs6 : list sobj := Eval vm_compute in firstn 7 (ss_objs (ax_S T2)).
Lemma T2_objs : ltac2:(tb__ "0|0|
SbS2S23A1S32S3cS63A1A1SaS23S6bS61A3A3"). Proof. reflexivity. Qed.

Definition T3 : axst := Eval vm_compute in ax_setS T2 (set_objs (ax_S T2) objs6).
Lemma T3_eq : ltac2:(tb__ "0|0|
SbS3bS3eS63Sb0S3cS63A1S6bA2A2S6aA3"). Proof. reflexivity. Qed.

Definition XF_T4 : list axform := ltac2:(tb__ "0|1|
S0S50S54U1A1S0S50S53U0A1M0S0S50G0S4S50A1A3A3A3").
Definition T4 : axst := Eval vm_compute in ax_of (apply_axforms T3 XF_T4) T3.
Lemma T4_eq : ltac2:(tb__ "0|0|
SbS6S3bA1S51S6aS70A2S5S3bS65A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T5 : axst := ltac2:(tb__ "0|1|
Sb3S65S0S8S21S21A2M0S1S21S21S24P35A1S24P36A1A4S0G0S1S21S21S24P37A1S24P38A1A4S4G0A1A3A3A2").

Definition s_fin : wsub := Eval vm_compute in infer_sub NF (ax_S T5) (ax_S (L_memcpy mc_ret)).
Lemma ent_fin : ltac2:(tb__ "0|0|
SbS7S41S6eS8aS58A1S6cA3S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Local Notation "'UU' r i" := (bv_unsigned (rw r i)) (at level 10, r at level 9, i at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Definition PZ (rho : valuation) : Prop := ltac2:(tb__ "0|12|
ScS13S1eQ40M0S25Vrho;P35A2A2M1S1eG0S25Vrho;PcA2A2M2A2ScS13S14G2S1eG0S25Vrho;PeA2A2M3A2S14G1S1eG0S25Vrho;P36A2A2M4A2M5A2ScS13G3S17Z2M6Z20A2A2ScS13SaaG1A2ScS13G5S1aS17G6Z2fA2M7Z8M8A2M9A2ScS13G4S17G6Z28A2MaA2ScS13Z1G3A2ScS13G1G9A2ScS13G2G7A2ScS13S1eG0S25Vrho;PaA2A2MbG7A2ScSbS1bS18GbZ10A2Z0McA3ScSbS1bS18G1G8A2GcA3ScS13S14S12Z900A2GbA2ScScS13S19GaA1Sb5S1eG0S25Vrho;PfA2A2A1MdA2S13GdN900A2A2ScS13S1eG0S25Vrho;P37A2A2MeS1eG0S25Vrho;PdA2A2MfA2ScS13S14GfG3A2S14GeS1eG0S25Vrho;P38A2A2M10A2M11A2ScS13SaaGeA2ScS13G11G9A2ScS13G10GaA2ScS13GeG9A2ScS13GfG7A2SbS1bS18GeG8A2GcA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").

Lemma facts_W_eq : ltac2:(tb__ "0|0|
SbS2S20A1S30S3cS5dA1A1S5cA3"). Proof. reflexivity. Qed.

Lemma PZ_of_pre : ltac2:(tb__ "0|0|
S7eS22S2S1dQ40A1A1S4cS7cS11R4S5dR3R2R1A6S69R4A1F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp [tr [ms md]] [(Hsm & HMI & Hwf & Hsh & Hhz) _].
  pose proof (smatch_facts_hold segs rho _ _ Hsm) as HF. cbn [ax_S PreW] in HF. rewrite facts_W_eq in HF || idtac.
  pose proof (urange (rw rho 53)) as R53. pose proof (urange (rw rho 54)) as R54. pose proof (urange (rw rho 12)) as R12.
  pose proof (urange (rw rho 14)) as R14. pose proof (urange (rw rho 10)) as R10. pose proof (urange (rw rho 15)) as R15.
  have_fact A1 HF (SPUle (SVar 53) (SVar 12)).
  have_fact A2 HF (SPUle (SAlu ALU_ADD (SVar 12) (SVar 14)) (SAlu ALU_ADD (SVar 53) (SVar 54))).
  have_fact A3 HF (SPUle (SVar 14) (SLit (2 ^ 32))).
  have_fact A4 HF (SPUle (SLit IMG_HI) (SVar 53)).
  have_fact A5 HF (SPUle (SAlu ALU_ADD (SVar 53) (SVar 54)) (SLit (2 ^ 47 - 8))).
  have_fact A6 HF (SPUle (SVar 54) (SLit (2 ^ 40))).
  have_fact A7 HF (SPUle (SLit 1) (SVar 14)).
  have_fact A8 HF (SPUle (SVar 53) (SLit (2 ^ 47 - 8))).
  have_fact A9 HF (SPUle (SVar 12) (SLit (2 ^ 47))).
  have_fact A10 HF (SPUle (SVar 10) (SLit (2 ^ 47))).
  have_fact A11 HF (SPAlign 10 4).
  have_fact A12 HF (SPUle (SLit 140735332483072) (SAlu ALU_ADD (SVar 10) (SVar V_DEPTH))).
  have_fact A13 HF (SPBranch BC_GE (SLit (- memx_depth)) (SVar V_DEPTH)).
  have_fact A14 HF (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40))).
  have_fact B1' HF (SPUle (SVar 55) (SVar 13)).
  have_fact B2 HF (SPUle (SAlu ALU_ADD (SVar 13) (SVar 14)) (SAlu ALU_ADD (SVar 55) (SVar 56))).
  have_fact B4 HF (SPUle (SLit IMG_HI) (SVar 55)).
  have_fact B5 HF (SPUle (SAlu ALU_ADD (SVar 55) (SVar 56)) (SLit (2 ^ 47 - 8))).
  have_fact B6 HF (SPUle (SVar 56) (SLit (2 ^ 40))).
  have_fact B8 HF (SPUle (SVar 55) (SLit (2 ^ 47 - 8))).
  have_fact B9 HF (SPUle (SVar 13) (SLit (2 ^ 47))).
  pose proof (urange (rw rho 55)) as R55. pose proof (urange (rw rho 56)) as R56. pose proof (urange (rw rho 13)) as R13.
  cbn [eval] in A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A12, B1', B2, B4, B5, B6, B8, B9.
  rewrite add_val in A2. rewrite add_val in A2. rewrite add_val in A5. rewrite add_val in A12.
  rewrite add_val in B2. rewrite add_val in B2. rewrite add_val in B5.
  rewrite !lit_unsigned in A3, A4, A5, A6, A7, A8, A9, A10, A12, B4, B5, B6, B8, B9.
  unfold IMG_HI in A4, B4.
  rewrite !Z.mod_small in A3, A4, A6, A7, A8, A9, A10, B4, B6, B8, B9 by lia.
  rewrite (Z.mod_small (2 ^ 47 - 8)) in A5, B5 by lia. rewrite (Z.mod_small 140735332483072) in A12 by lia.
  rewrite (Z.mod_small (UU rho 53 + UU rho 54)) in A2, A5 by lia.
  rewrite (Z.mod_small (UU rho 12 + UU rho 14)) in A2 by lia.
  rewrite (Z.mod_small (UU rho 55 + UU rho 56)) in B2, B5 by lia.
  rewrite (Z.mod_small (UU rho 13 + UU rho 14)) in B2 by lia.

  assert (AL : UU rho 53 mod 8 = 0 /\ UU rho 55 mod 8 = 0).
  { unfold shadow_ok in Hsh. cbn [ax_X PreW] in Hsh. apply Forall_cons_iff in Hsh as [[Hal _] Hsh]. apply Forall_inv in Hsh.
    destruct Hsh as (Hal' & _). split; [exact Hal | exact Hal']. }

  assert (SW : ACEIL + 2304 <= UU rho 10).
  { unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S PreW] in Hsm.
    destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
    apply Forall_inv in Hall. unfold obj_holds, obj_lo_of, obj_hi_of, stack_win in Hall. cbn [ob_base ob_lo ob_hi eval] in Hall.
    destruct Hall as ((B1 & _ & _ & _) & _). unfold soff in B1. cbn [eval] in B1. rewrite bv_signed_U in B1.
    cbn [holds branch_taken eval] in A13. unfold bv_lts in A13. rewrite !bv_signed_U in A13.
    rewrite lit_unsigned in A13. unfold memx_depth in A13.
    change ((- (2304)) mod 2 ^ 64) with 18446744073709549312 in A13.
    destruct (Z.ltb_spec (Zsigned 18446744073709549312) (Zsigned (UU rho V_DEPTH))) as [Hlt|Hge]; [discriminate A13|].
    destruct (Zsigned_spec 18446744073709549312) as [[X _]|[_ E0]]; [lia|]. rewrite E0 in Hge.
    unfold ACEIL. unfold V_DEPTH in *.
    destruct (Zsigned_spec (UU rho 15)) as [[X15 E15]|[X15 E15]]; rewrite E15 in Hge, B1.
    - lia.
    - replace ((UU rho 10 + UU rho 15) mod 2 ^ 64) with (UU rho 10 + UU rho 15 - 2 ^ 64) in A12; [lia|].
      symmetry. replace (UU rho 10 + UU rho 15) with ((UU rho 10 + UU rho 15 - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (SD : - 2 ^ 40 <= Zsigned (UU rho 15) <= - 2304).
  { unfold V_DEPTH in *.
    cbn [holds branch_taken eval] in A13, A14. unfold bv_lts in A13, A14. rewrite !bv_signed_U in A13, A14.
    rewrite !lit_unsigned in A13, A14. unfold memx_depth in A13.
    change ((- (2304)) mod 2 ^ 64) with 18446744073709549312 in A13.
    change ((- 2 ^ 40) mod 2 ^ 64) with 18446742974197923840 in A14.
    destruct (Z.ltb_spec (Zsigned 18446744073709549312) (Zsigned (UU rho 15))) as [Hlt|Hge]; [discriminate A13|].
    destruct (Z.ltb_spec (Zsigned (UU rho 15)) (Zsigned 18446742974197923840)) as [Hlt'|Hge']; [discriminate A14|].
    destruct (Zsigned_spec 18446744073709549312) as [[X _]|[_ E0]]; [lia|]. rewrite E0 in Hge.
    destruct (Zsigned_spec 18446742974197923840) as [[X _]|[_ E1]]; [lia|]. rewrite E1 in Hge'. lia. }
  destruct AL as [AL1 AL2]. unfold PZ, HSE, IMG_HI. repeat (split; [lia|]). lia.
Qed.

Lemma XF_holds : ltac2:(tb__ "0|0|
S22S69R1A1S92S20S2cR2A1S5eA3F_;Frho;").
Proof.
  intros rho HP. unfold PZ, HSE, IMG_HI, ACEIL in HP.
  destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & Q1 & Q2 & Q4 & Q5 & Q6 & Q8 & Q9 & Q12).
  pose proof (urange (rw rho 53)) as R53. pose proof (urange (rw rho 54)) as R54. pose proof (urange (rw rho 12)) as R12.
  pose proof (urange (rw rho 14)) as R14. pose proof (urange (rw rho 10)) as R10.
  pose proof (urange (rw rho 55)) as R55. pose proof (urange (rw rho 56)) as R56. pose proof (urange (rw rho 13)) as R13.
  assert (D : bv_unsigned (eval rho (SAlu ALU_SUB (SVar 12) (SVar 53))) = UU rho 12 - UU rho 53).
  { apply (U_sub2 rho (SVar 12) (SVar 53)); [reflexivity | reflexivity | lia]. }
  assert (D' : bv_unsigned (eval rho (SAlu ALU_SUB (SVar 13) (SVar 55))) = UU rho 13 - UU rho 55).
  { apply (U_sub2 rho (SVar 13) (SVar 55)); [reflexivity | reflexivity | lia]. }
  unfold XF. repeat apply Forall_cons; try apply Forall_nil; cbn [holds].
  - rewrite (U_add2 rho _ (SVar 14) (UU rho 12 - UU rho 53) (UU rho 14) D eq_refl) by lia. change (eval rho (SVar 54)) with (rw rho 54). lia.
  - rewrite D. change (eval rho (SVar 54)) with (rw rho 54). lia.
  - change (eval rho (SVar 54)) with (rw rho 54). change (eval rho (SVar 14)) with (rw rho 14). lia.
  - split; [lia | exact P12].
  - rewrite (U_add2 rho _ (SVar 14) (UU rho 13 - UU rho 55) (UU rho 14) D' eq_refl) by lia. change (eval rho (SVar 56)) with (rw rho 56). lia.
  - rewrite D'. change (eval rho (SVar 56)) with (rw rho 56). lia.
  - change (eval rho (SVar 56)) with (rw rho 56). change (eval rho (SVar 14)) with (rw rho 14). lia.
  - split; [lia | exact Q12].
  - rewrite (U_lit64 rho (ACEIL + 2304)) by (unfold ACEIL; lia). change (eval rho (SVar 10)) with (rw rho 10). unfold ACEIL. lia.
  - rewrite (U_lit64 rho (2 ^ 63)) by lia. change (eval rho (SVar 10)) with (rw rho 10). lia.
Qed.

Lemma wok_of_imageA : ltac2:(tb__ "0|1|
S1dQ40M0A1S6S1dQ8A1A1F_;S1bScS13Ze1000R1A2S15R1Z643000A2A2SbS7S75S11R3S1fG0R2A2A3S9A3F_;Fz;Fm;").
Proof.
  intros m z Hz. unfold wok_of. destruct (m (Z_to_bv 64 z)); [reflexivity|].
  unfold wseg_addr. rewrite u64_lit by lia.
  destruct (ImageFacts.byte_cond_A z Hz) as [_ (seg & b & Hf & Hw & _)].
  change ImageFacts.segsA with segs in Hf. rewrite Hf. exact Hw.
Qed.

Definition RTCL (G : ageom) : list acell := rtc_cells_img RTC_A G.
Lemma rtc_nth : ltac2:(tb__ "0|6|
S77ScSbS6S42A1M0S79S42S5fR1A1M1U12A3S5S42S43Zeed98U1M2Z1M3A3A2A3ScSbG0S79S42G1U13A3S5S42S43Zeed99G2G3A3A2A3ScSbG0S79S42G1U14A3S5S42S43Zeeda0U8M4SabA3A2A3ScSbG0S79S42G1U15A3S5S42S43Zeeda8G4Z0M5A3A2A3ScSbG0S79S42G1U16A3S5S42S43Zeedb0G4G5A3A2A3SbG0S79S42G1G2A3S5S42S43Ze6778G4S5aA3A2A3A2A2A2A2A2FG;").
Proof. intros G. repeat split; reflexivity. Qed.

Lemma cell_of : ltac2:(tb__ "0|0|
S49S77S3S42S46R4S5fR3A1A2SbS6S42A1S79S42S5fR4A1R3A3S5S42R2A2A3S45R6R3A2F_;F_;Fc;Fn;FG;Fm;").
Proof. intros m G n c H Hn. exact (proj1 (Forall_forall _ _) H c (nth_error_In _ _ Hn)). Qed.

Lemma cell_rd : ltac2:(tb__ "0|3|
S1dQ40M0A1S6S1dQ8A1M1A1M2F_;S1bS3S1bS1bS45S44S11R5A2S43R4R3R2A3A2ScS13R5R2A2S15R2S14R5S16R4A1A2A2A2S13Z0R6A2S13S14R7S16R6A1A2S17Z2Z40A2A2SeG1G1SbG2S74S11RaS1fG0R6A2A3S5G1R1A2A3Ly;A2F_;F_;F_;F_;Fz;Fv;Fk;Fa;Fm;").
Proof.
  intros m a k v z Hc Hz Ha1 Ha2. specialize (Hc (Z.to_nat (z - a)) ltac:(cbn [c_w]; lia)). cbn [c_addr c_w c_val] in Hc.
  rewrite view_in in Hc by lia. replace (a + Z.of_nat (Z.to_nat (z - a))) with z in Hc by lia. eexists. exact Hc.
Qed.

Lemma cell_civ : ltac2:(tb__ "0|5|
S22S1dQ40M0A1S6S1dQ8M1A1M2A1M3F_;S1bS3S1bS45S44S11R4A2S43R3R2R1A3A2S13Z0M4R4A2S13S14R5S16R4A1A2S17Z2Z40A2A2S3S9aR1R6A2SbG3S74S11R9S1fG0S14S14G4R8A2S16R2A1A2A2A3S5G2S94G2R2S2bR7S2fRaS26R6A1A2A2S1fG1G4A2A4A2A3F_;Fj;F_;F_;F_;Fv;Fk;Fa;Fm;Frho;").
Proof.
  intros rho m a k v Hc Ha1 Ha2 j Hj. specialize (Hc j Hj). cbn [c_addr c_w c_val] in Hc. rewrite view_in in Hc by lia.
  rewrite Z.add_0_l. cbn [eval]. exact Hc.
Qed.

Lemma swf_W2 : ltac2:(tb__ "0|0|
SbS7S3aS3cS64A1A1S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XF_below : ltac2:(tb__ "0|0|
SbS7S7aS20S2aS31S3cS64A1A1A1SaS20S5eS5cA3A3S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma SPA_C_of_pre : ltac2:(tb__ "0|0|
S7eS22S2S1dQ40A1A1S4cS77S46S44S11S28R4A1A2S5fR1A1A2S7cS11R6S5dR5R4R3A6S7cS11R7S5bR6R5R4A6F_;F_;FG;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w G HR HS. pose proof (PZ_of_pre J rho tp w HS) as HP.
  pose proof (SPA_axforms segs J XF_W1 rho PreW W1 tp w W1_eq HS) as HS1.
  pose proof HP as HP'. unfold PZ, HSE, IMG_HI, ACEIL in HP'.
  destruct HP' as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & Q1 & Q2 & Q4 & Q5 & Q6 & Q8 & Q9 & Q12).
  pose proof (urange (rw rho 10)) as R10. pose proof (urange (rw rho 12)) as R12. pose proof (urange (rw rho 14)) as R14. pose proof (urange (rw rho 15)) as R15. pose proof (urange (rw rho 13)) as R13.
  destruct (rtc_nth G) as (N18 & N19 & N20 & N21 & N22 & N2).
  pose proof (cell_of _ G _ _ HR N18) as C18. pose proof (cell_of _ G _ _ HR N19) as C19. pose proof (cell_of _ G _ _ HR N20) as C20.
  pose proof (cell_of _ G _ _ HR N21) as C21. pose proof (cell_of _ G _ _ HR N22) as C22. pose proof (cell_of _ G _ _ HR N2) as C2.
  assert (HS2 : SPA segs J W2 rho tp w).
  { rewrite <- W2_eq. unfold carve_S.
    apply (SPA_carve_list segs J rho W1 tp w N_rtc NF HS1 swf_W2 ltac:(apply Pos.le_refl)).
    -
      unfold N_rtc. repeat apply Forall_cons; try apply Forall_nil; cbv beta iota zeta; cbn [eval];
        rewrite !lit_unsigned; rewrite !(Z.mod_small 0) by lia.
      + split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
        split; [intros off Hoff; split; [apply wok_of_imageA; lia|];
                destruct (Z_lt_ge_dec off 0xeed99); [eapply (cell_rd _ _ _ _ _ C18); cbn; lia | eapply (cell_rd _ _ _ _ _ C19); cbn; lia]|].
        split; [unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; intros j Hj;
                [apply (cell_civ rho _ _ _ _ C18); cbn; lia | apply (cell_civ rho _ _ _ _ C19); cbn; lia]|].
        intros rr y j Hin Hy Hj. cbn [ax_base W1 eval]. rewrite lit_unsigned. unfold SHB. intros X. pose proof (urange (eval rho (fst rr))).
        pose proof (Z.div_mod (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)).
        change (2147450880 mod 2 ^ 64) with 2147450880 in *. assert (0 <= y / 8) by (apply Z.div_pos; lia). lia.
      + split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
        split; [intros off Hoff; split; [apply wok_of_imageA; lia|];
                destruct (Z_lt_ge_dec off 0xeeda8); [eapply (cell_rd _ _ _ _ _ C20); cbn; lia|];
                destruct (Z_lt_ge_dec off 0xeedb0); [eapply (cell_rd _ _ _ _ _ C21); cbn; lia | eapply (cell_rd _ _ _ _ _ C22); cbn; lia]|].
        split; [unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; intros j Hj;
                [apply (cell_civ rho _ _ _ _ C20); cbn; lia | apply (cell_civ rho _ _ _ _ C21); cbn; lia | apply (cell_civ rho _ _ _ _ C22); cbn; lia]|].
        intros rr y j Hin Hy Hj. cbn [ax_base W1 eval]. rewrite lit_unsigned. unfold SHB. intros X. pose proof (urange (eval rho (fst rr))).
        pose proof (Z.div_mod (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)).
        change (2147450880 mod 2 ^ 64) with 2147450880 in *. assert (0 <= y / 8) by (apply Z.div_pos; lia). lia.
      + split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
        split; [intros off Hoff; split; [apply wok_of_imageA; lia | eapply (cell_rd _ _ _ _ _ C2); cbn; lia]|].
        split; [unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; intros j Hj; apply (cell_civ rho _ _ _ _ C2); cbn; lia|].
        intros rr y j Hin Hy Hj. cbn [ax_base W1 eval]. rewrite lit_unsigned. unfold SHB. intros X. pose proof (urange (eval rho (fst rr))).
        pose proof (Z.div_mod (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)).
        change (2147450880 mod 2 ^ 64) with 2147450880 in *. assert (0 <= y / 8) by (apply Z.div_pos; lia). lia.
    -
      destruct HS1 as [(Hsm1 & _) _]. unfold virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm1.
      destruct Hsm1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
      cbn [ax_S W1 ss_objs] in Hall |- *.
      apply Forall_inv in Hall. unfold obj_holds, obj_lo_of, obj_hi_of in Hall. cbn [ob_base ob_lo ob_hi eval] in Hall.
      destruct Hall as ((B1 & _ & _ & _) & _).
      unfold soff in B1. cbn [eval] in B1. rewrite bv_signed_U in B1.
      pose proof (Zsigned_spec (UU rho 15)) as Z15. pose proof (Zsigned_spec (UU rho 14)) as Z14.
      unfold N_rtc. cbn [map carve_obj carved lit_cells].
      repeat apply Forall_cons; try apply Forall_nil;
        unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of, carved; cbn [ob_base ob_lo ob_hi fst snd];
        rewrite ?soff_lit_small by lia; unfold soff; cbn [eval]; rewrite ?bv_signed_U; rewrite ?lit_unsigned; rewrite ?(Z.mod_small 0) by lia;
        unfold V_DEPTH in *; lia.
    -
      unfold N_rtc. cbn [map carve_obj pairwise_disjoint].
      repeat split; repeat apply Forall_cons; try apply Forall_nil;
        unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of, carved; cbn [ob_base ob_lo ob_hi fst snd];
        rewrite ?soff_lit_small by lia; cbn [eval]; rewrite ?lit_unsigned; rewrite ?(Z.mod_small 0) by lia; lia. }
  rewrite <- C_eq. apply SPA_refacts; [exact HS2 | exact XF_below |].
  intros _. apply Forall_app. split; [apply XF_holds; exact HP|].
  rewrite <- facts_W_eq. eapply SPA_facts_hold. exact HS.
Qed.

Lemma triple_pre : ltac2:(tb__ "0|1|
S4cOF_;S4dOS4dS4cR4R1A1R4F_;Fw;R3S4fS11R6R5R3A4M0F_;G0F_;F_;FQ;FX;FP;Fok;").
Proof. intros ok P X Q HX H n Hg w Hw. exact (H (HX w Hw) n Hg w Hw). Qed.
Lemma etriple_pre : ltac2:(tb__ "0|2|
S4cOF_;M0OG0S4cR4R1A1R4F_;Fw;R3S4eS11R5R3A3M1F_;G1F_;F_;FQ;FX;FP;").
Proof. intros P X Q HX H w Hw. exact (H (HX w Hw) w Hw). Qed.
Lemma rm_rho_sub : ltac2:(tb__ "0|0|
S22S9eSbS1dQ40A1S6S1dQ8A1A1F_;S28S9cR2R1A2A1S28R2A1A3Fs;Frho;"). Proof. reflexivity. Qed.
Lemma rw_sub : ltac2:(tb__ "0|0|
S22S9eS1cSbS1dQ40A1S25S9cR3R2A2R1A2S2fR3Sa0R2R1A2A2A3Fi;Fs;Frho;"). Proof. reflexivity. Qed.
Lemma rm_absorb_nil : ltac2:(tb__ "0|0|
S22S9bSbS1dQ40A1S6S1dQ8A1A1F_;S28S9dR2S4S23A1R1A3A1S28R2A1A3Fm;Frho;").
Proof.
  intros rho m. apply functional_extensionality. intros a. unfold rho_absorb. cbn [rm].
  destruct (in_ranges_dec rho [] a) as [(o & [] & _)|]; reflexivity.
Qed.
Lemma Forall_holds_agree : ltac2:(tb__ "0|1|
S1cS22S22S2S20A1S2eR4R3R2A3SbS7S7aS20S2aR5A1R2A3S9A3S92S20S2cR5A1M0R3A3S92S20G0R4A3F_;F_;F_;FF;Frho';Frho;Fn;").
Proof.
  intros n rho rho' F Hag Hb HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree n rho rho' p Hag (proj1 (forallb_forall _ _) Hb p Hp))). exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.
Lemma Kc_mat_blind : ltac2:(tb__ "0|0|
S87S89R1A1S80R2A1F_;FKc;").
Proof. intros Kc HK tr md l p. split; intros H; eapply Kc_ok_mat; eauto. Qed.

Definition rtc3_rng (a : Z) : Prop := ltac2:(tb__ "0|0|
SdScS13Zeed98Va;A2S15Va;Zeed9aA2A2SdScS13Zeeda0Va;A2S15Va;Zeedb8A2A2ScS13Ze6778Va;A2S15Va;Ze6780A2A2A2A2").
Lemma rtc3_footb : ltac2:(tb__ "0|0|
S1bS67R1A1SbS7S4aS4bS48S47A2R2A2S9A3F_;Fa;").
Proof.
  intros a Ha. unfold cells_footb.
  assert (E : forall c, In c (rtc_cells_img RTC_A G0) -> in_cellb a c = true -> existsb (in_cellb a) (rtc_cells_img RTC_A G0) = true).
  { intros c Hc Hb. apply (proj2 (existsb_exists _ _)). exists c. auto. }
  destruct Ha as [H|[H|H]].
  - destruct (Z_lt_ge_dec a 0xeed99).
    + apply (E (mkACell 0xeed98 1 1)); [cbn; tauto | unfold in_cellb; cbn [c_addr c_w]; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia].
    + apply (E (mkACell 0xeed99 1 1)); [cbn; tauto | unfold in_cellb; cbn [c_addr c_w]; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia].
  - destruct (Z_lt_ge_dec a 0xeeda8); [|destruct (Z_lt_ge_dec a 0xeedb0)].
    + apply (E (mkACell 0xeeda0 8 K_HIGH_MEM_END)); [cbn; tauto | unfold in_cellb; cbn [c_addr c_w]; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia].
    + apply (E (mkACell 0xeeda8 8 0)); [cbn; tauto | unfold in_cellb; cbn [c_addr c_w]; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia].
    + apply (E (mkACell 0xeedb0 8 0)); [cbn; tauto | unfold in_cellb; cbn [c_addr c_w]; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia].
  - apply (E (mkACell 0xe6778 8 musl_memcpy)); [cbn; tauto | unfold in_cellb; cbn [c_addr c_w]; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia].
Qed.

Lemma T0_below : ltac2:(tb__ "0|0|
SbS7S7aS20S2aS31S3cS62A1A1A1SaS20S5eS5cA3A3S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XFW_belowNF : ltac2:(tb__ "0|0|
SbS7S7aS20S2aS73A1SaS20S5eS5cA3A3S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_fin : ltac2:(tb__ "0|0|
SbS7Sa1S6cS73A2S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_T4 : ltac2:(tb__ "0|3|
SbS2S8S21S21A2M0A1S40S65A1S0G0S1S21S21S24P35A1S24P36A1A4M1S0G0S1S21S21S24P37A1S24P38A1A4M2S0G0G1S0G0G2S4G0A1A3A3A3A3A3"). Proof. reflexivity. Qed.

Lemma in_ranges_R : ltac2:(tb__ "0|1|
S22S1dQ40M0A1SfS9fR2S61R1A3S67S1eG0R1A2A1A2Fa;Fr;").
Proof.
  intros r a. unfold in_ranges, R_rtc, rtc3_rng.
  assert (RG : forall lo hi cs, - 2 ^ 63 <= lo < 2 ^ 63 -> - 2 ^ 63 <= hi < 2 ^ 63 ->
            obj_range r (mkObj (SLit 0) (SLit lo) (SLit hi) cs DUnknown) = (lo, hi)).
  { intros lo hi cs Hlo Hhi. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval].
    rewrite !soff_lit_small by lia. rewrite lit_unsigned. reflexivity. }
  split.
  - intros (o & Hin & Hr). destruct Hin as [<-|[<-|[<-|[]]]]; rewrite RG in Hr by lia; cbn [fst snd] in Hr; lia.
  - intros [H|[H|H]].
    + eexists. split; [left; reflexivity|]. rewrite RG by lia. cbn [fst snd]. lia.
    + eexists. split; [right; left; reflexivity|]. rewrite RG by lia. cbn [fst snd]. lia.
    + eexists. split; [right; right; left; reflexivity|]. rewrite RG by lia. cbn [fst snd]. lia.
Qed.

Lemma rd_cell_eq : ltac2:(tb__ "0|9|
S1dQ40M0A1M1S6S1dQ8M2A1M3A1M4F_;M5G5S1bS3G1S1bS3S9aR1R4A2SbG4S74S11R8S1fG0S14R6S16R2A1M6A2A2A3S5G3S94G3R2S2bR5R4A2S1fG2Z0A2M7A4A2A3F_;Fj;S3S9aR1R5A2SbG4S74S11R8S1fG0S14R7G6A2A2A3S5G3S94G3R2S2bR6R5A2G7A4A2A3F_;Fj;ScS13R6R3A2S15R3S14R6S16R5A1A2A2A2SbG4S74S11R9S1fG0R4A2M8A3S74S11R8G8A3A3F_;F_;F_;Fz;Fv;Fk;Fa0;Fm2;Fm1;").
Proof.
  intros m1 m2 a0 k v z H1 H2 Hz.
  replace z with (a0 + Z.of_nat (Z.to_nat (z - a0))) by lia.
  rewrite (H1 (Z.to_nat (z - a0))) by lia. rewrite (H2 (Z.to_nat (z - a0))) by lia. reflexivity.
Qed.

Section Contract.
Variable AInvA : ltac2:(tb__ "0|0|
S76S22S2S1dQ40A1A1S56OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S8eS11VAInvA;VCST;A3").

Definition law_view_stmt : Prop := ltac2:(tb__ "0|1|
S76S22S22S2S1dQ40A1M0A1S56VAInvA;R5R4R2R1A4G0SbS6S1dQ8A1A1S74S11S28R5A1R1A3S74S11S28R6A1R1A3A3Fa;VAInvA;R7R5R4R3A4F_;F_;Fmd;Ftp;Frho';Frho;FA;").
Hypothesis HLV : law_view_stmt.
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Definition Jcore (A : AA) (Kc : KcA) (tp0 : list word) : jpredA := ltac2:(tb__ "0|1|
S22S2S1dQ40A1A1M0S2S57A1S56ScS88VAInvA;VA;VKc;R4R3R2R1A7ScScSa6R4PfP10A3Sa6R4P13P34A3A2SbG0R3Vtp0;A3A2A2Lmd;Ltr;Lt;Lr;").
Definition Jcont (A : AA) (Kc : KcA) (tp0 : list word) : jpredA := ltac2:(tb__ "0|1|
S22S2S1dQ40A1A1M0S2S57A1S56ScS88VAInvA;VA;VKc;R4R3R2R1A7SbG0R3Vtp0;A3A2Lmd;Ltr;Lt;Lr;").

Lemma Jcore_stable : ltac2:(tb__ "0|0|
S76S87S2S1dQ40A1A1S89R2A1S81S11S73S99R4R3R2A3A3F_;Ftp0;FKc;FA;").
Proof.
  intros A Kc tp0 HKc rho rho' tp tr md md' Hag Hme ((HA & HK & Htp & Htv) & Hcls & ->).
  pose proof Hag as (Hrw & _ & Hrm).
  split; [split; [|split; [|split]]|split; [|reflexivity]].
  - eapply (law_mat _ _ _ ALA); [|exact Hme]. eapply (law_vars _ _ _ ALA); [exact HA|].
    apply functional_extensionality. intros a. symmetry. apply Hrm.
  - eapply mat_blind_equiv; [apply Kc_mat_blind; exact HKc | exact Hme | exact HK].
  - unfold tp_ok in *. rewrite <- (Hrw 24%positive) by reflexivity. exact Htp.
  - unfold top_var in *. rewrite <- (Hrw _) by reflexivity. exact Htv.
  - unfold clsZ in *. rewrite <- (Hrw 15%positive), <- (Hrw 16%positive), <- (Hrw 19%positive), <- (Hrw 52%positive) by reflexivity. exact Hcls.
Qed.

Lemma Jcore_okf : ltac2:(tb__ "0|0|
S4cOF_;S76S87S2S1dQ40A1A1S7dS11R4S88VAInvA;R3R2A3A3S7dS11R5S99R4R3R2A3A3F_;Ftp0;FKc;FA;Fok;").
Proof. intros ok A Kc tp0 H rho tp tr ms md msv' [HJ _]. eapply H. exact HJ. Qed.

Lemma client_not_rtc3 : ltac2:(tb__ "0|0|
S76S22S2S1dQ40A1A1S56S1bVAInvA;R5R4R3R2A4S8fVCST;R6R2A3S10S67R3A1A1F_;F_;Fa;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md a HA Hcl Hr.
  destruct (law_blocks _ _ _ ALA A rho tp md HA) as (_ & HB & HFr). pose proof (topG_range (aa_geom A)) as TG. unfold HIGH_SHADOW_END, IMG_HI in *.
  destruct Hcl as [[S|[L|[F|C]]]|FL].
  - unfold rtc3_rng in Hr. lia.
  - destruct L as (b & n & Hbn & Hx). destruct (HB b n Hbn) as (B1 & B2 & B3 & B4 & B5). unfold rtc3_rng in Hr. lia.
  - destruct F as (f & s & Hfs & Hx). destruct (HFr f s Hfs) as (F1 & F2 & F3 & F4 & _). unfold rtc3_rng in Hr. lia.
  - destruct (HCST a C) as [_ Hf]. rewrite (rtc3_footb a Hr) in Hf. discriminate.
  - destruct FL as (fs & Hfs & ->). destruct fs as [f s]. destruct (HFr f s Hfs) as (F1 & F2 & F3 & F4 & F5 & F6 & _). unfold rtc3_rng in Hr. lia.
Qed.

Section Inst.
Variable ok : world -> Prop.
Variable A : AA. Variable Kc : KcA.
Variables (rho : valuation) (tp : list word).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HP : PZ rho.
Hypothesis HR : ltac2:(tb__ "0|0|
S46S44S11S28Vrho;A1A2S5fS78VA;A1A1A2").

Hypothesis HBF1 : ltac2:(tb__ "0|1|
S8dS1eQ40M0S25Vrho;P35A2A2S1eG0S25Vrho;P36A2A2A2").
Hypothesis HBF2 : ltac2:(tb__ "0|1|
S8dS1eQ40M0S25Vrho;P37A2A2S1eG0S25Vrho;P38A2A2A2").

Lemma J_in : ltac2:(tb__ "0|1|
S2S57A1M0S9bS56S7fS11Vrho;Vtp;S5bS1G0Sa2R3Sa3R2R1A2A4A5S98VA;VKc;Vtp;Vrho;Vtp;R4R2A7S99VA;VKc;Vtp;S9cS9dVrho;S4S23A1Sa7R3Vtp;R4A3A3S60A2Vtp;R5R3A7F_;F_;Fmd;Fms;Ftr;").
Proof.
  intros tr ms md _ [(HA & HK & Htp & Htv) _].
  split; [split; [|split; [|split]]|split; [|reflexivity]].
  - eapply (law_vars _ _ _ ALA); [exact HA|]. rewrite rm_rho_sub. apply rm_absorb_nil.
  - exact HK.
  - unfold tp_ok in *. rewrite rw_sub. replace (wsub_get s_ms 24) with (SVar 24) by reflexivity. rewrite eval_absorb. exact Htp.
  - unfold top_var in *. rewrite rw_sub. replace (wsub_get s_ms V_TOP) with (SVar V_TOP) by reflexivity. rewrite eval_absorb. exact Htv.
  - unfold clsZ. rewrite !rw_sub. replace (wsub_get s_ms 15) with (SVar 53) by reflexivity.
    replace (wsub_get s_ms 16) with (SVar 54) by reflexivity. replace (wsub_get s_ms 19) with (SVar 55) by reflexivity.
    replace (wsub_get s_ms 52) with (SVar 56) by reflexivity. rewrite !eval_absorb. cbn [eval].
    unfold band_free, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in HBF1, HBF2. unfold HSE, SHB. split; lia.
Qed.

Lemma J_out : ltac2:(tb__ "0|1|
S3dS22S22S2S1dQ40A1A1S2S57A1M0S9bS56G0S56S7bS3dR9S96A3S7fS11Vrho;Vtp;S5bS1G0Sa2R6Sa3R5R4A2A4A5S98VA;VKc;Vtp;Vrho;Vtp;R7R5A7Sb1Vrho;Sa7R6Vtp;R7A3S4S23A1S60S3cS95A1S3cS5bA1S3cS3fRcA1A1RbRaA9S99VA;VKc;Vtp;RbRaR6R5A7S98VA;VKc;Vtp;RdRbR7R6A7F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FtpL;FrhoL;Frho';FL;").
Proof.
  intros L rho' rhoL tpL tr ms md tr' md' _ _ [(HA & HK & Htp & Htv) _] (Hag & HagL & _) ((HA' & HK' & Htp' & _) & _ & ->).
  pose proof Hag as (Hrw & _ & Hrm). pose proof HagL as (_ & _ & HrmL).
  split; [split; [|split; [|split]]|reflexivity].
  - eapply (law_vars _ _ _ ALA); [exact HA'|]. apply functional_extensionality. intros a.
    rewrite <- (Hrm a), <- (HrmL a). rewrite rm_rho_sub, rm_absorb_nil. reflexivity.
  - exact HK'.
  - unfold tp_ok in *. rewrite <- (Hrw 24%positive) by reflexivity. exact Htp.
  - unfold top_var in *. rewrite <- (Hrw _) by reflexivity. exact Htv.
Qed.
Hypothesis HFW : ltac2:(tb__ "0|0|
S92S20S2cVrho;A1S5cA3").

Lemma cont_post : ltac2:(tb__ "0|1|
S22S2S1dQ40A1A1S4cS2eS73Vrho;R3A3S7cS11S98VA;VKc;Vtp;A3S62R4R3R2A6S83S11S73Vrho;Vtp;S0S8S3bS82A2M0S1S3bS82S8aS58A1S8bVAInvA;VCST;VXGL;VA;VKc;A5A4S4G0A1A3R3A6F_;F_;Fw;FtpL;Frho';").
Proof.
  intros rho' tpL [tr [ms md]] Hag HS0.
  pose proof (proj2 HS0) as HJ0. cbn [w_tr w_cfg cfg_model fst snd] in HJ0. destruct HJ0 as [_ EtpL]. subst tpL.
  pose proof Hag as (Hrw & Hrl & Hrm).

  assert (HS1 : SPA segs (Jcont A Kc tp) T1 rho' tp (tr, mkCfg ms md)).
  { split; [|exact (proj2 HS0)]. unfold T1. apply smatchA_add_facts; [exact (proj1 HS0) | | exact T0_below].
    apply (Forall_holds_agree NF rho rho'); [exact Hag | exact XFW_belowNF |].
    apply Forall_app. split; [apply XF_holds; exact HP | exact HFW]. }
  pose proof (SPA_axforms segs _ XF_T2 rho' T1 T2 tp _ T2_eq HS1) as HS2.

  pose proof (SPA_unobj segs (Jcont A Kc tp) rho' T2 objs6 R_rtc tp tr ms md T2_objs HS2) as HS3. cbn zeta in HS3.
  set (rho'' := rho_absorb rho' R_rtc (vms md tp ms)) in HS3.
  assert (RMout : forall a, ~ rtc3_rng (bv_unsigned a) -> rm rho'' a = rm rho a).
  { intros a Ha. unfold rho''. rewrite rm_absorb_out; [symmetry; apply Hrm|]. intros Hi. apply Ha. apply (in_ranges_R rho'). exact Hi. }
  assert (HJ3 : Jcont A Kc tp rho' tp tr md -> Jcont A Kc tp rho'' tp tr md).
  { intros [(HA & HK & Htp & Htv) _]. split; [split; [|split; [|split]]|reflexivity].
    - apply (HLV A rho' rho'' tp md HA). intros a.
      destruct (in_ranges_dec rho' R_rtc a) as [Hin|Hout].
      +
        pose proof (proj1 (proj1 HS2)) as Hsm2. unfold virt in Hsm2. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm2.
        assert (RR : forall a', rd_of segs (rm rho') a' = rd_of segs (rm rho) a') by (intros a'; unfold rd_of; rewrite <- (Hrm a'); reflexivity).
        rewrite RR. apply (in_ranges_R rho') in Hin.
        destruct (rtc_nth (aa_geom A)) as (N18 & N19 & N20 & N21 & N22 & N2).
        pose proof (fun n c Hn => cell_of _ (aa_geom A) n c HR Hn) as CO.
        assert (AC : forall lo hi cs, In (carved (SLit 0) lo hi cs) R_rtc -> - 2 ^ 63 <= lo -> lo <= hi -> hi < 2 ^ 63 -> cells_inside lo hi cs ->
                  cells_in_view rho'' (rd_of segs (rm rho'')) 0 cs).
        { intros lo hi cs Hin' H1 H2 H3 H4.
          pose proof (absorb_carved_cells segs rho' (ax_S T2) tr (vms md tp ms) (vmd md) objs6 R_rtc (SLit 0) lo hi cs Hsm2 T2_objs Hin' H1 H2 H3 H4) as [X _].
          cbn [eval] in X. rewrite lit_unsigned in X. exact X. }
        rewrite <- (Z_to_bv_bv_unsigned 64 a).
        destruct Hin as [H|[H|H]].
        * pose proof (AC 0xeed98 0xeed9a [(0xeed98, 1%nat, SLit 1); (0xeed99, 1%nat, SLit 1)] ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)) as CV.
          apply Forall_cons_iff in CV as [CV1 CV]. apply Forall_cons_iff in CV as [CV2 _]. cbn [eval] in CV1, CV2.
          destruct (Z_lt_ge_dec (bv_unsigned a) 0xeed99).
          -- apply (rd_cell_eq _ _ 0xeed98 1 (Z_to_bv 64 1)); [intros j Hj; rewrite <- (CV1 j Hj); f_equal; f_equal; lia | | lia].
             intros j Hj. pose proof (CO 18%nat _ N18 j Hj) as Y. cbn [c_addr c_w c_val] in Y. rewrite view_in in Y by lia. exact Y.
          -- apply (rd_cell_eq _ _ 0xeed99 1 (Z_to_bv 64 1)); [intros j Hj; rewrite <- (CV2 j Hj); f_equal; f_equal; lia | | lia].
             intros j Hj. pose proof (CO 19%nat _ N19 j Hj) as Y. cbn [c_addr c_w c_val] in Y. rewrite view_in in Y by lia. exact Y.
        * pose proof (AC 0xeeda0 0xeedb8 [(0xeeda0, 8%nat, SLit KHME); (0xeeda8, 8%nat, SLit 0); (0xeedb0, 8%nat, SLit 0)]
                        ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)) as CV.
          apply Forall_cons_iff in CV as [CV1 CV]. apply Forall_cons_iff in CV as [CV2 CV]. apply Forall_cons_iff in CV as [CV3 _]. cbn [eval] in CV1, CV2, CV3.
          destruct (Z_lt_ge_dec (bv_unsigned a) 0xeeda8); [|destruct (Z_lt_ge_dec (bv_unsigned a) 0xeedb0)].
          -- apply (rd_cell_eq _ _ 0xeeda0 8 (Z_to_bv 64 KHME)); [intros j Hj; rewrite <- (CV1 j Hj); f_equal; f_equal; lia | | lia].
             intros j Hj. pose proof (CO 20%nat _ N20 j Hj) as Y. cbn [c_addr c_w c_val] in Y. rewrite view_in in Y by lia. exact Y.
          -- apply (rd_cell_eq _ _ 0xeeda8 8 (Z_to_bv 64 0)); [intros j Hj; rewrite <- (CV2 j Hj); f_equal; f_equal; lia | | lia].
             intros j Hj. pose proof (CO 21%nat _ N21 j Hj) as Y. cbn [c_addr c_w c_val] in Y. rewrite view_in in Y by lia. exact Y.
          -- apply (rd_cell_eq _ _ 0xeedb0 8 (Z_to_bv 64 0)); [intros j Hj; rewrite <- (CV3 j Hj); f_equal; f_equal; lia | | lia].
             intros j Hj. pose proof (CO 22%nat _ N22 j Hj) as Y. cbn [c_addr c_w c_val] in Y. rewrite view_in in Y by lia. exact Y.
        * pose proof (AC 0xe6778 0xe6780 [(0xe6778, 8%nat, SLit musl_memcpy)] ltac:(right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)) as CV.
          apply Forall_cons_iff in CV as [CV1 _]. cbn [eval] in CV1.
          apply (rd_cell_eq _ _ 0xe6778 8 (Z_to_bv 64 musl_memcpy)); [intros j Hj; rewrite <- (CV1 j Hj); f_equal; f_equal; lia | | lia].
          intros j Hj. pose proof (CO 1%nat _ N2 j Hj) as Y. cbn [c_addr c_w c_val] in Y. rewrite view_in in Y by lia. exact Y.
      + unfold rd_of. unfold rho''. rewrite (rm_absorb_out rho' R_rtc _ a Hout). reflexivity.
    - exact HK.
    - exact Htp.
    - exact Htv. }
  specialize (HS3 HJ3). rewrite T3_eq in HS3.
  pose proof (SPA_axforms segs _ XF_T4 rho'' T3 T4 tp _ T4_eq HS3) as HS4.
  assert (HS5 : SPA segs (Jcont A Kc tp) T5 rho'' tp (tr, mkCfg ms md)).
  { unfold T5. apply SPA_x_sub; [|exact HS4]. rewrite X_T4. intros r [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity]. }
  destruct HS5 as [Hsm5 HJ5].
  pose proof (smatchA_entails segs T5 (L_memcpy mc_ret) s_fin rho'' tp _ ent_fin Hsm5) as HsmL.
  exists (L_memcpy mc_ret), (JL_pure AInvA CST XGL A Kc), (rho_sub rho'' s_fin), tp.
  split; [left; reflexivity|]. split.
  - apply (agree_vals_trans NF rho rho'' (rho_sub rho'' s_fin)).
    + split; [intros i Hi; unfold rho''; cbn [rho_absorb rw]; apply Hrw; exact Hi | intros l; unfold rho''; cbn [rho_absorb rl]; apply Hrl].
    + apply agree_below_vals. apply rho_sub_agree. exact ids_fin.
  - split; [exact HsmL|]. cbn [w_tr w_cfg cfg_model fst snd] in HJ5 |- *. destruct HJ5 as [(HA5 & HK5 & Htp5 & _) _].
    unfold JL_pure. split; [eapply (law_vars _ _ _ ALA); [exact HA5 | apply rm_rho_sub]|].
    split; [reflexivity|]. split; [|exact HK5].
    rewrite rm_rho_sub. split.
    + intros a Ha Hc. apply RMout. rewrite u64_lit by lia. intros Hr.
      destruct Hc as [[Hcl _]|[Hsh _]].
      * exact (client_not_rtc3 A rho'' tp md a HA5 Hcl Hr).
      * destruct Hsh as [(x & Hx & ->)|(x & Hx & ->)].
        -- pose proof (topG_range (aa_geom A)) as TG.
           destruct (law_client_app _ _ _ ALA A rho'' tp md x HA5 Hx) as [X|[X|X]]; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI, Sh, SHADOW_OFF, rtc3_rng in *;
             pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia.
        -- destruct (HXGL x Hx). unfold IMG_HI, Sh, SHADOW_OFF, rtc3_rng in *.
           pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia.
    + intros x j Hx Hj Hdef.
      assert (X0 : 0 <= x < 2 ^ 47).
      { destruct Hx as [[Hcl _]|Hgl].
        - pose proof (topG_range (aa_geom A)) as TG. destruct (law_client_app _ _ _ ALA A rho'' tp md x HA5 Hcl) as [X|[X|X]]; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI in *; lia.
        - destruct (HXGL x Hgl). unfold IMG_HI in *. lia. }
      rewrite RMout; [exact Hdef|]. unfold word_byte. rewrite u64_lit.
      2:{ unfold Sh, SHADOW_OFF. pose proof (Z.div_mod (x / 8 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 8 + 2147450880) 8 ltac:(lia)).
          assert (0 <= x / 8 <= 2 ^ 47) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). lia. }
      unfold Sh, SHADOW_OFF, rtc3_rng. pose proof (Z.div_mod (x / 8 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 8 + 2147450880) 8 ltac:(lia)).
      assert (0 <= x / 8) by (apply Z.div_pos; lia). lia.
Qed.
End Inst.

Theorem asan_memcpy_contract : ltac2:(tb__ "0|1|
S4cOF_;S76S87S22S2S1dQ40A1A1S89R3A1S7dS11R6S88VAInvA;R5R4A3A3S4fS11R7S7cS11S8cVAInvA;R6R5A3S5dR4R3A5S83S11S73R4R3S0S8S3bS82A2M0S1S3bS82S8aS58A1S8bVAInvA;VCST;VXGL;R6R5A5A4S4G0A1A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokf.
  apply (triple_pre ok _ (PZ rho /\ cells_ok (view segs (rm rho)) (RTCL (aa_geom A)) /\ Forall (holds rho) facts_W
                        /\ band_free (UU rho 53) (UU rho 54) /\ band_free (UU rho 55) (UU rho 56))).
  { intros w Hw. pose proof Hw as [Hsm [HJ [HB1 HB2]]]. pose proof HJ as (HA & _ & _).
    split; [exact (PZ_of_pre _ rho tp w Hw)|]. split; [exact (law_rtc _ _ _ ALA A rho tp _ HA)|].
    split; [|exact (conj HB1 HB2)]. rewrite <- facts_W_eq. exact (SPA_facts_hold segs _ rho PreW tp w Hw). }
  intros (HP & HR & HFW & HBF1 & HBF2).
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w Hw. apply (SPA_C_of_pre (Jcont A Kc tp) rho tp w (aa_geom A) HR).
    destruct Hw as [Hsm [HJ _]]. split; [exact Hsm | split; [exact HJ | reflexivity]]. }
  apply (call_soundA segs ok (Jcont A Kc tp) (Jcore A Kc tp) (Jcore A Kc tp) (Jcont A Kc tp) C Pre_mc0 s_ms [] Posts_mc _ rho tp fr_ms cc_ms).
  - intros rho1 tp1. apply asan_memcpy_core_sum; [apply Jcore_okf; exact Hokf | apply Jcore_stable; exact HKc | intros r t tr md [_ [[Hc _] _]]; exact Hc | intros r t tr md [_ [[_ Hc] _]]; exact Hc].
  - intros tr ms md Hsm HJ. eapply J_in; eauto.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ Hlink HJL. eapply J_out; eauto.
  - intros L rho' tpL HinL Hag. destruct HinL as [<-|[]]. cbn [la_state]. rewrite T0_eq.
    eapply triple_conseq; [ | | apply triple_refl]; [intros w Hw; exact Hw|].
    intros w Hw. eapply cont_post; eauto.
Qed.

Theorem asan_memcpy_contract_ex : ltac2:(tb__ "0|1|
S76S87S22S2S1dQ40A1A1S89R3A1S4eS11S7cS11S8cVAInvA;R5R4A3S5dR3R2A5S83S11S73R3R2S0S8S3bS82A2M0S1S3bS82S8aS58A1S8bVAInvA;VCST;VXGL;R5R4A5A4S4G0A1A3A5A3F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc.
  apply (etriple_pre _ (PZ rho /\ cells_ok (view segs (rm rho)) (RTCL (aa_geom A)) /\ Forall (holds rho) facts_W
                        /\ band_free (UU rho 53) (UU rho 54) /\ band_free (UU rho 55) (UU rho 56))).
  { intros w Hw. pose proof Hw as [Hsm [HJ [HB1 HB2]]]. pose proof HJ as (HA & _ & _).
    split; [exact (PZ_of_pre _ rho tp w Hw)|]. split; [exact (law_rtc _ _ _ ALA A rho tp _ HA)|].
    split; [|exact (conj HB1 HB2)]. rewrite <- facts_W_eq. exact (SPA_facts_hold segs _ rho PreW tp w Hw). }
  intros (HP & HR & HFW & HBF1 & HBF2).
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w Hw. apply (SPA_C_of_pre (Jcont A Kc tp) rho tp w (aa_geom A) HR).
    destruct Hw as [Hsm [HJ _]]. split; [exact Hsm | split; [exact HJ | reflexivity]]. }
  apply (call_completeA segs (Jcont A Kc tp) (Jcore A Kc tp) (Jcore A Kc tp) (Jcont A Kc tp) C Pre_mc0 s_ms [] Posts_mc _ rho tp fr_ms cc_ms).
  - intros rho1 tp1. apply asan_memcpy_core_sum_ex; [apply Jcore_stable; exact HKc | intros r t tr md [_ [[Hc _] _]]; exact Hc | intros r t tr md [_ [[_ Hc] _]]; exact Hc].
  - intros tr ms md Hsm HJ. eapply J_in; eauto.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ Hlink HJL. eapply J_out; eauto.
  - intros L rho' tpL HinL Hag. destruct HinL as [<-|[]]. cbn [la_state]. rewrite T0_eq.
    eapply etriple_conseq; [ | | apply etriple_refl]; [intros w Hw; exact Hw|].
    intros w Hw. eapply cont_post; eauto.
Qed.

Theorem aca_asan_memcpy_of_laws : ltac2:(tb__ "0|0|
S90S11VAInvA;VCST;VXGL;S59S58S58A7").
Proof.
  intros ok A Kc rho tp HKc Hokf.
  eapply triple_conseq; [intros w Hw; exact Hw | | apply (asan_memcpy_contract ok A Kc rho tp HKc Hokf)].
  intros w (L & JL & rho' & tp' & Hin & Hrest). exists L, JL, rho', tp'. split; [|exact Hrest].
  destruct Hin as [E|[]]. rewrite <- E. left. reflexivity.
Qed.
Theorem acx_asan_memcpy_of_laws : ltac2:(tb__ "0|0|
S91S11VAInvA;VCST;VXGL;S59S58S58A7").
Proof.
  intros A Kc rho tp HKc.
  eapply etriple_conseq; [intros w Hw; exact Hw | | apply (asan_memcpy_contract_ex A Kc rho tp HKc)].
  intros w (L & JL & rho' & tp' & Hin & Hrest). exists L, JL, rho', tp'. split; [|exact Hrest].
  destruct Hin as [E|[]]. rewrite <- E. left. reflexivity.
Qed.
End Contract.
