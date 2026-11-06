(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "ACEIL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "valuation"; "SVar"; "eval"; "SPUle"; "rw"; "SLit"; "cell"; "cell_holds"; "ob_base"; "ss_objs"; "obj_holds"; "rm"; "DUnknown"; "SAlu"; "ob_dflt"; "obj_hi_of"; "obj_lo_of"; "smatch"; "enc_bytes"; "mkCell"; "oaddr"; "odefault"; "sprop_below"; "ss_next"; "sstate"; "swf"; "SPAlign"; "holds"; "mkObj"; "ob_hi"; "ob_lo"; "outside_all"; "agree_below"; "in_cell"; "rd"; "ss_facts"; "sv_below"; "@Corelib.Init.Datatypes"; "list"; "cons"; "nil"; "bool"; "option"; "true"; "pair"; "app"; "Some"; "prod"; "None"; "S"; "andb"; "fst"; "nat"; "snd"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "pow"; "lt"; "to_nat"; "opp"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "ax_X"; "leafA"; "ax_base"; "la_state"; "entailsA"; "xr_below"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_add"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "smatchA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_memcpy48_contract"; "C48"; "facts_W48"; "PreW48"; "T0_48"; "XF48"; "T0r"; "dst4_obj"; "s48"; "T2_48"; "W2_48"; "T4_48"; "W1_48"; "set_obj_cells"; "PZ48"; "T3_48"; "objs6_48"; "s_fin48"; "T1_48"; "T5_48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_memcpy48_contract.Contract48"; "Jcont"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface"; "al48_cells"; "L_memcpy48"; "memcpy48_contractA"; "memcpy48_contractA_ex"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "w_cfg"; "w_tr"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "J_pure_pre"; "KcA"; "JL_pure"; "Kc_ok"; "alloc_lawsA"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "map"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ageom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Asan_memcpy48"; "Pre48_0"; "Posts48"; "P48"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "cfg_model"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_memcpy_contract"; "RTCL"; "R_rtc"; "XF_T2"; "XF_T4"; "XF_W1"; "carve_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cells_ok";
"view"; "@Corelib.Init.Specif"; "sumbool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "Zsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall Glue3.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_memcpy_contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Asan_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_memcpy_contract OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpy48_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Asan_memcpy48.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RegionAddr AMCAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition PreW48 : axst := Pre_memcpy48 AE_A al48_cells.
Definition facts_W48 : list sprop := Eval vm_compute in ss_facts (ax_S PreW48).
Definition W1_48 : axst := Eval vm_compute in ax_of (apply_axforms PreW48 XF_W1) PreW48.
Lemma W1_48_eq : ltac2:(tb__ "0|0|
S0S32S46A1S95S5bS9cA2S36S46S64A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition W2_48 : axst := Eval vm_compute in ax_setS W1_48 (carve_S (ax_S W1_48)).
Lemma W2_48_eq : ltac2:(tb__ "0|0|
S0S46S48S64S9dS47S64A1A1A2S62A3"). Proof. reflexivity. Qed.
Definition XF48 : list sprop := ltac2:(tb__ "0|9|
S2fS8ScS16S96S16S97SaPcA1SaP35M0A1A3M1SeZ30A1M2A3SaP36A1M3A2S2fS8ScG1G3A2S2fS8ScG2G3A2S2fS8S23G0Z3M4A2S2fS8ScS16S96S16S97SaPdA1SaP37M5A1A3M6G2A3SaP38A1M7A2S2fS8ScG6G7A2S2fS8ScG2G7A2S2fS8S23G5G4A2S2fS8ScSeS3fS5Z900A2A1SaPaA1M8A2S2fS8ScG8SeS41Z2Z3fA2A1A2S30S8A1A3A3A3A3A3A3A3A3A3A3").
Definition C48 : axst := Eval vm_compute in ax_with_facts W2_48 (XF48 ++ facts_W48).
Lemma C48_eq : ltac2:(tb__ "0|0|
S0S46SabS62S35S8S5dS5aA3A2S59A3"). Proof. reflexivity. Qed.

Definition s48 : wsub := Eval vm_compute in
  ([(15%positive, SVar 53); (16%positive, SVar 54); (17%positive, SAlu ALU_SUB (SVar 12) (SVar 53)); (18%positive, SLit 48);
    (19%positive, SVar 55); (52%positive, SVar 56); (53%positive, SAlu ALU_SUB (SVar 13) (SVar 55)); (95%positive, SVar V_DEPTH)]
   ++ infer_sub 1 (ax_S C48) (ax_S Pre48_0)).
Lemma fr48 : ltac2:(tb__ "0|1|
S0S32S2eS6A1M0A1S7bS59S8cS60A3S36G0S30S6A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc48 : ltac2:(tb__ "0|0|
S0S31S7aS59S8cS60S30S6A1S85S4aS46S4cS8dA4A5S33A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T0_48 : axst := Eval vm_compute in import_postA s48 Pre48_0 P48 C48 [].
Lemma T0_48_eq : ltac2:(tb__ "0|0|
S0S46S7cS60S8cS8eS59S30S6A1A5S5cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition set_obj_cells (S : sstate) (i : nat) (cs : list cell) : sstate := ltac2:(tb__ "0|1|
S32S6A1S21Lx;S90S6S12VS;A1M0Vi;A3S6S9eVS;S35S6S84S6Vi;G0A3S2fS6S25S11R1A1S27R1A1S26R1A1Vcs;S17R1A1A5S86S6S39Vi;A1G0A3A3A3A2Lo;VS;X32x2").
Definition T0r : axst := Eval vm_compute in ax_setS T0_48 (set_obj_cells (ax_S T0_48) 3 al48_cells).
Lemma T0r_eq : ltac2:(tb__ "0|0|
S0S46S48S5cS65S47S5cA1U3S6dA3A2S5eA3"). Proof. reflexivity. Qed.
Definition T1_48 : axst := ltac2:(tb__ "0|0|
Sa9S35S8S5dS5aA3S5eA2").
Definition T2_48 : axst := Eval vm_compute in ax_of (apply_axforms T1_48 XF_T2) T1_48.
Lemma T2_48_eq : ltac2:(tb__ "0|0|
S0S32S46A1S95S6aS9aA2S36S46S61A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition objs6_48 : list sobj := Eval vm_compute in firstn 7 (ss_objs (ax_S T2_48)).
Lemma T2_48_objs : ltac2:(tb__ "0|0|
S0S2eS6A1S12S47S61A1A1S35S6S68S99A3A3"). Proof. reflexivity. Qed.
Definition T3_48 : axst := Eval vm_compute in ax_setS T2_48 (set_objs (ax_S T2_48) objs6_48).
Lemma T3_48_eq : ltac2:(tb__ "0|0|
S0S46S48S61S9eS47S61A1S68A2A2S67A3"). Proof. reflexivity. Qed.
Definition T4_48 : axst := Eval vm_compute in ax_of (apply_axforms T3_48 XF_T4) T3_48.
Lemma T4_48_eq : ltac2:(tb__ "0|0|
S0S32S46A1S95S67S9bA2S36S46S63A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T5_48 : axst := ltac2:(tb__ "0|1|
SaaS63S2fS37S7S7A2M0S34S7S7SaP35A1SaP36A1A4S2fG0S34S7S7SaP37A1SaP38A1A4S30G0A1A3A3A2").
Definition s_fin48 : wsub := Eval vm_compute in infer_sub NF (ax_S T5_48) (ax_S (L_memcpy48 AE_A al48_cells)).
Lemma ent_fin48 : ltac2:(tb__ "0|0|
S0S31S4dS6bS6eS7dS6dA2S69A3S33A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Local Notation "'UU' r i" := (bv_unsigned (rw r i)) (at level 10, r at level 9, i at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Definition PZ48 (rho : valuation) : Prop := ltac2:(tb__ "0|12|
S1S3eS50Q40M0SdVrho;P35A2A2M1S50G0SdVrho;PcA2A2M2A2S1S3eS3fG2Z30M3A2S3fG1S50G0SdVrho;P36A2A2M4A2M5A2S1S0S53S40G2Z8M6A2Z0M7A3S1S3eSa1G1A2S1S3eG5S45S41Z2M8Z2fA2M9G6A2MaA2S1S3eG4S41G8Z28A2MbA2S1S0S53S40S50G0SdVrho;PdA2A2McG6A2G7A3S1S3eG1GaA2S1S3eG2G9A2S1S3eS50G0SdVrho;PaA2A2MdG9A2S1S0S53S40GdZ10A2G7A3S1S0S53S40G1G6A2G7A3S1S3eS3fS5Z900A2GdA2S1S1S3eS44GbA1SacS50G0SdVrho;PfA2A2A1MeA2S3eGeN900A2A2S1S3eS50G0SdVrho;P37A2A2MfGcA2S1S3eS3fGcG3A2S3fGfS50G0SdVrho;P38A2A2M10A2M11A2S1S3eSa1GfA2S1S3eG11GaA2S1S3eG10GbA2S1S3eGfGaA2S1S3eGcG9A2S0S53S40GfG6A2G7A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").

Lemma facts_W48_eq : ltac2:(tb__ "0|0|
S0S2eS8A1S2cS47S5bA1A1S5aA3"). Proof. reflexivity. Qed.

Lemma PZ48_of_pre : ltac2:(tb__ "0|0|
S55S9S2eS4fQ40A1A1S72S54S4R4S5bR3R2R1A6S66R4A1F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp [tr [ms md]] [(Hsm & HMI & Hwf & Hsh & Hhz) _].
  pose proof (smatch_facts_hold segs rho _ _ Hsm) as HF. cbn [ax_S PreW48] in HF. rewrite facts_W48_eq in HF || idtac.
  pose proof (urange (rw rho 53)) as R53. pose proof (urange (rw rho 54)) as R54. pose proof (urange (rw rho 12)) as R12.
  pose proof (urange (rw rho 14)) as R14. pose proof (urange (rw rho 10)) as R10. pose proof (urange (rw rho 15)) as R15.
  have_fact A1 HF (SPUle (SVar 53) (SVar 12)).
  have_fact A2 HF (SPUle (SAlu ALU_ADD (SVar 12) (SLit 48)) (SAlu ALU_ADD (SVar 53) (SVar 54))).
  have_fact A3 HF (SPAlign 12 3).
  have_fact A4 HF (SPUle (SLit IMG_HI) (SVar 53)).
  have_fact A5 HF (SPUle (SAlu ALU_ADD (SVar 53) (SVar 54)) (SLit (2 ^ 47 - 8))).
  have_fact A6 HF (SPUle (SVar 54) (SLit (2 ^ 40))).
  have_fact A7 HF (SPAlign 13 3).
  have_fact A8 HF (SPUle (SVar 53) (SLit (2 ^ 47 - 8))).
  have_fact A9 HF (SPUle (SVar 12) (SLit (2 ^ 47))).
  have_fact A10 HF (SPUle (SVar 10) (SLit (2 ^ 47))).
  have_fact A11 HF (SPAlign 10 4).
  have_fact A12 HF (SPUle (SLit 140735332483072) (SAlu ALU_ADD (SVar 10) (SVar V_DEPTH))).
  have_fact A13 HF (SPBranch BC_GE (SLit (- memx_depth)) (SVar V_DEPTH)).
  have_fact A14 HF (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40))).
  have_fact B1' HF (SPUle (SVar 55) (SVar 13)).
  have_fact B2 HF (SPUle (SAlu ALU_ADD (SVar 13) (SLit 48)) (SAlu ALU_ADD (SVar 55) (SVar 56))).
  have_fact B4 HF (SPUle (SLit IMG_HI) (SVar 55)).
  have_fact B5 HF (SPUle (SAlu ALU_ADD (SVar 55) (SVar 56)) (SLit (2 ^ 47 - 8))).
  have_fact B6 HF (SPUle (SVar 56) (SLit (2 ^ 40))).
  have_fact B8 HF (SPUle (SVar 55) (SLit (2 ^ 47 - 8))).
  have_fact B9 HF (SPUle (SVar 13) (SLit (2 ^ 47))).
  pose proof (urange (rw rho 55)) as R55. pose proof (urange (rw rho 56)) as R56. pose proof (urange (rw rho 13)) as R13.
  cbn [eval] in A1, A2, A4, A5, A6, A8, A9, A10, A12, B1', B2, B4, B5, B6, B8, B9. destruct A3 as [_ A3]. destruct A7 as [_ A7].
  rewrite add_val in A2. rewrite add_val in A2. rewrite add_val in A5. rewrite add_val in A12.
  rewrite add_val in B2. rewrite add_val in B2. rewrite add_val in B5.
  rewrite !lit_unsigned in A2, A4, A5, A6, A8, A9, A10, A12, B2, B4, B5, B6, B8, B9.
  unfold IMG_HI in A4, B4.
  rewrite !Z.mod_small in A4, A6, A8, A9, A10, B4, B6, B8, B9 by lia.
  rewrite (Z.mod_small (2 ^ 47 - 8)) in A5, B5 by lia. rewrite (Z.mod_small 140735332483072) in A12 by lia.
  rewrite (Z.mod_small (UU rho 53 + UU rho 54)) in A2, A5 by lia. rewrite (Z.mod_small 48) in A2, B2 by lia.
  rewrite (Z.mod_small (UU rho 12 + 48)) in A2 by lia.
  rewrite (Z.mod_small (UU rho 55 + UU rho 56)) in B2, B5 by lia.
  rewrite (Z.mod_small (UU rho 13 + 48)) in B2 by lia.

  assert (AL : UU rho 53 mod 8 = 0 /\ UU rho 55 mod 8 = 0).
  { unfold shadow_ok in Hsh. cbn [ax_X PreW48] in Hsh. apply Forall_cons_iff in Hsh as [[Hal _] Hsh]. apply Forall_inv in Hsh.
    destruct Hsh as (Hal' & _). split; [exact Hal | exact Hal']. }

  assert (SW : ACEIL + 2304 <= UU rho 10).
  { unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S PreW48] in Hsm.
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
  destruct AL as [AL1 AL2]. unfold PZ48, HSE, IMG_HI. repeat (split; [lia|]). lia.
Qed.

Lemma XF48_holds : ltac2:(tb__ "0|0|
S9S66R1A1S83S8S24R2A1S5dA3F_;Frho;").
Proof.
  intros rho HP. unfold PZ48, HSE, IMG_HI, ACEIL in HP.
  destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & Q1 & Q2 & Q4 & Q5 & Q6 & Q8 & Q9 & Q12).
  pose proof (urange (rw rho 53)) as R53. pose proof (urange (rw rho 54)) as R54. pose proof (urange (rw rho 12)) as R12.
  pose proof (urange (rw rho 10)) as R10.
  pose proof (urange (rw rho 55)) as R55. pose proof (urange (rw rho 56)) as R56. pose proof (urange (rw rho 13)) as R13.
  assert (D : bv_unsigned (eval rho (SAlu ALU_SUB (SVar 12) (SVar 53))) = UU rho 12 - UU rho 53).
  { apply (U_sub2 rho (SVar 12) (SVar 53)); [reflexivity | reflexivity | lia]. }
  assert (D' : bv_unsigned (eval rho (SAlu ALU_SUB (SVar 13) (SVar 55))) = UU rho 13 - UU rho 55).
  { apply (U_sub2 rho (SVar 13) (SVar 55)); [reflexivity | reflexivity | lia]. }
  unfold XF48. repeat apply Forall_cons; try apply Forall_nil; cbn [holds].
  - rewrite (U_add2 rho _ (SLit 48) (UU rho 12 - UU rho 53) 48 D (U_lit64 rho 48 ltac:(lia))) by lia. change (eval rho (SVar 54)) with (rw rho 54). lia.
  - rewrite D. change (eval rho (SVar 54)) with (rw rho 54). lia.
  - change (eval rho (SVar 54)) with (rw rho 54). rewrite (U_lit64 rho 48) by lia. lia.
  - split; [lia | exact P12].
  - rewrite (U_add2 rho _ (SLit 48) (UU rho 13 - UU rho 55) 48 D' (U_lit64 rho 48 ltac:(lia))) by lia. change (eval rho (SVar 56)) with (rw rho 56). lia.
  - rewrite D'. change (eval rho (SVar 56)) with (rw rho 56). lia.
  - change (eval rho (SVar 56)) with (rw rho 56). rewrite (U_lit64 rho 48) by lia. lia.
  - split; [lia | exact Q12].
  - rewrite (U_lit64 rho (ACEIL + 2304)) by (unfold ACEIL; lia). change (eval rho (SVar 10)) with (rw rho 10). unfold ACEIL. lia.
  - rewrite (U_lit64 rho (2 ^ 63)) by lia. change (eval rho (SVar 10)) with (rw rho 10). lia.
Qed.

Lemma swf_W2_48 : ltac2:(tb__ "0|0|
S0S31S22S47S62A1A1S33A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XF48_below : ltac2:(tb__ "0|0|
S0S31S8fS8S1fS20S47S62A1A1A1S35S8S5dS5aA3A3S33A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma SPA_C48_of_pre : ltac2:(tb__ "0|0|
S55S9S2eS4fQ40A1A1S72S8bSa2Sa3S4S14R4A1A2S98R1A1A2S54S4R6S5bR5R4R3A6S54S4R7S59R6R5R4A6F_;F_;FG;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w G HR HS. pose proof (PZ48_of_pre J rho tp w HS) as HP.
  pose proof (SPA_axforms segs J XF_W1 rho PreW48 W1_48 tp w W1_48_eq HS) as HS1.
  pose proof HP as HP'. unfold PZ48, HSE, IMG_HI, ACEIL in HP'.
  destruct HP' as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & Q1 & Q2 & Q4 & Q5 & Q6 & Q8 & Q9 & Q12).
  pose proof (urange (rw rho 10)) as R10. pose proof (urange (rw rho 12)) as R12. pose proof (urange (rw rho 15)) as R15. pose proof (urange (rw rho 13)) as R13.
  destruct (rtc_nth G) as (N18 & N19 & N20 & N21 & N22 & N2).
  pose proof (cell_of _ G _ _ HR N18) as C18. pose proof (cell_of _ G _ _ HR N19) as C19. pose proof (cell_of _ G _ _ HR N20) as C20.
  pose proof (cell_of _ G _ _ HR N21) as C21. pose proof (cell_of _ G _ _ HR N22) as C22. pose proof (cell_of _ G _ _ HR N2) as C2.
  assert (HS2 : SPA segs J W2_48 rho tp w).
  { rewrite <- W2_48_eq. unfold carve_S.
    apply (SPA_carve_list segs J rho W1_48 tp w N_rtc NF HS1 swf_W2_48 ltac:(apply Pos.le_refl)).
    -
      unfold N_rtc. repeat apply Forall_cons; try apply Forall_nil; cbv beta iota zeta; cbn [eval];
        rewrite !lit_unsigned; rewrite !(Z.mod_small 0) by lia.
      + split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
        split; [intros off Hoff; split; [apply wok_of_imageA; lia|];
                destruct (Z_lt_ge_dec off 0xeed99); [eapply (cell_rd _ _ _ _ _ C18); cbn; lia | eapply (cell_rd _ _ _ _ _ C19); cbn; lia]|].
        split; [unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; intros j Hj;
                [apply (cell_civ rho _ _ _ _ C18); cbn; lia | apply (cell_civ rho _ _ _ _ C19); cbn; lia]|].
        intros rr y j Hin Hy Hj. cbn [ax_base W1_48 eval]. rewrite lit_unsigned. unfold SHB. intros X. pose proof (urange (eval rho (fst rr))).
        pose proof (Z.div_mod (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)).
        change (2147450880 mod 2 ^ 64) with 2147450880 in *. assert (0 <= y / 8) by (apply Z.div_pos; lia). lia.
      + split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
        split; [intros off Hoff; split; [apply wok_of_imageA; lia|];
                destruct (Z_lt_ge_dec off 0xeeda8); [eapply (cell_rd _ _ _ _ _ C20); cbn; lia|];
                destruct (Z_lt_ge_dec off 0xeedb0); [eapply (cell_rd _ _ _ _ _ C21); cbn; lia | eapply (cell_rd _ _ _ _ _ C22); cbn; lia]|].
        split; [unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; intros j Hj;
                [apply (cell_civ rho _ _ _ _ C20); cbn; lia | apply (cell_civ rho _ _ _ _ C21); cbn; lia | apply (cell_civ rho _ _ _ _ C22); cbn; lia]|].
        intros rr y j Hin Hy Hj. cbn [ax_base W1_48 eval]. rewrite lit_unsigned. unfold SHB. intros X. pose proof (urange (eval rho (fst rr))).
        pose proof (Z.div_mod (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)).
        change (2147450880 mod 2 ^ 64) with 2147450880 in *. assert (0 <= y / 8) by (apply Z.div_pos; lia). lia.
      + split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
        split; [intros off Hoff; split; [apply wok_of_imageA; lia | eapply (cell_rd _ _ _ _ _ C2); cbn; lia]|].
        split; [unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; intros j Hj; apply (cell_civ rho _ _ _ _ C2); cbn; lia|].
        intros rr y j Hin Hy Hj. cbn [ax_base W1_48 eval]. rewrite lit_unsigned. unfold SHB. intros X. pose proof (urange (eval rho (fst rr))).
        pose proof (Z.div_mod (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 mod 2 ^ 64 + y / 8) 8 ltac:(lia)).
        change (2147450880 mod 2 ^ 64) with 2147450880 in *. assert (0 <= y / 8) by (apply Z.div_pos; lia). lia.
    -
      destruct HS1 as [(Hsm1 & _) _]. unfold virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm1.
      destruct Hsm1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
      cbn [ax_S W1_48 ss_objs] in Hall |- *.
      apply Forall_inv in Hall. unfold obj_holds, obj_lo_of, obj_hi_of in Hall. cbn [ob_base ob_lo ob_hi eval] in Hall.
      destruct Hall as ((B1 & _ & _ & _) & _).
      unfold soff in B1. cbn [eval] in B1. rewrite bv_signed_U in B1.
      pose proof (Zsigned_spec (UU rho 15)) as Z15.
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
  rewrite <- C48_eq. apply SPA_refacts; [exact HS2 | exact XF48_below |].
  intros _. apply Forall_app. split; [apply XF48_holds; exact HP|].
  rewrite <- facts_W48_eq. eapply SPA_facts_hold. exact HS.
Qed.

Lemma oaddr_shift : ltac2:(tb__ "0|1|
S9S7S53S53S3eZ0S3fS50Q40M0SbR4R3A2A2R2A2A2S0S4fG0A1S1dR5R4S3fR3R2A2A3S52G0S1dR5R4R3A3S51G0R2A2A3A3F_;Fd;Fk;Fbase;Frho;").
Proof.
  intros rho base k d Hk. unfold oaddr. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64%N) with (2 ^ 64). rewrite <- Zplus_mod. f_equal. lia.
Qed.

Lemma cell_holds_join : ltac2:(tb__ "0|5|
S9S7S53S53S71S53S53S53S7S7S7S42Z0M0R5A2M1G1S3eS44S41Z2Z3eA2M2A1R8A2S42S3fS3fR9R8A2R7A2G2A2S3eG0S3fS50Q40SbRfReA2A2RdA2A2S0S2eS4fQ8A1M3A1S1bS43S3fRaR9A2A1SbR10R6A2A2S35G3S1bS43RaA1SbR10R8A2A2S1bS43R9A1SbR10R7A2A2A3A3S10R11R10RfReRdS1cSeRcA1RbR9A3A6S10R12R11R10RfReS1cSeS3fRdRcA2M4A1RbR9A3A6S10R13R12R11R10RfS1cSeReA1G4R9A3A6F_;F_;F_;F_;F_;F_;F_;F_;Fv;Fv2;Fv1;Fw2;Fw1;Fk;Fms;Fhi;Flo;Fbase;Frho;").
Proof.
  intros rho base lo hi ms k w1 w2 v1 v2 v Hw1 Hw2 Hk1 Hk2 Hb Henc (A1 & B1 & C1) (A2 & B2 & C2).
  unfold cell_holds in *. cbn [c_off c_width SymState.c_val] in *. rewrite !soff_lit_small in * by lia.
  split; [lia|]. split; [lia|]. rewrite Henc. replace (Z.to_nat (w1 + w2)) with (Z.to_nat w1 + Z.to_nat w2)%nat by lia.
  apply (rd_bytes_app ms _ (Z.to_nat w1) (Z.to_nat w2)); [exact C1|].
  rewrite Z2Nat.id by lia. rewrite <- oaddr_shift by lia. exact C2.
Qed.

Lemma in_cell_dec : ltac2:(tb__ "0|1|
S9S53SfSa4S2aR3R2R1A3M0S2G0A1A2Fc;Foff;Frho;").
Proof.
  intros rho off c. unfold in_cell. destruct (Z_le_dec (soff rho (c_off c)) off); [|right; lia].
  destruct (Z_lt_dec off (soff rho (c_off c) + c_width c)); [left; lia | right; lia].
Qed.

Lemma obj_unknown_rd : ltac2:(tb__ "0|1|
S9S71S6S53S0S1eS17R2A1S15A3S13S4R5R4R3A4S1S3eS19R6R4A2R3A2S42R3S18R6R4A2A2A2S3S4fQ8A1M0G0S0S32G0A1S2bR7S1dR8S11R6A1R5A3A2S36G0R1A2A3Lbt;A2F_;F_;F_;Foff;Fo;Fms;Frho;").
Proof.
  intros rho ms o off Hu (Hb & Hw & Hc & Hd & _) Hoff.
  destruct (Exists_dec (in_cell rho off) (ob_cells o) (in_cell_dec rho off)) as [Hcov|Hncov].
  - apply Exists_exists in Hcov as (c & Hin & Hic). pose proof (proj1 (Forall_forall _ _) Hc c Hin) as (C1 & C2 & C3). cbn [SymState.c_val] in C3.
    unfold in_cell in Hic.
    pose proof (rd_bytes_nth ms (Z.to_nat (c_width c)) _ _ (Z.to_nat (off - soff rho (c_off c))) C3 ltac:(lia)) as X.
    unfold oaddr in X |- *. rewrite u64_of_sum in X by lia. specialize (X ltac:(lia)).
    replace (bv_unsigned (eval rho (ob_base o)) + soff rho (c_off c) + Z.of_nat (Z.to_nat (off - soff rho (c_off c))))
      with (bv_unsigned (eval rho (ob_base o)) + off) in X by lia. eexists. exact X.
  - specialize (Hd off Hoff Hncov). rewrite Hu in Hd. cbn [dflt_holds] in Hd. exact Hd.
Qed.

Lemma obj_holds_recell_unknown : ltac2:(tb__ "0|0|
S9S71S6S2eSfA1S0S1eS17R2A1S15A3S13S4R5R4R3A4S83SfS10R6S11R4A1S19R6R4A2S18R6R4A2R5A5R3A3S13S4R7R6S25S11R5A1S27R5A1S26R5A1R4S15A5A4F_;F_;F_;Fcs';Fo;Fms;Frho;").
Proof.
  intros rho ms o cs' Hu Ho Hcs. pose proof Ho as (Hb & Hw & Hc & Hd & Hi).
  unfold obj_holds. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. unfold obj_lo_of, obj_hi_of in *. cbn [ob_lo ob_hi].
  split; [exact Hb|]. split; [intros off Hoff _; apply Hw; [exact Hoff | rewrite Hu; reflexivity]|].
  split; [exact Hcs|]. split; [|exact I].
  intros off Hoff _. cbn [dflt_holds]. exact (obj_unknown_rd rho ms o off Hu Ho Hoff).
Qed.

Lemma smatch_set_obj_cells : ltac2:(tb__ "0|0|
S9S21S37S2eS88A1S92A2S3cS6S2eSfA1S0S32S6A1S90S6S12R5A1R3A3S36S6R2A2A3S0S1eS17R3A1S15A3S71S13S4R9R1R5A4S83SfS10RaS11R6A1S19RaR6A2S18RaR6A2R2A5R5A3F_;Fms;S0S31S22S65R8R6R4A3A1S33A3S1aS4RaR9R8A4S1aS4RbS65RaR8R6A3R9A4F_;F_;F_;F_;F_;Fcs';Fo;Fi;Fw;FS;Frho;").
Proof.
  intros rho S [tr [ms md]] i o cs' Hn Hu Hcs Hwf Hsm.
  pose proof (nth_error_split3 _ _ _ Hn) as Esplit.
  unfold set_obj_cells in Hwf |- *. rewrite Hn in Hwf |- *.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hcsr & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  assert (RNG : obj_range rho (mkObj (ob_base o) (ob_lo o) (ob_hi o) cs' (ob_dflt o)) = obj_range rho o) by reflexivity.
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hcsr|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs set_objs]. destruct Hm as (Hall & Hpd & Hfr). rewrite Esplit in Hall, Hpd, Hfr.
  split; [|split].
  - apply Forall_app in Hall as [HA HB]. inversion HB; subst. apply Forall_app. split; [exact HA|].
    constructor; [|assumption]. rewrite Hu. apply (obj_holds_recell_unknown rho ms o cs' Hu); [assumption | apply Hcs; assumption].
  - apply pairwise_disjoint_pdr. apply pairwise_disjoint_pdr in Hpd. rewrite map_app in Hpd |- *. cbn [map] in Hpd |- *. rewrite RNG. exact Hpd.
  - intros a Hout. apply Hfr. unfold outside_all in Hout |- *. rewrite Forall_app in Hout |- *. destruct Hout as [HA HB].
    split; [exact HA|]. inversion HB; subst. constructor; [rewrite <- RNG; assumption | assumption].
Qed.

Definition dst4_obj : sobj := Eval vm_compute in match nth_error (ss_objs (ax_S T0_48)) 3 with Some o => o | None => O_rtc3 end.
Lemma dst4_nth : ltac2:(tb__ "0|0|
S0S32S6A1S90S6S12S47S5cA1A1U3A3S36S6S5fA2A3"). Proof. reflexivity. Qed.
Lemma dst4_cells_hold : ltac2:(tb__ "0|0|
S9S71S13S4R2R1S5fA4S83SfS10R3S11S5fA1S19R3S5fA2S18R3S5fA2R2A5S6dA3F_;Fms;Frho;").
Proof.
  intros rho ms Ho. pose proof Ho as ((Hb0 & _) & _ & Hc & _).
  assert (C : forall c, In c (ob_cells dst4_obj) -> cell_holds rho (ob_base dst4_obj) (obj_lo_of rho dst4_obj) (obj_hi_of rho dst4_obj) ms c).
  { intros c Hc'. exact (proj1 (Forall_forall _ _) Hc c Hc'). }
  unfold al48_cells, c8x.
  repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- cell_holds _ _ _ _ _ (mkCell (SLit ?k) 8 (SLit ?v)) =>
      apply (cell_holds_join rho _ _ _ ms k 4 4 (SLit v) (SLit 0) (SLit v)); [lia | lia | lia | lia | exact Hb0 | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
       | apply C; cbn; tauto | apply C; cbn; tauto] end.
Qed.
Lemma swf_T0r : ltac2:(tb__ "0|0|
S0S31S22S47S5eA1A1S33A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma SPA_morphX' : ltac2:(tb__ "0|9|
S55S55S46S21S9S9S2eS4fQ40A1M0A1S72S0S31S3aS8fS37S7S7A2M1S4eS20R5A1M2A1S49R6A1A3S2dG2S4bR6A1A2A2S33A3S0G0SbR4S4bR7A1M3A2SbR5G3A2A3G1S91G1R1S49R9A1A3S1S0G0SbR7S3bS7S7R2A3M4A2SbR8G4A2A3S0G0SbR7S3dS7S7R2A3M5A2SbR8G5A2A3A2F_;Fr;G0S28R8S12S47RaA1M6A1R1A3S2S0S32S4fQ8A1M7A1M8S14R9R2A2S38G7A1A3A1S1S28R9S12RbA1R3A3S0G8S14R9R3A2S14RaR3A2A3A2F_;F_;Fx;S1aS4R8G6S9fR6R5A2A4S1aS4R8RaS9fR7R6A2A4F_;RdR9R7S74R6A1S93S73R6A1A1A4RdR9R8S74R7A1S93S73R7A1A1A4F_;S54S4ReRcRaR8R7A6S54S4ReS48RdRcA2RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;FS';FA;FJ';FJ;").
Proof.
  intros J J' A S' rho rho' tp w Hwf' Hb HX HO HS HJ [(Hsm & HMI & Hwf & Hsh & Hhz) Hk].
  split; [|apply HJ; exact Hk].
  split; [apply HS; exact Hsm|]. split; [exact HMI|].
  split; [unfold axwf; cbn [ax_S ax_X ax_base ax_setS]; exact Hwf'|].
  split; [|exact Hhz].
  apply (shadow_ok_transport rho rho' A (ax_setS A S')); [reflexivity | exact Hb | exact HX | | exact Hsh].
  intros x _ Hout Hrm. exact (HO x Hout Hrm).
Qed.

Lemma SPA_T0r : ltac2:(tb__ "0|0|
S55S9S2eS4fQ40A1A1S72S54S4R4S5cR3R2R1A6S54S4R5S5eR4R3R2A6F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w Hsp. rewrite <- T0r_eq.
  eapply (SPA_morphX' J J T0_48 _ rho rho tp w); [ | reflexivity | intros r Hr; split; reflexivity | | | intros HK; exact HK | exact Hsp].
  - pose proof swf_T0r as W. destruct (proj1 Hsp) as (_ & _ & Hwf & _). unfold axwf in Hwf.
    replace (ss_next (set_obj_cells (ax_S T0_48) 3 al48_cells)) with (ss_next (ax_S T0_48)) by reflexivity. exact Hwf.
  - intros x Hout Hrm. split; [|reflexivity].
    unfold set_obj_cells. rewrite dst4_nth. cbn [ss_objs set_objs].
    rewrite (nth_error_split3 _ _ _ dst4_nth) in Hout. unfold outside_all in Hout |- *. rewrite Forall_app in Hout |- *. destruct Hout as [HA HB].
    split; [exact HA|]. inversion HB; subst. constructor; assumption.
  - intros Hsm. apply (smatch_set_obj_cells rho (ax_S T0_48) (virt tp w) 3 dst4_obj al48_cells dst4_nth eq_refl).
    + intros ms Ho. exact (dst4_cells_hold rho ms Ho).
    + exact swf_T0r.
    + exact Hsm.
Qed.

Lemma T0r_below : ltac2:(tb__ "0|0|
S0S31S8fS8S1fS20S47S5eA1A1A1S35S8S5dS5aA3A3S33A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XFW48_belowNF : ltac2:(tb__ "0|0|
S0S31S8fS8S1fS77A1S35S8S5dS5aA3A3S33A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_fin48 : ltac2:(tb__ "0|0|
S0S31Sa7S69S77A2S33A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_T4_48 : ltac2:(tb__ "0|3|
S0S2eS37S7S7A2M0A1S49S63A1S2fG0S34S7S7SaP35A1SaP36A1A4M1S2fG0S34S7S7SaP37A1SaP38A1A4M2S2fG0G1S2fG0G2S30G0A1A3A3A3A3A3"). Proof. reflexivity. Qed.

Section Contract48.
Variable AInvA : ltac2:(tb__ "0|0|
S89S9S2eS4fQ40A1A1S87OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S82S4VAInvA;VCST;A3").

Hypothesis HLV : law_view_stmt AInvA.
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Definition Jcont (A : AA) (Kc : KcA) (tp0 : list word) : jpredA := ltac2:(tb__ "0|1|
S9S2eS4fQ40A1A1M0S2eS88A1S87S1S7eVAInvA;VA;VKc;R4R3R2R1A7S0G0R3Vtp0;A3A2Lmd;Ltr;Lt;Lr;").

Lemma Jcont_stable : ltac2:(tb__ "0|0|
S89S7fS2eS4fQ40A1A1S81R2A1S58S4S77S6cR4R3R2A3A3F_;Ftp0;FKc;FA;").
Proof.
  intros A Kc tp0 HKc rho rho' tp tr md md' Hag Hme ((HA & HK & Htp & Htv) & ->).
  pose proof Hag as (Hrw & _ & Hrm).
  split; [split; [|split; [|split]]|reflexivity].
  - eapply (law_mat _ _ _ ALA); [|exact Hme]. eapply (law_vars _ _ _ ALA); [exact HA|].
    apply functional_extensionality. intros a. symmetry. apply Hrm.
  - eapply mat_blind_equiv; [apply Kc_mat_blind; exact HKc | exact Hme | exact HK].
  - unfold tp_ok in *. rewrite <- (Hrw 24%positive) by reflexivity. exact Htp.
  - unfold top_var in *. rewrite <- (Hrw _) by reflexivity. exact Htv.
Qed.

Lemma Jcont_okf : ltac2:(tb__ "0|0|
S72OF_;S89S7fS2eS4fQ40A1A1S56S4R4S7eVAInvA;R3R2A3A3S56S4R5S6cR4R3R2A3A3F_;Ftp0;FKc;FA;Fok;").
Proof. intros ok A Kc tp0 H rho tp tr ms md msv' [HJ _]. eapply H. exact HJ. Qed.

Section Inst.
Variable ok : world -> Prop.
Variable A : AA. Variable Kc : KcA.
Variables (rho : valuation) (tp : list word).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HP : PZ48 rho.
Hypothesis HR : ltac2:(tb__ "0|0|
Sa2Sa3S4S14Vrho;A1A2S98S8aVA;A1A1A2").

Lemma J_in48 : ltac2:(tb__ "0|1|
S2eS88A1M0S71S87S57S4Vrho;Vtp;S59S34G0S92R3S94R2R1A2A4A5S6cVA;VKc;Vtp;Vrho;Vtp;R4R2A7S6cVA;VKc;Vtp;Sa6Sa5Vrho;S30S6A1Sa0R3Vtp;R4A3A3S60A2Vtp;R5R3A7F_;F_;Fmd;Fms;Ftr;").
Proof.
  intros tr ms md _ [(HA & HK & Htp & Htv) _].
  split; [split; [|split; [|split]]|reflexivity].
  - eapply (law_vars _ _ _ ALA); [exact HA|]. rewrite rm_rho_sub. apply rm_absorb_nil.
  - exact HK.
  - unfold tp_ok in *. rewrite rw_sub. replace (wsub_get s48 24) with (SVar 24) by reflexivity. rewrite eval_absorb. exact Htp.
  - unfold top_var in *. rewrite rw_sub. replace (wsub_get s48 V_TOP) with (SVar V_TOP) by reflexivity. rewrite eval_absorb. exact Htv.
Qed.

Lemma J_out48 : ltac2:(tb__ "0|1|
S4aS9S9S2eS4fQ40A1A1S2eS88A1M0S71S87G0S87S91S4aR9S8dA3S57S4Vrho;Vtp;S59S34G0S92R6S94R5R4A2A4A5S6cVA;VKc;Vtp;Vrho;Vtp;R7R5A7Sa8Vrho;Sa0R6Vtp;R7A3S30S6A1S60S47S8cA1S47S59A1S47S4cRcA1A1RbRaA9S6cVA;VKc;Vtp;RbRaR6R5A7S6cVA;VKc;Vtp;RdRbR7R6A7F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FtpL;FrhoL;Frho';FL;").
Proof.
  intros L rho' rhoL tpL tr ms md tr' md' _ _ [(HA & HK & Htp & Htv) _] (Hag & HagL & _) ((HA' & HK' & Htp' & _) & ->).
  pose proof Hag as (Hrw & _ & Hrm). pose proof HagL as (_ & _ & HrmL).
  split; [split; [|split; [|split]]|reflexivity].
  - eapply (law_vars _ _ _ ALA); [exact HA'|]. apply functional_extensionality. intros a.
    rewrite <- (Hrm a), <- (HrmL a). rewrite rm_rho_sub, rm_absorb_nil. reflexivity.
  - exact HK'.
  - unfold tp_ok in *. rewrite <- (Hrw 24%positive) by reflexivity. exact Htp.
  - unfold top_var in *. rewrite <- (Hrw _) by reflexivity. exact Htv.
Qed.
Hypothesis HFW : ltac2:(tb__ "0|0|
S83S8S24Vrho;A1S5aA3").

Lemma cont_post48 : ltac2:(tb__ "0|1|
S9S2eS4fQ40A1A1S72S29S77Vrho;R3A3S54S4S6cVA;VKc;Vtp;A3S5cR4R3R2A6S79S4S77Vrho;Vtp;S2fS37S46S78A2M0S34S46S78S6eS7dS6dA2S80VAInvA;VCST;VXGL;VA;VKc;A5A4S30G0A1A3R3A6F_;F_;Fw;FtpL;Frho';").
Proof.
  intros rho' tpL [tr [ms md]] Hag HS00. pose proof (SPA_T0r _ rho' tpL _ HS00) as HS0.
  pose proof (proj2 HS0) as HJ0. cbn [w_tr w_cfg cfg_model fst snd] in HJ0. destruct HJ0 as [_ EtpL]. subst tpL.
  pose proof Hag as (Hrw & Hrl & Hrm).

  assert (HS1 : SPA segs (Jcont A Kc tp) T1_48 rho' tp (tr, mkCfg ms md)).
  { split; [|exact (proj2 HS0)]. unfold T1_48. apply smatchA_add_facts; [exact (proj1 HS0) | | exact T0r_below].
    apply (Forall_holds_agree NF rho rho'); [exact Hag | exact XFW48_belowNF |].
    apply Forall_app. split; [apply XF48_holds; exact HP | exact HFW]. }
  pose proof (SPA_axforms segs _ XF_T2 rho' T1_48 T2_48 tp _ T2_48_eq HS1) as HS2.

  pose proof (SPA_unobj segs (Jcont A Kc tp) rho' T2_48 objs6_48 R_rtc tp tr ms md T2_48_objs HS2) as HS3. cbn zeta in HS3.
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
          pose proof (absorb_carved_cells segs rho' (ax_S T2_48) tr (vms md tp ms) (vmd md) objs6_48 R_rtc (SLit 0) lo hi cs Hsm2 T2_48_objs Hin' H1 H2 H3 H4) as [X _].
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
  specialize (HS3 HJ3). rewrite T3_48_eq in HS3.
  pose proof (SPA_axforms segs _ XF_T4 rho'' T3_48 T4_48 tp _ T4_48_eq HS3) as HS4.
  assert (HS5 : SPA segs (Jcont A Kc tp) T5_48 rho'' tp (tr, mkCfg ms md)).
  { unfold T5_48. apply SPA_x_sub; [|exact HS4]. rewrite X_T4_48. intros r [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity]. }
  destruct HS5 as [Hsm5 HJ5].
  pose proof (smatchA_entails segs T5_48 (L_memcpy48 AE_A al48_cells) s_fin48 rho'' tp _ ent_fin48 Hsm5) as HsmL.
  exists (L_memcpy48 AE_A al48_cells), (JL_pure AInvA CST XGL A Kc), (rho_sub rho'' s_fin48), tp.
  split; [left; reflexivity|]. split.
  - apply (agree_vals_trans NF rho rho'' (rho_sub rho'' s_fin)).
    + split; [intros i Hi; unfold rho''; cbn [rho_absorb rw]; apply Hrw; exact Hi | intros l; unfold rho''; cbn [rho_absorb rl]; apply Hrl].
    + apply agree_below_vals. apply rho_sub_agree. exact ids_fin48.
  - split; [exact HsmL|]. cbn [w_tr w_cfg cfg_model fst snd] in HJ5 |- *. destruct HJ5 as [(HA5 & HK5 & Htp5 & _) _].
    unfold JL_pure. split; [eapply (law_vars _ _ _ ALA); [exact HA5 | apply rm_rho_sub]|].
    split; [reflexivity|]. split; [|exact HK5].
    rewrite rm_rho_sub. split.
    + intros a Ha Hc. apply RMout. rewrite u64_lit by lia. intros Hr.
      destruct Hc as [[Hcl _]|[Hsh _]].
      * exact (client_not_rtc3 AInvA CST ALA HCST A rho'' tp md a HA5 Hcl Hr).
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

Theorem asan_memcpy48_contract : ltac2:(tb__ "0|1|
S72OF_;S89S7fS9S2eS4fQ40A1A1S81R3A1S56S4R6S7eVAInvA;R5R4A3A3S76S4R7S54S4S7eVAInvA;R6R5A3S5bR4R3A5S79S4S77R4R3S2fS37S46S78A2M0S34S46S78S6eS7dS6dA2S80VAInvA;VCST;VXGL;R6R5A5A4S30G0A1A3A5A4F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokf.
  apply (triple_pre ok _ (PZ48 rho /\ cells_ok (view segs (rm rho)) (RTCL (aa_geom A)) /\ Forall (holds rho) facts_W48)).
  { intros w Hw. destruct Hw as [Hsm HJ]. pose proof HJ as (HA & _ & _).
    split; [exact (PZ48_of_pre _ rho tp w (conj Hsm HJ))|]. split; [exact (law_rtc _ _ _ ALA A rho tp _ HA)|].
    rewrite <- facts_W48_eq. exact (SPA_facts_hold segs _ rho PreW48 tp w (conj Hsm HJ)). }
  intros (HP & HR & HFW).
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w Hw. apply (SPA_C48_of_pre (Jcont A Kc tp) rho tp w (aa_geom A) HR).
    destruct Hw as [Hsm HJ]. split; [exact Hsm | split; [exact HJ | reflexivity]]. }
  apply (call_soundA segs ok (Jcont A Kc tp) (Jcont A Kc tp) (Jcont A Kc tp) (Jcont A Kc tp) C48 Pre48_0 s48 [] Posts48 _ rho tp fr48 cc48).
  - intros rho1 tp1. apply core48_sum; [apply Jcont_okf; exact Hokf | apply Jcont_stable; exact HKc].
  - intros tr ms md Hsm HJ. eapply J_in48; eauto.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ Hlink HJL. eapply J_out48; eauto.
  - intros L rho' tpL HinL Hag. destruct HinL as [<-|[]]. cbn [la_state]. rewrite T0_48_eq.
    eapply triple_conseq; [ | | apply triple_refl]; [intros w Hw; exact Hw|].
    intros w Hw. eapply cont_post48; eauto.
Qed.

Theorem asan_memcpy48_contract_ex : ltac2:(tb__ "0|1|
S89S7fS9S2eS4fQ40A1A1S81R3A1S75S4S54S4S7eVAInvA;R5R4A3S5bR3R2A5S79S4S77R3R2S2fS37S46S78A2M0S34S46S78S6eS7dS6dA2S80VAInvA;VCST;VXGL;R5R4A5A4S30G0A1A3A5A3F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc.
  apply (etriple_pre _ (PZ48 rho /\ cells_ok (view segs (rm rho)) (RTCL (aa_geom A)) /\ Forall (holds rho) facts_W48)).
  { intros w Hw. destruct Hw as [Hsm HJ]. pose proof HJ as (HA & _ & _).
    split; [exact (PZ48_of_pre _ rho tp w (conj Hsm HJ))|]. split; [exact (law_rtc _ _ _ ALA A rho tp _ HA)|].
    rewrite <- facts_W48_eq. exact (SPA_facts_hold segs _ rho PreW48 tp w (conj Hsm HJ)). }
  intros (HP & HR & HFW).
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w Hw. apply (SPA_C48_of_pre (Jcont A Kc tp) rho tp w (aa_geom A) HR).
    destruct Hw as [Hsm HJ]. split; [exact Hsm | split; [exact HJ | reflexivity]]. }
  apply (call_completeA segs (Jcont A Kc tp) (Jcont A Kc tp) (Jcont A Kc tp) (Jcont A Kc tp) C48 Pre48_0 s48 [] Posts48 _ rho tp fr48 cc48).
  - intros rho1 tp1. apply core48_sum_ex. apply Jcont_stable; exact HKc.
  - intros tr ms md Hsm HJ. eapply J_in48; eauto.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ Hlink HJL. eapply J_out48; eauto.
  - intros L rho' tpL HinL Hag. destruct HinL as [<-|[]]. cbn [la_state]. rewrite T0_48_eq.
    eapply etriple_conseq; [ | | apply etriple_refl]; [intros w Hw; exact Hw|].
    intros w Hw. eapply cont_post48; eauto.
Qed.

Theorem mc48_of_laws : ltac2:(tb__ "0|0|
S6fS4S7dVAInvA;VCST;VXGL;S6dA6").
Proof. intros ok A Kc rho tp HKc Hokf. exact (asan_memcpy48_contract ok A Kc rho tp HKc Hokf). Qed.
Theorem mc48x_of_laws : ltac2:(tb__ "0|0|
S70S4S7dVAInvA;VCST;VXGL;S6dA6").
Proof. intros A Kc rho tp HKc. exact (asan_memcpy48_contract_ex A Kc rho tp HKc). Qed.
End Contract48.
