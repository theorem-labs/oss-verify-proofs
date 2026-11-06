(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "ACEIL"; "@Corelib.Init.Datatypes"; "list"; "true"; "option"; "bool"; "cons"; "Some"; "nat"; "nil"; "pair"; "prod"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "sym_runA"; "ax_setS"; "la_state"; "entailsA"; "mkLeafA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sprop"; "ss_next"; "rm"; "sprop_below"; "rw"; "ss_objs"; "sv"; "SLit"; "enc_bytes"; "agree_below"; "ss_facts"; "ss_lenient"; "eval"; "holds"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow"; "W2"; "CUTS_S"; "FUEL_S"; "facts_S"; "E_f5"; "E_f8"; "RTCL"; "O_realms"; "PreS"; "T2_f5"; "T2_f8"; "XF_T2"; "R_f5"; "R_f8"; "rt_rng"; "s_f5"; "s_f8"; "T0_f5"; "T0_f8"; "T3_f5"; "T3_f8"; "musl_memset"; "objs4_f5"; "objs4_f8"; "sfin_f5"; "sfin_f8"; "N_rtc"; "PZ"; "T1_f5"; "T1_f8"; "ax_of"; "carve_S"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "of_nat"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "memset_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "acell"; "view"; "cell_ok"; "cells_ok"; "mkACell"; "G0"; "RTC_A"; "bview"; "cells_footb"; "rtc_cells_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface"; "L_set_shadow"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "jpredA"; "mat_blind"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_pure"; "KcA"; "J_pure_pre"; "Kc_ok"; "alloc_lawsA"; "client_addrA"; "top_var"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow.Contract"; "Jfix"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "ageom"; "aa_geom"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Lists.ListDef"; "map"; "nth"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "in_ranges"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "Zsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL MuslMemset ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2 AxXform MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ax_of (o : option axst) (d : axst) : axst := match o with Some a => a | None => d end.
Definition musl_memset : Z := 0xdb004.

Definition PreS (xx : Z) : axst := Pre_set_shadow AE_A xx.
Definition facts_S : list sprop := Eval vm_compute in ss_facts (ax_S (PreS 0xf5)).
Lemma facts_S_eq : ltac2:(tb__ "0|0|
S1eS0S7S22A1S2cS14S40R1A1A1A1S3bA3Fxx;"). Proof. reflexivity. Qed.

Definition N_rtc : list carve_spec := ltac2:(tb__ "0|7|
SbS10S10S10S28S1eA2M0S1eA2M1S7S10S10S1eSdA2M2S28A2M3A1M4A2M5SfG1G4SfG0S1eSfS28S1eS29Z0A1Ze6780M6A4Ze6788A4SbG3SfG2S28SfS1eSdG6U8A4S29S4dA1A4SeG3A1A3A4SeG5A1A3").
Definition O_realms : sobj := Eval vm_compute in carve_obj (SLit 0, 0xe6780, 0xe6788, [(0xe6780, 8%nat, SLit musl_memset)]).
Definition carve_S (S : sstate) : sstate := ltac2:(tb__ "0|0|
S30S33VS;A1S34VS;A1S32VS;A1S31VS;A1S35VS;A1S11S20S27VS;A1S8cSa0S20S9fS52A4A3S2cVS;A1S37S2dVS;A1A9").
Definition W2 (xx : Z) : axst := ltac2:(tb__ "0|1|
S17S40Vxx;A1M0S57S14G0A1A1A2").

Definition FUEL_S : nat := 20%nat.
Definition CUTS_S : list Z := [musl_memset].
Definition E_of (xx : Z) : axst := ltac2:(tb__ "0|2|
S9S7S15A1M0A1S13Lx;S16S5S3aS39S38Vxx;A1M1S8A5G0G0S13Ll;R1G1S15G0G0S13Ll0;R1S18R2A1S15G0G1Ll2;Ll1;X7x2Ll0;LL;X7x2Ll;G1X9x2").
Definition run_f5__R : option (list leafA) := ltac2:(tb__ "0|0|
S16S5S3aS39S38Zf5A1S8A5").
Local Strategy expand [run_f5__R].
Definition E_f5 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some [L] => la_state L | _ => W2 0xf5 end)) run_f5__R).
Definition run_f8__R : option (list leafA) := ltac2:(tb__ "0|0|
S16S5S3aS39S38Zf8A1S8A5").
Local Strategy expand [run_f8__R].
Definition E_f8 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some [L] => la_state L | _ => W2 0xf8 end)) run_f8__R).

Definition s_f5 : wsub := Eval vm_compute in infer_sub 1 (ax_S E_f5) (ax_S Pre_memsetA).
Definition s_f8 : wsub := Eval vm_compute in infer_sub 1 (ax_S E_f8) (ax_S Pre_memsetA).
Definition R_f5 : list sobj := Eval vm_compute in (match entails_frA E_f5 Pre_memsetA s_f5 with Some R => R | None => [] end).
Definition R_f8 : list sobj := Eval vm_compute in (match entails_frA E_f8 Pre_memsetA s_f8 with Some R => R | None => [] end).
Definition T0_f5 : axst := Eval vm_compute in import_postA s_f5 Pre_memsetA (liftA (P_ret_memset memset_entryA)) E_f5 R_f5.
Definition T0_f8 : axst := Eval vm_compute in import_postA s_f8 Pre_memsetA (liftA (P_ret_memset memset_entryA)) E_f8 R_f8.

Definition XF_T2 : list axform := ltac2:(tb__ "0|0|
SbS92S93SbSdU1SbSdU0SbSdU2SbSdU3SbSdU4SeSdA1A3A3A3A3A3A1SeS92A1A3").
Definition T2_of (T1 : axst) : axst := ltac2:(tb__ "0|0|
S56S91VT1;S43A2VT1;A2").
Definition T1_f5 : axst := ax_add_facts facts_S T0_f5.
Definition T1_f8 : axst := ax_add_facts facts_S T0_f8.
Definition T2_f5 : axst := Eval vm_compute in T2_of T1_f5.
Definition T2_f8 : axst := Eval vm_compute in T2_of T1_f8.
Definition objs4_f5 : list sobj := Eval vm_compute in firstn 4 (ss_objs (ax_S T2_f5)).
Definition objs4_f8 : list sobj := Eval vm_compute in firstn 4 (ss_objs (ax_S T2_f8)).
Definition T3_f5 : axst := Eval vm_compute in ax_setS T2_f5 (set_objs (ax_S T2_f5) objs4_f5).
Definition T3_f8 : axst := Eval vm_compute in ax_setS T2_f8 (set_objs (ax_S T2_f8) objs4_f8).
Definition sfin_f5 : wsub := Eval vm_compute in infer_sub NF (ax_S T3_f5) (ax_S (L_set_shadow 0xf5)).
Definition sfin_f8 : wsub := Eval vm_compute in infer_sub NF (ax_S T3_f8) (ax_S (L_set_shadow 0xf8)).

Lemma run_f5 : ltac2:(tb__ "0|1|
S0S9S7S15A1M0A1S16S5S3aS39S38Zf5A1S8A5ScG0SbS15S1aS3cS9aA2SeS15A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_f5__R <: run_f5__R = Some [mkLeafA E_f5 RsCut]). Qed.
Lemma run_f8 : ltac2:(tb__ "0|1|
S0S9S7S15A1M0A1S16S5S3aS39S38Zf8A1S8A5ScG0SbS15S1aS3dS9aA2SeS15A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_f8__R <: run_f8__R = Some [mkLeafA E_f8 RsCut]). Qed.
Lemma fr_f5 : ltac2:(tb__ "0|1|
S0S9S7S20A1M0A1S7bS3cS5dS47A3ScG0S44A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_f8 : ltac2:(tb__ "0|1|
S0S9S7S20A1M0A1S7bS3dS5dS48A3ScG0S45A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_f5 : ltac2:(tb__ "0|0|
S0SaS7aS3cS5dS47S44S8cS15S13S18S5eA4A5S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_f8 : ltac2:(tb__ "0|0|
S0SaS7aS3dS5dS48S45S8cS15S13S18S5eA4A5S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T0_f5_eq : ltac2:(tb__ "0|0|
S0S13S7cS47S5dS95S9cS5fA1A1S3cS44A5S49A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T0_f8_eq : ltac2:(tb__ "0|0|
S0S13S7cS48S5dS95S9cS5fA1A1S3dS45A5S4aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T2_f5_eq : ltac2:(tb__ "0|0|
S0S9S13A1S91S54S43A2ScS13S41A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T2_f8_eq : ltac2:(tb__ "0|0|
S0S9S13A1S91S55S43A2ScS13S42A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T2_f5_objs : ltac2:(tb__ "0|0|
S0S7S20A1S27S14S41A1A1S11S20S4eSbS20S3fSeS20A1A3A3A3"). Proof. reflexivity. Qed.
Lemma T2_f8_objs : ltac2:(tb__ "0|0|
S0S7S20A1S27S14S42A1A1S11S20S4fSbS20S3fSeS20A1A3A3A3"). Proof. reflexivity. Qed.
Lemma ent_f5 : ltac2:(tb__ "0|0|
S0SaS19S4bS70Zf5A1S50A3S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_f8 : ltac2:(tb__ "0|0|
S0SaS19S4cS70Zf8A1S51A3S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Local Notation "'UU' r i" := (bv_unsigned (rw r i)) (at level 10, r at level 9, i at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Lemma triple_pre : ltac2:(tb__ "0|1|
S60OF_;S61OS61S60R4R1A1R4F_;Fw;R3S63S5R6R5R3A4M0F_;G0F_;F_;FQ;FX;FP;Fok;").
Proof. intros ok P X Q HX H n Hg w Hw. exact (H (HX w Hw) n Hg w Hw). Qed.
Lemma etriple_pre : ltac2:(tb__ "0|2|
S60OF_;M0OG0S60R4R1A1R4F_;Fw;R3S62S5R5R3A3M1F_;G1F_;F_;FQ;FX;FP;").
Proof. intros P X Q HX H w Hw. exact (H (HX w Hw) w Hw). Qed.
Lemma rm_rho_sub : ltac2:(tb__ "0|0|
S21S99S0S1bQ40A1S9S1bQ8A1A1F_;S24S98R2R1A2A1S24R2A1A3Fs;Frho;"). Proof. reflexivity. Qed.
Lemma Forall_holds_agree : ltac2:(tb__ "0|1|
S1fS21S21S7S22A1S2bR4R3R2A3S0SaS8aS22S25R5A1R2A3S8A3S8eS22S2fR5A1M0R3A3S8eS22G0R4A3F_;F_;F_;FF;Frho';Frho;Fn;").
Proof.
  intros n rho rho' F Hag Hb HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree n rho rho' p Hag (proj1 (forallb_forall _ _) Hb p Hp))). exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.
Lemma Kc_mat_blind : ltac2:(tb__ "0|0|
S7fS81R1A1S76R2A1F_;FKc;").
Proof. intros Kc HK tr md l p. split; intros H; eapply Kc_ok_mat; eauto. Qed.

Lemma wok_of_imageA : ltac2:(tb__ "0|1|
S1bQ40M0A1S9S1bQ8A1A1F_;S1eS1S58Ze1000R1A2S5bR1Z643000A2A2S0SaS65S5R3S1cG0R2A2A3S8A3F_;Fz;Fm;").
Proof.
  intros m z Hz. unfold wok_of. destruct (m (Z_to_bv 64 z)); [reflexivity|].
  unfold wseg_addr. rewrite u64_lit by lia.
  destruct (ImageFacts.byte_cond_A z Hz) as [_ (seg & b & Hf & Hw & _)].
  change ImageFacts.segsA with segs in Hf. rewrite Hf. exact Hw.
Qed.
Definition RTCL (G : ageom) : list acell := rtc_cells_img RTC_A G.
Lemma rtc_nth2 : ltac2:(tb__ "0|0|
S88S0S9S66A1S8bS66S3eR1A1U2A3ScS66S6aZe6780U8S4dA3A2A3FG;"). Proof. intros G. reflexivity. Qed.
Lemma cell_of : ltac2:(tb__ "0|0|
S6dS88SdS66S69R4S3eR3A1A2S0S9S66A1S8bS66S3eR4A1R3A3ScS66R2A2A3S68R6R3A2F_;F_;Fc;Fn;FG;Fm;").
Proof. intros m G n c H Hn. exact (proj1 (Forall_forall _ _) H c (nth_error_In _ _ Hn)). Qed.
Lemma cell_rd : ltac2:(tb__ "0|3|
S1bQ40M0A1S9S1bQ8A1M1A1M2F_;S1eSdS1eS1eS68S67S5R5A2S6aR4R3R2A3A2S1S58R5R2A2S5bR2S59R5S5aR4A1A2A2A2S58Z0R6A2S58S59R7S5aR6A1A2S5cZ2Z40A2A2S2G1G1S0G2S64S5RaS1cG0R6A2A3ScG1R1A2A3Ly;A2F_;F_;F_;F_;Fz;Fv;Fk;Fa;Fm;").
Proof.
  intros m a k v z Hc Hz Ha1 Ha2. specialize (Hc (Z.to_nat (z - a)) ltac:(cbn [c_w]; lia)). cbn [c_addr c_w c_val] in Hc.
  rewrite view_in in Hc by lia. replace (a + Z.of_nat (Z.to_nat (z - a))) with z in Hc by lia. eexists. exact Hc.
Qed.
Lemma cell_civ : ltac2:(tb__ "0|5|
S21S1bQ40M0A1S9S1bQ8M1A1M2A1M3F_;S1eSdS1eS68S67S5R4A2S6aR3R2R1A3A2S58Z0M4R4A2S58S59R5S5aR4A1A2S5cZ2Z40A2A2SdS94R1R6A2S0G3S64S5R9S1cG0S59S59G4R8A2S5aR2A1A2A2A3ScG2S8dG2R2S2aR7S2eRaS29R6A1A2A2S1cG1G4A2A4A2A3F_;Fj;F_;F_;F_;Fv;Fk;Fa;Fm;Frho;").
Proof.
  intros rho m a k v Hc Ha1 Ha2 j Hj. specialize (Hc j Hj). cbn [c_addr c_w c_val] in Hc. rewrite view_in in Hc by lia.
  rewrite Z.add_0_l. cbn [eval]. exact Hc.
Qed.
Lemma rd_cell_eq : ltac2:(tb__ "0|9|
S1bQ40M0A1M1S9S1bQ8M2A1M3A1M4F_;M5G5S1eSdG1S1eSdS94R1R4A2S0G4S64S5R8S1cG0S59R6S5aR2A1M6A2A2A3ScG3S8dG3R2S2aR5R4A2S1cG2Z0A2M7A4A2A3F_;Fj;SdS94R1R5A2S0G4S64S5R8S1cG0S59R7G6A2A2A3ScG3S8dG3R2S2aR6R5A2G7A4A2A3F_;Fj;S1S58R6R3A2S5bR3S59R6S5aR5A1A2A2A2S0G4S64S5R9S1cG0R4A2M8A3S64S5R8G8A3A3F_;F_;F_;Fz;Fv;Fk;Fa0;Fm2;Fm1;").
Proof.
  intros m1 m2 a0 k v z H1 H2 Hz.
  replace z with (a0 + Z.of_nat (Z.to_nat (z - a0))) by lia.
  rewrite (H1 (Z.to_nat (z - a0))) by lia. rewrite (H2 (Z.to_nat (z - a0))) by lia. reflexivity.
Qed.

Definition rt_rng (a : Z) : Prop := 0xe6780 <= a < 0xe6788.
Lemma rt_footb : ltac2:(tb__ "0|0|
S1eS46R1A1S0SaS6eS6fS6cS6bA2R2A2S8A3F_;Fa;").
Proof.
  intros a Ha. unfold cells_footb. apply (proj2 (existsb_exists _ _)). exists (mkACell 0xe6780 8 musl_memset).
  split; [cbn; tauto|]. unfold in_cellb, rt_rng in *. cbn [c_addr c_w]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma in_ranges_R : ltac2:(tb__ "0|1|
S21S1bQ40M0A1S3S97R2SbS20S3fSeS20A1A3R1A3S46S1dG0R1A2A1A2Fa;Fr;").
Proof.
  intros r a. unfold in_ranges, rt_rng.
  assert (RG : obj_range r O_realms = (0xe6780, 0xe6788)).
  { unfold obj_range, obj_lo_of, obj_hi_of, O_realms. cbn [ob_base ob_lo ob_hi eval]. rewrite !soff_lit_small by lia. rewrite lit_unsigned. reflexivity. }
  split.
  - intros (o & [<-|[]] & Hr). rewrite RG in Hr. cbn [fst snd] in Hr. lia.
  - intros H. eexists. split; [left; reflexivity|]. rewrite RG. cbn [fst snd]. lia.
Qed.

Definition PZ (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S1S58S1dQ40M0S26Vrho;PdA2A2S5cZ2Z28A2A2S1S58Sa1S1dG0S26Vrho;PcA2A2A2S1S58S6S59S1dG0S26Vrho;PaA2A2S9eS1dG0S26Vrho;PfA2A2A1M1A2A2S58G1Z0A2A2A2A2").
Lemma PZ_of_pre : ltac2:(tb__ "0|0|
S75S1eS21S7S1bQ40A1A1S60S73S5R5S40R4A1R3R2R1A6S53R4A1F_;Fw;Ftp;Frho;Fxx;FJ;").
Proof.
  intros J xx rho tp [tr [ms md]] [(Hsm & HMI & Hwf & Hsh & Hhz) _].
  pose proof (smatch_facts_hold segs rho _ _ Hsm) as HF. cbn [ax_S PreS Pre_set_shadow] in HF.
  pose proof (urange (rw rho 13)) as R13. pose proof (urange (rw rho 12)) as R12. pose proof (urange (rw rho 10)) as R10. pose proof (urange (rw rho 15)) as R15.
  have_fact A1 HF (SPUle (SVar 13) (SLit (2 ^ 40))).
  have_fact A2 HF (SPUle (SLit SHADOW_OFF) (SVar 12)).
  have_fact A12 HF (SPUle (SLit 140735332483072) (SAlu ALU_ADD (SVar 10) (SVar V_DEPTH))).
  have_fact A13 HF (SPBranch BC_GE (SLit (- set_shadow_depth)) (SVar V_DEPTH)).
  cbn [eval] in A1, A2, A12. rewrite add_val in A12. rewrite !lit_unsigned in A1, A2, A12.
  unfold SHADOW_OFF in A2.
  rewrite !Z.mod_small in A1, A2 by lia. rewrite (Z.mod_small 140735332483072) in A12 by lia.
  unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S PreS Pre_set_shadow] in Hsm.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
  apply Forall_inv in Hall. unfold obj_holds, obj_lo_of, obj_hi_of, stack_win in Hall. cbn [ob_base ob_lo ob_hi eval] in Hall.
  destruct Hall as ((B1 & _ & _ & _) & _). unfold soff in B1. cbn [eval] in B1. rewrite bv_signed_U in B1.
  cbn [holds branch_taken eval] in A13. unfold bv_lts in A13. rewrite !bv_signed_U in A13. rewrite lit_unsigned in A13.
  unfold set_shadow_depth in A13. change ((- 0) mod 2 ^ 64) with 0 in A13.
  destruct (Z.ltb_spec (Zsigned 0) (Zsigned (UU rho V_DEPTH))) as [Hlt|Hge]; [discriminate A13|].
  destruct (Zsigned_spec 0) as [[_ E0]|[X _]]; [rewrite E0 in Hge | lia].
  unfold V_DEPTH in *. unfold PZ, ACEIL, SHADOW_OFF.
  destruct (Zsigned_spec (UU rho 15)) as [[X15 E15]|[X15 E15]]; rewrite E15 in Hge, B1 |- *.
  - assert (UU rho 15 = 0) by lia. rewrite H in A12 |- *. rewrite Z.add_0_r, Z.mod_small in A12 by lia. lia.
  - replace ((UU rho 10 + UU rho 15) mod 2 ^ 64) with (UU rho 10 + UU rho 15 - 2 ^ 64) in A12; [lia|].
    symmetry. replace (UU rho 10 + UU rho 15) with ((UU rho 10 + UU rho 15 - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma swf_W2 : ltac2:(tb__ "0|0|
S1eS0SaS36S14S38R1A1A1A1S8A3Fxx;"). Proof. intros xx. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma facts_S_belowNF : ltac2:(tb__ "0|0|
S0SaS8aS22S25S37A1S3bA3S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma SPA_W2_of_pre : ltac2:(tb__ "0|0|
S75S1eS21S7S1bQ40A1A1S60S88S69S67S5S24R4A1A2S3eR1A1A2S73S5R7S40R6A1R5R4R3A6S73S5R8S38R7A1R6R5R4A6F_;F_;FG;Fw;Ftp;Frho;Fxx;FJ;").
Proof.
  intros J xx rho tp w G HR HS. pose proof (PZ_of_pre J xx rho tp w HS) as (P1 & P2 & P3 & P4).
  pose proof (urange (rw rho 10)) as R10. pose proof (urange (rw rho 12)) as R12. pose proof (urange (rw rho 13)) as R13.
  unfold ACEIL in P3.
  pose proof (cell_of _ G _ _ HR (rtc_nth2 G)) as C2.
  unfold W2, carve_S.
  apply (SPA_carve_list segs J rho (PreS xx) tp w N_rtc NF HS (swf_W2 xx) ltac:(apply Pos.le_refl)).
  - unfold N_rtc. repeat apply Forall_cons; try apply Forall_nil; cbv beta iota zeta; cbn [eval];
      rewrite !lit_unsigned; rewrite !(Z.mod_small 0) by lia.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
    split; [intros off Hoff; split; [apply wok_of_imageA; lia | eapply (cell_rd _ _ _ _ _ C2); cbn; lia]|].
    split; [unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; intros j Hj; apply (cell_civ rho _ _ _ _ C2); cbn; lia|].
    intros rr y j Hin. destruct Hin.
  - destruct HS as [(Hsm1 & _) _]. unfold virt in Hsm1. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm1.
    destruct Hsm1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
    cbn [ax_S PreS Pre_set_shadow ss_objs] in Hall |- *.
    pose proof (Zsigned_spec (UU rho 13)) as Z13.
    unfold N_rtc. cbn [map carve_obj carved lit_cells app].
    unfold PZ, SHADOW_OFF in P2.
    repeat apply Forall_cons; try apply Forall_nil;
      unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of, carved, stack_win, Iface.O_got, Iface.O_rtc, Code.O_got, Code.O_rtc,
             Iface.GOT_LO, Iface.GOT_HI, Iface.RTC_LO, Iface.RTC_HI, Code.GOT_LO, Code.GOT_HI, Code.RTC_LO, Code.RTC_HI;
      cbn [ob_base ob_lo ob_hi fst snd];
      rewrite ?soff_lit_small by lia; unfold soff; cbn [eval]; rewrite ?bv_signed_U; rewrite ?lit_unsigned; rewrite ?(Z.mod_small 0) by lia;
      unfold V_DEPTH in *; lia.
  - unfold N_rtc. cbn [map carve_obj pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.

Section Contract.
Variable AInvA : ltac2:(tb__ "0|0|
S87S21S7S1bQ40A1A1S8fOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S82S5VAInvA;VCST;A3").

Definition law_view_stmt : Prop := ltac2:(tb__ "0|1|
S87S21S21S7S1bQ40A1M0A1S8fVAInvA;R5R4R2R1A4G0S0S9S1bQ8A1A1S64S5S24R5A1R1A3S64S5S24R6A1R1A3A3Fa;VAInvA;R7R5R4R3A4F_;F_;Fmd;Ftp;Frho';Frho;FA;").
Hypothesis HLV : law_view_stmt.
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Definition Jfix (A : AA) (Kc : KcA) (rho0 : valuation) (tp0 : list word) : jpredA := ltac2:(tb__ "0|1|
S21S7S1bQ40A1A1M0S7S90A1S8fS1VAInvA;VA;Vrho0;R3R1A4S1VKc;R2R1A2S1S85VA;Vrho0;A2S1S84VA;Vrho0;A2S0G0R3Vtp0;A3A2A2A2A2Lmd;Ltr;Lt;L_;").

Lemma Jfix_stable : ltac2:(tb__ "0|0|
S87S7fS21S7S1bQ40A1A1S1fS81R4A1S77S5R2S86R6R5R4R3A4A3F_;Fn;Ftp0;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 tp0 n HKc rho rho' tp tr md md' Hag Hme (HA & HK & Htp & Htv & ->).
  split; [eapply (law_mat _ _ _ ALA); [exact HA | exact Hme]|].
  split; [eapply mat_blind_equiv; [apply Kc_mat_blind; exact HKc | exact Hme | exact HK]|].
  split; [exact Htp|]. split; [exact Htv | reflexivity].
Qed.
Lemma Jfix_okf : ltac2:(tb__ "0|0|
S60OF_;S87S7fS21S7S1bQ40A1A1S74S5R5S80VAInvA;R4R3A3A3S74S5R6S86R5R4R3R2A4A3F_;Ftp0;Frho0;FKc;FA;Fok;").
Proof. intros ok A Kc rho0 tp0 H rho tp tr ms md msv' (HA & HK & Htp & Htv & ->). eapply (H rho0); eauto. exact (conj HA (conj HK (conj Htp Htv))). Qed.

Lemma client_not_rt : ltac2:(tb__ "0|0|
S87S21S7S1bQ40A1A1S8fS1eVAInvA;R5R4R3R2A4S83VCST;R6R2A3S4S46R3A1A1F_;F_;Fa;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md a HA Hcl Hr.
  destruct (law_blocks _ _ _ ALA A rho tp md HA) as (_ & HB & HFr). pose proof (topG_range (aa_geom A)) as TG. unfold HIGH_SHADOW_END, IMG_HI in *.
  destruct Hcl as [[S|[L|[F|C]]]|FL].
  - unfold rt_rng in Hr. lia.
  - destruct L as (b & n & Hbn & Hx). destruct (HB b n Hbn) as (B1 & B2 & B3 & B4 & B5). unfold rt_rng in Hr. lia.
  - destruct F as (f & s & Hfs & Hx). destruct (HFr f s Hfs) as (F1 & F2 & F3 & F4 & _). unfold rt_rng in Hr. lia.
  - destruct (HCST a C) as [_ Hf]. rewrite (rt_footb a Hr) in Hf. discriminate.
  - destruct FL as (fs & Hfs & ->). destruct fs as [f s]. destruct (HFr f s Hfs) as (F1 & F2 & F3 & F4 & F5 & F6 & _). unfold rt_rng in Hr. lia.
Qed.

Section Inst.
Variable xx : Z.
Variables (E T0 T2 T3 : axst) (s sfin : wsub) (R objs4 : list sobj).
Hypothesis Hrun : ltac2:(tb__ "0|1|
S0S9S7S15A1M0A1S16S5S3aS39S38Vxx;A1S8A5ScG0SbS15S1aVE;S9aA2SeS15A1A3A2A3").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0S9S7S20A1M0A1S7bVE;S5dVs;A3ScG0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S0SaS7aVE;S5dVs;VR;S8cS15S13S18S5eA4A5S8A3").
Hypothesis HT0 : ltac2:(tb__ "0|0|
S0S13S7cVs;S5dS95S9cS5fA1A1VE;VR;A5VT0;A3").
Hypothesis HT2 : ltac2:(tb__ "0|0|
S0S9S13A1S91S9dS3bVT0;A2S43A2ScS13VT2;A2A3").
Hypothesis HT2o : ltac2:(tb__ "0|0|
S0S7S20A1S27S14VT2;A1A1S11S20Vobjs4;SbS20S3fSeS20A1A3A3A3").
Hypothesis HT3 : ltac2:(tb__ "0|0|
S0S13S17VT2;S9bS14VT2;A1Vobjs4;A2A2VT3;A3").
Hypothesis Hent : ltac2:(tb__ "0|0|
S0SaS19VT3;S70Vxx;A1Vsfin;A3S8A3").
Hypothesis HnE : ltac2:(tb__ "0|0|
S0S1fS23S14VE;A1A1S37A3").
Hypothesis HbT0 : ltac2:(tb__ "0|0|
S0SaS8aS22S25S23S14VT0;A1A1A1S3bA3S8A3").
Hypothesis Hids : ltac2:(tb__ "0|0|
S0SaS96Vsfin;S37A2S8A3").

Lemma lenW2 : ltac2:(tb__ "0|0|
S0SaS2dS14S38Vxx;A1A1A1S12A3"). Proof. reflexivity. Qed.
Lemma nxW2 : ltac2:(tb__ "0|0|
S0S1fS23S14S38Vxx;A1A1A1S37A3"). Proof. reflexivity. Qed.

Section Run.
Variables (A : AA) (Kc : KcA) (rho : valuation) (tp : list word).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HR : ltac2:(tb__ "0|0|
S69S67S5S24Vrho;A1A2S3eS89VA;A1A1A2").
Hypothesis HFS : Forall (holds rho) facts_S.

Lemma cont_post : ltac2:(tb__ "0|1|
S21S7S1bQ40A1A1S60S2bS37Vrho;R3A3S73S5S86VA;VKc;Vrho;Vtp;A4VT0;R4R3R2A6S79S5S37Vrho;Vtp;SbS10S13S78A2M0SfS13S78S70Vxx;A1S7eVAInvA;VCST;VXGL;VA;VKc;A5A4SeG0A1A3R3A6F_;F_;Fw;FtpL;Frho';").
Proof.
  intros rho' tpL [tr [ms md]] Hag HS0.
  pose proof (proj2 HS0) as HJ0. cbn [w_tr w_cfg cfg_model fst snd] in HJ0. destruct HJ0 as (HA & HK & Htp & Htv & EtpL). subst tpL.
  pose proof Hag as (Hrw & Hrl & Hrm).
  assert (HS1 : SPA segs (Jfix A Kc rho tp) (ax_add_facts facts_S T0) rho' tp (tr, mkCfg ms md)).
  { split; [|exact (proj2 HS0)]. apply smatchA_add_facts; [exact (proj1 HS0) | | exact HbT0].
    apply (Forall_holds_agree NF rho rho'); [exact Hag | exact facts_S_belowNF | exact HFS]. }
  pose proof (SPA_axforms segs _ XF_T2 rho' _ T2 tp _ HT2 HS1) as HS2.
  pose proof (SPA_unobj segs (Jfix A Kc rho tp) rho' T2 objs4 [O_realms] tp tr ms md HT2o HS2) as HS3. cbn zeta in HS3.
  set (rho'' := rho_absorb rho' [O_realms] (vms md tp ms)) in HS3.
  specialize (HS3 (fun H => H)). rewrite HT3 in HS3.
  destruct HS3 as [Hsm3 HJ3].
  pose proof (smatchA_entails segs T3 (L_set_shadow xx) sfin rho'' tp _ Hent Hsm3) as HsmL.
  assert (RMout : forall a, ~ rt_rng (bv_unsigned a) -> rm rho'' a = rm rho a).
  { intros a Ha. unfold rho''. rewrite rm_absorb_out; [symmetry; apply Hrm|]. intros Hi. apply Ha. apply (in_ranges_R rho'). exact Hi. }
  exists (L_set_shadow xx), (JL_pure AInvA CST XGL A Kc), (rho_sub rho'' sfin), tp.
  split; [left; reflexivity|]. split.
  - apply (agree_vals_trans NF rho rho'' (rho_sub rho'' sfin)).
    + split; [intros i Hi; unfold rho''; cbn [rho_absorb rw]; apply Hrw; exact Hi | intros l; unfold rho''; cbn [rho_absorb rl]; apply Hrl].
    + apply agree_below_vals. apply rho_sub_agree. exact Hids.
  - split; [exact HsmL|]. cbn [w_tr w_cfg cfg_model fst snd]. unfold JL_pure.
    split.
    +
      eapply (law_vars _ _ _ ALA); [|apply rm_rho_sub]. apply (HLV A rho rho'' tp md HA). intros a.
      destruct (in_ranges_dec rho' [O_realms] a) as [Hin|Hout].
      * pose proof (proj1 (proj1 HS2)) as Hsm2. unfold virt in Hsm2. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm2.
        pose proof (absorb_carved_cells segs rho' (ax_S T2) tr (vms md tp ms) (vmd md) objs4 [O_realms] (SLit 0) 0xe6780 0xe6788
                      [(0xe6780, 8%nat, SLit musl_memset)] Hsm2 HT2o ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)) as [CV _].
        apply Forall_cons_iff in CV as [CV1 _]. cbn [eval] in CV1. rewrite lit_unsigned in CV1. change (0 mod 2 ^ 64) with 0 in CV1.
        apply (in_ranges_R rho') in Hin. rewrite <- (Z_to_bv_bv_unsigned 64 a).
        pose proof (cell_of _ (aa_geom A) _ _ HR (rtc_nth2 (aa_geom A))) as C2.
        apply (rd_cell_eq _ _ 0xe6780 8 (Z_to_bv 64 musl_memset)); [intros j Hj; rewrite <- (CV1 j Hj); f_equal; f_equal; lia | | unfold rt_rng in Hin; lia].
        intros j Hj. pose proof (C2 j Hj) as Y. cbn [c_addr c_w c_val] in Y. rewrite view_in in Y by lia. exact Y.
      * unfold rd_of. unfold rho''. rewrite (rm_absorb_out rho' [O_realms] _ a Hout). rewrite <- (Hrm a). reflexivity.
    + split; [reflexivity|]. split; [|exact HK].
      rewrite rm_rho_sub. split.
      * intros a Ha Hc. apply RMout. rewrite u64_lit by lia. intros Hr.
        destruct Hc as [[Hcl _]|[Hsh _]].
        -- exact (client_not_rt A rho tp md a HA Hcl Hr).
        -- destruct Hsh as [(x & Hx & ->)|(x & Hx & ->)].
           ++ pose proof (topG_range (aa_geom A)) as TG.
              destruct (law_client_app _ _ _ ALA A rho tp md x HA Hx) as [X|[X|X]]; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI, Sh, SHADOW_OFF, rt_rng in *;
                pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia.
           ++ destruct (HXGL x Hx). unfold IMG_HI, Sh, SHADOW_OFF, rt_rng in *.
              pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia.
      * intros x j Hx Hj Hdef.
        assert (X0 : 0 <= x < 2 ^ 47).
        { destruct Hx as [[Hcl _]|Hgl].
          - pose proof (topG_range (aa_geom A)) as TG. destruct (law_client_app _ _ _ ALA A rho tp md x HA Hcl) as [X|[X|X]]; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI in *; lia.
          - destruct (HXGL x Hgl). unfold IMG_HI in *. lia. }
        rewrite RMout; [exact Hdef|]. unfold word_byte. rewrite u64_lit.
        2:{ unfold Sh, SHADOW_OFF. pose proof (Z.div_mod (x / 8 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 8 + 2147450880) 8 ltac:(lia)).
            assert (0 <= x / 8 <= 2 ^ 47) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). lia. }
        unfold Sh, SHADOW_OFF, rt_rng. pose proof (Z.div_mod (x / 8 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 8 + 2147450880) 8 ltac:(lia)).
        assert (0 <= x / 8) by (apply Z.div_pos; lia). lia.
Qed.

Lemma inst_sound : ltac2:(tb__ "0|1|
S60OF_;S74S5R1S80VAInvA;VA;VKc;A3A3S63S5R2S73S5S86VA;VKc;Vrho;Vtp;A4S38Vxx;A1Vrho;Vtp;A5S79S5S37Vrho;Vtp;SbS10S13S78A2M0SfS13S78S70Vxx;A1S7eVAInvA;VCST;VXGL;VA;VKc;A5A4SeG0A1A3A5A4F_;Fok;").
Proof.
  intros ok Hokf.
  eapply (runA_tr segs ok FUEL_S CUTS_S (W2 xx) _ (Jfix A Kc rho tp) rho tp); [exact Hrun | exact lenW2 | apply Jfix_okf; exact Hokf | apply Jfix_stable; exact HKc |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite nxW2 in Hag1.
  apply (call_soundA segs ok (Jfix A Kc rho tp) (Jfix A Kc rho tp) (Jfix A Kc rho tp) (Jfix A Kc rho tp) E Pre_memsetA s R Posts_memsetA _ rho1 tp Hfr Hcc).
  - intros rho2 tp2. apply memset_sumA; [apply Jfix_okf; exact Hokf | apply Jfix_stable; exact HKc].
  - intros tr ms md _ HJ. exact HJ.
  - intros L rho' rhoL tpL tr ms md tr' md' _ _ _ _ HJ. exact HJ.
  - intros L rho' tpL HinL Hag. destruct HinL as [<-|[]]. cbn [la_state liftLA lf_state]. rewrite HT0.
    eapply triple_conseq; [ | | apply triple_refl]; [intros w Hw; exact Hw|].
    intros w Hw. apply (cont_post rho' tpL w); [|exact Hw]. rewrite HnE in Hag. eapply agree_below_trans; [exact Hag1 | exact Hag].
Qed.

Lemma inst_complete : ltac2:(tb__ "0|1|
S62S5S73S5S86VA;VKc;Vrho;Vtp;A4S38Vxx;A1Vrho;Vtp;A5S79S5S37Vrho;Vtp;SbS10S13S78A2M0SfS13S78S70Vxx;A1S7eVAInvA;VCST;VXGL;VA;VKc;A5A4SeG0A1A3A5A3").
Proof.
  eapply (erunA_tr segs FUEL_S CUTS_S (W2 xx) _ (Jfix A Kc rho tp) rho tp); [exact Hrun | exact lenW2 | apply Jfix_stable; exact HKc |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite nxW2 in Hag1.
  apply (call_completeA segs (Jfix A Kc rho tp) (Jfix A Kc rho tp) (Jfix A Kc rho tp) (Jfix A Kc rho tp) E Pre_memsetA s R Posts_memsetA _ rho1 tp Hfr Hcc).
  - intros rho2 tp2. apply memset_sumA_ex. apply Jfix_stable; exact HKc.
  - intros tr ms md _ HJ. exact HJ.
  - intros L rho' rhoL tpL tr ms md tr' md' _ _ _ _ HJ. exact HJ.
  - intros L rho' tpL HinL Hag. destruct HinL as [<-|[]]. cbn [la_state liftLA lf_state]. rewrite HT0.
    eapply etriple_conseq; [ | | apply etriple_refl]; [intros w Hw; exact Hw|].
    intros w Hw. apply (cont_post rho' tpL w); [|exact Hw]. rewrite HnE in Hag. eapply agree_below_trans; [exact Hag1 | exact Hag].
Qed.
End Run.

Theorem inst_contract : ltac2:(tb__ "0|0|
S71S5S7dVAInvA;VCST;VXGL;Vxx;A6").
Proof.
  intros ok A Kc rho tp HKc Hokf.
  apply (triple_pre ok _ (cells_ok (view segs (rm rho)) (RTCL (aa_geom A)) /\ Forall (holds rho) facts_S)).
  { intros w [Hsm HJ]. pose proof HJ as (HA & _ & _). split; [exact (law_rtc _ _ _ ALA A rho tp _ HA)|].
    rewrite <- (facts_S_eq xx). exact (SPA_facts_hold segs _ rho (PreS xx) tp w (conj Hsm HJ)). }
  intros [HR HFS].
  eapply triple_conseq; [ | intros w Hw; exact Hw | apply (inst_sound A Kc rho tp HKc HR HFS ok Hokf)].
  intros w Hw. apply (SPA_W2_of_pre _ xx rho tp w (aa_geom A) HR).
  destruct Hw as [Hsm (HA & HK & Htp & Htv)]. split; [exact Hsm|]. exact (conj HA (conj HK (conj Htp (conj Htv eq_refl)))).
Qed.

Theorem inst_contract_ex : ltac2:(tb__ "0|0|
S72S5S7dVAInvA;VCST;VXGL;Vxx;A6").
Proof.
  intros A Kc rho tp HKc.
  apply (etriple_pre _ (cells_ok (view segs (rm rho)) (RTCL (aa_geom A)) /\ Forall (holds rho) facts_S)).
  { intros w [Hsm HJ]. pose proof HJ as (HA & _ & _). split; [exact (law_rtc _ _ _ ALA A rho tp _ HA)|].
    rewrite <- (facts_S_eq xx). exact (SPA_facts_hold segs _ rho (PreS xx) tp w (conj Hsm HJ)). }
  intros [HR HFS].
  eapply etriple_conseq; [ | intros w Hw; exact Hw | apply (inst_complete A Kc rho tp HKc HR HFS)].
  intros w Hw. apply (SPA_W2_of_pre _ xx rho tp w (aa_geom A) HR).
  destruct Hw as [Hsm (HA & HK & Htp & Htv)]. split; [exact Hsm|]. exact (conj HA (conj HK (conj Htp (conj Htv eq_refl)))).
Qed.
End Inst.

Lemma nxE_f5 : ltac2:(tb__ "0|0|
S0S1fS23S14S3cA1A1S37A3"). Proof. reflexivity. Qed.
Lemma nxE_f8 : ltac2:(tb__ "0|0|
S0S1fS23S14S3dA1A1S37A3"). Proof. reflexivity. Qed.
Lemma bT0_f5 : ltac2:(tb__ "0|0|
S0SaS8aS22S25S23S14S49A1A1A1S3bA3S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma bT0_f8 : ltac2:(tb__ "0|0|
S0SaS8aS22S25S23S14S4aA1A1A1S3bA3S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_f5 : ltac2:(tb__ "0|0|
S0SaS96S50S37A2S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_f8 : ltac2:(tb__ "0|0|
S0SaS96S51S37A2S8A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T3_f5_eq : ltac2:(tb__ "0|0|
S0S13S17S41S9bS14S41A1S4eA2A2S4bA3"). Proof. reflexivity. Qed.
Lemma T3_f8_eq : ltac2:(tb__ "0|0|
S0S13S17S42S9bS14S42A1S4fA2A2S4cA3"). Proof. reflexivity. Qed.

Theorem set_shadow_f5_contract : ltac2:(tb__ "0|0|
S71S5S7dVAInvA;VCST;VXGL;Zf5A6").
Proof. exact (inst_contract 0xf5 E_f5 T0_f5 T2_f5 T3_f5 s_f5 sfin_f5 R_f5 objs4_f5 run_f5 fr_f5 cc_f5 T0_f5_eq T2_f5_eq T2_f5_objs T3_f5_eq ent_f5 nxE_f5 bT0_f5 ids_f5). Qed.
Theorem set_shadow_f5_contract_ex : ltac2:(tb__ "0|0|
S72S5S7dVAInvA;VCST;VXGL;Zf5A6").
Proof. exact (inst_contract_ex 0xf5 E_f5 T0_f5 T2_f5 T3_f5 s_f5 sfin_f5 R_f5 objs4_f5 run_f5 fr_f5 cc_f5 T0_f5_eq T2_f5_eq T2_f5_objs T3_f5_eq ent_f5 nxE_f5 bT0_f5 ids_f5). Qed.
Theorem set_shadow_f8_contract : ltac2:(tb__ "0|0|
S71S5S7dVAInvA;VCST;VXGL;Zf8A6").
Proof. exact (inst_contract 0xf8 E_f8 T0_f8 T2_f8 T3_f8 s_f8 sfin_f8 R_f8 objs4_f8 run_f8 fr_f8 cc_f8 T0_f8_eq T2_f8_eq T2_f8_objs T3_f8_eq ent_f8 nxE_f8 bT0_f8 ids_f8). Qed.
Theorem set_shadow_f8_contract_ex : ltac2:(tb__ "0|0|
S72S5S7dVAInvA;VCST;VXGL;Zf8A6").
Proof. exact (inst_contract_ex 0xf8 E_f8 T0_f8 T2_f8 T3_f8 s_f8 sfin_f8 R_f8 objs4_f8 run_f8 fr_f8 cc_f8 T0_f8_eq T2_f8_eq T2_f8_objs T3_f8_eq ent_f8 nxE_f8 bT0_f8 ids_f8). Qed.
End Contract.
