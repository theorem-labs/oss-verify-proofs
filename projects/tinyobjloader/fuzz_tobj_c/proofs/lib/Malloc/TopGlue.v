(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sprop"; "sstate"; "SVar"; "smatch"; "ss_facts"; "SAlu"; "SPUle"; "holds"; "sobj"; "ss_objs"; "swf"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_pc"; "ss_regs"; "ss_resv"; "@Corelib.Init.Datatypes"; "list"; "cons"; "prod"; "nil"; "app"; "bool"; "pair"; "true"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_L"; "layout_extends"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_DEPTH"; "J_alloc_preT"; "top_high"; "J_free_preT"; "Pre_callocI"; "Pre_freeI"; "Pre_mallocI"; "ok_sideK"; "vm_insensitive"; "JL_free"; "J_alloc_pre"; "L_free"; "Posts_calloc"; "Posts_malloc"; "V_TOP"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "F_top"; "J_free_pre"; "Pre_calloc"; "Pre_free"; "Pre_malloc"; "calloc_contract"; "calloc_contract_ex"; "free_contract"; "free_contract_ex"; "malloc_contract"; "malloc_contract_ex"; "stack_win"; "top_var"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "jpost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "le"; "pow"; "@Stdlib.Lists.List"; "incl"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "topL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TopGlue"; "refacts"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundR SymFrame SymSummary SymCall ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocIface Contract ZEval.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition refacts (S : sstate) (F : list sprop) : sstate := ltac2:(tb__ "0|0|
SdS12VS;A1S13VS;A1SfVS;A1SeVS;A1S14VS;A1SbVS;A1VF;S11VS;A1S10VS;A1A9").

Lemma swf_refacts : ltac2:(tb__ "0|0|
S3S15S2A1S45S1aScR2A1S1cA3S53S2R2S6R3A1A3S45S1aScS58R4R3A2A1S1cA3F_;F_;FF;FS;").
Proof.
  intros S F H HI. unfold swf in *. cbn [refacts ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts].
  apply andb_prop in H as [H Hf]. rewrite H. cbn [andb].
  apply forallb_forall. intros p Hp. apply (proj1 (forallb_forall _ _) Hf). apply HI. exact Hp.
Qed.

Lemma smatch_refacts : ltac2:(tb__ "0|0|
S15S59A1S0S3S15S2A1S17S15S22A1S55A2S53S2R2S6R3A1A3S5R6R5R4R2A4S5R7R6S58R5R4A2R3A4F_;F_;Fw;FF;FS;Frho;Fsegs;").
Proof.
  intros segs rho S F w HI Hsm.
  pose proof Hsm as (Hwf & Hpc & Hpend & Hidle & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  unfold smatch. cbn [refacts ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split; [apply swf_refacts; [exact Hwf | exact HI]|].
  repeat (split; [assumption|]).
  apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) Hfacts). apply HI. exact Hp.
Qed.

Lemma top_high_of_facts : ltac2:(tb__ "0|4|
S1eS0S9R1S8S4S32A1S7S56S4PaM0A1S4S24A1A3A2A2S51Z0M1S4fS43Q40M2S1R2G0A2A2S4eZ40M3S43G2S1R2S24A2A2A2A2A2S50S4eG3S43G2S1R3S24A2A2A2G1A2S42R5R4A2S26R6R5A2F_;F_;F_;F_;Frho;FA;").
Proof.
  intros A rho H Hlo Hneg HT. unfold top_high. unfold top_var in HT. rewrite <- HT.
  rewrite (holds_zholds rho) in H by reflexivity. cbn [zholds zeval zalu] in H. unfold zr_of in H.
  set (u10 := bv_unsigned (rw rho 10%positive)) in *. set (u15 := bv_unsigned (rw rho V_DEPTH)) in *.
  set (u30 := bv_unsigned (rw rho V_TOP)) in *.
  pose proof (urange (rw rho 10%positive)) as U10. pose proof (urange (rw rho V_DEPTH)) as U15. pose proof (urange (rw rho V_TOP)) as U30.
  fold u10 in U10. fold u15 in U15. fold u30 in U30.
  rewrite (Z.mod_small u10), (Z.mod_small u15), (Z.mod_small u30) in H by lia.
  assert (E : u15 = toS 64 u15 + 2 ^ 64).
  { unfold toS in *. rewrite Z.mod_small in * by lia. change (2 ^ (64 - 1)) with (2 ^ 63) in *.
    destruct (u15 <? 2 ^ 63) eqn:C; [|lia]. apply Z.ltb_lt in C. exfalso. lia. }
  rewrite E in H. replace (u10 + (toS 64 u15 + 2 ^ 64)) with ((u10 + toS 64 u15) + 1 * 2 ^ 64) in H by lia.
  rewrite Z.mod_add in H by lia. rewrite Z.mod_small in H; [exact H|].
  unfold toS in *. rewrite Z.mod_small in * by lia. change (2 ^ (64 - 1)) with (2 ^ 63) in *.
  destruct (u15 <? 2 ^ 63) eqn:C; lia.
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable C : mconsts.
Variable E : entry_consts.

Lemma pre_window : ltac2:(tb__ "0|5|
S0S54S3S17S15S22A1S55A2S46S50Z0M0R3A2S50R3S52Z2Z28A2A2A2S5Vsegs;R5R3R2A4S47S15SaA1M1G1S45G1SbR5A1S16SaS41R6A1R1A3A3Lrest;A2S53S2S19S2S16S2S34S16S2S35R6A1S18S2A1A3A3S19S2S33R6A1S36A3A3S6R5A1A3S46S51G0S4fS43Q40M2S1R8PaM3A2A2S4eZ40S43G2S1R8S24A2A2A2M4A2A2S46S50G4G0A2S9R8S8S4S32A1S7S56S4G3A1S4S24A1A3A2A2A2A2F_;F_;F_;F_;Fw;FS;Fd;Frho;").
Proof.
  intros rho d S w Hd Hsm [rest Hobjs] HI.
  pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & Hfacts).
  rewrite Hobjs in Hall. pose proof (proj1 (Forall_forall _ _) Hall (stack_win d) ltac:(left; reflexivity)) as ((Hb & _) & _).
  unfold obj_lo_of, stack_win in Hb. cbn [ob_base ob_lo eval] in Hb. unfold soff in Hb. cbn [eval] in Hb.
  rewrite bv_signed_toS in Hb by (cbn; lia). change (Z.of_N 64) with 64 in Hb.
  assert (F : forall p, In p ([F_sp_aligned; F_sp_high d] ++ F_depth d ++ F_top) -> SymState.holds rho p).
  { intros p Hp. apply (proj1 (Forall_forall _ _) Hfacts). apply HI. exact Hp. }
  assert (H1 : SymState.holds rho (SPBranch BC_GE (SLit (- d)) (SVar V_DEPTH))) by (apply F; cbn; tauto).
  rewrite (holds_zholds rho) in H1 by reflexivity. cbn [zholds zcond zeval] in H1. unfold zr_of in H1.
  pose proof (urange (rw rho V_DEPTH)) as U15. set (u15 := bv_unsigned (rw rho V_DEPTH)) in *.
  rewrite (toS_mod 64 u15) in H1 by lia.
  assert (T1 : toS 64 ((- d) mod 2 ^ 64) = - d).
  { unfold toS. rewrite (Z.mod_small ((- d) mod 2 ^ 64)) by (apply Z.mod_pos_bound; lia).
    replace ((- d) mod 2 ^ 64) with (2 ^ 64 - d) by (Z.to_euclidean_division_equations; lia).
    destruct (2 ^ 64 - d <? 2 ^ (64 - 1)) eqn:X; [apply Z.ltb_lt in X; exfalso; change (2 ^ (64 - 1)) with (2 ^ 63) in X; lia | lia]. }
  rewrite T1 in H1. apply Bool.negb_true_iff in H1. apply Z.ltb_ge in H1.
  split; [exact Hb|]. split; [lia|]. apply F. unfold F_top. rewrite !in_app_iff. cbn. tauto.
Qed.

Lemma SPJ_malloc_T : ltac2:(tb__ "0|0|
S1eS15S22A1S23OF_;F_;S0S48S21Vsegs;S2eVsegs;VC;R4R3A4S3aVE;A1R2R1A5S21Vsegs;S25Vsegs;VC;R5R4A4S2aVE;A1R3R2A5F_;Fw;Frho;FKc;FA;").
Proof.
  intros A Kc rho w [Hsm (HM & HK & HT & HI & HV)].
  assert (W := pre_window rho malloc_stack (Pre_malloc E) w ltac:(unfold malloc_stack; lia) Hsm
                 ltac:(eexists; reflexivity) ltac:(intros p Hp; exact Hp)).
  destruct W as (Wlo & Wneg & Wf).
  split.
  - change (Pre_mallocI E) with (refacts (Pre_malloc E) ([F_sp_aligned; F_sp_high malloc_stack] ++ F_depth malloc_stack)).
    apply smatch_refacts; [|exact Hsm]. intros p Hp. cbn [ss_facts Pre_malloc]. rewrite !in_app_iff in *. tauto.
  - split; [exact HM|]. split; [exact HK|]. split; [exact HT|]. split; [exact HI|].
    exact (top_high_of_facts A rho Wf Wlo Wneg HV).
Qed.

Lemma SPJ_calloc_T : ltac2:(tb__ "0|0|
S1eS15S22A1S23OF_;F_;S0S48S21Vsegs;S2eVsegs;VC;R4R3A4S38VE;A1R2R1A5S21Vsegs;S25Vsegs;VC;R5R4A4S28VE;A1R3R2A5F_;Fw;Frho;FKc;FA;").
Proof.
  intros A Kc rho w [Hsm (HM & HK & HT & HI & HV)].
  assert (W := pre_window rho calloc_stack (Pre_calloc E) w ltac:(unfold calloc_stack; lia) Hsm
                 ltac:(eexists; reflexivity) ltac:(intros p Hp; exact Hp)).
  destruct W as (Wlo & Wneg & Wf).
  split.
  - change (Pre_callocI E) with (refacts (Pre_calloc E) ([F_sp_aligned; F_sp_high calloc_stack] ++ F_depth calloc_stack)).
    apply smatch_refacts; [|exact Hsm]. intros p Hp. cbn [ss_facts Pre_calloc]. rewrite !in_app_iff in *. tauto.
  - split; [exact HM|]. split; [exact HK|]. split; [exact HT|]. split; [exact HI|].
    exact (top_high_of_facts A rho Wf Wlo Wneg HV).
Qed.

Lemma SPJ_free_T : ltac2:(tb__ "0|0|
S1eS15S22A1S23OF_;F_;S0S48S21Vsegs;S37Vsegs;VC;R4R3A4S39VE;A1R2R1A5S21Vsegs;S27Vsegs;VC;R5R4A4S29VE;A1R3R2A5F_;Fw;Frho;FKc;FA;").
Proof.
  intros A Kc rho w [Hsm (HM & HIn & HK & HT & HI & HV)].
  assert (W := pre_window rho free_stack (Pre_free E) w ltac:(unfold free_stack; lia) Hsm
                 ltac:(eexists; reflexivity) ltac:(intros p Hp; exact Hp)).
  destruct W as (Wlo & Wneg & Wf).
  split.
  - change (Pre_freeI E) with (refacts (Pre_free E) ([F_sp_aligned; F_sp_high free_stack] ++ F_depth free_stack)).
    apply smatch_refacts; [|exact Hsm]. intros p Hp. cbn [ss_facts Pre_free]. rewrite !in_app_iff in *. tauto.
  - split; [exact HM|]. split; [exact HIn|]. split; [exact HK|]. split; [exact HT|]. split; [exact HI|].
    exact (top_high_of_facts A rho Wf Wlo Wneg HV).
Qed.

Lemma malloc_contract_of_T : ltac2:(tb__ "0|0|
S48OF_;S1eS15S22A1S23OF_;F_;S0S2bVsegs;R4R2A3S4aVsegs;R5S21Vsegs;S25Vsegs;VC;R4R3A4S2aVE;A1R2A4S4cVsegs;S4bR2S31Vsegs;VC;VE;R4R3A5A4A4F_;Frho;FKc;FA;Fok;S3fVsegs;VC;VE;A3F_;").
Proof. intros H ok A Kc rho Hok. eapply triple_conseq; [apply SPJ_malloc_T | intros w Hw; exact Hw | exact (H ok A Kc rho Hok)]. Qed.

Lemma malloc_contract_ex_of_T : ltac2:(tb__ "0|0|
S1eS15S22A1S23OF_;F_;S0S2cR2A1S49Vsegs;S21Vsegs;S25Vsegs;VC;R4R3A4S2aVE;A1R2A4S4cVsegs;S4bR2S31Vsegs;VC;VE;R4R3A5A4A3F_;Frho;FKc;FA;S40Vsegs;VC;VE;A3F_;").
Proof. intros H A Kc rho HK w Hw. exact (H A Kc rho HK w (SPJ_malloc_T A Kc rho w Hw)). Qed.

Lemma calloc_contract_of_T : ltac2:(tb__ "0|0|
S48OF_;S1eS15S22A1S23OF_;F_;S0S2bVsegs;R4R2A3S4aVsegs;R5S21Vsegs;S25Vsegs;VC;R4R3A4S28VE;A1R2A4S4cVsegs;S4bR2S30Vsegs;VC;VE;R4R3A5A4A4F_;Frho;FKc;FA;Fok;S3bVsegs;VC;VE;A3F_;").
Proof. intros H ok A Kc rho Hok. eapply triple_conseq; [apply SPJ_calloc_T | intros w Hw; exact Hw | exact (H ok A Kc rho Hok)]. Qed.

Lemma calloc_contract_ex_of_T : ltac2:(tb__ "0|0|
S1eS15S22A1S23OF_;F_;S0S2cR2A1S49Vsegs;S21Vsegs;S25Vsegs;VC;R4R3A4S28VE;A1R2A4S4cVsegs;S4bR2S30Vsegs;VC;VE;R4R3A5A4A3F_;Frho;FKc;FA;S3cVsegs;VC;VE;A3F_;").
Proof. intros H A Kc rho HK w Hw. exact (H A Kc rho HK w (SPJ_calloc_T A Kc rho w Hw)). Qed.

Lemma free_contract_of_T : ltac2:(tb__ "0|1|
S48OF_;S1eS15S22A1S23OF_;F_;S0S2bVsegs;R4R2A3S4aVsegs;R5S21Vsegs;S27Vsegs;VC;R4R3A4S29VE;A1R2A4S4cVsegs;S4bR2S16S17S3S4dA2M0S1bS3S4dS2fVE;A1S2dVsegs;VC;R4R3A4A4S18G0A1A3A4A4F_;Frho;FKc;FA;Fok;S3dVsegs;VC;VE;A3F_;").
Proof. intros H ok A Kc rho Hok. eapply triple_conseq; [apply SPJ_free_T | intros w Hw; exact Hw | exact (H ok A Kc rho Hok)]. Qed.

Lemma free_contract_ex_of_T : ltac2:(tb__ "0|1|
S1eS15S22A1S23OF_;F_;S0S2cR2A1S49Vsegs;S21Vsegs;S27Vsegs;VC;R4R3A4S29VE;A1R2A4S4cVsegs;S4bR2S16S17S3S4dA2M0S1bS3S4dS2fVE;A1S2dVsegs;VC;R4R3A4A4S18G0A1A3A4A3F_;Frho;FKc;FA;S3eVsegs;VC;VE;A3F_;").
Proof. intros H A Kc rho HK w Hw. exact (H A Kc rho HK w (SPJ_free_T A Kc rho w Hw)). Qed.

End WithSegs.

Lemma top_high_call : ltac2:(tb__ "0|4|
S1eS1eS0S0S45S54S57S1fR3A1A1S57S1fR4A1A1A3S51S4fS43Q40M0S1R3PaM1A2A2S4eZ40M2S43G0S1R3S24A2A2A2A2S4fS43G0S1R2G1A2A2S4eG2S43G0S1R2S24A2A2A2A2A2S26R6R4A2M3G3F_;F_;F_;Frho';Frho;FA';FA;").
Proof. intros A A' rho rho' E LE H. unfold top_high in *. rewrite E. lia. Qed.

Lemma top_high_agree : ltac2:(tb__ "0|2|
S1eS0S0S45S44Q40A1M0S1R1PaM1A2S1R2G1A2A3S45G0S1R2S24A2S1R3S24A2A3S26R5R4A2S26R6R4A2F_;F_;F_;Frho';Frho;FA;").
Proof. intros A rho rho' E1 E2 H. unfold top_high in *. rewrite E1, E2. exact H. Qed.

Lemma top_high_extends : ltac2:(tb__ "0|0|
S1eS1eS1dS0S20S1fR4A1S1fR3A1R2A3S26R5R2A2S26R5R3A2F_;F_;Frho;Fn;FA';FA;").
Proof. intros A A' n rho HE H. unfold top_high in *. rewrite (layout_extends_top _ _ _ HE). exact H. Qed.
