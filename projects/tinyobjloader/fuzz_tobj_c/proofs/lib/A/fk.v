(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.

(* [comment removed for export] *)
Module Icpt_memcpy_hdr_proof.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "ACEIL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "holds"; "ss_next"; "rw"; "sprop_below"; "ss_facts"; "SVar"; "agree_below"; "SAlu"; "SLit"; "SPBranch"; "SPNot"; "eval"; "sv"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "True"; "ex"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "modulo"; "sub"; "lt"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr"; "FT"; "Posts_mc"; "Pre_mc0"; "E_src"; "E_dst"; "base_mc"; "xor_facts"; "E_real"; "Pre_mc1"; "Pre_mc2"; "ord1"; "ord2"; "R_dst"; "R_real"; "R_src"; "cuts_mc"; "opnd_facts"; "s_dst"; "s_real"; "s_src"; "vcuts_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof"; "clsZ"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Icpt_memcpy_hdr_proof.OpZ"; "opZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Icpt_memcpy_hdr_proof"; "opZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "vnodeA"; "withGA"; "vna_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_XOR"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "Posts_mhA"; "Pre_mhA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL MuslMemcpy MuslMemcpyHdr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RegionAddr MCAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation "'UU' rho e" := (bv_unsigned (eval rho e)) (at level 10, rho at level 9, e at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Section OpZ.
Variable rho : valuation.

Definition opZ (ib il : positive) : Prop := ltac2:(tb__ "0|3|
S23Q40M0S6Vrho;Vib;A2A2S2dS23G0S6Vrho;Vil;A2A2S2dS23G0S6Vrho;P12A2A2S2dS15S1cR1R2A2S15S1cR2S1eZ2M1Z28A2A2S15S1cZ1000R3A2S15S1cS1dR3R2A2S20S1eG1Z2fA2Z8M2A2A2S16S2dS1fR3G2A2Z0A3A2A2A2A2TN;TL;TB;").

Lemma opnd_Z : ltac2:(tb__ "0|0|
S2eS2eS1aS2S4Vrho;A1S41S9R2A1S9R1A1R2A3A3S4cR3R2A2F_;Fil;Fib;").
Proof.
  intros ib il HF.
  pose proof (urange (rw rho ib)) as RB. pose proof (urange (rw rho il)) as RL.
  pose proof (urange (rw rho 18)) as RN.
  have_fact A2 HF (SPUle (SVar il) (SLit (2 ^ 40))).
  have_fact A3 HF (SPUle (SLit 4096) (SVar ib)). have_fact A4 HF (SPUle (add (SVar ib) (SVar il)) (SLit (2 ^ 47 - 8))).
  have_fact A5 HF (SPAlign ib 3). have_fact A7 HF (SPUle vN (SVar il)).
  have_fact A8 HF (SPUle (SVar ib) (SLit (2 ^ 47 - 8))).
  unfold vN, add in A2, A3, A4, A7, A8.
  rewrite (U_lit64 rho (2 ^ 40)) in A2 by lia. rewrite (U_lit64 rho 4096) in A3 by lia.
  pose proof (U_lit64 rho (2 ^ 47 - 8) ltac:(lia)) as T47. rewrite T47 in A4. rewrite T47 in A8.
  cbn [eval] in A2, A3, A7, A8.
  assert (B2 : 0 <= bv_unsigned (rw rho ib) + bv_unsigned (rw rho il) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar ib) (SVar il) (bv_unsigned (rw rho ib)) (bv_unsigned (rw rho il)) eq_refl eq_refl B2) in A4.
  destruct A5 as [_ A5]. change (2 ^ 3) with 8 in A5.
  unfold opZ. repeat split; lia.
Qed.

Lemma base_mc_Z : ltac2:(tb__ "0|4|
S1aS2S4Vrho;A1S36A3S15S4cPfP10A2S15S4cP13P34A2S15S15S1cZ41S23Q40M0S6Vrho;P12A2A2M1A2S1cG1S1eZ2M2Z28A2A2A2S15S15S1cS1dS1Z1000A2S23G0S6Vrho;PaA2A2M3A2S1cG3S1eG2Z3fA2A2A2S16S2dS1fG3Z10A2Z0A3A2A2A2A2F_;").
Proof.
  intros HF. unfold base_mc in HF. apply Forall_app in HF as [HD HF]. apply Forall_app in HF as [HS HN].
  pose proof (urange (rw rho 18)) as RN. pose proof (urange (rw rho 10)) as R10.
  have_fact N1 HN (SPUle (SLit 65) vN). have_fact N2 HN (SPUle vN (SLit (2 ^ 40))).
  have_fact N3 HN (SPUle (SLit (ACEIL + 4096)) (SVar 10)). have_fact N4 HN (SPUle (SVar 10) (SLit (2 ^ 63))).
  have_fact N5 HN (SPAlign 10 4).
  unfold vN in N1, N2. rewrite (U_lit64 rho 65) in N1 by lia. rewrite (U_lit64 rho (2 ^ 40)) in N2 by lia.
  rewrite (U_lit64 rho (ACEIL + 4096)) in N3 by (unfold ACEIL; lia). rewrite (U_lit64 rho (2 ^ 63)) in N4 by lia.
  cbn [eval] in N1, N2, N3, N4. destruct N5 as [_ N5]. change (2 ^ 4) with 16 in N5.
  split; [exact (opnd_Z 15 16 HD)|]. split; [exact (opnd_Z 19 52 HS)|]. repeat split; lia.
Qed.
End OpZ.

Lemma FT_of_E : ltac2:(tb__ "0|0|
S34S2bS3S1aS2S4R1A1S8S29S34A1A1A3S1aS2S4R2A1S31A3F_;Fr;TE;").
Proof. intros E r HF. cbn [ax_S ss_facts E_src mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Edst : ltac2:(tb__ "0|0|
S3S1aS2S4R1A1S8S29S35A1A1A3S1aS2S4R2A1S31A3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_dst mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Ereal : ltac2:(tb__ "0|0|
S3S1aS2S4R1A1S8S29S38A1A1A3S1aS2S4R2A1S31A3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_real mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Lemma next_E : ltac2:(tb__ "0|0|
S15S4eS1bS5S29S34A1A1A2S15S4eS1bS5S29S35A1A1A2S4eS1bS5S29S38A1A1A2A2A2").
Proof. repeat split; cbv; congruence. Qed.
Lemma FT_of_E_cls : ltac2:(tb__ "0|0|
S11S2A1S3S1aS2S4R1A1S8S29S52R2S34A2A1A1A3S1aS2S4R2A1S31A3F_;Fr;FF;").
Proof. intros F r HF. cbn [ax_S ss_facts E_src mid_state mkA ax_add_facts ax_setS add_facts] in HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Edst_cls : ltac2:(tb__ "0|0|
S11S2A1S3S1aS2S4R1A1S8S29S52R2S35A2A1A1A3S1aS2S4R2A1S31A3F_;Fr;FF;").
Proof. intros F r HF. cbn [ax_S ss_facts E_dst mid_state mkA ax_add_facts ax_setS add_facts] in HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Lemma FTbT1 : ltac2:(tb__ "0|0|
S2aS47S2aR1S51A3S16S12S48S2S7S5S29S4dS44S50S2cR2A1S34S3fA5A1A1A1S31A3S13A3F_;FL;").
Proof. intros L [<-|[]]. exact (proj1 FT_below_T). Qed.
Lemma FTbT2 : ltac2:(tb__ "0|0|
S2aS47S2aR1S51A3S16S12S48S2S7S5S29S4dS42S50S2cR2A1S35S3dA5A1A1A1S31A3S13A3F_;FL;").
Proof. intros L [<-|[]]. exact (proj1 (proj2 FT_below_T)). Qed.
Lemma FTbT3 : ltac2:(tb__ "0|0|
S2aS47S2aR1S59A3S16S12S48S2S7S5S29S4dS43S5aS2cR2A1S38S3eA5A1A1A1S31A3S13A3F_;FL;").
Proof. intros L [<-|[]]. exact (proj2 (proj2 FT_below_T)). Qed.

Section Sum.
Variable ok : assn.
Variable J : jpredA.
Hypothesis Hok : ltac2:(tb__ "0|0|
S27S0Vok;VJ;A3").
Hypothesis Hst : stableA segs NF J.

Hypothesis HclsD : ltac2:(tb__ "0|0|
S3S11S22Q40A1A1S11S30A1S2fVJ;R4R3R2R1A4S46R5PfP10A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HclsS : ltac2:(tb__ "0|0|
S3S11S22Q40A1A1S11S30A1S2fVJ;R4R3R2R1A4S46R5P13P34A3F_;Fmd;Ftr;Ft;Fr;").

Lemma cfg_mc_sound : ltac2:(tb__ "0|0|
S3S11S22Q40A1A1S2bS47S2bR1S40A3S3S4aS0Vok;S24S0S54S3SaS1bR6R1A3Lr;VJ;A2R3R1R4A5S25S0VJ;S1bR5R4S32A6A4FrhoT;F_;FT;Ftp;Frho;").
Proof.
  intros rho tp T HinT rhoT.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok (withGA (fun r => agree_below NF rho r) J)).
  { intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto. }
  apply (cfg_soundA segs FUELM cutpcs_mc NF cuts_mc exits_mc (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_mc) tp HokG HstG check_mc); [|exact HinT].
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply exit_postA. in_nth 0.
  -
    apply triple_SPA_pure. intros tr0 md0 [_ HJ0].
    eapply triple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_src rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsS rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_src_hi Pre_rip s_src R_src Posts_rip FT Hst fr_src_hi cc_src_hi (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 2]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 19 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_src_lo Pre_rip_lo s_src R_src Posts_rip FT Hst fr_src_lo cc_src_lo (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum_lo ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 2]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 19 52 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  -
    apply triple_SPA_pure. intros tr0 md0 [_ HJ0].
    eapply triple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_dst rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_dst_hi Pre_rip s_dst R_dst Posts_rip FT Hst fr_dst_hi cc_dst_hi (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 3]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_dst_lo Pre_rip_lo s_dst R_dst Posts_rip FT Hst fr_dst_lo cc_dst_lo (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum_lo ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 3]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA ok J NF rho tp E_real Pre_mhA s_real R_real Posts_mhA FT Hst fr_real cc_real (proj2 (proj2 next_E)) FT_of_Ereal FT_below_E FTbT3
             cuts_mc _ Hok).
    + intros ok' Jq rho1 tp1 Ho Hs. exact (memcpy_hdr_sumA ok' Jq rho1 tp1 Ho Hs).
    + intros L [<-|[]]. in_nth 4.
Qed.

Theorem memcpy_icpt_sum1 : ltac2:(tb__ "0|0|
S3S11S22Q40A1A1S4aS0Vok;S24S0VJ;S39R2R1A5S25S0VJ;S1bR2R1S32A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc1 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_mc_sound rho tp Pre_mc1). left; reflexivity.
Qed.

Theorem memcpy_icpt_sum2 : ltac2:(tb__ "0|0|
S3S11S22Q40A1A1S4aS0Vok;S24S0VJ;S3aR2R1A5S25S0VJ;S1bR2R1S32A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc2 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_mc_sound rho tp Pre_mc2). right; left; reflexivity.
Qed.
End Sum.

Section SumEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.
Hypothesis HclsD : ltac2:(tb__ "0|0|
S3S11S22Q40A1A1S11S30A1S2fVJ;R4R3R2R1A4S46R5PfP10A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HclsS : ltac2:(tb__ "0|0|
S3S11S22Q40A1A1S11S30A1S2fVJ;R4R3R2R1A4S46R5P13P34A3F_;Fmd;Ftr;Ft;Fr;").

Ltac meas_lit := intros r r'; unfold vmeasIA; cbn [vna_var vna_rank eval]; rewrite ?u64_lit by lia; lia.

Lemma cfg_mc_complete : ltac2:(tb__ "0|0|
S3S11S22Q40A1A1S53S47S53R1S45A3S3S49S0S24S0S54S3SaS1bR6R1A3Lr;VJ;A2S55R3A1R1R4A5S25S0VJ;S1bR5R4S32A6A3FrhoT;F_;Fn;Ftp;Frho;").
Proof.
  intros rho tp n HinT rhoT.
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  apply (cfg_complete_autoIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_mc) tp HstG); [ | exact echeck_mc | | exact HinT].
  { intros m Hm. unfold vcuts_mc in Hm. repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm. }
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[]]]]].
  - apply (eexit_post_IA0 segs J NF rho vcuts_mc Posts_mc (mkVNA P_icpt 0 (SLit (2 ^ 64 - 1)))). in_nth 0.
  - apply etriple_SPA_pure'. intros tr0 md0 [_ HJ0].
    eapply etriple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_src rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsS rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_src_hi Pre_rip s_src R_src Posts_rip FT Hst fr_src_hi cc_src_hi (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1
                   vcuts_mc _ (mkVNA E_src_hi 120 (SLit (2 ^ 61))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 119 (SLit (2 ^ 61))); split; [in_nth 2|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 19 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_src_lo Pre_rip_lo s_src R_src Posts_rip FT Hst fr_src_lo cc_src_lo (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1
                   vcuts_mc _ (mkVNA E_src_lo 120 (SLit (2 ^ 61))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_lo_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 119 (SLit (2 ^ 61))); split; [in_nth 2|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 19 52 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply etriple_SPA_pure'. intros tr0 md0 [_ HJ0].
    eapply etriple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_dst rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_dst_hi Pre_rip s_dst R_dst Posts_rip FT Hst fr_dst_hi cc_dst_hi (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2
                   vcuts_mc _ (mkVNA E_dst_hi 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T2 79 (SLit (2 ^ 63))); split; [in_nth 3|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_dst_lo Pre_rip_lo s_dst R_dst Posts_rip FT Hst fr_dst_lo cc_dst_lo (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2
                   vcuts_mc _ (mkVNA E_dst_lo 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_lo_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T2 79 (SLit (2 ^ 63))); split; [in_nth 3|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA_ex J NF rho tp E_real Pre_mhA s_real R_real Posts_mhA FT Hst fr_real cc_real (proj2 (proj2 next_E)) FT_of_Ereal FT_below_E FTbT3
             vcuts_mc _ (mkVNA E_real 40 (SLit (2 ^ 63 + 8))) eq_refl).
    + intros Jq rho1 tp1 Hs. exact (memcpy_hdr_sumA_ex Jq rho1 tp1 Hs).
    + intros L [<-|[]]. exists (mkVNA T3 39 (SLit (2 ^ 63 + 8))). split; [in_nth 4|]. split; [reflexivity|]. meas_lit.
Qed.

Theorem memcpy_icpt_sum1_ex : ltac2:(tb__ "0|0|
S3S11S22Q40A1A1S49S0S24S0VJ;S39R2R1A5S25S0VJ;S1bR2R1S32A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc1 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_mc1 with (vna_state (mkVNA Pre_mc1 200 (SLit 0))).
  apply (cfg_mc_complete rho tp). left; reflexivity.
Qed.

Theorem memcpy_icpt_sum2_ex : ltac2:(tb__ "0|0|
S3S11S22Q40A1A1S49S0S24S0VJ;S3aR2R1A5S25S0VJ;S1bR2R1S32A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc2 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_mc2 with (vna_state (mkVNA Pre_mc2 200 (SLit 0))).
  apply (cfg_mc_complete rho tp). right; left; reflexivity.
Qed.
End SumEx.

Section Public.
Variable rho : valuation.
Let a := bv_unsigned (eval rho dst). Let b := bv_unsigned (eval rho src). Let n := bv_unsigned (rw rho 18).

Lemma pre_disjoint : ltac2:(tb__ "0|1|
S11S22Q40A1A1M0S4bS17S24S0S3G0S11S30A1S2fS18L_;L_;L_;L_;S33Vrho;R2R1A6S19S26S26S24S0R1S33Vrho;R3R2A6LJ;A2A2S21Vn;S1eZ2Z3fA2A2S17S1cS1dVa;Vn;A2Vb;A2S17S1cS1dVb;Vn;A2Va;A2S16S2dVn;Z0A3A2A2F_;F_;Fw;Ftp;").
Proof.
  intros tp w HS Hn.
  assert (Hsm : smatchA segs rho tp Pre_mc0 w) by (destruct HS as [[H _]|[J [H _]]]; exact H).
  destruct Hsm as (Hsm & _). destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpd & _) & _).
  cbn [ss_objs ax_S Pre_mc0 mkA objs_mc app pairwise_disjoint] in Hpd.
  destruct Hpd as (_ & _ & HD & _). apply Forall_inv in HD.
  unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of, O_dst, O_src in HD. cbn [ob_base ob_lo ob_hi fst snd] in HD.
  rewrite !soff_lit_small in HD by lia.
  assert (Es : soff rho vN = n) by (unfold vN; apply soff_var'; subst n; lia). rewrite !Es in HD.
  subst a b. lia.
Qed.

Lemma pre_Z : ltac2:(tb__ "0|3|
S1aS2S4Vrho;A1S36A3S15S16S2dVa;S23Q40M0S6Vrho;PfM1A2A2A3S15S16S2dVb;S23G0S6Vrho;P13M2A2A2A3S15S4fVrho;G1P10A3S15S4fVrho;G2P34A3S15S1cZ41Vn;A2S1cVn;S1eZ2Z28A2A2A2A2A2A2A2F_;").
Proof.
  intros HF. destruct (base_mc_Z rho HF) as (ZD & ZS & ZN & _).
  split; [reflexivity|]. split; [reflexivity|]. auto.
Qed.

Lemma xor_fact_Z : ltac2:(tb__ "0|0|
S10S2dS16S2dS23Q40SfVrho;R2A2A2R1A3S1cS1dR2Vn;A2S20S1eZ2Z40A2Z1A2A2S4Vrho;SeSdS57SbS56R4ScZffffffffffffffffA1A3S58A3A1A2F_;F_;Fx;Fe;").
Proof.
  intros e x He Hx. cbn [holds branch_taken]. unfold bv_ltu.
  rewrite (U_xor_m1 rho e 18446744073709551615 eq_refl). rewrite He. change (eval rho vN) with (rw rho 18).
  unfold M64v. rewrite Z.ltb_lt. subst n. lia.
Qed.

Lemma facts1 : ltac2:(tb__ "0|1|
S1aS2S4Vrho;A1M0S36A3S1cS1dVa;Vn;A2Vb;A2S1aS2G0S14S2S3bS37A3A3F_;F_;").
Proof.
  intros HF Hab. destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN). pose proof ZD as ZD'. pose proof ZS as ZS'.
  unfold opZ in ZD', ZS'. cbv zeta in ZD'. cbv zeta in ZS'. unfold HSE in *.
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 19)).
  pose proof (urange (rw rho 18)). unfold ord1, xor_facts.
  constructor.
  { cbn [holds]. unfold add at 1. rewrite (U_add2 rho dst vN a n eq_refl eq_refl) by (subst a n; lia). fold b. lia. }
  constructor. { apply (xor_fact_Z src b eq_refl). subst b n. lia. }
  constructor. { apply (xor_fact_Z dst a eq_refl). subst a n. lia. }
  constructor.
Qed.

Lemma facts2 : ltac2:(tb__ "0|1|
S1aS2S4Vrho;A1M0S36A3S1cS1dVb;Vn;A2Va;A2S1aS2G0S14S2S3cS37A3A3F_;F_;").
Proof.
  intros HF Hab. destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN). pose proof ZD as ZD'. pose proof ZS as ZS'.
  unfold opZ in ZD', ZS'. cbv zeta in ZD'. cbv zeta in ZS'. unfold HSE in *.
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 19)).
  pose proof (urange (rw rho 18)). unfold ord2, xor_facts.
  constructor.
  { cbn [holds]. unfold add at 1. rewrite (U_add2 rho src vN b n eq_refl eq_refl) by (subst b n; lia). fold a. lia. }
  constructor. { apply (xor_fact_Z src b eq_refl). subst b n. lia. }
  constructor. { apply (xor_fact_Z dst a eq_refl). subst a n. lia. }
  constructor.
Qed.

Lemma F1_below : ltac2:(tb__ "0|0|
S16S12S48S2S7S5S29S33A1A1A1S14S2S3bS37A3A3S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2_below : ltac2:(tb__ "0|0|
S16S12S48S2S7S5S29S33A1A1A1S14S2S3cS37A3A3S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma SPA_cases : ltac2:(tb__ "0|0|
S26S11S22Q40A1A1S4bS24S0R3S33Vrho;R2R1A6S17S24S0R4S39Vrho;R3R2A6S24S0R4S3aVrho;R3R2A6A2F_;Fw;Ftp;FJ;").
Proof.
  intros J tp w Hw. pose proof (SPA_facts_hold segs J rho Pre_mc0 tp w Hw) as HF. cbn [ax_S ss_facts Pre_mc0 mkA] in HF.
  destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN).
  destruct (pre_disjoint tp w (or_intror (ex_intro _ J Hw)) ltac:(lia)) as [H|[H|H]]; [left | right | exfalso; lia].
  - destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (facts1 HF H) | exact F1_below].
  - destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (facts2 HF H) | exact F2_below].
Qed.
End Public.

Theorem memcpy_icpt_hdr_sum : ltac2:(tb__ "0|2|
S4bOF_;S26S3S11S22Q40A1A1M0S27S0R4R3A3S28S0S1bR4A3S3G0S11S30A1M1S2fR9R4R3R2R1A4S46R5PfP10A3F_;Fmd;Ftr;Ft;Fr;S3G0G1S2fRaR4R3R2R1A4S46R5P13P34A3F_;Fmd;Ftr;Ft;Fr;S4aS0R8S24S0R7S33R6R5A5S25S0R7S1bR6R5S32A6A4F_;F_;F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst HD HS.
  eapply triple_conseq; [intros w Hw; exact (SPA_cases rho J tp w Hw) | intros w Hw; exact Hw |].
  apply triple_disj; [apply memcpy_icpt_sum1 | apply memcpy_icpt_sum2]; assumption.
Qed.

Theorem memcpy_icpt_hdr_sum_ex : ltac2:(tb__ "0|2|
S26S3S11S22Q40A1A1M0S28S0S1bR3A3S3G0S11S30A1M1S2fR8R4R3R2R1A4S46R5PfP10A3F_;Fmd;Ftr;Ft;Fr;S3G0G1S2fR9R4R3R2R1A4S46R5P13P34A3F_;Fmd;Ftr;Ft;Fr;S49S0S24S0R6S33R5R4A5S25S0R6S1bR5R4S32A6A3F_;F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst HD HS.
  eapply etriple_conseq; [intros w Hw; exact (SPA_cases rho J tp w Hw) | intros w Hw; exact Hw |].
  apply etriple_disj; [apply memcpy_icpt_sum1_ex | apply memcpy_icpt_sum2_ex]; assumption.
Qed.
End Icpt_memcpy_hdr_proof.

(* [comment removed for export] *)
Module Str_strnlenA_st.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "true"; "bool"; "nil"; "pair"; "Some"; "option"; "false"; "list"; "prod"; "None"; "app"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SVar"; "ss_next"; "SLit"; "FcsrFrm0"; "mkSS"; "sprop"; "ss_lenient"; "sstate"; "swf"; "DUnknown"; "SAlu"; "SPUle"; "cell"; "mkObj"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "sym_runA"; "mkLeafA"; "axwf"; "entailsA"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Str_strnlenA_st"; "E_callS"; "Pre_sn"; "CUTS_SN"; "FUEL_SN"; "P_sn"; "s_call"; "D_SN"; "E_call"; "G_sn"; "R_call"; "R_sn"; "T_impF"; "facts_sn"; "T_imp"; "X_sn"; "objs_sn"; "sn_ret"; "sp_sn"; "O_winN"; "XN"; "sn_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "mkA"; "ACEIL"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXRebase"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "Pre_mci"; "O_realmc"; "O_strS"; "P_mci"; "Posts_mci"; "facts_mci"; "mci_entry"; "sX"; "vXB"; "vXL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "RsSymJump"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "O_rtc2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations. Import MCHAddr. Import RegionAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition sn_entry : Z := 0xde800.
Definition sn_ret : Z := 0xde840.
Definition D_SN : Z := D_MCI + 32.
Definition O_winN : sobj := ltac2:(tb__ "0|0|
S1eS11PaA1S13S5aS35A1A1S13Z0A1S4S1dA1S1aA5").
Definition facts_sn : list sprop := ltac2:(tb__ "0|0|
S0S16S1cS13S59S59S46Z1000A2Z20A2A1S11PaA1A2S52A3").
Definition X_sn : list (sv * sv) := ltac2:(tb__ "0|1|
S0SaSfSfA2M0S5SfSfS55S56A4S0G0S5SfSfS1bS5cS11PaA1S13S5aS35A1A1A3S13S35A1A4S4G0A1A3A3").
Definition objs_sn : list sobj := ltac2:(tb__ "0|0|
ScS10S0S10S41S0S10S4fS0S10S5dS0S10S5eS0S10S4eS4S10A1A3A3A3A3A3S47A3").

Definition Pre_sn : axst := ltac2:(tb__ "0|1|
S45S15S43S2aS2cS0SaS1SfA2M0S5S1SfUaS54A4S0G0S5S1SfUbS11PeA1A4S0G0S5S1SfUcS11PdA1A4S4G0A1A3A3A3A2S29S14SbSfA1S3eS3bS28S8A9S3dA2").
Definition CUTS_SN : ltac2:(tb__ "0|0|
S9S2eA1") := ltac2:(tb__ "0|0|
S0S2eS53S0S2eS3fS4S2eA1A3A3").
Definition FUEL_SN : nat := 100%nat.

Definition sn_run_call__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S44S32S31S30S2A5").
Local Strategy expand [sn_run_call__R].
Definition E_call : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => lf0 Pre_sn (ro1__) 0) sn_run_call__R).
Definition E_callS : axst := Eval vm_compute in match split_obj_at (ax_S E_call) 0 (SLit (-32)) with Some S' => ax_setS E_call S' | None => E_call end.
Definition s_call : wsub := Eval vm_compute in infer_sub 10 (ax_S E_callS) (ax_S Pre_mci).
Definition R_call : list sobj := Eval vm_compute in match entails_frA E_callS Pre_mci s_call with Some R => R | None => [] end.
Definition T_imp : axst := Eval vm_compute in import_postA s_call Pre_mci P_mci E_callS R_call.
Definition T_impF : axst := ax_add_facts facts_sn T_imp.

Definition sn_run_ret__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S44S32S31S3aS2A5").
Local Strategy expand [sn_run_ret__R].
Definition R_sn : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => lf0 T_impF (ro2__) 0) sn_run_ret__R).

Definition XN : list axform := ltac2:(tb__ "0|1|
S0S48S4aU0M0A1S0S48S4bS0S1G0S0S1U7S0S1U1S0S1U2S0S1U3S0S1U4S0S1U5S0S1U6S4S1A1A3A3A3A3A3A3A3A3A1S0S48S49G0A1S4S48A1A3A3A3").
Definition G_sn : axst := Eval vm_compute in match apply_axforms R_sn XN with Some A => A | None => R_sn end.
Definition P_sn0 : axst := ltac2:(tb__ "0|1|
S45S15S3fS2aS2bS28A1S0SaS1SfA2M0S5S1SfUaS11P8cA1A4S4G0A1A3A2S29S14SbSfA1S3eS3bP8dS8A9S3dA2").
Definition P_sn : axst := ax_add_facts F_post P_sn0.
Definition Posts_sn : list leafA := ltac2:(tb__ "0|0|
S0S21S24S33S58A2S4S21A1A3").
Definition sp_sn : wsub := Eval vm_compute in infer_sub NF (ax_S G_sn) (ax_S P_sn0).

Lemma sn_wf : ltac2:(tb__ "0|0|
SeSdS3S25S30A1S2A3SeSdS3S19S20S30A1A1S2A3SeSdS3S25S33A1S2A3SdS3S19S20S33A1A1S2A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma sn_run_call : ltac2:(tb__ "0|1|
SdS7S9S21A1M0A1S23S44S32S31S30S2A5S6G0S0S21S24S36S57A2S4S21A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) sn_run_call__R <: sn_run_call__R = Some [mkLeafA E_call RsCut]). Qed.
Lemma sn_split_call : ltac2:(tb__ "0|0|
SdS7S18A1S61S20S36A1U0S13N20A1A3S6S18S20S2fA1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sn_efr_call : ltac2:(tb__ "0|1|
SdS7S9S10A1M0A1S63S2fS4dS34A3S6G0S38A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sn_chk_call : ltac2:(tb__ "0|0|
SdS3S62S2fS4dS34S38S5bS21S22S27S51A4A5S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sn_imp_call : ltac2:(tb__ "0|0|
SdS22S64S34S4dS50S2fS38A5S3cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sn_run_ret : ltac2:(tb__ "0|1|
SdS7S9S21A1M0A1S23S44S32S31S3aS2A5S6G0S0S21S24S39S57A2S4S21A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) sn_run_ret__R <: sn_run_ret__R = Some [mkLeafA R_sn RsCut]). Qed.
Lemma sn_xf : ltac2:(tb__ "0|0|
SdS7S22A1S4cS39S42A2S6S22S37A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sn_ent : ltac2:(tb__ "0|0|
SdS3S26S37S33S40A3S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sn_ids : ltac2:(tb__ "0|0|
SdS3S60S40S28A2S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma sn_shape : ltac2:(tb__ "0|5|
SeSdS3S17S20S30A1M0A1S8A3SeSdS2dS12G0A1S28A3SeSdS2dS12S20S36A1A1S28A3SeSdS2dS12S20S2fA1A1S28A3SeSdSfS5fS34P10M1A2S11G1A1A3SeSdS2dS12S20S3cA1A1P8dM2A3SeSdS3S17S20S3aA1M3A1S8A3SeSdS2dS12G3A1G2A3SeSdS3S65S16S1fS28A1S3bA3S2A3SeSdS2dS12S20S39A1A1M4S12S20S37A1A1A3SdS3S66G2G4A2S2A3A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Str_strnlenA_st.

(* [comment removed for export] *)
Module Icpt_memcpy_rs_proof.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "rw"; "holds"; "eval"; "ss_next"; "ss_facts"; "SVar"; "sprop_below"; "SLit"; "agree_below"; "SPBranch"; "SPNot"; "SAlu"; "sobj"; "soff"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "SHB"; "ACEIL"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "True"; "not"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "mul"; "sub"; "modulo"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "nil"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "wsub_get"; "wsub_id_below"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_rs"; "FT"; "Posts_mc"; "Pre_mc0"; "cur"; "F_L"; "E_src"; "E_dst"; "base_mc"; "gs"; "xor_facts"; "E_real"; "Pre_mc1"; "Pre_mc2"; "gl"; "E_Ld_bk"; "F8of"; "lastd"; "lasts"; "ord1"; "ord2"; "s_Ld_bk"; "s_Ld_in"; "s_Ls_bk"; "s_Ls_in"; "vBd"; "vBs"; "vLd"; "vLs"; "E_Ld_in"; "E_Ls_bk"; "E_Ls_in"; "R_dst"; "R_real"; "R_src"; "cuts_mc"; "hi_fact"; "lo_fact"; "opnd_facts"; "s_dst"; "s_real"; "s_src"; "vcuts_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Icpt_memcpy_rs_proof"; "opZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof"; "clsZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "add"; "shp"; "vN"; "HSE"; "g8"; "shpk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "ax_add_facts"; "withGA"; "vna_state"; "SPfamA"; "SPfamEA"; "enodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "call_checkA"; "entails_frA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Icpt_memcpy_rs_proof.OpZ"; "opZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "vmeasIA"; "to_enodeIA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof"; "Posts_rip"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_XOR"; "BC_GEU"; "BC_LTU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memcpyAH"; "Posts_ahA"; "Pre_ahA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL MuslMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memcpyAH.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_rs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RegionAddr MCAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation "'UU' rho e" := (bv_unsigned (eval rho e)) (at level 10, rho at level 9, e at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Section CallExit.
Variable ok : assn.
Variable J : jpredA.
Variable n : positive.
Variable rho0 : valuation.
Variable tp : list word.
Let J' : jpredA := ltac2:(tb__ "0|0|
S79S1SaVn;Vrho0;R1A3Lr;VJ;A2").

Variables (E Pre : axst) (s : wsub) (R : list sobj) (Posts : list leafA) (F : list sprop).
Hypothesis Hst : ltac2:(tb__ "0|0|
S36S11Vn;VJ;A3").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S17S2eS27SeA1M0A1S80VE;VPre;Vs;A3S2dG0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S17S28S7fVE;VPre;Vs;VR;S1dS30S31S32VPosts;A4A5S29A3").
Hypothesis Hn : ltac2:(tb__ "0|0|
S81Vn;S5S2fVE;A1A1A2").
Hypothesis HF : ltac2:(tb__ "0|0|
S1S1cS0S3R1A1S6S2fVE;A1A1A3S1cS0S3R2A1VF;A3F_;Fr;").
Hypothesis HFb : ltac2:(tb__ "0|0|
S17S28S40S0S8S5S2fVE;A1A1A1VF;A3S29A3").
Hypothesis HFbT : ltac2:(tb__ "0|0|
S30S3fS30R1VPosts;A3S17S28S40S0S8S5S2fS7eVs;VPre;S32R2A1VE;VR;A5A1A1A1VF;A3S29A3F_;FL;").

Let Jp (rhoE : valuation) : jpredA := ltac2:(tb__ "0|1|
S1S27S15Q40A1A1M0S27S3aA1S39S16S17G0R3Vtp;A3VJ';VrhoE;R3R2R1A4A2Lmd;Ltr;Lt;L_;").
Let Jc : jpredA := ltac2:(tb__ "0|1|
S1S27S15Q40A1A1M0S27S3aA1S39S16S17G0R3Vtp;A3VJ';R4R3R2R1A4A2Lmd;Ltr;Lt;Lr;").

Lemma HstG : ltac2:(tb__ "0|0|
S36S11Vn;VJ';A3").
Proof. apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. Qed.

Lemma stable_Jp : ltac2:(tb__ "0|0|
S1S36S11S5S2fVPre;A1A1VJp;R1A1A3FrhoE;").
Proof.
  intros rhoE r r' t tr md md' Hag Hme [-> HJ]. split; [reflexivity|].
  eapply HstG; [apply agree_below_refl | exact Hme | exact HJ].
Qed.

Lemma okframe_Jp : ltac2:(tb__ "0|0|
S1S37S11Vok;VJ;A3S37S11Vok;VJp;R2A1A3F_;FrhoE;").
Proof.
  intros rhoE Hok r t tr ms md msv' [-> [_ HJ]]. eapply Hok; eauto.
Qed.

Lemma facts_transport : ltac2:(tb__ "0|1|
S1S1S1cS0S3R2A1S6S2fVE;A1M0A1A3SaS5G0A1R3R2A3S1cS0S3R3A1VF;A3F_;F_;Frho';FrhoE;").
Proof.
  intros rhoE rho' HFE Hag. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree (ss_next (ax_S E)) rhoE rho' p Hag (proj1 (forallb_forall _ _) HFb p Hp))).
  exact (proj1 (Forall_forall _ _) (HF rhoE HFE) p Hp).
Qed.

Lemma call_exitA : ltac2:(tb__ "0|1|
S27S31A1S76S37S11Vok;VJ;A3S74OF_;S35S1S27S15Q40A1A1S37S11R4R3A3S36S11S5S2fVPre;A1A1M0R4A3S75S11R6S33S11R5VPre;R4R3A5S34S11R5G0R4R3VPosts;A6A4F_;F_;Ftp1;Frho1;FJq;Fok';S30S3fS30R1VPosts;A3S3fS31S78VF;S7eVs;VPre;S32R2A1VE;VR;A5A2R6A3F_;FL;S1S75S11Vok;S33S11VJ';VE;R1Vtp;A5S74S18S7bS11VJ';R7Vtp;R1A5R6R1A1A2Lw;A4FrhoE;F_;F_;F_;FQ;Fcuts;").
Proof.
  intros cuts Q Hok Hsum Hcuts rhoE.
  apply triple_factsA. intros HFE.
  apply (call_soundA segs ok J' (Jp rhoE) (Jp rhoE) Jc E Pre s R Posts _ rhoE tp Hfr Hcc).
  - intros rho1 tp1. exact (Hsum ok (Jp rhoE) rho1 tp1 (okframe_Jp rhoE Hok) (stable_Jp rhoE)).
  - intros tr ms md Hsm HJ. split; [reflexivity | exact HJ].
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK [-> HJ2]. split; [reflexivity|].
    eapply HstG; [ | apply mat_equiv_refl | exact HJ2].
    eapply agree_below_le; [exact Hn | exact (proj1 HLK)].
  - intros L rho' tpL HinL Hag.
    eapply triple_conseq; [ | intros w Hw; exact Hw | apply triple_refl].
    intros w [Hsm [-> HJ2]]. left. exists (ax_add_facts F (import_postA s Pre (la_state L) E R)), rho'.
    split; [exact (Hcuts L HinL)|]. split; [|exact HJ2].
    apply smatchA_add_facts; [exact Hsm | exact (facts_transport rhoE rho' HFE Hag) | exact (HFbT L HinL)].
Qed.

Lemma call_exitA_ex : ltac2:(tb__ "0|3|
S27S77A1S74OF_;S77S17S31S7aR1A1M0VE;A3S35S1S27S15Q40A1A1S36S11S5S2fVPre;A1A1M1R3A3S73S11S33S11R4VPre;R3R2A5S34S11R4G1R3R2VPosts;A6A3F_;Ftp1;Frho1;FJq;S30S3fS30R1VPosts;A3S19S77S77S16S3fS77R1R8A3S16S17S31G0S78VF;S7eVs;VPre;S32R3A1VE;VR;A5A2A3S1S1S16S20Z0S84R3R1A2M2A2S23G2S84R8R2A2A2A2Fr';Fr;A2A2LnT;A2F_;FL;S1S73S11S33S11VJ';VE;R1Vtp;A5S74S18S7cS11S1dS77S7dS85VJ';A1R8A4Vtp;S84R6R2A2R1A5R7R1A1A2Lw;A3FrhoE;F_;F_;F_;FnE;FQ;Fvcuts;").
Proof.
  intros vcuts Q nE HnE Hsum Hcuts rhoE.
  apply etriple_factsA. intros HFE.
  apply (call_completeA segs J' (Jp rhoE) (Jp rhoE) Jc E Pre s R Posts _ rhoE tp Hfr Hcc).
  - intros rho1 tp1. exact (Hsum (Jp rhoE) rho1 tp1 (stable_Jp rhoE)).
  - intros tr ms md Hsm HJ. split; [reflexivity | exact HJ].
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK [-> HJ2]. split; [reflexivity|].
    eapply HstG; [ | apply mat_equiv_refl | exact HJ2].
    eapply agree_below_le; [exact Hn | exact (proj1 HLK)].
  - intros L rho' tpL HinL Hag w [Hsm [-> HJ2]]. exists w. split; [apply wsteps_refl|]. left.
    destruct (Hcuts L HinL) as (nT & HinT & HT & Hm).
    exists (to_enodeIA J' nT), rho'. split; [apply in_map; exact HinT|].
    cbn [to_enodeIA ena_state ena_pred ena_meas fst snd]. rewrite HT. split; [| exact (Hm rhoE rho')].
    split; [|exact HJ2].
    apply smatchA_add_facts; [exact Hsm | exact (facts_transport rhoE rho' HFE Hag) | exact (HFbT L HinL)].
Qed.
End CallExit.

Section OpZ.
Variable rho : valuation.

Definition opZ (ib il io : positive) : Prop := ltac2:(tb__ "0|3|
S14Q40M0S2Vrho;Vib;A2A2S1eS14G0S2Vrho;Vil;A2A2S1eS14G0S2Vrho;Vio;A2A2S1eS14G0S2Vrho;P12A2A2S1eS16S20S21R2R1A2R3A2S16S20R3S22Z2M1Z28A2A2S16S20Z1000R4A2S16S20S21R4R3A2S25S22G1Z2fA2Z8M2A2A2S17S1eS26R4G2A2Z0A3A2A2A2A2TN;TO;TL;TB;").

Lemma opnd_Z : ltac2:(tb__ "0|0|
S1fS1fS1fS1cS0S3Vrho;A1S66S7R3A1S7R2A1S7R1A1R3R1A5A3S83R4R3R2A3F_;Fio;Fil;Fib;").
Proof.
  intros ib il io HF.
  pose proof (urange (rw rho ib)) as RB. pose proof (urange (rw rho il)) as RL. pose proof (urange (rw rho io)) as RO.
  pose proof (urange (rw rho 18)) as RN.
  have_fact A1 HF (SPUle (add (SVar io) vN) (SVar il)). have_fact A2 HF (SPUle (SVar il) (SLit (2 ^ 40))).
  have_fact A3 HF (SPUle (SLit 4096) (SVar ib)). have_fact A4 HF (SPUle (add (SVar ib) (SVar il)) (SLit (2 ^ 47 - 8))).
  have_fact A5 HF (SPAlign ib 3). have_fact A6 HF (SPUle (SVar io) (SVar il)). have_fact A7 HF (SPUle vN (SVar il)).
  have_fact A8 HF (SPUle (SVar ib) (SLit (2 ^ 47 - 8))).
  unfold vN, add in A1, A2, A3, A4, A6, A7, A8.
  rewrite (U_lit64 rho (2 ^ 40)) in A2 by lia. rewrite (U_lit64 rho 4096) in A3 by lia.
  pose proof (U_lit64 rho (2 ^ 47 - 8) ltac:(lia)) as T47. rewrite T47 in A4. rewrite T47 in A8.
  cbn [eval] in A2, A3, A6, A7, A8.
  assert (B1 : 0 <= bv_unsigned (rw rho io) + bv_unsigned (rw rho 18) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar io) (SVar 18) (bv_unsigned (rw rho io)) (bv_unsigned (rw rho 18)) eq_refl eq_refl B1) in A1.
  cbn [eval] in A1.
  assert (B2 : 0 <= bv_unsigned (rw rho ib) + bv_unsigned (rw rho il) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar ib) (SVar il) (bv_unsigned (rw rho ib)) (bv_unsigned (rw rho il)) eq_refl eq_refl B2) in A4.
  destruct A5 as [_ A5]. change (2 ^ 3) with 8 in A5.
  unfold opZ. repeat split; lia.
Qed.

Lemma base_mc_Z : ltac2:(tb__ "0|4|
S1cS0S3Vrho;A1S48A3S16S83PfP10P11A3S16S83P13P34P35A3S16S16S20Z1S14Q40M0S2Vrho;P12A2A2M1A2S20G1S22Z2M2Z28A2A2A2S16S16S20S21S13Z1000A2S14G0S2Vrho;PaA2A2M3A2S20G3S22G2Z3fA2A2A2S17S1eS26G3Z10A2Z0A3A2A2A2A2F_;").
Proof.
  intros HF. unfold base_mc in HF. apply Forall_app in HF as [HD HF]. apply Forall_app in HF as [HS HN].
  pose proof (urange (rw rho 18)) as RN. pose proof (urange (rw rho 10)) as R10.
  have_fact N1 HN (SPUle (SLit 4) vN). have_fact N2 HN (SPUle vN (SLit (2 ^ 40))).
  have_fact N3 HN (SPUle (SLit (ACEIL + 4096)) (SVar 10)). have_fact N4 HN (SPUle (SVar 10) (SLit (2 ^ 63))).
  have_fact N5 HN (SPAlign 10 4).
  unfold vN in N1, N2. rewrite (U_lit64 rho 4) in N1 by lia. rewrite (U_lit64 rho (2 ^ 40)) in N2 by lia.
  rewrite (U_lit64 rho (ACEIL + 4096)) in N3 by (unfold ACEIL; lia). rewrite (U_lit64 rho (2 ^ 63)) in N4 by lia.
  cbn [eval] in N1, N2, N3, N4. destruct N5 as [_ N5]. change (2 ^ 4) with 16 in N5.
  split; [exact (opnd_Z 15 16 17 HD)|]. split; [exact (opnd_Z 19 52 53 HS)|]. repeat split; lia.
Qed.
End OpZ.

Lemma rw_sub : ltac2:(tb__ "0|0|
S1S3cS1fS17S15Q40A1S2S3bR3R2A2R1A2S4R3S3dR2R1A2A2A3Fi;Fs;Frho;").
Proof. reflexivity. Qed.

Section LoopZ.
Variables (ib il io : positive).
Let vB := SVar ib. Let vL := SVar il. Let vO := SVar io.
Let opd : sv := add vB vO.
Let lastx : sv := ltac2:(tb__ "0|0|
S6dS6dVopd;S6fA2S9N1A1A2").
Hypothesis Hib : (ib < NF)%positive. Hypothesis Hil : (il < NF)%positive. Hypothesis Hio : (io < NF)%positive.

Section Vals.
Variable r : valuation.
Let B : ltac2:(tb__ "0|0|
S1e") := ltac2:(tb__ "0|0|
S14Q40S2Vr;Vib;A2A2"). Let L : ltac2:(tb__ "0|0|
S1e") := ltac2:(tb__ "0|0|
S14Q40S2Vr;Vil;A2A2"). Let O : ltac2:(tb__ "0|0|
S1e") := ltac2:(tb__ "0|0|
S14Q40S2Vr;Vio;A2A2"). Let N := bv_unsigned (rw r 18).
Hypothesis HZ : ltac2:(tb__ "0|0|
S6bVr;Vib;Vil;Vio;A4").
Hypothesis HN : 1 <= N <= 2 ^ 40.

Lemma V_opd : ltac2:(tb__ "0|0|
S17S1eS14Q40S4Vr;Vopd;A2A2S21VB;VO;A2A3").
Proof using HZ HN.
  unfold opZ in HZ. pose proof (urange (rw r ib)). pose proof (urange (rw r io)). pose proof (urange (rw r il)).
  subst opd vB vO. unfold add. apply U_add2; [reflexivity | reflexivity | subst B L O N; unfold HSE in HZ; lia].
Qed.
Lemma V_last : ltac2:(tb__ "0|0|
S17S1eS14Q40S4Vr;Vlastx;A2A2S25S21S21VB;VO;A2VN;A2Z1A2A3").
Proof using HZ HN.
  pose proof V_opd as Vo. unfold opZ in HZ. pose proof (urange (rw r ib)). pose proof (urange (rw r io)). pose proof (urange (rw r il)).
  subst lastx. unfold add at 1. unfold add at 1.
  replace (B + O + N - 1) with ((B + O + N) + (-1)) by lia.
  apply (U_addc r (SAlu ALU_ADD opd vN) (-1) (B + O + N)); [ | subst B L O N; unfold HSE in HZ; lia | lia].
  apply U_add2; [exact Vo | reflexivity | subst B L O N; unfold HSE in HZ; lia].
Qed.
Lemma V_BL : ltac2:(tb__ "0|0|
S17S1eS14Q40S4Vr;S6dVvB;VvL;A2A2A2S21VB;VL;A2A3").
Proof using HZ HN.
  unfold opZ in HZ. pose proof (urange (rw r ib)). pose proof (urange (rw r il)).
  subst vB vL. unfold add. apply U_add2; [reflexivity | reflexivity | subst B L O N; lia].
Qed.
Lemma V_g8 : ltac2:(tb__ "0|1|
S1fS23S14Q40M0S2Vr;R1A2A2S22Z2Z3dA2A2S17S1eS14G0S4Vr;S71S7R2A1A1A2A2S24Z8S14G0S2Vr;R2A2A2A2A3F_;Fv;").
Proof. intros v Hv. apply U_g8. exact Hv. Qed.
Lemma V_shp : ltac2:(tb__ "0|1|
S1fS23S14Q40M0S2Vr;R1A2A2S22Z2Z3eA2A2S17S1eS14G0S4Vr;S6eS7R2A1A1A2A2S21S14G0S2Vr;R2A2A2S12A2A3F_;Fv;").
Proof. intros v Hv. apply U_shp. exact Hv. Qed.

Lemma F_L_intro : ltac2:(tb__ "0|3|
S1eS1eS17S1eS14Q40M0S2Vr;P8cA2A2R2A3S17S1eS14G0S2Vr;P8dA2A2R2A3S20VB;S24Z8M1R4A2A2S20S21S24G1R5A2G1A2S21VB;VL;A2A2S23R6R5A2S23R6S22Z2Z3dA2A2S20S24G1R7A2S25S21S21VB;VO;A2VN;A2Z1A2M2A2S20G2S21S24G1R8A2Z7A2A2S1cS0S3Vr;A1S45VvB;VvL;Vlastx;A3A3F_;F_;F_;F_;F_;F_;F_;F_;Fl;Fc;").
Proof using HZ HN.
  intros c l Ec El H1 H2 H3 H4 H5 H6. unfold opZ in HZ.
  pose proof (urange (rw r ib)). pose proof (urange (rw r il)). pose proof (urange (rw r io)).
  assert (Hc : bv_unsigned (rw r 140) < 2 ^ 61) by lia.
  assert (Eg8c : UU r (g8 cur) = 8 * c) by (unfold cur; rewrite (V_g8 140 Hc); lia).
  assert (Eg8l : UU r (g8 gl) = 8 * l) by (unfold gl; rewrite (V_g8 141 ltac:(lia)); lia).
  unfold F_L, F8of.
  constructor. { cbn [holds]. rewrite Eg8c. change (eval r vB) with (rw r ib). lia. }
  constructor. { cbn [holds]. unfold add at 1. rewrite (U_addc r (g8 cur) 8 (8 * c) Eg8c) by lia. fold (add vB vL). rewrite V_BL. lia. }
  constructor. { cbn [holds]. reflexivity. }
  constructor. { cbn [holds]. rewrite (U_lit64 r (2 ^ 61 - 1)) by lia. change (eval r cur) with (rw r 140). lia. }
  constructor. { cbn [holds]. change (eval r cur) with (rw r 140). change (eval r gl) with (rw r 141). lia. }
  constructor. { cbn [holds]. rewrite Eg8l, V_last. lia. }
  constructor. { cbn [holds]. unfold add at 1. rewrite (U_addc r (g8 gl) 7 (8 * l) Eg8l) by lia. rewrite V_last. lia. }
  constructor. { cbn [holds]. rewrite (U_lit64 r (2 ^ 61 - 1)) by lia. change (eval r gl) with (rw r 141). lia. }
  constructor.
Qed.
End Vals.

Lemma in_facts_Z : ltac2:(tb__ "0|e|
S1S6bR1Vib;Vil;Vio;A4S16S20Z1M0S14Q40M1S2R2P12M2A2A2M3A2S20G3S22Z2M4Z28A2A2A2S1cS0S3R3A1S2cS0S50S49P8eM5Vopd;A3S2cS0S50S4eP8dM6Vlastx;A3S2aS0ScSbS89S6eS49A1S6eS4eA1A3A1S2bS0A1A3A3A3A3S14G1S2R4Vib;A2A2S1eS14G1S2R5Vio;A2A2S1eS14G1S2R6G2A2A2S1eS14G1S2R7G5A2A2S1eS14G1S2R8G6A2A2S1eS16S16S20S24Z8M7R2A2M8S21R5R4A2M9A2S20G9S21G8Z7MaA2A2A2S16S23R2S22G4Z3dA2MbA2S16S16S20S24G7R1A2McS25S21G9R3A2G0A2MdA2S20GdS21GcGaA2A2A2S16S23R1GbA2S23R2R1A2A2A2A2A2Tl;Tg;TN;TO;TB;F_;F_;F_;Frho;").
Proof.
  intros rho HZ HN HF. pose proof HZ as HZ'. unfold opZ in HZ'.
  pose proof (urange (rw rho ib)). pose proof (urange (rw rho io)). pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  have_fact A1 HF (SPUle (g8 gs) opd). have_fact A2 HF (SPUle opd (add (g8 gs) (SLit 7))). have_fact A3 HF (SPUle gs (SLit (2 ^ 61 - 1))).
  have_fact A4 HF (SPUle (g8 gl) lastx). have_fact A5 HF (SPUle lastx (add (g8 gl) (SLit 7))). have_fact A6 HF (SPUle gl (SLit (2 ^ 61 - 1))).
  have_fact A7 HF (SPNot (SPBranch BC_GEU (shp gs) (shp gl))).
  rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia. rewrite (U_lit64 rho (2 ^ 61 - 1)) in A6 by lia.
  change (eval rho gs) with (rw rho 142) in A3. change (eval rho gl) with (rw rho 141) in A6.
  assert (Hg : bv_unsigned (rw rho 142) < 2 ^ 61) by lia. assert (Hl : bv_unsigned (rw rho 141) < 2 ^ 61) by lia.
  pose proof (V_g8 rho 142 Hg) as Eg. pose proof (V_g8 rho 141 Hl) as El. unfold gs in A1, A2, A7. unfold gl in A4, A5, A7.
  rewrite Eg in A1. rewrite El in A4.
  pose proof (V_opd rho HZ HN) as Vo. pose proof (V_last rho HZ HN) as Vl.
  rewrite Vo in A1. rewrite Vo in A2. rewrite Vl in A4. rewrite Vl in A5.
  unfold add in A2, A5.
  pose proof (U_addc rho (g8 (SVar 142)) 7 _ Eg ltac:(lia) ltac:(lia)) as T1. rewrite T1 in A2.
  pose proof (U_addc rho (g8 (SVar 141)) 7 _ El ltac:(lia) ltac:(lia)) as T2. rewrite T2 in A5.

  cbn [holds branch_taken] in A7. unfold bv_ltu in A7.
  pose proof (V_shp rho 142 ltac:(lia)) as S1. pose proof (V_shp rho 141 ltac:(lia)) as S2.
  assert (Hgl : bv_unsigned (rw rho 142) < bv_unsigned (rw rho 141)).
  { destruct (Z.ltb_spec (UU rho (shp (SVar 142))) (UU rho (shp (SVar 141)))) as [Hlt|Hge];
      [rewrite S1, S2 in Hlt; lia | exfalso; apply A7; reflexivity]. }
  cbv zeta. repeat split; lia.
Qed.

Lemma bk_facts_Z : ltac2:(tb__ "0|8|
S1S6bR1Vib;Vil;Vio;A4S16S20Z1M0S14Q40M1S2R2P12M2A2A2M3A2S20G3S22Z2M4Z28A2A2A2S1cS0S3R3A1S2cS0S45VvB;VvL;Vlastx;A3S2aS0SbS8bS72S44G0A2S6eS4eA1A3S2bS0A1A3A3A3S14G1S2R4Vib;A2A2S1eS14G1S2R5Vil;A2A2S1eS14G1S2R6Vio;A2A2S1eS14G1S2R7G2A2A2S1eS14G1S2R8P8cA2A2S1eS14G1S2R9P8dA2A2S1eS16S20R6S24Z8M5R2A2A2S16S23R2R1A2S16S23R1S22G4Z3dA2A2S16S16S20S24G5R1A2M6S25S21S21R6R4A2R3A2G0A2M7A2S20G7S21G6Z7A2A2A2S1bS17S1eS21R2G0A2R1A3A1A2A2A2A2Tl;Tc;TN;TO;TL;TB;F_;F_;F_;Frho;").
Proof.
  intros rho HZ HN HF. pose proof HZ as HZ'. unfold opZ in HZ'.
  pose proof (urange (rw rho ib)). pose proof (urange (rw rho io)). pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  apply Forall_app in HF as [HL HB].
  have_fact A1 HL (SPUle vB (g8 cur)). have_fact A3 HL (SPUle cur (SLit (2 ^ 61 - 1))). have_fact A4 HL (SPUlt cur gl).
  have_fact A5 HL (SPUle (g8 gl) lastx). have_fact A6 HL (SPUle lastx (add (g8 gl) (SLit 7))). have_fact A7 HL (SPUle gl (SLit (2 ^ 61 - 1))).
  have_fact A8 HB (SPBranch BC_NE (shpk cur 1) (shp gl)).
  rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia. rewrite (U_lit64 rho (2 ^ 61 - 1)) in A7 by lia.
  change (eval rho cur) with (rw rho 140) in A3, A4. change (eval rho gl) with (rw rho 141) in A4, A7.
  change (eval rho vB) with (rw rho ib) in A1.
  assert (Hc : bv_unsigned (rw rho 140) < 2 ^ 61) by lia. assert (Hl : bv_unsigned (rw rho 141) < 2 ^ 61) by lia.
  pose proof (V_g8 rho 140 Hc) as Ec. pose proof (V_g8 rho 141 Hl) as El. unfold cur in A1, A8. unfold gl in A5, A6, A8.
  rewrite Ec in A1. rewrite El in A5. pose proof (V_last rho HZ HN) as Vl. rewrite Vl in A5. rewrite Vl in A6.
  unfold add in A6. pose proof (U_addc rho (g8 (SVar 141)) 7 _ El ltac:(lia) ltac:(lia)) as T2. rewrite T2 in A6.

  cbn [holds branch_taken] in A8. unfold bv_eqb in A8. apply negb_true_iff in A8. apply Z.eqb_neq in A8.
  pose proof (V_shp rho 141 ltac:(lia)) as S2. rewrite S2 in A8.
  unfold shpk, add in A8.
  rewrite (U_addc rho (SVar 140) (SHB + 1) (bv_unsigned (rw rho 140)) eq_refl) in A8 by (unfold SHB; lia).
  cbv zeta. repeat split; try lia.
Qed.
End LoopZ.

Ltac split_mid HF HX HT :=
  cbn [ax_S ss_facts mid_state mkA] in HF; apply Forall_app in HF as [HX HT].

Lemma FT_Z : ltac2:(tb__ "0|1|
S1S1cS0S3R1A1S41A3S16S6bR2PfP10P11A4S16S6bR2P13P34P35A4S16S20Z1S14Q40S2R2P12A2A2M0A2S20G0S22Z2Z28A2A2A2A2A2F_;Frho;").
Proof.
  intros rho HF. unfold FT in HF. apply Forall_app in HF as [_ HB].
  destruct (base_mc_Z rho HB) as (ZD & ZS & ZN & _). auto.
Qed.

Lemma opZ_sub : ltac2:(tb__ "0|1|
S1S3cS1fS1fS1fS82R3S38A2M0G0G0S17S28S3eR7S38A2S29A3S6bR9R7R6R5A4S6bS3bRaR9A2R8R7R6A4F_;F_;F_;F_;F_;Fio;Fil;Fib;Fs;Frho;").
Proof.
  intros rho s ib il io Hb Hl Ho Hid HZ.
  assert (E : forall v, (v < NF)%positive -> rw (rho_sub rho s) v = rw rho v).
  { intros v Hv. rewrite rw_sub, (wsub_get_id s NF v Hid Hv). reflexivity. }
  unfold opZ in *. cbv zeta in *.
  rewrite (E ib Hb), (E il Hl), (E io Ho), (E 18%positive eq_refl). exact HZ.
Qed.

Section Glue.
Variable rho : valuation.

Lemma glue_Ls_in : ltac2:(tb__ "0|0|
S1cS0S3Vrho;A1S6S2fS5fA1A1A3S1cS0S3S3bVrho;S58A2A1S45S5aS5cS52A3A3F_;").
Proof.
  intros HF. unfold E_Ls_in in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (in_facts_Z 19 52 53 rho ZS ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZS as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ls_in).
  assert (ZS' : opZ rho' 19 52 53) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity. assert (E19 : rw rho' 19 = rw rho 19) by reflexivity.
  assert (E52 : rw rho' 52 = rw rho 52) by reflexivity. assert (E53 : rw rho' 53 = rw rho 53) by reflexivity.
  pose proof (Z.div_mod (bv_unsigned (rw rho 19)) 8 ltac:(lia)) as D. pose proof (urange (rw rho 53)) as R53.
  apply (F_L_intro 19 52 53 rho' ZS' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 141)));
    try reflexivity; rewrite ?E18, ?E19, ?E52, ?E53; unfold HSE in *; lia.
Qed.

Lemma glue_Ls_bk : ltac2:(tb__ "0|0|
S1cS0S3Vrho;A1S6S2fS5eA1A1A3S1cS0S3S3bVrho;S57A2A1S45S5aS5cS52A3A3F_;").
Proof.
  intros HF. unfold E_Ls_bk in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (bk_facts_Z 19 52 53 rho ZS ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZS as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ls_bk).
  assert (ZS' : opZ rho' 19 52 53) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity.
  assert (E140 : bv_unsigned (rw rho' 140) = bv_unsigned (rw rho 140) + 1).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_Ls_bk Pos.eqb]. unfold add, cur.
    apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  assert (E19 : rw rho' 19 = rw rho 19) by reflexivity.
  assert (E52 : rw rho' 52 = rw rho 52) by reflexivity. assert (E53 : rw rho' 53 = rw rho 53) by reflexivity.
  assert (E141 : rw rho' 141 = rw rho 141) by reflexivity.
  apply (F_L_intro 19 52 53 rho' ZS' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 140) + 1) (bv_unsigned (rw rho 141)));
    rewrite ?E18, ?E19, ?E52, ?E53, ?E141; unfold HSE in *; try lia.
Qed.

Lemma glue_Ld_in : ltac2:(tb__ "0|0|
S1cS0S3Vrho;A1S6S2fS5dA1A1A3S1cS0S3S3bVrho;S56A2A1S45S59S5bS51A3A3F_;").
Proof.
  intros HF. unfold E_Ld_in in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (in_facts_Z 15 16 17 rho ZD ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZD as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ld_in).
  assert (ZD' : opZ rho' 15 16 17) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity. assert (E15 : rw rho' 15 = rw rho 15) by reflexivity.
  assert (E16 : rw rho' 16 = rw rho 16) by reflexivity. assert (E17 : rw rho' 17 = rw rho 17) by reflexivity.
  pose proof (Z.div_mod (bv_unsigned (rw rho 15)) 8 ltac:(lia)) as D. pose proof (urange (rw rho 17)) as R17.
  apply (F_L_intro 15 16 17 rho' ZD' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 141)));
    try reflexivity; rewrite ?E18, ?E15, ?E16, ?E17; unfold HSE in *; lia.
Qed.

Lemma glue_Ld_bk : ltac2:(tb__ "0|0|
S1cS0S3Vrho;A1S6S2fS4fA1A1A3S1cS0S3S3bVrho;S55A2A1S45S59S5bS51A3A3F_;").
Proof.
  intros HF. unfold E_Ld_bk in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (bk_facts_Z 15 16 17 rho ZD ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZD as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ld_bk).
  assert (ZD' : opZ rho' 15 16 17) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity.
  assert (E140 : bv_unsigned (rw rho' 140) = bv_unsigned (rw rho 140) + 1).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_Ld_bk Pos.eqb]. unfold add, cur.
    apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  assert (E15 : rw rho' 15 = rw rho 15) by reflexivity.
  assert (E16 : rw rho' 16 = rw rho 16) by reflexivity. assert (E17 : rw rho' 17 = rw rho 17) by reflexivity.
  assert (E141 : rw rho' 141 = rw rho 141) by reflexivity.
  apply (F_L_intro 15 16 17 rho' ZD' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 140) + 1) (bv_unsigned (rw rho 141)));
    rewrite ?E18, ?E15, ?E16, ?E17, ?E141; unfold HSE in *; try lia.
Qed.

Lemma meas_Ls_in : ltac2:(tb__ "0|0|
S17S15Q40A1S4S3bVrho;S58A2S44A2S4Vrho;S49A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ls_bk : ltac2:(tb__ "0|0|
S17S15Q40A1S4S3bVrho;S57A2S44A2S4Vrho;S6dS44S9Z1A1A2A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ld_in : ltac2:(tb__ "0|1|
S17S15Q40A1S4S3bVrho;S56A2S6dS44S9S22Z2Z3eA2A1M0A2A2S4Vrho;S6dS49G0A2A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ld_bk : ltac2:(tb__ "0|2|
S1cS0S3Vrho;A1S6S2fS4fA1A1A3S20S14Q40M0S4Vrho;S6dS44S9S21S22Z2Z3eA2M1Z1A2A1A2A2A2S14G0S4S3bVrho;S55A2S6dS44S9G1A1A2A2A2A2F_;").
Proof.
  intros HF. unfold E_Ld_bk in HF. split_mid HF HX HT. apply Forall_app in HX as [HL _].
  have_fact A3 HL (SPUle cur (SLit (2 ^ 61 - 1))). rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia.
  change (eval rho cur) with (rw rho 140) in A3. pose proof (urange (rw rho 140)) as R140.
  assert (E1 : bv_unsigned (rw (rho_sub rho s_Ld_bk) 140) = bv_unsigned (rw rho 140) + 1).
  { rewrite rw_sub. cbn [wsub_get s_Ld_bk Pos.eqb]. unfold add, cur. apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  unfold add, cur.
  rewrite (U_addc rho (SVar 140) (2 ^ 62 + 1) (bv_unsigned (rw rho 140)) eq_refl) by lia.
  rewrite (U_addc (rho_sub rho s_Ld_bk) (SVar 140) (2 ^ 62) (bv_unsigned (rw rho 140) + 1) E1) by lia.
  lia.
Qed.
End Glue.

Lemma FT_of_E : ltac2:(tb__ "0|0|
S46S31S1S1cS0S3R1A1S6S2fS46A1A1A3S1cS0S3R2A1S41A3F_;Fr;TE;").
Proof. intros E r HF. cbn [ax_S ss_facts E_src mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Edst : ltac2:(tb__ "0|0|
S1S1cS0S3R1A1S6S2fS47A1A1A3S1cS0S3R2A1S41A3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_dst mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Ereal : ltac2:(tb__ "0|0|
S1S1cS0S3R1A1S6S2fS4bA1A1A3S1cS0S3R2A1S41A3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_real mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Lemma next_E : ltac2:(tb__ "0|0|
S16S81S38S5S2fS46A1A1A2S16S81S38S5S2fS47A1A1A2S81S38S5S2fS4bA1A1A2A2A2").
Proof. repeat split; cbv; congruence. Qed.
Lemma FT_of_E_cls : ltac2:(tb__ "0|0|
S27S0A1S1S1cS0S3R1A1S6S2fS78R2S46A2A1A1A3S1cS0S3R2A1S41A3F_;Fr;FF;").
Proof. intros F r HF. cbn [ax_S ss_facts E_src mid_state mkA ax_add_facts ax_setS add_facts] in HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Edst_cls : ltac2:(tb__ "0|0|
S27S0A1S1S1cS0S3R1A1S6S2fS78R2S47A2A1A1A3S1cS0S3R2A1S41A3F_;Fr;FF;").
Proof. intros F r HF. cbn [ax_S ss_facts E_dst mid_state mkA ax_add_facts ax_setS add_facts] in HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Lemma hi_fact_holds : ltac2:(tb__ "0|0|
S1S1fS20S70S14Q40S2R2R1A2A2A2S1cS0S3R3A1S2aS0S64S7R2A1A1S2bS0A1A3A3F_;Fib;Frho;").
Proof. intros rho ib H. constructor; [|constructor]. unfold hi_fact. cbn [holds]. rewrite (U_lit64 rho HSE) by (unfold HSE; lia). exact H. Qed.
Lemma lo_fact_holds : ltac2:(tb__ "0|1|
S1S1fS1fS20S21S14Q40M0S2R3R2A2A2S14G0S2R3R1A2A2A2S25S12Z8A2A2S1cS0S3R4A1S2aS0S65S7R3A1S7R2A1A2S2bS0A1A3A3F_;Fil;Fib;Frho;").
Proof.
  intros rho ib il H. pose proof (urange (rw rho ib)). pose proof (urange (rw rho il)). constructor; [|constructor]. unfold lo_fact, add. cbn [holds].
  rewrite (U_add2 rho (SVar ib) (SVar il) (bv_unsigned (rw rho ib)) (bv_unsigned (rw rho il)) eq_refl eq_refl) by (unfold SHB in H; lia).
  rewrite (U_lit64 rho (SHB - 8)) by (unfold SHB; lia). exact H.
Qed.

Lemma FTbT1 : ltac2:(tb__ "0|0|
S30S3fS30R1S87A3S17S28S40S0S8S5S2fS7eS69S86S32R2A1S46S62A5A1A1A1S41A3S29A3F_;FL;").
Proof. intros L [<-|[]]. exact (proj1 FT_below_T). Qed.
Lemma FTbT2 : ltac2:(tb__ "0|0|
S30S3fS30R1S87A3S17S28S40S0S8S5S2fS7eS67S86S32R2A1S47S60A5A1A1A1S41A3S29A3F_;FL;").
Proof. intros L [<-|[]]. exact (proj1 (proj2 FT_below_T)). Qed.
Lemma FTbT3 : ltac2:(tb__ "0|0|
S30S3fS30R1S8cA3S17S28S40S0S8S5S2fS7eS68S8dS32R2A1S4bS61A5A1A1A1S41A3S29A3F_;FL;").
Proof. intros L [<-|[<-|[]]]; [exact (proj1 (proj2 (proj2 FT_below_T))) | exact (proj2 (proj2 (proj2 FT_below_T)))]. Qed.

Section Sum.
Variable ok : assn.
Variable J : jpredA.
Hypothesis Hok : ltac2:(tb__ "0|0|
S37S11Vok;VJ;A3").
Hypothesis Hst : stableA segs NF J.

Hypothesis HclsD : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S27S3aA1S39VJ;R4R3R2R1A4S6cR5PfP10A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HclsS : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S27S3aA1S39VJ;R4R3R2R1A4S6cR5P13P34A3F_;Fmd;Ftr;Ft;Fr;").

Lemma cfg_mc_sound : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S31S3fS31R1S63A3S1S75S11Vok;S33S11S79S1SaS38R6R1A3Lr;VJ;A2R3R1R4A5S34S11VJ;S38R5R4S42A6A4FrhoT;F_;FT;Ftp;Frho;").
Proof.
  intros rho tp T HinT rhoT.
  destruct ids_mc as (I1 & I2 & I3 & I4).
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok (withGA (fun r => agree_below NF rho r) J)).
  { intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto. }
  apply (cfg_soundA segs FUELM cutpcs_mc NF cuts_mc exits_mc (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_mc) tp HokG HstG check_mc); [|exact HinT].
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
  - apply exit_postA. in_nth 0.
  -
    apply triple_SPA_pure. intros tr0 md0 [_ HJ0].
    eapply triple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_src rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsS rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_src_hi Pre_rip s_src R_src Posts_rip FT Hst fr_src_hi cc_src_hi (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 2]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 19 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_src_lo Pre_rip_lo s_src R_src Posts_rip FT Hst fr_src_lo cc_src_lo (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum_lo ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 2]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 19 52 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  -
    apply triple_SPA_pure. intros tr0 md0 [_ HJ0].
    eapply triple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_dst rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_dst_hi Pre_rip s_dst R_dst Posts_rip FT Hst fr_dst_hi cc_dst_hi (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 3]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_dst_lo Pre_rip_lo s_dst R_dst Posts_rip FT Hst fr_dst_lo cc_dst_lo (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum_lo ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 3]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA ok J NF rho tp E_real Pre_ahA s_real R_real Posts_ahA FT Hst fr_real cc_real (proj2 (proj2 next_E)) FT_of_Ereal FT_below_E FTbT3
             cuts_mc _ Hok).
    + intros ok' Jq rho1 tp1 Ho Hs. exact (memcpy_ah_sumA ok' Jq rho1 tp1 Ho Hs).
    + intros L [<-|[<-|[]]]; [in_nth 4 | in_nth 5].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ls_in CLs_0 (F_L vBs vLs lasts) s_Ls_in tp);
      [in_nth 6 | exact ent_Ls_in | exact I1 | exact HstG | exact FLs_below | intros r tp' tr md _ HF; exact (glue_Ls_in r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ls_bk CLs_0 (F_L vBs vLs lasts) s_Ls_bk tp);
      [in_nth 6 | exact ent_Ls_bk | exact I2 | exact HstG | exact FLs_below | intros r tp' tr md _ HF; exact (glue_Ls_bk r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ld_in CLd_0 (F_L vBd vLd lastd) s_Ld_in tp);
      [in_nth 7 | exact ent_Ld_in | exact I3 | exact HstG | exact FLd_below | intros r tp' tr md _ HF; exact (glue_Ld_in r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ld_bk CLd_0 (F_L vBd vLd lastd) s_Ld_bk tp);
      [in_nth 7 | exact ent_Ld_bk | exact I4 | exact HstG | exact FLd_below | intros r tp' tr md _ HF; exact (glue_Ld_bk r HF)].
Qed.

Theorem memcpy_icpt_sum1 : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S75S11Vok;S33S11VJ;S4cR2R1A5S34S11VJ;S38R2R1S42A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc1 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_mc_sound rho tp Pre_mc1). left; reflexivity.
Qed.

Theorem memcpy_icpt_sum2 : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S75S11Vok;S33S11VJ;S4dR2R1A5S34S11VJ;S38R2R1S42A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc2 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_mc_sound rho tp Pre_mc2). right; left; reflexivity.
Qed.
End Sum.

Lemma etriple_SPA_pure' : ltac2:(tb__ "0|2|
S35S31S1S27S15Q40A1A1M0S74OF_;S27S3aA1M1S39R7R5R4R2R1A4S73S11S33S11S1G0G1S39S16RcR4R3R2R1A4S16S17G1R2R7A3S17S39R1R6A3A2A2Lm;Lt;Lp;Lr;R7R6R5A5R4A3F_;Fmd;Ftr;S73S11S33S11R6R5R4R3A5R2A3F_;FQ;Ftp;Frho;FA;FJ;").
Proof.
  intros J A rho tp Q H w [Hsm Hk]. destruct w as [tr [ms md]]. apply (H tr md Hk). split; [exact Hsm|]. cbn. auto.
Qed.

Section SumEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.
Hypothesis HclsD : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S27S3aA1S39VJ;R4R3R2R1A4S6cR5PfP10A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HclsS : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S27S3aA1S39VJ;R4R3R2R1A4S6cR5P13P34A3F_;Fmd;Ftr;Ft;Fr;").

Ltac meas_lit := intros r r'; unfold vmeasIA; cbn [vna_var vna_rank eval]; rewrite ?u64_lit by lia; lia.

Lemma cfg_mc_complete : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S77S3fS77R1S6aA3S1S73S11S33S11S79S1SaS38R6R1A3Lr;VJ;A2S7aR3A1R1R4A5S34S11VJ;S38R5R4S42A6A3FrhoT;F_;Fn;Ftp;Frho;").
Proof.
  intros rho tp n HinT rhoT.
  destruct ids_mc as (I1 & I2 & I3 & I4).
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  apply (cfg_complete_autoIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_mc) tp HstG); [ | exact echeck_mc | | exact HinT].
  { intros m Hm. unfold vcuts_mc in Hm. repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm. }
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
  - apply (eexit_post_IA0 segs J NF rho vcuts_mc Posts_mc (mkVNA P_icpt 0 (SLit (2 ^ 64 - 1)))). in_nth 0.
  - apply etriple_SPA_pure'. intros tr0 md0 [_ HJ0].
    eapply etriple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_src rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsS rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_src_hi Pre_rip s_src R_src Posts_rip FT Hst fr_src_hi cc_src_hi (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1
                   vcuts_mc _ (mkVNA E_src_hi 120 (SLit (2 ^ 61))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 119 (SLit (2 ^ 61))); split; [in_nth 2|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 19 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_src_lo Pre_rip_lo s_src R_src Posts_rip FT Hst fr_src_lo cc_src_lo (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1
                   vcuts_mc _ (mkVNA E_src_lo 120 (SLit (2 ^ 61))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_lo_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 119 (SLit (2 ^ 61))); split; [in_nth 2|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 19 52 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply etriple_SPA_pure'. intros tr0 md0 [_ HJ0].
    eapply etriple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_dst rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_dst_hi Pre_rip s_dst R_dst Posts_rip FT Hst fr_dst_hi cc_dst_hi (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2
                   vcuts_mc _ (mkVNA E_dst_hi 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T2 79 (SLit (2 ^ 63))); split; [in_nth 3|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_dst_lo Pre_rip_lo s_dst R_dst Posts_rip FT Hst fr_dst_lo cc_dst_lo (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2
                   vcuts_mc _ (mkVNA E_dst_lo 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_lo_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T2 79 (SLit (2 ^ 63))); split; [in_nth 3|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA_ex J NF rho tp E_real Pre_ahA s_real R_real Posts_ahA FT Hst fr_real cc_real (proj2 (proj2 next_E)) FT_of_Ereal FT_below_E FTbT3
             vcuts_mc _ (mkVNA E_real 40 (SLit (2 ^ 63 + 8))) eq_refl).
    + intros Jq rho1 tp1 Hs. exact (memcpy_ah_sumA_ex Jq rho1 tp1 Hs).
    + intros L [<-|[<-|[]]].
      * exists (mkVNA T3a 39 (SLit (2 ^ 63 + 8))). split; [in_nth 4|]. split; [reflexivity|]. meas_lit.
      * exists (mkVNA T3b 39 (SLit (2 ^ 63 + 8))). split; [in_nth 5|]. split; [reflexivity|]. meas_lit.
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ls_in 151 gs) (mkVNA CLs 150 cur) (F_L vBs vLs lasts) CLs_0 s_Ls_in tp);
      [in_nth 6 | reflexivity | exact ent_Ls_in | exact I1 | exact HstG | exact FLs_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ls_in r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ls_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ls_bk 151 (add cur (SLit 1))) (mkVNA CLs 150 cur) (F_L vBs vLs lasts) CLs_0 s_Ls_bk tp);
      [in_nth 6 | reflexivity | exact ent_Ls_bk | exact I2 | exact HstG | exact FLs_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ls_bk r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ls_bk r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ld_in 101 (add gs (SLit (2 ^ 62)))) (mkVNA CLd 100 (add cur (SLit (2 ^ 62)))) (F_L vBd vLd lastd) CLd_0 s_Ld_in tp);
      [in_nth 7 | reflexivity | exact ent_Ld_in | exact I3 | exact HstG | exact FLd_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ld_in r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ld_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ld_bk 101 (add cur (SLit (2 ^ 62 + 1)))) (mkVNA CLd 100 (add cur (SLit (2 ^ 62)))) (F_L vBd vLd lastd) CLd_0 s_Ld_bk tp);
      [in_nth 7 | reflexivity | exact ent_Ld_bk | exact I4 | exact HstG | exact FLd_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ld_bk r HF) | right; split; [cbn [vna_var]; exact (meas_Ld_bk r HF) | cbn; lia]]
      | cbn; lia | cbn; lia].
Qed.

Theorem memcpy_icpt_sum1_ex : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S73S11S33S11VJ;S4cR2R1A5S34S11VJ;S38R2R1S42A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc1 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_mc1 with (vna_state (mkVNA Pre_mc1 200 (SLit 0))).
  apply (cfg_mc_complete rho tp). left; reflexivity.
Qed.

Theorem memcpy_icpt_sum2_ex : ltac2:(tb__ "0|0|
S1S27S15Q40A1A1S73S11S33S11VJ;S4dR2R1A5S34S11VJ;S38R2R1S42A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc2 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_mc2 with (vna_state (mkVNA Pre_mc2 200 (SLit 0))).
  apply (cfg_mc_complete rho tp). right; left; reflexivity.
Qed.
End SumEx.

Lemma soff_var' : ltac2:(tb__ "0|1|
S1S1fS23S14Q40M0S2R2R1A2A2S22Z2Z3fA2A2S17S1eSfR3S7R2A1A2S14G0S2R3R2A2A2A3F_;Fi;Frho;").
Proof.
  intros rho i Hi. unfold soff. cbn [eval]. rewrite bv_signed_U.
  destruct (Zsigned_spec (bv_unsigned (rw rho i))) as [[_ X]|[Y X]]; [exact X|]. pose proof (urange (rw rho i)). lia.
Qed.

Section Public.
Variable rho : valuation.
Let a := bv_unsigned (eval rho dst). Let b := bv_unsigned (eval rho src). Let n := bv_unsigned (rw rho 18).

Lemma pre_disjoint : ltac2:(tb__ "0|1|
S27S15Q40A1A1M0S74S18S33S11S1G0S27S3aA1S39S1aL_;L_;L_;L_;S43Vrho;R2R1A6S19S35S35S33S11R1S43Vrho;R3R2A6LJ;A2A2S23Vn;S22Z2Z3fA2A2S18S20S21Va;Vn;A2Vb;A2S18S20S21Vb;Vn;A2Va;A2S17S1eVn;Z0A3A2A2F_;F_;Fw;Ftp;").
Proof.
  intros tp w HS Hn.
  assert (Hsm : smatchA segs rho tp Pre_mc0 w) by (destruct HS as [[H _]|[J [H _]]]; exact H).
  destruct Hsm as (Hsm & _). destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpd & _) & _).
  cbn [ss_objs ax_S Pre_mc0 mkA objs_mc app pairwise_disjoint] in Hpd.
  destruct Hpd as (_ & _ & HD & _). apply Forall_inv in HD.
  unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of, O_dst, O_src in HD. cbn [ob_base ob_lo ob_hi fst snd] in HD.
  rewrite !soff_lit_small in HD by lia.
  assert (Es : soff rho vN = n) by (unfold vN; apply soff_var'; subst n; lia). rewrite !Es in HD.
  subst a b. lia.
Qed.

Lemma pre_Z : ltac2:(tb__ "0|5|
S1cS0S3Vrho;A1S48A3S16S17S1eVa;S21S14Q40M0S2Vrho;PfM1A2A2S14G0S2Vrho;P11M2A2A2A2A3S16S17S1eVb;S21S14G0S2Vrho;P13M3A2A2S14G0S2Vrho;P35M4A2A2A2A3S16S6bVrho;G1P10G2A4S16S6bVrho;G3P34G4A4S16S20Z1Vn;A2S20Vn;S22Z2Z28A2A2A2A2A2A2A2F_;").
Proof.
  intros HF. destruct (base_mc_Z rho HF) as (ZD & ZS & ZN & _).
  split; [exact (V_opd 15 16 17 rho ZD ZN)|]. split; [exact (V_opd 19 52 53 rho ZS ZN)|]. auto.
Qed.

Lemma xor_fact_Z : ltac2:(tb__ "0|0|
S10S1eS17S1eS14Q40S4Vrho;R2A2A2R1A3S20S21R2Vn;A2S25S22Z2Z40A2Z1A2A2S3Vrho;ScSbS8aSdS88R4S9ZffffffffffffffffA1A3S6fA3A1A2F_;F_;Fx;Fe;").
Proof.
  intros e x He Hx. cbn [holds branch_taken]. unfold bv_ltu.
  rewrite (U_xor_m1 rho e 18446744073709551615 eq_refl). rewrite He. change (eval rho vN) with (rw rho 18).
  unfold M64v. rewrite Z.ltb_lt. subst n. lia.
Qed.

Lemma facts1 : ltac2:(tb__ "0|1|
S1cS0S3Vrho;A1M0S48A3S20S21Va;Vn;A2Vb;A2S1cS0G0S2aS0S53S4aA3A3F_;F_;").
Proof.
  intros HF Hab. destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN). pose proof ZD as ZD'. pose proof ZS as ZS'.
  unfold opZ in ZD', ZS'. cbv zeta in ZD'. cbv zeta in ZS'. unfold HSE in *.
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 19)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 53)).
  pose proof (urange (rw rho 18)). unfold ord1, xor_facts.
  constructor.
  { cbn [holds]. unfold add at 1. rewrite (U_add2 rho dst vN a n eq_refl eq_refl) by (subst a n; lia). fold b. lia. }
  constructor. { apply (xor_fact_Z src b eq_refl). subst b n. lia. }
  constructor. { apply (xor_fact_Z dst a eq_refl). subst a n. lia. }
  constructor.
Qed.

Lemma facts2 : ltac2:(tb__ "0|1|
S1cS0S3Vrho;A1M0S48A3S20S21Vb;Vn;A2Va;A2S1cS0G0S2aS0S54S4aA3A3F_;F_;").
Proof.
  intros HF Hab. destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN). pose proof ZD as ZD'. pose proof ZS as ZS'.
  unfold opZ in ZD', ZS'. cbv zeta in ZD'. cbv zeta in ZS'. unfold HSE in *.
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 19)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 53)).
  pose proof (urange (rw rho 18)). unfold ord2, xor_facts.
  constructor.
  { cbn [holds]. unfold add at 1. rewrite (U_add2 rho src vN b n eq_refl eq_refl) by (subst b n; lia). fold a. lia. }
  constructor. { apply (xor_fact_Z src b eq_refl). subst b n. lia. }
  constructor. { apply (xor_fact_Z dst a eq_refl). subst a n. lia. }
  constructor.
Qed.

Lemma F1_below : ltac2:(tb__ "0|0|
S17S28S40S0S8S5S2fS43A1A1A1S2aS0S53S4aA3A3S29A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2_below : ltac2:(tb__ "0|0|
S17S28S40S0S8S5S2fS43A1A1A1S2aS0S54S4aA3A3S29A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma SPA_cases : ltac2:(tb__ "0|0|
S35S27S15Q40A1A1S74S33S11R3S43Vrho;R2R1A6S18S33S11R4S4cVrho;R3R2A6S33S11R4S4dVrho;R3R2A6A2F_;Fw;Ftp;FJ;").
Proof.
  intros J tp w Hw. pose proof (SPA_facts_hold segs J rho Pre_mc0 tp w Hw) as HF. cbn [ax_S ss_facts Pre_mc0 mkA] in HF.
  destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN).
  destruct (pre_disjoint tp w (or_intror (ex_intro _ J Hw)) ltac:(lia)) as [H|[H|H]]; [left | right | exfalso; lia].
  - destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (facts1 HF H) | exact F1_below].
  - destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (facts2 HF H) | exact F2_below].
Qed.
End Public.

Theorem memcpy_icpt_rs_sum : ltac2:(tb__ "0|2|
S74OF_;S35S1S27S15Q40A1A1M0S37S11R4R3A3S36S11S38R4A3S1G0S27S3aA1M1S39R9R4R3R2R1A4S6cR5PfP10A3F_;Fmd;Ftr;Ft;Fr;S1G0G1S39RaR4R3R2R1A4S6cR5P13P34A3F_;Fmd;Ftr;Ft;Fr;S75S11R8S33S11R7S43R6R5A5S34S11R7S38R6R5S42A6A4F_;F_;F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst HD HS.
  eapply triple_conseq; [intros w Hw; exact (SPA_cases rho J tp w Hw) | intros w Hw; exact Hw |].
  apply triple_disj; [apply memcpy_icpt_sum1 | apply memcpy_icpt_sum2]; assumption.
Qed.

Theorem memcpy_icpt_rs_sum_ex : ltac2:(tb__ "0|2|
S35S1S27S15Q40A1A1M0S36S11S38R3A3S1G0S27S3aA1M1S39R8R4R3R2R1A4S6cR5PfP10A3F_;Fmd;Ftr;Ft;Fr;S1G0G1S39R9R4R3R2R1A4S6cR5P13P34A3F_;Fmd;Ftr;Ft;Fr;S73S11S33S11R6S43R5R4A5S34S11R6S38R5R4S42A6A3F_;F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst HD HS.
  eapply etriple_conseq; [intros w Hw; exact (SPA_cases rho J tp w Hw) | intros w Hw; exact Hw |].
  apply etriple_disj; [apply memcpy_icpt_sum1_ex | apply memcpy_icpt_sum2_ex]; assumption.
Qed.
End Icpt_memcpy_rs_proof.

