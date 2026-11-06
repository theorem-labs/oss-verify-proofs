(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From LinuxProcessSemantics.LinuxProcessSem Require Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uaccess Uapi Syscall.

(* [comment removed for export] *)
Module Icpt_memcpy_hdr_proof.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "ACEIL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "holds"; "ss_next"; "rw"; "sprop_below"; "ss_facts"; "SVar"; "agree_below"; "SAlu"; "SLit"; "SPBranch"; "SPNot"; "eval"; "sv"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "True"; "ex"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "modulo"; "sub"; "lt"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_hdr"; "FT"; "Posts_mc"; "Pre_mc0"; "E_src"; "E_dst"; "base_mc"; "xor_facts"; "E_real"; "Pre_mc1"; "Pre_mc2"; "ord1"; "ord2"; "R_dst"; "R_real"; "R_src"; "cuts_mc"; "opnd_facts"; "s_dst"; "s_real"; "s_src"; "vcuts_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof"; "clsZ"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Icpt_memcpy_hdr_proof.OpZ"; "opZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Icpt_memcpy_hdr_proof"; "opZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "vnodeA"; "withGA"; "vna_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_XOR"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "Posts_mhA"; "Pre_mhA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_hdr.
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
Module Icpt_memcpy_rs_proof.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "rw"; "holds"; "eval"; "ss_next"; "ss_facts"; "SVar"; "sprop_below"; "SLit"; "agree_below"; "SPBranch"; "SPNot"; "SAlu"; "sobj"; "soff"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "SHB"; "ACEIL"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "True"; "not"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "mul"; "sub"; "modulo"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "nil"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "wsub_get"; "wsub_id_below"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_rs"; "FT"; "Posts_mc"; "Pre_mc0"; "cur"; "F_L"; "E_src"; "E_dst"; "base_mc"; "gs"; "xor_facts"; "E_real"; "Pre_mc1"; "Pre_mc2"; "gl"; "E_Ld_bk"; "F8of"; "lastd"; "lasts"; "ord1"; "ord2"; "s_Ld_bk"; "s_Ld_in"; "s_Ls_bk"; "s_Ls_in"; "vBd"; "vBs"; "vLd"; "vLs"; "E_Ld_in"; "E_Ls_bk"; "E_Ls_in"; "R_dst"; "R_real"; "R_src"; "cuts_mc"; "hi_fact"; "lo_fact"; "opnd_facts"; "s_dst"; "s_real"; "s_src"; "vcuts_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Icpt_memcpy_rs_proof"; "opZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof"; "clsZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "add"; "shp"; "vN"; "HSE"; "g8"; "shpk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "ax_add_facts"; "withGA"; "vna_state"; "SPfamA"; "SPfamEA"; "enodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "call_checkA"; "entails_frA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Icpt_memcpy_rs_proof.OpZ"; "opZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "vmeasIA"; "to_enodeIA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof"; "Posts_rip"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_XOR"; "BC_GEU"; "BC_LTU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memcpyAH"; "Posts_ahA"; "Pre_ahA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memcpyAH.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy_rs.
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

(* [comment removed for export] *)
Module Str_strnlenA_st.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "true"; "bool"; "nil"; "pair"; "Some"; "option"; "false"; "list"; "prod"; "None"; "app"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SVar"; "ss_next"; "SLit"; "FcsrFrm0"; "mkSS"; "sprop"; "ss_lenient"; "sstate"; "swf"; "DUnknown"; "SAlu"; "SPUle"; "cell"; "mkObj"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "sym_runA"; "mkLeafA"; "axwf"; "entailsA"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "post_regs"; "pre_regs"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st"; "E_callS"; "Pre_sn"; "CUTS_SN"; "FUEL_SN"; "P_sn"; "s_call"; "D_SN"; "E_call"; "G_sn"; "R_call"; "R_sn"; "T_impF"; "facts_sn"; "T_imp"; "X_sn"; "objs_sn"; "sn_ret"; "sp_sn"; "O_winN"; "XN"; "sn_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "mkA"; "ACEIL"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXRebase"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "Pre_mci"; "O_realmc"; "O_strS"; "P_mci"; "Posts_mci"; "facts_mci"; "mci_entry"; "sX"; "vXB"; "vXL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "RsSymJump"; "@Stdlib.ZArith.BinInt.Z"; "add"; "opp"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "O_rtc3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "O_rtc2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations. Import MCHAddr. Import RegionAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition sn_entry : Z := 0xdb48c.
Definition sn_ret : Z := 0xdb4cc.
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
Module Icpt_read_proof.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "ACEIL"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "sub"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "rw"; "valuation"; "holds"; "eval"; "reg_sv"; "cell"; "ss_facts"; "SLit"; "sv"; "agree_below"; "sobj"; "sprop_below"; "SPBranch"; "DUnknown"; "SPNot"; "mkObj"; "soff"; "ss_next"; "ss_objs"; "ss_pc"; "@Corelib.Init.Datatypes"; "list"; "nil"; "Some"; "option"; "app"; "bool"; "true"; "cons"; "prod"; "length"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read"; "E_ecall"; "Fpos"; "Posts_rd"; "buf"; "Pre_rd"; "vC"; "FR"; "F_L"; "Posts_rd_d"; "cur"; "hc"; "gl"; "gs"; "E_reg"; "F8of"; "T_rd_d"; "lastb"; "s_L_bk"; "s_L_in"; "E_L_bk"; "E_L_in"; "E_pos"; "base_rd"; "vBb"; "vLb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "ok_frameA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "fd_lookup"; "m_fds"; "FdFile"; "m_fs"; "FdDir"; "MAX_RW_COUNT"; "TASK_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Icpt_read_proof"; "rdZ"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "shp"; "add"; "shpk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "fs_lookup"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "BC_GEU"; "BC_NE"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA"; "A_after_fresh"; "A_after_hdr"; "rbA_md'"; "rhA_rho'"; "rkA_rho'"; "rbA_bs"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Icpt_read_proof.BaseZ"; "rdZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "withGA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess Uapi Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL SysRead.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2 SysStepA SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import RegionAddr RDAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation "'UU' rho e" := (bv_unsigned (eval rho e)) (at level 10, rho at level 9, e at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Section BaseZ.
Variable rho : valuation.
Let B := bv_unsigned (rw rho 15). Let L := bv_unsigned (rw rho 16). Let O := bv_unsigned (rw rho 17). Let C := bv_unsigned (rw rho 19).

Definition rdZ : Prop := ltac2:(tb__ "0|7|
S2bS5S6VO;VC;A2VL;A2S2bS5VL;S9Z2M0Z28A2A2S2bS5Z1000M1VB;A2S2bS5S6VB;VL;A2SaS9G0Z2fA2M2Z8M3A2A2S2bS2cS47SbVB;G3A2Z0A3S2bS2bS5Z1VC;A2S5VC;Z10000A2A2S2bS2bS5S6S1G1A2S2Q40M4SdVrho;PaA2A2M5A2S5G5S9G0Z3fA2A2A2S2bS5G1S2G4SdVrho;P18A2A2M6A2S5G6G2A2A2A2A2A2A2A2A2A2").

Lemma base_rd_Z : ltac2:(tb__ "0|0|
S49ScSfVrho;A1S44A3S75F_;").
Proof.
  intros HF.
  pose proof (urange (rw rho 15)) as R15. pose proof (urange (rw rho 16)) as R16. pose proof (urange (rw rho 17)) as R17.
  pose proof (urange (rw rho 19)) as R19. pose proof (urange (rw rho 10)) as R10. pose proof (urange (rw rho 24)) as R24.
  have_fact A1 HF (SPUle (add vOb vC) vLb). have_fact A2 HF (SPUle vLb (SLit (2 ^ 40))). have_fact A3 HF (SPUle (SLit 4096) vBb).
  have_fact A4 HF (SPUle (add vBb vLb) (SLit (2 ^ 47 - 8))). have_fact A5 HF (SPAlign 15 3).
  have_fact A6 HF (SPUle (SLit 1) vC). have_fact A7 HF (SPUle vC (SLit 65536)).
  have_fact A8 HF (SPUle (SLit (ACEIL + 4096)) (SVar 10)). have_fact A9 HF (SPUle (SVar 10) (SLit (2 ^ 63))).
  have_fact A10 HF (SPUle (SLit 4096) (SVar 24)). have_fact A11 HF (SPUle (SVar 24) (SLit (2 ^ 47))).
  have_fact A12 HF (SPUle vOb vLb). have_fact A13 HF (SPUle vC vLb). have_fact A14 HF (SPUle vBb (SLit (2 ^ 47 - 8))).
  unfold vBb, vLb, vOb, vC, add in A1, A2, A3, A4, A6, A7, A12, A13, A14.
  rewrite (U_lit64 rho (2 ^ 40)) in A2 by lia. rewrite (U_lit64 rho 4096) in A3 by lia.
  pose proof (U_lit64 rho (2 ^ 47 - 8) ltac:(lia)) as T47. rewrite T47 in A4. rewrite T47 in A14.
  rewrite (U_lit64 rho 1) in A6 by lia. rewrite (U_lit64 rho 65536) in A7 by lia.
  rewrite (U_lit64 rho (ACEIL + 4096)) in A8 by (unfold ACEIL; lia). rewrite (U_lit64 rho (2 ^ 63)) in A9 by lia.
  rewrite (U_lit64 rho 4096) in A10 by lia. rewrite (U_lit64 rho (2 ^ 47)) in A11 by lia.
  cbn [eval] in A2, A3, A6, A7, A8, A9, A10, A11, A12, A13, A14.
  assert (B1 : 0 <= bv_unsigned (rw rho 17) + bv_unsigned (rw rho 19) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar 17) (SVar 19) (bv_unsigned (rw rho 17)) (bv_unsigned (rw rho 19)) eq_refl eq_refl B1) in A1. cbn [eval] in A1.
  assert (B2 : 0 <= bv_unsigned (rw rho 15) + bv_unsigned (rw rho 16) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar 15) (SVar 16) (bv_unsigned (rw rho 15)) (bv_unsigned (rw rho 16)) eq_refl eq_refl B2) in A4.
  destruct A5 as [_ A5]. change (2 ^ 3) with 8 in A5.
  unfold rdZ. subst B L O C. repeat split; lia.
Qed.
End BaseZ.

Lemma rd_Hi : ltac2:(tb__ "0|0|
S2cS24S6aA1S76S0S20S4aS2eA1A1A2S23S6aS6dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma rd_H17 : ltac2:(tb__ "0|0|
S2cS15S11S4aS2eA1Z11A2S14Z3fA1A3"). Proof. reflexivity. Qed.
Lemma rd_H10 : ltac2:(tb__ "0|0|
S2cS15S11S4aS2eA1ZaA2S14Z3A1A3"). Proof. reflexivity. Qed.
Lemma rd_H11 : ltac2:(tb__ "0|0|
S2cS15S11S4aS2eA1ZbA2S31A3"). Proof. reflexivity. Qed.
Lemma rd_H12 : ltac2:(tb__ "0|0|
S2cS15S11S4aS2eA1ZcA2S33A3"). Proof. reflexivity. Qed.
Lemma rd_Hnth : ltac2:(tb__ "0|0|
S2cS24S17A1S62S17S1fS4aS2eA1A1U2A3S23S17S1cS31S14Z0A1S33S22S12A1S1aA5A2A3"). Proof. reflexivity. Qed.
Lemma rd_next : ss_next (ax_S E_ecall) = 100%positive. Proof. reflexivity. Qed.

Section EcallFacts.
Variable rhoE : valuation.
Hypothesis HFE : ltac2:(tb__ "0|0|
S49ScSfVrhoE;A1S13S4aS2eA1A1A3").
Let Z0 := base_rd_Z rhoE HFE.

Lemma rd_Vbuf : ltac2:(tb__ "0|1|
S2cS47S2Q40M0S10VrhoE;S31A2A2S6S2G0SdVrhoE;PfA2A2S2G0SdVrhoE;P11A2A2A2A3").
Proof using Z0.
  pose proof Z0 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8). unfold HSE in Z3.
  pose proof (urange (rw rhoE 15)). pose proof (urange (rw rhoE 17)). pose proof (urange (rw rhoE 16)).
  unfold buf, add, vBb, vOb. apply U_add2; [reflexivity | reflexivity | lia].
Qed.

Lemma rd_Hcnt : ltac2:(tb__ "0|0|
S5S2Q40S10VrhoE;S11S4aS2eA1ZcA2A2A2S5aA2").
Proof using Z0. rewrite rd_H12. pose proof Z0 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8). change (eval rhoE vC) with (rw rhoE 19). unfold MAX_RW_COUNT. lia. Qed.
Lemma rd_Hcnt_pos : ltac2:(tb__ "0|0|
S7Z0S2Q40S10VrhoE;S11S4aS2eA1ZcA2A2A2A2").
Proof using Z0. rewrite rd_H12. pose proof Z0 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8). change (eval rhoE vC) with (rw rhoE 19). lia. Qed.
Lemma rd_Hov : ltac2:(tb__ "0|2|
S5S6S2Q40M0S10VrhoE;S11S4aS2eA1M1ZbA2A2A2S2G0S10VrhoE;S11G1ZcA2A2A2A2S5bA2").
Proof using Z0.
  rewrite rd_H11, rd_H12, rd_Vbuf. pose proof Z0 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8).
  change (eval rhoE vC) with (rw rhoE 19). pose proof (urange (rw rhoE 17)). unfold TASK_SIZE. lia.
Qed.
Lemma rd_Hbuf : ltac2:(tb__ "0|1|
S2cS47S2Q40M0S10VrhoE;S11S4aS2eA1ZbA2A2A2S6S2G0S10VrhoE;S31A2A2Z0A2A3").
Proof. rewrite rd_H11. lia. Qed.
Lemma rd_Hlo : soff rhoE (SLit 0) <= 0.
Proof. rewrite soff_lit_small; lia. Qed.
Lemma rd_Hhi : ltac2:(tb__ "0|0|
S5S6Z0S2Q40S10VrhoE;S11S4aS2eA1ZcA2A2A2A2S1dVrhoE;S33A2A2").
Proof using Z0.
  rewrite rd_H12. pose proof Z0 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8). change (eval rhoE vC) with (rw rhoE 19).
  unfold vC. rewrite soff_var'; lia.
Qed.
Lemma rd_Hcells : Forall (fun c => soff rhoE (c_off c) + c_width c <= 0) ([] : list cell).
Proof. constructor. Qed.
Lemma rd_Hwoff : 0 = soff rhoE (SLit 0).
Proof. rewrite soff_lit_small; lia. Qed.
End EcallFacts.

Section LoopZr.
Variable lv : positive.
Hypothesis Hlv : ltac2:(tb__ "0|0|
S2bS63P64Vlv;A2S64Vlv;P8cA2A2").
Local Abbreviation res := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.res lv).
Local Abbreviation lastb := (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.lastb lv).

Section Vals.
Variable r : valuation.
Let B := bv_unsigned (rw r 15). Let L := bv_unsigned (rw r 16). Let O := bv_unsigned (rw r 17). Let N := bv_unsigned (rw r lv).
Hypothesis HZ : rdZ r.
Hypothesis HN : ltac2:(tb__ "0|0|
S2bS5Z1VN;A2S5S6VO;VN;A2VL;A2A2").

Lemma Vr_buf : ltac2:(tb__ "0|0|
S2cS47S2Q40S10Vr;S31A2A2S6VB;VO;A2A3").
Proof using HZ HN.
  unfold rdZ in HZ. pose proof (urange (rw r 15)). pose proof (urange (rw r 17)). pose proof (urange (rw r 16)).
  unfold buf, add, vBb, vOb. apply U_add2; [reflexivity | reflexivity | subst B L O N; unfold HSE in HZ; lia].
Qed.
Lemma Vr_last : ltac2:(tb__ "0|0|
S2cS47S2Q40S10Vr;S3eVlv;A1A2A2SaS6S6VB;VO;A2VN;A2Z1A2A3").
Proof using HZ HN.
  pose proof Vr_buf as Vo. unfold rdZ in HZ. pose proof (urange (rw r 15)). pose proof (urange (rw r 17)). pose proof (urange (rw r 16)). pose proof (urange (rw r lv)).
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.lastb. unfold add at 1. unfold add at 1.
  replace (B + O + N - 1) with ((B + O + N) + (-1)) by lia.
  apply (U_addc r (SAlu ALU_ADD buf res) (-1) (B + O + N)); [ | subst B L O N; unfold HSE in HZ; lia | lia].
  apply U_add2; [exact Vo | reflexivity | subst B L O N; unfold HSE in HZ; lia].
Qed.
Lemma Vr_BL : ltac2:(tb__ "0|0|
S2cS47S2Q40S10Vr;S66S45S46A2A2A2S6VB;VL;A2A3").
Proof using HZ HN.
  unfold rdZ in HZ. pose proof (urange (rw r 15)). pose proof (urange (rw r 16)).
  unfold add, vBb, vLb. apply U_add2; [reflexivity | reflexivity | subst B L O N; lia].
Qed.

Lemma F_Lr_intro : ltac2:(tb__ "0|3|
S47S47S2cS47S2Q40M0SdVr;P8cA2A2R2A3S2cS47S2G0SdVr;P8dA2A2R2A3S5VB;S8Z8M1R4A2A2S5S6S8G1R5A2G1A2S6VB;VL;A2A2S7R6R5A2S7R6S9Z2Z3dA2A2S5S8G1R7A2SaS6S6VB;VO;A2VN;A2Z1A2M2A2S5G2S6S8G1R8A2Z7A2A2S49ScSfVr;A1S35Vlv;A1A3F_;F_;F_;F_;F_;F_;F_;F_;Fl;Fc;").
Proof using HZ HN.
  intros c l Ec El H1 H2 H3 H4 H5 H6. unfold rdZ in HZ.
  pose proof (urange (rw r 15)). pose proof (urange (rw r 16)). pose proof (urange (rw r 17)).
  assert (Hc : bv_unsigned (rw r 140) < 2 ^ 61) by lia.
  assert (Eg8c : UU r (g8 cur) = 8 * c) by (unfold cur; rewrite (U_g8 r 140 Hc); lia).
  assert (Eg8l : UU r (g8 gl) = 8 * l) by (unfold gl; rewrite (U_g8 r 141 ltac:(lia)); lia).
  unfold F_L, F8of.
  constructor. { cbn [holds]. rewrite Eg8c. change (eval r vBb) with (rw r 15). lia. }
  constructor. { cbn [holds]. unfold add at 1. rewrite (U_addc r (g8 cur) 8 (8 * c) Eg8c) by lia. fold (add vBb vLb). rewrite Vr_BL. lia. }
  constructor. { cbn [holds]. reflexivity. }
  constructor. { cbn [holds]. rewrite (U_lit64 r (2 ^ 61 - 1)) by lia. change (eval r cur) with (rw r 140). lia. }
  constructor. { cbn [holds]. change (eval r cur) with (rw r 140). change (eval r gl) with (rw r 141). lia. }
  constructor. { cbn [holds]. rewrite Eg8l. rewrite Vr_last. lia. }
  constructor. { cbn [holds]. unfold add at 1. rewrite (U_addc r (g8 gl) 7 (8 * l) Eg8l) by lia. rewrite Vr_last. lia. }
  constructor. { cbn [holds]. rewrite (U_lit64 r (2 ^ 61 - 1)) by lia. change (eval r gl) with (rw r 141). lia. }
  constructor.
Qed.
End Vals.

Lemma Fpos_Z : ltac2:(tb__ "0|3|
SeS60R1A1S49ScSfR2A1S2fVlv;A1A3S2bS5Z1S2Q40M0SdR3Vlv;A2A2M1A2S2bS5S6S2G0SdR3P11A2A2G1A2S2G0SdR3P10A2A2M2A2S5G1G2A2A2A2F_;F_;Frho;").
Proof.
  intros rho HZ HF. unfold rdZ in HZ. pose proof (urange (rw rho 17)). pose proof (urange (rw rho lv)). pose proof (urange (rw rho 16)).
  have_fact A1 HF (SPUle (SLit 1) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.res lv)). have_fact A2 HF (SPUle (add vOb (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.res lv)) vLb).
  have_fact A3 HF (SPUle (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.res lv) vLb).
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.res, vOb, vLb, add in A1, A2, A3. rewrite (U_lit64 rho 1) in A1 by lia. cbn [eval] in A1, A3.
  assert (B1 : 0 <= bv_unsigned (rw rho 17) + bv_unsigned (rw rho lv) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar 17) (SVar lv) (bv_unsigned (rw rho 17)) (bv_unsigned (rw rho lv)) eq_refl eq_refl B1) in A2.
  cbn [eval] in A2. lia.
Qed.

Lemma in_facts_Zr : ltac2:(tb__ "0|a|
SeS60R1A1S49ScSfR2A1S2fVlv;A1A3S49ScSfR3A1S25ScS3cS3aP8eM0S31A3S25ScS3cS39P8dM1S3eVlv;A1A3S28ScS1bS19S6bS65S3aA1S65S39A1A3A1S22ScA1A3A3A3A3S2Q40M2SdR4PfA2A2S47S2G2SdR5P11A2A2S47S2G2SdR6Vlv;A2A2S47S2G2SdR7G0A2A2S47S2G2SdR8G1A2A2S47S2bS2bS5S8Z8M3R2A2M4S6R5R4A2M5A2S5G5S6G4Z7M6A2A2A2S2bS7R2S9Z2Z3dA2M7A2S2bS2bS5S8G3R1A2M8SaS6G5R3A2Z1A2M9A2S5G9S6G8G6A2A2A2S2bS7R1G7A2S7R2R1A2A2A2A2A2Tl;Tg;TN;TO;TB;F_;F_;F_;Frho;").
Proof.
  intros rho HZ HP HF. pose proof HZ as HZ'. unfold rdZ in HZ'. destruct (Fpos_Z rho HZ HP) as (P1 & P2 & P3).
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  have_fact A1 HF (SPUle (g8 gs) buf). have_fact A2 HF (SPUle buf (add (g8 gs) (SLit 7))). have_fact A3 HF (SPUle gs (SLit (2 ^ 61 - 1))).
  have_fact A4 HF (SPUle (g8 gl) lastb). have_fact A5 HF (SPUle lastb (add (g8 gl) (SLit 7))). have_fact A6 HF (SPUle gl (SLit (2 ^ 61 - 1))).
  have_fact A7 HF (SPNot (SPBranch BC_GEU (shp gs) (shp gl))).
  rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia. rewrite (U_lit64 rho (2 ^ 61 - 1)) in A6 by lia.
  change (eval rho gs) with (rw rho 142) in A3. change (eval rho gl) with (rw rho 141) in A6.
  assert (Hg : bv_unsigned (rw rho 142) < 2 ^ 61) by lia. assert (Hl : bv_unsigned (rw rho 141) < 2 ^ 61) by lia.
  pose proof (U_g8 rho 142 Hg) as Eg. pose proof (U_g8 rho 141 Hl) as El. unfold gs in A1, A2, A7. unfold gl in A4, A5, A7.
  rewrite Eg in A1. rewrite El in A4.
  pose proof (Vr_buf rho HZ (conj P1 P2)) as Vo. pose proof (Vr_last rho HZ (conj P1 P2)) as Vl.
  rewrite Vo in A1. rewrite Vo in A2. rewrite Vl in A4. rewrite Vl in A5.
  unfold add in A2, A5.
  pose proof (U_addc rho (g8 (SVar 142)) 7 _ Eg ltac:(lia) ltac:(lia)) as T1. rewrite T1 in A2.
  pose proof (U_addc rho (g8 (SVar 141)) 7 _ El ltac:(lia) ltac:(lia)) as T2. rewrite T2 in A5.
  cbn [holds branch_taken] in A7. unfold bv_ltu in A7.
  pose proof (U_shp rho 142 ltac:(lia)) as S1. pose proof (U_shp rho 141 ltac:(lia)) as S2.
  assert (Hgl : bv_unsigned (rw rho 142) < bv_unsigned (rw rho 141)).
  { destruct (Z.ltb_spec (UU rho (shp (SVar 142))) (UU rho (shp (SVar 141)))) as [Hlt|Hge];
      [rewrite S1, S2 in Hlt; lia | exfalso; apply A7; reflexivity]. }
  cbv zeta. repeat split; lia.
Qed.

Lemma bk_facts_Zr : ltac2:(tb__ "0|5|
SeS60R1A1S49ScSfR2A1S2fVlv;A1A3S49ScSfR3A1S25ScS35Vlv;A1S28ScS19S6cS67S37Z1M0A2S65S39A1A3S22ScA1A3A3A3S2Q40M1SdR4PfA2A2S47S2G1SdR5P10A2A2S47S2G1SdR6P11A2A2S47S2G1SdR7Vlv;A2A2S47S2G1SdR8P8cA2A2S47S2G1SdR9P8dA2A2S47S2bS5R6S8Z8M2R2A2A2S2bS7R2R1A2S2bS7R1S9Z2Z3dA2A2S2bS2bS5S8G2R1A2M3SaS6S6R6R4A2R3A2G0A2M4A2S5G4S6G3Z7A2A2A2S2dS2cS47S6R2G0A2R1A3A1A2A2A2A2Tl;Tc;TN;TO;TL;TB;F_;F_;F_;Frho;").
Proof.
  intros rho HZ HP HF. pose proof HZ as HZ'. unfold rdZ in HZ'. destruct (Fpos_Z rho HZ HP) as (P1 & P2 & P3).
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  apply Forall_app in HF as [HL HB].
  have_fact A1 HL (SPUle vBb (g8 cur)). have_fact A3 HL (SPUle cur (SLit (2 ^ 61 - 1))). have_fact A4 HL (SPUlt cur gl).
  have_fact A5 HL (SPUle (g8 gl) lastb). have_fact A6 HL (SPUle lastb (add (g8 gl) (SLit 7))). have_fact A7 HL (SPUle gl (SLit (2 ^ 61 - 1))).
  have_fact A8 HB (SPBranch BC_NE (shpk cur 1) (shp gl)).
  rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia. rewrite (U_lit64 rho (2 ^ 61 - 1)) in A7 by lia.
  change (eval rho cur) with (rw rho 140) in A3, A4. change (eval rho gl) with (rw rho 141) in A4, A7.
  change (eval rho vBb) with (rw rho 15) in A1.
  assert (Hc : bv_unsigned (rw rho 140) < 2 ^ 61) by lia. assert (Hl : bv_unsigned (rw rho 141) < 2 ^ 61) by lia.
  pose proof (U_g8 rho 140 Hc) as Ec. pose proof (U_g8 rho 141 Hl) as El. unfold cur in A1, A8. unfold gl in A5, A6, A8.
  rewrite Ec in A1. rewrite El in A5. pose proof (Vr_last rho HZ (conj P1 P2)) as Vl. rewrite Vl in A5. rewrite Vl in A6.
  unfold add in A6. pose proof (U_addc rho (g8 (SVar 141)) 7 _ El ltac:(lia) ltac:(lia)) as T2. rewrite T2 in A6.
  cbn [holds branch_taken] in A8. unfold bv_eqb in A8. apply negb_true_iff in A8. apply Z.eqb_neq in A8.
  pose proof (U_shp rho 141 ltac:(lia)) as S2. rewrite S2 in A8.
  unfold shpk, add in A8.
  rewrite (U_addc rho (SVar 140) (SHB + 1) (bv_unsigned (rw rho 140)) eq_refl) in A8 by (unfold SHB; lia).
  cbv zeta. repeat split; try lia.
Qed.
End LoopZr.

Lemma agree_sub_nil : ltac2:(tb__ "0|0|
S48SeS16R2R1S5fR1S22S29S48S15A2A1A2A3Frho;Fn;").
Proof. intros n rho. split; [intros i _; reflexivity|]. split; intros; reflexivity. Qed.

Lemma Forall_holds_agree : ltac2:(tb__ "0|1|
S48SeSeS21ScA1S16R4R3R2A3S2cS26S61ScS18R5A1R2A3S27A3S49ScSfR5A1M0R3A3S49ScG0R4A3F_;F_;F_;FF;Frho';Frho;Fn;").
Proof.
  intros n rho rho' F Hag Hb HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree n rho rho' p Hag (proj1 (forallb_forall _ _) Hb p Hp))). exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Lemma FR_Z : ltac2:(tb__ "0|1|
S48SeS49ScSfR1A1S34R2A1A3S2bS60R2A1S5S2Q40M0SdR2R3A2A2S2G0SdR2P13A2A2A2A2F_;Frho;Flv;").
Proof.
  intros lv rho HF. unfold FR in HF. apply Forall_app in HF as [H1 H2]. split; [exact (base_rd_Z rho H2)|].
  have_fact A H1 (SPUle (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.res lv) vC). exact A.
Qed.

Ltac split_mid3 HF HX HT := cbn [ax_S ss_facts mid_state mkA] in HF; apply Forall_app in HF as [HX HT].

Section GlueR.
Variables (bc : list cell) (lv : positive).
Hypothesis Hlv : ltac2:(tb__ "0|0|
S2bS63P64Vlv;A2S64Vlv;P8cA2A2").
Variable rho : valuation.

Lemma Fpos_below200 : ltac2:(tb__ "0|0|
S2cS26S61ScS18Pc8A1S2fVlv;A1A3S27A3").
Proof using Hlv.
  unfold Fpos, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.res, vOb, vLb, add. cbn. destruct Hlv as [H1 H2].
  rewrite !(proj2 (Pos.ltb_lt lv 200)) by lia. reflexivity.
Qed.

Lemma glue_pos : ltac2:(tb__ "0|0|
S49ScSfVrho;A1S13S4aS43Vbc;Vlv;A2A1A1A3S49ScSfS5fVrho;S22S29S48S15A2A1A2A1S2fVlv;A1A3F_;").
Proof using Hlv.
  intros HF. unfold E_pos in HF. split_mid3 HF HX HT. destruct (FR_Z lv rho HT) as [HZ Hle]. pose proof HZ as HZ'. unfold rdZ in HZ'.
  pose proof (urange (rw rho lv)) as Rl. pose proof (urange (rw rho 17)) as R17.
  have_fact A1 HX (SPNot (SPBranch BC_GE (SLit 0) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.res lv))).
  cbn [holds branch_taken] in A1. unfold bv_lts in A1.
  assert (Hpos : 1 <= bv_unsigned (rw rho lv)).
  { destruct (Z.ltb_spec (bv_signed (eval rho (SLit 0))) (bv_signed (eval rho (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.res lv)))) as [Hlt|Hge]; [| exfalso; apply A1; reflexivity].
    rewrite !bv_signed_U in Hlt. change (eval rho (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.res lv)) with (rw rho lv) in Hlt.
    rewrite (U_lit64 rho 0) in Hlt by lia.
    destruct (Zsigned_spec 0) as [[_ E0]|[X0 _]]; [rewrite E0 in Hlt | lia].
    destruct (Zsigned_spec (bv_unsigned (rw rho lv))) as [[_ E]|[X _]]; [rewrite E in Hlt; lia | lia]. }
  apply (Forall_holds_agree 200 rho); [apply agree_sub_nil | exact Fpos_below200 |].
  unfold Fpos. constructor.
  { cbn [holds]. rewrite (U_lit64 rho 1) by lia. change (eval rho (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.res lv)) with (rw rho lv). lia. }
  constructor.
  { cbn [holds]. unfold add, vOb, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.res, vLb.
    rewrite (U_add2 rho (SVar 17) (SVar lv) (bv_unsigned (rw rho 17)) (bv_unsigned (rw rho lv)) eq_refl eq_refl) by lia.
    cbn [eval]. lia. }
  constructor. { cbn [holds]. change (eval rho (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.res lv)) with (rw rho lv). change (eval rho vLb) with (rw rho 16). lia. }
  constructor.
Qed.

Lemma glue_L_in : ltac2:(tb__ "0|0|
S49ScSfVrho;A1S13S4aS42Vbc;Vlv;A2A1A1A3S49ScSfS5fVrho;S40A2A1S35Vlv;A1A3F_;").
Proof using Hlv.
  intros HF. unfold E_L_in in HF. split_mid3 HF HX HT. destruct (FR_Z lv rho HT) as [HZ Hle].
  apply Forall_app in HX as [HA HX]. apply Forall_app in HX as [HB HX]. apply Forall_app in HX as [HC HP].
  assert (HX1 : Forall (holds rho) (F8of gs 142 buf ++ F8of gl 141 (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_read.lastb lv) ++ [SPNot (SPBranch BC_GEU (shp gs) (shp gl))])).
  { apply Forall_app. split; [exact HA|]. apply Forall_app. split; [exact HB | exact HC]. }
  destruct (Fpos_Z lv Hlv rho HZ HP) as (P1 & P2 & P3).
  destruct (in_facts_Zr lv Hlv rho HZ HP HX1) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  pose proof HZ as HZ'. unfold rdZ in HZ'. unfold HSE in *.
  pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141. pose proof (urange (rw rho 17)) as R17.
  set (rho' := rho_sub rho s_L_in).
  assert (E15 : rw rho' 15 = rw rho 15) by reflexivity. assert (E16 : rw rho' 16 = rw rho 16) by reflexivity.
  assert (E17 : rw rho' 17 = rw rho 17) by reflexivity. assert (E19 : rw rho' 19 = rw rho 19) by reflexivity.
  assert (E10 : rw rho' 10 = rw rho 10) by reflexivity. assert (E24 : rw rho' 24 = rw rho 24) by reflexivity.
  assert (Elv : rw rho' lv = rw rho lv).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_L_in]. destruct Hlv as [H1 H2].
    replace (Pos.eqb lv 140) with false by (symmetry; apply Pos.eqb_neq; lia). reflexivity. }
  assert (HZr : rdZ rho') by (unfold rdZ; rewrite E15, E16, E17, E19, E10, E24; exact HZ').
  pose proof (Z.div_mod (bv_unsigned (rw rho 15)) 8 ltac:(lia)) as D.
  apply (F_Lr_intro lv rho' HZr ltac:(rewrite Elv, E17, E16; lia) (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 141)));
    try reflexivity; rewrite ?E15, ?E16, ?E17, ?Elv; lia.
Qed.

Lemma glue_L_bk : ltac2:(tb__ "0|0|
S49ScSfVrho;A1S13S4aS41Vbc;Vlv;A2A1A1A3S49ScSfS5fVrho;S3fA2A1S35Vlv;A1A3F_;").
Proof using Hlv.
  intros HF. unfold E_L_bk in HF. split_mid3 HF HX HT. destruct (FR_Z lv rho HT) as [HZ Hle].
  apply Forall_app in HX as [HA HX]. apply Forall_app in HX as [HB HP].
  assert (HX1 : Forall (holds rho) (F_L lv ++ [SPBranch BC_NE (shpk cur 1) (shp gl)])).
  { apply Forall_app. split; [exact HA | exact HB]. }
  destruct (Fpos_Z lv Hlv rho HZ HP) as (P1 & P2 & P3).
  destruct (bk_facts_Zr lv Hlv rho HZ HP HX1) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  pose proof HZ as HZ'. unfold rdZ in HZ'. unfold HSE in *.
  pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141. pose proof (urange (rw rho 17)) as R17.
  set (rho' := rho_sub rho s_L_bk).
  assert (E15 : rw rho' 15 = rw rho 15) by reflexivity. assert (E16 : rw rho' 16 = rw rho 16) by reflexivity.
  assert (E17 : rw rho' 17 = rw rho 17) by reflexivity. assert (E19 : rw rho' 19 = rw rho 19) by reflexivity.
  assert (E10 : rw rho' 10 = rw rho 10) by reflexivity. assert (E24 : rw rho' 24 = rw rho 24) by reflexivity.
  assert (E141 : rw rho' 141 = rw rho 141) by reflexivity.
  assert (Elv : rw rho' lv = rw rho lv).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_L_bk]. destruct Hlv as [H1 H2].
    replace (Pos.eqb lv 140) with false by (symmetry; apply Pos.eqb_neq; lia). reflexivity. }
  assert (HZr : rdZ rho') by (unfold rdZ; rewrite E15, E16, E17, E19, E10, E24; exact HZ').
  assert (E140 : bv_unsigned (rw rho' 140) = bv_unsigned (rw rho 140) + 1).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_L_bk Pos.eqb]. unfold add, cur.
    apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  apply (F_Lr_intro lv rho' HZr ltac:(rewrite Elv, E17, E16; lia) (bv_unsigned (rw rho 140) + 1) (bv_unsigned (rw rho 141)));
    rewrite ?E15, ?E16, ?E17, ?Elv, ?E141; try lia.
Qed.

Lemma meas_L_in : ltac2:(tb__ "0|0|
S2cS3Q40A1S10S5fVrho;S40A2S37A2S10Vrho;S3aA2A3").
Proof. reflexivity. Qed.
Lemma meas_L_bk : ltac2:(tb__ "0|0|
S2cS3Q40A1S10S5fVrho;S3fA2S37A2S10Vrho;S66S37S14Z1A1A2A2A3").
Proof. reflexivity. Qed.
End GlueR.

Lemma FposFR_of_Ereg : ltac2:(tb__ "0|0|
S21S12A1S48SeS49ScSfR1A1S13S4aS3bR3R2A2A1A1A3S49ScSfR2A1S25ScS2fR3A1S34R3A1A3A3F_;Fr;Flv;Fbc;").
Proof. intros bc lv r HF. cbn [ax_S ss_facts E_reg mid_state mkA] in HF. exact HF. Qed.
Lemma FposFR_below190 : ltac2:(tb__ "0|3|
S2bS2cS26S61ScS18PbeA1M0S25ScS2fP64M1A1S34G1A1A3A3S27A3S2cS26S61ScG0S25ScS2fP65M2A1S34G2A1A3A3S27A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma next_Ereg : ltac2:(tb__ "0|1|
S21S12A1S48S2bS63P65S1eS4aS3bR2R1A2A1A1M0A2S63P66G0A2A2Flv;Fbc;").
Proof. intros. cbn. split; cbv; congruence. Qed.
Lemma Hlv100 : (100 <= 100)%positive /\ (100 < 140)%positive. Proof. split; cbv; congruence. Qed.
Lemma Hlv101 : (100 <= 101)%positive /\ (101 < 140)%positive. Proof. split; cbv; congruence. Qed.

Lemma LQA_unG' : ltac2:(tb__ "0|0|
S4fS48S48SeSeS21S3Q40A1A1S21S4bA1S5eS4cS0S77SeS16R8R6R1A3Lr;R8A2R6R4R3R2R1A7S4cS0R9R8R6R4R3R2A7F_;Fw;Fposts;Ftp;Frho1;Frho;Fm;Fn;FJ;").
Proof. intros J n m rho rho1 tp posts w (L & rho'' & Hin & _ & Hsm & [Hag Hk]). exists L, rho''. auto. Qed.

Section Seg3Keep.
Variable ok : assn.
Variable J1x : jpredA.
Hypothesis Hok1 : ltac2:(tb__ "0|0|
S4eS0Vok;VJ1x;A3").
Hypothesis Hst1 : stableA segs 101 J1x.

Lemma seg3_keep : ltac2:(tb__ "0|2|
SeS21S3Q40M0A1A1S5S2G0SdR2P64M1A2A2S2G0SdR2P13A2A2A2S5dS0Vok;S4dS0VJ1x;S6eS2eA1R3R2A5S4cS0VJ1x;P65R3R2S30S22S12A1G1A2A6A4F_;Ftp;Frho1;").
Proof.
  intros rho1 tp Hlen.
  set (J3 := withGA (fun r => agree_below 101 rho1 r) J1x).
  assert (HstG : stableA segs 101 J3).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst1]. }
  assert (HokG : ok_frameA segs ok J3) by (intros r t tr ms md msv' [_ HJ]; eapply Hok1; eauto).
  destruct ids_rd as (_ & _ & _ & I1 & I2 & I3).
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w Hw. apply (SPA_withG_intro segs J1x 101 T_rd_k rho1 tp w).
    destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    constructor; [|constructor]. cbn [holds]. exact Hlen. }
  apply (cfg_soundA segs FUELR cutpcs_rd 101 cuts_k exits_k J3 ok (LQA segs J1x 101 rho1 tp (Posts_rd [] 100)) tp HokG HstG check_k);
    [| left; reflexivity].
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply exit_postA. in_nth 0.
  - apply (exit_reenterA segs ok _ 101 cuts_k _ (E_pos [] 100) (T_pos_0 [] 100) (Fpos 100) [] tp);
      [in_nth 1 | exact ent_pos_k | exact I1 | exact HstG | exact (proj1 Fpos_below) | intros r tp' tr md _ HF; exact (glue_pos [] 100 Hlv100 r HF)].
  - apply (call_exitA ok J1x 101 rho1 tp (E_reg [] 100) Pre_rip_lo s_reg_k R_reg_k Posts_rip (Fpos 100 ++ FR 100) Hst1 fr_reg_k cc_reg_k
             (proj1 (next_Ereg [] 100)) (FposFR_of_Ereg [] 100) (proj1 FposFR_below190)
             (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj1 FT_below_Tr)) | or_intror F => match F with end end)
             cuts_k _ Hok1).
    + intros ok' Jq rho2 tp2 Ho Hs. exact (region_sum_lo ok' Jq rho2 tp2 Ho Hs).
    + intros L [<-|[]]. in_nth 2.
  - apply (exit_reenterA segs ok _ 101 cuts_k _ (E_L_in [] 100) (CL_0 [] 100) (F_L 100) s_L_in tp);
      [in_nth 3 | exact ent_L_in_k | exact I2 | exact HstG | exact (proj1 FL_below) | intros r tp' tr md _ HF; exact (glue_L_in [] 100 Hlv100 r HF)].
  - apply (exit_reenterA segs ok _ 101 cuts_k _ (E_L_bk [] 100) (CL_0 [] 100) (F_L 100) s_L_bk tp);
      [in_nth 3 | exact ent_L_bk_k | exact I3 | exact HstG | exact (proj1 FL_below) | intros r tp' tr md _ HF; exact (glue_L_bk [] 100 Hlv100 r HF)].
Qed.
End Seg3Keep.

Section Seg3KeepEx.
Variable J1x : jpredA.
Hypothesis Hst1 : stableA segs 101 J1x.

Ltac meas_lit := intros r r'; unfold vmeasIA; cbn [vna_var vna_rank eval]; rewrite ?u64_lit by lia; lia.

Lemma seg3_keep_ex : ltac2:(tb__ "0|2|
SeS21S3Q40M0A1A1S5S2G0SdR2P64M1A2A2S2G0SdR2P13A2A2A2S5cS0S4dS0VJ1x;S6eS2eA1R3R2A5S4cS0VJ1x;P65R3R2S30S22S12A1G1A2A6A3F_;Ftp;Frho1;").
Proof.
  intros rho1 tp Hlen.
  set (J3 := withGA (fun r => agree_below 101 rho1 r) J1x).
  assert (HstG : stableA segs 101 J3).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst1]. }
  destruct ids_rd as (_ & _ & _ & I1 & I2 & I3).
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w Hw. apply (SPA_withG_intro segs J1x 101 T_rd_k rho1 tp w).
    destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    constructor; [|constructor]. cbn [holds]. exact Hlen. }
  change T_rd_k with (vna_state (mkVNA T_rd_k 200 (SLit 0))).
  apply (cfg_complete_autoIA segs FUELR cutpcs_rd 101 vcuts_k vexits_k J3 (LQA segs J1x 101 rho1 tp (Posts_rd [] 100)) tp HstG);
    [ | exact echeck_k | | left; reflexivity].
  { intros m Hm. unfold vcuts_k, vcuts_rd in Hm. repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm. }
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply (eexit_post_IA0 segs J1x 101 rho1 vcuts_k (Posts_rd [] 100) (mkVNA (P_rd [] 100) 0 (SLit (2 ^ 64 - 1)))). in_nth 0.
  - apply (eexit_reenter_IA segs _ 101 vcuts_k _ (mkVNA (E_pos [] 100) 150 (SLit 0)) (mkVNA (T_pos [] 100) 149 (SLit 0)) (Fpos 100) (T_pos_0 [] 100) [] tp);
      [in_nth 1 | reflexivity | exact ent_pos_k | exact I1 | exact HstG | exact (proj1 Fpos_below)
      | intros r tp' tr md _ HF; split; [exact (glue_pos [] 100 Hlv100 r HF) | right; split; [cbn; lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (call_exitA_ex J1x 101 rho1 tp (E_reg [] 100) Pre_rip_lo s_reg_k R_reg_k Posts_rip (Fpos 100 ++ FR 100) Hst1 fr_reg_k cc_reg_k
             (proj1 (next_Ereg [] 100)) (FposFR_of_Ereg [] 100) (proj1 FposFR_below190)
             (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj1 FT_below_Tr)) | or_intror F => match F with end end)
             vcuts_k _ (mkVNA (E_reg [] 100) 80 (SLit (2 ^ 61))) eq_refl).
    + intros Jq rho2 tp2 Hs. exact (region_sum_lo_ex Jq rho2 tp2 Hs).
    + intros L [<-|[]]. exists (mkVNA (Tr1 [] 100 s_reg_k R_reg_k) 79 (SLit (2 ^ 61))). split; [in_nth 2|]. split; [reflexivity|]. meas_lit.
  - apply (eexit_reenter_IA segs _ 101 vcuts_k _ (mkVNA (E_L_in [] 100) 101 gs) (mkVNA (CL [] 100) 100 cur) (F_L 100) (CL_0 [] 100) s_L_in tp);
      [in_nth 3 | reflexivity | exact ent_L_in_k | exact I2 | exact HstG | exact (proj1 FL_below)
      | intros r tp' tr md _ HF; split; [exact (glue_L_in [] 100 Hlv100 r HF) | right; split; [cbn [vna_var]; rewrite (meas_L_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ 101 vcuts_k _ (mkVNA (E_L_bk [] 100) 101 (add cur (SLit 1))) (mkVNA (CL [] 100) 100 cur) (F_L 100) (CL_0 [] 100) s_L_bk tp);
      [in_nth 3 | reflexivity | exact ent_L_bk_k | exact I3 | exact HstG | exact (proj1 FL_below)
      | intros r tp' tr md _ HF; split; [exact (glue_L_bk [] 100 Hlv100 r HF) | right; split; [cbn [vna_var]; rewrite (meas_L_bk r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
Qed.
End Seg3KeepEx.

Section ReadKeep.
Variables (J0 J1 : jpredA) (p : list byte) (data : list byte) (offZ : valuation -> Z).
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hst1 : stableA segs 101 J1.
Hypothesis Hoff : ltac2:(tb__ "0|1|
SeS2bS5Z0VoffZ;R1A1M0A2S7G0S9Z2Z40A2A2A2Fr;").
Hypothesis HJfd : ltac2:(tb__ "0|2|
SeS21S3Q40M0A1A1S21S53A1S52VJ0;R4R3R2R1A4S2bS2cS24S54A1S55S56R2A1S4G0Z3A2A2S23S54S57Vp;S4G0VoffZ;R5A1A2A2A2A3S2cS24S21S3Q8A1A1M1A1S69S58R2A1Vp;A2S23G1Vdata;A2A3A2F_;Fmd;Ftr;Ft;Fr;").

Hypothesis HK : ltac2:(tb__ "0|1|
SeS21S3Q40A1A1S21S53A1S52VJ0;R4R3R2R1A4VJ1;S72S2eR5Vdata;VoffZ;R5A1M0A4R4R3S70S2eR5Vp;Vdata;G0R2A6A4F_;Fmd;Ftr;Ft;Fr;").

Lemma len_le : ltac2:(tb__ "0|2|
SeS49ScSfR1A1S13S4aS2eA1A1A3S5S2Q40M0SdS72S2eR2Vdata;VoffZ;R2A1A4M1P64A2A2S2G0SdG1P13A2A2A2F_;Fr;").
Proof.
  intros r HF. unfold rkA_rho'. rewrite rd_next. rewrite rho_set_rw_at, rho_set_rw_other by (cbv; congruence).
  pose proof (rbA_bs_len E_ecall r data (offZ r) (Hoff r)) as Hl. rewrite rd_H12 in Hl.
  change (eval r vC) with (rw r 19) in Hl. pose proof (urange (rw r 19)).
  rewrite len_word_unsigned by (unfold two_pow_64; lia). exact Hl.
Qed.

Theorem read_keep_sum : ltac2:(tb__ "0|0|
S5eOF_;SeS21S3Q40A1A1S4eS0R3VJ0;A3S68S0R4VJ0;A3S4eS0R5VJ1;A3S5dS0R6S4dS0VJ0;S32R5R4A5S4cS0VJ1;S51R5R4S30S22S12A1P64A2A6A4F_;F_;F_;Ftp;Frho;Fok;").
Proof.
  intros ok rho tp Hok0 Hokp0 Hok1.
  set (J0' := withGA (fun r => agree_below NF rho r) J0).
  set (J1' := withGA (fun r => agree_below NF rho r) J1).
  assert (HstG0 : stableA segs NF J0').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst0]. }
  assert (HstG1 : stableA segs 101 J1').
  { apply stableA_withG; [| exact Hst1]. intros r1 r2 H1 H2. eapply agree_below_trans; [exact H1|]. eapply agree_below_le; [|exact H2]. cbv; congruence. }
  assert (HokG0 : ok_frameA segs ok J0') by (intros r t tr ms md msv' [_ HJ]; eapply Hok0; eauto).
  assert (HokpG0 : ok_pframeA segs ok J0') by (intros r t tr ms md x8 [_ HJ]; eapply Hokp0; eauto).
  assert (HokG1 : ok_frameA segs ok J1') by (intros r t tr ms md msv' [_ HJ]; eapply Hok1; eauto).
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J0 NF Pre_rd rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELR [rd_ecall] NF [Pre_rd] [E_ecall] J0' ok (LQA segs J1 NF rho tp (Posts_rd [] 100)) tp HokG0 HstG0 check_rd1);
    [| left; reflexivity].
  intros E rhoE [<-|[]].
  apply triple_factsA. intros HFE.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  eapply triple_seq with (R := SPA segs J1' (A_after_fresh E_ecall) (rkA_rho' E_ecall rhoE data (offZ rhoE)) tp).
  - apply triple1_triple.
    apply (triple1_read_keepA segs E_ecall rhoE tp 2 buf (SLit 0) vC [] p data (offZ rhoE) 0 rd_Hi rd_H17 rd_H10 (Hoff rhoE)
             (rd_Hcnt rhoE HFE) (rd_Hov rhoE HFE) rd_Hnth (rd_Hbuf rhoE) (rd_Hlo rhoE) (rd_Hhi rhoE HFE) (rd_Hcells rhoE)
             ok J0' J1' HokG0 HokpG0 HstG0 HstG1).
    + intros tr md [_ HJ]. exact (HJfd rhoE tp tr md HJ).
    + intros tr md [Hag HJ]. split; [| exact (HK rhoE tp tr md HJ)].
      eapply agree_below_trans; [exact Hag|]. unfold rkA_rho'. apply agree_below_set_rw. rewrite rd_next. apply Pos.le_refl.
  - eapply triple_conseq; [intros w Hw; exact Hw | | apply (seg3_keep ok J1' HokG1 HstG1); exact (len_le rhoE HFE)].
    intros w Hw. exact (LQA_unG' J1 NF 101 rho _ tp _ w Hw).
Qed.

Theorem read_keep_sum_ex : ltac2:(tb__ "0|0|
SeS21S3Q40A1A1S5cS0S4dS0VJ0;S32R2R1A5S4cS0VJ1;S51R2R1S30S22S12A1P64A2A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  set (J0' := withGA (fun r => agree_below NF rho r) J0).
  set (J1' := withGA (fun r => agree_below NF rho r) J1).
  assert (HstG0 : stableA segs NF J0').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst0]. }
  assert (HstG1 : stableA segs 101 J1').
  { apply stableA_withG; [| exact Hst1]. intros r1 r2 H1 H2. eapply agree_below_trans; [exact H1|]. eapply agree_below_le; [|exact H2]. cbv; congruence. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J0 NF Pre_rd rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_rd with (vna_state (mkVNA Pre_rd 1 (SLit 0))).
  apply (cfg_complete_autoA segs FUELR [rd_ecall] NF [mkVNA Pre_rd 1 (SLit 0)] [mkVNA E_ecall 0 (SLit 0)] J0'
           (LQA segs J1 NF rho tp (Posts_rd [] 100)) tp HstG0);
    [intros n [<-|[]]; cbv; congruence | exact echeck_rd1 | | left; reflexivity].
  intros E rhoE [<-|[]]. cbn [vna_state].
  apply etriple_factsA. intros HFE.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  eapply etriple_seq with (R := SPA segs J1' (A_after_fresh E_ecall) (rkA_rho' E_ecall rhoE data (offZ rhoE)) tp).
  - apply (etriple_read_keepA segs E_ecall rhoE tp 2 buf (SLit 0) vC [] p data (offZ rhoE) 0 rd_Hi rd_H17 rd_H10 (Hoff rhoE)
             (rd_Hcnt rhoE HFE) (rd_Hov rhoE HFE) rd_Hnth (rd_Hbuf rhoE) (rd_Hlo rhoE) (rd_Hhi rhoE HFE) (rd_Hcells rhoE)
             J0' J1' HstG0 HstG1).
    + intros tr md [_ HJ]. exact (HJfd rhoE tp tr md HJ).
    + intros tr md [Hag HJ]. split; [| exact (HK rhoE tp tr md HJ)].
      eapply agree_below_trans; [exact Hag|]. unfold rkA_rho'. apply agree_below_set_rw. rewrite rd_next. apply Pos.le_refl.
  - eapply etriple_conseq; [intros w Hw; exact Hw | | apply (seg3_keep_ex J1' HstG1); exact (len_le rhoE HFE)].
    intros w Hw. exact (LQA_unG' J1 NF 101 rho _ tp _ w Hw).
Qed.
End ReadKeep.

Section Seg3Hdr.
Variable ok : assn.
Variable J1x : jpredA.
Hypothesis Hok1 : ltac2:(tb__ "0|0|
S4eS0Vok;VJ1x;A3").
Hypothesis Hst1 : stableA segs 102 J1x.

Lemma seg3_hdr : ltac2:(tb__ "0|2|
SeS21S3Q40M0A1A1S5S2G0SdR2P65M1A2A2S2G0SdR2P13A2A2A2S5dS0Vok;S4dS0VJ1x;S6fS2eU2S31S14Z0A1S33A5R3R2A5S4cS0VJ1x;P66R3R2S30S38G1A2A6A4F_;Ftp;Frho1;").
Proof.
  intros rho1 tp Hlen.
  set (J3 := withGA (fun r => agree_below 102 rho1 r) J1x).
  assert (HstG : stableA segs 102 J3).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst1]. }
  assert (HokG : ok_frameA segs ok J3) by (intros r t tr ms md msv' [_ HJ]; eapply Hok1; eauto).
  destruct ids_rd as (I1 & I2 & I3 & _).
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w Hw. apply (SPA_withG_intro segs J1x 102 T_rd_h rho1 tp w).
    destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    constructor; [|constructor]. cbn [holds]. exact Hlen. }
  apply (cfg_soundA segs FUELR cutpcs_rd 102 cuts_h exits_h J3 ok (LQA segs J1x 102 rho1 tp (Posts_rd hc 101)) tp HokG HstG check_h);
    [| left; reflexivity].
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply exit_postA. in_nth 0.
  - apply (exit_reenterA segs ok _ 102 cuts_h _ (E_pos hc 101) (T_pos_0 hc 101) (Fpos 101) [] tp);
      [in_nth 1 | exact ent_pos_h | exact I1 | exact HstG | exact (proj2 Fpos_below) | intros r tp' tr md _ HF; exact (glue_pos hc 101 Hlv101 r HF)].
  - apply (call_exitA ok J1x 102 rho1 tp (E_reg hc 101) Pre_rip_lo s_reg_h R_reg_h Posts_rip (Fpos 101 ++ FR 101) Hst1 fr_reg_h cc_reg_h
             (proj2 (next_Ereg hc 101)) (FposFR_of_Ereg hc 101) (proj2 FposFR_below190)
             (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj2 FT_below_Tr)) | or_intror F => match F with end end)
             cuts_h _ Hok1).
    + intros ok' Jq rho2 tp2 Ho Hs. exact (region_sum_lo ok' Jq rho2 tp2 Ho Hs).
    + intros L [<-|[]]. in_nth 2.
  - apply (exit_reenterA segs ok _ 102 cuts_h _ (E_L_in hc 101) (CL_0 hc 101) (F_L 101) s_L_in tp);
      [in_nth 3 | exact ent_L_in_h | exact I2 | exact HstG | exact (proj2 FL_below) | intros r tp' tr md _ HF; exact (glue_L_in hc 101 Hlv101 r HF)].
  - apply (exit_reenterA segs ok _ 102 cuts_h _ (E_L_bk hc 101) (CL_0 hc 101) (F_L 101) s_L_bk tp);
      [in_nth 3 | exact ent_L_bk_h | exact I3 | exact HstG | exact (proj2 FL_below) | intros r tp' tr md _ HF; exact (glue_L_bk hc 101 Hlv101 r HF)].
Qed.
End Seg3Hdr.

Section Seg3HdrEx.
Variable J1x : jpredA.
Hypothesis Hst1 : stableA segs 102 J1x.

Ltac meas_lit := intros r r'; unfold vmeasIA; cbn [vna_var vna_rank eval]; rewrite ?u64_lit by lia; lia.

Lemma seg3_hdr_ex : ltac2:(tb__ "0|2|
SeS21S3Q40M0A1A1S5S2G0SdR2P65M1A2A2S2G0SdR2P13A2A2A2S5cS0S4dS0VJ1x;S6fS2eU2S31S14Z0A1S33A5R3R2A5S4cS0VJ1x;P66R3R2S30S38G1A2A6A3F_;Ftp;Frho1;").
Proof.
  intros rho1 tp Hlen.
  set (J3 := withGA (fun r => agree_below 102 rho1 r) J1x).
  assert (HstG : stableA segs 102 J3).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst1]. }
  destruct ids_rd as (I1 & I2 & I3 & _).
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  { intros w Hw. apply (SPA_withG_intro segs J1x 102 T_rd_h rho1 tp w).
    destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    constructor; [|constructor]. cbn [holds]. exact Hlen. }
  change T_rd_h with (vna_state (mkVNA T_rd_h 200 (SLit 0))).
  apply (cfg_complete_autoIA segs FUELR cutpcs_rd 102 vcuts_h vexits_h J3 (LQA segs J1x 102 rho1 tp (Posts_rd hc 101)) tp HstG);
    [ | exact echeck_h | | left; reflexivity].
  { intros m Hm. unfold vcuts_h, vcuts_rd in Hm. repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm. }
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply (eexit_post_IA0 segs J1x 102 rho1 vcuts_h (Posts_rd hc 101) (mkVNA (P_rd hc 101) 0 (SLit (2 ^ 64 - 1)))). in_nth 0.
  - apply (eexit_reenter_IA segs _ 102 vcuts_h _ (mkVNA (E_pos hc 101) 150 (SLit 0)) (mkVNA (T_pos hc 101) 149 (SLit 0)) (Fpos 101) (T_pos_0 hc 101) [] tp);
      [in_nth 1 | reflexivity | exact ent_pos_h | exact I1 | exact HstG | exact (proj2 Fpos_below)
      | intros r tp' tr md _ HF; split; [exact (glue_pos hc 101 Hlv101 r HF) | right; split; [cbn; lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (call_exitA_ex J1x 102 rho1 tp (E_reg hc 101) Pre_rip_lo s_reg_h R_reg_h Posts_rip (Fpos 101 ++ FR 101) Hst1 fr_reg_h cc_reg_h
             (proj2 (next_Ereg hc 101)) (FposFR_of_Ereg hc 101) (proj2 FposFR_below190)
             (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj2 FT_below_Tr)) | or_intror F => match F with end end)
             vcuts_h _ (mkVNA (E_reg hc 101) 80 (SLit (2 ^ 61))) eq_refl).
    + intros Jq rho2 tp2 Hs. exact (region_sum_lo_ex Jq rho2 tp2 Hs).
    + intros L [<-|[]]. exists (mkVNA (Tr1 hc 101 s_reg_h R_reg_h) 79 (SLit (2 ^ 61))). split; [in_nth 2|]. split; [reflexivity|]. meas_lit.
  - apply (eexit_reenter_IA segs _ 102 vcuts_h _ (mkVNA (E_L_in hc 101) 101 gs) (mkVNA (CL hc 101) 100 cur) (F_L 101) (CL_0 hc 101) s_L_in tp);
      [in_nth 3 | reflexivity | exact ent_L_in_h | exact I2 | exact HstG | exact (proj2 FL_below)
      | intros r tp' tr md _ HF; split; [exact (glue_L_in hc 101 Hlv101 r HF) | right; split; [cbn [vna_var]; rewrite (meas_L_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ 102 vcuts_h _ (mkVNA (E_L_bk hc 101) 101 (add cur (SLit 1))) (mkVNA (CL hc 101) 100 cur) (F_L 101) (CL_0 hc 101) s_L_bk tp);
      [in_nth 3 | reflexivity | exact ent_L_bk_h | exact I3 | exact HstG | exact (proj2 FL_below)
      | intros r tp' tr md _ HF; split; [exact (glue_L_bk hc 101 Hlv101 r HF) | right; split; [cbn [vna_var]; rewrite (meas_L_bk r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
Qed.
End Seg3HdrEx.

Section ReadHdr.
Variables (J0 J1 : jpredA) (p : list byte) (data : list byte) (offZ : valuation -> Z).
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hst1 : stableA segs 102 J1.
Hypothesis Hoff : ltac2:(tb__ "0|1|
SeS2bS5Z0VoffZ;R1A1M0A2S7G0S9Z2Z40A2A2A2Fr;").
Hypothesis HJfd : ltac2:(tb__ "0|2|
SeS21S3Q40M0A1A1S21S53A1S52VJ0;R4R3R2R1A4S2bS2cS24S54A1S55S56R2A1S4G0Z3A2A2S23S54S57Vp;S4G0VoffZ;R5A1A2A2A2A3S2cS24S21S3Q8A1A1M1A1S69S58R2A1Vp;A2S23G1Vdata;A2A3A2F_;Fmd;Ftr;Ft;Fr;").

Hypothesis HK : ltac2:(tb__ "0|1|
SeS21S3Q40A1A1S21S53A1S52VJ0;R4R3R2R1A4VJ1;S71S2eR5Vdata;VoffZ;R5A1M0A4R4R3S70S2eR5Vp;Vdata;G0R2A6A4F_;Fmd;Ftr;Ft;Fr;").
Hypothesis H4 : ltac2:(tb__ "0|0|
SeS21S3Q40A1A1S21S53A1S52VJ0;R4R3R2R1A4S74U4S2aS3Q8A1S73S2eR5Vdata;VoffZ;R5A1A4A2A2F_;Fmd;Ftr;Ft;Fr;").

Lemma len_le_h : ltac2:(tb__ "0|2|
SeS49ScSfR1A1S13S4aS2eA1A1A3S5S2Q40M0SdS71S2eR2Vdata;VoffZ;R2A1A4M1P65A2A2S2G0SdG1P13A2A2A2F_;Fr;").
Proof.
  intros r HF. unfold rhA_rho'. rewrite rd_next. cbn [Pos.succ].
  rewrite rho_set_rw_at. rewrite !rho_set_rw_other by (cbv; congruence).
  pose proof (rbA_bs_len E_ecall r data (offZ r) (Hoff r)) as Hl. rewrite rd_H12 in Hl.
  change (eval r vC) with (rw r 19) in Hl. pose proof (urange (rw r 19)).
  rewrite len_word_unsigned by (unfold two_pow_64; lia). exact Hl.
Qed.

Theorem read_hdr_sum : ltac2:(tb__ "0|0|
S5eOF_;SeS21S3Q40A1A1S4eS0R3VJ0;A3S68S0R4VJ0;A3S4eS0R5VJ1;A3S5dS0R6S4dS0VJ0;S32R5R4A5S4cS0VJ1;S51R5R4S30S38P65A2A6A4F_;F_;F_;Ftp;Frho;Fok;").
Proof.
  intros ok rho tp Hok0 Hokp0 Hok1.
  set (J0' := withGA (fun r => agree_below NF rho r) J0).
  set (J1' := withGA (fun r => agree_below NF rho r) J1).
  assert (HstG0 : stableA segs NF J0').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst0]. }
  assert (HstG1 : stableA segs 102 J1').
  { apply stableA_withG; [| exact Hst1]. intros r1 r2 H1 H2. eapply agree_below_trans; [exact H1|]. eapply agree_below_le; [|exact H2]. cbv; congruence. }
  assert (HokG0 : ok_frameA segs ok J0') by (intros r t tr ms md msv' [_ HJ]; eapply Hok0; eauto).
  assert (HokpG0 : ok_pframeA segs ok J0') by (intros r t tr ms md x8 [_ HJ]; eapply Hokp0; eauto).
  assert (HokG1 : ok_frameA segs ok J1') by (intros r t tr ms md msv' [_ HJ]; eapply Hok1; eauto).
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J0 NF Pre_rd rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELR [rd_ecall] NF [Pre_rd] [E_ecall] J0' ok (LQA segs J1 NF rho tp (Posts_rd hc 101)) tp HokG0 HstG0 check_rd1);
    [| left; reflexivity].
  intros E rhoE [<-|[]].
  apply triple_factsA. intros HFE.
  eapply triple_conseq; [intros w Hw; exact (conj (H4 rhoE tp _ _ (proj2 (proj2 Hw))) Hw) | intros w Hw; right; exact Hw |].
  apply triple_pure. intros H4E.
  eapply triple_seq with (R := SPA segs J1' (A_after_hdr E_ecall 2 buf (SLit 0) vC) (rhA_rho' E_ecall rhoE data (offZ rhoE)) tp).
  - apply triple1_triple.
    apply (triple1_read_hdrA segs E_ecall rhoE tp 2 buf (SLit 0) vC [] p data (offZ rhoE) 0 rd_Hi rd_H17 rd_H10 (Hoff rhoE)
             (rd_Hcnt rhoE HFE) (rd_Hov rhoE HFE) rd_Hnth (rd_Hbuf rhoE) (rd_Hlo rhoE) (rd_Hhi rhoE HFE) (rd_Hcells rhoE) eq_refl (rd_Hwoff rhoE)
             ok J0' J1' HokG0 HokpG0 HstG0 HstG1 H4E).
    + intros tr md [_ HJ]. exact (HJfd rhoE tp tr md HJ).
    + intros tr md [Hag HJ]. split; [| exact (HK rhoE tp tr md HJ)].
      eapply agree_below_trans; [exact Hag|]. unfold rhA_rho'. rewrite rd_next.
      eapply agree_below_trans; [apply agree_below_set_rw; apply Pos.le_refl | apply agree_below_set_rw; cbv; congruence].
  - eapply triple_conseq; [intros w Hw; exact Hw | | apply (seg3_hdr ok J1' HokG1 HstG1); exact (len_le_h rhoE HFE)].
    intros w Hw. exact (LQA_unG' J1 NF 102 rho _ tp _ w Hw).
Qed.

Theorem read_hdr_sum_ex : ltac2:(tb__ "0|0|
SeS21S3Q40A1A1S5cS0S4dS0VJ0;S32R2R1A5S4cS0VJ1;S51R2R1S30S38P65A2A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  set (J0' := withGA (fun r => agree_below NF rho r) J0).
  set (J1' := withGA (fun r => agree_below NF rho r) J1).
  assert (HstG0 : stableA segs NF J0').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst0]. }
  assert (HstG1 : stableA segs 102 J1').
  { apply stableA_withG; [| exact Hst1]. intros r1 r2 H1 H2. eapply agree_below_trans; [exact H1|]. eapply agree_below_le; [|exact H2]. cbv; congruence. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J0 NF Pre_rd rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_rd with (vna_state (mkVNA Pre_rd 1 (SLit 0))).
  apply (cfg_complete_autoA segs FUELR [rd_ecall] NF [mkVNA Pre_rd 1 (SLit 0)] [mkVNA E_ecall 0 (SLit 0)] J0'
           (LQA segs J1 NF rho tp (Posts_rd hc 101)) tp HstG0);
    [intros n [<-|[]]; cbv; congruence | exact echeck_rd1 | | left; reflexivity].
  intros E rhoE [<-|[]]. cbn [vna_state].
  apply etriple_factsA. intros HFE.
  eapply etriple_conseq; [intros w Hw; exact (conj (H4 rhoE tp _ _ (proj2 (proj2 Hw))) Hw) | intros w Hw; right; exact Hw |].
  apply etriple_pure. intros H4E.
  eapply etriple_seq with (R := SPA segs J1' (A_after_hdr E_ecall 2 buf (SLit 0) vC) (rhA_rho' E_ecall rhoE data (offZ rhoE)) tp).
  - apply (etriple_read_hdrA segs E_ecall rhoE tp 2 buf (SLit 0) vC [] p data (offZ rhoE) 0 rd_Hi rd_H17 rd_H10 (Hoff rhoE)
             (rd_Hcnt rhoE HFE) (rd_Hov rhoE HFE) rd_Hnth (rd_Hbuf rhoE) (rd_Hlo rhoE) (rd_Hhi rhoE HFE) (rd_Hcells rhoE) eq_refl (rd_Hwoff rhoE)
             J0' J1' HstG0 HstG1 H4E).
    + intros tr md [_ HJ]. exact (HJfd rhoE tp tr md HJ).
    + intros tr md [Hag HJ]. split; [| exact (HK rhoE tp tr md HJ)].
      eapply agree_below_trans; [exact Hag|]. unfold rhA_rho'. rewrite rd_next.
      eapply agree_below_trans; [apply agree_below_set_rw; apply Pos.le_refl | apply agree_below_set_rw; cbv; congruence].
  - eapply etriple_conseq; [intros w Hw; exact Hw | | apply (seg3_hdr_ex J1' HstG1); exact (len_le_h rhoE HFE)].
    intros w Hw. exact (LQA_unG' J1 NF 102 rho _ tp _ w Hw).
Qed.
End ReadHdr.

Section ReadDir.
Variables (J0 J1 : jpredA).
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hst1 : stableA segs NF J1.
Hypothesis HJfd : ltac2:(tb__ "0|1|
SeS21S3Q40M0A1A1S21S53A1S52VJ0;R4R3R2R1A4S2cS24S54A1S55S56R2A1S4G0Z3A2A2S23S54S59A2A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HK : ltac2:(tb__ "0|0|
SeS21S3Q40A1A1S21S53A1S52VJ0;R4R3R2R1A4VJ1;R5R4R3R2A4F_;Fmd;Ftr;Ft;Fr;").

Lemma seg3_dir : ltac2:(tb__ "0|0|
S5eOF_;S4fSeS21S3Q40A1A1S4eS0R4R3A3S50S0S51R4A3S5dS0R6S4dS0R5S3dR4R3A5S4cS0R5S51R4R3S36A6A4F_;F_;Ftp;Frho1;FJ1x;Fok;").
Proof.
  intros ok J1x rho1 tp Hok Hst.
  set (J3 := withGA (fun r => agree_below NF rho1 r) J1x).
  assert (HstG : stableA segs NF J3).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok J3) by (intros r t tr ms md msv' [_ HJ]; eapply Hok; eauto).
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J1x NF T_rd_d rho1 tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELR [] NF [T_rd_d] [P_rd_d] J3 ok (LQA segs J1x NF rho1 tp Posts_rd_d) tp HokG HstG check_d); [| left; reflexivity].
  intros E rhoE [<-|[]]. apply exit_postA. in_nth 0.
Qed.

Lemma seg3_dir_ex : ltac2:(tb__ "0|0|
S4fSeS21S3Q40A1A1S50S0S51R3A3S5cS0S4dS0R4S3dR3R2A5S4cS0R4S51R3R2S36A6A3F_;Ftp;Frho1;FJ1x;").
Proof.
  intros J1x rho1 tp Hst.
  set (J3 := withGA (fun r => agree_below NF rho1 r) J1x).
  assert (HstG : stableA segs NF J3).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J1x NF T_rd_d rho1 tp w Hw) | intros w Hw; exact Hw |].
  change T_rd_d with (vna_state (mkVNA T_rd_d 1 (SLit 0))).
  apply (cfg_complete_autoA segs FUELR [] NF [mkVNA T_rd_d 1 (SLit 0)] [mkVNA P_rd_d 0 (SLit 0)] J3 (LQA segs J1x NF rho1 tp Posts_rd_d) tp HstG);
    [intros n [<-|[]]; cbv; congruence | exact echeck_d | | left; reflexivity].
  intros E rhoE [<-|[]]. apply (eexit_postA segs J1x NF rho1 [mkVNA T_rd_d 1 (SLit 0)] Posts_rd_d (mkVNA P_rd_d 0 (SLit 0))). in_nth 0.
Qed.

Theorem read_dir_sum : ltac2:(tb__ "0|0|
S5eOF_;SeS21S3Q40A1A1S4eS0R3VJ0;A3S68S0R4VJ0;A3S4eS0R5VJ1;A3S5dS0R6S4dS0VJ0;S32R5R4A5S4cS0VJ1;S51R5R4S36A6A4F_;F_;F_;Ftp;Frho;Fok;").
Proof.
  intros ok rho tp Hok0 Hokp0 Hok1.
  set (J0' := withGA (fun r => agree_below NF rho r) J0).
  set (J1' := withGA (fun r => agree_below NF rho r) J1).
  assert (HstG0 : stableA segs NF J0').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst0]. }
  assert (HstG1 : stableA segs NF J1').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst1]. }
  assert (HokG0 : ok_frameA segs ok J0') by (intros r t tr ms md msv' [_ HJ]; eapply Hok0; eauto).
  assert (HokpG0 : ok_pframeA segs ok J0') by (intros r t tr ms md x8 [_ HJ]; eapply Hokp0; eauto).
  assert (HokG1 : ok_frameA segs ok J1') by (intros r t tr ms md msv' [_ HJ]; eapply Hok1; eauto).
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J0 NF Pre_rd rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELR [rd_ecall] NF [Pre_rd] [E_ecall] J0' ok (LQA segs J1 NF rho tp Posts_rd_d) tp HokG0 HstG0 check_rd1);
    [| left; reflexivity].
  intros E rhoE [<-|[]].
  apply triple_factsA. intros HFE.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  eapply triple_seq with (R := SPA segs J1' (dirA' E_ecall) rhoE tp).
  - apply triple1_triple.
    apply (triple1_read_dirA segs E_ecall rhoE tp rd_Hi rd_H17 rd_H10 (rd_Hov rhoE HFE)
             ok J0' J1' HokG0 HokpG0 HstG0).
    + intros tr md [_ HJ]. exact (HJfd rhoE tp tr md HJ).
    + intros tr md [Hag HJ]. split; [exact Hag | exact (HK rhoE tp tr md HJ)].
  - eapply triple_conseq; [intros w Hw; exact Hw | | apply (seg3_dir ok J1' rhoE tp HokG1 HstG1)].
    intros w Hw. exact (LQA_unG' J1 NF NF rho _ tp _ w Hw).
Qed.

Theorem read_dir_sum_ex : ltac2:(tb__ "0|0|
SeS21S3Q40A1A1S5cS0S4dS0VJ0;S32R2R1A5S4cS0VJ1;S51R2R1S36A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  set (J0' := withGA (fun r => agree_below NF rho r) J0).
  set (J1' := withGA (fun r => agree_below NF rho r) J1).
  assert (HstG0 : stableA segs NF J0').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst0]. }
  assert (HstG1 : stableA segs NF J1').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst1]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J0 NF Pre_rd rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_rd with (vna_state (mkVNA Pre_rd 1 (SLit 0))).
  apply (cfg_complete_autoA segs FUELR [rd_ecall] NF [mkVNA Pre_rd 1 (SLit 0)] [mkVNA E_ecall 0 (SLit 0)] J0'
           (LQA segs J1 NF rho tp Posts_rd_d) tp HstG0);
    [intros n [<-|[]]; cbv; congruence | exact echeck_rd1 | | left; reflexivity].
  intros E rhoE [<-|[]]. cbn [vna_state].
  apply etriple_factsA. intros HFE.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  eapply etriple_seq with (R := SPA segs J1' (dirA' E_ecall) rhoE tp).
  - apply (etriple_read_dirA segs E_ecall rhoE tp rd_Hi rd_H17 rd_H10 (rd_Hov rhoE HFE)
             J0' J1' HstG0).
    + intros tr md [_ HJ]. exact (HJfd rhoE tp tr md HJ).
    + intros tr md [Hag HJ]. split; [exact Hag | exact (HK rhoE tp tr md HJ)].
  - eapply etriple_conseq; [intros w Hw; exact Hw | | apply (seg3_dir_ex J1' rhoE tp HstG1)].
    intros w Hw. exact (LQA_unG' J1 NF NF rho _ tp _ w Hw).
Qed.
End ReadDir.
End Icpt_read_proof.

