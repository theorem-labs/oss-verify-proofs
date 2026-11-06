(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fp eh fm g0 g1 DrvTLXa.

(* [comment removed for export] *)
Module Str_strnlenA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "agree_below"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA"; "FirstNul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Str_strnlenA_st"; "Posts_sn"; "Pre_sn"; "P_sn"; "s_call"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fp.Icpt_memchr"; "Jf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "entailsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform StrBytes MuslWL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fp.Icpt_memchr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Str_strnlenA_st.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations. Import MCHAddr. Import RegionAddr.
Close Scope bv_scope. Open Scope Z_scope.

Section SN.
Variable ok : world -> Prop.
Variable J0 : jpredA.
Hypothesis Hok : ok_frameA segs ok J0.
Hypothesis Hst0 : stableA segs NF J0.

Lemma FirstNul_call_sn : ltac2:(tb__ "0|0|
S1S5S3A1S11S8R3A1S8S17S16R4R3R2A3ScA2A1F_;Fms;FR;Frho;").
Proof.
  intros rho R ms [H0 H1]. destruct sn_shape as (_ & _ & _ & _ & S16 & _). unfold FirstNul.
  change (rw (rho_sub (rho_absorb rho R ms) s_call) 16) with (eval (rho_absorb rho R ms) (wsub_get s_call 16)). rewrite S16.
  cbn [eval rw rl rho_sub rho_absorb]. split; assumption.
Qed.

Lemma to_post_sn : ltac2:(tb__ "0|0|
S1aS18S1S1S5SfQ40A1A1S1S15S10S6S1bR7SbR6A3S7A3S10S6S19R7S4A2S7A3S2S4R7R6A3S2S4R7R5A3SeS0S12VJ0;R8R7A3RbR6R7R5A6SdS0VJ0;S4RaR8S9R6A7F_;F_;F_;F_;F_;Fw;FrhoR;Ftp;Frho1;Frho;Fsp;FG;").
Proof.
  intros G sp rho rho1 tp rhoR w Hent Hid Hag1 HagR HS.
  pose proof (SPA_entails segs (Jf J0 rho1 tp) NF G P_sn sp rhoR tp w Hent Hid (Jf_stable J0 Hst0 rho1 tp NF (Pos.le_refl _)) HS) as [Hsm (Hag & _ & HJ)].
  exists (mkLeafA P_sn RsSymJump), (rho_sub rhoR sp). split; [left; reflexivity|]. split.
  - eapply agree_below_trans; [exact Hag1 | exact Hag].
  - split; [exact Hsm|]. eapply Hst0; [exact Hag | apply mat_equiv_refl | exact HJ].
Qed.

Theorem sn_sum : ltac2:(tb__ "0|0|
S1S5SfQ40A1A1S8R2A1S14S0Vok;SeS0VJ0;SaR3R2A5SdS0VJ0;S4R3R2S9A6A4F_;Ftp;Frho;").
Proof.
  intros rho tp HFN.
  destruct sn_shape as (HlenP & HnP & HnC & HnCS & _ & HnI & HlF & HnF & HbF & HnRG & Hge).
  apply (triple_pre ok _ (Forall (holds rho) facts_sn)); [intros w [Hsm _]; exact (smatchA_facts segs rho tp Pre_sn w Hsm) | intros HF0].

  eapply (runA_tr segs ok FUEL_SN CUTS_SN Pre_sn _ J0 rho tp); [exact sn_run_call | exact HlenP | exact Hok | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnP in Hag1.
  pose proof (FirstNul_agree NF rho rho1 ltac:(reflexivity) Hag1 HFN) as HFN1.
  pose proof (Forall_holds_agree NF rho rho1 facts_sn Hag1 HbF HF0) as HF1.
  eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) E_callS rho1 tp);
    [intros w [Hsm HJ]; apply (SPA_split segs _ rho1 E_call 0 (SLit (-32)) _ tp w sn_split_call); split;
       [exact Hsm | split; [apply agree_below_refl | split; [reflexivity | exact HJ]]] | intros w Hw; exact Hw |].

  apply (call_soundA segs ok (Jf J0 rho1 tp) (Jmc J0 rho1 tp) (Jmc J0 rho1 tp) (Jf J0 rho1 tp) E_callS Pre_mci s_call R_call Posts_mci _ rho1 tp sn_efr_call sn_chk_call).
  - intros rho2 tp2. apply (triple_pre ok _ (FirstNul rho2)); [intros w [_ (_ & _ & H)]; exact H | intros HFN2].
    exact (mci_sum ok (Jmc J0 rho1 tp) (Jmc_okf ok J0 Hok rho1 tp) (Jmc_stable J0 Hst0 rho1 tp) rho2 tp2 HFN2).
  - intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity|]. split; [exact HJ|]. apply FirstNul_call_sn. exact HFN1.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm _ HLK (-> & HJ' & _). split; [| split; [reflexivity | exact HJ']].
    rewrite <- HnCS. exact (proj1 HLK).
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite sn_imp_call. rewrite HnCS in Hag'.
    apply (triple_pre ok _ (tpL = tp)); [intros w [_ (_ & E & _)]; exact E | intros ->].
    pose proof (Forall_holds_agree NF rho1 rho' facts_sn Hag' HbF HF1) as HF'.
    eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_impF rho' tp);
      [intros w HS; exact (SPA_add_facts _ rho' tp facts_sn T_imp w HF' ltac:(rewrite HnI; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].

    eapply (runA_tr segs ok FUEL_SN CUTS_SN T_impF _ (Jf J0 rho1 tp) rho' tp);
      [exact sn_run_ret | exact HlF | apply (Jf_okf ok J0 Hok) | rewrite HnF; apply (Jf_stable J0 Hst0); unfold NF; lia |].
    intros L2 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnF in HagR.
    intros n Hg w HS. apply Hg. apply (SPA_axforms segs _ XN rhoR R_sn G_sn tp w sn_xf) in HS.
    assert (Hag3 : agree_below NF rho1 rhoR).
    { eapply agree_below_trans; [exact Hag' | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
    exact (to_post_sn G_sn sp_sn rho rho1 tp rhoR w sn_ent sn_ids Hag1 Hag3 HS).
Qed.

Theorem sn_sum_ex : ltac2:(tb__ "0|0|
S1S5SfQ40A1A1S8R2A1S13S0SeS0VJ0;SaR3R2A5SdS0VJ0;S4R3R2S9A6A3F_;Ftp;Frho;").
Proof.
  intros rho tp HFN.
  destruct sn_shape as (HlenP & HnP & HnC & HnCS & _ & HnI & HlF & HnF & HbF & HnRG & Hge).
  apply (etriple_pre _ (Forall (holds rho) facts_sn)); [intros w [Hsm _]; exact (smatchA_facts segs rho tp Pre_sn w Hsm) | intros HF0].
  eapply (erunA_tr segs FUEL_SN CUTS_SN Pre_sn _ J0 rho tp); [exact sn_run_call | exact HlenP | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnP in Hag1.
  pose proof (FirstNul_agree NF rho rho1 ltac:(reflexivity) Hag1 HFN) as HFN1.
  pose proof (Forall_holds_agree NF rho rho1 facts_sn Hag1 HbF HF0) as HF1.
  eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) E_callS rho1 tp);
    [intros w [Hsm HJ]; apply (SPA_split segs _ rho1 E_call 0 (SLit (-32)) _ tp w sn_split_call); split;
       [exact Hsm | split; [apply agree_below_refl | split; [reflexivity | exact HJ]]] | intros w Hw; exact Hw |].
  apply (call_completeA segs (Jf J0 rho1 tp) (Jmc J0 rho1 tp) (Jmc J0 rho1 tp) (Jf J0 rho1 tp) E_callS Pre_mci s_call R_call Posts_mci _ rho1 tp sn_efr_call sn_chk_call).
  - intros rho2 tp2. apply (etriple_pre _ (FirstNul rho2)); [intros w [_ (_ & _ & H)]; exact H | intros HFN2].
    exact (mci_sum_ex (Jmc J0 rho1 tp) (Jmc_stable J0 Hst0 rho1 tp) rho2 tp2 HFN2).
  - intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity|]. split; [exact HJ|]. apply FirstNul_call_sn. exact HFN1.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm _ HLK (-> & HJ' & _). split; [| split; [reflexivity | exact HJ']].
    rewrite <- HnCS. exact (proj1 HLK).
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite sn_imp_call. rewrite HnCS in Hag'.
    apply (etriple_pre _ (tpL = tp)); [intros w [_ (_ & E & _)]; exact E | intros ->].
    pose proof (Forall_holds_agree NF rho1 rho' facts_sn Hag' HbF HF1) as HF'.
    eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_impF rho' tp);
      [intros w HS; exact (SPA_add_facts _ rho' tp facts_sn T_imp w HF' ltac:(rewrite HnI; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
    eapply (erunA_tr segs FUEL_SN CUTS_SN T_impF _ (Jf J0 rho1 tp) rho' tp);
      [exact sn_run_ret | exact HlF | rewrite HnF; apply (Jf_stable J0 Hst0); unfold NF; lia |].
    intros L2 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnF in HagR.
    intros w HS. exists w. split; [apply wsteps_refl|]. apply (SPA_axforms segs _ XN rhoR R_sn G_sn tp w sn_xf) in HS.
    assert (Hag3 : agree_below NF rho1 rhoR).
    { eapply agree_below_trans; [exact Hag' | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
    exact (to_post_sn G_sn sp_sn rho rho1 tp rhoR w sn_ent sn_ids Hag1 Hag3 HS).
Qed.
End SN.
End Str_strnlenA.

(* [comment removed for export] *)
Module Icpt_strnlen.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "agree_below"; "holds"; "sprop"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA"; "FirstNul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Icpt_strnlen_st"; "Posts_si"; "Pre_si"; "P_si"; "facts_si"; "s_call"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fp.Icpt_memchr"; "Jf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "facts_mci"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "entailsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform StrBytes MuslWL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ea.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fp.Icpt_memchr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fk.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Str_strnlenA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Icpt_strnlen_st.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations. Import MCHAddr. Import RegionAddr.
Close Scope bv_scope. Open Scope Z_scope.

Lemma facts_si_mci : ltac2:(tb__ "0|0|
S1S14S4S3R1A1SeA3S14S4S3R2A1S17A3F_;Fr;").
Proof. intros r HF. unfold facts_si in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Section SI.
Variable ok : world -> Prop.
Variable J0 : jpredA.
Hypothesis Hok : ok_frameA segs ok J0.
Hypothesis Hst0 : stableA segs NF J0.

Lemma FirstNul_call_si : ltac2:(tb__ "0|0|
S1S7S5A1S15SaR3A1SaS1cS1bR4R3R2A3SfA2A1F_;Fms;FR;Frho;").
Proof.
  intros rho R ms [H0 H1]. destruct si_shape_call as (_ & _ & _ & _ & S16 & _). unfold FirstNul.
  change (rw (rho_sub (rho_absorb rho R ms) s_call) 16) with (eval (rho_absorb rho R ms) (wsub_get s_call 16)). rewrite S16.
  cbn [eval rw rl rho_sub rho_absorb]. split; assumption.
Qed.

Lemma to_post_si : ltac2:(tb__ "0|0|
S1fS1dS1S1S7S12Q40A1A1S1S1aS13S8S20R7SdR6A3S9A3S13S8S1eR7S6A2S9A3S2S6R7R6A3S2S6R7R5A3S11S0S16VJ0;R8R7A3RbR6R7R5A6S10S0VJ0;S6RaR8SbR6A7F_;F_;F_;F_;F_;Fw;FrhoR;Ftp;Frho1;Frho;Fsp;FG;").
Proof.
  intros G sp rho rho1 tp rhoR w Hent Hid Hag1 HagR HS.
  pose proof (SPA_entails segs (Jf J0 rho1 tp) NF G P_si sp rhoR tp w Hent Hid (Jf_stable J0 Hst0 rho1 tp NF (Pos.le_refl _)) HS) as [Hsm (Hag & _ & HJ)].
  exists (mkLeafA P_si RsSymJump), (rho_sub rhoR sp). split; [left; reflexivity|]. split.
  - eapply agree_below_trans; [exact Hag1 | exact Hag].
  - split; [exact Hsm|]. eapply Hst0; [exact Hag | apply mat_equiv_refl | exact HJ].
Qed.

Theorem si_sum : ltac2:(tb__ "0|0|
S1S7S12Q40A1A1SaR2A1S19S0Vok;S11S0VJ0;ScR3R2A5S10S0VJ0;S6R3R2SbA6A4F_;Ftp;Frho;").
Proof.
  intros rho tp HFN.
  destruct si_shape_call as (HlenP & HnP & HnC & HnCS & _ & HbF). destruct si_shape_imp as (HnI & HlS & HnS & HlB & HnB & Hf140 & HbS & HbB).
  destruct si_shape_rip as (HnRS & HnTr & HlTF & HnTF & HnE & HbTF). destruct si_shape_ret as (HnRS' & HnRB & HgeS & HgeB). destruct si_ids as [IdS IdB].
  apply (triple_pre ok _ (Forall (holds rho) facts_si)); [intros w [Hsm _]; exact (smatchA_facts segs rho tp Pre_si w Hsm) | intros HF0].

  eapply (runA_tr segs ok FUEL_SI CUTS_SI Pre_si _ J0 rho tp); [exact si_run_call | exact HlenP | exact Hok | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnP in Hag1.
  pose proof (FirstNul_agree NF rho rho1 ltac:(reflexivity) Hag1 HFN) as HFN1.
  pose proof (Forall_holds_agree NF rho rho1 facts_si Hag1 HbF HF0) as HF1.
  eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) E_callS rho1 tp);
    [intros w [Hsm HJ]; apply (SPA_split segs _ rho1 E_call 0 (SLit (- F_SI)) _ tp w si_split_call); split;
       [exact Hsm | split; [apply agree_below_refl | split; [reflexivity | exact HJ]]] | intros w Hw; exact Hw |].

  apply (call_soundA segs ok (Jf J0 rho1 tp) (Jmc J0 rho1 tp) (Jmc J0 rho1 tp) (Jf J0 rho1 tp) E_callS Pre_sn s_call R_call Posts_sn _ rho1 tp si_efr_call si_chk_call).
  - intros rho2 tp2. apply (triple_pre ok _ (FirstNul rho2)); [intros w [_ (_ & _ & H)]; exact H | intros HFN2].
    exact (sn_sum ok (Jmc J0 rho1 tp) (Jmc_okf ok J0 Hok rho1 tp) (Jmc_stable J0 Hst0 rho1 tp) rho2 tp2 HFN2).
  - intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity|]. split; [exact HJ|]. apply FirstNul_call_si. exact HFN1.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm _ HLK (-> & HJ' & _). split; [| split; [reflexivity | exact HJ']].
    rewrite <- HnCS. exact (proj1 HLK).
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite si_imp_call. rewrite HnCS in Hag'.
    apply (triple_pre ok _ (tpL = tp /\ Forall (holds rho') (ss_facts (ax_S T_imp))));
      [intros w [Hsm (_ & E & _)]; split; [exact E | exact (smatchA_facts segs _ _ _ w Hsm)] | intros [-> HFi]].
    pose proof (Forall_holds_agree NF rho1 rho' facts_si Hag' HbF HF1) as HF'. pose proof (facts_si_mci rho' HF') as HFm'.
    assert (H140 : rw rho' 140 = rw rho' 16) by exact (holds_fact rho' _ _ HFi Hf140).
    assert (Hz' : rw rho' 16 = rw rho 16).
    { destruct Hag1 as (A1 & _ & _). destruct Hag' as (A2 & _ & _). rewrite <- (A2 16%positive ltac:(reflexivity)), <- (A1 16%positive ltac:(reflexivity)). reflexivity. }
    eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_impF rho' tp);
      [intros w HS; exact (SPA_add_facts _ rho' tp facts_si T_imp w HF' ltac:(rewrite HnI; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
    destruct (Z_lt_le_dec (bv_unsigned (rw rho 16) + 1) 65) as [HzS|HzB].
    +
      assert (HFS : Forall (holds rho') factsS).
      { unfold factsS. constructor; [apply (GEU65_S rho' H140); rewrite Hz'; lia | exact (post_facts_hold rho' HFm' H140)]. }
      eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_S rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsS T_impF w HFS ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (runA_tr segs ok FUEL_SI CUTS_SI T_S _ (Jf J0 rho1 tp) rho' tp);
        [exact si_run_S | exact HlS | apply (Jf_okf ok J0 Hok) | rewrite HnS; apply (Jf_stable J0 Hst0); unfold NF; lia |].
      intros L2 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnS in HagR.
      intros n Hg w HS. apply Hg. apply (SPA_axforms segs _ XS4 rhoR R_S G_S tp w si_xf_S) in HS.
      assert (Hag3 : agree_below NF rho1 rhoR).
      { eapply agree_below_trans; [exact Hag' | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
      exact (to_post_si G_S sp_S rho rho1 tp rhoR w si_ent_S IdS Hag1 Hag3 HS).
    +
      assert (HFB : Forall (holds rho') factsB).
      { unfold factsB. constructor; [apply (GEU65_B rho' HFm' H140); rewrite Hz'; lia |].
        apply Forall_app. split; [exact (post_facts_hold rho' HFm' H140) | apply (big_facts_hold rho' HFm' H140); rewrite Hz'; lia]. }
      eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_B rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsB T_impF w HFB ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (runA_tr segs ok FUEL_SI CUTS_SI T_B _ (Jf J0 rho1 tp) rho' tp);
        [exact si_run_B | exact HlB | apply (Jf_okf ok J0 Hok) | rewrite HnB; apply (Jf_stable J0 Hst0); unfold NF; lia |].
      intros L2 rhoE [<-|[]] HagE. cbn [la_state]. rewrite HnB in HagE.
      eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) E_ripS rhoE tp);
        [intros w HS; exact (SPA_split segs _ rhoE E_rip 0 (SLit (-80)) _ tp w si_split_rip HS) | intros w Hw; exact Hw |].
      apply (call_soundA segs ok (Jf J0 rho1 tp) (Jz J0 rho1 tp) (Jz J0 rho1 tp) (Jf J0 rho1 tp) E_ripS Pre_rip s_rip R_rip Posts_rip _ rhoE tp si_efr_rip si_chk_rip).
      * intros rho2 tp2. exact (region_sum ok (Jz J0 rho1 tp) rho2 tp2 (Jz_okf ok J0 Hok rho1 tp) (Jz_stable J0 Hst0 rho1 tp NF)).
      * intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity | exact HJ].
      * intros L rho'' rhoL tpL tr ms md tr' md' HinL Hsm (HagE' & _ & _) HLK [-> HJ']. split; [| split; [reflexivity | exact HJ']].
        eapply agree_below_trans; [exact HagE' |]. eapply agree_below_le; [| exact (proj1 HLK)]. rewrite HnRS. apply Pos.leb_le in HnE. unfold NF in *; lia.
      * intros L rho'' tpL [<-|[]] Hag''. cbn [la_state]. rewrite si_imp_rip. rewrite HnRS in Hag''. apply Pos.leb_le in HnE.
        apply (triple_pre ok _ (tpL = tp)); [intros w [_ (_ & E & _)]; exact E | intros ->].
        assert (HF'' : Forall (holds rho'') (SPEq (SVar 140) (SVar 16) :: facts_si)).
        { apply (Forall_holds_agree 141 rho' rho''); [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | constructor; [exact (holds_fact rho' _ _ HFi Hf140) | exact HF']].
          eapply agree_below_trans; [exact HagE | eapply agree_below_le; [exact HnE | exact Hag'']]. }
        eapply triple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_ripF rho'' tp);
          [intros w HS; exact (SPA_add_facts _ rho'' tp _ T_rip w HF'' ltac:(rewrite HnTr; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
        eapply (runA_tr segs ok FUEL_SI CUTS_SI T_ripF _ (Jf J0 rho1 tp) rho'' tp);
          [exact si_run_B2 | exact HlTF | apply (Jf_okf ok J0 Hok) | rewrite HnTF; apply (Jf_stable J0 Hst0); unfold NF; lia |].
        intros L3 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnTF in HagR.
        intros n Hg w HS. apply Hg. apply (SPA_axforms segs _ XB4 rhoR R_B G_B tp w si_xf_B) in HS.
        assert (Hag3 : agree_below NF rho1 rhoR).
        { eapply agree_below_trans; [exact Hag' |]. eapply agree_below_trans; [eapply agree_below_le; [| exact HagE]; unfold NF; lia |].
          eapply agree_below_trans; [eapply agree_below_le; [| exact Hag'']; unfold NF; lia | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
        exact (to_post_si G_B sp_B rho rho1 tp rhoR w si_ent_B IdB Hag1 Hag3 HS).
Qed.

Theorem si_sum_ex : ltac2:(tb__ "0|0|
S1S7S12Q40A1A1SaR2A1S18S0S11S0VJ0;ScR3R2A5S10S0VJ0;S6R3R2SbA6A3F_;Ftp;Frho;").
Proof.
  intros rho tp HFN.
  destruct si_shape_call as (HlenP & HnP & HnC & HnCS & _ & HbF). destruct si_shape_imp as (HnI & HlS & HnS & HlB & HnB & Hf140 & HbS & HbB).
  destruct si_shape_rip as (HnRS & HnTr & HlTF & HnTF & HnE & HbTF). destruct si_shape_ret as (HnRS' & HnRB & HgeS & HgeB). destruct si_ids as [IdS IdB].
  apply (etriple_pre _ (Forall (holds rho) facts_si)); [intros w [Hsm _]; exact (smatchA_facts segs rho tp Pre_si w Hsm) | intros HF0].
  eapply (erunA_tr segs FUEL_SI CUTS_SI Pre_si _ J0 rho tp); [exact si_run_call | exact HlenP | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnP in Hag1.
  pose proof (FirstNul_agree NF rho rho1 ltac:(reflexivity) Hag1 HFN) as HFN1.
  pose proof (Forall_holds_agree NF rho rho1 facts_si Hag1 HbF HF0) as HF1.
  eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) E_callS rho1 tp);
    [intros w [Hsm HJ]; apply (SPA_split segs _ rho1 E_call 0 (SLit (- F_SI)) _ tp w si_split_call); split;
       [exact Hsm | split; [apply agree_below_refl | split; [reflexivity | exact HJ]]] | intros w Hw; exact Hw |].
  apply (call_completeA segs (Jf J0 rho1 tp) (Jmc J0 rho1 tp) (Jmc J0 rho1 tp) (Jf J0 rho1 tp) E_callS Pre_sn s_call R_call Posts_sn _ rho1 tp si_efr_call si_chk_call).
  - intros rho2 tp2. apply (etriple_pre _ (FirstNul rho2)); [intros w [_ (_ & _ & H)]; exact H | intros HFN2].
    exact (sn_sum_ex (Jmc J0 rho1 tp) (Jmc_stable J0 Hst0 rho1 tp) rho2 tp2 HFN2).
  - intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity|]. split; [exact HJ|]. apply FirstNul_call_si. exact HFN1.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm _ HLK (-> & HJ' & _). split; [| split; [reflexivity | exact HJ']].
    rewrite <- HnCS. exact (proj1 HLK).
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite si_imp_call. rewrite HnCS in Hag'.
    apply (etriple_pre _ (tpL = tp /\ Forall (holds rho') (ss_facts (ax_S T_imp))));
      [intros w [Hsm (_ & E & _)]; split; [exact E | exact (smatchA_facts segs _ _ _ w Hsm)] | intros [-> HFi]].
    pose proof (Forall_holds_agree NF rho1 rho' facts_si Hag' HbF HF1) as HF'. pose proof (facts_si_mci rho' HF') as HFm'.
    assert (H140 : rw rho' 140 = rw rho' 16) by exact (holds_fact rho' _ _ HFi Hf140).
    assert (Hz' : rw rho' 16 = rw rho 16).
    { destruct Hag1 as (A1 & _ & _). destruct Hag' as (A2 & _ & _). rewrite <- (A2 16%positive ltac:(reflexivity)), <- (A1 16%positive ltac:(reflexivity)). reflexivity. }
    eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_impF rho' tp);
      [intros w HS; exact (SPA_add_facts _ rho' tp facts_si T_imp w HF' ltac:(rewrite HnI; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
    destruct (Z_lt_le_dec (bv_unsigned (rw rho 16) + 1) 65) as [HzS|HzB].
    + assert (HFS : Forall (holds rho') factsS).
      { unfold factsS. constructor; [apply (GEU65_S rho' H140); rewrite Hz'; lia | exact (post_facts_hold rho' HFm' H140)]. }
      eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_S rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsS T_impF w HFS ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (erunA_tr segs FUEL_SI CUTS_SI T_S _ (Jf J0 rho1 tp) rho' tp);
        [exact si_run_S | exact HlS | rewrite HnS; apply (Jf_stable J0 Hst0); unfold NF; lia |].
      intros L2 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnS in HagR.
      intros w HS. exists w. split; [apply wsteps_refl|]. apply (SPA_axforms segs _ XS4 rhoR R_S G_S tp w si_xf_S) in HS.
      assert (Hag3 : agree_below NF rho1 rhoR).
      { eapply agree_below_trans; [exact Hag' | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
      exact (to_post_si G_S sp_S rho rho1 tp rhoR w si_ent_S IdS Hag1 Hag3 HS).
    + assert (HFB : Forall (holds rho') factsB).
      { unfold factsB. constructor; [apply (GEU65_B rho' HFm' H140); rewrite Hz'; lia |].
        apply Forall_app. split; [exact (post_facts_hold rho' HFm' H140) | apply (big_facts_hold rho' HFm' H140); rewrite Hz'; lia]. }
      eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_B rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsB T_impF w HFB ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (erunA_tr segs FUEL_SI CUTS_SI T_B _ (Jf J0 rho1 tp) rho' tp);
        [exact si_run_B | exact HlB | rewrite HnB; apply (Jf_stable J0 Hst0); unfold NF; lia |].
      intros L2 rhoE [<-|[]] HagE. cbn [la_state]. rewrite HnB in HagE.
      eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) E_ripS rhoE tp);
        [intros w HS; exact (SPA_split segs _ rhoE E_rip 0 (SLit (-80)) _ tp w si_split_rip HS) | intros w Hw; exact Hw |].
      apply (call_completeA segs (Jf J0 rho1 tp) (Jz J0 rho1 tp) (Jz J0 rho1 tp) (Jf J0 rho1 tp) E_ripS Pre_rip s_rip R_rip Posts_rip _ rhoE tp si_efr_rip si_chk_rip).
      * intros rho2 tp2. exact (region_sum_ex (Jz J0 rho1 tp) rho2 tp2 (Jz_stable J0 Hst0 rho1 tp NF)).
      * intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity | exact HJ].
      * intros L rho'' rhoL tpL tr ms md tr' md' HinL Hsm (HagE' & _ & _) HLK [-> HJ']. split; [| split; [reflexivity | exact HJ']].
        eapply agree_below_trans; [exact HagE' |]. eapply agree_below_le; [| exact (proj1 HLK)]. rewrite HnRS. apply Pos.leb_le in HnE. unfold NF in *; lia.
      * intros L rho'' tpL [<-|[]] Hag''. cbn [la_state]. rewrite si_imp_rip. rewrite HnRS in Hag''. apply Pos.leb_le in HnE.
        apply (etriple_pre _ (tpL = tp)); [intros w [_ (_ & E & _)]; exact E | intros ->].
        assert (HF'' : Forall (holds rho'') (SPEq (SVar 140) (SVar 16) :: facts_si)).
        { apply (Forall_holds_agree 141 rho' rho''); [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | constructor; [exact (holds_fact rho' _ _ HFi Hf140) | exact HF']].
          eapply agree_below_trans; [exact HagE | eapply agree_below_le; [exact HnE | exact Hag'']]. }
        eapply etriple_conseq with (P := SPA segs (Jf J0 rho1 tp) T_ripF rho'' tp);
          [intros w HS; exact (SPA_add_facts _ rho'' tp _ T_rip w HF'' ltac:(rewrite HnTr; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
        eapply (erunA_tr segs FUEL_SI CUTS_SI T_ripF _ (Jf J0 rho1 tp) rho'' tp);
          [exact si_run_B2 | exact HlTF | rewrite HnTF; apply (Jf_stable J0 Hst0); unfold NF; lia |].
        intros L3 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnTF in HagR.
        intros w HS. exists w. split; [apply wsteps_refl|]. apply (SPA_axforms segs _ XB4 rhoR R_B G_B tp w si_xf_B) in HS.
        assert (Hag3 : agree_below NF rho1 rhoR).
        { eapply agree_below_trans; [exact Hag' |]. eapply agree_below_trans; [eapply agree_below_le; [| exact HagE]; unfold NF; lia |].
          eapply agree_below_trans; [eapply agree_below_le; [| exact Hag'']; unfold NF; lia | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
        exact (to_post_si G_B sp_B rho rho1 tp rhoR w si_ent_B IdB Hag1 Hag3 HS).
Qed.
End SI.
End Icpt_strnlen.

(* [comment removed for export] *)
Module Start6JStates.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SAlu"; "SPUle"; "SVar"; "reg_sv"; "sstate"; "SPAlign"; "sobj"; "ss_objs"; "ss_pc"; "swf"; "mkSS"; "sprop_eqb"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_regs"; "ss_resv"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "prod"; "nil"; "pair"; "list"; "true"; "app"; "Some"; "option"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "FE"; "ax_X"; "ax_base"; "ax_setS"; "axwf"; "mkAX"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "Ecall"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "eqb"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Start6JStates"; "E_s17"; "CF16"; "ebot16"; "DX16"; "DX17"; "F17_of"; "F17n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run7"; "F17_7"; "IP16_7"; "IPm_7"; "IPr_7"; "M16_7"; "R16_7"; "s16_7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States"; "c1"; "R16b"; "classes16"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States"; "ECALL_MMAP"; "restate_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.Start6Run0"; "F17_0"; "IP16_0"; "IPm_0"; "IPr_0"; "M16_0"; "R16_0"; "s16_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.Start6Run1"; "F17_1"; "IP16_1"; "IPm_1"; "IPr_1"; "M16_1"; "R16_1"; "s16_1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run2"; "F17_2"; "IP16_2"; "IPm_2"; "IPr_2"; "M16_2"; "R16_2"; "s16_2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run3"; "F17_3"; "IP16_3"; "IPm_3"; "IPr_3"; "M16_3"; "R16_3"; "s16_3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run4"; "F17_4"; "IP16_4"; "IPm_4"; "IPr_4"; "M16_4"; "R16_4"; "s16_4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run5"; "F17_5"; "IP16_5"; "IPm_5"; "IPr_5"; "M16_5"; "R16_5"; "s16_5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run6"; "F17_6"; "IP16_6"; "IPm_6"; "IPr_6"; "M16_6"; "R16_6"; "s16_6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "noX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA"; "bump_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.Start6Run0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.Start6Run1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g0.Start6Run4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g1.Start6Run7.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition M16_of (t : Z) : axst := ltac2:(tb__ "0|3|
S1S27Lt;Vt;S50S0S0S27Lp;R1S0S0S27Lp0;M0R1S0S42Lp1;S0S0S27Lp1;M1R1S0S42Lp2;M2G2S73X0x3Lp1;S65X0x3Lp0;S0G0R1S0G1R1G2G2S7aX0x3Lp1;S0G1R1G2G2S6cX0x3Lp1;S5eX0x3Lp0;S57X0x3Lp;S0S42Lp;X1x3").
Definition s16_of (t : Z) : wsub := ltac2:(tb__ "0|3|
S1S3dLt;Vt;S52S0S0S3dLp;R1S0S0S3dLp0;M0R1S0S44Lp1;S0S0S3dLp1;M1R1S0S44Lp2;M2G2S75X0x3Lp1;S67X0x3Lp0;S0G0R1S0G1R1G2G2S7cX0x3Lp1;S0G1R1G2G2S6eX0x3Lp1;S60X0x3Lp0;S59X0x3Lp;S0S44Lp;X1x3").
Definition R16_of (t : Z) : list sobj := ltac2:(tb__ "0|4|
S1S20SbA1M0Lt;Vt;S51S0S0G0Lp;R1S0S0G0Lp0;M1R1S0S43Lp1;S0S0G0Lp1;M2R1S0S43Lp2;M3G3S74X0x3Lp1;S66X0x3Lp0;S0G1R1S0G2R1G3G3S7bX0x3Lp1;S0G2R1G3G3S6dX0x3Lp1;S5fX0x3Lp0;S58X0x3Lp;S0S43Lp;X1x3").
Definition IP16_of (t : Z) : axst := ltac2:(tb__ "0|3|
S1S27Lt;Vt;S4dS0S0S27Lp;R1S0S0S27Lp0;M0R1S0S3fLp1;S0S0S27Lp1;M1R1S0S3fLp2;M2G2S70X0x3Lp1;S62X0x3Lp0;S0G0R1S0G1R1G2G2S77X0x3Lp1;S0G1R1G2G2S69X0x3Lp1;S5bX0x3Lp0;S54X0x3Lp;S0S3fLp;X1x3").
Definition IPm_of (t : Z) : sstate := ltac2:(tb__ "0|3|
S1S9Lt;Vt;S4eS0S0S9Lp;R1S0S0S9Lp0;M0R1S0S40Lp1;S0S0S9Lp1;M1R1S0S40Lp2;M2G2S71X0x3Lp1;S63X0x3Lp0;S0G0R1S0G1R1G2G2S78X0x3Lp1;S0G1R1G2G2S6aX0x3Lp1;S5cX0x3Lp0;S55X0x3Lp;S0S40Lp;X1x3").
Definition IPr_of (t : Z) : axst := ltac2:(tb__ "0|3|
S1S27Lt;Vt;S4fS0S0S27Lp;R1S0S0S27Lp0;M0R1S0S41Lp1;S0S0S27Lp1;M1R1S0S41Lp2;M2G2S72X0x3Lp1;S64X0x3Lp0;S0G0R1S0G1R1G2G2S79X0x3Lp1;S0G1R1G2G2S6bX0x3Lp1;S5dX0x3Lp0;S56X0x3Lp;S0S41Lp;X1x3").
Definition F17_of (t : Z) : axst := ltac2:(tb__ "0|3|
S1S27Lt;Vt;S4cS0S0S27Lp;R1S0S0S27Lp0;M0R1S0S3eLp1;S0S0S27Lp1;M1R1S0S3eLp2;M2G2S6fX0x3Lp1;S61X0x3Lp0;S0G0R1S0G1R1G2G2S76X0x3Lp1;S0G1R1G2G2S68X0x3Lp1;S5aX0x3Lp0;S53X0x3Lp;S0S3eLp;X1x3").

Definition CF16 : list sprop := ltac2:(tb__ "0|d|
S22S4S1bS4SaP4fM0ZfA2S1bS4SaP50M1ZcM2A2S1eS4A1M3A3A3S22S4S29G1S7G0A1M4A2S1bS4S6S3S32Z7fff7f800000Z7000M5A2A1G4A2S1bS4S6G4S3S32S35Z2Z2fA2M6Z800000M7A2A1A2S1bS4S6S5S2fS7P1A1M8S3S32S32Na0M9G7A2G5A2A1A3G4A2S1bS4S6G4S5S2fG8S3S32Zf5fMaG7A2A1A3A2S1bS4SaP51MbG2A2S1bS4S6S5S2fG8S3G9A1A3S7GbA1McA2S1bS4S6GcS5S2fG8S3GaA1A3A2S1bS4S6GcS3G6A1A2S1bS4S6S3Z7fff80000000A1GcA2G3A3A3A3A3A3A3A3A3A3A3A3").

Definition ebot16 (t : Z) : sv := ltac2:(tb__ "0|1|
S1cS2L_;S33Vt;Z0A2S7P4fA1M0S5S2fG0S3S34Z1000Vt;A2A1A3X1cx2").
Definition DX16 (t : Z) : list (sv * sv) := ltac2:(tb__ "0|2|
S1bS1dS2S2A2M0S1fS2S2S38Vt;A1S5S2fS7P51A1M1S3N800000A1A3A4S1bG0S1fS2S2S5S2fS7P4fA1S3S45Vt;A1A1A3G1A4S1eG0A1A3A3").

Definition F17n (t : Z) : sstate := bump_next (ax_S (F17_of t)) 81%positive.

Definition canon17 (S : sstate) : axst := ltac2:(tb__ "0|0|
S4bS39Z0A1VS;A2S9S2eSfSdR1A1S16R1A1S13R1A1S12R1A1S17R1A1ScR1A1S22S4S37S11S46A1A3P53S14R1A1A9S1eS1dS2S2A2A1S3S48A1A3TS';").
Definition E_s17 : axst := Eval vm_compute in canon17 (F17n 0).

Definition DX17 (t : Z) : list (sv * sv) := ltac2:(tb__ "0|3|
S1bS1dS2S2A2M0S1fS2S2S38Vt;A1S5S2fS7P51A1M1S3N800000A1A3A4M2S1bG0S1fS2S2S5S2fS7P4fA1S3S45Vt;A1A1A3G1A4S1bG0G2S1eG0A1A3A3A3").

Lemma sd17 : ltac2:(tb__ "0|5|
S1S81S1R1S47A3S1aS20S4A1M0G0S19S18S24S1dS20S1dS2S2A2A1M1G0A2M2A1S7fS7eS3cR3A1M3P53A2S28S36A1M4A2S23G2S1fG1G0S3aR3A1R1A4A2A3S19S18S1cS83S4S4S82S4S10R1A1S37A3Lf;R1A3S21A3S19S18S1cSeG4A1S21A3S19S18S1cSeG3A1S21A3S18S1cS2dS2cS7dS3bR3A1A1G3A2A1S21A3A2A2A2A2Lnf;A2F_;Ft;").
Proof.
  intros t Ht. destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; eexists;
    (split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]]]).
Qed.

Lemma E_s17_at : ltac2:(tb__ "0|4|
S19S18S1SdS28S36A1M0A1M1S4aA3S19S18S0S15G0A1P53A3S19S18S24S30A1S80S49G1A2S23S30S31A2A3S19S18S20S1dS2S2A2M2A1S2aS36A1S1eG2A1A3S19S18S2S2bS36A1S3S48A1A3S19S18S26S25SbScG0A1A2U19A3S19S18S2S8G0Z11A2S3ZdeA1A3S19S18S2S8G0ZaA2S3Z0A1M3A3S19S18S2S8G0ZbA2S3Zb09000A1A3S19S18S2S8G0ZcA2S3Z3A1A3S19S18S2S8G0ZdA2S3Z22A1A3S19S18S2S8G0ZeA2S3ZffffffffffffffffA1A3S18S2S8G0ZfA2G3A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6JStates.

(* [comment removed for export] *)
Module DrvSite.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "valuation"; "SLit"; "ss_next"; "ss_facts"; "sstate"; "ss_objs"; "sprop_eqb"; "SPUle"; "rw"; "sv_eqb"; "holds"; "ss_lenient"; "cell"; "eval"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "mkObj"; "obj_range"; "sprop_below"; "DUnknown"; "SAlu"; "SVar"; "ob_base"; "ob_hi"; "ob_lo"; "odefault"; "swf"; "SPEq"; "agree_below"; "rm"; "SAluW"; "SExt"; "SLBytes"; "SMd"; "SMdW"; "ob_cells"; "ob_dflt"; "tfact"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "or"; "ex"; "not"; "True"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "prod"; "nil"; "option"; "andb"; "nat"; "false"; "Some"; "cons"; "pair"; "app"; "fst"; "orb"; "None"; "snd"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "ax_base"; "sym_runA"; "mkAX"; "la_state"; "mkLeafA"; "ax_setS"; "entailsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "ExitEv"; "FdChannel"; "WriteEv"; "fd_lookup"; "m_fds"; "m_fs"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "pow"; "leb"; "lt"; "sub"; "opp"; "ltb"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "setregs"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "LQA"; "smatchA"; "stableA"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "nd_below"; "nd_tv"; "ANone"; "NDA"; "nd_am"; "JA"; "JAi"; "nd_bd"; "nd_fr"; "tvinA"; "TPA"; "am_eqb"; "am_subst"; "amode"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "FERR"; "PEND"; "Pre_exit"; "Pre_exitP"; "supportedP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite.SITE"; "sp0_factsb"; "sp0_off"; "drv_xrb"; "xrs_checkD"; "drv_objb"; "robjs_checkD"; "kept_nzb"; "ob_shapeb"; "one_leaf"; "HKV_K"; "arg1b"; "argtop_factsb"; "d6_okb"; "ex_pipe"; "fb_pipe"; "HKP_K"; "cst_rangeb"; "ex_S5c"; "ex_S6"; "sp0_rangeb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "tcons"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite.SITE.FbChain"; "CF"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "cls_kept_freeA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "seq"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit"; "ch1"; "supported"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "vB"; "PreF"; "vCap"; "s_fb"; "vTP"; "PostF"; "sp0"; "vA1"; "locate"; "CUTS_X"; "DEEP"; "FUEL_X"; "N_ex"; "s_ex"; "spM"; "spT"; "vL3"; "O_deepM"; "O_deepS"; "dropX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa"; "BX0"; "KV_T"; "KP_T"; "CST_drv"; "HKVrng_T"; "HCSTKV_T"; "SH0";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite.SITE.ExitHandoff"; "S5c"; "CX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "img_cell_apply"; "img_cell_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "ERRNO_A"; "acell"; "cells_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "lcarve"; "lc_obj"; "JAK"; "carve_okb"; "JA_carve"; "JA_uncarve"; "pure_callJ"; "uncarve_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "errno_addrA"; "AE_A"; "alloc_contractsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "rho_absorb"; "rho_sub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsCut"; "stop_reason"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "KU"; "bd_below"; "bud_pay"; "bitem"; "bd_subst"; "bud_le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "is_prefix"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T0"; "T_ok"; "tvv"; "tvz"; "FBx"; "robj_tracked"; "tnz"; "tv_sub_eqb"; "tvd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "cmaddrA"; "lit_in_ranges"; "xr_tracked"; "robjs_checkA"; "site_okA"; "xr_in_stack_obj"; "xrs_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite.SITE.FreeCall"; "ndJ"; "ndX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "pclMA"; "robjs_okF"; "xrs_okF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform MuslWLA DrvGlueA DrvGlueB.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvJ DrvTLXa.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import PFAddr TAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma U_add_lit : ltac2:(tb__ "0|4|
S3S0S2dS31S60S65S61Z2M0Z3fA2M1A1R1A2S63R1G1A2A2S31S60Z0S5fS6bQ40M2S10R4R3A2A2R2A2M3A2S63G3S61G0Z40A2A2A2S30S2dS6bG2S10R5S1bSb2R4S4R3A1A3A2A2S5fS6bG2S10R5R4A2A2R3A2A3F_;F_;Fd;Fb;Frho;").
Proof.
  intros rho b d Hd Hr. rewrite U_add, U_lit. rewrite <- !M64v_eq.
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.

Lemma obj_range_lits : ltac2:(tb__ "0|2|
S3S0S2dS2dS38SfA1S20S60S65S61Z2Z3eA2M0A1R4A2S60R5R4A2S63R5G0A2S30S3aS2dS2dA2S18R9S17R8S4R7A1S4R6A1R5R4A5A2S42S2dS2dS5fS6bQ40S10R9R8A2A2M1R7A2S5fG1R6A2A4A3F_;F_;F_;Fd;Fcs;Fhi;Flo;Fb;Frho;").
Proof.
  intros. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. reflexivity.
Qed.

Section SITE.
Variable AInv : ltac2:(tb__ "0|0|
Sa8S3S38S6aQ40A1A1S57OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S2dSd4VCST;R1A2S31S60Z0R2A2S63R2S11aA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2dSd4VXGL;R1A2S31S60Z0R2A2S63R2S11aA2A2F_;Fa;").
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S2dSd4SccR1A2Sd4VCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.
Variable ok : world -> Prop.
Variable Spec : list event -> Prop.
Hypothesis HOKJ : ltac2:(tb__ "0|0|
S6eS3S38S6aQ40A1A1S38S56A1S57R5R4R3R2R1A4Sa2VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;S6fS4aVok;R2A3F_;FJ;").
Hypothesis HOKP : ltac2:(tb__ "0|0|
S6eS3S38S6aQ40A1A1S38S56A1S57R5R4R3R2R1A4Sa2VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;S125S4aVok;R2A3F_;FJ;").
Hypothesis Hokh : ok_halted ok Spec.
Hypothesis AC : ltac2:(tb__ "0|0|
SebS4aSeaVAInv;VCST;VXGL;A5").

Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Hypothesis HP0SH : ltac2:(tb__ "0|0|
S3VP0f;R1A1ScfR2A1F_;Fr;").
Hypothesis HKtc : ltac2:(tb__ "0|0|
S38S56A1S57VKc;R2R1A2Sa2VSpec;R3A2F_;Fmd;Ftr;").

Variable PA : AA -> Prop.
Hypothesis HPAf : ltac2:(tb__ "0|0|
Sa8Sa8VPA;R2A1SabR3R2A2VPA;R3A1F_;F_;FA';FA;").

Let JK (nd : ndesc) : jpredA := ltac2:(tb__ "0|1|
S7dVAInv;VCST;VXGL;S68VKc;Vrho0;VP0f;S3bS3aS2dS2dA2M0A1S3bS3aG0S2dA2A1Sc9VPA;Vnd;Ac").

Lemma HKV_K : ltac2:(tb__ "0|1|
Sa8OF_;Se7S77Sa8S2dS3S38S6aQ40A1A1S38S56A1S57S7eVAInv;VCST;VXGL;S68R8Vrho0;VP0f;S3bS3aS2dS2dA2M0A1S3bS3aG0S2dA2A1Sc9R9R7R6R5R4R3R2R1A12Sd7Sd9S4aS24R5A1A2ScaA2F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc';FPA';").
Proof.
  intros PA' Kc' nd Ai kc rho tp tr md (Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK0 & HP0 & _).
  unfold KV_T. apply Forall_app. split; [|apply Forall_app; split; [|exact (KVpp_ok AInv CST HLPP Ai rho tp md HM)]].
  - pose proof (law_rtc _ _ _ ALA Ai rho tp md HM) as HR.
    apply Forall_forall. intros c Hc. exact (proj1 (Forall_forall _ _) HR c (KVrtc_in _ c Hc)).
  - destruct (HP0SH _ HP0) as [HZ _]. destruct HK0 as [K1 _].
    assert (BY : forall a, 0x800c0998 <= a < 0x800c09a8 -> view segs (rm rho) a = Some (Z_to_bv 8 0)).
    { intros a Ha. rewrite view_in by lia. rewrite DrvJ.rd_of_high by lia.
      rewrite (K1 a ltac:(lia)).
      - exact (HZ a Ha).
      - right. split; [|rewrite (HZ a Ha); discriminate]. exists (8 * (a - SHADOW_OFF)). split; [unfold SHADOW_OFF; lia|]. split.
        + left. right. left. split; [apply HCSTdrv; exists 0x644ca8, 0x450; split; [cbn; tauto | unfold SHADOW_OFF; lia] | unfold errno_addrA, ERRNO_A, SHADOW_OFF; lia].
        + unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    unfold KVsh. repeat constructor; intros j Hj; cbn [c_addr c_w c_val] in Hj |- *;
      rewrite BY by lia; f_equal;
      do 8 (destruct j as [|j]; [reflexivity|]); lia.
Qed.

Lemma HKP_K : ltac2:(tb__ "0|3|
Sa8OF_;Se7S77Sa8S2dS3S38S6aQ40M0A1A1S38S56A1S57S2dS2dS2dS7eVAInv;VCST;VXGL;S68RbVrho0;VP0f;S3bS3aS2dS2dA2M1A1S3bS3aG1S2dA2A1Sc9RcRaR9R8R7R6R5R4A12S74G1S42S2dS2dR4R3A4ScbA3S31S60R5R3A2S63R3R4A2A2S31S31S60Z646000R4A2S63R4S61Z2Z40A2A2A2S35S30S3cS6aQ8A1M2A1S24RaS6cG0R4A2A2S46G2A1A3A1A2F_;F_;F_;Fz;Fhi;Flo;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc';FPA';").
Proof.
  intros PA' Kc' nd Ai kc rho tp tr md lo hi z (Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK0 & HP0 & _) Hin Hz.
  destruct (HP0SH _ HP0) as [_ HP]. destruct HK0 as [K1 _].
  unfold KP_T in Hin. cbn in Hin.
  assert (RNG : 0x7fffc570 <= z < 0x7fffc750 \/ 0x800158a8 <= z < 0x80015ba8).
  { destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. }
  split; [lia|]. rewrite (K1 z ltac:(lia)); [exact (HP z RNG)|].
  right. split; [|exact (HP z RNG)]. exists (8 * (z - SHADOW_OFF)). split; [unfold SHADOW_OFF; lia|]. split.
  - left. right. left. split; [apply HCSTdrv; destruct RNG as [R|R]; [exists 0x22b80, 0xf00 | exists 0xec540, 0x1800]; (split; [cbn; tauto | unfold SHADOW_OFF; lia])
                             | unfold errno_addrA, ERRNO_A, SHADOW_OFF; destruct RNG; lia].
  - unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Let HCK := HCSTKV_T AInv CST HCSTok HLPP.
Let carveK : ltac2:(tb__ "0|3|
Se7S77S4cS3S38S6aQ40A1A1Sa1S38SdbA1S2eS6dS4aSddVAInv;VCST;VXGL;S68Vrho0;VP0f;S3bS3aS2dS2dA2M0A1M1S3bS3aG0S2dA2A1M2Sc9VPA;R8R7AcR6R5R4R3A6S4bR7A1S7S11S14R1A1S15R1A1S13R1A1S12R1A1S16R1A1S43S1S8R1A1SadSdbS1SdcR4A4A3S6R1A1R3SeR1A1A9S7S30S37S21R1A1S39A3S30S37Sa5S5R3A1R5A2S39A3S30S0S4fRbA1S4S119A1A3S30S37SdeS6R5A1S8R5A1S4eRcA1ScaScbS79RdA1R8A7S39A3S6dS4aSddVAInv;VCST;VXGL;S68Vrho0;VP0f;G1G2Sc9VPA;RfReAcS54RdR5A2RcRbRaA6F_;F_;F_;F_;TS';TS;F_;Fnx;FN;Fw;Ftp;Frho;FA;Fnd;FKc;") := ltac2:(tb__ "0|1|
SdfVAInv;VCST;VXGL;VALA;S68Vrho0;VP0f;S3bS3aS2dS2dA2M0A1S3bS3aG0S2dA2A1Sc9VPA;ScaS95VPA;A1ScdScbS9bVPA;A1A10").
Let uncarveK : ltac2:(tb__ "0|5|
Se7S77S4cS3S38S6aQ40A1A1S38S56A1M0Sf4S57S38S1A1M1S38SdbA1Se8RaA1S30G1S8S4bR9A1A1S43S1R3SadSdbS1SdcR2A4A3A3S30S37Se2ScaR3A2S39A3S30S85S7cRcA1S7aA3S30S37S78S5S4bRcA1A1RdA2S39A3S6dS4aSddVAInv;VCST;VXGL;S68Vrho0;VP0f;S3bS3aS2dS2dA2M2A1M3S3bS3aG2S2dA2A1M4Sc9VPA;RfReAcRdRcRbS42G0S103RaS105R9R8A2A4A6S6dS4aSddVAInv;VCST;VXGL;S68Vrho0;VP0f;G3G4Sc9VPA;R10RfAcS54ReSf1S4bReA1R8A2A2SeeRdSadSdbS1SdcR7A4S121R9RcRaA3A3RcS42G0S103RbS105RaR9A2A4A6F_;F_;F_;F_;F_;F_;FN;Fobjs;Fmd;Fms;Ftr;Ftp;Frho;FA;Fnd;FKc;") := ltac2:(tb__ "0|1|
Se0VAInv;VCST;VXGL;VALA;VHLV;S68Vrho0;VP0f;S3bS3aS2dS2dA2M0A1S3bS3aG0S2dA2A1Sc9VPA;ScaS95VPA;A1ScdVHCK;A10").
Let pcallK := pure_callJ AInv CST XGL ALA NF rho0 P0f [] [] BX0 PA ok.

Lemma JK_Kc : ltac2:(tb__ "0|0|
S77S3S38S6aQ40A1A1S38S56A1S57VJK;R5R4R3R2R1A5VKc;R3R2A2F_;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof. intros nd rho tp tr md (Ai & kc & _ & H & _). exact H. Qed.

Lemma JK_stable : ltac2:(tb__ "0|0|
S77S2eSa7S68R1A2S30S37S78R2R3A2S39A3S72S4aR3VJK;R4A1A3F_;F_;Fn;Fnd;").
Proof. intros nd n Hn Hb. apply (stableA_JA segs AInv CST XGL NF _ rho0 P0f [] [] BX0 PA HKc ALA n nd Hn Hb). Qed.

Lemma JK_tcons : ltac2:(tb__ "0|0|
S77S3S38S6aQ40A1A1S38S56A1S57VJK;R5R4R3R2R1A5Sa2VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof. intros nd rho tp tr md H. apply (HKtc tr md). exact (JK_Kc _ _ _ _ _ H). Qed.

Lemma okKK : ok_frameKA segs Kc ok.
Proof. split; [apply HOKJ | apply HOKP]; intros rho tp tr md H; exact (HKtc tr md H). Qed.

Lemma JK_okframe : ltac2:(tb__ "0|0|
S77S6fS4aVok;VJK;R1A1A3Fnd;").
Proof. intros nd. apply HOKJ. apply JK_tcons. Qed.

Lemma JK_run : ltac2:(tb__ "0|1|
S77S3eS38S2dA1S4cS38S4dA1M0S3S38S6aQ40A1A1Sa3S30S3cG0A1S50S4aR7R6R5S39A5S40G0R4A2A3S30S37SeS4bR6A1A1S3fA3S30S37Sa5S68S5S4bR7A1A1A2S39A3S30S37S78S5S4bR8A1A1RbA2S39A3S4dS3S74S4dR2RaA3S23S5S4bRcA1A1RaR2A3Sa0S4aVok;S6dS4aVJK;R10A1S52R4A1R3RaA5R9A4F_;F_;Frho';FL;Sa0S4aVok;S6dS4aVJK;RdA1RaR8R7A5R6A4F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fleaves;FA;Fcuts;Ffuel;Fnd;").
Proof.
  intros nd fuel cuts A leaves rho tp Q Hrun Hlen Hnf Hnb H. apply Pos.leb_le in Hnf.
  eapply (runA_tr segs ok fuel cuts A leaves (JK nd) rho tp Q Hrun Hlen (JK_okframe nd) (JK_stable nd _ Hnf Hnb) H).
Qed.

Lemma JK_entails : ltac2:(tb__ "0|1|
S4cS4cSedS77S77S3S38S6aQ40A1A1Sa1S30S37S55R8R7R6A3S39A3S30S37Sf0R7S68A2S39A3S30S37Sa5S68S5S4bRaA1A1A2S39A3S30S37S78S5S4bRbA1A1R8A2S39A3S30S37S10eRaS79R9A1S79R8A1A3S39A3S30S37S86RbS80RaA1S80R9A1A3S39A3S30S37S101S6S4bReA1A1S100RcS7fRaA1A2S7fRbA1A3S39A3S30S37S83S84RdS7cRbA1A2S7cRcA1A2S39A3S6dS4aVJK;RdA1M0R10RbRaR9A6S6dS4aG0R10SefRcRfA2RbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fndj;Fndi;Fs;FT;FL;").
Proof.
  intros L T s ndi ndj rho tp w. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0f [] [] BX0 PA HKc).
Qed.

Definition sp0_off (b : sv) : option Z := ltac2:(tb__ "0|d|
S0S3cS2dA1M0Lb;Vb;S2dS46S2dA1M1Lz;M2S2eS2eG0Li;M3R1S2eG1Lp;M4G4S40S2dZ0A2X2ex3Li;Sb0S0S0Sb0G0Lop;R3S0G0La;R2G2S2eG3R1G4G4S0G0Lb0;R2S2dS40S2dR1A2Ld;S2eG1Li0;Sb0S0S0G1Lb1;La0;M5Lop0;M6G6Sb1G5Lop0;M7G7S37S2fS0G1La0;Lw;Lsgn;M8S2eS0S2dG1Lk;M9Li0;Ll;X0x8X2ex3Li;G6G6G7G7G8S2eS0G9Li;Ll;MaX0x8G1G1G1G1G1G1G1G1G1Xb0xaLb0;La;Lop;Sb0S0S0G1Lb0;La;MbLop;Sb1GbLop;McGcS37S2fS0G1La;Lw;Lsgn;GaX0x8").

Definition argtop_factsb (facts : list sprop) : bool := ltac2:(tb__ "0|0|
S3dS73S2S9SaS106SbbS4Z20A1A2SbcA2A1Vfacts;A3S73S2S9SaSbcS4S61Z2Z2fA2A1A2A1Vfacts;A3A2").
Definition sp0_rangeb (facts : list sprop) (b : sv) (l h : sv) : bool := ltac2:(tb__ "0|b|
S3cS2dA1S37Lx;S8dVb;A1S2dS0S37Ll;Vl;S2dS0S37Lh;Vh;S2dS3dS3dS3dS3dS3dS3dS62S65S61Z2M0Z14A2A1S5fR3R2A2A2S62R2R1A2A2S45S62S5fR3R1A2M1Z0M2A2S3dS62G1Z20A2S97Vfacts;A1A2A2A2S62S65S61G0Z28A2M3A1M4R2A2A2S66R1G3A2A2S62G4R3A2A2S62R3G2A2A2Lhi;S2eS3fLi;M5Sb0S0S0S3fLb0;La;M6Lop;M7G7Sb1G6Lop;M8G8S37S2fS0S3fLa;Lw;Lsgn;M9S2eS0S2dS3fLk;Li;Ll0;MaX0x8Llo;G5G7G7G8G8G9GaX0x8Ld;S3fX3cx2").
Lemma argtop_sound : ltac2:(tb__ "0|4|
S3S38S2A1SacS2SdR2A1R1A3S30S37S97R2A1S39A3S31S60Z7fff80000000S6bQ40M0SbR4P1M1A2A2M2A2S60G2S64S61Z2Z2fA2M3Ze0A2A2A2S60S5fS6bG0SbR5G1A2A2Z20A2G3A2F_;F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H Hsp. unfold argtop_factsb in H. apply andb_prop in H as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as A1. pose proof (holds_mem _ _ _ HF H2) as A2. cbn [holds] in A1, A2.
  unfold vA1, sp0, add in A1, A2. cbn [eval] in A1, A2. rewrite add_val, !lit_unsigned in A1. rewrite lit_unsigned in A2.
  change (32 mod 2 ^ 64) with 32 in A1. change (2 ^ 47 mod 2 ^ 64) with (2 ^ 47) in A2.
  rewrite Z.mod_small in A1 by lia. lia.
Qed.
Definition cst_rangeb (b : sv) (l h : sv) : bool := ltac2:(tb__ "0|7|
S0S37Lb;Vb;S2dS2dS37Lz;R1S0S37Ll;Vl;S2dS0S37Lh;Vh;S2dS3dS3dS3dS3dS62Z0R2A2S62R2R1A2A2S66R1S61Z2Z3eA2A2A2S113SccR2S64R1R2A2A3A2S45S62R1Sd5A2S62S5fSd5Z4A2R2A2A2A2Lhi;S2eS3fLi;M0Sb0S0S0S3fLb0;La;M1Lop;M2G2Sb1G1Lop;M3G3S37S2fS0S3fLa;Lw;Lsgn;M4S2eS0S2dS3fLk;Li;Ll0;M5X0x8Llo;G0G2G2G3G3G4G5X0x8S2eS3fLp;M6G6X2dx3Lz;G0G2G2G3G3G4G5X0x8").

Definition arg1b (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|2|
S3dS3dS3dS3dS3dS3dScS1dVo;A1SbcA2ScS1fVo;A1S4Z0A1A2A2ScS1eVo;A1Sc5A2A2S73S2S9SaS106SbbS4Z20A1A2SbcA2A1Vfacts;A3A2S73S2S9SaSbcS4S61Z2M0Z2fA2A1M1A2A1Vfacts;A3A2S73S2S9SaS106SbcSc5A2G1A2A1Vfacts;A3A2S73S2S9SaSc5S4S61G0Z16A2A1A2A1Vfacts;A3A2").
Definition drv_objb (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|3|
S45S45S9cS1dVo;A1M0S1fVo;A1M1S1eVo;A1M2A3S9fVfacts;G0G1G2A4A2S96Vfacts;Vo;A2A2").

Definition robjs_checkD (facts : list sprop) (tv : list (sv * sv)) (skip : option nat) (R : list sobj) : bool := ltac2:(tb__ "0|0|
S115Vfacts;Vtv;Vskip;S90Vfacts;A1VR;A5").

Lemma arg1b_sound : ltac2:(tb__ "0|5|
S3S38S2A1S1S2dSacS2SdR4A1R3A3S31S60Z7fff80000000S6bQ40M0SbR5P1M1A2A2M2A2S60G2S64S61Z2Z2fA2M3Ze0A2A2A2S30S37S96R5R4A2S39A3S31S60S44S2dS2dS18R7R5A2M4A3R4A2S63R4S47S2dS2dG4A3A2A2S31S60S5fS6bG0SbR8G1A2A2Z20A2R5A2S63R5G3A2A2F_;F_;F_;F_;Fa;Fo;Ffacts;Frho;").
Proof.
  intros rho facts o a HF Hsp H Hr. unfold arg1b in H.
  apply andb_prop in H as [H F3]. apply andb_prop in H as [H F2]. apply andb_prop in H as [H F4]. apply andb_prop in H as [H F1].
  apply andb_prop in H as [H E3]. apply andb_prop in H as [E1 E2].
  apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
  pose proof (holds_mem _ _ _ HF F1) as A1. pose proof (holds_mem _ _ _ HF F2) as A2. pose proof (holds_mem _ _ _ HF F3) as A3.
  pose proof (holds_mem _ _ _ HF F4) as A4.
  cbn [holds] in A1, A2, A3, A4. unfold vA1, vL3, add, sp0 in *. cbn [eval] in A1, A2, A3, A4.
  rewrite add_val, ?lit_unsigned in A1. rewrite ?lit_unsigned in A3. rewrite ?lit_unsigned in A4. rewrite !add_val, !lit_unsigned in A2.
  change (32 mod 2 ^ 64) with 32 in A1. rewrite Z.mod_small in A1 by lia. change (2 ^ 22 mod 2 ^ 64) with (2 ^ 22) in A3.
  change (2 ^ 47 mod 2 ^ 64) with (2 ^ 47) in A2, A4.
  pose proof (urange (rw rho 8%positive)) as R8. pose proof (urange (rw rho 10%positive)) as R10.
  rewrite Z.mod_small in A2 by lia.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite E1, E2, E3 in Hr. cbn [fst snd eval] in Hr.
  rewrite soff_lit_small in Hr by lia. rewrite soff_snorm in Hr. unfold U in Hr. cbn [eval] in Hr. rewrite snorm_small in Hr by lia.
  lia.
Qed.

Definition drv_xrb (r : sv * sv) : bool := ltac2:(tb__ "0|19|
S0S37Lx;M0S44S0S0Vr;A3S2dG0S47S0S0Vr;A3M1S2dS3dS3dS3dS3dS62Z0M2R2A2M3S62G2R1A2A2S66S5fR2R1A2M4S61Z2M5Z3eA2A2A2S113SccR2R1A3A2S45S62G4Sd5A2S62S5fSd5Z4A2R2A2A2A2Ll;S2eS3fLi;M6Sb0S0S0S3fLb0;M7La;M8Lop;M9G9Sb1G8Lop;MaGaS37S2fS0S3fLa;Lw;Lsgn;MbS2eS0S2dS3fLk;McLi;Ll;MdX0x8Lb;S2eG0G1S2dS3cS2dA1S37Lx;MeS8dS1cR2A1A1S2dS3dS3dS62S65S61G5Z14A2A1R1A2G3A2S62S5fR1R2A2G2A2A2Ld;MfS3fX3cx2Ll;S2eS3fLi0;M10G9G9GaGaGbS2eS0GcLi0;Ll;X0x8Li;Sb0S0S0G0G1S2dGeS8dS1bR4R3R2A3A1GfS3fX3cx2Ll;G6Sb0S0S0S3fLb1;La0;M11Lop0;M12G12Sb1G11Lop0;M13G13S37S2fS0S3fLa0;M14Lw;Lsgn;M15GdX0x8Lb0;La;Lop;Sb0S0S0G0G1S2dGeS8dS25R4R3R2A3A1GfS3fX3cx2Ll;G6G12G12G13G13G15GdX0x8Lb0;La;Lop;Sb1S0S0G0G1S2dGeS8dS28R4R3R2A3A1GfS3fX3cx2Ll;G6G12G12G13G13G15GdX0x8Lb0;La;Lop;Sb1S0S0G0G1S2dGeS8dS29R4R3R2A3A1GfS3fX3cx2Ll;G6G12G12G13G13G15GdX0x8Lb0;La;Lop;S37S2fS0G0G1S2dGeS8dS26R4R3R2A3A1GfS3fX3cx2Ll;G6Sb0S0G7La0;M16Lop;M17G17Sb1G16Lop;M18G18S37S2fG14Lw0;Lsgn0;GdX0x8La;Lw;Lsgn;S2eS0S2dG0G1S2dGeS8dS27R4R3R2A3A1GfS3fX3cx2Ll;G10G9G9GaGaGbS2eS0S2dS3fLk0;Li0;Ll;X0x8Lk;Li;Ll0;X0x8").

Definition sp0_factsb (facts : list sprop) : bool := ltac2:(tb__ "0|2|
S3dS3dS3dS73S2S9SaS4Z7fff80000000A1SbbA2A1Vfacts;A3S73S2S9SaSbbS4S64S61Z2Z2fA2Ze0A2A1A2A1Vfacts;A3A2S73S2S9SaS1bSb2S1cP1A1S4N800000A1A3M0S1cP1eA1M1A2A1Vfacts;A3A2S73S2S9SaG1G0A2A1Vfacts;A3A2").

Lemma sp0_facts_sound : ltac2:(tb__ "0|2|
S3S38S2A1SacS2SdR2A1R1A3S30S37S8cR2A1S39A3S31S31S60Z7fff80000000S6bQ40M0SbR4P1A2A2M1A2S60G1S64S61Z2Z2fA2Ze0A2A2A2S30S2dS6bG0SbR4P1eA2A2S64G1Z800000A2A3A2F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H. unfold sp0_factsb in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as A1. pose proof (holds_mem _ _ _ HF H2) as A2.
  pose proof (holds_mem _ _ _ HF H3) as A3. pose proof (holds_mem _ _ _ HF H4) as A4.
  cbn [holds] in A1, A2, A3, A4. unfold sp0 in A1, A2. cbn [eval] in A1, A2, A3, A4. rewrite lit_unsigned in A1, A2.
  rewrite Z.mod_small in A1 by lia. rewrite Z.mod_small in A2 by lia.
  rewrite add_val, lit_unsigned in A3, A4. pose proof (urange (rw rho 1%positive)) as R1.
  change ((-8388608) mod 2 ^ 64) with (2 ^ 64 - 8388608) in A3, A4.
  replace ((bv_unsigned (rw rho 1%positive) + (2 ^ 64 - 8388608)) mod 2 ^ 64) with (bv_unsigned (rw rho 1%positive) - 8388608) in A3, A4
    by (replace (bv_unsigned (rw rho 1%positive) + (2 ^ 64 - 8388608)) with ((bv_unsigned (rw rho 1%positive) - 8388608) + 1 * 2 ^ 64) by lia;
        rewrite Z.mod_add by lia; symmetry; apply Z.mod_small; lia).
  lia.
Qed.

Lemma sp0_off_sound : ltac2:(tb__ "0|2|
S3S0S2dS30S3cS2dA1S8dR2A1S40S2dR1A2A3S31S60S65S61Z2Z28A2A1R2A2S60R2Z0A2A2S60Z7fff80000000S6bQ40M0SbR5P1M1A2A2A2S30S2dS6bG0S10R6R5A2A2S5fS6bG0SbR6G1A2A2R4A2A3F_;F_;F_;Fd;Fb;Frho;").
Proof.
  intros rho b d H Hd Hsp. unfold sp0_off in H.
  destruct b as [z|v|op a1 b2|op a1 b2|op a1 b2|op a1 b2|sg w a1|l i k]; try discriminate.
  - destruct v; try discriminate. injection H as <-. cbn [eval]. lia.
  - destruct op; try discriminate. destruct a1 as [z|v|op a1' b2'|op a1' b2'|op a1' b2'|op a1' b2'|sg w a1'|l i k]; try discriminate.
    destruct v; try discriminate.
    destruct b2 as [d'|v'|op b1' b3'|op b1' b3'|op b1' b3'|op b1' b3'|sg w b1'|l i k]; try discriminate. injection H as <-.
    pose proof (urange (rw rho 1%positive)). rewrite U_add_lit; [cbn [eval]; reflexivity | lia | cbn [eval]; lia].
Qed.

Lemma drv_objb_core : ltac2:(tb__ "0|1|
S3S38S2A1S1S2dSacS2SdR4A1R3A3S30S37S8cR4A1S39A3S30S37S90R5R4A2S39A3S31S60S44S2dS2dS18R7R5A2M0A3R4A2S63R4S47S2dS2dG0A3A2A2S33S31S60S6bQ40SbR8P1eA2A2R5A2S63R5S61Z2Z2fA2A2A2S31Sd4VCST;R5A2S35Se9R5A1A1A2A2F_;F_;F_;F_;Fa;Fo;Ffacts;Frho;").
Proof using HCSTdrv.
  intros rho facts o a HF Hspf H Hr. pose proof (sp0_facts_sound rho facts HF Hspf) as [Hsp H30].
  unfold drv_objb in H. apply orb_prop in H as [H|H]; [|left; pose proof (arg1b_sound rho facts o a HF Hsp H Hr); lia].
  apply orb_prop in H as [H|H].
  - unfold cst_rangeb in H. destruct (ob_base o) as [z|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?] eqn:EB; try discriminate. destruct z; try discriminate.
    destruct (ob_lo o) as [lo|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?] eqn:EL; try discriminate.
    destruct (ob_hi o) as [hi|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?] eqn:EH; try discriminate.
    apply andb_prop in H as [H HE]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
    unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite EB, EL, EH in Hr. cbn [ob_base ob_lo ob_hi fst snd eval] in Hr.
    rewrite lit_unsigned, (Z.mod_small 0) in Hr by lia. rewrite !soff_lit_small in Hr by lia.
    right. split; [apply HCSTdrv; eapply lit_in_ranges_sound; [exact H4|]; lia|].
    unfold errno_addrA. apply orb_prop in HE as [HE|HE]; apply Z.leb_le in HE; lia.
  - unfold sp0_rangeb in H. destruct (sp0_off (ob_base o)) as [d|] eqn:ED; [|discriminate].
    destruct (ob_lo o) as [lo|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?] eqn:EL; try discriminate.
    destruct (ob_hi o) as [hi|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?] eqn:EH; try discriminate.
    apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H4. apply Z.ltb_lt in H5. apply Z.leb_le in H6. apply Z.leb_le in H7.
    assert (H3' : d + hi <= 0 \/ (d + hi <= 32 /\ bv_unsigned (rw rho 1%positive) + 32 <= 2 ^ 47)).
    { apply orb_prop in H3 as [H3|H3]; [left; apply Z.leb_le in H3; exact H3|].
      apply andb_prop in H3 as [H3 HT]. apply Z.leb_le in H3. right. split; [exact H3 | exact (argtop_sound rho facts HF HT Hsp)]. }
    left. unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite EL, EH in Hr. cbn [fst snd] in Hr.
    rewrite !soff_lit_small in Hr by lia. rewrite (sp0_off_sound rho (ob_base o) d ED ltac:(lia) ltac:(lia)) in Hr.
    lia.
Qed.

Lemma drv_xrb_core : ltac2:(tb__ "0|1|
S3S38S2A1S3aS0S0A2S2dSacS2SdR4A1R3A3S30S37S8cR4A1S39A3S30S37S8eR4A1S39A3S31S60SfbR7S44S0S0R5A3A2M0R4A2S63R4S5fG0SfbR7S47S0S0R5A3A2A2A2A2S33S31S60S6bQ40SbR8P1eA2A2R5A2S63R5S61Z2Z2fA2A2A2S31Sd4VCST;R5A2S35Se9R5A1A1A2A2F_;F_;F_;F_;Fa;Fr;Ffacts;Frho;").
Proof using HCSTdrv.
  intros rho facts [b l] a HF Hspf H Hr. pose proof (sp0_facts_sound rho facts HF Hspf) as [Hsp H30].
  unfold drv_xrb in H. cbn [fst snd] in H, Hr. unfold uval in Hr.
  destruct l as [l|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?];
    [| destruct b; discriminate | destruct b; discriminate | destruct b; discriminate | destruct b; discriminate
     | destruct b; discriminate | destruct b; discriminate | destruct b; discriminate].
  replace (bv_unsigned (eval rho (SLit l))) with (l mod 2 ^ 64) in Hr by (cbn [eval]; rewrite lit_unsigned; reflexivity).
  destruct b as [bz|v|op a1 b2|op a1 b2|op a1 b2|op a1 b2|sg w a1|li i k]; try discriminate.
  - apply andb_prop in H as [H HE]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. rewrite Z.mod_small in Hr by lia.
    cbn [eval] in Hr. rewrite lit_unsigned, Z.mod_small in Hr by lia.
    right. split; [apply HCSTdrv; eapply lit_in_ranges_sound; [exact H4 | lia]|].
    unfold errno_addrA. apply orb_prop in HE as [HE|HE]; apply Z.leb_le in HE; lia.
  - cbn [sp0_off] in H. destruct v; try discriminate.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    rewrite Z.mod_small in Hr by lia. cbn [eval] in Hr. left. lia.
  - destruct (sp0_off (SAlu op a1 b2)) as [d|] eqn:ED; [|discriminate].
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    rewrite Z.mod_small in Hr by lia. rewrite (sp0_off_sound rho _ d ED ltac:(lia) ltac:(lia)) in Hr. left. lia.
Qed.

Lemma drv_objb_sound : ltac2:(tb__ "0|1|
Sa8S3cS2dA1S3S38S2A1S1S2dSacS2SdR4A1R3A3S30S37S8cR4A1S39A3S108R6SaaSa9R8A1A1A2S30S37S90R6R5A2S39A3S31S60S44S2dS2dS18R8R6A2M0A3R5A2S63R5S47S2dS2dG0A3A2A2S112VCST;RbRaR6A4F_;F_;F_;F_;F_;Fa;Fo;Ffacts;Frho;Fx;FAi;").
Proof using HCSTdrv.
  intros Ai x rho facts o a HF Hs [HT _] H Hr. change (rw rho V_TOP) with (rw rho 30%positive) in HT.
  destruct (drv_objb_core rho facts o a HF Hs H Hr) as [X|X]; [left; rewrite <- HT; exact X | right; left; exact X].
Qed.
Lemma drv_xrb_sound : ltac2:(tb__ "0|1|
Sa8S3cS2dA1S3S38S2A1S3aS0S0A2S2dSacS2SdR4A1R3A3S30S37S8cR4A1S39A3S108R6SaaSa9R8A1A1A2S30S37S8eR5A1S39A3S31S60SfbR8S44S0S0R6A3A2M0R5A2S63R5S5fG0SfbR8S47S0S0R6A3A2A2A2A2S33S112VCST;RbRaR6A4Sd4VXGL;R6A2A2F_;F_;F_;F_;F_;Fa;Fr;Ffacts;Frho;Fx;FAi;").
Proof using HCSTdrv.
  intros Ai x rho facts r a HF Hs [HT _] H Hr. change (rw rho V_TOP) with (rw rho 30%positive) in HT.
  left. destruct (drv_xrb_core rho facts r a HF Hs H Hr) as [X|X]; [left; rewrite <- HT; exact X | right; left; exact X].
Qed.

Definition xrs_checkD (facts : list sprop) (tv : list (sv * sv)) (skip : option nat) (objs : list sobj)
           (extra : sv * sv -> bool) (X : list (sv * sv)) : bool := ltac2:(tb__ "0|2|
S75S3aS0S0A2M0G0S37S37L_;M1S114Vtv;Vskip;R1A3S39G1S73S1S117Vfacts;R1A2Vobjs;A3S39Vextra;R1A1X37x2X37x2Lr;VX;A3").
Lemma xrs_checkD_A : ltac2:(tb__ "0|2|
S38S2A1S38S3aS0S0A2M0A1M1S3cS3eA1S38S1A1G0S37F_;G1S30S37S8fR6R5R4R3R2R1A6S39A3S30S37S118VXGL;R7R6R5R4R3R2A7S39A3F_;FX;Fextra;Fobjs;Fskip;Ftv;Ffacts;").
Proof.
  intros facts tv skip objs extra X H. unfold xrs_checkD in H. rewrite xrs_checkA_ref_eq. unfold xrs_checkA_ref.
  apply forallb_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) H r Hr) as Hc. cbn beta in Hc.
  destruct (xr_lit_in XGL r); [reflexivity | exact Hc].
Qed.

Lemma site_ok_drv : ltac2:(tb__ "0|9|
S77S4cSedS38S1A1S3S3cS3eA1M0S3cS2dA1M1Sa8Sf4OF_;F_;S30S37S8cS6S4bR7A1A1A1S39A3S30S37S91S6S4bR8A1A1S79R9A1R4R6A4S39A3S30S37S8fS6S4bR9A1M2A1S79RaA1R5S8G2A1S8eS4eR9A1A6S39A3Sa8SacS2SdR8A1S6S4bRbA1A1A3S81S3bS3aS2dS2dA2M3A1M4R2R9S79RdA1A4S10aRaS79ReA1A2G0OLskip;RaS3eG1OLx;M5RaS2dS34S3aS0S0A2M6G6S31S30S3cG6A1S76G6S79R12A1M7R3A3S40G6R1A2A3S31S10dReR1A2S30S2dS44S2dS2dS109ReR1A2A3R2A3A2A2Lt;A2Lxb;S32X3cx2Li;G5R9S2dS32Lz;S36X3cx2X3cx2F_;F_;F_;FAi;Sa8Sf4SacS2SdRaA1S6S4bRdA1A1A3VP0f;Vrho0;A1S123S68Vrho0;RcA3S81G4R5RdS79R11A1A4S10fReG7A2S10aRfS79R13A1A2S34S3S3S34S38S6aQ40A1A1M8G8S34S57S57VAInv;RbR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2ReR9R8A2F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S116VAInv;VCST;VXGL;S68Vrho0;VP0f;G4S3bS3aG3S2dA2A1RcRbRaR9RdR7R6AfF_;F_;F_;F_;F_;Fextra;Fx;Fskip;Frho;FR;Fs;FCl;Fnd;").
Proof using ALA HCSTdrv.
  intros nd Cl s R rho skip x extra Hspf Hro Hxr Hsx Hex Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HTPA HTok.
  split; [|split].
  - eapply (robjs_checkA_sound segs AInv CST ALA [] Ai rho _ (nd_tv nd) skip (drv_objb (ss_facts (ax_S Cl))) R x rho1 tp1 md1 HM HF HN HD HZ HTok Hro).
    + intros o a Ho He Hr. eapply drv_objb_sound; eauto.
    + exact (Hsx Ai HF HN HZ).
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA [] Ai rho _ (nd_tv nd) skip (ss_objs (ax_S Cl)) drv_xrb (ax_X Cl) x rho1 tp1 md1 HM HF HN HD HZ HTok (xrs_checkD_A _ _ _ _ _ _ Hxr)).
    + intros r a Hr He Ha. eapply drv_xrb_sound; eauto.
    + exact (Hsx Ai HF HN HZ).
  - apply (Hex Ai ms HF HP0 Hav HN HD HZ). exists rho1, tp1, md1. exact HM.
Qed.

Definition kept_nzb (facts : list sprop) (kept : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S75S3aS0S0A2M0G0S73S2S9SaS4Z1000A1S44S0S0R1A3A2A1Vfacts;A3Lt;Vkept;A3").

Lemma kept_in_FBx : ltac2:(tb__ "0|4|
S3S3S38S2A1S38S3aS0S0A2M0A1G0S2dSacS2SdR5A1R4A3S30S37S92R5R4A2S39A3S74G0R4R5A3S31S60S44S2dS2dS109R8R5A2M1A3M2R4A2S63R4S5fG2S47S2dS2dG1A3A2A2A2S127VCST;RaS10bS3bS3aS2dS2dA2M3A1R9R7A3S126S3bS3aG3S2dA2A1R9S3bS3aS3aS0S2dA2S0A2A1A3R5A5F_;F_;F_;F_;Fa;Ft;Fkept;Ffacts;Frho;Fr0;").
Proof.
  intros r0 rho facts kept t a HF Hk Hin Ha. right; right; left. exists (fst (tvv rho t)), (snd (tvv rho t)). split; [|exact Ha].
  unfold FBx. cbn [app]. apply in_map_iff. exists t. rewrite <- surjective_pairing. split; [reflexivity|].
  apply filter_In. split; [exact Hin|]. apply (proj2 (tnzb_true rho t)).
  pose proof (holds_mem _ _ _ HF (proj1 (forallb_forall _ _) Hk t Hin)) as X. cbn [holds] in X.
  rewrite U_lit, <- M64v_eq, Z.mod_small in X by lia. unfold tnz. unfold tvv in Ha |- *. cbn [fst] in Ha, X |- *. lia.
Qed.

Lemma T0_of_site : ltac2:(tb__ "0|0|
S3S3Sa8S82R3R1A2S108R3SaaSa9R2A1A1A2S30S2dS107R5A1S6bQ40SbR4P1eA2A2A3F_;F_;FAi;Frho;Fr0;").
Proof. intros r0 rho Ai HTPA [HT _]. rewrite <- (TPA_top _ Ai HTPA). symmetry. exact HT. Qed.

Lemma robjs_okF_drv : ltac2:(tb__ "0|1|
S3S38S2A1S38S3aS0S0A2A1S38S1A1SacS2SdR4A1R3A3S30S37S8cR4A1S39A3S30S2dS107Vrho0;A1S6bQ40SbR6P1eA2A2A3S30S37S92R6R5A2S39A3S30S37S75S1S1S45S90R8R1A2S10cR7S46S3eA1R1A3A2Lo;R5A3S39A3S128VCST;Vrho0;S3bS3aS2dS2dA2M0A1S3bS3aG0S2dA2A1R9R7S3bS3aS3aS0S2dA2S0A2A1R6A8F_;F_;F_;F_;F_;FR;Fkept;Ffacts;Frho;").
Proof using HCSTdrv.
  intros rho facts kept R HF Hspf HT30 Hk Hchk o a Ho Hr.
  pose proof (proj1 (forallb_forall _ _) Hchk o Ho) as Hc. apply orb_prop in Hc as [Hc|Hc].
  - destruct (drv_objb_core rho facts o a HF Hspf Hc Hr) as [X|X]; [left; rewrite HT30; exact X | right; left; exact X].
  - destruct (robj_tracked_sound kept None o Hc) as (j & t & Hj & _ & Hb & Hl & Hh).
    destruct (tracked_range rho o t a Hb Hl Hh Hr) as [Ha _].
    eapply kept_in_FBx; [exact HF | exact Hk | eapply nth_error_In; exact Hj | exact Ha].
Qed.

Lemma xrs_okF_drv : ltac2:(tb__ "0|3|
S3S38S2A1S38S3aS0S0A2M0A1M1G1SacS2SdR4A1R3A3S30S37S8cR4A1S39A3S30S2dS107Vrho0;A1S6bQ40SbR6P1eA2A2A3S30S37S92R6R5A2S39A3S30S37S75G0G0S45S8eR1A1S114R7S46S3eA1R1A3A2Lr;R5A3S39A3S129VCST;VXGL;Vrho0;S3bS3aS2dS2dA2M2A1S3bS3aG2S2dA2A1R9R7S3bS3aS3aS0S2dA2S0A2A1R6A9F_;F_;F_;F_;F_;FX;Fkept;Ffacts;Frho;").
Proof using HCSTdrv.
  intros rho facts kept X HF Hspf HT30 Hk Hchk r a Hr Ha.
  pose proof (proj1 (forallb_forall _ _) Hchk r Hr) as Hc. apply orb_prop in Hc as [Hc|Hc].
  - left. destruct (drv_xrb_core rho facts r a HF Hspf Hc Ha) as [Y|Y]; [left; rewrite HT30; exact Y | right; left; exact Y].
  - left. unfold xr_tracked in Hc. destruct (robj_tracked_sound kept None _ Hc) as (j & t & Hj & _ & Hb & Hl & Hh). cbn [ob_base ob_lo ob_hi] in Hb, Hl, Hh.
    eapply kept_in_FBx; [exact HF | exact Hk | eapply nth_error_In; exact Hj |].
    destruct r as [b l]. cbn [fst snd] in Hb, Hh, Ha. subst. unfold tvv. destruct t as [tb tl]. cbn [fst snd] in Ha |- *. unfold uval in Ha. exact Ha.
Qed.

Lemma In_dropX : ltac2:(tb__ "0|3|
S3aS0S0A2M0S37F_;S38G0A1M1G0S74G0R1S11cG0G1S11eG0A1G0S11bR4R1A1M2A1Lx;G0S11dG2A1Lx;R2A6A3S74G0R2R3A3F_;Fr;FX;Ff;").
Proof.
  intros f X. induction X as [|x l IH]; intros r Hr; cbn in Hr; [exact Hr|].
  destruct (f x); cbn in Hr; [destruct Hr as [<-|Hr]; [left; reflexivity | right; apply IH; exact Hr] | right; apply IH; exact Hr].
Qed.

Lemma wcanon_nil : wcanon [].
Proof. exists 0%nat. split; [apply le_0_n | reflexivity]. Qed.

Lemma is_prefix_app_mono {A} : ltac2:(tb__ "0|1|
S38VA;A1M0G0G0S104VA;R2R1A3S104VA;S43VA;R4R3A3S43VA;R4R2A3A3F_;Fl2;Fl1;Fa;").
Proof. induction a; cbn; auto. Qed.
Lemma is_prefix_firstn {A} : ltac2:(tb__ "0|1|
S3eS38VA;A1M0G0S104VA;SaeVA;R3R2A3S43VA;R2R1A3A3Fr;Fl;Fk;").
Proof. induction k as [|k IH]; intros [|x l] r; cbn; auto. Qed.
Lemma firstn_map' {A B} : ltac2:(tb__ "0|0|
VA;VB;F_;S3eS38VA;A1S30S38VB;A1SaeVB;R2SadVA;VB;R3R1A4A3SadVA;VB;R3SaeVA;R2R1A3A4A3Fl;Fk;Ff;").
Proof. intros f k. induction k as [|k IH]; intros [|x l]; cbn; rewrite ?IH; reflexivity. Qed.

Section ExitCall.
Variable ph : bool.
Variable ndX : ndesc.
Variables n c : Z.
Variable CX : axst.
Variable s : wsub.
Variable R : list sobj.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S30S37Sa5S68S5S4bVCX;A1A1A2S39A3").
Hypothesis Hnb : ltac2:(tb__ "0|0|
S30S37S78S5S4bVCX;A1A1VndX;A2S39A3").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S30S3cS38S1A1M0A1Se3VCX;S8aVph;Vn;Vc;A3Vs;A3S40G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S30S37Se4VCX;S8aVph;Vn;Vc;A3Vs;VR;S3bS4cA1A5S39A3").
Hypothesis Hfb : ltac2:(tb__ "0|1|
S30S37S75S2S19S5S4bVCX;A1M0A1A1S6G0A1A3S39A3").
Hypothesis Hsupp : ltac2:(tb__ "0|0|
S74S3aS2dS2dA2S42S2dS2dVn;Vc;A4S8bVph;A1A3").

Hypothesis HSPEC : ltac2:(tb__ "0|0|
S38S56A1S57VKc;R2R1A2VSpec;S43S56R3S43S56SadS6aQ8A1S56S5bSb3A1S88Vn;A1A4S41S56S59S6cQ40Vc;A2S5eR2A1A2S3bS56A1A3A3A3A1F_;Fmd;Ftr;").
Hypothesis HKfd1 : ltac2:(tb__ "0|0|
S38S56A1S57VKc;R2R1A2S30S3cS58A1S5cS5dR2A1Sb3A2S40S58S5aSb3A1A2A3F_;Fmd;Ftr;").

Lemma X_exit_call : ltac2:(tb__ "0|0|
S3S38S6aQ40A1A1Sa0S4aVok;S6dS4aVJK;VndX;A1VCX;R2R1A5Sa1S32L_;A4Ftp;Frho;").
Proof.
  intros rho tp. pose proof Hnx as Hnx'. apply Pos.leb_le in Hnx'.
  set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) => JK ndX rho t tr md).
  assert (JpK : forall r t tr md, Jp r t tr md -> Kc tr md) by (intros r t tr md HJ; exact (JK_Kc _ _ _ _ _ HJ)).
  assert (TC : forall k, ok_frameA segs ok (Kw Jp n k) /\ ok_pframeA segs ok (Kw Jp n k)).
  { intros k.
    assert (T : forall r t tr md, Kw Jp n k r t tr md -> tcons Spec tr).
    { intros r t tr md (tr0 & HJ & ->). pose proof (JpK _ _ _ _ HJ) as Hk.
      exists (tr0 ++ map (WriteEv ch1) (PEND n) ++ [ExitEv (Z_to_bv 64 c) (m_fs md)]). split; [exact (HSPEC tr0 md Hk)|].
      apply is_prefix_app_mono. unfold EVS.
      eapply is_prefix_trans; [| apply is_prefix_app]. clear. generalize (PEND n) as l. intros l.
      induction k as [|k IH] in l |- *; [apply is_prefix_nil|]. destruct l; cbn; [exact I|]. split; [reflexivity | apply IH]. }
    split; [apply HOKJ; exact T | apply HOKP; exact T]. }
  apply (pcallK Kc Kc CX (Pre_exitP ph n c) s R [] rho tp ndX
           Jp (fun r t tr md => False) (fun _ => False) HKc).
  -
    intros rho1 tp1. eapply triple_conseq; [intros w' Hw'; exact Hw' | | apply (exit_sumP ok Jp Spec n c) with (ph := ph)].
    + intros w' Hf. destruct Hf.
    +   intros r r' t tr md md' Hag Hme HJ. unfold Jp in HJ |- *.
      destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF Kc rho0 P0f [] [] BX0 PA HKc ALA (ss_next (ax_S CX)) ndX Ai kc rho rho t tr md md');
        [exact Hnx' | exact Hnb | apply agree_below_refl | exact Hme | exact HJi].
    + intros r t tr md HJ. apply (HKfd1 tr md). exact (JpK _ _ _ _ HJ).
    + intros k. exact (proj1 (TC k)).
    + intros k. exact (proj2 (TC k)).
    + exact Hokh.
    + intros r t tr md HJ. exact (HSPEC tr md (JpK _ _ _ _ HJ)).
    + exact Hsupp.
  - exact Hfr.
  - exact Hcc.
  - exact Hnx.
  - exact Hnb.
  - exact Hfb.
  - intros tr ms md Hsm HJ. exact HJ.
  - intros rhoL tr' md' Hf. destruct Hf.
  - intros L rho' Hin. destruct Hin.
Qed.
End ExitCall.

Section ExitHandoff.
Variable ndX : ndesc.
Variables n c : Z.
Variable E : axst.

Variables S1 S4 S5 S6 : sstate.
Variable idxs : list nat.
Variable R : list sobj.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S30S37Sa5S68S5S4bVE;A1A1A2S39A3").
Hypothesis Hnb : ltac2:(tb__ "0|0|
S30S37S78S5S4bVE;A1A1VndX;A2S39A3").
Hypothesis HbE : ltac2:(tb__ "0|0|
S30S0S4fVE;A1S4S119A1A3").

Variable iw : nat.
Hypothesis H1n : ltac2:(tb__ "0|0|
S30S3cS1A1S76S1S8S4bVE;A1A1Viw;A3S40S1S17Sc3S4S65SbfA1A1S4Z0A1S3bSfA1S1aA5A2A3").
Variable S0 : sstate.
Hypothesis H1e : ltac2:(tb__ "0|0|
S30S7S102S4bVE;A1Viw;Sc7A3VS0;A3").
Hypothesis H1s : ltac2:(tb__ "0|0|
S30S37Sf5S4bVE;A1VS0;A2S39A3").

Variable ie : nat.
Let S0a : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|0|
Sd2VS0;Vie;S5fS87Z8cA2Z4S64S61Z2Z20A2Z1A2A5").
Let S0b : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|0|
Sd2VS0a;Vie;S5fS87Z10A2Z8Z0A5").
Let S0c : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
Sd2VS0b;Vie;S5fS87Z8M0A2G0Z0A5").
Let S0d : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|0|
Sd2VS0c;Vie;S5fS87Z38A2Z8Z0A5").
Hypothesis H1i : ltac2:(tb__ "0|2|
S31S30S37Sd3S4aVS0;Vie;S5fS87Z8cA2Z4S64S61Z2Z20A2Z1A2A6S39A3S31S30S37Sd3S4aVS0a;Vie;S5fS87Z10A2Z8M0Z0M1A6S39A3S31S30S37Sd3S4aVS0b;Vie;S5fS87G0A2G0G1A6S39A3S31S30S37Sd3S4aVS0c;Vie;S5fS87Z38A2G0G1A6S39A3S30S37Sd3S4aVS0d;Vie;S5fS87Z28A2G0G1A6S39A3A2A2A2A2").
Hypothesis H1j : ltac2:(tb__ "0|0|
S30S7Sd2VS0d;Vie;S5fS87Z28A2Z8Z0A5VS1;A3").

Hypothesis H2 : ltac2:(tb__ "0|0|
S30S37SfaS48S1S8VS1;A1A2Vidxs;A2S39A3").
Hypothesis H3 : ltac2:(tb__ "0|0|
S30S3cS7A1Sf8Sf1VS1;Sf7S8VS1;A1Vidxs;A2A2U0A2S40S7VS4;A2A3").
Hypothesis H4 : ltac2:(tb__ "0|0|
S30S3cS7A1Sf9VS4;U0S4N430A1A3S40S7VS5;A2A3").

Definition S5c : sstate := ltac2:(tb__ "0|0|
S11S14VS5;A1S15VS5;A1S13VS5;A1S12VS5;A1S16VS5;A1S43S1S8VS5;A1SadSdbS1SdcSc1A4A3S6VS5;A1S5VS5;A1SeVS5;A1A9").
Hypothesis H5n : ltac2:(tb__ "0|0|
S30S2eS5VS5;A1S5S4bVE;A1A1A3").
Hypothesis H5w : swf S5c = true.
Hypothesis H5c : ltac2:(tb__ "0|0|
S30S37SdeS6VS5;A1S8VS5;A1S3bS3aS0S0A2A1ScaScbS79VndX;A1Sc1A7S39A3").
Hypothesis H6e : ltac2:(tb__ "0|1|
S30S7S11S14Sd0A1S69S15Sd0A1S41S3aS3eS0A2M0S42S3eS0U4S4SdaA1A4S3bG0A1A3A2S13Sd0A1S12Sd0A1S16Sd0A1S8Sd0A1S6Sd0A1S5Sd0A1SeSd0A1A9VS6;A3").
Hypothesis H6w : swf S6 = true.
Variable d6 : list (sv * sv).
Hypothesis H6d : ltac2:(tb__ "0|3|
S30S3cS3aS38S3aS0S0A2A1M0S38S2A1M1A2M2A1Sf6Sd0VS6;A2S40G2S42G0G1Vd6;S3bS2A1A4A2A3").
Hypothesis H6v : ltac2:(tb__ "0|4|
S33S30S38S3aS0S0A2M0A1M1Vd6;S41G0S42S0S0Sb9S4SdaA1M2A4S3bG0A1M3A3A3S30G1Vd6;S41G0S42S0S0G2Sb9A4G3A3A3A2").
Hypothesis H6f : ltac2:(tb__ "0|0|
S30S37S73S2S9S22Sb9S4SdaA1A2A1S6S4bVE;A1A1A3S39A3").
Definition CX : axst := ltac2:(tb__ "0|0|
S51VS6;S3bS3aS0S0A2A1S4fVE;A1A3").

Hypothesis Hfr : ltac2:(tb__ "0|1|
S30S3cS38S1A1M0A1Se3Sd1S89Vn;Vc;A2Sc2Sd1Vn;Vc;A3A3S40G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S30S37Se4Sd1S89Vn;Vc;A2Sc2Sd1Vn;Vc;A3VR;S3bS4cA1A5S39A3").
Hypothesis Hfb : ltac2:(tb__ "0|1|
S30S37S75S2S19S5S4bSd1A1M0A1A1S6G0A1A3S39A3").
Hypothesis Hsupp : ltac2:(tb__ "0|0|
S74S3aS2dS2dA2S42S2dS2dVn;Vc;A4Sb4A3").
Hypothesis HSPEC : ltac2:(tb__ "0|0|
S38S56A1S57VKc;R2R1A2VSpec;S43S56R3S43S56SadS6aQ8A1S56S5bSb3A1S88Vn;A1A4S41S56S59S6cQ40Vc;A2S5eR2A1A2S3bS56A1A3A3A3A1F_;Fmd;Ftr;").
Hypothesis HKfd1 : ltac2:(tb__ "0|0|
S38S56A1S57VKc;R2R1A2S30S3cS58A1S5cS5dR2A1Sb3A2S40S58S5aSb3A1A2A3F_;Fmd;Ftr;").

Hypothesis HspfE : ltac2:(tb__ "0|0|
S30S37S8cS6S4bVE;A1A1A1S39A3").

Lemma X_exit : ltac2:(tb__ "0|0|
S3S38S6aQ40A1A1Sa0S4aVok;S6dS4aVJK;VndX;A1VE;R2R1A5Sa1S32L_;A4Ftp;Frho;").
Proof.
  intros rho tp. apply triple_factsA. intros HF.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF' Hb => proj1 (sp0_facts_sound r f HF' Hb)); [exact HF | exact HspfE]. }
  assert (Htp : eval rho vTP = eval rho (SLit TP)).
  { pose proof (holds_mem _ _ _ HF H6f) as X. cbn [holds] in X. exact X. }
  assert (HnxC : ss_next (ax_S CX) = ss_next (ax_S E)).
  { unfold CX. cbn [ax_S]. rewrite <- H6e. cbn [ss_next]. exact H5n. }
  eapply (triple_conseq (P := SPA segs (JK ndX) CX rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  {
  assert (HS0 : SPA segs (JK ndX) (ax_setS E S0) rho tp w).
  { rewrite <- H1e. apply (SPA_reslice segs (JK ndX) rho E iw _ O_deepS tp w H1n); try reflexivity.
    - rewrite H1e. exact H1s.
    - unfold O_deepS, spM. rewrite !obj_range_lits by (unfold DEEP; lia). rewrite U_add_lit by lia. unfold DEEP. f_equal; lia.
    - unfold O_deepS, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP; lia). unfold DEEP; lia.
    - exact HS. }
  destruct H1i as (I1 & I2 & I3 & I4 & I5).
  assert (HS1 : SPA segs (JK ndX) (mkAX S1 (ax_X E) (ax_base E)) rho tp w).
  { rewrite <- H1j.
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0d (ax_X E) (ax_base E)) ie _ 8 0 tp w I5).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0c (ax_X E) (ax_base E)) ie _ 8 0 tp w I4).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0b (ax_X E) (ax_base E)) ie _ 8 0 tp w I3).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0a (ax_X E) (ax_base E)) ie _ 8 0 tp w I2).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0 (ax_X E) (ax_base E)) ie _ 4 _ tp w I1). exact HS0. }
  pose proof (AxXform.SPA_select segs (JK ndX) rho (mkAX S1 (ax_X E) (ax_base E)) idxs tp w H2 HS1) as HS2.
  pose proof (SPA_merge segs (JK ndX) rho (mkAX (set_objs S1 (select (ss_objs S1) idxs)) (ax_X E) (ax_base E)) 0 S4 tp w H3 HS2) as HS3.
  pose proof (SPA_split segs (JK ndX) rho (mkAX S4 (ax_X E) (ax_base E)) 0 (SLit (-1072)) S5 tp w H4 HS3) as HS4.
  apply (SPA_x_sub segs (JK ndX) rho (mkAX S5 (ax_X E) (ax_base E)) [] tp w ltac:(intros rr Hrr; destruct Hrr)) in HS4.
  change (ax_setX (mkAX S5 (ax_X E) (ax_base E)) []) with (mkAX S5 [] (ax_base E)) in HS4.
  assert (HS5 : SPA segs (JK ndX) (mkAX S5c [] (ax_base E)) rho tp w).
  { pose proof (carveK Kc ndX (mkAX S5 [] (ax_base E)) rho tp w N_ex (ss_next S5) HS4) as X.
    cbn zeta in X. cbn [ax_S ax_setS ax_X ax_base] in X. apply X.
    - exact H5w.
    - apply Pos.leb_refl.
    - exact HbE.
    - exact H5c. }
  assert (HS6 : SPA segs (JK ndX) (mkAX S6 [] (ax_base E)) rho tp w).
  { change (mkAX S6 [] (ax_base E)) with (ax_setS (mkAX S5c [] (ax_base E)) S6).
    apply (SPA_restate segs (JK ndX) rho (mkAX S5c [] (ax_base E)) S6 tp w d6 [] H6w H6d).
    - rewrite <- H6e. reflexivity.
    - unfold diffs_ok. destruct H6v as [-> | ->]; (constructor; [cbn [fst snd] | constructor]); [exact Htp | symmetry; exact Htp].
    - constructor.
    - exact HS5. }
  unfold CX. exact HS6. }
  apply (X_exit_call true ndX n c CX (s_ex CX n c) R); [rewrite HnxC; exact Hnx | rewrite HnxC; exact Hnb | exact Hfr | exact Hcc | exact Hfb | exact Hsupp | exact HSPEC | exact HKfd1].
Qed.
End ExitHandoff.

Definition ob_shapeb (o : sobj) (b lo hi : sv) : bool := ltac2:(tb__ "0|2|
S3dS3dS3dS3dScS1dVo;A1Vb;A2ScS1fVo;A1Vlo;A2A2ScS1eVo;A1Vhi;A2A2S38SfA1M0S37Lx;S2aVo;A1S39SfG0S3fLl;Lc;X38x2A2S20S37Lx;S2bVo;A1S39S3fS3fS2eS3fLl;M1G1S2dS0S38S3aS2dS2dA2A1S38S2cA1S3fLtmpl;Lflds;Lcnt;Lesz;X20x6A2").
Lemma ob_shapeb_sound : ltac2:(tb__ "0|0|
S1S0S0S0S30S37S93R4R3R2R1A4S39A3S30S1R5S17R4R3R2S3bSfA1S1aA5A3F_;Fhi;Flo;Fb;Fo;").
Proof.
  intros [ob ol oh oc od] b lo hi H. unfold ob_shapeb in H. cbn in H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3. subst.
  destruct oc; [|discriminate]. destruct od; try discriminate. reflexivity.
Qed.
Definition d6_okb (d : list (sv * sv)) : bool := ltac2:(tb__ "0|3|
S38S3aS0S0A2M0A1M1S37Ld;Vd;S3fG0G1G0S37Lp;R2S0S0G1S37Ll;R3S45S3dScR2Sb9A2ScR1S4SdaA1M2A2A2S3dScR2G2A2ScR1Sb9A2A2A2G0G1S3fLl0;Lp0;X38x2Lb;La;X3ax1Ll;Lp;X38x2").
Lemma d6_okb_sound : ltac2:(tb__ "0|4|
S38S3aS0S0A2M0A1M1S30S37S98R1A1S39A3S33S30G1R2S41G0S42S0S0Sb9S4SdaA1M2A4S3bG0A1M3A3A3S30G1R2S41G0S42S0S0G2Sb9A4G3A3A3A2F_;Fd;").
Proof.
  intros [|[a b] [|]] H; try discriminate. cbn in H. apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2];
  apply sv_eqb_sound in H1; apply sv_eqb_sound in H2; subst; auto.
Qed.

Definition ex_S5c (E : axst) (S5 : sstate) : sstate := ltac2:(tb__ "0|0|
S11S14VS5;A1S15VS5;A1S13VS5;A1S12VS5;A1S16VS5;A1S43S1S8VS5;A1SadSdbS1SdcSc1A4A3S6VS5;A1S5VS5;A1SeVS5;A1A9").
Definition ex_S6 (S5c : sstate) : sstate := ltac2:(tb__ "0|1|
S11S14VS5c;A1S69S15VS5c;A1S41S3aS3eS0A2M0S42S3eS0U4S4SdaA1A4S3bG0A1A3A2S13VS5c;A1S12VS5c;A1S16VS5c;A1S8VS5c;A1S6VS5c;A1S5VS5c;A1SeVS5c;A1A9").

Definition ex_pipe (ndX : ndesc) (E : axst) (n c : Z) : option (list sobj) := ltac2:(tb__ "0|1f|
S4bVE;A1S7S8R1A1S38S1A1M0SbdR1Sc3S4S65SbfA1A1M1A3S3eSbdR2SbbS4N80A1A3S3eS3cS1A1S3cG0A1M2Lx;S76S1R3R2A3S1S37G2L_;M3S93R1Sc3G1S4Z0M4A1M5A4S102R5R3Sc7A3S7G3Sf5R6R1A2SbdR5G5S4S87A1A3S3eSd2R2R1S5fS87Z8cA2M6Z4M7S64S61Z2Z20A2Z1A2M8A5S7Sd2R1R2S5fS87Z10A2M9Z8MaG4A5S7Sd2R1R3S5fS87GaA2MbGaG4A5S7Sd2R1R4S5fS87Z38A2McGaG4A5S7Sd2R1R5S5fS87Z28A2MdGaG4A5S7G3S3dS3dS3dS3dSd3S4aR7R6G6G7G8A6Sd3S4aR5R6G9GaG4A6A2Sd3S4aR4R6GbGaG4A6A2Sd3S4aR3R6GcGaG4A6A2Sd3S4aR2R6GdGaG4A6A2S11cS3eS38S3eA1MeS11eS3eA1S3eS11bS49S73S3eS122R1A1S41S3eRbS41S3eRaS3bS3eA1A3A3MfA3A1M10A1Li;S3eS11dG10A1Lx;SafU0M11S48S1RbA2A2A6GeS43S3eGfR1A3GeG3SfaS48S1S8R3A1M12A2R1A2S3cS7A1G2Lx;M13Sf8Sf1R3Sf7G12R1A2A2G11A2S7G13Sf9R1G11S4N430A1A3S7S9dVE;R1A2S7S9eR1A1S7S51R1S3bS3aS0S0A2M14A1M15S4fVE;A1M16A3S4cG3S3dS3dS3dS3dS3dS3dS3dS3dS3dSa6S5R4A1S5R13A1M17A2S21R3A1A2SdeS6R4A1S8R4A1G15ScaScbS79VndX;A1Sc1A7A2S21R2A1A2S3cS3aS38G14A1M18S38S2A1M19A2M1aA1S37Lx;Sf6R3R2A2G1aG1aS37Lp;R1G18G19G19S37Ll;R1S98R2A1S2G19S3fLl0;Ls;X38x2Ll;Ld6;X3ax1Lp;S3fX3cx2A2S73S2S9S22Sb9S4SdaA1A2A1S6R13A1M1bA3A2S8cG1bA1A2Sa5S68G17A2A2S78G17VndX;A2A2ScG16S4S119A1A2A2G2G2Lx;Se3R1S89Vn;Vc;A2M1cSc2R1Vn;Vc;A3A3G0G3S3dSe4R2G1cSc2R2Vn;Vc;A3R1S3bS4cA1A5S75S2S19S5S4bR2A1M1dA1A1S6G1dA1A3A2S40G0R1A2S46G0A1M1eX37x2LR;G1eX3cx2G1eX37x2TC;TS6;TS5c;LS5;G1eX3cx2LS4;G1eX3cx2G1eX37x2Tidxs;Trest;G1eX37x2TS1;TS0d;TS0c;TS0b;TS0a;Tie;G1eX37x2TS0;G1eX37x2Lo;G1eX3cx2Tim;Tiw;Tobjs;TS;").

Lemma X_exit_pipe : ltac2:(tb__ "0|4|
S77S2dS2dS4cS38S1A1M0S30S3cG0A1S99R5R2R4R3A4S40G0R1A2A3S74S3aS2dS2dA2S42S2dS2dR5R4A4Sb4A3S38S56A1M1S57VKc;R2R1A2M2VSpec;S43S56R3S43S56SadS6aQ8A1S56S5bSb3A1S88R9A1A4S41S56S59S6cQ40M3R8A2S5eR2A1A2S3bS56A1A3A3A3A1F_;Fmd;Ftr;G1S57G2S30S3cS58A1S5cS5dR2A1Sb3A2S40S58S5aSb3A1A2A3F_;Fmd;Ftr;S3S38S6aG3A1A1Sa0S4aVok;S6dS4aVJK;RbA1R8R2R1A5Sa1S32L_;A4Ftp;Frho;F_;F_;F_;F_;FR;FE;Fc;Fn;FndX;").
Proof.
  intros ndX n c E R Hp Hsupp HSPEC HKfd1 rho tp. unfold ex_pipe in Hp. cbv zeta in Hp.
  destruct (nth_error (ss_objs (ax_S E)) (locate (ss_objs (ax_S E)) spM (SLit (- DEEP)))) as [o|] eqn:E1; [|discriminate].
  destruct (ob_shapeb o spM (SLit (- DEEP)) (SLit 0)) eqn:E2; [|discriminate]. apply ob_shapeb_sound in E2. subst o.
  destruct (same_but_objs _ _) eqn:E3; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:EI; [|discriminate] end.
  apply andb_prop in EI as [EI I5]. apply andb_prop in EI as [EI I4]. apply andb_prop in EI as [EI I3]. apply andb_prop in EI as [I1 I2].
  destruct (select_ok _ _) eqn:E4; [|discriminate].
  destruct (merge_objs_at _ 0) as [S4|] eqn:E5; [|discriminate].
  destruct (split_obj_at S4 0 (SLit (-1072))) as [S5|] eqn:E6; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E7; [|discriminate] end.
  destruct (entails_frA _ _ _) as [R'|] eqn:E8; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E9; [|discriminate] end. injection Hp as HR. subst R'.
  apply andb_prop in E9 as [E9 E10].
  apply andb_prop in E7 as [E7 E7j]. apply andb_prop in E7 as [E7 E7i]. apply andb_prop in E7 as [E7 E7h]. apply andb_prop in E7 as [E7 E7g].
  apply andb_prop in E7 as [E7 E7f]. apply andb_prop in E7 as [E7 E7e]. apply andb_prop in E7 as [E7 E7d]. apply andb_prop in E7 as [E7 E7c].
  apply andb_prop in E7 as [E7a E7b].
  destruct (state_diff (ex_S5c E S5) (ex_S6 (ex_S5c E S5))) as [[d6 [|]]|] eqn:E11; try discriminate.
  apply Pos.eqb_eq in E7a. apply sv_eqb_sound in E7j.
  eapply (X_exit ndX n c E _ S4 S5 (ex_S6 (ex_S5c E S5)) _ R E7h E7i E7j _ E1 _ eq_refl E3 _ (conj I1 (conj I2 (conj I3 (conj I4 I5)))) eq_refl
            E4 E5 E6 E7a E7b E7c eq_refl E7d d6 E11 (d6_okb_sound d6 E7e) E7f E8 E9 E10 Hsupp HSPEC HKfd1 E7g).
Qed.

Section FreeCall.
Variables tb tl : sv.
Let t : sv * sv := ltac2:(tb__ "0|0|
S42S0S0Vtb;Vtl;A4").
Variable kept : list (sv * sv).
Variables bdJ bdX : list bitem.
Definition ndJ : ndesc := ltac2:(tb__ "0|0|
S7bS41S3aS0S0A2Vt;Vkept;A3S3bS3aS3aS0S2dA2S0A2A1VbdJ;S7aA4").
Definition ndX : ndesc := ltac2:(tb__ "0|0|
S7bVkept;S3bS3aS3aS0S2dA2S0A2A1VbdX;S7aA4").
Variables (CF : axst) (s : wsub) (R : list sobj) (T : axst).
Hypothesis Hfr : ltac2:(tb__ "0|1|
S30S3cS38S1A1M0A1Se3VCF;Sb6Vs;A3S40G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S30S37Se5VCF;Sb6Vs;VR;S41S4cSbaS3bS4cA1A3A5S39A3").
Hypothesis HcT : ltac2:(tb__ "0|0|
S30S37S111S68Vs;A2S39A3").
Hypothesis Hnx : ltac2:(tb__ "0|0|
S30S37Sa5S68S5S4bVCF;A1A1A2S39A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S31S30S37S78S5S4bVCF;A1A1M0S11fA2S39A3S30S37SfdG0VbdX;A2S39A3A2").
Hypothesis Hs12 : ltac2:(tb__ "0|0|
S31S30S0SecVs;PcA2Vtb;A3S30S0SecVs;PdA2Vtl;A3A2").
Hypothesis Hpay : ltac2:(tb__ "0|0|
S30S37SfeS6S4bVCF;A1A1S4Z0A1SfcVbdJ;VbdX;A5S39A3").
Hypothesis Hspf : ltac2:(tb__ "0|0|
S30S37S8cS6S4bVCF;A1A1A1S39A3").
Hypothesis Hro : ltac2:(tb__ "0|0|
S30S37S91S6S4bVCF;A1A1S41S3aS0S0A2Vt;Vkept;A3S40S3eU0A2VR;A4S39A3").
Hypothesis Hxr : ltac2:(tb__ "0|1|
S30S37S8fS6S4bVCF;A1M0A1S41S3aS0S0A2Vt;Vkept;A3S40S3eU0A2S8G0A1S8eS4eVCF;A1A6S39A3").
Hypothesis Hnz : ltac2:(tb__ "0|0|
S30S37S73S2S9SaS4Z1000A1Vtb;A2A1S6S4bVCF;A1A1A3S39A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S30S4cS110Sb6VCF;Vs;VR;SbaA5VT;A3").
Hypothesis HT' : ltac2:(tb__ "0|0|
S3S38S6aQ40A1A1Sa0S4aVok;S6dS4aVJK;S120A1VT;R2R1A5Sa1S32L_;A4Ftp';Frho';").

Lemma X_free_call : ltac2:(tb__ "0|0|
S3S38S6aQ40A1A1Sa0S4aVok;S6dS4aVJK;S11fA1VCF;R2R1A5Sa1S32L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct Hnb as [Hnb1 Hnb2]. destruct Hs12 as [Hs12a Hs13].
  apply triple_factsA. intros HF.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF' Hb => proj1 (sp0_facts_sound r f HF' Hb)); [exact HF | exact Hspf]. }
  assert (Htnz : tnz rho t).
  { unfold tnz, t. cbn [fst]. pose proof (holds_mem _ _ _ HF Hnz) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X.
    rewrite Z.mod_small in X by lia. unfold uval in X |- *. lia. }
  apply (free_callA segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 P0f [] [] BX0 PA HKc ok [] UStopLe CF s R rho tp
           ndJ 0%nat t bdX (fun _ => False) free_shape_nil okKK AC Hfr Hcc HcT Hnx Hnb1 Hnb2 eq_refl).
  - apply payA_of_bud_pay. exact Hpay.
  - exact HPAf.
  -
    apply (site_ok_drv ndJ CF s R rho (Some 0%nat) (Some (uval rho (wsub_get s 12%positive)))); try assumption.
    + intros Ai HF' HN HZ. exists t. split; [reflexivity|]. rewrite Hs12a. split; [exact Htnz | reflexivity].
    + intros Ai ms HF' HP0 Hav HN HD HZ HM. split; [|split; [| exact I]].
      * exact Htnz.
      * rewrite Hs12a, Hs13. reflexivity.
  -
    intros rho' tp'. unfold PreF, PostF in HT. rewrite HT. cbn [nd_tv nd_fr nd_am ndJ remove_nth]. fold ndX. apply HT'.
Qed.
End FreeCall.

Section FbChain.
Variable A0 : axst.
Variable bdJ bdX : list bitem.
Let ndJ' : ndesc := ltac2:(tb__ "0|1|
S7bS41S3aS0S0A2M0S42S0S0Sb5Sb7A4S3bG0A1A3S3bS3aS3aS0S2dA2S0A2A1VbdJ;S7aA4").
Let ndX' : ndesc := ltac2:(tb__ "0|0|
S7bS3bS3aS0S0A2A1S3bS3aS3aS0S2dA2S0A2A1VbdX;S7aA4").
Variables (E : axst) (S2 S4 : sstate) (idxs : list nat) (R : list sobj) (T Ex : axst).
Variable iw : nat.

Hypothesis HJwf : ltac2:(tb__ "0|2|
S31S30S37Sa5S68S5S4bVA0;A1M0A1M1A2S39A3S31S30S37SeG0A1S3fA3S30S37S78G1VndJ';A2S39A3A2A2").
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S30S3cS38S4dA1M0A1S50S4aSc0SbeVA0;S39A5S40G0S41S4dS53VE;Sf2A2S3bS4dA1A3A2A3").

Hypothesis H1n : ltac2:(tb__ "0|0|
S30S3cS1A1S76S1S8S4bVE;A1A1Viw;A3S40S1S17Sc4S4S65S64SbfZ50A2A1A1S4Z0A1S3bSfA1S1aA5A2A3").
Hypothesis H1e : ltac2:(tb__ "0|0|
S30S7S102S4bVE;A1Viw;Sc6A3VS2;A3").
Hypothesis H1s : ltac2:(tb__ "0|0|
S30S37Sf5S4bVE;A1VS2;A2S39A3").
Hypothesis H2 : ltac2:(tb__ "0|0|
S30S37SfaS48S1S8VS2;A1A2Vidxs;A2S39A3").
Hypothesis H3 : ltac2:(tb__ "0|0|
S30S3cS7A1Sf8Sf1VS2;Sf7S8VS2;A1Vidxs;A2A2U0A2S40S7VS4;A2A3").
Definition CF : axst := ltac2:(tb__ "0|0|
Sc8S42S0S0Sb5Sb7A4S51VS4;S4eVE;A1S4fVE;A1A3A2").
Hypothesis H4n : ltac2:(tb__ "0|0|
S30S2eS5VS4;A1S5S4bVE;A1A1A3").

Hypothesis Hfr : ltac2:(tb__ "0|1|
S30S3cS38S1A1M0A1Se3Sa4Sb6Sb8Sa4A1A3S40G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S30S37Se5Sa4Sb6Sb8Sa4A1VR;S41S4cSbaS3bS4cA1A3A5S39A3").
Hypothesis HcT : ltac2:(tb__ "0|0|
S30S37S111S68Sb8Sa4A1A2S39A3").
Hypothesis Hnx : ltac2:(tb__ "0|0|
S30S37Sa5S68S5S4bVE;A1A1A2S39A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S31S30S37S78S5S4bVE;A1A1M0VndJ';A2S39A3S30S37SfdG0VbdX;A2S39A3A2").
Hypothesis Hs12 : ltac2:(tb__ "0|1|
S31S30S0SecSb8Sa4A1M0PcA2Sb5A3S30S0SecG0PdA2Sb7A3A2").
Hypothesis Hpay : ltac2:(tb__ "0|0|
S30S37SfeS6S4bSa4A1A1S4Z0A1SfcVbdJ;VbdX;A5S39A3").
Hypothesis HspfE : ltac2:(tb__ "0|0|
S30S37S8cS6S4bVE;A1A1A1S39A3").
Hypothesis Hspf : ltac2:(tb__ "0|0|
S30S37S8cS6S4bSa4A1A1A1S39A3").
Hypothesis Hro : ltac2:(tb__ "0|1|
S30S37S91S6S4bSa4A1A1S41S3aS0S0A2M0S42S0S0Sb5Sb7A4S3bG0A1A3S40S3eU0A2VR;A4S39A3").
Hypothesis Hxr : ltac2:(tb__ "0|2|
S30S37S8fS6S4bSa4A1M0A1S41S3aS0S0A2M1S42S0S0Sb5Sb7A4S3bG1A1A3S40S3eU0A2S8G0A1S8eS4eSa4A1A6S39A3").
Hypothesis HvB : ltac2:(tb__ "0|0|
S30S37S73S2S9SaS4Z1000A1Sb5A2A1S6S4bSa4A1A1A3S39A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S30S4cS110Sb6Sa4Sb8Sa4A1VR;SbaA5VT;A3").

Hypothesis HTwf : ltac2:(tb__ "0|2|
S31S30S37Sa5S68S5S4bVT;A1M0A1M1A2S39A3S31S30S37SeG0A1S3fA3S30S37S78G1VndX';A2S39A3A2A2").
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S30S3cS38S4dA1M0A1S50S4aSc0SbeVT;S39A5S40G0S41S4dS53VEx;Sf2A2S3bS4dA1A3A2A3").
Hypothesis HX : ltac2:(tb__ "0|0|
S3S38S6aQ40A1A1Sa0S4aVok;S6dS4aVJK;VndX';A1VEx;R2R1A5Sa1S32L_;A4Ftp;Frho;").

Lemma X_fb : ltac2:(tb__ "0|0|
S3S38S6aQ40A1A1Sa0S4aVok;S6dS4aVJK;VndJ';A1VA0;R2R1A5Sa1S32L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct HJwf as (W1 & W2 & W3). destruct Hnb as [Hnb1 Hnb2]. destruct HTwf as (V1 & V2 & V3).
  eapply JK_run; [exact Hrun1 | exact W2 | exact W1 | exact W3 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply triple_factsA. intros HF.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho1 sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF' Hb => proj1 (sp0_facts_sound r f HF' Hb)); [exact HF | exact HspfE]. }
  eapply (triple_conseq (P := SPA segs (JK ndJ') CF rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { assert (HS1 : SPA segs (JK ndJ') (ax_setS E S2) rho1 tp w).
    { rewrite <- H1e. apply (SPA_reslice segs (JK ndJ') rho1 E iw _ O_deepM tp w H1n); try reflexivity.
      - rewrite H1e. exact H1s.
      - unfold O_deepM, spT. rewrite !obj_range_lits by (unfold DEEP; lia). rewrite U_add_lit by lia. unfold DEEP. f_equal; lia.
      - unfold O_deepM, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP; lia). unfold DEEP; lia.
      - exact HS. }
    pose proof (AxXform.SPA_select segs (JK ndJ') rho1 (mkAX S2 (ax_X E) (ax_base E)) idxs tp w H2 HS1) as HS2.
    pose proof (SPA_merge segs (JK ndJ') rho1 (mkAX (set_objs S2 (select (ss_objs S2) idxs)) (ax_X E) (ax_base E)) 0 S4 tp w H3 HS2) as HS3.
    unfold CF, dropX. apply SPA_x_sub; [|exact HS3]. cbn [ax_X]. apply In_dropX. }
  assert (HnxC : ss_next (ax_S CF) = ss_next (ax_S E)) by (unfold CF, dropX; cbn [ax_S ax_setX]; exact H4n).
  apply (X_free_call vB vCap [] bdJ bdX CF (s_fb CF) R T Hfr Hcc HcT); try assumption.
  - rewrite HnxC. exact Hnx.
  - rewrite HnxC. split; [exact Hnb1 | exact Hnb2].
  -
    intros rho' tp'. eapply JK_run; [exact Hrun2 | exact V2 | exact V1 | exact V3 |].
    intros L rho3 [<-|[]] Hag3. cbn [la_state]. apply HX.
Qed.
End FbChain.

Definition one_leaf (r : option (list leafA)) : option axst := ltac2:(tb__ "0|3|
S3cS38S4dA1M0A1S3cS4cA1M1Lr;Vr;G0G0G1Ll;R1S46S4cA1M2S4dG0S4dG1Ll0;R2S4cSf3Sf3G1Lla_reason;R1G2G0G1Ll1;R3S40S4cR2A2S4dG0G2Ll3;Ll2;X38x2G2G2G2G2G2Xf3x7Lla_reason;LE;X4dx1Ll1;Ll0;X38x2Ll;G2X3cx2").
Lemma one_leaf_sound : ltac2:(tb__ "0|2|
S3cS38S4dA1M0A1M1S4cS30S3cS4cA1S94R2A1S40S4cR1A2A3S30G1R3S40G0S41S4dS53R2Sf2A2S3bS4dA1A3A2A3F_;FE;Fr;").
Proof. intros r E H. unfold one_leaf in H. destruct r as [[|[E' [| | | | | |]] [|]]|]; try discriminate. injection H as <-. reflexivity. Qed.

Definition fb_pipe (bdJ bdX : list bitem) (A0 : axst) : option axst := ltac2:(tb__ "0|18|
VA0;S4cS7bS41S3aS0S0A2M0S42S0S0Sb5Sb7A4M1S3bG0A1M2A3M3S3bS3aS3aS0S2dA2S0A2A1M4VbdJ;S7aA4S77S7bG2G4VbdX;S7aA4S77S37S3cS4cA1M5L_;M6S3dS3dSa5S68S5S4bR3A1M7A1M8A2S49SeG7A1A1A2S78G8R2A2A2G5G5Lx;S94S50S4aSc0SbeR3S39A5A1S4cS4bR1A1M9S7S8R1A1S38S1A1MaSbdR1Sc4S4S65S64SbfZ50A2A1A1MbA3S3eSbdR2SbbS4Nd0A1A3S3eS3cS1A1G5Lx;S76S1R3R2A3S1G6S93R1Sc4GbS4Z0A1McA4S102R5R3Sc6A3S7G6Sf5R6R1A2S11cS3eS38S3eA1MdS11eS3eA1S3eS11bS49S73S3eS122R1A1S41S3eR5S41S3eR4S3bS3eA1A3A3MeA3A1MfA1Li;S3eS11dGfA1Lx;SafU0M10S48S1R5A2A2A6GdS43S3eGeR1A3GdG6SfaS48S1S8R3A1M11A2R1A2S3cS7A1G5Lx;Sf8Sf1R3Sf7G11R1A2A2G10A2S7Sc8G1S51R1S4eRaA1S4fRaA1A3A2S4cS3cGaA1G5Lx;Se3R1Sb6Sb8R1A1A3GaS110Sb6R2Sb8R2A1R1SbaA5S4cG6S3dS3dS3dS3dS3dS3dS3dS3dS3dS3dS3dS3dS3dS3dS3dS3dSa6S5R4A1S5RcA1M12A2Se5R3Sb6Sb8R3A1M13R2S41S4cSbaS3bS4cA1A3A5A2S111S68G13A2A2Sa5S68G12A2A2S78G12RfA2A2SfdG12VbdX;A2A2ScSecG13PcA2Sb5A2A2ScSecG13PdA2Sb7A2A2SfeS6G7A1M14GcSfcVbdJ;VbdX;A5A2S8cS6RcA1A1A2S8cG14A1A2S91G14G3S40S3eG10A2M15R2A4A2S8fG14G3G15S8G7A1S8eS4eR3A1A6A2S73S2S9SaS4Z1000A1Sb5A2A1G14A3A2Sa5S68S5G9A1M16A2A2S49SeG9A1A1A2S78G16ReA2A2S94S50S4aSc0SbeR1S39A5A1S46S4cA1M17X37x2TT;LR;G17X3cx2TC;LS4;G17X3cx2G17X37x2Tidxs;Trest;G17X37x2TS2;G17X37x2Lo;G17X3cx2Tit;Tiw;Tobjs;TS;LE;G17X3cx2G17X37x2TndX;TndJ;TJ;").

Lemma negb_true : ltac2:(tb__ "0|0|
S37S30S37S49R1A1S39A3S30S37R2S3fA3F_;Fb;"). Proof. intros [|]; [discriminate | reflexivity]. Qed.

Lemma X_fb_pipe : ltac2:(tb__ "0|6|
S38SffA1M0G0S4cS4cS30S3cS4cA1S9aR4R3R2A3S40S4cR1A2A3S3S38S6aQ40A1A1M1Sa0S4aVok;S6dS4aVJK;S7bS3bS3aS0S0A2M2A1M3S3bS3aS3aS0S2dA2S0A2A1M4R6S7aA4A1R4R2R1A5Sa1S32L_;M5A4Ftp;Frho;S3G1Sa0S4aVok;S6dS4aVJK;S7bS41G2S42S0S0Sb5Sb7A4G3A3G4R8S7aA4A1R6R2R1A5G5A4Ftp;Frho;F_;F_;FEx;FA0;FbdX;FbdJ;").
Proof.
  intros bdJ bdX A0 Ex Hp HX rho tp. unfold fb_pipe in Hp. cbv zeta in Hp.
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E0; [|discriminate] end.
  apply andb_prop in E0 as [E0 E0c]. apply andb_prop in E0 as [E0a E0b]. apply negb_true in E0b.
  destruct (one_leaf (sym_runA segs FUEL_X CUTS_X A0 true)) as [E|] eqn:E1; [|discriminate]. apply one_leaf_sound in E1.
  destruct (nth_error (ss_objs (ax_S E)) _) as [o|] eqn:E2; [|discriminate].
  destruct (ob_shapeb o _ _ _) eqn:E3; [|discriminate]. apply ob_shapeb_sound in E3. subst o.
  destruct (same_but_objs _ _) eqn:E4; [|discriminate].
  destruct (select_ok _ _) eqn:E5; [|discriminate].
  destruct (merge_objs_at _ 0) as [S4|] eqn:E6; [|discriminate].
  destruct (entails_frA _ PreF _) as [R|] eqn:E7; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E8; [|discriminate] end.
  apply one_leaf_sound in Hp.
  apply andb_prop in E8 as [E8 Q3]. apply andb_prop in E8 as [E8 Q2]. apply andb_prop in E8 as [E8 Q1]. apply negb_true in Q2.
  apply andb_prop in E8 as [E8 P14]. apply andb_prop in E8 as [E8 P13]. apply andb_prop in E8 as [E8 P12].
  apply andb_prop in E8 as [E8 P11]. apply andb_prop in E8 as [E8 P10]. apply andb_prop in E8 as [E8 P9].
  apply andb_prop in E8 as [E8 P8]. apply andb_prop in E8 as [E8 P7]. apply andb_prop in E8 as [E8 P6].
  apply andb_prop in E8 as [E8 P5]. apply andb_prop in E8 as [E8 P4]. apply andb_prop in E8 as [E8 P3]. apply andb_prop in E8 as [P1 P2].
  apply Pos.eqb_eq in P1. apply sv_eqb_sound in P7. apply sv_eqb_sound in P8.
  eapply (X_fb A0 bdJ bdX E _ S4 _ R _ Ex _ (conj E0a (conj E0b E0c)) E1 E2 eq_refl E4 E5 E6 P1 E7 P2 P3 P4 (conj P5 P6) (conj P7 P8)
            P9 P10 P11 P12 P13 P14 eq_refl (conj Q1 (conj Q2 Q3)) Hp HX).
Qed.

Lemma X_join : ltac2:(tb__ "0|8|
S38SffA1M0G0S4cS2dS2dS4cS38S1A1M1S30S3cS4cA1S9aR7R6R5A3S40S4cR2A2A3S30S3cG1A1S99S7bS3bS3aS0S0A2M2A1M3S3bS3aS3aS0S2dA2S0A2A1M4R7S7aA4R3R5R4A4S40G1R2A2A3S74S3aS2dS2dA2S42S2dS2dR6R5A4Sb4A3S38S56A1M5S57VKc;R2R1A2M6VSpec;S43S56R3S43S56SadS6aQ8A1S56S5bSb3A1S88RaA1A4S41S56S59S6cQ40M7R9A2S5eR2A1A2S3bS56A1A3A3A3A1F_;Fmd;Ftr;G5S57G6S30S3cS58A1S5cS5dR2A1Sb3A2S40S58S5aSb3A1A2A3F_;Fmd;Ftr;S3S38S6aG7A1A1Sa0S4aVok;S6dS4aVJK;S7bS41G2S42S0S0Sb5Sb7A4G3A3G4ReS7aA4A1RcR2R1A5Sa1S32L_;A4Ftp;Frho;F_;F_;F_;F_;F_;FR;FEx;Fc;Fn;FA0;FbdX;FbdJ;").
Proof.
  intros bdJ bdX A0 n c Ex R Hfb Hex Hsupp HSPEC HKfd1.
  apply (X_fb_pipe bdJ bdX A0 Ex Hfb). apply (X_exit_pipe (NDA [] [] bdX ANone) n c Ex R Hex Hsupp HSPEC HKfd1).
Qed.

End SITE.
End DrvSite.

