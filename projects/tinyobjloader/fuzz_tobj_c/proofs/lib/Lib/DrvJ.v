(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_blocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sstate"; "ss_next"; "sv"; "rm"; "rw"; "eval"; "sobj"; "smatch"; "SVar"; "sv_below"; "sprop"; "holds"; "ss_facts"; "rl"; "sv_eqb"; "SLit"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_objs"; "ss_pc"; "ss_regs"; "ss_resv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "pair"; "bool"; "true"; "prod"; "nil"; "cons"; "Some"; "option"; "app"; "None"; "fst"; "andb"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "pos_add_nat"; "LQP"; "agree_vals"; "call_checkP"; "import_sub"; "call_completeP"; "call_soundP"; "J_ofP"; "call_linkP"; "import_okP"; "import_post"; "state_vars_all"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_fds"; "m_fs"; "with_vm_backing"; "FdEntry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "in_ranges"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ.WithSegs.Sum"; "JGD"; "tpchkD"; "TRe_facts"; "TRe_pre"; "TRs_facts"; "TRs_pre"; "TRe_ex"; "TRs_ex"; "dfree_callT"; "dmalloc_callT"; "init_callT"; "DTrue"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "MInvR"; "mem_kept"; "top_kept"; "V_RES"; "V_TOP"; "tp_ok"; "top_var"; "L_malloc_null"; "L_malloc_ok"; "Pre_malloc"; "J_free_pre"; "L_free"; "Pre_free"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_after"; "inited"; "robjs_ok"; "JGi"; "tv_below"; "remove_nth"; "tnz"; "tvv"; "JG"; "caddr"; "keptF"; "TPI"; "patchf"; "rho_patch"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "ltb"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "leb"; "ltb"; "pow"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvJ.WithSegs"; "strip_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "mc_tp"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymFrame SymEntail SymCFG SymSummary SymComplete ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma m_fds_with_vm_backing lz mt m : ltac2:(tb__ "0|0|
S1S21S25S4aQ40A1S41A2A1S3eS40Vlz;Vmt;Vm;A3A1S3eVm;A1A3"). Proof. reflexivity. Qed.
Lemma m_fs_with_vm_backing lz mt m : ltac2:(tb__ "0|0|
S1S85S3fS40Vlz;Vmt;Vm;A3A1S3fVm;A1A3"). Proof. reflexivity. Qed.
#[export] Hint Rewrite m_fds_with_vm_backing m_fs_with_vm_backing : model.

Section WithSegs.
Variable segs : list Segment.
Variable C : mconsts.
Variable E : entry_consts.

Definition strip_facts (S : sstate) : sstate := ltac2:(tb__ "0|0|
S17S1cVS;A1S1dVS;A1S19VS;A1S18VS;A1S1eVS;A1S1bVS;A1S26S11A1S8VS;A1S1aVS;A1A9").

Lemma smatch_reval : ltac2:(tb__ "0|2|
S20S23F_;S6S6S7S25S21S3dA1S7aA2S20S1S23R6R1A1S24A3S1S4aQ40A1M0SbR6R2A2SbR5R2A2A3F_;Fv;S20S1S21S4aQ8A1M1A1S14R6R1A2S14R5R1A2A3Fl;S1G0S29G1A1F_;SaR6A1SaR5A1A3S1S23S3bR8S86R5A1A2S24A3S80S11S12R7A1S13R6A1A3SeVsegs;R9R7R6A4SeVsegs;R9R8R7A4F_;F_;F_;F_;F_;F_;Fw;FS;Frho';Frho;Ff;").
Proof using .
  intros f rho rho' S w Hv Hl Hm Hs HF Hsm.
  assert (H0 : smatch segs rho (strip_facts S) w).
  { destruct w as [tr [ms md]].
    destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
    unfold smatch. cbn [fst snd cfg_ms cfg_model strip_facts ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient].
    split.
    { unfold swf in Hwf |- *. cbn [strip_facts ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient].
      apply andb_true_iff in Hwf as [Hwf _]. rewrite Hwf. reflexivity. }
    repeat (split; [assumption|]). constructor. }
  pose proof (smatch_agree_vars segs f rho rho' (strip_facts S) w Hv Hl Hm Hs H0) as H1.
  destruct w as [tr [ms md]].
  destruct H1 as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & _).
  cbn [fst snd cfg_ms cfg_model strip_facts ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact (proj1 Hsm)|]. repeat (split; [assumption|]). exact HF.
Qed.

Section Sum.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S21S3dA1S3cOF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Hypothesis ML : malloc_laws segs C.

Definition JGD (tv : list (sv * sv)) (D : MA -> Model -> Prop) : jpred := ltac2:(tb__ "0|0|
S6S21S3dA1S3cS2S4S4S0S6fVsegs;VC;VNP;VKc;Vrho0;VP0f;S26S25S1fS1fA2A1Vtv;R1R4R3R2AcVD;R1R2A2A2LAi;A2Lmd;Ltr;Lrho;").
Definition DTrue : MA -> Model -> Prop := fun _ _ => True.

Lemma JGD_JG : ltac2:(tb__ "0|0|
S21S25S9S9A2A1S4S3cOF_;F_;S6S21S3dA1S3cS4bR5R4R3R2R1A5S74Vsegs;VC;VNP;VKc;Vrho0;VP0f;S26S25S1fS1fA2A1R6R4R3R2AbF_;Fmd;Ftr;Frho;FD;Ftv;").
Proof using . intros tv D rho tr md (Ai & H & _). exists Ai. exact H. Qed.
Lemma JG_JGD : ltac2:(tb__ "0|0|
S21S25S9S9A2A1S6S21S3dA1S3cS74Vsegs;VC;VNP;VKc;Vrho0;VP0f;S26S25S1fS1fA2A1R4R3R2R1AbS4bR5S56R4R3R2A5F_;Fmd;Ftr;Frho;Ftv;").
Proof using . intros tv rho tr md (Ai & H). exists Ai. split; [exact H|exact I]. Qed.
Lemma JGD_mono : ltac2:(tb__ "0|1|
S21S25S9S9A2A1S4S3cOF_;F_;M0G0S6S21S3dA1S3cS4S3cR7R2R1A2R7R3R2A2F_;Fm;FA;S4bR7R6R4R3R2A5S4bR8R6R5R4R3A5F_;F_;Fmd;Ftr;Frho;FD';FD;Ftv;").
Proof using . intros tv D D' rho tr md HD (Ai & H & HDi). exists Ai. split; [exact H|apply HD; exact HDi]. Qed.

Ltac clear_sec := try clear P0f; try clear rho0; try clear Kc; try clear NP.

Lemma KEPT_stepW : ltac2:(tb__ "0|1|
S4S4S6S6S6aS47S21SdA1S3cS6S3cS5dVsegs;VC;RaR2R1A5S5dVsegs;VC;RaR8R4A5S6eVsegs;VC;RcS2bS1fA1M0RaR6A6S1fS75Vsegs;VC;ReG0R1A5S75Vsegs;VC;ReG0R2A5F_;Fa;S5eVsegs;VC;ReRdSaS46S45RcR8RaA3R9A2A1SaRbA1A6S4aQ40A1S48ReRaR1A3S1S29S4aQ8A1A1SaReR2A2SaS46S45RfRbRdA3RcA2R2A2A3F_;Fa;F_;F_;F_;F_;F_;FmdM;FrhoM;FmdL;FR;Fs;Fms;FrhoL;Frho;FA';FAi;").
Proof using ML.
  clear_sec. intros Ai A' rho rhoL ms s R mdL rhoM mdM HM HM' HRok Hsub Hkept a Hin.
  apply (robjs_in_ranges segs C Ai None rho R) in Hin; [|exact HRok].
  rewrite <- (Z_to_bv_bv_unsigned 64 a).
  pose proof (bv_urange a) as Ha.
  destruct (caddr_props segs C Ai None _ rhoM mdM ML HM Ha Hin) as (O1 & O2 & O3).
  destruct (caddr_props segs C A' None _ rhoL mdL ML HM' Ha (Hsub _ Hin)) as (O1' & _).
  apply Hkept; try assumption; [exact (caddr_client segs C _ _ _ Hin) | exact (caddr_client segs C _ _ _ (Hsub _ Hin)) |]. intros Hs. apply O3. apply static_alloc_static. exact Hs.
Qed.

Lemma keptF_stepW : ltac2:(tb__ "0|4|
S4S4S6S6S6aS47S21SdA1S3cS6S6S3cS25S1fS1fA2M0S5bG0R1S26G0A1M1A3S5bG0R2S5RcA1A3F_;Fb;S5dVsegs;VC;RcR3R2A5S5dVsegs;VC;RcRaR6A5S77VC;Vrho0;ReA3S5fRfReA2S6eVsegs;VC;R10S2bS1fA1ReRaA6S76Vsegs;VC;Vrho0;G1SaVrho0;A1M2SaRfA1M3A6S5eVsegs;VC;R12R11SaS46S45R10RcReA3RdA2A1G3A6S4aQ40A1S1S29S4aQ8A1A1SaRcR1A2SaR11R1A2A3Fa;S76Vsegs;VC;Vrho0;G1G2SaS79RcS78R12RcReA3A2A1A6F_;F_;F_;F_;F_;F_;F_;F_;F_;FmdM;FrhoM;Frho';FmdL;FR;Fs;Fms;FrhoL;Frho;FA';FAi;").
Proof using ML.
  intros Ai A' rho rhoL ms s R mdL rho' rhoM mdM HP' HM HM' HT HTK HRok HK Hkept Hrm a Ha Hp.
  pose proof (TPI_kept _ _ _ _ HTK HT) as HT'.
  cbn [rho_patch rm]. unfold patchf.
  destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn]; [apply HK; assumption|].
  rewrite Hrm.
  assert (FBI : fbin [] Ai) by (intros b Hb; destruct Hb).
  pose proof (pclF_caddr segs C rho0 [] Ai a FBI HT Hp) as Hc.
  destruct (caddr_props segs C Ai None a rhoM mdM ML HM Ha Hc) as (O1 & O2 & O3).
  destruct (caddr_props segs C A' None a rhoL mdL ML HM' Ha (pclF_caddr segs C rho0 [] A' a HP' HT' Hp)) as (O1' & _).
  transitivity (rm (rho_sub (rho_absorb rho R ms) s) (Z_to_bv 64 a)).
  - apply Hkept; try assumption; [exact (caddr_client segs C _ _ _ Hc) | exact (caddr_client segs C _ _ _ (pclF_caddr segs C rho0 [] A' a HP' HT' Hp)) |]. intros Hs. apply O3. apply static_alloc_static. exact Hs.
  - rewrite rm_absorb_out by exact Hn. apply HK; assumption.
Qed.

Definition tpchkD (s : wsub) : bool := ltac2:(tb__ "0|1|
S2dS2dS2dS15S44Vs;P18A2S16S87VC;A1M0A1A2S82Z0G0A2A2S83G0S84Z2Z40A2A2A2S15S44Vs;S61A2SfS61A1A2A2").

Lemma top_of_chkD : ltac2:(tb__ "0|0|
S47S6S21SdA1S6aS1S23S4cR4A1S24A3S1S4aQ40A1SbS46S45R4R3R2A3R5A2S61A2SbR4S61A2A3F_;Fms;FR;Frho;Fs;").
Proof using .
  clear_sec. clear ML. intros s rho R ms H. unfold tpchkD in H. apply andb_prop in H as [_ Ee]. apply sv_eqb_sound in Ee.
  cbn [rw rho_sub]. rewrite Ee, eval_absorb. reflexivity.
Qed.

Lemma top_var_callee : ltac2:(tb__ "0|0|
S4S47S6S21SdA1S6aS1S23S4cR4A1S24A3S63R6R4A2S63R7S46S45R5R4R3A3R6A2A2F_;F_;Fms;FR;Frho;Fs;FA;").
Proof using . clear_sec. clear ML. intros A s rho R ms H HT. unfold top_var in *. rewrite (top_of_chkD s rho R ms H). exact HT. Qed.

Lemma tp_of_chkD : ltac2:(tb__ "0|0|
S47S6S21SdA1S6aS1S23S4cR4A1S24A3S62VC;S46S45R4R3R2A3R5A2A2F_;Fms;FR;Frho;Fs;").
Proof using .
  clear_sec. clear ML. intros s rho R ms H. unfold tpchkD in H. apply andb_prop in H as [H _].
  apply andb_prop in H as [H Hhi]. apply andb_prop in H as [Ee Hlo]. apply sv_eqb_sound in Ee.
  apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  unfold tp_ok. cbn [rw rho_sub]. rewrite Ee, eval_absorb. cbn [eval].
  rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. rewrite two64. lia.
Qed.

Section CallT.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S43S7S6S57S80S11S12R2A1S13R3A1A3VTR;S42Vsegs;R5R4R3A4R2A2M0F_;G0F_;FQ;Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q) -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S57S57S57S5aR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S43S43S7S7S47S21SdA1M0S21S25S7S2fA2M1A1S57S6S1S29G0A1S7cR7R6R5A3S28G0R4A2A3S1S23S33R8R7R6R5S7fG1S7S2cS7S2fA2R4A4A5S24A3S6VTR;S42Vsegs;RbR9R1A4S31Vsegs;S8R9A1R1R6A4A2Frho1;S21S3dA1M2S6aS3cSeVsegs;R7RdS22G2S7aR3S7bR2R1A2A4A4R10R8R4R2A3R10S46S45R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S7S2fG2S6aS3cS6G2S6aS3cS5bG1S22S7S2fR9R8A4R10A3SeVsegs;RfR15S22G2S7aR8S7bR7R6A2A4A4R18R10R9R7A3S32S8R16A1S46S45R11R14R9A3R15A2R7A3SeVsegs;R8RdS22G2S7aR7S7bR6R5A2A4A4RdS46S45R13R16RbA3R17A2R9R8R6A4S0S39R14RcR17R18R19RfRaA7S6S38R15RdR18R19R1aR1bR10R1RbA9VTR;S42Vsegs;S37R10S46S45R16R19ReA3R1aA2RcA3S3aR1aS8R1bA1R11S8R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S42Vsegs;ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FCl;FJp;FJ;").

Theorem init_callT : ltac2:(tb__ "0|18|
S7S47S21SdA1M0S6S57S43S43S4S21S25S7S2fA2M1A1S2fS2fS4S3cOF_;F_;M2G2S1S23S4cRcA1S24A3S6VTR;S42Vsegs;R9S66VE;A1M3R1A4S31Vsegs;S6bR1R7A4A2Frho1;S1S29G0A1S7cRfG3ReA3S28G0RdA2A3S1S23S33R10G3RfReS7fG1S7S2cS7S2fA2R8A4A5S24A3S1S23S7dVNP;S8R11A1A2S24A3S1S23S10S8R12A1S44R11PcM4A2A2S24A3S1S9S44S34R12S6bS65VE;A1M5S8R13A1M6A4S60A2SfS30G6UaM7A2A1A3S1S6Vrho0;R11A3S21S3dA1M8S6aS3cSeVsegs;R15R18S22G8S7aR3S7bR2R1A2A4A4R14R16R4R2A3S62VC;S46S45R17R18R4A3R19A2A2S0R15S46S45R18R19R5A3R1aA2M9R6R4A3S0S5dVsegs;VC;R14G9R4A5S0VP0f;R18A1S0VKc;R6R4A2S0S6eVsegs;VC;R14S2bS1fA1R18R19A6S0S1S21S25S1fS1fA2MaA1MbS5R14A1S26GaA1McA3S0S81Z0S49Q40MdScR18S44R1aG4A2A2A2A2S0S62VC;R18A2S63R14R18A2A2A2A2A2A2A2A2A2F_;F_;F_;Fmd;Fms;Ftr;G1S5bG1R1RfA3S3S1G1R2S22S7S2fS64VE;A1MeRfA4A3S1G1R2S22S7S2fG5ReA4A3A2F_;Fx;S6S6G8S3cR12R4R3R2R1A4MfS2S4S4S0S5dVsegs;VC;R1R5R3A5M10S0S0S6dR1A1M11S5fR16R1A2A2S0S1GbS5R1A1M12GcA3S0S5eVsegs;VC;R16R1SaR6A1M13SaR5A1M14A6S0VKc;R4R3A2R12R1R3A2A2M15A2A2A2A2LA';A2F_;Fmd;Ftr;Fr';Fr0;S6S6G8S3cGfS2S4S4S0G10S0S0G11S5fR17R1A2A2S0S1GbG12S27GaS22S1fS1fS49GdSbR5S60A2A2S49GdSbR6G4A2A2A4GcA3A3S0S5eVsegs;VC;R17R1G13G14A6G15A2A2A2A2LA';A2F_;Fmd;Ftr;Fr';Fr0;S5bG1S22S7S2fGeR10A4R11A3S6VTR;S42Vsegs;S4bS26S25S9S9A2M16A1M17R10A2S6cR1bR1aR19GeA4R1A4R17A2Frho';F_;S5bG1S22S7S2fG5R10A4R12A3S6VTR;S42Vsegs;S4bS27G16S22S9S9SfS30S8R1cA1G7A2A1S44R1bG4A2A4G17A3R10A2S6cR1cR1bR1aG5A4R1A4R18A2Frho';F_;VTR;S42Vsegs;R16R1bR18A4R17A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FDo;FDn;FJLo;FJLn;FPosts;FA0;FJp;FJ0;FQ;Frho;FR;Fs;FCl;").
Proof using ML TR_callP TR_facts TR_pre.
  intros Cl s R rho Q J0 Jp A0 Posts JLn JLo Dn Do Htp CALLEE He Hchk Hnf Hs12 Hres Hrho0 HIN HPosts HJLn HJLo Tnull Tok.
  subst rho. apply Pos.leb_le in Hnf.
  pose proof (fun tr ms md Hsm HJ => HIN tr ms md Hsm HJ (tp_of_chkD s rho0 R ms Htp)) as HIN'. cbn beta in HIN'. clear HIN. rename HIN' into HIN.
  apply TR_facts. intros HF.
  eapply (TR_callP J0 Jp Cl (Pre_malloc E) s R Posts Q rho0 He Hchk CALLEE).
  -   intros tr ms md Hsm HJ. exact (proj1 (HIN tr ms md Hsm HJ)).
  -
    intros L JL tr ms md rhoL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    destruct (HIN tr ms md Hsm HJ) as (_ & HM0 & HP0 & Hk & HRok & HB0 & Hpos & HTP & HTOP).
    assert (FB0 : fbin [] A0) by (intros b Hb; destruct Hb).
    assert (HT0 : TPI C rho0 A0) by (split; [exact HTP | unfold T0; symmetry; exact HTOP]).
    pose proof HinL as HinL0.
    destruct (HPosts _ HinL) as [EE|EE]; injection EE as HL HJLe; subst L JL.
    +
      destruct (HJLn _ _ _ _ HJL) as (A' & HM' & [Hi' HTK'] & HbA' & Hkept & _ & _).
      assert (HsubA' : forall a, caddr segs C A0 None a -> caddr segs C A' None a).
      { intros a. apply caddr_mono; [exact HTK'|]. intros b Hb. rewrite HB0 in Hb. destruct Hb. }
      split.
      * split; [exact (KEPT_stepW A0 A' rho0 rhoL ms s R md' _ _ HM0 HM' HRok HsubA' Hkept)|].
        intros o' oR Hin' _. cbn in Hin'. destruct Hin'.
      * intros rho0' Hlink.
        eapply TR_pre; [ | apply (Tnull HinL0 (rho_patch rho0' (patchf rho0 rho0' R)))].
        intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
        destruct (HJLn _ _ _ _ HJ') as (A2 & HM2 & [Hi2 HTK2] & HbA2 & Hkept2 & Hk2 & HD2).
        assert (Hag' : agree_vals (ss_next Cl) rho0 rho0') by (destruct Hlink as (A & _); exact A).
        assert (HsubA : forall a, caddr segs C A0 None a -> caddr segs C A2 None a).
        { intros a. apply caddr_mono; [exact HTK2|]. intros b Hb. rewrite HB0 in Hb. destruct Hb. }
        split; [exact (cont_smatch segs Cl (Pre_malloc E) _ s R rho0 rho0' tr ms md w He Hsm eq_refl Hag' Hsm')|].
        exists A2. split; [|exact HD2].
        split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
        -- eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
        -- eapply (MInvR_cont segs C _ ML A0); [exact (conj HM2 (conj Hi2 (TPI_kept _ _ _ _ HTK2 HT0))) | exact HRok | exact HsubA | intros a; eapply call_linkP_rm; exact Hlink].
        -- intros b Hb. destruct Hb.
        -- constructor.
        -- exact I.
        -- constructor.
        -- eapply (keptF_stepW A0 A2 rho0 rhoL ms s R _ rho0' _ _ ltac:(intros b Hb; destruct Hb) HM0 HM2 HT0 HTK2 HRok);
             [intros a _ _; reflexivity | exact Hkept2 | intros a; eapply call_linkP_rm; exact Hlink].
    +
      destruct (HJLo _ _ _ _ HJL) as (A' & HM' & [Hi' HTK'] & HbA' & Hkept & _ & _).
      set (p := bv_unsigned (rw rhoL V_RES)) in *.
      set (n := bv_unsigned (rw (rho_sub (rho_absorb rho0 R ms) s) 12%positive)) in *.
      assert (Hn12 : bv_unsigned (rw rhoL 12%positive) = n).
      { subst n. f_equal. symmetry. apply (proj1 Hag1). reflexivity. }
      assert (Hnrho : bv_unsigned (eval rho0 (wsub_get s 12)) = n) by (subst n; rewrite rw_call'; reflexivity).
      assert (HinNew : In (p, n) (ma_blocks A')) by (rewrite HbA'; left; reflexivity).
      pose proof HM' as HMi'. unfold MInvR in HMi'.
      pose proof (minv_block_geom C A' _ _ _ p n HMi' HinNew) as (G0 & _ & G2 & G3 & G4).
      unfold PGSZ, UNIT, IB in G2, G3. pose proof HTK' as TK. unfold top_kept in TK. pose proof (topL_val (ma_L A')) as TR3.
      assert (HsubA' : forall a, caddr segs C A0 None a -> caddr segs C A' None a).
      { intros a. apply caddr_mono; [exact HTK'|]. intros b Hb. rewrite HB0 in Hb. destruct Hb. }
      assert (NEWFREE : forall a, p <= a < p + n -> caddr segs C A0 None a -> False).
      { intros a Ha [Hc|[Hc|(b & m & Hb & _ & Hr)]].
        - destruct (block_addr_props segs C A' _ _ _ p n a ML HMi' HinNew Ha) as [X _]. lia.
        - destruct Hc as (Hw & _). apply (ml_wseg segs C ML) in Hw.
          rewrite Z_to_bv_unsigned, bv_wrap_small in Hw by (rewrite two64; lia).
          destruct (block_addr_props segs C A' _ _ _ p n a ML HMi' HinNew Ha) as [_ X]. exact (X Hw).
        - rewrite HB0 in Hb. destruct Hb. }
      split.
      * split.
        -- exact (KEPT_stepW A0 A' rho0 rhoL ms s R md' _ _ HM0 HM' HRok HsubA' Hkept).
        -- intros o' oR Hin' HinR. cbn in Hin'. destruct Hin' as [<-|[]].
           destruct (obj_range rho0 oR) as [lo hi] eqn:HR2.
           unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
           rewrite soff_lit_small by lia. unfold soff. cbn [eval]. fold p.
           rewrite bv_signed_U, Hn12.
           apply ranges_disjoint_by_points. intros a Ha1 Ha2.
           apply (NEWFREE a).
           ++ destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X in Ha1; lia.
           ++ apply (HRok oR a HinR). rewrite HR2. cbn [fst snd]. exact Ha2.
      * intros rho0' Hlink.
        eapply TR_pre; [ | apply (Tok HinL0 (rho_patch rho0' (patchf rho0 rho0' R)))].
        intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
        destruct (HJLo _ _ _ _ HJ') as (A2 & HM2 & [Hi2 HTK2] & HbA2 & Hkept2 & Hk2 & HD2).
        assert (Hag' : agree_vals (ss_next Cl) rho0 rho0') by (destruct Hlink as (A & _); exact A).
        assert (HsubA : forall a, caddr segs C A0 None a -> caddr segs C A2 None a).
        { intros a. apply caddr_mono; [exact HTK2|]. intros b Hb. rewrite HB0 in Hb. destruct Hb. }
        assert (E1 : rw rho0' (pos_add_nat (ss_next Cl) 10) = rw rhoL V_RES).
        { destruct Hlink as (_ & _ & _ & L4).
          specialize (L4 V_RES). change (ss_next (Pre_malloc E)) with NF in L4.
          rewrite Hres in L4. cbn [eval] in L4. symmetry. apply L4; [reflexivity | cbv; lia]. }
        assert (E2 : bv_unsigned (eval rho0' (wsub_get s 12)) = n).
        { rewrite <- Hnrho. f_equal. symmetry. eapply eval_agree_vals; [exact Hag' | exact Hs12]. }
        assert (Enew : tvv (rho_patch rho0' (patchf rho0 rho0' R)) (SVar (pos_add_nat (ss_next Cl) 10), wsub_get s 12) = (p, n)).
        { unfold tvv. cbn [fst snd eval]. rewrite !eval_patch. cbn [eval rho_patch rw]. rewrite E1, E2. reflexivity. }
        split; [exact (cont_smatch segs Cl (Pre_malloc E) _ s R rho0 rho0' tr ms md w He Hsm eq_refl Hag' Hsm')|].
        exists A2. split; [|exact HD2].
        split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
        -- eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
        -- eapply (MInvR_cont segs C _ ML A0); [exact (conj HM2 (conj Hi2 (TPI_kept _ _ _ _ HTK2 HT0))) | exact HRok | exact HsubA | intros a; eapply call_linkP_rm; exact Hlink].
        -- intros b Hb. destruct Hb.
        -- constructor; [|constructor].
           intros _. rewrite Enew. cbn [snd]. split; [lia|]. split; [rewrite HbA2; left; reflexivity|]. intros [].
        -- cbn [tvd]. split; [|exact I]. intros t' [] _ _.
        -- constructor; [|constructor].
           intros Hz. exfalso. apply Hz. unfold tnz. change (bv_unsigned (eval ?r (fst ?t))) with (fst (tvv r t)). rewrite Enew. cbn [fst]. lia.
        -- eapply (keptF_stepW A0 A2 rho0 rhoL ms s R _ rho0' _ _ ltac:(intros b Hb; destruct Hb) HM0 HM2 HT0 HTK2 HRok);
             [intros a _ _; reflexivity | exact Hkept2 | intros a; eapply call_linkP_rm; exact Hlink].
Qed.

Theorem dmalloc_callT : ltac2:(tb__ "0|11|
S7S47S21SdA1M0S6S21S25S9S9A2M1A1S57S4S3cOF_;F_;M2S4S43F_;S4S21S25S7S2fA2M3A1F_;S4S2fF_;M4G4G2G2S1S23S4cRcA1S24A3S4S6VTR;S42Vsegs;R9R2A1S66VE;A1M5R1A4S31Vsegs;S6bR1R8R2A1A4A2Frho1;FAi;S1S29G0A1S7cRfG5ReA3S28G0RdA2A3S4S1S23S33R11G5R10RfS7fG3S7S2cS7S2fA2R9R1A1A4A5S24A3FAi;S1S23S7dVNP;S8R11A1A2S24A3S1S23S7eS61VNP;A2S24A3S1S23S70S8R13A1RfA2S24A3S1S23S10S8R14A1S44R13PcM6A2A2S24A3S1S9S44S34R14S6bS65VE;A1M7S8R15A1M8A4S60A2SfS30G8UaM9A2A1A3S4S21S3dA1MaS6aS3cSeVsegs;R17R1aS22GaS7aR3S7bR2R1A2A4A4S6fVsegs;VC;VNP;VKc;Vrho0;VP0f;S26S25S1fS1fA2MbA1R17R5R18R4R2AcR16R6R3A2S62VC;S46S45R1aR1bR5A3R1cA2A2S63R8S46S45R1bR1cR6A3R1dA2A2S0R18R9S46S45R1cR1dR7A3R1eA2R8R6A4S0S6eVsegs;VC;R9S2bS1fA1R1cR1dA6S81Z0S49Q40McScR1cS44R1eG6A2A2A2A2A2A2F_;F_;F_;F_;F_;Fmd;Fms;Ftr;FAi;S4G3S5bG3R1R11R2A1A3S3S1G3R2S22S7S2fS64VE;A1MdR11R3A1A4A3S1G3R2S22S7S2fG7R10R3A1A4A3A2F_;Fx;FAi;S4S6S6GaS3cR14R5R4R3R2R1A5S2S4S4S0S5dVsegs;VC;R1R5R3A5S0S0S6dR1A1S5fR7R1A2A2S0S1S21GbA1MeS5R1A1S5R7A1A3S0S5eVsegs;VC;R7R1SaR6A1SaR5A1A6S0VKc;R4R3A2R14R1R3A2A2A2A2A2A2LA';A2F_;Fmd;Ftr;Fr';Fr0;FAi;S4S6S6GaS3cS1S4aGcA1SbR4G6A2ScR1bS44R1dG6A2MfA2A3R15R6R5R4R3R2A5S2S4S4S2GeGeS2GeGeS0S5dVsegs;VC;R3R8R6A5S0S0S6dR3A1S5fRaR3A2A2S0S1GeS5R3A1S2aGbR2S27GbS22S1fS1fS49GcSbR8S60A2A2S49GcSbR9G6A2A2A4R1A3A3A3S0S1GeS5RaA1S2aGbR2R1A3A3S0S5eVsegs;VC;RaR3SaR9A1SaR8A1A6S0VKc;R7R6A2R17R3R6A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2F_;F_;Fmd;Ftr;Fr';Fr0;FAi;S2S4S4S5bG3S22S7S2fGdR12R1A1M10A4R13R1A1A3LAi;A2S6S32S8R1cA1R19R1A3VTR;S42Vsegs;S4bR19R12A2S6cR1dR1cR1bGdA4R2A4R18A2F_;Frho';F_;S2S4S4S5bG3S22S7S2fG7G10A4R14R1A1A3LAi;A2S6S32S8R1dA1R1aR1A3VTR;S42Vsegs;S4bS27G1S22S9S9SfS30S8R1eA1G9A2A1GfA4R1aA3R12A2S6cR1eR1dR1cG7A4R2A4R19A2F_;Frho';F_;VTR;S42Vsegs;S4bR18R16A2R1cR19A4R17A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FDo;FDn;FJLo;FJLn;FPosts;FJp;FD;FQ;Ftv;Frho;FR;Fs;FCl;").
Proof using ML TR_callP TR_ex TR_facts TR_pre.
  intros Cl s R rho tv Q D Jp Posts JLn JLo Dn Do Htp CALLEE He Hchk Hnf Hvt Hnb Hs12 Hres HIN HPosts HJLn HJLo Tnull Tok.
  apply Pos.leb_le in Hnf. apply Pos.ltb_lt in Hvt.
  assert (TOPV : forall Ai tr ms md, JGi segs C NP Kc rho0 P0f [] tv Ai rho tr md -> top_var Ai (rho_sub (rho_absorb rho R ms) s)).
  { intros Ai tr ms md (Hav & _ & (_ & _ & [_ HT]) & _). unfold top_var. rewrite (top_of_chkD s rho R ms Htp).
    rewrite <- (proj1 Hav V_TOP Hvt). symmetry. exact HT. }
  pose proof (fun Ai tr ms md Hsm HJ HD => HIN Ai tr ms md Hsm HJ HD (tp_of_chkD s rho R ms Htp) (TOPV Ai tr ms md HJ)) as HIN'. cbn beta in HIN'. clear HIN. rename HIN' into HIN.
  apply TR_facts. intros HF.
  apply (TR_ex MA (fun Ai => fun r t m => JGi segs C NP Kc rho0 P0f [] tv Ai r t m /\ D Ai m)). intros Ai.
  eapply (TR_callP _ (Jp Ai) Cl (Pre_malloc E) s R (Posts Ai) Q rho He (Hchk Ai) (CALLEE Ai)).
  -   intros tr ms md Hsm [HJ HD]. exact (proj1 (HIN Ai tr ms md Hsm HJ HD)).
  -
    intros L JL tr ms md rhoL tr' ms' md' HinL Hsm [HJ HD] Hag1 HsmL HJL.
    destruct (HIN Ai tr ms md Hsm HJ HD) as (_ & HRok & Hpos).
    destruct HJ as (Hav & Hk & HM & HP & (HN & HDv & HZ) & HK & HP0).
    pose proof HinL as HinL0.
    destruct (HPosts Ai _ HinL) as [EE|EE]; injection EE as HL HJLe; subst L JL.
    +
      destruct (HJLn _ _ _ _ _ HJL) as (A' & HM' & [Hi' HTK'] & HbA' & Hkept & _ & _).
      assert (HsubA' : forall a, caddr segs C Ai None a -> caddr segs C A' None a) by (intros a; apply caddr_mono; [exact HTK'|]; intros b Hb; rewrite HbA'; exact Hb).
      split.
      * split; [exact (KEPT_step segs C ML Ai A' rho rhoL ms s R md md' (MI1 segs C _ _ _ _ HM) HM' HRok HsubA' Hkept)|].
        intros o' oR Hin' _. cbn in Hin'. destruct Hin'.
      * intros rho' Hlink.
        assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
        eapply TR_pre; [ | apply (Tnull (ex_intro _ Ai HinL0) (rho_patch rho' (patchf rho rho' R)) ltac:(eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]))].
        intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
        destruct (HJLn _ _ _ _ _ HJ') as (A2 & HM2 & [Hi2 HTK2] & HbA2 & Hkept2 & Hk2 & HD2).
        assert (HsubA : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A2)) by (intros b Hb; rewrite HbA2; exact Hb).
        split; [exact (cont_smatch segs Cl (Pre_malloc E) _ s R rho rho' tr ms md w He Hsm eq_refl Hag' Hsm')|].
        exists A2. split; [|exact HD2].
        split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
        -- eapply agree_vals_trans; [exact Hav|].
           eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
        -- eapply (MInvR_cont segs C _ ML Ai); [exact (conj HM2 (conj Hi2 (TPI_kept _ _ _ _ HTK2 (proj2 (proj2 HM))))) | exact HRok | intros a; apply caddr_mono; [exact HTK2 | exact HsubA] | intros a; eapply call_linkP_rm; exact Hlink].
        -- intros b Hb. destruct Hb.
        -- apply (tvin_agree [] A2 (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb |].
           unfold tvin in HN |- *. apply Forall_forall. intros t Ht Hnz.
           destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [apply HsubA; exact X1 | exact X2].
        -- apply (tvd_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HDv].
        -- apply (tvz_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HZ].
        -- eapply (keptF_step segs C rho0 [] ML Ai A2 rho rhoL ms s R md _ rho' HP); [intros b Hb; destruct Hb | exact HM | exact HM2 | exact HTK2 | exact HRok | exact HK | exact Hkept2 | intros a; eapply call_linkP_rm; exact Hlink].
    +
      destruct (HJLo _ _ _ _ _ (rw_call' _ _ _ _ _) HJL) as (A' & l1 & l2 & HM' & [Hi' HTK'] & HbA' & HbAi & Hkept & _ & _).
      assert (HsubA' : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A')).
      { intros b Hb. rewrite HbA'. apply in_app_mid. rewrite <- HbAi. exact Hb. }
      set (p := bv_unsigned (rw rhoL V_RES)) in *.
      set (n := bv_unsigned (rw (rho_sub (rho_absorb rho R ms) s) 12%positive)) in *.
      assert (Hn12 : bv_unsigned (rw rhoL 12%positive) = n).
      { subst n. f_equal. symmetry. apply (proj1 Hag1). reflexivity. }
      assert (Hnrho : bv_unsigned (eval rho (wsub_get s 12)) = n) by (subst n; rewrite rw_call'; reflexivity).
      assert (HinNew : In (p, n) (ma_blocks A')) by (rewrite HbA'; apply in_or_app; right; left; reflexivity).
      pose proof HM' as HMi'. unfold MInvR in HMi'.
      pose proof (minv_block_geom C A' _ _ _ p n HMi' HinNew) as (G0 & _ & G2 & G3 & G4).
      unfold PGSZ, UNIT, IB in G2, G3. pose proof HTK' as TK. unfold top_kept in TK. pose proof (topL_val (ma_L A')) as TR3.
      assert (NEWFREE : forall a, p <= a < p + n -> caddr segs C Ai None a -> False).
      { intros a Ha [Hc|[Hc|(b & m & Hb & _ & Hr)]].
        - destruct (block_addr_props segs C A' _ _ _ p n a ML HMi' HinNew Ha) as [X _]. lia.
        - destruct Hc as (Hw & _). apply (ml_wseg segs C ML) in Hw.
          rewrite Z_to_bv_unsigned, bv_wrap_small in Hw by (rewrite two64; lia).
          destruct (block_addr_props segs C A' _ _ _ p n a ML HMi' HinNew Ha) as [_ X]. exact (X Hw).
        - pose proof (new_block_disjoint C A' _ _ _ l1 l2 (p, n) HMi' HbA' (b, m) ltac:(rewrite <- HbAi; exact Hb)) as DD.
          unfold MallocInv.ranges_disjoint in DD. cbn [fst snd] in DD. lia. }
      split.
      * split.
        -- exact (KEPT_step segs C ML Ai A' rho rhoL ms s R md md' (MI1 segs C _ _ _ _ HM) HM' HRok ltac:(intros a; apply caddr_mono; [exact HTK' | exact HsubA']) Hkept).
        -- intros o' oR Hin' HinR. cbn in Hin'. destruct Hin' as [<-|[]].
           destruct (obj_range rho oR) as [lo hi] eqn:HR2.
           unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
           rewrite soff_lit_small by lia. unfold soff. cbn [eval]. fold p.
           rewrite bv_signed_U, Hn12.
           apply ranges_disjoint_by_points. intros a Ha1 Ha2.
           apply (NEWFREE a).
           ++ destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X in Ha1; lia.
           ++ apply (HRok oR a HinR). rewrite HR2. cbn [fst snd]. exact Ha2.
      * intros rho' Hlink.
        assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
        eapply TR_pre; [ | apply (Tok (ex_intro _ Ai HinL0) (rho_patch rho' (patchf rho rho' R)) ltac:(eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]))].
        intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
        destruct (HJLo _ _ _ _ _ (rw_call' _ _ _ _ _) HJ') as (A2 & k1 & k2 & HM2 & [Hi2 HTK2] & HbA2 & HbAi2 & Hkept2 & Hk2 & HD2).
        assert (HsubA : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A2)).
        { intros b Hb. rewrite HbA2. apply in_app_mid. rewrite <- HbAi2. exact Hb. }
        assert (E1 : rw rho' (pos_add_nat (ss_next Cl) 10) = rw rhoL V_RES).
        { destruct Hlink as (_ & _ & _ & L4).
          specialize (L4 V_RES). change (ss_next (Pre_malloc E)) with NF in L4.
          rewrite Hres in L4. cbn [eval] in L4. symmetry. apply L4; [reflexivity | cbv; lia]. }
        assert (E2 : bv_unsigned (eval rho' (wsub_get s 12)) = n).
        { rewrite <- Hnrho. f_equal. symmetry. eapply eval_agree_vals; [exact Hag' | exact Hs12]. }
        assert (Enew : tvv (rho_patch rho' (patchf rho rho' R)) (SVar (pos_add_nat (ss_next Cl) 10), wsub_get s 12) = (p, n)).
        { unfold tvv. cbn [fst snd eval]. rewrite !eval_patch. cbn [eval rho_patch rw]. rewrite E1, E2. reflexivity. }
        assert (HMi2 : MInv C A2 (rd_of segs (rm rhoL)) (wok_of segs (rm rhoL)) (m_vmmaps (cfg_model (w_cfg w)))) by exact HM2.
        split; [exact (cont_smatch segs Cl (Pre_malloc E) _ s R rho rho' tr ms md w He Hsm eq_refl Hag' Hsm')|].
        exists A2. split; [|exact HD2].
        split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
        -- eapply agree_vals_trans; [exact Hav|].
           eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
        -- eapply (MInvR_cont segs C _ ML Ai); [exact (conj HM2 (conj Hi2 (TPI_kept _ _ _ _ HTK2 (proj2 (proj2 HM))))) | exact HRok | intros a; apply caddr_mono; [exact HTK2 | exact HsubA] | intros a; eapply call_linkP_rm; exact Hlink].
        -- intros b Hb. destruct Hb.
        -- constructor.
           ++ intros _. rewrite Enew. cbn [snd]. split; [lia|]. split; [rewrite HbA2; apply in_or_app; right; left; reflexivity|]. intros [].
           ++ apply (tvin_agree [] A2 (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb |].
              unfold tvin in HN |- *. apply Forall_forall. intros t Ht Hnz.
              destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [apply HsubA; exact X1 | exact X2].
        -- cbn [tvd]. split.
           ++ intros t' Ht' _ Hnz'. rewrite Enew.
              assert (Hbt : (sv_below (ss_next Cl) (fst t') && sv_below (ss_next Cl) (snd t')) = true) by exact (proj1 (forallb_forall _ _) Hnb t' Ht').
              assert (Hag'' : agree_vals (ss_next Cl) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
              rewrite (tvv_agree (ss_next Cl) rho _ t' Hag'' Hbt).
              apply (proj1 (tnz_agree (ss_next Cl) rho _ t' Hag'' Hbt)) in Hnz'.
              destruct (proj1 (Forall_forall _ _) HN t' Ht' Hnz') as (_ & X1 & _).
              intros Heq. apply (fresh_not_old C A2 _ _ _ k1 k2 p n (tvv rho t') HMi2 HbA2 ltac:(lia)); [|symmetry; exact Heq].
              rewrite <- HbAi2. exact X1.
           ++ apply (tvd_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HDv].
        -- constructor.
           ++ intros Hz. exfalso. apply Hz. unfold tnz. change (bv_unsigned (eval ?r (fst ?t))) with (fst (tvv r t)). rewrite Enew. cbn [fst]. lia.
           ++ apply (tvz_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HZ].
        -- eapply (keptF_step segs C rho0 [] ML Ai A2 rho rhoL ms s R md _ rho' HP); [intros b Hb; apply HsubA; exact (HP b Hb) | exact HM | exact HM2 | exact HTK2 | exact HRok | exact HK | exact Hkept2 | intros a; eapply call_linkP_rm; exact Hlink].
Qed.

Theorem dfree_callT : ltac2:(tb__ "0|d|
S7S47S21SdA1M0S6S21S25S9S9A2M1A1S2eG1S57S4S3cOF_;F_;M2S4S43F_;S4S2fF_;G2S1S23S4cRbA1S24A3S4S6VTR;S42Vsegs;R6R2A1S69VE;A1M3R1A4S31Vsegs;S6bR1S27S25S7S2fA2M4S22S7S2fS68VE;A1M5R5R2A1A4S26G4A1A3A4A2Frho1;FAi;S1S29G0A1S7cReG3RdA3S28G0RcA2A3S1S23S33RfG3ReRdS27S7G5S26S7A1A3A5S24A3S1S23S7dVNP;S8R10A1A2S24A3S1S23S7eS61VNP;A2S24A3S1S23S70S8R12A1ReA2S24A3S1S29G1A1S5cG1RfReA3S28G1RdA2A3S4S21S3dA1M6S6aS3cSeVsegs;R15R18S22G6S7aR3S7bR2R1A2A4A4S6fVsegs;VC;VNP;VKc;Vrho0;VP0f;S26S25S1fS1fA2M7A1R15R5R16R4R2AcR12R6R3A2S0S67Vsegs;VC;R7VKc;S46S45R18R19R5A3R1aA2R6R4A7R13R8S46S45R19R1aR6A3R1bA2R7R5A4F_;S0S72R18R15A2S0S1G7S73R18R15A2S22S1fS1fS49Q40M8ScR18S44R1aPcM9A2A2A2MaS49G8ScR18S44R1aPdMbA2A2A2A4A3S6eVsegs;VC;R7S28S1fGaA2R18R19A6A2A2A2F_;F_;F_;Fmd;Fms;Ftr;FAi;S4S6S6G6S3cR10R5R4R3R2R1A5S2S4S4S2S21G7A1McGcS2GcGcS0S5dVsegs;VC;R3R7R5A5S0S0S6dR3A1S5fR9R3A2A2S0S1GcS5R9A1S2aG7R2S27G7S22S1fS1fS49G8SbR8G9A2A2S49G8SbR8GbA2A2A4R1A3A3A3S0S1GcS5R3A1S2aG7R2R1A3A3S0S5eVsegs;VC;R9R3SaR8A1SaR7A1A6S0VKc;R6R5A2R13R3R5A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2F_;Fmd;Ftr;Fr';Fr0;FAi;S6S32S8R17A1R14R1A3VTR;S42Vsegs;S4bS71G1R13R14A3RdA2S6cR18R17R16G5A4R2A4R11A2F_;Frho';VTR;S42Vsegs;S4bR13RfA2R17R14A4R10A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FDf;FJLf;FJp;FD;FQ;Ft;Fi;Ftv;Frho;FR;Fs;FCl;").
Proof using ML TR_callP TR_ex TR_facts TR_pre.
  intros Cl s R rho tv i t Q D Jp JLf Df Htp CALLEE He Hchk Hnf Hvt Hnb Hnth HR HJLf Tfree.
  apply Pos.leb_le in Hnf. apply Pos.ltb_lt in Hvt.
  assert (TOPV : forall Ai tr ms md, JGi segs C NP Kc rho0 P0f [] tv Ai rho tr md -> top_var Ai (rho_sub (rho_absorb rho R ms) s)).
  { intros Ai tr ms md (Hav & _ & (_ & _ & [_ HT]) & _). unfold top_var. rewrite (top_of_chkD s rho R ms Htp).
    rewrite <- (proj1 Hav V_TOP Hvt). symmetry. exact HT. }
  apply TR_facts. intros HF.
  apply (TR_ex MA (fun Ai => fun r t' m => JGi segs C NP Kc rho0 P0f [] tv Ai r t' m /\ D Ai m)). intros Ai.
  eapply (TR_callP _ (Jp Ai) Cl (Pre_free E) s R [(L_free E, JLf Ai)] Q rho He Hchk (CALLEE Ai)).
  -
    intros tr ms md Hsm [HJ HDD]. destruct (HR Ai tr ms md Hsm HJ HDD) as (HJp & Hnz & Ht & HRok). apply HJp.
    destruct HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
    destruct (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Hnth) Hnz) as (Tpos & Tin & Tfb).
    split; [|split; [|split; [exact Hk | split; [exact (tp_of_chkD s rho R ms Htp) | split; [exact (proj1 (proj2 HM)) | exact (TOPV Ai tr ms md (conj Hav (conj Hk (conj HM (conj HP (conj (conj HN (conj HD HZ)) (conj HK HP0)))))))]]]]].
    + eapply MI1. eapply (MInvR_mem segs C _ ML); [exact HM| |reflexivity]. intros a Ha Ho. apply rm_absorb_out.
      exact (R_miss segs C ML Ai (Some _) rho rho md R a (MI1 segs C _ _ _ _ HM) HRok Ha Ho).
    + rewrite !rw_call'. rewrite <- Ht. exact Tin.
  -
    intros L JL tr ms md rhoL tr' ms' md' HinL Hsm [HJ HDD] Hag1 HsmL HJL.
    destruct (HR Ai tr ms md Hsm HJ HDD) as (_ & Hnz & Ht & HRok).
    destruct HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
    destruct (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Hnth) Hnz) as (Tpos & Tin & Tfb).
    cbn [In] in HinL. destruct HinL as [HinL|[]]. injection HinL as HL HJLe. subst L JL.
    destruct (HJLf _ _ _ _ _ HJL) as (A' & l1 & l2 & HM' & [Hi' HTK'] & HbAi & HbA' & Hkept & _ & _).
    rewrite !rw_call' in HbAi.
    set (x := bv_unsigned (eval rho (wsub_get s 12))) in *.
    set (m := bv_unsigned (eval rho (wsub_get s 13))) in *.
    assert (SUB : forall A2 k1 k2, ma_blocks Ai = k1 ++ (x, m) :: k2 -> ma_blocks A2 = k1 ++ k2 ->
                 forall bn, In bn (ma_blocks Ai) -> bn <> (x, m) -> In bn (ma_blocks A2)).
    { intros A2 k1 k2 E1 E2 bn Hb Hbx. rewrite E2. rewrite E1 in Hb.
      apply in_mid_cases in Hb as [Hb|Hb]; [|exact Hb]. exfalso. exact (Hbx Hb). }
    assert (CADDR : forall A2, top_kept Ai A2 -> (forall bn, In bn (ma_blocks Ai) -> bn <> (x, m) -> In bn (ma_blocks A2)) ->
                   forall a, caddr segs C Ai (Some x) a -> caddr segs C A2 None a).
    { intros A2 HTK HS a [H|[H|(b & n & Hb & Hbx & Hr)]]; [left; unfold top_kept in HTK; rewrite HTK; exact H | right; left; exact H | right; right].
      exists b, n. split; [apply HS; [exact Hb | intros Heq; apply Hbx; injection Heq as -> ->; reflexivity]|].
      split; [discriminate | exact Hr]. }
    pose proof (SUB A' l1 l2 HbAi HbA') as HsubA'.
    split.
    + split.
      * intros a Hina.
        apply (robjs_in_ranges segs C Ai (Some x) rho R) in Hina; [|exact HRok].
        rewrite <- (Z_to_bv_bv_unsigned 64 a).
        pose proof (bv_urange a) as Ha.
        destruct (caddr_props segs C Ai (Some x) _ rho md ML (MI1 segs C _ _ _ _ HM) Ha Hina) as (O1 & O2 & O3).
        destruct (caddr_props segs C A' None _ rhoL md' ML HM' Ha (CADDR A' HTK' HsubA' _ Hina)) as (O1' & _).
        apply Hkept; try assumption; [exact (caddr_client segs C _ _ _ Hina) | exact (caddr_client segs C _ _ _ (CADDR A' HTK' HsubA' _ Hina)) |]. intros Hs. apply O3. apply static_alloc_static. exact Hs.
      * intros o' oR Hin' _. cbn in Hin'. destruct Hin'.
    + intros rho' Hlink.
      assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
      assert (Hag'' : agree_vals (ss_next Cl) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
      eapply TR_pre; [ | apply (Tfree (rho_patch rho' (patchf rho rho' R)) Hag'')].
      intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
      destruct (HJLf _ _ _ _ _ HJ') as (A2 & k1 & k2 & HM2 & [Hi2 HTK2] & HbAi2 & HbA2 & Hkept2 & Hk2 & HD2).
      rewrite !rw_call' in HbAi2. fold x in HbAi2. fold m in HbAi2.
      pose proof (SUB A2 k1 k2 HbAi2 HbA2) as HsubA2.
      split; [exact (cont_smatch segs Cl (Pre_free E) _ s R rho rho' tr ms md w He Hsm eq_refl Hag' Hsm')|].
      exists A2. split; [|exact HD2].
      split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
      * eapply agree_vals_trans; [exact Hav|].
        eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
      * eapply (MInvR_mem segs C _ ML); [exact (conj HM2 (conj Hi2 (TPI_kept _ _ _ _ HTK2 (proj2 (proj2 HM)))))| |reflexivity]. intros a Ha Ho. cbn [rho_patch rm]. unfold patchf.
        destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn'].
        -- exfalso. eapply (R_miss segs C ML A2 None rho rhoL _ R a); [exact HM2 | | exact Ha | exact Ho | exact Hi].
           intros o b Ho' Hr'. apply (CADDR A2 HTK2 HsubA2). exact (HRok o b Ho' Hr').
        -- eapply call_linkP_rm. exact Hlink.
      * intros b Hb. destruct Hb.
      * apply (tvin_agree [] A2 (ss_next Cl) rho); [exact Hag'' | |].
        { unfold tv_below in *. apply forallb_forall. intros t' Ht'. apply (proj1 (forallb_forall _ _) Hnb). eapply remove_nth_In. exact Ht'. }
        unfold tvin in HN |- *. apply Forall_forall. intros t' Ht' Hnz'.
        destruct (proj1 (Forall_forall _ _) HN t' (remove_nth_In _ _ _ Ht') Hnz') as (X0 & X1 & X2).
        split; [exact X0|]. split; [|exact X2]. apply HsubA2; [exact X1|].
        rewrite <- Ht. exact (tvd_nth_distinct rho tv i t t' HD Hnth Ht' Hnz Hnz').
      * apply (tvd_agree (ss_next Cl) rho); [exact Hag'' | | apply tvd_remove; exact HD].
        unfold tv_below in *. apply forallb_forall. intros t' Ht'. apply (proj1 (forallb_forall _ _) Hnb). eapply remove_nth_In. exact Ht'.
      * apply (tvz_agree (ss_next Cl) rho); [exact Hag'' | |].
        { unfold tv_below in *. apply forallb_forall. intros t' Ht'. apply (proj1 (forallb_forall _ _) Hnb). eapply remove_nth_In. exact Ht'. }
        unfold tvz in HZ |- *. apply Forall_forall. intros t' Ht'. apply (proj1 (Forall_forall _ _) HZ). eapply remove_nth_In. exact Ht'.
      * intros a Ha Hp. cbn [rho_patch rm]. unfold patchf.
        destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn']; [apply HK; assumption|].
        rewrite (call_linkP_rm _ _ _ _ _ _ _ _ _ _ Hlink).
        assert (FBI : fbin [] Ai) by (intros b Hb; destruct Hb).
        pose proof (pclF_caddr segs C rho0 [] Ai a FBI (proj2 (proj2 HM)) Hp) as Hc.
        pose proof (TPI_kept _ _ _ _ HTK2 (proj2 (proj2 HM))) as HT2.
        destruct (caddr_props segs C Ai None a rho md ML (MI1 segs C _ _ _ _ HM) Ha Hc) as (O1 & O2 & O3).
        destruct (caddr_props segs C A2 None a rhoL _ ML HM2 Ha (pclF_caddr segs C rho0 [] A2 a ltac:(intros b Hb; destruct Hb) HT2 Hp)) as (O1' & _).
        transitivity (rm (rho_sub (rho_absorb rho R ms) s) (Z_to_bv 64 a)).
        -- apply Hkept2; try assumption; [exact (caddr_client segs C _ _ _ Hc) | exact (caddr_client segs C _ _ _ (pclF_caddr segs C rho0 [] A2 a ltac:(intros b Hb; destruct Hb) HT2 Hp)) |]. intros Hs. apply O3. apply static_alloc_static. exact Hs.
        -- rewrite rm_absorb_out by exact Hn'. apply HK; assumption.
Qed.
End CallT.

Let TRs (ok : world -> Prop) : assn -> assn -> Prop := triple segs ok.
Let TRe : assn -> assn -> Prop := etriple segs.
Lemma TRs_facts : ltac2:(tb__ "0|1|
S5aOF_;S43S7S6S57S80S11S12R2A1S13R3A1A3VTRs;R6S42Vsegs;R5R4R3A4R2A3M0F_;G0F_;FQ;Frho;FS;FJ;Fok;").
Proof using . intros ok. exact (triple_factsJ segs ok). Qed.
Lemma TRs_ex : forall ok (A : Type) (J : A -> jpred) S rho (Q : assn),
  (forall x, TRs ok (SPJ segs (J x) S rho) Q) -> TRs ok (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q.
Proof using . intros ok. exact (triple_SPJ_ex segs ok). Qed.
Lemma TRs_pre : ltac2:(tb__ "0|0|
S5aOF_;S57S57S57S5aR3R1A1R5R2A1F_;Fw;VTRs;R5R4R2A3VTRs;R6R4R3A3F_;F_;FQ;FP';FP;Fok;").
Proof using segs. intros ok P P' Q HP H. eapply triple_conseq; [exact HP | intros w Hw; exact Hw | exact H]. Qed.
Lemma TRe_facts : ltac2:(tb__ "0|1|
S43S7S6S57S80S11S12R2A1S13R3A1A3VTRe;S42Vsegs;R5R4R3A4R2A2M0F_;G0F_;FQ;Frho;FS;FJ;").
Proof using . exact (etriple_factsJ segs). Qed.
Lemma TRe_ex : forall (A : Type) (J : A -> jpred) S rho (Q : assn),
  (forall x, TRe (SPJ segs (J x) S rho) Q) -> TRe (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q.
Proof using . exact (etriple_SPJ_ex segs). Qed.
Lemma TRe_pre : ltac2:(tb__ "0|0|
S57S57S57S5aR3R1A1R5R2A1F_;Fw;VTRe;R4R2A2VTRe;R4R3A2F_;F_;FQ;FP';FP;").
Proof using segs. intros P P' Q HP H. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw | exact H]. Qed.

Definition init_call (ok : world -> Prop) := init_callT (triple segs ok) (TRs_facts ok) (TRs_pre ok) (call_soundP segs ok).
Definition init_call_ex := init_callT (etriple segs) TRe_facts TRe_pre (call_completeP segs).
Definition dmalloc_call (ok : world -> Prop) := dmalloc_callT (triple segs ok) (TRs_facts ok) (TRs_ex ok) (TRs_pre ok) (call_soundP segs ok).
Definition dmalloc_call_ex := dmalloc_callT (etriple segs) TRe_facts TRe_ex TRe_pre (call_completeP segs).
Definition dfree_call (ok : world -> Prop) := dfree_callT (triple segs ok) (TRs_facts ok) (TRs_ex ok) (TRs_pre ok) (call_soundP segs ok).
Definition dfree_call_ex := dfree_callT (etriple segs) TRe_facts TRe_ex TRe_pre (call_completeP segs).
End Sum.
End WithSegs.
