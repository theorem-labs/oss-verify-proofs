(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "nil"; "option"; "pair"; "cons"; "length"; "Some"; "nat"; "None"; "prod"; "app"; "andb"; "false"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "SHB"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sobj"; "sstate"; "sv"; "rm"; "ss_objs"; "smatch"; "sprop"; "eval"; "rl"; "rw"; "holds"; "agree_below"; "obj_range"; "outside_all"; "ranges_disjoint"; "SLit"; "ro_addr"; "ss_next"; "sv_below"; "sprop_below"; "ss_facts"; "ss_lenient"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface"; "MSGB"; "facts_fw"; "Pre_fw"; "Posts_fw"; "P_fw"; "fw_msgs"; "objs_farW"; "obj_farW"; "xblk"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "sub"; "of_nat"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "FdChannel"; "WriteEv"; "fd_lookup"; "m_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "w_cfg"; "w_tr"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw.Fw"; "Kw"; "Kf"; "ch2"; "EVS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "ax_base"; "ax_X"; "mkLeafA"; "sym_runA"; "entailsA"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "virt"; "vms"; "mat_equiv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.DrvFwStates"; "O_b1z"; "app_obj"; "O_b2r"; "CUTS_FW"; "FUEL_FW"; "XS1"; "XS2"; "axc"; "splits_fw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err.WLerrS"; "Pre_wl1"; "D"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw.Fw.Inst"; "Jp"; "rho_wl"; "rho_fin"; "WLF"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err.WLerr"; "Kw"; "MSG"; "Posts_wl"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "set_rl"; "obj_nolist"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine"; "rom_bytes_ok"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundI SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymBytes SymObj SymCall SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform DrvGlue DrvPristine.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SysA MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import SpecConsts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Musl_wl_err.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.DrvFwStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma triple_pre : ltac2:(tb__ "0|1|
S4fOF_;S54OS54S4fR4R1A1R4F_;Fw;R3S51S15R6R5R3A4M0F_;G0F_;F_;FQ;FX;FP;Fok;").
Proof. intros ok P X Q HX H n Hg w Hw. exact (H (HX w Hw) n Hg w Hw). Qed.
Lemma etriple_pre : ltac2:(tb__ "0|2|
S4fOF_;M0OG0S4fR4R1A1R4F_;Fw;R3S50S15R5R3A3M1F_;G1F_;F_;FQ;FX;FP;").
Proof. intros P X Q HX H w Hw. exact (H (HX w Hw) w Hw). Qed.

Lemma SPA_morph : ltac2:(tb__ "0|1|
S36S36S5eS1cS1aS1aS4S17Q40A1A1S4fS0S4SfS1dS1dA2M0A1S62R6A1S7G0A1A3S0S5S2dS2cR6A1S61R7A1A2S6A3S20S15R6S5dR8A1S67R4R3A2A4S20S15R6R8S67R5R4A2A4F_;RbR7R5S53R4A1S75S52R4A1A1A4RbR7R6S53R5A1S75S52R5A1A1A4F_;S34S15RcRaR8R6R5A6S34S15RcS5fRbRaA2R8R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;FS';FA;FJ';FJ;").
Proof.
  intros J J' A S' rho rho' tp w HX Hb HS HJ [(Hsm & HMI & Hwf & Hsh & Hhz) Hk].
  split; [|apply HJ; exact Hk].
  split; [apply HS; exact Hsm|]. split; [exact HMI|].
  split; [unfold axwf; cbn [ax_S ax_X ax_base ax_setS]; rewrite HX; cbn [forallb]; exact Hb|].
  split; [|exact Hhz]. unfold shadow_ok. cbn [ax_X ax_setS]. rewrite HX. constructor.
Qed.

Lemma SPA_morphX : ltac2:(tb__ "0|9|
S36S36S5eS1cS1aS1aS4S17Q40A1M0A1S4fS0S5S11S82SfS1dS1dA2M1S66S2cR5A1M2A1S62R6A1A3S2dG2S61R6A1A2A2S6A3S0G0S22R4S61R7A1M3A2S22R5G3A2A3G1S81G1R1S62R9A1A3S1S0G0S22R7S13S1dS1dR2A3M4A2S22R8G4A2A3S0G0S22R7S14S1dS1dR2A3M5A2S22R8G5A2A3A2F_;Fr;G0S28R8S1fS5dRaA1M6A1R1A3S3S0S8S17Q8A1M7A1M8S1eR9R2A2SeG7A1A3A1S1S28R9S1fRbA1R3A3S0G8S1eR9R3A2S1eRaR3A2A3A2F_;F_;Fx;S20S15R8G6S67R6R5A2A4S20S15R8RaS67R7R6A2A4F_;RdR9R7S53R6A1S75S52R6A1A1A4RdR9R8S53R7A1S75S52R7A1A1A4F_;S34S15ReRcRaR8R7A6S34S15ReS5fRdRcA2RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;FS';FA;FJ';FJ;").
Proof.
  intros J J' A S' rho rho' tp w Hwf' Hb HX HO HS HJ [(Hsm & HMI & Hwf & Hsh & Hhz) Hk].
  split; [|apply HJ; exact Hk].
  split; [apply HS; exact Hsm|]. split; [exact HMI|].
  split; [unfold axwf; cbn [ax_S ax_X ax_base ax_setS]; exact Hwf'|].
  split; [|exact Hhz].
  apply (shadow_ok_transport rho rho' A (ax_setS A S')); [reflexivity | exact Hb | exact HX | | exact Hsh].
  intros x _ Hout Hrm. exact (HO x Hout Hrm).
Qed.

Lemma outside_all_set_rl : ltac2:(tb__ "0|0|
S1aS33S4S17Q8A1A1F_;S4S1bA1S17Q40A1S0S5S82S1bS88R2A3S6A3S28R5R3R2A3S28S87R6R5A2R4R3A3F_;F_;Fa;Fobjs;Ff;Frho;").
Proof.
  intros rho f objs a Hnl Hout. unfold outside_all in *. apply Forall_forall. intros o Ho.
  rewrite (obj_range_set_rl rho f o (proj1 (forallb_forall _ _) Hnl o Ho)). exact (proj1 (Forall_forall _ _) Hout o Ho).
Qed.

Lemma rm_none_ro : ltac2:(tb__ "0|5|
S1aS1cS4S17Q40M0A1M1A1S4fS32S32S20S15R6R5S67R4R3A2A4S56S1bS1bS29S27R8R1A2S9S32S32R4R3A4A2Lo;S1fR6A1A3S32S1S42Z0M2R1A2S44R1S46R4R5A2A2A2S0S5S2bS15S19G0S43R6R2A2A2A2S6A3F_;Fk;S42G2R5A2S42R5S45Z2Z40A2A2G1S1S42R8S18G0R1A2M3A2S44G3R7A2A2S0S8S17Q8A1M4A1S1eRdR2A2SeG4A1A3F_;Fa;F_;F_;F_;F_;F_;Fhi;Flo;Fw;Ftp;FS;Frho;").
Proof.
  intros rho S tp w lo hi Hsm Hdisj Hro Hlo Hhi a Ha.
  destruct w as [tr [ms md]]. unfold virt in Hsm. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in Hsm.
  pose proof (smatch_mm segs _ _ _ _ _ Hsm) as (_ & _ & Hfr).
  pose proof Hsm as (_ & _ & _ & _ & _ & Hroc & _). cbn [fst snd cfg_ms] in Hroc.
  rewrite <- (Hfr a (ranges_disjoint_outside rho _ lo hi a Hdisj Ha)).
  apply Hroc. replace a with (Z_to_bv 64 (lo + (bv_unsigned a - lo))) by (apply bv_eq; rewrite Z_to_bv_small; [lia | rewrite two64; lia]).
  apply Hro. lia.
Qed.

Lemma vms_none_ro : ltac2:(tb__ "0|3|
S1aS1cS4S17Q40A1M0A1S4S49A1M1S7cS48G0S20S15R7R6S67R5S9G1S76R4S77R3R2A2A4A2A4S0S5S2bS15R2A2S6A3S0S8S17Q8A1M2A1S7dS68R4R7R5A3R3A2SeG2A1A3F_;F_;Fa;Fmd;Fms;Ftr;Ftp;FS;Frho;").
Proof.
  intros rho S tp tr ms md a Hsm Hro. unfold virt in Hsm. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in Hsm.
  pose proof Hsm as (_ & _ & _ & _ & _ & Hroc & _). cbn [fst snd cfg_ms] in Hroc. apply Hroc. exact Hro.
Qed.

Lemma ax_setS_twice : ltac2:(tb__ "0|0|
S5eS1cS1cS0S5eS5fS5fR3R2A2R1A2S5fR3R1A2A3FS2;FS1;FA;").
Proof. intros A S1 S2. reflexivity. Qed.

Lemma agree_below_sym : ltac2:(tb__ "0|0|
S33S1aS1aS26R3R2R1A3S26R4R2R3A3F_;Frho';Frho;Fn;").
Proof.
  intros n rho rho' (A & B & C). split; [intros i Hi; symmetry; apply A; exact Hi|].
  split; [intros l; symmetry; apply B | intros a; symmetry; apply C].
Qed.

Lemma obj_farW_disjoint : ltac2:(tb__ "0|0|
S1aS32S32S1bS42Z7fff7ff01000S18Q40S24R4PaA2A2A2S42Z0R4A2S42R4S45Z2Z20A2A2S0S5S40R6R5R4A3S6A3S29S27R8R5A2S9S32S32R7R6A4A2F_;F_;F_;F_;Fo;Fhi0;Flo0;Fr;").
Proof.
  intros r lo0 hi0 o H10 Hlo0 Hhi0 H. unfold obj_farW in H. unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [fst snd].
  pose proof (urange (rw r 10)) as R10.
  destruct (ob_base o) as [bz|bi|op ba bb| | | | |] eqn:Eb; try discriminate.
  - destruct (ob_lo o) as [lz| | | | | | |]; try discriminate. destruct (ob_hi o) as [hz| | | | | | |]; try discriminate.
    apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
    apply Z.eqb_eq in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. subst bz.
    cbn [eval]. rewrite Z_to_bv_small by (rewrite two64; lia). rewrite !soff_lit_small by lia.
    apply Bool.orb_true_iff in H4. rewrite !Z.leb_le in H4. lia.
  - destruct (ob_lo o) as [lz| | | | | | |]; try discriminate. destruct (ob_hi o) as [hz| | | | | | |]; try discriminate.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
    apply Pos.eqb_eq in H0. subst bi. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    cbn [eval]. rewrite !soff_lit_small by lia. lia.
Qed.
Lemma objs_farW_disjoint : ltac2:(tb__ "0|0|
S1aS32S32S4S1bA1S42Z7fff7ff01000S18Q40S24R4PaA2A2A2S0S5S3fR4R3R2A3S6A3S56S1bS1bS29S27R7R1A2S9S32S32R6R5A4A2Lo;R3A3F_;F_;Fobjs;Fhi0;Flo0;Fr;").
Proof.
  intros r lo0 hi0 objs H10 H. unfold objs_farW in H. apply andb_prop in H as [H Hf]. apply andb_prop in H as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  apply Forall_forall. intros o Ho. apply obj_farW_disjoint; [exact H10 | exact Hlo | exact Hhi | exact (proj1 (forallb_forall _ _) Hf o Ho)].
Qed.

Section Fw.
Variable ok : assn.
Variable J0 : jpredA.
Variables msg len : Z.

Definition ch2 : word := Z_to_bv 64 2.
Definition EVS (k : nat) : list event := ltac2:(tb__ "0|1|
S58S17Q8A1M0S49S4cS5bA1S57G0Vk;S39Vmsg;Vlen;A2A3A4").
Definition Kw (k : nat) : jpredA := ltac2:(tb__ "0|1|
S1aS4S17Q40A1A1S4S49A1M0S48S2G0G0S1VJ0;R5R4R1R2A4S0G0R3S10S49R1S5cVk;A1A3A3A2Ltr0;A2Lmd;Ltr;Lt;Lr;").

Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hfd2 : ltac2:(tb__ "0|0|
S1aS4S17Q40A1A1S4S49A1S48VJ0;R4R3R2R1A4S0S8S4aA1S4dS4eR2A1S5bA2ScS4aS4bS5bA1A2A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HokK : ltac2:(tb__ "0|0|
SdS37S15Vok;S59R1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
SdS85S15Vok;S59R1A1A3Fk;").

Definition Kf (r1 : valuation) (tp : list word) (k : nat) : jpredA := ltac2:(tb__ "0|1|
S1aS4S17Q40A1A1M0S4S49A1S48S1S0G0R3Vtp;A3S59Vk;Vr1;R3R2R1A5A2Lmd;Ltr;Lt;L_;").
Lemma J0_mat : ltac2:(tb__ "0|0|
S1aS4S17Q40A1A1S4S49A1S48S48S69S15R4R2R1A4VJ0;R6R5R4R3A4VJ0;R7R6R5R3A4F_;F_;Fmd';Fmd;Ftr;Ft;Fr;").
Proof. intros r t tr md md' Hme HJ. eapply Hst0; [apply agree_below_refl | exact Hme | exact HJ]. Qed.
Lemma Kf_stable : ltac2:(tb__ "0|0|
S1aS4S17Q40A1A1SdS33S38S15R1S5aR4R3R2A3A3Flvl;Fk;Ftp;Fr1;").
Proof.
  intros r1 tp k lvl r r' t tr md md' Hag Hme [Ht (tr0 & HJ & Htr)]. split; [exact Ht|].
  exists tr0. split; [eapply J0_mat; eauto | exact Htr].
Qed.
Lemma Kf_okK : ltac2:(tb__ "0|0|
S1aS4S17Q40A1A1SdS37S15Vok;S5aR3R2R1A3A3Fk;Ftp;Fr1;").
Proof. intros r1 tp k r t tr ms md msv' [_ HK]. exact (HokK k r1 t tr ms md msv' HK). Qed.
Lemma Kf_okP : ltac2:(tb__ "0|0|
S1aS4S17Q40A1A1SdS85S15Vok;S5aR3R2R1A3A3Fk;Ftp;Fr1;").
Proof. intros r1 tp k r t tr ms md x8 [_ HK]. exact (HokP k r1 t tr ms md x8 HK). Qed.
Lemma Kw0_of_J0 : ltac2:(tb__ "0|0|
S1aS4S17Q40A1A1S4S49A1S48VJ0;R4R3R2R1A4S59U0R5R4R3R2A5F_;Fmd;Ftr;Ft;Fr;").
Proof. intros r t tr md HJ. exists tr. split; [exact HJ|]. unfold EVS. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma okK_J0 : ok_frameA segs ok J0.
Proof. intros r t tr ms md msv' HJ. exact (HokK 0%nat r t tr ms md msv' (Kw0_of_J0 _ _ _ _ HJ)). Qed.

Section Inst.

Variable W : axst. Variables S4 Cs : sstate. Variable s : wsub. Variable R : list sobj.
Variables T Tf F : axst. Variables G1 G2 G3 : sstate. Variable sp : wsub.
Hypothesis HrunW : ltac2:(tb__ "0|1|
S0S8S4S60A1M0A1S64S83S6eS6dS3bVmsg;Vlen;A2S6A5ScG0SaS60S63VW;S84A2S7S60A1A3A2A3").
Hypothesis HnW : ltac2:(tb__ "0|0|
S0S33S2cS5dVW;A1A1S55A3").
Hypothesis HXW : ltac2:(tb__ "0|1|
S0S4SfS1dS1dA2M0A1S62VW;A1SaG0S41Vmsg;Vlen;A2S7G0A1A3A3").
Hypothesis HbW : ltac2:(tb__ "0|0|
S0S1dS61VW;A1S2aS16A1A3").
Hypothesis HfW : ltac2:(tb__ "0|0|
S0S4S21A1S2fS5dVW;A1A1S3aA3").
Hypothesis Hsplits : ltac2:(tb__ "0|0|
S0S8S1cA1S72S5dVW;A1A1ScS1cVS4;A2A3").
Hypothesis Hfinish : ltac2:(tb__ "0|0|
S0S1cS6bS6bVS4;S6aA2S6cVmsg;Vlen;A2A2VCs;A3").
Hypothesis Hswf1 : ltac2:(tb__ "0|0|
S0S5S31S6bVS4;S6aA2A1S6A3").
Hypothesis HswfC : swf Cs = true.
Hypothesis HnC : ss_next Cs = NF.
Hypothesis Hf4 : ss_facts S4 = facts_fw.
Hypothesis Hmiss : ltac2:(tb__ "0|0|
S0S5S3fVmsg;S43Vmsg;Vlen;A2S1fVS4;A1A3S6A3").
Hypothesis Hrom : ltac2:(tb__ "0|0|
S0S5S93S15Vmsg;S39Vmsg;Vlen;A2A3S6A3").
Hypothesis Hnl4 : state_nolist S4 = true.
Hypothesis Hn4 : ss_next S4 = NF.
Hypothesis Hobjs1 : ltac2:(tb__ "0|0|
S0S4S1bA1S1fS6bVS4;S6aA2A1S10S1bS1fVS4;A1SaS1bS6aS7S1bA1A3A3A3").
Hypothesis Hlen : ltac2:(tb__ "0|0|
S0S32S47SbS17Q8A1S39Vmsg;Vlen;A2A2A1Vlen;A3").
Hypothesis Hlen2 : 1 <= len <= 64.
Hypothesis Hmsg : ltac2:(tb__ "0|0|
S1S42Z1000Vmsg;A2S42S43Vmsg;Vlen;A2Z8933cA2A2").
Let C : axst := ax_setS W Cs.
Hypothesis Hefr : ltac2:(tb__ "0|1|
S0S8S4S1bA1M0A1S91VC;S73Vs;A3ScG0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0S5S90VC;S73Vs;VR;SaS5eS74S7S5eA1A3A5S6A3").
Hypothesis S13 : wsub_get s 13 = SLit 0.
Hypothesis S15 : ltac2:(tb__ "0|0|
S0S1dS8dVs;PfA2S2aVlen;A1A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S5eS92Vs;S73S74VC;VR;A5VT;A3").
Hypothesis HnT : ss_next (ax_S T) = 125%positive.
Hypothesis HTf : ltac2:(tb__ "0|0|
S0S5eS8fS3aVT;A2VTf;A3").
Hypothesis HlTf : ltac2:(tb__ "0|0|
S0S5S30S5dVTf;A1A1S12A3").
Hypothesis HnTf : ss_next (ax_S Tf) = 125%positive.
Hypothesis HrunF : ltac2:(tb__ "0|1|
S0S8S4S60A1M0A1S64S83S6eS6dVTf;S6A5ScG0SaS60S63VF;S84A2S7S60A1A3A2A3").
Hypothesis HnF : ss_next (ax_S F) = 125%positive.
Hypothesis HbF : ltac2:(tb__ "0|0|
S0S1dS61VF;A1S2aS16A1A3").
Hypothesis Hxs1 : ltac2:(tb__ "0|0|
S0S8S1cA1S86S5dVF;A1S6fA2ScS1cVG1;A2A3").
Hypothesis HobjsG1 : ltac2:(tb__ "0|1|
S0S4S1bA1S1fVG1;A1M0S10S1bS57S1bUbG0A3SaS1bS6aSaS1bS6cVmsg;Vlen;A2S7S1bA1A3A3A3A3").
Hypothesis HnG1 : ss_next G1 = 125%positive.
Hypothesis Hdrop : drop2 G1 = G2.
Hypothesis Hxs2 : ltac2:(tb__ "0|0|
S0S8S1cA1S86VG2;S70A2ScS1cVG3;A2A3").
Hypothesis HnG3 : ss_next G3 = 125%positive.
Hypothesis HnlG3 : state_nolist G3 = true.
Hypothesis Hent : ltac2:(tb__ "0|0|
S0S5S65S71VG3;A1S3dVsp;A3S6A3").
Hypothesis Hspid : ltac2:(tb__ "0|0|
S0S5S8eVsp;S55A2S6A3").

Definition fwl (r : valuation) : positive -> list byte := ltac2:(tb__ "0|2|
S33S5S4S17Q8A1M0A1L_;M1S89R1P5A2S7G0A1G1S89R1P6A2S39Vmsg;Vlen;A2S23Vr;R1A2X5x2X5x2Ll;").
Definition rho_wl (r : valuation) : valuation := set_rl r (fwl r).
Lemma rho_wl_5 : ltac2:(tb__ "0|1|
S1aS0S4S17Q8A1M0A1S23S79R1A1P5A2S7G0A1A3Fr;"). Proof. intros r. reflexivity. Qed.
Lemma rho_wl_6 : ltac2:(tb__ "0|0|
S1aS0S4S17Q8A1A1S23S79R1A1P6A2S39Vmsg;Vlen;A2A3Fr;"). Proof. intros r. reflexivity. Qed.

Definition WLF (r : valuation) : Prop := ltac2:(tb__ "0|3|
S1S0S4S17Q8A1M0A1M1S23Vr;P5A2S7G0A1A3S1S0G1S23Vr;P6A2S39Vmsg;Vlen;A2A3S1S0S32S18Q40M2S24Vr;PdA2A2Z0A3S0S32S18G2S24Vr;PfA2A2Vlen;A3A2A2A2").
Definition Jp (r1 : valuation) (tp : list word) : jpredA := ltac2:(tb__ "0|0|
S1aS4S17Q40A1A1S4S49A1S48S1S7bR4A1S5aVr1;Vtp;U0R4R3R2R1A7A2Lmd;Ltr;Lt;Lr;").

Lemma Jp_stable : ltac2:(tb__ "0|0|
S1aS4S17Q40A1A1S38S15P5cS78R2R1A2A3Ftp;Fr1;").
Proof.
  intros r1 tp r r' t tr md md' Hag Hme [(A5 & A6 & A13 & A15) HK].
  split; [| eapply (Kf_stable r1 tp 0%nat 92%positive); [exact Hag | exact Hme | exact HK]].
  destruct Hag as (Hw & Hl & _). unfold WLF.
  rewrite <- (Hl 5%positive), <- (Hl 6%positive), <- (Hw 13%positive ltac:(lia)), <- (Hw 15%positive ltac:(lia)).
  repeat split; assumption.
Qed.

Lemma Kw_Jp_Kf : ltac2:(tb__ "0|1|
S1aS4S17Q40A1A1M0SdS1aG0S4S49A1S48S7eS78R7R6A2S7S17Q8A1A1S39Vmsg;Vlen;A2R5R4R3R2R1A8S5aR8R7R6R5R4R3R2A7F_;Fmd;Ftr;Ft;Fr;Fk;Ftp;Fr1;").
Proof.
  intros r1 tp k r t tr md (tr0 & [_ [Ht (tr00 & HJ & ->)]] & ->). split; [exact Ht|].
  exists tr00. split; [exact HJ|]. unfold WLerr.TRk, WLerr.MSG, EVS. cbn [firstn map app]. rewrite app_nil_r. reflexivity.
Qed.

Lemma MSG_len : ltac2:(tb__ "0|2|
S0SdSbS17Q8A1M0S7fS7G0A1S39Vmsg;Vlen;A2M1A2A2SbG0G1A2A3").
Proof. reflexivity. Qed.

Lemma wl_call : ltac2:(tb__ "0|5|
S1aS4S17Q40A1A1M0S1aG0S51S15Vok;S34S15S78R4R3A2M1S73R2R1A5S35S15S7eG1S7S17Q8A1M2A1M3S39Vmsg;Vlen;A2M4SbG2S7fG3G4A2A2A4P5cR2R1S80A6A4Ftp2;Frho2;Ftp;Fr1;").
Proof.
  intros r1 tp rho2 tp2.
  apply triple_SPA_pure. intros tr md [(A5 & A6 & A13 & A15) _].
  apply (triple_SPA_conseq_J segs ok _ (Jp r1 tp)); [intros t md0 (HJ & _ & _); exact HJ|].
  apply (WLerr.wl1_sum ok (Jp r1 tp) rho2 tp2 [] (MSGB msg len) A5 A6).
  - rewrite A13. reflexivity.
  - rewrite A15. symmetry. exact Hlen.
  - rewrite MSG_len. unfold max_write_total. lia.
  - apply Jp_stable.
  - intros k r t tr0 ms md0 msv' HK HMI Hh Hp Hstep.
    exact (Kf_okK r1 tp k r t tr0 ms md0 msv' (Kw_Jp_Kf r1 tp k r t tr0 md0 HK) HMI Hh Hp Hstep).
  - intros k r t tr0 ms md0 x8 HK Hp Ho.
    exact (Kf_okP r1 tp k r t tr0 ms md0 x8 (Kw_Jp_Kf r1 tp k r t tr0 md0 HK) Hp Ho).
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd2 _ _ _ _ HJ).
  - reflexivity.
  - lia.
Qed.

Lemma wl_call_ex : ltac2:(tb__ "0|5|
S1aS4S17Q40A1A1M0S1aG0S50S15S34S15S78R4R3A2M1S73R2R1A5S35S15S7eG1S7S17Q8A1M2A1M3S39Vmsg;Vlen;A2M4SbG2S7fG3G4A2A2A4P5cR2R1S80A6A3Ftp2;Frho2;Ftp;Fr1;").
Proof.
  intros r1 tp rho2 tp2 w Hw. pose proof Hw as [Hsm [(A5 & A6 & A13 & A15) HK]].
  apply (WLerr.wl1_sum_ex (Jp r1 tp) rho2 tp2 [] (MSGB msg len) A6).
  - rewrite A15. symmetry. exact Hlen.
  - rewrite MSG_len. unfold max_write_total. lia.
  - apply Jp_stable.
  - intros r t tr0 md0 [_ [_ (tr00 & HJ & _)]]. exact (Hfd2 _ _ _ _ HJ).
  - reflexivity.
  - lia.
  - exact Hw.
Qed.

Lemma SPA_splits : ltac2:(tb__ "0|0|
S36S1aS4S17Q40A1A1S4fS34S15R4VW;R3R2R1A6S34S15R5S5fVW;VS4;A2R4R3R2A6F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w Hsp. pose proof Hsplits as H. unfold splits_fw, obindW in H.
  destruct (split_obj_at (ax_S W) 0 (SLit (-2296))) as [S1|] eqn:E1; [|discriminate].
  destruct (split_obj_at S1 1 (SLit (-2264))) as [S2|] eqn:E2; [|discriminate].
  destruct (split_obj_at S2 3 (SLit (FERR + 120))) as [S3|] eqn:E3; [|discriminate].
  pose proof (SPA_split segs J rho W 0 (SLit (-2296)) S1 tp w E1 Hsp) as H1.
  pose proof (SPA_split segs J rho (ax_setS W S1) 1 (SLit (-2264)) S2 tp w E2 H1) as H2.
  pose proof (SPA_split segs J rho (ax_setS (ax_setS W S1) S2) 3 (SLit (FERR + 120)) S3 tp w E3 H2) as H3.
  exact (SPA_split segs J rho (ax_setS (ax_setS (ax_setS W S1) S2) S3) 4 (SLit (FERR + 124)) S4 tp w H H3).
Qed.

Lemma facts_rho_wl : ltac2:(tb__ "0|0|
S1aS56S21S25R1A1S3aA3S56S21S25S79R2A1A1S3aA3F_;Fr;").
Proof.
  intros r H. apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) H p Hp) as X.
  unfold facts_fw in Hp. destruct Hp as [<-|[<-|[<-|[]]]]; exact X.
Qed.
Lemma fb_facts : ltac2:(tb__ "0|0|
S0S5S82S21S2eS55A1S3aA3S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma msg_ro : ltac2:(tb__ "0|0|
S32S1S42Z0R1A2S44R1S46S43Vmsg;Vlen;A2Vmsg;A2A2A2S0S5S2bS15S19Q40S43Vmsg;R2A2A2A2S6A3F_;Fk;").
Proof.
  intros k Hk. rewrite <- Hlen in Hk.
  exact (proj1 (rom_bytes_ok_sound segs msg (MSGB msg len) Hrom k ltac:(lia))).
Qed.
Lemma msg_disj : ltac2:(tb__ "0|0|
S1aS56S21S25R1A1S3aA3S56S1bS1bS29S27R3R1A2S9S32S32Vmsg;S43Vmsg;Vlen;A2A4A2Lo;S1fVS4;A1A3F_;Fr;").
Proof.
  intros r HF. apply (objs_farW_disjoint r); [|exact Hmiss].
  pose proof (proj1 (Forall_forall _ _) HF (SPUle (SLit 0x7fff7ff01000) (SVar 10)) ltac:(unfold facts_fw; cbn; tauto)) as H10.
  cbn [holds eval] in H10. rewrite Z_to_bv_small in H10 by (rewrite two64; lia). exact H10.
Qed.

Lemma reshape : ltac2:(tb__ "0|5|
S1aS4S17Q40M0A1M1A1S1aS4fS56S21S25R2A1S3aA3G1S1S42Vmsg;S18G0R1A2M2A2S44G2S43Vmsg;Vlen;A2A2A2S0S8S17Q8A1M3A1S1eR5R2A2SeG3A1A3F_;Fa;S34S15S5aR6R5U0M4A3VW;R4R5R3A6S34S15S5aR7R6G4A3VC;S79R5A1R6R4A6F_;F_;F_;Fw;Frho;Ftp;Fr1;").
Proof.
  intros r1 tp rho w HF HRM Hsp.
  pose proof (SPA_splits _ rho tp w Hsp) as H4.
  unfold C. rewrite <- (ax_setS_twice W S4 Cs).
  eapply (SPA_morphX (Kf r1 tp 0) (Kf r1 tp 0) (ax_setS W S4) Cs rho (rho_wl rho) tp w).
  - cbn [ax_X ax_base ax_setS]. rewrite HXW, HbW, HnC. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - cbn [ax_base ax_setS]. rewrite HbW. reflexivity.
  - cbn [ax_X ax_setS]. rewrite HXW. intros r [<-|[]]. split; reflexivity.
  - cbn [ax_S ax_setS]. intros x Hout Hrm. split; [|reflexivity].
    rewrite <- Hfinish. cbn [ss_objs app_obj]. rewrite <- app_assoc. apply outside_all_app_iff. split.
    + apply outside_all_set_rl; [|exact Hout]. pose proof Hnl4 as X. unfold state_nolist in X.
      apply andb_prop in X as [X _]. apply andb_prop in X as [_ X]. exact X.
    + cbn [app]. unfold outside_all.
      constructor; [|constructor; [|constructor]]; cbn zeta; unfold obj_range, obj_lo_of, obj_hi_of, O_b1z, O_b2r; cbn [ob_base ob_lo ob_hi eval fst snd];
        rewrite !soff_lit_small by lia.
      * rewrite Z_to_bv_small by (unfold EBUF; rewrite two64; lia). lia.
      * rewrite Z_to_bv_small by (rewrite two64; lia). intros Hin. apply Hrm. apply HRM. lia.
  - intros Hsm. rewrite <- Hfinish.
    pose proof (smatch_set_rl segs rho (fwl rho) S4 (virt tp w) Hnl4 Hsm) as H5. change (set_rl rho (fwl rho)) with (rho_wl rho) in H5.
    assert (HF' : Forall (holds (rho_wl rho)) facts_fw) by (apply facts_rho_wl; exact HF).
    assert (Hb1 : smatch segs (rho_wl rho) (app_obj S4 O_b1z) (virt tp w)).
    { unfold app_obj, O_b1z.
      apply (smatch_carve_listobj segs (rho_wl rho) S4 (virt tp w) (SLit EBUF) (SLit 0) (SLit 0) 0 0 (DList 5) 5 (ss_next S4) H5 eq_refl).
      - exact Hswf1.
      - cbn [eval]. rewrite soff_lit_small by lia. reflexivity.
      - cbn [eval]. rewrite soff_lit_small by lia. reflexivity.
      - lia. - lia.
      - cbn [eval]. rewrite Z_to_bv_small by (unfold EBUF; rewrite two64; lia). unfold EBUF. lia.
      - cbn [eval]. rewrite Z_to_bv_small by (unfold EBUF; rewrite two64; lia). unfold EBUF. lia.
      - rewrite rho_wl_5. reflexivity.
      - apply Forall_forall. intros o _. unfold ranges_disjoint. cbn [fst snd]. lia.
      - intros off Hoff _. exfalso. lia.
      - intros off Hoff. exfalso. lia. }
    unfold app_obj at 1. unfold O_b2r.
    apply (smatch_carve_rom segs (rho_wl rho) (app_obj S4 O_b1z) (virt tp w) msg len 6 (ss_next (app_obj S4 O_b1z)) Hb1).
    + rewrite <- Hfinish in HswfC. exact HswfC.
    + lia. + lia. + lia.
    + rewrite rho_wl_6. exact Hlen.
    + intros k Hk. rewrite rho_wl_6. apply (rom_bytes_ok_sound segs msg (MSGB msg len) Hrom). rewrite Hlen. exact Hk.
    + rewrite Hobjs1. apply Forall_app. split; [exact (msg_disj _ HF')|].
      constructor; [|constructor]. unfold obj_range, obj_lo_of, obj_hi_of, O_b1z. cbn [ob_base ob_lo ob_hi eval].
      rewrite !soff_lit_small by lia. unfold ranges_disjoint. cbn [fst snd]. lia.
  - intros HK. exact HK.
  - exact H4.
Qed.

Lemma W_facts : ltac2:(tb__ "0|4|
S36S1aS4S17Q40M0A1M1A1S4fS34S15R4VW;R3R2R1A6S1S56S21S25R4A1S3aA3G1S1S42Vmsg;S18G0R1A2M2A2S44G2S43Vmsg;Vlen;A2A2A2S0S8S17Q8A1M3A1S1eR6R2A2SeG3A1A3F_;Fa;A2F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w Hsp. pose proof (SPA_facts_hold segs J rho W tp w Hsp) as HF. rewrite HfW in HF. split; [exact HF|].
  destruct (SPA_splits J rho tp w Hsp) as [HsmA _]. pose proof (smatchA_smatch segs _ _ _ _ HsmA) as Hsm. cbn [ax_S ax_setS] in Hsm.
  apply (rm_none_ro rho S4 tp w msg (msg + len) Hsm); [ | exact msg_ro | lia | lia].
  apply msg_disj. rewrite <- Hf4. exact (smatch_facts segs _ _ _ Hsm).
Qed.

Definition rho_fin (rho0 rho3 : valuation) (ms : machine_state) (md : Model) (tp : list word) : valuation := ltac2:(tb__ "0|0|
S8cS87S8bVrho3;SaS1bS6aSaS1bS6cVmsg;Vlen;A2S7S1bA1A3A3S68Vmd;Vtp;Vms;A3A3S23Vrho0;A1A2Vsp;A2").

Lemma cleanup : ltac2:(tb__ "0|2|
S1aS4S17Q40A1A1M0S4S49A1M1S48OFx2;Fx1;Fx0;Fx;S1aS1aG0G1S7cS48S1aS1aG0G1S48RcR5R3R2R1A4RdR5R4R3R2A4F_;Fmd';Ftr';Ft;Fr';Fr;S34S15R8VF;R6R5S9G1S76R4S77R3R2A2A4A6S34S15R9S3dS7aR8R7R4R3R6A5R6S9G1S76R5S77R4R3A2A4A6F_;F_;Fmd;Fms;Ftr;Ftp;Frho3;Frho0;FJ;").
Proof.
  intros J rho0 rho3 tp tr ms md HJi Hsp.

  pose proof (SPA_x_sub segs J rho3 F [] tp _ ltac:(intros r Hr; destruct Hr) Hsp) as H0.
  assert (E0 : ax_setX F [] = axc (ax_S F)) by (unfold ax_setX, axc; rewrite HbF; reflexivity). rewrite E0 in H0.

  assert (H1 : SPA segs J (axc G1) rho3 tp (tr, mkCfg ms md)).
  { apply (SPA_morph J J (axc (ax_S F)) G1 rho3 rho3 tp _ eq_refl); [cbn [ax_base axc]; rewrite HnG1; reflexivity | | intros HK; exact HK | exact H0].
    intros Hsm. exact (smatch_xforms segs XS1 rho3 (ax_S F) G1 _ Hxs1 Hsm). }

  pose proof (SPA_unobj segs J rho3 (axc G1) (firstn 11 (ss_objs G1)) [O_b1z; O_b2r msg len] tp tr ms md
                HobjsG1 H1 ltac:(intros HK; exact (HJi _ _ _ _ _ HK))) as H2.
  cbn zeta in H2. cbn [ax_S axc] in H2. pose proof Hdrop as Hd. unfold drop2 in Hd. rewrite Hd in H2.
  set (rho4 := rho_absorb rho3 [O_b1z; O_b2r msg len] (vms md tp ms)) in H2.
  change (ax_setS (axc G1) G2) with (axc G2) in H2.

  assert (H3 : SPA segs J (axc G3) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_morph J J (axc G2) G3 rho4 rho4 tp _ eq_refl); [cbn [ax_base axc]; rewrite HnG3; reflexivity | | intros HK; exact HK | exact H2].
    intros Hsm. exact (smatch_xforms segs XS2 rho4 G2 G3 _ Hxs2 Hsm). }

  assert (H4 : SPA segs J (axc G3) (set_rl rho4 (rl rho0)) tp (tr, mkCfg ms md)).
  { apply (SPA_morph J J (axc G3) G3 rho4 (set_rl rho4 (rl rho0)) tp _ eq_refl); [cbn [ax_base axc]; rewrite HnG3; reflexivity | | intros HK; apply (HJi _ _ _ _ _ HK) | exact H3].
    intros Hsm. exact (smatch_set_rl segs rho4 (rl rho0) G3 _ HnlG3 Hsm). }

  unfold rho_fin. destruct H4 as [Hsm4 HK4]. split; [| apply (HJi _ _ _ _ _ HK4)].
  eapply smatchA_entails; [exact Hent | exact Hsm4].
Qed.

Lemma rho_fin_agree : ltac2:(tb__ "0|6|
S1aS1aS1aS4S17Q40M0A1M1A1S4S49A1M2S7cS48S26S55R7R6A3S33S8aR1S55A2S0G1S24R8R2A2S24R9R2A2A3F_;Fi;G1S0S8S17Q8A1M3A1M4S1eR8R1A2S1eR9R1A2A3Fa;G1S1S42Vmsg;S18G0R1A2M5A2S44G5S43Vmsg;Vlen;A2A2A2S0G4S1eRbR2A2SeG3A1A3F_;Fa;S20S15R9S5dVF;A1S67R8S9G2S76R7S77R6R5A2A4A2A4S26S55RcS7aRcRaR7R6R9A5A3F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho3;Frho1;Frho0;").
Proof.
  intros rho0 rho1 rho3 tp tr ms md Hag01 Hrw Hrm HRM Hsm3. destruct Hag01 as (A & B & Cc).
  unfold rho_fin. split; [|split].
  - intros i Hi. cbn [rw rho_sub set_rl rho_absorb].
    rewrite (wsub_get_id sp NF i Hspid Hi). cbn. rewrite (Hrw i Hi). apply A. exact Hi.
  - intros l. reflexivity.
  - intros a. cbn [rm rho_sub set_rl rho_absorb].
    destruct (in_ranges_dec rho3 [O_b1z; O_b2r msg len] a) as [Hin|Hnin]; [| rewrite Hrm; apply Cc].
    destruct Hin as (o & [<-|[<-|[]]] & Hr); unfold obj_range, obj_lo_of, obj_hi_of, O_b1z, O_b2r in Hr; cbn [ob_base ob_lo ob_hi eval fst snd] in Hr;
      rewrite !soff_lit_small in Hr by lia; rewrite Z_to_bv_small in Hr by (unfold EBUF; rewrite two64; lia).
    + exfalso. lia.
    + rewrite Cc, (HRM a ltac:(lia)). symmetry. apply (vms_none_ro rho3 (ax_S F) tp tr ms md a Hsm3).
      replace a with (Z_to_bv 64 (msg + (bv_unsigned a - msg))) by (apply bv_eq; rewrite Z_to_bv_small; [lia | rewrite two64; lia]).
      apply msg_ro. lia.
Qed.

Theorem fw_sum_inst : ltac2:(tb__ "0|0|
S1aS4S17Q40A1A1S51S15Vok;S34S15VJ0;S3bVmsg;Vlen;A2R2R1A5S35S15S59SbS17Q8A1S39Vmsg;Vlen;A2A2A1S55R2R1S3cA6A4Ftp;Frho;").
Proof.
  intros rho tp.

  eapply (runA_tr segs ok FUEL_FW CUTS_FW (Pre_fw msg len) _ J0 rho tp); [exact HrunW | reflexivity | apply okK_J0 | exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].

  apply (triple_pre ok _ _ _ (fun w Hw => W_facts J0 rho1 tp w Hw)). intros [HF1 HRM].
  eapply triple_conseq with (P := SPA segs (Kf rho1 tp 0) C (rho_wl rho1) tp); [ | intros w Hw; exact Hw |].
  { intros w Hw. apply (reshape rho1 tp rho1 w HF1 HRM). destruct Hw as [Hsm HJ]. split; [exact Hsm|]. split; [reflexivity|]. apply Kw0_of_J0. exact HJ. }

  apply (call_soundA segs ok (Kf rho1 tp 0) (Jp rho1 tp) (WLerr.Kw (Jp rho1 tp) [] (MSGB msg len) (length (WLerr.MSG [] (MSGB msg len))))
           (Kf rho1 tp (length (MSGB msg len))) C WLerrS.Pre_wl1 s R WLerr.Posts_wl _ (rho_wl rho1) tp Hefr).
  - exact Hchk.
  - intros rho2 tp2. apply wl_call.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15. cbn [eval].
    split; [apply rho_wl_5|]. split; [apply rho_wl_6|]. split; [reflexivity|].
    apply Z_to_bv_small. rewrite two64. lia.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp_Kf in HK'. rewrite MSG_len in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite HT.
    apply triple_SPA_pure. intros tr md [Et _]. subst tpL.
    apply (triple_SPA_conseq_J segs ok _ (Kf rho1 tp (length (MSGB msg len)))); [intros t md0 (HJ & _ & _); exact HJ|].
    assert (HF' : Forall (holds rho') facts_fw).
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree (ss_next (ax_S C)) (rho_wl rho1) rho' p Hag'
               ltac:(unfold C; cbn [ax_S ax_setS]; rewrite HnC; exact (proj1 (forallb_forall _ _) fb_facts p Hp)))).
      exact (proj1 (Forall_forall _ _) (facts_rho_wl rho1 HF1) p Hp). }
    eapply triple_conseq with (P := SPA segs (Kf rho1 tp (length (MSGB msg len))) Tf rho' tp); [ | intros w Hw; exact Hw |].
    { intros w [Hsm HJ]. split; [|exact HJ]. rewrite <- HTf. apply smatchA_add_facts; [exact Hsm | exact HF' | rewrite HnT; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. }

    eapply (runA_tr segs ok FUEL_FW CUTS_FW Tf _ (Kf rho1 tp (length (MSGB msg len))) rho' tp); [exact HrunF | exact HlTf | apply Kf_okK | apply Kf_stable |].
    intros L2 rho3 [<-|[]] Hag3. cbn [la_state]. rewrite HnTf in Hag3.

    intros n Hg w [Hsm3 HK3]. destruct w as [tr3 [ms3 md3]].
    pose proof (cleanup (Kf rho1 tp (length (MSGB msg len))) rho rho3 tp tr3 ms3 md3 ltac:(intros r r' t tr' md' HK; exact HK) (conj Hsm3 HK3)) as [HsmP HKP].
    assert (HagF : agree_below NF rho (rho_fin rho rho3 ms3 md3 tp)).
    { apply (rho_fin_agree rho rho1 rho3 tp tr3 ms3 md3 Hag1).
      - intros i Hi. destruct Hag3 as (A3 & _ & _). destruct Hag' as (A' & _ & _).
        assert (Hi' : (i < 125)%positive) by (unfold NF in Hi; lia).
        rewrite <- (A3 i Hi'). unfold C in A'. cbn [ax_S ax_setS] in A'. rewrite HnC in A'. rewrite <- (A' i Hi). reflexivity.
      - intros a. destruct Hag3 as (_ & _ & C3). destruct Hag' as (_ & _ & C'). rewrite <- (C3 a), <- (C' a). reflexivity.
      - exact HRM.
      - exact (smatchA_smatch segs _ _ _ _ Hsm3). }
    apply Hg.
    exists (mkLeafA P_fw RsCut), (rho_fin rho rho3 ms3 md3 tp). split; [left; reflexivity|]. split; [exact HagF|].
    split; [exact HsmP|]. cbn [la_state w_tr w_cfg cfg_model]. destruct HKP as [_ (tr0 & HJ0 & ->)].
    exists tr0. split; [|reflexivity].
    eapply Hst0; [ | apply mat_equiv_refl | exact HJ0].
    eapply agree_below_trans; [apply agree_below_sym; exact Hag1 | exact HagF].
Qed.

Theorem fw_sum_ex_inst : ltac2:(tb__ "0|0|
S1aS4S17Q40A1A1S50S15S34S15VJ0;S3bVmsg;Vlen;A2R2R1A5S35S15S59SbS17Q8A1S39Vmsg;Vlen;A2A2A1S55R2R1S3cA6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply (erunA_tr segs FUEL_FW CUTS_FW (Pre_fw msg len) _ J0 rho tp); [exact HrunW | reflexivity | exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply (etriple_pre _ _ _ (fun w Hw => W_facts J0 rho1 tp w Hw)). intros [HF1 HRM].
  eapply etriple_conseq with (P := SPA segs (Kf rho1 tp 0) C (rho_wl rho1) tp); [ | intros w Hw; exact Hw |].
  { intros w Hw. apply (reshape rho1 tp rho1 w HF1 HRM). destruct Hw as [Hsm HJ]. split; [exact Hsm|]. split; [reflexivity|]. apply Kw0_of_J0. exact HJ. }
  apply (call_completeA segs (Kf rho1 tp 0) (Jp rho1 tp) (WLerr.Kw (Jp rho1 tp) [] (MSGB msg len) (length (WLerr.MSG [] (MSGB msg len))))
           (Kf rho1 tp (length (MSGB msg len))) C WLerrS.Pre_wl1 s R WLerr.Posts_wl _ (rho_wl rho1) tp Hefr).
  - exact Hchk.
  - intros rho2 tp2. apply wl_call_ex.
  - intros tr ms md Hsm [_ HK]. split; [| split; [reflexivity | exact HK]].
    unfold WLF. cbn [rl rw rho_sub rho_absorb]. rewrite S13, S15. cbn [eval].
    split; [apply rho_wl_5|]. split; [apply rho_wl_6|]. split; [reflexivity|].
    apply Z_to_bv_small. rewrite two64. lia.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HK'. apply Kw_Jp_Kf in HK'. rewrite MSG_len in HK'. exact HK'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite HT.
    intros w0 [Hsm0 [Et HK0]]. subst tpL. revert w0 Hsm0 HK0.
    assert (HF' : Forall (holds rho') facts_fw).
    { apply Forall_forall. intros p Hp.
      apply (proj1 (holds_agree (ss_next (ax_S C)) (rho_wl rho1) rho' p Hag'
               ltac:(unfold C; cbn [ax_S ax_setS]; rewrite HnC; exact (proj1 (forallb_forall _ _) fb_facts p Hp)))).
      exact (proj1 (Forall_forall _ _) (facts_rho_wl rho1 HF1) p Hp). }
    assert (HE : etriple segs (SPA segs (Kf rho1 tp (length (MSGB msg len))) Tf rho' tp) (LQA segs (Kw (length (MSGB msg len))) NF rho tp Posts_fw)).
    { eapply (erunA_tr segs FUEL_FW CUTS_FW Tf _ (Kf rho1 tp (length (MSGB msg len))) rho' tp); [exact HrunF | exact HlTf | apply Kf_stable |].
      intros L2 rho3 [<-|[]] Hag3. cbn [la_state]. rewrite HnTf in Hag3.
      intros w [Hsm3 HK3]. destruct w as [tr3 [ms3 md3]]. exists (tr3, mkCfg ms3 md3). split; [apply wsteps_refl|].
      pose proof (cleanup (Kf rho1 tp (length (MSGB msg len))) rho rho3 tp tr3 ms3 md3 ltac:(intros r r' t tr' md' HK; exact HK) (conj Hsm3 HK3)) as [HsmP HKP].
      assert (HagF : agree_below NF rho (rho_fin rho rho3 ms3 md3 tp)).
      { apply (rho_fin_agree rho rho1 rho3 tp tr3 ms3 md3 Hag1).
        - intros i Hi. destruct Hag3 as (A3 & _ & _). destruct Hag' as (A' & _ & _).
          assert (Hi' : (i < 125)%positive) by (unfold NF in Hi; lia).
        rewrite <- (A3 i Hi'). unfold C in A'. cbn [ax_S ax_setS] in A'. rewrite HnC in A'. rewrite <- (A' i Hi). reflexivity.
        - intros a. destruct Hag3 as (_ & _ & C3). destruct Hag' as (_ & _ & C'). rewrite <- (C3 a), <- (C' a). reflexivity.
        - exact HRM.
        - exact (smatchA_smatch segs _ _ _ _ Hsm3). }
      exists (mkLeafA P_fw RsCut), (rho_fin rho rho3 ms3 md3 tp). split; [left; reflexivity|]. split; [exact HagF|].
      split; [exact HsmP|]. cbn [la_state w_tr w_cfg cfg_model]. destruct HKP as [_ (tr0 & HJ0 & ->)].
      exists tr0. split; [|reflexivity].
      eapply Hst0; [ | apply mat_equiv_refl | exact HJ0].
      eapply agree_below_trans; [apply agree_below_sym; exact Hag1 | exact HagF]. }
    intros w0 Hsm0 HK0. apply HE. split; [| split; [reflexivity | exact HK0]].
    rewrite <- HTf. apply smatchA_add_facts; [exact Hsm0 | exact HF' | rewrite HnT; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
Qed.
End Inst.

Local Ltac inst k :=
  lazymatch k with
  | 1 => apply (fw_sum_inst W_1 S4_1 Cs_1 s_1 R_1 T_1 Tf_1 F_1 G1_1 G2_1 G3_1 sp_1)
  | 2 => apply (fw_sum_inst W_2 S4_2 Cs_2 s_2 R_2 T_2 Tf_2 F_2 G1_2 G2_2 G3_2 sp_2)
  | 3 => apply (fw_sum_inst W_3 S4_3 Cs_3 s_3 R_3 T_3 Tf_3 F_3 G1_3 G2_3 G3_3 sp_3)
  end.
Local Ltac einst k :=
  lazymatch k with
  | 1 => apply (fw_sum_ex_inst W_1 S4_1 Cs_1 s_1 R_1 T_1 Tf_1 F_1 G1_1 G2_1 G3_1 sp_1)
  | 2 => apply (fw_sum_ex_inst W_2 S4_2 Cs_2 s_2 R_2 T_2 Tf_2 F_2 G1_2 G2_2 G3_2 sp_2)
  | 3 => apply (fw_sum_ex_inst W_3 S4_3 Cs_3 s_3 R_3 T_3 Tf_3 F_3 G1_3 G2_3 G3_3 sp_3)
  end.

Local Ltac side k :=
  lazymatch k with
  | 1 => destruct shapeW_1 as (?HnW & ?HXW & ?HbW & ?HfW & _); destruct shapeC_1 as (?Hs1 & ?HsC & ?HnC & ?Hf4 & ?Hmiss & ?Hrom & ?Hnl4 & ?Hn4 & ?Ho1);
         destruct shapeS_1 as (_ & ?S13 & _ & ?S15); destruct shapeT_1 as (?HnT & ?HlTf & ?HnTf); destruct shapeF_1 as (_ & ?HnF & ?HbF & ?HoG1 & ?HnG1 & ?HnG3 & ?HnlG3 & ?Hspid)
  | 2 => destruct shapeW_2 as (?HnW & ?HXW & ?HbW & ?HfW & _); destruct shapeC_2 as (?Hs1 & ?HsC & ?HnC & ?Hf4 & ?Hmiss & ?Hrom & ?Hnl4 & ?Hn4 & ?Ho1);
         destruct shapeS_2 as (_ & ?S13 & _ & ?S15); destruct shapeT_2 as (?HnT & ?HlTf & ?HnTf); destruct shapeF_2 as (_ & ?HnF & ?HbF & ?HoG1 & ?HnG1 & ?HnG3 & ?HnlG3 & ?Hspid)
  | 3 => destruct shapeW_3 as (?HnW & ?HXW & ?HbW & ?HfW & _); destruct shapeC_3 as (?Hs1 & ?HsC & ?HnC & ?Hf4 & ?Hmiss & ?Hrom & ?Hnl4 & ?Hn4 & ?Ho1);
         destruct shapeS_3 as (_ & ?S13 & _ & ?S15); destruct shapeT_3 as (?HnT & ?HlTf & ?HnTf); destruct shapeF_3 as (_ & ?HnF & ?HbF & ?HoG1 & ?HnG1 & ?HnG3 & ?HnlG3 & ?Hspid)
  end.

Theorem fwerr_sum : ltac2:(tb__ "0|0|
S81SfS32S32A2S9S32S32Vmsg;Vlen;A4S3eA3S1aS4S17Q40A1A1S51S15Vok;S34S15VJ0;S3bVmsg;Vlen;A2R2R1A5S35S15S59SbS17Q8A1S39Vmsg;Vlen;A2A2A1S55R2R1S3cA6A4Ftp;Frho;F_;").
Proof.
  intros Hin rho tp. unfold fw_msgs in Hin.
  destruct Hin as [E|[E|[E|[]]]]; injection E as El Em;
    [ side 1; inst 1 | side 2; inst 2 | side 3; inst 3 ]; try assumption; try reflexivity;
    try rewrite <- El; try rewrite <- Em; try assumption; try reflexivity;
    first [ exact runW_1 | exact runW_2 | exact runW_3 | exact splits_1 | exact splits_2 | exact splits_3
          | exact finish_1 | exact finish_2 | exact finish_3 | exact efr_1 | exact efr_2 | exact efr_3
          | exact chk_1 | exact chk_2 | exact chk_3 | exact T_1_eq | exact T_2_eq | exact T_3_eq
          | exact Tf_1_eq | exact Tf_2_eq | exact Tf_3_eq | exact runF_1 | exact runF_2 | exact runF_3
          | exact xs1_1 | exact xs1_2 | exact xs1_3 | exact drop2_1 | exact drop2_2 | exact drop2_3
          | exact xs2_1 | exact xs2_2 | exact xs2_3 | exact ent_1 | exact ent_2 | exact ent_3
          | (vm_compute; reflexivity) | lia | (split; lia) ].
Qed.

Theorem fwerr_sum_ex : ltac2:(tb__ "0|0|
S81SfS32S32A2S9S32S32Vmsg;Vlen;A4S3eA3S1aS4S17Q40A1A1S50S15S34S15VJ0;S3bVmsg;Vlen;A2R2R1A5S35S15S59SbS17Q8A1S39Vmsg;Vlen;A2A2A1S55R2R1S3cA6A3Ftp;Frho;F_;").
Proof.
  intros Hin rho tp. unfold fw_msgs in Hin.
  destruct Hin as [E|[E|[E|[]]]]; injection E as El Em;
    [ side 1; einst 1 | side 2; einst 2 | side 3; einst 3 ]; try assumption; try reflexivity;
    try rewrite <- El; try rewrite <- Em; try assumption; try reflexivity;
    first [ exact runW_1 | exact runW_2 | exact runW_3 | exact splits_1 | exact splits_2 | exact splits_3
          | exact finish_1 | exact finish_2 | exact finish_3 | exact efr_1 | exact efr_2 | exact efr_3
          | exact chk_1 | exact chk_2 | exact chk_3 | exact T_1_eq | exact T_2_eq | exact T_3_eq
          | exact Tf_1_eq | exact Tf_2_eq | exact Tf_3_eq | exact runF_1 | exact runF_2 | exact runF_3
          | exact xs1_1 | exact xs1_2 | exact xs1_3 | exact drop2_1 | exact drop2_2 | exact drop2_3
          | exact xs2_1 | exact xs2_2 | exact xs2_3 | exact ent_1 | exact ent_2 | exact ent_3
          | (vm_compute; reflexivity) | lia | (split; lia) ].
Qed.
End Fw.
