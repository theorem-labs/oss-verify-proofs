(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "nat"; "bool"; "true"; "list"; "nil"; "app"; "false"; "option"; "None"; "Some"; "andb"; "orb"; "fst"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "valuation"; "sobj"; "SVar"; "rw"; "swf"; "FcsrFrm0"; "eval"; "mkSS"; "agree_below"; "enc_bytes"; "rm"; "sprop_below"; "holds"; "ob_base"; "ob_hi"; "ob_lo"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "AE_A"; "KcA"; "L_free_null"; "Pre_free_nullI"; "JL_free_null"; "J_free_null_preT"; "Kc_ok"; "UStopLeOrPc"; "unwind_factsS"; "free_depth"; "pre_facts"; "ulink"; "A_globals"; "Wcan"; "stack_win"; "unwind_objs"; "V_FREE_A1"; "ae_free"; "ae_ret_free"; "base_sv"; "chain_facts"; "chain_pre"; "client_addrA"; "link_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "mkAX"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_internal_inited"; "ag_thread"; "ag_ctx"; "ageom"; "ag_stack_bottom"; "ag_stack_top"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "pre_fregs"; "setregs"; "cut_regs"; "pre_regs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "leb"; "ltb"; "add"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "vCTX"; "vT"; "vBOT"; "vTOP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull.FN"; "stR"; "N_fn"; "s_fn"; "sa_fn"; "rho1_of"; "rt_zone2"; "sb_fn"; "stK"; "img_zone2_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "F_geom_fn"; "E_fn"; "P0_fn"; "RT_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "geom_ok"; "AInvA"; "IA_BEG"; "IA_END"; "fs_footb"; "fs_inv"; "live_sep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.Lists.List"; "forallb"; "In"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "withGA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "G0"; "RTC_A"; "bview"; "cells_footb"; "rtc_cells_img"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_in_view"; "rd_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "K_HIGH_MEM_END"; "PG"; "forall_rangeZ"; "kMallocContextSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM"; "rt_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue"; "coverb"; "spec_range"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma rm_rho_sub' : ltac2:(tb__ "0|0|
S17S95S27S4aQ40A1SaS4aQ8A1A1F_;S21S94R2R1A2A1S21R2A1A3Fs;Frho;").
Proof. reflexivity. Qed.

Lemma nth0_enc1_one' : ltac2:(tb__ "0|3|
S27S4aQ8M0A1M1S8aG1U0S20U1S49Q40Z1M2A2A2S49G0Z0A2A4S49G0G2A2A3").
Proof. reflexivity. Qed.
Lemma nth0_enc1_zero' : ltac2:(tb__ "0|4|
S27S4aQ8M0A1M1S8aG1U0S20U1S49Q40Z0M2A2A2S49G0G2A2M3A4G3A3").
Proof. reflexivity. Qed.
Lemma nth_enc8_zero' : ltac2:(tb__ "0|5|
S3S9cR1U8M0A2S27S4aQ8M1A1M2S8aG2R2S20G0S49Q40Z0M3A2A2S49G1G3A2M4A4G4A3F_;Fj;").
Proof. intros j Hj. do 8 (destruct j as [|j]; [reflexivity|]). lia. Qed.

Lemma chain_facts_bases : ltac2:(tb__ "0|3|
S17S14S6S37A1S89S15S23R3A1S40R2R1A2A3S5bS4bQ40M0S1dR4R3A2A2S60Z2Z2fA2M1A2S89S18S18S28S28S5bS4bG0S1dR6R5A2A2S4bG0S1dR6S24R1A1A2A2M2A2S5bG2G1A2A2S28S27S14S26R1A1S16N10A1A3S27S14S25R1A1S16Z0A1A3A2A2Lo;S43R4R3A2A3F_;F_;FW;Fbp;Frho;").
Proof.
  intros rho bp W. revert bp. induction W as [|[nbp pc] W IH]; intros bp HF Hbp; cbn [link_objs]; [constructor|].
  constructor.
  - cbn [ob_base ob_lo ob_hi]. repeat split; try reflexivity; lia.
  - destruct W as [|[nbp' pc'] W'].
    + constructor.
    + cbn [chain_facts] in HF. apply Forall_inv_tail in HF as HF0. pose proof (Forall_inv HF) as F1. pose proof (Forall_inv HF0) as F2.
      apply Forall_inv_tail in HF0.
      cbn [holds eval] in F1, F2. rewrite add_val, !u64_lit in F1 by lia. rewrite u64_lit in F2 by lia.
      pose proof (urange (eval rho bp)) as UB.
      assert (LE : bv_unsigned (eval rho bp) <= bv_unsigned (eval rho nbp) <= 2 ^ 47) by (rewrite Z.mod_small in F1 by lia; lia).
      eapply Forall_impl; [|apply (IH nbp HF0); lia].
      intros o (B & L & Hh). repeat split; try assumption; lia.
Qed.

Lemma chain_pre_in : ltac2:(tb__ "0|0|
S6S37A1S15S88S15R1S41R2A1A3S88S15R2S34R3S2bA2A3F_;Fp;FW;").
Proof.
  intros W p H. destruct W as [|l W']; [destruct H|].
  unfold unwind_factsS, unwind_facts. unfold chain_pre in H. apply in_or_app. left. exact H.
Qed.

Section FN.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Hypothesis HCST2 : ltac2:(tb__ "0|0|
S11S96VCST;R1A2S28S29S28S5bS81R2A2S5cR2S82A2A2A1S29S28S5bZ180e88R2A2S5cR2Z180e8cA2A2A1A2F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S31VAInv;VW;Vst;VA;VKc;A5").

Definition rho1_of (A : AA) (rho : valuation) : valuation := ltac2:(tb__ "0|3|
S4dVA;A1S51S75Vrho;S1S2S12S4aQ40M0A1M1A2M2S0S12G1P97S49G0S4fR1A1A2A4S1G2S0S12G1P98S49G0S50R1A1A2A4S1G2S0S12G1P99S49G0S53R1A1A2A4S1G2S0S12G1P9aS49G0S52R1A1A2A4S7G2A1A3A3A3A3A2TG;").

Lemma rho1_agree : ltac2:(tb__ "0|0|
S4cS17S1fS56R1S6eR2R1A2A3Frho;FA;").
Proof.
  intros. apply agree_below_rho_sets. intros j v Hin. cbn in Hin. unfold NF.
  repeat (destruct Hin as [E|Hin]; [injection E; intros; subst; cbv; discriminate|]). destruct Hin.
Qed.

Lemma J_agree : ltac2:(tb__ "0|0|
S6S37A1S4cS2dS17S17S6S4aQ40A1A1S6S92A1S91S1fS56R5R4A3VJ;R9S2bR8R7R6R4R3R2A8VJ;RaS2bR9R8R6R5R4R3A8F_;F_;Fmd;Ftr;Ftp;Frho';Frho;FKc;FA;FW;").
Proof.
  intros W A Kc rho rho' tp tr md (Hw & Hl & Hm) (HA & HU & HK & Htp & Htop).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  split; [unfold AInv, AInvA in *; rewrite Erm; exact HA|]. split; [|split; [exact HK|split]].
  - unfold unwind_stopJ in *. destruct W; exact I.
  - unfold tp_ok in *. rewrite <- (Hw 24%positive) by (unfold NF; lia). exact Htp.
  - unfold top_high in *. rewrite <- (Hw 10%positive) by (unfold NF; lia). rewrite <- (Hw V_DEPTH) by (unfold NF, V_DEPTH; lia). exact Htop.
Qed.

Lemma J_stableA : ltac2:(tb__ "0|0|
S6S37A1S4cS2dS32R1A1S64Vsegs;S76VJ;R4S2bR3R2A4A3F_;FKc;FA;FW;").
Proof.
  intros W A Kc HKc rho rho' tp tr md md' Hag Hme HJ.
  pose proof (J_agree W A Kc rho rho' tp tr md ltac:(eapply agree_below_le; [|exact Hag]; cbv; discriminate) HJ) as (HA & HU & HK & Htp & Htop).
  split; [|split; [exact HU | split; [| split; [exact Htp | exact Htop]]]].
  - apply (AInvA_mat segs A rho' tp md md'); [exact HA | exact Hme].
  - destruct Hme as ((mat' & ->) & _). rewrite with_vm_backing_with_vm. apply HKc. exact HK.
Qed.

Definition N_fn : list carve_spec := ltac2:(tb__ "0|1e|
S1S2S2S2S14S11A2M0S11A2M1S6S2S2S11S3A2M2S14A2M3A1M4A2M5S0G1G4S0G0S11S0S14S11S16Z0M6A1M7Z180e88M8A4Z180e8aA4S1G3S0G2S14S0S11S3G8U1M9A4S16Z1A1MaA4S1G3S0G2S14S0S11S3Z180e89G9A4G7A4S7G3A1MbA3A3A4S1G5S0G1G4S0G0S11S0S14S11G7Zf2608McA4Zf2610A4S1G3S0G2S14S0S11S3GcU8MdA4G7A4GbA3A4S1G5S0G1G4S0G0S11S0S14S11G7Zf20d8MeA4Zf20daA4S1G3S0G2S14S0S11S3GeG9A4GaA4S1G3S0G2S14S0S11S3Zf20d9G9A4GaA4GbA3A3A4S1G5S0G1G4S0G0S11S0S14S11G7Zf20e0MfA4Zf20f8A4S1G3S0G2S14S0S11S3GfGdA4S16Sa2A1A4S1G3S0G2S14S0S11S3Zf20e8GdA4G7A4S1G3S0G2S14S0S11S3Zf20f0GdA4G7A4GbA3A3A3A4S1G5S0G1G4S0G0S11S0S14S11G7Zf0c5cM10A4Zf0c5dA4S1G3S0G2S14S0S11S3G10G9A4GaA4GbA3A4S1G5S0G1G4S0G0S11S0S14S11G7Zf0c60M11A4Zf0c61A4S1G3S0G2S14S0S11S3G11G9A4GaA4GbA3A4S1G5S0G1G4S0G0S11S0S14S11G7Zf0c64M12A4Zf0c68A4S1G3S0G2S14S0S11S3G12U4M13A4G7A4GbA3A4S1G5S0G1G4S0G0S11S0S14S11G7Z624560M14A4Z624568A4S1G3S0G2S14S0S11S3G14GdA4S16Z645960M15A1A4GbA3A4S1G5S0G1G4S0G0S11S0S14S11G7G15A4Z645968A4S1G3S0G2S14S0S11S3G15GdA4S66A4GbA3A4S1G5S0G1G4S0G0S11S0S14S11S66Z8M16A4ZcA4S1G3S0G2S14S0S11S3G16G13A4G7A4GbA3A4S1G5S0G1G4S0G0S11S0S14S11S66Z98M17A4Za0A4S1G3S0G2S14S0S11S3G17GdA4S67A4GbA3A4S1G5S0G1G4S0G0S11S0S14S11S67G6A4Z18A4S1G3S0G2S14S0S11S3G6GdA4S66A4S1G3S0G2S14S0S11S3G16GdA4S69A4S1G3S0G2S14S0S11S3Z10GdA4S68A4GbA3A3A3A4S1G5S0G1G4S0G0S11S0S14S11S67Z28M18A4Z29A4S1G3S0G2S14S0S11S3G18G9A4G7A4GbA3A4S1G5S0G1G4S0G0S11S0S14S11S67Zc60M19A4Zc61A4S1G3S0G2S14S0S11S3G19G9A4G7A4GbA3A4S1G5S0G1G4S0G0S11S0S14S11G7Z182f4aM1aA4Z182f4bA4S1G3S0G2S14S0S11S3G1aG9A4GaA4GbA3A4S1G5S0G1G4S0G0S11S0S14S11G7Z180e98M1bA4Z180e9cA4S1G3S0G2S14S0S11S3G1bG13A4G7A4GbA3A4S1G5S0G1G4S0G0S11S0S14S11G7Z180ea0M1cA4Z180ea8A4S1G3S0G2S14S0S11S3G1cGdA4S16Sa3A1A4GbA3A4S1G5S0G1G4S0G0S11S0S14S11G7Zf20fcM1dA4Zf2100A4S1G3S0G2S14S0S11S3G1dG13A4S16Sa5A1A4GbA3A4S7G5A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma N_fn_ok : ltac2:(tb__ "0|0|
S27S6S18A1S8bS73S18S74S6bA4S7eA3").
Proof. reflexivity. Qed.

Definition sa_fn (W : list ulink) : sstate := ltac2:(tb__ "0|1|
S1eS3dS2cA1S58S5aS1S2S3S14A2M0S0S3S14U4S16S65A1A4S1G0S0S3S14UaS16Z0A1A4S1G0S0S3S14UbS19S3cA1A4S7G0A1A3A3A3A2S57S1cSbS14A1S1S18S3aS8S18S3bVW;A1S38A3A3S8S15S34VW;S2bA2S36S35A1A3S56S9A9").
Definition sb_fn (W : list ulink) : sstate := ltac2:(tb__ "0|1|
S1eS3dS2cA1S58S5aS1S2S3S14A2M0S0S3S14U4S16S65A1A4S1G0S0S3S14UaS16Z0A1A4S1G0S0S3S14UbS19S3cA1A4S7G0A1A3A3A3A2S57S1cSbS14A1S8S18S1S18S3aS8S18S3bVW;A1S38A3A3S7eA3S8S15S34VW;S2bA2S36S35A1A3S7aS9A9").

Lemma fs_footb_img : ltac2:(tb__ "0|0|
S51S11S7fR2A1S5cR2Z646000A2S27S4S83R4R3A2S9A3F_;F_;Fz;FG;").
Proof.
  intros G z HG Hz. pose proof (geom_old _ HG) as (G1 & G2 & G3 & _). unfold IMG_HI in G2. rewrite FS_total_val in G3.
  apply fs_footb_false_intro; rewrite ?FS_frames_off_val, ?FS_total_val, ?FS_kFlagsOffset_val; unfold Sh, SHADOW_OFF; lia.
Qed.
Lemma fs_footb_thread : ltac2:(tb__ "0|1|
S51S11S7fR2A1S28S5bS4fR3A1M0R2A2S5cR2S5fG0Z1000A2A2A2S27S4S83R4R3A2S9A3F_;F_;Fz;FG;").
Proof.

  intros G z HG Hz. pose proof (geom_nums G HG) as (F1 & F2 & F0 & T1 & T2 & T0 & _ & _ & _ & _ & _ & _ & _ & TG).
  rewrite FS_total_val in *. unfold IMG_HI in *.
  assert (SU : Sh (ag_fsb G + 11571200) <= 17594333495296).
  { unfold Sh, SHADOW_OFF. pose proof (Z.div_le_upper_bound (ag_fsb G + 11571200) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  assert (SL : 2147450880 <= Sh (ag_fsb G + FS_frames_off)) by (unfold Sh, SHADOW_OFF; rewrite FS_frames_off_val; pose proof (Z.div_pos (ag_fsb G + 36864) 8); lia).
  pose proof (proj1 (proj2 (geom_bands G HG))) as TB. pose proof (proj1 (geom_seps G HG)) as Q1.
  rewrite FS_total_val in *. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in TB.
  apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_kFlagsOffset_val; clear -Hz T1 T2 TG SU SL TB Q1; lia.
Qed.

Local Ltac civ_try2F HR n :=
  eapply (civ_nth2 _ _ n); [exact HR | reflexivity | unfold fs_log_cell, fs_needs_gc_cell; reflexivity | unfold fs_log_cell, fs_needs_gc_cell; lia | unfold fs_log_cell, fs_needs_gc_cell; lia].
Local Ltac civ_any2F HR := first [ civ_try2F HR 43%nat | civ_try2F HR 44%nat | civ_try2F HR 45%nat | civ_try2F HR 46%nat | civ_try2F HR 47%nat | civ_try2F HR 48%nat | civ_try2F HR 49%nat | civ_try2F HR 50%nat | civ_try2F HR 51%nat | civ_try2F HR 52%nat | civ_try2F HR 53%nat | civ_try2F HR 54%nat | civ_try2F HR 0%nat | civ_try2F HR 1%nat | civ_try2F HR 2%nat | civ_try2F HR 3%nat | civ_try2F HR 4%nat | civ_try2F HR 5%nat | civ_try2F HR 6%nat | civ_try2F HR 7%nat | civ_try2F HR 8%nat | civ_try2F HR 9%nat | civ_try2F HR 10%nat | civ_try2F HR 11%nat | civ_try2F HR 12%nat | civ_try2F HR 13%nat | civ_try2F HR 14%nat | civ_try2F HR 15%nat | civ_try2F HR 16%nat | civ_try2F HR 17%nat | civ_try2F HR 18%nat | civ_try2F HR 19%nat | civ_try2F HR 20%nat | civ_try2F HR 21%nat | civ_try2F HR 22%nat | civ_try2F HR 23%nat | civ_try2F HR 24%nat | civ_try2F HR 25%nat | civ_try2F HR 26%nat | civ_try2F HR 27%nat | civ_try2F HR 28%nat | civ_try2F HR 29%nat | civ_try2F HR 30%nat | civ_try2F HR 31%nat | civ_try2F HR 32%nat | civ_try2F HR 33%nat | civ_try2F HR 34%nat | civ_try2F HR 35%nat | civ_try2F HR 36%nat | civ_try2F HR 37%nat | civ_try2F HR 38%nat | civ_try2F HR 39%nat | civ_try2F HR 40%nat | civ_try2F HR 41%nat | civ_try2F HR 42%nat ].

Local Ltac lia_only v := repeat match goal with H : context [v] |- _ => revert H end; clear - v; intros; lia.
Local Ltac wr_cell2F HR n off tacW :=
  eapply (cell_wok_rd2 _ _ _ _ _ (cells_ok_nth _ _ n _ HR eq_refl)); cbn [c_addr c_w Z.of_nat]; unfold fs_log_cell, fs_needs_gc_cell;
  [ lazymatch goal with |- ?x + _ <= ?x + _ < _ => idtac end; lia_only off | lia | tacW | lia ].
Local Ltac wr_any2F HR off tacW := first [ wr_cell2F HR 43%nat off tacW | wr_cell2F HR 44%nat off tacW | wr_cell2F HR 45%nat off tacW | wr_cell2F HR 46%nat off tacW | wr_cell2F HR 47%nat off tacW | wr_cell2F HR 48%nat off tacW | wr_cell2F HR 49%nat off tacW | wr_cell2F HR 50%nat off tacW | wr_cell2F HR 51%nat off tacW | wr_cell2F HR 52%nat off tacW | wr_cell2F HR 53%nat off tacW | wr_cell2F HR 54%nat off tacW ].

Lemma fn_instantiate : ltac2:(tb__ "0|4|
S6S37A1S4cS2dS17S6S4aQ40A1A1S77S27S4S4eR5A1S5A3S27S4S1bS6dR7A1A1S5A3S27SaS2S6S2S14S14A2M0A1M1S6S15A1M2A2M3A1S86S46S2fS2cR8S2bA3A1S6dR8A1A2ScG3S0G1G2S1G0S0S14S14S19P18A1S16S65A1A4S7G0A1A3S7S15A1A4A2A3S27S4S1bS70R9A1A1S5A3S27S4S87S15S22S7aA1S8S15S8S15S34RaS2bA2S36S35A1A3S7bA3A3S5A3S62Vsegs;VJ;RbS2bRaR9A4S2fS2cRbS2bA3R8R7R6A6S62Vsegs;VJ;RcS2bRbRaA4S7dRcS2bA2S6eRbR9A2R8R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FKc;FA;FW;").
Proof.
  intros W A Kc rho tp w Hii Wa Da Wb Fb H.
  set (rho1 := rho1_of A rho).
  pose proof H as [HsmA HJ]. destruct HJ as (HA & HU & HK & Htp & Htop).
  pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & _). unfold IMG_LO, IMG_HI in TI, CI.
  assert (E24 : rw rho1 24%positive = rw rho 24%positive) by reflexivity.
  assert (E10 : rw rho1 10%positive = rw rho 10%positive) by reflexivity.
  assert (Erm : rm rho1 = rm rho) by reflexivity.
  assert (E151 : rw rho1 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))) by reflexivity.
  assert (E152 : rw rho1 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))) by reflexivity.
  assert (E153 : rw rho1 153%positive = Z_to_bv 64 (ag_stack_top (aa_geom A))) by reflexivity.
  assert (E154 : rw rho1 154%positive = Z_to_bv 64 (ag_stack_bottom (aa_geom A))) by reflexivity.
  assert (TOPlo : topG (aa_geom A) <= fst (obj_range rho1 stack_win)) by (unfold stack_win; rewrite own_lo; exact Htop).

  assert (H1 : SPA segs (J W UStopLe A Kc) (Pre_free_nullI AE_A W UStopLe) rho1 tp w).
  { eapply SPA_agree; [| |exact H]; [eapply agree_below_le; [|apply rho1_agree]; cbv; discriminate | apply J_agree; apply rho1_agree]. }
  clear H HsmA.

  assert (H2 : SPA segs (J W UStopLe A Kc) (mkAX (sa_fn W) [] base_sv) rho1 tp w).
  { change (mkAX (sa_fn W) [] base_sv) with (ax_setS (Pre_free_nullI AE_A W UStopLe) (sa_fn W)).
    eapply SPA_restate; [exact Wa | exact Da | reflexivity | | constructor | exact H1].
    constructor; [|constructor]. cbn [fst snd eval]. rewrite E24. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    rewrite Htp, G4. reflexivity. }
  clear H1.

  destruct HRest as (Hsep & _ & _ & _ & _ & _ & HIA & HTH & HMI).
  unfold ia_inv in HIA. rewrite Hii in HIA. destruct HIA as (IA9 & IAa & IAb & IA8 & IAM).
  unfold thread_inv in HTH. destruct HTH as [HTH HTS].
  assert (MV : forall z, z < 0x646000 -> maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = view segs (rm rho) z).
  { intros z Hz. apply maskv_out. apply fs_footb_img; [exact HG0 | exact Hz]. }
  rewrite MV in IA9, IAa, IAb, IA8 by lia.
  assert (IAM' : forall z, IA_MAP1 <= z < IA_MAP1 + IA_MAP1_SZ -> view segs (rm rho) z = Some (Z_to_bv 8 0)).
  { intros z Hz. rewrite <- MV by (unfold IA_MAP1, IA_MAP1_SZ in Hz; lia). exact (IAM z Hz). }
  rewrite maskv_out in HTH by (apply fs_footb_thread; [exact HG0 | lia]).

  assert (H3 : SPA segs (J W UStopLe A Kc) (mkAX (sb_fn W) [] base_sv) rho1 tp w).
  { change (mkAX (sb_fn W) [] base_sv) with
      (ax_setS (mkAX (sa_fn W) [] base_sv) (let S := ax_S (mkAX (sa_fn W) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ map carve_obj N_fn) (ss_facts S) NW2 (ss_lenient S))).
    pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
    pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
    assert (Hhigh : holds rho1 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn [ss_facts sa_fn]; apply in_or_app; right; cbn; tauto).
    destruct (stack_win_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).

    assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rho1 (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                    (unwind_objs W)).
    { assert (HC : Forall (holds rho1) (chain_pre W)).
      { apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts sa_fn]. apply in_or_app. left. apply chain_pre_in. exact Hp. }
      unfold unwind_objs. destruct W as [|l W']; [constructor|].
      unfold chain_pre in HC. cbn [app] in HC.
      pose proof (Forall_inv HC) as C0. pose proof (Forall_inv (Forall_inv_tail HC)) as C1.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as C2. do 3 apply Forall_inv_tail in HC.
      cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
      pose proof (urange (rw rho1 10%positive)). rewrite Z.mod_small in C1 by lia.
      eapply Forall_impl; [|apply (chain_facts_bases rho1 (SVar 28) (l :: W') HC); cbn [eval]; lia].
      intros o (B & L & Hh). cbn [eval] in B. repeat split; try assumption; clear TI CI G15 G16 G17 G18 G19 G20 G21; lia. }
    eapply SPA_carve_list; [exact H2 | exact Wb | cbv; discriminate | | |].
    -
      clear G15 G16 G17 G18 G19 G20 G21 TI CI.
      unfold N_fn. unfold vT, vCTX, vTOP, vBOT.
      repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?u64_lit by lia.
      all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
      all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      all: split; [|split; [|apply xwords_clear_nil]].
      all: rewrite ?Erm.
      all: match goal with
           | |- cells_in_view _ _ 0 [(0x180e88, _, _); _] =>
               unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; intros j Hj; replace j with 0%nat by lia;
               cbn [Z.of_nat]; rewrite ?Z.add_0_r, ?Z.add_0_l; rewrite <- view_in by lia; [rewrite nth0_enc1_one; exact IA8 | rewrite nth0_enc1_zero; exact IA9]
           | |- cells_in_view _ _ 0 [(0xf2608, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil]; intros j Hj; rewrite nth_enc8_zero by exact Hj;
               rewrite <- view_in by lia; apply IAM'; unfold IA_MAP1, IA_MAP1_SZ; lia
           | |- cells_in_view _ _ (ag_thread _) [(3168, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil]; intros j Hj; replace j with 0%nat by lia;
               rewrite nth0_enc1_zero; cbn [Z.of_nat]; rewrite Z.add_0_r; rewrite <- view_in by lia; exact HTH
           | |- cells_in_view _ _ _ _ => unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; civ_any2F HR
           | _ => idtac end.
      all: try match goal with
           | |- forall off, 3168 <= off < 3169 -> _ =>
               intros off Hoff; replace off with 3168 by lia; eapply wok_rd_off_image2;
               [lia | pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & _); unfold IMG_LO, IMG_HI in *; lia |]; rewrite <- view_in by lia; exact HTH
           | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
           | |- forall off, _ -> wok_of _ _ _ = true /\ _ =>
               intros off Hoff;
               first [ wr_any2F HR off ltac:(pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & _); unfold IMG_LO, IMG_HI in *; lia)
                     | destruct (Z_lt_dec off 8); [|destruct (Z_lt_dec off 16)]; wr_any2F HR off ltac:(pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & _); unfold IMG_LO, IMG_HI in *; lia) ]
           end.
      all: fail "fn_instantiate: carve obligation left".
    -
      unfold N_fn. cbn [map carve_obj ss_objs ax_S sa_fn]. unfold carved, vT, vCTX, vTOP, vBOT.
      unfold A_globals. unfold O_got, O_rtc. unfold GOT_LO, GOT_HI, RTC_LO, RTC_HI.
      repeat (apply Forall_cons;
        [ apply Forall_cons;
          [ unfold ranges_disjoint; rewrite ?obj_range_mk by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); cbn [fst snd eval]; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]);
            destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in * ; (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ])
          | apply Forall_app; split;
            [ eapply Forall_impl; [|exact LNK]; intros [ob olo ohi ocs od] (B & L & Hh); cbn [ob_base ob_lo ob_hi] in B, L, Hh; subst olo ohi;
              unfold ranges_disjoint; rewrite !obj_range_mk by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); cbn [fst snd eval]; cbn [eval] in B; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]) ; (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ])
            | repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint;
              rewrite ?obj_range_mk by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); cbn [fst snd eval]; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]) ; (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]) ] ]
        | ]).
      apply Forall_nil.
    -
      unfold N_fn. cbn [map carve_obj pairwise_disjoint]. unfold carved, vT, vCTX, vTOP, vBOT.
      repeat split; repeat apply Forall_cons; try apply Forall_nil; try exact I; unfold ranges_disjoint;
        rewrite ?obj_range_mk by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); cbn [fst snd eval]; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]) ; (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]). }
  clear H2.

  change (P0_fn W UStopLe) with (ax_with_facts (mkAX (sb_fn W) [] base_sv) ((unwind_factsS W UStopLe ++ pre_facts free_depth) ++ F_geom_fn)).
  eapply SPA_refacts; [exact H3 | exact Fb |].
  intros Hold. apply Forall_app. split; [exact Hold|]. unfold F_geom_fn, vT, vCTX, vTOP, vBOT. clear TI CI G15 G16 G17 G18 G19 G20 G21.
  repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E151, ?E152, ?E153, ?E154; rewrite ?u64_lit by lia; try lia.
Qed.

Lemma N_fn_coverb : ltac2:(tb__ "0|0|
S27S4S87S73Sa7S6bA3S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N_fn_small : Forall spec_small N_fn.
Proof.
  unfold N_fn, spec_small.
  repeat apply Forall_cons; try apply Forall_nil; (split; [lia|]); (split; [lia|]); (split; [lia|]); unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
Qed.

Lemma fn_civ : ltac2:(tb__ "0|5|
S4cS17S6S4aQ40M0A1M1A1S91VAInv;R4R3R2R1A4S27S4S4eR5A1S5A3S27G1S1aR5P97A2S49G0S4fS4dR6A1A1A2A3S27G1S1aR6P98A2S49G0S50S4dR7A1A1A2A3S27G1S1aR7P99A2S49G0S53S4dR8A1A1A2A3S27G1S1aR8P9aA2S49G0S52S4dR9A1A1A2A3S89S73S73S2S2S2S14S11A2M2S11A2M3S6S2S2S11S3A2S14A2A1M4A2OLk;R1G3G4G3OLp;R2G2S11G2OLp0;R2S14S11Sa0R10Sa1Vsegs;S21R10A1A2S4bG0S1dR10R2A2A2R5A4Llo;Lbase;X2x1Lhi;Lp0;X2x1Lcs;Lp;X2x1Lk;S6bA3F_;F_;F_;F_;F_;F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md HA Hii E151 E152 E153 E154.
  pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & TG).
  destruct HRest as (Hsep & _ & _ & _ & _ & _ & HIA & HTH & HMI).
  unfold ia_inv in HIA. rewrite Hii in HIA. destruct HIA as (IA9 & IAa & IAb & IA8 & IAM). unfold thread_inv in HTH. destruct HTH as [HTH HTS].
  assert (MV : forall z, z < 0x646000 -> maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = view segs (rm rho) z).
  { intros z Hz. apply maskv_out. apply fs_footb_img; [exact HG | exact Hz]. }
  rewrite MV in IA9, IAa, IAb, IA8 by lia.
  assert (IAM' : forall z, IA_MAP1 <= z < IA_MAP1 + IA_MAP1_SZ -> view segs (rm rho) z = Some (Z_to_bv 8 0)).
  { intros z Hz. rewrite <- MV by (unfold IA_MAP1, IA_MAP1_SZ in Hz; lia). exact (IAM z Hz). }
  rewrite maskv_out in HTH by (apply fs_footb_thread; [exact HG | lia]).
  unfold N_fn. unfold vT, vCTX, vTOP, vBOT.
  repeat apply Forall_cons; try apply Forall_nil; lazy beta iota zeta; cbn [eval]; rewrite ?E151, ?E152, ?u64_lit by lia.
  all: unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?E153, ?E154.
  all: first [ intros j Hj; replace j with 0%nat by lia; cbn [Z.of_nat]; rewrite ?Z.add_0_r, ?Z.add_0_l; rewrite <- view_in by lia;
               first [ rewrite nth0_enc1_one'; exact IA8 | rewrite nth0_enc1_zero'; first [exact IA9 | exact HTH] ]
             | intros j Hj; rewrite nth_enc8_zero' by exact Hj; rewrite <- view_in by lia; apply IAM'; unfold IA_MAP1, IA_MAP1_SZ; lia
             | civ_any2F HR ].
Qed.

Definition rt_zone2 (G : ageom) (a : Z) : Prop := ltac2:(tb__ "0|0|
S2aSa6VG;Va;A2S2aS28S5bS81Va;A2S5cVa;S82A2A2S28S5bZ180e88Va;A2S5cVa;Z180e8cA2A2A2A2").

Definition img_zone2_okb (k : carve_spec) : bool := ltac2:(tb__ "0|7|
S2S2S2S14S11A2M0S11A2M1S6S2S2S11S3A2S14A2A1M2A2S4Lk;Vk;G1G2G1S4Lp;R2G0S11G0S4Lp0;R2S14S11S14S4Ls;R2S11S11S4Lz;R1Sa4S11SeSeS9aS9bS98S97A2R1A2SdS5dS81R1A2S5eR1S82A2A2A2SdS5dZ180e88R1A2S5eR1Z180e8cA2A2A2La;R2S61R4R2A2A3S12S5Lp1;M3G3X11x3Lz;S12S5Li;S9dS14S14S5Lb;La;M4Lop;M5G5S9eG4Lop;M6G6S4S13S14S5La;Lw;Lsgn;S12S14S11S5Lk0;Li;Ll0;X14x8Llo;Ls;X2x1Lhi;Lp0;X2x1Ll;Lp;X2x1").
Lemma N_fn_img_zone : ltac2:(tb__ "0|0|
S27S4S87S73S72S6bA3S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma N_fn_zone : ltac2:(tb__ "0|3|
S4cS17S73S11S7fS4dR4A1A1S27S4aQ40M0A1M1S1aR4P97A2S49G0S4fS4dR5A1A1A2A3S27G1S1aR5P98A2S49G0S50S4dR6A1A1A2A3S88S73R5S6bA3S28S5bSfS11S11Sa8R7R6A2M2A3R5A2S5cR5S10S11S11G2A3A2A2S6fS4dR9A1R6A2F_;F_;F_;F_;F_;Fa;Fk;Frho;FA;").
Proof.
  intros A rho k a HG E151 E152 Hk Ha.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (proj1 (forallb_forall _ _) N_fn_img_zone k Hk) as IZ.
  unfold N_fn in Hk. cbn [In] in Hk. unfold vT, vCTX, vTOP, vBOT in Hk. unfold rt_zone2, rt_zone.
  repeat (destruct Hk as [E|Hk];
    [subst k; cbn [spec_range fst snd eval] in Ha; rewrite ?E151, ?E152, ?u64_lit in Ha by lia;
     first [ unfold img_zone2_okb in IZ;
             pose proof (forall_rangeZ_ok _ _ _ a IZ ltac:(lia)) as B;
             apply orb_prop in B as [B|B]; [apply orb_prop in B as [B|B]; [left; left; split; [unfold IMG_HI; lia | exact B] | right; left]
                                          | right; right];
             try (apply andb_prop in B as [B1 B2]; apply Z.leb_le in B1; apply Z.ltb_lt in B2; lia)
           | left; right; lia ]
    |]).
  destruct Hk.
Qed.

Lemma client_not_rt2 : ltac2:(tb__ "0|0|
S4cS11S99S7fS4dR3A1A1S84R2R4A2S85R5A1S42VCST;R6R5A3S29S6fS4dR7A1R6A2A1F_;F_;F_;F_;Fm;Fa;FA;").
Proof.
  intros A a m HG HF Hsep Hcl [R|[R|R]].
  - exact (client_not_rt CST HCST A a m HG HF Hsep Hcl R).
  - destruct (client_addr_cases CST A a m HF Hcl) as [S|[L|[FR|[C|FL]]]]; unfold IA_BEG, IA_END in R; pose proof (topG_range (aa_geom A)) as TG.
    + lia.
    + destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in S2. lia.
    + destruct FR as (c & p & Hc & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in M. lia.
    + exact (proj1 (HCST2 _ C) R).
    + destruct FL as (c & p & Hc & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *. unfold IMG_HI in M. lia.
  - destruct (client_addr_cases CST A a m HF Hcl) as [S|[L|[FR|[C|FL]]]]; pose proof (topG_range (aa_geom A)) as TG.
    + lia.
    + destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in S2. lia.
    + destruct FR as (c & p & Hc & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in M. lia.
    + exact (proj2 (HCST2 _ C) R).
    + destruct FL as (c & p & Hc & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *. unfold IMG_HI in M. lia.
Qed.

Lemma shadow_not_rt2 : ltac2:(tb__ "0|0|
S4cS11S7fS4dR2A1A1S28S5bZ7fff8000R2A2S5cR2Z10007fff8000A2A2S29S6fS4dR4A1R3A2A1F_;F_;Fa;FA;").
Proof.
  intros A a HG Ha. pose proof (geom_bands _ HG) as (BF & BT & BC & BD & _).
  rewrite FS_total_val in BF. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BF, BT, BC, BD.
  unfold rt_zone2, rt_zone, IMG_HI, IA_BEG, IA_END.
  intros [[R|[R|[R|[R|R]]]]|[R|R]];
    [clear -Ha R; lia | clear -Ha R BT; lia | clear -Ha R BC; lia | clear -Ha R BD; lia | clear -Ha R BF; lia | clear -Ha R; lia | clear -Ha R; lia].
Qed.

Definition stK (W : list ulink) : sstate := ltac2:(tb__ "0|1|
S1eS3eS2cA1S58S59S76A1S1S2S3S14A2M0S0S3S14U4S16S65A1A4S7G0A1A3A2S57S1cSbS14A1S1S18S3aS8S18S3bVW;A1S38A3A3S8S15S8S15S34VW;S2bA2S36S35A1A3S7bA3S7aS9A9").
Definition stR (W : list ulink) : sstate := ltac2:(tb__ "0|0|
S1eS3eS2cA1S59S76A1S57S1cSbS14A1S1S18S3aS8S18S3bVW;A1S38A3A3S8S15S8S15S34VW;S2bA2S36S35A1A3S7bA3S7aS9A9").
Definition s_fn (W : list ulink) : wsub := ltac2:(tb__ "0|0|
S9fS56S6aVW;A1S46S2eS2cVW;S2bA3A1A3").

Lemma fn_reabstract : ltac2:(tb__ "0|6|
S6S37A1S4cS2dS17S6S4aQ40A1A1S77S17S27S4S4eR6A1S5A3S27S4S1bS6aR8A1A1S5A3S27SaS2S6S2S14S14A2M0A1M1S6S15A1M2A2M3A1S86S71R9A1S6aR9A1A2ScG3S0G1G2S1G0S0S14S14S16S65A1S19P18A1A4S7G0A1M4A3S7S15A1A4A2A3S27S4S47S48S6aRaA1G4S3fA3S2eS2cRaS2bA3S6cRaA1A3S5A3S27S4S93S6cRbA1S56A2S5A3S62Vsegs;S90S17S1fS76S6eRcRaA2R1A3Lr;VJ;RcS2bRbRaA4A2S7cRcS2bA2R6R8R7A6S55Vsegs;S56RaR9S1S2S45S54A2M5S0S45S54S2eS2cRdS2bA3S30VAInv;VCST;VXGL;RcRbA5A4S7G5A1A3R8A6F_;F_;F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;FW;").
Proof.
  intros W A Kc rho tp w rhoE Hii WR DKR Hent Hid H.
  destruct w as [tr [ms md]]. destruct H as [HsmA [Hag HJ]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct HJ as (HA & HU & HK & Htp & Htop).
  destruct Hag as (Hagw & Hagl & Hagm).
  assert (Erm : rm rhoE = rm rho).
  { apply functional_extensionality. intros a. rewrite <- Hagm. reflexivity. }
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (E153 : rw rhoE 153%positive = Z_to_bv 64 (ag_stack_top (aa_geom A))). { rewrite <- (Hagw 153%positive) by (unfold GW; lia). reflexivity. }
  assert (E154 : rw rhoE 154%positive = Z_to_bv 64 (ag_stack_bottom (aa_geom A))). { rewrite <- (Hagw 154%positive) by (unfold GW; lia). reflexivity. }
  pose proof HA as (HG & HR & HF & HRest & HM). pose proof (proj1 HRest) as Hsep.

  assert (Ha : SPA segs (fun _ _ t m => Kc t m) (E_fn W UStopLe) rhoE tp (tr, mkCfg ms md)) by (split; [exact HsmA | exact HK]).
  pose proof (SPA_unobj segs (fun _ _ t m => Kc t m) rhoE (E_fn W UStopLe) (stack_win :: unwind_objs W ++ A_globals) RT_fn tp tr ms md eq_refl Ha (fun k => k)) as Hb.
  cbn zeta in Hb. set (rho3 := rho_absorb rhoE RT_fn (vms md tp ms)) in *.
  change (ax_setS (E_fn W UStopLe) (set_objs (ax_S (E_fn W UStopLe)) (stack_win :: unwind_objs W ++ A_globals))) with (mkAX (stK W) [] base_sv) in Hb.
  pose proof (proj1 (proj1 Ha)) as Hsm2. unfold virt in Hsm2. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm2.

  pose proof (fn_civ A rhoE tp md HA Hii E151 E152 E153 E154) as CIV.
  assert (VEQ : forall z, view segs (rm rho3) z = view segs (rm rhoE) z).
  { intros z. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
    2,3: rewrite !view_out by lia; reflexivity.
    rewrite !view_in by lia. destruct (in_ranges_dec rhoE RT_fn (Z_to_bv 64 z)) as [Hri|Hrn].
    - destruct Hri as (o & Hin & Hr). rewrite <- N_fn_ok in Hin. apply in_map_iff in Hin as (k & <- & Hk).
      unfold rho3. eapply (absorb_specs_view rhoE (ax_S (E_fn W UStopLe)) tr (vms md tp ms) (vmd md) (stack_win :: unwind_objs W ++ A_globals) RT_fn N_fn (rd_of segs (rm rhoE)) Hsm2 eq_refl); [| exact Hk |].
      + intros k' Hk'. split; [rewrite <- N_fn_ok; apply in_map; exact Hk'|]. split; [exact (proj1 (Forall_forall _ _) N_fn_small k' Hk')|].
        split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_fn_coverb k' Hk')|].
        pose proof (proj1 (Forall_forall _ _) CIV k' Hk') as C'. destruct k' as [[[base lo] hi] cs]. cbn [spec_range fst snd].
        cbn zeta in C'. replace (bv_unsigned (eval rhoE base) + lo - lo) with (bv_unsigned (eval rhoE base)) by lia. exact C'.
      + pose proof (proj1 (Forall_forall _ _) N_fn_small k Hk) as Sk. destruct k as [[[base lo] hi] cs]. cbn [carve_obj] in Hr.
        destruct Sk as (S1 & S2 & S3 & _). unfold carved in Hr. rewrite obj_range_mk in Hr by lia. cbn [fst snd ob_base spec_range] in Hr |- *.
        rewrite u64_lit in Hr by lia. exact Hr.
    - unfold rho3, rd_of. rewrite rm_absorb_out by exact Hrn. reflexivity. }

  assert (Hc : SPA segs (fun _ _ t m => Kc t m) (mkAX (stR W) [] base_sv) rho3 tp (tr, mkCfg ms md)).
  { change (mkAX (stR W) [] base_sv) with (ax_setS (mkAX (stK W) [] base_sv) (stR W)).
    eapply SPA_restate; [exact WR | exact DKR | reflexivity | | constructor | exact Hb].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    unfold rho3. cbn [rho_absorb rw]. rewrite Htp. destruct (geom_old _ HG) as (_ & _ & _ & G4 & _). rewrite G4. reflexivity. }

  remember (s_fn W) as s eqn:Hs. clear Hs.
  pose proof (smatchA_entails segs _ _ _ rho3 tp _ Hent (proj1 Hc)) as Hsm4.
  set (rho4 := rho_sub rho3 s) in Hsm4.
  assert (Hlow : forall k, (k < NF)%positive -> rw rho4 k = rw rhoE k).
  { intros k Hk. unfold rho4. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ Hid Hk). reflexivity. }
  assert (Erm4 : rm rho4 = rm rho3) by exact (rm_rho_sub' rho3 s).

  exists (L_free_null AE_A W UStopLe), (JL_free_null AInv CST XGL A Kc), rho4, tp.
  split; [left; reflexivity|]. split; [|split; [exact Hsm4|]].
  { split; [intros k Hk; rewrite Hlow by exact Hk; rewrite (proj1 (rho1_agree A rho) k Hk); apply Hagw; unfold GW, NF in *; lia|].
    intros l. unfold rho4, rho3. cbn [rl rho_sub rho_absorb]. rewrite <- Hagl. reflexivity. }
  cbn [w_tr w_cfg cfg_model fst snd]. unfold JL_free_null. exists A.
  assert (HA' : AInv A rho4 tp md).
  { apply (AInvA_view A rhoE rho4 tp md HA). intros a. rewrite Erm4.
    pose proof (VEQ (bv_unsigned a)) as V. rewrite !view_in in V by apply urange. rewrite Z_to_bv_bv_unsigned in V. exact V. }
  split; [exact HA'|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [|exact HK].

  rewrite Erm4, <- Erm.
  assert (RMO : forall a, 0 <= a < 2 ^ 64 -> ~ rt_zone2 (aa_geom A) a -> rm rho3 (Z_to_bv 64 a) = rm rhoE (Z_to_bv 64 a)).
  { intros a Ba Hz. unfold rho3. apply rm_absorb_out. intros (o & Hin & Hr). apply Hz.
    rewrite <- N_fn_ok in Hin. apply in_map_iff in Hin as (k & <- & Hk).
    pose proof (proj1 (Forall_forall _ _) N_fn_small k Hk) as Sk.
    apply (N_fn_zone A rhoE k a HG E151 E152 Hk).
    destruct k as [[[base lo] hi] cs]. destruct Sk as (S1 & S2 & S3 & _). cbn [carve_obj] in Hr. unfold carved in Hr.
    rewrite obj_range_mk in Hr by lia. cbn [fst snd ob_base spec_range] in Hr |- *. rewrite u64_lit in Hr by lia. exact Hr. }
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). pose proof (topG_range (aa_geom A)) as TG.
  split.
  - intros a Ba Hcl. apply RMO; [exact Ba|].
    destruct Hcl as [[C1 _]|[C1 _]]; [exact (client_not_rt2 A a _ HG HF Hsep C1)|].
    pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
    exact (shadow_not_rt2 A a HG B).
  - intros x j Hx Hj Hdef.
    assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
    { destruct Hx as [[C1 C2]|GX].
      - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. lia.
      - destruct (HXGL x GX). unfold IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. lia. }
    unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
    destruct (word_byte_range (Sh x) j ltac:(lia) Hj) as (W1 & W2 & W3).
    unfold word_byte. rewrite RMO; [exact Hdef | lia |].
    apply (shadow_not_rt2 A _ HG). lia.
Qed.

Section PerN.
Variable n : nat.
Let W : list ulink := Wcan n.
Hypothesis Wa : ltac2:(tb__ "0|0|
S27S4S1bS6dVW;A1A1S5A3").
Hypothesis Da : ltac2:(tb__ "0|4|
S27SaS2S6S2S14S14A2M0A1M1S6S15A1M2A2M3A1S86S46S2fS2cVW;S2bA3A1S6dVW;A1A2ScG3S0G1G2S1G0S0S14S14S19P18A1S16S65A1A4S7G0A1A3S7S15A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S27S4S1bS70VW;A1A1S5A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S27S4S87S15S22S7aA1S8S15S8S15S34VW;S2bA2S36S35A1A3S7bA3A3S5A3").
Hypothesis WR : ltac2:(tb__ "0|0|
S27S4S1bS6aVW;A1A1S5A3").
Hypothesis DKR : ltac2:(tb__ "0|4|
S27SaS2S6S2S14S14A2M0A1M1S6S15A1M2A2M3A1S86S71VW;A1S6aVW;A1A2ScG3S0G1G2S1G0S0S14S14S16S65A1S19P18A1A4S7G0A1A3S7S15A1A4A2A3").
Hypothesis Ent : ltac2:(tb__ "0|0|
S27S4S47S48S6aVW;A1S7S2S14S14A2A1S3fA3S2eS2cVW;S2bA3S6cVW;A1A3S5A3").
Hypothesis Id : ltac2:(tb__ "0|0|
S27S4S93S6cVW;A1S56A2S5A3").
Hypothesis Cert : ltac2:(tb__ "0|1|
S27S4S8eS44Ubb8S7S11A1S76S1S45S7dVW;S2bA2S7S45A1M0A3S1S45S7cVW;S2bA2G0A3A6S5A3").
Hypothesis ECert : ltac2:(tb__ "0|3|
S27S4S8fS44Ubb8S7S11A1S76S1S8cS8dS7dVW;S2bA2Z1S16Z0M0A1M1A3S7S8cA1M2A3S1S8cS8dS7cVW;S2bA2G0G1A3G2A3A6S5A3").

Theorem free_null_inited : ltac2:(tb__ "0|1|
S77OF_;S4cS2dS17S6S4aQ40A1A1S27S4S4eR4A1S5A3S32R4A1S63Vsegs;R7VJ;VW;S2bR6R5A4A3S79Vsegs;R8S62Vsegs;VJ;VW;S2bR7R6A4S2fS2cVW;S2bA3R5R4A5S55Vsegs;S56R5R4S1S2S45S54A2M0S0S45S54S2eS2cVW;S2bA3S30VAInv;VCST;VXGL;R7R6A5A4S7G0A1A3A5A4F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Hii HKc Hokf.
  eapply triple_conseq; [intros w Hw; exact (fn_instantiate W A Kc rho tp w Hii Wa Da Wb Fb Hw) | intros w Hw; exact Hw |].
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs _ GW (P0_fn W UStopLe) (rho1_of A rho) tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 3000%nat [] GW [P0_fn W UStopLe] [E_fn W UStopLe] (withGA (fun r => agree_below GW (rho1_of A rho) r) (J W UStopLe A Kc)) ok
           (LQPA segs NF rho tp [(L_free_null AE_A W UStopLe, JL_free_null AInv CST XGL A Kc)]) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hokf; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply J_stableA; exact HKc].
  - exact Cert.
  - intros E rhoE [<-|[]].
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. right. exact (fn_reabstract W A Kc rho tp w rhoE Hii WR DKR Ent Id Hw).
  - left. reflexivity.
Qed.

Theorem free_null_inited_ex : ltac2:(tb__ "0|1|
S4cS2dS17S6S4aQ40A1A1S27S4S4eR4A1S5A3S32R4A1S78Vsegs;S62Vsegs;VJ;VW;S2bR6R5A4S2fS2cVW;S2bA3R4R3A5S55Vsegs;S56R4R3S1S2S45S54A2M0S0S45S54S2eS2cVW;S2bA3S30VAInv;VCST;VXGL;R6R5A5A4S7G0A1A3A5A3F_;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Hii HKc.
  eapply etriple_conseq; [intros w Hw; exact (fn_instantiate W A Kc rho tp w Hii Wa Da Wb Fb Hw) | intros w Hw; exact Hw |].
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs _ GW (P0_fn W UStopLe) (rho1_of A rho) tp w Hw) | intros w Hw; exact Hw |].
  change (P0_fn W UStopLe) with (vna_state (mkVNA (P0_fn W UStopLe) 1 (SLit 0))).
  apply (cfg_complete_autoA segs 3000%nat [] GW [mkVNA (P0_fn W UStopLe) 1 (SLit 0)] [mkVNA (E_fn W UStopLe) 0 (SLit 0)]
           (withGA (fun r => agree_below GW (rho1_of A rho) r) (J W UStopLe A Kc))
           (LQPA segs NF rho tp [(L_free_null AE_A W UStopLe, JL_free_null AInv CST XGL A Kc)]) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply J_stableA; exact HKc].
  - intros m [<-|[]]. cbv; congruence.
  - exact ECert.
  - intros E rhoE [<-|[]]. cbn [vna_state].
    eapply etriple_conseq; [| intros w Hw; exact Hw | apply etriple_refl].
    intros w Hw. right. exact (fn_reabstract W A Kc rho tp w rhoE Hii WR DKR Ent Id Hw).
  - left. reflexivity.
Qed.
End PerN.
End FN.

Section Inst.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCST2 : ltac2:(tb__ "0|0|
S11S96VCST;R1A2S28S29S28S5bS81R2A2S5cR2S82A2A2A1S29S28S5bZ180e88R2A2S5cR2Z180e8cA2A2A1A2F_;Fa;").
Ltac fn_close :=
  match goal with
  | |- forall r, _ -> Forall _ (unwind_objs _) => intros r Hr; cbn; constructor
  | |- _ = true => vm_compute; reflexivity
  | |- state_diff _ _ = _ => vm_compute; reflexivity
  | _ => assumption
  end.

Theorem free_null_contract_0_inited : ltac2:(tb__ "0|3|
S77OF_;S4cS2dS17S6S4aQ40A1A1S27S4S4eR4A1S5A3S32R4A1S63S44R7S31S80S44A1M0S39U0A1M1S2bR6R5A5A3S79S44R8S62S44S31G0G1S2bR7R6A5S2fS2cG1S2bA3R5R4A5S55S44S56R5R4S1S2S45S54A2M2S0S45S54S2eS2cG1S2bA3S30G0VCST;VXGL;R7R6A5A4S7G2A1A3A5A4F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Hii HKc Hokf.
  Time (apply (free_null_inited CST XGL HCST HXGL HCST2 0%nat); fn_close).
Qed.

Theorem free_null_contract_0_inited_ex : ltac2:(tb__ "0|3|
S4cS2dS17S6S4aQ40A1A1S27S4S4eR4A1S5A3S32R4A1S78S44S62S44S31S80S44A1M0S39U0A1M1S2bR6R5A5S2fS2cG1S2bA3R4R3A5S55S44S56R4R3S1S2S45S54A2M2S0S45S54S2eS2cG1S2bA3S30G0VCST;VXGL;R6R5A5A4S7G2A1A3A5A3F_;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp Hii HKc.
  Time (apply (free_null_inited_ex CST XGL HCST HXGL HCST2 0%nat); fn_close).
Qed.

Theorem free_null_contract_0_inited_orpc : ltac2:(tb__ "0|3|
S77OF_;S4cS2dS17S6S4aQ40A1A1S27S4S4eR4A1S5A3S32R4A1S63S44R7S31S80S44A1M0S39U0A1M1S33R6R5A5A3S79S44R8S62S44S31G0G1S33R7R6A5S2fS2cG1S33A3R5R4A5S55S44S56R5R4S1S2S45S54A2M2S0S45S54S2eS2cG1S33A3S30G0VCST;VXGL;R7R6A5A4S7G2A1A3A5A4F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof. exact free_null_contract_0_inited. Qed.
Theorem free_null_contract_0_inited_orpc_ex : ltac2:(tb__ "0|3|
S4cS2dS17S6S4aQ40A1A1S27S4S4eR4A1S5A3S32R4A1S78S44S62S44S31S80S44A1M0S39U0A1M1S33R6R5A5S2fS2cG1S33A3R4R3A5S55S44S56R4R3S1S2S45S54A2M2S0S45S54S2eS2cG1S33A3S30G0VCST;VXGL;R6R5A5A4S7G2A1A3A5A3F_;F_;Ftp;Frho;FKc;FA;").
Proof. exact free_null_contract_0_inited_ex. Qed.
End Inst.
