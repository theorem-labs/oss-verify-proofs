(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av b3.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be SpineMallocS9.

(* [comment removed for export] *)
Module SpineCallocR2.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "mul"; "div"; "of_nat"; "@Corelib.Init.Datatypes"; "list"; "cons"; "pair"; "bool"; "true"; "prod"; "nil"; "app"; "Some"; "option"; "false"; "andb"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "rw"; "sobj"; "sprop"; "ss_next"; "obj_range"; "ss_lenient"; "holds"; "ss_facts"; "ss_objs"; "sstate"; "swf"; "agree_below"; "eval"; "ranges_disjoint"; "rm"; "smatch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "axst"; "ax_setS"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ag_thread"; "ag_spacebeg"; "ageom"; "aa_cache_inited"; "ag_ctx"; "class_state"; "cs_allocated_user"; "cs_cache"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "JR"; "entryR"; "PCE"; "phase"; "frozen"; "ghosts"; "ph_fill"; "gh_new"; "gh_nf"; "ph0"; "ph_cnt"; "ph_pop"; "zoneR"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "ustop"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "cR0"; "k_e"; "GR"; "fa_e"; "ri_e"; "vFA"; "vK"; "vRI"; "O_pcm"; "O_ri"; "cR1"; "factsR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "cfacts"; "rigids"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "needed8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "max_count"; "kSpaceSize"; "region_info"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "bview"; "present"; "view"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "F_gen"; "O_pcc0"; "O_st"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "FACAP"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1"; "armint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5";
"tab1_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "@Stdlib.Lists.List"; "In"; "incl"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition rigids (A : AA) (rb r : valuation) : Prop := ltac2:(tb__ "0|5|
S34Q40M0S1cVrb;PcM1A2M2A2S4S6dR1A1S4S37VA;A1S3aS0S1S32G0A1M3S1cVr;G1A2G2A3S0S1G3S1cVr;P94A2S33G0S71R2A1A2A3S0S1G3S1cVr;P97A2S33G0S38R1A1A2A3S0S1G3S1cVr;P98A2S33G0S3cR1A1A2A3S0S1G3S1cVr;P9bA2S33G0S39R1A1M4A2A3S0S1G3S1cVr;P9cA2S33G0S6G4S73A2A2A3S0S1G3S1cVr;P9dA2S33G0S6fR3A1A2A3S1G3S1cVr;P9eA2S33G0R2A2A3A2A2A2A2A2A2A2TG;Tc;Tnv;").
Lemma entry_rigids : ltac2:(tb__ "0|0|
S36S1aScS32Q40A1A1S51ScS53A1S54S1aS1aS45R8R7R6R5R4R3R2A7S48R8R2A2S69RaR9R3A3F_;F_;Fr;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho r (Hag & _) [Fw _]. destruct Hag as (Hagw & _ & _).
  assert (E12 : rw rb 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  unfold rigids. cbn zeta. rewrite E12.
  repeat split; rewrite <- (Fw _) by lia; try reflexivity; rewrite <- (Hagw _) by (unfold GW; lia); reflexivity.
Qed.

Definition cfacts (A : AA) (rb : valuation) : Prop := ltac2:(tb__ "0|d|
S34Q40S1cVrb;PcA2A2S4S6dR1A1S4S6eVA;R2A2S3dS37VA;A1S3aS39R1A1S4S38R2A1S4S0S0S0S5Z1M0R6A2S5R6Zfc00A2A2S0S0S5G0R5A2S5R5Z1eA2A2S0S0S5Z20S71R5A1M1A2S5G1Z10000M2A2A2S1S4S8G1Z10A2Z0M3A3A2A2A2S0S0S0S5G0S8aR5A1M4A2S5G4Z8A2A2S0S1S4S9Z2G4A2S72R5A1A3S5S9G4G1A2G2A2A2A2S0S0S1S4S8S42R4A1M5Z40000M6A2G3A3S0S0S5G3S3eR4A1M7A2S5G7G5A2A2S0S5G5Ze0000000A2S0S1S4S8G7G1A2G3A3S7G5S6G7G1A2A2A2A2A2A2S0S0S1S4S8S41R4A1M8G6A2G3A3S0S5S9Z4SbS18S4S40R4A1A2A1A2G8A2S5G8Z20000000A2A2A2S0S0S5G5S89R5A1A2S0S5G8S88R5A1A2S1ScS4A1S3fR4A1S12S4A1A3A2A2S0S0S1S4S8R2G2A2G3A3S0S5Z100080000000R2A2S0S5S6S6R2Z2000000000A2Z1000M9A2MaS43R3A1MbA2S5GbZ7fffff800000A2A2A2A2S0S0S5G9R1A2S0S5S6R1G9A2McGbA2S0S2S5GcG2A2S5Z646000R1A2A2S2S5GcR2A2S5GaR1A2A2A2A2A2S2S5GcZ7fff7000A2S5Z10007fff8000R1A2A2A2A2A2A2A2A2A2TT;TSB;TG;Tcs;Tc;Tnv;").
Lemma entry_cfacts : ltac2:(tb__ "0|0|
S36S1aScS32Q40A1A1S51ScS53A1S54S1aS45R7R6R5R4R3R2R1A7S68R8R7A2F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho (_ & HA & _ & _ & _ & Hnv & _ & Hcnt & _). unfold cfacts. cbn zeta.
  set (nv := bv_unsigned (rw rb 12%positive)) in *.
  pose proof (cls_facts nv Hnv) as (C1 & C2 & C3 & C4). destruct (kchunks_facts _ C1) as (K1 & K2 & K3).
  destruct (cap_facts _ C1) as (S1 & _).
  pose proof HA as (HG & _ & _ & HRest & _ & HI3 & _).
  destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 (cls_of nv) C1).
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TI10 & _ & MC10 & FC10).
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize, kFreeArrayMapSize in N1, N2, N3, N5, N6.
  pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (_ & _ & _ & _ & G5 & G6 & _ & _ & _ & _ & _ & G12 & G13 & G14 & _).
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & _ & _). unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in TI, TB.
  pose proof (topG_range (aa_geom A)) as TG. destruct (proj1 HI3) as (PS1 & _). rewrite kSpaceSize_val in PS1.
  assert (Hc0 : cs_cache (cst_of A nv) = []).
  { unfold cnt_of in Hcnt. destruct (cs_cache (cst_of A nv)); [reflexivity | cbn [length] in Hcnt; lia]. }
  unfold cst_of. fold (cst_of A nv).
  split; [repeat split; first [exact C3 | lia]|]. split; [repeat split; lia|].
  split; [unfold cst_of; repeat split; first [exact N1 | exact N4 | lia]|].
  split; [unfold cst_of; repeat split; first [exact N5 | lia]|].
  split; [split; [exact MC10 | split; [exact FC10 | exact Hc0]]|].
  split; [repeat split; first [exact G12 | lia]|]. split; [repeat split; lia | lia].
Qed.

Definition tabK_okb : bool := ltac2:(tb__ "0|2|
S17S8cPdcM0S5dS4SaR1Z2M1A2Lz;G1UfA5S8dG0S5dA2A2").
Lemma tabK_ok : tabK_okb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma r1_diffs : ltac2:(tb__ "0|1|
S36S1aS1aS68R3R2A2S69R4R3R2A3S49R5R4R3A3S77R4SdS11S1bS1bA2M0SeS1bS1bS60S63A4SdG0SeS1bS1bS5dS62A4SdG0SeS1bS1bS5fS61A4S12G0A1A3A3A3A2F_;F_;F_;Fr;Frb;FA;").
Proof.
  intros A rb r CF RG GH. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & (K1 & K2 & _) & _ & _ & _ & (G12 & G13 & G14 & TG) & _ & _).
  destruct RG as (_ & _ & _ & _ & E155 & E156 & _ & E158). destruct GH as (Q220 & _ & _ & _ & _ & Q225 & Q226 & Q227 & _).
  unfold region_info, kRegionInfoStride in Q225. rewrite kSpaceSize_val in Q225, E156.
  unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Q226.
  unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - unfold ri_e, vRI, vRIS, V_CLS. cbn [eval]. rewrite E156, E158, Q225. apply bv_eq.
    rewrite add_val, sll_val, !u64_lit by lia. change (7 mod 64) with 7. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (_ * 2 ^ 7)) by lia. rewrite Z.mod_small by lia. lia.
  - unfold vK. cbn [eval]. rewrite Q227. pose proof tabK_ok as TK. unfold tabK_okb in TK. apply andb_prop in TK as [TK OV].
    rewrite (tab1_ok_sound 220 k_e (fun z => z / 2) 2 15 r (max_count (cls_of (bv_unsigned (rw rb 12%positive)))) TK OV Q220) by lia.
    unfold kchunks. reflexivity.
  - unfold fa_e, vFA, vSB, V_CLS. cbn [eval]. rewrite E155, E158, Q226. apply bv_eq.
    rewrite add_val, add_val, sll_val, !u64_lit by lia. change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + 3758096384)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition BASEO (W : list ulink) : list sobj := ltac2:(tb__ "0|0|
S13S1dSdS1dS80S13S1dS59VW;A1S55A3A3S85A3").
Definition BASEF (W : list ulink) (st : ustop) : list sprop := ltac2:(tb__ "0|0|
S13S1eS13S1eS58VW;Vst;A2S57S56A1A3S81A3").
Lemma arm_base_disj : ltac2:(tb__ "0|3|
S36S1aScS32Q40A1A1S51ScS53A1S54S1aS25ScS1dA1M0S1aS11ScS52A1S7eA2S7fR7R6A2S45RcRbRaR9R8R7R6A7S48RcR4A2S2bS87R5R7R4A4S1ScS11S11S1bS1bA2S1bA2M1A1M2S5aS1dG1S6cS24R8A1A4S5aS1dG1S6cS13S1dS6bRbA1R7A3A4A3S8fS1eS6aRcRbA2S23R9A1A3S3G0G0S3G0G0S0S1G0S24RcA1S13S1dR2R1A3A3S0S1G2S5aS1dG1S6cR1A4S5aS1dG1S6cRbA4A3S4S4S8bS37R15A1R2R1A3S5bS1dS1dS29S20ReR1A2SeS4S4R4R3A4A2Lo';R5A3F_;Fhi;Flo;A2A2Lox;A2Lob;A2F_;F_;F_;F_;F_;F_;Fw;Fr;Fextra;FS;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho S extra r w HW HE HFz Hsm HSK HXF.
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as (_ & _ & R151 & R152 & _).
  destruct HE as (_ & HA & _ & _ & _ & _ & Htop & _).
  pose proof HA as (HG & _ & _ & _ & _ & HI3 & _). pose proof (proj1 HI3) as HS3.
  destruct HFz as [Fw _].
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p (BASEF W st) -> holds r p) by (intros p Hp; exact (proj1 (Forall_forall _ _) HFa p (HXF p Hp))).
  destruct (map_eq_app _ _ _ _ ltac:(rewrite <- map_app; exact HSK)) as (ob & ox & EO & SKb & SKx).
  exists ob, ox. split; [exact EO|]. split; [exact SKx|].
  intros lo hi HI.
  apply (base_zone W (aa_geom A) r S w ob lo hi HG HS3 Hsm); [intros o Ho; rewrite EO; apply in_or_app; left; exact Ho | exact SKb | | | | exact R151 | exact R152 | exact HI].
  - apply HFX. unfold BASEF. apply in_or_app; left. apply in_or_app; right. cbn; tauto.
  - apply Forall_forall. intros p Hp. apply HFX. unfold BASEF. apply in_or_app; left. apply in_or_app; left.
    destruct st; [apply chain_pre_in; exact Hp|]. exact (chain_pre_factsS' _ _ _ Hp).
  - unfold top_high in Htop. rewrite <- (Fw 10%positive) by lia. rewrite <- (Fw V_DEPTH) by (unfold V_DEPTH; lia). exact Htop.
Qed.

Lemma arm_extra_ranges : ltac2:(tb__ "0|4|
S36S1aS1aS68R3R2A2S69R4R3R2A3S49R5R4R3A3S38S37R6A1A1S4S74S39S37R7A1A1S6dS34Q40M0S1cR6PcA2A2A1A2S4S0S1S4S34G0S28R6S84A2A2S46R8R7A2M1A3S0S1S11S4S4A2M2S20R6S82A2SeS4S4G1S6G1Z4A2M3A4A3S0S1G2S20R6S83A2SeS4S4S6R2Zad0A2S6R2Zc60A2A4A3S0S1G2S20R6S64A2SeS4S4G3S6G1Z8A2A4A3S1G2S20R6S65A2SeS4S4R1S6R1Z80A2A4A3A2A2A2A2Tri;TT;F_;F_;F_;Fr;Frb;FA;").
Proof.
  intros A rb r CF RG GH T ri. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & _ & _) & _). fold T in T1, T2.
  destruct RG as (_ & _ & E151 & _ & _ & _ & _ & E158). fold T in E151. destruct GH as (_ & _ & _ & _ & _ & Q225 & _). fold ri in Q225.
  assert (EB : bv_unsigned (eval r pc_base) = PCE A rb).
  { unfold pc_base, vT, V_CLS, PCE. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
    rewrite (Z.mod_small (_ * 80)) by lia. rewrite (Z.mod_small (T + 208)) by lia. rewrite Z.mod_small by lia. fold T. lia. }
  split; [exact EB|].
  split; [unfold O_pcc0; rewrite obj_range_mk by lia; rewrite EB; f_equal; lia|].
  split; [unfold O_st, vT; rewrite obj_range_mk by lia; cbn [eval]; rewrite E151, u64_lit by lia; reflexivity|].
  split; [unfold O_pcm; rewrite obj_range_mk by lia; rewrite EB; reflexivity|].
  unfold O_ri, vRI. rewrite obj_range_mk by lia. cbn [eval]. rewrite Q225, u64_lit by (unfold ri, region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia). f_equal; lia.
Qed.

Lemma entry_pc_cells : ltac2:(tb__ "0|2|
S36S1aScS32Q40M0A1A1S51ScS53A1S54S1aS45R7R6R5R4R3R2R1A7S1SfS3bR8A1S10A3S7dS86S2aR8A1A2S7bS6dS34G0S1cR9PcA2A2A1S4S0S79R2S7aS6S46RbRaA2M1Z4A2U4S72R1A1A3A2S0S79R2S7aS6G1Z8A2U8S71R1A1A3A2S7cR2G1S6G1Z50A2A3A2A2Tc;Tm0;F_;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho HE Hini m0 c.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold c in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & _ & (T1 & T2 & _) & _).
  destruct HE as (_ & HA & _ & _ & _ & Hnv & _ & Hcnt & _).
  pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  assert (MT : forall z, ag_thread (aa_geom A) <= z < ag_thread (aa_geom A) + 0x1000 -> maskv (fs_footb (aa_geom A)) m0 z = m0 z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  unfold class_repr in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PE & _ & _ & CI & _).
  destruct (CI Hini) as (_ & D2 & D3 & _).
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold c; lia).
  split; [|split].
  - intros j Hj. specialize (D2 j Hj). cbn [c_addr c_w RtCells.c_val] in D2, Hj |- *. rewrite MT in D2 by lia. rewrite PCr. exact D2.
  - intros j Hj. specialize (D3 j Hj). cbn [c_addr c_w RtCells.c_val] in D3, Hj |- *. rewrite MT in D3 by lia. rewrite PCr. exact D3.
  - intros z Hz. rewrite PCr in Hz. destruct (PE z ltac:(lia)) as [b Hb]. exists b. rewrite <- MT by lia. exact Hb.
Qed.

Lemma zone_thread_gen : ltac2:(tb__ "0|7|
S36S1aS47S4S68R4R3A2S7Z0M0S4aR3A1A2S0S5G0S4cR6R5A2M1A2S0S5S9Z4M2S6G1S4bR6R5A2M3A2A2Z20000000A2S5S4aR4A1G3A2A2A2F_;S0S5S6S38S37R6A1A1M4Z120A2R3A2S7R3S6G4Zc60A2A2A2S50R7R6R5R4A4S2S0S5S6S46R8R7A2M5Z10A2M6R5A2S7R5S6G6S9G2S4fR6A1A2A2A2A2S0S1SfS4eR6A1S10A3S0S5G5R5A2S7R5S6G5G2A2A2A2A2A2F_;F_;F_;F_;Fz;Fph;Frb;FA;").
Proof.
  intros A rb ph z CF HFL Hz HZ. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & _ & (_ & MU0 & MU1 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof (Zle_0_nat (length (cs_free_array (cst_of A (bv_unsigned (rw rb 12%positive)))))) as NF0.
  unfold zoneR in HZ.
  unfold U0, F0, FAb, free_array, region_beg, region_info, kRegionInfoStride, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize, Sh, SHADOW_OFF in HZ.
  rewrite kSpaceSize_val in HZ.
  destruct HZ as [[_ X]|[[_ X]|[[_ X]|[[_ X]|[[X X2]|[X|[X|[_ X]]]]]]]]; [exfalso | exfalso | exfalso | exfalso | exfalso | left; exact X | right; exact X | exfalso].
  - clear -X Hz MU0 MU1 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MU0 MU1 C1 G13 G14 TG PS1 T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG PS1 T1 T2. lia.
  - destruct (HFL X2) as (F1 & F2 & F3). clear -X Hz F1 F2 F3 C1 G13 G14 TG PS1 T1 T2. lia.
  - clear -X Hz C1 G13 G14 TG PS1 T1 T2. lia.
Qed.

Section STEPS.
Let segs : list Segment := segsA.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Notation JRp := (JR A Kc rb tp0 md0).

Lemma jr_run : ltac2:(tb__ "0|1|
S19ScS4A1S30ScS2dA1M0S47S1aScS32Q40A1A1S70S1S15G0A1S2fVsegs;R8R7R6S10A5S14G0R5A2A3S1SfS21S2cR7A1A1S16A3S1SfS75S5eS1fS2cR8A1A1A2S10A3S2dS1aS8eS2dR2RaA3S27S1fS2cRcA1A1R9R2A3VTR;S35Vsegs;S44VA;VKc;Vrb;Vtp0;Vmd0;RbA6S2eR4A1R3R9A5R8A2F_;F_;Frho';FL;VTR;S35Vsegs;S44VA;VKc;Vrb;Vtp0;Vmd0;R8A6RaR7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;Fph;Fleaves;FE;Fcuts;Ffuel;").
Proof.
  intros fuel cuts E leaves ph rho tp Q Hrun Hl Hn HL.
  apply (tr_run Kc TR KIT fuel cuts E leaves (JRp ph) rho tp Q (JR_K A Kc rb tp0 md0 ph)); [|exact Hrun | exact Hl | exact HL].
  apply JR_stable; [exact HKc | apply Pos.leb_le; exact Hn].
Qed.

Lemma jr_restate : ltac2:(tb__ "0|3|
S30S25ScS11S1bS1bA2A1M0ScS1eA1M1S47S1aScS32Q40A1A1S70S1SfS26R7A1S10A3S1S15S11G0G1A2M2A1S78S2cR9A1R8A2S14G2SeG0G1R7R6A4A2A3S1SfS76S1fR9A1S1fS2cRaA1A1A2S10A3ScS52A1S51S44VA;VKc;Vrb;Vtp0;Vmd0;R9R8R7R2R1AaS5bS1eS22R9A1S23S2cReA1A1A3S0S77RaRdA2S5bS1eS22RaA1RcA3A2F_;F_;Fmd;Ftr;VTR;S35Vsegs;S44VA;VKc;Vrb;Vtp0;Vmd0;R8A6S31RcRbA2R7R6A5R5A2VTR;S35Vsegs;S44VA;VKc;Vrb;Vtp0;Vmd0;R9A6RdR8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fph;Fnf;Fd;FS';FE;").
Proof.
  intros E S' d nf ph rho tp Q Hwf Hsd Hnx Hsem HT.
  apply (tr_pre Kc TR KIT _ _ Q) with (2 := HT). intros w Hw.
  pose proof (SPA_facts_hold segs _ rho E tp w Hw) as HF.
  destruct (Hsem _ _ (proj2 Hw) HF) as [Hd Hn].
  apply (SPA_restate segs _ rho E S' tp w d nf Hwf Hsd); [apply Pos.eqb_eq; exact Hnx | exact Hd | exact Hn | exact Hw].
Qed.

Section PREFIX.
Variable F : nat.
Variables (E3 : axst) (L1 LP LJ : leafA).
Let CR1 : axst := ltac2:(tb__ "0|0|
S66S67VE3;A1S2eVL1;A1A2").
Hypothesis R_1 : ltac2:(tb__ "0|1|
S1S15ScS2dA1M0A1S2fVsegs;VF;SdS4Z412e8S12S4A1A3S5cVE3;A1S10A5S14G0SdS2dVL1;S12S2dA1A3A2A3").
Hypothesis LN_0 : ltac2:(tb__ "0|0|
S1SfS21S2cS5cVE3;A1A1A1S16A3").
Hypothesis NX_0 : ltac2:(tb__ "0|0|
S1SfS75S5eS1fS2cS5cVE3;A1A1A1A2S10A3").
Hypothesis W_r1 : ltac2:(tb__ "0|0|
S1SfS26S2cVCR1;A1A1S10A3").
Hypothesis D_r1 : ltac2:(tb__ "0|4|
S1S15S11ScS11S1bS1bA2M0A1M1ScS1eA1M2A2M3A1S78S2cS2eVL1;A1A1S2cVCR1;A1A2S14G3SeG1G2SdG0SeS1bS1bS60S63A4SdG0SeS1bS1bS5dS62A4SdG0SeS1bS1bS5fS61A4S12G0A1A3A3A3S12S1eA1A4A2A3").
Hypothesis NX_r1 : ltac2:(tb__ "0|0|
S1SfS76S1fS2cVCR1;A1A1S1fS2cS2eVL1;A1A1A1A2S10A3").
Hypothesis R_2 : ltac2:(tb__ "0|1|
S1S15ScS2dA1M0A1S2fVsegs;VF;SdS4Z41570SdS4Z413ccS12S4A1A3A3VCR1;S10A5S14G0SdS2dVLP;SdS2dVLJ;S12S2dA1A3A3A2A3").
Hypothesis LN_1 : ltac2:(tb__ "0|0|
S1SfS21S2cVCR1;A1A1S16A3").
Hypothesis NX_1 : ltac2:(tb__ "0|0|
S1SfS75S5eS1fS2cVCR1;A1A1A2S10A3").

Lemma refill_prefix : ltac2:(tb__ "0|1|
ScS53A1S54S1aS1aScS32Q40A1A1S70S45VA;Vrb;Vtp0;Vmd0;R6R5R4A7S1aVTR;S35Vsegs;S44VA;VKc;Vrb;Vtp0;Vmd0;S4dA6M0S2eVLP;A1R1R4A5R3A2Fr';S1aVTR;S35Vsegs;G0S2eVLJ;A1R1R5A5R4A2Fr';VTR;S35Vsegs;G0S5cVE3;A1R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Frho;Fst;FW;").
Proof.
  intros W st rho r tp Q HE HP HJ.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_run F [0x412e8] (cR0 E3) [L1] ph0 r tp Q R_1 LN_0 NX_0).
  intros L r1 [<-|[]] _.
  apply (jr_restate (la_state L1) (ax_S CR1) _ _ ph0 r1 tp Q W_r1 D_r1 NX_r1).
  { intros tr md (HFz & HGh & _) _. split; [|constructor].
    exact (r1_diffs A rb r1 CF (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh). }
  change (ax_setS (la_state L1) (ax_S CR1)) with CR1.
  apply (jr_run F [0x41570; 0x413cc] CR1 [LP; LJ] ph0 r1 tp Q R_2 LN_1 NX_1).
  intros L r2 [<-|[<-|[]]] _; [apply HP | apply HJ].
Qed.
End PREFIX.
End STEPS.
End SpineCallocR2.

(* [comment removed for export] *)
Module SegQ3D_qc_arith.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "rw"; "SLit"; "valuation"; "SPUlt"; "SVar"; "eval"; "holds"; "SPBranch"; "SPNot"; "SPUle"; "@Corelib.Numbers.BinNums"; "Z"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_signed"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "cons"; "app"; "list"; "nil"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "mul"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "clsB"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith"; "FC_it"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith"; "FQ_stk"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "max_count"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_DEPTH"; "pre_facts"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs"; "factsC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "DEPTH_R"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma signed_add15 : ltac2:(tb__ "0|5|
S5SdS0SdS10Q40M0S3R2S22A2A2R1A3S1S16S1bS18Z2M1Z28A2A1R2A2S16R2N600A2A2S1S0SdS11G0S8R4S26S7PfA1S4Zc0M2A1A2A2M3A2S17S17R3G2A2M4S18G1Z40A2A2A3S0SdS10G0G3A2G4A3A2F_;F_;FD;Frho;").
Proof.
  intros rho D HD HR. pose proof (signed_neg_unsigned (rw rho V_DEPTH) D HD ltac:(lia)) as EU.
  assert (E1 : bv_unsigned (eval rho (add (SVar 15) (SLit 192))) = D + 192 + 2 ^ 64).
  { unfold add. cbn [eval]. rewrite add_val. change (rw rho 15%positive) with (rw rho V_DEPTH). rewrite EU, u64_lit by lia. rewrite Z.mod_small by lia. lia. }
  split; [exact E1|]. rewrite signed_of_unsigned, E1. unfold snorm. cbv zeta. rewrite (Z.mod_small (D + 192 + 2 ^ 64)) by lia.
  replace (D + 192 + 2 ^ 64 <? 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; lia). lia.
Qed.

Lemma stk_facts_hold : ltac2:(tb__ "0|0|
S25S5S24R2R1A2S1dS2S9R2A1S23S28A1A3S1dS2S9R3A1S1fA3F_;F_;Frho;FA;").
Proof.
  intros A rho HT HF. destruct (stk_facts A rho HT HF) as (HD & HTOP & Hsp). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (F_sp_holds A rho HT HF) as HSP. unfold F_sp in HSP. cbn [holds eval] in HSP. rewrite u64_lit in HSP by lia.
  pose proof (Forall_inv (Forall_inv_tail HF)) as Hf. unfold holds, F_sp_high in Hf. cbn [eval] in Hf. rewrite add_val in Hf. rewrite u64_lit in Hf by lia.
  pose proof (signed_neg_unsigned (rw rho V_DEPTH) _ eq_refl ltac:(lia)) as EU. rewrite EU in Hf.
  replace (bv_unsigned (rw rho 10%positive) + (bv_signed (rw rho V_DEPTH) + 2 ^ 64)) with (bv_unsigned (rw rho 10%positive) + bv_signed (rw rho V_DEPTH) + 1 * 2 ^ 64) in Hf by lia.
  rewrite Z.mod_add in Hf by lia. rewrite Z.mod_small in Hf by lia.
  destruct (signed_add15 rho _ eq_refl HD) as [EA ES].
  assert (ESP : bv_unsigned (eval rho spD) = bv_unsigned (rw rho 10%positive) - 192).
  { unfold spD. rewrite (eval_add_lit A rho (SVar 10) (bv_unsigned (rw rho 10%positive)) (-192)); [apply u64_lit; lia | cbn [eval]; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | lia]. }
  unfold FQ_stk. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. change (eval rho (SLit 140735332483072)) with (Z_to_bv 64 140735332483072). rewrite u64_lit by lia.
    unfold add at 1. cbn [eval]. rewrite add_val. fold (add (SVar 15) (SLit 192)). rewrite ESP, EA.
    replace (bv_unsigned (rw rho 10%positive) - 192 + (bv_signed (rw rho V_DEPTH) + 192 + 2 ^ 64)) with (bv_unsigned (rw rho 10%positive) + bv_signed (rw rho V_DEPTH) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. exact Hf.
  - cbn [holds branch_taken]. apply negb_true_iff. unfold bv_lts. apply Z.ltb_ge. rewrite ES. change (eval rho (SLit (-1024))) with (Z_to_bv 64 (-1024)). rewrite signed_lit.
    change (snorm (-1024)) with (-1024). lia.
  - cbn [holds branch_taken]. apply negb_true_iff. unfold bv_lts. apply Z.ltb_ge. rewrite ES. change (eval rho (SLit (-1099511627776))) with (Z_to_bv 64 (-1099511627776)). rewrite signed_lit.
    change (snorm (-1099511627776)) with (-1099511627776). lia.
Qed.

Lemma clsB_val : ltac2:(tb__ "0|7|
S5SdSdSdS0SfQ40M0A1M1S3R4Pa6A2SeG0R2A2A3S0G1S3R5P9bA2SeG0R4A2A3S0SdR4S17S17R5S1aZ18M2S18Z2M3Z20A2M4A2A2S1aZ10M5R3A2A2A3S16Z0M6R4A2S19S1aG5R5A2G4A2S16G6R8A2S19R8S18G3Z40A2A2S0G1S8RbS1cA2SeG0G2A2A3F_;F_;F_;F_;F_;F_;F_;Fy;Fa;FSB;Frho;").
Proof.
  intros rho SB a y E166 E155 Ea Hy Hy2 HSB Ha. apply bv_eq. rewrite (u64_lit 24) by lia.
  unfold clsB, vB, vSB. rewrite U_srl_lit, U_sll_lit, U_sub. cbn [eval]. rewrite E166, E155, !u64_lit by lia. change (27 mod 64) with 27. change (59 mod 64) with 59. unfold M64v.
  replace (a - SB) with (24 * 2 ^ 32 + 16 * y) by lia. rewrite (Z.mod_small (24 * 2 ^ 32 + 16 * y)) by lia.
  replace ((24 * 2 ^ 32 + 16 * y) * 2 ^ 27) with (16 * y * 2 ^ 27 + 24 * 2 ^ 59) by lia.
  rewrite Z.mod_small by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Definition FC_it : list sprop := ltac2:(tb__ "0|2|
S12S2S6S4Z0A1M0S1cA2S12S2S6S1cS4Z20A1A2S12S2SbSaS20S7PcfA1M1G0A3A1S12S2S6S7PceA1G1A2S12S2ScG1S4Z100A1A2S15S2A1A3A3A3A3A3").
Lemma factsC_eq : ltac2:(tb__ "0|0|
S0S14S2A1S27S13S2S1fS1eA3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma qc_it_facts : ltac2:(tb__ "0|4|
S5SdS0SfQ40M0A1M1S8R2S1cA2SeG0Z18M2A2A3S0G1S3R3PceA2SeG0R2A2A3S0G1S3R4PcfA2SeG0S21G2A1M3A2A3S1S16Z0R4A2S19R4G3A2A2S1dS2S9R6A1S1eA3F_;F_;F_;F_;Fk;Frho;").
Proof.
  intros rho k EC E206 E207 Hk. change (max_count 24) with 2 in *. unfold FC_it. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. rewrite EC. change (eval rho (SLit 0)) with (Z_to_bv 64 0). rewrite !u64_lit by lia. lia.
  - cbn [holds]. rewrite EC. change (eval rho (SLit 32)) with (Z_to_bv 64 32). rewrite !u64_lit by lia. lia.
  - cbn [holds branch_taken eval]. rewrite E207. intros HB. unfold bv_eqb in HB. apply Z.eqb_eq in HB. rewrite !u64_lit in HB by lia. lia.
  - cbn [holds eval]. rewrite E206, E207, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E207, !u64_lit by lia. lia.
Qed.
End SegQ3D_qc_arith.

(* [comment removed for export] *)
Module SpineMallocS8.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "la_state"; "leafA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "cons"; "list"; "prod"; "pair"; "Some"; "option"; "nat"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "ss_facts"; "SVar"; "ss_next"; "valuation"; "SLit"; "SPBranch"; "sobj"; "sstate"; "swf"; "SPNot"; "rw"; "sprop_below"; "SAlu"; "eval"; "SPUle"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "V_CLS"; "E7c1"; "E7c2"; "F_gen"; "C7p"; "E7q1"; "E7q2"; "E7p"; "V_ND"; "n8e"; "upd"; "C8"; "C8p"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "BP"; "C7"; "LPe"; "ube"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "JGb"; "@Stdlib.Lists.List"; "In"; "incl"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@Stdlib.ZArith.BinInt.Z"; "modulo"; "add"; "mul"; "le"; "lt"; "of_nat"; "sub"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "BC_EQ"; "ALU_ADD"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "memset_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "tab_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8.S8.B11S"; "E7c1'"; "E7c2'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8.S8.B12S"; "E7q1'"; "E7q2'"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "needed8"; "cnt_of"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "merge_objs_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocS8"; "a0e7"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4"; "pvals_ok"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition a0e7 : sv := ltac2:(tb__ "0|0|
S22S5bS22S5cS22S5bS40S35A3S1aZ3A1A3S28A3").

Section PSVals7.
Variable rho : valuation.
Variables SB c x rzv sz n : Z.
Hypothesis PV : ltac2:(tb__ "0|0|
S7eVrho;VSB;Vc;Vx;Vrzv;Vsz;Vn;A7").
Let ab : Z := ltac2:(tb__ "0|0|
S4cS4cVSB;S4dVc;S52Z2Z20A2A2A2S4dZ10Vx;A2A2").
Ltac pv := pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).

Lemma pv_a0e7 : ltac2:(tb__ "0|0|
S0S53Q40A1S23Vrho;S7cA2S23Vrho;S3dA2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_ub rho _ _ _ _ _ _ PV) as EUB. cbn zeta in EUB. fold ab in EUB.
  pose proof (pv_bp rho _ _ _ _ _ _ PV) as EBP. cbn zeta in EBP. fold ab in EBP.
  apply bv_eq. rewrite EBP. unfold a0e7, shb. cbn [eval]. fold ube. fold n8e.
  assert (EN8 : bv_unsigned (eval rho n8e) = n - n mod 8).
  { unfold n8e. cbn [eval]. rewrite and_val, E12, !u64_lit by (unfold M48; lia). apply land_M48. lia. }
  rewrite add_val, srl_val, add_val, EUB, EN8, !u64_lit by (unfold SHADOW_OFF; lia). change (3 mod 64) with 3.
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)).
  assert (B1 : 17594333495296 <= ab + rzv /\ ab + rzv + n <= 140737479966720) by (unfold ab; lia).
  rewrite (Z.mod_small (ab + rzv + _)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (Sh_small rho _ _ _ _ _ _ PV (ab + rzv + (n - n mod 8)) ltac:(lia)) as (_ & E & _). rewrite E.
  unfold Sh. pose proof (Z.div_mod rzv 16 ltac:(lia)). pose proof (Z.div_mod SB (2 ^ 16) ltac:(lia)).
  replace (ab + rzv + (n - n mod 8)) with (ab + rzv + (n / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

Lemma pv_lp1 : ltac2:(tb__ "0|0|
S2S0S25S4bVn;Z8A2Z0A3A1S0S25S54Q40S23Vrho;S3fA2A2Z1A3F_;").
Proof. intros Hn. rewrite (pv_lp rho _ _ _ _ _ _ PV). destruct (Z.eq_dec (n mod 8) 0); [contradiction | reflexivity]. Qed.
End PSVals7.

Section S8.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S62VAInv;VW;Vst;VA;VKc;S17PcA1A6").

Lemma class_restate_gen : ltac2:(tb__ "0|7|
S4S1dS15S25S12S63S60S19SdS53Q40M0A1A1S47S19S0S9S65P9dM1R9A2SaA3S0S9S66G1RaS64R9R8A5SaA3S0S9S1eRcA1SaA3S0S11SeSdSeS15S15A2M2A1M3SdS14A1M4A2M5A1S49S3ReA1RdA2S10G5SfG3G4ScG2SfS15S15RcS17S2cA1A4SbG2A1A3SbS14A1A4A2A3S0S26S18ReA1S18S3RfA1A1A3S71S54G0S20R9PcA2A2A1S25S1S1S4eReR1A2S4fR1S4cReS4dZ8M6S50RdA1A2A2A2A2S0S25S4bS51R1ReA2G6A2Z0A3A2Tnd;S29Vsegs;S42VW;Vst;RcRbRaA5R11R7R9R8A6S29Vsegs;S42VW;Vst;RdRcRbA5S6R12R11A2R8RaR9A6F_;F_;F_;F_;F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;Fcnt;Flo;Fcreg;FES;FE;").
Proof.
  intros E ES creg lo cnt A Kc rho tp w rhoE OV TAB WS DS NX [Hr Hm] Hw.
  destruct w as [tr [ms md]]. pose proof (proj2 Hw) as [Hag HJ]. destruct Hag as (Hagw & _ & _).
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 (bv_unsigned (rw rho 12%positive)))). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of (bv_unsigned (rw rho 12%positive)))). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  eapply SPA_restate; [exact WS | exact DS | exact NX | | constructor | exact Hw].
  unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold V_CLS. cbn [eval]. rewrite E158.
  exact (tab_ok_sound 157 _ ClassID lo cnt rhoE _ TAB OV E157 Hr Hm).
Qed.

Lemma needed_range : ltac2:(tb__ "0|6|
S63S60S19S19SdS53Q40M0A1A1S47S4S9S29Vsegs;S42VW;Vst;R8R7R6A5R2R5R4R3A6S44S14S2fS16S3R3A1A1A3S43S14S9S14Lb;R3S1bS59S1aZ200A1S17S34A1A3M1S1fG1A1X9x2S16S3R4A1A1A3S71S54G0S20R9PcA2A2A1S25S9OLb;R5S1S1S4eZ208M2R1A2S4fR1S4cG2S4dZ8M3S50S6bS6cS55S56S57S55S58A1A1A1A1A1A1A1A2A2A2A2S0S25S4bS51R1G2A2G3A2Z0M4A3A2S1S1S4eZ18M5R1A2S4fR1S4cG5S4dG3S50U3eA1A2A2A2A2S0S25S4bS51R1G5A2G3A2G4A3A2X9x2Tnd;F_;F_;F_;Fb;FE;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w E b Hw HG HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as [Hag HJ]. destruct Hag as (Hagw & _ & _). destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive) by (rewrite <- (Hagw 12%positive) by (unfold GW; lia); reflexivity).
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in *. cbn zeta.
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (NB0 : 0 <= needed8 nv < 2 ^ 62).
  { unfold needed8, round_up. pose proof (rz_bound nv). pose proof (Z.mul_div_le (Z.max nv 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.div_pos (Z.max nv 8 + 8 - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (G1 : holds rhoE (SPUle (SLit 24) (SVar V_ND))) by (apply (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw); apply HG; unfold F_gen; cbn; tauto).
  assert (G2 : holds rhoE (SPUle (SVar V_ND) (SLit 65536))) by (apply (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw); apply HG; unfold F_gen; cbn; tauto).
  assert (G3 : holds rhoE (SPAlign V_ND 3)) by (apply (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw); apply HG; unfold F_gen; cbn; tauto).
  cbn [holds eval] in G1, G2, G3. unfold V_ND in G1, G2, G3. rewrite E157 in G1, G2, G3. rewrite !u64_lit in G1, G2 by lia.
  destruct G3 as [_ G3]. rewrite u64_lit in G3 by lia. change (2 ^ 3) with 8 in G3.
  pose proof (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw HF) as F1.
  destruct b; cbn [holds eval] in F1; unfold V_ND in F1; rewrite E157 in F1; rewrite bt_ltu_lit in F1 by lia.
  - apply Z.ltb_lt in F1. split; [cbn; lia|]. replace (needed8 nv - 520) with (needed8 nv + (- 65) * 8) by lia. rewrite Z.mod_add by lia. exact G3.
  - assert (needed8 nv <= 512) by (destruct (Z.ltb_spec 512 (needed8 nv)); [exfalso; apply F1; reflexivity | lia]).
    split; [cbn; lia|]. replace (needed8 nv - 24) with (needed8 nv + (- 3) * 8) by lia. rewrite Z.mod_add by lia. exact G3.
Qed.

Section B11S.
Hypothesis Cert7 : ltac2:(tb__ "0|1|
S0S9S6dS6fUfa0ScS25Z3c728ScS25Z3c870SbS25A1A3A3S27ScS4S3eVW;Vst;Vtmax;A3SbS4A1M0A3ScS4S2dVW;Vst;Vtmax;A3ScS4S2eVW;Vst;Vtmax;A3ScS4S33VW;Vst;Vtmax;A3G0A3A3A3A6SaA3").
Definition E7c1' : axst := ltac2:(tb__ "0|1|
S36VW;Vst;Vtmax;S2dVW;Vst;Vtmax;A3Z3c870ScSeS12S15A2M0SfS12S15UbS17S2cA1A4SbG0A1A3SbS1cA1S13SbS14A1A9").
Definition E7c2' : axst := ltac2:(tb__ "0|1|
S36VW;Vst;Vtmax;S2eVW;Vst;Vtmax;A3Z3c870ScSeS12S15A2M0SfS12S15UbS17S2cA1A4SbG0A1A3SbS1cA1S13SbS14A1A9").
Hypothesis OV7a : ltac2:(tb__ "0|0|
S0S9S65P9dS39VW;Vst;Vtmax;A3A2SaA3").
Hypothesis OV7b : ltac2:(tb__ "0|0|
S0S9S65P9dS3aVW;Vst;Vtmax;A3A2SaA3").
Hypothesis TAB7a : ltac2:(tb__ "0|0|
S0S9S66P9dS39VW;Vst;Vtmax;A3S64Z208S6bS6cS55S56S57S55S58A1A1A1A1A1A1A5SaA3").
Hypothesis TAB7b : ltac2:(tb__ "0|0|
S0S9S66P9dS3aVW;Vst;Vtmax;A3S64Z18U3eA5SaA3").
Hypothesis W7a : ltac2:(tb__ "0|0|
S0S9S1eS3S67A1A1SaA3").
Hypothesis W7b : ltac2:(tb__ "0|0|
S0S9S1eS3S68A1A1SaA3").
Hypothesis D7a : ltac2:(tb__ "0|4|
S0S11SeSdSeS15S15A2M0A1M1SdS14A1M2A2M3A1S49S3S2dVW;Vst;Vtmax;A3A1S3S67A1A2S10G3SfG1G2ScG0SfS15S15S39VW;Vst;Vtmax;A3S17S2cA1A4SbG0A1A3SbS14A1A4A2A3").
Hypothesis D7b : ltac2:(tb__ "0|4|
S0S11SeSdSeS15S15A2M0A1M1SdS14A1M2A2M3A1S49S3S2eVW;Vst;Vtmax;A3A1S3S68A1A2S10G3SfG1G2ScG0SfS15S15S3aVW;Vst;Vtmax;A3S17S2cA1A4SbG0A1A3SbS14A1A4A2A3").
Hypothesis NX7a : ltac2:(tb__ "0|0|
S0S26S18S3S67A1A1S18S3S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis NX7b : ltac2:(tb__ "0|0|
S0S26S18S3S68A1A1S18S3S2eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7a : ltac2:(tb__ "0|0|
S44S14S2fS16S3S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7b : ltac2:(tb__ "0|0|
S44S14S2fS16S3S2eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7a : ltac2:(tb__ "0|0|
S43S14S1bS59S1aZ200A1S17S34A1A3S16S3S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7b : ltac2:(tb__ "0|0|
S43S14S1fS1bS59S1aZ200A1S17S34A1A3A1S16S3S2eVW;Vst;Vtmax;A3A1A1A3").
Variables s8a s8b : wsub.
Hypothesis ENT8a : ltac2:(tb__ "0|0|
S0S9S5S67S37VW;Vst;Vtmax;A3Vs8a;A3SaA3").
Hypothesis ENT8b : ltac2:(tb__ "0|0|
S0S9S5S68S37VW;Vst;Vtmax;A3Vs8b;A3SaA3").
Hypothesis SID8a : ltac2:(tb__ "0|0|
S0S9S4aVs8a;S27A2SaA3").
Hypothesis SID8b : ltac2:(tb__ "0|0|
S0S9S4aVs8b;S27A2SaA3").

Hypothesis G7p : ltac2:(tb__ "0|0|
S44S14S2fS16S3S33VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7p : ltac2:(tb__ "0|0|
S43S14S1fS1bS5aS17PcA1S35A3A1S16S3S33VW;Vst;Vtmax;A3A1A1A3").
Hypothesis W7p : ltac2:(tb__ "0|0|
S0S9S1eS3S30VW;Vst;Vtmax;A3A1A1SaA3").
Hypothesis D7p : ltac2:(tb__ "0|4|
S0S11SeSdSeS15S15A2M0A1M1SdS14A1M2A2M3A1S49S3S33VW;Vst;Vtmax;A3A1S3S30VW;Vst;Vtmax;A3A1A2S10G3SfG1G2ScG0SfS15S15S7cS3dA4SbG0A1A3ScS14S24S1aZ1A1S3fA2SbS14A1A3A4A2A3").
Hypothesis NX7p : ltac2:(tb__ "0|0|
S0S26S18S3S30VW;Vst;Vtmax;A3A1A1S18S3S33VW;Vst;Vtmax;A3A1A1A3").

Hypothesis F7an : ltac2:(tb__ "0|0|
S43S14S1bS5aS17PcA1S35A3S16S3S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7bn : ltac2:(tb__ "0|0|
S43S14S1bS5aS17PcA1S35A3S16S3S2eVW;Vst;Vtmax;A3A1A1A3").

Lemma nmod8_of_fact : ltac2:(tb__ "0|4|
S63S60S19S19SdS53Q40M0A1A1S47S4S9S29Vsegs;S42VW;Vst;R8R7R6A5R2R5R4R3A6S44S14S2fS16S3R3A1A1A3S43S14S9S14Lb;R3S1bS5aS17PcM1A1S35A3M2S1fG2A1X9x2S16S3R4A1A1A3S9OLb;R4S0S25S4bS54G0S20R9G1A2A2Z8A2Z0A3M3S2G3A1X9x2F_;F_;F_;Fb;FE;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w E b Hw HG HF. destruct w as [tr [ms md]].
  pose proof (JGb_rigid nW st A Kc rho rhoE tp tr md (proj2 Hw)) as (E12 & _).
  destruct (JGb_model nW st A Kc rho rhoE tp tr md (proj2 Hw)) as [_ HN]. cbn zeta in HN.
  pose proof (fact_of_stateB nW st A Kc rho rhoE tp _ E _ Hw HF) as F.
  assert (EV : bv_unsigned (eval rhoE n8e) = bv_unsigned (rw rho 12%positive) - bv_unsigned (rw rho 12%positive) mod 8).
  { unfold n8e. cbn [eval]. rewrite and_val, E12, u64_lit by (unfold M48; lia). apply land_M48. pose proof (urange (rw rho 12%positive)). lia. }
  destruct b; cbn [holds eval] in F; fold n8e in F; cbn [branch_taken] in F; unfold bv_eqb in F; rewrite E12, EV in F.
  - apply Z.eqb_eq in F. lia.
  - intros E0. apply F. apply Z.eqb_eq. lia.
Qed.

Theorem spine_s7 : ltac2:(tb__ "0|5|
S47OF_;S63S60S19SdS53Q40M0A1A1S48S70VW;Vst;A2S61R5A1S2bVsegs;R8S2aR6A1A3S4eZ1S72R8S54G0S20R6PcM1A2A2A2A2S0S25S4bS54G0S20R7G1A2A2Z8M2A2Z0M3A3S19S46Vsegs;RcS29Vsegs;S42VW;Vst;RbRaR9A5S37VW;Vst;Vtmax;A3R1R8A5R7A4FrhoX;F_;S2S0S25S4bS54G0S20R8G1A2A2G2A2G3A3A1S19S46Vsegs;RdS29Vsegs;S42VW;Vst;RcRbRaA5M4S30VW;Vst;Vtmax;A3R1R9A5R8A4FrhoX;F_;S19S46Vsegs;RdS29Vsegs;G4S3eVW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf Hcnt HC8 HC7p rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c728; 0x3c870] GW [C7 W st tmax] [E7c1 W st tmax; E7c2 W st tmax; E7p W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert7.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[<-|[]]]].
    + apply (triple_pre_pure segs ok _ _ (bv_unsigned (rw rho 12%positive) mod 8 = 0)); [intros w Hw; exact (nmod8_of_fact A Kc rho rhoX tp w _ true Hw G7a F7an)|]. intros Hm0.
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 Hm0 (rho_sub rhoX s8a))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7c1' (C8 W st tmax) s8a rhoX tp w ENT8a SID8a); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7c1', upd. lazy zeta.
      apply (class_restate_gen (E7c1 W st tmax) _ (creg7a W st tmax) 520 8128%nat A Kc rho tp w rhoX OV7a TAB7a W7a D7a NX7a); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ true Hw G7a F7a).
    + apply (triple_pre_pure segs ok _ _ (bv_unsigned (rw rho 12%positive) mod 8 = 0)); [intros w Hw; exact (nmod8_of_fact A Kc rho rhoX tp w _ true Hw G7b F7bn)|]. intros Hm0.
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 Hm0 (rho_sub rhoX s8b))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7c2' (C8 W st tmax) s8b rhoX tp w ENT8b SID8b); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7c2', upd. lazy zeta.
      apply (class_restate_gen (E7c2 W st tmax) _ (creg7b W st tmax) 24 62%nat A Kc rho tp w rhoX OV7b TAB7b W7b D7b NX7b); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ false Hw G7b F7b).
    + apply (triple_pre_pure segs ok _ _ (bv_unsigned (rw rho 12%positive) mod 8 <> 0)); [intros w Hw; exact (nmod8_of_fact A Kc rho rhoX tp w _ false Hw G7p F7p)|]. intros Hm8.
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC7p Hm8 rhoX)].
      pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G7p Hcnt) as PV. cbn zeta in PV.
      destruct w as [tr [ms md]].
      unfold C7p, upd. lazy zeta. eapply SPA_restate; [exact W7p | exact D7p | exact NX7p | | | exact Hw].
      * unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_a0e7 rhoX _ _ _ _ _ _ PV).
      * apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. fold LPe. rewrite (pv_lp1 rhoX _ _ _ _ _ _ PV Hm8). rewrite u64_lit by lia. lia.
  - left. reflexivity.
Qed.
End B11S.

Section B12S.
Hypothesis Cert7p : ltac2:(tb__ "0|1|
S0S9S6dS6fUfa0ScS25Z3c870SbS25A1A3S27ScS4S30VW;Vst;Vtmax;A3SbS4A1M0A3ScS4S31VW;Vst;Vtmax;A3ScS4S32VW;Vst;Vtmax;A3G0A3A3A6SaA3").
Definition E7q1' : axst := ltac2:(tb__ "0|1|
S36VW;Vst;Vtmax;S31VW;Vst;Vtmax;A3Z3c870ScSeS12S15A2M0SfS12S15UbS17S2cA1A4SbG0A1A3SbS1cA1S13SbS14A1A9").
Definition E7q2' : axst := ltac2:(tb__ "0|1|
S36VW;Vst;Vtmax;S32VW;Vst;Vtmax;A3Z3c870ScSeS12S15A2M0SfS12S15UbS17S2cA1A4SbG0A1A3SbS1cA1S13SbS14A1A9").
Hypothesis OV7c : ltac2:(tb__ "0|0|
S0S9S65P9dS3bVW;Vst;Vtmax;A3A2SaA3").
Hypothesis OV7d : ltac2:(tb__ "0|0|
S0S9S65P9dS3cVW;Vst;Vtmax;A3A2SaA3").
Hypothesis TAB7c : ltac2:(tb__ "0|0|
S0S9S66P9dS3bVW;Vst;Vtmax;A3S64Z208S6bS6cS55S56S57S55S58A1A1A1A1A1A1A5SaA3").
Hypothesis TAB7d : ltac2:(tb__ "0|0|
S0S9S66P9dS3cVW;Vst;Vtmax;A3S64Z18U3eA5SaA3").
Hypothesis W7c : ltac2:(tb__ "0|0|
S0S9S1eS3S69A1A1SaA3").
Hypothesis W7d : ltac2:(tb__ "0|0|
S0S9S1eS3S6aA1A1SaA3").
Hypothesis D7c : ltac2:(tb__ "0|4|
S0S11SeSdSeS15S15A2M0A1M1SdS14A1M2A2M3A1S49S3S31VW;Vst;Vtmax;A3A1S3S69A1A2S10G3SfG1G2ScG0SfS15S15S3bVW;Vst;Vtmax;A3S17S2cA1A4SbG0A1A3SbS14A1A4A2A3").
Hypothesis D7d : ltac2:(tb__ "0|4|
S0S11SeSdSeS15S15A2M0A1M1SdS14A1M2A2M3A1S49S3S32VW;Vst;Vtmax;A3A1S3S6aA1A2S10G3SfG1G2ScG0SfS15S15S3cVW;Vst;Vtmax;A3S17S2cA1A4SbG0A1A3SbS14A1A4A2A3").
Hypothesis NX7c : ltac2:(tb__ "0|0|
S0S26S18S3S69A1A1S18S3S31VW;Vst;Vtmax;A3A1A1A3").
Hypothesis NX7d : ltac2:(tb__ "0|0|
S0S26S18S3S6aA1A1S18S3S32VW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7c : ltac2:(tb__ "0|0|
S44S14S2fS16S3S31VW;Vst;Vtmax;A3A1A1A3").
Hypothesis G7d : ltac2:(tb__ "0|0|
S44S14S2fS16S3S32VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7c : ltac2:(tb__ "0|0|
S43S14S1bS59S1aZ200A1S17S34A1A3S16S3S31VW;Vst;Vtmax;A3A1A1A3").
Hypothesis F7d : ltac2:(tb__ "0|0|
S43S14S1fS1bS59S1aZ200A1S17S34A1A3A1S16S3S32VW;Vst;Vtmax;A3A1A1A3").
Variables s8c s8d : wsub.
Hypothesis ENT8c : ltac2:(tb__ "0|0|
S0S9S5S69S38VW;Vst;Vtmax;A3Vs8c;A3SaA3").
Hypothesis ENT8d : ltac2:(tb__ "0|0|
S0S9S5S6aS38VW;Vst;Vtmax;A3Vs8d;A3SaA3").
Hypothesis SID8c : ltac2:(tb__ "0|0|
S0S9S4aVs8c;S27A2SaA3").
Hypothesis SID8d : ltac2:(tb__ "0|0|
S0S9S4aVs8d;S27A2SaA3").

Theorem spine_s7p : ltac2:(tb__ "0|0|
S47OF_;S63S60S19SdS53Q40A1A1S48S70VW;Vst;A2S61R5A1S2bVsegs;R8S2aR6A1A3S19S46Vsegs;RaS29Vsegs;S42VW;Vst;R9R8R7A5S38VW;Vst;Vtmax;A3R1R6A5R5A4FrhoX;S19S46Vsegs;RbS29Vsegs;S42VW;Vst;RaR9R8A5S30VW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC8 rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c870] GW [C7p W st tmax] [E7q1 W st tmax; E7q2 W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert7p.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 (rho_sub rhoX s8c))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7q1' (C8p W st tmax) s8c rhoX tp w ENT8c SID8c); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7q1', upd. lazy zeta.
      apply (class_restate_gen (E7q1 W st tmax) _ (creg7c W st tmax) 520 8128%nat A Kc rho tp w rhoX OV7c TAB7c W7c D7c NX7c); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ true Hw G7c F7c).
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC8 (rho_sub rhoX s8d))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW E7q2' (C8p W st tmax) s8d rhoX tp w ENT8d SID8d); [apply JGb_stable; [exact HUS | exact HKc]|].
      unfold E7q2', upd. lazy zeta.
      apply (class_restate_gen (E7q2 W st tmax) _ (creg7d W st tmax) 24 62%nat A Kc rho tp w rhoX OV7d TAB7d W7d D7d NX7d); [|exact Hw].
      exact (needed_range A Kc rho rhoX tp w _ false Hw G7d F7d).
  - left. reflexivity.
Qed.
End B12S.

Section B13S.

Variables (CC8 CC9 EE8a EE8b CC8ma : axst).
Hypothesis Cert8 : ltac2:(tb__ "0|1|
S0S9S6dS6fUfa0ScS25Zde378ScS25Z3c8c0SbS25A1A3A3S27ScS4VCC8;SbS4A1M0A3ScS4VEE8a;ScS4VEE8b;G0A3A3A6SaA3").

Hypothesis HCC8ma : ltac2:(tb__ "0|1|
S0S4VCC8ma;S36VW;Vst;Vtmax;VEE8a;S41ScSeS12S15A2M0SfS12S15UaS40A4SbG0A1A3SbS1cA1S13SbS14A1A9A3").
Hypothesis W8a : ltac2:(tb__ "0|0|
S0S9S1eS3VCC8ma;A1A1SaA3").
Hypothesis D8a : ltac2:(tb__ "0|4|
S0S11SeSdSeS15S15A2M0A1M1SdS14A1M2A2M3A1S49S3VEE8a;A1S3VCC8ma;A1A2S10G3SfG1G2SbG0A1SbS14A1A4A2A3").
Hypothesis NX8a : ltac2:(tb__ "0|0|
S0S26S18S3VCC8ma;A1A1S18S3VEE8a;A1A1A3").
Variables (s8 sd8 : wsub) (R8 : list sobj) (T8 : axst).
Hypothesis He8 : ltac2:(tb__ "0|1|
S0S11SdS1cA1M0A1S79VCC8ma;S5dVs8;A3S10G0VR8;A2A3").
Hypothesis Hchk8 : ltac2:(tb__ "0|0|
S0S9S78VCC8ma;S5dVs8;VR8;S73S8S4S7S5eA4A5SaA3").
Hypothesis HT8 : ltac2:(tb__ "0|0|
S0S4S7aVs8;S5dS74S7bS5fA1A1VCC8ma;VR8;A5VT8;A3").
Hypothesis FBC8 : ltac2:(tb__ "0|1|
S0S9S45S14S21S18S3VCC8ma;A1M0A1A1S16G0A1A3SaA3").
Hypothesis FBT8 : ltac2:(tb__ "0|0|
S0S9S45S14S21S18S3VT8;A1A1A1S16S3VCC8ma;A1A1A3SaA3").
Hypothesis ENT9 : ltac2:(tb__ "0|0|
S0S9S5S77VT8;S16S3VCC8ma;A1A1A2VCC9;Vsd8;A3SaA3").
Hypothesis SID9 : ltac2:(tb__ "0|0|
S0S9S4aVsd8;S27A2SaA3").
Hypothesis NXC8 : ltac2:(tb__ "0|0|
S7dS27S18S3VCC8ma;A1A1A2").

Variables (i8 : nat) (S8s : sstate).
Hypothesis SPL8 : ltac2:(tb__ "0|0|
S0S11S1dA1S75S3VEE8b;A1Vi8;S1aZ1000A1A3S10S1dVS8s;A2A3").
Let X8b : axst := ax_setS EE8b S8s.
Variables (s8b sd8b : wsub) (R8b : list sobj) (T8b : axst).
Hypothesis He8b : ltac2:(tb__ "0|1|
S0S11SdS1cA1M0A1S79VX8b;S5dVs8b;A3S10G0VR8b;A2A3").
Hypothesis Hchk8b : ltac2:(tb__ "0|0|
S0S9S78VX8b;S5dVs8b;VR8b;S73S8S4S7S5eA4A5SaA3").
Hypothesis HT8b : ltac2:(tb__ "0|0|
S0S4S7aVs8b;S5dS74S7bS5fA1A1VX8b;VR8b;A5VT8b;A3").
Hypothesis FBC8b : ltac2:(tb__ "0|1|
S0S9S45S14S21S18S3VX8b;A1M0A1A1S16G0A1A3SaA3").
Hypothesis FBT8b : ltac2:(tb__ "0|0|
S0S9S45S14S21S18S3VT8b;A1A1A1S16S3VX8b;A1A1A3SaA3").
Hypothesis NXC8b : ltac2:(tb__ "0|0|
S7dS27S18S3VX8b;A1A1A2").

Variables (i9 : nat) (SU SM : sstate).
Let U8b0 : axst := ltac2:(tb__ "0|0|
S6eScS14S1fS1bS59S17PcA1S1aZ1000A1A3A1SbS14A1A3VCC9;A2").
Hypothesis SPLU : ltac2:(tb__ "0|0|
S0S11S1dA1S75S3VU8b0;A1Vi9;S1aZ1000A1A3S10S1dVSU;A2A3").
Let U8b : axst := ax_setS U8b0 SU.
Hypothesis ENTU : ltac2:(tb__ "0|0|
S0S9S5S77VT8b;S16S3VX8b;A1A1A2VU8b;Vsd8b;A3SaA3").
Hypothesis SIDU : ltac2:(tb__ "0|0|
S0S9S4aVsd8b;S27A2SaA3").
Hypothesis MRG : ltac2:(tb__ "0|0|
S0S11S1dA1S76S3VU8b;A1Vi9;A2S10S1dVSM;A2A3").
Variable s9m : wsub.
Hypothesis ENTM : ltac2:(tb__ "0|0|
S0S9S5S6VU8b;VSM;A2VCC9;Vs9m;A3SaA3").
Hypothesis SIDM : ltac2:(tb__ "0|0|
S0S9S4aVs9m;S27A2SaA3").

Theorem spine_s8_gen : ltac2:(tb__ "0|2|
S47OF_;S63S60S19SdS53Q40A1A1M0S48S70VW;Vst;A2S61R5A1S2bVsegs;R8S2aR6A1A3S19G0S46Vsegs;RbS29Vsegs;S42VW;Vst;RaR9R8A5M1VCC9;R2R1A5R6A4FtpX;FrhoX;S19S46Vsegs;RbS29Vsegs;G1VCC8;R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC9 rhoE.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  apply (cfg_soundA segs 4000%nat [0xde378; 0x3c8c0] GW [CC8] [EE8a; EE8b] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - exact HST.
  - exact Cert8.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    +
      eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
      2:{ apply (call_gen nW st CC8ma T8 CC9 s8 R8 sd8 Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
                  eq_refl (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) He8 Hchk8 HT8 FBC8 FBT8 ENT9 SID9 NXC8 eq_refl
                  ok A Kc rho tp rhoX Q HUS HKc Hokf HC9). }
      rewrite HCC8ma. unfold upd. lazy zeta. rewrite HCC8ma in W8a, D8a, NX8a. unfold upd in W8a, D8a, NX8a.
      eapply SPA_restate; [exact W8a | exact D8a | exact NX8a | constructor | constructor | exact Hw].
    +
      eapply triple_conseq; [intros w Hw; exact (SPA_split segs (JGb W st A Kc rho) rhoX EE8b i8 (SLit 4096) S8s tp w SPL8 Hw) | intros w Hw; right; exact Hw |].
      apply (call_gen nW st X8b T8b U8b s8b R8b sd8b Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
               eq_refl (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) He8b Hchk8b HT8b FBC8b FBT8b ENTU SIDU NXC8b eq_refl
               ok A Kc rho tp rhoX Q HUS HKc Hokf).
      intros rhoY tpY.
      eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HC9 (rho_sub rhoY s9m) tpY)].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW (ax_setS U8b SM) CC9 s9m rhoY tpY w ENTM SIDM HST).
      exact (SPA_merge segs (JGb W st A Kc rho) rhoY U8b i9 SM tpY w MRG Hw).
  - left. reflexivity.
Qed.
End B13S.
End S8.
End SpineMallocS8.

(* [comment removed for export] *)
Module SpineCallocS6.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "entailsA"; "la_state"; "mkLeafA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "cons"; "nil"; "Some"; "option"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "sprop"; "valuation"; "ss_next"; "ss_facts"; "sv"; "SLit"; "eval"; "sprop_below"; "SVar"; "rw"; "sobj"; "swf"; "agree_below"; "holds"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SUB"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "liftKA"; "LQA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "C5m1"; "C5m2"; "C5d"; "C5e"; "E5m1"; "E5m2"; "ab_e"; "F_gen"; "BR"; "C5c"; "C6"; "E5j"; "LLe"; "LRe"; "V_RZ"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5"; "JGb"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "memset_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6"; "re8"; "a0e2"; "len1e"; "len2e"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "modulo"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "cnt_of"; "chk_of"; "cls_of"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4"; "pvals_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "rz"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma Forall_holds_agree : ltac2:(tb__ "0|1|
S41S12S12S9S11A1S1dR4R3R2A3S0S7S43S11S18R5A1R2A3S8A3S60S11S1eR5A1M0R3A3S60S11G0R4A3F_;F_;F_;FF;Frho';Frho;Fn;").
Proof.
  intros n rho rho' F Hag Hb HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree n rho rho' p Hag (proj1 (forallb_forall _ _) Hb p Hp))). exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Definition len1e : sv := ltac2:(tb__ "0|1|
S10S21S10S1fS10S20S10S1fS10S1fS2fS19S37A1A3S16N8A1A3S16Z3A1M0A3S16Z1A1A3S10S20S2fG0A3A3").
Definition re8 : sv := ltac2:(tb__ "0|0|
S10S22S10S1fS10S1fS10S1fS2fS19S37A1A3S19PcA1A3S16Z7A1A3S16Zfffffffffffffff8A1A3").
Definition a0e2 : sv := ltac2:(tb__ "0|0|
S10S1fS10S20S4fS16Z3A1A3S3aA3").
Definition len2e : sv := ltac2:(tb__ "0|1|
S10S21S10S1fS10S20S10S1fS10S1fS4fS10S1fS10S21S2fS4fA3S19S38A1A3A3S16N8A1A3S16Z3A1M0A3S16Z1A1A3S10S20S4fG0A3A3").

Section PSVals.
Variable rho : valuation.
Variables SB c x rzv sz n : Z.
Hypothesis PV : ltac2:(tb__ "0|0|
S6bVrho;VSB;Vc;Vx;Vrzv;Vsz;Vn;A7").
Let ab : Z := ltac2:(tb__ "0|0|
S53S53VSB;S55Vc;S57Z2Z20A2A2A2S55Z10Vx;A2A2").
Let r8 : Z := ltac2:(tb__ "0|1|
S58S53Vn;Z7A2M0S56G0Z8A2A2").
Ltac pv := pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).

Lemma pv_len1 : ltac2:(tb__ "0|0|
S0S3eQ40A1S17Vrho;S51A2S17Vrho;S35A2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_ab rho _ _ _ _ _ _ PV) as EB. cbn zeta in EB.
  apply bv_eq. unfold len1e, LLe. cbn [eval]. fold ab_e. unfold V_RZ. rewrite E150.
  rewrite sub_val, add_val, srl_val, add_val, add_val, srl_val, srl_val, EB, !u64_lit by lia. change (3 mod 64) with 3.
  replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity.
  rewrite (Z.mod_small (_ + rzv)) by lia.
  replace ((SB + c * 2 ^ 32 + 16 * x + rzv + (2 ^ 64 - 8)) mod 2 ^ 64) with (SB + c * 2 ^ 32 + 16 * x + rzv - 8).
  2:{ replace (SB + c * 2 ^ 32 + 16 * x + rzv + (2 ^ 64 - 8)) with ((SB + c * 2 ^ 32 + 16 * x + rzv - 8) + 1 * 2 ^ 64) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_mod SB (2 ^ 16) ltac:(lia)). pose proof (Z.div_mod rzv 16 ltac:(lia)).
  set (q := SB / 2 ^ 16) in *. set (r := rzv / 16) in *.
  replace (SB + c * 2 ^ 32 + 16 * x + rzv - 8) with ((q * 2 ^ 13 + c * 2 ^ 29 + 2 * x + 2 * r - 1) * 8) by lia.
  replace (SB + c * 2 ^ 32 + 16 * x) with ((q * 2 ^ 13 + c * 2 ^ 29 + 2 * x) * 8) by lia.
  replace rzv with (2 * r * 8) at 3 by lia.
  rewrite !Z.div_mul by lia. rewrite (Z.mod_small (_ + 1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma pv_re8 : ltac2:(tb__ "0|0|
S0S40S3fQ40S17Vrho;S4fA2A2S53S53Vab;Vrzv;A2Vr8;A2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_ab rho _ _ _ _ _ _ PV) as EB. cbn zeta in EB. fold ab in EB.
  pose proof (r8_facts rho _ _ _ _ _ _ PV) as (R1 & R2 & R3 & R4). cbn zeta in R1, R2, R3, R4. fold r8 in R1, R2, R3, R4.
  unfold re8. cbn [eval]. fold ab_e. unfold V_RZ. rewrite E150, E12.
  rewrite and_val, add_val, add_val, add_val, EB, !u64_lit by lia.
  change 18446744073709551608 with (2 ^ 64 - 2 ^ 3).
  rewrite (Z.mod_small (ab + rzv)) by (unfold ab; lia). rewrite (Z.mod_small (ab + rzv + n)) by (unfold ab; destruct (Z_lt_dec n 8); lia).
  rewrite Z.mod_small by (unfold ab; destruct (Z_lt_dec n 8); lia).
  rewrite land_high_mask by (unfold ab; destruct (Z_lt_dec n 8); lia). change (2 ^ 3) with 8.
  pose proof (Z.div_mod SB (2 ^ 16) ltac:(lia)). pose proof (Z.div_mod rzv 16 ltac:(lia)).
  assert (E : (ab + rzv + n + 7) mod 8 = (n + 7) mod 8).
  { unfold ab. replace (SB + c * 2 ^ 32 + 16 * x + rzv + n + 7) with ((n + 7) + (SB / 2 ^ 16 * 2 ^ 13 + c * 2 ^ 29 + 2 * x + rzv / 16 * 2) * 8) by lia.
    apply Z.mod_add; lia. }
  rewrite E. unfold r8. lia.
Qed.

Lemma pv_a0e2 : ltac2:(tb__ "0|0|
S0S3eQ40A1S17Vrho;S50A2S17Vrho;S31A2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_br rho _ _ _ _ _ _ PV) as EBR. cbn zeta in EBR. fold ab in EBR.
  pose proof (r8_facts rho _ _ _ _ _ _ PV) as (R1 & R2 & R3 & R4). cbn zeta in R1, R2, R3, R4. fold r8 in R1, R2, R3, R4, EBR.
  apply bv_eq. rewrite EBR. unfold a0e2, shb. cbn [eval]. fold re8. rewrite add_val, srl_val, pv_re8, !u64_lit by (unfold SHADOW_OFF; lia).
  change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (Bf : 0 <= ab + rzv + r8 /\ ab + rzv + r8 <= 140737479966720) by (unfold ab; destruct (Z_lt_dec n 8); lia).
  destruct (Sh_small rho _ _ _ _ _ _ PV (ab + rzv + r8) Bf) as (_ & E & _). rewrite E.
  unfold Sh. pose proof (Z.div_mod rzv 16 ltac:(lia)).
  replace (ab + rzv + r8) with (ab + rzv + (r8 / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

Lemma pv_len2 : ltac2:(tb__ "0|0|
S0S3eQ40A1S17Vrho;S52A2S17Vrho;S36A2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_ab rho _ _ _ _ _ _ PV) as EB. cbn zeta in EB. fold ab in EB.
  pose proof (pv_lr rho _ _ _ _ _ _ PV) as [ELR LR0]. cbn zeta in ELR, LR0.
  pose proof (r8_facts rho _ _ _ _ _ _ PV) as (R1 & R2 & R3 & R4). cbn zeta in R1, R2, R3, R4. fold r8 in R1, R2, R3, R4, ELR, LR0.
  apply bv_eq. rewrite ELR. unfold len2e. cbn [eval]. fold re8. fold ab_e. unfold V_SIZE. rewrite E148.
  rewrite sub_val, add_val, srl_val, add_val, add_val, add_val, sub_val, srl_val, pv_re8, EB, !u64_lit by lia. change (3 mod 64) with 3.
  replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity.
  assert (Bf : 0 <= ab /\ ab + sz <= 140737479966720 /\ rzv + r8 <= sz) by (unfold ab; destruct (Z_lt_dec n 8); lia).
  replace ((ab - (ab + rzv + r8)) mod 2 ^ 64) with (2 ^ 64 - (rzv + r8)) by (rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small by lia; lia).
  replace ((2 ^ 64 - (rzv + r8) + sz) mod 2 ^ 64) with (sz - rzv - r8) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
  rewrite (Z.mod_small (ab + rzv + r8 + _)) by lia.
  replace ((ab + sz + (2 ^ 64 - 8)) mod 2 ^ 64) with (ab + sz - 8) by (rewrite <- (Z.mod_add _ (-1)) by lia; rewrite Z.mod_small by lia; lia).
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_mod SB (2 ^ 16) ltac:(lia)). pose proof (Z.div_mod rzv 16 ltac:(lia)). pose proof (Z.div_mod sz 16 ltac:(lia)).
  set (q := SB / 2 ^ 16) in *. set (r := rzv / 16) in *. set (t := sz / 16) in *.
  replace (ab + sz - 8) with ((q * 2 ^ 13 + c * 2 ^ 29 + 2 * x + 2 * t - 1) * 8) by (unfold ab; lia).
  replace (ab + rzv + r8) with ((q * 2 ^ 13 + c * 2 ^ 29 + 2 * x + 2 * r + r8 / 8) * 8) by (unfold ab; lia).
  replace (sz - rzv - r8) with ((2 * t - 2 * r - r8 / 8) * 8) by lia.
  rewrite !Z.div_mul by lia. rewrite (Z.mod_small (_ + 1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
End PSVals.

Section S6.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S4bVAInv;VW;Vst;VA;VKc;S19PcA1A6").

Lemma JGb_pvals : ltac2:(tb__ "0|3|
S4cS49S12S12S9S3eQ40M0A1A1S3cS2S23Vsegs;S42VW;Vst;R7R6R5A5R1R4R3R2A6S44S11S30S14S1R2A1A1A3S54Z1S5cR9S3fG0S1aR7PcM1A2A2A2A2S3fG0S1aR8G1A2A2S40S6bR8S4eS4dRbA1A1S5eR1A1M2S5dRbR1A2S6eR1A1S6dG2A1R1A7Tnv;F_;F_;F_;FE;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w E Hw HG Hcnt. cbn zeta. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as [Hag HJ]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in HN, Hcnt |- *.
  assert (E12' : rw rhoE 12%positive = Z_to_bv 64 nv). { rewrite E12. unfold nv. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (E148 : rw rhoE 148%positive = Z_to_bv 64 (Size (cls_of nv))). { rewrite <- (Hagw 148%positive) by (unfold GW; lia). reflexivity. }
  assert (E150 : rw rhoE 150%positive = Z_to_bv 64 (rz nv)). { rewrite <- (Hagw 150%positive) by (unfold GW; lia). reflexivity. }
  assert (E155 : rw rhoE 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A))). { rewrite <- (Hagw 155%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  assert (E159 : rw rhoE 159%positive = Z_to_bv 64 (chk_of A nv)). { rewrite <- (Hagw 159%positive) by (unfold GW; lia). reflexivity. }
  assert (HF : forall p, In p F_gen -> holds rhoE p). { intros p Hp. exact (fact_of_stateB nW st A Kc rho rhoE tp _ E p Hw (HG p Hp)). }
  assert (Hnv : nv <= 64512).
  { pose proof (HF (SPUle (SVar 12) (SLit 64512)) ltac:(unfold F_gen; cbn; tauto)) as F. cbn [holds eval] in F. rewrite E12', !u64_lit in F by lia. exact F. }
  assert (RZF : 16 <= rz nv <= 1024 /\ rz nv mod 16 = 0).
  { pose proof (HF (SPUle (SLit 16) (SVar V_RZ)) ltac:(unfold F_gen; cbn; tauto)) as F1.
    pose proof (HF (SPUle (SVar V_RZ) (SLit 1024)) ltac:(unfold F_gen; cbn; tauto)) as F2.
    pose proof (HF (SPAlign V_RZ 4) ltac:(unfold F_gen; cbn; tauto)) as F3.
    cbn [holds eval] in F1, F2, F3. unfold V_RZ in F1, F2, F3. rewrite E150 in F1, F2, F3. pose proof (rz_bound nv). rewrite !u64_lit in F1, F2 by lia.
    destruct F3 as [_ F3]. rewrite u64_lit in F3 by lia. change (2 ^ 4) with 16 in F3. lia. }
  pose proof (cls_facts nv ltac:(lia)) as (C1 & C2 & C3 & C4).
  pose proof (blk_facts segs A rhoE tp _ nv HA ltac:(lia) Hcnt) as BF. cbn zeta in BF. destruct BF as (Bx & Bal & Blo & Bhi & Breg & _ & _).
  pose proof (geom_old _ (proj1 HA)) as HGe. rewrite kSpaceSize_val in HGe. unfold HIGH_SHADOW_END in HGe.
  destruct HGe as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G12 & G13 & G14 & _). pose proof (topG_range (aa_geom A)) as TG.
  unfold kUserSpaceSize in Bhi. unfold region_beg, kRegionSize, kFreeArraySize in Blo, Bhi, Breg. rewrite kSpaceSize_val in Breg.
  assert (NFIT : nv + rz nv <= Size (cls_of nv) /\ (nv < 8 -> 8 + rz nv <= Size (cls_of nv))).
  { clear -C2 Hnv HN. unfold needed8, round_up in C2.
    pose proof (Z.mul_div_le (Z.max nv 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.div_mod (Z.max nv 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (Z.max nv 8 + 8 - 1) 8 ltac:(lia)). split; [|intros]; lia. }
  unfold pvals_ok. repeat split; try assumption; clear -C1 C2 C3 Hnv HN Bx RZF NFIT G12 G13 G14 TG Blo Bhi Breg; lia.
Qed.

Section Call.
Variables (Cst T D : axst) (s : wsub) (R : list sobj) (sd : wsub).
Variables (Pre : axst) (Posts : list leafA) (Pret : sstate).
Hypothesis HPosts : ltac2:(tb__ "0|0|
S0S9S3A1VPosts;SaS3S6S59VPret;A1S6cA2SbS3A1A3A3").
Hypothesis Hsum : ltac2:(tb__ "0|0|
S3cOF_;S27S12S9S3eQ40A1A1S24S48R4R3A3S28S48S61R4A3S3bS48R6S23S48R5VPre;R4R3A5S26S48R5S61R4R3VPosts;A6A4F_;F_;Ftp;Frho;FJx;Fok;").
Hypothesis He : ltac2:(tb__ "0|1|
S0SdS9S1bA1M0A1S65VCst;VPre;Vs;A3ScG0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0S7S64VCst;VPre;Vs;VR;S5fS3S2S5VPosts;A4A5S8A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S2S66Vs;VPre;S59VPret;A1VCst;VR;A5VT;A3").
Hypothesis FBC : ltac2:(tb__ "0|1|
S0S7S43S11S18S13S1VCst;A1M0A1A1S14G0A1A3S8A3").
Hypothesis FBT : ltac2:(tb__ "0|0|
S0S7S43S11S18S13S1VT;A1A1A1S14S1VCst;A1A1A3S8A3").
Hypothesis ENT : ltac2:(tb__ "0|0|
S0S7S4S63VT;S14S1VCst;A1A1A2VD;Vsd;A3S8A3").
Hypothesis SID : ltac2:(tb__ "0|0|
S0S7S5aVsd;S39A2S8A3").
Hypothesis NXC : ltac2:(tb__ "0|0|
S68S39S13S1VCst;A1A1A2").
Hypothesis NPre : ltac2:(tb__ "0|0|
S0S41S13S1VPre;A1A1S61A3").

Lemma call_gen : ltac2:(tb__ "0|1|
S3cOF_;S4cS49S12S9S3eQ40A1A1M0S12S3dS5bVW;Vst;A2S4aR6A1S24Vsegs;R9S25R7A1A3S12G0S3bVsegs;RcS23Vsegs;S42VW;Vst;RbRaR9A5VD;R2R1A5R6A4FtpX;FrhoX;S3bVsegs;RbS23Vsegs;S42VW;Vst;RaR9R8A5VCst;R6R7A5R5A4F_;F_;F_;F_;FQ;FrhoE;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp rhoE Q HUS HKc Hokf HD.
  pose proof (JGb_stable nW st A Kc rho HUS HKc) as HST.
  set (Jf := (fun (_ : valuation) t tr md => JGb W st A Kc rho rhoE t tr md) : jpredA).
  assert (Jf_okf : ok_frameA segs ok Jf).
  { intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf rhoE t tr ms md msv' HK HMI Hh Hp Hs). }
  assert (Jf_st : stableA segs NF Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }

  apply (triple_pre_pure segs ok _ _ (Forall (holds rhoE) (ss_facts (ax_S Cst)))).
  { intros w Hw. exact (SPA_facts_hold segs _ rhoE Cst tp w Hw). }
  intros HFC.
  apply (call_soundA segs ok (JGb W st A Kc rho) Jf Jf (JGb W st A Kc rho) Cst Pre s R Posts Q rhoE tp He Hchk).
  - intros rho1 tp1. rewrite NPre. exact (Hsum ok Jf rho1 tp1 Jf_okf Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ'].
    eapply agree_below_le; [exact NXC | exact (proj1 HLK)].
  - intros L rho' tpL HinL Hag. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state]. rewrite HT.
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HD (rho_sub rho' sd) tpL)].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (ax_with_facts T (ss_facts (ax_S Cst))) D sd rho' tpL w ENT SID HST).
    apply SPA_refacts; [exact Hw | exact FBT |]. intros _.
    exact (Forall_holds_agree _ rhoE rho' _ Hag FBC HFC).
Qed.
End Call.

Section B7S.
Hypothesis Cert5c : ltac2:(tb__ "0|1|
S0S7S62S67Ufa0SaS40Zde378SbS40A1A3S39SaS2S32VW;Vst;Vtmax;A3SbS2A1M0A3SaS2S2dVW;Vst;Vtmax;A3G0A3A6S8A3").
Hypothesis G5m1 : ltac2:(tb__ "0|0|
S44S11S30S14S1S2dVW;Vst;Vtmax;A3A1A1A3").
Hypothesis W5m1 : ltac2:(tb__ "0|0|
S0S7S1cS1S29VW;Vst;Vtmax;A3A1A1S8A3").
Hypothesis D5m1 : ltac2:(tb__ "0|4|
S0SdSfS9SfS15S15A2M0A1M1S9S11A1M2A2M3A1S69S1S2dVW;Vst;Vtmax;A3A1S1S29VW;Vst;Vtmax;A3A1A2ScG3SeG1G2SaG0SeS15S15S51S35A4SbG0A1A3SbS11A1A4A2A3").
Hypothesis NX5m1 : ltac2:(tb__ "0|0|
S0S41S13S1S29VW;Vst;Vtmax;A3A1A1S13S1S2dVW;Vst;Vtmax;A3A1A1A3").
Variables (s51 sd51 : wsub) (R51 : list sobj) (T51 : axst).
Hypothesis He51 : ltac2:(tb__ "0|1|
S0SdS9S1bA1M0A1S65S29VW;Vst;Vtmax;A3S45Vs51;A3ScG0VR51;A2A3").
Hypothesis Hchk51 : ltac2:(tb__ "0|0|
S0S7S64S29VW;Vst;Vtmax;A3S45Vs51;VR51;S5fS3S2S5S46A4A5S8A3").
Hypothesis HT51 : ltac2:(tb__ "0|0|
S0S2S66Vs51;S45S59S6aS47A1A1S29VW;Vst;Vtmax;A3VR51;A5VT51;A3").
Hypothesis FBC51 : ltac2:(tb__ "0|1|
S0S7S43S11S18S13S1S29VW;Vst;Vtmax;A3A1M0A1A1S14G0A1A3S8A3").
Hypothesis FBT51 : ltac2:(tb__ "0|0|
S0S7S43S11S18S13S1VT51;A1A1A1S14S1S29VW;Vst;Vtmax;A3A1A1A3S8A3").
Hypothesis ENT51 : ltac2:(tb__ "0|0|
S0S7S4S63VT51;S14S1S29VW;Vst;Vtmax;A3A1A1A2S2bVW;Vst;Vtmax;A3Vsd51;A3S8A3").
Hypothesis SID51 : ltac2:(tb__ "0|0|
S0S7S5aVsd51;S39A2S8A3").
Hypothesis NXC51 : ltac2:(tb__ "0|0|
S68S39S13S1S29VW;Vst;Vtmax;A3A1A1A2").

Theorem spine_s5c : ltac2:(tb__ "0|3|
S3cOF_;S4cS49S12S9S3eQ40M0A1A1M1S3dS5bVW;Vst;A2S4aR5A1S24Vsegs;R8S25R6A1A3S54Z1S5cR8S3fG0S1aR6PcA2A2A2A2S12G1S3bVsegs;RcS23Vsegs;S42VW;Vst;RbRaR9A5M2S2bVW;Vst;Vtmax;A3R2R1A5R7A4FtpX;FrhoX;S12S3bVsegs;RcS23Vsegs;G2S32VW;Vst;Vtmax;A3R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf Hcnt HC rhoE.
  apply (cfg_soundA segs 4000%nat [0xde378] GW [C5c W st tmax] [E5m1 W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert5c.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (call_gen (C5m1 W st tmax) T51 (C5d W st tmax) s51 R51 sd51 Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
                eq_refl (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) He51 Hchk51 HT51 FBC51 FBT51 ENT51 SID51 NXC51 eq_refl
                ok A Kc rho tp rhoX Q HUS HKc Hokf HC). }
    pose proof (JGb_pvals A Kc rho rhoX tp w _ Hw G5m1 Hcnt) as PV. cbn zeta in PV.
    unfold C5m1, upd. lazy zeta. eapply SPA_restate; [exact W5m1 | exact D5m1 | exact NX5m1 | | constructor | exact Hw].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_len1 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End B7S.

Section B8S.
Hypothesis Cert5d : ltac2:(tb__ "0|1|
S0S7S62S67Ufa0SaS40Zde378SbS40A1A3S39SaS2S2bVW;Vst;Vtmax;A3SbS2A1M0A3SaS2S2eVW;Vst;Vtmax;A3G0A3A6S8A3").
Hypothesis G5m2 : ltac2:(tb__ "0|0|
S44S11S30S14S1S2eVW;Vst;Vtmax;A3A1A1A3").
Hypothesis W5m2 : ltac2:(tb__ "0|0|
S0S7S1cS1S2aVW;Vst;Vtmax;A3A1A1S8A3").
Hypothesis D5m2 : ltac2:(tb__ "0|4|
S0SdSfS9SfS15S15A2M0A1M1S9S11A1M2A2M3A1S69S1S2eVW;Vst;Vtmax;A3A1S1S2aVW;Vst;Vtmax;A3A1A2ScG3SeG1G2SaG0SeS15S15S50S31A4SaG0SeS15S15S52S36A4SbG0A1A3A3SbS11A1A4A2A3").
Hypothesis NX5m2 : ltac2:(tb__ "0|0|
S0S41S13S1S2aVW;Vst;Vtmax;A3A1A1S13S1S2eVW;Vst;Vtmax;A3A1A1A3").
Variables (s52 sd52 : wsub) (R52 : list sobj) (T52 : axst).
Hypothesis He52 : ltac2:(tb__ "0|1|
S0SdS9S1bA1M0A1S65S2aVW;Vst;Vtmax;A3S45Vs52;A3ScG0VR52;A2A3").
Hypothesis Hchk52 : ltac2:(tb__ "0|0|
S0S7S64S2aVW;Vst;Vtmax;A3S45Vs52;VR52;S5fS3S2S5S46A4A5S8A3").
Hypothesis HT52 : ltac2:(tb__ "0|0|
S0S2S66Vs52;S45S59S6aS47A1A1S2aVW;Vst;Vtmax;A3VR52;A5VT52;A3").
Hypothesis FBC52 : ltac2:(tb__ "0|1|
S0S7S43S11S18S13S1S2aVW;Vst;Vtmax;A3A1M0A1A1S14G0A1A3S8A3").
Hypothesis FBT52 : ltac2:(tb__ "0|0|
S0S7S43S11S18S13S1VT52;A1A1A1S14S1S2aVW;Vst;Vtmax;A3A1A1A3S8A3").
Hypothesis ENT52 : ltac2:(tb__ "0|0|
S0S7S4S63VT52;S14S1S2aVW;Vst;Vtmax;A3A1A1A2S2cVW;Vst;Vtmax;A3Vsd52;A3S8A3").
Hypothesis SID52 : ltac2:(tb__ "0|0|
S0S7S5aVsd52;S39A2S8A3").
Hypothesis NXC52 : ltac2:(tb__ "0|0|
S68S39S13S1S2aVW;Vst;Vtmax;A3A1A1A2").

Theorem spine_s5d : ltac2:(tb__ "0|3|
S3cOF_;S4cS49S12S9S3eQ40M0A1A1M1S3dS5bVW;Vst;A2S4aR5A1S24Vsegs;R8S25R6A1A3S54Z1S5cR8S3fG0S1aR6PcA2A2A2A2S12G1S3bVsegs;RcS23Vsegs;S42VW;Vst;RbRaR9A5M2S2cVW;Vst;Vtmax;A3R2R1A5R7A4FtpX;FrhoX;S12S3bVsegs;RcS23Vsegs;G2S2bVW;Vst;Vtmax;A3R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf Hcnt HC rhoE.
  apply (cfg_soundA segs 4000%nat [0xde378] GW [C5d W st tmax] [E5m2 W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert5d.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (call_gen (C5m2 W st tmax) T52 (C5e W st tmax) s52 R52 sd52 Pre_memsetA Posts_memsetA (P_ret_memset memset_entryA)
                eq_refl (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) He52 Hchk52 HT52 FBC52 FBT52 ENT52 SID52 NXC52 eq_refl
                ok A Kc rho tp rhoX Q HUS HKc Hokf HC). }
    pose proof (JGb_pvals A Kc rho rhoX tp w _ Hw G5m2 Hcnt) as PV. cbn zeta in PV.
    unfold C5m2, upd. lazy zeta. eapply SPA_restate; [exact W5m2 | exact D5m2 | exact NX5m2 | | constructor | exact Hw].
    unfold diffs_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + exact (pv_a0e2 rhoX _ _ _ _ _ _ PV).
    + exact (pv_len2 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End B8S.

Section B9S.
Hypothesis Cert5e : ltac2:(tb__ "0|1|
S0S7S62S67Ufa0SaS40Z3c678SbS40A1A3S39SaS2S2cVW;Vst;Vtmax;A3SbS2A1M0A3SaS2S34VW;Vst;Vtmax;A3G0A3A6S8A3").
Variable s6j : wsub.
Hypothesis ENT6j : ltac2:(tb__ "0|0|
S0S7S4S34VW;Vst;Vtmax;A3S33VW;Vst;Vtmax;A3Vs6j;A3S8A3").
Hypothesis SID6j : ltac2:(tb__ "0|0|
S0S7S5aVs6j;S39A2S8A3").
Theorem spine_s5e : ltac2:(tb__ "0|0|
S3cOF_;S4cS49S12S9S3eQ40A1A1S3dS5bVW;Vst;A2S4aR5A1S24Vsegs;R8S25R6A1A3S12S3bVsegs;RaS23Vsegs;S42VW;Vst;R9R8R7A5S33VW;Vst;Vtmax;A3R1R6A5R5A4FrhoX;S12S3bVsegs;RbS23Vsegs;S42VW;Vst;RaR9R8A5S2cVW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c678] GW [C5e W st tmax] [E5j W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert5e.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s6j))].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E5j W st tmax) (C6 W st tmax) s6j rhoX tp w ENT6j SID6j); [|exact Hw].
    apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End B9S.
End S6.
End SpineCallocS6.

(* [comment removed for export] *)
Module SpineMallocR3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "rw"; "SLit"; "SVar"; "SAlu"; "rm"; "cell"; "ss_objs"; "sprop"; "ss_facts"; "SPBranch"; "eval"; "mkCell"; "obj_range"; "ss_lenient"; "ss_next"; "SExt"; "SPNot"; "ext_low"; "smatch"; "sstate"; "swf"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "sub"; "to_nat"; "of_nat"; "pow"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "bool"; "true"; "pair"; "prod"; "false"; "nat"; "option"; "app"; "Some"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "entailsA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "PV4"; "PV6"; "PV7"; "keepn"; "GR"; "O_cell"; "PNX"; "O_pcm"; "O_ri"; "vK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3.POP"; "JRpop"; "phK"; "O_dstc"; "O_srcc"; "e_end"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "FAb"; "PCE"; "ph_fill"; "frozen"; "ghosts"; "mkPh"; "ph_cnt"; "ph_f"; "ph_pop"; "ph_ri"; "ph_u"; "phase"; "rmlink"; "entryR"; "gh_new"; "gh_nf"; "rlink"; "zoneR"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "map"; "skipn"; "@Stdlib.Lists.List"; "In"; "incl"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "wsub_id_below"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "cell_ok"; "view"; "acell"; "c_addr"; "c_w"; "mkACell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "pc_base"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "IMG_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_thread"; "cs_cache"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refill_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "JK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2"; "BASEF"; "BASEO"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sext32_small : ltac2:(tb__ "0|2|
S0S3S1fZ0R1A2S20R1S25Z2Z1fA2A2A2S2S35Q40M0A1S1aS2aQ20S36G0R2A2M1A3G1A3F_;Fz;").
Proof.
  intros z Hz. unfold ext_low. apply bv_eq.
  assert (E : bv_unsigned (bv_extract 0 32 (Z_to_bv 64 z)) = z).
  { rewrite bv_extract_unsigned. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.shiftr_0_r.
    change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). rewrite (Z.mod_small z (2 ^ 64)) by lia. apply Z.mod_small. lia. }
  rewrite sext64_32_small by (rewrite E; lia). rewrite E. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). symmetry. apply Z.mod_small. lia.
Qed.

Lemma view_absorb_out : ltac2:(tb__ "0|1|
S7S27S6A1S6fS0S6S68S6R1R4A3S4S3S1fS32S0S0S15R6R2A2M0A3R3A2S20R3S33S0S0G0A3A2A2A1F_;Fo;S2S2fS35Q8A1A1S74S34SdS6dR5R4R3A3A1R2A3S74S34SdR5A1R2A3A3F_;Fz;Fms;FR;Frho;").
Proof.
  intros rho R ms z Hout. unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  unfold rd_of. rewrite rm_absorb_out; [reflexivity|].
  intros (o & Ho & Hr). apply (Hout o Ho). rewrite u64_lit in Hr by lia. exact Hr.
Qed.

Lemma rmlink_absorb : ltac2:(tb__ "0|1|
S35Q40A1S2fS35Q8A1A1F_;S7S27S6A1S6fS5eR4SdR3A1A2S6S68S6R1R4A3S5S1fS33S0S0S15R6R2A2M0A3S86A2S1fS85S32S0S0G0A3A2A2F_;Fo;S5eR6SdS6dR5R4R3A3A1A2F_;F_;Fms;FR;Frho;Ff0;").
Proof.
  intros f0 rho R ms H HR a Ha. rewrite rm_absorb_out; [exact (H a Ha)|].
  intros (o & Ho & Hr). rewrite u64_lit in Hr by (unfold IMG_LO, IMG_HI in Ha; lia). destruct (HR o Ho); lia.
Qed.

Lemma cell_ok_agree_range : ltac2:(tb__ "0|1|
S72S72S75S0S3S1fS76R2A1M0R1A2S20R1S1eG0S24S77R2A1A1A2A2A2S2S2fS35Q8A1A1R4R2A1R5R2A1A3F_;Fz;S73R4R2A2S73R4R3A2F_;F_;Fcc;Fm';Fm;").
Proof. intros m m' cc H Hc j Hj. rewrite H by lia. exact (Hc j Hj). Qed.

Lemma ph_eta : ltac2:(tb__ "0|0|
S5dS2S5dR1S57S5cR1A1S59R1A1S54R1A1S5aR1A1S58R1A1S5bR1A1A6A3Fp;").
Proof. intros p. destruct p. reflexivity. Qed.

Lemma nth_skipn_Z : ltac2:(tb__ "0|0|
S27S0A1S2eS2eS0S2S0S64S0R2S67S0R3R4A3R1A4S64S0S82R3R2A2R4R1A4A3Fd;Fi;Fn;Fl;").
Proof. intros l n. revert l. induction n as [|n IH]; intros l i d; [reflexivity|]. destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn Nat.add nth]. apply IH. Qed.

Section POP.

Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S2S7eVst;S7dA3S2S27S7cA1VW;S28S7cA1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S5fVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let k : Z := kchunks c.

Variable ph : phase.
Hypothesis PH0 : ltac2:(tb__ "0|0|
S3S2S0S5aVph;A1Z0A3S3S2S29S58Vph;A1S2dA3S2S29S5bVph;A1S2dA3A2A2").
Definition phK (i : Z) : phase := ltac2:(tb__ "0|0|
S57S5cVph;A1S59Vph;A1S54Vph;A1Vi;S2dS2dA6").
Variable faP : list Z.
Let nfP : Z := Z.of_nat (length faP).
Hypothesis HSRC : ltac2:(tb__ "0|1|
S0S72S3S1fZ0M0R2A2S1fR2Vk;A2A2S62VA;Vrb;S4aR3A1S74S34SdVrb;A1A2R2A5S0S3S1fG0R1A2S20R1VnfP;A2A2S73R5S78S1eS52VA;Vrb;A2S21Z4R2A2A2U4S64S0S23R2A1VfaP;G0A4A3A2F_;Fidx;F_;F_;Fm;Fi;").
Hypothesis HKF : k <= nfP.
Hypothesis HNFP : 4 * nfP <= 536870912.
Hypothesis HFILLR : ltac2:(tb__ "0|4|
S20Z0M0S54Vph;A1M1A2S3S1fG0S61VA;Vrb;A2M2A2S3S2S0S1eG2S60VA;Vrb;A2M3A2VnfP;A3S1fG1G3A2A2A2F_;").
Hypothesis HIDS : ltac2:(tb__ "0|0|
S0S68S0R1VfaP;A3S3S1fZ0R2A2S20R2S25Z2Z1cA2A2A2F_;Fx;").
Hypothesis HCACHE : ltac2:(tb__ "0|0|
S2S27S0A1S8aS8bVc;S8dVA;Vnv;A2A2A1S67S0S23S22VnfP;Vk;A2A1VfaP;A3A3").

Lemma zone_thread : ltac2:(tb__ "0|2|
S0S0S3S1fS1eS89S88VA;A1A1M0Z120A2R1A2S20R1S1eG0Zc60A2A2A2S63VA;Vrb;S4aR3A1R2A4S3S1fS1eS53VA;Vrb;A2Z10A2M1R3A2S20R3S1eG1S21Z4R4A2A2A2A2F_;F_;Fz;Fi;").
Proof.
  intros i z Hz HZ.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & _ & (_ & MU0 & MU1 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof (Zle_0_nat (length (cs_free_array (cst_of A nv)))) as NF0.
  unfold zoneR, phK in HZ. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri] in HZ. fold nv c in HZ.
  unfold U0, F0, FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize, Sh, SHADOW_OFF in HZ. fold nv c in HZ.
  destruct HZ as [[_ X]|[[_ X]|[[_ X]|[[_ X]|[[X X2]|[X|[[X _]|[X _]]]]]]]]; try discriminate X; try exact X; exfalso.
  - clear -X Hz MU0 MU1 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MU0 MU1 C1 G13 G14 TG PS1 T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG TB T1 T2. lia.
  - clear -X Hz MF0 NF0 C1 G13 G14 TG PS1 T1 T2. lia.
  - destruct (HFILLR X2) as (F1 & F2 & F3). unfold gh_nf, gh_new in *. fold nv c in F1, F2, F3, X.
    clear -X Hz F1 F2 F3 HNFP C1 G13 G14 TG PS1 T1 T2. lia.
Qed.

Definition JRpop (i : Z) : jpredA := ltac2:(tb__ "0|3|
S7S27S35Q40M0A1M1A1S27S6bA1S6aS3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVi;A1R4R3R2R1AaS3S2G1S9R4S3dA2S36G0S1eS1eS53VA;Vrb;A2Z10A2S21Z4M2Vi;A2A2A2A3S2G1S9R4S3eA2S36G0S1eS52VA;Vrb;A2S21G2S1eS22VnfP;Vk;A2Vi;A2A2A2A2A3A2A2Lmd;Ltr;Ltp;Lr;").
Lemma JRpop_K : ltac2:(tb__ "0|0|
S0S8cVKc;S49R1A1A2Fi;").
Proof. intros i r t tr md [H _]. exact (JR_K A Kc rb tp0 md0 _ r t tr md H). Qed.
Lemma JRpop_stable : ltac2:(tb__ "0|0|
S0S1S2S29S80S43R1A2S2aA3S48S34R2S49R3A1A3F_;Fn;Fi;").
Proof.
  intros i n Hn r r' tp tr md md' Hag Hme (HJ & H4 & H6). apply Pos.leb_le in Hn. unfold PNX in Hn.
  split; [|split].
  - eapply (JR_stable A Kc rb tp0 md0 (phK i) n HKc); [unfold GR; lia | exact Hag | exact Hme | exact HJ].
  - destruct Hag as (Hw & _). rewrite <- (Hw PV4) by (unfold PV4; lia). exact H4.
  - destruct Hag as (Hw & _). rewrite <- (Hw PV6) by (unfold PV6; lia). exact H6.
Qed.

Definition O_srcc : sobj := ltac2:(tb__ "0|0|
S42S3eS26SeS14SaZ0A1Z4SbS3fA1A3S28SeA1A3A2").
Definition O_dstc : sobj := ltac2:(tb__ "0|0|
S42S3dS26SeS14SaZ0A1Z4S18S2aQ20SbS3fA1A3A3S28SeA1A3A2").

Lemma pop_release : ltac2:(tb__ "0|6|
S1cS27S6A1M0S7S27S35Q40M1A1M2A1S27S6bA1M3S6fS6aS6aS0S3S1fZ0M4R1A2S20R1Vk;A2A2S2G0SfRaA1S30S6R9S26S6S4cS26S6S4bS28S6A1A3A3M5A3A3S1bS34R9RbS2bG3S83R7S84R6R5A2A4A4S2G2S9RaS3fA2S36G1S64S0S23S1eS22VnfP;Vk;A2R4A2A1VfaP;G4A4A2A3S49R5RbRaR9R6A5S6dRcG5R9A3S7S3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aS1eR7Z1A2A1R1RcRbR8AaS3S2G2S9R1S3dA2S9RdS3dA2A3S2G2S9R1S3eA2S9RdS3eA2A3A2A2Tr3;F_;F_;F_;F_;F_;Fi;FmdJ;Fmd;Fms;Ftr;Ftp;Fr2;FK;FS;").
Proof.
  intros S K r2 tp tr ms md mdJ i Hi HO Hsm H7 ((HFz & HGh & HKc' & HM & HR & HRM) & H4 & H6) r3.
  split; [|split; reflexivity].
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _ & _) & _ & (_ & N6) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0) in *.
  assert (Hid : 0 <= idv < 2 ^ 28).
  { apply HIDS. unfold idv. apply nth_In. unfold nfP in *. lia. }
  set (Si := FAb A rb + 4 * (nfP - k + i)) in *. set (Di := PCE A rb + 16 + 4 * i) in *.
  idtac "pr:1".
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  assert (RS : obj_range r2 O_srcc = (Si, Si + 4)).
  { unfold O_srcc, O_cell. rewrite obj_range_mk by lia. cbn [eval]. rewrite H6, u64_lit by (unfold Si in *; lia). f_equal; lia. }
  assert (RD : obj_range r2 O_dstc = (Di, Di + 4)).
  { unfold O_dstc, O_cell. rewrite obj_range_mk by lia. cbn [eval]. rewrite H4, u64_lit by (unfold Di in *; lia). f_equal; lia. }
  set (m2 := view segs (rm r2)) in *. set (m3 := view segs (rm r3)).

  assert (M3S : forall j, (j < 4)%nat -> m3 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. destruct (absorb_obj r2 S tr ms md K [O_srcc; O_dstc] O_srcc Hsm HO (or_introl eq_refl)) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 (SVar PV7)) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_srcc O_cell eval c_off SymState.c_val c_width] in ASb. rewrite H6, soff_lit_small, u64_lit in ASb by (unfold Si in *; lia).
    rewrite H7 in ASb. unfold m3. rewrite view_in by (unfold Si in *; lia). fold Si in ASb. replace (Si + 0 + Z.of_nat j) with (Si + Z.of_nat j) in ASb by lia. exact ASb. }
  assert (M3D : forall j, (j < 4)%nat -> m3 (Di + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. destruct (absorb_obj r2 S tr ms md K [O_srcc; O_dstc] O_dstc Hsm HO (or_intror (or_introl eq_refl))) as (_ & AS & _).
    destruct (AS (mkCell (SLit 0) 4 (SExt true 32 (SVar PV7))) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb j Hj).
    cbn [ob_base O_dstc O_cell eval c_off SymState.c_val c_width] in ASb. rewrite H4, soff_lit_small, u64_lit in ASb by (unfold Di in *; lia).
    rewrite H7, sext32_small in ASb by lia. unfold m3. rewrite view_in by (unfold Di in *; lia). fold Di in ASb. replace (Di + 0 + Z.of_nat j) with (Di + Z.of_nat j) in ASb by lia. exact ASb. }
  assert (M2S : forall j, (j < 4)%nat -> m2 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. pose proof (HSRC i m2 ltac:(lia) HR (nfP - k + i) ltac:(lia)) as Hc. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    unfold Si. exact Hc. }
  assert (AGR : forall z, ~ (Di <= z < Di + 4) -> m3 z = m2 z).
  { intros z Hz. destruct (Z_le_dec Si z) as [H1|H1]; [destruct (Z_lt_dec z (Si + 4)) as [H2|H2]|].
    - replace z with (Si + Z.of_nat (Z.to_nat (z - Si))) by lia. rewrite M3S, M2S by lia. reflexivity.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd]; lia.
    - unfold m3, r3. apply view_absorb_out. intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd]; lia. }
  idtac "pr:2".
  unfold JR. split; [exact HFz|]. split; [exact HGh|]. split; [exact HKc'|]. split; [exact HM|].
  split; [|apply (rmlink_absorb _ r2 [O_srcc; O_dstc] ms HRM); intros o [<-|[<-|[]]]; [rewrite RS | rewrite RD]; cbn [fst snd];
           unfold IMG_LO, IMG_HI, Si, Di; rewrite ?FAr, ?PCr; unfold nfP in *; lia].
  fold m3. unfold rlink in HR |- *. fold m2 in HR.
  destruct HR as (L1 & L2 & L3 & L4 & L5 & L6).
  assert (ZI : forall z, zoneR A rb (phK (i + 1)) z <-> (zoneR A rb (phK i) z \/ Di <= z < Di + 4)).
  { intros z. unfold zoneR, phK. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri]. fold nv c. unfold Di. split.
    - intros [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
      + left; left; exact H.
      + left; right; left; exact H.
      + left; right; right; left; exact H.
      + left; right; right; right; left; exact H.
      + left; right; right; right; right; left; exact H.
      + destruct (Z_lt_dec z (PCE A rb + 16 + 4 * i)); [left; right; right; right; right; right; left; lia | right; lia].
      + left; right; right; right; right; right; right; left; exact H.
      + left; right; right; right; right; right; right; right; exact H.
    - intros [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|H].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; exact H.
      + right; right; right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; lia.
      + right; right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; right; exact H.
      + right; right; right; right; right; left; lia. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros z Hz. rewrite AGR by (intros X; apply Hz; apply ZI; right; exact X). apply L1. intros X. apply Hz. apply ZI. left. exact X.
  - intros z Hz. apply ZI in Hz. destruct (Z_le_dec Di z) as [H1|H1]; [destruct (Z_lt_dec z (Di + 4)) as [H2|H2]|].
    + replace z with (Di + Z.of_nat (Z.to_nat (z - Di))) by lia. rewrite M3D by lia. discriminate.
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
    + rewrite AGR by lia. apply L2. destruct Hz as [Hz|Hz]; [exact Hz | exfalso; lia].
  - intros j Hj. cbn [ph_fill phK] in Hj |- *. eapply cell_ok_agree_range; [|exact (L3 j Hj)]. cbn [c_addr c_w]. intros z Hz. apply AGR.
    destruct (HFILLR ltac:(lia)) as (F1 & F2 & F3). unfold Di. rewrite PCr. rewrite FAr in Hz. change (Z.of_nat 4) with 4 in Hz.
    clear -Hz C1 PS1 T1 T2 G13 G14 TG Hj Hi K1 HNFP F1 F2 F3. lia.
  - intros i' Hi'. cbn [ph_pop phK] in Hi'. destruct (Z.eq_dec i' i) as [->|Hne].
    + intros j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *. fold Di. rewrite M3D by exact Hj. do 3 f_equal. fold nv c. rewrite HCACHE, nth_skipn_Z.
      unfold idv. replace (Z.to_nat (nfP - k) + Z.to_nat i)%nat with (Z.to_nat (nfP - k + i)) by (clear -HKF Hi; lia). reflexivity.
    + eapply cell_ok_agree_range; [|exact (L4 i' ltac:(cbn [ph_pop phK]; lia))]. cbn [c_addr c_w]. intros z Hz. apply AGR. unfold Di. lia.
  - intros X. discriminate X.
  - intros X. discriminate X.
Qed.

Variable F : nat.
Variable CT0 : axst.
Variables LB LX : leafA.
Variable nob : nat.
Variable s_bk : wsub.
Let CT1 : axst := cT1 CT0.
Definition e_end : sv := ltac2:(tb__ "0|0|
ScS4eScS4eS79SaZ10A1A3ScS50S46SaZ2A1A3A3").
Definition NPOP : list carve_spec := ltac2:(tb__ "0|9|
S26S2cS2cS2cS8S0A2M0S0A2M1S27S2cS2cS0S2eA2M2S8A2M3A1M4A2M5S2bG1G4S2bG0S0S2bS8S0SbS3eA1Z0M6A4Z4M7A4S26G3S2bG2S8S2bS0S2eG6U4A4SbS3fA1A4S28G3A1M8A3A4S26G5S2bG1G4S2bG0S0S2bS8S0SbS3dA1G6A4G7A4G8A4S28G5A1A3A3").
Hypothesis SK_t : ltac2:(tb__ "0|1|
S2S27S2cS2cS8S8A2S8A2M0A1S66S6G0S7fSfS38VCT0;A1A1A4S66S6G0S7fS30S6S8fVW;A1S26S6S7aS26S6S7bS26S6S44S26S6S45S28S6A1A3A3A3A3A3A4A3").
Hypothesis XX_t : ax_X CT0 = [].
Hypothesis XF_t : ltac2:(tb__ "0|0|
S69S10S8eVW;Vst;A2S11S38VCT0;A1A1A3").
Hypothesis NX_t : ltac2:(tb__ "0|0|
S2S29S81S17S38VCT0;A1A1S43A2S2aA3").
Hypothesis W_t1 : ltac2:(tb__ "0|0|
S2S29S1dS38VCT1;A1A1S2aA3").
Hypothesis R_t1 : ltac2:(tb__ "0|1|
S2S2fS27S3aA1M0A1S3cS34VF;S26S0Z413dcS26S0Z413f0S28S0A1A3A3VCT1;S2aA5S31G0S26S3aVLB;S26S3aVLX;S28S3aA1A3A3A2A3").
Hypothesis LN_t1 : ltac2:(tb__ "0|0|
S2S29S16S38VCT1;A1A1S2dA3").
Hypothesis OB_b : ltac2:(tb__ "0|1|
S2S27S6A1SfS38S39VLB;A1A1A1M0S30S6S65S6Vnob;G0A3S26S6S4cS26S6S4bS28S6A1A3A3A3A3").
Hypothesis OB_x : ltac2:(tb__ "0|1|
S2S27S6A1SfS38S39VLX;A1A1A1M0S30S6S65S6Vnob;G0A3S26S6S4cS26S6S4bS28S6A1A3A3A3A3").
Hypothesis ENT_bk : ltac2:(tb__ "0|0|
S2S29S3bS40S39VLB;A1Vnob;A2VCT0;Vs_bk;A3S2aA3").
Hypothesis SID_bk : ltac2:(tb__ "0|0|
S2S29S6eVs_bk;S41A2S2aA3").
Hypothesis S_bk4 : ltac2:(tb__ "0|0|
S2S8S6cVs_bk;S3dA2ScS4eSbS3dA1SaZ4A1A3A3").
Hypothesis S_bk6 : ltac2:(tb__ "0|0|
S2S8S6cVs_bk;S3eA2ScS4eSbS3eA1SaZ4A1A3A3").
Hypothesis FB_b : ltac2:(tb__ "0|0|
S68S10S12S4fScS4eSbS3dA1SaZ4A1A3S4dA3S11S38S39VLB;A1A1A1A3").
Hypothesis FB_x : ltac2:(tb__ "0|0|
S68S10S19S12S4fScS4eSbS3dA1SaZ4A1A3S4dA3A1S11S38S39VLX;A1A1A1A3").

Lemma pop_carve : ltac2:(tb__ "0|5|
S0S7S27S35Q40M0A1M1A1S71S3S1fZ0M2R4A2S20R4Vk;A2A2S47S34S49R5A1VCT0;R4R3R2A6S87R5S26S2cS1G1A2M3S2bS1G1S3fS36G0S64S0S23S1eS22VnfP;Vk;A2M4R6A2A1VfaP;G2A4A2A4S28G3A1A3A2S7S3S47S34S49R7A1VCT1;R1R5R4A6S2G1S9R1S3fA2S36G0S64S0S23S1eG4R7A2A1VfaP;G2A4A2A3A2Tr1;F_;F_;Fw;Ftp;Fr;Fi;").
Proof.
  intros i r tp w Hi H r1.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _ & _) & (_ & MU0 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0) in *.
  assert (E7 : rw r1 PV7 = Z_to_bv 64 idv).
  { unfold r1. apply (rw_rho_sets_in r _ PV7); [repeat constructor; intros [] | left; reflexivity]. }
  split; [|exact E7].
  assert (AG1 : agree_below PNX r r1). { unfold r1. apply agree_below_rho_sets. intros j v [X|[]]. injection X as <- _. unfold PNX, PV7. lia. }
  assert (Erm1 : rm r1 = rm r) by (unfold r1; apply rm_rho_sets).
  assert (H1 : SPA segs (JRpop i) CT0 r1 tp w).
  { destruct H as [Hsm HJ]. split.
    - eapply smatchA_agree; [|exact Hsm]. apply Pos.eqb_eq in NX_t. rewrite NX_t. exact AG1.
    - eapply (JRpop_stable i PNX ltac:(reflexivity)); [exact AG1 | apply mat_equiv_refl | exact HJ]. }
  idtac "pc:1".
  destruct H1 as [HsmA1 HJ1]. pose proof HJ1 as ((HFz & HGh & _ & _ & HR & _) & H4 & H6). pose proof (proj1 HJ1) as HJ1'.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0.
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r1 CF0 RG HGh) as (EB & RNc & RNs & RNm & RNr). cbn zeta in RNs, RNr. fold nv c in RNr.
  pose proof (proj1 HsmA1) as Hsm1. unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S CT0) [O_pcc0; O_st; O_pcm; O_ri] r1 _ HW HE HFz Hsm1 SK_t XF_t) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|om [|ori [|? ?]]]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence). assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (SKm : skel om = skel O_pcm) by (clear -SKx; congruence). assert (SKr : skel ori = skel O_ri) by (clear -SKx; congruence).
  rewrite <- (obj_range_skel r1 oc O_pcc0 SKc) in RNc. rewrite <- (obj_range_skel r1 os O_st SKs) in RNs.
  rewrite <- (obj_range_skel r1 om O_pcm SKm) in RNm. rewrite <- (obj_range_skel r1 ori O_ri SKr) in RNr.
  set (Si := FAb A rb + 4 * (nfP - k + i)) in *. set (Di := PCE A rb + 16 + 4 * i) in *.
  set (m1 := view segs (rm r1)) in *. unfold rlink in HR. fold m1 in HR.
  assert (ES : bv_unsigned (eval r1 (SVar PV6)) = Si) by (cbn [eval]; rewrite H6; apply u64_lit; unfold Si; lia).
  assert (ED : bv_unsigned (eval r1 (SVar PV4)) = Di) by (cbn [eval]; rewrite H4; apply u64_lit; unfold Di; lia).

  assert (MS : forall j, (j < 4)%nat -> m1 (Si + Z.of_nat j) = Some (nth j (enc_bytes 4 (Z_to_bv 64 idv)) (Z_to_bv 8 0))).
  { intros j Hj. pose proof (HSRC i m1 ltac:(lia) (proj1 (proj2 (proj2 (proj2 (proj2 HJ1'))))) (nfP - k + i) ltac:(lia)) as Hc. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc. exact Hc. }
  assert (PD : forall z, Di <= z < Di + 4 -> exists b, m1 z = Some b).
  { intros z Hz. destruct HR as (L1 & L2 & _).
    assert (ZD : zoneR A rb (phK i) z \/ ~ zoneR A rb (phK i) z).
    { destruct (Z_lt_dec z (PCE A rb + 16 + 4 * i)) as [Y|Y]; [left; unfold zoneR, phK; cbn [ph_pop]; do 5 right; left; unfold Di in Hz; lia|].
      right. intros X. apply (zone_thread i z) in X; [lia|]. unfold Di in Hz. rewrite PCr in Hz. lia. }
    destruct ZD as [ZD|ZD].
    - specialize (L2 z ZD). destruct (m1 z) as [b|] eqn:Em; [exists b; reflexivity | exfalso; apply L2; first [exact Em | reflexivity]].
    - rewrite (L1 z ZD). destruct HE as (_ & HA & _ & _ & _ & Hnv & _ & Hcnt & _).
      destruct (pc_entry_facts0 segs A rb tp0 md0 nv HA Hnv Hcnt) as (_ & PE & _). cbn zeta in PE. fold c in PE. apply PE. unfold Di in Hz. rewrite PCr in Hz. lia. }
  idtac "pc:2".
  assert (SiR : ag_spacebeg (aa_geom A) <= Si /\ Si + 4 <= ag_spacebeg (aa_geom A) + 137438953472) by (unfold Si; rewrite FAr; lia).
  assert (DiR : ag_thread (aa_geom A) + 288 <= Di /\ Di + 4 <= ag_thread (aa_geom A) + 2656) by (unfold Di; rewrite PCr; lia).
  assert (HS1 : SPA segs (JRpop i) CT0 r1 tp w) by (split; [exact HsmA1 | exact HJ1]).
  apply (SPA_carve_list segs _ r1 CT0 tp w NPOP PNX1 HS1 W_t1).
  - apply Pos.eqb_eq in NX_t. rewrite NX_t. unfold PNX, PNX1. lia.
  - unfold NPOP. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + rewrite ES. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [repeat apply Forall_cons; try apply Forall_nil; lia|].
      split.
      { intros off Hoff. rewrite Erm1. specialize (MS (Z.to_nat off) ltac:(lia)). replace (Si + Z.of_nat (Z.to_nat off)) with (Si + off) in MS by lia.
        unfold m1 in MS. rewrite Erm1 in MS. rewrite view_in in MS by lia. eapply wok_rd_off_image; [|exact MS]. lia. }
      split; [|unfold xwords_clear; rewrite XX_t; intros rr y j []].
      apply Forall_cons; [|apply Forall_nil]. intros j Hj. cbn [eval]. rewrite E7. specialize (MS j Hj). unfold m1 in MS. rewrite view_in in MS by lia.
      replace (Si + 0 + Z.of_nat j) with (Si + Z.of_nat j) by lia. exact MS.
    + rewrite ED. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [apply Forall_nil|].
      split.
      { intros off Hoff. destruct (PD (Di + off) ltac:(lia)) as [b Hb]. unfold m1 in Hb. rewrite view_in in Hb by lia.
        eapply wok_rd_off_image2; [| |exact Hb]; lia. }
      split; [apply Forall_nil | unfold xwords_clear; rewrite XX_t; intros rr y j []].
  - cbn [map carve_obj NPOP]. unfold carved.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; rewrite obj_range_mk by lia; rewrite ?ES, ?ED; rewrite EO; apply Forall_app; split.
    + apply BZ. right; left. rewrite kSpaceSize_val. lia.
    + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; lia.
    + apply BZ. left. lia.
    + repeat apply Forall_cons; try apply Forall_nil; rewrite ?RNc, ?RNs, ?RNm, ?RNr; unfold ranges_disjoint; cbn [fst snd]; rewrite ?PCr; unfold region_info, kRegionInfoStride; rewrite ?kSpaceSize_val; unfold Di in *; rewrite ?PCr in *; lia.
  - cbn [map carve_obj NPOP pairwise_disjoint]. unfold carved. split; [|split; [constructor | exact I]].
    apply Forall_cons; [|apply Forall_nil]. rewrite !obj_range_mk by lia. rewrite ES, ED. unfold ranges_disjoint; cbn [fst snd]. lia.
Qed.

Lemma e_end_val : ltac2:(tb__ "0|0|
S7S55Vrb;R1A2S56VA;Vrb;R2A3S2S0S37Q40S13R3S4dA2A2S1eS1eS53VA;Vrb;A2Z10A2S21Z4Vk;A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  destruct (arm_extra_ranges A rb r CF0 RG HGh) as (EB & _).
  unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
  destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB). fold k in K1.
  destruct HGh as (_ & _ & _ & _ & _ & _ & _ & Q227 & _). fold nv c k in Q227.
  assert (PCr : PCE A rb = ag_thread (aa_geom A) + 208 + 80 * c) by (unfold PCE; fold nv c; lia).
  unfold e_end, vK. cbn [eval]. rewrite add_val, add_val, sll_val. rewrite EB, Q227, !u64_lit by lia. change (2 mod 64) with 2.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (k * 2 ^ 2)) by lia. rewrite (Z.mod_small (PCE A rb + 16)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition JRrel (i : Z) : jpredA := ltac2:(tb__ "0|3|
S7S27S35Q40M0A1M1A1S27S6bA1S6aS3S51VA;VKc;Vrb;Vtp0;Vmd0;S4aS1eVi;Z1A2A1R4R3R2R1AaS3S2G1S9R4S3dA2S36G0S1eS1eS53VA;Vrb;A2Z10A2S21Z4M2Vi;A2A2A2A3S2G1S9R4S3eA2S36G0S1eS52VA;Vrb;A2S21G2S1eS22VnfP;Vk;A2Vi;A2A2A2A2A3A2A2Lmd;Ltr;Ltp;Lr;").

Lemma pop_iter : ltac2:(tb__ "0|1|
S0S7S27S35Q40A1A1S70S3S1fZ0R4A2S20R4Vk;A2A2S20S1eR5Z1M0A2Vk;A2S7VTR;S47S34S49S1eR7G0A2A1VCT0;R1R5A5R4A2Fr';F_;S2S0S1eR6G0A2Vk;A3S7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R6A5R5A2Fr';F_;VTR;S47S34S49R7A1VCT0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;").
Proof.
  intros i r tp Q Hi HKb HKx.
  assert (NUM : 0 <= PCE A rb /\ PCE A rb + 16 + 4 * k + 8 < 2 ^ 62 /\ 1 <= k <= 8).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
    destruct CF0 as ((_ & C1 & _) & (K1 & _ & _) & _ & _ & _ & _ & (T1 & T2 & _) & _). fold k in K1. pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia. }
  set (idv := nth (Z.to_nat (nfP - k + i)) faP 0).
  set (r1 := rho_sets r [(PV7, Z_to_bv 64 idv)]).
  assert (E7 : rw r1 PV7 = Z_to_bv 64 idv).
  { unfold r1. apply (rw_rho_sets_in r _ PV7); [repeat constructor; intros [] | left; reflexivity]. }
  apply (tr_pre Kc TR KIT (SPA segs (JRpop i) CT1 r1 tp)); [intros w Hw; exact (proj1 (pop_carve i r tp w Hi Hw))|].
  apply (tr_run Kc TR KIT F [0x413dc; 0x413f0] CT1 [LB; LX] (JRpop i) r1 tp Q (JRpop_K i) (JRpop_stable i (ss_next (ax_S CT1)) eq_refl) R_t1 LN_t1).
  intros L r2 HL Hag.
  assert (NX1 : ss_next (ax_S CT1) = PNX1) by reflexivity. rewrite NX1 in Hag.
  assert (E72 : rw r2 PV7 = Z_to_bv 64 idv) by (destruct Hag as (Hw & _); rewrite <- (Hw PV7) by (unfold PV7, PNX1; lia); exact E7).

  assert (REL : forall (LL : leafA), ss_objs (ax_S (la_state LL)) = firstn nob (ss_objs (ax_S (la_state LL))) ++ [O_srcc; O_dstc] ->
            forall w, SPA segs (JRpop i) (la_state LL) r2 tp w -> exists r3, SPA segs (JRrel i) (keepn (la_state LL) nob) r3 tp w).
  { intros LL HO [tr [ms md]] Hw. exists (rho_absorb r2 [O_srcc; O_dstc] (vms md tp ms)).
    apply (SPA_unobj_J (JRpop i) (JRrel i) r2 (la_state LL) _ [O_srcc; O_dstc] tp tr ms md HO Hw).
    intros Hsm HJ. pose proof HJ as (_ & H4 & H6).
    destruct (pop_release (ax_S (la_state LL)) _ r2 tp tr (vms md tp ms) (vmd md) md i Hi HO Hsm E72 HJ) as (P1 & P2 & P3). cbn zeta in P1, P2, P3.
    split; [exact P1|]. split; [rewrite P2; exact H4 | rewrite P3; exact H6]. }
  destruct HL as [<-|[<-|[]]].
  -
    apply (tr_facts Kc TR KIT). intros HF.
    pose proof (proj1 (Forall_forall _ _) HF _ FB_b) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 < k)).
    { intros w [_ ((HFz & HGh & _) & H4 & _)]. unfold branch_taken, bv_eqb in BF. apply negb_true_iff in BF. apply Z.eqb_neq in BF.
      rewrite (e_end_val r2 HFz HGh) in BF. cbn [eval] in BF. rewrite add_val, H4, !u64_lit in BF by lia.
      rewrite Z.mod_small in BF by lia. lia. }
    intros Hlt.
    apply (tr_cut Kc TR KIT valuation _ (fun r3 => SPA segs (JRrel i) (keepn (la_state LB) nob) r3 tp) Q (REL LB OB_b)).
    intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRpop (i + 1)) CT0 (rho_sub r3 s_bk) tp)); [|exact (HKb Hlt _)].
    intros w Hw. apply (SPA_entails_J (JRrel i) (JRpop (i + 1)) _ CT0 s_bk r3 tp w ENT_bk); [|exact Hw].
    intros (HJ & H4 & H6). pose proof (rho_sub_agree s_bk GR r3 SID_bk) as AGs.
    split; [|split].
    + eapply (JR_stable A Kc rb tp0 md0 (phK (i + 1)) GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
    + cbn [rho_sub rw]. rewrite S_bk4. cbn [eval]. rewrite H4. apply bv_eq. rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. lia.
    + cbn [rho_sub rw]. rewrite S_bk6. cbn [eval]. rewrite H6. apply bv_eq.
      assert (FAR : 0 <= FAb A rb /\ FAb A rb + 536870912 + 8 < 2 ^ 62).
      { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
        destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & _).
        unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. lia. }
      rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. lia.
  -
    apply (tr_facts Kc TR KIT). intros HF.
    pose proof (proj1 (Forall_forall _ _) HF _ FB_x) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (i + 1 = k)).
    { intros w [_ ((HFz & HGh & _) & H4 & _)]. unfold branch_taken, bv_eqb in BF. apply not_true_is_false in BF. apply negb_false_iff in BF. apply Z.eqb_eq in BF.
      rewrite (e_end_val r2 HFz HGh) in BF. cbn [eval] in BF. rewrite add_val, H4, !u64_lit in BF by lia.
      rewrite Z.mod_small in BF by lia. lia. }
    intros Heq.
    apply (tr_cut Kc TR KIT valuation _ (fun r3 => SPA segs (JRrel i) (keepn (la_state LX) nob) r3 tp) Q (REL LX OB_x)).
    intros r3.
    apply (tr_pre Kc TR KIT (SPA segs (JRp (phK k)) (keepn (la_state LX) nob) r3 tp)); [|exact (HKx Heq _)].
    intros w Hw. apply (SPA_J (JRrel i) (JRp (phK k)) _ r3 tp w); [|exact Hw]. intros (HJ & _). rewrite <- Heq. exact HJ.
Qed.

Lemma pop_loop : ltac2:(tb__ "0|0|
S2eS0S7S27S35Q40A1A1S70S2S0S22Vk;R4A2S24R5A1A3S3S1fZ0R5A2S20R5Vk;A2A2S7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R5A5R4A2Fr';VTR;S47S34S49R7A1VCT0;R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Fi;Fn;").
Proof.
  induction n as [|n IH]; intros i r tp Q Hn Hi HX; [lia|].
  apply (pop_iter i r tp Q Hi).
  - intros Hlt r'. apply (IH (i + 1) r' tp Q); [lia | lia | exact HX].
  - intros _ r'. apply HX.
Qed.

Variable J0 : axst.
Variable LT0 : leafA.
Variable s_in : wsub.
Variable e_src : sv.
Hypothesis R_t0 : ltac2:(tb__ "0|1|
S2S2fS27S3aA1M0A1S3cS34VF;S26S0Z413dcS26S0Z413f0S28S0A1A3A3VJ0;S2aA5S31G0S26S3aVLT0;S28S3aA1A3A2A3").
Hypothesis LN_t0 : ltac2:(tb__ "0|0|
S2S29S16S38VJ0;A1A1S2dA3").
Hypothesis NX_t0 : ltac2:(tb__ "0|0|
S2S29S80S41S17S38VJ0;A1A1A2S2aA3").
Hypothesis ENT_in : ltac2:(tb__ "0|0|
S2S29S3bS39VLT0;A1VCT0;Vs_in;A3S2aA3").
Hypothesis SID_in : ltac2:(tb__ "0|0|
S2S29S6eVs_in;S41A2S2aA3").
Hypothesis S_in4 : ltac2:(tb__ "0|0|
S2S8S6cVs_in;S3dA2ScS4eS79SaZ10A1A3A3").
Hypothesis S_in6 : ltac2:(tb__ "0|0|
S2S8S6cVs_in;S3eA2Ve_src;A3").
Hypothesis HSRCP : ltac2:(tb__ "0|1|
S7S55Vrb;R1A2S56VA;Vrb;R2A3S2S35Q40M0A1S13R3Ve_src;A2S36G0S1eS52VA;Vrb;A2S21Z4S22VnfP;Vk;A2A2A2A2A3F_;F_;Fr;").

Lemma phK0 : phK 0 = ph.
Proof.
  destruct PH0 as (P1 & P2 & P3).
  transitivity (mkPh (ph_u ph) (ph_f ph) (ph_fill ph) (ph_pop ph) (ph_cnt ph) (ph_ri ph)); [unfold phK; rewrite P1, P2, P3; reflexivity | symmetry; apply ph_eta].
Qed.

Lemma pop_all : ltac2:(tb__ "0|0|
S7S27S35Q40A1A1S70S7VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;S4aVk;A1A6S40S39VLX;A1Vnob;A2R1R3A5R2A2Fr';VTR;S47S34S51VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VJ0;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HX.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x413dc; 0x413f0] J0 [LT0] ph r tp Q R_t0 LN_t0 NX_t0).
  intros L r1 [<-|[]] _.
  assert (K1 : 1 <= k).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0. destruct CF0 as (_ & (K1 & _) & _). fold k in K1. lia. }
  apply (tr_pre Kc TR KIT (SPA segs (JRpop 0) CT0 (rho_sub r1 s_in) tp)); [|apply (pop_loop (Z.to_nat k) 0 _ tp Q); [lia | lia | exact HX]].
  intros w Hw. apply (SPA_entails_J (JRp ph) (JRpop 0) _ CT0 s_in r1 tp w ENT_in); [|exact Hw].
  intros HJ. pose proof (rho_sub_agree s_in GR r1 SID_in) as AGs. pose proof HJ as (HFz & HGh & _).
  split; [|split].
  - rewrite phK0. eapply (JR_stable A Kc rb tp0 md0 ph GR HKc ltac:(lia)); [exact AGs | apply mat_equiv_refl | exact HJ].
  - cbn [rho_sub rw]. rewrite S_in4. cbn [eval].
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF0. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
    destruct (arm_extra_ranges A rb r1 CF0 RG HGh) as (EB & _).
    apply bv_eq. rewrite add_val, EB, !u64_lit.
    + rewrite Z.mod_small; [lia|]. unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
      destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & _ & (T1 & T2 & _) & _). pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia.
    + unfold cfacts in CF0. cbn zeta in CF0. fold nv c in CF0.
      destruct CF0 as ((_ & C1 & _) & _ & _ & _ & _ & _ & (T1 & T2 & _) & _). pose proof (topG_range (aa_geom A)) as TG. unfold PCE. fold nv c. lia.
    + lia.
  - cbn [rho_sub rw]. rewrite S_in6. rewrite (HSRCP r1 HFz HGh). f_equal. lia.
Qed.
End POP.
End SpineMallocR3.

