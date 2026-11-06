(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am b8.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue.

(* [comment removed for export] *)
Module SpineMallocR2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "mul"; "div"; "of_nat"; "@Corelib.Init.Datatypes"; "list"; "cons"; "pair"; "bool"; "true"; "nil"; "prod"; "app"; "Some"; "option"; "false"; "andb"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "rw"; "sobj"; "sprop"; "ss_next"; "obj_range"; "ss_lenient"; "holds"; "ss_facts"; "ss_objs"; "sstate"; "swf"; "agree_below"; "eval"; "ranges_disjoint"; "rm"; "smatch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "axst"; "ax_setS"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ag_thread"; "ag_spacebeg"; "ageom"; "aa_cache_inited"; "ag_ctx"; "class_state"; "cs_allocated_user"; "cs_cache"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "ustop"; "A_globals"; "UStopLeOrPc"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "entryR"; "PCE"; "phase"; "frozen"; "ghosts"; "ph_fill"; "gh_new"; "gh_nf"; "ph0"; "ph_cnt"; "ph_pop"; "zoneR"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "cR0"; "k_e"; "GR"; "fa_e"; "ri_e"; "vFA"; "vK"; "vRI"; "O_pcm"; "O_ri"; "cR1"; "factsR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "needed8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2"; "cfacts"; "rigids"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "max_count"; "kSpaceSize"; "region_info"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "bview"; "present"; "view"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "F_gen"; "O_pcc0"; "O_st"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "FACAP"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1"; "armint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "tab1_ok"; "@Stdlib.Lists.List"; "In";
"incl"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition rigids (A : AA) (rb r : valuation) : Prop := ltac2:(tb__ "0|5|
S34Q40M0S1cVrb;PcM1A2M2A2S4S69R1A1S4S37VA;A1S3aS0S1S32G0A1M3S1cVr;G1A2G2A3S0S1G3S1cVr;P94A2S33G0S72R2A1A2A3S0S1G3S1cVr;P97A2S33G0S38R1A1A2A3S0S1G3S1cVr;P98A2S33G0S3cR1A1A2A3S0S1G3S1cVr;P9bA2S33G0S39R1A1M4A2A3S0S1G3S1cVr;P9cA2S33G0S6G4S74A2A2A3S0S1G3S1cVr;P9dA2S33G0S6bR3A1A2A3S1G3S1cVr;P9eA2S33G0R2A2A3A2A2A2A2A2A2A2TG;Tc;Tnv;").
Lemma entry_rigids : ltac2:(tb__ "0|0|
S36S1aScS32Q40A1A1S59ScS44A1S45S1aS1aS4dR8R7R6R5R4R3R2A7S50R8R2A2S6dRaR9R3A3F_;F_;Fr;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho r (Hag & _) [Fw _]. destruct Hag as (Hagw & _ & _).
  assert (E12 : rw rb 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  unfold rigids. cbn zeta. rewrite E12.
  repeat split; rewrite <- (Fw _) by lia; try reflexivity; rewrite <- (Hagw _) by (unfold GW; lia); reflexivity.
Qed.

Definition cfacts (A : AA) (rb : valuation) : Prop := ltac2:(tb__ "0|d|
S34Q40S1cVrb;PcA2A2S4S69R1A1S4S6aVA;R2A2S3dS37VA;A1S3aS39R1A1S4S38R2A1S4S0S0S0S5Z1M0R6A2S5R6Zfc00A2A2S0S0S5G0R5A2S5R5Z1eA2A2S0S0S5Z20S72R5A1M1A2S5G1Z10000M2A2A2S1S4S8G1Z10A2Z0M3A3A2A2A2S0S0S0S5G0S8aR5A1M4A2S5G4Z8A2A2S0S1S4S9Z2G4A2S73R5A1A3S5S9G4G1A2G2A2A2A2S0S0S1S4S8S42R4A1M5Z40000M6A2G3A3S0S0S5G3S3eR4A1M7A2S5G7G5A2A2S0S5G5Ze0000000A2S0S1S4S8G7G1A2G3A3S7G5S6G7G1A2A2A2A2A2A2S0S0S1S4S8S41R4A1M8G6A2G3A3S0S5S9Z4SbS18S4S40R4A1A2A1A2G8A2S5G8Z20000000A2A2A2S0S0S5G5S89R5A1A2S0S5G8S88R5A1A2S1ScS4A1S3fR4A1S11S4A1A3A2A2S0S0S1S4S8R2G2A2G3A3S0S5Z100080000000R2A2S0S5S6S6R2Z2000000000A2Z1000M9A2MaS43R3A1MbA2S5GbZ7fffff800000A2A2A2A2S0S0S5G9R1A2S0S5S6R1G9A2McGbA2S0S2S5GcG2A2S5Z646000R1A2A2S2S5GcR2A2S5GaR1A2A2A2A2A2S2S5GcZ7fff7000A2S5Z10007fff8000R1A2A2A2A2A2A2A2A2A2TT;TSB;TG;Tcs;Tc;Tnv;").
Lemma entry_cfacts : ltac2:(tb__ "0|0|
S36S1aScS32Q40A1A1S59ScS44A1S45S1aS4dR7R6R5R4R3R2R1A7S6cR8R7A2F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
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
S17S8dPdcM0S5eS4SaR1Z2M1A2Lz;G1UfA5S8cG0S5eA2A2").
Lemma tabK_ok : tabK_okb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma r1_diffs : ltac2:(tb__ "0|1|
S36S1aS1aS6cR3R2A2S6dR4R3R2A3S51R5R4R3A3S78R4SdS12S1bS1bA2M0SeS1bS1bS61S64A4SdG0SeS1bS1bS5eS63A4SdG0SeS1bS1bS60S62A4S11G0A1A3A3A3A2F_;F_;F_;Fr;Frb;FA;").
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
S13S1dSdS1dS81S13S1dS4bVW;A1S46A3A3S80A3").
Definition BASEF (W : list ulink) (st : ustop) : list sprop := ltac2:(tb__ "0|0|
S13S1eS13S1eS4aVW;Vst;A2S49S48A1A3S82A3").
Lemma arm_base_disj : ltac2:(tb__ "0|4|
S36S1aScS32Q40A1A1S59ScS44A1M0S45S1aS25ScS1dA1M1S1aS12ScS5aA1S7fA2S1S45R6S47A3S1G0R8S11S44A1A3F_;S4dRcRbRaR9R8R7R6A7S50RcR4A2S2bS87R5R7R4A4S1ScS12S12S1bS1bA2S1bA2M2A1M3S5bS1dG2S70S24R8A1A4S5bS1dG2S70S13S1dS6fRbA1R7A3A4A3S8fS1eS6eRcRbA2S23R9A1A3S3G1G1S3G1G1S0S1G1S24RcA1S13S1dR2R1A3A3S0S1G3S5bS1dG2S70R1A4S5bS1dG2S70RbA4A3S4S4S8bS37R15A1R2R1A3S5cS1dS1dS29S20ReR1A2SeS4S4R4R3A4A2Lo';R5A3F_;Fhi;Flo;A2A2Lox;A2Lob;A2F_;F_;F_;F_;F_;F_;Fw;Fr;Fextra;FS;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
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
    destruct st; [apply chain_pre_in; exact Hp|]. rewrite (HW eq_refl) in Hp. destruct Hp.
  - unfold top_high in Htop. rewrite <- (Fw 10%positive) by lia. rewrite <- (Fw V_DEPTH) by (unfold V_DEPTH; lia). exact Htop.
Qed.

Lemma arm_extra_ranges : ltac2:(tb__ "0|4|
S36S1aS1aS6cR3R2A2S6dR4R3R2A3S51R5R4R3A3S38S37R6A1A1S4S75S39S37R7A1A1S69S34Q40M0S1cR6PcA2A2A1A2S4S0S1S4S34G0S28R6S85A2A2S4eR8R7A2M1A3S0S1S12S4S4A2M2S20R6S83A2SeS4S4G1S6G1Z4A2M3A4A3S0S1G2S20R6S84A2SeS4S4S6R2Zad0A2S6R2Zc60A2A4A3S0S1G2S20R6S65A2SeS4S4G3S6G1Z8A2A4A3S1G2S20R6S66A2SeS4S4R1S6R1Z80A2A4A3A2A2A2A2Tri;TT;F_;F_;F_;Fr;Frb;FA;").
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
S36S1aScS32Q40M0A1A1S59ScS44A1S45S1aS4dR7R6R5R4R3R2R1A7S1SfS3bR8A1S10A3S7eS86S2aR8A1A2S7cS69S34G0S1cR9PcA2A2A1S4S0S7aR2S7bS6S4eRbRaA2M1Z4A2U4S73R1A1A3A2S0S7aR2S7bS6G1Z8A2U8S72R1A1A3A2S7dR2G1S6G1Z50A2A3A2A2Tc;Tm0;F_;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
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
S36S1aS4fS4S6cR4R3A2S7Z0M0S52R3A1A2S0S5G0S54R6R5A2M1A2S0S5S9Z4M2S6G1S53R6R5A2M3A2A2Z20000000A2S5S52R4A1G3A2A2A2F_;S0S5S6S38S37R6A1A1M4Z120A2R3A2S7R3S6G4Zc60A2A2A2S58R7R6R5R4A4S2S0S5S6S4eR8R7A2M5Z10A2M6R5A2S7R5S6G6S9G2S57R6A1A2A2A2A2S0S1SfS56R6A1S10A3S0S5G5R5A2S7R5S6G5G2A2A2A2A2A2F_;F_;F_;F_;Fz;Fph;Frb;FA;").
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
S19ScS4A1S30ScS2dA1M0S4fS1aScS32Q40A1A1S71S1S15G0A1S2fVsegs;R8R7R6S10A5S14G0R5A2A3S1SfS21S2cR7A1A1S16A3S1SfS76S5fS1fS2cR8A1A1A2S10A3S2dS1aS8eS2dR2RaA3S27S1fS2cRcA1A1R9R2A3VTR;S35Vsegs;S4cVA;VKc;Vrb;Vtp0;Vmd0;RbA6S2eR4A1R3R9A5R8A2F_;F_;Frho';FL;VTR;S35Vsegs;S4cVA;VKc;Vrb;Vtp0;Vmd0;R8A6RaR7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;Fph;Fleaves;FE;Fcuts;Ffuel;").
Proof.
  intros fuel cuts E leaves ph rho tp Q Hrun Hl Hn HL.
  apply (tr_run Kc TR KIT fuel cuts E leaves (JRp ph) rho tp Q (JR_K A Kc rb tp0 md0 ph)); [|exact Hrun | exact Hl | exact HL].
  apply JR_stable; [exact HKc | apply Pos.leb_le; exact Hn].
Qed.

Lemma jr_restate : ltac2:(tb__ "0|3|
S30S25ScS12S1bS1bA2A1M0ScS1eA1M1S4fS1aScS32Q40A1A1S71S1SfS26R7A1S10A3S1S15S12G0G1A2M2A1S79S2cR9A1R8A2S14G2SeG0G1R7R6A4A2A3S1SfS77S1fR9A1S1fS2cRaA1A1A2S10A3ScS5aA1S59S4cVA;VKc;Vrb;Vtp0;Vmd0;R9R8R7R2R1AaS5cS1eS22R9A1S23S2cReA1A1A3S0S78RaRdA2S5cS1eS22RaA1RcA3A2F_;F_;Fmd;Ftr;VTR;S35Vsegs;S4cVA;VKc;Vrb;Vtp0;Vmd0;R8A6S31RcRbA2R7R6A5R5A2VTR;S35Vsegs;S4cVA;VKc;Vrb;Vtp0;Vmd0;R9A6RdR8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fph;Fnf;Fd;FS';FE;").
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
S67S68VE3;A1S2eVL1;A1A2").
Hypothesis R_1 : ltac2:(tb__ "0|1|
S1S15ScS2dA1M0A1S2fVsegs;VF;SdS4Z412e8S11S4A1A3S5dVE3;A1S10A5S14G0SdS2dVL1;S11S2dA1A3A2A3").
Hypothesis LN_0 : ltac2:(tb__ "0|0|
S1SfS21S2cS5dVE3;A1A1A1S16A3").
Hypothesis NX_0 : ltac2:(tb__ "0|0|
S1SfS76S5fS1fS2cS5dVE3;A1A1A1A2S10A3").
Hypothesis W_r1 : ltac2:(tb__ "0|0|
S1SfS26S2cVCR1;A1A1S10A3").
Hypothesis D_r1 : ltac2:(tb__ "0|4|
S1S15S12ScS12S1bS1bA2M0A1M1ScS1eA1M2A2M3A1S79S2cS2eVL1;A1A1S2cVCR1;A1A2S14G3SeG1G2SdG0SeS1bS1bS61S64A4SdG0SeS1bS1bS5eS63A4SdG0SeS1bS1bS60S62A4S11G0A1A3A3A3S11S1eA1A4A2A3").
Hypothesis NX_r1 : ltac2:(tb__ "0|0|
S1SfS77S1fS2cVCR1;A1A1S1fS2cS2eVL1;A1A1A1A2S10A3").
Hypothesis R_2 : ltac2:(tb__ "0|1|
S1S15ScS2dA1M0A1S2fVsegs;VF;SdS4Z41570SdS4Z413ccS11S4A1A3A3VCR1;S10A5S14G0SdS2dVLP;SdS2dVLJ;S11S2dA1A3A3A2A3").
Hypothesis LN_1 : ltac2:(tb__ "0|0|
S1SfS21S2cVCR1;A1A1S16A3").
Hypothesis NX_1 : ltac2:(tb__ "0|0|
S1SfS76S5fS1fS2cVCR1;A1A1A2S10A3").

Lemma refill_prefix : ltac2:(tb__ "0|1|
ScS44A1S45S1aS1aScS32Q40A1A1S71S4dVA;Vrb;Vtp0;Vmd0;R6R5R4A7S1aVTR;S35Vsegs;S4cVA;VKc;Vrb;Vtp0;Vmd0;S55A6M0S2eVLP;A1R1R4A5R3A2Fr';S1aVTR;S35Vsegs;G0S2eVLJ;A1R1R5A5R4A2Fr';VTR;S35Vsegs;G0S5dVE3;A1R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Frho;Fst;FW;").
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
End SpineMallocR2.

(* [comment removed for export] *)
Module SegQ3D_exit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "app"; "bool"; "list"; "true"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sobj"; "SVar"; "ss_facts"; "SLit"; "SPBranch"; "holds"; "sprop_below"; "SPNot"; "ss_next"; "valuation"; "SPAlign"; "rw"; "ss_objs"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXRebase"; "apply_axforms"; "AXMerge"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit"; "EX1"; "EX2"; "EX3"; "F_T0x"; "KEPT_X"; "EX2'"; "EX4"; "REST_X"; "SWDr"; "XMERGE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel"; "F_sp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "pre_facts"; "A_globals"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "PostQ3Rs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "DEPTH_R"; "F_T0"; "O_gmax"; "QG"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "@Corelib.Lists.ListDef"; "Forall"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "qbatch"; "aa_cache_inited"; "aa_q_global"; "aa_q_thread"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "O_sb"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMax"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "qsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRD"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "O_mtx00"; "STK"; "SWD"; "cb_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostQ3r"; "PostsQ3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "entsI"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition EX1 : axst := Eval vm_compute in (match apply_axforms PostQ3Rs [AXSelect [0;1;2;3;6;7;4;5;8]%nat] with Some X => X | None => PostQ3Rs end).
Lemma EX1_eq : ltac2:(tb__ "0|0|
S17S8S1fA1S1bS32S0S19S1dS0S1U0S0S1U1S0S1U2S0S1U3S0S1U6S0S1U7S0S1U4S0S1U5S0S1U8S2S1A1A3A3A3A3A3A3A3A3A3A1S2S19A1A3A2S7S1fS24A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition SWDr : sobj := ltac2:(tb__ "0|0|
S55SbPa0A1SbPa1A1SbPa2A1SbPa3A1A4").
Definition KEPT_X : list sobj := ltac2:(tb__ "0|0|
S3SaS54S56S2cA2S30A3").
Definition REST_X : list sobj := ltac2:(tb__ "0|0|
S0SaS53S0SaS35S0SaS45S2SaA1A3A3A3").
Lemma EX1_objs : ltac2:(tb__ "0|0|
S17S5SaA1S16S1eS24A1A1S3SaS28S2bA3A3"). Proof. reflexivity. Qed.
Definition EX2 : axst := ltac2:(tb__ "0|0|
S20S24S49S1eS24A1S28A2A2").
Definition EX2' : axst := ltac2:(tb__ "0|0|
S4aS25S3S9ScS1eS25A1A1S0S9S2eS2S9A1A3A3A2").
Definition XMERGE : list axform := ltac2:(tb__ "0|2|
S0S19S1aU0M0A1S0S19S1aU2A1S0S19S1cG0A1M1S0S19G1S0S19G1S2S19A1A3A3A3A3A3").
Definition EX3 : axst := Eval vm_compute in (match apply_axforms EX2' XMERGE with Some X => X | None => EX2' end).
Lemma EX3_eq : ltac2:(tb__ "0|0|
S17S8S1fA1S1bS29S2dA2S7S1fS26A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition F_T0x : list sprop := ltac2:(tb__ "0|2|
S0S9S14PdM0Z3A2S0S9S11SeS3cSdS38S36Za0A2A1SbG0A1M1A3A1S0S9SeS3cG1S46S4dSdZ50A1A2A3S2S9A1A3A3A3").
Lemma F_T0_eq : ltac2:(tb__ "0|0|
S17S5S9A1S34S3S9S2fS33A1S27A3A3"). Proof. reflexivity. Qed.
Definition EX4 : axst := ax_with_facts EX3 F_T0.
Lemma EX4_ent : ltac2:(tb__ "0|0|
S17S4S59S2aS57A2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma EX2'_below : ltac2:(tb__ "0|1|
S17S4S37S9S10S12S1eS25A1M0A1A1S3S9ScG0A1S0S9S2eS2S9A1A3A3A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma EX4_below : ltac2:(tb__ "0|0|
S17S4S37S9S10S12S1eS26A1A1A1S34A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F_T0x_below : ltac2:(tb__ "0|0|
S17S4S37S9S10S44A1S27A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma EX_facts : ltac2:(tb__ "0|3|
S18S17S5S9A1M0ScS1eS32A1A1S3S9S2fS33A1S0S9S11SeS3dSbPa0A1SdZ0A1A3A1S2S9A1M1A3A3M2A3S17G0ScS1eS26A1A1S3S9G2S0S9S2eG1A3A3A3A2").
Proof. split; reflexivity. Qed.

Lemma F_sp_holds : ltac2:(tb__ "0|0|
S3fS13S31R2R1A2S3aS9SfR2A1S2fS33A1A3SfR3S2eA2F_;F_;Frho;FA;").
Proof.
  intros A rho HT HF. destruct (stk_facts A rho HT HF) as (HD & HTOP & Hsp). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (Forall_inv (Forall_inv_tail HF)) as Hf. unfold holds, F_sp_high in Hf. cbn [eval] in Hf. rewrite add_val in Hf. rewrite u64_lit in Hf by lia.
  pose proof (signed_neg_unsigned (rw rho V_DEPTH) _ eq_refl ltac:(lia)) as EU. rewrite EU in Hf.
  replace (bv_unsigned (rw rho 10%positive) + (bv_signed (rw rho V_DEPTH) + 2 ^ 64)) with (bv_unsigned (rw rho 10%positive) + bv_signed (rw rho V_DEPTH) + 1 * 2 ^ 64) in Hf by lia.
  rewrite Z.mod_add in Hf by lia. rewrite Z.mod_small in Hf by lia.
  unfold F_sp. cbn [holds eval]. rewrite u64_lit by lia. lia.
Qed.

Lemma cell4_of_1_1_2 : ltac2:(tb__ "0|2|
S23S3bS21R2S22R1U1M0Z0M1A3A2S21R3S22S38R2Z1A2G0G1A3A2S21R4S22S38R3Z2A2U2G1A3A2S21R5S22R4U4G1A3A2F_;F_;F_;Fa;Fm;").
Proof.
  intros m a H1 H2 H3 k Hk. unfold cell_ok in *. cbn [c_addr c_w RtCells.c_val] in *. destruct k as [|[|k]].
  - rewrite H1 by lia. reflexivity.
  - replace (a + Z.of_nat 1) with (a + 1 + Z.of_nat 0) by lia. rewrite H2 by lia. reflexivity.
  - replace (a + Z.of_nat (S (S k))) with (a + 2 + Z.of_nat k) by lia. rewrite H3 by lia. destruct k as [|[|k]]; [reflexivity | reflexivity | lia].
Qed.

Section DExit.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).

Lemma exit_R : ltac2:(tb__ "0|5|
S3fS5S40A1M0S13S5S5bQ40M1A1M2A1M3G3S48S17G0S43R6A1S2S40A1M4A3S17S4S41R7A1S6A3S3bS47R9R1A2S47VA0;R2A2F_;Fz;S52VA0;R9A2S17G0S42RaA1R9A3S39S50RaA1S4eA2S17G2S15RaPd0A2S5aG1S4fA2A3S3aS9SfVrho0;A1S27A3S4bS3eS51VK;VA0;Vrho0;ReG4RdA6S32RcRaR9A6S4cS3eS44Vrho0;RcS58VK;VA0;A2RaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Ftp0;Frho;Frest;FA;").
Proof.
  intros A rest rho tp0 tp w HTH HCI HQW HQP HGL HSZ E208 HF0 H. destruct w as [tr [ms md]].
  pose proof (SPA_axforms segsA _ _ rho _ _ tp _ EX1_eq H) as H1.
  destruct (proj2 H1) as (HK & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HRM, HFRM.
  pose proof (proj1 (proj1 H1)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  destruct (kq_facts segsA K HL A rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  destruct HRIG as (E151 & E152 & E155 & E156). change Inv.QG with QG in HMIN.
  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE.
  pose proof (geom_bands _ HG) as (_ & TBD & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI.
  assert (HMAX : cell_ok (view segsA (rm rho)) (mkACell (QG + 64) 8 kQuarantineMax)) by (unfold rtc_inv, rtc_cells in HRTC; exact (cells_ok_nth _ _ 7 _ HRTC eq_refl)).
  assert (HSB : cell_ok (view segsA (rm rho)) (mkACell 0xeddb8 8 (ag_spacebeg (aa_geom A)))) by (unfold rtc_inv, rtc_cells in HRTC; exact (cells_ok_nth _ _ 3 _ HRTC eq_refl)).
  set (rho3 := rho_absorb rho REST_X (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)) in *.
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) KEPT_X REST_X (SLit 0) (QG + 152) (QG + 156) _ Hsm EX1_objs ltac:(left; reflexivity) ltac:(unfold QG; lia) ltac:(lia) ltac:(unfold QG; lia)
                ltac:(unfold cells_inside, QG; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia)) as [AV1 PR1].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) KEPT_X REST_X (SLit 0) (QG + 64) (QG + 80) _ Hsm EX1_objs ltac:(right; left; reflexivity) ltac:(unfold QG; lia) ltac:(lia) ltac:(unfold QG; lia)
                ltac:(unfold cells_inside, QG; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia)) as [AV2 PR2].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) KEPT_X REST_X (SLit 0) 0xeddb8 0xeddc0 _ Hsm EX1_objs ltac:(right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; lia)) as [AV3 PR3].
  fold rho3 v3 in AV1, PR1, AV2, PR2, AV3, PR3. cbn [eval] in AV1, PR1, AV2, PR2, AV3, PR3. rewrite u64_lit in AV1, PR1, AV2, PR2, AV3, PR3 by lia.
  assert (C_mtx : cell_ok v3 (mkACell (QG + 152) 4 0)).
  { apply cell4_of_1_1_2.
    - replace (QG + 152) with (0 + (QG + 152)) by lia. exact (av_cell v3 0 (QG + 152) 1 ZQ 0 rho (fun j => AV1 (QG + 152) 1%nat ZQ j (or_intror (or_introl eq_refl))) eq_refl).
    - replace (QG + 152 + 1) with (0 + (QG + 153)) by lia. exact (av_cell v3 0 (QG + 153) 1 ZQ 0 rho (fun j => AV1 (QG + 153) 1%nat ZQ j (or_introl eq_refl)) eq_refl).
    - replace (QG + 152 + 2) with (0 + (QG + 154)) by lia. exact (av_cell v3 0 (QG + 154) 2 ZQ 0 rho (fun j => AV1 (QG + 154) 2%nat ZQ j (or_intror (or_intror (or_introl eq_refl)))) eq_refl). }
  assert (C_max : cell_ok v3 (mkACell (QG + 64) 8 kQuarantineMax)) by (replace (QG + 64) with (0 + (QG + 64)) by lia; exact (av_cell v3 0 (QG + 64) 8 _ _ rho (fun j => AV2 _ _ _ j (or_introl eq_refl)) eq_refl)).
  assert (C_min : cell_ok v3 (mkACell (QG + 72) 8 kQuarantineMin)) by (replace (QG + 72) with (0 + (QG + 72)) by lia; exact (av_cell v3 0 (QG + 72) 8 _ _ rho (fun j => AV2 _ _ _ j (or_intror (or_introl eq_refl))) E208)).
  assert (C_sb : cell_ok v3 (mkACell 0xeddb8 8 (ag_spacebeg (aa_geom A)))) by (replace 0xeddb8 with (0 + 0xeddb8) by lia; exact (av_cell v3 0 0xeddb8 8 _ _ rho (fun j => AV3 _ _ _ j (or_introl eq_refl)) E155)).
  clear AV1 AV2 AV3.
  set (P := fun z : Z => (QG + 152 <= z < QG + 156) \/ (QG + 64 <= z < QG + 80) \/ (0xeddb8 <= z < 0xeddc0)).
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).
  assert (PIMG : forall z, P z -> 0xe4000 <= z < 0x646000) by (intros z Hz; unfold P, QG in Hz; lia).
  assert (INRG : forall x, in_ranges rho REST_X x -> P (bv_unsigned x)).
  { intros x (o & Ho & Hz). unfold P. destruct Ho as [<-|[<-|[<-|[]]]]; unfold O_mtx00, O_gmax, O_sb, carved in Hz; rewrite obj_range_mk in Hz by (unfold QG; lia);
      cbn [fst snd eval] in Hz; rewrite u64_lit in Hz by lia; lia. }
  destruct (absorb_out rho REST_X (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (GV : forall z, (QG + 64 <= z < QG + 80) \/ (0xeddb8 <= z < 0xeddc0) -> v3 z = v z).
  { intros z [Hz|Hz].
    - destruct (Z_lt_dec z (QG + 72)) as [|]; [apply (cell_ok_same v v3 _ HMAX C_max); cbn [c_addr c_w]; lia | apply (cell_ok_same v v3 _ HMIN C_min); cbn [c_addr c_w]; lia].
    - apply (cell_ok_same v v3 _ HSB C_sb); cbn [c_addr c_w]; lia. }
  destruct (K_FRM_absorb2 K HL A0 rho0 A HQW rho rho3 tp tr md P PD ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)) as [HK3 HF3]; try assumption.
  { intros z Hz. split; [pose proof (PIMG z Hz); unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; lia|].
    destruct Hz as [Hz|Hz]; [left; right; left; right; left; unfold Inv.QG, QG in *; lia | right].
    split; [|exact (GV z Hz)]. right. unfold qrtc_zone. unfold Inv.QG, QG in *. lia. }
  { intros z Hz. fold v3. destruct Hz as [Hz|[Hz|Hz]]; [destruct (PR1 z Hz) as [x Hx] | destruct (PR2 z Hz) as [x Hx] | destruct (PR3 z Hz) as [x Hx]]; rewrite Hx; discriminate. }

  assert (HQ3 : q_mem v3 A).
  { destruct HRM as (HBM & _ & HLR & HTHD & HGH). cbn [app] in HBM. unfold q_mem, qall. rewrite HTH, HGL. cbn [app]. change Inv.QG with QG in *.
    assert (INR : forall b, In b rest -> In b (aa_q_global A)) by (intros b Hb; rewrite HGL; exact Hb).
    assert (OUT : forall z, 0x646000 <= z -> v3 z = v z) by (intros z Hz; apply FR; intros HP; pose proof (PIMG z HP); lia).
    split; [|split; [exact I|split; [|split; [|split; [|exact C_mtx]]]]].
    - apply Forall_forall. intros b Hb. pose proof (proj1 (be_qp _ _ BE)) as HBP. rewrite (qall_A1 A HTH) in HBP.
      apply (batch_mem_frame A v v3 b (proj1 (Forall_forall _ _) HBP b (INR b Hb))); [|exact (proj1 (Forall_forall _ _) HBM b Hb)].
      intros z Hz. apply OUT. exact (bfoot_high A HTH rho b z BE (INR b Hb) Hz).
    - apply qlinks_to_0. apply (qlinks_to_frame v v3 rest 0); [|apply qlinks_to_0; exact HLR].
      intros b z Hb Hz. apply OUT. destruct (batch_addr_facts A HTH rho b BE (INR b Hb)) as (B1 & _). lia.
    - destruct HTHD as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
      assert (TOUT : forall z, ag_thread (aa_geom A) + 0x50 <= z < ag_thread (aa_geom A) + 0x70 -> v3 z = v z) by (intros z Hz; apply FR; intros HP; pose proof (PIMG z HP); lia).
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply TOUT; lia|]. split; [intros X; exfalso; exact (X eq_refl)|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply TOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply TOUT; lia].
    - destruct HGH as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
      assert (GOUT : forall z, QG + 160 <= z < QG + 192 -> v3 z = v z) by (intros z Hz; apply FR; unfold P; unfold Inv.QG, QG in *; lia).
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply GOUT; lia|].
      split; [intros NE; destruct (Q2 NE) as [Qa Qb]; split; (eapply cell_ok_frame1; [|eassumption]); cbn; intros z Hz; apply GOUT; lia|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply GOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply GOUT; lia]. }

  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (STJ : stableA segsA NPRE TJ) by (unfold stableA, TJ; intros; exact I).
  assert (HT : SPA segsA TJ EX1 rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H1) | exact I]).
  pose proof (SPA_unobj segsA TJ rho EX1 KEPT_X REST_X tp tr ms md EX1_objs HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU. change (ax_setS EX1 (set_objs (ax_S EX1) KEPT_X)) with EX2 in HU.
  pose proof (SPA_facts_hold segsA _ rho3 EX2 tp _ HU) as HFa. change (ss_facts (ax_S EX2)) with (ss_facts (ax_S PostQ3Rs)) in HFa. rewrite (proj1 EX_facts) in HFa.
  pose proof (proj1 (Forall_app _ _ _) HFa) as [HFpre _].
  assert (HTOP3 : top_high A rho3) by exact HKTOP.
  assert (HU2 : SPA segsA TJ EX2' rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact HU | exact EX2'_below |]. intros HF. apply Forall_app. split; [exact HF|]. apply Forall_cons; [|apply Forall_nil]. exact (F_sp_holds A rho3 HTOP3 HFpre). }
  pose proof (SPA_axforms segsA _ _ rho3 _ _ tp _ EX3_eq HU2) as HU3.
  pose proof HF3 as ((F1 & F1') & F2 & F3 & F4).
  assert (HU4 : SPA segsA TJ EX4 rho3 tp (tr, mkCfg ms md)).
  { apply SPA_refacts; [exact HU3 | exact EX4_below |]. intros _. rewrite F_T0_eq. apply Forall_app. split; [exact HFpre|].
    apply Forall_forall. intros f Hf. apply (holds_agree_vals NPRE rho0 rho3 f (conj F1 F1')); [exact (proj1 (forallb_forall _ _) F_T0x_below f Hf) | exact (proj1 (Forall_forall _ _) HF0 f Hf)]. }
  destruct (ent_SPA TJ EX4 PostQ3r rho3 tp _ EX4_ent STJ HU4) as [HE AG4].
  set (rho4 := rho_sub rho3 (infer_sub NPRE (ax_S EX4) (ax_S PostQ3r))) in *.
  assert (ERM4 : rm rho4 = rm rho3) by reflexivity.
  apply (LQPA_intro segsA NPRE rho0 tp0 (PostsQ3 K A0) PostQ3r (JLQ3 segsA K A0) rho4 tp _ TJ (or_intror (or_introl eq_refl)) HE).
  - apply (agree_vals_trans NPRE rho0 rho3); [exact (conj F1 F1') | exact (agree_below_vals _ _ _ AG4)].
  - intros _. cbn [w_tr w_cfg cfg_model fst snd]. exists A.
    split; [eapply (kq_stable segsA K HL A); [exact AG4 | apply mat_equiv_refl | exact HK3]|].
    split; [rewrite ERM4; exact HQ3|].
    split; [apply (QP_qpost A0 A HQP HTH); rewrite HGL; exact HSZ|].
    split; [intros a NQ; rewrite ERM4; exact (F2 a NQ)|].
    split; [intros z NQ; rewrite ERM4; exact (F3 z NQ)|].
    split; [intros l; rewrite <- (proj1 (proj2 AG4) l); symmetry; exact (F1' l)|].
    split; [exact I|]. intros a HB Hdef. rewrite ERM4. exact (F4 a HB Hdef).
Qed.
End DExit.
End SegQ3D_exit.

(* [comment removed for export] *)
Module SegQ3D_qi_defs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "bool"; "pair"; "nil"; "list"; "true"; "app"; "prod"; "option"; "Some"; "false"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SVar"; "ss_next"; "sprop"; "valuation"; "SLit"; "ss_facts"; "sprop_below"; "ss_objs"; "swf"; "rw"; "FcsrFrm0"; "agree_below"; "mkSS"; "ss_lenient"; "ss_regs"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "mkLeafA"; "ax_X"; "ax_setS"; "axwf"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states"; "PreQI"; "PostQI"; "QIRET"; "optR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs"; "Cqi"; "sQ"; "RIr"; "RQ"; "SIDEQ"; "PostsQI"; "TQ1"; "TQI"; "TQIf"; "FRAMEQ"; "KEPTQ"; "TQ2"; "TQ3"; "idxT"; "renQ"; "runRr"; "RESTQ"; "TQ4"; "factsQ"; "objsQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "obj_subst"; "rho_sub"; "sprop_subst_opt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "vmap"; "chkNM"; "entsM"; "keepsM"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "O_sb"; "NPRE"; "add"; "runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "JOK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM"; "MI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel"; "addo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "F_DI"; "O_it"; "QIRET2"; "RI"; "vIT"; "DQI"; "DQIs"; "mkD"; "ruI"; "vS7"; "vS9"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "vXF"; "vXK"; "vXL"; "vXS"; "FRlo"; "O_mtx00"; "SWD"; "NXR"; "O_cbD"; "WLOW"; "cb_cells"; "spD"; "@Stdlib.Lists.List"; "forallb"; "In"; "fold_right"; "@Corelib.Lists.ListDef"; "map"; "seq"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "jpostA"; "LQPA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop"; "with_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "O_gmax"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "O_got"; "O_rtc"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side"; "QI_side"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib"; "JQ"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition renQ : wsub := ltac2:(tb__ "0|3|
S0S8S29SdA2M0S3S29SdPaM1S73A4S0G0S3S29SdPfM2S57SfG2A1S13Zc0A1A2A4S0G0S3S29SdPcS57SfG1A1S13Nb8A1A2A4S0G0S3S29SdPdS61A4S0G0S3S29SdP9eSfPc8A1A4S0G0S3S29SdP94SfPc9A1A4S0G0S3S29SdP8aSfPcaA1A4S0G0S3S29SdP8bSfPcbA1A4S0G0S3S29SdP8dSfPccA1A4S0G0S3S29SdP91SfPcdA1A4S0G0S3S29SdP7fSfPceA1A4S0G0S3S29SdP80SfPcfA1A4S0G0S3S29SdP83SfPd1A1A4S0G0S3S29SdP92SfPd2A1A4S0G0S3S29SdP99S13Z1A1A4S0G0S3S29SdP9aS13Z0A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition objsQ (vb : bool) : list sobj := ltac2:(tb__ "0|0|
S77SeSeS45S3eA1S16S21S2cVvb;A1A1A1A4").
Definition factsQ (vb : bool) : list sprop := ltac2:(tb__ "0|1|
S76S5S11A1M0S11S11G0S9S11A1G0Lx;S47S3eR2A2S11S0S11R1R2A3Lg;R1X9x2Lacc;Lf;S4S11A1S14S21S2cVvb;A1A1A1A5").
Definition FRAMEQ : list sobj := ltac2:(tb__ "0|0|
S0SeS6cS0SeS6eS69S68S6aS6bA4S0SeS6dS0SeS86S4SeA1A3A3A3A3").
Definition Cqi (vb : bool) : axst := ltac2:(tb__ "0|1|
S8dS1bS62S1dS21S63A1M0A1S89S19ScSdA1S7SeS43Vvb;A1S39A3S7S11S14G0A1S42Vvb;A1A3S6fSbA9S4S8SdSdA2A1A2").
Definition sQ (vb : bool) : wsub := ltac2:(tb__ "0|1|
S0S8S29SdA2M0S3S29SdP99S13Z1A1A4S0G0S3S29SdP9aS13Z0A1A4S8aP1S21S30Vvb;A1A1S21S2cVvb;A1A1A3A3A3").
Definition RQ (vb : bool) : list sobj := ltac2:(tb__ "0|0|
S2fS80S30Vvb;A1S2cVvb;A1S31Vvb;A1A3A1").
Definition PostsQI (vb : bool) : list leafA := ltac2:(tb__ "0|0|
S0S23S25S2dVvb;A1S7dA2S4S23A1A3").
Definition TQI (vb : bool) : axst := ltac2:(tb__ "0|0|
S81S31Vvb;A1S2cVvb;A1S2dVvb;A1S30Vvb;A1S33Vvb;A1A5").
Definition TQIf (vb : bool) : axst := ltac2:(tb__ "0|0|
S7fS37Vvb;A1S14S21S30Vvb;A1A1A1A2").

Lemma Cqi_wf : ltac2:(tb__ "0|2|
S2S1fS1eS2S28S30R1A1M0A1S6A3S1fS1eS2S17S21G0A1A1S6A3S1eS5S8SdSdA2M1A1S26G0A1S4G1A1A3A2A2Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RQ_eq : ltac2:(tb__ "0|0|
S2S1eS5SeA1S33R1A1S39A3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HeQ : ltac2:(tb__ "0|1|
S2S1eS9S5SeA1M0A1S80S30R1A1S2cR1A1S31R1A1A3SaG0S33R1A1A2A3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl (Some FRAMEQ)). Qed.
Lemma HchkQ : ltac2:(tb__ "0|0|
S2S1eS2S84S30R1A1S2cR1A1S31R1A1S33R1A1S77S23S22S24S35R1A1A4A5S6A3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma HTQ : ltac2:(tb__ "0|0|
S2S23S75S23R1S35R2A1A3S1eS22S81S31R3A1S2cR3A1S24R2A1S30R3A1S33R3A1A5S37R3A1A3F_;FP;Fvb;").
Proof. intros vb P [<-|[]]. reflexivity. Qed.
Lemma FBCQ : ltac2:(tb__ "0|1|
S2S1eS2S74S11S15S10S21S30R1A1A1M0A1A1S14G0A1A3S6A3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma FBTQ : ltac2:(tb__ "0|0|
S2S1eS2S74S11S15S10S21S37R1A1A1A1A1S14S21S30R1A1A1A1A3S6A3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma NXCQ : ltac2:(tb__ "0|0|
S2S87S56S10S21S30R1A1A1A1A2Fvb;"). Proof. intros vb. unfold Pos.le. cbn. discriminate. Qed.

Lemma sQ_vals : ltac2:(tb__ "0|3|
S2S1fS1eSdS44S31R1A1M0PdA2S61A3S1fS1eSdS44G0P9bM1A2SfG1A1A3S1fS1eSdS44G0P9eA2SfPc8A1A3S1fS1eSdS44G0P94A2SfPc9A1A3S1fS1eSdS44G0P8aA2SfPcaA1A3S1fS1eSdS44G0P8bA2SfPcbA1A3S1fS1eSdS44G0P8dA2SfPccA1A3S1fS1eSdS44G0P91A2SfPcdA1A3S1eSdS44G0P92M2A2S2SdLvb;R1SfPd2A1SfG2A1X2x2A3A2A2A2A2A2A2A2A2Fvb;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition idxT (vb : bool) : list nat := ltac2:(tb__ "0|f|
S2S5S1A1Lvb;Vvb;S7S1S0S1U1M0S0S1U16M1S0S1UfM2S0S1U17M3S0S1U18M4S0S1U19S0S1U2S0S1U3S4S1A1M5A3A3M6A3A3A3A3A3A3S7S1S78U4UbA2M7S0S1U0M8S0S1U10M9S0S1U11MaS0S1U12MbS0S1U13McS0S1U14MdS0S1U15MeG5A3A3A3A3A3A3A3A3A3S7S1S0S1G0S0S1GeS0S1G2S0S1G1S0S1G3S0S1G4G6A3A3A3A3A3A3S7S1G7S0S1G8S0S1G9S0S1GaS0S1GbS0S1GcS0S1GdG5A3A3A3A3A3A3A3A3X2x2").
Definition TQ1 (vb : bool) : axst := ltac2:(tb__ "0|1|
S9S22A1S22Lx;S54S38Vvb;A1M0S0S52S53S3dVvb;A1A1S4S52A1A3A2S22R1LX;G0X9x2").
Lemma TQ1_eq : ltac2:(tb__ "0|0|
S2S1eS9S22A1S54S38R1A1S0S52S53S3dR1A1A1S4S52A1A3A2SaS22S36R1A1A2A3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition KEPTQ : list sobj := ltac2:(tb__ "0|0|
S0SeS71S0SeS6cS0SeS70S72A1S0SeS6eS69S68S6aS6bA4S0SeS6dS0SeS86S0SeS8bS0SeS8cS4SeA1A3A3A3A3A3A3A3A3").
Definition RESTQ (vb : bool) : list sobj := ltac2:(tb__ "0|0|
S79SeU8S16S21S36Vvb;A1A1A1A3").
Lemma TQ1_objs : ltac2:(tb__ "0|0|
S2S1eS5SeA1S16S21S36R1A1A1A1S7SeS3aS40R1A1A3A3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition TQ2 (vb : bool) : axst := ltac2:(tb__ "0|1|
S27S36Vvb;A1M0S7eS21G0A1S3aA2A2").
Definition TQ3 (vb : bool) : axst := ltac2:(tb__ "0|0|
S5cS5cS3bVvb;A1S55A2S5eA2").
Definition TQ4 (vb : bool) : axst := ltac2:(tb__ "0|0|
S7fS3cVvb;A1S5dA2").
Definition RIr : axst := ltac2:(tb__ "0|1|
S64S2eS7S8S1SdA2M0S65S66S67A2S0G0S3S1SdU1S13S5fA1A4S4G0A1A3A3S69S68S6aS6bS0SeS55S0SeS5eS4SeA1A3A3S5dA8").
Lemma TQ4_ent : ltac2:(tb__ "0|0|
S2S1eS2S4fS41R1A1S32S5bA3S6A3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma TQ3_swf : ltac2:(tb__ "0|1|
S2S1fS1eS2S17S85S21S3bR1A1M0A1S55A2A1S6A3S1eS2S17S85S21S5cG0S55A2A1S5eA2A1S6A3A2Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma TQ4_below : ltac2:(tb__ "0|0|
S2S1eS2S74S11S15S10S21S3cR1A1A1A1A1S5dA3S6A3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition runRr : list leafA := ltac2:(tb__ "0|0|
S58UaS0S2aS5fS4S2aA1A3S32A3").
Lemma runRr_eq : ltac2:(tb__ "0|0|
S1eS5S23A1S58UaS0S2aS5fS4S2aA1A3S32A3S3fA3"). Proof. unfold runRr. reflexivity. Qed.
Lemma chkRrM : ltac2:(tb__ "0|1|
S1eS2S4eS10S21S32A1A1S3fS0S8S22S4dA2M0S3S22S4dS60S5bA4S4G0A1A3A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma nxRIr : ltac2:(tb__ "0|1|
S1fS1eS2S1cS21S32A1M0A1SbA3S87S56S10G0A1A2A2"). Proof. split; [reflexivity | unfold Pos.le; cbn; discriminate]. Qed.
Section TR.
Context {Q : assn} (X : trk Q).
Theorem seg_D_RrM : ltac2:(tb__ "0|1|
S49S12S5S51Q40A1A1S5aVQ;VX;R3A3S22S4dS12S75S8S22S4dA2M0S3S22S4dR3R2A4S0G0S3S22S4dS60S5bA4S4G0A1A3A3S50R3R7R2A3S59VQ;VX;S48S2bR9R5R3R7A5A3F_;F_;Frho';FM;FT;S59VQ;VX;S48S2bR5S32R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 10%nat _ RIr runRr [(RI, MI)] runRr_eq chkRrM (proj1 nxRIr) (proj2 nxRIr) J rho tp HJ HC). Qed.
End TR.

Definition SIDEQ (vb : bool) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S20S2aS2aS20S2aS2aS8eVrho;Vvb;R2R1A4Ld;A2Lx;A2").
Lemma SIDEQ_ext : ltac2:(tb__ "0|0|
S2S12S12S29S88R1S10S21S2cR4A1A1A1A2S1eS51Q40A1S18R3R2A2S18R4R2A2A3F_;Fi;S34R4R3A2S34R5R3A2F_;F_;Fr';Fr;Fvb;").
Proof.
  intros vb r r' HE (x & d & H). exists x, d. unfold QI_side in *. rewrite (proj1 (proj2 (proj2 (preQI_wf vb)))) in HE.
  assert (E : forall i, (i < NPRE)%positive -> bv_unsigned (rw r' i) = bv_unsigned (rw r i)) by (intros i Hi; rewrite (HE i Hi); reflexivity).
  assert (EB : bv_unsigned (eval r' (bgv vb)) = bv_unsigned (eval r (bgv vb))) by (destruct vb; cbn [bgv eval]; unfold vAB; cbn [eval]; apply E; reflexivity).
  cbv zeta in *. unfold V_CLS, V_SIZE in *. rewrite !E by reflexivity. rewrite EB. exact H.
Qed.
Lemma JQ_LQA1 : ltac2:(tb__ "0|1|
S49S29S12S5S51Q40A1A1S22S7aS83S2bR5R4R3S0S8S22S82A2M0S3S22S82R2S8fR6A1A4S4G0A1A3R1A6S4aS2bR7R6R5R4S0S23S25R3S7dA2S4S23A1A3R2A7F_;Fw;FPost;Ftp;Frho;Fn;FJ;").
Proof.
  intros J n rho tp Post w (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
  destruct Hin as [E|[]]. injection E as <- <-. destruct HJL as (HJ & -> & Hrm & Hrl). destruct Hag as [Hw Hl].
  exists (mkLeafA Post RsSymJump), rho'. split; [left; reflexivity|]. split; [|split; [exact Hsm | exact HJ]].
  split; [exact Hw|]. split; [exact Hl|]. intros a. symmetry. apply Hrm.
Qed.
Lemma QI_sumS : ltac2:(tb__ "0|1|
S2S7aOF_;S49S12S5S51Q40A1A1S4cS2bR4R3A3S4bS2bS10S21S2cR6A1A1A1R4A3S34R7R4A2S7cS2bR7S48S2bR6S2cR8A1M0R5R4A5S4aS2bR6S10S21G0A1A1R5R4S35R8A1A6A4F_;F_;F_;Ftp;Frho;FJx;Fok;Fvb;").
Proof.
  intros vb ok Jx rho tp HOK HST (x & d & HS). rewrite (proj1 (proj2 (proj2 (preQI_wf vb)))) in *.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (JQ_LQA1 Jx NPRE rho tp (PostQI vb) w Hw) | exact (seg_QI_sound_clean vb Jx ok rho tp x d HOK HST HS)].
Qed.
Lemma QI_sumC : ltac2:(tb__ "0|1|
S2S49S12S5S51Q40A1A1S4bS2bS10S21S2cR4A1A1A1R3A3S34R5R3A2S7bS2bS48S2bR5S2cR6A1M0R4R3A5S4aS2bR5S10S21G0A1A1R4R3S35R6A1A6A3F_;F_;Ftp;Frho;FJx;Fvb;").
Proof.
  intros vb Jx rho tp HST (x & d & HS). rewrite (proj1 (proj2 (proj2 (preQI_wf vb)))) in *.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (JQ_LQA1 Jx NPRE rho tp (PostQI vb) w Hw) | exact (seg_QI_complete_clean vb Jx rho tp x d HST HS)].
Qed.

Section CALL.
Context {Q : assn} (X : trk Q).
Theorem qi_call : ltac2:(tb__ "0|1|
S2S49S12S5S51Q40A1A1S5aVQ;VX;R3A3S34R5S46R3S31R5A1A2A2S12S1aS10S21S30R7A1M0A1A1R5R1A3S59VQ;VX;S48S2bR7S38R8A1R2R5A5A3F_;Frho';S59VQ;VX;S48S2bR6G0R5R4A5A3F_;F_;F_;Ftp;FrhoE;FJ;Fvb;").
Proof.
  intros vb J rhoE tp HJ HS HC.
  exact (tr_callS X (Cqi vb) (PreQI vb) (PostsQI vb) (sQ vb) (RQ vb) (TQI vb) (SIDEQ vb) (SIDEQ_ext vb) (QI_sumS vb) (QI_sumC vb)
           (HeQ vb) (HchkQ vb) (HTQ vb) (FBCQ vb) (FBTQ vb) (NXCQ vb) J rhoE tp HJ HS HC).
Qed.
End CALL.
End SegQ3D_qi_defs.

(* [comment removed for export] *)
Module SegQ3D_loop.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "aa_cache_inited"; "aa_q_global"; "aa_q_thread"; "mkQB"; "qb_addr"; "qb_items"; "@Corelib.Init.Datatypes"; "list"; "cons"; "nil"; "nat"; "prod"; "app"; "bool"; "true"; "S"; "length"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "JOK"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop"; "HVX"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRD"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop.DLoop"; "INVD"; "INVI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "qsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel"; "HVI"; "HVS"; "HVB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QW"; "sec_foot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "keepsM"; "vmap"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "pow"; "le"; "mul"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "DHn"; "RC"; "DH"; "DI"; "DQCs"; "DQIs"; "DTs"; "PostQ3Rs"; "RI"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM"; "MI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "Xg"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DLoop.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation).
Context {Q : assn} (X : trk Q).
Hypothesis HJD : ltac2:(tb__ "0|1|
S3SaS2A1M0G0S1cVQ;VX;S24VK;VA0;Vrho0;R3R2R1A6A3Frest;Ftmp;FA;").
Hypothesis HJI : ltac2:(tb__ "0|1|
S3S0S0SdSaSeS0S0A2A1SaS2A1M0G0S1cVQ;VX;S25VK;VA0;Vrho0;R7R6R5R4R3R2R1AaA3Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA;").
Variable rest : list qbatch.

Variable TPI : list word -> Prop.

Definition INVD (A : AA) (tmp : list qbatch) : Prop := ltac2:(tb__ "0|1|
S1eS1dSaS2A1M0S6VA;A1ScS2A1A3S1eS1dS10S4VA;A1S11A3S1eS0S2dVA;R1A2S2dVA0;R2A2F_;Fz;S1eS26VA0;VA;A2S1eS1dG0S5VA;A1SfS2Vtmp;Vrest;A3A3S0S2eVA;R1A2S2eVA0;R2A2F_;Fz;A2A2A2A2A2").
Definition INVI (A : AA) (a : Z) (its : list (Z * Z)) (tmp' : list qbatch) : Prop := ltac2:(tb__ "0|1|
S1eS1dSaS2A1M0S6VA;A1ScS2A1A3S1eS1dS10S4VA;A1S11A3S1eS0S2dVA;R1A2S2dVA0;R2A2F_;Fz;S1eS26VA0;VA;A2S1eS20S0S0S1dG0S5VA;A1SbS2S7Va;Vits;R1A3SfS2Vtmp';Vrest;A3A3A3Ls;A2S0S2eVA;R1A2S2eVA0;R2A2F_;Fz;A2A2A2A2A2").
Lemma INVD_INVI : ltac2:(tb__ "0|0|
S3S2SaS2A1S27R3SbS2R2R1A3A2S28R4S8R3A1S9R3A1R2A4F_;Ftmp';Fb;FA;").
Proof. intros A b tmp' (H1 & H2 & H3 & H4 & H5 & H6). repeat (split; [assumption|]). split; [|exact H6]. exists (qb_size b). rewrite H5. destruct b; reflexivity. Qed.

Lemma tr_glue : ltac2:(tb__ "0|0|
S42S19S44SaS22Q40A1A1S15OF_;S43R6R1A1S20S15S15S1eS18S1aR7R6R1R5R3A6R4R1A1A2Lrho2;A2F_;Fw;S15R3R1A1S1bVQ;VX;S18S1aR7R6R2R5A5A3F_;Frho2;S1bVQ;VX;R7A3F_;F_;FPU;Ftp;FSt;FJ;FP0;").
Proof.
  intros P0 J St tp PU HG HC.
  apply (tr_ex X valuation (fun rho2 w => SPA segsA J St rho2 tp w /\ PU rho2) P0 HG). intros rho2.
  apply (tr_pure X _ (PU rho2)); [intros w (_ & a); exact a|]. intros HP.
  eapply (tr_conseq X); [|exact (HC rho2 HP)]. intros w (Hs & _). exact Hs.
Qed.

Definition QI_step : Prop := ltac2:(tb__ "0|3|
S3S0S0SdSeS0S0A2M0SaG0A1SaS2A1S15SaS22Q40A1A1M1VTPI;R1A1M2S28RaR9SbG0R6R5A3R4A4S21R4R5A2S2aR5RbRaR9R8A5S2bR6RcRaR9A4S3S15G1G2S28R4R11RdRcA4S21R4RdA2S2aR5R13R12R11R10A5S2bR6R14R12R11A4S1bVQ;VX;S18S1aS25VK;VA0;Vrho0;R8R15R14S12R13A1R11R10Vrest;AaS3eR7R6A5A3F_;F_;F_;F_;F_;Ftp';Frho';FA';S1bVQ;VX;S18S1aS25VK;VA0;Vrho0;RfReRdRcSbG0RbRaA3R9Vrest;AaS3bR8R7A5A3F_;F_;F_;F_;F_;F_;Ftp;Frho;Ftmp';Fits;Fit;Fnd;Fn0;Fa;FA;").
Definition QC_step : Prop := ltac2:(tb__ "0|5|
S3S0S0SdSaS2A1S15SaS22Q40M0A1M1A1M2VTPI;R1A1M3S28R8R7ScSeS0S0A2A1M4R4A4S21R4R5A2S1dG1S16R5Pa6A2S23G0R9A2A3S3S15G2G3S27R4RbA2S21R4RcA2S1bVQ;VX;S18S1aS24VK;VA0;Vrho0;R6RdVrest;A6S37R5R4A5A3F_;F_;F_;Ftp';Frho';FA';S1bVQ;VX;S18S1aS25VK;VA0;Vrho0;RcRbRaR9G4R8Vrest;AaS3aR7R6A5A3F_;F_;F_;F_;F_;Ftp;Frho;Ftmp';Fnd;Fn0;Fa;FA;").
Definition EXIT_step : Prop := ltac2:(tb__ "0|3|
S3S15SaS22Q40M0A1M1A1VTPI;R1A1S27R4ScS2A1M2A2S1dG1S16R4Pd0A2S23G0S45A2A3S1bVQ;VX;S18S1aS24VK;VA0;Vrho0;R6G2Vrest;A6S3dR5R4A5A3F_;F_;F_;Ftp;Frho;FA;").
Hypothesis HQI : QI_step.
Hypothesis HQC : QC_step.
Hypothesis HEXIT : EXIT_step.

Lemma keeps_rm : ltac2:(tb__ "0|0|
S30S15S15S2fR3R2R1A3S1dS22Q40A1S14S22Q8A1A1F_;S17R2A1S17R3A1A3F_;Frho';Frho;FM;").
Proof. intros M rho rho' [Hag _]. apply functional_extensionality. intros a. symmetry. apply (proj2 (proj2 Hag)). Qed.
Lemma HVX_keep : ltac2:(tb__ "0|0|
SaS1A1S15S15SaS2A1S2fS47R4A1R3R2A3S1S3fS1R1SbS1Pb8SbS1Pb9SbS1PbaSbS1PbbSbS1Pd0ScS1A1A3A3A3A3A3A3S3fS1R2R7A3F_;Fv;S21R5R3A2S21R5R4A2F_;F_;F_;Ftmp;Frho';Frho;Fl;").
Proof. intros l rho rho' tmp HK HIN (E1 & E2 & E3 & E4 & E5). unfold HVX. rewrite !(keepsM_id l rho rho' _ HK) by (apply HIN; cbn; tauto). tauto. Qed.
Lemma HVI_keep : ltac2:(tb__ "0|0|
S15S15S0S0SdSeS0S0A2S2fS46R6R5A3S2aR7R5R4R3R2A5S2aR7R6R5R4R3A5F_;F_;Fit;Fnd;Fn0;Fa;Frho';Frho;").
Proof. intros rho rho' a n0 nd it HK (E1 & E2 & E3 & E4 & E5). unfold HVI. unfold MI in HK. rewrite !(keepsM_id _ rho rho' _ HK) by (cbn; tauto). tauto. Qed.
Lemma HVS_keep : ltac2:(tb__ "0|0|
S30S15S15S0SdSeS0S0A2S2fR6R5R4A3S2bR6R4R3R2A4S2bR6R5R4R3A4F_;F_;Fit;Fnd;Fa;Frho';Frho;FM;").
Proof. intros M rho rho' a nd it HK H. unfold HVS. rewrite (keeps_rm M rho rho' HK). exact H. Qed.

Lemma jrd_len2 : ltac2:(tb__ "0|0|
S3SaS2A1S15SaS22Q40A1A1SaS41A1S40S27R6R5A2S24VK;VA0;Vrho0;R7R6Vrest;R5R4R3R2AaS33S34Z2000S35S13S2R7A2A1A2S29R7A1A2F_;F_;Fmd;Ftr;Ftp;Frho;Ftmp;FA;").
Proof.
  intros A tmp rho tp tr md (HTH & HCI & _ & _ & HGL & _) (HK & (HBM & _) & _).
  pose proof (benv_of_K K HL A HCI rho tp tr md HK) as BE. pose proof (proj1 (be_qp _ _ BE)) as HBP. rewrite (qall_A1 A HTH), HGL in HBP.
  apply Forall_app in HBP as [P1 _]. apply Forall_app in HBM as [M1 _]. pose proof (qsize_ge A _ tmp P1 M1) as Q1. unfold kQuarantineBatchSize in Q1. exact Q1.
Qed.

Section Batch.
Variable tmp' : list qbatch.
Hypothesis HSZ' : qsize tmp' < 2 ^ 62.
Hypothesis IHn : ltac2:(tb__ "0|0|
S3S15SaS22Q40A1A1VTPI;R1A1S1fS1dSaS2A1Vtmp';ScS2A1A3A1S27R5Vtmp';A2S21R5Vtmp';A2S1bVQ;VX;S18S1aS24VK;VA0;Vrho0;R7Vtmp';Vrest;A6S36R6R5A5A3F_;F_;F_;F_;Ftp;Frho;FA;").

Lemma rc_step : ltac2:(tb__ "0|0|
S3S15SaS22Q40A1A1VTPI;R1A1S27R4Vtmp';A2S21R4Vtmp';A2S1bVQ;VX;S18S1aS24VK;VA0;Vrho0;R6Vtmp';Vrest;A6S37R5R4A5A3F_;F_;F_;Ftp;Frho;FA;").
Proof.
  intros A rho tp HTP HI HV. apply (seg_D_RCM X _ rho tp (HJD _ _ _)). intros Tx M rho' HIN HKp.
  unfold TsRCM in HIN. cbn [In] in HIN. destruct HIN as [E|[E|[]]]; injection E as <- <-.
  - pose proof (HVX_keep _ rho rho' tmp' HKp ltac:(cbn; tauto) HV) as HV'.
    apply (tr_pure X _ (tmp' <> [])).
    + intros [tr [ms md]] Hw. pose proof (jrd_len2 A tmp' rho' tp tr md HI (proj2 Hw)) as LN.
      pose proof (SPA_facts_hold segsA _ rho' DHn tp _ Hw) as HFa.
      assert (F : holds rho' (SPBranch BC_NE vXK (SLit 0))) by (apply (proj1 (Forall_forall _ _) HFa); unfold DHn, mkD, mkR; cbn [ax_S mkA ss_facts]; apply in_or_app; right; left; reflexivity).
      destruct HV' as (E184 & _). unfold vXK in F. cbn [holds branch_taken eval] in F. rewrite E184 in F. unfold bv_eqb in F. apply negb_true_iff in F. apply Z.eqb_neq in F.
      rewrite !u64_lit in F by lia. intros ->. cbn in F. lia.
    + intros NE. exact (IHn A rho' tp HTP NE HI HV').
  - apply (tr_pure X _ (tmp' = [])).
    + intros [tr [ms md]] Hw. pose proof (jrd_len2 A tmp' rho' tp tr md HI (proj2 Hw)) as LN.
      pose proof (SPA_facts_hold segsA _ rho' PostQ3Rs tp _ Hw) as HFa.
      assert (F : holds rho' (SPNot (SPBranch BC_NE (SVar 160) (SLit 0)))) by (apply (proj1 (Forall_forall _ _) HFa); unfold PostQ3Rs, mkR; cbn [ax_S mkA ss_facts]; apply in_or_app; right; left; reflexivity).
      destruct HV as (E184 & _). pose proof (proj2 HKp 160%positive (SVar 184) ltac:(unfold MRET; cbn; tauto)) as E160. cbn [eval] in E160. rewrite E184 in E160.
      cbn [holds branch_taken eval] in F. rewrite E160 in F. unfold bv_eqb in F. destruct tmp' as [|t0 t]; [reflexivity|]. exfalso. apply F. apply negb_true_iff. apply Z.eqb_neq.
      rewrite !u64_lit by lia. cbn [length]. lia.
    + intros ->. apply (HEXIT A rho' tp HTP HI). rewrite (proj2 HKp 208%positive (SVar 208) ltac:(unfold MRET; cbn; tauto)). cbn [eval]. exact (proj2 (proj2 (proj2 (proj2 HV)))).
Qed.

Lemma dt_step : ltac2:(tb__ "0|3|
S3S0S0SdS15SaS22Q40M0A1M1A1VTPI;R1A1S28R7R6ScSeS0S0A2A1M2Vtmp';A4S21R4Vtmp';A2S1dG1S16R5Pa6A2S23G0R8A2A3S1bVQ;VX;S18S1aS25VK;VA0;Vrho0;RaR9R8R7G2Vtmp';Vrest;AaS3cR6R5A5A3F_;F_;F_;F_;Ftp;Frho;Fnd;Fn0;Fa;FA;").
Proof.
  intros A a n0 nd rho tp HTP HI HV E166. apply (seg_D_DTM X _ rho tp (HJI _ _ _ _ _ _ _)). intros Tx M rho' HIN HKp.
  cbn [In] in HIN. destruct HIN as [E|[]]; injection E as <- <-.
  apply (HQC A a n0 nd tmp' rho' tp HTP HI (HVX_keep _ rho rho' tmp' HKp ltac:(cbn; tauto) HV)).
  - unfold MC in HKp. rewrite (keepsM_id _ rho rho' 166%positive HKp) by (cbn; tauto). exact E166.
  - intros A' rho2 tp2 HTP2 HI2 HV2. exact (rc_step A' rho2 tp2 HTP2 HI2 HV2).
Qed.

Lemma item_loop : ltac2:(tb__ "0|1|
SaSeS0S0A2M0A1G0SdS3S0S0S15SaS22Q40A1A1VTPI;R1A1S28R6R5SbG0R8R9A3Vtmp';A4S21R4Vtmp';A2S2aR5R7R6R9RaA5S2bR6R8RaRbA4S1bVQ;VX;S18S1aS25VK;VA0;Vrho0;RaR9R8RbSbG0RcRdA3Vtmp';Vrest;AaS39R7R6A5A3F_;F_;F_;F_;F_;Ftp;Frho;Fn0;Fa;FA;Fnd;Fit;Fits;").
Proof.
  induction its as [|it1 its' IH]; intros it nd A a n0 rho tp HTP HI HV HVi HVs.
  - apply (seg_D_DIM X _ rho tp (HJI _ _ _ _ _ _ _)). intros Tx M rho' HIN HKp. cbn [In] in HIN. destruct HIN as [E|[]]; injection E as <- <-.
    apply (HQI A a n0 nd it [] tmp' rho' tp HTP HI (HVX_keep _ rho rho' tmp' HKp ltac:(cbn; tauto) HV) (HVI_keep rho rho' a n0 nd it HKp HVi) (HVS_keep _ rho rho' a nd it HKp HVs)).
    intros A' rho2 tp2 HTP2 HI2 HV2 HVi2 HVs2.
    apply (seg_D_RIM X _ rho2 tp2 (HJI _ _ _ _ _ _ _)). intros Tx M rho3 HIN HKp3. unfold TsRIM, TsRI in HIN. cbn [map In] in HIN.
    destruct HIN as [E|[E|[]]]; injection E as <- <-.
    + apply (tr_pure X _ False); [|intros []]. intros w Hw. pose proof (HVI_keep rho2 rho3 a n0 nd it HKp3 HVi2) as (E162 & _ & E164 & _).
      destruct (proj2 Hw) as (_ & (_ & HN0 & HN1 & _) & _). unfold kQuarantineBatchCount in HN1. cbn [length Z.of_nat] in HN0.
      pose proof (proj1 (ri_flags A0 _ true rho3 tp2 w n0 nd Hw E162 E164 ltac:(lia) ltac:(lia)) eq_refl). lia.
    + destruct HI2 as (I1 & I2 & I3 & I4 & (s & I5) & I6).
      apply (tr_glue _ (JRI K A0 rho0 A' a n0 (S nd) [] tmp' rest) DTs tp2 (fun r => HVX r tmp' /\ rw r 166%positive = Z_to_bv 64 a)).
      * intros w Hw. exact (dtc_glue K HL A0 rho0 A' a s n0 nd it tmp' rest rho3 tp2 w I1 I2 I3 I5 Hw (HVX_keep _ rho2 rho3 tmp' HKp3 ltac:(cbn; tauto) HV2) (HVI_keep rho2 rho3 a n0 nd it HKp3 HVi2) (HVS_keep _ rho2 rho3 a nd it HKp3 HVs2)).
      * intros r [R1 R2]. apply (dt_step A' a n0 (S nd) r tp2 HTP2); [|exact R1 | exact R2]. repeat (split; [assumption|]). split; [exists s; exact I5 | exact I6].
  - apply (seg_D_DIM X _ rho tp (HJI _ _ _ _ _ _ _)). intros Tx M rho' HIN HKp. cbn [In] in HIN. destruct HIN as [E|[]]; injection E as <- <-.
    apply (HQI A a n0 nd it (it1 :: its') tmp' rho' tp HTP HI (HVX_keep _ rho rho' tmp' HKp ltac:(cbn; tauto) HV) (HVI_keep rho rho' a n0 nd it HKp HVi) (HVS_keep _ rho rho' a nd it HKp HVs)).
    intros A' rho2 tp2 HTP2 HI2 HV2 HVi2 HVs2.
    apply (seg_D_RIM X _ rho2 tp2 (HJI _ _ _ _ _ _ _)). intros Tx M rho3 HIN HKp3. unfold TsRIM, TsRI in HIN. cbn [map In] in HIN.
    destruct HIN as [E|[E|[]]]; injection E as <- <-.
    + destruct HI2 as (I1 & I2 & I3 & I4 & (s & I5) & I6).
      apply (tr_glue _ (JRI K A0 rho0 A' a n0 (S nd) (it1 :: its') tmp' rest) DI tp2 (fun r => HVX r tmp' /\ HVI r a n0 (S nd) it1 /\ HVS r a (S nd) it1)).
      * intros w Hw. exact (dic_glue K HL A0 rho0 A' a s n0 nd it it1 its' tmp' rest rho3 tp2 w I1 I2 I3 I5 Hw (HVX_keep _ rho2 rho3 tmp' HKp3 ltac:(cbn; tauto) HV2) (HVI_keep rho2 rho3 a n0 nd it HKp3 HVi2) (HVS_keep _ rho2 rho3 a nd it HKp3 HVs2)).
      * intros r (R1 & R2 & R3). apply (IH it1 (S nd) A' a n0 r tp2 HTP2); [|exact R1 | exact R2 | exact R3]. repeat (split; [assumption|]). split; [exists s; exact I5 | exact I6].
    + apply (tr_pure X _ False); [|intros []]. intros w Hw. pose proof (HVI_keep rho2 rho3 a n0 nd it HKp3 HVi2) as (E162 & _ & E164 & _).
      destruct (proj2 Hw) as (_ & (_ & HN0 & HN1 & _) & _). unfold kQuarantineBatchCount in HN1. cbn [length] in HN0.
      pose proof (ri_flags A0 _ false rho3 tp2 w n0 nd Hw E162 E164 ltac:(lia) ltac:(lia)) as FL.
      assert (NE : Z.of_nat (S nd) <> n0) by lia. discriminate (proj2 FL NE).
Qed.
End Batch.

Lemma dh_step : ltac2:(tb__ "0|3|
S2SaS2A1M0S3S15SaS22Q40A1A1M1S3S15G1VTPI;R1A1S1fS1dG0R8ScS2A1A3A1S31S29R9A1S32Z2Z3eA2M2A2S27R6RaA2S21R6RbA2S1bVQ;VX;S18S1aS24VK;VA0;Vrho0;R8RcVrest;A6S36R7R6A5A3F_;F_;F_;F_;F_;Ftp';Frho';FA';VTPI;R2A1S27R5SbS2R7R6A3A2S31S29SbS2R8R7A3A1G2A2S21R6SbS2R9R8A3A2S2cR7RaR9A3S1bVQ;VX;S18S1aS24VK;VA0;Vrho0;R9SbS2RbRaA3Vrest;A6S38R8R7A5A3F_;F_;F_;F_;F_;F_;Ftp;Frho;FA;Ftmp';Fb;").
Proof.
  intros b tmp' A rho tp IHn HTP HI HSZ HV HVb. pose proof HI as (I1 & I2 & I3 & I4 & I5 & I6).
  apply (seg_D_DBM X _ rho tp (HJD _ _ _)). intros Tx M rho' HIN HKp.
  assert (HV' : HVX rho' (b :: tmp')) by (unfold TsDBM in HIN; apply in_map_iff in HIN as (T0 & E & _); injection E as _ <-; exact (HVX_keep _ rho rho' _ HKp ltac:(cbn; tauto) HV)).
  assert (HVb' : HVB rho' b tmp').
  { unfold TsDBM in HIN. apply in_map_iff in HIN as (T0 & E & _). injection E as _ <-. destruct HVb as (E1 & E2 & E3). unfold HVB, MB in *.
    rewrite !(keepsM_id _ rho rho' _ HKp) by (cbn; tauto). tauto. }
  assert (CASES : exists nz cz, Tx = DBx nz cz).
  { unfold TsDBM, TsDB in HIN. cbn [map In] in HIN. destruct HIN as [E|[E|[E|[E|[]]]]]; injection E as <- _; eexists; eexists; reflexivity. }
  destruct CASES as (nz & cz & ->). destruct cz.
  - apply (tr_glue _ (JRI K A0 rho0 A (qb_addr b) (Z.of_nat (length (qb_items b))) 0 (qb_items b) tmp' rest) DTs tp (fun r => HVX r tmp' /\ rw r 166%positive = Z_to_bv 64 (qb_addr b) /\ qb_items b = [] /\ qsize tmp' < 2 ^ 62)).
    + intros w Hw. exact (dbt_glue K HL A0 rho0 nz A b tmp' rest rho' tp w I1 I2 I3 I5 HSZ Hw HV' HVb').
    + intros r (R1 & R2 & R3 & R4). pose proof (INVD_INVI A b tmp' HI) as HII. rewrite R3 in *.
      exact (dt_step tmp' R4 (fun A' rho2 tp2 HT2 NE => IHn A' rho2 tp2 HT2 NE R4) A (qb_addr b) _ 0%nat r tp HTP HII R1 R2).
  - apply (tr_pure X _ (exists it0 its, qb_items b = it0 :: its)).
    + intros [tr [ms md]] Hw. destruct (jrd_pure K HL A0 rho0 A b tmp' rest rho' tp tr md I1 I2 I5 (proj2 Hw)) as (BE & QB & QT0 & QTL & HCNT & HT0).
      destruct (dbx_flags _ nz false rho' tp _ b tmp' Hw HVb' HT0 ltac:(unfold kQuarantineBatchCount in HCNT; lia)) as (_ & _ & FL3 & _).
      destruct (qb_items b) as [|it0 its]; [discriminate (FL3 eq_refl) | exists it0, its; reflexivity].
    + intros (it0 & its & HIT).
      apply (tr_glue _ (JRI K A0 rho0 A (qb_addr b) (Z.of_nat (length (qb_items b))) 0 (qb_items b) tmp' rest) DI tp (fun r => HVX r tmp' /\ HVI r (qb_addr b) (Z.of_nat (length (qb_items b))) 0 it0 /\ HVS r (qb_addr b) 0 it0 /\ qsize tmp' < 2 ^ 62)).
      * intros w Hw. exact (dbi_glue K HL A0 rho0 nz A b it0 its tmp' rest rho' tp w I1 I2 I3 I5 HIT HSZ Hw HV' HVb').
      * intros r (R1 & R2 & R3 & R4). pose proof (INVD_INVI A b tmp' HI) as HII. rewrite HIT in *.
        exact (item_loop tmp' R4 (fun A' rho2 tp2 HT2 NE => IHn A' rho2 tp2 HT2 NE R4) its it0 0%nat A (qb_addr b) _ r tp HTP HII R1 R2 R3).
Qed.

Lemma dhn_loop : ltac2:(tb__ "0|1|
SaS2A1M0S3S15SaS22Q40A1A1VTPI;R1A1S1fS1dG0R5ScS2A1A3A1S27R5R6A2S31S29R7A1S32Z2Z3eA2A2S21R6R8A2S1bVQ;VX;S18S1aS24VK;VA0;Vrho0;R8R9Vrest;A6S36R7R6A5A3F_;F_;F_;F_;F_;Ftp;Frho;FA;Ftmp;").
Proof.
  induction tmp as [|b tmp' IH]; intros A rho tp HTP NE HI HSZ HV; [congruence|]. pose proof HI as (I1 & I2 & I3 & I4 & I5 & I6).
  apply (tr_glue _ (JRD K A0 rho0 A (b :: tmp') rest) DH tp (fun r => HVX r (b :: tmp') /\ HVB r b tmp')).
  - intros w Hw. exact (dhn_glue K HL A0 rho0 A b tmp' rest rho tp w I1 I2 I5 Hw HV).
  - intros r (R1 & R2). apply (dh_step b tmp' A r tp); try assumption.
    intros A' rho2 tp2 HTP2 NE2 HS2 HI2 HV2. exact (IH A' rho2 tp2 HTP2 NE2 HI2 HS2 HV2).
Qed.

Theorem dorecycle_xg : ltac2:(tb__ "0|1|
SaS2A1M0S3S15SaS22Q40A1A1VTPI;R1A1S1fS1dG0R5ScS2A1A3A1S27R5R6A2S31S29R7A1S32Z2Z3eA2A2S21R6R8A2S1bVQ;VX;S18S1aS24VK;VA0;Vrho0;R8R9Vrest;A6S48R7R6A5A3F_;F_;F_;F_;F_;Ftp;Frho;FA;Ftmp;").
Proof.
  intros tmp A rho tp HTP NE HI HSZ HV. pose proof HI as (I1 & I2 & I3 & I4 & I5 & I6).
  apply (seg_R_S1M X _ rho tp (HJD _ _ _)). intros Tx M rho1 HIN HKp1. cbn [In] in HIN. destruct HIN as [E|[]]; injection E as <- <-.
  pose proof (HVX_keep _ rho rho1 tmp HKp1 ltac:(cbn; tauto) HV) as HV1.
  apply (seg_D_D0M X _ rho1 tp (HJD _ _ _)). intros Tx M rho2 HIN HKp2. unfold TsD0M in HIN. cbn [In] in HIN. destruct HIN as [E|[E|[]]]; injection E as <- <-.
  - apply (tr_pure X _ False); [|intros []]. intros [tr [ms md]] Hw. pose proof (jrd_len2 A tmp rho2 tp tr md HI (proj2 Hw)) as LN.
    pose proof (SPA_facts_hold segsA _ rho2 PostQ3R0 tp _ Hw) as HFa.
    assert (F : holds rho2 (SPBranch BC_EQ (SVar 160) (SLit 0))) by (apply (proj1 (Forall_forall _ _) HFa); unfold PostQ3R0, mkR; cbn [ax_S mkA ss_facts]; apply in_or_app; right; left; reflexivity).
    destruct HV1 as (E184 & _). pose proof (proj2 HKp2 160%positive (SVar 184) ltac:(unfold MRET; cbn; tauto)) as E160. cbn [eval] in E160. rewrite E184 in E160.
    cbn [holds branch_taken eval] in F. rewrite E160 in F. unfold bv_eqb in F. apply Z.eqb_eq in F. rewrite !u64_lit in F by lia. destruct tmp; [congruence | cbn [length] in F; lia].
  - pose proof (HVX_keep _ rho1 rho2 tmp HKp2 ltac:(cbn; tauto) HV1) as HV2. destruct tmp as [|b tmp']; [congruence|].
    apply (tr_glue _ (JRD K A0 rho0 A (b :: tmp') rest) DH tp (fun r => HVX r (b :: tmp') /\ HVB r b tmp')).
    + intros w Hw. exact (dh0_glue K HL A0 rho0 A b tmp' rest rho2 tp w I1 I2 I5 Hw HV2).
    + intros r (R1 & R2). apply (dh_step b tmp' A r tp); try assumption.
      intros A' rho3 tp3 HTP3 NE3 HS3 HI3 HV3. exact (dhn_loop tmp' A' rho3 tp3 HTP3 NE3 HI3 HS3 HV3).
Qed.
End DLoop.
End SegQ3D_loop.

(* [comment removed for export] *)
Module SegQ3M_skel.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "qb_addr"; "qb_items"; "qb_size"; "aa_geom"; "aa_q_global"; "ageom"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "prod"; "nil"; "list"; "app"; "nat"; "bool"; "length"; "true"; "false"; "option"; "fst"; "Some"; "S"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "rw"; "sprop"; "eval"; "SLit"; "holds"; "SPBranch"; "SAlu"; "SPNot"; "ss_facts"; "ss_objs"; "SPAlign"; "sprop_eqb"; "SMd"; "obj_range"; "ranges_disjoint"; "rm"; "SPUle"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "iff"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3M_skel"; "V"; "lf"; "ccn"; "ne0"; "HQk"; "XQ"; "csz"; "ohb"; "HSEf"; "all_T"; "f'"; "k'"; "nM"; "otl"; "s'"; "sz13"; "GH"; "Mph"; "TH"; "T_adv"; "T_cp0"; "T_cpn"; "T_mg"; "obh"; "T_cpe"; "T_gh"; "T_gx"; "T_mrg0"; "dstE"; "T_first"; "T_hqk"; "T_m0h"; "T_m0m"; "T_xh0"; "T_xhk"; "T_xq"; "T_xx"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "mul"; "pow"; "sub"; "modulo"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue"; "JRM"; "GI"; "trans"; "mkT"; "dspec"; "emptyb"; "mergeb"; "MMEM"; "diss_res"; "dobj"; "t_Cd"; "carve_cond"; "diss_cond"; "dzone"; "t_C"; "COPIED"; "keepN"; "t_F"; "t_M"; "t_OC"; "t_T"; "t_bs"; "t_k"; "t_ok"; "apart_d"; "emptied"; "isum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3M_skel.Skel"; "HVM"; "mctx"; "c3"; "HVCp"; "dsN"; "HVE"; "HVTq"; "dsG"; "dsSd"; "HVB"; "HVG"; "dsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "qb_dflt"; "qsize"; "qlinks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "cell_ok"; "mkACell"; "present"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep"; "last_addr"; "hd_addr"; "@Stdlib.Lists.List"; "In"; "existsb"; "nth_error"; "ForallOrdPairs"; "forallb"; "hd"; "incl"; "last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "JOK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3M_states"; "LMH"; "MH"; "LM0"; "LMG"; "MG"; "VM"; "LMC"; "MC"; "PM1"; "VMc"; "endC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop"; "HVH"; "benv"; "HVX"; "HVC"; "HVT"; "JRX"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "ZQ"; "PH"; "Headk"; "PM"; "Xg"; "NXR"; "OH"; "SW"; "mkR"; "vK"; "Head0"; "LEXIT"; "LHEAD"; "O_gqH"; "regsH"; "regsX"; "vCUR"; "vJK"; "vJL"; "vN"; "vPRV"; "vS"; "vTF"; "vTS"; "vXF"; "vXK"; "vXL"; "vXS";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "kQuarantineMax"; "HIGH_SHADOW_END"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "BC_EQ"; "BC_GEU"; "BC_LTU"; "ALU_SLL"; "M_MUL"; "ALU_SRL"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel"; "JRQ"; "HVP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "set_q"; "QW"; "batch_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "vmap"; "keepsM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "cells_inside"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "QG"; "DEPTH_R"; "O_gq"; "vGF"; "vGN"; "vGS"; "vMIN"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qitems"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3M_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition lf (l : list axst) (i : nat) : axst := nth i l PM1.
Definition nM (e : bool) : nat := if e then 3%nat else 2%nat.
Definition V (n : positive) : sv := SVar n.
Definition ohb (b n s c : sv) : sobj := ltac2:(tb__ "0|4|
SebVb;Z0M0Z18S7S9S9S17SdA2M1S19A2M2S8G1S19S8S17SdG0U8M3A4Vn;A4S7G2S8G1S19S8S17SdZ8G3A4Vs;A4S7G2S8G1S19S8S17SdZ10G3A4Vc;A4SaG2A1A3A3A3A4").
Definition otl (b x : sv) : sobj := ltac2:(tb__ "0|3|
SebVb;Z0M0Z8S7S9S9S17SdA2M1S19A2M2S8G1S19S8S17SdG0U8A4Vx;A4SaG2A1A3A4").
Definition obh (b n s : sv) : sobj := ltac2:(tb__ "0|4|
SebVb;Z0M0Z10S7S9S9S17SdA2M1S19A2M2S8G1S19S8S17SdG0U8M3A4Vn;A4S7G2S8G1S19S8S17SdZ8G3A4Vs;A4SaG2A1A3A3A4").
Definition ne0 (x : sv) : sprop := ltac2:(tb__ "0|0|
S23S21SddVx;S1fZ0A1A3A1").
Definition sz13 (x : sv) : sprop := ltac2:(tb__ "0|0|
S23S21SddS22Se2Vx;S1fZdA1A3S1fZ0A1A3A1").
Definition GH : list positive := ltac2:(tb__ "0|0|
S7S18PccS7S18PcdS7S18PceS7S18PcfS7S18Pd0SaS18A1A3A3A3A3A3").
Definition TH : list positive := ltac2:(tb__ "0|0|
S7S18Pb8S7S18Pb9S7S18PbaS7S18PbbSaS18A1A3A3A3A3").
Definition HSEf (x : sv) : sprop := ltac2:(tb__ "0|0|
S2cS1fSdbA1Vx;A2").
Definition csz : sv := ltac2:(tb__ "0|0|
Sa7Sa7S34Pa1A1S34Pa5A1A2S1fN2000A1A2").
Definition ccn : sv := add (V 166) (V 162).
Definition k' (e : bool) : sv := ltac2:(tb__ "0|1|
SeS19Le;Ve;Sa7S34Pb8A1S1fZ1A1M0A2G0Xex2").
Definition f' (e : bool) : sv := if e then V 185 else V 163.
Definition s' (e : bool) : sv := ltac2:(tb__ "0|1|
SeS19Le;Ve;Sa7S34PbbA1S1fZ2000A1M0A2G0Xex2").
Definition dstE : sv := ltac2:(tb__ "0|0|
Sa7Sa7S34Pa0A1S22Se0S34Pa2A1S1fZ3A1A3A2S1fZ18A1A2").

Definition T_first : trans := ltac2:(tb__ "0|4|
S6aSc0U0S7S1bS3bSf0S34Pa0M0A1S34Pa1M1A1S34Pa2M2A1A4SaS1bA1A3S7S18G0S7S18G1S7S18G2SaS18A1A3A3A3M3SaS1dA1Sb2Sb5ScS18G3S44A3A1A7").
Definition T_m0h : trans := ltac2:(tb__ "0|8|
S6aS35SacU1M0A2G0S7S1bS4bS34PcdA1M1S34Pc6M2A1M3S34Pc7M4A1M5A3SaS1bA1A3S7S18G2S7S18G4SaS18A1A3A3SaS1dA1Sc7S7S9S18S19A2M6S8S18S19Pa0S34PccA1A4S7G6S8S18S19Pa1G1A4S7G6S8S18S19Pa2S34PceA1A4S7G6S8S18S19Pa3S34PcfA1A4S7G6S8S18S19Pa4G3A4S7G6S8S18S19Pa5G5A4S7G6S8S18S19Pd0M7S34G7A1A4SaG6A1A3A3A3A3A3A3A3A7").
Definition T_m0m : trans := ltac2:(tb__ "0|c|
S6aS35SacU2A2U0S7S1bS3bS34Pa0M0A1M1S34Pc2M2A1M3S34Pc3M4A1M5S34Pc4M6A1M7A4SaS1bA1A3S7S18G2S7S18G4S7S18G6SaS18A1A3A3A3S7S1dS37S34PccA1A1S7S1dS43S34Pa1M8A1M9A1SaS1dA1A3A3SabS11A1ScS9S18S19A2MaS7GaS8S18S19G0S34PcdA1A4S7GaS8S18S19G8G9A4S7GaS8S18S19Pa2MbS34GbA1A4S7GaS8S18S19Pa3G1A4S7GaS8S18S19Pa4G3A4S7GaS8S18S19Pa5G5A4S7GaS8S18S19Pa6G7A4S7GaS8S18S19Pa7SbdA4SaGaA1A3A3A3A3A3A3A3A3Sb5S44A1A3A7").
Definition T_adv (e : bool) : trans := ltac2:(tb__ "0|12|
S6aS35SaaVe;A1U2A2S40Ve;A1ScS1bS7S1bS3bS34Pa3M0A1M1S34Pa4M2A1M3S34Pa5M4A1M5S34Pa6M6A1M7A4S7S1bS3bG3S34Pc2M8A1M9S34Pc3MaA1MbS34Pc4McA1MdA4SaS1bA1MeA3A3SeSbS1bA1Le;Ve;S7S1bS41S34PbaA1SbdA2GeA3GeXex2A3S7S18G8S7S18GaS7S18GcSaS18A1A3A3A3S7S1dS43G5A1SaS1dA1A3SabVe;A1ScS9S18S19A2MfS7GfS8S18S19Pa0G1A4S7GfS8S18S19Pa1G5A4S7GfS8S18S19Pa2G7A4S7GfS8S18S19G0G3A4S7GfS8S18S19G2G9A4S7GfS8S18S19G4GbA4S7GfS8S18S19G6GdA4S7GfS8S18S19Pa7M10S34G10A1A4SaGfA1M11A3A3A3A3A3A3A3A3ScGfSb5S44A1SeSbGfA1Le;Ve;Sb5S46A1G11Xex2A3A3A7").
Definition T_mrg0 (e : bool) : trans := ltac2:(tb__ "0|0|
S6aS35SaaVe;A1U3A2U0SaS1bA1SaS18A1SaS1dA1SaeVe;A1Sb5SafVe;A1A1A7").
Definition T_cp0 (e : bool) : trans := ltac2:(tb__ "0|4|
S6aS35SaaVe;A1U4A2U0S7S1bS41Sa7S34Pa3A1S1fZ18A1A2M0S34PbdM1A1M2A2S7S1bSebS50Z0Z8SaS9S9S17SdA2S19A2A1A4SaS1bA1A3A3S7S18G1SaS18A1A3SaS1dA1Sb1Ve;A1ScS9S18S19A2M3Sb5SafVe;A1A1S7G3S8S18S19Pa9G0A4S7G3S8S18S19PaaS50A4S7G3S8S18S19PbcG2A4SaG3A1A3A3A3A3A7").
Definition T_cpn (e : bool) : trans := ltac2:(tb__ "0|9|
S6aS35Sb0Ve;A1U0A2U2S7S1bS41Sa7S34Pa9M0A1S1fZ8M1A1M2A2M3S34PbdM4A1M5A2S7S1bSebSa7S34PaaM6A1G2A2M7Z0G1SaS9S9S17SdA2S19A2A1A4SaS1bA1A3A3S7S18G4SaS18A1A3SaS1dA1Sb1Ve;A1ScS9S18S19A2M8Sb5SafVe;A1A1S7G8S8S18S19G0G3A4S7G8S8S18S19G6G7A4S7G8S8S18S19PbcG5A4SaG8A1A3A3A3A3A7").
Definition T_cpe (e : bool) : trans := ltac2:(tb__ "0|0|
S6aS35Sb0Ve;A1U1A2U2SaS1bA1SaS18A1SaS1dA1SaeVe;A1Sb5SafVe;A1A1A7").
Definition T_mg (e : bool) : trans := ltac2:(tb__ "0|16|
S6aS35SadVe;A1U3A2S40Ve;A1S7S1bS3bS34Pa0M0A1M1S34Pa4M2A1M3S3aS36A4S7S1bS3bG3S34Pc2M4A1M5S34Pc3M6A1M7S34Pc4M8A1M9A4S7S1bS41S34Pa3MaA1MbSbdA2SaS1bA1A3A3A3S7S18G4S7S18G6S7S18G8SaS18A1A3A3A3ScS1dS7S1dS37Sa7S34PccMcA1S1fN1A1A2MdA1S7S1dS43S3aA1SaS1dA1MeA3A3SeSbS1dA1Le;Ve;S7S1dS37S3fVe;A1MfA1GeA3GeXex2A3SabS10A1S7S9S18S19A2M10S8S18S19G0G1A4S7G10S8S18S19Pa1S3aA4S7G10S8S18S19Pa2S36A4S7G10S8S18S19GaG3A4S7G10S8S18S19G2G5A4S7G10S8S18S19Pa5G7A4S7G10S8S18S19Pa6G9A4S7G10S8S18S19Pa7M11Sa7S34G11A1S1fZ2000A1A2A4S7G10S8S18S19GcGdA4S7G10S8S18S19PcdM12S34G12A1A4S7G10S8S18S19PceM13S34G13A1A4S7G10S8S18S19PcfM14S34G14A1A4S7G10S8S18S19Pd0M15S34G15A1A4S7G10S8S18S19Pb8GfA4S7G10S8S18S19Pb9S3eVe;A1A4S7G10S8S18S19PbaGbA4S7G10S8S18S19PbbS42Ve;A1A4SaG10A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A7").

Definition HQk : axst := ltac2:(tb__ "0|0|
Sc5Sc9ScbScdSc6Sd1A3Sc3Sc4SceSd3ScfSd4A4A1S7S1bScaSaS1bA1A3ScS1dSf9SeeA1S7S1dS37Sd0A1S7S1dS23S21SdeSf3Sd2A3A1S7S1dS37Sc6A1SaS1dA1A3A3A3A3Sc2A6").
Definition XQ : axst := ltac2:(tb__ "0|0|
Sc5Sc8SccSc3Sc4Sd6Sd5Sd7Sd8A4A1S7S1bSefS34Pa0A1S34Pa1A1S34Pa2A1S34Pa3A1A4SaS1bA1A3Sf9SeeA1Sc2A6").
Definition Mph (n l s : sv) : vmap := ltac2:(tb__ "0|2|
S7S9S18S19A2M0S8S18S19Pa0Vn;A4S7G0S8S18S19Pa1S34PcdA1A4S7G0S8S18S19Pa2Vl;A4S7G0S8S18S19Pa3Vs;A4S7G0S8S18S19Pd0M1S34G1A1A4SaG0A1A3A3A3A3A3").
Definition T_xh0 : trans := ltac2:(tb__ "0|1|
S6aS35SaaS11A1U1A2U2SaS1bA1SaS18A1S7S1dS3cS34PcdM0A1A1S7S1dS26G0Z3A2SaS1dA1A3A3SbeS45S34PccA1S34PceA1S22SdcS34PcfA1S34Pa7A1A3A3A7").
Definition T_xhk : trans := ltac2:(tb__ "0|3|
S6aS35SaaS10A1U1A2U3SaS1bA1SaS18A1SaS1dA1S38ScS9S18S19A2M0S45S34PccA1S34PceA1S22SdcS34PcfA1S34Pa7A1A3A3S7G0S8S18S19Pa6S34PbaA1M1A4S7G0S8S18S19Pa8S34Pb8A1M2A4S7G0S8S18S19Pa9S34Pb9A1A4S7G0S8S18S19PaaS34PbbA1A4S7G0S8S18S19Pc0G2A4S7G0S8S18S19Pc1G1A4SaG0A1A3A3A3A3A3A3A3A7").
Definition T_gh (e : bool) : trans := ltac2:(tb__ "0|5|
S6aS35SadVe;A1U2A2S40Ve;A1SaS1bA1SaS18A1ScS1dS7S1dS37Sa7S34PccA1S1fN1A1A2M0A1SaS1dA1M1A3SeSbS1dA1Le;Ve;S7S1dS37S3fVe;A1M2A1G1A3G1Xex2A3S38ScS9S18S19A2M3S45G0S34Pa0A1S22SdcS34PcfA1Sa7S34Pa7A1S1fZ2000A1A2A3A3S7G3S8S18S19Pa6S34Pa3A1M4A4S7G3S8S18S19Pa8G2A4S7G3S8S18S19Pa9S3eVe;A1A4S7G3S8S18S19PaaS42Ve;A1A4S7G3S8S18S19Pc0G2A4S7G3S8S18S19Pc1G4A4SaG3A1A3A3A3A3A3A3A3A7").
Definition T_hqk : trans := ltac2:(tb__ "0|c|
S6aS38U0S7S1bS4bS34Pa1M0A1M1S34Pc6M2A1M3S34Pc7M4A1M5A3S7S1bS4bS34Pa6M6A1M7SbdS1fZ2000A1M8A3SaS1bA1A3A3S7S18G2S7S18G4SaS18A1M9A3A3S7S1dS3cG1A1S7S1dS26G0Z3MaA2S7S1dS3cG7A1S7S1dS26G6GaA2SaS1dA1A3A3A3A3SbfScS9S18S19A2MbSb5S7S18Pa0S7S18G0S7S18Pa2S7S18Pa3S7S18G6S7S18Pa8S7S18Pa9S7S18PaaS7S18Pc0S7S18Pc1S7S18Pd0G9A3A3A3A3A3A3A3A3A3A3A3A1S7GbS8S18S19Pa4G3A4S7GbS8S18S19Pa5G5A4S7GbS8S18S19Pa7G8A4SaGbA1A3A3A3A3A7").
Definition T_xx : trans := ltac2:(tb__ "0|2|
S6aS35SaaS10A1U0A2U3SaS1bA1SaS18A1M0SaS1dA1S39ScS9S18S19A2M1S7G1S8S18S19Pa0S34PccA1A4S7G1S8S18S19Pa1S34PcdA1A4S7G1S8S18S19Pa2S34PceA1A4S7G1S8S18S19Pa3S22SdcS34PcfA1S34Pa7A1A3A4SaG1A1A3A3A3A3Sb5ScS18S46S7S18Pd0G0A3A3A1A3A7").
Definition T_gx (e : bool) : trans := ltac2:(tb__ "0|4|
S6aS35SadVe;A1U1A2S40Ve;A1SaS1bA1SaS18A1SaS1dA1S39S7S9S18S19A2M0S8S18S19Pa0M1Sa7S34PccA1S1fN1A1A2A4S7G0S8S18S19Pa1S34PcdA1A4S7G0S8S18S19Pa2S34G1A1A4S7G0S8S18S19Pa3M2S22SdcS34PcfA1Sa7S34Pa7A1S1fZ2000A1A2A3A4S7G0S8S18S19Pb8S3fVe;A1A4S7G0S8S18S19Pb9S3eVe;A1A4S7G0S8S18S19PbaS34G2A1A4S7G0S8S18S19PbbS42Ve;A1A4S7G0S8S18S19Pd0M3S34G3A1A4SaG0A1A3A3A3A3A3A3A3A3A3A7").
Definition T_xq : trans := ltac2:(tb__ "0|1|
S6aS39U1SaS1bA1SaS18A1M0SaS1dA1Sc1Sb5ScS18S46S7S18Pd0G0A3A3A1A7").

Definition all_T : list trans := ltac2:(tb__ "0|0|
S7S69S51S7S69S53S7S69S54S7S69S47S10A1S7S69S47S11A1S7S69S4fS10A1S7S69S4fS11A1S7S69S48S10A1S7S69S48S11A1S7S69S49S10A1S7S69S49S11A1S7S69S4cS10A1S7S69S4cS11A1S7S69S4aS10A1S7S69S4aS11A1S7S69S55S7S69S56S7S69S58S7S69S4dS10A1S7S69S4dS11A1S7S69S4eS10A1S7S69S4eS11A1S7S69S52S7S69S57SaS69A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Lemma all_T_ok : ltac2:(tb__ "0|0|
S2dSeS9eS69S7eS3dA3S10A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma T_ok : ltac2:(tb__ "0|0|
S69S9aS69R1S3dA3S2dSeS7eR2A1S10A3F_;Ft;"). Proof. exact (proj1 (forallb_forall _ _) all_T_ok). Qed.

Lemma eval_sllk : ltac2:(tb__ "0|5|
S1aS19S17S17S2dS5aQ40M0A1M1S1eR4R3A2S59G0R2A2A3S5fZ0R3A2M2S2eG2S61R3Z40M3A2A2S61S62R5S63Z2M4R4A2A2S63G4G3A2A2S2dG1S1eR8S22Se0R7S1fR5A1A3A2S59G0S62R6S63G4R5A2A2A2A3F_;F_;F_;F_;Fk;Fx;Fa;Frho;").
Proof. intros rho a x k Ea Hx Hk Hs. apply bv_eq. rewrite U_sllk by lia. rewrite Ea, !u64_lit by lia. apply Z.mod_small. lia. Qed.
Lemma eval_addl : ltac2:(tb__ "0|7|
S1aS19S17S17S2dS5aQ40M0A1M1S1eR4R3A2S59G0R2A2A3S2eS5fZ0M2R3A2S61R3S63Z2M3Z40A2M4A2A2S2eS5fS66S63G3Z3fA2M5A1R3A2S61R3G5A2A2S2eS5fG2S5eR5R4A2M6A2S61G6G4A2A2S2dG1S1eR8Sa7R7S1fR5A1A2A2S59G0S5eR6R5A2A2A3F_;F_;F_;F_;Fk;Fx;Fa;Frho;").
Proof.
  intros rho a x k Ea Hx Hk Hs. apply bv_eq. unfold add. cbn [eval]. rewrite add_val, Ea, (u64_lit x), (u64_lit (x + k)) by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.
Lemma eval_subz : ltac2:(tb__ "0|3|
S1aS19S19S17S17S2dS5aQ40M0A1M1S1eR5R4A2S59G0R2A2M2A3S2dG1S1eR6R4A2G2A3S2eS5fZ0R3A2S5fR3R4A2A2S61R5S63Z2Z40A2A2S2dG1S1eR9S22SdcR8R7A3A2S59G0S64R6R5A2A2A3F_;F_;F_;F_;Fy;Fx;Fb;Fa;Frho;").
Proof. intros rho a b x y Ea Eb Hy Hx. apply bv_eq. cbn [eval]. rewrite sub_val, Ea, Eb, !u64_lit by lia. apply Z.mod_small. lia. Qed.
Lemma sz13_holds : ltac2:(tb__ "0|1|
S1aS19S17S2dS5aQ40M0A1S1eR3R2A2S59G0R1A2A3S2eS5fZ2000R2A2S61R2S63Z2Z40A2A2A2S20R5S43R4A1A2F_;F_;Fx;Fa;Frho;").
Proof.
  intros rho a x Ea Hx. unfold sz13. cbn [holds branch_taken eval]. intros E. unfold bv_eqb in E. apply Z.eqb_eq in E. rewrite srl_val, Ea, !u64_lit in E by lia.
  change (13 mod 64) with 13 in E. rewrite Z.shiftr_div_pow2 in E by lia. assert (1 <= x / 2 ^ 13) by (apply Z.div_le_lower_bound; lia). lia.
Qed.
Lemma ne0_holds : ltac2:(tb__ "0|1|
S1aS19S17S2dS5aQ40M0A1S1eR3R2A2S59G0R1A2A3S2eS61Z0R2A2S61R2S63Z2Z40A2A2A2S20R5S37R4A1A2F_;F_;Fx;Fa;Frho;").
Proof. intros rho a x Ea Hx. unfold ne0. cbn [holds branch_taken eval]. intros E. unfold bv_eqb in E. apply Z.eqb_eq in E. rewrite Ea, !u64_lit in E by lia. lia. Qed.
Lemma HSE_holds : ltac2:(tb__ "0|1|
S1aS19S17S2dS5aQ40M0A1S1eR3R2A2S59G0R1A2A3S2eS5fSdbR2A2S61R2S63Z2Z40A2A2A2S20R5S3cR4A1A2F_;F_;Fx;Fa;Frho;").
Proof. intros rho a x Ea Hx. unfold HSEf. cbn [holds eval]. rewrite Ea, !u64_lit by (unfold HIGH_SHADOW_END in *; lia). lia. Qed.
Lemma align3_holds : ltac2:(tb__ "0|2|
S1aS18S17S2dS5aQ40M0A1S1cR3R2A2S59G0R1A2A3S2eS5fZ0M1R2A2S61R2S63Z2Z40A2A2A2S2dS17S65R3Z2000A2G1A3S20R6S26R5Z3A2A2F_;F_;F_;Fa;Fv;Frho;").
Proof.
  intros rho v a Ev Ha Hm. cbn [holds]. split; [lia|]. rewrite Ev, u64_lit by lia. pose proof (Z.div_mod a 8192 ltac:(lia)) as D. rewrite Hm, Z.add_0_r in D. rewrite D.
  replace (8192 * (a / 8192)) with (1024 * (a / 8192) * 2 ^ 3) by lia. apply Z.mod_mul. lia.
Qed.
Lemma cell_present : ltac2:(tb__ "0|0|
S93S17SdS17S94R4S95R3R2R1A3A2S96R5R4S5eR4S60R3A1A2A3F_;Fval;Fk;Fa;Fm;").
Proof. intros m a k val H z Hz. pose proof (H (Z.to_nat (z - a)) ltac:(cbn; lia)) as X. cbn [c_addr c_w RtCells.c_val] in X. replace (a + Z.of_nat (Z.to_nat (z - a))) with z in X by lia. eexists. exact X. Qed.
Lemma cell_pr : ltac2:(tb__ "0|0|
S93S17SdS17S17S94R5S95R4R3R2A3A2S2dS17R2S5eR5S60R4A1A2A3S96R7R6R3A3F_;F_;Fhi;Fval;Fk;Fa;Fm;").
Proof. intros m a k val hi H ->. exact (cell_present m a k val H). Qed.
Lemma present_app : ltac2:(tb__ "0|0|
S93S17S17S17S96R4R3R2A3S96R5R3R2A3S96R6R5R3A3F_;F_;Fc;Fb;Fa;Fm;").
Proof. intros m a b c H1 H2 z Hz. destruct (Z_lt_dec z b); [apply H1; lia | apply H2; lia]. Qed.
Lemma glob_link : ltac2:(tb__ "0|1|
S93SbS0A1M0S0G0S92R4ScS0R3S7S0R2R1A3A3A2S94R5S95S1R3A1U8S99R2A1A3A2F_;FR;Fb;FD;Fv;").
Proof.
  intros v D b R H. apply qlinks_to_0 in H. destruct (qlinks_to_split v D (b :: R) 0 ltac:(discriminate) H) as [_ H2]. cbn [qlinks_to] in H2. destruct H2 as [H2 _].
  destruct R as [|r R']; exact H2.
Qed.
Lemma qsize_ge0 : ltac2:(tb__ "0|1|
SbS0A1Sa4S0S0S5fZ0M0S3R1A1A2Lb;R1A3S5fG0S91R2A1A2F_;Fl;").
Proof. intros l H. induction H as [|b r Hb HR IH]; [cbn; lia | rewrite qsize_cons; lia]. Qed.
Lemma isum_ge0 : ltac2:(tb__ "0|2|
SbS9S17S17A2M0A1Sa4G0G0S5fZ0M1S16S17S17R1A3A2Lit;R1A3S5fG1S81R2A1A2F_;Fl;").
Proof. intros l H. unfold isum. induction H as [|b r Hb HR IH]; cbn [fold_right]; lia. Qed.
Lemma MMEM_ext : ltac2:(tb__ "0|1|
S93S93S6SbS0A1M0G0S17S2dS12S5aQ8A1A1R5R1A1R6R1A1A3Fz;S6eR6R4R3R2A4S6eR6R5R4R3A4F_;F_;Fglob;FE;FG;Fv3;Fv;").
Proof. intros v v3 G E glob H HM. assert (E3 : v3 = v) by (apply functional_extensionality; exact H). rewrite E3. exact HM. Qed.

Section Skel.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation) (A1 : AA).
Hypothesis HTH : aa_q_thread A1 = [].
Hypothesis HCI : aa_cache_inited A1 = true.
Hypothesis HQW : ltac2:(tb__ "0|0|
S17Se7VA1;R1A2Se7VA0;R2A2F_;Fz;").
Let all := aa_q_global A1.
Hypothesis HSZ : qsize all < 2 ^ 50.
Notation JRM := (JRM K A0 rho0 A1).

Definition HVG (rho : valuation) (glob : list qbatch) : Prop := ltac2:(tb__ "0|2|
S2eS2dS5aQ40M0A1M1S1cVrho;PccA2S59G0S60SfS0Vglob;A2A1A2A3S2eS2dG1S1cVrho;PcdA2S59G0S99Vglob;A1A2A3S2eS2dG1S1cVrho;PceA2S59G0S98Vglob;A1A2A3S2eS2dG1S1cVrho;PcfA2S59G0S91Vall;A1A2A3S2dG1S1cVrho;Pd0A2S59G0Sd9A2A3A2A2A2A2").
Definition HVE (e : bool) (rho : valuation) (E : list qbatch) : Prop := ltac2:(tb__ "0|3|
S2eS2dS5aQ40M0A1M1S1cVrho;Pa7A2S59G0S91VE;A1A2M2A3S2eS32S2dSeVe;S11A3S2dSbS0A1VE;SaS0A1A3A2S2dSeVe;S10A3S2eS2dG1S1cVrho;Pb8A2S59G0S60SfS0VE;A2A1A2A3S2eS2dG1S1cVrho;Pb9A2S59G0S99VE;A1A2A3S2eS2dG1S1cVrho;PbaA2S59G0S98VE;A1A2A3S2dG1S1cVrho;PbbA2G2A3A2A2A2F_;A2A2").
Definition HVB (rho : valuation) (c n : qbatch) (L : list qbatch) : Prop := ltac2:(tb__ "0|3|
S2eS2dS5aQ40M0A1M1S1cVrho;Pa0A2S59G0S1Vc;A1A2A3S2eS2dG1S1cVrho;Pa1A2S59G0S3Vc;A1A2A3S2eS2dG1S1cVrho;Pa2A2S59G0S60SfS9S17S17A2M2S2Vc;A1A2A1A2A3S2eS2dG1S1cVrho;Pa3A2S59G0S1Vn;A1A2A3S2eS2dG1S1cVrho;Pa4A2S59G0S99VL;A1A2A3S2eS2dG1S1cVrho;Pa5A2S59G0S3Vn;A1A2A3S2dG1S1cVrho;Pa6A2S59G0S60SfG2S2Vn;A1A2A1A2A3A2A2A2A2A2A2").
Definition HVM (e : bool) (rho : valuation) (E D : list qbatch) (c n : qbatch) (L : list qbatch) : Prop := ltac2:(tb__ "0|0|
S2eS8eVrho;ScS0VD;S7S0Vc;S7S0Vn;VL;A3A3A3A2S2eS89Ve;Vrho;VE;A3S8dVrho;Vc;Vn;VL;A4A2A2").

Lemma HVM_vals : ltac2:(tb__ "0|1|
SeS1aS1aSbS0A1M0G0S0S0G0S18S9aS18R1SafR9A1A3S2dS5aQ40A1S1cR8R2A2S1cR9R2A2A3F_;Fv;S84R9R8R6R5R4R3R2A7S84RaR8R7R6R5R4R3A7F_;F_;FL;Fn;Fc;FD;FE;Frho';Frho;Fe;").
Proof.
  intros e rho rho' E D c n L KV ((G1 & G2 & G3 & G4 & G5) & (E1 & E2 & E3) & (B1 & B2 & B3 & B4 & B5 & B6 & B7)).
  assert (KB : forall v, In v [160; 161; 162; 163; 164; 165; 166; 167; 204; 205; 206; 207; 208]%positive -> rw rho' v = rw rho v).
  { intros v Hv. apply KV. unfold VM. apply in_or_app. left. exact Hv. }
  split; [|split].
  - unfold HVG. rewrite !KB by (cbn; tauto). tauto.
  - unfold HVE. rewrite KB by (cbn; tauto). split; [exact E1|]. split; [exact E2|]. intros He. subst e. specialize (E3 eq_refl).
    rewrite !KV by (unfold VM; apply in_or_app; right; cbn; tauto). exact E3.
  - unfold HVB. rewrite !KB by (cbn; tauto). tauto.
Qed.
Lemma HVM_keep : ltac2:(tb__ "0|1|
SeS1aS1aSbS0A1M0G0S0S0G0SbS18A1SeaSb5R1A1R8R7A3Sa0S18SafRaA1R2A3S84RbRaR8R7R6R5R4A7S84RcRaR9R8R7R6R5A7F_;F_;F_;Fl;FL;Fn;Fc;FD;FE;Frho';Frho;Fe;").
Proof. intros e rho rho' E D c n L l HKp HIN HV. apply (HVM_vals e rho rho'); [|exact HV]. intros v Hv. apply (keepsM_id l rho rho' v HKp). apply HIN. exact Hv. Qed.

Record mctx (v : bview) (rho : valuation) (E D : list qbatch) (c n : qbatch) (L : list qbatch) : Prop := mkMC {
  mc_be : benv A1 rho;
  mc_in : forall b, In b (E ++ D ++ c :: n :: L) -> In (qb_addr b) (map qb_addr all);
  mc_nd : NoDup (map qb_addr (E ++ D ++ c :: n :: L));
  mc_sz : forall b, In b (E ++ D ++ c :: n :: L) -> 8192 <= qb_size b;
  mc_sum : qb_size c + qb_size n + qsize E <= qsize all;
  mc_cap : forall b, In b (E ++ D ++ c :: n :: L) -> Z.of_nat (length (qb_items b)) <= 1021;
  mc_len : 8192 * Z.of_nat (length (D ++ c :: n :: L)) <= qsize all;
  mc_E : qsize E = 8192 * Z.of_nat (length E);
  mc_c0 : cell_ok v (mkACell (qb_addr c) 8 (qb_addr n)); mc_c1 : cell_ok v (mkACell (qb_addr c + 8) 8 (qb_size c));
  mc_c2 : cell_ok v (mkACell (qb_addr c + 16) 8 (Z.of_nat (length (qb_items c))));
  mc_n0 : cell_ok v (mkACell (qb_addr n) 8 (hd_addr L)); mc_n1 : cell_ok v (mkACell (qb_addr n + 8) 8 (qb_size n));
  mc_n2 : cell_ok v (mkACell (qb_addr n + 16) 8 (Z.of_nat (length (qb_items n))));
  mc_l0 : E <> [] -> cell_ok v (mkACell (last_addr E) 8 0)
}.

Lemma item_size_pos : ltac2:(tb__ "0|1|
S1aS9S17S17A2M0Sb7VA1;R2A2S9aG0R2SfcVall;A1A3S5fZ1S16S17S17R3A3A2F_;F_;Fit;Frho;").
Proof.
  intros rho it BE Hit. pose proof (proj1 (be_qp _ _ BE)) as HBP. rewrite (qall_A1 A1 HTH) in HBP. unfold all, qitems in Hit. apply in_flat_map in Hit as (b & Hb & Hit).
  pose proof (proj1 (Forall_forall _ _) HBP b Hb) as (_ & _ & _ & HIP). exact (proj1 (proj2 (proj1 (Forall_forall _ _) HIP it Hit))).
Qed.
Lemma qsize_in : ltac2:(tb__ "0|0|
SbS0A1S0Sa4S0S0S5fZ0S3R1A1A2Lb;R2A3S9aS0R2R3A3S5fS3R3A1S91R4A1A2F_;F_;Fb;Fl;").
Proof.
  intros l b H. induction H as [|x r Hx HR IH]; intros Hb; [destruct Hb|]. rewrite qsize_cons. pose proof (qsize_ge0 r HR). destruct Hb as [<-|Hb]; [lia | specialize (IH Hb); lia].
Qed.
Lemma qsize_len : ltac2:(tb__ "0|1|
SbS0A1Sa4S0S0S5fZ2000M0S3R1A1A2Lb;R1A3S5fS62G0S60SfS0R2A2A1A2S91R2A1A2F_;Fl;").
Proof. intros l H. induction H as [|x r Hx HR IH]; [cbn; lia | rewrite qsize_cons; cbn [length]; lia]. Qed.
Lemma qsize_emptied : ltac2:(tb__ "0|0|
SbS0A1Sa4S0S80R1A3S2dS17S91R2A1S62Z2000S60SfS0R2A2A1A2A3F_;Fl;").
Proof. intros l H. induction H as [|x r [_ Hx] HR IH]; [reflexivity | rewrite qsize_cons, IH, Hx; unfold kQuarantineBatchSize; cbn [length]; lia]. Qed.

Lemma mctx_of : ltac2:(tb__ "0|1|
SbS0A1M0G0S0S0G0SdS1aSbS5aQ40A1A1SbSf7A1Sf6S67VK;VA0;Vrho0;VA1;RaScS0R9S7S0R8S7S0R7R6A3A3A3R8R7R5R4R3R2R1AdS68Vall;RbScS0RaS7S0R9S7S0R8R7A3A3A3A3S85S97S5bS2bR6A1A2R6RcRbRaR9R8A7F_;F_;Fmd;Ftr;Ftp;Frho;Fj;FL;Fn;Fc;FD;FE;").
Proof.
  intros E D c n L j rho tp tr md (HK & ((HBM & HLE & HLG & HTD) & _) & _) HGI.
  pose proof (benv_of_K K HL A1 HCI rho tp tr md HK) as BE.
  assert (SZ : forall b, In b (E ++ D ++ c :: n :: L) -> 8192 <= qb_size b).
  { intros b Hb. pose proof (proj1 (Forall_forall _ _) HBM b Hb) as (_ & _ & H3 & _). fold (isum (qb_items b)) in H3. unfold kQuarantineBatchSize in H3.
    assert (0 <= isum (qb_items b)); [|lia]. apply isum_ge0. apply Forall_forall. intros it Hit.
    pose proof (item_size_pos rho it BE (GI_item A1 E _ b it HGI Hb Hit)). lia. }
  assert (SZ0 : Forall (fun b => 0 <= qb_size b) (E ++ D ++ c :: n :: L)) by (apply Forall_forall; intros b Hb; specialize (SZ b Hb); lia).
  pose proof HGI as (P1 & P2 & FC & FE & QS).
  assert (INC : In c (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  assert (INN : In n (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  split.
  - exact BE.
  - intros b Hb. exact (GI_addr A1 E _ b HGI Hb).
  - exact (GI_nodup A1 HTH rho E _ BE HGI).
  - exact SZ.
  - rewrite <- QS. rewrite !qsize_app, !qsize_cons. apply Forall_app in SZ0 as [S1 S2]. apply Forall_app in S2 as [S2 S3]. inversion S3 as [|? ? _ S4]; subst. inversion S4 as [|? ? _ S5]; subst.
    pose proof (qsize_ge0 _ S2). pose proof (qsize_ge0 _ S5). lia.
  - intros b Hb. pose proof (proj1 (Forall_forall _ _) FC b Hb) as X. unfold capb, kQuarantineBatchCount in X. exact X.
  - rewrite <- QS, qsize_app. pose proof (qsize_ge0 E ltac:(apply Forall_app in SZ0 as [S1 _]; exact S1)).
    assert (X : 8192 * Z.of_nat (length (D ++ c :: n :: L)) <= qsize (D ++ c :: n :: L)); [|lia]. apply qsize_len. apply Forall_forall. intros b Hb. apply SZ. apply in_or_app. right. exact Hb.
  - exact (qsize_emptied E FE).
  - pose proof (glob_link _ D c (n :: L) HLG) as X. exact X.
  - exact (proj1 (proj1 (Forall_forall _ _) HBM c INC)).
  - exact (proj1 (proj2 (proj1 (Forall_forall _ _) HBM c INC))).
  - replace (D ++ c :: n :: L) with ((D ++ [c]) ++ n :: L) in HLG by (rewrite <- app_assoc; reflexivity). exact (glob_link _ (D ++ [c]) n L HLG).
  - exact (proj1 (proj1 (Forall_forall _ _) HBM n INN)).
  - exact (proj1 (proj2 (proj1 (Forall_forall _ _) HBM n INN))).
  - intros NE. rewrite (app_removelast_last qb_dflt NE) in HLE. exact (glob_link _ (removelast E) (last E qb_dflt) [] HLE).
Qed.

Definition c3 (x y z : sv) : list (Z * nat * sv) := ltac2:(tb__ "0|3|
S7S9S9S17SdA2M0S19A2M1S8G0S19S8S17SdZ0U8M2A4Vx;A4S7G1S8G0S19S8S17SdZ8G2A4Vy;A4S7G1S8G0S19S8S17SdZ10G2A4Vz;A4SaG1A1A3A3A3").

Definition dsN (e : bool) (ac an al : Z) : list dspec := ltac2:(tb__ "0|b|
ScS9S9S9S9S19S17A2M0S17A2M1SbS9S9S17SdA2M2S19A2M3A1M4A2M5S17A2M6S7G6S8G5S17S8G1G4S8G0S17S8S19S17S34Pa0A1Z0M7A4Z18M8A4S86S34Pa3A1M9S34Pa1A1S34Pa2A1A3A4Vac;A4S7G6S8G5S17S8G1G4S8G0S17S8S19S17G9G7A4G8A4S86S34Pa4A1S34Pa5A1S34Pa6A1A3A4Van;A4SaG6A1MaA3A3SeSbG6A1Le;Ve;S7G6S8G5S17S8G1G4S8G0S17S8S19S17S34PbaA1G7A4Z8A4S7G3S8G2S19S8S17SdG7U8A4SbdA4SaG3A1A3A4Val;A4GaA3GaXex2A3").

Lemma rw_sets_absorb : ltac2:(tb__ "0|2|
S1aSbS1bA1Sf8SbS9S18S5aQ40A1M0A2M1A1S18S30S9aS18R1Sa5G1S18S13S18G0A2R2A4A3A1S2dG0S1cSfbSfaR6R5R4A3R3A2R2A2S1cR6R2A2A3F_;Fi;Fbs;Fms;FR;Frho;").
Proof. intros rho R ms bs i Hi. rewrite rho_sets_other by exact Hi. reflexivity. Qed.
Lemma e_ne : ltac2:(tb__ "0|1|
SeS1aSbS0A1M0S89R3R2R1A3S2dSeR4S10A3S30S2dG0R3SaS0A1A3A1F_;F_;FE;Frho;Fe;").
Proof. intros e rho E (_ & [H1 H2] & _) He NE. subst e. specialize (H2 NE). discriminate. Qed.
Lemma in_last_E : ltac2:(tb__ "0|1|
SbS0A1M0G0S30S2dG0R2SaS0A1A3A1S9aS0Sa1S0R3S90A3ScS0R3R2A3A3F_;Fl;FE;").
Proof. intros E l NE. apply in_or_app. left. apply In_last. exact NE. Qed.

Lemma hdr_cond : ltac2:(tb__ "0|6|
S1aS19S17SbS9S9S17SdA2S19A2A1M0S2dS5aQ40M1A1S1eR4R3A2S59G1R2A2A3Sb7VA1;R5A2S9aS17R4Sa5S0S17S1Vall;A4A3SecZ0M2Z18M3R4A3S73VA1;R8S8S9S9S9S19S17A2M4S17A2M5G0A2S17S8G5G0S8G4S17S8S19S17R7G2A4G3A4R5A4R6A4A3F_;F_;F_;F_;Fcs;Fa;Fb;Frho;").
Proof.
  intros rho b a cs Eb BE Ha CI. destruct (addr_facts A1 HTH rho a BE Ha) as (F1 & F2 & F3 & F4 & F5). unfold diss_cond.
  split; [exact Eb|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact CI|]. intros z Hz. apply (addr_in_QW A1 HTH rho a z BE Ha). lia.
Qed.
Lemma lnk_cond : ltac2:(tb__ "0|6|
S1aS19S17SbS9S9S17SdA2S19A2A1M0S2dS5aQ40M1A1S1eR4R3A2S59G1R2A2A3Sb7VA1;R5A2S9aS17R4Sa5S0S17S1Vall;A4A3SecZ0M2Z8M3R4A3S73VA1;R8S8S9S9S9S19S17A2M4S17A2M5G0A2S17S8G5G0S8G4S17S8S19S17R7G2A4G3A4R5A4R6A4A3F_;F_;F_;F_;Fcs;Fa;Fb;Frho;").
Proof.
  intros rho b a cs Eb BE Ha CI. destruct (addr_facts A1 HTH rho a BE Ha) as (F1 & F2 & F3 & F4 & F5). unfold diss_cond.
  split; [exact Eb|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact CI|]. intros z Hz. apply (addr_in_QW A1 HTH rho a z BE Ha). lia.
Qed.
Lemma ci3 : ltac2:(tb__ "0|0|
S19S19S19SecZ0Z18S86R3R2R1A3A3Fz;Fy;Fx;"). Proof. intros. unfold cells_inside, c3. repeat constructor; cbn; lia. Qed.
Lemma ci1 : ltac2:(tb__ "0|3|
S19SecZ0M0Z8S7S9S9S17SdA2M1S19A2M2S8G1S19S8S17SdG0U8A4R1A4SaG2A1A3A3Fx;"). Proof. intros. unfold cells_inside. repeat constructor; cbn; lia. Qed.

Lemma dsN_cond : ltac2:(tb__ "0|1|
SeS93S1aSbS0A1M0G0S0S0G0S85R7R6R5R4R3R2R1A7S84R9R7R6R5R4R3R2A7Sa4S6bS73VA1;R8A2S88RaS1R5A1S1R4A1S98R7A1A4A3F_;F_;FL;Fn;Fc;FD;FE;Frho;Fv;Fe;").
Proof.
  intros e v rho E D c n L MC (HG & HE & (B160 & B161 & B162 & B163 & _)). pose proof (mc_be _ _ _ _ _ _ _ MC) as BE.
  assert (INC : In c (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  assert (INN : In n (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  unfold dsN. apply Forall_app. split.
  - constructor; [apply hdr_cond; [exact B160 | exact BE | exact (mc_in _ _ _ _ _ _ _ MC c INC) | apply ci3]|].
    constructor; [apply hdr_cond; [exact B163 | exact BE | exact (mc_in _ _ _ _ _ _ _ MC n INN) | apply ci3] | constructor].
  - destruct e; [|constructor]. pose proof (e_ne _ _ _ HE eq_refl) as NE. destruct HE as (_ & _ & HE). destruct (HE eq_refl) as (_ & _ & E186 & _).
    constructor; [|constructor]. apply lnk_cond; [exact E186 | exact BE | exact (mc_in _ _ _ _ _ _ _ MC _ (in_last_E E _ NE)) | apply ci1].
Qed.

Lemma res3 : ltac2:(tb__ "0|7|
S1aS93S19S17S19S19S19S17S17S17S6fRaR9S8S9S9S9S19S17A2M0S17A2M1SbS9S9S17SdA2S19A2A1M2A2S17S8G1G2S8G0S17S8S19S17R8Z0A4Z18A4S86R6R5R4A3A4R7A4A3S2dS5aQ40M3A1M4S1eRbR7A2S59G3R4A2M5A3S2dG4S1eRcR7A2G5A3S2dG4S1eRdR7A2G5A3S2eS94RdS95RbU8M6R7A3A2S2eS94RdS95S5eRbZ8A2G6R6A3A2S94RdS95S5eRbZ10A2G6R5A3A2A2A2F_;F_;F_;F_;Fvz;Fvy;Fvx;Fz;Fy;Fx;Fa;Fb;Fv3;Frho;").
Proof.
  intros rho v3 b a x y z vx vy vz [H _] Ex Ey Ez. split; [|split].
  - replace a with (a + 0) at 1 by lia. apply (H 0 8%nat x vx); [left; reflexivity | exact Ex].
  - apply (H 8 8%nat y vy); [right; left; reflexivity | exact Ey].
  - apply (H 16 8%nat z vz); [right; right; left; reflexivity | exact Ez].
Qed.
Lemma res1 : ltac2:(tb__ "0|8|
S1aS93S19S17S19S17S6fR6R5S8S9S9S9S19S17A2M0S17A2M1SbS9S9S17SdA2M2S19A2M3A1M4A2S17S8G1G4S8G0S17S8S19S17R4Z0M5A4Z8A4S7G3S8G2S19S8S17SdG5U8M6A4R2A4SaG3A1A3A4R3A4A3S2dS5aQ40M7A1S1eR7R3A2S59G7R2A2A3S94R7S95R5G6R3A3A2F_;F_;Fvx;Fx;Fa;Fb;Fv3;Frho;").
Proof. intros rho v3 b a x vx [H _] Ex. replace a with (a + 0) at 1 by lia. apply (H 0 8%nat x vx); [left; reflexivity | exact Ex]. Qed.

Lemma dsN_same : ltac2:(tb__ "0|3|
SeS93S93S1aSbS0A1M0G0S0S0G0S85R8R6R5R4R3R2R1A7S84RaR7R6R5R4R3R2A7S17S30S74S88RcS1R6A1S1R5A1S98R8A1A4M1R1A2A1S2dS12S5aQ8A1A1M2RbR2A1RcR2A1A3F_;Fz;Sa4S6bS6fR9RaA2G1A3S17S2dG2RcR1A1RdR1A1A3Fz;F_;F_;F_;F_;FL;Fn;Fc;FD;FE;Frho;Fv3;Fv;Fe;").
Proof.
  intros e v v3 rho E D c n L MC (HG & HE & (B160 & B161 & B162 & B163 & B164 & B165 & B166)) FR AV z.
  destruct (dzone_dec (dsN e (qb_addr c) (qb_addr n) (last_addr E)) z) as [Hz|Hz]; [|exact (FR z Hz)].
  unfold dsN in AV, Hz. apply Forall_app in AV as [AV1 AV2]. apply Forall_cons_iff in AV1 as [AVc AV1]. apply Forall_cons_iff in AV1 as [AVn _].
  destruct (res3 rho v3 _ _ _ _ _ _ _ _ AVc B163 B161 B162) as (C0 & C1 & C2). destruct (res3 rho v3 _ _ _ _ _ _ _ _ AVn B164 B165 B166) as (N0 & N1 & N2).
  unfold dzone in Hz. apply List.Exists_app in Hz as [Hz|Hz].
  - inversion Hz as [? ? Hc|? ? Hz2]; subst.
    + destruct (Z_lt_dec z (qb_addr c + 8)); [apply (cell_ok_same v v3 _ (mc_c0 _ _ _ _ _ _ _ MC) C0); cbn; lia|].
      destruct (Z_lt_dec z (qb_addr c + 16)); [apply (cell_ok_same v v3 _ (mc_c1 _ _ _ _ _ _ _ MC) C1); cbn; lia | apply (cell_ok_same v v3 _ (mc_c2 _ _ _ _ _ _ _ MC) C2); cbn; lia].
    + inversion Hz2 as [? ? Hn|? ? Hz3]; subst; [|inversion Hz3].
      destruct (Z_lt_dec z (qb_addr n + 8)); [apply (cell_ok_same v v3 _ (mc_n0 _ _ _ _ _ _ _ MC) N0); cbn; lia|].
      destruct (Z_lt_dec z (qb_addr n + 16)); [apply (cell_ok_same v v3 _ (mc_n1 _ _ _ _ _ _ _ MC) N1); cbn; lia | apply (cell_ok_same v v3 _ (mc_n2 _ _ _ _ _ _ _ MC) N2); cbn; lia].
  - destruct e; [|inversion Hz]. pose proof (e_ne _ _ _ HE eq_refl) as NE. apply Forall_cons_iff in AV2 as [AVl _]. pose proof (res1 rho v3 _ _ _ 0 AVl eq_refl) as L0.
    inversion Hz as [? ? Hl|? ? Hz2]; subst; [|inversion Hz2]. apply (cell_ok_same v v3 _ (mc_l0 _ _ _ _ _ _ _ MC NE) L0). cbn. lia.
Qed.

Lemma c3_cond : ltac2:(tb__ "0|7|
S1aS1aS93S19S17S19S19S19S17S17S17S2dS5aQ40M0A1M1S1eRaR8A2S59G0R7A2A3Sb7VA1;RcA2S9aS17R9Sa5S0S17S1Vall;A4A3S2dG1S1eRdR9A2S59G0R6A2M2A3S2dG1S1eReR9A2G2A3S2dG1S1eRfR9A2G2A3S94RfS95RdU8M3R9A3A2S94R10S95S5eReZ8A2G3R9A3A2S94R11S95S5eRfZ10A2G3R9A3A2S72VA1;R13R12SaS1bA1S8S9S9S9S19S17A2M4S17A2M5SbS9S9S17SdA2S19A2A1M6A2S17S8G5G6S8G4S17S8S19S17R11Z0A4Z18A4S86RfReRdA3A4R10A4A5F_;F_;F_;F_;F_;F_;F_;F_;F_;Fvz;Fvy;Fvx;Fz;Fy;Fx;Fa;Fb;Fv;Frho4;FrhoB;").
Proof.
  intros rhoB rho4 v b a x y z vx vy vz Eb BE Ha Ex Ey Ez Cx Cy Cz. destruct (addr_facts A1 HTH rhoB a BE Ha) as (F1 & F2 & F3 & F4 & F5). unfold carve_cond.
  split; [exact Eb|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [apply ci3|].
  split; [replace (a + 0) with a by lia; apply (present_app v a (a + 8) (a + 24)); [(apply (cell_pr v a 8 vx _ Cx); cbn; lia)|];
          apply (present_app v (a + 8) (a + 16) (a + 24)); [(apply (cell_pr v (a + 8) 8 vy _ Cy); cbn; lia) | (apply (cell_pr v (a + 16) 8 vz _ Cz); cbn; lia)]|].
  split; [|constructor]. unfold c3. constructor; [exists vx; split; [exact Ex | replace (a + 0) with a by lia; exact Cx]|].
  constructor; [exists vy; split; [exact Ey | exact Cy]|]. constructor; [exists vz; split; [exact Ez | exact Cz] | constructor].
Qed.
Lemma c1_cond : ltac2:(tb__ "0|9|
S1aS1aS93S19S17S19S17S2dS5aQ40M0A1M1S1eR6R4A2S59G0R3A2A3Sb7VA1;R8A2S9aS17R5Sa5S0S17S1Vall;A4A3S2dG1S1eR9R5A2S59G0R4A2A3S94R9S95R7U8M2R5A3A2S72VA1;RbRaSaS1bA1S8S9S9S9S19S17A2M3S17A2M4SbS9S9S17SdA2M5S19A2M6A1M7A2S17S8G4G7S8G3S17S8S19S17R9Z0M8A4Z8A4S7G6S8G5S19S8S17SdG8G2A4R7A4SaG6A1A3A4R8A4A5F_;F_;F_;F_;F_;Fvx;Fx;Fa;Fb;Fv;Frho4;FrhoB;").
Proof.
  intros rhoB rho4 v b a x vx Eb BE Ha Ex Cx. destruct (addr_facts A1 HTH rhoB a BE Ha) as (F1 & F2 & F3 & F4 & F5). unfold carve_cond.
  split; [exact Eb|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [apply ci1|].
  split; [replace (a + 0) with a by lia; (apply (cell_pr v a 8 vx _ Cx); cbn; lia)|]. split; [|constructor].
  constructor; [exists vx; split; [exact Ex | replace (a + 0) with a by lia; exact Cx] | constructor].
Qed.
Lemma c2_cond : ltac2:(tb__ "0|b|
S1aS1aS93S19S17S19S19S17S17S2dS5aQ40M0A1M1S1eR8R6A2S59G0R5A2M2A3Sb7VA1;RaA2S9aS17R7Sa5S0S17S1Vall;A4A3S2dG1S1eRbR7A2G2A3S2dG1S1eRcR7A2G2A3S94RcS95RaU8M3R7A3A2S94RdS95S5eRbZ8M4A2G3R7A3A2S72VA1;RfReSaS1bA1S8S9S9S9S19S17A2M5S17A2M6SbS9S9S17SdA2M7S19A2M8A1M9A2S17S8G6G9S8G5S17S8S19S17RdZ0MaA4Z10A4S7G8S8G7S19S8S17SdGaG3A4RbA4S7G8S8G7S19S8S17SdG4G3A4RaA4SaG8A1A3A3A4RcA4A5F_;F_;F_;F_;F_;F_;F_;Fvy;Fvx;Fy;Fx;Fa;Fb;Fv;Frho4;FrhoB;").
Proof.
  intros rhoB rho4 v b a x y vx vy Eb BE Ha Ex Ey Cx Cy. destruct (addr_facts A1 HTH rhoB a BE Ha) as (F1 & F2 & F3 & F4 & F5). unfold carve_cond.
  split; [exact Eb|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [unfold cells_inside; repeat constructor; cbn; lia|].
  split; [replace (a + 0) with a by lia; apply (present_app v a (a + 8) (a + 16)); [(apply (cell_pr v a 8 vx _ Cx); cbn; lia) | (apply (cell_pr v (a + 8) 8 vy _ Cy); cbn; lia)]|].
  split; [|constructor]. constructor; [exists vx; split; [exact Ex | replace (a + 0) with a by lia; exact Cx]|]. constructor; [exists vy; split; [exact Ey | exact Cy] | constructor].
Qed.

Lemma reassoc1 : ltac2:(tb__ "0|2|
SbS0A1M0G0S0S0G0S2dG0ScS0R5ScS0R4S7S0R3S7S0R2R1A3M1A3A3A3ScS0ScS0R5ScS0R4S7S0R3SaS0A1A3A3A3G1A3A3FR;Fn;Fc;FD;FE;").
Proof. intros. rewrite <- !app_assoc. reflexivity. Qed.
Lemma reassoc2 : ltac2:(tb__ "0|2|
SbS0A1M0G0S0S0S0G0S2dG0ScS0R6ScS0R5S7S0R4S7S0R3S7S0R2R1A3M1A3A3A3A3ScS0ScS0R6ScS0R5S7S0R4S7S0R3SaS0A1A3A3A3A3G1A3A3FR;Fn2;Fn;Fc;FD;FE;").
Proof. intros. rewrite <- !app_assoc. reflexivity. Qed.
Lemma apart_in : ltac2:(tb__ "0|3|
S1aS0S0SbS0A1Sb7VA1;R4A2S0S9aS0R1R3A3S9aS17S1R2A1Sa5S0S17S1Vall;A4A3F_;Fb;S9aS0R5R3A3S9aS0R5R4A3S30S2dS17S1R7A1M0S1R6A1A3A1S31S5fS5eS1R8A1M1Z2000M2A2G0A2S5fS5eG0G2A2G1A2A2F_;F_;F_;F_;F_;Fl;Fb2;Fb1;Frho;").
Proof. intros rho b1 b2 l BE HIN H1 H2 NE. exact (addrs_apart A1 HTH rho _ _ BE (HIN b1 H1) (HIN b2 H2) NE). Qed.

Definition dsA (e : bool) (an a2 al : Z) : list dspec := ltac2:(tb__ "0|b|
ScS9S9S9S9S19S17A2M0S17A2M1SbS9S9S17SdA2M2S19A2M3A1M4A2M5S17A2M6S7G6S8G5S17S8G1G4S8G0S17S8S19S17S34Pa3A1Z0M7A4Z18M8A4S86S34Pa4A1M9S34Pa5A1S34Pa6A1A3A4Van;A4S7G6S8G5S17S8G1G4S8G0S17S8S19S17G9G7A4G8A4S86S34Pc2A1S34Pc3A1S34Pc4A1A3A4Va2;A4SaG6A1MaA3A3SeSbG6A1Le;Ve;S7G6S8G5S17S8G1G4S8G0S17S8S19S17S34PbaA1G7A4Z8A4S7G3S8G2S19S8S17SdG7U8A4SbdA4SaG3A1A3A4Val;A4GaA3GaXex2A3").
Lemma others_adv : ltac2:(tb__ "0|0|
SeS2dSbS1bA1Sa6S1bU9S25S83S71S47R1A1A1A1A1A3SaS1bA1A3Fe;"). Proof. intros [|]; reflexivity. Qed.

Lemma adv_glue : ltac2:(tb__ "0|3|
SeSbS0A1M0G0S0S0S0G0S1aSbS5aQ40A1A1Sa2S68Vall;R9ScS0R8S7S0R7S7S0R6S7S0R5R4A3A3A3A3A3S84RbR4RaR9R8R7S7S0R6R5A3A7S5cS5bS67VK;VA0;Vrho0;VA1;RbScS0RaS7S0R9S7S0R8S7S0R7R6A3A3A3A3R9R8U0M1A9S35SaaRcA1U2A2R5R4R3A6S2fS1aS1aS2eS5cS5bS67VK;VA0;Vrho0;VA1;RdScS0ScS0RcS7S0RbSaS0A1A3A3M2S7S0RaS7S0R9R8A3A3A3RaR9G1A9SabReA1R1R6R5A6S84ReR1RdG2RaR9R8A7A2Lrho5;A2F_;F_;F_;Fw;Ftp;Frho;FL;Fn2;Fn;Fc;FD;FE;Fe;").
Proof.
  intros e E D c n n2 L rho tp [tr [ms md]] HGI HV H.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ HGI) as MC.
  assert (GEQ : (D ++ [c]) ++ n :: n2 :: L = D ++ c :: n :: n2 :: L) by (rewrite <- app_assoc; reflexivity).
  assert (HGI2 : GI all E ((D ++ [c]) ++ n :: n2 :: L)) by (rewrite GEQ; exact HGI).
  destruct HJ as (HK & (HMM & _) & HFRM).
  assert (HJ2 : JRM E ((D ++ [c]) ++ n :: n2 :: L) n n2 0 rho tp tr md).
  { split; [exact HK|]. split; [|exact HFRM]. split; [rewrite GEQ; exact HMM | intros i it Hi; lia]. }
  pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ2 HGI2) as MC2.
  pose proof (mc_be _ _ _ _ _ _ _ MC) as BE.
  pose proof HV as (HG & HE & (B160 & B161 & B162 & B163 & B164 & B165 & B166)).
  set (old := E ++ D ++ c :: n :: n2 :: L) in *.
  assert (INN : In n old) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  assert (IN2 : In n2 old) by (apply in_or_app; right; apply in_or_app; right; right; right; left; reflexivity).
  assert (NN2 : qb_addr n2 <> qb_addr n).
  { apply (nodup_mid_ne (E ++ D ++ [c]) (n2 :: L) n n2); [rewrite <- reassoc1; exact (mc_nd _ _ _ _ _ _ _ MC) | apply in_or_app; right; left; reflexivity]. }
  assert (NLE : E <> [] -> last_addr E <> qb_addr n /\ last_addr E <> qb_addr n2).
  { intros NE. split.
    - apply (nodup_mid_ne (E ++ D ++ [c]) (n2 :: L) n (last E qb_dflt)); [rewrite <- reassoc1; exact (mc_nd _ _ _ _ _ _ _ MC) | apply in_or_app; left; apply in_last_E; exact NE].
    - apply (nodup_mid_ne (E ++ D ++ [c; n]) L n2 (last E qb_dflt)); [rewrite <- reassoc2; exact (mc_nd _ _ _ _ _ _ _ MC) | apply in_or_app; left; apply in_last_E; exact NE]. }
  pose proof (mc_sz _ _ _ _ _ _ _ MC n INN) as SZN. pose proof (mc_sum _ _ _ _ _ _ _ MC) as SUM. pose proof (mc_sz _ _ _ _ _ _ _ MC c ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)) as SZC.
  pose proof (mc_E _ _ _ _ _ _ _ MC) as QE.
  set (vals := [Z_to_bv 64 (hd_addr L); Z_to_bv 64 (qb_size n2); Z_to_bv 64 (Z.of_nat (length (qb_items n2)))]).
  destruct (m_step K HL A0 rho0 A1 HQW (T_adv e) (JRM E ((D ++ [c]) ++ n :: n2 :: L) n n2 0)
              (dsN e (qb_addr c) (qb_addr n) (last_addr E)) (dsA e (qb_addr n) (qb_addr n2) (last_addr E)) vals rho tp tr ms md) as (rho5 & H5 & V5).
  - apply T_ok. destruct e; cbn; tauto.
  - exact (JRM_stable K HL A0 rho0 A1 _ _ _ _ _).
  - destruct e; reflexivity.
  - destruct e; reflexivity.
  - reflexivity.
  - split; [exact (proj1 H) | exact I].
  - exact HK.
  - exact HFRM.
  - exact (be_top _ _ BE).
  - exact (dsN_cond e _ rho E D c n (n2 :: L) MC HV).
  - intros HK3 HF3 FR AV.
    pose proof (dsN_same e _ _ rho E D c n (n2 :: L) MC HV FR AV) as SAME.
    set (rho3 := rho_absorb rho (map dobj (dsN e (qb_addr c) (qb_addr n) (last_addr E))) (vms md tp ms)) in *. set (v3 := view segsA (rm rho3)) in *.
    set (rho4 := rho_sets rho3 (combine (t_bs (T_adv e)) vals)).
    assert (OTH : forall i, ~ In i [194; 195; 196]%positive -> rw rho4 i = rw rho i) by (intros i Hi; unfold rho4, rho3; apply rw_sets_absorb; exact Hi).
    assert (CS : forall a k val, cell_ok (view segsA (rm rho)) (mkACell a k val) -> cell_ok v3 (mkACell a k val)).
    { intros a k val Hc. eapply cell_ok_frame1; [|exact Hc]. intros z _. apply SAME. }
    split; [|split; [|split]].
    + split; [exact HK3|]. split; [|exact HF3]. split; [apply (MMEM_ext _ v3 _ _ _ SAME); rewrite GEQ; exact HMM | intros i it Hi; lia].
    + rewrite others_adv. unfold dsA. apply Forall_app. split.
      * constructor; [|constructor; [|constructor]].
        -- apply (c3_cond rho rho4 v3 _ _ _ _ _ (hd_addr (n2 :: L)) (qb_size n) (Z.of_nat (length (qb_items n)))); try exact BE.
           ++ cbn [eval V]. rewrite OTH by (cbn; intuition discriminate). exact B163.
           ++ exact (mc_in _ _ _ _ _ _ _ MC n INN).
           ++ cbn [eval V]. rewrite OTH by (cbn; intuition discriminate). exact B164.
           ++ cbn [eval V]. rewrite OTH by (cbn; intuition discriminate). exact B165.
           ++ cbn [eval V]. rewrite OTH by (cbn; intuition discriminate). exact B166.
           ++ apply CS. exact (mc_n0 _ _ _ _ _ _ _ MC).
           ++ apply CS. exact (mc_n1 _ _ _ _ _ _ _ MC).
           ++ apply CS. exact (mc_n2 _ _ _ _ _ _ _ MC).
        -- apply (c3_cond rho rho4 v3 _ _ _ _ _ (hd_addr L) (qb_size n2) (Z.of_nat (length (qb_items n2)))); try exact BE; try reflexivity.
           ++ cbn [eval V]. rewrite OTH by (cbn; intuition discriminate). exact B164.
           ++ exact (mc_in _ _ _ _ _ _ _ MC n2 IN2).
           ++ apply CS. exact (mc_n0 _ _ _ _ _ _ _ MC2).
           ++ apply CS. exact (mc_n1 _ _ _ _ _ _ _ MC2).
           ++ apply CS. exact (mc_n2 _ _ _ _ _ _ _ MC2).
      * destruct e; [|constructor]. pose proof (e_ne _ _ _ HE eq_refl) as NE. destruct HE as (_ & _ & HE'). destruct (HE' eq_refl) as (_ & _ & E186 & _).
        constructor; [|constructor]. apply (c1_cond rho rho4 v3 _ _ _ 0); try exact BE; try reflexivity.
        -- cbn [eval V]. rewrite OTH by (cbn; intuition discriminate). exact E186.
        -- exact (mc_in _ _ _ _ _ _ _ MC _ (in_last_E E _ NE)).
        -- apply CS. exact (mc_l0 _ _ _ _ _ _ _ MC NE).
    + pose proof (apart_in rho n n2 old BE (mc_in _ _ _ _ _ _ _ MC) INN IN2 ltac:(congruence)) as AP1.
      unfold dsA. destruct e; cbn [app].
      * pose proof (e_ne _ _ _ HE eq_refl) as NE. destruct (NLE NE) as [NL1 NL2].
        pose proof (apart_in rho _ n old BE (mc_in _ _ _ _ _ _ _ MC) (in_last_E E _ NE) INN NL1) as AP2.
        pose proof (apart_in rho _ n2 old BE (mc_in _ _ _ _ _ _ _ MC) (in_last_E E _ NE) IN2 NL2) as AP3. unfold last_addr in *.
        constructor; [constructor; [unfold apart_d; lia | constructor; [unfold apart_d; lia | constructor]]|].
        constructor; [constructor; [unfold apart_d; lia | constructor] | constructor; [constructor | constructor]].
      * constructor; [constructor; [unfold apart_d; lia | constructor] | constructor; [constructor | constructor]].
    + intros _. constructor; [|constructor]. apply (sz13_holds rho4 (V 165) (qb_size n)); [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact B165 | lia].
  - exists rho5. split; [exact H5|].
    set (rho4 := rho_sets _ _) in V5.
    assert (OTH : forall i, ~ In i [194; 195; 196]%positive -> rw rho4 i = rw rho i) by (intros i Hi; unfold rho4; apply rw_sets_absorb; exact Hi).
    assert (VID : forall i, In (i, V i) (t_M (T_adv e)) -> ~ In i [194; 195; 196]%positive -> rw rho5 i = rw rho i).
    { intros i Hi Hn. rewrite (V5 i (V i) Hi). cbn [eval V]. apply OTH. exact Hn. }
    destruct HG as (G204 & G205 & G206 & G207 & G208).
    split; [|split].
    + unfold HVG. rewrite GEQ. rewrite !VID by (first [destruct e; cbn; tauto | cbn; intuition discriminate]). tauto.
    + destruct HE as (E167 & E2 & E3). unfold HVE. rewrite VID by (first [destruct e; cbn; tauto | cbn; intuition discriminate]). split; [exact E167|]. split; [exact E2|].
      intros He. subst e. rewrite !VID by (first [cbn; tauto | cbn; intuition discriminate]). exact (E3 eq_refl).
    + unfold HVB. rewrite (V5 160%positive (V 163)), (V5 161%positive (V 165)), (V5 162%positive (V 166)), (V5 163%positive (V 164)), (V5 164%positive (V 194)), (V5 165%positive (V 195)), (V5 166%positive (V 196)) by (destruct e; cbn; tauto).
      cbn [eval V]. rewrite !OTH by (cbn; intuition discriminate). repeat split; try assumption; reflexivity.
Qed.

Definition dsG (e : bool) (ac an al : Z) : list dspec := ltac2:(tb__ "0|11|
ScS9S9S9S9S19S17A2M0S17A2M1SbS9S9S17SdA2M2S19A2M3A1M4A2M5S17A2M6S7G6S8G5S17S8G1G4S8G0S17S8S19S17S34Pa0A1Z0M7A4Z18M8A4S7G3S8G2S19S8S17SdG7U8M9A4MaS34Pa4A1A4S7G3S8G2S19S8S17SdZ10G9A4MbS36A4S7G3S8G2S19S8S17SdZ8McG9A4MdS3aA4SaG3A1MeA3A3A3A4Vac;A4S7G6S8G5S17S8G1G4S8G0S17S8S19S17S34Pa3A1MfG7A4G8A4S7G3S8G2S19GaSbdA4S7G3S8G2S19GbSbdA4S7G3S8G2S19GdS1fZ2000A1A4GeA3A3A3A4Van;A4SaG6A1M10A3A3SeSbG6A1Le;Ve;S7G6S8G5S17S8G1G4S8G0S17S8S19S17S34PbaA1G7A4GcA4S7G3S8G2S19GaGfA4GeA3A4Val;A4G10A3G10Xex2A3").
Lemma res_cell : ltac2:(tb__ "0|6|
S1aS93S19S17S17SbS9S9S17SdA2M0S19A2M1A1M2S17S17SdS19S17S6fRbRaS8S9S9S9S19S17A2M3S17A2M4G2A2S17S8G4G2S8G3S17S8S19S17R9R8A4R7A4R6A4R5A4A3S9aG1S8G0S19S8S17SdR5R4A4R3A4R7A3S2dS5aQ40M5A1S1eRdR4A2S59G5R3A2A3S94RdS95S5eR8R7A2R6R4A3A2F_;F_;F_;Fval;Fx;Fk;Foff;Fa;Fcs;Fhi;Flo;Fb;Fv3;Frho;").
Proof. intros rho v3 b lo hi cs a off k x val [H _] Hin Ex. exact (H off k x val Hin Ex). Qed.
Lemma ci3p : ltac2:(tb__ "0|4|
S19S19S19SecZ0M0Z18S7S9S9S17SdA2M1S19A2M2S8G1S19S8S17SdG0U8M3A4R3A4S7G2S8G1S19S8S17SdZ10G3A4R2A4S7G2S8G1S19S8S17SdZ8G3A4R1A4SaG2A1A3A3A3A3Fz;Fy;Fx;"). Proof. intros. unfold cells_inside. repeat constructor; cbn; lia. Qed.

Lemma dsG_cond : ltac2:(tb__ "0|1|
SeS93S1aSbS0A1M0G0S0S0G0S85R7R6R5R4R3R2R1A7S84R9R7R6R5R4R3R2A7Sa4S6bS73VA1;R8A2S8bRaS1R5A1S1R4A1S98R7A1A4A3F_;F_;FL;Fn;Fc;FD;FE;Frho;Fv;Fe;").
Proof.
  intros e v rho E D c n L MC (HG & HE & (B160 & B161 & B162 & B163 & _)). pose proof (mc_be _ _ _ _ _ _ _ MC) as BE.
  assert (INC : In c (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  assert (INN : In n (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  unfold dsG. apply Forall_app. split.
  - constructor; [apply hdr_cond; [exact B160 | exact BE | exact (mc_in _ _ _ _ _ _ _ MC c INC) | apply ci3p]|].
    constructor; [apply hdr_cond; [exact B163 | exact BE | exact (mc_in _ _ _ _ _ _ _ MC n INN) | apply ci3p] | constructor].
  - destruct e; [|constructor]. pose proof (e_ne _ _ _ HE eq_refl) as NE. destruct HE as (_ & _ & HE). destruct (HE eq_refl) as (_ & _ & E186 & _).
    constructor; [|constructor]. apply lnk_cond; [exact E186 | exact BE | exact (mc_in _ _ _ _ _ _ _ MC _ (in_last_E E _ NE)) | apply ci1].
Qed.

Lemma eval_csz : ltac2:(tb__ "0|5|
S1aS17S17S2dS5aQ40M0A1M1S1cR3Pa1A2S59G0R2A2M2A3S2dG1S1cR4Pa5A2G2A3S5fZ2000M3R4A2M4G4S61S5eR6R5A2S63Z2Z3eA2A2S2dG1S1eR8S3aA2S59G0S64S5eR7R6A2G3A2A2A3F_;F_;F_;F_;F_;Fsn;Fsc;Frho;").
Proof.
  intros rho sc sn E1 E2 H1 H2 H3. unfold csz. replace (sc + sn - 8192) with (sc + sn + -8192) by lia.
  apply eval_addl; [apply eval_add_z; [exact E1 | exact E2 | lia | lia | lia] | lia | lia | lia].
Qed.
Lemma eval_ccn : ltac2:(tb__ "0|4|
S1aS17S17S2dS5aQ40M0A1M1S1cR3Pa2A2S59G0R2A2M2A3S2dG1S1cR4Pa6A2G2A3S2eS5fZ0R4A2S5fR4Z3fdA2A2M3G3S2dG1S1eR7S36A2S59G0S5eR5R6A2A2A3F_;F_;F_;F_;Fcn;Fcc;Frho;").
Proof. intros rho cc cn E1 E2 H1 H2. unfold ccn. apply eval_add_z; [exact E2 | exact E1 | lia | lia | lia]. Qed.

Lemma mg_mem : ltac2:(tb__ "0|4|
SeS93S93S1aSbS0A1M0G0S0S0G0S85R8R6R5R4R3R2R1A7S84RaR7R6R5R4R3R2A7S68Vall;R7ScS0R6S7S0R5S7S0R4R3A3A3A3A3S6eRbS4VA1;A1M1R8ScS0R7S7S0R6S7S0R5R4A3A3A3A4S76RcR7R6SfS9S17S17A2M2S2R6A1A2A4S5fS60SbcSfG2S2R8A1A2SfG2S2R7A1A2A2A1Z3fdA2S17S30S74S8bR10S1RaA1S1R9A1S98RcA1A4M3R1A2A1S2dS12S5aQ8A1A1RfR2A1R10R2A1A3F_;Fz;Sa4S6bS6fRdReA2G3A3S6eRfG1ScS0RdS7S0S6cRaA1SaS0A1A3A3ScS0RcS7S0S6dRbRaA2R9A3A3A4F_;F_;F_;F_;F_;F_;F_;F_;FL;Fn;Fc;FD;FE;Frho;Fv3;Fv;Fe;").
Proof.
  intros e v v3 rho E D c n L MC (HG & HE & (B160 & B161 & B162 & B163 & B164 & B165 & B166)) HGI HMM HCP HCAP FR AV.
  pose proof (mc_be _ _ _ _ _ _ _ MC) as BE.
  assert (INC : In c (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  assert (INN : In n (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  pose proof (mc_sz _ _ _ _ _ _ _ MC c INC) as SZC. pose proof (mc_sz _ _ _ _ _ _ _ MC n INN) as SZN. pose proof (mc_sum _ _ _ _ _ _ _ MC) as SUM. pose proof (mc_E _ _ _ _ _ _ _ MC) as QE.
  pose proof (mc_cap _ _ _ _ _ _ _ MC c INC) as CPC. pose proof (mc_cap _ _ _ _ _ _ _ MC n INN) as CPN.
  unfold dsG in AV. apply Forall_app in AV as [AV1 AV2]. apply Forall_cons_iff in AV1 as [AVc AV1]. apply Forall_cons_iff in AV1 as [AVn _].
  apply (mmem_merge A1 HTH rho v v3 E D c n L BE HGI HMM HCP).
  - unfold capb, kQuarantineBatchCount. cbn [mergeb qb_items]. rewrite length_app. exact HCAP.
  - intros z Hz. apply FR. intros HD. apply Hz. unfold dsG, dzone in HD. apply List.Exists_app in HD as [HD|HD].
    + inversion HD as [? ? Hc|? ? HD2]; subst; [left; lia|]. inversion HD2 as [? ? Hn|? ? HD3]; subst; [right; left; lia | inversion HD3].
    + destruct e; [|inversion HD]. inversion HD as [? ? Hl|? ? HD2]; subst; [|inversion HD2]. right. right. split; [exact (e_ne _ _ _ HE eq_refl) | lia].
  - replace (qb_addr c) with (qb_addr c + 0) at 1 by lia. apply (res_cell rho v3 _ _ _ _ _ 0 8%nat (V 164) _ AVc); [cbn; tauto | exact B164].
  - apply (res_cell rho v3 _ _ _ _ _ 8 8%nat csz _ AVc); [cbn; tauto | apply eval_csz; [exact B161 | exact B165 | lia | lia | lia]].
  - apply (res_cell rho v3 _ _ _ _ _ 16 8%nat ccn _ AVc); [cbn; tauto|]. rewrite Nat2Z.inj_add, Z.add_comm. apply eval_ccn; [exact B162 | exact B166 | lia | lia].
  - replace (qb_addr n) with (qb_addr n + 0) at 1 by lia. apply (res_cell rho v3 _ _ _ _ _ 0 8%nat ZQ _ AVn); [cbn; tauto | reflexivity].
  - apply (res_cell rho v3 _ _ _ _ _ 8 8%nat (SLit 8192) _ AVn); [cbn; tauto | reflexivity].
  - apply (res_cell rho v3 _ _ _ _ _ 16 8%nat ZQ _ AVn); [cbn; tauto | reflexivity].
  - intros NE. destruct e; [|exfalso; exact (NE (proj1 (proj1 (proj2 HE)) eq_refl))]. apply Forall_cons_iff in AV2 as [AVl _].
    replace (last_addr E) with (last_addr E + 0) at 1 by lia. apply (res_cell rho v3 _ _ _ _ _ 0 8%nat (V 163) _ AVl); [cbn; tauto | exact B163].
Qed.

Lemma fact_in : ltac2:(tb__ "0|0|
S5dS82S1aSbS5aQ40A1A1Sa2S1dS5cS5bR6R5R4R3R2A6S2dSeS9bS1dS27R2A1S24S83R6A1A1A3S10A3S20R6R3A2F_;F_;Ff;Fw;Ftp;Frho;FC;FJ;").
Proof.
  intros J C rho tp w f H HB. apply existsb_exists in HB as (g & Hg & E). apply sprop_eqb_sound in E. subst g.
  exact (proj1 (Forall_forall _ _) (SPA_facts_hold segsA _ rho C tp w H) f Hg).
Qed.
Lemma hd_addr_mid : ltac2:(tb__ "0|1|
SbS0A1M0S0S0G0G0S2dS17S1R4A1S1R3A1A3S2dS17S99ScS0R6S7S0R5R3A3A3A1S99ScS0R6S7S0R4R2A3A3A1A3F_;FR';FR;Fb';Fb;FD;").
Proof. intros D b b' R R' Eb. destruct D; unfold hd_addr; cbn; [exact Eb | reflexivity]. Qed.
Lemma last_addr_app : ltac2:(tb__ "0|1|
SbS0A1M0G0S30S2dG0R1SaS0A1A3A1S2dS17S98ScS0R3R2A3A1S98R2A1A3F_;FY;FX;").
Proof. intros X Y NE. unfold last_addr. f_equal. induction X as [|x X' IH]; [reflexivity|]. cbn [app]. rewrite <- IH. destruct (X' ++ Y) eqn:EE; [apply app_eq_nil in EE as [_ EE]; congruence | reflexivity]. Qed.

Lemma cap_of_fact : ltac2:(tb__ "0|5|
S1aS17S17S2dS5aQ40M0A1M1S1cR3Pa2A2S59G0R2A2M2A3S2dG1S1cR4Pa6A2G2A3S2eS5fZ0R4A2S5fR4Z3fdM3A2A2M4G4S20R7S23S21SdfS1fG3A1S36A3A1A2S5fS5eR6R7A2G3A2F_;F_;F_;F_;F_;Fcn;Fcc;Frho;").
Proof.
  intros rho cc cn E1 E2 H1 H2 HF. destruct (Z_le_dec (cn + cc) 1021) as [LE|GT]; [exact LE|]. exfalso. apply HF. cbn [holds branch_taken].
  rewrite (eval_ccn rho cc cn E1 E2 H1 H2). cbn [eval]. unfold bv_ltu. rewrite !u64_lit by lia. apply Z.ltb_lt. lia.
Qed.

Definition dsM3 (an a2 : Z) (ac : Z) : list dspec := ltac2:(tb__ "0|a|
S7S9S9S9S9S19S17A2M0S17A2M1SbS9S9S17SdA2M2S19A2M3A1M4A2M5S17A2M6S8G5S17S8G1G4S8G0S17S8S19S17S34Pa0A1Z0M7A4Z18M8A4S86S34Pa4A1M9S3aS36A3A4Vac;A4S7G6S8G5S17S8G1G4S8G0S17S8S19S17G9G7A4G8A4S86S34Pc2A1S34Pc3A1S34Pc4A1A3A4Va2;A4S7G6S8G5S17S8G1G4S8G0S17S8S19S17S34Pa3A1G7A4Z8A4S7G3S8G2S19S8S17SdG7U8A4SbdA4SaG3A1A3A4Van;A4SaG6A1A3A3A3").
Lemma others_mg : ltac2:(tb__ "0|0|
SeS2dSbS1bA1Sa6S1bU9S25S83S71S4aR1A1A1A1A1A3SaS1bA1A3Fe;"). Proof. intros [|]; reflexivity. Qed.

Lemma mg_glue : ltac2:(tb__ "0|4|
SeSbS0A1M0G0S0S0S0G0S1aSbS5aQ40A1A1Sa2S68Vall;R9ScS0R8S7S0R7S7S0R6S7S0R5R4A3A3A3A3A3S84RbR4RaR9R8R7S7S0R6R5A3A7S5cS5bS67VK;VA0;Vrho0;VA1;RbScS0RaS7S0R9S7S0R8S7S0R7R6A3A3A3A3R9R8SfS9S17S17A2S2R8A1A2A9S35SadRcA1U3A2R5R4R3A6S2fS1aS1aS2eS5cS5bS67VK;VA0;Vrho0;VA1;ScS0RdS7S0S6cRaA1SaS0A1A3A3M1ScS0RcS7S0S6dRbRaA2M2S7S0R9R8A3A3A3M3G2R9U0A9SabS10A1R1R6R5A6S2eS84S10R1G1RcG2R9R8A7S68Vall;G1G3A3A2A2Lrho5;A2F_;F_;F_;Fw;Ftp;Frho;FL;Fn2;Fn;Fc;FD;FE;Fe;").
Proof.
  intros e E D c n n2 L rho tp [tr [ms md]] HGI HV H.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ HGI) as MC. destruct HJ as (HK & (HMM & HCP) & HFRM).
  pose proof (mc_be _ _ _ _ _ _ _ MC) as BE.
  pose proof HV as (HG & HE & (B160 & B161 & B162 & B163 & B164 & B165 & B166)).
  set (old := E ++ D ++ c :: n :: n2 :: L) in *.
  assert (INC : In c old) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  assert (INN : In n old) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  assert (IN2 : In n2 old) by (apply in_or_app; right; apply in_or_app; right; right; right; left; reflexivity).
  pose proof (mc_sz _ _ _ _ _ _ _ MC c INC) as SZC. pose proof (mc_sz _ _ _ _ _ _ _ MC n INN) as SZN. pose proof (mc_sum _ _ _ _ _ _ _ MC) as SUM. pose proof (mc_E _ _ _ _ _ _ _ MC) as QE.
  pose proof (mc_cap _ _ _ _ _ _ _ MC c INC) as CPC. pose proof (mc_cap _ _ _ _ _ _ _ MC n INN) as CPN. pose proof (mc_len _ _ _ _ _ _ _ MC) as LEN.
  assert (HCAP : Z.of_nat (length (qb_items c) + length (qb_items n)) <= 1021).
  { rewrite Nat2Z.inj_add, Z.add_comm. apply (cap_of_fact rho _ _ B162 B166 ltac:(lia) ltac:(lia)). apply (fact_in _ _ rho tp _ _ H). destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. }
  assert (HGI' : GI all (E ++ [emptyb n]) (D ++ mergeb c n :: n2 :: L)).
  { apply GI_merge; [exact HGI|]. unfold capb, kQuarantineBatchCount. cbn [mergeb qb_items]. rewrite length_app. exact HCAP. }
  assert (NC2 : qb_addr n2 <> qb_addr c).
  { apply (nodup_mid_ne (E ++ D) (n :: n2 :: L) c n2); [unfold old in *; rewrite <- app_assoc; exact (mc_nd _ _ _ _ _ _ _ MC) | apply in_or_app; right; right; left; reflexivity]. }
  assert (NN2 : qb_addr n2 <> qb_addr n).
  { apply (nodup_mid_ne (E ++ D ++ [c]) (n2 :: L) n n2); [rewrite <- reassoc1; exact (mc_nd _ _ _ _ _ _ _ MC) | apply in_or_app; right; left; reflexivity]. }
  assert (NCN : qb_addr c <> qb_addr n).
  { apply (nodup_mid_ne (E ++ D ++ [c]) (n2 :: L) n c); [rewrite <- reassoc1; exact (mc_nd _ _ _ _ _ _ _ MC) | apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; left; reflexivity]. }
  assert (LENB : 3 <= Z.of_nat (length (D ++ c :: n :: n2 :: L))) by (rewrite length_app; cbn [length]; lia).
  set (vals := [Z_to_bv 64 (hd_addr L); Z_to_bv 64 (qb_size n2); Z_to_bv 64 (Z.of_nat (length (qb_items n2)))]).
  destruct (m_step K HL A0 rho0 A1 HQW (T_mg e) (JRM (E ++ [emptyb n]) (D ++ mergeb c n :: n2 :: L) (mergeb c n) n2 0)
              (dsG e (qb_addr c) (qb_addr n) (last_addr E)) (dsM3 (qb_addr n) (qb_addr n2) (qb_addr c)) vals rho tp tr ms md) as (rho5 & H5 & V5).
  - apply T_ok. destruct e; cbn; tauto.
  - exact (JRM_stable K HL A0 rho0 A1 _ _ _ _ _).
  - destruct e; reflexivity.
  - destruct e; reflexivity.
  - reflexivity.
  - split; [exact (proj1 H) | exact I].
  - exact HK.
  - exact HFRM.
  - exact (be_top _ _ BE).
  - exact (dsG_cond e _ rho E D c n (n2 :: L) MC HV).
  - intros HK3 HF3 FR AV.
    pose proof (mg_mem e _ _ rho E D c n (n2 :: L) MC HV HGI HMM HCP HCAP FR AV) as HMM3.
    set (rho3 := rho_absorb rho (map dobj (dsG e (qb_addr c) (qb_addr n) (last_addr E))) (vms md tp ms)) in *. set (v3 := view segsA (rm rho3)) in *.
    set (rho4 := rho_sets rho3 (combine (t_bs (T_mg e)) vals)).
    assert (OTH : forall i, ~ In i [194; 195; 196]%positive -> rw rho4 i = rw rho i) by (intros i Hi; unfold rho4, rho3; apply rw_sets_absorb; exact Hi).
    assert (HJ3 : JRM (E ++ [emptyb n]) (D ++ mergeb c n :: n2 :: L) (mergeb c n) n2 0 rho3 tp tr md).
    { split; [exact HK3|]. split; [|exact HF3]. split; [exact HMM3 | intros i it Hi; lia]. }
    pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ3 HGI') as MC3. fold v3 in MC3.
    assert (NE' : E ++ [emptyb n] <> []) by (destruct E; discriminate).
    assert (LA' : last_addr (E ++ [emptyb n]) = qb_addr n) by (unfold last_addr; rewrite last_snoc; reflexivity).
    split; [exact HJ3|]. split; [|split].
    + rewrite others_mg. unfold dsM3. constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (c3_cond rho rho4 v3 _ _ _ _ _ (qb_addr n2) (qb_size c + qb_size n - 8192) (Z.of_nat (length (qb_items c ++ qb_items n)))); try exact BE.
        -- cbn [eval V]. rewrite OTH by (cbn; intuition discriminate). exact B160.
        -- exact (mc_in _ _ _ _ _ _ _ MC c INC).
        -- cbn [eval V]. rewrite OTH by (cbn; intuition discriminate). exact B164.
        -- apply eval_csz; [rewrite OTH by (cbn; intuition discriminate); exact B161 | rewrite OTH by (cbn; intuition discriminate); exact B165 | lia | lia | lia].
        -- rewrite length_app, Nat2Z.inj_add, Z.add_comm. apply eval_ccn; [rewrite OTH by (cbn; intuition discriminate); exact B162 | rewrite OTH by (cbn; intuition discriminate); exact B166 | lia | lia].
        -- exact (mc_c0 _ _ _ _ _ _ _ MC3).
        -- exact (mc_c1 _ _ _ _ _ _ _ MC3).
        -- exact (mc_c2 _ _ _ _ _ _ _ MC3).
      * apply (c3_cond rho rho4 v3 _ _ _ _ _ (hd_addr L) (qb_size n2) (Z.of_nat (length (qb_items n2)))); try exact BE; try reflexivity.
        -- cbn [eval V]. rewrite OTH by (cbn; intuition discriminate). exact B164.
        -- exact (mc_in _ _ _ _ _ _ _ MC n2 IN2).
        -- exact (mc_n0 _ _ _ _ _ _ _ MC3).
        -- exact (mc_n1 _ _ _ _ _ _ _ MC3).
        -- exact (mc_n2 _ _ _ _ _ _ _ MC3).
      * apply (c1_cond rho rho4 v3 _ _ _ 0); try exact BE; try reflexivity.
        -- cbn [eval V]. rewrite OTH by (cbn; intuition discriminate). exact B163.
        -- exact (mc_in _ _ _ _ _ _ _ MC n INN).
        -- rewrite <- LA'. exact (mc_l0 _ _ _ _ _ _ _ MC3 NE').
    + pose proof (apart_in rho c n2 old BE (mc_in _ _ _ _ _ _ _ MC) INC IN2 ltac:(congruence)) as AP1.
      pose proof (apart_in rho c n old BE (mc_in _ _ _ _ _ _ _ MC) INC INN NCN) as AP2.
      pose proof (apart_in rho n2 n old BE (mc_in _ _ _ _ _ _ _ MC) IN2 INN NN2) as AP3.
      unfold dsM3. constructor; [constructor; [unfold apart_d; lia | constructor; [unfold apart_d; lia | constructor]]|].
      constructor; [constructor; [unfold apart_d; lia | constructor] | constructor; [constructor | constructor]].
    + intros _. assert (E204 : eval rho4 (add (V 204) (SLit (-1))) = Z_to_bv 64 (Z.of_nat (length (D ++ c :: n :: n2 :: L)) + -1)).
      { apply eval_addl; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact (proj1 HG) | lia | lia | lia]. }
      constructor; [apply (ne0_holds rho4 _ _ E204); lia|].
      constructor; [apply (sz13_holds rho4 csz (qb_size c + qb_size n - 8192)); [apply eval_csz; [rewrite OTH by (cbn; intuition discriminate); exact B161 | rewrite OTH by (cbn; intuition discriminate); exact B165 | lia | lia | lia] | lia]|].
      destruct e; [|constructor]. constructor; [|constructor]. destruct HE as (_ & _ & HE'). destruct (HE' eq_refl) as (E184 & _).
      apply (ne0_holds rho4 _ (Z.of_nat (length E) + 1)); [apply eval_addl; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact E184 | lia | lia | lia] | lia].
  - exists rho5. split; [exact H5|]. split; [|exact HGI'].
    set (rho4 := rho_sets _ _) in V5.
    assert (OTH : forall i, ~ In i [194; 195; 196]%positive -> rw rho4 i = rw rho i) by (intros i Hi; unfold rho4; apply rw_sets_absorb; exact Hi).
    destruct HG as (G204 & G205 & G206 & G207 & G208). destruct HE as (E167 & E2 & E3).
    split; [|split].
    + unfold HVG. rewrite (V5 204%positive (add (V 204) (SLit (-1)))), (V5 205%positive (V 205)), (V5 206%positive (V 206)), (V5 207%positive (V 207)), (V5 208%positive (V 208)) by (cbn; tauto).
      cbn [eval V]. rewrite !OTH by (cbn; intuition discriminate).
      split; [|split; [|split; [|split]]]; try assumption.
      * replace (Z.of_nat (length (D ++ mergeb c n :: n2 :: L))) with (Z.of_nat (length (D ++ c :: n :: n2 :: L)) + -1) by (rewrite !length_app; cbn [length]; lia).
        apply eval_addl; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact G204 | lia | lia | lia].
      * rewrite G205. f_equal. apply hd_addr_mid. reflexivity.
      * rewrite G206. f_equal. replace (D ++ c :: n :: n2 :: L) with ((D ++ [c; n]) ++ n2 :: L) by (rewrite <- app_assoc; reflexivity).
        replace (D ++ mergeb c n :: n2 :: L) with ((D ++ [mergeb c n]) ++ n2 :: L) by (rewrite <- app_assoc; reflexivity). rewrite !last_addr_app by discriminate. reflexivity.
    + unfold HVE. rewrite (V5 167%positive (add (V 167) (SLit 8192))), (V5 184%positive (k' e)), (V5 185%positive (f' e)), (V5 186%positive (V 163)), (V5 187%positive (s' e)) by (cbn; tauto).
      assert (QE' : qsize (E ++ [emptyb n]) = qsize E + 8192) by (rewrite qsize_app, qsize_cons; cbn [emptyb qb_size]; unfold kQuarantineBatchSize; change (qsize []) with 0; lia).
      split; [rewrite QE'; apply eval_addl; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact E167 | lia | lia | lia]|].
      split; [split; [discriminate | intros X; destruct E; discriminate X]|]. intros _.
      destruct e.
      * destruct (E3 eq_refl) as (E184 & E185 & E186 & E187). pose proof (e_ne true rho E (conj E167 (conj E2 E3)) eq_refl) as NE.
        unfold k', f', s'. split; [|split; [|split]].
        -- rewrite length_app, Nat2Z.inj_add. cbn [length]. apply eval_addl; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact E184 | lia | lia | lia].
        -- cbn [eval V]. rewrite OTH by (cbn; intuition discriminate). rewrite (hd_addr_app E _ NE). exact E185.
        -- cbn [eval V]. rewrite OTH by (cbn; intuition discriminate). unfold last_addr. rewrite last_snoc. exact B163.
        -- rewrite QE'. apply eval_addl; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact E187 | lia | lia | lia].
      * assert (EN : E = []) by (apply (proj1 E2); reflexivity). subst E. unfold k', f', s'. cbn [app length eval V]. rewrite !OTH by (cbn; intuition discriminate).
        split; [reflexivity|]. split; [exact B163|]. split; [exact B163 | reflexivity].
    + unfold HVB. rewrite (V5 160%positive (V 160)), (V5 161%positive csz), (V5 162%positive ccn), (V5 163%positive (V 164)), (V5 164%positive (V 194)), (V5 165%positive (V 195)), (V5 166%positive (V 196)) by (cbn; tauto).
      cbn [eval V mergeb qb_addr qb_size qb_items]. rewrite !OTH by (cbn; intuition discriminate).
      split; [exact B160|]. split; [unfold kQuarantineBatchSize; apply eval_csz; [rewrite OTH by (cbn; intuition discriminate); exact B161 | rewrite OTH by (cbn; intuition discriminate); exact B165 | lia | lia | lia]|].
      split; [rewrite length_app, Nat2Z.inj_add, Z.add_comm; apply eval_ccn; [rewrite OTH by (cbn; intuition discriminate); exact B162 | rewrite OTH by (cbn; intuition discriminate); exact B166 | lia | lia]|].
      split; [exact B164|]. repeat split; reflexivity.
Qed.

Lemma dz_nil : ltac2:(tb__ "0|0|
S17S30S74SaS6bA1R1A2A1Fz;"). Proof. intros z H. inversion H. Qed.
Lemma mrg0_glue : ltac2:(tb__ "0|1|
SeSbS0A1M0G0S0S0G0S1aSbS5aQ40A1A1Sa2S68Vall;R8ScS0R7S7S0R6S7S0R5R4A3A3A3A3S84RaR4R9R8R7R6R5A7S5cS5bS67VK;VA0;Vrho0;VA1;RaScS0R9S7S0R8S7S0R7R6A3A3A3R8R7U0A9S35SaaRbA1U3A2R5R4R3A6S2fS1aS1aS2eS5cS5bS67VK;VA0;Vrho0;VA1;RcScS0RbS7S0RaS7S0R9R8A3A3A3RaR9SfS9S17S17A2S2R9A1A2A9SaeRdA1R1R6R5A6S84RdR1RcRbRaR9R8A7A2Lrho5;A2F_;F_;F_;Fw;Ftp;Frho;FL;Fn;Fc;FD;FE;Fe;").
Proof.
  intros e E D c n L rho tp [tr [ms md]] HGI HV H.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. destruct HJ as (HK & (HMM & _) & HFRM).
  pose proof (benv_of_K K HL A1 HCI rho tp tr md HK) as BE.
  pose proof HV as (HG & HE & (B160 & B161 & B162 & B163 & B164 & B165 & B166)).
  assert (LN0 : length (qb_items n) = 0%nat).
  { assert (F : holds rho (SPBranch BC_EQ (V 166) (SLit 0))) by (apply (fact_in _ _ rho tp _ _ H); destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    cbn [holds branch_taken eval V] in F. rewrite B166 in F. unfold bv_eqb in F. apply Z.eqb_eq in F.
    assert (Z.of_nat (length (qb_items n)) <= 1021).
    { destruct HGI as (_ & _ & FC & _). assert (INN : In n (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
      pose proof (proj1 (Forall_forall _ _) FC n INN) as X. unfold capb, kQuarantineBatchCount in X. exact X. }
    rewrite !u64_lit in F by lia. lia. }
  destruct (m_step K HL A0 rho0 A1 HQW (T_mrg0 e) (JRM E (D ++ c :: n :: L) c n (length (qb_items n))) [] [] [] rho tp tr ms md) as (rho5 & H5 & V5).
  - apply T_ok. destruct e; cbn; tauto.
  - exact (JRM_stable K HL A0 rho0 A1 _ _ _ _ _).
  - destruct e; reflexivity.
  - reflexivity.
  - reflexivity.
  - split; [exact (proj1 H) | exact I].
  - exact HK.
  - exact HFRM.
  - exact (be_top _ _ BE).
  - constructor.
  - intros HK3 HF3 FR AV. split; [|split; [constructor | split; [constructor | intros _; constructor]]].
    split; [exact HK3|]. split; [|exact HF3]. split; [apply (MMEM_ext _ _ _ _ _ (fun z => FR z (dz_nil z))); exact HMM | rewrite LN0; intros i it Hi; lia].
  - exists rho5. split; [exact H5|]. apply (HVM_vals e rho rho5); [|exact HV]. intros v Hv.
    rewrite (V5 v (V v)) by (unfold T_mrg0, idm; cbn [t_M]; apply in_map_iff; exists v; split; [reflexivity | exact Hv]). reflexivity.
Qed.

Definition HVCp (rho : valuation) (c n : qbatch) (j : nat) (it : Z * Z) : Prop := ltac2:(tb__ "0|5|
S2eS2dS5aQ40M0A1M1S1cVrho;Pa9A2S59G0S5eS5eS1Vn;A1Z18M2A2S62Z8M3S60Vj;A1A2A2A2A3S2eS2dG1S1cVrho;PaaA2S59G0S5eS5eS1Vc;A1G2A2S62G3S60SbcSfS9S17S17A2M4S2Vc;A1A2Vj;A2A1A2A2A2A3S2eS2dG1S1cVrho;PbcA2S59G0S64S13S17S17Vit;A3Z10A2A2A3S2dS12G4A1S9cG4S2Vn;A1Vj;A3S14G4Vit;A2A3A2A2A2").
Definition dsS (bs bd : sv) (asrc adst : Z) : list dspec := ltac2:(tb__ "0|a|
S7S9S9S9S9S19S17A2M0S17A2M1SbS9S9S17SdA2M2S19A2M3A1M4A2M5S17A2M6S8G5S17S8G1G4S8G0S17S8S19S17Vbs;Z0M7A4Z8M8A4S7G3S8G2S19S8S17SdG7U8A4S34PbdA1A4SaG3A1M9A3A4Vasrc;A4S7G6S8G5S17S8G1G4S8G0S17S8S19S17Vbd;G7A4G8A4G9A4Vadst;A4SaG6A1A3A3").
Definition dsSd (asrc adst : Z) : list dspec := ltac2:(tb__ "0|a|
S7S9S9S9S9S19S17A2M0S17A2M1SbS9S9S17SdA2M2S19A2M3A1M4A2M5S17A2M6S8G5S17S8G1G4S8G0S17S8S19S17S34Pa9A1Z0M7A4Z8M8A4S7G3S8G2S19S8S17SdG7U8A4S34PbcA1A4SaG3A1A3M9A4Vasrc;A4S7G6S8G5S17S8G1G4S8G0S17S8S19S17S34PaaA1G7A4G8A4G9A4Vadst;A4SaG6A1A3A3").

Lemma dsN_disj : ltac2:(tb__ "0|8|
SeS1aS17S17S17S17S17S2dS5aQ40M0A1M1S1cR6Pa0A2S59G0R5A2M2A3S2dG1S1cR7Pa3A2G2A3S2dSeR9S10A3S2dG1S1cR9PbaA2S59G0R6A2A3F_;S2eS5fZ0M3R8A2S61R8S64S63Z2Z3eA2Z18M4A2M5A2A2M6G6S2dSeRcS10A3S2eS5fG3R9A2S61R9G5A2A2F_;S31S5fR7RbA2S5fS5eRbG4A2M7R8A2A2S31S5fR8RbA2S5fG7R9A2A2S2dSeRfS10A3S31S5fRaRcA2S5fS5eRcZ8A2RbA2A2F_;Sa4S1bS1bS2aS29R10R1A2S8S17S17RcRbA4A2Lo';Sa5S6bS1bS70S88R10ReRdRcA4A4A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fal;Fan;Fac;Frho4;Fe;").
Proof.
  intros e rho4 ac an al lo hi E160 E163 E186 Hc Hn Hl Dc Dn Dl. unfold dsN. rewrite map_app. apply Forall_app. split.
  - constructor; [rewrite (dobj_range rho4 (V 160) 0 24 _ ac E160) by lia; unfold ranges_disjoint; cbn [fst snd]; lia|].
    constructor; [rewrite (dobj_range rho4 (V 163) 0 24 _ an E163) by lia; unfold ranges_disjoint; cbn [fst snd]; lia | constructor].
  - destruct e; [|constructor]. specialize (E186 eq_refl). specialize (Hl eq_refl). specialize (Dl eq_refl).
    constructor; [rewrite (dobj_range rho4 (V 186) 0 8 _ al E186) by lia; unfold ranges_disjoint; cbn [fst snd]; lia | constructor].
Qed.

Lemma slot_cell : ltac2:(tb__ "0|1|
S93S0SdS9S17S17A2M0Se8R4R3A2S2dS12G0A1S9cG0S2R4A1R3A3S14G0R2A2A3S94R6S95S5eS5eS1R5A1Z18A2S62Z8S60R4A1A2A2U8S64S13S17S17R3A3Z10A2A3A2F_;F_;Fit;Fj;Fb;Fv;").
Proof. intros v b j it (_ & _ & _ & _ & H5) Hn. exact (proj1 (H5 j it Hn)). Qed.

Lemma slot_carve : ltac2:(tb__ "0|b|
SeS1aS1aS93SbS0A1M0G0S0S0G0SdS9S17S17A2M1S19S19S85RaRcR9R8R7R6R5A7S6eRbS4VA1;A1RaScS0R9S7S0R8S7S0R7R6A3A3A3A4S89RfReRbA3S2dS12G1A1S9cG1S2R9A1R7A3S14G1R6A2A3S61S60SbcSfG1S2RbA1A2R8A2A1Z3fdA2S2dS5aQ40M2A1M3S1eR10R7A2S59G2S5eS5eS1RbA1Z18M4A2S62Z8M5S60R9A1A2A2A2A3S2dG3S1eR11R7A2S59G2S5eS5eS1RdA1G4A2S62G5S60SbcSfG1S2RdA1A2RaA2A1A2A2A2A3S2dG3S1cR12PbdA2S59G2S64S13S17S17RaA3Z10A2A2A3S2dG3S1cR13Pa0A2S59G2S1RfA1A2M6A3S2dG3S1cR14Pa3A2G6A3S2dSeR17S10A3S2dG3S1cR16PbaA2S59G2S98R14A1M7A2A3F_;S2eSa4S6bS72VA1;R16R15Sa5S6bS1bS70S88R18S1R12A1M8S1R11A1M9G7A4A4A4S8fRdRcS5eS5eG9G4A2S62G5S60RfA1A2A2S5eS5eG8G4A2S62G5S60SbcSfG1S2R12A1A2RfA2A1A2A2A4MaA3S9dS6bS7fGaA3A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fbd;Fbs;Fit;Fj;FL;Fn;Fc;FD;FE;Fv;Frho4;FrhoB;Fe;").
Proof.
  intros e rhoB rho4 v E D c n L j it bs bd MC (HBM & _) HE Hnth HJ Ebs Ebd E189 E160 E163 E186.
  pose proof (mc_be _ _ _ _ _ _ _ MC) as BE. set (old := E ++ D ++ c :: n :: L) in *.
  assert (INC : In c old) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  assert (INN : In n old) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  destruct (addr_facts A1 HTH rhoB _ BE (mc_in _ _ _ _ _ _ _ MC c INC)) as (C1 & C2 & C3 & C4 & C5).
  destruct (addr_facts A1 HTH rhoB _ BE (mc_in _ _ _ _ _ _ _ MC n INN)) as (N1 & N2 & N3 & N4 & N5).
  assert (NCN : qb_addr c <> qb_addr n).
  { apply (nodup_mid_ne (E ++ D ++ [c]) L n c); [rewrite <- reassoc1; exact (mc_nd _ _ _ _ _ _ _ MC) | apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; left; reflexivity]. }
  pose proof (apart_in rhoB c n old BE (mc_in _ _ _ _ _ _ _ MC) INC INN NCN) as APcn.
  assert (JN : (j < length (qb_items n))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hnth; discriminate).
  pose proof (mc_cap _ _ _ _ _ _ _ MC n INN) as CPN.
  assert (LE : e = true -> 0 <= last_addr E < 2 ^ 62 - 24 /\ (last_addr E + 8192 <= qb_addr c \/ qb_addr c + 8192 <= last_addr E) /\ (last_addr E + 8192 <= qb_addr n \/ qb_addr n + 8192 <= last_addr E)).
  { intros He. pose proof (e_ne _ _ _ HE He) as NE. pose proof (in_last_E E (D ++ c :: n :: L) NE) as INL. fold old in INL.
    destruct (addr_facts A1 HTH rhoB _ BE (mc_in _ _ _ _ _ _ _ MC _ INL)) as (L1 & L2 & L3 & L4 & L5).
    assert (X1 : qb_addr (last E qb_dflt) <> qb_addr c).
    { apply (nodup_mid_ne (E ++ D) (n :: L) c _); [unfold old in *; rewrite <- app_assoc; exact (mc_nd _ _ _ _ _ _ _ MC) | apply in_or_app; left; apply in_or_app; left; apply In_last; exact NE]. }
    assert (X2 : qb_addr (last E qb_dflt) <> qb_addr n).
    { apply (nodup_mid_ne (E ++ D ++ [c]) L n _); [rewrite <- reassoc1; exact (mc_nd _ _ _ _ _ _ _ MC) | apply in_or_app; left; apply in_or_app; left; apply In_last; exact NE]. }
    pose proof (apart_in rhoB _ c old BE (mc_in _ _ _ _ _ _ _ MC) INL INC X1). pose proof (apart_in rhoB _ n old BE (mc_in _ _ _ _ _ _ _ MC) INL INN X2). unfold last_addr. lia. }
  pose proof (proj1 (Forall_forall _ _) HBM c INC) as (_ & _ & _ & PRc & _). pose proof (proj1 (Forall_forall _ _) HBM n INN) as BMn. pose proof BMn as (_ & _ & _ & PRn & _).
  unfold kQuarantineBatchSize in PRc, PRn.
  split.
  - unfold dsS. constructor; [|constructor; [|constructor]].
    + unfold carve_cond. split; [exact Ebs|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [apply ci1|].
      split; [intros z Hz; apply PRn; lia|].
      split; [constructor; [exists (fst it - 16); split; [exact E189 | replace (qb_addr n + 24 + 8 * Z.of_nat j + 0) with (qb_addr n + 24 + 8 * Z.of_nat j) by lia; exact (slot_cell v n j it BMn Hnth)] | constructor]|].
      apply (dsN_disj e rho4 _ _ _ _ _ E160 E163 E186); try lia; intros He; destruct (LE He); lia.
    + unfold carve_cond. split; [exact Ebd|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold cells_inside; constructor|]. split; [intros z Hz; apply PRc; lia|]. split; [constructor|].
      apply (dsN_disj e rho4 _ _ _ _ _ E160 E163 E186); try lia; intros He; destruct (LE He); lia.
  - unfold dsS. constructor; [constructor; [unfold apart_d; lia | constructor] | constructor; [constructor | constructor]].
Qed.

Lemma slot_diss : ltac2:(tb__ "0|4|
S1aS93SbS0A1M0G0S0S0G0SdS9S17S17A2M1S85R8R9R7R6R5R4R3A7S87RaR6R5R3R2A5S61S60SbcSfG1S2R7A1A2R4A2A1Z3fdA2Sa4S6bS73VA1;RcA2S8cS5eS5eS1R7A1Z18M2A2S62Z8M3S60R5A1A2A2S5eS5eS1R8A1G2A2S62G3S60SbcSfG1S2R8A1A2R5A2A1A2A2A2A3F_;F_;F_;Fit;Fj;FL;Fn;Fc;FD;FE;Fv;Frho;").
Proof.
  intros rho v E D c n L j it MC (E169 & E170 & E188 & Hnth) HJ. pose proof (mc_be _ _ _ _ _ _ _ MC) as BE. set (old := E ++ D ++ c :: n :: L) in *.
  assert (INC : In c old) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  assert (INN : In n old) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  destruct (addr_facts A1 HTH rho _ BE (mc_in _ _ _ _ _ _ _ MC c INC)) as (C1 & C2 & C3 & C4 & C5).
  destruct (addr_facts A1 HTH rho _ BE (mc_in _ _ _ _ _ _ _ MC n INN)) as (N1 & N2 & N3 & N4 & N5).
  assert (JN : (j < length (qb_items n))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hnth; discriminate).
  pose proof (mc_cap _ _ _ _ _ _ _ MC n INN) as CPN.
  unfold dsSd. constructor; [|constructor; [|constructor]]; unfold diss_cond.
  - split; [exact E169|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [apply ci1|].
    intros z Hz. apply (addr_in_QW A1 HTH rho (qb_addr n) z BE (mc_in _ _ _ _ _ _ _ MC n INN)). lia.
  - split; [exact E170|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [apply ci1|].
    intros z Hz. apply (addr_in_QW A1 HTH rho (qb_addr c) z BE (mc_in _ _ _ _ _ _ _ MC c INC)). lia.
Qed.

Lemma cp_mem : ltac2:(tb__ "0|6|
S93S93S1aSbS0A1M0G0S0S0G0SdS9S17S17A2M1S85RaR8R7R6R5R4R3A7S68Vall;R8ScS0R7S7S0R6S7S0R5R4A3A3A3A3S6eRcS4VA1;A1M2R9ScS0R8S7S0R7S7S0R6R5A3A3A3A4S76RdR8R7R5A4S87RcR9R8R6R5A5S61S60SbcSfG1S2RaA1A2R7A2A1Z3fdA2S17S30S74S8cS5eS5eS1RbA1Z18M3A2S62Z8M4S60R9A1A2A2S5eS5eS1RcA1G3A2S62G4S60SbcSfG1S2RcA1A2R9A2A1A2A2A2M5R1A2A1S2dS12S5aQ8A1A1R11R2A1R12R2A1A3F_;Fz;Sa4S6bS6fRfR10A2G5A3S2eS6eR11G2RfScS0ReS7S0RdS7S0RcRbA3A3A3A4S76R11RdRcS15RaA1A4A2F_;F_;F_;F_;F_;F_;F_;F_;Fit;Fj;FL;Fn;Fc;FD;FE;Frho;Fv3;Fv;").
Proof.
  intros v v3 rho E D c n L j it MC HGI HMM HCP (E169 & E170 & E188 & Hnth) HJ FR AV. pose proof (mc_be _ _ _ _ _ _ _ MC) as BE.
  unfold dsSd in AV. apply Forall_cons_iff in AV as [AVs AV]. apply Forall_cons_iff in AV as [AVd _].
  assert (INN : In n (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  pose proof (slot_cell v n j it (proj1 (Forall_forall _ _) (proj1 HMM) n INN) Hnth) as CS.
  pose proof (res_cell rho v3 _ _ _ _ _ 0 8%nat (V 188) (fst it - 16) AVs ltac:(cbn; tauto) E188) as CS3. rewrite Z.add_0_r in CS3.
  pose proof (res_cell rho v3 _ _ _ _ _ 0 8%nat (V 188) (fst it - 16) AVd ltac:(cbn; tauto) E188) as CD3. rewrite Z.add_0_r in CD3.
  apply (mmem_copy A1 HTH rho v v3 E D c n L j it BE HGI HMM HCP Hnth); [unfold kQuarantineBatchCount; exact HJ | | exact CD3].
  intros z Hz. destruct (dzone_dec (dsSd (qb_addr n + 24 + 8 * Z.of_nat j) (qb_addr c + 24 + 8 * Z.of_nat (length (qb_items c) + j))) z) as [HD|HD]; [|exact (FR z HD)].
  unfold dsSd, dzone in HD. inversion HD as [? ? Hs|? ? HD2]; subst.
  - apply (cell_ok_same v v3 _ CS CS3). cbn. lia.
  - inversion HD2 as [? ? Hd|? ? HD3]; subst; [exfalso; apply Hz; lia | inversion HD3].
Qed.

Lemma others_cp0 : ltac2:(tb__ "0|0|
SeS17S17S17S2dSbS1bA1Sa6S1bU9S25S83S71S48R4A1A1A1A1A3Sa5S6bS1bS70S88R4R3R2R1A4A4A3Fal;Fan;Fac;Fe;"). Proof. intros [|] ac an al; reflexivity. Qed.
Lemma others_cpn : ltac2:(tb__ "0|0|
SeS17S17S17S2dSbS1bA1Sa6S1bU9S25S83S71S49R4A1A1A1A1A3Sa5S6bS1bS70S88R4R3R2R1A4A4A3Fal;Fan;Fac;Fe;"). Proof. intros [|] ac an al; reflexivity. Qed.
Lemma cap_sum : ltac2:(tb__ "0|3|
SeS82S1aSbS0A1M0G0S0S0G0SbS5aQ40A1A1Sa2S5dS85S97S5bS2bR9A1A2R9R8R7R6R5R4A7S84RcRaR9R8R7R6R5A7S5cS5bR3RcRbR5R4A6S2dSeS9bS1dS27S23S21SdfS1fZ3fdM1A1S36A3A1A1S24S83RdA1A1A3S10A3S5fS60SbcSfS9S17S17A2M2S2RaA1A2SfG2S2R9A1A2A2A1G1A2F_;F_;F_;F_;FJ;Fw;Ftp;FL;Fn;Fc;FD;FE;Frho;FC;Fe;").
Proof.
  intros e C rho E D c n L tp w J MC (_ & _ & (_ & _ & B162 & _ & _ & _ & B166)) H HB.
  assert (INC : In c (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  assert (INN : In n (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  pose proof (mc_cap _ _ _ _ _ _ _ MC c INC). pose proof (mc_cap _ _ _ _ _ _ _ MC n INN).
  rewrite Nat2Z.inj_add, Z.add_comm. apply (cap_of_fact rho _ _ B162 B166 ltac:(lia) ltac:(lia)). exact (fact_in _ _ rho tp _ _ H HB).
Qed.

Lemma cp0_glue : ltac2:(tb__ "0|3|
SeSbS0A1M0G0S0S0G0S1aSbS5aQ40A1A1Sa2S68Vall;R8ScS0R7S7S0R6S7S0R5R4A3A3A3A3S84RaR4R9R8R7R6R5A7S5cS5bS67VK;VA0;Vrho0;VA1;RaScS0R9S7S0R8S7S0R7R6A3A3A3R8R7U0M1A9S35SaaRbA1U4A2R5R4R3A6S2fS1aS1aS2fS9S17S17A2M2G2S2eS5cS5bS67VK;VA0;Vrho0;VA1;RdScS0RcS7S0RbS7S0RaR9A3A3A3RbRaG1A9Sb1ReA1R2R7R6A6S2eS84ReR2RdRcRbRaR9A7S87R2RbRaG1R1A5A2A2Lit;A2Lrho5;A2F_;F_;F_;Fw;Ftp;Frho;FL;Fn;Fc;FD;FE;Fe;").
Proof.
  intros e E D c n L rho tp [tr [ms md]] HGI HV H.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ HGI) as MC. destruct HJ as (HK & (HMM & HCP) & HFRM).
  pose proof (mc_be _ _ _ _ _ _ _ MC) as BE.
  pose proof HV as (HG & HE & (B160 & B161 & B162 & B163 & B164 & B165 & B166)).
  assert (INC : In c (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  assert (INN : In n (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  pose proof (mc_cap _ _ _ _ _ _ _ MC c INC) as CPC. pose proof (mc_cap _ _ _ _ _ _ _ MC n INN) as CPN.
  destruct (addr_facts A1 HTH rho _ BE (mc_in _ _ _ _ _ _ _ MC c INC)) as (C1 & C2 & C3 & C4 & C5).
  destruct (addr_facts A1 HTH rho _ BE (mc_in _ _ _ _ _ _ _ MC n INN)) as (N1 & N2 & N3 & N4 & N5).
  pose proof (cap_sum e _ rho E D c n L tp _ _ MC HV H ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as HCAP.
  assert (EX : exists it, nth_error (qb_items n) 0 = Some it).
  { assert (F : holds rho (SPNot (SPBranch BC_EQ (V 166) (SLit 0)))) by (apply (fact_in _ _ rho tp _ _ H); destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    destruct (qb_items n) as [|it0 r] eqn:EI; [|exists it0; reflexivity]. exfalso. apply F. cbn [holds branch_taken eval V]. rewrite B166. reflexivity. }
  destruct EX as (it & Hnth).
  assert (JN : (0 < length (qb_items n))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hnth; discriminate).
  destruct (m_step K HL A0 rho0 A1 HQW (T_cp0 e) (JRM E (D ++ c :: n :: L) c n 0) []
              (dsS (add (V 163) (SLit 24)) dstE (qb_addr n + 24 + 8 * Z.of_nat 0) (qb_addr c + 24 + 8 * Z.of_nat (length (qb_items c) + 0))) [Z_to_bv 64 (fst it - 16)] rho tp tr ms md) as (rho5 & H5 & V5).
  - apply T_ok. destruct e; cbn; tauto.
  - exact (JRM_stable K HL A0 rho0 A1 _ _ _ _ _).
  - destruct e; reflexivity.
  - reflexivity.
  - reflexivity.
  - split; [exact (proj1 H) | exact I].
  - exact HK.
  - exact HFRM.
  - exact (be_top _ _ BE).
  - constructor.
  - intros HK3 HF3 FR AV.
    set (rho3 := rho_absorb rho (map dobj []) (vms md tp ms)) in *. set (v3 := view segsA (rm rho3)) in *.
    set (rho4 := rho_sets rho3 (combine (t_bs (T_cp0 e)) [Z_to_bv 64 (fst it - 16)])).
    assert (OTH : forall i, ~ In i [189]%positive -> rw rho4 i = rw rho i) by (intros i Hi; unfold rho4, rho3; apply rw_sets_absorb; exact Hi).
    assert (HMM3 : MMEM v3 (aa_geom A1) E (D ++ c :: n :: L)) by (apply (MMEM_ext _ _ _ _ _ (fun z => FR z (dz_nil z))); exact HMM).
    assert (HJ3 : JRM E (D ++ c :: n :: L) c n 0 rho3 tp tr md) by (split; [exact HK3|]; split; [|exact HF3]; split; [exact HMM3 | intros i it' Hi; lia]).
    pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ3 HGI) as MC3. fold v3 in MC3.
    split; [exact HJ3|]. rewrite (others_cp0 e (qb_addr c) (qb_addr n) (last_addr E)).
    assert (HE3 : HVE e rho3 E) by exact HE.
    destruct (slot_carve e rho3 rho4 v3 E D c n L 0 it (add (V 163) (SLit 24)) dstE MC3 HMM3 HE3 Hnth ltac:(lia)) as [SC1 SC2].
    + replace (qb_addr n + 24 + 8 * Z.of_nat 0) with (qb_addr n + 24) by lia. apply eval_addl; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact B163 | lia | lia | lia].
    + unfold dstE. replace (qb_addr c + 24 + 8 * Z.of_nat (length (qb_items c) + 0)) with (qb_addr c + Z.of_nat (length (qb_items c)) * 2 ^ 3 + 24) by lia.
      apply eval_addl; [|lia | lia | lia]. apply eval_add_z; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact B160 | | lia | lia | lia].
      apply eval_sllk; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact B162 | lia | lia | lia].
    + reflexivity.
    + rewrite OTH by (cbn; intuition discriminate). exact B160.
    + rewrite OTH by (cbn; intuition discriminate). exact B163.
    + intros He. rewrite OTH by (cbn; intuition discriminate). destruct HE as (_ & _ & HE'). exact (proj1 (proj2 (proj2 (HE' He)))).
    + split; [exact SC1|]. split; [exact SC2 | intros _; constructor].
  - exists rho5, it. split; [exact H5|].
    set (rho4 := rho_sets _ _) in V5.
    assert (OTH : forall i, ~ In i [189]%positive -> rw rho4 i = rw rho i) by (intros i Hi; unfold rho4; apply rw_sets_absorb; exact Hi).
    split.
    + apply (HVM_vals e rho rho5); [|exact HV]. intros v Hv.
      rewrite (V5 v (V v)) by (unfold T_cp0, idm; cbn [t_M]; apply in_or_app; left; apply in_map_iff; exists v; split; [reflexivity | exact Hv]).
      cbn [eval V]. apply OTH. intros [X|[]]. subst v. destruct e; cbn in Hv; intuition discriminate.
    + unfold HVCp. rewrite (V5 169%positive (add (V 163) (SLit 24))), (V5 170%positive dstE), (V5 188%positive (V 189)) by (unfold T_cp0; cbn [t_M]; apply in_or_app; right; cbn; tauto).
      split; [replace (qb_addr n + 24 + 8 * Z.of_nat 0) with (qb_addr n + 24) by lia; apply eval_addl; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact B163 | lia | lia | lia]|].
      split; [|split; [reflexivity | exact Hnth]].
      unfold dstE. replace (qb_addr c + 24 + 8 * Z.of_nat (length (qb_items c) + 0)) with (qb_addr c + Z.of_nat (length (qb_items c)) * 2 ^ 3 + 24) by lia.
      apply eval_addl; [|lia | lia | lia]. apply eval_add_z; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact B160 | | lia | lia | lia].
      apply eval_sllk; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact B162 | lia | lia | lia].
Qed.

Lemma eval_endC : ltac2:(tb__ "0|5|
S1aS17S17S2dS5aQ40M0A1M1S1cR3Pa3A2S59G0R2A2M2A3S2dG1S1cR4Pa6A2G2A3S2eS5fZ0R4A2M3S61R4S63Z2M4Z3eA2A2A2S2eG3S5fR4Z3fdA2A2S2dG1S1eR7Sb4A2S59G0S5eS5eR6Z18A2S62R5S63G4Z3A2A2A2A2A3F_;F_;F_;F_;Fcn;Fan;Frho;").
Proof.
  intros rho an cn E1 E2 H1 H2. unfold endC. apply eval_add_z; [apply eval_addl; [exact E1 | lia | lia | lia] | apply eval_sllk; [exact E2 | lia | lia | lia] | lia | lia | lia].
Qed.

Lemma cpn_glue : ltac2:(tb__ "0|3|
SeSbS0A1M0G0S0S0G0SdS9S17S17A2M1S1aSbS5aQ40A1A1Sa2S68Vall;RaScS0R9S7S0R8S7S0R7R6A3A3A3A3S84RcR4RbRaR9R8R7A7S87R5RaR9R7R6A5S5cS5bS67VK;VA0;Vrho0;VA1;RdScS0RcS7S0RbS7S0RaR9A3A3A3RbRaR8A9S35Sb0ReA1U0A2R6R5R4A6S2fS1aS1aS2fG1G1S2eS5cS5bS67VK;VA0;Vrho0;VA1;R10ScS0RfS7S0ReS7S0RdRcA3A3A3ReRdS15RbA1M2A9Sb1R11A1R2R8R7A6S2eS84R11R2R10RfReRdRcA7S87R2ReRdG2R1A5A2A2Lit';A2Lrho5;A2F_;F_;F_;F_;Fw;Ftp;Frho;Fit;Fj;FL;Fn;Fc;FD;FE;Fe;").
Proof.
  intros e E D c n L j it rho tp [tr [ms md]] HGI HV HC H.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ HGI) as MC. destruct HJ as (HK & (HMM & HCP) & HFRM).
  pose proof (mc_be _ _ _ _ _ _ _ MC) as BE.
  pose proof HV as (HG & HE & (B160 & B161 & B162 & B163 & B164 & B165 & B166)). pose proof HC as (E169 & E170 & E188 & Hnth).
  assert (INC : In c (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  assert (INN : In n (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  pose proof (mc_cap _ _ _ _ _ _ _ MC c INC) as CPC. pose proof (mc_cap _ _ _ _ _ _ _ MC n INN) as CPN.
  destruct (addr_facts A1 HTH rho _ BE (mc_in _ _ _ _ _ _ _ MC c INC)) as (C1 & C2 & C3 & C4 & C5).
  destruct (addr_facts A1 HTH rho _ BE (mc_in _ _ _ _ _ _ _ MC n INN)) as (N1 & N2 & N3 & N4 & N5).
  pose proof (cap_sum e _ rho E D c n L tp _ _ MC HV H ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as HCAP.
  assert (JN : (j < length (qb_items n))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hnth; discriminate).
  assert (EX : exists it', nth_error (qb_items n) (S j) = Some it').
  { assert (F : holds rho (SPBranch BC_NE (add (V 169) (SLit 8)) endC)) by (apply (fact_in _ _ rho tp _ _ H); destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    cbn [holds branch_taken] in F. rewrite (eval_endC rho _ _ B163 B166 ltac:(lia) ltac:(lia)) in F.
    rewrite (eval_addl rho (V 169) _ 8 E169 ltac:(lia) ltac:(lia) ltac:(lia)) in F. apply negb_true_iff in F. unfold bv_eqb in F. apply Z.eqb_neq in F. rewrite !u64_lit in F by lia.
    destruct (nth_error (qb_items n) (S j)) as [it'|] eqn:EN; [exists it'; reflexivity|]. apply nth_error_None in EN. lia. }
  destruct EX as (it' & Hnth').
  assert (JN' : (S j < length (qb_items n))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hnth'; discriminate).
  set (asrc := qb_addr n + 24 + 8 * Z.of_nat j) in *. set (adst := qb_addr c + 24 + 8 * Z.of_nat (length (qb_items c) + j)) in *.
  destruct (m_step K HL A0 rho0 A1 HQW (T_cpn e) (JRM E (D ++ c :: n :: L) c n (S j)) (dsSd asrc adst)
              (dsS (add (V 169) (SLit 8)) (add (V 170) (SLit 8)) (qb_addr n + 24 + 8 * Z.of_nat (S j)) (qb_addr c + 24 + 8 * Z.of_nat (length (qb_items c) + S j))) [Z_to_bv 64 (fst it' - 16)] rho tp tr ms md) as (rho5 & H5 & V5).
  - apply T_ok. destruct e; cbn; tauto.
  - exact (JRM_stable K HL A0 rho0 A1 _ _ _ _ _).
  - destruct e; reflexivity.
  - reflexivity.
  - reflexivity.
  - split; [exact (proj1 H) | exact I].
  - exact HK.
  - exact HFRM.
  - exact (be_top _ _ BE).
  - exact (slot_diss rho _ E D c n L j it MC HC ltac:(lia)).
  - intros HK3 HF3 FR AV.
    destruct (cp_mem _ _ rho E D c n L j it MC HGI HMM HCP HC ltac:(lia) FR AV) as [HMM3 HCP3].
    set (rho3 := rho_absorb rho (map dobj (dsSd asrc adst)) (vms md tp ms)) in *. set (v3 := view segsA (rm rho3)) in *.
    set (rho4 := rho_sets rho3 (combine (t_bs (T_cpn e)) [Z_to_bv 64 (fst it' - 16)])).
    assert (OTH : forall i, ~ In i [189]%positive -> rw rho4 i = rw rho i) by (intros i Hi; unfold rho4, rho3; apply rw_sets_absorb; exact Hi).
    assert (HJ3 : JRM E (D ++ c :: n :: L) c n (S j) rho3 tp tr md) by (split; [exact HK3|]; split; [|exact HF3]; split; [exact HMM3 | exact HCP3]).
    pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ3 HGI) as MC3. fold v3 in MC3.
    split; [exact HJ3|]. rewrite (others_cpn e (qb_addr c) (qb_addr n) (last_addr E)).
    assert (HE3 : HVE e rho3 E) by exact HE.
    destruct (slot_carve e rho3 rho4 v3 E D c n L (S j) it' (add (V 169) (SLit 8)) (add (V 170) (SLit 8)) MC3 HMM3 HE3 Hnth' ltac:(lia)) as [SC1 SC2].
    + replace (qb_addr n + 24 + 8 * Z.of_nat (S j)) with (asrc + 8) by (unfold asrc; lia). apply eval_addl; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact E169 | unfold asrc; lia | lia | unfold asrc; lia].
    + replace (qb_addr c + 24 + 8 * Z.of_nat (length (qb_items c) + S j)) with (adst + 8) by (unfold adst; lia). apply eval_addl; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact E170 | unfold adst; lia | lia | unfold adst; lia].
    + reflexivity.
    + rewrite OTH by (cbn; intuition discriminate). exact B160.
    + rewrite OTH by (cbn; intuition discriminate). exact B163.
    + intros He. rewrite OTH by (cbn; intuition discriminate). destruct HE as (_ & _ & HE'). exact (proj1 (proj2 (proj2 (HE' He)))).
    + split; [exact SC1|]. split; [exact SC2 | intros _; constructor].
  - exists rho5, it'. split; [exact H5|].
    set (rho4 := rho_sets _ _) in V5.
    assert (OTH : forall i, ~ In i [189]%positive -> rw rho4 i = rw rho i) by (intros i Hi; unfold rho4; apply rw_sets_absorb; exact Hi).
    split.
    + apply (HVM_vals e rho rho5); [|exact HV]. intros v Hv.
      rewrite (V5 v (V v)) by (unfold T_cpn, idm; cbn [t_M]; apply in_or_app; left; apply in_map_iff; exists v; split; [reflexivity | exact Hv]).
      cbn [eval V]. apply OTH. intros [X|[]]. subst v. destruct e; cbn in Hv; intuition discriminate.
    + unfold HVCp. rewrite (V5 169%positive (add (V 169) (SLit 8))), (V5 170%positive (add (V 170) (SLit 8))), (V5 188%positive (V 189)) by (unfold T_cpn; cbn [t_M]; apply in_or_app; right; cbn; tauto).
      split; [replace (qb_addr n + 24 + 8 * Z.of_nat (S j)) with (asrc + 8) by (unfold asrc; lia); apply eval_addl; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact E169 | unfold asrc; lia | lia | unfold asrc; lia]|].
      split; [|split; [reflexivity | exact Hnth']].
      replace (qb_addr c + 24 + 8 * Z.of_nat (length (qb_items c) + S j)) with (adst + 8) by (unfold adst; lia). apply eval_addl; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact E170 | unfold adst; lia | lia | unfold adst; lia].
Qed.

Lemma cpe_glue : ltac2:(tb__ "0|2|
SeSbS0A1M0G0S0S0G0SdS9S17S17A2M1S1aSbS5aQ40A1A1Sa2S68Vall;RaScS0R9S7S0R8S7S0R7R6A3A3A3A3S84RcR4RbRaR9R8R7A7S87R5RaR9R7R6A5S5cS5bS67VK;VA0;Vrho0;VA1;RdScS0RcS7S0RbS7S0RaR9A3A3A3RbRaR8A9S35Sb0ReA1U1A2R6R5R4A6S2fS1aS1aS2eS5cS5bS67VK;VA0;Vrho0;VA1;RfScS0ReS7S0RdS7S0RcRbA3A3A3RdRcSfG1S2RcA1A2A9SaeR10A1R1R7R6A6S84R10R1RfReRdRcRbA7A2Lrho5;A2F_;F_;F_;F_;Fw;Ftp;Frho;Fit;Fj;FL;Fn;Fc;FD;FE;Fe;").
Proof.
  intros e E D c n L j it rho tp [tr [ms md]] HGI HV HC H.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ HGI) as MC. destruct HJ as (HK & (HMM & HCP) & HFRM).
  pose proof (mc_be _ _ _ _ _ _ _ MC) as BE.
  pose proof HV as (HG & HE & (B160 & B161 & B162 & B163 & B164 & B165 & B166)). pose proof HC as (E169 & E170 & E188 & Hnth).
  assert (INC : In c (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  assert (INN : In n (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  pose proof (mc_cap _ _ _ _ _ _ _ MC c INC) as CPC. pose proof (mc_cap _ _ _ _ _ _ _ MC n INN) as CPN.
  destruct (addr_facts A1 HTH rho _ BE (mc_in _ _ _ _ _ _ _ MC n INN)) as (N1 & N2 & N3 & N4 & N5).
  pose proof (cap_sum e _ rho E D c n L tp _ _ MC HV H ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as HCAP.
  assert (JN : (j < length (qb_items n))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hnth; discriminate).
  assert (SJ : S j = length (qb_items n)).
  { assert (F : holds rho (SPNot (SPBranch BC_NE (add (V 169) (SLit 8)) endC))) by (apply (fact_in _ _ rho tp _ _ H); destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    cbn [holds branch_taken] in F. rewrite (eval_endC rho _ _ B163 B166 ltac:(lia) ltac:(lia)) in F.
    rewrite (eval_addl rho (V 169) _ 8 E169 ltac:(lia) ltac:(lia) ltac:(lia)) in F.
    destruct (Nat.eq_dec (S j) (length (qb_items n))) as [EQ|NE]; [exact EQ|]. exfalso. apply F. apply negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
  set (asrc := qb_addr n + 24 + 8 * Z.of_nat j) in *. set (adst := qb_addr c + 24 + 8 * Z.of_nat (length (qb_items c) + j)) in *.
  destruct (m_step K HL A0 rho0 A1 HQW (T_cpe e) (JRM E (D ++ c :: n :: L) c n (length (qb_items n))) (dsSd asrc adst) [] [] rho tp tr ms md) as (rho5 & H5 & V5).
  - apply T_ok. destruct e; cbn; tauto.
  - exact (JRM_stable K HL A0 rho0 A1 _ _ _ _ _).
  - destruct e; reflexivity.
  - reflexivity.
  - reflexivity.
  - split; [exact (proj1 H) | exact I].
  - exact HK.
  - exact HFRM.
  - exact (be_top _ _ BE).
  - exact (slot_diss rho _ E D c n L j it MC HC ltac:(lia)).
  - intros HK3 HF3 FR AV.
    destruct (cp_mem _ _ rho E D c n L j it MC HGI HMM HCP HC ltac:(lia) FR AV) as [HMM3 HCP3]. rewrite SJ in HCP3.
    split; [split; [exact HK3|]; split; [|exact HF3]; split; [exact HMM3 | exact HCP3]|]. split; [constructor | split; [constructor | intros _; constructor]].
  - exists rho5. split; [exact H5|]. apply (HVM_vals e rho rho5); [|exact HV]. intros v Hv.
    rewrite (V5 v (V v)) by (unfold T_cpe, idm; cbn [t_M]; apply in_map_iff; exists v; split; [reflexivity | exact Hv]). reflexivity.
Qed.

Hypothesis HREG : KQ_regroup K.
Definition HVTq (rho : valuation) (E : list qbatch) : Prop := ltac2:(tb__ "0|4|
S2eS2dS5aQ40M0A1M1S1cVrho;Pa6A2S59G0S98VE;A1A2M2A3S2eS2dG1S1cVrho;Pa8A2S59G0S60SfS0VE;A2A1A2M3A3S2eS2dG1S1cVrho;Pa9A2S59G0S99VE;A1A2A3S2eS2dG1S1cVrho;PaaA2S59G0S91VE;A1A2A3S2eS2dG1S1cVrho;Pc0A2G3A3S2dG1S1cVrho;Pc1A2G2A3A2A2A2A2A2").

Lemma L_nil_iff : ltac2:(tb__ "0|2|
SeS93S1aSbS0A1M0G0S0S0G0S85R7R6R5R4R3R2R1A7S84R9R7R6R5R4R3R2A7S32S2dG0R3SaS0A1A3S2dS5aQ40M1A1S1cR8Pa4A2S59G1Z0A2A3A2F_;F_;FL;Fn;Fc;FD;FE;Frho;Fv;Fe;").
Proof.
  intros e v rho E D c n L MC (_ & _ & (_ & _ & _ & _ & B164 & _)). split; [intros ->; exact B164|]. intros E0. destruct L as [|l0 L']; [reflexivity|]. exfalso.
  assert (INL : In l0 (E ++ D ++ c :: n :: l0 :: L')) by (apply in_or_app; right; apply in_or_app; right; right; right; left; reflexivity).
  destruct (addr_facts A1 HTH rho _ (mc_be _ _ _ _ _ _ _ MC) (mc_in _ _ _ _ _ _ _ MC l0 INL)) as (F1 & _ & F3 & _). rewrite B164 in E0. unfold hd_addr in E0. cbn [hd] in E0.
  apply (f_equal bv_unsigned) in E0. rewrite !u64_lit in E0 by lia. lia.
Qed.
Lemma gsize_eq : ltac2:(tb__ "0|1|
SbS0A1M0G0S68Vall;R2R1A3S2dS17S91R2A1S64S91Vall;A1S91R3A1A2A3F_;Fglob;FE;").
Proof. intros E glob (_ & _ & _ & _ & QS). rewrite qsize_app in QS. lia. Qed.
Lemma regroup_K : ltac2:(tb__ "0|1|
SbS0A1M0G0S1aSbS5aQ40A1A1SbSf7A1Sf6S68Vall;R6R5A3VK;VA1;R5R4R3R2A5VK;Se6VA1;SaS0A1ScS0R8R7A3A3R6R5R4R3A5F_;F_;Fmd;Ftr;Ftp;Frho;Fglob;FE;").
Proof.
  intros E glob rho tp tr md (P1 & P2 & FC & _) HK. apply (HREG A1 [] (E ++ glob) rho tp tr md); [rewrite (qall_A1 A1 HTH); exact P1 | rewrite (qall_A1 A1 HTH); exact P2 | exact FC | exact HK].
Qed.

Lemma xh_common : ltac2:(tb__ "0|6|
SeSbS0A1M0G0S0S0G0S1aSbSf7A1M1Sf8Sf6SbS5aQ40A1M2A1S69S67VK;VA0;Vrho0;VA1;RbScS0RaS7S0R9S7S0R8R7A3A3A3S90S90U0M3A9S5dS9aS69R2S3dA3S2dSbS1bA1M4S7aR3A1SaS1bA1A3S2dSbS18A1S7cR4A1SaS18A1A3S17S17S17S2dG4S25S83S75R8A1M5A1A1ScS1bS77G5S7dR8A1A2Sa5S6bS1bS70S88R13R3R2R1A4A4A3A3Fal;Fan;Fac;S68Vall;R10ScS0RfS7S0ReS7S0RdRcA3A3A3A3S84R12RcR11R10RfReRdA7S5cS5bS67VK;VA0;Vrho0;VA1;R12ScS0R11S7S0R10S7S0RfReA3A3A3R10RfG3A9G5RdR9S8G1Sf4RcSf5RbRaA2A4A6Sa4S1dS20ReA1S24S83S71R9A1A1A1A3Sa4S1dS20RfA1S78RaA1A3F_;S2fS1aS1aS2eS5cS5bRaS7bRbA1R1RcS8G1Sf4RfSf5ReRdA2A4A6S18S19S9aS9S18S19A2S8S18S19R2R1A4S79RdA1A3S2dG2S1cR4R3A2S1eR13R2A2A3F_;Fex;Fv;A2Lrho5;A2F_;F_;F_;F_;F_;F_;F_;F_;TJ';Ft;Ftp;Fmd;Fms;Ftr;Frho;FL;Fn;Fc;FD;FE;Fe;").
Proof.
  intros e E D c n L rho tr ms md tp t J' HIN HOC HBS HOBJ HGI HV H HFN.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ HGI) as MC. destruct HJ as (HK & (HMM & _) & HFRM). pose proof (mc_be _ _ _ _ _ _ _ MC) as BE.
  destruct (m_step K HL A0 rho0 A1 HQW t J' (dsN e (qb_addr c) (qb_addr n) (last_addr E)) [] [] rho tp tr ms md) as (rho5 & H5 & V5).
  - exact (T_ok t HIN).
  - exact (JRM_stable K HL A0 rho0 A1 _ _ _ _ _).
  - apply HOBJ.
  - rewrite HOC. reflexivity.
  - rewrite HBS. reflexivity.
  - split; [exact (proj1 H) | exact I].
  - exact HK.
  - exact HFRM.
  - exact (be_top _ _ BE).
  - exact (dsN_cond e _ rho E D c n L MC HV).
  - intros HK3 HF3 FR AV. pose proof (dsN_same e _ _ rho E D c n L MC HV FR AV) as SAME.
    split; [split; [exact HK3|]; split; [|exact HF3]; split; [apply (MMEM_ext _ _ _ _ _ SAME); exact HMM | intros i it Hi; lia]|].
    split; [constructor|]. split; [constructor|]. rewrite HBS. cbn [combine rho_sets]. intros HF4. apply Forall_forall. intros f Hf.
    apply (proj2 (holds_absorb rho _ _ f)). refine (proj1 (Forall_forall _ _) (HFN _) f Hf). apply Forall_forall. intros g Hg.
    apply (proj1 (holds_absorb rho (map dobj (dsN e (qb_addr c) (qb_addr n) (last_addr E))) (vms md tp ms) g)). exact (proj1 (Forall_forall _ _) HF4 g Hg).
  - exists rho5. split; [exact H5|]. intros v ex Hin. rewrite (V5 v ex Hin). rewrite HBS. cbn [combine rho_sets]. apply eval_absorb.
Qed.

Lemma hd_in : ltac2:(tb__ "0|2|
SbS0A1M0S0G0S9aS0S9fS0S90ScS0R3S7S0R2R1A3A3M1A3G1A3FR;Fc;FD;").
Proof. intros [|d D'] c R; cbn [app hd]; left; reflexivity. Qed.
Lemma eval_qs : ltac2:(tb__ "0|6|
S1aSbS0A1M0G0S19S68Vall;R3R2A3S2dS5aQ40M1A1M2S1cR5PcfM3A2S59G1S91Vall;A1M4A2A3S2dG2S1eR6R3A2S59G1S91R5A1A2A3S2eS5fZ0S91R6A1M5A2S5fG5G4A2A2S2dG2S1eR8S22SdcS34G3A1R5A3A2S59G1G5A2A3F_;F_;F_;F_;Fx;Fglob;FE;Frho;").
Proof. intros rho E glob x HGI E207 Ex HB. rewrite (gsize_eq E glob HGI). apply eval_subz; [exact E207 | exact Ex | lia | lia]. Qed.
Lemma min_of_fact : ltac2:(tb__ "0|3|
S1aS17S19S2dS5aQ40M0A1M1S1cR3Pd0M2A2S59G0Sd9A2A3S2dG1S1eR4R2A2S59G0R3A2A3S2eS5fZ0R4A2S61R4S63Z2Z40A2A2A2S20R6S21SdeS34G2A1R4A3A2S5fR6Sd9A2F_;F_;F_;F_;Fx;Fq;Frho;").
Proof.
  intros rho q x E208 Ex Hq F. cbn [holds branch_taken eval V] in F. rewrite E208, Ex in F. apply negb_true_iff in F. unfold bv_ltu in F. apply Z.ltb_ge in F.
  rewrite !u64_lit in F by (unfold kQuarantineMin; lia). exact F.
Qed.

Lemma xh0_glue : ltac2:(tb__ "0|3|
SbS0A1M0G0S0S0G0S1aSbS5aQ40A1A1Sa2S68Vall;R8ScS0R7S7S0R6S7S0R5R4A3A3A3A3S84S11R4R9R8R7R6R5A7S5cS5bS67VK;VA0;Vrho0;VA1;RaScS0R9S7S0R8S7S0R7R6A3A3A3R8R7U0M1A9S35SaaS11A1U1A2R5R4R3A6S2fS1aS1aS2eS5cS5bS67VK;VA0;Vrho0;VA1;RcScS0RbS7S0RaS7S0R9R8A3A3A3M2S90S90G1A9SbeR1R6R5A6Sb6R1G2S98G2A1A3A2Lrho5;A2F_;F_;F_;Fw;Ftp;Frho;FL;Fn;Fc;FD;FE;").
Proof.
  intros E D c n L rho tp [tr [ms md]] HGI HV H.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ HGI) as MC. pose proof (mc_be _ _ _ _ _ _ _ MC) as BE.
  pose proof HV as ((G204 & G205 & G206 & G207 & G208) & (E167 & _) & _).
  assert (INH : In (hd qb_dflt (D ++ c :: n :: L)) (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply hd_in).
  destruct (addr_facts A1 HTH rho _ BE (mc_in _ _ _ _ _ _ _ MC _ INH)) as (F1 & F2 & F3 & F4 & F5).
  pose proof (mc_sum _ _ _ _ _ _ _ MC) as SUM. pose proof (mc_E _ _ _ _ _ _ _ MC) as QE.
  pose proof (mc_sz _ _ _ _ _ _ _ MC c ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)) as SZC.
  pose proof (mc_sz _ _ _ _ _ _ _ MC n ltac:(apply in_or_app; right; apply in_or_app; right; right; left; reflexivity)) as SZN.
  destruct (xh_common false E D c n L rho tr ms md tp T_xh0 ltac:(cbn; tauto) eq_refl eq_refl ltac:(intros; reflexivity) HGI HV H) as (rho5 & H5 & V5).
  - intros _. constructor; [apply (HSE_holds rho (V 205) _ G205); unfold hd_addr; lia|]. constructor; [|constructor]. apply (align3_holds rho 205%positive _ G205); unfold hd_addr; [lia | exact F5].
  - exists rho5. split; [exact H5|]. unfold HVH.
    rewrite (V5 160%positive (V 204)), (V5 161%positive (V 205)), (V5 162%positive (V 206)), (V5 163%positive (SAlu ALU_SUB (V 207) (V 167))), (V5 208%positive (V 208)) by (cbn; tauto).
    cbn [eval V]. repeat split; try assumption. apply (eval_qs rho E _ (V 167) HGI G207 E167). lia.
Qed.

Lemma xhk_glue : ltac2:(tb__ "0|3|
SbS0A1M0G0S0S0G0S1aSbS5aQ40A1A1Sa2S68Vall;R8ScS0R7S7S0R6S7S0R5R4A3A3A3A3S84S10R4R9R8R7R6R5A7S5cS5bS67VK;VA0;Vrho0;VA1;RaScS0R9S7S0R8S7S0R7R6A3A3A3R8R7U0M1A9S35SaaS10A1U1A2R5R4R3A6S2fS1aS1aS2eS5cS5bS67VK;VA0;Vrho0;VA1;RcScS0RbS7S0RaS7S0R9R8A3A3A3M2S90S90G1A9S38R1R6R5A6S2eSb6R1G2S98G2A1A3S8aR1RcA2A2A2Lrho5;A2F_;F_;F_;Fw;Ftp;Frho;FL;Fn;Fc;FD;FE;").
Proof.
  intros E D c n L rho tp [tr [ms md]] HGI HV H.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ HGI) as MC.
  pose proof HV as ((G204 & G205 & G206 & G207 & G208) & (E167 & _ & E3) & _). destruct (E3 eq_refl) as (E184 & E185 & E186 & E187).
  pose proof (mc_sum _ _ _ _ _ _ _ MC) as SUM. pose proof (mc_E _ _ _ _ _ _ _ MC) as QE.
  pose proof (mc_sz _ _ _ _ _ _ _ MC c ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)) as SZC.
  pose proof (mc_sz _ _ _ _ _ _ _ MC n ltac:(apply in_or_app; right; apply in_or_app; right; right; left; reflexivity)) as SZN.
  destruct (xh_common true E D c n L rho tr ms md tp T_xhk ltac:(cbn; tauto) eq_refl eq_refl ltac:(intros; reflexivity) HGI HV H ltac:(intros _; constructor)) as (rho5 & H5 & V5).
  exists rho5. split; [exact H5|]. split.
  - unfold HVH. rewrite (V5 160%positive (V 204)), (V5 161%positive (V 205)), (V5 162%positive (V 206)), (V5 163%positive (SAlu ALU_SUB (V 207) (V 167))), (V5 208%positive (V 208)) by (cbn; tauto).
    cbn [eval V]. repeat split; try assumption. apply (eval_qs rho E _ (V 167) HGI G207 E167). lia.
  - unfold HVTq. rewrite (V5 166%positive (V 186)), (V5 168%positive (V 184)), (V5 169%positive (V 185)), (V5 170%positive (V 187)), (V5 192%positive (V 184)), (V5 193%positive (V 186)) by (cbn; tauto).
    cbn [eval V]. repeat split; assumption.
Qed.

Lemma xx_glue : ltac2:(tb__ "0|3|
SbS0A1M0G0S0S0G0S1aSbS5aQ40A1A1Sa2S68Vall;R8ScS0R7S7S0R6S7S0R5R4A3A3A3A3S84S10R4R9R8R7R6R5A7S5cS5bS67VK;VA0;Vrho0;VA1;RaScS0R9S7S0R8S7S0R7R6A3A3A3R8R7U0M1A9S35SaaS10A1G1A2R5R4R3A6S2fS1aS1aS2eS5cS5bS67VK;VA0;Vrho0;VA1;RcScS0RbS7S0RaS7S0R9R8A3A3A3M2S90S90G1A9S39R1R6R5A6S2eSb6R1G2S98G2A1A3S2eSb8R1RcA2S5fS91G2A1Sd9A2A2A2A2Lrho5;A2F_;F_;F_;Fw;Ftp;Frho;FL;Fn;Fc;FD;FE;").
Proof.
  intros E D c n L rho tp [tr [ms md]] HGI HV H.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ HGI) as MC.
  pose proof HV as ((G204 & G205 & G206 & G207 & G208) & (E167 & _ & E3) & _). destruct (E3 eq_refl) as (E184 & E185 & E186 & E187).
  pose proof (mc_sum _ _ _ _ _ _ _ MC) as SUM. pose proof (mc_E _ _ _ _ _ _ _ MC) as QE.
  pose proof (mc_sz _ _ _ _ _ _ _ MC c ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)) as SZC.
  pose proof (mc_sz _ _ _ _ _ _ _ MC n ltac:(apply in_or_app; right; apply in_or_app; right; right; left; reflexivity)) as SZN.
  pose proof (eval_qs rho E _ (V 167) HGI G207 E167 ltac:(lia)) as EQS.
  assert (FMIN : qsize (D ++ c :: n :: L) <= kQuarantineMin).
  { apply (min_of_fact rho _ (SAlu ALU_SUB (V 207) (V 167)) G208 EQS); [rewrite (gsize_eq E _ HGI); lia|]. apply (fact_in _ _ rho tp _ _ H). OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. }
  destruct (xh_common true E D c n L rho tr ms md tp T_xx ltac:(cbn; tauto) eq_refl eq_refl ltac:(intros; reflexivity) HGI HV H ltac:(intros _; constructor)) as (rho5 & H5 & V5).
  exists rho5. split; [exact H5|]. split; [|split; [|exact FMIN]].
  - unfold HVH. rewrite (V5 160%positive (V 204)), (V5 161%positive (V 205)), (V5 162%positive (V 206)), (V5 163%positive (SAlu ALU_SUB (V 207) (V 167))), (V5 208%positive (V 208)) by (cbn; tauto).
    cbn [eval V]. repeat split; try assumption.
  - unfold HVX. rewrite (V5 184%positive (V 184)), (V5 185%positive (V 185)), (V5 186%positive (V 186)), (V5 187%positive (V 187)), (V5 208%positive (V 208)) by (cbn; tauto).
    cbn [eval V]. repeat split; assumption.
Qed.

Lemma g_common : ltac2:(tb__ "0|6|
SeSbS0A1M0G0S0S0G0S1aSbSf7A1M1Sf8Sf6SbS5aQ40A1M2A1S69S67VK;VA0;Vrho0;VA1;ScS0RbS7S0S6cR8A1SaS0A1M3A3A3ScS0RaS7S0S6dR9R8A2R7A3A3S90S90U0A9S5dS9aS69R2S3dA3S2dSbS1bA1M4S7aR3A1SaS1bA1A3S2dSbS18A1S7cR4A1SaS18A1A3S17S17S17S2dG4S25S83S75R8A1M5A1A1ScS1bS77G5S7dR8A1A2Sa5S6bS1bS70S8bR13R3R2R1A4A4A3A3Fal;Fan;Fac;S2dSeS9bS1dS27S23S21SdfS1fZ3fdA1S36A3A1A1S24S83S75R6A1A1A1A3S10A3S68Vall;R11ScS0R10S7S0RfS7S0ReRdA3A3A3A3S84R13RdR12R11R10RfReA7S5cS5bS67VK;VA0;Vrho0;VA1;R13ScS0R12S7S0R11S7S0R10RfA3A3A3R11R10SfS9S17S17A2S2R10A1A2A9S75R9A1ReRaS8G1Sf4RdSf5RcRbA2A4A6Sa4S1dS20RfA1S24S83S71RaA1A1A1A3Sa4S1dS20R10A1S78RbA1A3F_;S2fS1aS1aS2eS5cS5bRbS7bRcA1R1RdS8G1Sf4R10Sf5RfReA2A4A6S2eS18S19S9aS9S18S19A2S8S18S19R2R1A4S79ReA1A3S2dG2S1cR4R3A2S1eR14R2A2A3F_;Fex;Fv;S68Vall;ScS0R16S7S0S6cR13A1G3A3A3ScS0R15S7S0S6dR14R13A2R12A3A3A3A2A2Lrho5;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;TJ';Ft;Ftp;Fmd;Fms;Ftr;Frho;FL;Fn;Fc;FD;FE;Fe;").
Proof.
  intros e E D c n L rho tr ms md tp t J' HIN HOC HBS HOBJ HFB HGI HV H HFN.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ HGI) as MC. destruct HJ as (HK & (HMM & HCP) & HFRM). pose proof (mc_be _ _ _ _ _ _ _ MC) as BE.
  pose proof (cap_sum e _ rho E D c n L tp _ _ MC HV H HFB) as HCAP.
  assert (HGI' : GI all (E ++ [emptyb n]) (D ++ mergeb c n :: L)).
  { apply GI_merge; [exact HGI|]. unfold capb, kQuarantineBatchCount. cbn [mergeb qb_items]. rewrite length_app. exact HCAP. }
  destruct (m_step K HL A0 rho0 A1 HQW t J' (dsG e (qb_addr c) (qb_addr n) (last_addr E)) [] [] rho tp tr ms md) as (rho5 & H5 & V5).
  - exact (T_ok t HIN).
  - exact (JRM_stable K HL A0 rho0 A1 _ _ _ _ _).
  - apply HOBJ.
  - rewrite HOC. reflexivity.
  - rewrite HBS. reflexivity.
  - split; [exact (proj1 H) | exact I].
  - exact HK.
  - exact HFRM.
  - exact (be_top _ _ BE).
  - exact (dsG_cond e _ rho E D c n L MC HV).
  - intros HK3 HF3 FR AV. pose proof (mg_mem e _ _ rho E D c n L MC HV HGI HMM HCP HCAP FR AV) as HMM3.
    split; [split; [exact HK3|]; split; [|exact HF3]; split; [exact HMM3 | intros i it Hi; lia]|].
    split; [constructor|]. split; [constructor|]. rewrite HBS. cbn [combine rho_sets]. intros HF4. apply Forall_forall. intros f Hf.
    apply (proj2 (holds_absorb rho _ _ f)). refine (proj1 (Forall_forall _ _) (HFN _) f Hf). apply Forall_forall. intros g Hg.
    apply (proj1 (holds_absorb rho (map dobj (dsG e (qb_addr c) (qb_addr n) (last_addr E))) (vms md tp ms) g)). exact (proj1 (Forall_forall _ _) HF4 g Hg).
  - exists rho5. split; [exact H5|]. split; [|exact HGI']. intros v ex Hin. rewrite (V5 v ex Hin). rewrite HBS. cbn [combine rho_sets]. apply eval_absorb.
Qed.

Lemma Ep_vals : ltac2:(tb__ "0|6|
SeS1aSbS0A1S0S89R4R3R2A3S2dS5aQ40M0A1M1S1cR4Pa3A2S59G0S1R2A1A2A3S2dS17S91R4A1S62Z2000M2S60SfS0R4A2A1A2A3S61S91R5A1S63Z2Z3eA2A2S2eS2dG1S1eR7S3fR8A1A2S59G0S60SfS0ScS0R6S7S0S6cR5A1SaS0A1A3A3M3A2A1A2A3S2eS2dG1S1eR7S3eR8A1A2S59G0S99G3A1A2A3S2eS2dG1S1eR7S42R8A1A2S59G0S91G3A1M4A2M5A3S2eS2dS17S98G3A1S1R5A1A3S2eS2dS17G4S5eS91R6A1G2A2A3S2dG1S1eR7Sa7S34Pa7A1S1fG2A1A2A2G5A3A2A2A2A2A2F_;F_;F_;F_;Fn;FE;Frho;Fe;").
Proof.
  intros e rho E n (E167 & E2 & E3) B163 QE QB.
  assert (QE' : qsize (E ++ [emptyb n]) = qsize E + 8192) by (rewrite qsize_app, qsize_cons; cbn [emptyb qb_size]; unfold kQuarantineBatchSize; change (qsize []) with 0; lia).
  assert (LA : last_addr (E ++ [emptyb n]) = qb_addr n) by (unfold last_addr; rewrite last_snoc; reflexivity).
  assert (E167' : eval rho (add (V 167) (SLit 8192)) = Z_to_bv 64 (qsize (E ++ [emptyb n]))) by (rewrite QE'; apply eval_addl; [exact E167 | lia | lia | lia]).
  destruct e.
  - destruct (E3 eq_refl) as (E184 & E185 & E186 & E187). assert (NE : E <> []) by (intros X; pose proof (proj2 E2 X) as Y; discriminate Y).
    unfold k', f', s'. split; [rewrite length_app, Nat2Z.inj_add; cbn [length]; apply eval_addl; [exact E184 | lia | lia | lia]|].
    split; [cbn [eval V]; rewrite (hd_addr_app E _ NE); exact E185|]. split; [rewrite QE'; apply eval_addl; [exact E187 | lia | lia | lia]|]. split; [exact LA | split; [exact QE' | exact E167']].
  - assert (EN : E = []) by (apply (proj1 E2); reflexivity). subst E. unfold k', f', s'. cbn [app length eval V].
    split; [reflexivity|]. split; [exact B163|]. split; [reflexivity|]. split; [exact LA | split; [exact QE' | exact E167']].
Qed.

Lemma gh_glue : ltac2:(tb__ "0|4|
SeSbS0A1M0G0S0S0G0S1aSbS5aQ40A1A1Sa2S68Vall;R8ScS0R7S7S0R6S7S0R5R4A3A3A3A3S84RaR4R9R8R7R6R5A7S5cS5bS67VK;VA0;Vrho0;VA1;RaScS0R9S7S0R8S7S0R7R6A3A3A3R8R7SfS9S17S17A2S2R7A1A2A9S35SadRbA1U2A2R5R4R3A6S2eS2dG0R7SaS0A1M1A3S2eS68Vall;ScS0RbS7S0S6cR8A1G1A3A3ScS0RaS7S0S6dR9R8A2G1A3A3A3S2fS1aS1aS2eS5cS5bS67VK;VA0;Vrho0;VA1;ScS0RcS7S0S6cR9A1G1A3A3M2ScS0RbS7S0S6dRaR9A2G1A3A3M3S90S90U0A9S38R1R6R5A6S2eSb6R1G3S98G3A1A3S8aR1G2A2A2A2Lrho5;A2A2A2F_;F_;F_;Fw;Ftp;Frho;FL;Fn;Fc;FD;FE;Fe;").
Proof.
  intros e E D c n L rho tp [tr [ms md]] HGI HV H.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ HGI) as MC.
  pose proof HV as ((G204 & G205 & G206 & G207 & G208) & HE & (B160 & B161 & B162 & B163 & B164 & B165 & B166)).
  pose proof (mc_sum _ _ _ _ _ _ _ MC) as SUM. pose proof (mc_E _ _ _ _ _ _ _ MC) as QE. pose proof (mc_len _ _ _ _ _ _ _ MC) as LEN.
  pose proof (mc_sz _ _ _ _ _ _ _ MC c ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)) as SZC.
  pose proof (mc_sz _ _ _ _ _ _ _ MC n ltac:(apply in_or_app; right; apply in_or_app; right; right; left; reflexivity)) as SZN.
  assert (LNIL : L = []).
  { apply (proj2 (L_nil_iff e _ rho E D c n L MC HV)). assert (F : holds rho (SPNot (SPBranch BC_NE (V 164) (SLit 0)))) by (apply (fact_in _ _ rho tp _ _ H); destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    cbn [holds branch_taken eval V] in F. apply bv_eq. destruct (Z.eq_dec (bv_unsigned (rw rho 164%positive)) (bv_unsigned (Z_to_bv 64 0))) as [EQ|NQ]; [exact EQ|].
    exfalso. apply F. apply negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. exact NQ. }
  subst L.
  destruct (Ep_vals e rho E n HE B163 QE ltac:(lia)) as (EK & EF & ES & LA & QE' & E167').
  assert (LENB : 2 <= Z.of_nat (length (D ++ [c; n]))) by (rewrite length_app; cbn [length]; lia).
  assert (LD : Z.of_nat (length D) < 2 ^ 60) by (rewrite length_app in LEN; cbn [length] in LEN; lia).
  assert (E204 : eval rho (add (V 204) (SLit (-1))) = Z_to_bv 64 (Z.of_nat (length (D ++ [mergeb c n])))).
  { replace (Z.of_nat (length (D ++ [mergeb c n]))) with (Z.of_nat (length (D ++ [c; n])) + -1) by (rewrite !length_app; cbn [length]; lia). apply eval_addl; [exact G204 | lia | lia | lia]. }
  destruct (g_common e E D c n [] rho tr ms md tp (T_gh e) ltac:(destruct e; cbn; tauto) eq_refl eq_refl ltac:(intros; destruct e; reflexivity) ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HGI HV H) as (rho5 & H5 & V5 & HGI').
  - intros _. cbn [t_F T_gh app]. constructor; [apply (ne0_holds rho _ _ E204); rewrite length_app; cbn [length]; lia|].
    destruct e; [|constructor]. constructor; [|constructor]. apply (ne0_holds rho _ _ EK). rewrite length_app. cbn [length]. lia.
  - split; [reflexivity|]. split; [exact HGI'|]. exists rho5. split; [exact H5|]. split.
    + unfold HVH. rewrite (V5 160%positive (add (V 204) (SLit (-1)))), (V5 161%positive (V 205)), (V5 162%positive (V 160)), (V5 163%positive (SAlu ALU_SUB (V 207) (add (V 167) (SLit 8192)))), (V5 208%positive (V 208)) by (cbn; tauto).
      split; [exact E204|]. split; [cbn [eval V]; rewrite G205; f_equal; apply hd_addr_mid; reflexivity|].
      split; [cbn [eval V]; rewrite (last_addr_app D [mergeb c n]) by discriminate; exact B160|].
      split; [|cbn [eval V]; exact G208]. apply (eval_qs rho _ _ _ HGI' G207 E167'). lia.
    + unfold HVTq. rewrite (V5 166%positive (V 163)), (V5 168%positive (k' e)), (V5 169%positive (f' e)), (V5 170%positive (s' e)), (V5 192%positive (k' e)), (V5 193%positive (V 163)) by (cbn; tauto).
      rewrite LA. cbn [eval V]. repeat split; assumption.
Qed.

Lemma gx_glue : ltac2:(tb__ "0|5|
SeSbS0A1M0G0S0S0G0S1aSbS5aQ40A1A1Sa2S68Vall;R8ScS0R7S7S0R6S7S0R5R4A3A3A3A3S84RaR4R9R8R7R6R5A7S5cS5bS67VK;VA0;Vrho0;VA1;RaScS0R9S7S0R8S7S0R7R6A3A3A3R8R7SfS9S17S17A2S2R7A1A2A9S35SadRbA1U1A2R5R4R3A6S2eS2dG0R7SaS0A1M1A3S2eS68Vall;ScS0RbS7S0S6cR8A1G1A3A3ScS0RaS7S0S6dR9R8A2G1A3A3M2A3S2eS5fS91G2A1Sd9A2S2fS1aS1aS2eS5cS5bS67VK;VA0;Vrho0;VA1;ScS0RcS7S0S6cR9A1G1A3A3M3ScS0RbS7S0S6dRaR9A2G1A3A3M4S90S90U0A9S39R1R6R5A6S2eSb6R1G4S98G4A1A3Sb8R1G3A2A2A2Lrho5;A2A2A2A2F_;F_;F_;Fw;Ftp;Frho;FL;Fn;Fc;FD;FE;Fe;").
Proof.
  intros e E D c n L rho tp [tr [ms md]] HGI HV H.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ HGI) as MC.
  pose proof HV as ((G204 & G205 & G206 & G207 & G208) & HE & (B160 & B161 & B162 & B163 & B164 & B165 & B166)).
  pose proof (mc_sum _ _ _ _ _ _ _ MC) as SUM. pose proof (mc_E _ _ _ _ _ _ _ MC) as QE. pose proof (mc_len _ _ _ _ _ _ _ MC) as LEN.
  pose proof (mc_sz _ _ _ _ _ _ _ MC c ltac:(apply in_or_app; right; apply in_or_app; right; left; reflexivity)) as SZC.
  pose proof (mc_sz _ _ _ _ _ _ _ MC n ltac:(apply in_or_app; right; apply in_or_app; right; right; left; reflexivity)) as SZN.
  assert (LNIL : L = []).
  { apply (proj2 (L_nil_iff e _ rho E D c n L MC HV)). assert (F : holds rho (SPNot (SPBranch BC_NE (V 164) (SLit 0)))) by (apply (fact_in _ _ rho tp _ _ H); destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    cbn [holds branch_taken eval V] in F. apply bv_eq. destruct (Z.eq_dec (bv_unsigned (rw rho 164%positive)) (bv_unsigned (Z_to_bv 64 0))) as [EQ|NQ]; [exact EQ|].
    exfalso. apply F. apply negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. exact NQ. }
  subst L.
  destruct (Ep_vals e rho E n HE B163 QE ltac:(lia)) as (EK & EF & ES & LA & QE' & E167').
  assert (LENB : 2 <= Z.of_nat (length (D ++ [c; n]))) by (rewrite length_app; cbn [length]; lia).
  assert (LD : Z.of_nat (length D) < 2 ^ 60) by (rewrite length_app in LEN; cbn [length] in LEN; lia).
  assert (E204 : eval rho (add (V 204) (SLit (-1))) = Z_to_bv 64 (Z.of_nat (length (D ++ [mergeb c n])))).
  { replace (Z.of_nat (length (D ++ [mergeb c n]))) with (Z.of_nat (length (D ++ [c; n])) + -1) by (rewrite !length_app; cbn [length]; lia). apply eval_addl; [exact G204 | lia | lia | lia]. }
  destruct (g_common e E D c n [] rho tr ms md tp (T_gx e) ltac:(destruct e; cbn; tauto) eq_refl eq_refl ltac:(intros; destruct e; reflexivity) ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HGI HV H ltac:(intros _; constructor)) as (rho5 & H5 & V5 & HGI').
  pose proof (eval_qs rho _ _ _ HGI' G207 E167' ltac:(lia)) as EQS.
  split; [reflexivity|]. split; [exact HGI'|]. split.
  - apply (min_of_fact rho _ _ G208 EQS); [rewrite (gsize_eq _ _ HGI'); lia|]. apply (fact_in _ _ rho tp _ _ H). destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exists rho5. split; [exact H5|]. split.
    + unfold HVH. rewrite (V5 160%positive (add (V 204) (SLit (-1)))), (V5 161%positive (V 205)), (V5 162%positive (V 160)), (V5 163%positive (SAlu ALU_SUB (V 207) (add (V 167) (SLit 8192)))), (V5 208%positive (V 208)) by (cbn; tauto).
      split; [exact E204|]. split; [cbn [eval V]; rewrite G205; f_equal; apply hd_addr_mid; reflexivity|].
      split; [cbn [eval V]; rewrite (last_addr_app D [mergeb c n]) by discriminate; exact B160|]. split; [exact EQS | cbn [eval V]; exact G208].
    + unfold HVX. rewrite (V5 184%positive (k' e)), (V5 185%positive (f' e)), (V5 186%positive (V 163)), (V5 187%positive (s' e)), (V5 208%positive (V 208)) by (cbn; tauto).
      rewrite LA. cbn [eval V]. repeat split; assumption.
Qed.

Lemma hqk_glue : ltac2:(tb__ "0|4|
SbS0A1M0G0S1aSbS5aQ40A1A1Sa2S68Vall;R5R4A3S30S2dG0R6SaS0A1M1A3A1M2G2S5cS5bS67VK;VA0;Vrho0;VA1;R8R7S90S90U0A9S38R6R5R4A6Sb6R7R8S98R8A1A3S8aR8RaA2S2fS1aS1aS2eS5cS5bSe4VK;VA0;Vrho0;Se6VA1;G1ScS0RcRbA3A3M3RcRbA6SbfR1R9R8A6S2eSb6R1RbS98S5G3A1A1A3S2eSb9R1RbA2SbaR1RcA2A2A2A2Lrho5;A2F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fglob;FE;").
Proof.
  intros E glob rho tp [tr [ms md]] HGI NE NG H (E160 & E161 & E162 & E163 & E208) (E166 & E168 & E169 & E170 & E192 & E193).
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. destruct HJ as (HK & (HMM & _) & HFRM).
  pose proof (benv_of_K K HL A1 HCI rho tp tr md HK) as BE. pose proof HMM as (HBM & HLE & HLG & HTD).
  destruct glob as [|g0 G']; [congruence|]. set (glob := g0 :: G') in *. set (le := last E qb_dflt).
  assert (ING : In g0 (E ++ glob)) by (apply in_or_app; right; left; reflexivity).
  assert (INL : In le (E ++ glob)) by (apply in_last_E; exact NE).
  pose proof (GI_addr A1 E glob g0 HGI ING) as AG. pose proof (GI_addr A1 E glob le HGI INL) as AL.
  destruct (addr_facts A1 HTH rho _ BE AG) as (G1 & G2 & G3 & G4 & G5). destruct (addr_facts A1 HTH rho _ BE AL) as (L1 & L2 & L3 & L4 & L5).
  assert (NGL : qb_addr g0 <> qb_addr le).
  { intros EQ. pose proof (GI_nodup A1 HTH rho E glob BE HGI) as ND. rewrite map_app in ND. apply (NoDup_app_disj _ _ (qb_addr le) ND); [apply in_map; apply In_last; exact NE | rewrite <- EQ; left; reflexivity]. }
  pose proof (addrs_apart A1 HTH rho _ _ BE AG AL NGL) as APT.
  assert (CG0 : cell_ok (view segsA (rm rho)) (mkACell (qb_addr g0) 8 (hd_addr G'))) by exact (glob_link _ [] g0 G' HLG).
  assert (CG1 : cell_ok (view segsA (rm rho)) (mkACell (qb_addr g0 + 8) 8 (qb_size g0))) by exact (proj1 (proj1 (Forall_forall _ _) HBM g0 ING)).
  assert (CL0 : cell_ok (view segsA (rm rho)) (mkACell (qb_addr le) 8 0)).
  { rewrite (app_removelast_last qb_dflt NE) in HLE. exact (glob_link _ (removelast E) le [] HLE). }
  assert (SLE : qb_size le = 8192).
  { destruct HGI as (_ & _ & _ & FE & _). exact (proj2 (proj1 (Forall_forall _ _) FE le (In_last E qb_dflt NE))). }
  assert (CL1 : cell_ok (view segsA (rm rho)) (mkACell (qb_addr le + 8) 8 8192)) by (rewrite <- SLE; exact (proj1 (proj1 (Forall_forall _ _) HBM le INL))).
  set (A1' := set_q A1 [] (E ++ glob)).
  destruct (m_step K HL A0 rho0 A1 HQW T_hqk (JRQ K A0 rho0 A1' E glob) []
              [(V 161, 0, 16, [(0, 8%nat, V 198); (8, 8%nat, V 199)], qb_addr g0); (V 166, 0, 16, [(0, 8%nat, ZQ); (8, 8%nat, SLit 8192)], qb_addr le)]
              [Z_to_bv 64 (hd_addr G'); Z_to_bv 64 (qb_size g0)] rho tp tr ms md) as (rho5 & H5 & V5).
  - apply T_ok. cbn. tauto.
  - exact (JRQ_stable K HL A0 rho0 A1' E glob).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - split; [exact (proj1 H) | exact I].
  - exact HK.
  - exact HFRM.
  - exact (be_top _ _ BE).
  - constructor.
  - intros HK3 HF3 FR AV.
    set (rho3 := rho_absorb rho (map dobj []) (vms md tp ms)) in *. set (v3 := view segsA (rm rho3)) in *.
    set (rho4 := rho_sets rho3 (combine (t_bs T_hqk) [Z_to_bv 64 (hd_addr G'); Z_to_bv 64 (qb_size g0)])).
    assert (OTH : forall i, ~ In i [198; 199]%positive -> rw rho4 i = rw rho i) by (intros i Hi; unfold rho4, rho3; apply rw_sets_absorb; exact Hi).
    assert (SAME : forall z, v3 z = view segsA (rm rho) z) by (intros z; exact (FR z (dz_nil z))).
    assert (CS : forall a k val, cell_ok (view segsA (rm rho)) (mkACell a k val) -> cell_ok v3 (mkACell a k val)) by (intros a k val Hc; eapply cell_ok_frame1; [|exact Hc]; intros z _; apply SAME).
    pose proof (MMEM_ext _ v3 _ _ _ SAME HMM) as (HBM3 & HLE3 & HLG3 & HTD3).
    split; [split; [exact (regroup_K E glob rho3 tp tr md HGI HK3)|]; split; [|exact HF3]; split; [exact HBM3|]; split; [exact (qlinks_tlinks _ _ HLE3)|]; split; [exact HLG3 | exact HTD3]|].
    split; [|split].
    + constructor; [|constructor; [|constructor]].
      * apply (c2_cond rho rho4 v3 _ _ _ _ (hd_addr G') (qb_size g0)); try exact BE; try reflexivity; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact E161 | exact AG | apply CS; exact CG0 | apply CS; exact CG1].
      * apply (c2_cond rho rho4 v3 _ _ _ _ 0 8192); try exact BE; try reflexivity; [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact E166 | exact AL | apply CS; exact CL0 | apply CS; exact CL1].
    + constructor; [constructor; [unfold apart_d; lia | constructor] | constructor; [constructor | constructor]].
    + intros _. constructor; [apply (HSE_holds rho4 (V 161) (qb_addr g0)); [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact E161 | lia]|].
      constructor; [apply (align3_holds rho4 161%positive (qb_addr g0)); [rewrite OTH by (cbn; intuition discriminate); exact E161 | lia | exact G5]|].
      constructor; [apply (HSE_holds rho4 (V 166) (qb_addr le)); [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact E166 | lia]|].
      constructor; [apply (align3_holds rho4 166%positive (qb_addr le)); [rewrite OTH by (cbn; intuition discriminate); exact E166 | lia | exact L5] | constructor].
  - exists rho5. split; [exact H5|].
    set (rho4 := rho_sets _ _) in V5.
    assert (OTH : forall i, ~ In i [198; 199]%positive -> rw rho4 i = rw rho i) by (intros i Hi; unfold rho4; apply rw_sets_absorb; exact Hi).
    assert (VID : forall i, In (i, V i) (t_M T_hqk) -> ~ In i [198; 199]%positive -> rw rho5 i = rw rho i) by (intros i Hi Hn; rewrite (V5 i (V i) Hi); cbn [eval V]; apply OTH; exact Hn).
    split; [|split].
    + unfold HVH. rewrite !VID by (first [cbn; tauto | cbn; intuition discriminate]). cbn [aa_q_global set_q A1']. rewrite (last_addr_app E glob) by discriminate. repeat split; assumption.
    + unfold HVC. rewrite (V5 164%positive (V 198)), (V5 165%positive (V 199)) by (cbn; tauto). split; reflexivity.
    + unfold HVT. rewrite (V5 167%positive (SLit 8192)) by (cbn; tauto). rewrite !VID by (first [cbn; tauto | cbn; intuition discriminate]).
      fold le. rewrite SLE. repeat split; try assumption; reflexivity.
Qed.

Definition dsQ : list dspec := ltac2:(tb__ "0|9|
S7S9S9S9S9S19S17A2M0S17A2M1SbS9S9S17SdA2M2S19A2M3A1M4A2M5S17A2M6S8G5S17S8G1G4S8G0S17S8S19S17SbdS5eSedZa0A2M7A4S5eSedZc0A2A4S7G3S8G2S19S8S17SdG7U8M8A4S34Pa0A1A4S7G3S8G2S19S8S17SdS5eSedZa8A2G8A4S34Pa1A1A4S7G3S8G2S19S8S17SdS5eSedZb0A2G8A4S34Pa2A1A4S7G3S8G2S19S8S17SdS5eSedZb8A2G8A4S34Pa3A1A4SaG3A1A3A3A3A3A4Z0A4SaG6A1A3").
Lemma xq_glue : ltac2:(tb__ "0|2|
SbS0A1M0G0S1aSbS5aQ40A1A1Sa2S68Vall;R5R4A3S30S2dG0R5SaS0A1M1A3A1S5cS5bS67VK;VA0;Vrho0;VA1;R7R6S90S90U0A9S39R5R4R3A6Sb6R6R7S98R7A1A3Sb8R7R9A2S2fS1aS1aS2eS5cS5bSbbVK;VA0;Vrho0;Se6VA1;G1ScS0RbRaA3A3RbRaA6Sc1R1R8R7A6Sb8R1RbA2A2Lrho5;A2F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fglob;FE;").
Proof.
  intros E glob rho tp [tr [ms md]] HGI NG H (E160 & E161 & E162 & E163 & E208) HX.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. destruct HJ as (HK & (HMM & _) & HFRM).
  pose proof (benv_of_K K HL A1 HCI rho tp tr md HK) as BE. pose proof HMM as (HBM & HLE & HLG & HTD).
  set (A1' := set_q A1 [] (E ++ glob)).
  destruct (m_step K HL A0 rho0 A1 HQW T_xq (JRX K A0 rho0 A1' E glob) dsQ [] [] rho tp tr ms md) as (rho5 & H5 & V5).
  - apply T_ok. cbn. tauto.
  - exact (JRX_stable K HL A0 rho0 A1' E glob).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - split; [exact (proj1 H) | exact I].
  - exact HK.
  - exact HFRM.
  - exact (be_top _ _ BE).
  - unfold dsQ. constructor; [|constructor]. unfold diss_cond. split; [reflexivity|]. split; [lia|]. split; [unfold QG; lia|]. split; [lia|]. split; [unfold QG; lia|]. split; [unfold QG; lia|].
    split; [unfold cells_inside, QG; repeat constructor; cbn; lia|]. intros z Hz. split; [right; left; right; right; unfold Inv.QG; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states.QG in Hz; lia | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, QG in *; lia].
  - intros HK3 HF3 FR AV. set (v3 := view segsA (rm (rho_absorb rho (map dobj dsQ) (vms md tp ms)))) in *. set (v := view segsA (rm rho)) in *.
    set (W := fun z => QG + 160 <= z < QG + 192).
    assert (HW : w_ok A1 W) by exact (hdr_ok A1 HTH rho BE).
    assert (FRW : forall z, ~ W z -> v3 z = v z).
    { intros z Hz. apply FR. intros HD. unfold dsQ, dzone in HD. inversion HD as [? ? Hh|? ? HD2]; subst; [apply Hz; unfold W; lia | inversion HD2]. }
    assert (HIGH : forall b, In b (E ++ glob) -> forall z, qb_addr b <= z < qb_addr b + 8192 -> ~ W z).
    { intros b Hb z Hz HP. destruct (addr_facts A1 HTH rho _ BE (GI_addr A1 E glob b HGI Hb)) as (F1 & _). unfold W, QG in HP. lia. }
    unfold dsQ in AV. apply Forall_cons_iff in AV as [AVq _]. pose proof (proj2 AVq) as PRq. cbn beta iota in PRq.
    assert (C0 : cell_ok v3 (mkACell (QG + 160) 8 (Z.of_nat (length glob)))) by (replace (QG + 160) with (0 + (QG + 160)) by lia; apply (res_cell rho v3 _ _ _ _ _ _ 8%nat (V 160) _ AVq); [cbn; tauto | exact E160]).
    assert (C1 : cell_ok v3 (mkACell (QG + 160 + 8) 8 (hd_addr glob))) by (replace (QG + 160 + 8) with (0 + (QG + 168)) by lia; apply (res_cell rho v3 _ _ _ _ _ _ 8%nat (V 161) _ AVq); [cbn; tauto | exact E161]).
    assert (C2 : cell_ok v3 (mkACell (QG + 160 + 16) 8 (last_addr glob))) by (replace (QG + 160 + 16) with (0 + (QG + 176)) by lia; apply (res_cell rho v3 _ _ _ _ _ _ 8%nat (V 162) _ AVq); [cbn; tauto | exact E162]).
    assert (C3 : cell_ok v3 (mkACell (QG + 160 + 24) 8 (qsize glob))) by (replace (QG + 160 + 24) with (0 + (QG + 184)) by lia; apply (res_cell rho v3 _ _ _ _ _ _ 8%nat (V 163) _ AVq); [cbn; tauto | exact E163]).
    split; [|split; [constructor | split; [constructor | intros _; constructor]]].
    split; [exact (regroup_K E glob _ tp tr md HGI HK3)|]. split; [|exact HF3]. unfold RMEM2. fold v3.
    split; [apply Forall_forall; intros b Hb; apply (bm_frame_ext A1 v v3 E glob W HGI HW FRW b Hb); [intros z Hz; apply (HIGH b Hb); lia | exact (proj1 (Forall_forall _ _) HBM b Hb)]|].
    split; [apply qlinks_to_0; apply qlinks_to_0 in HLE; apply (links_frame v v3 W E 0 FRW); [|exact HLE]; intros b z Hb Hz; apply (HIGH b (in_or_app _ _ _ (or_introl Hb))); lia|].
    split; [apply qlinks_to_0; apply qlinks_to_0 in HLG; apply (links_frame v v3 W glob 0 FRW); [|exact HLG]; intros b z Hb Hz; apply (HIGH b (in_or_app _ _ _ (or_intror Hb))); lia|].
    split; [exact (thd_frame A1 v v3 W HW FRW HTD)|].
    unfold qhdr_repr. split; [exact C0|]. split; [intros _; split; [exact C1 | exact C2]|]. split; [intros z Hz; apply PRq; lia | exact C3].
  - exists rho5. split; [exact H5|]. destruct HX as (X184 & X185 & X186 & X187 & X208). unfold HVX.
    rewrite (V5 184%positive (V 184)), (V5 185%positive (V 185)), (V5 186%positive (V 186)), (V5 187%positive (V 187)), (V5 208%positive (V 208)) by (cbn; tauto).
    cbn [eval V combine rho_sets t_bs T_xq]. repeat split; assumption.
Qed.

Lemma first_glue : ltac2:(tb__ "0|4|
S0SbS0A1M0S1aSbS5aQ40M1A1M2A1Sa2S2dG0Vall;S7S0R5R4A3A3Se5R4Vall;A2S5cS5bSe4VK;VA0;Vrho0;VA1;SaS0A1Vall;A6M3Sc0R5R4R3A6S2fS1aS1aS2eS5cS5bG3Sb2R1R6R5A6S2eSe5R1Vall;A2S2eS2dG2S1cR1Pa0A2S59G1S99R8A1A2A3S2eS2dG2S1cR1Pa1A2S59G1S3R9A1A2A3S2dG2S1cR1Pa2A2S59G1S60SfS9S17S17A2S2R9A1A2A1A2A3A2A2A2A2Lrho5;A2F_;F_;F_;Fw;Ftp;Frho;FR;Fb1;").
Proof.
  intros b1 R rho tp [tr [ms md]] HALL (P204 & P205 & P206 & P207 & P208) H.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. destruct HJ as (HK & HRM & HFRM). pose proof HRM as (HBM & HTL & HLK & HTHD).
  pose proof (benv_of_K K HL A1 HCI rho tp tr md HK) as BE. cbn [app] in HBM.
  assert (IN1 : In b1 all) by (rewrite HALL; left; reflexivity).
  assert (A1in : In (qb_addr b1) (map qb_addr all)) by (apply in_map; exact IN1).
  assert (C0 : cell_ok (view segsA (rm rho)) (mkACell (qb_addr b1) 8 (hd_addr R))) by (rewrite HALL in HLK; exact (glob_link _ [] b1 R HLK)).
  pose proof (proj1 (Forall_forall _ _) HBM b1 IN1) as (C1 & C2 & _).
  destruct (m_step K HL A0 rho0 A1 HQW T_first (JRQ K A0 rho0 A1 [] all) [] [(vGF, 0, 24, c3 (V 160) (V 161) (V 162), qb_addr b1)]
              [Z_to_bv 64 (hd_addr R); Z_to_bv 64 (qb_size b1); Z_to_bv 64 (Z.of_nat (length (qb_items b1)))] rho tp tr ms md) as (rho5 & H5 & V5).
  - apply T_ok. cbn. tauto.
  - exact (JRQ_stable K HL A0 rho0 A1 [] all).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - split; [exact (proj1 H) | exact I].
  - exact HK.
  - exact HFRM.
  - exact (be_top _ _ BE).
  - constructor.
  - intros HK3 HF3 FR AV.
    set (rho3 := rho_absorb rho (map dobj []) (vms md tp ms)) in *. set (v3 := view segsA (rm rho3)) in *.
    set (rho4 := rho_sets rho3 (combine (t_bs T_first) [Z_to_bv 64 (hd_addr R); Z_to_bv 64 (qb_size b1); Z_to_bv 64 (Z.of_nat (length (qb_items b1)))])).
    assert (OTH : forall i, ~ In i [160; 161; 162]%positive -> rw rho4 i = rw rho i) by (intros i Hi; unfold rho4, rho3; apply rw_sets_absorb; exact Hi).
    assert (E3 : v3 = view segsA (rm rho)) by (apply functional_extensionality; intros z; exact (FR z (dz_nil z))).
    split; [split; [exact HK3|]; split; [fold v3; rewrite E3; exact HRM | exact HF3]|]. split; [|split; [constructor; [constructor | constructor] | intros _; constructor]].
    constructor; [|constructor]. apply (c3_cond rho rho4 v3 _ _ _ _ _ (hd_addr R) (qb_size b1) (Z.of_nat (length (qb_items b1)))); try exact BE; try reflexivity; try (rewrite E3; assumption).
    + unfold vGF. cbn [eval]. rewrite OTH by (cbn; intuition discriminate). rewrite P205, HALL. reflexivity.
    + exact A1in.
  - exists rho5. split; [exact H5|].
    set (rho4 := rho_sets _ _) in V5.
    assert (OTH : forall i, ~ In i [160; 161; 162]%positive -> rw rho4 i = rw rho i) by (intros i Hi; unfold rho4; apply rw_sets_absorb; exact Hi).
    split; [unfold HVP; rewrite (V5 204%positive (V 204)), (V5 205%positive (V 205)), (V5 206%positive (V 206)), (V5 207%positive (V 207)), (V5 208%positive (V 208)) by (cbn; tauto);
            cbn [eval V]; rewrite !OTH by (cbn; intuition discriminate); repeat split; assumption|].
    rewrite (V5 160%positive (V 160)), (V5 161%positive (V 161)), (V5 162%positive (V 162)) by (cbn; tauto). repeat split; reflexivity.
Qed.

Lemma c3_cond_o : ltac2:(tb__ "0|9|
S1aS1aS93S19S17S19S19S19S17S17S17SbS1bA1S2dS5aQ40M0A1M1S1eRbR9A2S59G0R8A2A3Sb7VA1;RdA2S9aS17RaSa5S0S17S1Vall;A4A3S2dG1S1eReRaA2S59G0R7A2M2A3S2dG1S1eRfRaA2G2A3S2dG1S1eR10RaA2G2A3S94R10S95ReU8M3RaA3A2S94R11S95S5eRfZ8A2G3RaA3A2S94R12S95S5eR10Z10A2G3RaA3A2Sa4S1bS1bS2aS29R15R1A2S8S17S17S5eR12Z0M4A2S5eR12Z18M5A2A4A2Lo';RaA3S72VA1;R15R14RbS8S9S9S9S19S17A2M6S17A2M7SbS9S9S17SdA2S19A2A1M8A2S17S8G7G8S8G6S17S8S19S17R13G4A4G5A4S86R11R10RfA3A4R12A4A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fothers;Fvz;Fvy;Fvx;Fz;Fy;Fx;Fa;Fb;Fv;Frho4;FrhoB;").
Proof.
  intros rhoB rho4 v b a x y z vx vy vz others Eb BE Ha Ex Ey Ez Cx Cy Cz DJ.
  pose proof (c3_cond rhoB rho4 v b a x y z vx vy vz Eb BE Ha Ex Ey Ez Cx Cy Cz) as X. unfold carve_cond in X |- *.
  destruct X as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & _). repeat (split; [assumption|]). exact DJ.
Qed.

Lemma m0m_glue : ltac2:(tb__ "0|4|
S0S0SbS0A1M0S1aSbS5aQ40M1A1M2A1Sa2S2dG0Vall;S7S0R6S7S0R5R4A3A3A3Se5R4Vall;A2S2dG2S1cR5Pa0A2S59G1S99S7S0R7R6A3A1A2A3S2dG2S1cR6Pa1A2S59G1S3R9A1A2A3S2dG2S1cR7Pa2A2S59G1S60SfS9S17S17A2S2RaA1A2A1A2A3S5cS5bSe4VK;VA0;Vrho0;VA1;SaS0A1M3Vall;A6S35SacU2A2R8R7R6A6S2eS68Vall;G3ScS0G3S7S0RcS7S0RbRaA3A3A3A3S2fS1aS1aS2eS5cS5bS67VK;VA0;Vrho0;VA1;G3ScS0G3S7S0RdS7S0RcRbA3A3A3RdRcU0A9SabS11A1R1R9R8A6S84S11R1G3G3RdRcRbA7A2Lrho5;A2A2F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FR;Fb2;Fb1;").
Proof.
  intros b1 b2 R rho tp [tr [ms md]] HALL (P204 & P205 & P206 & P207 & P208) E160 E161 E162 H.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. destruct HJ as (HK & HRM & HFRM). pose proof HRM as (HBM & HTL & HLK & HTHD).
  pose proof (benv_of_K K HL A1 HCI rho tp tr md HK) as BE. cbn [app] in HBM.
  assert (CAPS : Forall capb all).
  { pose proof (proj1 (be_qp _ _ BE)) as HBP. rewrite (qall_A1 A1 HTH) in HBP. apply Forall_forall. intros b Hb. exact (proj1 (proj2 (proj1 (Forall_forall _ _) HBP b Hb))). }
  assert (HGI : GI all [] ([] ++ b1 :: b2 :: R)) by (cbn [app]; rewrite <- HALL; exact (GI_init all CAPS)).
  split; [exact HGI|].
  assert (HJM : JRM [] ([] ++ b1 :: b2 :: R) b1 b2 0 rho tp tr md).
  { split; [exact HK|]. split; [|exact HFRM]. split; [|intros i it Hi; lia]. cbn [app]. rewrite <- HALL. split; [exact HBM|]. split; [exact I|]. split; [exact HLK | exact HTHD]. }
  pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJM HGI) as MC.
  assert (IN1 : In b1 ([] ++ [] ++ b1 :: b2 :: R)) by (left; reflexivity). assert (IN2 : In b2 ([] ++ [] ++ b1 :: b2 :: R)) by (right; left; reflexivity).
  destruct (addr_facts A1 HTH rho _ BE (mc_in _ _ _ _ _ _ _ MC b1 IN1)) as (F1 & F2 & F3 & F4 & F5).
  assert (N12 : qb_addr b1 <> qb_addr b2) by (apply (nodup_mid_ne [b1] R b2 b1); [exact (mc_nd _ _ _ _ _ _ _ MC) | left; reflexivity]).
  pose proof (apart_in rho b1 b2 _ BE (mc_in _ _ _ _ _ _ _ MC) IN1 IN2 N12) as APT.
  pose proof (mc_sz _ _ _ _ _ _ _ MC b1 IN1) as SZ1. pose proof (mc_sum _ _ _ _ _ _ _ MC) as SUM. pose proof (mc_len _ _ _ _ _ _ _ MC) as LEN. cbn [app length] in LEN.
  assert (SZ2 := mc_sz _ _ _ _ _ _ _ MC b2 IN2). change (qsize []) with 0 in SUM.
  destruct (m_step K HL A0 rho0 A1 HQW T_m0m (JRM [] ([] ++ b1 :: b2 :: R) b1 b2 0) [] [(V 160, 0, 24, c3 (V 194) (V 195) (V 196), qb_addr b2)]
              [Z_to_bv 64 (hd_addr R); Z_to_bv 64 (qb_size b2); Z_to_bv 64 (Z.of_nat (length (qb_items b2)))] rho tp tr ms md) as (rho5 & H5 & V5).
  - apply T_ok. cbn. tauto.
  - exact (JRM_stable K HL A0 rho0 A1 _ _ _ _ _).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - split; [exact (proj1 H) | exact I].
  - exact HK.
  - exact HFRM.
  - exact (be_top _ _ BE).
  - constructor.
  - intros HK3 HF3 FR AV.
    set (rho3 := rho_absorb rho (map dobj []) (vms md tp ms)) in *. set (v3 := view segsA (rm rho3)) in *.
    set (rho4 := rho_sets rho3 (combine (t_bs T_m0m) [Z_to_bv 64 (hd_addr R); Z_to_bv 64 (qb_size b2); Z_to_bv 64 (Z.of_nat (length (qb_items b2)))])).
    assert (OTH : forall i, ~ In i [194; 195; 196]%positive -> rw rho4 i = rw rho i) by (intros i Hi; unfold rho4, rho3; apply rw_sets_absorb; exact Hi).
    assert (E3 : v3 = view segsA (rm rho)) by (apply functional_extensionality; intros z; exact (FR z (dz_nil z))).
    assert (HJ3 : JRM [] ([] ++ b1 :: b2 :: R) b1 b2 0 rho3 tp tr md) by (split; [exact HK3|]; split; [fold v3; rewrite E3; exact (proj1 (proj2 HJM)) | exact HF3]).
    split; [exact HJ3|]. split; [|split; [constructor; [constructor | constructor]|]].
    + constructor; [|constructor].
      change (skipn 9 (ss_objs (ax_S (t_Cd T_m0m)))) with (map dobj [(vGF, 0, 24, c3 (V 160) (V 161) (V 162), qb_addr b1)]).
      apply (c3_cond_o rho rho4 v3 _ _ _ _ _ (hd_addr R) (qb_size b2) (Z.of_nat (length (qb_items b2)))); try exact BE; try reflexivity.
      * cbn [eval V]. rewrite OTH by (cbn; intuition discriminate). exact E160.
      * exact (mc_in _ _ _ _ _ _ _ MC b2 IN2).
      * rewrite E3. exact (mc_n0 _ _ _ _ _ _ _ MC).
      * rewrite E3. exact (mc_n1 _ _ _ _ _ _ _ MC).
      * rewrite E3. exact (mc_n2 _ _ _ _ _ _ _ MC).
      * constructor; [|constructor]. rewrite (dobj_range rho4 vGF 0 24 _ (qb_addr b1)) by (first [lia | unfold vGF; cbn [eval]; rewrite OTH by (cbn; intuition discriminate); rewrite P205, HALL; reflexivity]).
        unfold ranges_disjoint. cbn [fst snd]. lia.
    + intros _. constructor; [apply (ne0_holds rho4 (V 204) (Z.of_nat (length all))); [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact P204 | rewrite HALL; cbn [length]; lia]|].
      constructor; [|constructor]. apply (sz13_holds rho4 (V 161) (qb_size b1)); [cbn [eval V]; rewrite OTH by (cbn; intuition discriminate); exact E161 | lia].
  - exists rho5. split; [exact H5|].
    set (rho4 := rho_sets _ _) in V5.
    assert (OTH : forall i, ~ In i [194; 195; 196]%positive -> rw rho4 i = rw rho i) by (intros i Hi; unfold rho4; apply rw_sets_absorb; exact Hi).
    split; [|split].
    + unfold HVG. rewrite (V5 204%positive (V 204)), (V5 205%positive (V 205)), (V5 206%positive (V 206)), (V5 207%positive (V 207)), (V5 208%positive (V 208)) by (cbn; tauto).
      cbn [eval V app]. rewrite !OTH by (cbn; intuition discriminate). rewrite <- HALL. repeat split; assumption.
    + unfold HVE. rewrite (V5 167%positive ZQ) by (cbn; tauto). split; [reflexivity|]. split; [split; reflexivity | intros X; discriminate X].
    + unfold HVB. rewrite (V5 160%positive (V 205)), (V5 161%positive (V 161)), (V5 162%positive (V 162)), (V5 163%positive (V 160)), (V5 164%positive (V 194)), (V5 165%positive (V 195)), (V5 166%positive (V 196)) by (cbn; tauto).
      cbn [eval V]. rewrite !OTH by (cbn; intuition discriminate). split; [rewrite P205, HALL; reflexivity|]. split; [exact E161|]. split; [exact E162|]. split; [exact E160|]. repeat split; reflexivity.
Qed.

Lemma single_false : ltac2:(tb__ "0|0|
S1aS0S2dSbS0A1Vall;S7S0R1SaS0A1A3A3Se5R3Vall;A2S61SdaS91Vall;A1A2S20R5S23S21SdeS28Se1Sf2S1fZ64A1A3S28Se1Sf1S1fZ190000A1A3A3A1A2S33F_;F_;F_;F_;Fb1;Frho;").
Proof.
  intros rho b1 HALL (P204 & _ & _ & P207 & _) HGT HF. apply HF. cbn [holds branch_taken]. apply negb_true_iff. unfold bv_ltu. apply Z.ltb_ge.
  unfold vGS, vGN. cbn [eval]. rewrite !mul_val, P204, P207, HALL. cbn [length]. unfold kQuarantineMax in HGT. rewrite HALL in HGT, HSZ. rewrite !u64_lit by lia. rewrite !Z.mod_small by lia. lia.
Qed.
Lemma min_false : ltac2:(tb__ "0|3|
S1aS17S19S2dS5aQ40M0A1M1S1cR3Pd0M2A2S59G0Sd9A2A3S2dG1S1eR4R2A2S59G0R3A2A3S2eS61SdaR4A2S61R4S63Z2Z40A2A2A2S20R6S21SdeS34G2A1R4A3A2S33F_;F_;F_;F_;Fx;Fq;Frho;").
Proof. intros rho q x E208 Ex Hq F. unfold kQuarantineMax in Hq. pose proof (min_of_fact rho q x E208 Ex ltac:(lia) F) as X. unfold kQuarantineMin in X. lia. Qed.
Lemma last_eq_iff : ltac2:(tb__ "0|1|
SeS93S1aSbS0A1M0G0S0S0G0S85R7R6R5R4R3R2R1A7S84R9R7R6R5R4R3R2A7S32S20R8S21SddS34PceA1S34Pa3A1A3A2S2dG0R3SaS0A1A3A2F_;F_;FL;Fn;Fc;FD;FE;Frho;Fv;Fe;").
Proof.
  intros e v rho E D c n L MC ((_ & _ & G206 & _) & _ & (_ & _ & _ & B163 & _)). cbn [holds branch_taken eval V]. rewrite G206, B163. unfold bv_eqb.
  assert (INN : In n (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  destruct (addr_facts A1 HTH rho _ (mc_be _ _ _ _ _ _ _ MC) (mc_in _ _ _ _ _ _ _ MC n INN)) as (N1 & _ & N3 & _).
  replace (D ++ c :: n :: L) with ((D ++ [c]) ++ n :: L) by (rewrite <- app_assoc; reflexivity). rewrite (last_addr_app (D ++ [c]) (n :: L)) by discriminate.
  split.
  - intros HEq. apply Z.eqb_eq in HEq. destruct L as [|l0 L']; [reflexivity|]. exfalso.
    assert (NEL : l0 :: L' <> []) by discriminate. set (ll := last (l0 :: L') qb_dflt).
    assert (INL : In ll (E ++ D ++ c :: n :: l0 :: L')) by (apply in_or_app; right; apply in_or_app; right; right; right; apply In_last; exact NEL).
    destruct (addr_facts A1 HTH rho _ (mc_be _ _ _ _ _ _ _ MC) (mc_in _ _ _ _ _ _ _ MC ll INL)) as (L1 & _ & L3 & _).
    assert (NE : qb_addr ll <> qb_addr n).
    { apply (nodup_mid_ne (E ++ D ++ [c]) (l0 :: L') n ll); [rewrite <- reassoc1; exact (mc_nd _ _ _ _ _ _ _ MC) | apply in_or_app; right; apply In_last; exact NEL]. }
    unfold last_addr in HEq. change (last (n :: l0 :: L') qb_dflt) with ll in HEq. rewrite !u64_lit in HEq by lia. lia.
  - intros ->. apply Z.eqb_eq. reflexivity.
Qed.

Lemma LM0_eq : ltac2:(tb__ "0|0|
S2dSbS82A1SacS7S82S35SacU0A2S7S82S35SacU1A2S7S82S35SacU2A2SaS82A1A3A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LMH_eq : ltac2:(tb__ "0|1|
SeS2dSbS82A1SaaR1A1M0S7S82S35G0U0A2S7S82S35G0U1A2S7S82S35G0U2A2S7S82S35G0U3A2S7S82S35G0U4A2SaS82A1A3A3A3A3A3A3Fe;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LMC_eq : ltac2:(tb__ "0|1|
SeS2dSbS82A1Sb0R1A1M0S7S82S35G0U0A2S7S82S35G0U1A2SaS82A1A3A3A3Fe;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma LMG_eq : ltac2:(tb__ "0|1|
SeS2dSbS82A1SadR1A1M0S7S82S35G0U0A2S7S82S35G0U1A2S7S82S35G0U2A2S7S82S35G0U3A2S7S82S35G0U4A2S7S82S35G0U5A2SaS82A1A3A3A3A3A3A3A3Fe;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma in_Ts : ltac2:(tb__ "0|1|
SbS82A1Se9S82Se9S9aS9S82Se9A2M0S8S82Se9R2R1A4Sa5S82G0S82S8S82Se9R1R4A4LT;R4A4A3S2eS2dSe9R2R4A3S9aS82R3R5A3A2F_;FM';FT;FM;Fl;").
Proof. intros l M T M' H. apply in_map_iff in H as (T0 & E & HIn). injection E as <- <-. split; [reflexivity | exact HIn]. Qed.

Lemma L_of_fact : ltac2:(tb__ "0|8|
SeS82SbS0A1M0G0S0S0G0SdS1aSbS5aQ40A1A1Sa2S1dS5cS5bS67VK;VA0;Vrho0;VA1;RaScS0R9S7S0R8S7S0R7R6A3A3A3R8R7R5A9RbR4R3R2A6S68Vall;RbScS0RaS7S0R9S7S0R8R7A3A3A3A3S84ReR6RcRbRaR9R8A7S2dSeS9bS1dS27R4A1S24S83ReA1A1A3S10A3S2eS31S2dS1dR5S21Se3S34Pa4A1M1S1fZ0A1M2A3M3A3S2dS1dR5S23S21SddG1G2A3M4A1A3A2S30S2dG0RbSaS0A1A3M5A1M6F_;S2eS31S2dS1dR5S23G3A1A3S2dS1dR5G4A3A2G5F_;S2eS2dS1dR5S21SddS34PceA1S34Pa3A1A3M7A3G5F_;S2dS1dR5S23G7A1A3G6F_;A2A2A2F_;F_;F_;F_;Ff;Fw;Ftp;Frho;Fj;FL;Fn;Fc;FD;FE;FC;Fe;").
Proof.
  intros e C E D c n L j rho tp [tr [ms md]] f H HGI HV HB.
  pose proof (proj2 H) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. pose proof (mctx_of _ _ _ _ _ _ _ _ _ _ HJ HGI) as MC.
  pose proof (fact_in _ _ rho tp _ _ H HB) as HF. pose proof (L_nil_iff e _ rho E D c n L MC HV) as LI. pose proof (last_eq_iff e _ rho E D c n L MC HV) as LE.
  assert (DEC : rw rho 164%positive = Z_to_bv 64 0 \/ bv_unsigned (rw rho 164%positive) <> 0).
  { destruct (Z.eq_dec (bv_unsigned (rw rho 164%positive)) 0) as [EQ|NQ]; [left; apply bv_eq; rewrite EQ; reflexivity | right; exact NQ]. }
  split; [|split; [|split]].
  - intros [->| ->] LN; apply (proj1 LI) in LN; cbn [holds branch_taken eval V] in HF; rewrite LN in HF; [discriminate HF | apply HF; reflexivity].
  - intros [->| ->]; apply (proj2 LI); cbn [holds branch_taken eval V] in HF.
    + destruct DEC as [EQ|NQ]; [exact EQ|]. exfalso. apply HF. apply negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. rewrite (u64_lit 0) by lia. exact NQ.
    + unfold bv_eqb in HF. apply Z.eqb_eq in HF. rewrite (u64_lit 0) in HF by lia. apply bv_eq. rewrite HF. reflexivity.
  - intros ->. exact (proj1 LE HF).
  - intros -> LN. apply HF. exact (proj2 LE LN).
Qed.

Section TRM.
Context {Q : assn} (X : trk Q).
Variable tp : list word.
Hypothesis HJM : ltac2:(tb__ "0|1|
SbS0A1M0G0S0S0SdSa9VQ;VX;S67VK;VA0;Vrho0;VA1;R5R4R3R2R1A9A3Fj;Fn;Fc;Fglob;FE;").
Hypothesis HJQ0 : ltac2:(tb__ "0|0|
Sa9VQ;VX;Se4VK;VA0;Vrho0;VA1;SaS0A1Vall;A6A3").
Hypothesis HGT : ltac2:(tb__ "0|0|
S61SdaS91Vall;A1A2").

Hypothesis CONT_H0 : ltac2:(tb__ "0|2|
SbS0A1M0S1aS68Vall;SaS0A1M1R2A3S30S2dG0R3G1A3A1Sb6R3R4S98R4A1A3Sa8VQ;VX;S5cS5bSe4VK;VA0;Vrho0;Se6VA1;G1ScS0G1R5A3A3G1R5A6SbeR4Vtp;A5A3F_;F_;F_;Frho;Fglob;").
Hypothesis CONT_Hk : ltac2:(tb__ "0|3|
SbS0A1M0G0S1aS68Vall;R3R2A3S30S2dG0R4SaS0A1M1A3A1M2G2Sb6R4R5S98S5Se6VA1;G1ScS0R6R5A3A3A1A1A3Sb9R5R6A2SbaR6R8A2Sa8VQ;VX;S5cS5bSe4VK;VA0;Vrho0;Se6VA1;G1ScS0R9R8A3A3R9R8A6SbfR7Vtp;A5A3F_;F_;F_;F_;F_;F_;Frho;Fglob;FE;").
Hypothesis CONT_X : ltac2:(tb__ "0|2|
SbS0A1M0G0S1aS68Vall;R3R2A3S30S2dG0R4SaS0A1M1A3A1S5fS91R4A1Sd9A2Sb8R4R6A2Sa8VQ;VX;S5cS5bSbbVK;VA0;Vrho0;Se6VA1;G1ScS0R7R6A3A3R7R6A6Sc1R5Vtp;A5A3F_;F_;F_;F_;Frho;Fglob;FE;").

Lemma trg : ltac2:(tb__ "0|0|
Sa3S5dS82S1aOF_;Sa2R5R1A1S2fS1aS1aS2eS5cS5bR6R5R1Vtp;R3A6R4R1A1A2Lrho2;A2F_;Fw;S1aR3R1A1Sa8VQ;VX;S5cS5bR6R5R2Vtp;A5A3F_;Frho2;Sa8VQ;VX;R6A3F_;F_;FPU;FSt;FJ;FP0;").
Proof.
  intros P0 J St PU HG HC. apply (tr_ex X valuation (fun rho2 w => SPA segsA J St rho2 tp w /\ PU rho2) P0 HG). intros rho2.
  apply (tr_pure X _ (PU rho2)); [intros w (_ & a); exact a|]. intros HP. eapply (tr_conseq X); [|exact (HC rho2 HP)]. intros w (Hs & _). exact Hs.
Qed.
Lemma trg2 : ltac2:(tb__ "0|1|
Sa3S5dS82S1aS9S17S17A2M0OF_;F_;Sa2R5R1A1S2fS1aS1aS2fG0G0S2eS5cS5bR7R6R2Vtp;R4A6R5R2R1A2A2Lit;A2Lrho2;A2F_;Fw;S1aG0R4R2R1A2Sa8VQ;VX;S5cS5bR7R6R3Vtp;A5A3F_;Fit;Frho2;Sa8VQ;VX;R6A3F_;F_;FPU;FSt;FJ;FP0;").
Proof.
  intros P0 J St PU HG HC. apply (tr_ex X (valuation * (Z * Z))%type (fun p w => SPA segsA J St (fst p) tp w /\ PU (fst p) (snd p)) P0).
  { intros w Hw. destruct (HG w Hw) as (r & it & H1 & H2). exists (r, it). split; assumption. }
  intros [rho2 it]. cbn [fst snd]. apply (tr_pure X _ (PU rho2 it)); [intros w (_ & a); exact a|]. intros HP. eapply (tr_conseq X); [|exact (HC rho2 it HP)]. intros w (Hs & _). exact Hs.
Qed.

Lemma exit_hk : ltac2:(tb__ "0|2|
SbS0A1M0G0S1aS68Vall;R3R2A3S30S2dG0R4SaS0A1A3A1M1G1Sb6R4R5S98R5A1A3S8aR5R7A2Sa8VQ;VX;S5cS5bS67VK;VA0;Vrho0;VA1;R8R7S90S90U0A9S38R6Vtp;A5A3F_;F_;F_;F_;F_;Frho;Fglob;FE;").
Proof.
  intros E glob rho HGI NE NG HH HT.
  apply (trg _ (JRQ K A0 rho0 (set_q A1 [] (E ++ glob)) E glob) Headk (fun r => HVH r glob (last_addr (aa_q_global (set_q A1 [] (E ++ glob)))) /\ HVC r glob /\ HVT r E)).
  - intros w Hw. exact (hqk_glue E glob rho tp w HGI NE NG Hw HH HT).
  - intros r (R1 & R2 & R3). exact (CONT_Hk E glob r HGI NE NG R1 R2 R3).
Qed.
Lemma exit_x : ltac2:(tb__ "0|2|
SbS0A1M0G0S1aS68Vall;R3R2A3S30S2dG0R4SaS0A1A3A1M1G1S5fS91R5A1Sd9A2Sb6R5R6S98R6A1A3Sb8R6R8A2Sa8VQ;VX;S5cS5bS67VK;VA0;Vrho0;VA1;R9R8S90S90U0A9S39R7Vtp;A5A3F_;F_;F_;F_;F_;F_;Frho;Fglob;FE;").
Proof.
  intros E glob rho HGI NE NG HMIN HH HXx.
  apply (trg _ (JRX K A0 rho0 (set_q A1 [] (E ++ glob)) E glob) Xg (fun r => HVX r E)).
  - intros w Hw. exact (xq_glue E glob rho tp w HGI NG Hw HH HXx).
  - intros r R1. exact (CONT_X E glob r HGI NE HMIN R1).
Qed.
Lemma exit_h0 : ltac2:(tb__ "0|2|
SbS0A1M0S1aS68Vall;SaS0A1M1R2A3S30S2dG0R3G1A3A1Sb6R3R4S98R4A1A3Sa8VQ;VX;S5cS5bS67VK;VA0;Vrho0;VA1;G1R5S90S90U0A9SbeR4Vtp;A5A3F_;F_;F_;Frho;Fglob;").
Proof.
  intros glob rho HGI NG HH. eapply (tr_conseq X); [|exact (CONT_H0 glob rho HGI NG HH)].
  intros [tr [ms md]] Hw. split; [exact (proj1 Hw)|]. destruct (proj2 Hw) as (HK & ((HBM & HLE & HLG & HTD) & _) & HF). cbn [w_tr w_cfg cfg_model fst snd] in *.
  split; [exact (regroup_K [] glob rho tp tr md HGI HK)|]. split; [|exact HF]. split; [exact HBM|]. split; [exact I|]. split; [exact HLG | exact HTD].
Qed.

Lemma HVCp_keep : ltac2:(tb__ "0|0|
SeS1aS1aS0S0SdS9S17S17A2SeaSb5Sb3R7A1A1R6R5A3S87R7R5R4R3R2A5S87R7R6R5R4R3A5F_;F_;Fit;Fj;Fn;Fc;Frho';Frho;Fe;").
Proof.
  intros e rho rho' c n j it HKp (E1 & E2 & E3 & E4). unfold HVCp.
  rewrite !(keepsM_id (VMc e) rho rho' _ HKp) by (unfold VMc; apply in_or_app; right; cbn; tauto). tauto.
Qed.

Lemma mc_loop : ltac2:(tb__ "0|2|
SdSeSbS0A1M0G0S0S0G0SdS9S17S17A2M1S1aS2dSdSbcSbcR3U1A2RaA2SfG1S2R5A1A2A3S68Vall;R9ScS0R8S7S0R7S7S0R6R5A3A3A3A3S84RbR3RaR9R8R7R6A7S87R4R9R8R6R5A5S1aS84ReR1RdRcRbRaR9A7Sa8VQ;VX;S5cS5bS67VK;VA0;Vrho0;VA1;ReScS0RdS7S0RcS7S0RbRaA3A3A3RcRbSfG1S2RbA1A2A9SaeRfA1R2Vtp;A5A3F_;Frho';Sa8VQ;VX;S5cS5bS67VK;VA0;Vrho0;VA1;RdScS0RcS7S0RbS7S0RaR9A3A3A3RbRaR8A9Sb1ReA1R6Vtp;A5A3F_;F_;F_;F_;F_;Frho;Fit;Fj;FL;Fn;Fc;FD;FE;Fe;Fk;").
Proof.
  induction k as [|k IH]; intros e E D c n L j it rho HKK HGI HV HC CONTG;
    apply (seg_MC X e _ rho tp (HJM _ _ _ _ _)); intros T M rho' HIN HKp; unfold TsMC in HIN; apply in_Ts in HIN as [-> HIN]; rewrite LMC_eq in HIN; cbn [In] in HIN;
    pose proof (HVM_keep e rho rho' E D c n L (VMc e) HKp ltac:(unfold VMc; apply incl_appl; apply incl_refl) HV) as HV'; pose proof (HVCp_keep e rho rho' c n j it HKp HC) as HC';
    destruct HIN as [<-|[<-|[]]].
  - apply (trg2 _ (JRM E (D ++ c :: n :: L) c n (S j)) (MC e) (fun r it' => HVM e r E D c n L /\ HVCp r c n (S j) it')); [intros w Hw; exact (cpn_glue e E D c n L j it rho' tp w HGI HV' HC' Hw)|].
    intros r it' [_ (_ & _ & _ & Hn)]. exfalso. assert ((S j < length (qb_items n))%nat) by (apply nth_error_Some; rewrite Hn; discriminate). lia.
  - apply (trg _ (JRM E (D ++ c :: n :: L) c n (length (qb_items n))) (MG e) (fun r => HVM e r E D c n L)); [intros w Hw; exact (cpe_glue e E D c n L j it rho' tp w HGI HV' HC' Hw) | exact CONTG].
  - apply (trg2 _ (JRM E (D ++ c :: n :: L) c n (S j)) (MC e) (fun r it' => HVM e r E D c n L /\ HVCp r c n (S j) it')); [intros w Hw; exact (cpn_glue e E D c n L j it rho' tp w HGI HV' HC' Hw)|].
    intros r it' [R1 R2]. exact (IH e E D c n L (S j) it' r ltac:(lia) HGI R1 R2 CONTG).
  - apply (trg _ (JRM E (D ++ c :: n :: L) c n (length (qb_items n))) (MG e) (fun r => HVM e r E D c n L)); [intros w Hw; exact (cpe_glue e E D c n L j it rho' tp w HGI HV' HC' Hw) | exact CONTG].
Qed.

Lemma mg_step : ltac2:(tb__ "0|2|
SeSbS0A1M0G0S0S0G0S1aS68Vall;R6ScS0R5S7S0R4S7S0R3R2A3A3A3A3S84R8R2R7R6R5R4R3A7S0G0G0S0S1aS2dG0R9S7S0R5R4A3A3S68Vall;R4ScS0RdS7S0R3S7S0R6R5A3M1A3A3A3S84S10R3R5ReR4R7R6A7Sa8VQ;VX;S5cS5bS67VK;VA0;Vrho0;VA1;R6ScS0RfS7S0R5S7S0R8R7A3A3A3R5R8U0A9SabS10A1R4Vtp;A5A3F_;F_;F_;Frho';Fc';FE';FL';Fn2;Sa8VQ;VX;S5cS5bS67VK;VA0;Vrho0;VA1;R9ScS0R8S7S0R7G1A3A3R7R6SfS9S17S17A2S2R6A1A2A9SaeRaA1R4Vtp;A5A3F_;F_;F_;Frho;FL;Fn;Fc;FD;FE;Fe;").
Proof.
  intros e E D c n L rho HGI HV IHc.
  apply (seg_MG X e _ rho tp (HJM _ _ _ _ _)). intros T M rho' HIN HKp. unfold TsMG in HIN. apply in_Ts in HIN as [-> HIN]. rewrite LMG_eq in HIN. cbn [In] in HIN.
  pose proof (HVM_keep e rho rho' E D c n L (VM e) HKp (incl_refl _) HV) as HV'.
  destruct HIN as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
  - apply (tr_pure X _ False); [|intros []]. intros w Hw.
    destruct (L_of_fact e _ E D c n L _ rho' tp w (SPBranch BC_NE (V 164) (SLit 0)) Hw HGI HV' ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (P1 & _).
    destruct (L_of_fact e _ E D c n L _ rho' tp w (SPBranch BC_EQ (V 206) (V 163)) Hw HGI HV' ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (_ & _ & P3 & _).
    exact (P1 (or_introl eq_refl) (P3 eq_refl)).
  - apply (tr_pure X _ (L = [] /\ GI all (E ++ [emptyb n]) (D ++ [mergeb c n]) /\ qsize (D ++ [mergeb c n]) <= kQuarantineMin)).
    { intros w Hw. destruct (gx_glue e E D c n L rho' tp w HGI HV' Hw) as (P1 & P2 & P3 & _). auto. }
    intros (LN & HGI' & HMIN).
    apply (trg _ (JRM (E ++ [emptyb n]) (D ++ [mergeb c n]) qb_dflt qb_dflt 0) XQ (fun r => HVH r (D ++ [mergeb c n]) (last_addr (D ++ [mergeb c n])) /\ HVX r (E ++ [emptyb n]))).
    { intros w Hw. destruct (gx_glue e E D c n L rho' tp w HGI HV' Hw) as (_ & _ & _ & rho5 & Q1 & Q2 & Q3). exists rho5. auto. }
    intros r [R1 R2]. exact (exit_x _ _ r HGI' ltac:(destruct E; discriminate) ltac:(destruct D; discriminate) HMIN R1 R2).
  - apply (tr_pure X _ (L = [] /\ GI all (E ++ [emptyb n]) (D ++ [mergeb c n]))).
    { intros w Hw. destruct (gh_glue e E D c n L rho' tp w HGI HV' Hw) as (P1 & P2 & _). auto. }
    intros (LN & HGI').
    apply (trg _ (JRM (E ++ [emptyb n]) (D ++ [mergeb c n]) qb_dflt qb_dflt 0) HQk (fun r => HVH r (D ++ [mergeb c n]) (last_addr (D ++ [mergeb c n])) /\ HVTq r (E ++ [emptyb n]))).
    { intros w Hw. destruct (gh_glue e E D c n L rho' tp w HGI HV' Hw) as (_ & _ & rho5 & Q1 & Q2 & Q3). exists rho5. auto. }
    intros r [R1 R2]. exact (exit_hk _ _ r HGI' ltac:(destruct E; discriminate) ltac:(destruct D; discriminate) R1 R2).
  - apply (tr_pure X _ (L <> [])).
    { intros w Hw. destruct (L_of_fact e _ E D c n L _ rho' tp w (SPBranch BC_NE (V 164) (SLit 0)) Hw HGI HV' ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (P1 & _). exact (P1 (or_introl eq_refl)). }
    intros NL. destruct L as [|n2 L']; [congruence|].
    apply (trg _ (JRM (E ++ [emptyb n]) (D ++ mergeb c n :: n2 :: L') (mergeb c n) n2 0) (MH true) (fun r => HVM true r (E ++ [emptyb n]) D (mergeb c n) n2 L' /\ GI all (E ++ [emptyb n]) (D ++ mergeb c n :: n2 :: L'))).
    { intros w Hw. exact (mg_glue e E D c n n2 L' rho' tp w HGI HV' Hw). }
    intros r [R1 R2]. exact (IHc n2 L' _ _ r eq_refl R2 R1).
  - apply (tr_pure X _ False); [|intros []]. intros w Hw.
    destruct (L_of_fact e _ E D c n L _ rho' tp w (SPNot (SPBranch BC_NE (V 164) (SLit 0))) Hw HGI HV' ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (_ & P2 & _).
    destruct (L_of_fact e _ E D c n L _ rho' tp w (SPNot (SPBranch BC_EQ (V 206) (V 163))) Hw HGI HV' ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (_ & _ & _ & P4).
    exact (P4 eq_refl (P2 (or_introl eq_refl))).
  - apply (tr_pure X _ False); [|intros []]. intros w Hw.
    destruct (L_of_fact e _ E D c n L _ rho' tp w (SPNot (SPBranch BC_NE (V 164) (SLit 0))) Hw HGI HV' ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (_ & P2 & _).
    destruct (L_of_fact e _ E D c n L _ rho' tp w (SPNot (SPBranch BC_EQ (V 206) (V 163))) Hw HGI HV' ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (_ & _ & _ & P4).
    exact (P4 eq_refl (P2 (or_introl eq_refl))).
Qed.

Theorem mh_loop : ltac2:(tb__ "0|1|
SbS0A1M0SeG0G0S0S0S1aS68Vall;R5ScS0R4S7S0R3S7S0R2R7A3A3A3A3S84R7R2R6R5R4R3R8A7Sa8VQ;VX;S5cS5bS67VK;VA0;Vrho0;VA1;R7ScS0R6S7S0R5S7S0R4R9A3A3A3R5R4U0A9SabR8A1R3Vtp;A5A3F_;F_;Frho;Fn;Fc;FD;FE;Fe;FL;").
Proof.
  induction L as [|n2 L' IH]; intros e E D c n rho HGI HV.
  -
    assert (CONTG : forall r, HVM e r E D c n [] -> TR X (SPA segsA (JRM E (D ++ c :: n :: []) c n (length (qb_items n))) (MG e) r tp)).
    { intros r Hr. apply (mg_step e E D c n [] r HGI Hr). intros n2 L'' E' c' rho' EQ. discriminate EQ. }
    apply (seg_MH X e _ rho tp (HJM _ _ _ _ _)). intros T M rho' HIN HKp. unfold TsMH in HIN. apply in_Ts in HIN as [-> HIN]. rewrite LMH_eq in HIN. cbn [In] in HIN.
    pose proof (HVM_keep e rho rho' E D c n [] (VM e) HKp (incl_refl _) HV) as HV'.
    destruct HIN as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + destruct e.
      * apply (trg _ (JRM E (D ++ c :: n :: []) qb_dflt qb_dflt 0) XQ (fun r => HVH r (D ++ c :: n :: []) (last_addr (D ++ c :: n :: [])) /\ HVX r E /\ qsize (D ++ c :: n :: []) <= kQuarantineMin)).
        { intros w Hw. exact (xx_glue E D c n [] rho' tp w HGI HV' Hw). }
        intros r (R1 & R2 & R3). exact (exit_x E _ r HGI (e_ne _ _ _ (proj1 (proj2 HV')) eq_refl) ltac:(destruct D; discriminate) R3 R1 R2).
      * apply (tr_pure X _ False); [|intros []]. intros w Hw. destruct HV' as ((G204 & G205 & G206 & G207 & G208) & (E167 & E2 & _) & _).
        assert (EN : E = []) by (apply (proj1 E2); reflexivity). subst E.
        pose proof (fact_in _ _ rho' tp _ (SPBranch BC_GEU (V 208) (SAlu ALU_SUB (V 207) (V 167))) Hw ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as F.
        apply (min_false rho' (qsize (D ++ c :: n :: [])) _ G208 (eval_qs rho' [] _ (V 167) HGI G207 E167 ltac:(change (qsize []) with 0; unfold kQuarantineMax in HGT; lia))); [|exact F].
        rewrite (gsize_eq [] _ HGI). change (qsize []) with 0. lia.
    + destruct e.
      * apply (trg _ (JRM E (D ++ c :: n :: []) qb_dflt qb_dflt 0) HQk (fun r => HVH r (D ++ c :: n :: []) (last_addr (D ++ c :: n :: [])) /\ HVTq r E)).
        { intros w Hw. exact (xhk_glue E D c n [] rho' tp w HGI HV' Hw). }
        intros r (R1 & R2). exact (exit_hk E _ r HGI (e_ne _ _ _ (proj1 (proj2 HV')) eq_refl) ltac:(destruct D; discriminate) R1 R2).
      * assert (EN : E = []) by (apply (proj1 (proj1 (proj2 (proj1 (proj2 HV'))))); reflexivity). subst E.
        apply (trg _ (JRM [] (D ++ c :: n :: []) qb_dflt qb_dflt 0) PH (fun r => HVH r (D ++ c :: n :: []) (last_addr (D ++ c :: n :: [])))).
        { intros w Hw. exact (xh0_glue [] D c n [] rho' tp w HGI HV' Hw). }
        intros r R1. exact (exit_h0 _ r HGI ltac:(destruct D; discriminate) R1).
    + apply (tr_pure X _ False); [|intros []]. intros w Hw.
      destruct (L_of_fact e _ E D c n [] _ rho' tp w (SPNot (SPBranch BC_EQ (V 164) (SLit 0))) Hw HGI HV' ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (P1 & _).
      exact (P1 (or_intror eq_refl) eq_refl).
    + apply (trg _ (JRM E (D ++ c :: n :: []) c n (length (qb_items n))) (MG e) (fun r => HVM e r E D c n [])); [intros w Hw; exact (mrg0_glue e E D c n [] rho' tp w HGI HV' Hw) | exact CONTG].
    + apply (trg2 _ (JRM E (D ++ c :: n :: []) c n 0) (MC e) (fun r it => HVM e r E D c n [] /\ HVCp r c n 0 it)); [intros w Hw; exact (cp0_glue e E D c n [] rho' tp w HGI HV' Hw)|].
      intros r it [R1 R2]. assert (JN : (0 < length (qb_items n))%nat) by (apply nth_error_Some; rewrite (proj2 (proj2 (proj2 R2))); discriminate).
      exact (mc_loop (length (qb_items n) - 1) e E D c n [] 0 it r ltac:(lia) HGI R1 R2 CONTG).
  -
    assert (CONTG : forall r, HVM e r E D c n (n2 :: L') -> TR X (SPA segsA (JRM E (D ++ c :: n :: n2 :: L') c n (length (qb_items n))) (MG e) r tp)).
    { intros r Hr. apply (mg_step e E D c n (n2 :: L') r HGI Hr). intros n2' L'' E' c' rho' EQ HGI' HV''. injection EQ as <- <-. exact (IH true E' D c' n2 rho' HGI' HV''). }
    apply (seg_MH X e _ rho tp (HJM _ _ _ _ _)). intros T M rho' HIN HKp. unfold TsMH in HIN. apply in_Ts in HIN as [-> HIN]. rewrite LMH_eq in HIN. cbn [In] in HIN.
    pose proof (HVM_keep e rho rho' E D c n (n2 :: L') (VM e) HKp (incl_refl _) HV) as HV'.
    destruct HIN as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + apply (tr_pure X _ False); [|intros []]. intros w Hw.
      destruct (L_of_fact e _ E D c n (n2 :: L') _ rho' tp w (SPBranch BC_EQ (V 164) (SLit 0)) Hw HGI HV' ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (_ & P2 & _).
      discriminate (P2 (or_intror eq_refl)).
    + apply (tr_pure X _ False); [|intros []]. intros w Hw.
      destruct (L_of_fact e _ E D c n (n2 :: L') _ rho' tp w (SPBranch BC_EQ (V 164) (SLit 0)) Hw HGI HV' ltac:(destruct e; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (_ & P2 & _).
      discriminate (P2 (or_intror eq_refl)).
    + apply (trg _ (JRM E ((D ++ [c]) ++ n :: n2 :: L') n n2 0) (MH e) (fun r => HVM e r E (D ++ [c]) n n2 L')); [intros w Hw; exact (adv_glue e E D c n n2 L' rho' tp w HGI HV' Hw)|].
      intros r R1. apply (IH e E (D ++ [c]) n n2 r); [rewrite <- app_assoc; exact HGI | exact R1].
    + apply (trg _ (JRM E (D ++ c :: n :: n2 :: L') c n (length (qb_items n))) (MG e) (fun r => HVM e r E D c n (n2 :: L'))); [intros w Hw; exact (mrg0_glue e E D c n (n2 :: L') rho' tp w HGI HV' Hw) | exact CONTG].
    + apply (trg2 _ (JRM E (D ++ c :: n :: n2 :: L') c n 0) (MC e) (fun r it => HVM e r E D c n (n2 :: L') /\ HVCp r c n 0 it)); [intros w Hw; exact (cp0_glue e E D c n (n2 :: L') rho' tp w HGI HV' Hw)|].
      intros r it [R1 R2]. assert (JN : (0 < length (qb_items n))%nat) by (apply nth_error_Some; rewrite (proj2 (proj2 (proj2 R2))); discriminate).
      exact (mc_loop (length (qb_items n) - 1) e E D c n (n2 :: L') 0 it r ltac:(lia) HGI R1 R2 CONTG).
Qed.

Lemma list_ne_ex : ltac2:(tb__ "0|1|
SbS0A1M0S30S2dG0R1SaS0A1A3A1S2fS0S0S2fG0G0S2dG0R4S7S0R2R1A3A3Lr;A2Lb;A2F_;Fl;").
Proof. intros [|b r] H; [congruence | exists b, r; reflexivity]. Qed.

Theorem merge_pm : ltac2:(tb__ "0|0|
S1aSe5R1Vall;A2Sa8VQ;VX;S5cS5bSe4VK;VA0;Vrho0;VA1;SaS0A1Vall;A6Sc0R2Vtp;A5A3F_;Frho;").
Proof.
  intros rho HVp.
  assert (NEA : all <> []) by (intros EN; pose proof HGT as X1; rewrite EN in X1; cbn in X1; unfold kQuarantineMax in X1; lia).
  destruct (list_ne_ex all NEA) as (b1 & R & HALL).
  apply (trg _ (JRQ K A0 rho0 A1 [] all) PM1 (fun r => HVP r all /\ rw r 160%positive = Z_to_bv 64 (hd_addr R) /\ rw r 161%positive = Z_to_bv 64 (qb_size b1)
                                                    /\ rw r 162%positive = Z_to_bv 64 (Z.of_nat (length (qb_items b1))))).
  { intros w Hw. exact (first_glue b1 R rho tp w HALL HVp Hw). }
  intros r1 (HVp1 & E160 & E161 & E162).
  apply (seg_M0 X _ r1 tp HJQ0). intros T M rho' HIN HKp. unfold TsM0 in HIN. apply in_Ts in HIN as [-> HIN]. rewrite LM0_eq in HIN. cbn [In] in HIN.
  assert (KV : forall v, In v VM0 -> rw rho' v = rw r1 v) by (intros v Hv; exact (keepsM_id VM0 r1 rho' v HKp Hv)).
  assert (HVp' : HVP rho' all) by (destruct HVp1 as (Q1 & Q2 & Q3 & Q4 & Q5); unfold HVP; rewrite !KV by (cbn; tauto); tauto).
  rewrite <- (KV 160%positive) in E160 by (cbn; tauto). rewrite <- (KV 161%positive) in E161 by (cbn; tauto). rewrite <- (KV 162%positive) in E162 by (cbn; tauto).
  assert (SINGLE : forall i, (i < 2)%nat -> existsb (sprop_eqb (SPBranch BC_EQ (V 160) (SLit 0))) (ss_facts (ax_S (lf LM0 i))) = true ->
             existsb (sprop_eqb (SPNot (SPBranch BC_GEU (SMd M_MUL vGS (SLit 100)) (SMd M_MUL vGN (SLit 1638400))))) (ss_facts (ax_S (lf LM0 i))) = true ->
             forall w, SPA segsA (JRQ K A0 rho0 A1 [] all) (lf LM0 i) rho' tp w -> False).
  { intros i _ HB1 HB2 [tr [ms md]] Hw. pose proof (fact_in _ _ rho' tp _ _ Hw HB1) as F1. pose proof (fact_in _ _ rho' tp _ _ Hw HB2) as F2.
    destruct R as [|r0 R']; [exact (single_false rho' b1 HALL HVp' HGT F2)|]. exfalso.
    pose proof (proj2 Hw) as (HK & _). cbn [w_tr w_cfg cfg_model fst snd] in HK. pose proof (benv_of_K K HL A1 HCI rho' tp tr md HK) as BE.
    assert (INR : In (qb_addr r0) (map qb_addr all)) by (rewrite HALL; right; left; reflexivity).
    destruct (addr_facts A1 HTH rho' _ BE INR) as (A1x & _ & A3x & _). cbn [holds branch_taken eval V] in F1. rewrite E160 in F1. unfold hd_addr in F1. cbn [hd] in F1.
    unfold bv_eqb in F1. apply Z.eqb_eq in F1. rewrite !u64_lit in F1 by lia. lia. }
  destruct HIN as [<-|[<-|[<-|[]]]].
  - apply (tr_pure X _ False); [|intros []]. exact (SINGLE 0%nat ltac:(lia) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)).
  - apply (tr_pure X _ False); [|intros []]. exact (SINGLE 1%nat ltac:(lia) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)).
  - apply (tr_pure X _ (R <> [])).
    { intros w Hw EN. pose proof (fact_in _ _ rho' tp _ (SPNot (SPBranch BC_EQ (V 160) (SLit 0))) Hw ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as F. apply F. cbn [holds branch_taken eval V]. rewrite E160, EN. reflexivity. }
    intros NR. destruct (list_ne_ex R NR) as (b2 & R' & HR). subst R.
    apply (tr_pure X _ (GI all [] ([] ++ b1 :: b2 :: R'))).
    { intros w Hw. exact (proj1 (m0m_glue b1 b2 R' rho' tp w HALL HVp' E160 E161 E162 Hw)). }
    intros HGI0.
    apply (trg _ (JRM [] ([] ++ b1 :: b2 :: R') b1 b2 0) (MH false) (fun r => HVM false r [] [] b1 b2 R')).
    { intros w Hw. exact (proj2 (m0m_glue b1 b2 R' rho' tp w HALL HVp' E160 E161 E162 Hw)). }
    intros r R1. exact (mh_loop R' false [] [] b1 b2 r HGI0 R1).
Qed.
End TRM.
End Skel.
End SegQ3M_skel.

(* [comment removed for export] *)
Module SpineMallocS6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "entailsA"; "la_state"; "mkLeafA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "cons"; "nil"; "Some"; "option"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "sprop"; "valuation"; "ss_next"; "ss_facts"; "sv"; "SLit"; "eval"; "sprop_below"; "SVar"; "rw"; "sobj"; "swf"; "agree_below"; "holds"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SUB"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "liftKA"; "LQA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "C5m1"; "C5m2"; "C5d"; "C5e"; "E5m1"; "E5m2"; "ab_e"; "F_gen"; "BR"; "C5c"; "C6"; "E5j"; "LLe"; "LRe"; "V_RZ"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "JGb"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "memset_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6"; "re8"; "a0e2"; "len1e"; "len2e"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "modulo"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "cnt_of"; "chk_of"; "cls_of"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset"; "P_ret_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4"; "pvals_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "rz"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
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
End SpineMallocS6.

