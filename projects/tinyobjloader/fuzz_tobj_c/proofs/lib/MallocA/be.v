(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.Riscv Require Decode DecodeC.

(* [comment removed for export] *)
Module SegQ3D_qi_arith.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SPUle"; "SVar"; "rw"; "SPAlign"; "SPBranch"; "SPUlt"; "SPNot"; "SAlu"; "SExt"; "holds"; "@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "snd"; "app"; "true"; "fst"; "length"; "list"; "negb"; "prod"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "mul"; "pow"; "div"; "of_nat"; "sub"; "eqb"; "lt"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "max_count"; "Size"; "kUserSpaceSize"; "rz"; "is_primary"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_allocated_user"; "aa_geom"; "ag_spacebeg"; "cs_cache"; "cs_mapped_user"; "ag_ctx"; "ag_thread"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "BC_GE"; "ALU_AND"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith"; "FQ_mag"; "vb_of"; "FQ_geo"; "FQ_it"; "FQ_stk"; "QIV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "it_ab"; "it_cls"; "qall"; "qitems"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs"; "SIDEQ"; "factsQ"; "sQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "spD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "@Stdlib.Lists.List"; "In"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition FQ_stk : list sprop := ltac2:(tb__ "0|1|
SeS0S2S1Z7fff7f800000A1S26S47S26S3PfA1S1Zc0A1A2M0A2A2SeS0S6S35S1N400A1G0A3SeS0S6S35G0S1N10000000000A1A3S10S0A1A3A3A3").
Definition FQ_geo : list sprop := ltac2:(tb__ "0|5|
SeS0S7S1Z0A1S1Z1A1A2SeS0S2S1Z1000A1M0S3P97M1A1M2A2SeS0S2G2S1Z7fffff7ff000A1M3A2SeS0S5G1ZcA2SeS0S2G0S3P98A1M4A2SeS0S2G4G3A2S10S0A1A3A3A3A3A3A3").
Definition FQ_it : list sprop := ltac2:(tb__ "0|10|
SeS0S5Pa5M0Z4M1A2SeS0S5P9bM2Z10M3A2SeS0S2S1Z10007fff8000A1S3G2A1M4A2SeS0S2G4S1Z7fdfff7ff000A1A2SeS0S6S34S3P9cA1S26G4S1Z2000000000A1A2M5A3SeS0S2S1Z1A1S3Pc8A1M6A2SeS0S2G6S1Z1eA1A2SeS0S2S1G3A1M7S3Pc9M8A1M9A2SeS0S2G9S1Z10000A1A2SeS0S5G8G1A2SeS0S2G4S3G0A1MaA2SeS0S7GaG5A2SeS0S8S6S37S9S36SaS13Q20S3PcbA1A3S1ZffA1A3S1Z3MbA1A3A1SeS0S8S6S34S3PcfA1McS1Z0A1A3A1SeS0S7S3PceA1GcA2SeS0S2GcS1Z100A1A2SeS0S2S1Z8A1S3PcdMdA1MeA2SeS0S2GeS1Z10000000000A1A2SeS0S5GdGbA2SeS0S2S26S26GaG7A2GeA2MfG5A2SeS0S2GfS1Z7fffff800000A1A2S10S0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition FQ_mag : list sprop := ltac2:(tb__ "0|2|
SeS0S5Pd2M0Z4A2SeS0S2S3P9bA1S3G0A1M1A2SeS0S7G1S3Pa5A1A2S10S0A1A3A3A3").
Lemma factsQ_eq : ltac2:(tb__ "0|1|
SfSdS16S0A1M0S45R1A1S12S0S3cS12S0S3aS12S0S3bSfG0Lvb;R1S38S10S0A1Xfx2A3A3A3A3Fvb;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition QIV (rho : valuation) (it : Z * Z) (cs : class_state) (t st : Z) : Prop := ltac2:(tb__ "0|4|
S14S19S19Vit;A3S19S11S19S19Vit;A3S19S3fVit;A1S19ScSdS25Q40M0A1M1S4Vrho;Pa5A2S24G0S21R3Z10A2A2A3ScSdG1S4Vrho;Pc8A2S24G0R1A2A3ScSdG1S4Vrho;Pc9A2S24G0S28R1A1A2A3ScSdG1S4Vrho;PcaA2S24G0S31Vcs;A1A2A3ScSdG1S4Vrho;PcbA2S24G0S1bS1bZ3S1dZ100Vt;A2A2S1dZ10000S1fR2S1eZ2Z20A2M2A2A2A2A2A3ScSdG1S4Vrho;PccA2S24G0S1cR2G2A2A2A3ScSdG1S4Vrho;PcdA2S24G0S1dS1fS1bR2Z7A2Z8M3A2G3A2A2A3ScSdG1S4Vrho;PceA2S24G0S20S15S19S30Vcs;A1A2A1A2A3ScSdG1S4Vrho;PcfA2S24G0S27R1A1A2A3ScSdG1S4Vrho;Pd1A2S24G0Vst;A2A3SdG1S4Vrho;Pd2A2S24G0S3eVit;A1A2A3A2A2A2A2A2A2A2A2A2A2Tc;Tn;Tu;").

Definition vb_of (it : Z * Z) : bool := ltac2:(tb__ "0|0|
S17S22S2aS11S19S19Vit;A3A1Z10A2A1").

Lemma max_count_facts : ltac2:(tb__ "0|2|
S19ScS1aZ1M0R1A2S1aR1Z1eA2A2ScS1aG0S27R2A1M1A2S1aG1Z100A2A2F_;Fc;").
Proof.
  assert (H : forallb (fun c => (1 <=? max_count c) && (max_count c <=? 256)) (zseq 1 30) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  intros c Hc. pose proof (range_check _ 1 30 H c ltac:(lia)) as X. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.

Section Arith.
Variable A : AA.
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis HQP : q_pure A.
Hypothesis HAU : ltac2:(tb__ "0|1|
S19ScS1aZ1R1A2S1aR1Z1eA2A2ScS1aZ0S2dS48VA;R2A2A1M0A2S1aG0S29A2A2F_;Fc;").
Variables (rho : valuation) (it : Z * Z) (t st : Z).
Hypothesis HIN : ltac2:(tb__ "0|0|
S49S18S19S19A2Vit;S41S40VA;A1A1A3").
Hypothesis HPR : ltac2:(tb__ "0|0|
SdSfS2bS11S19S19Vit;A3A1S13A3").
Let c := it_cls it.
Let cs := cls_of A c.
Hypothesis HMU : ltac2:(tb__ "0|1|
ScS1aS2dVcs;A1S31Vcs;A1M0A2S1aG0S29A2A2").
Hypothesis HNF : ltac2:(tb__ "0|0|
S23S20S15S19S30Vcs;A1A2A1S27Vc;A1A2").
Hypothesis Ht : 0 <= t < 256.
Hypothesis HRIG : ltac2:(tb__ "0|4|
ScSdS25Q40M0A1M1S4Vrho;P97A2S24G0S33S2eVA;A1M2A1A2A3ScSdG1S4Vrho;P98A2S24G0S32G2A1A2A3ScSdG1S4Vrho;P9bA2S24G0S2fG2A1M3A2A3SdG1S4Vrho;P9cA2S24G0S1bG3S2cA2A2A3A2A2A2").
Hypothesis HV : ltac2:(tb__ "0|0|
S3dVrho;Vit;Vcs;Vt;Vst;A5").

Lemma qi_geo_facts : Forall (holds rho) FQ_geo.
Proof.
  destruct HRIG as (E151 & E152 & _ & _). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (geom_old _ HG) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & _).
  unfold FQ_geo. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E151, ?E152, ?u64_lit by lia; try lia.
Qed.

Lemma qi_geom : ltac2:(tb__ "0|c|
S14S19S19Vit;A3S19S11S19S19Vit;A3S19S28Vc;A1S19S3eVit;A1S19S2fS2eVA;A1A1S19ScScS1aZ1M0Vc;A2S1aVc;Z1eA2A2ScScS1aZ10M1R3A2S1aR3Z10000A2A2ScSdS19S1cR3G1A2Z0M2A3ScScS1aG1S2aR4A1M3A2S1aG3Z800A2A2ScSdS19S1cG3G1A2G2A3ScSdS19R5S1bR2G3A2A3ScScS1aG0R4A2S1aR4Zfc00M4A2A2ScS1aS1bR1S1dVc;S1eZ2M5Z20A2A2A2M6R2A2ScSdS19S1cS21R2G6A2M7R3A2G2A3ScS1aS1bG7R3A2S2dVcs;A1A2ScSdS19S1cR2G1A2G2A3ScS1aS1bR5S1dS1fS1bR4Z7A2Z8M8A2G8A2M9A2S1bR2R3A2MaA2ScS1aGaS1bR1S1eG5Z25A2A2MbA2ScSdS19S1cR1S1eG5G1A2A2G2A3ScS1aZ10007fff8000R1A2ScS1aS1bGbZ1000A2Z7fffff800000A2ScScS1aG8G9A2S1aG9G4A2A2SdS19S1cG9G8A2G2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2TSB;Tab;TS;Tn;Tu;").
Proof.
  cbv zeta. pose proof (item_slot A HQP HAU HG it HIN HPR) as IS. cbv zeta in IS. fold c in IS.
  destruct IS as (C1 & R1 & M1 & U1 & A16 & Z1 & Z2 & RZ & RZ16 & EU & UN & N1 & HS & TOP).
  pose proof (SB_facts A HG) as (S1 & S2 & S3). rewrite kSpaceSize_val in *. unfold HIGH_SHADOW_END in *.
  assert (IP : item_pure A it).
  { destruct (qitems_In A it HIN) as (b & Hb & Hib). destruct HQP as [HBP _]. pose proof (proj1 (Forall_forall _ _) HBP b Hb) as (_ & _ & _ & HF).
    exact (proj1 (Forall_forall _ _) HF it Hib). }
  destruct IP as (_ & _ & IPP & _). specialize (IPP HPR). cbv zeta in IPP. fold c cs in IPP. unfold region_beg, kRegionSize in IPP. unfold it_ab in *.
  pose proof (Z.div_mod (snd it + 7) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (snd it + 7) 8 ltac:(lia)) as B8.
  assert (R8 : (fst it - rz (snd it) + Size c - fst it) mod 8 = 0).
  { replace (fst it - rz (snd it) + Size c - fst it) with (Size c - rz (snd it)) by lia.
    pose proof (Z.div_mod (Size c) 16 ltac:(lia)) as DS. pose proof (Z.div_mod (rz (snd it)) 16 ltac:(lia)) as DR. rewrite Z2 in DS. rewrite RZ16 in DR.
    rewrite DS, DR. replace (16 * (Size c / 16) + 0 - (16 * (rz (snd it) / 16) + 0)) with ((2 * (Size c / 16) - 2 * (rz (snd it) / 16)) * 8) by lia. apply Z.mod_mul. lia. }
  pose proof (Z.div_mod (fst it - rz (snd it) + Size c - fst it) 8 ltac:(lia)) as DQ. rewrite R8 in DQ.
  assert (N8LE : (snd it + 7) / 8 * 8 <= fst it - rz (snd it) + Size c - fst it).
  { assert ((snd it + 7) / 8 <= (fst it - rz (snd it) + Size c - fst it) / 8); [|lia]. apply Z.div_le_lower_bound; [lia|]. lia. }
  repeat split; try lia.
  destruct IPP as (P1 & P2 & P3). unfold cs, c, it_cls in *. lia.
Qed.

Lemma qi_it_facts : Forall (holds rho) FQ_it.
Proof.
  destruct HRIG as (E151 & E152 & E155 & E156). destruct HV as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
  pose proof qi_geom as GEO. cbv zeta in GEO. fold c cs in E200, E201, E202, E206, E207.
  destruct GEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  pose proof (max_count_facts c C1) as MC. rewrite kSpaceSize_val in E156.
  assert (M16 : (fst it - 16) mod 16 = 0).
  { rewrite EU. pose proof (Z.div_mod (it_ab it) 16 ltac:(lia)) as DA. pose proof (Z.div_mod (rz (snd it)) 16 ltac:(lia)) as DR. rewrite A16 in DA. rewrite RZ16 in DR.
    rewrite DA, DR. replace (16 * (it_ab it / 16) + 0 + (16 * (rz (snd it) / 16) + 0) - 16) with ((it_ab it / 16 + rz (snd it) / 16 - 1) * 16) by lia. apply Z.mod_mul. lia. }
  assert (N0 : snd it / 2 ^ 32 = 0) by (apply Z.div_small; lia).
  assert (EM : eval rho (add (SVar 165) (SLit 16)) = Z_to_bv 64 (fst it)).
  { pose proof (eval_add_lit A rho (SVar 165) (fst it - 16) 16 E165 ltac:(lia) ltac:(lia) ltac:(lia)) as X. replace (fst it - 16 + 16) with (fst it) in X by lia. exact X. }
  assert (EMN : eval rho (add (add (SVar 165) (SLit 16)) (SVar 205)) = Z_to_bv 64 (fst it + (snd it + 7) / 8 * 8)) by (apply eval_add_z; [exact EM | cbn [eval]; exact E205 | lia | lia | lia]).
  assert (ESK : eval rho (add (SVar 155) (SLit 137438953472)) = Z_to_bv 64 (ag_spacebeg (aa_geom A) + 137438953472)) by (apply (eval_add_lit A); try lia; cbn [eval]; exact E155).
  unfold FQ_it. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. split; [lia|]. rewrite E165, u64_lit by lia. exact M16.
  - cbn [holds]. split; [lia|]. rewrite E155, u64_lit by lia. exact S1.
  - cbn [holds eval]. rewrite E155, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E155, !u64_lit by lia. lia.
  - cbn [holds branch_taken]. rewrite ESK. cbn [eval]. rewrite E156. unfold bv_eqb. apply Z.eqb_eq. reflexivity.
  - cbn [holds eval]. rewrite E200, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E200, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E201, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E201, !u64_lit by lia. lia.
  - cbn [holds]. split; [lia|]. rewrite E201, u64_lit by lia. exact Z2.
  - cbn [holds eval]. rewrite E155, E165, !u64_lit by lia. lia.
  - cbn [holds]. rewrite ESK. cbn [eval]. rewrite E165, !u64_lit by lia. lia.
  - cbn [holds branch_taken]. intros HB. apply negb_true_iff in HB. unfold bv_eqb in HB. apply Z.eqb_neq in HB. apply HB. clear HB.
    rewrite U_and2, U_sext_e by lia. cbn [eval]. rewrite E203, N0, !u64_lit by lia. change (Z.of_N 32) with 32.
    rewrite (Z.mod_small (3 + 256 * t + 65536 * 0) (2 ^ 32)) by lia. unfold CursorGlue.zsext. replace (3 + 256 * t + 65536 * 0 <? 2 ^ (32 - 1)) with true by (symmetry; apply Z.ltb_lt; lia).
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. replace (3 + 256 * t + 65536 * 0) with (3 + t * 2 ^ 8) by lia. rewrite Z.mod_add by lia. reflexivity.
  - cbn [holds branch_taken eval]. rewrite E207. intros HB. unfold bv_eqb in HB. apply Z.eqb_eq in HB. rewrite !u64_lit in HB by lia. lia.
  - cbn [holds eval]. rewrite E206, E207, !u64_lit by lia. exact HNF.
  - cbn [holds eval]. rewrite E207, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E205, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E205, !u64_lit by lia. lia.
  - cbn [holds]. split; [lia|]. rewrite E205, u64_lit by lia. exact N8b.
  - cbn [holds]. rewrite EMN, ESK, !u64_lit by lia. lia.
  - cbn [holds]. rewrite EMN. cbn [eval]. rewrite !u64_lit by lia. lia.
Qed.

Lemma qi_mag_facts : ltac2:(tb__ "0|0|
SdSfS39Vit;A1S13A3S42S0SbVrho;A1S38A3F_;").
Proof.
  intros HVB. destruct HRIG as (E151 & E152 & E155 & E156). destruct HV as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
  pose proof qi_geom as GEO. cbv zeta in GEO.
  destruct GEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  unfold vb_of in HVB. apply negb_true_iff in HVB. apply Z.eqb_neq in HVB.
  assert (RZ32 : 32 <= rz (snd it)).
  { pose proof (Z.div_mod (rz (snd it)) 16 ltac:(lia)) as DR. rewrite RZ16 in DR. lia. }
  unfold FQ_mag. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. split; [lia|]. rewrite E210, u64_lit by lia. exact A16.
  - cbn [holds eval]. rewrite E155, E210, !u64_lit by lia. lia.
  - cbn [holds eval]. rewrite E165, E210, !u64_lit by lia. lia.
Qed.

Lemma qi_side : ltac2:(tb__ "0|1|
S44S39Vit;A1M0S43Vrho;S46G0A1A2A2").
Proof.
  destruct HRIG as (E151 & E152 & E155 & E156). destruct HV as (E165 & E200 & E201 & E202 & E203 & E204 & E205 & E206 & E207 & E209 & E210).
  pose proof qi_geom as GEO. cbv zeta in GEO. fold c cs in E200, E201, E202, E206, E207.
  destruct GEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  assert (N0 : snd it / 2 ^ 32 = 0) by (apply Z.div_small; lia). assert (NM : snd it mod 2 ^ 32 = snd it) by (apply Z.mod_small; lia).
  rewrite N0 in E203. rewrite NM in E204.
  set (x := (it_ab it - (ag_spacebeg (aa_geom A) + c * 2 ^ 32)) / Size c).
  assert (EX : it_ab it - (ag_spacebeg (aa_geom A) + c * 2 ^ 32) = Size c * x).
  { unfold x. pose proof (Z.div_mod (it_ab it - (ag_spacebeg (aa_geom A) + c * 2 ^ 32)) (Size c) ltac:(lia)) as D. rewrite M1 in D. lia. }
  assert (X0 : 0 <= x) by (unfold x; apply Z.div_pos; lia).
  assert (M16 : (fst it - 16) mod 16 = 0).
  { rewrite EU. pose proof (Z.div_mod (it_ab it) 16 ltac:(lia)) as DA. pose proof (Z.div_mod (rz (snd it)) 16 ltac:(lia)) as DR. rewrite A16 in DA. rewrite RZ16 in DR.
    rewrite DA, DR. replace (16 * (it_ab it / 16) + 0 + (16 * (rz (snd it) / 16) + 0) - 16) with ((it_ab it / 16 + rz (snd it) / 16 - 1) * 16) by lia. apply Z.mod_mul. lia. }
  assert (HWD : (3 + 256 * t + 65536 * 0) / 2 ^ 16 = 0) by (apply Z.div_small; lia).
  assert (HWM : (3 + 256 * t + 65536 * 0) mod 256 = 3) by (replace (3 + 256 * t + 65536 * 0) with (3 + t * 256) by lia; rewrite Z.mod_add by lia; reflexivity).
  exists x, (rz (snd it) - 16). destruct (sQ_vals (vb_of it)) as (W13 & W155 & W158 & W148 & W138 & W139 & W141 & W145 & W146).
  unfold QI_side, V_CLS, V_SIZE, ACQ. cbv zeta. cbn [rho_sub rw]. rewrite W13, W155, W158, W148, W138, W139, W141, W145. unfold vIT. cbn [eval].
  assert (KU : kUserSpaceSize = 2 ^ 32 - 2 ^ 29) by reflexivity. unfold HIGH_SHADOW_END.
  rewrite E165, E155, E200, E201, E202, E203, E204, E205. rewrite !u64_lit by (clear -C1 Z1 HMU KU S2 S3 N1 N8a Ht RZ EU R1 TOP UN U1; lia). rewrite HWD, HWM.
  assert (EM : fst it - 16 = ag_spacebeg (aa_geom A) + c * 2 ^ 32 + Size c * x + (rz (snd it) - 16)) by (clear -EU EX; lia).
  assert (DS : rz (snd it) - 16 < Size c) by (clear -EU UN N8a; lia).
  assert (MUB : Size c * x + Size c <= cs_mapped_user cs) by (clear -EX U1 HMU; lia).
  split; [exact C1|]. split; [reflexivity|]. split; [exact X0|]. split; [clear -RZ DS; lia|]. split; [exact EM|]. split; [exact MUB|].
  split; [clear -HMU KU; lia|]. split; [clear -S2; lia|]. split; [clear -EU UN TOP S3 N8a; lia|]. split; [exact M16|].
  split; [clear -Ht; lia|]. split; [clear -N1; lia|]. split; [replace (0 * 2 ^ 32 + snd it + 7) with (snd it + 7) by lia; reflexivity|].
  unfold vb_of in *. destruct (rz (snd it) =? 16) eqn:ERZ; cbn [negb bgv] in *.
  - apply Z.eqb_eq in ERZ. cbn [eval rho_sub rw]. rewrite W13. unfold vIT. cbn [eval]. rewrite E165, u64_lit by (clear -EU R1 S2 S3 TOP UN RZ C1 Z1 N8a; lia). clear -ERZ. lia.
  - unfold vAB. cbn [eval rho_sub rw]. rewrite W146. cbn [eval]. rewrite E210, u64_lit by (clear -R1 S2 S3 TOP Z1 C1; lia). clear -EU. lia.
Qed.
End Arith.
End SegQ3D_qi_arith.

(* [comment removed for export] *)
Module SpineMallocS7.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_setS"; "la_state"; "leafA"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "list"; "Some"; "option"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "ss_next"; "SAlu"; "sv"; "sobj"; "ss_facts"; "SLit"; "eval"; "sprop_below"; "ss_objs"; "swf"; "SVar"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "C6m"; "C6l"; "C6b"; "C7"; "E6l"; "E6s"; "E6m"; "O_U"; "C6"; "E6j"; "LUe"; "ube"; "F_gen"; "n8e"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "JGb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ"; "Pre_mszA"; "P_msz"; "Posts_mszA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "stopJ_stable"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SpineMallocS7"; "len3e"; "@Stdlib.Lists.List"; "forallb"; "incl"; "nth_error"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "le"; "pow"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueZ"; "zero_covered"; "zobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4"; "pvals_ok"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition len3e : sv := ltac2:(tb__ "0|1|
S13S3aS13S38S13S39S13S38S13S38S29S2bA3S17N8A1A3S17Z3A1M0A3S17Z1A1A3S13S39S29G0A3A3").

Section PSVals3.
Variable rho : valuation.
Variables SB c x rzv sz n : Z.
Hypothesis PV : ltac2:(tb__ "0|0|
S5aVrho;VSB;Vc;Vx;Vrzv;Vsz;Vn;A7").
Let ab : Z := ltac2:(tb__ "0|0|
S4cS4cVSB;S4dVc;S4fZ2Z20A2A2A2S4dZ10Vx;A2A2").
Ltac pv := pose proof PV as (E12 & E148 & E150 & E155 & E158 & E159 & Bn & Bsz & Brz & Bfit & BSB & Bc & Bx & Btop).

Lemma pv_len3 : ltac2:(tb__ "0|0|
S0S36Q40A1S18Vrho;S48A2S18Vrho;S28A2A3").
Proof.
  pv. pose proof (eq_refl 140737479966720) as ACV. pose proof (pv_ub rho _ _ _ _ _ _ PV) as EUB. cbn zeta in EUB. fold ab in EUB.
  pose proof (pv_lu rho _ _ _ _ _ _ PV) as ELU.
  apply bv_eq. rewrite ELU. unfold len3e. cbn [eval]. fold ube. fold n8e.
  assert (EN8 : bv_unsigned (eval rho n8e) = n - n mod 8).
  { unfold n8e. cbn [eval]. rewrite and_val, E12, !u64_lit by (unfold M48; lia). apply land_M48. lia. }
  rewrite sub_val, add_val, srl_val, add_val, add_val, srl_val, EUB, EN8.
  replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity. rewrite !u64_lit by lia. change (3 mod 64) with 3.
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)).
  assert (B1 : 17594333495296 <= ab + rzv /\ ab + rzv + n <= 140737479966720) by (unfold ab; lia).
  rewrite (Z.mod_small (ab + rzv + (n - n mod 8))) by lia.
  replace ((ab + rzv + (n - n mod 8) + (2 ^ 64 - 8)) mod 2 ^ 64) with (ab + rzv + (n - n mod 8) - 8).
  2:{ replace (ab + rzv + (n - n mod 8) + (2 ^ 64 - 8)) with ((ab + rzv + (n - n mod 8) - 8) + 1 * 2 ^ 64) by lia.
      rewrite Z.mod_add by lia. rewrite (Z.mod_small (ab + rzv + (n - n mod 8) - 8)) by lia. reflexivity. }
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_mod SB (2 ^ 16) ltac:(lia)). pose proof (Z.div_mod rzv 16 ltac:(lia)).
  set (q := SB / 2 ^ 16) in *. set (r := rzv / 16) in *. set (k := n / 8) in *.
  replace (ab + rzv + (n - n mod 8) - 8) with ((q * 2 ^ 13 + c * 2 ^ 29 + 2 * x + 2 * r + k - 1) * 8) by (unfold ab; lia).
  replace (ab + rzv) with ((q * 2 ^ 13 + c * 2 ^ 29 + 2 * x + 2 * r) * 8) by (unfold ab; lia).
  rewrite !Z.div_mul by lia. rewrite (Z.mod_small (_ + 1)) by lia. rewrite (Z.mod_small (_ - _)) by lia. lia.
Qed.
End PSVals3.

Section S7.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S42VAInv;VW;Vst;VA;VKc;S1cPcA1A6").

Section B10aS.
Hypothesis Cert6 : ltac2:(tb__ "0|1|
S0S7S3fS43Ufa0S9S2cZ5f864S9S2cZ3c698SaS2cA1A3A3S34S9S2S26VW;Vst;Vtmax;A3SaS2A1M0A3S9S2S23VW;Vst;Vtmax;A3S9S2S22VW;Vst;Vtmax;A3G0A3A3A6S8A3").

Variable k6 : nat.
Hypothesis NTH6s : ltac2:(tb__ "0|0|
S0SdS15A1S4bS15S1aS1S23VW;Vst;Vtmax;A3A1A1Vk6;A3ScS15S25A2A3").
Hypothesis ZC6s : ltac2:(tb__ "0|0|
S0S7S55S16S1S23VW;Vst;Vtmax;A3A1A1S25A2S8A3").
Variable s7s : wsub.
Hypothesis ENT7s : ltac2:(tb__ "0|2|
S0S7S3S4S23VW;Vst;Vtmax;A3M0S53S1G0A1M1S52S15S1aG1A1Vk6;S56S25A1A4A2A2S21VW;Vst;Vtmax;A3Vs7s;A3S8A3").
Hypothesis SID7s : ltac2:(tb__ "0|0|
S0S7S3eVs7s;S34A2S8A3").

Hypothesis G6l : ltac2:(tb__ "0|0|
S4aS11S2aS16S1S22VW;Vst;Vtmax;A3A1A1A3").
Hypothesis W6l : ltac2:(tb__ "0|0|
S0S7S1bS1S1fVW;Vst;Vtmax;A3A1A1S8A3").
Hypothesis D6l : ltac2:(tb__ "0|4|
S0SdSeSbSeS14S14A2M0A1M1SbS11A1M2A2M3A1S47S1S22VW;Vst;Vtmax;A3A1S1S1fVW;Vst;Vtmax;A3A1A2ScG3SfG1G2S9G0SfS14S14S48S28A4SaG0A1A3SaS11A1A4A2A3").
Hypothesis NX6l : ltac2:(tb__ "0|0|
S0S2dS12S1S1fVW;Vst;Vtmax;A3A1A1S12S1S22VW;Vst;Vtmax;A3A1A1A3").

Theorem spine_s6 : ltac2:(tb__ "0|1|
S30OF_;S44S40S10SbS36Q40M0A1A1S2fS45VW;Vst;A2S41R5A1S33Vsegs;R8S32R6A1A3S4eZ1S46R8S37G0S1dR6PcA2A2A2A2S10S2eVsegs;RbS31Vsegs;S35VW;Vst;RaR9R8A5S21VW;Vst;Vtmax;A3R1R7A5R6A4FrhoX;S10S2eVsegs;RcS31Vsegs;S35VW;Vst;RbRaR9A5S1fVW;Vst;Vtmax;A3R1R8A5R7A4FrhoX;S10S2eVsegs;RdS31Vsegs;S35VW;Vst;RcRbRaA5S26VW;Vst;Vtmax;A3R1R9A5R8A4FrhoE;F_;F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf Hcnt HC7 HC6l rhoE.
  apply (cfg_soundA segs 4000%nat [0x5f864; 0x3c698] GW [C6 W st tmax] [E6s W st tmax; E6l W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert6.
  - intros E rhoX HinE. destruct HinE as [<-|[<-|[]]].
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC7 (rho_sub rhoX s7s))].
      apply (SPA_entails0 segs (JGb W st A Kc rho) GW _ (C7 W st tmax) s7s rhoX tp w ENT7s SID7s); [apply JGb_stable; [exact HUS | exact HKc]|].
      apply (SPA_zero_fold segs (JGb W st A Kc rho) rhoX (E6s W st tmax) tp w k6 O_U NTH6s ZC6s Hw).
    + eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC6l rhoX)].
      pose proof (JGb_pvals nW st A Kc rho rhoX tp w _ Hw G6l Hcnt) as PV. cbn zeta in PV.
      unfold C6l, upd. lazy zeta. eapply SPA_restate; [exact W6l | exact D6l | exact NX6l | | constructor | exact Hw].
      unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exact (pv_len3 rhoX _ _ _ _ _ _ PV).
  - left. reflexivity.
Qed.
End B10aS.

Section B10bS.
Hypothesis Cert6l : ltac2:(tb__ "0|1|
S0S7S3fS43Ufa0S9S2cZde378SaS2cA1A3S34S9S2S1fVW;Vst;Vtmax;A3SaS2A1M0A3S9S2S24VW;Vst;Vtmax;A3G0A3A6S8A3").
Hypothesis W6m : ltac2:(tb__ "0|0|
S0S7S1bS1S1eVW;Vst;Vtmax;A3A1A1S8A3").
Hypothesis D6m : ltac2:(tb__ "0|4|
S0SdSeSbSeS14S14A2M0A1M1SbS11A1M2A2M3A1S47S1S24VW;Vst;Vtmax;A3A1S1S1eVW;Vst;Vtmax;A3A1A2ScG3SfG1G2SaG0A1SaS11A1A4A2A3").
Hypothesis NX6m : ltac2:(tb__ "0|0|
S0S2dS12S1S1eVW;Vst;Vtmax;A3A1A1S12S1S24VW;Vst;Vtmax;A3A1A1A3").
Variables (s6 sd6 : wsub) (R6 : list sobj) (T6 : axst).
Hypothesis He6 : ltac2:(tb__ "0|1|
S0SdSbS15A1M0A1S58S1eVW;Vst;Vtmax;A3S3bVs6;A3ScG0VR6;A2A3").
Hypothesis Hchk6 : ltac2:(tb__ "0|0|
S0S7S57S1eVW;Vst;Vtmax;A3S3bVs6;VR6;S50S6S2S5S3dA4A5S8A3").
Hypothesis HT6 : ltac2:(tb__ "0|0|
S0S2S59Vs6;S3bS51S3cA1S1eVW;Vst;Vtmax;A3VR6;A5VT6;A3").
Hypothesis FBC6 : ltac2:(tb__ "0|1|
S0S7S49S11S19S12S1S1eVW;Vst;Vtmax;A3A1M0A1A1S16G0A1A3S8A3").
Hypothesis FBT6 : ltac2:(tb__ "0|0|
S0S7S49S11S19S12S1VT6;A1A1A1S16S1S1eVW;Vst;Vtmax;A3A1A1A3S8A3").
Hypothesis ENT6 : ltac2:(tb__ "0|0|
S0S7S3S54VT6;S16S1S1eVW;Vst;Vtmax;A3A1A1A2S20VW;Vst;Vtmax;A3Vsd6;A3S8A3").
Hypothesis SID6 : ltac2:(tb__ "0|0|
S0S7S3eVsd6;S34A2S8A3").
Hypothesis NXC6 : ltac2:(tb__ "0|0|
S5bS34S12S1S1eVW;Vst;Vtmax;A3A1A1A2").

Theorem spine_s6l : ltac2:(tb__ "0|2|
S30OF_;S44S40S10SbS36Q40A1A1M0S2fS45VW;Vst;A2S41R5A1S33Vsegs;R8S32R6A1A3S10G0S2eVsegs;RbS31Vsegs;S35VW;Vst;RaR9R8A5M1S20VW;Vst;Vtmax;A3R2R1A5R6A4FtpX;FrhoX;S10S2eVsegs;RbS31Vsegs;G1S1fVW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC rhoE.
  apply (cfg_soundA segs 4000%nat [0xde378] GW [C6l W st tmax] [E6m W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert6l.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw |].
    2:{ apply (call_gen nW st (C6m W st tmax) T6 (C6b W st tmax) s6 R6 sd6 Pre_mszA Posts_mszA P_msz
                eq_refl (fun ok0 Jx r0 t0 Ho Hs => memsetZ_sumA ok0 Jx Ho Hs r0 t0) He6 Hchk6 HT6 FBC6 FBT6 ENT6 SID6 NXC6 eq_refl
                ok A Kc rho tp rhoX Q HUS HKc Hokf HC). }
    unfold C6m, upd. lazy zeta. eapply SPA_restate; [exact W6m | exact D6m | exact NX6m | constructor | constructor | exact Hw].
  - left. reflexivity.
Qed.
End B10bS.

Section B10cS.
Hypothesis Cert6b : ltac2:(tb__ "0|1|
S0S7S3fS43Ufa0S9S2cZ3c698SaS2cA1A3S34S9S2S20VW;Vst;Vtmax;A3SaS2A1M0A3S9S2S27VW;Vst;Vtmax;A3G0A3A6S8A3").
Variable s7j : wsub.
Hypothesis ENT7j : ltac2:(tb__ "0|0|
S0S7S3S27VW;Vst;Vtmax;A3S21VW;Vst;Vtmax;A3Vs7j;A3S8A3").
Hypothesis SID7j : ltac2:(tb__ "0|0|
S0S7S3eVs7j;S34A2S8A3").
Theorem spine_s6b : ltac2:(tb__ "0|0|
S30OF_;S44S40S10SbS36Q40A1A1S2fS45VW;Vst;A2S41R5A1S33Vsegs;R8S32R6A1A3S10S2eVsegs;RaS31Vsegs;S35VW;Vst;R9R8R7A5S21VW;Vst;Vtmax;A3R1R6A5R5A4FrhoX;S10S2eVsegs;RbS31Vsegs;S35VW;Vst;RaR9R8A5S20VW;Vst;Vtmax;A3R1R7A5R6A4FrhoE;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HUS HKc Hokf HC rhoE.
  apply (cfg_soundA segs 4000%nat [0x3c698] GW [C6b W st tmax] [E6j W st tmax] (JGb W st A Kc rho) ok Q tp).
  - intros r t tr ms md msv' [_ HJ] HMI Hh Hp Hs. destruct HJ as (_ & HK & _). exact (Hokf r t tr ms md msv' HK HMI Hh Hp Hs).
  - apply JGb_stable; [exact HUS | exact HKc].
  - exact Cert6b.
  - intros E rhoX HinE. destruct HinE as [<-|[]].
    eapply triple_conseq; [intros w Hw | intros w Hw; right; exact Hw | apply (HC (rho_sub rhoX s7j))].
    apply (SPA_entails0 segs (JGb W st A Kc rho) GW (E6j W st tmax) (C7 W st tmax) s7j rhoX tp w ENT7j SID7j); [|exact Hw].
    apply JGb_stable; [exact HUS | exact HKc].
  - left. reflexivity.
Qed.
End B10cS.
End S7.
End SpineMallocS7.

