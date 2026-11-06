(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn bz.

(* [comment removed for export] *)
Module SpineMallocQ11.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "SLit"; "reg_sv"; "eval"; "ss_facts"; "valuation"; "ss_objs"; "swf"; "sprop_below"; "ss_lenient"; "ss_pc"; "sv_below"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "list"; "nil"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "nat"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "GR"; "rMS"; "sMS"; "O_pcm"; "O_ri"; "beg1"; "beg2"; "cX"; "idx_rot"; "nobj"; "relM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "add"; "ge"; "le"; "modulo"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_pcc0"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "ghosts"; "mlink"; "F0"; "U0"; "frozen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP"; "ph_set"; "pbase"; "ph_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "BASEFq"; "BASEOq"; "entryRq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ11"; "a0_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ9"; "O_piece"; "O_shp"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ10"; "a2_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2"; "rigids"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ10.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition a0_e (eb : sv) : sv := SAlu ALU_AND eb (SLit 18446744073709547520).

Lemma a0_val : ltac2:(tb__ "0|1|
SfS8S22S0S22S34Q40M0SdR3R2A2A2R1A3S0S22S38R2Z1000A2Z0A3S0S33G0A1SdR5S52R4A1A2SdR5R4A2A3F_;F_;FB;Feb;Fr;").
Proof.
  intros r eb B EB HM. unfold a0_e. cbn [eval]. apply bv_eq. rewrite and_val. replace (bv_unsigned (Z_to_bv 64 18446744073709547520)) with 18446744073709547520 by reflexivity.
  rewrite EB. apply land_m4096_id; [|exact HM]. rewrite <- EB. apply urange.
Qed.

Section ADDR.
Variables (A : AA) (rb r : valuation).
Hypothesis CF : cfacts A rb.
Hypothesis RG : ltac2:(tb__ "0|0|
S62VA;Vrb;Vr;A3").
Hypothesis GH : ltac2:(tb__ "0|0|
S47VA;Vrb;Vr;A3").

Lemma beg1_val : ltac2:(tb__ "0|0|
S0S22S34Q40SdVr;S2cA2A2S4aVA;Vrb;A2A3").
Proof.
  unfold cfacts in CF. cbn zeta in CF. destruct CF as ((_ & C1 & _) & _ & (_ & AU0 & MU1 & _) & _ & _ & (G12 & G13 & G14 & TG) & _).
  destruct RG as (_ & _ & _ & _ & E155 & _ & _ & E158). destruct GH as (_ & _ & _ & _ & Q224 & _).
  unfold beg1, rb_e, vMU, vSB, V_CLS, U0, region_beg, kRegionSize. cbn [eval]. rewrite !add_val, sll_val, E155, E158, Q224, !u64_lit by lia.
  change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + _ * 2 ^ 32)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma beg2_val : ltac2:(tb__ "0|0|
S0S22S34Q40SdVr;S2dA2A2S49VA;Vrb;A2A3").
Proof.
  unfold cfacts in CF. cbn zeta in CF. destruct CF as ((_ & C1 & _) & _ & _ & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & _).
  pose proof (Zle_0_nat (length (cs_free_array (cst_of A (bv_unsigned (rw rb 12%positive)))))) as NF0.
  destruct RG as (_ & _ & _ & _ & E155 & _ & _ & E158). destruct GH as (_ & _ & Q222 & _).
  unfold beg2, fa_e2, rb_e, vMFA, vSB, V_CLS, F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. cbn [eval].
  rewrite !add_val, sll_val, E155, E158, Q222, !u64_lit by lia.
  change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + _ * 2 ^ 32)) by lia.
  rewrite (Z.mod_small (_ + _ * 2 ^ 32 + 3758096384)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
End ADDR.

Section PIECE.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S0S45Vst;S44A3S0S19S43A1VW;S1aS43A1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S51VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).

Variable p : piece.
Variable eb : sv.
Variable ph : phase.
Hypothesis PH0 : ltac2:(tb__ "0|0|
S0S21S4eVp;Vph;A2U0A3").
Hypothesis PORD : pord p ph.
Hypothesis PQ : ph_quiet ph.
Let B : Z := ltac2:(tb__ "0|0|
S4dVA;Vrb;Vp;A3").
Hypothesis HBv : ltac2:(tb__ "0|0|
SfS4bVrb;R1A2S47VA;Vrb;R2A3S0S22S34Q40SdR3Veb;A2A2VB;A3F_;F_;Fr;").
Hypothesis HBn : ltac2:(tb__ "0|1|
S1S37S35S5fS5eVA;A1A1M0Z100000000A2VB;A2S1S37S35VB;Z40000A2S35G0Z2000000000A2A2S0S22S38VB;Z10000A2Z0A3A2A2").
Hypothesis HROOM_c : ltac2:(tb__ "0|0|
S19S33Q40A1A1S39S48VA;Vrb;Vtp0;Vmd0;Vph;R2R1A7S36S40R2R3A2Z40000A2F_;Fmd;Ftp;").
Hypothesis HROOM_r : ltac2:(tb__ "0|0|
S19S33Q40A1A1S39S48VA;Vrb;Vtp0;Vmd0;S4cVp;U1Vph;A3R2R1A7S36S40R2R3A2Z8000A2F_;Fmd;Ftp;").

Variable F : nat.
Variables (C0 : axst) (LX LM : leafA).
Let CX : axst := ltac2:(tb__ "0|0|
S2eS4VLX;A1Veb;A2").
Let G1 : axst := commit_post CX eb 262144.
Let EM : axst := la_state LM.
Let CMR : axst := cMr EM.
Let CMC : axst := cMc EM eb.
Let DM : axst := dMSf CMC.
Let RM : axst := rotM DM.

Hypothesis R_x : ltac2:(tb__ "0|1|
S0S1dS19S3A1M0A1S5S25VF;S16S22Z7050cS1aS22A1A3VC0;S18A5S1cG0S16S3VLX;S1aS3A1A3A2A3").
Hypothesis LN_0 : ltac2:(tb__ "0|0|
S0S17S13S2VC0;A1A1S20A3").
Hypothesis NX_0 : ltac2:(tb__ "0|0|
S0S17S26S27SaS2VC0;A1A1A2S18A3").
Hypothesis W_x : ltac2:(tb__ "0|0|
S0S17S11S2VCX;A1A1S18A3").
Hypothesis D_x : ltac2:(tb__ "0|4|
S0S1dS1bS19S1bS8S8A2M0A1M1S19S9A1M2A2M3A1S3eS2S4VLX;A1A1S2VCX;A1A2S1cG3S1eG1G2S16G0S1eS8S8S52Veb;A1Veb;A4S1aG0A1A3S1aS9A1A4A2A3").

Hypothesis SK_x : ltac2:(tb__ "0|1|
S0S19S1bS1bS8S8A2S8A2M0A1S23S7G0S32S10S2VCX;A1A1A4S23S7G0S32S1fS7S50VW;A1S16S7S41S16S7S42S16S7S2aS16S7S2bS1aS7A1A3A3A3A3A3A4A3").
Hypothesis XF_x : ltac2:(tb__ "0|0|
S56S9S4fVW;Vst;A2SeS2VCX;A1A1A3").
Hypothesis XX_x : ax_X CX = [].
Hypothesis NX_x : ltac2:(tb__ "0|0|
S0S17S26S27SaS2VCX;A1A1A2S18A3").
Hypothesis IC_x : ltac2:(tb__ "0|0|
S0S1dS3aA1S5bS25S14S2VCX;A1A1A2S1cS3aS3bA2A3").
Hypothesis R17_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1Z11A2SbZdeA1A3").
Hypothesis R10_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZaA2Veb;A3").
Hypothesis BEL_x : ltac2:(tb__ "0|0|
S0S17S15SaS2VCX;A1A1Veb;A2S18A3").
Hypothesis R11_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZbA2SbZ40000A1A3").
Hypothesis R12_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZcA2SbZ3A1A3").
Hypothesis R13_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZdA2SbZ32A1A3").
Hypothesis R14_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZeA2SbZffffffffffffffffA1A3").
Hypothesis R15_x : ltac2:(tb__ "0|0|
S0S8ScS2VCX;A1ZfA2SbZ0A1A3").

Hypothesis R_m : ltac2:(tb__ "0|1|
S0S1dS19S3A1M0A1S5S25VF;S16S22Zde378S1aS22A1A3VG1;S18A5S1cG0S16S3VLM;S1aS3A1A3A2A3").
Hypothesis LN_g : ltac2:(tb__ "0|0|
S0S17S13S2VG1;A1A1S20A3").
Hypothesis NX_g : ltac2:(tb__ "0|0|
S0S17S26S27SaS2VG1;A1A1A2S18A3").
Hypothesis SK_m : ltac2:(tb__ "0|1|
S0S19S1bS1bS8S8A2S8A2M0A1S23S7G0S32S10S2VEM;A1A1A4S23S7G0S32S1fS7S50VW;A1S16S7S41S16S7S42S16S7S2aS16S7S2bS16S7S53Veb;A1S1aS7A1A3A3A3A3A3A3A4A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S56S9S4fVW;Vst;A2SeS2VEM;A1A1A3").
Hypothesis XX_m : ax_X EM = [].
Hypothesis W_mr : ltac2:(tb__ "0|0|
S0S17S11S2VCMR;A1A1S18A3").
Hypothesis D_mr : ltac2:(tb__ "0|4|
S0S1dS1bS19S1bS8S8A2M0A1M1S19S9A1M2A2M3A1S3eS2VEM;A1S2VCMR;A1A2S1cG3S1eG1G2S16G0S1eS8S8S61Veb;A1SbZ8000A1A4S1aG0A1A3S1aS9A1A4A2A3").
Hypothesis W_mc : ltac2:(tb__ "0|0|
S0S17S11S2VCMC;A1A1S18A3").
Hypothesis E_ms : ltac2:(tb__ "0|1|
S0S1dS19S7A1M0A1S5dVCMC;S3cS29VCMC;A1A3S1cG0S28VCMC;A1A2A3").
Hypothesis CHK_ms : ltac2:(tb__ "0|0|
S0S17S5cVCMC;S3cS29VCMC;A1S28VCMC;A1S23S3S6S4S3dA4A5S18A3").
Hypothesis NF_ms : ltac2:(tb__ "0|0|
S0S17S26S59SaS2VCMC;A1A1A2S18A3").
Hypothesis NX_ms : ltac2:(tb__ "0|0|
S0S17S26S27SaS2VCMC;A1A1A2S18A3").
Hypothesis FBC_ms : ltac2:(tb__ "0|1|
S0S17S55S9S12SaS2VCMC;A1M0A1A1SeG0A1A3S18A3").
Hypothesis FBT_ms : ltac2:(tb__ "0|0|
S0S17S55S9S12SaS2S60VCMC;S29VCMC;A1S28VCMC;A1A3A1A1A1SeS2VCMC;A1A1A3S18A3").
Hypothesis ND_r : ltac2:(tb__ "0|0|
S0S17S5aS2fVDM;A1A1S18A3").
Hypothesis NO_r : (1 <= nobj DM)%nat.
Hypothesis OB_r : ltac2:(tb__ "0|1|
S0S19S7A1S10S2VRM;A1A1M0S1fS7S24S7S57S30VDM;A1U2A2G0A3S16S7S53Veb;A1S16S7S54Veb;A1S1aS7A1A3A3A3A3").

Theorem piece_full : ltac2:(tb__ "0|1|
SfS19S33Q40A1A1M0S58SfG0VTR;S3fS25S46VA;VKc;Vrb;Vtp0;Vmd0;S4cVp;U3Vph;A3A6S31VDM;A1R2R1A5R3A2Ftp';Fr';VTR;S3fS25S46VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6VC0;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x7050c] C0 [LX] ph r tp Q R_x LN_0 NX_0).
  intros L r1 [<-|[]] _.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state LX) (ax_S CX) _ _ ph r1 tp Q W_x D_x ltac:(apply Pos.eqb_refl)).
  { intros tr md (HFz & HGh & _) _. split; [|constructor]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    destruct HBn as (_ & _ & HB3). apply (a0_val r1 eb B (HBv r1 HFz HGh)).
    destruct (proj1 (Z.mod_divide B 65536 ltac:(clear; lia)) HB3) as [q Hq]. rewrite Hq. replace (q * 65536) with (q * 16 * 4096) by (clear; lia). apply Z_mod_mult. }
  change (ax_setS (la_state LX) (ax_S CX)) with CX.
  assert (HBn' : ag_spacebeg (aa_geom A) + 4294967296 <= B /\ B + 262144 <= ag_spacebeg (aa_geom A) + 137438953472 /\ B mod 4096 = 0).
  { destruct HBn as (H1 & H2 & HB3). split; [exact H1|]. split; [exact H2|].
    destruct (proj1 (Z.mod_divide B 65536 ltac:(clear; lia)) HB3) as [q Hq]. rewrite Hq. replace (q * 65536) with (q * 16 * 4096) by (clear; lia). apply Z_mod_mult. }
  apply (piece_commit A Kc rb tp0 md0 TR KIT HKc W st rho HW HE p eb ph PH0 PORD PQ HBv HBn' HROOM_c CX SK_x XF_x XX_x NX_x IC_x R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x r1 tp Q).
  fold G1.
  apply (piece_map A Kc rb tp0 md0 TR KIT HKc W st rho HW HE p eb (ph_set p 1 ph) (ph_get_set p 1 ph) (ph_quiet_set p 1 ph PQ) HBv HBn HROOM_r
           F G1 LM R_m LN_g NX_g SK_m XF_m XX_m W_mr D_mr W_mc E_ms CHK_ms NF_ms NX_ms FBC_ms FBT_ms ND_r NO_r OB_r r1 tp Q).
  intros r' tp'. rewrite ph_set_set. exact (HC r' tp').
Qed.
End PIECE.
End SpineMallocQ11.

(* [comment removed for export] *)
Module SpineCallocU1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "nat"; "list"; "prod"; "cons"; "pair"; "nil"; "bool"; "true"; "andb"; "false"; "app"; "Some"; "option"; "None"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "valuation"; "cell"; "rm"; "mkCell"; "rw"; "ss_objs"; "eval"; "smatch"; "sstate"; "sv_eqb"; "DUnknown"; "c_off"; "c_val"; "c_width"; "mkObj"; "sprop"; "ss_facts"; "swf"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "lt"; "eqb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocU1"; "JU"; "cell_inb"; "O_arrF"; "O_pcmZ"; "arr_okb"; "cU0"; "NU2"; "O_arr0"; "cU2"; "cnt_spec"; "idx1"; "idx2"; "kU1"; "kU2"; "perm_okb"; "sU1"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_cache_inited"; "ag_thread"; "topG"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "O_pcc0"; "pc_base"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "nobj"; "addobjs"; "nxt"; "keepn"; "selobjs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI"; "initA"; "ZI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "max_count"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "view"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5"; "rho_after"; "posts_conv"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "w_cfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "PCE"; "entryR"; "frozen"; "mlink"; "ph0"; "rmlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "mem_keptA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "CLS30"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "cfacts"; "rigids"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocU1.UJ"; "JU"; "umem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "rhoM_of"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "JK"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "le"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.CRebuildRN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition NU0 : list carve_spec := ltac2:(tb__ "0|7|
S5S4S4S4S16S0A2M0S0A2M1S3S4S4S0S2A2M2S16A2M3A1M4A2M5S6G1G4S6G0S0S6S16S0S52Z4M6A4Z8A4S5G3S6G2S16S6S0S2G6U4A4S17Z0A1A4S7G3A1A3A4S7G5A1A3").
Definition O_pcmZ : sobj := ltac2:(tb__ "0|3|
S8aS52Z4M0Z8S5S4S4S0S2A2M1S16A2M2S6G1S16S6S0S2G0U4A4S17Z0A1A4S7G2A1A3A4").
Definition cnt_spec : list (Z * nat * sv) := ltac2:(tb__ "0|1|
S4fS0S4S4S0S2A2M0S16A2S0S6G0S16S6S0S2S2aZd0S2cZ50R1A2A2U4A4S17Z0A1A4Lc;S7fA4").
Definition NU1 : list carve_spec := ltac2:(tb__ "0|4|
S5S4S4S4S16S0A2M0S0A2M1S3S4S4S0S2A2S16A2A1M2A2M3S6G1G2S6G0S0S6S16S0S5dZ120A4Zad0A4S3fA4S7G3A1A3").
Definition O_arr0 : sobj := carved vT 288 2768 cnt_spec.
Definition O_arrF (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S26S5dS17Z120A1S17Zad0A1Vcells;S22A5").
Definition NU2 : list carve_spec := ltac2:(tb__ "0|7|
S5S4S4S4S16S0A2M0S0A2M1S3S4S4S0S2A2M2S16A2M3A1M4A2M5S6G1G4S6G0S0S6S16S0S52Z0M6A4Z4A4S5G3S6G2S16S6S0S2G6U4A4S17G6A1A4S7G3A1A3A4S7G5A1A3").
Lemma NU2_objs : ltac2:(tb__ "0|0|
S11S3S15A1S4fS8dS15S8cS3cA4S5S15S51S7S15A1A3A3"). Proof. reflexivity. Qed.

Definition cU0 (E : axst) : axst := ltac2:(tb__ "0|0|
S55VE;S5S15S39S7S15A1A3S56VE;A1A3").

Definition idx1 (E : axst) : list nat := ltac2:(tb__ "0|2|
ScS2S50U0S35S54VE;A1M0U3A2M1A2S5S2S35G0U2A2S5S2G1S5S2S35G0U1A2S7S2A1A3A3A3A3").
Definition sU1 (E : axst) : axst := ltac2:(tb__ "0|0|
S58VE;S40VE;A1A2").
Definition kU1 (E : axst) : axst := ltac2:(tb__ "0|0|
S57S45VE;A1S35S54VE;A1U2A2A2").
Definition cU1 (E : axst) : axst := ltac2:(tb__ "0|0|
S55S42VE;A1S5S15S3dS7S15A1A3S56VE;A1A3").
Definition kU2 (E : axst) : axst := ltac2:(tb__ "0|0|
S57VE;S35S54VE;A1U1A2A2").
Definition cU2 (E : axst) : axst := ltac2:(tb__ "0|0|
S55S43VE;A1S5S15S51S7S15A1A3S56VE;A1A3").

Definition idx2 (E : axst) : list nat := ltac2:(tb__ "0|2|
ScS2S50U0S35S54VE;A1M0U2A2M1A2S5S2S35G0U1A2S5S2G1S7S2A1A3A3A3").
Definition eU (E : axst) : axst := ltac2:(tb__ "0|1|
S58S3eVE;A1M0S41G0A1A2").

Definition perm_okb (n : nat) (idxs : list nat) : bool := ltac2:(tb__ "0|0|
SaSaS6eVidxs;A1S47S2S2S90R1Vn;A2Li;Vidxs;A3A2S47S2S2S48S2S8fR1A1Vidxs;A3Li;S50U0Vn;A2A3A2").
Lemma perm_okb_sound : ltac2:(tb__ "0|0|
S2S3S2A1S11S8S44R2R1A2S9A3S10S11S8S6eR2A1S9A3S10S2S46S2R1R3A3S66R2R5A2F_;Fi;S2S66R1R4A2S46S2R2R4A3F_;Fi;A2A2F_;Fidxs;Fn;").
Proof.
  intros n idxs H. unfold perm_okb in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [exact H1|]. split.
  - intros i Hi. apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) H2 i Hi).
  - intros i Hi. pose proof (proj1 (forallb_forall _ _) H3 i ltac:(apply in_seq; lia)) as X.
    apply existsb_exists in X as (j & Hj & E). apply Nat.eqb_eq in E. subst j. exact Hj.
Qed.

Definition cell_inb (off w v : Z) (cells : list cell) : bool := ltac2:(tb__ "0|0|
S48S19S19SaSaS21S23R1A1S17Voff;A1A2S2eS25R1A1Vw;A2A2S21S24R1A1S17Vv;A1A2A2Lcl;Vcells;A3").
Definition arr_okb (cells : list cell) : bool := ltac2:(tb__ "0|2|
S47S0S0SaSaS37S2aZd0S2cZ50R1A2M0A2Z4M1Z0Vcells;A4S37S2aZd4G0A2G1S5fR1A1Vcells;A4A2S37S2aZd8G0A2Z8S5eR1A1Vcells;A4A2Lc;S7fA3").
Lemma cell_inb_In : ltac2:(tb__ "0|0|
S0S0S0S3S19A1S11S8S37R4R3R2R1A4S9A3S46S19S1bS17R5A1R4S17R3A1A3R2A3F_;Fcells;Fv;Fw;Foff;").
Proof.
  intros off w v cells H. unfold cell_inb in H. apply existsb_exists in H as ([o w' v'] & Hin & E). cbn [c_off c_width SymState.c_val] in E.
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply sv_eqb_sound in E1. apply sv_eqb_sound in E3. apply Z.eqb_eq in E2.
  subst o w' v'. exact Hin.
Qed.
Lemma arr_okb_In : ltac2:(tb__ "0|2|
S3S19A1S0S11S8S3aR2A1S9A3S10S2bZ1R2A2S2bR2Z1eA2A2S10S46S19S1bS17S2aZd0S2cZ50R3A2M0A2A1Z4M1S17Z0A1A3R4A3S10S46S19S1bS17S2aZd4G0A2A1G1S17S5fR3A1A1A3R4A3S46S19S1bS17S2aZd8G0A2A1Z8S17S5eR3A1A1A3R4A3A2A2F_;F_;Fc;Fcells;").
Proof.
  intros cells c H Hc. unfold arr_okb in H. pose proof (proj1 (forallb_forall _ _) H c (proj2 (In_CLS30 c) Hc)) as X. cbv beta in X.
  apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
  split; [exact (cell_inb_In _ _ _ _ X1)|]. split; [exact (cell_inb_In _ _ _ _ X2) | exact (cell_inb_In _ _ _ _ X3)].
Qed.

Lemma uninit_frame : ltac2:(tb__ "0|5|
S4aS18S3S2fQ40A1A1S33S7dS7eR4R3R2R1A5S11S8S4cR5A1SbA3S4dS4bR6A1A1S0S62S7eS1aR6A1A2S63S10S0S0S10S2bZ1R2A2S2bR2Z1eA2A2S10S2bS2aS2aR5Zd0A2S2cZ50M0R3A2A2M1R2A2S2dR2S2aG1G0A2A2A2S11SeS2fQ8M2A1M3A1M4R5R3A1SdG3S31G2Z0A2A2A3F_;F_;Fz;Fc;S0S10S2bS2aR3Za80A2R1A2S2dR1S2aR3Zc60A2A2A2S13G3G3S11G4R4R3A1SdG3R1A2A3Lb;A2F_;Fz;A2Tm0;TT;F_;F_;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 HA Hini T m0. pose proof HA as (HG & _ & _ & HRest & _).
  destruct HRest as (_ & _ & Hprim & _ & _ & _ & _ & HTH & _). destruct Hprim as (_ & _ & _ & PC).
  assert (MT : forall z, T <= z < T + 0x1000 -> maskv (fs_footb (aa_geom A)) m0 z = m0 z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  split.
  - intros c z Hc Hz. pose proof (PC c Hc) as P4. unfold class_repr in P4.
    destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CN & _).
    destruct (CN Hini) as [_ FL]. fold T in FL. rewrite <- MT by (clear -Hz Hc; lia). exact (FL z Hz).
  - intros z Hz. destruct HTH as [_ TH2]. fold T in TH2. destruct (TH2 z Hz) as [b Hb]. exists b. rewrite <- MT by (clear -Hz; lia). exact Hb.
Qed.

Section UJ.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Let T : Z := ag_thread (aa_geom A).

Definition umem (s : bool) (m0 m : bview) : Prop := ltac2:(tb__ "0|6|
S8OLs;Vs;S10S0S12S5aVT;R1A2M0A1S11SeS2fQ8A1M1A1M2Vm;R2A1M3Vm0;R2A1A3F_;Fz;S10S0G0S12S11G2G3SfG1A1A3A1F_;Fz;S0S10S2bZ1R1A2S2bR1Z1eA2A2S10S60Vm;S61S2aS2aVT;Zd0A2S2cZ50R2A2A2M4U4M5Z0A3A2S10S60Vm;S61S2aG4Z4A2G5S5fR2A1A3A2S60Vm;S61S2aG4Z8A2U8S5eR2A1A3A2A2A2F_;Fc;A2A2S0S11G2Vm;R1A1Vm0;R1A1A3Fz;X8x2").
Definition JU (s : bool) : jpredA := ltac2:(tb__ "0|2|
S18S3S2fQ40A1A1S3S34A1S33S10S76Vrb;R4A2S10VKc;R2R1A2S10S77VA;Vrb;Vtp0;Vmd0;S78R3R1A7S10S86Vs;S62S32S1aVrb;A1M0A2S62S32S1aR4A1M1A2A3S79G0G1A2A2A2A2A2Lmd;Ltr;Ltp;Lr;").

Lemma JU_K : ltac2:(tb__ "0|0|
S8S8eVKc;S85R1A1A2Fs;").
Proof. intros s r t tr md (_ & HK & _). exact HK. Qed.

Lemma JU_stable : ltac2:(tb__ "0|0|
S8S1S7cVKc;A1S91PdcR2A2S71S32R3S85R4A1A3F_;F_;Fn;Fs;").
Proof.
  intros s n HKc Hn r r' tp tr md md' Hag Hme (HF & HK & HM & HR & HRM).
  destruct Hag as (Hw & Hl & Hm).
  assert (Erm : rm r' = rm r) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  assert (Hlt : forall i, (i < 220)%positive -> rw r' i = rw r i) by (intros i Hi; symmetry; apply Hw; lia).
  destruct Hme as ((mat' & ->) & Hpaid & _).
  split; [|split; [|split; [|split]]].
  - destruct HF as [F1 F2]. split; [intros i Hi; rewrite (Hlt i Hi); exact (F1 i Hi) | intros l; rewrite <- (Hl l); exact (F2 l)].
  - rewrite with_vm_backing_with_vm. apply HKc. exact HK.
  - unfold mlink in *. cbn zeta in *. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|].
    exists tp1. split; [exact M7|]. split; [exact M8|]. split; [exact M9|]. rewrite Hpaid. exact M10.
  - rewrite Erm. exact HR.
  - rewrite Erm. exact HRM.
Qed.
End UJ.

Lemma pc_base_val : ltac2:(tb__ "0|0|
S4aS18S18S80R3R2A2S81R4R3R2A3S11S0S30Q40S1eR3S52A2A2S74R5R4A2A3F_;F_;Fr;Frb;FA;").
Proof.
  intros A rb r CF RG. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & _ & _) & _).
  destruct RG as (_ & _ & E151 & _ & _ & _ & _ & E158).
  unfold pc_base, vT, V_CLS, PCE. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
  rewrite (Z.mod_small (_ * 80)) by lia. rewrite (Z.mod_small (_ + 208)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma vT_val : ltac2:(tb__ "0|0|
S4aS18S18S80R3R2A2S81R4R3R2A3S11S0S30Q40S1eR3S5dA2A2S4dS4bR5A1A1A3F_;F_;Fr;Frb;FA;").
Proof.
  intros A rb r CF RG. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as (_ & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & _ & _) & _).
  destruct RG as (_ & _ & E151 & _). unfold vT. cbn [eval]. rewrite E151. apply u64_lit. lia.
Qed.

Section UENTRY.
Variable nW : nat. Variable st : ustop.
Let W : list ulink := Wcan nW.
Variable E3 : axst.
Hypothesis SK3 : ltac2:(tb__ "0|1|
S11S3S4S4S16S16A2S16A2M0A1S4fS15G0S84S1dS5bVE3;A1A1A4S4fS15G0S84ScS15S83VW;A1S5S15S51S5S15S53S7S15A1A3A3A3A4A3").
Hypothesis XX3 : ax_X E3 = [].
Hypothesis XF3 : ltac2:(tb__ "0|0|
S49S27S82VW;Vst;A2S28S5bVE3;A1A1A3").
Hypothesis WU0 : ltac2:(tb__ "0|0|
S11S8S29S5bS3bVE3;A1A1A1S9A3").

Lemma uninit_entry : ltac2:(tb__ "0|2|
S4aS7aS18S18S3S2fQ40M0A1A1S6bS8bVW;Vst;A2S11S8S4cR7A1SbA3S11S0S88R8S30G0S1cR6PcA2A2A2Z0A3S70S32S89VW;Vst;R9R8R7A5VE3;R6R5R4A6S10S75RaR7R6S6aS6cR5A1A1M1VW;Vst;R8A7S70S32S36RaR9R7R6G1SbA6S3bVE3;A1R7R6R5A6A2F_;F_;F_;F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w HW Hini Hcnt H.
  pose proof H as [HsmA [Hag HJ]]. pose proof Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN, HB.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite <- E12 in Hcnt. set (nv := bv_unsigned (rw rhoE 12%positive)) in *.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (Hnv : nv <= 64512).
  { pose proof (proj1 (Forall_forall _ _) HFa (SPUle (SVar 12) (SLit 64512)) (XF3 (SPUle (SVar 12) (SLit 64512)) ltac:(unfold BASEF; apply in_or_app; right; unfold F_gen; cbn; tauto))) as F.
    cbn [holds eval] in F. rewrite u64_lit in F by lia. exact F. }
  assert (HE : entryR A rhoE tp (cfg_model (w_cfg w)) W st rho).
  { unfold entryR. split; [exact Hag|]. split; [exact HA|]. split; [exact Htp|]. split; [exact HU|]. split; [exact HB|]. split; [lia|]. split; [exact Htop|]. split; [exact Hcnt|].
    exact (MI_ivs_wf segs _ _ (proj1 (proj2 HsmA))). }
  split; [exact HE|].
  assert (HFz : frozen rhoE rhoE) by (split; intros; reflexivity).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (pc_base_val A rhoE rhoE CF RG) as EB. pose proof (vT_val A rhoE rhoE CF RG) as ET.
  unfold cfacts in CF. cbn zeta in CF. fold nv in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  set (c := cls_of nv) in *. set (T := ag_thread (aa_geom A)) in *.
  assert (PCr : PCE A rhoE = T + 208 + 80 * c) by (unfold PCE; fold nv c T; clear; lia).
  destruct (uninit_frame A rhoE tp _ HA Hini) as (FZ & _). fold T in FZ.

  assert (Ha : SPA segs (JU A Kc rhoE tp (cfg_model (w_cfg w)) false) E3 rhoE tp w).
  { split; [exact HsmA|]. unfold JU. split; [exact HFz|]. split; [exact HK|]. split; [|split; [intros z; reflexivity | intros a _; reflexivity]].
    unfold mlink, ph0, committed, revealedp, subU, subF. cbn [ph_u ph_f Nat.leb].
    repeat (split; [reflexivity|]). exists []. cbn [app length Z.of_nat]. split; [reflexivity|]. split; [intros p []|]. split; [lia | lia]. }

  destruct (arm_base_disj A rhoE tp _ W st rho (ax_S E3) [O_pcc0; O_st] rhoE _ HW HE HFz Hsm SK3 XF3) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|? ?]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence).
  assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (RNc : obj_range rhoE oc = (T + 208 + 80 * c, T + 208 + 80 * c + 4)).
  { rewrite (obj_range_skel rhoE oc O_pcc0 SKc). unfold O_pcc0. rewrite obj_range_mk by (clear; lia). rewrite EB, PCr. f_equal; clear; lia. }
  assert (RNs : obj_range rhoE os = (T + 2768, T + 3168)).
  { rewrite (obj_range_skel rhoE os O_st SKs). unfold O_st. rewrite obj_range_mk by (clear; lia). rewrite ET. reflexivity. }
  apply (SPA_carve_list segs _ rhoE E3 tp w NU0 (nxt E3) Ha WU0).
  - apply Pos.le_refl.
  - unfold NU0. apply Forall_cons; [|apply Forall_nil].
    rewrite EB, PCr. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear -C1 T1; lia|]. split; [clear -C1 T1 T2 TG; lia|].
    split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
    assert (BY : forall off, 4 <= off < 8 -> rd_of segs (rm rhoE) (Z_to_bv 64 (T + 208 + 80 * c + off)) = Some (Z_to_bv 8 0)).
    { intros off Hoff. pose proof (FZ c (T + 208 + 80 * c + off) C1 ltac:(clear -Hoff; lia)) as Hb. rewrite view_in in Hb by (clear -Hoff C1 T1 T2 TG; lia). exact Hb. }
    split.
    { intros off Hoff. eapply wok_rd_off_image2; [| |exact (BY off Hoff)]; [clear -Hoff C1 T1 T2 TG; lia | clear -Hoff C1 TI; lia]. }
    split; [|unfold xwords_clear; rewrite XX3; intros rr y j []].
    apply Forall_cons; [|apply Forall_nil]. intros j Hj. cbn [eval].
    rewrite (enc_bytes_zero_nth 4 (Z_to_bv 64 0) j ltac:(apply u64_lit; clear; lia) Hj).
    replace (T + 208 + 80 * c + 4 + Z.of_nat j) with (T + 208 + 80 * c + (4 + Z.of_nat j)) by (clear; lia). apply BY. clear -Hj. lia.
  - cbn [map carve_obj NU0]. unfold carved. apply Forall_cons; [|apply Forall_nil]. rewrite obj_range_mk by (clear; lia). rewrite EB, PCr.
    rewrite EO. apply Forall_app. split.
    + apply BZ. left. fold T. clear -C1. lia.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; [rewrite RNc | rewrite RNs]; unfold ranges_disjoint; cbn [fst snd]; clear -C1; lia.
  - cbn [map carve_obj NU0 pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.
End UENTRY.

Section USTEPS.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variables (W : list Iface.ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S75VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis Hini : aa_cache_inited A = false.
Notation JUp := (JU A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let T : Z := ag_thread (aa_geom A).

Lemma u_nums : ltac2:(tb__ "0|3|
S10S10S2bZ1Vc;A2S2bVc;Z1eA2A2S10S2bZ1000M0VT;A2S10S2bS2aVT;G0A2M1S4eS4bVA;A1A1M2A2S10S2bG2Z7fffff800000A2S10S14S2bG1Z10000A2S2bZ646000VT;A2A2S11S0S74VA;Vrb;A2S2aS2aVT;Zd0A2S2cZ50Vc;A2A2A3A2A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c T in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  split; [exact C1|]. split; [exact T1|]. split; [exact T2|]. split; [exact TG|]. split; [exact TI|]. unfold PCE. fold nv c T. lia.
Qed.

Lemma u_release1 : ltac2:(tb__ "0|3|
S20S3S15A1M0S18S3S2fQ40A1A1S3S34A1M1S67S33S33S11G0S1dR8A1ScS15R7S5S15S51S5S15S39S7S15A1A3A3M2A3A3S1fS32R7R9S6G1S68R5S69R4R3A2A4A4S36VA;VKc;Vrb;Vtp0;Vmd0;SbR8R7R6R3AaS36VA;VKc;Vrb;Vtp0;Vmd0;SbS6fR9G2R6A3R8R7R4AaF_;F_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;FK;FS;").
Proof.
  intros S K r tp tr ms md mdJ HO Hsm (HFz & HK & HM & HR & HRM).
  destruct u_nums as (C1 & T1 & T2 & TG & TI & PCr).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (pc_base_val A rb r CF RG) as EB. rewrite PCr in EB.
  destruct HE as (_ & HA & _). destruct (uninit_frame A rb tp0 md0 HA Hini) as (FZ & _). fold T in FZ.
  set (r3 := rho_absorb r [O_pcc0; O_pcmZ] ms).
  assert (RC : obj_range r O_pcc0 = (T + 208 + 80 * c, T + 208 + 80 * c + 4)).
  { unfold O_pcc0. rewrite obj_range_mk by lia. rewrite EB. f_equal; lia. }
  assert (RM : obj_range r O_pcmZ = (T + 208 + 80 * c + 4, T + 208 + 80 * c + 8)).
  { unfold O_pcmZ, carved. rewrite obj_range_mk by lia. rewrite EB. reflexivity. }

  assert (EZ : forall k j, (j < k)%nat -> nth j (enc_bytes k (Z_to_bv 64 0)) (Z_to_bv 8 0) = Z_to_bv 8 0) by (intros k j Hj; apply enc_bytes_zero_nth; [apply u64_lit; lia | exact Hj]).
  assert (M3 : forall z, T + 208 + 80 * c <= z < T + 208 + 80 * c + 8 -> view segs (rm r3) z = Some (Z_to_bv 8 0)).
  { intros z Hz. destruct (Z_lt_dec z (T + 208 + 80 * c + 4)) as [LT|GE].
    - destruct (absorb_obj r S tr ms md K [O_pcc0; O_pcmZ] O_pcc0 Hsm HO (or_introl eq_refl)) as (_ & AS & _).
      destruct (AS (mkCell (SLit 0) 4 (SLit 0)) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb (Z.to_nat (z - (T + 208 + 80 * c))) ltac:(cbn [c_width]; lia)).
      cbn [ob_base O_pcc0 eval c_off SymState.c_val c_width] in ASb. rewrite soff_lit_small in ASb by lia. fold (eval r pc_base) in ASb. rewrite EB in ASb.
      rewrite EZ in ASb by lia.
      unfold r3. rewrite view_in by lia. replace z with (T + 208 + 80 * c + 0 + Z.of_nat (Z.to_nat (z - (T + 208 + 80 * c)))) at 1 by lia. exact ASb.
    - destruct (absorb_obj r S tr ms md K [O_pcc0; O_pcmZ] O_pcmZ Hsm HO (or_intror (or_introl eq_refl))) as (_ & AS & _).
      destruct (AS (mkCell (SLit 4) 4 (SLit 0)) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb (Z.to_nat (z - (T + 208 + 80 * c + 4))) ltac:(cbn [c_width]; lia)).
      cbn [ob_base O_pcmZ carved eval c_off SymState.c_val c_width] in ASb. rewrite soff_lit_small in ASb by lia. fold (eval r pc_base) in ASb. rewrite EB in ASb.
      rewrite EZ in ASb by lia.
      unfold r3. rewrite view_in by lia. replace z with (T + 208 + 80 * c + 4 + Z.of_nat (Z.to_nat (z - (T + 208 + 80 * c + 4)))) at 1 by lia. exact ASb. }
  unfold JU. split; [exact HFz|]. split; [exact HK|]. split; [exact HM|]. split.
  - cbn [umem] in HR |- *. intros z. destruct (Z_le_dec (T + 208 + 80 * c) z) as [H1|H1]; [destruct (Z_lt_dec z (T + 208 + 80 * c + 8)) as [H2|H2]|].
    + rewrite (M3 z (conj H1 H2)). symmetry. apply (FZ c z C1). lia.
    + unfold r3. rewrite view_absorb_out; [exact (HR z)|]. intros o [<-|[<-|[]]]; [rewrite RC | rewrite RM]; cbn [fst snd]; lia.
    + unfold r3. rewrite view_absorb_out; [exact (HR z)|]. intros o [<-|[<-|[]]]; [rewrite RC | rewrite RM]; cbn [fst snd]; lia.
  - apply (rmlink_absorb _ r [O_pcc0; O_pcmZ] ms HRM). intros o [<-|[<-|[]]]; [rewrite RC | rewrite RM]; cbn [fst snd]; unfold IMG_LO, IMG_HI; lia.
Qed.

Lemma u_release2 : ltac2:(tb__ "0|3|
S20S3S15A1M0S3S19A1S18S3S2fQ40A1A1S3S34A1M1S67S33S33S11G0S1dR9A1ScS15R8S5S15S38R7A1S7S15A1M2A3A3A3S11S8S3aR8A1S9A3S1fS32R8RbS6G1S68R6S69R5R4A2A4A4S36VA;VKc;Vrb;Vtp0;Vmd0;SbR9R8R7R4AaS36VA;VKc;Vrb;Vtp0;Vmd0;S9S6fRaS5S15S38RbA1G2A3R7A3R9R8R5AaF_;F_;F_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;Fcells;FK;FS;").
Proof.
  intros S K cells r tp tr ms md mdJ HO HOK Hsm (HFz & HK & HM & HR & HRM).
  destruct u_nums as (C1 & T1 & T2 & TG & TI & PCr).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (vT_val A rb r CF RG) as ET. fold T in ET.
  set (r3 := rho_absorb r [O_arrF cells] ms).
  assert (RA : obj_range r (O_arrF cells) = (T + 288, T + 2768)).
  { unfold O_arrF. rewrite obj_range_mk by lia. rewrite ET. reflexivity. }
  destruct (absorb_obj r S tr ms md K [O_arrF cells] (O_arrF cells) Hsm HO (or_introl eq_refl)) as (_ & AS & AP & _).
  cbn [ob_base O_arrF ob_cells ob_dflt] in AS, AP. rewrite ET in AS, AP.
  assert (CELL : forall off w v, In (mkCell (SLit off) (Z.of_nat w) (SLit v)) cells -> 0 <= off < 4096 -> cell_ok (view segs (rm r3)) (mkACell (T + off) w v)).
  { intros off w v Hin Hoff j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    destruct (AS _ Hin) as (B1 & B2 & ASb). cbn [c_off c_width SymState.c_val] in B1, B2, ASb. rewrite soff_lit_small in B1, B2, ASb by lia.
    unfold obj_lo_of, obj_hi_of in B1, B2. cbn [ob_lo ob_hi O_arrF] in B1, B2. rewrite !soff_lit_small in B1, B2 by lia.
    specialize (ASb j ltac:(rewrite Nat2Z.id; exact Hj)). rewrite Nat2Z.id in ASb. cbn [eval] in ASb.
    unfold r3. rewrite view_in by lia. exact ASb. }
  unfold JU. split; [exact HFz|]. split; [exact HK|]. split; [exact HM|]. split.
  - cbn [umem] in HR |- *. fold T. split; [|split].
    + intros z Hz. unfold r3. rewrite view_absorb_out; [exact (HR z)|]. intros o [<-|[]]. rewrite RA. cbn [fst snd]. exact Hz.
    + intros z Hz. unfold ZI in Hz. destruct (AP (or_introl eq_refl) (z - T)) as [x Hx].
      { unfold obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi O_arrF]. rewrite !soff_lit_small by lia. lia. }
      replace (T + (z - T)) with z in Hx by lia. unfold r3. rewrite view_in by lia. rewrite Hx. discriminate.
    + intros c' Hc'. destruct (arr_okb_In cells c' HOK Hc') as (I1 & I2 & I3).
      split; [|split].
      * replace (T + 208 + 80 * c') with (T + (208 + 80 * c')) by lia. apply (CELL _ 4%nat); [exact I1 | lia].
      * replace (T + 208 + 80 * c' + 4) with (T + (212 + 80 * c')) by lia. apply (CELL _ 4%nat); [exact I2 | lia].
      * replace (T + 208 + 80 * c' + 8) with (T + (216 + 80 * c')) by lia. apply (CELL _ 8%nat); [exact I3 | lia].
  - apply (rmlink_absorb _ r [O_arrF cells] ms HRM). intros o [<-|[]]. rewrite RA. cbn [fst snd]. unfold IMG_LO, IMG_HI. lia.
Qed.

Lemma u_rebuild : ltac2:(tb__ "0|1|
S18S3S2fQ40A1A1S3S34A1S33S36VA;VKc;Vrb;Vtp0;Vmd0;S9R4R3R2R1AaS10S7dS32S59VA;A1M0R5R4R2A5S7bVCST;VXGL;VA;G0S1aVrb;A1S1aR5A1A6A2F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md (HFz & HK & HM & HR & HRM).
  pose proof HE as (_ & HA & _). pose proof HA as (_ & _ & _ & _ & HM0 & _ & HB0).
  unfold mlink in HM. cbn zeta in HM. unfold ph0, committed, revealedp, subU, subF in HM. cbn [ph_u ph_f Nat.leb] in HM.
  destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & _ & M10).
  assert (Etp1 : tp1 = []).
  { destruct tp1 as [|p tp1']; [reflexivity|]. exfalso. destruct (M8 p (or_introl eq_refl)) as [_ [[X _]|[X _]]]; discriminate X. }
  subst tp1. cbn [app length Z.of_nat] in M7, M10. subst tp.
  cbn [umem] in HR. fold T in HR. destruct HR as (L1 & L2 & L3).
  apply (init_rebuild CST XGL HCST HXGL A rb r tp0 tp0 md0 md HA Hini).
  - exact L1.
  - intros z Hz. pose proof (L2 z Hz) as D. change (exists b, view segs (rm r) z = Some b). destruct (view segs (rm r) z) as [b|]; [exists b; reflexivity | contradiction].
  - exact HRM.
  - exact L3.
  - apply (model_inv_fields A (initA A) tp0 md0 md); try reflexivity; try assumption. clear -M10. lia.
  - eapply bandtp_mono; [|exact HB0]. intros z _ Hd. change (view segs (rm r) z <> None). change (view segs (rm rb) z <> None) in Hd.
    assert (D : ZI T z \/ ~ ZI T z) by (unfold ZI; clear; lia).
    destruct D as [D|D]; [exact (L2 z D) | rewrite (L1 z D); exact Hd].
Qed.

Lemma rhoM_init : ltac2:(tb__ "0|0|
S18S18S1S11S2fQ40A1S1cS87S59VA;A1S64R3R2A2A2R1A2S1cS87VA;R3A2R1A2A3Fi;Fr;Frho0;").
Proof. intros rho0 r i. reflexivity. Qed.

Lemma JG_init : ltac2:(tb__ "0|0|
S18S3S2fQ40A1A1S3S34A1S33S36VA;VKc;Vrb;Vtp0;Vmd0;S9R4R3R2R1AaS89VW;Vst;S59VA;A1VKc;S64Vrho;R5A2R5R4R3R2A9F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HJ. pose proof HJ as (HFz & HK' & _).
  pose proof HE as (Hag & HA & Htp & HU & HB & Hnv & Htop & Hcnt & _). destruct Hag as (Hagw & Hagl & Hagm). destruct HFz as [Fw Fl].
  assert (RWid : forall i, (i < GW)%positive -> rw r i = rw (rhoM_of A rho) i).
  { intros i Hi. rewrite <- (Fw i) by (unfold GW in Hi; lia). symmetry. apply Hagw. exact Hi. }
  split.
  - split; [|split].
    + intros i Hi. rewrite rhoM_init. symmetry. exact (RWid i Hi).
    + intros l. unfold rhoM_of. rewrite rl_rho_sets. cbn [rho_after rl]. rewrite <- Fl. rewrite <- Hagl. unfold rhoM_of. rewrite rl_rho_sets. reflexivity.
    + intros a. unfold rhoM_of. rewrite rm_rho_sets. reflexivity.
  - assert (R12 : rw r 12%positive = rw rb 12%positive) by (rewrite (RWid 12%positive) by (unfold GW; lia); apply Hagw; unfold GW; lia).
    split; [|split; [exact HK'|split; [|split; [|split; [|split]]]]].
    + exact (proj1 (u_rebuild r tp tr md HJ)).
    + unfold tp_ok in *. rewrite (RWid 24%positive) by (unfold GW; lia). rewrite (Hagw 24%positive) by (unfold GW; lia). exact Htp.
    + apply (HW rb r); [|exact HU]. intros i Hi. assert (Hi' : (i < GW)%positive) by (unfold NF in Hi; unfold GW; lia).
      rewrite (RWid i Hi'). apply Hagw. exact Hi'.
    + cbn [eval]. rewrite R12. fold nv. exact HB.
    + cbn [eval]. rewrite R12. fold nv. lia.
    + unfold top_high in *. rewrite (RWid 10%positive) by (unfold GW; lia). rewrite (RWid V_DEPTH) by (unfold GW, V_DEPTH; lia).
      rewrite (Hagw 10%positive) by (unfold GW; lia). rewrite (Hagw V_DEPTH) by (unfold GW, V_DEPTH; lia). exact Htop.
Qed.

Lemma posts_init : ltac2:(tb__ "0|1|
S4aS7aS3S4S5cS73A2A1F_;F_;S65VCST;VXGL;R1A3S18S3S2fQ40A1A1S6bS7bVCST;VXGL;VA;S59VA;A1M0S1aVrho;A1S1aR3A1A6S72S32S6dS64Vrho;R4A2R3R6G0VKc;A2R2A6S72S32S6dVrho;R4R7VA;VKc;A2R3A6F_;F_;Fw;Ftp;Fr;F_;FPFam;").
Proof.
  intros PFam HPF r tp w HM0 H.
  apply (HPF A (initA A) Kc rho r tp tp w); [repeat split; reflexivity | exact HM0 | | exact H].
  intros A' HCK c' Hc' Hn Hf. exact (HCK c' Hc' Hn Hf).
Qed.
End USTEPS.
End SpineCallocU1.

(* [comment removed for export] *)
Module SpineMallocQ6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "eval"; "SAlu"; "rm"; "SLit"; "SPBranch"; "SPNot"; "sprop"; "ss_facts"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "of_nat"; "mul"; "to_nat"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "w_cfg"; "world"; "@Corelib.Init.Datatypes"; "list"; "length"; "bool"; "false"; "true"; "cons"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "ph0"; "FAb"; "frozen"; "ghosts"; "ph_fill"; "zoneR"; "gh_nf"; "phase"; "gh_new"; "ph_cnt"; "ph_pop"; "ph_ri"; "rlink"; "PCE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "class_state"; "cs_cache"; "cs_free_array"; "aa_cache_inited"; "aa_geom"; "budget_bound"; "cs_allocated_user"; "cs_mapped_free_array"; "cs_mapped_user"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "entryRq"; "cQ0"; "r0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "refill_cs"; "kchunks"; "refillA"; "take_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3"; "phK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ6"; "phFN"; "e16N"; "@Corelib.Lists.ListDef"; "nth"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "NXR"; "JRf"; "L_rf"; "JLRf"; "refill_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "vAU"; "vK"; "vMFA"; "vMU"; "vNF"; "vFA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ4"; "ph_setcnt"; "ph_setri"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SUB"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ5"; "JRfin"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ6.ARMN"; "e16N"; "e_srcN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ6.ASMN"; "exitT"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Lemma entry_fa : ltac2:(tb__ "0|3|
S3cS1S1cS39Q40M0A1A1S3aS1cS50A1S51S1S47R7R6R5R4R3R2R1A7S37G0S2R7PcA2A2S0S35R1A1S0S36RaR2A2S3dS65S18S5RaA1A2S62SbS0SbS10Z0M1R1A2S11R1S13S1dS0S3fR3A1M2A2A1A2A2S63R3S64S12S28ReRdA2S14Z4R2A2A2U4S5aS0S15R2A1S3fR4A1G1A4A3A2F_;Fidx;S0S54S0R1G2A3SbS10G1R2A2S11R2S16Z2Z1cA2A2A2F_;Fx;A2Tm0;Tcs;Tc;Tnv;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho HE nv c cs m0.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as ((_ & C1 & S1 & _) & _ & (_ & MU0 & MU1 & _) & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & _).
  destruct HE as (_ & HA & _). pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  assert (MS : forall z, ag_spacebeg (aa_geom A) <= z < ag_spacebeg (aa_geom A) + kSpaceSize + 4096 -> maskv (fs_footb (aa_geom A)) m0 z = m0 z).
  { intros z Hz. apply maskv_out. apply fs_footb_space; [exact HG | exact Hz]. }
  unfold class_repr in P4. change (nthZ (aa_cls A) c cs_empty) with cs in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C9 & _ & N7 & _).
  split.
  - intros idx Hidx j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    assert (NE : nth_error (cs_free_array cs) (Z.to_nat idx) = Some (nth (Z.to_nat idx) (cs_free_array cs) 0)) by (apply nth_error_nth'; lia).
    pose proof (C9 _ _ NE j Hj) as Hc. cbn [c_addr c_w RtCells.c_val] in Hc. rewrite Z2Nat.id in Hc by lia.
    unfold FAb. fold nv c. rewrite MS in Hc; [exact Hc|]. rewrite kSpaceSize_val. unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. clear -Hidx Hj MF0 C1. lia.
  - intros x Hx. destruct (N7 x ltac:(apply in_or_app; left; exact Hx)) as (X1 & _ & X3). unfold kCompactPtrScale in X3. rewrite Z.shiftl_mul_pow2 in X3 by lia. lia.
Qed.

Section ARMN.
Variables (A : AA) (rb : valuation) (tp0 : list word) (md0 : Model) (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S47VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.
Let k : Z := kchunks c.
Let fa : list Z := cs_free_array cs.

Hypothesis HNP : ltac2:(tb__ "0|0|
S10Vk;S13S1dS0Vfa;A2A1A2").

Lemma N_refill_cs : ltac2:(tb__ "0|0|
ScS3dS4aVc;Vcs;A2S4dS15Vk;A1Vcs;A2A3").
Proof. unfold refill_cs, needs_populate. fold k fa. replace (Z.of_nat (length fa) <? k) with false by (symmetry; apply Z.ltb_ge; exact HNP). reflexivity. Qed.

Lemma N_HCACHE : ltac2:(tb__ "0|0|
ScS1cS0A1S3eS4aVc;Vcs;A2A1S5bS0S15S17S13S1dS0Vfa;A2A1Vk;A2A1Vfa;A3A3").
Proof.
  rewrite N_refill_cs. unfold take_cs. cbn [cs_cache]. fold fa. f_equal.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as (_ & (K1 & _) & _). fold k in K1. lia.
Qed.

Lemma N_HLEN : ltac2:(tb__ "0|0|
ScS0S13S1dS0S3eS4aVc;Vcs;A2A1A2A1Vk;A3").
Proof.
  rewrite N_HCACHE, length_skipn.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as (_ & (K1 & _) & _). fold k in K1. lia.
Qed.

Lemma N_HIDS : ltac2:(tb__ "0|0|
S0S54S0R1Vfa;A3SbS10Z0R2A2S11R2S16Z2Z1cA2A2A2F_;Fx;").
Proof. exact (proj2 (entry_fa _ _ _ _ _ _ _ HE)). Qed.

Lemma N_HIDC : ltac2:(tb__ "0|0|
S0S54S0R1S3eS4aVc;Vcs;A2A1A3SbS10Z0R2A2S11R2S16Z2Z1cA2A2A2F_;Fx;").
Proof. intros x Hx. rewrite N_HCACHE in Hx. apply N_HIDS. rewrite <- (firstn_skipn (Z.to_nat (Z.of_nat (length fa) - k)) fa). apply in_or_app. right. exact Hx. Qed.

Definition e_srcN : sv := ltac2:(tb__ "0|0|
S4S72S6cS4S73S4S74S6bS68A3S6Z2A1A3A3").
Definition e16N : sv := SAlu ALU_SUB vNF vK.

Lemma N_HSRCP : ltac2:(tb__ "0|1|
S1S29Vrb;R1A2S2aVA;Vrb;R2A3ScS39Q40M0A1S3R3S7aA2S38G0S12S28VA;Vrb;A2S14Z4S17S13S1dS0Vfa;A2A1Vk;A2A2A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh. destruct HGh as (_ & Q221 & _ & _ & _ & _ & Q226 & Q227 & _). unfold gh_nf in Q221. fold nv c cs fa in Q221. fold nv c k in Q227.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _) & _ & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & _). fold k in K1. fold fa in MF0.
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384) by (unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; fold nv c; lia).
  unfold e_srcN, vFA, vNF, vK. cbn [eval]. rewrite Q221, Q226, Q227. apply bv_eq.
  rewrite add_val, sll_val, sub_val. rewrite (u64_lit (Z.of_nat (length fa))), (u64_lit k), (u64_lit (FAb A rb)) by lia.
  change (2 mod 64) with 2. rewrite (Z.mod_small (Z.of_nat (length fa) - k)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (_ * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. rewrite u64_lit by lia. lia.
Qed.

Lemma N_HRIv : ltac2:(tb__ "0|2|
S1S29Vrb;R1A2S2aVA;Vrb;R2A3S4aVc;Vcs;A2S3dSbScS39Q40M0A1M1S3R4S79A2S38G0S13S1dS0S3fR1A1A2A1A2A3SbScG1S3R4S69A2S38G0S44R1A1A2A3SbScG1S3R4S67A2S38G0S43R1A1A2A3ScG1S3R4S6aA2S38G0S45R1A1A2A3A2A2A2TcsR;F_;F_;Fr;").
Proof.
  intros r HFz HGh csR. unfold csR. rewrite N_refill_cs. unfold take_cs. cbn [cs_free_array cs_mapped_free_array cs_allocated_user cs_mapped_user]. fold fa.
  destruct HGh as (_ & Q221 & Q222 & Q223 & Q224 & _ & _ & Q227 & _). unfold gh_nf in Q221. fold nv c cs fa in Q221. fold nv c cs in Q222, Q223, Q224. fold nv c k in Q227.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as (_ & (K1 & _) & _ & (_ & MF0) & _). fold k in K1. fold fa in MF0.
  split; [|split; [exact Q222 | split; [exact Q223 | exact Q224]]].
  unfold e16N, vNF, vK. cbn [eval]. rewrite Q221, Q227. apply bv_eq. rewrite sub_val. rewrite (u64_lit (Z.of_nat (length fa))), (u64_lit k) by lia.
  rewrite firstn_length_le by lia. rewrite Z.mod_small by lia. rewrite u64_lit by lia. lia.
Qed.

Lemma N_HSRC : ltac2:(tb__ "0|1|
S0S62SbS10Z0M0R2A2S10R2Vk;A2A2S33VA;Vrb;S57S27R3A2S65S18S5Vrb;A1A2R2A5S0SbS10G0R1A2S11R1S13S1dS0Vfa;A2A1A2A2S63R5S64S12S28VA;Vrb;A2S14Z4R2A2A2U4S5aS0S15R2A1Vfa;G0A4A3A2F_;Fidx;F_;F_;Fm;Fi;").
Proof.
  intros i m Hi (L1 & _) idx Hidx.
  eapply cell_ok_agree_range; [|exact (proj1 (entry_fa _ _ _ _ _ _ _ HE) idx Hidx)]. cbn [c_addr c_w]. intros z Hz. apply L1.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _) & _ & (_ & MF0) & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & _ & PS1) & _). fold k in K1. fold fa in MF0.
  change (Z.of_nat 4) with 4 in Hz. unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. fold nv c in Hz.
  unfold zoneR, phK, ph0, revealedp, releasedp. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb]. unfold PCE. fold nv c.
  intros [[X _]|[[X _]|[[X _]|[[X _]|[[_ X]|[X|[[X _]|[X _]]]]]]]]; try discriminate X; lia.
Qed.
End ARMN.

Definition phFN (k : Z) : phase := ltac2:(tb__ "0|0|
S70S6fS57S27Vk;A2A1A1").
Lemma zone_FN : ltac2:(tb__ "0|4|
S3cS1S0S0SfS2cR4R3S58R2A1R1A4SdSbS10S12S34R4R3A2M0Z10A2M1R1A2S11R1S12G1S14Z4M2R2A2A2A2A2SdSbS10G0R1A2S11R1S12G0G2A2A2A2SbS10S77S46S41R4A1A1S35S37Q40S2R3PcA2A2A1A2M3R1A2S11R1S12G3Z80A2A2A2A2A2A2Fz;Fk;Frb;FA;").
Proof.
  intros A rb k z. unfold zoneR, phFN, ph_setri, ph_setcnt, phK, ph0, revealedp, releasedp. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb]. split.
  - intros [[X _]|[[X _]|[[X _]|[[X _]|[[_ X]|[X|[[_ X]|[_ X]]]]]]]]; try discriminate X; try (exfalso; lia).
    + left; exact X.
    + right; left; exact X.
    + right; right; exact X.
  - intros [X|[X|X]].
    + right; right; right; right; right; left; exact X.
    + right; right; right; right; right; right; left; split; [reflexivity | exact X].
    + right; right; right; right; right; right; right; split; [reflexivity | exact X].
Qed.
Lemma zone_FN_dec : ltac2:(tb__ "0|1|
S3cS1S0S0SdS2cR4R3S58R2A1R1A4M0SeG0A1A2Fz;Fk;Frb;FA;").
Proof.
  intros A rb k z. pose proof (zone_FN A rb k z) as ZI.
  set (P := PCE A rb) in *. set (ri := region_info (ag_spacebeg (aa_geom A)) (cls_of (bv_unsigned (rw rb 12%positive)))) in *.
  assert (D : (P + 16 <= z < P + 16 + 4 * k \/ P <= z < P + 4 \/ ri <= z < ri + 128) \/ ~ (P + 16 <= z < P + 16 + 4 * k \/ P <= z < P + 4 \/ ri <= z < ri + 128)) by (clear; lia).
  destruct D as [D|D]; [left; apply ZI; exact D | right; intros HZ; apply D; apply ZI; exact HZ].
Qed.
Lemma zone_FN_in : ltac2:(tb__ "0|0|
S3cS1S0S37Q40S2R2PcA2A2S0S35R1A1S0S2cR5R4S58S4bR1A1A1R3A4S60S41R6A1S20R2S36R6R3A2R4A5F_;Tc;Tnv;Fz;Frb;FA;").
Proof.
  intros A rb z nv c HZ. apply zone_FN in HZ. unfold refill_zone. cbn zeta. unfold PCE in HZ. fold nv c in HZ.
  destruct HZ as [X|[X|X]]; [right; left; exact X | left; exact X | right; right; left; exact X].
Qed.

Section ASMN.
Variables (W : list ulink) (st : ustop).
Variables (E3 LP LJ XL X4 : axst).
Hypothesis FJ : ltac2:(tb__ "0|0|
S54S9S8S7S75S6bS68A3A1SaS56VLJ;A1A1A3").

Definition prefixT : Prop := ltac2:(tb__ "0|2|
S3cS4eS1S1cS39Q40A1A1M0S3aS19S19OF_;F_;S61R5R1A2S4fR6A1S1S1G0S19S47RcRaR9R8VW;Vst;R4A7S1R9S25S18S26ReRdRcRbRaS27A6VLP;R1R4A5R3A2Fr';S1RaS25S18S26RfReRdRcRbS27A6M1VLJ;R1R5A5R4A2Fr';RaS25S18G1S48VE3;A1R6R5A5R4A2F_;F_;F_;FQ;Ftp;Fr;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition popT (e_src : sv) : Prop := ltac2:(tb__ "0|9|
S3cS4eS1S1cS39Q40M0A1M1A1M2S3aS19S19OF_;F_;S61R5R1A2S4fR6A1S1S47R9R7R6R5VW;Vst;R1A7S2eSbScS0S31R1A1Z0M3A3SbScS1eS30R1A1S1fA3ScS1eS32R1A1S1fA3A2A2S1cS0A1M4S37G0S2RbPcA2A2S0S35R1A1S0S4bR1A1S0S13S1dS0R4A2A1S0S0S62SbS10G3R2A2M5S10R2R4A2A2S33R14R12S57RaR3A2S65S18S5R12A1A2R2A5S0SbS10G3R1A2S11R1R6A2A2S63R5S64S12S28R17R15A2S14Z4M6R2A2A2U4S5aS0S15R2A1RbG3A4A3A2F_;Fidx;F_;F_;Fm;Fi;S10R3R2A2S10S14G6R3A2Z20000000A2S11G3S2bRaA1A2SbS10G3S2dR15R13A2M7A2SbScS0S12G7S2fR15R13A2M8A2R5A3S10S2bRbA1G8A2A2A2F_;S0S54S0R1RaA3SbG5S11R2S16Z2Z1cA2A2A2F_;Fx;ScG4S3eS4aR8S36R16R9A2A2A1S5bS0S15S17R6R7A2A1RaA3A3S1S29R16R1A2S2aR19R17R2A3ScG1S3R3Ve_src;A2S38G0S12S28R1aR18A2S14G6S17RaRbA2A2A2A2A3F_;F_;Fr;S1G2S19S1R17S25S18S26R1cR1bR1aR19R18S57R12RdA2A6VXL;R1R3A5R2A2Fr';R17S25S18S26R1cR1bR1aR19R18R12A6VLJ;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;F_;F_;F_;F_;F_;TnfP;Tk;Tc;Tnv;FfaP;FPH0;Fph;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition entryT : Prop := ltac2:(tb__ "0|2|
S3cS4eS0S0S1S1cS39Q40M0A1A1S1bS10S42R7A1S66A2ScS1eS40R8A1S20A3S25S18S5dR9R8R7R6A4VE3;R5R4R3A6SbScS0R8S35S37G0S2R6PcA2A2A1A3SbS47RaR6R5S71S1aR4A1A1M1VW;Vst;R6A7S25S18S26RaR9R6R5G1S27A6S48VE3;A1S49RaR6A2R5R4A6A2A2F_;F_;F_;Fw;Ftp;FrhoE;Fnv0;Fc0;FKc;FA;").
Definition exitT (e16 e24 e32 e48 : sv) : Prop := ltac2:(tb__ "0|6|
S3cS4eS1S1cS39Q40M0A1M1A1M2S3aS19S19OF_;F_;S61R5R1A2S4fR6A1S1S47R9R7R6R5VW;Vst;R1A7S2eS37G0S2R9PcA2A2S0S35R1A1S0S4bR1A1S0SbScS0S31R4A1R1A3SbScS1eS30R4A1S1fA3ScS1eS32R4A1S1fA3A2A2S11Z0M3S2bR5A1A2SbS10G3S2dR10ReA2M4A2SbS10S14Z4S12G4S2fR10ReA2M5A2A2Z20000000A2S10S2bR6A1G5A2A2A2F_;ScS1eS40R10A1S20A3S1S29R10R1A2S2aR13R11R2A3S4aR8S36R14R9A2A2S3dSbScG1S3R4Ve16;A2S38G0S13S1dS0S3fR1A1A2A1A2A3SbScG1S3R4Ve24;A2S38G0S44R1A1A2A3SbScG1S3R4Ve32;A2S38G0S43R1A1A2A3ScG1S3R4Ve48;A2S38G0S45R1A1A2A3A2A2A2TcsR;F_;F_;Fr;S1G2S19S1R11S25S18S26R16R15R14R13R12S70S6fRcA1A1A6VX4;R1R3A5R2A2Fr';R11S25S18S26R16R15R14R13R12RcA6VXL;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;F_;F_;Tk;Tc;Tnv;FphX;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition finT : Prop := ltac2:(tb__ "0|5|
S3cS4eS1S1cS39Q40M0A1A1M1S3aS19S19OF_;F_;S6dR5R1A2S4fR6A1S1S47R9R7R6R5VW;Vst;R1A7S2eS1G1S52S1G1S1cS3bA1M2S3aS26R12R11R10RfReR8R4R3R2R1AaS6eS4cR13S35S37G0S2R11PcA2A2A1A2R5R4R2A4F_;Fmd;Ftr;Ftp;Fr;S0SdS2cR10ReR6R1A4M3SeG3A1A2Fz;S1G1G2S3aS78R14R13R12RaR4R3R2R1A8SbS76S5cRaR5A3R8RaR9R5R4R3R2A6A2F_;Fmd;Ftr;Ftp';Fr';S1G1ReS25S18S26R13R12R11R10RfR9A6VX4;R2R1A5S53S18S5cR8R7S21S24S55S52A2M4S23S55S52S5eR6A4S22G4A1A3A5A2Ftp;Fr;F_;F_;F_;FJLq;FtpQ;FrhoQ;FphF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").

Hypothesis H_entry : entryT.
Hypothesis H_prefix : prefixT.
Hypothesis H_pop : popT e_srcN.
Hypothesis H_exit : ltac2:(tb__ "0|0|
S7bS59S69S67S6aA4").
Hypothesis H_fin : finT.

Theorem refill_N : ltac2:(tb__ "0|4|
S3cS4eS0S0S1S1cS39Q40M0A1A1M1S19S19OF_;F_;S6dR6R1A2S4fR7A1S10S42R9A1S66A2ScS1eS40RaA1S20A3S53S18S5cR7R6S21S24S55S52A2M2S23S55S52S5eS5fRbRaR9A3A4S22G2A1A3A5S19S3aS47RdR9R8R1VW;Vst;R9A7S10S4bS35S37G0S2RaPcM3A2A2A1A1S2dReRaA2A2S1G1S1cS3bA1S3aS26R13R12RfReR7S58S4bS35S37G0S2RfG3A2A2A1A1A1R4R3R2R1AaS6eS4cR14S35S37G0S2R10G3A2A2A1A2R5R4R2A4F_;Fmd;Ftr;Ftp';Fr;F_;FHE;Fmd0;S3aS1ScS0RdS35S37G0S2RbG3A2A2A1A3S47R10RcRbR3VW;Vst;RcA7RbS25S18S26R11R10RdRcR4S27A6VLP;R3RcA5R6A2F_;F_;Fr';Fmd0;R8S25S18S5dReRdRcRbA4VE3;RaR9A5R3A2F_;F_;TQ;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;Fnv0;Fc0;FKc;FA;").
Proof.
  intros A Kc c0 nv0 rho tp TR KIT HKc HBUD Hini Q HREB HPOPUL.
  pose proof (trd_ok Kc TR KIT) as KT.
  apply (tr_cutP Kc TR KT Model _ (fun md0 => c0 = cls_of (bv_unsigned (rw rho 12%positive)) /\ entryRq A rho tp md0 W st rho)
           (fun md0 => SPA segs (JR A Kc rho tp md0 ph0) (cQ0 E3) (r0_of A rho) tp) Q).
  { intros w Hw. exists (cfg_model (w_cfg w)). destruct (H_entry A Kc c0 nv0 rho tp w HBUD Hini Hw) as (E0 & HE & HS). exact (conj (conj E0 HE) HS). }
  intros md0 [E0 HE].
  apply (H_prefix A Kc rho tp md0 TR KT HKc rho _ tp Q HE); [intros r'; exact (HPOPUL md0 r' E0 HE)|].
  intros r1.

  apply (tr_facts Kc TR KT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ FJ) as BF. cbn [holds] in BF.
  apply (tr_pure Kc TR KT (kchunks (cls_of (bv_unsigned (rw rho 12%positive))) <= gh_nf A rho)).
  { intros w [_ (HFz & HGh & _)]. destruct HGh as (_ & Q221 & _ & _ & _ & _ & _ & Q227 & _).
    pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. destruct CF as (_ & (K1 & _) & _ & (_ & MF0) & _).
    unfold branch_taken, bv_ltu, vNF, vK in BF. cbn [eval] in BF. rewrite Q221, Q227 in BF. unfold gh_nf in *.
    rewrite !u64_lit in BF by lia. destruct (Z.ltb_spec (Z.of_nat (length (cs_free_array (cst_of A (bv_unsigned (rw rho 12%positive)))))) (kchunks (cls_of (bv_unsigned (rw rho 12%positive))))) as [X|X]; [exfalso; apply BF; reflexivity | exact X]. }
  intros HNP. pose proof HNP as HNP'. unfold gh_nf in HNP.
  set (nv := bv_unsigned (rw rho 12%positive)) in *. set (c := cls_of nv) in *. set (k := kchunks c) in *.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as (_ & _ & _ & (_ & MF0) & _).
  apply (H_pop A Kc rho tp md0 TR KT HKc rho HE ph0 (conj eq_refl (conj eq_refl eq_refl)) (cs_free_array (cst_of A nv))
           (N_HSRC A rho tp md0 W st rho HE) HNP ltac:(lia) ltac:(cbn; intros X; exfalso; lia)
           (N_HIDS A rho tp md0 W st rho HE) (N_HCACHE A rho tp md0 W st rho HE HNP) (N_HSRCP A rho tp md0 W st rho HE HNP)).
  intros r2.
  apply (H_exit A Kc rho tp md0 TR KT HKc rho HE (phK ph0 k) (conj eq_refl (conj eq_refl eq_refl)) ltac:(cbn; intros X; exfalso; lia) Hini
           (N_HRIv A rho tp md0 W st rho HE HNP)).
  intros r3.
  apply (H_fin A Kc rho tp md0 TR KIT HKc rho HE (phFN k) rho tp (JLRf A Kc c0) (HREB md0 HE HNP') (zone_FN_dec A rho k)).
  exact (fin_post A Kc rho tp (phFN k) c0 E0 Hini (zone_FN_in A rho)).
Qed.
End ASMN.
End SpineMallocQ6.

(* [comment removed for export] *)
Module SpineCallocR15.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "sv"; "eval"; "sprop"; "SAlu"; "SLit"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "JR"; "phase"; "entryR"; "gh_new"; "ph0"; "frozen"; "ghosts"; "mlink"; "FAb"; "committed"; "ph_f"; "ph_u"; "releasedp"; "rlink"; "@Corelib.Init.Datatypes"; "list"; "bool"; "length"; "true"; "prod"; "nil"; "option"; "pair"; "None"; "Some"; "cons"; "nat"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "of_nat"; "le"; "lt"; "ge"; "ltb"; "modulo"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "cs_free_array"; "cs_mapped_free_array"; "class_state"; "aa_cache_inited"; "aa_geom"; "ag_spacebeg"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7"; "popfacts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cst_of"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP"; "ph_quiet"; "pbase"; "ph_set"; "PF"; "PU"; "ph_get"; "pord"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR13"; "phL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocR14"; "e16P"; "e32P"; "e48P"; "e_srcP"; "e24M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR6"; "backT"; "exitT"; "popT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "vMFA"; "beg1"; "beg2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15.ASMP"; "pieceT"; "fillT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15"; "phFin"; "phUF3"; "phU3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR12"; "rup_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3"; "phK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4"; "ph_setcnt"; "ph_setri"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv InvLaws PrimCredit GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RefillModelP RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocR14.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Section FAMAP.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
SfVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Notation JRp := (JR A Kc rb tp0 md0).
Let cs : class_state := ltac2:(tb__ "0|0|
S45VA;S3eQ40S1Vrb;PcA2A2A2").
Variable LFm : axst.
Let CFM : axst := cFm LFm.
Hypothesis W_fm : ltac2:(tb__ "0|0|
S27S1cS8S48VCFM;A1A1S1eA3").
Hypothesis D_fm : ltac2:(tb__ "0|4|
S27S21S1fS1bS1fS3S3A2M0A1M1S1bS5A1M2A2M3A1S69S48VLFm;A1S48VCFM;A1A2S24G3S22G1G2S25G0S22S3S3S6dS6S68S5cS7Z40000A1A3A4S20G0A1A3S20S5A1A4A2A3").

Lemma famap_restate : ltac2:(tb__ "0|0|
SeS0S1bS3dQ40A1A1SaS30S38Vcs;A1S2dZ4S2cS2eS1dSbS37Vcs;A1A2A1S10VA;Vrb;A2A2A2A2VTR;ScS9SdVA;VKc;Vrb;Vtp0;Vmd0;R5A6VCFM;R4R3A5R2A2VTR;ScS9SdVA;VKc;Vrb;Vtp0;Vmd0;R6A6VLFm;R5R4A5R3A2F_;F_;FQ;Ftp;Fr;Fph;").
Proof.
  intros ph r tp Q HLT HT. pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_restate A Kc rb tp0 md0 TR KIT LFm (ax_S CFM) _ _ ph r tp Q W_fm D_fm ltac:(apply Pos.eqb_refl)); [|exact HT].
  intros tr md (HFz & HGh & _) _. split; [|constructor]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  exact (rup_val A rb r CF PF HGh HLT).
Qed.
End FAMAP.

Definition phU3 : phase := ph_set PU 3 ph0.
Definition phUF3 : phase := ph_set PF 3 phU3.
Definition phFin (ph : phase) (new k : Z) : phase := ltac2:(tb__ "0|0|
S70S6fS6eS53Vph;Vnew;A2Vk;A2A1A1").

Section ASMP.
Variables CST XGL : list (Z * Z).
Variable PFam : ltac2:(tb__ "0|0|
S36S40S1bS1fS47S4bA2A1F_;F_;").
Variables (W : list ulink) (st : ustop).

Variables (LP CP2C RU LF0 LFm CFM RF LF1 : axst) (LJP XLP LZP LJM XLM LZM E3P : axst).
Notation AInvS := (AInvA segs).
Hypothesis HWs : stopJ_w W st.

Definition headT : Prop := ltac2:(tb__ "0|1|
S36S40S0S1bS3dQ40A1A1M0S34SaSaOF_;F_;S43R5R1A2S41R6A1S0S0G0SaSfRcRaR9R8VW;Vst;R4A7S44RdRbA2S0RaScS9SdRfReRdRcRbS11A6VCP2C;R1R5A5R4A2Fr';F_;R9ScS9SdReRdRcRbRaS11A6VLP;R5R4A5R3A2F_;F_;FQ;Ftp;Fr;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition pieceT (p : piece) (eb : sv) (C0 RX : axst) : Prop := ltac2:(tb__ "0|6|
S36S40S0S1bS3dQ40M0A1A1M1S34SaSaOF_;F_;S43R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7SeS27S26S51Vp;R1A2U0A3S52Vp;R2A2S4cR3A1S0S12RdR1A2S13R10ReR2A3S27SbS3eG0S4R3Veb;A2A2S4dR11RfVp;A3A3F_;F_;Fr;S28S2fS2cS3cS3bRfA1A1M2Z100000000A2S4dRfRdVp;A3M3A2S28S2fS2cG3Z40000M4A2S2cG2Z2000000000A2A2S27SbS33G3Z10000A2Z0A3A2A2G1S34S14R12R10RfReR8R2R1A7S31S6aR2R3A2M5G4A2F_;Fmd;Ftp;G1S34S14R13R11R10RfS4eVp;U1R9A3R2R1A7S31G5Z8000A2F_;Fmd;Ftp;S0G1SaS0G1R12ScS9SdR17R16R15R14R13S4eVp;U3RdA3A6VRX;R2R1A5R3A2Ftp';Fr';R11ScS9SdR16R15R14R13R12RcA6VC0;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;F_;F_;F_;F_;F_;Fph;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition midT : Prop := ltac2:(tb__ "0|4|
S36S40S0S1bS3dQ40M0A1A1M1S34SaSaOF_;F_;S43R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7S44RaR8A2SeS0G1SaS45RfS3eG0S1RdPcA2A2A2S39S29S30S38R1A1S2dZ4M2S2cS2eS1dSbS37R1A1A2A1S10R10ReA2A2A2A2A1S0RdScS9SdR12R11R10RfReR7A6M3VLF0;R1R5A5R4A2Fr';F_;S30S38R2A1S2dG2S2cS2eS1dSbS37R2A1A2A1S10R11RfA2A2A2A2S0ReScS9SdR13R12R11R10RfR8A6VLFm;R1R6A5R5A2Fr';F_;RdScS9G3VRU;R6R5A5R4A2F_;F_;Tcs;FQ;Ftp;Fr;Fph;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition fmT : Prop := ltac2:(tb__ "0|2|
S36S40S0S1bS3dQ40M0A1A1M1S34SaSaOF_;F_;S43R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7S44RaR8A2SeS0G1SaS45RfS3eG0S1RdPcA2A2A2S39S30S38R1A1S2dZ4S2cS2eS1dSbS37R1A1A2A1S10R10ReA2A2A2A2RcScS9SdR11R10RfReRdR6A6VCFM;R5R4A5R3A2RdScS9SdR12R11R10RfReR7A6VLFm;R6R5A5R4A2F_;F_;Tcs;FQ;Ftp;Fr;Fph;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition runT (C L : axst) : Prop := ltac2:(tb__ "0|2|
S36S40S0S1bS3dQ40A1A1M0S34SaSaOF_;F_;S43R5R1A2S41R6A1SeS0G0SaS0R8ScS9SdRdRcRbRaR9R5A6M1VL;R1R3A5R2A2Fr';R8ScS9G1VC;R4R3A5R2A2F_;FQ;Ftp;Fr;Fph;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition fillT (LH LJ : axst) : Prop := ltac2:(tb__ "0|7|
S36S40S0S1bS3dQ40M0A1A1M1S34SaSaOF_;F_;S43R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7S44RaR8A2SeS4cR1A1SbS6bS28S2fZ0R2A2S2fR2S10RfRdA2A2A2S1aR10ReS53R5R3A2S6cS9S2ReA1A2R2A5SbS28S2fS2cS15R12R10A2M2S2dZ4M3S2eS1dSbS37S45R12S3eG0S1R10PcA2A2A2A1A2A1M4A2A2R1A2S30R1S2cG2S2dG3S2cG4S10R12R10A2M5A2A2A2A2A2S29S27S21S3dQ8A1M6A1R5R2A1S23G6A1A3A1F_;Fz;F_;F_;Fm;Fi;S0G1SaS0RdScS9SdR12R11R10RfReS53R7G5A2A6VLJ;R1R3A5R2A2Fr';RdScS9SdR12R11R10RfReR7A6VLH;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;Fph;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").

Hypothesis H_head : headT.
Hypothesis H_pu : ltac2:(tb__ "0|0|
S62S50S5dVCP2C;VRU;A4").
Hypothesis H_mid : midT.
Hypothesis H_fm : fmT.
Hypothesis H_pf : ltac2:(tb__ "0|0|
S62S4fS5eVCFM;VRF;A4").
Hypothesis H_run : runT RF LF1.
Hypothesis H_fillP : fillT LF0 LJP.
Hypothesis H_fillM : fillT LF1 LJM.
Hypothesis H_popP : ltac2:(tb__ "0|0|
S5bVW;Vst;VLJP;VXLP;S57A5").
Hypothesis H_popM : ltac2:(tb__ "0|0|
S5bVW;Vst;VLJM;VXLM;S57A5").
Hypothesis H_exitP : ltac2:(tb__ "0|0|
S5aVW;Vst;VXLP;VLZP;S54S5cS55S56A8").
Hypothesis H_exitM : ltac2:(tb__ "0|0|
S5aVW;Vst;VXLM;VLZM;S54S58S55S56A8").
Hypothesis H_backP : ltac2:(tb__ "0|0|
S59VCST;VXGL;VPFam;VW;Vst;VE3P;VLZP;A7").
Hypothesis H_backM : ltac2:(tb__ "0|0|
S59VCST;VXGL;VPFam;VW;Vst;VE3P;VLZM;A7").

Lemma pop_tail : ltac2:(tb__ "0|5|
S47S47S47S47S3S63R5R4A2S5bVW;Vst;R5R4S57A5S5aVW;Vst;R5R4S54R3S55S56A8S59VCST;VXGL;VPFam;VW;Vst;VE3P;R5A7S36S40S0S1bS3dQ40M0A1M1A1M2S34SaSaOF_;F_;S43R5R1A2S41R6A1S0SfR9R7R6R5VW;Vst;R1A7S44RaR8A2SeS27S1cS3aRcA1S1eA3S4cR2A1S27S1cS16S18R3A1A1S1eA3S3eG0S1RdPcA2A2SbS46R1A1SbS45R11R2A2S39S2eS1dSbS37R1A1A2A1SbS10R13R11A2SbS38R3A1SbS2aS27S1cS19S17RaA1A1S1eA3S2fS2dZ4M3S2cR3R2A2A2R1A2A2S0S12R15R1A2S13R18R16R2A3S27G1S4R3R1eA2S3fG0S1cSbL_;S32R5S2dG3S2cR7R6A2A2A2S2cR5Z40000A2R5X1cx2A2A3F_;F_;Fr;S0G2S1bS35A1S34SdR1bR1aR19R18R17S64R10R8S60RbA1A3R4R3R2R1AaS28S5fS9S61R1cRcA2M4R5R4R2A5S42VCST;VXGL;R1cG4S2R1aA1S2R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;S36S0G2S0R17ScS9S67VW;Vst;R4R1bR3A5VE3P;R1R2A5S4aS9S49R3R2VPFam;R4R1bA2A5A2FrX;Ftp';Frho';FA';S0G2R16ScS9SdR1bR1aR19R18R17R10A6R24R2R1A5S4aS9S49R13R18VPFam;R1bR1aA2A5A2Ftp;Fr;F_;F_;F_;F_;Tmfa;Tnew;Tnf;Tcs;Tc;Tnv;F_;F_;F_;FphX;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;F_;F_;F_;F_;Fe24;FLZ;FXL;FLJ;FLH;").
Proof.
  intros LH LJ XL LZ e24 HFI HPO HEX HBA A Kc rb tp0 md0 TR KIT HKc rho HE PF phX Hini PQ PCU nv c cs nf new mfa HARM HE24 HREB HPOP r tp.
  pose proof (P_csR A rb tp0 md0 W st rho HE PF) as (X1 & X2 & X3 & X5 & X6 & X7 & LP' & HIDS). cbn zeta in X1, X2, X3, X5, X6, X7, LP', HIDS. fold nv c cs nf new in X1, X2, X3, X5, X6, X7, LP', HIDS.
  destruct (pop_geo A rb tp0 md0 W st rho HE PF) as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & _). fold nv c cs nf new mfa in C1, S1, AU0, MU1, N4, K1, KN, NF0, MF1, MF2, MF0.
  set (k := kchunks c) in *. set (fP := faP c cs) in *.

  apply (HFI A Kc rb tp0 md0 TR KIT HKc rho HE PF phX PQ).
  { intros i m Hi HR z Hz. apply (P_HDEF A rb tp0 md0 W st rho HE PF (phL phX i) m); [exact HARM | exact HR | exact Hz]. }
  intros r1.

  apply (HPO A Kc rb tp0 md0 TR KIT HKc rho HE (phL phX new) (conj eq_refl (conj eq_refl eq_refl)) fP).
  - intros i m Hi HR idx Hidx. apply (P_HSRC A rb tp0 md0 W st rho HE PF (phK (phL phX new) i) m); [reflexivity | cbn [ph_pop phK]; fold nv c k in Hi; clear -Hi K1; lia | exact HR | exact Hidx].
  - fold nv c k. rewrite LP'. clear -KN NF0. lia.
  - rewrite LP'. clear -MF1 MF2 N4. lia.
  - intros _. unfold gh_nf. fold nv c cs nf new. rewrite LP'. cbn [ph_fill phL]. clear -NF0 N4. lia.
  - exact HIDS.
  - fold nv c cs k. rewrite LP'. exact X1.
  - fold nv c k. exact (P_HSRCP A rb tp0 md0 W st rho HE PF).
  - intros r2.

    apply (HEX A Kc rb tp0 md0 TR KIT HKc rho HE (phK (phL phX new) k) (conj eq_refl (conj eq_refl eq_refl))).
    + intros _. unfold gh_nf. fold nv c cs nf new. cbn [ph_fill phK phL]. clear -NF0 N4 MF1 MF2. lia.
    + exact Hini.
    + intros r' HFz HGh. exact (P_HRIv A rb tp0 md0 W st rho HE PF e24 r' HFz HGh (HE24 r' HFz HGh)).
    + fold nv c cs k. exact X2.
    + fold nv c cs. intros x Hx. rewrite X1 in Hx. apply HIDS. rewrite <- (firstn_skipn (Z.to_nat (nf + new - k)) fP). apply in_or_app. right. exact Hx.
    + intros r3.

      apply (HBA A Kc rb tp0 md0 TR KIT rho HE (phFin phX new k)).
      * intros r' t tr md HJ. exact (proj1 (HREB r' t tr md HJ)).
      * intros r' t tr md HJ. exact (proj2 (HREB r' t tr md HJ)).
      * fold nv c cs k. exact X2.
      * exact (HPOP (refillA A c)).
Qed.

Theorem refill_populate : ltac2:(tb__ "0|3|
S36S40S0S1bS3dQ40M0A1A1M1SaSaOF_;F_;S43R4R1A2S41R5A1S27S1cS3aR7A1S1eA3S4aS9S49R6R5VPFam;R8R7A2A5SaS0S34SfRbR2R8R1VW;Vst;R9A7S44RcR3A2SeS2aS27SeR1S66A3S27SeR1S65A3A2S3eG0S1R6PcA2A2SbS46R1A1SbS45R11R2A2S39S2bS27SeR5S65A3S30S38R1A1S2dZ4S2cS2eS1dSbS37R1A1A2A1S10R12R9A2A2A2A2A2S0G1S1bS35A1S34SdR17R16ReR14RdS64RaS10R17ReA2S60R7A1A3R4R3R2R1AaS28S5fS9S61R18R8A2M2R5R4R2A5S42VCST;VXGL;R18G2S2RfA1S2R5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;Frb;S36S0G1S0RaScS9S67VW;Vst;R4RdR3A5VE3P;R1R2A5S4aS9S49R3R2VPFam;R4RdA2A5A2FrX;Ftp';Frho';FA';S0S34S0SfReR3RbR2VW;Vst;RcA7RbScS9SdRfReR4RcR3S11A6VLP;R2RcA5R7A2F_;Fr';Fmd0;Frb;F_;F_;TQ;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp TR KIT HKc Hini Q HREB HPOP rb md0 r0 HE.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (H_head A Kc rb tp md0 TR KIT HKc rho r0 tp Q HE). intros PF r1.
  set (nv := bv_unsigned (rw rb 12%positive)) in *. set (c := cls_of nv) in *. set (cs := cst_of A nv) in *.
  destruct (pop_geo A rb tp md0 W st rho HE PF) as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & _).
  fold nv c cs in C1, S1, AU0, MU1, N4, K1, KN, NF0, MF1, MF2, MF0, FAr.
  destruct (pop_credit A rb tp md0 W st rho HE PF) as (CR & _). fold nv c cs in CR.
  assert (G12 : ag_spacebeg (aa_geom A) mod 65536 = 0) by (unfold cfacts in CF; cbn zeta in CF; destruct CF as (_ & _ & _ & _ & _ & (X & _) & _); exact X).
  assert (MU18 : cs_mapped_user cs mod 262144 = 0) by (unfold cfacts in CF; cbn zeta in CF; fold nv c cs in CF; destruct CF as (_ & _ & (X & _) & _); exact X).

  apply (H_pu A Kc rb tp md0 TR KIT HKc rho HE ph0 eq_refl eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
  - intros r HFz HGh. exact (beg1_val A rb r CF (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh).
  - cbn [pbase]. unfold U0, region_beg, kRegionSize. fold nv c cs. split; [clear -C1 AU0; lia|]. split; [clear -C1 MU1; lia|].
    rewrite Z.add_mod, (Z.add_mod (ag_spacebeg (aa_geom A))), G12 by (clear; lia).
    destruct (proj1 (Z.mod_divide (cs_mapped_user cs) 262144 ltac:(clear; lia)) MU18) as [q Hq]. rewrite Hq.
    replace (c * 2 ^ 32) with (c * 65536 * 65536) by (clear; lia). replace (q * 262144) with (q * 4 * 65536) by (clear; lia). rewrite !Z_mod_mult. reflexivity.
  - intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF ph0 t md HM) as X. cbn [ph0 ph_u ph_f committed revealedp Nat.leb] in X.
    destruct (cs_mapped_free_array cs <? _); clear -X CR; lia.
  - intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF (ph_set PU 1 ph0) t md HM) as X. cbn [ph_set ph0 ph_u ph_f committed revealedp Nat.leb] in X.
    destruct (cs_mapped_free_array cs <? _); clear -X CR; lia.
  - intros r2 tp2. fold phU3.
    apply (H_mid A Kc rb tp md0 TR KIT HKc rho HE PF phU3 r2 tp2 Q); cbn zeta; fold nv c cs.
    +
      intros NLT r3.
      apply (pop_tail LF0 LJP XLP LZP vMFA H_fillP H_popP H_exitP H_backP A Kc rb tp md0 TR KIT HKc rho HE PF phU3 Hini (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))) eq_refl).
      * right. fold nv c cs. clear -NLT. lia.
      * intros r HFz HGh. fold nv c cs. replace (cs_mapped_free_array cs <? _) with false by (symmetry; apply Z.ltb_ge; clear -NLT; lia).
        destruct HGh as (_ & _ & Q222 & _). fold nv c cs in Q222. exact Q222.
      * fold nv c. apply (HREB rb md0 HE PF phU3 (or_introl eq_refl)). cbn zeta. fold nv c cs. split; [intros X; discriminate X | intros X; contradiction].
      * exact HPOP.
    +
      intros LT r3.
      apply (H_fm A Kc rb tp md0 TR KIT HKc rho HE PF phU3 r3 tp2 Q LT).
      pose proof (P_newZ A rb) as ENZ. fold nv c cs in ENZ.
      destruct (RefillModelP.P_famap c cs _ C1 (proj1 (entry_pure A rb tp md0 W st rho HE PF)) (proj2 (proj2 (proj2 (entry_pure A rb tp md0 W st rho HE PF))))
                  ltac:(rewrite ENZ; exact LT)) as (_ & FCM).
      pose proof (facap_room c C1) as FRM.
      apply (H_pf A Kc rb tp md0 TR KIT HKc rho HE phU3 eq_refl I (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
      * intros r HFz HGh. exact (beg2_val A rb r CF (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh).
      * cbn [pbase]. unfold F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c cs.
        split; [clear -C1 NF0 MF1; lia|]. split; [clear -C1 FCM FRM; lia|].
        rewrite Z.add_mod, (Z.add_mod (ag_spacebeg (aa_geom A) + c * 2 ^ 32)), (Z.add_mod (ag_spacebeg (aa_geom A))), G12 by (clear; lia).
        destruct (proj1 (Z.mod_divide (cs_mapped_free_array cs) 262144 ltac:(clear; lia)) MF0) as [q Hq]. rewrite Hq.
        replace (c * 2 ^ 32) with (c * 65536 * 65536) by (clear; lia). replace (q * 262144) with (q * 4 * 65536) by (clear; lia). rewrite !Z_mod_mult. reflexivity.
      * intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF phU3 t md HM) as X. cbn [phU3 ph_set ph0 ph_u ph_f committed revealedp Nat.leb] in X.
        fold nv c cs in CR. replace (cs_mapped_free_array cs <? _) with true in CR by (symmetry; apply Z.ltb_lt; exact LT). clear -X CR. lia.
      * intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF (ph_set OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP.PF 1 phU3) t md HM) as X. cbn [phU3 ph_set ph0 ph_u ph_f committed revealedp Nat.leb] in X.
        fold nv c cs in CR. replace (cs_mapped_free_array cs <? _) with true in CR by (symmetry; apply Z.ltb_lt; exact LT). clear -X CR. lia.
      * intros r4 tp4. fold phUF3.
        apply (H_run A Kc rb tp md0 TR KIT HKc phUF3 r4 tp4 Q). intros r5.
        apply (pop_tail LF1 LJM XLM LZM e24M H_fillM H_popM H_exitM H_backM A Kc rb tp md0 TR KIT HKc rho HE PF phUF3 Hini (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))) eq_refl).
        -- left. reflexivity.
        -- intros r HFz HGh. fold nv c cs. replace (cs_mapped_free_array cs <? _) with true by (symmetry; apply Z.ltb_lt; exact LT).
           destruct HGh as (_ & _ & Q222 & _). fold nv c cs in Q222. unfold e24M, vMFA. cbn [eval]. rewrite Q222. apply bv_eq.
           rewrite add_val, !u64_lit by (clear -NF0 MF1 MF2; lia). rewrite Z.mod_small by (clear -NF0 MF1 MF2; lia). reflexivity.
        -- fold nv c. apply (HREB rb md0 HE PF phUF3 (or_intror eq_refl)). cbn zeta. fold nv c cs. split; [intros _; exact LT | intros _; reflexivity].
        -- exact HPOP.
Qed.
End ASMP.
End SpineCallocR15.

(* [comment removed for export] *)
Module RebuildQI.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "bview"; "view"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI"; "ZI"; "initA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "Some"; "bool"; "false"; "list"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "IMG_LO"; "Size"; "max_count"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "bandtp_inv"; "model_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "aa_geom"; "ag_thread"; "ageom"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws Inv InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue ContractFreeNull SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.RebuildR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RI.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvQC.

Lemma init_rebuild : ltac2:(tb__ "0|8|
S20S1S1S17S12Q40M0A1A1M1G1SfSfVAInv;R7R6R4R2A4S3S15S21R8A1S16A3S22R9A1S24S23R1A1S6SeVsegs;S0R9A1A2SdSeVsegs;S0RbA1A2SdS6S5S10R4R1A2A1S3S18S12Q8A1M2A1M3R4R2A1R3R2A1A3F_;Fz;S6S10R5R1A2S4G2G2S3G3R6R3A1S14G2R1A2A3Lb;A2F_;Fz;S6S2S8S1aR1A2S9R1S19A2A2S3G3S0RfS13G0R2A2M4A2S0R10G4A2A3F_;Fa;S6S2S8Z1R1A2S8R1Z1eA2A2S2SbR7ScS7S7R8Zd0A2SaZ50R2A2A2M5U4M6Z0A3A2S2SbR7ScS7G5Z4A2G6S1cR2A1A3A2SbR7ScS7G5Z8A2U8S1bR2A1A3A2A2A2F_;Fc;S1fVsegs;S11R11A1RdRbA4S1eR7ReA2S2VAInv;S11R13A1M7R11RfRdA4S1dVCST;VXGL;R13G7S0R12A1S0R11A1A6A2F_;F_;F_;F_;F_;F_;TvE;Tv3;TT;TG;F_;F_;Fmd;Fmd0;Ftp;Ftp0;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp0 tp md0 md HA Hini G T v3 vE VO PRES HRMI HCELLS HMD HBT.
  set (Ar := initA A).
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB). fold vE in HR, HF, HRest. fold G in HG, HR, HF, HRest.
  pose proof HG as HG0. pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & TG).
  fold G in G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12, G13, G14, G15, G16, G17, TG. fold T in G4, G5, G10, G13, G14.
  set (SB := ag_spacebeg G) in *.
  assert (GS : 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G /\ SB mod 2 ^ 16 = 0
               /\ (ag_fsb G + 11571200 <= SB \/ SB + 2 ^ 37 + 4096 <= ag_fsb G)).
  { pose proof (geom_old _ HG) as X. rewrite FS_total_val, kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G in X. fold SB in X. clear -X. tauto. }
  destruct GS as (S1 & S2 & S3 & S4).
  pose proof (geom_bands _ HG) as (WF & TB & CB & DB & TI & CTI & DTI). fold G T in TB, TI. fold G in WF, CB, DB, CTI, DTI.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in WF, TB, CB, DB, TI, CTI, DTI. rewrite FS_total_val in WF.
  pose proof HI3 as HI3c. destruct HI3 as (SG3 & LIV3 & SEC3 & Q3 & DEP3 & ND3). fold G in SG3, SEC3, Q3, DEP3.
  pose proof SG3 as SG3c. destruct SG3 as (T3 & CTX3 & DTLS3 & PAB3 & PABT3 & _). rewrite kSpaceSize_val in T3, CTX3, DTLS3, PAB3, SEC3. fold T in T3, PABT3. fold SB in T3, CTX3, DTLS3, PAB3.
  destruct HRest as (Hsep & Hlive & Hprim & Hsec & Hq & Hdep & Hia & HTH & Hmisc). pose proof Hprim as Hprim0.
  destruct Hprim as (PL & P0 & P31 & PC).
  assert (GEO : geoR SB T (topG G)).
  { unfold geoR. clear -S1 S2 TG G4 G5 T3 TB. lia. }
  assert (ZND : forall z, ZI T z \/ ~ ZI T z) by (intros z; unfold ZI; clear; lia).

  assert (ENVF : forall z, ZI T z -> fs_footb G z = false).
  { intros z Hz. apply fs_footb_thread; [exact HG0 | fold G T; unfold ZI in Hz; clear -Hz; lia]. }
  set (m3 := maskv (fs_footb G) v3). set (mE := maskv (fs_footb G) vE).
  assert (AGm : forall z, ~ ZI T z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity | exact (VO z Hz)]. }
  assert (MTH : forall z, T <= z < T + 4096 -> m3 z = v3 z).
  { intros z Hz. unfold m3. apply maskv_out. apply fs_footb_thread; [exact HG0 | fold G T; clear -Hz; lia]. }
  fold mE in Hlive, PC, Hsec, Hq, Hdep, Hia, HTH, Hmisc.
  assert (PRES3 : forall z, ZI T z -> exists b, m3 z = Some b).
  { intros z Hz. rewrite MTH by (unfold ZI in Hz; clear -Hz; lia). exact (PRES z Hz). }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc) | rewrite (AGm z Hn); exact (Hp z Hz)]. }
  assert (PRESB : forall lo hi L, present_but mE lo hi L -> present_but m3 lo hi L).
  { intros lo hi L Hp z Hz HL. destruct (ZND z) as [Hc|Hn]; [exact (PRES3 z Hc) | rewrite (AGm z Hn); exact (Hp z Hz HL)]. }
  assert (EG' : aa_geom Ar = G) by reflexivity.
  assert (HQP : q_pure A) by exact (proj1 Hq).
  assert (HAU : forall c', 1 <= c' <= 30 -> 0 <= cs_allocated_user (SegQ_wf2.cls_of A c') <= kUserSpaceSize).
  { intros c' Hc'. pose proof (PC c' Hc') as HC. unfold class_repr in HC.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _). unfold SegQ_wf2.cls_of, kUserMapSize in *. clear -M2 M3. lia. }

  assert (NE_img : forall z, IMG_LO <= z < IMG_HI -> ~ ZI T z).
  { intros z Hz. unfold IMG_LO, IMG_HI in Hz. apply (zi_out T 65536 6578176 z Hz). clear -TI. lia. }
  assert (NE_space : forall z, SB <= z < SB + 2 ^ 37 + 4096 -> ~ ZI T z).
  { intros z Hz. apply (zi_out T SB (SB + 2 ^ 37 + 4096) z Hz). clear -T3. lia. }
  assert (NE_sec : forall i ch z, nth_error (aa_sec A) i = Some ch ->
            (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch \/ Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch)) -> ~ ZI T z).
  { intros i ch z Hi Hz. destruct (SEC3 i ch Hi) as (E1 & E2 & _). fold T in E2. fold SB in E1.
    destruct Hsec as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D10, D12. unfold PG in D8.
    destruct D10 as (D10a & D10l & _ & _ & D10b).
    destruct Hz as [Hz|Hz].
    - apply (zi_out T (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z Hz). clear -E2. lia.
    - apply (zi_sh_out SB T (topG G) (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z GEO Hz); [clear -D10a; lia | clear -D12 TG; lia]. }
  assert (LIVE_OUT : forall b n z, In (b, n) (aa_live A) ->
            (b - rz n <= z < b + n \/ Sh b <= z < Sh b + (n + 7) / 8) -> ~ ZI T z).
  { intros b n z Hin Hz. destruct (is_primary n) eqn:HP.
    - pose proof (live_prim_czone A HG SG3c mE Hsep Hprim0 b n Hin HP) as LPC. cbv zeta in LPC. destruct LPC as (D1 & O0 & OM & OE & _ & _ & CZ). fold SB in O0, OM, OE, CZ.
      set (c' := ClassID (needed n)) in *. set (o' := b - rz n - (SB + c' * 2 ^ 32)) in *.
      assert (SZ0 : 0 < Size c') by (destruct (Size_facts c' D1) as [X _]; clear -X; lia).
      exact (zi_czone SB T (topG G) c' o' (Size c') z GEO D1 O0 SZ0 OE (CZ z Hz)).
    - destruct (live_sec_map A mE Hsep Hsec HI3c b n Hin HP) as (i & ch & Hi & Eb & RZ & Hn1 & BN & D6 & D0 & DI). unfold PG in Eb, D6.
      apply (NE_sec i ch z Hi). destruct Hz as [Hz|Hz]; [left; clear -Hz Eb RZ BN; lia | right].
      pose proof (Geometry.Sh_mono (sc_map_beg ch) b ltac:(clear -Eb; lia)) as M1.
      pose proof (Sh_add_le b (n + 7) (sc_map_beg ch + sc_map_size ch) ltac:(clear -Eb DI; destruct DI as (X & _); lia) ltac:(clear -Hn1; lia) ltac:(clear -BN; lia)) as M2.
      clear -Hz M1 M2. lia. }
  assert (QF_OUT : forall z, q_foot A z -> ~ ZI T z).
  { intros z Hz. destruct (qfoot_cases A mE HG HI3c HQP Hsec HAU z Hz) as [(c' & o' & (D1 & O0 & OM & OE & IDin) & CZ)|(i & ch & Hi & Hr)].
    - fold SB in CZ. assert (SZ0 : 0 < Size c') by (destruct (Size_facts c' D1) as [X _]; clear -X; lia).
      exact (zi_czone SB T (topG G) c' o' (Size c') z GEO D1 O0 SZ0 OE CZ).
    - exact (NE_sec i ch z Hi Hr). }

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz. apply VO.
    destruct (rtc_foot_cases G z Hz) as [K|[K|[K|[K|K]]]].
    - exact (NE_img z K).
    - fold T in K. apply (zi_out T T (T + 288) z); clear -K; lia.
    - apply (zi_out T (ag_ctx G) (ag_ctx G + 4096) z ltac:(clear -K; lia)). clear -G13. lia.
    - apply (zi_out T (ag_dtls G) (ag_dtls G + 4096) z ltac:(clear -K; lia)). clear -G14. lia.
    - apply (zi_out T (ag_fsb G) (ag_fsb G + 11571200) z ltac:(clear -K; lia)). clear -G10. lia. }
  assert (HFS : fs_inv (restrictv (fs_footb G) v3) Ar).
  { rewrite (restrictv_ext (fs_footb G) vE v3) by (intros z Hz; apply VO; intros Hc; rewrite (ENVF z Hc) in Hz; discriminate).
    exact HF. }
  assert (HLS : live_sep Ar) by exact Hsep.
  assert (HLB : live_block_reprC m3 Ar).
  { apply (live_block_reprC_agree mE m3 A Ar eq_refl); [|intros b n Hin; exact (proj1 (Hsep b n Hin))|exact Hlive].
    intros b n z Hin Hz. apply AGm. exact (LIVE_OUT b n z Hin Hz). }
  assert (HPR : primary_repr m3 Ar).
  { unfold primary_repr. rewrite EG'. split; [exact PL|]. split; [exact P0|]. split; [exact P31|].
    intros c' Hc'. change (aa_cls Ar) with (aa_cls A).
    pose proof (PC c' Hc') as PC'. pose proof PC' as PCd. unfold class_repr in PCd.
    destruct PCd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & M6 & _ & _ & _ & PU & _ & PE & _).
    pose proof (Zle_0_nat (length (cs_free_array (nthZ (aa_cls A) c' cs_empty)))) as L0.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3, M6.
    destruct (HCELLS c' Hc') as (K1' & K2' & K3').
    assert (PCB : T + 288 <= T + 0xd0 + 80 * c' /\ T + 0xd0 + 80 * c' + 80 <= T + 2768) by (clear -Hc'; lia).
    apply (class_repr_init mE m3 G A c' _ Hc' Hini); [| apply PRESB; exact PU | apply PRESX; exact PE | | | | exact PC'].
    - intros z Hz. apply AGm. fold SB in Hz.
      unfold region_info, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kRegionInfoStride in Hz. rewrite kSpaceSize_val in Hz.
      destruct Hz as [Hz|[Hz|Hz]].
      + apply NE_space. clear -Hz Hc'. lia.
      + apply NE_space. clear -Hz Hc' M6 L0. lia.
      + apply (zi_sh_out SB T (topG G) _ _ z GEO Hz); [clear -S1 Hc'; lia | clear -S2 TG Hc' M2 M3; lia].
    - eapply cell_ok_agree; [|exact K1']. cbn [c_addr c_w]. intros k Hk. apply MTH. clear -Hk PCB G4. lia.
    - eapply cell_ok_agree; [|exact K2']. cbn [c_addr c_w]. intros k Hk. apply MTH. clear -Hk PCB G4. lia.
    - eapply cell_ok_agree; [|exact K3']. cbn [c_addr c_w]. intros k Hk. apply MTH. clear -Hk PCB G4. lia. }
  assert (LIVM : forall z, in_rangesZ (aa_live A) z -> in_rangesZ (aa_live Ar) z) by (intros z Hz; exact Hz).
  assert (HSR : secondary_repr m3 Ar).
  { refine (secondary_repr_agree mE m3 A Ar eq_refl eq_refl eq_refl _ _ _ LIVM Hsec).
    - intros i ch z Hi Hz. apply AGm. exact (NE_sec i ch z Hi Hz).
    - intros z Hz. apply AGm. destruct Hsec as (_ & _ & SC2 & _ & SC45 & _). fold G in SC45, Hz. destruct SC45 as [_ (SC4a & _ & SC5 & _ & SC4)].
      unfold kPtrArrayReserve in SC2, SC4, PAB3, PABT3.
      apply (zi_out T (ag_pab G) (ag_pab G + 2 ^ 23) z ltac:(clear -Hz SC2; lia)). clear -PABT3. lia.
    - intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HQR : q_pure Ar /\ cell_ok m3 (mkACell (QG + 72) 8 kQuarantineMin)).
  { split.
    - apply (q_pure_mono A Ar eq_refl eq_refl eq_refl); [|exact HQP]. intros c'. change (SegQ_wf2.cls_of Ar c') with (SegQ_wf2.cls_of A c'). clear; lia.
    - eapply cell_ok_agree; [|exact (proj2 Hq)]. cbn [c_addr c_w]. intros k Hk. apply AGm. apply NE_img. unfold QG, IMG_LO, IMG_HI. clear -Hk. lia. }
  assert (HIA : ia_inv m3 Ar).
  { refine (ia_inv_agree mE m3 A Ar eq_refl _ Hia). intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HTI : thread_inv m3 G).
  { destruct HTH as [TH1 TH2]. fold G T in TH1, TH2. unfold thread_inv. fold T. split.
    - rewrite AGm; [exact TH1|]. unfold ZI. clear. lia.
    - apply PRESX. exact TH2. }
  assert (HMI : misc_inv m3).
  { refine (misc_inv_agree mE m3 _ Hmisc). intros z Hz. apply AGm. exact (NE_img z Hz). }
  assert (HDEP : depot_wf m3 Ar).
  { unfold depot_wf in Hdep |- *. change (aa_depot Ar) with (aa_depot A). eapply depot_mem_frame; [|exact Hdep]. intros a Ha. apply AGm.
    assert (BLK : forall bb L, In (bb, L) (dblocks (aa_depot A)) -> bb <= a < bb + L -> ~ ZI T a).
    { intros bb L Hbb Hab. destruct (DEP3 (bb, L) Hbb) as (DI & ST & _ & _ & _ & SS & _). unfold sepZ in ST, SS. cbn [fst snd] in DI, ST, SS. fold T in ST.
      apply (zi_out T bb (bb + L) a Hab). clear -ST. lia. }
    destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
    - apply (NE_img a). unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. unfold IMG_LO, IMG_HI. clear -Hs. lia.
    - apply (BLK bb NBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. left. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb].
    - apply (BLK bb FBSZ); [|exact Hab]. unfold dblocks. apply in_or_app. right. apply in_map_iff. exists bb. split; [reflexivity | exact Hbb]. }
  assert (HI3' : inv3 Ar).
  { pose proof HI3c as (X1' & X2' & X3' & X4' & X5' & X6' & X7' & X8' & X9'). split; [exact X1'|]. split; [exact X2'|]. split; [exact X3'|].
    split; [exact X4'|]. split; [exact X5'|]. split; [exact X6'|]. split; [exact X7'|]. split; [exact X8'|]. intros _. reflexivity. }
  assert (HA' : AInv Ar rho3 tp md).
  { unfold AInv, AInvQC. rewrite EG'. fold v3. split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|].
    split; [|split; [exact HMD | split; [exact HI3' | exact HBT]]].
    fold m3. split; [exact HLS|]. split; [exact HLB|]. split; [exact HPR|]. split; [exact HSR|]. split; [exact HQR|].
    split; [exact HDEP|]. split; [exact HIA|]. split; [exact HTI | exact HMI]. }
  split; [exact HA'|].

  assert (HFv : fs_inv (restrictv (fs_footb G) vE) A) by exact HF.
  assert (RMO : forall a, 0 <= a < 2 ^ 64 -> ~ ZI T a -> rm rho3 (Z_to_bv 64 a) = rm rhoE (Z_to_bv 64 a)).
  { intros a Ha Hn. destruct (Z_lt_dec a IMG_LO) as [LO|NLO]; [|destruct (Z_le_dec IMG_HI a) as [HI|NHI]].
    - rewrite <- (view_rm_off (rm rho3) a Ha (or_introl LO)), <- (view_rm_off (rm rhoE) a Ha (or_introl LO)). exact (VO a Hn).
    - rewrite <- (view_rm_off (rm rho3) a Ha (or_intror HI)), <- (view_rm_off (rm rhoE) a Ha (or_intror HI)). exact (VO a Hn).
    - apply HRMI. clear -NLO NHI. lia. }
  assert (DEFM : forall a, IMG_HI <= a < 2 ^ 64 -> rm rhoE (Z_to_bv 64 a) <> None -> rm rho3 (Z_to_bv 64 a) <> None).
  { intros a Ha Hd. assert (Ha' : 0 <= a < 2 ^ 64) by (unfold IMG_HI in Ha; clear -Ha; lia).
    rewrite <- (view_rm_off (rm rho3) a Ha' (or_intror (proj1 Ha))). rewrite <- (view_rm_off (rm rhoE) a Ha' (or_intror (proj1 Ha))) in Hd.
    change (v3 a <> None). change (vE a <> None) in Hd. destruct (ZND a) as [Hc|Hn]; [destruct (PRES a Hc) as [b Hb]; rewrite Hb; discriminate | rewrite (VO a Hn); exact Hd]. }
  split.
  2: { intros x0 j Hx Hj Hdef.
       assert (Bx : 0 <= x0 < 2 ^ 47).
       { destruct Hx as [[CX _]|GX]; [exact (proj1 (client_addr_bounds CST HCST A x0 _ HG HFv Hsep CX))|].
         destruct (HXGL x0 GX) as [XG1 XG2]. unfold IMG_HI in XG2. clear -XG1 XG2. lia. }
       unfold word_byte. apply DEFM; [|exact Hdef].
       pose proof (Z.div_mod (Sh x0) 8 ltac:(clear; lia)) as DM. pose proof (Z.mod_pos_bound (Sh x0) 8 ltac:(clear; lia)) as MB.
       unfold Sh, SHADOW_OFF, IMG_HI in DM, MB |- *. pose proof (Z.div_le_mono 0 x0 8 ltac:(clear; lia) ltac:(clear -Bx; lia)) as D0.
       pose proof (Z.div_lt_upper_bound x0 8 (2 ^ 44) ltac:(clear; lia) ltac:(clear -Bx; lia)) as D1. change (0 / 8) with 0 in D0.
       clear -Hj DM MB D0 D1. lia. }
  intros a Ha Hcl.

  assert (NOC : forall y, client_addrA CST A y ->
            (exists b n, In (b, n) (aa_live A) /\ b <= y < b + n)
            \/ (0 <= y < 2 ^ 47 /\ (y < T \/ T + 4096 <= y))).
  { intros y Hy.
    destruct (client_addr_cases CST A y _ HFv Hy) as [S|[L|[FR|[C|FL]]]].
    - right. fold G in S. clear -S S2 G5 TG. lia.
    - left. exact L.
    - right. destruct FR as (c0 & p0 & Hc0 & Hp0 & _ & Hyf). pose proof (fs_geom_nums G c0 p0 HG Hc0 Hp0) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G in Hyf. clear -Hyf M S4 G10 WF G2 G3 TG. lia.
    - right. destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI in X. clear -X S1 TI. lia.
    - right. destruct FL as (c0 & p0 & Hc0 & Hp0 & _ & ->). pose proof (fs_geom_nums G c0 p0 HG Hc0 Hp0) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G. unfold fs_flags. rewrite FS_kFlagsOffset_val.
      unfold fs_flags in M. rewrite FS_kFlagsOffset_val in M. clear -M S4 G10 WF G2 G3 TG. lia. }
  assert (SHY : forall y, 0 <= y < 2 ^ 47 -> ~ ZI T (Sh y)).
  { intros y By.
    pose proof (Z.div_mod y 8 ltac:(clear; lia)) as DY. pose proof (Z.mod_pos_bound y 8 ltac:(clear; lia)) as MY.
    apply (zi_sh_out SB T (topG G) (8 * (y / 8)) (8 * (y / 8) + 8) (Sh y) GEO); [|clear -By DY MY; lia|clear -By DY MY; lia].
    unfold Sh. replace (8 * (y / 8) / 8) with (y / 8) by (rewrite Z.mul_comm, Z.div_mul; clear; lia).
    replace ((8 * (y / 8) + 8) / 8) with (y / 8 + 1) by (replace (8 * (y / 8) + 8) with ((y / 8 + 1) * 8) by (clear; lia); rewrite Z.div_mul; clear; lia).
    clear. lia. }
  apply RMO; [exact Ha|].
  destruct Hcl as [[CL1 _]|[CL1 _]].
  - destruct (NOC a CL1) as [(b & n & Hbn & Hab)|(B1 & B2)].
    + apply (LIVE_OUT b n a Hbn). left. pose proof (rz_bound n). clear -Hab H. lia.
    + unfold ZI. clear -B2. lia.
  - destruct CL1 as [(y & Cy & ->)|(y & Gy & ->)].
    + apply SHY. destruct (NOC y Cy) as [(b & n & Hbn & Hyb)|(B1 & _)]; [|exact B1].
      exact (proj1 (client_addr_bounds CST HCST A y _ HG HFv Hsep Cy)).
    + destruct (HXGL y Gy) as [Y1 Y2]. unfold IMG_HI in Y2. apply (SHY y). clear -Y1 Y2. lia.
Qed.
End RI.
End RebuildQI.

(* [comment removed for export] *)
Module SpineMallocQU1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "ex"; "or"; "@Corelib.Init.Datatypes"; "nat"; "list"; "cons"; "prod"; "pair"; "nil"; "bool"; "true"; "andb"; "false"; "app"; "option"; "None"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "valuation"; "cell"; "rm"; "mkCell"; "ss_objs"; "eval"; "smatch"; "sstate"; "sv_eqb"; "DUnknown"; "c_off"; "c_val"; "c_width"; "mkObj"; "rw"; "sprop"; "ss_facts"; "swf"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "lt"; "eqb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQU1"; "JU"; "cell_inb"; "O_arrF"; "O_pcmZ"; "arr_okb"; "cU0"; "NU2"; "O_arr0"; "cU2"; "cnt_spec"; "idx1"; "idx2"; "kU1"; "kU2"; "perm_okb"; "sU1"; "@Corelib.Init.Nat"; "sub"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "incl"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_pcc0"; "pc_base"; "O_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "nobj"; "addobjs"; "nxt"; "keepn"; "selobjs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "UStopLeOrPc"; "ustop"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "aa_cache_inited"; "ag_thread"; "budget_bound"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "max_count"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI"; "initA"; "ZI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "view"; "bview"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "cfg_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "w_cfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "CLS30"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "PCE"; "frozen"; "mlink"; "ph0"; "rmlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "JLRf"; "JRf"; "L_rf"; "NXR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "entryRq"; "BASEFq"; "BASEOq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2"; "cfacts"; "rigids"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQU1.UJ"; "JU"; "umem";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQU1.USTEPS"; "ulinkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "JK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "ltb"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.RebuildRN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.RebuildQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ5.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition NU0 : list carve_spec := ltac2:(tb__ "0|7|
S9SaSaSaS16S0A2M0S0A2M1S8SaSaS0S7A2M2S16A2M3A1M4A2M5SbG1G4SbG0S0SbS16S0S4dZ4M6A4Z8A4S9G3SbG2S16SbS0S7G6U4A4S17Z0A1A4ScG3A1A3A4ScG5A1A3").
Definition O_pcmZ : sobj := ltac2:(tb__ "0|3|
S8eS4dZ4M0Z8S9SaSaS0S7A2M1S16A2M2SbG1S16SbS0S7G0U4A4S17Z0A1A4ScG2A1A3A4").
Definition cnt_spec : list (Z * nat * sv) := ltac2:(tb__ "0|1|
S4aS0SaSaS0S7A2M0S16A2S0SbG0S16SbS0S7S2aZd0S2cZ50R1A2A2U4A4S17Z0A1A4Lc;S7bA4").
Definition NU1 : list carve_spec := ltac2:(tb__ "0|4|
S9SaSaSaS16S0A2M0S0A2M1S8SaSaS0S7A2S16A2A1M2A2M3SbG1G2SbG0S0SbS16S0S64Z120A4Zad0A4S3eA4ScG3A1A3").
Definition O_arr0 : sobj := carved vT 288 2768 cnt_spec.
Definition O_arrF (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S25S64S17Z120A1S17Zad0A1Vcells;S21A5").
Definition NU2 : list carve_spec := ltac2:(tb__ "0|7|
S9SaSaSaS16S0A2M0S0A2M1S8SaSaS0S7A2M2S16A2M3A1M4A2M5SbG1G4SbG0S0SbS16S0S4dZ0M6A4Z4A4S9G3SbG2S16SbS0S7G6U4A4S17G6A1A4ScG3A1A3A4ScG5A1A3").
Lemma NU2_objs : ltac2:(tb__ "0|0|
S3S8S15A1S4aS91S15S90S3bA4S9S15S4cScS15A1A3A3"). Proof. reflexivity. Qed.

Definition cU0 (E : axst) : axst := ltac2:(tb__ "0|0|
S50VE;S9S15S38ScS15A1A3S51VE;A1A3").

Definition idx1 (E : axst) : list nat := ltac2:(tb__ "0|2|
S11S7S4bU0S45S4fVE;A1M0U3A2M1A2S9S7S45G0U2A2S9S7G1S9S7S45G0U1A2ScS7A1A3A3A3A3").
Definition sU1 (E : axst) : axst := ltac2:(tb__ "0|0|
S53VE;S3fVE;A1A2").
Definition kU1 (E : axst) : axst := ltac2:(tb__ "0|0|
S52S44VE;A1S45S4fVE;A1U2A2A2").
Definition cU1 (E : axst) : axst := ltac2:(tb__ "0|0|
S50S41VE;A1S9S15S3cScS15A1A3S51VE;A1A3").
Definition kU2 (E : axst) : axst := ltac2:(tb__ "0|0|
S52VE;S45S4fVE;A1U1A2A2").
Definition cU2 (E : axst) : axst := ltac2:(tb__ "0|0|
S50S42VE;A1S9S15S4cScS15A1A3S51VE;A1A3").

Definition idx2 (E : axst) : list nat := ltac2:(tb__ "0|2|
S11S7S4bU0S45S4fVE;A1M0U2A2M1A2S9S7S45G0U1A2S9S7G1ScS7A1A3A3A3").
Definition eU (E : axst) : axst := ltac2:(tb__ "0|1|
S53S3dVE;A1M0S40G0A1A2").

Definition perm_okb (n : nat) (idxs : list nat) : bool := ltac2:(tb__ "0|0|
SfSfS76Vidxs;A1S47S7S7S96R1Vn;A2Li;Vidxs;A3A2S47S7S7S48S7S95R1A1Vidxs;A3Li;S4bU0Vn;A2A3A2").
Lemma perm_okb_sound : ltac2:(tb__ "0|0|
S7S8S7A1S3SdS43R2R1A2SeA3S2S3SdS76R2A1SeA3S2S7S46S7R1R3A3S6fR2R5A2F_;Fi;S7S6fR1R4A2S46S7R2R4A3F_;Fi;A2A2F_;Fidxs;Fn;").
Proof.
  intros n idxs H. unfold perm_okb in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [exact H1|]. split.
  - intros i Hi. apply Nat.ltb_lt. exact (proj1 (forallb_forall _ _) H2 i Hi).
  - intros i Hi. pose proof (proj1 (forallb_forall _ _) H3 i ltac:(apply in_seq; lia)) as X.
    apply existsb_exists in X as (j & Hj & E). apply Nat.eqb_eq in E. subst j. exact Hj.
Qed.

Definition cell_inb (off w v : Z) (cells : list cell) : bool := ltac2:(tb__ "0|0|
S48S19S19SfSfS20S22R1A1S17Voff;A1A2S2eS24R1A1Vw;A2A2S20S23R1A1S17Vv;A1A2A2Lcl;Vcells;A3").
Definition arr_okb (cells : list cell) : bool := ltac2:(tb__ "0|2|
S47S0S0SfSfS36S2aZd0S2cZ50R1A2M0A2Z4M1Z0Vcells;A4S36S2aZd4G0A2G1S66R1A1Vcells;A4A2S36S2aZd8G0A2Z8S65R1A1Vcells;A4A2Lc;S7bA3").
Lemma cell_inb_In : ltac2:(tb__ "0|0|
S0S0S0S8S19A1S3SdS36R4R3R2R1A4SeA3S46S19S1bS17R5A1R4S17R3A1A3R2A3F_;Fcells;Fv;Fw;Foff;").
Proof.
  intros off w v cells H. unfold cell_inb in H. apply existsb_exists in H as ([o w' v'] & Hin & E). cbn [c_off c_width SymState.c_val] in E.
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2]. apply sv_eqb_sound in E1. apply sv_eqb_sound in E3. apply Z.eqb_eq in E2.
  subst o w' v'. exact Hin.
Qed.
Lemma arr_okb_In : ltac2:(tb__ "0|2|
S8S19A1S0S3SdS39R2A1SeA3S2S2bZ1R2A2S2bR2Z1eA2A2S2S46S19S1bS17S2aZd0S2cZ50R3A2M0A2A1Z4M1S17Z0A1A3R4A3S2S46S19S1bS17S2aZd4G0A2A1G1S17S66R3A1A1A3R4A3S46S19S1bS17S2aZd8G0A2A1Z8S17S65R3A1A1A3R4A3A2A2F_;F_;Fc;Fcells;").
Proof.
  intros cells c H Hc. unfold arr_okb in H. pose proof (proj1 (forallb_forall _ _) H c (proj2 (In_CLS30 c) Hc)) as X. cbv beta in X.
  apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
  split; [exact (cell_inb_In _ _ _ _ X1)|]. split; [exact (cell_inb_In _ _ _ _ X2) | exact (cell_inb_In _ _ _ _ X3)].
Qed.

Lemma uninit_frame : ltac2:(tb__ "0|5|
S5aS18S8S2fQ40A1A1S32S7aR4R3R2R1A4S3SdS5cR5A1S10A3S5dS5bR6A1A1S0S6dS92S1aR6A1A2S6eS2S0S0S2S2bZ1R2A2S2bR2Z1eA2A2S2S2bS2aS2aR5Zd0A2S2cZ50M0R3A2A2M1R2A2S2dR2S2aG1G0A2A2A2S3S12S2fQ8M2A1M3A1M4R5R3A1S14G3S31G2Z0A2A2A3F_;F_;Fz;Fc;S0S2S2bS2aR3Za80A2R1A2S2dR1S2aR3Zc60A2A2A2S5G3G3S3G4R4R3A1S14G3R1A2A3Lb;A2F_;Fz;A2Tm0;TT;F_;F_;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 HA Hini T m0. pose proof HA as (HG & _ & _ & HRest & _).
  destruct HRest as (_ & _ & Hprim & _ & _ & _ & _ & HTH & _). destruct Hprim as (_ & _ & _ & PC).
  assert (MT : forall z, T <= z < T + 0x1000 -> maskv (fs_footb (aa_geom A)) m0 z = m0 z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  split.
  - intros c z Hc Hz. pose proof (PC c Hc) as P4. unfold class_repr in P4.
    destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CN & _).
    destruct (CN Hini) as [_ FL]. fold T in FL. rewrite <- MT by (clear -Hz Hc; lia). exact (FL z Hz).
  - intros z Hz. destruct HTH as [_ TH2]. fold T in TH2. destruct (TH2 z Hz) as [b Hb]. exists b. rewrite <- MT by (clear -Hz; lia). exact Hb.
Qed.

Section UJ.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Let T : Z := ag_thread (aa_geom A).

Definition umem (s : bool) (m0 m : bview) : Prop := ltac2:(tb__ "0|6|
SdOLs;Vs;S2S0S4S6aVT;R1A2M0A1S3S12S2fQ8A1M1A1M2Vm;R2A1M3Vm0;R2A1A3F_;Fz;S2S0G0S4S3G2G3S13G1A1A3A1F_;Fz;S0S2S2bZ1R1A2S2bR1Z1eA2A2S2S6bVm;S6cS2aS2aVT;Zd0A2S2cZ50R2A2A2M4U4M5Z0A3A2S2S6bVm;S6cS2aG4Z4A2G5S66R2A1A3A2S6bVm;S6cS2aG4Z8A2U8S65R2A1A3A2A2A2F_;Fc;A2A2S0S3G2Vm;R1A1Vm0;R1A1A3Fz;Xdx2").
Definition JU (s : bool) : jpredA := ltac2:(tb__ "0|2|
S18S8S2fQ40A1A1S8S33A1S32S2S7dVrb;R4A2S2VKc;R2R1A2S2S7eVA;Vrb;Vtp0;Vmd0;S7fR3R1A7S2S8bVs;S6dS34S1aVrb;A1M0A2S6dS34S1aR4A1M1A2A3S80G0G1A2A2A2A2A2Lmd;Ltr;Ltp;Lr;").

Lemma JU_K : ltac2:(tb__ "0|0|
SdS93VKc;S8aR1A1A2Fs;").
Proof. intros s r t tr md (_ & HK & _). exact HK. Qed.

Lemma JU_stable : ltac2:(tb__ "0|0|
SdS1S58VKc;A1S97PdcR2A2S79S34R3S8aR4A1A3F_;F_;Fn;Fs;").
Proof.
  intros s n HKc Hn r r' tp tr md md' Hag Hme (HF & HK & HM & HR & HRM).
  destruct Hag as (Hw & Hl & Hm).
  assert (Erm : rm r' = rm r) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  assert (Hlt : forall i, (i < 220)%positive -> rw r' i = rw r i) by (intros i Hi; symmetry; apply Hw; lia).
  destruct Hme as ((mat' & ->) & Hpaid & _).
  split; [|split; [|split; [|split]]].
  - destruct HF as [F1 F2]. split; [intros i Hi; rewrite (Hlt i Hi); exact (F1 i Hi) | intros l; rewrite <- (Hl l); exact (F2 l)].
  - rewrite with_vm_backing_with_vm. apply HKc. exact HK.
  - unfold mlink in *. cbn zeta in *. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|].
    exists tp1. split; [exact M7|]. split; [exact M8|]. split; [exact M9|]. rewrite Hpaid. exact M10.
  - rewrite Erm. exact HR.
  - rewrite Erm. exact HRM.
Qed.
End UJ.

Lemma pc_base_val : ltac2:(tb__ "0|0|
S5aS18S18S88R3R2A2S89R4R3R2A3S3S0S30Q40S1dR3S4dA2A2S7cR5R4A2A3F_;F_;Fr;Frb;FA;").
Proof.
  intros A rb r CF RG. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & _ & _) & _).
  destruct RG as (_ & _ & E151 & _ & _ & _ & _ & E158).
  unfold pc_base, vT, V_CLS, PCE. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
  rewrite (Z.mod_small (_ * 80)) by lia. rewrite (Z.mod_small (_ + 208)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma vT_val : ltac2:(tb__ "0|0|
S5aS18S18S88R3R2A2S89R4R3R2A3S3S0S30Q40S1dR3S64A2A2S5dS5bR5A1A1A3F_;F_;Fr;Frb;FA;").
Proof.
  intros A rb r CF RG. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as (_ & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & _ & _) & _).
  destruct RG as (_ & _ & E151 & _). unfold vT. cbn [eval]. rewrite E151. apply u64_lit. lia.
Qed.

Section UENTRY.
Variable nW : nat. Variable st : ustop.
Let W : list ulink := Wcan nW.
Variable E3 : axst.
Hypothesis SK3 : ltac2:(tb__ "0|1|
S3S8SaSaS16S16A2S16A2M0A1S4aS15G0S8dS1cS60VE3;A1A1A4S4aS15G0S8dS11S15S87VW;A1S9S15S4cS9S15S4eScS15A1A3A3A3A4A3").
Hypothesis XX3 : ax_X E3 = [].
Hypothesis XF3 : ltac2:(tb__ "0|0|
S49S27S86VW;Vst;A2S28S60VE3;A1A1A3").
Hypothesis WU0 : ltac2:(tb__ "0|0|
S3SdS29S60S3aVE3;A1A1A1SeA3").

Lemma uninit_entry : ltac2:(tb__ "0|3|
S5aS57S0S0S18S8S2fQ40M0A1A1S74S3S56Vst;S55A3S3S8S54A1VW;ScS54A1A3F_;S2bS5eR8A1S8fA2S3SdS5cR9A1S10A3S78S34S82RaR9R8R7A4VE3;R6R5R4A6S2S2S3S0R9S94S30G0S26R7PcA2A2M1A1A3S3S0R8G1A3A2S2S85RbR7R6S73S75R5A1A1M2VW;Vst;R7A7S78S34S35RbRaR7R6G2S10A6S3aVE3;A1R7R6R5A6A2A2F_;F_;F_;F_;Fw;Ftp;FrhoE;Fnv0;Fc0;FKc;FA;").
Proof.
  intros A Kc c0 nv0 rhoE tp w HW HBUD Hini H.
  pose proof H as [HsmA HJ]. destruct HJ as ((HA & HK & Htp & Htop & HRQ) & (Hnv0 & Hcls0 & E12 & E158 & E148 & Hc0 & Hroom)).
  assert (ENV : bv_unsigned (rw rhoE 12%positive) = nv0) by (rewrite E12; apply u64_lit; lia).
  set (nv := bv_unsigned (rw rhoE 12%positive)) in *. rewrite <- ENV in Hnv0, Hcls0. subst c0.
  change (SegQ_wf2.cls_of A (cls_of nv)) with (cst_of A nv) in Hc0, Hroom.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  split; [split; [reflexivity | symmetry; exact ENV]|].
  set (rho := rhoE).
  assert (HE : entryRq A rhoE tp (cfg_model (w_cfg w)) W st rho).
  { unfold entryRq. cbn zeta. fold nv. split; [exact (conj HRQ (conj E158 (conj E148 Hroom)))|].
    split; [exact HA|]. split; [exact Htp|]. split; [exact I|]. split; [exact HBUD|]. split; [exact Hnv0|]. split; [exact Htop|].
    split; [unfold cnt_of; rewrite Hc0; reflexivity|]. exact (MI_ivs_wf segs _ _ (proj1 (proj2 HsmA))). }
  split; [exact HE|].
  assert (HFz : frozen rhoE rhoE) by (split; intros; reflexivity).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (pc_base_val A rhoE rhoE CF RG) as EB. pose proof (vT_val A rhoE rhoE CF RG) as ET.
  unfold cfacts in CF. cbn zeta in CF. fold nv in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  set (c := cls_of nv) in *. set (T := ag_thread (aa_geom A)) in *.
  assert (PCr : PCE A rhoE = T + 208 + 80 * c) by (unfold PCE; fold nv c T; clear; lia).
  destruct (uninit_frame A rhoE tp _ HA Hini) as (FZ & _). fold T in FZ.

  assert (Ha : SPA segs (JU A Kc rhoE tp (cfg_model (w_cfg w)) false) E3 rhoE tp w).
  { split; [exact HsmA|]. unfold JU. split; [exact HFz|]. split; [exact HK|]. split; [|split; [intros z; reflexivity | intros a _; reflexivity]].
    unfold mlink, ph0, committed, revealedp, subU, subF. cbn [ph_u ph_f Nat.leb].
    repeat (split; [reflexivity|]). exists []. cbn [app length Z.of_nat]. split; [reflexivity|]. split; [intros p []|]. split; [lia | lia]. }

  destruct (arm_base_disj A rhoE tp _ W st rho (ax_S E3) [O_pcc0; O_st] rhoE _ HW HE HFz Hsm SK3 XF3) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|oc [|os [|? ?]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence).
  assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (RNc : obj_range rhoE oc = (T + 208 + 80 * c, T + 208 + 80 * c + 4)).
  { rewrite (obj_range_skel rhoE oc O_pcc0 SKc). unfold O_pcc0. rewrite obj_range_mk by (clear; lia). rewrite EB, PCr. f_equal; clear; lia. }
  assert (RNs : obj_range rhoE os = (T + 2768, T + 3168)).
  { rewrite (obj_range_skel rhoE os O_st SKs). unfold O_st. rewrite obj_range_mk by (clear; lia). rewrite ET. reflexivity. }
  apply (SPA_carve_list segs _ rhoE E3 tp w NU0 (nxt E3) Ha WU0).
  - apply Pos.le_refl.
  - unfold NU0. apply Forall_cons; [|apply Forall_nil].
    rewrite EB, PCr. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear -C1 T1; lia|]. split; [clear -C1 T1 T2 TG; lia|].
    split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
    assert (BY : forall off, 4 <= off < 8 -> rd_of segs (rm rhoE) (Z_to_bv 64 (T + 208 + 80 * c + off)) = Some (Z_to_bv 8 0)).
    { intros off Hoff. pose proof (FZ c (T + 208 + 80 * c + off) C1 ltac:(clear -Hoff; lia)) as Hb. rewrite view_in in Hb by (clear -Hoff C1 T1 T2 TG; lia). exact Hb. }
    split.
    { intros off Hoff. eapply wok_rd_off_image2; [| |exact (BY off Hoff)]; [clear -Hoff C1 T1 T2 TG; lia | clear -Hoff C1 TI; lia]. }
    split; [|unfold xwords_clear; rewrite XX3; intros rr y j []].
    apply Forall_cons; [|apply Forall_nil]. intros j Hj. cbn [eval].
    rewrite (enc_bytes_zero_nth 4 (Z_to_bv 64 0) j ltac:(apply u64_lit; clear; lia) Hj).
    replace (T + 208 + 80 * c + 4 + Z.of_nat j) with (T + 208 + 80 * c + (4 + Z.of_nat j)) by (clear; lia). apply BY. clear -Hj. lia.
  - cbn [map carve_obj NU0]. unfold carved. apply Forall_cons; [|apply Forall_nil]. rewrite obj_range_mk by (clear; lia). rewrite EB, PCr.
    rewrite EO. apply Forall_app. split.
    + apply BZ. left. fold T. clear -C1. lia.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; [rewrite RNc | rewrite RNs]; unfold ranges_disjoint; cbn [fst snd]; clear -C1; lia.
  - cbn [map carve_obj NU0 pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.
End UENTRY.

Section USTEPS.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variables (W : list Iface.ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
S3S56Vst;S55A3S3S8S54A1VW;ScS54A1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S85VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis Hini : aa_cache_inited A = false.
Notation JUp := (JU A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let T : Z := ag_thread (aa_geom A).

Lemma u_nums : ltac2:(tb__ "0|3|
S2S2S2bZ1Vc;A2S2bVc;Z1eA2A2S2S2bZ1000M0VT;A2S2S2bS2aVT;G0A2M1S5fS5bVA;A1A1M2A2S2S2bG2Z7fffff800000A2S2S6S2bG1Z10000A2S2bZ646000VT;A2A2S3S0S7cVA;Vrb;A2S2aS2aVT;Zd0A2S2cZ50Vc;A2A2A3A2A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c T in CF.
  destruct CF as ((_ & C1 & _) & _ & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  split; [exact C1|]. split; [exact T1|]. split; [exact T2|]. split; [exact TG|]. split; [exact TI|]. unfold PCE. fold nv c T. lia.
Qed.

Lemma u_release1 : ltac2:(tb__ "0|3|
S1fS8S15A1M0S18S8S2fQ40A1A1S8S33A1M1S70S32S32S3G0S1cR8A1S11S15R7S9S15S4cS9S15S38ScS15A1A3A3M2A3A3S1eS34R7R9SbG1S71R5S72R4R3A2A4A4S35VA;VKc;Vrb;Vtp0;Vmd0;S10R8R7R6R3AaS35VA;VKc;Vrb;Vtp0;Vmd0;S10S77R9G2R6A3R8R7R4AaF_;F_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;FK;FS;").
Proof.
  intros S K r tp tr ms md mdJ HO Hsm (HFz & HK & HM & HR & HRM).
  destruct u_nums as (C1 & T1 & T2 & TG & TI & PCr).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (pc_base_val A rb r CF RG) as EB. rewrite PCr in EB.
  destruct HE as (_ & HA & _). destruct (uninit_frame A rb tp0 md0 HA Hini) as (FZ & _). fold T in FZ.
  set (r3 := rho_absorb r [O_pcc0; O_pcmZ] ms).
  assert (RC : obj_range r O_pcc0 = (T + 208 + 80 * c, T + 208 + 80 * c + 4)).
  { unfold O_pcc0. rewrite obj_range_mk by lia. rewrite EB. f_equal; lia. }
  assert (RM : obj_range r O_pcmZ = (T + 208 + 80 * c + 4, T + 208 + 80 * c + 8)).
  { unfold O_pcmZ, carved. rewrite obj_range_mk by lia. rewrite EB. reflexivity. }

  assert (EZ : forall k j, (j < k)%nat -> nth j (enc_bytes k (Z_to_bv 64 0)) (Z_to_bv 8 0) = Z_to_bv 8 0) by (intros k j Hj; apply enc_bytes_zero_nth; [apply u64_lit; lia | exact Hj]).
  assert (M3 : forall z, T + 208 + 80 * c <= z < T + 208 + 80 * c + 8 -> view segs (rm r3) z = Some (Z_to_bv 8 0)).
  { intros z Hz. destruct (Z_lt_dec z (T + 208 + 80 * c + 4)) as [LT|GE].
    - destruct (absorb_obj r S tr ms md K [O_pcc0; O_pcmZ] O_pcc0 Hsm HO (or_introl eq_refl)) as (_ & AS & _).
      destruct (AS (mkCell (SLit 0) 4 (SLit 0)) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb (Z.to_nat (z - (T + 208 + 80 * c))) ltac:(cbn [c_width]; lia)).
      cbn [ob_base O_pcc0 eval c_off SymState.c_val c_width] in ASb. rewrite soff_lit_small in ASb by lia. fold (eval r pc_base) in ASb. rewrite EB in ASb.
      rewrite EZ in ASb by lia.
      unfold r3. rewrite view_in by lia. replace z with (T + 208 + 80 * c + 0 + Z.of_nat (Z.to_nat (z - (T + 208 + 80 * c)))) at 1 by lia. exact ASb.
    - destruct (absorb_obj r S tr ms md K [O_pcc0; O_pcmZ] O_pcmZ Hsm HO (or_intror (or_introl eq_refl))) as (_ & AS & _).
      destruct (AS (mkCell (SLit 4) 4 (SLit 0)) (or_introl eq_refl)) as (_ & _ & ASb). specialize (ASb (Z.to_nat (z - (T + 208 + 80 * c + 4))) ltac:(cbn [c_width]; lia)).
      cbn [ob_base O_pcmZ carved eval c_off SymState.c_val c_width] in ASb. rewrite soff_lit_small in ASb by lia. fold (eval r pc_base) in ASb. rewrite EB in ASb.
      rewrite EZ in ASb by lia.
      unfold r3. rewrite view_in by lia. replace z with (T + 208 + 80 * c + 4 + Z.of_nat (Z.to_nat (z - (T + 208 + 80 * c + 4)))) at 1 by lia. exact ASb. }
  unfold JU. split; [exact HFz|]. split; [exact HK|]. split; [exact HM|]. split.
  - cbn [umem] in HR |- *. intros z. destruct (Z_le_dec (T + 208 + 80 * c) z) as [H1|H1]; [destruct (Z_lt_dec z (T + 208 + 80 * c + 8)) as [H2|H2]|].
    + rewrite (M3 z (conj H1 H2)). symmetry. apply (FZ c z C1). lia.
    + unfold r3. rewrite view_absorb_out; [exact (HR z)|]. intros o [<-|[<-|[]]]; [rewrite RC | rewrite RM]; cbn [fst snd]; lia.
    + unfold r3. rewrite view_absorb_out; [exact (HR z)|]. intros o [<-|[<-|[]]]; [rewrite RC | rewrite RM]; cbn [fst snd]; lia.
  - apply (rmlink_absorb _ r [O_pcc0; O_pcmZ] ms HRM). intros o [<-|[<-|[]]]; [rewrite RC | rewrite RM]; cbn [fst snd]; unfold IMG_LO, IMG_HI; lia.
Qed.

Lemma u_release2 : ltac2:(tb__ "0|3|
S1fS8S15A1M0S8S19A1S18S8S2fQ40A1A1S8S33A1M1S70S32S32S3G0S1cR9A1S11S15R8S9S15S37R7A1ScS15A1M2A3A3A3S3SdS39R8A1SeA3S1eS34R8RbSbG1S71R6S72R5R4A2A4A4S35VA;VKc;Vrb;Vtp0;Vmd0;S10R9R8R7R4AaS35VA;VKc;Vrb;Vtp0;Vmd0;SeS77RaS9S15S37RbA1G2A3R7A3R9R8R5AaF_;F_;F_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;Fcells;FK;FS;").
Proof.
  intros S K cells r tp tr ms md mdJ HO HOK Hsm (HFz & HK & HM & HR & HRM).
  destruct u_nums as (C1 & T1 & T2 & TG & TI & PCr).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (vT_val A rb r CF RG) as ET. fold T in ET.
  set (r3 := rho_absorb r [O_arrF cells] ms).
  assert (RA : obj_range r (O_arrF cells) = (T + 288, T + 2768)).
  { unfold O_arrF. rewrite obj_range_mk by lia. rewrite ET. reflexivity. }
  destruct (absorb_obj r S tr ms md K [O_arrF cells] (O_arrF cells) Hsm HO (or_introl eq_refl)) as (_ & AS & AP & _).
  cbn [ob_base O_arrF ob_cells ob_dflt] in AS, AP. rewrite ET in AS, AP.
  assert (CELL : forall off w v, In (mkCell (SLit off) (Z.of_nat w) (SLit v)) cells -> 0 <= off < 4096 -> cell_ok (view segs (rm r3)) (mkACell (T + off) w v)).
  { intros off w v Hin Hoff j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    destruct (AS _ Hin) as (B1 & B2 & ASb). cbn [c_off c_width SymState.c_val] in B1, B2, ASb. rewrite soff_lit_small in B1, B2, ASb by lia.
    unfold obj_lo_of, obj_hi_of in B1, B2. cbn [ob_lo ob_hi O_arrF] in B1, B2. rewrite !soff_lit_small in B1, B2 by lia.
    specialize (ASb j ltac:(rewrite Nat2Z.id; exact Hj)). rewrite Nat2Z.id in ASb. cbn [eval] in ASb.
    unfold r3. rewrite view_in by lia. exact ASb. }
  unfold JU. split; [exact HFz|]. split; [exact HK|]. split; [exact HM|]. split.
  - cbn [umem] in HR |- *. fold T. split; [|split].
    + intros z Hz. unfold r3. rewrite view_absorb_out; [exact (HR z)|]. intros o [<-|[]]. rewrite RA. cbn [fst snd]. exact Hz.
    + intros z Hz. unfold ZI in Hz. destruct (AP (or_introl eq_refl) (z - T)) as [x Hx].
      { unfold obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi O_arrF]. rewrite !soff_lit_small by lia. lia. }
      replace (T + (z - T)) with z in Hx by lia. unfold r3. rewrite view_in by lia. rewrite Hx. discriminate.
    + intros c' Hc'. destruct (arr_okb_In cells c' HOK Hc') as (I1 & I2 & I3).
      split; [|split].
      * replace (T + 208 + 80 * c') with (T + (208 + 80 * c')) by lia. apply (CELL _ 4%nat); [exact I1 | lia].
      * replace (T + 208 + 80 * c' + 4) with (T + (212 + 80 * c')) by lia. apply (CELL _ 4%nat); [exact I2 | lia].
      * replace (T + 208 + 80 * c' + 8) with (T + (216 + 80 * c')) by lia. apply (CELL _ 8%nat); [exact I3 | lia].
  - apply (rmlink_absorb _ r [O_arrF cells] ms HRM). intros o [<-|[]]. rewrite RA. cbn [fst snd]. unfold IMG_LO, IMG_HI. lia.
Qed.

Lemma u_rebuild : ltac2:(tb__ "0|1|
S18S8S2fQ40A1A1S8S33A1S32S35VA;VKc;Vrb;Vtp0;Vmd0;SeR4R3R2R1AaS2S7aS69VA;A1M0R5R4R2A4S59VCST;VXGL;VA;G0S1aVrb;A1S1aR5A1A6A2F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md (HFz & HK & HM & HR & HRM).
  pose proof HE as (_ & HA & _). pose proof HA as (_ & _ & _ & _ & HM0 & _ & HB0).
  unfold mlink in HM. cbn zeta in HM. unfold ph0, committed, revealedp, subU, subF in HM. cbn [ph_u ph_f Nat.leb] in HM.
  destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & _ & M10).
  assert (Etp1 : tp1 = []).
  { destruct tp1 as [|p tp1']; [reflexivity|]. exfalso. destruct (M8 p (or_introl eq_refl)) as [_ [[X _]|[X _]]]; discriminate X. }
  subst tp1. cbn [app length Z.of_nat] in M7, M10. subst tp.
  cbn [umem] in HR. fold T in HR. destruct HR as (L1 & L2 & L3).
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.RebuildQI.init_rebuild CST XGL HCST HXGL A rb r tp0 tp0 md0 md HA Hini).
  - exact L1.
  - intros z Hz. pose proof (L2 z Hz) as D. change (exists b, view segs (rm r) z = Some b). destruct (view segs (rm r) z) as [b|]; [exists b; reflexivity | contradiction].
  - exact HRM.
  - exact L3.
  - apply (model_inv_fields A (initA A) tp0 md0 md); try reflexivity; try assumption. clear -M10. lia.
  - eapply bandtp_mono; [|exact HB0]. intros z _ Hd. change (view segs (rm r) z <> None). change (view segs (rm rb) z <> None) in Hd.
    assert (D : ZI T z \/ ~ ZI T z) by (unfold ZI; clear; lia).
    destruct D as [D|D]; [exact (L2 z D) | rewrite (L1 z D); exact Hd].
Qed.

Lemma JRf_init : ltac2:(tb__ "0|0|
S18S8S2fQ40A1A1S8S33A1S32S35VA;VKc;Vrb;Vtp0;Vmd0;SeR4R3R2R1AaS82S69VA;A1VKc;Vc;Vnv;R5R4R3R2A8F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md HJ. pose proof HJ as (HFz & HK' & _).
  pose proof HE as ((HRQ & E158 & E148 & Hroom) & HA & Htp & _ & _ & Hnv & Htop & Hcnt & _). destruct HFz as [Fw Fl].
  fold nv in Hnv, Hcnt, E158, E148, Hroom. fold c in E158, E148, Hroom.
  split.
  - split; [exact (proj1 (u_rebuild r tp tr md HJ))|]. split; [exact HK'|].
    split; [unfold tp_ok in *; cbn [aa_geom initA]; rewrite <- (Fw 24%positive) by lia; exact Htp|].
    split; [unfold top_high in *; cbn [aa_geom initA]; rewrite <- (Fw 10%positive) by lia; rewrite <- (Fw V_DEPTH) by (unfold V_DEPTH; lia); exact Htop|].
    destruct HRQ as (E151 & E152 & E155 & E156). unfold rigidQ. cbn [aa_geom initA].
    rewrite <- (Fw 151%positive), <- (Fw 152%positive), <- (Fw 155%positive), <- (Fw 156%positive) by lia. exact (conj E151 (conj E152 (conj E155 E156))).
  - unfold rfacts. cbn zeta. split; [exact Hnv|]. split; [reflexivity|].
    split; [rewrite <- (Fw 12%positive) by lia; unfold nv; symmetry; apply Z_to_bv_bv_unsigned|].
    split; [unfold V_CLS; rewrite <- (Fw 158%positive) by lia; exact E158|]. split; [unfold V_SIZE; rewrite <- (Fw 148%positive) by lia; exact E148|].
    change (SegQ_wf2.cls_of (initA A) c) with (cst_of A nv).
    split; [|exact Hroom]. unfold cnt_of in Hcnt. destruct (cs_cache (cst_of A nv)); [reflexivity | cbn [length] in Hcnt; lia].
Qed.

Definition ulinkR (r : valuation) : Prop := ltac2:(tb__ "0|7|
S2S7dVrb;Vr;A2S2S2fQ40M0A1M1S4S6aVT;S30G0R1A2M2A2A1S3S12S2fQ8A1M3A1M4S1aVr;R2A2S1aVrb;R2A2M5A3F_;Fa;G1S2S2bS68G2A2S2dG2S67A2A2S4S3G4G5S13G3A1M6A3A1S4S3G4S1aVr;R3A2G6A3A1F_;F_;Fa;A2A2").
Lemma JU_ulink : ltac2:(tb__ "0|0|
S18S8S2fQ40A1A1S8S33A1S32S35VA;VKc;Vrb;Vtp0;Vmd0;SeR4R3R2R1AaS8cR5A1F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md (HFz & _ & _ & HR & HRM). cbn [umem] in HR. fold T in HR. destruct HR as (L1 & L2 & _).
  assert (VR : forall (f : word -> option byte) z, 0 <= z < 2 ^ 64 -> (z < IMG_LO \/ IMG_HI <= z) -> view OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA f z = f (Z_to_bv 64 z)).
  { intros f z Hz Hoff. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.RebuildR.view_rm_off f z Hz Hoff). }
  split; [exact HFz|]. split.
  - intros a NZ. pose proof (bv_unsigned_in_range _ a) as Ha. unfold bv_modulus in Ha. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ha.
    rewrite <- (Z_to_bv_bv_unsigned 64 a).
    destruct (Z_lt_dec (bv_unsigned a) IMG_LO) as [H1|H1]; [|destruct (Z_le_dec IMG_HI (bv_unsigned a)) as [H2|H2]].
    + rewrite <- !(VR _ _ Ha (or_introl H1)). exact (L1 _ NZ).
    + rewrite <- !(VR _ _ Ha (or_intror H2)). exact (L1 _ NZ).
    + apply HRM. lia.
  - intros a Hb Hd. pose proof (bv_unsigned_in_range _ a) as Ha. unfold bv_modulus in Ha. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ha.
    assert (OFF : bv_unsigned a < IMG_LO \/ IMG_HI <= bv_unsigned a) by (unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, IMG_HI in *; right; lia).
    assert (E : Z_to_bv 64 (bv_unsigned a) = a) by apply Z_to_bv_bv_unsigned.
    pose proof (VR (rm rb) _ Ha OFF) as V1. pose proof (VR (rm r) _ Ha OFF) as V2. rewrite E in V1, V2.
    rewrite <- V2. rewrite <- V1 in Hd.
    assert (D : ZI T (bv_unsigned a) \/ ~ ZI T (bv_unsigned a)) by (unfold ZI; clear; lia).
    destruct D as [D|D]; [exact (L2 _ D) | rewrite (L1 _ D); exact Hd].
Qed.

Lemma post_init : ltac2:(tb__ "0|2|
S0S18S8S2fQ40A1A1S74S3S0R4Vc;A3S8cR4A1S63S34S84R5R4S9SaS61S62A2M0SbS61S62S83S81S69VA;A1VKc;R6A3A4ScG0A1M1A3R3A6S63S34S84Vrb;R5S9G0SbS61S62S83S81VA;VKc;R7A3A4G1A3R4A6F_;F_;F_;Fw;Ftp;Fr;Fc0;").
Proof.
  intros c0 r tp w -> (HFz & RAW & BND) (L & JL & rho' & tp' & HIn & AV & Hsm & HJL).
  destruct HIn as [E|[]]. injection E as <- <-.
  exists L_rf, (JLRf A Kc c), rho', tp'. split; [left; reflexivity|].
  destruct HFz as [Fw Fl]. destruct AV as [Aw Al].
  split; [split; [intros i Hi; rewrite (Fw i) by (unfold NXR in Hi; lia); apply Aw; exact Hi | intros l; rewrite (Fl l); apply Al]|].
  split; [exact Hsm|].
  destruct HJL as (J1 & J2 & J3 & J4). unfold JLRf. split; [exact J1|]. split.
  - intros a NZ. rewrite Hini in NZ.
    rewrite (J2 a).
    + apply RAW. intros Z1. apply NZ. unfold refill_zone. cbn zeta. do 5 right. split; [reflexivity | exact Z1].
    + intros Z1. apply NZ. change (aa_cache_inited (initA A)) with true in Z1. change (aa_geom (initA A)) with (aa_geom A) in Z1.
      change (SegQ_wf2.cls_of (initA A) c) with (SegQ_wf2.cls_of A c) in Z1. unfold refill_zone in Z1 |- *. cbn zeta in Z1 |- *.
      destruct Z1 as [X|[X|[X|[X|[X|[X _]]]]]]; [left; exact X | right; left; exact X | do 2 right; left; exact X | do 3 right; left; exact X | do 4 right; left; exact X | discriminate X].
  - split; [intros a Hb Hd; apply J3; [exact Hb | apply BND; assumption] | intros l; rewrite (J4 l); symmetry; exact (Fl l)].
Qed.
End USTEPS.
End SpineMallocQU1.

