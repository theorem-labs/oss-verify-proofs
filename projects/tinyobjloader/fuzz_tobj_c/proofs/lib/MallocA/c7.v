(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c2.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require da dv.

(* [comment removed for export] *)
Module SpineMallocQ15.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sv"; "eval"; "sprop"; "SAlu"; "SLit"; "rm"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "phase"; "gh_new"; "ph0"; "frozen"; "ghosts"; "mlink"; "FAb"; "committed"; "ph_f"; "ph_u"; "releasedp"; "rlink"; "zoneR"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "of_nat"; "lt"; "le"; "ge"; "ltb"; "modulo"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Corelib.Init.Datatypes"; "list"; "length"; "bool"; "true"; "nil"; "pair"; "prod"; "cons"; "option"; "None"; "Some"; "nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "cs_free_array"; "cs_mapped_free_array"; "class_state"; "aa_cache_inited"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "entryRq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cst_of"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ7"; "popfacts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SpineMallocQ15"; "phFin"; "phUF3"; "phU3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP"; "ph_quiet"; "pbase"; "ph_set"; "PF"; "PU"; "ph_get"; "pord"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "NXR"; "L_rf"; "JLRf"; "refill_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineMallocQ13"; "phL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineMallocQ14"; "e16P"; "e32P"; "e48P"; "e_srcP"; "e24M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ6"; "exitT"; "finT"; "popT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "vMFA"; "beg1"; "beg2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SpineMallocQ15.ASMP"; "pieceT"; "fillT"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQ12"; "rup_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3"; "phK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ4";
"ph_setcnt"; "ph_setri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ5"; "JRfin"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR InvLaws PrimCredit GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RefillModelP RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQ12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.SpineMallocQ13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c2.SpineMallocQ14.
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
S40VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Notation JRp := (JR A Kc rb tp0 md0).
Let cs : class_state := ltac2:(tb__ "0|0|
S45VA;S37Q40S1Vrb;PcA2A2A2").
Variable LFm : axst.
Let CFM : axst := cFm LFm.
Hypothesis W_fm : ltac2:(tb__ "0|0|
ScS2cS8S42VCFM;A1A1S2dA3").
Hypothesis D_fm : ltac2:(tb__ "0|4|
ScS32S30S2aS30S2S2A2M0A1M1S2aS4A1M2A2M3A1S6cS42VLFm;A1S42VCFM;A1A2S34G3S2fG1G2S31G0S2fS2S2S71S5S6bS64S6Z40000A1A3A4S2eG0A1A3S2eS4A1A4A2A3").

Lemma famap_restate : ltac2:(tb__ "0|0|
S13S0S2aS36Q40A1A1SaS23S3bVcs;A1S21Z4S20S22S2bS9S3aVcs;A1A2A1S14VA;Vrb;A2A2A2A2VTR;S11SbS12VA;VKc;Vrb;Vtp0;Vmd0;R5A6VCFM;R4R3A5R2A2VTR;S11SbS12VA;VKc;Vrb;Vtp0;Vmd0;R6A6VLFm;R5R4A5R3A2F_;F_;FQ;Ftp;Fr;Fph;").
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
S74S73S72S5bVph;Vnew;A2Vk;A2A1A1").

Lemma zone_Fin_in : ltac2:(tb__ "0|1|
S39S0S13S9S47R4R3A2S37Q40S1R4PcA2A2S9S46R1A1S9S45R7R2A2S3cSeScS13R6S4fA3ScS13R6S4eA3A2ScS13R7S4eA3S23S3bR3A1S21Z4S20S22S2bS9S3aR3A1A2A1S14RaR9A2M0A2A2A2F_;S1fRaR9S4dR8G0S4bR4A1A3R7A4S5aS3eRbA1S2dR5R4R8A5F_;F_;F_;Tcs;Tc;Tnv;F_;Fz;FphX;Frb;FA;").
Proof.
  intros A rb phX z PF nv c cs HX HLT HZ. destruct PF as (NP & _). fold nv c cs in NP.
  assert (ENP : needs_populate c cs = true) by (unfold needs_populate; apply Z.ltb_lt; exact NP).
  assert (ENW : rf_new c cs = gh_new A rb) by (unfold rf_new, gh_new; fold nv c cs; reflexivity).
  unfold refill_zone. cbn zeta. rewrite ENW. unfold zoneR in HZ. fold nv c cs in HZ. unfold U0, F0, FAb, PCE, gh_nf in HZ. fold nv c cs in HZ.
  destruct HX as [-> | ->]; unfold phFin, phU3, phUF3, ph_setri, ph_setcnt, phK, phL, ph_set, ph0, revealedp, releasedp in HZ; cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb] in HZ.
  - destruct HZ as [[_ X]|[[_ X]|[[X _]|[[X _]|[[X _]|[X|[[_ X]|[_ X]]]]]]]]; try discriminate X.
    + right; right; right; left. split; [exact ENP|]. right; left. exact X.
    + right; right; right; left. split; [exact ENP|]. left. exact X.
    + right; right; right; left. split; [exact ENP|]. right; right. clear -X. lia.
    + right; left. exact X.
    + left. exact X.
    + right; right; left. exact X.
  - specialize (HLT eq_refl).
    assert (EGR : rf_grows c cs = true) by (unfold rf_grows; rewrite ENP, ENW; cbn [andb]; apply Z.ltb_lt; exact HLT).
    destruct HZ as [[_ X]|[[_ X]|[[_ X]|[[_ X]|[[X _]|[X|[[_ X]|[_ X]]]]]]]].
    + right; right; right; left. split; [exact ENP|]. right; left. exact X.
    + right; right; right; left. split; [exact ENP|]. left. exact X.
    + right; right; right; right; left. split; [exact EGR|]. right. exact X.
    + right; right; right; right; left. split; [exact EGR|]. left. exact X.
    + right; right; right; left. split; [exact ENP|]. right; right. clear -X. lia.
    + right; left. exact X.
    + left. exact X.
    + right; right; left. exact X.
Qed.

Section ASMP.
Variables (W : list ulink) (st : ustop).

Variables (LP CP2C RU LF0 LFm CFM RF LF1 : axst) (LJP XLP X4P LJM XLM X4M : axst).

Definition headT : Prop := ltac2:(tb__ "0|1|
S39S43S0S2aS36Q40A1A1M0S28SaSaOF_;F_;S48R5R1A2S44R6A1S0S0G0SaS40RcRaR9R8VW;Vst;R4A7S47RdRbA2S0RaS11SbS12RfReRdRcRbS15A6VCP2C;R1R5A5R4A2Fr';F_;R9S11SbS12ReRdRcRbRaS15A6VLP;R5R4A5R3A2F_;F_;FQ;Ftp;Fr;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition pieceT (p : piece) (eb : sv) (C0 RX : axst) : Prop := ltac2:(tb__ "0|6|
S39S43S0S2aS36Q40M0A1A1M1S28SaSaOF_;F_;S48R5R1A2S44R6A1S0S40R9R7R6R5VW;Vst;R1A7S13ScS35S55Vp;R1A2U0A3S56Vp;R2A2S50R3A1S0S16RdR1A2S17R10ReR2A3ScS9S37G0S3R3Veb;A2A2S51R11RfVp;A3A3F_;F_;Fr;SdS24S20S3fS3eRfA1A1M2Z100000000A2S51RfRdVp;A3M3A2SdS24S20G3Z40000M4A2S20G2Z2000000000A2A2ScS9S27G3Z10000A2Z0A3A2A2G1S28S18R12R10RfReR8R2R1A7S25S6eR2R3A2M5G4A2F_;Fmd;Ftp;G1S28S18R13R11R10RfS52Vp;U1R9A3R2R1A7S25G5Z8000A2F_;Fmd;Ftp;S0G1SaS0G1R12S11SbS12R17R16R15R14R13S52Vp;U3RdA3A6VRX;R2R1A5R3A2Ftp';Fr';R11S11SbS12R16R15R14R13R12RcA6VC0;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;F_;F_;F_;F_;F_;Fph;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition midT : Prop := ltac2:(tb__ "0|4|
S39S43S0S2aS36Q40M0A1A1M1S28SaSaOF_;F_;S48R5R1A2S44R6A1S0S40R9R7R6R5VW;Vst;R1A7S47RaR8A2S13S0G1SaS45RfS37G0S1RdPcA2A2A2S3cSfS23S3bR1A1S21Z4M2S20S22S2bS9S3aR1A1A2A1S14R10ReA2A2A2A2A1S0RdS11SbS12R12R11R10RfReR7A6M3VLF0;R1R5A5R4A2Fr';F_;S23S3bR2A1S21G2S20S22S2bS9S3aR2A1A2A1S14R11RfA2A2A2A2S0ReS11SbS12R13R12R11R10RfR8A6VLFm;R1R6A5R5A2Fr';F_;RdS11SbG3VRU;R6R5A5R4A2F_;F_;Tcs;FQ;Ftp;Fr;Fph;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition fmT : Prop := ltac2:(tb__ "0|2|
S39S43S0S2aS36Q40M0A1A1M1S28SaSaOF_;F_;S48R5R1A2S44R6A1S0S40R9R7R6R5VW;Vst;R1A7S47RaR8A2S13S0G1SaS45RfS37G0S1RdPcA2A2A2S3cS23S3bR1A1S21Z4S20S22S2bS9S3aR1A1A2A1S14R10ReA2A2A2A2RcS11SbS12R11R10RfReRdR6A6VCFM;R5R4A5R3A2RdS11SbS12R12R11R10RfReR7A6VLFm;R6R5A5R4A2F_;F_;Tcs;FQ;Ftp;Fr;Fph;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition runT (C L : axst) : Prop := ltac2:(tb__ "0|2|
S39S43S0S2aS36Q40A1A1M0S28SaSaOF_;F_;S48R5R1A2S44R6A1S13S0G0SaS0R8S11SbS12RdRcRbRaR9R5A6M1VL;R1R3A5R2A2Fr';R8S11SbG1VC;R4R3A5R2A2F_;FQ;Ftp;Fr;Fph;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").
Definition fillT (LH LJ : axst) : Prop := ltac2:(tb__ "0|7|
S39S43S0S2aS36Q40M0A1A1M1S28SaSaOF_;F_;S48R5R1A2S44R6A1S0S40R9R7R6R5VW;Vst;R1A7S47RaR8A2S13S50R1A1S9S6fSdS24Z0R2A2S24R2S14RfRdA2A2A2S1eR10ReS5bR5R3A2S70SbS7ReA1A2R2A5S9SdS24S20S19R12R10A2M2S21Z4M3S22S2bS9S3aS45R12S37G0S1R10PcA2A2A2A1A2A1M4A2A2R1A2S23R1S20G2S21G3S20G4S14R12R10A2M5A2A2A2A2A2SfScS32S36Q8A1M6A1R5R2A1S33G6A1A3A1F_;Fz;F_;F_;Fm;Fi;S0G1SaS0RdS11SbS12R12R11R10RfReS5bR7G5A2A6VLJ;R1R3A5R2A2Fr';RdS11SbS12R12R11R10RfReR7A6VLH;R4R3A5R2A2F_;FQ;Ftp;Fr;F_;F_;Fph;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;").

Hypothesis H_head : headT.
Hypothesis H_pu : ltac2:(tb__ "0|0|
S69S54S65VCP2C;VRU;A4").
Hypothesis H_mid : midT.
Hypothesis H_fm : fmT.
Hypothesis H_pf : ltac2:(tb__ "0|0|
S69S53S66VCFM;VRF;A4").
Hypothesis H_run : runT RF LF1.
Hypothesis H_fillP : fillT LF0 LJP.
Hypothesis H_fillM : fillT LF1 LJM.
Hypothesis H_popP : ltac2:(tb__ "0|0|
S63VW;Vst;VLJP;VXLP;S5fA5").
Hypothesis H_popM : ltac2:(tb__ "0|0|
S63VW;Vst;VLJM;VXLM;S5fA5").
Hypothesis H_exitP : ltac2:(tb__ "0|0|
S61VW;Vst;VXLP;VX4P;S5cS64S5dS5eA8").
Hypothesis H_exitM : ltac2:(tb__ "0|0|
S61VW;Vst;VXLM;VX4M;S5cS60S5dS5eA8").
Hypothesis H_finP : ltac2:(tb__ "0|0|
S62VW;Vst;VX4P;A3").
Hypothesis H_finM : ltac2:(tb__ "0|0|
S62VW;Vst;VX4M;A3").

Lemma pop_tail : ltac2:(tb__ "0|6|
S41S41S41S41S2S6aR5R4A2S63VW;Vst;R5R4S5fA5S61VW;Vst;R5R4S5cR3S5dS5eA8S62VW;Vst;R5A3S39S43S0S2aS36Q40M0A1M1A1M2S28SaSaOF_;F_;S67R5R1A2S44R6A1S0S40R9R7R6R5VW;Vst;R1A7S47RaR8A2S13ScS2cS3dRcA1S2dA3S50R2A1ScS2cS1aS1cR3A1A1S2dA3S37G0S1RdPcA2A2S9S46R1A1S9S45R11R2A2S3cS22S2bS9S3aR1A1A2A1S9S14R13R11A2S9S3bR3A1S9SeScS2cS1dS1bRaA1A1S2dA3S24S21Z4M3S20R3R2A2A2R1A2A2S0S16R15R1A2S17R18R16R2A3ScG1S3R3R1eA2S38G0S2cS9L_;S26R5S21G3S20R7R6A2A2A2S20R5Z40000A2R5X2cx2A2A3F_;F_;Fr;S0G2S2aS29A1M4S28S12R1bR1aR19R18R17S4dR10R8S4bRbA1A3R4R3R2R1AaS68S4cR1cRcA2R5R4R2A4F_;Fmd;Ftr;Ftp';Fr;S0G2S49S0G2G4S28S75R1fR1eR1dS4dR14RcS4bRfA1A3R4R3R2R1A8SdS6dS57R8R5A3R6R8R7R5R4R3R2A6A2F_;Fmd;Ftr;Ftp';Fr';S0G2R19S11SbS12R1eR1dR1cR1bR1aR13A6R27R2R1A5S4aSbS57R6R5S31S30S41S49A2M5S2fS41S49S58R4A4S2eG5A1A3A5A2Ftp;Fr;F_;FJLq;FtpQ;FrhoQ;F_;F_;F_;Tmfa;Tnew;Tnf;Tcs;Tc;Tnv;F_;F_;F_;FphX;FPF;FHE;Frho;FHKc;FKIT;FTR;Fmd0;Ftp0;Frb;FKc;FA;F_;F_;F_;F_;Fe24;FX4;FXL;FLJ;FLH;").
Proof.
  intros LH LJ XL X4 e24 HFI HPO HEX HFN A Kc rb tp0 md0 TR KIT HKc rho HE PF phX Hini PQ PCU nv c cs nf new mfa HARM HE24 HREB rhoQ tpQ JLq HPOST r tp.
  pose proof (trd_ok Kc TR KIT) as KT.
  pose proof (P_csR A rb tp0 md0 W st rho HE PF) as (X1 & X2 & X3 & X5 & X6 & X7 & LP' & HIDS). cbn zeta in X1, X2, X3, X5, X6, X7, LP', HIDS. fold nv c cs nf new in X1, X2, X3, X5, X6, X7, LP', HIDS.
  destruct (pop_geo A rb tp0 md0 W st rho HE PF) as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & _). fold nv c cs nf new mfa in C1, S1, AU0, MU1, N4, K1, KN, NF0, MF1, MF2, MF0.
  set (k := kchunks c) in *. set (fP := faP c cs) in *.

  apply (HFI A Kc rb tp0 md0 TR KT HKc rho HE PF phX PQ).
  { intros i m Hi HR z Hz. apply (P_HDEF A rb tp0 md0 W st rho HE PF (phL phX i) m); [exact HARM | exact HR | exact Hz]. }
  intros r1.

  apply (HPO A Kc rb tp0 md0 TR KT HKc rho HE (phL phX new) (conj eq_refl (conj eq_refl eq_refl)) fP).
  - intros i m Hi HR idx Hidx. apply (P_HSRC A rb tp0 md0 W st rho HE PF (phK (phL phX new) i) m); [reflexivity | cbn [ph_pop phK]; fold nv c k in Hi; clear -Hi K1; lia | exact HR | exact Hidx].
  - fold nv c k. rewrite LP'. clear -KN NF0. lia.
  - rewrite LP'. clear -MF1 MF2 N4. lia.
  - intros _. unfold gh_nf. fold nv c cs nf new. rewrite LP'. cbn [ph_fill phL]. clear -NF0 N4. lia.
  - exact HIDS.
  - fold nv c cs k. rewrite LP'. exact X1.
  - fold nv c k. exact (P_HSRCP A rb tp0 md0 W st rho HE PF).
  - intros r2.

    apply (HEX A Kc rb tp0 md0 TR KT HKc rho HE (phK (phL phX new) k) (conj eq_refl (conj eq_refl eq_refl))).
    + intros _. unfold gh_nf. fold nv c cs nf new. cbn [ph_fill phK phL]. clear -NF0 N4 MF1 MF2. lia.
    + exact Hini.
    + intros r' HFz HGh. exact (P_HRIv A rb tp0 md0 W st rho HE PF e24 r' HFz HGh (HE24 r' HFz HGh)).
    + intros r3.

      exact (HFN A Kc rb tp0 md0 TR KIT HKc rho HE (phFin phX new k) rhoQ tpQ JLq HREB (zoneR_dec A rb _) HPOST r3 tp).
Qed.

Theorem refill_populate : ltac2:(tb__ "0|4|
S39S43S9S0S2aS36Q40M0A1A1M1SaSaOF_;F_;S67R5R1A2S44R6A1ScS2cS3dR8A1S2dA3S4aSbS57R6R5S31S30S41S49A2M2S2fS41S49S58S59R9R8R7A3A4S2eG2A1A3A5SaS28S40RbR8R7R1VW;Vst;R8A7S47RcR9A2S13SeScS13R1S4fA3ScS13R1S4eA3A2S37G0S1RcPcM3A2A2S9S46R1A1S9S45R11R2A2S3cS10ScS13R5S4eA3S23S3bR1A1S21Z4S20S22S2bS9S3aR1A1A2A1S14R12RfA2A2A2A2A2S0G1S2aS29A1S28S12R17R16R14R13RdS4dRaS14R17R14A2S4bR7A1A3R4R3R2R1AaS68S4cR18R8A2R5R4R2A4F_;Fmd;Ftr;Ftp';Fr;F_;Tcs;Tc;Tnv;F_;FphX;FPF;FHE;Fmd0;S28S0ScS9RbS46S37G0S1RaG3A2A2A1A3S40ReRbRaR3VW;Vst;RbA7RaS11SbS12RfReRcRbR4S15A6VLP;R3RbA5R6A2F_;F_;Fr';Fmd0;F_;TQ;F_;FHKc;FKIT;FTR;Ftp;Frho;Fc0;FKc;FA;").
Proof.
  intros A Kc c0 rho tp TR KIT HKc Hini Q HREB md0 r0 E0 HE.
  pose proof (trd_ok Kc TR KIT) as KT. set (rb := rho) in *.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (H_head A Kc rb tp md0 TR KT HKc rho r0 tp Q HE). intros PF r1.
  set (nv := bv_unsigned (rw rb 12%positive)) in *. set (c := cls_of nv) in *. set (cs := cst_of A nv) in *.
  destruct (pop_geo A rb tp md0 W st rho HE PF) as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & _).
  fold nv c cs in C1, S1, AU0, MU1, N4, K1, KN, NF0, MF1, MF2, MF0, FAr.
  destruct (pop_credit A rb tp md0 W st rho HE PF) as (CR & _). fold nv c cs in CR.
  assert (G12 : ag_spacebeg (aa_geom A) mod 65536 = 0) by (unfold cfacts in CF; cbn zeta in CF; destruct CF as (_ & _ & _ & _ & _ & (X & _) & _); exact X).
  assert (MU18 : cs_mapped_user cs mod 262144 = 0) by (unfold cfacts in CF; cbn zeta in CF; fold nv c cs in CF; destruct CF as (_ & _ & (X & _) & _); exact X).

  apply (H_pu A Kc rb tp md0 TR KT HKc rho HE ph0 eq_refl eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
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
    apply (H_mid A Kc rb tp md0 TR KT HKc rho HE PF phU3 r2 tp2 Q); cbn zeta; fold nv c cs.
    +
      intros NLT r3.
      apply (pop_tail LF0 LJP XLP X4P vMFA H_fillP H_popP H_exitP H_finP A Kc rb tp md0 TR KIT HKc rho HE PF phU3 Hini (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))) eq_refl).
      * right. fold nv c cs. clear -NLT. lia.
      * intros r HFz HGh. fold nv c cs. replace (cs_mapped_free_array cs <? _) with false by (symmetry; apply Z.ltb_ge; clear -NLT; lia).
        destruct HGh as (_ & _ & Q222 & _). fold nv c cs in Q222. exact Q222.
      * fold nv c. apply (HREB md0 HE PF phU3 (or_introl eq_refl)). cbn zeta. fold nv c cs. split; [intros X; discriminate X | intros X; contradiction].
      * apply (fin_post A Kc rb tp (phFin phU3 (gh_new A rb) (kchunks c)) c0 E0 Hini).
        intros z HZ. apply (zone_Fin_in A rb phU3 z PF (or_introl eq_refl)); [intros X; discriminate X | exact HZ].
    +
      intros LT r3.
      apply (H_fm A Kc rb tp md0 TR KT HKc rho HE PF phU3 r3 tp2 Q LT).
      pose proof (P_newZ A rb) as ENZ. fold nv c cs in ENZ.
      destruct (RefillModelP.P_famap c cs _ C1 (proj1 (entry_pure A rb tp md0 W st rho HE PF)) (proj2 (proj2 (proj2 (entry_pure A rb tp md0 W st rho HE PF))))
                  ltac:(rewrite ENZ; exact LT)) as (_ & FCM).
      pose proof (facap_room c C1) as FRM.
      apply (H_pf A Kc rb tp md0 TR KT HKc rho HE phU3 eq_refl I (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
      * intros r HFz HGh. exact (beg2_val A rb r CF (entry_rigids _ _ _ _ _ _ _ _ HE HFz) HGh).
      * cbn [pbase]. unfold F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c cs.
        split; [clear -C1 NF0 MF1; lia|]. split; [clear -C1 FCM FRM; lia|].
        rewrite Z.add_mod, (Z.add_mod (ag_spacebeg (aa_geom A) + c * 2 ^ 32)), (Z.add_mod (ag_spacebeg (aa_geom A))), G12 by (clear; lia).
        destruct (proj1 (Z.mod_divide (cs_mapped_free_array cs) 262144 ltac:(clear; lia)) MF0) as [q Hq]. rewrite Hq.
        replace (c * 2 ^ 32) with (c * 65536 * 65536) by (clear; lia). replace (q * 262144) with (q * 4 * 65536) by (clear; lia). rewrite !Z_mod_mult. reflexivity.
      * intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF phU3 t md HM) as X. cbn [phU3 ph_set ph0 ph_u ph_f committed revealedp Nat.leb] in X.
        fold nv c cs in CR. replace (cs_mapped_free_array cs <? _) with true in CR by (symmetry; apply Z.ltb_lt; exact LT). clear -X CR. lia.
      * intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF (ph_set OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP.PF 1 phU3) t md HM) as X. cbn [phU3 ph_set ph0 ph_u ph_f committed revealedp Nat.leb] in X.
        fold nv c cs in CR. replace (cs_mapped_free_array cs <? _) with true in CR by (symmetry; apply Z.ltb_lt; exact LT). clear -X CR. lia.
      * intros r4 tp4. fold phUF3.
        apply (H_run A Kc rb tp md0 TR KT HKc phUF3 r4 tp4 Q). intros r5.
        apply (pop_tail LF1 LJM XLM X4M e24M H_fillM H_popM H_exitM H_finM A Kc rb tp md0 TR KIT HKc rho HE PF phUF3 Hini (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))) eq_refl).
        -- left. reflexivity.
        -- intros r HFz HGh. fold nv c cs. replace (cs_mapped_free_array cs <? _) with true by (symmetry; apply Z.ltb_lt; exact LT).
           destruct HGh as (_ & _ & Q222 & _). fold nv c cs in Q222. unfold e24M, vMFA. cbn [eval]. rewrite Q222. apply bv_eq.
           rewrite add_val, !u64_lit by (clear -NF0 MF1 MF2; lia). rewrite Z.mod_small by (clear -NF0 MF1 MF2; lia). reflexivity.
        -- fold nv c. apply (HREB md0 HE PF phUF3 (or_intror eq_refl)). cbn zeta. fold nv c cs. split; [intros _; exact LT | intros _; reflexivity].
        -- apply (fin_post A Kc rb tp (phFin phUF3 (gh_new A rb) (kchunks c)) c0 E0 Hini).
           intros z HZ. apply (zone_Fin_in A rb phUF3 z PF (or_intror eq_refl)); [intros _; exact LT | exact HZ].
Qed.
End ASMP.
End SpineMallocQ15.

(* [comment removed for export] *)
Module DrainG5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "sprop"; "ss_next"; "reg_sv"; "ss_facts"; "ss_objs"; "valuation"; "rm"; "swf"; "sprop_below"; "ss_lenient"; "SAlu"; "cell"; "smatch"; "ss_pc"; "sstate"; "sv_below"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "nil"; "prod"; "option"; "Some"; "pair"; "app"; "false"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "beg2"; "rMS"; "sMS"; "cX"; "idx_rot"; "nobj"; "relM"; "vMFA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1"; "JDg"; "entryG"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "ALU_ADD"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF"; "O_riX"; "frozenD"; "ri_hasD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2"; "SKELG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "drain_zone"; "O_cntD"; "O_dstD"; "dst_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "F_sp_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9"; "O_piece"; "O_shp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG5.GFIN"; "JDfinG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel"; "drainA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "ageom"; "class_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10"; "a2_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11"; "a0_e"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 SMGlue PrimCredit PrimCreditLaws SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillBits DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ci.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.RebuildD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ci.DrainG3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Section GPIECE.
Variable n : Z.
Variables (A : AA) (Kc : KcA) (c : Z) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Hypothesis HE : ltac2:(tb__ "0|0|
S3aVn;VA;Vc;Vrb;Vtp0;Vmd0;A6").
Notation JDp := (JDg A Kc c rb tp0 md0).
Let B : Z := F0d A c.

Variable F : nat.
Variables (C0 : axst) (LX LM : leafA).
Let CX : axst := ltac2:(tb__ "0|0|
S2bS6VLX;A1S28A2").
Let G1 : axst := commit_post CX beg2 262144.
Let EM : axst := la_state LM.
Let CMR : axst := cMr EM.
Let CMC : axst := cMc EM beg2.
Let DM : axst := dMSf CMC.
Let RM : axst := rotM DM.
Hypothesis R_x : ltac2:(tb__ "0|1|
S0S22S1cS5A1M0A1S7S31VF;S1fS30Z7050cS20S30A1A3VC0;S1eA5S23G0S1fS5VLX;S20S5A1A3A2A3").
Hypothesis LN_0 : ltac2:(tb__ "0|0|
S0S1dS15S4VC0;A1A1S26A3").
Hypothesis NX_0 : ltac2:(tb__ "0|0|
S0S1dS32Pf0SdS4VC0;A1A1A2S1eA3").
Hypothesis W_x : ltac2:(tb__ "0|0|
S0S1dS13S4VCX;A1A1S1eA3").
Hypothesis D_x : ltac2:(tb__ "0|4|
S0S22S21S1cS21S9S9A2M0A1M1S1cScA1M2A2M3A1S40S4S6VLX;A1A1S4VCX;A1A2S23G3S24G1G2S1fG0S24S9S9S64S28A1S28A4S20G0A1A3S20ScA1A4A2A3").
Hypothesis SK_x : ltac2:(tb__ "0|1|
S0S1cS21S21S9S9A2S9A2M0A1S35SaG0S4dS10S4VCX;A1A1A4S45Vn;S20SaA1A2A3").
Hypothesis XF_x : ltac2:(tb__ "0|0|
S4eScS4aSfS4VCX;A1A1A3").
Hypothesis XX_x : ax_X CX = [].
Hypothesis NX_x : ltac2:(tb__ "0|0|
S0S1dS32Pf0SdS4VCX;A1A1A2S1eA3").
Hypothesis IC_x : ltac2:(tb__ "0|0|
S0S22S3bA1S58S31S19S4VCX;A1A1A2S23S3bS3dA2A3").
Hypothesis R17_x : ltac2:(tb__ "0|0|
S0S9SeS4VCX;A1Z11A2SbZdeA1A3").
Hypothesis R10_x : ltac2:(tb__ "0|0|
S0S9SeS4VCX;A1ZaA2S28A3").
Hypothesis BEL_x : ltac2:(tb__ "0|0|
S0S1dS1bSdS4VCX;A1A1S28A2S1eA3").
Hypothesis R11_x : ltac2:(tb__ "0|0|
S0S9SeS4VCX;A1ZbA2SbZ40000A1A3").
Hypothesis R12_x : ltac2:(tb__ "0|0|
S0S9SeS4VCX;A1ZcA2SbZ3A1A3").
Hypothesis R13_x : ltac2:(tb__ "0|0|
S0S9SeS4VCX;A1ZdA2SbZ32A1A3").
Hypothesis R14_x : ltac2:(tb__ "0|0|
S0S9SeS4VCX;A1ZeA2SbZffffffffffffffffA1A3").
Hypothesis R15_x : ltac2:(tb__ "0|0|
S0S9SeS4VCX;A1ZfA2SbZ0A1A3").
Hypothesis R_m : ltac2:(tb__ "0|1|
S0S22S1cS5A1M0A1S7S31VF;S1fS30Zde378S20S30A1A3VG1;S1eA5S23G0S1fS5VLM;S20S5A1A3A2A3").
Hypothesis LN_g : ltac2:(tb__ "0|0|
S0S1dS15S4VG1;A1A1S26A3").
Hypothesis NX_g : ltac2:(tb__ "0|0|
S0S1dS32Pf0SdS4VG1;A1A1A2S1eA3").
Hypothesis SK_m : ltac2:(tb__ "0|1|
S0S1cS21S21S9S9A2S9A2M0A1S35SaG0S4dS10S4VEM;A1A1A4S45Vn;S1fSaS4bS28A1S20SaA1A3A2A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S4eScS4aSfS4VEM;A1A1A3").
Hypothesis XX_m : ax_X EM = [].
Hypothesis W_mr : ltac2:(tb__ "0|0|
S0S1dS13S4VCMR;A1A1S1eA3").
Hypothesis D_mr : ltac2:(tb__ "0|4|
S0S22S21S1cS21S9S9A2M0A1M1S1cScA1M2A2M3A1S40S4VEM;A1S4VCMR;A1A2S23G3S24G1G2S1fG0S24S9S9S63S28A1SbZ8000A1A4S20G0A1A3S20ScA1A4A2A3").
Hypothesis W_mc : ltac2:(tb__ "0|0|
S0S1dS13S4VCMC;A1A1S1eA3").
Hypothesis E_ms : ltac2:(tb__ "0|1|
S0S22S1cSaA1M0A1S5aVCMC;S3eS2aVCMC;A1A3S23G0S29VCMC;A1A2A3").
Hypothesis CHK_ms : ltac2:(tb__ "0|0|
S0S1dS59VCMC;S3eS2aVCMC;A1S29VCMC;A1S35S5S8S6S3fA4A5S1eA3").
Hypothesis NF_ms : ltac2:(tb__ "0|0|
S0S1dS32S55SdS4VCMC;A1A1A2S1eA3").
Hypothesis NX_ms : ltac2:(tb__ "0|0|
S0S1dS32Pf0SdS4VCMC;A1A1A2S1eA3").
Hypothesis FBC_ms : ltac2:(tb__ "0|1|
S0S1dS4fScS14SdS4VCMC;A1M0A1A1SfG0A1A3S1eA3").
Hypothesis FBT_ms : ltac2:(tb__ "0|0|
S0S1dS4fScS14SdS4S62VCMC;S2aVCMC;A1S29VCMC;A1A3A1A1A1SfS4VCMC;A1A1A3S1eA3").
Hypothesis ND_r : ltac2:(tb__ "0|0|
S0S1dS56S2cVDM;A1A1S1eA3").
Hypothesis NO_r : (1 <= nobj DM)%nat.
Hypothesis OB_r : ltac2:(tb__ "0|1|
S0S1cSaA1S10S4VRM;A1A1M0S25SaS36SaS50S2dVDM;A1U2A2G0A3S1fSaS4bS28A1S1fSaS4cS28A1S20SaA1A3A3A3A3").

Theorem g_piece_full : ltac2:(tb__ "0|1|
S11S1cS33Q40A1A1M0S54S11G0VTR;S41S31S39VA;VKc;Vc;Vrb;Vtp0;Vmd0;U3A7S2eVDM;A1R2R1A5R3A2Ftp';Fr';VTR;S41S31S39VA;VKc;Vc;Vrb;Vtp0;Vmd0;U0A7VC0;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC.
  apply (jg_run A Kc c rb tp0 md0 TR KIT HKc F [0x7050c] C0 [LX] 0%nat r tp Q R_x LN_0 NX_0).
  intros L r1 [<-|[]] _.
  apply (jg_restate A Kc c rb tp0 md0 TR KIT (la_state LX) (ax_S CX) _ _ 0%nat r1 tp Q W_x D_x ltac:(apply Pos.eqb_refl)).
  { intros tr md (HFz & _) _. split; [|constructor]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    destruct (g_evals n A c rb tp0 md0 HE r1 HFz) as (_ & _ & _ & _ & EB & _). fold B in EB.
    destruct (g_piece n A c rb tp0 md0 HE) as (_ & _ & HB3 & _). fold B in HB3.
    apply (a0_val r1 beg2 B EB).
    destruct (proj1 (Z.mod_divide B 65536 ltac:(clear; lia)) HB3) as [q Hq]. rewrite Hq. replace (q * 65536) with (q * 16 * 4096) by (clear; lia). apply Z_mod_mult. }
  change (ax_setS (la_state LX) (ax_S CX)) with CX.
  apply (g_commit n A Kc c rb tp0 md0 TR KIT HKc HE CX SK_x XF_x XX_x NX_x IC_x R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x r1 tp Q).
  fold G1.
  exact (g_map n A Kc c rb tp0 md0 TR KIT HKc HE F G1 LM R_m LN_g NX_g SK_m XF_m XX_m W_mr D_mr W_mc E_ms CHK_ms NF_ms NX_ms FBC_ms FBT_ms ND_r NO_r OB_r r1 tp Q HC).
Qed.
End GPIECE.

Lemma drain_zone_dec : ltac2:(tb__ "0|1|
S60S30S61S30S3S46R4R3R2R1A4M0S2G0A1A2Fz;Fcs;Fc;FG;").
Proof.
  intros G c cs z. unfold drain_zone. cbv zeta.
  match goal with |- (?P1 \/ ?P2 \/ ?P3 \/ (?g = true /\ (?P4 \/ ?P5))) \/ _ =>
    assert (D1 : P1 \/ ~ P1) by lia; assert (D2 : P2 \/ ~ P2) by lia; assert (D3 : P3 \/ ~ P3) by lia;
    assert (D4 : P4 \/ ~ P4) by lia; assert (D5 : P5 \/ ~ P5) by lia;
    assert (TT : true = true) by reflexivity; assert (FT : false = true -> False) by discriminate;
    destruct g; tauto end.
Qed.

Section GFIN.
Variable n : Z.
Variables (A : AA) (Kc : KcA) (c : Z) (rb : valuation) (tp0 : list word) (md0 : Model).
Hypothesis HE : ltac2:(tb__ "0|0|
S3aVn;VA;Vc;Vrb;Vtp0;Vmd0;A6").
Notation JDp := (JDg A Kc c rb tp0 md0).
Let G : ageom := aa_geom A.
Let T : Z := ag_thread G.
Let SB : Z := ag_spacebeg G.
Let cs : class_state := SegQ_wf2.cls_of A c.
Let nf : Z := Z.of_nat (length (cs_free_array cs)).
Let mfa : Z := cs_mapped_free_array cs.
Let B : Z := F0d A c.

Definition JDfinG : jpredA := ltac2:(tb__ "0|7|
S11S1cS33Q40M0A1M1A1S1cS38A1S37S1S5fVKc;S5cVA;Vc;A2R4R3R2R1A6S1G1S2S46VG;Vc;Vcs;S34G0R1A2M2A4A1S0S22S33Q8A1M3A1M4S12R6R2A2S12Vrb;R2A2M5A3F_;Fa;S1G1S1S65S5eG2A2S66G2S5dA2A2S2S0G4G5S27G3A1M6A3A1S2S0G4S12R7R3A2G6A3A1F_;F_;Fa;S43Vrb;R4A2A2A2A2Lmd;Ltr;Ltp';Lr';").

Lemma d_finalG : ltac2:(tb__ "0|4|
S1aS1cSaA1M0S1cS17A1S11S1cS33Q40A1A1S1cS38A1M1S51S37S37S0G0S10R9A1S25SaR8S1fSaS47Vn;A1M2S1fSaS42R7A1S1fSaS48Vn;S49Vn;A1A2S20SaA1A3M3A3A3A3A3S0S1dS44Vn;S16S3cS2fSbZ40000A1A3R8A3S1eA3S18S31R8RbS24G1S52R6S53R5R4A2A4A4S39VA;VKc;Vc;Vrb;Vtp0;Vmd0;U3R9R8R7R4AbS5bS57RaS1fSaG2S1fSaS42RbA1G3A3A3R7A3R9R8R5A4F_;F_;F_;F_;FmdJ;Fmd;Fms;Ftr;Ftp;Fr;FcellsR;FK;FS;").
Proof.
  intros S K cellsR r tp tr ms md mdJ HO HRI Hsm (HFz & HK & HM & HR).
  destruct (g_nums n A c rb tp0 md0 HE) as (C1 & EK & K1 & EMC & T1 & T2 & TG & TI & S1 & S2 & TS & TB & NF0 & NF1 & NF2 & MM & MC).
  fold G in T1, T2, TG, TI, S1, S2, TS, TB. fold T in T1, T2, TI, TS, TB. fold SB in S1, S2, TS. fold cs in NF0, NF1, NF2, MM, MC. fold nf in NF0, NF1, NF2. fold mfa in NF1, NF2, MM, MC.
  destruct (g_evals n A c rb tp0 md0 HE r HFz) as (EB & ERI & _ & EDS & _ & _ & V221 & V222). fold G in EB, ERI, EDS. fold T in EB. fold SB in ERI, EDS. fold cs in EDS, V221, V222. fold nf in EDS, V221. fold mfa in V222.
  destruct (g_piece n A c rb tp0 md0 HE) as (HB1 & HB2 & HB3 & FAv). fold G in HB1, HB2, FAv. fold SB in HB1, HB2, FAv. fold B in HB1, HB2, HB3.
  destruct (piece_numsG n A c rb tp0 md0 HE) as (B0 & B1 & BM & Q1 & Q2 & Q3). fold B in B0, B1, BM, Q1, Q2, Q3.
  destruct (g_pure n A c rb tp0 md0 HE) as (_ & _ & HFULL & _ & _ & EMF). fold cs in HFULL, EMF. fold mfa in EMF.
  destruct (g_credit n A c rb tp0 md0 HE) as (CEQ & PB0 & _ & _).
  pose proof HE as (HA & Htp & Htop & HRG & DF & HWF & _). destruct DF as (Hini & _ & _ & _ & HGR & E158 & _ & _ & _ & E223 & E224 & _ & ECH).
  fold cs in HGR, E223, E224, ECH.
  destruct HR as [R1 R2].
  set (R := [O_cntD n; O_riX cellsR; O_dstD n (dst_cells n)]) in *. set (r3 := rho_absorb r R ms).
  set (pce := T + 208 + 80 * c) in *. set (ri := region_info SB c) in *. set (fa := free_array SB c) in *.
  assert (EBv : B = fa + mfa) by reflexivity.
  assert (RIv : ri = SB + 137438953472 + c * 128) by (unfold ri, region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  assert (RC : obj_range r (O_cntD n) = (pce, pce + 4)) by (unfold O_cntD; rewrite obj_range_mk by lia; rewrite EB; f_equal; lia).
  assert (RR : obj_range r (O_riX cellsR) = (ri, ri + 128)) by (unfold O_riX; rewrite obj_range_mk by lia; rewrite ERI; f_equal; lia).
  assert (RD : obj_range r (O_dstD n (dst_cells n)) = (fa + 4 * nf, fa + 4 * nf + 4 * n)) by (unfold O_dstD; rewrite obj_range_mk by lia; rewrite EDS; f_equal; lia).

  assert (ZEQ : forall z, drain_zone G c cs z <-> (pce <= z < pce + 4 \/ ri <= z < ri + 128 \/ fa + 4 * nf <= z < fa + 4 * nf + 4 * n
                                                  \/ B <= z < B + 262144 \/ Sh B <= z < Sh B + 32768)).
  { intros z. unfold drain_zone. cbv zeta. fold T SB. fold ri fa nf mfa. rewrite HGR, EK. rewrite <- EBv. unfold pce, kFreeArrayMapSize. split.
    - intros [X|[X|[X|(_ & [X|X])]]]; [left; lia | right; right; left; lia | right; left; exact X | right; right; right; left; exact X | right; right; right; right; exact X].
    - intros [X|[X|[X|[X|X]]]]; [left; lia | right; right; left; exact X | right; left; lia | right; right; right; split; [reflexivity | left; exact X]
                                | right; right; right; split; [reflexivity | right; exact X]]. }
  assert (INR : forall a : word, in_ranges r R a <-> (pce <= bv_unsigned a < pce + 4 \/ ri <= bv_unsigned a < ri + 128 \/ fa + 4 * nf <= bv_unsigned a < fa + 4 * nf + 4 * n)).
  { intros a. unfold in_ranges, R. split.
    - intros (o & [<-|[<-|[<-|[]]]] & Hr); [rewrite RC in Hr | rewrite RR in Hr | rewrite RD in Hr]; cbn [fst snd] in Hr; tauto.
    - intros [X|[X|X]]; [exists (O_cntD n); split; [left; reflexivity | rewrite RC; exact X]
                        | exists (O_riX cellsR); split; [right; left; reflexivity | rewrite RR; exact X]
                        | exists (O_dstD n (dst_cells n)); split; [right; right; left; reflexivity | rewrite RD; exact X]]. }
  assert (RAW : forall a : word, ~ drain_zone G c cs (bv_unsigned a) -> rm r3 a = rm rb a).
  { intros a Ha. unfold r3. rewrite rm_absorb_out by (intros X; apply Ha; apply ZEQ; apply INR in X; clear -X; tauto).
    apply R1. intros X. apply Ha. apply ZEQ. apply (zoneG_3 A c) in X. fold B in X. clear -X. tauto. }

  assert (ZIMG : forall z, drain_zone G c cs z -> (z < 65536 \/ 6578176 <= z) /\ 0 <= z < 2 ^ 64).
  { intros z Hz. apply ZEQ in Hz. unfold pce in Hz. rewrite RIv, FAv in Hz. clear -Hz C1 T1 T2 TG TI S1 S2 NF0 NF1 NF2 MC K1 B0 B1 HB1 Q2 Q3. lia. }

  set (vE := view segs (rm rb)). set (v3 := view segs (rm r3)).
  assert (VO : forall z, ~ drain_zone G c cs z -> v3 z = vE z).
  { intros z Hz. unfold v3, vE, view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|reflexivity].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    unfold rd_of. rewrite RAW by (rewrite u64_lit by lia; exact Hz). reflexivity. }
  assert (ABS : forall o, In o R -> forall cl, In cl (ob_cells o) -> forall j, (j < Z.to_nat (c_width cl))%nat ->
            v3 (bv_unsigned (eval r (ob_base o)) + soff r (c_off cl) + Z.of_nat j) = Some (nth j (enc_bytes (Z.to_nat (c_width cl)) (eval r (SymState.c_val cl))) (Z_to_bv 8 0))
            /\ obj_lo_of r o <= soff r (c_off cl) /\ soff r (c_off cl) + c_width cl <= obj_hi_of r o).
  { intros o Ho cl Hcl j Hj. destruct (absorb_obj r S tr ms md K R o Hsm HO Ho) as (B0' & AS & _).
    destruct (AS cl Hcl) as (B1' & B2' & ASb). specialize (ASb j Hj). split; [|exact (conj B1' B2')].
    unfold v3. rewrite view_in; [exact ASb|]. clear -B0' B1' B2' Hj. cbv zeta in B0'. lia. }
  assert (PRS : forall z, drain_zone G c cs z -> exists b, v3 z = Some b).
  { intros z Hz. pose proof (ZIMG z Hz) as (_ & Z64). apply ZEQ in Hz.
    assert (D3 : (pce <= z < pce + 4 \/ ri <= z < ri + 128 \/ fa + 4 * nf <= z < fa + 4 * nf + 4 * n)
                 \/ ~ (pce <= z < pce + 4 \/ ri <= z < ri + 128 \/ fa + 4 * nf <= z < fa + 4 * nf + 4 * n)) by (clear; lia).
    destruct D3 as [IN3|OUT3].
    - assert (X : exists o off, In o R /\ (ob_dflt o = DUnknown) /\ z = bv_unsigned (eval r (ob_base o)) + off /\ obj_lo_of r o <= off < obj_hi_of r o).
      { unfold obj_lo_of, obj_hi_of. destruct IN3 as [X|[X|X]].
        - exists (O_cntD n), (z - pce). split; [left; reflexivity|]. split; [reflexivity|]. cbn [ob_base ob_lo ob_hi O_cntD]. rewrite EB, !soff_lit_small by lia. unfold pce in *. lia.
        - exists (O_riX cellsR), (z - ri). split; [right; left; reflexivity|]. split; [reflexivity|]. cbn [ob_base ob_lo ob_hi O_riX]. rewrite ERI, !soff_lit_small by lia. lia.
        - exists (O_dstD n (dst_cells n)), (z - (fa + 4 * nf)). split; [right; right; left; reflexivity|]. split; [reflexivity|]. cbn [ob_base ob_lo ob_hi O_dstD]. rewrite EDS, !soff_lit_small by lia. lia. }
      destruct X as (o & off & Ho & Hd & -> & Hoff). destruct (absorb_obj r S tr ms md K R o Hsm HO Ho) as (_ & _ & AP & _).
      destruct (AP (or_introl Hd) off Hoff) as [x Hx]. exists x. unfold v3. rewrite view_in by exact Z64. exact Hx.
    - assert (ZG : zoneG A c 3%nat z) by (apply (zoneG_3 A c); fold B; clear -Hz OUT3; tauto).
      pose proof (R2 z ZG) as D.
      assert (E3 : v3 z = view segs (rm r) z).
      { unfold v3, r3. apply view_absorb_out. intros o [<-|[<-|[<-|[]]]]; [rewrite RC | rewrite RR | rewrite RD]; cbn [fst snd]; clear -OUT3; tauto. }
      rewrite E3. destruct (view segs (rm r) z) as [b|]; [exists b; reflexivity | contradiction]. }

  assert (CELL : forall o off w v (e : sv), In o R -> In (mkCell (SLit off) (Z.of_nat w) e) (ob_cells o) -> - 2 ^ 62 <= off < 2 ^ 62 -> eval r e = Z_to_bv 64 v ->
            cell_ok v3 (mkACell (bv_unsigned (eval r (ob_base o)) + off) w v)).
  { intros o off w v e Ho Hcl Hoff Ee j Hj. cbn [c_addr c_w RtCells.c_val] in Hj |- *.
    destruct (ABS o Ho _ Hcl j ltac:(cbn [c_width]; rewrite Nat2Z.id; exact Hj)) as (X & _). cbn [c_off c_width SymState.c_val] in X.
    rewrite soff_lit_small in X by lia. rewrite Nat2Z.id, Ee in X. exact X. }
  repeat (apply andb_prop in HRI as [HRI ?]).
  repeat match goal with X : cell_insv _ _ _ _ = true |- _ => apply cell_insv_In in X end.
  assert (Ekeep : drain_keep c cs = Z.to_nat n) by (unfold drain_keep; rewrite EK; lia).
  destruct HFz as [Fw Fl].
  assert (HDM : drain_mem A c vE v3).
  { unfold drain_mem. cbv zeta. fold G. fold T SB. change (nthZ (aa_cls A) c cs_empty) with cs. fold nf. fold ri fa. replace (T + 208 + 80 * c) with pce by reflexivity.
    split; [exact VO|]. split; [exact PRS|].
    split.
    { rewrite Ekeep, Z2Nat.id by lia. replace pce with (bv_unsigned (eval r (ob_base (O_cntD n))) + 0) by (cbn [ob_base O_cntD]; rewrite EB; unfold pce; lia).
      apply (CELL (O_cntD n) 0 4%nat n (SLit n)); [left; reflexivity | left; reflexivity | lia | reflexivity]. }
    split.
    { intros i Hi. rewrite EK in Hi. rewrite Ekeep.
      replace (fa + 4 * (nf + Z.of_nat i)) with (bv_unsigned (eval r (ob_base (O_dstD n (dst_cells n)))) + 4 * Z.of_nat i) by (cbn [ob_base O_dstD]; rewrite EDS; lia).
      apply (CELL (O_dstD n (dst_cells n)) (4 * Z.of_nat i) 4%nat _ (SExt true 32 (vCH i))); [right; right; left; reflexivity | | lia |].
      - cbn [ob_cells O_dstD]. unfold dst_cells. apply (proj1 (in_rev _ _)). apply in_map_iff. exists i. split; [reflexivity | unfold idxs; apply in_seq; lia].
      - cbn [eval vCH]. rewrite <- (Fw (Pos.of_nat (170 + i))) by lia. rewrite (ECH i Hi).
        apply sext32_small.
        pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & PC). pose proof (PC c C1) as PCc. unfold class_repr in PCc.
        destruct PCc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & N2 & N3 & _ & _ & _ & _ & _ & N7 & _). change (nthZ (aa_cls A) c cs_empty) with cs in N2, N3, N7.
        assert (HIN : In (nth (Z.to_nat n + i) (cs_cache cs) 0) (cs_free_array cs ++ cs_cache cs)).
        { apply in_or_app; right. apply nth_In. rewrite <- (Nat2Z.id (length (cs_cache cs))), HFULL, EMC. lia. }
        destruct (N7 _ HIN) as (X1 & _ & X3). unfold kCompactPtrScale in X3. rewrite Z.shiftl_mul_pow2 in X3 by lia. change (2 ^ 4) with 16 in X3.
        destruct (cap_facts c C1) as (SZ & _). unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in N3. clear -X1 X3 N2 N3 SZ. lia. }
    assert (RIC : forall off w v (e : sv), In (mkCell (SLit off) (Z.of_nat w) e) cellsR -> - 2 ^ 62 <= off < 2 ^ 62 -> eval r e = Z_to_bv 64 v -> cell_ok v3 (mkACell (ri + off) w v)).
    { intros off w v e Hcl Hoff Ee. replace ri with (bv_unsigned (eval r (ob_base (O_riX cellsR)))) by (cbn [ob_base O_riX]; exact ERI).
      apply (CELL (O_riX cellsR) off w v e); [right; left; reflexivity | exact Hcl | exact Hoff | exact Ee]. }
    assert (V223 : rw r 223%positive = Z_to_bv 64 (cs_allocated_user cs)) by (rewrite <- (Fw 223%positive) by lia; exact E223).
    assert (V224 : rw r 224%positive = Z_to_bv 64 (cs_mapped_user cs)) by (rewrite <- (Fw 224%positive) by lia; exact E224).
    unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted.
    split; [apply (RIC 0 8%nat 0 (SLit 0)); [assumption | lia | reflexivity]|].
    split.
    { rewrite EK. apply (RIC 16 8%nat (nf + n) (SAlu ALU_ADD vNF (SLit n))); [assumption | lia |].
      unfold vNF. cbn [eval]. rewrite V221. apply bv_eq. rewrite add_val, !u64_lit by lia. apply Z.mod_small. lia. }
    split.
    { rewrite EMF. apply (RIC 24 8%nat _ (SAlu ALU_ADD vMFA (SLit 262144))); [assumption | lia |].
      unfold vMFA. cbn [eval]. rewrite V222. apply bv_eq. rewrite add_val, !u64_lit by lia. apply Z.mod_small. lia. }
    split; [apply (RIC 32 8%nat _ vAU); [assumption | lia | unfold vAU; cbn [eval]; exact V223]|].
    split; [apply (RIC 40 8%nat 0 (SLit 0)); [assumption | lia | reflexivity]|].
    split; [apply (RIC 48 8%nat _ vMU); [assumption | lia | unfold vMU; cbn [eval]; exact V224]|].
    split; [apply (RIC 56 8%nat 0 (SLit 0)); [assumption | lia | reflexivity]|].
    apply (RIC 68 1%nat 0 (SLit 0)); [assumption | lia | reflexivity]. }

  pose proof HA as (HG0 & _ & _ & _ & HM0 & HI3 & HB0).
  unfold mlinkG in HM. cbn zeta in HM. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10). fold B in M5, M6, M8.
  assert (HFULL' : Z.of_nat (length (cs_cache (nthZ (aa_cls A) c cs_empty))) = max_count c) by exact HFULL.
  assert (HMD : model_inv segs (drainA A c) tp mdJ).
  { rewrite M7.
    assert (LH : B < B + 262144) by (clear; lia).
    assert (SL : ag_spacebeg (aa_geom A) <= B) by (fold G SB; clear -HB1; lia).
    assert (SH : B + 262144 <= ag_spacebeg (aa_geom A) + kSpaceSize + 4096) by (fold G SB; rewrite kSpaceSize_val; clear -HB2; lia).
    assert (SBH : HIGH_SHADOW_END <= ag_spacebeg (aa_geom A)) by (fold G SB; unfold HIGH_SHADOW_END; exact S1).
    assert (HBP : forall p, In p tp1 -> band_page (bv_unsigned p)).
    { intros p Hp. destruct (M8 p Hp) as [_ [_ (j & Hj & Ej)]]. rewrite Ej. unfold band_page. right. unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG. clear -Hj Q2 Q3. lia. }
    assert (HPAID : paid mdJ (tp1 ++ tp0) + prim_credit (drainA A c) <= budget_boundD A).
    { rewrite <- M7. unfold committed, revealedp in M10. cbn [Nat.leb] in M10. clear -PB0 M10 CEQ. lia. }
    exact (model_inv_sub2 A (drainA A c) tp0 tp1 md0 mdJ false true B (B + 262144) B (B + 262144) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
             HI3 HWF LH LH SL SH SL SH SBH M1 M2 M3 M4 M5 M6 HBP HPAID HM0). }
  assert (HBT : bandtp_inv v3 tp).
  { rewrite M7. apply (bandtp_grow v3 tp0).
    - eapply bandtp_mono; [|exact HB0]. intros z _ Hd. change InvLaws.segsA with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA in Hd. fold vE in Hd.
      destruct (drain_zone_dec G c cs z) as [ZI|ZO]; [destruct (PRS z ZI) as [b Hb]; rewrite Hb; discriminate | rewrite (VO z ZO); exact Hd].
    - intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [|left; exact Hp]. right. intros _ z Hz.
      destruct (M8 p Hp) as [_ [_ (j & Hj & Ej)]]. rewrite Ej in Hz. unfold PG in Hz.
      apply PRS. apply ZEQ. right; right; right; right. clear -Hz Hj. lia. }
  assert (RMI : forall a, IMG_LO <= a < IMG_HI -> rm r3 (Z_to_bv 64 a) = rm rb (Z_to_bv 64 a)).
  { intros a Ha. apply RAW. unfold IMG_LO, IMG_HI in Ha. rewrite u64_lit by lia. intros X. destruct (ZIMG a X) as (Bx & _). clear -Ha Bx. lia. }
  destruct (drain_rebuild [] [] cst_ok_nil xgl_ok_nil A rb r3 tp0 tp md0 mdJ c HA C1 Hini HFULL' HDM RMI HMD HBT) as (HAQ & _).
  assert (RW3 : forall i, rw r3 i = rw r i) by (intros i; reflexivity).
  split.
  { split; [exact HAQ|]. split; [exact HK|].
    split; [unfold tp_ok in *; change (aa_geom (drainA A c)) with (aa_geom A); rewrite RW3, <- (Fw 24%positive) by lia; exact Htp|].
    split; [unfold top_high in *; change (aa_geom (drainA A c)) with (aa_geom A); rewrite !RW3, <- (Fw 10%positive), <- (Fw V_DEPTH) by (unfold V_DEPTH; lia); exact Htop|].
    destruct HRG as (Q1' & Q2' & Q3' & Q4'). unfold rigidQ. change (aa_geom (drainA A c)) with (aa_geom A).
    rewrite !RW3, <- (Fw 151%positive), <- (Fw 152%positive), <- (Fw 155%positive), <- (Fw 156%positive) by lia. exact (conj Q1' (conj Q2' (conj Q3' Q4'))). }
  split; [exact RAW|].
  split.
  { intros a Ha Hd. destruct (drain_zone_dec G c cs (bv_unsigned a)) as [ZI|ZO]; [|rewrite (RAW a ZO); exact Hd].
    destruct (PRS _ ZI) as [b Hb]. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in Ha.
    unfold v3 in Hb. rewrite (view_rm_hi (rm r3) (bv_unsigned a)) in Hb by (unfold IMG_LO, IMG_HI; pose proof (urange a); lia).
    rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
  split; [intros i Hi; rewrite RW3; exact (Fw i Hi) | intros l; exact (Fl l)].
Qed.
End GFIN.
End DrainG5.

(* [comment removed for export] *)
Module DrainG6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "sym_runA"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "ss_next"; "valuation"; "reg_sv"; "swf"; "ss_facts"; "ss_objs"; "ss_lenient"; "SAlu"; "sprop_below"; "cell"; "ss_pc"; "sv_below"; "@Corelib.Init.Datatypes"; "list"; "nil"; "true"; "bool"; "cons"; "prod"; "pair"; "Some"; "option"; "false"; "app"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "beg2"; "rMS"; "sMS"; "nobj"; "vMFA"; "cX"; "idx_rot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1"; "JDg"; "entryG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "NXD"; "JLD"; "JD"; "O_cntD"; "O_dstD"; "dst_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG"; "L_dh_g"; "Pre_dh_g"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4"; "cG0"; "cCD"; "mid_okG"; "XFG"; "rupD_e"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2"; "SKELG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "F_sp_high"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG6.GCHAIN"; "leaf_okG"; "run_okG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9"; "O_piece"; "O_shp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF"; "O_riX"; "ri_hasD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10"; "a2_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11"; "a0_e"; "@Stdlib.ZArith.BinInt.Z"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 SMGlue PrimCredit PrimCreditLaws SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillBits DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ci.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.RebuildD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ci.DrainG3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bu.DrainG4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.DrainG5.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Section GCHAIN.
Variable n : Z.

Definition leaf_okG (L : axst) : Prop := ltac2:(tb__ "0|3|
S2S1aS17A1M0G0S2S5aS5aS1S0S1aS1fSaSaA2M1A1S8VL;A1S1bG1A1A3S1S0S1aSbA1S13S3VL;A1A1M2S24SbS42SbS53S2bVL;A1U3A2G2A3S1eSbS3cVn;A1S1eSbS64R2A1S1eSbS3dVn;S3eVn;A1A2S1bSbA1A3A3A3A3A3S1S0S1dS65Vn;S15S55S2cSdZ40000A1A3R2A3S1cA3S1S0S1dS9VL;S3fVn;A1R1A3S1cA3S0S1dS5bR1S39A2S1cA3A2A2A2A2Ls;A2LcellsR;A2").

Definition run_okG (F : nat) (cuts : list Z) (next_ok : axst -> Prop) (E : axst) : Prop := ltac2:(tb__ "0|2|
S1S0S1dS14S3VE;A1M0A1S23A3S1S0S1dS37Pf0SeG0A1A2S1cA3S2S1aS5A1M1G1S1S0S22G1A1S7S26VF;Vcuts;VE;S1cA5S21G1R1A2A3S5S49S5R1R2A3Vnext_ok;S6R2A1A1F_;FL';A2Lleaves;A2A2A2").

Variables (A : AA) (Kc : KcA) (c : Z) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRokD Kc TR.
Hypothesis HKc : Kc_ok Kc.
Hypothesis HE : ltac2:(tb__ "0|0|
S36Vn;VA;Vc;Vrb;Vtp0;Vmd0;A6").
Notation JDp := (JDg A Kc c rb tp0 md0).
Notation KT := (trd_ok Kc TR KIT).
Let Q : assn := ltac2:(tb__ "0|1|
S30S26S39Vrb;Vtp0;S1eS1fS4S2fA2M0S20S4S2fS3fVn;A1S3aVA;VKc;Vc;A3A4S1bG0A1A3A5").

Lemma d_leafG : ltac2:(tb__ "0|0|
S4SfS1aS38Q40A1A1S5cR3A1VTR;S33S26S35VA;VKc;Vc;Vrb;Vtp0;Vmd0;U3A7R4R3R2A5VQ;A2F_;Ftp;Fr;FL;").
Proof.
  intros L r tp (cellsR & s & HX & HO & HRI & HENT & HSID).
  set (R := [O_cntD n; O_riX cellsR; O_dstD n (dst_cells n)]) in *.
  apply (tr_cut Kc TR KT valuation _ (fun r3 => SPA segs (JDfinG A Kc c rb) L r3 tp) Q).
  { intros [tr [ms md]] Hw. exists (rho_absorb r R (vms md tp ms)).
    apply (SPA_rebase_J (JDp 3%nat) (JDfinG A Kc c rb) r L _ R tp tr ms md HX HO Hw).
    intros Hsm HJ. exact (d_finalG n A Kc c rb tp0 md0 HE _ _ cellsR r tp tr (vms md tp ms) (vmd md) md HO HRI Hsm HJ). }
  intros r3.
  apply (tr_pre Kc TR KT (SPA segs (JDfinG A Kc c rb) (L_dh_g n) (rho_sub r3 s) tp)).
  { intros w Hw. apply (SPA_entails_J (JDfinG A Kc c rb) (JDfinG A Kc c rb) L (L_dh_g n) s r3 tp w HENT); [|exact Hw].
    intros (J1 & J2 & J3 & J4). pose proof (rho_sub_agree s NXD r3 HSID) as AG.
    split; [|split; [exact J2 | split; [exact J3|]]].
    - eapply (K0_stable Kc (drainA A c) HKc); [|apply mat_equiv_refl | exact J1]. eapply agree_below_le; [|exact AG]. unfold QNPRE, NXD. lia.
    - destruct J4 as [F1 F2]. destruct AG as (Aw & Al & _). split; [intros i Hi; rewrite (F1 i Hi); apply Aw; unfold NXD; lia | intros l; rewrite (F2 l); apply Al]. }
  apply (tr_done Kc TR KIT). intros w [Hsm (J1 & J2 & J3 & J4)].
  exists (L_dh_g n), (JLD A Kc c), (rho_sub r3 s), tp.
  split; [left; reflexivity|]. split; [destruct J4 as [F1 F2]; split; [intros i Hi; apply F1; unfold NXD in Hi; lia | exact F2]|].
  split; [exact Hsm|]. unfold JLD. split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. intros l. symmetry. exact (proj2 J4 l).
Qed.

Lemma g_runs : ltac2:(tb__ "0|1|
S25S1aS27A1S4OF_;S4S25SfS1aS38Q40A1A1M0S5dR7R6R5R4A4S4SfG0R9R3A1VTR;S33S26S35VA;VKc;Vc;Vrb;Vtp0;Vmd0;R8A7R4R3R2A5VQ;A2F_;Ftp';Fr';FL';VTR;S33S26S35VA;VKc;Vc;Vrb;Vtp0;Vmd0;R5A7R6R4R3A5VQ;A2F_;F_;Ftp;Fr;Ff;FE;Fnext_ok;Fcuts;FF;").
Proof.
  intros F cuts next_ok E f r tp (HLN & HNL & leaves & HRUN & HNEXT) HC.
  apply (jg_run A Kc c rb tp0 md0 TR KT HKc F cuts E leaves f r tp Q HRUN HLN HNL).
  intros L' r' HIn _. exact (HC (la_state L') r' tp (HNEXT L' HIn)).
Qed.

Variable F : nat.
Variables (L1 L2 LX LM : leafA).
Let C0 : axst := cFm (la_state L2).
Let CX : axst := ltac2:(tb__ "0|0|
S2dS6VLX;A1S28A2").
Let G1 : axst := commit_post CX beg2 262144.
Let EM : axst := la_state LM.
Let CMR : axst := cMr EM.
Let CMC : axst := cMc EM beg2.
Let DM : axst := dMSf CMC.
Let RM : axst := rotM DM.
Let RL : axst := relM DM.

Hypothesis W_0 : ltac2:(tb__ "0|0|
S0S1dS11S3S44Vn;A1A1A1S1cA3").
Hypothesis D_0 : ltac2:(tb__ "0|4|
S0S22S1fS1aS1fSaSaA2M0A1M1S1aScA1M2A2M3A1S43S3S40Vn;A1A1S3S44Vn;A1A1A2S21G3S20G1G2S1bG0A1S47A4A2A3").
Hypothesis R_1 : ltac2:(tb__ "0|1|
S0S22S1aS5A1M0A1S7S26VF;S1eS27Z3ef90S1bS27A1A3S44Vn;A1S1cA5S21G0S1eS5VL1;S1bS5A1A3A2A3").
Hypothesis LN_1 : ltac2:(tb__ "0|0|
S0S1dS14S3S44Vn;A1A1A1S23A3").
Hypothesis M_1 : ltac2:(tb__ "0|0|
S46VF;U8S1eS27Z3f270S1bS27A1A3S4S0S4R1S6VL2;A1A3LL';S6VL1;A1A5").

Hypothesis W_fm : ltac2:(tb__ "0|0|
S0S1dS11S3VC0;A1A1S1cA3").
Hypothesis D_fm : ltac2:(tb__ "0|4|
S0S22S1fS1aS1fSaSaA2M0A1M1S1aScA1M2A2M3A1S43S3S6VL2;A1A1S3VC0;A1A2S21G3S20G1G2S1eG0S20SaSaS48Vn;A1S15S55S2cSdZ40000A1A3A4S1bG0A1A3S1bScA1A4A2A3").

Hypothesis R_x : ltac2:(tb__ "0|1|
S0S22S1aS5A1M0A1S7S26VF;S1eS27Z7050cS1bS27A1A3VC0;S1cA5S21G0S1eS5VLX;S1bS5A1A3A2A3").
Hypothesis LN_0 : ltac2:(tb__ "0|0|
S0S1dS14S3VC0;A1A1S23A3").
Hypothesis NX_0 : ltac2:(tb__ "0|0|
S0S1dS37Pf0SeS3VC0;A1A1A2S1cA3").
Hypothesis W_x : ltac2:(tb__ "0|0|
S0S1dS11S3VCX;A1A1S1cA3").
Hypothesis D_x : ltac2:(tb__ "0|4|
S0S22S1fS1aS1fSaSaA2M0A1M1S1aScA1M2A2M3A1S43S3S6VLX;A1A1S3VCX;A1A2S21G3S20G1G2S1eG0S20SaSaS68S28A1S28A4S1bG0A1A3S1bScA1A4A2A3").
Hypothesis SK_x : ltac2:(tb__ "0|1|
S0S1aS1fS1fSaSaA2SaA2M0A1S41SbG0S52S13S3VCX;A1A1A4S4bVn;S1bSbA1A2A3").
Hypothesis XF_x : ltac2:(tb__ "0|0|
S49ScS4dS12S3VCX;A1A1A3").
Hypothesis XX_x : ax_X CX = [].
Hypothesis NX_x : ltac2:(tb__ "0|0|
S0S1dS37Pf0SeS3VCX;A1A1A2S1cA3").
Hypothesis IC_x : ltac2:(tb__ "0|0|
S0S22S56A1S62S26S18S3VCX;A1A1A2S21S56S57A2A3").
Hypothesis R17_x : ltac2:(tb__ "0|0|
S0SaS10S3VCX;A1Z11A2SdZdeA1A3").
Hypothesis R10_x : ltac2:(tb__ "0|0|
S0SaS10S3VCX;A1ZaA2S28A3").
Hypothesis BEL_x : ltac2:(tb__ "0|0|
S0S1dS19SeS3VCX;A1A1S28A2S1cA3").
Hypothesis R11_x : ltac2:(tb__ "0|0|
S0SaS10S3VCX;A1ZbA2SdZ40000A1A3").
Hypothesis R12_x : ltac2:(tb__ "0|0|
S0SaS10S3VCX;A1ZcA2SdZ3A1A3").
Hypothesis R13_x : ltac2:(tb__ "0|0|
S0SaS10S3VCX;A1ZdA2SdZ32A1A3").
Hypothesis R14_x : ltac2:(tb__ "0|0|
S0SaS10S3VCX;A1ZeA2SdZffffffffffffffffA1A3").
Hypothesis R15_x : ltac2:(tb__ "0|0|
S0SaS10S3VCX;A1ZfA2SdZ0A1A3").
Hypothesis R_m : ltac2:(tb__ "0|1|
S0S22S1aS5A1M0A1S7S26VF;S1eS27Zde378S1bS27A1A3VG1;S1cA5S21G0S1eS5VLM;S1bS5A1A3A2A3").
Hypothesis LN_g : ltac2:(tb__ "0|0|
S0S1dS14S3VG1;A1A1S23A3").
Hypothesis NX_g : ltac2:(tb__ "0|0|
S0S1dS37Pf0SeS3VG1;A1A1A2S1cA3").
Hypothesis SK_m : ltac2:(tb__ "0|1|
S0S1aS1fS1fSaSaA2SaA2M0A1S41SbG0S52S13S3VEM;A1A1A4S4bVn;S1eSbS5eS28A1S1bSbA1A3A2A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S49ScS4dS12S3VEM;A1A1A3").
Hypothesis XX_m : ax_X EM = [].
Hypothesis W_mr : ltac2:(tb__ "0|0|
S0S1dS11S3VCMR;A1A1S1cA3").
Hypothesis D_mr : ltac2:(tb__ "0|4|
S0S22S1fS1aS1fSaSaA2M0A1M1S1aScA1M2A2M3A1S43S3VEM;A1S3VCMR;A1A2S21G3S20G1G2S1eG0S20SaSaS67S28A1SdZ8000A1A4S1bG0A1A3S1bScA1A4A2A3").
Hypothesis W_mc : ltac2:(tb__ "0|0|
S0S1dS11S3VCMC;A1A1S1cA3").
Hypothesis E_ms : ltac2:(tb__ "0|1|
S0S22S1aSbA1M0A1S32VCMC;S58S2aVCMC;A1A3S21G0S29VCMC;A1A2A3").
Hypothesis CHK_ms : ltac2:(tb__ "0|0|
S0S1dS31VCMC;S58S2aVCMC;A1S29VCMC;A1S41S5S4S6S59A4A5S1cA3").
Hypothesis NF_ms : ltac2:(tb__ "0|0|
S0S1dS37S60SeS3VCMC;A1A1A2S1cA3").
Hypothesis NX_ms : ltac2:(tb__ "0|0|
S0S1dS37Pf0SeS3VCMC;A1A1A2S1cA3").
Hypothesis FBC_ms : ltac2:(tb__ "0|1|
S0S1dS4aScS16SeS3VCMC;A1M0A1A1S12G0A1A3S1cA3").
Hypothesis FBT_ms : ltac2:(tb__ "0|0|
S0S1dS4aScS16SeS3S66VCMC;S2aVCMC;A1S29VCMC;A1A3A1A1A1S12S3VCMC;A1A1A3S1cA3").
Hypothesis ND_r : ltac2:(tb__ "0|0|
S0S1dS61S2eVDM;A1A1S1cA3").
Hypothesis NO_r : (1 <= nobj DM)%nat.
Hypothesis OB_r : ltac2:(tb__ "0|1|
S0S1aSbA1S13S3VRM;A1A1M0S24SbS42SbS53S2bVDM;A1U2A2G0A3S1eSbS5eS28A1S1eSbS5fS28A1S1bSbA1A3A3A3A3").

Hypothesis SK_c : ltac2:(tb__ "0|1|
S0S1aS1fS1fSaSaA2SaA2M0A1S41SbG0S52S13S3VRL;A1A1A4S4bVn;S1bSbA1A2A3").
Hypothesis XF_c : ltac2:(tb__ "0|0|
S49ScS4dS12S3VRL;A1A1A3").
Hypothesis XX_c : ax_X RL = [].
Hypothesis W_c : ltac2:(tb__ "0|0|
S0S1dS11S3S45Vn;VRL;A2A1A1S1cA3").
Hypothesis T_5 : ltac2:(tb__ "0|1|
S5dVF;S1eS27Z3f440S1bS27A1M0A3S46VF;U16S1eS27Z3ede4G0A3S5cA4S45Vn;VRL;A2A4").

Theorem drain_growth_chain : ltac2:(tb__ "0|0|
SfS1aS38Q40A1A1VTR;S33S26S35VA;VKc;Vc;Vrb;Vtp0;Vmd0;U0A7S40Vn;A1R2R1A5VQ;A2Ftp;Fr;").
Proof.
  intros r tp.

  apply (jg_restate A Kc c rb tp0 md0 TR KT (Pre_dh_g n) (ax_S (cG0 n)) _ _ 0%nat r tp Q W_0 D_0 ltac:(apply Pos.eqb_refl)).
  { intros tr md (HFz & _) _. split; [constructor | exact (xfg_holds n A c rb tp0 md0 HE r HFz)]. }
  change (ax_setS (Pre_dh_g n) (ax_S (cG0 n))) with (cG0 n).
  apply (jg_run A Kc c rb tp0 md0 TR KT HKc F [0x3ef90] (cG0 n) [L1] 0%nat r tp Q R_1 LN_1 ltac:(reflexivity)).
  intros L r1 [<-|[]] _.
  apply (g_mid n A Kc c rb tp0 md0 TR KT HKc HE F 8 [0x3f270] (fun L' => L' = la_state L2) (la_state L1) 0%nat r1 tp Q M_1).
  intros L' r2 tp2 ->.

  apply (jg_restate A Kc c rb tp0 md0 TR KT (la_state L2) (ax_S C0) _ _ 0%nat r2 tp2 Q W_fm D_fm ltac:(apply Pos.eqb_refl)).
  { intros tr md (HFz & _) _. split; [|constructor]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    exact (rupD_val n A c rb tp0 md0 HE r2 HFz). }
  change (ax_setS (la_state L2) (ax_S C0)) with C0.
  apply (g_piece_full n A Kc c rb tp0 md0 TR KT HKc HE F C0 LX LM R_x LN_0 NX_0 W_x D_x SK_x XF_x XX_x NX_x IC_x R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x
           R_m LN_g NX_g SK_m XF_m XX_m W_mr D_mr W_mc E_ms CHK_ms NF_ms NX_ms FBC_ms FBT_ms ND_r NO_r OB_r r2 tp2 Q).
  intros r3 tp3. fold RL.
  apply (g_carve_dst n A Kc c rb tp0 md0 TR KT HE RL r3 tp3 Q SK_c XF_c XX_c W_c).
  apply (g_runs F [0x3f440] (mid_okG F 22 [0x3ede4] leaf_okG) (cCD n RL) 3%nat r3 tp3 T_5).
  intros L5 r5 tp5 M5.
  apply (g_mid n A Kc c rb tp0 md0 TR KT HKc HE F 22 [0x3ede4] leaf_okG L5 3%nat r5 tp5 Q M5).
  intros L6 r6 tp6 M6. exact (d_leafG L6 r6 tp6 M6).
Qed.
End GCHAIN.

Definition chain_okG (n : Z) (F : nat) (L1 L2 LX LM : leafA) : Prop := ltac2:(tb__ "0|2|
S50S4eS27SfS1aS38Q40A1A1M0S54S34S34OF_;F_;S4cR6R1A2S4fR7A1S36Vn;R9R7R6R5R4A6SfG0R6S33S26S35RcRbRaR9R8R7U0A7S40Vn;A1R2R1A5S30S26S39R9R8S1eS1fS4S2fA2M1S20S4S2fS3fVn;A1S3aRcRbRaA3A4S1bG1A1A3A5A2Ftp;Fr;F_;F_;FKIT;FTR;Fmd0;Ftp0;Frb;Fc;FKc;FA;").

Section GTOP.
Variable n : Z.
Hypothesis CH : ltac2:(tb__ "0|2|
S50S4eS27SfS1aS38Q40A1A1M0S54S34S34OF_;F_;S4cR6R1A2S4fR7A1S36Vn;R9R7R6R5R4A6SfG0R6S33S26S35RcRbRaR9R8R7U0A7S40Vn;A1R2R1A5S30S26S39R9R8S1eS1fS4S2fA2M1S20S4S2fS3fVn;A1S3aRcRbRaA3A4S1bG1A1A3A5A2Ftp;Fr;F_;F_;FKIT;FTR;Fmd0;Ftp0;Frb;Fc;FKc;FA;").

Theorem drain_g : ltac2:(tb__ "0|1|
S4eS34S34OF_;F_;S4cR2R1A2S4fR3A1S50S27SfS1aS38Q40A1A1S69S51R4A1S63A2R8S33S26S3bVn;S1cR5R9R4A5S40Vn;A1R3R2A5S30S26S39R3R2S1eS1fS4S2fA2M0S20S4S2fS3fVn;A1S3aR5R9R4A3A4S1bG0A1A3A5A2F_;Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof.
  intros Kc TR KIT HKc A c rho tp HBUD.
  apply (tr_cutP Kc TR (trd_ok Kc TR KIT) Model _ (fun md0 => entryG n A c rho tp md0) (fun md0 => SPA segs (JDg A Kc c rho tp md0 0%nat) (Pre_dh_g n) rho tp)).
  { intros w Hw. exists (cfg_model (w_cfg w)). destruct Hw as [HsmA ((HAQ & HK & Htp & Htop & HRG) & DF)].
    split; [split; [exact HAQ|]; split; [exact Htp|]; split; [exact Htop|]; split; [exact HRG|]; split; [exact DF|]; split; [|exact HBUD];
            destruct w as [tr [ms md]]; exact (MI_ivs_wf segs _ _ (proj1 (proj2 HsmA)))|].
    split; [exact HsmA|]. unfold JDg. split; [split; intros; reflexivity|]. split; [exact HK|]. split.
    - unfold mlinkG, committed, revealedp, sub1. cbn [Nat.leb].
      repeat (split; [reflexivity|]). exists []. cbn [app length Z.of_nat]. split; [reflexivity|]. split; [intros p []|]. split; [lia | lia].
    - split; [intros a _; reflexivity | intros z Hz; exfalso; exact (zoneG_0 A c z Hz)]. }
  intros md0 HE. exact (CH A Kc c rho tp md0 TR KIT HKc HE rho tp).
Qed.
End GTOP.
End DrainG6.

(* [comment removed for export] *)
Module F0A_hbN_qsz.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sprop"; "sprop_below"; "sv"; "rm"; "ss_facts"; "ss_next"; "ss_objs"; "swf"; "valuation"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "div"; "lt"; "@Corelib.Init.Datatypes"; "andb"; "list"; "bool"; "nat"; "pair"; "prod"; "true"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_thread"; "aa_q_thread"; "ag_ctx"; "ag_spacebeg"; "sc_map_beg"; "sc_map_size"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert"; "hv_LR"; "hbvar_ok"; "hv_PT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states"; "O_qsz"; "F_qsz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "qsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_entry"; "ZUH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.F0A_hbN_qsz"; "ZD_qsz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.F0A_hbN_scan"; "hbnums"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_scand"; "FCHs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap"; "DUZh"; "JH2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones"; "zd_allb"; "zds_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "zdisjb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "kQuarantineCacheMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel"; "addo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop"; "with_obj"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_hbN_env F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require da.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.F0A_hbN_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cp.F0A_hbN_step OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_entry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c9.F0A_hbN_stepU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cw.F0A_hbN_scand OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.F0A_hbN_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.da.F0A_hbN_disj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cv.F0A_hbN_unmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ZD_qsz : zdesc := ltac2:(tb__ "0|0|
S18S19S17SfA2SfS18S17SfU1Z68A4Z70A4").
Definition qsz_chk (nW : nat) (cv : hbvar) : bool := ltac2:(tb__ "0|6|
S14S14S14S14S15S19S6S6A2M0A1M1S16Lx;S28S29Vcv;A1M2A1S1aG0G1S1cLl;Lp;X15x2SbS42S27G2A1M3S2cA2A1A2S37VnW;S31SaG3A1M4A3A2S25S39S3aS32A1S38VnW;G4A2A3A2S25S4S5S9S27S41G2S2cA2A1M5A1A1S1bS4S8G5A1S2dA3A3A2").

Record hbqsz_ok (nW : nat) (cv : hbvar) : Prop := mkQZ { qz_chk : qsz_chk nW cv = true }.

Section Qsz.
Variables (nW : nat) (Kc : KcA) (A : AA) (rho1 : valuation) (p n : Z) (i : nat) (ch : sec_chunk) (l1 l2 : list (Z * Z)) (TZ : Z -> Prop).
Variables (SC : axst) (f : nat) (l : bool) (cv : hbvar).
Hypothesis VOK : ltac2:(tb__ "0|0|
S2aVSC;Vf;Vl;Vcv;A4").
Hypothesis QZ : hbqsz_ok nW cv.
Hypothesis HU : ltac2:(tb__ "0|0|
S0SfVp;S10S10S23Vch;A1S3bA2Z800A2A3").
Hypothesis HN : 1 <= n.
Hypothesis HNB : ltac2:(tb__ "0|0|
S11S10Z1800S2eVn;A1A2S24Vch;A1A2").
Hypothesis HPIN : ltac2:(tb__ "0|4|
S1S0SeQ40M0A1M1S3Vrho1;P97A2SdG0S1fS1eVA;A1M2A1A2A3S1S0G1S3Vrho1;P98A2SdG0S21G2A1A2A3S1S0G1S3Vrho1;P9bA2SdG0S22G2A1A2A3S1S0G1S3Vrho1;PcA2SdG0Vp;A2A3S1S0G1S3Vrho1;P69A2SdG0S2eVn;A1M3A2A3S0G1S3Vrho1;P6aA2SdG0S12G3Z8A2A2A3A2A2A2A2A2").
Hypothesis HNUM : ltac2:(tb__ "0|0|
S33VA;Vp;Vn;Vi;Vch;A5").
Hypothesis FCHB : ltac2:(tb__ "0|0|
S0S16S25S4S5S40A1S34VnW;A1A3S1aA3").
Hypothesis F1 : FCH1 nW rho1.

Hypothesis LFq : ltac2:(tb__ "0|1|
S1S3dS3fS1dS7Vrho1;A1A2S3eS10S1fS1eVA;A1A1Z68A2U8S2fS20VA;A1A1M0A3A2S1S11Z0G0A2S11G0S3cA2A2A2").
Hypothesis HZ_T : ltac2:(tb__ "0|1|
SfS1S11S1fS1eVA;A1A1M0R1A2S13R1S10G0Z1000A2A2A2S2S35VA;Vi;Vch;R2A4A1F_;Fz;").
Hypothesis P123 : ltac2:(tb__ "0|1|
S0SeQ40M0A1S3Vrho1;P7bA2SdG0S2fS20VA;A1A1A2A3").
Let JH2' : jpredA := ltac2:(tb__ "0|0|
S36VKc;VA;Vrho1;Vl1;Vl2;Vi;Vch;VTZ;A8").

Theorem G_qsz_hb : ltac2:(tb__ "0|0|
ScS15SeQ40A1A1S30S26S1dVJH2';S29Vcv;A1R3R2R1A6S26S1dVJH2';S2bVcv;A1R4R3R2A6F_;Fw;Ftp;Fr;").
Proof.
  intros r tp [tr [ms md]] H. rewrite (v_PT SC f l cv VOK). unfold PT_hb.
  destruct QZ as [HC]. unfold qsz_chk in HC. apply andb_prop in HC as [HC C5]. apply andb_prop in HC as [HC C4]. apply andb_prop in HC as [HC C3]. apply andb_prop in HC as [C1 C2].
  assert (HX : ax_X (hv_LR cv) = []) by (destruct (ax_X (hv_LR cv)); [reflexivity | discriminate C1]).
  destruct (proj2 H) as (HA & HK & Htp & Htop & RW4 & RLL & KEY & VK & PR). cbn [w_tr w_cfg cfg_model fst snd] in VK, RW4, RLL, Htop.
  pose proof (zenv_rw nW A rho1 p n i ch HU HN HNB HPIN HNUM FCHB F1 r RW4 RLL Htop) as ZE.
  destruct HNUM as ((r0 & QS0) & _).
  pose proof (qs_nums A (p, n) i ch r0 QS0) as (T0 & T1 & _ & _ & TG & TI & _).
  destruct HPIN as (P151 & _). destruct LFq as (LC & LQ0 & LQ1).
  set (T := ag_thread (aa_geom A)) in *. set (qsz := qsize (aa_q_thread A)) in *.
  assert (E151 : rw r 151%positive = Z_to_bv 64 T) by (rewrite RW4 by (unfold GW; lia); exact P151).
  assert (E123 : rw r 123%positive = Z_to_bv 64 qsz) by (rewrite RW4 by (unfold GW; lia); exact P123).
  assert (EcQ : eval r cQ = Z_to_bv 64 (T + 80)) by (unfold cQ; apply (ev_add_lit r vT T 80); [unfold vT; cbn [eval]; exact E151 | lia | lia | lia]).
  assert (CV : cell_ok (view segsA (rm r)) (mkACell (T + 80 + 24) 8 qsz)).
  { intros k Hk. cbn [c_addr c_w c_val] in *. rewrite VK; [replace (T + 80 + 24) with (T + 104) by lia; exact (LC k Hk) | apply HZ_T; fold T; lia]. }
  assert (IZ : in_zoneW r (zbH A ch) zloS (zhiX (sc_map_size ch)) ZUH O_qsz ZD_qsz).
  { split; [unfold ZUH; cbn; tauto|]. right. unfold O_qsz, carved. rewrite obj_range_mk by lia. cbn [fst snd]. rewrite EcQ, u64_lit by lia.
    unfold zbH, zbX, zloS, zhiX. fold T. lia. }
  assert (H3 : SPA segsA JH2' (addo (hv_LR cv) O_qsz) r tp (tr, mkCfg ms md)).
  { pose proof (SPA_carve_list segsA JH2' r (hv_LR cv) tp _ [(cQ, 24, 32, [(24, 8%nat, SVar 123)])] (ss_next (ax_S (hv_LR cv))) H) as Y. cbn zeta in Y. apply Y; clear Y.
    - exact C2.
    - apply Pos.le_refl.
    - apply carve_okq_list; [exact HX|]. apply Forall_cons; [|apply Forall_nil]. unfold carve_okq. lazy beta iota zeta. rewrite EcQ, u64_lit by lia.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|]. split.
      + intros off Hoff. apply (cell_wok_rd2 (rm r) (T + 80 + 24) 8 qsz (T + 80 + off) CV); [cbn [Z.of_nat]; lia | lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia].
      + unfold cells_in_view. apply Forall_cons; [|apply Forall_nil]. intros jj Hjj.
        apply (civ_cell r (rm r) (T + 80) 24 8 qsz (SVar 123)); [exact CV | cbn [eval]; exact E123 | lia | cbn [Z.of_nat]; lia | exact Hjj].
    - apply (zonesW_cross r (zbH A ch) zloS (zhiX (sc_map_size ch)) ZUH (zsepH A (p, n) i ch r0 QS0) [O_qsz] [ZD_qsz] (ss_objs (ax_S (hv_LR cv))) (zds_of nW (ss_objs (ax_S (hv_LR cv))))).
      + constructor; [exact IZ | constructor].
      + apply (zds_sound nW A p n ch r (zbH A ch) zloS (zhiX (sc_map_size ch)) ZUH); try (repeat split; reflexivity); [exact ZE | exact C3].
      + cbn [forallb]. rewrite C4. reflexivity.
    - apply (zonesW_pd r (zbH A ch) zloS (zhiX (sc_map_size ch)) ZUH (zsepH A (p, n) i ch r0 QS0) [O_qsz] [ZD_qsz]); [constructor; [exact IZ | constructor] | reflexivity]. }
  unfold addf. apply SPA_refacts; [exact H3 | exact C5 |]. intros HF4. apply Forall_app. split; [exact HF4|].
  unfold F_qsz. apply Forall_cons; [|apply Forall_nil].
  apply (hle r (SVar 123) (SLit kQuarantineCacheMax) qsz kQuarantineCacheMax); [cbn [eval]; exact E123 | apply elit | unfold kQuarantineCacheMax in *; lia | unfold kQuarantineCacheMax; lia | exact LQ1].
Qed.
End Qsz.
End F0A_hbN_qsz.

(* [comment removed for export] *)
Module SegQIF_cont.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "pow"; "div"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "it_cls"; "it_ab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "cls_of"; "QFP"; "@Corelib.Init.Datatypes"; "bool"; "list"; "cons"; "true"; "length"; "prod"; "nat"; "nil"; "pair"; "None"; "app"; "fst"; "option"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "ss_next"; "rw"; "obj_range"; "sobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "qbatch"; "aa_cache_inited"; "ag_spacebeg"; "cs_cache"; "aa_q_global"; "aa_q_thread"; "budget_bound"; "class_state"; "cs_mapped_free_array"; "mkQB"; "aa_cls"; "ag_thread"; "ageom"; "cs_free_array"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel"; "drain_grows"; "drainA"; "drain_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "drain_zone"; "JLD"; "JD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env"; "qienvF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "kQuarantineMin"; "max_count"; "SHADOW_BAND_LO"; "free_array"; "kFreeArraySize"; "HIGH_SHADOW_END"; "Sh"; "kFreeArrayMapSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith"; "vb_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.SegQIF_glue"; "ENVM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs"; "PostD"; "PreD"; "m_C1"; "m_RF"; "m_T1f"; "m_sF"; "mcert"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "J_ofPA"; "LQPA"; "import_okPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SegQF_lib"; "DZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c7.SegQIF_cont"; "DZM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "TRP"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dv.SegQIF_call"; "FLM"; "fr_okG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQIF_env SegQIF_mdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SegQF_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.SegQCF_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQIF_mdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dt.SegQIF_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cy.SegQIF_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dv.SegQIF_call.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition DZM (A : AA) (c z : Z) : Prop := ltac2:(tb__ "0|3|
S34S28VA;A1M0A1S0S2bG0A1S0S4S2S6S7S7R2Zd0A2S9Z50Vc;A2A2M1Vz;A2S8Vz;S7G1Z4A2A2A2S4S2S6S54R1Vc;A2M2Vz;A2S8Vz;S7S7R1SbZ2Z25A2A2Z1000A2A2A2S2S6S57G2A1Vz;A2S8Vz;S50A2A2A2A2TSB;TT;").

Section GeoM.
Variables (A : AA) (it : Z * Z) (r : valuation) (t st : Z).
Hypothesis QE : ltac2:(tb__ "0|0|
S49VA;Vit;Vr;Vt;Vst;A5").

Lemma geoM_nums : ltac2:(tb__ "0|8|
S2bS28VA;A1M0A1S0SeVit;A1S0S2S2S6Z1R1A2S6R1Z1eA2A2S2S1S0S54R2R1A2M1S7S7R2S9R1SbZ2M2Z20A2A2A2M3Ze0000000A2A3S2S6S56R2A2S2S6S7S7R2SbG2Z25A2A2Z1000A2S37G0A1M4A2S2S6G4Z7fffff800000A2S2S6S7S1eS0S0Vit;A3M5S9ScS7S20S0S0Vit;A3Z7A2Z8M6A2G6A2A2G1A2S2S6G3SfVit;A1M7A2S6G7G5A2A2A2A2A2A2A2A2Tc;TSB;").
Proof.
  intros SB c. pose proof QE as [HG HSEP3 HRTC HRIG HGEO HV HCV HIM HSTAT Ht Hst HNF HQP HAU HIN HPR HMU]. unfold qgeo in HGEO.
  pose proof (qf_nums A it r t st QE) as (T0 & T1 & C0 & C1' & S14 & TG & K16).
  destruct HGEO as (C1 & Z1 & Z2 & RZ & RZ16 & EU & N1 & R1 & M1 & U1 & A16 & UN & TOP & S1 & S2 & S3 & N8a & N8b).
  assert (FAv : free_array SB c = SB + c * 2 ^ 32 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  fold SB c in R1, U1, UN, S2, S14, HMU |- *. unfold kUserSpaceSize, kRegionSize, kFreeArraySize in HMU. unfold HIGH_SHADOW_END.
  split; [exact C1|]. split; [exact FAv|]. rewrite FAv. clear - R1 U1 UN S2 S14 HMU TG EU RZ. repeat split; lia.
Qed.

Lemma dzone_M : ltac2:(tb__ "0|1|
S0S46S28VA;A1SeVit;A1M0S11VA;G0A2R1A4S6dVA;G0R2A3F_;Fz;").
Proof.
  intros z HZ. destruct geoM_nums as (C1 & FAv & S1 & S14 & TG & _). cbv zeta in FAv, S1, S14.
  pose proof (cv_fa_bounds _ _ _ _ _ (qf_hcv A it r t st QE)) as (_ & FB2 & FB3).
  destruct (kchunks_facts _ C1) as (KC & _).
  pose proof (Zle_0_nat (length (cs_free_array (cls_of A (it_cls it))))) as NF0.
  unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS.drain_zone in HZ. cbv zeta in HZ. unfold DZM. cbv zeta.
  set (SB := ag_spacebeg (aa_geom A)) in *. set (c := it_cls it) in *. set (cs := cls_of A c) in *. set (fa := free_array SB c) in *.
  unfold region_info, kRegionInfoStride, kFreeArraySize, kFreeArrayMapSize, HIGH_SHADOW_END in *. rewrite kSpaceSize_val in HZ.
  destruct HZ as [H|[H|[H|(_ & [H|H])]]].
  - left. lia.
  - right; left. lia.
  - right; left. lia.
  - right; left. lia.
  - right; right. unfold SHADOW_BAND_HI, HIGH_SHADOW_END, Sh, SHADOW_OFF in *.
    pose proof (Z.div_le_mono fa (fa + cs_mapped_free_array cs) 8 ltac:(lia) ltac:(lia)) as D0.
    pose proof (Z.div_le_upper_bound (fa + cs_mapped_free_array cs) 8 (2 ^ 44 - 32768) ltac:(lia) ltac:(lia)) as D1. lia.
Qed.

Lemma floc_outM : ltac2:(tb__ "0|0|
S0S72VA;Vit;R1A3S3S6dVA;SeVit;A1R2A3A1F_;Fz;").
Proof.
  intros z HF HZ. destruct geoM_nums as (C1 & FAv & S1 & S14 & TG & UF & R1 & ABU). cbv zeta in FAv, S1, S14, UF, R1.
  pose proof (qf_nums A it r t st QE) as (T0 & T1 & C0 & C1' & _ & _ & _). pose proof (qf_Sh A it r t st QE) as (SH0 & SH1 & L0 & L1).
  pose proof (qf_wins A it r t st QE) as (WTI & WCI & WTB & WCB & WTC & WTS & WCS).
  unfold FLM in HF. unfold DZM in HZ. cbv zeta in HZ.
  set (SB := ag_spacebeg (aa_geom A)) in *. set (c := it_cls it) in *. set (fa := free_array SB c) in *. set (T := ag_thread (aa_geom A)) in *. set (CTX := ag_ctx (aa_geom A)) in *.
  assert (SHF : Sh (fst it) + (snd it + 7) / 8 <= Sh fa).
  { unfold Sh. pose proof (Z.div_le_mono (fst it + (snd it + 7) / 8 * 8) fa 8 ltac:(lia) UF) as D0. rewrite Z.div_add in D0 by lia. lia. }
  assert (SHL : 0x7fff8000 <= Sh fa) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos fa 8 ltac:(unfold HIGH_SHADOW_END in S1; lia) ltac:(lia)); lia).
  rewrite <- L1 in SHF. unfold IMG_LO, IMG_HI, SHADOW_BAND_HI, HIGH_SHADOW_END in *.
  clear - HF HZ C1 FAv S1 S14 TG UF R1 ABU T0 T1 C0 C1' SH0 SH1 L0 WTI WCI WTB WCB WTC WTS WCS SHF SHL. lia.
Qed.
End GeoM.

Lemma fr_okG_loc : ltac2:(tb__ "0|1|
S0OF_;S27S21S26S73R4R3R2R1A4S0S2S6S1eS0S0S25R4R3A2M0A3R1A2S8R1S20S0S0G0A3A2A2R7R2A1F_;Fz;F_;Fo;Frho;FA;FFL;").
Proof.
  intros FL A rho o [(b & lo & hi & cs & -> & L1 & L2 & L3 & CI & B1 & B2 & LOC & _)|(_ & _ & _ & HU)] z Hz.
  - unfold carved in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd] in Hz. exact (LOC z Hz).
  - exact (proj1 (HU z Hz)).
Qed.

Section ContM.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).
Variables (n : Z) (g vb : bool) (D : mdata).
Hypothesis HC : ltac2:(tb__ "0|0|
S62Vn;Vg;Vvb;VD;A4").

Lemma qif_post_ok : ltac2:(tb__ "0|c|
S27S0S0S19S18S0S0A2M0S14G0A1S14S29A1M1G1S21S14S3bQ40M2A1M3A1M4S14S4bA1M5S63S4aS0S0S21G4G5S4aS1S13S2aR13A1S16A3S1S0S40SeR10A1A1Vn;A3S1S0SaS17S0S2cS11R15SeR11A1M6A2A1A2A1S52G6A1A3S1S13S43SeR12A1M7S11R16G7A2A2Vg;A3S1S13Vvb;S5aR13A1A3S5bVn;R18SeR14A1R10A4S49R19R15R11RcRbA5S1G3S24R12Pd0A2S3cG2S51A2A3S3eS10R13R12S5eVD;A1M8S1bG5S64R11S65R10RfA2A4A5S41S59VKc;A1VA0;Vrho0;R1cR1bR1aR19S15G0R18R17A3R16R15R14R13R12R10AeS4eS23S39S5dVn;Vg;A2M9A1A1S4dS4cR15S5fVD;A1MaS3fR11R14R12A3A3S61VD;A1MbA2ReA3S47R1eVKc;SeR1aA1S4dS4cR16GaS3fR12R15R13A3A3GbA2R15RfReRdRcA9S69R17S3fR13R16R14A3GaGbG9S5cVn;Vg;A2G8R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd';Ftr';FtpL;FrhoL;Fst;Ft;Fmd;Fms;Ftr;Ftp;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fa;FA;").
Proof.
  intros A a n0 nd it its tmp' rest rho tp tr ms md t st rhoL tpL tr' md' HCI Hn HFULL HGR EVB (E200 & E201 & E221 & E222 & E223 & E224 & E225 & ECH) QE E208 Hsm (HK & _) Hag (HKL & HRM & _).
  pose proof (sF_get n g vb D HC 155%positive _ ltac:(unfold SFREF; cbn; tauto)) as W155. pose proof (sF_get n g vb D HC 158%positive _ ltac:(unfold SFREF; cbn; tauto)) as W158.
  pose proof (sF_get n g vb D HC 221%positive _ ltac:(unfold SFREF; cbn; tauto)) as W221.
  destruct (c_XF0 n g vb D HC) as (XP & XC & _ & NXP & _).
  pose proof (C1_pre_holds n g vb D HC rho tp _ Hsm) as HFp.
  pose proof (fr_allM Kc A it rho tp tr md t st HKc HK HCI HFp QE E208 n g vb D HC EVB) as FRA.
  destruct (frame_viewG (FLM A it) A (m_C1 D) _ (m_RF D) rho tp tr ms md Hsm (c_C1objs n g vb D HC) FRA) as (_ & _ & _ & FR4).
  split; [split|split].
  - intros a0 Hin. apply HRM. intros HZ. exact (floc_outM A it rho t st QE _ (proj1 (FR4 a0 Hin)) (dzone_M A it rho t st QE _ HZ)).
  - intros o' oR Ho' HoR. rewrite (c_new n g vb D HC) in Ho'. destruct g; [|destruct Ho']. destruct Ho' as [<-|[]].
    destruct (geoM_nums A it rho t st QE) as (C1 & FAv & S1 & S14 & TG & _). cbv zeta in FAv, S1, S14.
    pose proof (cv_fa_bounds _ _ _ _ _ (qf_hcv A it rho t st QE)) as (_ & FB2 & FB3).
    destruct (qf_hrig A it rho t st QE) as (_ & _ & E155 & _).
    destruct (kchunks_facts _ C1) as (KC & _). rewrite Hn in KC.
    set (SB := ag_spacebeg (aa_geom A)) in *. set (c := it_cls it) in *. set (nf := Z.of_nat (length (cs_free_array (cls_of A c)))) in *. assert (NF0 : 0 <= nf) by (unfold nf; lia).
    assert (EL : forall v, (v < 240)%positive -> rw rhoL v = eval rho (wsub_get (m_sF D) v)).
    { intros v Hv. rewrite <- (proj1 Hag v ltac:(rewrite NXP; exact Hv)). cbn [rw rho_sub]. apply eval_absorb. }
    assert (E155L : rw rhoL 155%positive = Z_to_bv 64 SB) by (rewrite (EL 155%positive eq_refl), W155; exact E155).
    assert (E158L : rw rhoL 158%positive = Z_to_bv 64 c) by (rewrite (EL 158%positive eq_refl), W158; exact E200).
    assert (E221L : rw rhoL 221%positive = Z_to_bv 64 nf) by (rewrite (EL 221%positive eq_refl), W221; exact E221).
    unfold HIGH_SHADOW_END, kFreeArraySize in *.
    assert (Edst : bv_unsigned (eval (rho_sub rhoL []) dst_e) = free_array SB c + 4 * nf).
    { unfold dst_e, fa_e. rewrite U_add, U_add, U_add, !U_sll_lit. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.vSB, vNF. cbn [eval rw rho_sub wsub_get]. change V_CLS with 158%positive. rewrite E158L, E155L, E221L, !u64_lit by lia.
      change (32 mod 64) with 32. change (2 mod 64) with 2. unfold M64v. rewrite (Z.mod_small (c * 2 ^ 32)) by lia. rewrite (Z.mod_small (c * 2 ^ 32 + 3758096384)) by lia.
      rewrite (Z.mod_small (SB + (c * 2 ^ 32 + 3758096384))) by lia. rewrite (Z.mod_small (nf * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. rewrite FAv. lia. }
    rewrite obj_range_subst. unfold O_dstD. rewrite obj_range_mk by lia. rewrite Edst.
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q1.SegQCF_call.rd_pointwise _ _ _ _ (FLM A it) (fr_okG_loc _ A rho oR (proj1 (Forall_forall _ _) FRA oR HoR))).
    intros z Hz HF. apply (floc_outM A it rho t st QE z HF). unfold DZM. cbv zeta. right; left. fold SB c. rewrite FAv in Hz |- *. lia.
  - intros r0 a0 j oR Hr. rewrite XP in Hr. destruct Hr.
  - intros r0 a0 j Hr. rewrite XC in Hr. destruct Hr.
Qed.

Lemma drainA_clsM : ltac2:(tb__ "0|0|
S27S0S70SdR1A1S17S30S33R2A1A2A2S1S30S11S44R3R2A2R2A2S45R2S11R3R2A2A2A3F_;Fc;FA;").
Proof. intros A c HL. unfold cls_of, nthZ, drainA. cbn [aa_cls]. apply nth_list_upd_same. exact HL. Qed.

Lemma dzone_DZM : ltac2:(tb__ "0|2|
S27S0S0S6Z0M0S2bS28R3A1A1A2S6G0S31S11R4R3A2A1A2S6Z1S40R4A1A2S6S9Z4S7SaS17S0S36S11R6R5A2A1A2A1S40R5A1A2A2S55A2S1S13S43R6S11R7R6A2A2S16A3S6S7S31S11R8R7A2M1A1S58A2S55A2F_;S46S28R8A1R7G1R6A4S6cR9R8R7A3F_;F_;F_;F_;F_;F_;Fz;Fc;FA;").
Proof.
  intros A c z HSB HM0 HKC HN HGRW HZ. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS.drain_zone in HZ. cbv zeta in HZ. unfold DZ. cbv zeta.
  pose proof (Zle_0_nat (length (cs_free_array (cls_of A c)))) as NF0.
  unfold kRegionInfoStride, kFreeArraySize, kFreeArrayMapSize in *.
  destruct HZ as [H|[H|[H|(HGW & [H|H])]]].
  - left. lia.
  - right; right; left. lia.
  - right; left. lia.
  - specialize (HGRW HGW). right; right; left. lia.
  - specialize (HGRW HGW). right; right; right. unfold Sh in *. set (fa := free_array (ag_spacebeg (aa_geom A)) c) in *. set (mfa := cs_mapped_free_array (cls_of A c)) in *.
    pose proof (Z.div_le_mono fa (fa + mfa) 8 ltac:(lia) ltac:(lia)) as D0.
    pose proof (Z.div_le_mono (fa + mfa + 32768 * 8) (fa + 536870912) 8 ltac:(lia) ltac:(lia)) as D1. rewrite Z.div_add in D1 by lia. lia.
Qed.
Lemma DZ_QFPM : ltac2:(tb__ "0|0|
S27S27S0S0S2S6Z1R2A2S6R2Z1eA2A2S1S35S28R5A1S28R4A1A3S6cR6R4R3A3S12R6R4A2F_;F_;F_;Fz;Fc;FA0';FA;").
Proof.
  intros A A0' c z Hc EG HZ. unfold DZ in HZ. cbv zeta in HZ. rewrite EG in HZ. unfold QFP. destruct HZ as [H|[H|[H|H]]].
  - right; left. lia.
  - right; right; left. exists c. split; [exact Hc|]. left. exact H.
  - right; right; left. exists c. split; [exact Hc|]. right; left. exact H.
  - right; right; left. exists c. split; [exact Hc|]. right; right. exact H.
Qed.

Lemma qif_exit_core : ltac2:(tb__ "0|14|
S27S0S0S0S19S18S0S0A2M0S14G0A1S14S29A1M1G1S21S14S3bQ40M2A1M3A1M4S14S4bA1M5S63S4aS0S0S21G4S1G1S2eR12A1S1aS29A1A3S1S13S2aR13A1S16A3S42VA0;R14A2S1G1S2dR15A1S15S29S32R14S15G0R10RfA3R13A3S1dS29ReRdA3A3A3S1S0S40SeR11A1A1Vn;A3S1S0SaS17S0S2cS11R17SeR12A1M6A2A1A2A1S52G6A1A3S1S13S43SeR13A1M7S11R18G7A2A2Vg;A3S1S13Vvb;S5aR14A1A3S5bVn;R1aSeR15A1R11A4S49R1bR16R12RdRcA5S1G3S24R13Pd0A2S3cG2S51A2A3S3eS10R14R13S5eVD;A1M8S1bG5S64R12S65R11R10A2A4A5S41S59VKc;A1M9VA0;Vrho0;R1eR1dR1bR1aS15G0R19R18A3R17R16R15R14R13R11AeS21S71S4fR18S3fR14R17R15A3S5fVD;A1MaS61VD;A1MbS39S5dVn;Vg;A2McA1S39G8A1MdS39S5cVn;Vg;A2MeA1R2R11A9S3dS10S67S47R22VKc;SeR1dA1A3S4dS4cR19GaS3fR15R18R16A3A3GbA2R18R12R11A5S6aGbGcGeG8GaA5R3R11R2A6S5S21S21S2S3dS10S41G9VA0;Vrho0;S44R24SeR1fA1A2R23R21R20S15G0R1fR1eA3R1dR1cAaS60VD;A1R1R13R4A6S2S4eS23GdA1R1bR1A3S2S0S3S46S28R25A1SeR20A1MfS11R25GfA2R1A4A1S1S1fS3bQ8A1M10A1M11S38S10S22R3A1R2A3S38S10S22R1dA1R2A3M12A3F_;Fz;S0S2S6S53R1A2S8R1S50A2A2S3S1G11G12S1cG10A1M13A3A1S3S1G11S38S10S22R4A1R3A3G13A3A1F_;F_;Fz;A2A2A2Lrho5;A2F_;F_;Fw';Frho';F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FtpL;FrhoL;Fst;Ft;Fmd;Fms;Ftr;Ftp;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd it its tmp' rest rho tp tr ms md t st rhoL tpL HTH HCI HQP HGL Hn HFULL HGR EVB HENV QE E208 Hsm0 HJ0 rho' w' HLK [Hsm' HJ'].
  pose proof HJ0 as (HK & HCB & HRMM & HFRM).
  destruct (c_XF0 n g vb D HC) as (XP & XC & XT & NXP & NXC).
  assert (EG : aa_geom A = aa_geom A0) by (destruct HQP as (ESB & _); unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  pose proof (smatch_facts_hold _ _ _ _ (proj1 Hsm0)) as HFa.
  pose proof (C1_pre_holds n g vb D HC rho tp _ Hsm0) as HFp.
  pose proof (fr_allM Kc A it rho tp tr md t st HKc HK HCI HFp QE E208 n g vb D HC EVB) as FRA.
  destruct (frame_viewG (FLM A it) A (m_C1 D) _ (m_RF D) rho tp tr ms md Hsm0 (c_C1objs n g vb D HC) FRA) as (_ & _ & _ & FR4). set (r3 := rho_absorb rho (m_RF D) (vms md tp ms)) in *.
  destruct (entails_frA_sound segsA (m_C1 D) (PreD n g) (m_sF D) (m_RF D) rho tp tr ms md (c_He n g vb D HC) Hsm0) as (_ & _ & _ & HwfR & HinR).
  destruct w' as [tr2 [ms2 md2]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ'.
  pose proof HJ' as HJc. unfold J_ofPA in HJ'. destruct HJ' as (HK3 & HRM & HDEF & HRL3).
  pose proof HLK as (Hag' & Hrm' & HagL' & Hlink').
  set (c := it_cls it) in *.
  assert (HF4 : Forall (holds rho') (ss_facts (ax_S (m_C1 D)))).
  { apply Forall_forall. intros f Hf. exact (proj1 (holds_agree_vals _ rho rho' f Hag' (proj1 (forallb_forall _ _) (c_FBC1 n g vb D HC) f Hf)) (proj1 (Forall_forall _ _) HFa f Hf)). }
  assert (HT40 : SPA segsA (J_ofPA (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS.JLD A Kc c) (rho_sub r3 (m_sF D)) tp rhoL tpL) (m_T1f D) rho' tpL (tr2, mkCfg ms2 md2)).
  { rewrite <- (c_T1f n g vb D HC). unfold T1f_of. apply (SPA_refacts segsA); [exact (conj Hsm' HJc) | exact (c_FBT1 n g vb D HC) | intros _; exact HF4]. }
  assert (RNG : forall o, In o (m_RF D) -> obj_range rho' o = obj_range rho o).
  { intros o Ho. apply (obj_range_agree_vals (ss_next (ax_S (m_C1 D)))); [exact Hag' | exact (proj1 (forallb_forall _ _) HwfR o Ho)]. }
  set (rho5 := rho_absorb rho' (m_RF D) (ms_with_mem ms2 (rm rho))).
  assert (RM5 : forall x, rm rho5 x = if in_ranges_dec rho' (m_RF D) x then rm rho x else rm rhoL x).
  { intros x. unfold rho5, rho_absorb, ms_with_mem. cbn [rm ms_mem]. rewrite Hrm'. reflexivity. }
  assert (IRE : forall x, in_ranges rho' (m_RF D) x <-> in_ranges rho (m_RF D) x).
  { intros x. split; intros (o & Ho & Hox); exists o; [rewrite <- (RNG o Ho) | rewrite (RNG o Ho)]; exact (conj Ho Hox). }
  assert (KEPT : forall x, in_ranges rho (m_RF D) x -> rm rhoL x = rm r3 x).
  { intros x Hin. apply (HRM x). intros HZ. exact (floc_outM A it rho t st QE _ (proj1 (FR4 x Hin)) (dzone_M A it rho t st QE _ HZ)). }
  assert (KEY : forall x : word, ~ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS.drain_zone (aa_geom A) c (cls_of A c) (bv_unsigned x) -> rm rho5 x = rm rho x).
  { intros x Hx. rewrite RM5. destruct (in_ranges_dec rho' (m_RF D) x) as [Hi|Hn']; [reflexivity|]. rewrite (HRM x Hx). cbn [rm rho_sub]. apply rm_absorb_out. intros Hi. exact (Hn' (proj2 (IRE x) Hi)). }
  assert (DEF5 : forall x : word, SHADOW_BAND_LO <= bv_unsigned x < SHADOW_BAND_HI -> rm rho x <> None -> rm rho5 x <> None).
  { intros x HBx Hd. rewrite RM5. destruct (in_ranges_dec rho' (m_RF D) x) as [Hi|Hn']; [exact Hd|].
    apply (HDEF x HBx). cbn [rm rho_sub]. unfold r3. rewrite (rm_absorb_out _ _ _ _ (fun Hi => Hn' (proj2 (IRE x) Hi))). exact Hd. }

  set (A1 := drainA A c).
  pose proof HK3 as (HAQ3 & HKc3 & _).
  destruct (AInvQ_parts' A1 rhoL tpL md2 HAQ3) as (HG3 & HI33 & HQP3 & HAU3 & HSR3).
  assert (QWT : forall z, QW A z -> z < topG (aa_geom A)).
  { intros z HQ. exact (QRD_lt_top A1 HG3 HI33 HQP3 HAU3 _ HSR3 z (QRD_QFP A1 z (or_introl HQ))). }
  assert (V5IN : forall z, 0 <= z < 2 ^ 64 -> in_ranges rho' (m_RF D) (Z_to_bv 64 z) -> view segsA (rm rho5) z = view segsA (rm rho) z).
  { intros z Hr Hi. apply view_agree. intros _. rewrite RM5. destruct (in_ranges_dec rho' (m_RF D) (Z_to_bv 64 z)) as [|Hn']; [reflexivity | exfalso; exact (Hn' Hi)]. }
  assert (V5OUT : forall z, ~ in_ranges rho' (m_RF D) (Z_to_bv 64 z) -> view segsA (rm rho5) z = view segsA (rm rhoL) z).
  { intros z Hn'. apply view_agree. intros _. rewrite RM5. destruct (in_ranges_dec rho' (m_RF D) (Z_to_bv 64 z)) as [Hi|]; [exfalso; exact (Hn' Hi) | reflexivity]. }
  assert (VL3 : forall z, 0 <= z < 2 ^ 64 -> in_ranges rho (m_RF D) (Z_to_bv 64 z) -> view segsA (rm rhoL) z = view segsA (rm r3) z).
  { intros z Hr Hi. apply view_agree. intros _. exact (KEPT _ Hi). }
  set (r5 := set_rm rhoL (rm rho5)).
  assert (HK5' : K0 Kc A1 r5 tpL tr2 md2).
  { apply (K0_blind Kc A1 rhoL r5 tpL tr2 md2); [intros i; reflexivity | intros l; reflexivity | | | exact HK3].
    - intros z Hz NQ. unfold r5. cbn [rm set_rm]. destruct (Z_le_dec 0 z) as [Z0|Z0]; [destruct (Z_lt_dec z (2 ^ 64)) as [Z1|Z1]|].
      2, 3: unfold view; replace ((0 <=? z) && (z <? 2 ^ 64))%bool with false; [reflexivity | symmetry; apply andb_false_iff; first [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]].
      destruct (in_ranges_dec rho' (m_RF D) (Z_to_bv 64 z)) as [Hi|Hn']; [|exact (V5OUT z Hn')].
      pose proof (proj1 (IRE _) Hi) as Hi'. rewrite (V5IN z ltac:(lia) Hi). rewrite (VL3 z ltac:(lia) Hi').
      destruct (FR4 _ Hi') as (_ & ALT). rewrite u64_lit in ALT by lia. destruct ALT as [ALT|[ALT|ALT]].
      + exfalso. change (aa_geom A1) with (aa_geom A) in Hz. lia.
      + exfalso. exact (NQ (proj1 ALT)).
      + symmetry. exact ALT.
    - intros z HQ Hd. unfold r5. cbn [rm set_rm]. pose proof (view_range _ _ Hd) as Hr.
      destruct (in_ranges_dec rho' (m_RF D) (Z_to_bv 64 z)) as [Hi|Hn']; [|rewrite (V5OUT z Hn'); exact Hd].
      pose proof (proj1 (IRE _) Hi) as Hi'. rewrite (V5IN z Hr Hi). rewrite (VL3 z Hr Hi') in Hd.
      destruct (FR4 _ Hi') as (_ & ALT). rewrite u64_lit in ALT by lia. destruct ALT as [ALT|[ALT|ALT]].
      + exfalso. pose proof (QWT z HQ). lia.
      + exact (proj2 ALT).
      + rewrite <- ALT. exact Hd. }
  destruct HK5' as (HA5 & HKc5 & _).
  pose proof HK as (_ & _ & Htp & Htop & HRG).
  assert (RW5 : forall i, (i < NXM)%positive -> rw rho5 i = rw rho i).
  { intros i Hi. unfold rho5. cbn [rw rho_absorb]. symmetry. apply (proj1 Hag'). rewrite NXC. exact Hi. }
  assert (HK5 : K0 Kc A1 rho5 tpL tr2 md2).
  { split; [exact HA5|]. split; [exact HKc5|]. split; [|split].
    - unfold tp_ok in *. rewrite (RW5 24%positive eq_refl). exact Htp.
    - unfold top_high, V_DEPTH in *. rewrite (RW5 10%positive eq_refl), (RW5 15%positive eq_refl). exact Htop.
    - unfold rigidQ in *. rewrite (RW5 151%positive eq_refl), (RW5 152%positive eq_refl), (RW5 155%positive eq_refl), (RW5 156%positive eq_refl). exact HRG. }

  pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A rho tp _ _ HK) as [HG _ _ _ _ HLEN HCLS _ _ _ _ _ _].
  destruct (kq_facts segsA (K0 Kc) HL A1 rhoL tpL _ _ HK3) as [_ _ _ _ _ _ HCLS3 _ _ _ _ _ _].
  destruct (geoM_nums A it rho t st QE) as (C1 & FAv & S1 & _). cbv zeta in FAv, S1. fold c in C1, FAv. unfold HIGH_SHADOW_END in S1.
  destruct (kchunks_facts _ C1) as (KC & KMX & _). rewrite Hn in KC, KMX.
  pose proof (HCLS HCI c C1) as CV. pose proof (cv_fa_bounds _ _ _ _ _ CV) as (FB1 & FB2 & FB3).
  pose proof (HCLS3 HCI c C1) as CV3. pose proof (cv_fa_bounds _ _ _ _ _ CV3) as (_ & FC2 & FC3).
  unfold A1 in FC2, FC3. rewrite (drainA_clsM A c ltac:(rewrite HLEN; lia)) in FC2, FC3. unfold drain_cs in FC2, FC3. cbn [cs_free_array cs_mapped_free_array] in FC2, FC3.
  rewrite length_app, length_skipn in FC2. unfold drain_keep in FC2. rewrite Hn in FC2.
  assert (DZI : forall z, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS.drain_zone (aa_geom A) c (cls_of A c) z -> DZ A c z).
  { intros z HZ. apply (dzone_DZM A c z); [lia | lia | rewrite Hn; lia | | | exact HZ].
    - rewrite Hn. clear - FC2 FC3 HFULL KC KMX. destruct (drain_grows c (cls_of A c)); lia.
    - intros EGW. rewrite EGW in FC3. exact FC3. }
  assert (VOUTP : forall z, ~ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS.drain_zone (aa_geom A) c (cls_of A c) z -> view segsA (rm rho5) z = view segsA (rm rho) z).
  { intros z Hz. apply view_agree. intros Hr. apply KEY. rewrite u64_lit by exact Hr. exact Hz. }
  assert (VOUT : forall z, ~ DZ A c z -> view segsA (rm rho5) z = view segsA (rm rho) z).
  { intros z Hz. apply VOUTP. intros HZ. exact (Hz (DZI z HZ)). }
  assert (VBAND : forall z, SHADOW_BAND_LO <= z < SHADOW_BAND_HI -> view segsA (rm rho) z <> None -> view segsA (rm rho5) z <> None).
  { intros z HB Hd. pose proof (view_range _ _ Hd) as Hr. rewrite view_in in Hd |- * by exact Hr.
    destruct (rd_of segsA (rm rho) (Z_to_bv 64 z)) as [x|] eqn:E; [|exfalso; exact (Hd eq_refl)].
    pose proof (rd_off_image (rm rho) z x ltac:(unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in HB; lia) E) as E'.
    pose proof (DEF5 (Z_to_bv 64 z) ltac:(rewrite u64_lit by exact Hr; exact HB) ltac:(rewrite E'; discriminate)) as D5.
    unfold rd_of. destruct (rm rho5 (Z_to_bv 64 z)); [discriminate | exfalso; exact (D5 eq_refl)]. }
  destruct (CR_drain (K0 Kc) HL (K0_secband Kc) A a s (it :: its) tmp' rest c HTH HCI HGL C1 rho tp tr md (view segsA (rm rho)) (view segsA (rm rho5)) n0 nd HK VOUT VBAND HCB HRMM) as (HCB5 & HRM5).
  destruct HFRM as ((F1 & F1') & F2 & F3 & F4).
  assert (HFRM5 : FRM A0 rho0 rho5).
  { split; [split|split; [|split]].
    - intros i Hi. rewrite (F1 i Hi). symmetry. apply RW5. unfold NPRE in Hi. unfold NXM. lia.
    - intros l. rewrite (F1' l). unfold rho5. cbn [rl rho_absorb]. exact (proj2 Hag' l).
    - intros x Hx. rewrite KEY; [exact (F2 x Hx)|]. intros HZ. apply Hx. apply QRD_QFP. exact (DZ_QFPM A A0 c _ C1 EG (DZI _ HZ)).
    - intros z Hz. rewrite VOUT; [exact (F3 z Hz)|]. intros HZ. exact (Hz (DZ_QFPM A A0 c _ C1 EG HZ)).
    - intros x HBx Hd. exact (DEF5 x HBx (F4 x HBx Hd)). }
  exists rho5. split; [|split; [|split; [exact VOUTP | exact VBAND]]].
  - pose proof (proj1 (proj1 HT40)) as HsmT. pose proof (smatch_facts_hold _ _ _ _ HsmT) as HfT.
    unfold rho5. apply (SPA_absorb_any segsA (J_ofPA (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS.JLD A Kc c) (rho_sub r3 (m_sF D)) tp rhoL tpL)); [exact XT | | exact HT40 | ].
    + intros o x Ho Hx. exact (coveredb_sound _ _ _ rho' o x HfT (c_RFcov n g vb D HC) Ho Hx).
    + cbn [w_tr w_cfg cfg_model fst snd]. fold rho5. split; [exact HK5|]. split; [exact HCB5|]. split; [exact HRM5 | exact HFRM5].
  - split; [intros i Hi; symmetry; apply RW5; rewrite NXC in Hi; exact Hi | intros l; unfold rho5; cbn [rl rho_absorb]; exact (proj2 Hag' l)].
Qed.
End ContM.

Section CallT.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).
Context {Q : assn} (X : trk Q).
Variables (n : Z) (g vb : bool) (D : mdata).
Hypothesis HC : ltac2:(tb__ "0|0|
S62Vn;Vg;Vvb;VD;A4").

Hypothesis HDC : ltac2:(tb__ "0|2|
S27S0S21S14S3bQ40A1A1S1S13Vg;S16A3S6S2fR5A1S6bA2F_;S6fVQ;VX;S3dS10S48Vn;Vg;R5VKc;R4A5S5dVn;Vg;A2M0R3R2A5S68S10S23S39G0A1A1R3R2S15S18S3aS66A2M1S1bS3aS66S5cVn;Vg;A2S47R5VKc;R4A3A4S1aG1A1A3A5A4F_;Ftp1;Frho1;Fc;FA;").

Lemma qif_call : ltac2:(tb__ "0|d|
S27S0S0S0S19S18S0S0A2M0S14G0A1S14S29A1M1G1S21S14S3bQ40M2A1M3A1M4S0S0S1G1S2eRdA1S1aS29A1A3S1S13S2aReA1S16A3S42VA0;RfA2S1G1S2dR10A1S15S29S32RfS15G0RbRaA3ReA3S1dS29R9R8A3A3A3S1S0S40SeRcA1A1Vn;A3S1S0SaS17S0S2cS11R12SeRdA1M5A2A1A2A1S52G5A1A3S1S13S43SeReA1M6S11R13G6A2A2Vg;A3S1S13Vvb;S5aRfA1A3S1S13Vg;S16A3S6S2fR16A1S6bA2F_;S5bVn;R16SeR11A1RdA4S49R17R12ReRcRbA5S1G3S24RfPd0A2S3cG2S51A2A3S21G4S4eS23S39S5eVD;A1M7A1A1R12R2A3S0S3S46S28R1dA1SeR18A1M8S11R1dG8A2R1A4A1S1S1fS3bQ8A1M9A1MaS38S10S22R5A1R2A3S38S10S22R15A1R2A3A3F_;Fz;S0S2S6S53R1A2S8R1S50A2A2S3S1GaS38S10S22R16A1R2A3S1cG9A1MbA3A1S3S1GaS38S10S22R7A1R3A3GbA3A1F_;F_;Fz;S6eVQ;VX;S3dS10S41S59VKc;A1McVA0;Vrho0;S44R1eSeR19A1A2R1dR1bR1aS15G0R19R18A3R17R16AaS60VD;A1R5R4A5A3F_;F_;F_;FtpL;Frho5;S6eVQ;VX;S3dS10S41GcVA0;Vrho0;R1aR19R17R16S15G0R15R14A3R13R12AaG7R11R10A5A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fst;Ft;Ftp;Frho;Frest;Ftmp';Fits;Fit;Fnd;Fn0;Fs;Fa;FA;").
Proof.
  intros A a s n0 nd it its tmp' rest rho tp t st HTH HCI HQP HGL Hn HFULL HGR EVB HB HENV QE E208 HCt.
  apply (tr_callP X (JRI (K0 Kc) A0 rho0 A a n0 nd (it :: its) tmp' rest) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS.JD n g A Kc (it_cls it)) (m_C1 D) (PreD n g) (m_sF D) (m_RF D) [(PostD n g, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS.JLD A Kc (it_cls it))] rho tp
           (c_He n g vb D HC) (c_Hchk n g vb D HC)).
  - intros rho1 tp1. exact (HDC A (it_cls it) rho1 tp1 HB).
  - intros tr ms md Hsm HJ. exact (qif_JP Kc HKc A0 rho0 n g vb D HC A a n0 nd it its tmp' rest rho tp tr ms md t st HCI Hn HFULL HGR EVB HENV QE E208 Hsm HJ).
  - intros L JL tr ms md rhoL tpL tr' ms' md' Hin Hsm HJ Hag HsmL HJL. destruct Hin as [E|[]]. injection E as <- <-. split.
    + exact (qif_post_ok Kc HKc A0 rho0 n g vb D HC A a n0 nd it its tmp' rest rho tp tr ms md t st rhoL tpL tr' md' HCI Hn HFULL HGR EVB HENV QE E208 Hsm HJ Hag HJL).
    + intros rho' HLK.
      apply (tr_glue X _ (JRI (K0 Kc) A0 rho0 (drainA A (it_cls it)) a n0 nd (it :: its) tmp' rest) (m_T1f D) tpL
               (fun r => agree_vals (ss_next (ax_S (m_C1 D))) rho r
                         /\ (forall z, ~ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS.drain_zone (aa_geom A) (it_cls it) (cls_of A (it_cls it)) z -> view segsA (rm r) z = view segsA (rm rho) z)
                         /\ (forall z, SHADOW_BAND_LO <= z < SHADOW_BAND_HI -> view segsA (rm rho) z <> None -> view segsA (rm r) z <> None)));
        [|intros r (Hr1 & Hr2 & Hr3); exact (HCt r tpL Hr1 Hr2 Hr3)].
      intros w' Hw'. exact (qif_exit_core Kc HKc A0 rho0 n g vb D HC A a s n0 nd it its tmp' rest rho tp tr ms md t st rhoL tpL HTH HCI HQP HGL Hn HFULL HGR EVB HENV QE E208 Hsm HJ rho' w' HLK Hw').
Qed.
End CallT.
End SegQIF_cont.

