(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kb.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lg.

(* [comment removed for export] *)
Module SpineMallocQ15.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sv"; "eval"; "sprop"; "SAlu"; "SLit"; "rm"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "JR"; "phase"; "gh_new"; "ph0"; "frozen"; "ghosts"; "mlink"; "FAb"; "committed"; "ph_f"; "ph_u"; "releasedp"; "rlink"; "zoneR"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "of_nat"; "lt"; "le"; "ge"; "ltb"; "modulo"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Corelib.Init.Datatypes"; "list"; "length"; "bool"; "true"; "nil"; "pair"; "prod"; "cons"; "option"; "None"; "Some"; "nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "cs_free_array"; "cs_mapped_free_array"; "class_state"; "aa_cache_inited"; "aa_geom"; "ag_spacebeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineMallocQ1"; "entryRq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cst_of"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineMallocQ7"; "popfacts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kk.SpineMallocQ15"; "phFin"; "phUF3"; "phU3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP"; "ph_quiet"; "pbase"; "ph_set"; "PF"; "PU"; "ph_get"; "pord"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "NXR"; "L_rf"; "JLRf"; "refill_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k7.SpineMallocQ13"; "phL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kb.SpineMallocQ14"; "e16P"; "e32P"; "e48P"; "e_srcP"; "e24M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jy.SpineMallocQ6"; "exitT"; "finT"; "popT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "vMFA"; "beg1"; "beg2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kk.SpineMallocQ15.ASMP"; "pieceT"; "fillT"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k0.SpineMallocQ12"; "rup_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineMallocQ3"; "phK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineMallocQ4";
"ph_setcnt"; "ph_setri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ju.SpineMallocQ5"; "JRfin"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainTR InvLaws PrimCredit.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RefillModelP RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ju.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineMallocQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ju.SpineMallocQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jy.SpineMallocQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SpineMallocQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jy.SpineMallocQ11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k0.SpineMallocQ12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k7.SpineMallocQ13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kb.SpineMallocQ14.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

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
      * intros t md HM. pose proof (pop_headroom A rb tp md0 W st rho HE PF (ph_set OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.RefillJP.PF 1 phU3) t md HM) as X. cbn [phU3 ph_set ph0 ph_u ph_f committed revealedp Nat.leb] in X.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "la_state"; "sym_runA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "sprop"; "ss_next"; "reg_sv"; "ss_facts"; "ss_objs"; "valuation"; "rm"; "swf"; "sprop_below"; "ss_lenient"; "SAlu"; "cell"; "smatch"; "ss_pc"; "sstate"; "sv_below"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "nil"; "prod"; "option"; "Some"; "pair"; "app"; "false"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "beg2"; "rMS"; "sMS"; "cX"; "idx_rot"; "nobj"; "relM"; "vMFA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.DrainG1"; "JDg"; "entryG"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "ALU_ADD"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF"; "O_riX"; "frozenD"; "ri_hasD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kd.DrainG2"; "SKELG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "drain_zone"; "O_cntD"; "O_dstD"; "dst_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "F_sp_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9"; "O_piece"; "O_shp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kk.DrainG5.GFIN"; "JDfinG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel"; "drainA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "ageom"; "class_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocR10"; "a2_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR11"; "a0_e"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 SMGlue PrimCredit PrimCreditLaws SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillBits DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocR8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.RebuildD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.DrainG1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kd.DrainG2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kh.DrainG3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k7.DrainG4.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

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
S0S22S1cS5A1M0A1S7S31VF;S1fS30Z706a0S20S30A1A3VC0;S1eA5S23G0S1fS5VLX;S20S5A1A3A2A3").
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
S0S22S1cS5A1M0A1S7S31VF;S1fS30Zdb004S20S30A1A3VG1;S1eA5S23G0S1fS5VLM;S20S5A1A3A2A3").
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
  apply (jg_run A Kc c rb tp0 md0 TR KIT HKc F [0x706a0] C0 [LX] 0%nat r tp Q R_x LN_0 NX_0).
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

  assert (ZIMG : forall z, drain_zone G c cs z -> (z < 65536 \/ 6565888 <= z) /\ 0 <= z < 2 ^ 64).
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
    - eapply bandtp_mono; [|exact HB0]. intros z _ Hd. change InvLaws.segsA with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA in Hd. fold vE in Hd.
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "sym_runA"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "ss_next"; "valuation"; "reg_sv"; "swf"; "ss_facts"; "ss_objs"; "ss_lenient"; "SAlu"; "sprop_below"; "cell"; "ss_pc"; "sv_below"; "@Corelib.Init.Datatypes"; "list"; "nil"; "true"; "bool"; "cons"; "prod"; "pair"; "Some"; "option"; "false"; "app"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "beg2"; "rMS"; "sMS"; "nobj"; "vMFA"; "cX"; "idx_rot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.DrainG1"; "JDg"; "entryG"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "NXD"; "JLD"; "JD"; "O_cntD"; "O_dstD"; "dst_cells"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG"; "L_dh_g"; "Pre_dh_g"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k7.DrainG4"; "cG0"; "cCD"; "mid_okG"; "XFG"; "rupD_e"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kd.DrainG2"; "SKELG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "F_sp_high"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kk.DrainG6.GCHAIN"; "leaf_okG"; "run_okG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9"; "O_piece"; "O_shp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF"; "O_riX"; "ri_hasD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "memset_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocR10"; "a2_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR11"; "a0_e"; "@Stdlib.ZArith.BinInt.Z"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 SMGlue PrimCredit PrimCreditLaws SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillBits DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocR8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineMallocR10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.SpineMallocR11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.RebuildD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.DrainG1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kd.DrainG2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kh.DrainG3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k7.DrainG4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kk.DrainG5.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

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
S0S22S1aS5A1M0A1S7S26VF;S1eS27Z3f124S1bS27A1A3S44Vn;A1S1cA5S21G0S1eS5VL1;S1bS5A1A3A2A3").
Hypothesis LN_1 : ltac2:(tb__ "0|0|
S0S1dS14S3S44Vn;A1A1A1S23A3").
Hypothesis M_1 : ltac2:(tb__ "0|0|
S46VF;U8S1eS27Z3f404S1bS27A1A3S4S0S4R1S6VL2;A1A3LL';S6VL1;A1A5").

Hypothesis W_fm : ltac2:(tb__ "0|0|
S0S1dS11S3VC0;A1A1S1cA3").
Hypothesis D_fm : ltac2:(tb__ "0|4|
S0S22S1fS1aS1fSaSaA2M0A1M1S1aScA1M2A2M3A1S43S3S6VL2;A1A1S3VC0;A1A2S21G3S20G1G2S1eG0S20SaSaS48Vn;A1S15S55S2cSdZ40000A1A3A4S1bG0A1A3S1bScA1A4A2A3").

Hypothesis R_x : ltac2:(tb__ "0|1|
S0S22S1aS5A1M0A1S7S26VF;S1eS27Z706a0S1bS27A1A3VC0;S1cA5S21G0S1eS5VLX;S1bS5A1A3A2A3").
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
S0S22S1aS5A1M0A1S7S26VF;S1eS27Zdb004S1bS27A1A3VG1;S1cA5S21G0S1eS5VLM;S1bS5A1A3A2A3").
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
S5dVF;S1eS27Z3f5d4S1bS27A1M0A3S46VF;U16S1eS27Z3ef78G0A3S5cA4S45Vn;VRL;A2A4").

Theorem drain_growth_chain : ltac2:(tb__ "0|0|
SfS1aS38Q40A1A1VTR;S33S26S35VA;VKc;Vc;Vrb;Vtp0;Vmd0;U0A7S40Vn;A1R2R1A5VQ;A2Ftp;Fr;").
Proof.
  intros r tp.

  apply (jg_restate A Kc c rb tp0 md0 TR KT (Pre_dh_g n) (ax_S (cG0 n)) _ _ 0%nat r tp Q W_0 D_0 ltac:(apply Pos.eqb_refl)).
  { intros tr md (HFz & _) _. split; [constructor | exact (xfg_holds n A c rb tp0 md0 HE r HFz)]. }
  change (ax_setS (Pre_dh_g n) (ax_S (cG0 n))) with (cG0 n).
  apply (jg_run A Kc c rb tp0 md0 TR KT HKc F [0x3f124] (cG0 n) [L1] 0%nat r tp Q R_1 LN_1 ltac:(reflexivity)).
  intros L r1 [<-|[]] _.
  apply (g_mid n A Kc c rb tp0 md0 TR KT HKc HE F 8 [0x3f404] (fun L' => L' = la_state L2) (la_state L1) 0%nat r1 tp Q M_1).
  intros L' r2 tp2 ->.

  apply (jg_restate A Kc c rb tp0 md0 TR KT (la_state L2) (ax_S C0) _ _ 0%nat r2 tp2 Q W_fm D_fm ltac:(apply Pos.eqb_refl)).
  { intros tr md (HFz & _) _. split; [|constructor]. unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    exact (rupD_val n A c rb tp0 md0 HE r2 HFz). }
  change (ax_setS (la_state L2) (ax_S C0)) with C0.
  apply (g_piece_full n A Kc c rb tp0 md0 TR KT HKc HE F C0 LX LM R_x LN_0 NX_0 W_x D_x SK_x XF_x XX_x NX_x IC_x R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x
           R_m LN_g NX_g SK_m XF_m XX_m W_mr D_mr W_mc E_ms CHK_ms NF_ms NX_ms FBC_ms FBT_ms ND_r NO_r OB_r r2 tp2 Q).
  intros r3 tp3. fold RL.
  apply (g_carve_dst n A Kc c rb tp0 md0 TR KT HE RL r3 tp3 Q SK_c XF_c XX_c W_c).
  apply (g_runs F [0x3f5d4] (mid_okG F 22 [0x3ef78] leaf_okG) (cCD n RL) 3%nat r3 tp3 T_5).
  intros L5 r5 tp5 M5.
  apply (g_mid n A Kc c rb tp0 md0 TR KT HKc HE F 22 [0x3ef78] leaf_okG L5 3%nat r5 tp5 Q M5).
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
Module F0A_hbN_madv.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sobj"; "valuation"; "eval"; "obj_range"; "ranges_disjoint"; "reg_sv"; "ss_objs"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "sec_chunk"; "aa_geom"; "ag_spacebeg"; "aa_sec"; "ag_ctx"; "ag_thread"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_tail"; "TPIN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail"; "MB"; "EBEG"; "ELEN"; "ME"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4"; "chunk_sh_zone"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "add"; "modulo"; "pow"; "sub"; "@Corelib.Init.Datatypes"; "Some"; "false"; "list"; "option"; "pair"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MadviseA"; "madvise_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue"; "fam_ok"; "@Stdlib.Lists.List"; "In"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import PaidMunmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SysCallA MmapA MmapFixedA MmapFixedA2 MmapNodesA MadviseSpecA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_env.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require le.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_tail.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section MadvPre.
Variables (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Variables (A : AA) (rho1 : valuation) (i : nat) (ch : sec_chunk) (f : nat) (TZ : Z -> Prop).
Hypothesis HZT : ltac2:(tb__ "0|0|
S2S1cVch;R1A2VTZ;R2A1F_;Fz;").
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Let JH : jpredA := ltac2:(tb__ "0|0|
S29S17S1cVch;A1VTZ;S2aVnW;S2bS23VA;VKc;Vrho1;A6A4").
Hypothesis HI : ltac2:(tb__ "0|0|
S0S25ScA1S2eScSfVA;A1Vi;A3S22ScVch;A2A3").
Hypothesis CH : CHFh ch.
Hypothesis HFAM : ltac2:(tb__ "0|0|
S2cVf;SeSdVA;A1A1Vh;Vmsz;A4").
Hypothesis HPIN : ltac2:(tb__ "0|3|
S1S0S13Q40M0A1M1S3Vrho1;P97A2S12G0S11SdVA;A1M2A1A2A3S1S0G1S3Vrho1;P98A2S12G0S10G2A1A2A3S0G1S3Vrho1;P9bA2S12G0SeG2A1A2A3A2A2").
Variable EMd : axst.
Hypothesis NA0 : ltac2:(tb__ "0|0|
S0SbS9S15VEMd;A1ZaA2S19A3").
Hypothesis NAX : ax_X EMd = [].
Let nlit : Z := ltac2:(tb__ "0|0|
S21S1bVh;Vmsz;A2S18Vh;A1A2").

Lemma madv_num : ltac2:(tb__ "0|1|
S5S16Vch;R1A2S1S0S2S14Q40S6R2S1aA2A2Vnlit;A3S1S0S2S1fVnlit;Z1000A2Z0M0A3S1S1dG0Vnlit;A2S1dVnlit;S20Z2Z3eA2A2A2A2A2F_;Fr;").
Proof.
  intros r (EH & EM). destruct CH as (CH1 & CH2 & CH3 & CH4 & CH5). fold h msz in CH1, CH2, CH3, CH4, CH5.
  destruct (mrange_facts h msz ltac:(lia) CH1 CH2 CH3) as (M1 & M2 & M3 & M4 & M5). fold nlit in M5.
  assert (EB : eval r EBEG = Z_to_bv 64 (MB h)) by (apply eval_EBEG; [unfold vH; cbn [eval]; exact EH | lia]).
  assert (EE : eval r EEND = Z_to_bv 64 (ME h msz)) by (apply eval_EEND; [unfold vH; cbn [eval]; exact EH | unfold vMS; cbn [eval]; exact EM | lia | lia | lia]).
  pose proof (Z.div_pos msz 8 ltac:(lia) ltac:(lia)) as MD0. pose proof (Z.div_lt_upper_bound msz 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as MD1.
  pose proof (Sh_in_band h ltac:(lia)) as SB1. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in SB1.
  assert (SHE : Sh (h + msz) = Sh h + msz / 8) by (apply Sh_add8; [exact (mod8_of_4096 _ CH1) | exact (mod8_of_4096 _ CH2)]).
  split; [|split; [exact M5 | unfold nlit; lia]].
  unfold ELEN. rewrite (U_sub r _ _ (ME h msz) (MB h) EE EB ltac:(lia) ltac:(lia)). unfold nlit. apply Z.mod_small. lia.
Qed.

Lemma madv_pre : ltac2:(tb__ "0|2|
S5S24S13Q40A1M0A1S16Vch;R2A2S4S2dS4R1SaS15VEMd;A1A1A3S8S7R5R2A2S26S2S2S18Vh;A1M1S1eG1Vnlit;A2A4A2F_;Fo;S28S17VJH;VJH;VEMd;R4R3G0S27L_;Vnlit;A8F_;F_;Ftp;Fr;").
Proof.
  intros r tp (EH & EM) DISJ. unfold madvise_pre. intros tr ms md Hsp HJ. cbv zeta.
  destruct CH as (CH1 & CH2 & CH3 & CH4 & CH5). fold h msz in CH1, CH2, CH3, CH4, CH5. destruct HPIN as (P151 & P152 & P155).
  destruct (mrange_facts h msz ltac:(lia) CH1 CH2 CH3) as (M1 & M2 & M3 & M4 & M5). fold nlit in M5.
  assert (EB : eval r EBEG = Z_to_bv 64 (MB h)) by (apply eval_EBEG; [unfold vH; cbn [eval]; exact EH | lia]).
  pose proof (Z.div_pos msz 8 ltac:(lia) ltac:(lia)) as MD0. pose proof (Z.div_lt_upper_bound msz 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as MD1.
  pose proof (Sh_in_band h ltac:(lia)) as SB1. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in SB1.
  assert (SHE : Sh (h + msz) = Sh h + msz / 8) by (apply Sh_add8; [exact (mod8_of_4096 _ CH1) | exact (mod8_of_4096 _ CH2)]).
  destruct (pending_argsA segsA r tp EMd tr ms md Hsp) as (G0 & _). rewrite NA0, EB in G0. rewrite G0. rewrite (u64_lit (MB h)) by lia.
  rewrite tp_dontneed_keep.
  destruct HJ as (rp & (Hag & HA & HUW & HLV & HK & Htp & HBD & Htop) & (BW & BL & BOUT & BIN & BRM)).

  set (rpK := rho_sets rp [(156%positive, Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize))]).
  assert (ERM : rm rpK = rm rp) by (unfold rpK; apply rm_rho_sets).
  assert (OTH : forall v, v <> 156%positive -> rw rpK v = rw rp v) by (intros v Hv; unfold rpK; rewrite rho_sets_other; [reflexivity | cbn; intros [E|[]]; congruence]).
  assert (RP : forall v, (v < GW)%positive -> rw rp v = rw rho1 v) by (intros v Hv; symmetry; exact (proj1 Hag v Hv)).
  assert (HK0 : K0 Kc A rpK tp tr md).
  { split; [|split; [exact HK|split; [|split]]].
    - pose proof (AInvA_Q A rp tp md HA) as HQ. unfold AInvQ in *. rewrite ERM. exact HQ.
    - unfold tp_ok in *. rewrite OTH by discriminate. exact Htp.
    - unfold top_high in *. unfold V_DEPTH in *. rewrite !OTH by discriminate. exact Htop.
    - unfold rigidQ. rewrite !OTH by discriminate. rewrite !RP by (unfold GW; lia). split; [exact P151|]. split; [exact P152|]. split; [exact P155|].
      unfold rpK. apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]. }
  destruct (kq_facts segsA (K0 Kc) (K0_laws Kc HKc) A rpK tp _ _ HK0) as [HG _ _ _ _ _ _ _ _ _ _ _ _].
  pose proof (geom_old _ HG) as GO. destruct GO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSB & _).
  assert (FSH : (LOW_SHADOW_BEG <= Sh h /\ Sh h + msz / 8 <= SHADOW_GAP_BEG) \/ (HIGH_SHADOW_BEG <= Sh h /\ Sh h + msz / 8 <= HIGH_SHADOW_END)).
  { rewrite <- SHE. unfold Sh, SHADOW_OFF, LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END in *.
    pose proof (Z.div_pos h 8 ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound (h + msz) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as D1.
    destruct f as [|[|f']]; cbn [fam_ok] in HFAM.
    - left. pose proof (Z.div_le_upper_bound (h + msz) 8 268430848 ltac:(lia) ltac:(lia)). lia.
    - right. pose proof (Z.div_le_lower_bound h 8 2199291686912 ltac:(lia) ltac:(lia)). lia.
    - right. pose proof (Z.div_le_lower_bound h 8 2199291686912 ltac:(lia) ltac:(lia)). lia. }
  destruct (ks_madvise_ok segsA (K0 Kc) (K0_sec Kc HKc) A rpK tp tr md HK0 (Z_to_bv 64 (MB h)) nlit) as [GATE LAZY].
  { rewrite u64_lit by lia. unfold PG. exact M1. } { unfold PG. exact M5. } { unfold nlit. lia. }
  { rewrite u64_lit by lia. unfold nlit. unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END in *. lia. }
  rewrite (u64_lit (MB h)) in LAZY by lia.
  split; [unfold page_size; exact M1|]. split; [unfold nlit; lia|]. split; [exact GATE|]. split; [exact LAZY|]. split; [exact DISJ|].
  split; [intros rr y Hin; rewrite NAX in Hin; destruct Hin|].

  set (aw := Z_to_bv 64 (MB h)). set (nw := Z_to_bv 64 nlit).
  set (r4 := set_rm r (splice (rm r) (rereserve_bytes tp) aw nw)). set (v2 := view segsA (rm r)). set (v4 := view segsA (rm r4)).
  assert (INR : forall z, 0 <= z < 2 ^ 64 -> SysStep.in_range aw nw (Z_to_bv 64 z) = true <-> MB h <= z < MB h + nlit).
  { intros z Hz. rewrite SysStep.in_range_spec. unfold aw, nw. rewrite !u64_lit by (unfold nlit; lia). tauto. }
  assert (PAID : forall z, MB h <= z < MB h + nlit -> rm r (Z_to_bv 64 z) <> None -> page_mem (page_base (Z_to_bv 64 z)) tp = true).
  { intros z Hz Hd. destruct (smatch_pendingA_mem segsA r tp EMd tr ms md Hsp) as (_ & _ & HMF).
    assert (OUT : outside_all r (ss_objs (ax_S EMd)) (Z_to_bv 64 z)).
    { apply Forall_forall. intros o Ho. pose proof (DISJ o Ho) as D. unfold SymState.ranges_disjoint in D. cbn [fst snd] in D. cbv zeta. rewrite u64_lit by (unfold nlit in Hz; lia). lia. }
    pose proof (HMF _ OUT) as E. rewrite vms_mem in E. pose proof (LAZY (Z_to_bv 64 z) ltac:(rewrite u64_lit by (unfold nlit in Hz; lia); exact Hz)) as LZ.
    unfold hid in E. rewrite LZ in E. cbn [andb] in E. destruct (page_mem (page_base (Z_to_bv 64 z)) tp); [reflexivity|]. cbn [negb] in E. exfalso. apply Hd. rewrite <- E. reflexivity. }
  pose proof (ks_repr segsA (K0 Kc) (K0_sec Kc HKc) A rpK tp tr md HK0) as (SC1 & _). rewrite ERM in SC1.
  destruct (SC1 i ch HI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PSH). fold h msz in PSH. rewrite SHE in PSH.
  assert (INSH : forall z, MB h <= z < MB h + nlit -> chunk_sh_zone ch z) by (intros z Hz; unfold chunk_sh_zone; fold h msz; rewrite SHE; unfold nlit in Hz; lia).
  assert (PSH2 : forall z, MB h <= z < MB h + nlit -> exists b, v2 z = Some b).
  { intros z Hz. destruct (PSH z ltac:(unfold nlit in Hz; lia)) as [b Hb]. pose proof (BIN z (INSH z Hz) ltac:(rewrite Hb; discriminate)) as X. unfold v2. destruct (view segsA (rm r) z) as [b2|]; [eexists; reflexivity | exfalso; apply X; reflexivity]. }
  assert (V4IN : forall z, MB h <= z < MB h + nlit -> v4 z = Some (Z_to_bv 8 0)).
  { intros z Hz. assert (Hz' : 0 <= z < 2 ^ 64) by (unfold nlit in Hz; lia). destruct (PSH2 z Hz) as [b Hb]. unfold v2 in Hb. rewrite view_in in Hb by lia.
    pose proof (rd_off_image (rm r) z b ltac:(lia) Hb) as Hm.
    unfold v4, r4. rewrite view_in by lia. unfold rd_of. cbn [rm set_rm]. unfold splice. rewrite (proj2 (INR z Hz') Hz). unfold rereserve_bytes.
    rewrite (PAID z Hz ltac:(rewrite Hm; discriminate)). reflexivity. }
  assert (V4OUT : forall z, ~ (MB h <= z < MB h + nlit) -> v4 z = v2 z).
  { intros z NZ. unfold v4, v2. apply view_agree. intros Hz. unfold r4. cbn [rm set_rm]. unfold splice.
    destruct (SysStep.in_range aw nw (Z_to_bv 64 z)) eqn:EI; [exfalso; exact (NZ (proj1 (INR z Hz) EI)) | reflexivity]. }
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  pose proof (JF_stable nW UStopLe false A Kc rho1 (stopJ_stable_le _) HKc) as HST.
  exists rp. split.
  - apply (HST rp rp tp tr md (madvise_dontneed_next md aw nw)); [split; [intros v0 _; reflexivity | split; [intros l0; reflexivity | intros x; reflexivity]] | | exact (conj Hag (conj HA (conj HUW (conj HLV (conj HK (conj Htp (conj HBD Htop)))))))].
    apply (mat_equiv_dontneed segsA md tp aw nw HMI). intros x Hx. apply LAZY. unfold aw, nw in Hx. rewrite !u64_lit in Hx by (unfold nlit; lia). exact Hx.
  - split; [intros v0; cbn [rw set_rm]; exact (BW v0)|]. split; [intros l0; cbn [rl set_rm]; exact (BL l0)|]. split.
    + intros z NZ. change (v4 z = view segsA (rm rp) z). rewrite V4OUT by (intros Hz; exact (NZ (INSH z Hz))). exact (BOUT z NZ).
    + split.
      * intros z HZ Hp. change (v4 z <> None). destruct (Z_le_dec (MB h) z) as [L1|L1]; [destruct (Z_lt_dec z (MB h + nlit)) as [L2|L2]|];
          [rewrite (V4IN z (conj L1 L2)); discriminate | rewrite V4OUT by lia; exact (BIN z HZ Hp) | rewrite V4OUT by lia; exact (BIN z HZ Hp)].
      * intros a0 NT. rewrite <- (BRM a0 NT). unfold r4. cbn [rm set_rm]. unfold splice.
        destruct (SysStep.in_range aw nw a0) eqn:EI; [|reflexivity]. exfalso. apply NT. apply HZT. apply INSH.
        pose proof (bv_unsigned_in_range _ a0) as RA. change (bv_modulus 64) with (2 ^ 64) in RA.
        apply (INR (bv_unsigned a0) RA). rewrite Z_to_bv_bv_unsigned. exact EI.
Qed.
End MadvPre.
End F0A_hbN_madv.

(* [comment removed for export] *)
Module F0A_hbN_nodes.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "proj1"; "conj"; "proj2"; "iff"; "not"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv_unsigned"; "bv"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sv"; "eval"; "valuation"; "sobj"; "obj_range"; "ranges_disjoint"; "rm"; "ss_objs"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "div"; "pow"; "sub"; "mul"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "sec_chunk"; "sc_map_beg"; "aa_geom"; "sc_map_size"; "aa_sec"; "ag_spacebeg"; "ag_ctx"; "ag_thread"; "aa_live"; "ag_pab"; "sc_size"; "@Corelib.Init.Datatypes"; "bool"; "list"; "pair"; "true"; "length"; "prod"; "Some"; "false"; "option"; "app"; "cons"; "fst"; "nat"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws"; "N8"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_maps"; "Model"; "TASK_SIZE"; "event"; "map_has"; "map_remove"; "page_size"; "region_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kPtrArrayReserve"; "PG"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "round_up"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail"; "MB"; "ME"; "ELEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4"; "chunk_sh_zone"; "chunk_zone"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_gpr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MadviseA"; "madvise_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "shadow_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert"; "hbvar_ok"; "hf_SC"; "hv_EMd"; "hv_EUd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lg.F0A_hbN_disj"; "hbdisj_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kw.F0A_hbN_scan"; "ENVXs"; "hbnums"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_unmap"; "JH2"; "JPh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue"; "fam_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states"; "vMS"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SysCallA MmapFixedA MmapNodesA MunmapSymA MadviseSpecA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_env F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require le.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_hbN_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.F0A_hbN_step OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_entry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_hbN_stepU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kv.F0A_hbN_scand OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kw.F0A_hbN_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lg.F0A_hbN_disj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kk.F0A_hbN_madv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_unmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Nodes.
Variables (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Variables (A : AA) (rho1 : valuation) (l1 l2 : list (Z * Z)) (p n : Z) (i : nat) (ch lst : sec_chunk) (f : nat) (l : bool) (TZ : Z -> Prop).
Variables (cf : hbfam) (cv : hbvar).
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Hypothesis HLV : ltac2:(tb__ "0|1|
S0S2aS2eSbSbA2M0A1S26VA;A1S32G0Vl1;S33G0S2bSbSbVp;Vn;A4Vl2;A3A3A3").
Hypothesis HPR : is_primary n = false.
Hypothesis HI : ltac2:(tb__ "0|0|
S0S31S1eA1S3aS1eS22VA;A1Vi;A3S2fS1eVch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
S0SbVp;S15S15S1fVch;A1S46A2Z800A2A3").
Hypothesis HSZ : ltac2:(tb__ "0|0|
S0SbS28Vch;A1S15S49Vn;Z8A2Z1000A2A3").
Hypothesis HN : 1 <= n.
Hypothesis HNB : ltac2:(tb__ "0|0|
S16S15Z1800S38Vn;A1A2S21Vch;A1A2").
Hypothesis Hf : (f <= 2)%nat.
Hypothesis HFAM : ltac2:(tb__ "0|0|
S69Vf;S23S20VA;A1A1S1fVch;A1S21Vch;A1A4").
Hypothesis Hl : ltac2:(tb__ "0|1|
S0S31S1eA1S3aS1eS22VA;A1M0S3bS2dS1eG0A2U1A2A3S2fS1eVlst;A2A3").
Hypothesis HLI : ltac2:(tb__ "0|0|
S6S0S29Vl;S2cA3S0S35Vi;S3bS2dS1eS22VA;A1A2U1A2A3A2").
Hypothesis CH : CHFh ch.
Hypothesis BND : ltac2:(tb__ "0|1|
S2S16S15S1fVch;A1M0S21Vch;A1A2S48A2S16S47G0A2A2").
Hypothesis LSTOFF : ltac2:(tb__ "0|2|
S0S29Vl;S30A3S2S16S15S1fVlst;A1M0Z20A2S1fVch;A1M1A2S16S15G1S21Vch;A1A2G0A2A2F_;").
Hypothesis PABOFF : ltac2:(tb__ "0|2|
S2S16S15S27S20VA;A1A1M0S45A2S1fVch;A1M1A2S16S15G1S21Vch;A1A2G0A2A2").
Hypothesis NCB : ltac2:(tb__ "0|0|
S16S1cZ8S1dS2dS1eS22VA;A1A2A1A2S45A2").
Hypothesis HPIN : ltac2:(tb__ "0|4|
S1S0SaQ40M0A1M1ScVrho1;P97A2S8G0S25S20VA;A1M2A1A2A3S1S0G1ScVrho1;P98A2S8G0S24G2A1A2A3S1S0G1ScVrho1;P9bA2S8G0S23G2A1A2A3S1S0G1ScVrho1;PcA2S8G0Vp;A2A3S1S0G1ScVrho1;P69A2S8G0S38Vn;A1M3A2A3S0G1ScVrho1;P6aA2S8G0S19G3Z8A2A2A3A2A2A2A2A2").
Hypothesis HNUM : ltac2:(tb__ "0|0|
S64VA;Vp;Vn;Vi;Vch;A5").
Hypothesis F1 : FCH1 nW rho1.
Hypothesis SF : hbscanF_ok nW cf.
Hypothesis VOK : ltac2:(tb__ "0|0|
S5eS5fVcf;A1Vf;Vl;Vcv;A4").
Hypothesis DJ : ltac2:(tb__ "0|0|
S62VnW;Vl;Vcv;A3").
Hypothesis HZT_sh : ltac2:(tb__ "0|0|
SbS4dVch;R1A2VTZ;R2A1F_;Fz;").
Hypothesis HZTc : ltac2:(tb__ "0|0|
SbS4eVch;R1A2VTZ;R2A1F_;Fz;").
Let JH1 : jpredA := ltac2:(tb__ "0|0|
S5dS37S4dVch;A1VTZ;S67VnW;S68S30VA;VKc;Vrho1;A6A4").
Let JP : jpredA := ltac2:(tb__ "0|0|
S66VnW;VKc;VA;Vrho1;Vi;Vch;Vlst;Vl;VTZ;A9").
Let J2 : jpredA := ltac2:(tb__ "0|0|
S65VKc;VA;Vrho1;Vl1;Vl2;Vi;Vch;VTZ;A8").
Let ENVX : valuation -> Prop := ltac2:(tb__ "0|0|
S63VA;Vi;Vch;Vl;Vlst;A5").
Let HPIN3 : ltac2:(tb__ "0|3|
S1S0SaQ40M0A1M1ScVrho1;P97A2S8G0S25S20VA;A1M2A1A2A3S1S0G1ScVrho1;P98A2S8G0S24G2A1A2A3S0G1ScVrho1;P9bA2S8G0S23G2A1A2A3A2A2") := ltac2:(tb__ "0|b|
S4S0SaQ40M0A1M1ScVrho1;P97A2S8G0S25S20VA;A1M2A1A2A3M3S1S0G1ScVrho1;P98A2S8G0S24G2A1A2A3M4S0G1ScVrho1;P9bA2S8G0S23G2A1A2A3M5A2S3G3S1G4S1G5S1S0G1ScVrho1;PcA2S8G0Vp;A2A3S1S0G1ScVrho1;P69A2S8G0S38Vn;A1M6A2A3S0G1ScVrho1;P6aA2S8G0S19G6Z8A2A2A3A2A2M7A2M8A2M9VHPIN;A3S4G4G5S3G4G8S5G3G9VHPIN;A3MaA3S3G5G7S5G4G8GaA3A3A4A4").

Lemma N_madv_num : ltac2:(tb__ "0|2|
SfVENVX;R1A1S1S0SbS9Q40SeR2S4cA2A2S1bS4bVh;Vmsz;A2S4aVh;A1A2M0A3S1S0SbS18G0Z1000A2Z0M1A3S1S17G1G0A2S17G0S1aZ2Z3eA2A2A2A2A2F_;Fr;").
Proof. intros r (_ & E202 & E203 & _). exact (madv_num ch CH r (conj E202 E203)). Qed.

Lemma N_madv_pre : ltac2:(tb__ "0|1|
SfS2aSaQ40A1M0A1VENVX;R2A1S56S37VJH1;VJH1;S60Vcv;A1R3R2G0S2cL_;S1bS4bVh;Vmsz;A2S4aVh;A1A2A8F_;Ftp;Fr;").
Proof.
  intros r tp EX. pose proof EX as (P0 & E202 & E203 & _).
  pose proof (v_EMdnode _ f l cv VOK) as (_ & _ & NA0 & _ & _ & NAX & _).
  intros tr ms md Hsp HJ.
  pose proof (zenv_at nW Kc HKc A rho1 p n i ch f TZ HI HU HSZ HN HNB Hf HPIN cf SF r tp tr md HJ P0 F1) as ZE.
  exact (madv_pre nW Kc HKc A rho1 i ch f TZ HZT_sh HI CH HFAM HPIN3 (hv_EMd cv) NA0 NAX r tp (conj E202 E203)
           (DISJ4_hb nW A p n i ch l lst cv HNUM Hl HLI HI DJ r ZE EX) tr ms md Hsp HJ).
Qed.

Lemma N_mun_num : ltac2:(tb__ "0|2|
SfVENVX;R1A1S1S0SaQ40M0A1SeR2S6aA2S8G0Vmsz;A2A3S1S0SbS18Vmsz;Z1000A2Z0M1A3S1S17G1Vmsz;A2S17Vmsz;S1aZ2Z3eA2A2A2A2A2F_;Fr;").
Proof. intros r (_ & _ & E203 & _). destruct CH as (C1 & C2 & C3 & C4 & C5). split; [exact E203|]. split; [exact C2|]. unfold msz. fold h in C4, C5. clear -C3 C4 C5. lia. Qed.

Lemma N_mun_pre : ltac2:(tb__ "0|d|
SfS2aSaQ40M0A1M1A1VENVX;R2A1S2aS40A1M2S4fS3eS5cS37R6R5S61Vcv;A1M3S2bG2S51R3S52R2R1A2A4A5VJP;R7R6R4R2A4S50R4U0A2G1S1S0SbS18S9G0R1A2M4S43A2Z0A3S1S16S15G4Vmsz;A2M5S3fA2S1S0S29S41S3dS3cR4A1A1M6R1S8G0Vmsz;A2M7A3S2cA3S1G1S39S2eG1G1A2S2bG1G1R2R1A4S3dS3cR5A1A1A3S0G1R2G7A3F_;Fs;S1S0S29S44S42G6R1A2R1G7A3S2cA3S1S10S39S10R1S14S58G3A1A1A3S12S11RbR2A2S2bSbSbS9G0R3A2M8S15G8Vmsz;A2A4A2F_;Fo;S1S2eSdSdA2M9SbS39G9R2S59G3A1A3S1S16S9G0SeRcS34SdSdR3A3A2A2MaR2A2S17R2S15GaS9G0SeRcS36SdSdR3A3A2A2A2A2A2S7S1S16S9G0R5A2MbS9G0S5bS9G0SeRdS5aG3A1A2A2R3A2A2McA2S17GcS15GbVmsz;A2A2A2A1F_;F_;Fy;Frr;VJ2;S55R9S54S13R9A1R1G7A3A2S57G4G5R8A3R6S53R4R1G7A3A4A2A2A2A2A2A2A2Ta;F_;F_;Fmd;Fms;Ftr;F_;Ftp;Fr;").
Proof.
  intros r tp EX tr ms md Hsp HJP. pose proof EX as (P0 & E202 & E203 & _).
  pose proof (v_EUdnode _ f l cv VOK) as (_ & _ & NA0 & _ & NAX & _).
  assert (ZE : zenv nW A p n ch r).
  { destruct HJP as (rp & HJF & BR & _). destruct HJF as (Hag & HA & _ & _ & HK & Htp & _ & Htop).
    apply (zenv_rw nW A rho1 p n i ch HU HN HNB HPIN HNUM (FCHs_below_SF nW cf SF) F1 r).
    - intros v Hv. rewrite (proj1 BR v). symmetry. exact (proj1 Hag v Hv).
    - intros l0. rewrite (proj1 (proj2 BR) l0). symmetry. exact (proj1 (proj2 Hag) l0).
    - unfold top_high in *. unfold V_DEPTH in *. rewrite !(proj1 BR). exact Htop. }
  destruct CH as (C1 & C2 & C3 & C4 & C5).
  assert (CH4 : 0x643000 <= sc_map_beg ch /\ 0 < sc_map_size ch /\ sc_map_beg ch + sc_map_size ch < 2 ^ 47
                /\ (sc_map_beg ch + sc_map_size ch <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= sc_map_beg ch))
    by (split; [exact C4 | split; [clear -C3; lia | split; [exact C5 | exact BND]]]).
  exact (mun_pre nW Kc HKc A rho1 l1 l2 p n i ch lst l TZ HZTc HLV HPR HI HU Hl (proj1 HLI) (HLF_of A i ch HI l HLI)
           CH4 C1 LSTOFF PABOFF NCB HPIN3 (hv_EUd cv) NA0 NAX r tp E202
           (HDISJ_hb nW A p n i ch l lst cv HNUM Hl HLI HI DJ r ZE EX) tr ms md Hsp HJP).
Qed.
End Nodes.
End F0A_hbN_nodes.

(* [comment removed for export] *)
Module F0A_hbN_qsz.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sprop"; "sprop_below"; "sv"; "rm"; "ss_facts"; "ss_next"; "ss_objs"; "swf"; "valuation"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "div"; "lt"; "@Corelib.Init.Datatypes"; "andb"; "list"; "bool"; "nat"; "pair"; "prod"; "true"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_thread"; "aa_q_thread"; "ag_ctx"; "ag_spacebeg"; "sc_map_beg"; "sc_map_size"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert"; "hv_LR"; "hbvar_ok"; "hv_PT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states"; "O_qsz"; "F_qsz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "qsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "zdisjb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_entry"; "ZUH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kk.F0A_hbN_qsz"; "ZD_qsz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kw.F0A_hbN_scan"; "hbnums"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kv.F0A_hbN_scand"; "FCHs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_unmap"; "DUZh"; "JH2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_hbN_zones"; "zd_allb"; "zds_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "kQuarantineCacheMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel"; "addo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop"; "with_obj"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_env F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require le.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_hbN_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.F0A_hbN_step OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_entry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_hbN_stepU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kv.F0A_hbN_scand OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kw.F0A_hbN_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lg.F0A_hbN_disj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_unmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ZD_qsz : zdesc := ltac2:(tb__ "0|0|
S18S19S17SfA2SfS18S17SfU1Z68A4Z70A4").
Definition qsz_chk (nW : nat) (cv : hbvar) : bool := ltac2:(tb__ "0|6|
S14S14S14S14S15S19S6S6A2M0A1M1S16Lx;S28S29Vcv;A1M2A1S1aG0G1S1cLl;Lp;X15x2SbS42S27G2A1M3S2cA2A1A2S39VnW;S33SaG3A1M4A3A2S25S31S32S34A1S3aVnW;G4A2A3A2S25S4S5S9S27S41G2S2cA2A1M5A1A1S1bS4S8G5A1S2dA3A3A2").

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
S35VA;Vp;Vn;Vi;Vch;A5").
Hypothesis FCHB : ltac2:(tb__ "0|0|
S0S16S25S4S5S40A1S36VnW;A1A3S1aA3").
Hypothesis F1 : FCH1 nW rho1.

Hypothesis LFq : ltac2:(tb__ "0|1|
S1S3dS3fS1dS7Vrho1;A1A2S3eS10S1fS1eVA;A1A1Z68A2U8S2fS20VA;A1A1M0A3A2S1S11Z0G0A2S11G0S3cA2A2A2").
Hypothesis HZ_T : ltac2:(tb__ "0|1|
SfS1S11S1fS1eVA;A1A1M0R1A2S13R1S10G0Z1000A2A2A2S2S37VA;Vi;Vch;R2A4A1F_;Fz;").
Hypothesis P123 : ltac2:(tb__ "0|1|
S0SeQ40M0A1S3Vrho1;P7bA2SdG0S2fS20VA;A1A1A2A3").
Let JH2' : jpredA := ltac2:(tb__ "0|0|
S38VKc;VA;Vrho1;Vl1;Vl2;Vi;Vch;VTZ;A8").

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

