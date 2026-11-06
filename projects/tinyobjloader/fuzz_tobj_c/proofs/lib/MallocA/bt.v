(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec2 ac CertMallocST.

(* [comment removed for export] *)
Module SpineMallocSec3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "not"; "@Corelib.Init.Datatypes"; "list"; "bool"; "nil"; "app"; "true"; "prod"; "cons"; "pair"; "option"; "Some"; "None"; "fst"; "length"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "rw"; "sprop"; "eval"; "ss_facts"; "ss_next"; "ss_objs"; "rl"; "SLit"; "sprop_below"; "swf"; "cell"; "mkObj"; "obj_range"; "rm"; "DUnknown"; "ranges_disjoint"; "SVar"; "holds"; "DZero"; "agree_below"; "image_byte"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_setS"; "ax_X"; "mkLeafA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "modulo"; "sub"; "pow"; "mul"; "land"; "of_nat"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ageom"; "budget_bound"; "aa_ptr_committed"; "aa_sec"; "ag_ctx"; "ag_pab"; "ag_spacebeg"; "ag_thread"; "budget_ok_alloc"; "sec_chunk"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.SEC3"; "JGs"; "GS"; "slink"; "SKEL0"; "JGsC"; "clsP"; "pgq"; "noband"; "npg"; "range_noband"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "ulink"; "UStopLeOrPc"; "ustop"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "Kc_ok"; "unwind_stopJ"; "A_globals"; "top_high"; "tp_ok"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "stableA"; "liftKA"; "smatchA"; "LQA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "Sh"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "IMG_HI"; "round_up"; "HIGH_SHADOW_BEG"; "HIGH_SHADOW_END"; "LOW_SHADOW_BEG"; "SHADOW_GAP_BEG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "secneeded"; "rhoM_of"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST"; "carveS"; "B2"; "L1"; "L2"; "B1"; "F_map"; "Pret_ms"; "a0e2"; "a2e1"; "a2e2"; "O_1"; "fx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "MSENT";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "V_MS"; "RT_sec"; "V_NCH"; "V_NRES"; "V_NS"; "V_PAB"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "geom_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "budget_boundD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv"; "bumpV"; "JGsC"; "SHC"; "pendS"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "prim_credit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "rt_zoneG"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Placement StartLib StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocST.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SEC3.
Variable nW : nat. Variable st : ustop. Variable tmax : Z. Variable hi : bool.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Variable nx : positive.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S0S14Sa5VW;Vst;Vtmax;A3Vnx;A3").
Hypothesis NXG : ltac2:(tb__ "0|0|
S0S6S92S9bVnx;A2S9A3").

Variable AX : AA -> AA.
Hypothesis AXg : ltac2:(tb__ "0|0|
S41S0S43S42VAX;R1A1A1S42R1A1A3FX;").
Hypothesis AXb : ltac2:(tb__ "0|0|
S41S0S13S44VAX;R1A1A1S44R1A1A3FX;").
Definition GS : positive := Pos.succ nx.

Lemma GW_le_nx : (GW <= nx)%positive.
Proof. apply Pos.leb_le. exact NXG. Qed.
Lemma nx_lt_GS : (nx < GS)%positive.
Proof. unfold GS. apply Pos.lt_succ_diag_r. Qed.
Lemma GW_lt_GS : (GW < GS)%positive.
Proof. eapply Pos.le_lt_trans; [exact GW_le_nx | exact nx_lt_GS]. Qed.
Lemma lt_GW_GS : ltac2:(tb__ "0|0|
S14S93R1S9bA2S93R2S50A2F_;Fi;").
Proof. intros i Hi. eapply Pos.lt_trans; [exact Hi | exact GW_lt_GS]. Qed.

Definition JGs (A : AA) (Kc : KcA) (rho : valuation) (a : word) : jpredA := ltac2:(tb__ "0|2|
S16S5S3fQ40M0A1M1A1S5S7dA1S7cS3eG0S18Vrho;PcA2A2S13S1S2bS9bS7bVA;Vrho;A2R5A3S1S0G1S18R5Vnx;A2Va;A3S1Sa6Vsegs;VAX;Sa9VA;R1A2A1R5R4R2A5S1SacVA;S3eG0Va;A2S78R1A1R2A4S1VKc;R3R2A2S1S64VA;R5A2S1S61VW;Vst;R5A3S1S1S34Zfc01R1A2S37R1S3aZ2Z27A2A2A2S1S63VA;R5A2S4bVA;R1A2A2A2A2A2A2A2A2A2A2Tnv;Lmd;Ltr;Ltp;Lr;").
Definition JGsC (A : AA) (Kc : KcA) (rho : valuation) (a : word) : jpredA := ltac2:(tb__ "0|2|
S16S5S3fQ40M0A1A1S5S7dA1S7cS3eG0S18Vrho;PcA2A2S13S1S4fVA;VKc;Vrho;Va;R5R4R3R2A8S34S35S35SafR2R4A2Sb2VAX;Sa9VA;R1A2A1M1A1A2SabR1A1A2Sa8G1A1A2A2Tnv;Lmd;Ltr;Ltp;Lr;").

Lemma JGsC_of_Sec : ltac2:(tb__ "0|1|
S41S59S16S3fQ40A1M0S16S5G0A1S5S7dA1S7cS41S0S41VAX;R1A1R1A3FX;SaaVW;Vst;Vtmax;R9R8R7R6R5R4R3R2AbS53RaR9R8R7R6R5R4R3A8F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof. intros A Kc rho a r tp tr md AXid H. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv.JGsC, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv.JGs in H. rewrite Hnx in H. unfold JGsC, JGs. rewrite !AXid. rewrite (PrimCredit.prim_credit_same A (bumpV A (bv_unsigned (rw rho 12%positive))) eq_refl). exact H. Qed.

Definition slink (ua L : Z) (rho rho' : valuation) : Prop := ltac2:(tb__ "0|a|
S1S14S0S3fQ40M0A1M1S18Vrho';R1A2S18Vrho;R1A2A3Fi;S1S14S0S5S3fQ8A1M2A1S1eVrho';R1A2S1eVrho;R1A2A3Fl;S1G1S3S0SdG2A1M3S25Vrho';R1A2M4S25Vrho;R1A2M5A3S3S1S0G3G5SfG2A1M6A3S1S0G3S2cS91R1A2G6A3S1S34S71S3eG0R1A2M7A2S37G7S70A2A2A2A2S1S1S34S6fVua;A1M8G7A2S37G7S35G8S36VL;Z8A2A2M9A2A2S4S0G3G4G6A3A1A2A2A2Fa;S13S1S34G8R1A2S37R1G9A2A2S4S0G3S25Vrho';S40G0R2A2A2G6A3A1F_;Fz;A2A2A2").

Lemma slink_trans : ltac2:(tb__ "0|0|
S13S13S16S16S16S51R5R4R3R2A4S51R6R5R3R2A4S51R7R6R5R3A4F_;F_;Fr3;Fr2;Fr1;FL;Fua;").
Proof.
  intros ua L r1 r2 r3 (W1 & L1 & M1 & D1) (W2 & L2 & M2 & D2).
  split; [intros i; rewrite W2; apply W1|]. split; [intros l; rewrite L2; apply L1|]. split; [|exact D2].
  intros a. destruct (M2 a) as [E2|[(N2 & I2 & B2)|(R2 & S2)]].
  - rewrite E2. destruct (M1 a) as [E1|[X|X]]; [left; exact E1 | right; left; exact X | right; right; exact X].
  - destruct (M1 a) as [E1|[(N1 & I1 & B1)|(R1 & S1)]].
    + right. left. rewrite <- E1. exact (conj N2 (conj I2 B2)).
    + right. left. exact (conj N1 (conj I2 B2)).
    + exfalso. exact (S1 N2).
  - right. right. exact (conj R2 S2).
Qed.

Lemma JGs_rigidS : ltac2:(tb__ "0|5|
S41S59S16S3fQ40M0A1M1S16S5G1A1S5S7dA1S7cS4fR8R7R6R5R4R3R2R1A8S3eG0S18R7PcM2A2M3A2S13S42RaA1S43S1S0G1G3S18R9G2A2A3S1S0G1S18R7Vnx;A2R8A3S1S0G1S18R7Sa3A2S40G0S7aR2A1A2A3S1S0G1S18R7S9fA2S40G0S78R2A1A2A3S1S0G1S18R7P97A2S40G0S4aR1A1A2A3S1S0G1S18R7P98A2S40G0S47R1A1A2A3S1S0G1S18R7P9bA2S40G0S49R1A1A2A3S1S0G1S18R7Sa4A2S40G0S48R1A1A2A3S1S0G1S18R7Sa2A2S40G0S36S45RbA1Z8A2A2A3S1S0G1S18R7Sa1A2S40G0S3dS11S4cS46RbA1A2A1A2A3S1G1S0SdS3fQ8A1M4A1S25R8R1A2S25RaR1A2A3Fx;S14S0S5G4A1S1eR8R1A2S1eRaR1A2A3Fl;A2A2A2A2A2A2A2A2A2A2A2TG;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ. destruct HJ as ((Hagw & Hagl & Hagm) & Ha & _).
  cbn zeta. unfold V_NS, V_MS, V_PAB, V_NRES, V_NCH.
  repeat match goal with |- _ /\ _ => split end;
    try (rewrite <- (Hagw _) by (unfold GW; lia); reflexivity).
  - exact Ha.
  - intros x. rewrite <- (Hagm x). reflexivity.
  - intros l. rewrite <- (Hagl l). reflexivity.
Qed.

Lemma JGs_K : ltac2:(tb__ "0|1|
S41S59S16S3fQ40A1M0S16S5G0A1S5S7dA1S7cS4fR8R7R6R5R4R3R2R1A8R8R3R2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof. intros A Kc rho a r tp tr md HJ. destruct HJ as (_ & _ & _ & _ & HK & _). exact HK. Qed.
Lemma JGsC_K : ltac2:(tb__ "0|1|
S41S59S16S3fQ40A1M0S16S5G0A1S5S7dA1S7cS53R8R7R6R5R4R3R2R1A8R8R3R2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof. intros A Kc rho a r tp tr md [HJ _]. exact (JGs_K _ _ _ _ _ _ _ _ HJ). Qed.

Lemma stopJ_rwrl : ltac2:(tb__ "0|1|
S16S16S14S0S3fQ40A1S18R3R1A2S18R2R1A2A3Fi;S14S0S5S3fQ8A1A1S1eR4R1A2S1eR3R1A2A3Fl;S61VW;Vst;R4A3M0G0F_;F_;F_;Fr';Fr;").
Proof.
  intros r r' Hw Hl H. unfold unwind_stopJ in *. destruct W as [|u us]; [exact H|]. destruct st; [exact H|].
  destruct (last_link (SVar 28) (u :: us)) as [[bp nbp] pc]. rewrite !(eval_ext_rwrl r' r) in H by assumption. exact H.
Qed.

Lemma JGs_stable : ltac2:(tb__ "0|0|
S41S59S16S3fQ40A1S79VW;Vst;A2S60R4A1S69Vsegs;S50S4fR6R5R4R3A4A3F_;F_;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a HUS HKc r r' tp tr md md' Hag Hme HJ.
  pose proof Hag as (Hw & Hl & Hm). pose proof GW_lt_GS as LT. pose proof nx_lt_GS as LT2.
  destruct HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HB).
  assert (Erm : rm r' = rm r) by (apply functional_extensionality; intros x; symmetry; apply Hm).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact HN|split; [|exact HB]]]]]]]]].
  - destruct Hagr as (A1 & A2 & A3). split; [|split].
    + intros i Hi. rewrite (A1 i Hi). apply Hw. exact (lt_GW_GS i Hi).
    + intros l. rewrite (A2 l). apply Hl.
    + intros x. rewrite (A3 x). apply Hm.
  - rewrite <- (Hw nx LT2). exact Ha.
  - unfold AInvA in HA |- *. rewrite Erm. fold (AInvA segs (AX (bumpV A (bv_unsigned (rw rho 12%positive)))) r tp md') (AInvA segs (AX (bumpV A (bv_unsigned (rw rho 12%positive)))) r tp md) in *.
    eapply AInvA_mat; [exact HA | exact Hme].
  - destruct Hme as ((mat' & ->) & _). unfold pendS in HP |- *. rewrite m_vmmaps_with_vm_backing. exact HP.
  - destruct Hme as ((mat' & ->) & _). rewrite with_vm_backing_with_vm. apply HKc. exact HK.
  - unfold tp_ok in Htp |- *. rewrite <- (Hw 24%positive) by (apply lt_GW_GS; unfold GW; lia). exact Htp.
  - apply (HUS r r'); [|exact HU]. eapply agree_below_le; [|exact Hag]. pose proof GW_lt_GS. unfold GW, NF in *. lia.
  - unfold top_high in Htop |- *. rewrite <- (Hw 10%positive), <- (Hw V_DEPTH) by (apply lt_GW_GS; unfold GW, V_DEPTH; lia). exact Htop.
Qed.
Lemma JGsC_stable : ltac2:(tb__ "0|0|
S41S59S16S3fQ40A1S79VW;Vst;A2S60R4A1S69Vsegs;S50S53R6R5R4R3A4A3F_;F_;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a HUS HKc r r' tp tr md md' Hag Hme [HJ HC].
  split; [exact (JGs_stable A Kc rho a HUS HKc r r' tp tr md md' Hag Hme HJ)|].
  destruct Hme as (_ & Hpaid & _). rewrite Hpaid. exact HC.
Qed.

Lemma AInvA_boundD : ltac2:(tb__ "0|0|
S41S16S5S3fQ40A1A1S7cSa6S91R4R3R2R1A5S34Sa8R5A1S44R5A1A2F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (_ & _ & _ & _ & _ & HD & _). unfold depot_wf in HD.
  destruct HM as (_ & PB & VL & V0 & K0 & F0 & _ & _ & _ & _ & _ & _ & DN & PC & _).
  apply budgetD_le_budget; [| |exact DN|exact PC|exact K0|exact F0].
  - exact (dep_cost_bound_mem _ _ HD).
  - exact (dm_F_NFBLK _ _ HD).
Qed.

Lemma Sh_add8 : ltac2:(tb__ "0|1|
S13S13S0S13S38R1Z8M0A2Z0A3S0S13S6fS35R3R2A2A1S35S6fR3A1S36R2G0A2A2A3F_;Fb;Fa;").
Proof. intros a b Hb. unfold Sh. rewrite (Z.div_mod b 8) at 1 by lia. rewrite Hb, Z.add_0_r. rewrite Z.mul_comm, Z.div_add by lia. lia. Qed.

Definition npg (lo h2 : Z) : Z := ltac2:(tb__ "0|1|
S35S39S36S39Vh2;Z1M0A2S6eA2S36Vlo;S6eA2A2G0A2").
Definition pgq (lo : Z) : Z := ltac2:(tb__ "0|0|
S3bS6eS36Vlo;S6eA2A2").
Lemma pg_run : ltac2:(tb__ "0|4|
S13S13S34Z0M0R2A2S37R3R2A2S1S34S55R4A1M1R4A2S1S34R3S35G1S3bS6eS57R4R3A2M2A2A2M3A2S1S0S13S38G1S6eA2G0A3S1S1S34G0G2A2S34G2S35S36S39R3R4A2S6eA2Z2A2A2A2S1S37R4S35G1S6eA2A2S37G3S35R3S6eA2A2A2A2A2A2A2F_;F_;Fh2;Flo;").
Proof.
  intros lo h2 H0 Hlt. unfold npg, pgq, PG.
  pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
  pose proof (Z.div_mod (h2 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (h2 - 1) 4096 ltac:(lia)).
  pose proof (Z.div_mod (h2 - lo) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (h2 - lo) 4096 ltac:(lia)).
  assert (lo / 4096 <= (h2 - 1) / 4096) by (apply Z.div_le_mono; lia).
  repeat split; try lia.
Qed.

Definition clsP (h : bool) (ua L : Z) : Prop := ltac2:(tb__ "0|0|
S6OLh;Vh;S34S70Vua;A2S34S35Vua;VL;A2S71A2X6x2").
Lemma shadow_run_band : ltac2:(tb__ "0|1|
S6S13S13S54R3R2R1A3S34S72R3A2S37Z0R3A2S34S35R5R4A2Z7fffff800000A2S55S6fR6A1A1S13S35S55S6fR7A1M0A1S3bS6eS57G0S35G0S36R6Z8A2A2A2A2A2S13S1S6OLh;R9S1S34S74R2A2S34R1S75A2A2S1S34S76R2A2S34R1S77A2A2X6x2S1S34Z646000R2A2S1S34R1S3aZ2Z40A2A2S1S34S71R2A2S34R1S70A2A2A2A2A2Th2;Tlo;F_;F_;F_;F_;FL;Fua;Fh;").
Proof.
  intros h ua L HC Himg HL Htop lo h2.
  assert (R : Sh ua < Sh ua + L / 8 \/ L / 8 = 0) by (pose proof (Z.div_pos L 8); lia).
  pose proof (Z.div_mod L 8 ltac:(lia)). pose proof (Z.mod_pos_bound L 8 ltac:(lia)).
  unfold clsP in HC. unfold Sh, SHADOW_OFF, IMG_HI, HIGH_SHADOW_BEG, HIGH_SHADOW_END, LOW_SHADOW_BEG, SHADOW_GAP_BEG, SHADOW_BAND_LO, SHADOW_BAND_HI, HIGH_SHADOW_END, LOW_SHADOW_BEG in *.
  subst lo h2. unfold npg, pgq, PG.
  pose proof (Z.div_mod ua 8 ltac:(lia)). pose proof (Z.mod_pos_bound ua 8 ltac:(lia)).
  set (s := ua / 8 + 2147450880) in *.
  pose proof (Z.div_mod s 4096 ltac:(lia)). pose proof (Z.mod_pos_bound s 4096 ltac:(lia)).
  pose proof (Z.div_mod (s + L / 8 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (s + L / 8 - 1) 4096 ltac:(lia)).
  destruct h; lia.
Qed.

Definition SKEL0 : list sobj := ltac2:(tb__ "0|0|
S8S15S8S15S8S15SbS15Sb1S8S15S65VW;A1S62A3A3Sb0A3Sa0A3SbS15S23S28Vnx;A1S1fZ0A1S28S9fA1S7S22A1S2aA5S7S15A1A3A3").
Definition noband (x : Z) : Prop := ltac2:(tb__ "0|0|
S3S37Vx;S71A2S34S70Vx;A2A2").
Definition range_noband (r : Z * Z) : Prop := ltac2:(tb__ "0|0|
S13S1S34S10S13S13Vr;A3R1A2S37R1S12S13S13Vr;A3A2A2S56R2A1F_;Fx;").

Lemma rt_zoneG_noband : ltac2:(tb__ "0|0|
S43S13Sa7R2A1Sb3R3R2A2S56R3A1F_;F_;Fx;FG;").
Proof.
  intros G x HG Hz. pose proof (geom_bands G HG) as (FB & TB & CB & DB & _). rewrite FS_total_val in FB.
  unfold noband. unfold rt_zoneG in Hz. rewrite FS_total_val in Hz. unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  destruct Hz as [Z1|[Z2|[Z3|[Z4|Z5]]]]; [clear -Z1; lia | clear -Z2 TB; lia | clear -Z3 CB; lia | clear -Z4 DB; lia | clear -Z5 FB; lia].
Qed.

Lemma objs_noband : ltac2:(tb__ "0|4|
S2eS5S15A1M0G0S41S59S16S3fQ40A1M1S16S5G1A1S7eS0S5cVst;S5bA3S0S5S5aA1VW;S7S5aA1A3F_;S67Vsegs;S4fR8R7R6R5A4RbR4R3R2A6S0S5SaSaS17S17A2S17A2M2A1M3S4dS15G2S66S1dS2dRcA1A1A4S4dS15G2S66S8S15RbS8S15S52RaA3A3A4A3S84S19S8S19S5fVW;Vst;A2S5eS5dA1A3S1bS2dRdA1A1A3S2G0G0S2G0G0S2G0G0S1S0G0S1dS2dR11A1A1S8S15R3S8S15R2R1A3A3A3S1S0G3S4dS15G2S66R3A4S4dS15G2S66R10A4A3S1S0G3S4dS15G2S66R1A4S4dS15G2S66RfA4A3S4eS15S15S58S24RbR1A2A1Lo;R2A3A2A2A2Ll2;A2Ll1;A2Ll0;A2F_;F_;F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;FP;FP0;FX;").
Proof.
  intros X P0 P A Kc rho a rhoX tp w HW Hsp SKP FC. destruct w as [tr [ms md]].
  rewrite map_app in SKP. destruct (map_eq_app _ _ _ _ SKP) as (l0 & l12 & EO0 & SK0' & SKP').
  rewrite map_app in SKP'. destruct (map_eq_app _ _ _ _ SKP') as (l1 & l2 & EO12 & SK & SK2).
  exists l0, l1, l2. split; [rewrite EO0, EO12; reflexivity|]. split; [exact SK0'|]. split; [exact SK2|].
  pose proof (proj2 Hsp) as HJ. pose proof (JGs_rigidS A Kc rho a rhoX tp tr md HJ) as (E12 & Enx & E141 & E142 & E151 & E152 & E155 & _).
  destruct HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HB).
  pose proof HA as (HG & _). rewrite AXg in HG. cbn [aa_geom bumpV] in HG.
  pose proof (geom_nums _ HG) as (F1 & F2 & F0 & T1 & T2 & T0' & C1 & C2 & D1 & D2 & S1 & S2 & S0 & TG).
  pose proof (smatchA_smatch segs _ _ _ _ (proj1 Hsp)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFall.
  assert (HFX : forall p, In p (unwind_factsS W st ++ pre_facts malloc_depth) -> holds rhoX p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFall p (FC p Hp)). }
  assert (Hhigh : holds rhoX F_sp_high) by (apply HFX; apply in_or_app; right; cbn; tauto).
  assert (Hall : Forall (obj_holds segs rhoX (vms md tp ms)) l1).
  { destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). rewrite EO0, EO12 in Hall.
    apply Forall_app in Hall as [_ Hall]. apply Forall_app in Hall as [Hall _]. exact Hall. }
  unfold SKEL0 in SK. cbn [app] in SK.
  destruct (skel_head _ sw_s1 _ SK) as (o0 & rest & EO & SK0 & SKR).
  subst l1.
  pose proof (sw_range_holds segs rhoX _ _ o0 Hall ltac:(left; reflexivity) SK0 Hhigh) as (SW1 & SW2 & SW3).
  constructor.
  { intros x Hx. unfold noband, SHADOW_BAND_HI, HIGH_SHADOW_END. right. clear -SW1 Hx. lia. }
  apply (Forall_ranges_skel rhoX range_noband _ _ SKR).
  assert (SW0 : topG (aa_geom A) <= fst (obj_range rhoX o0)) by (rewrite (sw_lo_gen rhoX o0 SK0); exact Htop).
  apply Forall_app. split.
  2:{
    apply Forall_cons; [|apply Forall_nil].
    pose proof HP as (_ & _ & HL & DI & _). destruct DI as (_ & _ & _ & _ & WB).
    pose proof (secmapsize_bounds (bv_unsigned (rw rho 12%positive)) ltac:(clear -HN; lia)) as [SMB _].
    assert (SO : soff rhoX (SVar V_MS) = secmapsize (bv_unsigned (rw rho 12%positive))).
    { unfold soff. cbn [eval]. rewrite E142, signed_lit. unfold snorm. rewrite Z.mod_small by (clear -SMB HN; lia).
      destruct (Z.ltb_spec (secmapsize (bv_unsigned (rw rho 12%positive))) (2 ^ 63)); clear -SMB HN H; lia. }
    intros x Hx. unfold obj_range, obj_lo_of, obj_hi_of in Hx. cbn [ob_base ob_lo ob_hi fst snd] in Hx.
    rewrite SO, soff_lit_small in Hx by lia. cbn [eval] in Hx. rewrite Enx in Hx.
    unfold noband. clear -WB Hx. lia. }
  apply Forall_app. split.
  2:{
    unfold RT_sec. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
    rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_sec_small k Hk)).
    intros x Hx. apply (rt_zoneG_noband (aa_geom A) x HG). apply (N_sec_zone (aa_geom A) rhoX k x E151 ltac:(clear -T1 T2 TG; lia) Hk). exact Hx. }
  apply Forall_app. split.
  2:{
    rewrite <- N_m1_ok. apply Forall_forall. intros o Ho'. apply in_map_iff in Ho' as (k & <- & Hk).
    rewrite (carve_range rhoX k (proj1 (Forall_forall _ _) N_m1_small k Hk)).
    intros x Hx. apply (rt_zoneG_noband (aa_geom A) x HG). apply (N_m1_zoneG (aa_geom A) rhoX k x HG E151 E152 Hk). exact Hx. }
  apply Forall_app. split.
  2:{
    unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI. repeat apply Forall_cons; try apply Forall_nil;
      intros x Hx; rewrite obj_range_mk in Hx by lia; cbn [fst snd eval] in Hx; rewrite u64_lit in Hx by lia;
      unfold noband, SHADOW_BAND_LO, LOW_SHADOW_BEG; left; lia. }

  assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rhoX (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG (aa_geom A))); [|clear -SW0 SW2 SW3; lia|clear -TG; lia]. apply Forall_forall. intros p Hp.
    assert (Hp' : In p (unwind_factsS W st)).
    { destruct st; [apply chain_pre_in; exact Hp|]. exfalso. clear -Hp HW. unfold W in *. rewrite (HW eq_refl) in Hp. destruct Hp. }
    apply HFX. apply in_or_app; left. exact Hp'. }
  eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
  intros x Hx. rewrite obj_range_mk in Hx by (clear -B; lia). cbn [fst snd] in Hx. unfold noband, SHADOW_BAND_HI, HIGH_SHADOW_END. right. clear -B Hx TG. lia.
Qed.

Lemma carve_piece : ltac2:(tb__ "0|4|
S2eS17S17S41S59S16S16S3fQ40M0A1M1S16S5G1A1S7eS3eG0S18R5PcA2A2S13S85RcS23RbS1fZ0A1RaS7S22A1S26A5A2S2eS51S3eG0R6A2S78R2A1R8R7A4S67Vsegs;S4fRbRaR8R7A4ReR6R5R4A6S0S6S21S2dR3A1A1S9A3S0S5SaS17S17A2M2A1S32R10A1S7G2A1A3S34S6fS3eG0RaA2A1S3eG0S1aR9R10A2A2A2S34S35S3eG0S1aRaR11A2A2S3eG0S1aRaR10A2A2A2S35S6fS3eG0RbA2A1S36S78R7A1Z8A2A2A2S4eS15S15S27S24RcR1A2ScS13S13S3eG0S1aRcR13A2A2M3S35G3S3eG0S1aRcR12A2A2A2A4A2Lo;S1dS2dR13A1A1A3S67Vsegs;S4fR11R10ReRdA4R8RcRbRaA6F_;F_;F_;F_;F_;F_;F_;TCO;Tnv;Fw;Ftp;FrhoX;Fa;Frho;Frho0;FKc;FA;FL;FB;FC;").
Proof.
  intros C B L A Kc rho0 rho a rhoX tp w nv CO SL Hsp WCO XC HB1 HB2 DJ. destruct w as [tr [ms md]].
  pose proof (proj2 Hsp) as HJ. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJ.
  pose proof (JGs_rigidS A Kc rho a rhoX tp tr md HJ) as (E12 & Enx & E141 & E142 & _ & _ & _ & _ & _ & _ & Erm & Erl).
  destruct HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HBud). fold nv in HN.
  pose proof (secmapsize_bounds nv ltac:(clear -HN; lia)) as [SMB SMM].
  pose proof (urange a) as Ra. pose proof (urange (eval rhoX B)) as RB. pose proof (urange (eval rhoX L)) as RL.
  set (b := bv_unsigned (eval rhoX B)) in *. set (l := bv_unsigned (eval rhoX L)) in *.
  assert (L8 : secmapsize nv / 8 <= nv / 8 + 1537) by (clear -SMB; pose proof (Z.div_le_mono (secmapsize nv) (nv + 12295) 8 ltac:(lia) ltac:(lia)); rewrite <- Z.div_add by lia; lia).
  assert (SO0 : soff rhoX (SLit 0) = 0) by (apply soff_lit_small; lia).
  assert (SOL : soff rhoX L = l) by (unfold soff; rewrite signed_small; [reflexivity|]; clear -HB1 HB2 L8 HN RB; subst l; lia).
  destruct SL as (_ & _ & _ & DEF).
  unfold CO, carveS. eapply (SPA_carve_unk segs (JGs A Kc rho a) rhoX C tp _ B (SLit 0) L (ss_next (ax_S C)) Hsp WCO (Pos.le_refl _));
    rewrite ?SO0, ?SOL; fold b.
  - clear -RL; lia.
  - clear -HB1 HB2 L8 HN; lia.
  - clear -RB; lia.
  - clear -HB1 HB2 L8 HN Ra; unfold Sh, SHADOW_OFF in *. pose proof (Z.div_lt_upper_bound (bv_unsigned a) 8 (2 ^ 61) ltac:(lia) ltac:(lia)). lia.
  - rewrite Z.add_0_r. exact DJ.
  - intros z Hz. rewrite Z.add_0_r in Hz.
    pose proof (DEF z ltac:(clear -Hz HB1 HB2; lia)) as D. rewrite <- (Erm (Z_to_bv 64 z)) in D.
    unfold wok_of, rd_of. destruct (rm rhoX (Z_to_bv 64 z)) as [x|]; [|exfalso; exact (D eq_refl)]. split; [reflexivity | exists x; reflexivity].
  - intros rr y j Hin. rewrite XC in Hin. destruct Hin.
Qed.

Lemma pieces_disjoint : ltac2:(tb__ "0|6|
S2eS5S15A1M0G0S41S59S16S3fQ40A1M1S16S5G1A1S7eS13S13S0S5cVst;S5bA3S0S5S5aA1VW;S7S5aA1A3F_;S67Vsegs;S4fRaR9R8R7A4RdR6R5R4A6S0S5SaSaS17S17A2S17A2M2A1M3S4dS15G2S66S1dS2dReA1A1A4S4dS15G2S66S8S15RdS8S15S52RcA3A3A4A3S84S19S8S19S5fVW;Vst;A2S5eS5dA1A3S1bS2dRfA1A1A3S34S71R6A2S34R6S70A2G0S0G3S4dS15G2S66R1A4S4dS15G2S66R12A4A3M4S4eS15S15S27S24ReR1A2ScS13S13RbRaA4A2Lo;M5R2A3F_;Fl;G0G4S4eS15S15S27S24RfR1A2ScS13S13RcRbA4A2Lo;R2A3F_;Fl;S4eS15G5S1dS2dR14A1A1A3F_;F_;F_;F_;F_;F_;F_;F_;Fh2;Flo;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;FP;FP0;FX;").
Proof.
  intros X P0 P A Kc rho a rhoX tp w lo h2 HW Hsp SK FC HLO HHI HP0 HP.
  destruct (objs_noband X P0 P A Kc rho a rhoX tp w HW Hsp SK FC) as (l0 & l1 & l2 & EO & SK0' & SK2 & NB).
  rewrite EO. apply Forall_app. split; [exact (HP0 l0 SK0')|]. apply Forall_app. split; [|exact (HP l2 SK2)].
  eapply Forall_impl; [|exact NB]. intros o Ho. unfold ranges_disjoint, range_noband, noband in *. cbn [fst snd].
  destruct (obj_range rhoX o) as [olo ohi]. cbn [fst snd] in Ho |- *.
  destruct (Z_le_dec ohi olo) as [E|E]; [left; exact E|].
  destruct (Z_le_dec ohi lo) as [E2|E2]; [right; right; left; exact E2|].
  destruct (Z_le_dec h2 olo) as [E3|E3]; [right; right; right; exact E3|].
  destruct (Z_le_dec h2 lo) as [E4|E4]; [right; left; exact E4|].
  exfalso. destruct (Ho (Z.max olo lo) ltac:(clear -E E2 E3 E4; lia)) as [Y|Y]; clear -Y E E2 E3 E4 HLO HHI; lia.
Qed.

Section MS.
Variables (E C CO T : axst) (B L : sv) (P0 P : list sobj).
Variables (Pre Pret : axst) (Posts : list leafA) (s : wsub) (R : list sobj).
Hypothesis HPosts : ltac2:(tb__ "0|0|
S0S5S2fA1VPosts;SbS2fS33VPret;SaeA2S7S2fA1A3A3").
Hypothesis Hsum : ltac2:(tb__ "0|0|
S7eOF_;S6dS16S5S3fQ40A1A1S68Vsegs;R4R3A3S69Vsegs;S96R4A3S7fVsegs;R6S67Vsegs;R5VPre;R4R3A5S6cVsegs;R5S96R4R3VPosts;A6A4F_;F_;Ftp;Frho;FJx;Fok;").
Hypothesis NPre : ltac2:(tb__ "0|0|
S0S14S1cS2dVPre;A1A1S96A3").

Hypothesis RS : ltac2:(tb__ "0|1|
S41S59S16S3fQ40A1M0S16S5G0A1S7eS0S5cVst;S5bA3S0S5S5aA1VW;S7S5aA1A3F_;S67Vsegs;S4fR8R7R6R5A4VE;R4R3R2A6S67Vsegs;S4fR9R8R7R6A4VC;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Hypothesis HBL : ltac2:(tb__ "0|a|
S41S59S16S3fQ40M0A1M1S16S5G1A1S7eS67Vsegs;S4fR7R6R5R4A4VC;R3R2R1A6S1S34S6fS3eG0R5A2A1M2S3eG0S1aR4VB;A2A2M3A2S1S34S35G3S3eG0S1aR4VL;A2A2A2S35G2S36S78S3eG0S18R6PcA2A2A1Z8A2A2A2S1S5S15A1M4S0S5SaSaS17S17A2S17A2M5A1M6S4dS15G5S66R1A4M7S4dS15G5S66VP0;A4A3S4eS15S15S27S24R7R1A2ScS13S13S3eG0S1aR7VB;A2A2M8S35G8S3eG0S1aR7VL;A2A2A2A4A2Lo;R2A3M9F_;Fl;G4S0G6G7S4dS15G5S66VP;A4A3G9F_;Fl;A2A2A2F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").

Hypothesis SKC : ltac2:(tb__ "0|1|
S0S5SaSaS17S17A2S17A2M0A1S4dS15G0S66S1dS2dVC;A1A1A4S4dS15G0S66S8S15VP0;S8S15S52VP;A3A3A4A3").
Hypothesis FCC : ltac2:(tb__ "0|0|
S84S19S8S19S5fVW;Vst;A2S5eS5dA1A3S1bS2dVC;A1A1A3").
Hypothesis XC : ax_X C = [].
Hypothesis HCO : ltac2:(tb__ "0|0|
S0S2eS85VC;S23VB;S1fZ0A1VL;S7S22A1S26A5A2VCO;A3").
Hypothesis WCO : ltac2:(tb__ "0|0|
S0S6S21S2dVCO;A1A1S9A3").
Hypothesis He : ltac2:(tb__ "0|1|
S0SdS5S15A1M0A1S99VCO;VPre;Vs;A3SeG0VR;A2A3").
Hypothesis Hchk : ltac2:(tb__ "0|0|
S0S6S98VCO;VPre;Vs;VR;S4dS2fS2eS30VPosts;A4A5S9A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S0S2eS9aVs;VPre;VPret;VCO;VR;A5VT;A3").
Hypothesis FBC : ltac2:(tb__ "0|1|
S0S6S83S19S20S1cS2dVCO;A1M0A1A1S1bG0A1A3S9A3").
Hypothesis FBT : ltac2:(tb__ "0|0|
S0S6S83S19S20S1cS2dVT;A1A1A1S1bS2dVCO;A1A1A3S9A3").
Hypothesis NXC : ltac2:(tb__ "0|0|
S0S6S92S50S1cS2dVCO;A1A1A2S9A3").

Lemma ms_step : ltac2:(tb__ "0|4|
S7eOF_;S41S59S16S16S3fQ40M0A1M1S5G1A1M2S80S0S5cVst;S5bA3S0S5S5aA1VW;S7S5aA1A3F_;S79VW;Vst;A2S60R8A1S68Vsegs;RbS6aR9A1A3S51S3eG0R7A2S78S3eG0S18R8PcA2A2A1R9R8A4S16G2S7fVsegs;RfS67Vsegs;S4fReRdRbRaA4M3S97VT;S1bS2dVCO;A1A1A2R2R1A5R8A4FtpY;FrhoY;S16S7fVsegs;RfS67Vsegs;G3VE;R1R9A5R8A4FrhoX;F_;F_;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 rho a tp Q HW HUS HKc Hokf SL HD rhoX.
  pose proof (JGs_stable A Kc rho a HUS HKc) as HST.

  apply (triple_conseq (P:=SPA segs (JGs A Kc rho a) CO rhoX tp) (SPA segs (JGs A Kc rho a) E rhoX tp) (Q:=Q)); [intros w Hw | intros w Hw; exact Hw |].
  { pose proof (RS A Kc rho a rhoX tp w HW Hw) as HC.
    destruct (HBL A Kc rho a rhoX tp w HC) as (HB1 & HB2 & HDP0 & HDP).
    rewrite <- HCO. apply (carve_piece C B L A Kc rho0 rho a rhoX tp w SL HC); [rewrite HCO; exact WCO | exact XC | exact HB1 | exact HB2 |].
    destruct w as [trw [msw mdw]]. pose proof (proj2 HC) as HJc. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJc.
    destruct HJc as (_ & _ & _ & HPc & _ & _ & _ & HNc & _). pose proof HPc as (_ & _ & HLc & DIc & _). destruct DIc as (D0c & _ & DTc & _).
    pose proof (topG_range (aa_geom A)) as TG. pose proof (urange a) as Ra.
    pose proof (Sh_in_band (bv_unsigned a) ltac:(clear -Ra DTc TG HLc; lia)) as SB.
    apply (pieces_disjoint C P0 P A Kc rho a rhoX tp _ _ _ HW HC SKC FCC); [| |exact HDP0|exact HDP].
    - clear -SB HB1. lia.
    - eapply Z.le_trans; [exact HB2|]. clear -DTc TG Ra HLc. unfold Sh, SHADOW_OFF, SHADOW_BAND_HI, HIGH_SHADOW_END in *.
      pose proof (Z.div_le_mono (bv_unsigned a + secmapsize (bv_unsigned (rw rho 12%positive))) 140737479966720 8 ltac:(lia) ltac:(lia)).
      assert (DS : bv_unsigned a / 8 + secmapsize (bv_unsigned (rw rho 12%positive)) / 8 <= (bv_unsigned a + secmapsize (bv_unsigned (rw rho 12%positive))) / 8).
      { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (bv_unsigned a) 8). pose proof (Z.mul_div_le (secmapsize (bv_unsigned (rw rho 12%positive))) 8). lia. }
      lia. }

  set (Jf := (fun (_ : valuation) t tr md => JGs A Kc rho a rhoX t tr md) : jpredA).
  assert (Jf_okf : ok_frameA segs ok Jf).
  { intros r t tr ms md msv' HJ HMI Hh Hp Hs. exact (Hokf rhoX t tr ms md msv' (JGs_K _ _ _ _ _ _ _ _ HJ) HMI Hh Hp Hs). }
  assert (Jf_st : stableA segs NF Jf).
  { intros r r' t tr md md' Hag Hme HJ. unfold Jf in *. eapply HST; [apply agree_below_refl | exact Hme | exact HJ]. }
  apply (triple_pre_pure segs ok _ _ (Forall (holds rhoX) (ss_facts (ax_S CO)))).
  { intros w Hw. exact (SPA_facts_hold segs _ rhoX CO tp w Hw). }
  intros HFC.
  apply (call_soundA segs ok (JGs A Kc rho a) Jf Jf (JGs A Kc rho a) CO Pre s R Posts Q rhoX tp He Hchk).
  - intros rho1 tp1. rewrite NPre. exact (Hsum ok Jf rho1 tp1 Jf_okf Jf_st).
  - intros tr ms md Hsm HJ. exact HJ.
  - intros Lf rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. unfold Jf in HJ'.
    eapply HST; [| apply mat_equiv_refl | exact HJ'].
    eapply agree_below_le; [apply Pos.leb_le; exact NXC | exact (proj1 HLK)].
  - intros Lf rho' tpL HinL Hag. rewrite HPosts in HinL. destruct HinL as [<-|[]]. cbn [la_state]. rewrite HT.
    eapply triple_conseq; [intros w Hw | intros w Hw; exact Hw | apply (HD rho' tpL)].
    apply SPA_refacts; [exact Hw | exact FBT |]. intros _.
    exact (Forall_holds_agree _ rhoX rho' _ Hag FBC HFC).
Qed.
End MS.

Lemma JGs_nums : ltac2:(tb__ "0|6|
S41S59S16S3fQ40M0A1M1S16S5G1A1S5S7dA1S7cS4fR8R7R6R5R4R3R2R1A8S3eG0S18R7PcA2A2S13S3eG0R7A2S13S78R2A1S13S1S1S34Zfc01R3A2S37R3S3aZ2Z27A2A2A2S1S1S34Z12000R1A2S34R1S35R3Z3007A2A2A2S1S0S13S38R1S6eA2Z0M2A3S1S0S13S38R2S6eA2G2A3S1S34S72R2A2S1S34S35R2R1A2Z7fffff800000A2S1S0S13S7aR3A1M3S35S73R3Z8M4A2M5Z1000A2A3S1S0S13R1S35S73G3S6eA2S6eA2A3S1S0S13S38G5G4A2G2A3S1S34R3G5A2S34G5S35R3Z7A2A2A2A2A2A2A2A2A2A2A2A2TL;Tua;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ. destruct HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HB). cbn zeta.
  pose proof (secmapsize_bounds (bv_unsigned (rw rho 12%positive)) ltac:(clear -HN; lia)) as [SMB SMM].
  pose proof HP as (_ & AL & HL & DI & _). pose proof (dyn_in_big _ _ _ DI ltac:(clear -SMB; lia)) as IMG. destruct DI as (_ & _ & DT & _).
  pose proof (topG_range (aa_geom A)) as TG.
  pose proof (round_up_ge' (bv_unsigned (rw rho 12%positive)) 8 ltac:(lia)) as R1. pose proof (round_up_mod (bv_unsigned (rw rho 12%positive)) 8 ltac:(lia)) as R2.
  repeat split; try assumption; try reflexivity; try (clear -HN; lia); try (clear -DT TG; lia); try (clear -R1; lia); try (clear -SMB; lia).
Qed.

Lemma site1_a2 : ltac2:(tb__ "0|1|
S41S59S16S3fQ40A1M0S16S5G0A1S5S7dA1S7cS4fR8R7R6R5R4R3R2R1A8S0G0S1aR5S8dVnx;A1A2S1aR5S1fZ200A1A2A3F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & _).
  pose proof (urange a) as Ra.
  unfold a2e1, vMAPn. cbn [eval]. rewrite Enx. apply bv_eq.
  rewrite sub_val, add_val, !srl_val, add_val, !u64_lit by lia. change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold PG in AL. set (ua := bv_unsigned a) in *.
  rewrite (Z.mod_small (ua + 4088)) by (clear -Ra TOP SMB; lia).
  replace ((ua + 4088) / 8) with (ua / 8 + 511).
  2:{ replace (ua + 4088) with (ua + 511 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  rewrite (Z.mod_small (ua / 8 + 511 + 1)) by (clear -Ra TOP SMB; pose proof (Z.div_pos ua 8); pose proof (Z.div_lt_upper_bound ua 8 (2 ^ 61)); lia).
  rewrite Z.mod_small by (clear -Ra; pose proof (Z.div_pos ua 8); lia). lia.
Qed.

Lemma site1_bounds : ltac2:(tb__ "0|4|
S41S59S16S3fQ40M0A1M1S16S5G1A1S5S7dA1S7cS4fR8R7R6R5R4R3R2R1A8S1S0S13S3eG0S1aR5S89Vnx;A1A2A2S6fS3eG0R6A2A1M2A3S1S0S13S3eG0S1aR5S87A2A2Z200M3A3S34S35G2G3A2S35G2S36S78S3eG0S18R7PcA2A2A1Z8A2A2A2A2A2F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS A Kc rho a r tp tr md HJ) as (E12 & Enx & _).
  pose proof (JGs_nums A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & _).
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.
  split; [|split].
  - unfold B1, shS, vMAPn. cbn [eval]. rewrite Enx, add_val, srl_val, !u64_lit by (unfold SHADOW_OFF; lia). change (3 mod 64) with 3.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. fold ua. unfold Sh, SHADOW_OFF. apply Z.mod_small.
    clear -Ra TOP. pose proof (Z.div_pos ua 8). pose proof (Z.div_lt_upper_bound ua 8 (2 ^ 61)). lia.
  - unfold L1. cbn [eval]. apply u64_lit. lia.
  - pose proof (Z.div_le_mono 73728 (secmapsize (bv_unsigned (rw rho 12%positive))) 8 ltac:(lia) ltac:(clear -SMB; lia)). clear -H. cbn in H. lia.
Qed.

Lemma land_m8 : ltac2:(tb__ "0|0|
S13S1S34Z0R1A2S37R1S3aZ2Z40A2A2A2S0S13S3cR2Zfffffffffffffff8A2S39R2S38R2Z8A2A2A3F_;Fx;").
Proof. intros x Hx. change 18446744073709551608 with (2 ^ 64 - 2 ^ 3). rewrite land_high_mask by lia. reflexivity. Qed.
Lemma land_m4096 : ltac2:(tb__ "0|0|
S13S1S34Z0R1A2S37R1S3aZ2Z40A2A2A2S0S13S3cR2Zfffffffffffff000A2S39R2S38R2Z1000A2A2A3F_;Fx;").
Proof. intros x Hx. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_high_mask by lia. reflexivity. Qed.

Lemma site2_vals : ltac2:(tb__ "0|a|
S41S59S16S3fQ40M0A1M1S16S5G1A1S5S7dA1S7cS4fR8R7R6R5R4R3R2R1A8S3eG0S18R7PcA2A2S13S3eG0R7A2S13S7aR2A1S13S78R3A1S13S1S0S13S3eG0S1aR9S8cVnx;A1A2A2S35S35S6fR3A1M2S36R2Z8M3A2M4A2Z200M5A2M6A3S1S0S13S3eG0S1aR9S86Vnx;A1A2A2G6A3S1S0S13S3eG0S1aR9S8eVnx;A1A2A2S39S39S36R1G3A2M7G4A2G5A2M8A3S1S0S13S3eG0S1aR9S88A2A2G8A3S1S1S34Z0M9G8A2S34G8Z1ffA2A2S1S0S13S38R2G3A2G9A3S1S0S13S38R1G3A2G9A3S0S13S35G6G8A2S35G2G7A2A3A2A2A2A2A2A2A2TMS;TVNS;Tua;Tnv;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ.
  pose proof (JGs_rigidS A Kc rho a r tp tr md HJ) as (E12 & Enx & E141 & E142 & _).
  pose proof (JGs_nums A Kc rho a r tp tr md HJ) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  pose proof (urange a) as Ra. cbn zeta. set (nv := bv_unsigned (rw rho 12%positive)) in *. set (ua := bv_unsigned a) in *.
  set (VNS := secneeded nv) in *. set (MS := secmapsize nv) in *.
  assert (V8 : VNS mod 8 = 0) by (rewrite ENS, Z.add_mod, R8M by lia; reflexivity).
  assert (M8 : MS mod 8 = 0).
  { pose proof (Z.div_mod MS 4096 ltac:(lia)) as X. unfold PG in SMM. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (MS / 4096)) with ((512 * (MS / 4096)) * 8) by lia. apply Z_mod_mult. }
  assert (A8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(lia)) as X. unfold PG in AL. rewrite AL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by lia. apply Z_mod_mult. }
  assert (VB : 68609 <= VNS <= nv + 4103) by (rewrite ENS; clear -R8B HN; lia).
  assert (MB : VNS + 4096 <= MS <= VNS + 8191).
  { rewrite EMS. unfold PG. pose proof (round_up_ge' VNS 4096 ltac:(lia)). fold VNS in H. clear -H. lia. }
  pose proof (Z.div_mod VNS 8 ltac:(lia)) as DV. pose proof (Z.div_mod MS 8 ltac:(lia)) as DM. pose proof (Z.div_mod ua 8 ltac:(lia)) as DA.
  rewrite V8 in DV. rewrite M8 in DM. rewrite A8 in DA.
  assert (SHB : Sh ua + MS / 8 < 2 ^ 45) by (unfold Sh, SHADOW_OFF; clear -TOP DM DA Ra MB VB; lia).
  assert (EA0 : bv_unsigned (eval r (a0e2 nx)) = Sh ua + VNS / 8 + 512).
  { unfold a0e2, vMAPn. cbn [eval]. rewrite Enx, E141. rewrite add_val, srl_val, and_val, !add_val, !u64_lit by (unfold SHADOW_OFF in *; lia).
    fold ua VNS. change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (Z.mod_small (ua + 4096)) by lia. rewrite (Z.mod_small (ua + 4096 + VNS)) by lia.
    rewrite land_m8 by lia. replace (ua + 4096 + VNS) with ((ua / 8 + 512 + VNS / 8) * 8) by (clear -DA DV; lia).
    rewrite Z_mod_mult, Z.sub_0_r, Z.div_mul by lia.
    unfold Sh, SHADOW_OFF in *. rewrite Z.mod_small; clear -SHB DM DA DV MB Ra VB; lia. }
  assert (EB : bv_unsigned (eval r (B2 nx)) = Sh ua + VNS / 8 + 512).
  { unfold B2, BR, shS, vMAPn. cbn [eval]. rewrite Enx, E141.
    rewrite !add_val. rewrite !srl_val. rewrite !u64_lit by (unfold SHADOW_OFF in *; lia).
    fold ua. change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold Sh, SHADOW_OFF in *. rewrite !Z.mod_small; clear -SHB DM DA DV MB Ra VB; lia. }
  assert (EA2 : bv_unsigned (eval r (a2e2 nx)) = MS / 8 - VNS / 8 - 512).
  { unfold a2e2, msx, vMAPn. cbn [eval]. rewrite Enx, E141.
    rewrite !sub_val. rewrite !add_val. rewrite !srl_val. rewrite !and_val. rewrite ?add_val, ?and_val, ?add_val.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with (2 ^ 64 - 8) by reflexivity.
    rewrite !u64_lit by lia.
    fold ua. change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (Z.mod_small (VNS + 4095)) by lia. rewrite land_m4096 by lia.
    assert (ERU : VNS + 4095 - (VNS + 4095) mod 4096 + 4096 = MS).
    { rewrite EMS. unfold round_up, PG. pose proof (Z.div_mod (VNS + 4096 - 1) 4096 ltac:(lia)). replace (VNS + 4095) with (VNS + 4096 - 1) by lia. lia. }
    rewrite ERU. rewrite (Z.mod_small MS) by lia. rewrite (Z.mod_small (MS + ua)) by lia.
    replace ((MS + ua + (2 ^ 64 - 8)) mod 2 ^ 64) with (MS + ua - 8).
    2:{ replace (MS + ua + (2 ^ 64 - 8)) with (MS + ua - 8 + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia. }
    rewrite (Z.mod_small (ua + 4096)) by lia. rewrite (Z.mod_small (ua + 4096 + VNS)) by lia. rewrite land_m8 by lia.
    replace (ua + 4096 + VNS) with ((ua / 8 + 512 + VNS / 8) * 8) by (clear -DA DV; lia).
    rewrite Z_mod_mult, Z.sub_0_r, Z.div_mul by lia.
    replace (MS + ua - 8) with ((MS / 8 + ua / 8 - 1) * 8) by (clear -DA DM; lia). rewrite Z.div_mul by lia.
    rewrite (Z.mod_small (MS / 8 + ua / 8 - 1 + 1)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (EL : bv_unsigned (eval r L2) = MS / 8 - VNS / 8 - 512).
  { unfold L2. cbn [eval]. rewrite E141, E142. rewrite ?sub_val, ?add_val, ?srl_val, ?add_val, ?srl_val. rewrite !u64_lit by lia.
    change (3 mod 64) with 3. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite !Z.mod_small; lia. }
  repeat split; try assumption; lia.
Qed.

Section Reveal.
Variables E0 T0 : axst.
Hypothesis SKT : ltac2:(tb__ "0|1|
S0S5SaSaS17S17A2S17A2M0A1S4dS15G0S66S1dS2dVT0;A1A1A4S4dS15G0S66S52A4A3").
Hypothesis FCT : ltac2:(tb__ "0|0|
S84S19S8S19S5fVW;Vst;A2S5eS5dA1A3S1bS2dVT0;A1A1A3").
Hypothesis AF0 : ltac2:(tb__ "0|0|
S16S5S3fQ40A1A1SaS5S7dA1S94A2S6bVsegs;R3R2VE0;R1A5S4eS19S29R4A1S8aVnx;Vhi;A2A3S6bVsegs;R5R4VT0;R3A5F_;F_;Fw;Ftp;Frho;").

Lemma F_map_hold : ltac2:(tb__ "0|2|
S41S59S16S3fQ40M0A1M1S16S5G1A1S5S7dA1S7cS4fR8R7R6R5R4R3R2R1A8S54Vhi;S3eG0R6A2S78S3eG0S18R7PcA2A2A1A3S4eS19S29R6A1S8aVnx;Vhi;A2A3F_;F_;Fmd;Ftr;Ftp;Fr;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a r tp tr md HJ HC.
  pose proof (JGs_rigidS A Kc rho a r tp tr md HJ) as (E12 & Enx & E141 & E142 & _).
  destruct HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HB).
  set (nv := bv_unsigned (rw rho 12%positive)) in *. pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.
  pose proof (secmapsize_bounds nv ltac:(clear -HN; lia)) as [SMB _].
  pose proof HP as (_ & _ & HL & DI & _). pose proof (dyn_in_big _ _ _ DI ltac:(clear -SMB; lia)) as IMG.
  destruct DI as (D0 & _ & DT & _ & WB). pose proof (topG_range (aa_geom A)) as TG.
  assert (EUM : bv_unsigned (alu64 ALU_ADD a (rw r V_MS)) = ua + secmapsize nv).
  { rewrite add_val, E142, u64_lit by (clear -SMB HN; lia). fold ua. apply Z.mod_small. clear -Ra DT TG SMB. lia. }
  unfold F_map, F_cls, clsP in *. apply Forall_app. split.
  - apply Forall_cons. { cbn [holds]. rewrite Enx. fold ua. split; [lia|]. change (2 ^ 12) with PG. exact (proj1 (proj2 HP)). }
    apply Forall_cons. { cbn [holds]. unfold vMAPn. cbn [eval]. rewrite Enx, u64_lit by (unfold IMG_HI; lia). exact IMG. }
    apply Forall_cons. { cbn [holds]. unfold vMAPn. cbn [eval]. rewrite Enx, EUM, u64_lit by lia. clear -DT TG. lia. }
    apply Forall_nil.
  - destruct hi.
    + apply Forall_cons. { cbn [holds]. unfold vMAPn. cbn [eval]. rewrite Enx, u64_lit by (unfold SHADOW_BAND_HI, HIGH_SHADOW_END; lia). exact HC. }
      apply Forall_cons. { cbn [holds]. unfold vMAPn. cbn [eval]. rewrite Enx, u64_lit by lia. fold ua. clear -DT TG SMB. lia. }
      apply Forall_nil.
    + apply Forall_cons. { cbn [holds]. unfold vMAPn. cbn [eval]. rewrite Enx, u64_lit by (unfold SHADOW_BAND_LO, LOW_SHADOW_BEG; lia). fold ua. unfold SHADOW_BAND_LO, LOW_SHADOW_BEG in *. clear -HC SMB. lia. }
      apply Forall_cons. { cbn [holds]. unfold vMAPn. cbn [eval]. rewrite Enx, EUM, u64_lit by (unfold SHADOW_BAND_LO, LOW_SHADOW_BEG; lia). exact HC. }
      apply Forall_nil.
Qed.

Lemma sec_reveal : ltac2:(tb__ "0|4|
S41S59S16S3fQ40M0A1M1S16S5G1A1M2S5S7dA1M3SadS7cS0S5cVst;S5bA3S0S5S5aA1VW;S7S5aA1A3F_;S79VW;Vst;A2S60RaA1S3eG0S18RaPcA2A2S13S54Vhi;S3eG0RaA2S78R1A1A3S67Vsegs;S53ReRdRcRbA4VE0;RaR9ScG3S94R8S95R7R6A2A4A6S2G2G2S2S16S16S2S16S16S1S51S3eG0RfA2S78R6A1R10R1A4S1S14S0G1S18R3R1A2S18RfR1A2A3Fi;S1S14S0S5S3fQ8A1A1S1eR3R1A2S1eRfR1A2A3Fl;S67Vsegs;S4fR12R11R1RfA4VT0;R2S8G1R3RdA3ScG3S94RcS95RbRaA2A4A6A2A2A2Lrho';A2LrhoX';A2Ltp1;A2F_;F_;Tnv;F_;F_;F_;Fmd;Fms;Ftr;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp tr ms md HW HUS HKc nv HC Hsp.
  pose proof (proj2 Hsp) as [HJ HCR]. cbn [w_tr w_cfg cfg_model cfg_ms fst snd] in HJ, HCR. fold nv in HCR.
  pose proof (JGs_rigidS A Kc rho a rhoX tp tr md HJ) as (E12 & Enx & E141 & E142 & E151 & E152 & E155 & E145 & E146 & E147 & Erm & Erl).
  pose proof HJ as (Hagr & Ha & HA & HP & HK & Htp & HU & HN & Htop & HB). fold nv in HA, HP, HN, HB.
  pose proof (urange a) as Ra. set (ua := bv_unsigned a) in *.
  pose proof (secmapsize_bounds nv ltac:(clear -HN; lia)) as [SMB SMM]. set (L := secmapsize nv) in *.
  pose proof HP as (_ & _ & HL & DI & _). pose proof (dyn_in_big _ _ _ DI ltac:(clear -SMB; lia)) as IMG.
  destruct DI as (D0 & _ & DT & _ & WB). pose proof (topG_range (aa_geom A)) as TG.

  assert (HT0 : SPA segs (JGsC A Kc rho a) T0 rhoX tp (tr, mkCfg ms md)).
  { split; [|exact (proj2 Hsp)]. apply AF0; [exact (proj1 Hsp) | exact (F_map_hold A Kc rho a rhoX tp tr md HJ HC)]. }

  destruct (SPA_J_out segs _ T0 rhoX tp _ HT0) as [HJT _].
  set (q := pgq (Sh ua)). set (np := npg (Sh ua) (Sh ua + L / 8)).
  pose proof (pg_run (Sh ua) (Sh ua + L / 8) ltac:(unfold Sh, SHADOW_OFF; clear -Ra; lia) ltac:(clear -SMB; pose proof (Z.div_pos L 8); lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  fold q in Q1, Q2, Q3, Q5, Q6. fold np in Q2, Q4, Q6.
  pose proof (shadow_run_band hi ua L HC IMG HL ltac:(clear -DT TG; lia)) as (RB & RLO & RHI & RBL & RBH). fold q np in RB, RLO, RHI, RBL, RBH.

  pose proof HA as (HG & _ & _ & _ & HM & HI3 & HBT). rewrite AXg in HG. cbn [aa_geom bumpV] in HG.
  pose proof HM as (VG & V2 & V3 & V0 & _). destruct VG as (_ & _ & _ & _ & _ & _ & _ & _ & G9).
  assert (BAND : forall k, (k < Z.to_nat np)%nat ->
            page_in_ranges (pageZ q k) (m_vm_lazy md) = true /\ forall j, 0 <= j < PG -> covered (vm_noaccess (m_vmmaps md)) (bv_unsigned (pageZ q k) + j) = false).
  { intros k Hk. assert (UP : bv_unsigned (pageZ q k) = q + 4096 * Z.of_nat k) by (apply pageZ_u; clear -Hk RLO RHI Q4; unfold PG in *; lia).
    apply G9; rewrite UP.
    - replace (q + 4096 * Z.of_nat k) with (q + Z.of_nat k * 4096) by lia. unfold PG. rewrite Z_mod_plus_full. exact Q3.
    - clear -RB Hk Q4. unfold PG in *. destruct hi; [right | left]; lia. }
  assert (NPZ : 4096 * Z.of_nat (Z.to_nat np) = PG * np) by (unfold PG; clear -Q4; lia).
  assert (ROOM : headroom md tp >= 4096 * Z.of_nat (Z.to_nat np)).
  { rewrite NPZ. unfold headroom. rewrite V3. pose proof (AInvA_boundD _ _ _ _ HA) as BD. rewrite AXb in BD.
    unfold budget_bound in BD. unfold budget_ok_alloc, limit_ok_alloc in HB. cbn [aa_V aa_Km aa_Kf bumpV] in BD.
    assert (NP : PG * np <= SHC nv).
    { unfold SHC, PG. fold L. replace (L / (8 * 4096)) with (L / 8 / 4096) by (rewrite Zdiv_Zdiv by lia; reflexivity). clear -Q4 SMB. unfold PG in Q4. lia. }
    pose proof (PrimCredit.prim_credit_nonneg (AX (bumpV A nv))) as PCN. clear -HCR BD HB NP PCN. unfold BETA_M in *. lia. }

  assert (HT0' : SPA segs (JGs A Kc rho a) T0 rhoX tp (tr, mkCfg ms md)) by (split; [exact (proj1 HT0) | exact HJ]).
  assert (NP1 : 1 <= np).
  { assert (L8 : 9216 <= L / 8) by (apply Z.div_le_lower_bound; clear -SMB; lia). clear -Q1 Q2 L8. unfold PG in Q2. nia. }
  assert (DISJ : Forall (fun o => ranges_disjoint (obj_range rhoX o) (q, q + 4096 * Z.of_nat (Z.to_nat np))) (ss_objs (ax_S T0))).
  { destruct (objs_noband T0 [] [] A Kc rho a rhoX tp _ HW HT0' ltac:(cbn [app]; rewrite app_nil_r; exact SKT) FCT) as (l0 & l1 & l2 & EO12 & SK0' & SK2 & NB).
    destruct l2; [|discriminate SK2]. destruct l0; [|discriminate SK0']. rewrite app_nil_r in EO12. cbn [app] in EO12. rewrite EO12. eapply Forall_impl; [|exact NB]. intros o Ho. rewrite NPZ. unfold ranges_disjoint, range_noband, noband in *. cbn [fst snd].
    destruct (obj_range rhoX o) as [olo ohi]. cbn [fst snd] in Ho |- *.
    destruct (Z_le_dec ohi olo) as [E|E]; [left; exact E|].
    destruct (Z_le_dec ohi q) as [E2|E2]; [right; right; left; exact E2|].
    destruct (Z_le_dec (q + PG * np) olo) as [E3|E3]; [right; right; right; exact E3|].
    exfalso. destruct (Ho (Z.max olo q) ltac:(clear -E E2 E3; lia)) as [Y|Y]; clear -Y E E2 E3 RBL RBH NP1; unfold PG in *; lia. }
  destruct (SPA_reveal_pages T0 q (Z.to_nat np) rhoX tp tr ms md HJT Q3 RLO ltac:(rewrite NPZ; exact RHI)
              ltac:(intros k Hk; exact (proj1 (BAND k Hk)))
              ltac:(intros z Hz; rewrite NPZ in Hz; destruct (page_base_run q (Z.to_nat np) (Z_to_bv 64 z) Q3 ltac:(clear -RLO; lia) ltac:(rewrite NPZ; exact RHI) ltac:(rewrite u64_lit by (clear -Hz RLO RHI; lia); rewrite NPZ; exact Hz)) as (k & Hk & Ek & Rk);
                    rewrite u64_lit in Rk by (clear -Hz RLO RHI; lia);
                    pose proof (proj2 (BAND k Hk) (z - (q + 4096 * Z.of_nat k)) ltac:(unfold PG; clear -Rk; lia)) as X;
                    rewrite pageZ_u in X by (clear -Hk RLO RHI Q4 NPZ; unfold PG in *; lia);
                    replace (q + 4096 * Z.of_nat k + (z - (q + 4096 * Z.of_nat k))) with z in X by lia; exact X)
              ROOM DISJ) as (tp1 & rho1 & Hsp1 & HR).
  pose proof HR as (Rw & Rl & Rtp1 & Rlen & Rvis & Rz & Rk & Ro).
  assert (RHI' : q + 4096 * Z.of_nat (Z.to_nat np) <= 2 ^ 64) by (rewrite NPZ; exact RHI).
  pose proof (revealed_ext JT T0 q (Z.to_nat np) rhoX tp rho1 tp1 tr ms md HJT HR Q3 RLO RHI' ltac:(intros k Hk; exact (proj1 (BAND k Hk))) DISJ) as EXT.

  assert (RUNPG : forall k, (k < Z.to_nat np)%nat -> band_page (bv_unsigned (pageZ q k)) /\ bv_unsigned (pageZ q k) = q + 4096 * Z.of_nat k).
  { intros k Hk. assert (UP : bv_unsigned (pageZ q k) = q + 4096 * Z.of_nat k) by (apply pageZ_u; clear -Hk RLO RHI Q4; unfold PG in *; lia).
    split; [|exact UP]. rewrite UP. unfold band_page. clear -RB Hk Q4. unfold PG in *. destruct hi; [right | left]; lia. }
  assert (NP : PG * np <= SHC nv).
  { unfold SHC, PG. fold L. replace (L / (8 * 4096)) with (L / 8 / 4096) by (rewrite Zdiv_Zdiv by lia; reflexivity). clear -Q4 SMB. unfold PG in Q4. lia. }

  assert (HA1 : AInvA segs (AX (bumpV A nv)) rho1 (tp1 ++ tp) md).
  { apply (AInvA_reveal segs _ rhoX); [exact HA | exact EXT | |].
    - intros p Hp. destruct (Rtp1 p Hp) as ((k & Hk & ->) & Hnin). destruct (RUNPG k Hk) as [BP UP]. split; [exact BP|].
      intros z Hz. rewrite UP in Hz. rewrite view_in by (clear -Hz RLO RHI' Hk Q4 NPZ; unfold PG in *; lia). unfold rd_of.
      rewrite (Rz (Z_to_bv 64 z)); [eexists; reflexivity| |].
      + rewrite u64_lit by (clear -Hz RLO RHI' Hk NPZ; unfold PG in *; lia). clear -Hz Hk NPZ RLO. unfold PG in *. lia.
      + apply (proj2 (page_mem_false _ _)). rewrite (page_base_in_page (pageZ q k)); [exact Hnin| |].
        * rewrite UP. replace (q + 4096 * Z.of_nat k) with (q + Z.of_nat k * 4096) by lia. change page_size with 4096. rewrite Z_mod_plus_full. exact Q3.
        * unfold in_page. rewrite UP, u64_lit by (clear -Hz RLO RHI' Hk NPZ; unfold PG in *; lia). change page_size with 4096. unfold PG in Hz. exact Hz.
    - pose proof (revealed_paid q (Z.to_nat np) rhoX tp rho1 tp1 md HR) as RP. rewrite NPZ in RP. clear -RP NP HCR. lia. }

  set (rho' := mkVal (rw rho) (rl rho) (rm rho1)).
  assert (RWM : forall i, rw (rhoM_of A rho') i = rw (rhoM_of A rho) i) by (intros i; reflexivity).
  assert (RLM : forall l, rl (rhoM_of A rho') l = rl (rhoM_of A rho) l) by (intros l; reflexivity).
  assert (RMM : forall x, rm (rhoM_of A rho') x = rm rho1 x) by (intros x; reflexivity).
  destruct Hagr as (A1 & A2 & A3).
  exists tp1, rho1, rho'. split; [|split; [exact Rw | split; [exact Rl|]]].
  -
    split; [intros i; reflexivity|]. split; [intros l; reflexivity|]. split.
    + intros x. cbn [rho' rm]. destruct (EXT x) as [E|[N I]].
      * left. rewrite E. apply Erm.
      * destruct (Z_lt_le_dec (bv_unsigned x) q) as [Y|Y]; [left; rewrite (Ro x) by (clear -Y; lia); apply Erm|].
        destruct (Z_lt_le_dec (bv_unsigned x) (q + 4096 * Z.of_nat (Z.to_nat np))) as [Y2|Y2]; [|left; rewrite (Ro x) by (clear -Y2; lia); apply Erm].
        right. left. split; [rewrite <- Erm; exact N|]. split; [exact I|]. rewrite NPZ in Y2. clear -Y Y2 RBL RBH. lia.
    + intros z Hz. cbn [rho' rm].
      assert (Hzq : q <= z < q + 4096 * Z.of_nat (Z.to_nat np)) by (rewrite NPZ; clear -Hz Q1 Q2; lia).
      assert (Uz : bv_unsigned (Z_to_bv 64 z) = z) by (apply u64_lit; clear -Hzq RLO RHI'; lia).
      destruct (page_mem (page_base (Z_to_bv 64 z)) tp) eqn:PM.
      * rewrite (Rk (Z_to_bv 64 z)) by (rewrite ?Uz; assumption).

        destruct (page_base_run q (Z.to_nat np) (Z_to_bv 64 z) Q3 ltac:(clear -RLO; lia) RHI' ltac:(rewrite Uz; exact Hzq)) as (k & Hk & Ek & Rk2).
        destruct (RUNPG k Hk) as [BP UP]. apply (proj1 (page_mem_In _ _)) in PM. rewrite Ek in PM.
        pose proof (HBT _ PM BP z ltac:(rewrite UP; rewrite Uz in Rk2; unfold PG; clear -Rk2; lia)) as [b Hb].
        rewrite view_in in Hb by (clear -Hzq RLO RHI'; lia). unfold rd_of in Hb.
        destruct (rm rhoX (Z_to_bv 64 z)) eqn:E; [discriminate|]. exfalso. rewrite image_byte_none_A in Hb by (rewrite Uz; clear -Hzq RLO; lia). discriminate.
      * rewrite (Rz (Z_to_bv 64 z)) by (rewrite ?Uz; assumption). discriminate.
  -
    apply SPA_J_in; [exact Hsp1|]. cbn [w_tr w_cfg cfg_model cfg_ms fst snd].
    unfold JGs. cbn [rw rho']. fold nv.
    split.
    { split; [|split].
      - intros i Hi. rewrite RWM, Rw. exact (A1 i Hi).
      - intros l. rewrite RLM, Rl. rewrite <- (A2 l). reflexivity.
      - intros x. rewrite RMM. reflexivity. }
    split; [rewrite Rw; exact Enx|].
    split; [exact HA1|]. split; [exact HP|]. split; [exact HK|].
    split; [unfold tp_ok in Htp |- *; rewrite Rw; exact Htp|].
    split; [apply (stopJ_rwrl rhoX rho1); [intros i; symmetry; apply Rw | intros l; symmetry; apply Rl | exact HU]|].
    split; [exact HN|]. split; [|exact HB].
    unfold top_high in Htop |- *. rewrite !Rw. exact Htop.
Qed.

Section G12.

Variables (ET1 CT1 CO1 T1 ET2 CT2 CO2 T2 : axst) (s1 s2 : wsub) (R1 R2 : list sobj).
Let D1 : axst := ltac2:(tb__ "0|0|
S97VT1;S1bS2dVCO1;A1A1A2").
Let D2 : axst := ltac2:(tb__ "0|0|
S97VT2;S1bS2dVCO2;A1A1A2").

Hypothesis Cert1 : ltac2:(tb__ "0|1|
S0S6S9dS91Ufa0SbS13S9eS7S13A1A3S50SbS2eVT0;S7S2eA1M0A3SbS2eVET1;G0A3A6S9A3").
Hypothesis Cert2 : ltac2:(tb__ "0|1|
S0S6S9dS91Ufa0SbS13S9eS7S13A1A3S50SbS2eVD1;S7S2eA1M0A3SbS2eVET2;G0A3A6S9A3").

Hypothesis WC1 : ltac2:(tb__ "0|0|
S0S6S21S2dVCT1;A1A1S9A3").
Hypothesis DF1 : ltac2:(tb__ "0|4|
S0SdSaS5SaS17S17A2M0A1M1S5S19A1M2A2M3A1S9cS2dVET1;A1S2dVCT1;A1A2SeG3ScG1G2SbG0ScS17S17S8dVnx;A1S87A4S7G0A1A3S7S19A1A4A2A3").
Hypothesis NX1 : ltac2:(tb__ "0|0|
S0S14S1cS2dVCT1;A1A1S1cS2dVET1;A1A1A3").
Hypothesis HC1 : ltac2:(tb__ "0|0|
S0S2eS31VET1;S2dVCT1;A1A2VCT1;A3").
Hypothesis SK1 : ltac2:(tb__ "0|2|
S0S5SaSaS17S17A2S17A2M0A1S4dS15G0S66S1dS2dVCT1;A1A1A4S4dS15G0S66S8S15S7S15A1M1S8S15S52G1A3A3A4A3").
Hypothesis FC1 : ltac2:(tb__ "0|0|
S84S19S8S19S5fVW;Vst;A2S5eS5dA1A3S1bS2dVCT1;A1A1A3").
Hypothesis XC1 : ax_X CT1 = [].
Hypothesis HCO1 : ltac2:(tb__ "0|0|
S0S2eS85VCT1;S23S89Vnx;A1S1fZ0A1S87S7S22A1S26A5A2VCO1;A3").
Hypothesis WCO1 : ltac2:(tb__ "0|0|
S0S6S21S2dVCO1;A1A1S9A3").
Hypothesis He1 : ltac2:(tb__ "0|1|
S0SdS5S15A1M0A1S99VCO1;S81Vs1;A3SeG0VR1;A2A3").
Hypothesis Hchk1 : ltac2:(tb__ "0|0|
S0S6S98VCO1;S81Vs1;VR1;S4dS2fS2eS30S82A4A5S9A3").
Hypothesis HT1 : ltac2:(tb__ "0|0|
S0S2eS9aVs1;S81S8bVCO1;VR1;A5VT1;A3").
Hypothesis FBC1 : ltac2:(tb__ "0|1|
S0S6S83S19S20S1cS2dVCO1;A1M0A1A1S1bG0A1A3S9A3").
Hypothesis FBT1 : ltac2:(tb__ "0|0|
S0S6S83S19S20S1cS2dVT1;A1A1A1S1bS2dVCO1;A1A1A3S9A3").
Hypothesis NXC1 : ltac2:(tb__ "0|0|
S0S6S92S50S1cS2dVCO1;A1A1A2S9A3").

Hypothesis WC2 : ltac2:(tb__ "0|0|
S0S6S21S2dVCT2;A1A1S9A3").
Hypothesis DF2 : ltac2:(tb__ "0|4|
S0SdSaS5SaS17S17A2M0A1M1S5S19A1M2A2M3A1S9cS2dVET2;A1S2dVCT2;A1A2SeG3ScG1G2SbG0ScS17S17S8cVnx;A1S86Vnx;A1A4SbG0ScS17S17S8eVnx;A1S88A4S7G0A1A3A3S90A4A2A3").
Hypothesis NX2 : ltac2:(tb__ "0|0|
S0S14S1cS2dVCT2;A1A1S1cS2dVET2;A1A1A3").
Hypothesis HC2 : ltac2:(tb__ "0|0|
S0S2eS31VET2;S2dVCT2;A1A2VCT2;A3").
Hypothesis SK2 : ltac2:(tb__ "0|2|
S0S5SaSaS17S17A2S17A2M0A1S4dS15G0S66S1dS2dVCT2;A1A1A4S4dS15G0S66S8S15SbS15S8fVnx;A1S7S15A1M1A3S8S15S52G1A3A3A4A3").
Hypothesis FC2 : ltac2:(tb__ "0|0|
S84S19S8S19S5fVW;Vst;A2S5eS5dA1A3S1bS2dVCT2;A1A1A3").
Hypothesis XC2 : ax_X CT2 = [].
Hypothesis HCO2 : ltac2:(tb__ "0|0|
S0S2eS85VCT2;S23S86Vnx;A1S1fZ0A1S88S7S22A1S26A5A2VCO2;A3").
Hypothesis WCO2 : ltac2:(tb__ "0|0|
S0S6S21S2dVCO2;A1A1S9A3").
Hypothesis He2 : ltac2:(tb__ "0|1|
S0SdS5S15A1M0A1S99VCO2;S81Vs2;A3SeG0VR2;A2A3").
Hypothesis Hchk2 : ltac2:(tb__ "0|0|
S0S6S98VCO2;S81Vs2;VR2;S4dS2fS2eS30S82A4A5S9A3").
Hypothesis HT2 : ltac2:(tb__ "0|0|
S0S2eS9aVs2;S81S8bVCO2;VR2;A5VT2;A3").
Hypothesis FBC2 : ltac2:(tb__ "0|1|
S0S6S83S19S20S1cS2dVCO2;A1M0A1A1S1bG0A1A3S9A3").
Hypothesis FBT2 : ltac2:(tb__ "0|0|
S0S6S83S19S20S1cS2dVT2;A1A1A1S1bS2dVCO2;A1A1A3S9A3").
Hypothesis NXC2 : ltac2:(tb__ "0|0|
S0S6S92S50S1cS2dVCO2;A1A1A2S9A3").

Lemma RS1 : ltac2:(tb__ "0|1|
S41S59S16S3fQ40A1M0S16S5G0A1S7eS0S5cVst;S5bA3S0S5S5aA1VW;S7S5aA1A3F_;S67Vsegs;S4fR8R7R6R5A4VET1;R4R3R2A6S67Vsegs;S4fR9R8R7R6A4VCT1;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW Hw. destruct w as [tr [ms md]]. rewrite <- HC1.
  eapply SPA_restate; [exact WC1 | exact DF1 | exact NX1 | | constructor | exact Hw].
  unfold diffs_ok. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold L1.
  exact (site1_a2 A Kc rho a rhoX tp tr md (proj2 Hw)).
Qed.

Lemma HBL1 : forall A Kc rho a rhoX tp w, SPA segs (JGs A Kc rho a) CT1 rhoX tp w ->
  Sh (bv_unsigned a) <= bv_unsigned (eval rhoX (B1 nx))
  /\ bv_unsigned (eval rhoX (B1 nx)) + bv_unsigned (eval rhoX L1) <= Sh (bv_unsigned a) + secmapsize (bv_unsigned (rw rho 12%positive)) / 8
  /\ (forall l, map skel l = map skel ([] : list sobj) ->
        Forall (fun o => ranges_disjoint (obj_range rhoX o) (bv_unsigned (eval rhoX (B1 nx)), bv_unsigned (eval rhoX (B1 nx)) + bv_unsigned (eval rhoX L1))) l)
  /\ (forall l, map skel l = map skel ([] : list sobj) ->
        Forall (fun o => ranges_disjoint (obj_range rhoX o) (bv_unsigned (eval rhoX (B1 nx)), bv_unsigned (eval rhoX (B1 nx)) + bv_unsigned (eval rhoX L1))) l).
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]].
  destruct (site1_bounds A Kc rho a rhoX tp tr md (proj2 Hw)) as (EB & EL & BB). rewrite EB, EL.
  split; [lia|]. split; [exact BB|]. split; intros [|o l2] EE; [constructor | discriminate EE | constructor | discriminate EE].
Qed.

Lemma RS2 : ltac2:(tb__ "0|1|
S41S59S16S3fQ40A1M0S16S5G0A1S7eS0S5cVst;S5bA3S0S5S5aA1VW;S7S5aA1A3F_;S67Vsegs;S4fR8R7R6R5A4VET2;R4R3R2A6S67Vsegs;S4fR9R8R7R6A4VCT2;R5R4R3A6F_;F_;Fw;Ftp;FrhoX;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoX tp w HW Hw. destruct w as [tr [ms md]]. rewrite <- HC2.
  destruct (site2_vals A Kc rho a rhoX tp tr md (proj2 Hw)) as (EA0 & EB & EA2 & EL & BL & _).
  eapply SPA_restate; [exact WC2 | exact DF2 | exact NX2 | | | exact Hw].
  - unfold diffs_ok. apply Forall_cons; [cbn [fst snd]; apply bv_eq; rewrite EA0, EB; reflexivity|].
    apply Forall_cons; [cbn [fst snd]; apply bv_eq; rewrite EA2, EL; reflexivity | apply Forall_nil].
  - unfold fx2. apply Forall_cons; [|apply Forall_nil]. cbn [holds eval]. rewrite EL, u64_lit by lia. lia.
Qed.

Lemma HBL2 : forall A Kc rho a rhoX tp w, SPA segs (JGs A Kc rho a) CT2 rhoX tp w ->
  Sh (bv_unsigned a) <= bv_unsigned (eval rhoX (B2 nx))
  /\ bv_unsigned (eval rhoX (B2 nx)) + bv_unsigned (eval rhoX L2) <= Sh (bv_unsigned a) + secmapsize (bv_unsigned (rw rho 12%positive)) / 8
  /\ (forall l, map skel l = map skel [O_1 nx] ->
        Forall (fun o => ranges_disjoint (obj_range rhoX o) (bv_unsigned (eval rhoX (B2 nx)), bv_unsigned (eval rhoX (B2 nx)) + bv_unsigned (eval rhoX L2))) l)
  /\ (forall l, map skel l = map skel ([] : list sobj) ->
        Forall (fun o => ranges_disjoint (obj_range rhoX o) (bv_unsigned (eval rhoX (B2 nx)), bv_unsigned (eval rhoX (B2 nx)) + bv_unsigned (eval rhoX L2))) l).
Proof.
  intros A Kc rho a rhoX tp w Hw. destruct w as [tr [ms md]].
  destruct (site2_vals A Kc rho a rhoX tp tr md (proj2 Hw)) as (EA0 & EB & EA2 & EL & BL & V8 & M8 & SUM). rewrite EB, EL.
  destruct (site1_bounds A Kc rho a rhoX tp tr md (proj2 Hw)) as (EB1 & EL1 & BB1).
  pose proof (JGs_nums A Kc rho a rhoX tp tr md (proj2 Hw)) as (HN & SMB & SMM & AL & IMG & TOP & ENS & EMS & R8M & R8B).
  assert (V512 : 512 <= secneeded (bv_unsigned (rw rho 12%positive)) / 8) by (rewrite ENS; apply Z.div_le_lower_bound; clear -R8B HN; lia).
  split; [clear -V512; lia|]. split; [clear -SUM BL; lia|]. split; [|intros [|o l2] EE; [constructor | discriminate EE]].
  intros l2 EE. destruct l2 as [|o [|o' l2']]; [constructor | | cbn in EE; discriminate EE].
  apply Forall_cons; [|apply Forall_nil].
  assert (Es : skel o = skel (O_1 nx)) by (cbn in EE; congruence).
  rewrite (obj_range_skel rhoX o (O_1 nx) Es). unfold O_1, L1. rewrite obj_range_mk by lia. rewrite EB1.
  unfold ranges_disjoint. cbn [fst snd]. right. right. left. clear -V512. lia.
Qed.

Theorem sec_g12 : ltac2:(tb__ "0|3|
S7eOF_;S41S59S16S3fQ40M0A1M1S5G1A1M2S80S0S5cVst;S5bA3S0S5S5aA1VW;S7S5aA1A3F_;S79VW;Vst;A2S60R7A1S68Vsegs;RaS6aR8A1A3S3eG0S18R8PcA2A2S13S54Vhi;S3eG0R8A2S78R1A1A3S16S16G2S51S3eG0RcA2S78R5A1RdR3A4S7fVsegs;R11S67Vsegs;S4fR10RfR4RdA4VD2;R3R2A5RbA4F_;FtpY;FrhoY;Frho';S16S7fVsegs;RfS67Vsegs;S53ReRdRcRbA4VE0;R1RaA5R9A4FrhoX;F_;F_;Tnv;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp Q HW HUS HKc Hokl nv HC HCONT rhoX.
  apply (triple_conseq (P:=fun w => exists tp1 rhoX' rho', slink (bv_unsigned a) (secmapsize nv) rho rho' /\ SPA segs (JGs A Kc rho' a) T0 rhoX' (tp1 ++ tp) w)
           (SPA segs (JGsC A Kc rho a) E0 rhoX tp) (Q:=Q)); [intros w Hw | intros w Hw; exact Hw |].
  { destruct w as [tr [ms md]]. destruct (sec_reveal A Kc rho a rhoX tp tr ms md HW HUS HKc HC Hw) as (tp1 & rhoX' & rho' & SL & _ & _ & Hsp).
    exists tp1, rhoX', rho'. exact (conj SL Hsp). }
  apply triple_ex; intros tp1. apply triple_ex; intros rhoX'. apply triple_ex; intros rho'.
  apply (triple_pre_pure segs ok _ _ (slink (bv_unsigned a) (secmapsize nv) rho rho')); [intros w [SL _]; exact SL|]. intros SL.
  eapply triple_conseq; [intros w [_ Hw]; exact Hw | intros w Hw; exact Hw |].
  assert (E12' : rw rho' 12%positive = rw rho 12%positive) by (destruct SL as (SW & _); apply SW).
  assert (HST : stableA segs GS (JGs A Kc rho' a)) by (apply JGs_stable; assumption).
  assert (Hokf : ok_frameA segs ok (JGs A Kc rho' a)).
  { intros r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). exact (JGs_K _ _ _ _ _ _ _ _ HJ). }
  apply (cfg_soundA segs 4000%nat [MSENT] GS [T0] [ET1] (JGs A Kc rho' a) ok Q (tp1 ++ tp) Hokf HST Cert1); [|left; reflexivity].
  intros E rhoE HinE. destruct HinE as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  apply (ms_step ET1 CT1 CO1 T1 (B1 nx) L1 [] [] Pre_memsetA Pret_ms Posts_memsetA s1 R1 eq_refl
           (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl RS1 HBL1 SK1 FC1 XC1 HCO1 WCO1 He1 Hchk1 HT1 FBC1 FBT1 NXC1
           ok A Kc rho rho' a (tp1 ++ tp) Q HW HUS HKc Hokl); [unfold nv in SL; rewrite E12'; exact SL|].
  intros rhoY tpY. fold D1.
  apply (cfg_soundA segs 4000%nat [MSENT] GS [D1] [ET2] (JGs A Kc rho' a) ok Q tpY Hokf HST Cert2); [|left; reflexivity].
  intros E' rhoE' HinE'. destruct HinE' as [<-|[]].
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
  apply (ms_step ET2 CT2 CO2 T2 (B2 nx) L2 [O_1 nx] [] Pre_memsetA Pret_ms Posts_memsetA s2 R2 eq_refl
           (fun ok0 Jx r0 t0 Ho Hs => memset_sumA ok0 Jx r0 t0 Ho Hs) eq_refl RS2 HBL2 SK2 FC2 XC2 HCO2 WCO2 He2 Hchk2 HT2 FBC2 FBT2 NXC2
           ok A Kc rho rho' a tpY Q HW HUS HKc Hokl); [unfold nv in SL; rewrite E12'; exact SL|].
  intros rhoZ tpZ. fold D2. apply HCONT. exact SL.
Qed.
End G12.
End Reveal.

End SEC3.
End SpineMallocSec3.

(* [comment removed for export] *)
Module SpineMallocSecI.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI"; "W0"; "st0"; "@Corelib.Init.Logic"; "eq"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "sstate"; "ss_next"; "reg_sv"; "valuation"; "SVar"; "swf"; "sprop_below"; "ss_facts"; "ss_objs"; "ss_pc"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "bool"; "prod"; "true"; "app"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "CS1"; "ES1"; "ES1f"; "SS0"; "ESn"; "SSa_S"; "SSb_S"; "V_MS"; "ES1g"; "F_sgen"; "RT_sec"; "V_NS"; "nxS"; "@Corelib.Init.Specif"; "sig"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN"; "stRn_S"; "s_n"; "stKn"; "R_n"; "stRn"; "N_secn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "E_s1"; "RT_m1"; "F_fam"; "F_s1"; "neededx"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "Kc_ok"; "L_malloc_null"; "A_globals"; "JL_malloc_null"; "Posts_malloc"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "vm_reserved"; "with_vmmaps"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "a1x"; "@Stdlib.Lists.List"; "forallb"; "incl"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition W0 : list ulink := Wcan 0.
Definition st0 : ustop := UStopLe.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S2dScScS2ScS25S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S48S0S1Z2Z8A4R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S2dScScS2ScS26S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S23S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S21S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S20S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S22S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S24S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_8 : ltac2:(tb__ "0|1|
S2dS18SaA1M0G0S2G0S3bS0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_9 : ltac2:(tb__ "0|0|
S2dScScS2ScS38S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_10 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S3aS0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_11 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S3cS0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_12 : ltac2:(tb__ "0|0|
S2dS42S42S2S42S39S0S1Z2A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma SWa_0 : ltac2:(tb__ "0|0|
S2S19S11S25S0S1Z2A3A1S1bA3"). Proof. memo_rw (SSa_S W0 st0 2) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SDa_0 : ltac2:(tb__ "0|7|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S41S5S48S0S1Z2M4Z8M5A4A1S25S0S1G4A3A2S1eG3S1dG1G2S16G0S1dS8S8S4cG5A1S10S2bA1A4M6S16G0G6S17G0A1A3A3S17S9A1A4A2A3"). Proof. memo_rw (E_s1 W0 st0 2 8) memo_1. memo_rw (SSa_S W0 st0 2) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SWb_0 : ltac2:(tb__ "0|0|
S2S19S11S26S0S1Z2A3A1S1bA3"). Proof. memo_rw (SSb_S W0 st0 2) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SFB : ltac2:(tb__ "0|0|
S2S19S7cS9S12S6aA1S29A3S1bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma CertS1_0 : ltac2:(tb__ "0|2|
S2S19S32S35Ufa0S16S2eZ7050cS17S2eA1A3S34S16S4S23S0S1Z2M0A3S17S4A1M1A3S16S4S21S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 2) memo_3. memo_rw (ES1 W0 st0 2) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WC1_0 : ltac2:(tb__ "0|0|
S2S19S11S5S20S0S1Z2A3A1A1S1bA3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DC1_0 : ltac2:(tb__ "0|5|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S41S5S21S0S1Z2M4A3A1S5S20S0S1G4A3A1A2S1eG3S1dG1G2S16G0S1dS8S8S7bS10S27A1A4S17G0A1A3S17S9A1A4A2A3"). Proof. memo_rw (ES1 W0 st0 2) memo_4. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC1_0 : ltac2:(tb__ "0|1|
S2S2fSdS5S20S0S1Z2M0A3A1A1SdS5S21S0S1G0A3A1A1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. memo_rw (ES1 W0 st0 2) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IC1_0 : ltac2:(tb__ "0|0|
S2S1fS61A1S73S35S15S5S20S0S1Z2A3A1A1A2S1eS61S62A2A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R17_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z2A3A1Z11A2SbZdeA1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R11_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z2A3A1ZbA2S10S27A1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R10_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z2A3A1ZaA2SbZ0A1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R12_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z2A3A1ZcA2SbZ3A1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R13_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z2A3A1ZdA2SbZ22A1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R14_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z2A3A1ZeA2SbZffffffffffffffffA1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R15_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z2A3A1ZfA2SbZ0A1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1_0 : ltac2:(tb__ "0|0|
S2S2fSdS5S20S0S1Z2A3A1A1S6aA3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC1_0 : ltac2:(tb__ "0|1|
S2S18S1aS8S8A2M0A1S6S20S0S1Z2A3A1S17G0A1A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK1_0 : ltac2:(tb__ "0|1|
S2S18S1aS1aS8S8A2S8A2M0A1S3fSaG0S6cS14S5S20S0S1Z2A3A1A1A4S3fSaG0S6cS1cSaS1cSaS16SaS4dS1cSaS58S0A1S52A3A3S49A3S2aA3A4A3"). Proof. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC1_0 : ltac2:(tb__ "0|1|
S7dS9S1cS9S1cS9S1cS9S1cS9S57S0S1A2S56S55A1A3S6bA3S4bA3S4aZ2M0Z8A2A3S13S5S20S0S1G0A3A1A1A3").
Proof. apply inclb_incl. memo_rw (CS1 W0 st0 2) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma CertSf_0 : ltac2:(tb__ "0|2|
S2S19S32S35Ufa0S16S2eZ5e398S17S2eA1A3S34S16S4S22S0S1Z2M0A3S17S4A1M1A3S16S4S24S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 2) memo_6. memo_rw (ESn W0 st0 2) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RN_0 : ltac2:(tb__ "0|0|
S2S18SaA1S3bS0S1Z2A3S1cSaS49S3fS78SaS77S3dA4A3A3"). Proof. memo_rw (R_n W0 st0 2) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WRn_0 : ltac2:(tb__ "0|0|
S2S19S11S38S0S1Z2A3A1S1bA3"). Proof. memo_rw (stRn_S W0 st0 2) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DKRn_0 : ltac2:(tb__ "0|5|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S41S5S3aS0S1Z2M4A3A1S38S0S1G4A3A2S1eG3S1dG1G2S16G0S1dS8S8SbS76A1S10P18A1A4S17G0A1A3S17S9A1A4A2A3"). Proof. memo_rw (stKn W0 st0 2) memo_10. memo_rw (stRn_S W0 st0 2) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXRn_0 : ltac2:(tb__ "0|1|
S2S2fSdS38S0S1Z2M0A3A1SdS5S3aS0S1G0A3A1A1A3"). Proof. memo_rw (stRn_S W0 st0 2) memo_9. memo_rw (stKn W0 st0 2) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTn_0 : ltac2:(tb__ "0|1|
S2S19S7S3cS0S1Z2M0A3S51S4eS0S1A3S39S0S1G0A3A3S1bA3"). Proof. memo_rw (stRn W0 st0 2) memo_11. memo_rw (s_n W0 st0 2) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IDn_0 : ltac2:(tb__ "0|0|
S2S19S43S39S0S1Z2A3S40A2S1bA3"). Proof. memo_rw (s_n W0 st0 2) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma NXS0_0 : ltac2:(tb__ "0|0|
S6dS34SdS5S23S0S1Z2A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (SS0 W0 st0 2) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertS1_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ7050cS17S2eA1A3S34S16S30S31S23S0S1Z2M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S21S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 2) memo_3. memo_rw (ES1 W0 st0 2) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXS1f_0 : ltac2:(tb__ "0|0|
S6dS34SdS5S22S0S1Z2A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (ES1f W0 st0 2) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertSf_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ5e398S17S2eA1A3S34S16S30S31S22S0S1Z2M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S24S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 2) memo_6. memo_rw (ESn W0 st0 2) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section SEC0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S2eS3eVCST;R1A2S3eS79R2A2S3F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S2eS3eVCST;R1A2S3eS7aR2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Hypothesis law_res : ltac2:(tb__ "0|1|
S59SfS18S5bQ40A1M0A1S5cVAInv;R4R3R2R1A4S2S18S1aG0G0A2A1S5fS5dR2A1A1S70S35A1A3F_;Fmd;Ftp;Frho;FA;").

Theorem malloc_sec_0 : ltac2:(tb__ "0|5|
S66OF_;S59S4fS5bQ40A1M0S46F_;SfS18G0A1S68Vsegs;S40R2R1S54S4eVAInv;VCST;VXGL;S0S1R5R4A8A5S64S50R5A1S47Vsegs;R8S45R6A1A3S74Vsegs;R9S45R7A1A3SfS18S5eA1M1S37S5cG0S75Vsegs;R5RaS20S0S1Z2M2A3M3S1dG1S6eR4S6fR3R2A2A4A5S5aS0S1RfReRcR6RbR5R3A9S71S36R5U0A2S36R5U3A2R4S36R5U1M4A2R3A5RfR4S67R8SdS5G3A1A1R4A3RdR7S60S72S5dR5A1S36R6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;SfG0S63Vsegs;RdS44Vsegs;RaR1A1S28S0S1G2A3S67R2S2cS0S1G2A3R1A3R8A5R7A4Fa;FrhoX;SfS63Vsegs;RdS44Vsegs;S5aS0S1RcRbR9A5S48S0S1G2Z8A4R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;TQ;Ftp;Frho;FJo;FKc;FA;Fok;").
Proof.
  intros ok A Kc Jo rho tp Q HKc Hokl Hokpl HJo HOK rhoE.
  refine (sec_spine 0%nat st0 2 CST XGL HCST HXGL HCSTM HCSTS law_res SWa_0 SDa_0 SWb_0 SFB CertS1_0 WC1_0 DC1_0 NXC1_0 IC1_0 R17_0 R11_0 R10_0 R12_0 R13_0 R14_0 R15_0
            NX1_0 XC1_0 SK1_0 FC1_0 CertSf_0 RN_0 WRn_0 DKRn_0 NXRn_0 ENTn_0 IDn_0 ok A Kc Jo rho tp _ _ (stopJ_stable_le _) HKc Hokl Hokpl _ HJo HOK rhoE).
  - intros E. discriminate E.
  - unfold Posts_malloc. left. reflexivity.
Qed.

Theorem emalloc_tail_null_0 : ltac2:(tb__ "0|1|
S59S4fSfS18S5bQ40A1A1S50R3A1SfS65Vsegs;S44Vsegs;S5aS0S1R6R5R4A5S22S0S1Z2A3R1R3A5S68Vsegs;S40R4R3S16S1aS4S69A2M0S1dS4S69S51S4eS0S1A3S53VAInv;VCST;VXGL;R6R5A5A4S17G0A1A3A5A3FrhoX;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc rhoX.
  refine (esec_tail_null 0%nat st0 2 CST XGL HCST HXGL HCSTM HCSTS NXS1f_0 ECertSf_0 RN_0 WRn_0 DKRn_0 NXRn_0 ENTn_0 IDn_0 A Kc rho tp _ (stopJ_stable_le _) HKc _ rhoX).
  left. reflexivity.
Qed.
End SEC0.
End SpineMallocSecI.

(* [comment removed for export] *)
Module SpineMallocSecIW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecIW2"; "W0"; "st0"; "@Corelib.Init.Logic"; "eq"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "sstate"; "ss_next"; "reg_sv"; "valuation"; "SVar"; "swf"; "sprop_below"; "ss_facts"; "ss_objs"; "ss_pc"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "bool"; "prod"; "true"; "app"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "CS1"; "ES1"; "ES1f"; "SS0"; "ESn"; "SSa_S"; "SSb_S"; "V_MS"; "ES1g"; "F_sgen"; "RT_sec"; "V_NS"; "nxS"; "@Corelib.Init.Specif"; "sig"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN"; "stRn_S"; "s_n"; "stKn"; "R_n"; "stRn"; "N_secn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "E_s1"; "RT_m1"; "F_fam"; "F_s1"; "neededx"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "KcA"; "Kc_ok"; "L_malloc_null"; "A_globals"; "JL_malloc_null"; "Posts_malloc"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "vm_reserved"; "with_vmmaps"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "a1x"; "@Stdlib.Lists.List"; "forallb"; "incl"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition W0 : list ulink := Wcan 2.
Definition st0 : ustop := UStopLe.

Ltac memo_rw t M := try (pattern t; refine (@eq_ind_r _ (proj1_sig M) _ _ t (proj2_sig M)); cbv beta).
Lemma memo_0 : ltac2:(tb__ "0|0|
S2dScScS2ScS25S0S1Z4A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_1 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S48S0S1Z4Z8A4R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_2 : ltac2:(tb__ "0|0|
S2dScScS2ScS26S0S1Z4A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_3 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S23S0S1Z4A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_4 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S21S0S1Z4A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_5 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S20S0S1Z4A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_6 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S22S0S1Z4A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_7 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S24S0S1Z4A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_8 : ltac2:(tb__ "0|1|
S2dS18SaA1M0G0S2G0S3bS0S1Z4A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_9 : ltac2:(tb__ "0|0|
S2dScScS2ScS38S0S1Z4A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_10 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S3aS0S1Z4A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_11 : ltac2:(tb__ "0|0|
S2dS4S4S2S4S3cS0S1Z4A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma memo_12 : ltac2:(tb__ "0|0|
S2dS42S42S2S42S39S0S1Z4A3R1A3Lx;A2"). Proof. eexists. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Defined.
Lemma SWa_0 : ltac2:(tb__ "0|0|
S2S19S11S25S0S1Z4A3A1S1bA3"). Proof. memo_rw (SSa_S W0 st0 4) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SDa_0 : ltac2:(tb__ "0|7|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S41S5S48S0S1Z4M4Z8M5A4A1S25S0S1G4A3A2S1eG3S1dG1G2S16G0S1dS8S8S4cG5A1S10S2bA1A4M6S16G0G6S17G0A1A3A3S17S9A1A4A2A3"). Proof. memo_rw (E_s1 W0 st0 4 8) memo_1. memo_rw (SSa_S W0 st0 4) memo_0. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SWb_0 : ltac2:(tb__ "0|0|
S2S19S11S26S0S1Z4A3A1S1bA3"). Proof. memo_rw (SSb_S W0 st0 4) memo_2. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SFB : ltac2:(tb__ "0|0|
S2S19S7cS9S12S6aA1S29A3S1bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma CertS1_0 : ltac2:(tb__ "0|2|
S2S19S32S35Ufa0S16S2eZ7050cS17S2eA1A3S34S16S4S23S0S1Z4M0A3S17S4A1M1A3S16S4S21S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 4) memo_3. memo_rw (ES1 W0 st0 4) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WC1_0 : ltac2:(tb__ "0|0|
S2S19S11S5S20S0S1Z4A3A1A1S1bA3"). Proof. memo_rw (CS1 W0 st0 4) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DC1_0 : ltac2:(tb__ "0|5|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S41S5S21S0S1Z4M4A3A1S5S20S0S1G4A3A1A2S1eG3S1dG1G2S16G0S1dS8S8S7bS10S27A1A4S17G0A1A3S17S9A1A4A2A3"). Proof. memo_rw (ES1 W0 st0 4) memo_4. memo_rw (CS1 W0 st0 4) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXC1_0 : ltac2:(tb__ "0|1|
S2S2fSdS5S20S0S1Z4M0A3A1A1SdS5S21S0S1G0A3A1A1A3"). Proof. memo_rw (CS1 W0 st0 4) memo_5. memo_rw (ES1 W0 st0 4) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IC1_0 : ltac2:(tb__ "0|0|
S2S1fS61A1S73S35S15S5S20S0S1Z4A3A1A1A2S1eS61S62A2A3"). Proof. memo_rw (CS1 W0 st0 4) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R17_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z4A3A1Z11A2SbZdeA1A3"). Proof. memo_rw (CS1 W0 st0 4) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R11_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z4A3A1ZbA2S10S27A1A3"). Proof. memo_rw (CS1 W0 st0 4) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R10_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z4A3A1ZaA2SbZ0A1A3"). Proof. memo_rw (CS1 W0 st0 4) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R12_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z4A3A1ZcA2SbZ3A1A3"). Proof. memo_rw (CS1 W0 st0 4) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R13_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z4A3A1ZdA2SbZ22A1A3"). Proof. memo_rw (CS1 W0 st0 4) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R14_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z4A3A1ZeA2SbZffffffffffffffffA1A3"). Proof. memo_rw (CS1 W0 st0 4) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R15_0 : ltac2:(tb__ "0|0|
S2S8SeS5S20S0S1Z4A3A1ZfA2SbZ0A1A3"). Proof. memo_rw (CS1 W0 st0 4) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NX1_0 : ltac2:(tb__ "0|0|
S2S2fSdS5S20S0S1Z4A3A1A1S6aA3"). Proof. memo_rw (CS1 W0 st0 4) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma XC1_0 : ltac2:(tb__ "0|1|
S2S18S1aS8S8A2M0A1S6S20S0S1Z4A3A1S17G0A1A3"). Proof. memo_rw (CS1 W0 st0 4) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma SK1_0 : ltac2:(tb__ "0|1|
S2S18S1aS1aS8S8A2S8A2M0A1S3fSaG0S6cS14S5S20S0S1Z4A3A1A1A4S3fSaG0S6cS1cSaS1cSaS16SaS4dS1cSaS58S0A1S52A3A3S49A3S2aA3A4A3"). Proof. memo_rw (CS1 W0 st0 4) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FC1_0 : ltac2:(tb__ "0|1|
S7dS9S1cS9S1cS9S1cS9S1cS9S57S0S1A2S56S55A1A3S6bA3S4bA3S4aZ4M0Z8A2A3S13S5S20S0S1G0A3A1A1A3").
Proof. apply inclb_incl. memo_rw (CS1 W0 st0 4) memo_5. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma CertSf_0 : ltac2:(tb__ "0|2|
S2S19S32S35Ufa0S16S2eZ5e398S17S2eA1A3S34S16S4S22S0S1Z4M0A3S17S4A1M1A3S16S4S24S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 4) memo_6. memo_rw (ESn W0 st0 4) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RN_0 : ltac2:(tb__ "0|0|
S2S18SaA1S3bS0S1Z4A3S1cSaS49S3fS78SaS77S3dA4A3A3"). Proof. memo_rw (R_n W0 st0 4) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WRn_0 : ltac2:(tb__ "0|0|
S2S19S11S38S0S1Z4A3A1S1bA3"). Proof. memo_rw (stRn_S W0 st0 4) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DKRn_0 : ltac2:(tb__ "0|5|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S41S5S3aS0S1Z4M4A3A1S38S0S1G4A3A2S1eG3S1dG1G2S16G0S1dS8S8SbS76A1S10P18A1A4S17G0A1A3S17S9A1A4A2A3"). Proof. memo_rw (stKn W0 st0 4) memo_10. memo_rw (stRn_S W0 st0 4) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXRn_0 : ltac2:(tb__ "0|1|
S2S2fSdS38S0S1Z4M0A3A1SdS5S3aS0S1G0A3A1A1A3"). Proof. memo_rw (stRn_S W0 st0 4) memo_9. memo_rw (stKn W0 st0 4) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTn_0 : ltac2:(tb__ "0|1|
S2S19S7S3cS0S1Z4M0A3S51S4eS0S1A3S39S0S1G0A3A3S1bA3"). Proof. memo_rw (stRn W0 st0 4) memo_11. memo_rw (s_n W0 st0 4) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IDn_0 : ltac2:(tb__ "0|0|
S2S19S43S39S0S1Z4A3S40A2S1bA3"). Proof. memo_rw (s_n W0 st0 4) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma NXS0_0 : ltac2:(tb__ "0|0|
S6dS34SdS5S23S0S1Z4A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (SS0 W0 st0 4) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertS1_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ7050cS17S2eA1A3S34S16S30S31S23S0S1Z4M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S21S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 4) memo_3. memo_rw (ES1 W0 st0 4) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXS1f_0 : ltac2:(tb__ "0|0|
S6dS34SdS5S22S0S1Z4A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (ES1f W0 st0 4) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertSf_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ5e398S17S2eA1A3S34S16S30S31S22S0S1Z4M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S24S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 4) memo_6. memo_rw (ESn W0 st0 4) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section SEC0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S2eS3eVCST;R1A2S3eS79R2A2S3F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S2eS3eVCST;R1A2S3eS7aR2A2S3F_;F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Hypothesis law_res : ltac2:(tb__ "0|1|
S59SfS18S5bQ40A1M0A1S5cVAInv;R4R3R2R1A4S2S18S1aG0G0A2A1S5fS5dR2A1A1S70S35A1A3F_;Fmd;Ftp;Frho;FA;").

Theorem malloc_sec_2 : ltac2:(tb__ "0|5|
S66OF_;S59S4fS5bQ40A1M0S46F_;SfS18G0A1S68Vsegs;S40R2R1S54S4eVAInv;VCST;VXGL;S0S1R5R4A8A5S64S50R5A1S47Vsegs;R8S45R6A1A3S74Vsegs;R9S45R7A1A3SfS18S5eA1M1S37S5cG0S75Vsegs;R5RaS20S0S1Z4M2A3M3S1dG1S6eR4S6fR3R2A2A4A5S5aS0S1RfReRcR6RbR5R3A9S71S36R5U0A2S36R5U3A2R4S36R5U1M4A2R3A5RfR4S67R8SdS5G3A1A1R4A3RdR7S60S72S5dR5A1S36R6G4A2R4A3R5A2A5F_;F_;F_;Fa;Fmd;Fms;Ftr;FrhoX;SfG0S63Vsegs;RdS44Vsegs;RaR1A1S28S0S1G2A3S67R2S2cS0S1G2A3R1A3R8A5R7A4Fa;FrhoX;SfS63Vsegs;RdS44Vsegs;S5aS0S1RcRbR9A5S48S0S1G2Z8A4R1R8A5R7A4FrhoE;F_;F_;F_;F_;F_;TQ;Ftp;Frho;FJo;FKc;FA;Fok;").
Proof.
  intros ok A Kc Jo rho tp Q HKc Hokl Hokpl HJo HOK rhoE.
  refine (sec_spine 2%nat st0 4 CST XGL HCST HXGL HCSTM HCSTS law_res SWa_0 SDa_0 SWb_0 SFB CertS1_0 WC1_0 DC1_0 NXC1_0 IC1_0 R17_0 R11_0 R10_0 R12_0 R13_0 R14_0 R15_0
            NX1_0 XC1_0 SK1_0 FC1_0 CertSf_0 RN_0 WRn_0 DKRn_0 NXRn_0 ENTn_0 IDn_0 ok A Kc Jo rho tp _ _ (stopJ_stable_le _) HKc Hokl Hokpl _ HJo HOK rhoE).
  - intros E. discriminate E.
  - unfold Posts_malloc. left. reflexivity.
Qed.

Theorem emalloc_tail_null_2 : ltac2:(tb__ "0|1|
S59S4fSfS18S5bQ40A1A1S50R3A1SfS65Vsegs;S44Vsegs;S5aS0S1R6R5R4A5S22S0S1Z4A3R1R3A5S68Vsegs;S40R4R3S16S1aS4S69A2M0S1dS4S69S51S4eS0S1A3S53VAInv;VCST;VXGL;R6R5A5A4S17G0A1A3A5A3FrhoX;F_;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp HKc rhoX.
  refine (esec_tail_null 2%nat st0 4 CST XGL HCST HXGL HCSTM HCSTS NXS1f_0 ECertSf_0 RN_0 WRn_0 DKRn_0 NXRn_0 ENTn_0 IDn_0 A Kc rho tp _ (stopJ_stable_le _) HKc _ rhoX).
  left. reflexivity.
Qed.
End SEC0.
End SpineMallocSecIW2.

