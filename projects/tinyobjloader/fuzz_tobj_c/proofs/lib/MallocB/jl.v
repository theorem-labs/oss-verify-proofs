(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec2 jb F0A_instok.

(* [comment removed for export] *)
Module SpineMallocSec3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "not"; "@Corelib.Init.Datatypes"; "list"; "bool"; "nil"; "app"; "true"; "prod"; "cons"; "pair"; "option"; "Some"; "None"; "fst"; "length"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "rw"; "sprop"; "eval"; "ss_facts"; "ss_next"; "ss_objs"; "rl"; "SLit"; "sprop_below"; "swf"; "cell"; "mkObj"; "obj_range"; "rm"; "DUnknown"; "ranges_disjoint"; "SVar"; "holds"; "DZero"; "agree_below"; "image_byte"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_setS"; "ax_X"; "mkLeafA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "modulo"; "sub"; "pow"; "mul"; "land"; "of_nat"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "ageom"; "budget_bound"; "aa_ptr_committed"; "aa_sec"; "ag_ctx"; "ag_pab"; "ag_spacebeg"; "ag_thread"; "budget_ok_alloc"; "sec_chunk"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.SEC3"; "JGs"; "GS"; "slink"; "SKEL0"; "JGsC"; "clsP"; "pgq"; "noband"; "npg"; "range_noband"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "ulink"; "UStopLeOrPc"; "ustop"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "Kc_ok"; "unwind_stopJ"; "A_globals"; "top_high"; "tp_ok"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "stableA"; "liftKA"; "smatchA"; "LQA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "Sh"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "IMG_HI"; "round_up"; "HIGH_SHADOW_BEG"; "HIGH_SHADOW_END"; "LOW_SHADOW_BEG"; "SHADOW_GAP_BEG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "secneeded"; "rhoM_of"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@Stdlib.Lists.List"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST"; "carveS"; "B2"; "L1"; "L2"; "B1"; "F_map"; "Pret_ms"; "a0e2"; "a2e1"; "a2e2"; "O_1"; "fx2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "MSENT";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_MS"; "RT_sec"; "V_NCH"; "V_NRES"; "V_NS"; "V_PAB"; "nxS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "geom_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "budget_boundD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv"; "bumpV"; "JGsC"; "SHC"; "pendS"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "prim_credit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "rt_zoneG"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA SysCallA MmapA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Placement StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2 SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST.
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
Proof. intros A Kc rho a r tp tr md AXid H. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv.JGsC, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv.JGs in H. rewrite Hnx in H. unfold JGsC, JGs. rewrite !AXid. rewrite (PrimCredit.prim_credit_same A (bumpV A (bv_unsigned (rw rho 12%positive))) eq_refl). exact H. Qed.

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
S6S13S13S54R3R2R1A3S34S72R3A2S37Z0R3A2S34S35R5R4A2Z7fffff800000A2S55S6fR6A1A1S13S35S55S6fR7A1M0A1S3bS6eS57G0S35G0S36R6Z8A2A2A2A2A2S13S1S6OLh;R9S1S34S74R2A2S34R1S75A2A2S1S34S76R2A2S34R1S77A2A2X6x2S1S34Z643000R2A2S1S34R1S3aZ2Z40A2A2S1S34S71R2A2S34R1S70A2A2A2A2A2Th2;Tlo;F_;F_;F_;F_;FL;Fua;Fh;").
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
Module RebuildS.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "modulo"; "pow"; "sub"; "mul"; "of_nat"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "False"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "in_rangesZ"; "bview"; "ERRNO_A"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "PG"; "kPtrArrayReserve"; "kSpaceSize"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "sec_chunk"; "aa_geom"; "aa_sec"; "AA"; "aa_cls"; "aa_ptr_committed"; "ag_pab"; "aa_q_global"; "aa_q_thread"; "ag_spacebeg"; "ageom"; "aa_Km"; "aa_live"; "ag_thread"; "class_state"; "sc_map_beg"; "sc_map_size"; "aa_Kf"; "aa_V"; "aa_cache_inited"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "cs_empty"; "mkAA"; "mkSC"; "qbatch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.RebuildS"; "newZ"; "chg_s"; "secA"; "zimg"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "SEC_INST"; "AInvA"; "quarantine_repr"; "kAllocBegMagic"; "nthZ"; "q_foot"; "@Corelib.Init.Datatypes"; "pair"; "Some"; "list"; "option"; "None"; "cons"; "length"; "prod"; "app"; "nat"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Stdlib.Lists.List"; "In"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "secneeded"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv"; "pendS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "cls_foot"; "rt_zoneM"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvEnsure OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition secA (A : AA) (ua nv : Z) : AA := ltac2:(tb__ "0|0|
S36S1eVA;A1S21VA;A1S30VA;A1S50S1dS1fVA;A1S4dS1dS37Vua;S56Vnv;A1S57Vnv;A1A3S52S1dA1A3A3S22VA;A1S4dS4fS0S0A2S48S0S0S2Vua;Z1800A2Vnv;A4S29VA;A1A3S25VA;A1S24VA;A1S31VA;A1S33VA;A1S32VA;A1S34VA;A1S2fVA;A1S28VA;A1S2eVA;A1Af").

Definition newZ (ua L : Z) (z : Z) : Prop := ltac2:(tb__ "0|1|
SdSaS1Vua;Vz;A2S3Vz;S2Vua;VL;A2A2A2SaS1S16Vua;A1M0Vz;A2S3Vz;S2G0S4VL;Z8A2A2A2A2A2").

Definition zimg (z : Z) : Prop := ltac2:(tb__ "0|0|
SdSaS1S42Vz;A2S3Vz;Zead04A2A2SdSaS1Zead08Vz;A2S3Vz;Zead30A2A2SdSbS0Vz;Z170320A3SaS1S14Vz;A2S3Vz;S2S14Z4A2A2A2A2A2A2").
Definition chg_s (G : ageom) (ua L pw blk : Z) (z : Z) : Prop := ltac2:(tb__ "0|1|
SdS3eVz;A1SdSaS1S2S2aVG;A1M0Zad0A2Vz;A2S3Vz;S2G0Zc60A2A2A2SdS3bVua;VL;Vz;A3SaS1Vpw;Vz;A2S3Vz;S2Vpw;Vblk;A2A2A2A2A2A2").

Lemma sh_apart : ltac2:(tb__ "0|6|
S0S0S0S0S0SbS0S5R5Z8M0A2Z0M1A3M2G2S1G1R6A2M3G3G3SdS1S2R8R7A2RaA2S1S2RaR9A2R8A2A2SaS1S16R9A1M4R7A2S3R7S2G4S4S2R8Z7A2G0A2A2A2A2ScSaS1S16RcA1M5R8A2S3R8S2G5S4RbG0A2A2A2A2A1F_;F_;F_;F_;F_;F_;F_;Fz;Flen;Flo;FL;Fua;").
Proof.
  intros ua L lo len z Hu HL HL0 Hlo Hlen Hs Hz X. unfold Sh in *.
  pose proof (Z.div_mod ua 8 ltac:(lia)) as DU. rewrite Hu, Z.add_0_r in DU.
  pose proof (Z.div_mod L 8 ltac:(lia)) as DL. rewrite HL, Z.add_0_r in DL.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (len + 7) 8 ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(lia)) as M2.
  destruct Hs as [Hs|Hs]; lia.
Qed.
Lemma sh_apart2 : ltac2:(tb__ "0|4|
S0S0S0S0S0SbS0S5R5Z8M0A2Z0M1A3M2G2S1G1R6A2SdS1R5R8A2S1S2R8R7A2R6A2A2SaS1S16R7A1R5A2S3R5S16R6A1A2A2ScSaS1S16RaA1M3R6A2S3R6S2G3S4R9G0A2A2A2A2A1F_;F_;F_;F_;F_;Fz;Fhi;Flo;FL;Fua;").
Proof.
  intros ua L lo hi z Hu HL HL0 Hs Hz X. unfold Sh in *.
  pose proof (Z.div_mod ua 8 ltac:(lia)) as DU. rewrite Hu, Z.add_0_r in DU.
  pose proof (Z.div_mod L 8 ltac:(lia)) as DL. rewrite HL, Z.add_0_r in DL.
  destruct Hs as [Hs|Hs].
  - pose proof (Z.div_le_mono hi ua 8 ltac:(lia) Hs). lia.
  - pose proof (Z.div_le_mono (ua + L) lo 8 ltac:(lia) Hs) as D. replace (ua + L) with ((ua / 8 + L / 8) * 8) in D by lia. rewrite Z.div_mul in D by lia. lia.
Qed.

Section Foot.
Variables (ua L : Z).
Hypothesis U8 : ua mod 8 = 0.
Hypothesis L8 : L mod 8 = 0.
Hypothesis L0 : 0 < L.
Hypothesis UI : IMG_HI <= ua.
Hypothesis UT : ua + L <= 140737479966720.
Hypothesis UB : ltac2:(tb__ "0|0|
SdS1S2Vua;VL;A2S18A2S1S17Vua;A2A2").

Lemma app_new : ltac2:(tb__ "0|1|
S0S0S0S1Z0R3A2M0G0S1S2R5R4A2Z7fffff800000A2SdS1S2R6R5A2Vua;A2S1S2Vua;VL;A2R6A2A2SdS1S2R7R6A2S18A2S1S17R7A2A2SaS1R8R6A2S3R6S2R8R7A2A2A2ScS3bVua;VL;R7A3A1F_;F_;F_;F_;F_;F_;Fz;Flen;Flo;").
Proof.
  intros lo len z Hlo Hlen Htop Hs Hb Hz [X|X]; [lia|].
  pose proof (sh_run_band2 ua (ua + L) z ltac:(unfold IMG_HI in UI; lia) ltac:(lia)) as BY.
  assert (E : Sh (ua + L) = Sh ua + L / 8).
  { unfold Sh. pose proof (Z.div_mod L 8 ltac:(lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by lia. lia. }
  rewrite E in BY. specialize (BY X). lia.
Qed.
Lemma sh_new : ltac2:(tb__ "0|2|
S0S0S0S1Z0R3A2M0G0S1S2R5R4A2Z7fffff800000A2SdS1S2R6R5A2Vua;A2S1S2Vua;VL;A2R6A2A2SaS1S16R7A1M1R5A2S3R5S2G1S4S2R6Z7A2Z8A2A2A2A2ScS3bVua;VL;R6A3A1F_;F_;F_;F_;F_;Fz;Flen;Flo;").
Proof.
  intros lo len z Hlo Hlen Htop Hs Hz [X|X].
  - pose proof (sh_run_band lo len z Hlo Hlen Htop Hz) as BY. lia.
  - exact (sh_apart ua L lo len z U8 L8 ltac:(lia) Hlo Hlen Hs Hz X).
Qed.
Lemma sh2_new : ltac2:(tb__ "0|0|
S0S0S0S1Z0R3A2SaS1R4R3A2S1R3Z7fffff800000A2A2SdS1R4Vua;A2S1S2Vua;VL;A2R5A2A2SaS1S16R6A1R4A2S3R4S16R5A1A2A2ScS3bVua;VL;R5A3A1F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z Hlo Hhi Hs Hz [X|X].
  - pose proof (sh_run_band2 lo hi z Hlo Hhi Hz) as BY. lia.
  - exact (sh_apart2 ua L lo hi z U8 L8 ltac:(lia) Hs Hz X).
Qed.

Variable A : AA.
Variable m : bview.
Hypothesis HG : geom_ok (aa_geom A).
Hypothesis Hsep : live_sep A.
Hypothesis HI3 : inv3 A.
Hypothesis HPR : primary_repr m A.
Hypothesis HSR : secondary_repr m A.
Hypothesis SSP : ltac2:(tb__ "0|0|
S59S48S0S0Vua;VL;A4S48S0S0S26S1eVA;A1A1S2S1bZ1000A2A4A2").
Hypothesis SSX : ltac2:(tb__ "0|0|
S1dS54S1dR1S1fVA;A1A3S59S48S0S0Vua;VL;A4S48S0S0S2cR2A1S2dR2A1A4A2F_;Fch;").

Lemma space_new : ltac2:(tb__ "0|1|
S0SaS1S26S1eVA;A1A1M0R1A2S3R1S2S2G0S6Z2Z25A2A2Z1000A2A2A2ScS3bVua;VL;R2A3A1F_;Fz;").
Proof.
  intros z Hz. pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _ & TG). rewrite kSpaceSize_val in S2.
  unfold HIGH_SHADOW_END in S1. unfold sepZ in SSP. cbn [fst snd] in SSP. rewrite kSpaceSize_val in SSP.
  apply (app_new (ag_spacebeg (aa_geom A)) (2 ^ 37 + 4096) z); unfold SHADOW_BAND_HI, HIGH_SHADOW_END; lia.
Qed.
Lemma space_sh_new : ltac2:(tb__ "0|1|
S0S0S0S1S26S1eVA;A1A1M0R3A2S1R4R3A2S1R4S2S2G0S6Z2Z25A2A2Z1000A2A2SaS1S16R6A1R4A2S3R4S16R5A1A2A2ScS3bVua;VL;R5A3A1F_;F_;F_;F_;Fz;Fhi;Flo;").
Proof.
  intros lo hi z H1 H2 H3 Hz. pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _ & TG). rewrite kSpaceSize_val in S2.
  unfold HIGH_SHADOW_END in S1. unfold sepZ in SSP. cbn [fst snd] in SSP. rewrite kSpaceSize_val in SSP.
  apply (sh2_new lo hi z); lia.
Qed.
Lemma chunk_new : ltac2:(tb__ "0|2|
S51S1dS0SbS4bS1dA1S55S1dS1fVA;A1R3A3S49S1dR2A2A3SdSaS1S2cR3A1M0R2A2S3R2S2G0S2dR3A1A2M1A2A2SaS1S16G0A1R2A2S3R2S16G1A1A2A2A2ScS3bVua;VL;R3A3A1F_;F_;Fz;Fch;Fi;").
Proof.
  intros i ch z Hi Hz. destruct HSR as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _).
  pose proof (topG_range (aa_geom A)) as TG. pose proof (SSX ch (nth_error_In _ _ Hi)) as SX. unfold sepZ in SX. cbn [fst snd] in SX.
  pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; lia)) as BI. unfold IMG_HI in BI. destruct D10 as (_ & _ & _ & _ & DB). unfold PG in D8.
  destruct Hz as [Hz|Hz].
  - apply (app_new (sc_map_beg ch) (sc_map_size ch) z); lia.
  - apply (sh2_new (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z); lia.
Qed.

Lemma live_foot_new : ltac2:(tb__ "0|1|
S0S0S0S54S4fS0S0A2S48S0S0R3R2A4S29VA;A1A3SdSaS1S7R4S1cR3A1A2R2A2S3R2S2R4R3A2A2A2SaS1S16R4A1M0R2A2S3R2S2G0S4S2R3Z7A2Z8A2A2A2A2A2ScS3bVua;VL;R3A3A1F_;F_;Fz;Fn;Fb;").
Proof.
  intros b n z Hin Hz.
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  destruct (Hsep b n Hin) as (L1 & L2 & L3 & _). unfold IMG_HI in L2. fold G in L3.
  pose proof (rz_bound n) as RZB.
  pose proof HI3 as (_ & LIV3 & _).
  unfold sepZ in SSP. cbn [fst snd] in SSP. fold G SB in SSP. rewrite kSpaceSize_val in SSP.
  destruct (LIV3 b n Hin) as [PRM | (ch & Hch & Eb & Esz)].
  - assert (Hn : 1 <= n <= 64512).
    { split; [exact L1|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. set (c := ClassID (needed n)) in D1, D2, D3, Y3.
    destruct HPR as (_ & _ & _ & PC). pose proof (PC c D1) as PC'. fold G in PC'. unfold class_repr in PC'.
    destruct PC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _ & _).
    destruct (LV b n Hin PRM eq_refl) as (V1 & V2 & V3). fold SB in V1, V2, V3.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3.
    assert (ERB : region_beg SB c = SB + c * 2 ^ 32) by reflexivity. rewrite ERB in V1, V3.
    assert (BLO : SB <= b - rz n /\ b + n <= SB + 2 ^ 37) by (clear -V1 V3 M2 M3 D1 Y1 Y3 Hn; nia).
    destruct Hz as [Hz|Hz].
    + apply space_new. fold G SB. clear -Hz BLO. lia.
    + pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). fold G SB in S1, S2. rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
      apply (sh_new b n z); [clear -L2; lia | clear -L1; lia | clear -L3 ACV; lia | clear -BLO SSP RZB; lia | exact Hz].
  - destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct HSR as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in D6, D8, D11, Eb.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    pose proof (SSX ch Hch) as SX. unfold sepZ in SX. cbn [fst snd] in SX.
    assert (INB : sc_map_beg ch <= b - rz n /\ b + n <= sc_map_beg ch + sc_map_size ch) by (clear -Eb Esz RZB D8 D11 RU1 RU2 L1; lia).
    destruct Hz as [Hz|Hz].
    + apply (chunk_new i ch z Hi). left. clear -Hz INB. lia.
    + apply (sh_new b n z); [clear -L2; lia | clear -L1; lia | clear -L3 ACV; lia | clear -INB SX RZB; lia | exact Hz].
Qed.

Lemma cls_foot_new : ltac2:(tb__ "0|3|
S0SaS1Z1R1A2S1R1Z1eA2A2S0S5eS1eVA;A1M0R3S46S2bS21VA;A1R3S35A4R1A4ScSaS1S2S2S2aG0A1Zd0A2S8Z50M1R4A2A2M2R2A2S3R2S2G2G1A2A2A2A1ScS3bVua;VL;R3A3A1F_;F_;Fz;F_;Fc;").
Proof.
  intros c Hc z Hz NT.
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  destruct HPR as (_ & _ & _ & PC). pose proof (PC c Hc) as X. fold G in X. unfold class_repr in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & M5 & M6 & _).
  pose proof (geom_old _ HG) as Y. rewrite kSpaceSize_val in Y. unfold HIGH_SHADOW_END in Y. fold G SB in Y.
  destruct Y as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _).
  unfold cls_foot in Hz. cbn zeta in Hz. fold G SB in Hz. unfold region_info, free_array, region_beg in Hz.
  unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize, kRegionInfoStride, kSpaceSize in *.
  destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
  - apply space_new. fold G SB. clear -Hz Hc. lia.
  - apply space_new. fold G SB. clear -Hz Hc M5 M6. nia.
  - apply space_new. fold G SB. clear -Hz Hc M1 M2 M3. nia.
  - apply (space_sh_new (SB + c * 2 ^ 32) (SB + c * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) c cs_empty)) z); fold G SB; [clear -Hc; nia | clear -M1 M2; lia | clear -Hc M1 M2 M3; nia | exact Hz].
  - exfalso. exact (NT Hz).
Qed.

Lemma q_foot_new : ltac2:(tb__ "0|0|
S44Vm;VA;A2S0S47VA;R1A2ScS3bVua;VL;R2A3A1F_;Fz;F_;").
Proof.
  intros (Q1 & _) z Hq.
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  pose proof HPR as (_ & _ & _ & PC).
  assert (REG : forall c, 1 <= c <= 30 -> SB <= region_beg SB c /\ region_beg SB c + cs_allocated_user (nthZ (aa_cls A) c cs_empty) <= SB + 2 ^ 37).
  { intros c Hc. pose proof (PC c Hc) as X. fold G SB in X. unfold class_repr in X.
    destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _).
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in *. unfold region_beg, kRegionSize. clear -Hc M1 M2 M3. nia. }
  assert (GSB : 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G).
  { pose proof (geom_old _ HG) as X. rewrite kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G SB in X. clear -X. tauto. }
  unfold sepZ in SSP. cbn [fst snd] in SSP. fold G SB in SSP. rewrite kSpaceSize_val in SSP.
  unfold q_foot in Hq. apply Exists_exists in Hq as (qb & Hqb & Hz).
  pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7). fold G SB in B7.
  destruct Hz as [Hz|Hz].
  { destruct B7 as (x & Ex & X0 & _ & XA). destruct (REG 24 ltac:(lia)) as [R1 R2]. unfold kQuarantineBatchSize in *.
    apply space_new. fold G SB. clear -Hz Ex X0 XA R1 R2. lia. }
  apply Exists_exists in Hz as (it & Hit & Hz). destruct (In_nth_error _ _ Hit) as [i Hi]. destruct (B6 i it Hi) as [_ IT].
  destruct IT as (J1 & J2 & _ & _ & _ & _ & _ & _ & JP & JS & _). unfold IMG_HI in J1. fold G SB in JP.
  pose proof (rz_bound (snd it)) as RZ. set (u := fst it) in *. set (n := snd it) in *.
  destruct (is_primary n) eqn:PRM.
  - assert (Hn : 1 <= n <= 64512).
    { split; [exact J2|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. destruct (JP eq_refl) as (V1 & V2 & V3). fold n in V1, V2, V3.
    set (c := ClassID (needed n)) in *. destruct (REG c D1) as [R1 R2].
    assert (BLO : SB <= u - rz n /\ u + n <= SB + 2 ^ 37) by (clear -V1 V3 R1 R2 Y1 Y3 Hn; nia).
    destruct Hz as [Hz|Hz].
    + apply space_new. fold G SB. clear -Hz BLO J2. lia.
    + apply (sh_new u n z); [clear -J1; lia | clear -J2; lia | clear -BLO GSB ACV; lia | clear -BLO SSP RZ; lia | exact Hz].
  - destruct (JS eq_refl) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [j Hj].
    destruct HSR as (SC1 & _). destruct (SC1 j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D12. unfold PG in *.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    pose proof (SSX ch Hch) as SX. unfold sepZ in SX. cbn [fst snd] in SX.
    assert (INB : sc_map_beg ch <= u - rz n /\ u + n <= sc_map_beg ch + sc_map_size ch) by (clear -Eu Esz RZ D8 D11 RU1 RU2 J2; lia).
    destruct Hz as [Hz|Hz].
    + apply (chunk_new j ch z Hj). left. clear -Hz INB J2. lia.
    + apply (sh_new u n z); [clear -J1; lia | clear -J2; lia | clear -INB D12 ACV; lia | clear -INB SX RZ; lia | exact Hz].
Qed.
End Foot.

Lemma quarantine_repr_sec_mono : ltac2:(tb__ "0|2|
S13S20S20SbS27S1eR1A1S1eR2A1A3SbS4aS2bA1S21R2A1S21R3A1A3SbS4aS38A1M0S25R3A1S25R4A1A3SbG0S24R4A1S24R5A1A3S1dS54S1dR1S1fR7A1M1A3S54S1dR2G1A3F_;Fch;S44R8R7A2S44R9R7A2F_;F_;F_;F_;F_;F_;FA';FA;Fm;").
Proof.
  intros m A A' EG EC ET EGq HS (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  unfold quarantine_repr. rewrite EG, ET, EGq.
  split; [|split; [exact Q2 | split; [exact Q3 | split; [exact Q4 | split; [exact Q5 | split; [exact Q6 | split; [exact Q7 | split; [exact Q8 | exact Q9]]]]]]]].
  apply Forall_forall. intros qb Hqb. pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
  unfold batch_repr. rewrite EG, EC.
  split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [|exact B7].
  intros i it Hi. destruct (B6 i it Hi) as [I1 I2]. split; [exact I1|].
  unfold q_item_ok in I2 |- *. cbn zeta in I2 |- *. rewrite EG, EC.
  destruct I2 as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11).
  split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|]. split; [exact J5|]. split; [exact J6|]. split; [exact J7|]. split; [exact J8|].
  split; [exact J9|]. split; [|exact J11].
  intros HP. destruct (J10 HP) as (ch & Hch & X). exists ch. split; [exact (HS ch Hch) | exact X].
Qed.

Lemma nth_error_snoc : forall {T} (l : list T) (x y : T) i, nth_error (l ++ [x]) i = Some y ->
  (nth_error l i = Some y /\ (i < length l)%nat) \/ (i = length l /\ y = x).
Proof.
  intros T l x y i H. destruct (Nat.lt_ge_cases i (length l)) as [Lt|Ge].
  - rewrite nth_error_app1 in H by exact Lt. left. exact (conj H Lt).
  - rewrite nth_error_app2 in H by exact Ge. destruct (i - length l)%nat as [|k] eqn:E; cbn in H.
    + right. split; [lia | congruence].
    + destruct k; discriminate H.
Qed.

Theorem sec_rebuild : ltac2:(tb__ "0|10|
S20S3aS3aS4aS40Q40M0A1A1S58S0S0S0S43S53R8R7R5R4A5SaS1Zfc01R4A2S3R4S6Z2M1Z27A2A2A2S1eRaA1S27S56R6A1S0S9S4eS1dS1fRcA1A2A1S0S2R7Z1800A2S0S2S23R4A1S8Z8M2R2A2A2S0S15S53S39RdA1A2S13S15S53S39RfA1A2S13S5aR11RbR6RdA4S1G2RbA2S1S2S8G2R7A2RcA2S22R13A1A2S1S2R8Z1M3A2S28R14A1A2S10R6S11RfU8M4RfA3A2S10R7S11S2R10G2A2G4RbA3A2S10R8S11S2R11Z10M5A2G4S57R12A1A3A2S10R9S11S2R12Z18M6A2G4RcA3A2S10RaS11RbG4R13A3A2S10RbS11S42G4S19A3A2S10RcS11S2S42G2A2G4S23R11A1A3A2S10RdS11S2S42G5A2G4S23R12A1A3A2S10ReS11S2S42G6A2G4S1aA3A2S10RfS11S2S42Z30A2G4S4S22R1eA1G2A2A3A2S10R10S11S2S42Z38A2G4S2R13G3A2A3A2S10R11S11Zead00U4M7Z0M8A3A2SbS4bS40Q8M9A1MaA1MbR12S7R14G5A2A1S49GaS3fG9G1A2A2A3S10R13S11S7R15ZcA2G7S5R1dS6G1Z20A2McA2A3A2S10R14S11S7R16ZeA2U2S4R1eGcA2A3A2SfGaGaSaSbGbR16S7R18ZfA2A1S49GaR1A2MdA3SbS0S5S41G9R1A2Z4A2G3A3A2Lt;A2S10R16S11S2R1fZ1000A2G4S45A3A2S10R17S11S2R20Z1008A2G4S7R19G5A2A3A2S0SaS1G8R1A2S3R1S4R23G2A2A2A2SbGbR1aS2S16R1cA1MeR2A2A1S49GaS3fG9G8A2A2A3F_;Fg;ScSbS0S5R23G2A2G8A3A1SbGbR1aS2GeS4R24G2A2A2A1S49GaS3fG9S5R24G2A2A2A2A3F_;S0S3cR20R24R1fR1cR23R1A6SfGaGaSbGbR1dR3A1GdA3Lb;A2F_;Fz;S0ScS3cR21R25R20R1dR24R1A6A1SbGbR1dR2A1R1cR2A1A3F_;Fz;S0SaS1S18R1A2S3R1S17A2A2ScSbGbS39R2cS3fG0R2A2A2S4cGaA1MfA3A1ScSbGbS39R2cS3fG0R3A2A2GfA3A1F_;F_;Fa;S43S53S3dR2cR26R27A3R2aR29R28A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TvE;Tv3;Tpw;Tub;Tidx;TL;TG;F_;F_;Fblk;Fua;Fnv;Fmd;Ftp;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp md nv ua blk HA Hnv. cbn zeta.
  intros HPD Hblk HROOM HKM C0 C8 C16 C24 CPW CI0 CI8 CI16 CI24 C48 C56 CMU VH2 VHN VH0 VH1 VMG0 VMG8 VZ VP PRES VO DEFB.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  set (vE := view segsA (rm rhoE)) in *. set (v3 := view segsA (rm rho3)) in *.
  set (G := aa_geom A) in *. set (T := ag_thread G) in *. set (L := secmapsize nv) in *. set (idx := Z.of_nat (length (aa_sec A))) in *.
  set (ub := ua + 6144) in *. set (pw := ag_pab G + 8 * idx) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.
  pose proof (geom_bands _ HG) as (FB & TB & CB & DB & TI & CI & DI). fold G T in TB, TI. fold G in FB, CB, DB, CI, DI.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in FB, TB, CB, DB, TI, CI, DI.
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  destruct HPD as (PM & PAL & PL0 & PDI & ST & SC & SD & SF & SS & SP & SX & SDB). fold G L in PM, PL0, PDI, ST, SC, SD, SF, SS, SP, SX, SDB. fold T in ST.
  pose proof (secmapsize_bounds nv ltac:(clear -Hnv; lia)) as [SMB SMM]. fold L in SMB, SMM. unfold PG in SMM, PAL.
  pose proof (dyn_in_big _ _ _ PDI ltac:(clear -SMB; lia)) as UI. destruct PDI as (_ & _ & PDT & _ & PDB).
  pose proof (pab_facts _ A HSR) as (P1 & P2 & P3 & P4 & P5). fold G in P1, P2, P3. fold idx in P4.
  assert (U8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(clear; lia)) as X. rewrite PAL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (L8 : L mod 8 = 0).
  { pose proof (Z.div_mod L 4096 ltac:(clear; lia)) as X. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (L / 4096)) with ((512 * (L / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (UT : ua + L <= 140737479966720) by (clear -PDT ACV; lia).
  assert (ESHL : Sh (ua + L) = Sh ua + L / 8).
  { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }
  assert (RUNB : forall z, Sh ua <= z < Sh ua + L / 8 -> SHADOW_BAND_LO <= z < SHADOW_BAND_HI).
  { intros z Hz. apply (sh_run_band2 ua (ua + L) z); [unfold IMG_HI in UI; clear -UI; lia | clear -UT PL0; lia | rewrite ESHL; exact Hz]. }
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in RUNB, PDB.

  assert (APPN : forall lo len z, 0 <= lo -> 0 <= len -> lo + len <= 140737479966720 -> sepZ (ua, L) (lo, len) ->
                 (lo + len <= 0x7fff7000 \/ 0x10007fff8000 <= lo) -> lo <= z < lo + len -> ~ newZ ua L z).
  { intros lo len z H1 H2 H3 H4 H5 Hz. apply (app_new ua L L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) lo len z H1 H2 H3);
      [unfold sepZ in H4; cbn [fst snd] in H4; clear -H4; lia | unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact H5 | exact Hz]. }
  assert (NEW_img : forall z, z < IMG_HI -> ~ newZ ua L z).
  { intros z Hz [X|X]; [clear -X UI Hz; lia | pose proof (RUNB z X) as Y; unfold IMG_HI in Hz; clear -Y Hz; lia]. }
  assert (NEW_T : forall z, T <= z < T + 0x1000 -> ~ newZ ua L z).
  { intros z Hz. apply (APPN T 0x1000 z); [clear -G4; lia | clear; lia | clear -G5 ACV; lia | exact ST | clear -TB; lia | exact Hz]. }
  assert (NEW_pab : forall z, ag_pab G <= z < ag_pab G + kPtrArrayReserve -> ~ newZ ua L z).
  { intros z Hz. unfold kPtrArrayReserve in *. apply (APPN (ag_pab G) (2 ^ 23) z); [unfold IMG_HI in P1; clear -P1; lia | clear; lia | clear -P2 ACV; lia | exact SP | | exact Hz].
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in P3. clear -P3. lia. }
  assert (PWZ : forall z, pw <= z < pw + blk -> ag_pab G <= z < ag_pab G + kPtrArrayReserve).
  { intros z Hz. unfold pw in Hz. pose proof (Zle_0_nat (length (aa_sec A))) as NN. fold idx in NN. clear -Hz HROOM P4 NN. lia. }
  assert (ZD : forall z, chg_s G ua L pw blk z \/ ~ chg_s G ua L pw blk z) by (intros z; unfold chg_s, zimg, newZ; clear; lia).

  assert (AGI : forall z, z < IMG_HI -> ~ zimg z -> ~ (T + 2768 <= z < T + 3168) -> v3 z = vE z).
  { intros z H1 H2 H3. apply VO. intros [X|[X|[X|X]]]; [exact (H2 X) | exact (H3 X) | exact (NEW_img z H1 X) |].
    pose proof (PWZ z X) as Y. clear -Y H1 P1. lia. }
  assert (AGH : forall z, IMG_HI <= z -> ~ (T + 2768 <= z < T + 3168) -> ~ newZ ua L z -> ~ (pw <= z < pw + blk) -> v3 z = vE z).
  { intros z H1 H2 H3 H4. apply VO. intros [X|[X|[X|X]]]; [|exact (H2 X) | exact (H3 X) | exact (H4 X)].
    unfold zimg, SEC_INST, ERRNO_A, IMG_HI in *. clear -X H1. lia. }
  idtac "sr:1".

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz.
    unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin).
    unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
    unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
    - unfold rtc_cells_img in Hc. apply AGI; unfold IMG_HI, zimg, SEC_INST, ERRNO_A;
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; clear -X Y TI; lia|]); destruct Hc.
    - unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc.
      assert (ZZ : (T <= z < T + 288) \/ (ag_ctx G <= z < ag_ctx G + 0x1000) \/ (ag_dtls G <= z < ag_dtls G + 0x1000) \/ (ag_fsb G <= z < ag_fsb G + 97)).
      { repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; fold G T in X, Y; clear -X Y; lia|]). destruct Hc. }
      clear Hc X Y.
      assert (NZ : ~ newZ ua L z).
      { destruct ZZ as [Z1|[Z1|[Z1|Z1]]].
        - apply NEW_T. clear -Z1. lia.
        - apply (APPN (ag_ctx G) 0x1000 z); [clear -G6; lia | clear; lia | clear -G7 ACV; lia | exact SC | clear -CB; lia | exact Z1].
        - apply (APPN (ag_dtls G) 0x1000 z); [clear -G8; lia | clear; lia | clear -G9 ACV; lia | exact SD | clear -DB; lia | exact Z1].
        - rewrite FS_total_val in SF, FB. apply (APPN (ag_fsb G) 11571200 z); [clear -G2; lia | clear; lia | clear -G3 ACV; lia | exact SF | clear -FB; lia | clear -Z1; lia]. }
      assert (NP : ~ (pw <= z < pw + blk)).
      { intros X. pose proof (PWZ z X) as Y. destruct HI3 as ((_ & _ & _ & _ & PT & PF & PC & PD) & _). fold G T in PT, PF, PC, PD. rewrite FS_total_val in PF.
        unfold kPtrArrayReserve in *. clear -Y ZZ PT PF PC PD. lia. }
      destruct (Z_lt_dec z IMG_HI) as [LO|HI].
      + apply AGI; [exact LO | | clear -ZZ G10 G13 G14; intros X; unfold IMG_HI in *; lia].
        unfold zimg, SEC_INST, ERRNO_A. unfold IMG_HI in LO. clear -ZZ LO TI CI DI G2. intros X. lia.
      + apply AGH; [clear -HI; lia | | exact NZ | exact NP]. clear -ZZ G10 G13 G14. intros X. lia. }
  idtac "sr:2".

  assert (FZ : forall z, chg_s G ua L pw blk z -> fs_footb G z = false).
  { intros z [X|[X|[X|X]]].
    - apply (fs_footb_img G z HG). unfold zimg, SEC_INST, ERRNO_A in X. clear -X. lia.
    - apply (fs_footb_T G z HG). fold T. clear -X. lia.
    - rewrite FS_total_val in SF, FB. unfold sepZ in SF. cbn [fst snd] in SF.
      apply (fs_footb_false_intro G z); rewrite ?FS_frames_off_val, ?FS_total_val, ?FS_kFlagsOffset_val.
      + destruct X as [X|X]; [clear -X SF; lia | pose proof (RUNB z X) as Y; clear -Y FB; lia].
      + destruct X as [X|X]; [clear -X SF; lia | pose proof (RUNB z X) as Y; clear -Y FB; lia].
      + destruct X as [X|X].
        * pose proof (sh_run_band2 (ag_fsb G + 36864) (ag_fsb G + 11571200)) as BY.
          destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [Lz|Lz]; [left; exact Lz|right].
          destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
          specialize (BY z ltac:(clear -G2; lia) ltac:(clear -G3 ACV; lia) ltac:(clear -Lz R; lia)).
          unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. clear -BY X PDB. lia.
        * destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [Lz|Lz]; [left; exact Lz|right].
          destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
          apply (sh_apart2 ua L (ag_fsb G + 36864) (ag_fsb G + 11571200) z U8 L8 ltac:(clear -PL0; lia) ltac:(clear -SF; lia) ltac:(clear -Lz R; lia) X).
    - pose proof (PWZ z X) as Y. destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      apply (fs_footb_false_intro G z); rewrite ?FS_frames_off_val, ?FS_total_val, ?FS_kFlagsOffset_val.
      + clear -Y PF. lia.
      + clear -Y PF. lia.
      + pose proof (sh_run_band2 (ag_fsb G + 36864) (ag_fsb G + 11571200)) as BY.
        destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [Lz|Lz]; [left; exact Lz|right].
        destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
        specialize (BY z ltac:(clear -G2; lia) ltac:(clear -G3 ACV; lia) ltac:(clear -Lz R; lia)).
        clear -BY Y P3. unfold kPtrArrayReserve in *. lia. }

  assert (HFS : fs_inv (restrictv (fs_footb G) v3) (secA A ua nv)).
  { rewrite (restrictv_ext (fs_footb G) vE v3).
    2: { intros z Hz. apply VO. intros Zz. rewrite (FZ z Zz) in Hz. discriminate Hz. }
    exact HF. }
  idtac "sr:3".

  set (mE := maskv (fs_footb G) vE) in *. set (m3 := maskv (fs_footb G) v3).
  assert (AGm : forall z, ~ chg_s G ua L pw blk z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. apply VO. exact Hz. }
  assert (AGmI : forall z, z < IMG_HI -> ~ zimg z -> ~ (T + 2768 <= z < T + 3168) -> m3 z = mE z).
  { intros z H1 H2 H3. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. exact (AGI z H1 H2 H3). }
  assert (AGmH : forall z, IMG_HI <= z -> ~ (T + 2768 <= z < T + 3168) -> ~ newZ ua L z -> ~ (pw <= z < pw + blk) -> m3 z = mE z).
  { intros z H1 H2 H3 H4. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. exact (AGH z H1 H2 H3 H4). }
  assert (CHm : forall z, chg_s G ua L pw blk z -> m3 z = v3 z).
  { intros z Hz. unfold m3. apply maskv_out. exact (FZ z Hz). }
  assert (PRm : forall z, chg_s G ua L pw blk z -> exists b, m3 z = Some b).
  { intros z Hz. rewrite (CHm z Hz). exact (PRES z Hz). }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (ZD z) as [Hc|Hn].
    - exact (PRm z Hc).
    - rewrite (AGm z Hn). exact (Hp z Hz). }
  assert (CELL3 : forall a w v, (forall k, (k < w)%nat -> chg_s G ua L pw blk (a + Z.of_nat k)) -> cell_ok v3 (mkACell a w v) -> cell_ok m3 (mkACell a w v)).
  { intros a w v Hk Hc k Hkw. cbn [c_addr c_w c_val] in *. rewrite (CHm _ (Hk k Hkw)). exact (Hc k Hkw). }

  assert (SSP' : sepZ (ua, L) (ag_spacebeg (aa_geom A), kSpaceSize + 4096)) by exact SS.
  pose proof (live_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A mE HG Hsep HI3 HPR HSR SSP' SX) as LFN.
  pose proof (cls_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A mE HG HPR SSP') as CFN.
  pose proof (q_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A mE HG HPR HSR SSP' SX HQR) as QFN.
  pose proof (chunk_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A mE HSR SX) as CHN.
  assert (NPWpab : forall z, ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> ~ (pw <= z < pw + blk)) by (intros z H X; exact (H (PWZ z X))).

  assert (NB : ub + nv + 2048 <= ua + L /\ nv / 8 <= L / 8 - 1024 /\ rz nv = 2048 /\ is_primary nv = false).
  { split; [|split; [|split; [apply rz_large; clear -Hnv; lia | apply not_primary_large; clear -Hnv; lia]]].
    - unfold ub, L, secmapsize, secneeded, PG. pose proof (round_up_ge nv 8 ltac:(clear; lia)) as R1.
      pose proof (round_up_ge (round_up nv 8 + 4096) 4096 ltac:(clear; lia)) as R2. clear -R1 R2. lia.
    - unfold L, secmapsize, secneeded, PG. pose proof (round_up_ge nv 8 ltac:(clear; lia)) as R1.
      pose proof (round_up_ge (round_up nv 8 + 4096) 4096 ltac:(clear; lia)) as R2.
      pose proof (Z.div_le_mono (nv + 8192) (round_up (round_up nv 8 + 4096) 4096 + 4096) 8 ltac:(clear; lia) ltac:(clear -R1 R2; lia)) as D.
      replace (nv + 8192) with (nv + 1024 * 8) in D by (clear; lia). rewrite Z.div_add in D by (clear; lia). clear -D. lia. }
  destruct NB as (NB1 & NB2 & ERZ & ENP).
  assert (ESHub : Sh ub = Sh ua + 768).
  { unfold Sh, ub. replace (ua + 6144) with (ua + 768 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear. lia. }
  assert (INnew : forall z, ua <= z < ua + L -> chg_s G ua L pw blk z) by (intros z Hz; right; right; left; left; exact Hz).
  assert (INrun : forall z, Sh ua <= z < Sh ua + L / 8 -> chg_s G ua L pw blk z) by (intros z Hz; right; right; left; right; exact Hz).
  idtac "sr:4".

  assert (HLS : live_sep (secA A ua nv)).
  { intros b n Hin. cbn [aa_live secA] in Hin. cbn [aa_geom secA]. fold G. destruct Hin as [E|Hin]; [|exact (Hsep b n Hin)].
    injection E as <- <-. fold ub. unfold sepZ in SF, ST, SC, SD. cbn [fst snd] in SF, ST, SC, SD. fold T in ST |- *.
    split; [clear -Hnv; lia|]. split; [unfold ub; clear -UI; lia|]. split; [clear -NB1 PDT; lia|].
    split; [unfold ub; clear -SF NB1; lia|]. split; [unfold ub; clear -ST NB1; lia|]. split; [unfold ub; clear -SC NB1; lia|]. split; [unfold ub; clear -SD NB1; lia|].
    unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. unfold ub. clear -PDB NB1. lia. }
  assert (HLB : live_block_repr m3 (secA A ua nv)).
  { intros b n Hin. cbn [aa_live secA] in Hin. destruct Hin as [E|Hin].
    - injection E as <- <-. fold ub.
      assert (CU : forall z, ua <= z < ua + L -> m3 z = v3 z) by (intros z Hz; apply CHm; apply INnew; exact Hz).
      assert (CS : forall z, Sh ua <= z < Sh ua + L / 8 -> m3 z = v3 z) by (intros z Hz; apply CHm; apply INrun; exact Hz).
      pose proof (Z.div_pos nv 8 ltac:(clear -Hnv; lia) ltac:(clear; lia)) as DP.
      split; [rewrite CU by (unfold ub; clear -SMB; lia); exact VH2|].
      split; [apply CELL3; [intros k Hk; apply INnew; unfold ub; clear -Hk SMB; lia | exact VHN]|].
      split; [apply CELL3; [intros k Hk; apply INnew; unfold ub; clear -Hk SMB; lia | exact VH0]|].
      split; [split|split].
      + intros g Hg. rewrite CS by (rewrite ESHub; clear -Hg NB2; lia). exact (VZ g Hg).
      + intros Hm. rewrite CS by (rewrite ESHub; clear -DP NB2; lia). exact (VP Hm).
      + right. rewrite ERZ. replace (ub - 2048) with (ua + 4096) by (unfold ub; clear; lia). replace (ua + 4096 + 8) with (ua + 4104) by (clear; lia).
        split; apply CELL3; first [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | assumption].
      + destruct VH1 as (t & Ht & Hm4). exists t. split; [rewrite CU by (unfold ub; clear -SMB; lia); exact Ht | exact Hm4].
    - destruct (Hlive b n Hin) as (B1 & B2 & B3 & [B4 B5] & B6 & B7).
      assert (NO : forall z, (b - rz n <= z < b + n \/ Sh b <= z < Sh b + (n + 7) / 8) -> m3 z = mE z).
      { intros z Hz. destruct (live_foot mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as (X & Y & _). fold G T in Y.
        pose proof (live_foot_pab mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as Z1. fold G in Z1.
        apply AGmH; [exact X | clear -Y; lia | exact (LFN b n z Hin Hz) | exact (NPWpab z Z1)]. }
      pose proof (rz_bound n) as RZ. destruct (Hsep b n Hin) as (L1 & _).
      pose proof (Z.div_le_mono n (n + 7) 8 ltac:(clear; lia) ltac:(clear; lia)) as DL. pose proof (Z.div_pos n 8 ltac:(clear -L1; lia) ltac:(clear; lia)) as DP.
      split; [rewrite NO by (left; clear -RZ L1; lia); exact B1|].
      split; [eapply cell_ok_agree; [|exact B2]; cbn [c_addr c_w]; intros k Hk; apply NO; left; clear -RZ L1 Hk; lia|].
      split; [eapply cell_ok_agree; [|exact B3]; cbn [c_addr c_w]; intros k Hk; apply NO; left; clear -RZ L1 Hk; lia|].
      split; [split|split].
      + intros g Hg. rewrite NO by (right; clear -Hg DL; lia). exact (B4 g Hg).
      + intros Hm. rewrite NO; [exact (B5 Hm)|]. right.
        replace ((n + 7) / 8) with (n / 8 + 1) by (apply Z.div_unique with (n mod 8 - 1); [pose proof (Z.mod_pos_bound n 8); clear -Hm H; lia | pose proof (Z.div_mod n 8); clear -H; lia]).
        clear -DP. lia.
      + apply (alloc_magic_ok_agree mE m3); [intros z Hz; apply NO; left; clear -Hz L1; lia | clear -RZ; lia | exact B6].
      + destruct B7 as (t & Ht & Hm4). exists t. split; [rewrite NO by (left; clear -RZ L1; lia); exact Ht | exact Hm4]. }
  idtac "sr:5".

  assert (LIVM : forall z, in_rangesZ (aa_live A) z -> in_rangesZ (aa_live (secA A ua nv)) z).
  { intros z (b & n & Hbn & Hz). exists b, n. split; [cbn [aa_live secA]; right; exact Hbn | exact Hz]. }
  assert (HPR' : primary_repr m3 (secA A ua nv)).
  { destruct HPR as (Q1 & Q2 & Q3' & P4'). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3'|].
    intros cl Hc. change (aa_geom (secA A ua nv)) with G. change (aa_cls (secA A ua nv)) with (aa_cls A).
    apply (class_repr_agree mE m3 G A (secA A ua nv) cl); [exact Hc | reflexivity | | reflexivity | | exact LIVM | | exact (P4' cl Hc)].
    - unfold secA. rewrite (live_ids_cons G A (ua + 6144) nv cl). rewrite ENP. reflexivity.
    - intros b n Hin HP _. cbn [aa_live secA] in Hin. destruct Hin as [E|Hin]; [|exact Hin]. injection E as <- <-. rewrite ENP in HP. discriminate HP.
    - intros z Hz.
      pose proof (cls_foot_pab mE A cl HG HI3 (conj Q1 (conj Q2 (conj Q3' P4'))) HSR Hc z Hz) as Y. fold G in Y.
      assert (TAIL : ~ (T + 0xd0 + 80 * cl <= z < T + 0xd0 + 80 * cl + 80) -> m3 z = mE z).
      { intros NTe. pose proof (CFN cl Hc z Hz NTe) as NZ.
        assert (ZH : IMG_HI <= z /\ ~ (T + 2768 <= z < T + 3168)).
        { pose proof (P4' cl Hc) as PCX. fold G in PCX. unfold class_repr in PCX.
          destruct PCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & M5 & M6 & _).
          unfold cls_foot in Hz. cbn zeta in Hz. fold G T in Hz. destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]]; [| | | |exfalso; exact (NTe Hz)].
          all: pose proof (geom_old _ HG) as X; rewrite kSpaceSize_val in X; unfold HIGH_SHADOW_END in X; fold G in X;
               destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _);
               destruct HI3 as ((T3 & _) & _); fold G T in T3; rewrite kSpaceSize_val in T3;
               unfold region_info, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kSpaceSize, kRegionInfoStride, Sh, SHADOW_OFF, IMG_HI in *.
          - clear -Hz Hc GS1 T3. lia.
          - unfold kUserMapSize in *. clear -Hz Hc GS1 T3 M5 M6. nia.
          - unfold kUserMapSize in *. clear -Hz Hc GS1 T3 M1 M2 M3. nia.
          - pose proof (Z.div_pos (ag_spacebeg G + cl * 2 ^ 32) 8 ltac:(clear -Hc GS1; lia) ltac:(clear; lia)) as D2.
            unfold kUserMapSize in *.
            pose proof (Z.div_le_mono (ag_spacebeg G + cl * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) cl cs_empty)) 140737479966720 8 ltac:(clear; lia) ltac:(clear -Hc M1 M2 M3 GS2 ACV; nia)) as D1.
            change (140737479966720 / 8) with 17592184995840 in D1. clear -Hz D1 D2 TB. lia. }
        apply AGmH; [exact (proj1 ZH) | exact (proj2 ZH) | exact NZ | exact (NPWpab z Y)]. }
      destruct (Z_le_dec (T + 0xd0 + 80 * cl) z) as [GE|LT]; [destruct (Z_lt_dec z (T + 0xd0 + 80 * cl + 80)) as [LT2|GE2]|].
      +
        assert (ZT : T <= z < T + 0x1000) by (clear -GE LT2 Hc; lia).
        destruct (Z_lt_dec z IMG_HI) as [LO|HI].
        * apply AGmI; [exact LO | unfold zimg, SEC_INST, ERRNO_A; unfold IMG_HI in LO; clear -ZT LO TI; intros X; lia | clear -GE LT2 Hc; lia].
        * apply AGmH; [clear -HI; lia | clear -GE LT2 Hc; lia | exact (NEW_T z ZT) | exact (NPWpab z Y)].
      + apply TAIL. clear -GE2. lia.
      + apply TAIL. clear -LT. lia. }
  idtac "sr:6".

  assert (AGpabOld : forall z, ag_pab G <= z < pw -> m3 z = mE z).
  { intros z Hz. pose proof (Zle_0_nat (length (aa_sec A))) as NN. fold idx in NN.
    assert (ZP : ag_pab G <= z < ag_pab G + kPtrArrayReserve) by (unfold pw in Hz; clear -Hz HROOM P4 NN Hblk; lia).
    destruct HI3 as ((_ & _ & _ & _ & PT & _) & _). fold G T in PT.
    apply AGmH; [clear -ZP P1; lia | clear -ZP PT; unfold kPtrArrayReserve in *; lia | exact (NEW_pab z ZP) | clear -Hz; lia]. }
  assert (HSR' : secondary_repr m3 (secA A ua nv)).
  { pose proof HSR as (S1 & SPT & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
    unfold secondary_repr. cbn [aa_geom aa_sec aa_ptr_committed aa_live secA]. fold G.
    assert (ELEN : Z.of_nat (length (aa_sec A ++ [mkSC ua L (secneeded nv)])) = idx + 1) by (rewrite length_app; cbn [length]; unfold idx; clear; lia).
    fold L. rewrite ELEN.
    split.
    { intros i ch Hi. apply nth_error_snoc in Hi as [[Hi Lt]|[-> ->]].
      - destruct (S1 i ch Hi) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14). fold G in C5, D10, D12.
        assert (MS : 0 <= sc_map_size ch) by (unfold PG in D8; clear -D8 D9; lia).
        assert (AGC : forall z, (sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch \/ Sh (sc_map_beg ch) <= z < Sh (sc_map_beg ch + sc_map_size ch)) -> m3 z = mE z).
        { intros z Hz. pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; clear -D8 D9; lia)) as BI.
          destruct HI3 as (_ & _ & SEC3 & _). destruct (SEC3 i ch Hi) as (_ & STh & SPb & _). fold G T in STh, SPb.
          pose proof D10 as (D10a & _ & _ & _ & D10b). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in D10b.
          apply AGmH; [| | exact (CHN i ch z Hi Hz) |].
          - destruct Hz as [Hz|Hz]; [clear -Hz BI; lia|]. unfold Sh, SHADOW_OFF, IMG_HI in *. pose proof (Z.div_pos (sc_map_beg ch) 8 ltac:(clear -D10a; lia) ltac:(clear; lia)). clear -Hz H. lia.
          - destruct Hz as [Hz|Hz]; [clear -Hz STh; lia|].
            pose proof (sh_run_band2 (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z ltac:(clear -D10a; lia) ltac:(clear -MS D12 ACV; lia) Hz) as BY.
            unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. clear -BY TB. lia.
          - apply NPWpab. destruct Hz as [Hz|Hz]; [clear -Hz SPb; unfold kPtrArrayReserve in *; lia|].
            pose proof (sh_run_band2 (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z ltac:(clear -D10a; lia) ltac:(clear -MS D12 ACV; lia) Hz) as BY.
            clear -BY P3. unfold kPtrArrayReserve in *. lia. }
        assert (CA : forall off w v, 0 <= off -> off + Z.of_nat w <= 32 -> cell_ok mE (mkACell (sc_map_beg ch + off) w v) -> cell_ok m3 (mkACell (sc_map_beg ch + off) w v)).
        { intros off w v Ho Hw. apply cell_ok_agree. cbn [c_addr c_w]. intros k Hk. apply AGC. left. unfold PG in D8. clear -Ho Hw Hk D8 D9. lia. }
        split; [apply CA; [clear; lia | cbn; clear; lia | exact C1]|]. split; [apply CA; [clear; lia | cbn; clear; lia | exact C2]|].
        split; [apply CA; [clear; lia | cbn; clear; lia | exact C3]|]. split; [apply CA; [clear; lia | cbn; clear; lia | exact C4]|].
        split; [eapply cell_ok_agree; [|exact C5]; cbn [c_addr c_w]; intros k Hk; apply AGpabOld; unfold pw, idx; cbn in Hk; clear -Hk Lt; lia|].
        split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
        split; [|eapply present_agree; [|exact D14]; intros z Hz; apply AGC; right; exact Hz].
        eapply present_but_mono; [exact LIVM | | exact D13]. intros z Hz _ Hm. rewrite (AGC z (or_introl Hz)). exact Hm.
      - cbn [sc_map_beg sc_map_size sc_size]. replace (Z.of_nat (length (aa_sec A))) with idx by reflexivity.
        split; [replace (ua + 0) with ua by (clear; lia); apply CELL3; [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | exact C0]|].
        split; [apply CELL3; [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | exact C8]|].
        split; [apply CELL3; [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | exact C16]|].
        split; [apply CELL3; [intros k Hk; apply INnew; cbn in Hk; clear -Hk SMB; lia | exact C24]|].
        split; [apply CELL3; [intros k Hk; right; right; right; fold pw; cbn in Hk; clear -Hk Hblk; lia | exact CPW]|].
        split; [unfold PG; exact PAL|]. split; [unfold PG; exact SMM|].
        split; [unfold L, secmapsize, PG; pose proof (round_up_ge (secneeded nv) 4096 ltac:(clear; lia)) as R; clear -R; lia|].
        split; [unfold secneeded; pose proof (round_up_ge nv 8 ltac:(clear; lia)) as R; clear -R Hnv; lia|].
        split; [unfold dyn_in; unfold IMG_HI in UI; unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; clear -UI PL0 PDT PDB; lia|].
        split; [reflexivity|]. split; [exact PDT|].
        split; [intros z Hz _; apply PRm; apply INnew; exact Hz|].
        intros z Hz. apply PRm. apply INrun. rewrite <- ESHL. exact Hz. }
    split.
    { intros z Hz. destruct (ZD z) as [Hc|Hn]; [exact (PRm z Hc)|]. rewrite (AGm z Hn). apply SPT. fold G idx. clear -Hz. lia. }
    split; [clear -HROOM Hblk P4; lia|]. split; [exact S3|]. split; [exact S45|].
    assert (CZI : forall a w v, SEC_INST <= a -> a + Z.of_nat w <= 0xead04 -> cell_ok v3 (mkACell a w v) -> cell_ok m3 (mkACell a w v)).
    { intros a w v H1 H2. apply CELL3. intros k Hk. left. unfold zimg. clear -H1 H2 Hk. lia. }
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact CI0]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact CI8]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact CI16]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact CI24]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact C48]|].
    split; [apply CZI; [clear; lia | unfold SEC_INST; cbn; clear; lia | exact C56]|].
    split; [apply PRESX; exact I7|].
    split; [|apply PRESX; exact I9].
    apply CZI; [unfold SEC_INST; clear; lia | cbn; clear; lia | exact CMU]. }
  idtac "sr:7".
  assert (HQR' : quarantine_repr m3 (secA A ua nv)).
  { apply (quarantine_repr_sec_mono m3 A (secA A ua nv)); try reflexivity.
    - intros ch Hch. cbn [aa_sec secA]. apply in_or_app. left. exact Hch.
    - apply (quarantine_repr_agreeQ mE m3 A A); try reflexivity.
      + exact (q_items_rz A).
      + intros z Hz. pose proof HI3 as (_ & _ & _ & Q3 & _). destruct (Q3 z Hz) as [QT _]. fold G T in QT.
        pose proof (q_foot_high mE A z HQR Hz) as QH. pose proof (q_foot_pab mE A HG HI3 HPR HSR HQR z Hz) as Y. fold G in Y.
        apply AGmH; [exact QH | clear -QT; lia | exact (QFN z Hz) | exact (NPWpab z Y)].
      + intros z Hz. fold G T in Hz. assert (ZT : T <= z < T + 0x1000) by (clear -Hz; lia).
        destruct (Z_lt_dec z IMG_HI) as [LO|HI].
        * apply AGmI; [exact LO | unfold zimg, SEC_INST, ERRNO_A; unfold IMG_HI in LO; clear -ZT LO TI; intros X; lia | clear -Hz; lia].
        * pose proof HI3 as ((_ & _ & _ & _ & PT & _) & _). fold G T in PT.
          apply AGmH; [clear -HI; lia | clear -Hz; lia | exact (NEW_T z ZT) | apply NPWpab; clear -ZT PT; unfold kPtrArrayReserve in *; lia].
      + intros z Hz. apply AGmI; unfold QG, zimg, SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz; lia | clear -Hz TI; lia].
      + exact HQR. }
  assert (HIA' : ia_inv m3 (secA A ua nv)).
  { apply (ia_inv_agreeN mE m3 A (secA A ua nv)); [reflexivity | | exact HIA].
    intros z Hz. apply AGmI; unfold IA_BEG, IA_END, zimg, SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz; lia | clear -Hz TI; lia]. }
  assert (HTH' : thread_inv m3 G).
  { destruct HTH as [X Y]. fold T in X, Y |- *. split.
    - fold T. assert (ZT : T <= T + 3168 < T + 0x1000) by (clear; lia).
      destruct (Z_lt_dec (T + 3168) IMG_HI) as [LO|HI].
      + rewrite AGmI; [exact X | exact LO | unfold zimg, SEC_INST, ERRNO_A; unfold IMG_HI in LO; clear -LO TI; intros Z1; lia | clear; lia].
      + pose proof HI3 as ((_ & _ & _ & _ & PT & _) & _). fold G T in PT.
        rewrite AGmH; [exact X | clear -HI; lia | clear; lia | exact (NEW_T _ ZT) | apply NPWpab; clear -PT; unfold kPtrArrayReserve in *; lia].
    - fold T. apply PRESX. exact Y. }
  assert (HMI' : misc_inv m3).
  { apply (misc_inv_N mE m3); [| | | exact HMI].
    - intros z Hz. apply AGmI; unfold zimg, SEC_INST, ERRNO_A, IMG_HI in *; [clear -Hz; lia | clear -Hz; lia | clear -Hz TI; lia].
    - intros z Hz. apply PRm. left. unfold zimg. clear -Hz. lia.
    - intros z Hz. apply PRm. left. unfold zimg. clear -Hz. lia. }
  idtac "sr:8".
  assert (HDEP : depot_wf m3 (secA A ua nv)).
  { unfold depot_wf in HDW |- *. change (aa_depot (secA A ua nv)) with (aa_depot A).
    pose proof HI3 as (_ & _ & _ & _ & DEP3 & _).
    eapply depot_mem_frame; [|exact HDW]. intros a Ha.
    assert (BLKZ : forall bb LL, In (bb, LL) (dblocks (aa_depot A)) -> 0xf000 < LL -> bb <= a < bb + LL -> m3 a = mE a).
    { intros bb LL Hb HLL Hab. destruct (DEP3 (bb, LL) Hb) as (DY & STb & _ & _ & _ & _ & SPb & _). cbn [fst snd] in DY.
      unfold sepZ in STb, SPb. cbn [fst snd] in STb, SPb. fold G T in STb, SPb.
      pose proof (dyn_in_big _ _ _ DY HLL) as BB. pose proof DY as (_ & _ & DT & _ & DBb). fold G in DT.
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in DBb.
      pose proof (SDB (bb, LL) Hb) as SN.
      apply AGmH; [clear -BB Hab; lia | clear -STb Hab; lia | | apply NPWpab; clear -SPb Hab; unfold kPtrArrayReserve in *; lia].
      apply (APPN bb LL a); [unfold IMG_HI in BB; clear -BB; lia | clear -HLL; lia | clear -DT ACV; lia | apply sepZ_sym; exact SN | exact DBb | exact Hab]. }
    destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
    - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. apply AGmI; unfold zimg, SEC_INST, ERRNO_A, IMG_HI; [clear -Hs; lia | clear -Hs; lia | clear -Hs TI; lia].
    - apply (BLKZ bb NBSZ); [unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb] | unfold NBSZ; clear; lia | exact Hab].
    - apply (BLKZ bb FBSZ); [unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb] | unfold FBSZ; clear; lia | exact Hab]. }
  idtac "sr:9".

  assert (HMD : model_inv segsA (secA A ua nv) tp md).
  { unfold model_inv in HM |- *. cbn [aa_geom aa_V aa_Km aa_Kf secA]. fold G.
    destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
    split.
    { unfold vm_geom in V1 |- *. cbn [aa_sec aa_geom secA]. fold G. fold G in V1.
      destruct V1 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
      split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|]. split; [exact N7|]. split; [|exact N9].
      intros ch Hch. apply in_app_or in Hch as [Hch|[<-|[]]]; [exact (N8 ch Hch)|]. cbn [sc_map_beg sc_map_size]. exact PM. }
    split; [exact V2|]. split; [exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [exact V6|]. split; [exact V7|].
    unfold ledger_inv in V8 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_sec secA] in V8 |- *.
    destruct V8 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8' & L9 & L10).
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8'|].
    split; [|exact L10]. rewrite length_app. cbn [length]. fold idx in HKM. unfold idx in HKM. clear -HKM. lia. }
  idtac "sr:10".
  assert (HI3' : inv3 (secA A ua nv)).
  { pose proof HI3 as (SG3 & LIV3 & SEC3 & Q3 & DEP3 & ND3 & CNT3 & SML3 & QCI3).
    unfold inv3. cbn [aa_geom aa_live aa_sec aa_cls aa_depot secA]. fold G.
    split; [exact SG3|].
    split.
    { intros b n Hin. destruct Hin as [E|Hin].
      - injection E as <- <-. right. exists (mkSC ua L (secneeded nv)). split; [apply in_or_app; right; left; reflexivity|].
        cbn [sc_map_beg sc_size]. split; [unfold PG; clear; lia | reflexivity].
      - destruct (LIV3 b n Hin) as [P|(ch & Hch & X)]; [left; exact P | right; exists ch; split; [apply in_or_app; left; exact Hch | exact X]]. }
    split.
    { unfold sepZ in SS, ST, SP, SF, SC, SD. cbn [fst snd] in SS, ST, SP, SF, SC, SD. fold T in ST |- *.
      intros i ch Hi. apply nth_error_snoc in Hi as [[Hi Lt]|[-> ->]].
      - destruct (SEC3 i ch Hi) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). fold G T in X1, X2, X3, X4, X6, X7.
        split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [|exact (conj X6 X7)].
        intros j ch' Hj Hij. apply nth_error_snoc in Hj as [[Hj _]|[-> ->]]; [exact (X5 j ch' Hj Hij)|].
        cbn [sc_map_beg sc_map_size]. pose proof (SX ch (nth_error_In _ _ Hi)) as Y. unfold sepZ in Y. cbn [fst snd] in Y. clear -Y. lia.
      - cbn [sc_map_beg sc_map_size].
        split; [clear -SS; lia|]. split; [clear -ST; lia|]. split; [clear -SP; lia|]. split; [clear -SF; lia|]. split; [|split; [clear -SC; lia | clear -SD; lia]].
        intros j ch' Hj Hij. apply nth_error_snoc in Hj as [[Hj _]|[E _]]; [|exfalso; exact (Hij (eq_sym E))].
        pose proof (SX ch' (nth_error_In _ _ Hj)) as Y. unfold sepZ in Y. cbn [fst snd] in Y. exact Y. }
    split; [exact Q3|].
    split.
    { intros bn Hbn. destruct (DEP3 bn Hbn) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
      split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|]. split; [exact D7|].
      intros ch Hch. apply in_app_or in Hch as [Hch|[<-|[]]]; [exact (D8 ch Hch)|]. cbn [sc_map_beg sc_map_size]. exact (SDB bn Hbn). }
    split.
    {
      cbn [List.filter snd]. rewrite ENP. cbn [negb List.map fst app].
      constructor; [|exact ND3]. intros Hin. apply (proj1 (list_elem_of_In _ _)) in Hin.
      assert (OLDU : exists ch, In ch (aa_sec A) /\ ua + 6144 = sc_map_beg ch + PG + 2048).
      { apply in_app_or in Hin as [Hin|Hin].
        - apply in_map_iff in Hin as ([b n] & Eb & Hf). cbn [fst] in Eb. subst b. apply filter_In in Hf as [Hl Hp]. cbn [snd] in Hp.
          destruct (LIV3 _ _ Hl) as [P|(ch & Hch & X & _)]; [rewrite P in Hp; discriminate Hp | exists ch; exact (conj Hch X)].
        - apply in_map_iff in Hin as ([u n] & Eu & Hf). cbn [fst] in Eu. subst u. apply filter_In in Hf as [Hq Hp]. cbn [snd] in Hp.
          unfold qitems in Hq. apply in_flat_map in Hq as (qb & Hqb & Hit).
          destruct HQR as (QB & _). pose proof (proj1 (Forall_forall _ _) QB qb Hqb) as (_ & _ & _ & _ & _ & _ & B6 & _).
          destruct (In_nth_error _ _ Hit) as [k Hk]. destruct (B6 k _ Hk) as [_ IT]. destruct IT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & JS & _). cbn [fst snd] in JS.
          destruct (is_primary n) eqn:EPn; [discriminate Hp|]. destruct (JS eq_refl) as (ch & Hch & X & _). exists ch. exact (conj Hch X). }
      destruct OLDU as (ch & Hch & Eu). pose proof (SX ch Hch) as Y. unfold sepZ in Y. cbn [fst snd] in Y.
      destruct (In_nth_error _ _ Hch) as [i Hi]. destruct HSR as (S1 & _). destruct (S1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & _).
      unfold PG in Eu, D8. clear -Y Eu D8 D9 SMB. lia. }
    rewrite length_app. cbn [length].
    assert (ELL : large_live (secA A ua nv) = large_live A + 1).
    { rewrite (large_live_insert A (secA A ua nv) [] (aa_live A) (ua + 6144) nv eq_refl eq_refl).
      destruct (Z.leb_spec 64513 nv) as [_|X]; [reflexivity | exfalso; clear -X Hnv; lia]. }
    split; [rewrite ELL; change (qlarge (secA A ua nv)) with (qlarge A); clear -CNT3; lia|].
    split; [|exact QCI3].

    rewrite (small_live_insert A (secA A ua nv) [] (aa_live A) (ua + 6144) nv eq_refl eq_refl).
    destruct (Z.leb_spec 64513 nv) as [_|X]; [clear -SML3; lia | exfalso; clear -X Hnv; lia]. }
  idtac "sr:11".

  unfold AInvA. change (aa_geom (secA A ua nv)) with G. fold v3.
  split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|]. split.
  { unfold rest_inv. fold m3. change (aa_geom (secA A ua nv)) with G.
    split; [exact HLS|]. split; [exact HLB|]. split; [exact HPR'|]. split; [exact HSR'|]. split; [exact HQR'|].
    split; [exact HDEP|]. split; [exact HIA'|]. split; [exact HTH' | exact HMI']. }
  split; [exact HMD|]. split; [exact HI3'|].
  eapply bandtp_mono_rm; [|exact HB]. exact DEFB.
Qed.

Section Kept.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0S12VCST;R1A2S12S5dR2A2SeF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S0S12VCST;R1A2S12S5bR2A2SeF_;F_;Fa;").

Theorem sec_kept : ltac2:(tb__ "0|7|
S20S3aS3aS4aS40Q40M0A1A1S58S0S0S0S43S53R8R7R5R4A5SaS1Zfc01R4A2S3R4S6Z2M1Z27A2A2A2S1eRaA1S27S56R6A1S0S9S4eS1dS1fRcA1A2A1S0S2S23R3A1S8Z8M2R1A2A2S0S5aReR8R3RaA4S1G2R8A2S1S2S8G2R4A2R9A2S22R10A1A2S0SaS1Z0R1A2S3R1S6G1Z40A2A2A2ScS5fR9R2A2A1ScS3cRaReR9R7RdR3A6A1ScS12S5bR4A2A1SbS4bS40Q8A1M3A1M4S39R14S3fG0R5A2M5A2S39R15G5A2A3F_;F_;F_;F_;Fa;S0SaS1S18R1A2S3R1S17A2A2ScSbG4S39R13S3fG0R2A2A2S4cG3A1M6A3A1ScSbG4S39R13S3fG0R3A2A2G6A3A1F_;F_;Fa;S5cVCST;VXGL;R13S3dR13RdReA3S39R12A1S39R11A1A6F_;F_;F_;F_;F_;Tpw;Tidx;TL;TG;F_;F_;Fblk;Fua;Fnv;Fmd;Ftp;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp md nv ua blk HA Hnv. cbn zeta. intros HPD Hblk HROOM RMO DEFB.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  set (G := aa_geom A) in *. set (T := ag_thread G) in *. set (L := secmapsize nv) in *. set (idx := Z.of_nat (length (aa_sec A))) in *. set (pw := ag_pab G + 8 * idx) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.
  pose proof (geom_bands _ HG) as (FB & TB & CB & DB & TI & CI & DI). fold G T in TB, TI. fold G in FB, CB, DB, CI, DI.
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in FB, TB, CB, DB, TI, CI, DI. rewrite FS_total_val in FB.
  destruct HPD as (PM & PAL & PL0 & PDI & ST & SC & SD & SF & SS & SP & SX & SDB). fold G L in PM, PL0, PDI, ST, SC, SD, SF, SS, SP, SX, SDB. fold T in ST.
  pose proof (secmapsize_bounds nv ltac:(clear -Hnv; lia)) as [SMB SMM]. fold L in SMB, SMM. unfold PG in SMM, PAL.
  pose proof (dyn_in_big _ _ _ PDI ltac:(clear -SMB; lia)) as UI. destruct PDI as (_ & _ & PDT & _ & PDB).
  pose proof (pab_facts _ A HSR) as (P1 & P2 & P3 & P4 & P5). fold G in P1, P2, P3. fold idx in P4.
  assert (U8 : ua mod 8 = 0).
  { pose proof (Z.div_mod ua 4096 ltac:(clear; lia)) as X. rewrite PAL, Z.add_0_r in X. rewrite X. replace (4096 * (ua / 4096)) with ((512 * (ua / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (L8 : L mod 8 = 0).
  { pose proof (Z.div_mod L 4096 ltac:(clear; lia)) as X. rewrite SMM, Z.add_0_r in X. rewrite X. replace (4096 * (L / 4096)) with ((512 * (L / 4096)) * 8) by (clear; lia). apply Z_mod_mult. }
  assert (UT : ua + L <= 140737479966720) by (clear -PDT ACV; lia).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in PDB, DEFB.
  pose proof (live_foot_new ua L U8 L8 PL0 UI UT ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; exact PDB) A _ HG Hsep HI3 HPR HSR SS SX) as LFN.
  assert (PWZ : forall z, pw <= z < pw + blk -> ag_pab G <= z < ag_pab G + kPtrArrayReserve).
  { intros z Hz. unfold pw in Hz. pose proof (Zle_0_nat (length (aa_sec A))) as NN. fold idx in NN. clear -Hz HROOM P4 NN. lia. }
  unfold sepZ in SF, ST. cbn [fst snd] in SF, ST. rewrite FS_total_val in SF.

  assert (NOC : forall a, client_addrA CST A a -> ~ errno_addrA a ->
                  ~ chg_s G ua L pw blk a /\ ~ in_rangesZ IMG_S a /\ ~ (ua <= a < ua + L)).
  { intros a Hcl NE.
    pose proof (client_not_rt CST HCST A a _ HG HF Hsep Hcl) as NR. unfold rt_zone in NR. fold G T in NR.
    assert (IMGS : forall x, in_rangesZ IMG_S x -> 0x10000 <= x < IMG_HI).
    { intros x (b & n & Hbn & Hx). unfold IMG_S in Hbn. unfold SEC_INST, IMG_HI in *. cbn [In] in Hbn.
      destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hx; lia. }
    destruct (client_addr_cases CST A a _ HF Hcl) as [S|[Lv|[FR|[C|FL]]]].
    - fold G in S. split; [|split; [intros X; pose proof (IMGS a X) as Y; unfold IMG_HI in Y; clear -S Y ACV; lia | clear -S PDT; lia]].
      intros [X|[X|[[X|X]|X]]].
      + unfold zimg, SEC_INST, ERRNO_A in X. clear -X S ACV. lia.
      + clear -X S G5. lia.
      + clear -X S PDT. lia.
      + unfold Sh, SHADOW_OFF in X. pose proof (Z.div_le_mono (ua + L) 140737479966720 8 ltac:(clear; lia) UT) as D.
        pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. pose proof (Z.div_mod ua 8 ltac:(clear; lia)) as DU. rewrite U8, Z.add_0_r in DU.
        replace (ua + L) with ((ua / 8 + L / 8) * 8) in D by (clear -DL DU; lia). rewrite Z.div_mul in D by (clear; lia). cbn in D. clear -X D S ACV. lia.
      + pose proof (PWZ a X) as Y. clear -Y S P2. lia.
    - destruct Lv as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & _). unfold IMG_HI in S2.
      pose proof (rz_bound n) as RZ.
      pose proof (LFN b n a Hbn ltac:(left; clear -Hx RZ; lia)) as NZ.
      pose proof (live_foot _ A HG Hsep HI3 HPR HSR b n a Hbn ltac:(left; clear -Hx RZ; lia)) as (X1 & X2 & _).
      pose proof (live_foot_pab _ A HG Hsep HI3 HPR HSR b n a Hbn ltac:(left; clear -Hx RZ; lia)) as X3. fold G T in X2, X3.
      split; [|split; [intros X; pose proof (IMGS a X) as Y; clear -X1 Y; lia | intros X; apply NZ; left; exact X]].
      intros [X|[X|[X|X]]]; [unfold zimg, SEC_INST, ERRNO_A, IMG_HI in *; clear -X X1; lia | clear -X X2; lia | exact (NZ X) | exact (X3 (PWZ a X))].
    - destruct FR as (c & p & Hcp & Hp & _ & Hx). pose proof (fs_geom_nums G c p HG Hcp Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in M. fold G in Hx.
      destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      split; [|split; [intros X; pose proof (IMGS a X) as Y; unfold IMG_HI in Y; clear -Hx M Y; lia | clear -Hx M SF; lia]].
      intros [X|[X|[[X|X]|X]]].
      + unfold zimg, SEC_INST, ERRNO_A in X. clear -X Hx M. lia.
      + clear -X Hx M G10. lia.
      + clear -X Hx M SF. lia.
      + pose proof (sh_run_band2 ua (ua + L) a ltac:(unfold IMG_HI in UI; clear -UI; lia) ltac:(clear -UT PL0; lia)) as BY.
        assert (E : Sh (ua + L) = Sh ua + L / 8).
        { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }
        rewrite E in BY. specialize (BY X). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. clear -BY Hx M FB. lia.
      + pose proof (PWZ a X) as Y. clear -Y Hx M PF. lia.
    - destruct (HCST _ C) as [X0 _]. unfold IMG_LO, IMG_HI in X0.
      split; [|split; [exact (HCSTS a C) | unfold IMG_HI in UI; clear -X0 UI; lia]].
      intros [X|[X|[[X|X]|X]]].
      + apply (HCSTS a C). unfold IMG_S, in_rangesZ. unfold zimg, SEC_INST, ERRNO_A in *.
        destruct X as [Hz|[Hz|[Hz|Hz]]].
        * exists 0xeaa98, (0xead04 - 0xeaa98). split; [left; reflexivity | clear -Hz; lia].
        * exists 0xead08, (0xead30 - 0xead08). split; [right; left; reflexivity | clear -Hz; lia].
        * exists 0x170320, 2. split; [right; right; right; left; reflexivity | clear -Hz; lia].
        * exfalso. apply NE. unfold errno_addrA, ERRNO_A. clear -Hz. lia.
      + apply NR. right. left. clear -X. lia.
      + unfold IMG_HI in UI. clear -X X0 UI. lia.
      + unfold Sh, SHADOW_OFF in X. pose proof (Z.div_pos ua 8 ltac:(unfold IMG_HI in UI; clear -UI; lia) ltac:(clear; lia)) as D. clear -X X0 D. lia.
      + pose proof (PWZ a X) as Y. unfold IMG_HI in P1. clear -Y X0 P1. lia.
    - destruct FL as (c & p & Hcp & Hp & _ & Ea). pose proof (fs_geom_nums G c p HG Hcp Hp) as M. cbn zeta in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. fold G in Ea. unfold fs_flags in M, Ea. rewrite FS_kFlagsOffset_val in M, Ea. unfold IMG_HI in M.
      destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _). fold G in PF. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      split; [|split; [intros X; pose proof (IMGS _ X) as Y; unfold IMG_HI in Y; clear -M Ea Y; lia | clear -M Ea SF; lia]].
      intros [X|[X|[[X|X]|X]]].
      + unfold zimg, SEC_INST, ERRNO_A in X. clear -X M Ea. lia.
      + clear -X M Ea G10. lia.
      + clear -X M Ea SF. lia.
      + pose proof (sh_run_band2 ua (ua + L) a ltac:(unfold IMG_HI in UI; clear -UI; lia) ltac:(clear -UT PL0; lia)) as BY.
        assert (E : Sh (ua + L) = Sh ua + L / 8).
        { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }
        rewrite E in BY. specialize (BY X). unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BY. clear -BY M Ea FB. lia.
      + pose proof (PWZ _ X) as Y. clear -Y M Ea PF. lia. }
  idtac "sk:1".
  assert (ESHL : Sh (ua + L) = Sh ua + L / 8).
  { unfold Sh. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL. rewrite DL at 1. rewrite Z.mul_comm, Z.div_add by (clear; lia). clear. lia. }

  assert (NOS : forall a, client_shadowA CST XGL A a ->
                  SHADOW_OFF <= a < HIGH_SHADOW_END /\ ~ chg_s G ua L pw blk a).
  { intros a C1. pose proof (client_shadow_bounds CST XGL HCST HXGL A a _ HG HF Hsep C1) as B0. split; [exact B0|].
    unfold SHADOW_OFF, HIGH_SHADOW_END in B0.
    intros [X|[X|[[X|X]|X]]].
    - unfold zimg, SEC_INST, ERRNO_A in X. clear -X B0. lia.
    - clear -X B0 TB G4. lia.
    - clear -X B0 PDB. lia.
    -
      assert (XIN : forall x, a = Sh x -> 0 <= x -> ua <= x < ua + L).
      { intros x -> Hx0. unfold Sh in X. pose proof (Z.div_mod L 8 ltac:(clear; lia)) as DL. rewrite L8, Z.add_0_r in DL.
        pose proof (Z.div_mod ua 8 ltac:(clear; lia)) as DU. rewrite U8, Z.add_0_r in DU.
        pose proof (Z.div_mod x 8 ltac:(clear; lia)) as DX. pose proof (Z.mod_pos_bound x 8 ltac:(clear; lia)) as MX. clear -X DL DU DX MX. lia. }
      destruct C1 as [(y & Cy & Ey)|(y & Gy & Ey)].
      + destruct (client_addr_bounds CST HCST A y _ HG HF Hsep Cy) as [By _]. pose proof (XIN y Ey ltac:(clear -By; lia)) as YIN.
        assert (NEy : ~ errno_addrA y) by (unfold errno_addrA, ERRNO_A; unfold IMG_HI in UI; clear -YIN UI; lia).
        exact (proj2 (proj2 (NOC y Cy NEy)) YIN).
      + destruct (HXGL y Gy) as [Y1 Y2]. pose proof (XIN y Ey ltac:(clear -Y1; unfold IMG_LO in *; lia)) as YIN. clear -YIN Y2 UI. lia.
    - pose proof (PWZ a X) as Y. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, kPtrArrayReserve in *. clear -Y B0 P3. lia. }
  idtac "sk:2".
  split.
  - intros a Ba Hcl. destruct Hcl as [(C1 & _ & NE)|(C1 & _ & _)].
    + destruct (NOC a C1 NE) as (N1 & N2 & _).
      apply RMO; [exact Ba | exact (client_not_rtM CST HCST HCSTM A a _ HG HF Hsep C1) | exact N1 | exact N2].
    + destruct (NOS a C1) as (B0 & N1). unfold SHADOW_OFF, HIGH_SHADOW_END in B0.
      apply RMO; [exact Ba | | exact N1 |].
      * unfold rt_zoneM, rt_zone, IMG_HI. intros [[R1|[R1|[R1|[R1|R1]]]]|R1].
        -- destruct R1 as [R1 _]. clear -R1 B0. lia.
        -- fold G T in R1. clear -R1 B0 TB. lia.
        -- fold G in R1. clear -R1 B0 CB. lia.
        -- fold G in R1. clear -R1 B0 DB. lia.
        -- fold G in R1. clear -R1 B0 FB. lia.
        -- pose proof (IMG_M_range a R1) as IR. unfold IMG_HI in *. clear -IR B0. lia.
      * intros (b & n & Hbn & Hx). unfold IMG_S in Hbn. unfold SEC_INST in *. cbn [In] in Hbn.
        destruct Hbn as [E|[E|[E|[E|[]]]]]; injection E; intros; subst; clear -Hx B0; lia.
  - intros x j Hx Hj Hdef.
    assert (Bx : SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
    { destruct Hx as [[C1 C2]|GX].
      - destruct (client_addr_bounds CST HCST A x _ HG HF Hsep C1) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. clear -B. lia.
      - destruct (HXGL x GX) as [X0 X1]. unfold IMG_LO, IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. clear -X0 X1. lia. }
    unfold SHADOW_OFF, HIGH_SHADOW_END in Bx.
    destruct (word_byte_range (Sh x) j ltac:(clear -Bx; lia) Hj) as (W1 & W2 & W3).
    unfold word_byte in *. apply DEFB; [|exact Hdef]. clear -W3 Bx Hj. lia.
Qed.
End Kept.
End RebuildS.

(* [comment removed for export] *)
Module SpineMallocSecI.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI"; "W0"; "st0"; "@Corelib.Init.Logic"; "eq"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "sstate"; "ss_next"; "reg_sv"; "valuation"; "SVar"; "swf"; "sprop_below"; "ss_facts"; "ss_objs"; "ss_pc"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "bool"; "prod"; "true"; "app"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "CS1"; "ES1"; "ES1f"; "SS0"; "ESn"; "SSa_S"; "SSb_S"; "V_MS"; "ES1g"; "F_sgen"; "RT_sec"; "V_NS"; "nxS"; "@Corelib.Init.Specif"; "sig"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN"; "stRn_S"; "s_n"; "stKn"; "R_n"; "stRn"; "N_secn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "E_s1"; "RT_m1"; "F_fam"; "F_s1"; "neededx"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "KcA"; "Kc_ok"; "L_malloc_null"; "A_globals"; "JL_malloc_null"; "Posts_malloc"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "vm_reserved"; "with_vmmaps"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "a1x"; "@Stdlib.Lists.List"; "forallb"; "incl"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2.
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
S2S19S32S35Ufa0S16S2eZ706a0S17S2eA1A3S34S16S4S23S0S1Z2M0A3S17S4A1M1A3S16S4S21S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 2) memo_3. memo_rw (ES1 W0 st0 2) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
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
S2S19S32S35Ufa0S16S2eZ5e52cS17S2eA1A3S34S16S4S22S0S1Z2M0A3S17S4A1M1A3S16S4S24S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 2) memo_6. memo_rw (ESn W0 st0 2) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RN_0 : ltac2:(tb__ "0|0|
S2S18SaA1S3bS0S1Z2A3S1cSaS49S3fS77SaS76S3dA4A3A3"). Proof. memo_rw (R_n W0 st0 2) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WRn_0 : ltac2:(tb__ "0|0|
S2S19S11S38S0S1Z2A3A1S1bA3"). Proof. memo_rw (stRn_S W0 st0 2) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DKRn_0 : ltac2:(tb__ "0|5|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S41S5S3aS0S1Z2M4A3A1S38S0S1G4A3A2S1eG3S1dG1G2S16G0S1dS8S8SbS78A1S10P18A1A4S17G0A1A3S17S9A1A4A2A3"). Proof. memo_rw (stKn W0 st0 2) memo_10. memo_rw (stRn_S W0 st0 2) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXRn_0 : ltac2:(tb__ "0|1|
S2S2fSdS38S0S1Z2M0A3A1SdS5S3aS0S1G0A3A1A1A3"). Proof. memo_rw (stRn_S W0 st0 2) memo_9. memo_rw (stKn W0 st0 2) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTn_0 : ltac2:(tb__ "0|1|
S2S19S7S3cS0S1Z2M0A3S51S4eS0S1A3S39S0S1G0A3A3S1bA3"). Proof. memo_rw (stRn W0 st0 2) memo_11. memo_rw (s_n W0 st0 2) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IDn_0 : ltac2:(tb__ "0|0|
S2S19S43S39S0S1Z2A3S40A2S1bA3"). Proof. memo_rw (s_n W0 st0 2) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma NXS0_0 : ltac2:(tb__ "0|0|
S6dS34SdS5S23S0S1Z2A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (SS0 W0 st0 2) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertS1_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ706a0S17S2eA1A3S34S16S30S31S23S0S1Z2M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S21S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 2) memo_3. memo_rw (ES1 W0 st0 2) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXS1f_0 : ltac2:(tb__ "0|0|
S6dS34SdS5S22S0S1Z2A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (ES1f W0 st0 2) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertSf_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ5e52cS17S2eA1A3S34S16S30S31S22S0S1Z2M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S24S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 2) memo_6. memo_rw (ESn W0 st0 2) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

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
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecIW2"; "W0"; "st0"; "@Corelib.Init.Logic"; "eq"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "sstate"; "ss_next"; "reg_sv"; "valuation"; "SVar"; "swf"; "sprop_below"; "ss_facts"; "ss_objs"; "ss_pc"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "bool"; "prod"; "true"; "app"; "pair"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "CS1"; "ES1"; "ES1f"; "SS0"; "ESn"; "SSa_S"; "SSb_S"; "V_MS"; "ES1g"; "F_sgen"; "RT_sec"; "V_NS"; "nxS"; "@Corelib.Init.Specif"; "sig"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN"; "stRn_S"; "s_n"; "stKn"; "R_n"; "stRn"; "N_secn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "E_s1"; "RT_m1"; "F_fam"; "F_s1"; "neededx"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "KcA"; "Kc_ok"; "L_malloc_null"; "A_globals"; "JL_malloc_null"; "Posts_malloc"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "event"; "vm_reserved"; "with_vmmaps"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "assn"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok"; "mmap_rw_vm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "a1x"; "@Stdlib.Lists.List"; "forallb"; "incl"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2.
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
S2S19S32S35Ufa0S16S2eZ706a0S17S2eA1A3S34S16S4S23S0S1Z4M0A3S17S4A1M1A3S16S4S21S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 4) memo_3. memo_rw (ES1 W0 st0 4) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
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
S2S19S32S35Ufa0S16S2eZ5e52cS17S2eA1A3S34S16S4S22S0S1Z4M0A3S17S4A1M1A3S16S4S24S0S1G0A3G1A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 4) memo_6. memo_rw (ESn W0 st0 4) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma RN_0 : ltac2:(tb__ "0|0|
S2S18SaA1S3bS0S1Z4A3S1cSaS49S3fS77SaS76S3dA4A3A3"). Proof. memo_rw (R_n W0 st0 4) memo_8. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma WRn_0 : ltac2:(tb__ "0|0|
S2S19S11S38S0S1Z4A3A1S1bA3"). Proof. memo_rw (stRn_S W0 st0 4) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DKRn_0 : ltac2:(tb__ "0|5|
S2S1fS1aS18S1aS8S8A2M0A1M1S18S9A1M2A2M3A1S41S5S3aS0S1Z4M4A3A1S38S0S1G4A3A2S1eG3S1dG1G2S16G0S1dS8S8SbS78A1S10P18A1A4S17G0A1A3S17S9A1A4A2A3"). Proof. memo_rw (stKn W0 st0 4) memo_10. memo_rw (stRn_S W0 st0 4) memo_9. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXRn_0 : ltac2:(tb__ "0|1|
S2S2fSdS38S0S1Z4M0A3A1SdS5S3aS0S1G0A3A1A1A3"). Proof. memo_rw (stRn_S W0 st0 4) memo_9. memo_rw (stKn W0 st0 4) memo_10. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ENTn_0 : ltac2:(tb__ "0|1|
S2S19S7S3cS0S1Z4M0A3S51S4eS0S1A3S39S0S1G0A3A3S1bA3"). Proof. memo_rw (stRn W0 st0 4) memo_11. memo_rw (s_n W0 st0 4) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma IDn_0 : ltac2:(tb__ "0|0|
S2S19S43S39S0S1Z4A3S40A2S1bA3"). Proof. memo_rw (s_n W0 st0 4) memo_12. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma NXS0_0 : ltac2:(tb__ "0|0|
S6dS34SdS5S23S0S1Z4A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (SS0 W0 st0 4) memo_3. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertS1_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ706a0S17S2eA1A3S34S16S30S31S23S0S1Z4M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S21S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (SS0 W0 st0 4) memo_3. memo_rw (ES1 W0 st0 4) memo_4. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXS1f_0 : ltac2:(tb__ "0|0|
S6dS34SdS5S22S0S1Z4A3A1A1A2"). Proof. apply Pos.leb_le. memo_rw (ES1f W0 st0 4) memo_6. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ECertSf_0 : ltac2:(tb__ "0|4|
S2S19S33S35Ufa0S16S2eZ5e52cS17S2eA1A3S34S16S30S31S22S0S1Z4M0A3Z1SbZ0M1A1M2A3S17S30A1M3A3S16S30S31S24S0S1G0A3G1G2A3G3A3A6S1bA3"). Proof. memo_rw (ES1f W0 st0 4) memo_6. memo_rw (ESn W0 st0 4) memo_7. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

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

(* [comment removed for export] *)
Module F0A_dzone.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "leb"; "sub"; "modulo"; "pow"; "mul"; "opp"; "div"; "@Corelib.Init.Datatypes"; "bool"; "false"; "prod"; "andb"; "true"; "list"; "orb"; "pair"; "fst"; "nat"; "nil"; "snd"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "obj_range"; "sobj"; "valuation"; "ob_base"; "ob_hi"; "ob_lo"; "rm"; "rw"; "sv_below"; "sv_eqb"; "agree_below"; "holds"; "sprop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "qbatch"; "sec_chunk"; "AA"; "aa_live"; "aa_sec"; "ag_thread"; "aa_q_thread"; "ageom"; "DG"; "aa_depot"; "ag_ctx"; "ag_spacebeg"; "sc_map_beg"; "sc_map_size"; "topG"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone"; "same_rng"; "zoneF"; "rng_below"; "img_okD"; "rd_okb"; "winpb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "QG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst"; "NFS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "hw_of"; "j_min"; "j_qb"; "j_qf"; "j_st"; "rhoF_of"; "ZD_NRT"; "ZD_NV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "O_blkN"; "O_sh"; "qvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "IMG_LO"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Sh"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "free_depth"; "V_DEPTH"; "chain_pre"; "unwind_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "DFP"; "MAP1"; "MAP1N"; "STORE"; "DFPw"; "dfp_static"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "bv_signed"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "blk_geo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD"; "AInvX"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundA SymSoundM SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface SegQ_defs Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.InvKf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.LiveGeom.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition zoneF (A : AA) (a : Z) : Prop := ltac2:(tb__ "0|5|
S32VA;A1S3aS5S3S3S8S5fVa;A2S9Va;S5eA2A2S5S9Va;S6cA2S8SaS6aSfZ8S6bA2A2Va;A2A2A2S5S3S8S38R1A1M0Va;A2S9Va;SaG0Z1000M1A2A2A2S5S3S8S3dR1A1M2Va;A2S9Va;SaG2G1A2A2A2S5S3S8S3eR1A1M3Va;A2S9Va;SaG3S63A2A2A2S5S6S34S34S3S42S34R1S37VA;A1A3S3S8S3fR1A1M4Va;A2S9Va;SaG4S40R1A1A2A2A2A2Lch;A2S5S3S8S61Va;A2S9Va;S60A2A2S8S41R1A1Va;A2A2A2A2A2A2A2TG;").

Lemma DFP_splitF : ltac2:(tb__ "0|0|
S3bS0S69R2R1A2S5S6eR2A1S6dR3R2A2A2F_;Fa;FG;").
Proof. intros G a [H|[H|H]]; [left; exact H | right; right; left; exact H | right; right; right; exact H]. Qed.

Lemma zoneF_not_DFP : ltac2:(tb__ "0|0|
S35S35S25S17S6fQ40A1A1S50S0S77R5R4R3R2A4S4S3aS32R6A1S32R7A1A3S4S17S34A1S37R7A1S37R8A1A3S46R9R4A2S7S69S3cR9A1R5A2A1F_;F_;F_;F_;Fa;Fmd;Ftp;Frho;FAx;FA;").
Proof.
  intros A Ax rho tp md a HX EG ES HZ HD. unfold zoneF in HZ. cbn zeta in HZ. rewrite <- EG, <- ES in HZ.
  pose proof HX as (HG & HR & HF & HRest & HM & HI3 & HB). destruct HRest as (Hsep & Hlive & HP & HS & _).
  assert (HSEC : forall i ch, nth_error (aa_sec Ax) i = Some ch -> dyn_in (topG (aa_geom Ax)) (sc_map_beg ch) (sc_map_size ch)).
  { intros i ch Hi. destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). exact D10. }
  assert (HPAB : dyn_ok (topG (aa_geom Ax)) (ag_pab (aa_geom Ax)) kPtrArrayReserve) by (destruct HS as (_ & _ & _ & _ & X4 & _); exact X4).
  pose proof (zones_not_DFPw Ax a HG HI3 HSEC HPAB) as ZN. cbn zeta in ZN.
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & T1 & T2 & _ & C1 & C2 & D1 & D2 & S1 & S2 & _ & TG). unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2, HZ.
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & _). unfold IMG_LO, IMG_HI in TI, CI.
  assert (GOAL : forall (P : Prop), (P -> ~ DFPw (aa_depot Ax) a) -> P -> ~ dfp_static a -> False).
  { intros P XP Xp Xns. destruct (DFP_splitF _ _ HD) as [Hs|Hw]; [exact (Xns Hs) | exact (XP Xp Hw)]. }
  assert (NS : forall lo hi, lo <= a < hi -> (hi <= STORE \/ MAP1 + 8 * MAP1N <= lo) -> ~ dfp_static a).
  { intros lo hi X1 X2 Hs. pose proof (dstat_range a Hs). lia. }
  destruct HZ as [[Z1 Z2]|[ZT|[ZC|[ZA|[ZM|[ZS|ZK]]]]]].
  - apply (GOAL (IMG_LO <= a < IMG_HI /\ ~ dstatw a)); [intros H; apply ZN; left; exact H | |].
    + split; [exact Z1|]. intros [Hs _]. pose proof (dstat_range a Hs). lia.
    + intros Hs. pose proof (dstat_range a Hs). lia.
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_introl H)))) ZT). eapply NS; [exact ZT | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL _ (fun H => ZN (or_intror (or_intror (or_intror (or_introl H))))) ZC). eapply NS; [exact ZC | unfold STORE, MAP1, MAP1N; lia].
  - apply (GOAL (ag_spacebeg (aa_geom Ax) <= a < ag_spacebeg (aa_geom Ax) + kSpaceSize + 4096)); [intros H; apply ZN; right; left; exact H | rewrite kSpaceSize_val; lia |].
    apply (NS (ag_spacebeg (aa_geom Ax)) (a + 1)); [lia | unfold MAP1, MAP1N; lia].
  - destruct ZM as (ch & Hch & Hz).
    apply (GOAL (exists ch, In ch (aa_sec Ax) /\ sc_map_beg ch <= a < sc_map_beg ch + sc_map_size ch)).
    + intros H. apply ZN. do 7 right. left. exact H.
    + exists ch. exact (conj Hch Hz).
    + destruct (In_nth_error _ _ Hch) as (i & Hi). destruct HS as [X1 _]. destruct (X1 i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & D8 & D9 & D10 & _).
      pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; lia)) as CB. eapply NS; [exact Hz | unfold IMG_HI in CB; unfold MAP1, MAP1N; lia].
  - apply (GOAL (SHADOW_BAND_LO <= a < SHADOW_BAND_HI)); [intros H; apply ZN; do 8 right; left; exact H | exact ZS |].
    apply (NS SHADOW_BAND_LO (a + 1)); [lia | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, MAP1, MAP1N; lia].
  - apply (GOAL (topG (aa_geom Ax) <= a)); [intros H; apply ZN; do 9 right; exact H | exact ZK |].
    apply (NS (topG (aa_geom Ax)) (a + 1)); [lia | unfold MAP1, MAP1N; lia].
Qed.

Lemma chunk_zoneF : ltac2:(tb__ "0|0|
S35S25S17S6fQ40A1A1S50S0S0S0S4eS30R7R6R5R4A5S42S14S0S0A2S19S0S0R4R3A4S36R8A1A3S3S8ScR5Z10A2R3A2S9R3SaR5S4bR4A1A2A2A2S46RaR4A2F_;F_;F_;Fa;Fn;Fp;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md p n a HA HL Ha. unfold zoneF. cbn zeta.
  destruct (is_primary n) eqn:EP.
  - pose proof (live_slot A rho tp md p n HA HL EP) as LS. cbn zeta in LS. destruct LS as (C1 & O1 & _ & _ & L1 & L2 & _).
    pose proof (live_prim_facts segsA A rho tp md p n HA HL EP) as LP. cbn zeta in LP. destruct LP as (_ & _ & X0 & _ & X1 & _).
    unfold region_beg, kUserSpaceSize, kFreeArraySize in *. unfold kRegionSize in *. rewrite kSpaceSize_val. change (2 ^ 32) with 4294967296 in *. do 3 right. left.
    set (c := ClassID (needed n)) in *. set (SB := ag_spacebeg (aa_geom A)) in *. clearbody c SB. clear -C1 O1 L1 L2 X0 X1 Ha. lia.
  - destruct (live_sec A rho tp md p n HA HL EP) as (ch & Hch & M1 & M2 & _).
    do 4 right. left. exists ch. split; [exact Hch | lia].
Qed.

Definition img_okD (d : zdesc) : bool := ltac2:(tb__ "0|1|
S14S14S1bS0A2M0S0A2S12Ld;Vd;G0S0G0S12Lp;R2S1bS0S12S12L_;S78R2U0A2S15S15SbS5fR1A2SbR3S5eA2A2S18SbR3S6cA2SbSaS6aSfZ8S6bA2A2R1A2A2A2S16X12x2Llo;Lz;X14x1Lhi;Lp;X14x1").
Lemma ZD_chkD : ltac2:(tb__ "0|0|
S5dS4S12S44S51S48S1eS51S59S5aR1A1A3A3S16A3Fq;").
Proof. intros [| |]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section NFSZ.
Variables (A : AA) (rho : valuation) (tp : list word) (md : Model) (p n : Z).
Hypothesis HA : ltac2:(tb__ "0|0|
S4eS30VA;Vrho;Vtp;Vmd;A5").
Hypothesis HL : ltac2:(tb__ "0|0|
S42S14S0S0A2S19S0S0Vp;Vn;A4S36VA;A1A3").
Hypothesis HHI : blk_cls p n.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S4S0S70Q40S2aVrho;PcA2A2Vp;A3").
Variables (t : Z) (jv : junkF).
Hypothesis Ht : ltac2:(tb__ "0|2|
S3S3S8Z0Vt;A2S9Vt;Z100A2A2S3S4S0SdVt;Z4A2Z1A3S3S1fS21S30S29Vrho;A1A2M0S20ScVp;Z10A2U4M1S53Vt;Vn;A2A3A2S1fG0S20ScVp;ZcA2G1SdVn;SeZ2Z20A2A2A3A2A2A2A2").
Hypothesis Hjv : ltac2:(tb__ "0|9|
S3S3S8Z0M0S54Vjv;A1M1A2S9G1SeZ2Z40A2M2A2A2S3S3S8G0S57Vjv;A1M3A2S9G3G2A2A2S3S3S8G0S56Vjv;A1M4A2S9G4G2A2A2S3S3S8G0S55Vjv;A1M5A2S9G5G2A2A2S3S1fS21S30S29Vrho;A1A2M6S20SaS4fZ48A2U8M7G1A3A2S3S1fG6S20SaS38S32VA;A1A1M8Zae0A2G7G3A3A2S4S17S33A1S39VA;A1S1cS33A1A3S3S1fG6S20SaG8Z58A2G7G4A3A2S1fG6S20SaG8Z60A2G7G5A3A2A2F_;A2A2A2A2A2A2").
Variable q : qvar.
Hypothesis QC : qcond q A.

Theorem nfs_zoneF : ltac2:(tb__ "0|1|
S4cS42S4cR1S52Vq;A1A3S0S3S8S1aS0S0S23S58VA;Vrho;Vp;Vn;Vt;Vjv;A6S4dR3A1A2M0A3R1A2S9R1S1dS0S0G0A3A2A2S46VA;R2A2F_;Fa;F_;Fk;").
Proof.
  intros k Hk a Ha. unfold zoneF. cbn zeta.
  pose proof (inz_NFS A rho tp md p n HA HL HHI Hp12 t Ht jv Hjv q QC) as F2.
  destruct (Forall2_In_l _ _ _ (carve_obj k) F2 (in_map carve_obj _ _ Hk)) as (d & Hd & IZ).
  pose proof (proj1 (forallb_forall _ _) (ZD_chkD q) d Hd) as OKd.
  destruct d as [ [z lo] hi]. unfold in_zone in IZ. destruct IZ as (HU & L1 & L2 & R). destruct R as [R|[R1 R2]]; [lia|].
  assert (Z5 : (z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5)%nat).
  { clear -HU. destruct q; cbn [ZU In] in HU; lia. }
  destruct Z5 as [-> | [-> | [-> | [-> | [-> | ->] ] ] ] ]; cbn [zloF zhiF] in L1, L2; cbn beta iota in R1, R2.
  -   unfold img_okD in OKd. cbn [Nat.eqb] in OKd. apply andb_prop in OKd as [OK1 OK3]. apply andb_prop in OK1 as [OK1 OK2].
    apply Z.leb_le in OK1, OK2. left. split; [lia|]. apply Bool.orb_prop in OK3 as [OK3|OK3]; apply Z.leb_le in OK3; lia.
  - right. left. lia.
  - right. right. left. lia.
  - apply (chunk_zoneF A rho tp md p n a HA HL : (fun P => P) _). pose proof (N8_facts n) as NF. destruct (blkF_geom A rho tp md p n HA HL HHI) as (_ & _ & N1 & _). specialize (NF N1). lia.
  -
    assert (QNE : aa_q_thread A <> []) by (clear -QC HU; destruct q; cbn [ZU In] in HU; [exact (proj1 QC) | exfalso; lia | exact (proj1 QC)]).
    pose proof (qF A rho tp md p n HA HL) as QF. cbn zeta in QF. destruct QF as (_ & _ & _ & _ & _ & QF). specialize (QF QNE).
    destruct QF as (_ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). unfold kQuarantineBatchSize in S2. unfold lastq in R1, R2.
    do 3 right. left. lia.
  -
    assert (CI : aa_cache_inited A = true /\ cache24 A <> []) by (clear -QC HU; destruct q; cbn [ZU In] in HU; [exfalso; lia | exact (proj2 QC) | exact (proj2 (proj2 QC))]).
    pose proof (cF A rho tp md p n HA HL (proj1 CI) (proj2 CI)) as CF. cbn zeta in CF. destruct CF as (_ & _ & _ & _ & _ & X & _).
    rewrite kSpaceSize_val. change (2 ^ 32) with 4294967296 in *. change (2 ^ 28) with 268435456 in X. do 3 right. left. lia.
Qed.
End NFSZ.

Definition same_rng (o o' : sobj) : bool := ltac2:(tb__ "0|0|
S15S15S2cS26Vo;A1S26Vo';A1A2S2cS28Vo;A1S28Vo';A1A2A2S2cS27Vo;A1S27Vo';A1A2A2").
Lemma same_rng_range : ltac2:(tb__ "0|0|
S25S24S24S4S12S45R2R1A2S16A3S4S14S0S0A2S23R4R3A2S23R4R2A2A3F_;Fo';Fo;Frho;").
Proof.
  intros rho o o' H. unfold same_rng in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1, H2, H3. unfold obj_range, obj_lo_of, obj_hi_of. rewrite H1, H2, H3. reflexivity.
Qed.
Definition rng_below (k : positive) (o : sobj) : bool := ltac2:(tb__ "0|0|
S15S15S2bVk;S26Vo;A1A2S2bVk;S28Vo;A1A2A2S2bVk;S27Vo;A1A2A2").
Lemma rng_below_agree : ltac2:(tb__ "0|0|
S1S25S25S24S2dR4R3R2A3S4S12S47R5R2A2S16A3S4S14S0S0A2S23R4R3A2S23R5R3A2A3F_;F_;Fo;Frho';Frho;Fk;").
Proof.
  intros k rho rho' o Hag H. unfold rng_below in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite <- (eval_agree k rho rho' _ Hag H1), (soff_agree k rho rho' _ Hag H2), (soff_agree k rho rho' _ Hag H3). reflexivity.
Qed.

Definition winpb (o : sobj) : bool := ltac2:(tb__ "0|9|
S22S12Lx;M0S26Vo;A1S0S13Lz;S1S1S12Li;R1S1S13Lp;S1S1S12Lp;R1S1S1S12Lp0;R1S1S13Lp1;S1S1S12Lp1;R1S1S13Lp2;M1G1G0S28Vo;A1S0G0S27Vo;A1S0S15S15SbS10S65A1R2A2SbR2R1A2A2SbR1Z0A2A2Lhi;S1S13Li0;M2S74S22S22S13Lb;La;M3Lop;M4G4S75G3Lop;M5G5S12S2S22S13La;Lw;Lsgn;M6S1S22S0S13Lk;M7Li0;Ll;M8X22x8Llo;G2G4G4G5G5G6G8X22x8X1x3Lp1;S13X1x3Lp0;S1S13Lp0;S13X1x3Lp;S13X1x3Li;G4G4G5G5G6S1S22G7Li;Ll;X22x8").
Definition rd_okb (nW : nat) (q : qvar) (o : sobj) : bool := ltac2:(tb__ "0|1|
S18S18S18S18S43S24S45Vo;A1M0S73S4cS24S4dS52Vq;A1A4A3S45Vo;S5cA2A2S45Vo;S5bA2A2S4aVo;A1A2S43S24G0S68S64VnW;A1A1A3A2").

Section RDZ.
Variables (A : AA) (rho : valuation) (tp0 : list word) (md0 : Model) (p n : Z).
Hypothesis HA : ltac2:(tb__ "0|0|
S4eS30VA;Vrho;Vtp0;Vmd0;A5").
Hypothesis HL : ltac2:(tb__ "0|0|
S42S14S0S0A2S19S0S0Vp;Vn;A4S36VA;A1A3").
Hypothesis HHI : blk_cls p n.
Hypothesis Hp12 : ltac2:(tb__ "0|0|
S4S0S70Q40S2aVrho;PcA2A2Vp;A3").
Variables (t : Z) (jv : junkF).
Hypothesis Ht : ltac2:(tb__ "0|2|
S3S3S8Z0Vt;A2S9Vt;Z100A2A2S3S4S0SdVt;Z4A2Z1A3S3S1fS21S30S29Vrho;A1A2M0S20ScVp;Z10A2U4M1S53Vt;Vn;A2A3A2S1fG0S20ScVp;ZcA2G1SdVn;SeZ2Z20A2A2A3A2A2A2A2").
Hypothesis Hjv : ltac2:(tb__ "0|9|
S3S3S8Z0M0S54Vjv;A1M1A2S9G1SeZ2Z40A2M2A2A2S3S3S8G0S57Vjv;A1M3A2S9G3G2A2A2S3S3S8G0S56Vjv;A1M4A2S9G4G2A2A2S3S3S8G0S55Vjv;A1M5A2S9G5G2A2A2S3S1fS21S30S29Vrho;A1A2M6S20SaS4fZ48A2U8M7G1A3A2S3S1fG6S20SaS38S32VA;A1A1M8Zae0A2G7G3A3A2S4S17S33A1S39VA;A1S1cS33A1A3S3S1fG6S20SaG8Z58A2G7G4A3A2S1fG6S20SaG8Z60A2G7G5A3A2A2F_;A2A2A2A2A2A2").
Variables (nW : nat) (q : qvar).
Hypothesis QC : qcond q A.
Let rho1 : valuation := ltac2:(tb__ "0|0|
S58VA;Vrho;Vp;Vn;Vt;Vjv;A6").
Variable rhoE : valuation.
Hypothesis HAG : ltac2:(tb__ "0|0|
S2dS31Vrho1;VrhoE;A3").
Hypothesis HTOP : top_high A rhoE.
Hypothesis HDEP : ltac2:(tb__ "0|0|
S8S71Q40S2aVrhoE;S66A2A2S10S65A1A2").
Hypothesis HCH : ltac2:(tb__ "0|0|
S72S2fS2eVrhoE;A1S67S64VnW;A1A1A3").

Lemma BNDz : ltac2:(tb__ "0|1|
S3S76Vp;S4bVn;A1M0A2S3S8Z1Vn;A2S3S9SaVp;G0A2Z7fffff800000A2S3S8Vn;G0A2S8Z8G0A2A2A2A2A2").
Proof.
  pose proof (blkF_geom A rho tp0 md0 p n HA HL HHI) as (B1 & _ & B3 & B4 & _). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (N8_facts n B3) as (N1 & _ & N3 & _). repeat split; try assumption; lia.
Qed.
Lemma R_blk1 : ltac2:(tb__ "0|0|
S4S14S0S0A2S23Vrho1;S5bA2S19S0S0Vp;SaVp;S4bVn;A1A2A4A3").
Proof.
  pose proof BNDz as (B1 & B2 & B3 & B4 & B5). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. unfold O_blkN, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  rewrite soff_lit_small by lia. rewrite (soff_of_val rho1 vN8 (N8 n)); [| change (eval rho1 vN8) with (Z_to_bv 64 (N8 n)); apply u64_lit; lia | lia].
  change (eval rho1 (SVar 12)) with (rw rho 12%positive). rewrite Hp12. f_equal; lia.
Qed.
Lemma R_sh1 : ltac2:(tb__ "0|1|
S4S14S0S0A2S23Vrho1;S5cA2S19S0S0S62Vp;A1M0SaG0S11S4bVn;A1Z8A2A2A4A3").
Proof.
  pose proof BNDz as (B1 & B2 & B3 & B4 & B5). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1. unfold O_sh, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
  pose proof (Z.div_pos (N8 n) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (N8 n) 8 (N8 n) ltac:(lia) ltac:(lia)).
  rewrite soff_lit_small by lia. rewrite (soff_of_val rho1 vN8g (N8 n / 8)); [| change (eval rho1 vN8g) with (Z_to_bv 64 (N8 n / 8)); apply u64_lit; lia | lia].
  assert (E : bv_unsigned (eval rho1 shb) = Sh p).
  { cbn [eval shb]. change (rw rho1 12%positive) with (rw rho 12%positive). rewrite add_val, srl_val, !u64_lit by (unfold SHADOW_OFF; lia). rewrite Hp12. change (3 mod 64) with 3.
    rewrite Z.shiftr_div_pow2 by lia. unfold Sh, SHADOW_OFF. pose proof (Z.div_lt_upper_bound p (2 ^ 3) (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos p (2 ^ 3) ltac:(lia) ltac:(lia)). rewrite Z.mod_small by lia. reflexivity. }
  rewrite E. f_equal; lia.
Qed.

Theorem rd_zone : ltac2:(tb__ "0|1|
S24S4S12S49VnW;Vq;R1A3S16A3S4S12S47S31R2A2S16A3S0S3S8S1aS0S0S23VrhoE;R4A2M0A3R1A2S9R1S1dS0S0G0A3A2A2S46VA;R2A2F_;Fa;F_;F_;Fo;").
Proof.
  intros o Hok Hb a Ha. rewrite (rng_below_agree GW rho1 rhoE o HAG Hb) in Ha.
  pose proof BNDz as (B1 & B2 & B3 & B4 & B5). unfold blk_geo in B1.
  unfold rd_okb in Hok. apply Bool.orb_prop in Hok as [Hok|Hok]; [apply Bool.orb_prop in Hok as [Hok|Hok]; [apply Bool.orb_prop in Hok as [Hok|Hok]; [apply Bool.orb_prop in Hok as [Hok|Hok]|]|]|].
  - apply existsb_exists in Hok as (o' & Ho' & Hs). rewrite (same_rng_range rho1 o o' Hs) in Ha.
    apply in_map_iff in Ho' as (k & <- & Hk). exact (nfs_zoneF A rho tp0 md0 p n HA HL HHI Hp12 t jv Ht Hjv q QC k Hk a Ha).
  - rewrite (same_rng_range rho1 o O_sh Hok), R_sh1 in Ha. cbn [fst snd] in Ha. unfold zoneF. cbn zeta. do 5 right. left.
    pose proof (Sh_in_band p ltac:(unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1; lia)) as S1. pose proof (Sh_in_band (p + N8 n) ltac:(unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1; lia)) as S2.
    assert (S3 : Sh p + N8 n / 8 <= Sh (p + N8 n)).
    { unfold Sh. pose proof (N8_facts n B2) as (_ & _ & _ & N4). rewrite <- N4 at 2. rewrite Z.div_add by lia. lia. }
    lia.
  - rewrite (same_rng_range rho1 o O_blkN Hok), R_blk1 in Ha. cbn [fst snd] in Ha. apply (chunk_zoneF A rho tp0 md0 p n a HA HL). lia.
  -
    unfold winpb in Hok. destruct o as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in Hok.
    destruct ob as [| v | | | | | | ]; try discriminate. destruct v as [v|v|]; try discriminate. do 3 (destruct v as [v|v|]; try discriminate).
    destruct olo as [lo| | | | | | | ]; try discriminate. destruct ohi as [hi| | | | | | | ]; try discriminate.
    apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [H1 H2]. apply Z.leb_le in H1, H2, H3. unfold free_depth in *.
    rewrite obj_range_mk in Ha by lia. cbn [fst snd eval] in Ha.
    assert (E10 : rw rho1 10%positive = rw rhoE 10%positive) by (apply (proj1 HAG); unfold GW; lia). rewrite E10 in Ha.
    unfold top_high in HTOP. unfold zoneF. cbn zeta. do 6 right. lia.
  -
    apply existsb_exists in Hok as (o' & Ho' & Hs). rewrite (same_rng_range rho1 o o' Hs) in Ha.
    assert (LNK : Forall (fun o => bv_unsigned (rw rhoE 10%positive) + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs (Wcan nW))).
    { unfold unwind_objs. destruct (Wcan nW) as [|l W'] eqn:EW; [constructor|].
      unfold chain_pre in HCH. cbn [app] in HCH.
      pose proof (Forall_inv HCH) as C0. pose proof (Forall_inv (Forall_inv_tail HCH)) as C1.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HCH))) as C2. do 3 apply Forall_inv_tail in HCH.
      cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
      pose proof (urange (rw rhoE 10%positive)). rewrite Z.mod_small in C1 by lia.
      eapply Forall_impl; [|apply (chain_facts_bases rhoE (SVar 28) (l :: W') HCH); cbn [eval]; lia].
      intros o0 (B & L & Hh). cbn [eval] in B. repeat split; try assumption; lia. }
    pose proof (proj1 (Forall_forall _ _) LNK o' Ho') as (L1 & L2 & L3).
    assert (WF' : rng_below GW o' = true).
    { unfold rng_below in Hb |- *. unfold same_rng in Hs. apply andb_prop in Hs as [Hs S3]. apply andb_prop in Hs as [S1 S2].
      apply sv_eqb_sound in S1, S2, S3. rewrite <- S1, <- S2, <- S3. exact Hb. }
    rewrite <- (rng_below_agree GW rho1 rhoE o' HAG WF') in Ha.
    destruct o' as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in L1, L2, L3. subst olo ohi. rewrite obj_range_mk in Ha by lia. cbn [fst snd] in Ha.
    unfold top_high in HTOP. unfold free_depth in HDEP. unfold zoneF. cbn zeta. do 6 right. lia.
Qed.
End RDZ.
End F0A_dzone.

(* [comment removed for export] *)
Module F0A_minit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "Pre_freeI"; "KcA"; "ulink"; "Kc_ok"; "ustop"; "J_free_preT"; "UStopLeOrPc"; "Wcan"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Init.Datatypes"; "list"; "bool"; "prod"; "true"; "cons"; "nil"; "false"; "option"; "pair"; "Some"; "nat"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "rm"; "sobj"; "swf"; "sprop"; "SLit"; "SVar"; "agree_below"; "eval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_internal_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit"; "N_pg"; "N_i0"; "N_i1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates"; "sa_i"; "MIDx"; "Pre_mid"; "RT_i"; "fi_cutpcs"; "sb_i"; "sc_i"; "P0i"; "fi_cuts"; "fi_vcuts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "@Corelib.Lists.ListDef"; "map"; "nth"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit"; "N_rest"; "K_iaw0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok"; "junkF"; "rhoF_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "set_inited"; "ia_zone"; "geom_ok"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "check_cfgA"; "check_ecfgA"; "mkVNA"; "withGA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull"; "rt_zone2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_minit.MI"; "mid_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_in_view"; "rd_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit"; "O_iaw"; "O_iaw_done"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM"; "rt_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue"; "coverb"; "spec_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.GlueMZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.F0A_mstates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition N_pg : list carve_spec := ltac2:(tb__ "0|0|
S15SfS45SfUdS47S48A4S15SfS45SfUeS47S48A4S16SfA1A3A3").
Definition N_i0 : list carve_spec := K_iaw0 :: N_pg.
Definition N_i1 : list carve_spec := K_iaw_done :: N_pg.
Lemma N_pg_ok : ltac2:(tb__ "0|0|
S0S11S21A1S44SfS21S10S32A4S3cA3"). Proof. reflexivity. Qed.
Lemma N_i0_ok : ltac2:(tb__ "0|1|
S0S11S21A1S44SfS21S10S33A4S15S21S63Z0M0G0A2S3cA3A3"). Proof. reflexivity. Qed.
Lemma N_i1_ok : ltac2:(tb__ "0|0|
S0S11S21A1S44SfS21S10S34A4S15S21S64S3cA3A3"). Proof. reflexivity. Qed.
Lemma N_pg_rest : ltac2:(tb__ "0|0|
SfS4eSfR1S32A3S4eSfR2S47A3F_;Fk;").
Proof. intros k [<-|[<-|[]]]; unfold N_rest, N_fn; cbn [tl nth]; cbn; tauto. Qed.

Section MI.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
ScVAInv;VW;Vst;VA;VKc;A5").

Lemma fi_instantiate : ltac2:(tb__ "0|5|
S1bSbS2eS8S1eS11S2bQ40A1A1S35S4S4S4S49SeRbA1S11S9A1M0S0SbRbSdA3S0G0R2S16S9A1A3F_;S68R2RcA2S0S12S30RcA1S17A3S0S12S22S39R4ReA2A1S14A3S0S18S13S11S13S1fS1fA2M1A1M2S11S23A1M3A2M4A1S53S5aS7S6R5RfA3A1S39R5RfA2A2S1aG4S19G2G3S15G1S19S1fS1fS25P18A1S24S5cA1A4S16G1A1A3S16S23A1A4A2A3S0S12S22S3eR6R10A2A1S14A3S0S12S22S3fR7R11A2A1S14A3S28Vsegs;VJ;R8R12R11R10A4S7S6R8R12A3RfReRdA6S28Vsegs;VJ;R9R13R12R11A4S40R9R13A2S4aR12R10RdRcRbRaA6RfReA6F_;F_;F_;F_;F_;F_;F_;F_;TW;Fjv;Ft;Fn;Fp;Fw;Ftp;Frho0;FKc;FA;Fst;FnW;").
Proof.
  intros nW st A Kc rho0 tp w p0 n0 t jv W HW HUS Hii Wa Da Wb Wc H0.
  set (rho := rhoF_of A rho0 p0 n0 t jv).
  assert (H : SPA segs (J W st A Kc) (Pre_freeI AE_A W st) rho tp w).
  { eapply SPA_agree; [| |exact H0]; [eapply agree_below_le; [|exact (rhoF_agree A rho0 p0 n0 t jv)]; cbv; discriminate
                                     | apply (JFr_agree nW st true A Kc rho0 rho); [exact HUS | exact (rhoF_agree A rho0 p0 n0 t jv)]]. }
  clear H0.
  pose proof H as [HsmA HJ]. destruct HJ as (HA & HU & HL & HK & Htp & HB & Htop).
  pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. destruct HG' as (_ & _ & _ & G4 & _).
  pose proof (topG_range (aa_geom A)) as TR. set (TOP := topG (aa_geom A)) in *.
  set (p := bv_unsigned (rw rho 12%positive)) in *. set (n := bv_unsigned (rw rho 13%positive)) in *.
  destruct HRest as (Hsep & _ & _ & _ & _ & _ & HIA & _).
  destruct (Hsep p n HL) as (S1 & S2 & S3 & _). unfold IMG_HI in S2. fold TOP in S3.
  unfold ia_inv in HIA. rewrite Hii in HIA. destruct HIA as (IA9 & IAa & IAb & IA8 & IAF).
  assert (MV : forall z, z < 0x643000 -> maskv (fs_footb (aa_geom A)) (view segs (rm rho)) z = view segs (rm rho) z).
  { intros z Hz. apply maskv_out. apply fs_footb_img; [exact HG0 | exact Hz]. }
  rewrite MV in IA9, IAa, IAb, IA8 by lia.
  assert (IAF' : forall z, IA_BEG <= z < IA_END -> view segs (rm rho) z = Some (Z_to_bv 8 0)).
  { intros z Hz. rewrite <- MV by (unfold IA_BEG, IA_END in Hz; lia). exact (IAF z Hz). }
  assert (TOPlo : TOP <= fst (obj_range rho stack_win)) by exact Htop.

  assert (H2 : SPA segs (J W st A Kc) (mkAX (sa_i W st) [] base_sv) rho tp w).
  { change (mkAX (sa_i W st) [] base_sv) with (ax_setS (Pre_freeI AE_A W st) (sa_i W st)).
    eapply SPA_restate; [exact Wa | exact Da | reflexivity | | constructor | exact H].
    constructor; [|constructor]. cbn [fst snd eval]. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    rewrite Htp, G4. reflexivity. }
  clear H HsmA.
  pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
  assert (Hhigh : holds rho F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn [ss_facts sa_i]; unfold FACTSi; apply in_or_app; right; cbn; tauto).
  destruct (stack_win_range _ rho _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
  assert (LNK : Forall (fun o => TOP + 16 <= bv_unsigned (eval rho (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { unfold unwind_objs. destruct W as [|l W'] eqn:EW; [constructor|].
    destruct st; [|discriminate (HW eq_refl)].
    assert (HC : Forall (holds rho) (chain_pre (l :: W'))).
    { apply Forall_forall. intros pp Hp. apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts sa_i]. unfold FACTSi. apply in_or_app. left. apply chain_pre_in. exact Hp. }
    unfold chain_pre in HC. cbn [app] in HC.
    pose proof (Forall_inv HC) as C0. pose proof (Forall_inv (Forall_inv_tail HC)) as C1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as C2. do 3 apply Forall_inv_tail in HC.
    cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
    pose proof (urange (rw rho 10%positive)). rewrite Z.mod_small in C1 by lia.
    eapply Forall_impl; [|apply (chain_facts_bases rho (SVar 28) (l :: W') HC); cbn [eval]; lia].
    intros o (B & L & Hh). cbn [eval] in B. repeat split; try assumption; lia. }
  pose proof (urange (rw rho 12%positive)) as U12. pose proof (urange (rw rho 13%positive)) as U13. fold p in U12. fold n in U13.

  assert (RBLK : obj_range rho O_blkP = (p, p + n)).
  { unfold O_blkP, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite soff_lit_small by lia.
    unfold soff. cbn [eval]. fold p. rewrite bv_signed_U. unfold Zsigned, H63v, M64v. fold n.
    destruct (Z.ltb_spec n 9223372036854775808); [f_equal; lia | exfalso; lia]. }

  assert (H3 : SPA segs (J W st A Kc) (mkAX (sb_i W st) [] base_sv) rho tp w).
  { change (mkAX (sb_i W st) [] base_sv) with
      (ax_setS (mkAX (sa_i W st) [] base_sv) (let S := ax_S (mkAX (sa_i W st) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ map carve_obj N_i0) (ss_facts S) NW2 (ss_lenient S))).
    eapply SPA_carve_list; [exact H2 | exact Wb | cbv; discriminate | | |].
    - unfold N_i0, N_pg, N_rest, N_fn, K_iaw0. cbn [tl nth].
      repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?u64_lit by lia.
      all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
      all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      all: split; [|split; [|apply xwords_clear_nil]].
      all: match goal with
           | |- cells_in_view _ _ 0 [(0x17db48, _, _); _; _; _] =>
               unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; intros j Hj; replace j with 0%nat by lia;
               cbn [Z.of_nat]; rewrite ?Z.add_0_r, ?Z.add_0_l; rewrite <- view_in by lia; rewrite nth0_enc1_zero;
               first [exact IA8 | exact IA9 | exact IAa | exact IAb]
           | |- cells_in_view _ _ _ _ => unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; civ_any2 HR
           | _ => idtac end.
      all: try match goal with
           | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
           end.
      all: fail "fi_instantiate: carve obligation left".
    - unfold N_i0, N_pg, N_rest, N_fn, K_iaw0. cbn [tl nth map carve_obj ss_objs ax_S sa_i]. unfold PREOBJSi, carved.
      unfold A_globals. unfold O_got, O_rtc. unfold GOT_LO, GOT_HI, RTC_LO, RTC_HI.
      repeat (apply Forall_cons;
        [ apply Forall_cons;
          [ unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia;
            destruct (obj_range rho stack_win) as [lo' hi']; cbn [fst snd] in *; lia
          | apply Forall_app; split;
            [ eapply Forall_impl; [|exact LNK]; intros [ob olo ohi ocs od] (B & L & Hh); cbn [ob_base ob_lo ob_hi] in B, L, Hh; subst olo ohi;
              unfold ranges_disjoint; rewrite !obj_range_mk by lia; cbn [fst snd eval]; cbn [eval] in B; rewrite ?u64_lit by lia; lia
            | apply Forall_cons; [unfold ranges_disjoint; rewrite RBLK; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia|];
              repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint;
              rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia ] ]
        | ]).
      apply Forall_nil.
    - unfold N_i0, N_pg, N_rest, N_fn, K_iaw0. cbn [tl nth map carve_obj pairwise_disjoint]. unfold carved.
      repeat split; repeat apply Forall_cons; try apply Forall_nil; try exact I; unfold ranges_disjoint;
        rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia. }
  clear H2.

  destruct w as [tr [ms md]].
  change (P0i W st) with
      (ax_setS (mkAX (sb_i W st) [] base_sv) (let S := ax_S (mkAX (sb_i W st) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [mkObj (SLit 0) (SLit IA_LO) (SLit IA_HI) [] DZero]) (ss_facts S) NW2 (ss_lenient S))).
  apply (SPA_carve_zero_rd segs (J W st A Kc) rho (mkAX (sb_i W st) [] base_sv) tp tr ms md (SLit 0) IA_LO IA_HI NW2 H3 Wc);
    cbn [ax_S ss_next sb_i ax_X ss_objs eval]; rewrite ?u64_lit by lia; unfold IA_LO, IA_HI; try lia.
  - apply Forall_app. split.
    + unfold PREOBJSi. apply Forall_cons; [unfold ranges_disjoint; destruct (obj_range rho stack_win) as [lo' hi']; cbn [fst snd] in *; lia|].
      apply Forall_app. split.
      * eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
        unfold ranges_disjoint. rewrite !obj_range_mk by lia. cbn [fst snd eval]. cbn [eval] in B. lia.
      * apply Forall_cons; [unfold ranges_disjoint; rewrite RBLK; cbn [fst snd]; lia|].
        unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; lia.
    + unfold RT_i, O_iaw, O_pga, O_pgb. unfold carved.
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia; unfold PG; lia.
  - intros a Ha. split; [apply wok_of_imageA; lia|]. rewrite <- view_in by lia. apply IAF'. unfold IA_BEG, IA_END. lia.
  - intros rr y j [].
Qed.

Lemma N_pg_small : Forall spec_small N_pg.
Proof. apply Forall_forall. intros k Hk. exact (proj1 (Forall_forall _ _) N_rest_small k (N_pg_rest k Hk)). Qed.
Lemma N_i1_small : Forall spec_small N_i1.
Proof. apply Forall_cons; [exact (Forall_inv N_fni1_small) | exact N_pg_small]. Qed.
Lemma N_pg_coverb : ltac2:(tb__ "0|0|
S0S12S4fSfS66S32A3S14A3").
Proof. apply forallb_forall. intros k Hk. exact (proj1 (forallb_forall _ _) N_rest_coverb k (N_pg_rest k Hk)). Qed.
Lemma fi_civ : ltac2:(tb__ "0|4|
S2eS1eS11S2bQ40M0A1A1S60VAInv;R4R3R2R1A4S46SfSfS13S13S13S1fS4A2M1S4A2M2S11S13S13S4S1bA2S1fA2A1M3A2OLk;R1G2G3G2OLp;R2G1S4G1OLp0;R2S1fS4S61RbS62Vsegs;S20RbA1A2S2dG0S27RbR2A2A2R5A4Llo;Lbase;X13x1Lhi;Lp0;X13x1Lcs;Lp;X13x1Lk;S32A3F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md HA. pose proof HA as (HG & HR & _).
  unfold N_pg, N_rest, N_fn. cbn [tl nth].
  repeat apply Forall_cons; try apply Forall_nil; lazy beta iota zeta; cbn [eval]; rewrite ?u64_lit by lia.
  all: unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; cbn [eval].
  all: civ_any2 HR.
Qed.
Lemma N_pg_zone : ltac2:(tb__ "0|1|
S2eS1eSfS4S4dS2fR4A1A1S4eSfR3S32A3S1S50S1cS4S4S67R5R4A2M0A3R3A2S51R3S1dS4S4G0A3A2A2S65S2fR7A1R4A2F_;F_;F_;Fa;Fk;Frho;FA;").
Proof.
  intros A rho k a HG Hk Ha.
  pose proof (proj1 (forallb_forall _ _) N_rest_img_zone1 k (N_pg_rest k Hk)) as IZ.
  unfold N_pg, N_rest, N_fn in Hk. cbn [tl nth In] in Hk. unfold rt_zone.
  repeat (destruct Hk as [E|Hk];
    [subst k; cbn [spec_range fst snd eval] in Ha; rewrite ?u64_lit in Ha by lia;
     left; split; [unfold IMG_HI; lia|]; unfold img_zone_okb in IZ;
     eapply (forall_rangeZ_ok (fun a0 => cells_footb (rtc_cells_img RTC_A G0) a0)); [exact IZ | lia]
    |]).
  destruct Hk.
Qed.

Lemma fi_reabstract : ltac2:(tb__ "0|3|
S11S9A1S2eS8S1eS11S2bQ40M0A1A1S35S1eS0S12S30R6A1S17A3S28Vsegs;S59S1eS26S31R6R1A3Lr;VJ;R8S5R7R6A4A2S3aR8S5A2R2R4R3A6S3S1eS1eS1S28Vsegs;VJ;RaS5S4bR9A1R8A4S3bRaS5A2R1R6R5A6S1S54S31R7R1A3S1S4S2S4cR1A1A1S0S18S2bQ8A1A1M1S43Vsegs;S20R3A1R2A3S43Vsegs;S20R9A1R2A3A3F_;Fz;S4S1S50Z0R1A2S51R1S52Z2Z40A2A2A2S2S5dS2fRbA1R2A2A1S0G1S20R4S2cG0R3A2M2A2S20RaG2A2A3F_;F_;Fa;A2A2A2Lrho2;A2F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;FW;").
Proof.
  intros W A Kc rho tp w rhoE Hii H.
  destruct w as [tr [ms md]]. destruct H as [HsmA [Hag HJ]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  destruct HJ as (HA & HU & HL & HK & Htp & HB & Htop).
  destruct Hag as (Hagw & Hagl & Hagm).
  assert (Erm : rm rhoE = rm rho).
  { apply functional_extensionality. intros a. rewrite <- Hagm. reflexivity. }
  pose proof HA as (HG & HR & HF & HRest & HM). pose proof (proj1 HRest) as Hsep.
  pose proof (topG_range (aa_geom A)) as TG.

  assert (Ha : SPA segs (fun _ _ t m => Kc t m) (MIDx W UStopLe) rhoE tp (tr, mkCfg ms md)) by (split; [exact HsmA | exact HK]).
  pose proof (SPA_unobj segs (fun _ _ t m => Kc t m) rhoE (MIDx W UStopLe) (PREOBJSi W stack_win_mid ++ (O_iaw_done :: RT_i)) [O_inst inst_cells] tp tr ms md eq_refl Ha (fun k => k)) as Hb1.
  cbn zeta in Hb1. set (rho2 := rho_absorb rhoE [O_inst inst_cells] (vms md tp ms)) in *.
  change (ax_setS (MIDx W UStopLe) (set_objs (ax_S (MIDx W UStopLe)) (PREOBJSi W stack_win_mid ++ (O_iaw_done :: RT_i)))) with (mkAX (stJ_i W UStopLe) [] base_sv) in Hb1.
  pose proof (proj1 (proj1 Ha)) as HsmE. unfold virt in HsmE. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in HsmE.

  pose proof (SPA_unobj segs (fun _ _ t m => Kc t m) rho2 (mkAX (stJ_i W UStopLe) [] base_sv) (PREOBJSi W stack_win_mid) (O_iaw_done :: RT_i) tp tr ms md eq_refl Hb1 (fun k => k)) as Hb.
  cbn zeta in Hb. set (rho3 := rho_absorb rho2 (O_iaw_done :: RT_i) (vms md tp ms)) in *.
  change (ax_setS (mkAX (stJ_i W UStopLe) [] base_sv) (set_objs (ax_S (mkAX (stJ_i W UStopLe) [] base_sv)) (PREOBJSi W stack_win_mid))) with (Pre_mid W UStopLe) in Hb.
  pose proof (proj1 (proj1 Hb1)) as Hsm2. unfold virt in Hsm2. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm2.
  assert (EV2 : forall e, eval rho2 e = eval rhoE e) by (intros e; unfold rho2; apply eval_absorb).
  pose proof (fi_civ A rhoE tp md HA) as CIV.
  assert (RNG1 : forall z o, In o (O_iaw_done :: RT_i) -> fst (obj_range rho2 o) <= z < snd (obj_range rho2 o) ->
                 (0x17db48 <= z < 0x17db4c) \/ exists k, In k N_pg /\ fst (spec_range rhoE k) <= z < snd (spec_range rhoE k)).
  { intros z o Hin Hr. rewrite <- N_i1_ok in Hin. apply in_map_iff in Hin as (k & <- & Hk).
    pose proof (proj1 (Forall_forall _ _) N_i1_small k Hk) as Sk.
    destruct Hk as [<-|Hk].
    - left. cbn [carve_obj K_iaw_done] in Hr. unfold carved in Hr. rewrite obj_range_mk in Hr by lia. cbn [fst snd] in Hr. rewrite EV2 in Hr. cbn [eval] in Hr. rewrite u64_lit in Hr by lia. lia.
    - right. exists k. split; [exact Hk|]. destruct k as [[[base lo] hi] cs]. cbn [carve_obj] in Hr.
      destruct Sk as (S1 & S2 & S3 & _). unfold carved in Hr. rewrite obj_range_mk in Hr by lia. cbn [fst snd ob_base spec_range] in Hr |- *.
      rewrite EV2 in Hr. exact Hr. }
  assert (VEQ : forall z, ~ ia_zone z -> view segs (rm rho3) z = view segs (rm rhoE) z).
  { intros z Hz. destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|].
    2,3: rewrite !view_out by lia; reflexivity.
    rewrite !view_in by lia. destruct (in_ranges_dec rho2 (O_iaw_done :: RT_i) (Z_to_bv 64 z)) as [Hri|Hrn].
    - destruct Hri as (o & Hin & Hr). rewrite u64_lit in Hr by lia.
      destruct (RNG1 z o Hin Hr) as [Zi|(k & Hk & Hzk)]; [exfalso; apply Hz; unfold ia_zone; lia|].
      unfold rho3. eapply (absorb_specs_view rho2 (stJ_i W UStopLe) tr (vms md tp ms) (vmd md) (PREOBJSi W stack_win_mid) (O_iaw_done :: RT_i) N_pg (rd_of segs (rm rhoE)) Hsm2 eq_refl); [| exact Hk |].
      + intros k' Hk'. split; [rewrite <- N_i1_ok; apply in_map; right; exact Hk'|]. split; [exact (proj1 (Forall_forall _ _) N_pg_small k' Hk')|].
        split; [apply coverb_sound; exact (proj1 (forallb_forall _ _) N_pg_coverb k' Hk')|].
        pose proof (proj1 (Forall_forall _ _) CIV k' Hk') as C'. destruct k' as [[[base lo] hi] cs]. cbn [spec_range fst snd].
        cbn zeta in C'. rewrite EV2. replace (bv_unsigned (eval rhoE base) + lo - lo) with (bv_unsigned (eval rhoE base)) by lia.
        unfold cells_in_view in C' |- *. apply Forall_forall. intros [[o1 n1] e1] Hin' j Hj. rewrite EV2. exact (proj1 (Forall_forall _ _) C' _ Hin' j Hj).
      + destruct k as [[[base lo] hi] cs]. cbn [spec_range fst snd] in Hzk |- *. rewrite EV2. exact Hzk.
    - unfold rho3, rd_of. rewrite rm_absorb_out by exact Hrn.
      destruct (in_ranges_dec rhoE [O_inst inst_cells] (Z_to_bv 64 z)) as [Hri2|Hrn2].
      + exfalso. destruct Hri2 as (o & [<-|[]] & Hr). unfold O_inst in Hr. rewrite obj_range_mk in Hr by (unfold IA_LO, IA_HI; lia).
        cbn [fst snd eval] in Hr. rewrite !u64_lit in Hr by lia. apply Hz. unfold ia_zone, IA_BEG, IA_END. unfold IA_LO, IA_HI in Hr. lia.
      + unfold rho2. rewrite rm_absorb_out by exact Hrn2. reflexivity. }
  assert (Hrom2 : rom_ok segs (vms md tp ms)) by exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm2))))).
  assert (IAZ : forall z, IA_MAP1 <= z < IA_MAP1 + IA_MAP1_SZ -> view segs (rm rho3) z = Some (Z_to_bv 8 0)).
  { intros z Hz. unfold IA_MAP1, IA_MAP1_SZ in Hz. rewrite view_in by lia.
    assert (Hrn : ~ in_ranges rho2 (O_iaw_done :: RT_i) (Z_to_bv 64 z)).
    { intros (o & Hin & Hr). rewrite u64_lit in Hr by lia. destruct (RNG1 z o Hin Hr) as [Zi|(k & Hk & Hzk)]; [lia|].
      destruct (rt_zone_not_ia _ z HG (N_pg_zone A rhoE k z HG Hk Hzk)) as [X _]. unfold IA_BEG, IA_END in X. lia. }
    pose proof (absorb_zero_dflt segs rhoE (ax_S (MIDx W UStopLe)) tr (vms md tp ms) (vmd md) _ [O_inst inst_cells] (SLit 0) IA_LO IA_HI inst_cells
                  HsmE eq_refl ltac:(left; reflexivity) ltac:(unfold IA_LO; lia) ltac:(unfold IA_LO, IA_HI; lia) ltac:(unfold IA_HI; lia)) as ZD.
    cbn zeta in ZD. cbn [eval] in ZD. rewrite u64_lit in ZD by lia. fold rho2 in ZD.
    unfold rho3, rd_of. rewrite rm_absorb_out by exact Hrn.
    change (rd_of segs (rm rho2) (Z_to_bv 64 z) = Some (Z_to_bv 8 0)). rewrite <- (Z.add_0_l z).
    apply ZD; [unfold IA_LO, IA_HI; lia|].
    unfold inst_cells. intros Hcov. unfold covered in Hcov. apply Exists_exists in Hcov as (c & Hc & Hic).
    destruct Hc as [<-|[<-|[]]]; unfold in_cell in Hic; cbn [c_off c_width] in Hic; rewrite soff_lit_small in Hic by lia; lia. }
  assert (IAW : view segs (rm rho3) 0x17db49 = Some (Z_to_bv 8 0) /\ view segs (rm rho3) 0x17db4a = Some (Z_to_bv 8 0)
                /\ view segs (rm rho3) 0x17db4b = Some (Z_to_bv 8 0) /\ view segs (rm rho3) 0x17db48 = Some (Z_to_bv 8 1)).
  { destruct (absorb_carved_cells segs rho2 (stJ_i W UStopLe) tr (vms md tp ms) (vmd md) (PREOBJSi W stack_win_mid) (O_iaw_done :: RT_i)
                (SLit 0) 0x17db48 0x17db4c [(0x17db49, 1%nat, SLit 0); (0x17db48, 1%nat, SLit 1); (0x17db4a, 2%nat, SLit 0)]
                Hsm2 eq_refl ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)) as [C _].
    fold rho3 in C. unfold cells_in_view in C. rewrite EV2 in C. cbn [eval] in C. rewrite u64_lit in C by lia.
    pose proof (Forall_inv C) as C9. pose proof (Forall_inv (Forall_inv_tail C)) as C8. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail C))) as Ca.
    cbn zeta in C9, C8, Ca.
    rewrite !view_in by lia.
    split; [specialize (C9 0%nat ltac:(lia)); replace (0 + 0x17db49 + Z.of_nat 0) with 0x17db49 in C9 by lia; change (eval rho3 (SLit 0)) with (Z_to_bv 64 0) in C9; rewrite nth0_enc1_zero' in C9; exact C9|].
    split; [pose proof (Ca 0%nat ltac:(lia)) as Ca0; replace (0 + 0x17db4a + Z.of_nat 0) with 0x17db4a in Ca0 by lia; change (eval rho3 (SLit 0)) with (Z_to_bv 64 0) in Ca0; rewrite (nth_enc2_zero' 0%nat ltac:(lia)) in Ca0; exact Ca0|].
    split; [pose proof (Ca 1%nat ltac:(lia)) as Ca1; replace (0 + 0x17db4a + Z.of_nat 1) with 0x17db4b in Ca1 by lia; change (eval rho3 (SLit 0)) with (Z_to_bv 64 0) in Ca1; rewrite (nth_enc2_zero' 1%nat ltac:(lia)) in Ca1; exact Ca1|].
    specialize (C8 0%nat ltac:(lia)). replace (0 + 0x17db48 + Z.of_nat 0) with 0x17db48 in C8 by lia. change (eval rho3 (SLit 1)) with (Z_to_bv 64 1) in C8. rewrite nth0_enc1_one' in C8. exact C8. }
  destruct IAW as (V9 & Va & Vb & V8).
  assert (HA3 : AInv (set_inited A) rho3 tp md).
  { apply (AInvA_ia_update segs A rhoE rho3 tp md HA VEQ). unfold ia_inv. cbn [aa_internal_inited set_inited].
    split; [exact V9|]. split; [exact Va|]. split; [exact Vb|]. split; [exact V8|]. intros z Hz. exact (IAZ z Hz). }
  assert (E3w : forall k, rw rho3 k = rw rhoE k) by (intros k; unfold rho3, rho2; cbn [rho_absorb rw]; reflexivity).
  exists rho3. split; [|split; [|split]].
  - split; [exact (proj1 Hb)|]. cbn [w_tr w_cfg cfg_model fst snd].
    split; [exact HA3|]. split; [destruct W; exact I|].
    split; [rewrite !E3w; exact HL|]. split; [exact HK|].
    split; [unfold tp_ok in *; rewrite E3w; exact Htp|]. split; [exact HB|].
    unfold top_high in *. rewrite !E3w. exact Htop.
  - split; [intros k Hk; rewrite E3w; apply Hagw; exact Hk|].
    intros l. unfold rho3, rho2. cbn [rl rho_absorb]. apply Hagl.
  - intros z Hz. rewrite <- Erm. exact (VEQ z Hz).
  - intros a Ba Hz. rewrite <- Erm. unfold rho3. rewrite rm_absorb_out.
    + unfold rho2. apply rm_absorb_out. intros (o & [<-|[]] & Hr). apply Hz. unfold O_inst in Hr. rewrite obj_range_mk in Hr by (unfold IA_LO, IA_HI; lia).
      cbn [fst snd eval] in Hr. rewrite !u64_lit in Hr by lia. unfold rt_zone2, IA_BEG, IA_END. unfold IA_LO, IA_HI in Hr. right. left. lia.
    + intros (o & Hin & Hr). rewrite u64_lit in Hr by lia. apply Hz. destruct (RNG1 a o Hin Hr) as [Zi|(k & Hk & Hzk)]; [unfold rt_zone2; right; right; exact Zi|].
      left. exact (N_pg_zone A rhoE k a HG Hk Hzk).
Qed.

Definition mid_link (A : AA) (rho rho2 : valuation) : Prop := ltac2:(tb__ "0|2|
S1S54S31Vrho;Vrho2;A3S1S4S2S4cR1A1A1S0S18S2bQ8A1A1M0S43Vsegs;S20Vrho2;A1R2A3S43Vsegs;S20Vrho;A1R2A3A3F_;Fz;S4S1S50Z0R1A2S51R1S52Z2Z40A2A2A2S2S5dS2fVA;A1R2A2A1S0G0S20Vrho2;S2cQ40R3A2M1A2S20Vrho;G1A2A3F_;F_;Fa;A2A2").

Section PerN.
Variable n : nat.
Let W : list ulink := Wcan n.
Hypothesis Wa : ltac2:(tb__ "0|0|
S0S12S22S39VW;S5A2A1S14A3").
Hypothesis Da : ltac2:(tb__ "0|4|
S0S18S13S11S13S1fS1fA2M0A1M1S11S23A1M2A2M3A1S53S5aS7S6VW;S5A3A1S39VW;S5A2A2S1aG3S19G1G2S15G0S19S1fS1fS25P18A1S24S5cA1A4S16G0A1A3S16S23A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S0S12S22S3eVW;S5A2A1S14A3").
Hypothesis Wc : ltac2:(tb__ "0|0|
S0S12S22S3fVW;S5A2A1S14A3").

Hypothesis Cert : ltac2:(tb__ "0|0|
S0S12S56S5fUbb8S3dS31S41Vn;S5A2S15S5bS3aVW;S5A2S16S5bA1A3A6S14A3").
Hypothesis ECert : ltac2:(tb__ "0|1|
S0S12S57S5fUbb8S3dS31S42Vn;S5A2S15S55S58S3aVW;S5A2Z0M0S24G0A1A3S16S55A1A3A6S14A3").

Theorem fi_prefix : ltac2:(tb__ "0|0|
S35OF_;S2eS8S1eS11S2bQ40A1A1S38S4S4S4S49S0S12S30R9A1S17A3SaR9A1S2aVsegs;RcS29RaA1A3S1eS5eRdS4aRdRbR8R7R6R5A6R1A3S37Vsegs;RfS28Vsegs;VJ;VW;S5S4bReA1RdA4S3bVW;S5A2R2RbA5RaA4F_;Frho2;S37Vsegs;ReS28Vsegs;VJ;VW;S5RdRcA4S7S6VW;S5A3RbRaA5R9A4F_;F_;F_;F_;Fjv;Ft;Fn0;Fp0;FQ;Ftp;Frho0;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho0 tp Q p0 n0 t jv Hii HKc Hokf HC. set (rho := rhoF_of A rho0 p0 n0 t jv) in *.
  eapply triple_conseq; [intros w Hw; exact (fi_instantiate n UStopLe A Kc rho0 tp w p0 n0 t jv ltac:(intros E; discriminate E) (stopJ_stable_le _) Hii Wa Da Wb Wc Hw) | intros w Hw; exact Hw |]. fold rho.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs _ GW (P0i W UStopLe) rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 3000%nat fi_cutpcs GW (fi_cuts n UStopLe) [MIDx W UStopLe] (JF n UStopLe true A Kc rho) ok Q tp).
  - apply JF_okf. exact Hokf.
  - apply JF_stable; [apply stopJ_stable_le | exact HKc].
  - exact Cert.
  - intros E rhoE [<-|[]]. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    intros k Hg w Hw. destruct (fi_reabstract W A Kc rho tp w rhoE Hii Hw) as (rho2 & Hw2 & AG & VQ & RMO).
    exact (HC rho2 (conj AG (conj VQ RMO)) k Hg w Hw2).
  - left. reflexivity.
Qed.
Theorem efi_prefix : ltac2:(tb__ "0|0|
S2eS8S1eS11S2bQ40A1A1S35OF_;S4S4S4S49S0S12S30R9A1S17A3SaR9A1S1eS5eRcS4aRcRaR7R6R5R4A6R1A3S36Vsegs;S28Vsegs;VJ;VW;S5S4bRdA1RcA4S3bVW;S5A2R2RaA5R9A3F_;Frho2;S36Vsegs;S28Vsegs;VJ;VW;S5RcRbA4S7S6VW;S5A3RaR9A5R8A3F_;F_;F_;Fjv;Ft;Fn0;Fp0;FQ;Ftp;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 tp Q p0 n0 t jv Hii HKc HC. set (rho := rhoF_of A rho0 p0 n0 t jv) in *.
  eapply etriple_conseq; [intros w Hw; exact (fi_instantiate n UStopLe A Kc rho0 tp w p0 n0 t jv ltac:(intros E; discriminate E) (stopJ_stable_le _) Hii Wa Da Wb Wc Hw) | intros w Hw; exact Hw |]. fold rho.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs _ GW (P0i W UStopLe) rho tp w Hw) | intros w Hw; exact Hw |].
  change (P0i W UStopLe) with (vna_state (mkVNA (P0i W UStopLe) 5 (SLit 0))).
  apply (cfg_complete_autoA segs 3000%nat fi_cutpcs GW (fi_vcuts n UStopLe) [mkVNA (MIDx W UStopLe) 0 (SLit 0)] (JF n UStopLe true A Kc rho) Q tp).
  - apply JF_stable; [apply stopJ_stable_le | exact HKc].
  - intros m Hm. cbn [fi_vcuts In] in Hm.
    repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm.
  - exact ECert.
  - intros E rhoE [<-|[]]. cbn [vna_state]. eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    intros w Hw. destruct (fi_reabstract W A Kc rho tp w rhoE Hii Hw) as (rho2 & Hw2 & AG & VQ & RMO).
    exact (HC rho2 (conj AG (conj VQ RMO)) w Hw2).
  - left. reflexivity.
Qed.
End PerN.
End MI.
End F0A_minit.

