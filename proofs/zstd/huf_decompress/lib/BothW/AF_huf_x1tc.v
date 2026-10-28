(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface
     ADepot_iface ARep ALayout AHeapP AFake_iface AFake_arep AFake0k_iface AFake_arep0k AF_huf_tbl_iface3 AF_huf_rsc
     AH_huf_iface AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_x1tc () := "C46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission5BothW<AFake_arep0k<fake_flag_AIC5ARocqVerifyHarness?AgentSubmission5BothW<AFake_arep0k?fake_release_AIK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission5BothW<AFake_arep0kBstack_malloc_0k_AIK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive02C5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_rscBhuf_rstats_closedAC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_x1tAhuf_rdt_x1_proofAK46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums8positive01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C5ARocqVerifyHarness?AgentSubmission5BothW;AFake_iface5fflagC5ARocqVerifyHarness?AgentSubmission5BothW;AFake_iface9afake_rngK47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Inst.
  Variable DI : ADepotIface.
  Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
  Hypothesis HL : ahole_laws (AH DI AQ ASEC).
  Variable CI : list (Z * Z).
  Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P (AH DI AQ ASEC).
  Hypothesis EC : aci AI = CI.

  (* [comment removed for export] *)
  Theorem huf_rdt_x1_closedA : huf_rdt_stmtA2 AI afake_rng huf_dt_okA AHUF_RDT_X1.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_x1tc ()) ["CANSEC1"; "Inst"] "h07__arithh14__ffh28__varmaph35__witp;9p;7p;1p;2p;4p;3p;<p;8p-1p10000p4p710p8g000Gl9JTg001Kj7ITg002Rj1=Tg0032j19Tg003Rj1HTg0040j1CTg004Nj1>Tg0059j22Tg005\j13Tg006:j45Tg006ej2:Tg007Gj2GTg007aj2FTg008Mj3ETg008gj3BTg009Fj4ATg00:8j27Tg00:Tl<?Tg00;^j1@Tg00<=j14Tg00<bl<<Tg00=jj8DTg00?1j7;Tg00?Uj18Tf0R0#4#4p=0f1R1g00@:g00@YR2P2g00A9R2P0g00AYF;p=6%80#8p=1p,2rcR3p,2AIR4g00B9g00C5P3p,2DIR5p,2AQR6p,4ASECR7p,2CIR8p,5CI_OKR9P4p,1ER:p,2ECR;M9JP3P5P6P7p,2HLR<P4P:FIP3P5P6P7P<P8P9P4P:P;g00D5R=g00DTR>#=R?%9>R>g00E@R@#HRA%C@RB%>@RCP@g00E^RD,2@g00F<REg00FcRF#0#0#0#0#0#0#0#3RG,2@C5'61:C2R2P0f2RHg00GHRIg00GhRJ'G1F0H=EIJdAB@D1CAR1b1b2b317DGP0b0M<?P3P5P6P7P<P8P9P4P:P;%@=P?P>PAPBP@%3FRB,2@PE%1F#1#1#1#1#1#4#3RF,2@C5,6CP2P1b1b2b317BFP0b0M<<GDo"). Qed.
End Inst.
End CANSEC1.
