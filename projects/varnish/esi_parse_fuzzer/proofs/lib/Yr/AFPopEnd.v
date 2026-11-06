(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 ARtSb8o AMTac AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalz1i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalmys AMaldga AMalrrv ASecB1 ANodeA7 ANodl61 ATransp ATranspR AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRW2 ABudget ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1 APopG2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopP.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSb8o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalz1i.AMallocR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMaldga OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalrrv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRW2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp.APopCap OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5.APopG3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5.APopG4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopP.APopK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AInvWfp.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_3ti ARt_fpo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_png ARtSscs ARtSoqz ANodeA6 APopSA APopSB APopSC APopSD.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_3ti OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_srv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSB OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSD.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeH AFreeHc AFreeH4w AFreeH5e AFreeH5c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AFreeB1 AFreeB3 AFreeB1F ACoresk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFPopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFPopP APopCtx.

Module AFPopE.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 ARtSb8o AMTac AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalz1i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalmys AMaldga AMalrrv ASecB1 ANodeA7 ANodl61 ATransp ATranspR AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRW2 ABudget ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1 APopG2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopP.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSb8o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalz1i.AMallocR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMaldga OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalrrv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRW2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp.APopCap OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5.APopG3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5.APopG4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopP.APopK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AInvWfp.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_3ti ARt_fpo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_png ARtSscs ARtSoqz ANodeA6 APopSA APopSB APopSC APopSD.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_3ti OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_srv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSB OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSD.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeH AFreeHc AFreeH4w AFreeH5e AFreeH5c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AFreeB1 AFreeB3 AFreeB1F ACoresk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFPopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFPopP.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeHc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH4w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH5e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH5c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1F OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFPopP.AFPopK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFPopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@Q2; @Q5; @L1; @B3; @B1; @CE; @Q4; @B2; @R1; @H5; @H3; @CSR; @LJ; @SEP_tr; @Lt1; @B4; @Lt4; @Q6; @Lt2; @Q7; @SEP_ts; @Q10; @KL; @Q1; @Hi; @R6; @PU; @Hal; @P3; @Ha; @H1; @PN; @NEEDMAP; @X; @H; @U1; @F1; @Q9; @PF; @HI47; @D; @P6; @Hb; @CAP0; @P1; @P2; @Q3; @FAST; @LOSA; @S2; @AU1; @LK; @RBEq; @SAE; @CEILw; @H2; @SAHI; @CLO; @SOLO; @SOHI; @NR; @SEP_rn; @SEP_rf; @LL2; @PP3; @LL4; @LL1; @MR; @NOFIT; @R10; @PREF; @R8; @KS; @MXR; @PU4; @OLD; @L3; @NDE; @ER; @PHI; @PP6; @LBH; @L2; @RIE; @WL; @N0; @IHr; @H0; @QTB; @LENB; @LL3; @LL5; @LL6; @LL7; @AU2; @SPR; @PP1; @KB; @R9; @FIT; @U0; @Hj; @NEW; @EF; @KLz; @KLz__])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pasan).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kShadowGapBeg, kHighShadowMapSize,
                        kAuCap, kFreeArraySize, kUserMapSize, kFreeArrayMapSize in *.

(* [comment removed for export] *)
Lemma inside_pos : forall (W : list (Z * Z)) (k : nat) (lo hi a n : Z), nth_error W k = Some (lo, hi) -> lo <= a /\ a + n <= hi -> inside W a n.
Proof.
  induction W as [|[l h] W IH]; intros [|k] lo hi a n E H; cbn [nth_error] in E; try discriminate.
  - injection E as -> ->. left. exact H.
  - right. exact (IH k lo hi a n E H).
Qed.
Ltac inside_at k :=
  lazymatch goal with |- inside ?WW ?a ?n =>
    let e := eval cbv [nth_error WW] in (nth_error WW k) in
    lazymatch e with Some (?lo, ?hi) => refine (inside_pos WW k lo hi a n eq_refl _) end
  end.
Section FArm.
Context {Clg : Ceiling}.
  Variables (rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (md : Model) (A : AState) (p n0 stkobj lo hi : Z) (key : list Z).
  Hypothesis PRE : dealloc_core_pre rac spd (cl_tp LPA) m md A p n0 stkobj lo hi key.
  Hypothesis HL : as_live A p = Some n0.
  Hypothesis NQ : n0 <= 2^28.
  Hypothesis EMP : pk_chunks (a_cache A 24) = [].
  Hypothesis SHORT : Z.of_nat (length (rg_free (a_reg A 24))) < refill_count 24.
  Hypothesis SHAPE : a_qthread A = [] \/ (a_qthread A <> [] /\ Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) = kQuarantineBatchCount).
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned spd).
  #[warnings="-notation-for-abbreviation"] Local Notation sa := (bv_unsigned spd + -80 + 112).
  #[warnings="-notation-for-abbreviation"] Local Notation spaw := (Z_to_bv 64 (bv_unsigned spd + -80 + 112)).
  #[warnings="-notation-for-abbreviation"] Local Notation tp := (cl_tp LPA).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation ctx := (p_ctx (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation ri := (a_ri A).
  #[warnings="-notation-for-abbreviation"] Local Notation n0d := (p_nodes0 (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation f0d := (p_frames0 (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation r8 := ((n0 + 7) / 8).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (a_ri A + 128 * 24).
  #[warnings="-notation-for-abbreviation"] Local Notation C := (p_thr (a_pl A) + 208).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (p_thr (a_pl A) + 208 + 80 * 24).
  #[warnings="-notation-for-abbreviation"] Local Notation uG := (bv_unsigned spd + -80 + 112 + -128 + -48 + -32 + -128).
  #[warnings="-notation-for-abbreviation"] Local Notation rb := (region_beg (a_sb A) 24).
  #[warnings="-notation-for-abbreviation"] Local Notation rbs := (a_sb A + 24 * 4294967296).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (region_beg (a_sb A) 24 + kFreeArrayOffset).
  #[warnings="-notation-for-abbreviation"] Local Notation mu := (rg_mapped_user (a_reg A 24)).
  #[warnings="-notation-for-abbreviation"] Local Notation au := (rg_allocated_user (a_reg A 24)).
  #[warnings="-notation-for-abbreviation"] Local Notation mfa := (rg_mapped_fa (a_reg A 24)).
  #[warnings="-notation-for-abbreviation"] Local Notation nf := (Z.of_nat (length (rg_free (a_reg A 24)))).
  #[warnings="-notation-for-abbreviation"] Local Notation kk := (refill_count 24).
  #[warnings="-notation-for-abbreviation"] Local Notation size := (class_size 24).
  #[warnings="-notation-for-abbreviation"] Local Notation U := (pop_ums A 24).
  #[warnings="-notation-for-abbreviation"] Local Notation N := (pop_nc A 24).
  #[warnings="-notation-for-abbreviation"] Local Notation Fm := (pop_fam A 24).
  #[warnings="-notation-for-abbreviation"] Local Notation D' := (fst (depot_putC (a_depot A) key)).
  #[warnings="-notation-for-abbreviation"] Local Notation fid := (snd (depot_putC (a_depot A) key)).

  Let AI : @pa_ainv _ DepotRepL A m md. Proof. exact (proj1 PRE). Qed.
  Let W0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CR : 1 <= 24 <= 30. Proof. lia. Qed.
  Let N7R : 1 <= 7000 <= kMaxPrimaryUser. Proof. unfold kMaxPrimaryUser. lia. Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.
  Let MIv : mem_inv rsegs v. Proof. exact (proj1 (proj2 PRE)). Qed.
  (* [comment removed for export] *)
  Let PREF : alloc_ceiling <= lo /\ lo <= usp - 4096 /\ usp <= hi /\ hi <= 2^47 /\ usp mod 16 = 0 /\ bv_unsigned rac mod 2 = 0 /\
             stk rsegs v lo usp /\ mapped v usp (hi - usp) /\ usp <= stkobj /\ stkobj + 2064 <= hi.
  Proof.
    destruct PRE as (_ & _ & _ & _ & _ & CLO & LOSA & SAHI & HI47 & SPA & RAC2 & ST & SM & SOLO & SOHI & _). cbn [cl_segs LPA] in ST.
    exact (conj CLO (conj LOSA (conj SAHI (conj HI47 (conj SPA (conj RAC2 (conj ST (conj SM (conj SOLO SOHI))))))))).
  Qed.
  Let SAE : bv_unsigned spaw = sa.
  Proof. destruct PREF as (_ & _ & SAHI & HI47 & _). pose proof (zr_word spd) as X. unfold inr64 in X. apply unsigned_lit. lia. Qed.
  Let CEIL : alloc_ceiling <= sa - 1024. Proof. destruct PREF as (CLO & LOSA & _). lia. Qed.
  Let CEILw : alloc_ceiling <= bv_unsigned spaw - 1024. Proof. rewrite SAE. exact CEIL. Qed.
  Let EMP7 : pk_chunks (a_cache A (class_of 7000)) = []. Proof. rewrite class_of_7000. exact EMP. Qed.
  Let SHORT7 : Z.of_nat (length (rg_free (a_reg A (class_of 7000)))) < refill_count (class_of 7000). Proof. rewrite class_of_7000. exact SHORT. Qed.
  Let KS : Z.shiftr (max_count 24) 1 = kk. Proof. exact (proj1 (proj2 (proj2 (ar_k A 24 CR)))). Qed.

  #[warnings="-notation-for-abbreviation"] Local Notation CY := (carryF rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A p n0 stkobj key).
  #[warnings="-notation-for-abbreviation"] Local Notation RW := (regwF A).
  #[warnings="-notation-for-abbreviation"] Local Notation Wi := (fk_Wi spd A).
  #[warnings="-notation-for-abbreviation"] Local Notation Wfo := (fk_Wfo A p n0).
  #[warnings="-notation-for-abbreviation"] Local Notation LIN := (fk_lin rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation PLIN := (fk_plin rac spd m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation Wle := (fk_Wi_le spd A).
  #[warnings="-notation-for-abbreviation"] Local Notation Wmono := (fk_Wi_mono spd A).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_step := (carryF_step rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE).
  #[warnings="-notation-for-abbreviation"] Local Notation rw_step := (regwF_step rac spd A).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_statics := (fcy_statics rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_seal := (fcy_seal rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_na := (fcy_na rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_thr_mapped := (fcy_thr_mapped rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_tst := (fcy_tst rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_stm := (fcy_stm rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_mapped := (fcy_mapped rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A p n0 stkobj key).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_NN := (fcy_NN rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A p n0 stkobj key).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_fcells := (fcy_fcells rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_UMS := (fk_UMS rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_FAM := (fk_FAM rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_NC := (fk_NC rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_POS := (fk_POS rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_SHG := (fk_SHG rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_region := (fk_region rac spd m md A p n0 stkobj lo hi key PRE).
  #[warnings="-notation-for-abbreviation"] Local Notation f_regw_entry := (regwF_entry rac spd m md A p n0 stkobj lo hi key PRE).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition hp_post : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' : word) (junk0 pad scr : list byte) (ksc : list word) (w : mem),
      st = MS (mkR (wz refill_ret) (wz uG) gp tp t0' t1' t2' (wz R) (wz 0xb1d58) a0' (wz (C + 2560)) (wz 24) (wz (E + 16)) (wz kk) a5' a6' a7'
                   (wz (p + -16)) (wz 2305843009213693952) (wz (free_array_of sb 24)) (wz 1099511627776) (wz 1152921504607895551)
                   (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
               F (wz gfa_locked) fc None w (seg_rom rsegs)
      /\ CY junk0 pad scr ksc 0 0 0 w /\ RW nf mfa au mu w /\ stk rsegs w lo uG.

  #[using="PREF MIv CE N7R CR W0 AI SHAPE SHORT EMP NQ HL PRE hi md"] Lemma pop_head : forall (t0 t1 t2 a2 a3 a6 a7 t3 t4 t5 t6 : word),
    evt rsegs hp_post
        (MS (mkR rac spd gp tp t0 t1 t2 s0 s1 (wz 0xb1d58) (wz p) a2 a3 (wz stkobj) (wz 1) a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x36e88) fc None v (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a2 a3 a6 a7 t3 t4 t5 t6.
    destruct PREF as (CLO & LOSA & SAHI & HI47 & SPA0 & RAC2 & ST & SM & SOLO & SOHI).
    pose proof (conj W0 (ai_repr _ _ _ _ _ _ _ AI) : WF A /\ @arepr _ DepotRepL LPA AL_pasan [] A v) as AR.
    pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    (first [ pose proof ((free_li A p n0 HL)) as dR_1; dex1 dR_1 as li; destruct dR_1 as [LU LN] | pose proof ((free_li A p n0 HL)) as dR_1; dand3 dR_1 as li LU LN | destruct (free_li A p n0 HL) as (li & LU & LN) ]).
    destruct (free_n0 A m md p n0 AI HL) as [NR US]. unfold REQ_MAX in NR.
    (first [ pose proof ((AFreeB1.free_geom A m md p n0 AI HL)) as dR_2; dand4 dR_2 as PAL PLO PCE PHI | destruct (AFreeB1.free_geom A m md p n0 AI HL) as (PAL & PLO & PCE & PHI) ]).
    (first [ pose proof ((AFreeB1.free_HDR A m md p n0 AI HL)) as dR_3; dex2 dR_3 as b1 ido; dand6 dR_3 as B1R B1M3 B1M IDR HDR CTXID | pose proof ((AFreeB1.free_HDR A m md p n0 AI HL)) as dR_3; dand8 dR_3 as b1 ido B1R B1M3 B1M IDR HDR CTXID | destruct (AFreeB1.free_HDR A m md p n0 AI HL) as (b1 & ido & B1R & B1M3 & B1M & IDR & HDR & CTXID) ]).
    destruct (free_CTX0 A m md p n0 AI HL) as (old & CTX0).
    pose proof (free_SHC A m md p n0 AI HL) as SHC. pose proof (free_FCo A m md AI) as FCo.
    (first [ pose proof ((free_TST A m md AI)) as dR_4; dex2 dR_4 as fr fd; dand3 dR_4 as FRR FDR TST | pose proof ((free_TST A m md AI)) as dR_4; dand5 dR_4 as fr fd FRR FDR TST | destruct (free_TST A m md AI) as (fr & fd & FRR & FDR & TST) ]).
    pose proof (free_sep A m md p n0 AI HL) as SEPp. cbv zeta in SEPp. (first [ dand4 SEPp as SEP_pc SEP_pt SEP_pn SEP_pf | destruct SEPp as (SEP_pc & SEP_pt & SEP_pn & SEP_pf) ]).
    (first [ pose proof ((hit_sep A m md AI)) as dR_6; dand13 dR_6 as SEP_thr SEP_ctx SEP_tc SEP_n0 SEP_f0 SEP_n0t SEP_f0t SEP_n0c SEP_f0c DN01 DN02 DF01 DF02 | pose proof (hit_sep A m md AI) as (SEP_thr & SEP_ctx & SEP_tc & SEP_n0 & SEP_f0 & SEP_n0t & SEP_f0t & SEP_n0c & SEP_f0c & DN01 & DN02 & DF01 & DF02) ]).
    (first [ pose proof ((hit_place A m md AI)) as dR_7; dand7 dR_7 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]).
    (first [ pose proof ((hit_depot_wf A m md AI)) as dR_8; dand5 dR_8 as DND DLEN _ DKEY _ | pose proof (hit_depot_wf A m md AI) as (DND & DLEN & _ & DKEY & _) ]).
    pose proof (hit_DR A m md AI) as DR0. pose proof (hit_TC A m md AI) as TC.
    assert (TSDL : 0x5e8328 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000) by (unfold pa_tsd; lia).
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STO & TRW & KEYU & KR). cbn [cl_segs LPA] in STO, TRW.
    assert (KL : (1 <= length key <= 255)%nat /\ depot_total (a_depot A) + 256 < kStackStoreBlockFrames).
    { (first [ pose proof ((wfD A W0)) as dR_9; dand3 dR_9 as INC ND NN | destruct (wfD A W0) as (INC & ND & NN) ]). pose proof (wfP A W0) as PL. pose proof (wf_place_dkeys _ _ PL) as DK.
      (first [ dand3 DK as DK1 DK2 DK3 | destruct DK as (DK1 & DK2 & DK3) ]). clear PL.
      assert (INC' : incl (a_depot A) (p_dkeys (a_pl A))) by (intros k Hk; exact (proj1 (Forall_forall _ _) INC k Hk)).
      (first [ pose proof ((depot_universe_bounds _ _ DK1 DK3 ND INC')) as dR_11; dand3 dR_11 as L1 _ L3 | pose proof (depot_universe_bounds _ _ DK1 DK3 ND INC') as (L1 & _ & L3) ]).
      split; [exact (proj1 (Forall_forall _ _) DK1 key KEYU)| unfold kStackStoreBlockFrames; clear - L1 L3; lia]. }
    destruct KL as [KL DTOT].
    assert (STOR : usp <= stkobj /\ stkobj + 2064 <= 2^47) by (clear - SOLO SOHI HI47; lia).
    assert (TPE : cl_tp LPA = wz TP) by reflexivity.
    pose proof (Z_div_mod_eq_full (n0 + 7) 8) as NDE. pose proof (Z.mod_pos_bound (n0 + 7) 8 ltac:(lia)) as ER.
    assert (R8 : 8 * r8 - 8 < n0 <= 8 * r8) by (clear - NDE ER; lia).
    assert (NR' : 1 <= n0 < 2^32) by (clear - NR; lia).
    assert (PHI' : p + 8 * r8 <= alloc_ceiling) by (clear - PHI; lia).
    assert (LO : alloc_ceiling <= lo /\ lo <= usp - 1024) by (clear - CLO LOSA; lia).
    assert (SPH : usp <= 2^47) by (clear - SAHI HI47; lia).
    (first [ pose proof (PLIN) as dR_12; dand3 dR_12 as (PP1 & PP2 & PP3 & PP4) (PP5 & PP6 & PP7 & PP8) _ | pose proof PLIN as ((PP1 & PP2 & PP3 & PP4) & (PP5 & PP6 & PP7 & PP8) & _) ]).
    assert (PNB : 0x60a000 <= p + -16) by exact PP1.
    (first [ pose proof ((f24_sep A m md AI)) as dR_13; dand8 dR_13 as SEP_tr SEP_rs SEP_rc SEP_rn SEP_rf SEP_ts SEP_ns SEP_fs | pose proof (f24_sep A m md AI) as (SEP_tr & SEP_rs & SEP_rc & SEP_rn & SEP_rf & SEP_ts & SEP_ns & SEP_fs) ]).
    (first [ pose proof ((f24_ri A m md AI)) as dR_14; dand7 dR_14 as RIE RILO RIHI RIAL SBAL SBLO SBHI | pose proof (f24_ri A m md AI) as (RIE & RILO & RIHI & RIAL & SBAL & SBLO & SBHI) ]).
    assert (SEP_rp : apart ri 4096 (p + -16) (8 * r8 + 16)) by (unfold apart; clear - PP6; lia).
    destruct (f24_STA A m md AI) as [statv STA].
    pose proof (f24_CRI A m md AI) as CRI. pose proof (f24_CSB A m md AI) as CSB.
    pose proof f_region as (MXc & _).
    pose proof (free_QC A m md AI) as QC.
    (* [comment removed for export] *)
    set (qt := a_qthread A) in *. set (bl := last qt (BA 0 [])) in *.
    assert (LBX : qt <> [] ->
              (kHighMemBeg <= qc_last A qt /\ qc_last A qt + 8192 <= alloc_ceiling /\ apart (qc_last A qt) 8192 thr 4096 /\ apart (qc_last A qt) 8192 (p + -16) (8 * r8 + 16)
               /\ apart (qc_last A qt) 8192 n0d kDepotNodesBlock /\ apart (qc_last A qt) 8192 f0d kStackStoreBlockBytes /\ qc_last A qt + 8192 <= ri) /\
              rw_cells rsegs v (qc_last A qt) [C8 (wz 0); C8 (wz (batch_bytes bl)); C8 (wz 1021)]).
    { intros QNE. destruct SHAPE as [QTE|[_ FULL]]; [exfalso; exact (QNE QTE)|].
      assert (EQT : qt = removelast qt ++ [bl]) by (symmetry; apply removelast_last_app; exact QNE).
      pose proof (free_LB A m md AI (removelast qt) bl EQT) as LBF. cbv zeta in LBF. (first [ dand7 LBF as LB _ LBM CNT LBL LBH LB16 | destruct LBF as (LB & _ & LBM & CNT & LBL & LBH & LB16) ]).
      assert (QL : qc_last A qt = batch_addr sb bl) by (unfold qc_last; subst bl; destruct qt; [congruence| reflexivity]). rewrite QL.
      assert (INbl : In bl (qt ++ a_qglobal A)) by (apply in_or_app; left; rewrite EQT; apply in_or_app; right; left; reflexivity).
      pose proof (ATransp.batch_carved A v AR bl INbl) as CBL.
      pose proof (AFreeB3.KN A v p n0 li AR LU LN) as KNp. pose proof (ATransp.known_carved A v AR _ _ KNp) as CVp.
      pose proof (AFreeB3.GEO A v p n0 li spd AR LU LN) as G.
      split.
      - split; [exact LBL|]. split; [clear - LBH; unfold kQuarantineBatchBytes in LBH; lia|].
        split. { pose proof (ATransp.carved_apart_thr A v AR _ CBL) as D. rewrite (proj1 (AFreeB3.c24_range A (ba_idx bl))), (proj2 (AFreeB3.c24_range A (ba_idx bl))) in D. clear - D. unfold apart, AMallocA.apart, batch_addr, kQuarantineBatchBytes in *. lia. }
        split. { pose proof (ATransp.carved_disjoint A v AR _ _ CBL CVp ltac:(intros E0; exact (ATransp.live_not_batch A v AR p li bl LU INbl (eq_sym E0)))) as D.
                 rewrite (proj1 (AFreeB3.c24_range A (ba_idx bl))), (proj2 (AFreeB3.c24_range A (ba_idx bl))) in D. (first [ dand5 G as _ _ L1 L2 _ | destruct G as (_ & _ & L1 & L2 & _) ]). clear - D L1 L2. unfold apart, AMallocA.apart, batch_addr, kQuarantineBatchBytes in *. lia. }
        split. { pose proof (ATransp.carved_apart_n0 A v AR _ CBL) as D. rewrite (proj1 (AFreeB3.c24_range A (ba_idx bl))), (proj2 (AFreeB3.c24_range A (ba_idx bl))) in D. clear - D. unfold apart, AMallocA.apart, batch_addr, kQuarantineBatchBytes in *. lia. }
        split. { pose proof (ATransp.carved_apart_f0 A v AR _ CBL) as D. rewrite (proj1 (AFreeB3.c24_range A (ba_idx bl))), (proj2 (AFreeB3.c24_range A (ba_idx bl))) in D. clear - D. unfold apart, AMallocA.apart, batch_addr, kQuarantineBatchBytes in *. lia. }
        { pose proof (ATransp.carved_prim_where A v AR _ _ CBL) as WL. rewrite class_size_24 in WL. clear - WL RIE. unfold batch_addr, kQuarantineBatchBytes, region_beg in *. kung_all. lia. }
      - unfold kQuarantineBatchCount in FULL. fold qt in FULL. fold bl in FULL. rewrite FULL in LB. exact LB. }
    assert (NB0x : Z.of_nat (length qt) <> 0 <-> qt <> []) by (generalize qt; intros q; destruct q; cbn [length]; split; intros X; [exfalso; apply X; reflexivity| exfalso; apply X; reflexivity| discriminate| lia]).
    assert (NBR : 0 <= Z.of_nat (length qt) < 2^63).
    { (first [ pose proof ((wfQ A W0)) as dR_17; dand5 dR_17 as _ _ _ QTB _ | pose proof (wfQ A W0) as (_ & _ & _ & QTB & _) ]). fold qt in QTB. unfold kQuarantineCacheSize in QTB.
      assert (QWF : forall e, In e (q_entries (qt ++ a_qglobal A)) -> 0 <= qe_n e) by (intros e He; destruct (ATransp.qentry_wf A v AR e He) as [N0 _]; lia).
      assert (QBall : forall bs, (forall e, In e (q_entries bs) -> 0 <= qe_n e) -> Z.of_nat (length bs) * kQuarantineBatchBytes <= q_bytes bs).
      { clear. intros bs QW. induction bs as [|b0 r IH]; [cbn; lia|]. rewrite q_bytes_cons, batch_bytes_ebytes. cbn [length]. rewrite Nat2Z.inj_succ.
        assert (IHr : Z.of_nat (length r) * kQuarantineBatchBytes <= q_bytes r) by (apply IH; intros e He; apply QW; rewrite q_entries_cons; apply in_or_app; right; exact He).
        assert (EW : forall e, In e (ba_entries b0) -> 0 <= qe_n e) by (intros e He; apply QW; rewrite q_entries_cons; apply in_or_app; left; exact He).
        assert (0 <= ebytes (ba_entries b0)); [| lia].
        clear - EW. induction (ba_entries b0) as [|e es IHe]; [cbn; lia|].
        rewrite ebytes_cons. unfold qe_bytes. pose proof (user_size_pos (qe_n e) ltac:(apply EW; left; reflexivity)).
        assert (0 <= ebytes es) by (apply IHe; intros e' He'; apply EW; right; exact He'). lia. }
      assert (LENB : Z.of_nat (length qt) * kQuarantineBatchBytes <= q_bytes qt).
      { apply QBall. intros e He. apply QWF. unfold q_entries in He |- *. rewrite flat_map_app. apply in_or_app. left. exact He. }
      clear - LENB QTB. unfold kQuarantineBatchBytes in *. lia. }
    (first [ pose proof (LIN) as dR_18; dand6 dR_18 as L1 L2 (Lt1 & Lt2 & Lt3 & Lt4) (B1 & B2 & B3 & B4 & B5) (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) (H1 & H2 & H3 & H4 & H5) | pose proof LIN as (L1 & L2 & (Lt1 & Lt2 & Lt3 & Lt4) & (B1 & B2 & B3 & B4 & B5) & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) & (H1 & H2 & H3 & H4 & H5)) ]).
    (* [comment removed for export] *)
    assert (HSUB : forall LW, (LW = [] \/ (a_cache_inited A = false /\ LW = [(C + 80, C + 2560)])) ->
              sub_fp (free_cprefix_W spd thr p r8 n0d f0d ++ [(usp + -80 - 224, usp + -80)] ++ LW ++ [(ri + 128 * 24, ri + 128 * 24 + 8)]) (Wi 0 0 0 ++ Wfo) /\
              disjoint_from (free_cprefix_W spd thr p r8 n0d f0d ++ [(usp + -80 - 224, usp + -80)] ++ LW ++ [(ri + 128 * 24, ri + 128 * 24 + 8)]) (R + 16) 64).
    { (first [ pose proof (PLIN) as dR_19; dand6 dR_19 as (P1 & P2 & P3 & P4) (P5 & P6 & P7 & P8) (S1 & S2 & S3) ((N1 & N2 & N3 & N4) & N5 & N6 & N7) ((F1 & F2 & F3 & F4) & F5 & F6 & F7) _ | pose proof PLIN as ((P1 & P2 & P3 & P4) & (P5 & P6 & P7 & P8) & (S1 & S2 & S3) & ((N1 & N2 & N3 & N4) & N5 & N6 & N7) & ((F1 & F2 & F3 & F4) & F5 & F6 & F7) & _) ]).
      unfold apart, AMallocA.apart, kDepotNodesBlock, kStackStoreBlockBytes in SEP_tr, SEP_rn, SEP_rf.
      intros LW [->|[CI ->]]; (split; [apply sub_fp_all_inside; unfold free_cprefix_W, fk_Wi, fk_Wfo, fpop_Wq, fpop_Wfo; cbn [app]; rewrite ?CI; cbn [app];
                                         (lazymatch goal with |- all_inside ?W' _ => let WW := fresh "WW" in set (WW := W') end); cbn [all_inside];
                                         OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; right;
                                         (lazymatch goal with WW0 := _ : list (Z * Z) |- _ => clear - WW0 end);
                                         first [ inside_at 0%nat; lia | inside_at 1%nat; lia | inside_at 2%nat; lia | inside_at 3%nat; lia | inside_at 4%nat; lia | inside_at 5%nat; lia
                                               | inside_at 6%nat; lia | inside_at 7%nat; lia | inside_at 8%nat; lia | inside_at 9%nat; lia | inside_at 10%nat; lia | inside_at 11%nat; lia
                                               | inside_at 12%nat; lia | inside_at 13%nat; lia | inside_at 14%nat; lia | inside_at 15%nat; lia | inside_at 16%nat; lia | inside_at 17%nat; lia
                                               | inside_at 18%nat; lia | inside_at 19%nat; lia | inside_at 20%nat; lia | inside_at 21%nat; lia | inside_at 22%nat; lia | inside_at 23%nat; lia
                                               | inside_at 24%nat; lia | inside_at 25%nat; lia | inside_at 26%nat; lia | inside_at 27%nat; lia | inside_at 28%nat; lia | inside_at 29%nat; lia ]
                                       | unfold free_cprefix_W; cbn [app disjoint_from]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I;
                                         first [ solve [clear - CE L1 L2 B1 B2 B3; lia] | solve [clear - P6 P3 B3; lia] | solve [clear - SEP_tr B3 Lt1 Lt2; lia]
                                               | solve [clear - B1 B3; lia] | solve [clear - SEP_rn B3; lia] | solve [clear - SEP_rf B3; lia] | solve [clear - S2 B1 B3; lia] ] ]). }
    destruct (a_cache_inited A) eqn:CI.
    - (* [comment removed for export] *)
      (first [ pose proof ((f24_PC A m md AI CI EMP)) as dR_20; dex1 dR_20 as ks; destruct dR_20 as [LKS PC24] | pose proof ((f24_PC A m md AI CI EMP)) as dR_20; dand3 dR_20 as ks LKS PC24 | destruct (f24_PC A m md AI CI EMP) as (ks & LKS & PC24) ]).
      pose proof (free_cpop_head rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc v
                    lo p n0 b1 pa_tsd ctx thr r8 n0d f0d fr fd stkobj (a_depot A) key old (shpat n0)
                    MIv ST LO SPH RAC2 TPE PAL PLO PNB PHI' NR' NQ R8 B1R B1M3 HDR CTX0 SHC FCo
                    (hit_PCo A m md AI) TC (hit_TH0 A m md AI) (hit_CT8 A m md AI) TSDL
                    TST FRR FDR DR0 DND DLEN DTOT (conj DN01 DN02) (conj DF01 DF02) STO TRW STOR KL KR SEP_pc SEP_pt SEP_pn SEP_pf SEP_n0t SEP_f0t SEP_n0c SEP_f0c SEP_tc
                    sb ri SBLO SBHI RILO RIHI RIAL SEP_tr SEP_ts SEP_rs SEP_rp SEP_rn SEP_rf
                    (Z.of_nat (length qt)) (qc_first A qt) (qc_last A qt) (q_bytes qt) 0 (batch_bytes bl) ks statv THRA LKS NBR) as EV.
      specialize (EV ltac:(intros NZ; (first [ pose proof ((proj1 (LBX (proj1 NB0x NZ)))) as dR_21; dand7 dR_21 as Y1 Y2 Y3 Y4 Y5 Y6 _ | destruct (proj1 (LBX (proj1 NB0x NZ))) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & _) ]); exact (conj Y1 (conj Y2 (conj Y3 (conj Y4 (conj Y5 Y6)))))) CSB CRI QC ltac:(intros NZ; exact (proj2 (LBX (proj1 NB0x NZ)))) PC24 STA MXc).
      eapply evt_mono; [exact EV|]. intros st PO. unfold free_cpop_head_post in PO. cbv zeta in PO.
      (first [ dex15 PO as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' scr pad rpad w; dand18 PO as -> MU WM MI' ST' PFR EF RF GF MX' TST' HDR' CTX' SHD' DR' QC' PC' STA' | dand33 PO as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' scr pad rpad w -> MU WM MI' ST' PFR EF RF GF MX' TST' HDR' CTX' SHD' DR' QC' PC' STA' | destruct PO as (t0' & t1' & t2' & a0' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & scr & pad & rpad & w & -> & MU & WM & MI' & ST' & PFR & EF & RF & GF & MX' & TST' & HDR' & CTX' & SHD' & DR' & QC' & PC' & STA') ]).
      destruct (HSUB [] (or_introl eq_refl)) as (HS1 & HS2). unfold free_cpop_head_W in MU. cbn [app] in HS1, HS2.
      change (Z.shiftr 2 1) with kk.
      first [ hotw_ex16 t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' pad rpad scr ks w | exists t0', t1', t2', a0', a5', a6', a7', t3', t4', t5', t6', pad, rpad, scr, ks, w ]. split; [reflexivity|].
      split; [| split; [exact (rw_step _ _ _ _ _ v w f_regw_entry MU WM HS2)| exact ST']].
      unfold carryF. split; [exact (munch_weaken _ _ _ _ HS1 MU)|]. split; [exact WM|]. split; [exact MI'|].
      split; [exact PFR|]. split; [exact EF|]. split; [exact RF|]. split; [exact GF|]. split; [exact MX'|]. split; [exact LKS|].
      split; [exact PC'|]. split; [intros X; rewrite CI in X; discriminate X|].
      exists w. split; [apply munch_refl|]. split; [apply wmono_refl|].
      first [ hotw_ex6 b1 fr fd 0 (batch_bytes bl) statv | exists b1, fr, fd, 0, (batch_bytes bl), statv ]. split; [exact (conj B1R (conj B1M3 (conj FRR FDR)))|]. split; [exact HDR|]. split; [exact TST|].
      split; [exact TST'|]. split; [exact HDR'|]. split; [exact CTX'|]. split; [exact SHD'|]. split; [exact DR'|]. split; [exact QC'|].
      split; [| exact STA']. intros QNE. specialize (LBX QNE). destruct LBX as ((LL1 & LL2 & LL3 & LL4 & LL5 & LL6 & LL7) & LBC).
      eapply rw_cells_transport; [exact LBC| exact MU| exact WM|]. subst bl qt.
      unfold free_cprefix_W. cbn [app disjoint_from cells_size csize Nat.add]. unfold apart, AMallocA.apart, kDepotNodesBlock, kStackStoreBlockBytes, kHighMemBeg in *.
      (first [ pose proof (PLIN) as dR_23; dand4 dR_23 as _ _ (S1 & S2 & S3) _ | pose proof PLIN as (_ & _ & (S1 & S2 & S3) & _) ]).
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I;
        first [ solve [clear - LL1 LL2 CE L1 L2; lia] | solve [clear - LL4 PP3; lia] | solve [clear - LL7; lia] | solve [clear - LL3; lia] | solve [clear - LL1; lia] | solve [clear - LL5; lia] | solve [clear - LL6; lia]
              | solve [clear - LL1 S2; lia] | solve [clear - LL1 LL2 B1 B3; lia] ].
    - (* [comment removed for export] *)
      assert (QTE : qt = []).
      { destruct SHAPE as [X|[QNE _]]; [exact X|]. exfalso.
        destruct qt as [|b r] eqn:EQ; [congruence|]. assert (INb : In b (a_qthread A)) by (fold qt; rewrite EQ; left; reflexivity).
        destruct (wfQ A W0) as (WQ1 & _). pose proof (proj1 (Forall_forall _ _) WQ1 b INb) as WB. unfold wf_batch_ in WB. (first [ dand3 WB as _ KB _ | destruct WB as (_ & KB & _) ]).
        (first [ pose proof ((wfR A W0)) as dR_25; dand3 dR_25 as WR _ R3 | destruct (wfR A W0) as (WR & _ & R3) ]). assert (X : a_cache_inited A = true); [| rewrite CI in X; discriminate X].
        apply R3. exists kQuarantineBatchClass. split; [unfold kQuarantineBatchClass; lia|].
        destruct (WR kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia)) as (BB1 & _). destruct BB1 as [[AU1 AU2] _].
        unfold carved_count_ in KB. rewrite class_size_24 in KB. unfold kQuarantineBatchBytes in KB. intros E0. rewrite E0 in AU2.
        assert (rg_allocated_user (a_reg A kQuarantineBatchClass) / 8192 <= 0) by (apply Z.div_le_upper_bound; lia). lia. }
      pose proof (free_cpop_head0 rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc v
                    lo p n0 b1 pa_tsd ctx thr r8 n0d f0d fr fd stkobj (a_depot A) key old (shpat n0)
                    MIv ST LO SPH RAC2 TPE PAL PLO PNB PHI' NR' NQ R8 B1R B1M3 HDR CTX0 SHC FCo
                    (hit_PCo A m md AI) TC (hit_TH0 A m md AI) (hit_CT8 A m md AI) TSDL
                    TST FRR FDR DR0 DND DLEN DTOT (conj DN01 DN02) (conj DF01 DF02) STO TRW STOR KL KR SEP_pc SEP_pt SEP_pn SEP_pf SEP_n0t SEP_f0t SEP_n0c SEP_f0c SEP_tc
                    sb ri SBLO SBHI RILO RIHI RIAL SEP_tr SEP_ts SEP_rs SEP_rp SEP_rn SEP_rf
                    (Z.of_nat (length qt)) (qc_first A qt) (qc_last A qt) (q_bytes qt) 0 (batch_bytes bl) (fun _ => 0) (fun _ => 0) (fun _ => 0) (pk_ks0 A m) statv THRA NBR) as EV.
      specialize (EV ltac:(intros NZ; (first [ pose proof ((proj1 (LBX (proj1 NB0x NZ)))) as dR_26; dand7 dR_26 as Y1 Y2 Y3 Y4 Y5 Y6 _ | destruct (proj1 (LBX (proj1 NB0x NZ))) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & _) ]); exact (conj Y1 (conj Y2 (conj Y3 (conj Y4 (conj Y5 Y6)))))) CSB CRI QC ltac:(intros NZ; exact (proj2 (LBX (proj1 NB0x NZ))))
                     ltac:(intros i Hi; destruct (pk_lines0 A m md AI CI i Hi) as (LK & RWi); cbv beta; split; [lia|]; split; [lia|]; split; [lia|]; split; [exact LK| exact RWi]) eq_refl eq_refl STA MXc).
      eapply evt_mono; [exact EV|]. intros st PO. unfold free_cpop_head0_post in PO. cbv zeta in PO.
      (first [ dex15 PO as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' scr pad rpad w; dand18 PO as -> MU WM MI' ST' PFR EF RF GF MX' TST' HDR' CTX' SHD' DR' QC' STA' LP | dand33 PO as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' scr pad rpad w -> MU WM MI' ST' PFR EF RF GF MX' TST' HDR' CTX' SHD' DR' QC' STA' LP | destruct PO as (t0' & t1' & t2' & a0' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & scr & pad & rpad & w & -> & MU & WM & MI' & ST' & PFR & EF & RF & GF & MX' & TST' & HDR' & CTX' & SHD' & DR' & QC' & STA' & LP) ]).
      destruct (HSUB [(C + 80, C + 2560)] (or_intror (conj eq_refl eq_refl))) as (HS1 & HS2). unfold free_cpop_head0_W in MU. cbn [app] in HS1, HS2.
      change (Z.shiftr 2 1) with kk.
      first [ hotw_ex16 t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' pad rpad scr (pk_ks0 A m 24) w | exists t0', t1', t2', a0', a5', a6', a7', t3', t4', t5', t6', pad, rpad, scr, (pk_ks0 A m 24), w ]. split; [reflexivity|].
      split; [| split; [exact (rw_step _ _ _ _ _ v w f_regw_entry MU WM HS2)| exact ST']].
      unfold carryF. split; [exact (munch_weaken _ _ _ _ HS1 MU)|]. split; [exact WM|]. split; [exact MI'|].
      split; [exact PFR|]. split; [exact EF|]. split; [exact RF|]. split; [exact GF|]. split; [exact MX'|].
      split; [exact (proj1 (pk_lines0 A m md AI CI 24 ltac:(lia)))|].
      split; [exact (LP 24 ltac:(lia))|].
      split; [intros _ i Hi NE; exists (pk_ks0 A m i); split; [exact (proj1 (pk_lines0 A m md AI CI i Hi))| exact (LP i Hi)]|].
      exists w. split; [apply munch_refl|]. split; [apply wmono_refl|].
      first [ hotw_ex6 b1 fr fd 0 (batch_bytes bl) statv | exists b1, fr, fd, 0, (batch_bytes bl), statv ]. split; [exact (conj B1R (conj B1M3 (conj FRR FDR)))|]. split; [exact HDR|]. split; [exact TST|].
      split; [exact TST'|]. split; [exact HDR'|]. split; [exact CTX'|]. split; [exact SHD'|]. split; [exact DR'|]. split; [exact QC'|].
      split; [| exact STA']. intros QNE. exfalso. exact (QNE QTE).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac lin_open :=
    let L := fresh "L" in pose proof LIN as L;
    destruct L as (L1 & L2 & (Lt1 & Lt2 & Lt3 & Lt4) & (B1 & B2 & B3 & B4 & B5) & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) & (H1 & H2 & H3 & H4 & H5)).
  Tactic Notation "cv" constr(k) := split; [right; (let kn := lazymatch type of k with Z => eval cbv in (Z.to_nat k) | _ => k end in inside_at kn); lia|].
  Ltac sub_open := apply sub_fp_all_inside; unfold fk_Wi, fpop_Wq, free_array_of, kFreeArrayOffset, off_th_stats in *; cbn [app]; destruct (a_cache_inited A); (lazymatch goal with |- all_inside ?W' _ => let WW := fresh "WW" in set (WW := W') end); cbn [all_inside app].
  Ltac dj_tac := unfold fk_Wi, fpop_Wq, free_array_of, kFreeArrayOffset, off_th_stats in *; cbn [disjoint_from app]; try (destruct (a_cache_inited A));
                 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; lia.

  (* [comment removed for export] *)
  #[using="PREF CE SHORT EMP PRE key hi lo stkobj n0 p md m rac Clg"] Lemma pk_stackW : forall a b ums fam nc, sa - 1024 <= a -> b <= uG ->
    sub_fp [(a, b)] (Wi ums fam nc) /\ disjoint_from [(a, b)] (sa - 336) 336 /\ disjoint_from [(a, b)] R 8 /\
    disjoint_from [(a, b)] (thr + 288) 2480 /\ disjoint_from [(a, b)] (R + 16) 64.
  Proof. intros a b ums fam nc Ha Hb. lin_open. split; [sub_open; (cv 0; exact I)|]. split; [dj_tac|]. split; [dj_tac|]. split; dj_tac. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation FRPc a0h := (pop_frame (wz kk) (wz (E + 16)) (wz (free_array_of sb 24)) (wz 2305843009213693952) a0h (wz 0xb1d58) (wz R) (wz gfa_popret)).

  Definition pm1_post (junk0 pad scr : list byte) (ksc : list word) (a0h : word) : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (scrM : list byte) (w' : mem),
      st = MSsvc (mkR (wz mapfixed_resume) (wz (uG + -64 + -128)) gp tp t0' t1' t2' (wz U) (wz 1) (wz (rbs + mu)) (wz U) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz (rbs + mu)) (wz pop_name) (wz PSC) (wz size) (wz 0xb1d58) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
                 F (wz mmap_ecall_pc) (wz 222) fc None w' (seg_rom rsegs)
      /\ CY junk0 pad scr ksc 0 0 0 w' /\ RW nf mfa au mu w' /\ stk rsegs w' lo (uG + -64 + -128)
      /\ rw_cells rsegs w' (uG + -64) (FRPc a0h)
      /\ rw_cells rsegs w' (uG + -64 + -128) (mapcb_frame scrM (wz (rbs + mu)) (wz U) (wz rbs) (rbs + mu) U (wz (C + 2560)) (wz R) (wz pop_mapret)).

  (* [comment removed for export] *)
  #[using="PREF CR AI SHORT EMP PRE key hi stkobj n0 p md m rac"] Lemma seg_pre :
    (alloc_ceiling <= lo /\ lo <= sa - 1024) /\ sa mod 16 = 0 /\ sa <= 2^47 /\
    (2 <= max_count 24 <= 16 /\ max_count 24 = 2 * kk) /\ (aobj thr 4096 /\ thr + 4096 <= alloc_ceiling) /\ thr mod 16 = 0 /\
    (kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling) /\ ri mod 128 = 0 /\ (kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling) /\ sb mod 4096 = 0 /\
    (thr + 4096 <= ri \/ ri + 4096 <= thr) /\ (ri + 4096 <= sb \/ sb + 2^37 <= ri) /\ (thr + 4096 <= sb \/ sb + 2^37 <= thr) /\
    0 <= nf < kk /\ bv_unsigned tp = 0x5e83d8 /\ (0x5e8328 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000).
  Proof.
    destruct PREF as (CLO & LOSA & SAHI & HI47 & SPA0 & RAC2 & ST & SM & SOLO & SOHI).
    assert (SPA : sa mod 16 = 0) by (replace sa with (usp + 2 * 16) by lia; rewrite Z_mod_plus_full; exact SPA0).
    (first [ pose proof ((ar_k A 24 CR)) as dR_28; dand4 dR_28 as MK2 KR2 _ MR | pose proof (ar_k A 24 CR) as (MK2 & KR2 & _ & MR) ]).
    (first [ pose proof ((hit_place A m md AI)) as dR_29; dand4 dR_29 as TH1 TH2 THRA _ | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & _) ]).
    pose proof (hit_sep A m md AI) as (SEP_thr & _).
    (first [ pose proof ((ref_sep A m md 7000 AI)) as dR_30; dand3 dR_30 as SEP_tr SEP_rs _ | pose proof (ref_sep A m md 7000 AI) as (SEP_tr & SEP_rs & _) ]).
    (first [ pose proof ((ref_ri A m md 7000 AI)) as dR_31; dand7 dR_31 as RIE RIL RIH RIAL SBAL _ _ | pose proof (ref_ri A m md 7000 AI) as (RIE & RIL & RIH & RIAL & SBAL & _ & _) ]).
    lin_open. unfold apart in *. unfold kHighMemBeg.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; try lia.
    - cbn [cl_tp LPA]. rewrite unsigned_lit by lia. reflexivity.
    - unfold pa_tsd. lia.
    - unfold pa_tsd. lia.
  Qed.

  #[using="KS PREF CE CR W0 AI SHORT EMP NQ HL PRE hi md"] Lemma pop_A_map : forall (t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 : word) (junk0 pad scr : list byte) (ksc : list word) (w : mem),
    mu < au + (kk - nf) * size ->
    CY junk0 pad scr ksc 0 0 0 w -> RW nf mfa au mu w -> stk rsegs w lo uG ->
    evt rsegs (pm1_post junk0 pad scr ksc a0)
        (MS (mkR (wz refill_ret) (wz uG) gp tp t0 t1 t2 (wz R) (wz 0xb1d58) a0 (wz (C + 2560)) (wz 24) (wz (E + 16)) (wz kk) a5 a6 a7
                 (wz (p + -16)) (wz 2305843009213693952) (wz (free_array_of sb 24)) (wz 1099511627776) (wz 1152921504607895551)
                 (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3 t4 t5 t6)
            F (wz gfa_locked) fc None w (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 junk0 pad scr ksc w NOFIT CYw RWw STw.
    (first [ pose proof (seg_pre) as dR_32; dand16 dR_32 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof seg_pre as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    (first [ pose proof ((ar_reg A 24 W0 CR)) as dR_33; dand10 dR_33 as (R1 & R2) R3 R4 R5 R6 R7 R8 R9 R10 R11 | pose proof (ar_reg A 24 W0 CR) as ((R1 & R2) & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) ]). (* [comment removed for export] *)
    assert (CAP0 : mu <= 3682891136 /\ au <= 3615782272 /\ mfa <= 469762048).
    { pose proof (ar_csr 24 CR) as CSR0. pose proof (Z.div_le_compat_l au 32 size ltac:(hot_lia_full) ltac:(hot_lia_full)) as Q1. pose proof (Z.mul_div_le au 32 ltac:(hot_lia_full)) as Q2.
      clear - R1 R2 R9 R10 CSR0 Q1 Q2. unfold kAuCap, kMaxSize in *. hot_lia_full. }
    assert (EU : U = round_up (au + (kk - nf) * size - mu) kUserMap) by (destruct (ar_ums_cases A 24) as [[_ X]|[X _]]; [lia| exact X]).
    (first [ pose proof ((cy_statics _ _ _ _ _ _ _ w CYw (Wle 0 0 0 ltac:(pose proof f_UMS; lia) ltac:(pose proof f_FAM; lia) ltac:(pose proof f_NC; lia)))) as dR_34; dand8 dR_34 as PCo TC CSB CREL CPMH CCF2 CCF144 MRN | pose proof (cy_statics _ _ _ _ _ _ _ w CYw (Wle 0 0 0 ltac:(pose proof f_UMS; lia) ltac:(pose proof f_FAM; lia) ltac:(pose proof f_NC; lia)))
      as (PCo & TC & CSB & CREL & CPMH & CCF2 & CCF144 & MRN) ]).
    (first [ dand13 PCo as _ CCF1 _ _ _ _ _ _ _ _ _ CPSC1 CPSC2 | destruct PCo as (_ & CCF1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CPSC1 & CPSC2) ]).
    (first [ pose proof (CYw) as dR_36; dand4 dR_36 as MUw WMw MIw _ | pose proof CYw as (MUw & WMw & MIw & _) ]). (first [ dand7 RWw as RNF RMFA RAU R40 RMU RMM REX | destruct RWw as (RNF & RMFA & RAU & R40 & RMU & RMM & REX) ]).
    pose proof (pop_sA_map gp tp t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 F fc w (wz (p + -16)) s10 s11 sa lo thr 24 (max_count 24) sb ri nf au mu) as EV.
    unfold pop_sA_map_post in EV. cbv zeta in EV. rewrite !KS in EV. rewrite <- !EU in EV.
    specialize (EV MIw STw LO SPH CR MXR THR RIR SBR SBAL NF ltac:(unfold kUserMap; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) ltac:(lia)
                   CSB CREL CPMH CPSC1 CPSC2 CCF1 CCF2 RNF RAU RMU RMM NOFIT).
    eapply evt_mono; [exact EV|]. (intros st; (first [ intro dR_100; dex10 dR_100 as t0' t1' t2' a6' t3' t4' t5' t6' scrM w'; dand7 dR_100 as -> MU WM MI' ST' FRP FRM | intro dR_100; dand17 dR_100 as t0' t1' t2' a6' t3' t4' t5' t6' scrM w' -> MU WM MI' ST' FRP FRM | intros (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & scrM & w' & -> & MU & WM & MI' & ST' & FRP & FRM) ])).
    (first [ pose proof ((pk_stackW (uG - 464) uG 0 0 0 ltac:(lia) ltac:(lia))) as dR_38; dand5 dR_38 as S1 S2 S3 S4 S5 | destruct (pk_stackW (uG - 464) uG 0 0 0 ltac:(lia) ltac:(lia)) as (S1 & S2 & S3 & S4 & S5) ]).
    first [ hotw_ex10 t0' t1' t2' a6' t3' t4' t5' t6' scrM w' | exists t0', t1', t2', a6', t3', t4', t5', t6', scrM, w' ]. split; [reflexivity|].
    split; [exact (cy_step _ _ _ _ _ _ _ _ _ _ _ w w' CYw MU WM MI' (fun x H => H) S1 S2 S3 S4)|].
    split; [exact (rw_step _ _ _ _ _ w w' (conj RNF (conj RMFA (conj RAU (conj R40 (conj RMU (conj RMM REX)))))) MU WM S5)|].
    split; [exact ST'|]. split; [exact FRP| exact FRM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m spd rac Clg"] Lemma par_facts :
    (0 <= U /\ U mod 262144 = 0 /\ mu + U <= 3750000000) /\ au + (kk - nf) * size <= mu + U /\ mu + U - au < 9 * size + 262144 /\
    (0 <= N /\ au + N * size <= mu + U /\ kk - nf <= N /\ N < 9 + 8192) /\
    (0 <= Fm /\ Fm mod 262144 = 0 /\ mfa + Fm <= 536870912 /\ 4 * (nf + N) <= mfa + Fm) /\
    ((0 <= au <= mu /\ mu mod 262144 = 0 /\ au mod size = 0) /\ 0 <= mfa <= 469762048 /\ mfa mod 262144 = 0 /\ 4 * nf <= mfa /\ au <= 3615782272 /\ mu <= 3682891136) /\
    32 <= size <= 65536 /\ (mu + U) mod 262144 = 0.   (* [comment removed for export] *)
  Proof.
    (first [ pose proof ((ar_ums A 24 W0 CR EMP SHORT)) as dR_39; dand4 dR_39 as (U1 & U2 & U3) U4 U5 _ | pose proof (ar_ums A 24 W0 CR EMP SHORT) as ((U1 & U2 & U3) & U4 & U5 & _) ]). (first [ pose proof ((ar_nc A 24 W0 CR EMP SHORT)) as dR_40; dand5 dR_40 as N1 N2 _ N4 N5 | pose proof (ar_nc A 24 W0 CR EMP SHORT) as (N1 & N2 & _ & N4 & N5) ]).
    pose proof (ar_fam A 24 W0 CR EMP SHORT) as ((F1 & F2 & F3 & F3') & F4 & _).
    (first [ pose proof ((ar_reg A 24 W0 CR)) as dR_42; dand10 dR_42 as (R1 & R2) R3 R4 R5 R6 R7 R8 R9 R10 R11 | pose proof (ar_reg A 24 W0 CR) as ((R1 & R2) & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) ]). pose proof (ar_cap A 24 W0 CR EMP SHORT) as CAP0.
    pose proof (ar_csr 24 CR) as CSR. unfold kUserMapSize, kFreeArrayMapSize, kFreeArraySize, kAuCap in *. change (2^18) with 262144 in *.
    assert (Q1 : au / size <= au / 32) by (apply Z.div_le_compat_l; hot_lia_full). assert (Q2 : 32 * (au / 32) <= au) by (apply Z.mul_div_le; hot_lia_full).
    assert (MUM : (mu + U) mod 262144 = 0) by (rewrite Z.add_mod, R4, U2 by lia; reflexivity).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; try hot_lia_full.   (* [comment removed for export] *)
  Qed.
  #[using="CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m rac Clg"] Lemma Wle000 : sub_fp (Wi 0 0 0) (Wi U Fm N). Proof. (first [ pose proof (par_facts) as dR_43; dand6 dR_43 as (P1 & _) _ _ (P2 & _) (P3 & _) _ | pose proof par_facts as ((P1 & _) & _ & _ & (P2 & _) & (P3 & _) & _) ]). apply Wle; lia. Qed.
  #[using="CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m rac Clg"] Lemma WleU00 : sub_fp (Wi U 0 0) (Wi U Fm N). Proof. (first [ pose proof (par_facts) as dR_44; dand6 dR_44 as (P1 & _) _ _ (P2 & _) (P3 & _) _ | pose proof par_facts as ((P1 & _) & _ & _ & (P2 & _) & (P3 & _) & _) ]). apply Wle; lia. Qed.
  #[using="CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m rac Clg"] Lemma WleU0N : sub_fp (Wi U 0 N) (Wi U Fm N). Proof. (first [ pose proof (par_facts) as dR_45; dand6 dR_45 as (P1 & _) _ _ (P2 & _) (P3 & _) _ | pose proof par_facts as ((P1 & _) & _ & _ & (P2 & _) & (P3 & _) & _) ]). apply Wle; lia. Qed.
  #[using="CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m rac Clg"] Lemma WleUF0 : sub_fp (Wi U Fm 0) (Wi U Fm N). Proof. (first [ pose proof (par_facts) as dR_46; dand6 dR_46 as (P1 & _) _ _ (P2 & _) (P3 & _) _ | pose proof par_facts as ((P1 & _) & _ & _ & (P2 & _) & (P3 & _) & _) ]). apply Wle; lia. Qed.
  #[using="spd rac"] Lemma FAE : free_array_of sb 24 = fa. Proof. unfold free_array_of, region_beg, kRegionSize, kFreeArrayOffset. lia. Qed.
  #[using="spd rac"] Lemma RBE : rbs = rb. Proof. unfold region_beg, kRegionSize. lia. Qed.

  (* [comment removed for export] *)
  Definition ep_post (junk0 pad scr : list byte) (ksc : list word) (a0h : word) : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a4' a5' a6' a7' s6' t3' t4' t5' t6' : word) (w' : mem),
      st = MS (mkR (wz pop_efasret) (wz (uG + -64)) gp tp t0' t1' t2' (wz R) (wz (nf + N)) (wz 0xb1d58) (wz R) (wz rbs) (wz (nf + N)) a4' a5' a6' a7'
                   (wz rbs) (wz N) (wz (mu + U - au)) (wz size) s6' (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
              F (wz efas_entry) fc None w' (seg_rom rsegs)
      /\ CY junk0 pad scr ksc U 0 0 w' /\ RW nf mfa au (mu + U) w' /\ stk rsegs w' lo (uG - 64)
      /\ rw_cells rsegs w' (uG + -64) (FRPc a0h)
      /\ mapped w' (rb + mu) U /\ bytes_at rsegs w' (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))).

  #[using="KS PREF CE CR W0 AI SHORT EMP NQ HL PRE hi md"] Lemma pop_A_fit : forall (t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 : word) (junk0 pad scr : list byte) (ksc : list word) (w : mem),
    au + (kk - nf) * size <= mu ->
    CY junk0 pad scr ksc 0 0 0 w -> RW nf mfa au mu w -> stk rsegs w lo uG ->
    evt rsegs (ep_post junk0 pad scr ksc a0)
        (MS (mkR (wz refill_ret) (wz uG) gp tp t0 t1 t2 (wz R) (wz 0xb1d58) a0 (wz (C + 2560)) (wz 24) (wz (E + 16)) (wz kk) a5 a6 a7
                 (wz (p + -16)) (wz 2305843009213693952) (wz (free_array_of sb 24)) (wz 1099511627776) (wz 1152921504607895551)
                 (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3 t4 t5 t6)
            F (wz gfa_locked) fc None w (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 junk0 pad scr ksc w FIT CYw RWw STw.
    (first [ pose proof (seg_pre) as dR_47; dand16 dR_47 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof seg_pre as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    (first [ pose proof (par_facts) as dR_48; dand8 dR_48 as PU PU4 PU5 PN PF ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    assert (U0 : U = 0) by (destruct (ar_ums_cases A 24) as [[X _]|[_ X]]; [exact X| lia]).
    assert (EN : (mu - au) / size = N) by (unfold pop_nc; rewrite U0, Z.add_0_r; reflexivity).
    assert (EM : mu - au = mu + U - au) by lia.
    (first [ pose proof ((cy_statics _ _ _ _ _ _ _ w CYw Wle000)) as dR_49; dand4 dR_49 as PCo TC CSB _ | pose proof (cy_statics _ _ _ _ _ _ _ w CYw Wle000) as (PCo & TC & CSB & _) ]).
    (first [ pose proof (CYw) as dR_50; dand4 dR_50 as MUw WMw MIw _ | pose proof CYw as (MUw & WMw & MIw & _) ]). (first [ pose proof (RWw) as dR_51; dand7 dR_51 as RNF RMFA RAU R40 RMU RMM REX | pose proof RWw as (RNF & RMFA & RAU & R40 & RMU & RMM & REX) ]).
    pose proof (pop_sA_fit gp tp t0 t1 t2 a0 a5 a6 a7 t3 t4 t5 t6 F fc w (wz (p + -16)) s10 s11 sa lo thr 24 (max_count 24) sb ri nf au mu) as EV.
    unfold pop_sA_fit_post in EV. cbv zeta in EV. rewrite !KS in EV. rewrite !EN in EV. rewrite EM in EV.
    specialize (EV MIw STw LO SPH CR MXR THR RIR SBR NF ltac:(unfold kUserMap; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) ltac:(lia) CSB RNF RAU RMU FIT).
    eapply evt_mono; [exact EV|]. (intros st; (first [ intro dR_101; dex3 dR_101 as a5' a6' w'; dand6 dR_101 as -> MU WM MI' ST' FRP | intro dR_101; dand9 dR_101 as a5' a6' w' -> MU WM MI' ST' FRP | intros (a5' & a6' & w' & -> & MU & WM & MI' & ST' & FRP) ])).
    (first [ pose proof ((pk_stackW (uG - 64) uG U 0 0 ltac:(lia) ltac:(lia))) as dR_52; dand5 dR_52 as S1 S2 S3 S4 S5 | destruct (pk_stackW (uG - 64) uG U 0 0 ltac:(lia) ltac:(lia)) as (S1 & S2 & S3 & S4 & S5) ]).
    lin_open.
    first [ hotw_ex13 t0 t1 t2 (wz (kk - nf)) a5' a6' a7 (wz kk) t3 t4 t5 t6 w' | exists t0, t1, t2, (wz (kk - nf)), a5', a6', a7, (wz kk), t3, t4, t5, t6, w' ]. split; [reflexivity|].
    split; [exact (cy_step _ _ _ _ _ _ _ _ _ _ _ w w' CYw MU WM MI' (Wmono 0 0 0 U 0 0 ltac:(lia) ltac:(lia) ltac:(lia)) S1 S2 S3 S4)|].
    split; [rewrite U0, Z.add_0_r; exact (rw_step _ _ _ _ _ w w' RWw MU WM S5)|].
    split; [exact ST'|]. split; [exact FRP|].
    rewrite U0. split; [intros i Hi; lia|]. change (0 / 8) with 0. apply bytes_at_nil. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pk_Wb : list (Z * Z) :=
    [(uG - 192, uG - 64); (sh (rbs + mu), sh (rbs + mu) + U / 8); (thr + off_th_stats + 72, thr + off_th_stats + 88);
     (C + 2560 + 24, C + 2560 + 32); (R + 48, R + 56)].
  #[using="PREF CE CR AI SHORT EMP PRE key hi lo stkobj n0 p md m rac Clg"] Lemma pk_WB : sub_fp pk_Wb (Wi U 0 0) /\ disjoint_from pk_Wb (sa - 336) 336 /\ disjoint_from pk_Wb R 8 /\ disjoint_from pk_Wb (thr + 288) 2480 /\
    (forall a l, (R + 8 <= a /\ a + l <= R + 48) \/ (R + 56 <= a /\ a + l <= R + 128) -> disjoint_from pk_Wb a l).
  Proof.
    (first [ pose proof (seg_pre) as dR_53; dand14 dR_53 as _ _ _ _ _ _ _ _ _ _ SEP_tr SEP_rs SEP_ts _ | pose proof seg_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEP_tr & SEP_rs & SEP_ts & _) ]).
    lin_open. unfold pk_Wb. rewrite RBE.
    split; [sub_open; (cv 0; cv 9; cv 6; cv 12; cv 3; exact I)|].
    split; [dj_tac|]. split; [dj_tac|]. split; [dj_tac|]. intros a l Hal. dj_tac.
  Qed.

  #[using="KS PREF CE CR W0 AI SHORT EMP NQ HL PRE hi md"] Lemma pop_B : forall (t0 t1 t2 a6 t3 t4 t5 t6 a0h : word) (junk0 pad scr scrM old : list byte) (ksc : list word) (w : mem),
    mu < au + (kk - nf) * size ->
    CY junk0 pad scr ksc U 0 0 w -> RW nf mfa au mu w -> stk rsegs w lo (uG + -64 + -128) ->
    rw_cells rsegs w (uG + -64) (FRPc a0h) ->
    rw_cells rsegs w (uG + -64 + -128) (mapcb_frame scrM (wz (rbs + mu)) (wz U) (wz rbs) (rbs + mu) U (wz (C + 2560)) (wz R) (wz pop_mapret)) ->
    rw_cells rsegs w (sh (rbs + mu)) [CB (Z.to_nat (U / 8)) old] -> mapped w (rb + mu) U ->
    evt rsegs (ep_post junk0 pad scr ksc a0h)
        (MS (mkR (wz mapfixed_resume) (wz (uG + -64 + -128)) gp tp t0 t1 t2 (wz U) (wz 1) (wz (rbs + mu)) (wz U) (wz 3) (wz 50) (wz (-1)) (wz 0) a6 (wz 222)
                 (wz (rbs + mu)) (wz pop_name) (wz PSC) (wz size) (wz 0xb1d58) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3 t4 t5 t6)
            F (wz mmap_after_pc) fc None w (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a6 t3 t4 t5 t6 a0h junk0 pad scr scrM old ksc w NOFIT CYw RWw STw FRP FRM SHB NEWU.
    (first [ pose proof (seg_pre) as dR_54; dand16 dR_54 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof seg_pre as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    (first [ pose proof (par_facts) as dR_55; dand8 dR_55 as PU PU4 PU5 PN PF ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    assert (EU : U = round_up (au + (kk - nf) * size - mu) kUserMap) by (destruct (ar_ums_cases A 24) as [[_ X]|[X _]]; [lia| exact X]).
    assert (EN : (mu + U - au) / size = N) by reflexivity.
    (first [ pose proof ((cy_statics _ _ _ _ _ _ _ w CYw WleU00)) as dR_56; dand8 dR_56 as PCo TC CSB CREL CPMH CCF2 CCF144 MRN | pose proof (cy_statics _ _ _ _ _ _ _ w CYw WleU00) as (PCo & TC & CSB & CREL & CPMH & CCF2 & CCF144 & MRN) ]).
    (first [ pose proof ((cy_tst _ _ _ _ _ _ _ w CYw)) as dR_57; dex2 dR_57 as mm72 mm80; rename dR_57 into TST | pose proof ((cy_tst _ _ _ _ _ _ _ w CYw)) as dR_57; dand3 dR_57 as mm72 mm80 TST | destruct (cy_tst _ _ _ _ _ _ _ w CYw) as (mm72 & mm80 & TST) ]). destruct (cy_stm _ _ _ _ _ _ _ w CYw) as (statm & STM).
    (first [ pose proof (CYw) as dR_58; dand4 dR_58 as MUw WMw MIw _ | pose proof CYw as (MUw & WMw & MIw & _) ]). (first [ pose proof (RWw) as dR_59; dand7 dR_59 as RNF RMFA RAU R40 RMU RMM REX | pose proof RWw as (RNF & RMFA & RAU & R40 & RMU & RMM & REX) ]).
    pose proof (pop_sB gp tp t0 t1 t2 a6 t3 t4 t5 t6 a0h F fc w s10 s11 sa lo thr 24 (max_count 24) sb ri nf au mu pa_tsd ctx scrM old mm72 mm80 statm) as EV.
    unfold pop_sB_post in EV. cbv zeta in EV. rewrite !KS in EV. rewrite <- !EU in EV. rewrite !EN in EV.
    specialize (EV poison_ok thread_stats_ok MIw STw LO SPA SPH CR MXR THR THRA RIR SBR SBAL SEP_tr NF ltac:(unfold kUserMap; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) NOFIT ltac:(lia)
                   TPL TSDL PCo TC CCF144 RNF RAU RMU FRP FRM SHB TST STM).
    eapply evt_mono; [exact EV|].
    (intros st; (first [ intro dR_102; dex13 dR_102 as t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' statm' w'; dand12 dR_102 as -> MU WM MI' ST' FRP' RNF' RAU' RMU' SHU' TST' STM' | intro dR_102; dand25 dR_102 as t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' statm' w' -> MU WM MI' ST' FRP' RNF' RAU' RMU' SHU' TST' STM' | intros (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & statm' & w' & -> & MU & WM & MI' & ST' & FRP' & RNF' & RAU' & RMU' & SHU' & TST' & STM') ])).
    lin_open. pose proof RBE as RBEq.
    fold pk_Wb in MU. (first [ dand5 pk_WB as SUB DF DR DL DW | destruct pk_WB as (SUB & DF & DR & DL & DW) ]).
    first [ hotw_ex13 t0' t1' t2' a4' a5' a6' a7' (wz 0xb1d58) t3' t4' t5' t6' w' | exists t0', t1', t2', a4', a5', a6', a7', (wz 0xb1d58), t3', t4', t5', t6', w' ]. split; [reflexivity|].
    split; [exact (cy_step _ _ _ _ _ _ _ _ _ _ _ w w' CYw MU WM MI' (fun x H => H) SUB DF DR DL)|].
    split.
    { unfold regw. split; [exact RNF'|].
      split; [eapply rw_cells_transport; [exact RMFA| exact MU| exact WM| apply DW; cbn; lia]|].
      split; [exact RAU'|].
      split; [eapply rw_cells_transport; [exact R40| exact MU| exact WM| apply DW; cbn; lia]|].
      split; [exact RMU'|].
      split; [eapply rw_cells_transport; [exact RMM| exact MU| exact WM| apply DW; cbn; lia]|].
      eapply rw_cells_transport; [exact REX| exact MU| exact WM| apply DW; cbn; lia]. }
    split; [exact ST'|]. split; [exact FRP'|].
    split; [apply (pk_mapped_wm w w' _ _ WM); [lia| right; lia| lia| exact NEWU]|].
    rewrite <- RBEq. exact SHU'.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition gpk (junk0 pad scr : list byte) (ksc : list word) (na : word) (v5 : mem) : Prop :=
    CY junk0 pad scr ksc U Fm N v5 /\ stk rsegs v5 lo uG /\
    rw_cells rsegs v5 (R + 16) [C8 (wz (nf + N))] /\ rw_cells rsegs v5 (R + 24) [C8 (wz (mfa + Fm))] /\
    rw_cells rsegs v5 (R + 32) [C8 (wz (au + N * size))] /\ rw_cells rsegs v5 (R + 48) [C8 (wz (mu + U))] /\ rw_cells rsegs v5 (R + 68) [C1 (Z_to_bv 8 0)] /\
    rw_cells rsegs v5 (R + 72) [C8 na] /\
    u32arr rsegs v5 (fa + 4 * nf) (map (fun k => wz (k * size / kCompactPtrScale)) (newfree (au / size) N)) /\
    mapped v5 (rb + mu) U /\ mapped v5 (fa + mfa) Fm /\
    bytes_at rsegs v5 (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))) /\
    bytes_at rsegs v5 (sh (fa + mfa)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (Fm / 8))).

  Definition gp_post (junk0 pad scr : list byte) (ksc : list word) : machine_state -> Prop := fun st =>
    exists (tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 a0g na : word) (v5 : mem),
      st = MS (mkR (wz gfa_popret) (wz uG) gp tp tq0 tq1 tq2 (wz R) (wz 0xb1d58) (wz 1) aq1 aq2 aq3 aq4 aq5 aq6 aq7
                   a0g (wz 2305843009213693952) (wz (free_array_of sb 24)) (wz (E + 16)) (wz kk)
                   (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 tq3 tq4 tq5 tq6)
              F (wz gfa_popret) fc None v5 (seg_rom rsegs)
      /\ gpk junk0 pad scr ksc na v5.

  (* [comment removed for export] *)
  Lemma cy_weaken : forall (junk0 pad scr : list byte) (ksc : list word) (u f x u' f' x' : Z) (w : mem),
    CY junk0 pad scr ksc u f x w -> sub_fp (Wi u f x) (Wi u' f' x') -> CY junk0 pad scr ksc u' f' x' w.
  Proof.
    (intros junk0 pad scr ksc u f x u' f' x' w; (first [ intro dR_103; dand12 dR_103 as MU0 WM0 MI0 FA FC FR FG MX LK LN LNS (wH & MUH & WMH & FCH) | intros (MU0 & WM0 & MI0 & FA & FC & FR & FG & MX & LK & LN & LNS & (wH & MUH & WMH & FCH)) ]); intros LE).
    unfold carryF.
    split; [exact (munch_weaken _ _ _ _ (sub_fp_app2 _ _ _ LE) MU0)|]. split; [exact WM0|]. split; [exact MI0|].
    split; [exact FA|]. split; [exact FC|]. split; [exact FR|]. split; [exact FG|]. split; [exact MX|]. split; [exact LK|]. split; [exact LN|]. split; [exact LNS|].
    exists wH. split; [exact (munch_weaken _ _ _ _ LE MUH)|]. split; [exact WMH| exact FCH].
  Qed.

  (* [comment removed for export] *)
  #[using="CR W0 AI SHORT EMP PRE hi md"] Lemma gpk_intro : forall (junk0 pad scr : list byte) (ksc : list word) (u f x : Z) (v5 : mem),
    CY junk0 pad scr ksc u f x v5 -> sub_fp (Wi u f x) (Wi U Fm N) -> stk rsegs v5 lo uG ->
    rw_cells rsegs v5 (R + 16) [C8 (wz (nf + N))] -> rw_cells rsegs v5 (R + 24) [C8 (wz (mfa + Fm))] ->
    rw_cells rsegs v5 (R + 32) [C8 (wz (au + N * size)); C8 (wz 0); C8 (wz (mu + U)); C8 (wz 0)] -> rw_cells rsegs v5 (R + 68) [C1 (Z_to_bv 8 0)] ->
    u32arr rsegs v5 (free_array_of sb 24 + 4 * nf) (ARtSb8o.carved au size N) ->
    mapped v5 (rb + mu) U -> mapped v5 (fa + mfa) Fm ->
    bytes_at rsegs v5 (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))) ->
    bytes_at rsegs v5 (sh (fa + mfa)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (Fm / 8))) ->
    exists na, gpk junk0 pad scr ksc na v5.
  Proof.
    intros junk0 pad scr ksc u f x v5 CY5 LE ST5 PNF PMFA RAU4 PEX PFA PNU PNF' PSU PSF.
    destruct (cy_na _ _ _ _ _ _ _ v5 CY5) as (na & PNA). exists na.
    (first [ pose proof (par_facts) as dR_61; dand8 dR_61 as PU PU4 PU5 PN PF ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    change [C8 (wz (au + N * size)); C8 (wz 0); C8 (wz (mu + U)); C8 (wz 0)] with ([C8 (wz (au + N * size))] ++ [C8 (wz 0)] ++ [C8 (wz (mu + U))] ++ [C8 (wz 0)]) in RAU4.
    apply rw_cells_app_iff in RAU4. destruct RAU4 as [PAU RAU4]. apply rw_cells_app_iff in RAU4. destruct RAU4 as [_ RAU4]. apply rw_cells_app_iff in RAU4. destruct RAU4 as [PMU _].
    cbn [cells_size csize Nat.add] in PMU. replace (R + 32 + Z.of_nat 8 + Z.of_nat 8) with (R + 48) in PMU by lia.
    unfold gpk.
    split; [exact (cy_weaken _ _ _ _ _ _ _ _ _ _ v5 CY5 LE)|].
    split; [exact ST5|]. split; [exact PNF|]. split; [exact PMFA|].
    split; [exact PAU|]. split; [exact PMU|]. split; [exact PEX|]. split; [exact PNA|].
    split; [rewrite <- FAE, <- (carved_newfree au size N ltac:(lia) R5); exact PFA|].
    split; [exact PNU|]. split; [exact PNF'|]. split; [exact PSU| exact PSF].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pk_Wc : list (Z * Z) :=
    [(uG - 112, uG); (R + 16, R + 24); (R + 32, R + 40); (R + 68, R + 69); (free_array_of sb 24 + 4 * nf, free_array_of sb 24 + 4 * nf + 4 * N)].
  #[using="PREF CE CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m rac Clg"] Lemma pk_WC : sub_fp pk_Wc (Wi U 0 N) /\ disjoint_from pk_Wc (sa - 336) 336 /\ disjoint_from pk_Wc R 8 /\ disjoint_from pk_Wc (thr + 288) 2480 /\
    disjoint_from pk_Wc (sh (rb + mu)) (U / 8).
  Proof.
    (first [ pose proof (seg_pre) as dR_62; dand14 dR_62 as _ _ _ _ _ _ _ _ _ _ SEP_tr SEP_rs SEP_ts _ | pose proof seg_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEP_tr & SEP_rs & SEP_ts & _) ]).
    (first [ pose proof (par_facts) as dR_63; dand6 dR_63 as PU PU4 PU5 PN PF _ | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & _) ]).
    lin_open. unfold pk_Wc.
    split; [sub_open; (cv 0; cv 2; cv 2; cv 4; cv 5; exact I)|].
    split; [dj_tac|]. split; [dj_tac|]. split; [dj_tac|]. dj_tac.
  Qed.

  #[using="spd rac"] Lemma merge_RAU4 : forall (w : mem) auv muv, RW nf mfa auv muv w -> rw_cells rsegs w (R + 32) [C8 (wz auv); C8 (wz 0); C8 (wz muv); C8 (wz 0)].
  Proof.
    (intros w auv muv; (first [ intro dR_104; dand7 dR_104 as _ _ RAU R40 RMU RMM _ | intros (_ & _ & RAU & R40 & RMU & RMM & _) ])).
    change [C8 (wz auv); C8 (wz 0); C8 (wz muv); C8 (wz 0)] with ([C8 (wz auv)] ++ [C8 (wz 0)] ++ [C8 (wz muv)] ++ [C8 (wz 0)]).
    apply rw_cells_app_iff. split; [exact RAU|]. cbn [cells_size csize Nat.add]. replace (R + 32 + Z.of_nat 8) with (R + 40) by lia.
    apply rw_cells_app_iff. split; [exact R40|]. cbn [cells_size csize Nat.add]. replace (R + 40 + Z.of_nat 8) with (R + 48) by lia.
    apply rw_cells_app_iff. split; [exact RMU|]. cbn [cells_size csize Nat.add]. replace (R + 48 + Z.of_nat 8) with (R + 56) by lia. exact RMM.
  Qed.

  (* [comment removed for export] *)
  #[using="CE CR W0 AI SHORT EMP PRE hi lo md"] Lemma faj_old : forall (junk0 pad scr : list byte) (ksc : list word) (u f x : Z) (w : mem), CY junk0 pad scr ksc u f x w -> 4 * (nf + N) <= mfa ->
    exists junk, length junk = Z.to_nat N /\ u32arr rsegs w (free_array_of sb 24 + 4 * nf) junk.
  Proof.
    intros junk0 pad scr ksc u f x w CYw FAST. (first [ pose proof (par_facts) as dR_64; dand5 dR_64 as _ _ _ (N0 & _) _ | pose proof par_facts as (_ & _ & _ & (N0 & _) & _) ]). lin_open.
    (first [ pose proof (f_region) as dR_65; dand11 dR_65 as _ _ _ _ _ _ _ _ _ MFA _ | pose proof f_region as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MFA & _) ]).
    apply mapped_u32arr; [| rewrite FAE; unfold kFreeArrayOffset; lia| rewrite FAE; unfold kFreeArrayOffset; lia].
    rewrite FAE. apply (cy_mapped _ _ _ _ _ _ _ w CYw); [| unfold kFreeArrayOffset; lia| right; unfold kFreeArrayOffset; lia| unfold kFreeArrayOffset; lia].
    intros i Hi. replace (fa + 4 * nf + i) with (fa + (4 * nf + i)) by lia. apply MFA. lia.
  Qed.

  #[using="KS CEILw CEIL SAE PREF CE CR W0 AI SHORT EMP PRE hi md"] Lemma pop_C_fast : forall (t0 t1 t2 a4 a5 a6 a7 s6v t3 t4 t5 t6 a0h : word) (junk0 pad scr : list byte) (ksc : list word) (w : mem),
    4 * (nf + N) <= mfa ->
    CY junk0 pad scr ksc U 0 0 w -> RW nf mfa au (mu + U) w -> stk rsegs w lo (uG - 64) ->
    rw_cells rsegs w (uG + -64) (FRPc a0h) ->
    mapped w (rb + mu) U -> bytes_at rsegs w (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))) ->
    evt rsegs (gp_post junk0 pad scr ksc)
        (MS (mkR (wz pop_efasret) (wz (uG + -64)) gp tp t0 t1 t2 (wz R) (wz (nf + N)) (wz 0xb1d58) (wz R) (wz rbs) (wz (nf + N)) a4 a5 a6 a7
                 (wz rbs) (wz N) (wz (mu + U - au)) (wz size) s6v (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3 t4 t5 t6)
            F (wz efas_entry) fc None w (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a4 a5 a6 a7 s6v t3 t4 t5 t6 a0h junk0 pad scr ksc w FAST CYw RWw STw FRP NEWU SHU.
    (first [ pose proof (seg_pre) as dR_66; dand16 dR_66 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof seg_pre as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    (first [ pose proof (par_facts) as dR_67; dand8 dR_67 as PU PU4 PU5 PN PF ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    assert (F0 : Fm = 0) by (destruct (ar_fam_cases A 24) as [[X _]|[_ X]]; [exact X| lia]).
    (first [ pose proof ((faj_old _ _ _ _ _ _ _ w CYw FAST)) as dR_68; dex1 dR_68 as junk; destruct dR_68 as [LJ FAJ] | pose proof ((faj_old _ _ _ _ _ _ _ w CYw FAST)) as dR_68; dand3 dR_68 as junk LJ FAJ | destruct (faj_old _ _ _ _ _ _ _ w CYw FAST) as (junk & LJ & FAJ) ]).
    (first [ pose proof (CYw) as dR_69; dand4 dR_69 as MUw WMw MIw _ | pose proof CYw as (MUw & WMw & MIw & _) ]). (first [ pose proof (RWw) as dR_70; dand7 dR_70 as RNF RMFA _ _ _ _ REX | pose proof RWw as (RNF & RMFA & _ & _ & _ & _ & REX) ]).
    pose proof (pop_sC_fast gp tp t0 t1 t2 a4 a5 a6 a7 s6v t3 t4 t5 t6 a0h F fc w s10 s11 sa lo thr 24 (max_count 24) sb ri nf au (mu + U) mfa junk) as EV.
    unfold pop_grow_post in EV. cbv zeta in EV. rewrite !KS in EV. change ((mu + U - au) / size) with N in EV.
    change (pop_sC_W sa 24 sb ri nf au (mu + U)) with pk_Wc in EV.
    replace (ret_pc (wz gfa_popret)) with (wz gfa_popret : word) in EV by (symmetry; apply ret_pc_even; [unfold gfa_popret; lia| reflexivity]).
    specialize (EV MIw STw LO SPA SPH CR MXR THR RIR SBR SBAL SEP_rs NF ltac:(unfold kUserMap; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) ltac:(lia)
                   ltac:(unfold kFreeArrayMapSize; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) LJ RNF RMFA (merge_RAU4 w _ _ RWw) (ex_intro (fun ex => rw_cells rsegs w (R + 68) [C1 ex]) _ REX) FRP FAJ FAST).
    eapply evt_mono; [exact EV|].
    (intros st; (first [ intro dR_105; dex15 dR_105 as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w'; dand11 dR_105 as -> MU WM MI' ST' RNF' RMFA' RAU4' REX' FA' _ | intro dR_105; dand26 dR_105 as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w' -> MU WM MI' ST' RNF' RMFA' RAU4' REX' FA' _ | intros (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & w' & -> & MU & WM & MI' & ST' & RNF' & RMFA' & RAU4' & REX' & FA' & _) ])).
    (first [ dand5 pk_WC as SUB DF DR DL DS | destruct pk_WC as (SUB & DF & DR & DL & DS) ]). lin_open.
    pose proof (cy_step _ _ _ _ U 0 0 U 0 N _ w w' CYw MU WM MI' (Wmono U 0 0 U 0 N ltac:(lia) ltac:(lia) ltac:(lia)) SUB DF DR DL) as CY'.
    destruct (gpk_intro junk0 pad scr ksc U 0 N w' CY' WleU0N ST' RNF' ltac:(rewrite F0, Z.add_0_r; exact RMFA') RAU4' REX' FA') as (na & GP).
    - apply (pk_mapped_wm w w' _ _ WM); [lia| right; lia| lia| exact NEWU].
    - rewrite F0. intros i Hi. lia.
    - eapply bytes_at_transport; [exact SHU| exact MU|]. rewrite repeat_length, Z2Nat.id by lia. exact DS.
    - rewrite F0. change (0 / 8) with 0. apply bytes_at_nil. lia.
    - exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', a0h, na, w'. split; [reflexivity| exact GP].
  Qed.

  #[warnings="-notation-for-abbreviation"] Local Notation nmv := (round_up (4 * (nf + N)) kFaMap).
  #[warnings="-notation-for-abbreviation"] Local Notation fev := (rbs + kFreeArrayOffset + mfa).
  #[warnings="-notation-for-abbreviation"] Local Notation FREc scr2 := (efas_frame scr2 (wz N) (wz rbs) (wz (nf + N)) (wz R) (wz pop_efasret)).
  #[warnings="-notation-for-abbreviation"] Local Notation FRM2c scrM := (mapcb_frame scrM (wz (mu + U - au)) (wz R) (wz (nmv - mfa)) fev (nmv - mfa) (wz fev) (wz nmv) (wz efas_mapret)).

  Definition pm2_post (junk0 pad scr : list byte) (ksc : list word) (a0h s6v : word) : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (scr2 scrM : list byte) (w' : mem),
      st = MSsvc (mkR (wz mapfixed_resume) (wz (uG + -64 + -48 + -128)) gp tp t0' t1' t2' (wz (nmv - mfa)) (wz 1) (wz fev) (wz (nmv - mfa)) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz fev) (wz efas_name) (wz PSC) (wz size) s6v (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
                 F (wz mmap_ecall_pc) (wz 222) fc None w' (seg_rom rsegs)
      /\ CY junk0 pad scr ksc U 0 0 w' /\ RW nf mfa au (mu + U) w' /\ stk rsegs w' lo (uG + -64 + -48 + -128)
      /\ rw_cells rsegs w' (uG + -64) (FRPc a0h) /\ rw_cells rsegs w' (uG + -64 + -48) (FREc scr2) /\ rw_cells rsegs w' (uG + -64 + -48 + -128) (FRM2c scrM)
      /\ mapped w' (rb + mu) U /\ bytes_at rsegs w' (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))).


  #[using="KS CEILw CEIL SAE PREF CE CR W0 AI SHORT EMP NQ HL PRE hi md"] Lemma pop_C_map : forall (t0 t1 t2 a4 a5 a6 a7 s6v t3 t4 t5 t6 a0h : word) (junk0 pad scr : list byte) (ksc : list word) (w : mem),
    mfa < 4 * (nf + N) ->
    CY junk0 pad scr ksc U 0 0 w -> RW nf mfa au (mu + U) w -> stk rsegs w lo (uG - 64) ->
    rw_cells rsegs w (uG + -64) (FRPc a0h) ->
    mapped w (rb + mu) U -> bytes_at rsegs w (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))) ->
    evt rsegs (pm2_post junk0 pad scr ksc a0h s6v)
        (MS (mkR (wz pop_efasret) (wz (uG + -64)) gp tp t0 t1 t2 (wz R) (wz (nf + N)) (wz 0xb1d58) (wz R) (wz rbs) (wz (nf + N)) a4 a5 a6 a7
                 (wz rbs) (wz N) (wz (mu + U - au)) (wz size) s6v (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3 t4 t5 t6)
            F (wz efas_entry) fc None w (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a4 a5 a6 a7 s6v t3 t4 t5 t6 a0h junk0 pad scr ksc w NEEDMAP CYw RWw STw FRP NEWU SHU.
    (first [ pose proof (seg_pre) as dR_72; dand16 dR_72 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof seg_pre as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    (first [ pose proof (par_facts) as dR_73; dand8 dR_73 as PU PU4 PU5 PN PF ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    (first [ pose proof ((cy_statics _ _ _ _ _ _ _ w CYw WleU00)) as dR_74; dand8 dR_74 as PCo TC CSB CREL CPMH CCF2 CCF144 MRN | pose proof (cy_statics _ _ _ _ _ _ _ w CYw WleU00) as (PCo & TC & CSB & CREL & CPMH & CCF2 & CCF144 & MRN) ]).
    (first [ dand13 PCo as _ CCF1 _ _ _ _ _ _ _ _ _ CPSC1 CPSC2 | destruct PCo as (_ & CCF1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CPSC1 & CPSC2) ]).
    (first [ pose proof (CYw) as dR_76; dand4 dR_76 as MUw WMw MIw _ | pose proof CYw as (MUw & WMw & MIw & _) ]). (first [ pose proof (RWw) as dR_77; dand3 dR_77 as RNF RMFA _ | pose proof RWw as (RNF & RMFA & _) ]).
    pose proof (pop_sC_map gp tp t0 t1 t2 a4 a5 a6 a7 s6v t3 t4 t5 t6 F fc w s10 s11 sa lo thr 24 (max_count 24) sb ri nf au (mu + U) mfa (repeat (wz 0) (Z.to_nat N))) as EV.
    unfold pop_sC_map_post in EV. cbv zeta in EV. rewrite ?KS in EV. change ((mu + U - au) / size) with N in EV.
    specialize (EV MIw STw LO SPH CR MXR THR RIR SBR SBAL NF ltac:(unfold kUserMap; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia)
                   ltac:(unfold kFreeArrayMapSize; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) ltac:(apply repeat_length) CPMH CPSC1 CPSC2 CCF1 CCF2 RMFA NEEDMAP).
    eapply evt_mono; [exact EV|].
    (intros st; (first [ intro dR_106; dex11 dR_106 as t0' t1' t2' a6' t3' t4' t5' t6' scr2 scrM w'; dand7 dR_106 as -> MU WM MI' ST' FRE FRM | intro dR_106; dand18 dR_106 as t0' t1' t2' a6' t3' t4' t5' t6' scr2 scrM w' -> MU WM MI' ST' FRE FRM | intros (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & scr2 & scrM & w' & -> & MU & WM & MI' & ST' & FRE & FRM) ])).
    (first [ pose proof ((pk_stackW (uG - 512) (uG + -64) U 0 0 ltac:(lia) ltac:(lia))) as dR_78; dand5 dR_78 as S1 S2 S3 S4 S5 | destruct (pk_stackW (uG - 512) (uG + -64) U 0 0 ltac:(lia) ltac:(lia)) as (S1 & S2 & S3 & S4 & S5) ]). lin_open.
    first [ hotw_ex11 t0' t1' t2' a6' t3' t4' t5' t6' scr2 scrM w' | exists t0', t1', t2', a6', t3', t4', t5', t6', scr2, scrM, w' ]. split; [reflexivity|].
    split; [exact (cy_step _ _ _ _ _ _ _ _ _ _ _ w w' CYw MU WM MI' (fun x H => H) S1 S2 S3 S4)|].
    split; [exact (rw_step _ _ _ _ _ w w' RWw MU WM S5)|].
    split; [exact ST'|].
    split; [eapply rw_cells_transport; [exact FRP| exact MU| exact WM| cbn [disjoint_from cells_size csize pop_frame Nat.add]; split; [lia| exact I]]|].
    split; [exact FRE|]. split; [exact FRM|].
    split; [apply (pk_mapped_wm w w' _ _ WM); [lia| right; lia| lia| exact NEWU]|].
    eapply bytes_at_transport; [exact SHU| exact MU|]. rewrite repeat_length, Z2Nat.id by lia. cbn [disjoint_from]. split; [lia| exact I].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pk_Wd : list (Z * Z) :=
    [(uG - 240, uG); (sh (fa + mfa), sh (fa + mfa) + Fm / 8); (thr + off_th_stats + 72, thr + off_th_stats + 88);
     (R + 16, R + 32); (R + 32, R + 40); (R + 68, R + 69); (free_array_of sb 24 + 4 * nf, free_array_of sb 24 + 4 * nf + 4 * N)].
  #[using="PREF CE CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m rac Clg"] Lemma pk_WD : sub_fp pk_Wd (Wi U Fm N) /\ disjoint_from pk_Wd (sa - 336) 336 /\ disjoint_from pk_Wd R 8 /\ disjoint_from pk_Wd (thr + 288) 2480 /\
    disjoint_from pk_Wd (sh (rb + mu)) (U / 8).
  Proof.
    (first [ pose proof (seg_pre) as dR_79; dand14 dR_79 as _ _ _ _ _ _ _ _ _ _ SEP_tr SEP_rs SEP_ts _ | pose proof seg_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEP_tr & SEP_rs & SEP_ts & _) ]).
    (first [ pose proof (par_facts) as dR_80; dand6 dR_80 as PU PU4 PU5 PN PF _ | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & _) ]).
    lin_open. unfold pk_Wd.
    split; [sub_open; (cv 0; cv 11; cv 6; cv 2; cv 2; cv 4; cv 5; exact I)|].
    split; [dj_tac|]. split; [dj_tac|]. split; [dj_tac|]. dj_tac.
  Qed.

  #[using="KS CEILw CEIL SAE PREF CE CR W0 AI SHORT EMP NQ HL PRE hi md"] Lemma pop_D : forall (t0 t1 t2 a6 s6v t3 t4 t5 t6 a0h : word) (junk0 pad scr scr2 scrM old : list byte) (ksc : list word) (w : mem),
    mfa < 4 * (nf + N) ->
    CY junk0 pad scr ksc U Fm 0 w -> RW nf mfa au (mu + U) w -> stk rsegs w lo (uG + -64 + -48 + -128) ->
    rw_cells rsegs w (uG + -64) (FRPc a0h) -> rw_cells rsegs w (uG + -64 + -48) (FREc scr2) -> rw_cells rsegs w (uG + -64 + -48 + -128) (FRM2c scrM) ->
    mapped w (rb + mu) U -> bytes_at rsegs w (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))) ->
    rw_cells rsegs w (sh fev) [CB (Z.to_nat ((nmv - mfa) / 8)) old] -> mapped w (fa + mfa) Fm ->
    evt rsegs (gp_post junk0 pad scr ksc)
        (MS (mkR (wz mapfixed_resume) (wz (uG + -64 + -48 + -128)) gp tp t0 t1 t2 (wz (nmv - mfa)) (wz 1) (wz fev) (wz (nmv - mfa)) (wz 3) (wz 50) (wz (-1)) (wz 0) a6 (wz 222)
                 (wz fev) (wz efas_name) (wz PSC) (wz size) s6v (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3 t4 t5 t6)
            F (wz mmap_after_pc) fc None w (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a6 s6v t3 t4 t5 t6 a0h junk0 pad scr scr2 scrM old ksc w NEEDMAP CYw RWw STw FRP FRE FRM NEWU SHU SHF NEWF.
    (first [ pose proof (seg_pre) as dR_81; dand16 dR_81 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof seg_pre as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    (first [ pose proof (par_facts) as dR_82; dand8 dR_82 as PU PU4 PU5 PN PF ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof par_facts as (PU & PU4 & PU5 & PN & PF & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    assert (EF : Fm = nmv - mfa) by (destruct (ar_fam_cases A 24) as [[_ X]|[X _]]; [lia| exact X]).
    (first [ pose proof ((cy_statics _ _ _ _ _ _ _ w CYw WleUF0)) as dR_83; dand8 dR_83 as PCo TC CSB CREL CPMH CCF2 CCF144 MRN | pose proof (cy_statics _ _ _ _ _ _ _ w CYw WleUF0) as (PCo & TC & CSB & CREL & CPMH & CCF2 & CCF144 & MRN) ]).
    (first [ pose proof ((cy_tst _ _ _ _ _ _ _ w CYw)) as dR_84; dex2 dR_84 as mm72 mm80; rename dR_84 into TST | pose proof ((cy_tst _ _ _ _ _ _ _ w CYw)) as dR_84; dand3 dR_84 as mm72 mm80 TST | destruct (cy_tst _ _ _ _ _ _ _ w CYw) as (mm72 & mm80 & TST) ]).
    (first [ pose proof (CYw) as dR_85; dand4 dR_85 as MUw WMw MIw _ | pose proof CYw as (MUw & WMw & MIw & _) ]). (first [ pose proof (RWw) as dR_86; dand7 dR_86 as RNF RMFA _ _ _ _ REX | pose proof RWw as (RNF & RMFA & _ & _ & _ & _ & REX) ]).
    (* [comment removed for export] *)
    assert (FAJx : exists junk, length junk = Z.to_nat N /\ u32arr rsegs w (free_array_of sb 24 + 4 * nf) junk).
    { (first [ pose proof (f_region) as dR_87; dand11 dR_87 as _ _ _ _ _ _ _ _ _ MFAv _ | pose proof f_region as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MFAv & _) ]). lin_open.
      apply mapped_u32arr; [| rewrite FAE; unfold kFreeArrayOffset; lia| rewrite FAE; unfold kFreeArrayOffset; lia].
      rewrite FAE. intros i Hi. destruct (Z_lt_le_dec (4 * nf + i) mfa) as [OLD|NEW].
      - assert (X : mapped w (fa + 4 * nf + i) 1).
        { apply (cy_mapped _ _ _ _ _ _ _ w CYw (fa + 4 * nf + i) 1); [| unfold kFreeArrayOffset; lia| right; unfold kFreeArrayOffset; lia| unfold kFreeArrayOffset; lia].
          intros j Hj. replace (fa + 4 * nf + i + j) with (fa + (4 * nf + i)) by lia. apply MFAv. lia. }
        specialize (X 0 ltac:(lia)). rewrite Z.add_0_r in X. exact X.
      - replace (fa + 4 * nf + i) with (fa + mfa + (4 * nf + i - mfa)) by lia. apply NEWF. lia. }
    (first [ dex1 FAJx as junk; destruct FAJx as [LJ FAJ] | dand3 FAJx as junk LJ FAJ | destruct FAJx as (junk & LJ & FAJ) ]).
    pose proof (pop_sD gp tp t0 t1 t2 a6 s6v t3 t4 t5 t6 a0h F fc w s10 s11 sa lo thr 24 (max_count 24) sb ri nf au (mu + U) mfa pa_tsd ctx scr2 scrM old junk mm72 mm80) as EV.
    unfold pop_grow_post in EV. cbv zeta in EV. rewrite ?KS in EV. change ((mu + U - au) / size) with N in EV.
    replace (ret_pc (wz gfa_popret)) with (wz gfa_popret : word) in EV by (symmetry; apply ret_pc_even; [unfold gfa_popret; lia| reflexivity]).
    specialize (EV poison_ok thread_stats_ok MIw STw LO SPA SPH CR MXR THR RIR SBR SBAL SEP_tr SEP_rs SEP_ts NF ltac:(unfold kUserMap; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) ltac:(lia)
                   ltac:(unfold kFreeArrayMapSize; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption || lia) LJ TPL TSDL PCo TC CCF144 RNF RMFA (merge_RAU4 w _ _ RWw)
                   (ex_intro (fun ex => rw_cells rsegs w (R + 68) [C1 ex]) _ REX) FRP FRE FRM FAJ SHF TST).
    eapply evt_mono; [exact EV|].
    (intros st; (first [ intro dR_107; dex15 dR_107 as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w'; dand12 dR_107 as -> MU WM MI' ST' RNF' RMFA' RAU4' REX' FA' SHF' _ | intro dR_107; dand27 dR_107 as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w' -> MU WM MI' ST' RNF' RMFA' RAU4' REX' FA' SHF' _ | intros (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & w' & -> & MU & WM & MI' & ST' & RNF' & RMFA' & RAU4' & REX' & FA' & SHF' & _) ])).
    unfold pop_sD_W in MU. change ((mu + U - au) / size) with N in MU. rewrite <- EF in MU, SHF'. rewrite RBE in MU, SHF'. change (munch pk_Wd w w') in MU.
    (first [ dand5 pk_WD as SUB DF DR DL DS | destruct pk_WD as (SUB & DF & DR & DL & DS) ]). lin_open.
    pose proof (cy_step _ _ _ _ U Fm 0 U Fm N _ w w' CYw MU WM MI' (Wmono U Fm 0 U Fm N ltac:(lia) ltac:(lia) ltac:(lia)) SUB DF DR DL) as CY'.
    destruct (gpk_intro junk0 pad scr ksc U Fm N w' CY' (fun x H => H) ST' RNF' ltac:(replace (mfa + Fm) with nmv by lia; exact RMFA') RAU4' REX' FA') as (na & GP).
    - apply (pk_mapped_wm w w' _ _ WM); [lia| right; lia| lia| exact NEWU].
    - apply (pk_mapped_wm w w' _ _ WM); [unfold kFreeArrayOffset; lia| right; unfold kFreeArrayOffset; lia| unfold kFreeArrayOffset; lia| exact NEWF].
    - eapply bytes_at_transport; [exact SHU| exact MU|]. rewrite repeat_length, Z2Nat.id by lia. exact DS.
    - exact SHF'.
    - exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', a0h, na, w'. split; [reflexivity| exact GP].
  Qed.

  (* [comment removed for export] *)
End FArm.
End AFPopE.


Module AFPopT.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 ARtSb8o AMTac AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalz1i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalmys AMaldga AMalrrv ASecB1 ANodeA7 ANodl61 ATransp ATranspR AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRW2 ABudget ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG1 APopG2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopP.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSb8o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalz1i.AMallocR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMaldga OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalrrv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRW2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1.APopDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp.APopCap OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5.APopG3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5.APopG4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopP.APopK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_3ti ARt_fpo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_png ARtSscs ARtSoqz ANodeA6 APopSA APopSB APopSC APopSD.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_3ti OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_srv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSB OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopSD.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeH AFreeHc AFreeH4w AFreeH5e AFreeH5c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AFreeB1 AFreeB3 AFreeB1F ACoresk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFPopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFPopP APopCtx.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeHc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH4w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH5e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH5c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1F OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFPopP.AFPopK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFPopP OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopCtx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFPopEnd.AFPopE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@H5; @B1; @R1; @L1; @Q2; @Q5; @B3; @B4; @H3; @CE; @B2; @Q4; @Q6; @Q3; @R6; @Hi; @X; @PU1; @Hal; @CSR; @RANGE; @U0; @H1; @H2; @Q1; @F0; @SEP_ts; @Lt1; @NEEDMAP; @Hz; @EF; @R10; @NU; @FEB; @Lt4; @PU; @PN2; @SHGEO; @U21; @X0; @NS; @SAE; @CEILw; @G4; @PF1; @Q10; @RBEq; @A1; @A5; @L; @L2; @S1; @S2; @D0; @R8; @G3; @Z64; @SPH; @Hx; @Q9; @LO; @K0'; @SAHI; @HI47; @CLO; @LOSA; @R2; @PU5; @Hu; @Hf; @NF; @NFS; @NE0; @ROOM; @G1; @G2; @E1; @M1; @E2; @E3; @M3; @S3; @S4; @FEQ; @NFx; @NFSx; @FAST; @NOFIT; @PU4; @PN1; @RIR; @SBR; @FIT])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pasan).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kShadowGapBeg, kHighShadowMapSize,
                        kAuCap, kFreeArraySize, kUserMapSize, kFreeArrayMapSize in *.


(* [comment removed for export] *)
Lemma inside_pos : forall (W : list (Z * Z)) (k : nat) (lo hi a n : Z), nth_error W k = Some (lo, hi) -> lo <= a /\ a + n <= hi -> inside W a n.
Proof.
  induction W as [|[l h] W IH]; intros [|k] lo hi a n E H; cbn [nth_error] in E; try discriminate.
  - injection E as -> ->. left. exact H.
  - right. exact (IH k lo hi a n E H).
Qed.
Ltac inside_at k :=
  lazymatch goal with |- inside ?WW ?a ?n =>
    let e := eval cbv [nth_error WW] in (nth_error WW k) in
    lazymatch e with Some (?lo, ?hi) => refine (inside_pos WW k lo hi a n eq_refl _) end
  end.
Section FArm.
Context {Clg : Ceiling}.
  Variables (rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (md : Model) (A : AState) (p n0 stkobj lo hi : Z) (key : list Z).
  Hypothesis PRE : dealloc_core_pre rac spd (cl_tp LPA) m md A p n0 stkobj lo hi key.
  Hypothesis HL : as_live A p = Some n0.
  Hypothesis NQ : n0 <= 2^28.
  Hypothesis EMP : pk_chunks (a_cache A 24) = [].
  Hypothesis SHORT : Z.of_nat (length (rg_free (a_reg A 24))) < refill_count 24.
  Hypothesis SHAPE : a_qthread A = [] \/ (a_qthread A <> [] /\ Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) = kQuarantineBatchCount).
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned spd).
  #[warnings="-notation-for-abbreviation"] Local Notation sa := (bv_unsigned spd + -80 + 112).
  #[warnings="-notation-for-abbreviation"] Local Notation spaw := (Z_to_bv 64 (bv_unsigned spd + -80 + 112)).
  #[warnings="-notation-for-abbreviation"] Local Notation tp := (cl_tp LPA).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation ctx := (p_ctx (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation ri := (a_ri A).
  #[warnings="-notation-for-abbreviation"] Local Notation n0d := (p_nodes0 (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation f0d := (p_frames0 (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation r8 := ((n0 + 7) / 8).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (a_ri A + 128 * 24).
  #[warnings="-notation-for-abbreviation"] Local Notation C := (p_thr (a_pl A) + 208).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (p_thr (a_pl A) + 208 + 80 * 24).
  #[warnings="-notation-for-abbreviation"] Local Notation uG := (bv_unsigned spd + -80 + 112 + -128 + -48 + -32 + -128).
  #[warnings="-notation-for-abbreviation"] Local Notation rb := (region_beg (a_sb A) 24).
  #[warnings="-notation-for-abbreviation"] Local Notation rbs := (a_sb A + 24 * 4294967296).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (region_beg (a_sb A) 24 + kFreeArrayOffset).
  #[warnings="-notation-for-abbreviation"] Local Notation mu := (rg_mapped_user (a_reg A 24)).
  #[warnings="-notation-for-abbreviation"] Local Notation au := (rg_allocated_user (a_reg A 24)).
  #[warnings="-notation-for-abbreviation"] Local Notation mfa := (rg_mapped_fa (a_reg A 24)).
  #[warnings="-notation-for-abbreviation"] Local Notation nf := (Z.of_nat (length (rg_free (a_reg A 24)))).
  #[warnings="-notation-for-abbreviation"] Local Notation kk := (refill_count 24).
  #[warnings="-notation-for-abbreviation"] Local Notation size := (class_size 24).
  #[warnings="-notation-for-abbreviation"] Local Notation U := (pop_ums A 24).
  #[warnings="-notation-for-abbreviation"] Local Notation N := (pop_nc A 24).
  #[warnings="-notation-for-abbreviation"] Local Notation Fm := (pop_fam A 24).
  #[warnings="-notation-for-abbreviation"] Local Notation D' := (fst (depot_putC (a_depot A) key)).
  #[warnings="-notation-for-abbreviation"] Local Notation fid := (snd (depot_putC (a_depot A) key)).

  Let AI : @pa_ainv _ DepotRepL A m md. Proof. exact (proj1 PRE). Qed.
  Let W0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CR : 1 <= 24 <= 30. Proof. lia. Qed.
  Let N7R : 1 <= 7000 <= kMaxPrimaryUser. Proof. unfold kMaxPrimaryUser. lia. Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.
  Let MIv : mem_inv rsegs v. Proof. exact (proj1 (proj2 PRE)). Qed.
  (* [comment removed for export] *)
  Let PREF : alloc_ceiling <= lo /\ lo <= usp - 4096 /\ usp <= hi /\ hi <= 2^47 /\ usp mod 16 = 0 /\ bv_unsigned rac mod 2 = 0 /\
             stk rsegs v lo usp /\ mapped v usp (hi - usp) /\ usp <= stkobj /\ stkobj + 2064 <= hi.
  Proof.
    destruct PRE as (_ & _ & _ & _ & _ & CLO & LOSA & SAHI & HI47 & SPA & RAC2 & ST & SM & SOLO & SOHI & _). cbn [cl_segs LPA] in ST.
    exact (conj CLO (conj LOSA (conj SAHI (conj HI47 (conj SPA (conj RAC2 (conj ST (conj SM (conj SOLO SOHI))))))))).
  Qed.
  Let SAE : bv_unsigned spaw = sa.
  Proof. destruct PREF as (_ & _ & SAHI & HI47 & _). pose proof (zr_word spd) as X. unfold inr64 in X. apply unsigned_lit. lia. Qed.
  Let CEIL : alloc_ceiling <= sa - 1024. Proof. destruct PREF as (CLO & LOSA & _). lia. Qed.
  Let CEILw : alloc_ceiling <= bv_unsigned spaw - 1024. Proof. rewrite SAE. exact CEIL. Qed.
  Let EMP7 : pk_chunks (a_cache A (class_of 7000)) = []. Proof. rewrite class_of_7000. exact EMP. Qed.
  Let SHORT7 : Z.of_nat (length (rg_free (a_reg A (class_of 7000)))) < refill_count (class_of 7000). Proof. rewrite class_of_7000. exact SHORT. Qed.
  Let KS : Z.shiftr (max_count 24) 1 = kk. Proof. exact (proj1 (proj2 (proj2 (ar_k A 24 CR)))). Qed.

  #[warnings="-notation-for-abbreviation"] Local Notation CY := (carryF rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A p n0 stkobj key).
  #[warnings="-notation-for-abbreviation"] Local Notation RW := (regwF A).
  #[warnings="-notation-for-abbreviation"] Local Notation Wi := (fk_Wi spd A).
  #[warnings="-notation-for-abbreviation"] Local Notation Wfo := (fk_Wfo A p n0).
  #[warnings="-notation-for-abbreviation"] Local Notation LIN := (fk_lin rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation PLIN := (fk_plin rac spd m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation Wle := (fk_Wi_le spd A).
  #[warnings="-notation-for-abbreviation"] Local Notation Wmono := (fk_Wi_mono spd A).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_step := (carryF_step rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE).
  #[warnings="-notation-for-abbreviation"] Local Notation rw_step := (regwF_step rac spd A).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_statics := (fcy_statics rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_seal := (fcy_seal rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_na := (fcy_na rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_thr_mapped := (fcy_thr_mapped rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_tst := (fcy_tst rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_stm := (fcy_stm rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_mapped := (fcy_mapped rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A p n0 stkobj key).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_NN := (fcy_NN rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A p n0 stkobj key).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_fcells := (fcy_fcells rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_UMS := (fk_UMS rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_FAM := (fk_FAM rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_NC := (fk_NC rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_POS := (fk_POS rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_SHG := (fk_SHG rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_region := (fk_region rac spd m md A p n0 stkobj lo hi key PRE).
  #[warnings="-notation-for-abbreviation"] Local Notation f_regw_entry := (regwF_entry rac spd m md A p n0 stkobj lo hi key PRE).

  Variable T : TSet.
  #[warnings="-notation-for-abbreviation"] Local Notation e_par := (par_facts rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation e_seg := (seg_pre rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation HU := (pa_hull (popg A 24 (pop_ums A 24) 0 0)).
  #[warnings="-notation-for-abbreviation"] Local Notation HF := (pa_hull (popg A 24 (pop_ums A 24) (pop_fam A 24) 0)).
  #[warnings="-notation-for-abbreviation"] Local Notation HS := (pa_hull (popg A 24 (pop_ums A 24) (pop_fam A 24) (pop_nc A 24))).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation AgU := (popg A 24 (pop_ums A 24) 0 0).
  #[warnings="-notation-for-abbreviation"] Local Notation AgF := (popg A 24 (pop_ums A 24) (pop_fam A 24) 0).
  #[warnings="-notation-for-abbreviation"] Local Notation AgN := (popg A 24 (pop_ums A 24) (pop_fam A 24) (pop_nc A 24)).
  #[warnings="-notation-for-abbreviation"] Local Notation HLU := (pa_lhull (popg A 24 (pop_ums A 24) 0 0)).
  #[warnings="-notation-for-abbreviation"] Local Notation HLF := (pa_lhull (popg A 24 (pop_ums A 24) (pop_fam A 24) 0)).
  #[warnings="-notation-for-abbreviation"] Local Notation HLS := (pa_lhull (popg A 24 (pop_ums A 24) (pop_fam A 24) (pop_nc A 24))).
  #[warnings="-notation-for-abbreviation"] Local Notation GPp := (gp_post rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A p n0 stkobj lo key).
  #[warnings="-notation-for-abbreviation"] Local Notation GPk := (gpk rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A p n0 stkobj lo key).

  (* [comment removed for export] *)
  Hypothesis KEND : forall (Mk : mem) (mdk md' : Model) (v5 : mem) (junk0 pad scr : list byte) (ksc : list word)
      (tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 a0g na : word),
    (forall a, hidc HS a = true -> Mk a = m a) -> pop_mod AgN md mdk ->   (* [comment removed for export] *)
    MInv HS HLS (pa_eager (popg A 24 (pop_ums A 24) (pop_fam A 24) (pop_nc A 24))) md' -> same_but_materialized mdk md' ->
    (forall a, hidc HS a = true -> v5 a = None) ->
    GPk junk0 pad scr ksc na v5 ->
    srealizes rsegs
      (mkCfg (MS (mkR (wz gfa_popret) (wz uG) gp tp tq0 tq1 tq2 (wz R) (wz 0xb1d58) (wz 1) aq1 aq2 aq3 aq4 aq5 aq6 aq7
                     a0g (wz 2305843009213693952) (wz (free_array_of sb 24)) (wz (E + 16)) (wz kk)
                     (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 tq3 tq4 tq5 tq6)
                 F (wz gfa_popret) fc None (munrestrict (hidc HS) Mk v5) (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Ltac lin_open :=
    let L := fresh "L" in pose proof LIN as L;
    destruct L as (L1 & L2 & (Lt1 & Lt2 & Lt3 & Lt4) & (B1 & B2 & B3 & B4 & B5) & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) & (H1 & H2 & H3 & H4 & H5)).
  Tactic Notation "cv" constr(k) := split; [right; (let kn := lazymatch type of k with Z => eval cbv in (Z.to_nat k) | _ => k end in inside_at kn); lia|].
  Ltac sub_open := apply sub_fp_all_inside; unfold fk_Wi, fpop_Wq, free_array_of, kFreeArrayOffset, off_th_stats in *; cbn [app]; destruct (a_cache_inited A); (lazymatch goal with |- all_inside ?W' _ => let WW := fresh "WW" in set (WW := W') end); cbn [all_inside app].
  Ltac dj_tac := unfold fk_Wi, fpop_Wq, free_array_of, kFreeArrayOffset, off_th_stats in *; cbn [disjoint_from app]; try (destruct (a_cache_inited A));
                 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m spd rac Clg"] Lemma t_UMS0 : 0 <= 0 /\ 0 mod kUserMapSize = 0 /\ mu + 0 < au + 9 * size + kUserMapSize /\ au <= size * (Z.of_nat (length (a_paid A 24)) + 7) + class_slack 24.   (* [comment removed for export] *)
  Proof. pose proof (ar_reg A 24 W0 CR) as ((R1 & R2) & _). pose proof (ar_cap A 24 W0 CR EMP SHORT) as CAP. unfold kUserMapSize in *. split; [clear; hot_lia_full|]. split; [reflexivity|]. split; [clear - R2; hot_lia_full| exact CAP]. Qed.
  #[using="SHORT EMP PRE key hi lo stkobj n0 p md m spd rac Clg"] Lemma t_UMS : 0 <= U /\ U mod kUserMapSize = 0 /\ mu + U < au + 9 * size + kUserMapSize /\ au <= size * (Z.of_nat (length (a_paid A 24)) + 7) + class_slack 24. Proof. exact f_UMS. Qed.
  #[using="CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m spd rac Clg"] Lemma t_FAM0 : 0 <= 0 /\ 0 mod kFreeArrayMapSize = 0 /\ mfa + 0 <= 4 * (au / size) + kFreeArrayMapSize /\ mfa + 0 <= kFreeArraySize.   (* [comment removed for export] *)
  Proof. pose proof (ar_reg A 24 W0 CR) as (_ & _ & _ & _ & R5 & _ & _ & _ & R10 & _). unfold kFreeArrayMapSize in *. split; [clear; hot_lia_full|]. split; [reflexivity|]. split; [clear - R10; hot_lia_full| clear - R5; hot_lia_full]. Qed.
  #[using="SHORT EMP PRE key hi lo stkobj n0 p md m spd rac Clg"] Lemma t_FAM : 0 <= Fm /\ Fm mod kFreeArrayMapSize = 0 /\ mfa + Fm <= 4 * (au / size) + kFreeArrayMapSize /\ mfa + Fm <= kFreeArraySize. Proof. exact f_FAM. Qed.
  #[using="CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m spd rac Clg"] Lemma t_TAIL0 : forall ums, ums = 0 \/ ums = U -> mu + ums < au + 0 * size + 9 * size + kUserMapSize.
  Proof.
    intros ums Hu. (first [ pose proof (e_par) as dR_3; dand8 dR_3 as PU PU4 PU5 PN PF ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof e_par as (PU & PU4 & PU5 & PN & PF & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    pose proof (ar_reg A 24 W0 CR) as ((_ & R2) & _). unfold kUserMapSize. destruct Hu as [->| ->]; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="KEND CR SHORT EMP PRE hi"] Lemma grant_tail : forall (Rg : bvmap 5 word) (pc : word) (Mk : mem) (mdk : Model),
    (forall a, hidc HF a = true -> Mk a = m a) ->
    pop_mod AgF md mdk -> MInv HF HLF (pa_eager A + U + Fm) mdk ->   (* [comment removed for export] *)
    evt rsegs (fun st => exists junk0 pad scr ksc, GPp junk0 pad scr ksc st) (MS Rg F pc fc None (aview_of HF Mk) (seg_rom rsegs)) ->
    srealizes rsegs (mkCfg (MS Rg F pc fc None Mk (seg_rom rsegs)) mdk) T.
  Proof.
    intros Rg pc Mk mdk MSH PM HI EV. (first [ pose proof (PM) as dR_5; dand6 dR_5 as V LED COV TOP AMD HH | pose proof PM as (V & LED & COV & TOP & AMD & HH) ]).
    rewrite (popg_hull_nc A 24 U Fm 0 N) in MSH, HI, EV. rewrite (popg_lhull_nc A 24 U Fm 0 N) in HI.
    assert (PMN : pop_mod AgN md mdk).
    { refine (conj V (conj _ (conj COV (conj TOP (conj AMD HH))))). exact (aledger_reg _ _ _ (a_reg (popg A 24 U Fm N)) _ _ (fun c' _ => popg_mapped_nc A 24 U Fm N 0 c') LED). }
    eapply (srz_evt_restrict rsegs (pa_hull (popg A 24 U Fm N)) (hull_segsR _) pa_wxR _ (pa_eager A + U + Fm) _ _ mdk T HI HH).
    { rewrite restrict_MS. exact EV. }
    intros msr' md' Q HI' SB CL.
    (first [ dex21 Q as junk0 pad scr ksc tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 a0g na v5; destruct Q as [-> GPK] | dand23 Q as junk0 pad scr ksc tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 a0g na v5 -> GPK | destruct Q as (junk0 & pad & scr & ksc & tq0 & tq1 & tq2 & aq1 & aq2 & aq3 & aq4 & aq5 & aq6 & aq7 & tq3 & tq4 & tq5 & tq6 & a0g & na & v5 & -> & GPK) ]).
    rewrite unrestrict_MS. cbn [ms_mem] in CL |- *.
    assert (HI'' : MInv (pa_hull (popg A 24 U Fm N)) (pa_lhull (popg A 24 U Fm N)) (pa_eager (popg A 24 U Fm N)) md') by (rewrite (popg_eager A 24 U Fm N CR t_UMS t_FAM); exact HI').
    exact (KEND Mk mdk md' v5 junk0 pad scr ksc tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 a0g na MSH PMN HI'' SB CL GPK).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="spd rac"] Lemma tRBE : rbs = rb. Proof. unfold region_beg, kRegionSize. lia. Qed.
  Lemma hull_000 : pa_hull (popg A 24 0 0 0) = pa_hull A. Proof. rewrite popg_zero. reflexivity. Qed.
  Lemma lhull_000 : pa_lhull (popg A 24 0 0 0) = pa_lhull A. Proof. rewrite popg_zero. reflexivity. Qed.   (* [comment removed for export] *)
  #[using="CEILw CEIL SAE PREF CE CR W0 AI PRE key hi lo stkobj n0 p md m spd rac"] Lemma lhull_le_gen : forall u f x u' f' x', 0 <= u <= u' -> 0 <= f <= f' -> hull_le (pa_lhull (popg A 24 u f x)) (pa_lhull (popg A 24 u' f' x')).
  Proof.
    intros u f x u' f' x' Hu Hf.
    unfold pa_lhull, alhull_of, alhull_of_, alregions_. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec a_deadsh].
    rewrite !hull_of_app.
    apply hull_le_app2; [| apply hull_le_refl]. apply hull_le_app2; [apply hull_le_refl|]. apply hull_le_app2; [| apply hull_le_refl].
    apply lclasses_regions_le. intros c'. unfold reg_upd. (first [ pose proof ((wfR A W0)) as dR_7; dand3 dR_7 as WR WZ _ | destruct (wfR A W0) as (WR & WZ & _) ]).
    destruct (Z.eqb_spec c' 24) as [->|NE].
    - cbn [grow rg_mapped_user rg_mapped_fa]. (first [ pose proof ((WR 24 CR)) as dR_8; dand6 dR_8 as A1 _ _ _ A5 _ | destruct (WR 24 CR) as (A1 & _ & _ & _ & A5 & _) ]). lia.
    - destruct (Z_le_dec 1 c') as [L|L]; [destruct (Z_le_dec c' 30) as [L2|L2]|].
      + (first [ pose proof ((WR c' ltac:(lia))) as dR_9; dand6 dR_9 as A1 _ _ _ A5 _ | destruct (WR c' ltac:(lia)) as (A1 & _ & _ & _ & A5 & _) ]). lia.
      + rewrite (WZ c') by lia. cbn. lia.
      + rewrite (WZ c') by lia. cbn. lia.
  Qed.

  #[using="CEILw CEIL SAE PREF CE CR W0 AI PRE key hi lo stkobj n0 p md m spd rac"] Lemma hull_le_gen : forall u f x u' f' x', 0 <= u <= u' -> 0 <= f <= f' -> hull_le (pa_hull (popg A 24 u f x)) (pa_hull (popg A 24 u' f' x')).
  Proof.
    intros u f x u' f' x' Hu Hf.
    unfold pa_hull, ahull_of, ahull_of_, aregions_. cbn [popg set_cache_inited set_reg a_pl a_reg a_sec a_deadsh].
    rewrite !hull_of_app.
    apply hull_le_app2; [apply hull_le_refl|]. apply hull_le_app2; [| apply hull_le_refl].
    apply hull_le_app2; [apply hull_le_refl|]. apply hull_le_app2; [| apply hull_le_refl].
    apply classes_regions_le. intros c'. unfold reg_upd. (first [ pose proof ((wfR A W0)) as dR_7; dand3 dR_7 as WR WZ _ | destruct (wfR A W0) as (WR & WZ & _) ]).
    destruct (Z.eqb_spec c' 24) as [->|NE].
    - cbn [grow rg_mapped_user rg_mapped_fa]. (first [ pose proof ((WR 24 CR)) as dR_8; dand6 dR_8 as A1 _ _ _ A5 _ | destruct (WR 24 CR) as (A1 & _ & _ & _ & A5 & _) ]). lia.
    - destruct (Z_le_dec 1 c') as [L|L]; [destruct (Z_le_dec c' 30) as [L2|L2]|].
      + (first [ pose proof ((WR c' ltac:(lia))) as dR_9; dand6 dR_9 as A1 _ _ _ A5 _ | destruct (WR c' ltac:(lia)) as (A1 & _ & _ & _ & A5 & _) ]). lia.
      + rewrite (WZ c') by lia. cbn. lia.
      + rewrite (WZ c') by lia. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m spd rac"] Lemma newh_U : forall x, in_hullb HU x = true -> in_hullb (pa_hull A) x = false ->
    (rbs + mu <= x < rbs + mu + U) \/ (sh (rbs + mu) <= x < sh (rbs + mu) + U / 8).
  Proof.
    intros x X1 X0. rewrite tRBE.
    destruct (pop_hull_cases A 24 U 0 0 W0 CR t_UMS t_FAM0 x X1) as [OLD|[NU|[NS|[NF|NFS]]]].
    - rewrite OLD in X0. discriminate.
    - left. exact NU.
    - right. exact NS.
    - exfalso. lia.
    - exfalso. change (0 / 8) with 0 in NFS. lia.
  Qed.
  #[using="CEILw CEIL SAE PREF CE CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m spd rac"] Lemma newh_F : forall x, in_hullb HF x = true -> in_hullb HU x = false ->
    (rbs + kFreeArrayOffset + mfa <= x < rbs + kFreeArrayOffset + mfa + Fm) \/ (sh (rbs + kFreeArrayOffset + mfa) <= x < sh (rbs + kFreeArrayOffset + mfa) + Fm / 8).
  Proof.
    intros x X1 X0. rewrite tRBE.
    (first [ pose proof (e_par) as dR_10; dand7 dR_10 as (PU1 & _) _ _ _ _ ((R1 & _) & _) _ | pose proof e_par as ((PU1 & _) & _ & _ & _ & _ & ((R1 & _) & _) & _) ]). (first [ pose proof (f_SHG) as dR_11; dand3 dR_11 as S1 S2 _ | pose proof f_SHG as (S1 & S2 & _) ]).
    destruct (pop_hull_cases A 24 U Fm 0 W0 CR t_UMS t_FAM x X1) as [OLD|[NU|[NS|[NF|NFS]]]].
    - exfalso. rewrite (in_hullb_mono _ _ x (hull_le_gen 0 0 0 U 0 0 ltac:(lia) ltac:(lia)) ltac:(rewrite hull_000; exact OLD)) in X0. discriminate.
    - exfalso. rewrite (pop_vis_user A 24 U 0 0 CR ltac:(lia) x ltac:(lia)) in X0. discriminate.
    - exfalso. assert (D0 : 0 <= mu / 8) by (apply Z.div_pos; lia).
      destruct (Z.eq_dec U 0) as [E0|NE0]; [rewrite E0 in NS; change (0 / 8) with 0 in NS; lia|].
      rewrite (pop_vis_ush A 24 U 0 0 W0 CR t_UMS t_FAM0 ltac:(lia) x ltac:(lia)) in X0. discriminate.
    - left. exact NF.
    - right. exact NFS.
  Qed.

  (* [comment removed for export] *)
  #[using="CEILw CEIL SAE PREF CE CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m spd rac"] Lemma WF_gen : forall u f, (u = 0 /\ f = 0) \/ (u = U /\ (f = 0 \/ f = Fm)) -> WF (popg A 24 u f 0).
  Proof.
    intros u f Huf.
    (first [ pose proof (e_par) as dR_12; dand8 dR_12 as PU PU4 PU5 (PN1 & PN2 & PN3 & PN4) (PF1 & PF2 & PF3 & PF4) ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof e_par as (PU & PU4 & PU5 & (PN1 & PN2 & PN3 & PN4) & (PF1 & PF2 & PF3 & PF4) & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    assert (Hu : u = 0 \/ u = U) by (destruct Huf as [[X _]|[X _]]; [left| right]; exact X).
    assert (Hf : f = 0 \/ f = Fm) by (destruct Huf as [[_ X]|[_ X]]; [left; exact X| exact X]).
    assert (UMSx : 0 <= u /\ u mod kUserMapSize = 0 /\ mu + u < au + 9 * size + kUserMapSize /\ au <= size * (Z.of_nat (length (a_paid A 24)) + 7) + class_slack 24) by (destruct Hu as [->| ->]; [exact t_UMS0| exact t_UMS]).
    assert (FAMx : 0 <= f /\ f mod kFreeArrayMapSize = 0 /\ mfa + f <= 4 * (au / size) + kFreeArrayMapSize /\ mfa + f <= kFreeArraySize) by (destruct Hf as [->| ->]; [exact t_FAM0| exact t_FAM]).
    assert (NCx : 0 <= 0 /\ au + 0 * size <= mu + u /\ 4 * (nf + 0) <= mfa + f) by (destruct UMSx as (U0 & _); destruct FAMx as (F0 & _); lia).
    assert (POSx : mu + u = 0 -> f = 0 /\ 0 = 0).
    { intros Z0. split; [| reflexivity]. destruct Huf as [[_ X]|[X1 X2]]; [exact X|]. subst u. destruct X2 as [X|X]; [exact X|].
      pose proof (f_POS Z0) as [Y _]. rewrite X. exact Y. }
    exact (pop_WF A 24 u f 0 W0 CR UMSx FAMx NCx POSx ltac:(destruct Hu as [->| ->]; [exact (t_TAIL0 0 (or_introl eq_refl))| exact (t_TAIL0 U (or_intror eq_refl))])).
  Qed.
  #[using="CEILw CEIL SAE PREF CE CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m spd rac"] Lemma cover_gen : forall u f mdx, (u = 0 /\ f = 0) \/ (u = U /\ (f = 0 \/ f = Fm)) ->
    pop_mod (popg A 24 u f 0) md mdx ->
    forall (H0x : hull) l0 h0, In (l0, h0) (pa_hull (popg A 24 u f 0)) ->
      iv_sub H0x l0 h0 \/ iv_sub (pa_lhull (popg A 24 u f 0)) l0 h0 \/ lazy_free (m_vm_lazy mdx) l0 h0.
  Proof.
    intros u f mdx Huf (_ & LED & _) H0x l0 h0 Hin. right. exact (ahull_cover (popg A 24 u f 0) mdx (WF_gen u f Huf) LED l0 h0 Hin).
  Qed.
  #[using="CEILw CEIL SAE PREF CE CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m spd rac"] Lemma room_gen : forall u f, (u = 0 /\ f = 0) \/ (u = U /\ (f = 0 \/ f = Fm)) -> pa_eager A + u + f + hull_bytes (pa_lhull (popg A 24 u f 0)) + (2^30 + 2^28) <= p_tlim (a_pl A).   (* [comment removed for export] *)
  Proof.
    intros u f Huf. pose proof (WF_gen u f Huf) as WFx.
    (first [ pose proof (e_par) as dR_12; dand8 dR_12 as PU PU4 PU5 (PN1 & PN2 & PN3 & PN4) (PF1 & PF2 & PF3 & PF4) ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof e_par as (PU & PU4 & PU5 & (PN1 & PN2 & PN3 & PN4) & (PF1 & PF2 & PF3 & PF4) & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    assert (Hu : u = 0 \/ u = U) by (destruct Huf as [[X _]|[X _]]; [left| right]; exact X).
    assert (Hf : f = 0 \/ f = Fm) by (destruct Huf as [[_ X]|[_ X]]; [left; exact X| exact X]).
    assert (UMSx : 0 <= u /\ u mod kUserMapSize = 0 /\ mu + u < au + 9 * size + kUserMapSize /\ au <= size * (Z.of_nat (length (a_paid A 24)) + 7) + class_slack 24) by (destruct Hu as [->| ->]; [exact t_UMS0| exact t_UMS]).
    assert (FAMx : 0 <= f /\ f mod kFreeArrayMapSize = 0 /\ mfa + f <= 4 * (au / size) + kFreeArrayMapSize /\ mfa + f <= kFreeArraySize) by (destruct Hf as [->| ->]; [exact t_FAM0| exact t_FAM]).
    assert (NCx : 0 <= 0 /\ au + 0 * size <= mu + u /\ 4 * (nf + 0) <= mfa + f) by (destruct UMSx as (U0 & _); destruct FAMx as (F0 & _); lia).
    pose proof (wf_budget_room (popg A 24 u f 0) WFx (ai_extra _ _ _ _ _ _ _ AI)) as ROOM. unfold kBudgetRoom in ROOM. change (p_tlim (a_pl (popg A 24 u f 0))) with (p_tlim (a_pl A)) in ROOM.
    change (aeager_of (popg A 24 u f 0)) with (pa_eager (popg A 24 u f 0)) in ROOM. rewrite (popg_eager A 24 u f 0 CR UMSx FAMx) in ROOM. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CEILw CEIL SAE PREF CE W0 AI PRE hi lo md"] Lemma shadow_present : forall (H0x H1x : hull) (beg len : Z) (Mk w : mem) (junk0 pad scr : list byte) (ksc : list word) (u f x : Z),
    hull_le (pa_hull A) H0x -> (forall a, hidc H0x a = true -> Mk a = m a) -> CY junk0 pad scr ksc u f x w ->
    kHighMemBeg <= beg /\ beg + len <= 2^47 /\ 0 < len ->
    sh sb <= sh beg /\ sh beg + len / 8 <= sh sb + kSpaceSize / 8 /\ kLowShadowMapBeg <= sh beg /\ sh beg + len / 8 <= kHighMemBeg ->
    (forall z, sh beg <= z < sh beg + len / 8 -> in_hullb H1x z = true) ->
    (forall z, sh beg <= z < sh beg + len / 8 -> in_hullb H0x z = true -> in_hullb (pa_hull A) z = true) ->
    mapped (mrestrict (hidc H1x) (apply_zeros (munrestrict (hidc H0x) Mk w) [(wz beg, wz len)])) (sh beg) (len / 8).
  Proof.
    (intros H0x H1x beg len Mk w junk0 pad scr ksc u f x HLE MSH CYw FEB; (first [ intro dR_33; dand4 dR_33 as G1 G2 G3 G4 | intros (G1 & G2 & G3 & G4) ]); intros VIS1 OLDV i Hi).
    set (z := sh beg + i). assert (Hz : sh beg <= z < sh beg + len / 8) by (unfold z; lia).
    assert (Z64 : 0 <= z < 2^64) by (unfold kLowShadowMapBeg, kHighMemBeg in *; lia).
    assert (GH : m (wz z) <> None).
    { destruct (ai_hidden _ _ _ _ _ _ _ AI) as [HH1 _]. exact (proj1 (HH1 z (prim_shadow_ghost A W0 z ltac:(lia)))). }
    unfold mrestrict, hidc. rewrite unsigned_lit by exact Z64. rewrite (VIS1 z Hz). cbn [negb].
    destruct (in_hullb (pa_hull A) z) eqn:VA.
    - (* [comment removed for export] *)
      rewrite (sw_zspec H0x beg len Mk w FEB). unfold in_range. rewrite unsigned_lit by exact Z64.
      replace ((beg <=? z) && (z <? beg + len)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; unfold kHighMemBeg in *; lia).
      unfold munrestrict, hidc. rewrite unsigned_lit by exact Z64. rewrite (in_hullb_mono _ _ z HLE VA). cbn [negb].
      apply (cy_NN _ _ _ _ _ _ _ w CYw z); [lia| right; unfold kLowShadowMapBeg in *; lia| lia|].
      unfold aview_of, mrestrict, hidc. rewrite unsigned_lit by exact Z64. rewrite VA. exact GH.
    - (* [comment removed for export] *)
      destruct (in_hullb H0x z) eqn:V0; [rewrite (OLDV z Hz V0) in VA; discriminate|].
      rewrite (sw_zspec H0x beg len Mk w FEB). unfold in_range. rewrite unsigned_lit by exact Z64.
      replace ((beg <=? z) && (z <? beg + len)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; unfold kHighMemBeg in *; lia).
      unfold munrestrict, hidc. rewrite unsigned_lit by exact Z64. rewrite V0. cbn [negb].
      rewrite (MSH (wz z)); [exact GH|]. unfold hidc. rewrite unsigned_lit by exact Z64. rewrite V0. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma mod4096_of : forall x, x mod 262144 = 0 -> x mod 4096 = 0.
  Proof. intros x Hx. apply (mod0_down _ 262144 4096); [exists 64; reflexivity| exact Hx]. Qed.
  #[using="SHORT EMP PRE key hi lo stkobj n0 p md m spd rac Clg"] Lemma rbs_mod : rbs mod 4096 = 0.
  Proof.
    (first [ pose proof (e_seg) as dR_13; dand11 dR_13 as _ _ _ _ _ _ _ _ _ SBAL _ | pose proof e_seg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SBAL & _) ]).
    rewrite Z.add_mod, SBAL by lia. replace (24 * 4294967296) with (24 * 1048576 * 4096) by lia. rewrite Z_mod_mult. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CEILw CEIL SAE PREF CE PRE key hi lo stkobj n0 p md m spd rac Clg"] Lemma sh_prim_range : forall x l, sb <= x -> x + l <= sb + kSpaceSize -> 0 <= l -> sh sb <= sh x /\ sh x + l / 8 <= sh sb + kSpaceSize / 8.
  Proof.
    intros x l H1 H2 H3. unfold sh, kSpaceSize in *. change (2^37 / 8) with 17179869184.
    pose proof (Z_div_mod_eq_full x 8) as E1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1.
    pose proof (Z_div_mod_eq_full l 8) as E2. pose proof (Z.mod_pos_bound l 8 ltac:(lia)) as M2.
    pose proof (Z_div_mod_eq_full sb 8) as E3. pose proof (Z.mod_pos_bound sb 8 ltac:(lia)) as M3.
    lia.
  Qed.

  Definition pk_Wg1 : list (Z * Z) := [(rb + mu, rb + mu + U); (sh (rb + mu), sh (rb + mu) + U / 8)].
  Definition pk_Wg2 : list (Z * Z) := [(fa + mfa, fa + mfa + Fm); (sh (fa + mfa), sh (fa + mfa) + Fm / 8)].
  #[using="CE SHORT EMP PRE key hi lo stkobj n0 p md m rac"] Lemma pk_WG1 : sub_fp pk_Wg1 (Wi U 0 0) /\ disjoint_from pk_Wg1 (sa - 336) 336 /\ disjoint_from pk_Wg1 R 8 /\ disjoint_from pk_Wg1 (thr + 288) 2480 /\
    disjoint_from pk_Wg1 (R + 16) 64 /\ (forall a l, alloc_ceiling <= a -> disjoint_from pk_Wg1 a l).
  Proof.
    (first [ pose proof (e_seg) as dR_14; dand14 dR_14 as _ _ _ _ _ _ _ _ _ _ SEP_tr SEP_rs SEP_ts _ | pose proof e_seg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEP_tr & SEP_rs & SEP_ts & _) ]).
    lin_open. unfold pk_Wg1.
    split; [sub_open; (cv 8; cv 9; exact I)|].
    split; [dj_tac|]. split; [dj_tac|]. split; [dj_tac|]. split; [dj_tac|]. intros a l Hal. dj_tac.
  Qed.
  #[using="CE SHORT EMP PRE key hi lo stkobj n0 p md m rac"] Lemma pk_WG2 : sub_fp pk_Wg2 (Wi U Fm 0) /\ disjoint_from pk_Wg2 (sa - 336) 336 /\ disjoint_from pk_Wg2 R 8 /\ disjoint_from pk_Wg2 (thr + 288) 2480 /\
    disjoint_from pk_Wg2 (R + 16) 64 /\ (forall a l, alloc_ceiling <= a -> disjoint_from pk_Wg2 a l) /\ disjoint_from pk_Wg2 (sh (rb + mu)) (U / 8).
  Proof.
    (first [ pose proof (e_seg) as dR_15; dand14 dR_15 as _ _ _ _ _ _ _ _ _ _ SEP_tr SEP_rs SEP_ts _ | pose proof e_seg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEP_tr & SEP_rs & SEP_ts & _) ]).
    lin_open. unfold pk_Wg2.
    split; [sub_open; (cv 10; cv 11; exact I)|].
    split; [dj_tac|]. split; [dj_tac|]. split; [dj_tac|]. split; [dj_tac|]. split; [intros a l Hal; dj_tac| dj_tac].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation nmv := (round_up (4 * (nf + N)) kFaMap).
  #[warnings="-notation-for-abbreviation"] Local Notation fev := (rbs + kFreeArrayOffset + mfa).
  #[warnings="-notation-for-abbreviation"] Local Notation FRPc a0h := (pop_frame (wz kk) (wz (E + 16)) (wz (free_array_of sb 24)) (wz 2305843009213693952) a0h (wz 0xb1d58) (wz R) (wz gfa_popret)).
  #[warnings="-notation-for-abbreviation"] Local Notation FREc scr2 := (efas_frame scr2 (wz N) (wz rbs) (wz (nf + N)) (wz R) (wz pop_efasret)).
  #[warnings="-notation-for-abbreviation"] Local Notation FRM2c scrM := (mapcb_frame scrM (wz (mu + U - au)) (wz R) (wz (nmv - mfa)) fev (nmv - mfa) (wz fev) (wz nmv) (wz efas_mapret)).
  #[warnings="-notation-for-abbreviation"] Local Notation e_D := (pop_D rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).

  #[using="KEND CEILw CEIL SAE PREF CE CR W0 AI SHORT EMP NQ HL PRE hi"] Lemma node2 : forall (junk0 pad scr scr2 scrM : list byte) (ksc : list word) (a0h s6v t0' t1' t2' a6' t3' t4' t5' t6' : word) (Mk w : mem) (mdk : Model),
    mfa < 4 * (nf + N) ->
    (forall a, hidc HU a = true -> Mk a = m a) -> pop_mod AgU md mdk -> MInv HU HLU (pa_eager A + U) mdk ->   (* [comment removed for export] *)
    (forall a, hidc HU a = true -> w a = None) ->
    CY junk0 pad scr ksc U 0 0 w -> RW nf mfa au (mu + U) w -> stk rsegs w lo (uG + -64 + -48 + -128) ->
    rw_cells rsegs w (uG + -64) (FRPc a0h) -> rw_cells rsegs w (uG + -64 + -48) (FREc scr2) -> rw_cells rsegs w (uG + -64 + -48 + -128) (FRM2c scrM) ->
    mapped w (rb + mu) U -> bytes_at rsegs w (sh (rb + mu)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (U / 8))) ->
    srealizes rsegs
      (mkCfg (MSsvc (mkR (wz mapfixed_resume) (wz (uG + -64 + -48 + -128)) gp tp t0' t1' t2' (wz (nmv - mfa)) (wz 1) (wz fev) (wz (nmv - mfa)) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                        (wz fev) (wz efas_name) (wz PSC) (wz size) s6v (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
                   F (wz mmap_ecall_pc) (wz 222) fc None (munrestrict (hidc HU) Mk w) (seg_rom rsegs)) mdk)
      T.
  Proof.
    intros junk0 pad scr scr2 scrM ksc a0h s6v t0' t1' t2' a6' t3' t4' t5' t6' Mk w mdk NEEDMAP MSH PM HI CL CYw RWw STw FRP FRE FRM NEWU SHU.
    (first [ pose proof (e_par) as dR_16; dand8 dR_16 as PU PU4 PU5 (PN1 & PN2 & PN3 & PN4) (PF1 & PF2 & PF3 & PF4) ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof e_par as (PU & PU4 & PU5 & (PN1 & PN2 & PN3 & PN4) & (PF1 & PF2 & PF3 & PF4) & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    (first [ pose proof (e_seg) as dR_17; dand16 dR_17 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof e_seg as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    assert (EF : Fm = nmv - mfa) by (destruct (ar_fam_cases A 24) as [[_ X]|[X _]]; [lia| exact X]).
    assert (F0 : 0 < Fm) by ((first [ pose proof ((ar_fam A 24 W0 CR EMP SHORT)) as dR_18; dand3 dR_18 as _ X _ | pose proof (ar_fam A 24 W0 CR EMP SHORT) as (_ & X & _) ]); lia).
    pose proof tRBE as RBEq. lin_open.
    assert (FEQ : fev = fa + mfa) by (rewrite RBEq; reflexivity).
    assert (RANGE : a_sb A <= fev /\ fev + (nmv - mfa) <= a_sb A + kSpaceSize + 4096 /\ fev mod 4096 = 0 /\ (nmv - mfa) mod 4096 = 0 /\ 0 < nmv - mfa).
    { rewrite <- EF. split; [unfold kFreeArrayOffset; lia|]. split; [unfold kFreeArrayOffset, kSpaceSize; lia|].
      split; [| split; [apply mod4096_of; exact PF2| exact F0]].
      rewrite Z.add_mod, (mod4096_of mfa R7), Z.add_0_r, Z.mod_mod by lia. rewrite Z.add_mod, rbs_mod by lia. reflexivity. }
    assert (BR : pa_eager A + U + (nmv - mfa) + hull_bytes HLU <= p_tlim (a_pl A)).
    { pose proof (room_gen U 0 (or_intror (conj eq_refl (or_introl eq_refl)))) as X. rewrite <- EF. unfold kFreeArraySize in *. lia. }
    pose proof (hull_le_gen U 0 0 U Fm 0 ltac:(lia) ltac:(lia)) as HLE. pose proof (lhull_le_gen U 0 0 U Fm 0 ltac:(lia) ltac:(lia)) as LHLE.
    assert (FEB : kHighMemBeg <= fev /\ fev + (nmv - mfa) <= 2^47 /\ 0 < nmv - mfa) by (rewrite <- EF; unfold kHighMemBeg, kFreeArrayOffset; lia).
    assert (VISN : forall x, fev <= x < fev + (nmv - mfa) -> in_hullb HF x = true).
    { intros x Hx. rewrite <- EF in Hx. apply (pop_vis_fa A 24 U Fm 0 CR ltac:(lia)). rewrite FEQ in Hx. lia. }
    eapply (fpop_node A m md AI mdk HU HLU (pa_eager A + U) fev (nmv - mfa) AgU eq_refl eq_refl PM HI RANGE BR).
    - (* [comment removed for export] *)
      cbv zeta. intros HI2 PM2 LZ2.
      set (md2 := commit_model (wz 50) (wz fev) (wz (nmv - mfa)) false mdk) in *.
      (* [comment removed for export] *)
      assert (PMF2 : pop_mod AgF md md2).
      { apply (pop_mod_grow AgU AgF md md2 fev (nmv - mfa) eq_refl eq_refl ltac:(lia)); [| exact PM2| exact LZ2].
        intros c' Hc'. cbn [popg set_cache_inited set_reg a_reg a_pl]. unfold reg_upd.
        destruct (Z.eqb_spec c' 24) as [->|NE]; cbn [grow rg_mapped_user rg_mapped_fa]; [| split; left; reflexivity].
        split; [left; reflexivity| right]. split; [| clear - EF; lia].
        clear - RBEq. unfold region_beg, a_sb, kRegionSize in *. cbn [a_pl popg set_cache_inited set_reg] in *. lia. }
      (first [ pose proof (CYw) as dR_19; dand4 dR_19 as _ _ MIw _ | pose proof CYw as (_ & _ & MIw & _) ]).
      assert (SHGEO : sh sb <= sh fev /\ sh fev + (nmv - mfa) / 8 <= sh sb + kSpaceSize / 8 /\ kLowShadowMapBeg <= sh fev /\ sh fev + (nmv - mfa) / 8 <= kHighMemBeg).
      { destruct (sh_prim_range fev (nmv - mfa) ltac:(unfold kFreeArrayOffset; lia) ltac:(rewrite <- EF; unfold kFreeArrayOffset, kSpaceSize; lia) ltac:(lia)) as [G1 G2].
        split; [exact G1|]. split; [exact G2|]. rewrite <- EF, FEQ. unfold kLowShadowMapBeg, kHighMemBeg, kFreeArrayOffset in *. lia. }
      pose proof (sw_munch HU HF fev (nmv - mfa) Mk w HLE ltac:(rewrite <- EF; exact newh_F) FEB CL) as MU2.
      pose proof (sw_wmono HU HF fev (nmv - mfa) Mk w HLE FEB CL) as WM2.
      pose proof (sw_mem_inv HU HF fev (nmv - mfa) Mk w ltac:(rewrite <- EF; exact newh_F) FEB (conj (proj1 (proj2 (proj2 SHGEO))) (proj2 (proj2 (proj2 SHGEO)))) MIw) as MI2.
      assert (MSF : mapped (mrestrict (hidc HF) (apply_zeros (munrestrict (hidc HU) Mk w) [(wz fev, wz (nmv - mfa))])) (sh fev) ((nmv - mfa) / 8)).
      { apply (shadow_present HU HF fev (nmv - mfa) Mk w junk0 pad scr ksc U 0 0 (popg_hull_le A 24 U 0 0 W0 CR t_UMS t_FAM0) MSH CYw FEB SHGEO).
        - intros z Hz. rewrite <- EF, FEQ in Hz. (first [ pose proof (f_SHG) as dR_20; dand5 dR_20 as _ _ S3 S4 _ | pose proof f_SHG as (_ & _ & S3 & S4 & _) ]).
          assert (D0 : 0 <= mfa / 8) by (apply Z.div_pos; lia).
          apply (pop_vis_fsh A 24 U Fm 0 W0 CR t_UMS t_FAM ltac:(lia)). lia.
        - intros z Hz V0. rewrite <- EF, FEQ in Hz.
          destruct (pop_hull_cases A 24 U 0 0 W0 CR t_UMS t_FAM0 z V0) as [OLD|[NU|[NS|[NFx|NFSx]]]]; [exact OLD| exfalso; unfold kFreeArrayOffset in *; lia| exfalso; unfold kFreeArrayOffset in *; lia| exfalso; lia| exfalso; change (0 / 8) with 0 in NFSx; lia]. }
      assert (ZNF : mapped (mrestrict (hidc HF) (apply_zeros (munrestrict (hidc HU) Mk w) [(wz fev, wz (nmv - mfa))])) (fa + mfa) Fm).
      { intros i Hi. rewrite <- FEQ. rewrite (sw_zero HU HF fev (nmv - mfa) Mk w FEB VISN (fev + i) ltac:(lia)). discriminate. }
      set (M2 := apply_zeros (munrestrict (hidc HU) Mk w) [(wz fev, wz (nmv - mfa))]) in *.
      set (w2 := mrestrict (hidc HF) M2) in *.
      rewrite <- EF in MU2. rewrite FEQ in MU2. change (munch pk_Wg2 w w2) in MU2.
      (first [ dand7 pk_WG2 as SUB DF DR DL DRW DHI DSH | destruct pk_WG2 as (SUB & DF & DR & DL & DRW & DHI & DSH) ]).
      apply (grant_tail _ _ M2 md2).
      + intros a Ha. unfold M2. rewrite (sw_hidden HU HF fev (nmv - mfa) Mk w HLE FEB VISN a Ha). apply MSH. exact (hidc_grow_le HU HF HLE a Ha).
      + exact PMF2.
      + apply (MInv_hull_mono HU HLU HF HLF (pa_eager A + U + (nmv - mfa)) _ md2 HI2 LHLE (cover_gen U Fm md2 (or_intror (conj eq_refl (or_intror eq_refl))) PMF2 HU)); [lia|].
        destruct PM2 as ((_ & _ & VL & _) & _). rewrite VL. (first [ pose proof ((ai_ledger _ _ _ _ _ _ _ AI)) as dR_22; dand6 dR_22 as _ _ _ _ L5 _ | destruct (ai_ledger _ _ _ _ _ _ _ AI) as (_ & _ & _ & _ & L5 & _) ]). rewrite L5.
        pose proof (room_gen U Fm (or_intror (conj eq_refl (or_intror eq_refl)))) as X. lia.
      + change (aview_of HF M2) with w2.
        eapply evt_mono; [| intros st' PO; exists junk0, pad, scr, ksc; exact PO].
        apply (e_D t0' t1' t2' a6' s6v t3' t4' t5' t6' a0h junk0 pad scr scr2 scrM (rdbytes w2 (sh fev) (Z.to_nat ((nmv - mfa) / 8))) ksc w2 NEEDMAP).
        * exact (cy_step _ _ _ _ U 0 0 U Fm 0 _ w w2 CYw MU2 WM2 MI2 (Wmono U 0 0 U Fm 0 ltac:(lia) ltac:(lia) ltac:(lia)) SUB DF DR DL).
        * exact (rw_step _ _ _ _ _ w w2 RWw MU2 WM2 DRW).
        * apply (stk_transport_disjoint rsegs _ w w2 _ _ STw MU2 WM2). apply DHI. lia.
        * eapply rw_cells_transport; [exact FRP| exact MU2| exact WM2| apply DHI; lia].
        * eapply rw_cells_transport; [exact FRE| exact MU2| exact WM2| apply DHI; lia].
        * eapply rw_cells_transport; [exact FRM| exact MU2| exact WM2| apply DHI; lia].
        * apply (pk_mapped_wm w w2 _ _ WM2); [lia| right; lia| lia| exact NEWU].
        * eapply bytes_at_transport; [exact SHU| exact MU2|]. rewrite repeat_length, Z2Nat.id by lia. exact DSH.
        * assert (K0' : 0 <= (nmv - mfa) / 8) by (apply Z.div_pos; lia).
          apply OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopP.APopK.mapped_CB; [rewrite Z2Nat.id by lia; exact MSF| unfold kLowShadowMapBeg in *; lia| rewrite Z2Nat.id by lia; unfold kHighMemBeg in *; lia].
        * exact ZNF.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation EPp := (ep_post rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A p n0 stkobj lo key).
  #[warnings="-notation-for-abbreviation"] Local Notation PM2p := (pm2_post rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A p n0 stkobj lo key).
  #[warnings="-notation-for-abbreviation"] Local Notation e_Cfast := (pop_C_fast rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation e_Cmap := (pop_C_map rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).

  #[using="KEND CEILw CEIL SAE PREF CE CR W0 AI SHORT EMP NQ HL PRE hi"] Lemma c_stage : forall (Rg : bvmap 5 word) (pc : word) (Mk : mem) (mdk : Model),
    (forall a, hidc HU a = true -> Mk a = m a) -> pop_mod AgU md mdk -> MInv HU HLU (pa_eager A + U) mdk ->   (* [comment removed for export] *)
    evt rsegs (fun st => exists junk0 pad scr ksc a0h, EPp junk0 pad scr ksc a0h st) (MS Rg F pc fc None (aview_of HU Mk) (seg_rom rsegs)) ->
    srealizes rsegs (mkCfg (MS Rg F pc fc None Mk (seg_rom rsegs)) mdk) T.
  Proof.
    intros Rg pc Mk mdk MSH PM HI EV.
    destruct (Z.leb_spec (4 * (nf + N)) mfa) as [FAST|NEED].
    - (* [comment removed for export] *)
      assert (F0 : Fm = 0) by (destruct (ar_fam_cases A 24) as [[X _]|[_ X]]; [exact X| lia]).
      pose proof (grant_tail Rg pc Mk mdk) as GT. rewrite F0, Z.add_0_r in GT. apply GT; [exact MSH| exact PM| exact HI|].
      eapply evt_cut; [exact EV|].
      (intros st; (first [ intro dR_34; dex18 dR_34 as junk0 pad scr ksc a0h t0' t1' t2' a4' a5' a6' a7' s6' t3' t4' t5' t6' w'; dand7 dR_34 as -> CYw RWw STw FRP NEWU SHU | intro dR_34; dand25 dR_34 as junk0 pad scr ksc a0h t0' t1' t2' a4' a5' a6' a7' s6' t3' t4' t5' t6' w' -> CYw RWw STw FRP NEWU SHU | intros (junk0 & pad & scr & ksc & a0h & t0' & t1' & t2' & a4' & a5' & a6' & a7' & s6' & t3' & t4' & t5' & t6' & w' & -> & CYw & RWw & STw & FRP & NEWU & SHU) ])).
      eapply evt_mono; [exact (e_Cfast t0' t1' t2' a4' a5' a6' a7' s6' t3' t4' t5' t6' a0h junk0 pad scr ksc w' FAST CYw RWw STw FRP NEWU SHU)|].
      intros st' PO. exists junk0, pad, scr, ksc. exact PO.
    - (* [comment removed for export] *)
      (first [ pose proof (PM) as dR_23; dand6 dR_23 as _ _ _ _ _ HH | pose proof PM as (_ & _ & _ & _ & _ & HH) ]).
      eapply (srz_evt_restrict rsegs HU (hull_segsR _) pa_wxR _ (pa_eager A + U) (fun st => exists junk0 pad scr ksc a0h s6v, PM2p junk0 pad scr ksc a0h s6v st) _ mdk _ HI HH).
      { rewrite restrict_MS. eapply evt_cut; [exact EV|].
        (intros st; (first [ intro dR_35; dex18 dR_35 as junk0 pad scr ksc a0h t0' t1' t2' a4' a5' a6' a7' s6' t3' t4' t5' t6' w'; dand7 dR_35 as -> CYw RWw STw FRP NEWU SHU | intro dR_35; dand25 dR_35 as junk0 pad scr ksc a0h t0' t1' t2' a4' a5' a6' a7' s6' t3' t4' t5' t6' w' -> CYw RWw STw FRP NEWU SHU | intros (junk0 & pad & scr & ksc & a0h & t0' & t1' & t2' & a4' & a5' & a6' & a7' & s6' & t3' & t4' & t5' & t6' & w' & -> & CYw & RWw & STw & FRP & NEWU & SHU) ])).
        eapply evt_mono; [exact (e_Cmap t0' t1' t2' a4' a5' a6' a7' s6' t3' t4' t5' t6' a0h junk0 pad scr ksc w' NEED CYw RWw STw FRP NEWU SHU)|].
        intros st' PO. exists junk0, pad, scr, ksc, a0h, s6'. exact PO. }
      (intros msr' md'; (first [ intro dR_36; dex6 dR_36 as junk0 pad scr ksc a0h s6v; rename dR_36 into Q | intro dR_36; dand7 dR_36 as junk0 pad scr ksc a0h s6v Q | intros (junk0 & pad & scr & ksc & a0h & s6v & Q) ]); intros HI' SB CL).
      (first [ dex11 Q as t0' t1' t2' a6' t3' t4' t5' t6' scr2 scrM w'; dand9 Q as -> CYw RWw STw FRP FRE FRM NEWU SHU | dand20 Q as t0' t1' t2' a6' t3' t4' t5' t6' scr2 scrM w' -> CYw RWw STw FRP FRE FRM NEWU SHU | destruct Q as (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & scr2 & scrM & w' & -> & CYw & RWw & STw & FRP & FRE & FRM & NEWU & SHU) ]).
      rewrite unrestrict_MSsvc. cbn [ms_mem] in CL |- *.
      exact (node2 junk0 pad scr scr2 scrM ksc a0h s6v t0' t1' t2' a6' t3' t4' t5' t6' Mk w' md' NEED MSH (pop_mod_sbm_any _ md mdk md' PM SB) HI' CL CYw RWw STw FRP FRE FRM NEWU SHU).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation e_B := (pop_B rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).

  #[using="KEND CEILw CEIL SAE PREF CE N7R CR W0 AI SHAPE SHORT EMP NQ HL PRE hi"] Lemma node1 : forall (junk0 pad scr scrM : list byte) (ksc : list word) (a0h t0' t1' t2' a6' t3' t4' t5' t6' : word) (w : mem) (mdk : Model),
    mu < au + (kk - nf) * size ->
    pop_mod A md mdk -> MInv (pa_hull A) (pa_lhull A) (pa_eager A) mdk ->
    (forall a, hidc (pa_hull A) a = true -> w a = None) ->
    CY junk0 pad scr ksc 0 0 0 w -> RW nf mfa au mu w -> stk rsegs w lo (uG + -64 + -128) ->
    rw_cells rsegs w (uG + -64) (FRPc a0h) ->
    rw_cells rsegs w (uG + -64 + -128) (mapcb_frame scrM (wz (rbs + mu)) (wz U) (wz rbs) (rbs + mu) U (wz (C + 2560)) (wz R) (wz pop_mapret)) ->
    srealizes rsegs
      (mkCfg (MSsvc (mkR (wz mapfixed_resume) (wz (uG + -64 + -128)) gp tp t0' t1' t2' (wz U) (wz 1) (wz (rbs + mu)) (wz U) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                        (wz (rbs + mu)) (wz pop_name) (wz PSC) (wz size) (wz 0xb1d58) (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 t3' t4' t5' t6')
                   F (wz mmap_ecall_pc) (wz 222) fc None (munrestrict (hidc (pa_hull A)) m w) (seg_rom rsegs)) mdk)
      T.
  Proof.
    intros junk0 pad scr scrM ksc a0h t0' t1' t2' a6' t3' t4' t5' t6' w mdk NOFIT PM HI CL CYw RWw STw FRP FRM.
    (first [ pose proof (e_par) as dR_25; dand8 dR_25 as PU PU4 PU5 (PN1 & PN2 & PN3 & PN4) (PF1 & PF2 & PF3 & PF4) ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof e_par as (PU & PU4 & PU5 & (PN1 & PN2 & PN3 & PN4) & (PF1 & PF2 & PF3 & PF4) & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    (first [ pose proof (e_seg) as dR_26; dand16 dR_26 as LO SPA SPH MXR THR THRA RIR RIAL SBR SBAL SEP_tr SEP_rs SEP_ts NF TPL TSDL | pose proof e_seg as (LO & SPA & SPH & MXR & THR & THRA & RIR & RIAL & SBR & SBAL & SEP_tr & SEP_rs & SEP_ts & NF & TPL & TSDL) ]).
    assert (U0 : 0 < U) by lia.
    (first [ pose proof ((ar_ums A 24 W0 CR EMP SHORT)) as dR_27; dand5 dR_27 as _ _ _ _ U21 | pose proof (ar_ums A 24 W0 CR EMP SHORT) as (_ & _ & _ & _ & U21) ]).
    pose proof tRBE as RBEq. lin_open.
    assert (BEQ : rbs + mu = rb + mu) by (rewrite RBEq; reflexivity).
    assert (RANGE : a_sb A <= rbs + mu /\ rbs + mu + U <= a_sb A + kSpaceSize + 4096 /\ (rbs + mu) mod 4096 = 0 /\ U mod 4096 = 0 /\ 0 < U).
    { split; [lia|]. split; [unfold kSpaceSize; lia|]. split; [| split; [apply mod4096_of; tauto| exact U0]].
      rewrite Z.add_mod, rbs_mod, (mod4096_of mu R4) by lia. reflexivity. }
    assert (BR : pa_eager A + U + hull_bytes (pa_lhull A) <= p_tlim (a_pl A)).
    { pose proof (room_gen 0 0 (or_introl (conj eq_refl eq_refl))) as X. rewrite lhull_000 in X. lia. }
    pose proof (popg_hull_le A 24 U 0 0 W0 CR t_UMS t_FAM0) as HLE. pose proof (popg_lhull_le A 24 U 0 0 W0 CR t_UMS t_FAM0) as LHLE.
    assert (FEB : kHighMemBeg <= rbs + mu /\ rbs + mu + U <= 2^47 /\ 0 < U) by (unfold kHighMemBeg; lia).
    assert (VISN : forall x, rbs + mu <= x < rbs + mu + U -> in_hullb HU x = true).
    { intros x Hx. apply (pop_vis_user A 24 U 0 0 CR ltac:(lia)). rewrite BEQ in Hx. lia. }
    eapply (fpop_node A m md AI mdk (pa_hull A) (pa_lhull A) (pa_eager A) (rbs + mu) U A eq_refl eq_refl PM HI RANGE BR).
    - (* [comment removed for export] *)
      cbv zeta. intros HI2 PM2 LZ2.
      set (md2 := commit_model (wz 50) (wz (rbs + mu)) (wz U) false mdk) in *.
      (* [comment removed for export] *)
      assert (PMU2 : pop_mod AgU md md2).
      { apply (pop_mod_grow A AgU md md2 (rbs + mu) U eq_refl eq_refl ltac:(lia)); [| exact PM2| exact LZ2].
        intros c' Hc'. cbn [popg set_cache_inited set_reg a_reg a_pl]. unfold reg_upd.
        destruct (Z.eqb_spec c' 24) as [->|NE]; cbn [grow rg_mapped_user rg_mapped_fa]; [| split; left; reflexivity].
        split; [right| left; clear; lia]. split; [| clear; lia].
        clear - RBEq. unfold region_beg, a_sb, kRegionSize in *. lia. }
      (first [ pose proof (CYw) as dR_28; dand4 dR_28 as _ _ MIw _ | pose proof CYw as (_ & _ & MIw & _) ]).
      assert (SHGEO : sh sb <= sh (rbs + mu) /\ sh (rbs + mu) + U / 8 <= sh sb + kSpaceSize / 8 /\ kLowShadowMapBeg <= sh (rbs + mu) /\ sh (rbs + mu) + U / 8 <= kHighMemBeg).
      { destruct (sh_prim_range (rbs + mu) U ltac:(lia) ltac:(unfold kSpaceSize; lia) ltac:(lia)) as [G1 G2].
        split; [exact G1|]. split; [exact G2|]. rewrite BEQ. unfold kLowShadowMapBeg, kHighMemBeg in *. lia. }
      pose proof (sw_munch (pa_hull A) HU (rbs + mu) U m w HLE newh_U FEB CL) as MU2.
      pose proof (sw_wmono (pa_hull A) HU (rbs + mu) U m w HLE FEB CL) as WM2.
      pose proof (sw_mem_inv (pa_hull A) HU (rbs + mu) U m w newh_U FEB (conj (proj1 (proj2 (proj2 SHGEO))) (proj2 (proj2 (proj2 SHGEO)))) MIw) as MI2.
      assert (MSF : mapped (mrestrict (hidc HU) (apply_zeros (munrestrict (hidc (pa_hull A)) m w) [(wz (rbs + mu), wz U)])) (sh (rbs + mu)) (U / 8)).
      { apply (shadow_present (pa_hull A) HU (rbs + mu) U m w junk0 pad scr ksc 0 0 0 (hull_le_refl _) (fun a _ => eq_refl) CYw FEB SHGEO).
        - intros z Hz. rewrite BEQ in Hz. (first [ pose proof (f_SHG) as dR_29; dand3 dR_29 as S1 S2 _ | pose proof f_SHG as (S1 & S2 & _) ]).
          assert (D0 : 0 <= mu / 8) by (apply Z.div_pos; lia).
          apply (pop_vis_ush A 24 U 0 0 W0 CR t_UMS t_FAM0 ltac:(lia)). lia.
        - intros z Hz V0. exact V0. }
      assert (ZNU : mapped (mrestrict (hidc HU) (apply_zeros (munrestrict (hidc (pa_hull A)) m w) [(wz (rbs + mu), wz U)])) (rb + mu) U).
      { intros i Hi. rewrite <- BEQ. rewrite (sw_zero (pa_hull A) HU (rbs + mu) U m w FEB VISN (rbs + mu + i) ltac:(lia)). discriminate. }
      set (M2 := apply_zeros (munrestrict (hidc (pa_hull A)) m w) [(wz (rbs + mu), wz U)]) in *.
      set (w2 := mrestrict (hidc HU) M2) in *.
      rewrite BEQ in MU2. change (munch pk_Wg1 w w2) in MU2.
      (first [ dand6 pk_WG1 as SUB DF DR DL DRW DHI | destruct pk_WG1 as (SUB & DF & DR & DL & DRW & DHI) ]).
      apply (c_stage _ _ M2 md2).
      + intros a Ha. unfold M2. exact (sw_hidden (pa_hull A) HU (rbs + mu) U m w HLE FEB VISN a Ha).
      + exact PMU2.
      + apply (MInv_hull_mono (pa_hull A) (pa_lhull A) HU HLU (pa_eager A + U) _ md2 HI2 LHLE (cover_gen U 0 md2 (or_intror (conj eq_refl (or_introl eq_refl))) PMU2 (pa_hull A))); [lia|].
        destruct PM2 as ((_ & _ & VL & _) & _). rewrite VL. (first [ pose proof ((ai_ledger _ _ _ _ _ _ _ AI)) as dR_31; dand6 dR_31 as _ _ _ _ L5 _ | destruct (ai_ledger _ _ _ _ _ _ _ AI) as (_ & _ & _ & _ & L5 & _) ]). rewrite L5.
        pose proof (room_gen U 0 (or_intror (conj eq_refl (or_introl eq_refl)))) as X. lia.
      + change (aview_of HU M2) with w2.
        eapply evt_mono; [| intros st' PO; exists junk0, pad, scr, ksc, a0h; exact PO].
        apply (e_B t0' t1' t2' a6' t3' t4' t5' t6' a0h junk0 pad scr scrM (rdbytes w2 (sh (rbs + mu)) (Z.to_nat (U / 8))) ksc w2 NOFIT).
        * exact (cy_step _ _ _ _ 0 0 0 U 0 0 _ w w2 CYw MU2 WM2 MI2 (Wmono 0 0 0 U 0 0 ltac:(lia) ltac:(lia) ltac:(lia)) SUB DF DR DL).
        * exact (rw_step _ _ _ _ _ w w2 RWw MU2 WM2 DRW).
        * apply (stk_transport_disjoint rsegs _ w w2 _ _ STw MU2 WM2). apply DHI. lia.
        * eapply rw_cells_transport; [exact FRP| exact MU2| exact WM2| apply DHI; lia].
        * eapply rw_cells_transport; [exact FRM| exact MU2| exact WM2| apply DHI; lia].
        * assert (K0' : 0 <= U / 8) by (apply Z.div_pos; lia).
          apply OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopP.APopK.mapped_CB; [rewrite Z2Nat.id by lia; exact MSF| unfold kLowShadowMapBeg in *; lia| rewrite Z2Nat.id by lia; unfold kHighMemBeg in *; lia].
        * exact ZNU.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation HPp := (hp_post rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A p n0 stkobj lo key).
  #[warnings="-notation-for-abbreviation"] Local Notation PM1p := (pm1_post rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A p n0 stkobj lo key).
  #[warnings="-notation-for-abbreviation"] Local Notation e_head := (pop_head rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT SHAPE).
  #[warnings="-notation-for-abbreviation"] Local Notation e_Afit := (pop_A_fit rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation e_Amap := (pop_A_map rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).

  #[using="KEND CEILw CEIL SAE PREF CE N7R CR W0 AI SHAPE SHORT EMP NQ HL PRE key hi lo n0 A Clg"] Theorem fpop_core_gen : forall (t0 t1 t2 a2 a3 a6 a7 t3 t4 t5 t6 : word),
    srealizes rsegs
      (mkCfg (MS (mkR rac spd gp tp t0 t1 t2 s0 s1 (wz 0xb1d58) (wz p) a2 a3 (wz stkobj) (wz 1) a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x36e88) fc None m (seg_rom rsegs)) md)
      T.
  Proof.
    intros t0 t1 t2 a2 a3 a6 a7 t3 t4 t5 t6.
    destruct (asI_minv A m md AI) as [HMI HH]. pose proof (pop_mod_entry A m md AI) as PM0.
    destruct (Z.leb_spec (au + (kk - nf) * size) mu) as [FIT|NOFIT].
    - (* [comment removed for export] *)
      assert (U0 : U = 0) by (destruct (ar_ums_cases A 24) as [[X _]|[_ X]]; [exact X| lia]).
      pose proof c_stage as CS. rewrite U0 in CS. rewrite hull_000 in CS. rewrite lhull_000 in CS. rewrite popg_zero in CS.   (* [comment removed for export] *)
      eapply (CS _ _ m md (fun a _ => eq_refl) PM0 ltac:(rewrite Z.add_0_r; exact HMI)).
      eapply evt_cut; [exact (e_head t0 t1 t2 a2 a3 a6 a7 t3 t4 t5 t6)|].
      (intros st; (first [ intro dR_37; dex16 dR_37 as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr ksc w; dand4 dR_37 as -> CYw RWw STw | intro dR_37; dand20 dR_37 as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr ksc w -> CYw RWw STw | intros (t0' & t1' & t2' & a0' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk0 & pad & scr & ksc & w & -> & CYw & RWw & STw) ])).
      eapply evt_mono; [exact (e_Afit t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr ksc w FIT CYw RWw STw)|].
      intros st' PO. exists junk0, pad, scr, ksc, a0'. exact PO.
    - (* [comment removed for export] *)
      eapply (srz_evt_restrict rsegs (pa_hull A) (hull_segsR _) pa_wxR _ (pa_eager A)
                (fun st => exists junk0 pad scr ksc a0h, PM1p junk0 pad scr ksc a0h st) _ md _ HMI HH).
      { rewrite restrict_MS. eapply evt_cut; [exact (e_head t0 t1 t2 a2 a3 a6 a7 t3 t4 t5 t6)|].
        (intros st; (first [ intro dR_38; dex16 dR_38 as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr ksc w; dand4 dR_38 as -> CYw RWw STw | intro dR_38; dand20 dR_38 as t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr ksc w -> CYw RWw STw | intros (t0' & t1' & t2' & a0' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk0 & pad & scr & ksc & w & -> & CYw & RWw & STw) ])).
        eapply evt_mono; [exact (e_Amap t0' t1' t2' a0' a5' a6' a7' t3' t4' t5' t6' junk0 pad scr ksc w NOFIT CYw RWw STw)|].
        intros st' PO. exists junk0, pad, scr, ksc, a0'. exact PO. }
      (intros msr' md'; (first [ intro dR_39; dex5 dR_39 as junk0 pad scr ksc a0h; rename dR_39 into Q | intro dR_39; dand6 dR_39 as junk0 pad scr ksc a0h Q | intros (junk0 & pad & scr & ksc & a0h & Q) ]); intros HI' SB CL).
      (first [ dex10 Q as t0' t1' t2' a6' t3' t4' t5' t6' scrM w'; dand6 Q as -> CYw RWw STw FRP FRM | dand16 Q as t0' t1' t2' a6' t3' t4' t5' t6' scrM w' -> CYw RWw STw FRP FRM | destruct Q as (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & scrM & w' & -> & CYw & RWw & STw & FRP & FRM) ]).
      rewrite unrestrict_MSsvc. cbn [ms_mem] in CL |- *.
      exact (node1 junk0 pad scr scrM ksc a0h t0' t1' t2' a6' t3' t4' t5' t6' w' md' NOFIT (pop_mod_sbm A m md AI md md' PM0 SB) HI' CL CYw RWw STw FRP FRM).
  Qed.
End FArm.
End AFPopT.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeHc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH4w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH5e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH5c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1F OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFPopP.AFPopK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFPopP OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopCtx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFPopEnd.AFPopE OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFPopEnd.AFPopT.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AClient APopTE AFreeT AFreeH4c AFreeB4c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB4F.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB4F AFreeFS.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRI3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRI3 AFreptn AFrejxv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFrejxv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFrelij AFrext2 AFre9ly AFreo3f AFre1om AFreldj.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopTE OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH4c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB4c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB4F.AFreeB3F OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB4F OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeFS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF2.ACoreF OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI3.AFreeRI2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreptn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFrejxv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFrejxv.AFreib5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFrelij OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFrext2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFre9ly OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreo3f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFre1om OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreldj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.lazy_rounds := Ltac2.Init.false.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.cheap_first := Ltac2.Init.false.

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pasan).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kShadowGapBeg, kHighShadowMapSize,
                        kAuCap, kFreeArraySize, kUserMapSize, kFreeArrayMapSize in *.


Section FEnd.
Context {Clg : Ceiling}.
  Variables (rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (md : Model) (A : AState) (p n0 stkobj lo hi : Z) (key : list Z).
  Hypothesis PRE : dealloc_core_pre rac spd (cl_tp LPA) m md A p n0 stkobj lo hi key.
  Hypothesis HL : as_live A p = Some n0.
  Hypothesis NQ : n0 <= 2^28.
  Hypothesis EMP : pk_chunks (a_cache A 24) = [].
  Hypothesis SHORT : Z.of_nat (length (rg_free (a_reg A 24))) < refill_count 24.
  Hypothesis SHAPE : a_qthread A = [] \/ (a_qthread A <> [] /\ Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) = kQuarantineBatchCount).
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned spd).
  #[warnings="-notation-for-abbreviation"] Local Notation sa := (bv_unsigned spd + -80 + 112).
  #[warnings="-notation-for-abbreviation"] Local Notation spaw := (Z_to_bv 64 (bv_unsigned spd + -80 + 112)).
  #[warnings="-notation-for-abbreviation"] Local Notation tp := (cl_tp LPA).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation ctx := (p_ctx (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation ri := (a_ri A).
  #[warnings="-notation-for-abbreviation"] Local Notation n0d := (p_nodes0 (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation f0d := (p_frames0 (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation r8 := ((n0 + 7) / 8).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (a_ri A + 128 * 24).
  #[warnings="-notation-for-abbreviation"] Local Notation C := (p_thr (a_pl A) + 208).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (p_thr (a_pl A) + 208 + 80 * 24).
  #[warnings="-notation-for-abbreviation"] Local Notation uG := (bv_unsigned spd + -80 + 112 + -128 + -48 + -32 + -128).
  #[warnings="-notation-for-abbreviation"] Local Notation rb := (region_beg (a_sb A) 24).
  #[warnings="-notation-for-abbreviation"] Local Notation rbs := (a_sb A + 24 * 4294967296).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (region_beg (a_sb A) 24 + kFreeArrayOffset).
  #[warnings="-notation-for-abbreviation"] Local Notation mu := (rg_mapped_user (a_reg A 24)).
  #[warnings="-notation-for-abbreviation"] Local Notation au := (rg_allocated_user (a_reg A 24)).
  #[warnings="-notation-for-abbreviation"] Local Notation mfa := (rg_mapped_fa (a_reg A 24)).
  #[warnings="-notation-for-abbreviation"] Local Notation nf := (Z.of_nat (length (rg_free (a_reg A 24)))).
  #[warnings="-notation-for-abbreviation"] Local Notation kk := (refill_count 24).
  #[warnings="-notation-for-abbreviation"] Local Notation size := (class_size 24).
  #[warnings="-notation-for-abbreviation"] Local Notation U := (pop_ums A 24).
  #[warnings="-notation-for-abbreviation"] Local Notation N := (pop_nc A 24).
  #[warnings="-notation-for-abbreviation"] Local Notation Fm := (pop_fam A 24).
  #[warnings="-notation-for-abbreviation"] Local Notation D' := (fst (depot_putC (a_depot A) key)).
  #[warnings="-notation-for-abbreviation"] Local Notation fid := (snd (depot_putC (a_depot A) key)).

  Let AI : @pa_ainv _ DepotRepL A m md. Proof. exact (proj1 PRE). Qed.
  Let W0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CR : 1 <= 24 <= 30. Proof. lia. Qed.
  Let N7R : 1 <= 7000 <= kMaxPrimaryUser. Proof. unfold kMaxPrimaryUser. lia. Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.
  Let MIv : mem_inv rsegs v. Proof. exact (proj1 (proj2 PRE)). Qed.
  (* [comment removed for export] *)
  Let PREF : alloc_ceiling <= lo /\ lo <= usp - 4096 /\ usp <= hi /\ hi <= 2^47 /\ usp mod 16 = 0 /\ bv_unsigned rac mod 2 = 0 /\
             stk rsegs v lo usp /\ mapped v usp (hi - usp) /\ usp <= stkobj /\ stkobj + 2064 <= hi.
  Proof.
    destruct PRE as (_ & _ & _ & _ & _ & CLO & LOSA & SAHI & HI47 & SPA & RAC2 & ST & SM & SOLO & SOHI & _). cbn [cl_segs LPA] in ST.
    exact (conj CLO (conj LOSA (conj SAHI (conj HI47 (conj SPA (conj RAC2 (conj ST (conj SM (conj SOLO SOHI))))))))).
  Qed.
  Let SAE : bv_unsigned spaw = sa.
  Proof. destruct PREF as (_ & _ & SAHI & HI47 & _). pose proof (zr_word spd) as X. unfold inr64 in X. apply unsigned_lit. lia. Qed.
  Let CEIL : alloc_ceiling <= sa - 1024. Proof. destruct PREF as (CLO & LOSA & _). lia. Qed.
  Let CEILw : alloc_ceiling <= bv_unsigned spaw - 1024. Proof. rewrite SAE. exact CEIL. Qed.
  Let EMP7 : pk_chunks (a_cache A (class_of 7000)) = []. Proof. rewrite class_of_7000. exact EMP. Qed.
  Let SHORT7 : Z.of_nat (length (rg_free (a_reg A (class_of 7000)))) < refill_count (class_of 7000). Proof. rewrite class_of_7000. exact SHORT. Qed.
  Let KS : Z.shiftr (max_count 24) 1 = kk. Proof. exact (proj1 (proj2 (proj2 (ar_k A 24 CR)))). Qed.

  #[warnings="-notation-for-abbreviation"] Local Notation CY := (carryF rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A p n0 stkobj key).
  #[warnings="-notation-for-abbreviation"] Local Notation RW := (regwF A).
  #[warnings="-notation-for-abbreviation"] Local Notation Wi := (fk_Wi spd A).
  #[warnings="-notation-for-abbreviation"] Local Notation Wfo := (fk_Wfo A p n0).
  #[warnings="-notation-for-abbreviation"] Local Notation LIN := (fk_lin rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation PLIN := (fk_plin rac spd m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation Wle := (fk_Wi_le spd A).
  #[warnings="-notation-for-abbreviation"] Local Notation Wmono := (fk_Wi_mono spd A).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_step := (carryF_step rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE).
  #[warnings="-notation-for-abbreviation"] Local Notation rw_step := (regwF_step rac spd A).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_statics := (fcy_statics rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_seal := (fcy_seal rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_na := (fcy_na rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_thr_mapped := (fcy_thr_mapped rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_tst := (fcy_tst rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_stm := (fcy_stm rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_mapped := (fcy_mapped rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A p n0 stkobj key).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_NN := (fcy_NN rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A p n0 stkobj key).
  #[warnings="-notation-for-abbreviation"] Local Notation cy_fcells := (fcy_fcells rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_UMS := (fk_UMS rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_FAM := (fk_FAM rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_NC := (fk_NC rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_POS := (fk_POS rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_SHG := (fk_SHG rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation f_region := (fk_region rac spd m md A p n0 stkobj lo hi key PRE).
  #[warnings="-notation-for-abbreviation"] Local Notation f_regw_entry := (regwF_entry rac spd m md A p n0 stkobj lo hi key PRE).

  Variable T : TSet.
  Hypothesis KK : dealloc_core_K rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 lo hi T.
  #[warnings="-notation-for-abbreviation"] Local Notation HS := (pa_hull (popg A 24 (pop_ums A 24) (pop_fam A 24) (pop_nc A 24))).
  #[warnings="-notation-for-abbreviation"] Local Notation Ag := (popg A 24 (pop_ums A 24) (pop_fam A 24) (pop_nc A 24)).
  #[warnings="-notation-for-abbreviation"] Local Notation HLS := (pa_lhull (popg A 24 (pop_ums A 24) (pop_fam A 24) (pop_nc A 24))).   (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation GPk := (gpk rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m A p n0 stkobj lo key).
  #[warnings="-notation-for-abbreviation"] Local Notation e_par := (par_facts rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).
  #[warnings="-notation-for-abbreviation"] Local Notation e_seg := (seg_pre rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT).

  (* [comment removed for export] *)
  Variables (Mk : mem) (mdk md' : Model) (v5 : mem) (junk0 pad scr : list byte) (ksc : list word) (na : word).
  Hypothesis MSH : forall a, hidc HS a = true -> Mk a = m a.
  Hypothesis PM : pop_mod Ag md mdk.   (* [comment removed for export] *)
  Hypothesis HI5 : MInv HS HLS (pa_eager Ag) md'.   (* [comment removed for export] *)
  Hypothesis SB5 : same_but_materialized mdk md'.
  Hypothesis CL5 : forall a, hidc HS a = true -> v5 a = None.
  Hypothesis GPK : GPk junk0 pad scr ksc na v5.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vh : mem := mhyb Wfo v v5.
  Definition vpF : mem := write_to_mem vh (wa R) (le8 (wz 0)).

  Let CY5 : CY junk0 pad scr ksc U Fm N v5. Proof. exact (proj1 GPK). Qed.
  Let LErefl : sub_fp (Wi U Fm N) (Wi U Fm N). Proof. intros x Hx. exact Hx. Qed.
  Let MU5 : munch (Wi U Fm N ++ Wfo) v v5. Proof. exact (proj1 CY5). Qed.
  Let WM5 : wmono rsegs v v5. Proof. exact (proj1 (proj2 CY5)). Qed.
  Let MI5 : mem_inv rsegs v5. Proof. exact (proj1 (proj2 (proj2 CY5))). Qed.

  #[using="MU5 CY5 GPK na ksc scr pad junk0 SAE PREF CE N7R CR SHAPE PRE key hi lo stkobj md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac"] Lemma MUh : munch (pop_W (bv_unsigned spaw - 1024) (bv_unsigned spaw) thr E R fa nf N rb mu U mfa Fm (a_cache_inited A)) v vh.
  Proof.
    rewrite SAE. unfold vh. eapply munch_weaken; [| apply (mhyb_munch_entry Wfo (Wi U Fm N) v v5)].
    - unfold fk_Wi. apply fpop_Wq_sub_W; lia.
    - eapply munch_weaken; [| exact MU5]. intros x Hx. rewrite fk_outside_app in *. tauto.
  Qed.
  #[using="CY5 GPK na ksc scr pad junk0 key lo stkobj s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 spd rac"] Lemma NNh : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> vh (wz a) <> None.
  Proof. intros a H0 H1 H2 H3. unfold vh. apply mhyb_NN; [exact H3|]. intros _. exact (cy_NN _ _ _ _ _ _ _ v5 CY5 a H0 H1 H2 H3). Qed.
  #[using="CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md m spd rac"] Lemma hull_AS : hull_le (pa_hull A) HS.
  Proof. exact (popg_hull_le A 24 U Fm N W0 CR f_UMS f_FAM). Qed.
  #[using="CL5 CR W0 AI SHORT EMP PRE key hi lo stkobj md spd rac"] Lemma CLh : forall a, hidc HS a = true -> vh a = None.
  Proof.
    intros a Ha. unfold vh. apply (mhyb_clean Wfo v v5 (hidc HS)); [| exact CL5| exact Ha].
    intros x Hx. unfold aview_of, mrestrict. rewrite (hidc_grow_le (pa_hull A) HS hull_AS x Hx). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac fo_open :=
    let L := fresh "L" in let P := fresh "P" in pose proof LIN as L; pose proof PLIN as P;
    unfold fk_Wfo, fpop_Wfo;
    destruct L as (L1 & L2 & (T1 & T2 & T3 & T4) & (B1 & B2 & B3 & B4 & B5) & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) & (H1 & H2 & H3 & H4 & H5));
    destruct P as ((P1 & P2 & P3 & P4) & (P5 & P6 & P7 & P8) & (S1 & S2 & S3) & ((N1 & N2 & N3 & N4) & N5 & N6 & N7) & ((F1 & F2 & F3 & F4) & F5 & F6 & F7) & ((C1 & C2 & C3) & C4 & C5 & C6));
    unfold kFreeArrayOffset in *;
    set (Sp := sh p) in *; set (Su := sh (rb + mu)) in *; set (Sf := sh (region_beg sb 24 + 3758096384 + mfa)) in *; set (u8 := U / 8) in *; set (f8 := Fm / 8) in *;
    cbn [disjoint_from outside app]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I.

  #[using="AI SHORT EMP NQ HL PRE key hi lo stkobj md m spd rac Clg"] Lemma Wfo_ri : forall a l, ri <= a -> a + l <= ri + 4096 -> disjoint_from Wfo a l.
  Proof.
    intros a l A1 A2. pose proof (f24_sep A m md AI) as (SEP_tr & _). unfold apart, AMallocA.apart in SEP_tr. fo_open;
      first [ solve [clear - A1 A2 P6 P3; lia] | solve [clear - A1 A2 SEP_tr; lia] | solve [clear - A1 A2 B1 B3; lia] | solve [clear - A1 A2 N6 B3; lia]
            | solve [clear - A1 A2 F6 B3; lia] | solve [clear - A1 A2 S2 B1 B3; lia] ].
  Qed.
  #[using="AI SHORT EMP NQ HL PRE key hi lo stkobj md m spd rac Clg"] Lemma Wfo_reg : forall a l, rb + au <= a -> a + l <= rb + 4294967296 -> disjoint_from Wfo a l.
  Proof.
    intros a l A1 A2. (first [ pose proof ((f24_sep A m md AI)) as dR_1; dand7 dR_1 as _ _ _ _ _ SEP_ts _ | pose proof (f24_sep A m md AI) as (_ & _ & _ & _ & _ & SEP_ts & _) ]). unfold apart, AMallocA.apart in SEP_ts. fo_open;
      first [ solve [clear - A1 A2 P5 P3; lia] | solve [clear - A1 A2 SEP_ts B4 Q1; lia] | solve [clear - A1 A2 B1 B4 Q1; lia] | solve [clear - A1 A2 N6 B4 Q1; lia]
            | solve [clear - A1 A2 F6 B4 Q1; lia] | solve [clear - A1 A2 S2 B1 B4 Q1; lia] ].
  Qed.
  #[using="SHORT EMP NQ HL PRE key hi lo stkobj md m spd rac Clg"] Lemma Wfo_sh : forall a l, sh (rb + mu) <= a -> a + l <= sh (fa + mfa) + Fm / 8 -> disjoint_from Wfo a l.
  Proof.
    intros a l A1 A2. fo_open;
      first [ solve [clear - A1 A2 P1 P3 P4 H1 H5; lia] | solve [clear - A1 A2 T1 T4 H1 H5; lia] | solve [clear - A1 A2 H1; lia] | solve [clear - A1 A2 N1 N4 H1 H5; lia]
            | solve [clear - A1 A2 F1 F4 H1 H5; lia] | solve [clear - A1 A2 S3 P3 H2 H3 H4; lia] ].
  Qed.
  #[using="SHORT EMP NQ HL PRE key hi lo stkobj md m spd rac Clg"] Lemma Wfo_thr : forall a l, thr <= a -> a + l <= thr + 4096 -> (a + l <= thr + 2824 \/ thr + 2840 <= a) -> disjoint_from Wfo a l.
  Proof.
    intros a l A1 A2 A3. fo_open;
      first [ solve [clear - A1 A2 P7 P3; lia] | solve [clear - A1 A2 A3; lia] | solve [clear - A1 A2 T1 T3; lia] | solve [clear - A1 A2 N5; lia]
            | solve [clear - A1 A2 F5; lia] | solve [clear - A1 A2 T1 T4 S1 S2; lia] ].
  Qed.
  #[using="CE SHORT EMP NQ HL PRE key hi lo stkobj md m spd rac"] Lemma Wfo_hi : forall a l, alloc_ceiling <= a -> disjoint_from Wfo a l.
  Proof.
    intros a l A1. fo_open;
      first [ solve [clear - A1 P2 P3; lia] | solve [clear - A1 T2; lia] | solve [clear - A1 CE; lia] | solve [clear - A1 N2; lia]
            | solve [clear - A1 F2; lia] | solve [clear - A1 S2 CE; lia] ].
  Qed.

  (* [comment removed for export] *)
  #[using="CEILw CEIL SAE PREF CE PRE key hi lo stkobj md spd rac"] Lemma vh_rw : forall a cs, rw_cells rsegs v5 a cs -> disjoint_from Wfo a (Z.of_nat (cells_size cs)) -> rw_cells rsegs vh a cs.
  Proof.
    intros a cs H DJ. pose proof H as [_ (W1 & W2 & _)]. apply (rw_cells_agree v5 vh a cs H). intros x Hx. unfold vh. apply (mhyb_off Wfo v v5 a _ x DJ Hx). lia.
  Qed.
  #[using="CEILw CEIL SAE PREF CE PRE key hi lo stkobj md spd rac"] Lemma vh_bytes : forall a bs, bytes_at rsegs v5 a bs -> disjoint_from Wfo a (Z.of_nat (length bs)) -> bytes_at rsegs vh a bs.
  Proof.
    intros a bs H DJ. (first [ pose proof (H) as dR_2; dand3 dR_2 as W1 W2 _ | pose proof H as (W1 & W2 & _) ]). apply (bytes_at_agree v5 vh a bs H). intros x Hx. unfold vh. apply (mhyb_off Wfo v v5 a _ x DJ Hx). lia.
  Qed.
  #[using="CEILw CEIL SAE PREF CE PRE key hi lo stkobj md spd rac"] Lemma vh_u32 : forall a ws, u32arr rsegs v5 a ws -> disjoint_from Wfo a (4 * Z.of_nat (length ws)) -> u32arr rsegs vh a ws.
  Proof.
    intros a ws H DJ. pose proof H as [_ (W1 & W2 & _)]. apply (u32arr_agree v5 vh a ws H). intros x Hx. unfold vh. apply (mhyb_off Wfo v v5 a _ x DJ Hx). lia.
  Qed.
  #[using="CEILw CEIL SAE PREF CE PRE key hi lo stkobj md spd rac"] Lemma vh_mapped : forall a k, mapped v5 a k -> disjoint_from Wfo a k -> 0 <= a -> a + k <= 2^64 -> mapped vh a k.
  Proof. intros a k M DJ A0 A1 i Hi. unfold vh. rewrite (mhyb_off Wfo v v5 a k (a + i) DJ ltac:(lia) ltac:(lia)). exact (M i Hi). Qed.
  (* [comment removed for export] *)
  #[using="CEILw CEIL SAE PREF CE PRE key hi lo stkobj md spd rac"] Lemma v5_rw : forall a cs, rw_cells rsegs vh a cs -> disjoint_from Wfo a (Z.of_nat (cells_size cs)) -> rw_cells rsegs v5 a cs.
  Proof.
    intros a cs H DJ. pose proof H as [_ (W1 & W2 & _)]. apply (rw_cells_agree vh v5 a cs H). intros x Hx. unfold vh. symmetry. apply (mhyb_off Wfo v v5 a _ x DJ Hx). lia.
  Qed.
  #[using="CEILw CEIL SAE PREF CE PRE key hi lo stkobj md spd rac"] Lemma v5_ro : forall a cs, ro_cells rsegs vh a cs -> disjoint_from Wfo a (Z.of_nat (cells_size cs)) -> ro_cells rsegs v5 a cs.
  Proof.
    intros a cs H DJ. pose proof H as [Hwf (W1 & W2 & _)]. rewrite cells_bytes_length in W2 by exact Hwf.
    apply (ro_cells_agree vh v5 a cs H). intros x Hx. unfold vh. symmetry. apply (mhyb_off Wfo v v5 a _ x DJ Hx). lia.
  Qed.
  #[using="CEILw CEIL SAE PREF CE PRE key hi lo stkobj md spd rac"] Lemma v5_u32 : forall a ws, u32arr rsegs vh a ws -> disjoint_from Wfo a (4 * Z.of_nat (length ws)) -> u32arr rsegs v5 a ws.
  Proof.
    intros a ws H DJ. pose proof H as [_ (W1 & W2 & _)]. apply (u32arr_agree vh v5 a ws H). intros x Hx. unfold vh. symmetry. apply (mhyb_off Wfo v v5 a _ x DJ Hx). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CE SHORT EMP PRE key hi lo stkobj md spd rac"] Lemma MUvp : munch [(R, R + 8)] vh vpF.
  Proof.
    (first [ pose proof (LIN) as dR_3; dand5 dR_3 as L1 L2 _ (B1 & B2 & B3 & B4 & B5) _ | pose proof LIN as (L1 & L2 & _ & (B1 & B2 & B3 & B4 & B5) & _) ]).
    unfold vpF. apply munch_write; [apply munch_refl| | |]; rewrite ?length_le8; [lia| lia| cbn; lia].
  Qed.
  Lemma WMvp : wmono rsegs vh vpF. Proof. unfold vpF. apply wmono_write. apply wmono_refl. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation mg := (munrestrict (hidc HS) Mk vpF).

  #[using="MU5 CY5 GPK CL5 SB5 HI5 PM MSH na ksc scr pad junk0 mdk CEILw CEIL SAE PREF CE N7R CR W0 AI SHAPE SHORT EMP NQ HL PRE key hi lo stkobj md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 spd rac"] Lemma AIg24 : @pa_ainv _ DepotRepL Ag mg md'.
  Proof.
    destruct PREF as (CLO & LOSA & SAHI & HI47 & SPA0 & RAC2 & ST & SM & SOLO & SOHI).
    destruct PM as (V & LED & COV & TOP & AMD & HH).
    destruct GPK as (_ & ST5 & P_nf & P_mfa & P_au & P_mu & P_ex & P_na & P_fa & P_newU & P_newF & P_shU & P_shF).
    pose proof CY5 as (_ & _ & _ & _ & _ & _ & _ & MX5 & LK5 & LN5 & LNS5 & _).
    (first [ pose proof (LIN) as dR_4; dand6 dR_4 as L1 L2 (T1 & T2 & T3 & T4) (B1 & B2 & B3 & B4 & B5) (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) (H1 & H2 & H3 & H4 & H5) | pose proof LIN as (L1 & L2 & (T1 & T2 & T3 & T4) & (B1 & B2 & B3 & B4 & B5) & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) & (H1 & H2 & H3 & H4 & H5)) ]).
    (first [ pose proof (e_par) as dR_5; dand8 dR_5 as PU PU4 PU5 (PN1 & PN2 & PN3 & PN4) (PF1 & PF2 & PF3 & PF4) ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) CSR MUM | pose proof e_par as (PU & PU4 & PU5 & (PN1 & PN2 & PN3 & PN4) & (PF1 & PF2 & PF3 & PF4) & ((R1 & R4 & R5) & R6 & R7 & R8 & CAP0 & R10) & CSR & MUM) ]).
    (first [ pose proof ((ar_nc A 24 W0 CR EMP SHORT)) as dR_6; dand4 dR_6 as _ _ NTL _ | pose proof (ar_nc A 24 W0 CR EMP SHORT) as (_ & _ & NTL & _) ]).
    pose proof (APopTE.AIg rac spaw m md A 7000 0 lo U Fm N AI N7R) as X. unfold APopTE.vp in X. rewrite class_of_7000 in X. unfold kQuarantineBatchClass in X.
    refine (X EMP ltac:(lia) CLO ltac:(rewrite SAE; lia) f_UMS f_FAM f_NC f_POS ltac:(unfold kUserMapSize; lia) Mk mdk md' vh ksc MSH V LED HH AMD HI5 SB5 CLh MUh NNh LK5 _ _ _ _ _ _ _ _ _ _ _ _ _).
    - apply vh_rw; [exact MX5| apply Wfo_ri; cbn; lia].
    - apply vh_rw; [exact P_nf| apply Wfo_ri; cbn; lia].
    - apply vh_rw; [exact P_mfa| apply Wfo_ri; cbn; lia].
    - apply vh_rw; [exact P_au| apply Wfo_ri; cbn; lia].
    - apply vh_rw; [exact P_mu| apply Wfo_ri; cbn; lia].
    - apply vh_rw; [exact P_ex| apply Wfo_ri; cbn; lia].
    - apply vh_u32; [exact P_fa| apply Wfo_reg; rewrite ?length_map, ?newfree_length by lia; unfold kFreeArrayOffset in *; lia].
    - apply vh_mapped; [exact P_newU| apply Wfo_reg; lia| lia| lia].
    - apply vh_mapped; [exact P_newF| apply Wfo_reg; unfold kFreeArrayOffset in *; lia| unfold kFreeArrayOffset in *; lia| unfold kFreeArrayOffset in *; lia].
    - apply vh_bytes; [exact P_shU| rewrite repeat_length, Z2Nat.id by lia; apply Wfo_sh; lia].
    - apply vh_bytes; [exact P_shF| rewrite repeat_length, Z2Nat.id by lia; apply Wfo_sh; lia].
    - apply vh_rw; [exact LN5| apply Wfo_thr; cbn; lia].
    - intros CI0 i Hi Hic. (first [ pose proof ((LNS5 CI0 i Hi Hic)) as dR_7; dex1 dR_7 as ks; destruct dR_7 as [Lks Xi] | pose proof ((LNS5 CI0 i Hi Hic)) as dR_7; dand3 dR_7 as ks Lks Xi | destruct (LNS5 CI0 i Hi Hic) as (ks & Lks & Xi) ]). exists ks. split; [exact Lks|]. apply vh_rw; [exact Xi| apply Wfo_thr; cbn; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac lin_open :=
    let L := fresh "L" in pose proof LIN as L;
    destruct L as (L1 & L2 & (Lt1 & Lt2 & Lt3 & Lt4) & (B1 & B2 & B3 & B4 & B5) & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) & (H1 & H2 & H3 & H4 & H5)).
  Tactic Notation "cv" integer(k) := split; [right; (do k right); left; lia|].
  Ltac sub_open := apply sub_fp_all_inside; unfold fk_Wi, fpop_Wq, free_array_of, kFreeArrayOffset, off_th_stats in *; cbn [all_inside inside app]; destruct (a_cache_inited A).
  Ltac dj_tac := unfold fk_Wi, fpop_Wq, free_array_of, kFreeArrayOffset, off_th_stats in *; cbn [disjoint_from app]; try (destruct (a_cache_inited A));
                 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; lia.

  #[using="CY5 GPK CL5 na ksc scr pad junk0 v5 CE SHORT EMP PRE key hi lo stkobj n0 p md m s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 spd rac"] Lemma R_visible : forall i, 0 <= i < 8 -> hidc HS (wz (R + i)) = false.
  Proof.
    intros i Hi. destruct (hidc HS (wz (R + i))) eqn:Hz; [| reflexivity]. exfalso.
    pose proof CY5 as (_ & _ & _ & _ & _ & _ & _ & MX5 & _). destruct MX5 as [_ (W00 & W1 & WW)]. cbn [cells_size csize Nat.add] in W1, WW. specialize (WW i ltac:(lia)).
    apply WW. unfold wview, wa. rewrite (CL5 _ Hz). lin_open.
    rewrite unsigned_lit by lia. rewrite (pa_find_segment_none (R + i) 1); [reflexivity| lia| right; lia].
  Qed.
  #[using="CE SHORT EMP PRE key hi lo stkobj md spd rac"] Lemma AGRw : forall x : word, ~ (R <= bv_unsigned x < R + 8) -> vpF x = vh x.
  Proof. intros x Hx. apply MUvp. cbn. lia. Qed.
  #[using="CE SHORT EMP PRE key hi lo stkobj md spd rac"] Lemma AGR : forall a, 0 <= a < 2^64 -> ~ (R <= a < R + 8) -> vpF (wz a) = vh (wz a).
  Proof. intros a Ha NRa. apply AGRw. rewrite unsigned_lit by exact Ha. exact NRa. Qed.
  #[using="CY5 GPK CL5 na ksc scr pad junk0 CE CR W0 AI SHORT EMP PRE key hi lo stkobj md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 spd rac"] Lemma CLp : forall a, hidc HS a = true -> vpF a = None.
  Proof.
    intros a Ha. pose proof (zr_word a) as XR; unfold inr64 in XR.
    destruct (classic (R <= bv_unsigned a < R + 8)) as [IN|OUT].
    - exfalso. pose proof (R_visible (bv_unsigned a - R) ltac:(lia)) as X.
      replace (R + (bv_unsigned a - R)) with (bv_unsigned a) in X by lia. rewrite Z_to_bv_lit_self in X. congruence.
    - rewrite (AGRw a OUT). exact (CLh a Ha).
  Qed.
  #[using="CY5 GPK CL5 na ksc scr pad junk0 CE CR W0 AI SHORT EMP PRE key hi lo stkobj md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 spd rac"] Lemma VIEWg : aview_of HS (munrestrict (hidc HS) Mk vpF) = vpF.
  Proof. unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact CLp. Qed.
  #[using="MU5 CY5 GPK na ksc scr pad junk0 SAE PREF CE N7R CR SHAPE SHORT EMP PRE key hi lo stkobj md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac"] Lemma MUp : munch (pop_W (bv_unsigned spaw - 1024) (bv_unsigned spaw) thr E R fa nf N rb mu U mfa Fm (a_cache_inited A)) v vpF.
  Proof.
    eapply munch_trans; [exact MUh|]. eapply munch_weaken; [| exact MUvp]. unfold sub_fp. intros x Hx. unfold pop_W in Hx. cbn [outside app] in Hx |- *. tauto.
  Qed.
  #[using="CY5 GPK na ksc scr pad junk0 key lo stkobj s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 spd rac"] Lemma NNp : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> vpF (wz a) <> None.
  Proof. intros a H0 H1 H2 H3. apply (pk_wmono_NN vh vpF a WMvp H1 ltac:(lia)). exact (NNh a H0 H1 H2 H3). Qed.

  #[using="CE CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md spd rac"] Lemma t_VNEW : forall ums, mu + ums <= kFreeArrayOffset -> forall a, rb + mu <= a < rb + mu + ums -> v (wz a) = None.
  Proof.
    intros ums Hu a Ha. lin_open. unfold aview_of, mrestrict, hidc.
    rewrite unsigned_lit by (unfold region_beg, kRegionSize, kFreeArrayOffset in *; lia).
    assert (DEADB : forall dlo dhi, In (dlo, dhi) (a_deadsh A) -> dhi <= kHighMemBeg).
    { intros dlo dhi Hd. (first [ pose proof ((wfE A W0)) as dR_8; dand3 dR_8 as _ DF0 _ | destruct (wfE A W0) as (_ & DF0 & _) ]). pose proof (proj1 (Forall_forall _ _) DF0 _ Hd) as (D1 & _). cbn [fst snd] in D1. kung_all. unfold kShadowGapBeg in *. lia. }
    rewrite (prim_unmapped_hidden A (WFT_of_WF A W0) (ai_extra _ _ _ _ _ _ _ AI) DEADB 24 a CR); [reflexivity|]. left. lia.
  Qed.
  #[using="CE CR W0 AI SHORT EMP PRE key hi lo stkobj n0 p md spd rac"] Lemma t_VNEWF : forall fam, mfa + fam <= kFreeArraySize -> forall a, fa + mfa <= a < fa + mfa + fam -> v (wz a) = None.
  Proof.
    intros fam Hf a Ha. lin_open. unfold aview_of, mrestrict, hidc.
    rewrite unsigned_lit by (unfold region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize in *; lia).
    assert (DEADB : forall dlo dhi, In (dlo, dhi) (a_deadsh A) -> dhi <= kHighMemBeg).
    { intros dlo dhi Hd. (first [ pose proof ((wfE A W0)) as dR_9; dand3 dR_9 as _ DF0 _ | destruct (wfE A W0) as (_ & DF0 & _) ]). pose proof (proj1 (Forall_forall _ _) DF0 _ Hd) as (D1 & _). cbn [fst snd] in D1. kung_all. unfold kShadowGapBeg in *. lia. }
    rewrite (prim_unmapped_hidden A (WFT_of_WF A W0) (ai_extra _ _ _ _ _ _ _ AI) DEADB 24 a CR); [reflexivity|]. right.
    unfold region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PREF CE SHORT EMP NQ HL PRE key hi lo stkobj md m rac Clg"] Lemma W_caller : forall a, usp <= a -> a < 2^64 -> outside (Wi U Fm N ++ Wfo) a.
  Proof.
    intros a Ha H64. rewrite fk_outside_app. split.
    - apply (disjoint_outside _ a 1 a); [| lia]. pose proof LIN as L. pose proof PLIN as P.
      unfold fk_Wi, fpop_Wq.
      (first [ dand6 L as L1 L2 (T1 & T2 & T3 & T4) (B1 & B2 & B3 & B4 & B5) (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) (H1 & H2 & H3 & H4 & H5) | destruct L as (L1 & L2 & (T1 & T2 & T3 & T4) & (B1 & B2 & B3 & B4 & B5) & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10) & (H1 & H2 & H3 & H4 & H5)) ]).
      unfold kFreeArrayOffset in *. set (Su := sh (rb + mu)) in *; set (Sf := sh (region_beg sb 24 + 3758096384 + mfa)) in *; set (u8 := U / 8) in *; set (f8 := Fm / 8) in *.
      cbn [disjoint_from]. destruct (a_cache_inited A); OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I;
        first [ solve [clear - Ha; lia] | solve [clear - Ha L1 B2 B3; lia] | solve [clear - Ha L1 B2 B4 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10; lia]
              | solve [clear - Ha L1 T2; lia] | solve [clear - Ha L1 CE H1 H2 H3 H4 H5; lia] ].
    - apply (disjoint_outside _ a 1 a); [| lia]. apply Wfo_hi. lin_open. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="SB5 PM mdk A Clg"] Lemma AMDg : amd_frame md md'.
  Proof. destruct PM as (_ & _ & _ & _ & AMD & _). exact (amd_frame_sbm_r md mdk md' AMD SB5). Qed.

  #[using="MU5 CY5 GPK na ksc scr pad junk0 PREF CE SHORT EMP NQ HL PRE key lo stkobj md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac"] Lemma vp_caller : forall a, usp <= a < hi -> vpF (wz a) = v (wz a).
  Proof.
    intros a Ha. destruct PREF as (CLO & LOSA & SAHI & HI47 & _). lin_open.
    rewrite (AGR a ltac:(lia) ltac:(lia)). unfold vh, mhyb. destruct (in_fpb Wfo (bv_unsigned (wz a))); [reflexivity|].
    apply MU5. rewrite unsigned_lit by lia. apply W_caller; lia.
  Qed.

  #[using="MU5 CY5 GPK CL5 SB5 PM na ksc scr pad junk0 mdk KK CEILw CEIL SAE PREF CE N7R CR W0 AI SHAPE SHORT EMP NQ HL PRE key stkobj md"] Lemma KKg : dealloc_core_K rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (munrestrict (hidc HS) Mk vpF) md' Ag p n0 lo hi T.
  Proof.
    pose proof KK as K0. unfold dealloc_core_K in K0 |- *. cbv zeta in K0 |- *.
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md'' AI' MI' AMD' FF PL LV0 LVq LB TCR SC PC NL VIR ERR FRO CALLER STK.   (* [comment removed for export] *)
    rewrite VIEWg in ERR, FRO, CALLER.
    destruct PREF as (CLO & LOSA & SAHI & HI47 & SPA0 & RAC2 & ST & SM & SOLO & SOHI).
    pose proof LIN as LL. pose proof f_SHG as SG. pose proof (fk_GEO rac spd m md A p n0 stkobj lo hi key PRE EMP SHORT) as G.
    apply (K0 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md'' AI' MI').
    - exact (amd_frame_trans md md' md'' AMDg AMD').
    - exact FF.
    - exact PL.
    - exact LV0.
    - exact LVq.
    - exact LB.
    - exact TCR.
    - exact SC.
    - exact PC.
    - exact NL.
    - intros c0 Hc V. apply (VIR c0 Hc). exact (popg_virgin_other A 24 U Fm N c0 Hc V).
    - intros i Hi. rewrite (ERR i Hi). cbn [cl_errno LPA]. unfold mrd.
      rewrite (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5.APopG3.AGimg A m md 24 U Fm N spaw vpF AI CR CEILw f_UMS f_FAM f_NC f_POS MUp (6193972 + i)); [reflexivity| clear - Hi; lia| clear - Hi; lia].
    - apply (frame_grow_free (pa_owned A) (pa_owned Ag) (pa_owned A') (newblk p n0) hi (hi - lo) v vpF (aview_of (pa_hull A') m')).
      + exact (popg_owned_mono A 24 U Fm N f_UMS f_FAM).
      + intros a Ha Og NO. destruct (popg_owned_new A 24 U Fm N CR f_UMS f_FAM f_NC a Og) as [X|[X|[X|[X|X]]]]; [exfalso; exact (NO X)| | | |].
        * split; [apply (t_VNEW U); [| exact X]; (first [ dand6 LL as _ _ _ _ (Q1 & Q2 & Q3 & _) _ | destruct LL as (_ & _ & _ & _ & (Q1 & Q2 & Q3 & _) & _) ]); unfold kFreeArrayOffset; lia|].
          unfold heap_zone, in_image. cbn [cl_image_lo cl_image_hi LPA]. clear - X G CE. kung_all. lia.
        * split; [apply (t_VNEWF Fm); [| exact X]; (first [ dand6 LL as _ _ _ _ (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _) _ | destruct LL as (_ & _ & _ & _ & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _) & _) ]); unfold kFreeArraySize; lia|].
          unfold heap_zone, in_image. cbn [cl_image_lo cl_image_hi LPA]. clear - X G CE. kung_all. lia.
        * exfalso. apply NO. apply (newUsh_ownedA A 24 U Fm W0 CR f_UMS f_FAM). clear - X SG. lia.
        * exfalso. apply NO. apply (newFsh_ownedA A 24 U Fm W0 CR f_UMS f_FAM). clear - X SG. lia.
      + intros a Ha NOg NW. replace (hi - (hi - lo)) with lo in NW by lia. apply (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopG5.APopG3.AGW A m 24 U Fm N spaw vpF MUp a Ha).
        apply (W_owned A 24 U Fm N W0 CR f_UMS f_FAM f_NC); [rewrite SAE; clear - NW LOSA SAHI SOLO SOHI; lia| exact NOg].
      + intros a Ha NI. unfold in_image in NI. cbn [cl_image_lo cl_image_hi LPA] in NI. apply NNp; clear - Ha NI; lia.
      + exact FRO.
    - intros a Ha. rewrite (CALLER a Ha). exact (vp_caller a Ha).
    - exact STK.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HL"] Lemma HLg : as_live Ag p = Some n0. Proof. exact HL. Qed.
  #[using="PRE key hi lo stkobj n0 p md m spd rac Clg"] Lemma IATg : a_ia_inited Ag = true. Proof. destruct PRE as (_ & _ & _ & X & _). exact X. Qed.
  #[using="PRE hi lo stkobj n0 p md m spd rac Clg"] Lemma KEYUg : In key (p_dkeys (a_pl Ag)).
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. Qed.
  #[using="CY5 GPK CL5 na ksc scr pad junk0 CEILw CEIL SAE PREF CE CR W0 AI SHORT EMP PRE key hi stkobj md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac"] Lemma STg : stk rsegs (aview_of HS (munrestrict (hidc HS) Mk vpF)) lo usp.
  Proof.
    rewrite VIEWg. destruct PREF as (CLO & LOSA & SAHI & HI47 & SPA0 & RAC2 & ST & SM & SOLO & SOHI). (first [ dand3 ST as S0 S1 S2 | destruct ST as (S0 & S1 & S2) ]).
    split; [exact S0|]. split; [exact S1|]. intros a Ha.
    assert (NNa : vpF (wz a) <> None).
    { apply NNp; [lia| right; lia| lia|]. destruct (S2 a Ha) as [X _]. unfold wview, wa in X. intros E0. apply X. rewrite E0.
      rewrite unsigned_lit by lia. rewrite (pa_find_segment_none a 1); [reflexivity| lia| right; lia]. }
    unfold wview, mrd, wa. destruct (vpF (wz a)) as [b|] eqn:E0; [| exfalso; exact (NNa eq_refl)]. split; [discriminate| exists b; reflexivity].
  Qed.
  #[using="CY5 GPK CL5 na ksc scr pad junk0 CEILw CEIL SAE PREF CE CR W0 AI SHORT EMP PRE key lo stkobj md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac"] Lemma SMHg : mapped (aview_of HS (munrestrict (hidc HS) Mk vpF)) usp (hi - usp).
  Proof.
    rewrite VIEWg. destruct PREF as (CLO & LOSA & SAHI & HI47 & SPA0 & RAC2 & ST & SM & SOLO & SOHI).
    intros i Hi. apply NNp; [lia| right; lia| lia| exact (SM i Hi)].
  Qed.
  #[using="CE AI HL PRE key hi lo stkobj A md m spd rac"] Lemma VBg : forall a, newblk p n0 a -> a < alloc_ceiling.
  Proof.
    intros a Ha. (first [ pose proof ((AFreeB1.free_geom A m md p n0 AI HL)) as dR_14; dand4 dR_14 as PAL PLO PCE PHI | destruct (AFreeB1.free_geom A m md p n0 AI HL) as (PAL & PLO & PCE & PHI) ]). destruct (free_n0 A m md p n0 AI HL) as [NR _].
    unfold newblk, blk in Ha. destruct Ha as [Ha|[_ Ha]].
    - clear - Ha PCE. lia.
    - unfold sh in Ha. clear - Ha PHI CE NR. kung_all.
      assert (p / 8 <= 2^44) by (apply Z.div_le_upper_bound; lia).
      assert ((n0 + 7) / 8 <= n0) by (apply Z.div_le_upper_bound; lia). unfold REQ_MAX in NR. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="MU5 CY5 GPK na ksc scr pad junk0 key lo stkobj s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac"] Lemma vh_entry : forall x, 0 <= x < 2^64 -> outside (Wi U Fm N) x -> vh (wz x) = v (wz x).
  Proof.
    intros x X64 OUT. unfold vh, mhyb. rewrite unsigned_lit by exact X64. destruct (in_fpb Wfo x) eqn:E0; [reflexivity|].
    apply MU5. rewrite unsigned_lit by exact X64. rewrite fk_outside_app. split; [exact OUT| apply in_fpb_false; exact E0].
  Qed.
  #[using="MU5 CY5 GPK na ksc scr pad junk0 CEILw CEIL SAE PREF CE SHORT EMP PRE key hi lo stkobj md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac"] Lemma vp_entry_rw : forall a cs, rw_cells rsegs v a cs -> disjoint_from (Wi U Fm N) a (Z.of_nat (cells_size cs)) -> rw_cells rsegs vpF a cs.
  Proof.
    intros a cs H DJ. pose proof H as [_ (W1 & W2 & _)]. apply (rw_cells_agree v vpF a cs H). intros x Hx.
    assert (OUT : outside (Wi U Fm N) x) by exact (disjoint_outside _ a _ x DJ Hx).
    rewrite AGR; [apply vh_entry; [lia| exact OUT]| lia|]. intros IN. unfold fk_Wi, fpop_Wq in OUT. cbn [outside] in OUT. (first [ dand3 OUT as _ O1 _ | destruct OUT as (_ & O1 & _) ]). exact (O1 IN).
  Qed.
  (* [comment removed for export] *)
  #[using="CEILw CEIL SAE PREF CE N7R CR SHAPE SHORT EMP PRE key hi lo stkobj md spd rac"] Lemma vp5_rw : forall a cs, rw_cells rsegs vpF a cs -> disjoint_from Wfo a (Z.of_nat (cells_size cs)) -> disjoint_from [(R, R + 8)] a (Z.of_nat (cells_size cs)) -> rw_cells rsegs v5 a cs.
  Proof.
    intros a cs H DJ DR. apply v5_rw; [| exact DJ]. pose proof H as [_ (W1 & W2 & _)]. apply (rw_cells_agree vpF vh a cs H). intros x Hx. symmetry. apply AGR; [lia|].
    pose proof (disjoint_outside _ a _ x DR Hx) as O. cbn [outside] in O. tauto.
  Qed.
  #[using="CEILw CEIL SAE PREF CE N7R CR SHAPE SHORT EMP PRE key hi lo stkobj md spd rac"] Lemma vp5_ro : forall a cs, ro_cells rsegs vpF a cs -> disjoint_from Wfo a (Z.of_nat (cells_size cs)) -> disjoint_from [(R, R + 8)] a (Z.of_nat (cells_size cs)) -> ro_cells rsegs v5 a cs.
  Proof.
    intros a cs H DJ DR. apply v5_ro; [| exact DJ]. pose proof H as [Hwf (W1 & W2 & _)]. rewrite cells_bytes_length in W2 by exact Hwf.
    apply (ro_cells_agree vpF vh a cs H). intros x Hx. symmetry. apply AGR; [lia|].
    pose proof (disjoint_outside _ a _ x DR Hx) as O. cbn [outside] in O. tauto.
  Qed.
  #[using="CEILw CEIL SAE PREF CE N7R CR SHAPE SHORT EMP PRE key hi lo stkobj md spd rac"] Lemma vp5_u32 : forall a ws, u32arr rsegs vpF a ws -> disjoint_from Wfo a (4 * Z.of_nat (length ws)) -> disjoint_from [(R, R + 8)] a (4 * Z.of_nat (length ws)) -> u32arr rsegs v5 a ws.
  Proof.
    intros a ws H DJ DR. apply v5_u32; [| exact DJ]. pose proof H as [_ (W1 & W2 & _)]. apply (u32arr_agree vpF vh a ws H). intros x Hx. symmetry. apply AGR; [lia|].
    pose proof (disjoint_outside _ a _ x DR Hx) as O. cbn [outside] in O. tauto.
  Qed.
  #[using="WM5 CY5 GPK na ksc scr pad junk0 CE SHORT EMP PRE key hi lo stkobj md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 spd rac"] Lemma WMp5 : wmono rsegs vpF v5.
  Proof.
    intros x Hx. pose proof (zr_word x) as XR; unfold inr64 in XR.
    destruct (classic (R <= bv_unsigned x < R + 8)) as [IN|OUT].
    - pose proof CY5 as (_ & _ & _ & _ & _ & _ & _ & MX5 & _). destruct MX5 as [_ (W00 & W1 & WW)]. cbn [cells_size csize Nat.add] in W1, WW.
      specialize (WW (bv_unsigned x - R) ltac:(lia)). replace (R + (bv_unsigned x - R)) with (bv_unsigned x) in WW by lia. unfold wa in WW. rewrite Z_to_bv_lit_self in WW. exact WW.
    - unfold wview in Hx |- *. rewrite (AGRw x OUT) in Hx. exact (mhyb_wmono_cur Wfo v v5 WM5 x Hx).
  Qed.
  Lemma unrestrict_ext : forall (Hd : word -> bool) (f1 f2 : mem) ms, (forall a, Hd a = true -> f1 a = f2 a) -> unrestrict Hd f1 ms = unrestrict Hd f2 ms.
  Proof.
    intros Hd f1 f2 ms E. unfold unrestrict. f_equal. apply functional_extensionality. intros a. unfold munrestrict. destruct (Hd a) eqn:Ha; [exact (E a Ha)| reflexivity].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CEILw CEIL SAE PREF CE N7R CR W0 AI SHAPE SHORT EMP NQ HL PRE hi md m rac"] Lemma end_place :
    (alloc_ceiling <= lo /\ lo <= usp - 1024) /\ usp mod 16 = 0 /\ usp <= 2^47 /\
    (p mod 16 = 0 /\ aobj (p + -16) (16 + 8 * r8) /\ 0x60a000 <= p + -16 /\ 1 <= n0 < 2^32 /\ 8 * r8 - 8 < n0 <= 8 * r8) /\
    ((aobj n0d kDepotNodesBlock /\ n0d + kDepotNodesBlock <= alloc_ceiling) /\ (aobj f0d kStackStoreBlockBytes /\ f0d + kStackStoreBlockBytes <= alloc_ceiling) /\
     (usp <= stkobj /\ stkobj + 2064 <= 2^47) /\ (1 <= length key <= 255)%nat) /\
    (apart (p + -16) (8 * r8 + 16) thr 4096 /\ apart n0d kDepotNodesBlock thr 4096 /\ apart f0d kStackStoreBlockBytes thr 4096) /\
    ((kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling /\ sb mod 4096 = 0) /\ (kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling /\ ri mod 128 = 0 /\ ri = sb + kSpaceSize)) /\
    (apart thr 4096 ri 4096 /\ apart thr 4096 sb (2^37) /\ apart ri 4096 sb (2^37) /\ apart ri 4096 (p + -16) (8 * r8 + 16) /\
     apart ri 4096 n0d kDepotNodesBlock /\ apart ri 4096 f0d kStackStoreBlockBytes) /\
    thr mod 16 = 0.
  Proof.
    destruct PREF as (CLO & LOSA & SAHI & HI47 & SPA0 & RAC2 & ST & SM & SOLO & SOHI).
    destruct (free_n0 A m md p n0 AI HL) as [NR US]. unfold REQ_MAX in NR.
    (first [ pose proof ((AFreeB1.free_geom A m md p n0 AI HL)) as dR_16; dand4 dR_16 as PAL PLO PCE PHI | destruct (AFreeB1.free_geom A m md p n0 AI HL) as (PAL & PLO & PCE & PHI) ]).
    pose proof (free_sep A m md p n0 AI HL) as SEPp. cbv zeta in SEPp. (first [ dand4 SEPp as SEP_pc SEP_pt SEP_pn SEP_pf | destruct SEPp as (SEP_pc & SEP_pt & SEP_pn & SEP_pf) ]).
    (first [ pose proof ((hit_sep A m md AI)) as dR_18; dand13 dR_18 as SEP_thr SEP_ctx SEP_tc SEP_n0 SEP_f0 SEP_n0t SEP_f0t SEP_n0c SEP_f0c DN01 DN02 DF01 DF02 | pose proof (hit_sep A m md AI) as (SEP_thr & SEP_ctx & SEP_tc & SEP_n0 & SEP_f0 & SEP_n0t & SEP_f0t & SEP_n0c & SEP_f0c & DN01 & DN02 & DF01 & DF02) ]).
    (first [ pose proof ((hit_place A m md AI)) as dR_19; dand4 dR_19 as TH1 TH2 THRA _ | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & _) ]).
    (first [ pose proof ((f24_sep A m md AI)) as dR_20; dand8 dR_20 as SEP_tr SEP_rs SEP_rc SEP_rn SEP_rf SEP_ts SEP_ns SEP_fs | pose proof (f24_sep A m md AI) as (SEP_tr & SEP_rs & SEP_rc & SEP_rn & SEP_rf & SEP_ts & SEP_ns & SEP_fs) ]).
    (first [ pose proof ((f24_ri A m md AI)) as dR_21; dand7 dR_21 as RIE RILO RIHI RIAL SBAL SBLO SBHI | pose proof (f24_ri A m md AI) as (RIE & RILO & RIHI & RIAL & SBAL & SBLO & SBHI) ]).
    (first [ pose proof (PLIN) as dR_22; dand3 dR_22 as (PP1 & PP2 & PP3 & PP4) (PP5 & PP6 & PP7 & PP8) _ | pose proof PLIN as ((PP1 & PP2 & PP3 & PP4) & (PP5 & PP6 & PP7 & PP8) & _) ]).
    pose proof (Z_div_mod_eq_full (n0 + 7) 8) as NDE. pose proof (Z.mod_pos_bound (n0 + 7) 8 ltac:(lia)) as ER.
    assert (KL : (1 <= length key <= 255)%nat).
    { destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KEYU & _).
      pose proof (wfP A W0) as PL. apply wf_place_cheap in PL.
      assert (DK1 : Forall (fun k => (1 <= length k <= 255)%nat) (p_dkeys (a_pl A))) by tauto. exact (proj1 (Forall_forall _ _) DK1 key KEYU). }
    split; [lia|]. split; [exact SPA0|]. split; [lia|].
    split; [split; [exact PAL|]; split; [exact PLO|]; split; [exact PP1|]; split; lia|].
    assert (STOR : usp <= stkobj /\ stkobj + 2064 <= 2^47) by lia.
    split; [exact (conj (conj DN01 DN02) (conj (conj DF01 DF02) (conj STOR KL)))|].
    split; [exact (conj SEP_pt (conj SEP_n0t SEP_f0t))|].
    split; [exact (conj (conj SBLO (conj SBHI SBAL)) (conj RILO (conj RIHI (conj RIAL RIE))))|].
    split; [| exact THRA].
    split; [exact SEP_tr|]. split; [exact SEP_ts|]. split; [exact SEP_rs|]. split; [unfold apart; clear - PP6; lia|]. exact (conj SEP_rn SEP_rf).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 a0g : word).
  #[warnings="-notation-for-abbreviation"] Local Notation ms0 :=
    (MS (mkR (wz gfa_popret) (wz uG) gp tp tq0 tq1 tq2 (wz R) (wz 0xb1d58) (wz 1) aq1 aq2 aq3 aq4 aq5 aq6 aq7
             a0g (wz 2305843009213693952) (wz (free_array_of sb 24)) (wz (E + 16)) (wz kk)
             (wz kMutexWriter) (wz 1500) (wz 16140901064495857663) s10 s11 tq3 tq4 tq5 tq6)
        F (wz gfa_popret) fc None (munrestrict (hidc HS) Mk v5) (seg_rom rsegs)).

  (* [comment removed for export] *)
  #[using="CL5"] Lemma VIEW5 : aview_of HS (munrestrict (hidc HS) Mk v5) = v5.
  Proof. unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact CL5. Qed.
  #[using="MU5 CY5 GPK CL5 SB5 HI5 PM MSH na ksc scr pad junk0 v5 mdk Mk CEILw CEIL SAE PREF CE N7R CR W0 AI SHAPE SHORT EMP NQ HL PRE key hi lo stkobj n0 p A md m s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 spd rac Clg"] Lemma HHg : m_halted md' = None. Proof. exact (proj2 (asI_minv Ag _ md' AIg24)). Qed.

  (* [comment removed for export] *)
  #[using="CEILw CEIL SAE PREF CE N7R CR SHAPE SHORT EMP NQ HL PRE key hi lo stkobj md spd rac"] Lemma vp5_img : forall a cs, ro_cells rsegs vpF a cs -> 0x10000 <= a -> a + Z.of_nat (cells_size cs) <= 0x187288 -> ro_cells rsegs v5 a cs.
  Proof.
    intros a cs H A1 A2. pose proof (proj1 (fk_Wmax_img rac spd m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT) a _ A1 A2) as DJ.
    lin_open. apply vp5_ro; [exact H| | cbn [disjoint_from]; split; [lia| exact I]].
    clear - DJ. unfold fk_Wi, fpop_Wq in DJ. cbn [app disjoint_from] in DJ. unfold fk_Wfo, fpop_Wfo. cbn [disjoint_from].
    (first [ dand15 DJ as _ _ _ _ _ _ _ _ _ _ _ _ _ _ D | destruct DJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D) ]). exact D.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="W0 AI PRE key hi lo stkobj n0 p md m spd rac Clg"] Lemma qt_len_range : 0 <= Z.of_nat (length (a_qthread A)) < 2^40.
  Proof.
    pose proof (conj W0 (ai_repr _ _ _ _ _ _ _ AI) : WF A /\ @arepr _ DepotRepL LPA AL_pasan [] A v) as AR.
    (first [ pose proof ((wfQ A W0)) as dR_24; dand5 dR_24 as _ _ _ QTB _ | pose proof (wfQ A W0) as (_ & _ & _ & QTB & _) ]). unfold kQuarantineCacheSize in QTB.
    assert (QWF : forall e, In e (q_entries (a_qthread A ++ a_qglobal A)) -> 0 <= qe_n e) by (intros e He; destruct (ATransp.qentry_wf A v AR e He) as [N0 _]; lia).
    assert (QBall : forall bs, (forall e, In e (q_entries bs) -> 0 <= qe_n e) -> Z.of_nat (length bs) * kQuarantineBatchBytes <= q_bytes bs).
    { clear. intros bs QW. induction bs as [|b0 r IH]; [cbn; lia|]. rewrite q_bytes_cons, batch_bytes_ebytes. cbn [length]. rewrite Nat2Z.inj_succ.
      assert (IHr : Z.of_nat (length r) * kQuarantineBatchBytes <= q_bytes r) by (apply IH; intros e He; apply QW; rewrite q_entries_cons; apply in_or_app; right; exact He).
      assert (EW : forall e, In e (ba_entries b0) -> 0 <= qe_n e) by (intros e He; apply QW; rewrite q_entries_cons; apply in_or_app; left; exact He).
      assert (0 <= ebytes (ba_entries b0)); [| lia].
      clear - EW. induction (ba_entries b0) as [|e es IHe]; [cbn; lia|].
      rewrite ebytes_cons. unfold qe_bytes. pose proof (user_size_pos (qe_n e) ltac:(apply EW; left; reflexivity)).
      assert (0 <= ebytes es) by (apply IHe; intros e' He'; apply EW; right; exact He'). lia. }
    assert (LENB : Z.of_nat (length (a_qthread A)) * kQuarantineBatchBytes <= q_bytes (a_qthread A)).
    { apply QBall. intros e He. apply QWF. unfold q_entries in He |- *. rewrite flat_map_app. apply in_or_app. left. exact He. }
    clear - LENB QTB. unfold kQuarantineBatchBytes in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="MI5 CY5 GPK na ksc scr pad junk0 MIv PRE key hi lo stkobj md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 spd rac"] Lemma MIh : mem_inv rsegs vh.
  Proof. intros x b Hx. unfold vh, mhyb in Hx. destruct (in_fpb Wfo (bv_unsigned x)); [exact (MIv _ _ Hx)| exact (MI5 _ _ Hx)]. Qed.
  #[using="MI5 CY5 GPK CL5 na ksc scr pad junk0 MIv CE CR W0 AI SHORT EMP PRE key hi lo stkobj md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 spd rac"] Lemma MIg : mem_inv rsegs (aview_of HS (munrestrict (hidc HS) Mk vpF)).
  Proof.
    rewrite VIEWg. intros x b Hx. unfold vpF in Hx.
    destruct (write_to_mem_some _ _ _ _ _ Hx) as [H | (i & Hi & ->)]; [exact (MIh _ _ H)|].
    rewrite length_le8 in Hi.
    pose proof CY5 as (_ & _ & _ & _ & _ & _ & _ & MX5 & _). destruct MX5 as [_ (W00 & W1 & WW)]. cbn [cells_size csize Nat.add] in W1, WW. specialize (WW (Z.of_nat i) ltac:(lia)).
    lin_open. unfold wa in *. rewrite unsigned_lit by lia.
    destruct (vh (Z_to_bv 64 (R + Z.of_nat i))) eqn:E0; [exact (MIh _ _ E0)|].
    unfold vh, mhyb in E0. destruct (in_fpb Wfo (bv_unsigned (Z_to_bv 64 (R + Z.of_nat i)))).
    - destruct (v5 (Z_to_bv 64 (R + Z.of_nat i))) eqn:E5; [exact (MI5 _ _ E5)| exact (wview_not_ro _ _ _ WW E5)].
    - exact (wview_not_ro _ _ _ WW E0).
  Qed.
  #[using="MU5 CY5 GPK CL5 na ksc scr pad junk0 CEILw CEIL SAE PREF CE CR W0 AI SHORT EMP NQ HL PRE hi lo md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 spd rac"] Lemma STOg : ro_cells rsegs (aview_of HS (munrestrict (hidc HS) Mk vpF)) stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length key)))].
  Proof.
    rewrite VIEWg. destruct PREF as (CLO & LOSA & SAHI & HI47 & SPA0 & RAC2 & ST & SM & SOLO & SOHI).
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STO & _).
    apply (ro_cells_agree v vpF _ _ STO). intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply vp_caller. lia.
  Qed.
  #[using="MU5 CY5 GPK CL5 na ksc scr pad junk0 CEILw CEIL SAE PREF CE N7R CR W0 AI SHAPE SHORT EMP NQ HL PRE hi lo md s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 spd rac"] Lemma TRWg : bytes_at rsegs (aview_of HS (munrestrict (hidc HS) Mk vpF)) (stkobj + 16) (u64s (map (Z_to_bv 64) key)).
  Proof.
    rewrite VIEWg. destruct PREF as (CLO & LOSA & SAHI & HI47 & SPA0 & RAC2 & ST & SM & SOLO & SOHI).
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TRW & _).
    (first [ pose proof (end_place) as dR_25; dand6 dR_25 as _ _ _ _ (_ & _ & _ & KL) _ | pose proof end_place as (_ & _ & _ & _ & (_ & _ & _ & KL) & _) ]).
    apply (bytes_at_agree v vpF _ _ TRW). intros x Hx. rewrite u64s_length, length_map in Hx. apply vp_caller. lia.
  Qed.
  #[using="PRE hi lo stkobj n0 p A md m spd rac Clg"] Lemma KRg : Forall (fun w => 0 <= w < 2^64) key.
  Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KR). exact KR. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="MI5 WM5 MU5 LErefl CY5 GPK CL5 SB5 HI5 PM MSH na ksc scr pad junk0 mdk KK CEILw CEIL SAE PREF MIv CE N7R CR W0 AI SHAPE SHORT EMP NQ HL PRE key hi lo stkobj p md m s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac"] Theorem end_new0G : forall tk : ftail,
    a_qthread A = [] ->
    match tk with
    | TN => n0 + kQuarantineBatchBytes <= kQuarantineCacheSize
    | T0 => kQuarantineCacheSize < n0 + kQuarantineBatchBytes /\ a_qglobal A = [] /\ n0 + kQuarantineBatchBytes <= kQuarantineMaxSize
    | TA => kQuarantineCacheSize < n0 + kQuarantineBatchBytes /\ a_qglobal A <> [] /\ q_bytes (a_qglobal A) + (n0 + kQuarantineBatchBytes) <= kQuarantineMaxSize
    end ->
    srealizes rsegs (mkCfg ms0 md') T.
  Proof.
    intros tk QTE TKC.
    destruct PREF as (CLO & LOSA & SAHI & HI47 & SPA0 & RAC2 & ST & SM & SOLO & SOHI).
    (first [ pose proof ((ar_nc A 24 W0 CR EMP SHORT)) as dR_26; dand5 dR_26 as _ _ _ NK _ | pose proof (ar_nc A 24 W0 CR EMP SHORT) as (_ & _ & _ & NK & _) ]). (first [ pose proof ((ar_k A 24 CR)) as dR_27; dand3 dR_27 as _ KR1 _ | pose proof (ar_k A 24 CR) as (_ & KR1 & _) ]).
    assert (NF1g : 1 <= Z.of_nat (length (rg_free (a_reg Ag kQuarantineBatchClass)))).
    { unfold kQuarantineBatchClass. rewrite popg_reg_c. cbn [grow rg_free]. rewrite length_app, newfree_length by (pose proof f_NC; lia). lia. }
    refine (dealloc_new0GX rac spd gp rac rac rac s0 s1 rac rac rac rac s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rac rac rac rac F fc _ md' Ag p n0 stkobj lo hi key T AIg24 MIg HLg IATg CLO LOSA SAHI HI47 SPA0 RAC2 STg SMHg SOLO SOHI STOg TRWg KEYUg KRg NQ KKg ms0 _ tk QTE eq_refl EMP NF1g TKC).
    (* [comment removed for export] *)
    intros tk' b1 fr fd ks na' statv bj0 bj1 bj2 bj3 fr24 gf gl gn gqb kb b kw nf Efr24 Egf Egl Egn Egqb Ekb Eb Ekw Enf
           HDR B1R TST FRR FDR Afap KSMW NFR BLO BHI BFA Abt Abp Abn Abf TPRE TOK TAP TAPR THRA LKS CSB CRI QC PC24 STA MXc NFCc NALc FARRc BC _ KC.
    rewrite VIEWg in *. change (a_pl Ag) with (a_pl A) in *. change (a_sb Ag) with sb in *. change (a_ri Ag) with ri in *. change (a_depot Ag) with (a_depot A) in *.
    (* [comment removed for export] *)
    (first [ pose proof ((cy_fcells _ _ _ _ _ _ _ v5 CY5 LErefl)) as dR_28; dex6 dR_28 as b1r frr fdr nxr bszr statvr; dand11 dR_28 as (B1Rr & B1Mr & FRRr & FDRr) HDRe TSTe TST5 HDR5 CTX5 SHD5 DR5 QC5 LBC5 STA5 | pose proof ((cy_fcells _ _ _ _ _ _ _ v5 CY5 LErefl)) as dR_28; dand17 dR_28 as b1r frr fdr nxr bszr statvr (B1Rr & B1Mr & FRRr & FDRr) HDRe TSTe TST5 HDR5 CTX5 SHD5 DR5 QC5 LBC5 STA5 | destruct (cy_fcells _ _ _ _ _ _ _ v5 CY5 LErefl) as (b1r & frr & fdr & nxr & bszr & statvr & (B1Rr & B1Mr & FRRr & FDRr) & HDRe & TSTe & TST5 & HDR5 & CTX5 & SHD5 & DR5 & QC5 & LBC5 & STA5) ]).
    assert (EB1 : b1r = b1).
    { pose proof (vp_entry_rw _ _ HDRe ltac:(apply (fk_Wq_chunk rac spd m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT); pose proof PLIN as ((_ & _ & P3 & _) & _); cbn; lia)) as X.
      exact (rw_C1_snd_inj vpF _ _ _ _ _ _ B1Rr B1R X HDR). }
    assert (EFR : frr = fr /\ fdr = fd).
    { pose proof (vp_entry_rw _ _ TSTe ltac:(apply (fk_Wq_thr rac spd m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT); cbn; lia)) as X.
      exact (rw_C8x2_inj vpF _ _ _ _ _ FRRr FDRr FRR FDR X TST). }
    destruct EFR as [EFR1 EFR2]. subst b1r frr fdr.
    (* [comment removed for export] *)
    (first [ dand9 end_place as LO SPA SPH (PAL & PLO & PNB & NR & R8) (DN0 & DF0 & STOR & KL) (SEP_pt & SEP_n0t & SEP_f0t) ((SBLO & SBHI & SBAL) & (RILO & RIHI & RIAL & RIE)) (SEP_tr & SEP_ts & SEP_rs & SEP_rp & SEP_rn & SEP_rf) _ | destruct end_place as (LO & SPA & SPH & (PAL & PLO & PNB & NR & R8) & (DN0 & DF0 & STOR & KL) & (SEP_pt & SEP_n0t & SEP_f0t) & ((SBLO & SBHI & SBAL) & (RILO & RIHI & RIAL & RIE)) & (SEP_tr & SEP_ts & SEP_rs & SEP_rp & SEP_rn & SEP_rf) & _) ]).
    pose proof (f24_geom Ag _ md' AIg24 NF1g) as GB. cbv zeta in GB. change (a_sb Ag) with sb in GB. rewrite <- Efr24, <- Ekb, <- Eb in GB. (first [ dand3 GB as BE KWR _ | destruct GB as (BE & KWR & _) ]).
    assert (KWV : bv_unsigned kw = kb * 512) by (rewrite Ekw; apply unsigned_lit; clear - KWR; lia).
    assert (BE' : sb + 24 * 2^32 + 16 * bv_unsigned kw = b) by (rewrite KWV; symmetry; exact BE).
    assert (DJR : forall a l, (a + l <= ri \/ ri + 4096 <= a) -> disjoint_from [(R, R + 8)] a l) by (intros a l Hal; cbn [disjoint_from]; split; [lia| exact I]).
    assert (Abr : apart b 8192 ri 4096) by (unfold apart; clear - BFA RIE; unfold free_array_of, kSpaceSize in *; lia).
    assert (DJbW : disjoint_from Wfo b 32).
    { (first [ pose proof (PLIN) as dR_31; dand4 dR_31 as (_ & _ & P3 & _) _ (S1 & S2 & S3) _ | pose proof PLIN as ((_ & _ & P3 & _) & _ & (S1 & S2 & S3) & _) ]). unfold fk_Wfo, fpop_Wfo. cbn [disjoint_from]. unfold apart, AMallocA.apart, kDepotNodesBlock, kStackStoreBlockBytes, kHighMemBeg in *.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I;
        first [ solve [clear - Abp P3; lia] | solve [clear - Abt; lia] | solve [clear - BLO; lia] | solve [clear - Abn; lia] | solve [clear - Abf; lia] | solve [clear - BLO S2; lia] ]. }
    (* [comment removed for export] *)
    unfold apart, AMallocA.apart in SEP_tr.
    pose proof (vp5_rw _ _ PC24 ltac:(apply Wfo_thr; cbn; lia) ltac:(apply DJR; cbn; lia)) as PC5.
    pose proof (vp5_rw _ _ STA ltac:(apply Wfo_thr; cbn; lia) ltac:(apply DJR; cbn; lia)) as STA5'.
    pose proof (vp5_rw _ _ QC ltac:(apply Wfo_thr; cbn; lia) ltac:(apply DJR; cbn; lia)) as QC5'.
    pose proof (vp5_rw _ _ BC ltac:(exact DJbW) ltac:(apply DJR; unfold apart in Abr; cbn; lia)) as BC5.
    pose proof (vp5_rw _ _ NFCc ltac:(apply Wfo_ri; cbn; lia) ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I])) as NFC5.
    pose proof (vp5_rw _ _ NALc ltac:(apply Wfo_ri; cbn; lia) ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I])) as NAL5.
    pose proof (vp5_img _ _ CSB ltac:(lia) ltac:(cbn; lia)) as CSB5.
    assert (FARR5 : u32arr rsegs v5 (free_array_of sb 24 + 4 * (nf - 1)) [kw]).
    { lin_open. apply (vp5_u32 _ _ FARRc).
      - apply Wfo_reg; cbn [length]; unfold free_array_of, kFreeArrayOffset, region_beg, kRegionSize in *; lia.
      - apply DJR. cbn [length]. unfold free_array_of, kSpaceSize in *. lia. }
    pose proof CY5 as (_ & _ & _ & PFR5 & EF5 & RF5 & GF5 & MX5 & _).
    pose proof (proj1 (proj2 GPK)) as ST5.
    (* [comment removed for export] *)
    eapply (srz_evt_restrict rsegs HS (hull_segsR Ag) pa_wxR _ (pa_eager Ag) _ _ md' T HI5 HHg).
    { rewrite restrict_MS. change (mrestrict (hidc HS) (munrestrict (hidc HS) Mk v5)) with (aview_of HS (munrestrict (hidc HS) Mk v5)). rewrite VIEW5.
      pose proof (free_cpop_tail0 rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v lo p n0 b1 pa_tsd ctx thr r8 n0d f0d fr fd stkobj (a_depot A) key
                    LO SPA SPH PAL PLO PNB NR R8 (hit_TC A m md AI) DN0 DF0 STOR KL SEP_pt SEP_n0t SEP_f0t sb ri SBLO SBHI SBAL RILO RIHI RIAL
                    ltac:(exact SEP_tr) SEP_ts SEP_rs SEP_rp SEP_rn SEP_rf
                    a0g tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 scr junk0 pad statv na' kw bj0 bj1 bj2 bj3 nf 0 0 0 ks v5) as EV.
      cbv zeta in EV. rewrite BE' in EV.
      specialize (EV THRA LKS NFR KSMW BLO BHI BFA Abt Abp Abn Abf Abr MI5 ST5 PFR5 EF5 RF5 GF5 TST5 HDR5 CTX5 SHD5 DR5 CSB5 MX5 NFC5 NAL5 FARR5 PC5 STA5' BC5 QC5').
      replace (ret_pc (wz gfa_popret)) with (wz gfa_popret : word) in EV by (symmetry; apply ret_pc_even; [unfold gfa_popret; lia| reflexivity]).
      change (Z.shiftr 2 1) with kk in EV.
      eapply evt_cut; [exact EV|]. clear EV.
      intros ms7 PO.
      assert (FCog : free_consts vpF) by (pose proof (free_FCo Ag _ md' AIg24) as X; rewrite VIEWg in X; exact X).
      assert (TCg : thread_cells vpF tp pa_tsd ctx thr) by (pose proof (hit_TC Ag _ md' AIg24) as X; rewrite VIEWg in X; exact X).
      assert (LO704 : alloc_ceiling <= lo /\ lo <= usp - 704) by (clear - LO; lia).
      pose proof BLO as BLO'. pose proof BHI as BHI'. pose proof Abt as Abt'. rewrite <- BE' in BLO', BHI', Abt'.
      apply (free_chitG_new0F_tl rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc vpF lo p n0 b1 pa_tsd ctx thr r8 n0d f0d fr fd stkobj (a_depot A) key
               LO704 SPH PAL PLO PNB NR R8 FCog TCg DN0 DF0 STOR KL SEP_pt SEP_n0t SEP_f0t sb ri nf kw na' SBLO SBHI RILO RIHI SEP_tr SEP_ts NFR BLO' BHI' Abt'
               tk' gn gf gl gqb (Z_to_bv 64 0) 0 ks statv bj0 bj1 bj2 bj3 ms7).
      all: rewrite ?BE'.
      all: try first [ exact TPRE | exact TOK | exact TAP | exact TAPR | exact THRA | exact LKS | exact CSB | exact CRI | exact QC | exact PC24 | exact STA | exact MXc | exact NFCc | exact NALc | exact FARRc | exact BC | lia ].
      (* [comment removed for export] *)
      unfold free_cenq_new0F_post in PO. cbv zeta in PO. rewrite ?BE' in PO.
      (first [ dex17 PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7; dand19 PO as -> MUc WMc MI7 ST7 PFR7 TST7 HDR7 CTX7 SHD7 DR7 QC7 PC7 STA7 B7 MX7 NFC7 NAL7 FARR7 | dand36 PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7 -> MUc WMc MI7 ST7 PFR7 TST7 HDR7 CTX7 SHD7 DR7 QC7 PC7 STA7 B7 MX7 NFC7 NAL7 FARR7 | destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & statv' & m7 & -> & MUc & WMc & MI7 & ST7 & PFR7 & TST7 & HDR7 & CTX7 & SHD7 & DR7 & QC7 & PC7 & STA7 & B7 & MX7 & NFC7 & NAL7 & FARR7) ]).
      unfold free_chead_new0F_post. cbv zeta. rewrite ?BE'.
      first [ hotw_ex17 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7 | exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', statv', m7 ]. split; [reflexivity|].
      split.
      { intros x Hx. unfold free_chit_new0F_W, free_cprefix_W in Hx. cbn [app outside] in Hx.
        (first [ dand16 Hx as O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 O13 O14 O15 _ | destruct Hx as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15 & _) ]).
        rewrite (MUc x); [| unfold free_ccore_new0F_W; cbn [outside]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; first [assumption | lia]].
        rewrite AGRw by lia. unfold vh. symmetry. apply mhyb_out. apply in_fpb_false. unfold fk_Wfo, fpop_Wfo. cbn [outside].
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; assumption. }
      split; [exact (wmono_trans _ _ _ _ WMp5 WMc)|].
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }

    intros msr' md'' HQ HI'' SB'' CL''. change (ms_mem ms0) with (munrestrict (hidc HS) Mk v5).
    rewrite (unrestrict_ext (hidc HS) (munrestrict (hidc HS) Mk v5) (munrestrict (hidc HS) Mk vpF) msr') by (intros a Ha; unfold munrestrict; rewrite Ha; reflexivity).
    exact (KC msr' md'' HQ HI'' SB'' CL'').
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="MI5 WM5 MU5 LErefl CY5 GPK CL5 SB5 HI5 PM MSH na ksc scr pad junk0 mdk KK CEILw CEIL SAE PREF MIv CE N7R CR W0 AI SHAPE SHORT EMP NQ HL PRE key hi lo stkobj p md m s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac"] Theorem end_newfullG : forall tk : ftail,
    a_qthread A <> [] -> Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) = kQuarantineBatchCount ->
    match tk with
    | TN => q_bytes (a_qthread A) + n0 + kQuarantineBatchBytes <= kQuarantineCacheSize
    | T0 => kQuarantineCacheSize < q_bytes (a_qthread A) + n0 + kQuarantineBatchBytes /\ a_qglobal A = [] /\ q_bytes (a_qthread A) + n0 + kQuarantineBatchBytes <= kQuarantineMaxSize
    | TA => kQuarantineCacheSize < q_bytes (a_qthread A) + n0 + kQuarantineBatchBytes /\ a_qglobal A <> [] /\
            q_bytes (a_qglobal A) + (q_bytes (a_qthread A) + n0 + kQuarantineBatchBytes) <= kQuarantineMaxSize
    end ->
    srealizes rsegs (mkCfg ms0 md') T.
  Proof.
    intros tk QNE FULL TKC.
    destruct PREF as (CLO & LOSA & SAHI & HI47 & SPA0 & RAC2 & ST & SM & SOLO & SOHI).
    (first [ pose proof ((ar_nc A 24 W0 CR EMP SHORT)) as dR_34; dand5 dR_34 as _ _ _ NK _ | pose proof (ar_nc A 24 W0 CR EMP SHORT) as (_ & _ & _ & NK & _) ]). (first [ pose proof ((ar_k A 24 CR)) as dR_35; dand3 dR_35 as _ KR1 _ | pose proof (ar_k A 24 CR) as (_ & KR1 & _) ]).
    assert (NF1g : 1 <= Z.of_nat (length (rg_free (a_reg Ag kQuarantineBatchClass)))).
    { unfold kQuarantineBatchClass. rewrite popg_reg_c. cbn [grow rg_free]. rewrite length_app, newfree_length by (pose proof f_NC; lia). lia. }
    refine (dealloc_newfullGX rac spd gp rac rac rac s0 s1 rac rac rac rac s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rac rac rac rac F fc _ md' Ag p n0 stkobj lo hi key T AIg24 MIg HLg IATg CLO LOSA SAHI HI47 SPA0 RAC2 STg SMHg SOLO SOHI STOg TRWg KEYUg KRg NQ KKg ms0 _ tk QNE FULL eq_refl EMP NF1g TKC).
    (* [comment removed for export] *)
    intros tk' b1 fr fd ks na' statv bj0 bj1 bj2 bj3 fr24 gf gl gn gqb kb b kw nf qt bl lb Efr24 Egf Egl Egn Egqb Ekb Eb Ekw Enf Eqt Ebl Elb
           HDR B1R TST FRR FDR Afap KSMW NFR BLO BHI BFA Abt Abp Abn Abf TPRE TOK TAP TAPR NB0 NBR FBR QB0 THRA LKS LBL LBH' LBFA Alt Alp Alc Aln Alf Alr Abl CSB CRI QC LB PC24 STA MXc NFCc NALc FARRc BC _ KC.
    rewrite VIEWg in *. change (a_pl Ag) with (a_pl A) in *. change (a_sb Ag) with sb in *. change (a_ri Ag) with ri in *. change (a_depot Ag) with (a_depot A) in *.
    (* [comment removed for export] *)
    (first [ pose proof ((cy_fcells _ _ _ _ _ _ _ v5 CY5 LErefl)) as dR_36; dex6 dR_36 as b1r frr fdr nxr bszr statvr; dand11 dR_36 as (B1Rr & B1Mr & FRRr & FDRr) HDRe TSTe TST5 HDR5 CTX5 SHD5 DR5 QC5 LBC5 STA5 | pose proof ((cy_fcells _ _ _ _ _ _ _ v5 CY5 LErefl)) as dR_36; dand17 dR_36 as b1r frr fdr nxr bszr statvr (B1Rr & B1Mr & FRRr & FDRr) HDRe TSTe TST5 HDR5 CTX5 SHD5 DR5 QC5 LBC5 STA5 | destruct (cy_fcells _ _ _ _ _ _ _ v5 CY5 LErefl) as (b1r & frr & fdr & nxr & bszr & statvr & (B1Rr & B1Mr & FRRr & FDRr) & HDRe & TSTe & TST5 & HDR5 & CTX5 & SHD5 & DR5 & QC5 & LBC5 & STA5) ]).
    assert (EB1 : b1r = b1).
    { pose proof (vp_entry_rw _ _ HDRe ltac:(apply (fk_Wq_chunk rac spd m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT); pose proof PLIN as ((_ & _ & P3 & _) & _); cbn; lia)) as X.
      exact (rw_C1_snd_inj vpF _ _ _ _ _ _ B1Rr B1R X HDR). }
    assert (EFR : frr = fr /\ fdr = fd).
    { pose proof (vp_entry_rw _ _ TSTe ltac:(apply (fk_Wq_thr rac spd m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT); cbn; lia)) as X.
      exact (rw_C8x2_inj vpF _ _ _ _ _ FRRr FDRr FRR FDR X TST). }
    destruct EFR as [EFR1 EFR2]. subst b1r frr fdr.
    (* [comment removed for export] *)
    (first [ dand9 end_place as LO SPA SPH (PAL & PLO & PNB & NR & R8) (DN0 & DF0 & STOR & KL) (SEP_pt & SEP_n0t & SEP_f0t) ((SBLO & SBHI & SBAL) & (RILO & RIHI & RIAL & RIE)) (SEP_tr & SEP_ts & SEP_rs & SEP_rp & SEP_rn & SEP_rf) _ | destruct end_place as (LO & SPA & SPH & (PAL & PLO & PNB & NR & R8) & (DN0 & DF0 & STOR & KL) & (SEP_pt & SEP_n0t & SEP_f0t) & ((SBLO & SBHI & SBAL) & (RILO & RIHI & RIAL & RIE)) & (SEP_tr & SEP_ts & SEP_rs & SEP_rp & SEP_rn & SEP_rf) & _) ]).
    pose proof (f24_geom Ag _ md' AIg24 NF1g) as GB. cbv zeta in GB. change (a_sb Ag) with sb in GB. rewrite <- Efr24, <- Ekb, <- Eb in GB. (first [ dand3 GB as BE KWR _ | destruct GB as (BE & KWR & _) ]).
    assert (KWV : bv_unsigned kw = kb * 512) by (rewrite Ekw; apply unsigned_lit; clear - KWR; lia).
    assert (BE' : sb + 24 * 2^32 + 16 * bv_unsigned kw = b) by (rewrite KWV; symmetry; exact BE).
    assert (DJR : forall a l, (a + l <= ri \/ ri + 4096 <= a) -> disjoint_from [(R, R + 8)] a l) by (intros a l Hal; cbn [disjoint_from]; split; [lia| exact I]).
    assert (Abr : apart b 8192 ri 4096) by (unfold apart; clear - BFA RIE; unfold free_array_of, kSpaceSize in *; lia).
    assert (DJbW : disjoint_from Wfo b 32).
    { (first [ pose proof (PLIN) as dR_39; dand4 dR_39 as (_ & _ & P3 & _) _ (S1 & S2 & S3) _ | pose proof PLIN as ((_ & _ & P3 & _) & _ & (S1 & S2 & S3) & _) ]). unfold fk_Wfo, fpop_Wfo. cbn [disjoint_from]. unfold apart, AMallocA.apart, kDepotNodesBlock, kStackStoreBlockBytes, kHighMemBeg in *.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I;
        first [ solve [clear - Abp P3; lia] | solve [clear - Abt; lia] | solve [clear - BLO; lia] | solve [clear - Abn; lia] | solve [clear - Abf; lia] | solve [clear - BLO S2; lia] ]. }
    (* [comment removed for export] *)
    unfold apart, AMallocA.apart in SEP_tr.
    pose proof (vp5_rw _ _ PC24 ltac:(apply Wfo_thr; cbn; lia) ltac:(apply DJR; cbn; lia)) as PC5.
    pose proof (vp5_rw _ _ STA ltac:(apply Wfo_thr; cbn; lia) ltac:(apply DJR; cbn; lia)) as STA5'.
    pose proof (vp5_rw _ _ QC ltac:(apply Wfo_thr; cbn; lia) ltac:(apply DJR; cbn; lia)) as QC5'.
    assert (DJlW : disjoint_from Wfo lb 24).
    { (first [ pose proof (PLIN) as dR_40; dand4 dR_40 as (_ & _ & P3 & _) _ (S1 & S2 & S3) _ | pose proof PLIN as ((_ & _ & P3 & _) & _ & (S1 & S2 & S3) & _) ]). unfold fk_Wfo, fpop_Wfo. cbn [disjoint_from]. unfold apart, AMallocA.apart, kDepotNodesBlock, kStackStoreBlockBytes, kHighMemBeg in *.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I;
        first [ solve [clear - Alp P3; lia] | solve [clear - Alt; lia] | solve [clear - LBL; lia] | solve [clear - Aln; lia] | solve [clear - Alf; lia] | solve [clear - LBL S2; lia] ]. }
    pose proof (vp5_rw _ _ LB ltac:(exact DJlW) ltac:(apply DJR; unfold apart in Alr; cbn; lia)) as LB5.
    pose proof (vp5_rw _ _ BC ltac:(exact DJbW) ltac:(apply DJR; unfold apart in Abr; cbn; lia)) as BC5.
    pose proof (vp5_rw _ _ NFCc ltac:(apply Wfo_ri; cbn; lia) ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I])) as NFC5.
    pose proof (vp5_rw _ _ NALc ltac:(apply Wfo_ri; cbn; lia) ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I])) as NAL5.
    pose proof (vp5_img _ _ CSB ltac:(lia) ltac:(cbn; lia)) as CSB5.
    assert (FARR5 : u32arr rsegs v5 (free_array_of sb 24 + 4 * (nf - 1)) [kw]).
    { lin_open. apply (vp5_u32 _ _ FARRc).
      - apply Wfo_reg; cbn [length]; unfold free_array_of, kFreeArrayOffset, region_beg, kRegionSize in *; lia.
      - apply DJR. cbn [length]. unfold free_array_of, kSpaceSize in *. lia. }
    pose proof CY5 as (_ & _ & _ & PFR5 & EF5 & RF5 & GF5 & MX5 & _).
    pose proof (proj1 (proj2 GPK)) as ST5.
    (* [comment removed for export] *)
    eapply (srz_evt_restrict rsegs HS (hull_segsR Ag) pa_wxR _ (pa_eager Ag) _ _ md' T HI5 HHg).
    { rewrite restrict_MS. change (mrestrict (hidc HS) (munrestrict (hidc HS) Mk v5)) with (aview_of HS (munrestrict (hidc HS) Mk v5)). rewrite VIEW5.
      pose proof (free_cpop_tailF rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v lo p n0 b1 pa_tsd ctx thr r8 n0d f0d fr fd stkobj (a_depot A) key
                    LO SPA SPH PAL PLO PNB NR R8 (hit_TC A m md AI) DN0 DF0 STOR KL SEP_pt SEP_n0t SEP_f0t sb ri SBLO SBHI SBAL RILO RIHI RIAL
                    ltac:(exact SEP_tr) SEP_ts SEP_rs SEP_rp SEP_rn SEP_rf
                    a0g tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 scr junk0 pad statv na' kw bj0 bj1 bj2 bj3 nf (qc_first Ag qt) lb (q_bytes qt) ks v5) as EV.
      cbv zeta in EV. rewrite BE' in EV.
      specialize (EV THRA LKS NFR KSMW BLO BHI BFA Abt Abp Abn Abf Abr MI5 ST5 PFR5 EF5 RF5 GF5 TST5 HDR5 CTX5 SHD5 DR5 CSB5 MX5 NFC5 NAL5 FARR5 PC5 STA5' BC5
                     (Z.of_nat (length qt)) 0 (batch_bytes bl) NB0 NBR LBL LBH' LBFA Alt Alp Alc Aln Alf Alr Abl QC5' LB5).
      replace (ret_pc (wz gfa_popret)) with (wz gfa_popret : word) in EV by (symmetry; apply ret_pc_even; [unfold gfa_popret; lia| reflexivity]).
      change (Z.shiftr 2 1) with kk in EV.
      eapply evt_cut; [exact EV|]. clear EV.
      intros ms7 PO.
      assert (FCog : free_consts vpF) by (pose proof (free_FCo Ag _ md' AIg24) as X; rewrite VIEWg in X; exact X).
      assert (TCg : thread_cells vpF tp pa_tsd ctx thr) by (pose proof (hit_TC Ag _ md' AIg24) as X; rewrite VIEWg in X; exact X).
      assert (LO704 : alloc_ceiling <= lo /\ lo <= usp - 704) by (clear - LO; lia).
      pose proof BLO as BLO'. pose proof BHI as BHI'. pose proof Abt as Abt'. rewrite <- BE' in BLO', BHI', Abt'.
      apply (free_chitG_newfullF_tl rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc vpF lo p n0 b1 pa_tsd ctx thr r8 n0d f0d fr fd stkobj (a_depot A) key
               LO704 SPH PAL PLO PNB NR R8 FCog TCg DN0 DF0 STOR KL SEP_pt SEP_n0t SEP_f0t sb ri nf kw na' SBLO SBHI RILO RIHI SEP_tr SEP_ts NFR BLO' BHI' Abt'
               tk' gn gf gl gqb (Z_to_bv 64 0) (Z.of_nat (length qt)) (qc_first Ag qt) lb (q_bytes qt) 0 (batch_bytes bl) ks statv bj0 bj1 bj2 bj3 ms7).
      all: rewrite ?BE'.
      all: try first [ exact TPRE | exact TOK | exact TAP | exact TAPR | exact NB0 | exact NBR | exact FBR | exact QB0 | exact THRA | exact LKS | exact LBL | exact LBH' | exact LBFA | exact Alt | exact Alp | exact Alc | exact Aln | exact Alf | exact Alr | exact Abl | exact LB | exact CSB | exact CRI | exact QC | exact PC24 | exact STA | exact MXc | exact NFCc | exact NALc | exact FARRc | exact BC | lia ].
      (* [comment removed for export] *)
      unfold free_cenq_newfullF_post in PO. cbv zeta in PO. rewrite ?BE' in PO.
      (first [ dex17 PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7; dand20 PO as -> MUc WMc MI7 ST7 PFR7 TST7 HDR7 CTX7 SHD7 DR7 QC7 LB7 PC7 STA7 B7 MX7 NFC7 NAL7 FARR7 | dand36 PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7 -> MUc WMc MI7 ST7 PFR7 TST7 HDR7 CTX7 SHD7 DR7 QC7 LB7 PC7 STA7 B7 MX7 NFC7 dR_PO_t0; destruct dR_PO_t0 as [NAL7 FARR7] | destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & statv' & m7 & -> & MUc & WMc & MI7 & ST7 & PFR7 & TST7 & HDR7 & CTX7 & SHD7 & DR7 & QC7 & LB7 & PC7 & STA7 & B7 & MX7 & NFC7 & NAL7 & FARR7) ]).
      unfold free_chead_newfullF_post. cbv zeta. rewrite ?BE'.
      first [ hotw_ex17 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7 | exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', statv', m7 ]. split; [reflexivity|].
      split.
      { intros x Hx. unfold free_chit_newfullF_W, free_cprefix_W in Hx. cbn [app outside] in Hx.
        repeat match type of Hx with _ /\ _ => let O := fresh "O" in destruct Hx as [O Hx] end.
        rewrite (MUc x); [| unfold free_ccore_newfullF_W; cbn [outside]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; first [assumption | lia]].
        rewrite AGRw by lia. unfold vh. symmetry. apply mhyb_out. apply in_fpb_false. unfold fk_Wfo, fpop_Wfo. cbn [outside].
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; assumption. }
      split; [exact (wmono_trans _ _ _ _ WMp5 WMc)|].
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }

    intros msr' md'' HQ HI'' SB'' CL''. change (ms_mem ms0) with (munrestrict (hidc HS) Mk v5).
    rewrite (unrestrict_ext (hidc HS) (munrestrict (hidc HS) Mk v5) (munrestrict (hidc HS) Mk vpF) msr') by (intros a Ha; unfold munrestrict; rewrite Ha; reflexivity).
    exact (KC msr' md'' HQ HI'' SB'' CL'').
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="MI5 WM5 MU5 LErefl CY5 GPK CL5 SB5 HI5 PM MSH na ksc scr pad junk0 mdk KK CEILw CEIL SAE PREF MIv CE N7R CR W0 AI SHAPE SHORT EMP NQ HL PRE key hi lo stkobj p md m s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac"] Theorem end_new0R : forall tk : ftail,
    a_qthread A = [] ->
    match tk with
    | TN => False
    | T0 => kQuarantineCacheSize < n0 + kQuarantineBatchBytes /\ a_qglobal A = [] /\ kQuarantineMaxSize < n0 + kQuarantineBatchBytes
    | TA => kQuarantineCacheSize < n0 + kQuarantineBatchBytes /\ a_qglobal A <> [] /\ kQuarantineMaxSize < q_bytes (a_qglobal A) + (n0 + kQuarantineBatchBytes)
    end ->
    srealizes rsegs (mkCfg ms0 md') T.
  Proof.
    intros tk QTE TKC.
    destruct PREF as (CLO & LOSA & SAHI & HI47 & SPA0 & RAC2 & ST & SM & SOLO & SOHI).
    (first [ pose proof ((ar_nc A 24 W0 CR EMP SHORT)) as dR_42; dand5 dR_42 as _ _ _ NK _ | pose proof (ar_nc A 24 W0 CR EMP SHORT) as (_ & _ & _ & NK & _) ]). (first [ pose proof ((ar_k A 24 CR)) as dR_43; dand3 dR_43 as _ KR1 _ | pose proof (ar_k A 24 CR) as (_ & KR1 & _) ]).
    assert (NF1g : 1 <= Z.of_nat (length (rg_free (a_reg Ag kQuarantineBatchClass)))).
    { unfold kQuarantineBatchClass. rewrite popg_reg_c. cbn [grow rg_free]. rewrite length_app, newfree_length by (pose proof f_NC; lia). lia. }
        set (SP := fun A1 m1 md1 b0 i more scr0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n =>
                 step_pdm_ok rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Ag (munrestrict (hidc HS) Mk vpF) md' p n0 stkobj lo hi T (Z_to_bv 64 n0) (Z_to_bv 64 (p + -16))
                      A1 m1 md1 b0 i more scr0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n CLO LOSA SAHI HI47 SPA0 VBg).
    set (SS := fun A1 m1 md1 b0 i more scr0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s n =>
                 step_sec_ok rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Ag (munrestrict (hidc HS) Mk vpF) md' p n0 stkobj lo hi T (Z_to_bv 64 n0) (Z_to_bv 64 (p + -16))
                      A1 m1 md1 b0 i more scr0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s n CLO LOSA SAHI HI47 SPA0 VBg).
    set (SBd := fun A1 m1 md1 b0 more scr0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' =>
                 step_bdm_ok rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Ag (munrestrict (hidc HS) Mk vpF) md' p n0 stkobj lo hi T (Z_to_bv 64 n0) (Z_to_bv 64 (p + -16))
                      A1 m1 md1 b0 more scr0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' CLO LOSA SAHI HI47 SPA0 VBg).
    refine (dealloc_new0RX rac spd gp rac rac rac s0 s1 rac rac rac rac s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rac rac rac rac F fc _ md' Ag p n0 stkobj lo hi key T AIg24 MIg HLg IATg CLO LOSA SAHI HI47 SPA0 RAC2 STg SMHg SOLO SOHI STOg TRWg KEYUg KRg NQ KKg VBg SP SS SBd ms0 _ tk QTE eq_refl EMP NF1g TKC).
    (* [comment removed for export] *)
    intros tk' b1 fr fd ks na' statv bj0 bj1 bj2 bj3 fr24 gf gl gn gqb kb b kw nf Efr24 Egf Egl Egn Egqb Ekb Eb Ekw Enf
           HDR B1R TST FRR FDR Afap KSMW NFR BLO BHI BFA Abt Abp Abn Abf TPRE TOK TAP QMR QMM TAPR THRA LKS CSB CRI QC PC24 STA MXc NFCc NALc FARRc BC _ KC.
    rewrite VIEWg in *. change (a_pl Ag) with (a_pl A) in *. change (a_sb Ag) with sb in *. change (a_ri Ag) with ri in *. change (a_depot Ag) with (a_depot A) in *.
    (* [comment removed for export] *)
    (first [ pose proof ((cy_fcells _ _ _ _ _ _ _ v5 CY5 LErefl)) as dR_44; dex6 dR_44 as b1r frr fdr nxr bszr statvr; dand11 dR_44 as (B1Rr & B1Mr & FRRr & FDRr) HDRe TSTe TST5 HDR5 CTX5 SHD5 DR5 QC5 LBC5 STA5 | pose proof ((cy_fcells _ _ _ _ _ _ _ v5 CY5 LErefl)) as dR_44; dand17 dR_44 as b1r frr fdr nxr bszr statvr (B1Rr & B1Mr & FRRr & FDRr) HDRe TSTe TST5 HDR5 CTX5 SHD5 DR5 QC5 LBC5 STA5 | destruct (cy_fcells _ _ _ _ _ _ _ v5 CY5 LErefl) as (b1r & frr & fdr & nxr & bszr & statvr & (B1Rr & B1Mr & FRRr & FDRr) & HDRe & TSTe & TST5 & HDR5 & CTX5 & SHD5 & DR5 & QC5 & LBC5 & STA5) ]).
    assert (EB1 : b1r = b1).
    { pose proof (vp_entry_rw _ _ HDRe ltac:(apply (fk_Wq_chunk rac spd m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT); pose proof PLIN as ((_ & _ & P3 & _) & _); cbn; lia)) as X.
      exact (rw_C1_snd_inj vpF _ _ _ _ _ _ B1Rr B1R X HDR). }
    assert (EFR : frr = fr /\ fdr = fd).
    { pose proof (vp_entry_rw _ _ TSTe ltac:(apply (fk_Wq_thr rac spd m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT); cbn; lia)) as X.
      exact (rw_C8x2_inj vpF _ _ _ _ _ FRRr FDRr FRR FDR X TST). }
    destruct EFR as [EFR1 EFR2]. subst b1r frr fdr.
    (* [comment removed for export] *)
    (first [ dand9 end_place as LO SPA SPH (PAL & PLO & PNB & NR & R8) (DN0 & DF0 & STOR & KL) (SEP_pt & SEP_n0t & SEP_f0t) ((SBLO & SBHI & SBAL) & (RILO & RIHI & RIAL & RIE)) (SEP_tr & SEP_ts & SEP_rs & SEP_rp & SEP_rn & SEP_rf) _ | destruct end_place as (LO & SPA & SPH & (PAL & PLO & PNB & NR & R8) & (DN0 & DF0 & STOR & KL) & (SEP_pt & SEP_n0t & SEP_f0t) & ((SBLO & SBHI & SBAL) & (RILO & RIHI & RIAL & RIE)) & (SEP_tr & SEP_ts & SEP_rs & SEP_rp & SEP_rn & SEP_rf) & _) ]).
    pose proof (f24_geom Ag _ md' AIg24 NF1g) as GB. cbv zeta in GB. change (a_sb Ag) with sb in GB. rewrite <- Efr24, <- Ekb, <- Eb in GB. (first [ dand3 GB as BE KWR _ | destruct GB as (BE & KWR & _) ]).
    assert (KWV : bv_unsigned kw = kb * 512) by (rewrite Ekw; apply unsigned_lit; clear - KWR; lia).
    assert (BE' : sb + 24 * 2^32 + 16 * bv_unsigned kw = b) by (rewrite KWV; symmetry; exact BE).
    assert (DJR : forall a l, (a + l <= ri \/ ri + 4096 <= a) -> disjoint_from [(R, R + 8)] a l) by (intros a l Hal; cbn [disjoint_from]; split; [lia| exact I]).
    assert (Abr : apart b 8192 ri 4096) by (unfold apart; clear - BFA RIE; unfold free_array_of, kSpaceSize in *; lia).
    assert (DJbW : disjoint_from Wfo b 32).
    { (first [ pose proof (PLIN) as dR_47; dand4 dR_47 as (_ & _ & P3 & _) _ (S1 & S2 & S3) _ | pose proof PLIN as ((_ & _ & P3 & _) & _ & (S1 & S2 & S3) & _) ]). unfold fk_Wfo, fpop_Wfo. cbn [disjoint_from]. unfold apart, AMallocA.apart, kDepotNodesBlock, kStackStoreBlockBytes, kHighMemBeg in *.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I;
        first [ solve [clear - Abp P3; lia] | solve [clear - Abt; lia] | solve [clear - BLO; lia] | solve [clear - Abn; lia] | solve [clear - Abf; lia] | solve [clear - BLO S2; lia] ]. }
    (* [comment removed for export] *)
    unfold apart, AMallocA.apart in SEP_tr.
    pose proof (vp5_rw _ _ PC24 ltac:(apply Wfo_thr; cbn; lia) ltac:(apply DJR; cbn; lia)) as PC5.
    pose proof (vp5_rw _ _ STA ltac:(apply Wfo_thr; cbn; lia) ltac:(apply DJR; cbn; lia)) as STA5'.
    pose proof (vp5_rw _ _ QC ltac:(apply Wfo_thr; cbn; lia) ltac:(apply DJR; cbn; lia)) as QC5'.
    pose proof (vp5_rw _ _ BC ltac:(exact DJbW) ltac:(apply DJR; unfold apart in Abr; cbn; lia)) as BC5.
    pose proof (vp5_rw _ _ NFCc ltac:(apply Wfo_ri; cbn; lia) ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I])) as NFC5.
    pose proof (vp5_rw _ _ NALc ltac:(apply Wfo_ri; cbn; lia) ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I])) as NAL5.
    pose proof (vp5_img _ _ CSB ltac:(lia) ltac:(cbn; lia)) as CSB5.
    assert (FARR5 : u32arr rsegs v5 (free_array_of sb 24 + 4 * (nf - 1)) [kw]).
    { lin_open. apply (vp5_u32 _ _ FARRc).
      - apply Wfo_reg; cbn [length]; unfold free_array_of, kFreeArrayOffset, region_beg, kRegionSize in *; lia.
      - apply DJR. cbn [length]. unfold free_array_of, kSpaceSize in *. lia. }
    pose proof CY5 as (_ & _ & _ & PFR5 & EF5 & RF5 & GF5 & MX5 & _).
    pose proof (proj1 (proj2 GPK)) as ST5.
    (* [comment removed for export] *)
    eapply (srz_evt_restrict rsegs HS (hull_segsR Ag) pa_wxR _ (pa_eager Ag) _ _ md' T HI5 HHg).
    { rewrite restrict_MS. change (mrestrict (hidc HS) (munrestrict (hidc HS) Mk v5)) with (aview_of HS (munrestrict (hidc HS) Mk v5)). rewrite VIEW5.
      pose proof (free_cpop_tail0 rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v lo p n0 b1 pa_tsd ctx thr r8 n0d f0d fr fd stkobj (a_depot A) key
                    LO SPA SPH PAL PLO PNB NR R8 (hit_TC A m md AI) DN0 DF0 STOR KL SEP_pt SEP_n0t SEP_f0t sb ri SBLO SBHI SBAL RILO RIHI RIAL
                    ltac:(exact SEP_tr) SEP_ts SEP_rs SEP_rp SEP_rn SEP_rf
                    a0g tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 scr junk0 pad statv na' kw bj0 bj1 bj2 bj3 nf 0 0 0 ks v5) as EV.
      cbv zeta in EV. rewrite BE' in EV.
      specialize (EV THRA LKS NFR KSMW BLO BHI BFA Abt Abp Abn Abf Abr MI5 ST5 PFR5 EF5 RF5 GF5 TST5 HDR5 CTX5 SHD5 DR5 CSB5 MX5 NFC5 NAL5 FARR5 PC5 STA5' BC5 QC5').
      replace (ret_pc (wz gfa_popret)) with (wz gfa_popret : word) in EV by (symmetry; apply ret_pc_even; [unfold gfa_popret; lia| reflexivity]).
      change (Z.shiftr 2 1) with kk in EV.
      eapply evt_cut; [exact EV|]. clear EV.
      intros ms7 PO.
      assert (FCog : free_consts vpF) by (pose proof (free_FCo Ag _ md' AIg24) as X; rewrite VIEWg in X; exact X).
      assert (TCg : thread_cells vpF tp pa_tsd ctx thr) by (pose proof (hit_TC Ag _ md' AIg24) as X; rewrite VIEWg in X; exact X).
      assert (LO704 : alloc_ceiling <= lo /\ lo <= usp - 704) by (clear - LO; lia).
      pose proof BLO as BLO'. pose proof BHI as BHI'. pose proof Abt as Abt'. rewrite <- BE' in BLO', BHI', Abt'.
      apply (free_chitR_new0F_tl rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc vpF lo p n0 b1 pa_tsd ctx thr r8 n0d f0d fr fd stkobj (a_depot A) key
               LO704 SPH PAL PLO PNB NR R8 FCog TCg DN0 DF0 STOR KL SEP_pt SEP_n0t SEP_f0t sb ri nf kw na' SBLO SBHI RILO RIHI SEP_tr SEP_ts NFR BLO' BHI' Abt'
               tk' gn gf gl gqb (Z_to_bv 64 0) 0 ks statv bj0 bj1 bj2 bj3 kQuarantineMinSize ms7).
      all: rewrite ?BE'.
      all: try first [ exact TPRE | exact TOK | exact TAP | exact QMR | exact QMM | exact TAPR | exact THRA | exact LKS | exact CSB | exact CRI | exact QC | exact PC24 | exact STA | exact MXc | exact NFCc | exact NALc | exact FARRc | exact BC | lia ].
      (* [comment removed for export] *)
      unfold free_cenq_new0F_post in PO. cbv zeta in PO. rewrite ?BE' in PO.
      (first [ dex17 PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7; dand19 PO as -> MUc WMc MI7 ST7 PFR7 TST7 HDR7 CTX7 SHD7 DR7 QC7 PC7 STA7 B7 MX7 NFC7 NAL7 FARR7 | dand36 PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7 -> MUc WMc MI7 ST7 PFR7 TST7 HDR7 CTX7 SHD7 DR7 QC7 PC7 STA7 B7 MX7 NFC7 NAL7 FARR7 | destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & statv' & m7 & -> & MUc & WMc & MI7 & ST7 & PFR7 & TST7 & HDR7 & CTX7 & SHD7 & DR7 & QC7 & PC7 & STA7 & B7 & MX7 & NFC7 & NAL7 & FARR7) ]).
      unfold free_chead_new0F_post. cbv zeta. rewrite ?BE'.
      first [ hotw_ex17 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7 | exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', statv', m7 ]. split; [reflexivity|].
      split.
      { intros x Hx. unfold free_chit_new0F_W, free_cprefix_W in Hx. cbn [app outside] in Hx.
        (first [ dand16 Hx as O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 O13 O14 O15 _ | destruct Hx as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15 & _) ]).
        rewrite (MUc x); [| unfold free_ccore_new0F_W; cbn [outside]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; first [assumption | lia]].
        rewrite AGRw by lia. unfold vh. symmetry. apply mhyb_out. apply in_fpb_false. unfold fk_Wfo, fpop_Wfo. cbn [outside].
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; assumption. }
      split; [exact (wmono_trans _ _ _ _ WMp5 WMc)|].
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }

    intros msr' md'' HQ HI'' SB'' CL''. change (ms_mem ms0) with (munrestrict (hidc HS) Mk v5).
    rewrite (unrestrict_ext (hidc HS) (munrestrict (hidc HS) Mk v5) (munrestrict (hidc HS) Mk vpF) msr') by (intros a Ha; unfold munrestrict; rewrite Ha; reflexivity).
    exact (KC msr' md'' HQ HI'' SB'' CL'').
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="MI5 WM5 MU5 LErefl CY5 GPK CL5 SB5 HI5 PM MSH na ksc scr pad junk0 mdk KK CEILw CEIL SAE PREF MIv CE N7R CR W0 AI SHAPE SHORT EMP NQ HL PRE key hi lo stkobj p md m s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac"] Theorem end_newfullR : forall tk : ftail,
    a_qthread A <> [] -> Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) = kQuarantineBatchCount ->
    match tk with
    | TN => False
    | T0 => kQuarantineCacheSize < q_bytes (a_qthread A) + n0 + kQuarantineBatchBytes /\ a_qglobal A = [] /\ kQuarantineMaxSize < q_bytes (a_qthread A) + n0 + kQuarantineBatchBytes
    | TA => kQuarantineCacheSize < q_bytes (a_qthread A) + n0 + kQuarantineBatchBytes /\ a_qglobal A <> [] /\
            kQuarantineMaxSize < q_bytes (a_qglobal A) + (q_bytes (a_qthread A) + n0 + kQuarantineBatchBytes)
    end ->
    srealizes rsegs (mkCfg ms0 md') T.
  Proof.
    intros tk QNE FULL TKC.
    destruct PREF as (CLO & LOSA & SAHI & HI47 & SPA0 & RAC2 & ST & SM & SOLO & SOHI).
    (first [ pose proof ((ar_nc A 24 W0 CR EMP SHORT)) as dR_50; dand5 dR_50 as _ _ _ NK _ | pose proof (ar_nc A 24 W0 CR EMP SHORT) as (_ & _ & _ & NK & _) ]). (first [ pose proof ((ar_k A 24 CR)) as dR_51; dand3 dR_51 as _ KR1 _ | pose proof (ar_k A 24 CR) as (_ & KR1 & _) ]).
    assert (NF1g : 1 <= Z.of_nat (length (rg_free (a_reg Ag kQuarantineBatchClass)))).
    { unfold kQuarantineBatchClass. rewrite popg_reg_c. cbn [grow rg_free]. rewrite length_app, newfree_length by (pose proof f_NC; lia). lia. }
        set (SP := fun A1 m1 md1 b0 i more scr0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n =>
                 step_pdm_ok rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Ag (munrestrict (hidc HS) Mk vpF) md' p n0 stkobj lo hi T (Z_to_bv 64 n0) (Z_to_bv 64 (p + -16))
                      A1 m1 md1 b0 i more scr0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n CLO LOSA SAHI HI47 SPA0 VBg).
    set (SS := fun A1 m1 md1 b0 i more scr0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s n =>
                 step_sec_ok rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Ag (munrestrict (hidc HS) Mk vpF) md' p n0 stkobj lo hi T (Z_to_bv 64 n0) (Z_to_bv 64 (p + -16))
                      A1 m1 md1 b0 i more scr0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s n CLO LOSA SAHI HI47 SPA0 VBg).
    set (SBd := fun A1 m1 md1 b0 more scr0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' =>
                 step_bdm_ok rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Ag (munrestrict (hidc HS) Mk vpF) md' p n0 stkobj lo hi T (Z_to_bv 64 n0) (Z_to_bv 64 (p + -16))
                      A1 m1 md1 b0 more scr0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' CLO LOSA SAHI HI47 SPA0 VBg).
    refine (dealloc_newfullRX rac spd gp rac rac rac s0 s1 rac rac rac rac s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rac rac rac rac F fc _ md' Ag p n0 stkobj lo hi key T AIg24 MIg HLg IATg CLO LOSA SAHI HI47 SPA0 RAC2 STg SMHg SOLO SOHI STOg TRWg KEYUg KRg NQ KKg VBg SP SS SBd ms0 _ tk QNE FULL eq_refl EMP NF1g TKC).
    (* [comment removed for export] *)
    intros tk' b1 fr fd ks na' statv bj0 bj1 bj2 bj3 fr24 gf gl gn gqb kb b kw nf qt bl lb Efr24 Egf Egl Egn Egqb Ekb Eb Ekw Enf Eqt Ebl Elb
           HDR B1R TST FRR FDR Afap KSMW NFR BLO BHI BFA Abt Abp Abn Abf TPRE TOK TAP QMR QMM TAPR NB0 FBR QB0 THRA LKS LBL LBH' LBFA Alt Alp Alc Aln Alf Alr Abl CSB CRI QC LB PC24 STA MXc NFCc NALc FARRc BC _ KC.
    assert (NBR40 : 0 <= Z.of_nat (length qt) < 2^40) by (rewrite Eqt; exact qt_len_range).
    assert (NBR : 0 <= Z.of_nat (length qt) < 2^63) by (clear - NBR40; lia).
    rewrite VIEWg in *. change (a_pl Ag) with (a_pl A) in *. change (a_sb Ag) with sb in *. change (a_ri Ag) with ri in *. change (a_depot Ag) with (a_depot A) in *.
    (* [comment removed for export] *)
    (first [ pose proof ((cy_fcells _ _ _ _ _ _ _ v5 CY5 LErefl)) as dR_52; dex6 dR_52 as b1r frr fdr nxr bszr statvr; dand11 dR_52 as (B1Rr & B1Mr & FRRr & FDRr) HDRe TSTe TST5 HDR5 CTX5 SHD5 DR5 QC5 LBC5 STA5 | pose proof ((cy_fcells _ _ _ _ _ _ _ v5 CY5 LErefl)) as dR_52; dand17 dR_52 as b1r frr fdr nxr bszr statvr (B1Rr & B1Mr & FRRr & FDRr) HDRe TSTe TST5 HDR5 CTX5 SHD5 DR5 QC5 LBC5 STA5 | destruct (cy_fcells _ _ _ _ _ _ _ v5 CY5 LErefl) as (b1r & frr & fdr & nxr & bszr & statvr & (B1Rr & B1Mr & FRRr & FDRr) & HDRe & TSTe & TST5 & HDR5 & CTX5 & SHD5 & DR5 & QC5 & LBC5 & STA5) ]).
    assert (EB1 : b1r = b1).
    { pose proof (vp_entry_rw _ _ HDRe ltac:(apply (fk_Wq_chunk rac spd m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT); pose proof PLIN as ((_ & _ & P3 & _) & _); cbn; lia)) as X.
      exact (rw_C1_snd_inj vpF _ _ _ _ _ _ B1Rr B1R X HDR). }
    assert (EFR : frr = fr /\ fdr = fd).
    { pose proof (vp_entry_rw _ _ TSTe ltac:(apply (fk_Wq_thr rac spd m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT); cbn; lia)) as X.
      exact (rw_C8x2_inj vpF _ _ _ _ _ FRRr FDRr FRR FDR X TST). }
    destruct EFR as [EFR1 EFR2]. subst b1r frr fdr.
    (* [comment removed for export] *)
    (first [ dand9 end_place as LO SPA SPH (PAL & PLO & PNB & NR & R8) (DN0 & DF0 & STOR & KL) (SEP_pt & SEP_n0t & SEP_f0t) ((SBLO & SBHI & SBAL) & (RILO & RIHI & RIAL & RIE)) (SEP_tr & SEP_ts & SEP_rs & SEP_rp & SEP_rn & SEP_rf) _ | destruct end_place as (LO & SPA & SPH & (PAL & PLO & PNB & NR & R8) & (DN0 & DF0 & STOR & KL) & (SEP_pt & SEP_n0t & SEP_f0t) & ((SBLO & SBHI & SBAL) & (RILO & RIHI & RIAL & RIE)) & (SEP_tr & SEP_ts & SEP_rs & SEP_rp & SEP_rn & SEP_rf) & _) ]).
    pose proof (f24_geom Ag _ md' AIg24 NF1g) as GB. cbv zeta in GB. change (a_sb Ag) with sb in GB. rewrite <- Efr24, <- Ekb, <- Eb in GB. (first [ dand3 GB as BE KWR _ | destruct GB as (BE & KWR & _) ]).
    assert (KWV : bv_unsigned kw = kb * 512) by (rewrite Ekw; apply unsigned_lit; clear - KWR; lia).
    assert (BE' : sb + 24 * 2^32 + 16 * bv_unsigned kw = b) by (rewrite KWV; symmetry; exact BE).
    assert (DJR : forall a l, (a + l <= ri \/ ri + 4096 <= a) -> disjoint_from [(R, R + 8)] a l) by (intros a l Hal; cbn [disjoint_from]; split; [lia| exact I]).
    assert (Abr : apart b 8192 ri 4096) by (unfold apart; clear - BFA RIE; unfold free_array_of, kSpaceSize in *; lia).
    assert (DJbW : disjoint_from Wfo b 32).
    { (first [ pose proof (PLIN) as dR_55; dand4 dR_55 as (_ & _ & P3 & _) _ (S1 & S2 & S3) _ | pose proof PLIN as ((_ & _ & P3 & _) & _ & (S1 & S2 & S3) & _) ]). unfold fk_Wfo, fpop_Wfo. cbn [disjoint_from]. unfold apart, AMallocA.apart, kDepotNodesBlock, kStackStoreBlockBytes, kHighMemBeg in *.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I;
        first [ solve [clear - Abp P3; lia] | solve [clear - Abt; lia] | solve [clear - BLO; lia] | solve [clear - Abn; lia] | solve [clear - Abf; lia] | solve [clear - BLO S2; lia] ]. }
    (* [comment removed for export] *)
    unfold apart, AMallocA.apart in SEP_tr.
    pose proof (vp5_rw _ _ PC24 ltac:(apply Wfo_thr; cbn; lia) ltac:(apply DJR; cbn; lia)) as PC5.
    pose proof (vp5_rw _ _ STA ltac:(apply Wfo_thr; cbn; lia) ltac:(apply DJR; cbn; lia)) as STA5'.
    pose proof (vp5_rw _ _ QC ltac:(apply Wfo_thr; cbn; lia) ltac:(apply DJR; cbn; lia)) as QC5'.
    assert (DJlW : disjoint_from Wfo lb 24).
    { (first [ pose proof (PLIN) as dR_56; dand4 dR_56 as (_ & _ & P3 & _) _ (S1 & S2 & S3) _ | pose proof PLIN as ((_ & _ & P3 & _) & _ & (S1 & S2 & S3) & _) ]). unfold fk_Wfo, fpop_Wfo. cbn [disjoint_from]. unfold apart, AMallocA.apart, kDepotNodesBlock, kStackStoreBlockBytes, kHighMemBeg in *.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I;
        first [ solve [clear - Alp P3; lia] | solve [clear - Alt; lia] | solve [clear - LBL; lia] | solve [clear - Aln; lia] | solve [clear - Alf; lia] | solve [clear - LBL S2; lia] ]. }
    pose proof (vp5_rw _ _ LB ltac:(exact DJlW) ltac:(apply DJR; unfold apart in Alr; cbn; lia)) as LB5.
    pose proof (vp5_rw _ _ BC ltac:(exact DJbW) ltac:(apply DJR; unfold apart in Abr; cbn; lia)) as BC5.
    pose proof (vp5_rw _ _ NFCc ltac:(apply Wfo_ri; cbn; lia) ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I])) as NFC5.
    pose proof (vp5_rw _ _ NALc ltac:(apply Wfo_ri; cbn; lia) ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I])) as NAL5.
    pose proof (vp5_img _ _ CSB ltac:(lia) ltac:(cbn; lia)) as CSB5.
    assert (FARR5 : u32arr rsegs v5 (free_array_of sb 24 + 4 * (nf - 1)) [kw]).
    { lin_open. apply (vp5_u32 _ _ FARRc).
      - apply Wfo_reg; cbn [length]; unfold free_array_of, kFreeArrayOffset, region_beg, kRegionSize in *; lia.
      - apply DJR. cbn [length]. unfold free_array_of, kSpaceSize in *. lia. }
    pose proof CY5 as (_ & _ & _ & PFR5 & EF5 & RF5 & GF5 & MX5 & _).
    pose proof (proj1 (proj2 GPK)) as ST5.
    (* [comment removed for export] *)
    eapply (srz_evt_restrict rsegs HS (hull_segsR Ag) pa_wxR _ (pa_eager Ag) _ _ md' T HI5 HHg).
    { rewrite restrict_MS. change (mrestrict (hidc HS) (munrestrict (hidc HS) Mk v5)) with (aview_of HS (munrestrict (hidc HS) Mk v5)). rewrite VIEW5.
      pose proof (free_cpop_tailF rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v lo p n0 b1 pa_tsd ctx thr r8 n0d f0d fr fd stkobj (a_depot A) key
                    LO SPA SPH PAL PLO PNB NR R8 (hit_TC A m md AI) DN0 DF0 STOR KL SEP_pt SEP_n0t SEP_f0t sb ri SBLO SBHI SBAL RILO RIHI RIAL
                    ltac:(exact SEP_tr) SEP_ts SEP_rs SEP_rp SEP_rn SEP_rf
                    a0g tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 scr junk0 pad statv na' kw bj0 bj1 bj2 bj3 nf (qc_first Ag qt) lb (q_bytes qt) ks v5) as EV.
      cbv zeta in EV. rewrite BE' in EV.
      specialize (EV THRA LKS NFR KSMW BLO BHI BFA Abt Abp Abn Abf Abr MI5 ST5 PFR5 EF5 RF5 GF5 TST5 HDR5 CTX5 SHD5 DR5 CSB5 MX5 NFC5 NAL5 FARR5 PC5 STA5' BC5
                     (Z.of_nat (length qt)) 0 (batch_bytes bl) NB0 NBR LBL LBH' LBFA Alt Alp Alc Aln Alf Alr Abl QC5' LB5).
      replace (ret_pc (wz gfa_popret)) with (wz gfa_popret : word) in EV by (symmetry; apply ret_pc_even; [unfold gfa_popret; lia| reflexivity]).
      change (Z.shiftr 2 1) with kk in EV.
      eapply evt_cut; [exact EV|]. clear EV.
      intros ms7 PO.
      assert (FCog : free_consts vpF) by (pose proof (free_FCo Ag _ md' AIg24) as X; rewrite VIEWg in X; exact X).
      assert (TCg : thread_cells vpF tp pa_tsd ctx thr) by (pose proof (hit_TC Ag _ md' AIg24) as X; rewrite VIEWg in X; exact X).
      assert (LO704 : alloc_ceiling <= lo /\ lo <= usp - 704) by (clear - LO; lia).
      pose proof BLO as BLO'. pose proof BHI as BHI'. pose proof Abt as Abt'. rewrite <- BE' in BLO', BHI', Abt'.
      apply (free_chitR_newfullF_tl rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc vpF lo p n0 b1 pa_tsd ctx thr r8 n0d f0d fr fd stkobj (a_depot A) key
               LO704 SPH PAL PLO PNB NR R8 FCog TCg DN0 DF0 STOR KL SEP_pt SEP_n0t SEP_f0t sb ri nf kw na' SBLO SBHI RILO RIHI SEP_tr SEP_ts NFR BLO' BHI' Abt'
               tk' gn gf gl gqb (Z_to_bv 64 0) (Z.of_nat (length qt)) (qc_first Ag qt) lb (q_bytes qt) 0 (batch_bytes bl) ks statv bj0 bj1 bj2 bj3 kQuarantineMinSize ms7).
      all: rewrite ?BE'.
      all: try first [ exact TPRE | exact TOK | exact TAP | exact QMR | exact QMM | exact TAPR | exact NB0 | exact NBR40 | exact NBR | exact FBR | exact QB0 | exact THRA | exact LKS | exact LBL | exact LBH' | exact LBFA | exact Alt | exact Alp | exact Alc | exact Aln | exact Alf | exact Alr | exact Abl | exact LB | exact CSB | exact CRI | exact QC | exact PC24 | exact STA | exact MXc | exact NFCc | exact NALc | exact FARRc | exact BC | lia ].
      (* [comment removed for export] *)
      unfold free_cenq_newfullF_post in PO. cbv zeta in PO. rewrite ?BE' in PO.
      (first [ dex17 PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7; dand20 PO as -> MUc WMc MI7 ST7 PFR7 TST7 HDR7 CTX7 SHD7 DR7 QC7 LB7 PC7 STA7 B7 MX7 NFC7 NAL7 FARR7 | dand36 PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7 -> MUc WMc MI7 ST7 PFR7 TST7 HDR7 CTX7 SHD7 DR7 QC7 LB7 PC7 STA7 B7 MX7 NFC7 dR_PO_t0; destruct dR_PO_t0 as [NAL7 FARR7] | destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & statv' & m7 & -> & MUc & WMc & MI7 & ST7 & PFR7 & TST7 & HDR7 & CTX7 & SHD7 & DR7 & QC7 & LB7 & PC7 & STA7 & B7 & MX7 & NFC7 & NAL7 & FARR7) ]).
      unfold free_chead_newfullF_post. cbv zeta. rewrite ?BE'.
      first [ hotw_ex17 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m7 | exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', statv', m7 ]. split; [reflexivity|].
      split.
      { intros x Hx. unfold free_chit_newfullF_W, free_cprefix_W in Hx. cbn [app outside] in Hx.
        repeat match type of Hx with _ /\ _ => let O := fresh "O" in destruct Hx as [O Hx] end.
        rewrite (MUc x); [| unfold free_ccore_newfullF_W; cbn [outside]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; first [assumption | lia]].
        rewrite AGRw by lia. unfold vh. symmetry. apply mhyb_out. apply in_fpb_false. unfold fk_Wfo, fpop_Wfo. cbn [outside].
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try exact I; assumption. }
      split; [exact (wmono_trans _ _ _ _ WMp5 WMc)|].
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }

    intros msr' md'' HQ HI'' SB'' CL''. change (ms_mem ms0) with (munrestrict (hidc HS) Mk v5).
    rewrite (unrestrict_ext (hidc HS) (munrestrict (hidc HS) Mk v5) (munrestrict (hidc HS) Mk vpF) msr') by (intros a Ha; unfold munrestrict; rewrite Ha; reflexivity).
    exact (KC msr' md'' HQ HI'' SB'' CL'').
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="MI5 WM5 MU5 LErefl CY5 GPK CL5 SB5 HI5 PM MSH na ksc scr pad junk0 mdk KK CEILw CEIL SAE PREF MIv CE N7R CR W0 AI SHAPE SHORT EMP NQ HL PRE key hi lo stkobj n0 p md m s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac"] Theorem kend_all : srealizes rsegs (mkCfg ms0 md') T.
  Proof.
    assert (TKE : forall qb', ~ ctail_covered A qb' ->
              (a_qglobal A = [] /\ kQuarantineCacheSize < qb' /\ kQuarantineMaxSize < qb') \/
              (a_qglobal A <> [] /\ kQuarantineCacheSize < qb' /\ kQuarantineMaxSize < q_bytes (a_qglobal A) + qb')).
    { intros qb' NC. unfold ctail_covered in NC.
      destruct (a_qglobal A) as [|g r] eqn:EG.
      - left. split; [reflexivity|]. cbn in NC. clear - NC. lia.
      - right. split; [discriminate|]. rewrite <- EG in NC |- *. clear - NC. lia. }
    destruct SHAPE as [QTE|[QNE FULL]].
    - destruct (classic (ctail_covered A (n0 + kQuarantineBatchBytes))) as [TC|NTC].
      + apply ctail_pick in TC. destruct TC as [C|[C|C]]; [exact (end_new0G TN QTE C)| exact (end_new0G T0 QTE C)| exact (end_new0G TA QTE C)].
      + destruct (TKE _ NTC) as [(QGE & C1 & C2)|(QGN & C1 & C2)]; [exact (end_new0R T0 QTE (conj C1 (conj QGE C2)))| exact (end_new0R TA QTE (conj C1 (conj QGN C2)))].
    - destruct (classic (ctail_covered A (q_bytes (a_qthread A) + n0 + kQuarantineBatchBytes))) as [TC|NTC].
      + apply ctail_pick in TC. destruct TC as [C|[C|C]]; [exact (end_newfullG TN QNE FULL C)| exact (end_newfullG T0 QNE FULL C)| exact (end_newfullG TA QNE FULL C)].
      + destruct (TKE _ NTC) as [(QGE & C1 & C2)|(QGN & C1 & C2)]; [exact (end_newfullR T0 QNE FULL (conj C1 (conj QGE C2)))| exact (end_newfullR TA QNE FULL (conj C1 (conj QGN C2)))].
  Qed.
End FEnd.
