(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BReach BazyRestrict BazyLedger BazySR BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocBudget BllocRep BllocRepX BsDepotInv BG_MallocModel BG_Malloc2 BG_RepQ BG_WriteSet BG_RecycleDefs BG_RecyclePrim BG_RecycleSec.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Section RCStep.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (XC XB : list Z) (ch : chunk) (d : depot) (lo cb : Z).

  Hypothesis RQ : AREPQ s (ch_chunk_beg ch :: XC) XB m.
  Hypothesis CHIN : In ch (chunk_list (a_st s)).
  Hypothesis QUAR : ch_state ch = CQuarantine.
  Hypothesis INIT : as_cache_inited (a_st s) = true.
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 800 <= bv_unsigned sp.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis TP : bv_unsigned tp = ATP.
  Hypothesis PROOM : pusage (a_st s) + 303104 <= B_PRIM.
  Hypothesis CBR : bv_unsigned sp <= cb /\ cb + 8 <= 2^63.
  Hypothesis CBC : rw_cells asegs m cb [C8 (wz (a_cache s))].
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
                    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz cb) (wz (ch_chunk_beg ch)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x947ac) fc None m (seg_rom asegs).

  Theorem recycle_chunk_arepq :
    (forall msF' mo',
       rstep_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s d lo m mo XC XB XB
         (fun st' => forall stA, same_but_shadow stA (a_st s) ->
                       exists stA' ev, cb_recycle stA (ch_chunk_beg ch) = Some (stA', ev) /\ same_but_shadow stA' st') msF' mo' ->
       sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K. destruct (ch_primary ch) eqn:PRIM.
    - apply (recycle_prim_arepq ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF mo Q s XC XB ch d lo cb
               RQ CHIN PRIM QUAR INIT AX AMX DEP DPL DCOV MI LO ltac:(clear - HI; lia) SPT SPA ST TP PROOM CBR CBC OK VISE).
      intros msF' mo' P. apply K. exact P.
    - apply (recycle_sec_arepq ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF mo Q s XC XB ch d lo cb
               RQ CHIN PRIM QUAR INIT AX AMX DEP DPL DCOV MI LO HI SPA ST TP OK VISE).
      intros msF' mo' P. apply K. exact P.
  Qed.
End RCStep.

Theorem step_chunk_real : forall (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (Q : config -> Prop) (d' : depot) (lo : Z),
  forall (spD : word) (ra1 t0 t1 t2 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 t3 t4 t5 t6 s10x s11x : word)
      (m0 : mem) (msF : machine_state) (mo : Model) (sx : ast) (XC XB : list Z) (chx : chunk),
      AREPQ sx (ch_chunk_beg chx :: XC) XB m0 -> In chx (chunk_list (a_st sx)) -> ch_state chx = CQuarantine ->
      as_cache_inited (a_st sx) = true -> awin_vis sx m0 /\ flagsx_rep m0 -> AMODELX sx mo ->
      DEPOT asegs d' m0 -> depot_placed sx d' -> depot_cov d' mo -> mem_inv asegs m0 ->
      aceil <= lo -> lo + 800 <= bv_unsigned spD -> bv_unsigned spD + 16 <= 2^47 -> bv_unsigned spD mod 16 = 0 ->
      stk asegs m0 lo (bv_unsigned spD) -> bv_unsigned tp = ATP -> pusage (a_st sx) + 303104 <= B_PRIM ->
      bv_unsigned spD <= bv_unsigned spD + 8 /\ bv_unsigned spD + 8 + 8 <= 2^63 ->
      rw_cells asegs m0 (bv_unsigned spD + 8) [C8 (wz (a_cache sx))] ->
      lzok asegs (a_L sx) (a_S sx) (a_Zr sx) (mkCfg msF mo) ->
      restrict (a_L sx) (a_S sx) msF
        = MS (mkR ra1 spD gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned spD + 112)) (wz AINST) (wz (bv_unsigned spD + 8)) (wz (ch_chunk_beg chx)) a2 a3 a4 a5 a6 a7
                  x2 x3 x4 x5 x6 x7 x8 x9 s10x s11x t3 t4 t5 t6) F (Z_to_bv 64 0x947ac) fc None m0 (seg_rom asegs) ->
      (forall msF' mo',
         rstep_post ra1 spD gp tp (Z_to_bv 64 (bv_unsigned spD + 112)) (wz AINST) x2 x3 x4 x5 x6 x7 x8 x9 s10x s11x F fc sx d' lo m0 mo XC XB XB
           (fun st' => forall stA, same_but_shadow stA (a_st sx) ->
                         exists stA' ev, cb_recycle stA (ch_chunk_beg chx) = Some (stA', ev) /\ same_but_shadow stA' st') msF' mo' ->
         sreach asegs Q (mkCfg msF' mo')) ->
      sreach asegs Q (mkCfg msF mo).
Proof.
  intros gp tp F fc Q d' lo spD ra1 t0 t1 t2 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 t3 t4 t5 t6 s10x s11x m0 msF mo sx XC XB chx.
  intros RQ CHIN QUAR INIT AX AMX DEP DPL DCOV MI LO HI SPT SPA ST TP PROOM CBR CBC OK VISE K.
  exact (recycle_chunk_arepq ra1 spD gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned spD + 112)) (wz AINST) a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 s10x s11x t3 t4 t5 t6
           F fc m0 msF mo Q sx XC XB chx d' lo (bv_unsigned spD + 8)
           RQ CHIN QUAR INIT AX AMX DEP DPL DCOV MI LO HI SPT SPA ST TP PROOM CBR CBC OK VISE K).
Qed.
End HCW.
