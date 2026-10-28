(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame BCells BStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_SR LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_StateStmt LbB_HKit LbB_HStKit LbB_Bridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoKit3 LbB_WoSt LbB_WoSt2 LbB_WoMs LbB_WoCut LbB_WoZ.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoR6 LbB_WoT2 LbB_WoBP LbB_WoUR LbB_WoS4 LbB_WoVec LbB_WoUK LbB_WoUW.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ResvB LbB_PiStmt LbB_DStat.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoU.
  #[local] Set Default Proof Using "All".
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.

  Lemma wu_top : forall (Q : config -> Prop) (e : went H) ff fp (mo0 : Model),
    (forall msF mo s LB LBs XS m cP (r : Z)
        (x5 x6 x7 x12 x13 x14 x15 x16 x17 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
       as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
       as_AL H s >= as_AL H (w_s e) - po_cost (w_n e) -> 0 <= as_AL H s ->
       frm_zero fc -> wtl H e ff fp XS s LB LBs [] m cP -> wtst0 ff m Z24 Z24 Z24 ->
       lb_small LB + 700 <= RT_SMALL_MAX -> Z.of_nat (length LB) + 3 <= RT_CNT_MAX -> nlarge LB <= RT_LARGE_MAX ->
       - 2 ^ 31 <= r < 2 ^ 31 ->
       as_VIS H s msF = MS (mkR (Z_to_bv 64 WO_AN7_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7
                              (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 25)
                              x12 x13 x14 x15 x16 x17
                              (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 (ff + 3504))
                              (Z_to_bv 64 (ff + 3248)) (Z_to_bv 64 r) (Z_to_bv 64 (ff + 3272)) s10 s11 x28 x29 x30 x31)
                           F (Z_to_bv 64 RESV_OPND_ENTRY) fc None m (seg_rom asegs) ->
       as_SR H Q (mkCfg msF mo)) ->
    bp_kwcf H e ff fp Q mo0.
  Proof.
    intros Q e ff fp mo0 K.
    intros s LB LBs m mo msF R F fc XSc w r VIS RF FZ KR MP WP WI SL SH RC RG R24 RB WL (c & PE).
    pose proof (rt_bp_base H HHb) as HB.
    destruct RC as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
    assert (ESP : w_sp e = Z_to_bv 64 (wSP e)) by (unfold wSP; symmetry; apply Z_to_bv_bv_unsigned).
    rewrite (rfull_eq R RF) in VIS.
    rewrite R2, R3, R4, R8, R9, R19, R20, RG, R24, ESP in VIS. unfold wz in VIS.
    set (P := fun ms : machine_state => exists (m' : mem) (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      winv H e ff fp XSc s LB m' /\ bp_slots H e ff m' /\ bp_shad ff [19; 20; 21]%nat m' /\ wtst0 ff m' Z24 Z24 Z24
      /\ wmono asegs m m' /\ munch [(sh ff + 382, sh ff + 412); (wS1 e - AINTRIN_STACK, wS1 e); (ff + 3056, ff + 3296)] m m'
      /\ ms = MS (mkR (Z_to_bv 64 0xec200) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) y5 y6 y7
                      (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 25)
                      y12 y13 y14 y15 y16 y17
                      (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 (ff + 3504))
                      (Z_to_bv 64 (ff + 3248)) (Z_to_bv 64 r) (Z_to_bv 64 (ff + 3272)) (Z_to_bv 64 32) (PropExec.getr R 27)
                      y28 y29 y30 y31)
                 F (Z_to_bv 64 0xec4ac) fc None m' (seg_rom asegs)).
    eapply (ahh_evt_then H HB P Q s msF _ mo KR VIS).
    - eapply (wu_run H HHb e ff fp XSc s LB m P); [exact WP | exact WI | exact SL | exact SH |].
      intros m' y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HI' SL' SH' TS WM MU.
      apply evt_done. exists m', y5, y6, y7, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31.
      repeat (split; [assumption|]). reflexivity.
    - intros msF' mo' KR' MP' (m' & y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31
                               & HI' & SL' & SH' & TS & WM & MU & VIS').
      destruct (LbB_WoUW.wu_wtl H HHb e ff fp XSc s LB LBs m m' c w WP WL WI PE SL SH MU WM HI' SL' SH') as (WT & B1 & B2 & B3 & AL1 & AL2).
      exact (K msF' mo' s LB LBs XSc m' (pc_state c) r y5 y6 y7 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 32) (PropExec.getr R 27)
               y28 y29 y30 y31 F fc KR' (ah_mpres_trans H HB _ _ _ MP MP') AL1 AL2 FZ WT TS B1 B2 B3 RB VIS').
  Qed.
End WoU.
