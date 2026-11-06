(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AU_kit AU_iface AHarnessU_iface AU_parts_iface
     AU_wild_iface AInstanceM AInstanceW AInstanceW2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Set Keyed Unification.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Notation AI := AI_W.

(* [comment removed for export] *)
Lemma implMA_afree_call_wild : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A n lo : Z) (tr : list Z),
  AHEAP AI L RNG (aps_m s) LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  bv_unsigned sp + 16 < al_top L ->
  uchain m (al_top L) AFREE_PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr -> (length tr <= 28)%nat ->
  dk (aps_m s) < DWMAX ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (al_top L - lo) ->
  aps_ok L s ->
  implMA RNG (afree_M p) s
    (fun _ s' RNG' ms' => aps_rest s' = aps_rest s
       /\ afree_post (aci AI) (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (aps_m s) LB p lo m (aps_m s') RNG' ms')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. intros AH HIN MI ST BOT LOS TP A0 TOP UC LTR DK NS8 RA4 RAPC SP16 RSTK [ROK AT].
  assert (UW : aunwW m L RNG lo AFREE_PC sp s0 ra tr) by (split; [exact TOP|]; split; [exact UC|]; split; [exact LTR| exact RSTK]).
  assert (RLO : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| destruct ST as [? _]; lia]).
  assert (AHW : AHEAP_W L RNG (aps_m s) LB m) by exact AH.
  apply implMA_afree; [exact AT|]. eapply implF_epost_mono; [eapply AHW_free_wild; eauto|].
  cbv beta. intros st' RNG' ms' PO. split; [reflexivity| exact PO].
Qed.

(* [comment removed for export] *)
Theorem opdelete_arr_wild_proofA : opdelete_arr_wild_stmtA AI.
Proof.
  unfold opdelete_arr_wild_stmtA, opdelete_stmtA_wild_at; intros until tr; intros AH HIN MI ST BOT LOS TOP TP A0 UC DK NS8 RA4 RAPC LTR SP16 RSTK ROK;
    unfold HarnessP.opdelete; apply implMA_from_evtF; unfold AOPDEL_ARR.
  zstep. zstep. apply evtF_done. eapply implMA_afree_call_wild; eauto.
Qed.
End CANSEC1.
