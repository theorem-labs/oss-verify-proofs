(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AU_kit AU_iface AHarnessU_iface AU_parts_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Set Keyed Unification.

Section CANSEC1. Context {rc : runConstT}.
Section OpDelTop.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).

  Definition opdelete_dataA_at (entry : Z) : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A n lo : Z),
    AHEAP AI L RNG (aps_m s) LB m -> In (HB p A n) LB ->
    mem_inv asegs m ->
    stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
    tp = Z_to_bv 64 ATP ->
    a0 = Z_to_bv 64 A ->
    bv_unsigned s0 <= bv_unsigned sp ->                                  (* [comment removed for export] *)
    4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> bv_unsigned sp mod 16 = 0 ->
    In [AFREE_PC; bv_unsigned ra] (al_U L) -> In [AFREE_PC] (al_U L) ->    (* [comment removed for export] *)
    rng RNG lo (al_top L - lo) -> bv_unsigned sp < 2^47 -> rng RNG lo (bv_unsigned sp - lo) ->
    aps_ok L s ->
    implMA RNG (HarnessM.opdelete afree_M p) s
      (fun _ s' RNG' ms' => aps_rest s' = aps_rest s
         /\ afree_post CI (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (aps_m s) LB p lo m (aps_m s') RNG' ms')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition opdelete_dataA : Prop := opdelete_dataA_at AOPDEL_SZ /\ opdelete_dataA_at AOPDEL.

  (* [comment removed for export] *)
  Lemma implMA_afree_call_data : forall (L : alayout) (RNG : footprint)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : amem) (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A n lo : Z),
    AHEAP AI L RNG (aps_m s) LB m -> In (HB p A n) LB ->
    mem_inv asegs m ->
    stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
    tp = Z_to_bv 64 ATP ->
    a0 = Z_to_bv 64 A ->
    bv_unsigned s0 <= bv_unsigned sp ->
    4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> bv_unsigned sp mod 16 = 0 ->
    In [AFREE_PC; bv_unsigned ra] (al_U L) -> In [AFREE_PC] (al_U L) ->
    rng RNG lo (al_top L - lo) -> bv_unsigned sp < 2^47 -> rng RNG lo (bv_unsigned sp - lo) ->
    aps_ok L s ->
    implMA RNG (afree_M p) s
      (fun _ s' RNG' ms' => aps_rest s' = aps_rest s
         /\ afree_post (aci AI) (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (aps_m s) LB p lo m (aps_m s') RNG' ms')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros AH HIN MI ST BOT LOS TP A0 S0D RA4 RAPC SP16 HU2 HU1 RTOP SP47 RSP [ROK AT].
    assert (UW : aunw m L RNG lo AFREE_PC sp s0 ra []).
    { destruct (Z.lt_ge_cases (bv_unsigned sp + 16) (al_top L)) as [LT|GE].
      - left. split; [exact LT|]. split; [apply uchain_data; exact S0D|]. split; [cbn; lia|]. split; [exact HU2| exact RTOP].
      - right. split; [lia|]. split; [exact SP47| exact HU1]. }
    assert (NS8 : bv_unsigned s0 <> bv_unsigned sp + 8) by lia.
    apply implMA_afree; [exact AT|]. eapply implF_epost_mono; [eapply (AI_free AI); eauto|].
    cbv beta. intros st' RNG' ms' PO. split; [reflexivity| exact PO].
  Qed.

  (* [comment removed for export] *)
  Theorem opdelete_data_proofA : opdelete_dataA.
  Proof.
    split; unfold opdelete_dataA_at; intros until lo; intros AH HIN MI ST BOT LOS TP A0 S0D RA4 RAPC SP16 HU2 HU1 RTOP SP47 RSP ROK;
      unfold HarnessM.opdelete; apply implMA_from_evtF; unfold AOPDEL_SZ, AOPDEL.
    - zstep. zstep. apply evtF_done. eapply implMA_afree_call_data; eauto.
    - zstep. apply evtF_done. eapply implMA_afree_call_data; eauto.
  Qed.
End OpDelTop.
End CANSEC1.
