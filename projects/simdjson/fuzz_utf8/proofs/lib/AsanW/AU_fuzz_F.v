(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import DrvAgree F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg RtCells ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AU_kit AU_iface AU_consts AU_client_kit AU_steptac AU_first_A.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import ShadowTac.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

Ltac zland K := try (change 18446744073709551615 with (2^64-1) in K; rewrite ?zb_land_mask in K by lia; rewrite ?Z.mod_small in K by lia).
Ltac bcase K := if_cases K; zify_cond K; zland K.

Section CANSEC1. Context {rc : runConstT}.
Definition ACXA_ICEPT : Z := 0x7592c.    (* [comment removed for export] *)
Definition ADSO : Z := 0x167f08.         (* [comment removed for export] *)

Section S.
  Variables (sp gp tp : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (D SZ SPA F : Z).
  Variable RNG : footprint.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RL : rng RNG (SPA + 80) 16.
  Hypothesis SPAB : ATOP <= SPA /\ SPA + 112 <= 2^47.

  Notation WST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 s6v x23 x24 s9v x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 SZ) (Z_to_bv 64 D) (Z_to_bv 64 (shad F)) x21 s6v x23 x24 s9v (Z_to_bv 64 ASHOFF) x27 x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma f_w1 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x27 x28 x29 x30 x31 : word) m (l80 l88 : list byte),
    mem_inv asegs m -> rw_cells asegs m AVEC_GUARD guard0 -> rw_cells asegs m (SPA + 80) [CB 8 l80; CB 8 l88] ->
    evtF asegs RNG (fun ms' => exists m' y11 y12,
        ms' = WST ARSI m' (Z_to_bv 64 0xb184c) x5 x6 x7 (Z_to_bv 64 AVEC) y11 y12 x13 x14 x15 x16 x17 x21 (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 F) x27 x28 x29 x30 x31
        /\ munch [(SPA + 80, SPA + 96); (AVEC_GUARD, AVEC_GUARD + 2)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' AVEC_GUARD [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 2)]
        /\ rw_cells asegs m' (SPA + 80) [C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F)])
      (WST 0xb1824 m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 F) x27 x28 x29 x30 x31).
  Proof.
    intros until l88. intros MI GRD LOC. unfold AVEC_GUARD, AVEC, ARSI, guard0 in *. atop_facts.
    pose proof (munch_refl [(SPA + 80, SPA + 96); (6951968, 6951968 + 2)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    steps_to 0xafeb8.
    apply evtF_done. eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact GRD| exact LOC].
  Qed.

  (* [comment removed for export] *)
  Lemma f_w2 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x27 x28 x29 x30 x31 : word) (s6v s9v : word) m,
    mem_inv asegs m ->
    evtF asegs RNG (fun ms' =>
        ms' = WST ACXA_ICEPT m (Z_to_bv 64 0xb1868) x5 x6 x7 (Z_to_bv 64 ADTOR_THUNK) (Z_to_bv 64 AVEC) (Z_to_bv 64 ADSO) x13 x14 x15 x16 x17 x21 s6v x23 x24 s9v x27 x28 x29 x30 x31)
      (WST 0xb184c m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 s6v x23 x24 s9v x27 x28 x29 x30 x31).
  Proof.
    intros until m. intros MI. unfold ACXA_ICEPT, ADTOR_THUNK, AVEC, ADSO in *.
    steps_to 0x7592c.
    apply evtF_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma f_w3 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x27 x28 x29 x30 x31 : word) (s6v s9v : word) m (g0 g1 : byte),
    mem_inv asegs m -> rw_cells asegs m AVEC_GUARD [C1 g0; C1 g1] -> rw_cells asegs m (SPA + 80) [C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F)] ->
    evtF asegs RNG (fun ms' => exists m' y1 y10 y11,
        ms' = WST 0xb1640 m' y1 x5 x6 x7 y10 y11 x12 x13 x14 x15 x16 x17 x21 (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 F) x27 x28 x29 x30 x31
        /\ munch [(AVEC_GUARD, AVEC_GUARD + 2)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' AVEC_GUARD guard1
        /\ rw_cells asegs m' (SPA + 80) [C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F)])
      (WST 0xb1868 m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 s6v x23 x24 s9v x27 x28 x29 x30 x31).
  Proof.
    intros until g1. intros MI GRD LOC. unfold AVEC_GUARD, guard1 in *. atop_facts.
    pose proof (munch_refl [(6951968, 6951968 + 2)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    steps_to 0xb1640.
    apply evtF_done. eexists _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact GRD| exact LOC].
  Qed.
End S.
End CANSEC1.
