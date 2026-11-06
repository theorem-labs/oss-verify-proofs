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
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg RtCells ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import AU_kit AU_iface AU_consts AU_client_kit AU_steptac AU_first_A.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import ShadowTac.
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
Definition ACXA_ICEPT : Z := 0x75778.    (* [comment removed for export] *)
Definition ADSO : Z := 0x173e60.         (* [comment removed for export] *)

Section S.
  Variables (sp gp tp : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (D SZ SPA F : Z).
  Variable RNG : footprint.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RL : rng RNG (SPA + 40) 16.
  Hypothesis SPAB : ATOP <= SPA /\ SPA + 80 <= 2^47.

  Notation WST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 s4v x21 x22 x23 x24 s10v x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
             x18 (Z_to_bv 64 D) s4v x21 x22 x23 x24 (Z_to_bv 64 ASHOFF) s10v (Z_to_bv 64 (shad F)) x28 x29 x30 x31)
        FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma f_w1 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x28 x29 x30 x31 : word) m (l40 l48 : list byte),
    mem_inv bsegs m -> rw_cells bsegs m AVEC_GUARD guard0 -> rw_cells bsegs m (SPA + 40) [CB 8 l40; CB 8 l48] ->
    evtF bsegs RNG (fun ms' => exists m' y11 y12,
        ms' = WST ARSI m' (Z_to_bv 64 0xb1670) x5 x6 x7 (Z_to_bv 64 AVEC) y11 y12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 F) x21 x22 x23 x24 (Z_to_bv 64 F) x28 x29 x30 x31
        /\ munch [(SPA + 40, SPA + 56); (AVEC_GUARD, AVEC_GUARD + 2)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' AVEC_GUARD [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 2)]
        /\ rw_cells bsegs m' (SPA + 40) [C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F)])
      (WST 0xb1648 m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 F) x21 x22 x23 x24 (Z_to_bv 64 F) x28 x29 x30 x31).
  Proof.
    intros until l48. intros MI GRD LOC. unfold AVEC_GUARD, AVEC, ARSI, guard0 in *. atop_facts.
    pose proof (munch_refl [(SPA + 40, SPA + 56); (7002016, 7002016 + 2)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    steps_to 0xafd04.
    apply evtF_done. eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact GRD| exact LOC].
  Qed.

  (* [comment removed for export] *)
  Lemma f_w2 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x28 x29 x30 x31 : word) (s4v s10v : word) m,
    mem_inv bsegs m ->
    evtF bsegs RNG (fun ms' =>
        ms' = WST ACXA_ICEPT m (Z_to_bv 64 0xb168c) x5 x6 x7 (Z_to_bv 64 ADTOR_THUNK) (Z_to_bv 64 AVEC) (Z_to_bv 64 ADSO) x13 x14 x15 x16 x17 x18 s4v x21 x22 x23 x24 s10v x28 x29 x30 x31)
      (WST 0xb1670 m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 s4v x21 x22 x23 x24 s10v x28 x29 x30 x31).
  Proof.
    intros until m. intros MI. unfold ACXA_ICEPT, ADTOR_THUNK, AVEC, ADSO in *.
    steps_to 0x75778.
    apply evtF_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma f_w3 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x28 x29 x30 x31 : word) (s4v s10v : word) m (g0 g1 : byte),
    mem_inv bsegs m -> rw_cells bsegs m AVEC_GUARD [C1 g0; C1 g1] -> rw_cells bsegs m (SPA + 40) [C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F)] ->
    evtF bsegs RNG (fun ms' => exists m' y1 y10 y11,
        ms' = WST 0xb143c m' y1 x5 x6 x7 y10 y11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 F) x21 x22 x23 x24 (Z_to_bv 64 F) x28 x29 x30 x31
        /\ munch [(AVEC_GUARD, AVEC_GUARD + 2)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' AVEC_GUARD guard1
        /\ rw_cells bsegs m' (SPA + 40) [C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F)])
      (WST 0xb168c m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 s4v x21 x22 x23 x24 s10v x28 x29 x30 x31).
  Proof.
    intros until g1. intros MI GRD LOC. unfold AVEC_GUARD, guard1 in *. atop_facts.
    pose proof (munch_refl [(7002016, 7002016 + 2)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    steps_to 0xb143c.
    apply evtF_done. eexists _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact GRD| exact LOC].
  Qed.
End S.
End CANSEC1.
