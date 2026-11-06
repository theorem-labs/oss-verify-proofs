(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep ZBridge Cells InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow ITreeA StepF StrwF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells ShadowTac F_syscalls StdioFiles Stdio_kit I_fwrite AExitU_wr AIcptU_hmap AIcptU_fflush.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation rt_real_wcrtomb m := (rw_cells asegs m 0x168f20 [C8 (Z_to_bv 64 0x14e768)]).
Definition BOFF_OUT : Z := 1354800.     (* [comment removed for export] *)
Definition BOFF_ERR : Z := 1697640.     (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Section Defs.
  Variables (T SLO SHI : Z).
  Definition icpt_rt (m : mem) : Prop :=
    rt_inited m /\ rt_real_fflush m /\ rt_real_fwrite m /\ rt_real_wcrtomb m /\ rt_real_mem m /\ rt_got_ric m.
  Definition icpt_tab (m : mem) : Prop :=
    rw_cells asegs m 0x16fc00 [C8 (Z_to_bv 64 HMAP)] /\ rw_cells asegs m HMAP [C8 (Z_to_bv 64 T)]
    /\ rw_cells asegs m (T + BOFF_ERR) hm_bucket0 /\ rw_cells asegs m (T + BOFF_OUT) hm_bucket0
    /\ 0x6c7000 <= T /\ T + 0x38e000 <= ATOP /\ T mod 8 = 0.
  Definition icptU (m : mem) : Prop := icpt_rt m /\ icpt_tab m.
  Definition icptU_rng (RNG : footprint) : Prop := rng RNG (T + BOFF_ERR) 120 /\ rng RNG (T + BOFF_OUT) 120.

  Lemma icptU_rng_mono : forall RNG RNG', fp_le RNG RNG' -> icptU_rng RNG -> icptU_rng RNG'.
  Proof. intros RNG RNG' LE [A B]. split; (eapply rng_fp_le; [exact LE|]; assumption). Qed.

  (* [comment removed for export] *)
  Lemma icptU_frame_exit : forall W m m', icptU m -> munch W m m' -> wmono asegs m m' -> Forall exit_wr_ok W -> icptU m'.
  Proof.
    intros W m m' ((R1 & R2 & R3 & R4 & R5 & R6) & (M1 & M2 & B1 & B2 & TLO & THI & TAL)) MU WM HW.
    assert (X : forall A cs, rw_cells asegs m A cs ->
                  (A + Z.of_nat (cells_size cs) <= 0x16b840 \/ (0x16bb08 <= A /\ A + Z.of_nat (cells_size cs) <= 0x16cd50)
                   \/ (0x16cd51 <= A /\ A + Z.of_nat (cells_size cs) <= 0x6a4db8) \/ (0x6c5060 <= A /\ A + Z.of_nat (cells_size cs) <= ATOP)) ->
                  rw_cells asegs m' A cs).
    { intros A cs H HD. eapply rw_cells_transport; [exact H | exact MU | exact WM |].
      clear -HW HD. induction HW as [|[l h] W H1 HW IH]; cbn; [exact I|]. split; [| exact IH].
      unfold exit_wr_ok in H1. cbn [fst snd] in H1. lia. }
    unfold icptU, icpt_rt, icpt_tab, HMAP, BOFF_ERR, BOFF_OUT, hm_bucket0 in *.
    repeat match goal with |- _ /\ _ => split end; try assumption.
    all: (apply X; [assumption | cbn [cells_size csize Nat.add]; lia]).
  Qed.
End Defs.
End CANSEC1.
