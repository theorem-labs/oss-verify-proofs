(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Arr Bytes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Image ZBridge RegsEquiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Mem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_lock.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Definition NEED_LOCKS : Z := 0x53d2b.      (* [comment removed for export] *)
Definition lock_entry : Z := 0x2114c.
Definition unlock_entry : Z := 0x213d4.
Definition errno_location_entry : Z := 0x181bc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a3,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom ssegs)
    /\ munch [] m m /\ wmono ssegs m m /\ mem_inv ssegs m
    /\ rw_cells ssegs m NEED_LOCKS [C1 (Z_to_bv 8 0)].

Lemma lock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  rw_cells ssegs m NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
  mem_inv ssegs m ->
  evt ssegs (lock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2114c) fc None m (seg_rom ssegs)).
Proof.
  intros until m. intros NL MI. unfold NEED_LOCKS in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ssegs m) as WM.
  do 3 step. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). if_true.
  step. unfold lock_post, NEED_LOCKS. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition unlock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (v : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (sx32 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom ssegs)
    /\ munch [] m m /\ wmono ssegs m m /\ mem_inv ssegs m
    /\ rw_cells ssegs m (bv_unsigned a0) [C4 v].

Lemma unlock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (v : word),
  rw_cells ssegs m (bv_unsigned a0) [C4 v] ->
  mem_inv ssegs m ->
  (bv_unsigned v mod 2^32 < 2^31)%Z ->          (* [comment removed for export] *)
  evt ssegs (unlock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 v F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x213d4) fc None m (seg_rom ssegs)).
Proof.
  intros until v. intros LK MI POS.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ssegs m) as WM.
  do 2 step. if_cases K; zify_cond K.
  { exfalso. revert K. unfold sx32.
    pose proof (bv_unsigned_in_range 64 v) as Rv. unfold bv_modulus in Rv.
    assert (E : bv_swrap 32 (bv_unsigned v) = (bv_unsigned v mod 2^32)%Z).
    { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
      change (2 ^ 32 `div` 2)%Z with (2^31)%Z. Z.div_mod_to_equations. lia. }
    rewrite E. rewrite unsigned_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
  step. unfold unlock_post. finish.
Qed.

(* [comment removed for export] *)
Lemma unlock_spec0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  rw_cells ssegs m (bv_unsigned a0) [C4 (Z_to_bv 64 0)] ->
  mem_inv ssegs m ->
  evt ssegs (unlock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 0) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x213d4) fc None m (seg_rom ssegs)).
Proof. intros. apply unlock_spec; [assumption|assumption|]. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma sx32_zero : sx32 (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition errno_location_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (errno_addr tp)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom ssegs)
    /\ munch [] m m /\ wmono ssegs m m /\ mem_inv ssegs m.

Lemma errno_location_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  mem_inv ssegs m ->
  evt ssegs (errno_location_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x181bc) fc None m (seg_rom ssegs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ssegs m) as WM.
  do 3 step. unfold errno_location_post. finish.
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Definition NEED_LOCKS : Z := 0x544eb.      (* [comment removed for export] *)
Definition lock_entry : Z := 0x2190c.
Definition unlock_entry : Z := 0x21b94.
Definition errno_location_entry : Z := 0x1897c.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a3,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs)
    /\ munch [] m m /\ wmono usegs m m /\ mem_inv usegs m
    /\ rw_cells usegs m NEED_LOCKS [C1 (Z_to_bv 8 0)].

Lemma lock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  rw_cells usegs m NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
  mem_inv usegs m ->
  evt usegs (lock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2190c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros NL MI. unfold NEED_LOCKS in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 3 step. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). if_true.
  step. unfold lock_post, NEED_LOCKS. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition unlock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (v : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (sx32 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs)
    /\ munch [] m m /\ wmono usegs m m /\ mem_inv usegs m
    /\ rw_cells usegs m (bv_unsigned a0) [C4 v].

Lemma unlock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (v : word),
  rw_cells usegs m (bv_unsigned a0) [C4 v] ->
  mem_inv usegs m ->
  (bv_unsigned v mod 2^32 < 2^31)%Z ->          (* [comment removed for export] *)
  evt usegs (unlock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 v F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x21b94) fc None m (seg_rom usegs)).
Proof.
  intros until v. intros LK MI POS.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 2 step. if_cases K; zify_cond K.
  { exfalso. revert K. unfold sx32.
    pose proof (bv_unsigned_in_range 64 v) as Rv. unfold bv_modulus in Rv.
    assert (E : bv_swrap 32 (bv_unsigned v) = (bv_unsigned v mod 2^32)%Z).
    { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
      change (2 ^ 32 `div` 2)%Z with (2^31)%Z. Z.div_mod_to_equations. lia. }
    rewrite E. rewrite unsigned_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
  step. unfold unlock_post. finish.
Qed.

(* [comment removed for export] *)
Lemma unlock_spec0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  rw_cells usegs m (bv_unsigned a0) [C4 (Z_to_bv 64 0)] ->
  mem_inv usegs m ->
  evt usegs (unlock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 0) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x21b94) fc None m (seg_rom usegs)).
Proof. intros. apply unlock_spec; [assumption|assumption|]. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma sx32_zero : sx32 (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition errno_location_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (errno_addr tp)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs)
    /\ munch [] m m /\ wmono usegs m m /\ mem_inv usegs m.

Lemma errno_location_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  mem_inv usegs m ->
  evt usegs (errno_location_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1897c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 3 step. unfold errno_location_post. finish.
Qed.
End TwB.
End F_lock.

(* [comment removed for export] *)
Module F_stdio_leaf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ferror_entry := 0x1ac20%Z.
Definition fileno_entry := 0x1b020%Z.

Lemma lock_word_neg : (9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295)))%Z.
Proof. vm_compute. discriminate. Qed.

(* [comment removed for export] *)
Definition ferr_bit__stmt : Prop := forall flags : word,
  (Z.shiftr ((Z.shiftl (bv_unsigned (sx32 flags)) 58) mod 18446744073709551616) 63 = (bv_unsigned flags / 32) mod 2)%Z.
Section Sz2.
Variables flags : ltac2:(SecDiet.SzSec.tyM 'ferr_bit__stmt "v" @flags).
#[using="Type"] Lemma ferr_bit__body : ltac2:(SecDiet.SzSec.bodyP 'ferr_bit__stmt "v").
Proof.
 unfold sx32. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (bv_unsigned_in_range 64 flags) as R. unfold bv_modulus in R.
  Z.div_mod_to_equations. lia.
Qed.
End Sz2.
Lemma ferr_bit : ltac:(let t := eval cbv delta [ferr_bit__stmt] in ferr_bit__stmt in exact t).
Proof. intros flags. ltac2:(SecDiet.SzSec.closeP 'ferr_bit__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ferror_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 flags : word) rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd (mode : word) lbf tail
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ((bv_unsigned flags / 32) mod 2)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail).

Definition ferror_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z)
    flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  stk ssegs m lo (bv_unsigned sp) ->
  rw_cells ssegs m (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  mem_inv ssegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + 232 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  evt ssegs (ferror_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ac20) fc None m (seg_rom ssegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail : ltac2:(SecDiet.SzSec.tyM 'ferror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma ferror_spec__body : ltac2:(SecDiet.SzSec.bodyP 'ferror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST FC MI LO SEP.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  unfold file_cells in FC.
  carve_frame 32%nat ST.
  do 5 step. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. pose proof lock_word_neg. lia. }
  zstep. zstep. zstep. rewrite ferr_bit.
  do 4 step. release_frame FR ST (bv_unsigned sp). step.
  unfold ferror_post, file_cells. finish.
Qed.
End Sz3.
Lemma ferror_spec : ltac:(let t := eval cbv delta [ferror_spec__stmt] in ferror_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail. ltac2:(SecDiet.SzSec.closeP 'ferror_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fileno_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 flags : word) rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd (mode : word) lbf tail
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail).

Definition fileno_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z)
    flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  stk ssegs m lo (bv_unsigned sp) ->
  rw_cells ssegs m (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  mem_inv ssegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + 232 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 <= fd < 2^31)%Z ->
  evt ssegs (fileno_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b020) fc None m (seg_rom ssegs)).
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail : ltac2:(SecDiet.SzSec.tyM 'fileno_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma fileno_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fileno_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST FC MI LO SEP FD.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  unfold file_cells in FC.
  carve_frame 32%nat ST.
  do 5 step. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. pose proof lock_word_neg. lia. }
  zstep.
  replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd).
  2:{ unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. }
  zstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  zstep. do 4 step. release_frame FR ST (bv_unsigned sp). step.
  unfold fileno_post, file_cells. finish.
Qed.
End Sz4.
Lemma fileno_spec : ltac:(let t := eval cbv delta [fileno_spec__stmt] in fileno_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail. ltac2:(SecDiet.SzSec.closeP 'fileno_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ferror_entry := 0x1b3e0%Z.
Definition fileno_entry := 0x1b7e0%Z.

Lemma lock_word_neg : (9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295)))%Z.
Proof. vm_compute. discriminate. Qed.

(* [comment removed for export] *)
Definition ferr_bit__stmt : Prop := forall flags : word,
  (Z.shiftr ((Z.shiftl (bv_unsigned (sx32 flags)) 58) mod 18446744073709551616) 63 = (bv_unsigned flags / 32) mod 2)%Z.
Section Sz2.
Variables flags : ltac2:(SecDiet.SzSec.tyM 'ferr_bit__stmt "v" @flags).
#[using="Type"] Lemma ferr_bit__body : ltac2:(SecDiet.SzSec.bodyP 'ferr_bit__stmt "v").
Proof.
 unfold sx32. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (bv_unsigned_in_range 64 flags) as R. unfold bv_modulus in R.
  Z.div_mod_to_equations. lia.
Qed.
End Sz2.
Lemma ferr_bit : ltac:(let t := eval cbv delta [ferr_bit__stmt] in ferr_bit__stmt in exact t).
Proof. intros flags. ltac2:(SecDiet.SzSec.closeP 'ferr_bit__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ferror_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 flags : word) rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd (mode : word) lbf tail
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ((bv_unsigned flags / 32) mod 2)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail).

Definition ferror_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z)
    flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  mem_inv usegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + 232 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  evt usegs (ferror_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b3e0) fc None m (seg_rom usegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail : ltac2:(SecDiet.SzSec.tyM 'ferror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma ferror_spec__body : ltac2:(SecDiet.SzSec.bodyP 'ferror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST FC MI LO SEP.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold file_cells in FC.
  carve_frame 32%nat ST.
  do 5 step. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. pose proof lock_word_neg. lia. }
  zstep. zstep. zstep. rewrite ferr_bit.
  do 4 step. release_frame FR ST (bv_unsigned sp). step.
  unfold ferror_post, file_cells. finish.
Qed.
End Sz3.
Lemma ferror_spec : ltac:(let t := eval cbv delta [ferror_spec__stmt] in ferror_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail. ltac2:(SecDiet.SzSec.closeP 'ferror_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fileno_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 flags : word) rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd (mode : word) lbf tail
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail).

Definition fileno_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z)
    flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  mem_inv usegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + 232 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 <= fd < 2^31)%Z ->
  evt usegs (fileno_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b7e0) fc None m (seg_rom usegs)).
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail : ltac2:(SecDiet.SzSec.tyM 'fileno_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma fileno_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fileno_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST FC MI LO SEP FD.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold file_cells in FC.
  carve_frame 32%nat ST.
  do 5 step. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. pose proof lock_word_neg. lia. }
  zstep.
  replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd).
  2:{ unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. }
  zstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  zstep. do 4 step. release_frame FR ST (bv_unsigned sp). step.
  unfold fileno_post, file_cells. finish.
Qed.
End Sz4.
Lemma fileno_spec : ltac:(let t := eval cbv delta [fileno_spec__stmt] in fileno_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail. ltac2:(SecDiet.SzSec.closeP 'fileno_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_stdio_leaf.

(* [comment removed for export] *)
Module F_syscalls.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)

Definition sysret_entry := 0x1861c%Z.
Definition read_entry := 0x214e8%Z.
Definition close_entry := 0x21488%Z.
Definition open_entry := 0x18538%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

Definition sysret_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (errv : word) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  evt ssegs (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1861c) fc None m (seg_rom ssegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m errv lo : ltac2:(SecDiet.SzSec.tyM 'sysret_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma sysret_spec__body : ltac2:(SecDiet.SzSec.bodyP 'sysret_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST ERR MI LO SEP TP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  do 3 step. if_cases Hc; zify_cond Hc.
  - (* [comment removed for export] *)
    step. unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_small a0) by lia. finish.
  - carve_frame 16%nat ST.
    do 14 step.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    rewrite negw_errno in ERR by lia.
    unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
    release_frame FR ST (bv_unsigned sp).
    finish.
Qed.
End Sz1.
Lemma sysret_spec : ltac:(let t := eval cbv delta [sysret_spec__stmt] in sysret_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m errv lo. ltac2:(SecDiet.SzSec.closeP 'sysret_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition read_ret (a : read_ans) : word :=
  match a with RdErr _ => Z_to_bv 64 (-1) | RdData bs => Z_to_bv 64 (Z.of_nat (length bs)) end.

Definition read_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells ssegs m' B [CB n junk]
                    /\ rw_cells ssegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells ssegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells ssegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

Definition read_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd count : Z) (junk : list byte) (errv : word) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  rw_cells ssegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (1 <= count <= 2^24)%Z (* [comment removed for export] *) ->
  (bv_unsigned a1 + count <= 2^47)%Z (* [comment removed for export] *) ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a1 + count <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + count <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a1)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl ssegs (at_node ssegs) (npeek ssegs) (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
       (epost (read_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x214e8) fc None m (seg_rom ssegs)).
Section Sz2.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fd count junk errv lo : ltac2:(SecDiet.SzSec.tyM 'read_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma read_spec__body : ltac2:(SecDiet.SzSec.bodyP 'read_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST DST ERR MI -> -> FD CNT UB LO SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + Z.of_nat (Z.to_nat count));
                          (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  apply impl_enode.
  carve_frame 16%nat ST.
  do 18 step.
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_read_Some in Hdec; [|lia].
  destruct ans as [e|bs].
  - destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    do 3 step. release_frame FR ST (bv_unsigned sp).
    step. call sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ].
    unfold read_post, sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    finish; lia.
  - destruct Hdec as [-> Hlen]. sys_nret.
    do 3 step. release_frame FR ST (bv_unsigned sp).
    step. call sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ].
    unfold read_post, sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    finish; lia.
Qed.
End Sz2.
Lemma read_spec : ltac:(let t := eval cbv delta [read_spec__stmt] in read_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fd count junk errv lo. ltac2:(SecDiet.SzSec.closeP 'read_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition eintr_mask_errno__stmt : Prop := forall e, (1 <= e <= 4095)%Z ->
  Z_to_bv 64 (Z.land ((Z.b2z ((bv_unsigned (errno_ret e) + 4) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616)
                     (bv_unsigned (errno_ret e)))
  = if (e =? 4)%Z then Z_to_bv 64 0 else errno_ret e.
Section Sz3.
Variables e : ltac2:(SecDiet.SzSec.tyM 'eintr_mask_errno__stmt "v" @e).
#[using="Type"] Lemma eintr_mask_errno__body : ltac2:(SecDiet.SzSec.bodyP 'eintr_mask_errno__stmt "v").
Proof.
  intros He.
 rewrite unsigned_errno_ret by lia.
  destruct (Z.eqb_spec e 4) as [->|Hne].
  - replace ((2 ^ 64 - 4 + 4) mod 18446744073709551616)%Z with 0%Z by reflexivity.
    cbn. reflexivity.
  - assert (Hnz : ((2 ^ 64 - e + 4) mod 18446744073709551616 <? 1)%Z = false).
    { apply Z.ltb_ge. destruct (Z.ltb_spec0 e 4).
      - replace (2 ^ 64 - e + 4)%Z with ((4 - e) + 1 * 18446744073709551616)%Z by lia.
        rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      - rewrite Z.mod_small by lia. lia. }
    rewrite Hnz. cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616)%Z with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. change (2^64)%Z with 18446744073709551616%Z.
    rewrite Z.mod_small by lia. unfold errno_ret. rewrite <- (Z_to_bv_minus_mod (18446744073709551616 - e)). f_equal. lia.
Qed.
End Sz3.
Lemma eintr_mask_errno : ltac:(let t := eval cbv delta [eintr_mask_errno__stmt] in eintr_mask_errno__stmt in exact t).
Proof. intros e. ltac2:(SecDiet.SzSec.closeP 'eintr_mask_errno__body "v"). Qed.

Definition close_ret (a : sret) : word :=
  match a with
  | SVal _ => Z_to_bv 64 0
  | SErr e => if (e =? EINTR)%Z then Z_to_bv 64 0 else Z_to_bv 64 (-1)
  end.
Definition close_errno (a : sret) (errv : word) : word :=
  match a with
  | SVal _ => errv
  | SErr e => if (e =? EINTR)%Z then errv else Z_to_bv 64 e
  end.

Definition close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (errv : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (close_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 (close_errno a errv)].

Definition close_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd : Z) (errv : word) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 fd -> (3 <= fd < 2^32)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl ssegs (at_node ssegs) (npeek ssegs) (enode (NClose fd) dec_close)
       (epost (close_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x21488) fc None m (seg_rom ssegs)).
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fd errv lo : ltac2:(SecDiet.SzSec.tyM 'close_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma close_spec__body : ltac2:(SecDiet.SzSec.bodyP 'close_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST ERR MI -> FD LO SEP1 TP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  apply impl_enode.
  carve_frame 16%nat ST.
  do 20 step.
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_plain_Some in Hdec.
  destruct ans as [e|v].
  - destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    do 2 step. rewrite sextw_errno by lia.
    do 4 zstep. rewrite eintr_mask_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *.
    destruct (Z.eqb_spec e 4) as [->|Hne].
    + rewrite errno_of_lit in * by lia.
      do 4 step. release_frame FR ST (bv_unsigned sp).
      unfold close_post, close_ret, close_errno, EINTR. rewrite Z.eqb_refl. finish.
    + rewrite errno_of_errno_ret in * by lia.
      do 4 step. release_frame FR ST (bv_unsigned sp).
      unfold close_post, close_ret, close_errno, EINTR. replace (e =? 4)%Z with false by (symmetry; apply Z.eqb_neq; lia). finish.
  - destruct Hdec as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v. unfold eff0. sys_nret.
    do 6 zstep. rewrite Z.land_0_r. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 4 step. release_frame FR ST (bv_unsigned sp).
    unfold close_post, close_ret, close_errno. finish.
Qed.
End Sz4.
Lemma close_spec : ltac:(let t := eval cbv delta [close_spec__stmt] in close_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fd errv lo. ltac2:(SecDiet.SzSec.closeP 'close_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x22620%Z.
Definition ssp_guard := 0x53d08%Z.

Definition open_ret (a : sret) : word :=
  match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
  match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.

Definition open_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (path : list byte) (errv canary : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 (open_errno a errv)]
    /\ bytes_at ssegs m' P (path ++ [Z_to_bv 8 0])
    /\ rw_cells ssegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)]
    /\ rw_cells ssegs m' ssp_guard [C8 canary]
    /\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.

Definition open_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (path : list byte) (errv canary : word) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  bytes_at ssegs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  rw_cells ssegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
  rw_cells ssegs m ssp_guard [C8 canary] ->
  mem_inv ssegs m ->
  a1 = Z_to_bv 64 0 (* [comment removed for export] *) ->
  ~ In (Z_to_bv 8 0) path ->
  Namei.path_has_slash path = false -> Fs.path_eqb path Namei.dotdot_path = false ->   (* [comment removed for export] *)
  (lo <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a0)%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= ssp_guard \/ ssp_guard + 8 <= errno_addr tp)%Z ->
  (got_ssp + 8 <= errno_addr tp \/ errno_addr tp + 4 <= got_ssp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl ssegs (at_node ssegs) (npeek ssegs) (enode (NOpen path) dec_open)
       (epost (open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x18538) fc None m (seg_rom ssegs)).
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path errv canary lo : ltac2:(SecDiet.SzSec.tyM 'open_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma open_spec__body : ltac2:(SecDiet.SzSec.bodyP 'open_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST SRC ERR GOT SSP MI -> NUL NSLASH NDOTDOT LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 TP.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BP. rewrite length_app in BP. cbn [length] in BP.
  apply impl_enode.
  carve_frame 96%nat ST.
  do 18 step. if_false. do 3 step. if_false. do 2 step.
  do 8 step. (* [comment removed for export] *) do 8 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_plain_Some in Hdec.
  destruct ans as [e|fd].
  - destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    do 4 step. if_true. step. rewrite sextw_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    do 3 step. if_false. do 6 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
  - destruct Hdec as (-> & Hfd & Hrange). apply andb_prop in Hfd as [Hfd3 Hfd]. apply Z.leb_le in Hfd3. apply Z.leb_le in Hfd. unfold eff0. sys_nret.
    do 4 step. if_true. step. rewrite sextw_small by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 3 step. if_false. step. rewrite sextw_small by lia. do 5 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
Qed.
End Sz5.
Lemma open_spec : ltac:(let t := eval cbv delta [open_spec__stmt] in open_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path errv canary lo. ltac2:(SecDiet.SzSec.closeP 'open_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)

Definition sysret_entry := 0x18ddc%Z.
Definition read_entry := 0x21ca8%Z.
Definition close_entry := 0x21c48%Z.
Definition open_entry := 0x18cf8%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

Definition sysret_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  evt usegs (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x18ddc) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m errv lo : ltac2:(SecDiet.SzSec.tyM 'sysret_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma sysret_spec__body : ltac2:(SecDiet.SzSec.bodyP 'sysret_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST ERR MI LO SEP TP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  do 3 step. if_cases Hc; zify_cond Hc.
  - (* [comment removed for export] *)
    step. unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_small a0) by lia. finish.
  - carve_frame 16%nat ST.
    do 14 step.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    rewrite negw_errno in ERR by lia.
    unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
    release_frame FR ST (bv_unsigned sp).
    finish.
Qed.
End Sz1.
Lemma sysret_spec : ltac:(let t := eval cbv delta [sysret_spec__stmt] in sysret_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m errv lo. ltac2:(SecDiet.SzSec.closeP 'sysret_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition read_ret (a : read_ans) : word :=
  match a with RdErr _ => Z_to_bv 64 (-1) | RdData bs => Z_to_bv 64 (Z.of_nat (length bs)) end.

Definition read_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells usegs m' B [CB n junk]
                    /\ rw_cells usegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells usegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells usegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.

Definition read_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd count : Z) (junk : list byte) (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (bv_unsigned a1) [CB (Z.to_nat count) junk] ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 fd -> a2 = Z_to_bv 64 count ->
  (3 <= fd < 2^32)%Z -> (1 <= count <= 2^24)%Z (* [comment removed for export] *) ->
  (bv_unsigned a1 + count <= 2^47)%Z (* [comment removed for export] *) ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a1 + count <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + count <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a1)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (npeek usegs) (enode (NRead fd (bv_unsigned a1) count) (dec_read (bv_unsigned a1) count))
       (epost (read_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a1) (Z.to_nat count) junk errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x21ca8) fc None m (seg_rom usegs)).
Section Sz2.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fd count junk errv lo : ltac2:(SecDiet.SzSec.tyM 'read_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma read_spec__body : ltac2:(SecDiet.SzSec.bodyP 'read_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST DST ERR MI -> -> FD CNT UB LO SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + Z.of_nat (Z.to_nat count));
                          (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  apply impl_enode.
  carve_frame 16%nat ST.
  do 18 step.
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_read_Some in Hdec; [|lia].
  destruct ans as [e|bs].
  - destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    do 3 step. release_frame FR ST (bv_unsigned sp).
    step. call sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ].
    unfold read_post, sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    finish; lia.
  - destruct Hdec as [-> Hlen]. sys_nret.
    do 3 step. release_frame FR ST (bv_unsigned sp).
    step. call sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ].
    unfold read_post, sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    finish; lia.
Qed.
End Sz2.
Lemma read_spec : ltac:(let t := eval cbv delta [read_spec__stmt] in read_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fd count junk errv lo. ltac2:(SecDiet.SzSec.closeP 'read_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition eintr_mask_errno__stmt : Prop := forall e, (1 <= e <= 4095)%Z ->
  Z_to_bv 64 (Z.land ((Z.b2z ((bv_unsigned (errno_ret e) + 4) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616)
                     (bv_unsigned (errno_ret e)))
  = if (e =? 4)%Z then Z_to_bv 64 0 else errno_ret e.
Section Sz3.
Variables e : ltac2:(SecDiet.SzSec.tyM 'eintr_mask_errno__stmt "v" @e).
#[using="Type"] Lemma eintr_mask_errno__body : ltac2:(SecDiet.SzSec.bodyP 'eintr_mask_errno__stmt "v").
Proof.
  intros He.
 rewrite unsigned_errno_ret by lia.
  destruct (Z.eqb_spec e 4) as [->|Hne].
  - replace ((2 ^ 64 - 4 + 4) mod 18446744073709551616)%Z with 0%Z by reflexivity.
    cbn. reflexivity.
  - assert (Hnz : ((2 ^ 64 - e + 4) mod 18446744073709551616 <? 1)%Z = false).
    { apply Z.ltb_ge. destruct (Z.ltb_spec0 e 4).
      - replace (2 ^ 64 - e + 4)%Z with ((4 - e) + 1 * 18446744073709551616)%Z by lia.
        rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
      - rewrite Z.mod_small by lia. lia. }
    rewrite Hnz. cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616)%Z with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. change (2^64)%Z with 18446744073709551616%Z.
    rewrite Z.mod_small by lia. unfold errno_ret. rewrite <- (Z_to_bv_minus_mod (18446744073709551616 - e)). f_equal. lia.
Qed.
End Sz3.
Lemma eintr_mask_errno : ltac:(let t := eval cbv delta [eintr_mask_errno__stmt] in eintr_mask_errno__stmt in exact t).
Proof. intros e. ltac2:(SecDiet.SzSec.closeP 'eintr_mask_errno__body "v"). Qed.

Definition close_ret (a : sret) : word :=
  match a with
  | SVal _ => Z_to_bv 64 0
  | SErr e => if (e =? EINTR)%Z then Z_to_bv 64 0 else Z_to_bv 64 (-1)
  end.
Definition close_errno (a : sret) (errv : word) : word :=
  match a with
  | SVal _ => errv
  | SErr e => if (e =? EINTR)%Z then errv else Z_to_bv 64 e
  end.

Definition close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (errv : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (close_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (close_errno a errv)].

Definition close_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (fd : Z) (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 fd -> (3 <= fd < 2^32)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (npeek usegs) (enode (NClose fd) dec_close)
       (epost (close_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x21c48) fc None m (seg_rom usegs)).
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fd errv lo : ltac2:(SecDiet.SzSec.tyM 'close_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma close_spec__body : ltac2:(SecDiet.SzSec.bodyP 'close_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST ERR MI -> FD LO SEP1 TP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  apply impl_enode.
  carve_frame 16%nat ST.
  do 20 step.
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_plain_Some in Hdec.
  destruct ans as [e|v].
  - destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    do 2 step. rewrite sextw_errno by lia.
    do 4 zstep. rewrite eintr_mask_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *.
    destruct (Z.eqb_spec e 4) as [->|Hne].
    + rewrite errno_of_lit in * by lia.
      do 4 step. release_frame FR ST (bv_unsigned sp).
      unfold close_post, close_ret, close_errno, EINTR. rewrite Z.eqb_refl. finish.
    + rewrite errno_of_errno_ret in * by lia.
      do 4 step. release_frame FR ST (bv_unsigned sp).
      unfold close_post, close_ret, close_errno, EINTR. replace (e =? 4)%Z with false by (symmetry; apply Z.eqb_neq; lia). finish.
  - destruct Hdec as (-> & Hv & _). apply Z.eqb_eq in Hv. subst v. unfold eff0. sys_nret.
    do 6 zstep. rewrite Z.land_0_r. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 4 step. release_frame FR ST (bv_unsigned sp).
    unfold close_post, close_ret, close_errno. finish.
Qed.
End Sz4.
Lemma close_spec : ltac:(let t := eval cbv delta [close_spec__stmt] in close_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fd errv lo. ltac2:(SecDiet.SzSec.closeP 'close_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x22de0%Z.
Definition ssp_guard := 0x544c8%Z.

Definition open_ret (a : sret) : word :=
  match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
  match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.

Definition open_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (path : list byte) (errv canary : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (open_errno a errv)]
    /\ bytes_at usegs m' P (path ++ [Z_to_bv 8 0])
    /\ rw_cells usegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)]
    /\ rw_cells usegs m' ssp_guard [C8 canary]
    /\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.

Definition open_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (path : list byte) (errv canary : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  bytes_at usegs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
  rw_cells usegs m ssp_guard [C8 canary] ->
  mem_inv usegs m ->
  a1 = Z_to_bv 64 0 (* [comment removed for export] *) ->
  ~ In (Z_to_bv 8 0) path ->
  Namei.path_has_slash path = false -> Fs.path_eqb path Namei.dotdot_path = false ->   (* [comment removed for export] *)
  (lo <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a0)%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= ssp_guard \/ ssp_guard + 8 <= errno_addr tp)%Z ->
  (got_ssp + 8 <= errno_addr tp \/ errno_addr tp + 4 <= got_ssp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (npeek usegs) (enode (NOpen path) dec_open)
       (epost (open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x18cf8) fc None m (seg_rom usegs)).
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path errv canary lo : ltac2:(SecDiet.SzSec.tyM 'open_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma open_spec__body : ltac2:(SecDiet.SzSec.bodyP 'open_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST SRC ERR GOT SSP MI -> NUL NSLASH NDOTDOT LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 TP.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BP. rewrite length_app in BP. cbn [length] in BP.
  apply impl_enode.
  carve_frame 96%nat ST.
  do 18 step. if_false. do 3 step. if_false. do 2 step.
  do 8 step. (* [comment removed for export] *) do 8 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_plain_Some in Hdec.
  destruct ans as [e|fd].
  - destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    do 4 step. if_true. step. rewrite sextw_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    do 3 step. if_false. do 6 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
  - destruct Hdec as (-> & Hfd & Hrange). apply andb_prop in Hfd as [Hfd3 Hfd]. apply Z.leb_le in Hfd3. apply Z.leb_le in Hfd. unfold eff0. sys_nret.
    do 4 step. if_true. step. rewrite sextw_small by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 3 step. if_false. step. rewrite sextw_small by lia. do 5 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
Qed.
End Sz5.
Lemma open_spec : ltac:(let t := eval cbv delta [open_spec__stmt] in open_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path errv canary lo. ltac2:(SecDiet.SzSec.closeP 'open_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_syscalls.

(* [comment removed for export] *)
Module Pcap_iface_pp.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition zbytes (d : list Z) : list byte := map (Z_to_bv 8) d.
Definition zarr (m : mem) (A : Z) (d : list Z) : Prop :=
  bytes_at ssegs m A (zbytes d) /\ wr_at ssegs m A (Z.of_nat (length d)) /\ Forall (fun x => 0 <= x < 256) d.

(* [comment removed for export] *)
Definition pkthdr_cells (ws wu : word) (h : pkthdr) : list cell :=
  [C8 ws; C8 wu; C4 (Z_to_bv 64 (h_caplen h)); C4 (Z_to_bv 64 (h_len h))].

Definition PP_ENTRY : Z := 0x15940.
Definition PP_FRAME : Z := 32.

Definition post_process_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (HA DA : Z) (ws wu : word) (linktype : Z) (swapped : bool) (hdr : pkthdr) (d : list Z) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - PP_FRAME, bv_unsigned sp); (HA + 20, HA + 24); (DA, DA + h_caplen hdr)] m m'
    /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' HA (pkthdr_cells ws wu (fst (pcapint_post_process linktype swapped hdr d)))
    /\ zarr m' DA (snd (pcapint_post_process linktype swapped hdr d)).

Definition post_process_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (HA DA : Z) (ws wu : word) (linktype : Z) (swapped : bool) (hdr : pkthdr) (d : list Z) (lo : Z),
    stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PP_FRAME ->
    rw_cells ssegs m HA (pkthdr_cells ws wu hdr) ->
    zarr m DA d ->
    mem_inv ssegs m ->
    a0 = Z_to_bv 64 linktype -> a1 = Z_to_bv 64 (Z.b2z swapped) -> a2 = Z_to_bv 64 HA -> a3 = Z_to_bv 64 DA ->
    0 <= linktype < 2^31 ->
    0 <= h_caplen hdr <= Z.of_nat (length d) -> Z.of_nat (length d) < 2^31 -> 0 <= h_len hdr < 2^32 ->
    (* [comment removed for export] *)
    (bv_unsigned sp <= HA \/ HA + 24 <= bv_unsigned sp - PP_FRAME) ->
    (HA + 24 <= DA \/ DA + Z.of_nat (length d) <= HA) ->
    DA + Z.of_nat (length d) <= bv_unsigned sp - PP_FRAME ->
    (* [comment removed for export] *)
    HA mod 8 = 0 -> DA mod 4 = 0 -> HA + 24 <= 2^47 -> DA + Z.of_nat (length d) <= 2^47 -> 0 < HA -> 0 < DA ->
    evt ssegs (post_process_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HA DA ws wu linktype swapped hdr d lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PP_ENTRY) fc None m (seg_rom ssegs)).

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition zbytes (d : list Z) : list byte := map (Z_to_bv 8) d.
Definition zarr (m : mem) (A : Z) (d : list Z) : Prop :=
  bytes_at usegs m A (zbytes d) /\ wr_at usegs m A (Z.of_nat (length d)) /\ Forall (fun x => 0 <= x < 256) d.

(* [comment removed for export] *)
Definition pkthdr_cells (ws wu : word) (h : pkthdr) : list cell :=
  [C8 ws; C8 wu; C4 (Z_to_bv 64 (h_caplen h)); C4 (Z_to_bv 64 (h_len h))].

Definition PP_ENTRY : Z := 0x15f44.
Definition PP_FRAME : Z := 32.

Definition post_process_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (HA DA : Z) (ws wu : word) (linktype : Z) (swapped : bool) (hdr : pkthdr) (d : list Z) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - PP_FRAME, bv_unsigned sp); (HA + 20, HA + 24); (DA, DA + h_caplen hdr)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' HA (pkthdr_cells ws wu (fst (pcapint_post_process linktype swapped hdr d)))
    /\ zarr m' DA (snd (pcapint_post_process linktype swapped hdr d)).

Definition post_process_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (HA DA : Z) (ws wu : word) (linktype : Z) (swapped : bool) (hdr : pkthdr) (d : list Z) (lo : Z),
    stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PP_FRAME ->
    rw_cells usegs m HA (pkthdr_cells ws wu hdr) ->
    zarr m DA d ->
    mem_inv usegs m ->
    a0 = Z_to_bv 64 linktype -> a1 = Z_to_bv 64 (Z.b2z swapped) -> a2 = Z_to_bv 64 HA -> a3 = Z_to_bv 64 DA ->
    0 <= linktype < 2^31 ->
    0 <= h_caplen hdr <= Z.of_nat (length d) -> Z.of_nat (length d) < 2^31 -> 0 <= h_len hdr < 2^32 ->
    (* [comment removed for export] *)
    (bv_unsigned sp <= HA \/ HA + 24 <= bv_unsigned sp - PP_FRAME) ->
    (HA + 24 <= DA \/ DA + Z.of_nat (length d) <= HA) ->
    DA + Z.of_nat (length d) <= bv_unsigned sp - PP_FRAME ->
    (* [comment removed for export] *)
    HA mod 8 = 0 -> DA mod 4 = 0 -> HA + 24 <= 2^47 -> DA + Z.of_nat (length d) <= 2^47 -> 0 < HA -> 0 < DA ->
    evt usegs (post_process_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc HA DA ws wu linktype swapped hdr d lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PP_ENTRY) fc None m (seg_rom usegs)).
End TwB.
End Pcap_iface_pp.

(* [comment removed for export] *)
Module PP_kit.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes Image ZBridge ITree Nodes Decode SysStep RegsEquiv ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zbytes_length : forall d, length (zbytes d) = length d.
Proof. intros. unfold zbytes. apply length_map. Qed.

Lemma Forall_range_firstn : forall (P : Z -> Prop) n (d : list Z), Forall P d -> Forall P (firstn n d).
Proof. intros P n d H. rewrite <- (firstn_skipn n d) in H. apply Forall_app in H as [H _]. exact H. Qed.
Lemma Forall_range_skipn : forall (P : Z -> Prop) n (d : list Z), Forall P d -> Forall P (skipn n d).
Proof. intros P n d H. rewrite <- (firstn_skipn n d) in H. apply Forall_app in H as [_ H]. exact H. Qed.
Lemma Forall_rev : forall (P : Z -> Prop) (d : list Z), Forall P d -> Forall P (rev d).
Proof. intros P d H. apply Forall_forall. intros x Hx. apply in_rev in Hx. exact (proj1 (Forall_forall _ _) H x Hx). Qed.

Lemma zslice_length : forall off n (d : list Z), 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length d) ->
  length (zslice off n d) = Z.to_nat n.
Proof. intros. unfold zslice, zfirstn, zskipn. rewrite length_firstn, length_skipn. lia. Qed.

Lemma buf_write_at_length : forall off l (d : list Z), 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
  length (buf_write_at off l d) = length d.
Proof.
  intros. unfold buf_write_at, zfirstn, zskipn, zlength. rewrite !length_app, length_firstn, length_skipn. lia.
Qed.

Lemma buf_write_at_range : forall off l (d : list Z),
  Forall (fun x => 0 <= x < 256) d -> Forall (fun x => 0 <= x < 256) l -> Forall (fun x => 0 <= x < 256) (buf_write_at off l d).
Proof.
  intros. unfold buf_write_at, zfirstn, zskipn. apply Forall_app. split; [apply Forall_range_firstn; assumption|].
  apply Forall_app. split; [assumption| apply Forall_range_skipn; assumption].
Qed.

Lemma swap_field_length : forall k off (d : list Z), 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) ->
  length (swap_field k off d) = length d.
Proof.
  intros. unfold swap_field. apply buf_write_at_length; [lia|]. rewrite length_rev, zslice_length by lia. lia.
Qed.

Lemma swap_field_range : forall k off (d : list Z),
  Forall (fun x => 0 <= x < 256) d -> Forall (fun x => 0 <= x < 256) (swap_field k off d).
Proof.
  intros. unfold swap_field. apply buf_write_at_range; [assumption|]. apply Forall_rev. unfold zslice, zfirstn, zskipn.
  apply Forall_range_firstn. apply Forall_range_skipn. assumption.
Qed.

(* [comment removed for export] *)
Lemma zslice_4 : forall off (d : list Z), 0 <= off -> off + 4 <= Z.of_nat (length d) ->
  exists x0 x1 x2 x3, zslice off 4 d = [x0; x1; x2; x3].
Proof.
  intros off d Ho Hl. pose proof (zslice_length off 4 d Ho ltac:(lia) Hl) as L.
  destruct (zslice off 4 d) as [|x0 [|x1 [|x2 [|x3 [|]]]]]; cbn in L; try lia. repeat eexists.
Qed.
Lemma zslice_2 : forall off (d : list Z), 0 <= off -> off + 2 <= Z.of_nat (length d) ->
  exists x0 x1, zslice off 2 d = [x0; x1].
Proof.
  intros off d Ho Hl. pose proof (zslice_length off 2 d Ho ltac:(lia) Hl) as L.
  destruct (zslice off 2 d) as [|x0 [|x1 [|]]]; cbn in L; try lia. repeat eexists.
Qed.

Lemma zslice_range : forall off n (d : list Z), Forall (fun x => 0 <= x < 256) d -> Forall (fun x => 0 <= x < 256) (zslice off n d).
Proof. intros. unfold zslice, zfirstn, zskipn. apply Forall_range_firstn. apply Forall_range_skipn. assumption. Qed.

(* [comment removed for export] *)
Lemma znth_slice : forall (d : list Z) off n j, 0 <= off -> 0 <= j < n -> off + n <= Z.of_nat (length d) ->
  nth_error (zslice off n d) (Z.to_nat j) = Some (znth d (off + j)).
Proof.
  intros d off n j Ho Hj Hl. unfold zslice, zfirstn, zskipn.
  rewrite (nth_error_nth' _ 0).
  2:{ rewrite length_firstn, length_skipn. lia. }
  f_equal. rewrite nth_firstn. replace (Z.to_nat j <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_skipn. unfold znth.
  replace (off + j <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  f_equal. lia.
Qed.

Lemma get_u8_of_slice4 : forall off d x0 x1 x2 x3, 0 <= off -> off + 4 <= Z.of_nat (length d) ->
  zslice off 4 d = [x0; x1; x2; x3] ->
  get_u8 d off = x0 /\ get_u8 d (off + 1) = x1 /\ get_u8 d (off + 2) = x2 /\ get_u8 d (off + 3) = x3.
Proof.
  intros off d x0 x1 x2 x3 Ho Hl E. unfold get_u8.
  pose proof (znth_slice d off 4 0 Ho ltac:(lia) Hl) as E0. change (Z.to_nat 0) with 0%nat in E0.
  pose proof (znth_slice d off 4 1 Ho ltac:(lia) Hl) as E1. change (Z.to_nat 1) with 1%nat in E1.
  pose proof (znth_slice d off 4 2 Ho ltac:(lia) Hl) as E2. change (Z.to_nat 2) with 2%nat in E2.
  pose proof (znth_slice d off 4 3 Ho ltac:(lia) Hl) as E3. change (Z.to_nat 3) with 3%nat in E3.
  rewrite E in E0, E1, E2, E3. cbn [nth_error] in E0, E1, E2, E3. rewrite Z.add_0_r in E0.
  injection E0 as <-. injection E1 as <-. injection E2 as <-. injection E3 as <-. repeat split; reflexivity.
Qed.
Lemma get_u8_of_slice2 : forall off d x0 x1, 0 <= off -> off + 2 <= Z.of_nat (length d) ->
  zslice off 2 d = [x0; x1] -> get_u8 d off = x0 /\ get_u8 d (off + 1) = x1.
Proof.
  intros off d x0 x1 Ho Hl E. unfold get_u8.
  pose proof (znth_slice d off 2 0 Ho ltac:(lia) Hl) as E0. change (Z.to_nat 0) with 0%nat in E0.
  pose proof (znth_slice d off 2 1 Ho ltac:(lia) Hl) as E1. change (Z.to_nat 1) with 1%nat in E1.
  rewrite E in E0, E1. cbn [nth_error] in E0, E1. rewrite Z.add_0_r in E0.
  injection E0 as <-. injection E1 as <-. split; reflexivity.
Qed.
Lemma get_u8_single : forall off d, 0 <= off -> off + 1 <= Z.of_nat (length d) -> zslice off 1 d = [get_u8 d off].
Proof.
  intros off d Ho Hl. pose proof (zslice_length off 1 d Ho ltac:(lia) Hl) as L.
  pose proof (znth_slice d off 1 0 Ho ltac:(lia) Hl) as E0. change (Z.to_nat 0) with 0%nat in E0.
  destruct (zslice off 1 d) as [|y [|]]; cbn in L; try lia. cbn [nth_error] in E0. rewrite Z.add_0_r in E0. unfold get_u8. injection E0 as ->. reflexivity.
Qed.

Lemma get_le32_of_slice : forall off d x0 x1 x2 x3, zslice off 4 d = [x0; x1; x2; x3] ->
  get_le32 d off = x0 + 256 * x1 + 65536 * x2 + 16777216 * x3.
Proof. intros off d x0 x1 x2 x3 E. unfold get_le32. rewrite E. cbn. lia. Qed.
Lemma get_le16_of_slice : forall off d x0 x1, zslice off 2 d = [x0; x1] -> get_le16 d off = x0 + 256 * x1.
Proof. intros off d x0 x1 E. unfold get_le16. rewrite E. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZA.
  Notation segs := ssegs.

  #[using="Type"] Lemma zarr_bound : forall m A d, zarr m A d -> 0 <= A /\ A + Z.of_nat (length d) <= 2^64.
  Proof. intros m A d (B & _ & _). apply bytes_at_bound in B. rewrite zbytes_length in B. exact B. Qed.

  #[using="Type"] Lemma zarr_read_raw : forall m A d off n, zarr m A d -> 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) (Z.to_nat n) = Some (zbytes (zslice off n d)).
  Proof.
    intros m A d off n (B & _ & _) Ho Hn Hl.
    rewrite (bytes_at_read segs m A (zbytes d) off (Z.to_nat n) B) by (rewrite ?zbytes_length; lia).
    unfold zslice, zfirstn, zskipn, zbytes. rewrite skipn_map, firstn_map. reflexivity.
  Qed.

  #[using="Type"] Lemma zb_eq : forall a b, a mod 256 = b mod 256 -> Z_to_bv 8 a = Z_to_bv 8 b.
  Proof. intros a b E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact E. Qed.

  #[using="Type"] Lemma le4_zbytes : forall x0 x1 x2 x3, 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
    le4 (Z_to_bv 64 (x0 + 256 * x1 + 65536 * x2 + 16777216 * x3)) = zbytes [x0; x1; x2; x3].
  Proof.
    intros. unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
    cbn [Z_to_le_bytes zbytes map]. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal. apply zb_eq; Z.div_mod_to_equations; lia.
  Qed.

  #[using="Type"] Lemma le2_zbytes : forall x0 x1, 0 <= x0 < 256 -> 0 <= x1 < 256 ->
    le2 (Z_to_bv 64 (x0 + 256 * x1)) = zbytes [x0; x1].
  Proof.
    intros. unfold le2. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
    cbn [Z_to_le_bytes zbytes map]. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal. apply zb_eq; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma zarr_read4 : forall m A d off, zarr m A d -> 0 <= off -> off + 4 <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) 4 = Some (le4 (Z_to_bv 64 (get_le32 d off))) /\ 0 <= get_le32 d off < 2^32.
  Proof.
    intros m A d off ZA Ho Hl.
    destruct (zslice_4 off d Ho Hl) as (x0 & x1 & x2 & x3 & E).
    pose proof (zslice_range off 4 d (proj2 (proj2 ZA))) as R. rewrite E in R.
    apply Forall_cons_iff in R as [R0 R]. apply Forall_cons_iff in R as [R1 R]. apply Forall_cons_iff in R as [R2 R]. apply Forall_cons_iff in R as [R3 _].
    rewrite (get_le32_of_slice _ _ _ _ _ _ E). split; [|lia].
    rewrite (le4_zbytes x0 x1 x2 x3) by lia. rewrite <- E. change 4%nat with (Z.to_nat 4). apply zarr_read_raw; [exact ZA|lia|lia|lia].
  Qed.

  #[using="Type"] Lemma zarr_read2 : forall m A d off, zarr m A d -> 0 <= off -> off + 2 <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) 2 = Some (le2 (Z_to_bv 64 (get_le16 d off))) /\ 0 <= get_le16 d off < 65536.
  Proof.
    intros m A d off ZA Ho Hl.
    destruct (zslice_2 off d Ho Hl) as (x0 & x1 & E).
    pose proof (zslice_range off 2 d (proj2 (proj2 ZA))) as R. rewrite E in R.
    apply Forall_cons_iff in R as [R0 R]. apply Forall_cons_iff in R as [R1 _].
    rewrite (get_le16_of_slice _ _ _ _ E). split; [|lia].
    rewrite (le2_zbytes x0 x1) by lia. rewrite <- E. change 2%nat with (Z.to_nat 2). apply zarr_read_raw; [exact ZA|lia|lia|lia].
  Qed.

  #[using="Type"] Lemma zarr_read1 : forall m A d off, zarr m A d -> 0 <= off -> off + 1 <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) 1 = Some [Z_to_bv 8 (get_u8 d off)] /\ 0 <= get_u8 d off < 256.
  Proof.
    intros m A d off ZA Ho Hl. split.
    - change 1%nat with (Z.to_nat 1). rewrite (zarr_read_raw m A d off 1 ZA) by lia. rewrite (get_u8_single off d) by lia. reflexivity.
    - pose proof (zslice_range off 1 d (proj2 (proj2 ZA))) as R. rewrite (get_u8_single off d) in R by lia. apply Forall_cons_iff in R as [R _]. exact R.
  Qed.

  #[using="Type"] Lemma zarr_store_ok : forall m A d off n a, zarr m A d -> 0 <= off -> off + Z.of_nat n <= Z.of_nat (length d) -> a = wa (A + off) ->
    store_ok segs m a n = true.
  Proof. intros m A d off n a (_ & W & _) Ho Hl ->. eapply wr_at_store_ok; [exact W| lia | lia]. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma zarr_write : forall m A d off l, zarr m A d -> 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
    Forall (fun x => 0 <= x < 256) l ->
    zarr (write_to_mem m (wa (A + off)) (zbytes l)) A (buf_write_at off l d).
  Proof.
    intros m A d off l (B & W & R) Ho Hl Rl. split; [|split].
    - pose proof (bytes_at_write_inside segs m A (zbytes d) off (zbytes l) B Ho ltac:(rewrite !zbytes_length; lia)) as B'.
      eapply bytes_at_ext; [exact B'|]. unfold upd_bytes, buf_write_at, zbytes, zfirstn, zskipn, zlength.
      rewrite map_app, map_app, firstn_map, skipn_map, length_map. do 2 f_equal. f_equal. f_equal. lia.
    - rewrite buf_write_at_length by lia. apply wr_at_write. exact W.
    - apply buf_write_at_range; assumption.
  Qed.

  #[using="Type"] Lemma zarr_mem_inv : forall m A d off l, zarr m A d -> mem_inv segs m -> 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
    mem_inv segs (write_to_mem m (wa (A + off)) (zbytes l)).
  Proof.
    intros m A d off l ZA MI Ho Hl. apply mem_inv_store; [exact MI|]. rewrite zbytes_length.
    eapply zarr_store_ok; [exact ZA| exact Ho| exact Hl| reflexivity].
  Qed.
End ZA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sx32_small : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold sx32. f_equal. rewrite unsigned_lit by lia. rewrite bv_swrap32_eq.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma zx32_small : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.
Lemma zx16_small : forall x, 0 <= x < 2^16 -> zx16 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx16. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.
Lemma zxb_small : forall x, 0 <= x < 256 -> zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply Z.mod_small. exact Hx. Qed.
Lemma sxb_small : forall x, 0 <= x < 256 -> sxb (Z_to_bv 8 x) = Z_to_bv 64 (if x <? 128 then x else x - 256).
Proof.
  intros x Hx. unfold sxb. f_equal. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 8) with 8. change (2^8) with 256. cbn [Z.div Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  destruct (Z.ltb_spec x 128); Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ltu_falseZ : forall x y, 0 <= y <= x -> x < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_trueZ : forall x y, 0 <= x < y -> y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_lt. lia. Qed.
Lemma eqb_falseZ : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> x <> y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.
Lemma eqb_trueZ : forall x y, x = y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros x y ->. unfold bv_eqb. apply Z.eqb_refl. Qed.
Lemma signed_small : forall x, 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 64) with 64. change (2^64 `div` 2) with (2^63). rewrite (Z.mod_small x) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma lts_falseZ : forall x y, 0 <= y <= x -> x < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros. unfold bv_lts. rewrite !signed_small by lia. apply Z.ltb_ge. lia. Qed.
Lemma lts_trueZ : forall x y, 0 <= x < y -> y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros. unfold bv_lts. rewrite !signed_small by lia. apply Z.ltb_lt. lia. Qed.

(* [comment removed for export] *)
Lemma unsigned_sx32 : forall x, 0 <= x < 2^32 ->
  bv_unsigned (sx32 (Z_to_bv 64 x)) = (if x <? 2^31 then x else x + 2^64 - 2^32).
Proof.
  intros x Hx. unfold sx32. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  destruct (Z.ltb_spec x (2^31)).
  - rewrite (Z.mod_small (x + 2^31)) by lia. rewrite Z.mod_small by lia. lia.
  - replace ((x + 2 ^ 31) mod 2 ^ 32) with (x + 2^31 - 2^32) by (Z.div_mod_to_equations; lia).
    Z.div_mod_to_equations. lia.
Qed.
Lemma ltu_sx32_lit : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 ->
  bv_ltu (sx32 (Z_to_bv 64 x)) (Z_to_bv 64 k) = (x <? k).
Proof.
  intros x k Hx Hk. rewrite bv_ltu_Z, unsigned_sx32, (unsigned_lit k) by lia.
  destruct (Z.ltb_spec x (2^31)); destruct (Z.ltb_spec x k); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]).
Qed.

(* [comment removed for export] *)
Lemma lor_be16 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z.lor ((Z.shiftl a 8) mod 2^64) b = a * 256 + b.
Proof.
  intros a b Ha Hb. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. rewrite Z.mod_small by lia.
  rewrite (lor_add (a * 256) b 8); [lia| lia | change (2^8) with 256; lia |]. change (2^8) with 256. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma ltu_minus12 : forall p, 0 <= p < 65536 ->
  bv_ltu (Z_to_bv 64 (p + -12)) (Z_to_bv 64 2) = ((p =? 12) || (p =? 13))%bool.
Proof.
  intros p Hp. rewrite bv_ltu_Z, (unsigned_lit 2), unsigned_lit_wrap by lia.
  destruct (Z.eqb_spec p 12) as [->|N1]; [reflexivity|]. destruct (Z.eqb_spec p 13) as [->|N2]; [reflexivity|]. cbn [orb].
  apply Z.ltb_ge. destruct (Z_lt_le_dec p 12).
  - replace ((p + -12) mod 2^64) with (p + -12 + 2^64) by (Z.div_mod_to_equations; lia). lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma swrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_period : forall x k, bv_swrap 32 (x + k * 2^32) = bv_swrap 32 x.
Proof. intros. rewrite !bv_swrap32_eq. f_equal. replace (x + k * 2^32 + 2^31) with (x + 2^31 + k * 2^32) by lia. apply Z.mod_add. lia. Qed.
Lemma swrap_of_sx32 : forall x k, 0 <= x < 2^32 -> bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 x)) + k) = bv_swrap 32 (x + k).
Proof.
  intros x k Hx. rewrite unsigned_sx32 by lia. destruct (Z.ltb_spec x (2^31)); [reflexivity|].
  replace (x + 2^64 - 2^32 + k) with (x + k + (2^32 - 1) * 2^32) by lia. apply swrap32_period.
Qed.
Lemma sx32_swrap : forall x, 0 <= x < 2^32 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 (bv_swrap 32 x).
Proof. intros. unfold sx32. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma unsigned_swrap32 : forall x, bv_unsigned (Z_to_bv 64 (bv_swrap 32 x)) = (if x mod 2^32 <? 2^31 then x mod 2^32 else x mod 2^32 + 2^64 - 2^32).
Proof.
  intros x. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  replace ((x + 2^31) mod 2^32) with ((x mod 2^32 + 2^31) mod 2^32) by (Z.div_mod_to_equations; nia || lia).
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)) as R. set (y := x mod 2^32) in *.
  destruct (Z.ltb_spec y (2^31)).
  - rewrite (Z.mod_small (y + 2^31)) by lia. rewrite Z.mod_small by lia. lia.
  - replace ((y + 2^31) mod 2^32) with (y + 2^31 - 2^32) by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.
Lemma ltu_swrap_lit : forall x k, 0 <= k < 2^31 ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = (x mod 2^32 <? k).
Proof.
  intros x k Hk. rewrite bv_ltu_Z, unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)) as R.
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); destruct (Z.ltb_spec (x mod 2^32) k); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]).
Qed.

Lemma ltu_swrap_falseZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> k <= x ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = false.
Proof. intros. rewrite ltu_swrap_lit by lia. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_swrap_trueZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> x < k ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = true.
Proof. intros. rewrite ltu_swrap_lit by lia. rewrite Z.mod_small by lia. apply Z.ltb_lt. lia. Qed.
Lemma ltu_sx32_falseZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> k <= x ->
  bv_ltu (sx32 (Z_to_bv 64 x)) (Z_to_bv 64 k) = false.
Proof. intros. rewrite ltu_sx32_lit by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_sx32_trueZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> x < k ->
  bv_ltu (sx32 (Z_to_bv 64 x)) (Z_to_bv 64 k) = true.
Proof. intros. rewrite ltu_sx32_lit by lia. apply Z.ltb_lt. lia. Qed.

Ltac cond_side :=
  fastfirst (first [ noevar_assumption | apply ltu_falseZ; lia | apply ltu_trueZ; lia | apply eqb_falseZ; lia | apply eqb_trueZ; lia
        | apply lts_falseZ; lia | apply lts_trueZ; lia
        | apply ltu_swrap_falseZ; lia | apply ltu_swrap_trueZ; lia | apply ltu_sx32_falseZ; lia | apply ltu_sx32_trueZ; lia
        | apply (proj2 (Bool.negb_false_iff _)); cond_side_t
        | apply (proj2 (Bool.negb_true_iff _)); cond_side ])
with cond_side_t :=
  fastfirst (first [ noevar_assumption | apply ltu_trueZ; lia | apply eqb_trueZ; lia | apply lts_trueZ; lia
        | apply ltu_swrap_trueZ; lia | apply ltu_sx32_trueZ; lia
        | apply (proj2 (Bool.negb_true_iff _)); cond_side ]).
(* [comment removed for export] *)
Ltac bfalse :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with false; [cbv iota| symmetry; cond_side] end.
Ltac btrue :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with true; [cbv iota| symmetry; cond_side_t] end.
(* [comment removed for export] *)
Ltac bstep := lstep; try (lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [bfalse | btrue] end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_mask8 : forall y k, 0 <= y -> 0 <= k -> Z.land y (255 * 2^k) = ((y / 2^k) mod 256) * 2^k.
Proof.
  intros y k Hy Hk. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec.
  replace (255 * 2^k) with (Z.shiftl (Z.ones 8) k) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  replace ((y / 2^k) mod 256 * 2^k) with (Z.shiftl ((Z.shiftr y k) mod 2^8) k)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
  destruct (Z_lt_le_dec n k).
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia.
    destruct (Z_lt_le_dec (n - k) 8).
    + rewrite Z.ones_spec_low, Z.mod_pow2_bits_low, Z.shiftr_spec by lia. rewrite Bool.andb_true_r. f_equal. lia.
    + rewrite Z.ones_spec_high, Z.mod_pow2_bits_high by lia. apply Bool.andb_false_r.
Qed.

Lemma land_65280 : forall y, 0 <= y -> Z.land y 65280 = ((y / 256) mod 256) * 256.
Proof. intros. change 65280 with (255 * 2^8). rewrite land_mask8 by lia. reflexivity. Qed.
Lemma land_16711680 : forall y, 0 <= y -> Z.land y 16711680 = ((y / 65536) mod 256) * 65536.
Proof. intros. change 16711680 with (255 * 2^16). rewrite land_mask8 by lia. reflexivity. Qed.



Lemma sx32_mod32 : forall x, 0 <= x < 2^32 -> bv_unsigned (sx32 (Z_to_bv 64 x)) mod 2^32 = x.
Proof.
  intros x Hx. rewrite unsigned_sx32 by lia. destruct (Z.ltb_spec x (2^31)).
  - apply Z.mod_small. lia.
  - Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma le4_bswap32 : forall X x0 x1 x2 x3,
  0 <= X < 2^64 -> 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  X mod 2^32 = x0 + 256 * x1 + 65536 * x2 + 16777216 * x3 ->
  le4 (Z_to_bv 64 (Z.lor (Z.lor ((Z.shiftl X 24) mod 18446744073709551616) ((Z.shiftl (Z.land X 65280) 8) mod 18446744073709551616))
                           (Z.lor (Z.land (Z.shiftr X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 X) 24)) mod 18446744073709551616))))
  = zbytes [x3; x2; x1; x0].
Proof.
  intros X x0 x1 x2 x3 HX H0 H1 H2 H3 HV.
  rewrite bv_wrap32_eq.
  rewrite !land_65280 by (try apply Z.shiftr_nonneg; lia).
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  assert (E1 : (X / 256) mod 256 = x1) by (Z.div_mod_to_equations; lia).
  assert (E2 : (X / 2^8 / 256) mod 256 = x2) by (Z.div_mod_to_equations; lia).
  assert (E3 : X mod 2^32 / 2^24 = x3) by (Z.div_mod_to_equations; lia).
  rewrite E1, E2, E3. rewrite (swrap32_small x3) by lia.
  rewrite (Z.mod_small x3) by lia.
  rewrite (Z.mod_small (x1 * 256 * 2^8)) by lia.
  rewrite (lor_add (x2 * 256) x3 8) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (lor_add ((X * 2^24) mod 18446744073709551616) (x1 * 256 * 2^8) 24) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (lor_add _ (x2 * 256 + x3) 16) by (try lia; Z.div_mod_to_equations; lia).
  apply le4_of_mod32; [reflexivity|]. cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2^64). change (bv_modulus 8) with 256.
  rewrite !(Z.mod_small _ 256) by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma word_range : forall w : word, 0 <= bv_unsigned w < 2^64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma le2_of_mod16 : forall (v : word) (bs : list byte), length bs = 2%nat ->
  bv_unsigned v mod 2^16 = le_val (map bv_unsigned bs) -> le2 v = bs.
Proof.
  intros v bs Hl Hv. unfold le2.
  rewrite <- (Z_to_le_bytes_mod 2 _ 16) by (cbn; lia). change (2 ^ 16) with (2^16) in *. rewrite Hv.
  rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma le2_bswap16 : forall X x0 x1, 0 <= x0 < 256 -> 0 <= x1 < 256 -> X = x0 + 256 * x1 ->
  le2 (Z_to_bv 64 (Z.lor ((Z.shiftl X 8) mod 18446744073709551616) (Z.shiftr X 8))) = zbytes [x1; x0].
Proof.
  intros X x0 x1 H0 H1 ->.
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  replace ((x0 + 256 * x1) / 256) with x1 by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small _ 18446744073709551616) by lia.
  rewrite (lor_add ((x0 + 256 * x1) * 256) x1 8); [| lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia].
  apply le2_of_mod16; [reflexivity|]. cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2^64). change (bv_modulus 8) with 256.
  rewrite !(Z.mod_small _ 256) by lia. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.RegsEquiv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zbytes_length : forall d, length (zbytes d) = length d.
Proof. intros. unfold zbytes. apply length_map. Qed.

Lemma Forall_range_firstn : forall (P : Z -> Prop) n (d : list Z), Forall P d -> Forall P (firstn n d).
Proof. intros P n d H. rewrite <- (firstn_skipn n d) in H. apply Forall_app in H as [H _]. exact H. Qed.
Lemma Forall_range_skipn : forall (P : Z -> Prop) n (d : list Z), Forall P d -> Forall P (skipn n d).
Proof. intros P n d H. rewrite <- (firstn_skipn n d) in H. apply Forall_app in H as [_ H]. exact H. Qed.
Lemma Forall_rev : forall (P : Z -> Prop) (d : list Z), Forall P d -> Forall P (rev d).
Proof. intros P d H. apply Forall_forall. intros x Hx. apply in_rev in Hx. exact (proj1 (Forall_forall _ _) H x Hx). Qed.

Lemma zslice_length : forall off n (d : list Z), 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length d) ->
  length (zslice off n d) = Z.to_nat n.
Proof. intros. unfold zslice, zfirstn, zskipn. rewrite length_firstn, length_skipn. lia. Qed.

Lemma buf_write_at_length : forall off l (d : list Z), 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
  length (buf_write_at off l d) = length d.
Proof.
  intros. unfold buf_write_at, zfirstn, zskipn, zlength. rewrite !length_app, length_firstn, length_skipn. lia.
Qed.

Lemma buf_write_at_range : forall off l (d : list Z),
  Forall (fun x => 0 <= x < 256) d -> Forall (fun x => 0 <= x < 256) l -> Forall (fun x => 0 <= x < 256) (buf_write_at off l d).
Proof.
  intros. unfold buf_write_at, zfirstn, zskipn. apply Forall_app. split; [apply Forall_range_firstn; assumption|].
  apply Forall_app. split; [assumption| apply Forall_range_skipn; assumption].
Qed.

Lemma swap_field_length : forall k off (d : list Z), 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) ->
  length (swap_field k off d) = length d.
Proof.
  intros. unfold swap_field. apply buf_write_at_length; [lia|]. rewrite length_rev, zslice_length by lia. lia.
Qed.

Lemma swap_field_range : forall k off (d : list Z),
  Forall (fun x => 0 <= x < 256) d -> Forall (fun x => 0 <= x < 256) (swap_field k off d).
Proof.
  intros. unfold swap_field. apply buf_write_at_range; [assumption|]. apply Forall_rev. unfold zslice, zfirstn, zskipn.
  apply Forall_range_firstn. apply Forall_range_skipn. assumption.
Qed.

(* [comment removed for export] *)
Lemma zslice_4 : forall off (d : list Z), 0 <= off -> off + 4 <= Z.of_nat (length d) ->
  exists x0 x1 x2 x3, zslice off 4 d = [x0; x1; x2; x3].
Proof.
  intros off d Ho Hl. pose proof (zslice_length off 4 d Ho ltac:(lia) Hl) as L.
  destruct (zslice off 4 d) as [|x0 [|x1 [|x2 [|x3 [|]]]]]; cbn in L; try lia. repeat eexists.
Qed.
Lemma zslice_2 : forall off (d : list Z), 0 <= off -> off + 2 <= Z.of_nat (length d) ->
  exists x0 x1, zslice off 2 d = [x0; x1].
Proof.
  intros off d Ho Hl. pose proof (zslice_length off 2 d Ho ltac:(lia) Hl) as L.
  destruct (zslice off 2 d) as [|x0 [|x1 [|]]]; cbn in L; try lia. repeat eexists.
Qed.

Lemma zslice_range : forall off n (d : list Z), Forall (fun x => 0 <= x < 256) d -> Forall (fun x => 0 <= x < 256) (zslice off n d).
Proof. intros. unfold zslice, zfirstn, zskipn. apply Forall_range_firstn. apply Forall_range_skipn. assumption. Qed.

(* [comment removed for export] *)
Lemma znth_slice : forall (d : list Z) off n j, 0 <= off -> 0 <= j < n -> off + n <= Z.of_nat (length d) ->
  nth_error (zslice off n d) (Z.to_nat j) = Some (znth d (off + j)).
Proof.
  intros d off n j Ho Hj Hl. unfold zslice, zfirstn, zskipn.
  rewrite (nth_error_nth' _ 0).
  2:{ rewrite length_firstn, length_skipn. lia. }
  f_equal. rewrite nth_firstn. replace (Z.to_nat j <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_skipn. unfold znth.
  replace (off + j <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  f_equal. lia.
Qed.

Lemma get_u8_of_slice4 : forall off d x0 x1 x2 x3, 0 <= off -> off + 4 <= Z.of_nat (length d) ->
  zslice off 4 d = [x0; x1; x2; x3] ->
  get_u8 d off = x0 /\ get_u8 d (off + 1) = x1 /\ get_u8 d (off + 2) = x2 /\ get_u8 d (off + 3) = x3.
Proof.
  intros off d x0 x1 x2 x3 Ho Hl E. unfold get_u8.
  pose proof (znth_slice d off 4 0 Ho ltac:(lia) Hl) as E0. change (Z.to_nat 0) with 0%nat in E0.
  pose proof (znth_slice d off 4 1 Ho ltac:(lia) Hl) as E1. change (Z.to_nat 1) with 1%nat in E1.
  pose proof (znth_slice d off 4 2 Ho ltac:(lia) Hl) as E2. change (Z.to_nat 2) with 2%nat in E2.
  pose proof (znth_slice d off 4 3 Ho ltac:(lia) Hl) as E3. change (Z.to_nat 3) with 3%nat in E3.
  rewrite E in E0, E1, E2, E3. cbn [nth_error] in E0, E1, E2, E3. rewrite Z.add_0_r in E0.
  injection E0 as <-. injection E1 as <-. injection E2 as <-. injection E3 as <-. repeat split; reflexivity.
Qed.
Lemma get_u8_of_slice2 : forall off d x0 x1, 0 <= off -> off + 2 <= Z.of_nat (length d) ->
  zslice off 2 d = [x0; x1] -> get_u8 d off = x0 /\ get_u8 d (off + 1) = x1.
Proof.
  intros off d x0 x1 Ho Hl E. unfold get_u8.
  pose proof (znth_slice d off 2 0 Ho ltac:(lia) Hl) as E0. change (Z.to_nat 0) with 0%nat in E0.
  pose proof (znth_slice d off 2 1 Ho ltac:(lia) Hl) as E1. change (Z.to_nat 1) with 1%nat in E1.
  rewrite E in E0, E1. cbn [nth_error] in E0, E1. rewrite Z.add_0_r in E0.
  injection E0 as <-. injection E1 as <-. split; reflexivity.
Qed.
Lemma get_u8_single : forall off d, 0 <= off -> off + 1 <= Z.of_nat (length d) -> zslice off 1 d = [get_u8 d off].
Proof.
  intros off d Ho Hl. pose proof (zslice_length off 1 d Ho ltac:(lia) Hl) as L.
  pose proof (znth_slice d off 1 0 Ho ltac:(lia) Hl) as E0. change (Z.to_nat 0) with 0%nat in E0.
  destruct (zslice off 1 d) as [|y [|]]; cbn in L; try lia. cbn [nth_error] in E0. rewrite Z.add_0_r in E0. unfold get_u8. injection E0 as ->. reflexivity.
Qed.

Lemma get_le32_of_slice : forall off d x0 x1 x2 x3, zslice off 4 d = [x0; x1; x2; x3] ->
  get_le32 d off = x0 + 256 * x1 + 65536 * x2 + 16777216 * x3.
Proof. intros off d x0 x1 x2 x3 E. unfold get_le32. rewrite E. cbn. lia. Qed.
Lemma get_le16_of_slice : forall off d x0 x1, zslice off 2 d = [x0; x1] -> get_le16 d off = x0 + 256 * x1.
Proof. intros off d x0 x1 E. unfold get_le16. rewrite E. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZA.
  Notation segs := usegs.

  #[using="Type"] Lemma zarr_bound : forall m A d, zarr m A d -> 0 <= A /\ A + Z.of_nat (length d) <= 2^64.
  Proof. intros m A d (B & _ & _). apply bytes_at_bound in B. rewrite zbytes_length in B. exact B. Qed.

  #[using="Type"] Lemma zarr_read_raw : forall m A d off n, zarr m A d -> 0 <= off -> 0 <= n -> off + n <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) (Z.to_nat n) = Some (zbytes (zslice off n d)).
  Proof.
    intros m A d off n (B & _ & _) Ho Hn Hl.
    rewrite (bytes_at_read segs m A (zbytes d) off (Z.to_nat n) B) by (rewrite ?zbytes_length; lia).
    unfold zslice, zfirstn, zskipn, zbytes. rewrite skipn_map, firstn_map. reflexivity.
  Qed.

  #[using="Type"] Lemma zb_eq : forall a b, a mod 256 = b mod 256 -> Z_to_bv 8 a = Z_to_bv 8 b.
  Proof. intros a b E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact E. Qed.

  #[using="Type"] Lemma le4_zbytes : forall x0 x1 x2 x3, 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
    le4 (Z_to_bv 64 (x0 + 256 * x1 + 65536 * x2 + 16777216 * x3)) = zbytes [x0; x1; x2; x3].
  Proof.
    intros. unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
    cbn [Z_to_le_bytes zbytes map]. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal. apply zb_eq; Z.div_mod_to_equations; lia.
  Qed.

  #[using="Type"] Lemma le2_zbytes : forall x0 x1, 0 <= x0 < 256 -> 0 <= x1 < 256 ->
    le2 (Z_to_bv 64 (x0 + 256 * x1)) = zbytes [x0; x1].
  Proof.
    intros. unfold le2. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
    cbn [Z_to_le_bytes zbytes map]. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    f_equal; [apply zb_eq; Z.div_mod_to_equations; lia|].
    f_equal. apply zb_eq; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma zarr_read4 : forall m A d off, zarr m A d -> 0 <= off -> off + 4 <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) 4 = Some (le4 (Z_to_bv 64 (get_le32 d off))) /\ 0 <= get_le32 d off < 2^32.
  Proof.
    intros m A d off ZA Ho Hl.
    destruct (zslice_4 off d Ho Hl) as (x0 & x1 & x2 & x3 & E).
    pose proof (zslice_range off 4 d (proj2 (proj2 ZA))) as R. rewrite E in R.
    apply Forall_cons_iff in R as [R0 R]. apply Forall_cons_iff in R as [R1 R]. apply Forall_cons_iff in R as [R2 R]. apply Forall_cons_iff in R as [R3 _].
    rewrite (get_le32_of_slice _ _ _ _ _ _ E). split; [|lia].
    rewrite (le4_zbytes x0 x1 x2 x3) by lia. rewrite <- E. change 4%nat with (Z.to_nat 4). apply zarr_read_raw; [exact ZA|lia|lia|lia].
  Qed.

  #[using="Type"] Lemma zarr_read2 : forall m A d off, zarr m A d -> 0 <= off -> off + 2 <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) 2 = Some (le2 (Z_to_bv 64 (get_le16 d off))) /\ 0 <= get_le16 d off < 65536.
  Proof.
    intros m A d off ZA Ho Hl.
    destruct (zslice_2 off d Ho Hl) as (x0 & x1 & E).
    pose proof (zslice_range off 2 d (proj2 (proj2 ZA))) as R. rewrite E in R.
    apply Forall_cons_iff in R as [R0 R]. apply Forall_cons_iff in R as [R1 _].
    rewrite (get_le16_of_slice _ _ _ _ E). split; [|lia].
    rewrite (le2_zbytes x0 x1) by lia. rewrite <- E. change 2%nat with (Z.to_nat 2). apply zarr_read_raw; [exact ZA|lia|lia|lia].
  Qed.

  #[using="Type"] Lemma zarr_read1 : forall m A d off, zarr m A d -> 0 <= off -> off + 1 <= Z.of_nat (length d) ->
    ov_read_bytes segs m (wa (A + off)) 1 = Some [Z_to_bv 8 (get_u8 d off)] /\ 0 <= get_u8 d off < 256.
  Proof.
    intros m A d off ZA Ho Hl. split.
    - change 1%nat with (Z.to_nat 1). rewrite (zarr_read_raw m A d off 1 ZA) by lia. rewrite (get_u8_single off d) by lia. reflexivity.
    - pose proof (zslice_range off 1 d (proj2 (proj2 ZA))) as R. rewrite (get_u8_single off d) in R by lia. apply Forall_cons_iff in R as [R _]. exact R.
  Qed.

  #[using="Type"] Lemma zarr_store_ok : forall m A d off n a, zarr m A d -> 0 <= off -> off + Z.of_nat n <= Z.of_nat (length d) -> a = wa (A + off) ->
    store_ok segs m a n = true.
  Proof. intros m A d off n a (_ & W & _) Ho Hl ->. eapply wr_at_store_ok; [exact W| lia | lia]. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma zarr_write : forall m A d off l, zarr m A d -> 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
    Forall (fun x => 0 <= x < 256) l ->
    zarr (write_to_mem m (wa (A + off)) (zbytes l)) A (buf_write_at off l d).
  Proof.
    intros m A d off l (B & W & R) Ho Hl Rl. split; [|split].
    - pose proof (bytes_at_write_inside segs m A (zbytes d) off (zbytes l) B Ho ltac:(rewrite !zbytes_length; lia)) as B'.
      eapply bytes_at_ext; [exact B'|]. unfold upd_bytes, buf_write_at, zbytes, zfirstn, zskipn, zlength.
      rewrite map_app, map_app, firstn_map, skipn_map, length_map. do 2 f_equal. f_equal. f_equal. lia.
    - rewrite buf_write_at_length by lia. apply wr_at_write. exact W.
    - apply buf_write_at_range; assumption.
  Qed.

  #[using="Type"] Lemma zarr_mem_inv : forall m A d off l, zarr m A d -> mem_inv segs m -> 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
    mem_inv segs (write_to_mem m (wa (A + off)) (zbytes l)).
  Proof.
    intros m A d off l ZA MI Ho Hl. apply mem_inv_store; [exact MI|]. rewrite zbytes_length.
    eapply zarr_store_ok; [exact ZA| exact Ho| exact Hl| reflexivity].
  Qed.
End ZA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sx32_small : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold sx32. f_equal. rewrite unsigned_lit by lia. rewrite bv_swrap32_eq.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma zx32_small : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.
Lemma zx16_small : forall x, 0 <= x < 2^16 -> zx16 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx16. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.
Lemma zxb_small : forall x, 0 <= x < 256 -> zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply Z.mod_small. exact Hx. Qed.
Lemma sxb_small : forall x, 0 <= x < 256 -> sxb (Z_to_bv 8 x) = Z_to_bv 64 (if x <? 128 then x else x - 256).
Proof.
  intros x Hx. unfold sxb. f_equal. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 8) with 8. change (2^8) with 256. cbn [Z.div Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  destruct (Z.ltb_spec x 128); Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ltu_falseZ : forall x y, 0 <= y <= x -> x < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_trueZ : forall x y, 0 <= x < y -> y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros. rewrite bv_ltu_Z, !unsigned_lit by lia. apply Z.ltb_lt. lia. Qed.
Lemma eqb_falseZ : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> x <> y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.
Lemma eqb_trueZ : forall x y, x = y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros x y ->. unfold bv_eqb. apply Z.eqb_refl. Qed.
Lemma signed_small : forall x, 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 64) with 64. change (2^64 `div` 2) with (2^63). rewrite (Z.mod_small x) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma lts_falseZ : forall x y, 0 <= y <= x -> x < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros. unfold bv_lts. rewrite !signed_small by lia. apply Z.ltb_ge. lia. Qed.
Lemma lts_trueZ : forall x y, 0 <= x < y -> y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros. unfold bv_lts. rewrite !signed_small by lia. apply Z.ltb_lt. lia. Qed.

(* [comment removed for export] *)
Lemma unsigned_sx32 : forall x, 0 <= x < 2^32 ->
  bv_unsigned (sx32 (Z_to_bv 64 x)) = (if x <? 2^31 then x else x + 2^64 - 2^32).
Proof.
  intros x Hx. unfold sx32. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  destruct (Z.ltb_spec x (2^31)).
  - rewrite (Z.mod_small (x + 2^31)) by lia. rewrite Z.mod_small by lia. lia.
  - replace ((x + 2 ^ 31) mod 2 ^ 32) with (x + 2^31 - 2^32) by (Z.div_mod_to_equations; lia).
    Z.div_mod_to_equations. lia.
Qed.
Lemma ltu_sx32_lit : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 ->
  bv_ltu (sx32 (Z_to_bv 64 x)) (Z_to_bv 64 k) = (x <? k).
Proof.
  intros x k Hx Hk. rewrite bv_ltu_Z, unsigned_sx32, (unsigned_lit k) by lia.
  destruct (Z.ltb_spec x (2^31)); destruct (Z.ltb_spec x k); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]).
Qed.

(* [comment removed for export] *)
Lemma lor_be16 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z.lor ((Z.shiftl a 8) mod 2^64) b = a * 256 + b.
Proof.
  intros a b Ha Hb. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. rewrite Z.mod_small by lia.
  rewrite (lor_add (a * 256) b 8); [lia| lia | change (2^8) with 256; lia |]. change (2^8) with 256. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma ltu_minus12 : forall p, 0 <= p < 65536 ->
  bv_ltu (Z_to_bv 64 (p + -12)) (Z_to_bv 64 2) = ((p =? 12) || (p =? 13))%bool.
Proof.
  intros p Hp. rewrite bv_ltu_Z, (unsigned_lit 2), unsigned_lit_wrap by lia.
  destruct (Z.eqb_spec p 12) as [->|N1]; [reflexivity|]. destruct (Z.eqb_spec p 13) as [->|N2]; [reflexivity|]. cbn [orb].
  apply Z.ltb_ge. destruct (Z_lt_le_dec p 12).
  - replace ((p + -12) mod 2^64) with (p + -12 + 2^64) by (Z.div_mod_to_equations; lia). lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma swrap32_small : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_period : forall x k, bv_swrap 32 (x + k * 2^32) = bv_swrap 32 x.
Proof. intros. rewrite !bv_swrap32_eq. f_equal. replace (x + k * 2^32 + 2^31) with (x + 2^31 + k * 2^32) by lia. apply Z.mod_add. lia. Qed.
Lemma swrap_of_sx32 : forall x k, 0 <= x < 2^32 -> bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 x)) + k) = bv_swrap 32 (x + k).
Proof.
  intros x k Hx. rewrite unsigned_sx32 by lia. destruct (Z.ltb_spec x (2^31)); [reflexivity|].
  replace (x + 2^64 - 2^32 + k) with (x + k + (2^32 - 1) * 2^32) by lia. apply swrap32_period.
Qed.
Lemma sx32_swrap : forall x, 0 <= x < 2^32 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 (bv_swrap 32 x).
Proof. intros. unfold sx32. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma unsigned_swrap32 : forall x, bv_unsigned (Z_to_bv 64 (bv_swrap 32 x)) = (if x mod 2^32 <? 2^31 then x mod 2^32 else x mod 2^32 + 2^64 - 2^32).
Proof.
  intros x. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  replace ((x + 2^31) mod 2^32) with ((x mod 2^32 + 2^31) mod 2^32) by (Z.div_mod_to_equations; nia || lia).
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)) as R. set (y := x mod 2^32) in *.
  destruct (Z.ltb_spec y (2^31)).
  - rewrite (Z.mod_small (y + 2^31)) by lia. rewrite Z.mod_small by lia. lia.
  - replace ((y + 2^31) mod 2^32) with (y + 2^31 - 2^32) by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.
Lemma ltu_swrap_lit : forall x k, 0 <= k < 2^31 ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = (x mod 2^32 <? k).
Proof.
  intros x k Hk. rewrite bv_ltu_Z, unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)) as R.
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); destruct (Z.ltb_spec (x mod 2^32) k); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]).
Qed.

Lemma ltu_swrap_falseZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> k <= x ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = false.
Proof. intros. rewrite ltu_swrap_lit by lia. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_swrap_trueZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> x < k ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = true.
Proof. intros. rewrite ltu_swrap_lit by lia. rewrite Z.mod_small by lia. apply Z.ltb_lt. lia. Qed.
Lemma ltu_sx32_falseZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> k <= x ->
  bv_ltu (sx32 (Z_to_bv 64 x)) (Z_to_bv 64 k) = false.
Proof. intros. rewrite ltu_sx32_lit by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_sx32_trueZ : forall x k, 0 <= x < 2^32 -> 0 <= k < 2^31 -> x < k ->
  bv_ltu (sx32 (Z_to_bv 64 x)) (Z_to_bv 64 k) = true.
Proof. intros. rewrite ltu_sx32_lit by lia. apply Z.ltb_lt. lia. Qed.

Ltac cond_side :=
  fastfirst (first [ noevar_assumption | apply ltu_falseZ; lia | apply ltu_trueZ; lia | apply eqb_falseZ; lia | apply eqb_trueZ; lia
        | apply lts_falseZ; lia | apply lts_trueZ; lia
        | apply ltu_swrap_falseZ; lia | apply ltu_swrap_trueZ; lia | apply ltu_sx32_falseZ; lia | apply ltu_sx32_trueZ; lia
        | apply (proj2 (Bool.negb_false_iff _)); cond_side_t
        | apply (proj2 (Bool.negb_true_iff _)); cond_side ])
with cond_side_t :=
  fastfirst (first [ noevar_assumption | apply ltu_trueZ; lia | apply eqb_trueZ; lia | apply lts_trueZ; lia
        | apply ltu_swrap_trueZ; lia | apply ltu_sx32_trueZ; lia
        | apply (proj2 (Bool.negb_true_iff _)); cond_side ]).
(* [comment removed for export] *)
Ltac bfalse :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with false; [cbv iota| symmetry; cond_side] end.
Ltac btrue :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with true; [cbv iota| symmetry; cond_side_t] end.
(* [comment removed for export] *)
Ltac bstep := lstep; try (lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [bfalse | btrue] end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_mask8 : forall y k, 0 <= y -> 0 <= k -> Z.land y (255 * 2^k) = ((y / 2^k) mod 256) * 2^k.
Proof.
  intros y k Hy Hk. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec.
  replace (255 * 2^k) with (Z.shiftl (Z.ones 8) k) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  replace ((y / 2^k) mod 256 * 2^k) with (Z.shiftl ((Z.shiftr y k) mod 2^8) k)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
  destruct (Z_lt_le_dec n k).
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia.
    destruct (Z_lt_le_dec (n - k) 8).
    + rewrite Z.ones_spec_low, Z.mod_pow2_bits_low, Z.shiftr_spec by lia. rewrite Bool.andb_true_r. f_equal. lia.
    + rewrite Z.ones_spec_high, Z.mod_pow2_bits_high by lia. apply Bool.andb_false_r.
Qed.

Lemma land_65280 : forall y, 0 <= y -> Z.land y 65280 = ((y / 256) mod 256) * 256.
Proof. intros. change 65280 with (255 * 2^8). rewrite land_mask8 by lia. reflexivity. Qed.
Lemma land_16711680 : forall y, 0 <= y -> Z.land y 16711680 = ((y / 65536) mod 256) * 65536.
Proof. intros. change 16711680 with (255 * 2^16). rewrite land_mask8 by lia. reflexivity. Qed.



Lemma sx32_mod32 : forall x, 0 <= x < 2^32 -> bv_unsigned (sx32 (Z_to_bv 64 x)) mod 2^32 = x.
Proof.
  intros x Hx. rewrite unsigned_sx32 by lia. destruct (Z.ltb_spec x (2^31)).
  - apply Z.mod_small. lia.
  - Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma le4_bswap32 : forall X x0 x1 x2 x3,
  0 <= X < 2^64 -> 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  X mod 2^32 = x0 + 256 * x1 + 65536 * x2 + 16777216 * x3 ->
  le4 (Z_to_bv 64 (Z.lor (Z.lor ((Z.shiftl X 24) mod 18446744073709551616) ((Z.shiftl (Z.land X 65280) 8) mod 18446744073709551616))
                           (Z.lor (Z.land (Z.shiftr X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 X) 24)) mod 18446744073709551616))))
  = zbytes [x3; x2; x1; x0].
Proof.
  intros X x0 x1 x2 x3 HX H0 H1 H2 H3 HV.
  rewrite bv_wrap32_eq.
  rewrite !land_65280 by (try apply Z.shiftr_nonneg; lia).
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  assert (E1 : (X / 256) mod 256 = x1) by (Z.div_mod_to_equations; lia).
  assert (E2 : (X / 2^8 / 256) mod 256 = x2) by (Z.div_mod_to_equations; lia).
  assert (E3 : X mod 2^32 / 2^24 = x3) by (Z.div_mod_to_equations; lia).
  rewrite E1, E2, E3. rewrite (swrap32_small x3) by lia.
  rewrite (Z.mod_small x3) by lia.
  rewrite (Z.mod_small (x1 * 256 * 2^8)) by lia.
  rewrite (lor_add (x2 * 256) x3 8) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (lor_add ((X * 2^24) mod 18446744073709551616) (x1 * 256 * 2^8) 24) by (try lia; Z.div_mod_to_equations; lia).
  rewrite (lor_add _ (x2 * 256 + x3) 16) by (try lia; Z.div_mod_to_equations; lia).
  apply le4_of_mod32; [reflexivity|]. cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2^64). change (bv_modulus 8) with 256.
  rewrite !(Z.mod_small _ 256) by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma word_range : forall w : word, 0 <= bv_unsigned w < 2^64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma le2_of_mod16 : forall (v : word) (bs : list byte), length bs = 2%nat ->
  bv_unsigned v mod 2^16 = le_val (map bv_unsigned bs) -> le2 v = bs.
Proof.
  intros v bs Hl Hv. unfold le2.
  rewrite <- (Z_to_le_bytes_mod 2 _ 16) by (cbn; lia). change (2 ^ 16) with (2^16) in *. rewrite Hv.
  rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma le2_bswap16 : forall X x0 x1, 0 <= x0 < 256 -> 0 <= x1 < 256 -> X = x0 + 256 * x1 ->
  le2 (Z_to_bv 64 (Z.lor ((Z.shiftl X 8) mod 18446744073709551616) (Z.shiftr X 8))) = zbytes [x1; x0].
Proof.
  intros X x0 x1 H0 H1 ->.
  rewrite !Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  replace ((x0 + 256 * x1) / 256) with x1 by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small _ 18446744073709551616) by lia.
  rewrite (lor_add ((x0 + 256 * x1) * 256) x1 8); [| lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia].
  apply le2_of_mod16; [reflexivity|]. cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2^64). change (bv_modulus 8) with 256.
  rewrite !(Z.mod_small _ 256) by lia. Z.div_mod_to_equations. lia.
Qed.
End TwB.
End PP_kit.

(* [comment removed for export] *)
Module PP_kit2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge Mem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma znth_nonneg_nth : forall l i, 0 <= i -> znth l i = nth (Z.to_nat i) l 0.
Proof. intros l i Hi. unfold znth. replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma zlist_ext : forall (l1 l2 : list Z), length l1 = length l2 ->
  (forall i, 0 <= i < Z.of_nat (length l1) -> znth l1 i = znth l2 i) -> l1 = l2.
Proof.
  intros l1 l2 HL HE. apply (nth_ext l1 l2 0 0 HL). intros n Hn.
  specialize (HE (Z.of_nat n) ltac:(lia)). rewrite !znth_nonneg_nth, !Nat2Z.id in HE by lia. exact HE.
Qed.

Lemma znth_app : forall (l1 l2 : list Z) i, 0 <= i ->
  znth (l1 ++ l2) i = if i <? Z.of_nat (length l1) then znth l1 i else znth l2 (i - Z.of_nat (length l1)).
Proof.
  intros l1 l2 i Hi. destruct (Z.ltb_spec i (Z.of_nat (length l1))); rewrite !znth_nonneg_nth by lia.
  - apply app_nth1. lia.
  - rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma nth_firstn_any : forall (l : list Z) k i, (i < k)%nat -> nth i (firstn k l) 0 = nth i l 0.
Proof.
  intros l k i Hik. revert l k Hik. induction i as [|i IH]; intros l k Hik.
  - destruct k; [lia|]. destruct l; reflexivity.
  - destruct k; [lia|]. destruct l; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma znth_zfirstn : forall n (l : list Z) i, 0 <= i < n -> znth (zfirstn n l) i = znth l i.
Proof. intros n l i Hi. rewrite !znth_nonneg_nth by lia. unfold zfirstn. apply nth_firstn_any. lia. Qed.

Lemma znth_zskipn : forall n (l : list Z) i, 0 <= n -> 0 <= i -> znth (zskipn n l) i = znth l (n + i).
Proof. intros n l i Hn Hi. rewrite !znth_nonneg_nth by lia. unfold zskipn. rewrite nth_skipn. f_equal. lia. Qed.

Lemma znth_over : forall (l : list Z) i, Z.of_nat (length l) <= i -> znth l i = 0.
Proof. intros l i Hi. rewrite znth_nonneg_nth by lia. apply nth_overflow. lia. Qed.

Lemma zfirstn_length_le : forall n (l : list Z), 0 <= n <= Z.of_nat (length l) -> length (zfirstn n l) = Z.to_nat n.
Proof. intros. unfold zfirstn. rewrite length_firstn. lia. Qed.
Lemma zskipn_length : forall n (l : list Z), length (zskipn n l) = (length l - Z.to_nat n)%nat.
Proof. intros. unfold zskipn. apply length_skipn. Qed.

(* [comment removed for export] *)
Lemma znth_buf_write_at : forall off l d i, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) -> 0 <= i ->
  znth (buf_write_at off l d) i =
  if (off <=? i) && (i <? off + Z.of_nat (length l)) then znth l (i - off) else znth d i.
Proof.
  intros off l d i Ho Hl Hi. unfold buf_write_at, zlength.
  rewrite znth_app by lia. rewrite zfirstn_length_le by lia.
  destruct (Z.ltb_spec i (Z.of_nat (Z.to_nat off))).
  - replace (off <=? i) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb]. apply znth_zfirstn. lia.
  - replace (off <=? i) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    rewrite znth_app by lia. destruct (Z.ltb_spec (i - Z.of_nat (Z.to_nat off)) (Z.of_nat (length l))).
    + replace (i <? off + Z.of_nat (length l)) with true by (symmetry; apply Z.ltb_lt; lia). f_equal. lia.
    + replace (i <? off + Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite znth_zskipn by lia. f_equal. lia.
Qed.

Lemma znth_zslice : forall off n (d : list Z) j, 0 <= off -> 0 <= j < n ->
  znth (zslice off n d) j = znth d (off + j).
Proof. intros. unfold zslice. rewrite znth_zfirstn by lia. apply znth_zskipn; lia. Qed.

Lemma znth_rev : forall (l : list Z) j, 0 <= j < Z.of_nat (length l) -> znth (rev l) j = znth l (Z.of_nat (length l) - 1 - j).
Proof.
  intros l j Hj. rewrite !znth_nonneg_nth by lia.
  rewrite rev_nth by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_u8_write_other : forall off l d j, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) -> 0 <= j ->
  (j < off \/ off + Z.of_nat (length l) <= j) ->
  get_u8 (buf_write_at off l d) j = get_u8 d j.
Proof.
  intros off l d j Ho Hl Hj Hd. unfold get_u8. rewrite znth_buf_write_at by lia.
  destruct Hd; [replace (off <=? j) with false by (symmetry; apply Z.leb_gt; lia)
              | replace (j <? off + Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; lia); rewrite Bool.andb_false_r];
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zslice_write_other : forall off l d a n, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
  0 <= a -> 0 <= n -> a + n <= Z.of_nat (length d) ->
  (a + n <= off \/ off + Z.of_nat (length l) <= a) ->
  zslice a n (buf_write_at off l d) = zslice a n d.
Proof.
  intros off l d a n Ho Hl Ha Hn Han Hd.
  apply zlist_ext.
  - rewrite !zslice_length; rewrite ?buf_write_at_length; lia.
  - intros i Hi. rewrite zslice_length in Hi by (rewrite ?buf_write_at_length; lia).
    rewrite !znth_zslice by lia. rewrite znth_buf_write_at by lia.
    destruct Hd.
    + replace (off <=? a + i) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    + replace (a + i <? off + Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zslice_write_same : forall off l d, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
  zslice off (Z.of_nat (length l)) (buf_write_at off l d) = l.
Proof.
  intros off l d Ho Hl. apply zlist_ext.
  - rewrite zslice_length; rewrite ?buf_write_at_length; lia.
  - intros i Hi. rewrite zslice_length in Hi by (rewrite ?buf_write_at_length; lia).
    rewrite znth_zslice by lia. rewrite znth_buf_write_at by lia.
    replace (off <=? off + i) with true by (symmetry; apply Z.leb_le; lia).
    replace (off + i <? off + Z.of_nat (length l)) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. f_equal. lia.
Qed.

Lemma get_u8_swap_other : forall k off d j, 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) -> 0 <= j ->
  (j < off \/ off + k <= j) -> get_u8 (swap_field k off d) j = get_u8 d j.
Proof.
  intros k off d j Ho Hk Hl Hj Hd. unfold swap_field.
  apply get_u8_write_other; rewrite ?length_rev, ?zslice_length; lia.
Qed.
Lemma get_le32_swap_other : forall k off d a, 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) -> 0 <= a -> a + 4 <= Z.of_nat (length d) ->
  (a + 4 <= off \/ off + k <= a) -> get_le32 (swap_field k off d) a = get_le32 d a.
Proof.
  intros k off d a Ho Hk Hl Ha Ha4 Hd. unfold get_le32, swap_field. f_equal.
  apply zslice_write_other; rewrite ?length_rev, ?zslice_length; lia.
Qed.
Lemma get_le16_swap_other : forall k off d a, 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) -> 0 <= a -> a + 2 <= Z.of_nat (length d) ->
  (a + 2 <= off \/ off + k <= a) -> get_le16 (swap_field k off d) a = get_le16 d a.
Proof.
  intros k off d a Ho Hk Hl Ha Ha2 Hd. unfold get_le16, swap_field. f_equal.
  apply zslice_write_other; rewrite ?length_rev, ?zslice_length; lia.
Qed.
Lemma get_u8_write_other' : forall off l d j n, length l = n -> 0 <= off -> off + Z.of_nat n <= Z.of_nat (length d) -> 0 <= j ->
  (j < off \/ off + Z.of_nat n <= j) -> get_u8 (buf_write_at off l d) j = get_u8 d j.
Proof. intros off l d j n <-. apply get_u8_write_other. Qed.

(* [comment removed for export] *)
Lemma get_le32_write_same : forall off d y0 y1 y2 y3, 0 <= off -> off + 4 <= Z.of_nat (length d) ->
  get_le32 (buf_write_at off [y0; y1; y2; y3] d) off = y0 + 256 * y1 + 65536 * y2 + 16777216 * y3.
Proof.
  intros off d y0 y1 y2 y3 Ho Hl. unfold get_le32.
  pose proof (zslice_write_same off [y0; y1; y2; y3] d Ho ltac:(cbn [length]; lia)) as E. change (Z.of_nat (length [y0; y1; y2; y3])) with 4 in E.
  rewrite E. cbn. lia.
Qed.
Lemma get_le16_write_same : forall off d y0 y1, 0 <= off -> off + 2 <= Z.of_nat (length d) ->
  get_le16 (buf_write_at off [y0; y1] d) off = y0 + 256 * y1.
Proof.
  intros off d y0 y1 Ho Hl. unfold get_le16.
  pose proof (zslice_write_same off [y0; y1] d Ho ltac:(cbn [length]; lia)) as E. change (Z.of_nat (length [y0; y1])) with 2 in E.
  rewrite E. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma buf_write_at_comm : forall o1 l1 o2 l2 d, 0 <= o1 -> 0 <= o2 ->
  o1 + Z.of_nat (length l1) <= Z.of_nat (length d) -> o2 + Z.of_nat (length l2) <= Z.of_nat (length d) ->
  (o1 + Z.of_nat (length l1) <= o2 \/ o2 + Z.of_nat (length l2) <= o1) ->
  buf_write_at o2 l2 (buf_write_at o1 l1 d) = buf_write_at o1 l1 (buf_write_at o2 l2 d).
Proof.
  intros o1 l1 o2 l2 d H1 H2 L1 L2 D. apply zlist_ext.
  - rewrite !buf_write_at_length; rewrite ?buf_write_at_length; lia.
  - intros i Hi. rewrite !buf_write_at_length in Hi by (rewrite ?buf_write_at_length; lia).
    rewrite !znth_buf_write_at by (rewrite ?buf_write_at_length; lia).
    destruct (Z.leb_spec o2 i); destruct (Z.ltb_spec i (o2 + Z.of_nat (length l2)));
    destruct (Z.leb_spec o1 i); destruct (Z.ltb_spec i (o1 + Z.of_nat (length l1))); cbn [andb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma swap8_split : forall off off4 d x0 x1 x2 x3 x4 x5 x6 x7, 0 <= off -> off + 8 <= Z.of_nat (length d) -> off4 = off + 4 ->
  zslice off 4 d = [x0; x1; x2; x3] -> zslice off4 4 d = [x4; x5; x6; x7] ->
  buf_write_at off4 [x3; x2; x1; x0] (buf_write_at off [x7; x6; x5; x4] d) = swap_field 8 off d.
Proof.
  intros off off4 d x0 x1 x2 x3 x4 x5 x6 x7 Ho Hl -> E0 E1.
  pose proof (get_u8_of_slice4 off d _ _ _ _ Ho ltac:(lia) E0) as (A0 & A1 & A2 & A3).
  pose proof (get_u8_of_slice4 (off + 4) d _ _ _ _ ltac:(lia) ltac:(lia) E1) as (A4 & A5 & A6 & A7). unfold get_u8 in *.
  unfold swap_field. apply zlist_ext.
  - rewrite !buf_write_at_length; cbn [length]; rewrite ?buf_write_at_length, ?length_rev, ?zslice_length; cbn [length]; lia.
  - intros i Hi. rewrite !buf_write_at_length in Hi by (cbn [length]; rewrite ?buf_write_at_length; cbn [length]; lia).
    rewrite !znth_buf_write_at by (cbn [length]; rewrite ?buf_write_at_length, ?length_rev, ?zslice_length; cbn [length]; lia).
    cbn [length]. rewrite length_rev, zslice_length by lia.
    destruct (Z.leb_spec (off + 4) i); destruct (Z.ltb_spec i (off + 4 + Z.of_nat 4));
    destruct (Z.leb_spec off i); destruct (Z.ltb_spec i (off + Z.of_nat 4)); destruct (Z.ltb_spec i (off + Z.of_nat (Z.to_nat 8)));
    cbn [andb]; try reflexivity; try lia.
    + rewrite znth_rev by (rewrite zslice_length; lia). rewrite zslice_length by lia. rewrite znth_zslice by lia.
      assert (C : i - (off + 4) = 0 \/ i - (off + 4) = 1 \/ i - (off + 4) = 2 \/ i - (off + 4) = 3) by lia.
      destruct C as [C|[C|[C|C]]]; rewrite C; cbn -[Z.add Z.sub Z.of_nat];
      [rewrite <- A3 | rewrite <- A2 | rewrite <- A1 | rewrite <- A0]; f_equal; lia.
    + rewrite znth_rev by (rewrite zslice_length; lia). rewrite zslice_length by lia. rewrite znth_zslice by lia.
      assert (C : i - off = 0 \/ i - off = 1 \/ i - off = 2 \/ i - off = 3) by lia.
      destruct C as [C|[C|[C|C]]]; rewrite C; cbn -[Z.add Z.sub Z.of_nat];
      [rewrite <- A7 | rewrite <- A6 | rewrite <- A5 | rewrite <- A4]; f_equal; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le4_of_lanes : forall E y0 y1 y2 y3,
  E mod 2^32 = y0 + 256 * y1 + 65536 * y2 + 16777216 * y3 ->
  0 <= y0 < 256 -> 0 <= y1 < 256 -> 0 <= y2 < 256 -> 0 <= y3 < 256 ->
  le4 (Z_to_bv 64 E) = zbytes [y0; y1; y2; y3].
Proof.
  intros E y0 y1 y2 y3 HE H0 H1 H2 H3. apply le4_of_mod32; [reflexivity|].
  cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^32 * 2^32). change (bv_modulus 8) with 256.
  rewrite Z.rem_mul_r, HE by lia. rewrite !(Z.mod_small _ 256) by lia. lia.
Qed.
Lemma le2_of_lanes : forall E y0 y1,
  E mod 2^16 = y0 + 256 * y1 -> 0 <= y0 < 256 -> 0 <= y1 < 256 ->
  le2 (Z_to_bv 64 E) = zbytes [y0; y1].
Proof.
  intros E y0 y1 HE H0 H1. apply le2_of_mod16; [reflexivity|].
  cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^16 * 2^48). change (bv_modulus 8) with 256.
  rewrite Z.rem_mul_r, HE by lia. rewrite !(Z.mod_small _ 256) by lia. lia.
Qed.

(* [comment removed for export] *)
Definition bytes_ok (L : list Z) : Prop := Forall (fun x => 0 <= x < 256) L.

Lemma le_of_bytes_range : forall L, bytes_ok L -> 0 <= le_of_bytes L < 256 ^ (Z.of_nat (length L)).
Proof.
  induction L as [|x L IH]; intros HB; cbn [le_of_bytes length].
  - lia.
  - apply Forall_cons_iff in HB as [Hx HB]. specialize (IH HB). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma le_of_bytes_app : forall L1 L2, le_of_bytes (L1 ++ L2) = le_of_bytes L1 + 256 ^ (Z.of_nat (length L1)) * le_of_bytes L2.
Proof.
  induction L1 as [|x L1 IH]; intros L2; cbn [le_of_bytes app length].
  - lia.
  - rewrite IH. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma le_of_bytes_repeat0 : forall k L, le_of_bytes (repeat 0 k ++ L) = 256 ^ (Z.of_nat k) * le_of_bytes L.
Proof.
  intros k L. rewrite le_of_bytes_app, repeat_length.
  replace (le_of_bytes (repeat 0 k)) with 0; [lia|]. induction k; cbn; lia.
Qed.

Lemma bytes_ok_firstn : forall n L, bytes_ok L -> bytes_ok (firstn n L).
Proof. intros. unfold bytes_ok. rewrite <- (firstn_skipn n L) in H. apply Forall_app in H. tauto. Qed.
Lemma bytes_ok_skipn : forall n L, bytes_ok L -> bytes_ok (skipn n L).
Proof. intros. unfold bytes_ok. rewrite <- (firstn_skipn n L) in H. apply Forall_app in H. tauto. Qed.

Lemma le_of_bytes_split : forall n L, le_of_bytes L = le_of_bytes (firstn n L) + 256 ^ (Z.of_nat (length (firstn n L))) * le_of_bytes (skipn n L).
Proof. intros n L. rewrite <- (firstn_skipn n L) at 1. apply le_of_bytes_app. Qed.

(* [comment removed for export] *)
Lemma lanes_mod : forall n L, bytes_ok L -> le_of_bytes L mod 256 ^ (Z.of_nat n) = le_of_bytes (firstn n L).
Proof.
  intros n L HB. rewrite (le_of_bytes_split n L).
  pose proof (le_of_bytes_range (firstn n L) (bytes_ok_firstn n L HB)) as R.
  destruct (Nat.le_gt_cases (length L) n).
  - rewrite firstn_all2, skipn_all2 by lia. cbn [le_of_bytes]. rewrite Z.mul_0_r, Z.add_0_r.
    apply Z.mod_small. pose proof (le_of_bytes_range L HB). rewrite firstn_all2 in R by lia.
    assert (256 ^ Z.of_nat (length L) <= 256 ^ Z.of_nat n) by (apply Z.pow_le_mono_r; lia). lia.
  - rewrite length_firstn in *. rewrite Nat.min_l in * by lia.
    set (A := le_of_bytes (firstn n L)) in *. set (B := le_of_bytes (skipn n L)) in *. set (P := 256 ^ Z.of_nat n) in *.
    replace (A + P * B) with (A + B * P) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma lanes_mod64 : forall L, bytes_ok L -> le_of_bytes L mod 18446744073709551616 = le_of_bytes (firstn 8 L).
Proof. intros. change 18446744073709551616 with (256 ^ Z.of_nat 8). apply lanes_mod. assumption. Qed.
Lemma lanes_mod32 : forall L, bytes_ok L -> le_of_bytes L mod 2^32 = le_of_bytes (firstn 4 L).
Proof. intros. change (2^32) with (256 ^ Z.of_nat 4). apply lanes_mod. assumption. Qed.
Lemma lanes_mod16 : forall L, bytes_ok L -> le_of_bytes L mod 2^16 = le_of_bytes (firstn 2 L).
Proof. intros. change (2^16) with (256 ^ Z.of_nat 2). apply lanes_mod. assumption. Qed.
Lemma lanes_wrap32 : forall L, bytes_ok L -> bv_wrap 32 (le_of_bytes L) = le_of_bytes (firstn 4 L).
Proof. intros. rewrite bv_wrap32_eq. apply lanes_mod32. assumption. Qed.

(* [comment removed for export] *)
Lemma lanes_shl : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  (Z.shiftl (le_of_bytes L) n) mod 18446744073709551616 = le_of_bytes (firstn 8 (repeat 0 k ++ L)).
Proof.
  intros k L n HB ->. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite <- lanes_mod64 by (unfold bytes_ok; apply Forall_app; split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia| exact HB]).
  rewrite le_of_bytes_repeat0. rewrite Z.pow_mul_r by lia. change (2^8) with 256. f_equal. lia.
Qed.
Lemma lanes_shl_nomod : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  Z.shiftl (le_of_bytes L) n = le_of_bytes (repeat 0 k ++ L).
Proof.
  intros k L n HB ->. rewrite Z.shiftl_mul_pow2 by lia. rewrite le_of_bytes_repeat0. rewrite Z.pow_mul_r by lia.
  change (2^8) with 256. lia.
Qed.
Lemma lanes_shr : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  Z.shiftr (le_of_bytes L) n = le_of_bytes (skipn k L).
Proof.
  intros k L n HB ->. rewrite Z.shiftr_div_pow2 by lia. rewrite (le_of_bytes_split k L) at 1.
  pose proof (le_of_bytes_range (firstn k L) (bytes_ok_firstn k L HB)) as R.
  destruct (Nat.le_gt_cases (length L) k).
  - rewrite firstn_all2, skipn_all2 by lia. cbn [le_of_bytes]. rewrite Z.mul_0_r, Z.add_0_r. apply Z.div_small.
    rewrite firstn_all2 in R by lia. rewrite Z.pow_mul_r by lia. change (2^8) with 256.
    assert (256 ^ Z.of_nat (length L) <= 256 ^ Z.of_nat k) by (apply Z.pow_le_mono_r; lia). lia.
  - rewrite length_firstn in *. rewrite Nat.min_l in * by lia. rewrite Z.pow_mul_r by lia. change (2^8) with 256.
    set (A := le_of_bytes (firstn k L)) in *. set (B := le_of_bytes (skipn k L)) in *. set (P := 256 ^ Z.of_nat k) in *.
    replace (A + P * B) with (B * P + A) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma lanes_mask : forall j L, bytes_ok L ->
  Z.land (le_of_bytes L) (255 * 2 ^ (8 * Z.of_nat j)) = le_of_bytes (repeat 0 j ++ [nth j L 0]).
Proof.
  intros j L HB. rewrite land_mask8 by (pose proof (le_of_bytes_range L HB); lia).
  rewrite le_of_bytes_repeat0. cbn [le_of_bytes]. rewrite Z.mul_0_r, Z.add_0_r.
  rewrite <- Z.shiftr_div_pow2 by lia. rewrite (lanes_shr j L) by (auto; lia).
  rewrite Z.pow_mul_r by lia. change (2^8) with 256. rewrite Z.mul_comm. f_equal.
  pose proof (bytes_ok_skipn j L HB) as HS.
  destruct (skipn j L) as [|y R] eqn:E.
  - cbn. rewrite nth_overflow; [reflexivity|]. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
  - apply Forall_cons_iff in HS as [Hy HR]. cbn [le_of_bytes].
    replace (y + 256 * le_of_bytes R) with (y + le_of_bytes R * 256) by lia. rewrite Z.mod_add, Z.mod_small by lia.
    replace y with (nth 0 (skipn j L) 0) by (rewrite E; reflexivity). rewrite nth_skipn. f_equal. lia.
Qed.
Lemma lanes_mask1 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 65280 = le_of_bytes [0; nth 1 L 0].
Proof. intros. change 65280 with (255 * 2 ^ (8 * Z.of_nat 1)). rewrite lanes_mask by assumption. reflexivity. Qed.
Lemma lanes_mask2 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 16711680 = le_of_bytes [0; 0; nth 2 L 0].
Proof. intros. change 16711680 with (255 * 2 ^ (8 * Z.of_nat 2)). rewrite lanes_mask by assumption. reflexivity. Qed.
Lemma lanes_mask0 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 255 = le_of_bytes [nth 0 L 0].
Proof. intros. change 255 with (255 * 2 ^ (8 * Z.of_nat 0)) at 1. rewrite lanes_mask by assumption. reflexivity. Qed.
Lemma lanes_mask3 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 4278190080 = le_of_bytes [0; 0; 0; nth 3 L 0].
Proof. intros. change 4278190080 with (255 * 2 ^ (8 * Z.of_nat 3)). rewrite lanes_mask by assumption. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint lanes_merge (L1 L2 L : list Z) : Prop :=
  match L1, L2, L with
  | [], l2, l => l = l2
  | l1, [], l => l = l1
  | a :: l1, b :: l2, c :: l => ((a = 0 /\ c = b) \/ (b = 0 /\ c = a)) /\ lanes_merge l1 l2 l
  | _ :: _, _ :: _, [] => False
  end.
Lemma lor_shift8 : forall a b c d, 0 <= a < 256 -> 0 <= c < 256 -> 0 <= b -> 0 <= d -> (a = 0 \/ c = 0) ->
  Z.lor (a + 256 * b) (c + 256 * d) = (Z.lor a c) + 256 * Z.lor b d.
Proof.
  intros a b c d Ha Hc Hb Hd Hz.
  assert (E1 : a + 256 * b = Z.lor (256 * b) a).
  { rewrite (lor_add (256 * b) a 8); [lia | lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia]. }
  assert (E2 : c + 256 * d = Z.lor (256 * d) c).
  { rewrite (lor_add (256 * d) c 8); [lia | lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia]. }
  rewrite E1, E2.
  transitivity (Z.lor (Z.lor (256 * b) (256 * d)) (Z.lor a c)).
  { rewrite <- !Z.lor_assoc. f_equal. rewrite (Z.lor_comm a (Z.lor (256 * d) c)). rewrite <- Z.lor_assoc. f_equal. apply Z.lor_comm. }
  assert (R : 0 <= Z.lor a c < 256).
  { destruct Hz as [-> | ->]; [rewrite Z.lor_0_l | rewrite Z.lor_0_r]; lia. }
  replace (Z.lor (256 * b) (256 * d)) with (256 * Z.lor b d).
  2:{ rewrite !(Z.mul_comm 256). change 256 with (2^8). rewrite <- !Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_lor. reflexivity. }
  pose proof (Z.lor_nonneg b d).
  rewrite (lor_add (256 * Z.lor b d) (Z.lor a c) 8); [lia | lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia].
Qed.
Lemma lanes_lor : forall L1 L2 L, lanes_merge L1 L2 L -> bytes_ok L1 -> bytes_ok L2 ->
  Z.lor (le_of_bytes L1) (le_of_bytes L2) = le_of_bytes L.
Proof.
  induction L1 as [|a L1 IH]; intros L2 L HM H1 H2.
  - cbn in HM. subst L. cbn [le_of_bytes]. apply Z.lor_0_l.
  - destruct L2 as [|b L2].
    + cbn in HM. subst L. apply Z.lor_0_r.
    + destruct L as [|c L]; [destruct HM|]. cbn [lanes_merge] in HM. destruct HM as [Hc HM].
      apply Forall_cons_iff in H1 as [Ha H1]. apply Forall_cons_iff in H2 as [Hb H2].
      cbn [le_of_bytes]. pose proof (le_of_bytes_range L1 H1). pose proof (le_of_bytes_range L2 H2).
      rewrite lor_shift8 by lia. rewrite (IH L2 L) by assumption. f_equal.
      destruct Hc as [[-> ->]|[-> ->]]; [apply Z.lor_0_l | apply Z.lor_0_r].
Qed.

(* [comment removed for export] *)
Definition sx_lane (x3 : Z) : Z := if x3 <? 128 then 0 else 255.
Lemma sx_lane_range : forall x, 0 <= sx_lane x < 256.
Proof. intros. unfold sx_lane. destruct (x <? 128); lia. Qed.
Lemma lanes_sx32 : forall x0 x1 x2 x3, 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [x0; x1; x2; x3]))) =
  le_of_bytes [x0; x1; x2; x3; sx_lane x3; sx_lane x3; sx_lane x3; sx_lane x3].
Proof.
  intros. cbn [le_of_bytes]. rewrite unsigned_sx32 by lia. unfold sx_lane.
  destruct (Z.ltb_spec x3 128); destruct (Z.ltb_spec (x0 + 256 * (x1 + 256 * (x2 + 256 * (x3 + 256 * 0)))) (2^31)); lia.
Qed.
(* [comment removed for export] *)
Lemma lanes_swrap_small : forall L, bytes_ok L -> (length L <= 3)%nat ->
  (bv_swrap 32 (le_of_bytes L)) mod 18446744073709551616 = le_of_bytes L.
Proof.
  intros L HB HL. pose proof (le_of_bytes_range L HB) as R.
  assert (256 ^ Z.of_nat (length L) <= 256 ^ 3) by (apply Z.pow_le_mono_r; lia).
  rewrite swrap32_small by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma lanes_swrap4 : forall a b c e, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= e < 256 ->
  (bv_swrap 32 (le_of_bytes [a; b; c; e])) mod 18446744073709551616 =
  le_of_bytes [a; b; c; e; sx_lane e; sx_lane e; sx_lane e; sx_lane e].
Proof.
  intros. cbn [le_of_bytes]. rewrite bv_swrap32_eq. unfold sx_lane.
  destruct (Z.ltb_spec e 128); Z.div_mod_to_equations; lia.
Qed.
Lemma lanes_swrap_any : forall L, bytes_ok L -> (4 < length L)%nat ->
  bv_swrap 32 (le_of_bytes L) = bv_swrap 32 (le_of_bytes (firstn 4 L)).
Proof.
  intros L HB HL. rewrite !bv_swrap32_eq. rewrite <- (lanes_mod32 L HB). Z.div_mod_to_equations. lia.
Qed.
Lemma lanes_swrap_shl : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  bv_swrap 32 (Z.shiftl (le_of_bytes L) n) = bv_swrap 32 (le_of_bytes (firstn 4 (repeat 0 k ++ L))).
Proof.
  intros k L n HB ->. rewrite Z.shiftl_mul_pow2 by lia.
  assert (HB' : bytes_ok (repeat 0 k ++ L)).
  { unfold bytes_ok. apply Forall_app. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia| exact HB]. }
  replace (le_of_bytes L * 2 ^ (8 * Z.of_nat k)) with (le_of_bytes (repeat 0 k ++ L))
    by (rewrite le_of_bytes_repeat0, Z.pow_mul_r by lia; change (2^8) with 256; lia).
  rewrite !bv_swrap32_eq. rewrite <- (lanes_mod32 _ HB'). Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma ltu_lit_sx32 : forall k x, 0 <= x < 2^32 -> 0 <= k < 2^31 ->
  bv_ltu (Z_to_bv 64 k) (sx32 (Z_to_bv 64 x)) = (k <? x).
Proof.
  intros k x Hx Hk. rewrite bv_ltu_Z, unsigned_sx32, (unsigned_lit k) by lia.
  destruct (Z.ltb_spec x (2^31)); destruct (Z.ltb_spec k x); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]).
Qed.
Lemma ltu_lit_sx32_falseZ : forall k x, 0 <= x < 2^32 -> 0 <= k < 2^31 -> x <= k -> bv_ltu (Z_to_bv 64 k) (sx32 (Z_to_bv 64 x)) = false.
Proof. intros. rewrite ltu_lit_sx32 by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_lit_sx32_trueZ : forall k x, 0 <= x < 2^32 -> 0 <= k < 2^31 -> k < x -> bv_ltu (Z_to_bv 64 k) (sx32 (Z_to_bv 64 x)) = true.
Proof. intros. rewrite ltu_lit_sx32 by lia. apply Z.ltb_lt. lia. Qed.
(* [comment removed for export] *)
Lemma sx32_as_swrap : forall x, sx32 (Z_to_bv 64 x) = Z_to_bv 64 (bv_swrap 32 x).
Proof.
  intros x. unfold sx32. rewrite unsigned_lit_wrap. f_equal. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia.
Qed.
Lemma ltu_swrap_swrap : forall x y, bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x mod 2^32 <? y mod 2^32).
Proof.
  intros x y. rewrite bv_ltu_Z, !unsigned_swrap32.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound y (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); destruct (Z.ltb_spec (y mod 2^32) (2^31)); cbv iota;
    (destruct (Z.ltb_spec (x mod 2^32) (y mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia])).
Qed.
Lemma eqb_swrap_swrap : forall x y, bv_eqb (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x mod 2^32 =? y mod 2^32).
Proof.
  intros x y. unfold bv_eqb. rewrite !unsigned_swrap32.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound y (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); destruct (Z.ltb_spec (y mod 2^32) (2^31)); cbv iota;
    (destruct (Z.eqb_spec (x mod 2^32) (y mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia])).
Qed.
Lemma eqb_swrap_small : forall x k, 0 <= k < 2^31 -> bv_eqb (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = (x mod 2^32 =? k).
Proof.
  intros x k Hk. unfold bv_eqb. rewrite unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); cbv iota; (destruct (Z.eqb_spec (x mod 2^32) k); fastfirst (first [ noevar_assumption |reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia])).
Qed.
Lemma eqb_small_swrap : forall k x, 0 <= k < 2^31 -> bv_eqb (Z_to_bv 64 k) (Z_to_bv 64 (bv_swrap 32 x)) = (k =? x mod 2^32).
Proof.
  intros k x Hk. unfold bv_eqb. rewrite unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); cbv iota; (destruct (Z.eqb_spec k (x mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia])).
Qed.
(* [comment removed for export] *)
Lemma ltu_swrap_small : forall x k, 0 <= k < 2^31 -> bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = (x mod 2^32 <? k).
Proof. intros. apply ltu_swrap_lit. lia. Qed.
Lemma ltu_small_swrap : forall k x, 0 <= k < 2^31 -> bv_ltu (Z_to_bv 64 k) (Z_to_bv 64 (bv_swrap 32 x)) = (k <? x mod 2^32).
Proof.
  intros k x Hk. rewrite bv_ltu_Z, unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); cbv iota; (destruct (Z.ltb_spec k (x mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia])).
Qed.

Ltac bytes_ok_tac := unfold bytes_ok; repeat (apply Forall_cons; [fastfirst (first [assumption | apply sx_lane_range | lia]) |]); apply Forall_nil.

(* [comment removed for export] *)
Ltac lanes_merge_compute L1 L2 :=
  lazymatch L1 with
  | [] => L2
  | ?a :: ?l1 =>
    lazymatch L2 with
    | [] => L1
    | ?b :: ?l2 =>
      let r := lanes_merge_compute l1 l2 in
      lazymatch a with
      | 0 => constr:(b :: r)
      | _ => lazymatch b with 0 => constr:(a :: r) end
      end
    end
  end.
Ltac lanes_merge_tac := cbn [lanes_merge]; repeat split; try reflexivity;
  first [ left; split; reflexivity | right; split; reflexivity ].

(* [comment removed for export] *)
Ltac lanes_step :=
  match goal with
  | |- context [ (Z.shiftl (le_of_bytes ?L) ?n) mod 18446744073709551616 ] =>
      let k := eval cbv -[sx_lane] in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (firstn 8 (repeat 0 k ++ L)) in
      replace ((Z.shiftl (le_of_bytes L) n) mod 18446744073709551616) with (le_of_bytes L2)
        by (symmetry; apply (lanes_shl k L n); [bytes_ok_tac | reflexivity])
  | |- context [ Z.shiftl (le_of_bytes ?L) ?n ] =>
      let k := eval cbv in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (repeat 0 k ++ L) in
      replace (Z.shiftl (le_of_bytes L) n) with (le_of_bytes L2)
        by (symmetry; apply (lanes_shl_nomod k L n); [bytes_ok_tac | reflexivity])
  | |- context [ Z.shiftr (le_of_bytes ?L) ?n ] =>
      let k := eval cbv -[sx_lane] in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (skipn k L) in
      replace (Z.shiftr (le_of_bytes L) n) with (le_of_bytes L2)
        by (symmetry; apply (lanes_shr k L n); [bytes_ok_tac | reflexivity])
  | |- context [ Z.land (le_of_bytes ?L) 65280 ] =>
      let y := eval cbv -[sx_lane] in (nth 1 L 0) in
      replace (Z.land (le_of_bytes L) 65280) with (le_of_bytes [0; y]) by (symmetry; apply (lanes_mask1 L); bytes_ok_tac)
  | |- context [ Z.land (le_of_bytes ?L) 16711680 ] =>
      let y := eval cbv -[sx_lane] in (nth 2 L 0) in
      replace (Z.land (le_of_bytes L) 16711680) with (le_of_bytes [0; 0; y]) by (symmetry; apply (lanes_mask2 L); bytes_ok_tac)
  | |- context [ Z.land (le_of_bytes ?L) 4278190080 ] =>
      let y := eval cbv -[sx_lane] in (nth 3 L 0) in
      replace (Z.land (le_of_bytes L) 4278190080) with (le_of_bytes [0; 0; 0; y]) by (symmetry; apply (lanes_mask3 L); bytes_ok_tac)
  | |- context [ Z.land (le_of_bytes ?L) 255 ] =>
      let y := eval cbv -[sx_lane] in (nth 0 L 0) in
      replace (Z.land (le_of_bytes L) 255) with (le_of_bytes [y]) by (symmetry; apply (lanes_mask0 L); bytes_ok_tac)
  | |- context [ bv_wrap 32 (le_of_bytes ?L) ] =>
      let L2 := eval cbv -[sx_lane] in (firstn 4 L) in
      replace (bv_wrap 32 (le_of_bytes L)) with (le_of_bytes L2) by (symmetry; apply (lanes_wrap32 L); bytes_ok_tac)
  | |- context [ (le_of_bytes ?L) mod 18446744073709551616 ] =>
      let L2 := eval cbv -[sx_lane] in (firstn 8 L) in
      replace ((le_of_bytes L) mod 18446744073709551616) with (le_of_bytes L2) by (symmetry; apply (lanes_mod64 L); bytes_ok_tac)
  | |- context [ (bv_swrap 32 (le_of_bytes [?a; ?b; ?e; ?f])) mod 18446744073709551616 ] =>
      rewrite (lanes_swrap4 a b e f) by (fastfirst (first [assumption | apply sx_lane_range | lia]))
  | |- context [ bv_swrap 32 (Z.shiftl (le_of_bytes ?L) ?n) ] =>
      let k := eval cbv in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (firstn 4 (repeat 0 k ++ L)) in
      replace (bv_swrap 32 (Z.shiftl (le_of_bytes L) n)) with (bv_swrap 32 (le_of_bytes L2))
        by (symmetry; apply (lanes_swrap_shl k L n); [bytes_ok_tac | reflexivity])
  | |- context [ bv_swrap 32 (le_of_bytes (?a :: ?b :: ?e :: ?f :: _ :: _)) ] =>
      lazymatch goal with |- context [ bv_swrap 32 (le_of_bytes ?L) ] =>
        let L2 := eval cbv -[sx_lane] in (firstn 4 L) in
        replace (bv_swrap 32 (le_of_bytes L)) with (bv_swrap 32 (le_of_bytes L2))
          by (symmetry; apply (lanes_swrap_any L); [bytes_ok_tac | cbn; lia]) end
  | |- context [ (bv_swrap 32 (le_of_bytes ?L)) mod 18446744073709551616 ] =>
      replace ((bv_swrap 32 (le_of_bytes L)) mod 18446744073709551616) with (le_of_bytes L)
        by (symmetry; apply (lanes_swrap_small L); [bytes_ok_tac | cbn; lia])
  | |- context [ Z.lor (le_of_bytes ?L1) (le_of_bytes ?L2) ] =>
      let L := lanes_merge_compute L1 L2 in
      replace (Z.lor (le_of_bytes L1) (le_of_bytes L2)) with (le_of_bytes L)
        by (symmetry; apply (lanes_lor L1 L2 L); [lanes_merge_tac | bytes_ok_tac | bytes_ok_tac])
  | |- context [ bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [?x0; ?x1; ?x2; ?x3]))) ] =>
      rewrite (lanes_sx32 x0 x1 x2 x3) by lia
  end.

(* [comment removed for export] *)
Ltac bswap_arith :=
  repeat lanes_step;
  first [ rewrite lanes_mod32 by bytes_ok_tac | rewrite lanes_mod16 by bytes_ok_tac | idtac ];
  cbn [firstn le_of_bytes]; lia.

(* [comment removed for export] *)
Example bswap_arith_ex1 : forall x0 x1 x2 x3 X,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> X = le_of_bytes [x0; x1; x2; x3] ->
  (Z.lor (Z.lor ((Z.shiftl X 24) mod 18446744073709551616) (Z.land ((Z.shiftl X 8) mod 18446744073709551616) 16711680))
          (Z.lor (Z.land (Z.shiftr X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 X) 24)) mod 18446744073709551616))) mod 2^32
  = x3 + 256 * x2 + 65536 * x1 + 16777216 * x0.
Proof. intros. subst X. bswap_arith. Qed.

(* [comment removed for export] *)
Example bswap_arith_ex1s : forall x0 x1 x2 x3 X,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> X = bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [x0; x1; x2; x3]))) ->
  (Z.lor (Z.lor ((Z.shiftl X 24) mod 18446744073709551616) ((Z.shiftl (Z.land X 65280) 8) mod 18446744073709551616))
         (Z.lor (Z.land (Z.shiftr X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 X) 24)) mod 18446744073709551616))) mod 2^32
  = x3 + 256 * x2 + 65536 * x1 + 16777216 * x0.
Proof. intros. subst X. bswap_arith. Qed.

(* [comment removed for export] *)
Example bswap_arith_ex2 : forall x0 x1 x2 x3 x4 x5 x6 x7 X0 X1,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  0 <= x4 < 256 -> 0 <= x5 < 256 -> 0 <= x6 < 256 -> 0 <= x7 < 256 ->
  X0 = le_of_bytes [x0; x1; x2; x3] -> X1 = le_of_bytes [x4; x5; x6; x7] ->
  (Z.shiftr (Z.lor (Z.lor ((Z.shiftl X0 56) mod 18446744073709551616) ((Z.shiftl (Z.land X0 65280) 40) mod 18446744073709551616))
       (Z.lor ((Z.shiftl (Z.land (Z.lor ((Z.shiftl X1 32) mod 18446744073709551616) X0) 16711680) 24) mod 18446744073709551616)
             ((Z.shiftl ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.lor ((Z.shiftl X1 32) mod 18446744073709551616) X0)) 24)) mod 18446744073709551616) 32) mod 18446744073709551616))) 32) mod 2^32
  = x3 + 256 * x2 + 65536 * x1 + 16777216 * x0.
Proof. intros. subst X0 X1. bswap_arith. Qed.

(* [comment removed for export] *)
Example bswap_arith_ex3 : forall x0 x1 x2 x3 X,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> X = le_of_bytes [x0; x1; x2; x3] ->
  Z.lor (Z.lor ((bv_swrap 32 (Z.shiftl X 24)) mod 18446744073709551616) ((Z.shiftl (Z.land X 65280) 8) mod 18446744073709551616))
        (Z.lor (Z.land (Z.shiftr X 8) 65280) (Z.shiftr X 24))
  = le_of_bytes [x3; x2; x1; x0; sx_lane x0; sx_lane x0; sx_lane x0; sx_lane x0].
Proof. intros. subst X. repeat lanes_step. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma swrap32_mod32 : forall x, bv_swrap 32 (x mod 2^32) = bv_swrap 32 x.
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_add_mod64_l : forall x y, bv_swrap 32 ((bv_swrap 32 x) mod 18446744073709551616 + y) = bv_swrap 32 (x + y).
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_add_mod64_r : forall x y, bv_swrap 32 (y + (bv_swrap 32 x) mod 18446744073709551616) = bv_swrap 32 (y + x).
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma Z_to_bv64_mod : forall x, Z_to_bv 64 (x mod 18446744073709551616) = Z_to_bv 64 x.
Proof. intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. apply Z.mod_mod. lia. Qed.
Lemma unsigned_RF : forall x, bv_unsigned (Z_to_bv 64 (bv_swrap 32 x)) = (bv_swrap 32 x) mod 18446744073709551616.
Proof. intros. rewrite unsigned_lit_wrap. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sat_idiom : forall a b,
  Z_to_bv 64 (Z.lor ((0 - Z.b2z ((bv_swrap 32 (a + b)) mod 18446744073709551616 <? (bv_swrap 32 a) mod 18446744073709551616)) mod 18446744073709551616)
                    ((bv_swrap 32 (a + b)) mod 18446744073709551616))
  = Z_to_bv 64 (bv_swrap 32 (u_int_sum (a mod 2^32) (b mod 2^32))).
Proof.
  intros a b.
  pose proof (ltu_swrap_swrap (a + b) a) as E. rewrite bv_ltu_Z, !unsigned_RF in E. rewrite E. clear E.
  unfold u_int_sum, UINT_MAX.
  pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound b (2^32) ltac:(lia)).
  destruct (Z.leb_spec (b mod 2^32) (2^32 - 1 - a mod 2^32)).
  - replace ((a + b) mod 2^32 <? a mod 2^32) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
    cbn [Z.b2z Z.sub]. rewrite Z.lor_0_l. rewrite Z_to_bv64_mod. f_equal.
    rewrite !bv_swrap32_eq. Z.div_mod_to_equations; lia.
  - replace ((a + b) mod 2^32 <? a mod 2^32) with true by (symmetry; apply Z.ltb_lt; Z.div_mod_to_equations; lia).
    cbn [Z.b2z]. change ((0 - 1) mod 18446744073709551616) with (Z.ones 64).
    rewrite Z.lor_comm, Z.lor_ones_low; [apply bv_eq; vm_compute; reflexivity | |].
    + apply Z.mod_pos_bound. lia.
    + destruct (Z.eq_dec ((bv_swrap 32 (a + b)) mod 18446744073709551616) 0) as [-> | NZ]; [cbn; lia|].
      apply Z.log2_lt_pow2; [pose proof (Z.mod_pos_bound (bv_swrap 32 (a + b)) 18446744073709551616); lia|].
      change (2 ^ 64) with 18446744073709551616. apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)
Lemma u_int_sum_range : forall a b, 0 <= a < 2^32 -> 0 <= b < 2^32 -> 0 <= u_int_sum a b < 2^32.
Proof. intros. unfold u_int_sum, UINT_MAX. destruct (Z.leb_spec b (2^32 - 1 - a)); lia. Qed.

(* [comment removed for export] *)
Lemma zslice_length_le : forall {A} off n (d : list A), 0 <= n -> (length (zslice off n d) <= Z.to_nat n)%nat.
Proof. intros. unfold zslice, zfirstn. rewrite length_firstn. lia. Qed.
Lemma get_le32_range : forall d k, Forall (fun x => 0 <= x < 256) d -> 0 <= get_le32 d k < 2^32.
Proof.
  intros d k HF. unfold get_le32.
  pose proof (le_of_bytes_range (zslice k 4 d) (zslice_range k 4 d HF)) as R.
  pose proof (zslice_length_le k 4 d ltac:(lia)) as L.
  assert (256 ^ Z.of_nat (length (zslice k 4 d)) <= 256 ^ 4) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma get_le16_range : forall d k, Forall (fun x => 0 <= x < 256) d -> 0 <= get_le16 d k < 65536.
Proof.
  intros d k HF. unfold get_le16.
  pose proof (le_of_bytes_range (zslice k 2 d) (zslice_range k 2 d HF)) as R.
  pose proof (zslice_length_le k 2 d ltac:(lia)) as L.
  assert (256 ^ Z.of_nat (length (zslice k 2 d)) <= 256 ^ 2) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma get_u8_range : forall d k, Forall (fun x => 0 <= x < 256) d -> 0 <= get_u8 d k < 256.
Proof.
  intros d k HF. unfold get_u8, znth. destruct (k <? 0); [lia|].
  destruct (nth_in_or_default (Z.to_nat k) d 0) as [HI | ->]; [|lia].
  rewrite Forall_forall in HF. apply HF. exact HI.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_128 : forall x, 0 <= x < 256 -> Z.land x 128 = (if x <? 128 then 0 else 128).
Proof.
  intros x Hx. change 128 with (2^7) at 1. rewrite land_single_bit by lia.
  change (2^(7+1)) with 256. change (2^7) with 128. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma signed_negZ : forall x, -2^63 <= x < 0 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 64) with 64. change (2^64 `div` 2) with (2^63). Z.div_mod_to_equations. lia.
Qed.
Lemma lts_negZ : forall x y, -2^63 <= x < 0 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros. unfold bv_lts. rewrite signed_negZ, signed_small by lia. apply Z.ltb_lt. lia. Qed.
Lemma le4_swrap : forall v, le4 (Z_to_bv 64 (bv_swrap 32 v)) = le4 (Z_to_bv 64 v).
Proof.
  intros v. unfold le4. rewrite !unsigned_lit_wrap.
  rewrite <- (Z_to_le_bytes_mod 4 ((bv_swrap 32 v) mod 2^64) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (v mod 2^64) 32) by (cbn; lia). f_equal.
  rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia.
Qed.
Lemma rw_cells_ext : forall segs m A cs cs', cells_bytes cs = cells_bytes cs' -> cells_size cs = cells_size cs' -> cells_wf cs' ->
  rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' EB ES WF [[_ B] W]. split; [split; [exact WF|]|].
  - rewrite <- EB. exact B.
  - rewrite <- ES. exact W.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_3 : forall v, 0 <= v -> Z.land v 3 = v mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_65532 : forall v, 0 <= v -> Z.land v 65532 = v mod 65536 - v mod 4.
Proof.
  intros v Hv.
  assert (E : Z.land v 65532 = Z.ldiff (Z.land v (Z.ones 16)) (Z.ones 2)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, !Z.land_spec.
    change 65532 with (Z.ldiff (Z.ones 16) (Z.ones 2)). rewrite Z.ldiff_spec. rewrite Bool.andb_assoc. reflexivity. }
  rewrite E, Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^16) with 65536. change (2^2) with 4. Z.div_mod_to_equations. lia.
Qed.
Lemma shlr48 : forall v, 0 <= v -> Z.shiftr ((Z.shiftl v 48) mod 18446744073709551616) 48 = v mod 65536.
Proof. intros. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_sub_mod64_l : forall x y, bv_swrap 32 ((bv_swrap 32 x) mod 18446744073709551616 - y) = bv_swrap 32 (x - y).
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)
Lemma swap16_val : forall x0 x1, 0 <= x0 < 256 -> 0 <= x1 < 256 ->
  Z.lor ((Z.shiftl (x0 + 256 * x1) 8) mod 18446744073709551616) (Z.shiftr (x0 + 256 * x1) 8) = x1 + 256 * x0 + 65536 * x1.
Proof.
  intros x0 x1 H0 H1. replace (x0 + 256 * x1) with (le_of_bytes [x0; x1]) by (cbn; lia).
  repeat lanes_step. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma tlv_pair : forall p p2 d x0 x1 x2 x3, 0 <= p -> p + 4 <= Z.of_nat (length d) -> p2 = p + 2 ->
  zslice p 2 d = [x0; x1] -> zslice p2 2 d = [x2; x3] ->
  buf_write_at p2 [x3; x2] (buf_write_at p [x1; x0] d) = swap_field 2 p (swap_field 2 p2 d).
Proof.
  intros p p2 d x0 x1 x2 x3 Hp Hl -> E0 E1. unfold swap_field.
  rewrite E1. cbn [rev app].
  rewrite (zslice_write_other (p + 2) [x3; x2] d p 2) by (cbn [length]; lia). rewrite E0. cbn [rev app].
  apply buf_write_at_comm; cbn [length]; lia.
Qed.
Lemma tlv_pair_size : forall p p2 d x0 x1 x2 x3, 0 <= p -> p + 4 <= Z.of_nat (length d) -> p2 = p + 2 ->
  get_le16 (buf_write_at p2 [x3; x2] (buf_write_at p [x1; x0] d)) p = x1 + 256 * x0.
Proof.
  intros p p2 d x0 x1 x2 x3 Hp Hl ->. unfold get_le16.
  rewrite (zslice_write_other (p + 2) [x3; x2] _ p 2) by (cbn [length]; rewrite ?buf_write_at_length; cbn [length]; lia).
  pose proof (zslice_write_same p [x1; x0] d Hp ltac:(cbn [length]; lia)) as E. change (Z.of_nat (length [x1; x0])) with 2 in E.
  rewrite E. cbn. lia.
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma znth_nonneg_nth : forall l i, 0 <= i -> znth l i = nth (Z.to_nat i) l 0.
Proof. intros l i Hi. unfold znth. replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma zlist_ext : forall (l1 l2 : list Z), length l1 = length l2 ->
  (forall i, 0 <= i < Z.of_nat (length l1) -> znth l1 i = znth l2 i) -> l1 = l2.
Proof.
  intros l1 l2 HL HE. apply (nth_ext l1 l2 0 0 HL). intros n Hn.
  specialize (HE (Z.of_nat n) ltac:(lia)). rewrite !znth_nonneg_nth, !Nat2Z.id in HE by lia. exact HE.
Qed.

Lemma znth_app : forall (l1 l2 : list Z) i, 0 <= i ->
  znth (l1 ++ l2) i = if i <? Z.of_nat (length l1) then znth l1 i else znth l2 (i - Z.of_nat (length l1)).
Proof.
  intros l1 l2 i Hi. destruct (Z.ltb_spec i (Z.of_nat (length l1))); rewrite !znth_nonneg_nth by lia.
  - apply app_nth1. lia.
  - rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma nth_firstn_any : forall (l : list Z) k i, (i < k)%nat -> nth i (firstn k l) 0 = nth i l 0.
Proof.
  intros l k i Hik. revert l k Hik. induction i as [|i IH]; intros l k Hik.
  - destruct k; [lia|]. destruct l; reflexivity.
  - destruct k; [lia|]. destruct l; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma znth_zfirstn : forall n (l : list Z) i, 0 <= i < n -> znth (zfirstn n l) i = znth l i.
Proof. intros n l i Hi. rewrite !znth_nonneg_nth by lia. unfold zfirstn. apply nth_firstn_any. lia. Qed.

Lemma znth_zskipn : forall n (l : list Z) i, 0 <= n -> 0 <= i -> znth (zskipn n l) i = znth l (n + i).
Proof. intros n l i Hn Hi. rewrite !znth_nonneg_nth by lia. unfold zskipn. rewrite nth_skipn. f_equal. lia. Qed.

Lemma znth_over : forall (l : list Z) i, Z.of_nat (length l) <= i -> znth l i = 0.
Proof. intros l i Hi. rewrite znth_nonneg_nth by lia. apply nth_overflow. lia. Qed.

Lemma zfirstn_length_le : forall n (l : list Z), 0 <= n <= Z.of_nat (length l) -> length (zfirstn n l) = Z.to_nat n.
Proof. intros. unfold zfirstn. rewrite length_firstn. lia. Qed.
Lemma zskipn_length : forall n (l : list Z), length (zskipn n l) = (length l - Z.to_nat n)%nat.
Proof. intros. unfold zskipn. apply length_skipn. Qed.

(* [comment removed for export] *)
Lemma znth_buf_write_at : forall off l d i, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) -> 0 <= i ->
  znth (buf_write_at off l d) i =
  if (off <=? i) && (i <? off + Z.of_nat (length l)) then znth l (i - off) else znth d i.
Proof.
  intros off l d i Ho Hl Hi. unfold buf_write_at, zlength.
  rewrite znth_app by lia. rewrite zfirstn_length_le by lia.
  destruct (Z.ltb_spec i (Z.of_nat (Z.to_nat off))).
  - replace (off <=? i) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb]. apply znth_zfirstn. lia.
  - replace (off <=? i) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    rewrite znth_app by lia. destruct (Z.ltb_spec (i - Z.of_nat (Z.to_nat off)) (Z.of_nat (length l))).
    + replace (i <? off + Z.of_nat (length l)) with true by (symmetry; apply Z.ltb_lt; lia). f_equal. lia.
    + replace (i <? off + Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite znth_zskipn by lia. f_equal. lia.
Qed.

Lemma znth_zslice : forall off n (d : list Z) j, 0 <= off -> 0 <= j < n ->
  znth (zslice off n d) j = znth d (off + j).
Proof. intros. unfold zslice. rewrite znth_zfirstn by lia. apply znth_zskipn; lia. Qed.

Lemma znth_rev : forall (l : list Z) j, 0 <= j < Z.of_nat (length l) -> znth (rev l) j = znth l (Z.of_nat (length l) - 1 - j).
Proof.
  intros l j Hj. rewrite !znth_nonneg_nth by lia.
  rewrite rev_nth by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_u8_write_other : forall off l d j, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) -> 0 <= j ->
  (j < off \/ off + Z.of_nat (length l) <= j) ->
  get_u8 (buf_write_at off l d) j = get_u8 d j.
Proof.
  intros off l d j Ho Hl Hj Hd. unfold get_u8. rewrite znth_buf_write_at by lia.
  destruct Hd; [replace (off <=? j) with false by (symmetry; apply Z.leb_gt; lia)
              | replace (j <? off + Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; lia); rewrite Bool.andb_false_r];
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zslice_write_other : forall off l d a n, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
  0 <= a -> 0 <= n -> a + n <= Z.of_nat (length d) ->
  (a + n <= off \/ off + Z.of_nat (length l) <= a) ->
  zslice a n (buf_write_at off l d) = zslice a n d.
Proof.
  intros off l d a n Ho Hl Ha Hn Han Hd.
  apply zlist_ext.
  - rewrite !zslice_length; rewrite ?buf_write_at_length; lia.
  - intros i Hi. rewrite zslice_length in Hi by (rewrite ?buf_write_at_length; lia).
    rewrite !znth_zslice by lia. rewrite znth_buf_write_at by lia.
    destruct Hd.
    + replace (off <=? a + i) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    + replace (a + i <? off + Z.of_nat (length l)) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zslice_write_same : forall off l d, 0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length d) ->
  zslice off (Z.of_nat (length l)) (buf_write_at off l d) = l.
Proof.
  intros off l d Ho Hl. apply zlist_ext.
  - rewrite zslice_length; rewrite ?buf_write_at_length; lia.
  - intros i Hi. rewrite zslice_length in Hi by (rewrite ?buf_write_at_length; lia).
    rewrite znth_zslice by lia. rewrite znth_buf_write_at by lia.
    replace (off <=? off + i) with true by (symmetry; apply Z.leb_le; lia).
    replace (off + i <? off + Z.of_nat (length l)) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. f_equal. lia.
Qed.

Lemma get_u8_swap_other : forall k off d j, 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) -> 0 <= j ->
  (j < off \/ off + k <= j) -> get_u8 (swap_field k off d) j = get_u8 d j.
Proof.
  intros k off d j Ho Hk Hl Hj Hd. unfold swap_field.
  apply get_u8_write_other; rewrite ?length_rev, ?zslice_length; lia.
Qed.
Lemma get_le32_swap_other : forall k off d a, 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) -> 0 <= a -> a + 4 <= Z.of_nat (length d) ->
  (a + 4 <= off \/ off + k <= a) -> get_le32 (swap_field k off d) a = get_le32 d a.
Proof.
  intros k off d a Ho Hk Hl Ha Ha4 Hd. unfold get_le32, swap_field. f_equal.
  apply zslice_write_other; rewrite ?length_rev, ?zslice_length; lia.
Qed.
Lemma get_le16_swap_other : forall k off d a, 0 <= off -> 0 <= k -> off + k <= Z.of_nat (length d) -> 0 <= a -> a + 2 <= Z.of_nat (length d) ->
  (a + 2 <= off \/ off + k <= a) -> get_le16 (swap_field k off d) a = get_le16 d a.
Proof.
  intros k off d a Ho Hk Hl Ha Ha2 Hd. unfold get_le16, swap_field. f_equal.
  apply zslice_write_other; rewrite ?length_rev, ?zslice_length; lia.
Qed.
Lemma get_u8_write_other' : forall off l d j n, length l = n -> 0 <= off -> off + Z.of_nat n <= Z.of_nat (length d) -> 0 <= j ->
  (j < off \/ off + Z.of_nat n <= j) -> get_u8 (buf_write_at off l d) j = get_u8 d j.
Proof. intros off l d j n <-. apply get_u8_write_other. Qed.

(* [comment removed for export] *)
Lemma get_le32_write_same : forall off d y0 y1 y2 y3, 0 <= off -> off + 4 <= Z.of_nat (length d) ->
  get_le32 (buf_write_at off [y0; y1; y2; y3] d) off = y0 + 256 * y1 + 65536 * y2 + 16777216 * y3.
Proof.
  intros off d y0 y1 y2 y3 Ho Hl. unfold get_le32.
  pose proof (zslice_write_same off [y0; y1; y2; y3] d Ho ltac:(cbn [length]; lia)) as E. change (Z.of_nat (length [y0; y1; y2; y3])) with 4 in E.
  rewrite E. cbn. lia.
Qed.
Lemma get_le16_write_same : forall off d y0 y1, 0 <= off -> off + 2 <= Z.of_nat (length d) ->
  get_le16 (buf_write_at off [y0; y1] d) off = y0 + 256 * y1.
Proof.
  intros off d y0 y1 Ho Hl. unfold get_le16.
  pose proof (zslice_write_same off [y0; y1] d Ho ltac:(cbn [length]; lia)) as E. change (Z.of_nat (length [y0; y1])) with 2 in E.
  rewrite E. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma buf_write_at_comm : forall o1 l1 o2 l2 d, 0 <= o1 -> 0 <= o2 ->
  o1 + Z.of_nat (length l1) <= Z.of_nat (length d) -> o2 + Z.of_nat (length l2) <= Z.of_nat (length d) ->
  (o1 + Z.of_nat (length l1) <= o2 \/ o2 + Z.of_nat (length l2) <= o1) ->
  buf_write_at o2 l2 (buf_write_at o1 l1 d) = buf_write_at o1 l1 (buf_write_at o2 l2 d).
Proof.
  intros o1 l1 o2 l2 d H1 H2 L1 L2 D. apply zlist_ext.
  - rewrite !buf_write_at_length; rewrite ?buf_write_at_length; lia.
  - intros i Hi. rewrite !buf_write_at_length in Hi by (rewrite ?buf_write_at_length; lia).
    rewrite !znth_buf_write_at by (rewrite ?buf_write_at_length; lia).
    destruct (Z.leb_spec o2 i); destruct (Z.ltb_spec i (o2 + Z.of_nat (length l2)));
    destruct (Z.leb_spec o1 i); destruct (Z.ltb_spec i (o1 + Z.of_nat (length l1))); cbn [andb]; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma swap8_split : forall off off4 d x0 x1 x2 x3 x4 x5 x6 x7, 0 <= off -> off + 8 <= Z.of_nat (length d) -> off4 = off + 4 ->
  zslice off 4 d = [x0; x1; x2; x3] -> zslice off4 4 d = [x4; x5; x6; x7] ->
  buf_write_at off4 [x3; x2; x1; x0] (buf_write_at off [x7; x6; x5; x4] d) = swap_field 8 off d.
Proof.
  intros off off4 d x0 x1 x2 x3 x4 x5 x6 x7 Ho Hl -> E0 E1.
  pose proof (get_u8_of_slice4 off d _ _ _ _ Ho ltac:(lia) E0) as (A0 & A1 & A2 & A3).
  pose proof (get_u8_of_slice4 (off + 4) d _ _ _ _ ltac:(lia) ltac:(lia) E1) as (A4 & A5 & A6 & A7). unfold get_u8 in *.
  unfold swap_field. apply zlist_ext.
  - rewrite !buf_write_at_length; cbn [length]; rewrite ?buf_write_at_length, ?length_rev, ?zslice_length; cbn [length]; lia.
  - intros i Hi. rewrite !buf_write_at_length in Hi by (cbn [length]; rewrite ?buf_write_at_length; cbn [length]; lia).
    rewrite !znth_buf_write_at by (cbn [length]; rewrite ?buf_write_at_length, ?length_rev, ?zslice_length; cbn [length]; lia).
    cbn [length]. rewrite length_rev, zslice_length by lia.
    destruct (Z.leb_spec (off + 4) i); destruct (Z.ltb_spec i (off + 4 + Z.of_nat 4));
    destruct (Z.leb_spec off i); destruct (Z.ltb_spec i (off + Z.of_nat 4)); destruct (Z.ltb_spec i (off + Z.of_nat (Z.to_nat 8)));
    cbn [andb]; try reflexivity; try lia.
    + rewrite znth_rev by (rewrite zslice_length; lia). rewrite zslice_length by lia. rewrite znth_zslice by lia.
      assert (C : i - (off + 4) = 0 \/ i - (off + 4) = 1 \/ i - (off + 4) = 2 \/ i - (off + 4) = 3) by lia.
      destruct C as [C|[C|[C|C]]]; rewrite C; cbn -[Z.add Z.sub Z.of_nat];
      [rewrite <- A3 | rewrite <- A2 | rewrite <- A1 | rewrite <- A0]; f_equal; lia.
    + rewrite znth_rev by (rewrite zslice_length; lia). rewrite zslice_length by lia. rewrite znth_zslice by lia.
      assert (C : i - off = 0 \/ i - off = 1 \/ i - off = 2 \/ i - off = 3) by lia.
      destruct C as [C|[C|[C|C]]]; rewrite C; cbn -[Z.add Z.sub Z.of_nat];
      [rewrite <- A7 | rewrite <- A6 | rewrite <- A5 | rewrite <- A4]; f_equal; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le4_of_lanes : forall E y0 y1 y2 y3,
  E mod 2^32 = y0 + 256 * y1 + 65536 * y2 + 16777216 * y3 ->
  0 <= y0 < 256 -> 0 <= y1 < 256 -> 0 <= y2 < 256 -> 0 <= y3 < 256 ->
  le4 (Z_to_bv 64 E) = zbytes [y0; y1; y2; y3].
Proof.
  intros E y0 y1 y2 y3 HE H0 H1 H2 H3. apply le4_of_mod32; [reflexivity|].
  cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^32 * 2^32). change (bv_modulus 8) with 256.
  rewrite Z.rem_mul_r, HE by lia. rewrite !(Z.mod_small _ 256) by lia. lia.
Qed.
Lemma le2_of_lanes : forall E y0 y1,
  E mod 2^16 = y0 + 256 * y1 -> 0 <= y0 < 256 -> 0 <= y1 < 256 ->
  le2 (Z_to_bv 64 E) = zbytes [y0; y1].
Proof.
  intros E y0 y1 HE H0 H1. apply le2_of_mod16; [reflexivity|].
  cbn [zbytes map le_val]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^16 * 2^48). change (bv_modulus 8) with 256.
  rewrite Z.rem_mul_r, HE by lia. rewrite !(Z.mod_small _ 256) by lia. lia.
Qed.

(* [comment removed for export] *)
Definition bytes_ok (L : list Z) : Prop := Forall (fun x => 0 <= x < 256) L.

Lemma le_of_bytes_range : forall L, bytes_ok L -> 0 <= le_of_bytes L < 256 ^ (Z.of_nat (length L)).
Proof.
  induction L as [|x L IH]; intros HB; cbn [le_of_bytes length].
  - lia.
  - apply Forall_cons_iff in HB as [Hx HB]. specialize (IH HB). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma le_of_bytes_app : forall L1 L2, le_of_bytes (L1 ++ L2) = le_of_bytes L1 + 256 ^ (Z.of_nat (length L1)) * le_of_bytes L2.
Proof.
  induction L1 as [|x L1 IH]; intros L2; cbn [le_of_bytes app length].
  - lia.
  - rewrite IH. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma le_of_bytes_repeat0 : forall k L, le_of_bytes (repeat 0 k ++ L) = 256 ^ (Z.of_nat k) * le_of_bytes L.
Proof.
  intros k L. rewrite le_of_bytes_app, repeat_length.
  replace (le_of_bytes (repeat 0 k)) with 0; [lia|]. induction k; cbn; lia.
Qed.

Lemma bytes_ok_firstn : forall n L, bytes_ok L -> bytes_ok (firstn n L).
Proof. intros. unfold bytes_ok. rewrite <- (firstn_skipn n L) in H. apply Forall_app in H. tauto. Qed.
Lemma bytes_ok_skipn : forall n L, bytes_ok L -> bytes_ok (skipn n L).
Proof. intros. unfold bytes_ok. rewrite <- (firstn_skipn n L) in H. apply Forall_app in H. tauto. Qed.

Lemma le_of_bytes_split : forall n L, le_of_bytes L = le_of_bytes (firstn n L) + 256 ^ (Z.of_nat (length (firstn n L))) * le_of_bytes (skipn n L).
Proof. intros n L. rewrite <- (firstn_skipn n L) at 1. apply le_of_bytes_app. Qed.

(* [comment removed for export] *)
Lemma lanes_mod : forall n L, bytes_ok L -> le_of_bytes L mod 256 ^ (Z.of_nat n) = le_of_bytes (firstn n L).
Proof.
  intros n L HB. rewrite (le_of_bytes_split n L).
  pose proof (le_of_bytes_range (firstn n L) (bytes_ok_firstn n L HB)) as R.
  destruct (Nat.le_gt_cases (length L) n).
  - rewrite firstn_all2, skipn_all2 by lia. cbn [le_of_bytes]. rewrite Z.mul_0_r, Z.add_0_r.
    apply Z.mod_small. pose proof (le_of_bytes_range L HB). rewrite firstn_all2 in R by lia.
    assert (256 ^ Z.of_nat (length L) <= 256 ^ Z.of_nat n) by (apply Z.pow_le_mono_r; lia). lia.
  - rewrite length_firstn in *. rewrite Nat.min_l in * by lia.
    set (A := le_of_bytes (firstn n L)) in *. set (B := le_of_bytes (skipn n L)) in *. set (P := 256 ^ Z.of_nat n) in *.
    replace (A + P * B) with (A + B * P) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma lanes_mod64 : forall L, bytes_ok L -> le_of_bytes L mod 18446744073709551616 = le_of_bytes (firstn 8 L).
Proof. intros. change 18446744073709551616 with (256 ^ Z.of_nat 8). apply lanes_mod. assumption. Qed.
Lemma lanes_mod32 : forall L, bytes_ok L -> le_of_bytes L mod 2^32 = le_of_bytes (firstn 4 L).
Proof. intros. change (2^32) with (256 ^ Z.of_nat 4). apply lanes_mod. assumption. Qed.
Lemma lanes_mod16 : forall L, bytes_ok L -> le_of_bytes L mod 2^16 = le_of_bytes (firstn 2 L).
Proof. intros. change (2^16) with (256 ^ Z.of_nat 2). apply lanes_mod. assumption. Qed.
Lemma lanes_wrap32 : forall L, bytes_ok L -> bv_wrap 32 (le_of_bytes L) = le_of_bytes (firstn 4 L).
Proof. intros. rewrite bv_wrap32_eq. apply lanes_mod32. assumption. Qed.

(* [comment removed for export] *)
Lemma lanes_shl : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  (Z.shiftl (le_of_bytes L) n) mod 18446744073709551616 = le_of_bytes (firstn 8 (repeat 0 k ++ L)).
Proof.
  intros k L n HB ->. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite <- lanes_mod64 by (unfold bytes_ok; apply Forall_app; split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia| exact HB]).
  rewrite le_of_bytes_repeat0. rewrite Z.pow_mul_r by lia. change (2^8) with 256. f_equal. lia.
Qed.
Lemma lanes_shl_nomod : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  Z.shiftl (le_of_bytes L) n = le_of_bytes (repeat 0 k ++ L).
Proof.
  intros k L n HB ->. rewrite Z.shiftl_mul_pow2 by lia. rewrite le_of_bytes_repeat0. rewrite Z.pow_mul_r by lia.
  change (2^8) with 256. lia.
Qed.
Lemma lanes_shr : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  Z.shiftr (le_of_bytes L) n = le_of_bytes (skipn k L).
Proof.
  intros k L n HB ->. rewrite Z.shiftr_div_pow2 by lia. rewrite (le_of_bytes_split k L) at 1.
  pose proof (le_of_bytes_range (firstn k L) (bytes_ok_firstn k L HB)) as R.
  destruct (Nat.le_gt_cases (length L) k).
  - rewrite firstn_all2, skipn_all2 by lia. cbn [le_of_bytes]. rewrite Z.mul_0_r, Z.add_0_r. apply Z.div_small.
    rewrite firstn_all2 in R by lia. rewrite Z.pow_mul_r by lia. change (2^8) with 256.
    assert (256 ^ Z.of_nat (length L) <= 256 ^ Z.of_nat k) by (apply Z.pow_le_mono_r; lia). lia.
  - rewrite length_firstn in *. rewrite Nat.min_l in * by lia. rewrite Z.pow_mul_r by lia. change (2^8) with 256.
    set (A := le_of_bytes (firstn k L)) in *. set (B := le_of_bytes (skipn k L)) in *. set (P := 256 ^ Z.of_nat k) in *.
    replace (A + P * B) with (B * P + A) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma lanes_mask : forall j L, bytes_ok L ->
  Z.land (le_of_bytes L) (255 * 2 ^ (8 * Z.of_nat j)) = le_of_bytes (repeat 0 j ++ [nth j L 0]).
Proof.
  intros j L HB. rewrite land_mask8 by (pose proof (le_of_bytes_range L HB); lia).
  rewrite le_of_bytes_repeat0. cbn [le_of_bytes]. rewrite Z.mul_0_r, Z.add_0_r.
  rewrite <- Z.shiftr_div_pow2 by lia. rewrite (lanes_shr j L) by (auto; lia).
  rewrite Z.pow_mul_r by lia. change (2^8) with 256. rewrite Z.mul_comm. f_equal.
  pose proof (bytes_ok_skipn j L HB) as HS.
  destruct (skipn j L) as [|y R] eqn:E.
  - cbn. rewrite nth_overflow; [reflexivity|]. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia.
  - apply Forall_cons_iff in HS as [Hy HR]. cbn [le_of_bytes].
    replace (y + 256 * le_of_bytes R) with (y + le_of_bytes R * 256) by lia. rewrite Z.mod_add, Z.mod_small by lia.
    replace y with (nth 0 (skipn j L) 0) by (rewrite E; reflexivity). rewrite nth_skipn. f_equal. lia.
Qed.
Lemma lanes_mask1 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 65280 = le_of_bytes [0; nth 1 L 0].
Proof. intros. change 65280 with (255 * 2 ^ (8 * Z.of_nat 1)). rewrite lanes_mask by assumption. reflexivity. Qed.
Lemma lanes_mask2 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 16711680 = le_of_bytes [0; 0; nth 2 L 0].
Proof. intros. change 16711680 with (255 * 2 ^ (8 * Z.of_nat 2)). rewrite lanes_mask by assumption. reflexivity. Qed.
Lemma lanes_mask0 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 255 = le_of_bytes [nth 0 L 0].
Proof. intros. change 255 with (255 * 2 ^ (8 * Z.of_nat 0)) at 1. rewrite lanes_mask by assumption. reflexivity. Qed.
Lemma lanes_mask3 : forall L, bytes_ok L -> Z.land (le_of_bytes L) 4278190080 = le_of_bytes [0; 0; 0; nth 3 L 0].
Proof. intros. change 4278190080 with (255 * 2 ^ (8 * Z.of_nat 3)). rewrite lanes_mask by assumption. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint lanes_merge (L1 L2 L : list Z) : Prop :=
  match L1, L2, L with
  | [], l2, l => l = l2
  | l1, [], l => l = l1
  | a :: l1, b :: l2, c :: l => ((a = 0 /\ c = b) \/ (b = 0 /\ c = a)) /\ lanes_merge l1 l2 l
  | _ :: _, _ :: _, [] => False
  end.
Lemma lor_shift8 : forall a b c d, 0 <= a < 256 -> 0 <= c < 256 -> 0 <= b -> 0 <= d -> (a = 0 \/ c = 0) ->
  Z.lor (a + 256 * b) (c + 256 * d) = (Z.lor a c) + 256 * Z.lor b d.
Proof.
  intros a b c d Ha Hc Hb Hd Hz.
  assert (E1 : a + 256 * b = Z.lor (256 * b) a).
  { rewrite (lor_add (256 * b) a 8); [lia | lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia]. }
  assert (E2 : c + 256 * d = Z.lor (256 * d) c).
  { rewrite (lor_add (256 * d) c 8); [lia | lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia]. }
  rewrite E1, E2.
  transitivity (Z.lor (Z.lor (256 * b) (256 * d)) (Z.lor a c)).
  { rewrite <- !Z.lor_assoc. f_equal. rewrite (Z.lor_comm a (Z.lor (256 * d) c)). rewrite <- Z.lor_assoc. f_equal. apply Z.lor_comm. }
  assert (R : 0 <= Z.lor a c < 256).
  { destruct Hz as [-> | ->]; [rewrite Z.lor_0_l | rewrite Z.lor_0_r]; lia. }
  replace (Z.lor (256 * b) (256 * d)) with (256 * Z.lor b d).
  2:{ rewrite !(Z.mul_comm 256). change 256 with (2^8). rewrite <- !Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_lor. reflexivity. }
  pose proof (Z.lor_nonneg b d).
  rewrite (lor_add (256 * Z.lor b d) (Z.lor a c) 8); [lia | lia | change (2^8) with 256; lia | change (2^8) with 256; Z.div_mod_to_equations; lia].
Qed.
Lemma lanes_lor : forall L1 L2 L, lanes_merge L1 L2 L -> bytes_ok L1 -> bytes_ok L2 ->
  Z.lor (le_of_bytes L1) (le_of_bytes L2) = le_of_bytes L.
Proof.
  induction L1 as [|a L1 IH]; intros L2 L HM H1 H2.
  - cbn in HM. subst L. cbn [le_of_bytes]. apply Z.lor_0_l.
  - destruct L2 as [|b L2].
    + cbn in HM. subst L. apply Z.lor_0_r.
    + destruct L as [|c L]; [destruct HM|]. cbn [lanes_merge] in HM. destruct HM as [Hc HM].
      apply Forall_cons_iff in H1 as [Ha H1]. apply Forall_cons_iff in H2 as [Hb H2].
      cbn [le_of_bytes]. pose proof (le_of_bytes_range L1 H1). pose proof (le_of_bytes_range L2 H2).
      rewrite lor_shift8 by lia. rewrite (IH L2 L) by assumption. f_equal.
      destruct Hc as [[-> ->]|[-> ->]]; [apply Z.lor_0_l | apply Z.lor_0_r].
Qed.

(* [comment removed for export] *)
Definition sx_lane (x3 : Z) : Z := if x3 <? 128 then 0 else 255.
Lemma sx_lane_range : forall x, 0 <= sx_lane x < 256.
Proof. intros. unfold sx_lane. destruct (x <? 128); lia. Qed.
Lemma lanes_sx32 : forall x0 x1 x2 x3, 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [x0; x1; x2; x3]))) =
  le_of_bytes [x0; x1; x2; x3; sx_lane x3; sx_lane x3; sx_lane x3; sx_lane x3].
Proof.
  intros. cbn [le_of_bytes]. rewrite unsigned_sx32 by lia. unfold sx_lane.
  destruct (Z.ltb_spec x3 128); destruct (Z.ltb_spec (x0 + 256 * (x1 + 256 * (x2 + 256 * (x3 + 256 * 0)))) (2^31)); lia.
Qed.
(* [comment removed for export] *)
Lemma lanes_swrap_small : forall L, bytes_ok L -> (length L <= 3)%nat ->
  (bv_swrap 32 (le_of_bytes L)) mod 18446744073709551616 = le_of_bytes L.
Proof.
  intros L HB HL. pose proof (le_of_bytes_range L HB) as R.
  assert (256 ^ Z.of_nat (length L) <= 256 ^ 3) by (apply Z.pow_le_mono_r; lia).
  rewrite swrap32_small by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma lanes_swrap4 : forall a b c e, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= e < 256 ->
  (bv_swrap 32 (le_of_bytes [a; b; c; e])) mod 18446744073709551616 =
  le_of_bytes [a; b; c; e; sx_lane e; sx_lane e; sx_lane e; sx_lane e].
Proof.
  intros. cbn [le_of_bytes]. rewrite bv_swrap32_eq. unfold sx_lane.
  destruct (Z.ltb_spec e 128); Z.div_mod_to_equations; lia.
Qed.
Lemma lanes_swrap_any : forall L, bytes_ok L -> (4 < length L)%nat ->
  bv_swrap 32 (le_of_bytes L) = bv_swrap 32 (le_of_bytes (firstn 4 L)).
Proof.
  intros L HB HL. rewrite !bv_swrap32_eq. rewrite <- (lanes_mod32 L HB). Z.div_mod_to_equations. lia.
Qed.
Lemma lanes_swrap_shl : forall k L n, bytes_ok L -> n = 8 * Z.of_nat k ->
  bv_swrap 32 (Z.shiftl (le_of_bytes L) n) = bv_swrap 32 (le_of_bytes (firstn 4 (repeat 0 k ++ L))).
Proof.
  intros k L n HB ->. rewrite Z.shiftl_mul_pow2 by lia.
  assert (HB' : bytes_ok (repeat 0 k ++ L)).
  { unfold bytes_ok. apply Forall_app. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia| exact HB]. }
  replace (le_of_bytes L * 2 ^ (8 * Z.of_nat k)) with (le_of_bytes (repeat 0 k ++ L))
    by (rewrite le_of_bytes_repeat0, Z.pow_mul_r by lia; change (2^8) with 256; lia).
  rewrite !bv_swrap32_eq. rewrite <- (lanes_mod32 _ HB'). Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma ltu_lit_sx32 : forall k x, 0 <= x < 2^32 -> 0 <= k < 2^31 ->
  bv_ltu (Z_to_bv 64 k) (sx32 (Z_to_bv 64 x)) = (k <? x).
Proof.
  intros k x Hx Hk. rewrite bv_ltu_Z, unsigned_sx32, (unsigned_lit k) by lia.
  destruct (Z.ltb_spec x (2^31)); destruct (Z.ltb_spec k x); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]).
Qed.
Lemma ltu_lit_sx32_falseZ : forall k x, 0 <= x < 2^32 -> 0 <= k < 2^31 -> x <= k -> bv_ltu (Z_to_bv 64 k) (sx32 (Z_to_bv 64 x)) = false.
Proof. intros. rewrite ltu_lit_sx32 by lia. apply Z.ltb_ge. lia. Qed.
Lemma ltu_lit_sx32_trueZ : forall k x, 0 <= x < 2^32 -> 0 <= k < 2^31 -> k < x -> bv_ltu (Z_to_bv 64 k) (sx32 (Z_to_bv 64 x)) = true.
Proof. intros. rewrite ltu_lit_sx32 by lia. apply Z.ltb_lt. lia. Qed.
(* [comment removed for export] *)
Lemma sx32_as_swrap : forall x, sx32 (Z_to_bv 64 x) = Z_to_bv 64 (bv_swrap 32 x).
Proof.
  intros x. unfold sx32. rewrite unsigned_lit_wrap. f_equal. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia.
Qed.
Lemma ltu_swrap_swrap : forall x y, bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x mod 2^32 <? y mod 2^32).
Proof.
  intros x y. rewrite bv_ltu_Z, !unsigned_swrap32.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound y (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); destruct (Z.ltb_spec (y mod 2^32) (2^31)); cbv iota;
    (destruct (Z.ltb_spec (x mod 2^32) (y mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia])).
Qed.
Lemma eqb_swrap_swrap : forall x y, bv_eqb (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x mod 2^32 =? y mod 2^32).
Proof.
  intros x y. unfold bv_eqb. rewrite !unsigned_swrap32.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound y (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); destruct (Z.ltb_spec (y mod 2^32) (2^31)); cbv iota;
    (destruct (Z.eqb_spec (x mod 2^32) (y mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia])).
Qed.
Lemma eqb_swrap_small : forall x k, 0 <= k < 2^31 -> bv_eqb (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = (x mod 2^32 =? k).
Proof.
  intros x k Hk. unfold bv_eqb. rewrite unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); cbv iota; (destruct (Z.eqb_spec (x mod 2^32) k); fastfirst (first [ noevar_assumption |reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia])).
Qed.
Lemma eqb_small_swrap : forall k x, 0 <= k < 2^31 -> bv_eqb (Z_to_bv 64 k) (Z_to_bv 64 (bv_swrap 32 x)) = (k =? x mod 2^32).
Proof.
  intros k x Hk. unfold bv_eqb. rewrite unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); cbv iota; (destruct (Z.eqb_spec k (x mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia])).
Qed.
(* [comment removed for export] *)
Lemma ltu_swrap_small : forall x k, 0 <= k < 2^31 -> bv_ltu (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 k) = (x mod 2^32 <? k).
Proof. intros. apply ltu_swrap_lit. lia. Qed.
Lemma ltu_small_swrap : forall k x, 0 <= k < 2^31 -> bv_ltu (Z_to_bv 64 k) (Z_to_bv 64 (bv_swrap 32 x)) = (k <? x mod 2^32).
Proof.
  intros k x Hk. rewrite bv_ltu_Z, unsigned_swrap32, (unsigned_lit k) by lia.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); cbv iota; (destruct (Z.ltb_spec k (x mod 2^32)); fastfirst (first [ noevar_assumption |reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia])).
Qed.

Ltac bytes_ok_tac := unfold bytes_ok; repeat (apply Forall_cons; [fastfirst (first [assumption | apply sx_lane_range | lia]) |]); apply Forall_nil.

(* [comment removed for export] *)
Ltac lanes_merge_compute L1 L2 :=
  lazymatch L1 with
  | [] => L2
  | ?a :: ?l1 =>
    lazymatch L2 with
    | [] => L1
    | ?b :: ?l2 =>
      let r := lanes_merge_compute l1 l2 in
      lazymatch a with
      | 0 => constr:(b :: r)
      | _ => lazymatch b with 0 => constr:(a :: r) end
      end
    end
  end.
Ltac lanes_merge_tac := cbn [lanes_merge]; repeat split; try reflexivity;
  first [ left; split; reflexivity | right; split; reflexivity ].

(* [comment removed for export] *)
Ltac lanes_step :=
  match goal with
  | |- context [ (Z.shiftl (le_of_bytes ?L) ?n) mod 18446744073709551616 ] =>
      let k := eval cbv -[sx_lane] in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (firstn 8 (repeat 0 k ++ L)) in
      replace ((Z.shiftl (le_of_bytes L) n) mod 18446744073709551616) with (le_of_bytes L2)
        by (symmetry; apply (lanes_shl k L n); [bytes_ok_tac | reflexivity])
  | |- context [ Z.shiftl (le_of_bytes ?L) ?n ] =>
      let k := eval cbv in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (repeat 0 k ++ L) in
      replace (Z.shiftl (le_of_bytes L) n) with (le_of_bytes L2)
        by (symmetry; apply (lanes_shl_nomod k L n); [bytes_ok_tac | reflexivity])
  | |- context [ Z.shiftr (le_of_bytes ?L) ?n ] =>
      let k := eval cbv -[sx_lane] in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (skipn k L) in
      replace (Z.shiftr (le_of_bytes L) n) with (le_of_bytes L2)
        by (symmetry; apply (lanes_shr k L n); [bytes_ok_tac | reflexivity])
  | |- context [ Z.land (le_of_bytes ?L) 65280 ] =>
      let y := eval cbv -[sx_lane] in (nth 1 L 0) in
      replace (Z.land (le_of_bytes L) 65280) with (le_of_bytes [0; y]) by (symmetry; apply (lanes_mask1 L); bytes_ok_tac)
  | |- context [ Z.land (le_of_bytes ?L) 16711680 ] =>
      let y := eval cbv -[sx_lane] in (nth 2 L 0) in
      replace (Z.land (le_of_bytes L) 16711680) with (le_of_bytes [0; 0; y]) by (symmetry; apply (lanes_mask2 L); bytes_ok_tac)
  | |- context [ Z.land (le_of_bytes ?L) 4278190080 ] =>
      let y := eval cbv -[sx_lane] in (nth 3 L 0) in
      replace (Z.land (le_of_bytes L) 4278190080) with (le_of_bytes [0; 0; 0; y]) by (symmetry; apply (lanes_mask3 L); bytes_ok_tac)
  | |- context [ Z.land (le_of_bytes ?L) 255 ] =>
      let y := eval cbv -[sx_lane] in (nth 0 L 0) in
      replace (Z.land (le_of_bytes L) 255) with (le_of_bytes [y]) by (symmetry; apply (lanes_mask0 L); bytes_ok_tac)
  | |- context [ bv_wrap 32 (le_of_bytes ?L) ] =>
      let L2 := eval cbv -[sx_lane] in (firstn 4 L) in
      replace (bv_wrap 32 (le_of_bytes L)) with (le_of_bytes L2) by (symmetry; apply (lanes_wrap32 L); bytes_ok_tac)
  | |- context [ (le_of_bytes ?L) mod 18446744073709551616 ] =>
      let L2 := eval cbv -[sx_lane] in (firstn 8 L) in
      replace ((le_of_bytes L) mod 18446744073709551616) with (le_of_bytes L2) by (symmetry; apply (lanes_mod64 L); bytes_ok_tac)
  | |- context [ (bv_swrap 32 (le_of_bytes [?a; ?b; ?e; ?f])) mod 18446744073709551616 ] =>
      rewrite (lanes_swrap4 a b e f) by (fastfirst (first [assumption | apply sx_lane_range | lia]))
  | |- context [ bv_swrap 32 (Z.shiftl (le_of_bytes ?L) ?n) ] =>
      let k := eval cbv in (Z.to_nat (n / 8)) in
      let L2 := eval cbv -[sx_lane] in (firstn 4 (repeat 0 k ++ L)) in
      replace (bv_swrap 32 (Z.shiftl (le_of_bytes L) n)) with (bv_swrap 32 (le_of_bytes L2))
        by (symmetry; apply (lanes_swrap_shl k L n); [bytes_ok_tac | reflexivity])
  | |- context [ bv_swrap 32 (le_of_bytes (?a :: ?b :: ?e :: ?f :: _ :: _)) ] =>
      lazymatch goal with |- context [ bv_swrap 32 (le_of_bytes ?L) ] =>
        let L2 := eval cbv -[sx_lane] in (firstn 4 L) in
        replace (bv_swrap 32 (le_of_bytes L)) with (bv_swrap 32 (le_of_bytes L2))
          by (symmetry; apply (lanes_swrap_any L); [bytes_ok_tac | cbn; lia]) end
  | |- context [ (bv_swrap 32 (le_of_bytes ?L)) mod 18446744073709551616 ] =>
      replace ((bv_swrap 32 (le_of_bytes L)) mod 18446744073709551616) with (le_of_bytes L)
        by (symmetry; apply (lanes_swrap_small L); [bytes_ok_tac | cbn; lia])
  | |- context [ Z.lor (le_of_bytes ?L1) (le_of_bytes ?L2) ] =>
      let L := lanes_merge_compute L1 L2 in
      replace (Z.lor (le_of_bytes L1) (le_of_bytes L2)) with (le_of_bytes L)
        by (symmetry; apply (lanes_lor L1 L2 L); [lanes_merge_tac | bytes_ok_tac | bytes_ok_tac])
  | |- context [ bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [?x0; ?x1; ?x2; ?x3]))) ] =>
      rewrite (lanes_sx32 x0 x1 x2 x3) by lia
  end.

(* [comment removed for export] *)
Ltac bswap_arith :=
  repeat lanes_step;
  first [ rewrite lanes_mod32 by bytes_ok_tac | rewrite lanes_mod16 by bytes_ok_tac | idtac ];
  cbn [firstn le_of_bytes]; lia.

(* [comment removed for export] *)
Example bswap_arith_ex1 : forall x0 x1 x2 x3 X,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> X = le_of_bytes [x0; x1; x2; x3] ->
  (Z.lor (Z.lor ((Z.shiftl X 24) mod 18446744073709551616) (Z.land ((Z.shiftl X 8) mod 18446744073709551616) 16711680))
          (Z.lor (Z.land (Z.shiftr X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 X) 24)) mod 18446744073709551616))) mod 2^32
  = x3 + 256 * x2 + 65536 * x1 + 16777216 * x0.
Proof. intros. subst X. bswap_arith. Qed.

(* [comment removed for export] *)
Example bswap_arith_ex1s : forall x0 x1 x2 x3 X,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> X = bv_unsigned (sx32 (Z_to_bv 64 (le_of_bytes [x0; x1; x2; x3]))) ->
  (Z.lor (Z.lor ((Z.shiftl X 24) mod 18446744073709551616) ((Z.shiftl (Z.land X 65280) 8) mod 18446744073709551616))
         (Z.lor (Z.land (Z.shiftr X 8) 65280) ((bv_swrap 32 (Z.shiftr (bv_wrap 32 X) 24)) mod 18446744073709551616))) mod 2^32
  = x3 + 256 * x2 + 65536 * x1 + 16777216 * x0.
Proof. intros. subst X. bswap_arith. Qed.

(* [comment removed for export] *)
Example bswap_arith_ex2 : forall x0 x1 x2 x3 x4 x5 x6 x7 X0 X1,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  0 <= x4 < 256 -> 0 <= x5 < 256 -> 0 <= x6 < 256 -> 0 <= x7 < 256 ->
  X0 = le_of_bytes [x0; x1; x2; x3] -> X1 = le_of_bytes [x4; x5; x6; x7] ->
  (Z.shiftr (Z.lor (Z.lor ((Z.shiftl X0 56) mod 18446744073709551616) ((Z.shiftl (Z.land X0 65280) 40) mod 18446744073709551616))
       (Z.lor ((Z.shiftl (Z.land (Z.lor ((Z.shiftl X1 32) mod 18446744073709551616) X0) 16711680) 24) mod 18446744073709551616)
             ((Z.shiftl ((bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.lor ((Z.shiftl X1 32) mod 18446744073709551616) X0)) 24)) mod 18446744073709551616) 32) mod 18446744073709551616))) 32) mod 2^32
  = x3 + 256 * x2 + 65536 * x1 + 16777216 * x0.
Proof. intros. subst X0 X1. bswap_arith. Qed.

(* [comment removed for export] *)
Example bswap_arith_ex3 : forall x0 x1 x2 x3 X,
  0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 -> X = le_of_bytes [x0; x1; x2; x3] ->
  Z.lor (Z.lor ((bv_swrap 32 (Z.shiftl X 24)) mod 18446744073709551616) ((Z.shiftl (Z.land X 65280) 8) mod 18446744073709551616))
        (Z.lor (Z.land (Z.shiftr X 8) 65280) (Z.shiftr X 24))
  = le_of_bytes [x3; x2; x1; x0; sx_lane x0; sx_lane x0; sx_lane x0; sx_lane x0].
Proof. intros. subst X. repeat lanes_step. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma swrap32_mod32 : forall x, bv_swrap 32 (x mod 2^32) = bv_swrap 32 x.
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_add_mod64_l : forall x y, bv_swrap 32 ((bv_swrap 32 x) mod 18446744073709551616 + y) = bv_swrap 32 (x + y).
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_add_mod64_r : forall x y, bv_swrap 32 (y + (bv_swrap 32 x) mod 18446744073709551616) = bv_swrap 32 (y + x).
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma Z_to_bv64_mod : forall x, Z_to_bv 64 (x mod 18446744073709551616) = Z_to_bv 64 x.
Proof. intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. apply Z.mod_mod. lia. Qed.
Lemma unsigned_RF : forall x, bv_unsigned (Z_to_bv 64 (bv_swrap 32 x)) = (bv_swrap 32 x) mod 18446744073709551616.
Proof. intros. rewrite unsigned_lit_wrap. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sat_idiom : forall a b,
  Z_to_bv 64 (Z.lor ((0 - Z.b2z ((bv_swrap 32 (a + b)) mod 18446744073709551616 <? (bv_swrap 32 a) mod 18446744073709551616)) mod 18446744073709551616)
                    ((bv_swrap 32 (a + b)) mod 18446744073709551616))
  = Z_to_bv 64 (bv_swrap 32 (u_int_sum (a mod 2^32) (b mod 2^32))).
Proof.
  intros a b.
  pose proof (ltu_swrap_swrap (a + b) a) as E. rewrite bv_ltu_Z, !unsigned_RF in E. rewrite E. clear E.
  unfold u_int_sum, UINT_MAX.
  pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound b (2^32) ltac:(lia)).
  destruct (Z.leb_spec (b mod 2^32) (2^32 - 1 - a mod 2^32)).
  - replace ((a + b) mod 2^32 <? a mod 2^32) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
    cbn [Z.b2z Z.sub]. rewrite Z.lor_0_l. rewrite Z_to_bv64_mod. f_equal.
    rewrite !bv_swrap32_eq. Z.div_mod_to_equations; lia.
  - replace ((a + b) mod 2^32 <? a mod 2^32) with true by (symmetry; apply Z.ltb_lt; Z.div_mod_to_equations; lia).
    cbn [Z.b2z]. change ((0 - 1) mod 18446744073709551616) with (Z.ones 64).
    rewrite Z.lor_comm, Z.lor_ones_low; [apply bv_eq; vm_compute; reflexivity | |].
    + apply Z.mod_pos_bound. lia.
    + destruct (Z.eq_dec ((bv_swrap 32 (a + b)) mod 18446744073709551616) 0) as [-> | NZ]; [cbn; lia|].
      apply Z.log2_lt_pow2; [pose proof (Z.mod_pos_bound (bv_swrap 32 (a + b)) 18446744073709551616); lia|].
      change (2 ^ 64) with 18446744073709551616. apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)
Lemma u_int_sum_range : forall a b, 0 <= a < 2^32 -> 0 <= b < 2^32 -> 0 <= u_int_sum a b < 2^32.
Proof. intros. unfold u_int_sum, UINT_MAX. destruct (Z.leb_spec b (2^32 - 1 - a)); lia. Qed.

(* [comment removed for export] *)
Lemma zslice_length_le : forall {A} off n (d : list A), 0 <= n -> (length (zslice off n d) <= Z.to_nat n)%nat.
Proof. intros. unfold zslice, zfirstn. rewrite length_firstn. lia. Qed.
Lemma get_le32_range : forall d k, Forall (fun x => 0 <= x < 256) d -> 0 <= get_le32 d k < 2^32.
Proof.
  intros d k HF. unfold get_le32.
  pose proof (le_of_bytes_range (zslice k 4 d) (zslice_range k 4 d HF)) as R.
  pose proof (zslice_length_le k 4 d ltac:(lia)) as L.
  assert (256 ^ Z.of_nat (length (zslice k 4 d)) <= 256 ^ 4) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma get_le16_range : forall d k, Forall (fun x => 0 <= x < 256) d -> 0 <= get_le16 d k < 65536.
Proof.
  intros d k HF. unfold get_le16.
  pose proof (le_of_bytes_range (zslice k 2 d) (zslice_range k 2 d HF)) as R.
  pose proof (zslice_length_le k 2 d ltac:(lia)) as L.
  assert (256 ^ Z.of_nat (length (zslice k 2 d)) <= 256 ^ 2) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma get_u8_range : forall d k, Forall (fun x => 0 <= x < 256) d -> 0 <= get_u8 d k < 256.
Proof.
  intros d k HF. unfold get_u8, znth. destruct (k <? 0); [lia|].
  destruct (nth_in_or_default (Z.to_nat k) d 0) as [HI | ->]; [|lia].
  rewrite Forall_forall in HF. apply HF. exact HI.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_128 : forall x, 0 <= x < 256 -> Z.land x 128 = (if x <? 128 then 0 else 128).
Proof.
  intros x Hx. change 128 with (2^7) at 1. rewrite land_single_bit by lia.
  change (2^(7+1)) with 256. change (2^7) with 128. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma signed_negZ : forall x, -2^63 <= x < 0 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 64) with 64. change (2^64 `div` 2) with (2^63). Z.div_mod_to_equations. lia.
Qed.
Lemma lts_negZ : forall x y, -2^63 <= x < 0 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros. unfold bv_lts. rewrite signed_negZ, signed_small by lia. apply Z.ltb_lt. lia. Qed.
Lemma le4_swrap : forall v, le4 (Z_to_bv 64 (bv_swrap 32 v)) = le4 (Z_to_bv 64 v).
Proof.
  intros v. unfold le4. rewrite !unsigned_lit_wrap.
  rewrite <- (Z_to_le_bytes_mod 4 ((bv_swrap 32 v) mod 2^64) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (v mod 2^64) 32) by (cbn; lia). f_equal.
  rewrite bv_swrap32_eq. Z.div_mod_to_equations. lia.
Qed.
Lemma rw_cells_ext : forall segs m A cs cs', cells_bytes cs = cells_bytes cs' -> cells_size cs = cells_size cs' -> cells_wf cs' ->
  rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' EB ES WF [[_ B] W]. split; [split; [exact WF|]|].
  - rewrite <- EB. exact B.
  - rewrite <- ES. exact W.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_3 : forall v, 0 <= v -> Z.land v 3 = v mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_65532 : forall v, 0 <= v -> Z.land v 65532 = v mod 65536 - v mod 4.
Proof.
  intros v Hv.
  assert (E : Z.land v 65532 = Z.ldiff (Z.land v (Z.ones 16)) (Z.ones 2)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, !Z.land_spec.
    change 65532 with (Z.ldiff (Z.ones 16) (Z.ones 2)). rewrite Z.ldiff_spec. rewrite Bool.andb_assoc. reflexivity. }
  rewrite E, Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^16) with 65536. change (2^2) with 4. Z.div_mod_to_equations. lia.
Qed.
Lemma shlr48 : forall v, 0 <= v -> Z.shiftr ((Z.shiftl v 48) mod 18446744073709551616) 48 = v mod 65536.
Proof. intros. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_sub_mod64_l : forall x y, bv_swrap 32 ((bv_swrap 32 x) mod 18446744073709551616 - y) = bv_swrap 32 (x - y).
Proof. intros. rewrite !bv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)
Lemma swap16_val : forall x0 x1, 0 <= x0 < 256 -> 0 <= x1 < 256 ->
  Z.lor ((Z.shiftl (x0 + 256 * x1) 8) mod 18446744073709551616) (Z.shiftr (x0 + 256 * x1) 8) = x1 + 256 * x0 + 65536 * x1.
Proof.
  intros x0 x1 H0 H1. replace (x0 + 256 * x1) with (le_of_bytes [x0; x1]) by (cbn; lia).
  repeat lanes_step. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma tlv_pair : forall p p2 d x0 x1 x2 x3, 0 <= p -> p + 4 <= Z.of_nat (length d) -> p2 = p + 2 ->
  zslice p 2 d = [x0; x1] -> zslice p2 2 d = [x2; x3] ->
  buf_write_at p2 [x3; x2] (buf_write_at p [x1; x0] d) = swap_field 2 p (swap_field 2 p2 d).
Proof.
  intros p p2 d x0 x1 x2 x3 Hp Hl -> E0 E1. unfold swap_field.
  rewrite E1. cbn [rev app].
  rewrite (zslice_write_other (p + 2) [x3; x2] d p 2) by (cbn [length]; lia). rewrite E0. cbn [rev app].
  apply buf_write_at_comm; cbn [length]; lia.
Qed.
Lemma tlv_pair_size : forall p p2 d x0 x1 x2 x3, 0 <= p -> p + 4 <= Z.of_nat (length d) -> p2 = p + 2 ->
  get_le16 (buf_write_at p2 [x3; x2] (buf_write_at p [x1; x0] d)) p = x1 + 256 * x0.
Proof.
  intros p p2 d x0 x1 x2 x3 Hp Hl ->. unfold get_le16.
  rewrite (zslice_write_other (p + 2) [x3; x2] _ p 2) by (cbn [length]; rewrite ?buf_write_at_length; cbn [length]; lia).
  pose proof (zslice_write_same p [x1; x0] d Hp ltac:(cbn [length]; lia)) as E. change (Z.of_nat (length [x1; x0])) with 2 in E.
  rewrite E. cbn. lia.
Qed.
End TwB.
End PP_kit2.

(* [comment removed for export] *)
Module StdioKit.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte) (only parsing).

(* [comment removed for export] *)
Definition F_STDIO_READ : Z := 0x1a8d4.
Definition F_STDIO_WRITE : Z := 0x1b3f4.
Definition F_STDIO_SEEK : Z := 0x1a9ec.
Definition F_STDIO_CLOSE : Z := 0x1a8a8.
Definition F_STDOUT_WRITE : Z := 0x1bb0c.
Definition F_SYSRET : Z := 0x1861c.
(* [comment removed for export] *)
Definition A_STDOUT : Z := 0x23840.
Definition A_STDOUT_BUF : Z := 0x54570.
Definition A_STDERR : Z := 0x23660.
Definition A_STDERR_BUF : Z := 0x54160.
Definition A_STDIN : Z := 0x23750.
Definition A_STDIN_BUF : Z := 0x54168.
Definition A_OFL_LOCK : Z := 0x54148.
Definition A_OFL_HEAD : Z := 0x54150.

(* [comment removed for export] *)
Definition ssp_cells (m : mem) (canary : word) : Prop :=
  rw_cells ssegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells ssegs m ssp_guard [C8 canary].

(* [comment removed for export] *)
Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac fix_litstore :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | _ => idtac
  end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.

Lemma bv_swrap32_eq : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. intros z. reflexivity. Qed.

Lemma sx32_small : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Section Glue.
  Context {St : Type}.

  (* [comment removed for export] *)
  Lemma implM_sys_ret : forall {A} (n : node) (dec : resp -> option A) (s0 : St)
      (Q : unit -> St -> machine_state -> Prop) ms,
    evt ssegs (fun ms1 : machine_state => at_node ssegs n ms1 /\
                 (forall (rsp : resp) (a : A), dec rsp = Some a -> evt ssegs (Q tt s0) (nret ms1 rsp))) ms ->
    implM ssegs (mbind (msys n dec) (fun _ => mret tt)) s0 Q ms.
  Proof using Type. pin_using tt.
    intros A n dec s0 Q ms H.
    eapply implM_bind with (Q1 := fun _ s' ms' => s' = s0 /\ evt ssegs (Q tt s0) ms').
    - apply implM_sys. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp a E. apply evt_done. split; [reflexivity|]. exact (Hk rsp a E).
    - intros a s' ms' [-> H']. apply implM_ret. exact H'.
  Qed.

  (* [comment removed for export] *)
  Lemma implM_prefix : forall {A} (c : M St A) s Q ms,
    evt ssegs (fun ms' => implM ssegs c s Q ms') ms -> implM ssegs c s Q ms.
  Proof using Type. pin_using tt. intros A c s Q ms H. unfold implM in *. eapply impl_evt; [exact H|]. intros ms' H'; exact H'. Qed.
End Glue.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte) (only parsing).

(* [comment removed for export] *)
Definition F_STDIO_READ : Z := 0x1b094.
Definition F_STDIO_WRITE : Z := 0x1bbb4.
Definition F_STDIO_SEEK : Z := 0x1b1ac.
Definition F_STDIO_CLOSE : Z := 0x1b068.
Definition F_STDOUT_WRITE : Z := 0x1c2cc.
Definition F_SYSRET : Z := 0x18ddc.
(* [comment removed for export] *)
Definition A_STDOUT : Z := 0x24000.
Definition A_STDOUT_BUF : Z := 0x54d30.
Definition A_STDERR : Z := 0x23e20.
Definition A_STDERR_BUF : Z := 0x54920.
Definition A_STDIN : Z := 0x23f10.
Definition A_STDIN_BUF : Z := 0x54928.
Definition A_OFL_LOCK : Z := 0x54908.
Definition A_OFL_HEAD : Z := 0x54910.

(* [comment removed for export] *)
Definition ssp_cells (m : mem) (canary : word) : Prop :=
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].

(* [comment removed for export] *)
Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac fix_litstore :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | _ => idtac
  end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.

Lemma bv_swrap32_eq : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. intros z. reflexivity. Qed.

Lemma sx32_small : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Section Glue.
  Context {St : Type}.

  (* [comment removed for export] *)
  Lemma implM_sys_ret : forall {A} (n : node) (dec : resp -> option A) (s0 : St)
      (Q : unit -> St -> machine_state -> Prop) ms,
    evt usegs (fun ms1 : machine_state => at_node usegs n ms1 /\
                 (forall (rsp : resp) (a : A), dec rsp = Some a -> evt usegs (Q tt s0) (nret ms1 rsp))) ms ->
    implM usegs (mbind (msys n dec) (fun _ => mret tt)) s0 Q ms.
  Proof using Type. pin_using tt.
    intros A n dec s0 Q ms H.
    eapply implM_bind with (Q1 := fun _ s' ms' => s' = s0 /\ evt usegs (Q tt s0) ms').
    - apply implM_sys. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp a E. apply evt_done. split; [reflexivity|]. exact (Hk rsp a E).
    - intros a s' ms' [-> H']. apply implM_ret. exact H'.
  Qed.

  (* [comment removed for export] *)
  Lemma implM_prefix : forall {A} (c : M St A) s Q ms,
    evt usegs (fun ms' => implM usegs c s Q ms') ms -> implM usegs c s Q ms.
  Proof using Type. pin_using tt. intros A c s Q ms H. unfold implM in *. eapply impl_evt; [exact H|]. intros ms' H'; exact H'. Qed.
End Glue.
End TwB.
End StdioKit.

(* [comment removed for export] *)
Module F_towrite.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition towrite_entry : Z := 0x1b914.

Definition towrite_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (closefn readfn writefn seekfn buf bufsize prev next fd : Z) (lbf : Z) (tail : list byte)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(Fp, Fp + 232)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ rw_cells ssegs m' Fp (file_cells flags 0 0 closefn (buf + bufsize) buf buf readfn writefn seekfn buf bufsize prev next fd mode' lbf tail).

Definition towrite_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (flags mode : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf : Z) (tail : list byte),
  rw_cells ssegs m (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  Z.land (bv_unsigned flags) 8 = 0 ->
  (0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
  mem_inv ssegs m ->
  evt ssegs (towrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) flags closefn readfn writefn seekfn buf bufsize prev next fd lbf tail m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b914) fc None m (seg_rom ssegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m flags mode rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf tail : ltac2:(SecDiet.SzSec.tyM 'towrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma towrite_spec__body : ltac2:(SecDiet.SzSec.bodyP 'towrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros FC NOWR B0 BHI BS0 MI.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
  set (Fp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  unfold file_cells in FC.
  assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
  { unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
    rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
  do 5 zs. rewrite FL8. zs. zs. if_lit.
  do 10 zs.
  apply evt_done. unfold towrite_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold file_cells. match goal with H : rw_cells _ _ Fp _ |- _ => exact H end.
Qed.
End Sz1.
Lemma towrite_spec : ltac:(let t := eval cbv delta [towrite_spec__stmt] in towrite_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m flags mode rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf tail. ltac2:(SecDiet.SzSec.closeP 'towrite_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition towrite_entry : Z := 0x1c0d4.

Definition towrite_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (closefn readfn writefn seekfn buf bufsize prev next fd : Z) (lbf : Z) (tail : list byte)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(Fp, Fp + 232)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' Fp (file_cells flags 0 0 closefn (buf + bufsize) buf buf readfn writefn seekfn buf bufsize prev next fd mode' lbf tail).

Definition towrite_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (flags mode : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf : Z) (tail : list byte),
  rw_cells usegs m (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  Z.land (bv_unsigned flags) 8 = 0 ->
  (0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
  mem_inv usegs m ->
  evt usegs (towrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) flags closefn readfn writefn seekfn buf bufsize prev next fd lbf tail m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1c0d4) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m flags mode rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf tail : ltac2:(SecDiet.SzSec.tyM 'towrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma towrite_spec__body : ltac2:(SecDiet.SzSec.bodyP 'towrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros FC NOWR B0 BHI BS0 MI.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
  set (Fp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold file_cells in FC.
  assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
  { unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
    rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
  do 5 zs. rewrite FL8. zs. zs. if_lit.
  do 10 zs.
  apply evt_done. unfold towrite_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold file_cells. match goal with H : rw_cells _ _ Fp _ |- _ => exact H end.
Qed.
End Sz1.
Lemma towrite_spec : ltac:(let t := eval cbv delta [towrite_spec__stmt] in towrite_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m flags mode rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf tail. ltac2:(SecDiet.SzSec.closeP 'towrite_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_towrite.
