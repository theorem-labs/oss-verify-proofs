(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require StrerrorData.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_lock.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Definition NEED_LOCKS : Z := 0x60184b.      (* [comment removed for export] *)
Definition lock_entry : Z := 0x9f074.
Definition unlock_entry : Z := 0x9f2fc.
Definition errno_location_entry : Z := 0x944b8.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a3,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m
    /\ rw_cells asegs m NEED_LOCKS [C1 (Z_to_bv 8 0)].

Lemma lock_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  rw_cells asegs m NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  rng_aimg RNG ->
  evtF asegs RNG (lock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f074) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros NL MI RIMG. unfold NEED_LOCKS in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
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
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m
    /\ rw_cells asegs m (bv_unsigned a0) [C4 v].

Lemma unlock_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (v : word),
  rw_cells asegs m (bv_unsigned a0) [C4 v] ->
  mem_inv asegs m ->
  (bv_unsigned v mod 2^32 < 2^31)%Z ->          (* [comment removed for export] *)
  rng RNG (bv_unsigned a0) 4 ->
  evtF asegs RNG (unlock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 v F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f2fc) fc None m (seg_rom asegs)).
Proof.
  intros until v. intros LK MI POS RLK.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
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
Lemma unlock_spec0 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  rw_cells asegs m (bv_unsigned a0) [C4 (Z_to_bv 64 0)] ->
  mem_inv asegs m ->
  rng RNG (bv_unsigned a0) 4 ->
  evtF asegs RNG (unlock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 0) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f2fc) fc None m (seg_rom asegs)).
Proof. intros. apply unlock_spec; [assumption|assumption| |assumption]. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma sx32_zero : sx32 (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition errno_location_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (errno_addr tp)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m.

Lemma errno_location_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  mem_inv asegs m ->
  evtF asegs RNG (errno_location_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x944b8) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 3 step. unfold errno_location_post. finish.
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.

Definition NEED_LOCKS : Z := 0x601c4b.      (* [comment removed for export] *)
Definition lock_entry : Z := 0x9f458.
Definition unlock_entry : Z := 0x9f6e0.
Definition errno_location_entry : Z := 0x9489c.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lock_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a3,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m
    /\ rw_cells asegs m NEED_LOCKS [C1 (Z_to_bv 8 0)].

Lemma lock_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  rw_cells asegs m NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  rng_aimg RNG ->
  evtF asegs RNG (lock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f458) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros NL MI RIMG. unfold NEED_LOCKS in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
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
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m
    /\ rw_cells asegs m (bv_unsigned a0) [C4 v].

Lemma unlock_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (v : word),
  rw_cells asegs m (bv_unsigned a0) [C4 v] ->
  mem_inv asegs m ->
  (bv_unsigned v mod 2^32 < 2^31)%Z ->          (* [comment removed for export] *)
  rng RNG (bv_unsigned a0) 4 ->
  evtF asegs RNG (unlock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 v F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f6e0) fc None m (seg_rom asegs)).
Proof.
  intros until v. intros LK MI POS RLK.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
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
Lemma unlock_spec0 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  rw_cells asegs m (bv_unsigned a0) [C4 (Z_to_bv 64 0)] ->
  mem_inv asegs m ->
  rng RNG (bv_unsigned a0) 4 ->
  evtF asegs RNG (unlock_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 0) F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9f6e0) fc None m (seg_rom asegs)).
Proof. intros. apply unlock_spec; [assumption|assumption| |assumption]. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma sx32_zero : sx32 (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition errno_location_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' =>
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (errno_addr tp)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m.

Lemma errno_location_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m,
  mem_inv asegs m ->
  evtF asegs RNG (errno_location_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9489c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 3 step. unfold errno_location_post. finish.
Qed.
End TwB.
End F_lock.

(* [comment removed for export] *)
Module F_strlen.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)

Definition strlen_entry := 0x9edb8%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ bytes_at asegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section Proofs.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis STR : bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  (* [comment removed for export] *)
  Hypothesis RSTR : rng RNG (bv_unsigned a0) (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))).
  Hypothesis RIMG : rng_aimg RNG.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono asegs m m := wmono_refl asegs m.

  Notation A := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation POST := (strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m).
  (* [comment removed for export] *)
  Notation ST pc x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)

  Lemma full_length : length full = (length str + S (length slack))%nat.
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite length_app. cbn. lia. Qed.

  Lemma A_bound : (0 <= A /\ A + len + 1 + Z.of_nat (length slack) <= 2^64)%Z.
  Proof using STR. pin_using (fun (STR : unit) => tt). pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B. lia. Qed.

  Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof using NONUL a0. pin_using (fun (NONUL a0 : unit) => tt).
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. }
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma strlen_tail : forall (k : nat) (i : Z) (a3 a4 a5 a6 : word),
    (Z.to_nat (len - i) = k) -> (0 <= i <= len)%Z ->
    evtF asegs RNG POST (ST 0x9ee28 (Z_to_bv 64 (A + i - 1)) (Z_to_bv 64 (A + i)) a3 a4 a5 a6).
  Proof using MI NONUL STR RSTR RIMG. pin_using (fun (MI NONUL STR : unit) => tt).
    induction k as [|k IH]; intros i a3 a4 a5 a6 Hk Hi; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read asegs m A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
      do 4 zstep. if_false. zstep. zstep.
      replace (A + len - 1 + 1 - A)%Z with len by lia. finish.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hb).
      pose proof (u8ro_read asegs m A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
      do 4 zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
      replace (A + i - 1 + 1)%Z with (A + (i + 1) - 1)%Z by lia.
      replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
      apply (IH (i + 1)%Z); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_words : forall (k : nat) (j : Z) (a5 a6 : word),
    (Z.to_nat (len - j) = k) -> (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z ->
    evtF asegs RNG POST (ST 0x9ee0c (Z_to_bv 64 (A + j - 9)) (Z_to_bv 64 (A + j - 8)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS) a5 a6).
  Proof using MI NONUL PAD STR RSTR RIMG. pin_using (fun (MI NONUL PAD STR : unit) => tt).
    induction k as [k IH] using lt_wf_ind; intros j a5 a6 Hk Hj Hal; pose proof A_bound as AB.
    assert (HW : (Z.to_nat j + 8 <= length full)%nat).
    { rewrite full_length. Z.div_mod_to_equations. lia. }
    pose proof (bytes_at_read asegs m A full j 8 STR ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat j) full)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    do 7 zstep.
    replace (A + j - 8 + 8)%Z with (A + j)%Z by lia.
    replace (A + j - 9 + 8)%Z with (A + j - 1)%Z by lia.
    rewrite (load8_le_val chunk CL).
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in K.
      rewrite In0_map_unsigned in K.
      assert (Hj8 : (j + 8 <= len)%Z).
      { destruct (Z.lt_ge_cases len (j + 8)); [|assumption]. exfalso. apply K. subst chunk.
        apply nth_error_In with (n := (Z.to_nat len - Z.to_nat j)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
      replace (A + j - 1)%Z with (A + (j + 8) - 9)%Z by lia.
      replace (Z_to_bv 64 (A + j)) with (Z_to_bv 64 (A + (j + 8) - 8)) by (f_equal; lia).
      apply (IH (Z.to_nat (len - (j + 8)))); try lia. all: Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      apply (strlen_tail (Z.to_nat (len - j)) j); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_wentry : forall (j : Z) (a1 a3 a4 a5 a6 : word),
    (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z ->
    evtF asegs RNG POST (ST 0x9edf4 a1 (Z_to_bv 64 (A + j)) a3 a4 a5 a6).
  Proof using MI NONUL PAD STR RSTR RIMG. pin_using (fun (MI NONUL PAD STR : unit) => tt).
    intros j a1 a3 a4 a5 a6 Hj Hal. pose proof A_bound as AB.
    do 6 zstep.
    replace (A + j + -9)%Z with (A + j - 9)%Z by lia.
    replace (A + j + -8)%Z with (A + j - 8)%Z by lia.
    apply (strlen_words (Z.to_nat (len - j)) j); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_head : forall (k : nat) (i : Z) (a3 a4 a5 a6 : word),
    (Z.to_nat (len - i) = k) -> (0 <= i < len)%Z ->
    evtF asegs RNG POST (ST 0x9edd4 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 a6).
  Proof using MI NONUL PAD STR RSTR RIMG. pin_using (fun (MI NONUL PAD STR : unit) => tt).
    induction k as [|k IH]; intros i a3 a4 a5 a6 Hk Hi; pose proof A_bound as AB; [lia|].
    do 3 zstep. if_cases Kal; zify_cond Kal.
    - replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
      apply strlen_wentry; [lia|]. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
    - destruct (Z.eq_dec (i + 1) len) as [E|NE].
      + pose proof (u8ro_read asegs m A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
        do 4 zstep. if_false. do 3 zstep.
        replace (A + i + 1 - A)%Z with len by lia. finish.
      + destruct (full_nth_lt (i + 1) ltac:(lia)) as (b & Hn & Hb).
        pose proof (u8ro_read asegs m A full (i + 1) b _ STR Hn ltac:(lia) eq_refl) as RD.
        replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        do 4 zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
        replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); lia.
  Qed.
End Proofs.

Lemma strlen_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte),
  bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv asegs m ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) -> rng_aimg RNG ->
  evtF asegs RNG (strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9edb8) fc None m (seg_rom asegs)).
Proof.
  intros until slack. intros STR NONUL PAD MI RSTR RIMG.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 3 zstep. if_cases Kal; zify_cond Kal.
  - (* [comment removed for export] *)
    eapply evtF_eq.
    2:{ eapply (strlen_wentry _ _ _ _ _ _ _ _ _ _ a0) with (j := 0%Z); try eassumption; try lia.
        revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
    unfold mkR. rewrite Z_to_bv_plus0. reflexivity.
  - destruct str as [|c str'] eqn:Es.
    + (* [comment removed for export] *)
      pose proof (u8ro_read asegs m (bv_unsigned a0) _ 0 _ a0 STR eq_refl ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
      do 2 zstep. if_true. do 2 zstep.
      replace (bv_unsigned a0 - bv_unsigned a0)%Z with 0%Z by lia. finish.
    + assert (Hc : bv_unsigned c <> 0%Z).
      { intros Hc. apply NONUL. left. apply bv_eq. rewrite Hc. reflexivity. }
      pose proof (u8ro_read asegs m (bv_unsigned a0) _ 0 _ a0 STR eq_refl ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
      do 2 zstep. if_cases K; zify_cond K. { exfalso. exact (Hc K). }
      do 2 zstep.
      eapply evtF_eq.
      2:{ eapply (strlen_head _ _ _ _ _ _ _ _ _ _ a0) with (i := 0%Z) (k := length (c :: str')); try eassumption; cbn [length]; lia. }
      unfold mkR. rewrite Z.add_0_r, Z_to_bv_lit_self. reflexivity.
Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)

Definition strlen_entry := 0x9f19c%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (str slack : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ bytes_at asegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section Proofs.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis STR : bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  (* [comment removed for export] *)
  Hypothesis RSTR : rng RNG (bv_unsigned a0) (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))).
  Hypothesis RIMG : rng_aimg RNG.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono asegs m m := wmono_refl asegs m.

  Notation A := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation POST := (strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m).
  (* [comment removed for export] *)
  Notation ST pc x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)

  Lemma full_length : length full = (length str + S (length slack))%nat.
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite length_app. cbn. lia. Qed.

  Lemma A_bound : (0 <= A /\ A + len + 1 + Z.of_nat (length slack) <= 2^64)%Z.
  Proof using STR. pin_using (fun (STR : unit) => tt). pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B. lia. Qed.

  Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof using NONUL a0. pin_using (fun (NONUL a0 : unit) => tt).
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. }
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma strlen_tail : forall (k : nat) (i : Z) (a3 a4 a5 a6 : word),
    (Z.to_nat (len - i) = k) -> (0 <= i <= len)%Z ->
    evtF asegs RNG POST (ST 0x9f20c (Z_to_bv 64 (A + i - 1)) (Z_to_bv 64 (A + i)) a3 a4 a5 a6).
  Proof using MI NONUL STR RSTR RIMG. pin_using (fun (MI NONUL STR : unit) => tt).
    induction k as [|k IH]; intros i a3 a4 a5 a6 Hk Hi; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read asegs m A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
      do 4 zstep. if_false. zstep. zstep.
      replace (A + len - 1 + 1 - A)%Z with len by lia. finish.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hb).
      pose proof (u8ro_read asegs m A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
      do 4 zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
      replace (A + i - 1 + 1)%Z with (A + (i + 1) - 1)%Z by lia.
      replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
      apply (IH (i + 1)%Z); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_words : forall (k : nat) (j : Z) (a5 a6 : word),
    (Z.to_nat (len - j) = k) -> (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z ->
    evtF asegs RNG POST (ST 0x9f1f0 (Z_to_bv 64 (A + j - 9)) (Z_to_bv 64 (A + j - 8)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS) a5 a6).
  Proof using MI NONUL PAD STR RSTR RIMG. pin_using (fun (MI NONUL PAD STR : unit) => tt).
    induction k as [k IH] using lt_wf_ind; intros j a5 a6 Hk Hj Hal; pose proof A_bound as AB.
    assert (HW : (Z.to_nat j + 8 <= length full)%nat).
    { rewrite full_length. Z.div_mod_to_equations. lia. }
    pose proof (bytes_at_read asegs m A full j 8 STR ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat j) full)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    do 7 zstep.
    replace (A + j - 8 + 8)%Z with (A + j)%Z by lia.
    replace (A + j - 9 + 8)%Z with (A + j - 1)%Z by lia.
    rewrite (load8_le_val chunk CL).
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in K.
      rewrite In0_map_unsigned in K.
      assert (Hj8 : (j + 8 <= len)%Z).
      { destruct (Z.lt_ge_cases len (j + 8)); [|assumption]. exfalso. apply K. subst chunk.
        apply nth_error_In with (n := (Z.to_nat len - Z.to_nat j)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
      replace (A + j - 1)%Z with (A + (j + 8) - 9)%Z by lia.
      replace (Z_to_bv 64 (A + j)) with (Z_to_bv 64 (A + (j + 8) - 8)) by (f_equal; lia).
      apply (IH (Z.to_nat (len - (j + 8)))); try lia. all: Z.div_mod_to_equations; lia.
    - (* [comment removed for export] *)
      apply (strlen_tail (Z.to_nat (len - j)) j); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_wentry : forall (j : Z) (a1 a3 a4 a5 a6 : word),
    (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z ->
    evtF asegs RNG POST (ST 0x9f1d8 a1 (Z_to_bv 64 (A + j)) a3 a4 a5 a6).
  Proof using MI NONUL PAD STR RSTR RIMG. pin_using (fun (MI NONUL PAD STR : unit) => tt).
    intros j a1 a3 a4 a5 a6 Hj Hal. pose proof A_bound as AB.
    do 6 zstep.
    replace (A + j + -9)%Z with (A + j - 9)%Z by lia.
    replace (A + j + -8)%Z with (A + j - 8)%Z by lia.
    apply (strlen_words (Z.to_nat (len - j)) j); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_head : forall (k : nat) (i : Z) (a3 a4 a5 a6 : word),
    (Z.to_nat (len - i) = k) -> (0 <= i < len)%Z ->
    evtF asegs RNG POST (ST 0x9f1b8 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 a6).
  Proof using MI NONUL PAD STR RSTR RIMG. pin_using (fun (MI NONUL PAD STR : unit) => tt).
    induction k as [|k IH]; intros i a3 a4 a5 a6 Hk Hi; pose proof A_bound as AB; [lia|].
    do 3 zstep. if_cases Kal; zify_cond Kal.
    - replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
      apply strlen_wentry; [lia|]. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
    - destruct (Z.eq_dec (i + 1) len) as [E|NE].
      + pose proof (u8ro_read asegs m A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
        do 4 zstep. if_false. do 3 zstep.
        replace (A + i + 1 - A)%Z with len by lia. finish.
      + destruct (full_nth_lt (i + 1) ltac:(lia)) as (b & Hn & Hb).
        pose proof (u8ro_read asegs m A full (i + 1) b _ STR Hn ltac:(lia) eq_refl) as RD.
        replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        do 4 zstep. if_cases K; zify_cond K. 2:{ exfalso. exact (Hb K). }
        replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); lia.
  Qed.
End Proofs.

Lemma strlen_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte),
  bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv asegs m ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) -> rng_aimg RNG ->
  evtF asegs RNG (strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9f19c) fc None m (seg_rom asegs)).
Proof.
  intros until slack. intros STR NONUL PAD MI RSTR RIMG.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 3 zstep. if_cases Kal; zify_cond Kal.
  - (* [comment removed for export] *)
    eapply evtF_eq.
    2:{ eapply (strlen_wentry _ _ _ _ _ _ _ _ _ _ a0) with (j := 0%Z); try eassumption; try lia.
        revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
    unfold mkR. rewrite Z_to_bv_plus0. reflexivity.
  - destruct str as [|c str'] eqn:Es.
    + (* [comment removed for export] *)
      pose proof (u8ro_read asegs m (bv_unsigned a0) _ 0 _ a0 STR eq_refl ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
      do 2 zstep. if_true. do 2 zstep.
      replace (bv_unsigned a0 - bv_unsigned a0)%Z with 0%Z by lia. finish.
    + assert (Hc : bv_unsigned c <> 0%Z).
      { intros Hc. apply NONUL. left. apply bv_eq. rewrite Hc. reflexivity. }
      pose proof (u8ro_read asegs m (bv_unsigned a0) _ 0 _ a0 STR eq_refl ltac:(lia) ltac:(symmetry; apply Z_to_bv_plus0)) as RD.
      do 2 zstep. if_cases K; zify_cond K. { exfalso. exact (Hc K). }
      do 2 zstep.
      eapply evtF_eq.
      2:{ eapply (strlen_head _ _ _ _ _ _ _ _ _ _ a0) with (i := 0%Z) (k := length (c :: str')); try eassumption; cbn [length]; lia. }
      unfold mkR. rewrite Z.add_0_r, Z_to_bv_lit_self. reflexivity.
Qed.
End TwB.
End F_strlen.

(* [comment removed for export] *)
Module F_stdio_leaf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ferror_entry := 0x9a2cc%Z.
Definition fileno_entry := 0x9a758%Z.

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
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail).

Definition ferror_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z)
    flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + 232 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned a0) 232 -> rng_aimg RNG ->
  evtF asegs RNG (ferror_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9a2cc) fc None m (seg_rom asegs)).
Section Sz3.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail : ltac2:(SecDiet.SzSec.tyM 'ferror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma ferror_spec__body : ltac2:(SecDiet.SzSec.bodyP 'ferror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST FC MI LO SEP RSTK RFP RIMG.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold file_cells in FC.
  carve_frame 32%nat ST.
  do 5 step. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. pose proof lock_word_neg. lia. }
  zstep. zstep. zstep. rewrite ferr_bit.
  do 4 step. release_frame FR ST (bv_unsigned sp). step.
  unfold ferror_post, file_cells. finish.
Qed.
End Sz3.
Lemma ferror_spec : ltac:(let t := eval cbv delta [ferror_spec__stmt] in ferror_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail. ltac2:(SecDiet.SzSec.closeP 'ferror_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fileno_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 flags : word) rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd (mode : word) lbf tail
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail).

Definition fileno_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z)
    flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + 232 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 <= fd < 2^31)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned a0) 232 -> rng_aimg RNG ->
  evtF asegs RNG (fileno_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9a758) fc None m (seg_rom asegs)).
Section Sz4.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail : ltac2:(SecDiet.SzSec.tyM 'fileno_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma fileno_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fileno_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST FC MI LO SEP FD RSTK RFP RIMG.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
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
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail. ltac2:(SecDiet.SzSec.closeP 'fileno_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ferror_entry := 0x9a6b0%Z.
Definition fileno_entry := 0x9ab3c%Z.

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
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail).

Definition ferror_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z)
    flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + 232 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned a0) 232 -> rng_aimg RNG ->
  evtF asegs RNG (ferror_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9a6b0) fc None m (seg_rom asegs)).
Section Sz3.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail : ltac2:(SecDiet.SzSec.tyM 'ferror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma ferror_spec__body : ltac2:(SecDiet.SzSec.bodyP 'ferror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST FC MI LO SEP RSTK RFP RIMG.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold file_cells in FC.
  carve_frame 32%nat ST.
  do 5 step. zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. pose proof lock_word_neg. lia. }
  zstep. zstep. zstep. rewrite ferr_bit.
  do 4 step. release_frame FR ST (bv_unsigned sp). step.
  unfold ferror_post, file_cells. finish.
Qed.
End Sz3.
Lemma ferror_spec : ltac:(let t := eval cbv delta [ferror_spec__stmt] in ferror_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail. ltac2:(SecDiet.SzSec.closeP 'ferror_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fileno_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 flags : word) rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd (mode : word) lbf tail
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail).

Definition fileno_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z)
    flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + 232 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 <= fd < 2^31)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned a0) 232 -> rng_aimg RNG ->
  evtF asegs RNG (fileno_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9ab3c) fc None m (seg_rom asegs)).
Section Sz4.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail : ltac2:(SecDiet.SzSec.tyM 'fileno_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma fileno_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fileno_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST FC MI LO SEP FD RSTK RFP RIMG.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
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
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail. ltac2:(SecDiet.SzSec.closeP 'fileno_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_stdio_leaf.

(* [comment removed for export] *)
Module F_strchr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Bytes SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memchr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strlen.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition strchrnul_entry := 0x9ec08%Z.
Definition strchr_entry := 0x9ebcc%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strchrnul_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat (strchrnul_idx (bv_unsigned a1 mod 256) str)))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section StrchrnulProof.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte) (str slack : list byte) (lo : Z).
  (* [comment removed for export] *)
  Hypothesis MI : mem_inv asegs m1.
  Hypothesis STR : bytes_at asegs m1 (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis MU : munch [(bv_unsigned sp + -16, bv_unsigned sp)]%Z m m1.
  Hypothesis WM : wmono asegs m m1.
  Hypothesis ST : stk asegs m1 lo (bv_unsigned sp + -16).
  Hypothesis FR : rw_cells asegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra].
  Hypothesis LO : (0 <= lo <= bv_unsigned sp - 16)%Z.
  Hypothesis SPR : (bv_unsigned sp < 2^64)%Z.
  (* [comment removed for export] *)
  Hypothesis RSTR : rng RNG (bv_unsigned a0) (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RSTK : rng RNG (bv_unsigned sp + -16) 16.

  Notation A := (bv_unsigned a0).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation POST := (strchrnul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m).
  (* [comment removed for export] *)
  Notation AT pc xra xs0 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 xs0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom asegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)
  Notation ONES := 72340172838076673%Z.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition NOB (i : Z) : Prop :=
    forall j b, (j < Z.to_nat i)%nat -> nth_error str j = Some b -> bv_unsigned b <> c.

  Lemma full_length : length full = (length str + S (length slack))%nat.
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite length_app. cbn. lia. Qed.

  Lemma A_bound : (0 <= A /\ A + len + 1 + Z.of_nat (length slack) <= 2^64 /\ 0 <= c < 256)%Z.
  Proof using STR. pin_using (fun (STR : unit) => tt).
    pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). lia.
  Qed.

  Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ nth_error str (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof using NONUL a0. pin_using (fun (NONUL a0 : unit) => tt).
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. } split; [reflexivity|].
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  Lemma NOB_0 : NOB 0.
  Proof using Type. pin_using tt. intros j b Hj. exfalso. exact (Nat.nlt_0_r _ Hj). Qed.

  Lemma NOB_S : forall i b, (0 <= i)%Z -> NOB i -> nth_error str (Z.to_nat i) = Some b -> bv_unsigned b <> c -> NOB (i + 1).
  Proof using a0 slack. pin_using (fun (a0 slack : unit) => tt).
    intros i b Hi H Hn Hb j b' Hj Hn'.
    destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE]. { rewrite Hn in Hn'. injection Hn' as <-. exact Hb. }
    eapply H; [|exact Hn']. lia.
  Qed.

  Lemma idx_found : forall i b, (0 <= i < len)%Z -> NOB i -> nth_error str (Z.to_nat i) = Some b -> bv_unsigned b = c ->
    Z.of_nat (strchrnul_idx c str) = i.
  Proof using a0 slack. pin_using (fun (a0 slack : unit) => tt).
    intros i b Hi HN Hn Hb. unfold strchrnul_idx.
    rewrite (find_byte_charact c str (Z.to_nat i) b Hn Hb). { lia. }
    intros j b' Hj Hn'. exact (HN _ _ Hj Hn').
  Qed.

  Lemma idx_end : NOB len -> Z.of_nat (strchrnul_idx c str) = len.
  Proof using a0 slack. pin_using (fun (a0 slack : unit) => tt).
    intros HN. unfold strchrnul_idx. rewrite find_byte_None_intro; [reflexivity|].
    intros j b Hn. apply (HN j b); [|exact Hn]. apply nth_error_lt in Hn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_ret : forall x12 x13 x14 x15 x16 x17,
    evtF asegs RNG POST (AT 0x9ecd8 (Z_to_bv 64 0x9ebe0) s0 (Z_to_bv 64 (A + Z.of_nat (strchrnul_idx c str))) x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU ST STR WM RSTR RIMG RSTK. pin_using (fun (FR LO MI MU ST STR WM : unit) => tt).
    intros. pose proof A_bound as AB. pose proof FR as FR'. pose proof ST as ST'. pose proof MI as MI'.
    do 3 step. release_frame FR' ST' (bv_unsigned sp). step. unfold strchrnul_post. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_ret_any : forall xra xs0 x12 x13 x14 x15 x16 x17,
    evtF asegs RNG POST (AT 0x9ecd8 xra xs0 (Z_to_bv 64 (A + Z.of_nat (strchrnul_idx c str))) x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU ST STR WM RSTR RIMG RSTK. pin_using (fun (FR LO MI MU ST STR WM : unit) => tt).
    intros. pose proof A_bound as AB. pose proof FR as FR'. pose proof ST as ST'. pose proof MI as MI'.
    do 3 step. release_frame FR' ST' (bv_unsigned sp). step. unfold strchrnul_post. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_tail : forall (k : nat) (i : Z) xra xs0 x12 x13 x14 x15 x16 x17,
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z -> NOB i ->
    evtF asegs RNG POST (AT 0x9ecc8 xra xs0 (Z_to_bv 64 (A + i - 1)) x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU NONUL ST STR WM RSTR RIMG RSTK. pin_using (fun (FR LO MI MU NONUL ST STR WM : unit) => tt).
    induction k as [|k IH]; intros i xra xs0 x12 x13 x14 x15 x16 x17 Hk Hi HN; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read asegs m1 A full len _ (wa (A + len - 1 + 1)) STR full_nth_len ltac:(lia) ltac:(f_equal; lia)) as RD.
      do 3 zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
      replace (A + len - 1 + 1)%Z with (A + Z.of_nat (strchrnul_idx c str))%Z by (rewrite idx_end; [lia|exact HN]).
      apply strchrnul_ret_any.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hns & Hb).
      pose proof (u8ro_read asegs m1 A full i b (wa (A + i - 1 + 1)) STR Hn ltac:(lia) ltac:(f_equal; lia)) as RD.
      do 3 zstep. if_cases K; zify_cond K. { exfalso. exact (Hb K). }
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        replace (A + i - 1 + 1)%Z with (A + (i + 1) - 1)%Z by lia.
        apply (IH (i + 1)%Z); try lia. eapply NOB_S; eauto; lia.
      + (* [comment removed for export] *)
        replace (A + i - 1 + 1)%Z with (A + Z.of_nat (strchrnul_idx c str))%Z by (rewrite (idx_found i b); [lia|lia|exact HN|exact Hns|exact K2]).
        apply strchrnul_ret_any.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_words : forall (k : nat) (j : Z) xra xs0 (chunk : list byte) x16 x17,
    Z.to_nat (len - j) = k -> (0 <= j)%Z -> (j + 8 <= len)%Z -> ((A + j) mod 8 = 0)%Z -> NOB j ->
    chunk = firstn 8 (skipn (Z.to_nat j) full) ->
    evtF asegs RNG POST (AT 0x9ec70 xra xs0 (Z_to_bv 64 (A + j)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS)
                       (bv_extract 0 64 (le_bytes_to_word chunk)) (Z_to_bv 64 (c * ONES)) x16 x17).
  Proof using FR LO MI MU NONUL PAD ST STR WM RSTR RIMG RSTK. pin_using (fun (FR LO MI MU NONUL PAD ST STR WM : unit) => tt).
    induction k as [k IH] using lt_wf_ind; intros j xra xs0 chunk x16 x17 Hk Hj Hj8 Hal HN Hch; pose proof A_bound as AB.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite length_firstn, length_skipn, full_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    pose proof (le_val_range _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia))) as XR. rewrite !length_map, CL in XR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in XR.
    zstep. rewrite (load8_le_val chunk CL).
    replace (Z.lxor (le_val (map bv_unsigned chunk)) (c * ONES)) with (le_val (map (fun b => Z.lxor b c) (map bv_unsigned chunk))).
    2:{ change ONES with ONES64b. rewrite <- ones_8, <- CL, <- (length_map bv_unsigned). symmetry. apply le_val_xor_bcast; [apply bytes_ok_map| lia]. }
    do 4 zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      do 2 zstep. replace (A + j + -1)%Z with (A + j - 1)%Z by lia.
      apply (strchrnul_tail (Z.to_nat (len - j)) j); try lia. exact HN.
    - apply (haszero64_clang _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia)) ltac:(rewrite !length_map; exact CL)) in K.
      rewrite In0_xor in K.
      assert (HN8 : NOB (j + 8)).
      { intros i b Hi Hn. destruct (Nat.lt_ge_cases i (Z.to_nat j)) as [Hlt|Hge]. { exact (HN _ _ Hlt Hn). }
        intros Hb. apply K. rewrite <- Hb. apply in_map. subst chunk.
        apply nth_error_In with (n := (i - Z.to_nat j)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn. rewrite nth_error_app1 by (apply nth_error_lt in Hn; lia). rewrite <- Hn. f_equal. lia. }
      (* [comment removed for export] *)
      assert (HW : (Z.to_nat (j + 8) + 8 <= length full)%nat).
      { rewrite full_length. Z.div_mod_to_equations. lia. }
      pose proof (bytes_at_read asegs m1 A full (j + 8) 8 STR ltac:(lia) HW) as RD.
      set (chunk2 := firstn 8 (skipn (Z.to_nat (j + 8)) full)) in RD.
      assert (CL2 : length chunk2 = 8%nat). { subst chunk2. rewrite length_firstn, length_skipn. lia. }
      pose proof (le_val_range _ (bytes_ok_map chunk2)) as WR2. rewrite length_map, CL2 in WR2.
      change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR2.
      replace (wa (A + (j + 8))) with (wa (A + j + 8)) in RD by (f_equal; lia).
      do 7 zstep. rewrite (load8_le_val chunk2 CL2).
      if_cases K8; zify_cond K8.
      + (* [comment removed for export] *)
        apply (haszero64_clang _ (bytes_ok_map chunk2) ltac:(rewrite length_map; exact CL2)) in K8.
        rewrite In0_map_unsigned in K8.
        assert (Hj16 : (j + 16 <= len)%Z).
        { destruct (Z.lt_ge_cases len (j + 16)); [|assumption]. exfalso. apply K8. subst chunk2.
          apply nth_error_In with (n := (Z.to_nat len - Z.to_nat (j + 8))%nat).
          rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
          rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
        replace (A + j + 8)%Z with (A + (j + 8))%Z by lia.
        apply (IH (Z.to_nat (len - (j + 8))) ltac:(lia) (j + 8)%Z); try lia; try exact HN8; try reflexivity.
        all: Z.div_mod_to_equations; lia.
      + (* [comment removed for export] *)
        zstep. zstep. replace (A + j + 7)%Z with (A + (j + 8) - 1)%Z by lia.
        apply (strchrnul_tail (Z.to_nat (len - (j + 8))) (j + 8)); try lia. exact HN8.
  Qed.

  (* [comment removed for export] *)
  Definition strchrnul_wentry__stmt : Prop := forall (j : Z) xra xs0 x10 x12 x13 x14 x15 x16 x17,
    (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z -> NOB j -> x10 = Z_to_bv 64 (A + j) ->
    evtF asegs RNG POST (AT 0x9ec44 xra xs0 x10 x12 x13 x14 x15 x16 x17).
  Section Sz13.
  Variables j xra xs0 x10 x12 x13 x14 x15 x16 x17 : ltac2:(SecDiet.SzSec.tyM 'strchrnul_wentry__stmt "vvvvvvvvvv" @j).
  Lemma strchrnul_wentry__body : ltac2:(SecDiet.SzSec.bodyP 'strchrnul_wentry__stmt "vvvvvvvvvv").
  Proof using FR LO MI MU NONUL PAD ST STR WM RSTR RIMG RSTK. pin_using (fun (FR LO MI MU NONUL PAD ST STR WM : unit) => tt).
    intros Hj Hal HN ->.
 pose proof A_bound as AB.
    assert (HW : (Z.to_nat j + 8 <= length full)%nat).
    { rewrite full_length. Z.div_mod_to_equations. lia. }
    pose proof (bytes_at_read asegs m1 A full j 8 STR ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat j) full)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite length_firstn, length_skipn. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    do 9 zstep. rewrite (load8_le_val chunk CL).
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      do 2 zstep. replace (A + j + -1)%Z with (A + j - 1)%Z by lia.
      apply (strchrnul_tail (Z.to_nat (len - j)) j); try lia. exact HN.
    - apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in K.
      rewrite In0_map_unsigned in K.
      assert (Hj8 : (j + 8 <= len)%Z).
      { destruct (Z.lt_ge_cases len (j + 8)); [|assumption]. exfalso. apply K. subst chunk.
        apply nth_error_In with (n := (Z.to_nat len - Z.to_nat j)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
      do 2 zstep.
      replace (c * (CMAGIC + 1))%Z with (c * ONES)%Z by reflexivity.
      apply (strchrnul_words (Z.to_nat (len - j)) j xra xs0 chunk); try lia; try exact HN. reflexivity.
  Qed.
  End Sz13.
  Lemma strchrnul_wentry : ltac:(let t := eval cbv delta [strchrnul_wentry__stmt] in strchrnul_wentry__stmt in exact t).
  Proof using FR LO MI MU NONUL PAD ST STR WM RSTR RIMG RSTK. intros j xra xs0 x10 x12 x13 x14 x15 x16 x17. ltac2:(SecDiet.SzSec.closeP 'strchrnul_wentry__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_head : forall (k : nat) (i : Z) xra xs0 x10 x12 x13 x14 x15 x16 x17,
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z -> NOB i -> x10 = Z_to_bv 64 (A + i) -> x12 = Z_to_bv 64 (A + i + 1) ->
    evtF asegs RNG POST (AT 0x9ec28 xra xs0 x10 x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU NONUL PAD ST STR WM RSTR RIMG RSTK. pin_using (fun (FR LO MI MU NONUL PAD ST STR WM : unit) => tt).
    induction k as [|k IH]; intros i xra xs0 x10 x12 x13 x14 x15 x16 x17 Hk Hi HN -> ->; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read asegs m1 A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
      replace (A + len)%Z with (A + Z.of_nat (strchrnul_idx c str))%Z by (rewrite idx_end; [lia|exact HN]).
      apply strchrnul_ret_any.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hns & Hb).
      pose proof (u8ro_read asegs m1 A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases K; zify_cond K. { exfalso. exact (Hb K). }
      zstep. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        rewrite <- (idx_found i b ltac:(lia) HN Hns K2). apply strchrnul_ret_any. }
      pose proof (NOB_S i b ltac:(lia) HN Hns K2) as HN1.
      do 4 zstep. if_cases Kal; zify_cond Kal.
      + apply (IH (i + 1)%Z); try lia; try (f_equal; lia). exact HN1.
      + apply (strchrnul_wentry (i + 1)); try lia; try exact HN1; try (f_equal; lia).
        revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
  Qed.
End StrchrnulProof.

Lemma strchrnul_idx_nul : forall str, ~ In (Z_to_bv 8 0) str -> strchrnul_idx 0 str = length str.
Proof.
  intros str H. unfold strchrnul_idx. rewrite find_byte_notin; [reflexivity|].
  intros b Hb E. apply H. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
Qed.

Definition strchrnul_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 mod 256 <> 0)%Z ->   (* [comment removed for export] *)
  rng RNG (bv_unsigned a0) (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) -> rng_aimg RNG -> rng RNG (bv_unsigned sp + -16) 16 ->
  evtF asegs RNG (strchrnul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9ec08) fc None m (seg_rom asegs)).
Section Sz16.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'strchrnul_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma strchrnul_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strchrnul_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST STR NONUL PAD MI LO SEP CNZ RSTR RIMG RSTK.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  carve_frame 16%nat ST.
  do 3 step.
  zstep. replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
  zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *) exfalso. apply CNZ. exact K0.
  - zstep. zstep. if_cases Kal; zify_cond Kal.
    + (* [comment removed for export] *)
      eapply strchrnul_wentry with (j := 0%Z); try reflexivity; try eassumption; try lia; try apply NOB_0.
      * revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal.
      * rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
    + zstep.
      eapply strchrnul_head with (i := 0%Z); try reflexivity; try eassumption; try lia; try apply NOB_0; try (f_equal; lia).
      rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
End Sz16.
Lemma strchrnul_spec : ltac:(let t := eval cbv delta [strchrnul_spec__stmt] in strchrnul_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'strchrnul_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Definition strchr_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 mod 256 <> 0)%Z ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) -> rng_aimg RNG -> rng RNG (bv_unsigned sp + -32) 32 ->
  evtF asegs RNG (strchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9ebcc) fc None m (seg_rom asegs)).
Section Sz17.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'strchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma strchr_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST STR NONUL PAD MI LO SEP CNZ RSTR RIMG RSTK.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  carve_frame 16%nat ST.
  do 4 step.
  step. call_sp strchrnul_spec; [exact ST | exact STR | exact NONUL | exact PAD | exact MI | lia | lia | exact CNZ | ].
  rename PC into ST; clear STR; rename POST into STR.
  (* [comment removed for export] *)
  set (i := strchrnul_idx (bv_unsigned a1 mod 256) str) in *.
  pose proof (strchrnul_idx_le (bv_unsigned a1 mod 256) str) as Hi. fold i in Hi.
  assert (Hb : exists b, nth_error (str ++ Z_to_bv 8 0 :: slack) i = Some b /\
                         (bv_unsigned b = bv_unsigned a1 mod 256 -> strchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str = bv_unsigned a0 + Z.of_nat i)%Z /\
                         (bv_unsigned b <> bv_unsigned a1 mod 256 -> strchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str = 0)%Z).
  { unfold strchr_res. subst i. unfold strchrnul_idx.
    destruct (find_byte (bv_unsigned a1 mod 256) str) as [j|] eqn:FB.
    - destruct (find_byte_Some _ _ _ FB) as (Hj & (b & Hn & Hbb) & _). exists b.
      rewrite nth_error_app1 by lia. split; [exact Hn|].
      destruct (Z.eqb_spec (bv_unsigned a1 mod 256) 0) as [E|NE].
      { exfalso. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. } apply bv_eq. rewrite Hbb, E. reflexivity. }
      split; [intros _; reflexivity | intros X; exfalso; exact (X Hbb)].
    - exists (Z_to_bv 8 0). rewrite nth_error_app2, Nat.sub_diag by lia. split; [reflexivity|].
      destruct (Z.eqb_spec (bv_unsigned a1 mod 256) 0) as [E|NE].
      + split; [intros _; reflexivity | intros X; exfalso; apply X; rewrite E; reflexivity].
      + split; [intros X; exfalso; apply NE; rewrite <- X; reflexivity | intros _; reflexivity]. }
  destruct Hb as (b & Hn & Heq & Hne).
  pose proof (u8ro_read asegs _ (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) (Z.of_nat i) b (wa (bv_unsigned a0 + Z.of_nat i + 0)) STR
                ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(f_equal; lia)) as RD.
  pose proof (byte_range b) as Rb.
  do 6 zstep.
  replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
  do 3 step. release_frame FR ST (bv_unsigned sp). step.
  destruct (Z.eq_dec (bv_unsigned b) (bv_unsigned a1 mod 256)) as [E|NE].
  - rewrite E, Z.lxor_nilpotent. change (Z.b2z (0 <? 0) + -1)%Z with (-1)%Z.
    replace (Z.land ((-1) mod 18446744073709551616) (bv_unsigned a0 + Z.of_nat i))%Z with (bv_unsigned a0 + Z.of_nat i)%Z.
    2:{ change ((-1) mod 18446744073709551616)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
    rewrite <- (Heq E). unfold strchr_post. finish.
  - assert (Hx : (0 <? Z.lxor (bv_unsigned b) (bv_unsigned a1 mod 256))%Z = true).
    { apply Z.ltb_lt. pose proof (Z.lxor_nonneg (bv_unsigned b) (bv_unsigned a1 mod 256)).
      destruct (Z.eq_dec (Z.lxor (bv_unsigned b) (bv_unsigned a1 mod 256)) 0) as [E0|]; [|lia].
      apply Z.lxor_eq in E0. exfalso. exact (NE E0). }
    rewrite Hx. change (Z.b2z true + -1)%Z with 0%Z. change (0 mod 18446744073709551616)%Z with 0%Z. rewrite Z.land_0_l.
    rewrite <- (Hne NE). unfold strchr_post. finish.
Qed.
End Sz17.
Lemma strchr_spec : ltac:(let t := eval cbv delta [strchr_spec__stmt] in strchr_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'strchr_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memchr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strlen.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition strchrnul_entry := 0x9efec%Z.
Definition strchr_entry := 0x9efb0%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strchrnul_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat (strchrnul_idx (bv_unsigned a1 mod 256) str)))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section StrchrnulProof.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte) (str slack : list byte) (lo : Z).
  (* [comment removed for export] *)
  Hypothesis MI : mem_inv asegs m1.
  Hypothesis STR : bytes_at asegs m1 (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis MU : munch [(bv_unsigned sp + -16, bv_unsigned sp)]%Z m m1.
  Hypothesis WM : wmono asegs m m1.
  Hypothesis ST : stk asegs m1 lo (bv_unsigned sp + -16).
  Hypothesis FR : rw_cells asegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra].
  Hypothesis LO : (0 <= lo <= bv_unsigned sp - 16)%Z.
  Hypothesis SPR : (bv_unsigned sp < 2^64)%Z.
  (* [comment removed for export] *)
  Hypothesis RSTR : rng RNG (bv_unsigned a0) (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RSTK : rng RNG (bv_unsigned sp + -16) 16.

  Notation A := (bv_unsigned a0).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation POST := (strchrnul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m).
  (* [comment removed for export] *)
  Notation AT pc xra xs0 x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 xs0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom asegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)
  Notation ONES := 72340172838076673%Z.       (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition NOB (i : Z) : Prop :=
    forall j b, (j < Z.to_nat i)%nat -> nth_error str j = Some b -> bv_unsigned b <> c.

  Lemma full_length : length full = (length str + S (length slack))%nat.
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite length_app. cbn. lia. Qed.

  Lemma A_bound : (0 <= A /\ A + len + 1 + Z.of_nat (length slack) <= 2^64 /\ 0 <= c < 256)%Z.
  Proof using STR. pin_using (fun (STR : unit) => tt).
    pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). lia.
  Qed.

  Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ nth_error str (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z.
  Proof using NONUL a0. pin_using (fun (NONUL a0 : unit) => tt).
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. } split; [reflexivity|].
      intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof using a0. pin_using (fun (a0 : unit) => tt). rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  Lemma NOB_0 : NOB 0.
  Proof using Type. pin_using tt. intros j b Hj. exfalso. exact (Nat.nlt_0_r _ Hj). Qed.

  Lemma NOB_S : forall i b, (0 <= i)%Z -> NOB i -> nth_error str (Z.to_nat i) = Some b -> bv_unsigned b <> c -> NOB (i + 1).
  Proof using a0 slack. pin_using (fun (a0 slack : unit) => tt).
    intros i b Hi H Hn Hb j b' Hj Hn'.
    destruct (Nat.eq_dec j (Z.to_nat i)) as [->|NE]. { rewrite Hn in Hn'. injection Hn' as <-. exact Hb. }
    eapply H; [|exact Hn']. lia.
  Qed.

  Lemma idx_found : forall i b, (0 <= i < len)%Z -> NOB i -> nth_error str (Z.to_nat i) = Some b -> bv_unsigned b = c ->
    Z.of_nat (strchrnul_idx c str) = i.
  Proof using a0 slack. pin_using (fun (a0 slack : unit) => tt).
    intros i b Hi HN Hn Hb. unfold strchrnul_idx.
    rewrite (find_byte_charact c str (Z.to_nat i) b Hn Hb). { lia. }
    intros j b' Hj Hn'. exact (HN _ _ Hj Hn').
  Qed.

  Lemma idx_end : NOB len -> Z.of_nat (strchrnul_idx c str) = len.
  Proof using a0 slack. pin_using (fun (a0 slack : unit) => tt).
    intros HN. unfold strchrnul_idx. rewrite find_byte_None_intro; [reflexivity|].
    intros j b Hn. apply (HN j b); [|exact Hn]. apply nth_error_lt in Hn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_ret : forall x12 x13 x14 x15 x16 x17,
    evtF asegs RNG POST (AT 0x9f0bc (Z_to_bv 64 0x9efc4) s0 (Z_to_bv 64 (A + Z.of_nat (strchrnul_idx c str))) x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU ST STR WM RSTR RIMG RSTK. pin_using (fun (FR LO MI MU ST STR WM : unit) => tt).
    intros. pose proof A_bound as AB. pose proof FR as FR'. pose proof ST as ST'. pose proof MI as MI'.
    do 3 step. release_frame FR' ST' (bv_unsigned sp). step. unfold strchrnul_post. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_ret_any : forall xra xs0 x12 x13 x14 x15 x16 x17,
    evtF asegs RNG POST (AT 0x9f0bc xra xs0 (Z_to_bv 64 (A + Z.of_nat (strchrnul_idx c str))) x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU ST STR WM RSTR RIMG RSTK. pin_using (fun (FR LO MI MU ST STR WM : unit) => tt).
    intros. pose proof A_bound as AB. pose proof FR as FR'. pose proof ST as ST'. pose proof MI as MI'.
    do 3 step. release_frame FR' ST' (bv_unsigned sp). step. unfold strchrnul_post. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_tail : forall (k : nat) (i : Z) xra xs0 x12 x13 x14 x15 x16 x17,
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z -> NOB i ->
    evtF asegs RNG POST (AT 0x9f0ac xra xs0 (Z_to_bv 64 (A + i - 1)) x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU NONUL ST STR WM RSTR RIMG RSTK. pin_using (fun (FR LO MI MU NONUL ST STR WM : unit) => tt).
    induction k as [|k IH]; intros i xra xs0 x12 x13 x14 x15 x16 x17 Hk Hi HN; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read asegs m1 A full len _ (wa (A + len - 1 + 1)) STR full_nth_len ltac:(lia) ltac:(f_equal; lia)) as RD.
      do 3 zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
      replace (A + len - 1 + 1)%Z with (A + Z.of_nat (strchrnul_idx c str))%Z by (rewrite idx_end; [lia|exact HN]).
      apply strchrnul_ret_any.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hns & Hb).
      pose proof (u8ro_read asegs m1 A full i b (wa (A + i - 1 + 1)) STR Hn ltac:(lia) ltac:(f_equal; lia)) as RD.
      do 3 zstep. if_cases K; zify_cond K. { exfalso. exact (Hb K). }
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        replace (A + i - 1 + 1)%Z with (A + (i + 1) - 1)%Z by lia.
        apply (IH (i + 1)%Z); try lia. eapply NOB_S; eauto; lia.
      + (* [comment removed for export] *)
        replace (A + i - 1 + 1)%Z with (A + Z.of_nat (strchrnul_idx c str))%Z by (rewrite (idx_found i b); [lia|lia|exact HN|exact Hns|exact K2]).
        apply strchrnul_ret_any.
  Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_words : forall (k : nat) (j : Z) xra xs0 (chunk : list byte) x16 x17,
    Z.to_nat (len - j) = k -> (0 <= j)%Z -> (j + 8 <= len)%Z -> ((A + j) mod 8 = 0)%Z -> NOB j ->
    chunk = firstn 8 (skipn (Z.to_nat j) full) ->
    evtF asegs RNG POST (AT 0x9f054 xra xs0 (Z_to_bv 64 (A + j)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS)
                       (bv_extract 0 64 (le_bytes_to_word chunk)) (Z_to_bv 64 (c * ONES)) x16 x17).
  Proof using FR LO MI MU NONUL PAD ST STR WM RSTR RIMG RSTK. pin_using (fun (FR LO MI MU NONUL PAD ST STR WM : unit) => tt).
    induction k as [k IH] using lt_wf_ind; intros j xra xs0 chunk x16 x17 Hk Hj Hj8 Hal HN Hch; pose proof A_bound as AB.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite length_firstn, length_skipn, full_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    pose proof (le_val_range _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia))) as XR. rewrite !length_map, CL in XR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in XR.
    zstep. rewrite (load8_le_val chunk CL).
    replace (Z.lxor (le_val (map bv_unsigned chunk)) (c * ONES)) with (le_val (map (fun b => Z.lxor b c) (map bv_unsigned chunk))).
    2:{ change ONES with ONES64b. rewrite <- ones_8, <- CL, <- (length_map bv_unsigned). symmetry. apply le_val_xor_bcast; [apply bytes_ok_map| lia]. }
    do 4 zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      do 2 zstep. replace (A + j + -1)%Z with (A + j - 1)%Z by lia.
      apply (strchrnul_tail (Z.to_nat (len - j)) j); try lia. exact HN.
    - apply (haszero64_clang _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia)) ltac:(rewrite !length_map; exact CL)) in K.
      rewrite In0_xor in K.
      assert (HN8 : NOB (j + 8)).
      { intros i b Hi Hn. destruct (Nat.lt_ge_cases i (Z.to_nat j)) as [Hlt|Hge]. { exact (HN _ _ Hlt Hn). }
        intros Hb. apply K. rewrite <- Hb. apply in_map. subst chunk.
        apply nth_error_In with (n := (i - Z.to_nat j)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn. rewrite nth_error_app1 by (apply nth_error_lt in Hn; lia). rewrite <- Hn. f_equal. lia. }
      (* [comment removed for export] *)
      assert (HW : (Z.to_nat (j + 8) + 8 <= length full)%nat).
      { rewrite full_length. Z.div_mod_to_equations. lia. }
      pose proof (bytes_at_read asegs m1 A full (j + 8) 8 STR ltac:(lia) HW) as RD.
      set (chunk2 := firstn 8 (skipn (Z.to_nat (j + 8)) full)) in RD.
      assert (CL2 : length chunk2 = 8%nat). { subst chunk2. rewrite length_firstn, length_skipn. lia. }
      pose proof (le_val_range _ (bytes_ok_map chunk2)) as WR2. rewrite length_map, CL2 in WR2.
      change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR2.
      replace (wa (A + (j + 8))) with (wa (A + j + 8)) in RD by (f_equal; lia).
      do 7 zstep. rewrite (load8_le_val chunk2 CL2).
      if_cases K8; zify_cond K8.
      + (* [comment removed for export] *)
        apply (haszero64_clang _ (bytes_ok_map chunk2) ltac:(rewrite length_map; exact CL2)) in K8.
        rewrite In0_map_unsigned in K8.
        assert (Hj16 : (j + 16 <= len)%Z).
        { destruct (Z.lt_ge_cases len (j + 16)); [|assumption]. exfalso. apply K8. subst chunk2.
          apply nth_error_In with (n := (Z.to_nat len - Z.to_nat (j + 8))%nat).
          rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
          rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
        replace (A + j + 8)%Z with (A + (j + 8))%Z by lia.
        apply (IH (Z.to_nat (len - (j + 8))) ltac:(lia) (j + 8)%Z); try lia; try exact HN8; try reflexivity.
        all: Z.div_mod_to_equations; lia.
      + (* [comment removed for export] *)
        zstep. zstep. replace (A + j + 7)%Z with (A + (j + 8) - 1)%Z by lia.
        apply (strchrnul_tail (Z.to_nat (len - (j + 8))) (j + 8)); try lia. exact HN8.
  Qed.

  (* [comment removed for export] *)
  Definition strchrnul_wentry__stmt : Prop := forall (j : Z) xra xs0 x10 x12 x13 x14 x15 x16 x17,
    (0 <= j <= len)%Z -> ((A + j) mod 8 = 0)%Z -> NOB j -> x10 = Z_to_bv 64 (A + j) ->
    evtF asegs RNG POST (AT 0x9f028 xra xs0 x10 x12 x13 x14 x15 x16 x17).
  Section Sz13.
  Variables j xra xs0 x10 x12 x13 x14 x15 x16 x17 : ltac2:(SecDiet.SzSec.tyM 'strchrnul_wentry__stmt "vvvvvvvvvv" @j).
  Lemma strchrnul_wentry__body : ltac2:(SecDiet.SzSec.bodyP 'strchrnul_wentry__stmt "vvvvvvvvvv").
  Proof using FR LO MI MU NONUL PAD ST STR WM RSTR RIMG RSTK. pin_using (fun (FR LO MI MU NONUL PAD ST STR WM : unit) => tt).
    intros Hj Hal HN ->.
 pose proof A_bound as AB.
    assert (HW : (Z.to_nat j + 8 <= length full)%nat).
    { rewrite full_length. Z.div_mod_to_equations. lia. }
    pose proof (bytes_at_read asegs m1 A full j 8 STR ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat j) full)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite length_firstn, length_skipn. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    do 9 zstep. rewrite (load8_le_val chunk CL).
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      do 2 zstep. replace (A + j + -1)%Z with (A + j - 1)%Z by lia.
      apply (strchrnul_tail (Z.to_nat (len - j)) j); try lia. exact HN.
    - apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in K.
      rewrite In0_map_unsigned in K.
      assert (Hj8 : (j + 8 <= len)%Z).
      { destruct (Z.lt_ge_cases len (j + 8)); [|assumption]. exfalso. apply K. subst chunk.
        apply nth_error_In with (n := (Z.to_nat len - Z.to_nat j)%nat).
        rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_error_skipn, <- full_nth_len. f_equal. lia. }
      do 2 zstep.
      replace (c * (CMAGIC + 1))%Z with (c * ONES)%Z by reflexivity.
      apply (strchrnul_words (Z.to_nat (len - j)) j xra xs0 chunk); try lia; try exact HN. reflexivity.
  Qed.
  End Sz13.
  Lemma strchrnul_wentry : ltac:(let t := eval cbv delta [strchrnul_wentry__stmt] in strchrnul_wentry__stmt in exact t).
  Proof using FR LO MI MU NONUL PAD ST STR WM RSTR RIMG RSTK. intros j xra xs0 x10 x12 x13 x14 x15 x16 x17. ltac2:(SecDiet.SzSec.closeP 'strchrnul_wentry__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma strchrnul_head : forall (k : nat) (i : Z) xra xs0 x10 x12 x13 x14 x15 x16 x17,
    Z.to_nat (len - i) = k -> (0 <= i <= len)%Z -> NOB i -> x10 = Z_to_bv 64 (A + i) -> x12 = Z_to_bv 64 (A + i + 1) ->
    evtF asegs RNG POST (AT 0x9f00c xra xs0 x10 x12 x13 x14 x15 x16 x17).
  Proof using FR LO MI MU NONUL PAD ST STR WM RSTR RIMG RSTK. pin_using (fun (FR LO MI MU NONUL PAD ST STR WM : unit) => tt).
    induction k as [|k IH]; intros i xra xs0 x10 x12 x13 x14 x15 x16 x17 Hk Hi HN -> ->; pose proof A_bound as AB.
    - assert (Ei : i = len) by lia. subst i.
      pose proof (u8ro_read asegs m1 A full len _ _ STR full_nth_len ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
      replace (A + len)%Z with (A + Z.of_nat (strchrnul_idx c str))%Z by (rewrite idx_end; [lia|exact HN]).
      apply strchrnul_ret_any.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hns & Hb).
      pose proof (u8ro_read asegs m1 A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
      zstep. zstep. if_cases K; zify_cond K. { exfalso. exact (Hb K). }
      zstep. if_cases K2; zify_cond K2.
      { (* [comment removed for export] *)
        rewrite <- (idx_found i b ltac:(lia) HN Hns K2). apply strchrnul_ret_any. }
      pose proof (NOB_S i b ltac:(lia) HN Hns K2) as HN1.
      do 4 zstep. if_cases Kal; zify_cond Kal.
      + apply (IH (i + 1)%Z); try lia; try (f_equal; lia). exact HN1.
      + apply (strchrnul_wentry (i + 1)); try lia; try exact HN1; try (f_equal; lia).
        revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
  Qed.
End StrchrnulProof.

Lemma strchrnul_idx_nul : forall str, ~ In (Z_to_bv 8 0) str -> strchrnul_idx 0 str = length str.
Proof.
  intros str H. unfold strchrnul_idx. rewrite find_byte_notin; [reflexivity|].
  intros b Hb E. apply H. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
Qed.

Definition strchrnul_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 mod 256 <> 0)%Z ->   (* [comment removed for export] *)
  rng RNG (bv_unsigned a0) (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) -> rng_aimg RNG -> rng RNG (bv_unsigned sp + -16) 16 ->
  evtF asegs RNG (strchrnul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9efec) fc None m (seg_rom asegs)).
Section Sz16.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'strchrnul_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma strchrnul_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strchrnul_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST STR NONUL PAD MI LO SEP CNZ RSTR RIMG RSTK.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  carve_frame 16%nat ST.
  do 3 step.
  zstep. replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
  zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *) exfalso. apply CNZ. exact K0.
  - zstep. zstep. if_cases Kal; zify_cond Kal.
    + (* [comment removed for export] *)
      eapply strchrnul_wentry with (j := 0%Z); try reflexivity; try eassumption; try lia; try apply NOB_0.
      * revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal.
      * rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
    + zstep.
      eapply strchrnul_head with (i := 0%Z); try reflexivity; try eassumption; try lia; try apply NOB_0; try (f_equal; lia).
      rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
End Sz16.
Lemma strchrnul_spec : ltac:(let t := eval cbv delta [strchrnul_spec__stmt] in strchrnul_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'strchrnul_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Definition strchr_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 mod 256 <> 0)%Z ->
  rng RNG (bv_unsigned a0) (Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack))) -> rng_aimg RNG -> rng RNG (bv_unsigned sp + -32) 32 ->
  evtF asegs RNG (strchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9efb0) fc None m (seg_rom asegs)).
Section Sz17.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo : ltac2:(SecDiet.SzSec.tyM 'strchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma strchr_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strchr_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST STR NONUL PAD MI LO SEP CNZ RSTR RIMG RSTK.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  carve_frame 16%nat ST.
  do 4 step.
  step. call_sp strchrnul_spec; [exact ST | exact STR | exact NONUL | exact PAD | exact MI | lia | lia | exact CNZ | ].
  rename PC into ST; clear STR; rename POST into STR.
  (* [comment removed for export] *)
  set (i := strchrnul_idx (bv_unsigned a1 mod 256) str) in *.
  pose proof (strchrnul_idx_le (bv_unsigned a1 mod 256) str) as Hi. fold i in Hi.
  assert (Hb : exists b, nth_error (str ++ Z_to_bv 8 0 :: slack) i = Some b /\
                         (bv_unsigned b = bv_unsigned a1 mod 256 -> strchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str = bv_unsigned a0 + Z.of_nat i)%Z /\
                         (bv_unsigned b <> bv_unsigned a1 mod 256 -> strchr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str = 0)%Z).
  { unfold strchr_res. subst i. unfold strchrnul_idx.
    destruct (find_byte (bv_unsigned a1 mod 256) str) as [j|] eqn:FB.
    - destruct (find_byte_Some _ _ _ FB) as (Hj & (b & Hn & Hbb) & _). exists b.
      rewrite nth_error_app1 by lia. split; [exact Hn|].
      destruct (Z.eqb_spec (bv_unsigned a1 mod 256) 0) as [E|NE].
      { exfalso. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. } apply bv_eq. rewrite Hbb, E. reflexivity. }
      split; [intros _; reflexivity | intros X; exfalso; exact (X Hbb)].
    - exists (Z_to_bv 8 0). rewrite nth_error_app2, Nat.sub_diag by lia. split; [reflexivity|].
      destruct (Z.eqb_spec (bv_unsigned a1 mod 256) 0) as [E|NE].
      + split; [intros _; reflexivity | intros X; exfalso; apply X; rewrite E; reflexivity].
      + split; [intros X; exfalso; apply NE; rewrite <- X; reflexivity | intros _; reflexivity]. }
  destruct Hb as (b & Hn & Heq & Hne).
  pose proof (u8ro_read asegs _ (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) (Z.of_nat i) b (wa (bv_unsigned a0 + Z.of_nat i + 0)) STR
                ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(f_equal; lia)) as RD.
  pose proof (byte_range b) as Rb.
  do 6 zstep.
  replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
  do 3 step. release_frame FR ST (bv_unsigned sp). step.
  destruct (Z.eq_dec (bv_unsigned b) (bv_unsigned a1 mod 256)) as [E|NE].
  - rewrite E, Z.lxor_nilpotent. change (Z.b2z (0 <? 0) + -1)%Z with (-1)%Z.
    replace (Z.land ((-1) mod 18446744073709551616) (bv_unsigned a0 + Z.of_nat i))%Z with (bv_unsigned a0 + Z.of_nat i)%Z.
    2:{ change ((-1) mod 18446744073709551616)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
    rewrite <- (Heq E). unfold strchr_post. finish.
  - assert (Hx : (0 <? Z.lxor (bv_unsigned b) (bv_unsigned a1 mod 256))%Z = true).
    { apply Z.ltb_lt. pose proof (Z.lxor_nonneg (bv_unsigned b) (bv_unsigned a1 mod 256)).
      destruct (Z.eq_dec (Z.lxor (bv_unsigned b) (bv_unsigned a1 mod 256)) 0) as [E0|]; [|lia].
      apply Z.lxor_eq in E0. exfalso. exact (NE E0). }
    rewrite Hx. change (Z.b2z true + -1)%Z with 0%Z. change (0 mod 18446744073709551616)%Z with 0%Z. rewrite Z.land_0_l.
    rewrite <- (Hne NE). unfold strchr_post. finish.
Qed.
End Sz17.
Lemma strchr_spec : ltac:(let t := eval cbv delta [strchr_spec__stmt] in strchr_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo. ltac2:(SecDiet.SzSec.closeP 'strchr_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_strchr.

(* [comment removed for export] *)
Module F_strerror.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Bytes SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require StrerrorData. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.StrerrorData OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv asegs _ |- _ => exact H end.

(* [comment removed for export] *)
Definition ERRMSGIDX_A : Z := 0x23c64.
Definition ERRMSGSTR_A : Z := 0x234bc.

Definition strerror_entry := 0x944c4%Z.
Definition strerror_r_entry := 0x9ed20%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition strerror_e (e : Z) : Z := if ((0 <=? e) && (e <? 132))%Z then e else 0.

(* [comment removed for export] *)
Definition strerror_tab : list byte := errmsgstr_bytes ++ errmsgidx_bytes.

(* [comment removed for export] *)
Definition sr_idx (k : Z) : Z :=
  bv_unsigned (zext 64 (bv_extract 0 16 (le_bytes_to_word (firstn 2 (skipn (Z.to_nat (2 * k)) errmsgidx_bytes))))).
Definition sr_res (k : Z) : Z := ERRMSGSTR_A + sr_idx k.
Definition sr_msgb (k : Z) : list byte := map (Z_to_bv 8) (nth (Z.to_nat k) strerror_msgZ []).
Definition sr_slack (k : Z) : list byte :=
  firstn 7 (skipn (Z.to_nat (sr_idx k) + length (sr_msgb k) + 1) strerror_tab).

Definition strerror_res (e : Z) : Z := sr_res (strerror_e e).
Definition strerror_msgb (e : Z) : list byte := sr_msgb (strerror_e e).
Definition strerror_slack (e : Z) : list byte := sr_slack (strerror_e e).

Example strerror_res_2 : strerror_res 2 = (0x234bc + 133)%Z. Proof. vm_compute. reflexivity. Qed.
Example strerror_res_neg : strerror_res (-7) = 0x234bc%Z. Proof. vm_compute. reflexivity. Qed.
Example strerror_msgb_12 : map bv_unsigned (strerror_msgb 12) = [79; 117; 116; 32; 111; 102; 32; 109; 101; 109; 111; 114; 121]%Z. (* [comment removed for export] *)
Proof. vm_compute. reflexivity. Qed.

Lemma strerror_e_range : forall e, (0 <= strerror_e e < 132)%Z.
Proof. intros e. unfold strerror_e. destruct (Z.leb_spec0 0 e), (Z.ltb_spec0 e 132); cbn; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma errmsgidx_at : forall m, mem_inv asegs m -> bytes_at asegs m ERRMSGIDX_A errmsgidx_bytes.
Proof.
  intros m MI.
  pose proof (ro_cells_image asegs m ERRMSGIDX_A errmsgidx_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold ERRMSGIDX_A; lia)
                ltac:(unfold errmsgidx_bytes, ERRMSGIDX_A; rewrite length_map; vm_compute (length errmsgidx_Z); lia)) as RO.
  apply ro_cells_bytes_at in RO. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO. exact RO.
Qed.

Lemma strerror_tab_at : forall m, mem_inv asegs m -> bytes_at asegs m ERRMSGSTR_A strerror_tab.
Proof.
  intros m MI.
  pose proof (ro_cells_image asegs m ERRMSGSTR_A strerror_tab MI ltac:(vm_compute; reflexivity) ltac:(unfold ERRMSGSTR_A; lia)
                ltac:(unfold strerror_tab, errmsgstr_bytes, errmsgidx_bytes, ERRMSGSTR_A; rewrite length_app, !length_map;
                      vm_compute (length errmsgidx_Z); vm_compute (length errmsgstr_Z); lia)) as RO.
  apply ro_cells_bytes_at in RO. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO. exact RO.
Qed.

Lemma bytes_at_sub : forall m A l (i n : nat), bytes_at asegs m A l -> (i + n <= length l)%nat ->
  bytes_at asegs m (A + Z.of_nat i) (firstn n (skipn i l)).
Proof.
  intros m A l i n H Hl.
  rewrite <- (firstn_skipn i l) in H. apply (proj1 (bytes_at_app _ _ _ _ _)) in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn n (skipn i l)) in H. apply (proj1 (bytes_at_app _ _ _ _ _)) in H. destruct H as [H _]. exact H.
Qed.

Lemma notin0_of_forallb : forall l : list byte,
  forallb (fun b => negb (bv_unsigned b =? 0)%Z) l = true -> ~ In (Z_to_bv 8 0) l.
Proof.
  intros l H Hin. apply forallb_forall with (x := Z_to_bv 8 0) in H; [|exact Hin]. cbn in H. discriminate.
Qed.

Lemma Zcases_nat : forall (P : Z -> Prop) (n : nat),
  (forall k : nat, (k < n)%nat -> P (Z.of_nat k)) -> forall z, (0 <= z < Z.of_nat n)%Z -> P z.
Proof. intros P n H z Hz. replace z with (Z.of_nat (Z.to_nat z)) by lia. apply H. lia. Qed.

Local Ltac sr_case TAB :=
  lazymatch goal with |- bytes_at _ _ (sr_res (Z.of_nat ?k)) _ /\ _ =>
    let i := eval vm_compute in (Z.to_nat (sr_idx (Z.of_nat k))) in
    let n := eval vm_compute in (length (sr_msgb (Z.of_nat k)) + 8)%nat in
    split; [ replace (sr_res (Z.of_nat k)) with (ERRMSGSTR_A + Z.of_nat i)%Z by (vm_compute; reflexivity);
             replace (sr_msgb (Z.of_nat k) ++ Z_to_bv 8 0 :: sr_slack (Z.of_nat k)) with (firstn n (skipn i strerror_tab)) by (vm_compute; reflexivity);
             apply (bytes_at_sub _ _ _ i n TAB); vm_compute; lia
           | split; [ apply notin0_of_forallb; vm_compute; reflexivity | vm_compute; reflexivity ] ]
  end.

(* [comment removed for export] *)
Lemma bytes_eq_chk_s : forall l1 l2 : list byte, length l1 = length l2 ->
  forallb (fun p => Z.eqb (bv_unsigned (fst p)) (bv_unsigned (snd p))) (combine l1 l2) = true -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] Hl H; cbn in *; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [apply bv_eq; exact H1 | apply IH; [lia | exact H2]].
Qed.

Lemma sr_msg_at : forall m k, mem_inv asegs m -> (0 <= k < 132)%Z ->
  bytes_at asegs m (sr_res k) (sr_msgb k ++ Z_to_bv 8 0 :: sr_slack k) /\ ~ In (Z_to_bv 8 0) (sr_msgb k) /\ length (sr_slack k) = 7%nat.
Proof.
  intros m k MI Hk. pose proof (strerror_tab_at m MI) as TAB.
  assert (ALL : forallb (fun j : nat =>
      let K := Z.of_nat j in let i := Z.to_nat (sr_idx K) in let n := (length (sr_msgb K) + 8)%nat in
      forallb (fun p => Z.eqb (bv_unsigned (fst p)) (bv_unsigned (snd p)))
              (combine (sr_msgb K ++ Z_to_bv 8 0 :: sr_slack K) (firstn n (skipn i strerror_tab)))
      && Nat.eqb (length (sr_msgb K ++ Z_to_bv 8 0 :: sr_slack K)) (length (firstn n (skipn i strerror_tab)))
      && Nat.leb (i + n) (length strerror_tab)
      && forallb (fun b => negb (bv_unsigned b =? 0)%Z) (sr_msgb K)
      && Nat.eqb (length (sr_slack K)) 7
      && Z.eqb (sr_res K) (ERRMSGSTR_A + Z.of_nat i)) (seq 0 132) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat k) ltac:(apply in_seq; lia)). cbv beta zeta in ALL.
  rewrite Z2Nat.id in ALL by lia.
  apply andb_true_iff in ALL as [ALL E6]. apply andb_true_iff in ALL as [ALL E5]. apply andb_true_iff in ALL as [ALL E4].
  apply andb_true_iff in ALL as [ALL E3]. apply andb_true_iff in ALL as [E1 E2].
  apply Nat.eqb_eq in E2. apply Nat.leb_le in E3. apply Nat.eqb_eq in E5. apply Z.eqb_eq in E6.
  split; [| split; [apply notin0_of_forallb; exact E4 | exact E5]].
  rewrite E6, (bytes_eq_chk_s _ _ E2 E1). apply bytes_at_sub; [exact TAB | exact E3].
Qed.

(* [comment removed for export] *)
Lemma strerror_msg_at : forall m e, mem_inv asegs m ->
  bytes_at asegs m (strerror_res e) (strerror_msgb e ++ Z_to_bv 8 0 :: strerror_slack e)
  /\ ~ In (Z_to_bv 8 0) (strerror_msgb e) /\ length (strerror_slack e) = 7%nat.
Proof. intros m e MI. apply sr_msg_at; [exact MI | apply strerror_e_range]. Qed.

Lemma strerror_msgb_length : forall e, (length (strerror_msgb e) <= 40)%nat.
Proof.
  intros e. unfold strerror_msgb. pose proof (strerror_e_range e) as R.
  assert (ALL : forallb (fun j : nat => Nat.leb (length (sr_msgb (Z.of_nat j))) 40) (seq 0 132) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat (strerror_e e)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in ALL by lia. apply Nat.leb_le in ALL. exact ALL.
Qed.

Lemma strerror_res_range : forall e, (0x234bc <= strerror_res e /\ strerror_res e + 48 <= 0x23d70)%Z.
Proof.
  intros e. unfold strerror_res. pose proof (strerror_e_range e) as R.
  assert (ALL : forallb (fun j : nat => (0x234bc <=? sr_res (Z.of_nat j)) && (sr_res (Z.of_nat j) + 48 <=? 0x23d70))%Z (seq 0 132) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat (strerror_e e)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in ALL by lia. apply andb_true_iff in ALL as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2. split; assumption.
Qed.

(* [comment removed for export] *)
Definition strerror_index_eq__stmt : Prop := forall e, (-2^31 <= e < 2^31)%Z ->
  Z.shiftl (Z.land ((0 - Z.b2z (e mod 18446744073709551616 <? 132)%Z) mod 18446744073709551616) (e mod 18446744073709551616)) 1 = (2 * strerror_e e)%Z.
Section Sz11.
Variables e : ltac2:(SecDiet.SzSec.tyM 'strerror_index_eq__stmt "v" @e).
#[using="Type"] Lemma strerror_index_eq__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_index_eq__stmt "v").
Proof.
  intros He.
 unfold strerror_e. rewrite Z.shiftl_mul_pow2 by lia.
  destruct (Z.leb_spec0 0 e).
  - rewrite (Z.mod_small e) by lia. destruct (Z.ltb_spec0 e 132); cbn [Z.b2z andb].
    + change ((0 - 1) mod 18446744073709551616)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. lia.
    + rewrite Z.mod_0_l, Z.land_0_l by lia. lia.
  - replace (e mod 18446744073709551616)%Z with (18446744073709551616 + e)%Z.
    2:{ symmetry. replace e with ((18446744073709551616 + e) + (-1) * 18446744073709551616)%Z at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    destruct (Z.ltb_spec0 (18446744073709551616 + e) 132); [lia|]. cbn [Z.b2z andb]. rewrite Z.mod_0_l, Z.land_0_l by lia. lia.
Qed.
End Sz11.
Lemma strerror_index_eq : ltac:(let t := eval cbv delta [strerror_index_eq__stmt] in strerror_index_eq__stmt in exact t).
Proof. intros e. ltac2:(SecDiet.SzSec.closeP 'strerror_index_eq__body "v"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition strerror_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (e loc lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strerror_res e)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)]
    /\ rw_cells asegs m' (loc + 40) [C8 (Z_to_bv 64 0)].

Definition strerror_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e loc lo : Z),
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z ->
  rw_cells asegs m (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)] ->
  rw_cells asegs m (loc + 40) [C8 (Z_to_bv 64 0)] ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 e -> (-2^31 <= e < 2^31)%Z ->
  (48 <= bv_unsigned tp)%Z -> (0 <= loc /\ loc + 48 <= 2^64)%Z ->
  (bv_unsigned tp - 40 <= lo \/ bv_unsigned sp <= bv_unsigned tp - 48)%Z ->       (* [comment removed for export] *)
  (loc + 48 <= lo \/ bv_unsigned sp <= loc + 40)%Z ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned tp + -48) 8 -> rng RNG (loc + 40) 8 ->
  evtF asegs RNG (strerror_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc e loc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x944c4) fc None m (seg_rom asegs)).
Section Sz12.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e loc lo : ltac2:(SecDiet.SzSec.tyM 'strerror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma strerror_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST LO TLSL LOC MI -> He Htp Hloc SEP1 SEP2 RIMG RSTK RTL RLOC.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (errmsgidx_at m MI) as TABI.
  set (e' := strerror_e e). pose proof (strerror_e_range e) as He'. fold e' in He'.
  assert (HW : (Z.to_nat (2 * e') + 2 <= length errmsgidx_bytes)%nat).
  { unfold errmsgidx_bytes. rewrite length_map. vm_compute (length errmsgidx_Z). lia. }
  pose proof (bytes_at_read asegs m ERRMSGIDX_A errmsgidx_bytes (2 * e') 2 TABI ltac:(lia) HW) as RD. unfold ERRMSGIDX_A in RD.
  do 8 zstep. rewrite strerror_index_eq by lia. fold e'.
  do 6 zstep.
  replace (144572 + _)%Z with (strerror_res e) by reflexivity.
  zstep. zstep.                                (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 4 zstep. zstep. if_true.                  (* [comment removed for export] *)
  zstep. zstep. if_false.                      (* [comment removed for export] *)
  do 5 zstep.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  zstep.
  unfold strerror_post. finish.
Qed.
End Sz12.
#[using="Type"] Lemma strerror_spec : ltac:(let t := eval cbv delta [strerror_spec__stmt] in strerror_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e loc lo. ltac2:(SecDiet.SzSec.closeP 'strerror_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.StrerrorData OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv asegs _ |- _ => exact H end.

(* [comment removed for export] *)
Definition ERRMSGIDX_A : Z := 0x23c64.
Definition ERRMSGSTR_A : Z := 0x234bc.

Definition strerror_entry := 0x948a8%Z.
Definition strerror_r_entry := 0x9f104%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition strerror_e (e : Z) : Z := if ((0 <=? e) && (e <? 132))%Z then e else 0.

(* [comment removed for export] *)
Definition strerror_tab : list byte := errmsgstr_bytes ++ errmsgidx_bytes.

(* [comment removed for export] *)
Definition sr_idx (k : Z) : Z :=
  bv_unsigned (zext 64 (bv_extract 0 16 (le_bytes_to_word (firstn 2 (skipn (Z.to_nat (2 * k)) errmsgidx_bytes))))).
Definition sr_res (k : Z) : Z := ERRMSGSTR_A + sr_idx k.
Definition sr_msgb (k : Z) : list byte := map (Z_to_bv 8) (nth (Z.to_nat k) strerror_msgZ []).
Definition sr_slack (k : Z) : list byte :=
  firstn 7 (skipn (Z.to_nat (sr_idx k) + length (sr_msgb k) + 1) strerror_tab).

Definition strerror_res (e : Z) : Z := sr_res (strerror_e e).
Definition strerror_msgb (e : Z) : list byte := sr_msgb (strerror_e e).
Definition strerror_slack (e : Z) : list byte := sr_slack (strerror_e e).

Example strerror_res_2 : strerror_res 2 = (0x234bc + 133)%Z. Proof. vm_compute. reflexivity. Qed.
Example strerror_res_neg : strerror_res (-7) = 0x234bc%Z. Proof. vm_compute. reflexivity. Qed.
Example strerror_msgb_12 : map bv_unsigned (strerror_msgb 12) = [79; 117; 116; 32; 111; 102; 32; 109; 101; 109; 111; 114; 121]%Z. (* [comment removed for export] *)
Proof. vm_compute. reflexivity. Qed.

Lemma strerror_e_range : forall e, (0 <= strerror_e e < 132)%Z.
Proof. intros e. unfold strerror_e. destruct (Z.leb_spec0 0 e), (Z.ltb_spec0 e 132); cbn; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma errmsgidx_at : forall m, mem_inv asegs m -> bytes_at asegs m ERRMSGIDX_A errmsgidx_bytes.
Proof.
  intros m MI.
  pose proof (ro_cells_image asegs m ERRMSGIDX_A errmsgidx_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold ERRMSGIDX_A; lia)
                ltac:(unfold errmsgidx_bytes, ERRMSGIDX_A; rewrite length_map; vm_compute (length errmsgidx_Z); lia)) as RO.
  apply ro_cells_bytes_at in RO. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO. exact RO.
Qed.

Lemma strerror_tab_at : forall m, mem_inv asegs m -> bytes_at asegs m ERRMSGSTR_A strerror_tab.
Proof.
  intros m MI.
  pose proof (ro_cells_image asegs m ERRMSGSTR_A strerror_tab MI ltac:(vm_compute; reflexivity) ltac:(unfold ERRMSGSTR_A; lia)
                ltac:(unfold strerror_tab, errmsgstr_bytes, errmsgidx_bytes, ERRMSGSTR_A; rewrite length_app, !length_map;
                      vm_compute (length errmsgidx_Z); vm_compute (length errmsgstr_Z); lia)) as RO.
  apply ro_cells_bytes_at in RO. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO. exact RO.
Qed.

Lemma bytes_at_sub : forall m A l (i n : nat), bytes_at asegs m A l -> (i + n <= length l)%nat ->
  bytes_at asegs m (A + Z.of_nat i) (firstn n (skipn i l)).
Proof.
  intros m A l i n H Hl.
  rewrite <- (firstn_skipn i l) in H. apply (proj1 (bytes_at_app _ _ _ _ _)) in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn n (skipn i l)) in H. apply (proj1 (bytes_at_app _ _ _ _ _)) in H. destruct H as [H _]. exact H.
Qed.

Lemma notin0_of_forallb : forall l : list byte,
  forallb (fun b => negb (bv_unsigned b =? 0)%Z) l = true -> ~ In (Z_to_bv 8 0) l.
Proof.
  intros l H Hin. apply forallb_forall with (x := Z_to_bv 8 0) in H; [|exact Hin]. cbn in H. discriminate.
Qed.

Lemma Zcases_nat : forall (P : Z -> Prop) (n : nat),
  (forall k : nat, (k < n)%nat -> P (Z.of_nat k)) -> forall z, (0 <= z < Z.of_nat n)%Z -> P z.
Proof. intros P n H z Hz. replace z with (Z.of_nat (Z.to_nat z)) by lia. apply H. lia. Qed.

Local Ltac sr_case TAB :=
  lazymatch goal with |- bytes_at _ _ (sr_res (Z.of_nat ?k)) _ /\ _ =>
    let i := eval vm_compute in (Z.to_nat (sr_idx (Z.of_nat k))) in
    let n := eval vm_compute in (length (sr_msgb (Z.of_nat k)) + 8)%nat in
    split; [ replace (sr_res (Z.of_nat k)) with (ERRMSGSTR_A + Z.of_nat i)%Z by (vm_compute; reflexivity);
             replace (sr_msgb (Z.of_nat k) ++ Z_to_bv 8 0 :: sr_slack (Z.of_nat k)) with (firstn n (skipn i strerror_tab)) by (vm_compute; reflexivity);
             apply (bytes_at_sub _ _ _ i n TAB); vm_compute; lia
           | split; [ apply notin0_of_forallb; vm_compute; reflexivity | vm_compute; reflexivity ] ]
  end.

(* [comment removed for export] *)
Lemma bytes_eq_chk_s : forall l1 l2 : list byte, length l1 = length l2 ->
  forallb (fun p => Z.eqb (bv_unsigned (fst p)) (bv_unsigned (snd p))) (combine l1 l2) = true -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] Hl H; cbn in *; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [apply bv_eq; exact H1 | apply IH; [lia | exact H2]].
Qed.

Lemma sr_msg_at : forall m k, mem_inv asegs m -> (0 <= k < 132)%Z ->
  bytes_at asegs m (sr_res k) (sr_msgb k ++ Z_to_bv 8 0 :: sr_slack k) /\ ~ In (Z_to_bv 8 0) (sr_msgb k) /\ length (sr_slack k) = 7%nat.
Proof.
  intros m k MI Hk. pose proof (strerror_tab_at m MI) as TAB.
  assert (ALL : forallb (fun j : nat =>
      let K := Z.of_nat j in let i := Z.to_nat (sr_idx K) in let n := (length (sr_msgb K) + 8)%nat in
      forallb (fun p => Z.eqb (bv_unsigned (fst p)) (bv_unsigned (snd p)))
              (combine (sr_msgb K ++ Z_to_bv 8 0 :: sr_slack K) (firstn n (skipn i strerror_tab)))
      && Nat.eqb (length (sr_msgb K ++ Z_to_bv 8 0 :: sr_slack K)) (length (firstn n (skipn i strerror_tab)))
      && Nat.leb (i + n) (length strerror_tab)
      && forallb (fun b => negb (bv_unsigned b =? 0)%Z) (sr_msgb K)
      && Nat.eqb (length (sr_slack K)) 7
      && Z.eqb (sr_res K) (ERRMSGSTR_A + Z.of_nat i)) (seq 0 132) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat k) ltac:(apply in_seq; lia)). cbv beta zeta in ALL.
  rewrite Z2Nat.id in ALL by lia.
  apply andb_true_iff in ALL as [ALL E6]. apply andb_true_iff in ALL as [ALL E5]. apply andb_true_iff in ALL as [ALL E4].
  apply andb_true_iff in ALL as [ALL E3]. apply andb_true_iff in ALL as [E1 E2].
  apply Nat.eqb_eq in E2. apply Nat.leb_le in E3. apply Nat.eqb_eq in E5. apply Z.eqb_eq in E6.
  split; [| split; [apply notin0_of_forallb; exact E4 | exact E5]].
  rewrite E6, (bytes_eq_chk_s _ _ E2 E1). apply bytes_at_sub; [exact TAB | exact E3].
Qed.

(* [comment removed for export] *)
Lemma strerror_msg_at : forall m e, mem_inv asegs m ->
  bytes_at asegs m (strerror_res e) (strerror_msgb e ++ Z_to_bv 8 0 :: strerror_slack e)
  /\ ~ In (Z_to_bv 8 0) (strerror_msgb e) /\ length (strerror_slack e) = 7%nat.
Proof. intros m e MI. apply sr_msg_at; [exact MI | apply strerror_e_range]. Qed.

Lemma strerror_msgb_length : forall e, (length (strerror_msgb e) <= 40)%nat.
Proof.
  intros e. unfold strerror_msgb. pose proof (strerror_e_range e) as R.
  assert (ALL : forallb (fun j : nat => Nat.leb (length (sr_msgb (Z.of_nat j))) 40) (seq 0 132) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat (strerror_e e)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in ALL by lia. apply Nat.leb_le in ALL. exact ALL.
Qed.

Lemma strerror_res_range : forall e, (0x234bc <= strerror_res e /\ strerror_res e + 48 <= 0x23d70)%Z.
Proof.
  intros e. unfold strerror_res. pose proof (strerror_e_range e) as R.
  assert (ALL : forallb (fun j : nat => (0x234bc <=? sr_res (Z.of_nat j)) && (sr_res (Z.of_nat j) + 48 <=? 0x23d70))%Z (seq 0 132) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat (strerror_e e)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in ALL by lia. apply andb_true_iff in ALL as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2. split; assumption.
Qed.

(* [comment removed for export] *)
Definition strerror_index_eq__stmt : Prop := forall e, (-2^31 <= e < 2^31)%Z ->
  Z.shiftl (Z.land ((0 - Z.b2z (e mod 18446744073709551616 <? 132)%Z) mod 18446744073709551616) (e mod 18446744073709551616)) 1 = (2 * strerror_e e)%Z.
Section Sz11.
Variables e : ltac2:(SecDiet.SzSec.tyM 'strerror_index_eq__stmt "v" @e).
#[using="Type"] Lemma strerror_index_eq__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_index_eq__stmt "v").
Proof.
  intros He.
 unfold strerror_e. rewrite Z.shiftl_mul_pow2 by lia.
  destruct (Z.leb_spec0 0 e).
  - rewrite (Z.mod_small e) by lia. destruct (Z.ltb_spec0 e 132); cbn [Z.b2z andb].
    + change ((0 - 1) mod 18446744073709551616)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. lia.
    + rewrite Z.mod_0_l, Z.land_0_l by lia. lia.
  - replace (e mod 18446744073709551616)%Z with (18446744073709551616 + e)%Z.
    2:{ symmetry. replace e with ((18446744073709551616 + e) + (-1) * 18446744073709551616)%Z at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    destruct (Z.ltb_spec0 (18446744073709551616 + e) 132); [lia|]. cbn [Z.b2z andb]. rewrite Z.mod_0_l, Z.land_0_l by lia. lia.
Qed.
End Sz11.
Lemma strerror_index_eq : ltac:(let t := eval cbv delta [strerror_index_eq__stmt] in strerror_index_eq__stmt in exact t).
Proof. intros e. ltac2:(SecDiet.SzSec.closeP 'strerror_index_eq__body "v"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition strerror_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (e loc lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strerror_res e)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)]
    /\ rw_cells asegs m' (loc + 40) [C8 (Z_to_bv 64 0)].

Definition strerror_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e loc lo : Z),
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z ->
  rw_cells asegs m (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)] ->
  rw_cells asegs m (loc + 40) [C8 (Z_to_bv 64 0)] ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 e -> (-2^31 <= e < 2^31)%Z ->
  (48 <= bv_unsigned tp)%Z -> (0 <= loc /\ loc + 48 <= 2^64)%Z ->
  (bv_unsigned tp - 40 <= lo \/ bv_unsigned sp <= bv_unsigned tp - 48)%Z ->       (* [comment removed for export] *)
  (loc + 48 <= lo \/ bv_unsigned sp <= loc + 40)%Z ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (bv_unsigned tp + -48) 8 -> rng RNG (loc + 40) 8 ->
  evtF asegs RNG (strerror_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc e loc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x948a8) fc None m (seg_rom asegs)).
Section Sz12.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e loc lo : ltac2:(SecDiet.SzSec.tyM 'strerror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma strerror_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST LO TLSL LOC MI -> He Htp Hloc SEP1 SEP2 RIMG RSTK RTL RLOC.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (errmsgidx_at m MI) as TABI.
  set (e' := strerror_e e). pose proof (strerror_e_range e) as He'. fold e' in He'.
  assert (HW : (Z.to_nat (2 * e') + 2 <= length errmsgidx_bytes)%nat).
  { unfold errmsgidx_bytes. rewrite length_map. vm_compute (length errmsgidx_Z). lia. }
  pose proof (bytes_at_read asegs m ERRMSGIDX_A errmsgidx_bytes (2 * e') 2 TABI ltac:(lia) HW) as RD. unfold ERRMSGIDX_A in RD.
  do 8 zstep. rewrite strerror_index_eq by lia. fold e'.
  do 6 zstep.
  replace (144572 + _)%Z with (strerror_res e) by reflexivity.
  zstep. zstep.                                (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 4 zstep. zstep. if_true.                  (* [comment removed for export] *)
  zstep. zstep. if_false.                      (* [comment removed for export] *)
  do 5 zstep.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  zstep.
  unfold strerror_post. finish.
Qed.
End Sz12.
#[using="Type"] Lemma strerror_spec : ltac:(let t := eval cbv delta [strerror_spec__stmt] in strerror_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e loc lo. ltac2:(SecDiet.SzSec.closeP 'strerror_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End CANSEC1.
End TwB.
End F_strerror.

(* [comment removed for export] *)
Module F_pop_arg.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Definition pop_arg_entry := 0x9bec0%Z.
Definition T_PTR := 9%Z. Definition T_INT := 10%Z. Definition T_UINT := 11%Z. Definition T_SIZET := 20%Z.

(* [comment removed for export] *)
Definition va_area (m : word -> option byte) (VA : Z) (slots : list word) : Prop :=
  bytes_at asegs m VA (u64s slots).

(* [comment removed for export] *)
Definition pop_arg_lo (ty : Z) (slot : word) : word :=
  if (ty =? T_INT)%Z then sx32 slot
  else if (ty =? T_UINT)%Z then zx32 slot
  else slot.                                   (* [comment removed for export] *)
Definition pop_arg_hi (ty : Z) (slot y : word) : word := y.

Definition pop_arg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ARG AP VA : Z) (slots : list word) (i ty : Z) (slot y : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' (bv_unsigned sp - 16) (bv_unsigned sp)
    /\ rw_cells asegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (i + 1)))]
    /\ rw_cells asegs m' ARG [C8 (pop_arg_lo ty slot); C8 (pop_arg_hi ty slot y)]
    /\ va_area m' VA slots
    /\ Ft = F.   (* [comment removed for export] *)

Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Definition va_read8__stmt : Prop := forall m VA slots (i : Z) w a,
  bytes_at asegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes asegs m a 8 = Some (le8 w).
Section Sz2.
Variables m VA slots i w a : ltac2:(SecDiet.SzSec.tyM 'va_read8__stmt "vvvvvv" @m).
#[using="Type"] Lemma va_read8__body : ltac2:(SecDiet.SzSec.bodyP 'va_read8__stmt "vvvvvv").
Proof.
  intros Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read asegs m VA (u64s slots) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
End Sz2.
Lemma va_read8 : ltac:(let t := eval cbv delta [va_read8__stmt] in va_read8__stmt in exact t).
Proof. intros m VA slots i w a. ltac2:(SecDiet.SzSec.closeP 'va_read8__body "vvvvvv"). Qed.

Definition va_read4__stmt : Prop := forall m VA slots (i : Z) w a,
  bytes_at asegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes asegs m a 4 = Some (le4 w).
Section Sz3.
Variables m VA slots i w a : ltac2:(SecDiet.SzSec.tyM 'va_read4__stmt "vvvvvv" @m).
#[using="Type"] Lemma va_read4__body : ltac2:(SecDiet.SzSec.bodyP 'va_read4__stmt "vvvvvv").
Proof.
  intros Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read asegs m VA (u64s slots) (8 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app. rewrite length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r.
  rewrite firstn4_le8. reflexivity.
Qed.
End Sz3.
Lemma va_read4 : ltac:(let t := eval cbv delta [va_read4__stmt] in va_read4__stmt in exact t).
Proof. intros m VA slots i w a. ltac2:(SecDiet.SzSec.closeP 'va_read4__body "vvvvvv"). Qed.

Lemma va_area_bound : forall m VA slots, va_area m VA slots -> (0 <= VA /\ VA + 8 * Z.of_nat (length slots) <= 2^64)%Z.
Proof. intros m VA slots H. pose proof (bytes_at_bound _ _ _ _ H) as B. rewrite u64s_length in B. lia. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

Definition pop_arg_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (VA : Z) (slots : list word) (i ty : Z) (slot x y : word),
  rw_cells asegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
  va_area m VA slots -> nth_error slots (Z.to_nat i) = Some slot -> (0 <= i)%Z ->
  rw_cells asegs m (bv_unsigned a0) [C8 x; C8 y] ->
  stk asegs m (bv_unsigned sp - 16) (bv_unsigned sp) ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 ty -> (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_SIZET) ->
  (16 <= bv_unsigned sp)%Z ->
  (bv_unsigned sp <= bv_unsigned a2)%Z -> (bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned a2)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= VA)%Z ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG (bv_unsigned sp - 16) 16 -> rng RNG (bv_unsigned a2) 8 -> rng RNG (bv_unsigned a0) 16 ->
  rng RNG VA (8 * Z.of_nat (length slots)) ->
  evtF asegs RNG (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) (bv_unsigned a2) VA slots i ty slot y m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9bec0) fc None m (seg_rom asegs)).
Section Sz5.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m VA slots i ty slot x y : ltac2:(SecDiet.SzSec.tyM 'pop_arg_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma pop_arg_spec__body : ltac2:(SecDiet.SzSec.bodyP 'pop_arg_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros APC VAA NTH Hi ARGC ST MI -> TY SPLO A2 A0 SEP1 SEP2 SEP3 SEP4 RIMG RFR RAP RARG RVA.
  pose_word_ranges.
  pose proof (va_area_bound _ _ _ VAA) as VB. unfold va_area in VAA.
  assert (IL : (Z.to_nat i < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
  set (AP := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 AP) by (unfold AP; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (ARG := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 ARG) by (unfold ARG; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  destruct TY as [-> | [-> | [-> | ->]]]; unfold T_PTR, T_INT, T_UINT, T_SIZET, pop_arg_lo, pop_arg_hi; cbn [Z.eqb Pos.eqb].
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
Qed.
End Sz5.
Lemma pop_arg_spec : ltac:(let t := eval cbv delta [pop_arg_spec__stmt] in pop_arg_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m VA slots i ty slot x y. ltac2:(SecDiet.SzSec.closeP 'pop_arg_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Definition pop_arg_entry := 0x9c2a4%Z.
Definition T_PTR := 9%Z. Definition T_INT := 10%Z. Definition T_UINT := 11%Z. Definition T_SIZET := 20%Z.

(* [comment removed for export] *)
Definition va_area (m : word -> option byte) (VA : Z) (slots : list word) : Prop :=
  bytes_at asegs m VA (u64s slots).

(* [comment removed for export] *)
Definition pop_arg_lo (ty : Z) (slot : word) : word :=
  if (ty =? T_INT)%Z then sx32 slot
  else if (ty =? T_UINT)%Z then zx32 slot
  else slot.                                   (* [comment removed for export] *)
Definition pop_arg_hi (ty : Z) (slot y : word) : word := y.

Definition pop_arg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ARG AP VA : Z) (slots : list word) (i ty : Z) (slot y : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ft m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' (bv_unsigned sp - 16) (bv_unsigned sp)
    /\ rw_cells asegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (i + 1)))]
    /\ rw_cells asegs m' ARG [C8 (pop_arg_lo ty slot); C8 (pop_arg_hi ty slot y)]
    /\ va_area m' VA slots
    /\ Ft = F.   (* [comment removed for export] *)

Lemma firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. reflexivity. Qed.

Definition va_read8__stmt : Prop := forall m VA slots (i : Z) w a,
  bytes_at asegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes asegs m a 8 = Some (le8 w).
Section Sz2.
Variables m VA slots i w a : ltac2:(SecDiet.SzSec.tyM 'va_read8__stmt "vvvvvv" @m).
#[using="Type"] Lemma va_read8__body : ltac2:(SecDiet.SzSec.bodyP 'va_read8__stmt "vvvvvv").
Proof.
  intros Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read asegs m VA (u64s slots) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
End Sz2.
Lemma va_read8 : ltac:(let t := eval cbv delta [va_read8__stmt] in va_read8__stmt in exact t).
Proof. intros m VA slots i w a. ltac2:(SecDiet.SzSec.closeP 'va_read8__body "vvvvvv"). Qed.

Definition va_read4__stmt : Prop := forall m VA slots (i : Z) w a,
  bytes_at asegs m VA (u64s slots) -> nth_error slots (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (VA + 8 * i) ->
  ov_read_bytes asegs m a 4 = Some (le4 w).
Section Sz3.
Variables m VA slots i w a : ltac2:(SecDiet.SzSec.tyM 'va_read4__stmt "vvvvvv" @m).
#[using="Type"] Lemma va_read4__body : ltac2:(SecDiet.SzSec.bodyP 'va_read4__stmt "vvvvvv").
Proof.
  intros Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read asegs m VA (u64s slots) (8 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app. rewrite length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r.
  rewrite firstn4_le8. reflexivity.
Qed.
End Sz3.
Lemma va_read4 : ltac:(let t := eval cbv delta [va_read4__stmt] in va_read4__stmt in exact t).
Proof. intros m VA slots i w a. ltac2:(SecDiet.SzSec.closeP 'va_read4__body "vvvvvv"). Qed.

Lemma va_area_bound : forall m VA slots, va_area m VA slots -> (0 <= VA /\ VA + 8 * Z.of_nat (length slots) <= 2^64)%Z.
Proof. intros m VA slots H. pose proof (bytes_at_bound _ _ _ _ H) as B. rewrite u64s_length in B. lia. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac if_lit :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

Definition pop_arg_spec__stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte)
    (VA : Z) (slots : list word) (i ty : Z) (slot x y : word),
  rw_cells asegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
  va_area m VA slots -> nth_error slots (Z.to_nat i) = Some slot -> (0 <= i)%Z ->
  rw_cells asegs m (bv_unsigned a0) [C8 x; C8 y] ->
  stk asegs m (bv_unsigned sp - 16) (bv_unsigned sp) ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 ty -> (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_SIZET) ->
  (16 <= bv_unsigned sp)%Z ->
  (bv_unsigned sp <= bv_unsigned a2)%Z -> (bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a2 + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= bv_unsigned a2)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= VA)%Z ->
  (VA + 8 * Z.of_nat (length slots) <= bv_unsigned a0 \/ bv_unsigned a0 + 16 <= VA)%Z ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG (bv_unsigned sp - 16) 16 -> rng RNG (bv_unsigned a2) 8 -> rng RNG (bv_unsigned a0) 16 ->
  rng RNG VA (8 * Z.of_nat (length slots)) ->
  evtF asegs RNG (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) (bv_unsigned a2) VA slots i ty slot y m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9c2a4) fc None m (seg_rom asegs)).
Section Sz5.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m VA slots i ty slot x y : ltac2:(SecDiet.SzSec.tyM 'pop_arg_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma pop_arg_spec__body : ltac2:(SecDiet.SzSec.bodyP 'pop_arg_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros APC VAA NTH Hi ARGC ST MI -> TY SPLO A2 A0 SEP1 SEP2 SEP3 SEP4 RIMG RFR RAP RARG RVA.
  pose_word_ranges.
  pose proof (va_area_bound _ _ _ VAA) as VB. unfold va_area in VAA.
  assert (IL : (Z.to_nat i < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
  set (AP := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 AP) by (unfold AP; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (ARG := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 ARG) by (unfold ARG; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (AP, AP + 8); (ARG, ARG + 16)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  destruct TY as [-> | [-> | [-> | ->]]]; unfold T_PTR, T_INT, T_UINT, T_SIZET, pop_arg_lo, pop_arg_hi; cbn [Z.eqb Pos.eqb].
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read4 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
  - (* [comment removed for export] *)
    zstep. zstep. zstep. if_lit. do 7 zstep.
    zstep. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => pose proof (va_read8 mc VA slots i slot _ VAA NTH Hi eq_refl) as RD end.
    zstep. clear RD. zstep. zstep.
    replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in APC by lia.
    finish. { reflexivity. }
Qed.
End Sz5.
Lemma pop_arg_spec : ltac:(let t := eval cbv delta [pop_arg_spec__stmt] in pop_arg_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m VA slots i ty slot x y. ltac2:(SecDiet.SzSec.closeP 'pop_arg_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_pop_arg.
