(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import DrvAgree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow ITreeA SysStepF.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg ABase RtCells F_syscalls.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition AATEXIT : Z := 0x892dc.
Definition AFUNCS_ON_EXIT : Z := 0x89210.
Definition AATX_CALL : Z := 0x893a0.
Definition AAEF_GUARD : Z := 0x80424.
Definition AAEF_INCB : Z := 0x5d4154.
Definition AATX : Z := 0x5f4ae0.
Definition AATX_N : Z := 544.
Definition ALOCK_FN : Z := 0x934d8.
Definition AUNLOCK_FN : Z := 0x93760.
Definition ALIBC : Z := 0x5f4d20.
Definition ACOV_HOOK : Z := 0x6fa5c.
Definition ACOV_FLAG : Z := 0x1339a0.

Definition atx_cells1 (m : amem) : Prop :=
     rw_cells bsegs m AATX [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m (AATX + 4) [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m (AATX + 8) [C4 (Z_to_bv 64 1)]
  /\ rw_cells bsegs m (AATX + 16) [C8 (Z_to_bv 64 (AATX + 24))]
  /\ rw_cells bsegs m (AATX + 24) [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m (AATX + 32) [C8 (Z_to_bv 64 AATX_CALL)]
  /\ rw_cells bsegs m (AATX + 288) [C8 (Z_to_bv 64 ACOV_HOOK)].

Definition atx_cells2 (m : amem) : Prop :=
     rw_cells bsegs m AATX [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m (AATX + 4) [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m (AATX + 8) [C4 (Z_to_bv 64 2)]
  /\ rw_cells bsegs m (AATX + 16) [C8 (Z_to_bv 64 (AATX + 24))]
  /\ rw_cells bsegs m (AATX + 24) [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m (AATX + 32) [C8 (Z_to_bv 64 AATX_CALL)]
  /\ rw_cells bsegs m (AATX + 288) [C8 (Z_to_bv 64 ACOV_HOOK)]
  /\ rw_cells bsegs m (AATX + 40) [C8 (Z_to_bv 64 AATX_CALL)]
  /\ rw_cells bsegs m (AATX + 296) [C8 (Z_to_bv 64 AAEF_GUARD)].

Definition atx_cellsR (m : amem) : Prop := atx_cells2 m /\ rw_cells bsegs m AAEF_INCB [C1 (Z_to_bv 8 0)].

Definition atx_exit (m : amem) : Prop := atx_cells1 m \/ atx_cellsR m.

Definition atx_addr (a : Z) : Prop := (AATX <= a < AATX + AATX_N) \/ (AAEF_INCB <= a < AAEF_INCB + 1).
Definition atx_addrA (a : Z) : Prop := AATX <= a < AATX + AATX_N.

Local Ltac tr AG HP H := eapply rw_cells_magree; [exact AG| exact H| intros a Ha; apply HP; cbn in Ha; lia].
Lemma atx_cells1_agree : forall (P : Z -> Prop) m m', magree bsegs P m m' -> (forall a, atx_addrA a -> P a) -> atx_cells1 m -> atx_cells1 m'.
Proof.
  intros P m m' AG HP H. unfold atx_cells1, atx_addrA, AATX, AATX_N in *. destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|]. split; [tr AG HP A5|]. split; [tr AG HP A6| tr AG HP A7].
Qed.
Lemma atx_cells2_agree : forall (P : Z -> Prop) m m', magree bsegs P m m' -> (forall a, atx_addrA a -> P a) -> atx_cells2 m -> atx_cells2 m'.
Proof.
  intros P m m' AG HP H. unfold atx_cells2, atx_addrA, AATX, AATX_N in *. destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|]. split; [tr AG HP A5|]. split; [tr AG HP A6|].
  split; [tr AG HP A7|]. split; [tr AG HP A8| tr AG HP A9].
Qed.
Lemma atx_cellsR_agree : forall (P : Z -> Prop) m m', magree bsegs P m m' -> (forall a, atx_addr a -> P a) -> atx_cellsR m -> atx_cellsR m'.
Proof.
  intros P m m' AG HP [H C]. split.
  - eapply atx_cells2_agree; [exact AG| | exact H]. intros a Ha. apply HP. left. exact Ha.
  - eapply rw_cells_magree; [exact AG| exact C| intros a Ha; apply HP; right; unfold AAEF_INCB in *; cbn in Ha; lia].
Qed.
Lemma atx_exit_agree : forall (P : Z -> Prop) m m', magree bsegs P m m' -> (forall a, atx_addr a -> P a) -> atx_exit m -> atx_exit m'.
Proof.
  intros P m m' AG HP [H|H].
  - left. eapply atx_cells1_agree; [exact AG| | exact H]. intros a Ha. apply HP. left. exact Ha.
  - right. eapply atx_cellsR_agree; [exact AG| exact HP| exact H].
Qed.
Lemma atx_cells1_munch : forall W m m', munch W m m' -> wmono bsegs m m' -> (forall a, atx_addrA a -> outside W a) -> atx_cells1 m -> atx_cells1 m'.
Proof. intros W m m' MU WM HW. apply (atx_cells1_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma atx_cellsR_munch : forall W m m', munch W m m' -> wmono bsegs m m' -> (forall a, atx_addr a -> outside W a) -> atx_cellsR m -> atx_cellsR m'.
Proof. intros W m m' MU WM HW. apply (atx_cellsR_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma atx_exit_munch : forall W m m', munch W m m' -> wmono bsegs m m' -> (forall a, atx_addr a -> outside W a) -> atx_exit m -> atx_exit m'.
Proof. intros W m m' MU WM HW. apply (atx_exit_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma atx_exit_of_cells1 : forall m, atx_cells1 m -> atx_exit m.  Proof. intros m H; left; exact H. Qed.
Lemma atx_exit_of_cellsR : forall m, atx_cellsR m -> atx_exit m.  Proof. intros m H; right; exact H. Qed.

Definition atx_cells1w (m : amem) : Prop :=
  atx_cells1 m /\ rw_cells bsegs m (AATX + 40) [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs m (AATX + 296) [C8 (Z_to_bv 64 0)].
Lemma atx_cells1w_agree : forall (P : Z -> Prop) m m', magree bsegs P m m' -> (forall a, atx_addrA a -> P a) -> atx_cells1w m -> atx_cells1w m'.
Proof.
  intros P m m' AG HP (H & F1 & A1). split; [exact (atx_cells1_agree P m m' AG HP H)|].
  unfold atx_addrA, AATX, AATX_N in *. split; [tr AG HP F1| tr AG HP A1].
Qed.
Lemma atx_cells1w_1 : forall m, atx_cells1w m -> atx_cells1 m.  Proof. intros m [H _]; exact H. Qed.

Definition atexitA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (AATX, AATX + AATX_N)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ atx_cells2 m'.

Definition atexit_guard_specA_stmt : Prop :=
  forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (cdt thr sec : byte) (tm1 w1 w2 : word),
    stk bsegs m lo (bv_unsigned sp) ->
    atx_cells1 m ->
    rw_cells bsegs m (AATX + 40) [C8 w1] -> rw_cells bsegs m (AATX + 296) [C8 w2] ->
    rw_cells bsegs m ALIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    mem_inv bsegs m ->
    a0 = Z_to_bv 64 AAEF_GUARD ->
    (lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
    evtF bsegs RNG (atexitA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 AATEXIT) fc None m (seg_rom bsegs)).

Definition funcs_on_exitA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (AATX, AATX + 24)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Definition funcs_on_exit_specA_stmt : Prop :=
  forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
    stk bsegs m lo (bv_unsigned sp) ->
    atx_exit m ->
    rw_cells bsegs m ALIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells bsegs m ACOV_FLAG [C1 (Z_to_bv 8 0)] ->
    mem_inv bsegs m ->
    (lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
    evtF bsegs RNG (funcs_on_exitA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 AFUNCS_ON_EXIT) fc None m (seg_rom bsegs)).
End CANSEC1.
