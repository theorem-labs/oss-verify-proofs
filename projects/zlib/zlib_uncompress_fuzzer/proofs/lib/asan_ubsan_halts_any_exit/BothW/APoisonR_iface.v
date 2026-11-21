(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode Tac InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg AProto ABase F_apoison.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Export ACanary.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Definition zeros (n : Z) : list byte := repeat (Z_to_bv 8 0) (Z.to_nat n).

Section CANSEC1. Context {rc : runConstT}.
Definition PZR_STACK : Z := 592.

Definition premap_cells (m : amem) : Prop :=
     rw_cells bsegs m 0xd1310 [C8 (Z_to_bv 64 0x1695e0)]
  /\ rw_cells bsegs m 0x1695e0 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m 0x16b6f8 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0x16b740 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1);
                               C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0x16b758 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                               C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
  /\ (exists cb : list byte, rw_cells bsegs m 0x67cd38 [CB 8 cb])
  /\ rw_cells bsegs m 0x67cfb8 [C8 (Z_to_bv 64 4096)].


Lemma bytes_eq_of_unsigned : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.
Lemma premap_word_212a00 : forall m,
  rw_cells bsegs m 0x16b740 [C8 (Z_to_bv 64 0x10101000100)] ->
  rw_cells bsegs m 0x16b740 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1);
                            C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m H. eapply rw_cells_recast; [exact H| cbn; tauto| apply bytes_eq_of_unsigned; vm_compute; reflexivity| reflexivity]. Qed.
Lemma premap_word_212a18 : forall m,
  rw_cells bsegs m 0x16b758 [C8 (Z_to_bv 64 0x101000100000000)] ->
  rw_cells bsegs m 0x16b758 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                            C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
Proof. intros m H. eapply rw_cells_recast; [exact H| cbn; tauto| apply bytes_eq_of_unsigned; vm_compute; reflexivity| reflexivity]. Qed.

Definition premap_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ (fp_bw RNG -> fp_bw RNG')
  /\ munch [(bv_unsigned sp - PZR_STACK, bv_unsigned sp); (shad addr, shad addr + shlen size)] m m' /\ wmono bsegs m m'
  /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' (shad addr) [CB (Z.to_nat (shlen size)) (zeros (shlen size))]
  /\ rng RNG' (shad addr) (shlen size)
  /\ poison_cells m' /\ premap_cells m'.

Definition poison_remap_stmt : Prop :=
  forall (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (addr size lo : Z) (junk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PZR_STACK ->
  mem_inv bsegs m ->
  poison_cells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->
  0x10000 <= shlen size ->
  rw_cells bsegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  (forall RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      premap_post RNG sp addr size lo m RNG' m' ->
      implS bsegs RNG' (aembed ATOP k) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (poison0 addr size k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x5fa38) fc None m (seg_rom bsegs)).
End CANSEC1.
