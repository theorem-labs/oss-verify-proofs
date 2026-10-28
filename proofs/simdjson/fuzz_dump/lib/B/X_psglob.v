(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small F_memset D_kit X_atexit X_xdefs X_unregi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

Definition psglob_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (XS2_LO, XS2_HI)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp) /\ stk bsegs m' XS2_LO XS2_HI.

Lemma psglob_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  a0 = Z_to_bv 64 0x173090 -> a1 = Z_to_bv 64 2496 -> a2 = Z_to_bv 64 0 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x800d0000 <= lo ->
  ro_cells bsegs m 0x16e1c0 [C8 (Z_to_bv 64 0x208c68); C8 (Z_to_bv 64 0x174938); C8 (Z_to_bv 64 0x177138);
                            C8 (Z_to_bv 64 0x177e28); C8 (Z_to_bv 64 0x177e30); C8 (Z_to_bv 64 0x177e20);
                            C8 (Z_to_bv 64 0x1701e0)] ->
  ro_cells bsegs m 0x1701e0 [C8 (Z_to_bv 64 0x160c88)] ->
  ro_cells bsegs m 0x177138 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells bsegs m 0x208ce0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  stk bsegs m XS2_LO XS2_HI ->
  mem_inv bsegs m ->
  evt bsegs (psglob_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8171c) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros -> -> -> ST LO LOLO UG2 RMS SHC THR SC2 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (XS2_LO, XS2_HI)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 64%nat ST.
  xsteps_to 0x81ab8%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  lazymatch goal with H : stk bsegs ?mm 2147635508 0x8002674a |- _ =>
    destruct (stk_window mm 2147635508 0x8002674a 0x80026612 0x138 H ltac:(lia) ltac:(lia) ltac:(lia)) as (SA & (junk2 & DST) & SB); clear H end.
  call memset_callZ; [exact DST| assumption| lia| lia| lia| lia|].
  lazymatch goal with P : rw_cells bsegs ?mm 2147640850 [CB _ _] |- _ =>
    pose proof (stk_unwindow mm 2147635508 0x8002674a _ 0x138 _ SA P ltac:(reflexivity) SB ltac:(lia) ltac:(lia)) as SC2'; clear SA SB P end.
  unfold psglob_post. sys_finish.
Qed.
