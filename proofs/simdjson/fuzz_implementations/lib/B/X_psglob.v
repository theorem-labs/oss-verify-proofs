(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_small F_memset D_kit X_atexit X_xdefs X_unregi.
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
  a0 = Z_to_bv 64 0x184df0 -> a1 = Z_to_bv 64 5312 -> a2 = Z_to_bv 64 0 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x800d1c58 <= lo ->
  ro_cells bsegs m 0x17feb8 [C8 (Z_to_bv 64 0x21b4a8); C8 (Z_to_bv 64 0x187178); C8 (Z_to_bv 64 0x189978);
                            C8 (Z_to_bv 64 0x18a668); C8 (Z_to_bv 64 0x18a670); C8 (Z_to_bv 64 0x18a660);
                            C8 (Z_to_bv 64 0x181f40)] ->
  ro_cells bsegs m 0x181f40 [C8 (Z_to_bv 64 0x1721b4)] ->
  ro_cells bsegs m 0x189978 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells bsegs m 0x21b520 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  stk bsegs m XS2_LO XS2_HI ->
  mem_inv bsegs m ->
  evt bsegs (psglob_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x875cc) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros -> -> -> ST LO LOLO UG2 RMS SHC THR SC2 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (XS2_LO, XS2_HI)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 64%nat ST.
  xsteps_to 0x87968%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  lazymatch goal with H : stk bsegs ?mm 2147644348 2147650646 |- _ =>
    destruct (stk_window mm 2147644348 2147650646 0x800289be 0x298 H ltac:(lia) ltac:(lia) ltac:(lia)) as (SA & (junk2 & DST) & SB); clear H end.
  call memset_callZ; [exact DST| assumption| lia| lia| lia| lia|].
  lazymatch goal with P : rw_cells bsegs ?mm 2147649982 [CB _ _] |- _ =>
    pose proof (stk_unwindow mm 2147644348 2147650646 _ 0x298 _ SA P ltac:(reflexivity) SB ltac:(lia) ltac:(lia)) as SC2'; clear SA SB P end.
  unfold psglob_post. sys_finish.
Qed.
