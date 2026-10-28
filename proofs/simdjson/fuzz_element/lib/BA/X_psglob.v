(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_memset. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import X_atexit X_xdefs X_unregi.
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
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (XS2_LO, XS2_HI)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ stk asegs m' XS2_LO XS2_HI.

Lemma psglob_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  a0 = Z_to_bv 64 0x16ed30 -> a1 = Z_to_bv 64 6208 -> a2 = Z_to_bv 64 0 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x800ce1f8 <= lo ->
  ro_cells asegs m 0x16a220 [C8 (Z_to_bv 64 0x205768); C8 (Z_to_bv 64 0x171438); C8 (Z_to_bv 64 0x173c38);
                            C8 (Z_to_bv 64 0x174928); C8 (Z_to_bv 64 0x174930); C8 (Z_to_bv 64 0x174920);
                            C8 (Z_to_bv 64 0x16c250)] ->
  ro_cells asegs m 0x16c250 [C8 (Z_to_bv 64 0x15c928)] ->
  ro_cells asegs m 0x173c38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m 0x2057e0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  stk asegs m XS2_LO XS2_HI ->
  mem_inv asegs m ->
  evt asegs (psglob_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x8419c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros -> -> -> ST LO LOLO UG2 RMS SHC THR SC2 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (XS2_LO, XS2_HI)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  xsteps_to 0x84538%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  lazymatch goal with H : stk asegs ?mm 2147633388 2147647154 |- _ =>
    destruct (stk_window mm 2147633388 2147647154 0x80025da6 0x308 H ltac:(lia) ltac:(lia) ltac:(lia)) as (SA & (junk2 & DST) & SB); clear H end.
  call memset_callZ; [exact DST| assumption| lia| lia| lia| lia|].
  lazymatch goal with P : rw_cells asegs ?mm 2147638694 [CB _ _] |- _ =>
    pose proof (stk_unwindow mm 2147633388 2147647154 _ 0x308 _ SA P ltac:(reflexivity) SB ltac:(lia) ltac:(lia)) as SC2'; clear SA SB P end.
  unfold psglob_post. sys_finish.
Qed.
