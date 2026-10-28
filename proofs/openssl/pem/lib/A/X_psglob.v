(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small F_memset D_kit X_atexit X_gdefs X_unregi.
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
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (SHW_LO, SHW_HI)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ stk asegs m' SHW_LO SHW_HI.

Lemma psglob_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  a0 = Z_to_bv 64 0x5aaa60 -> a1 = Z_to_bv 64 780800 -> a2 = Z_to_bv 64 0 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> SHW_HI <= lo ->
  ro_cells asegs m 0x5a45a8 [C8 (Z_to_bv 64 0x6fe668); C8 (Z_to_bv 64 0x66a338); C8 (Z_to_bv 64 0x66cb38);
                            C8 (Z_to_bv 64 0x66d828); C8 (Z_to_bv 64 0x66d830); C8 (Z_to_bv 64 0x66d820);
                            C8 (Z_to_bv 64 0x5a77f0)] ->
  ro_cells asegs m 0x5a77f0 [C8 (Z_to_bv 64 0x526914)] ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m 0x6fe6e0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  stk asegs m SHW_LO SHW_HI ->
  mem_inv asegs m ->
  evt asegs (psglob_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c4550) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros -> -> -> ST LO LOLO UG2 RMS SHC THR SC2 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (SHW_LO, SHW_HI)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  xsteps_to 0x1c48ec%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  lazymatch goal with H : stk asegs ?mm SHW_LO SHW_HI |- _ =>
    destruct (stk_window mm SHW_LO SHW_HI 0x800ad54c 0x17d40 H ltac:(lia) ltac:(lia) ltac:(lia)) as (SA & (junk2 & DST) & SB); clear H end.
  call memset_callZ; [exact DST| assumption| lia| lia| lia| lia|].
  lazymatch goal with P : rw_cells asegs ?mm _ [CB _ _] |- _ =>
    pose proof (stk_unwindow mm SHW_LO SHW_HI _ 0x17d40 _ SA P ltac:(reflexivity) SB ltac:(lia) ltac:(lia)) as SC2'; clear SA SB P end.
  unfold psglob_post. sys_finish.
Qed.
