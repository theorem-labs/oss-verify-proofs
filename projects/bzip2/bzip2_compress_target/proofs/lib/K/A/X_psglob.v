(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small F_memset D_kit X_atexit X_xdefs X_unregi.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_memset.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_atexit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_xdefs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_unregi.TwinB__.
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
  a0 = Z_to_bv 64 0xd2660 -> a1 = Z_to_bv 64 2048 -> a2 = Z_to_bv 64 0 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x800c0000 <= lo ->
  ro_cells bsegs m 0xcce28 [C8 (Z_to_bv 64 0x168068); C8 (Z_to_bv 64 0xd3d38); C8 (Z_to_bv 64 0xd6538);
                            C8 (Z_to_bv 64 0xd7228); C8 (Z_to_bv 64 0xd7230); C8 (Z_to_bv 64 0xd7220);
                            C8 (Z_to_bv 64 0xcecb0)] ->
  ro_cells bsegs m 0xcecb0 [C8 (Z_to_bv 64 0xc6568)] ->
  ro_cells bsegs m 0xd6538 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells bsegs m 0x1680e0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  stk bsegs m XS2_LO XS2_HI ->
  mem_inv bsegs m ->
  evt bsegs (psglob_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x54644) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros -> -> -> ST LO LOLO UG2 RMS SHC THR SC2 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (XS2_LO, XS2_HI)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 64%nat ST.
  xsteps_to 0x549e0%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  lazymatch goal with H : stk bsegs ?mm 2147558012 2147558860 |- _ =>
    destruct (stk_window mm 2147558012 2147558860 0x800124cc 0x100 H ltac:(lia) ltac:(lia) ltac:(lia)) as (SA & (junk2 & DST) & SB); clear H end.
  call memset_callZ; [exact DST| assumption| lia| lia| lia| lia|].
  lazymatch goal with P : rw_cells bsegs ?mm 2147558604 [CB _ _] |- _ =>
    pose proof (stk_unwindow mm 2147558012 2147558860 _ 0x100 _ SA P ltac:(reflexivity) SB ltac:(lia) ltac:(lia)) as SC2'; clear SA SB P end.
  unfold psglob_post. sys_finish.
Qed.
End TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_small F_memset D_kit X_atexit X_xdefs X_unregi.
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
  a0 = Z_to_bv 64 0xc5220 -> a1 = Z_to_bv 64 2112 -> a2 = Z_to_bv 64 0 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x800c0000 <= lo ->
  ro_cells asegs m 0xbfa48 [C8 (Z_to_bv 64 0x15ac68); C8 (Z_to_bv 64 0xc6938); C8 (Z_to_bv 64 0xc9138);
                            C8 (Z_to_bv 64 0xc9e28); C8 (Z_to_bv 64 0xc9e30); C8 (Z_to_bv 64 0xc9e20);
                            C8 (Z_to_bv 64 0xc18d0)] ->
  ro_cells asegs m 0xc18d0 [C8 (Z_to_bv 64 0xb9188)] ->
  ro_cells asegs m 0xc9138 [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m 0x15ace0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  stk asegs m XS2_LO XS2_HI ->
  mem_inv asegs m ->
  evt asegs (psglob_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x54bf8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros -> -> -> ST LO LOLO UG2 RMS SHC THR SC2 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (XS2_LO, XS2_HI)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  xsteps_to 0x54f94%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  lazymatch goal with H : stk asegs ?mm 2147551232 2147552076 |- _ =>
    destruct (stk_window mm 2147551232 2147552076 0x80010a44 0x108 H ltac:(lia) ltac:(lia) ltac:(lia)) as (SA & (junk2 & DST) & SB); clear H end.
  call memset_callZ; [exact DST| assumption| lia| lia| lia| lia|].
  lazymatch goal with P : rw_cells asegs ?mm 2147551812 [CB _ _] |- _ =>
    pose proof (stk_unwindow mm 2147551232 2147552076 _ 0x108 _ SA P ltac:(reflexivity) SB ltac:(lia) ltac:(lia)) as SC2'; clear SA SB P end.
  unfold psglob_post. sys_finish.
Qed.
