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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small F_memset D_kit X_atexit X_xdefs X_unregi X_unregl X_psglob.
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
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_memset.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_atexit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_xdefs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_unregi.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_unregl.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_psglob.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

(* [comment removed for export] *)
Definition unreg_got (m : mem) : Prop :=
  ro_cells bsegs m 0xcce18 [C8 (Z_to_bv 64 0x165fe0)]
  /\ ro_cells bsegs m 0xcce28 [C8 (Z_to_bv 64 0x168068); C8 (Z_to_bv 64 0xd3d38); C8 (Z_to_bv 64 0xd6538);
                               C8 (Z_to_bv 64 0xd7228); C8 (Z_to_bv 64 0xd7230); C8 (Z_to_bv 64 0xd7220);
                               C8 (Z_to_bv 64 0xcecb0)].

Definition unreg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (0xd3df0, 0xd3df8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x608bc0, 0x608bc1); (0x608bc1, 0x608bc3)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Lemma unreg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (o1 o2 o3 : byte),
  a0 = Z_to_bv 64 0xd2660 -> a1 = Z_to_bv 64 32 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> 0x800c0000 <= lo ->
  unreg_got m ->
  ro_cells bsegs m 0xd3d50 [C4 (Z_to_bv 64 1)] ->
  rw_cells bsegs m 0xd3df0 [C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0xd6538 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells bsegs m 0xd7218 [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0xd5d9c [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x1680e0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells bsegs m 0xcecb0 [C8 (Z_to_bv 64 0xc6568)] ->
  stk bsegs m XS1_LO XS1_HI -> stk bsegs m XS2_LO XS2_HI -> stk bsegs m XS3_LO XS3_HI ->
  gds_at m 0xd2660 asan_gds ->
  rw_cells bsegs m 0x608bc0 [C1 o1] -> rw_cells bsegs m 0x608bc1 [C1 o2] -> rw_cells bsegs m 0x608bc2 [C1 o3] ->
  mem_inv bsegs m ->
  evt bsegs (unreg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x40b90) fc None m (seg_rom bsegs)).
Proof.
  intros until o3. intros -> -> ST LO LOLO (G1 & G2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS O1 O2 O3 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0xd3df0, 0xd3df8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x608bc0, 0x608bc1); (0x608bc1, 0x608bc3)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 176%nat ST.
  xsteps_to 0x40c38%Z.
  amo_step. showpc. xstep. showpc. amo_step. showpc. xstep. showpc. xstep. showpc.
  xsteps_to 0x40d4c%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gds_at mm 0xd2660 asan_gds)
      by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
          rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call (unreg_loop asan_gds 32); [exact asan_gds_ok| reflexivity| lia| exact GDS1| exact AI| exact CP| exact RG| exact SHC| exact THR
        | exact RMS| exact SC1| exact SC2| exact SC3| exact O1| exact O2| exact O3| assumption|].
  xsteps_to 0x54644%Z.
  assert (EU176 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176) by (apply unsigned_lit; lia).
  lazymatch goal with H : stk bsegs ?mm 2147558012 2147558860 |- _ => rename H into SCX2 end.
  call psglob_spec; [reflexivity| reflexivity| reflexivity| rewrite EU176; exact ST| lia| lia| exact G2| exact RMS| exact SHC| exact THR
        | exact SCX2| assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176))) |- _ => rewrite EU176 in H; rename H into ST end.
  xsteps_to 0x40fa8%Z.
  amo_step. xstep. amo_step. xstep. xstep. xstep.
  xsteps_to 0x4105c%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  unfold unreg_post. sys_finish.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_small F_memset D_kit X_atexit X_xdefs X_unregi X_unregl X_psglob.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

(* [comment removed for export] *)
Definition unreg_got (m : mem) : Prop :=
  ro_cells asegs m 0xbfa38 [C8 (Z_to_bv 64 0x158be0)]
  /\ ro_cells asegs m 0xbfa48 [C8 (Z_to_bv 64 0x15ac68); C8 (Z_to_bv 64 0xc6938); C8 (Z_to_bv 64 0xc9138);
                               C8 (Z_to_bv 64 0xc9e28); C8 (Z_to_bv 64 0xc9e30); C8 (Z_to_bv 64 0xc9e20);
                               C8 (Z_to_bv 64 0xc18d0)].

Definition unreg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (0xc69f0, 0xc69f8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x5fb7c0, 0x5fb7c1); (0x5fb7c1, 0x5fb7c3)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma unreg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (o1 o2 o3 : byte),
  a0 = Z_to_bv 64 0xc5220 -> a1 = Z_to_bv 64 33 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> 0x800c0000 <= lo ->
  unreg_got m ->
  ro_cells asegs m 0xc6950 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m 0xc69f0 [C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0xc9138 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m 0xc9e18 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0xc899c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x15ace0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells asegs m 0xc18d0 [C8 (Z_to_bv 64 0xb9188)] ->
  stk asegs m XS1_LO XS1_HI -> stk asegs m XS2_LO XS2_HI -> stk asegs m XS3_LO XS3_HI ->
  gds_at m 0xc5220 asan_gds ->
  rw_cells asegs m 0x5fb7c0 [C1 o1] -> rw_cells asegs m 0x5fb7c1 [C1 o2] -> rw_cells asegs m 0x5fb7c2 [C1 o3] ->
  mem_inv asegs m ->
  evt asegs (unreg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x40ca8) fc None m (seg_rom asegs)).
Proof.
  intros until o3. intros -> -> ST LO LOLO (G1 & G2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS O1 O2 O3 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0xc69f0, 0xc69f8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x5fb7c0, 0x5fb7c1); (0x5fb7c1, 0x5fb7c3)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 176%nat ST.
  xsteps_to 0x40d50%Z.
  amo_step. showpc. xstep. showpc. amo_step. showpc. xstep. showpc. xstep. showpc.
  xsteps_to 0x40e64%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gds_at mm 0xc5220 asan_gds)
      by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
          rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call (unreg_loop asan_gds 33); [exact asan_gds_ok| reflexivity| lia| exact GDS1| exact AI| exact CP| exact RG| exact SHC| exact THR
        | exact RMS| exact SC1| exact SC2| exact SC3| exact O1| exact O2| exact O3| assumption|].
  xsteps_to 0x54bf8%Z.
  assert (EU176 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176) by (apply unsigned_lit; lia).
  lazymatch goal with H : stk asegs ?mm 2147551232 2147552076 |- _ => rename H into SCX2 end.
  call psglob_spec; [reflexivity| reflexivity| reflexivity| rewrite EU176; exact ST| lia| lia| exact G2| exact RMS| exact SHC| exact THR
        | exact SCX2| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176))) |- _ => rewrite EU176 in H; rename H into ST end.
  xsteps_to 0x410c0%Z.
  amo_step. xstep. amo_step. xstep. xstep. xstep.
  xsteps_to 0x41174%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  unfold unreg_post. sys_finish.
Qed.
