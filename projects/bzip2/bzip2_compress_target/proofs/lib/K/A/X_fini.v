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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout R_small D_kit X_atexit X_xdefs X_unreg.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_atexit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_xdefs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_unreg.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition fini_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (0xd2ed0, 0xd2ed1); (0xd2e80, 0xd2e88); (0xd3df0, 0xd3df8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x608bc0, 0x608bc1); (0x608bc1, 0x608bc3)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Lemma fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (o1 o2 o3 : byte) (flag dso : word),
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 304 -> 0x800c0000 <= lo ->
  ro_cells bsegs m 0xcc8c0 [C8 (Z_to_bv 64 0x81638); C8 (Z_to_bv 64 0x31788)] ->
  ro_cells bsegs m 0xcdb00 [C8 (Z_to_bv 64 0xcc8d0); C8 (Z_to_bv 64 0xcc8c0)] ->
  ro_cells bsegs m 0xcce08 [C8 (Z_to_bv 64 0xbc610); C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0xceb40 [C8 dso] ->
  ro_cells bsegs m 0xcdac0 [C8 (Z_to_bv 64 0xd2660); C8 (Z_to_bv 64 0xd2e60)] ->
  rw_cells bsegs m 0xd2ed0 [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0xd2e80 [C8 flag] -> bv_unsigned flag <> 0 ->
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
  evt bsegs (fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xbc6e0) fc None m (seg_rom bsegs)).
Proof.
  intros until dso. intros ST LO LOLO FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS O1 O2 O3 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (0xd2ed0, 0xd2ed1); (0xd2e80, 0xd2e88); (0xd3df0, 0xd3df8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x608bc0, 0x608bc1); (0x608bc1, 0x608bc3)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EU32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (EU64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  steps_to 0x31788%Z.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  steps_to 0x31814%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  (* [comment removed for export] *)
  steps_to 0x81638%Z.
  carve_frame 16%nat ST.
  steps_to 0x411c8%Z.
  carve_frame 16%nat ST.
  steps_to 0x40b90%Z.
  match goal with |- evt _ _ (MS _ _ _ _ _ _ _) => idtac end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gds_at mm 0xd2660 asan_gds)
      by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
          rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call unreg_spec; [reflexivity| reflexivity| rewrite EU64; exact ST| lia| lia| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP
        | exact THR| exact RMS| exact SC1| exact SC2| exact SC3| exact GDS1| exact O1| exact O2| exact O3| assumption|].
  rewrite EU64 in POST. rename POST into ST.
  steps_to 0x41210%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
  steps_to 0x81664%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  steps_to 0xbc728%Z. release_frame FR ST (bv_unsigned sp).
  astep. astep.
  unfold fini_post. sys_finish.
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow R_small D_kit X_atexit X_xdefs X_unreg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition fini_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (0xc5ad0, 0xc5ad1); (0xc5a80, 0xc5a88); (0xc69f0, 0xc69f8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x5fb7c0, 0x5fb7c1); (0x5fb7c1, 0x5fb7c3)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (o1 o2 o3 : byte) (flag dso : word),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 304 -> 0x800c0000 <= lo ->
  ro_cells asegs m 0xbf4e0 [C8 (Z_to_bv 64 0x81bf4); C8 (Z_to_bv 64 0x318a0)] ->
  ro_cells asegs m 0xc0720 [C8 (Z_to_bv 64 0xbf4f0); C8 (Z_to_bv 64 0xbf4e0)] ->
  ro_cells asegs m 0xbfa28 [C8 (Z_to_bv 64 0xaf230); C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0xc1760 [C8 dso] ->
  ro_cells asegs m 0xc06e0 [C8 (Z_to_bv 64 0xc5220); C8 (Z_to_bv 64 0xc5a60)] ->
  rw_cells asegs m 0xc5ad0 [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xc5a80 [C8 flag] -> bv_unsigned flag <> 0 ->
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
  evt asegs (fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xaf300) fc None m (seg_rom asegs)).
Proof.
  intros until dso. intros ST LO LOLO FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS O1 O2 O3 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (0xc5ad0, 0xc5ad1); (0xc5a80, 0xc5a88); (0xc69f0, 0xc69f8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x5fb7c0, 0x5fb7c1); (0x5fb7c1, 0x5fb7c3)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EU32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (EU64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  steps_to 0x318a0%Z.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  steps_to 0x3192c%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  (* [comment removed for export] *)
  steps_to 0x81bf4%Z.
  carve_frame 16%nat ST.
  steps_to 0x412e0%Z.
  carve_frame 16%nat ST.
  steps_to 0x40ca8%Z.
  match goal with |- evt _ _ (MS _ _ _ _ _ _ _) => idtac end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gds_at mm 0xc5220 asan_gds)
      by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
          rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call unreg_spec; [reflexivity| reflexivity| rewrite EU64; exact ST| lia| lia| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP
        | exact THR| exact RMS| exact SC1| exact SC2| exact SC3| exact GDS1| exact O1| exact O2| exact O3| assumption|].
  rewrite EU64 in POST. rename POST into ST.
  steps_to 0x41328%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
  steps_to 0x81c20%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  steps_to 0xaf348%Z. release_frame FR ST (bv_unsigned sp).
  astep. astep.
  unfold fini_post. sys_finish.
Qed.
