(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import SysStep.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import R_small D_kit X_atexit X_xdefs X_unreg.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition fini_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) (RT_iface.frm_clear fc) None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (0x1e14d0, 0x1e14d1); (0x1e1480, 0x1e1488); (0x1e23f0, 0x1e23f8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x7171c2, 0x7171c3); (0x7171c0, 0x7171c2)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (o1 o2 o3 : byte) (flag dso : word),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 304 -> 0x800c0000 <= lo ->
  ro_cells asegs m 0x1c8c60 [C8 (Z_to_bv 64 0xe8080); C8 (Z_to_bv 64 0x90428)] ->
  ro_cells asegs m 0x1d0268 [C8 (Z_to_bv 64 0x1c8c70); C8 (Z_to_bv 64 0x1c8c60)] ->
  ro_cells asegs m 0x1cf3d0 [C8 (Z_to_bv 64 0x1b1e6c); C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x1d12e0 [C8 dso] ->
  ro_cells asegs m 0x1d0090 [C8 (Z_to_bv 64 0x1d4090); C8 (Z_to_bv 64 0x1e1450)] ->
  rw_cells asegs m 0x1e14d0 [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x1e1480 [C8 flag] -> bv_unsigned flag <> 0 ->
  unreg_got m ->
  ro_cells asegs m 0x1e2350 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m 0x1e23f0 [C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x1e4b38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m 0x1e5818 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x1e439c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x2766e0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells asegs m 0x1d1500 [C8 (Z_to_bv 64 0x1c1bfc)] ->
  stk asegs m XS1_LO XS1_HI -> stk asegs m XS2_LO XS2_HI -> stk asegs m XS3_LO XS3_HI ->
  gds_at m 0x1d4090 asan_gds ->
  rw_cells asegs m 0x7171c2 [C1 o1] -> rw_cells asegs m 0x7171c0 [C1 o2] -> rw_cells asegs m 0x7171c1 [C1 o3] ->
  mem_inv asegs m ->
  evt asegs (fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b1f3c) (RT_iface.frm_clear fc) None m (seg_rom asegs)).
Proof.
  intros until dso. intros ST LO LOLO FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS O1 O2 O3 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (0x1e14d0, 0x1e14d1); (0x1e1480, 0x1e1488); (0x1e23f0, 0x1e23f8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x7171c2, 0x7171c3); (0x7171c0, 0x7171c2)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EU32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (EU64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  steps_to 0x90428%Z.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  steps_to 0x904b8%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  (* [comment removed for export] *)
  steps_to 0xe8080%Z.
  carve_frame 16%nat ST.
  steps_to 0xa0570%Z.
  carve_frame 16%nat ST.
  steps_to 0x9ff38%Z.
  match goal with |- evt _ _ (MS _ _ _ _ _ _ _) => idtac end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gds_at mm 0x1d4090 asan_gds)
      by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
          rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call unreg_spec; [reflexivity| reflexivity| rewrite EU64; exact ST| lia| lia| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP
        | exact THR| exact RMS| exact SC1| exact SC2| exact SC3| exact GDS1| exact O1| exact O2| exact O3| assumption|].
  rewrite EU64 in POST. rename POST into ST.
  steps_to 0xa05b8%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
  steps_to 0xe80ac%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  steps_to 0x1b1f84%Z. release_frame FR ST (bv_unsigned sp).
  astep. astep.
  unfold fini_post. sys_finish.
Qed.
