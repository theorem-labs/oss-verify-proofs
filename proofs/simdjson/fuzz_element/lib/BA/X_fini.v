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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import X_atexit X_xdefs X_unreg.
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
    /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (0x1705d0, 0x1705d1); (0x170580, 0x170588); (0x1714f0, 0x1714f8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x6a6460, 0x6a6461); (0x6a6461, 0x6a646b)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte) (flag dso : word),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 304 -> 0x800ce1f8 <= lo ->
  ro_cells asegs m 0x164170 [C8 (Z_to_bv 64 0xb9304); C8 (Z_to_bv 64 0x5a4e0)] ->
  ro_cells asegs m 0x16b008 [C8 (Z_to_bv 64 0x164180); C8 (Z_to_bv 64 0x164170)] ->
  ro_cells asegs m 0x16a200 [C8 (Z_to_bv 64 0x14b2b8); C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x16c048 [C8 dso] ->
  ro_cells asegs m 0x16af20 [C8 (Z_to_bv 64 0x16ed30); C8 (Z_to_bv 64 0x170570)] ->
  rw_cells asegs m 0x1705d0 [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x170580 [C8 flag] -> bv_unsigned flag <> 0 ->
  unreg_got m ->
  ro_cells asegs m 0x171450 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m 0x1714f0 [C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x173c38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m 0x174918 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x17349c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x2057e0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells asegs m 0x16c250 [C8 (Z_to_bv 64 0x15c928)] ->
  stk asegs m XS1_LO XS1_HI -> stk asegs m XS2_LO XS2_HI -> stk asegs m XS3_LO XS3_HI ->
  gds_at m 0x16ed30 asan_gds ->
  rw_cells asegs m 0x6a6460 [C1 o1] -> rw_cells asegs m 0x6a6461 [C1 o2] -> rw_cells asegs m 0x6a6462 [C1 o3] -> rw_cells asegs m 0x6a6463 [C1 o4] -> rw_cells asegs m 0x6a6464 [C1 o5] -> rw_cells asegs m 0x6a6465 [C1 o6] -> rw_cells asegs m 0x6a6466 [C1 o7] -> rw_cells asegs m 0x6a6467 [C1 o8] -> rw_cells asegs m 0x6a6468 [C1 o9] -> rw_cells asegs m 0x6a6469 [C1 o10] -> rw_cells asegs m 0x6a646a [C1 o11] ->
  mem_inv asegs m ->
  evt asegs (fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14b450) fc None m (seg_rom asegs)).
Proof.
  intros until dso. intros ST LO LOLO FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (0x1705d0, 0x1705d1); (0x170580, 0x170588); (0x1714f0, 0x1714f8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x6a6460, 0x6a6461); (0x6a6461, 0x6a646b)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EU32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (EU64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  steps_to 0x5a4e0%Z.

  carve_frame 16%nat ST.
  steps_to 0x5a56c%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.

  steps_to 0xb9304%Z.
  carve_frame 16%nat ST.
  steps_to 0x6a3b8%Z.
  carve_frame 16%nat ST.
  steps_to 0x69d80%Z.
  match goal with |- evt _ _ (MS _ _ _ _ _ _ _) => idtac end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gds_at mm 0x16ed30 asan_gds)
      by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
          rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call unreg_spec; [reflexivity| reflexivity| rewrite EU64; exact ST| lia| lia| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP
        | exact THR| exact RMS| exact SC1| exact SC2| exact SC3| exact GDS1| exact O1| exact O2| exact O3| exact O4| exact O5| exact O6| exact O7| exact O8| exact O9| exact O10| exact O11| assumption|].
  rewrite EU64 in POST. rename POST into ST.
  steps_to 0x6a400%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
  steps_to 0xb9330%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  steps_to 0x14b498%Z. release_frame FR ST (bv_unsigned sp).
  astep. astep.
  unfold fini_post. sys_finish.
Qed.
