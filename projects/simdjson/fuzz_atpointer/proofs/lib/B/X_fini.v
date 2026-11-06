(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac ImageA Z119.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Z10m.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zot D_kit Z11l Z11v Z11s.
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
    /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (0x11d250, 0x11d251); (0x11d200, 0x11d208); (0x11e170, 0x11e178);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x6530e0, 0x6530e1); (0x6530e1, 0x6530ea)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Lemma fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 : byte) (flag dso : word),
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 304 -> 0x800d0000 <= lo ->
  ro_cells bsegs m 0x1142d8 [C8 (Z_to_bv 64 0x9b158); C8 (Z_to_bv 64 0x44880)] ->
  ro_cells bsegs m 0x1188e0 [C8 (Z_to_bv 64 0x1142e8); C8 (Z_to_bv 64 0x1142d8)] ->
  ro_cells bsegs m 0x117b30 [C8 (Z_to_bv 64 0xff588); C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x119920 [C8 dso] ->
  ro_cells bsegs m 0x118820 [C8 (Z_to_bv 64 0x11c8e0); C8 (Z_to_bv 64 0x11d1e0)] ->
  rw_cells bsegs m 0x11d250 [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x11d200 [C8 flag] -> bv_unsigned flag <> 0 ->
  unreg_got m ->
  ro_cells bsegs m 0x11e0d0 [C4 (Z_to_bv 64 1)] ->
  rw_cells bsegs m 0x11e170 [C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x1208b8 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells bsegs m 0x121598 [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x12011c [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x1b2460 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells bsegs m 0x119aa8 [C8 (Z_to_bv 64 0x10dd6c)] ->
  stk bsegs m XS1_LO XS1_HI -> stk bsegs m XS2_LO XS2_HI -> stk bsegs m XS3_LO XS3_HI ->
  gds_at m 0x11c8e0 asan_gds ->
  rw_cells bsegs m 0x6530e0 [C1 o1] -> rw_cells bsegs m 0x6530e1 [C1 o2] -> rw_cells bsegs m 0x6530e2 [C1 o3] -> rw_cells bsegs m 0x6530e3 [C1 o4] -> rw_cells bsegs m 0x6530e4 [C1 o5] -> rw_cells bsegs m 0x6530e5 [C1 o6] -> rw_cells bsegs m 0x6530e6 [C1 o7] -> rw_cells bsegs m 0x6530e7 [C1 o8] -> rw_cells bsegs m 0x6530e8 [C1 o9] -> rw_cells bsegs m 0x6530e9 [C1 o10] ->
  mem_inv bsegs m ->
  evt bsegs (fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xff658) fc None m (seg_rom bsegs)).
Proof.
  intros until dso. intros ST LO LOLO FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (0x11d250, 0x11d251); (0x11d200, 0x11d208); (0x11e170, 0x11e178);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x6530e0, 0x6530e1); (0x6530e1, 0x6530ea)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EU32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (EU64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  steps_to 0x44880%Z.

  carve_frame 16%nat ST.
  steps_to 0x4490c%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.

  steps_to 0x9b158%Z.
  carve_frame 16%nat ST.
  steps_to 0x544d0%Z.
  carve_frame 16%nat ST.
  steps_to 0x53e98%Z.
  match goal with |- evt _ _ (MS _ _ _ _ _ _ _) => idtac end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gds_at mm 0x11c8e0 asan_gds)
      by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
          rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call unreg_spec; [reflexivity| reflexivity| rewrite EU64; exact ST| lia| lia| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP
        | exact THR| exact RMS| exact SC1| exact SC2| exact SC3| exact GDS1| exact O1| exact O2| exact O3| exact O4| exact O5| exact O6| exact O7| exact O8| exact O9| exact O10| assumption|].
  rewrite EU64 in POST. rename POST into ST.
  steps_to 0x54518%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
  steps_to 0x9b184%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  steps_to 0xff6a0%Z. release_frame FR ST (bv_unsigned sp).
  astep. astep.
  unfold fini_post. sys_finish.
Qed.
