(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.B Require Import Layout R_small D_kit X_atexit X_xdefs X_unreg.
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
    /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (0x17c7d0, 0x17c7d1); (0x17c780, 0x17c788); (0x17d6f0, 0x17d6f8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x6b2660, 0x6b2661); (0x6b2661, 0x6b266a)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Lemma fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 : byte) (flag dso : word),
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 304 -> 0x800d0000 <= lo ->
  ro_cells bsegs m 0x171180 [C8 (Z_to_bv 64 0xba438); C8 (Z_to_bv 64 0x5af9c)] ->
  ro_cells bsegs m 0x177d10 [C8 (Z_to_bv 64 0x171190); C8 (Z_to_bv 64 0x171180)] ->
  ro_cells bsegs m 0x176f20 [C8 (Z_to_bv 64 0x158304); C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x178d60 [C8 dso] ->
  ro_cells bsegs m 0x177c18 [C8 (Z_to_bv 64 0x17be10); C8 (Z_to_bv 64 0x17c750)] ->
  rw_cells bsegs m 0x17c7d0 [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x17c780 [C8 flag] -> bv_unsigned flag <> 0 ->
  unreg_got m ->
  ro_cells bsegs m 0x17d650 [C4 (Z_to_bv 64 1)] ->
  rw_cells bsegs m 0x17d6f0 [C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x17fe38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells bsegs m 0x180b18 [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x17f69c [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x2119e0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells bsegs m 0x178f60 [C8 (Z_to_bv 64 0x169974)] ->
  stk bsegs m XS1_LO XS1_HI -> stk bsegs m XS2_LO XS2_HI -> stk bsegs m XS3_LO XS3_HI ->
  gds_at m 0x17be10 asan_gds ->
  rw_cells bsegs m 0x6b2660 [C1 o1] -> rw_cells bsegs m 0x6b2661 [C1 o2] -> rw_cells bsegs m 0x6b2662 [C1 o3] -> rw_cells bsegs m 0x6b2663 [C1 o4] -> rw_cells bsegs m 0x6b2664 [C1 o5] -> rw_cells bsegs m 0x6b2665 [C1 o6] -> rw_cells bsegs m 0x6b2666 [C1 o7] -> rw_cells bsegs m 0x6b2667 [C1 o8] -> rw_cells bsegs m 0x6b2668 [C1 o9] -> rw_cells bsegs m 0x6b2669 [C1 o10] ->
  mem_inv bsegs m ->
  evt bsegs (fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15849c) fc None m (seg_rom bsegs)).
Proof.
  intros until dso. intros ST LO LOLO FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (0x17c7d0, 0x17c7d1); (0x17c780, 0x17c788); (0x17d6f0, 0x17d6f8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x6b2660, 0x6b2661); (0x6b2661, 0x6b266a)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EU32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (EU64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  steps_to 0x5af9c%Z.

  carve_frame 16%nat ST.
  steps_to 0x5b028%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.

  steps_to 0xba438%Z.
  carve_frame 16%nat ST.
  steps_to 0x6aeac%Z.
  carve_frame 16%nat ST.
  steps_to 0x6a874%Z.
  match goal with |- evt _ _ (MS _ _ _ _ _ _ _) => idtac end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gds_at mm 0x17be10 asan_gds)
      by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
          rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call unreg_spec; [reflexivity| reflexivity| rewrite EU64; exact ST| lia| lia| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP
        | exact THR| exact RMS| exact SC1| exact SC2| exact SC3| exact GDS1| exact O1| exact O2| exact O3| exact O4| exact O5| exact O6| exact O7| exact O8| exact O9| exact O10| assumption|].
  rewrite EU64 in POST. rename POST into ST.
  steps_to 0x6aef4%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
  steps_to 0xba464%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  steps_to 0x1584e4%Z. release_frame FR ST (bv_unsigned sp).
  astep. astep.
  unfold fini_post. sys_finish.
Qed.
