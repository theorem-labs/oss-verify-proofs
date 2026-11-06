(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout R_small D_kit X_atexit X_xdefs X_unreg.
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
    /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (0x120490, 0x120491); (0x120440, 0x120448); (0x1213b0, 0x1213b8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x656320, 0x656321); (0x656321, 0x65632b)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Lemma fini_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte) (flag dso : word),
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 304 -> 0x800d0000 <= lo ->
  ro_cells bsegs m 0x117508 [C8 (Z_to_bv 64 0x9e74c); C8 (Z_to_bv 64 0x44700)] ->
  ro_cells bsegs m 0x11bb20 [C8 (Z_to_bv 64 0x117518); C8 (Z_to_bv 64 0x117508)] ->
  ro_cells bsegs m 0x11ad50 [C8 (Z_to_bv 64 0x1027b8); C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x11cb60 [C8 dso] ->
  ro_cells bsegs m 0x11ba60 [C8 (Z_to_bv 64 0x11fb20); C8 (Z_to_bv 64 0x120420)] ->
  rw_cells bsegs m 0x120490 [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x120440 [C8 flag] -> bv_unsigned flag <> 0 ->
  unreg_got m ->
  ro_cells bsegs m 0x121310 [C4 (Z_to_bv 64 1)] ->
  rw_cells bsegs m 0x1213b0 [C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x123af8 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells bsegs m 0x1247d8 [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x12335c [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x1b56a0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells bsegs m 0x11cce8 [C8 (Z_to_bv 64 0x110f9c)] ->
  stk bsegs m XS1_LO XS1_HI -> stk bsegs m XS2_LO XS2_HI -> stk bsegs m XS3_LO XS3_HI ->
  gds_at m 0x11fb20 asan_gds ->
  rw_cells bsegs m 0x656320 [C1 o1] -> rw_cells bsegs m 0x656321 [C1 o2] -> rw_cells bsegs m 0x656322 [C1 o3] -> rw_cells bsegs m 0x656323 [C1 o4] -> rw_cells bsegs m 0x656324 [C1 o5] -> rw_cells bsegs m 0x656325 [C1 o6] -> rw_cells bsegs m 0x656326 [C1 o7] -> rw_cells bsegs m 0x656327 [C1 o8] -> rw_cells bsegs m 0x656328 [C1 o9] -> rw_cells bsegs m 0x656329 [C1 o10] -> rw_cells bsegs m 0x65632a [C1 o11] ->
  mem_inv bsegs m ->
  evt bsegs (fini_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x102888) fc None m (seg_rom bsegs)).
Proof.
  intros until dso. intros ST LO LOLO FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (0x120490, 0x120491); (0x120440, 0x120448); (0x1213b0, 0x1213b8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x656320, 0x656321); (0x656321, 0x65632b)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EU32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (EU64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  carve_frame 32%nat ST.
  steps_to 0x44700%Z.

  carve_frame 16%nat ST.
  steps_to 0x4478c%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.

  steps_to 0x9e74c%Z.
  carve_frame 16%nat ST.
  steps_to 0x54360%Z.
  carve_frame 16%nat ST.
  steps_to 0x53d28%Z.
  match goal with |- evt _ _ (MS _ _ _ _ _ _ _) => idtac end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gds_at mm 0x11fb20 asan_gds)
      by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
          rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call unreg_spec; [reflexivity| reflexivity| rewrite EU64; exact ST| lia| lia| exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP
        | exact THR| exact RMS| exact SC1| exact SC2| exact SC3| exact GDS1| exact O1| exact O2| exact O3| exact O4| exact O5| exact O6| exact O7| exact O8| exact O9| exact O10| exact O11| assumption|].
  rewrite EU64 in POST. rename POST into ST.
  steps_to 0x543a8%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
  steps_to 0x9e778%Z. release_frame FR0 ST (bv_unsigned sp + -32). astep.
  steps_to 0x1028d0%Z. release_frame FR ST (bv_unsigned sp).
  astep. astep.
  unfold fini_post. sys_finish.
Qed.
