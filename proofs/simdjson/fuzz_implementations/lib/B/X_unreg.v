(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_small F_memset D_kit X_atexit X_xdefs X_unregi X_unregl X_psglob.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

Definition unreg_got (m : mem) : Prop :=
  ro_cells bsegs m 0x17fea8 [C8 (Z_to_bv 64 0x219420)]
  /\ ro_cells bsegs m 0x17feb8 [C8 (Z_to_bv 64 0x21b4a8); C8 (Z_to_bv 64 0x187178); C8 (Z_to_bv 64 0x189978);
                               C8 (Z_to_bv 64 0x18a668); C8 (Z_to_bv 64 0x18a670); C8 (Z_to_bv 64 0x18a660);
                               C8 (Z_to_bv 64 0x181f40)].

Definition unreg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (0x187230, 0x187238);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x6bc240, 0x6bc241); (0x6bc241, 0x6bc24b)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Lemma unreg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte),
  a0 = Z_to_bv 64 0x184df0 -> a1 = Z_to_bv 64 83 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> 0x800d1c58 <= lo ->
  unreg_got m ->
  ro_cells bsegs m 0x187190 [C4 (Z_to_bv 64 1)] ->
  rw_cells bsegs m 0x187230 [C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x189978 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells bsegs m 0x18a658 [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x1891dc [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x21b520 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells bsegs m 0x181f40 [C8 (Z_to_bv 64 0x1721b4)] ->
  stk bsegs m XS1_LO XS1_HI -> stk bsegs m XS2_LO XS2_HI -> stk bsegs m XS3_LO XS3_HI ->
  gds_at m 0x184df0 asan_gds ->
  rw_cells bsegs m 0x6bc240 [C1 o1] -> rw_cells bsegs m 0x6bc241 [C1 o2] -> rw_cells bsegs m 0x6bc242 [C1 o3] -> rw_cells bsegs m 0x6bc243 [C1 o4] -> rw_cells bsegs m 0x6bc244 [C1 o5] -> rw_cells bsegs m 0x6bc245 [C1 o6] -> rw_cells bsegs m 0x6bc246 [C1 o7] -> rw_cells bsegs m 0x6bc247 [C1 o8] -> rw_cells bsegs m 0x6bc248 [C1 o9] -> rw_cells bsegs m 0x6bc249 [C1 o10] -> rw_cells bsegs m 0x6bc24a [C1 o11] ->
  mem_inv bsegs m ->
  evt bsegs (unreg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6d770) fc None m (seg_rom bsegs)).
Proof.
  intros until o11. intros -> -> ST LO LOLO (G1 & G2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0x187230, 0x187238);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x6bc240, 0x6bc241); (0x6bc241, 0x6bc24b)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 176%nat ST.
  xsteps_to 0x6d818%Z.
  amo_step. showpc. xstep. showpc. amo_step. showpc. xstep. showpc. xstep. showpc.
  xsteps_to 0x6d92c%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gds_at mm 0x184df0 asan_gds)
      by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
          rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call (unreg_loop asan_gds 83); [exact asan_gds_ok| reflexivity| lia| exact GDS1| exact AI| exact CP| exact RG| exact SHC| exact THR
        | exact RMS| exact SC1| exact SC2| exact SC3| exact O1| exact O2| exact O3| exact O4| exact O5| exact O6| exact O7| exact O8| exact O9| exact O10| exact O11| assumption|].
  xsteps_to 0x875cc%Z.
  assert (EU176 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176) by (apply unsigned_lit; lia).
  lazymatch goal with H : stk bsegs ?mm 2147644348 2147650646 |- _ => rename H into SCX2 end.
  call psglob_spec; [reflexivity| reflexivity| reflexivity| rewrite EU176; exact ST| lia| lia| exact G2| exact RMS| exact SHC| exact THR
        | exact SCX2| assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176))) |- _ => rewrite EU176 in H; rename H into ST end.
  xsteps_to 0x6db88%Z.
  amo_step. xstep. amo_step. xstep. xstep. xstep.
  xsteps_to 0x6dc3c%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  unfold unreg_post. sys_finish.
Qed.
