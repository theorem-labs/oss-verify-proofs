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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_memset. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import X_atexit X_xdefs X_unregi X_unregl X_psglob.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

Definition unreg_got (m : mem) : Prop :=
  ro_cells asegs m 0x16a210 [C8 (Z_to_bv 64 0x2036e0)]
  /\ ro_cells asegs m 0x16a220 [C8 (Z_to_bv 64 0x205768); C8 (Z_to_bv 64 0x171438); C8 (Z_to_bv 64 0x173c38);
                               C8 (Z_to_bv 64 0x174928); C8 (Z_to_bv 64 0x174930); C8 (Z_to_bv 64 0x174920);
                               C8 (Z_to_bv 64 0x16c250)].

Definition unreg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (0x1714f0, 0x1714f8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x6a6460, 0x6a6461); (0x6a6461, 0x6a646b)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma unreg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte),
  a0 = Z_to_bv 64 0x16ed30 -> a1 = Z_to_bv 64 97 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> 0x800ce1f8 <= lo ->
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
  evt asegs (unreg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x69d80) fc None m (seg_rom asegs)).
Proof.
  intros until o11. intros -> -> ST LO LOLO (G1 & G2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0x1714f0, 0x1714f8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x6a6460, 0x6a6461); (0x6a6461, 0x6a646b)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 176%nat ST.
  xsteps_to 0x69e28%Z.
  amo_step. showpc. xstep. showpc. amo_step. showpc. xstep. showpc. xstep. showpc.
  xsteps_to 0x69f3c%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gds_at mm 0x16ed30 asan_gds)
      by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
          rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call (unreg_loop asan_gds 97); [exact asan_gds_ok| reflexivity| lia| exact GDS1| exact AI| exact CP| exact RG| exact SHC| exact THR
        | exact RMS| exact SC1| exact SC2| exact SC3| exact O1| exact O2| exact O3| exact O4| exact O5| exact O6| exact O7| exact O8| exact O9| exact O10| exact O11| assumption|].
  xsteps_to 0x8419c%Z.
  assert (EU176 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176) by (apply unsigned_lit; lia).
  lazymatch goal with H : stk asegs ?mm 2147633388 2147647154 |- _ => rename H into SCX2 end.
  call psglob_spec; [reflexivity| reflexivity| reflexivity| rewrite EU176; exact ST| lia| lia| exact G2| exact RMS| exact SHC| exact THR
        | exact SCX2| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176))) |- _ => rewrite EU176 in H; rename H into ST end.
  xsteps_to 0x6a198%Z.
  amo_step. xstep. amo_step. xstep. xstep. xstep.
  xsteps_to 0x6a24c%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  unfold unreg_post. sys_finish.
Qed.
