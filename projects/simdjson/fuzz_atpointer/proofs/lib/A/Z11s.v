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
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zot Z9p D_kit Z11l Z11v Z11t Z11u Z11r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

Definition unreg_got (m : mem) : Prop :=
  ro_cells asegs m 0x10b1c0 [C8 (Z_to_bv 64 0x1a35e0)]
  /\ ro_cells asegs m 0x10b1d0 [C8 (Z_to_bv 64 0x1a5668); C8 (Z_to_bv 64 0x111338); C8 (Z_to_bv 64 0x113b38);
                               C8 (Z_to_bv 64 0x114828); C8 (Z_to_bv 64 0x114830); C8 (Z_to_bv 64 0x114820);
                               C8 (Z_to_bv 64 0x10d128)].

Definition unreg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (0x1113f0, 0x1113f8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x646360, 0x646361); (0x646361, 0x64636a)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma unreg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 : byte),
  a0 = Z_to_bv 64 0x10fba0 -> a1 = Z_to_bv 64 35 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> 0x800d0000 <= lo ->
  unreg_got m ->
  ro_cells asegs m 0x111350 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m 0x1113f0 [C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x113b38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m 0x114818 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x11339c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x1a56e0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells asegs m 0x10d128 [C8 (Z_to_bv 64 0x1013ec)] ->
  stk asegs m XS1_LO XS1_HI -> stk asegs m XS2_LO XS2_HI -> stk asegs m XS3_LO XS3_HI ->
  gds_at m 0x10fba0 asan_gds ->
  rw_cells asegs m 0x646360 [C1 o1] -> rw_cells asegs m 0x646361 [C1 o2] -> rw_cells asegs m 0x646362 [C1 o3] -> rw_cells asegs m 0x646363 [C1 o4] -> rw_cells asegs m 0x646364 [C1 o5] -> rw_cells asegs m 0x646365 [C1 o6] -> rw_cells asegs m 0x646366 [C1 o7] -> rw_cells asegs m 0x646367 [C1 o8] -> rw_cells asegs m 0x646368 [C1 o9] -> rw_cells asegs m 0x646369 [C1 o10] ->
  mem_inv asegs m ->
  evt asegs (unreg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x53d98) fc None m (seg_rom asegs)).
Proof.
  intros until o10. intros -> -> ST LO LOLO (G1 & G2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0x1113f0, 0x1113f8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x646360, 0x646361); (0x646361, 0x64636a)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 176%nat ST.
  xsteps_to 0x53e40%Z.
  amo_step. showpc. xstep. showpc. amo_step. showpc. xstep. showpc. xstep. showpc.
  xsteps_to 0x53f54%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gds_at mm 0x10fba0 asan_gds)
      by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
          rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call (unreg_loop asan_gds 35); [exact asan_gds_ok| reflexivity| lia| exact GDS1| exact AI| exact CP| exact RG| exact SHC| exact THR
        | exact RMS| exact SC1| exact SC2| exact SC3| exact O1| exact O2| exact O3| exact O4| exact O5| exact O6| exact O7| exact O8| exact O9| exact O10| assumption|].
  xsteps_to 0x69560%Z.
  assert (EU176 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176) by (apply unsigned_lit; lia).
  lazymatch goal with H : stk asegs ?mm 2147585964 2147590284 |- _ => rename H into SCX2 end.
  call psglob_spec; [reflexivity| reflexivity| reflexivity| rewrite EU176; exact ST| lia| lia| exact G2| exact RMS| exact SHC| exact THR
        | exact SCX2| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176))) |- _ => rewrite EU176 in H; rename H into ST end.
  xsteps_to 0x541b0%Z.
  amo_step. xstep. amo_step. xstep. xstep. xstep.
  xsteps_to 0x54264%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  unfold unreg_post. sys_finish.
Qed.
