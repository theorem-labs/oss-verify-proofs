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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import SysStep.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import R_small F_memset D_kit X_atexit X_xdefs X_unregi X_unregl X_psglob.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

(* [comment removed for export] *)
Definition unreg_got (m : mem) : Prop :=
  ro_cells asegs m 0xeb9c0 [C8 (Z_to_bv 64 0x1870e0)]
  /\ ro_cells asegs m 0xeb9d0 [C8 (Z_to_bv 64 0x189168); C8 (Z_to_bv 64 0xf4e38); C8 (Z_to_bv 64 0xf7638);
                               C8 (Z_to_bv 64 0xf8328); C8 (Z_to_bv 64 0xf8330); C8 (Z_to_bv 64 0xf8320);
                               C8 (Z_to_bv 64 0xed8c0)].

Definition unreg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) (RT_iface.frm_clear fc) None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (0xf4ef0, 0xf4ef8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x629cc2, 0x629cc3); (0x629cc0, 0x629cc2)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma unreg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (o1 o2 o3 : byte),
  a0 = Z_to_bv 64 0xf03c0 -> a1 = Z_to_bv 64 239 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 240 -> 0x800c0000 <= lo ->
  unreg_got m ->
  ro_cells asegs m 0xf4e50 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m 0xf4ef0 [C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0xf7638 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m 0xf8318 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0xf6e9c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x1891e0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells asegs m 0xed8c0 [C8 (Z_to_bv 64 0xe211c)] ->
  stk asegs m XS1_LO XS1_HI -> stk asegs m XS2_LO XS2_HI -> stk asegs m XS3_LO XS3_HI ->
  gds_at m 0xf03c0 asan_gds ->
  rw_cells asegs m 0x629cc2 [C1 o1] -> rw_cells asegs m 0x629cc0 [C1 o2] -> rw_cells asegs m 0x629cc1 [C1 o3] ->
  mem_inv asegs m ->
  evt asegs (unreg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4e928) (RT_iface.frm_clear fc) None m (seg_rom asegs)).
Proof.
  intros until o3. intros -> -> ST LO LOLO (G1 & G2) RG MUX SHC AI CP THR RMS SC1 SC2 SC3 GDS O1 O2 O3 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0xf4ef0, 0xf4ef8);
              (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI); (0x629cc2, 0x629cc3); (0x629cc0, 0x629cc2)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 176%nat ST.
  xsteps_to 0x4e9d0%Z.
  amo_step. showpc. xstep. showpc. amo_step. showpc. xstep. showpc. xstep. showpc.
  xsteps_to 0x4eae4%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gds_at mm 0xf03c0 asan_gds)
      by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
          rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call (unreg_loop asan_gds 239); [exact asan_gds_ok| reflexivity| lia| exact GDS1| exact AI| exact CP| exact RG| exact SHC| exact THR
        | exact RMS| exact SC1| exact SC2| exact SC3| exact O1| exact O2| exact O3| assumption|].
  xsteps_to 0x636f4%Z.
  assert (EU176 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176) by (apply unsigned_lit; lia).
  lazymatch goal with H : stk asegs ?mm 2147573760 2147575792 |- _ => rename H into SCX2 end.
  call psglob_spec; [reflexivity| reflexivity| reflexivity| rewrite EU176; exact ST| lia| lia| exact G2| exact RMS| exact SHC| exact THR
        | exact SCX2| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176))) |- _ => rewrite EU176 in H; rename H into ST end.
  xsteps_to 0x4ed40%Z.
  amo_step. xstep. amo_step. xstep. xstep. xstep.
  xsteps_to 0x4edf4%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  unfold unreg_post. sys_finish.
Qed.
