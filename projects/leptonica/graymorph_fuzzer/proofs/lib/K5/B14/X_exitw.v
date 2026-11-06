(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import SysStep.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import R_small D_kit X_atexit X_xdefs X_unreg X_fini.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

Definition exit_prefix_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0xd71e8) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 code) s1
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xdcc6c) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 320, bv_unsigned sp); (0x649538, 0x64953c); (0x649318, 0x649330); (0xf2a90, 0xf2a91);
              (0xf2a40, 0xf2a48); (0xf39b0, 0xf39b8); (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI);
              (0x628782, 0x628783); (0x628780, 0x628782)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -16).

Lemma exit_prefix_spec : forall (ph : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo code tid : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word)
    (o1 o2 o3 : byte) (flag dso : word),
  a0 = Z_to_bv 64 code -> tp = Z_to_bv 64 0x6292c8 -> 0 <= code < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 320 -> 0x800c0000 <= lo ->
  rw_cells asegs m 0x629220 [C4 (Z_to_bv 64 tid)] -> 1 <= tid < 2^31 ->
  rw_cells asegs m 0x649318 (atexit_cells fin p1 p2 (ph_slot ph) 0x649330 0 0xd7128) ->
  atexit_ph ph m ->
  rw_cells asegs m 0x649438 [C8 (Z_to_bv 64 0x7f98c)] ->
  rw_cells asegs m 0x649538 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x649558 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells asegs m 0x187fa0 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 0xe7498 [C8 (Z_to_bv 64 0x90a20); C8 (Z_to_bv 64 0x3edb8)] ->
  ro_cells asegs m 0xeb5e0 [C8 (Z_to_bv 64 0xe74a8); C8 (Z_to_bv 64 0xe7498)] ->
  ro_cells asegs m 0xea8a8 [C8 (Z_to_bv 64 0xd7060); C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0xec620 [C8 dso] ->
  ro_cells asegs m 0xeb558 [C8 (Z_to_bv 64 0xef2a0); C8 (Z_to_bv 64 0xf2a20)] ->
  rw_cells asegs m 0xf2a90 [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xf2a40 [C8 flag] -> bv_unsigned flag <> 0 ->
  unreg_got m ->
  ro_cells asegs m 0xf3910 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m 0xf39b0 [C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0xf60f8 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m 0xf6dd8 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0xf595c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x187ca0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells asegs m 0xec7a0 [C8 (Z_to_bv 64 0xe1014)] ->
  stk asegs m XS1_LO XS1_HI -> stk asegs m XS2_LO XS2_HI -> stk asegs m XS3_LO XS3_HI ->
  gds_at m 0xef2a0 asan_gds ->
  rw_cells asegs m 0x628782 [C1 o1] -> rw_cells asegs m 0x628780 [C1 o2] -> rw_cells asegs m 0x628781 [C1 o3] ->
  mem_inv asegs m ->
  evt asegs (exit_prefix_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xd717c) fc None m (seg_rom asegs)).
Proof.
  intros until dso. intros -> -> HC ST LO LOLO TID HT ATX PH ATA EXL LIBC COV FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP
    THR RMS SC1 SC2 SC3 GDS O1 O2 O3 MI.
  destruct ph; cbn [ph_slot atexit_ph] in ATX, PH; [destruct PH as (PF1 & PA1 & PFL)| clear PH].
  - (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (0x649538, 0x64953c); (0x649318, 0x649330); (0xf2a90, 0xf2a91);
                (0xf2a40, 0xf2a48); (0xf39b0, 0xf39b8); (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI);
                (0x628782, 0x628783); (0x628780, 0x628782)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (EU16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
    assert (EUT : bv_unsigned (Z_to_bv 64 tid) = tid) by (apply unsigned_lit; lia).
    unfold atexit_cells in ATX.
    carve_frame 16%nat ST.
    do 6 lstep.
    rewrite (sx32_small_A tid ltac:(lia)).
    lstep. lstep.
    amo_step. showpc. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
    astep. showpc. amo_step. showpc. astep. showpc.
    astep. showpc. fold_sx32. fold_closed_in_goal.
    astep. showpc. astep. showpc.
    astep. showpc.
    astep.
    call funcs_on_exit_spec1; [rewrite EU16; exact ST| exact ATX| exact ATA| exact LIBC| exact COV| exact (conj PF1 (conj PA1 PFL))| assumption| lia| lia|].
    lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
    astep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GDS1 : gds_at mm 0xef2a0 asan_gds)
        by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
            rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
    clear GDS.
    call fini_spec; [rewrite EU16; exact ST| lia| lia| exact FA| exact GF| exact GCX| exact DSO| exact GX| exact CPL| exact FLG| exact FLGNZ
          | exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP| exact THR| exact RMS| exact SC1| exact SC2| exact SC3
          | exact GDS1| exact O1| exact O2| exact O3| assumption|].
    lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
    astep.
    unfold exit_prefix_post. sys_finish.
  - (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (0x649538, 0x64953c); (0x649318, 0x649330); (0xf2a90, 0xf2a91);
                (0xf2a40, 0xf2a48); (0xf39b0, 0xf39b8); (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI);
                (0x628782, 0x628783); (0x628780, 0x628782)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (EU16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
    assert (EUT : bv_unsigned (Z_to_bv 64 tid) = tid) by (apply unsigned_lit; lia).
    unfold atexit_cells in ATX.
    carve_frame 16%nat ST.
    do 6 lstep.
    rewrite (sx32_small_A tid ltac:(lia)).
    lstep. lstep.
    amo_step. showpc. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
    astep. showpc. amo_step. showpc. astep. showpc.
    astep. showpc. fold_sx32. fold_closed_in_goal.
    astep. showpc. astep. showpc.
    astep. showpc.
    astep.
    call funcs_on_exit_spec0; [rewrite EU16; exact ST| exact ATX| exact ATA| exact LIBC| exact COV| assumption| lia| lia|].
    lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
    astep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GDS1 : gds_at mm 0xef2a0 asan_gds)
        by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
            rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
    clear GDS.
    call fini_spec; [rewrite EU16; exact ST| lia| lia| exact FA| exact GF| exact GCX| exact DSO| exact GX| exact CPL| exact FLG| exact FLGNZ
          | exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP| exact THR| exact RMS| exact SC1| exact SC2| exact SC3
          | exact GDS1| exact O1| exact O2| exact O3| assumption|].
    lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
    astep.
    unfold exit_prefix_post. sys_finish.
Qed.

Lemma exit_tail_spec : forall (sp code : Z) (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  0 <= code < 2^64 -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (ra' : word),
      ms' = MSsvc (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 (Z_to_bv 64 code) (Z_to_bv 64 code) a2 a3 a4 a5 a6
                       (Z_to_bv 64 94) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0xd6f54) (Z_to_bv 64 94) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 0xd71e8) (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xd71e8) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros HC MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 4 lstep. step_ecall.
  eexists. reflexivity.
Qed.
