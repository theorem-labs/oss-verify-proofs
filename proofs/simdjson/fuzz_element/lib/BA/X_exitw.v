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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small D_kit X_aexdefs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import X_atexit X_xdefs X_unreg X_fini.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
    ms' = MS (mkR (Z_to_bv 64 0x14b508) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 code) s1
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1533d4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 320, bv_unsigned sp); (0x6c80d8, 0x6c80dc); (0x6c7eb8, 0x6c7ed0); (0x1705d0, 0x1705d1);
              (0x170580, 0x170588); (0x1714f0, 0x1714f8); (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI);
              (0x6a6460, 0x6a6461); (0x6a6461, 0x6a646b)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -16).

Lemma exit_prefix_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo code tid : Z) (p1 p2 : list byte) (f1 : word) (cdt thr sec : byte) (tm1 : word)
    (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte) (flag dso : word),
  a0 = Z_to_bv 64 code -> tp = Z_to_bv 64 0x6a7e68 -> 0 <= code < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 320 -> 0x800ce1f8 <= lo ->
  rw_cells asegs m 0x6a7dc0 [C4 (Z_to_bv 64 tid)] -> 1 <= tid < 2^31 ->
  aex_case m p1 p2 f1 ->
  rw_cells asegs m 0x6c80d8 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x6c80f8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells asegs m 0x205ae0 [C1 (Z_to_bv 8 0)] ->
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
  evt asegs (exit_prefix_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14b49c) fc None m (seg_rom asegs)).
Proof.
  intros until dso. intros -> -> HC ST LO LOLO TID HT AEXC EXL LIBC COV FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP
    THR RMS SC1 SC2 SC3 GDS O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (0x6c80d8, 0x6c80dc); (0x6c7eb8, 0x6c7ed0); (0x1705d0, 0x1705d1);
              (0x170580, 0x170588); (0x1714f0, 0x1714f8); (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI);
              (0x6a6460, 0x6a6461); (0x6a6461, 0x6a646b)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EU16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  assert (EUT : bv_unsigned (Z_to_bv 64 tid) = tid) by (apply unsigned_lit; lia).
  destruct AEXC as [(ar1 & ATX & ATA)|(Ef1 & ATX & ATA & AFL)]; unfold aex_tbl in ATX; aex_lits.
  -
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
    call funcs_on_exit_spec1; [rewrite EU16; exact ST| exact ATX| exact ATA| exact LIBC| exact COV| assumption| lia| lia|].
    lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.

    astep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GDS1 : gds_at mm 0x16ed30 asan_gds)
        by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
            rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
    clear GDS.
    call fini_spec; [rewrite EU16; exact ST| lia| lia| exact FA| exact GF| exact GCX| exact DSO| exact GX| exact CPL| exact FLG| exact FLGNZ
          | exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP| exact THR| exact RMS| exact SC1| exact SC2| exact SC3
          | exact GDS1| exact O1| exact O2| exact O3| exact O4| exact O5| exact O6| exact O7| exact O8| exact O9| exact O10| exact O11| assumption|].
    lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.

    astep.
    unfold exit_prefix_post. sys_finish.
  -
    subst f1.
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
    call funcs_on_exit_spec2; [rewrite EU16; exact ST| exact ATX| exact ATA| exact AFL| exact LIBC| exact COV| assumption| lia| lia|].
    lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.

    astep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GDS1 : gds_at mm 0x16ed30 asan_gds)
        by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
            rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
    clear GDS.
    call fini_spec; [rewrite EU16; exact ST| lia| lia| exact FA| exact GF| exact GCX| exact DSO| exact GX| exact CPL| exact FLG| exact FLGNZ
          | exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP| exact THR| exact RMS| exact SC1| exact SC2| exact SC3
          | exact GDS1| exact O1| exact O2| exact O3| exact O4| exact O5| exact O6| exact O7| exact O8| exact O9| exact O10| exact O11| assumption|].
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
                  F (Z_to_bv 64 0x14b1ac) (Z_to_bv 64 94) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 0x14b508) (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14b508) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros HC MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 4 lstep. step_ecall.
  eexists. reflexivity.
Qed.
