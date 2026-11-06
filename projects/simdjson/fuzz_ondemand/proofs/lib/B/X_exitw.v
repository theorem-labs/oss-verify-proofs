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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout R_small D_kit X_aexdefs X_atexit X_xdefs X_unreg X_fini.
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
    ms' = MS (mkR (Z_to_bv 64 0x102940) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 code) s1
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1087fc) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 320, bv_unsigned sp); (0x6770e0, 0x6770e4); (0x676ec0, 0x676ed8); (0x120490, 0x120491);
              (0x120440, 0x120448); (0x1213b0, 0x1213b8); (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI);
              (0x656320, 0x656321); (0x656321, 0x65632b)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp + -16).

Lemma exit_prefix_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo code tid : Z) (p1 p2 : list byte) (f1 : word) (cdt thr sec : byte) (tm1 : word)
    (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte) (flag dso : word),
  a0 = Z_to_bv 64 code -> tp = Z_to_bv 64 0x656e70 -> 0 <= code < 2^64 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 320 -> 0x800d0000 <= lo ->
  rw_cells bsegs m 0x656dc8 [C4 (Z_to_bv 64 tid)] -> 1 <= tid < 2^31 ->
  aex_case m p1 p2 f1 ->
  rw_cells bsegs m 0x6770e0 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x677100 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells bsegs m 0x1b59a0 [C1 (Z_to_bv 8 0)] ->
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
  evt bsegs (exit_prefix_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1028d4) fc None m (seg_rom bsegs)).
Proof.
  intros until dso. intros -> -> HC ST LO LOLO TID HT AEXC EXL LIBC COV FA GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP
    THR RMS SC1 SC2 SC3 GDS O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (0x6770e0, 0x6770e4); (0x676ec0, 0x676ed8); (0x120490, 0x120491);
              (0x120440, 0x120448); (0x1213b0, 0x1213b8); (XS1_LO, XS1_HI); (XS2_LO, XS2_HI); (XS3_LO, XS3_HI);
              (0x656320, 0x656321); (0x656321, 0x65632b)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
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
    lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.

    astep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GDS1 : gds_at mm 0x11fb20 asan_gds)
        by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
            rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
    clear GDS.
    call fini_spec; [rewrite EU16; exact ST| lia| lia| exact FA| exact GF| exact GCX| exact DSO| exact GX| exact CPL| exact FLG| exact FLGNZ
          | exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP| exact THR| exact RMS| exact SC1| exact SC2| exact SC3
          | exact GDS1| exact O1| exact O2| exact O3| exact O4| exact O5| exact O6| exact O7| exact O8| exact O9| exact O10| exact O11| assumption|].
    lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.

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
    lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.

    astep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (GDS1 : gds_at mm 0x11fb20 asan_gds)
        by (apply (gds_at_agree _ m _ _ GDS); apply (agree_of_munch _ _ _ _ MU); intros xa Hxa;
            rewrite asan_gds_length in Hxa; cbn [outside]; lia) end.
    clear GDS.
    call fini_spec; [rewrite EU16; exact ST| lia| lia| exact FA| exact GF| exact GCX| exact DSO| exact GX| exact CPL| exact FLG| exact FLGNZ
          | exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP| exact THR| exact RMS| exact SC1| exact SC2| exact SC3
          | exact GDS1| exact O1| exact O2| exact O3| exact O4| exact O5| exact O6| exact O7| exact O8| exact O9| exact O10| exact O11| assumption|].
    lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.

    astep.
    unfold exit_prefix_post. sys_finish.
Qed.

Lemma exit_tail_spec : forall (sp code : Z) (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  0 <= code < 2^64 -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' : word),
      ms' = MSsvc (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 (Z_to_bv 64 code) (Z_to_bv 64 code) a2 a3 a4 a5 a6
                       (Z_to_bv 64 94) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1026ac) (Z_to_bv 64 94) fc None m (seg_rom bsegs))
    (MS (mkR (Z_to_bv 64 0x102940) (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x102940) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros HC MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  do 4 lstep. step_ecall.
  eexists. reflexivity.
Qed.
