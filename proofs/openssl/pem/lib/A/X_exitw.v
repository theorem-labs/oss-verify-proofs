(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small D_kit X_ax X_atexit X_gdefs X_unreg X_fini.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
    ms' = MS (mkR (Z_to_bv 64 0x51b0cc) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 code) s1
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x5214bc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 320, bv_unsigned sp); (0xbc4160, 0xbc4164); (0xbc3f40, 0xbc3f58); (0x6694d0, 0x6694d1);
              (0x669480, 0x669488); (0x66a3f0, 0x66a3f8); (SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -16).

Lemma exit_prefix_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo code tid : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word)
    (flag dso : word) (bi : byte) (k : bool),
  a0 = Z_to_bv 64 code -> tp = Z_to_bv 64 0xba3ef0 -> 0 <= code < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 320 -> SHW_HI <= lo ->
  rw_cells asegs m 0xba3e48 [C4 (Z_to_bv 64 tid)] -> 1 <= tid < 2^31 ->
  rw_cells asegs m 0xbc3f40 (ax_cells k fin p1 p2) ->                        (* [comment removed for export] *)
  rw_cells asegs m 0xbc4060 (ax_acells k) ->
  rw_cells asegs m 0xbc4160 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xbc4180 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells asegs m 0x6fe9e0 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 0x52e860 [C8 (Z_to_bv 64 0x1f34cc); C8 (Z_to_bv 64 0x199adc); C8 (Z_to_bv 64 0x1f34fc)] ->
  rw_cells asegs m 0xb9f1c0 [C1 bi] ->                                       (* [comment removed for export] *)
  rw_cells asegs m 0xb9f1e0 [C1 (Z_to_bv 8 0)] ->                           (* [comment removed for export] *)
  ro_cells asegs m 0x5a6548 [C8 (Z_to_bv 64 0x52e878); C8 (Z_to_bv 64 0x52e860)] ->
  ro_cells asegs m 0x5a4588 [C8 (Z_to_bv 64 0x51af44); C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x5a75c0 [C8 dso] ->
  ro_cells asegs m 0x5a6500 [C8 (Z_to_bv 64 0x5aaa60); C8 (Z_to_bv 64 0x669460)] ->
  rw_cells asegs m 0x6694d0 [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x669480 [C8 flag] -> bv_unsigned flag <> 0 ->
  unreg_got m ->
  ro_cells asegs m 0x66a350 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m 0x66a3f0 [C8 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m 0x66d818 [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x66c39c [C1 (Z_to_bv 8 1)] ->
  ro_cells asegs m 0x6fe6e0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells asegs m 0x5a77f0 [C8 (Z_to_bv 64 0x526914)] ->
  stk asegs m SHW_LO SHW_HI -> stk asegs m ODR_LO ODR_HI ->
  gtab_at m ->
  mem_inv asegs m ->
  rw_cells asegs m AX_INCB [C1 (Z_to_bv 8 0)] ->                              (* [comment removed for export] *)
  evt asegs (exit_prefix_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x51b060) fc None m (seg_rom asegs)).
Proof.
  intros until k. intros -> -> HC ST LO LOLO TID HT ATX ATA EXL LIBC COV FA BI CL GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP
    THR RMS SCW OW GDS MI INCB.
  unfold AX_INCB in INCB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (0xbc4160, 0xbc4164); (0xbc3f40, 0xbc3f58); (0x6694d0, 0x6694d1);
              (0x669480, 0x669488); (0x66a3f0, 0x66a3f8); (SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EU16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  assert (EUT : bv_unsigned (Z_to_bv 64 tid) = tid) by (apply unsigned_lit; lia).
  unfold ax_cells, ax_acells, ax_slot, AX_CALL, AX_GUARD, AX_COVD in ATX, ATA.
  carve_frame 16%nat ST.
  do 6 lstep.
  rewrite (sx32_small_A tid ltac:(lia)).
  lstep. lstep.
  (* [comment removed for export] *)
  amo_step. showpc. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
  astep. showpc. amo_step. showpc. astep. showpc.
  astep. showpc. fold_sx32. fold_closed_in_goal.
  astep. showpc. astep. showpc.
  astep. showpc.
  (* [comment removed for export] *)
  astep.
  call funcs_on_exit_spec; [rewrite EU16; exact ST| unfold ax_cells, ax_slot, AX_CALL; exact ATX| unfold ax_acells, AX_COVD, AX_GUARD; exact ATA
                           | exact LIBC| exact COV| assumption| lia| lia| unfold AX_INCB; exact INCB|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
  (* [comment removed for export] *)
  astep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gtab_at mm)
      by (apply (gtab_at_munch _ m _ GDS MU); intros xa Hxa; unfold GT_LO, GT_HI in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call fini_spec; [rewrite EU16; exact ST| lia| lia| exact FA| exact BI| exact CL| exact GF| exact GCX| exact DSO| exact GX| exact CPL| exact FLG| exact FLGNZ
        | exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP| exact THR| exact RMS| exact SCW| exact OW
        | exact GDS1| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
  (* [comment removed for export] *)
  astep.
  unfold exit_prefix_post. sys_finish.
Qed.

(* [comment removed for export] *)
Lemma exit_tail_spec : forall (sp code : Z) (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  0 <= code < 2^64 -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (ra' : word),
      ms' = MSsvc (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 (Z_to_bv 64 code) (Z_to_bv 64 code) a2 a3 a4 a5 a6
                       (Z_to_bv 64 94) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x51ae34) (Z_to_bv 64 94) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 0x51b0cc) (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x51b0cc) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros HC MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 4 lstep. step_ecall.
  eexists. reflexivity.
Qed.
