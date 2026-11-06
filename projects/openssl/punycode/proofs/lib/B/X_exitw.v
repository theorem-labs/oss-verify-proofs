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
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import Layout R_small D_kit X_ax X_atexit X_gdefs X_unreg X_fini.
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
    ms' = MS (mkR (Z_to_bv 64 0x557ef0) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 code) s1
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x55e2e0) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 320, bv_unsigned sp); (0xbfb080, 0xbfb084); (0xbfae60, 0xbfae78); (0x6a0410, 0x6a0411);
              (0x6a03c0, 0x6a03c8); (0x6a1330, 0x6a1338); (SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp + -16).

Lemma exit_prefix_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo code tid : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word)
    (flag dso : word) (k : bool),
  a0 = Z_to_bv 64 code -> tp = Z_to_bv 64 0xbdae10 -> 0 <= code < 2^64 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 320 -> SHW_HI <= lo ->
  rw_cells bsegs m 0xbdad68 [C4 (Z_to_bv 64 tid)] -> 1 <= tid < 2^31 ->
  rw_cells bsegs m 0xbfae60 (ax_cells k fin p1 p2) ->                        (* [comment removed for export] *)
  rw_cells bsegs m 0xbfaf80 (ax_acells k) ->
  rw_cells bsegs m 0xbfb080 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xbfb0a0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells bsegs m 0x735920 [C1 (Z_to_bv 8 0)] ->
  ro_cells bsegs m 0x56b680 [C8 (Z_to_bv 64 0x1eea6c); C8 (Z_to_bv 64 0x194a48); C8 (Z_to_bv 64 0x2080b8)] ->
  rw_cells bsegs m 0xbd65a0 [C1 (Z_to_bv 8 0)] ->                          (* [comment removed for export] *)
  ro_cells bsegs m 0x5e2ef8 [C8 (Z_to_bv 64 0x56b698); C8 (Z_to_bv 64 0x56b680)] ->
  ro_cells bsegs m 0x5e0f28 [C8 (Z_to_bv 64 0x557d68); C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x5e3f60 [C8 dso] ->
  ro_cells bsegs m 0x5e2eb0 [C8 (Z_to_bv 64 0x5e76c0); C8 (Z_to_bv 64 0x6a03c0)] ->
  rw_cells bsegs m 0x6a0410 [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x6a03c0 [C8 flag] -> bv_unsigned flag <> 0 ->
  unreg_got m ->
  ro_cells bsegs m 0x6a1290 [C4 (Z_to_bv 64 1)] ->
  rw_cells bsegs m 0x6a1330 [C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x6a3a78 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells bsegs m 0x6a4758 [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x6a32dc [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m 0x735620 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
  ro_cells bsegs m 0x5e4190 [C8 (Z_to_bv 64 0x563738)] ->
  stk bsegs m SHW_LO SHW_HI -> stk bsegs m ODR_LO ODR_HI ->
  gtab_at m ->
  mem_inv bsegs m ->
  rw_cells bsegs m AX_INCB [C1 (Z_to_bv 8 0)] ->                              (* [comment removed for export] *)
  evt bsegs (exit_prefix_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x557e84) fc None m (seg_rom bsegs)).
Proof.
  intros until k. intros -> -> HC ST LO LOLO TID HT ATX ATA EXL LIBC COV FA BI GF GCX DSO GX CPL FLG FLGNZ (UG1 & UG2) RG MUX SHC AI CP
    THR RMS SCW OW GDS MI INCB.
  unfold AX_INCB in INCB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (0xbfb080, 0xbfb084); (0xbfae60, 0xbfae78); (0x6a0410, 0x6a0411);
              (0x6a03c0, 0x6a03c8); (0x6a1330, 0x6a1338); (SHW_LO, SHW_HI); (ODR_LO, ODR_HI)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
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
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
  (* [comment removed for export] *)
  astep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GDS1 : gtab_at mm)
      by (apply (gtab_at_munch _ m _ GDS MU); intros xa Hxa; unfold GT_LO, GT_HI in Hxa; cbn [outside]; lia) end.
  clear GDS.
  call fini_spec; [rewrite EU16; exact ST| lia| lia| exact FA| exact BI| exact GF| exact GCX| exact DSO| exact GX| exact CPL| exact FLG| exact FLGNZ
        | exact (conj UG1 UG2)| exact RG| exact MUX| exact SHC| exact AI| exact CP| exact THR| exact RMS| exact SCW| exact OW
        | exact GDS1| assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
  (* [comment removed for export] *)
  astep.
  unfold exit_prefix_post. sys_finish.
Qed.

(* [comment removed for export] *)
Lemma exit_tail_spec : forall (sp code : Z) (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  0 <= code < 2^64 -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' : word),
      ms' = MSsvc (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 (Z_to_bv 64 code) (Z_to_bv 64 code) a2 a3 a4 a5 a6
                       (Z_to_bv 64 94) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x557c58) (Z_to_bv 64 94) fc None m (seg_rom bsegs))
    (MS (mkR (Z_to_bv 64 0x557ef0) (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x557ef0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros HC MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  do 4 lstep. step_ecall.
  eexists. reflexivity.
Qed.
