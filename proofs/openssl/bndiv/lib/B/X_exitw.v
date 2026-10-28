(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA SysStep Arr Walk.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_thread D_kit X_atexit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition ossl_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma ossl_dtor_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (b0 : byte),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m 0xbd65e0 [C1 b0] -> rw_cells bsegs m 0xbd6600 [C1 (Z_to_bv 8 0)] ->
  mem_inv bsegs m ->
  lo <= bv_unsigned sp - 48 -> 0xbfd000 <= lo ->
  evt bsegs (ossl_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20c324) fc None m (seg_rom bsegs)).
Proof.
  intros until b0. intros ST BI DGC MI LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (ZX : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b) by (intros b; unfold zxb; apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia).
  carve_frame 48%nat ST.
  steps_to 0x20c348%Z.
  assert (EB : bv_unsigned (Z_to_bv 64 (bv_unsigned b0)) = bv_unsigned b0)
    by (apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b0) as R; unfold bv_modulus in R; cbn in R; lia).
  destruct (Z.eq_dec (bv_unsigned b0) 0) as [B0|B0].
  - assert (EZ : bv_unsigned (zxb b0) = 0) by (rewrite ZX; exact B0).
    astep.
    steps_to 0x20c418%Z. release_frame FR ST (bv_unsigned sp). astep.
    unfold ossl_dtor_post. sys_finish.
  - assert (EZ : bv_unsigned (zxb b0) <> 0) by (rewrite ZX; exact B0).
    astep.
    steps_to 0x20c418%Z. release_frame FR ST (bv_unsigned sp). astep.
    unfold ossl_dtor_post. sys_finish.
Qed.

(* [comment removed for export] *)
Definition exit_A_post (ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code tid : Z) (p1 p2 : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s0x : word) (jf : list byte) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x55798c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 tpA) t0' t1' t2'
                  (Z_to_bv 64 0x56b3f0) (Z_to_bv 64 0x56b3f0) a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x1ee8d4) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (0xbfb0c0, 0xbfb0c4); (0xbfaea0, 0xbfaeb8); (0x6a0390, 0x6a0391)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    (* [comment removed for export] *)
    /\ rw_cells bsegs m' (bv_unsigned sp + -16) [C8 s0x; C8 ra]
    /\ rw_cells bsegs m' (bv_unsigned sp + -48) [CB 8 jf; C8 s1; C8 (Z_to_bv 64 code); C8 (Z_to_bv 64 0x557a10)]
    /\ stk bsegs m' lo (bv_unsigned sp + -48).

Lemma exit_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo code tid : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 dso : word) (b0 : byte)
    (n : Z) (f1 a1v : word),
  a0 = Z_to_bv 64 code -> tp = Z_to_bv 64 tpA -> 0 <= code < 2^64 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> 0xbfd000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells bsegs m 0xbdada8 [C4 (Z_to_bv 64 tid)] -> 1 <= tid < 2^31 ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xbfaea0 (atexit_cells fin p1 p2 n 0xbfaeb8 0 0x557954 f1) ->
  rw_cells bsegs m 0xbfafc0 [C8 (Z_to_bv 64 0x1dd8a8); C8 a1v] ->
  n = 1 \/ (n = 2 /\ f1 = Z_to_bv 64 0x557954 /\ a1v = Z_to_bv 64 0x1ee2e0) ->
  rw_cells bsegs m 0xbd6054 [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0xbfb0c0 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xbfb0e0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells bsegs m 0x7358a0 [C1 (Z_to_bv 8 0)] ->
  ro_cells bsegs m 0x56b3f0 [C8 (Z_to_bv 64 0x1ee8d4); C8 (Z_to_bv 64 0x194a98); C8 (Z_to_bv 64 0x20c324)] ->
  ro_cells bsegs m 0x5e2c70 [C8 (Z_to_bv 64 0x56b408); C8 (Z_to_bv 64 0x56b3f0)] ->
  ro_cells bsegs m 0x5e0ca8 [C8 (Z_to_bv 64 0x55788c); C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x5e3ce0 [C8 dso] ->
  rw_cells bsegs m 0x6a0390 [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xbd65e0 [C1 b0] -> rw_cells bsegs m 0xbd6600 [C1 (Z_to_bv 8 0)] ->
  mem_inv bsegs m ->
  evt bsegs (exit_A_post ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code tid p1 p2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5579a8) fc None m (seg_rom bsegs)).
Proof.
  intros until a1v. intros -> -> HC ST LO LOLO HSP TID HT ATX ATA NH ICB EXL LIBC COV FA GF GCX DSO CPL BI DGC MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (0xbfb0c0, 0xbfb0c4); (0xbfaea0, 0xbfaeb8); (0x6a0390, 0x6a0391)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EU16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (EUT : bv_unsigned (Z_to_bv 64 tid) = tid) by (apply unsigned_lit; lia).
  unfold atexit_cells in ATX. unfold tpA in *.
  carve_frame 16%nat ST.
  do 6 lstep.
  rewrite (sx32_small_A tid ltac:(lia)).
  lstep. lstep.
  (* [comment removed for export] *)
  amo_step. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
  astep. amo_step. astep.
  astep. fold_sx32. fold_closed_in_goal.
  astep. astep.
  astep.
  (* [comment removed for export] *)
  astep.
  destruct NH as [->|(-> & -> & ->)].
  - call funcs_on_exit_spec; [rewrite EU16; exact ST| exact ATX| exact ATA| exact LIBC| exact COV| assumption| lia| lia|].
    lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
    lazymatch goal with H : rw_cells bsegs _ 12562080 _ |- _ => unfold atexit_cells in H; rename H into ATX end.
    (* [comment removed for export] *)
    astep.
    carve_frame 32%nat ST.
    steps_to 0x20c324%Z.
    call (ossl_dtor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo b0); [rewrite EU48; exact ST| assumption| assumption| assumption| rewrite EU48; lia| lia|].
    lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST end.
    (* [comment removed for export] *)
    steps_to 0x194a98%Z.
    carve_frame 16%nat ST.
    steps_to 0x194b2c%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
    (* [comment removed for export] *)
    steps_to 0x1ee8d4%Z.
    unfold exit_A_post. sys_finish.
    all: try eassumption.
  - call funcs_on_exit_spec2; [rewrite EU16; exact ST| exact ATX| exact ATA| exact LIBC| exact COV| exact ICB| assumption| lia| lia|].
    lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
    lazymatch goal with H : rw_cells bsegs _ 12562080 _ |- _ => unfold atexit_cells in H; rename H into ATX end.
    (* [comment removed for export] *)
    astep.
    carve_frame 32%nat ST.
    steps_to 0x20c324%Z.
    call (ossl_dtor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo b0); [rewrite EU48; exact ST| assumption| assumption| assumption| rewrite EU48; lia| lia|].
    lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST end.
    (* [comment removed for export] *)
    steps_to 0x194a98%Z.
    carve_frame 16%nat ST.
    steps_to 0x194b2c%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
    (* [comment removed for export] *)
    steps_to 0x1ee8d4%Z.
    unfold exit_A_post. sys_finish.
    all: try eassumption.
Qed.

(* [comment removed for export] *)
Definition exit_E_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR (Z_to_bv 64 0x557a14) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 code) s1
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x55de04) fc None m (seg_rom bsegs)
    /\ stk bsegs m lo (bv_unsigned sp + -16).

Lemma exit_E_spec : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo code : Z) (jf : list byte),
  0 <= code < 2^64 ->
  rw_cells bsegs m (bv_unsigned sp + -48) [CB 8 jf; C8 s1; C8 (Z_to_bv 64 code); C8 (Z_to_bv 64 0x557a10)] ->
  stk bsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 0xbfd000 <= lo -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m ->
  evt bsegs (exit_E_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code m)
    (MS (mkR (Z_to_bv 64 0x55798c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 0x56b3f0) (Z_to_bv 64 0x56b3f0)
             a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55798c) fc None m (seg_rom bsegs)).
Proof.
  intros until jf. intros HC FR ST LO LOLO HSP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  steps_to 0x5579a4%Z. release_frame FR ST (bv_unsigned sp + -16).
  astep. astep.
  (* [comment removed for export] *)
  astep.
  unfold exit_E_post. sys_finish.
Qed.

(* [comment removed for export] *)
Lemma exit_tail_spec : forall (sp code : Z) (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  0 <= code < 2^64 -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (ra' : word),
      ms' = MSsvc (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 (Z_to_bv 64 code) (Z_to_bv 64 code) a2 a3 a4 a5 a6
                       (Z_to_bv 64 94) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x55777c) (Z_to_bv 64 94) fc None m (seg_rom bsegs))
    (MS (mkR (Z_to_bv 64 0x557a14) (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x557a14) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros HC MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  do 4 lstep. step_ecall.
  eexists. reflexivity.
Qed.
