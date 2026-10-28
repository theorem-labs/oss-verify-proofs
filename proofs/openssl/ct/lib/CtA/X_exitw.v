(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac SysStep Arr Walk. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_thread D_kit X_atexit.
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
             F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ stk ctasegs m' lo (bv_unsigned sp).

Lemma ossl_dtor_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (b0 : byte),
  stk ctasegs m lo (bv_unsigned sp) ->
  rw_cells ctasegs m 0xba46c0 [C1 b0] -> rw_cells ctasegs m 0xba46e0 [C1 (Z_to_bv 8 0)] ->
  mem_inv ctasegs m ->
  lo <= bv_unsigned sp - 48 -> 0xbcb000 <= lo ->
  evt ctasegs (ossl_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1f4400) fc None m (seg_rom ctasegs)).
Proof.
  intros until b0. intros ST BI DGC MI LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  assert (ZX : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b) by (intros b; unfold zxb; apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia).
  carve_frame 48%nat ST.
  steps_to 0x1f4424%Z.
  assert (EB : bv_unsigned (Z_to_bv 64 (bv_unsigned b0)) = bv_unsigned b0)
    by (apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b0) as R; unfold bv_modulus in R; cbn in R; lia).
  destruct (Z.eq_dec (bv_unsigned b0) 0) as [B0|B0].
  - assert (EZ : bv_unsigned (zxb b0) = 0) by (rewrite ZX; exact B0).
    astep.
    steps_to 0x1f4500%Z. release_frame FR ST (bv_unsigned sp). astep.
    unfold ossl_dtor_post. sys_finish.
  - assert (EZ : bv_unsigned (zxb b0) <> 0) by (rewrite ZX; exact B0).
    astep.
    steps_to 0x1f4500%Z. release_frame FR ST (bv_unsigned sp). astep.
    unfold ossl_dtor_post. sys_finish.
Qed.

(* [comment removed for export] *)
Definition exit_A_post (ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code tid : Z) (p1 p2 : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s0x : word) (jf : list byte) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x51fc10) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 tpA) t0' t1' t2'
                  (Z_to_bv 64 0x533428) (Z_to_bv 64 0x533428) a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x1f43d0) fc None m' (seg_rom ctasegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (0xbc9660, 0xbc9664); (0xbc9440, 0xbc9458); (0x66e9d0, 0x66e9d1)] m m'
    /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    (* [comment removed for export] *)
    /\ rw_cells ctasegs m' (bv_unsigned sp + -16) [C8 s0x; C8 ra]
    /\ rw_cells ctasegs m' (bv_unsigned sp + -48) [CB 8 jf; C8 s1; C8 (Z_to_bv 64 code); C8 (Z_to_bv 64 0x51fc94)]
    /\ stk ctasegs m' lo (bv_unsigned sp + -48).

Lemma exit_A_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo code tid : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 dso : word) (b0 : byte)
    (n : Z) (f1 a1v : word),
  a0 = Z_to_bv 64 code -> tp = Z_to_bv 64 tpA -> 0 <= code < 2^64 ->
  stk ctasegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> 0xbcb000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells ctasegs m 0xba9348 [C4 (Z_to_bv 64 tid)] -> 1 <= tid < 2^31 ->
  (* [comment removed for export] *)
  rw_cells ctasegs m 0xbc9440 (atexit_cells fin p1 p2 n 0xbc9458 0 0x51fbd8 f1) ->
  rw_cells ctasegs m 0xbc9560 [C8 (Z_to_bv 64 0x1e363c); C8 a1v] ->
  n = 1 \/ (n = 2 /\ f1 = Z_to_bv 64 0x51fbd8 /\ a1v = Z_to_bv 64 0x1f4074) ->
  rw_cells ctasegs m 0xba4694 [C1 (Z_to_bv 8 0)] ->
  rw_cells ctasegs m 0xbc9660 [C4 (Z_to_bv 64 0)] ->
  rw_cells ctasegs m 0xbc9680 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells ctasegs m 0x703ee0 [C1 (Z_to_bv 8 0)] ->
  ro_cells ctasegs m 0x533428 [C8 (Z_to_bv 64 0x1f43d0); C8 (Z_to_bv 64 0x19ab8c); C8 (Z_to_bv 64 0x1f4400)] ->
  ro_cells ctasegs m 0x5ab210 [C8 (Z_to_bv 64 0x533440); C8 (Z_to_bv 64 0x533428)] ->
  ro_cells ctasegs m 0x5a9208 [C8 (Z_to_bv 64 0x51fb10); C8 (Z_to_bv 64 0)] ->
  ro_cells ctasegs m 0x5ac280 [C8 dso] ->
  rw_cells ctasegs m 0x66e9d0 [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  rw_cells ctasegs m 0xba46c0 [C1 b0] -> rw_cells ctasegs m 0xba46e0 [C1 (Z_to_bv 8 0)] ->
  mem_inv ctasegs m ->
  evt ctasegs (exit_A_post ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code tid p1 p2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x51fc2c) fc None m (seg_rom ctasegs)).
Proof.
  intros until a1v. intros -> -> HC ST LO LOLO HSP TID HT ATX ATA NH ICB EXL LIBC COV FA GF GCX DSO CPL BI DGC MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (0xbc9660, 0xbc9664); (0xbc9440, 0xbc9458); (0x66e9d0, 0x66e9d1)] m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
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
    lazymatch goal with H : stk ctasegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
    lazymatch goal with H : rw_cells ctasegs _ 12358720 _ |- _ => unfold atexit_cells in H; rename H into ATX end.
    (* [comment removed for export] *)
    astep.
    carve_frame 32%nat ST.
    steps_to 0x1f4400%Z.
    call (ossl_dtor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo b0); [rewrite EU48; exact ST| assumption| assumption| assumption| rewrite EU48; lia| lia|].
    lazymatch goal with H : stk ctasegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST end.
    (* [comment removed for export] *)
    steps_to 0x19ab8c%Z.
    carve_frame 16%nat ST.
    steps_to 0x19ac20%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
    (* [comment removed for export] *)
    steps_to 0x1f43d0%Z.
    unfold exit_A_post. sys_finish.
    all: try eassumption.
  - call funcs_on_exit_spec2; [rewrite EU16; exact ST| exact ATX| exact ATA| exact LIBC| exact COV| exact ICB| assumption| lia| lia|].
    lazymatch goal with H : stk ctasegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU16 in H; rename H into ST end.
    lazymatch goal with H : rw_cells ctasegs _ 12358720 _ |- _ => unfold atexit_cells in H; rename H into ATX end.
    (* [comment removed for export] *)
    astep.
    carve_frame 32%nat ST.
    steps_to 0x1f4400%Z.
    call (ossl_dtor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo b0); [rewrite EU48; exact ST| assumption| assumption| assumption| rewrite EU48; lia| lia|].
    lazymatch goal with H : stk ctasegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU48 in H; rename H into ST end.
    (* [comment removed for export] *)
    steps_to 0x19ab8c%Z.
    carve_frame 16%nat ST.
    steps_to 0x19ac20%Z. release_frame FR1 ST (bv_unsigned sp + -48). astep.
    (* [comment removed for export] *)
    steps_to 0x1f43d0%Z.
    unfold exit_A_post. sys_finish.
    all: try eassumption.
Qed.

(* [comment removed for export] *)
Definition exit_E_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR (Z_to_bv 64 0x51fc98) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 code) s1
                  a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x526088) fc None m (seg_rom ctasegs)
    /\ stk ctasegs m lo (bv_unsigned sp + -16).

Lemma exit_E_spec : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo code : Z) (jf : list byte),
  0 <= code < 2^64 ->
  rw_cells ctasegs m (bv_unsigned sp + -48) [CB 8 jf; C8 s1; C8 (Z_to_bv 64 code); C8 (Z_to_bv 64 0x51fc94)] ->
  stk ctasegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 0xbcb000 <= lo -> bv_unsigned sp <= 2^47 ->
  mem_inv ctasegs m ->
  evt ctasegs (exit_E_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code m)
    (MS (mkR (Z_to_bv 64 0x51fc10) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 0x533428) (Z_to_bv 64 0x533428)
             a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x51fc10) fc None m (seg_rom ctasegs)).
Proof.
  intros until jf. intros HC FR ST LO LOLO HSP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [] m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  steps_to 0x51fc28%Z. release_frame FR ST (bv_unsigned sp + -16).
  astep. astep.
  (* [comment removed for export] *)
  astep.
  unfold exit_E_post. sys_finish.
Qed.

(* [comment removed for export] *)
Lemma exit_tail_spec : forall (sp code : Z) (gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  0 <= code < 2^64 -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (ra' : word),
      ms' = MSsvc (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 (Z_to_bv 64 code) (Z_to_bv 64 code) a2 a3 a4 a5 a6
                       (Z_to_bv 64 94) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x51fa00) (Z_to_bv 64 94) fc None m (seg_rom ctasegs))
    (MS (mkR (Z_to_bv 64 0x51fc98) (Z_to_bv 64 sp) gp tp t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x51fc98) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. intros HC MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  do 4 lstep. step_ecall.
  eexists. reflexivity.
Qed.
