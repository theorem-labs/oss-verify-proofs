(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma opened_walk : forall (usp : Z) (gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  mem_inv bsegs m ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0x1edf00) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
                          (Z_to_bv 64 65536) a1 a2 a3 a4 a5 a6 a7 p1 s3 (Z_to_bv 64 3) (Z_to_bv 64 65536) s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6 F fc e_malloc m))
    (MS (mkR (Z_to_bv 64 RET_OPEN) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1 (Z_to_bv 64 3)
             a1 a2 a3 a4 a5 a6 a7 p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 RET_OPEN) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros MI. unfold RET_OPEN.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  step. if_false.
  do 4 step.
  apply evt_done. unfold entry_st. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma first_read_walk : forall (usp p : Z) (gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 p1 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  0 < p < 2^64 -> mem_inv bsegs m ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0x1edf94) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 p)
                          (Z_to_bv 64 3) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 65536) a3 a4 a5 a6 a7 p1 (Z_to_bv 64 0)
                          (Z_to_bv 64 3) (Z_to_bv 64 65536) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 p) s8 s9 s10 s11
                          t3 t4 t5 t6 F fc e_read m))
    (MS (mkR (Z_to_bv 64 0x1edf00) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1 (Z_to_bv 64 p)
             a1 a2 a3 a4 a5 a6 a7 p1 s3 (Z_to_bv 64 3) (Z_to_bv 64 65536) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1edf00) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros Hp MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  step. if_false.
  do 5 step. if_true.
  do 5 step. if_false.
  do 4 step.
  apply evt_done. unfold entry_st, g_read_stage. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma read_err_walk : forall (usp : Z) (gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  stderr_cells m -> mem_inv bsegs m ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0x1ee114) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
                          (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 FMT_read_error) p1 a3 a4 a5 a6 a7 p1 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6 F fc e_fprintf m))
    (MS (mkR (Z_to_bv 64 0x1edf94) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1 (Z_to_bv 64 (-1))
             a1 a2 a3 a4 a5 a6 a7 p1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1edf94) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros [SC1 SC2] MI. unfold GOT_STDERR, STDERR_VAR in SC1, SC2.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  step. if_true.
  do 8 step.
  apply evt_done. unfold entry_st. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma eof_walk : forall (usp : Z) (gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 p1 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  mem_inv bsegs m ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0x1edfac) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
                          (Z_to_bv 64 3) a1 a2 a3 a4 a5 a6 a7 p1 s3 (Z_to_bv 64 3) s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11
                          t3 t4 t5 t6 F fc e_close m))
    (MS (mkR (Z_to_bv 64 0x1edf94) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1 (Z_to_bv 64 0)
             a1 a2 a3 a4 a5 a6 a7 p1 s3 (Z_to_bv 64 3) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1edf94) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  step. if_false.
  step. step. if_false.
  do 3 step.   (* [comment removed for export] *)
  apply evt_done. unfold entry_st. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma read_ok_walk : forall (usp buf len n : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 p1 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  0 < n < 2^63 -> 0 <= buf -> 0 <= len -> buf + len < 2^64 -> mem_inv bsegs m ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0x1edf2c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf)
                          (Z_to_bv 64 (buf + len)) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 n) a3 a4 a5 a6 a7 p1 (Z_to_bv 64 len)
                          s4 s5 (Z_to_bv 64 g_read_stage) (Z_to_bv 64 n) s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memcpy m))
    (MS (mkR (Z_to_bv 64 0x1edf94) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) (Z_to_bv 64 n)
             a1 a2 a3 a4 a5 a6 a7 p1 (Z_to_bv 64 len) s4 s5 (Z_to_bv 64 g_read_stage) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1edf94) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros Hn Hb Hl Hbl MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (ESN : bv_signed (Z_to_bv 64 n) = n) by (rewrite bv_signed_small; lia).
  step. if_false.
  step. step. if_true.
  do 4 step.
  apply evt_done. unfold entry_st.
  replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 buf) + bv_unsigned (Z_to_bv 64 len))) with (Z_to_bv 64 (buf + len))
    by (rewrite !unsigned_lit by lia; reflexivity).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cont_walk : forall (usp buf len n cap : Z) (gp t0 t1 t2 v a1 a2 a3 a4 a5 a6 a7 p1 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  0 < n -> 0 <= len -> len + n < cap -> cap < 2^40 -> mem_inv bsegs m ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0x1edf94) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf)
                          s4 s6 (Z_to_bv 64 (Z.min (cap - (len + n)) 65536)) a3 a4 a5 a6 a7 p1 (Z_to_bv 64 (len + n))
                          s4 (Z_to_bv 64 cap) s6 (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6 F fc e_read m))
    (MS (mkR (Z_to_bv 64 0x1edf2c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) v
             a1 a2 a3 a4 a5 a6 a7 p1 (Z_to_bv 64 len) s4 (Z_to_bv 64 cap) s6 (Z_to_bv 64 n) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1edf2c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros Hn Hl Hc Hcap MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (E1 : bv_unsigned (Z_to_bv 64 (n + len)) = n + len) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 cap) = cap) by (apply unsigned_lit; lia).
  step. step. step. if_false.
  do 5 step. rewrite E1.
  assert (E3 : bv_unsigned (Z_to_bv 64 (cap + - (n + len))) = cap - (n + len)) by (apply unsigned_lit; lia).
  destruct (Z.ltb_spec (cap - (n + len)) 65536) as [LT|GE].
  - if_true. do 3 step.
    apply evt_done. unfold entry_st.
    replace (Z.min (cap - (len + n)) 65536) with (cap + - (n + len)) by lia. replace (len + n) with (n + len) by lia. reflexivity.
  - if_false. do 4 step.
    apply evt_done. unfold entry_st.
    replace (Z.min (cap - (len + n)) 65536) with 65536 by lia. replace (len + n) with (n + len) by lia. reflexivity.
Qed.

Lemma shiftr26_zero_iff' : forall a, 0 <= a -> Z.shiftr a 26 = 0 <-> a < 67108864.
Proof.
  intros a Ha. rewrite Z.shiftr_div_pow2 by lia. change (2^26) with 67108864. split; intros H.
  - destruct (Z.ltb_spec a 67108864); [assumption|]. pose proof (Z.div_le_mono 67108864 a 67108864 ltac:(lia) ltac:(lia)). rewrite Z.div_same in H1 by lia. lia.
  - apply Z.div_small. lia.
Qed.

(* [comment removed for export] *)
Lemma grow_walk : forall (usp buf len n cap : Z) (gp t0 t1 t2 v a1 a2 a3 a4 a5 a6 a7 p1 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  0 < n -> 0 <= len -> len + n = cap -> cap < 2^26 -> mem_inv bsegs m ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0x1edf54) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf)
                          (Z_to_bv 64 (2 * cap)) a1 a2 a3 a4 a5 a6 a7 p1 (Z_to_bv 64 cap)
                          s4 (Z_to_bv 64 (2 * cap)) s6 (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6 F fc e_malloc m))
    (MS (mkR (Z_to_bv 64 0x1edf2c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) v
             a1 a2 a3 a4 a5 a6 a7 p1 (Z_to_bv 64 len) s4 (Z_to_bv 64 cap) s6 (Z_to_bv 64 n) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1edf2c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros Hn Hl Hc Hcap MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (E1 : bv_unsigned (Z_to_bv 64 (n + len)) = n + len) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 cap) = cap) by (apply unsigned_lit; lia).
  assert (E4 : Z.shiftr (n + len) 26 = 0) by (apply shiftr26_zero_iff'; lia).
  step. step. step. if_true.
  step. rewrite E1, E4. step. if_false.
  do 3 step.
  apply evt_done. unfold entry_st. rewrite ?E1.
  replace (Z.shiftl (n + len) 1) with (2 * cap) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (n + len) with cap by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma toobig_walk : forall (usp buf len n : Z) (gp t0 t1 t2 v a1 a2 a3 a4 a5 a6 a7 p1 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  0 < n -> 0 <= len -> len + n = 67108864 -> stderr_cells m -> mem_inv bsegs m ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0x1ee114) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf)
                          (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 FMT_too_big) (Z_to_bv 64 67108864) a3 a4 a5 a6 a7 p1
                          (Z_to_bv 64 67108864) s4 (Z_to_bv 64 67108864) s6 (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6
                          F fc e_fprintf m))
    (MS (mkR (Z_to_bv 64 0x1edf2c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) v
             a1 a2 a3 a4 a5 a6 a7 p1 (Z_to_bv 64 len) s4 (Z_to_bv 64 67108864) s6 (Z_to_bv 64 n) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1edf2c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros Hn Hl Hc [SC1 SC2] MI. unfold GOT_STDERR, STDERR_VAR in SC1, SC2.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (E1 : n + len = 67108864) by lia. 
  step. rewrite E1. step. step. if_true.
  step. step. if_true.
  do 7 step.
  apply evt_done. unfold entry_st. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grow_ret_walk1 : forall (usp buf cap nb : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 p1 s1 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  0 < nb < 2^64 -> 0 < cap < 2^64 -> mem_inv bsegs m ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0x1edf70) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 nb)
                          (Z_to_bv 64 nb) (Z_to_bv 64 buf) (Z_to_bv 64 cap) a3 a4 a5 a6 a7 p1
                          (Z_to_bv 64 cap) s4 s5 s6 (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memcpy m))
    (MS (mkR (Z_to_bv 64 0x1edf54) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1 (Z_to_bv 64 nb)
             a1 a2 a3 a4 a5 a6 a7 p1 (Z_to_bv 64 cap) s4 s5 s6 (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1edf54) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros Hnb Hcap MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (E1 : bv_unsigned (Z_to_bv 64 nb) = nb) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 cap) = cap) by (apply unsigned_lit; lia).
  step. if_false. step. step. if_false.
  do 4 step.
  apply evt_done. unfold entry_st. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grow_ret_walk2 : forall (usp buf : Z) (gp t0 t1 t2 v a1 a2 a3 a4 a5 a6 a7 p1 s1 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  mem_inv bsegs m ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0x1edf78) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
                          (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 p1
                          s3 s4 s5 s6 (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m))
    (MS (mkR (Z_to_bv 64 0x1edf70) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1 v
             a1 a2 a3 a4 a5 a6 a7 p1 s3 s4 s5 s6 (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1edf70) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  do 2 step.
  apply evt_done. unfold entry_st. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grow_ret_walk3 : forall (usp nb cap : Z) (gp t0 t1 t2 v a1 a2 a3 a4 a5 a6 a7 p1 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : word -> option byte),
  65536 <= cap < 2^40 -> mem_inv bsegs m ->
  evt bsegs (eq (entry_st (Z_to_bv 64 0x1edf94) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 nb)
                          s4 s6 (Z_to_bv 64 (Z.min (2 * cap - cap) 65536)) a3 a4 a5 a6 a7 p1 (Z_to_bv 64 cap)
                          s4 (Z_to_bv 64 (2 * cap)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_read m))
    (MS (mkR (Z_to_bv 64 0x1edf78) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 nb) v
             a1 a2 a3 a4 a5 a6 a7 p1 (Z_to_bv 64 cap) s4 (Z_to_bv 64 (2 * cap)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1edf78) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros Hcap MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (E1 : bv_unsigned (Z_to_bv 64 cap) = cap) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 (2 * cap)) = 2 * cap) by (apply unsigned_lit; lia).
  do 3 step. rewrite ?E1, ?E2.
  assert (E3 : bv_unsigned (Z_to_bv 64 (2 * cap + - cap)) = cap) by (rewrite unsigned_lit by lia; lia).
  if_false. do 4 step.
  apply evt_done. unfold entry_st.
  replace (Z.min (2 * cap - cap) 65536) with 65536 by lia. reflexivity.
Qed.
