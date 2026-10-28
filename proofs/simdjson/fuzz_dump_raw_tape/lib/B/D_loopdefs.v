(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_auxv D_libiface D_clx D_rlkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition cap_ok (cap : Z) : Prop := exists k : nat, (k <= 10)%nat /\ cap = 65536 * 2 ^ Z.of_nat k.

Lemma cap_ok_range : forall cap, cap_ok cap -> 65536 <= cap <= 67108864.
Proof.
  intros cap (k & Hk & ->). split.
  - pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)). lia.
  - assert (2 ^ Z.of_nat k <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). change (2 ^ 10) with 1024 in H. lia.
Qed.

Lemma cap_ok_double : forall cap, cap_ok cap -> cap < 67108864 -> cap_ok (2 * cap).
Proof.
  intros cap (k & Hk & ->) Hlt. exists (S k). split.
  - destruct (Nat.eq_dec k 10) as [E|E]; [subst k; change (2 ^ Z.of_nat 10) with 1024 in Hlt; lia| lia].
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma cap_ok_top : forall cap, cap_ok cap -> 67108864 <= cap -> cap = 67108864.
Proof. intros cap H1 H2. pose proof (cap_ok_range cap H1). lia. Qed.

Section LoopDefs.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Variable data : list byte.

Definition FD (len : Z) : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) (FdFile (path_b argvb) (Z_to_bv 64 len)).

Definition LOOPS (Σ : rts RT) (usp buf cap : Z) : Prop :=
  rt_live RT Σ = [(buf, cap)] /\ rt_frames RT Σ = [] /\ CREDIT_DRV - 37 * cap <= rt_credit RT Σ /\ usp <= rt_sp0 RT Σ <= usp + 48.

Definition DCTX (Σ : rts RT) (usp ap path : Z) (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem) : Prop :=
  MAINCTX RT OUT_rep ERR_rep XENV LIB argvb Σ stdout_init usp ap c0 c1 c2 c3 c4 c5 c6 c7 m
  /\ bytes_at bsegs m path (path_b argvb ++ [Z_to_bv 8 0]) /\ ap < path
  /\ path + Z.of_nat (length (path_b argvb)) + 1 <= USTACK_TOP - 16 /\ 0x7fff80000000 <= rt_sp0 RT Σ.

Definition RL (len cap : Z) (c : config) : Prop :=
  exists (Σ : rts RT) (usp ap path buf : Z) (gp t0 t1 t2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    frm0 fc /\ ASTA RT Σ (PMfd (FD len) fs)
      (eq (entry_st (Z_to_bv 64 0xae8b4) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf)
             (Z_to_bv 64 3) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 (Z.min (cap - len) 65536)) a3 a4 a5 a6 a7
             (Z_to_bv 64 path) (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 g_read_stage) s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc e_read m)) c
    /\ DCTX Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m /\ LOOPS Σ usp buf cap
    /\ bytes_at bsegs m buf (firstn (Z.to_nat len) data)
    /\ 0 <= len < cap /\ len <= Z.of_nat (length data) /\ cap_ok cap.

Definition RMEM (len cap : Z) (c : config) : Prop :=
  exists (Σ : rts RT) (usp ap path buf n : Z) (gp t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    frm0 fc /\ ASTA RT Σ (PMfd (FD (len + n)) fs)
      (eq (entry_st (Z_to_bv 64 0xae84c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf)
             (Z_to_bv 64 (buf + len)) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             (Z_to_bv 64 path) (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 n)
             s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memcpy m)) c
    /\ DCTX Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m /\ LOOPS Σ usp buf cap
    /\ bytes_at bsegs m buf (firstn (Z.to_nat len) data)
    /\ bytes_at bsegs m g_read_stage (firstn (Z.to_nat n) (skipn (Z.to_nat len) data))
    /\ 0 < n <= 65536 /\ 0 <= len /\ len + n <= cap /\ len + n <= Z.of_nat (length data) /\ cap_ok cap.

Definition RGROW (len cap : Z) (c : config) : Prop :=
  exists (Σ : rts RT) (usp ap path buf : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    frm0 fc /\ ASTA RT Σ (PMfd (FD cap) fs)
      (eq (entry_st (Z_to_bv 64 0xae874) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf)
             (Z_to_bv 64 (2 * cap)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 path) (Z_to_bv 64 cap) (Z_to_bv 64 3) (Z_to_bv 64 (2 * cap)) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf)
             s8 s9 s10 s11 t3 t4 t5 t6 F fc e_malloc m)) c
    /\ DCTX Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m /\ LOOPS Σ usp buf cap
    /\ bytes_at bsegs m buf (firstn (Z.to_nat cap) data)
    /\ 0 <= len < cap /\ cap <= Z.of_nat (length data) /\ cap < 67108864 /\ cap_ok cap.

Definition RDONE (c : config) : Prop :=
  exists (Σ : rts RT) (usp ap path buf cap : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    frm0 fc /\ ASTA RT Σ (PMfd (FD (Z.of_nat (length data))) fs)
      (eq (entry_st (Z_to_bv 64 0xae8c8) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf)
             (Z_to_bv 64 3) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) (Z_to_bv 64 (Z.of_nat (length data))) (Z_to_bv 64 3)
             (Z_to_bv 64 cap) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6 F fc e_close m)) c
    /\ DCTX Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m /\ LOOPS Σ usp buf cap
    /\ bytes_at bsegs m buf data /\ Z.of_nat (length data) < cap /\ cap_ok cap.

Definition RTOOBIG (c : config) : Prop :=
  exists (Σ : rts RT) (usp ap path buf : Z) (gp t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    frm0 fc /\ ASTA RT Σ (PMfd (FD 67108864) fs)
      (eq (entry_st (Z_to_bv 64 0xaea30) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf)
             (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 FMT_too_big) (Z_to_bv 64 67108864) a3 a4 a5 a6 a7 (Z_to_bv 64 path)
             (Z_to_bv 64 67108864) (Z_to_bv 64 3) (Z_to_bv 64 67108864) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf)
             s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fprintf m)) c
    /\ DCTX Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m /\ LOOPS Σ usp buf 67108864 /\ 67108864 <= Z.of_nat (length data).

End LoopDefs.

Section DTransport.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Hypothesis AF : art_facts RT.

Lemma DCTX_agree : forall Σ Σ' usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m m',
  DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m ->
  ART RT Σ' m' -> mem_inv bsegs m' -> wmono bsegs m m' -> stk bsegs m' (rt_sp0 RT Σ - STACK_WIN) (usp - 80) ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> CLX OUT_rep ERR_rep XENV LIB stdout_init m' ->
  agree_on (fun x => usp - 80 <= x < USTACK_TOP) m m' -> agree_on auxc m m' ->
  DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ' usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m'.
Proof using AF.
  intros Σ Σ' usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m m' (HC & HB & Hap & Hhi & SPW) ART1 MI1 WM ST1 ESP CLX1 AG AGC.
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & UA & _).
  split; [exact (MAINCTX_agree RT OUT_rep ERR_rep XENV LIB argvb AF Σ Σ' _ _ usp ap c0 c1 c2 c3 c4 c5 c6 c7 m m' HC ART1 MI1 WM ST1 ESP CLX1 AG AGC)|].
  split; [apply (path_agree m m' usp path); [exact HB| lia| rewrite length_app; cbn [length]; unfold USTACK_TOP in *; lia| exact AG]|].
  rewrite ESP. tauto.
Qed.

Lemma DCTX_agree_nw : forall Σ Σ' usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m m',
  DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m ->
  ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (rt_sp0 RT Σ - STACK_WIN) (usp - 80) ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> CLX OUT_rep ERR_rep XENV LIB stdout_init m' ->
  agree_on (fun x => usp - 80 <= x < USTACK_TOP) m m' -> agree_on auxc m m' ->
  DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ' usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m'.
Proof using AF.
  intros Σ Σ' usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m m' (HC & HB & Hap & Hhi & SPW) ART1 MI1 ST1 ESP CLX1 AG AGC.
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & UA & _).
  split; [exact (MAINCTX_agree_nw RT OUT_rep ERR_rep XENV LIB argvb AF Σ Σ' _ _ usp ap c0 c1 c2 c3 c4 c5 c6 c7 m m' HC ART1 MI1 ST1 ESP CLX1 AG AGC)|].
  split; [apply (path_agree m m' usp path); [exact HB| lia| rewrite length_app; cbn [length]; unfold USTACK_TOP in *; lia| exact AG]|].
  rewrite ESP. tauto.
Qed.

End DTransport.
