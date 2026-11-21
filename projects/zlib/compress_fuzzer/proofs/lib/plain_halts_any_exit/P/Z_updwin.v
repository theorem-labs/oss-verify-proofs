(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_pure2 Z_updwin_pure Zh_kit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface InflateState RefUpdWin1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition Z_UPDATEWINDOW : Z := 0x1ef88.
Definition PC_UW_BODY : Z := 0x1efe0.
Definition PC_UW_RET : Z := 0x1efd8.

Definition updwin_post (L : ilay) (s' : inflate_state) (rc : Z) (lo : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (W : list ivl) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz rc) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch W m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp) /\ isA m' L s' /\ iwin m' L s'.
Definition PC_UW_COPY : Z := 0x1efec.

Definition PC_MALLOC : Z := 0x20b28.

Definition uw_at_malloc (L : ilay) (copy E lo : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (wz PC_UW_RET) (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz E) (wz copy) (wz 32768) a1 a2 a3 a4 a5 a6 a7
                  (wz 1) (wz (il_As L)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz PC_MALLOC) fc None m' (seg_rom psegs)
    /\ rw_cells psegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk psegs m' lo (bv_unsigned sp + -48)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'.

Lemma updwin_to_malloc : forall (L : ilay) (s : inflate_state) (c : icall) (copy E lo : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk psegs m lo (bv_unsigned sp) -> izs m L c ->
  isA m L s -> is_window_blk s = None -> is_wbits s = 15 ->
  lo <= bv_unsigned sp - 64 -> 0x5c000 <= lo -> bv_unsigned sp <= il_S L -> il_S L + 112 < 2^63 ->
  0 < il_As L -> il_As L + 7176 <= lo ->
  mem_inv psegs m ->
  evt psegs (uw_at_malloc L copy E lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (il_S L)) (wz E) (wz copy) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_UPDATEWINDOW) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros STK ZS GA HB Hwb LO1 LO2 SPS S63 As0 As1 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  open_isA GA. open_izs ZS.
  unfold Z_UPDATEWINDOW. carve_frame 48%nat STK.
  do 12 zs. rewrite HB. cbn [win_addr]. zs. br_false.
  zs. rewrite Hwb. do 6 zs. do 4 zs.
  apply evt_done. unfold uw_at_malloc. do 15 eexists. split; [reflexivity|].
  split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma updwin_ret_null : forall (L : ilay) (s : inflate_state) (copy E lo : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells psegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk psegs m lo (bv_unsigned sp + -48) ->
  isA m L s -> is_window_blk s = None ->
  lo <= bv_unsigned sp - 64 -> 0x5c000 <= lo -> bv_unsigned sp < 2^63 -> 0 < il_As L -> il_As L + 7176 <= lo ->
  mem_inv psegs m ->
  evt psegs (updwin_post L s 1 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(lo, bv_unsigned sp); (il_As L, il_As L + 168)] m)
    (MS (mkR x1 (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz E) (wz copy) (wz 0) a1 a2 a3 a4 a5 a6 a7 (wz 1) (wz (il_As L)) s4
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PC_UW_RET) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros FR STK GA HB LO1 LO2 SP63 As0 As1 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp); (il_As L, il_As L + 168)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  open_isA GA. rewrite HB in GA. cbn [win_addr] in GA.
  unfold PC_UW_RET. zs. zs. br_true. do 8 zs. release_frame FR STK (bv_unsigned sp). zs.
  apply evt_done. unfold updwin_post. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  split; [exact STK|]. split; [unfold isA, isA_cells; rewrite HB; cbn [win_addr]; exact GA|].
  unfold iwin; rewrite HB; exact I.
Qed.

Definition il_setw (L : ilay) (A : Z) : ilay := mkIL (il_S L) (il_As L) A (il_NI L) (il_NO L).

Definition s_fresh (s : inflate_state) (wb : ZProg.blk) (junk : list byte) : inflate_state :=
  iset_window (iset_window_blk s (Some wb)) (iarr_u8_of (gwb junk) 0 32768).

