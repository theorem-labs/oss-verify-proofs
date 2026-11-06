(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs.StoreFast.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl Ubsan_chk ImgFacts.

Module U_large_mul_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs U_long_mul_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition large_mul_entry : Z := 0x271d0.
Definition large_mul_need : Z := 1248.

Definition large_mul_W (sp A : Z) : list ivl := [(sp - 1248, sp); (A, A + 498)]%Z.

Definition large_mul_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A : Z) (ws : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch (large_mul_W (bv_unsigned sp) A) m m'
    /\ wmono USEGS m m'
    /\ stk USEGS m' (bv_unsigned sp - 1248) (bv_unsigned sp)
    /\ u64arr USEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells USEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (0 <= len' <= 62)%Z
    /\ bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) * 5 ^ 135)%Z
    /\ bnorm ws' (Z.to_nat len')
    /\ pristine m' 0x10000 0x22000.

Definition large_mul_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    stk USEGS m (bv_unsigned sp - 1248) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (0x22000 <= bv_unsigned sp - 1248)%Z ->
    pristine m 0x10000 0x22000 ->
    u64arr USEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells USEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> (bv_unsigned a0 mod 8 = 0)%Z -> (0 < bv_unsigned a0)%Z ->
    bnorm ws (Z.to_nat len) ->
    a1 = Z_to_bv 64 U_LARGE_POW5_ADDR -> a2 = Z_to_bv 64 5 ->
    (bval ws (Z.to_nat len) * 5 ^ 135 < BIG_CAP)%Z ->
    (bv_unsigned a0 + 498 <= bv_unsigned sp - 1248 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    evt USEGS (large_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) ws len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x271d0) fc None m (seg_rom USEGS)).
End U_large_mul_stmt.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_pow5_stmt.

Module U_pow5_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs.StoreFast.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl Ubsan_chk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation USEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section usmulM.
  Variables (x1 x2 x3 x4 x8 x9 x10 x12 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (A y : Z) (ws : list word) (len : Z).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis Hy : (0 <= y < 2 ^ 64)%Z.
  Hypothesis HA : (0 < A /\ A + 498 <= 2 ^ 64)%Z.

  Definition usmulM_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (c' : Z) (tl tlo tcnt tsum : word) (m' : word -> option byte) (cur : list word),
      ms' = MS (mkR x1 x2 x3 x4 (Z_to_bv 64 (A + 8 * len)) tl tlo x8 x9 x10 (Z_to_bv 64 y) x12 (Z_to_bv 64 63) x14 (Z_to_bv 64 len) (Z_to_bv 64 c') tcnt x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 tsum x29 x30 x31)
               F (Z_to_bv 64 0x270ec) fc None m' (seg_rom USEGS)
      /\ munch [(A, A + 8 * len)]%Z m m'
      /\ wmono USEGS m m'
      /\ u64arr USEGS m' A cur
      /\ length cur = 62%nat
      /\ smul_inv ws cur y (Z.to_nat len) c'.

  Definition usmulM_ok (k : nat) : Prop :=
    forall (i : nat) (p tl tlo tsum : word) (c : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      u64arr USEGS m A cur -> length cur = 62%nat ->
      smul_inv ws cur y i c ->
      munch [(A, A + 8 * len)]%Z m0 m -> wmono USEGS m0 m ->
      evt USEGS (usmulM_post m0)
        (MS (mkR x1 x2 x3 x4 p tl tlo x8 x9 x10 (Z_to_bv 64 y) x12 (Z_to_bv 64 63) x14 (Z_to_bv 64 len) (Z_to_bv 64 c) (Z_to_bv 64 (63 - Z.of_nat i)) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 tsum x29 x30 x31)
            F (Z_to_bv 64 0x270bc) fc None m (seg_rom USEGS)).

  #[using="L62 LEN Hy HA"] Lemma usmulM_body : forall k, usmulM_ok k -> usmulM_ok (S k).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold usmulM_ok. intros i p tl tlo tsum c cur m Hk Hi Hp CUR Hcur INV MU WM.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    destruct INV as (Hv & Hag & Hc & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    step. (* [comment removed for export] *)
    kill_check.
    pose proof (u64arr_read USEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit y), ?(unsigned_lit c) by lia.
    pose proof (u64arr_store_ok USEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write USEGS m A cur (Z.of_nat i) (Z_to_bv 64 (bv_unsigned w * y + c)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit y), ?(unsigned_lit c) by lia.
    rewrite ?(lm_smul_carry_word (bv_unsigned w) y c), ?(lm_smul_carry_word' (bv_unsigned w) y c) by lia.
    step. (* [comment removed for export] *)
    assert (INV' : smul_inv ws (upd cur i (Z_to_bv 64 (bv_unsigned w * y + c))) y (S i) (mul_cout (limbZ ws i) y c)).
    { replace (bv_unsigned w * y)%Z with (limbZ ws i * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply smul_inv_step; [split; [exact Hv| split; [exact Hag| split; [exact Hc| exact Hlc]]] | lia | rewrite L62; lia |].
      unfold limbZ. rewrite <- Hw. apply lm_smul_lo_word; lia. }
    replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
    step. (* [comment removed for export] *)
    if_cases Hb.
    - cond_cleanup Hb.
      replace (63 - Z.of_nat i + -1)%Z with (63 - Z.of_nat (S i))%Z by lia.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8))).
      all: try eassumption; try lia.
      all: first [rewrite unsigned_lit by lia; lia | rewrite upd_length; exact Hcur].
    - cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      apply evt_done. unfold usmulM_post.
      eexists (mul_cout (limbZ ws i) y c), _, _, _, _, m1, (upd cur i (Z_to_bv 64 (limbZ ws i * y + c))).
      split. { f_equal. replace (bv_unsigned p + 8)%Z with (A + 8 * len)%Z by lia. reflexivity. }
      split; [exact MU|]. split; [exact WM|].
      split. { replace (limbZ ws i) with (bv_unsigned w) by (unfold limbZ; rewrite <- Hw; reflexivity). exact CUR'. }
      split; [rewrite upd_length; exact Hcur|].
      rewrite <- Hil. replace (limbZ ws i * y)%Z with (bv_unsigned w * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity). exact INV'.
  Qed.

  #[using="L62 LEN Hy HA"] Lemma usmulM_loop : forall k, usmulM_ok k.
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0). induction k as [|k IH]. - unfold usmulM_ok; intros; exfalso; lia. - apply usmulM_body; exact IH. Qed.

  #[using="L62 LEN Hy HA"] Lemma usmulM_run : forall (p tl tlo tsum : word) (cur : list word),
    bv_unsigned p = A ->
    u64arr USEGS m0 A cur -> length cur = 62%nat -> (forall j, nth j cur w0 = nth j ws w0) ->
    evt USEGS (usmulM_post m0)
      (MS (mkR x1 x2 x3 x4 p tl tlo x8 x9 x10 (Z_to_bv 64 y) x12 (Z_to_bv 64 63) x14 (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 63) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 tsum x29 x30 x31)
          F (Z_to_bv 64 0x270bc) fc None m0 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0).
    intros p tl tlo tsum cur Hp CUR Hcur Hag.
    replace (Z_to_bv 64 63) with (Z_to_bv 64 (63 - Z.of_nat 0)) at 2 by (f_equal; lia).
    eapply (usmulM_loop (Z.to_nat len) 0%nat); try eassumption; try lia.
    - split; [cbn; lia|]. split; [intros; apply Hag|]. split; [lia|]. rewrite Hcur, L62. reflexivity.
    - apply munch_refl.
    - apply wmono_refl.
  Qed.
End usmulM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section usmulF.
  Variables (x1 x2 x3 x4 x7 x8 x9 x10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (A y : Z) (ws : list word) (len : Z).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis Hy : (0 <= y < 2 ^ 64)%Z.
  Hypothesis HA : (0 < A /\ A + 498 <= 2 ^ 64)%Z.

  Definition usmulF_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (c' : Z) (tl tlo tcnt tsum : word) (m' : word -> option byte) (cur : list word),
      ms' = MS (mkR x1 x2 x3 x4 tlo tsum x7 x8 x9 x10 (Z_to_bv 64 len) (Z_to_bv 64 c') (Z_to_bv 64 y) (Z_to_bv 64 63) (Z_to_bv 64 (A + 8 * len)) tcnt tl x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x27180) fc None m' (seg_rom USEGS)
      /\ munch [(A, A + 8 * len)]%Z m m'
      /\ wmono USEGS m m'
      /\ u64arr USEGS m' A cur
      /\ length cur = 62%nat
      /\ smul_inv ws cur y (Z.to_nat len) c'.

  Definition usmulF_ok (k : nat) : Prop :=
    forall (i : nat) (p tl tlo tsum : word) (c : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      u64arr USEGS m A cur -> length cur = 62%nat ->
      smul_inv ws cur y i c ->
      munch [(A, A + 8 * len)]%Z m0 m -> wmono USEGS m0 m ->
      evt USEGS (usmulF_post m0)
        (MS (mkR x1 x2 x3 x4 tlo tsum x7 x8 x9 x10 (Z_to_bv 64 len) (Z_to_bv 64 c) (Z_to_bv 64 y) (Z_to_bv 64 63) p (Z_to_bv 64 (63 - Z.of_nat i)) tl x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x27150) fc None m (seg_rom USEGS)).

  #[using="L62 LEN Hy HA"] Lemma usmulF_body : forall k, usmulF_ok k -> usmulF_ok (S k).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold usmulF_ok. intros i p tl tlo tsum c cur m Hk Hi Hp CUR Hcur INV MU WM.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    destruct INV as (Hv & Hag & Hc & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    step. (* [comment removed for export] *)
    kill_check.
    pose proof (u64arr_read USEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit y), ?(unsigned_lit c) by lia.
    pose proof (u64arr_store_ok USEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write USEGS m A cur (Z.of_nat i) (Z_to_bv 64 (bv_unsigned w * y + c)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit y), ?(unsigned_lit c) by lia.
    rewrite ?(lm_smul_carry_word (bv_unsigned w) y c), ?(lm_smul_carry_word' (bv_unsigned w) y c) by lia.
    step. (* [comment removed for export] *)
    assert (INV' : smul_inv ws (upd cur i (Z_to_bv 64 (bv_unsigned w * y + c))) y (S i) (mul_cout (limbZ ws i) y c)).
    { replace (bv_unsigned w * y)%Z with (limbZ ws i * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply smul_inv_step; [split; [exact Hv| split; [exact Hag| split; [exact Hc| exact Hlc]]] | lia | rewrite L62; lia |].
      unfold limbZ. rewrite <- Hw. apply lm_smul_lo_word; lia. }
    replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
    step. (* [comment removed for export] *)
    if_cases Hb.
    - cond_cleanup Hb.
      replace (63 - Z.of_nat i + -1)%Z with (63 - Z.of_nat (S i))%Z by lia.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8))).
      all: try eassumption; try lia.
      all: first [rewrite unsigned_lit by lia; lia | rewrite upd_length; exact Hcur].
    - cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      apply evt_done. unfold usmulF_post.
      eexists (mul_cout (limbZ ws i) y c), _, _, _, _, m1, (upd cur i (Z_to_bv 64 (limbZ ws i * y + c))).
      split. { f_equal. replace (bv_unsigned p + 8)%Z with (A + 8 * len)%Z by lia. reflexivity. }
      split; [exact MU|]. split; [exact WM|].
      split. { replace (limbZ ws i) with (bv_unsigned w) by (unfold limbZ; rewrite <- Hw; reflexivity). exact CUR'. }
      split; [rewrite upd_length; exact Hcur|].
      rewrite <- Hil. replace (limbZ ws i * y)%Z with (bv_unsigned w * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity). exact INV'.
  Qed.

  #[using="L62 LEN Hy HA"] Lemma usmulF_loop : forall k, usmulF_ok k.
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0). induction k as [|k IH]. - unfold usmulF_ok; intros; exfalso; lia. - apply usmulF_body; exact IH. Qed.

  #[using="L62 LEN Hy HA"] Lemma usmulF_run : forall (p tl tlo tsum : word) (cur : list word),
    bv_unsigned p = A ->
    u64arr USEGS m0 A cur -> length cur = 62%nat -> (forall j, nth j cur w0 = nth j ws w0) ->
    evt USEGS (usmulF_post m0)
      (MS (mkR x1 x2 x3 x4 tlo tsum x7 x8 x9 x10 (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 y) (Z_to_bv 64 63) p (Z_to_bv 64 63) tl x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x27150) fc None m0 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0).
    intros p tl tlo tsum cur Hp CUR Hcur Hag.
    replace (Z_to_bv 64 63) with (Z_to_bv 64 (63 - Z.of_nat 0)) at 2 by (f_equal; lia).
    eapply (usmulF_loop (Z.to_nat len) 0%nat); try eassumption; try lia.
    - split; [cbn; lia|]. split; [intros; apply Hag|]. split; [lia|]. rewrite Hcur, L62. reflexivity.
    - apply munch_refl.
    - apply wmono_refl.
  Qed.
End usmulF.
End U_pow5_A.


Module U_pow5_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs.StoreFast.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl Ubsan_chk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_pow5_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5.U_large_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5.U_pow5_A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Local Ltac post_call segs m ::=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      let W' := eval hnf in W in change (munch W' m m') in MUc;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Section Loops.
  Hypothesis large_mul_spec : large_mul_stmt.
  Variables (sp va gp tp x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (ws : list word) (len e0 : Z).
  Notation A := (bv_unsigned va).
  Notation SP' := (bv_unsigned sp + -48)%Z.
  Notation X := (bval ws (Z.to_nat len)).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis A8 : (A mod 8 = 0)%Z.
  Hypothesis A0p : (0 < A)%Z.
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SEP : (A + 498 <= bv_unsigned sp - 1296 \/ bv_unsigned sp <= A)%Z.
  Hypothesis SPLO : (0x22000 <= bv_unsigned sp - 1296)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.
  Hypothesis AROD : (A + 498 <= 0x10000 \/ 0x22000 <= A)%Z.
  Hypothesis He0 : (0 <= e0 < 2 ^ 31)%Z.
  Hypothesis CAP : (X * 5 ^ e0 < BIG_CAP)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition big_W : list ivl := [(bv_unsigned sp - 1296, SP'); (A, A + 498)]%Z.

  Definition big_post (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (e' : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
                      (m' : word -> option byte) (wsk : list word) (lenk : Z),
      ms' = MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e') x10 x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 0x15aa8) (Z_to_bv 64 134) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x27088) fc None m' (seg_rom USEGS)
      /\ munch big_W m0 m'
      /\ wmono USEGS m0 m'
      /\ u64arr USEGS m' A wsk /\ length wsk = 62%nat
      /\ rw_cells USEGS m' (A + 496) [C2 (Z_to_bv 64 lenk)] /\ (0 <= lenk <= 62)%Z
      /\ bnorm wsk (Z.to_nat lenk)
      /\ (0 <= e' < 135)%Z /\ (e' <= e0)%Z
      /\ bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e'))%Z
      /\ stk USEGS m' (bv_unsigned sp - 1296) SP'
      /\ pristine m' 0x10000 0x22000.

  Definition big_ok (n : nat) : Prop :=
    forall (m0 : word -> option byte) (e : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m : word -> option byte) (wsk : list word) (lenk : Z),
      (Z.to_nat e <= n)%nat -> (135 <= e <= e0)%Z ->
      u64arr USEGS m A wsk -> length wsk = 62%nat ->
      rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e))%Z ->
      stk USEGS m (bv_unsigned sp - 1296) SP' ->
      pristine m 0x10000 0x22000 ->
      munch big_W m0 m -> wmono USEGS m0 m ->
      evt USEGS (big_post m0)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 0x15aa8) (Z_to_bv 64 134) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2706c) fc None m (seg_rom USEGS)).

  #[using="large_mul_spec L62 A8 A0p AL SEP SPLO Rsp AROD He0 CAP"] Lemma big_body : forall n, big_ok n -> big_ok (S n).
  Proof. LiaFast.lf_pins (fun (large_mul_spec L62 A8 A0p AL SEP SPLO Rsp AROD He0 CAP : LiaFast.U) => LiaFast.u0).
    intros n IH. unfold big_ok.
    intros m0 e x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m wsk lenk Hn He XA Lx LENC Hlenk BN VAL ST PR MU WM.
    cbv delta [big_W] in MU.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit SP' ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    call large_mul_spec.
    1:{ rewrite ULs. replace (SP' - 1248)%Z with (bv_unsigned sp - 1296)%Z by lia. exact ST. }
    1:{ rewrite ULs. Z.div_mod_to_equations. lia. }
    1:{ rewrite ULs. lia. }
    1:{ exact PR. } 1:{ exact XA. } 1:{ exact Lx. } 1:{ exact LENC. } 1:{ exact Hlenk. } 1:{ exact A8. } 1:{ exact A0p. } 1:{ exact BN. }
    1:{ reflexivity. } 1:{ reflexivity. }
    1:{ rewrite VAL. rewrite (pow5_step_val X e0 e 135) by lia. apply (cap_pow5_mono X _ e0); lia. }
    1:{ rewrite ULs. lia. }
    rewrite ?ULs in *.
    step. (* [comment removed for export] *)
    if_not_taken.
    zstep. (* [comment removed for export] *)
    rewrite swrap32_small by lia.
    step. (* [comment removed for export] *)
    if_cases Hmore.
    - cond_cleanup Hmore.
      replace (SP' - 1248)%Z with (bv_unsigned sp - 1296)%Z in * by lia.
      eapply (IH m0 (e + -135)%Z); try eassumption; try lia.
      all: lazymatch goal with
           | |- bval _ _ = _ => match goal with H : bval ?a ?b = (bval ?c ?d * 5 ^ 135)%Z |- _ => rewrite H end;
                                rewrite VAL; rewrite (pow5_step_val X e0 e 135) by lia; repeat f_equal; try lia
           | |- munch _ _ _ => cbv delta [big_W]; assumption
           | |- stk _ _ _ _ => assumption
           end.
    - cond_cleanup Hmore.
      apply evt_done. unfold big_post.
      exists (e + -135)%Z. do 16 eexists. eexists _, _, _.
      split; [reflexivity|].
      split. { cbv delta [big_W]. assumption. } split. { assumption. }
      split. { eassumption. } split. { assumption. } split. { eassumption. } split. { lia. }
      split. { assumption. } split. { lia. } split. { lia. }
      split. { match goal with H : bval ?a ?b = (bval ?c ?d * 5 ^ 135)%Z |- _ => rewrite H end.
               rewrite VAL. rewrite (pow5_step_val X e0 e 135) by lia. reflexivity. }
      split. { replace (SP' - 1248)%Z with (bv_unsigned sp - 1296)%Z in * by lia. assumption. }
      assumption.
  Qed.

  #[using="large_mul_spec L62 A8 A0p AL SEP SPLO Rsp AROD He0 CAP"] Lemma big_loop : forall n, big_ok n.
  Proof. LiaFast.lf_pins (fun (large_mul_spec L62 A8 A0p AL SEP SPLO Rsp AROD He0 CAP : LiaFast.U) => LiaFast.u0). induction n as [|n IHn]. - unfold big_ok; intros; exfalso; lia. - apply big_body; exact IHn. Qed.

  #[using="large_mul_spec L62 A8 A0p AL SEP SPLO Rsp AROD He0 CAP"] Lemma big_run : forall (e : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m : word -> option byte) (wsk : list word) (lenk : Z),
      (135 <= e <= e0)%Z ->
      u64arr USEGS m A wsk -> length wsk = 62%nat ->
      rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e))%Z ->
      stk USEGS m (bv_unsigned sp - 1296) SP' ->
      pristine m 0x10000 0x22000 ->
      evt USEGS (big_post m)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 0x15aa8) (Z_to_bv 64 134) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2706c) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (large_mul_spec L62 A8 A0p AL SEP SPLO Rsp AROD He0 CAP : LiaFast.U) => LiaFast.u0).
    intros. eapply (big_loop (Z.to_nat e) m e); try eassumption; try lia.
    - cbv delta [big_W]. apply munch_refl. - apply wmono_refl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mid_post (x1 x18 x19 x29 x30 x31 wn : word) (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (e' : Z) (x5 x6 x7 x15 x16 x17 x28 : word)
                      (m' : word -> option byte) (wsk : list word) (lenk : Z),
      ms' = MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e') wn (Z_to_bv 64 POW5_27) (Z_to_bv 64 26) (Z_to_bv 64 63) (Z_to_bv 64 61) x15 x16 x17
                   x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x27114) fc None m' (seg_rom USEGS)
      /\ munch [(A, A + 498)]%Z m0 m'
      /\ wmono USEGS m0 m'
      /\ u64arr USEGS m' A wsk /\ length wsk = 62%nat
      /\ rw_cells USEGS m' (A + 496) [C2 (Z_to_bv 64 lenk)] /\ (0 <= lenk <= 62)%Z
      /\ bnorm wsk (Z.to_nat lenk)
      /\ (0 <= e' < 27)%Z /\ (e' <= e0)%Z
      /\ bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e'))%Z.

  Definition mid_ok (x1 x18 x19 x29 x30 x31 wn : word) (m0 : word -> option byte) (n : nat) : Prop :=
    forall (e : Z) (x5 x6 x7 x15 x16 x17 x28 : word) (m : word -> option byte) (wsk : list word) (lenk : Z),
      (Z.to_nat e <= n)%nat -> (27 <= e <= e0)%Z ->
      u64arr USEGS m A wsk -> length wsk = 62%nat ->
      rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e))%Z ->
      munch [(A, A + 498)]%Z m0 m -> wmono USEGS m0 m ->
      evt USEGS (mid_post x1 x18 x19 x29 x30 x31 wn m0)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e) wn (Z_to_bv 64 POW5_27) (Z_to_bv 64 26) (Z_to_bv 64 63) (Z_to_bv 64 61) x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x270a8) fc None m (seg_rom USEGS)).

  #[using="L62 A8 A0p AL SPLO HA He0 CAP"] Lemma mid_body : forall x1 x18 x19 x29 x30 x31 wn m0 n,
    (bv_unsigned wn = 2 ^ 64 - 1 - A)%Z ->
    mid_ok x1 x18 x19 x29 x30 x31 wn m0 n -> mid_ok x1 x18 x19 x29 x30 x31 wn m0 (S n).
  Proof. LiaFast.lf_pins (fun (L62 A8 A0p AL SPLO HA He0 CAP : LiaFast.U) => LiaFast.u0).
    clear Rsp AROD. (* [comment removed for export] *)
    intros x1 x18 x19 x29 x30 x31 wn m0 n Hwn IH. unfold mid_ok.
    intros e x5 x6 x7 x15 x16 x17 x28 m wsk lenk Hn He XA Lx LENC Hlenk BN VAL MU WM.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    assert (P27 : (0 < 5 ^ 27)%Z) by (apply Z.pow_pos_nonneg; lia).
    assert (CAPs : (X * 5 ^ (e0 - e) * 5 ^ 27 < BIG_CAP)%Z).
    { rewrite (pow5_step_val X e0 e 27) by lia. apply (cap_pow5_mono X _ e0); lia. }
    step. (* [comment removed for export] *)
    rewrite zx16_lit_small by lia.
    step. (* [comment removed for export] *)
    if_cases Hl0.
    - (* [comment removed for export] *)
      cond_cleanup Hl0.
      zstep. (* [comment removed for export] *)
      rewrite swrap32_small by lia.
      assert (XZ : X = 0%Z).
      { apply (mul_pow5_zero X (e0 - e)); [lia|]. rewrite <- VAL, Hl0. reflexivity. }
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore.
        eapply (IH (e + -27)%Z); try eassumption; try lia.
        all: rewrite Hl0 in *; change (Z.to_nat 0) with 0%nat in *; rewrite bval_0 in *; rewrite XZ; ring.
      + cond_cleanup Hmore.
        apply evt_done. unfold mid_post. exists (e + -27)%Z. do 7 eexists. eexists _, wsk, lenk.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact XA|]. split; [exact Lx|].
        split; [exact LENC|]. split; [lia|]. split; [exact BN|]. split; [lia|]. split; [lia|].
        first [lia | rewrite Hl0 in *; change (Z.to_nat 0) with 0%nat in *; rewrite bval_0 in *; rewrite XZ; ring].
    - cond_cleanup Hl0.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      name_mem mc.
      call (@usmulM_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               F fc mc A POW5_27 wsk lenk Lx ltac:(lia) ltac:(unfold POW5_27; lia) (conj A0p (proj2 HA)) va).
      all: try lia.
      1:{ exact XA. } 1:{ exact Lx. } 1:{ intros j; reflexivity. }
      match goal with H : smul_inv _ _ _ _ ?c |- _ => rename H into INV; rename c into c' end.
      match goal with H : u64arr USEGS _ A ?cu |- _ => rename H into CUR; rename cu into cur end.
      pose proof INV as (Hv & Hag & Hc' & Hlc).
      assert (CAPy : (POW5_27 * bval wsk (Z.to_nat lenk) < BIG_CAP)%Z).
      { rewrite VAL, POW5_27_eq. rewrite Z.mul_comm. exact CAPs. }
      step. (* [comment removed for export] *)
      if_cases Hcz.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        zstep. (* [comment removed for export] *)
        rewrite swrap32_small by lia.
        assert (VAL' : bval cur (Z.to_nat lenk) = (X * 5 ^ (e0 - (e - 27)))%Z).
        { rewrite (smul_inv_finish_nocarry wsk cur POW5_27 (Z.to_nat lenk)) by (rewrite <- Hcz; exact INV).
          rewrite VAL, POW5_27_eq, <- (pow5_step_val X e0 e 27) by lia. ring. }
        assert (BN' : bnorm cur (Z.to_nat lenk)).
        { apply bnorm_of_value; [lia|].
          pose proof (bnorm_lower wsk (Z.to_nat lenk) BN ltac:(lia)) as LO.
          rewrite (smul_inv_finish_nocarry wsk cur POW5_27 (Z.to_nat lenk)) by (rewrite <- Hcz; exact INV).
          unfold POW5_27. nia. }
        step. (* [comment removed for export] *)
        if_cases Hmore.
        * cond_cleanup Hmore.
          eapply (IH (e + -27)%Z); try eassumption; try lia.
          all: rewrite VAL'; repeat f_equal; try lia.
        * cond_cleanup Hmore.
          apply evt_done. unfold mid_post. exists (e + -27)%Z. do 7 eexists. eexists _, cur, lenk.
          split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact CUR|]. split; [assumption|].
          split; [eassumption|]. split; [lia|]. split; [exact BN'|]. split; [lia|]. split; [lia|].
          rewrite VAL'; repeat f_equal; try lia.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        pose proof (smul_carry_room wsk _ _ _ _ INV ltac:(lia) CAPy) as ROOM.
        step. (* [comment removed for export] *)
        if_not_taken.
        zstep. (* [comment removed for export] *)
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
        step. (* [comment removed for export] *)
        if_cases Hck. { cond_cleanup Hck. exfalso. clear -Hck Hwn HA Hlenk ROOM. lia. } clear Hck.
        zstep. (* [comment removed for export] *)
        replace (A + lenk * 8)%Z with (A + 8 * lenk)%Z by lia.
        zstep. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          pose proof (u64arr_store_ok USEGS m1 _ _ lenk (Z_to_bv 64 (A + 8 * lenk)) CUR ltac:(rewrite Hlc, Lx; lia) eq_refl) as SOK end.
        step. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ _) _) =>
          pose proof (u64arr_write USEGS m1 _ _ lenk (Z_to_bv 64 c') CUR ltac:(rewrite Hlc, Lx; lia)) as CUR2 end.
        store_done.
        step. (* [comment removed for export] *)
        zstep. (* [comment removed for export] *)
        rewrite swrap32_small by lia.
        assert (VAL' : bval (upd cur (Z.to_nat lenk) (Z_to_bv 64 c')) (Z.to_nat (lenk + 1)) = (X * 5 ^ (e0 - (e - 27)))%Z).
        { replace (Z.to_nat (lenk + 1)) with (S (Z.to_nat lenk)) by lia.
          rewrite (smul_inv_finish_carry wsk cur POW5_27 (Z.to_nat lenk)) by (first [exact INV | rewrite Lx; lia]).
          rewrite VAL, POW5_27_eq, <- (pow5_step_val X e0 e 27) by lia. ring. }
        assert (BN' : bnorm (upd cur (Z.to_nat lenk) (Z_to_bv 64 c')) (Z.to_nat (lenk + 1))).
        { replace (Z.to_nat (lenk + 1)) with (S (Z.to_nat lenk)) by lia. apply bnorm_push; [rewrite Hlc, Lx; lia|].
          rewrite unsigned_lit by lia. lia. }
        step. (* [comment removed for export] *)
        if_cases Hmore.
        * cond_cleanup Hmore.
          eapply (IH (e + -27)%Z); try eassumption; try lia.
          all: first [rewrite upd_length, Hlc; exact Lx | rewrite VAL'; repeat f_equal; try lia].
        * cond_cleanup Hmore.
          apply evt_done. unfold mid_post. exists (e + -27)%Z. do 7 eexists. eexists _, _, (lenk + 1)%Z.
          split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact CUR2|].
          split; [rewrite upd_length, Hlc; exact Lx|].
          split; [eassumption|]. split; [lia|]. split; [exact BN'|]. split; [lia|]. split; [lia|].
          rewrite VAL'; repeat f_equal; try lia.
  Qed.

  #[using="L62 A8 A0p AL SPLO HA He0 CAP"] Lemma mid_loop : forall x1 x18 x19 x29 x30 x31 wn m0 n, (bv_unsigned wn = 2 ^ 64 - 1 - A)%Z -> mid_ok x1 x18 x19 x29 x30 x31 wn m0 n.
  Proof. LiaFast.lf_pins (fun (L62 A8 A0p AL SPLO HA He0 CAP : LiaFast.U) => LiaFast.u0). intros. induction n as [|n IHn]. - unfold mid_ok; intros; exfalso; lia. - apply mid_body; [assumption| exact IHn]. Qed.

  #[using="L62 A8 A0p AL SPLO HA He0 CAP"] Lemma mid_run : forall (x1 x18 x19 x29 x30 x31 wn : word) (e : Z) (x5 x6 x7 x15 x16 x17 x28 : word)
           (m : word -> option byte) (wsk : list word) (lenk : Z),
      (bv_unsigned wn = 2 ^ 64 - 1 - A)%Z ->
      (27 <= e <= e0)%Z ->
      u64arr USEGS m A wsk -> length wsk = 62%nat ->
      rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e))%Z ->
      evt USEGS (mid_post x1 x18 x19 x29 x30 x31 wn m)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e) wn (Z_to_bv 64 POW5_27) (Z_to_bv 64 26) (Z_to_bv 64 63) (Z_to_bv 64 61) x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x270a8) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (L62 A8 A0p AL SPLO HA He0 CAP : LiaFast.U) => LiaFast.u0).
    intros. eapply (mid_loop x1 x18 x19 x29 x30 x31 wn m (Z.to_nat e) ltac:(assumption) e); try eassumption; try lia.
    - apply munch_refl. - apply wmono_refl.
  Qed.
End Loops.
End U_pow5_B.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.ImgFacts OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5.U_large_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5.U_pow5_A OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5.U_pow5_B.
Import ListNotations.

Module U_large_mul.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs U_long_mul_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5.U_large_mul_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac post_call segs m ::=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      let W' := eval hnf in W in change (munch W' m m') in MUc;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Section Main.
  Hypothesis long_mul_spec : long_mul_stmt.

  #[using="long_mul_spec"] Lemma large_mul_spec : large_mul_stmt.
  Proof. LiaFast.lf_pins (fun (long_mul_spec : LiaFast.U) => LiaFast.u0).
    unfold large_mul_stmt. intros until len. intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 A0p NORM Ha1 Ha2 CAP SEP.
    subst a1 a2.
    pose proof (munch_refl [(bv_unsigned sp - 1248, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 498)]%Z m) as MU.
    pose proof (wmono_refl USEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    carve_frame 16%nat ST.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_taken.
    pose proof (unsigned_lit (bv_unsigned sp + -16) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    call long_mul_spec.
    1:{ rewrite ULs. replace (bv_unsigned sp + -16 - 1232)%Z with (bv_unsigned sp - 1248)%Z by lia. exact ST. }
    1:{ rewrite ULs. Z.div_mod_to_equations. lia. }
    1:{ rewrite ULs. lia. }
    1:{ exact PR. } 1:{ exact LIMBS. } 1:{ exact L62. } 1:{ exact LENC. } 1:{ exact Hlen. } 1:{ exact A8. } 1:{ exact A0p. } 1:{ exact NORM. }
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact CAP. }
    1:{ rewrite ULs. lia. }
    rewrite ?ULs in *.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. step. step. (* [comment removed for export] *)
    match goal with H : stk USEGS _ _ _ |- _ => rename H into ST2 end.
    release_frame FR ST2 (bv_unsigned sp).
    unfold large_mul_post. finish.
    all: try eassumption. all: try lia.
    replace (bv_unsigned sp - 1248)%Z with (bv_unsigned sp + -16 - 1232)%Z by lia. assumption.
  Qed.
End Main.
End U_large_mul.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Local Ltac post_call segs m ::=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      let W' := eval hnf in W in change (munch W' m m') in MUc;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Lemma U_SP5_tbl : table_b USEGS 0x15ad0 8 (fun v => le8 (Z_to_bv 64 v)) SMALL_POW5 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma SMALL_POW5_length : length SMALL_POW5 = 28%nat.
Proof. reflexivity. Qed.

Section Main.
  Hypothesis large_mul_spec : large_mul_stmt.

  Section Fixed.
  Variables (ra sp gp tp a0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (ws : list word) (len e0 : Z) (j8 : list byte).
  Notation A := (bv_unsigned a0).
  Notation SP' := (bv_unsigned sp + -48)%Z.
  Notation X := (bval ws (Z.to_nat len)).
  Notation POST := (pow5_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A e0 ws len m).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis A8 : (A mod 8 = 0)%Z.
  Hypothesis A0p : (0 < A)%Z.
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SEP : (A + 498 <= bv_unsigned sp - 1296 \/ bv_unsigned sp <= A)%Z.
  Hypothesis SPLO : (0x22000 <= bv_unsigned sp - 1296)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.
  Hypothesis AROD : (A + 498 <= 0x10000 \/ 0x22000 <= A)%Z.
  Hypothesis He0 : (0 <= e0 < 2 ^ 31)%Z.
  Hypothesis CAP : (X * 5 ^ e0 < BIG_CAP)%Z.

  (* [comment removed for export] *)
  #[using="L62"] Lemma exit_244e0 : forall (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word)
      (m' : word -> option byte) (wsf : list word) (lenf : Z),
      u64arr USEGS m' A wsf -> length wsf = 62%nat ->
      rw_cells USEGS m' (A + 496) [C2 (Z_to_bv 64 lenf)] -> (0 <= lenf <= 62)%Z ->
      bnorm wsf (Z.to_nat lenf) ->
      bval wsf (Z.to_nat lenf) = (X * 5 ^ e0)%Z ->
      rw_cells USEGS m' SP' [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk USEGS m' (bv_unsigned sp - 1296) SP' ->
      pristine m' 0x10000 0x22000 ->
      munch (pow5_W (bv_unsigned sp) A) m m' -> wmono USEGS m m' ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 a0 x9 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x271b0) fc None m' (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (L62 : LiaFast.U) => LiaFast.u0).
    intros * XA Lx LENC Hl BN VAL FR ST PR MU WM.
    do 7 step.
    release_frame FR ST (bv_unsigned sp).
    unfold pow5_post. finish. all: try eassumption. all: try lia.
  Qed.

  (* [comment removed for export] *)
  #[using="L62 A8 A0p AL SEP SPLO Rsp HA AROD He0 CAP"] Lemma from_25160 : forall (e2 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word)
      (m1 : word -> option byte) (wsk : list word) (lenk : Z),
      (0 <= e2 < 27)%Z -> (e2 <= e0)%Z ->
      u64arr USEGS m1 A wsk -> length wsk = 62%nat ->
      rw_cells USEGS m1 (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e2))%Z ->
      rw_cells USEGS m1 SP' [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk USEGS m1 (bv_unsigned sp - 1296) SP' ->
      pristine m1 0x10000 0x22000 ->
      munch (pow5_W (bv_unsigned sp) A) m m1 -> wmono USEGS m m1 ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 a0 (Z_to_bv 64 e2) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x27114) fc None m1 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (L62 A8 A0p AL SEP SPLO Rsp HA AROD He0 CAP : LiaFast.U) => LiaFast.u0).
    intros * He2 He2' XA Lx LENC Hl BN VAL FR ST PR MU WM.
    cbv delta [pow5_W] in MU.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz.
    - cond_cleanup Hz.
      eapply exit_244e0; try eassumption; try lia.
      all: first [rewrite VAL, Hz, Z.sub_0_r; reflexivity | cbv delta [pow5_W]; exact MU].
    - cond_cleanup Hz.
      zstep. (* [comment removed for export] *)
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
      step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      kill_check.
      step. (* [comment removed for export] *)
      rewrite zx16_lit_small by lia.
      step. (* [comment removed for export] *)
      if_cases Hl0.
      + cond_cleanup Hl0.
        assert (XZ : X = 0%Z). { apply (mul_pow5_zero X (e0 - e2)); [lia|]. rewrite <- VAL, Hl0. reflexivity. }
        eapply exit_244e0; try eassumption; try lia.
        all: first [rewrite Hl0; rewrite XZ; change (Z.to_nat 0) with 0%nat; rewrite bval_0; ring | cbv delta [pow5_W]; exact MU].
      + cond_cleanup Hl0.
        step. (* [comment removed for export] *)
        zstep. (* [comment removed for export] *)
        replace (88784 + e2 * 8)%Z with (88784 + 8 * e2)%Z by lia.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          pose proof (table_read USEGS (fun v => le8 (Z_to_bv 64 v)) SMALL_POW5 0x15ad0 8 mc 0x10000 0x22000
                        U_SP5_tbl PR ltac:(lia) ltac:(rewrite SMALL_POW5_length; cbn; lia) e2
                        ltac:(rewrite SMALL_POW5_length; cbn; lia)) as RD end.
        change (Z.of_nat 8) with 8%Z in RD. rewrite (SMALL_POW5_nth (Z.to_nat e2)) in RD by lia. rewrite Z2Nat.id in RD by lia.
        step. (* [comment removed for export] *)
        clear RD.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        assert (Py : (0 < 5 ^ e2 < 2 ^ 64)%Z).
        { split; [apply Z.pow_pos_nonneg; lia|]. apply (Z.le_lt_trans _ (5 ^ 27)); [apply Z.pow_le_mono_r; lia|]. cbn; lia. }
        assert (CAPs : (X * 5 ^ (e0 - e2) * 5 ^ e2 < BIG_CAP)%Z).
        { rewrite (pow5_step_val X e0 e2 e2) by lia. apply (cap_pow5_mono X _ e0); lia. }
        name_mem mc.
        call (@usmulF_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 F fc mc A (5 ^ e2) wsk lenk Lx ltac:(lia) ltac:(lia) (conj A0p (proj2 HA)) a0).
        all: try lia.
        1:{ exact XA. } 1:{ exact Lx. } 1:{ intros j; reflexivity. }
        match goal with H : smul_inv _ _ _ _ ?c |- _ => rename H into INV; rename c into c' end.
        match goal with H : u64arr USEGS _ A ?cu |- _ => rename H into CUR; rename cu into cur end.
        pose proof INV as (Hv & Hag & Hc' & Hlc).
        assert (CAPy : (5 ^ e2 * bval wsk (Z.to_nat lenk) < BIG_CAP)%Z) by (rewrite VAL, Z.mul_comm; exact CAPs).
        step. (* [comment removed for export] *)
        if_cases Hcz.
        * (* [comment removed for export] *)
          cond_cleanup Hcz.
          eapply exit_244e0; try eassumption; try lia.
          all: first [ cbv delta [pow5_W]; assumption
                     | apply bnorm_of_value; [lia|];
                       pose proof (bnorm_lower wsk (Z.to_nat lenk) BN ltac:(lia)) as LO;
                       rewrite (smul_inv_finish_nocarry wsk cur (5 ^ e2) (Z.to_nat lenk)) by (rewrite <- Hcz; exact INV); nia
                     | rewrite (smul_inv_finish_nocarry wsk cur (5 ^ e2) (Z.to_nat lenk)) by (rewrite <- Hcz; exact INV);
                       rewrite VAL, (Z.mul_comm (5 ^ e2)), (pow5_step_val X e0 e2 e2) by lia; repeat f_equal; lia ].
        * (* [comment removed for export] *)
          cond_cleanup Hcz.
          pose proof (smul_carry_room wsk _ _ _ _ INV ltac:(lia) CAPy) as ROOM.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_not_taken.
          zstep. (* [comment removed for export] *)
          rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          kill_check.
          zstep. (* [comment removed for export] *)
          replace (A + lenk * 8)%Z with (A + 8 * lenk)%Z by lia.
          zstep. (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            pose proof (u64arr_store_ok USEGS m1 _ _ lenk (Z_to_bv 64 (A + 8 * lenk)) CUR ltac:(rewrite Hlc, Lx; lia) eq_refl) as SOK end.
          step. (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ _) _) =>
            pose proof (u64arr_write USEGS m1 _ _ lenk (Z_to_bv 64 c') CUR ltac:(rewrite Hlc, Lx; lia)) as CUR2 end.
          store_done.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          eapply exit_244e0; try eassumption; try lia.
          all: first [ cbv delta [pow5_W]; assumption
                     | rewrite upd_length, Hlc; exact Lx
                     | replace (Z.to_nat (lenk + 1)) with (S (Z.to_nat lenk)) by lia; apply bnorm_push; [rewrite Hlc, Lx; lia|]; rewrite unsigned_lit by lia; lia
                     | replace (Z.to_nat (lenk + 1)) with (S (Z.to_nat lenk)) by lia;
                       rewrite (smul_inv_finish_carry wsk cur (5 ^ e2) (Z.to_nat lenk)) by (first [exact INV | rewrite Lx; lia]);
                       rewrite VAL, (Z.mul_comm (5 ^ e2)), (pow5_step_val X e0 e2 e2) by lia; repeat f_equal; lia ].
  Qed.

  (* [comment removed for export] *)
  #[using="L62 A8 A0p AL SEP SPLO Rsp HA AROD He0 CAP"] Lemma from_250d4 : forall (e1 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word)
      (m1 : word -> option byte) (wsk : list word) (lenk : Z),
      (0 <= e1 < 135)%Z -> (e1 <= e0)%Z ->
      u64arr USEGS m1 A wsk -> length wsk = 62%nat ->
      rw_cells USEGS m1 (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e1))%Z ->
      rw_cells USEGS m1 SP' [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk USEGS m1 (bv_unsigned sp - 1296) SP' ->
      pristine m1 0x10000 0x22000 ->
      munch (pow5_W (bv_unsigned sp) A) m m1 -> wmono USEGS m m1 ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 a0 (Z_to_bv 64 e1) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x27088) fc None m1 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (L62 A8 A0p AL SEP SPLO Rsp HA AROD He0 CAP : LiaFast.U) => LiaFast.u0).
    intros * He1 He1' XA Lx LENC Hl BN VAL FR ST PR MU WM.
    cbv delta [pow5_W] in MU.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H27.
    - cond_cleanup H27.
      eapply from_25160; try eassumption; try lia. all: cbv delta [pow5_W]; exact MU.
    - cond_cleanup H27.
      step. (* [comment removed for export] *)
      lazymatch goal with |- context [Z_to_bv 64 (Z.lxor (bv_unsigned a0) 18446744073709551615)] =>
        remember (Z_to_bv 64 (Z.lxor (bv_unsigned a0) 18446744073709551615)) as wn eqn:Ewn end.
      assert (Hwn : (bv_unsigned wn = 2 ^ 64 - 1 - A)%Z).
      { subst wn. rewrite zb_lxor_ones by lia. rewrite unsigned_lit by lia. lia. }
      clear Ewn.
      step. step. (* [comment removed for export] *)
      change 7450580596923828125%Z with POW5_27.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      name_mem mc.
      eapply evt_cut; [ eapply mid_run with (ws:=ws) (len:=len) | post_call USEGS mc ].
      all: try eassumption; try lia.
      eapply from_25160; try eassumption; try lia. all: cbv delta [pow5_W]; assumption.
  Qed.
  End Fixed.

  #[using="large_mul_spec"] Lemma pow5_spec : pow5_stmt.
  Proof. LiaFast.lf_pins (fun (large_mul_spec : LiaFast.U) => LiaFast.u0).
    unfold pow5_stmt. intros until len. intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 A0p NORM He CAP SEP.
    pose proof (munch_refl (pow5_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU.
    cbv delta [pow5_W] in MU.
    pose proof (wmono_refl USEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a1) as Re. unfold bv_modulus in Re.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    pose proof (u64arr_outside_rodata_U m _ _ PR LIMBS ltac:(rewrite L62; lia)) as AROD. rewrite L62 in AROD.
    pose proof (rw_cells_outside_rodata_U m _ _ PR LENC ltac:(cbn; lia)) as CROD. cbn [cells_size csize Nat.add] in CROD.
    assert (HA : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 498 <= 2 ^ 64)%Z) by lia.
    assert (AROD' : (bv_unsigned a0 + 498 <= 0x10000 \/ 0x22000 <= bv_unsigned a0)%Z) by lia.
    clear Bl Bc AROD CROD. rename AROD' into AROD.
    remember (bv_unsigned a1) as e0 eqn:Ee0.
    rewrite <- (Z_to_bv_bv_unsigned a1), <- Ee0.
    carve_frame 48%nat ST.
    do 6 step. (* [comment removed for export] *)
    match type of FR with context [CB 8 ?j] => remember j as j8 eqn:E8 in FR; clear E8 end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H135.
    - (* [comment removed for export] *)
      cond_cleanup H135.
      eapply from_250d4; try eassumption; try lia.
      all: first [rewrite Z.sub_diag, Z.pow_0_r; ring | cbv delta [pow5_W]; exact MU].
    - cond_cleanup H135.
      step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      name_mem mc.
      eapply evt_cut; [ eapply (big_run large_mul_spec) with (ws:=ws) (len:=len) | post_call USEGS mc ].
      all: try eassumption; try lia.
      all: try (rewrite Z.sub_diag, Z.pow_0_r; ring).
      eapply from_250d4; try eassumption; try lia. all: cbv delta [pow5_W]; assumption.
  Qed.
End Main.
