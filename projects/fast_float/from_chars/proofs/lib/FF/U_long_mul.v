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
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_large_add_from_stmt.

Module U_extend_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition extend_entry : Z := 0x276fc.

Definition extend_W (sp V : Z) : list ivl := [(sp - 96, sp); (V, V + 498)]%Z.

Definition extend_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (V c : Z) (vws sws : list word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch (extend_W (bv_unsigned sp) V) m m'
    /\ wmono USEGS m m'
    /\ stk USEGS m' (bv_unsigned sp - 96) (bv_unsigned sp)
    /\ u64arr USEGS m' V (firstn (Z.to_nat c) sws ++ skipn (Z.to_nat c) vws)
    /\ rw_cells USEGS m' (V + 496) [C2 (Z_to_bv 64 c)].

Definition extend_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (vws sws : list word),
    stk USEGS m (bv_unsigned sp - 96) (bv_unsigned sp) ->
    u64arr USEGS m (bv_unsigned a0) vws -> length vws = 62%nat ->
    rw_cells USEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 0)] ->
    u64arr USEGS m (bv_unsigned a1) sws -> length sws = 62%nat ->
    (bv_unsigned a2 <= 62)%Z ->
    (bv_unsigned a0 mod 8 = 0)%Z -> (bv_unsigned a1 mod 8 = 0)%Z ->
    (0 < bv_unsigned a0)%Z -> (0 < bv_unsigned a1)%Z -> (bv_unsigned a1 + 496 < 2 ^ 64)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    (bv_unsigned a0 + 498 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 496 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a0 + 498 <= bv_unsigned a1 \/ bv_unsigned a1 + 496 <= bv_unsigned a0)%Z ->
    evt USEGS (extend_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (bv_unsigned a0) (bv_unsigned a2) vws sws m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x276fc) fc None m (seg_rom USEGS)).
End U_extend_stmt.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_large_add_from_stmt U_normalize_stmt U_long_mul_stmt.

Module U_long_mul_A.
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
Section usmul1.
  Variables (x1 x2 x3 x4 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (A y NA : Z) (ws : list word) (len : Z).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis Hy : (0 <= y < 2 ^ 64)%Z.
  Hypothesis HA : (0 < A /\ A + 498 <= 2 ^ 64)%Z.
  Hypothesis HNA : (NA = (2 ^ 64 - A) / 8)%Z.

  Definition usmul1_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (c' : Z) (tl tlo tcnt tsum : word) (m' : word -> option byte) (cur : list word),
      ms' = MS (mkR x1 x2 x3 x4 tlo tsum x7 x8 x9 (Z_to_bv 64 len) (Z_to_bv 64 c') (Z_to_bv 64 y) (Z_to_bv 64 NA) (Z_to_bv 64 63) (Z_to_bv 64 (A + 8 * len)) tcnt tl x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x273ac) fc None m' (seg_rom USEGS)
      /\ munch [(A, A + 8 * len)]%Z m m'
      /\ wmono USEGS m m'
      /\ u64arr USEGS m' A cur
      /\ length cur = 62%nat
      /\ smul_inv ws cur y (Z.to_nat len) c'.

  Definition usmul1_ok (k : nat) : Prop :=
    forall (i : nat) (p tl tlo tsum : word) (c : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      u64arr USEGS m A cur -> length cur = 62%nat ->
      smul_inv ws cur y i c ->
      munch [(A, A + 8 * len)]%Z m0 m -> wmono USEGS m0 m ->
      evt USEGS (usmul1_post m0)
        (MS (mkR x1 x2 x3 x4 tlo tsum x7 x8 x9 (Z_to_bv 64 len) (Z_to_bv 64 c) (Z_to_bv 64 y) (Z_to_bv 64 NA) (Z_to_bv 64 63) p (Z_to_bv 64 (63 - Z.of_nat i)) tl x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x27374) fc None m (seg_rom USEGS)).

  #[using="L62 LEN Hy HA HNA"] Lemma usmul1_body : forall k, usmul1_ok k -> usmul1_ok (S k).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA HNA : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold usmul1_ok. intros i p tl tlo tsum c cur m Hk Hi Hp CUR Hcur INV MU WM.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    destruct INV as (Hv & Hag & Hc & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    step. (* [comment removed for export] *)
    kill_check.
    zstep. (* [comment removed for export] *)
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
      apply evt_done. unfold usmul1_post.
      eexists (mul_cout (limbZ ws i) y c), _, _, _, _, m1, (upd cur i (Z_to_bv 64 (limbZ ws i * y + c))).
      split. { f_equal. replace (bv_unsigned p + 8)%Z with (A + 8 * len)%Z by lia. reflexivity. }
      split; [exact MU|]. split; [exact WM|].
      split. { replace (limbZ ws i) with (bv_unsigned w) by (unfold limbZ; rewrite <- Hw; reflexivity). exact CUR'. }
      split; [rewrite upd_length; exact Hcur|].
      rewrite <- Hil. replace (limbZ ws i * y)%Z with (bv_unsigned w * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity). exact INV'.
  Qed.

  #[using="L62 LEN Hy HA HNA"] Lemma usmul1_loop : forall k, usmul1_ok k.
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA HNA : LiaFast.U) => LiaFast.u0). induction k as [|k IH]. - unfold usmul1_ok; intros; exfalso; lia. - apply usmul1_body; exact IH. Qed.

  #[using="L62 LEN Hy HA HNA"] Lemma usmul1_run : forall (p tl tlo tsum : word) (cur : list word),
    bv_unsigned p = A ->
    u64arr USEGS m0 A cur -> length cur = 62%nat -> (forall j, nth j cur w0 = nth j ws w0) ->
    evt USEGS (usmul1_post m0)
      (MS (mkR x1 x2 x3 x4 tlo tsum x7 x8 x9 (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 y) (Z_to_bv 64 NA) (Z_to_bv 64 63) p (Z_to_bv 64 63) tl x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x27374) fc None m0 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA HNA : LiaFast.U) => LiaFast.u0).
    intros p tl tlo tsum cur Hp CUR Hcur Hag.
    replace (Z_to_bv 64 63) with (Z_to_bv 64 (63 - Z.of_nat 0)) at 2 by (f_equal; lia).
    eapply (usmul1_loop (Z.to_nat len) 0%nat); try eassumption; try lia.
    - split; [cbn; lia|]. split; [intros; apply Hag|]. split; [lia|]. rewrite Hcur, L62. reflexivity.
    - apply munch_refl.
    - apply wmono_refl.
  Qed.
End usmul1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section usmul2.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x17 x18 x19 x20 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (A y : Z) (ws : list word) (len : Z).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis Hy : (0 <= y < 2 ^ 64)%Z.
  Hypothesis HA : (0 < A /\ A + 498 <= 2 ^ 64)%Z.

  Definition usmul2_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (c' : Z) (tl tlo tcnt tsum : word) (m' : word -> option byte) (cur : list word),
      ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 c') tcnt (Z_to_bv 64 len) (Z_to_bv 64 (A + 8 * len)) tl tlo tsum x17 x18 x19 x20 (Z_to_bv 64 63) x22 x23 (Z_to_bv 64 y) x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x27460) fc None m' (seg_rom USEGS)
      /\ munch [(A, A + 8 * len)]%Z m m'
      /\ wmono USEGS m m'
      /\ u64arr USEGS m' A cur
      /\ length cur = 62%nat
      /\ smul_inv ws cur y (Z.to_nat len) c'.

  Definition usmul2_ok (k : nat) : Prop :=
    forall (i : nat) (p tl tlo tsum : word) (c : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      u64arr USEGS m A cur -> length cur = 62%nat ->
      smul_inv ws cur y i c ->
      munch [(A, A + 8 * len)]%Z m0 m -> wmono USEGS m0 m ->
      evt USEGS (usmul2_post m0)
        (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 c) (Z_to_bv 64 (63 - Z.of_nat i)) (Z_to_bv 64 len) p tl tlo tsum x17 x18 x19 x20 (Z_to_bv 64 63) x22 x23 (Z_to_bv 64 y) x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x27430) fc None m (seg_rom USEGS)).

  #[using="L62 LEN Hy HA"] Lemma usmul2_body : forall k, usmul2_ok k -> usmul2_ok (S k).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold usmul2_ok. intros i p tl tlo tsum c cur m Hk Hi Hp CUR Hcur INV MU WM.
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
      apply evt_done. unfold usmul2_post.
      eexists (mul_cout (limbZ ws i) y c), _, _, _, _, m1, (upd cur i (Z_to_bv 64 (limbZ ws i * y + c))).
      split. { f_equal. replace (bv_unsigned p + 8)%Z with (A + 8 * len)%Z by lia. reflexivity. }
      split; [exact MU|]. split; [exact WM|].
      split. { replace (limbZ ws i) with (bv_unsigned w) by (unfold limbZ; rewrite <- Hw; reflexivity). exact CUR'. }
      split; [rewrite upd_length; exact Hcur|].
      rewrite <- Hil. replace (limbZ ws i * y)%Z with (bv_unsigned w * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity). exact INV'.
  Qed.

  #[using="L62 LEN Hy HA"] Lemma usmul2_loop : forall k, usmul2_ok k.
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0). induction k as [|k IH]. - unfold usmul2_ok; intros; exfalso; lia. - apply usmul2_body; exact IH. Qed.

  #[using="L62 LEN Hy HA"] Lemma usmul2_run : forall (p tl tlo tsum : word) (cur : list word),
    bv_unsigned p = A ->
    u64arr USEGS m0 A cur -> length cur = 62%nat -> (forall j, nth j cur w0 = nth j ws w0) ->
    evt USEGS (usmul2_post m0)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 len) p tl tlo tsum x17 x18 x19 x20 (Z_to_bv 64 63) x22 x23 (Z_to_bv 64 y) x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x27430) fc None m0 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0).
    intros p tl tlo tsum cur Hp CUR Hcur Hag.
    replace (Z_to_bv 64 63) with (Z_to_bv 64 (63 - Z.of_nat 0)) at 1 by (f_equal; lia).
    eapply (usmul2_loop (Z.to_nat len) 0%nat); try eassumption; try lia.
    - split; [cbn; lia|]. split; [intros; apply Hag|]. split; [lia|]. rewrite Hcur, L62. reflexivity.
    - apply munch_refl.
    - apply wmono_refl.
  Qed.
End usmul2.
End U_long_mul_A.


Module U_long_mul_B.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_large_add_from_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_large_add_from_stmt U_long_mul_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_large_add_from_stmt.U_span_index_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_extend_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_large_add_from_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_long_mul_A.
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

Lemma U_LP5_tbl : table_b USEGS 0x15aa8 8 (fun v => le8 (Z_to_bv 64 v)) LARGE_POW5 = true.
Proof. vm_compute. reflexivity. Qed.

Section Iter.
  Hypothesis span_index_spec : span_index_stmt.
  Hypothesis extend_spec : extend_stmt.
  Hypothesis large_add_from_spec : large_add_from_stmt.
  Variables (sp va gp tp w6 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (ws zw : list word) (len : Z) (j1 : list byte).
  Notation A := (bv_unsigned va).
  Notation SP' := (bv_unsigned sp + -1120)%Z.
  Notation X := (bval ws (Z.to_nat len)).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis A8 : (A mod 8 = 0)%Z.
  Hypothesis A0p : (0 < A)%Z.
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SEP : (A + 498 <= bv_unsigned sp - 1232 \/ bv_unsigned sp <= A)%Z.
  Hypothesis SPLO : (0x22000 <= bv_unsigned sp - 1232)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.
  Hypothesis AROD : (A + 498 <= 0x10000 \/ 0x22000 <= A)%Z.
  Hypothesis NORM : bnorm ws (Z.to_nat len).
  Hypothesis CAP : (X * 5 ^ 135 < BIG_CAP)%Z.
  Hypothesis Lzw : length zw = 62%nat.
  Hypothesis Hzw : forall j, (j < Z.to_nat len)%nat -> nth j zw w0 = nth j ws w0.
  Hypothesis Hw6 : (bv_unsigned w6 = 2 ^ 64 - 1 - (bv_unsigned sp + -1104))%Z.

  Definition iter_W : list ivl :=
    [(bv_unsigned sp - 1232, bv_unsigned sp + -1120); (bv_unsigned sp + -1104, bv_unsigned sp + -606); (A, A + 498)]%Z.

  Definition iter_post (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word)
                      (m' : word -> option byte) (wsk : list word) (lenk : Z) (ziw : list word) (zil : Z),
      ms' = MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 len) x10 x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 5) (Z_to_bv 64 (bv_unsigned sp + -1104)) (Z_to_bv 64 62) (Z_to_bv 64 63) w6 (Z_to_bv 64 61)
                   x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x274a0) fc None m' (seg_rom USEGS)
      /\ munch iter_W m0 m'
      /\ wmono USEGS m0 m'
      /\ u64arr USEGS m' A wsk /\ length wsk = 62%nat
      /\ rw_cells USEGS m' (A + 496) [C2 (Z_to_bv 64 lenk)] /\ (0 <= lenk <= 62)%Z
      /\ bval wsk (Z.to_nat lenk) = (X * 5 ^ 135)%Z
      /\ u64arr USEGS m' (bv_unsigned sp + -1104) ziw /\ length ziw = 62%nat
      /\ rw_cells USEGS m' (bv_unsigned sp + -608) [C2 (Z_to_bv 64 zil)]
      /\ rw_cells USEGS m' (bv_unsigned sp + -606) [CB 6 j1]
      /\ u64arr USEGS m' (bv_unsigned sp + -600) zw
      /\ rw_cells USEGS m' (bv_unsigned sp + -96) [C8 (Z_to_bv 64 0x15aa8); C8 (Z_to_bv 64 5)]
      /\ stk USEGS m' (bv_unsigned sp - 1232) SP'
      /\ pristine m' 0x10000 0x22000.

  Definition iter_ok (n : nat) : Prop :=
    forall (m0 : word -> option byte) (k : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word)
           (m : word -> option byte) (wsk : list word) (lenk : Z) (ziw : list word) (zil : Z),
      (Z.to_nat (5 - k) = n)%nat -> (1 <= k <= 4)%Z ->
      u64arr USEGS m A wsk -> length wsk = 62%nat ->
      rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bval wsk (Z.to_nat lenk) = (X * zsum LARGE_POW5 (Z.to_nat k))%Z ->
      u64arr USEGS m (bv_unsigned sp + -1104) ziw -> length ziw = 62%nat ->
      rw_cells USEGS m (bv_unsigned sp + -608) [C2 (Z_to_bv 64 zil)] ->
      rw_cells USEGS m (bv_unsigned sp + -606) [CB 6 j1] ->
      u64arr USEGS m (bv_unsigned sp + -600) zw ->
      rw_cells USEGS m (bv_unsigned sp + -96) [C8 (Z_to_bv 64 0x15aa8); C8 (Z_to_bv 64 5)] ->
      stk USEGS m (bv_unsigned sp - 1232) SP' ->
      pristine m 0x10000 0x22000 ->
      munch iter_W m0 m -> wmono USEGS m0 m ->
      evt USEGS (iter_post m0)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 len) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 k) (Z_to_bv 64 (bv_unsigned sp + -1104)) (Z_to_bv 64 62) (Z_to_bv 64 63) w6 (Z_to_bv 64 61)
                 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x273f0) fc None m (seg_rom USEGS)).

  (* [comment removed for export] *)
  #[using="large_add_from_spec L62 A8 A0p AL SEP SPLO Rsp AROD CAP Lzw"] Lemma from_254cc : forall (n : nat), iter_ok n ->
    forall (k yk : Z) (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m0 m : word -> option byte) (wsk : list word) (lenk : Z) (ziw : list word) (zil : Z),
      (Z.to_nat (5 - (k + 1)) = n)%nat -> (1 <= k <= 4)%Z ->
      yk = nth (Z.to_nat k) LARGE_POW5 0%Z ->
      u64arr USEGS m A wsk -> length wsk = 62%nat ->
      rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bval wsk (Z.to_nat lenk) = (X * zsum LARGE_POW5 (Z.to_nat k))%Z ->
      u64arr USEGS m (bv_unsigned sp + -1104) ziw -> length ziw = 62%nat ->
      rw_cells USEGS m (bv_unsigned sp + -608) [C2 (Z_to_bv 64 zil)] ->
      rw_cells USEGS m (bv_unsigned sp + -606) [CB 6 j1] ->
      (0 <= zil)%Z -> (zil + k <= 62)%Z ->
      bval ziw (Z.to_nat zil) = (yk * X)%Z ->
      u64arr USEGS m (bv_unsigned sp + -600) zw ->
      rw_cells USEGS m (bv_unsigned sp + -96) [C8 (Z_to_bv 64 0x15aa8); C8 (Z_to_bv 64 5)] ->
      stk USEGS m (bv_unsigned sp - 1232) SP' ->
      pristine m 0x10000 0x22000 ->
      munch iter_W m0 m -> wmono USEGS m0 m ->
      evt USEGS (iter_post m0)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 len) x10 x11 (Z_to_bv 64 zil) x13 x14 x15 x16 x17
                 (Z_to_bv 64 k) (Z_to_bv 64 (bv_unsigned sp + -1104)) (Z_to_bv 64 62) (Z_to_bv 64 63) w6 (Z_to_bv 64 61)
                 (Z_to_bv 64 yk) x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x27480) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (large_add_from_spec L62 A8 A0p AL SEP SPLO Rsp AROD CAP Lzw : LiaFast.U) => LiaFast.u0).
    intros n IH k yk x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 m0 m wsk lenk ziw zil
           Hn Hk Hyk XA Lx LENC Hlenk VAL ZIA Lzi ZIL PAD Hzil0 ROOM VZI ZA SPAN ST PR MU WM.
    cbv delta [iter_W] in MU.
    pose proof (LP5_nth_range (Z.to_nat k) ltac:(lia)) as Ryk. rewrite <- Hyk in Ryk.
    pose proof (LP5_zsum_step_le (Z.to_nat k) ltac:(lia)) as STEP. rewrite <- Hyk in STEP. rewrite Z2Nat.id in STEP by lia.
    pose proof (LP5_zsum_mono (Z.to_nat k) ltac:(lia)) as MONO.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit SP' ltac:(lia)) as ULs. pose proof (unsigned_lit (bv_unsigned sp + -1104) ltac:(lia)) as ULy.
    step. (* [comment removed for export] *)
    call large_add_from_spec.
    1:{ eapply stk_at_eq; [exact ST | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia]. }
    1:{ rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia. }
    1:{ exact XA. } 1:{ exact Lx. } 1:{ exact LENC. } 1:{ exact Hlenk. } 1:{ exact A8. }
    1:{ eapply u64arr_at_eq; [exact ZIA | rewrite unsigned_lit by lia; lia]. } 1:{ exact Lzi. }
    1:{ reflexivity. } 1:{ lia. }
    1:{ rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia. } 1:{ rewrite unsigned_lit by lia. lia. } 1:{ rewrite unsigned_lit by lia. lia. }
    1:{ reflexivity. } 1:{ lia. } 1:{ lia. }
    1:{ rewrite VAL, VZI. unfold BIG_CAP in *. apply (cap_step X _ yk _ (5 ^ 135)); try lia; apply Z.pow_nonneg; lia. }
    1:{ rewrite !unsigned_lit by lia. lia. } 1:{ rewrite !unsigned_lit by lia. lia. } 1:{ rewrite !unsigned_lit by lia. lia. }
    rewrite ?ULs, ?ULy in *.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hmore.
    - cond_cleanup Hmore.
      replace (SP' - 112)%Z with (bv_unsigned sp - 1232)%Z in * by lia.
      eapply (IH m0 (k + 1)%Z); try eassumption; try lia.
      all: lazymatch goal with
           | |- bval _ _ = _ =>
               match goal with H : bval ?a ?b = (bval ?c ?d + bval ?e ?f * _)%Z |- _ => rewrite H end;
               rewrite VAL, VZI; replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia; rewrite zsum_S, <- Hyk; rewrite Z2Nat.id by lia; ring
           | |- munch _ _ _ => cbv delta [iter_W]; assumption
           | |- stk _ _ _ _ => assumption
           end.
    - cond_cleanup Hmore.
      apply evt_done. unfold iter_post.
      do 17 eexists. eexists _, _, _, ziw, zil.
      split. { assert (k = 4)%Z as -> by lia. reflexivity. }
      split. { cbv delta [iter_W]. assumption. } split. { assumption. }
      split. { eassumption. } split. { assumption. } split. { eassumption. } split. { lia. }
      split. { match goal with H : bval ?a ?b = (bval ?c ?d + bval ?e ?f * _)%Z |- _ => rewrite H end.
               rewrite VAL, VZI. rewrite <- LP5_zsum_5. assert (k = 4)%Z as -> by lia.
               change 5%nat with (S (Z.to_nat 4)). rewrite zsum_S, <- Hyk. change (Z.of_nat (Z.to_nat 4)) with 4%Z. ring. }
      split. { assumption. } split. { assumption. } split. { assumption. } split. { assumption. } split. { assumption. } split. { assumption. }
      split. { replace (SP' - 112)%Z with (bv_unsigned sp - 1232)%Z in * by lia. assumption. }
      assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="large_add_from_spec L62 Hlen A8 A0p AL SEP SPLO Rsp AROD NORM CAP Lzw Hw6"] Lemma from_25468 : forall (n : nat), iter_ok n ->
    forall (k yk : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m0 m : word -> option byte) (wsk : list word) (lenk : Z) (ziw : list word),
      (Z.to_nat (5 - (k + 1)) = n)%nat -> (1 <= k <= 4)%Z ->
      yk = nth (Z.to_nat k) LARGE_POW5 0%Z ->
      u64arr USEGS m A wsk -> length wsk = 62%nat ->
      rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bval wsk (Z.to_nat lenk) = (X * zsum LARGE_POW5 (Z.to_nat k))%Z ->
      u64arr USEGS m (bv_unsigned sp + -1104) ziw -> length ziw = 62%nat ->
      (forall j, (j < Z.to_nat len)%nat -> nth j ziw w0 = nth j ws w0) ->
      rw_cells USEGS m (bv_unsigned sp + -608) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m (bv_unsigned sp + -606) [CB 6 j1] ->
      u64arr USEGS m (bv_unsigned sp + -600) zw ->
      rw_cells USEGS m (bv_unsigned sp + -96) [C8 (Z_to_bv 64 0x15aa8); C8 (Z_to_bv 64 5)] ->
      stk USEGS m (bv_unsigned sp - 1232) SP' ->
      pristine m 0x10000 0x22000 ->
      munch iter_W m0 m -> wmono USEGS m0 m ->
      evt USEGS (iter_post m0)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 len) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 k) (Z_to_bv 64 (bv_unsigned sp + -1104)) (Z_to_bv 64 62) (Z_to_bv 64 63) w6 (Z_to_bv 64 61)
                 (Z_to_bv 64 yk) x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2741c) fc None m (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (large_add_from_spec L62 Hlen A8 A0p AL SEP SPLO Rsp AROD NORM CAP Lzw Hw6 : LiaFast.U) => LiaFast.u0).
    clear HA. (* [comment removed for export] *)
    intros n IH k yk x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m0 m wsk lenk ziw
           Hn Hk Hyk XA Lx LENC Hlenk VAL ZIA Lzi AGR ZIL PAD ZA SPAN ST PR MU WM.
    cbv delta [iter_W] in MU.
    pose proof (LP5_nth_range (Z.to_nat k) ltac:(lia)) as Ryk. rewrite <- Hyk in Ryk.
    pose proof (LP5_zsum_step_le (Z.to_nat k) ltac:(lia)) as STEP. rewrite <- Hyk in STEP. rewrite Z2Nat.id in STEP by lia.
    pose proof (LP5_zsum_mono (Z.to_nat k) ltac:(lia)) as MONO.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    assert (XZ : bval ziw (Z.to_nat len) = X) by (apply bval_agree; exact AGR).
    assert (P64k : (1 <= 2 ^ (64 * k))%Z). { pose proof (pow64_pos (Z.to_nat k)) as P. rewrite Z2Nat.id in P by lia. lia. }
    pose proof (cap_yk X _ yk _ (5 ^ 135) BIG_CAP X0 (proj1 MONO) ltac:(lia) P64k STEP CAP) as [CAP1 CAP2].
    unfold BIG_CAP in CAP2.
    step. (* [comment removed for export] *)
    rewrite zx16_lit_small by lia.
    step. (* [comment removed for export] *)
    if_cases Hz.
    - (* [comment removed for export] *)
      cond_cleanup Hz.
      eapply (from_254cc n IH k yk); try eassumption; try lia.
      all: lazymatch goal with
           | |- munch _ _ _ => cbv delta [iter_W]; assumption
           | |- bval _ _ = _ => rewrite Hz in XZ |- *; change (Z.to_nat 0) with 0%nat in *; rewrite bval_0; rewrite <- XZ, bval_0; ring
           | _ => idtac
           end.
      all: fail "from_25468: leftover".
    - cond_cleanup Hz.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      call (@usmul2_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               F fc mc (bv_unsigned sp + -1104) yk ziw len Lzi ltac:(lia) ltac:(lia) ltac:(lia) (Z_to_bv 64 (bv_unsigned sp + -1104)))
      end.
      all: try lia.
      1:{ rewrite unsigned_lit by lia. reflexivity. } 1:{ exact ZIA. } 1:{ exact Lzi. } 1:{ intros j; reflexivity. }
      match goal with H : smul_inv _ _ _ _ ?c |- _ => rename H into INV; rename c into c' end.
      match goal with H : u64arr USEGS _ (bv_unsigned sp + -1104) ?cu |- _ => rename H into CUR; rename cu into cur end.
      pose proof INV as (Hv & Hag & Hc' & Hlc).
      step. (* [comment removed for export] *)
      if_cases Hcz.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        eapply (from_254cc n IH k yk); try eassumption; try lia.
        all: lazymatch goal with
             | |- munch _ _ _ => cbv delta [iter_W]; assumption
             | |- bval _ _ = _ =>
                 rewrite <- XZ; symmetry; apply (smul_inv_finish_nocarry ziw _ yk); rewrite <- Hcz; exact INV
             | |- (_ <= 62)%Z =>
                 destruct NORM as [N0|NT]; [lia|];
                 pose proof (bnorm_lower ws (Z.to_nat len) (or_intror NT) ltac:(lia)) as LO;
                 replace (Z.of_nat (Z.to_nat len - 1)) with (len - 1)%Z in LO by lia;
                 pose proof (room_nocarry X yk k (len - 1) ltac:(lia) ltac:(lia) LO ltac:(lia) CAP2); lia
             | _ => idtac
             end.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        pose proof (smul_carry_room ziw _ yk _ _ INV ltac:(lia) ltac:(rewrite XZ; exact CAP1)) as ROOM1.
        step. (* [comment removed for export] *)
        if_not_taken.
        zstep. (* [comment removed for export] *)
        rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
        step. (* [comment removed for export] *)
        if_cases Hc6. { cond_cleanup Hc6. exfalso. clear -Hc6 Hw6 Rsp Hlen. lia. } clear Hc6.
        zstep. (* [comment removed for export] *)
        replace (bv_unsigned sp + -1104 + len * 8)%Z with (bv_unsigned sp + -1104 + 8 * len)%Z by lia.
        zstep. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          pose proof (u64arr_store_ok USEGS mc _ _ len (Z_to_bv 64 (bv_unsigned sp + -1104 + 8 * len)) CUR ltac:(rewrite Hlc, Lzi; lia) eq_refl) as SOK end.
        step. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
          pose proof (u64arr_write USEGS mc _ _ len (Z_to_bv 64 c') CUR ltac:(rewrite Hlc, Lzi; lia)) as CUR2 end.
        store_done.
        step. (* [comment removed for export] *)
        eapply (from_254cc n IH k yk); try eassumption; try lia.
        all: lazymatch goal with
             | |- munch _ _ _ => cbv delta [iter_W]; assumption
             | |- length _ = _ => rewrite upd_length, Hlc; exact Lzi
             | |- bval _ _ = _ =>
                 replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia; rewrite <- XZ;
                 apply (smul_inv_finish_carry ziw _ yk); [exact INV| rewrite Lzi; lia]
             | |- (_ <= 62)%Z =>
                 rewrite XZ in Hv; rewrite Z2Nat.id in Hv by lia;
                 pose proof (room_carry _ c' (yk * X) k len ltac:(lia) ltac:(lia) (bval_nonneg _ _) ltac:(lia) Hv CAP2); lia
             | _ => idtac
             end.
  Qed.

  #[using="span_index_spec extend_spec large_add_from_spec L62 Hlen A8 A0p AL SEP SPLO Rsp AROD NORM CAP Lzw Hzw Hw6"] Lemma iter_body : forall n, iter_ok n -> iter_ok (S n).
  Proof. LiaFast.lf_pins (fun (span_index_spec extend_spec large_add_from_spec L62 Hlen A8 A0p AL SEP SPLO Rsp AROD NORM CAP Lzw Hzw Hw6 : LiaFast.U) => LiaFast.u0).
    intros n IH. unfold iter_ok.
    intros m0 k x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 m wsk lenk ziw zil
           Hn Hk XA Lx LENC Hlenk VAL ZIA Lzi ZIL PAD ZA SPAN ST PR MU WM.
    cbv delta [iter_W] in MU.
    pose proof (LP5_nth_range (Z.to_nat k) ltac:(lia)) as Ryk.
    remember (nth (Z.to_nat k) LARGE_POW5 0%Z) as yk eqn:Hyk.
    pose proof (u64arr_bound _ _ _ _ ZA) as Bz. rewrite Lzw in Bz.
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (rw_cells_read USEGS m _ _ 0%nat _ SPAN eq_refl) as RDS.
    cbn [csize cbytes Z.of_nat] in RDS. rewrite Z.add_0_r in RDS. unfold wa in RDS.
    step. (* [comment removed for export] *)
    eapply evt_cut; [ eapply span_index_spec with (p := Z_to_bv 64 0x15aa8) (i := k) | ].
    1:{ exact RDS. } 1:{ reflexivity. } 1:{ lia. }
    1:{ rewrite unsigned_lit by lia. lia. } 1:{ rewrite unsigned_lit by lia. reflexivity. } 1:{ rewrite unsigned_lit by lia. lia. }
    clear RDS.
    intros ms' PO. destruct PO as (xa1 & xa2 & xa3 & xa4 & E & _). subst ms'.
    rewrite (unsigned_lit 0x15aa8) by lia.
    replace (ret_pc (Z_to_bv 64 0x273fc)) with (Z_to_bv 64 0x273fc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof (table_read USEGS (fun v => le8 (Z_to_bv 64 v)) LARGE_POW5 0x15aa8 8 m 0x10000 0x22000
                  U_LP5_tbl PR ltac:(lia) ltac:(cbn; lia) k ltac:(cbn; lia)) as RD.
    change (Z.of_nat 8) with 8%Z in RD. rewrite <- Hyk in RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    name_mem mc1.
    destruct (stk_split USEGS _ _ (bv_unsigned sp + -1120 - 96) _ ST ltac:(lia)) as [STlo SThi].
    clear ST.
    pose proof (unsigned_lit (bv_unsigned sp + -1120) ltac:(lia)) as ULs.
    pose proof (unsigned_lit (bv_unsigned sp + -1104) ltac:(lia)) as UL1.
    pose proof (unsigned_lit (bv_unsigned sp + -600) ltac:(lia)) as UL2.
    step. (* [comment removed for export] *)
    call extend_spec.
    1:{ eapply stk_at_eq; [exact SThi | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia]. }
    1:{ eapply u64arr_at_eq; [exact ZIA | rewrite unsigned_lit by lia; lia]. } 1:{ exact Lzi. }
    1:{ eapply rw_cells_at_eq; [exact ZIL | rewrite unsigned_lit by lia; lia]. }
    1:{ eapply u64arr_at_eq; [exact ZA | rewrite unsigned_lit by lia; lia]. } 1:{ exact Lzw. }
    1:{ rewrite unsigned_lit by lia. lia. }
    1:{ rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia. } 1:{ rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia. }
    1:{ rewrite unsigned_lit by lia. lia. } 1:{ rewrite unsigned_lit by lia. lia. } 1:{ rewrite unsigned_lit by lia. lia. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    1:{ rewrite !unsigned_lit by lia. lia. } 1:{ rewrite !unsigned_lit by lia. lia. } 1:{ rewrite !unsigned_lit by lia. lia. }
    rewrite ?ULs, ?UL1, ?UL2 in *. rewrite ?(unsigned_lit len) in * by lia.
    name_mem mc2.
    match goal with H : stk USEGS mc2 (bv_unsigned sp + -1120 - 96) _ |- _ =>
      pose proof (stk_merge USEGS mc2 _ _ _ STlo H ltac:(lia)) as ST2; clear H STlo end.
    eapply (from_25468 n IH k yk); try eassumption; try lia.
    all: lazymatch goal with
         | |- munch _ _ _ => cbv delta [iter_W]; assumption
         | |- length _ = _ => rewrite app_length, firstn_length, skipn_length, Lzw, Lzi; lia
         | |- forall j, _ -> _ => intros j Hj; rewrite app_nth1 by (rewrite firstn_length, Lzw; lia);
                                 rewrite <- (Hzw j Hj); rewrite <- (firstn_skipn (Z.to_nat len) zw) at 2; symmetry; apply app_nth1; rewrite firstn_length, Lzw; lia
         | |- rw_cells _ _ _ _ => eapply rw_cells_at_eq; [eassumption| lia]
         | _ => idtac
         end.
  Qed.

  #[using="span_index_spec extend_spec large_add_from_spec L62 Hlen A8 A0p AL SEP SPLO Rsp AROD NORM CAP Lzw Hzw Hw6"] Lemma iter_loop : forall n, iter_ok n.
  Proof. LiaFast.lf_pins (fun (span_index_spec extend_spec large_add_from_spec L62 Hlen A8 A0p AL SEP SPLO Rsp AROD NORM CAP Lzw Hzw Hw6 : LiaFast.U) => LiaFast.u0). induction n as [|n IHn]. - unfold iter_ok; intros; exfalso; lia. - apply iter_body; exact IHn. Qed.
End Iter.
End U_long_mul_B.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.ImgFacts OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_large_add_from_stmt.U_span_index_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_extend_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_large_add_from_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_normalize_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_long_mul_A OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_long_mul_B.
Import ListNotations.

Module U_copy_impl_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition copy_impl_entry : Z := 0x2781c.

(* [comment removed for export] *)
Definition copy_impl_post
    (ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a1
                 (Z_to_bv 64 (bv_unsigned a2 + (bv_unsigned a1 - bv_unsigned a0))) a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp);
              (bv_unsigned a2, bv_unsigned a2 + (bv_unsigned a1 - bv_unsigned a0))]%Z m m'
    /\ wmono USEGS m m'
    /\ u8arr USEGS m' (bv_unsigned a2) bs
    /\ stk USEGS m' (bv_unsigned sp - 32) (bv_unsigned sp).

Definition copy_impl_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z) (bs old : list byte),
    stk USEGS m (bv_unsigned sp - 32) (bv_unsigned sp) ->
    (bv_unsigned a1 = bv_unsigned a0 + n)%Z ->
    (0 <= n < 2 ^ 40)%Z -> (n mod 8 = 0)%Z ->
    bytes_at USEGS m (bv_unsigned a0) bs -> Z.of_nat (length bs) = n ->
    u8arr USEGS m (bv_unsigned a2) old -> length old = length bs ->
    (bv_unsigned a0 mod 8 = 0)%Z -> (bv_unsigned a2 mod 8 = 0)%Z ->
    (0 < bv_unsigned a0)%Z -> (0 < bv_unsigned a2)%Z -> (bv_unsigned a2 + n < 2 ^ 64)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    (bv_unsigned a2 + n <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
    (bv_unsigned a0 + n <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    evt USEGS (copy_impl_post ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2781c) fc None m (seg_rom USEGS)).
End U_copy_impl_stmt.

Module U_copy_fwd_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation USEGS := Ubsan.M.loaded_segments.

Definition copy_fwd_entry : Z := 0x277a0.

(* [comment removed for export] *)
Definition copy_fwd_post
    (ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a1
                 (Z_to_bv 64 (bv_unsigned a2 + (bv_unsigned a1 - bv_unsigned a0))) a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom USEGS)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp);
              (bv_unsigned a2, bv_unsigned a2 + (bv_unsigned a1 - bv_unsigned a0))]%Z m m'
    /\ wmono USEGS m m'
    /\ u8arr USEGS m' (bv_unsigned a2) bs
    /\ stk USEGS m' (bv_unsigned sp - 64) (bv_unsigned sp).

Definition copy_fwd_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z) (bs old : list byte),
    stk USEGS m (bv_unsigned sp - 64) (bv_unsigned sp) ->
    (bv_unsigned a1 = bv_unsigned a0 + n)%Z ->
    (0 <= n < 2 ^ 40)%Z -> (n mod 8 = 0)%Z ->
    bytes_at USEGS m (bv_unsigned a0) bs -> Z.of_nat (length bs) = n ->
    u8arr USEGS m (bv_unsigned a2) old -> length old = length bs ->
    (bv_unsigned a0 mod 8 = 0)%Z -> (bv_unsigned a2 mod 8 = 0)%Z ->
    (0 < bv_unsigned a0)%Z -> (0 < bv_unsigned a2)%Z -> (bv_unsigned a2 + n < 2 ^ 64)%Z ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    (bv_unsigned a2 + n <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
    (bv_unsigned a0 + n <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    evt USEGS (copy_fwd_post ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x277a0) fc None m (seg_rom USEGS)).
End U_copy_fwd_stmt.

Module U_copy_fwd.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl Ubsan_chk.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_copy_impl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_copy_fwd_stmt.
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
  Hypothesis copy_impl_spec : copy_impl_stmt.

  #[using="copy_impl_spec"] Lemma copy_fwd_spec : copy_fwd_stmt.
  Proof. LiaFast.lf_pins (fun (copy_impl_spec : LiaFast.U) => LiaFast.u0).
    unfold copy_fwd_stmt. intros until old. intros ST Ha1 Hn Hn8 SRC Lbs DST Lold A08 D8 A0p Dp Dn RA SEPD SEPS.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + (bv_unsigned a1 - bv_unsigned a0))]%Z m) as MU.
    replace (bv_unsigned a1 - bv_unsigned a0)%Z with n in MU by lia.
    pose proof (wmono_refl USEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0.
    pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1.
    pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2.
    assert (SPB : (0 <= bv_unsigned sp - 64)%Z) by (destruct ST as (? & ? & ?); lia).
    carve_frame 32%nat ST.
    do 4 step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    call copy_impl_spec.
    1:{ rewrite ULs. replace (bv_unsigned sp + -32 - 32)%Z with (bv_unsigned sp - 64)%Z by lia. exact ST. }
    1:{ exact Ha1. } 1:{ exact Hn. } 1:{ exact Hn8. } 1:{ exact SRC. } 1:{ exact Lbs. } 1:{ exact DST. } 1:{ exact Lold. }
    1:{ exact A08. } 1:{ exact D8. } 1:{ exact A0p. } 1:{ exact Dp. } 1:{ exact Dn. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    1:{ rewrite ULs. lia. } 1:{ rewrite ULs. lia. }
    rewrite ?ULs in *.
    replace (bv_unsigned a1 - bv_unsigned a0)%Z with n in * by lia.
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc.
    { exfalso. cond_cleanup Hc.
      replace ((bv_unsigned a2 + n - bv_unsigned a2) mod 18446744073709551616)%Z with n in Hc
        by (rewrite Z.mod_small by lia; lia).
      rewrite ?lxor_high in Hc by lia. decide_ltb_in Hc. discriminate. }
    clear Hc.
    do 5 step. (* [comment removed for export] *)
    match goal with H : stk USEGS _ _ _ |- _ => rename H into ST' end.
    replace (bv_unsigned sp + -32 - 32)%Z with (bv_unsigned sp - 64)%Z in ST' by lia.
    release_frame FR ST' (bv_unsigned sp).
    unfold copy_fwd_post. replace (bv_unsigned a1 - bv_unsigned a0)%Z with n by lia.
    finish.
    all: try eassumption. all: try lia.
    all: try (split; assumption).
  Qed.
End Main.
End U_copy_fwd.

Module U_extend.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl Ubsan_chk.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.Ubsan_chk OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_copy_fwd_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_long_mul.U_extend_stmt.
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

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Section Main.
  Hypothesis copy_fwd_spec : copy_fwd_stmt.

  #[using="copy_fwd_spec"] Lemma extend_spec : extend_stmt.
  Proof. LiaFast.lf_pins (fun (copy_fwd_spec : LiaFast.U) => LiaFast.u0).
    unfold extend_stmt. intros until sws. intros ST VA Lv VLEN SA Ls Hcnt V8 S8 Vp Sp Sn RA SEPV SEPS SEPVS.
    pose proof (munch_refl (extend_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU. cbv delta [extend_W] in MU.
    pose proof (wmono_refl USEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2.
    pose proof (u64arr_bound _ _ _ _ VA) as Bv. rewrite Lv in Bv.
    pose proof (u64arr_bound _ _ _ _ SA) as Bs. rewrite Ls in Bs.
    pose proof (rw_cells_bound _ _ _ _ VLEN) as Bc. cbn [cells_size csize Nat.add] in Bc.
    assert (SPB : (0 <= bv_unsigned sp - 96)%Z) by (destruct ST as (? & ? & ?); lia).
    remember (bv_unsigned a2) as c eqn:Ec.
    destruct (Z_of_nat_complete c ltac:(lia)) as [cn Ecn].
    carve_frame 32%nat ST.
    do 4 step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite zx16_lit_small by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    zstep. (* [comment removed for export] *)
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z. rewrite <- ?Ec.
    zstep. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite <- ?Ec.
    zstep. (* [comment removed for export] *)
    rewrite (Z.shiftr_div_pow2 _ 61), (Z.div_small) by lia.
    step. (* [comment removed for export] *)
    kill_check.
    zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    rewrite <- ?Ec.
    step. (* [comment removed for export] *)
    kill_check.
    zstep. (* [comment removed for export] *)
    rewrite ?Z.shiftl_0_l, ?Z.add_0_r.
    step. step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    name_mem mc1.
    pose proof (u64arr_prefix_bytes USEGS mc1 _ sws cn ltac:(rewrite Ls; lia) SA) as SRC.
    destruct (u64arr_split3 USEGS mc1 _ vws 0 cn ltac:(rewrite Lv; lia) VA) as (_ & U2 & U3).
    pose proof (u8arr_of_u64arr USEGS _ _ _ U2) as DST.
    destruct (u64arr_len_split3 vws 0 cn ltac:(rewrite Lv; lia)) as (_ & _ & Ll & Lr). rewrite Lv in Lr.
    cbn [firstn skipn Nat.add app] in DST, U3, Ll, Lr.
    clear VA U2.
    pose proof (unsigned_lit (c * 8 + bv_unsigned a1) ltac:(lia)) as UL1.
    pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    eapply evt_cut; [ eapply copy_fwd_spec with (n := (8 * c)%Z) | post_call USEGS mc1 ].
    1:{ rewrite ULs. replace (bv_unsigned sp + -32 - 64)%Z with (bv_unsigned sp - 96)%Z by lia. exact ST. }
    1:{ rewrite UL1. lia. } 1:{ lia. } 1:{ rewrite Z.mul_comm. apply Z_mod_mult. }
    1:{ exact SRC. } 1:{ rewrite u64s_length, firstn_length, Ls. lia. }
    1:{ eapply u8arr_at_eq; [exact DST| lia]. } 1:{ rewrite !u64s_length, Ll, firstn_length, Ls. lia. }
    1:{ exact S8. } 1:{ exact V8. } 1:{ exact Sp. } 1:{ exact Vp. } 1:{ lia. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    1:{ rewrite ULs. lia. } 1:{ rewrite ULs. lia. }
    rewrite ?UL1, ?ULs in *.
    name_mem mc2.
    match goal with H : u8arr USEGS mc2 _ (u64s (firstn cn sws)) |- _ =>
      pose proof (u64arr_of_u8arr USEGS mc2 _ cn (u64s (firstn cn sws)) H
                  ltac:(rewrite u64s_length, firstn_length, Ls; lia)) as MID; clear H end.
    rewrite words_of_bytes_u64s in MID.
    assert (Lm : length (firstn cn sws) = cn) by (rewrite firstn_length, Ls; lia).
    assert (CUR2 : u64arr USEGS mc2 (bv_unsigned a0) (firstn cn sws ++ skipn cn vws)).
    { apply u64arr_app. rewrite Lm. split; [exact MID|]. eapply u64arr_at_eq; [exact U3| lia]. }
    clear MID U3.
    step. (* [comment removed for export] *)
    rewrite sx16_lit_small by lia.
    zstep. (* [comment removed for export] *)
    rewrite <- ?Ec. rewrite ?Z.add_0_l.
    step. (* [comment removed for export] *)
    do 5 step.
    match goal with H : stk USEGS _ _ _ |- _ => rename H into ST' end.
    replace (bv_unsigned sp + -32 - 64)%Z with (bv_unsigned sp - 96)%Z in ST' by lia.
    release_frame FR ST' (bv_unsigned sp).
    unfold extend_post. finish.
    all: try (cbv delta [extend_W]; assumption). all: try eassumption. all: try lia.
    all: try (replace (Z.to_nat c) with cn by lia; exact CUR2).
  Qed.
End Main.
End U_extend.

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

Section Main.
  Hypothesis span_index_spec : span_index_stmt.
  Hypothesis extend_spec : extend_stmt.
  Hypothesis large_add_from_spec : large_add_from_stmt.
  Hypothesis normalize_spec : normalize_stmt.

  Section From20.
  Variables (ra sp gp tp a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s0 s1 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (ws zw : list word) (len : Z) (j0 j1 j3 j4 : list byte).
  Notation A := (bv_unsigned a0).
  Notation SP' := (bv_unsigned sp + -1120)%Z.
  Notation X := (bval ws (Z.to_nat len)).
  Notation POST := (long_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A ws len m).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis A8 : (A mod 8 = 0)%Z.
  Hypothesis A0p : (0 < A)%Z.
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SEP : (A + 498 <= bv_unsigned sp - 1232 \/ bv_unsigned sp <= A)%Z.
  Hypothesis SPLO : (0x22000 <= bv_unsigned sp - 1232)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.
  Hypothesis AROD : (A + 498 <= 0x10000 \/ 0x22000 <= A)%Z.
  Hypothesis NORM : bnorm ws (Z.to_nat len).
  Hypothesis CAP : (X * 5 ^ 135 < BIG_CAP)%Z.
  Hypothesis Lzw : length zw = 62%nat.
  Hypothesis Hzw : forall j, (j < Z.to_nat len)%nat -> nth j zw w0 = nth j ws w0.

  (* [comment removed for export] *)
  #[using="span_index_spec extend_spec large_add_from_spec normalize_spec L62 Hlen A8 A0p AL SEP SPLO Rsp AROD NORM CAP Lzw Hzw"] Lemma from_25420 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word)
      (m1 : word -> option byte) (wsk : list word) (lenk : Z) (ziw : list word) (j5 : list byte),
      u64arr USEGS m1 A wsk -> length wsk = 62%nat ->
      rw_cells USEGS m1 (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bval wsk (Z.to_nat lenk) = (X * nth 0 LARGE_POW5 0%Z)%Z ->
      u64arr USEGS m1 (bv_unsigned sp + -1104) ziw -> length ziw = 62%nat ->
      rw_cells USEGS m1 (bv_unsigned sp + -608) [CB 2 j0] ->
      rw_cells USEGS m1 (bv_unsigned sp + -606) [CB 6 j1] ->
      u64arr USEGS m1 (bv_unsigned sp + -600) zw ->
      rw_cells USEGS m1 (bv_unsigned sp + -104) [C2 (Z_to_bv 64 len)] ->
      rw_cells USEGS m1 (bv_unsigned sp + -102) [CB 6 j3] ->
      rw_cells USEGS m1 (bv_unsigned sp + -96) [C8 (Z_to_bv 64 0x15aa8); C8 (Z_to_bv 64 5)] ->
      rw_cells USEGS m1 (bv_unsigned sp + -1120) [CB 16 j5] ->
      rw_cells USEGS m1 (bv_unsigned sp + -80)
        [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk USEGS m1 (bv_unsigned sp - 1232) SP' ->
      pristine m1 0x10000 0x22000 ->
      munch [(bv_unsigned sp - 1232, bv_unsigned sp); (A, A + 498)]%Z m m1 -> wmono USEGS m m1 ->
      evt USEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 a0 (Z_to_bv 64 len) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 0x15aa8) (Z_to_bv 64 5) x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x273d4) fc None m1 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (span_index_spec extend_spec large_add_from_spec normalize_spec L62 Hlen A8 A0p AL SEP SPLO Rsp AROD NORM CAP Lzw Hzw : LiaFast.U) => LiaFast.u0).
    intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 m1 wsk lenk ziw j5
           XA Lx LENC Hlenk VAL1 ZIA Lzi ZIL PAD1 ZA ZL PAD2 SPAN FR0 FRsv ST PR MU WM.
    destruct (rw_cells_CB2_C2 _ _ _ _ _ ZIL) as (zil & Hzil & ZIL'). clear ZIL. rename ZIL' into ZIL.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- context [Z_to_bv 64 (Z.lxor ?u 18446744073709551615)] =>
      remember (Z_to_bv 64 (Z.lxor u 18446744073709551615)) as w6 eqn:Ew6 end.
    assert (Hw6 : (bv_unsigned w6 = 2 ^ 64 - 1 - (bv_unsigned sp + -1104))%Z).
    { subst w6. rewrite (unsigned_lit (bv_unsigned sp + -1104)) by lia. rewrite zb_lxor_ones by lia. rewrite unsigned_lit by lia. lia. }
    clear Ew6.
    name_mem mc.
    call (iter_loop span_index_spec extend_spec large_add_from_spec sp a0 gp tp w6 s9 s10 s11 F fc ws zw len j1
             L62 Hlen A8 A0p AL SEP SPLO Rsp AROD NORM CAP Lzw Hzw Hw6 (Z.to_nat 4) mc 1%Z).
    all: try lia.
    1:{ exact XA. } 1:{ exact Lx. } 1:{ exact LENC. } 1:{ exact Hlenk. }
    1:{ rewrite VAL1. change (Z.to_nat 1) with 1%nat. rewrite zsum_S. cbn [zsum Z.of_nat Z.mul]. rewrite Z.pow_0_r. ring. }
    1:{ exact ZIA. } 1:{ exact Lzi. } 1:{ exact ZIL. } 1:{ exact PAD1. } 1:{ exact ZA. } 1:{ exact SPAN. } 1:{ exact ST. } 1:{ exact PR. }
    1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    (* [comment removed for export] *)
    name_mem m5.
    match goal with H : rw_cells USEGS m5 (A + 496) [C2 (Z_to_bv 64 ?l)] |- _ => rename H into LENC5; rename l into len5 end.
    match goal with H : u64arr USEGS m5 A ?w |- _ => rename H into XA5; rename w into ws5 end.
    match goal with H : length ws5 = 62%nat |- _ => rename H into L5 end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call normalize_spec.
    1:{ exact XA5. } 1:{ exact L5. } 1:{ exact LENC5. } 1:{ lia. }
    name_mem m6.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    do 12 step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    match goal with H : stk USEGS m6 _ _ |- _ => rename H into ST6 end.
    match goal with H : rw_cells USEGS m6 (bv_unsigned sp + -1120) _ |- _ => release_frame H ST6 (bv_unsigned sp + -1104)%Z end.
    match goal with H : u64arr USEGS m6 (bv_unsigned sp + -1104) ?w |- _ =>
      pose proof (rw_cells_of_u64arr _ _ _ _ H) as ZIc; clear H;
      match goal with L : length w = 62%nat |- _ => rewrite L in ZIc end end.
    release_frame ZIc ST6 (bv_unsigned sp + -608)%Z.
    match goal with H : rw_cells USEGS m6 (bv_unsigned sp + -608) _ |- _ => release_frame H ST6 (bv_unsigned sp + -606)%Z end.
    match goal with H : rw_cells USEGS m6 (bv_unsigned sp + -606) _ |- _ => release_frame H ST6 (bv_unsigned sp + -600)%Z end.
    match goal with H : u64arr USEGS m6 (bv_unsigned sp + -600) ?w |- _ =>
      pose proof (rw_cells_of_u64arr _ _ _ _ H) as ZAc; clear H; rewrite Lzw in ZAc end.
    release_frame ZAc ST6 (bv_unsigned sp + -104)%Z.
    release_frame ZL ST6 (bv_unsigned sp + -102)%Z.
    release_frame PAD2 ST6 (bv_unsigned sp + -96)%Z.
    release_frame SPAN ST6 (bv_unsigned sp + -80)%Z.
    release_frame FRsv ST6 (bv_unsigned sp).
    unfold long_mul_post. finish.
    all: try eassumption. all: try lia.
    all: try (pose proof (norm_len_le ws5 (Z.to_nat len5)); lia).
    - rewrite Nat2Z.id. rewrite norm_len_bval. match goal with H : bval ws5 (Z.to_nat len5) = _ |- _ => exact H end.
    - rewrite Nat2Z.id. apply norm_len_bnorm.
  Qed.
  End From20.

  #[using="span_index_spec extend_spec large_add_from_spec normalize_spec"] Lemma long_mul_spec : long_mul_stmt.
  Proof. LiaFast.lf_pins (fun (span_index_spec extend_spec large_add_from_spec normalize_spec : LiaFast.U) => LiaFast.u0).
    unfold long_mul_stmt. intros until len. intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 A0p NORM Ha1 Ha2 CAP SEP.
    subst a1 a2. cbv delta [U_LARGE_POW5_ADDR].
    pose proof (munch_refl [(bv_unsigned sp - 1232, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 498)]%Z m) as MU.
    pose proof (wmono_refl USEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    pose proof (u64arr_outside_rodata_U m _ _ PR LIMBS ltac:(rewrite L62; lia)) as AROD. rewrite L62 in AROD.
    pose proof (rw_cells_outside_rodata_U m _ _ PR LENC ltac:(cbn; lia)) as CROD. cbn [cells_size csize Nat.add] in CROD.
    assert (HA : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 498 <= 2 ^ 64)%Z) by lia.
    assert (AROD' : (bv_unsigned a0 + 498 <= 0x10000 \/ 0x22000 <= bv_unsigned a0)%Z) by lia.
    clear Bl Bc AROD CROD. rename AROD' into AROD.
    assert (SPB : (0 <= bv_unsigned sp - 1232)%Z) by lia.
    (* [comment removed for export] *)
    carve_frame 1120%nat ST.
    apply (rw_cells_split_CB USEGS m _ [] 1120%nat junk [] [16;496;2;6;496;2;6;8;8;80]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    chunk_split FR 9%nat FRlo FRsv.
    chunk_split FRlo 1%nat FR0 FR1. chunk_split FR1 1%nat ZI FR2. chunk_split FR2 1%nat ZIL FR3. chunk_split FR3 1%nat PAD1 FR4.
    chunk_split FR4 1%nat ZZ FR5. chunk_split FR5 1%nat ZL FR6. chunk_split FR6 1%nat PAD2 SPAN.
    match type of ZI with context [CB 496 ?j] => remember j as zij eqn:E1 in ZI; clear E1 end.
    match type of ZZ with context [CB 496 ?j] => remember j as zj eqn:E1 in ZZ; clear E1 end.
    match type of FRsv with context [CB 80 ?j] => remember j as svj eqn:E1 in FRsv; clear E1 end.
    match type of ZIL with context [CB 2 ?j] => remember j as j0 eqn:E1 in ZIL; clear E1 end.
    match type of PAD1 with context [CB 6 ?j] => remember j as j1 eqn:E1 in PAD1; clear E1 end.
    match type of ZL with context [CB 2 ?j] => remember j as j4 eqn:E1 in ZL; clear E1 end.
    match type of PAD2 with context [CB 6 ?j] => remember j as j3 eqn:E1 in PAD2; clear E1 end.
    match type of FR0 with context [CB 16 ?j] => remember j as j5 eqn:E1 in FR0; clear E1 end.
    match type of SPAN with context [CB 8 ?j] => remember j as j6 eqn:E1 in SPAN; clear E1 end.
    match type of SPAN with context [CB 8 (firstn ?a ?b)] => remember (firstn a b) as j7 eqn:E1 in SPAN; clear E1 end.
    clear junk.
    change (CB 496 zij) with (CB (8 * 62) zij) in ZI. change (CB 496 zj) with (CB (8 * 62) zj) in ZZ.
    destruct (u64arr_of_rw_cells USEGS _ _ 62 _ ZI) as (ziw & Lzi & ZIA). clear ZI.
    destruct (u64arr_of_rw_cells USEGS _ _ 62 _ ZZ) as (zw0 & Lz0 & ZA). clear ZZ.
    do 11 step. (* [comment removed for export] *)
    step. step. step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite zx16_lit_small by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    destruct (Z_of_nat_complete len ltac:(lia)) as [ln El].
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    name_mem mc1.
    destruct (stk_split USEGS _ _ (bv_unsigned sp + -1120 - 96) _ ST ltac:(lia)) as [STlo SThi]. clear ST.
    pose proof (unsigned_lit (bv_unsigned sp + -600) ltac:(lia)) as UL2.
    pose proof (unsigned_lit (bv_unsigned sp + -1120) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    call extend_spec.
    1:{ eapply stk_at_eq; [exact SThi | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia]. }
    1:{ eapply u64arr_at_eq; [exact ZA | rewrite unsigned_lit by lia; lia]. } 1:{ exact Lz0. }
    1:{ eapply rw_cells_at_eq; [exact ZL | rewrite unsigned_lit by lia; lia]. }
    1:{ exact LIMBS. } 1:{ exact L62. }
    1:{ rewrite unsigned_lit by lia. lia. }
    1:{ rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia. } 1:{ exact A8. }
    1:{ rewrite unsigned_lit by lia. lia. } 1:{ exact A0p. } 1:{ lia. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    1:{ rewrite !unsigned_lit by lia. lia. } 1:{ rewrite !unsigned_lit by lia. lia. } 1:{ rewrite !unsigned_lit by lia. lia. }
    rewrite ?UL2, ?ULs in *. rewrite ?(unsigned_lit len) in * by lia.
    name_mem mc2.
    match goal with H : stk USEGS mc2 (bv_unsigned sp + -1120 - 96) _ |- _ =>
      pose proof (stk_merge USEGS mc2 _ _ _ STlo H ltac:(lia)) as ST; clear H STlo end.
    match goal with H : u64arr USEGS mc2 _ (firstn _ ws ++ skipn _ zw0) |- _ =>
      pose proof (u64arr_at_eq _ _ _ (bv_unsigned sp + -600) _ H ltac:(lia)) as ZA2; clear H end.
    match goal with H : rw_cells USEGS mc2 _ [C2 (Z_to_bv 64 len)] |- _ =>
      pose proof (rw_cells_at_eq _ _ _ (bv_unsigned sp + -104) _ H ltac:(lia)) as ZL2; clear H end.
    remember (firstn (Z.to_nat len) ws ++ skipn (Z.to_nat len) zw0) as zw eqn:Ezw.
    assert (Lzw : length zw = 62%nat). { subst zw. rewrite app_length, firstn_length, skipn_length, L62, Lz0. lia. }
    assert (Hzw : forall j, (j < Z.to_nat len)%nat -> nth j zw w0 = nth j ws w0).
    { intros j Hj. subst zw. rewrite app_nth1 by (rewrite firstn_length, L62; lia).
      rewrite <- (firstn_skipn (Z.to_nat len) ws) at 2. symmetry. apply app_nth1. rewrite firstn_length, L62; lia. }
    clear Ezw.
    step. (* [comment removed for export] *)
    rewrite zx16_lit_small by lia.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    kill_check.
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    kill_check.
    step. (* [comment removed for export] *)
    rewrite zx16_lit_small by lia.
    step. (* [comment removed for export] *)
    if_cases Hz.
    - (* [comment removed for export] *)
      cond_cleanup Hz.
      eapply (from_25420 ra sp gp tp a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 s1 F fc m ws zw len j0 j1 j3);
        try eassumption; try lia.
      all: rewrite Hz; change (Z.to_nat 0) with 0%nat; rewrite bval_0; ring.
    - cond_cleanup Hz.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      remember ((((0 - bv_unsigned a0) mod 18446744073709551616) ≫ 3))%Z as NA eqn:HNA.
      assert (HNA' : (NA = (2 ^ 64 - bv_unsigned a0) / 8)%Z).
      { subst NA. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3)%Z with 8%Z. f_equal.
        symmetry. apply (Z.mod_unique_pos _ _ (-1)); lia. }
      clear HNA.
      name_mem mc3.
      call (@usmul1_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               F fc mc3 (bv_unsigned a0) 1414648277510068013 NA ws len L62 ltac:(lia) ltac:(lia) ltac:(lia) HNA' a0).
      all: try lia.
      1:{ exact LIMBS. } 1:{ exact L62. } 1:{ intros j; reflexivity. }
      match goal with H : smul_inv _ _ _ _ ?c |- _ => rename H into INV1; rename c into c1 end.
      match goal with H : u64arr USEGS _ (bv_unsigned a0) ?cur |- _ => rename H into CUR1 end.
      pose proof INV1 as (Hv1 & Hag1 & Hc1 & Hlc1).
      pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
      assert (CAP1 : (1414648277510068013 * bval ws (Z.to_nat len) < BIG_CAP)%Z).
      { pose proof (LP5_zsum_step_le 0 ltac:(lia)) as ST0. cbn [zsum nth LARGE_POW5 Z.of_nat Z.mul] in ST0.
        unfold BIG_CAP in *. nia. }
      step. (* [comment removed for export] *)
      if_cases Hcz.
      + cond_cleanup Hcz.
        eapply (from_25420 ra sp gp tp a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 s1 F fc m ws zw len j0 j1 j3);
          try eassumption; try lia.
        all: cbn [nth LARGE_POW5]; rewrite (Z.mul_comm (bval ws _)); apply (smul_inv_finish_nocarry ws _ _ (Z.to_nat len));
             rewrite <- Hcz; exact INV1.
      + cond_cleanup Hcz.
        pose proof (smul_carry_room ws _ _ _ _ INV1 ltac:(lia) CAP1) as ROOM1.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_not_taken.
        zstep. (* [comment removed for export] *)
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        kill_check.
        zstep. (* [comment removed for export] *)
        replace (bv_unsigned a0 + len * 8)%Z with (bv_unsigned a0 + 8 * len)%Z by lia.
        zstep. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          pose proof (u64arr_store_ok USEGS mc _ _ len (Z_to_bv 64 (bv_unsigned a0 + 8 * len)) CUR1 ltac:(rewrite Hlc1, L62; lia) eq_refl) as SOK end.
        step. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
          pose proof (u64arr_write USEGS mc _ _ len (Z_to_bv 64 c1) CUR1 ltac:(rewrite Hlc1, L62; lia)) as CUR2 end.
        store_done.
        step. (* [comment removed for export] *)
        eapply (from_25420 ra sp gp tp a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 s1 F fc m ws zw len j0 j1 j3);
          try eassumption; try lia.
        all: first [ rewrite upd_length, Hlc1; exact L62
                   | cbn [nth LARGE_POW5]; replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia;
                     rewrite (Z.mul_comm (bval ws _)); apply (smul_inv_finish_carry ws _ _ (Z.to_nat len)); [exact INV1| rewrite L62; lia] ].
  Qed.
End Main.
