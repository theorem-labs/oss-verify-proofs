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
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl ImgFacts.

Module P_long_mul_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation PSEGS := Plain.M.loaded_segments.

Definition long_mul_entry : Z := 0x26478.
Definition long_mul_need : Z := 1168.
Definition P_LARGE_POW5_ADDR : Z := 0x15aa0.

Definition long_mul_W (sp A : Z) : list ivl := [(sp - 1168, sp); (A, A + 498)]%Z.

Definition long_mul_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A : Z) (ws : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom PSEGS)
    /\ munch (long_mul_W (bv_unsigned sp) A) m m'
    /\ wmono PSEGS m m'
    /\ stk PSEGS m' (bv_unsigned sp - 1168) (bv_unsigned sp)
    /\ u64arr PSEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (0 <= len' <= 62)%Z
    /\ bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) * 5 ^ 135)%Z
    /\ bnorm ws' (Z.to_nat len')
    /\ pristine m' 0x10000 0x22000.

Definition long_mul_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    stk PSEGS m (bv_unsigned sp - 1168) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (0x22000 <= bv_unsigned sp - 1168)%Z ->
    pristine m 0x10000 0x22000 ->
    u64arr PSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells PSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> (bv_unsigned a0 mod 8 = 0)%Z ->
    bnorm ws (Z.to_nat len) ->
    a1 = Z_to_bv 64 P_LARGE_POW5_ADDR -> a2 = Z_to_bv 64 5 ->
    (bval ws (Z.to_nat len) * 5 ^ 135 < BIG_CAP)%Z ->
    (bv_unsigned a0 + 498 <= bv_unsigned sp - 1168 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    evt PSEGS (long_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) ws len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x26478) fc None m (seg_rom PSEGS)).
End P_long_mul_stmt.

Module P_large_mul_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_long_mul_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation PSEGS := Plain.M.loaded_segments.

Definition large_mul_entry : Z := 0x263ec.
Definition large_mul_need : Z := 1184.

Definition large_mul_W (sp A : Z) : list ivl := [(sp - 1184, sp); (A, A + 498)]%Z.

Definition large_mul_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A : Z) (ws : list word) (len : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom PSEGS)
    /\ munch (large_mul_W (bv_unsigned sp) A) m m'
    /\ wmono PSEGS m m'
    /\ stk PSEGS m' (bv_unsigned sp - 1184) (bv_unsigned sp)
    /\ u64arr PSEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (0 <= len' <= 62)%Z
    /\ bval ws' (Z.to_nat len') = (bval ws (Z.to_nat len) * 5 ^ 135)%Z
    /\ bnorm ws' (Z.to_nat len')
    /\ pristine m' 0x10000 0x22000.

Definition large_mul_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z),
    stk PSEGS m (bv_unsigned sp - 1184) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (0x22000 <= bv_unsigned sp - 1184)%Z ->
    pristine m 0x10000 0x22000 ->
    u64arr PSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells PSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> (bv_unsigned a0 mod 8 = 0)%Z ->
    bnorm ws (Z.to_nat len) ->
    a1 = Z_to_bv 64 P_LARGE_POW5_ADDR -> a2 = Z_to_bv 64 5 ->
    (bval ws (Z.to_nat len) * 5 ^ 135 < BIG_CAP)%Z ->
    (bv_unsigned a0 + 498 <= bv_unsigned sp - 1184 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    evt PSEGS (large_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) ws len m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x263ec) fc None m (seg_rom PSEGS)).
End P_large_mul_stmt.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5_stmt.

Module P_pow5_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs.StoreFast.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation PSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section smulM.
  Variables (x1 x2 x3 x4 x6 x7 x8 x9 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (A y : Z) (ws : list word) (len : Z).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis Hy : (0 <= y < 2 ^ 64)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.

  Definition smulM_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (c' : Z) (thi tlo : word) (m' : word -> option byte) (cur : list word),
      ms' = MS (mkR x1 x2 x3 x4 thi x6 x7 x8 x9 (Z_to_bv 64 y) x11 x12 x13 (Z_to_bv 64 (A + 8 * len)) (Z_to_bv 64 c') (Z_to_bv 64 (A + 8 * len)) tlo x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x2633c) fc None m' (seg_rom PSEGS)
      /\ munch [(A, A + 8 * len)]%Z m m'
      /\ wmono PSEGS m m'
      /\ u64arr PSEGS m' A cur
      /\ length cur = 62%nat
      /\ smul_inv ws cur y (Z.to_nat len) c'.

  Definition smulM_ok (k : nat) : Prop :=
    forall (i : nat) (p thi tlo : word) (c : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      u64arr PSEGS m A cur -> length cur = 62%nat ->
      smul_inv ws cur y i c ->
      munch [(A, A + 8 * len)]%Z m0 m -> wmono PSEGS m0 m ->
      evt PSEGS (smulM_post m0)
        (MS (mkR x1 x2 x3 x4 thi x6 x7 x8 x9 (Z_to_bv 64 y) x11 x12 x13 (Z_to_bv 64 (A + 8 * len)) (Z_to_bv 64 c) p tlo x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26318) fc None m (seg_rom PSEGS)).

  #[using="L62 LEN Hy HA"] Lemma smulM_body : forall k, smulM_ok k -> smulM_ok (S k).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold smulM_ok. intros i p thi tlo c cur m Hk Hi Hp CUR Hcur INV MU WM.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    destruct INV as (Hv & Hag & Hc & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (u64arr_read PSEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit y), ?(unsigned_lit c) by lia.
    pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write PSEGS m A cur (Z.of_nat i) (Z_to_bv 64 (bv_unsigned w * y + c)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(lm_smul_carry_word (bv_unsigned w) y c), ?(lm_smul_carry_word' (bv_unsigned w) y c) by lia.
    assert (INV' : smul_inv ws (upd cur i (Z_to_bv 64 (bv_unsigned w * y + c))) y (S i) (mul_cout (limbZ ws i) y c)).
    { replace (bv_unsigned w * y)%Z with (limbZ ws i * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply smul_inv_step; [split; [exact Hv| split; [exact Hag| split; [exact Hc| exact Hlc]]] | lia | rewrite L62; lia |].
      unfold limbZ. rewrite <- Hw. apply lm_smul_lo_word; lia. }
    replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
    step. (* [comment removed for export] *)
    if_cases Hb.
    - cond_cleanup Hb.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite upd_length. exact Hcur.
    - cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      apply evt_done. unfold smulM_post.
      eexists (mul_cout (limbZ ws i) y c), _, _, m1, (upd cur i (Z_to_bv 64 (limbZ ws i * y + c))).
      split. { f_equal. replace (bv_unsigned p + 8)%Z with (A + 8 * len)%Z by lia. reflexivity. }
      split; [exact MU|]. split; [exact WM|].
      split. { replace (limbZ ws i) with (bv_unsigned w) by (unfold limbZ; rewrite <- Hw; reflexivity). exact CUR'. }
      split; [rewrite upd_length; exact Hcur|].
      rewrite <- Hil. replace (limbZ ws i * y)%Z with (bv_unsigned w * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity). exact INV'.
  Qed.

  #[using="L62 LEN Hy HA"] Lemma smulM_loop : forall k, smulM_ok k.
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0). induction k as [|k IH]. - unfold smulM_ok; intros; exfalso; lia. - apply smulM_body; exact IH. Qed.

  #[using="L62 LEN Hy HA"] Lemma smulM_run : forall (p thi tlo : word) (cur : list word),
    bv_unsigned p = A ->
    u64arr PSEGS m0 A cur -> length cur = 62%nat -> (forall j, nth j cur w0 = nth j ws w0) ->
    evt PSEGS (smulM_post m0)
      (MS (mkR x1 x2 x3 x4 thi x6 x7 x8 x9 (Z_to_bv 64 y) x11 x12 x13 (Z_to_bv 64 (A + 8 * len)) (Z_to_bv 64 0) p tlo x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x26318) fc None m0 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0).
    intros p thi tlo cur Hp CUR Hcur Hag.
    eapply (smulM_loop (Z.to_nat len) 0%nat); try eassumption; try lia.
    - split; [cbn; lia|]. split; [intros; apply Hag|]. split; [lia|]. rewrite Hcur, L62. reflexivity.
    - apply munch_refl.
    - apply wmono_refl.
  Qed.
End smulM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section smulF.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (A y : Z) (ws : list word) (len : Z).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis Hy : (0 <= y < 2 ^ 64)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.

  Definition smulF_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (c' : Z) (thi tlo : word) (m' : word -> option byte) (cur : list word),
      ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 c') (Z_to_bv 64 (A + 8 * len)) (Z_to_bv 64 y) (Z_to_bv 64 (A + 8 * len)) tlo thi x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x263b0) fc None m' (seg_rom PSEGS)
      /\ munch [(A, A + 8 * len)]%Z m m'
      /\ wmono PSEGS m m'
      /\ u64arr PSEGS m' A cur
      /\ length cur = 62%nat
      /\ smul_inv ws cur y (Z.to_nat len) c'.

  Definition smulF_ok (k : nat) : Prop :=
    forall (i : nat) (p thi tlo : word) (c : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      u64arr PSEGS m A cur -> length cur = 62%nat ->
      smul_inv ws cur y i c ->
      munch [(A, A + 8 * len)]%Z m0 m -> wmono PSEGS m0 m ->
      evt PSEGS (smulF_post m0)
        (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 c) (Z_to_bv 64 (A + 8 * len)) (Z_to_bv 64 y) p tlo thi x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2638c) fc None m (seg_rom PSEGS)).

  #[using="L62 LEN Hy HA"] Lemma smulF_body : forall k, smulF_ok k -> smulF_ok (S k).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold smulF_ok. intros i p thi tlo c cur m Hk Hi Hp CUR Hcur INV MU WM.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    destruct INV as (Hv & Hag & Hc & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (u64arr_read PSEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit y), ?(unsigned_lit c) by lia.
    pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write PSEGS m A cur (Z.of_nat i) (Z_to_bv 64 (bv_unsigned w * y + c)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(lm_smul_carry_word (bv_unsigned w) y c), ?(lm_smul_carry_word' (bv_unsigned w) y c) by lia.
    assert (INV' : smul_inv ws (upd cur i (Z_to_bv 64 (bv_unsigned w * y + c))) y (S i) (mul_cout (limbZ ws i) y c)).
    { replace (bv_unsigned w * y)%Z with (limbZ ws i * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply smul_inv_step; [split; [exact Hv| split; [exact Hag| split; [exact Hc| exact Hlc]]] | lia | rewrite L62; lia |].
      unfold limbZ. rewrite <- Hw. apply lm_smul_lo_word; lia. }
    replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
    step. (* [comment removed for export] *)
    if_cases Hb.
    - cond_cleanup Hb.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite upd_length. exact Hcur.
    - cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      apply evt_done. unfold smulF_post.
      eexists (mul_cout (limbZ ws i) y c), _, _, m1, (upd cur i (Z_to_bv 64 (limbZ ws i * y + c))).
      split. { f_equal. replace (bv_unsigned p + 8)%Z with (A + 8 * len)%Z by lia. reflexivity. }
      split; [exact MU|]. split; [exact WM|].
      split. { replace (limbZ ws i) with (bv_unsigned w) by (unfold limbZ; rewrite <- Hw; reflexivity). exact CUR'. }
      split; [rewrite upd_length; exact Hcur|].
      rewrite <- Hil. replace (limbZ ws i * y)%Z with (bv_unsigned w * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity). exact INV'.
  Qed.

  #[using="L62 LEN Hy HA"] Lemma smulF_loop : forall k, smulF_ok k.
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0). induction k as [|k IH]. - unfold smulF_ok; intros; exfalso; lia. - apply smulF_body; exact IH. Qed.

  #[using="L62 LEN Hy HA"] Lemma smulF_run : forall (p thi tlo : word) (cur : list word),
    bv_unsigned p = A ->
    u64arr PSEGS m0 A cur -> length cur = 62%nat -> (forall j, nth j cur w0 = nth j ws w0) ->
    evt PSEGS (smulF_post m0)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 0) (Z_to_bv 64 (A + 8 * len)) (Z_to_bv 64 y) p tlo thi x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x2638c) fc None m0 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0).
    intros p thi tlo cur Hp CUR Hcur Hag.
    eapply (smulF_loop (Z.to_nat len) 0%nat); try eassumption; try lia.
    - split; [cbn; lia|]. split; [intros; apply Hag|]. split; [lia|]. rewrite Hcur, L62. reflexivity.
    - apply munch_refl.
    - apply wmono_refl.
  Qed.
End smulF.
End P_pow5_A.


Module P_pow5_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs.StoreFast.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Bigint_shl.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_large_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_pow5_A.
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
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SEP : (A + 498 <= bv_unsigned sp - 1232 \/ bv_unsigned sp <= A)%Z.
  Hypothesis SPLO : (0x22000 <= bv_unsigned sp - 1232)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.
  Hypothesis AROD : (A + 498 <= 0x10000 \/ 0x22000 <= A)%Z.
  Hypothesis He0 : (0 <= e0 < 2 ^ 31)%Z.
  Hypothesis CAP : (X * 5 ^ e0 < BIG_CAP)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition big_W : list ivl := [(bv_unsigned sp - 1232, SP'); (A, A + 498)]%Z.

  Definition big_post (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (e' : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
                      (m' : word -> option byte) (wsk : list word) (lenk : Z),
      ms' = MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e') x10 x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 0x15aa0) (Z_to_bv 64 134) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x262e8) fc None m' (seg_rom PSEGS)
      /\ munch big_W m0 m'
      /\ wmono PSEGS m0 m'
      /\ u64arr PSEGS m' A wsk /\ length wsk = 62%nat
      /\ rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 lenk)] /\ (0 <= lenk <= 62)%Z
      /\ bnorm wsk (Z.to_nat lenk)
      /\ (0 <= e' < 135)%Z /\ (e' <= e0)%Z
      /\ bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e'))%Z
      /\ stk PSEGS m' (bv_unsigned sp - 1232) SP'
      /\ pristine m' 0x10000 0x22000.

  Definition big_ok (n : nat) : Prop :=
    forall (m0 : word -> option byte) (e : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m : word -> option byte) (wsk : list word) (lenk : Z),
      (Z.to_nat e <= n)%nat -> (135 <= e <= e0)%Z ->
      u64arr PSEGS m A wsk -> length wsk = 62%nat ->
      rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e))%Z ->
      stk PSEGS m (bv_unsigned sp - 1232) SP' ->
      pristine m 0x10000 0x22000 ->
      munch big_W m0 m -> wmono PSEGS m0 m ->
      evt PSEGS (big_post m0)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 0x15aa0) (Z_to_bv 64 134) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x262cc) fc None m (seg_rom PSEGS)).

  #[using="large_mul_spec L62 A8 AL SEP SPLO Rsp HA AROD He0 CAP"] Lemma big_body : forall n, big_ok n -> big_ok (S n).
  Proof. LiaFast.lf_pins (fun (large_mul_spec L62 A8 AL SEP SPLO Rsp HA AROD He0 CAP : LiaFast.U) => LiaFast.u0).
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
    1:{ rewrite ULs. replace (SP' - 1184)%Z with (bv_unsigned sp - 1232)%Z by lia. exact ST. }
    1:{ rewrite ULs. Z.div_mod_to_equations. lia. }
    1:{ rewrite ULs. lia. }
    1:{ exact PR. } 1:{ exact XA. } 1:{ exact Lx. } 1:{ exact LENC. } 1:{ exact Hlenk. } 1:{ exact A8. } 1:{ exact BN. }
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
      replace (SP' - 1184)%Z with (bv_unsigned sp - 1232)%Z in * by lia.
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
      split. { replace (SP' - 1184)%Z with (bv_unsigned sp - 1232)%Z in * by lia. assumption. }
      assumption.
  Qed.

  #[using="large_mul_spec L62 A8 AL SEP SPLO Rsp HA AROD He0 CAP"] Lemma big_loop : forall n, big_ok n.
  Proof. LiaFast.lf_pins (fun (large_mul_spec L62 A8 AL SEP SPLO Rsp HA AROD He0 CAP : LiaFast.U) => LiaFast.u0). induction n as [|n IHn]. - unfold big_ok; intros; exfalso; lia. - apply big_body; exact IHn. Qed.

  #[using="large_mul_spec L62 A8 AL SEP SPLO Rsp HA AROD He0 CAP"] Lemma big_run : forall (e : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m : word -> option byte) (wsk : list word) (lenk : Z),
      (135 <= e <= e0)%Z ->
      u64arr PSEGS m A wsk -> length wsk = 62%nat ->
      rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e))%Z ->
      stk PSEGS m (bv_unsigned sp - 1232) SP' ->
      pristine m 0x10000 0x22000 ->
      evt PSEGS (big_post m)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 0x15aa0) (Z_to_bv 64 134) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x262cc) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (large_mul_spec L62 A8 AL SEP SPLO Rsp HA AROD He0 CAP : LiaFast.U) => LiaFast.u0).
    intros. eapply (big_loop (Z.to_nat e) m e); try eassumption; try lia.
    - cbv delta [big_W]. apply munch_refl. - apply wmono_refl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mid_post (x1 x6 x7 x18 x19 x28 x29 x30 x31 : word) (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (e' : Z) (x5 x14 x15 x16 x17 : word)
                      (m' : word -> option byte) (wsk : list word) (lenk : Z),
      ms' = MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e') (Z_to_bv 64 POW5_27) (Z_to_bv 64 lenk) (Z_to_bv 64 26) (Z_to_bv 64 61) x14 x15 x16 x17
                   x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x26358) fc None m' (seg_rom PSEGS)
      /\ munch [(A, A + 498)]%Z m0 m'
      /\ wmono PSEGS m0 m'
      /\ u64arr PSEGS m' A wsk /\ length wsk = 62%nat
      /\ rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 lenk)] /\ (0 <= lenk <= 62)%Z
      /\ bnorm wsk (Z.to_nat lenk)
      /\ (0 <= e' < 27)%Z /\ (e' <= e0)%Z
      /\ bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e'))%Z.

  Definition mid_ok (x1 x6 x7 x18 x19 x28 x29 x30 x31 : word) (m0 : word -> option byte) (n : nat) : Prop :=
    forall (e : Z) (x5 x14 x15 x16 x17 : word) (m : word -> option byte) (wsk : list word) (lenk : Z),
      (Z.to_nat e <= n)%nat -> (27 <= e <= e0)%Z ->
      u64arr PSEGS m A wsk -> length wsk = 62%nat ->
      rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e))%Z ->
      munch [(A, A + 498)]%Z m0 m -> wmono PSEGS m0 m ->
      evt PSEGS (mid_post x1 x6 x7 x18 x19 x28 x29 x30 x31 m0)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e) (Z_to_bv 64 POW5_27) (Z_to_bv 64 lenk) (Z_to_bv 64 26) (Z_to_bv 64 61) x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26304) fc None m (seg_rom PSEGS)).

  #[using="L62 A8 AL SPLO HA He0 CAP"] Lemma mid_body : forall x1 x6 x7 x18 x19 x28 x29 x30 x31 m0 n,
    mid_ok x1 x6 x7 x18 x19 x28 x29 x30 x31 m0 n -> mid_ok x1 x6 x7 x18 x19 x28 x29 x30 x31 m0 (S n).
  Proof. LiaFast.lf_pins (fun (L62 A8 AL SPLO HA He0 CAP : LiaFast.U) => LiaFast.u0).
    clear Rsp AROD. (* [comment removed for export] *)
    intros x1 x6 x7 x18 x19 x28 x29 x30 x31 m0 n IH. unfold mid_ok.
    intros e x5 x14 x15 x16 x17 m wsk lenk Hn He XA Lx LENC Hlenk BN VAL MU WM.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    assert (P27 : (0 < 5 ^ 27)%Z) by (apply Z.pow_pos_nonneg; lia).
    assert (CAPs : (X * 5 ^ (e0 - e) * 5 ^ 27 < BIG_CAP)%Z).
    { rewrite (pow5_step_val X e0 e 27) by lia. apply (cap_pow5_mono X _ e0); lia. }
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
        apply evt_done. unfold mid_post. exists (e + -27)%Z. do 5 eexists. eexists _, wsk, lenk.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact XA|]. split; [exact Lx|].
        split; [exact LENC|]. split; [lia|]. split; [exact BN|]. split; [lia|]. split; [lia|].
        first [lia | rewrite Hl0 in *; change (Z.to_nat 0) with 0%nat in *; rewrite bval_0 in *; rewrite XZ; ring].
    - cond_cleanup Hl0.
      step. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
      zstep. (* [comment removed for export] *)
      replace (A + lenk * 8)%Z with (A + 8 * lenk)%Z by lia.
      step. (* [comment removed for export] *)
      name_mem mc.
      call (@smulM_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               F fc mc A POW5_27 wsk lenk Lx ltac:(lia) ltac:(unfold POW5_27; lia) HA va).
      all: try lia.
      1:{ exact XA. } 1:{ exact Lx. } 1:{ intros j; reflexivity. }
      match goal with H : smul_inv _ _ _ _ ?c |- _ => rename H into INV; rename c into c' end.
      match goal with H : u64arr PSEGS _ A ?cu |- _ => rename H into CUR; rename cu into cur end.
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
          apply evt_done. unfold mid_post. exists (e + -27)%Z. do 5 eexists. eexists _, cur, lenk.
          split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact CUR|]. split; [assumption|].
          split; [eassumption|]. split; [lia|]. split; [exact BN'|]. split; [lia|]. split; [lia|].
          rewrite VAL'; repeat f_equal; try lia.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        pose proof (smul_carry_room wsk _ _ _ _ INV ltac:(lia) CAPy) as ROOM.
        step. (* [comment removed for export] *)
        if_not_taken.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          pose proof (u64arr_store_ok PSEGS m1 _ _ lenk (Z_to_bv 64 (A + 8 * lenk)) CUR ltac:(rewrite Hlc, Lx; lia) eq_refl) as SOK end.
        step. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ _) _) =>
          pose proof (u64arr_write PSEGS m1 _ _ lenk (Z_to_bv 64 c') CUR ltac:(rewrite Hlc, Lx; lia)) as CUR2 end.
        store_done.
        zstep. (* [comment removed for export] *)
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
          apply evt_done. unfold mid_post. exists (e + -27)%Z. do 5 eexists. eexists _, _, (lenk + 1)%Z.
          split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact CUR2|].
          split; [rewrite upd_length, Hlc; exact Lx|].
          split; [eassumption|]. split; [lia|]. split; [exact BN'|]. split; [lia|]. split; [lia|].
          rewrite VAL'; repeat f_equal; try lia.
  Qed.

  #[using="L62 A8 AL SPLO HA He0 CAP"] Lemma mid_loop : forall x1 x6 x7 x18 x19 x28 x29 x30 x31 m0 n, mid_ok x1 x6 x7 x18 x19 x28 x29 x30 x31 m0 n.
  Proof. LiaFast.lf_pins (fun (L62 A8 AL SPLO HA He0 CAP : LiaFast.U) => LiaFast.u0). intros. induction n as [|n IHn]. - unfold mid_ok; intros; exfalso; lia. - apply mid_body; exact IHn. Qed.

  #[using="L62 A8 AL SPLO HA He0 CAP"] Lemma mid_run : forall (x1 x6 x7 x18 x19 x28 x29 x30 x31 : word) (e : Z) (x5 x14 x15 x16 x17 : word)
           (m : word -> option byte) (wsk : list word) (lenk : Z),
      (27 <= e <= e0)%Z ->
      u64arr PSEGS m A wsk -> length wsk = 62%nat ->
      rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e))%Z ->
      evt PSEGS (mid_post x1 x6 x7 x18 x19 x28 x29 x30 x31 m)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e) (Z_to_bv 64 POW5_27) (Z_to_bv 64 lenk) (Z_to_bv 64 26) (Z_to_bv 64 61) x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26304) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (L62 A8 AL SPLO HA He0 CAP : LiaFast.U) => LiaFast.u0).
    intros. eapply (mid_loop x1 x6 x7 x18 x19 x28 x29 x30 x31 m (Z.to_nat e) e); try eassumption; try lia.
    - apply munch_refl. - apply wmono_refl.
  Qed.
End Loops.
End P_pow5_B.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_shl OSSVerify.Proofs.fast_float.from_chars.lib.FF.ImgFacts OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_large_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_pow5_A OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_pow5_B.
Import ListNotations.

Module P_large_mul.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5.P_large_mul_stmt.
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
    unfold large_mul_stmt. intros until len. intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NORM Ha1 Ha2 CAP SEP.
    subst a1 a2.
    pose proof (munch_refl [(bv_unsigned sp - 1184, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 498)]%Z m) as MU.
    pose proof (wmono_refl PSEGS m) as WM.
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
    1:{ rewrite ULs. replace (bv_unsigned sp + -16 - 1168)%Z with (bv_unsigned sp - 1184)%Z by lia. exact ST. }
    1:{ rewrite ULs. Z.div_mod_to_equations. lia. }
    1:{ rewrite ULs. lia. }
    1:{ exact PR. } 1:{ exact LIMBS. } 1:{ exact L62. } 1:{ exact LENC. } 1:{ exact Hlen. } 1:{ exact A8. } 1:{ exact NORM. }
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact CAP. }
    1:{ rewrite ULs. lia. }
    rewrite ?ULs in *.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. step. step. (* [comment removed for export] *)
    match goal with H : stk PSEGS _ _ _ |- _ => rename H into ST2 end.
    release_frame FR ST2 (bv_unsigned sp).
    unfold large_mul_post. finish.
    all: try eassumption. all: try lia.
    replace (bv_unsigned sp - 1184)%Z with (bv_unsigned sp + -16 - 1168)%Z by lia. assumption.
  Qed.
End Main.
End P_large_mul.

Module P_long_mul_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs.StoreFast.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Notation PSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Smul1.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (A y : Z) (ws : list word) (len : Z).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis Hy : (0 <= y < 2 ^ 64)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.

  Definition smul1_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (c' : Z) (a4 a5 : word) (m' : word -> option byte) (cur : list word),
      ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (A + 8 * len)) (Z_to_bv 64 c') (Z_to_bv 64 y) (Z_to_bv 64 (A + 8 * len)) a4 a5 x16 x17
                   x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x26538) fc None m' (seg_rom PSEGS)
      /\ munch [(A, A + 8 * len)]%Z m m'
      /\ wmono PSEGS m m'
      /\ u64arr PSEGS m' A cur
      /\ length cur = 62%nat
      /\ smul_inv ws cur y (Z.to_nat len) c'.

  Definition smul1_ok (k : nat) : Prop :=
    forall (i : nat) (p a4 a5 : word) (c : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      u64arr PSEGS m A cur -> length cur = 62%nat ->
      smul_inv ws cur y i c ->
      munch [(A, A + 8 * len)]%Z m0 m -> wmono PSEGS m0 m ->
      evt PSEGS (smul1_post m0)
        (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (A + 8 * len)) (Z_to_bv 64 c) (Z_to_bv 64 y) p a4 a5 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26514) fc None m (seg_rom PSEGS)).

  #[using="L62 LEN Hy HA"] Lemma smul1_body : forall k, smul1_ok k -> smul1_ok (S k).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold smul1_ok. intros i p a4 a5 c cur m Hk Hi Hp CUR Hcur INV MU WM.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    destruct INV as (Hv & Hag & Hc & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (u64arr_read PSEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit y), ?(unsigned_lit c) by lia.
    pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write PSEGS m A cur (Z.of_nat i) (Z_to_bv 64 (bv_unsigned w * y + c)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (lm_smul_carry_word (bv_unsigned w) y c) by lia.
    assert (INV' : smul_inv ws (upd cur i (Z_to_bv 64 (bv_unsigned w * y + c))) y (S i) (mul_cout (limbZ ws i) y c)).
    { replace (bv_unsigned w * y)%Z with (limbZ ws i * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply smul_inv_step; [split; [exact Hv| split; [exact Hag| split; [exact Hc| exact Hlc]]] | lia | rewrite L62; lia |].
      unfold limbZ. rewrite <- Hw. apply lm_smul_lo_word; lia. }
    replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
    step. (* [comment removed for export] *)
    if_cases Hb.
    - cond_cleanup Hb.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite upd_length. exact Hcur.
    - cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      apply evt_done. unfold smul1_post.
      exists (mul_cout (limbZ ws i) y c), (v_sltu (Z_to_bv 64 (limbZ ws i * y + c)) (Z_to_bv 64 (limbZ ws i * y))),
             (Z_to_bv 64 (Z.shiftr (limbZ ws i * y) 64)), m1, (upd cur i (Z_to_bv 64 (limbZ ws i * y + c))).
      split. { f_equal. replace (bv_unsigned p + 8)%Z with (A + 8 * len)%Z by lia. reflexivity. }
      split; [exact MU|]. split; [exact WM|].
      split. { replace (limbZ ws i) with (bv_unsigned w) by (unfold limbZ; rewrite <- Hw; reflexivity). exact CUR'. }
      split; [rewrite upd_length; exact Hcur|].
      rewrite <- Hil. replace (limbZ ws i * y)%Z with (bv_unsigned w * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity). exact INV'.
  Qed.

  #[using="L62 LEN Hy HA"] Lemma smul1_loop : forall k, smul1_ok k.
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0). induction k as [|k IH]. - unfold smul1_ok; intros; exfalso; lia. - apply smul1_body; exact IH. Qed.

  (* [comment removed for export] *)
  #[using="L62 LEN Hy HA"] Lemma smul1_run : forall (p a4 a5 : word) (cur : list word),
    bv_unsigned p = A ->
    u64arr PSEGS m0 A cur -> length cur = 62%nat -> (forall j, nth j cur w0 = nth j ws w0) ->
    evt PSEGS (smul1_post m0)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (A + 8 * len)) (Z_to_bv 64 0) (Z_to_bv 64 y) p a4 a5 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x26514) fc None m0 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0).
    intros p a4 a5 cur Hp CUR Hcur Hag.
    eapply (smul1_loop (Z.to_nat len) 0%nat); try eassumption; try lia.
    - split; [cbn; lia|]. split; [intros; apply Hag|]. split; [lia|]. rewrite Hcur, L62. reflexivity.
    - apply munch_refl.
    - apply wmono_refl.
  Qed.
End Smul1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Smul2.
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (A y : Z) (ws : list word) (len : Z).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis Hy : (0 <= y < 2 ^ 64)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.

  Definition smul2_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (c' : Z) (a6 a7 : word) (m' : word -> option byte) (cur : list word),
      ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 c') (Z_to_bv 64 (A + 8 * len)) (Z_to_bv 64 (A + 8 * len)) a6 a7
                   x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 y) x28 x29 x30 x31)
               F (Z_to_bv 64 0x26604) fc None m' (seg_rom PSEGS)
      /\ munch [(A, A + 8 * len)]%Z m m'
      /\ wmono PSEGS m m'
      /\ u64arr PSEGS m' A cur
      /\ length cur = 62%nat
      /\ smul_inv ws cur y (Z.to_nat len) c'.

  Definition smul2_ok (k : nat) : Prop :=
    forall (i : nat) (p a6 a7 : word) (c : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      u64arr PSEGS m A cur -> length cur = 62%nat ->
      smul_inv ws cur y i c ->
      munch [(A, A + 8 * len)]%Z m0 m -> wmono PSEGS m0 m ->
      evt PSEGS (smul2_post m0)
        (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 c) p (Z_to_bv 64 (A + 8 * len)) a6 a7
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 y) x28 x29 x30 x31)
            F (Z_to_bv 64 0x265e0) fc None m (seg_rom PSEGS)).

  #[using="L62 LEN Hy HA"] Lemma smul2_body : forall k, smul2_ok k -> smul2_ok (S k).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold smul2_ok. intros i p a6 a7 c cur m Hk Hi Hp CUR Hcur INV MU WM.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    destruct INV as (Hv & Hag & Hc & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (u64arr_read PSEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit y), ?(unsigned_lit c) by lia.
    pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write PSEGS m A cur (Z.of_nat i) (Z_to_bv 64 (bv_unsigned w * y + c)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (lm_smul_carry_word (bv_unsigned w) y c) by lia.
    assert (INV' : smul_inv ws (upd cur i (Z_to_bv 64 (bv_unsigned w * y + c))) y (S i) (mul_cout (limbZ ws i) y c)).
    { replace (bv_unsigned w * y)%Z with (limbZ ws i * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply smul_inv_step; [split; [exact Hv| split; [exact Hag| split; [exact Hc| exact Hlc]]] | lia | rewrite L62; lia |].
      unfold limbZ. rewrite <- Hw. apply lm_smul_lo_word; lia. }
    replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
    step. (* [comment removed for export] *)
    if_cases Hb.
    - cond_cleanup Hb.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite upd_length. exact Hcur.
    - cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      apply evt_done. unfold smul2_post.
      exists (mul_cout (limbZ ws i) y c), (v_sltu (Z_to_bv 64 (limbZ ws i * y + c)) (Z_to_bv 64 (limbZ ws i * y))),
             (Z_to_bv 64 (Z.shiftr (limbZ ws i * y) 64)), m1, (upd cur i (Z_to_bv 64 (limbZ ws i * y + c))).
      split. { f_equal. replace (bv_unsigned p + 8)%Z with (A + 8 * len)%Z by lia. reflexivity. }
      split; [exact MU|]. split; [exact WM|].
      split. { replace (limbZ ws i) with (bv_unsigned w) by (unfold limbZ; rewrite <- Hw; reflexivity). exact CUR'. }
      split; [rewrite upd_length; exact Hcur|].
      rewrite <- Hil. replace (limbZ ws i * y)%Z with (bv_unsigned w * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity). exact INV'.
  Qed.

  #[using="L62 LEN Hy HA"] Lemma smul2_loop : forall k, smul2_ok k.
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0). induction k as [|k IH]. - unfold smul2_ok; intros; exfalso; lia. - apply smul2_body; exact IH. Qed.

  (* [comment removed for export] *)
  #[using="L62 LEN Hy HA"] Lemma smul2_run : forall (a6 a7 : word) (cur : list word),
    u64arr PSEGS m0 A cur -> length cur = 62%nat -> (forall j, nth j cur w0 = nth j ws w0) ->
    evt PSEGS (smul2_post m0)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 (A + 8 * len)) a6 a7
               x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 y) x28 x29 x30 x31)
          F (Z_to_bv 64 0x265e0) fc None m0 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy HA : LiaFast.U) => LiaFast.u0).
    intros a6 a7 cur CUR Hcur Hag.
    eapply (smul2_loop (Z.to_nat len) 0%nat); try eassumption; try lia.
    - rewrite unsigned_lit by lia. lia.
    - split; [cbn; lia|]. split; [intros; apply Hag|]. split; [lia|]. rewrite Hcur, L62. reflexivity.
    - apply munch_refl.
    - apply wmono_refl.
  Qed.
End Smul2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Norm.
  Variables (x1 x2 x3 x4 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (va : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (cur : list word).
  Notation A := (bv_unsigned va).
  Hypothesis Hcur : length cur = 62%nat.
  Hypothesis HA : (A + 498 <= 2 ^ 64)%Z.

  Definition norm_post (l : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (l' : Z) (a1 : word) (m' : word -> option byte),
      ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 va x9 (Z_to_bv 64 1) a1 x12 x13 x14 x15 x16 x17
                   x18 (Z_to_bv 64 l') x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x26684) fc None m' (seg_rom PSEGS)
      /\ munch [(A + 496, A + 498)]%Z m m'
      /\ wmono PSEGS m m'
      /\ rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 l')]
      /\ (0 <= l' <= l)%Z
      /\ bnorm cur (Z.to_nat l')
      /\ bval cur (Z.to_nat l') = bval cur (Z.to_nat l).

  Definition norm_ok (m0 : word -> option byte) (l0 : Z) (k : nat) : Prop :=
    forall (l : Z) (a1 : word) (m : word -> option byte),
      (Z.to_nat l <= k)%nat -> (0 < l <= l0)%Z ->
      u64arr PSEGS m A cur ->
      rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 l)] ->
      bval cur (Z.to_nat l) = bval cur (Z.to_nat l0) ->
      munch [(A + 496, A + 498)]%Z m0 m -> wmono PSEGS m0 m ->
      evt PSEGS (norm_post l0 m0)
        (MS (mkR x1 x2 x3 x4 x5 x6 x7 va x9 (Z_to_bv 64 1) a1 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 l) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26658) fc None m (seg_rom PSEGS)).

  #[using="Hcur HA"] Lemma norm_body : forall m0 l0 k, (0 <= l0 <= 62)%Z -> norm_ok m0 l0 k -> norm_ok m0 l0 (S k).
  Proof. LiaFast.lf_pins (fun (Hcur HA : LiaFast.U) => LiaFast.u0).
    intros m0 l0 k Hl0 IH. unfold norm_ok. intros l a1 m Hk Hl CUR LENC VAL MU WM.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite shl48_shr45 by lia.
    zstep. (* [comment removed for export] *)
    destruct (nth_error cur (Z.to_nat (l - 1))) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    pose proof (u64arr_read PSEGS m A cur (l - 1) w _ CUR Hn ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    assert (Hw : limbZ cur (Z.to_nat l - 1) = bv_unsigned w).
    { unfold limbZ. replace (Z.to_nat l - 1)%nat with (Z.to_nat (l - 1)) by lia. rewrite (nth_error_nth _ _ _ Hn). reflexivity. }
    step. (* [comment removed for export] *)
    if_cases Hnz.
    - (* [comment removed for export] *)
      cond_cleanup Hnz.
      apply evt_done. unfold norm_post. exists l, w, m.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact LENC|]. split; [lia|].
      split; [| exact VAL]. right. rewrite Hw. exact Hnz.
    - cond_cleanup Hnz.
      step. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz.
      + (* [comment removed for export] *)
        cond_cleanup Hz. apply (shl48_zero_iff (l + -1)) in Hz; [|lia].
        apply evt_done. unfold norm_post. eexists (l + -1)%Z, _, _.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact LENC|]. split; [lia|].
        split. { left. lia. }
        rewrite <- VAL. replace (Z.to_nat (l + -1)) with (Z.to_nat l - 1)%nat by lia. symmetry. apply bval_drop_zero_top; [lia|]. rewrite Hw. exact Hnz.
      + cond_cleanup Hz.
        assert (Hl1 : (l + -1 <> 0)%Z). { intros E. apply Hz. apply (shl48_zero_iff (l + -1)); lia. }
        step. (* [comment removed for export] *)
        eapply IH; try eassumption; try lia.
        rewrite <- VAL. replace (Z.to_nat (l + -1)) with (Z.to_nat l - 1)%nat by lia. symmetry. apply bval_drop_zero_top; [lia|]. rewrite Hw. exact Hnz.
  Qed.

  #[using="Hcur HA"] Lemma norm_loop : forall m0 l0 k, (0 <= l0 <= 62)%Z -> norm_ok m0 l0 k.
  Proof. LiaFast.lf_pins (fun (Hcur HA : LiaFast.U) => LiaFast.u0). intros m0 l0 k H. induction k as [|k IH]. - unfold norm_ok; intros; exfalso; lia. - apply norm_body; [exact H| exact IH]. Qed.

  (* [comment removed for export] *)
  #[using="Hcur HA"] Lemma norm_run : forall (l : Z) (a0 a1 : word) (m : word -> option byte),
    (0 <= l <= 62)%Z ->
    u64arr PSEGS m A cur ->
    rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 l)] ->
    evt PSEGS (norm_post l m)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 va x9 a0 a1 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 l) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x2664c) fc None m (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (Hcur HA : LiaFast.U) => LiaFast.u0).
    intros l a0 a1 m Hl CUR LENC.
    zstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz.
    - cond_cleanup Hz. apply (shl48_zero_iff l) in Hz; [|lia]. subst l.
      apply evt_done. unfold norm_post. eexists 0%Z, _, _.
      split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact LENC|]. split; [lia|].
      split; [apply bnorm_0| reflexivity].
    - cond_cleanup Hz.
      assert (Hl1 : (l <> 0)%Z). { intros E. apply Hz. apply (shl48_zero_iff l); lia. }
      eapply (norm_loop m l (Z.to_nat l)); try eassumption; try lia.
      + apply munch_refl. + apply wmono_refl.
  Qed.
End Norm.
End P_long_mul_A.

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

Lemma P_SP5_tbl : table_b PSEGS 0x15ac8 8 (fun v => le8 (Z_to_bv 64 v)) SMALL_POW5 = true.
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
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SEP : (A + 498 <= bv_unsigned sp - 1232 \/ bv_unsigned sp <= A)%Z.
  Hypothesis SPLO : (0x22000 <= bv_unsigned sp - 1232)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.
  Hypothesis AROD : (A + 498 <= 0x10000 \/ 0x22000 <= A)%Z.
  Hypothesis He0 : (0 <= e0 < 2 ^ 31)%Z.
  Hypothesis CAP : (X * 5 ^ e0 < BIG_CAP)%Z.

  (* [comment removed for export] *)
  #[using="L62"] Lemma exit_244e0 : forall (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word)
      (m' : word -> option byte) (wsf : list word) (lenf : Z),
      u64arr PSEGS m' A wsf -> length wsf = 62%nat ->
      rw_cells PSEGS m' (A + 496) [C2 (Z_to_bv 64 lenf)] -> (0 <= lenf <= 62)%Z ->
      bnorm wsf (Z.to_nat lenf) ->
      bval wsf (Z.to_nat lenf) = (X * 5 ^ e0)%Z ->
      rw_cells PSEGS m' SP' [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk PSEGS m' (bv_unsigned sp - 1232) SP' ->
      pristine m' 0x10000 0x22000 ->
      munch (pow5_W (bv_unsigned sp) A) m m' -> wmono PSEGS m m' ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 a0 x9 (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x263d0) fc None m' (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (L62 : LiaFast.U) => LiaFast.u0).
    intros * XA Lx LENC Hl BN VAL FR ST PR MU WM.
    do 7 step.
    release_frame FR ST (bv_unsigned sp).
    unfold pow5_post. finish. all: try eassumption. all: try lia.
  Qed.

  (* [comment removed for export] *)
  #[using="L62 A8 AL SEP SPLO HA AROD He0 CAP"] Lemma from_24468 : forall (e2 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word)
      (m1 : word -> option byte) (wsk : list word) (lenk : Z),
      (0 <= e2 < 27)%Z -> (e2 <= e0)%Z ->
      u64arr PSEGS m1 A wsk -> length wsk = 62%nat ->
      rw_cells PSEGS m1 (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e2))%Z ->
      rw_cells PSEGS m1 SP' [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk PSEGS m1 (bv_unsigned sp - 1232) SP' ->
      pristine m1 0x10000 0x22000 ->
      munch (pow5_W (bv_unsigned sp) A) m m1 -> wmono PSEGS m m1 ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 a0 (Z_to_bv 64 e2) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x26358) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (L62 A8 AL SEP SPLO HA AROD He0 CAP : LiaFast.U) => LiaFast.u0).
    clear Rsp. (* [comment removed for export] *)
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
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
        step. step. (* [comment removed for export] *)
        zstep. (* [comment removed for export] *)
        replace (88776 + e2 * 8)%Z with (88776 + 8 * e2)%Z by lia.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
          pose proof (table_read PSEGS (fun v => le8 (Z_to_bv 64 v)) SMALL_POW5 0x15ac8 8 mc 0x10000 0x22000
                        P_SP5_tbl PR ltac:(lia) ltac:(rewrite SMALL_POW5_length; cbn; lia) e2
                        ltac:(rewrite SMALL_POW5_length; cbn; lia)) as RD end.
        change (Z.of_nat 8) with 8%Z in RD. rewrite (SMALL_POW5_nth (Z.to_nat e2)) in RD by lia. rewrite Z2Nat.id in RD by lia.
        step. (* [comment removed for export] *)
        clear RD.
        zstep. (* [comment removed for export] *)
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
        zstep. (* [comment removed for export] *)
        replace (A + lenk * 8)%Z with (A + 8 * lenk)%Z by lia.
        step. (* [comment removed for export] *)
        assert (Py : (0 < 5 ^ e2 < 2 ^ 64)%Z).
        { split; [apply Z.pow_pos_nonneg; lia|]. apply (Z.le_lt_trans _ (5 ^ 27)); [apply Z.pow_le_mono_r; lia|]. cbn; lia. }
        assert (CAPs : (X * 5 ^ (e0 - e2) * 5 ^ e2 < BIG_CAP)%Z).
        { rewrite (pow5_step_val X e0 e2 e2) by lia. apply (cap_pow5_mono X _ e0); lia. }
        name_mem mc.
        call (@smulF_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 F fc mc A (5 ^ e2) wsk lenk Lx ltac:(lia) ltac:(lia) HA a0).
        all: try lia.
        1:{ exact XA. } 1:{ exact Lx. } 1:{ intros j; reflexivity. }
        match goal with H : smul_inv _ _ _ _ ?c |- _ => rename H into INV; rename c into c' end.
        match goal with H : u64arr PSEGS _ A ?cu |- _ => rename H into CUR; rename cu into cur end.
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
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            pose proof (u64arr_store_ok PSEGS m1 _ _ lenk (Z_to_bv 64 (A + 8 * lenk)) CUR ltac:(rewrite Hlc, Lx; lia) eq_refl) as SOK end.
          step. (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ _) _) =>
            pose proof (u64arr_write PSEGS m1 _ _ lenk (Z_to_bv 64 c') CUR ltac:(rewrite Hlc, Lx; lia)) as CUR2 end.
          store_done.
          zstep. (* [comment removed for export] *)
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
  #[using="L62 A8 AL SEP SPLO HA AROD He0 CAP"] Lemma from_243f8 : forall (e1 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word)
      (m1 : word -> option byte) (wsk : list word) (lenk : Z),
      (0 <= e1 < 135)%Z -> (e1 <= e0)%Z ->
      u64arr PSEGS m1 A wsk -> length wsk = 62%nat ->
      rw_cells PSEGS m1 (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      bval wsk (Z.to_nat lenk) = (X * 5 ^ (e0 - e1))%Z ->
      rw_cells PSEGS m1 SP' [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk PSEGS m1 (bv_unsigned sp - 1232) SP' ->
      pristine m1 0x10000 0x22000 ->
      munch (pow5_W (bv_unsigned sp) A) m m1 -> wmono PSEGS m m1 ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 a0 (Z_to_bv 64 e1) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x262e8) fc None m1 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins (fun (L62 A8 AL SEP SPLO HA AROD He0 CAP : LiaFast.U) => LiaFast.u0).
    intros * He1 He1' XA Lx LENC Hl BN VAL FR ST PR MU WM.
    cbv delta [pow5_W] in MU.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H27.
    - cond_cleanup H27.
      eapply from_24468; try eassumption; try lia. all: cbv delta [pow5_W]; exact MU.
    - cond_cleanup H27.
      step. (* [comment removed for export] *)
      rewrite zx16_lit_small by lia.
      step. step. (* [comment removed for export] *)
      change 7450580596923828125%Z with POW5_27.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      name_mem mc.
      eapply evt_cut; [ eapply mid_run with (ws:=ws) (len:=len) | post_call PSEGS mc ].
      all: try eassumption; try lia.
      eapply from_24468; try eassumption; try lia. all: cbv delta [pow5_W]; assumption.
  Qed.
  End Fixed.

  #[using="large_mul_spec"] Lemma pow5_spec : pow5_stmt.
  Proof. LiaFast.lf_pins (fun (large_mul_spec : LiaFast.U) => LiaFast.u0).
    unfold pow5_stmt. intros until len. intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NORM He CAP SEP.
    pose proof (munch_refl (pow5_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU.
    cbv delta [pow5_W] in MU.
    pose proof (wmono_refl PSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a1) as Re. unfold bv_modulus in Re.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    pose proof (u64arr_outside_rodata_P m _ _ PR LIMBS ltac:(rewrite L62; lia)) as AROD. rewrite L62 in AROD.
    pose proof (rw_cells_outside_rodata_P m _ _ PR LENC ltac:(cbn; lia)) as CROD. cbn [cells_size csize Nat.add] in CROD.
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
      eapply from_243f8; try eassumption; try lia.
      all: first [rewrite Z.sub_diag, Z.pow_0_r; ring | cbv delta [pow5_W]; exact MU].
    - cond_cleanup H135.
      step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      name_mem mc.
      eapply evt_cut; [ eapply (big_run large_mul_spec) with (ws:=ws) (len:=len) | post_call PSEGS mc ].
      all: try eassumption; try lia.
      all: try (rewrite Z.sub_diag, Z.pow_0_r; ring).
      eapply from_243f8; try eassumption; try lia. all: cbv delta [pow5_W]; assumption.
  Qed.
End Main.
