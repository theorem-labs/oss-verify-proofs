(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac U_small_add_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition sadd_inv (ws cur : list word) (y : Z) (i : nat) (cv : Z) : Prop :=
  (bval cur i + cv * 2 ^ (64 * Z.of_nat i) = bval ws i + y)%Z
  /\ (forall j, (i <= j)%nat -> nth j cur w0 = nth j ws w0)
  /\ length cur = length ws.

Lemma sadd_inv_init : forall ws y, sadd_inv ws ws y 0 y.
Proof. intros. split; [cbn; lia|]. split; [intros; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma sadd_inv_step_val : forall ws cur y i cv,
  sadd_inv ws cur y i cv -> (i < length ws)%nat -> (0 <= cv < 2^64)%Z ->
  let x := limbZ ws i in
  (bval (upd cur i (Z_to_bv 64 (x + cv))) (S i) + (if (x + cv <? 2^64)%Z then 0 else 1) * 2 ^ (64 * Z.of_nat (S i))
   = bval ws (S i) + y)%Z
  /\ (forall j, (S i <= j)%nat -> nth j (upd cur i (Z_to_bv 64 (x + cv))) w0 = nth j ws w0)
  /\ length (upd cur i (Z_to_bv 64 (x + cv))) = length ws.
Proof.
  intros ws cur y i cv (Hv & Hag & Hl) Hi Hcv x.
  pose proof (limbZ_range ws i) as Hx. fold x in Hx.
  split; [| split; [intros j Hj; rewrite nth_upd_other by lia; apply Hag; lia | rewrite upd_length; exact Hl]].
  rewrite bval_push by (rewrite Hl; exact Hi). rewrite bval_S, pow64_S.
  rewrite unsigned_lit_wrap.
  replace (limbZ ws i) with x by reflexivity.
  destruct (Z.ltb_spec (x + cv) (2 ^ 64)) as [Hlt|Hge].
  - rewrite Z.mod_small by lia. nia.
  - rewrite <- (Z.mod_unique_pos (x + cv) (2^64) 1 (x + cv - 2^64)) by lia. nia.
Qed.

(* [comment removed for export] *)
Lemma bval_agree_above : forall (l1 l2 : list word) k n, (k <= n)%nat ->
  (forall j, (k <= j)%nat -> nth j l1 w0 = nth j l2 w0) ->
  (bval l1 n - bval l1 k = bval l2 n - bval l2 k)%Z.
Proof.
  intros l1 l2 k n Hkn Hag. induction n as [|n IH].
  - assert (k = 0%nat) as -> by lia. cbn. lia.
  - destruct (Nat.eq_dec k (S n)) as [->|Hne]; [lia|].
    rewrite !bval_S. unfold limbZ. rewrite (Hag n) by lia. specialize (IH ltac:(lia)). lia.
Qed.

Section Loop.
  Variables (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
  Variables (vec : word) (y : Z) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (len : Z).
  Hypothesis Hlen : length ws = 62%nat.
  Hypothesis LEN : (0 <= len <= 62)%Z.
  Hypothesis Hy : (0 < y < 2^64)%Z.
  Hypothesis CAP : (bval ws (Z.to_nat len) + y < BIG_CAP)%Z.

  Notation A := (bv_unsigned vec).
  Notation POST := (small_add_post ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A y ws len m0).
  Notation NOTA := (Z_to_bv 64 (Z.lxor A 18446744073709551615)).

  (* [comment removed for export] *)
  Definition loop_ok (k : nat) : Prop :=
    forall (i : nat) (p cw t0 t1 : word) (cv : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i <= Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      bv_unsigned cw = cv -> (cv <> 0)%Z -> (i = 0%nat -> cv = y) -> ((0 < i)%nat -> cv = 1%Z) ->
      u64arr USEGS m A cur -> length cur = 62%nat ->
      rw_cells USEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      sadd_inv ws cur y i cv ->
      munch (small_add_W A) m0 m -> wmono USEGS m0 m ->
      evt USEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) cw vec (Z_to_bv 64 len) NOTA
                 (Z_to_bv 64 (-512 + 8 * Z.of_nat i)) (Z_to_bv 64 (len - Z.of_nat i)) p
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x26d3c) fc None m (seg_rom USEGS)).

  #[using="Hlen LEN Hy"] Lemma loop_body : forall k, loop_ok k -> loop_ok (S k).
  Proof. LiaFast.lf_pins (fun (Hlen LEN Hy : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold loop_ok. intros i p cw t0 t1 cv cur m Hk Hi Hp Hcw Hcv Hcv0 Hcv1 CUR Hcur LC INV MU WM.
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    pose proof (bv_unsigned_in_range 64 cw) as Rcw. unfold bv_modulus in Rcw.
    cbv delta [small_add_W] in MU.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (rw_cells_bound _ _ _ _ LC) as BL. cbn [cells_size csize Nat.add] in BL.
    assert (Hil : (i < Z.to_nat len)%nat) by lia.
    destruct INV as (Hv & Hag & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    pose proof (u64arr_read USEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    pose proof (u64arr_store_ok USEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write USEGS m A cur (Z.of_nat i) (Z_to_bv 64 (bv_unsigned w + bv_unsigned cw)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (sadd_inv_step_val ws cur y i cv (conj Hv (conj Hag Hlc)) ltac:(rewrite Hlen; lia) ltac:(lia)) as (Hv' & Hag' & Hlc').
    unfold limbZ in Hv', Hag', Hlc'. rewrite <- Hw, Hcw in *.
    step. (* [comment removed for export] *)
    if_cases Hb.
    - (* [comment removed for export] *)
      cond_cleanup Hb. rewrite ?unsigned_lit_wrap in Hb.
      pose proof (addc_wrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hb) as Hge.
      replace (bv_unsigned w + cv <? 2 ^ 64)%Z with false in Hv' by (symmetry; apply Z.ltb_ge; lia).
      replace (-512 + 8 * Z.of_nat i + 8)%Z with (-512 + 8 * Z.of_nat (S i))%Z by lia.
      replace (len - Z.of_nat i + -1)%Z with (len - Z.of_nat (S i))%Z by lia.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8)) (Z_to_bv 64 1) _ _ 1%Z); try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite unsigned_lit by lia. reflexivity.
      + split; [exact Hv'| split; [exact Hag'| exact Hlc']].
    - (* [comment removed for export] *)
      cond_cleanup Hb. rewrite ?unsigned_lit_wrap in Hb.
      pose proof (addc_nowrap (bv_unsigned w) cv ltac:(lia) ltac:(lia) Hb) as Hlt.
      replace (bv_unsigned w + cv <? 2 ^ 64)%Z with true in Hv' by (symmetry; apply Z.ltb_lt; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      unfold small_add_post. finish.
      { exact CUR'. } { rewrite upd_length. exact Hcur. } { exact LC. } all: try lia.
      + (* [comment removed for export] *)
        replace ((if true then 0 else 1) : Z) with 0%Z in Hv' by reflexivity.
        pose proof (bval_agree_above _ _ (S i) (Z.to_nat len) ltac:(lia) Hag') as E. lia.
      + (* [comment removed for export] *)
        intros BN. right. unfold limbZ.
        destruct (Nat.eq_dec (Z.to_nat len - 1) i) as [E|E].
        * rewrite E, nth_upd_same by (rewrite Hcur; lia). rewrite unsigned_lit by lia. lia.
        * rewrite Hag' by lia. apply (bnorm_top ws (Z.to_nat len) ltac:(lia) BN).
  Qed.

  (* [comment removed for export] *)
  #[using="Hlen LEN Hy CAP"] Lemma loop_exit : forall k, loop_ok k.
  Proof. LiaFast.lf_pins (fun (Hlen LEN Hy CAP : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; [| apply loop_body; exact IH].
    unfold loop_ok. intros i p cw t0 t1 cv cur m Hk Hi Hp Hcw Hcv Hcv0 Hcv1 CUR Hcur LC INV MU WM.
    assert (Hil : i = Z.to_nat len) by lia.
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    pose proof (bv_unsigned_in_range 64 cw) as Rcw. unfold bv_modulus in Rcw.
    cbv delta [small_add_W] in MU.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (rw_cells_bound _ _ _ _ LC) as BL. cbn [cells_size csize Nat.add] in BL.
    destruct INV as (Hv & Hag & Hlc).
    (* [comment removed for export] *)
    assert (ROOM : (len <= 61)%Z).
    { subst i. pose proof (bval_nonneg cur (Z.to_nat len)) as B0.
      destruct (Z.le_gt_cases len 61) as [|Hgt]; [assumption|]. exfalso.
      assert (E62 : Z.to_nat len = 62%nat) by lia. rewrite E62 in Hv, B0, CAP.
      unfold BIG_CAP in CAP. change (64 * Z.of_nat 62)%Z with 3968%Z in Hv.
      pose proof (Z.pow_pos_nonneg 2 3968 ltac:(lia) ltac:(lia)) as P0.
      assert (2 ^ 3968 <= cv * 2 ^ 3968)%Z by nia. lia. }
    step. (* [comment removed for export] *)
    if_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit len) by lia. rewrite Z.shiftl_mul_pow2 by lia. replace (len * 2 ^ 3)%Z with (8 * len)%Z by lia.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_store_ok USEGS m A cur len (Z_to_bv 64 (A + 8 * len)) CUR ltac:(lia) eq_refl) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write USEGS m A cur len cw CUR ltac:(lia)) as CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    unfold small_add_post. finish.
    { exact CUR'. } { rewrite upd_length. exact Hcur. } { exact LC. } all: try lia.
    + replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia. rewrite <- Hil.
      rewrite bval_push by (rewrite Hlc, Hlen; lia). rewrite Hcw. subst i. lia.
    + intros _. replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia. rewrite <- Hil.
      apply bnorm_push; [rewrite Hcur; lia|]. rewrite Hcw. exact Hcv.
  Qed.
End Loop.

Lemma small_add_spec : small_add_stmt.
Proof.
  unfold small_add_stmt. intros until len. intros LIMBS Hlen LC LEN CAP.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  pose proof (bv_unsigned_in_range 64 a1) as Ry. unfold bv_modulus in Ry.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bd. rewrite Hlen in Bd.
  pose proof (munch_refl (small_add_W (bv_unsigned a0)) m) as MU.
  pose proof (wmono_refl USEGS m) as WM.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hy0.
  - (* [comment removed for export] *)
    cond_cleanup Hy0.
    step. (* [comment removed for export] *)
    unfold small_add_post. finish.
    { exact LIMBS. } { exact Hlen. } { exact LC. } all: try lia.
    intros BN; exact BN.
  - cond_cleanup Hy0.
    step. (* [comment removed for export] *)
    rewrite zx16_lit by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    change (Z_to_bv 64 (-512)) with (Z_to_bv 64 (-512 + 8 * Z.of_nat 0)).
    replace (Z_to_bv 64 len) with (Z_to_bv 64 (len - Z.of_nat 0)) at 2 by (f_equal; lia).
    eapply (loop_exit ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 (bv_unsigned a1) F fc m ws len
              Hlen LEN ltac:(lia) CAP (Z.to_nat len) 0%nat a0 a1); try eassumption; try lia.
    apply sadd_inv_init.
Qed.
