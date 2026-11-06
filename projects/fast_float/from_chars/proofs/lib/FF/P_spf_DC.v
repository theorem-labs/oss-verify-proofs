(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs.

Module P_spf_commonT.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Export P_spf_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation PSEGS := Plain.M.loaded_segments.

Section CTX.
  Variable c : spf_ctx.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  Definition savesC : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition frameP (q w lm : word) (ng tm : Z) (j5 : list byte) (k3 kI fp fL : Z) (rest : list cell) : list cell :=
    [C8 q; C8 w; C8 lm; C1 (Z_to_bv 8 ng); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 tm); CB 5 j5;
     C8 (Z_to_bv 64 (P + k3)); C8 (Z_to_bv 64 (kI - k3)); C8 (Z_to_bv 64 fp); C8 (Z_to_bv 64 fL)]
    ++ rest ++ savesC.

  (* [comment removed for export] *)
  Definition tinv (cells : list cell) (m : word -> option byte) : Prop :=
    bytes_at PSEGS m P bs
    /\ rw_cells PSEGS m SP cells
    /\ stk PSEGS m (bv_unsigned sp - NEED) SP
    /\ rw_cells PSEGS m V [C4 v]
    /\ pristine m 0x10000 0x22000
    /\ pristine m P_FMIN (P_FMIN + 4)
    /\ munch W m0 m
    /\ wmono PSEGS m0 m.

  #[using="Type"] Lemma tinv_pinv : forall junk m, pinv c junk m <-> tinv (frameA c junk) m.
  Proof. LiaFast.lf_pins LiaFast.u0. intros; unfold pinv, tinv; tauto. Qed.

  (* [comment removed for export] *)
  Definition pnsok (ng k3 kI fp fL tm : Z) (w : word) : Prop :=
    (0 <= ng <= 1)%Z /\ (0 <= k3 <= kI)%Z /\ (kI <= L)%Z /\ (0 <= fL)%Z
    /\ ((fp = 0 /\ fL = 0) \/ (fp = P + kI + 1 /\ kI + 1 + fL <= L))%Z
    /\ (0 <= tm <= 1)%Z /\ (tm = 1 -> 0 < bv_unsigned w < 2^64 - 1)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition K_26740 : Prop :=
    forall m (r : list byte) (j5 : list byte)
           (x1 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm : word) (ng k3 kI fp fL tm : Z),
      tinv (frameP q w lm ng tm j5 k3 kI fp fL [CB 520 r]) m -> pnsok ng k3 kI fp fL tm w ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) (Z_to_bv 64 1) w (Z_to_bv 64 tm) x14 x15 x16 x17
                 x18 x19 q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28630) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_264ec : Prop :=
    forall m (r : list byte) (j5 : list byte)
           (x1 x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm : word) (ng k3 kI fp fL : Z),
      tinv (frameP q w lm ng 0 j5 k3 kI fp fL [C8 (Z_to_bv 64 0); CB 512 r]) m -> pnsok ng k3 kI fp fL 0 w ->
      (-10 <= bv_signed q)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) x11 w x13 x14 x15 x16 x17
                 x18 x19 q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x283dc) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_26754 : Prop :=
    forall m (r : list byte) (j5 : list byte)
           (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm : word) (ng k3 kI fp fL tm tf : Z),
      tinv (frameP q w lm ng tm j5 k3 kI fp fL [C8 (Z_to_bv 64 0); CB 512 r]) m -> pnsok ng k3 kI fp fL tm w ->
      (tf = 0 \/ (tf = 1 /\ tm = 1))%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) (Z_to_bv 64 tf) w x13 x14 x15 x16 x17
                 x18 x19 q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28644) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_26924 : Prop :=
    forall m (r : list byte) (j5 : list byte)
           (x1 x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm am ap : word) (ng k3 kI fp fL : Z),
      tinv (frameP q w lm ng 1 j5 k3 kI fp fL [C8 (Z_to_bv 64 0); CB 512 r]) m -> pnsok ng k3 kI fp fL 1 w ->
      (bv_signed q < -64 -> am = Z_to_bv 64 0 /\ ap = Z_to_bv 64 0)%Z ->
      (38 < bv_signed q -> am = Z_to_bv 64 0 /\ ap = Z_to_bv 64 255)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) x11 w x13 x14 x15 x16 x17
                 ap am q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28814) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_26b2c : Prop :=
    forall m (r : list byte) (j5 : list byte)
           (x1 x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm : word) (ng k3 kI fp fL : Z),
      tinv (frameP q w lm ng 1 j5 k3 kI fp fL [C8 (Z_to_bv 64 0); CB 512 r]) m -> pnsok ng k3 kI fp fL 1 w ->
      (-64 <= bv_signed q <= 38)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) x11 w x13 x14 x15 x16 x17
                 x18 x19 q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28a1c) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_26c4c : Prop :=
    forall m (r : list byte) (j5 : list byte)
           (x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm am : word) (ng k3 kI fp fL X : Z),
      tinv (frameP q w lm ng 1 j5 k3 kI fp fL [C8 (Z_to_bv 64 0); CB 512 r]) m -> pnsok ng k3 kI fp fL 1 w ->
      (-64 <= bv_signed q <= 38)%Z -> (-34100 <= X <= -31500)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 x10 x11 w x13 x14 x15 x16 x17
                 (Z_to_bv 64 X) am q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28b3c) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_26d50 : Prop :=
    forall m (cells : list cell)
           (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      bytes_at PSEGS m P bs ->
      rw_cells PSEGS m SP cells -> Z.of_nat (cells_size cells) = 584%Z ->
      rw_cells PSEGS m (SP + 584)%Z savesC ->
      stk PSEGS m (bv_unsigned sp - NEED) SP ->
      rw_cells PSEGS m V [C4 v] ->
      pristine m 0x10000 0x22000 -> pristine m P_FMIN (P_FMIN + 4) ->
      munch W m0 m -> wmono PSEGS m0 m ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28c40) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_26d8c : Prop :=
    forall m (cells : list cell) (F' : bvmap 5 word) (fc' : bv 32) (v' : word)
           (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      frm0 fc' ->
      rw_cells PSEGS m SP cells -> Z.of_nat (cells_size cells) = 584%Z ->
      rw_cells PSEGS m (SP + 584)%Z savesC ->
      stk PSEGS m (bv_unsigned sp - NEED) SP ->
      rw_cells PSEGS m V [C4 v'] ->
      munch W m0 m -> wmono PSEGS m0 m ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F' (Z_to_bv 64 0x28c7c) fc' None m (seg_rom PSEGS)).

End CTX.
End P_spf_commonT.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spf_tbl P_memset.

Module P_small_mul.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Wbig_tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_small_mul_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Loop.
  Variables (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
  Variables (vec yw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (len : Z).
  Hypothesis Hlen : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis CAP : (bval ws (Z.to_nat len) * bv_unsigned yw < BIG_CAP)%Z.

  Notation A := (bv_unsigned vec).
  Notation y := (bv_unsigned yw).
  Notation POST := (small_mul_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A y ws len m0).

  Definition loop_ok (k : nat) : Prop :=
    forall (i : nat) (p a7 t0 : word) (c : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      u64arr PSEGS m A cur -> length cur = 62%nat ->
      rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 len)] ->
      smul_inv ws cur y i c ->
      munch (small_mul_W A) m0 m -> wmono PSEGS m0 m ->
      evt PSEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) yw vec (Z_to_bv 64 len) (Z_to_bv 64 (A + 8 * len)) (Z_to_bv 64 c) p a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x25ff0) fc None m (seg_rom PSEGS)).

  #[using="Hlen LEN CAP"] Lemma loop_body : forall k, loop_ok k -> loop_ok (S k).
  Proof. LiaFast.lf_pins (fun (Hlen LEN CAP : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold loop_ok. intros i p a7 t0 c cur m Hk Hi Hp CUR Hcur LC INV MU WM.
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    cbv delta [small_mul_W] in MU.
    pose proof (bv_unsigned_in_range 64 yw) as Ry. unfold bv_modulus in Ry.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    destruct INV as (Hv & Hag & Hc & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    pose proof (u64arr_read PSEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_store_ok PSEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write PSEGS m A cur (Z.of_nat i) (Z_to_bv 64 (bv_unsigned w * y + c)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    rewrite (smul_carry_word (bv_unsigned w) y c) by lia.
    assert (INV' : smul_inv ws (upd cur i (Z_to_bv 64 (bv_unsigned w * y + c))) y (S i) (mul_cout (limbZ ws i) y c)).
    { replace (bv_unsigned w * y)%Z with (limbZ ws i * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply smul_inv_step; [split; [exact Hv| split; [exact Hag| split; [exact Hc| exact Hlc]]] | lia | rewrite Hlen; lia |].
      unfold limbZ. rewrite <- Hw. apply smul_lo_word; lia. }
    replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
    step. (* [comment removed for export] *)
    if_cases Hb.
    - (* [comment removed for export] *)
      cond_cleanup Hb.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8))); try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite upd_length. exact Hcur.
    - (* [comment removed for export] *)
      cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      pose proof (proj1 (proj2 (proj2 INV'))) as Hc'. cbn beta in Hc'.
      remember (mul_cout (limbZ ws i) y c) as c' eqn:Ec'.
      step. (* [comment removed for export] *)
      if_cases Hz.
      + (* [comment removed for export] *)
        cond_cleanup Hz.
        step. (* [comment removed for export] *)
        unfold small_mul_post. finish.
        { exact CUR'. } { rewrite upd_length. exact Hcur. } { exact LC. } all: try lia.
        * rewrite <- Hil. rewrite (Z.mul_comm (bval ws _) y). apply (smul_inv_finish_nocarry ws _ y (S i)). rewrite <- Hz. exact INV'.
        * intros Hy BN. rewrite <- Hil in BN |- *. right. cbn [Nat.sub]. rewrite Nat.sub_0_r.
          unfold limbZ. rewrite nth_upd_same by (rewrite Hcur; lia).
          rewrite (smul_lo_word (bv_unsigned w) y c) by lia.
          unfold limbZ in Ec'. rewrite <- Hw in Ec'.
          apply smul_top_nonzero; try lia.
          destruct BN as [BN|BN]; [lia|]. cbn [Nat.sub] in BN. rewrite Nat.sub_0_r in BN. unfold limbZ in BN. rewrite <- Hw in BN. lia.
      + (* [comment removed for export] *)
        cond_cleanup Hz.
        pose proof (smul_carry_room ws _ y _ _ INV' ltac:(lia) ltac:(rewrite Hil; lia)) as ROOM.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_not_taken.
        pose proof (u64arr_store_ok PSEGS m1 A _ len (Z_to_bv 64 (A + 8 * len)) CUR' ltac:(rewrite upd_length; lia) eq_refl) as SOK2.
        step. (* [comment removed for export] *)
        pose proof (u64arr_write PSEGS m1 A _ len (Z_to_bv 64 c') CUR' ltac:(rewrite upd_length; lia)) as CUR''.
        store_done.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        unfold small_mul_post. finish.
        { exact CUR''. } { rewrite !upd_length. exact Hcur. } { exact LC. } all: try lia.
        * replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia. replace (Z.to_nat len) with (S i) by lia.
          rewrite (Z.mul_comm (bval ws _) y). subst c'. apply (smul_inv_finish_carry ws _ y (S i)); [exact INV'| rewrite Hlen; lia].
        * intros Hy BN. replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia.
          apply bnorm_push; [rewrite upd_length, Hcur; lia|]. rewrite unsigned_lit by lia. lia.
  Qed.
End Loop.

Section Loop2.
  Context (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (vec yw : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
          (ws : list word) (len : Z)
          (Hlen : length ws = 62%nat) (LEN : (0 < len <= 62)%Z)
          (CAP : (bval ws (Z.to_nat len) * bv_unsigned yw < BIG_CAP)%Z).
  #[using="Hlen LEN CAP"] Lemma sm_loop : forall k, loop_ok ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 vec yw F fc m0 ws len k.
  Proof. LiaFast.lf_pins (fun (Hlen LEN CAP : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH].
    - unfold loop_ok. intros. exfalso. lia.
    - apply loop_body; assumption.
  Qed.
End Loop2.

Lemma small_mul_spec : small_mul_stmt.
Proof.
  unfold small_mul_stmt. intros until len. intros LIMBS Hlen LC LEN CAP.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bd. rewrite Hlen in Bd.
  pose proof (munch_refl (small_mul_W (bv_unsigned a0)) m) as MU.
  pose proof (wmono_refl PSEGS m) as WM.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite zx16_lit by lia.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hz.
  - (* [comment removed for export] *)
    cond_cleanup Hz.
    step. (* [comment removed for export] *)
    unfold small_mul_post. finish.
    { exact LIMBS. } { exact Hlen. } { exact LC. } all: try lia.
    + subst len. change (Z.to_nat 0) with 0%nat. rewrite bval_0. lia.
    + intros _ BN. exact BN.
  - cond_cleanup Hz.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit len) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    replace (len * 2 ^ 3)%Z with (8 * len)%Z by lia.
    eapply (sm_loop ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a1 F fc m ws len
              Hlen ltac:(lia) CAP (Z.to_nat len) 0%nat a0); try eassumption; try lia.
    apply smul_inv_init.
Qed.
End P_small_mul.


Module P_parse_mantissa.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Wbig_tac Wbig_bigadd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_bigadd OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_small_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_parse_mantissa_2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1 OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section Proof.
  Set Default Proof Using "All".
  Hypothesis small_mul_spec : small_mul_stmt.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i : word).
  Variables (resv numv mdw dv : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (ws : list word) (iptr fptr : word) (ibs fbs : list byte).
  Variables (ilen flen maxd : Z).
  Hypothesis Hilen : ilen = Z.of_nat (length ibs).
  Hypothesis Hflen : flen = Z.of_nat (length fbs).
  Hypothesis Hmaxd : maxd = bv_unsigned mdw.
  Hypothesis Hws : length ws = 62%nat.
  Hypothesis MAXD : (0 < maxd <= 769)%Z.
  Hypothesis XAL : (bv_unsigned resv mod 8 = 0)%Z.
  Hypothesis ALIGN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis INZ : (bv_unsigned iptr <> 0)%Z.
  Hypothesis IEND : (bv_unsigned iptr + ilen < 2^64)%Z.
  Hypothesis ILEN : (0 <= ilen < 2^40)%Z.
  Hypothesis FEND : (bv_unsigned fptr + flen < 2^64)%Z.
  Hypothesis FLEN : (0 <= flen < 2^40)%Z.
  Hypothesis FNULL : boxed (bv_unsigned fptr = 0 -> length fbs = 0%nat)%Z.
  Hypothesis FBS0 : boxed (bytes_at PSEGS m0 (bv_unsigned fptr) fbs).
  Hypothesis LAY0 : (0x22000 <= bv_unsigned sp - 144)%Z.
  Hypothesis LAY1 : (bv_unsigned sp <= bv_unsigned numv + 32)%Z.
  Hypothesis LAY2 : (bv_unsigned numv + 64 <= bv_unsigned resv)%Z.
  Hypothesis LAY3 : (bv_unsigned resv + 498 <= bv_unsigned dv)%Z.
  Hypothesis LAY4 : (bv_unsigned dv + 8 <= bv_unsigned iptr \/ 16 <= bv_unsigned iptr /\ bv_unsigned iptr + Z.of_nat (length ibs) <= bv_unsigned sp - 144)%Z.
  Hypothesis LAY5 : boxed (bv_unsigned fptr <> 0 -> bv_unsigned dv + 8 <= bv_unsigned fptr \/ 16 <= bv_unsigned fptr /\ bv_unsigned fptr + Z.of_nat (length fbs) <= bv_unsigned sp - 144)%Z.

  Notation A := (bv_unsigned resv).
  Notation D := (bv_unsigned dv).
  Notation NP := (bv_unsigned numv).
  Notation IP := (bv_unsigned iptr).
  Notation FP := (bv_unsigned fptr).
  Notation SP := (bv_unsigned sp).
  Notation W := [((SP - 144)%Z, SP); (A, (A + 498)%Z); (D, (D + 8)%Z)].
  Notation POST := (parse_mantissa_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i F fc A D maxd ws m0).
  Notation FRHI m := (rw_cells PSEGS m (SP + -104)
     [C8 s11i; C8 s10i; C8 s9i; C8 s8i; C8 s7i; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]).
  Notation NUMF m := (rw_cells PSEGS m (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)]).
  Notation VAL cur len K := (boxed (bnorm cur (Z.to_nat len) /\ (bval cur (Z.to_nat len) < 2 ^ (64 * K))%Z)).

  Ltac bounds :=
    pose proof (bv_unsigned_in_range 64 resv) as RA; unfold bv_modulus in RA;
    pose proof (bv_unsigned_in_range 64 dv) as RDv; unfold bv_modulus in RDv;
    pose proof (bv_unsigned_in_range 64 numv) as RN; unfold bv_modulus in RN;
    pose proof (bv_unsigned_in_range 64 iptr) as RI; unfold bv_modulus in RI;
    pose proof (bv_unsigned_in_range 64 fptr) as RF; unfold bv_modulus in RF;
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp.

  #[local] Definition end_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.end_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.end_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv dv F fc m0 ws maxd).
  #[local] Definition end_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.end_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition diginc_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.diginc_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.diginc_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv dv F fc m0 ws maxd).
  #[local] Definition diginc_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.diginc_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Notation FRLO3 w8 w16 w24 m := (rw_cells PSEGS m (SP + -144) [C8 numv; C8 w8; C8 w16; C8 w24; C8 resv]).
  Notation ADDV ws1 n1 y K := (boxed (bnorm ws1 n1 /\ (0 <= y)%Z /\ (bval ws1 n1 + y < 2 ^ (64 * K))%Z /\ (0 <= K <= 61)%Z)).

  #[local] Definition cap_of_K := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.cap_of_K small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition rupush_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.rupush_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.rupush_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws maxd).
  #[local] Definition rupush_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.rupush_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ru1add_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ru1add_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ru1add_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws maxd).
  #[local] Definition ru1add_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ru1add_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ru2add_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ru2add_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ru2add_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws maxd).
  #[local] Definition ru2add_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ru2add_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ru_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ru_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ru_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws maxd).
  #[local] Definition ru1_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ru1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ru2_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ru2_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftb1_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftb1_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftb1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition ftb8_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftb8_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftb8_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition ftb_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftb_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftb_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition ftaend_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftaend_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftaend_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition fta1_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.fta1_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.fta1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fta8_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.fta8_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.fta8_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fta_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.fta_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.fta_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition itb_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.itb_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.itb_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition ita_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ita_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ita_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition it1_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.it1_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.it1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition it8_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.it8_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.it8_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition it_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.it_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.it_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  Ltac pre := bounds;
    try (lazymatch goal with XL : u64arr PSEGS ?m A ?cur, Hcur : length ?cur = 62%nat |- _ =>
           pose proof (u64arr_bound _ _ _ _ XL) as BdX; rewrite Hcur in BdX end).

  #[local] Definition ftb1_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftb1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftb8_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftb8_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftb_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftb_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftaend_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftaend_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fta1_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.fta1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fta8_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.fta8_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fta_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.fta_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fbs_now := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.fbs_now small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition itb_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.itb_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ita_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ita_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition it1_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.it1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition it8_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.it8_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition it_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.it_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition itadd_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.itadd_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.itadd_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition itadd_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.itadd_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftadd_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftadd_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftadd_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition ftadd_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.ftadd_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition iadd_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.iadd_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.iadd_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition iadd_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.iadd_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fadd_ok := Eval cbv beta delta [OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.fadd_ok] in (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.fadd_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition fadd_proof := (@OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_2.P_parse_mantissa_1.fadd_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition itrunc_ok := Eval cbv beta delta [P_parse_mantissa_2.itrunc_ok] in (@P_parse_mantissa_2.itrunc_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition ftrunc_ok := Eval cbv beta delta [P_parse_mantissa_2.ftrunc_ok] in (@P_parse_mantissa_2.ftrunc_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition itrunc_proof := (@P_parse_mantissa_2.itrunc_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition ftrunc_proof := (@P_parse_mantissa_2.ftrunc_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fback_ok := Eval cbv beta delta [P_parse_mantissa_2.fback_ok] in (@P_parse_mantissa_2.fback_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fmul_ok := Eval cbv beta delta [P_parse_mantissa_2.fmul_ok] in (@P_parse_mantissa_2.fmul_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition f1_ok := Eval cbv beta delta [P_parse_mantissa_2.f1_ok] in (@P_parse_mantissa_2.f1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition f1entry_ok := Eval cbv beta delta [P_parse_mantissa_2.f1entry_ok] in (@P_parse_mantissa_2.f1entry_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition f8body_ok := Eval cbv beta delta [P_parse_mantissa_2.f8body_ok] in (@P_parse_mantissa_2.f8body_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fout_ok := Eval cbv beta delta [P_parse_mantissa_2.fout_ok] in (@P_parse_mantissa_2.fout_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  Notation TBL10 := P_parse_mantissa_2.TBL10.
  #[local] Definition TBL10_ok := (@P_parse_mantissa_2.TBL10_ok small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition TBL10_nth := (@P_parse_mantissa_2.TBL10_nth small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Ltac introsF := intros FRLO FRH ST XL Hcur XC DG NUM IBS FBS FNZ FPD MU WM PR LEN DGB Hw8.

  #[local] Definition fback_proof := (@P_parse_mantissa_2.fback_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fmul_proof := (@P_parse_mantissa_2.fmul_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition f1_proof := (@P_parse_mantissa_2.f1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition f1entry_proof := (@P_parse_mantissa_2.f1entry_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Ltac f8_body_steps p FBS off :=
    pose proof (ro_block PSEGS _ FP fbs off 8 FBS ltac:(lia)) as BLK;
    replace (FP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia;
    do 45 step;
    clear BLK.

  #[local] Definition f8body0_proof := (@P_parse_mantissa_2.f8body0_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition f8body1_proof := (@P_parse_mantissa_2.f8body1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fout_proof := (@P_parse_mantissa_2.fout_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Notation FRLOJ j1 j2 m := (rw_cells PSEGS m (SP + -144) [C8 numv; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 88576); C8 resv]).

  #[local] Definition fconst_ok := Eval cbv beta delta [P_parse_mantissa_2.fconst_ok] in (@P_parse_mantissa_2.fconst_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fz1_ok := Eval cbv beta delta [P_parse_mantissa_2.fz1_ok] in (@P_parse_mantissa_2.fz1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fzmid_ok := Eval cbv beta delta [P_parse_mantissa_2.fzmid_ok] in (@P_parse_mantissa_2.fzmid_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fz8_ok := Eval cbv beta delta [P_parse_mantissa_2.fz8_ok] in (@P_parse_mantissa_2.fz8_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fz_ok := Eval cbv beta delta [P_parse_mantissa_2.fz_ok] in (@P_parse_mantissa_2.fz_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd).
  #[local] Definition fset_ok := Eval cbv beta delta [P_parse_mantissa_2.fset_ok] in (@P_parse_mantissa_2.fset_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  Ltac introsE := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB V HK HKd.

  #[local] Definition fconst_proof := (@P_parse_mantissa_2.fconst_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fz1_proof := (@P_parse_mantissa_2.fz1_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fzmid_proof := (@P_parse_mantissa_2.fzmid_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fz8_proof := (@P_parse_mantissa_2.fz8_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fz_proof := (@P_parse_mantissa_2.fz_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition fset_proof := (@P_parse_mantissa_2.fset_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition iback_ok := Eval cbv beta delta [P_parse_mantissa_2.iback_ok] in (@P_parse_mantissa_2.iback_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition imul_ok := Eval cbv beta delta [P_parse_mantissa_2.imul_ok] in (@P_parse_mantissa_2.imul_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition i1_ok := Eval cbv beta delta [P_parse_mantissa_2.i1_ok] in (@P_parse_mantissa_2.i1_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition i1entry_ok := Eval cbv beta delta [P_parse_mantissa_2.i1entry_ok] in (@P_parse_mantissa_2.i1entry_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition i8body_ok := Eval cbv beta delta [P_parse_mantissa_2.i8body_ok] in (@P_parse_mantissa_2.i8body_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  #[local] Definition iout_ok := Eval cbv beta delta [P_parse_mantissa_2.iout_ok] in (@P_parse_mantissa_2.iout_ok ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs ilen flen maxd).
  Ltac introsI := intros FRLO FRH ST XL Hcur XC DG NUM IBS MU WM PR LEN DGB Hw8.

  #[local] Definition frlo3_to_J := (@P_parse_mantissa_2.frlo3_to_J small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition iback_proof := (@P_parse_mantissa_2.iback_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  #[local] Definition imul_proof := (@P_parse_mantissa_2.imul_proof small_mul_spec ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i resv numv mdw dv F fc m0 ws iptr fptr ibs fbs ilen flen maxd Hilen Hflen Hmaxd Hws MAXD XAL ALIGN INZ IEND ILEN FEND FLEN FNULL FBS0 LAY0 LAY1 LAY2 LAY3 LAY4 LAY5).
  Lemma i1_proof : forall kk, imul_ok kk -> forall k, i1_ok kk k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IM. induction k as [|k IH]; unfold i1_ok; intros until dg; introsI; intros V HK Hcnt Hk Hcd HKd DGM Hoff Hp Hkk; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block PSEGS m IP ibs off 1 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H19; cond_cleanup H19.
    { eapply (IM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K w8); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia. }
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (IM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K w8); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia. }
    step. (* [comment removed for export] *)
    if_cases Hm; cond_cleanup Hm.
    - eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K w8); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
    - eapply (IM (S off) (Z_to_bv 64 (bv_unsigned p + 1)) _ (cnt + 1)%Z K w8); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
  Qed.

  Lemma i1entry_proof : forall kk, imul_ok kk -> (forall k, i1_ok kk k) -> i1entry_ok kk.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IM I1. unfold i1entry_ok; intros until dg; introsI; intros V HK Hcnt Hcd HKd H0 Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (IM off p vw cnt K w8); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    if_cases Hg; cond_cleanup Hg.
    { eapply (IM off p vw cnt K w8); try eassumption; try lia. }
    eapply (I1 (Z.to_nat (19 - cnt)) off p vw cnt K w8); try eassumption; try lia.
  Qed.

  Ltac i8_body_steps p IBS off :=
    pose proof (ro_block PSEGS _ IP ibs off 8 IBS ltac:(lia)) as BLK;
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia;
    do 45 step;
    clear BLK.

  Lemma i8body0_proof : forall kk, i1entry_ok kk -> i8body_ok kk 0.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IE. unfold i8body_ok; intros until dg; introsI; intros V HK Hz Hcd HKd DGM Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    i8_body_steps p IBS off.
    step. (* [comment removed for export] *)
    if_cases Hc. { exfalso. exact (f8flag0 _ Hc). } clear Hc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (IE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
    all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma i8body1_proof : forall kk, i1entry_ok kk -> i8body_ok kk 0 -> i8body_ok kk 1.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros kk IE I80. unfold i8body_ok; intros until dg; introsI; intros V HK Hz Hcd HKd DGM Hoff Hp Hkk; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    i8_body_steps p IBS off.
    step. (* [comment removed for export] *)
    if_cases Hc.
    - pose proof (f8flag1 (ilen - Z.of_nat off - 8) ltac:(lia) Hc) as H16. clear Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb; cond_cleanup Hb.
      + eapply (IE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ 8%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; lia.
      + replace (Z_to_bv 64 (ilen - Z.of_nat off - 8 + -8)) with (Z_to_bv 64 (ilen - Z.of_nat (off + 8) - 8)) by (f_equal; lia).
        replace (Z_to_bv 64 (maxd - dg + -8)) with (Z_to_bv 64 (maxd - (dg + 8))) by (f_equal; lia).
        eapply (I80 (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ 8%Z K w8); try eassumption; try lia.
        all: rewrite ?unsigned_lit by lia; lia.
    - pose proof (f8flag1' (ilen - Z.of_nat off - 8) ltac:(lia) Hc) as H16. clear Hc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (IE (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) _ (cnt0 + 8)%Z K w8); try eassumption; try lia.
      all: rewrite ?unsigned_lit by lia; lia.
  Qed.

  Lemma iout_proof : fset_ok -> itrunc_ok -> (forall k, iadd_ok k) -> forall k, iout_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FS IT IADD. induction k as [|k IH]; unfold iout_ok; intros until dg; introsI; intros V HK HKd DGM Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (iback_proof k FS IH) as IB.
    pose proof (imul_proof k IT IB IADD) as IM.
    pose proof (i1_proof k IM) as I1.
    pose proof (i1entry_proof k IM I1) as IE.
    pose proof (i8body0_proof k IE) as I80.
    pose proof (i8body1_proof k IE I80) as I81.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (IP + ilen)) by lia.
    replace (Z_to_bv 64 (IP + ilen - bv_unsigned p)) with (Z_to_bv 64 (ilen - Z.of_nat off)) by (f_equal; lia).
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (IE off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite Hw8. replace (Z_to_bv 64 (IP + ilen - 8 - bv_unsigned p)) with (Z_to_bv 64 (ilen - Z.of_nat off - 8)) by (f_equal; lia).
      step. (* [comment removed for export] *)
      rewrite <- Hmaxd.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit dg) in * by lia.
      if_cases Hc; cond_cleanup Hc.
      + eapply (IE off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia.
      + eapply (I81 off p (Z_to_bv 64 0) 0%Z K w8); try eassumption; try lia.
  Qed.
  Notation FRLO0 j0 m := (rw_cells PSEGS m (SP + -144) [C8 numv; CB 24 j0; C8 resv]).

  Definition iconst_ok : Prop :=
    forall (off : nat) (p : word) (j1 j2 : list byte) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
      FRLOJ j1 j2 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A ws -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 x10 x11 x12 x13 x14 x15 x16 x17 mdw x19 x20 (Z_to_bv 64 (IP + ilen)) p x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x253b8) fc None m (seg_rom PSEGS)).

  Definition iz1_ok (k : nat) : Prop :=
    forall (off : nat) (p pendw : word) (j1 j2 : list byte) (x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
      FRLOJ j1 j2 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A ws -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (length ibs - off <= k)%nat -> (off < length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z -> bv_unsigned pendw = (IP + ilen)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 pendw (Z_to_bv 64 48) x12 x13 x14 x15 x16 x17 mdw x19 x20 (Z_to_bv 64 (IP + ilen)) p x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x253a4) fc None m (seg_rom PSEGS)).

  Definition izmid_ok : Prop :=
    forall (off : nat) (p : word) (j1 j2 : list byte) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
      FRLOJ j1 j2 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A ws -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 p x11 x12 x13 x14 x15 x16 x17 mdw x19 x20 (Z_to_bv 64 (IP + ilen)) p x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25394) fc None m (seg_rom PSEGS)).

  Definition izpre_ok : Prop :=
    forall (off : nat) (p : word) (j0 : list byte) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
      FRLO0 j0 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A ws -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (off <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 p x11 x12 x13 x14 x15 x16 x17 mdw x19 x20 (Z_to_bv 64 (IP + ilen)) p x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25388) fc None m (seg_rom PSEGS)).

  Definition iz8_ok (k : nat) : Prop :=
    forall (off : nat) (p : word) (j0 : list byte) (x1 x5 x6 x7 x9 x14 x15 x16 x17 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
      FRLO0 j0 m -> FRHI m -> stk PSEGS m (SP + -144) (SP + -144) ->
      u64arr PSEGS m A ws -> rw_cells PSEGS m (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells PSEGS m D [C8 (Z_to_bv 64 0)] -> NUMF m -> bytes_at PSEGS m IP ibs ->
      munch W m0 m -> wmono PSEGS m0 m -> pristine m 0x10000 0x22000 ->
      (length ibs - off <= k)%nat -> (off + 8 <= length ibs)%nat -> bv_unsigned p = (IP + Z.of_nat off)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 dv x9 p (Z_to_bv 64 (ilen - Z.of_nat off)) (Z_to_bv 64 3472328296227680304) (Z_to_bv 64 7) x14 x15 x16 x17 mdw x19 x20 (Z_to_bv 64 (IP + ilen)) p x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25314) fc None m (seg_rom PSEGS)).

  Ltac introsZ := intros FRLO FRH ST XL XC DG NUM IBS MU WM PR.

  Lemma val0 : VAL ws 0 0.
  Proof. LiaFast.lf_pins LiaFast.lf_all. unfold boxed. split. { apply bnorm_0. } change (Z.to_nat 0) with 0%nat. rewrite bval_0. cbn. lia. Qed.

  Lemma iconst_proof : fset_ok -> (forall k, iout_ok k) -> iconst_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FS IOUT. unfold iconst_ok; intros until m; introsZ; intros Hoff Hp; pre.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX'. rewrite Hws in BdX'.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (FS tt 0%Z j1 j2); try eassumption; try lia. apply val0. }
    do 19 step.
    eapply (IOUT (length ibs - off)%nat off p 0%Z (Z_to_bv 64 (IP + ilen + -8))); try eassumption; try lia.
    { rewrite unsigned_lit by lia. lia. }
    apply val0.
  Qed.

  Lemma iz1_proof : iconst_ok -> forall k, iz1_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IC. induction k as [|k IH]; unfold iz1_ok; intros until m; introsZ; intros Hk Hoff Hp Hpe; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (bv_unsigned_in_range 64 pendw) as Rpe; unfold bv_modulus in Rpe.
    pose proof (ro_block PSEGS m IP ibs off 1 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    step. (* [comment removed for export] *)
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { eapply (IC off p j1 j2); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb.
    - eapply (IH (S off) (Z_to_bv 64 (bv_unsigned p + 1)) pendw j1 j2); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      eapply (IC (length ibs) pendw j1 j2); try eassumption; try lia.
  Qed.

  Lemma izmid_proof : fset_ok -> (forall k, iz1_ok k) -> izmid_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros FS IZ1. unfold izmid_ok; intros until m; introsZ; intros Hoff Hp; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    if_cases He; cond_cleanup He.
    { eapply (FS tt 0%Z j1 j2); try eassumption; try lia. apply val0. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (IZ1 (length ibs - off)%nat off p _ j1 j2); try eassumption; try lia.
    rewrite (unsigned_lit (IP + ilen)) by lia. rewrite !unsigned_lit by lia. lia.
  Qed.

  Lemma izpre_proof : izmid_ok -> izpre_ok.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IM. unfold izpre_ok; intros until m; introsZ; intros Hoff Hp; pre.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with FR : rw_cells PSEGS ?m1 (SP + -144) [C8 numv; CB 16 ?j; C8 _; C8 resv] |- _ =>
      pose proof (rw_cells_split_CB PSEGS m1 (SP + -144) [C8 numv] 16 j [C8 (Z_to_bv 64 88576); C8 resv] [8; 8]%nat FR eq_refl) as FRJ;
      cbn [mk_CB_cells app] in FRJ; clear FR
    end.
    eapply (IM off p); try eassumption; try lia.
  Qed.

  Lemma iz8_proof : izpre_ok -> forall k, iz8_ok k.
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IP8. induction k as [|k IH]; unfold iz8_ok; intros until m; introsZ; intros Hk Hoff Hp; pre.
    { exfalso; lia. }
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp.
    pose proof (ro_block PSEGS m IP ibs off 8 IBS ltac:(lia)) as BLK.
    replace (IP + Z.of_nat off)%Z with (bv_unsigned p) in BLK by lia.
    do 22 step.
    clear BLK.
    step. (* [comment removed for export] *)
    if_cases Hc; clear Hc.
    { eapply (IP8 off p j0); try eassumption; try lia. }
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hb; cond_cleanup Hb; rewrite ?signed_lit in Hb by lia.
    - replace (Z_to_bv 64 (ilen - Z.of_nat off + -8)) with (Z_to_bv 64 (ilen - Z.of_nat (off + 8))) by (f_equal; lia).
      eapply (IH (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) j0); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
    - step. (* [comment removed for export] *)
      eapply (IP8 (off + 8)%nat (Z_to_bv 64 (bv_unsigned p + 8)) j0); try eassumption; try lia.
      rewrite unsigned_lit by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma body_ok : izpre_ok -> (forall k, iz8_ok k) ->
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 dg0 : word),
      stk PSEGS m0 (SP - 144) SP ->
      u64arr PSEGS m0 A ws -> rw_cells PSEGS m0 (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells PSEGS m0 (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)] ->
      bytes_at PSEGS m0 IP ibs -> rw_cells PSEGS m0 D [C8 dg0] -> pristine m0 0x10000 0x22000 ->
      evt PSEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0i s1i resv numv mdw dv a4 a5 a6 a7 s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i t3 t4 t5 t6)
            F (Z_to_bv 64 0x252a4) fc None m0 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    intros IZP IZ8. intros until dg0. intros ST XL XC NUM IBS DG PR. bounds.
    pose proof (u64arr_bound _ _ _ _ XL) as BdX. rewrite Hws in BdX.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl PSEGS m0) as WM.
    carve_frame 144%nat ST.
    do 14 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with FR : rw_cells PSEGS ?m1 (SP + -144) ?cs |- _ =>
      chunk_split FR 3%nat FRLO FRH end.
    change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)) in DG |- *.
    step. (* [comment removed for export] *)
    if_cases H8; cond_cleanup H8; rewrite ?signed_lit in H8 by lia.
    - step. (* [comment removed for export] *)
      eapply (IZP 0%nat iptr); try eassumption; try lia.
    - step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      replace (Z_to_bv 64 ilen) with (Z_to_bv 64 (ilen - Z.of_nat 0)) by (f_equal; lia).
      eapply (IZ8 (length ibs) 0%nat iptr); try eassumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma main_ok :
    forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 dg0 : word),
      stk PSEGS m0 (SP - 144) SP ->
      u64arr PSEGS m0 A ws -> rw_cells PSEGS m0 (A + 496) [C2 (Z_to_bv 64 0)] ->
      rw_cells PSEGS m0 (NP + 32) [C8 iptr; C8 (Z_to_bv 64 ilen); C8 fptr; C8 (Z_to_bv 64 flen)] ->
      bytes_at PSEGS m0 IP ibs -> rw_cells PSEGS m0 D [C8 dg0] -> pristine m0 0x10000 0x22000 ->
      evt PSEGS POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0i s1i resv numv mdw dv a4 a5 a6 a7 s2i s3i s4i s5i s6i s7i s8i s9i s10i s11i t3 t4 t5 t6)
            F (Z_to_bv 64 0x252a4) fc None m0 (seg_rom PSEGS)).
  Proof. LiaFast.lf_pins LiaFast.lf_all.
    pose proof end_proof as END.
    pose proof (diginc_proof END) as DIG.
    pose proof (rupush_proof DIG) as PUSH.
    pose proof (ru1add_proof DIG PUSH) as RU1A.
    pose proof (ru2add_proof DIG PUSH) as RU2A.
    pose proof (ru1_proof RU1A) as RU1.
    pose proof (ru2_proof RU2A) as RU2.
    pose proof (ftb1_proof END RU2) as FTB1.
    pose proof (ftb8_proof END RU2 FTB1) as FTB8.
    pose proof (ftb_proof END FTB1 FTB8) as FTB.
    pose proof (ftaend_proof END RU1) as FE.
    pose proof (fta1_proof FE RU1) as FTA1.
    pose proof (fta8_proof FE RU1 FTA1) as FTA8.
    pose proof (fta_proof FE FTA1 FTA8) as FTA.
    pose proof (itb_proof FE FTA) as ITB.
    pose proof (ita_proof END FTA) as ITA.
    pose proof (it1_proof ITB) as IT1.
    pose proof (it8_proof ITB ITA IT1) as IT8.
    pose proof (it_proof ITA IT1 IT8) as IT.
    pose proof (itrunc_proof IT itadd_proof) as ITRUNC.
    pose proof (ftrunc_proof FTB ftadd_proof) as FTRUNC.
    pose proof (fout_proof END FTRUNC fadd_proof) as FOUT.
    pose proof (fconst_proof END FOUT) as FCONST.
    pose proof (fz1_proof FCONST) as FZ1.
    pose proof (fzmid_proof END FZ1) as FZMID.
    pose proof (fz8_proof FZMID) as FZ8.
    pose proof (fz_proof FZMID FZ8) as FZ.
    pose proof (fset_proof END FZ FCONST) as FSET.
    pose proof (iout_proof FSET ITRUNC iadd_proof) as IOUT.
    pose proof (iconst_proof FSET IOUT) as ICONST.
    pose proof (iz1_proof ICONST) as IZ1.
    pose proof (izmid_proof FSET IZ1) as IZMID.
    pose proof (izpre_proof IZMID) as IZPRE.
    pose proof (iz8_proof IZPRE) as IZ8.
    exact (body_ok IZPRE IZ8).
  Qed.
End Proof.

Section Top.
  Hypothesis small_mul_spec : small_mul_stmt.

  Lemma parse_mantissa_spec : parse_mantissa_stmt.
  Proof.
    unfold parse_mantissa_stmt. intros until dg.
    intros ST ALIGN PR XL Hxl XC XAL NUM IBS INZ IEND ILEN FBS FEND FLEN FNULL MAXD DG LAY0 LAY1 LAY2 LAY3 LAY4 LAY5.
    pose proof (bytes_at_bound _ _ _ _ IBS) as BI. pose proof (bytes_at_bound _ _ _ _ FBS) as BF.
    eapply (main_ok small_mul_spec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 F fc m ws iptr fptr ibs fbs
              (Z.of_nat (length ibs)) (Z.of_nat (length fbs)) (bv_unsigned a2)
              eq_refl eq_refl eq_refl Hxl MAXD XAL ALIGN INZ IEND ltac:(lia) FEND ltac:(lia) FNULL FBS LAY0 LAY1 LAY2 LAY3 LAY4 LAY5);
      eassumption.
  Qed.
End Top.
End P_parse_mantissa.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_positive_digit_comp_f_stmt P_negative_digit_comp_f_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spf_DC.P_spf_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spf_tbl OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memset OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spf_DC.P_small_mul OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spf_DC.P_parse_mantissa OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_positive_digit_comp_f_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_negative_digit_comp_f_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma magic_div10000 : forall x, (0 <= x < 2^64)%Z ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (x * 3777893186295716171) 64))) 11 = (x / 10000)%Z.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
  rewrite unsigned_lit by (Z.div_mod_to_equations; nia).
  Z.div_mod_to_equations. nia.
Qed.
Lemma magic_div100 : forall x, (0 <= x < 2^64)%Z ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr x 2)) * 2951479051793528259) 64))) 2 = (x / 100)%Z.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
  rewrite (unsigned_lit (x / 2^2)) by (Z.div_mod_to_equations; nia).
  rewrite unsigned_lit by (Z.div_mod_to_equations; nia).
  Z.div_mod_to_equations. nia.
Qed.
Lemma magic_div10 : forall x, (0 <= x < 2^64)%Z ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (x * 14757395258967641293) 64))) 3 = (x / 10)%Z.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia.
  rewrite unsigned_lit by (Z.div_mod_to_equations; nia).
  Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma sci_T_bound : forall mv T uw, (1 <= mv)%Z -> (0 <= T)%Z -> (mv * 10^T <= uw)%Z -> (uw < 2^64)%Z -> (T <= 19)%Z.
Proof.
  intros mv T uw H1 H2 H3 H4.
  destruct (Z.le_gt_cases T 19) as [|HT]; [assumption|]. exfalso.
  assert (10 ^ 20 <= 10 ^ T)%Z by (apply Z.pow_le_mono_r; lia).
  assert (0 < 10 ^ T)%Z by (apply Z.pow_pos_nonneg; lia).
  nia.
Qed.
Lemma pow10_step : forall mv d k uw, (0 <= d)%Z -> (0 < k)%Z -> (0 <= mv)%Z -> (mv * 10^d <= uw)%Z ->
  ((mv / 10^k) * 10^(d + k) <= uw)%Z.
Proof.
  intros mv d k uw Hd Hk Hmv H. rewrite Z.pow_add_r by lia.
  assert (0 < 10 ^ k)%Z by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 10 ^ d)%Z by (apply Z.pow_pos_nonneg; lia).
  assert ((mv / 10 ^ k) * 10 ^ k <= mv)%Z by (Z.div_mod_to_equations; nia).
  nia.
Qed.

Lemma bytes_at_slice : forall m A bs i n, bytes_at PSEGS m A bs -> (i + n <= length bs)%nat ->
  bytes_at PSEGS m (A + Z.of_nat i) (firstn n (skipn i bs)).
Proof.
  intros m A bs i n H Hle.
  rewrite <- (firstn_skipn i bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn n (skipn i bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma cb2_c2_zero : forall m A,
  rw_cells PSEGS m A [CB 2 (repeat (Z_to_bv 8 0) 2)] -> rw_cells PSEGS m A [C2 (Z_to_bv 64 0)].
Proof.
  intros m A [[Hwf Hb] Hw]. split; [split|]; [cbn; tauto | exact Hb | exact Hw].
Qed.

Lemma shiftr_small_0 : forall dg n, (0 <= dg < 2^32)%Z -> (32 <= n)%Z -> Z.shiftr dg n = 0%Z.
Proof.
  intros dg n H Hn. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. split; [lia|].
  eapply Z.lt_le_trans; [apply (proj2 H)|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Lemma c8_as_c4s : forall m A dg, (0 <= dg < 2^32)%Z ->
  rw_cells PSEGS m A [C8 (Z_to_bv 64 dg)] -> rw_cells PSEGS m A [C4 (Z_to_bv 64 dg); C4 (Z_to_bv 64 0)].
Proof.
  intros m A dg Hdg [[Hwf Hb] Hw]. split; [split|]; [cbn; tauto | | exact Hw].
  revert Hb. cbn [cells_bytes cbytes app]. unfold le8, le4, word_to_le_bytes.
  rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes app].
  rewrite !Z.shiftr_shiftr by lia.
  rewrite (shiftr_small_0 dg (8+8+8+8)) by lia. rewrite (shiftr_small_0 dg (8+8+8+8+8)) by lia.
  rewrite (shiftr_small_0 dg (8+8+8+8+8+8)) by lia. rewrite (shiftr_small_0 dg (8+8+8+8+8+8+8)) by lia.
  rewrite !Z.shiftr_0_l. exact (fun H => H).
Qed.

Lemma dc_exp_eq : forall (q : word) (T dg : Z), (-342 <= bv_signed q <= 308)%Z -> (0 <= T <= 19)%Z -> (0 <= dg <= 770)%Z ->
  bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_unsigned q + T)) - bv_unsigned (sx32 (Z_to_bv 64 dg))))) + 1)
  = (bv_signed q + T - dg + 1)%Z.
Proof.
  intros q T dg Hq HT Hdg. pose proof (zb_signed q) as SQ.
  pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
  unfold sx32. rewrite !unsigned_lit_wrap. swrap_unfold.
  destruct (Z.ltb_spec0 (bv_unsigned q) (2^63)); Z.div_mod_to_equations; lia.
Qed.

Section ZLEMMAS.
Open Scope Z_scope.
(* [comment removed for export] *)
#[using="Type"] Lemma cap_pos : forall b dg e, 0 <= dg -> 0 <= e -> e + dg <= 329 -> 0 <= b ->
  b < 2 ^ (64 * (dg / 19 + 3)) -> b * 10 ^ e < BIG_CAP.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros b dg e Hdg He Hs Hb Hlt. unfold BIG_CAP.
  assert (H10 : 10 ^ e <= 2 ^ (4 * e)).
  { rewrite Z.pow_mul_r by lia. change (2 ^ 4) with 16. apply Z.pow_le_mono_l. lia. }
  assert (H2 : 2 ^ (64 * (dg / 19 + 3)) * 2 ^ (4 * e) <= 2 ^ 3968).
  { rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; [lia|]. Z.div_mod_to_equations. lia. }
  assert (0 < 10 ^ e) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= 2 ^ (4 * e)) by (apply Z.pow_nonneg; lia).
  nia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma dc_zx32 : forall X : Z,
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 X)) 32))) 32)) = X mod 2^32.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite !unsigned_lit_wrap.
  Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma dc_zx32' : forall X : Z,
  bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 X) + 32768))) 32))) 32))
  = (X + 32768) mod 2^32.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X. rewrite dc_zx32. rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia.
Qed.
End ZLEMMAS.

Section BLK.
  Variable c : spf_ctx.
  Hypothesis PRE : spf_pre c.
  #[local] Notation ra := (r_ra c).   #[local] Notation sp := (r_sp c).
  #[local] Notation gp := (r_gp c).   #[local] Notation tp := (r_tp c).
  #[local] Notation t0 := (r_t0 c).   #[local] Notation t1 := (r_t1 c).
  #[local] Notation t2 := (r_t2 c).
  #[local] Notation s0 := (r_s0 c).   #[local] Notation s1 := (r_s1 c).
  #[local] Notation a0 := (r_a0 c).   #[local] Notation a1 := (r_a1 c).
  #[local] Notation a2 := (r_a2 c).   #[local] Notation a3 := (r_a3 c).
  #[local] Notation a4 := (r_a4 c).   #[local] Notation a5 := (r_a5 c).
  #[local] Notation a6 := (r_a6 c).   #[local] Notation a7 := (r_a7 c).
  #[local] Notation s2 := (r_s2 c).   #[local] Notation s3 := (r_s3 c).
  #[local] Notation s4 := (r_s4 c).   #[local] Notation s5 := (r_s5 c).
  #[local] Notation s6 := (r_s6 c).   #[local] Notation s7 := (r_s7 c).
  #[local] Notation s8 := (r_s8 c).   #[local] Notation s9 := (r_s9 c).
  #[local] Notation s10 := (r_s10 c). #[local] Notation s11 := (r_s11 c).
  #[local] Notation t3 := (r_t3 c).   #[local] Notation t4 := (r_t4 c).
  #[local] Notation t5 := (r_t5 c).   #[local] Notation t6 := (r_t6 c).
  #[local] Notation F := (r_F c).     #[local] Notation fc := (r_fc c).
  #[local] Notation m0 := (r_m0 c).   #[local] Notation bs := (r_bs c).
  #[local] Notation v := (r_v c).
  #[local] Notation P := (bv_unsigned (r_a0 c)).
  #[local] Notation E := (bv_unsigned (r_a1 c)).
  #[local] Notation V := (bv_unsigned (r_a2 c)).
  #[local] Notation L := (bv_unsigned (r_a1 c) - bv_unsigned (r_a0 c))%Z.
  #[local] Notation SP := (bv_unsigned (r_sp c) + -688)%Z.
  #[local] Notation NEED := slow_path_float_need.
  #[local] Notation POST := (slow_path_float_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_float_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL4 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0; pose proof (pre_VLO c PRE) as VLO;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_float_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_float_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_float_need in ST; unfold P_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Notation mI := (r_m0 c).
  #[local] Notation Zw z := (Z_to_bv 64 z).


  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_float_need in ST; unfold P_FMIN in PR2;
    cbv beta delta [slow_path_float_W slow_path_float_need] in MU;
    unfold frameP, savesC in FR; cbn [app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  #[local] Ltac gen_val e := let X := fresh "rv" in set (X := e) in |- *; clearbody X.
  #[local] Ltac gen_big :=
    repeat match goal with
    | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
    | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
    | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
    | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
    | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
    | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
    | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
    | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
    | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
    | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
    | |- context [Some (v_sltiu ?a ?b)] => gen_val (v_sltiu a b)
    | |- context [Some (v_sltu ?a ?b)] => gen_val (v_sltu a b)
    | |- context [Some (v_slt ?a ?b)] => gen_val (v_slt a b)
    | |- context [Some (v_slti ?a ?b)] => gen_val (v_slti a b)
    end.
  #[local] Ltac gstep := step; gen_big.
  (* [comment removed for export] *)
  #[local] Ltac pose_sp_lits :=
    repeat match goal with |- context [Some (Z_to_bv 64 (bv_unsigned (r_sp c) + ?k)%Z)] =>
      lazymatch goal with
      | _ : bv_unsigned (Z_to_bv 64 (bv_unsigned (r_sp c) + k)%Z) = _ |- _ => fail
      | _ => pose proof (unsigned_lit (bv_unsigned (r_sp c) + k)%Z ltac:(lia))
      end end.
  #[local] Ltac rewrite_sp_lits :=
    repeat match goal with U : bv_unsigned (Z_to_bv 64 (bv_unsigned (r_sp c) + ?k)%Z) = _ |- _ => rewrite !U end.
  #[local] Ltac rewrite_sp_lits_all :=
    repeat match goal with U : bv_unsigned (Z_to_bv 64 (bv_unsigned (r_sp c) + ?k)%Z) = _ |- _ => rewrite !U in *; clear U end.

  (* [comment removed for export] *)
  #[local] Ltac exact_at H :=
    first [ exact H
          | lazymatch goal with
            | |- rw_cells _ _ ?a _ => lazymatch type of H with rw_cells _ _ ?b _ => replace a with b by lia; exact H end
            | |- u64arr _ _ ?a _ => lazymatch type of H with u64arr _ _ ?b _ => replace a with b by lia; exact H end
            | |- bytes_at _ _ ?a _ => lazymatch type of H with bytes_at _ _ ?b _ => replace a with b by lia; exact H end
            | |- stk _ _ ?a ?b => lazymatch type of H with stk _ _ ?a' ?b' => replace a with a' by lia; replace b with b' by lia; exact H end
            end ].

  Hypothesis positive_digit_comp_f_spec : positive_digit_comp_f_stmt.
  Hypothesis negative_digit_comp_f_spec : negative_digit_comp_f_stmt.
  Hypothesis C_26d50 : K_26d50 c.

  (* [comment removed for export] *)
  #[using="PRE positive_digit_comp_f_spec negative_digit_comp_f_spec C_26d50"] Lemma spf_DC : K_26c4c c.
  Proof. LiaFast.lf_pins (fun (PRE positive_digit_comp_f_spec negative_digit_comp_f_spec C_26d50 : LiaFast.U) => LiaFast.u0).
    unfold K_26d50 in C_26d50.
    unfold K_26c4c. intros m r j5 x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm am ng k3 kI fp fL X TI PN Hq HX.
    pre_facts.
    pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ. specialize (Hw eq_refl).
    pose proof (rw_cells_bound _ _ _ _ VAL) as Bval. cbn [cells_size csize Nat.add] in Bval.
    (* [comment removed for export] *)
    assert (Jdc : forall (T : Z) (v10 v11 v12 v13 v14 : word), (0 <= T <= 19)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 v10 v11 v12 v13 v14 x15 x16 x17
                 (Z_to_bv 64 X) am (Z_to_bv 64 (bv_unsigned q + T)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28bcc) fc None m (seg_rom PSEGS))).
    { intros T v10 v11 v12 v13 v14 HT.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      chunk_split FR 12%nat FRa FRb. chunk_split FRb 1%nat FRo FRc.
      assert (LJ : length (firstn 504 r) = 504%nat) by exact (proj1 (proj1 (proj1 FRo))).
      pose proof (u8arr_of_rw_cells _ _ _ _ _ FRo) as OLD. clear FRo.
      pose_sp_lits. pose proof (unsigned_lit 504 ltac:(lia)) as U504.
      step. (* [comment removed for export] *)
      call memset_spec.
      { reflexivity. }
      { rewrite_sp_lits. exact_at OLD. }
      { rewrite U504, LJ. reflexivity. }
      { rewrite_sp_lits. Z.div_mod_to_equations. lia. }
      rewrite_sp_lits_all. rewrite -> ?U504 in *.
      change (Z.to_nat 504) with 504%nat in *.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
        lazymatch goal with M : bytes_at _ m' _ (repeat _ _), Wt : wr_at _ m' _ _ |- _ =>
          pose proof (conj M Wt : u8arr PSEGS m' _ _) as Z504; clear M Wt; rename m' into m1 end end.
      replace (repeat (Z_to_bv 8 0) 504) with (repeat (Z_to_bv 8 0) (8 * 62) ++ (repeat (Z_to_bv 8 0) 2 ++ repeat (Z_to_bv 8 0) 6))
        in Z504 by reflexivity.
      apply u8arr_app in Z504. destruct Z504 as [ZL Z26]. rewrite repeat_length in Z26.
      apply u8arr_app in Z26. destruct Z26 as [Z2 Z6]. rewrite repeat_length in Z6.
      pose proof (u64arr_of_u8arr PSEGS _ _ 62 _ ZL (repeat_length _ _)) as LIMBS. clear ZL.
      rewrite words_of_bytes_zero in LIMBS.
      pose proof (rw_cells_of_u8arr PSEGS _ _ _ Z2) as LENC. clear Z2. rewrite repeat_length in LENC.
      apply cb2_c2_zero in LENC.
      pose proof (rw_cells_of_u8arr PSEGS _ _ _ Z6) as PAD. clear Z6. rewrite repeat_length in PAD.
      change (Z.of_nat (8 * 62)) with 496%Z in LENC, PAD. change (Z.of_nat 2) with 2%Z in PAD.
      replace (bv_unsigned sp + -688 + 72 + 496)%Z with (bv_unsigned sp + -120)%Z in LENC by lia.
      replace (bv_unsigned sp + -688 + 72 + 496 + 2)%Z with (bv_unsigned sp + -118)%Z in PAD by lia.
      (* [comment removed for export] *)
      chunk_split FRa 7%nat FRh FRm. chunk_split FRm 4%nat FRs FR64.
      set (ibs := firstn (Z.to_nat (kI - k3)) (skipn (Z.to_nat k3) bs)).
      set (fbs := firstn (Z.to_nat fL) (skipn (Z.to_nat (kI + 1)) bs)).
      assert (Libs : Z.of_nat (length ibs) = (kI - k3)%Z).
      { subst ibs. rewrite firstn_length_le; [lia|]. rewrite skipn_length. lia. }
      assert (Lfbs : Z.of_nat (length fbs) = fL).
      { subst fbs. destruct Hfp as [[-> ->]|[Hfp1 Hfp2]]; [reflexivity|].
        rewrite firstn_length_le; [lia|]. rewrite skipn_length. lia. }
      replace (Z_to_bv 64 (kI - k3)) with (Z_to_bv 64 (Z.of_nat (length ibs))) in FRs by (f_equal; lia).
      replace (Z_to_bv 64 fL) with (Z_to_bv 64 (Z.of_nat (length fbs))) in FRs by (f_equal; lia).
      assert (TXi : bytes_at PSEGS m1 (bv_unsigned (Z_to_bv 64 (P + k3))) ibs).
      { rewrite unsigned_lit by lia. subst ibs. replace (P + k3)%Z with (P + Z.of_nat (Z.to_nat k3))%Z by lia.
        apply bytes_at_slice; [assumption | lia]. }
      assert (TXf : bytes_at PSEGS m1 (bv_unsigned (Z_to_bv 64 fp)) fbs).
      { destruct Hfp as [[Hfp1 Hfp2]|[Hfp1 Hfp2]].
        - subst fbs. rewrite Hfp1, Hfp2. rewrite unsigned_lit by lia. cbn [Z.to_nat firstn]. apply bytes_at_nil. lia.
        - rewrite unsigned_lit by lia. subst fbs. rewrite Hfp1.
          replace (P + kI + 1)%Z with (P + Z.of_nat (Z.to_nat (kI + 1)))%Z by lia.
          apply bytes_at_slice; [assumption | lia]. }
      chunk_split FRc 1%nat DIG SAV.
      replace (bv_unsigned sp + -656)%Z with (bv_unsigned sp + -688 + 32)%Z in FRs by lia.
      do 4 step. (* [comment removed for export] *)
      pose_sp_lits.
      pose proof (unsigned_lit (bv_unsigned sp + -688) ltac:(lia)) as USP.
      pose proof (unsigned_lit 114 ltac:(lia)) as U114.
      destruct (stk_split _ _ _ (bv_unsigned sp + -688 - 144)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
      assert (LL : length (repeat (Z_to_bv 64 0) 62) = 62%nat) by apply repeat_length.
      step. (* [comment removed for export] *)
      call (parse_mantissa_spec small_mul_spec).
      { rewrite ?USP. exact_at SThi. }
      { rewrite ?USP. Z.div_mod_to_equations. lia. }
      { exact PR1. }
      { rewrite_sp_lits. exact_at LIMBS. }
      { exact LL. }
      { rewrite_sp_lits. exact_at LENC. }
      { rewrite_sp_lits. Z.div_mod_to_equations. lia. }
      { rewrite ?USP. rewrite_sp_lits. exact_at FRs. }
      { exact TXi. }
      { rewrite unsigned_lit by lia. lia. }
      { rewrite unsigned_lit by lia. lia. }
      { lia. }
      { exact TXf. }
      { destruct Hfp as [[Hfp1 Hfp2]|[Hfp1 Hfp2]]; rewrite Hfp1, ?unsigned_lit by lia; lia. }
      { lia. }
      { intros Hz. destruct Hfp as [[Hfp1 Hfp2]|[Hfp1 Hfp2]]; [| rewrite Hfp1, unsigned_lit in Hz by lia; exfalso; lia].
        apply (f_equal Z.to_nat) in Lfbs. rewrite Nat2Z.id in Lfbs. rewrite Lfbs, Hfp2. reflexivity. }
      { rewrite U114. lia. }
      { rewrite_sp_lits. exact_at DIG. }
      { rewrite ?USP. lia. }
      { rewrite ?USP. lia. }
      { rewrite ?USP. rewrite_sp_lits. lia. }
      { rewrite_sp_lits. lia. }
      { rewrite_sp_lits. rewrite unsigned_lit by lia. lia. }
      { rewrite_sp_lits. intros Hz. destruct Hfp as [[Hfp1 Hfp2]|[Hfp1 Hfp2]]; rewrite Hfp1, ?unsigned_lit in * by lia; lia. }
      rewrite_sp_lits_all. rewrite -> ?USP, -> ?U114 in *.
      clear LL U504 U114. try clear H.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => rename m' into m2 end.
      rename MI into ST2. rename PC into LIMBS. rename PC0 into L62. rename PC1 into LENC. rename PC2 into DIG.
      rename PC3 into Hlen. rename PC4 into Hdg. rename PC5 into NORM. rename POST into BVAL.
      lazymatch type of LIMBS with u64arr _ _ _ ?ws => rename ws into ws1 end.
      lazymatch type of Hlen with (0 <= ?l <= 62)%Z => rename l into len1 end.
      lazymatch type of Hdg with (0 <= ?d <= _)%Z => rename d into dg end.
      pose proof (stk_merge _ _ _ _ _ STlo ST2 ltac:(lia)) as ST. clear STlo ST2.
      apply c8_as_c4s in DIG; [|lia].
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (dc_exp_eq q T dg) by lia.
      set (e := (bv_signed q + T - dg + 1)%Z) in |- *.
      assert (He : (-200 <= e <= 60)%Z) by (subst e; lia).
      assert (Hedg : (0 <= e -> e + dg <= 329)%Z) by (subst e; lia).
      clearbody e.
      (* [comment removed for export] *)
      assert (J40 : forall (m3 : word -> option byte) (ws3 : list word) (len3 : Z)
                           (v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word),
        bytes_at PSEGS m3 P bs ->
        rw_cells PSEGS m3 SP [C8 q; C8 w; C8 lm; C1 (Z_to_bv 8 ng); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); CB 5 j5] ->
        rw_cells PSEGS m3 (SP + 32) [C8 (Z_to_bv 64 (P + k3)); C8 (Z_to_bv 64 (Z.of_nat (length ibs)));
                                     C8 (Z_to_bv 64 fp); C8 (Z_to_bv 64 (Z.of_nat (length fbs)))] ->
        rw_cells PSEGS m3 (bv_unsigned sp + -624) [C8 (Z_to_bv 64 0)] ->
        u64arr PSEGS m3 (bv_unsigned sp + -616) ws3 -> length ws3 = 62%nat ->
        rw_cells PSEGS m3 (bv_unsigned sp + -616 + 496) [C2 (Z_to_bv 64 len3)] ->
        rw_cells PSEGS m3 (bv_unsigned sp + -118) [CB 6 (repeat (Z_to_bv 8 0) 6)] ->
        rw_cells PSEGS m3 (bv_unsigned sp + -112) [C4 (Z_to_bv 64 dg); C4 (Z_to_bv 64 0)] ->
        rw_cells PSEGS m3 (bv_unsigned sp + -104) (savesC c) ->
        stk PSEGS m3 (bv_unsigned sp - (688 + 1808)) SP ->
        rw_cells PSEGS m3 V [C4 v] ->
        pristine m3 65536 139264 -> pristine m3 413152 (413152 + 4) ->
        munch [((bv_unsigned sp - (688 + 1808))%Z, bv_unsigned sp); (V, (V + 4)%Z)] m0 m3 ->
        wmono PSEGS m0 m3 ->
        evt PSEGS POST
          (MS (mkR v1 (Z_to_bv 64 SP) gp tp v5 v6 v7 a2 x9 v10 v11 v12 v13 v14 v15 v16 v17
                   (Z_to_bv 64 X) am (Z_to_bv 64 (bv_unsigned q + T)) x21 x22 x23 x24 x25 x26 x27 v28 v29 v30 v31)
              F (Z_to_bv 64 0x28c30) fc None m3 (seg_rom PSEGS))).
      { intros m3 ws3 len3 v1 v5 v6 v7 y10 y11 y12 y13 y14 y15 y16 y17 v28 v29 v30 v31
               TXT3 FRh3 FRs3 FR643 LIMBS3 L3 LENC3 PAD3 DIG3 SAV3 ST3 VAL3 PR13 PR23 MU3 WM3.
        pose proof (rw_cells_bound _ _ _ _ VAL3) as Bval3. cbn [cells_size csize Nat.add] in Bval3.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose proof (rw_cells_of_u64arr PSEGS _ _ _ LIMBS3) as OBJ. rewrite L3 in OBJ. clear LIMBS3.
        chunk_join FRh3 FRs3 FRa. chunk_join FRa FR643 FRb. chunk_join FRb OBJ FRd.
        chunk_join FRd LENC3 FRe. chunk_join FRe PAD3 FRf. chunk_join FRf DIG3 FRg.
        eapply C_26d50; [exact TXT3 | exact FRg | reflexivity | | exact ST3 | exact VAL3 | exact PR13 | exact PR23 | exact MU3 | exact WM3].
        replace (SP + 584)%Z with (bv_unsigned sp + -104)%Z by lia. exact SAV3. }
      step. (* [comment removed for export] *)
      if_cases Hneg.
      - cond_cleanup Hneg. assert (Hen : (e < 0)%Z) by (rewrite ?signed_lit in Hneg by lia; Z.div_mod_to_equations; lia). clear Hneg.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose_sp_lits. pose proof (unsigned_lit (bv_unsigned sp + -688) ltac:(lia)) as USP.
        step. (* [comment removed for export] *)
        call negative_digit_comp_f_spec.
        { rewrite ?USP. replace (bv_unsigned sp + -688 - 1808)%Z with (bv_unsigned sp - (688 + 1808))%Z by lia. exact ST. }
        { rewrite ?USP. Z.div_mod_to_equations. lia. }
        { rewrite ?USP. lia. }
        { exact PR1. }
        { rewrite_sp_lits. exact_at LIMBS. }
        { exact L62. }
        { rewrite_sp_lits. exact_at LENC. }
        { exact Hlen. }
        { rewrite_sp_lits. Z.div_mod_to_equations. lia. }
        { exact NORM. }
        { match goal with |- bv_unsigned ?t = (?p mod 2^32)%Z => idtac | |- ?g => idtac "P2GOAL:"; idtac g end.
          instantiate (1 := (X + 32768)%Z).
          first [ exact (dc_zx32 (X + 32768)%Z)
                | match goal with |- ?g => idtac "P2FAIL:"; idtac g end; fail ]. }
        { lia. }
        { reflexivity. }
        { lia. }
        { rewrite ?USP. rewrite_sp_lits. lia. }
        rewrite_sp_lits_all. rewrite -> ?USP in *.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
          lazymatch goal with ST3 : stk _ m' _ _, LI : u64arr _ m' _ _, L3 : length _ = 62%nat, LE : rw_cells _ m' (bv_unsigned sp + -616 + 496) _ |- _ =>
            eapply (J40 m'); [exact TXT | exact FRh | exact FRs | exact FR64 | exact LI | exact L3 | exact_at LE | exact_at PAD | exact_at DIG | exact_at SAV | exact_at ST3 | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM]
          end end.
      - cond_cleanup Hneg. assert (Hen : (0 <= e)%Z) by (rewrite ?signed_lit in Hneg by lia; Z.div_mod_to_equations; lia). clear Hneg.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose_sp_lits. pose proof (unsigned_lit (bv_unsigned sp + -688) ltac:(lia)) as USP.
        pose proof (unsigned_lit e ltac:(lia)) as UE.
        destruct (stk_split _ _ _ (bv_unsigned sp + -688 - 1296)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
        step. (* [comment removed for export] *)
        call positive_digit_comp_f_spec.
        { rewrite ?USP. exact_at SThi. }
        { rewrite ?USP. Z.div_mod_to_equations. lia. }
        { rewrite ?USP. lia. }
        { exact PR1. }
        { rewrite_sp_lits. exact_at LIMBS. }
        { exact L62. }
        { rewrite_sp_lits. exact_at LENC. }
        { exact Hlen. }
        { rewrite_sp_lits. Z.div_mod_to_equations. lia. }
        { exact NORM. }
        { rewrite UE. lia. }
        { rewrite UE. apply (cap_pos _ dg e); [lia | lia | lia | apply bval_nonneg | exact BVAL]. }
        { rewrite ?USP. rewrite_sp_lits. lia. }
        rewrite_sp_lits_all. rewrite -> ?USP, -> ?UE in *.
        step. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
          lazymatch goal with SThi' : stk _ m' (SP - 1296)%Z _, LI : u64arr _ m' _ _, L3 : length _ = 62%nat, LE : rw_cells _ m' (bv_unsigned sp + -616 + 496) _ |- _ =>
            pose proof (stk_merge _ _ _ _ _ STlo SThi' ltac:(lia)) as ST3;
            eapply (J40 m'); [exact TXT | exact FRh | exact FRs | exact FR64 | exact LI | exact L3 | exact_at LE | exact_at PAD | exact_at DIG | exact_at SAV | exact_at ST3 | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM]
          end end. }
    (* [comment removed for export] *)
    assert (Jb4 : forall (mv d : Z) (v11 v12 v13 v14 : word),
      (1 <= mv)%Z -> (0 <= d)%Z -> (mv * 10^d <= bv_unsigned w)%Z -> (mv < 100)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 mv) v11 v12 v13 v14 x15 x16 x17
                 (Z_to_bv 64 X) am (Z_to_bv 64 (bv_unsigned q + d)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28ba4) fc None m (seg_rom PSEGS))).
    { intros mv d v11 v12 v13 v14 Hmv1 Hd Hmvd Hmv2.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H10.
      - cond_cleanup H10. apply Jdc. split; [lia|]. eapply sci_T_bound; [exact Hmv1 | exact Hd | exact Hmvd | lia].
      - cond_cleanup H10.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite (unsigned_lit mv) by lia. rewrite (magic_div10 mv) by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases H99; [cond_cleanup H99; exfalso; lia|]. clear H99.
        goto (apply (Jdc (d + 1)%Z)).
        pose proof (pow10_step mv d 1 (bv_unsigned w) Hd ltac:(lia) ltac:(lia) Hmvd) as HS.
        change (10 ^ 1)%Z with 10%Z in HS.
        split; [lia|]. eapply (sci_T_bound (mv / 10)); [Z.div_mod_to_equations; lia | lia | exact HS | lia]. }
    (* [comment removed for export] *)
    assert (J7c : forall (mv d : Z) (v10 v11 v13 : word),
      (1 <= mv)%Z -> (0 <= d)%Z -> (mv * 10^d <= bv_unsigned w)%Z -> (mv < 10000)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 v10 v11 (Z_to_bv 64 mv) v13 x14 x15 x16 x17
                 (Z_to_bv 64 X) am (Z_to_bv 64 (bv_unsigned q + d)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28b6c) fc None m (seg_rom PSEGS))).
    { intros mv d v10 v11 v13 Hmv1 Hd Hmvd Hmv4.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H100.
      - cond_cleanup H100.
        step. (* [comment removed for export] *)
        apply (Jb4 mv d); assumption.
      - cond_cleanup H100.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite (unsigned_lit mv) by lia. rewrite (magic_div100 mv) by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases H624. { cond_cleanup H624. exfalso. rewrite Z.shiftr_div_pow2 in H624 by lia. Z.div_mod_to_equations. lia. }
        clear H624.
        step. (* [comment removed for export] *)
        goto (apply (Jb4 (mv / 100)%Z (d + 2)%Z)).
        + Z.div_mod_to_equations; lia.
        + lia.
        + pose proof (pow10_step mv d 2 (bv_unsigned w) Hd ltac:(lia) ltac:(lia) Hmvd) as HS.
          change (10 ^ 2)%Z with 100%Z in HS. exact HS.
        + Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    assert (L1 : forall (k : nat) (mv d : Z) (v13 : word),
      (mv < 10000 ^ Z.of_nat k)%Z -> (10000 <= mv)%Z -> (0 <= d)%Z -> (mv * 10^d <= bv_unsigned w)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 3777893186295716171) (Z_to_bv 64 99999999)
                 (Z_to_bv 64 mv) v13 x14 x15 x16 x17
                 (Z_to_bv 64 X) am (Z_to_bv 64 (bv_unsigned q + d)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28b58) fc None m (seg_rom PSEGS))).
    { induction k as [|k IH]; intros mv d v13 Hk Hmv4 Hd Hmvd.
      { exfalso. cbn in Hk. lia. }
      rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hk by lia.
      assert (Rmv : (mv < 2^64)%Z).
      { assert (0 < 10 ^ d)%Z by (apply Z.pow_pos_nonneg; lia). nia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit mv) by lia. rewrite (magic_div10000 mv) by lia.
      step. (* [comment removed for export] *)
      pose proof (pow10_step mv d 4 (bv_unsigned w) Hd ltac:(lia) ltac:(lia) Hmvd) as HS.
      change (10 ^ 4)%Z with 10000%Z in HS.
      step. (* [comment removed for export] *)
      if_cases Hbig.
      - cond_cleanup Hbig.
        goto (apply (IH (mv / 10000)%Z (d + 4)%Z)).
        + Z.div_mod_to_equations; nia.
        + Z.div_mod_to_equations; lia.
        + lia.
        + exact HS.
      - cond_cleanup Hbig.
        goto (apply (J7c (mv / 10000)%Z (d + 4)%Z)).
        + Z.div_mod_to_equations; lia.
        + lia.
        + exact HS.
        + Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hsmall.
    - cond_cleanup Hsmall. rewrite Z.shiftr_div_pow2 in Hsmall by lia.
      goto (apply (J7c (bv_unsigned w) 0%Z)).
      + lia. + lia. + change (10 ^ 0)%Z with 1%Z. lia. + Z.div_mod_to_equations; lia.
    - cond_cleanup Hsmall. rewrite Z.shiftr_div_pow2 in Hsmall by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      goto (apply (L1 5%nat (bv_unsigned w) 0%Z)).
      + change (10000 ^ Z.of_nat 5)%Z with (10^20)%Z. lia.
      + Z.div_mod_to_equations; lia.
      + lia.
      + change (10 ^ 0)%Z with 1%Z. lia.
  Qed.
End BLK.
