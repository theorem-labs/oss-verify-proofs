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

Module P_spd_commonT.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Export P_spd_common.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation PSEGS := Plain.M.loaded_segments.

Section CTX.
  Variable c : spd_ctx.
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
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

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
    /\ rw_cells PSEGS m V [C8 v]
    /\ pristine m 0x10000 0x22000
    /\ pristine m P_FMIN_D (P_FMIN_D + 4)
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
  Definition K_22d1c : Prop :=
    forall m (r : list byte) (j5 : list byte)
           (x1 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm : word) (ng k3 kI fp fL tm : Z),
      tinv (frameP q w lm ng tm j5 k3 kI fp fL [CB 520 r]) m -> pnsok ng k3 kI fp fL tm w ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) (Z_to_bv 64 1) w (Z_to_bv 64 tm) x14 x15 x16 x17
                 x18 x19 q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x24c0c) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_22ad4 : Prop :=
    forall m (r : list byte) (j5 : list byte)
           (x1 x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm : word) (ng k3 kI fp fL : Z),
      tinv (frameP q w lm ng 0 j5 k3 kI fp fL [C8 (Z_to_bv 64 0); CB 512 r]) m -> pnsok ng k3 kI fp fL 0 w ->
      (-22 <= bv_signed q)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) x11 w x13 x14 x15 x16 x17
                 x18 x19 q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x249c4) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_22d30 : Prop :=
    forall m (r : list byte) (j5 : list byte)
           (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm : word) (ng k3 kI fp fL tm tf : Z),
      tinv (frameP q w lm ng tm j5 k3 kI fp fL [C8 (Z_to_bv 64 0); CB 512 r]) m -> pnsok ng k3 kI fp fL tm w ->
      (tf = 0 \/ (tf = 1 /\ tm = 1))%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) (Z_to_bv 64 tf) w x13 x14 x15 x16 x17
                 x18 x19 q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x24c20) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_22ef4 : Prop :=
    forall m (r : list byte) (j5 : list byte)
           (x1 x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm am ap : word) (ng k3 kI fp fL : Z),
      tinv (frameP q w lm ng 1 j5 k3 kI fp fL [C8 (Z_to_bv 64 0); CB 512 r]) m -> pnsok ng k3 kI fp fL 1 w ->
      (bv_signed q < -342 -> am = Z_to_bv 64 0 /\ ap = Z_to_bv 64 0)%Z ->
      (308 < bv_signed q -> am = Z_to_bv 64 0 /\ ap = Z_to_bv 64 2047)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) x11 w x13 x14 x15 x16 x17
                 am ap q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x24de4) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_230e8 : Prop :=
    forall m (r : list byte) (j5 : list byte)
           (x1 x5 x6 x7 x9 x11 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm am ap bm bp : word) (ng k3 kI fp fL : Z),
      tinv (frameP q w lm ng 1 j5 k3 kI fp fL [C8 (Z_to_bv 64 0); CB 512 r]) m -> pnsok ng k3 kI fp fL 1 w ->
      ((am <> bm \/ ap <> bp) -> -342 <= bv_signed q <= 308)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 ng) x11 w bp bm x15 x16 x17
                 am ap q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x24fd8) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_23210 : Prop :=
    forall m (r : list byte) (j5 : list byte)
           (x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (w q lm am ap : word) (ng k3 kI fp fL px : Z),
      tinv (frameP q w lm ng 1 j5 k3 kI fp fL [C8 (Z_to_bv 64 0); CB 512 r]) m -> pnsok ng k3 kI fp fL 1 w ->
      (-342 <= bv_signed q <= 308)%Z ->
      (bv_unsigned ap = px mod 2 ^ 32)%Z -> (-33100 <= px <= -30600)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 x10 x11 w x13 x14 x15 x16 x17
                 am ap q x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25100) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_23318 : Prop :=
    forall m (cells : list cell)
           (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      bytes_at PSEGS m P bs ->
      rw_cells PSEGS m SP cells -> Z.of_nat (cells_size cells) = 584%Z ->
      rw_cells PSEGS m (SP + 584)%Z savesC ->
      stk PSEGS m (bv_unsigned sp - NEED) SP ->
      rw_cells PSEGS m V [C8 v] ->
      pristine m 0x10000 0x22000 -> pristine m P_FMIN_D (P_FMIN_D + 4) ->
      munch W m0 m -> wmono PSEGS m0 m ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25208) fc None m (seg_rom PSEGS)).

  (* [comment removed for export] *)
  Definition K_23350 : Prop :=
    forall m (cells : list cell) (F' : bvmap 5 word) (fc' : bv 32) (v' : word)
           (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
      frm0 fc' ->
      rw_cells PSEGS m SP cells -> Z.of_nat (cells_size cells) = 584%Z ->
      rw_cells PSEGS m (SP + 584)%Z savesC ->
      stk PSEGS m (bv_unsigned sp - NEED) SP ->
      rw_cells PSEGS m V [C8 v'] ->
      munch W m0 m -> wmono PSEGS m0 m ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F' (Z_to_bv 64 0x25240) fc' None m (seg_rom PSEGS)).

End CTX.
End P_spd_commonT.

From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_spd_tbl P_memset_stmt P_parse_mantissa_stmt P_positive_digit_comp_d_stmt P_negative_digit_comp_d_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_DC.P_spd_commonT OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_spd_tbl OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memset_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_parse_mantissa_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_positive_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_negative_digit_comp_d_stmt.
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

#[using="Type"] Lemma dc_p2 : forall (ap : word) (px : Z), bv_unsigned ap = px mod 2^32 ->
  bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned ap + 32768))) 4294967295)) = (px + 32768) mod 2^32.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ap px Hap. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia.
  rewrite !unsigned_lit_wrap. rewrite Hap.
  pose proof (Z.mod_pos_bound px (2^32) ltac:(lia)).
  rewrite (Z.mod_small _ (2^64)) by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small _ (2^64)) by (Z.div_mod_to_equations; lia).
  Z.div_mod_to_equations. lia.
Qed.
End ZLEMMAS.

Section BLK.
  Variable c : spd_ctx.
  Hypothesis PRE : spd_pre c.
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
  #[local] Notation NEED := slow_path_double_need.
  #[local] Notation POST := (slow_path_double_post (r_ra c) (r_sp c) (r_gp c) (r_tp c) (r_s0 c) (r_s1 c)
                               (r_s2 c) (r_s3 c) (r_s4 c) (r_s5 c) (r_s6 c) (r_s7 c) (r_s8 c) (r_s9 c)
                               (r_s10 c) (r_s11 c) (bv_unsigned (r_a2 c)) (r_m0 c)).
  #[local] Notation W := (slow_path_double_W (bv_unsigned (r_sp c)) (bv_unsigned (r_a2 c))).

  (* [comment removed for export] *)
  #[local] Ltac pre_facts :=
    pose proof (pre_LEN c PRE) as LEN; pose proof (pre_RANGE c PRE) as RANGE;
    pose proof (pre_ENW c PRE) as ENW; pose proof (pre_VAL8 c PRE) as VAL4;
    pose proof (pre_AL c PRE) as AL; pose proof (pre_LO c PRE) as LO;
    pose proof (pre_P0 c PRE) as P0; pose proof (pre_V0 c PRE) as V0;
    pose proof (pre_FRM c PRE) as FRM;
    pose proof (pre_SEP1 c PRE) as SEP1; unfold slow_path_double_need in SEP1; pose proof (pre_SEP2 c PRE) as SEP2; pose proof (pre_SEP3 c PRE) as SEP3;
    unfold slow_path_double_need in LO, SEP1, SEP2;
    pose proof (bv_unsigned_in_range 64 (r_sp c)) as Rsp; unfold bv_modulus in Rsp;
    pose proof (bv_unsigned_in_range 64 (r_a0 c)) as Ra0; unfold bv_modulus in Ra0;
    pose proof (bv_unsigned_in_range 64 (r_a1 c)) as Ra1; unfold bv_modulus in Ra1;
    pose proof (bv_unsigned_in_range 64 (r_a2 c)) as Ra2; unfold bv_modulus in Ra2.

  (* [comment removed for export] *)
  #[local] Ltac open_pinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv beta delta [slow_path_double_W slow_path_double_need] in MU;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.

  (* [comment removed for export] *)
  #[local] Ltac open_tinv H :=
    destruct H as (TXT & FR & ST & VAL & PR1 & PR2 & MU & WM);
    unfold slow_path_double_need in ST; unfold P_FMIN_D in PR2;
    cbv delta [slow_path_double_W slow_path_double_need] in MU;
    cbn [frameP savesC app] in FR;
    pose proof (bytes_at_bound _ _ _ _ TXT) as Btxt.
  #[local] Ltac open_pnsok H :=
    destruct H as (Hng & Hk3 & HkI & HfL & Hfp & Htm & Hw).

  (* [comment removed for export] *)
  #[local] Ltac gen_val e := let X := fresh "rv" in set (X := e) in *; clearbody X.
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

  Hypothesis memset_spec : memset_stmt.
  Hypothesis parse_mantissa_spec : parse_mantissa_stmt.
  Hypothesis positive_digit_comp_d_spec : positive_digit_comp_d_stmt.
  Hypothesis negative_digit_comp_d_spec : negative_digit_comp_d_stmt.
  Hypothesis C_23318 : K_23318 c.

  (* [comment removed for export] *)
  #[using="PRE memset_spec parse_mantissa_spec positive_digit_comp_d_spec negative_digit_comp_d_spec C_23318"] Lemma spd_DC : K_23210 c.
  Proof. LiaFast.lf_pins (fun (PRE memset_spec parse_mantissa_spec positive_digit_comp_d_spec negative_digit_comp_d_spec C_23318 : LiaFast.U) => LiaFast.u0).
    unfold K_23318 in C_23318.
    unfold K_23210. intros m r j5 x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      w q lm am ap ng k3 kI fp fL px TI PN Hq Hap Hpx.
    pre_facts. pose proof (pre_L40 c PRE) as L40. 
    pose proof TI as TI'. open_tinv TI'. pose proof PN as PN'. open_pnsok PN'.
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    pose proof (zb_signed q) as SQ. specialize (Hw eq_refl).
    (* [comment removed for export] *)
    assert (Ja0 : forall (T : Z) (v10 v11 v12 v13 v14 : word), (0 <= T <= 19)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 v10 v11 v12 v13 v14 x15 x16 x17
                 am ap (Z_to_bv 64 (bv_unsigned q + T)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25190) fc None m (seg_rom PSEGS))).
    { intros T v10 v11 v12 v13 v14 HT.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
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
      { rewrite_sp_lits. exact OLD. }
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
      replace (bv_unsigned sp + -688 + 72 + Z.of_nat (8 * 62))%Z with (bv_unsigned sp + -688 + 72 + 496)%Z in LENC by lia.
      pose proof (rw_cells_of_u8arr PSEGS _ _ _ Z6) as PAD. clear Z6. rewrite repeat_length in PAD.
      replace (bv_unsigned sp + -688 + 72 + Z.of_nat (8 * 62) + Z.of_nat 2)%Z with (bv_unsigned sp + -118)%Z in PAD by lia.
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
      change (Z.of_nat (8 * 62)) with 496%Z in LENC, PAD. change (Z.of_nat 2) with 2%Z in PAD.
      replace (bv_unsigned sp + -616 + 496 + 2)%Z with (bv_unsigned sp + -118)%Z in PAD by lia.
      replace (bv_unsigned sp + -656)%Z with (bv_unsigned sp + -688 + 32)%Z in FRs by lia.
      do 4 step. (* [comment removed for export] *)
      pose_sp_lits.
      pose proof (unsigned_lit (bv_unsigned sp + -688) ltac:(lia)) as USP.
      pose proof (unsigned_lit 769 ltac:(lia)) as U769.
      destruct (stk_split _ _ _ (bv_unsigned sp + -688 - 144)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
      assert (LL : length (repeat (Z_to_bv 64 0) 62) = 62%nat) by apply repeat_length.
      step. (* [comment removed for export] *)
      call parse_mantissa_spec.
      { rewrite USP. exact SThi. }
      { rewrite USP. Z.div_mod_to_equations. lia. }
      { exact PR1. }
      { rewrite_sp_lits. exact LIMBS. }
      { exact LL. }
      { rewrite_sp_lits. exact LENC. }
      { rewrite_sp_lits. Z.div_mod_to_equations. lia. }
      { rewrite USP. exact FRs. }
      { exact TXi. }
      { rewrite unsigned_lit by lia. lia. }
      { rewrite unsigned_lit by lia. lia. }
      { lia. }
      { exact TXf. }
      { destruct Hfp as [[Hfp1 Hfp2]|[Hfp1 Hfp2]]; rewrite Hfp1, ?unsigned_lit by lia; lia. }
      { lia. }
      { intros Hz. destruct Hfp as [[Hfp1 Hfp2]|[Hfp1 Hfp2]]; [| rewrite Hfp1, unsigned_lit in Hz by lia; exfalso; lia].
        apply (f_equal Z.to_nat) in Lfbs. rewrite Nat2Z.id in Lfbs. rewrite Lfbs, Hfp2. reflexivity. }
      { rewrite U769. lia. }
      { rewrite_sp_lits. exact DIG. }
      { rewrite USP. lia. }
      { rewrite USP. lia. }
      { rewrite USP. rewrite_sp_lits. lia. }
      { rewrite_sp_lits. lia. }
      { rewrite_sp_lits. rewrite unsigned_lit by lia. lia. }
      { rewrite_sp_lits. intros Hz. destruct Hfp as [[Hfp1 Hfp2]|[Hfp1 Hfp2]]; rewrite Hfp1, ?unsigned_lit in * by lia; lia. }
      rewrite_sp_lits_all. rewrite -> ?USP, -> ?U769 in *.
      clear LL U504 U769. try clear H.
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
      assert (He : (-1111 <= e <= 328)%Z) by (subst e; lia).
      assert (Hedg : (0 <= e -> e + dg <= 329)%Z) by (subst e; lia).
      clearbody e.
      (* [comment removed for export] *)
      assert (J08 : forall (m3 : word -> option byte) (ws3 : list word) (len3 : Z)
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
        rw_cells PSEGS m3 V [C8 v] ->
        pristine m3 65536 139264 -> pristine m3 413152 (413152 + 4) ->
        munch [((bv_unsigned sp - (688 + 1808))%Z, bv_unsigned sp); (V, (V + 8)%Z)] m0 m3 ->
        wmono PSEGS m0 m3 ->
        evt PSEGS POST
          (MS (mkR v1 (Z_to_bv 64 SP) gp tp v5 v6 v7 a2 x9 v10 v11 v12 v13 v14 v15 v16 v17
                   am ap (Z_to_bv 64 (bv_unsigned q + T)) (Z_to_bv 64 4294967295) x22 x23 x24 x25 x26 x27 v28 v29 v30 v31)
              F (Z_to_bv 64 0x251f8) fc None m3 (seg_rom PSEGS))).
      { intros m3 ws3 len3 v1 v5 v6 v7 y10 y11 y12 y13 y14 y15 y16 y17 v28 v29 v30 v31
               TXT3 FRh3 FRs3 FR643 LIMBS3 L3 LENC3 PAD3 DIG3 SAV3 ST3 VAL3 PR13 PR23 MU3 WM3.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose proof (rw_cells_of_u64arr PSEGS _ _ _ LIMBS3) as OBJ. rewrite L3 in OBJ. clear LIMBS3.
        chunk_join FRh3 FRs3 FRa. chunk_join FRa FR643 FRb. chunk_join FRb OBJ FRd.
        chunk_join FRd LENC3 FRe. chunk_join FRe PAD3 FRf. chunk_join FRf DIG3 FRg.
        eapply C_23318; [exact TXT3 | exact FRg | reflexivity | | exact ST3 | exact VAL3 | exact PR13 | exact PR23 | exact MU3 | exact WM3].
        replace (SP + 584)%Z with (bv_unsigned sp + -104)%Z by lia. exact SAV3. }
      step. (* [comment removed for export] *)
      if_cases Hneg.
      - cond_cleanup Hneg. assert (Hen : (e < 0)%Z) by (Z.div_mod_to_equations; lia). clear Hneg.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose_sp_lits. pose proof (unsigned_lit (bv_unsigned sp + -688) ltac:(lia)) as USP.
        pose proof (dc_p2 ap px Hap) as HP2.
        step. (* [comment removed for export] *)
        call negative_digit_comp_d_spec.
        { rewrite USP. replace (bv_unsigned sp + -688 - 1808)%Z with (bv_unsigned sp - (688 + 1808))%Z by lia. exact ST. }
        { rewrite USP. Z.div_mod_to_equations. lia. }
        { rewrite USP. lia. }
        { exact PR1. }
        { rewrite_sp_lits. exact LIMBS. }
        { exact L62. }
        { rewrite_sp_lits. exact LENC. }
        { exact Hlen. }
        { rewrite_sp_lits. Z.div_mod_to_equations. lia. }
        { exact NORM. }
        { exact HP2. }
        { lia. }
        { reflexivity. }
        { lia. }
        { rewrite USP. rewrite_sp_lits. lia. }
        rewrite_sp_lits_all. rewrite -> ?USP in *.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
          lazymatch goal with ST3 : stk _ m' _ _, LI : u64arr _ m' _ _, L3 : length _ = 62%nat, LE : rw_cells _ m' (bv_unsigned sp + -616 + 496) _ |- _ =>
            eapply (J08 m'); [exact TXT | exact FRh | exact FRs | exact FR64 | exact LI | exact L3 | exact LE | exact PAD | exact DIG | exact SAV | | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM];
            replace (bv_unsigned sp - (688 + 1808))%Z with (SP - 1808)%Z by lia; exact ST3
          end end.
      - cond_cleanup Hneg. assert (Hen : (0 <= e)%Z) by (Z.div_mod_to_equations; lia). clear Hneg.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        pose_sp_lits. pose proof (unsigned_lit (bv_unsigned sp + -688) ltac:(lia)) as USP.
        pose proof (unsigned_lit e ltac:(lia)) as UE.
        destruct (stk_split _ _ _ (bv_unsigned sp + -688 - 1296)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
        step. (* [comment removed for export] *)
        call positive_digit_comp_d_spec.
        { rewrite USP. exact SThi. }
        { rewrite USP. Z.div_mod_to_equations. lia. }
        { rewrite USP. lia. }
        { exact PR1. }
        { rewrite_sp_lits. exact LIMBS. }
        { exact L62. }
        { rewrite_sp_lits. exact LENC. }
        { exact Hlen. }
        { rewrite_sp_lits. Z.div_mod_to_equations. lia. }
        { exact NORM. }
        { rewrite UE. lia. }
        { rewrite UE. apply (cap_pos _ dg e); [lia | lia | lia | apply bval_nonneg | exact BVAL]. }
        { rewrite USP. rewrite_sp_lits. lia. }
        rewrite_sp_lits_all. rewrite -> ?USP, -> ?UE in *.
        step. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
          lazymatch goal with SThi' : stk _ m' (SP - 1296)%Z _, LI : u64arr _ m' _ _, L3 : length _ = 62%nat, LE : rw_cells _ m' (bv_unsigned sp + -616 + 496) _ |- _ =>
            pose proof (stk_merge _ _ _ _ _ STlo SThi' ltac:(lia)) as ST3;
            eapply (J08 m'); [exact TXT | exact FRh | exact FRs | exact FR64 | exact LI | exact L3 | exact LE | exact PAD | exact DIG | exact SAV | exact ST3 | exact VAL | exact PR1 | exact PR2 | exact MU | exact WM]
          end end. }
    (* [comment removed for export] *)
    assert (J78 : forall (mv d : Z) (v11 v12 v13 v14 : word),
      (1 <= mv)%Z -> (0 <= d)%Z -> (mv * 10^d <= bv_unsigned w)%Z -> (mv < 100)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 (Z_to_bv 64 mv) v11 v12 v13 v14 x15 x16 x17
                 am ap (Z_to_bv 64 (bv_unsigned q + d)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25168) fc None m (seg_rom PSEGS))).
    { intros mv d v11 v12 v13 v14 Hmv1 Hd Hmvd Hmv2.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H10.
      - cond_cleanup H10. apply Ja0. split; [lia|]. eapply sci_T_bound; [exact Hmv1 | exact Hd | exact Hmvd | lia].
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
        goto (apply (Ja0 (d + 1)%Z)).
        pose proof (pow10_step mv d 1 (bv_unsigned w) Hd ltac:(lia) ltac:(lia) Hmvd) as HS.
        change (10 ^ 1)%Z with 10%Z in HS.
        split; [lia|]. eapply (sci_T_bound (mv / 10)); [Z.div_mod_to_equations; lia | lia | exact HS | lia]. }
    (* [comment removed for export] *)
    assert (J40 : forall (mv d : Z) (v10 v11 v13 : word),
      (1 <= mv)%Z -> (0 <= d)%Z -> (mv * 10^d <= bv_unsigned w)%Z -> (mv < 10000)%Z ->
      evt PSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 a2 x9 v10 v11 (Z_to_bv 64 mv) v13 x14 x15 x16 x17
                 am ap (Z_to_bv 64 (bv_unsigned q + d)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x25130) fc None m (seg_rom PSEGS))).
    { intros mv d v10 v11 v13 Hmv1 Hd Hmvd Hmv4.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases H100.
      - cond_cleanup H100.
        step. (* [comment removed for export] *)
        apply (J78 mv d); assumption.
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
        goto (apply (J78 (mv / 100)%Z (d + 2)%Z)).
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
                 am ap (Z_to_bv 64 (bv_unsigned q + d)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2511c) fc None m (seg_rom PSEGS))).
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
        goto (apply (J40 (mv / 10000)%Z (d + 4)%Z)).
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
      goto (apply (J40 (bv_unsigned w) 0%Z)).
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
