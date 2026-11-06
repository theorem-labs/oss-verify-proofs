(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 267 of its 288 lines of code are new or changed and 123 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img codec_agree
  codec_main_inv codec_main_oweb_lib LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(** ---- the led loop (0x145fc-0x14654) ---- *)

Lemma pow_sllw : forall x, 0 <= x <= 6 -> bv_swrap 32 (1 ≪ (x mod 32)) mod 18446744073709551616 = 2 ^ x.
Proof.
  intros x Hx. assert (E : x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6) by lia.
  repeat (destruct E as [-> | E]; [vm_compute; reflexivity |]). subst x. vm_compute. reflexivity.
Qed.

Lemma ring_bit : forall b j, 0 <= b < 2 ^ 32 -> 1 <= j <= 14 ->
  Z.land (bv_swrap 32 (bv_wrap 32 b ≫ (j mod 32)) mod 18446744073709551616) 1 = if Z.testbit b j then 1 else 0.
Proof.
  intros b j Hb Hj.
  rewrite (Z.mod_small j 32) by lia.
  unfold bv_wrap at 1. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  rewrite (Z.mod_small b (2 ^ 32)) by lia.
  assert (Hs : 0 <= b ≫ j < 2 ^ 31).
  { rewrite Z.shiftr_div_pow2 by lia.
    assert (2 <= 2 ^ j) by (change 2 with (2 ^ 1); apply Z.pow_le_mono_r; lia).
    split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. nia. }
  unfold bv_swrap, bv_wrap. replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  rewrite (Z.mod_small (b ≫ j + 2 ^ 31) (2 ^ 32)) by lia.
  replace (b ≫ j + 2 ^ 31 - 2 ^ 31) with (b ≫ j) by lia.
  rewrite (Z.mod_small (b ≫ j)) by lia.
  replace (Z.testbit b j) with (Z.testbit (b ≫ j) 0) by (rewrite Z.shiftr_spec by lia; f_equal; lia).
  change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. rewrite Z.pow_1_r.
  rewrite Zmod_odd, Z.bit0_odd. reflexivity.
Qed.

Lemma swrap_small : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap. replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity. rewrite Z.mod_small by lia. lia.
Qed.

Lemma swrap_neg : forall led, 2 <= led <= 15 -> bv_swrap 32 (- led mod 18446744073709551616 + -1) = - (led + 1).
Proof.
  intros led Hl. unfold bv_swrap, bv_wrap. replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  change (2 ^ 31) with 2147483648. change (2 ^ 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Ltac ring_tail K led :=
  zstep; zstep; zstep;
  rewrite (swrap_small (led + 1)) by lia;
  rewrite (swrap_neg led) by lia;
  zstep;
  let E3 := fresh "E3" in
  if_cases E3;
  [ zify_cond E3;
    let L15 := fresh "L15" in
    assert (L15 : led <> 15) by (intro; subst led; apply E3; reflexivity);
    rewrite (proj2 (Z.eqb_neq led 15) L15) in K; apply K
  | zify_cond E3;
    let L15 := fresh "L15" in
    assert (L15 : led = 15) by (Z.div_mod_to_equations; lia);
    subst led; apply K ].

Lemma ring_iter : forall (Q : machine_state -> Prop) F fc m
    ra sp gp tp t2 s0 s1 a0 a4 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (b led p1 p2 : Z) t0 t1 a7,
  0 <= b < 2 ^ 32 -> 2 <= led <= 15 -> 0 <= p1 < 128 -> 0 <= p2 < 128 ->
  (forall t0' t1' a7',
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0
                     (Z_to_bv 64 (snd (owe_ring_step b (p1, p2) led)))
                     (Z_to_bv 64 (fst (owe_ring_step b (p1, p2) led)))
                     (Z_to_bv 64 b) a4 (Z_to_bv 64 (led + 1)) (Z_to_bv 64 (- (led + 1))) a7'
                     (Z_to_bv 64 9) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if led =? 15 then 0x14658 else 0x145fc)) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 p2) (Z_to_bv 64 p1) (Z_to_bv 64 b) a4
                   (Z_to_bv 64 led) (Z_to_bv 64 (- led)) a7 (Z_to_bv 64 9) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x145fc) fc None m (seg_rom rsegs)).
Proof.
  intros Q F fc m ra sp gp tp t2 s0 s1 a0 a4 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 b led p1 p2 t0 t1 a7
         Hb Hl Hp1 Hp2 K.
  zstep. zstep. zstep. zstep.
  if_cases E1.
  - zify_cond E1. rewrite (ring_bit b (led + -1)) in E1 by lia.
    assert (Tb : Z.testbit b (led - 1) = false)
      by (replace (led - 1) with (led + -1) by lia; destruct (Z.testbit b (led + -1)); [discriminate | reflexivity]).
    assert (Es : owe_ring_step b (p1, p2) led = (p1, p2))
      by (unfold owe_ring_step; cbn [fst snd]; rewrite Tb; cbn [bit_or_0]; rewrite !Z.lor_0_r;
          destruct (led <=? 8); reflexivity).
    rewrite Es in K. cbn [fst snd] in K.
    ring_tail K led.
  - zify_cond E1. rewrite (ring_bit b (led + -1)) in E1 by lia.
    assert (Tb : Z.testbit b (led - 1) = true)
      by (replace (led - 1) with (led + -1) by lia; destruct (Z.testbit b (led + -1)); [reflexivity | contradiction]).
    zstep. if_cases E2; pose proof E2 as E2b.
    + zify_cond E2. zstep. zstep. zstep. rewrite E2b; cbv iota. zstep. zstep. zstep. zstep. zstep.
      rewrite E2b; cbv iota. zstep.
      rewrite (pow_sllw (8 + - led)) by lia. try rewrite (Z.mod_small p1 18446744073709551616) by lia.
      assert (Es : owe_ring_step b (p1, p2) led = (Z.lor p1 (2 ^ (8 + - led)), p2))
        by (unfold owe_ring_step; cbn [fst snd]; rewrite Tb; cbn [bit_or_0];
            replace (led <=? 8) with true by (symmetry; apply Z.leb_le; lia);
            do 3 f_equal; lia).
      rewrite Es in K. cbn [fst snd] in K.
      ring_tail K led.
    + zify_cond E2. zstep. zstep. zstep. zstep. rewrite E2b; cbv iota. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite E2b; cbv iota. zstep. zstep.
      rewrite (pow_sllw (15 + - led)) by lia. try rewrite (Z.mod_small p2 18446744073709551616) by lia.
      assert (Es : owe_ring_step b (p1, p2) led = (p1, Z.lor p2 (2 ^ (15 + - led))))
        by (unfold owe_ring_step; cbn [fst snd]; rewrite Tb; cbn [bit_or_0];
            replace (led <=? 8) with false by (symmetry; apply Z.leb_gt; lia);
            do 3 f_equal; lia).
      rewrite Es in K. cbn [fst snd] in K.
      ring_tail K led.
Qed.

Lemma ring_acc_range : forall b l p, Forall (fun x => 2 <= x <= 15) l ->
  0 <= fst p < 128 -> 0 <= snd p < 128 ->
  0 <= fst (fold_left (owe_ring_step b) l p) < 128 /\ 0 <= snd (fold_left (owe_ring_step b) l p) < 128.
Proof.
  intros b l p Hl H1 H2.
  apply (fold_left_inv (fun pr => 0 <= fst pr < 128 /\ 0 <= snd pr < 128)); [split; assumption|].
  intros [x1 x2] y Hy [Hx1 Hx2]. rewrite Forall_forall in Hl. specialize (Hl y Hy).
  cbn [fst snd] in *. unfold owe_ring_step. cbn [fst snd].
  assert (B : forall t k, 0 <= k <= 6 -> 0 <= bit_or_0 t (2 ^ k) < 128).
  { intros [|] k Hk; cbn [bit_or_0]; [|lia].
    split; [apply Z.pow_nonneg; lia|]. change 128 with (2 ^ 7). apply Z.pow_lt_mono_r; lia. }
  destruct (Z.leb_spec y 8).
  - split; [|exact Hx2]. change 128 with (2 ^ 7). apply lor_lt_pow2; [exact Hx1 | apply B; lia].
  - split; [exact Hx1|]. change 128 with (2 ^ 7). apply lor_lt_pow2; [exact Hx2 | apply B; lia].
Qed.

Lemma seq_leds : forall n, (n <= 14)%nat -> Forall (fun x => 2 <= x <= 15) (map Z.of_nat (seq 2 n)).
Proof.
  intros n Hn. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (y & <- & Hy).
  apply in_seq in Hy. lia.
Qed.

Lemma ring_loop : forall (Q : machine_state -> Prop) F fc m
    ra sp gp tp t2 s0 s1 a0 a4 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (b : Z),
  0 <= b < 2 ^ 32 ->
  (forall t0' t1' a5' a6' a7',
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0
                     (Z_to_bv 64 (snd (owe_ring b))) (Z_to_bv 64 (fst (owe_ring b)))
                     (Z_to_bv 64 b) a4 a5' a6' a7'
                     (Z_to_bv 64 9) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14658) fc None m (seg_rom rsegs))) ->
  forall t0 t1 a7,
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 b) a4
                   (Z_to_bv 64 2) (Z_to_bv 64 (-2)) a7 (Z_to_bv 64 9) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x145fc) fc None m (seg_rom rsegs)).
Proof.
  intros Q F fc m ra sp gp tp t2 s0 s1 a0 a4 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 b Hb K.
  assert (G : forall r, (r <= 13)%nat -> forall t0 t1 a7,
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0
                     (Z_to_bv 64 (snd (fold_left (owe_ring_step b) (map Z.of_nat (seq 2 (13 - r))) (0, 0))))
                     (Z_to_bv 64 (fst (fold_left (owe_ring_step b) (map Z.of_nat (seq 2 (13 - r))) (0, 0))))
                     (Z_to_bv 64 b) a4
                     (Z_to_bv 64 (2 + Z.of_nat (13 - r))) (Z_to_bv 64 (- (2 + Z.of_nat (13 - r)))) a7
                     (Z_to_bv 64 9) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x145fc) fc None m (seg_rom rsegs))).
  { induction r as [|r IH]; intros Hr t0 t1 a7.
    - pose proof (ring_acc_range b (map Z.of_nat (seq 2 (13 - 0))) (0, 0) (seq_leds (13 - 0) ltac:(lia))
                    ltac:(cbn; lia) ltac:(cbn; lia)) as RA.
      destruct (fold_left (owe_ring_step b) (map Z.of_nat (seq 2 (13 - 0))) (0, 0)) as [p1 p2] eqn:EP.
      cbn [fst snd] in *.
      apply ring_iter; [exact Hb | cbn; lia | lia | lia |].
      intros t0' t1' a7'.
      replace (2 + Z.of_nat (13 - 0) =? 15) with true by reflexivity.
      replace (2 + Z.of_nat (13 - 0) + 1) with 16 by reflexivity.
      replace (owe_ring_step b (p1, p2) (2 + Z.of_nat (13 - 0))) with (owe_ring b).
      + apply K.
      + rewrite owe_ring_step_eq. rewrite <- EP.
        change (seq 2 14) with (seq 2 13 ++ [15]%nat). rewrite map_app, fold_left_app. reflexivity.
    - pose proof (ring_acc_range b (map Z.of_nat (seq 2 (13 - S r))) (0, 0) (seq_leds (13 - S r) ltac:(lia))
                    ltac:(cbn; lia) ltac:(cbn; lia)) as RA.
      destruct (fold_left (owe_ring_step b) (map Z.of_nat (seq 2 (13 - S r))) (0, 0)) as [p1 p2] eqn:EP.
      cbn [fst snd] in *.
      apply ring_iter; [exact Hb | lia | lia | lia |].
      intros t0' t1' a7'.
      replace (2 + Z.of_nat (13 - S r) =? 15) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (2 + Z.of_nat (13 - S r) + 1) with (2 + Z.of_nat (13 - r)) by lia.
      replace (owe_ring_step b (p1, p2) (2 + Z.of_nat (13 - S r)))
        with (fold_left (owe_ring_step b) (map Z.of_nat (seq 2 (13 - r))) (0, 0)).
      + apply IH. lia.
      + rewrite <- EP. replace (13 - r)%nat with (S (13 - S r)) by lia.
        rewrite seq_S, map_app, fold_left_app. cbn [map fold_left]. f_equal. lia. }
  intros t0 t1 a7. exact (G 13%nat ltac:(lia) t0 t1 a7).
Qed.

(** andi a3, a4, 0x40 on a4 = b << 6: bit 0 of b in bit 6. *)
Lemma land_shl6 : forall b, 0 <= b < 2 ^ 32 ->
  Z.land (b ≪ 6 mod 18446744073709551616) 64 = bit_or_0 (Z.testbit b 0) 64.
Proof.
  intros b Hb. rewrite Z.mod_small.
  2: { rewrite Z.shiftl_mul_pow2 by lia. lia. }
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec. change 64 with (2 ^ 6). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 6 n) as [<- | Hne].
  - rewrite andb_true_r. rewrite Z.shiftl_spec by lia. replace (6 - 6) with 0 by lia.
    destruct (Z.testbit b 0); cbn [bit_or_0]; [rewrite Z.pow2_bits_eqb by lia; reflexivity | rewrite Z.bits_0; reflexivity].
  - rewrite andb_false_r. destruct (Z.testbit b 0); cbn [bit_or_0];
      [rewrite Z.pow2_bits_eqb by lia; symmetry; apply Z.eqb_neq; exact Hne | rewrite Z.bits_0; reflexivity].
Qed.

Lemma codec_main_owe5 : S_owe5.
Proof.
  unfold S_owe5, owe_ok, st, body_regs.
  intros e fuel HE CHK ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' t3' t4' t5' t6' ops k od c rem tl m1
         HF HRC HK HOD HRCk HWR HWL HWK HWD HC FR HFR.
  replace (owe_pc 5) with 0x145d4 by reflexivity.
  pose proof HRC as (_ & HPD & HRD & _ & _).
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _ & _ & HPB & _ & HDJ). unfold LLVM_CODEC_STACK in HLO.
  pose proof HFR as (SV & ST & MU & WM & HMI). unfold LLVM_CODEC_STACK in MU.
  pose proof ST as [Hlo0 _].
  pose proof (relro_of_fr e m1 HE HFR) as HRI.
  pose proof HRD as (Ra & Rb & Rc & Rdl & Rlen & Rby & Rn & Rb16 & _ & _). specialize (Rb16 HK).
  destruct od as [d|]; [| exfalso; destruct (HOD eq_refl) as [X | [X | X]]; discriminate X].
  destruct (desk_ro m1 (k_p k) (k_desk k) d HRI HPD) as (Hd & Dr & Hdv & np & pad & DK).
  pose proof Dr as (Ddev & Dstr & Dch & Dctr).
  unfold desk_cells in DK.
  unfold disj, RELRO_BASE, RELRO_LEN in HDJ.
  unfold body_cells in FR. cbn [kcall_cells app] in FR.
  zstep. zstep. cbv beta. rewrite (u8_unsigned (d_strips d)) by lia. zstep.
  if_cases E1.
  - (* a >= strips *)
    zify_cond E1.
    assert (Has : d_strips d <= k_a k) by (rewrite sx32_u in E1 by lia; destruct (Z.ltb_spec (k_a k) (2 ^ 31)); lia).
    zstep.
    assert (FB : rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl)) by exact FR.
    eapply (owe_err_tail e fuel HE CHK) with (rc := E_RANGE);
      [ exact HF | exact HRC | exact HRCk | | | | exact HWL | exact HWK | exact HWD | exact HC | exact FB | exact HFR ].
    + unfold owe_k, owe_spec. rewrite HK. cbv beta iota zeta. cbn [Z.eqb Pos.eqb orb negb].
      replace (d_strips d <=? k_a k) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    + unfold E_RANGE. lia.
    + first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
  - zify_cond E1.
    assert (Has : k_a k < d_strips d) by (rewrite sx32_u in E1 by lia; destruct (Z.ltb_spec (k_a k) (2 ^ 31)); lia).
    rewrite (sx32_small (k_a k)) by lia.
    zstep. rewrite zx32_small by lia. zstep. zstep.
    if_cases E2.
    + (* b >> 15 != 0 *)
      zify_cond E2.
      zstep.
      assert (FB : rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl)) by exact FR.
      eapply (owe_err_tail e fuel HE CHK) with (rc := E_RANGE);
        [ exact HF | exact HRC | exact HRCk | | | | exact HWL | exact HWK | exact HWD | exact HC | exact FB | exact HFR ].
      * unfold owe_k, owe_spec. rewrite HK. cbv beta iota zeta. cbn [Z.eqb Pos.eqb orb negb].
        replace (Z.shiftr (k_b k) 15 =? 0) with false by (symmetry; apply Z.eqb_neq; exact E2).
        rewrite orb_true_r. reflexivity.
      * unfold E_RANGE. lia.
      * first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
    + zify_cond E2. rewrite E2.
      zstep. zstep. zstep. zstep.
      eapply ring_loop; [ lia | ].
      intros t0x t1x a5x a6x a7x.
      pose proof (owe_ring_range (k_b k)) as RR.
      destruct (owe_ring (k_b k)) as [p1 p2] eqn:ER. cbn [fst snd] in *.
      zstep. zstep. cbv beta. rewrite (u8_unsigned (d_dev d)) by lia.
      do 20 zstep.
      match goal with H : rw_cells rsegs ?mm (bv_unsigned (e_sp e) + -400) _ |- _ =>
        pose proof (rw_cells_merge_at mm _ _ 16 8 H) as FM; clear H end.
      cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in FM.
      rewrite HWR in FM.
      replace (Z.lor (k_a k mod 65536) 196608) with (KEY 3 (k_a k)) in FM
        by (unfold KEY; rewrite Z.lor_comm; change 0xffff with (Z.ones 16); rewrite Z.land_ones by lia; reflexivity).
      match type of FM with context [CB 24 ?W :: C8 (Z_to_bv 64 8) :: _] => set (Wv := W) in FM end.
      set (BS := fst (owe_sx (d_dev d) 0x00 [u8 (Z.lor (k_a k) (bit_or_0 (Z.testbit (k_b k) 0) 0x40)); p1; p2])).
      assert (FR' : rw_cells rsegs m0 (bv_unsigned (e_sp e) + -400)
                      (body_cells e (set_owe k 0 Wv (Z.of_nat (length BS)) (KEY 3 (k_a k)) 0) c rem tl))
        by exact FM.
      eapply (owe_ok_tail e fuel CHK) with (bs := BS) (key := KEY 3 (k_a k)) (dp := 0);
        [ exact HF | exact HRC | exact HRCk | | | exact HC | exact FR' | ].
      * unfold owe_k, owe_spec. rewrite HK. cbv beta iota zeta. cbn [Z.eqb Pos.eqb orb negb andb].
        replace (d_strips d <=? k_a k) with false by (symmetry; apply Z.leb_gt; lia).
        replace (Z.shiftr (k_b k) 15 =? 0) with true by (symmetry; apply Z.eqb_eq; exact E2).
        cbn [orb negb]. rewrite ER. unfold BS, owe_sx. cbn [fst snd]. reflexivity.
      * unfold Wv, BS, owe_sx. cbn [fst length app].
        replace (le2 (Z_to_bv 64 5104)) with [b8 0xf0; b8 0x13]
          by (apply bytes_eq_of_unsigned; vm_compute; reflexivity).
        cbn [firstn app bz map]. rewrite !b8_lit, !b8_u8.
        rewrite (land_shl6 (k_b k)) by lia. rewrite (Z.lor_comm (k_a k)).
        replace (b8 (-9)) with (b8 0xf7) by (apply bv_eq; vm_compute; reflexivity). reflexivity.
      * split; [eassumption|]. split; [eassumption|]. split; [unfold LLVM_CODEC_STACK; eassumption|].
        split; eassumption.
Qed.
