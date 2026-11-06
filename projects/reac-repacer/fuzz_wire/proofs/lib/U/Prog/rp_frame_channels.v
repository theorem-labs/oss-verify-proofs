(* rp_frame_channels walk, fuzz_wire ubsan 6e91fe0b5555 0x13938..0x139a8 (no UBSan check in it) (repace_wire.c:74-86); new.
   reac_frame_clean_len is the named Section hypothesis HCL (its contract, reac_frame_clean_len_c.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import reac_frame_clean_len_c rp_frame_channels_c.
Import ListNotations.
Open Scope Z_scope.

(* The .rodata constants, read from the image through any overlay that keeps mem_inv. *)
Lemma wire_consts : forall m, mem_inv rsegs m ->
  bytes_at rsegs m A_M (le8 (Z_to_bv 64 KM)) /\ bytes_at rsegs m A_T (le8 (Z_to_bv 64 KT)) /\
  bytes_at rsegs m A_K36 (le8 (Z_to_bv 64 K36)).
Proof.
  intros m MI. split; [|split]; (apply ro_bytes_at;
    [ exact MI | unfold A_M, A_T, A_K36; lia
    | rewrite length_le8; change (Z.of_nat 8) with 8; unfold A_M, A_T, A_K36; lia
    | apply ro_bytes_b_sound; vm_compute; reflexivity ]).
Qed.

Lemma clean_range : forall n, 0 <= n -> 0 <= reac_frame_clean_len_model n <= n.
Proof.
  intros n Hn. unfold reac_frame_clean_len_model.
  destruct ((54 <=? n) && ((n - 52) mod 36 =? 2)) eqn:E; [|lia].
  apply andb_prop in E. destruct E as [E _]. apply Z.leb_le in E. lia.
Qed.

(* mulhu by K36 = ceil(2^69 / 36), then srli 5: the quotient by 36 of any 64-bit x. *)
Lemma div36 : forall x, 0 <= x < 2^64 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr (x * 16397105843297379215) 64))) 5 = x / 36.
Proof.
  intros x Hx.
  rewrite (Z.shiftr_div_pow2 (x * 16397105843297379215) 64) by lia.
  rewrite unsigned_lit.
  2: { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
  assert (E : x = 36 * (x / 36) + x mod 36) by (apply Z.div_mod; lia).
  pose proof (Z.mod_pos_bound x 36 ltac:(lia)) as R.
  set (q := x / 36) in *. set (r := x mod 36) in *. clearbody q r.
  symmetry. apply Z.div_unique with (r := x * 16397105843297379215 - 2^64 * 2^5 * q); lia.
Qed.

Lemma odd_mod2 : forall a, Z.odd a = (a mod 2 =? 1).
Proof.
  intros a. pose proof (Z.mod_pos_bound a 2 ltac:(lia)) as R. pose proof (Z.div_mod a 2 ltac:(lia)) as D.
  destruct (Z.odd a) eqn:E.
  - apply Z.odd_spec in E. destruct E as [k Hk]. symmetry. apply Z.eqb_eq. lia.
  - symmetry. apply Z.eqb_neq. intro H1.
    assert (E2 : Z.odd a = true) by (apply Z.odd_spec; exists (a / 2); lia). congruence.
Qed.

Lemma odd_sw32 : forall q, Z.odd (bv_swrap 32 q) = (q mod 2 =? 1).
Proof.
  intros q. rewrite odd_mod2. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31).
  Z.div_mod_to_equations. lia.
Qed.

(* addiw a1, q, -2; sltiu a1, a1, 39: (int)q - 2 in [0, 38]. *)
Lemma sw32_iff : forall q, 0 <= q ->
  (bv_swrap 32 (q + -2) mod 2^64 < 39 <-> 2 <= bv_swrap 32 q <= 40).
Proof.
  intros q Hq. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31).
  split; intros H; Z.div_mod_to_equations; lia.
Qed.

Lemma sltiu39 : forall q, 0 <= q ->
  v_sltiu (Z_to_bv 64 (bv_swrap 32 (q + -2))) 39 =
  Z_to_bv 64 (if (2 <=? bv_swrap 32 q) && (bv_swrap 32 q <=? 40) then 1 else 0).
Proof.
  intros q Hq. unfold v_sltiu. change (bv_wrap 64 39) with 39. rewrite unsigned_lit_wrap.
  destruct (sw32_iff q Hq) as [I1 I2].
  destruct (Z.ltb_spec (bv_swrap 32 (q + -2) mod 2^64) 39) as [H1|H1];
  destruct (Z.leb_spec 2 (bv_swrap 32 q)) as [H2|H2];
  destruct (Z.leb_spec (bv_swrap 32 q) 40) as [H3|H3]; cbn [andb];
  first [reflexivity | exfalso; lia].
Qed.

(* andi a2, q, 1; seqz a2, a2: q even. *)
Lemma seqz_lsb : forall q, 0 <= q ->
  v_sltiu (Z_to_bv 64 (Z.land q 1)) 1 = Z_to_bv 64 (if q mod 2 =? 0 then 1 else 0).
Proof.
  intros q Hq. unfold v_sltiu. change (bv_wrap 64 1) with 1.
  replace (Z.land q 1) with (q mod 2) by (symmetry; apply (Z.land_ones q 1); lia).
  pose proof (Z.mod_pos_bound q 2 ltac:(lia)) as R.
  rewrite unsigned_lit by lia.
  destruct (Z.ltb_spec (q mod 2) 1); destruct (Z.eqb_spec (q mod 2) 0); first [reflexivity | exfalso; lia].
Qed.

Lemma lor_ones64 : forall q, 0 <= q < 2^64 -> Z.lor 18446744073709551615 q = 18446744073709551615.
Proof.
  intros q Hq. change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. cbn [orb].
    destruct (Z.eq_dec q 0) as [->|Hq0]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia | lia].
Qed.

(* 0x1397c..0x13998: the channel test and the return value, on the quotient q in register a0 (w). *)
Lemma fc_tail : forall (w : word) q, w = Z_to_bv 64 q -> 0 <= q < 2^62 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64
     (Z.land (bv_unsigned (v_sltiu (Z_to_bv 64 (bv_swrap 32 (bv_unsigned w + -2))) 39))
             (bv_unsigned (v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned w) 1)) 1)) + -1)))
     (bv_unsigned w))) + 0))
  = Z_to_bv 64 (if (bv_swrap 32 q <? 2) || (40 <? bv_swrap 32 q) || Z.odd (bv_swrap 32 q) then -1
                else bv_swrap 32 q).
Proof.
  intros w q -> Hq. rewrite (unsigned_lit q) by lia.
  rewrite (sltiu39 q), (seqz_lsb q) by lia. rewrite odd_sw32.
  pose proof (Z.mod_pos_bound q 2 ltac:(lia)) as R2.
  set (s := bv_swrap 32 q).
  destruct (Z.leb_spec 2 s) as [L1|L1]; destruct (Z.leb_spec s 40) as [L2|L2];
  destruct (Z.eqb_spec (q mod 2) 0) as [E2|E2]; cbn [andb]; fold_closed_in_goal.
  1: { rewrite Z.lor_0_l, (unsigned_lit q), Z.add_0_r by lia.
       rewrite (proj2 (Z.ltb_ge s 2)), (proj2 (Z.ltb_ge 40 s)), (proj2 (Z.eqb_neq (q mod 2) 1)) by lia.
       reflexivity. }
  all: rewrite lor_ones64 by lia; fold_closed_in_goal;
       destruct (Z.ltb_spec s 2); destruct (Z.ltb_spec 40 s); destruct (Z.eqb_spec (q mod 2) 1); cbn [orb];
       first [reflexivity | exfalso; lia].
Qed.

(* The a0 (x10) entry of a register map in mkR's tree layout. *)
Ltac a0_of R := lazymatch R with TNode _ _ (TNode _ _ (TNode (TNode _ (Some ?w) _) _ _)) => w end.
Ltac set_a0 v := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => let w := a0_of R in replace w with v end.

Section FC.
Hypothesis HCL : reac_frame_clean_len_contract.

Ltac fc_finish sp :=
  lazymatch goal with
  | FR : rw_cells _ _ _ _, ST : stk _ _ _ _, MU : munch _ _ _, WM : wmono _ _ _, MI : mem_inv _ _ |- _ =>
      release_frame FR ST (bv_unsigned sp);
      apply evt_done; do 4 eexists; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [exact MI|exact ST]
  end.

Theorem rp_frame_channels_holds : rp_frame_channels_contract.
Proof.
  unfold rp_frame_channels_contract, RP_FRAME_CHANNELS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    MI ST LO.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  do 5 step.
  if_cases HZ.
  - (* len < 0 *)
    zify_cond HZ. do 5 step.
    set_a0 (Z_to_bv 64 (rp_frame_channels_model (bv_signed a0))).
    2: { f_equal. unfold rp_frame_channels_model. rewrite (zb_signed a0).
         rewrite (proj2 (Z.ltb_ge (bv_unsigned a0) (2^63))) by lia. cbv beta iota.
         rewrite (proj2 (Z.ltb_lt (bv_unsigned a0 - 2^64) 0)) by lia. reflexivity. }
    fc_finish sp.
  - zify_cond HZ. step.
    destruct (wire_consts m1 MI) as (CM & CT & _).
    eapply evt_cut; [eapply HCL; [exact CM | exact CT] |].
    intros ms' (a1' & a2' & a3' & ->). clear CM CT.
    replace (ret_pc (Z_to_bv 64 80208)) with (Z_to_bv 64 80208) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    remember (reac_frame_clean_len_model (bv_unsigned a0)) as c eqn:Ec.
    assert (Rc : 0 <= c <= bv_unsigned a0) by (subst c; apply clean_range; lia).
    step. step. if_cases HC.
    + (* clean < 52 *)
      zify_cond HC. try rewrite Z.mod_small in HC by lia. do 5 step.
      set_a0 (Z_to_bv 64 (rp_frame_channels_model (bv_signed a0))).
      2: { f_equal. unfold rp_frame_channels_model. rewrite (zb_signed a0).
           rewrite (proj2 (Z.ltb_lt (bv_unsigned a0) (2^63))) by lia. cbv beta iota zeta.
           rewrite (proj2 (Z.ltb_ge (bv_unsigned a0) 0)) by lia. rewrite <- Ec.
           rewrite (proj2 (Z.ltb_lt c 52)) by lia. reflexivity. }
      fc_finish sp.
    + zify_cond HC. try rewrite Z.mod_small in HC by lia.
      do 5 step.
      rewrite (unsigned_lit (c + -52)) by lia.
      replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftr ((c + -52) * 16397105843297379215) 64))) 5))
        with (Z_to_bv 64 ((c + -52) / 36)) by (f_equal; symmetry; apply div36; lia).
      remember ((c + -52) / 36) as q eqn:Eq.
      assert (Er : c + -52 = 36 * q + (c + -52) mod 36) by (subst q; apply Z.div_mod; lia).
      pose proof (Z.mod_pos_bound (c + -52) 36 ltac:(lia)) as R36.
      remember ((c + -52) mod 36) as r eqn:Erd.
      assert (Rq : 0 <= q) by (subst q; apply Z.div_pos; lia).
      step. step. rewrite (unsigned_lit q) by lia. step.
      rewrite (unsigned_lit (c + -52)), (unsigned_lit (q * 36)) by lia.
      replace (c + -52 - q * 36) with r by lia.
      step. if_cases HR.
      * (* (clean - 52) % 36 != 0 *)
        zify_cond HR. try rewrite Z.mod_small in HR by lia. do 5 step.
        set_a0 (Z_to_bv 64 (rp_frame_channels_model (bv_signed a0))).
        2: { f_equal. unfold rp_frame_channels_model. rewrite (zb_signed a0).
             rewrite (proj2 (Z.ltb_lt (bv_unsigned a0) (2^63))) by lia. cbv beta iota zeta.
             rewrite (proj2 (Z.ltb_ge (bv_unsigned a0) 0)) by lia. rewrite <- Ec.
             replace ((c - 52) mod 36) with r by (rewrite Erd; reflexivity).
             rewrite (proj2 (Z.ltb_ge c 52)), (proj2 (Z.eqb_neq r 0)) by lia. reflexivity. }
        fc_finish sp.
      * zify_cond HR. try rewrite Z.mod_small in HR by lia. do 7 step. do 5 step.
        set_a0 (Z_to_bv 64 (rp_frame_channels_model (bv_signed a0))).
        2: { transitivity (Z_to_bv 64 (if (bv_swrap 32 q <? 2) || (40 <? bv_swrap 32 q) || Z.odd (bv_swrap 32 q)
                                       then -1 else bv_swrap 32 q)).
             - f_equal. unfold rp_frame_channels_model. rewrite (zb_signed a0).
               rewrite (proj2 (Z.ltb_lt (bv_unsigned a0) (2^63))) by lia. cbv beta iota zeta.
               rewrite (proj2 (Z.ltb_ge (bv_unsigned a0) 0)) by lia. rewrite <- Ec.
               replace ((c - 52) mod 36) with r by (rewrite Erd; reflexivity).
               replace ((c - 52) / 36) with q by (rewrite Eq; reflexivity).
               rewrite (proj2 (Z.ltb_ge c 52)), (proj2 (Z.eqb_eq r 0)) by lia. reflexivity.
             - symmetry. apply fc_tail; [reflexivity | lia]. }
        fc_finish sp.
Qed.

End FC.
