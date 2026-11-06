From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd lowest_free_base_c range_taken_c.
Import ListNotations.
Open Scope Z_scope.

Lemma lfb_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lfb_rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a _ 0 4 H) by (rewrite ?length_le4; lia).
  first [ reflexivity | f_equal; apply firstn_all2; rewrite length_le4; lia ].
Qed.

Lemma lfb_land3 : forall r, Z.land r 3 = r mod 4.
Proof. intros r. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Theorem lowest_free_base_holds : range_taken_contract -> lowest_free_base_contract.
Proof.
  intros RT. unfold range_taken_contract, RANGE_TAKEN in RT.
  unfold lowest_free_base_contract, LOWEST_FREE_BASE, LOWEST_FREE_BASE_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo r k bs E0 E1 Hk HB HL H1 H2 H3 H4 ST LO DJ HI.
  subst a0 a1.
  pose proof H2 as H2'. unfold boxreg_B2 in H2'.
  pose proof H1 as H1'. unfold boxreg_B1 in H1'.
  assert (H3' : forall i, 0 <= i < bx_n bs ->
            0 <= bx_base bs i /\ 0 <= bx_nch bs i /\ bx_base bs i + bx_nch bs i <= bx_fabric bs)
    by (intros i Hi; destruct (H3 i Hi) as (_ & ? & _ & ? & ?); lia).
  pose proof (bytes_at_bound rsegs m r bs HB) as RB. rewrite HL in RB. change (Z.of_nat 288) with 288 in RB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  carve_frame 32%nat ST.
  do 8 step.
  if_cases HC0; zify_cond HC0; [ exfalso; rewrite lfb_land3 in HC0; lia | clear HC0 ].
  step. step.
  lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mm _) => set (QQ := Q); try rename mm into m1 end.
  pose proof (rd4_bytes_at m1 r bs 284 HB ltac:(lia) ltac:(rewrite HL; lia)) as HF.
  change (rd4 bs 284) with (bx_fabric bs) in HF.
  pose proof (lfb_rd4 _ _ _ HF) as RF. clear HF.
  assert (EPI : forall (z : Z) (ra' x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
      x2 = Z_to_bv 64 (bv_unsigned sp + -32) -> x8 = Z_to_bv 64 r -> x9 = Z_to_bv 64 k -> x18 = Z_to_bv 64 z ->
      lowest_free bs k z ->
      evt rsegs QQ (MS (mkR ra' x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
                            s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x13da8) fc None m1 (seg_rom rsegs))).
  { intros z ra' x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 -> -> -> -> LF.
    do 6 step.
    release_frame FR ST (bv_unsigned sp).
    step.
    apply evt_done. unfold QQ. do 15 eexists. exists m1.
    split; [ reflexivity | ].
    split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact HI | ]. split; [ exact ST | ].
    exists z. split; [ word_eq_tac | exact LF ]. }
  assert (LOOP : forall (d : nat) (b : Z)
      (ra' x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
      d = Z.to_nat (41 - b) -> 0 <= b <= 40 -> b + k < 2^31 ->
      (forall c, 0 <= c < b -> slice_meets bs c k) ->
      x2 = Z_to_bv 64 (bv_unsigned sp + -32) -> x8 = Z_to_bv 64 r -> x9 = Z_to_bv 64 k -> x18 = Z_to_bv 64 b ->
      evt rsegs QQ (MS (mkR ra' x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
                            s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x13d68) fc None m1 (seg_rom rsegs))).
  { induction d as [|d IH];
      intros b ra' x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 Hd Hb Hbk HM E2 E8 E9 E18;
      [ lia | ].
    subst x2 x8 x9 x18.
    step. rewrite lfb_sx32 by lia.
    step. rewrite swrap_add by lia.
    step. rewrite lts_lit by lia.
    if_cases HC; zify_bool HC.
    - step.
      eapply (EPI (-1)); [ word_eq_tac | word_eq_tac | word_eq_tac | word_eq_tac | ].
      left. split; [ reflexivity | ].
      intros c Hc0 Hck. destruct (Z.lt_ge_cases c b) as [L|L]; [ apply HM; lia | lia ].
    - step. step. step. step.
      eapply evt_cut.
      { eapply RT with (r := r) (b := b) (k := k) (bs := bs);
          [ word_eq_tac | word_eq_tac | word_eq_tac | exact HB | exact HL | exact H4 | exact H1 | lia | exact H3'
          | lia | lia | lia ]. }
      intros ms' PO.
      destruct PO as (y5 & y6 & y7 & res & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & E & RES).
      subst ms'.
      lazymatch goal with
      | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end.
      destruct RES as [(SM & ->) | (NSM & ->)].
      + step. if_false.
        step. rewrite swrap_addi by lia.
        step. rewrite lts_lit by lia. if_false.
        step. step. rewrite swrap_add by lia.
        step. step. if_true.
        eapply IH with (b := b + 1); [ lia | lia | lia | | word_eq_tac | word_eq_tac | word_eq_tac | word_eq_tac ].
        intros c Hc. destruct (Z.lt_ge_cases c b) as [L|L]; [ apply HM; lia | ].
        replace c with b by lia. exact SM.
      + step. if_true.
        eapply (EPI b); [ word_eq_tac | word_eq_tac | word_eq_tac | word_eq_tac | ].
        right. split; [ lia | split; [ lia | split; [ exact NSM | exact HM ] ] ]. }
  eapply (LOOP (Z.to_nat 41) 0); [ reflexivity | lia | lia | intros c Hc; lia
                                 | word_eq_tac | word_eq_tac | word_eq_tac | word_eq_tac ].
Qed.
