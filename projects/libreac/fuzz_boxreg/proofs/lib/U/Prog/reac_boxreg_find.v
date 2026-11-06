From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd bcmp_c mac_is_zero_c reac_boxreg_find_c.
Import ListNotations.
Open Scope Z_scope.

Lemma fnd_memcmp : forall n (l r : list byte) v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  -256 < v < 256 /\ (v = 0 <-> l = r).
Proof.
  induction n as [|n IH]; intros [|a l] [|b r] v Hl Hr H; cbn [length memcmp_model] in *; try discriminate.
  - injection H as <-. split; [lia|]. split; intros _; reflexivity.
  - injection Hl as Hl. injection Hr as Hr.
    pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    change (bv_modulus 8) with 256 in Ra, Rb.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
    + assert (a = b) by (apply bv_eq; exact E). subst b.
      destruct (IH l r v Hl Hr H) as [Hv Hi]. split; [exact Hv|].
      split; [intros V; f_equal; apply Hi; exact V | intros Hc; injection Hc as Hc; apply Hi; exact Hc].
    + injection H as <-. split; [lia|].
      split; [intros; lia | intros Hc; injection Hc as Hc _; subst; lia].
Qed.

Lemma fnd_bv : forall m A B bs, bytes_at rsegs m A bs -> B = A -> 0 <= B < 2^64 ->
  bytes_at rsegs m (bv_unsigned (Z_to_bv 64 B)) bs.
Proof. intros m A B bs H -> HB. rewrite unsigned_lit by lia. exact H. Qed.

Lemma fnd_rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a _ 0 4 H) by (rewrite ?length_le4; lia).
  first [ reflexivity | f_equal; apply firstn_all2; rewrite length_le4; lia ].
Qed.

Lemma fnd_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma fnd_addiw : forall i c, 0 <= i < 2^31 -> -2^31 <= i + c < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 i) + c)) = Z_to_bv 64 (i + c).
Proof.
  intros i c Hi Hc. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  change (bv_half_modulus 32) with 2147483648. change (2^31) with 2147483648 in Hi, Hc. lia.
Qed.

Lemma fnd_land3 : forall x, x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.

Lemma fnd_hi : forall x i, 0 <= x < 2^64 -> 64 <= i -> Z.testbit x i = false.
Proof. intros x i Hx Hi. rewrite <- (Z.mod_small x (2^64)) by lia. apply Z.mod_pow2_bits_high. lia. Qed.

Lemma fnd_lxor : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  assert (L : Z.ldiff x (Z.ones 64) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 64).
    - rewrite Z.ones_spec_low by lia. cbn [negb]. apply andb_false_r.
    - rewrite (fnd_hi x i Hx) by lia. reflexivity. }
  rewrite (Z.sub_nocarry_ldiff (Z.ones 64) x L).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.ldiff_spec.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x i); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite (fnd_hi x i Hx) by lia. reflexivity.
Qed.

Ltac fnd_eq := first [ reflexivity | word_eq_tac | rewrite fnd_addiw by lia; word_eq_tac ].
Ltac fnd_fin := first [ lia | Z.div_mod_to_equations; lia ].

Theorem reac_boxreg_find_holds : mac_is_zero_contract -> bcmp_contract -> reac_boxreg_find_contract.
Proof.
  intros MZ BC. unfold mac_is_zero_contract, MAC_IS_ZERO in MZ. unfold bcmp_contract, BCMP in BC.
  unfold reac_boxreg_find_contract, REAC_BOXREG_FIND, REAC_BOXREG_FIND_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo r p bs M -> -> HB HL B1 HM HLM Hr0 Hr4 Hp0 ST LO DR DP HI.
  unfold boxreg_B1 in B1.
  pose proof (bytes_at_bound rsegs m r bs HB) as RB. rewrite HL in RB. change (Z.of_nat 288) with 288 in RB.
  pose proof (bytes_at_bound rsegs m p M HM) as PB. rewrite HLM in PB. change (Z.of_nat 6) with 6 in PB.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  carve_frame 80%nat ST.
  do 14 step.
  lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mm _) => set (QQ := Q); try rename mm into m1 end.
  assert (EPI : forall (mm : word -> option byte) (z : Z)
      (ra' x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
    munch [] m1 mm -> wmono rsegs m1 mm -> mem_inv rsegs mm -> find_result bs M z ->
    x2 = Z_to_bv 64 (bv_unsigned sp + -80) -> x8 = Z_to_bv 64 z ->
    evt rsegs QQ (MS (mkR ra' x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                          x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x13a74) fc None mm (seg_rom rsegs))).
  { intros mm z ra' x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31
      MU0 WM0 HI0 RES -> ->.
    pose proof (rw_cells_transport rsegs [] m1 mm _ _ FR MU0 WM0 I) as FR0.
    pose proof (stk_transport_disjoint rsegs [] m1 mm lo _ ST MU0 WM0 I) as ST0.
    pose proof (bytes_at_transport rsegs [] m1 mm r bs HB MU0 I) as HB0.
    pose proof (bytes_at_transport rsegs [] m1 mm p _ HM MU0 I) as HM0.
    clear FR ST.
    do 11 step.
    release_frame FR0 ST0 (bv_unsigned sp).
    step.
    apply evt_done. unfold QQ. do 15 eexists. exists mm.
    split; [reflexivity|].
    split; [ eapply munch_trans; [ exact MU | eapply munch_weaken; [ | exact MU0 ]; unfold sub_fp; intros; exact I ] |].
    split; [ eapply wmono_trans; [ exact WM | exact WM0 ] |].
    split; [exact HI0|]. split; [exact ST0|]. split; [exact HB0|]. split; [exact HM0|].
    exists z. split; [fnd_eq | exact RES]. }
  assert (KNZ : M <> zero6 -> forall ra' x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word,
    evt rsegs QQ (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 (Z_to_bv 64 (-1)) (Z_to_bv 64 p)
                          x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x13aa4) fc None m1 (seg_rom rsegs))).
  { intros NZ k1 k5 k6 k7 k10 k11 k12 k13 k14 k15 k16 k17 k28 k29 k30 k31.
    assert (LOOP : forall (k : nat) (i : Z) (mm : word -> option byte)
        (ra' x2 x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
      k = Z.to_nat (bx_n bs - i) -> 0 <= i < bx_n bs ->
      x2 = Z_to_bv 64 (bv_unsigned sp + -80) -> x8 = Z_to_bv 64 (-1) -> x9 = Z_to_bv 64 p ->
      x18 = Z_to_bv 64 (r + 56 * i) -> x19 = Z_to_bv 64 i -> x20 = Z_to_bv 64 (56 * i) ->
      bv_unsigned x21 = 18446744073709551615 - r -> x22 = Z_to_bv 64 (bx_n bs - i) -> x23 = Z_to_bv 64 280 ->
      munch [] m1 mm -> wmono rsegs m1 mm -> mem_inv rsegs mm ->
      (forall j, 0 <= j < i -> bx_mac bs j <> M) ->
      evt rsegs QQ (MS (mkR ra' x2 gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20
                            x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x13ad4) fc None mm (seg_rom rsegs))).
    { induction k as [|k IH];
        intros i mm ra' x2 x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31
          Hk Hi E2 E8 E9 E18 E19 E20 E21 E22 E23 MU0 WM0 HI0 NB; [ lia | ].
      subst x2 x8 x9 x18 x19 x20 x22 x23.
      assert (Li : length (bx_mac bs i) = 6%nat) by (unfold bx_mac; apply bsub_length; lia).
      pose proof (bytes_at_transport rsegs [] m1 mm r bs HB MU0 I) as HBm.
      pose proof (bytes_at_transport rsegs [] m1 mm p _ HM MU0 I) as HMm.
      pose proof (bytes_at_bsub mm r bs (56 * i) 6 HBm ltac:(lia) ltac:(lia) ltac:(lia)) as HBi.
      destruct (memcmp_model_total (bx_mac bs i) M 6 ltac:(lia) ltac:(lia)) as [v Hv].
      destruct (fnd_memcmp 6 (bx_mac bs i) M v Li HLM Hv) as [Rv Iv].
      step. if_cases HT0; [ exfalso; zify_cond HT0; fnd_fin | ].
      step. if_cases HT1;
        [ exfalso; zify_cond HT1; rewrite ?E21 in HT1; fnd_fin | ].
      do 4 step.
      eapply evt_cut.
      { eapply BC with (ls := bx_mac bs i) (rs := M) (v := v);
          [ eapply fnd_bv; [ exact HBi | lia | lia ] | eapply fnd_bv; [ exact HMm | lia | lia ]
          | exact Hv | exact HI0 ]. }
      intros ms' PO. unfold memcmp_post in PO.
      destruct PO as (y5' & y6' & y7' & z11 & z12 & z13 & z14 & z15 & z16 & z17 & y28' & y29' & y30' & y31' & mm'
        & E & MUc & WMc & MIc & _ & _).
      subst ms'.
      lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end.
      pose proof (munch_trans [] m1 mm mm' MU0 MUc) as MU1.
      pose proof (wmono_trans rsegs m1 mm mm' WM0 WMc) as WM1.
      step. if_cases HC; zify_cond HC; rewrite ?unsigned_lit_wrap in HC.
      - assert (V : v = 0) by (clear - HC Rv; Z.div_mod_to_equations; lia).
        apply Iv in V.
        step. step.
        apply (EPI mm' i); [ exact MU1 | exact WM1 | exact MIc | | fnd_eq | fnd_eq ].
        unfold find_result, first_mac. right. left. split; [ exact NZ | ].
        split; [ lia | ]. split; [ exact V | exact NB ].
      - assert (V : v <> 0) by (clear - HC Rv; Z.div_mod_to_equations; lia).
        assert (NV : bx_mac bs i <> M) by (intros E; apply Iv in E; lia).
        do 5 step.
        if_cases HC3; zify_cond HC3; rewrite ?unsigned_lit_wrap in HC3.
        + assert (Hi1 : i + 1 < bx_n bs) by (clear - HC3 Hi B1; Z.div_mod_to_equations; lia).
          eapply (IH (i + 1) mm');
            [ lia | lia | fnd_eq | fnd_eq | fnd_eq | fnd_eq | fnd_eq | fnd_eq | exact E21 | fnd_eq | fnd_eq
            | exact MU1 | exact WM1 | exact MIc | ].
          intros j Hj. destruct (Z.eq_dec j i) as [->|Ne]; [ exact NV | apply NB; lia ].
        + assert (Hi1 : i + 1 = bx_n bs) by (clear - HC3 Hi B1; Z.div_mod_to_equations; lia).
          step.
          apply (EPI mm' (-1)); [ exact MU1 | exact WM1 | exact MIc | | fnd_eq | fnd_eq ].
          unfold find_result. right. right. split; [ exact NZ | ]. split; [ reflexivity | ].
          intros j Hj. destruct (Z.eq_dec j i) as [->|Ne]; [ exact NV | apply NB; lia ]. }
    pose proof (rd4_bytes_at m1 r bs 280 HB ltac:(lia) ltac:(rewrite HL; lia)) as HN.
    change (rd4 bs 280) with (bx_n bs) in HN.
    pose proof (fnd_rd4 _ _ _ HN) as RN.
    step. if_cases HT0; [ exfalso; zify_cond HT0; fnd_fin | ].
    step. step. if_cases HT1;
      [ exfalso; zify_cond HT1; rewrite ?(Z.mod_small r) in HT1 by lia; rewrite (fnd_land3 r Hr4) in HT1; fnd_fin | ].
    step. rewrite ?fnd_sx32 by lia.
    step.
    if_cases HC; zify_cond HC.
    - apply (EPI m1 (-1)); [ apply munch_refl | apply wmono_refl | exact HI | | fnd_eq | fnd_eq ].
      unfold find_result. right. right. split; [ exact NZ | ]. split; [ reflexivity | ].
      intros i Hi. lia.
    - do 7 step.
      eapply (LOOP _ 0 m1);
        [ reflexivity | lia | fnd_eq | fnd_eq | fnd_eq | fnd_eq | fnd_eq | fnd_eq | | | fnd_eq
        | apply munch_refl | apply wmono_refl | exact HI | ].
      + rewrite (unsigned_lit r) by lia. rewrite fnd_lxor by lia. apply unsigned_lit. lia.
      + unfold v_slt, c_lts. rewrite lts_lit by lia. rewrite (proj2 (Z.ltb_lt 0 (bx_n bs))) by lia.
        rewrite (unsigned_lit 1), (unsigned_lit (bx_n bs)) by lia.
        rewrite unsigned_lit_wrap. change ((0 - 1) mod 2 ^ 64) with 18446744073709551615.
        rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
        rewrite Z.mod_small by lia. f_equal. lia.
      + intros j Hj. lia. }
  eapply evt_cut.
  { eapply MZ with (p := p) (M := M); [ first [ reflexivity | fnd_eq ] | exact Hp0 | exact HM | exact HLM ]. }
  intros ms' PO.
  destruct PO as (u5 & u6 & u7 & res & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & E & RES).
  subst ms'.
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  destruct RES as [[MZ0 ->] | [MNZ ->]].
  - step. step. try if_false.
    apply (EPI m1 (-1)); [ apply munch_refl | apply wmono_refl | exact HI | | fnd_eq | fnd_eq ].
    unfold find_result. left. split; [ exact MZ0 | reflexivity ].
  - step. step. try if_true.
    apply KNZ. exact MNZ.
Qed.
