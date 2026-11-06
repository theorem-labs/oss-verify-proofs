From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg BoxregRd bcmp_c reac_boxreg_find_c.
Import ListNotations.
Open Scope Z_scope.

Lemma fnd_ub : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  apply unsigned_lit. lia.
Qed.

Lemma fnd_b0 : forall b : byte, bv_unsigned b = 0 -> b = Z_to_bv 8 0.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma fnd_zero6 : forall b0 b1 b2 b3 b4 b5 : byte,
  bv_unsigned b0 = 0 -> bv_unsigned b1 = 0 -> bv_unsigned b2 = 0 ->
  bv_unsigned b3 = 0 -> bv_unsigned b4 = 0 -> bv_unsigned b5 = 0 ->
  [b0; b1; b2; b3; b4; b5] = zero6.
Proof.
  intros b0 b1 b2 b3 b4 b5 H0 H1 H2 H3 H4 H5.
  apply fnd_b0 in H0, H1, H2, H3, H4, H5. subst. reflexivity.
Qed.

Lemma fnd_nz : forall (l : list byte) (k : nat) (b : byte),
  nth_error l k = Some b -> bv_unsigned b <> 0 -> l <> zero6.
Proof.
  intros l k b Hk Hb E. subst l. unfold zero6 in Hk.
  apply nth_error_In, repeat_spec in Hk. subst b. apply Hb. reflexivity.
Qed.

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

Ltac fnd_eq := first [ reflexivity | word_eq_tac | rewrite fnd_addiw by lia; word_eq_tac ].

Theorem reac_boxreg_find_holds : bcmp_contract -> reac_boxreg_find_contract.
Proof.
  intros BC. unfold bcmp_contract, BCMP in BC.
  unfold reac_boxreg_find_contract, REAC_BOXREG_FIND, REAC_BOXREG_FIND_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo r p bs M -> -> HB HL B1 HM HLM ST LO DR DP HI.
  unfold boxreg_B1 in B1.
  destruct M as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|]]]]]]]; try discriminate HLM. clear HLM.
  pose proof (bytes_at_bound rsegs m r bs HB) as RB. rewrite HL in RB. change (Z.of_nat 288) with 288 in RB.
  pose proof (bytes_at_bound rsegs m p _ HM) as PB. cbn [length] in PB. change (Z.of_nat 6) with 6 in PB.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  carve_frame 48%nat ST.
  do 11 step.
  lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mm _) => set (QQ := Q); try rename mm into m1 end.
  assert (EPI : forall (mm : word -> option byte) (z : Z)
      (ra' x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
    munch [] m1 mm -> wmono rsegs m1 mm -> mem_inv rsegs mm -> find_result bs [b0; b1; b2; b3; b4; b5] z ->
    x2 = Z_to_bv 64 (bv_unsigned sp + -48) -> x18 = Z_to_bv 64 z ->
    evt rsegs QQ (MS (mkR ra' x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                          s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x13840) fc None mm (seg_rom rsegs))).
  { intros mm z ra' x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31
      MU0 WM0 HI0 RES -> ->.
    pose proof (rw_cells_transport rsegs [] m1 mm _ _ FR MU0 WM0 I) as FR0.
    pose proof (stk_transport_disjoint rsegs [] m1 mm lo _ ST MU0 WM0 I) as ST0.
    pose proof (bytes_at_transport rsegs [] m1 mm r bs HB MU0 I) as HB0.
    pose proof (bytes_at_transport rsegs [] m1 mm p _ HM MU0 I) as HM0.
    clear FR ST.
    do 8 step.
    release_frame FR0 ST0 (bv_unsigned sp).
    step.
    apply evt_done. unfold QQ. do 15 eexists. exists mm.
    split; [reflexivity|].
    split; [ eapply munch_trans; [ exact MU | eapply munch_weaken; [ | exact MU0 ]; unfold sub_fp; intros; exact I ] |].
    split; [ eapply wmono_trans; [ exact WM | exact WM0 ] |].
    split; [exact HI0|]. split; [exact ST0|]. split; [exact HB0|]. split; [exact HM0|].
    exists z. split; [fnd_eq | exact RES]. }
  assert (KNZ : [b0; b1; b2; b3; b4; b5] <> zero6 -> forall x10 x11 x12 x13 : word,
    evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 p) (Z_to_bv 64 r)
                          x10 x11 x12 x13 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13808) fc None m1 (seg_rom rsegs))).
  { intros NZ x10 x11 x12 x13.
    assert (LOOP : forall (k : nat) (i : Z) (mm : word -> option byte)
        (ra' x2 x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x28 x29 x30 x31 : word),
      k = Z.to_nat (bx_n bs - i) -> 0 <= i < bx_n bs ->
      x2 = Z_to_bv 64 (bv_unsigned sp + -48) -> x8 = Z_to_bv 64 p -> x9 = Z_to_bv 64 (r + 56 * i) ->
      x18 = Z_to_bv 64 (-1) -> x19 = Z_to_bv 64 (bx_n bs - i) -> x20 = Z_to_bv 64 i ->
      munch [] m1 mm -> wmono rsegs m1 mm -> mem_inv rsegs mm ->
      (forall j, 0 <= j < i -> bx_mac bs j <> [b0; b1; b2; b3; b4; b5]) ->
      evt rsegs QQ (MS (mkR ra' x2 gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20
                            s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x13814) fc None mm (seg_rom rsegs))).
    { induction k as [|k IH];
        intros i mm ra' x2 x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x28 x29 x30 x31
          Hk Hi E2 E8 E9 E18 E19 E20 MU0 WM0 HI0 NB; [ lia | ].
      subst x2 x8 x9 x18 x19 x20.
      assert (Li : length (bx_mac bs i) = 6%nat) by (unfold bx_mac; apply bsub_length; lia).
      pose proof (bytes_at_transport rsegs [] m1 mm r bs HB MU0 I) as HBm.
      pose proof (bytes_at_transport rsegs [] m1 mm p _ HM MU0 I) as HMm.
      pose proof (bytes_at_bsub mm r bs (56 * i) 6 HBm ltac:(lia) ltac:(lia) ltac:(lia)) as HBi.
      destruct (memcmp_model_total (bx_mac bs i) [b0; b1; b2; b3; b4; b5] 6 ltac:(lia) ltac:(cbn; lia))
        as [v Hv].
      destruct (fnd_memcmp 6 (bx_mac bs i) [b0; b1; b2; b3; b4; b5] v Li eq_refl Hv) as [Rv Iv].
      do 4 step.
      eapply evt_cut.
      { eapply BC with (ls := bx_mac bs i) (rs := [b0; b1; b2; b3; b4; b5]) (v := v);
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
        step.
        apply (EPI mm' i); [ exact MU1 | exact WM1 | exact MIc | | fnd_eq | fnd_eq ].
        unfold find_result, first_mac. right. left. split; [ exact NZ | ].
        split; [ lia | ]. split; [ exact V | exact NB ].
      - assert (V : v <> 0) by (clear - HC Rv; Z.div_mod_to_equations; lia).
        assert (NV : bx_mac bs i <> [b0; b1; b2; b3; b4; b5]) by (intros E; apply Iv in E; lia).
        do 4 step.
        if_cases HC3; zify_cond HC3; rewrite ?unsigned_lit_wrap in HC3.
        + assert (Hi1 : i + 1 < bx_n bs) by (clear - HC3 Hi B1; Z.div_mod_to_equations; lia).
          eapply (IH (i + 1) mm'); [ lia | lia | fnd_eq | fnd_eq | fnd_eq | fnd_eq | fnd_eq | fnd_eq
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
    step. rewrite ?fnd_sx32 by lia.
    step.
    if_cases HC; zify_cond HC.
    - apply (EPI m1 (-1)); [ apply munch_refl | apply wmono_refl | exact HI | | fnd_eq | fnd_eq ].
      unfold find_result. right. right. split; [ exact NZ | ]. split; [ reflexivity | ].
      intros i Hi. lia.
    - step.
      eapply (LOOP _ 0 m1); [ reflexivity | lia | fnd_eq | fnd_eq | fnd_eq
                            | fnd_eq | fnd_eq | fnd_eq | apply munch_refl | apply wmono_refl | exact HI | ].
      intros j Hj. lia. }
  assert (RD : forall k, 0 <= k < 6 ->
    ov_read_bytes rsegs m1 (wa (p + k)) 1 = Some (firstn 1 (skipn (Z.to_nat k) [b0; b1; b2; b3; b4; b5])))
    by (intros k Hk; apply bytes_at_read; [ exact HM | lia | cbn [length]; lia ]).
  pose proof (RD 0 ltac:(lia)) as R0. change (firstn 1 (skipn (Z.to_nat 0) [b0; b1; b2; b3; b4; b5])) with [b0] in R0.
  pose proof (RD 1 ltac:(lia)) as R1. change (firstn 1 (skipn (Z.to_nat 1) [b0; b1; b2; b3; b4; b5])) with [b1] in R1.
  pose proof (RD 2 ltac:(lia)) as R2. change (firstn 1 (skipn (Z.to_nat 2) [b0; b1; b2; b3; b4; b5])) with [b2] in R2.
  pose proof (RD 3 ltac:(lia)) as R3. change (firstn 1 (skipn (Z.to_nat 3) [b0; b1; b2; b3; b4; b5])) with [b3] in R3.
  pose proof (RD 4 ltac:(lia)) as R4. change (firstn 1 (skipn (Z.to_nat 4) [b0; b1; b2; b3; b4; b5])) with [b4] in R4.
  pose proof (RD 5 ltac:(lia)) as R5. change (firstn 1 (skipn (Z.to_nat 5) [b0; b1; b2; b3; b4; b5])) with [b5] in R5.
  clear RD.
  step. clear R0. step. if_cases HC0; zify_cond HC0; rewrite ?fnd_ub in HC0.
  { step. step. if_cases HZ; zify_cond HZ; rewrite ?fnd_ub in HZ; [ lia | ].
    apply KNZ. apply (fnd_nz _ 0 b0); [ reflexivity | exact HC0 ]. }
  step. step. step. step. if_true.
  step. clear R1. step. if_cases HC1; zify_cond HC1; rewrite ?fnd_ub in HC1.
  { step. step. if_cases HZ; zify_cond HZ; rewrite ?fnd_ub in HZ; [ lia | ].
    apply KNZ. apply (fnd_nz _ 1 b1); [ reflexivity | exact HC1 ]. }
  step. step. step. step. if_true.
  step. clear R2. step. if_cases HC2; zify_cond HC2; rewrite ?fnd_ub in HC2.
  { step. step. if_cases HZ; zify_cond HZ; rewrite ?fnd_ub in HZ; [ lia | ].
    apply KNZ. apply (fnd_nz _ 2 b2); [ reflexivity | exact HC2 ]. }
  step. step. step. step. if_true.
  step. clear R3. step. if_cases HC3; zify_cond HC3; rewrite ?fnd_ub in HC3.
  { step. step. if_cases HZ; zify_cond HZ; rewrite ?fnd_ub in HZ; [ lia | ].
    apply KNZ. apply (fnd_nz _ 3 b3); [ reflexivity | exact HC3 ]. }
  step. step. step. step. if_true.
  step. clear R4. step. if_cases HC4; zify_cond HC4; rewrite ?fnd_ub in HC4.
  { step. step. if_cases HZ; zify_cond HZ; rewrite ?fnd_ub in HZ; [ lia | ].
    apply KNZ. apply (fnd_nz _ 4 b4); [ reflexivity | exact HC4 ]. }
  step. step. step. step. if_true.
  step. clear R5. step. if_cases HC5; zify_cond HC5; rewrite ?fnd_ub in HC5.
  { step. step. if_cases HZ; zify_cond HZ; rewrite ?fnd_ub in HZ; [ lia | ].
    apply KNZ. apply (fnd_nz _ 5 b5); [ reflexivity | exact HC5 ]. }
  step. step. step. step. if_false.
  step. step. if_cases HZ; zify_cond HZ; rewrite ?fnd_ub in HZ; [ | lia ].
  apply (EPI m1 (-1)); [ apply munch_refl | apply wmono_refl | exact HI | | fnd_eq | fnd_eq ].
  unfold find_result. left. split; [ apply fnd_zero6; assumption | reflexivity ].
Qed.
