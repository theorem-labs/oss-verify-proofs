From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact RcBraid RcBraidLib reac_braid_encode_exact_c.
Import ListNotations.
Open Scope Z_scope.

Definition rbe_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (a N P ns : Z) (K : Z -> Z -> Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 N) (Z_to_bv 64 P) (Z_to_bv 64 N)
                  a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc None m' (seg_rom rsegs) /\
    (forall k : bv 5, ~ (10 <= bv_unsigned k <= 15) -> reg_get F' k = reg_get F k) /\
    munch [(bv_unsigned sp - 32, bv_unsigned sp); (a, a + 3 * N * ns)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' (bv_unsigned sp - 32) (bv_unsigned sp) /\
    (forall x : word, outside [(bv_unsigned sp - 32, bv_unsigned sp)] (bv_unsigned x) ->
       m' x = rb_enc m (rb_rows a N K (Z.to_nat ns)) x).

Section Run.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (a N P ns : Z) (Q : Z -> Z) (V K : Z -> Z -> Z).
  Hypothesis HN : 2 <= N <= 127.
  Hypothesis HNe : N mod 2 = 0.
  Hypothesis Hns : 1 <= ns <= 12.
  Hypothesis FRM : frm0 fc.
  Hypothesis Ha : 0 < a.
  Hypothesis HaE : a + 3 * N * ns <= 2^64.
  Hypothesis HP0 : 0 < P.
  Hypothesis HP8 : P + 8 * N <= 2^64.
  Hypothesis HQ : forall ch, 0 <= ch < N -> 0 < Q ch /\ Q ch mod 4 = 0 /\ Q ch + 4 * ns <= 2^64.
  Hypothesis HV : forall s ch, 0 <= s < ns -> 0 <= ch < N ->
    bytes_at rsegs m (Q ch + 4 * s) (le4 (Z_to_bv 64 (V s ch))) /\ rb_sample (V s ch) (K s ch).
  Hypothesis HD1 : a + 3 * N * ns <= P \/ P + 8 * N <= a.
  Hypothesis HD2 : forall ch, 0 <= ch < N -> a + 3 * N * ns <= Q ch \/ Q ch + 4 * ns <= a.
  Hypothesis HD3 : a + 3 * N * ns <= bv_unsigned sp + -32 \/ bv_unsigned sp <= a.
  Hypothesis Hsp : 32 <= bv_unsigned sp.

  Definition INV (mm : word -> option byte) (L : list (Z * byte)) : Prop :=
    (forall ch, 0 <= ch < N -> bytes_at rsegs mm (P + 8 * ch) (le8 (Z_to_bv 64 (Q ch)))) /\
    (forall s ch, 0 <= s < ns -> 0 <= ch < N -> bytes_at rsegs mm (Q ch + 4 * s) (le4 (Z_to_bv 64 (V s ch)))) /\
    wr_at rsegs mm a (3 * N * ns) /\ mem_inv rsegs mm /\
    (forall x, outside [(bv_unsigned sp + -32, bv_unsigned sp)] (bv_unsigned x) -> mm x = rb_enc m L x) /\
    munch [(bv_unsigned sp + -32, bv_unsigned sp); (a, a + 3 * N * ns)] m mm /\ wmono rsegs m mm.

  Lemma INV_store : forall mm L X b, INV mm L -> a <= X < a + 3 * N * ns ->
    INV (write_to_mem mm (wa X) [b]) (L ++ [(X, b)]).
  Proof.
    intros mm L X b (I1 & I2 & I3 & I4 & I5 & I6 & I7) HX.
    assert (HL : X + Z.of_nat (length [b]) <= 2^64) by (cbn [length Z.of_nat]; lia).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - intros ch Hch. apply bytes_at_write_other; [apply I1; exact Hch | lia | exact HL |].
      rewrite length_le8. cbn [length Z.of_nat]. destruct HD1; lia.
    - intros s ch Hs Hch. apply bytes_at_write_other; [apply I2; assumption | lia | exact HL |].
      rewrite length_le4. cbn [length Z.of_nat]. destruct (HD2 ch Hch); lia.
    - apply wr_at_write. exact I3.
    - apply mem_inv_store; [exact I4|]. cbn [length].
      replace (wa X) with (wa (a + (X - a))) by (f_equal; lia).
      apply (wr_at_store_ok rsegs mm a (3 * N * ns) (X - a) 1 I3); lia.
    - intros x Hx. rewrite rb_enc_app.
      change (rb_enc (rb_enc m L) [(X, b)]) with (write_to_mem (rb_enc m L) (wa X) [b]).
      apply (rbe_wr_agree [(bv_unsigned sp + -32, bv_unsigned sp)]); [lia | exact I5 | exact Hx].
    - apply munch_write; [exact I6 | lia | exact HL | cbn [inside length Z.of_nat]; lia].
    - apply wmono_write. exact I7.
  Qed.

  Lemma FR_store : forall mm cs X b, rw_cells rsegs mm (bv_unsigned sp + -32) cs -> cells_size cs = 32%nat ->
    a <= X < a + 3 * N * ns -> rw_cells rsegs (write_to_mem mm (wa X) [b]) (bv_unsigned sp + -32) cs.
  Proof.
    intros mm cs X b H Hs HX. apply rw_cells_frame; [exact H | lia | cbn [length Z.of_nat]; lia |].
    rewrite Hs. cbn [length Z.of_nat]. destruct HD3; lia.
  Qed.

  Lemma INV_list : forall mm L L', INV mm L -> L = L' -> INV mm L'.
  Proof. intros mm L L' H ->. exact H. Qed.

  Lemma rbe_loop : forall (n : nat) (s ch : Z) (mm : word -> option byte) (G : bvmap 5 word) (j : list byte)
      (x2 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
    n = Z.to_nat ((ns - s) * N - ch) -> 0 <= s < ns -> 0 <= ch < N ->
    x2 = Z_to_bv 64 (bv_unsigned sp + -32) -> x5 = Z_to_bv 64 ch -> x6 = Z_to_bv 64 (s * N) ->
    x7 = Z_to_bv 64 (4 * s) -> x14 = Z_to_bv 64 ns -> x15 = Z_to_bv 64 s -> x16 = Z_to_bv 64 N ->
    x17 = Z_to_bv 64 2147483646 -> x28 = Z_to_bv 64 (P + 8 * ch) ->
    INV mm (rb_rows a N K (Z.to_nat s) ++ rb_row a N K s (Z.to_nat ch)) ->
    rw_cells rsegs mm (bv_unsigned sp + -32) [CB 8 j; C8 s2; C8 s1; C8 s0] -> length j = 8%nat ->
    (forall k : bv 5, ~ (10 <= bv_unsigned k <= 15) -> reg_get G k = reg_get F k) ->
    evt rsegs (rbe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a N P ns K)
      (MS (mkR ra x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 a) (Z_to_bv 64 N) (Z_to_bv 64 P) (Z_to_bv 64 N)
               x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          (bvmap_set 12 (Z_to_bv 64 18446744072820359168) (bvmap_set 13 (Z_to_bv 64 18446744070672875518)
            (bvmap_set 14 (Z_to_bv 64 18446744070672875520) (bvmap_set 15 (Z_to_bv 64 18446744069414584320) G))))
          (Z_to_bv 64 0x138bc) fc None mm (seg_rom rsegs)).
  Proof.
    induction n as [|n IH];
      intros s ch mm G j x2 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x28 x29 x30 x31
        Hn Hs Hch E2 E5 E6 E7 E14 E15 E16 E17 E28 HI FR Hj HG.
    { exfalso. clear - Hn Hs Hch HN. assert (s * N <= ns * N - N) by nia. lia. }
    subst x2 x5 x6 x7 x14 x15 x16 x17 x28.
    destruct (HQ ch Hch) as (HQ0 & HQ4 & HQE).
    destruct (HV s ch Hs Hch) as [_ HVs].
    destruct (rbe_pipe (V s ch) (K s ch) HVs) as (Hv & w & Hw & HM & HL1 & HL2 & HC).
    destruct HVs as [HK _].
    unfold F2P23, FCLAMP_HI, FCLAMP_LO in HM, HL1, HL2.
    pose proof (rbe_pos_bound N s ch ns Hs Hch HNe) as HB.
    assert (HsN : 0 <= s * N <= 1524) by (clear - Hs Hns HN; nia).
    pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hc2.
    assert (RP : ov_read_bytes rsegs mm (wa (P + 8 * ch)) 8 = Some (le8 (Z_to_bv 64 (Q ch))))
      by (apply rbe_rd8; apply (proj1 HI); exact Hch).
    assert (RV : ov_read_bytes rsegs mm (wa (Q ch + 4 * s)) 4 = Some (le4 (Z_to_bv 64 (V s ch))))
      by (apply rbe_rd4; apply (proj1 (proj2 HI)); assumption).
    rbe_st. rbe_st.
    rewrite (rbe_eqb P 0) by lia. if_false.
    rbe_st. rbe_st.
    rewrite (rbe_lts ch N) by lia. if_false.
    rbe_st. rbe_st. rbe_st.
    rewrite (rbe_eqb (Q ch) 0) by lia. if_false.
    rbe_st. rbe_st.
    rewrite (rbe_ld4 (V s ch)) by lia. step. rbe_fpc. rewrite (rbe_u32 (V s ch)) by lia. rewrite HM. cbn [fst snd]. rewrite rbe_fc_same.
    step. rbe_fpc. rewrite (rbe_u32 w) by lia. rewrite HL1. cbn [fst snd]. rewrite rbe_fc_same.
    rbe_st. rbe_st. rbe_st.
    step. rbe_fpc. rewrite (rbe_u32 w) by lia. rewrite HL2. cbn [fst snd]. rewrite rbe_fc_same.
    rbe_st. rbe_st. rbe_st.
    step. rbe_fpc. rewrite (rbe_u32 w) by lia. rewrite HC. cbn [fst snd]. rewrite rbe_fc_same.
    do 14 rbe_st.
    rewrite (unsigned_lit ch) by lia. rewrite (rbe_land_even ch) by lia. rewrite (rbe_land1 ch) by lia.
    rewrite (unsigned_lit (ch mod 2)) by lia. rewrite (rbe_neg5 (ch mod 2)) by lia.
    rewrite (unsigned_lit (ch - ch mod 2 + s * N)) by lia.
    rewrite (Z.shiftl_mul_pow2 _ 1) by lia.
    rewrite (unsigned_lit (K s ch mod 2^64)) by (pose proof (Z.mod_pos_bound (K s ch) (2^64)); lia).
    replace (a + ch mod 2 + ((ch - ch mod 2 + s * N) * 2 ^ 1 + (ch - ch mod 2 + s * N)))
      with (a + rb_lo N s ch - 3) by (unfold rb_lo, rb_G; ring).
    replace (a + 5 * (ch mod 2) + ((ch - ch mod 2 + s * N) * 2 ^ 1 + (ch - ch mod 2 + s * N)))
      with (a + rb_mid N s ch) by (unfold rb_mid, rb_G; ring).
    destruct HB as [HB0 HB1].
    assert (HX1 : a <= a + rb_lo N s ch < a + 3 * N * ns) by (unfold rb_lo; lia).
    assert (HX2 : a <= a + rb_mid N s ch < a + 3 * N * ns) by (unfold rb_mid; lia).
    assert (HX3 : a <= a + rb_hi N s ch < a + 3 * N * ns) by (unfold rb_hi; lia).
    set (L := rb_rows a N K (Z.to_nat s) ++ rb_row a N K s (Z.to_nat ch)) in *.
    set (b1 := Z_to_bv 8 ((K s ch mod 2 ^ 24) mod 256)).
    set (b2 := Z_to_bv 8 ((K s ch mod 2 ^ 24) / 256 mod 256)).
    set (b3 := Z_to_bv 8 ((K s ch mod 2 ^ 24) / 65536)).
    assert (HS1 : store_ok rsegs mm (wa (a + rb_lo N s ch)) 1 = true).
    { apply (wr_at_store_ok rsegs mm a (3 * N * ns) (rb_lo N s ch) 1 (proj1 (proj2 (proj2 HI)))); cbn [Z.of_nat]; lia. }
    step.
    rewrite rbe_le1, rbe_b0. fold b1.
    change (Z_to_bv 64 (a + rb_lo N s ch)) with (wa (a + rb_lo N s ch)).
    pose proof (INV_store mm L (a + rb_lo N s ch) b1 HI HX1) as HI1.
    pose proof (FR_store mm _ (a + rb_lo N s ch) b1 FR eq_refl HX1) as FR1.
    set (mm1 := write_to_mem mm (wa (a + rb_lo N s ch)) [b1]) in *. clearbody mm1.
    assert (HS2 : store_ok rsegs mm1 (wa (a + rb_mid N s ch)) 1 = true).
    { apply (wr_at_store_ok rsegs mm1 a (3 * N * ns) (rb_mid N s ch) 1 (proj1 (proj2 (proj2 HI1)))); unfold rb_mid; cbn [Z.of_nat]; lia. }
    step.
    rewrite rbe_le1, rbe_b1. fold b2.
    change (Z_to_bv 64 (a + rb_mid N s ch)) with (wa (a + rb_mid N s ch)).
    pose proof (INV_store mm1 _ (a + rb_mid N s ch) b2 HI1 HX2) as HI2.
    pose proof (FR_store mm1 _ (a + rb_mid N s ch) b2 FR1 eq_refl HX2) as FR2.
    set (mm2 := write_to_mem mm1 (wa (a + rb_mid N s ch)) [b2]) in *. clearbody mm2.
    assert (HS3 : store_ok rsegs mm2 (wa (a + rb_lo N s ch - 2)) 1 = true).
    { replace (a + rb_lo N s ch - 2) with (a + rb_hi N s ch) by (unfold rb_lo, rb_hi; ring).
      apply (wr_at_store_ok rsegs mm2 a (3 * N * ns) (rb_hi N s ch) 1 (proj1 (proj2 (proj2 HI2)))); unfold rb_hi; cbn [Z.of_nat]; lia. }
    step.
    rewrite rbe_le1, rbe_b2. fold b3.
    replace (a + rb_lo N s ch - 2) with (a + rb_hi N s ch) by (unfold rb_lo, rb_hi; ring).
    change (Z_to_bv 64 (a + rb_hi N s ch)) with (wa (a + rb_hi N s ch)).
    pose proof (INV_store mm2 _ (a + rb_hi N s ch) b3 HI2 HX3) as HI3.
    pose proof (FR_store mm2 _ (a + rb_hi N s ch) b3 FR2 eq_refl HX3) as FR3.
    set (mm3 := write_to_mem mm2 (wa (a + rb_hi N s ch)) [b3]) in *. clearbody mm3.
    assert (HI4 : INV mm3 (rb_rows a N K (Z.to_nat s) ++ rb_row a N K s (Z.to_nat (ch + 1)))).
    { apply (INV_list mm3 _ _ HI3). subst L. rewrite rb_row_succ by lia. unfold rb_turn. subst b1 b2 b3.
      rewrite <- !app_assoc. reflexivity. }
    clear HI HI1 HI2 HI3 FR FR1 FR2 HS1 HS2 HS3 RP RV.
    rbe_st. step.
    rewrite (rbe_eqb N (ch + 1)) by lia.
    destruct (Z.eq_dec (ch + 1) N) as [Hlast|Hmore].
    - replace (N =? ch + 1) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. rbe_rif.
      rbe_st. step.
      rewrite (rbe_eqb (s + 1) ns) by lia.
      destruct (Z.eq_dec (s + 1) ns) as [Hend|Hnext].
      + replace (s + 1 =? ns) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. rbe_rif.
        rbe_st. rbe_st. rbe_st. rbe_st.
        assert (ST : stk rsegs mm3 (bv_unsigned sp + -32) (bv_unsigned sp + -32)).
        { split; [lia|]. split; [pose proof (bv_unsigned_in_range 64 sp) as R; change (bv_modulus 64) with (2^64) in R; lia|].
          intros x Hx; lia. }
        release_frame FR3 ST (bv_unsigned sp).
        step.
        destruct HI4 as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
        apply evt_done. unfold rbe_post. do 13 eexists. split; [reflexivity|].
        split; [intros k Hk; rewrite rbe_fget6 by (first [exact Hk | reflexivity]); apply HG; exact Hk|].
        split; [exact I6|]. split; [exact I7|]. split; [exact I4|]. split; [exact ST|].
        intros x Hx. rewrite (I5 x Hx). rewrite <- Hend, rb_rows_succ by lia. rewrite <- Hlast. reflexivity.
      + replace (s + 1 =? ns) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. rbe_rif.
        step. rewrite (rbe_lts 0 N) by lia. if_false.
        rbe_st. rbe_st. rbe_st. rbe_st.
        rewrite rbe_frot by reflexivity.
        eapply (IH (s + 1) 0 mm3 _ j).
        all: match goal with
             | |- INV _ _ => apply (INV_list mm3 _ _ HI4); rewrite rb_rows_succ by lia; rewrite <- Hlast;
                             cbn [Z.to_nat rb_row]; rewrite app_nil_r; reflexivity
             | |- rw_cells _ _ _ _ => exact FR3
             | |- length _ = _ => exact Hj
             | |- forall k, _ -> _ => intros k Hk; rewrite rbe_fget2 by (first [exact Hk | reflexivity]); apply HG; exact Hk
             | |- _ = Z_to_bv 64 _ => rbe_weq
             | |- _ => idtac
             end.
        all: try (clear - Hn Hs Hch HN Hlast Hnext; nia).
    - replace (N =? ch + 1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. rbe_rif.
      rewrite rbe_frot by reflexivity.
      eapply (IH s (ch + 1) mm3 _ j).
      all: match goal with
           | |- INV _ _ => exact HI4
           | |- rw_cells _ _ _ _ => exact FR3
           | |- length _ = _ => exact Hj
           | |- forall k, _ -> _ => intros k Hk; rewrite rbe_fget2 by (first [exact Hk | reflexivity]); apply HG; exact Hk
           | |- _ = Z_to_bv 64 _ => rbe_weq
           | |- _ => idtac
           end.
      all: try (clear - Hn Hs Hch HN Hmore; nia).
  Qed.

End Run.

Theorem reac_braid_encode_exact_holds : reac_braid_encode_exact_contract.
Proof.
  unfold reac_braid_encode_exact_contract, REAC_BRAID_ENCODE, REAC_BRAID_ENCODE_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    a N P ns Q V K -> -> -> -> -> HN HNe Hns FRM HI ST Ha HaE HW HP0 HP8m HP8 HPb HQ HV HD1 HD2 HD3 HD4 HD5.
  change (evt rsegs ?Qx ?ms) with
    (evt rsegs (rbe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a N P ns K) ms).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  step. rewrite (rbe_lts 0 ns) by lia. if_false.
  step. step.
  assert (PRO : forall x14 : word, x14 = Z_to_bv 64 ns ->
    evt rsegs (rbe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m a N P ns K)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 N) (Z_to_bv 64 P) (Z_to_bv 64 N)
               x14 (Z_to_bv 64 12) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13868) fc None m (seg_rom rsegs))).
  { intros x14 ->.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 32%nat ST.
    step. step. step. step.
    do 12 rbe_st.
    step. rewrite (rbe_lts 0 N) by lia. if_false.
    do 4 rbe_st.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
      assert (HI0 : INV sp m a N P ns Q V m3 (rb_rows a N K (Z.to_nat 0) ++ rb_row a N K 0 (Z.to_nat 0)))
    end.
    { unfold INV. cbn [rb_rows rb_row Z.to_nat app].
      split.
      { intros ch Hch. eapply bytes_at_transport; [apply HPb; exact Hch | exact MU |].
        cbn [disjoint_from]. split; [|exact I]. rewrite length_le8. destruct HD4; lia. }
      split.
      { intros s' ch Hs' Hch. eapply bytes_at_transport; [apply (proj1 (HV s' ch Hs' Hch)) | exact MU |].
        cbn [disjoint_from]. split; [|exact I]. rewrite length_le4. destruct (HD5 ch Hch); lia. }
      split; [exact HW|].
      split; [exact HI|].
      split; [intros x Hx; exact (MU x Hx)|].
      split; [eapply munch_weaken; [|exact MU]; intros x [H1 [H2 _]]; split; [exact H1|exact I]|].
      exact WM. }
    eapply rbe_loop with (n := Z.to_nat ((ns - 0) * N - 0)) (s := 0) (ch := 0).
    all: first
      [ exact HI0
      | match goal with
        | FR : rw_cells _ _ _ ?cs |- length _ = _ => exact (proj1 (proj1 (proj1 FR)))
        | |- forall k, _ -> _ => intros k Hk; reflexivity
        end
      | eassumption
      | reflexivity
      | match goal with |- @eq word _ _ => rbe_weq end
      | lia ].
  }
  if_cases HC12.
  - apply (PRO (Z_to_bv 64 ns)). reflexivity.
  - rbe_rif. step. apply (PRO (Z_to_bv 64 12)).
    unfold bv_ltu in HC12. rewrite !unsigned_lit in HC12 by lia. apply Z.ltb_ge in HC12.
    f_equal. lia.
Qed.

