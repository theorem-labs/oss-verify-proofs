(* Ported by a Theorem Labs lane from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Prog/twoway_loops.v, unchanged. *)
From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Spec Require Import TwoWay StrBytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog Require Import twoway_loops_c.
Import ListNotations.
Open Scope Z_scope.

Lemma tw_at_u : forall (l : list byte) i b, nth_error l i = Some b -> at_ (map bv_unsigned l) i = bv_unsigned b.
Proof.
  induction l as [|y l IH]; intros [|i] b E; cbn in *; try discriminate.
  - inversion E; reflexivity.
  - apply IH. exact E.
Qed.

Lemma tw_nth_ex : forall (l : list byte) i, (i < length l)%nat -> exists b, nth_error l i = Some b.
Proof. intros l i H. destruct (nth_error l i) as [b|] eqn:E; [eauto|]. apply nth_error_None in E. lia. Qed.

Ltac tw_side := first [ reflexivity | f_equal; lia
                      | apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia | lia ].

Theorem msuf1_ok : MSUF1_OK.
Proof.
  unfold MSUF1_OK.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m x c0 jp0 k0 p0
         HX L Hc0 Hk0 Hp0 Hl0 K0.
  pose proof (bytes_at_bound _ _ _ _ HX) as BX. rewrite length_app in BX. cbn [length] in BX.
  enough (MAIN : forall (a b c jp k p : nat) (y5 y6 : word),
    (2 * length x - (c + jp) = a)%nat -> (length x - k = b)%nat ->
    (c <= jp)%nat -> (1 <= k <= p)%nat -> (p <= length x)%nat -> (jp + k < length x)%nat ->
    (forall (c' p' : nat) (y2 y3 y4 y5 y6 : word),
        msuf_run Z.gtb (map bv_unsigned x) c jp k p c' p' ->
        evt rsegs Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat c' - 1)) (Z_to_bv 64 (Z.of_nat p'))
                   y2 y3 y4 y5 y6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x93518) fc None m (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat c - 1)) (Z_to_bv 64 (Z.of_nat p))
               (Z_to_bv 64 (Z.of_nat jp)) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (Z.of_nat (jp + k))) y5 y6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x932b4) fc None m (seg_rom rsegs))).
  { exact (MAIN _ _ c0 jp0 k0 p0 a5 a6 eq_refl eq_refl Hc0 Hk0 Hp0 Hl0 K0). }
  clear K0 Hc0 Hk0 Hp0 Hl0.
  induction a as [a IHa] using lt_wf_ind.
  induction b as [b IHb] using lt_wf_ind.
  intros c jp k p y5 y6 Ha Hb Hc Hk Hp Hl K.
  assert (BACK : forall (c' jp' k' p' : nat) (w0 w1 w2 w3 z4 z5 z6 : word),
    w0 = Z_to_bv 64 (Z.of_nat c' - 1) -> w1 = Z_to_bv 64 (Z.of_nat p') ->
    w2 = Z_to_bv 64 (Z.of_nat jp') -> w3 = Z_to_bv 64 (Z.of_nat k') ->
    (c' <= jp')%nat -> (1 <= k' <= p')%nat -> (p' <= length x)%nat -> (jp' + k' <= length x)%nat ->
    ((jp' + k' < length x)%nat -> (2 * length x - (c' + jp') < a)%nat \/
                                   (2 * length x - (c' + jp') = a /\ length x - k' < b)%nat) ->
    (forall (c'' p'' : nat) (y2 y3 y4 y5 y6 : word),
        msuf_run Z.gtb (map bv_unsigned x) c' jp' k' p' c'' p'' ->
        evt rsegs Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat c'' - 1)) (Z_to_bv 64 (Z.of_nat p''))
                   y2 y3 y4 y5 y6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x93518) fc None m (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 z4 z5 z6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x932ac) fc None m (seg_rom rsegs))).
  { intros c' jp' k' p' w0 w1 w2 w3 z4 z5 z6 -> -> -> -> Hc' Hk' Hp' Hl' HM K'.
    step. step. if_cases KX; zify_cond KX; rewrite ?Z.mod_small in KX by lia; cbv iota.
    - apply K'. apply msr_stop. rewrite length_map. lia.
    - replace (Z_to_bv 64 (Z.of_nat k' + Z.of_nat jp')) with (Z_to_bv 64 (Z.of_nat (jp' + k'))) by (f_equal; lia).
      destruct (HM ltac:(lia)) as [LT | [EQ LT]].
      + eapply (IHa _ LT _ c' jp' k' p' z5 z6 eq_refl eq_refl); [lia | lia | lia | lia | exact K'].
      + eapply (IHb _ LT c' jp' k' p' z5 z6 EQ eq_refl); [lia | lia | lia | lia | exact K']. }
  destruct (tw_nth_ex x (c + k - 1) ltac:(lia)) as [b1 E1].
  destruct (tw_nth_ex x (jp + k) ltac:(lia)) as [b2 E2].
  assert (R1 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned s0 + (Z.of_nat c - 1) + Z.of_nat k)) 1 = Some [b1]).
  { apply (sb_rd1 rsegs m (bv_unsigned s0) _ (c + k - 1) b1 _ HX);
      [rewrite nth_error_app1 by lia; exact E1 | rewrite unsigned_lit by lia; lia]. }
  assert (R2 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned s0 + Z.of_nat (jp + k))) 1 = Some [b2]).
  { apply (sb_rd1 rsegs m (bv_unsigned s0) _ (jp + k) b2 _ HX);
      [rewrite nth_error_app1 by lia; exact E2 | rewrite unsigned_lit by lia; lia]. }
  pose proof (tw_at_u x _ _ E1) as A1. pose proof (tw_at_u x _ _ E2) as A2.
  pose proof (sb_byte_range b1) as B1. pose proof (sb_byte_range b2) as B2.
  step. step. step. step. step. step.
  if_cases K1; zify_cond K1; rewrite ?sb_u_zxb, ?sb_u_byte, ?Z.mod_small in K1 by lia; cbv iota.
  - step. if_cases K2; zify_cond K2; rewrite ?sb_u_zxb, ?sb_u_byte, ?Z.mod_small in K2 by lia; cbv iota.
    + step. step. step. step.
      eapply (BACK (jp + 1) (jp + 1) 1 1)%nat; try tw_side.
      intros c'' p'' y2 y3 y4 y5' y6' H. apply K.
      eapply msr_lt; [rewrite length_map; lia | rewrite A1, A2; lia | | exact H].
      rewrite A1, A2, Z.gtb_ltb. apply Z.ltb_ge. lia.
    + step. step. step. step.
      eapply (BACK c (jp + k) 1 (jp + k + 1 - c))%nat; try tw_side.
      intros c'' p'' y2 y3 y4 y5' y6' H. apply K.
      eapply msr_gt; [rewrite length_map; lia | rewrite A1, A2; lia | | exact H].
      rewrite A1, A2, Z.gtb_ltb. apply Z.ltb_lt. lia.
  - step. if_cases K3; zify_cond K3; rewrite ?Z.mod_small in K3 by lia; cbv iota.
    + step. step.
      eapply (BACK c jp (k + 1) p)%nat; try tw_side.
      intros c'' p'' y2 y3 y4 y5' y6' H. apply K.
      eapply msr_eq_k; [rewrite length_map; lia | rewrite A1, A2; lia | lia | exact H].
    + step. step. step.
      eapply (BACK c (jp + p) 1 p)%nat; try tw_side.
      intros c'' p'' y2 y3 y4 y5' y6' H. apply K.
      eapply msr_eq_p; [rewrite length_map; lia | rewrite A1, A2; lia | lia | exact H].
Qed.

Theorem msuf2_ok : MSUF2_OK.
Proof.
  unfold MSUF2_OK.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 F fc m x c0 jp0 k0 p0
         HX L Hc0 Hk0 Hp0 Hl0 K0.
  pose proof (bytes_at_bound _ _ _ _ HX) as BX. rewrite length_app in BX. cbn [length] in BX.
  enough (MAIN : forall (a b c jp k p : nat) (y5 y6 : word),
    (2 * length x - (c + jp) = a)%nat -> (length x - k = b)%nat ->
    (c <= jp)%nat -> (1 <= k <= p)%nat -> (p <= length x)%nat -> (jp + k < length x)%nat ->
    (forall (c' p' : nat) (y2 y3 y4 y5 y6 : word),
        msuf_run Z.ltb (map bv_unsigned x) c jp k p c' p' ->
        evt rsegs Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 y2 y3 y4 y5 y6 a7
                   s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (Z.of_nat c' - 1)) (Z_to_bv 64 (Z.of_nat p')) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x93308) fc None m (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1
               (Z_to_bv 64 (Z.of_nat jp)) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (Z.of_nat (jp + k))) y5 y6 a7
               s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (Z.of_nat c - 1)) (Z_to_bv 64 (Z.of_nat p)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x93548) fc None m (seg_rom rsegs))).
  { exact (MAIN _ _ c0 jp0 k0 p0 a5 a6 eq_refl eq_refl Hc0 Hk0 Hp0 Hl0 K0). }
  clear K0 Hc0 Hk0 Hp0 Hl0.
  induction a as [a IHa] using lt_wf_ind.
  induction b as [b IHb] using lt_wf_ind.
  intros c jp k p y5 y6 Ha Hb Hc Hk Hp Hl K.
  assert (BACK : forall (c' jp' k' p' : nat) (w8 w9 w2 w3 z4 z5 z6 : word),
    w8 = Z_to_bv 64 (Z.of_nat c' - 1) -> w9 = Z_to_bv 64 (Z.of_nat p') ->
    w2 = Z_to_bv 64 (Z.of_nat jp') -> w3 = Z_to_bv 64 (Z.of_nat k') ->
    (c' <= jp')%nat -> (1 <= k' <= p')%nat -> (p' <= length x)%nat -> (jp' + k' <= length x)%nat ->
    ((jp' + k' < length x)%nat -> (2 * length x - (c' + jp') < a)%nat \/
                                   (2 * length x - (c' + jp') = a /\ length x - k' < b)%nat) ->
    (forall (c'' p'' : nat) (y2 y3 y4 y5 y6 : word),
        msuf_run Z.ltb (map bv_unsigned x) c' jp' k' p' c'' p'' ->
        evt rsegs Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 y2 y3 y4 y5 y6 a7
                   s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (Z.of_nat c'' - 1)) (Z_to_bv 64 (Z.of_nat p'')) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x93308) fc None m (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 w2 w3 z4 z5 z6 a7
               s2 s3 s4 s5 s6 s7 w8 w9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x93540) fc None m (seg_rom rsegs))).
  { intros c' jp' k' p' w8 w9 w2 w3 z4 z5 z6 -> -> -> -> Hc' Hk' Hp' Hl' HM K'.
    step. step. if_cases KX; zify_cond KX; rewrite ?Z.mod_small in KX by lia; cbv iota.
    - apply K'. apply msr_stop. rewrite length_map. lia.
    - replace (Z_to_bv 64 (Z.of_nat k' + Z.of_nat jp')) with (Z_to_bv 64 (Z.of_nat (jp' + k'))) by (f_equal; lia).
      destruct (HM ltac:(lia)) as [LT | [EQ LT]].
      + eapply (IHa _ LT _ c' jp' k' p' z5 z6 eq_refl eq_refl); [lia | lia | lia | lia | exact K'].
      + eapply (IHb _ LT c' jp' k' p' z5 z6 EQ eq_refl); [lia | lia | lia | lia | exact K']. }
  destruct (tw_nth_ex x (c + k - 1) ltac:(lia)) as [b1 E1].
  destruct (tw_nth_ex x (jp + k) ltac:(lia)) as [b2 E2].
  assert (R1 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned s0 + (Z.of_nat c - 1) + Z.of_nat k)) 1 = Some [b1]).
  { apply (sb_rd1 rsegs m (bv_unsigned s0) _ (c + k - 1) b1 _ HX);
      [rewrite nth_error_app1 by lia; exact E1 | rewrite unsigned_lit by lia; lia]. }
  assert (R2 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned s0 + Z.of_nat (jp + k))) 1 = Some [b2]).
  { apply (sb_rd1 rsegs m (bv_unsigned s0) _ (jp + k) b2 _ HX);
      [rewrite nth_error_app1 by lia; exact E2 | rewrite unsigned_lit by lia; lia]. }
  pose proof (tw_at_u x _ _ E1) as A1. pose proof (tw_at_u x _ _ E2) as A2.
  pose proof (sb_byte_range b1) as B1. pose proof (sb_byte_range b2) as B2.
  step. step. step. step. step. step.
  if_cases K1; zify_cond K1; rewrite ?sb_u_zxb, ?sb_u_byte, ?Z.mod_small in K1 by lia; cbv iota.
  - step. if_cases K2; zify_cond K2; rewrite ?sb_u_zxb, ?sb_u_byte, ?Z.mod_small in K2 by lia; cbv iota.
    + step. step. step. step.
      eapply (BACK (jp + 1) (jp + 1) 1 1)%nat; try tw_side.
      intros c'' p'' y2 y3 y4 y5' y6' H. apply K.
      eapply msr_lt; [rewrite length_map; lia | rewrite A1, A2; lia | | exact H].
      rewrite A1, A2. apply Z.ltb_ge. lia.
    + step. step. step. step.
      eapply (BACK c (jp + k) 1 (jp + k + 1 - c))%nat; try tw_side.
      intros c'' p'' y2 y3 y4 y5' y6' H. apply K.
      eapply msr_gt; [rewrite length_map; lia | rewrite A1, A2; lia | | exact H].
      rewrite A1, A2. apply Z.ltb_lt. lia.
  - step. if_cases K3; zify_cond K3; rewrite ?Z.mod_small in K3 by lia; cbv iota.
    + step. step.
      eapply (BACK c jp (k + 1) p)%nat; try tw_side.
      intros c'' p'' y2 y3 y4 y5' y6' H. apply K.
      eapply msr_eq_k; [rewrite length_map; lia | rewrite A1, A2; lia | lia | exact H].
    + step. step. step.
      eapply (BACK c (jp + p) 1 p)%nat; try tw_side.
      intros c'' p'' y2 y3 y4 y5' y6' H. apply K.
      eapply msr_eq_p; [rewrite length_map; lia | rewrite A1, A2; lia | lia | exact H].
Qed.
