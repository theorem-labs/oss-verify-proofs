From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import check_braid_c.
Import ListNotations.
Open Scope Z_scope.

Lemma land_hi : forall x k, 0 <= x < 2^64 -> 0 <= k <= 64 -> Z.land x (2^64 - 2^k) = 2^k * (x / 2^k).
Proof.
  intros x k Hx Hk.
  assert (E : 2^64 - 2^k = Z.shiftl (Z.ones (64 - k)) k).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.ones_equiv. unfold Z.pred.
    rewrite Z.mul_add_distr_r, <- Z.pow_add_r by lia. replace (64 - k + k) with 64 by lia. lia. }
  rewrite E, (Z.mul_comm (2^k)), <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i k).
  - rewrite (Z.testbit_neg_r (Z.ones (64 - k)) (i - k)), (Z.testbit_neg_r (Z.shiftr x k) (i - k)) by lia.
    apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - k + k) with i by lia.
    destruct (Z.ltb_spec i 64).
    + rewrite Z.ones_spec_low by lia. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
      destruct (Z.eq_dec x 0) as [->|Hnz]; [symmetry; apply Z.bits_0|].
      symmetry. apply Z.bits_above_log2; [lia|].
      apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma land_m2 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551614 = 2 * (x / 2).
Proof. intros x Hx. exact (land_hi x 1 Hx ltac:(lia)). Qed.

Lemma land_m8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = 8 * (x / 8).
Proof. intros x Hx. exact (land_hi x 3 Hx ltac:(lia)). Qed.

Lemma land_1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. exact (Z.land_ones x 1 ltac:(lia)). Qed.

Lemma rd1 : forall m a b, mrd rsegs m (wa a) = Some b -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof. intros m a b H. rewrite ov_rdn, rdn_unfold, H. reflexivity. Qed.

Lemma rdw : forall m (w : word) k a b, mrd rsegs m (wa a) = Some b -> bv_unsigned w + k = a ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned w + k)) 1 = Some [b].
Proof. intros m w k a b H E. rewrite E. apply rd1. exact H. Qed.

Lemma rdw0 : forall m (w : word) a b, mrd rsegs m (wa a) = Some b -> bv_unsigned w = a ->
  ov_read_bytes rsegs m w 1 = Some [b].
Proof. intros m w a b H E. rewrite <- (Z_to_bv_bv_unsigned w), E. apply rd1. exact H. Qed.

Lemma braid_transport : forall m m' audio pcm nch ns lo hi,
  1 <= nch <= 127 -> 1 <= ns <= 127 -> 0 <= audio < 2^63 -> 0 <= pcm < 2^63 ->
  munch [(lo, hi)] m m' ->
  audio + 3 * nch * ns + 3 <= lo \/ hi <= audio ->
  pcm + 3 * nch * ns <= lo \/ hi <= pcm ->
  braid_map m audio pcm nch ns -> braid_map m' audio pcm nch ns.
Proof.
  intros m m' audio pcm nch ns lo hi HN HS HA HP MU DA DP BR ch s j Hch Hs Hj.
  destruct (BR ch s j Hch Hs Hj) as (b & H1 & H2). exists b.
  assert (NN : nch * ns <= 16129) by nia.
  assert (I1 : 0 <= ch * ns + s <= nch * ns - 1) by nia.
  assert (I2 : 0 <= s * nch + 2 * (ch / 2) <= nch * ns - 1).
  { pose proof (Z.mul_div_le ch 2 ltac:(lia)). pose proof (Z.div_pos ch 2 ltac:(lia) ltac:(lia)). nia. }
  assert (O : 0 <= braid_off ch j <= 5)
    by (unfold braid_off; destruct (Z.even ch); destruct (j =? 0); destruct (j =? 1); lia).
  unfold mrd in *. rewrite !MU; [split; assumption | | ].
  all: rewrite wa_unsigned by lia; cbn [outside]; split; [lia | exact I].
Qed.

Ltac rng := lia.
Ltac wsub := repeat match goal with H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H end.
Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by rng end.
Ltac shn := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; zb_fold_lits.
Ltac lnd := repeat match goal with
  | |- context [Z.land ?x 18446744073709551614] => rewrite (land_m2 x) by rng
  | |- context [Z.land ?x 18446744073709551608] => rewrite (land_m8 x) by rng
  | |- context [Z.land ?x 1] => rewrite (land_1 x)
  end.
Ltac norm := wsub; do 3 (shn; usub; lnd).
Ltac fact := rewrite ?v_sltu_b2z, ?Z.lxor_nilpotent; norm; first [ reflexivity | rng | (vm_compute; reflexivity) ].
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?zb_signed; norm;
  do 3 (decide_tests; cbv beta iota); reflexivity.
Ltac take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.

Section Loops.
Variables (ra sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (audio pcm nch ns : Z) (t0 t1 a7 : word).
Hypothesis HN : 1 <= nch <= 127.
Hypothesis HS : 1 <= ns <= 127.
Hypothesis HA : 0 <= audio < 2^63.
Hypothesis HP : 0 <= pcm < 2^63.
Hypothesis BR : braid_map m audio pcm nch ns.
Hypothesis Ht0 : bv_unsigned t0 = 3 * ns.
Hypothesis Ht1 : bv_unsigned t1 = 3 * ns + 1.
Hypothesis Ha7 : bv_unsigned a7 = 3 * nch.
Variable Q : machine_state -> Prop.

Local Notation ST pc t2 s0 s1 a4 a5 a6 t3 t4 t5 t6 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 audio) (Z_to_bv 64 pcm) (Z_to_bv 64 nch) (Z_to_bv 64 ns)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma body : forall ch s (a5 a6 t2 s0 s1 a4 t3 t4 t5 t6 : word),
  0 <= ch < nch -> 0 <= s < ns ->
  bv_unsigned a4 = 0 ->
  bv_unsigned t3 = audio + 3 * (2 * (ch / 2)) + 3 * nch * s ->
  bv_unsigned t4 = ch mod 2 ->
  bv_unsigned t5 = pcm + 1 + 3 * ns * ch + 3 * s ->
  (forall s0' s1' a4' t3' t5' t6' : word, bv_unsigned a4' = 0 ->
     bv_unsigned t3' = audio + 3 * (2 * (ch / 2)) + 3 * nch * (s + 1) ->
     bv_unsigned t5' = pcm + 1 + 3 * ns * ch + 3 * (s + 1) ->
     evt rsegs Q (ST 0x13570 t2 s0' s1' a4' a5 a6 t3' t4 t5' t6')) ->
  evt rsegs Q (ST 0x13508 t2 s0 s1 a4 a5 a6 t3 t4 t5 t6).
Proof.
  intros ch s a5 a6 t2 s0 s1 a4 t3 t4 t5 t6 Hch Hs Ha4 Ht3 Ht4 Ht5 K.
  assert (B1 : 0 <= ns * ch <= 16129) by nia.
  assert (B2 : 0 <= nch * s <= 16129) by nia.
  destruct (BR ch s 0 Hch Hs ltac:(lia)) as (b0 & P0 & A0).
  destruct (BR ch s 1 Hch Hs ltac:(lia)) as (b1 & P1 & A1).
  destruct (BR ch s 2 Hch Hs ltac:(lia)) as (b2 & P2 & A2).
  unfold braid_off in A0, A1, A2.
  pose proof (Zmod_even ch) as Hev.
  destruct (Z.even ch) eqn:E; cbn [Z.eqb Pos.eqb] in A0, A1, A2.
  - pose proof (rdw m t5 (-1) _ _ P0 ltac:(lia)) as R. step. clear R.
    step. take false.
    pose proof (rdw m t3 3 _ _ A0 ltac:(lia)) as R. step. clear R.
    step. take false.
    pose proof (rdw0 m t5 _ _ P1 ltac:(lia)) as R. step. clear R.
    pose proof (rdw0 m t3 _ _ A1 ltac:(lia)) as R. step. clear R.
    step. step. take true.
    pose proof (rdw m t5 1 _ _ P2 ltac:(lia)) as R. step. clear R.
    step.
    pose proof (rdw m t3 1 _ _ A2 ltac:(lia)) as R. step. clear R.
    do 6 step.
    apply K; fact.
  - pose proof (rdw m t5 (-1) _ _ P0 ltac:(lia)) as R. step. clear R.
    step. take true.
    pose proof (rdw m t3 4 _ _ A0 ltac:(lia)) as R. step. clear R.
    step. step. take false.
    pose proof (rdw0 m t5 _ _ P1 ltac:(lia)) as R. step. clear R.
    pose proof (rdw m t3 5 _ _ A1 ltac:(lia)) as R. step. clear R.
    step. take false.
    step.
    pose proof (rdw m t5 1 _ _ P2 ltac:(lia)) as R. step. clear R.
    step.
    pose proof (rdw m t3 2 _ _ A2 ltac:(lia)) as R. step. clear R.
    do 6 step.
    apply K; fact.
Qed.

Lemma inner_loop : forall ch (a5 a6 t2 : word),
  0 <= ch < nch -> bv_unsigned a5 = ch -> bv_unsigned a6 = pcm + 1 + 3 * ns * ch ->
  bv_unsigned t2 = pcm + 3 * ns * ch + 3 * ns + 1 ->
  (forall t2' s0 s1 a4 t3 t4 t5 t6 : word, bv_unsigned a4 = 0 ->
     evt rsegs Q (ST 0x13574 t2' s0 s1 a4 a5 a6 t3 t4 t5 t6)) ->
  forall n s (s0 s1 a4 t3 t4 t5 t6 : word),
  0 <= s -> s + Z.of_nat (S n) = ns ->
  bv_unsigned a4 = 0 ->
  bv_unsigned t3 = audio + 3 * (2 * (ch / 2)) + 3 * nch * s ->
  bv_unsigned t4 = ch mod 2 ->
  bv_unsigned t5 = pcm + 1 + 3 * ns * ch + 3 * s ->
  evt rsegs Q (ST 0x13508 t2 s0 s1 a4 a5 a6 t3 t4 t5 t6).
Proof.
  intros ch a5 a6 t2 Hch Ha5 Ha6 Ht2 K n.
  assert (B1 : 0 <= ns * ch <= 16129) by nia.
  induction n as [|n IH]; intros s s0 s1 a4 t3 t4 t5 t6 Hs0 Hsn Ha4 Ht3 Ht4 Ht5.
  - apply (body ch s a5 a6 t2 s0 s1 a4 t3 t4 t5 t6); try assumption; [lia|].
    intros s0' s1' a4' t3' t5' t6' Ha4' Ht3' Ht5'.
    step. take false. apply K. exact Ha4'.
  - apply (body ch s a5 a6 t2 s0 s1 a4 t3 t4 t5 t6); try assumption; [lia|].
    intros s0' s1' a4' t3' t5' t6' Ha4' Ht3' Ht5'.
    step. take true. apply (IH (s + 1)); try assumption; lia.
Qed.

Lemma outer_loop :
  (forall t2 s0 s1 a4 a5 a6 t3 t4 t5 t6 : word, bv_unsigned a4 = 0 ->
     evt rsegs Q (ST 0x13580 t2 s0 s1 a4 a5 a6 t3 t4 t5 t6)) ->
  forall k ch (t2 s0 s1 a4 a5 a6 t3 t4 t5 t6 : word),
  0 <= ch -> ch + Z.of_nat (S k) = nch ->
  bv_unsigned a4 = 0 -> bv_unsigned a5 = ch -> bv_unsigned a6 = pcm + 1 + 3 * ns * ch ->
  evt rsegs Q (ST 0x134dc t2 s0 s1 a4 a5 a6 t3 t4 t5 t6).
Proof.
  intros K k. induction k as [|k IH]; intros ch t2 s0 s1 a4 a5 a6 t3 t4 t5 t6 Hc0 Hck Ha4 Ha5 Ha6.
  all: assert (Hch : 0 <= ch < nch) by lia.
  all: assert (B1 : 0 <= ns * ch <= 16129) by nia.
  all: step; take false.
  all: do 10 step.
  all: eapply (inner_loop ch) with (n := Z.to_nat (ns - 1)) (s := 0);
         [ exact Hch | fact | fact | fact | | lia | lia | fact | fact | fact | fact ].
  - intros t2' s0' s1' a4' t3' t4' t5' t6' Ha4'.
    do 3 step. take false. apply K. exact Ha4'.
  - intros t2' s0' s1' a4' t3' t4' t5' t6' Ha4'.
    do 3 step. take true. apply (IH (ch + 1)); [lia | lia | exact Ha4' | fact | fact].
Qed.

End Loops.

Theorem check_braid_holds : check_braid_contract.
Proof.
  unfold check_braid_contract, CHECK_BRAID, CHECK_BRAID_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m audio pcm nch ns lo
    HN HS HA HP BR ST HLO DA DP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  do 4 step.
  match goal with MU' : munch _ m ?m1 |- _ =>
    assert (BR1 : braid_map m1 audio pcm nch ns)
      by exact (braid_transport m m1 audio pcm nch ns (bv_unsigned sp + -32) (bv_unsigned sp) HN HS HA HP MU' DA DP BR)
  end.
  step; take false.
  do 12 step.
  eapply outer_loop with (k := Z.to_nat (nch - 1)) (ch := 0).
  all: lazymatch goal with
       | |- forall _ : word, _ => idtac
       | _ => first [ assumption | fact | lia ]
       end.
  intros t2' s0' s1' a4' a5' a6' t3' t4' t5' t6' Ha4'.
  step; take false.
  do 5 step.
  apply evt_done. do 16 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
  release_frame FR ST (bv_unsigned sp). exact ST.
Qed.
