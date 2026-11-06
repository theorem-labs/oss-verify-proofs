From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Img0 EgressFrame.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import want_width_c.
Import ListNotations.
Open Scope Z_scope.

Lemma ww_firstn1_skipn : forall (bs : list byte) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
Proof. induction bs as [|b bs IH]; intros [|k] d H; cbn in *; try lia; auto. apply IH; lia. Qed.

Lemma ww_zxb_unsigned : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  apply unsigned_lit. cbn in R |- *. lia.
Qed.

Lemma w_width_pos : forall n, 0 <= w_width_model n -> 124 <= n.
Proof.
  intros n. unfold w_width_model.
  destruct ((n - 52) mod 72 =? 0); destruct (124 <=? n) eqn:B; destruct (n <=? 1492); cbn [andb];
  destruct ((n - 54) mod 72 =? 0); destruct (126 <=? n) eqn:E; destruct (n <=? 1494); cbn [andb];
  rewrite ?Z.leb_le, ?Z.leb_gt in *; try lia.
Qed.

Lemma ww_land_top0 : forall r, 0 <= r < 2^63 -> Z.land r (2^63) = 0.
Proof.
  intros r Hr. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia. rewrite Z.bits_0.
  destruct (Z.eqb_spec 63 i) as [<-|Ne]; [|apply andb_false_r].
  rewrite andb_true_r. pose proof (Z.testbit_spec' r 63 ltac:(lia)) as T.
  rewrite Z.div_small in T by lia. destruct (Z.testbit r 63); cbn in T; [discriminate|reflexivity].
Qed.

Lemma ww_lxor_sign : forall x, -2^63 <= x < 2^63 -> Z.lxor (bv_unsigned (Z_to_bv 64 x)) (2^63) = x + 2^63.
Proof.
  intros x Hx. destruct (Z.le_gt_cases 0 x) as [P|N].
  - rewrite unsigned_lit by lia. rewrite <- Z.add_nocarry_lxor; [reflexivity|]. apply ww_land_top0. lia.
  - assert (E : bv_unsigned (Z_to_bv 64 x) = (x + 2^63) + 2^63).
    { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
      replace x with ((x + 2^64) + (-1) * 2^64) at 1 by ring. rewrite Z.mod_add by lia.
      rewrite Z.mod_small by lia. ring. }
    rewrite E. rewrite Z.add_nocarry_lxor by (apply ww_land_top0; lia).
    rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity.
Qed.

Lemma ww_slt : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  v_slt (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.b2z (x <? y)).
Proof.
  intros x y Hx Hy. rewrite v_slt_b2z, !ww_lxor_sign by lia.
  destruct (Z.ltb_spec (x + 2^63) (y + 2^63)); destruct (Z.ltb_spec x y); try reflexivity; lia.
Qed.

Lemma ww_slti0 : forall x, -2^63 <= x < 2^63 -> v_slti (Z_to_bv 64 x) 0 = Z_to_bv 64 (Z.b2z (x <? 0)).
Proof.
  intros x Hx. rewrite v_slti_b2z, ww_lxor_sign by lia.
  destruct (Z.ltb_spec (x + 2^63) (0 + 2^63)); destruct (Z.ltb_spec x 0); try reflexivity; lia.
Qed.

Lemma ww_sltu0 : forall b : byte, v_sltu (Z_to_bv 64 0) (zxb b) = Z_to_bv 64 (Z.b2z (0 <? bv_unsigned b)).
Proof.
  intros b. rewrite v_sltu_b2z. unfold zxb. rewrite ww_zxb_unsigned. reflexivity.
Qed.

Ltac ww_nch_cases nch Hn :=
  assert (Hc : nch = 2 \/ nch = 3 \/ nch = 4 \/ nch = 5 \/ nch = 6 \/ nch = 7 \/ nch = 8 \/ nch = 9 \/ nch = 10 \/
               nch = 11 \/ nch = 12 \/ nch = 13 \/ nch = 14 \/ nch = 15 \/ nch = 16 \/ nch = 17 \/ nch = 18 \/
               nch = 19 \/ nch = 20 \/ nch = 21 \/ nch = 22 \/ nch = 23 \/ nch = 24 \/ nch = 25 \/ nch = 26 \/
               nch = 27 \/ nch = 28 \/ nch = 29 \/ nch = 30 \/ nch = 31 \/ nch = 32 \/ nch = 33 \/ nch = 34 \/
               nch = 35 \/ nch = 36 \/ nch = 37 \/ nch = 38 \/ nch = 39 \/ nch = 40) by lia;
  repeat destruct Hc as [Hc|Hc]; subst nch.

(* The value want_width leaves in a0 at its return, from the three test bits. *)
Definition ww_val (P Q R nch : Z) : word :=
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned
    (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lxor P 1))) Q))) R))))))
    (bv_unsigned (Z_to_bv 64 nch))).

Lemma ww_val_ok : forall c1 c2 c3 nch, 2 <= nch <= 40 ->
  ww_val (bv_unsigned (Z_to_bv 64 (Z.b2z c1))) (bv_unsigned (Z_to_bv 64 (Z.b2z c2))) (bv_unsigned (Z_to_bv 64 (Z.b2z c3))) nch
  = Z_to_bv 64 (if c1 && negb c2 && negb c3 then nch else -1).
Proof. intros [] [] [] nch Hn; ww_nch_cases nch Hn; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma ww_val_ok1 : forall c1 c2 nch, 2 <= nch <= 40 ->
  ww_val (bv_unsigned (Z_to_bv 64 (Z.b2z c1))) (bv_unsigned (Z_to_bv 64 (Z.b2z c2))) 1 nch = Z_to_bv 64 (-1).
Proof. intros [] [] nch Hn; ww_nch_cases nch Hn; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma ww_mod_eq : forall x d, -2^64 + 3 <= x < 2^64 -> 0 <= d <= 2 -> x mod 2^64 = d -> x = d.
Proof.
  intros x d Hx Hd H. destruct (Z.le_gt_cases 0 x).
  - rewrite Z.mod_small in H by lia. lia.
  - replace x with ((x + 2^64) + (-1) * 2^64) in H by ring. rewrite Z.mod_add, Z.mod_small in H by lia. lia.
Qed.

Lemma ww_mod_ne : forall x d, 0 <= d < 2^64 -> x mod 2^64 <> d -> x <> d.
Proof. intros x d Hd H E. subst. rewrite Z.mod_small in H by lia. exact (H eq_refl). Qed.

Ltac ww_bools :=
  repeat match goal with |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E end;
  repeat match goal with
   | E : (_ && _) = true |- _ => apply andb_true_iff in E; destruct E
   | E : (_ && _) = false |- _ => apply andb_false_iff in E; destruct E
   | E : (_ =? _) = true |- _ => apply Z.eqb_eq in E
   | E : (_ =? _) = false |- _ => apply Z.eqb_neq in E
   | E : (_ <=? _) = true |- _ => apply Z.leb_le in E
   | E : (_ <=? _) = false |- _ => apply Z.leb_gt in E
   end.

Lemma w_width_fix : forall n c, (n = 124 + 36 * (c - 2) \/ n = 126 + 36 * (c - 2)) -> 2 <= c <= 40 -> Z.even c = true ->
  w_width_model n = c.
Proof.
  intros n c Hn Hc He. apply Zeven_bool_iff, Zeven_ex in He. destruct He as [j ->].
  unfold w_width_model. ww_bools; Z.div_mod_to_equations; lia.
Qed.

Lemma w_width_none : forall n, (forall j, 0 <= j < 20 -> n <> 124 + 72 * j /\ n <> 126 + 72 * j) -> w_width_model n = -1.
Proof.
  intros n H. unfold w_width_model. ww_bools; try reflexivity; exfalso.
  all: first
    [ assert (Eq : n - 52 = 72 * ((n - 52) / 72)) by (rewrite (Z_div_mod_eq_full (n - 52) 72) at 1; lia);
      destruct (H ((n - 52) / 72 - 1)) as [Hq _]; [lia|]; lia
    | assert (Eq : n - 54 = 72 * ((n - 54) / 72)) by (rewrite (Z_div_mod_eq_full (n - 54) 72) at 1; lia);
      destruct (H ((n - 54) / 72 - 1)) as [_ Hq]; [lia|]; lia ].
Qed.

Section WW.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (slot : Z).
Hypothesis HB : bytes_at rsegs m (bv_unsigned a0) bs.
Hypothesis HL : length bs = Z.to_nat (bv_unsigned a1).
Hypothesis Hs : -2^31 <= slot < 2^31.

Notation POST := (fun ms' => exists (a1' a2' a3' a4' a5' a6' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (want_width_model (bv_unsigned a1) bs slot))
                       a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs)).

Lemma ww_found : forall (x11 x12 x13 x14 x15 x16 : word) (nch : Z),
  x11 = Z_to_bv 64 nch -> x12 = Z_to_bv 64 slot -> 2 <= nch <= 40 -> w_width_model (bv_unsigned a1) = nch ->
  evt rsegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13220) fc None m (seg_rom rsegs)).
Proof.
  intros x11 x12 x13 x14 x15 x16 nch -> -> Hn HW.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. change (bv_modulus 64) with (2^64) in Ra1.
  assert (Hn1 : 124 <= bv_unsigned a1) by (apply w_width_pos; lia).
  set (b16 := nth 16 bs (Z_to_bv 8 1)). set (b17 := nth 17 bs (Z_to_bv 8 1)).
  assert (RB16 : ov_read_bytes rsegs m (wa (bv_unsigned a0 + 16)) 1 = Some [b16]).
  { rewrite (bytes_at_read rsegs m _ bs 16 1 HB) by lia. f_equal. apply ww_firstn1_skipn. lia. }
  assert (RB17 : ov_read_bytes rsegs m (wa (bv_unsigned a0 + 17)) 1 = Some [b17]).
  { rewrite (bytes_at_read rsegs m _ bs 17 1 HB) by lia. f_equal. apply ww_firstn1_skipn. lia. }
  step. step.
  assert (Hww : want_width_model (bv_unsigned a1) bs slot =
                if (slot <? nch) && negb (slot <? 0) && negb (negb (frame_is_audio bs)) then nch else -1).
  { unfold want_width_model. rewrite HW. rewrite (proj2 (Z.ltb_ge nch 0)) by lia.
    destruct (Z.ltb_spec slot nch); destruct (Z.ltb_spec slot 0); destruct (Z.leb_spec nch slot);
      destruct (frame_is_audio bs); cbn; try reflexivity; lia. }
  if_cases H16; zify_cond H16; rewrite ?ww_zxb_unsigned in H16.
  - do 2 step. do 8 step.
    rewrite ww_slt, ww_slti0, ww_sltu0 by lia.
    match goal with |- context [Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64
        (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lxor ?P 1))) ?Q))) ?R))))))
        (bv_unsigned (Z_to_bv 64 nch)))] =>
      change (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64
        (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lxor P 1))) Q))) R))))))
        (bv_unsigned (Z_to_bv 64 nch)))) with (ww_val P Q R nch)
    end.
    rewrite ww_val_ok by lia.
    replace (if (slot <? nch) && negb (slot <? 0) && negb (0 <? bv_unsigned b17) then nch else -1)
      with (want_width_model (bv_unsigned a1) bs slot).
    + apply evt_done. do 6 eexists. reflexivity.
    + rewrite Hww. unfold frame_is_audio. fold b16 b17. rewrite (proj2 (Z.eqb_eq (bv_unsigned b16) 0)) by lia.
      pose proof (bv_unsigned_in_range 8 b17) as R17. unfold bv_modulus in R17.
      destruct (Z.eqb_spec (bv_unsigned b17) 0); destruct (Z.ltb_spec 0 (bv_unsigned b17)); cbn [andb negb];
        try reflexivity; lia.
  - do 2 step. do 8 step.
    rewrite ww_slt, ww_slti0 by lia.
    match goal with |- context [Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64
        (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lxor ?P 1))) ?Q))) 1))))))
        (bv_unsigned (Z_to_bv 64 nch)))] =>
      change (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64
        (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lxor P 1))) Q))) 1))))))
        (bv_unsigned (Z_to_bv 64 nch)))) with (ww_val P Q 1 nch)
    end.
    rewrite ww_val_ok1 by lia.
    replace (-1) with (want_width_model (bv_unsigned a1) bs slot).
    + apply evt_done. do 6 eexists. reflexivity.
    + rewrite Hww. unfold frame_is_audio. fold b16 b17. rewrite (proj2 (Z.eqb_neq (bv_unsigned b16) 0)) by lia.
      cbn [andb negb]. rewrite !andb_false_r. reflexivity.
Qed.


Ltac ww_even := first [ reflexivity | match goal with |- Z.even (2 + 2 * ?k) = true =>
  replace (2 + 2 * k) with (2 * (k + 1)) by ring; rewrite Z.even_mul; reflexivity end ].

Ltac ww_body :=
  step;
  let HA := fresh "HA" in
  if_cases HA; zify_cond HA;
  [ apply ww_mod_eq in HA; [| lia | lia];
    eapply ww_found; [reflexivity | reflexivity | lia | apply w_width_fix; [lia | lia | ww_even]]
  | apply ww_mod_ne in HA; [| lia];
    step;
    let HB := fresh "HB" in
    if_cases HB; zify_cond HB;
    [ apply ww_mod_eq in HB; [| lia | lia];
      eapply ww_found; [reflexivity | reflexivity | lia | apply w_width_fix; [lia | lia | ww_even]]
    | apply ww_mod_ne in HB; [| lia];
      do 4 step ] ].

Definition ww_inv (n k : Z) : Prop := forall j, 0 <= j < k -> n <> 124 + 72 * j /\ n <> 126 + 72 * j.

Lemma ww_loop : forall (i : nat) (k : Z) (x11 x13 x14 x15 x16 : word),
  k = 19 - Z.of_nat i -> 0 <= k -> ww_inv (bv_unsigned a1) k ->
  x11 = Z_to_bv 64 (2 + 2 * k) -> x13 = Z_to_bv 64 (2 * k) -> x14 = Z_to_bv 64 2 -> x15 = Z_to_bv 64 38 ->
  x16 = Z_to_bv 64 (126 - bv_unsigned a1 + 72 * k) ->
  evt rsegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 (Z_to_bv 64 slot) x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13200) fc None m (seg_rom rsegs)).
Proof.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. change (bv_modulus 64) with (2^64) in Ra1.
  induction i as [|i IH]; intros k x11 x13 x14 x15 x16 Ek Hk HI -> -> -> -> ->.
  - cbn [Z.of_nat] in Ek. replace k with 19 in * by lia. clear Ek Hk.
    ww_body.
    if_false. step. step.
    assert (HN : w_width_model (bv_unsigned a1) = -1).
    { apply w_width_none. intros j Hj. destruct (Z.eq_dec j 19) as [->|Nj]; [lia|]. apply HI. lia. }
    assert (HM : want_width_model (bv_unsigned a1) bs slot = -1).
    { unfold want_width_model. rewrite HN. reflexivity. }
    rewrite HM. apply evt_done. do 6 eexists. reflexivity.
  - ww_body.
    let HC := fresh "HC" in
    if_cases HC; zify_cond HC; [| exfalso; rewrite ?Z.mod_small in HC by lia; lia].
    eapply (IH (k + 1)).
    all: try (match goal with |- ww_inv _ _ => intros j Hj; destruct (Z.eq_dec j k) as [->|Nj]; [lia|]; apply HI; lia end).
    all: try lia.
    all: first [ reflexivity | (f_equal; lia)
               | (f_equal; rewrite unsigned_lit by lia; rewrite bv_swrap_small; [lia | change (bv_half_modulus 32) with (2^31); lia]) ].
Qed.

Lemma ww_main :
  evt rsegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 slot) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WANT_WIDTH) fc None m (seg_rom rsegs)).
Proof.
  unfold WANT_WIDTH. do 6 step.
  eapply (ww_loop 19%nat 0).
  all: try (match goal with |- ww_inv _ _ => intros j Hj; lia end).
  all: try lia.
  all: first [ reflexivity | (f_equal; lia) ].
Qed.

End WW.

Theorem want_width_holds : want_width_contract.
Proof.
  unfold want_width_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs slot
    HB HL -> Hs.
  eapply ww_main; eassumption.
Qed.
