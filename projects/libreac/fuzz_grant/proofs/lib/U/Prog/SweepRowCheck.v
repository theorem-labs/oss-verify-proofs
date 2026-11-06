From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel GrantSweepModel SlotNeeds_c LLVMFuzzerTestOneInput_c GrantSlotPlan SlotBridge SegCLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Spec Require Import StrFun.
Import ListNotations.
Open Scope Z_scope.

Definition bsum (bs : list byte) : Z := fold_right Z.add 0 (map bv_unsigned bs).

Lemma land_m1_l : forall x, 0 <= x < 2 ^ 64 -> Z.land 18446744073709551615 x = x.
Proof.
  intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. apply Z.mod_small. exact Hx.
Qed.

Lemma lxor_sign_small : forall x, 0 <= x < 2 ^ 63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x Hx. change 9223372036854775808 with (2 ^ 63). rewrite zb_lxor_sign by lia. apply Z.mod_small. lia.
Qed.

Lemma lxor_sign_small2 : forall x, 0 <= x < 2 ^ 63 -> Z.lxor x (2 ^ 63) = x + 2 ^ 63.
Proof. intros x Hx. rewrite zb_lxor_sign by lia. apply Z.mod_small. lia. Qed.

(* Succeeds when [e] is built from integer literals with [+], [-], [*] and [Z.opp] only. *)
Ltac closedZ e :=
  lazymatch e with
  | Z0 => idtac
  | Zpos ?p => is_Zlit_zb e
  | Zneg ?p => is_Zlit_zb e
  | ?a + ?b => closedZ a; closedZ b
  | ?a - ?b => closedZ a; closedZ b
  | ?a * ?b => closedZ a; closedZ b
  | Z.opp ?a => closedZ a
  end.

(* Replaces each closed [Z_to_bv 64 e] that is not a nonnegative literal by its canonical literal. *)
Ltac canon_lits :=
  repeat match goal with
  | |- context [Z_to_bv 64 ?e] =>
      lazymatch e with
      | Zpos _ => fail
      | Z0 => fail
      | _ => closedZ e
      end;
      let v := eval vm_compute in (e mod 18446744073709551616) in
      is_Zlit_zb v;
      replace (Z_to_bv 64 e) with (Z_to_bv 64 v) by (apply Z_to_bv_eqm; vm_compute; reflexivity)
  end.

(* Decides a branch: by [ifc], else by case analysis where one side contradicts the context. *)
Ltac dbr :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?C then _ else _) _ _ _ _) =>
      first [ ifc
            | (let HC := fresh "HC" in destruct C eqn:HC; zify_cond HC; cbv iota;
               try (exfalso; first [ lia | (Z.div_mod_to_equations; lia) ]); clear HC) ]
  end.

(* Normalizes a [slti]/[sltu] result whose test is decided by the context. *)
Ltac slt_fix :=
  rewrite ?lxor_sign_small by lia; rewrite ?lxor_sign_small2 by lia; decide_tests; cbn [Z.b2z].

Lemma sum_loop : forall bs (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (acc A X c : Z),
  t6 = Z_to_bv 64 acc -> s3 = Z_to_bv 64 X -> s4 = Z_to_bv 64 c -> s5 = Z_to_bv 64 A -> a5 = Z_to_bv 64 32 ->
  bytes_at rsegs m A bs -> bs <> [] -> c = Z.of_nat (length bs) -> c <= 32 -> 2 ^ 63 <= X < 2 ^ 64 ->
  evt rsegs (fun ms' => exists s4' s5' s6', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                         s2 s3 s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5 (Z_to_bv 64 (acc + bsum bs)))
                                    F (Z_to_bv 64 0x136c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x136a8) fc None m (seg_rom rsegs)).
Proof.
  induction bs as [|b bs IH]; intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m acc A X c -> -> -> -> -> HB Hne Hc Hc32 HX; [congruence|].
  pose proof (bytes_at_bound _ _ _ _ HB) as HBd. cbn [length] in HBd, Hc.
  pose proof (bytes_byte_read m A (b :: bs) 0 HB ltac:(cbn; lia)) as R0. cbn [nth Z.of_nat] in R0. rewrite Z.add_0_r in R0.
  zstep. zstep. dbr. zstep. zstep. zstep. zstep. zstep.
  destruct bs as [|b' bs'].
  - cbn [length] in Hc. ifc.
    apply evt_done. do 3 eexists.
    replace (acc + bsum [b]) with (acc + bv_unsigned b) by (unfold bsum; cbn [map fold_right]; lia).
    reflexivity.
  - cbn [length] in Hc, HBd. ifc.
    apply (proj1 (bytes_at_app rsegs m A [b] (b' :: bs'))) in HB. destruct HB as [_ HB]. cbn [length Z.of_nat] in HB.
    eapply evt_mono.
    + refine (IH ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 _ a6 a7 s2 _ _ _ _ s7 s8 s9 s10 s11 t3 t4 t5 _ F fc m
        (acc + bv_unsigned b) (A + 1) X (c + -1) eq_refl eq_refl eq_refl eq_refl eq_refl HB ltac:(congruence)
        ltac:(cbn [length] in *; lia) ltac:(lia) HX).
    + intros ms' (s4' & s5' & s6' & ->). exists s4', s5', s6'.
      replace (acc + bsum (b :: b' :: bs')) with (acc + bv_unsigned b + bsum (b' :: bs')) by (unfold bsum; cbn [map fold_right]; lia).
      reflexivity.
Qed.

Definition rowok (r : list byte) : Prop := length r = 34%nat /\ rf1z (map bv_unsigned r) = true.

Lemma rowok_split : forall r, rowok r ->
  exists rest, r = Z_to_bv 8 205 :: Z_to_bv 8 234 :: Z_to_bv 8 4 :: Z_to_bv 8 3 :: rest /\
    length rest = 30%nat /\ bsum (Z_to_bv 8 4 :: Z_to_bv 8 3 :: rest) mod 256 = 0.
Proof.
  intros r [Hl Hr]. destruct r as [|b0 [|b1 [|b2 [|b3 rest]]]]; cbn [length] in Hl; try lia.
  exists rest. unfold rf1z in Hr. cbn [map] in Hr.
  apply andb_prop in Hr as [Hr H5]. apply andb_prop in Hr as [Hr H4]. apply andb_prop in Hr as [Hr H3].
  apply andb_prop in Hr as [H1 H2]. apply Z.eqb_eq in H1, H2, H3, H4, H5.
  assert (E0 : b0 = Z_to_bv 8 205) by (rewrite <- (Z_to_bv8_unsigned b0), H1; reflexivity).
  assert (E1 : b1 = Z_to_bv 8 234) by (rewrite <- (Z_to_bv8_unsigned b1), H2; reflexivity).
  assert (E2 : b2 = Z_to_bv 8 4) by (rewrite <- (Z_to_bv8_unsigned b2), H3; reflexivity).
  assert (E3 : b3 = Z_to_bv 8 3) by (rewrite <- (Z_to_bv8_unsigned b3), H4; reflexivity).
  subst b0 b1 b2 b3. split; [reflexivity|]. split; [lia|]. exact H5.
Qed.

Lemma land255_sum : forall x, x mod 256 = 0 -> Z.land (x mod 18446744073709551616) 255 = 0.
Proof.
  intros x H. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change 18446744073709551616 with (2 ^ 64).
  rewrite mod_mod8_of_modw by lia. exact H.
Qed.

Lemma bytes_at_eqa : forall m a a' bs, bytes_at rsegs m a bs -> a = a' -> bytes_at rsegs m a' bs.
Proof. intros; subst; assumption. Qed.

Lemma rows_loop : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s k n : Z),
  a0 = Z_to_bv 64 n -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 (s + 34 * k + 2) ->
  a3 = Z_to_bv 64 (-2) -> a4 = Z_to_bv 64 34 -> a5 = Z_to_bv 64 32 -> a6 = Z_to_bv 64 205 -> a7 = Z_to_bv 64 (-1) ->
  t0 = Z_to_bv 64 234 -> t1 = Z_to_bv 64 (-3) -> t2 = Z_to_bv 64 4 -> t3 = Z_to_bv 64 (-4) -> t4 = Z_to_bv 64 3 ->
  t5 = Z_to_bv 64 (s + 34 * k) -> s1 = Z_to_bv 64 s -> s11 = Z_to_bv 64 (18446744073709551615 - s) ->
  0 <= k -> n = k + Z.of_nat (length L) -> L <> [] -> 0 < s -> s + 34 * n < 2 ^ 63 -> n < 2 ^ 31 ->
  bytes_at rsegs m (s + 34 * k) (concat L) -> Forall rowok L ->
  evt rsegs (fun ms' => exists a1' a2' s2' s3' s4' s5' s6' t5' t6',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3 t4 t5' t6')
               F (Z_to_bv 64 0x13708) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1367c) fc None m (seg_rom rsegs)).
Proof.
  induction L as [|r L IH]; intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m s k n -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> Hk Hn Hne Hs Hsn Hn31 HB HF; [congruence|].
  inversion HF as [|r0 L0 Hr HFL]; subst r0 L0. clear HF.
  destruct (rowok_split r Hr) as (rest & -> & Hrl & Hsum).
  cbn [concat] in HB. apply (proj1 (bytes_at_app rsegs m _ _ _)) in HB. destruct HB as [HR HL].
  cbn [length] in Hn, HR, HL. rewrite Hrl in HL.
  pose proof (bytes_at_bound _ _ _ _ HR) as HRb. cbn [length] in HRb. rewrite Hrl in HRb.
  pose proof (proj1 (bytes_at_app rsegs m (s + 34 * k) [Z_to_bv 8 205; Z_to_bv 8 234] (Z_to_bv 8 4 :: Z_to_bv 8 3 :: rest)) HR) as [_ HR2].
  cbn [length Z.of_nat] in HR2.
  pose proof (bytes_byte_read m _ _ 0 HR ltac:(cbn; lia)) as R0.
  pose proof (bytes_byte_read m _ _ 1 HR ltac:(cbn; lia)) as R1.
  pose proof (bytes_byte_read m _ _ 2 HR ltac:(cbn; lia)) as R2.
  pose proof (bytes_byte_read m _ _ 3 HR ltac:(cbn; lia)) as R3.
  cbn [nth Z.of_nat] in R0, R1, R2, R3.
  zstep. zstep. dbr. zstep. zstep. zstep. zstep. zstep.
  decide_tests. cbn [Z.b2z].
  zstep. canon_lits. zstep. rewrite land_m1_l by lia. zstep. zstep.
  eapply evt_cut.
  { eapply sum_loop with (bs := Z_to_bv 8 4 :: Z_to_bv 8 3 :: rest) (acc := 0) (A := s + 34 * k + 2)
      (X := 18446744073709551614 - (s + 34 * k)) (c := 32).
    all: first [ reflexivity | (f_equal; lia) | exact HR2 | congruence | (cbn [length]; lia) | lia | word_eq_tac ]. }
  intros ms' (s4' & s5' & s6' & ->).
  zstep. zstep. dbr. zstep. dbr. zstep. zstep. dbr. zstep. dbr. zstep. zstep. dbr. zstep. dbr.
  zstep. zstep. dbr. zstep.
  rewrite land255_sum by (rewrite Z.add_0_l; exact Hsum).
  zstep. dbr. zstep. rewrite ?swrap32_id by lia. zstep. zstep. zstep.
  destruct L as [|r' L'].
  - cbn [length Z.of_nat] in Hn. subst n. dbr.
    apply evt_done. do 9 eexists. reflexivity.
  - cbn [length] in Hn. dbr.
    eapply IH with (s := s) (k := k + 1) (n := n).
    all: first [ reflexivity | (f_equal; lia) | congruence | lia | (cbn [length] in *; lia) | exact HFL | word_eq_tac | idtac ].
    eapply bytes_at_eqa; [exact HL | lia].
Qed.

Definition ga_rows (base : Z) (vals : list byte) (c : nat) : list (list byte) :=
  [ga_row base vals c 0; ga_row base vals c 1; ga_row base vals c 2].

Definition sweep_rows (base : Z) (w : nat) (vals : list byte) : list (list byte) :=
  HEAD_ACK34 :: ga_rows base vals 0 ++ HEAD_MARK34 :: GB 0 :: GB 1 :: GB 2 :: GB 3 :: GB 4 :: GB 5 ::
  flat_map (ga_rows base vals) (seq 1 (w - 1)).

Lemma concat_chans : forall base vals l,
  concat (map (ga_chan base vals) l) = concat (flat_map (ga_rows base vals) l).
Proof.
  intros base vals l. induction l as [|c l IH]; [reflexivity|].
  cbn [map flat_map concat]. rewrite concat_app, <- IH. unfold ga_chan, ga_rows. cbn [concat]. rewrite app_nil_r. reflexivity.
Qed.

Lemma SWEEP_rows : forall base w vals, SWEEP base w vals = concat (sweep_rows base w vals).
Proof.
  intros base w vals. unfold SWEEP, sweep_rows. rewrite GBall_split, concat_chans.
  unfold ga_chan, ga_rows. cbn [concat app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma length_flat_rows : forall base vals l, length (flat_map (ga_rows base vals) l) = (3 * length l)%nat.
Proof.
  intros base vals l. induction l as [|c l IH]; [reflexivity|].
  change (flat_map (ga_rows base vals) (c :: l)) with (ga_rows base vals c ++ flat_map (ga_rows base vals) l).
  rewrite length_app, IH. unfold ga_rows. cbn [length]. lia.
Qed.

Lemma length_sweep_rows : forall base w vals, (1 <= w)%nat ->
  Z.of_nat (length (sweep_rows base w vals)) = 8 + 3 * Z.of_nat w.
Proof.
  intros base w vals Hw. unfold sweep_rows. cbn [length]. rewrite length_app. cbn [length].
  rewrite length_flat_rows, length_seq. unfold ga_rows. cbn [length]. lia.
Qed.

Lemma rf1z_intro : forall zs, firstn 4 zs = [0xcd; 0xea; 4; 3] -> sum_from 2 zs mod 256 = 0 -> rf1z zs = true.
Proof.
  intros zs H1 H2. destruct zs as [|a [|b [|c [|d r]]]]; cbn in H1; try discriminate.
  injection H1 as -> -> -> ->. unfold rf1z. rewrite H2. reflexivity.
Qed.

Lemma GA_rowok : forall ch p v, 0 <= ch < 256 -> 0 <= p < 256 -> 0 <= v < 256 -> rowok (GA ch p v).
Proof.
  intros ch p v Hc Hp Hv. split; [reflexivity|]. unfold GA.
  rewrite map_unsigned_bl by (apply GA_bytes_range; assumption).
  apply rf1z_intro; [reflexivity | apply GA_sum_block].
Qed.

Lemma ga_row_ok : forall base vals c p, (p < 256)%nat -> rowok (ga_row base vals c p).
Proof.
  intros base vals c p Hp. unfold ga_row. apply GA_rowok; [apply Z.mod_pos_bound; lia | lia | unfold vz; apply byte_range].
Qed.

Lemma sweep_rows_ok : forall base w vals, Forall rowok (sweep_rows base w vals).
Proof.
  intros base w vals.
  assert (HG : forall c, Forall rowok (ga_rows base vals c)).
  { intros c. unfold ga_rows. apply Forall_cons; [apply ga_row_ok; lia|].
    apply Forall_cons; [apply ga_row_ok; lia|]. apply Forall_cons; [apply ga_row_ok; lia|]. apply Forall_nil. }
  assert (HF : forall l, Forall rowok (flat_map (ga_rows base vals) l)).
  { intros l. induction l as [|c l IH]; cbn [flat_map]; [apply Forall_nil|]. apply Forall_app. split; [apply HG | exact IH]. }
  unfold sweep_rows. apply Forall_cons; [split; vm_compute; reflexivity|].
  apply Forall_app. split; [apply HG|].
  do 7 (apply Forall_cons; [split; vm_compute; reflexivity|]). apply HF.
Qed.

Lemma Forall_rowok_len : forall L, Forall rowok L -> Forall (fun r => length r = 34%nat) L.
Proof. intros L H. eapply Forall_impl; [|exact H]. intros r [Hl _]. exact Hl. Qed.

Lemma concat_row : forall L k m a, Forall (fun r => length r = 34%nat) L -> (k < length L)%nat ->
  bytes_at rsegs m a (concat L) -> bytes_at rsegs m (a + 34 * Z.of_nat k) (nth k L []).
Proof.
  induction L as [|r L IH]; intros k m a HL Hk HB; cbn [length] in Hk; [lia|].
  inversion HL as [|r0 L0 Hr HL']; subst r0 L0.
  cbn [concat] in HB. apply (proj1 (bytes_at_app rsegs m _ _ _)) in HB. destruct HB as [HB1 HB2].
  destruct k as [|k]; cbn [nth].
  - eapply bytes_at_eqa; [exact HB1 | lia].
  - rewrite Hr in HB2. eapply bytes_at_eqa; [apply (IH k m _ HL' ltac:(lia) HB2) | lia].
Qed.

Lemma nth_flat_rows : forall base vals n a j q, (j < n)%nat -> (q < 3)%nat ->
  nth (3 * j + q) (flat_map (ga_rows base vals) (seq a n)) [] = ga_row base vals (a + j) q.
Proof.
  intros base vals n. induction n as [|n IH]; intros a j q Hj Hq; [lia|].
  cbn [seq flat_map]. destruct j as [|j].
  - unfold ga_rows. replace (a + 0)%nat with a by lia. cbn [Nat.mul Nat.add].
    destruct q as [|[|[|q]]]; [reflexivity | reflexivity | reflexivity | lia].
  - replace (3 * S j + q)%nat with (S (S (S (3 * j + q)))) by lia. unfold ga_rows at 1. cbn [app nth].
    rewrite IH by lia. f_equal. lia.
Qed.

Lemma nth_row_A0 : forall base w vals q, (q < 3)%nat ->
  nth (1 + q) (sweep_rows base w vals) [] = ga_row base vals 0 q.
Proof.
  intros base w vals q Hq. unfold sweep_rows, ga_rows. cbn [app].
  destruct q as [|[|[|q]]]; [reflexivity | reflexivity | reflexivity | lia].
Qed.

Lemma nth_row_A : forall base w vals c q, (1 <= c < w)%nat -> (q < 3)%nat ->
  nth (11 + 3 * (c - 1) + q) (sweep_rows base w vals) [] = ga_row base vals c q.
Proof.
  intros base w vals c q Hc Hq. unfold sweep_rows, ga_rows at 1. cbn [app].
  replace (11 + 3 * (c - 1) + q)%nat with (S (S (S (S (S (S (S (S (S (S (S (3 * (c - 1) + q)))))))))))) by lia.
  cbn [nth]. rewrite nth_flat_rows by lia. f_equal. lia.
Qed.

Lemma nth_row_B : forall base w vals i, (i < 6)%nat ->
  nth (5 + i) (sweep_rows base w vals) [] = GB (Z.of_nat i).
Proof.
  intros base w vals i Hi. unfold sweep_rows, ga_rows. cbn [app].
  destruct i as [|[|[|[|[|[|i]]]]]]; try reflexivity. lia.
Qed.

Lemma nth_row_0 : forall base w vals, nth 0 (sweep_rows base w vals) [] = HEAD_ACK34.
Proof. reflexivity. Qed.

Lemma nth_row_4 : forall base w vals, nth 4 (sweep_rows base w vals) [] = HEAD_MARK34.
Proof. reflexivity. Qed.

Lemma eff_range : forall T t ch p, 0 <= eff T t ch p < 256.
Proof.
  intros T t ch p. unfold eff, dflt, tb.
  destruct (3 <=? p); [lia|]. destruct ((t =? 0) || (48 <=? ch)); [destruct (p =? 2); lia|].
  destruct (bv_unsigned (nth (Z.to_nat (144 + 3 * ch + p)) T (Z_to_bv 8 0)) =? 0); [destruct (p =? 2); lia|].
  apply byte_range.
Qed.

Lemma vz_sweep_vals : forall T t base w c q, (c < w)%nat -> (q < 3)%nat ->
  vz (sweep_vals T t base w) (3 * c + q) = eff T t (base + Z.of_nat c) (Z.of_nat q).
Proof.
  intros T t base w c q Hc Hq. unfold vz, sweep_vals.
  rewrite (nth_indep _ _ (Z_to_bv 8 (eff T t (base + Z.of_nat (0 / 3)) (Z.of_nat (0 mod 3)))))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth (fun j => Z_to_bv 8 (eff T t (base + Z.of_nat (j / 3)) (Z.of_nat (j mod 3))))).
  rewrite seq_nth by lia. rewrite Nat.add_0_l.
  replace ((3 * c + q) / 3)%nat with c by (apply (Nat.div_unique _ 3 c q); lia).
  replace ((3 * c + q) mod 3)%nat with q by (apply (Nat.mod_unique _ 3 c q); lia).
  apply bv8_small. apply eff_range.
Qed.

Lemma memcmp_self : forall l n, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros l Hl; [reflexivity|].
  destruct l as [|a l]; cbn [length] in Hl; [lia|]. cbn [memcmp_model]. rewrite Z.eqb_refl. apply IH. lia.
Qed.
