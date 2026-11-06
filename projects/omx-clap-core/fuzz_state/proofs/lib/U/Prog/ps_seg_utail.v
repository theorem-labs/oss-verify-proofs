From Stdlib Require Import ZArith List Lia Bool Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require hex4_c hex4.
Import ListNotations.
Open Scope Z_scope.

Local Ltac cond_fact H := zify_cond H; rewrite ?unsigned_lit_wrap in H.

Lemma psu_lts : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !zb_signed, !unsigned_lit_wrap.
  apply eq_true_iff_eq. rewrite !Z.ltb_lt.
  destruct (Z.ltb_spec (a mod 2 ^ 64) (2 ^ 63)); destruct (Z.ltb_spec (b mod 2 ^ 64) (2 ^ 63));
    Z.div_mod_to_equations; lia.
Qed.

Lemma psu_rd8 : forall m A (v : word), bytes_at rsegs m A (le8 v) -> ov_read_bytes rsegs m (wa A) 8 = Some (le8 v).
Proof.
  intros m A v H. rewrite <- (Z.add_0_r A) at 1.
  rewrite (bytes_at_read rsegs m A (le8 v) 0 8 H) by (rewrite ?length_le8; cbn; lia). reflexivity.
Qed.

Lemma psu_rd4 : forall m A (v : word), bytes_at rsegs m A (le4 v) -> ov_read_bytes rsegs m (wa A) 4 = Some (le4 v).
Proof.
  intros m A v H. rewrite <- (Z.add_0_r A) at 1.
  rewrite (bytes_at_read rsegs m A (le4 v) 0 4 H) by (rewrite ?length_le4; cbn; lia). reflexivity.
Qed.

Lemma psu_skip : forall m text tb k, bytes_at rsegs m text tb -> (k <= length tb)%nat ->
  bytes_at rsegs m (text + Z.of_nat k) (skipn k tb).
Proof.
  intros m text tb k H Hk. rewrite <- (firstn_skipn k tb) in H.
  apply bytes_at_app in H. destruct H as [_ H].
  replace (Z.of_nat (length (firstn k tb))) with (Z.of_nat k) in H by (rewrite length_firstn; lia). exact H.
Qed.

Lemma psu_land : forall h, 0 <= h < 2 ^ 64 -> Z.land h 18446744073709550592 = 1024 * (h / 1024).
Proof.
  intros h Hh.
  change 18446744073709550592 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 10))).
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 10) with 1024. lia.
Qed.

Lemma psu_swrap : forall z w, - 2 ^ 31 <= w < 2 ^ 31 -> z mod 2 ^ 32 = w mod 2 ^ 32 -> bv_swrap 32 z = w.
Proof.
  intros z w Hw Hm. change (bv_swrap 32 z) with ((z + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31).
  rewrite Zplus_mod, Hm, <- Zplus_mod. rewrite Z.mod_small by lia. lia.
Qed.

Lemma psu_sx32 : forall lo, 0 <= lo < 2 ^ 31 -> sx32 (Z_to_bv 64 lo) = Z_to_bv 64 lo.
Proof.
  intros lo H. unfold sx32. rewrite (unsigned_lit lo) by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia). reflexivity.
Qed.

Lemma psu_hex4_range : forall bs v, hex4_c.hex4 bs = Some v -> 0 <= v < 65536.
Proof.
  intros bs v H. unfold hex4_c.hex4 in H.
  destruct bs as [|b0 [|b1 [|b2 [|b3 r]]]]; try discriminate.
  destruct (hex4_c.hexval b0) as [d0|] eqn:H0; try discriminate.
  destruct (hex4_c.hexval b1) as [d1|] eqn:H1; try discriminate.
  destruct (hex4_c.hexval b2) as [d2|] eqn:H2; try discriminate.
  destruct (hex4_c.hexval b3) as [d3|] eqn:H3; try discriminate.
  injection H as <-.
  pose proof (hex4.hexval_range _ _ H0). pose proof (hex4.hexval_range _ _ H1).
  pose proof (hex4.hexval_range _ _ H2). pose proof (hex4.hexval_range _ _ H3). lia.
Qed.

Definition ps_lo (bs : list byte) : option Z :=
  match bs with
  | b0 :: b1 :: hs =>
      if (bv_unsigned b0 =? 92) && (bv_unsigned b1 =? 117) then
        match hex4_c.hex4 hs with
        | Some lo => if (0xDC00 <=? lo) && (lo <=? 0xDFFF) then Some lo else None
        | None => None
        end
      else None
  | _ => None
  end.

Definition ps_cp (h : Z) (bs : list byte) : option (Z * Z) :=
  if h =? 0 then None
  else if (0xD800 <=? h) && (h <? 0xDC00) then
    match ps_lo bs with
    | Some lo => Some (0x10000 + (h - 0xD800) * 1024 + (lo - 0xDC00), 12)
    | None => None
    end
  else if (0xDC00 <=? h) && (h <? 0xE000) then None
  else Some (h, 6).

Lemma psu_lo_short : forall bs, (length bs < 6)%nat -> ps_lo bs = None.
Proof.
  intros bs H. destruct bs as [|b0 [|b1 [|c0 [|c1 [|c2 [|c3 r]]]]]]; cbn [length] in H; try (exfalso; lia);
    try reflexivity;
    unfold ps_lo; cbv beta iota; destruct ((bv_unsigned b0 =? 92) && (bv_unsigned b1 =? 117)); reflexivity.
Qed.

Lemma psu_lo_x0 : forall x0 x1 hs, bv_unsigned x0 <> 92 -> ps_lo (x0 :: x1 :: hs) = None.
Proof. intros x0 x1 hs H. unfold ps_lo. cbv beta iota. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma psu_lo_x1 : forall x0 x1 hs, bv_unsigned x1 <> 117 -> ps_lo (x0 :: x1 :: hs) = None.
Proof. intros x0 x1 hs H. unfold ps_lo. cbv beta iota. rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. reflexivity. Qed.

Lemma psu_lo_hex : forall x0 x1 hs, bv_unsigned x0 = 92 -> bv_unsigned x1 = 117 ->
  ps_lo (x0 :: x1 :: hs) = match hex4_c.hex4 hs with
                           | Some lo => if (0xDC00 <=? lo) && (lo <=? 0xDFFF) then Some lo else None
                           | None => None
                           end.
Proof. intros x0 x1 hs H0 H1. unfold ps_lo. cbv beta iota. rewrite H0, H1. reflexivity. Qed.

Lemma psu_rng_true : forall lo, 0xDC00 <= lo <= 0xDFFF -> (0xDC00 <=? lo) && (lo <=? 0xDFFF) = true.
Proof. intros lo H. apply andb_true_iff. split; apply Z.leb_le; lia. Qed.

Lemma psu_rng_false : forall lo, lo < 0xDC00 \/ 0xDFFF < lo -> (0xDC00 <=? lo) && (lo <=? 0xDFFF) = false.
Proof.
  intros lo H. destruct (Z.leb_spec 0xDC00 lo), (Z.leb_spec lo 0xDFFF); cbn [andb]; try reflexivity. exfalso. lia.
Qed.

Lemma psu_cp_zero : forall bs, ps_cp 0 bs = None.
Proof. reflexivity. Qed.

Lemma psu_cp_hi : forall h bs, 0xD800 <= h < 0xDC00 ->
  ps_cp h bs = match ps_lo bs with
               | Some lo => Some (0x10000 + (h - 0xD800) * 1024 + (lo - 0xDC00), 12)
               | None => None
               end.
Proof.
  intros h bs H. unfold ps_cp.
  replace (h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((0xD800 <=? h) && (h <? 0xDC00)) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  reflexivity.
Qed.

Lemma psu_cp_lo : forall h bs, 0xDC00 <= h < 0xE000 -> ps_cp h bs = None.
Proof.
  intros h bs H. unfold ps_cp.
  replace (h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace ((0xD800 <=? h) && (h <? 0xDC00)) with false
    by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
  replace ((0xDC00 <=? h) && (h <? 0xE000)) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  reflexivity.
Qed.

Lemma psu_cp_bmp : forall h bs, 0 < h -> h < 0xD800 \/ 0xE000 <= h -> ps_cp h bs = Some (h, 6).
Proof.
  intros h bs H0 H1. unfold ps_cp.
  replace (h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct H1 as [H1|H1].
  - replace ((0xD800 <=? h) && (h <? 0xDC00)) with false
      by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    replace ((0xDC00 <=? h) && (h <? 0xE000)) with false
      by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    reflexivity.
  - replace ((0xD800 <=? h) && (h <? 0xDC00)) with false
      by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
    replace ((0xDC00 <=? h) && (h <? 0xE000)) with false
      by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
    reflexivity.
Qed.

Local Ltac psu_fail M MU WM :=
  apply evt_done; cbv beta; left; do 17 eexists; exists M; split; [exact MU|]; split; [exact WM|]; split; [|reflexivity].

Local Ltac psu_ok h0 cp0 k0 M MU WM :=
  apply evt_done; cbv beta; right; exists h0, cp0, k0; do 15 eexists; exists M;
  split; [|split; [|split; [exact MU | split; [exact WM | reflexivity]]]].

Local Ltac psu_byte x H := assert (H : 0 <= bv_unsigned x < 256)
  by (pose proof (bv_unsigned_in_range 8 x) as HR; unfold bv_modulus in HR; exact HR).

Local Ltac trap H := cond_fact H; Z.div_mod_to_equations; lia.

Lemma ps_utail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (text len st P S : Z) (tb : list byte),
  hex4_c.hex4_contract ->
  s0 = Z_to_bv 64 st -> sp = Z_to_bv 64 S -> a0 = Z_to_bv 64 (text + len) -> s3 = Z_to_bv 64 P ->
  s9 = Z_to_bv 64 (P + 2) -> s6 = Z_to_bv 64 92 -> s7 = Z_to_bv 64 (-1) -> s10 = Z_to_bv 64 0xD800 ->
  bytes_at rsegs m text tb -> Z.of_nat (length tb) = len -> text + len < 2 ^ 62 -> text <= P -> P + 2 <= text + len ->
  0 < S -> S mod 8 = 0 -> S + 24 < 2 ^ 64 -> (S + 24 <= text \/ text + len <= S + 16) ->
  bytes_at rsegs m (st + 8) (le8 (Z_to_bv 64 (text + len))) -> (S + 24 <= st + 8 \/ st + 16 <= S + 16) ->
  bytes_at rsegs m S (le8 (Z_to_bv 64 0xFFFFFFFFFCA02400)) ->
  bytes_at rsegs m (S + 8) (le8 (Z_to_bv 64 0xDC00)) ->
  wr_at rsegs m (S + 16) 8 ->
  evt rsegs
    (fun ms' =>
       (exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s9' t3' t4' t5' t6' : word) (m' : word -> option byte),
          munch [(S + 16, S + 24)] m m' /\ wmono rsegs m m' /\
          (text + len - (P + 2) < 4 \/ hex4_c.hex4 (skipn (Z.to_nat (P + 2 - text)) tb) = None \/
           exists h, hex4_c.hex4 (skipn (Z.to_nat (P + 2 - text)) tb) = Some h /\
             ps_cp h (skipn (Z.to_nat (P + 6 - text)) tb) = None) /\
          ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9' s10 s11
                        t3' t4' t5' t6') F (Z_to_bv 64 0x15bc0) fc None m' (seg_rom rsegs))
       \/
       (exists (h cp k : Z) (ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
               (m' : word -> option byte),
          hex4_c.hex4 (skipn (Z.to_nat (P + 2 - text)) tb) = Some h /\
          ps_cp h (skipn (Z.to_nat (P + 6 - text)) tb) = Some (cp, k) /\
          munch [(S + 16, S + 24)] m m' /\ wmono rsegs m m' /\
          ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' (Z_to_bv 64 cp) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8
                        (Z_to_bv 64 (P + k)) s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15ba0) fc None m' (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a14) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m text len st P S tb
    HX Es0 Esp Ea0 Es3 Es9 Es6 Es7 Es10 HB HL Hend HP1 HP2 HS0 HSm HS24 HD HE HDE H0 H8 HW.
  subst s0 sp a0 s3 s9 s6 s7 s10.
  pose proof (bytes_at_bound rsegs m text tb HB) as [Ht _].
  assert (MU0 : munch [(S + 16, S + 24)] m m) by apply munch_refl.
  assert (WM0 : wmono rsegs m m) by apply wmono_refl.
  step. step. step.
  rewrite (unsigned_lit (text + len)), (unsigned_lit (P + 2)) by lia.
  rewrite (psu_lts (text + len - (P + 2)) 4) by lia.
  destruct (Z.ltb_spec (text + len - (P + 2)) 4) as [L4|L4]; cbv iota.
  { psu_fail m MU0 WM0. left. exact L4. }
  pose proof (psu_skip m text tb (Z.to_nat (P + 2 - text)) HB ltac:(lia)) as HB2.
  rewrite Z2Nat.id in HB2 by lia. replace (text + (P + 2 - text)) with (P + 2) in HB2 by lia.
  assert (HL2 : length (skipn (Z.to_nat (P + 2 - text)) tb) = Z.to_nat (text + len - (P + 2)))
    by (rewrite length_skipn; lia).
  assert (E6 : skipn (Z.to_nat (P + 6 - text)) tb = skipn 4 (skipn (Z.to_nat (P + 2 - text)) tb)).
  { rewrite skipn_skipn. f_equal. lia. }
  rewrite E6. clear E6.
  revert HL2 HB2.
  destruct (skipn (Z.to_nat (P + 2 - text)) tb) as [|b0 [|b1 [|b2 [|b3 bs]]]] eqn:Er2; intros HL2 HB2;
    try (cbn [length] in HL2; lia).
  change (skipn 4 (b0 :: b1 :: b2 :: b3 :: bs)) with bs.
  change (hex4_c.hex4 (b0 :: b1 :: b2 :: b3 :: bs)) with (hex4_c.hex4 [b0; b1; b2; b3]).
  assert (HB4 : bytes_at rsegs m (P + 2) [b0; b1; b2; b3]).
  { change (b0 :: b1 :: b2 :: b3 :: bs) with ([b0; b1; b2; b3] ++ bs) in HB2.
    apply bytes_at_app in HB2. exact (proj1 HB2). }
  assert (HBs : bytes_at rsegs m (P + 6) bs).
  { change (b0 :: b1 :: b2 :: b3 :: bs) with ([b0; b1; b2; b3] ++ bs) in HB2.
    apply bytes_at_app in HB2. destruct HB2 as [_ HB2]. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in HB2.
    replace (P + 6) with (P + 2 + 4) by lia. exact HB2. }
  assert (HLs : Z.of_nat (length bs) = text + len - (P + 6)) by (cbn [length] in HL2; lia).
  clear HB2 HL2 Er2.
  assert (HW20 : wr_at rsegs m (S + 20) 4).
  { pose proof HW as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
    replace (S + 20 + i) with (S + 16 + (4 + i)) by lia. apply W. lia. }
  step. step. step.
  eapply evt_cut.
  { eapply HX; [reflexivity | reflexivity | lia | exact HB4 | lia | Z.div_mod_to_equations; lia | exact HW20 | lia]. }
  intros ms1 (t0' & t1' & t2' & r0 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & HR1).
  replace (ret_pc (Z_to_bv 64 0x15a2c)) with (Z_to_bv 64 0x15a2c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (MU1' : munch [(S + 16, S + 24)] m m1).
  { apply (munch_weaken [(S + 20, S + 20 + 4)]); [|exact MU1].
    intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx & _). split; [lia | exact I]. }
  destruct (hex4_c.hex4 [b0; b1; b2; b3]) as [h|] eqn:Hh.
  2: { destruct HR1 as [-> ->]. step. if_true. psu_fail m MU0 WM0. right. left. reflexivity. }
  destruct HR1 as [-> HBh].
  pose proof (psu_hex4_range _ _ Hh) as Hhr.
  assert (R20 : ov_read_bytes rsegs m1 (wa (S + 20)) 4 = Some (le4 (Z_to_bv 64 h))) by (apply psu_rd4; exact HBh).
  assert (H8' : bytes_at rsegs m1 (S + 8) (le8 (Z_to_bv 64 0xDC00))).
  { apply (bytes_at_transport rsegs _ m m1 (S + 8) _ H8 MU1). cbn [disjoint_from]. rewrite length_le8. split; [lia | exact I]. }
  pose proof (psu_rd8 m1 _ _ H8') as R8.
  step. if_false.
  step. rewrite (psu_sx32 h) by lia.
  step. if_cases HC0.
  { cond_fact HC0. assert (h = 0) by (Z.div_mod_to_equations; lia). subst h.
    psu_fail m1 MU1' WM1. right. right. exists 0. split; [reflexivity | apply psu_cp_zero]. }
  cond_fact HC0.
  step. step. if_cases HT1; [trap HT1|].
  step. step.
  step. if_cases HC1.
  - cond_fact HC1. rewrite (psu_land h) in HC1 by lia.
    assert (Hhi : 0xD800 <= h < 0xDC00) by (Z.div_mod_to_equations; lia).
    assert (HE1 : bytes_at rsegs m1 (st + 8) (le8 (Z_to_bv 64 (text + len)))).
    { apply (bytes_at_transport rsegs _ m m1 (st + 8) _ HE MU1). cbn [disjoint_from]. rewrite length_le8. split; [lia | exact I]. }
    pose proof (psu_rd8 m1 _ _ HE1) as RE.
    step. step. step. step.
    rewrite (unsigned_lit (text + len)), (unsigned_lit (P + 6)) by lia.
    rewrite (psu_lts (text + len - (P + 6)) 6) by lia.
    destruct (Z.ltb_spec (text + len - (P + 6)) 6) as [L6|L6]; cbv iota.
    { psu_fail m1 MU1' WM1. right. right. exists h. split; [reflexivity|].
      rewrite (psu_cp_hi h bs Hhi), (psu_lo_short bs) by lia. reflexivity. }
    assert (HBs1 : bytes_at rsegs m1 (P + 6) bs).
    { apply (bytes_at_transport rsegs _ m m1 (P + 6) _ HBs MU1). cbn [disjoint_from]. lia. }
    clear HBs.
    destruct bs as [|x0 [|x1 [|c0 [|c1 [|c2 [|c3 r]]]]]]; try (cbn [length] in HLs; exfalso; lia).
    psu_byte x0 XB0. psu_byte x1 XB1.
    assert (R6 : ov_read_bytes rsegs m1 (wa (P + 6)) 1 = Some [x0]).
    { rewrite <- (Z.add_0_r (P + 6)) at 1. rewrite (bytes_at_read rsegs m1 (P + 6) _ 0 1 HBs1) by (cbn; lia). reflexivity. }
    assert (R7 : ov_read_bytes rsegs m1 (wa (P + 7)) 1 = Some [x1]).
    { replace (P + 7) with (P + 6 + 1) by lia. rewrite (bytes_at_read rsegs m1 (P + 6) _ 1 1 HBs1) by (cbn; lia). reflexivity. }
    assert (HC : bytes_at rsegs m1 (P + 8) [c0; c1; c2; c3]).
    { pose proof HBs1 as HB6. change (x0 :: x1 :: c0 :: c1 :: c2 :: c3 :: r) with ([x0; x1] ++ [c0; c1; c2; c3] ++ r) in HB6.
      apply bytes_at_app in HB6. destruct HB6 as [_ HB6]. apply bytes_at_app in HB6. destruct HB6 as [HB6 _].
      cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in HB6. replace (P + 8) with (P + 6 + 2) by lia. exact HB6. }
    step. step. if_cases HC2.
    { cond_fact HC2. rewrite Z.mod_small in HC2 by lia.
      psu_fail m1 MU1' WM1. right. right. exists h. split; [reflexivity|].
      rewrite (psu_cp_hi h _ Hhi), (psu_lo_x0 x0 x1 _ HC2). reflexivity. }
    cond_fact HC2. rewrite Z.mod_small in HC2 by lia.
    step. if_cases HT2; [trap HT2|].
    step. step. step. if_cases HC3.
    { cond_fact HC3. rewrite Z.mod_small in HC3 by lia.
      psu_fail m1 MU1' WM1. right. right. exists h. split; [reflexivity|].
      rewrite (psu_cp_hi h _ Hhi), (psu_lo_x1 x0 x1 _ HC3). reflexivity. }
    cond_fact HC3. rewrite Z.mod_small in HC3 by lia.
    step. step. if_cases HT3; [trap HT3|].
    assert (HW16 : wr_at rsegs m1 (S + 16) 4).
    { pose proof (wr_at_transport rsegs m m1 _ _ HW WM1) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      apply W. lia. }
    step. step. step.
    eapply evt_cut.
    { eapply HX; [reflexivity | reflexivity | lia | exact HC | lia | Z.div_mod_to_equations; lia | exact HW16 | lia]. }
    intros ms2 (t0'' & t1'' & t2'' & r1 & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2
      & -> & MU2 & WM2 & HR2).
    replace (ret_pc (Z_to_bv 64 0x15b64)) with (Z_to_bv 64 0x15b64) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (MU2' : munch [(S + 16, S + 24)] m m2).
    { apply (munch_trans _ _ _ _ MU1'). apply (munch_weaken [(S + 16, S + 16 + 4)]); [|exact MU2].
      intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx & _). split; [lia | exact I]. }
    pose proof (wmono_trans rsegs _ _ _ WM1 WM2) as WM2'.
    destruct (hex4_c.hex4 [c0; c1; c2; c3]) as [lo|] eqn:Hlo.
    2: { destruct HR2 as [-> ->]. step. if_true. psu_fail m1 MU1' WM1. right. right. exists h. split; [reflexivity|].
         rewrite (psu_cp_hi h _ Hhi), (psu_lo_hex x0 x1 _ HC2 HC3).
         change (hex4_c.hex4 (c0 :: c1 :: c2 :: c3 :: r)) with (hex4_c.hex4 [c0; c1; c2; c3]). rewrite Hlo. reflexivity. }
    destruct HR2 as [-> HBl].
    pose proof (psu_hex4_range _ _ Hlo) as Hlr.
    assert (R16 : ov_read_bytes rsegs m2 (wa (S + 16)) 4 = Some (le4 (Z_to_bv 64 lo))) by (apply psu_rd4; exact HBl).
    assert (HBh2 : bytes_at rsegs m2 (S + 20) (le4 (Z_to_bv 64 h))).
    { apply (bytes_at_transport rsegs _ m1 m2 (S + 20) _ HBh MU2). cbn [disjoint_from]. rewrite length_le4. split; [lia | exact I]. }
    pose proof (psu_rd4 m2 _ _ HBh2) as R20'.
    assert (H02 : bytes_at rsegs m2 S (le8 (Z_to_bv 64 0xFFFFFFFFFCA02400))).
    { apply (bytes_at_transport rsegs _ m m2 S _ H0 MU2'). cbn [disjoint_from]. rewrite length_le8. split; [lia | exact I]. }
    pose proof (psu_rd8 m2 _ _ H02) as R0.
    step. if_false.
    step. rewrite (psu_sx32 lo) by lia.
    step. step.
    match goal with |- context [bv_swrap 32 ?z] =>
      replace (bv_swrap 32 z) with (lo - 57344)
        by (symmetry; apply psu_swrap; [lia | rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia]) end.
    step. step. if_cases HC4.
    { cond_fact HC4. psu_fail m2 MU2' WM2'. right. right. exists h. split; [reflexivity|].
      rewrite (psu_cp_hi h _ Hhi), (psu_lo_hex x0 x1 _ HC2 HC3).
      change (hex4_c.hex4 (c0 :: c1 :: c2 :: c3 :: r)) with (hex4_c.hex4 [c0; c1; c2; c3]). rewrite Hlo.
      rewrite (psu_rng_false lo) by (Z.div_mod_to_equations; lia). reflexivity. }
    cond_fact HC4.
    assert (Hlo2 : 0xDC00 <= lo <= 0xDFFF) by (Z.div_mod_to_equations; lia).
    step. step. if_cases HT4; [trap HT4|].
    step. rewrite (psu_sx32 h) by lia.
    step. step. step. step. step.
    match goal with |- context [bv_swrap 32 ?z] =>
      replace (bv_swrap 32 z) with (0x10000 + (h - 0xD800) * 1024 + (lo - 0xDC00))
        by (symmetry; apply psu_swrap; [lia | rewrite ?(unsigned_lit h), ?(unsigned_lit lo) by lia;
            rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia]) end.
    assert (HS20 : store_ok rsegs m2 (wa (S + 20)) 4 = true).
    { rewrite <- (Z.add_0_r (S + 20)) at 1. apply (wr_at_store_ok rsegs m2 (S + 20) 4 0 4); [|lia|cbn; lia].
      exact (wr_at_transport rsegs m m2 _ _ HW20 WM2'). }
    step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?M3 _) =>
      assert (MU3 : munch [(S + 16, S + 24)] m M3);
      [| assert (WM3 : wmono rsegs m M3); [| psu_ok h (0x10000 + (h - 0xD800) * 1024 + (lo - 0xDC00)) 12 M3 MU3 WM3]] end.
    + apply munch_write; [exact MU2' | lia | rewrite length_le4; lia | cbn [inside]; rewrite length_le4; lia].
    + apply wmono_write. exact WM2'.
    + reflexivity.
    + rewrite (psu_cp_hi h _ Hhi), (psu_lo_hex x0 x1 _ HC2 HC3).
      change (hex4_c.hex4 (c0 :: c1 :: c2 :: c3 :: r)) with (hex4_c.hex4 [c0; c1; c2; c3]). rewrite Hlo.
      rewrite (psu_rng_true lo) by lia. reflexivity.
  - cond_fact HC1. rewrite (psu_land h) in HC1 by lia.
    step. step. if_cases HC2.
    { cond_fact HC2. rewrite (psu_land h) in HC2 by lia.
      psu_fail m1 MU1' WM1. right. right. exists h. split; [reflexivity|].
      apply psu_cp_lo. Z.div_mod_to_equations; lia. }
    cond_fact HC2. rewrite (psu_land h) in HC2 by lia.
    step.
    psu_ok h h 6 m1 MU1' WM1.
    + reflexivity.
    + apply psu_cp_bmp; [lia | Z.div_mod_to_equations; lia].
Qed.
