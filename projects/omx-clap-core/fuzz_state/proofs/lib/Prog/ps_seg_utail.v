From Stdlib Require Import ZArith List Lia Bool Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require hex4_c hex4.
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

Lemma ps_utail_pre : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (e q : Z),
  a0 = Z_to_bv 64 e -> s10 = Z_to_bv 64 q -> 0 <= e < 2 ^ 62 -> 0 <= q < 2 ^ 62 ->
  evt rsegs
    (fun ms' => if 4 <=? e - q
       then ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (e - q)) (Z_to_bv 64 4) a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x153e8) fc None m (seg_rom rsegs)
       else ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (e - q)) (Z_to_bv 64 4) a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1558c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x153dc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e q
    E0 E10 He Hq.
  subst a0 s10.
  step. rewrite (unsigned_lit e), (unsigned_lit q) by lia.
  step. step.
  rewrite (psu_lts (e - q) 4) by lia.
  destruct (Z.ltb_spec (e - q) 4) as [L|L]; cbv iota; apply evt_done; cbv beta.
  - replace (4 <=? e - q) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - replace (4 <=? e - q) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma psu_rd8 : forall m A (v : word), bytes_at rsegs m A (le8 v) -> ov_read_bytes rsegs m (wa A) 8 = Some (le8 v).
Proof.
  intros m A v H. rewrite <- (Z.add_0_r A) at 1.
  rewrite (bytes_at_read rsegs m A (le8 v) 0 8 H) by (rewrite ?length_le8; cbn; lia). reflexivity.
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

Local Ltac psu_none M MU WM :=
  apply evt_done; cbv beta iota; do 18 eexists; exists M; split; [exact MU | split; [exact WM | reflexivity]].

Local Ltac psu_some M MU WM :=
  apply evt_done; cbv beta iota; do 14 eexists; exists M; split; [exact MU | split; [exact WM | reflexivity]].

Local Ltac psu_byte x H := assert (H : 0 <= bv_unsigned x < 256)
  by (pose proof (bv_unsigned_in_range 8 x) as HR; unfold bv_modulus in HR; exact HR).

Lemma ps_utail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (text len P S h : Z) (tb : list byte),
  hex4_c.hex4_contract ->
  ra = Z_to_bv 64 117 -> sp = Z_to_bv 64 S -> a0 = Z_to_bv 64 (text + len) -> s3 = Z_to_bv 64 h ->
  s6 = Z_to_bv 64 92 -> s8 = Z_to_bv 64 P -> s11 = Z_to_bv 64 6 -> 0 <= h < 65536 ->
  bytes_at rsegs m text tb -> Z.of_nat (length tb) = len -> text + len < 2 ^ 62 -> text <= P -> P + 6 <= text + len ->
  0 <= S -> S mod 4 = 0 -> S + 40 <= text \/ text + len <= S + 36 ->
  bytes_at rsegs m (S + 8) (le8 (Z_to_bv 64 0xFFFFFFFFFCA02400)) ->
  bytes_at rsegs m (S + 16) (le8 (Z_to_bv 64 0xDC00)) ->
  bytes_at rsegs m (S + 24) (le8 (Z_to_bv 64 0xD800)) ->
  wr_at rsegs m (S + 36) 4 ->
  evt rsegs
    (fun ms' => match ps_cp h (skipn (Z.to_nat (P + 6 - text)) tb) with
       | Some (cp, k) => exists (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
           munch [(S + 36, S + 40)] m m' /\ wmono rsegs m m' /\
           ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 s2 (Z_to_bv 64 cp) a2' a3' a4' a5' a6' a7'
                         s2 (Z_to_bv 64 cp) s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (P + k)) s11 t3' t4' t5' t6')
                    F (Z_to_bv 64 0x1554c) fc None m' (seg_rom rsegs)
       | None => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s10' t3' t4' t5' t6' : word)
                        (m' : word -> option byte),
           munch [(S + 36, S + 40)] m m' /\ wmono rsegs m m' /\
           ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                         s2 s3' s4 s5 s6 s7 s8 s9 s10' s11 t3' t4' t5' t6')
                    F (Z_to_bv 64 0x1558c) fc None m' (seg_rom rsegs)
       end)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1543c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m text len P S h tb
    HX Era Esp E0 E3 E6 E8 E11 Hh HB HL Hend HP1 HP2 HS HSm HD H8 H16 H24 HW.
  subst ra sp a0 s3 s6 s8 s11.
  pose proof (bytes_at_bound rsegs m text tb HB) as [Ht _].
  pose proof (psu_rd8 m _ _ H16) as R16.
  pose proof (psu_rd8 m _ _ H24) as R24.
  assert (MU0 : munch [(S + 36, S + 40)] m m) by apply munch_refl.
  assert (WM0 : wmono rsegs m m) by apply wmono_refl.
  pose proof (psu_skip m text tb (Z.to_nat (P + 6 - text)) HB ltac:(lia)) as HBs.
  rewrite Z2Nat.id in HBs by lia. replace (text + (P + 6 - text)) with (P + 6) in HBs by lia.
  assert (HLs : Z.of_nat (length (skipn (Z.to_nat (P + 6 - text)) tb)) = text + len - (P + 6))
    by (rewrite length_skipn; lia).
  set (bs := skipn (Z.to_nat (P + 6 - text)) tb) in *. clearbody bs.
  step.
  if_cases HC0.
  { cond_fact HC0. subst h. rewrite psu_cp_zero. psu_none m MU0 WM0. }
  cond_fact HC0.
  step. step. step. step.
  if_cases HC1.
  - cond_fact HC1. rewrite (psu_land h) in HC1 by lia.
    assert (Hhi : 0xD800 <= h < 0xDC00) by (Z.div_mod_to_equations; lia).
    rewrite (psu_cp_hi h bs Hhi).
    step. rewrite (unsigned_lit (text + len)), (unsigned_lit (P + 6)) by lia.
    step. rewrite (psu_lts (text + len - (P + 6)) 6) by lia.
    destruct (Z.ltb_spec (text + len - (P + 6)) 6) as [L6|L6]; cbv iota.
    { rewrite (psu_lo_short bs) by lia. psu_none m MU0 WM0. }
    destruct bs as [|x0 [|x1 [|c0 [|c1 [|c2 [|c3 r]]]]]]; try (cbn [length] in HLs; exfalso; lia).
    psu_byte x0 XB0. psu_byte x1 XB1.
    assert (R6 : ov_read_bytes rsegs m (wa (P + 6)) 1 = Some [x0]).
    { rewrite <- (Z.add_0_r (P + 6)) at 1. rewrite (bytes_at_read rsegs m (P + 6) _ 0 1 HBs) by (cbn; lia). reflexivity. }
    assert (R7 : ov_read_bytes rsegs m (wa (P + 7)) 1 = Some [x1]).
    { replace (P + 7) with (P + 6 + 1) by lia. rewrite (bytes_at_read rsegs m (P + 6) _ 1 1 HBs) by (cbn; lia). reflexivity. }
    assert (HC : bytes_at rsegs m (P + 8) [c0; c1; c2; c3]).
    { pose proof HBs as HB6. change (x0 :: x1 :: c0 :: c1 :: c2 :: c3 :: r) with ([x0; x1] ++ [c0; c1; c2; c3] ++ r) in HB6.
      apply bytes_at_app in HB6. destruct HB6 as [_ HB6]. apply bytes_at_app in HB6. destruct HB6 as [HB6 _].
      cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in HB6. replace (P + 8) with (P + 6 + 2) by lia. exact HB6. }
    step. step. if_cases HC2.
    { cond_fact HC2. rewrite Z.mod_small in HC2 by lia. rewrite (psu_lo_x0 x0 x1 _ HC2). psu_none m MU0 WM0. }
    cond_fact HC2. rewrite Z.mod_small in HC2 by lia.
    step. step. if_cases HC3.
    { cond_fact HC3. rewrite Z.mod_small in HC3 by lia. rewrite (psu_lo_x1 x0 x1 _ HC3). psu_none m MU0 WM0. }
    cond_fact HC3. rewrite Z.mod_small in HC3 by lia.
    rewrite (psu_lo_hex x0 x1 _ HC2 HC3).
    change (hex4_c.hex4 (c0 :: c1 :: c2 :: c3 :: r)) with (hex4_c.hex4 [c0; c1; c2; c3]).
    step. step. step.
    eapply evt_cut; [ eapply HX; [ reflexivity | reflexivity | lia | exact HC | lia | Z.div_mod_to_equations; lia | exact HW | lia ] | ].
    intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & r0 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & HR).
    replace (S + 36 + 4) with (S + 40) in MU by lia.
    replace (ret_pc (Z_to_bv 64 87320)) with (Z_to_bv 64 87320) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    destruct (hex4_c.hex4 [c0; c1; c2; c3]) as [lo|] eqn:Hlo.
    2: { destruct HR as [-> ->]. step. if_true. psu_none m MU WM. }
    destruct HR as [-> HBl].
    pose proof (psu_hex4_range _ _ Hlo) as Hlr.
    assert (H8' : bytes_at rsegs m' (S + 8) (le8 (Z_to_bv 64 0xFFFFFFFFFCA02400))).
    { apply (bytes_at_transport rsegs [(S + 36, S + 40)] m m' (S + 8) _ H8 MU). cbn [disjoint_from]. simpl_sizes. slia. }
    pose proof (psu_rd8 m' _ _ H8') as R8.
    assert (R36 : ov_read_bytes rsegs m' (wa (S + 36)) 4 = Some (le4 (Z_to_bv 64 lo))).
    { rewrite <- (Z.add_0_r (S + 36)) at 1.
      rewrite (bytes_at_read rsegs m' (S + 36) _ 0 4 HBl) by (rewrite ?length_le4; cbn; lia). reflexivity. }
    step. if_false.
    step. rewrite (psu_sx32 lo) by lia.
    step. step.
    match goal with |- context [bv_swrap 32 ?z] =>
      replace (bv_swrap 32 z) with (lo - 57344)
        by (symmetry; apply psu_swrap; [lia | rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia]) end.
    step. step. if_cases HC4.
    { cond_fact HC4.
      rewrite (psu_rng_false lo) by (Z.div_mod_to_equations; lia). psu_none m' MU WM. }
    cond_fact HC4.
    rewrite (psu_rng_true lo) by (Z.div_mod_to_equations; lia).
    step. step. step. step. step. step. step.
    match goal with |- context [bv_swrap 32 ?z] =>
      replace (bv_swrap 32 z) with (0x10000 + (h - 0xD800) * 1024 + (lo - 0xDC00))
        by (symmetry; apply psu_swrap; [lia | rewrite ?(unsigned_lit h), ?(unsigned_lit lo) by lia;
            rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia]) end.
    psu_some m' MU WM.
  - cond_fact HC1. rewrite (psu_land h) in HC1 by lia.
    step. step. if_cases HC2.
    { cond_fact HC2. rewrite (psu_land h) in HC2 by lia.
      rewrite (psu_cp_lo h bs) by (Z.div_mod_to_equations; lia). psu_none m MU0 WM0. }
    cond_fact HC2. rewrite (psu_land h) in HC2 by lia.
    rewrite (psu_cp_bmp h bs) by (Z.div_mod_to_equations; lia).
    step. step. step.
    psu_some m MU0 WM0.
Qed.
