From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK15 YM02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YO0i YO0f YO0g YO0q YO0x YO0d YO0e
YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 DriverPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocPack AllocPackRoom AllocPackCut SlotPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocPack3 AllocPack3Room AllocPack3Cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Lemma mis_realloc_nil_grow : forall k n p q, band k <= band n -> mis_realloc [] k n p q = [].
Proof.
  intros k n p q Hb. unfold mis_realloc.
  destruct (Z.eqb_spec (band n + 1) (band k)) as [E|_]; [lia|].
  destruct (sptr_eqb q p && (band n + 1 <? 48)); reflexivity.
Qed.
Lemma mis_nil_malloc : forall b n, p3_mis b = [] -> p3_mis (pb3_malloc b n) = [].
Proof. intros b n H. exact H. Qed.
Lemma mis_nil_free : forall b n p, p3_mis b = [] -> p3_mis (pb3_free b n p) = [].
Proof. intros b n p H. unfold pb3_free, mis_del. cbn [p3_mis]. rewrite H. reflexivity. Qed.
Lemma mis_nil_realloc : forall b k n p q, p3_mis b = [] -> band k <= band n -> p3_mis (pb3_realloc b k n p q) = [].
Proof. intros b k n p q H Hb. unfold pb3_realloc. cbn [p3_mis]. rewrite H. exact (mis_realloc_nil_grow k n p q Hb). Qed.
Lemma pk27_tab : forallb (fun k => znth k (repeat 27 49) =? 27) (zseq 0 49) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pk27_ok : forall k, 0 <= k < 49 -> znth k (repeat 27 49) = 27.
Proof. intros k Hk. apply Z.eqb_eq. exact (forallb_zseq49 _ k pk27_tab Hk). Qed.
Lemma GALL3_c27 : 845 <= GALL3 (repeat 64 49) (repeat 27 49).
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma capok3 : CAPOK2 (GALL3 (repeat 64 49) (repeat 27 49)) (GMAP3 (repeat 64 49) (repeat 27 49)) (2 ^ 28) (2 ^ 27).
Proof. unfold CAPOK2. repeat split; first [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. Qed.
Lemma room64_3 : forall L y n, (forall k, 0 <= k < 49 -> znth k L <= 1) -> 0 <= n <= 2 ^ 27 -> y + n <= 2 ^ 28 ->
  room_pack3 (PB3 L y (repeat 64 49) [] (repeat 27 49)) n.
Proof.
  intros L y n HL Hn Hy. pose proof (AllocPackRoom.band_range n ltac:(lia)) as Hb.
  apply (room_pack3_of (PB3 L y (repeat 64 49) [] (repeat 27 49)) n (2 ^ 28) (2 ^ 27));
    cbn [p3_live p3_bytes p3_cap p3_mis p3_mcap].
  - exact capok3.
  - exact Hn.
  - exact Hy.
  - rewrite (proj2 (pk0_ok (band n) Hb)). pose proof (HL (band n) Hb). lia.
  - intros Hb1. unfold count_mis. cbn [filter length Z.of_nat]. rewrite (pk27_ok (band n + 1) ltac:(lia)). lia.
Qed.
Definition PK13 (s : astate) (cap : Z) : Prop :=
  res_ok_pack3 s (PB3 (lv_add (repeat 0 49) (band cap) 1) cap (repeat 64 49) [] (repeat 27 49)).
Lemma read_phase_pack3 : forall fuel L cap k buf s b K c,
  WF s -> In (buf, cap) (user_blocks s) -> cap = 2 ^ k -> 16 <= k -> cap <= MAX_INPUT ->
  res_ok s b -> RPinv K c cap b -> K + capflag cap <= 2 ^ 24 -> 0 <= c -> c + Z.of_nat fuel <= 12 ->
  PK13 s cap ->
  leaves (fun r => match fst r with RdLoaded _ cap' => PK13 (snd r) cap' | _ => True end) (read_phase fuel L cap buf s).
Proof.
  induction fuel as [|fuel IH]; intros L cap k buf s b K c HW Hin Hk Hk16 Hmax HR (V1 & V2 & V3 & V4 & V5) HK Hc Hcf HP;
    cbn [read_phase].
  - apply leaves_ret. exact I.
  - assert (Hcap : 65536 <= cap).
    { subst cap. change 65536 with (2 ^ 16). apply Z.pow_le_mono_r; lia. }
    assert (Hfl : 0 <= capflag cap) by (unfold capflag; destruct (cap <=? MMAP_THRESHOLD); unfold MMAX; lia).
    pose proof (mdelta_le cap ltac:(lia)) as Hmd.
    destruct (L <? cap) eqn:EL.
    { apply leaves_ret. exact HP. }
    destruct (MAX_INPUT <=? cap) eqn:EM.
    { apply leaves_ret. exact I. }
    apply Z.leb_gt in EM.
    assert (Hmd2 : mdelta (2 * cap) = 2 * cap + PGSZ).
    { rewrite mdelta_big by (unfold MMAP_THRESHOLD; lia). apply page_round_exact; [|lia].
      subst cap. replace (2 * 2 ^ k) with ((2 * 2 ^ (k - 12)) * PGSZ); [apply Z_mod_mult|].
      unfold PGSZ. change 4096 with (2 ^ 12). rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. lia. }
    pose proof (shcap_845 (rb_hand b) ltac:(lia)) as SC.
    eapply leaves_mbind.
    { apply (malloc_leaves_res s b (2 * cap) HW HR). unfold room. rewrite <- mdelta_big by (unfold MMAP_THRESHOLD; lia). rewrite Hmd2.
      unfold MG_LIVE, MG_SLOTS, MG_REQ, MAX_INPUT, MMAX, IB, UNIT, PGSZ in *.
      assert (rb_brk b / 4096 <= 2 * c) by (apply Z.div_le_upper_bound; lia).
      repeat split; try lia. }
    intros [nb|] s1 tr1 Hy1 [[HW1 Hb] HR1]; cbn [fst snd] in HW1, Hb, HR1.
    2:{ apply leaves_ret. exact I. }
    destruct Hb as (l1 & l2 & E1 & E2).
    assert (Hin1 : In (buf, cap) (user_blocks s1)).
    { rewrite E1. apply in_app_iff. rewrite E2 in Hin. apply in_app_iff in Hin. destruct Hin; [left | right; right]; assumption. }
    assert (Hnb1 : In (nb, 2 * cap) (user_blocks s1)) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
    pose proof (AllocPackRoom.band_range cap ltac:(lia)) as Hbc.
    assert (HP1 : res_ok_pack3 s1
      (pb3_malloc (PB3 (lv_add (repeat 0 49) (band cap) 1) cap (repeat 64 49) [] (repeat 27 49)) (2 * cap))).
    { apply (malloc_pack3_yields s _ (2 * cap) tr1 nb s1 HW HP).
      - apply room64_3; [| unfold MAX_INPUT in *; lia | unfold MAX_INPUT in *; lia].
        intros k0 Hk0. exact (proj2 (proj1 (proj2 (pk1_ok (band cap) Hbc)) k0 Hk0)).
      - exact Hy1.
      - cbn [p3_cap p3_mcap]. pose proof GALL3_c27. destruct HR1 as (_ & _ & _ & Hh & _).
        unfold rb_malloc in Hh. cbn [rb_hand] in Hh. lia. }
    eapply leaves_mbind; [apply (free_leaves_res s1 _ buf cap HW1 Hin1 HR1)|].
    intros [] s2 tr2 Hy2 [[HW2 (m1 & m2 & F1 & F2)] HR2]; cbn [fst snd] in HW2, F1, F2, HR2.
    assert (Hin2 : In (nb, 2 * cap) (user_blocks s2)).
    { rewrite F2. eapply in_remove_other; [rewrite <- F1; exact Hnb1 |]. intros E. injection E. lia. }
    assert (HP2 : PK13 s2 (2 * cap)).
    { pose proof (free_pack3_yields s1 _ buf cap tr2 s2 HW1 Hin1 HP1 Hy2) as HP2. unfold PK13.
      replace (PB3 (lv_add (repeat 0 49) (band (2 * cap)) 1) (2 * cap) (repeat 64 49) [] (repeat 27 49))
        with (pb3_free (pb3_malloc (PB3 (lv_add (repeat 0 49) (band cap) 1) cap (repeat 64 49) [] (repeat 27 49))
          (2 * cap)) cap buf); [exact HP2|].
      unfold pb3_free, pb3_malloc, mis_del. cbn [p3_live p3_bytes p3_cap p3_mis p3_mcap filter]. f_equal; [|lia].
      rewrite lv_add_comm. rewrite lv_add_cancel by lia. reflexivity. }
    assert (H2max : 2 * cap <= MAX_INPUT).
    { subst cap. unfold MAX_INPUT in *. change 67108864 with (2 ^ 26) in *. rewrite <- Z.pow_succ_r by lia.
      apply Z.pow_le_mono_r; [lia|]. apply Z.pow_lt_mono_r_iff in EM; lia. }
    assert (Hfl2 : capflag (2 * cap) = 0).
    { unfold capflag. replace (2 * cap <=? MMAP_THRESHOLD) with false by (symmetry; apply Z.leb_gt; unfold MMAP_THRESHOLD; lia). reflexivity. }
    apply (IH L (2 * cap) (k + 1) nb s2 (rb_free (rb_malloc b (2 * cap)) cap) (K + capflag cap) (c + 1) HW2 Hin2);
      [subst cap; rewrite Z.pow_add_r by lia; lia | lia | exact H2max | exact HR2 | | rewrite Hfl2; lia | lia | lia | exact HP2].
    unfold RPinv, rb_free, rb_malloc. rewrite Hmd2.
    destruct (MMAP_THRESHOLD <? cap) eqn:Et; cbn.
    + apply Z.ltb_lt in Et. rewrite <- (mdelta_big cap) by lia. unfold PGSZ in *. repeat split; lia.
    + apply Z.ltb_ge in Et. unfold capflag. replace (cap <=? MMAP_THRESHOLD) with true by (symmetry; apply Z.leb_le; exact Et).
      unfold PGSZ, MMAX, MMAP_THRESHOLD, IB, UNIT in *. repeat split; lia.
Qed.
Theorem driver_pack3 data : leaves (fun r => match fst r with
  | DL_run _ _ _ => exists d, drv_pb d /\
      res_ok_pack3 (snd r) (PB3 (pb_live d) (pb_bytes d) (repeat 64 49) [] (repeat 27 49))
  | _ => True end) (driver_tree data).
Proof.
  unfold driver_tree, driver_m.
  assert (R0 : room (RB 0 0 0 0) CAP0).
  { unfold room, CAP0. cbn -[Z.le Z.lt Z.add Z.mul Z.max Z.pow Z.div]. unfold MG_LIVE, MG_SLOTS, MG_REQ, MMAX, PGSZ, shcap, METAS_PER_AREA, page_round, IB, UNIT, PGSZ. cbn. lia. }
  eapply leaves_mbind; [apply (malloc_leaves_res init_state (RB 0 0 0 0) CAP0 wf_init res_ok_init R0)|].
  assert (HmdC : mdelta CAP0 = MMAX) by (apply mdelta_small; unfold CAP0, MMAP_THRESHOLD; lia).
  intros [b0|] s1 tr1 Hy1 [[HW1 Hb] HR1]; cbn [fst snd] in HW1, Hb, HR1.
  2:{ apply leaves_ret. exact I. }
  destruct Hb as (l1 & l2 & E1 & _).
  assert (Hin1 : In (b0, CAP0) (user_blocks s1)) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
  assert (HP1 : PK13 s1 CAP0).
  { assert (Hc : forall k, 0 <= k < 49 -> 0 <= znth k (repeat 64 49) /\ 0 <= znth k (repeat 27 49))
      by (intros k Hk; rewrite (proj2 (pk0_ok k Hk)), (pk27_ok k Hk); lia).
    apply (malloc_pack3_yields init_state (PB3 (repeat 0 49) 0 (repeat 64 49) [] (repeat 27 49)) CAP0 tr1 b0 s1 wf_init
      (res_ok_pack3_init (repeat 64 49) (repeat 27 49) eq_refl eq_refl Hc)).
    - apply room64_3; [| unfold CAP0; lia | unfold CAP0; lia]. intros k Hk. rewrite (proj1 (pk0_ok k Hk)). lia.
    - exact Hy1.
    - cbn [p3_cap p3_mcap]. pose proof GALL3_c27. destruct HR1 as (_ & _ & _ & Hh & _).
      unfold rb_malloc in Hh. cbn [rb_hand] in Hh. lia. }
  assert (HRP : RPinv 0 1 CAP0 (rb_malloc (RB 0 0 0 0) CAP0)).
  { unfold RPinv, rb_malloc. cbn -[mdelta]. rewrite HmdC. unfold PGSZ. repeat split; lia. }
  assert (Hcf : 0 + capflag CAP0 <= 2 ^ 24) by (unfold capflag, CAP0, MMAP_THRESHOLD, MMAX; cbn; lia).
  pose proof (read_phase_res READ_FUEL (dlen data) CAP0 16 b0 s1 (rb_malloc (RB 0 0 0 0) CAP0) 0 1 HW1 Hin1
    eq_refl ltac:(lia) ltac:(unfold CAP0, MAX_INPUT; lia) HR1 HRP Hcf ltac:(lia) ltac:(unfold READ_FUEL; cbn; lia)) as HL1.
  pose proof (read_phase_pack3 READ_FUEL (dlen data) CAP0 16 b0 s1 (rb_malloc (RB 0 0 0 0) CAP0) 0 1 HW1 Hin1
    eq_refl ltac:(lia) ltac:(unfold CAP0, MAX_INPUT; lia) HR1 HRP Hcf ltac:(lia) ltac:(unfold READ_FUEL; cbn; lia) HP1) as HL2.
  eapply leaves_mbind; [exact (leaves_and _ _ _ HL1 HL2)|].
  intros rd s2 tr2 Hy2 [Hr Hp]. cbn [fst snd] in Hr, Hp.
  assert (Hfl : capflag CAP0 = MMAX) by reflexivity. rewrite Hfl in Hr. unfold READ_FUEL in Hr.
  destruct rd as [ | | buf cap]; [apply leaves_ret; exact I | apply leaves_ret; exact I |].
  change (PK13 s2 cap) in Hp.
  destruct Hr as (HW2 & HL & Hmax & b' & HR2 & (V1 & V2 & V3 & V4 & V5)).
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in V1, V2, V3, V4, V5.
  assert (Hdl : 0 <= dlen data) by (unfold dlen; lia).
  assert (Hcap0 : 0 <= cap) by lia.
  pose proof (AllocPackRoom.band_range cap Hcap0) as Hbc.
  destruct (pk1_ok (band cap) Hbc) as (P1 & P2 & P3).
  destruct (dlen data <? HDR_MIN); [apply leaves_ret; exact I|].
  destruct (dlen data <? HDR_MIN + config_len data) eqn:E6; [apply leaves_ret; exact I|].
  destruct (payload_len data =? 0) eqn:Ep.
  { apply leaves_ret. cbn [fst snd]. exists (PB (lv_add (repeat 0 49) (band cap) 1) cap (repeat 64 49)). split; [|exact Hp].
    unfold drv_pb. cbn [pb_live pb_bytes]. split; [exact P1|]. split; [intros k Hk; exact (proj1 (P2 k Hk))|].
    unfold PDRV_LIVE, PDRV_BYTES, MAX_INPUT in *. split; lia. }
  assert (Hpl : 0 <= payload_len data < cap).
  { unfold payload_len, HDR_MIN in *. apply Z.ltb_ge in E6. pose proof (Z.mod_pos_bound (cfg_word data) 32768 ltac:(lia)). unfold config_len in *. lia. }
  pose proof (mdelta_le (payload_len data) ltac:(lia)) as Hmdp.
  pose proof (mdelta_le cap ltac:(lia)) as Hmd.
  pose proof (shcap_845 (rb_hand b') ltac:(lia)) as SC.
  eapply leaves_mbind.
  { apply (malloc_leaves_res s2 b' (payload_len data) HW2 HR2). unfold room.
    pose proof (page_round_bounds (payload_len data + IB + UNIT) ltac:(unfold IB, UNIT; lia)).
    unfold MG_LIVE, MG_SLOTS, MG_REQ, MAX_INPUT, MMAX, IB, UNIT, PGSZ in *.
    assert (rb_brk b' / 4096 <= 2 * 12) by (apply Z.div_le_upper_bound; lia).
    repeat split; try lia. }
  intros [q|] s3 tr3 Hy3 [[HW3 _] HR3]; cbn [fst snd] in HR3; apply leaves_ret; cbn [fst snd]; [|exact I].
  pose proof (AllocPackRoom.band_range (payload_len data) ltac:(lia)) as Hbp.
  pose proof (malloc_pack3_yields s2 _ (payload_len data) tr3 q s3 HW2 Hp) as HP3.
  exists (pb_malloc (PB (lv_add (repeat 0 49) (band cap) 1) cap (repeat 64 49)) (payload_len data)).
  split.
  - destruct (pk2_ok (band cap) (band (payload_len data)) Hbc Hbp) as (Q1 & Q2 & Q3).
    unfold drv_pb, pb_malloc. cbn [pb_live pb_bytes]. split; [exact Q1|]. split; [exact Q2|].
    unfold PDRV_LIVE, PDRV_BYTES, MAX_INPUT in *. split; lia.
  - apply HP3.
    + apply room64_3; [| unfold MAX_INPUT in *; lia | unfold MAX_INPUT in *; lia].
      intros k Hk. exact (proj2 (P2 k Hk)).
    + exact Hy3.
    + cbn [p3_cap p3_mcap]. pose proof GALL3_c27. destruct HR3 as (_ & _ & _ & Hh & _).
      unfold rb_malloc in Hh. cbn [rb_hand] in Hh. lia.
Qed.
