From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Arr
  Tac Bytes ZBridge Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel SlotNeeds_c GrantSlotPlan SlotBridge
  LLVMFuzzerTestOneInput_c Seg_sched_lib memset_c reac_headamp_tx_arm_scene_c reac_headamp_tx_set_resweep_c
  NextLemmas GrantModel HeadampSched SegSetModel.
Import ListNotations.
Open Scope Z_scope.

Lemma lor8 : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 ->
  Z.lor (Z.shiftl hi 8 mod 18446744073709551616) lo = lo + 256 * hi.
Proof.
  intros lo hi Hlo Hhi.
  pose proof (brute 256 (fun hi => forallb (fun lo =>
    Z.eqb (Z.lor (Z.shiftl hi 8 mod 18446744073709551616) lo) (lo + 256 * hi)) (zfrom 0 (Z.to_nat 256)))
    ltac:(vm_compute; reflexivity) hi Hhi) as H.
  cbv beta in H. pose proof (brute 256 _ H lo Hlo) as H2. cbv beta in H2. apply Z.eqb_eq in H2. exact H2.
Qed.

Lemma fr_mod : forall fr, 0 <= fr < 65536 ->
  fr - Z.lor (Z.shiftl (Z.shiftr (fr * 4502500384112656) 64 mod 18446744073709551616) 12 mod 18446744073709551616)
             (Z.shiftr (fr * 4502500384112656) 64 mod 18446744073709551616) = fr mod 4097.
Proof.
  intros fr Hfr.
  pose proof (brute 65536 (fun fr => Z.eqb
    (fr - Z.lor (Z.shiftl (Z.shiftr (fr * 4502500384112656) 64 mod 18446744073709551616) 12 mod 18446744073709551616)
               (Z.shiftr (fr * 4502500384112656) 64 mod 18446744073709551616)) (fr mod 4097))
    ltac:(vm_compute; reflexivity) fr Hfr) as H.
  cbv beta in H. apply Z.eqb_eq in H. exact H.
Qed.

Definition bat (pl : list byte) (k : nat) : Z := if (k <? length pl)%nat then pbz pl k else 0.
Definition bx (x : slot_ctx) (k : nat) : Z := bat (x_pl x) (pos_raw (x_pl x) + k).

Lemma bat_range : forall pl k, 0 <= bat pl k < 256.
Proof. intros. unfold bat. destruct (k <? length pl)%nat; [unfold pbz; apply byte_range | lia]. Qed.

Lemma bat_in : forall pl k, (k < length pl)%nat -> bat pl k = pbz pl k.
Proof. intros pl k H. unfold bat. rewrite (proj2 (Nat.ltb_lt _ _) H). reflexivity. Qed.

Lemma bat_out : forall pl k, (length pl <= k)%nat -> bat pl k = 0.
Proof. intros pl k H. unfold bat. rewrite (proj2 (Nat.ltb_ge _ _) H). reflexivity. Qed.

Lemma pos_raw_le : forall pl, (pos_raw pl <= length pl)%nat.
Proof.
  intros pl. unfold pos_raw, raw_rd.
  pose proof (cells_upto_le pl (Z.to_nat (nset pl))) as H0. change (snd (cells_upto pl (Z.to_nat (nset pl)))) with (pos_end pl) in H0.
  pose proof (rd8_le pl (pos_end pl) H0) as H1. destruct (rd8 pl (pos_end pl)) as [rb p1]. cbn [snd] in H1.
  pose proof (rd8_le pl p1 H1) as H2. destruct (rd8 pl p1) as [rw p2]. cbn [snd] in H2. exact H2.
Qed.

Lemma rd8_step : forall pl r k, (r <= length pl)%nat ->
  rd8 pl (Nat.min (r + k) (length pl)) = (bat pl (r + k), Nat.min (r + S k) (length pl)).
Proof.
  intros pl r k Hr. unfold rd8, bat. destruct (Nat.ltb_spec (r + k) (length pl)) as [L|L].
  - rewrite Nat.min_l by lia. rewrite (proj2 (Nat.ltb_lt _ _) L). f_equal. lia.
  - rewrite Nat.min_r by lia. rewrite Nat.ltb_irrefl. f_equal. lia.
Qed.

Lemma rd8_first : forall pl r, (r <= length pl)%nat -> rd8 pl r = (bat pl (r + 0), Nat.min (r + 1) (length pl)).
Proof.
  intros pl r Hr. rewrite <- (rd8_step pl r 0 Hr). f_equal. lia.
Qed.

Lemma sched_rd_bat : forall pl,
  let '(sb, sw, per, f, _) := sched_rd pl in
  sb = bat pl (pos_raw pl) /\ sw = bat pl (pos_raw pl + 1) /\
  per = bat pl (pos_raw pl + 2) + 256 * bat pl (pos_raw pl + 3) +
        65536 * (bat pl (pos_raw pl + 4) + 256 * bat pl (pos_raw pl + 5)) /\
  f = (bat pl (pos_raw pl + 6) + 256 * bat pl (pos_raw pl + 7)) mod 4097.
Proof.
  intros pl. pose proof (pos_raw_le pl) as HR. unfold sched_rd, rd32, rd16.
  set (R := pos_raw pl) in *.
  rewrite (rd8_first pl R HR). cbv beta iota zeta.
  rewrite (rd8_step pl R 1 HR). cbv beta iota zeta.
  rewrite (rd8_step pl R 2 HR). cbv beta iota zeta.
  rewrite (rd8_step pl R 3 HR). cbv beta iota zeta.
  rewrite (rd8_step pl R 4 HR). cbv beta iota zeta.
  rewrite (rd8_step pl R 5 HR). cbv beta iota zeta.
  rewrite (rd8_step pl R 6 HR). cbv beta iota zeta.
  rewrite (rd8_step pl R 7 HR). cbv beta iota zeta.
  rewrite Nat.add_0_r. repeat split; lia.
Qed.

Lemma T_sched0_bx : forall x,
  T_sched0 (x_pl x) = set_resweep_T (Tarm (T_end (x_pl x)) (bx x 0) (bx x 1))
    (Z_to_bv 64 (bx x 2 + 256 * bx x 3 + 65536 * (bx x 4 + 256 * bx x 5))).
Proof.
  intros x. unfold T_sched0, Tarm, bx. pose proof (sched_rd_bat (x_pl x)) as H.
  destruct (sched_rd (x_pl x)) as [[[[sb sw] per] f] p4]. destruct H as (-> & -> & -> & _).
  rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma frames_bx : forall x, frames (x_pl x) = (bx x 6 + 256 * bx x 7) mod 4097.
Proof.
  intros x. unfold frames, bx. pose proof (sched_rd_bat (x_pl x)) as H.
  destruct (sched_rd (x_pl x)) as [[[[sb sw] per] f] p4]. destruct H as (_ & _ & _ & ->). reflexivity.
Qed.

Lemma sbw_bx : forall x, let '(sb', sw', _, _, _) := sched_rd (x_pl x) in sb' = bx x 0 /\ sw' = bx x 1.
Proof.
  intros x. unfold bx. pose proof (sched_rd_bat (x_pl x)) as H.
  destruct (sched_rd (x_pl x)) as [[[[sb sw] per] f] p4]. destruct H as (-> & -> & _). rewrite Nat.add_0_r. split; reflexivity.
Qed.

Lemma pl_read : forall m p pl (i : nat), rw_cells rsegs m p [CB (length pl) pl] -> (i < length pl)%nat ->
  ov_read_bytes rsegs m (wa (p + Z.of_nat i)) 1 = Some [nth i pl (Z_to_bv 8 0)].
Proof.
  intros m p pl i H Hi. destruct (cb_u8 _ _ _ _ H) as [U _].
  apply (u8arr_read rsegs m p pl (Z.of_nat i)); [exact U | | lia | reflexivity].
  rewrite Nat2Z.id. apply nth_error_nth'. exact Hi.
Qed.

Lemma lor256 : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> Z.lor (256 * hi) lo = lo + 256 * hi.
Proof.
  intros lo hi Hlo Hhi.
  pose proof (brute 256 (fun hi => forallb (fun lo => Z.eqb (Z.lor (256 * hi) lo) (lo + 256 * hi))
    (zfrom 0 (Z.to_nat 256))) ltac:(vm_compute; reflexivity) hi Hhi) as H.
  cbv beta in H. pose proof (brute 256 _ H lo Hlo) as H2. cbv beta in H2. apply Z.eqb_eq in H2. exact H2.
Qed.

Lemma land_low_high : forall lo k, 0 <= lo < 65536 -> Z.land lo (Z.shiftl k 16) = 0.
Proof.
  intros lo k Hlo. apply Z.bits_inj_0. intros n. rewrite Z.land_spec.
  destruct (Z_lt_le_dec n 16) as [L|L].
  - destruct (Z_lt_le_dec n 0) as [N|N]; [rewrite Z.testbit_neg_r by lia; reflexivity|].
    rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
  - replace lo with (lo mod 2 ^ 16) by (apply Z.mod_small; lia). rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma lor_per : forall lo hi, 0 <= lo < 65536 -> 0 <= hi < 65536 ->
  Z.lor lo (bv_swrap 32 (Z.shiftl hi 16) mod 18446744073709551616) mod 4294967296 =
  (lo + 65536 * hi) mod 4294967296.
Proof.
  intros lo hi Hlo Hhi.
  set (Y := bv_swrap 32 (Z.shiftl hi 16) mod 18446744073709551616).
  assert (HY0 : Y mod 65536 = 0).
  { unfold Y. rewrite Z.shiftl_mul_pow2 by lia. unfold bv_swrap, bv_wrap.
    change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
    change (2 ^ 16) with 65536. Z.div_mod_to_equations. lia. }
  assert (HYp : 0 <= Y) by (unfold Y; apply Z.mod_pos_bound; lia).
  assert (HY : Y = Z.shiftl (Y / 65536) 16).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536. pose proof (Z.div_mod Y 65536 ltac:(lia)). lia. }
  assert (H0 : Z.land lo Y = 0) by (rewrite HY; apply land_low_high; lia).
  rewrite <- (Z.lxor_lor lo Y H0), <- (Z.add_nocarry_lxor lo Y H0).
  unfold Y. rewrite Zplus_mod, mod64_mod32, swrap32_mod32, <- Zplus_mod.
  rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia.
Qed.

Lemma u64_mod32 : forall z, bv_unsigned (Z_to_bv 64 z) mod 4294967296 = z mod 4294967296.
Proof. intros z. rewrite unsigned_lit_wrap. change (2 ^ 64) with 18446744073709551616. apply mod64_mod32. Qed.


Lemma t4_of_16 : forall t, t mod 16 = 0 -> t mod 4 = 0.
Proof. intros t H. Z.div_mod_to_equations. lia. Qed.

Lemma flag_and : forall sb sw, 0 <= sw ->
  Z.land (Z.b2z (sb <? 48)) (Z.b2z (0 <? sw)) = (if negb (sw =? 0) && (sb <? 48) then 1 else 0).
Proof.
  intros sb sw Hsw. destruct (Z.ltb_spec sb 48), (Z.ltb_spec 0 sw), (Z.eqb_spec sw 0); try lia; reflexivity.
Qed.

Ltac tail2_close :=
  first [ assumption | lia | apply byte_range | unfold blk; lia ].

Ltac sbr :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?C then _ else _) _ _ _ _) =>
      let HC := fresh "HC" in destruct C eqn:HC; zify_cond HC; try (exfalso; lia)
  end.

Lemma tail2 : memset_contract -> forall x t ms0
  (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m lo hi sb sw,
  0 <= lo < 256 -> 0 <= hi < 256 -> 0 <= sb < 256 -> 0 <= sw < 256 ->
  frames (x_pl x) = (lo + 256 * hi) mod 4097 ->
  (let '(sb', sw', _, _, _) := sched_rd (x_pl x) in sb' = sb /\ sw' = sw) ->
  rw_cells rsegs m (x_p x) [CB (length (x_pl x)) (x_pl x)] ->
  stk rsegs m (x_S x - LLVM_STACK) (x_S x) -> mem_inv rsegs m ->
  bytes_at rsegs m CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES -> CTRL_HEADAMP_ROW + 24 <= x_S x - LLVM_STACK ->
  (x_p x + x_n x <= CTRL_HEADAMP_ROW \/ CTRL_HEADAMP_ROW + 24 <= x_p x) ->
  rw_cells rsegs m (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x])) ->
  rw_cells rsegs m t [CB 460 (T_sched0 (x_pl x))] -> I1 (T_sched0 (x_pl x)) ->
  rw_cells rsegs m (SPL x + 360) [CB 144 (ws_end (x_pl x))] ->
  rw_cells rsegs m (SPL x + 216) [CB 144 (st_end (x_pl x))] ->
  length (ws_end (x_pl x)) = 144%nat -> length (st_end (x_pl x)) = 144%nat ->
  Hrel (T_end (x_pl x)) (ws_end (x_pl x)) (st_end (x_pl x)) ->
  x_S x mod 16 = 0 -> length (x_sv x) = 12%nat -> x_S x < 2 ^ 63 ->
  0 < x_p x -> x_p x + x_n x < 2 ^ 63 -> (x_p x + x_n x <= x_S x - LLVM_STACK \/ x_S x <= x_p x) ->
  x_n x < 2 ^ 26 -> blk x t 460 -> t mod 16 = 0 ->
  munch ((x_S x - LLVM_STACK, x_S x) :: [(t, t + 460)]) (ms_mem ms0) m -> wmono rsegs (ms_mem ms0) m ->
  evt rsegs (fun ms' => kept x [(t, t + 460)] ms0 ms' /\
    ((frames (x_pl x) = 0 /\ At_freeT x t ms') \/ (0 < frames (x_pl x) /\ At_sched x t 0 ms')))
    (MS (mkR ra (Z_to_bv 64 (SPL x)) (x_gp x) (x_tp x) t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 sb)
             (Z_to_bv 64 lo) (Z_to_bv 64 hi) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 sw) s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        (x_F x) (Z_to_bv 64 0x13b24) (x_fc x) None m (seg_rom rsegs)).
Proof.
  intros MEMSET x t ms0 ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m lo hi sb sw
    Hlo Hhi Hsb Hsw HFR HSR HP HS HMI Hrow Hrs Hrp HSV HT HI1 HWS HST HLW HLS0 HH HS16 Hsv12 HS63 Hp0 Hpn Hpd Hn HBLK
    Ht16 MU WM.
  assert (HSPL : SPL x = x_S x - 608) by reflexivity.
  assert (HLS : LLVM_STACK = 8800) by reflexivity.
  assert (ELR : length CTRL_HEADAMP_BYTES = 24%nat) by reflexivity.
  assert (Hxn : x_n x = Z.of_nat (length (x_pl x))) by reflexivity.
  remember (map C8 (rev (x_sv x) ++ [x_ra x])) as SVC eqn:ESVC.
  assert (HSVC : cells_size SVC = 104%nat) by (subst SVC; rewrite cells_size_C8, length_app, length_rev, Hsv12; reflexivity).
  unfold blk in HBLK.
  pose proof HS as (HS0 & HS0' & _).
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite lor8 by lia. rewrite fr_mod by lia.
  zstep. zstep. zstep. zstep.
  destruct (stk_split3 m _ _ (SPL x + 66) 144 HS ltac:(lia) ltac:(lia)) as (HS1 & (junk & HJ) & HS2). clear HS.
  call (memset_call MEMSET (SPL x + 66) 144 junk).
  1-3: reflexivity.
  1-2: lia. exact HJ. exact HMI.
  match goal with H : rw_cells rsegs ?mm (SPL x + 66) [CB 144 _] |- _ =>
    pose proof (stk_merge3 _ _ _ _ _ _ _ HS1 H HS2 ltac:(lia) ltac:(lia) ltac:(lia)) as HS end.
  pose proof (sched0_ok (x_pl x)) as [_ HL0].
  pose proof (Z.mod_pos_bound (lo + 256 * hi) 4097 ltac:(lia)) as HM.
  rewrite <- HFR in *.
  zstep. if_cases HC1; zify_cond HC1.
  - apply evt_done. split.
    + split; cbn [ms_mem MS]; assumption.
    + left. split; [lia|]. unfold At_freeT, body, common.
      cbn [ms_mem ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom MS].
      subst SVC. repeat match goal with |- _ /\ _ => split end; try reflexivity; try assumption; try lia.
  - match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_cell mm _ _ (SPL x + 48) 8 HS ltac:(lia) ltac:(lia)) as [junk48 C48] end.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (swrap32_id (0 - frames (x_pl x))) by lia.
    rewrite ?wnot_lxor in * by lia.
    apply evt_done. split.
    + split; cbn [ms_mem MS]; assumption.
    + right. split; [lia|]. unfold At_sched, sched_flag, body, common, table, arrays.
      destruct (sched_rd (x_pl x)) as [[[[sb' sw'] per'] f'] p'] eqn:ESR. destruct HSR as [<- <-].
      change (sched_at (x_pl x) t 0) with (T_sched0 (x_pl x), Z144). cbv iota beta.
      cbn [ms_mem ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom MS].
      rewrite flag_and by lia.
      subst SVC. repeat match goal with |- _ /\ _ => split end; try reflexivity; try assumption; try lia.
      all: rewrite (Z.add_comm sb' sw'); reflexivity.
Qed.

Lemma tail1 : memset_contract -> reac_headamp_tx_set_resweep_contract -> forall x t ms0
  (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m q e,
  s3 = Z_to_bv 64 (x_p x + q) -> s1 = Z_to_bv 64 (bx x 0) -> s2 = Z_to_bv 64 (bx x 1) -> s9 = Z_to_bv 64 e ->
  a0 = Z_to_bv 64 (bx x 2) -> a1 = Z_to_bv 64 (256 * bx x 3) ->
  a2 = Z_to_bv 64 (bx x 4) -> a3 = Z_to_bv 64 (256 * bx x 5) ->
  (e = 0 /\ x_n x <= Z.of_nat (pos_raw (x_pl x)) + 6 \/
   0 < e /\ q = Z.of_nat (pos_raw (x_pl x)) + 6 /\ q + e = x_n x) ->
  rw_cells rsegs m (x_p x) [CB (length (x_pl x)) (x_pl x)] ->
  stk rsegs m (x_S x - LLVM_STACK) (x_S x) -> mem_inv rsegs m ->
  bytes_at rsegs m CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES -> CTRL_HEADAMP_ROW + 24 <= x_S x - LLVM_STACK ->
  (x_p x + x_n x <= CTRL_HEADAMP_ROW \/ CTRL_HEADAMP_ROW + 24 <= x_p x) ->
  rw_cells rsegs m (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x])) ->
  rw_cells rsegs m t [CB 460 (Tarm (T_end (x_pl x)) (bx x 0) (bx x 1))] ->
  rw_cells rsegs m (SPL x + 360) [CB 144 (ws_end (x_pl x))] ->
  rw_cells rsegs m (SPL x + 216) [CB 144 (st_end (x_pl x))] ->
  length (ws_end (x_pl x)) = 144%nat -> length (st_end (x_pl x)) = 144%nat ->
  Hrel (T_end (x_pl x)) (ws_end (x_pl x)) (st_end (x_pl x)) ->
  x_S x mod 16 = 0 -> length (x_sv x) = 12%nat -> x_S x < 2 ^ 63 ->
  0 < x_p x -> x_p x + x_n x < 2 ^ 63 -> (x_p x + x_n x <= x_S x - LLVM_STACK \/ x_S x <= x_p x) ->
  x_n x < 2 ^ 26 -> blk x t 460 -> t mod 16 = 0 ->
  munch ((x_S x - LLVM_STACK, x_S x) :: [(t, t + 460)]) (ms_mem ms0) m -> wmono rsegs (ms_mem ms0) m ->
  evt rsegs (fun ms' => kept x [(t, t + 460)] ms0 ms' /\
    ((frames (x_pl x) = 0 /\ At_freeT x t ms') \/ (0 < frames (x_pl x) /\ At_sched x t 0 ms')))
    (MS (mkR ra (Z_to_bv 64 (SPL x)) (x_gp x) (x_tp x) t0 t1 t2 (Z_to_bv 64 t) s1
             a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        (x_F x) (Z_to_bv 64 0x13ad8) (x_fc x) None m (seg_rom rsegs)).
Proof.
  intros MEMSET RSW x t ms0 ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m q e
    -> -> -> -> -> -> -> -> He HP HS HMI Hrow Hrs Hrp HSV HT HWS HST HLW HLS0 HH HS16 Hsv12 HS63 Hp0 Hpn Hpd Hn HBLK
    Ht16 MU WM.
  assert (HSPL : SPL x = x_S x - 608) by reflexivity.
  assert (HLS : LLVM_STACK = 8800) by reflexivity.
  assert (ELR : length CTRL_HEADAMP_BYTES = 24%nat) by reflexivity.
  assert (Hxn : x_n x = Z.of_nat (length (x_pl x))) by reflexivity.
  assert (Ht4 : t mod 4 = 0) by (apply t4_of_16; exact Ht16).
  remember (map C8 (rev (x_sv x) ++ [x_ra x])) as SVC eqn:ESVC.
  assert (HSVC : cells_size SVC = 104%nat) by (subst SVC; rewrite cells_size_C8, length_app, length_rev, Hsv12; reflexivity).
  unfold blk in HBLK.
  pose proof HS as (HS0 & HS0' & _).
  pose proof (pos_raw_le (x_pl x)) as HR.
  pose proof (bat_range (x_pl x) (pos_raw (x_pl x) + 2)) as B2.
  pose proof (bat_range (x_pl x) (pos_raw (x_pl x) + 3)) as B3.
  pose proof (bat_range (x_pl x) (pos_raw (x_pl x) + 4)) as B4.
  pose proof (bat_range (x_pl x) (pos_raw (x_pl x) + 5)) as B5.
  pose proof (bat_range (x_pl x) (pos_raw (x_pl x) + 0)) as B0.
  pose proof (bat_range (x_pl x) (pos_raw (x_pl x) + 1)) as B1.
  pose proof (frames_bx x) as HFR. pose proof (sbw_bx x) as HSR. pose proof (T_sched0_bx x) as HT0.
  pose proof (sched0_ok (x_pl x)) as [HI0 HL0].
  unfold bx in *.
  set (b0 := bat (x_pl x) (pos_raw (x_pl x) + 0)) in *.
  set (b1 := bat (x_pl x) (pos_raw (x_pl x) + 1)) in *.
  set (b2 := bat (x_pl x) (pos_raw (x_pl x) + 2)) in *.
  set (b3 := bat (x_pl x) (pos_raw (x_pl x) + 3)) in *.
  set (b4 := bat (x_pl x) (pos_raw (x_pl x) + 4)) in *.
  set (b5 := bat (x_pl x) (pos_raw (x_pl x) + 5)) in *.
  zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite (lor256 b2 b3), (lor256 b4 b5) by lia.
  call (rsw_call RSW t (b2 + 256 * b3 + 65536 * (b4 + 256 * b5)) (Tarm (T_end (x_pl x)) b0 b1)).
  { reflexivity. }
  { rewrite u64_mod32, lor_per by lia. try (f_equal; lia). }
  { exact HT. }
  { exact HMI. }
  { lia. }
  { exact Ht4. }
  rewrite <- HT0 in *.
  zstep. sbr.
  - assert (E0 : e = 0) by lia.
    assert (H6 : bat (x_pl x) (pos_raw (x_pl x) + 6) = 0) by (apply bat_out; lia).
    assert (H7 : bat (x_pl x) (pos_raw (x_pl x) + 7) = 0) by (apply bat_out; lia).
    rewrite H6, H7 in HFR.
    zstep. zstep.
    eapply (tail2 MEMSET x t ms0); try exact HFR; try subst SVC; tail2_close.
  - assert (Hq : q = Z.of_nat (pos_raw (x_pl x)) + 6 /\ q + e = x_n x) by lia. destruct Hq as [Hq Hqe].
    match goal with H : rw_cells rsegs ?mm (x_p x) _ |- _ =>
      pose proof (pl_read mm (x_p x) (x_pl x) (pos_raw (x_pl x) + 6) H ltac:(lia)) as RD6 end.
    zstep. zstep. zstep. sbr. zstep. zstep. sbr.
    + assert (H6 : bat (x_pl x) (pos_raw (x_pl x) + 6) = pbz (x_pl x) (pos_raw (x_pl x) + 6)) by (apply bat_in; lia).
      assert (H7 : bat (x_pl x) (pos_raw (x_pl x) + 7) = 0) by (apply bat_out; lia).
      rewrite H6, H7 in HFR. unfold pbz in HFR.
      zstep.
      eapply (tail2 MEMSET x t ms0); try exact HFR; try subst SVC; tail2_close.
    + match goal with H : rw_cells rsegs ?mm (x_p x) _ |- _ =>
        pose proof (pl_read mm (x_p x) (x_pl x) (pos_raw (x_pl x) + 7) H ltac:(lia)) as RD7 end.
      assert (H6 : bat (x_pl x) (pos_raw (x_pl x) + 6) = pbz (x_pl x) (pos_raw (x_pl x) + 6)) by (apply bat_in; lia).
      assert (H7 : bat (x_pl x) (pos_raw (x_pl x) + 7) = pbz (x_pl x) (pos_raw (x_pl x) + 7)) by (apply bat_in; lia).
      rewrite H6, H7 in HFR. unfold pbz in HFR.
      zstep. zstep. zstep. sbr. zstep. zstep.
      eapply (tail2 MEMSET x t ms0); try exact HFR; try subst SVC; tail2_close.
Qed.

Lemma bx_in : forall x k, (pos_raw (x_pl x) + k < length (x_pl x))%nat ->
  bv_unsigned (nth (pos_raw (x_pl x) + k) (x_pl x) (Z_to_bv 8 0)) = bx x k.
Proof. intros x k H. unfold bx. rewrite bat_in by exact H. reflexivity. Qed.

Lemma bx_out : forall x k, (length (x_pl x) <= pos_raw (x_pl x) + k)%nat -> bx x k = 0.
Proof. intros x k H. unfold bx. apply bat_out. exact H. Qed.

Lemma bx_range : forall x k, 0 <= bx x k < 256.
Proof. intros x k. unfold bx. apply bat_range. Qed.

Ltac sdrive :=
  repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 80600) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 87588) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => sbr
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    end).

Ltac bxr := rewrite ?bx_in by lia.

Ltac sgoal :=
  first [ reflexivity | assumption | lia
        | (bxr; rewrite ?Z.shiftl_mul_pow2 by lia; word_eq_tac)
        | (match goal with ES : ?S = map C8 _ |- _ => subst S; assumption end) ].

Ltac rdk mm k :=
  match goal with H : rw_cells rsegs mm (x_p ?x) _ |- _ =>
    let R := fresh "RD" in pose proof (pl_read mm (x_p x) (x_pl x) (pos_raw (x_pl x) + k) H ltac:(lia)) as R end.


Theorem seg_sched_setup_holds : reac_headamp_tx_arm_scene_contract -> reac_headamp_tx_set_resweep_contract ->
  memset_contract -> seg_sched_setup.
Proof.
  intros ARM RSW MEMSET. unfold seg_sched_setup. intros x t ms H.
  apply evt_canon; [eqv_inv_tac|].
  destruct H as (((Hpc & HF & Hfc & Hrv & Hsvc & Hro & Hgp & Htp & HPL & HST & HMI & Hp0 & Hpn & Hpd & Hrow & Hrs & Hrp) &
                  Hsp & HSV & HS16 & Hsv12 & HS63) &
                 Hn & Hs0 & (Hs5 & Hs9) & (HTb & HT16 & HTl & HT) & (Hwl & Hstl & HWS & HSTA) & HHr & HI1).
  rewrite canon_rg by exact Hsvc.
  rewrite Hpc, HF, Hfc, Hrv, Hro, Hs0, Hs5, Hs9, Hsp, Hgp, Htp.
  unfold w64, PC_FREE_SW2_RET.
  set (m00 := ms_mem ms) in *.
  assert (MU : munch [(x_S x - LLVM_STACK, x_S x); (t, t + 460)] m00 m00) by apply munch_refl.
  assert (WM : wmono rsegs m00 m00) by apply wmono_refl.
  pose proof HTb as HTb'. unfold blk in HTb'.
  assert (ELS : LLVM_STACK = 8800) by reflexivity.
  assert (Ht4 : t mod 4 = 0) by (apply t4_of_16; exact HT16).
  assert (ELR : length CTRL_HEADAMP_BYTES = 24%nat) by reflexivity.
  assert (ESPL : SPL x = x_S x - 608) by reflexivity.
  assert (Exn : x_n x = Z.of_nat (length (x_pl x))) by reflexivity.
  remember (map C8 (rev (x_sv x) ++ [x_ra x])) as SVC eqn:ESVC.
  assert (HSVC : cells_size SVC = 104%nat)
    by (subst SVC; rewrite cells_size_C8, length_app, length_rev, Hsv12; reflexivity).
  pose proof HST as (HS0 & HS0' & _).
  pose proof (pos_raw_le (x_pl x)) as HR.
  pose proof (bx_range x 0) as R0. pose proof (bx_range x 1) as R1. pose proof (bx_range x 2) as R2.
  pose proof (bx_range x 3) as R3. pose proof (bx_range x 4) as R4. pose proof (bx_range x 5) as R5.
  assert (CE : (length (x_pl x) = pos_raw (x_pl x) + 0)%nat \/ (length (x_pl x) = pos_raw (x_pl x) + 1)%nat \/
               (length (x_pl x) = pos_raw (x_pl x) + 2)%nat \/ (length (x_pl x) = pos_raw (x_pl x) + 3)%nat \/
               (length (x_pl x) = pos_raw (x_pl x) + 4)%nat \/ (length (x_pl x) = pos_raw (x_pl x) + 5)%nat \/
               (pos_raw (x_pl x) + 6 <= length (x_pl x))%nat) by lia.
  destruct CE as [CE|[CE|[CE|[CE|[CE|[CE|CE]]]]]].
  - pose proof (bx_out x 0 ltac:(lia)) as Z0. pose proof (bx_out x 1 ltac:(lia)) as Z1.
    pose proof (bx_out x 2 ltac:(lia)) as Z2. pose proof (bx_out x 3 ltac:(lia)) as Z3.
    pose proof (bx_out x 4 ltac:(lia)) as Z4. pose proof (bx_out x 5 ltac:(lia)) as Z5.
    sdrive.
    call (arm_call ARM t (bx x 0) (bx x 1) (T_end (x_pl x))).
    all: try sgoal.
    sdrive.
    eapply (tail1 MEMSET RSW x t ms) with (q := Z.of_nat (pos_raw (x_pl x))) (e := 0).
    all: sgoal.
  - pose proof (bx_out x 1 ltac:(lia)) as Z1.
    pose proof (bx_out x 2 ltac:(lia)) as Z2. pose proof (bx_out x 3 ltac:(lia)) as Z3.
    pose proof (bx_out x 4 ltac:(lia)) as Z4. pose proof (bx_out x 5 ltac:(lia)) as Z5.
    rdk m00 0%nat.
    sdrive.
    call (arm_call ARM t (bx x 0) (bx x 1) (T_end (x_pl x))).
    all: try sgoal.
    sdrive.
    eapply (tail1 MEMSET RSW x t ms) with (q := Z.of_nat (pos_raw (x_pl x)) + 1) (e := 0).
    all: sgoal.
  - pose proof (bx_out x 2 ltac:(lia)) as Z2. pose proof (bx_out x 3 ltac:(lia)) as Z3.
    pose proof (bx_out x 4 ltac:(lia)) as Z4. pose proof (bx_out x 5 ltac:(lia)) as Z5.
    rdk m00 0%nat. rdk m00 1%nat.
    sdrive.
    call (arm_call ARM t (bx x 0) (bx x 1) (T_end (x_pl x))).
    all: try sgoal.
    sdrive.
    eapply (tail1 MEMSET RSW x t ms) with (q := Z.of_nat (pos_raw (x_pl x)) + 2) (e := 0).
    all: sgoal.
  - pose proof (bx_out x 3 ltac:(lia)) as Z3.
    pose proof (bx_out x 4 ltac:(lia)) as Z4. pose proof (bx_out x 5 ltac:(lia)) as Z5.
    rdk m00 0%nat. rdk m00 1%nat.
    sdrive.
    call (arm_call ARM t (bx x 0) (bx x 1) (T_end (x_pl x))).
    all: try sgoal.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rdk mm 2%nat end.
    sdrive.
    eapply (tail1 MEMSET RSW x t ms) with (q := Z.of_nat (pos_raw (x_pl x)) + 3) (e := 0).
    all: sgoal.
  - pose proof (bx_out x 4 ltac:(lia)) as Z4. pose proof (bx_out x 5 ltac:(lia)) as Z5.
    rdk m00 0%nat. rdk m00 1%nat.
    sdrive.
    call (arm_call ARM t (bx x 0) (bx x 1) (T_end (x_pl x))).
    all: try sgoal.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rdk mm 2%nat; rdk mm 3%nat end.
    sdrive.
    eapply (tail1 MEMSET RSW x t ms) with (q := Z.of_nat (pos_raw (x_pl x)) + 4) (e := 0).
    all: sgoal.
  - pose proof (bx_out x 5 ltac:(lia)) as Z5.
    rdk m00 0%nat. rdk m00 1%nat.
    sdrive.
    call (arm_call ARM t (bx x 0) (bx x 1) (T_end (x_pl x))).
    all: try sgoal.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rdk mm 2%nat; rdk mm 3%nat; rdk mm 4%nat end.
    sdrive.
    eapply (tail1 MEMSET RSW x t ms) with (q := Z.of_nat (pos_raw (x_pl x)) + 5) (e := 0).
    all: sgoal.
  - rdk m00 0%nat. rdk m00 1%nat.
    sdrive.
    call (arm_call ARM t (bx x 0) (bx x 1) (T_end (x_pl x))).
    all: try sgoal.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rdk mm 2%nat; rdk mm 3%nat; rdk mm 4%nat; rdk mm 5%nat end.
    sdrive.
    eapply (tail1 MEMSET RSW x t ms) with (q := Z.of_nat (pos_raw (x_pl x)) + 6)
      (e := x_n x - Z.of_nat (pos_raw (x_pl x)) - 6).
    all: sgoal.
Qed.
