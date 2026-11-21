From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Zh_kit Z_infl_iface Z_itab_kit Z_itab_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_itab_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState Inftrees ItableModel ItableModel2 RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Definition tx_match (X : itx) : Z := it_match (tx_ty X).
Definition tx_extraA (X : itx) : Z := match tx_ty X with CODES => 0 | LENS => Z_LEXT | DISTS => Z_DEXT end.
Definition tx_baseA (X : itx) : Z := match tx_ty X with CODES => 0 | LENS => Z_LBASE | DISTS => Z_DBASE end.

Definition tx_flagA (X : itx) : Z := match tx_ty X with CODES => 0 | LENS => 1 | DISTS => 1 end.
(* [comment removed for export] *)
Definition notw (X : itx) : Z := 18446744073709551615 - (il_As (tx_L X) + 808).
Definition notc (X : itx) : Z := 18446744073709551615 - (bv_unsigned (tx_sp X) + -136).
Definition it_low (X : itx) (root : Z) (j2 : list byte) : list cell :=
  [C8 (wz (tx_extraA X)); C8 (wz (2 ^ root - 1)); C8 (wz (tx_baseA X)); C8 (wz (tx_flagA X)); C8 (wz (notw X)); CB 2 j2].
Record lscr : Type := mkLS {
  l1 : word; l6 : word; l7 : word; l9 : word; l16 : word; l18 : word; l19 : word; l20 : word; l21 : word; l22 : word;
  l23 : word; l25 : word; l26 : word; l27 : word; l28 : word; l29 : word; l30 : word; l31 : word }.
Definition ITL (X : itx) (root max : Z) (pc : Z) (q : lscr) (cnt wk tb : arr) : machine_state -> Prop :=
  fun ms => exists m j2 ofs,
    ms = MS (mkR (l27 q) (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) (wz max) (l6 q) (wz (tx_match X)) (l31 q)
                 (wz (bv_unsigned (tx_sp X) + -136))
                 (wz (ity_code (tx_ty X))) (wz (tx_lensA X)) (l7 q) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808))
                 (l16 q) (wz root) (l9 q) (l19 q) (l20 q) (l28 q) (l21 q) (l23 q) (l1 q) (wz (notc X)) (l25 q) (l26 q) (l18 q) (l22 q) (l29 q) (l30 q))
            (tx_F X) (wz pc) (tx_fc X) None m (seg_rom usegs)
    /\ ITM X (it_low X root j2) cnt ofs wk tb m.

Lemma ITL_intro : forall X root max pc cnt wk tb j2 ofs
    x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x2 = wz (bv_unsigned (tx_sp X) + -208) -> x3 = tx_gp X -> x4 = tx_tp X -> x5 = wz max -> x9 = wz (bv_unsigned (tx_sp X) + -136) ->
  x10 = wz (ity_code (tx_ty X)) -> x11 = wz (tx_lensA X) -> x7 = wz (tx_match X) -> x13 = wz (il_As (tx_L X) + 160) -> x14 = wz (tx_bitsA X) ->
  x15 = wz (il_As (tx_L X) + 808) -> x17 = wz root -> x25 = wz (notc X) -> F = tx_F X -> fc = tx_fc X ->
  ITM X (it_low X root j2) cnt ofs wk tb m ->
  ITL X root max pc (mkLS x24 x6 x12 x18 x16 x28 x19 x20 x22 x29 x23 x26 x27 x1 x21 x30 x31 x8) cnt wk tb
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (wz pc) fc None m (seg_rom usegs)).
Proof. intros. subst. unfold ITL. do 3 eexists. split; [reflexivity| eassumption]. Qed.
Lemma it_saved_bound : forall X m, rw_cells usegs m (bv_unsigned (tx_sp X) + -104) (it_saved X) ->
  104 <= bv_unsigned (tx_sp X) /\ bv_unsigned (tx_sp X) <= 2 ^ 64.
Proof. intros X m H. pose proof (rw_cells_bound usegs m _ _ H) as B. unfold it_saved in B. cbn [cells_size csize Nat.add Z.of_nat] in B. lia. Qed.
Ltac itl_open HL :=
  let m := fresh "m" in let j2 := fresh "jg" in
  let LOW := fresh "LOW" in let CNT := fresh "CNT" in let SAV := fresh "SAV" in let ST := fresh "ST" in
  let Gw := fresh "Gw" in let Gc := fresh "Gc" in let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in
  let L16w := fresh "L16w" in let L16c := fresh "L16c" in let BSP := fresh "BSP" in
  let ofs := fresh "ofs" in let OFS := fresh "OFS" in let L16o := fresh "L16o" in
  destruct HL as (m & j2 & ofs & -> & [LOW OFS CNT SAV ST Gw Gc MI MU WM]);
  unfold it_low in LOW; unfold tx_W1 in MU; unfold u16arr in Gw; pose proof (it_saved_bound _ m SAV) as BSP;
  lazymatch type of Gw with u8arr _ _ _ (u16s (av16 ?wk _)) => pose proof (av16_zlength wk 288 ltac:(lia)) as L16w end;
  lazymatch type of CNT with u8arr _ _ _ (u16s (av16 ?c _)) => pose proof (av16_zlength c 16 ltac:(lia)) as L16c end;
  pose proof (av16s_zlength ofs 1 15 ltac:(lia)) as L16o;
  cbn [l1 l6 l7 l9 l16 l18 l19 l20 l21 l22 l23 l25 l26 l27 l28 l29 l30 l31] in *.
Ltac treg :=
  first [ reflexivity | f_equal; lia
        | f_equal; rewrite ?bv_swrap32_id, ?wrap32_id, ?wrap64_id by lia; lia
        | apply Z_to_bv_eqm; rewrite ?wrap64_mod, ?wrap32_mod, ?Z.mod_mod by lia; first [ reflexivity | Z.div_mod_to_equations; lia ] ].
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition lowx (l : Z) : Z := if l =? 4294967295 then -1 else l.
Lemma zext32_x2 : forall x, 0 <= x < 4294967296 -> Z.land (x ≪ 32) 18446744073709551615 ≫ 31 = 2 * x.
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^32) with 4294967296. change (2^64) with 18446744073709551616. change (2^31) with 2147483648. Z.div_mod_to_equations. lia.
Qed.
Lemma zext32_x4' : forall x, 0 <= x < 4294967296 -> Z.land (x ≪ 32) 18446744073709551615 ≫ 30 = 4 * x.
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^32) with 4294967296. change (2^64) with 18446744073709551616. change (2^30) with 1073741824. Z.div_mod_to_equations. lia.
Qed.
Lemma Z8_of_wz : forall v, Z_to_bv 8 (bv_unsigned (wz v)) = Z_to_bv 8 v.
Proof.
  intros v. apply Z8_eqm'. rewrite unsigned_lit_wrap. apply Z.mod_mod_divide. exists 72057594037927936. reflexivity.
Qed.
Lemma extra_read : forall X m wk i, mem_inv usegs m -> u16arr usegs m (il_As (tx_L X) + 808) (av16 wk 288) ->
  0 <= i < it_ext_len (tx_ty X) 288 -> (tx_ty X = LENS -> i < 29) -> tx_ty X <> CODES ->
  ov_read_bytes usegs m (wa (tx_extraA X + 2 * i)) 1 = Some [Z_to_bv 8 (it_extra (tx_ty X) wk i)].
Proof.
  intros X m wk i MI [Hb _] Hi H29 HNC. unfold tx_extraA, it_extra. unfold it_ext_len in Hi. destruct (tx_ty X).
  - exfalso. exact (HNC eq_refl).
  - specialize (H29 eq_refl).
    rewrite <- (Z8_of_wz (arr_get lext_a i)). eapply u16_lo_read; [exact (rod_lext m MI)| apply av16_nth; lia| lia| reflexivity].
  - rewrite <- (Z8_of_wz (arr_get dext_a i)). eapply u16_lo_read; [exact (rod_dext m MI)| apply av16_nth; lia| lia| reflexivity].
Qed.
Lemma base_read : forall X m wk i, mem_inv usegs m -> u16arr usegs m (il_As (tx_L X) + 808) (av16 wk 288) ->
  0 <= i < it_ext_len (tx_ty X) 288 -> tx_ty X <> CODES ->
  ov_read_bytes usegs m (wa (tx_baseA X + 2 * i)) 2 = Some (le2 (wz (it_base (tx_ty X) wk i))).
Proof.
  intros X m wk i MI [Hb W] Hi HNC. unfold tx_baseA, it_base. unfold it_ext_len in Hi. destruct (tx_ty X).
  - exfalso. exact (HNC eq_refl).
  - eapply u16ro_read; [exact (rod_lbase m MI)| apply av16_nth; lia| lia| reflexivity].
  - eapply u16ro_read; [exact (rod_dbase m MI)| apply av16_nth; lia| lia| reflexivity].
Qed.
Lemma shiftr_le' : forall a k, 0 <= a -> 0 <= k -> 0 <= a ≫ k <= a.
Proof.
  intros a k Ha Hk. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; [lia| nia]].
Qed.
Lemma srlw_small' : forall x k, 0 <= x < 2147483648 -> 0 <= k <= 31 -> bv_swrap 32 (bv_wrap 32 x ≫ (k mod 32)) = x ≫ k.
Proof.
  intros x k Hx Hk. rewrite (bv_wrap_small 32 x) by (unfold bv_modulus; cbn; lia). rewrite (Z.mod_small k 32) by lia.
  pose proof (shiftr_le' x k ltac:(lia) ltac:(lia)). apply bv_swrap32_id. change (2^31) with 2147483648. lia.
Qed.
Lemma sllw_m1 : forall b, 0 <= b <= 31 -> bv_swrap 32 (18446744073709551615 ≪ (b mod 32)) = - 2 ^ b.
Proof.
  intros b Hb. rewrite (Z.mod_small b 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.div N.div Z.of_N].
  change (4294967296 / 2) with 2147483648.
  pose proof (Z.pow_pos_nonneg 2 b ltac:(lia) ltac:(lia)) as P0.
  assert (P1 : 2 ^ b <= 2147483648) by (change 2147483648 with (2 ^ 31); apply Z.pow_le_mono_r; lia).
  replace (18446744073709551615 * 2 ^ b + 2147483648) with ((2147483648 - 2 ^ b) + (4294967296 * 2 ^ b) * 4294967296) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma addw_small : forall a c, - 2147483648 <= a + c < 2147483648 -> bv_swrap 32 (a + c) = a + c.
Proof. intros. apply bv_swrap32_id. change (2^31) with 2147483648. lia. Qed.
Lemma addw_neg : forall a c, 0 < c <= 2 ^ 62 -> - 2 ^ 31 <= a - c < 2 ^ 31 ->
  bv_swrap 32 (a + Z.land (- c) 18446744073709551615) = a - c.
Proof.
  intros a c Hc Ha. rewrite land_ones64_neg by lia. apply (swrap32_sub a c); lia.
Qed.

Lemma add_neg_wz : forall a c, 0 < c <= 2 ^ 62 -> wz (a + Z.land (- c) 18446744073709551615) = wz (a - c).
Proof.
  intros a c Hc. rewrite land_ones64_neg by lia. apply Z_to_bv_eqm.
  replace (a + (- c + 2 ^ 64)) with ((a - c) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma u32arr_store_ok_part : forall m A ws (i k : Z) (j : nat) a,
  u32arr usegs m A ws -> 0 <= i < Z.of_nat (length ws) -> 0 <= k -> k + Z.of_nat j <= 4 -> a = wa (A + 4 * i + k) ->
  store_ok usegs m a j = true.
Proof.
  intros m A ws i k j a [_ Hw] Hi Hk Hj ->.
  replace (A + 4 * i + k) with (A + (4 * i + k)) by lia. eapply wr_at_store_ok; [exact Hw| lia| lia].
Qed.
Lemma ITL_intro' : forall X root max pc (q : lscr) cnt wk tb j2 ofs
    x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x1 = l27 q -> x2 = wz (bv_unsigned (tx_sp X) + -208) -> x3 = tx_gp X -> x4 = tx_tp X -> x5 = wz max -> x6 = l6 q -> x7 = wz (tx_match X) ->
  x8 = l31 q -> x9 = wz (bv_unsigned (tx_sp X) + -136) -> x10 = wz (ity_code (tx_ty X)) -> x11 = wz (tx_lensA X) -> x12 = l7 q ->
  x13 = wz (il_As (tx_L X) + 160) -> x14 = wz (tx_bitsA X) -> x15 = wz (il_As (tx_L X) + 808) -> x16 = l16 q -> x17 = wz root -> x18 = l9 q ->
  x19 = l19 q -> x20 = l20 q -> x21 = l28 q -> x22 = l21 q -> x23 = l23 q -> x24 = l1 q -> x25 = wz (notc X) -> x26 = l25 q -> x27 = l26 q ->
  x28 = l18 q -> x29 = l22 q -> x30 = l29 q -> x31 = l30 q -> F = tx_F X -> fc = tx_fc X ->
  ITM X (it_low X root j2) cnt ofs wk tb m ->
  ITL X root max pc q cnt wk tb
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (wz pc) fc None m (seg_rom usegs)).
Proof. intros. subst. unfold ITL. do 3 eexists. split; [reflexivity| eassumption]. Qed.
Ltac itm_close :=
  lazymatch goal with |- ITM _ _ _ _ _ _ ?m =>
    split;
    [ match goal with H : rw_cells _ m (bv_unsigned (tx_sp _) + -208) _ |- _ => exact H end
    | match goal with H : u8arr _ m _ (u16s (av16s _ 1 15)) |- _ => exact H end
    | match goal with H : u8arr _ m _ (u16s (av16 _ 16)) |- _ => exact H end
    | match goal with H : rw_cells _ m _ (it_saved _) |- _ => exact H end
    | match goal with H : stk _ m _ _ |- _ => exact H end
    | match goal with H : u8arr _ m _ (u16s (av16 _ 288)) |- _ => split; [exact (proj1 H)| exact (proj2 H)] | H : u16arr _ m _ _ |- _ => exact H end
    | match goal with H : u32arr _ m _ _ |- _ => exact H end
    | match goal with H : mem_inv _ m |- _ => exact H end
    | unfold tx_W1; match goal with H : munch _ _ m |- _ => exact H end
    | match goal with H : wmono _ _ m |- _ => exact H end ] end.
Ltac itl_close :=
  eapply ITL_intro'; [cbn [l1 l6 l7 l9 l16 l18 l19 l20 l21 l22 l23 l25 l26 l27 l28 l29 l30 l31]; treg ..| itm_close].

Lemma le2_sx16_add : forall v d, 0 <= v < 65536 -> le2 (wz (bv_unsigned (sx16 (wz v)) + d)) = le2 (wz (wrap16 (v + d))).
Proof.
  intros v d Hv. apply le2_wz_mod. unfold sx16. rewrite !Z_to_bv_unsigned. unfold wrap16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (65536 / 2) with 32768. change (2^16) with 65536. change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.
Lemma le2_swrap16_add : forall v d, 0 <= v < 65536 -> le2 (wz (bv_swrap 16 v + d)) = le2 (wz (wrap16 (v + d))).
Proof.
  intros v d Hv. apply le2_wz_mod. rewrite Z_to_bv_unsigned. unfold wrap16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (65536 / 2) with 32768. change (2^16) with 65536. change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.
Lemma dec48_mod : forall v, 0 <= v < 65536 ->
  (bv_unsigned (sx16 (wz v)) ≪ 48 + 18446462598732840960) mod 2 ^ 64 = wrap16 (v - 1) * 2 ^ 48.
Proof.
  intros v Hv. unfold sx16. rewrite !Z_to_bv_unsigned. unfold wrap16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (65536 / 2) with 32768. Z.div_mod_to_equations. nia.
Qed.
Lemma dec48_land : forall v, 0 <= v < 65536 ->
  Z.land (bv_unsigned (sx16 (wz v)) ≪ 48 + 18446462598732840960) 18446744073709551615 = wrap16 (v - 1) * 2 ^ 48.
Proof.
  intros v Hv. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply dec48_mod. exact Hv.
Qed.
Ltac st16 ARR a n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok usegs _ A (av16 a n) idx (wa (A + 2 * idx)) ARR ltac:(rewrite av16_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (av16_write m0 A a n idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      unfold u16arr in ARR';
      replace (A + 2 * idx) with E in ARR' by lia;
      let LN := fresh "L16" in pose proof (av16_zlength (arr_set a idx v) n ltac:(lia)) as LN;
      let LA := fresh "LNA" in pose proof (arr_len_set a idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.
Lemma sgtz_small : forall v, - 2 ^ 62 <= v < 2 ^ 62 -> negb (bv_lts (wz 0) (wz v)) = (v <=? 0).
Proof.
  intros v Hv. rewrite bv_lts_zero_l. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (2^62) with 4611686018427387904 in Hv. change (2^63) with 9223372036854775808. change (2^64) with 18446744073709551616.
  destruct (Z.leb_spec v 0); destruct (Z.ltb_spec 0 (v mod 18446744073709551616)); destruct (Z.ltb_spec (v mod 18446744073709551616) 9223372036854775808); cbn [andb negb]; try reflexivity; exfalso; Z.div_mod_to_equations; lia.
Qed.
Ltac br_sgtz K := if_cases K; rewrite sgtz_small in K by lia; [apply Z.leb_le in K| apply Z.leb_gt in K].
Lemma sllw_1 : forall r, 0 <= r <= 30 -> bv_swrap 32 (1 ≪ (r mod 32)) = 2 ^ r.
Proof.
  intros r Hr. rewrite (Z.mod_small r 32) by lia. rewrite Z.shiftl_1_l. apply bv_swrap32_id.
  split; [pose proof (Z.pow_nonneg 2 r); lia| apply Z.pow_lt_mono_r; lia].
Qed.
Lemma lowx_test : forall v low, 0 <= v < 65536 -> (low = 4294967295 \/ 0 <= low < 65536) ->
  (v = Z.land (lowx low) 18446744073709551615 <-> v = low).
Proof.
  intros v low Hv Hl. unfold lowx. destruct Hl as [-> | Hl].
  - rewrite Z.eqb_refl, Z.land_m1_l. lia.
  - replace (low =? 4294967295) with false by (symmetry; apply Z.eqb_neq; lia). rewrite land_ones64 by lia. tauto.
Qed.
