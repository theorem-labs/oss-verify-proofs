(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 262 of its 291 lines of code are new or changed and 232 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import CType Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import VerbsMem __intscan_c strtol_c number_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sp_eq : forall b, is_space b = c_space b.
Proof. intros b. unfold is_space, c_space. apply orb_comm. Qed.

Lemma dropw_skip : forall l, dropw is_space l = skip_space l.
Proof.
  induction l as [|b l IH]; cbn [dropw skip_space]; [reflexivity|].
  rewrite sp_eq. destruct (c_space b); [exact IH | reflexivity].
Qed.

Lemma ndig_le : forall l, (ndig l <= length l)%nat.
Proof. induction l as [|b l IH]; cbn [ndig length]; [lia|]. destruct (c_digit b); lia. Qed.

Lemma skip_le : forall l, (length (skip_space l) <= length l)%nat.
Proof. induction l as [|b l IH]; cbn [skip_space length]; [lia|]. destruct (c_space b); cbn [length]; lia. Qed.

Lemma rest_le : forall wd, (length (s10_rest wd) <= length wd)%nat.
Proof.
  intros wd. unfold s10_rest. pose proof (skip_le wd) as H.
  destruct (skip_space wd) as [|b r]; cbn [sign_split]; [cbn [snd length]; lia|].
  cbn [length] in H. destruct (bv_unsigned b =? 45); [cbn [snd]; lia|].
  destruct (bv_unsigned b =? 43); cbn [snd length]; lia.
Qed.

Lemma dv_eq : forall l acc, digits_val acc l = if Nat.eqb (ndig l) (length l) then Some (dval acc l) else None.
Proof.
  induction l as [|b l IH]; intros acc; [reflexivity|].
  cbn [digits_val ndig dval length]. change (is_digit b) with (c_digit b).
  destruct (c_digit b); [rewrite IH; reflexivity | reflexivity].
Qed.

Lemma dm_some : forall l x, digits_m l = Some x <-> (l <> [] /\ ndig l = length l /\ x = dval 0 l).
Proof.
  intros [|b l] x; cbn [digits_m].
  - split; [discriminate | intros (C & _); congruence].
  - rewrite dv_eq. destruct (Nat.eqb_spec (ndig (b :: l)) (length (b :: l))) as [E|N].
    + split; [intros H; injection H as <-; split; [discriminate | split; [exact E | reflexivity]]
             | intros (_ & _ & ->); reflexivity].
    + split; [discriminate | intros (_ & C & _); contradiction].
Qed.

Lemma sd_eq : forall wd, signed_digits (dropw is_space wd) =
  option_map (fun x => if s10_neg wd then - x else x) (digits_m (s10_rest wd)).
Proof.
  intros wd. rewrite dropw_skip. unfold s10_neg, s10_rest.
  destruct (skip_space wd) as [|b r]; [reflexivity|].
  cbn [signed_digits sign_split].
  destruct (Z.eqb_spec (bv_unsigned b) 45) as [E45|N45]; destruct (Z.eqb_spec (bv_unsigned b) 43) as [E43|N43];
    try lia; cbn [fst snd]; first [destruct (digits_m r); reflexivity | destruct (digits_m (b :: r)); reflexivity].
Qed.

Lemma end_le : forall wd, 0 <= s10_end wd <= Z.of_nat (length wd).
Proof.
  intros wd. pose proof (rest_le wd) as R. pose proof (ndig_le (s10_rest wd)) as N.
  unfold s10_end, s10_nd. destruct (Nat.eqb (ndig (s10_rest wd)) 0); lia.
Qed.

Lemma end_full : forall wd, (wd <> [] /\ s10_end wd = Z.of_nat (length wd)) <->
  (s10_rest wd <> [] /\ ndig (s10_rest wd) = length (s10_rest wd)).
Proof.
  intros wd. pose proof (rest_le wd) as R. pose proof (ndig_le (s10_rest wd)) as N.
  unfold s10_end, s10_nd.
  destruct (Nat.eqb_spec (ndig (s10_rest wd)) 0) as [Z0|Z0].
  - split.
    + intros (NE & E). destruct wd as [|b w]; [congruence|]. cbn [length] in E. lia.
    + intros (NE & E). destruct (s10_rest wd) as [|b r]; [congruence|]. cbn [length] in E. lia.
  - split.
    + intros (_ & E). split; [intros C; rewrite C in Z0; cbn in Z0; lia | lia].
    + intros (NE & E). split; [intros ->; apply NE; reflexivity | lia].
Qed.

Lemma number_bridge : forall wd v, number_m wd = Some v <->
  (wd <> [] /\ s10_end wd = Z.of_nat (length wd) /\ -1000000 <= s10_val wd <= 1000000 /\ v = s10_val wd).
Proof.
  intros wd v. unfold number_m. rewrite sd_eq.
  destruct (digits_m (s10_rest wd)) as [x|] eqn:DM; cbn [option_map].
  - apply dm_some in DM. destruct DM as (NE & ND & ->).
    change (if s10_neg wd then - dval 0 (s10_rest wd) else dval 0 (s10_rest wd)) with (s10_signed wd).
    assert (VS : -1000000 <= s10_val wd <= 1000000 -> -1000000 <= s10_signed wd <= 1000000)
      by (unfold s10_val, LMIN; lia).
    assert (VE : -1000000 <= s10_signed wd <= 1000000 -> s10_val wd = s10_signed wd)
      by (unfold s10_val, LMIN; lia).
    destruct (proj2 (end_full wd) (conj NE ND)) as [EF1 EF2].
    destruct ((-1000000 <=? s10_signed wd) && (s10_signed wd <=? 1000000)) eqn:R.
    + apply andb_true_iff in R. destruct R as [R1 R2]. apply Z.leb_le in R1. apply Z.leb_le in R2.
      rewrite VE by lia. split.
      * intros H. injection H as <-. split; [exact EF1|]. split; [exact EF2|]. split; [lia | reflexivity].
      * intros (_ & _ & _ & ->). reflexivity.
    + split; [discriminate|]. intros (_ & _ & IR & _). apply VS in IR.
      apply andb_false_iff in R. destruct R as [R|R]; apply Z.leb_gt in R; lia.
  - split; [discriminate|]. intros (NE & E & _).
    destruct (proj1 (end_full wd) (conj NE E)) as [RN RD].
    assert (S : digits_m (s10_rest wd) = Some (dval 0 (s10_rest wd))) by (apply dm_some; split; [exact RN | split; [exact RD | reflexivity]]).
    congruence.
Qed.

Lemma nm_none : forall wd, ~ (wd <> [] /\ s10_end wd = Z.of_nat (length wd) /\ -1000000 <= s10_val wd <= 1000000) ->
  number_m wd = None.
Proof.
  intros wd H. destruct (number_m wd) as [v|] eqn:E; [|reflexivity].
  exfalso. apply H. apply number_bridge in E. destruct E as (E1 & E2 & E3 & _). split; [exact E1 | split; [exact E2 | exact E3]].
Qed.

Lemma nm_some : forall wd, wd <> [] -> s10_end wd = Z.of_nat (length wd) -> -1000000 <= s10_val wd <= 1000000 ->
  number_m wd = Some (s10_val wd).
Proof. intros wd H1 H2 H3. apply number_bridge. split; [exact H1 | split; [exact H2 | split; [exact H3 | reflexivity]]]. Qed.

Lemma first1 : forall (l : list byte) k b, nth_error l k = Some b -> firstn 1 (skipn k l) = [b].
Proof.
  induction l as [|x l IH]; intros [|k] b H; cbn in H |- *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

Lemma read1 : forall m A bs k b, bytes_at rsegs m A bs -> 0 <= k -> nth_error bs (Z.to_nat k) = Some b ->
  ov_read_bytes rsegs m (wa (A + k)) 1 = Some [b].
Proof.
  intros m A bs k b H Hk Hn.
  assert (L : (Z.to_nat k < length bs)%nat) by (apply nth_error_Some; congruence).
  rewrite (bytes_at_read rsegs m A bs k 1 H Hk) by lia.
  rewrite (first1 _ _ _ Hn). reflexivity.
Qed.

Lemma byte_end : forall wd, Forall (fun b : byte => bv_unsigned b <> 0) wd ->
  exists b, nth_error (wd ++ [Z_to_bv 8 0]) (Z.to_nat (s10_end wd)) = Some b /\
            (bv_unsigned b = 0 <-> s10_end wd = Z.of_nat (length wd)).
Proof.
  intros wd HZ. pose proof (end_le wd) as EL.
  destruct (Z.eq_dec (s10_end wd) (Z.of_nat (length wd))) as [E|N].
  - exists (Z_to_bv 8 0). rewrite E, Nat2Z.id, nth_error_app2, Nat.sub_diag by lia.
    split; [reflexivity|]. split; intros _; reflexivity.
  - destruct (nth_error wd (Z.to_nat (s10_end wd))) as [b|] eqn:B.
    + exists b. rewrite nth_error_app1 by (apply nth_error_Some; congruence). split; [exact B|].
      rewrite Forall_forall in HZ. pose proof (HZ b (nth_error_In _ _ B)) as NZ.
      split; intros C; contradiction.
    + apply nth_error_None in B. lia.
Qed.

Lemma byte_first : forall wd, Forall (fun b : byte => bv_unsigned b <> 0) wd ->
  exists b, nth_error (wd ++ [Z_to_bv 8 0]) (Z.to_nat 0) = Some b /\ (bv_unsigned b = 0 <-> wd = []).
Proof.
  intros [|b w] HZ.
  - exists (Z_to_bv 8 0). split; [reflexivity|]. split; intros _; reflexivity.
  - exists b. split; [reflexivity|]. apply Forall_inv in HZ. split; [intros C; contradiction | discriminate].
Qed.

Lemma eqb_byte : forall b : byte, bv_eqb (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0) = (bv_unsigned b =? 0).
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma tle : forall bs : list byte, Z_to_le_bytes (length bs) (le_val (map bv_unsigned bs)) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length map le_val Z_to_le_bytes].
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Rv.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8). change (2^8) with 256.
    rewrite (Z.mul_comm 256), Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    rewrite (Z.mul_comm 256), Z.div_add, Z.div_small, Z.add_0_l by lia. exact IH.
Qed.

Lemma le8_lebw : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned, bytes_le_to_Z_le_val.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as R. rewrite length_map, L in R.
  change (256 ^ Z.of_nat 8) with (2^64) in R.
  rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia).
  rewrite <- L. apply tle.
Qed.

Lemma cb8_c8 : forall m A bs, rw_cells rsegs m A [CB 8 bs] -> rw_cells rsegs m A [C8 (le_bytes_to_word bs)].
Proof.
  intros m A bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes] in Hb |- *. rewrite le8_lebw by exact L. exact Hb.
  - exact Hw.
Qed.

Lemma rw1_bytes : forall m A c, rw_cells rsegs m A [c] -> bytes_at rsegs m A (cbytes c).
Proof. intros m A c [[_ Hb] _]. cbn [cells_bytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma rwc_split : forall m A B cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 [[Hwf Hb] (H0 & H1 & H2)] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app in H1, H2.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply H2. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H2. lia.
Qed.

Lemma rwc_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (H0 & H1 & H2)] [[W2 B2] (G0 & G1 & G2)] ->.
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact W1. exact B2.
  - unfold wr_at. rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
    + apply H2. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G2. lia.
Qed.

Lemma range_ltu : forall r, -9223372036854775808 <= r <= 9223372036854775807 ->
  bv_ltu (Z_to_bv 64 (r + -1000001)) (Z_to_bv 64 (-2000001)) = negb ((-1000000 <=? r) && (r <=? 1000000)).
Proof.
  intros r Hr. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  destruct ((-1000000 <=? r) && (r <=? 1000000)) eqn:E; cbn [negb].
  - apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    apply Z.ltb_ge. Z.div_mod_to_equations. lia.
  - apply Z.ltb_lt. apply andb_false_iff in E. destruct E as [E|E]; apply Z.leb_gt in E; Z.div_mod_to_equations; lia.
Qed.

Theorem number_holds : strtol_contract -> number_contract.
Proof.
  intros STL. unfold number_contract, NUMBER, NUMBER_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    can ev wd ob HW W4 WL WB OM OB OL OW ER HSSP MI ST LO OV OO OE OG OGd D1 D2 D3 D4.
  destruct HW as [HWb HWz]. destruct HSSP as [HG HGd].
  unfold off_lo, SSP_GOT, SSP_GUARD in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 tp) as Rtp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  change (bv_modulus 64) with (2^64) in Rsp, Rtp, Ra0, Ra1.
  assert (EA : a0 = Z_to_bv 64 (bv_unsigned a0)) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (EO : a1 = Z_to_bv 64 (bv_unsigned a1)) by (symmetry; apply Z_to_bv_bv_unsigned).
  set (A := bv_unsigned a0) in *. set (O := bv_unsigned a1) in *. clearbody A O. subst a0 a1.
  assert (OC : rw_cells rsegs m O [CB 4 ob]).
  { split; [split|]; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact OB | exact OW]. }
  clear OB OW.
  pose proof (bytes_at_bound _ _ _ _ HWb) as BW. rewrite length_app in BW. cbn [length] in BW.
  pose proof (end_le wd) as EL.
  assert (VR : -9223372036854775808 <= s10_val wd <= 9223372036854775807) by (unfold s10_val, LMIN; lia).
  pose proof (munch_refl [(bv_unsigned sp - 400, bv_unsigned sp); (O, O + 4);
              (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (proj1 ST) as LO0.
  carve_frame 32%nat ST.
  do 9 zstep.
  pose proof (rwc_split _ _ (bv_unsigned sp + -32 + 8) [_] _ FR) as X.
  specialize (X ltac:(cbn [cells_size csize Nat.add]; lia)). destruct X as [F0 F1]. clear FR.
  apply cb8_c8 in F0.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply STL | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold strtol_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call segs mm ]
  end;
  [ exact HWb | lia | lia | exact F0 | exact ER | exact HG | exact HGd
  | rewrite unsigned_lit by lia; exact ST
  | rewrite unsigned_lit by lia; lia
  | rewrite unsigned_lit by lia; lia
  | rewrite unsigned_lit by lia; lia
  | rewrite unsigned_lit by lia; lia
  | lia
  | unfold STRTOL_SSP_GOT; rewrite unsigned_lit by lia; lia
  | unfold STRTOL_SSP_GUARD; rewrite unsigned_lit by lia; lia
  | unfold STRTOL_SSP_GUARD; lia
  | unfold STRTOL_SSP_GUARD; lia
  | exact MI | ].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => rename H into G0 end.
  pose proof (rwc_join _ _ _ _ _ G0 F1 ltac:(cbn [cells_size csize Nat.add]; lia)) as FR.
  clear G0 F1. cbn [app] in FR.
  destruct (byte_first wd HWz) as (b0 & B0 & B0z).
  pose proof (read1 _ _ _ 0 _ HWb ltac:(lia) B0) as R0.
  zstep. zstep.
  rewrite eqb_byte.
  destruct (Z.eqb_spec (bv_unsigned b0) 0) as [Z0|Z0]; cbv iota.
  - apply B0z in Z0. subst wd.
    pose proof (rw1_bytes _ _ _ OC) as OBf. cbn [cbytes] in OBf.
    do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    unfold number_post. rewrite number_m_nil. finish.
  - assert (NE : wd <> []) by (intros C; apply Z0; apply B0z; exact C).
    destruct (byte_end wd HWz) as (be & BE & BEz).
    pose proof (read1 _ _ _ (s10_end wd) _ HWb ltac:(lia) BE) as RE.
    do 5 zstep.
    rewrite eqb_byte.
    destruct (Z.eqb_spec (bv_unsigned be) 0) as [Z1|Z1]; cbn [negb].
    + apply BEz in Z1.
      do 6 zstep.
      rewrite (range_ltu (s10_val wd) VR).
      destruct ((-1000000 <=? s10_val wd) && (s10_val wd <=? 1000000)) eqn:IR; cbn [negb].
      * apply andb_true_iff in IR. destruct IR as [IR1 IR2]. apply Z.leb_le in IR1. apply Z.leb_le in IR2.
        assert (NM : number_m wd = Some (s10_val wd)) by (apply nm_some; [exact NE | exact Z1 | lia]).
        do 7 zstep. release_frame FR ST (bv_unsigned sp). zstep.
        pose proof (rw1_bytes _ _ _ OC) as OBf. cbn [cbytes] in OBf.
        unfold number_post. rewrite NM. finish.
      * assert (NM : number_m wd = None).
        { apply nm_none. intros (_ & _ & R1 & R2). apply andb_false_iff in IR.
          destruct IR as [IR|IR]; apply Z.leb_gt in IR; lia. }
        pose proof (rw1_bytes _ _ _ OC) as OBf. cbn [cbytes] in OBf.
        do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep.
        unfold number_post. rewrite NM. finish.
    + assert (NM : number_m wd = None) by (apply nm_none; intros (_ & E & _); apply Z1, BEz, E).
      pose proof (rw1_bytes _ _ _ OC) as OBf. cbn [cbytes] in OBf.
      do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep.
      unfold number_post. rewrite NM. finish.
Qed.
