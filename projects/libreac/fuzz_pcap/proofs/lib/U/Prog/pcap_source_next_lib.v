(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 532 of its 545 lines of code are new or changed and 47 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Lia Bool Btauto.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel pcap_source_struct_next.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_app_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hl & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hl, Hw.
  rewrite cells_bytes_length in B2 by exact W1.
  split.
  - split; [split; [exact W1 | exact B1] |]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [exact W2 | exact B2] |]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

Lemma rw_cells_app_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (Ha1 & Hl1 & Hw1)] [[W2 B2] (Ha2 & Hl2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

Lemma bytes_at_byte : forall m a bs (k : Z),
  bytes_at rsegs m a bs -> 0 <= k < Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (a + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k H Hk.
  rewrite (bytes_at_read rsegs m a bs k 1 H) by lia.
  f_equal. remember (Z.to_nat k) as j. assert (j < length bs)%nat by lia. clear Heqj Hk H.
  revert j H0. induction bs as [|x bs IH]; intros j Hj; cbn in *; [lia|].
  destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.

Lemma rw_cells_of_bytes : forall m A bs,
  bytes_at rsegs m A bs -> wr_at rsegs m A (Z.of_nat (length bs)) -> rw_cells rsegs m A [CB (length bs) bs].
Proof.
  intros m A bs HB HW. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma rw_cells_wr_at : forall m A cs, rw_cells rsegs m A cs -> wr_at rsegs m A (Z.of_nat (cells_size cs)).
Proof. intros m A cs [_ H]. exact H. Qed.

Lemma rw_cells_bytes : forall m A cs, rw_cells rsegs m A cs -> bytes_at rsegs m A (cells_bytes cs).
Proof. intros m A cs [[_ H] _]. exact H. Qed.

Lemma mfile_cells_size1304 : forall h b n fl pad0 rpos rend prev next md pad1 pos pad2 ung buf,
  length ung = 8%nat -> length buf = 1024%nat ->
  cells_size (mfile_cells h b n fl pad0 rpos rend prev next md pad1 pos pad2 ung buf) = 1304%nat.
Proof. intros. reflexivity. Qed.

Lemma mstl_frame : forall m h b Fc p pv nx, mstl m h b Fc p pv nx ->
  exists cs, cells_size cs = 1304%nat /\ rw_cells rsegs m h cs /\ bytes_at rsegs m b Fc /\
    (h + 1304 <= b \/ b + Z.of_nat (length Fc) <= h) /\ 0 < h /\
    forall m', rw_cells rsegs m' h cs -> bytes_at rsegs m' b Fc -> mstl m' h b Fc p pv nx.
Proof.
  intros m h b Fc p pv nx (fl & md & q & rb & MF & R1 & R2 & R3 & R4).
  destruct MF as (buf & (pad0 & pad1 & pad2 & ung & HC & L1 & L2 & H0 & H16) & Hq & Hrb & HFc & Hb0 & Hd).
  exists (mfile_cells h b (Z.of_nat (length Fc)) fl pad0 (rpos_of h rb) (rend_of h rb) pv nx md pad1 (wz q) pad2 ung buf).
  split; [reflexivity|]. split; [exact HC|]. split; [exact HFc|]. split; [exact Hd|]. split; [exact H0|].
  intros m' HC' HB'. exists fl, md, q, rb. split; [|tauto].
  unfold mfile. cbv zeta. exists buf. split.
  - exists pad0, pad1, pad2, ung. tauto.
  - tauto.
Qed.

Lemma find_segment_range : forall (segs : list Segment) a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  destruct ((Z.of_N (seg_base s) <=? a) && (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:E.
  - injection H as <-. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity|]. lia.
  - destruct (IH a n seg H) as (Hin & H1 & H2). split; [right; exact Hin|]. lia.
Qed.

Lemma rsegs_span : forallb (fun s => (0x10000 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? (symaddr ImgPages.Ubsan.top))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_apart : forall a, (a < 0x10000 \/ (symaddr ImgPages.Ubsan.top) <= a) -> find_segment rsegs a 1 = None.
Proof.
  intros a Ha. destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity]. exfalso.
  destruct (find_segment_range rsegs a 1 seg E) as (Hin & H1 & H2).
  pose proof rsegs_span as S. rewrite forallb_forall in S. specialize (S seg Hin).
  apply andb_true_iff in S as [S1 S2]. apply Z.leb_le in S1. apply Z.leb_le in S2. lia.
Qed.

Lemma ro_addr_apart : forall a, 0 <= a < 2 ^ 64 -> (a < 0x10000 \/ (symaddr ImgPages.Ubsan.top) <= a) -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Hr Ha. unfold ro_addr. rewrite unsigned_lit by lia. rewrite find_segment_apart by exact Ha. reflexivity.
Qed.

Lemma not_ro_apart : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> img_apart a n -> RoAdapt.not_ro rsegs a n.
Proof.
  intros a n H0 H1 H2 i Hi. unfold wa. apply ro_addr_apart; [lia|]. unfold img_apart in H2. lia.
Qed.

Lemma not_ro_hi : forall a n, (symaddr ImgPages.Ubsan.top) <= a -> a + n <= 2 ^ 64 -> RoAdapt.not_ro rsegs a n.
Proof. intros a n H0 H1. apply not_ro_apart; [lia | lia | right; lia]. Qed.

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_ge_dec x lo) as [H1|H1]; [left; split; [lia|exact H]|].
  destruct (Z_le_gt_dec hi x) as [H2|H2]; [left; split; [lia|exact H]|].
  right. intros [H3 _]. lia.
Qed.

Lemma ro_agree_munch : forall W m m', MemNorm.ro_agree rsegs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> ro_addr rsegs x = false) -> MemNorm.ro_agree rsegs m'.
Proof.
  intros W m m' HR HM HW a E. destruct (outside_dec W (bv_unsigned a)) as [Ho|Hn].
  - unfold mrd. rewrite (HM a Ho). exact (HR a E).
  - rewrite (HW a Hn) in E. discriminate.
Qed.

Lemma nth_firstn_lt : forall (A : Type) (l : list A) n m d, (n < m)%nat -> nth n (firstn m l) d = nth n l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n m d H; destruct m as [|m]; cbn; try lia; [destruct n; reflexivity|].
  destruct n as [|n]; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_skipn_add : forall (A : Type) (l : list A) n m d, nth n (skipn m l) d = nth (m + n) l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n m d; destruct m as [|m]; cbn; try reflexivity; [destruct n; reflexivity|].
  apply IH.
Qed.

Lemma nth_hdr : forall (l : list byte) q k d, 0 <= q -> 0 <= k -> (Z.to_nat k < 16)%nat ->
  nth (Z.to_nat k) (firstn 16 (skipn (Z.to_nat q) l)) d = nth (Z.to_nat (q + k)) l d.
Proof.
  intros l q k d Hq Hk H. rewrite nth_firstn_lt by exact H. rewrite nth_skipn_add. f_equal. lia.
Qed.

Lemma tb_wrap : forall n x i, Z.testbit (bv_wrap n x) i = (i <? Z.of_N n) && Z.testbit x i.
Proof.
  intros n x i. unfold bv_wrap, bv_modulus.
  destruct (Z.ltb_spec i 0) as [Hn|Hn].
  - rewrite !Z.testbit_neg_r by lia. symmetry. apply andb_false_r.
  - destruct (Z.ltb_spec i (Z.of_N n)) as [H|H]; cbn [andb].
    + apply Z.mod_pow2_bits_low. exact H.
    + apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma swrap32_eq : forall x, bv_swrap 32 x = (x + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31.
Proof.
  intros x. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity. reflexivity.
Qed.

Lemma swrap32_range : forall x, - 2 ^ 31 <= bv_swrap 32 x < 2 ^ 31.
Proof.
  intros x. rewrite swrap32_eq. pose proof (Z.mod_pos_bound (x + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia.
Qed.

Lemma swrap32_mod : forall x, bv_swrap 32 x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  intros x. rewrite swrap32_eq. rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma tb_small_hi : forall z i, - 2 ^ 31 <= z < 2 ^ 31 -> 31 <= i -> Z.testbit z i = (z <? 0).
Proof.
  intros z i Hz Hi. destruct (Z.ltb_spec z 0) as [Hn|Hn].
  - apply Z.bits_above_log2_neg; [lia|]. try unfold Z.lnot.
    match goal with |- Z.log2 ?t < _ =>
      destruct (Z.eq_dec t 0) as [E0|E0]; [rewrite E0; cbn; lia|];
      assert (Z.log2 t < 31) by (apply Z.log2_lt_pow2; lia); lia end.
  - destruct (Z.eq_dec z 0) as [->|E]; [apply Z.testbit_0_l|].
    apply Z.bits_above_log2; [lia|].
    assert (Z.log2 z < 31) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma tb_swrap32 : forall x i,
  Z.testbit (bv_swrap 32 x) i = if i <? 32 then Z.testbit x i else (0 <=? i) && Z.testbit x 31.
Proof.
  intros x i. destruct (Z.ltb_spec i 0) as [Hn|Hn].
  - rewrite !Z.testbit_neg_r by lia. destruct (Z.ltb_spec i 32); [reflexivity | lia].
  - pose proof (swrap32_range x) as R. destruct (Z.ltb_spec i 32) as [Hl|Hl].
    + rewrite <- (Z.mod_pow2_bits_low (bv_swrap 32 x) 32 i Hl), swrap32_mod.
      apply Z.mod_pow2_bits_low. exact Hl.
    + replace (0 <=? i) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
      rewrite (tb_small_hi _ i R) by lia.
      rewrite <- (Z.mod_pow2_bits_low x 32 31) by lia. rewrite <- swrap32_mod.
      rewrite Z.mod_pow2_bits_low by lia. symmetry. apply tb_small_hi; [exact R | lia].
Qed.

Lemma tb_shiftl : forall a n i, 0 <= n -> Z.testbit (Z.shiftl a n) i = Z.testbit a (i - n).
Proof.
  intros a n i Hn. destruct (Z.ltb_spec i 0).
  - rewrite !Z.testbit_neg_r by lia. reflexivity.
  - apply Z.shiftl_spec. lia.
Qed.

Lemma tb_shiftr : forall a n i, 0 <= n -> Z.testbit (Z.shiftr a n) i = (0 <=? i) && Z.testbit a (i + n).
Proof.
  intros a n i Hn. destruct (Z.leb_spec 0 i); cbn [andb].
  - apply Z.shiftr_spec. lia.
  - apply Z.testbit_neg_r. lia.
Qed.

Lemma tb_byte_hi : forall (c : byte) i, 8 <= i -> Z.testbit (bv_unsigned c) i = false.
Proof.
  intros c i Hi. pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with (2 ^ 8) in R.
  rewrite <- (Z.mod_small (bv_unsigned c) (2 ^ 8)) by lia. apply Z.mod_pow2_bits_high. lia.
Qed.

Ltac gen_bytes :=
  repeat match goal with
  | |- context [@bv_unsigned 8%N ?c] =>
      tryif is_var c then fail else (let x := fresh "c" in generalize c as x; intros x)
  end.

Ltac bits_rw :=
  repeat first [ rewrite Z.lor_spec | rewrite Z.land_spec | rewrite tb_wrap | rewrite tb_swrap32
               | rewrite tb_shiftl by lia | rewrite tb_shiftr by lia ].

Ltac bits_hi :=
  repeat match goal with
  | |- context [Z.testbit (@bv_unsigned 8%N ?c) ?k] =>
      let b := eval compute in (8 <=? k) in
      lazymatch b with true => rewrite (tb_byte_hi c k) by lia end
  end.

Ltac split_range i H k n :=
  lazymatch eval compute in (k =? n) with
  | true => exfalso; lia
  | false =>
      let Hne := fresh "Hne" in
      destruct (Z.eq_dec i k) as [->|Hne];
      [ clear H
      | let k' := eval compute in (k + 1) in
        let H' := fresh "Hr" in
        assert (H' : k' <= i < n) by lia; clear H Hne; split_range i H' k' n ]
  end.

Ltac bits_lit :=
  repeat match goal with
  | |- context [Z.testbit ?a ?k] =>
      lazymatch a with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end;
      lazymatch k with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end;
      let v := eval vm_compute in (Z.testbit a k) in change (Z.testbit a k) with v
  end.

Ltac bits_neg :=
  repeat match goal with
  | |- context [Z.testbit (@bv_unsigned 8%N ?c) (Zneg ?p)] =>
      rewrite (Z.testbit_neg_r (bv_unsigned c) (Zneg p)) by lia
  end.

Ltac zclosed e :=
  lazymatch e with
  | Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac
  | Z.add ?a ?b => zclosed a; zclosed b
  | Z.sub ?a ?b => zclosed a; zclosed b
  | Z.opp ?a => zclosed a
  | Z.of_N ?n => lazymatch n with N0 => idtac | Npos _ => idtac end
  end.

Ltac bits_arith :=
  repeat match goal with
  | |- context [Z.of_N ?n] => zclosed (Z.of_N n);
      let v := eval vm_compute in (Z.of_N n) in change (Z.of_N n) with v
  | |- context [Z.sub ?a ?b] => zclosed a; zclosed b;
      let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
  | |- context [Z.add ?a ?b] => zclosed a; zclosed b;
      let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.ltb ?a ?b] => zclosed a; zclosed b;
      let v := eval vm_compute in (Z.ltb a b) in change (Z.ltb a b) with v
  | |- context [Z.leb ?a ?b] => zclosed a; zclosed b;
      let v := eval vm_compute in (Z.leb a b) in change (Z.leb a b) with v
  end.

Ltac bits_case :=
  bits_arith; cbn [andb orb negb]; bits_lit; bits_hi; bits_neg; cbn [andb orb negb]; first [reflexivity | btauto].

Ltac bits_eq :=
  unfold zxb; apply bv_eq; rewrite !Z_to_bv_unsigned; gen_bytes;
  apply Z.bits_inj'; let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  rewrite !tb_wrap;
  let Hl := fresh "Hl" in
  destruct (Z.ltb_spec i (Z.of_N 64)) as [Hl|Hl];
  [ cbn [andb]; bits_rw;
    let H := fresh "Hr" in assert (H : 0 <= i < 64) by (change (Z.of_N 64) with 64 in Hl; lia); clear Hi Hl;
    split_range i H 0 64; bits_case
  | reflexivity ].

Lemma lor_add_lo : forall a b n, 0 <= n -> 0 <= a < 2 ^ n -> 0 <= b -> b mod 2 ^ n = 0 -> Z.lor a b = a + b.
Proof.
  intros a b n Hn Ha Hb Hm.
  assert (HL : Z.land a b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n) as [Hlt|Hge].
    - rewrite <- (Z.mod_pow2_bits_low b n i Hlt), Hm, Z.bits_0. apply andb_false_r.
    - rewrite <- (Z.mod_small a (2 ^ n)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact HL. symmetry. apply Z.add_nocarry_lxor. exact HL.
Qed.

Lemma w32le_lor : forall x0 x1 x2 x3, 0 <= x0 < 256 -> 0 <= x1 < 256 -> 0 <= x2 < 256 -> 0 <= x3 < 256 ->
  w32le x0 x1 x2 x3 = Z.lor x0 (Z.lor (Z.shiftl x1 8) (Z.lor (Z.shiftl x2 16) (Z.shiftl x3 24))).
Proof.
  intros x0 x1 x2 x3 H0 H1 H2 H3. unfold w32le. rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite (lor_add_lo (x2 * 2 ^ 16) (x3 * 2 ^ 24) 24) by (first [apply Z.mod_mul | idtac]; lia).
  rewrite (lor_add_lo (x1 * 2 ^ 8) (x2 * 2 ^ 16 + x3 * 2 ^ 24) 16).
  2-4: lia.
  2: { replace (x2 * 2 ^ 16 + x3 * 2 ^ 24) with ((x2 + x3 * 2 ^ 8) * 2 ^ 16) by ring. apply Z.mod_mul. lia. }
  rewrite (lor_add_lo x0 (x1 * 2 ^ 8 + (x2 * 2 ^ 16 + x3 * 2 ^ 24)) 8).
  2-4: lia.
  2: { replace (x1 * 2 ^ 8 + (x2 * 2 ^ 16 + x3 * 2 ^ 24)) with ((x1 + x2 * 2 ^ 8 + x3 * 2 ^ 16) * 2 ^ 8) by ring.
       apply Z.mod_mul. lia. }
  lia.
Qed.

Lemma vid_lor : forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
  (256 * x + y) mod 4096 = Z.lor (Z.shiftl (Z.land x 15) 8) y.
Proof.
  intros x y Hx Hy. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.lor_comm. rewrite (lor_add_lo y ((x mod 2 ^ 4) * 2 ^ 8) 8).
  - change (2 ^ 4) with 16. change (2 ^ 8) with 256. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - pose proof (Z.mod_pos_bound x (2 ^ 4)). lia.
  - apply Z.mod_mul. lia.
Qed.

Lemma byte_range : forall c : byte, 0 <= bv_unsigned c < 256.
Proof. intros c. pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R. exact R. Qed.

Definition hdr_kind (k : pkind) : bool := match k with KEnd | KCutH | KEmpty => false | _ => true end.
Definition exit_kind (k : pkind) : bool := match k with KEnd | KCutH | KFit | KCutFit => true | _ => false end.
Definition big_kind (k : pkind) : bool := match k with KBig0 | KBig | KCutBig => true | _ => false end.

Lemma hdr_ov : forall m A (F : list byte) q k r, bytes_at rsegs m A (firstn 16 (skipn (Z.to_nat q) F)) ->
  0 <= q -> q + 16 <= Z.of_nat (length F) -> 0 <= k < 16 -> r = q + k ->
  ov_read_bytes rsegs m (wa (A + k)) 1 = Some [nth (Z.to_nat r) F (Z_to_bv 8 0)].
Proof.
  intros m A F q k r H Hq Hn Hk ->.
  rewrite (bytes_at_byte m A _ k H) by (rewrite firstn_length, skipn_length; lia).
  rewrite nth_hdr by lia. reflexivity.
Qed.

Lemma rec_ov : forall m A (F : list byte) q I k r, bytes_at rsegs m A (firstn (Z.to_nat I) (skipn (Z.to_nat (q + 16)) F)) ->
  0 <= q -> q + 16 + I <= Z.of_nat (length F) -> 0 <= k < I -> r = q + 16 + k ->
  ov_read_bytes rsegs m (wa (A + k)) 1 = Some [nth (Z.to_nat r) F (Z_to_bv 8 0)].
Proof.
  intros m A F q I k r H Hq Hn Hk ->.
  rewrite (bytes_at_byte m A _ k H) by (rewrite firstn_length, skipn_length; lia).
  rewrite nth_firstn_lt by lia. rewrite nth_skipn_add. repeat f_equal. lia.
Qed.

Lemma u8arr_take : forall m A bs k, u8arr rsegs m A bs -> (k <= length bs)%nat ->
  rw_cells rsegs m A [CB k (firstn k bs)].
Proof.
  intros m A bs k [HB HW] Hk.
  rewrite <- (firstn_skipn k bs) in HB. apply bytes_at_app in HB. destruct HB as [HB _].
  split; [split|].
  - cbn. split; [rewrite firstn_length; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - destruct HW as (H1 & H2 & H3). cbn [cells_size csize]. split; [lia|]. split; [lia|].
    intros i Hi. apply H3. lia.
Qed.

Lemma u8arr_after : forall W m m' A bs xs, u8arr rsegs m A bs -> munch W m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' A xs -> (length xs <= length bs)%nat ->
  (forall x, A + Z.of_nat (length xs) <= x < A + Z.of_nat (length bs) -> outside W x) ->
  u8arr rsegs m' A (xs ++ skipn (length xs) bs).
Proof.
  intros W m m' A bs xs [HB HW] MU WM HX Hl HO.
  assert (HB2 : bytes_at rsegs m (A + Z.of_nat (length xs)) (skipn (length xs) bs)).
  { rewrite <- (firstn_skipn (length xs) bs) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
    rewrite firstn_length, Nat.min_l in HB by exact Hl. exact HB. }
  split.
  - apply bytes_at_app. split; [exact HX|].
    destruct HB2 as (B1 & B2 & B3). split; [lia|]. split; [lia|]. intros i Hi.
    rewrite <- (B3 i Hi). unfold mrd. rewrite (MU (wa (A + Z.of_nat (length xs) + Z.of_nat i))); [reflexivity|].
    rewrite skipn_length in Hi, B2. rewrite wa_unsigned by lia. apply HO. lia.
  - rewrite app_length, skipn_length. replace (length xs + (length bs - length xs))%nat with (length bs) by lia.
    exact (wr_at_transport rsegs m m' A _ HW WM).
Qed.

Lemma u8arr_len : forall m A bs, u8arr rsegs m A bs -> 0 <= A /\ A + Z.of_nat (length bs) <= 2 ^ 64.
Proof. intros m A bs [HB _]. exact (bytes_at_bound rsegs m A bs HB). Qed.

Lemma rw_of_u8arr : forall m A bs, u8arr rsegs m A bs -> rw_cells rsegs m A [CB (length bs) bs].
Proof.
  intros m A bs [HB HW]. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma ph_after : forall W m m' A ph xs, rw_cells rsegs m A [CB 16 ph] -> munch W m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' A xs -> (length xs <= 16)%nat ->
  (forall x, A + Z.of_nat (length xs) <= x < A + 16 -> outside W x) ->
  exists ph', rw_cells rsegs m' A [CB 16 ph'].
Proof.
  intros W m m' A ph xs H MU WM HX Hl HO.
  pose proof (proj1 (proj1 H)) as Wf. cbn in Wf. destruct Wf as [Wf _].
  pose proof (u8arr_of_rw_cells rsegs m A 16 ph H) as U.
  assert (Hl' : (length xs <= length ph)%nat) by lia.
  assert (HO' : forall x, A + Z.of_nat (length xs) <= x < A + Z.of_nat (length ph) -> outside W x)
    by (intros x Hx; apply HO; lia).
  pose proof (u8arr_after W m m' A ph xs U MU WM HX Hl' HO') as U2.
  exists (xs ++ skipn (length xs) ph).
  pose proof (rw_of_u8arr _ _ _ U2) as R.
  rewrite app_length, skipn_length in R. replace (length xs + (length ph - length xs))%nat with 16%nat in R by lia.
  exact R.
Qed.

Ltac disj_tac := cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia.

Ltac xp_rw H MU WM :=
  let X := fresh "X" in
  pose proof (rw_cells_transport rsegs _ _ _ _ _ H MU WM ltac:(disj_tac)) as X; clear H; rename X into H.

Ltac xp_u8 H MU WM :=
  let X := fresh "X" in
  pose proof (u8arr_transport rsegs _ _ _ _ _ H MU WM ltac:(disj_tac)) as X; clear H; rename X into H.

Ltac xp_ro H MU :=
  let X := fresh "X" in
  pose proof (ro_cells_transport rsegs _ _ _ _ _ H MU ltac:(disj_tac)) as X; clear H; rename X into H.

Lemma munch_ext : forall W W' m1 m2 m3, munch W m1 m2 -> munch W' m2 m3 ->
  (forall x, outside W x -> outside W' x) -> munch W m1 m3.
Proof. intros W W' m1 m2 m3 H1 H2 Hs x Hx. rewrite (H2 x (Hs _ Hx)). apply H1, Hx. Qed.

Ltac out_tac :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [outside] in Hx |- *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat split; try exact I; lia.

Ltac bool_dec :=
  repeat first [ rewrite (proj2 (Z.eqb_eq _ _)) by lia | rewrite (proj2 (Z.eqb_neq _ _)) by lia
               | rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia
               | rewrite (proj2 (Z.leb_le _ _)) by lia | rewrite (proj2 (Z.leb_gt _ _)) by lia ].

Ltac kind_tac := unfold kind, flen; bool_dec; reflexivity.

Ltac get_reg k :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
      let v := eval cbv beta iota delta [tget] in (match tget p R with Some v => v | None => Z_to_bv 64 0 end) in v
  end.

Ltac rep_reg k t tac := let v := get_reg k in replace v with t by tac.

Ltac norm_idx :=
  repeat match goal with
  | |- context [Z.add (Z.add ?q ?a) ?b] => is_Zlit a; is_Zlit b;
      let c := eval compute in (a + b) in replace (q + a + b) with (q + c) by lia
  end.

Ltac byte_facts :=
  repeat match goal with
  | |- context [@bv_unsigned 8%N ?c] =>
      lazymatch goal with
      | _ : 0 <= @bv_unsigned 8%N c < 256 |- _ => fail
      | _ => pose proof (byte_range c)
      end
  end.

Ltac hw_eq :=
  unfold incl, orig, hw;
  try change (0 =? 1) with false; try change (1 =? 1) with true; cbv iota;
  unfold fb; norm_idx; rewrite ?w32le_lor by apply byte_range; bits_eq.

Lemma hw_range : forall sw F q j, 0 <= hw sw F q j < 2 ^ 32.
Proof. intros sw F q j. unfold hw, w32le, fb. destruct sw; byte_facts; lia. Qed.

Lemma mod64_mod32 : forall x, (x mod 2 ^ 64) mod 2 ^ 32 = x mod 2 ^ 32.
Proof. intros x. Z.div_mod_to_equations. lia. Qed.

Lemma swrap_cases : forall I, 0 <= I < 2 ^ 32 ->
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 I)) = if I <? 2 ^ 31 then I else I - 2 ^ 32 + 2 ^ 64.
Proof.
  intros I HI. rewrite swrap32_eq, unsigned_lit_wrap. destruct (Z.ltb_spec I (2 ^ 31)).
  - rewrite (Z.mod_small (I + 2 ^ 31) (2 ^ 32)) by lia. replace (I + 2 ^ 31 - 2 ^ 31) with I by lia.
    apply Z.mod_small. lia.
  - rewrite <- (Z.mod_unique (I + 2 ^ 31) (2 ^ 32) 1 (I + 2 ^ 31 - 2 ^ 32)) by lia.
    rewrite <- (Z.mod_unique (I + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) (2 ^ 64) (-1) (I - 2 ^ 32 + 2 ^ 64)) by lia. reflexivity.
Qed.

Lemma eqb_swrap0 : forall I, 0 <= I < 2 ^ 32 -> bv_eqb (Z_to_bv 64 (bv_swrap 32 I)) (Z_to_bv 64 0) = (I =? 0).
Proof.
  intros I HI. unfold bv_eqb. rewrite swrap_cases by exact HI. rewrite unsigned_lit by lia.
  destruct (Z.ltb_spec I (2 ^ 31)); apply Bool.eq_iff_eq_true; rewrite !Z.eqb_eq; lia.
Qed.

Lemma zx32_val : forall v : word,
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned v) 32))) 32) = Z_to_bv 64 (bv_unsigned v mod 2 ^ 32).
Proof.
  intros v. f_equal. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite unsigned_lit_wrap.
  replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by reflexivity. rewrite Z.mul_mod_distr_r by lia.
  rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma uns_swrap_mod32 : forall I d, 0 <= I < 2 ^ 32 ->
  bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 I)) + d)) mod 2 ^ 32 = (I + d) mod 2 ^ 32.
Proof.
  intros I d HI. rewrite unsigned_lit_wrap, mod64_mod32. rewrite swrap_cases by exact HI.
  destruct (Z.ltb_spec I (2 ^ 31)); [reflexivity|].
  replace (I - 2 ^ 32 + 2 ^ 64 + d) with ((I + d) + (2 ^ 32 - 1) * 2 ^ 32) by lia. apply Z_mod_plus_full.
Qed.

Lemma uns_swrap_mod32_0 : forall I, 0 <= I < 2 ^ 32 -> bv_unsigned (Z_to_bv 64 (bv_swrap 32 I)) mod 2 ^ 32 = I.
Proof.
  intros I HI. rewrite swrap_cases by exact HI. destruct (Z.ltb_spec I (2 ^ 31)).
  - apply Z.mod_small. lia.
  - replace (I - 2 ^ 32 + 2 ^ 64) with (I + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma ro_agree_munch_apart : forall W m m', MemNorm.ro_agree rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> x < 0x10000 \/ (symaddr ImgPages.Ubsan.top) <= x) -> MemNorm.ro_agree rsegs m'.
Proof.
  intros W m m' HR HM HW. apply (ro_agree_munch W m m' HR HM). intros x Hx.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  rewrite <- (Z_to_bv_bv_unsigned x). apply ro_addr_apart; [lia|]. apply HW; [lia | exact Hx].
Qed.

Ltac ro_tac :=
  let x := fresh "x" in let Hr := fresh "Hr" in let Hx := fresh "Hx" in
  intros x Hr Hx; cbn [outside] in Hx; unfold img_apart in *; lia.

Lemma ltu_swrap : forall I k, 0 <= I < 2 ^ 32 -> 0 <= k < 2 ^ 31 ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 I)) (Z_to_bv 64 k) = (I <? k).
Proof.
  intros I k HI Hk. unfold bv_ltu. rewrite swrap_cases by exact HI. rewrite (unsigned_lit k) by lia.
  destruct (Z.ltb_spec I (2 ^ 31)); apply Bool.eq_iff_eq_true; rewrite !Z.ltb_lt; lia.
Qed.

Ltac big_tac :=
  unfold big_kind, kind, flen; bool_dec;
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.

Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Lemma rec_nth : forall (F tail : list byte) q I k, 0 <= q -> q + 16 + I <= Z.of_nat (length F) -> 0 <= k < I ->
  nth_error (firstn (Z.to_nat I) (skipn (Z.to_nat (q + 16)) F) ++ tail) (Z.to_nat k) =
  Some (nth (Z.to_nat (q + 16 + k)) F (Z_to_bv 8 0)).
Proof.
  intros F tail q I k Hq Hn Hk.
  rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite length_app, length_firstn, length_skipn; lia).
  rewrite app_nth1 by (rewrite length_firstn, length_skipn; lia).
  rewrite nth_firstn_lt by lia. rewrite nth_skipn_add. repeat f_equal. lia.
Qed.

Lemma firstn_rec : forall (B R : list byte) n, length B = n -> firstn n (B ++ R) = B.
Proof.
  intros B R n HB. rewrite firstn_app, HB, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. lia.
Qed.

Lemma mm_rec : forall (B R : list byte) (n : nat), (18 <= n)%nat -> length B = n ->
  firstn n (upd_bytes (B ++ R) 12 (firstn (n - 16) (skipn 16 (B ++ R)))) =
  firstn 12 B ++ firstn (n - 16) (skipn 16 B) ++ skipn (n - 4) B.
Proof.
  intros B R n Hn HB. unfold upd_bytes.
  rewrite (firstn_app 12), (skipn_app 16). rewrite HB.
  replace (12 - n)%nat with 0%nat by lia. replace (16 - n)%nat with 0%nat by lia. rewrite firstn_O, skipn_O, app_nil_r.
  rewrite (firstn_app (n - 16)). rewrite length_skipn, HB. replace (n - 16 - (n - 16))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r.
  rewrite length_firstn, length_skipn, HB. replace (Nat.min (n - 16) (n - 16)) with (n - 16)%nat by lia.
  rewrite (skipn_app (12 + (n - 16))). rewrite HB. replace (12 + (n - 16) - n)%nat with 0%nat by lia. rewrite skipn_O.
  replace (12 + (n - 16))%nat with (n - 4)%nat by lia.
  rewrite (app_assoc (firstn (n - 16) (skipn 16 B)) (skipn (n - 4) B) R).
  rewrite (app_assoc (firstn 12 B) (firstn (n - 16) (skipn 16 B) ++ skipn (n - 4) B) R).
  apply firstn_rec. rewrite !length_app, !length_firstn, !length_skipn, HB. lia.
Qed.

Lemma uns_mod32 : forall x, bv_unsigned (Z_to_bv 64 x) mod 2 ^ 32 = x mod 2 ^ 32.
Proof. intros x. rewrite unsigned_lit_wrap. apply mod64_mod32. Qed.

Lemma swrap_add_mod32 : forall I d, (bv_swrap 32 I + d) mod 2 ^ 32 = (I + d) mod 2 ^ 32.
Proof. intros I d. rewrite Zplus_mod, swrap32_mod, <- Zplus_mod. reflexivity. Qed.

Lemma zxb_val : forall c : byte, bv_unsigned (zxb c) = bv_unsigned c.
Proof. intros c. unfold zxb. apply unsigned_lit. pose proof (byte_range c). lia. Qed.

Lemma mm_rec_z : forall (B R : list byte) (I : Z), 18 <= I -> Z.of_nat (length B) = I ->
  firstn (Z.to_nat I) (upd_bytes (B ++ R) 12 (firstn (Z.to_nat (I + -16)) (skipn 16 (B ++ R)))) =
  firstn 12 B ++ firstn (Z.to_nat (I - 16)) (skipn 16 B) ++ skipn (Z.to_nat (I - 4)) B.
Proof.
  intros B R I HI HB.
  replace (Z.to_nat (I + -16)) with (Z.to_nat I - 16)%nat by lia.
  replace (Z.to_nat (I - 16)) with (Z.to_nat I - 16)%nat by lia.
  replace (Z.to_nat (I - 4)) with (Z.to_nat I - 4)%nat by lia.
  apply mm_rec; lia.
Qed.

Lemma mstl_transport : forall W m m' h b Fc p pv nx, mstl m h b Fc p pv nx -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W h 1304 -> disjoint_from W b (Z.of_nat (length Fc)) -> mstl m' h b Fc p pv nx.
Proof.
  intros W m m' h b Fc p pv nx H MU WM D1 D2.
  destruct (mstl_frame m h b Fc p pv nx H) as (cs & Hcs & HC & HB & _ & _ & REB).
  apply REB.
  - apply (rw_cells_transport rsegs W m m' h cs HC MU WM). rewrite Hcs. exact D1.
  - exact (bytes_at_transport rsegs W m m' b Fc HB MU D2).
Qed.

Ltac xp_mstl H MU WM :=
  let X := fresh "X" in
  pose proof (mstl_transport _ _ _ _ _ _ _ _ _ H MU WM ltac:(disj_tac) ltac:(disj_tac)) as X; clear H; rename X into H.

Ltac xp_stk H MU WM :=
  let X := fresh "X" in
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ H MU WM ltac:(disj_tac)) as X; clear H; rename X into H.
