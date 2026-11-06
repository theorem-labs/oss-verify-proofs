(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R6.v, with its module names and numbers changed; 1086 of its 1232 lines of code are new or changed and 1651 lines of the source are left out. *)
(* Stage 1 scratch: rp_id reads its frame g only at byte index >= 12, so it is determined by skipn 12 g. *)
(* libreac v1.9.0 (S_R7's b = 6 tail, IDENTICAL): pcs +0x58, cut names per v190-cutnames-A.tsv, the catalogue at
   CAT = 0x9e800, FRAME_BYTES / FRAME_SHADOW for the frame and its shadow, [A + 208] -> [A + 192], PRO's appended
   [A + 32]; the catalogue's AG / RELRO blocks are found in FrameAPI's lists by computation. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcReply RcFrag RcEmit
  RcEmitLib RcSynth RcSynthLib RcLay RcFin RcFinLib RcIdentModel RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel.
Import ListNotations.
Open Scope Z_scope.

Lemma nth_skipn_b : forall (l : list byte) m n d, nth n (skipn m l) d = nth (m + n) l d.
Proof.
  induction l as [|x l IH]; intros m n d.
  - rewrite skipn_nil. now rewrite !nth_overflow by (cbn [length]; lia).
  - destruct m as [|m]; [reflexivity|].
    replace (S m + n)%nat with (S (m + n)) by lia.
    cbn [skipn nth]. apply IH.
Qed.

Lemma skipn_skipn_b : forall b a (l : list byte), skipn a (skipn b l) = skipn (a + b) l.
Proof.
  induction b as [|b IH]; intros a l.
  - rewrite Nat.add_0_r. reflexivity.
  - replace (a + S b)%nat with (S (a + b)) by lia.
    destruct l as [|x l].
    + rewrite !skipn_nil. reflexivity.
    + cbn [skipn]. apply IH.
Qed.

Section Skip12.
Variables g g' : list byte.
Hypothesis Hsk : skipn 12 g = skipn 12 g'.

Lemma cpb_12 : forall i, (12 <= i)%nat -> cp_b g i = cp_b g' i.
Proof.
  intros i Hi. unfold cp_b.
  replace i with (12 + (i - 12))%nat at 1 by lia.
  replace i with (12 + (i - 12))%nat at 2 by lia.
  rewrite <- !nth_skipn_b. rewrite Hsk. reflexivity.
Qed.

Lemma cpv_12 : forall i, (12 <= i)%nat -> cp_v g i = cp_v g' i.
Proof. intros i Hi. unfold cp_v. rewrite (cpb_12 i Hi). reflexivity. Qed.

Lemma skip_12 : forall k, (12 <= k)%nat -> skipn k g = skipn k g'.
Proof.
  intros k Hk. replace k with ((k - 12) + 12)%nat by lia.
  rewrite <- !skipn_skipn_b. rewrite Hsk. reflexivity.
Qed.

Lemma irs_12 : ir_s g = ir_s g'.
Proof. unfold ir_s. apply (cpv_12 26). lia. Qed.

Lemma ir_12 : forall n, ir n g = ir n g'.
Proof.
  intros n.
  assert (Hfst : fst (ctrlparse n g) = fst (ctrlparse n g')).
  { unfold ctrlparse, cp_hdr.
    rewrite (cpv_12 12 ltac:(lia)), (cpv_12 13 ltac:(lia)).
    destruct ((50 <=? n) && (cp_v g' 12 =? 136) && (cp_v g' 13 =? 25)); cbn [fst]; [|reflexivity].
    unfold cp_kind, cp_type, cp_amp.
    rewrite (cpv_12 16 ltac:(lia)), (cpv_12 17 ltac:(lia)), (cpv_12 18 ltac:(lia)),
            (cpv_12 19 ltac:(lia)), (cpv_12 22 ltac:(lia)), (cpv_12 32 ltac:(lia)),
            (cpv_12 33 ltac:(lia)), (cpv_12 34 ltac:(lia)), (cpv_12 35 ltac:(lia)).
    reflexivity. }
  assert (Hblk : ir_blk g = ir_blk g') by (unfold ir_blk; apply (skip_12 18); lia).
  assert (Hrec : ir_rec g = ir_rec g').
  { unfold ir_rec. rewrite irs_12. rewrite (skip_12 34 ltac:(lia)). reflexivity. }
  unfold ir. rewrite Hfst, irs_12, Hblk, Hrec.
  rewrite (cpv_12 34 ltac:(lia)), (cpv_12 35 ltac:(lia)), (cpv_12 32 ltac:(lia)),
          (cpv_12 33 ltac:(lia)), (cpv_12 27 ltac:(lia)).
  assert (Hs0 : (12 <= Z.to_nat (26 + ir_s g'))%nat).
  { unfold ir_s, cp_v. pose proof (bv_unsigned_in_range 8 (cp_b g' 26)) as Hr. lia. }
  rewrite (cpv_12 (Z.to_nat (26 + ir_s g')) Hs0).
  reflexivity.
Qed.

Lemma raddr_12 : r_addr g = r_addr g'.
Proof. unfold r_addr. rewrite (cpv_12 36 ltac:(lia)), (cpv_12 37 ltac:(lia)). reflexivity. Qed.

Lemma rpl_12 : r_pl g = r_pl g'.
Proof.
  unfold r_pl, bsl, r_pll. rewrite irs_12.
  change (Z.to_nat 38) with 38%nat.
  rewrite (skip_12 38 ltac:(lia)). reflexivity.
Qed.

Lemma rpid_12 : forall idb n, rp_id idb n g = rp_id idb n g'.
Proof.
  intros idb n. unfold rp_id. rewrite (ir_12 n).
  destruct (ir n g'); [|reflexivity].
  rewrite raddr_12, rpl_12. reflexivity.
Qed.

End Skip12.

(* ===== Model facts: the b = 6, n_6 = 0 identity-record check against the catalogue row =====
   Every fact below rests on ONE computation over the image (r7t_tbl).  Each `vm_compute` invocation pays the
   VM's compilation cost of the image constant rsegs, so the eleven rows and the three live records are checked
   in a single boolean rather than in a case split with one computation per case. *)

(* The catalogue row i and the round-trip width uw as a function of the row index. *)
Definition p_uw (i : Z) : Z := bm_uw (CAT + CAT_ROW * i) (firstn 8 (skipn 16 (rowb i))).

(* An input whose seventh byte selects row i and turns the round trip on (mode = 2 i + 1). *)
Definition canon (i : Z) : list byte := map (Z_to_bv 8) [0; 0; 0; 0; 0; 0; 2 * i + 1].

Definition leqb (l1 l2 : list byte) : bool := if list_eq_dec (@bv_eq_dec 8) l1 l2 then true else false.

Lemma leqb_eq : forall l1 l2, leqb l1 l2 = true -> l1 = l2.
Proof.
  intros l1 l2 H. unfold leqb in H.
  destruct (list_eq_dec (@bv_eq_dec 8) l1 l2) as [E|E]; [exact E | discriminate H].
Qed.

Definition IX : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10].
Definition JX : list Z := [0; 2; 3].

(* Row i: the width is a valid even width (so E(b) is decided by the row's has-identity-record field alone), and
   the field is zero only for rows 0, 2 and 3. *)
Definition r7t_row_b (i : Z) : bool :=
  em_wok (p_uw i) && implb (em_hid (rowb i) =? 0) ((i =? 0) || (i =? 2) || (i =? 3)).

(* Row j (one of the three with a zero field): the turn-6 identity record of canon j has its has_fw byte (+ 2) and
   its has_reac_version byte (+ 36) non-zero and its firmware / major / minor / patch halfwords equal to the row's
   bytes at + 266, + 268, + 270, + 272; the row's field at + 56 is four zero bytes; canon j selects row j and
   emits nothing at turn 6. *)
Definition r7t_rec_b (j : Z) : bool :=
  Nat.eqb (length (RID (canon j) 6)) 38 &&
  negb (bv_unsigned (nth 2 (RID (canon j) 6) (Z_to_bv 8 0)) =? 0) &&
  negb (bv_unsigned (nth 36 (RID (canon j) 6) (Z_to_bv 8 0)) =? 0) &&
  leqb (firstn 2 (RID (canon j) 6)) (firstn 2 (skipn 266 (rowb j))) &&
  leqb (firstn 2 (skipn 22 (RID (canon j) 6))) (firstn 2 (skipn 268 (rowb j))) &&
  leqb (firstn 2 (skipn 24 (RID (canon j) 6))) (firstn 2 (skipn 270 (rowb j))) &&
  leqb (firstn 2 (skipn 26 (RID (canon j) 6))) (firstn 2 (skipn 272 (rowb j))) &&
  leqb (firstn 4 (skipn 56 (rowb j))) (repeat (Z_to_bv 8 0) 4) &&
  (istar (canon j) =? j) && (rt_n (canon j) 6 =? 0).

(* Row i is mapped: the image holds its 296 bytes, so rowb i is the image's bytes and not the fallback. *)
Definition r7t_img_b (i : Z) : bool :=
  match Image.image_bytes rsegs (CAT + CAT_ROW * i) 296 with Some _ => true | None => false end.

Lemma r7t_tbl : forallb r7t_row_b IX && forallb r7t_rec_b JX && forallb r7t_img_b IX = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r7t_in_IX : forall i, 0 <= i <= 10 -> In i IX.
Proof.
  intros i H. unfold IX.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10)
    by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
    cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

Lemma r7t_row_true : forall i, 0 <= i <= 10 -> r7t_row_b i = true.
Proof.
  intros i Hi. pose proof r7t_tbl as T. apply andb_true_iff in T as [T _]. apply andb_true_iff in T as [T _].
  rewrite forallb_forall in T. exact (T i (r7t_in_IX i Hi)).
Qed.

Lemma r7t_rec_true : forall j, (j = 0 \/ j = 2 \/ j = 3) -> r7t_rec_b j = true.
Proof.
  intros j Hj. pose proof r7t_tbl as T. apply andb_true_iff in T as [T _]. apply andb_true_iff in T as [_ T].
  rewrite forallb_forall in T. apply T. unfold JX.
  destruct Hj as [->|[->| ->]]; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

Lemma r7t_row_img : forall i, 0 <= i <= 10 -> Image.image_bytes rsegs (CAT + CAT_ROW * i) 296 = Some (rowb i).
Proof.
  intros i Hi. pose proof r7t_tbl as T. apply andb_true_iff in T as [_ T].
  rewrite forallb_forall in T. pose proof (T i (r7t_in_IX i Hi)) as Ti. unfold r7t_img_b in Ti.
  unfold rowb, img. revert Ti.
  destruct (Image.image_bytes rsegs (CAT + CAT_ROW * i) 296) as [l|]; intros Ti; [reflexivity | discriminate Ti].
Qed.

Lemma row_len : forall i, length (rowb i) = 296%nat.
Proof.
  intros i. unfold rowb, img. destruct (Image.image_bytes rsegs (CAT + CAT_ROW * i) 296) eqn:E.
  - exact (Image.image_bytes_length rsegs 296 _ _ E).
  - apply repeat_length.
Qed.

Lemma rtX_len : forall inp b, length (rt_X inp b) = 32%nat.
Proof.
  intros inp b. unfold rt_X, reac_ctrl_build_as_c.ba_X.
  assert (HZ : length (ly_Z (mrow inp) (rt_mb inp) (rt_nb inp) b) = 32%nat).
  { unfold ly_Z, ly_zero. destruct (mrow inp =? 0); [apply repeat_length|].
    destruct (rc (rt_mb inp) b =? 1); [|apply repeat_length].
    apply rs_synth_len. unfold rt_mb. apply row_len. }
  destruct (b <=? 1); [apply rcf_stamp32_len; exact HZ | exact HZ].
Qed.

Lemma rtuw_istar : forall inp, rt_uw inp = p_uw (istar inp).
Proof. intros inp. unfold rt_uw, p_uw, rt_mb, mrow. reflexivity. Qed.

Lemma istar_range : forall inp, 0 <= istar inp <= 10.
Proof.
  intros inp. unfold istar, CAT_N. pose proof (Z.mod_pos_bound (mode inp / 2) 11 ltac:(lia)). lia.
Qed.

Lemma em_wok_all : forall inp, em_wok (rt_uw inp) = true.
Proof.
  intros inp. rewrite rtuw_istar.
  pose proof (r7t_row_true (istar inp) (istar_range inp)) as T.
  unfold r7t_row_b in T. apply andb_true_iff in T as [T _]. exact T.
Qed.

Lemma rtn_simp : forall inp b,
  rt_n inp b = if (b <=? 4) || negb (em_hid (rt_mb inp) =? 0) then 52 + 36 * rt_uw inp else 0.
Proof.
  intros inp b. unfold rt_n, rt_E, reac_ctrl_build_as_c.ba_E. rewrite (em_wok_all inp). reflexivity.
Qed.

Lemma hid0_cases : forall inp, em_hid (rt_mb inp) = 0 -> istar inp = 0 \/ istar inp = 2 \/ istar inp = 3.
Proof.
  intros inp H.
  pose proof (r7t_row_true (istar inp) (istar_range inp)) as T.
  unfold r7t_row_b in T. apply andb_true_iff in T as [_ T].
  unfold rt_mb in H. rewrite H in T. cbn [Z.eqb implb] in T.
  apply orb_true_iff in T as [T|T]; [apply orb_true_iff in T as [T|T]|].
  - left. apply Z.eqb_eq. exact T.
  - right; left. apply Z.eqb_eq. exact T.
  - right; right. apply Z.eqb_eq. exact T.
Qed.

Lemma rtn_le4 : forall inp b, b <= 4 -> rt_n inp b = 52 + 36 * rt_uw inp.
Proof.
  intros inp b Hb. rewrite rtn_simp.
  assert (Hb4 : (b <=? 4) = true) by (apply (proj2 (Z.leb_le _ _)); lia).
  rewrite Hb4. reflexivity.
Qed.

Lemma n6_hid0 : forall inp, rt_n inp 6 = 0 -> em_hid (rt_mb inp) = 0.
Proof.
  intros inp H.
  destruct (Z.eqb_spec (em_hid (rt_mb inp)) 0) as [He|He]; [exact He|].
  exfalso. pose proof (em_wok_all inp) as Hw. destruct (em_wok_range _ Hw) as [Hlo _].
  assert (He0 : (em_hid (rt_mb inp) =? 0) = false) by (apply (proj2 (Z.eqb_neq _ _)); exact He).
  assert (Hv : rt_n inp 6 = 52 + 36 * rt_uw inp) by (rewrite rtn_simp, He0; reflexivity).
  lia.
Qed.

(* rt_n and rt_X depend on the input only through the row index istar.  The constants are unfolded at once with
   cbv delta: a sequential unfold of rt_mb before rt_nb leaves the rt_mb that rt_nb's body brings back folded, and
   a reflexivity on rt_mb inp against rt_mb inp' then explores the image constant. *)
Lemma rtn_istar : forall inp inp' b, istar inp = istar inp' -> rt_n inp b = rt_n inp' b.
Proof.
  intros inp inp' b He. cbv beta delta [rt_n rt_E rt_mb rt_uw mrow]. rewrite He. reflexivity.
Qed.

Lemma rtX_istar : forall inp inp' b, istar inp = istar inp' -> rt_X inp b = rt_X inp' b.
Proof.
  intros inp inp' b He. cbv beta delta [rt_X rt_nb rt_mb mrow]. rewrite He. reflexivity.
Qed.

(* The frame bytes that rp_id reads start at byte index 12 (the fixed header + the control block rt_X). *)
Lemma firstn50_6_6_6_32 : forall (a b c d e : list byte),
  length a = 6%nat -> length b = 6%nat -> length c = 6%nat -> length d = 32%nat ->
  firstn 50 (a ++ b ++ c ++ d ++ e) = a ++ b ++ c ++ d.
Proof.
  intros a b c d e Ha Hb Hc Hd.
  replace 50%nat with (length a + (length b + (length c + (length d + 0))))%nat
    by (rewrite Ha, Hb, Hc, Hd; reflexivity).
  rewrite firstn_app_2, firstn_app_2, firstn_app_2, firstn_app_2.
  rewrite firstn_O, !app_nil_r. reflexivity.
Qed.

(* A turn's frame: the six input bytes OUR, the round trip's box, the six fixed header bytes and the 32-byte
   control block.  fr50 keeps exactly those 50 bytes, whatever the turn's length is. *)
Lemma rtg_form : forall inp b, rt_g inp b =
  OUR inp ++ box6 ++ [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 52; Z_to_bv 8 18; Z_to_bv 8 205; Z_to_bv 8 234]
    ++ rt_X inp b.
Proof.
  intros inp b. unfold rt_g, fr50, rt_F, em_fr, em_hdr, zb.
  replace (CNT16 mod 256) with 52 by reflexivity.
  replace (CNT16 / 256) with 18 by reflexivity.
  rewrite <- !app_assoc.
  apply firstn50_6_6_6_32; [apply OUR_length | reflexivity | reflexivity | apply rtX_len].
Qed.

Lemma skipn12_app : forall (a b r : list byte), length (a ++ b) = 12%nat -> skipn 12 (a ++ b ++ r) = r.
Proof.
  intros a b r Hab. rewrite app_assoc. rewrite <- Hab.
  rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_O. reflexivity.
Qed.

Lemma tg12 : forall inp b, skipn 12 (rt_g inp b) =
  [Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 52; Z_to_bv 8 18; Z_to_bv 8 205; Z_to_bv 8 234] ++ rt_X inp b.
Proof.
  intros inp b. rewrite rtg_form. apply skipn12_app.
  rewrite length_app, OUR_length. reflexivity.
Qed.

(* rt_st steps for the n_6 = 0 run (every turn 0..4 emits a frame, turn 5 does not). *)
Lemma rtst_skip : forall inp b, rt_n inp (Z.of_nat b) = 0 -> rt_st inp (S b) = rt_st inp b.
Proof. intros inp b H. cbn [rt_st]. cbv zeta. rewrite H. reflexivity. Qed.

Lemma rtst_else : forall inp b, rt_n inp (Z.of_nat b) <> 0 ->
  (Z.of_nat b =? 3) = false -> (Z.of_nat b =? 4) = false ->
  (Z.of_nat b =? 5) = false -> (Z.of_nat b =? 6) = false -> rt_st inp (S b) = rt_st inp b.
Proof.
  intros inp b Hn H3 H4 H5 H6. cbn [rt_st]. cbv zeta.
  destruct (Z.eqb_spec (rt_n inp (Z.of_nat b)) 0) as [E|E]; [contradiction|].
  rewrite H3, H4, H5, H6. reflexivity.
Qed.

Lemma rtst_reply : forall inp b, rt_n inp (Z.of_nat b) <> 0 ->
  ((Z.of_nat b =? 3) = true \/ (Z.of_nat b =? 4) = true) ->
  rt_st inp (S b) =
    (rp_id (fst (rt_st inp b)) (rt_n inp (Z.of_nat b)) (rt_g inp (Z.of_nat b)), snd (rt_st inp b)).
Proof.
  intros inp b Hn Hor. cbn [rt_st]. cbv zeta.
  destruct (Z.eqb_spec (rt_n inp (Z.of_nat b)) 0) as [E|E]; [contradiction|].
  destruct Hor as [H3|H4]; [rewrite H3 | rewrite H4, orb_true_r]; reflexivity.
Qed.

(* The fragment state keeps its 72 bytes across a turn (a Theorem Labs lane's Seg/R15.v r15_fg_st_len, a working branch). *)
Lemma r7t_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, fg_class.
  change ((1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0)) with false. cbv iota.
  destruct (fg_fr len g) eqn:Efr; cbn [negb]; [|exact Hs].
  assert (Hn : 1 <= fg_n g <= 22).
  { unfold fg_fr in Efr. rewrite !andb_true_iff in Efr. destruct Efr as [[[_ H1] H2] _].
    apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
  assert (Hb : forall bs i, 0 <= bat bs i).
  { intros bs i. unfold bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia. }
  assert (Hbody : length (fg_body g) = Z.to_nat (fg_n g)).
  { unfold fg_body, bsl. rewrite length_firstn, length_skipn, Hg. lia. }
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. unfold fg_first. rewrite !length_app, Hbody, length_skipn, Hs. cbn [length].
    unfold bsl. rewrite length_firstn, length_skipn, Hg. lia.
  - destruct (fg_keep st g) eqn:Ek; cbn [negb]; [|cbn [fg_next]; unfold fg_clear;
      rewrite !length_app, length_firstn, length_skipn, Hs; cbn [length]; lia].
    assert (HT : fg_T st g <= 64).
    { unfold fg_keep in Ek. rewrite !andb_true_iff in Ek. destruct Ek as [_ H]. apply Z.leb_le in H. exact H. }
    assert (Hj : length (fg_join st g) = 72%nat).
    { unfold fg_join. unfold fg_T, fg_lf in HT. pose proof (Hb st 7).
      rewrite !length_app, Hbody, length_firstn, length_skipn, Hs. unfold fg_T, fg_lf. lia. }
    destruct (fg_close st g); cbn [negb fg_next]; unfold fg_clear;
      rewrite !length_app, length_firstn, length_skipn, Hj; cbn [length]; lia.
Qed.

(* The identity record of every turn has 38 bytes and the fragment record 72 (a Theorem Labs lane's Seg/R15.v r15_RS_len): Seg/R7.v
   keeps both across the allocator call as frame bytes. *)
Lemma r7t_RS_len : forall inp b, length (RID inp b) = 38%nat /\ length (RFG inp b) = 72%nat.
Proof.
  intros inp b. unfold RID, RFG. induction b as [|b [IH1 IH2]]; [split; reflexivity|].
  cbn [rt_st].
  destruct (rt_n inp (Z.of_nat b) =? 0); [exact (conj IH1 IH2)|].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); cbn [fst snd].
  - split; [|exact IH2]. unfold rp_id. destruct (RcReply.ir _ _); [apply RcIdentModel.ING_length; exact IH1 | exact IH1].
  - destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)); cbn [fst snd]; [|exact (conj IH1 IH2)].
    split.
    + unfold fg_id. destruct (fg_rf _ _ _ =? 1); [apply RcIdentModel.ING_length; exact IH1 | exact IH1].
    + apply r7t_fg_st_len; [exact IH2 | apply fr50_length].
Qed.

(* With n_6 = 0 the row has no identity record, so turns 5 and 6 emit nothing and turns 0..4 do; only the reply
   turns 3 and 4 move the identity record, from ID0.  The model terms are generalised before the closing
   reflexivity: a mismatch then fails at once instead of unfolding rt_g into the image. *)
Lemma rid6_unfold : forall inp, rt_n inp 6 = 0 ->
  RID inp 6 = rp_id (rp_id ID0 (rt_n inp 3) (rt_g inp 3)) (rt_n inp 4) (rt_g inp 4).
Proof.
  intros inp H6.
  pose proof (n6_hid0 inp H6) as Hhid.
  assert (N : forall bb, 0 <= bb <= 4 -> rt_n inp bb <> 0).
  { intros bb Hb. rewrite (rtn_le4 inp bb ltac:(lia)).
    pose proof (em_wok_all inp) as Hw. destruct (em_wok_range _ Hw) as [Huw _]. lia. }
  assert (H5 : rt_n inp 5 = 0) by (rewrite rtn_simp; rewrite Hhid; reflexivity).
  unfold RID.
  rewrite (rtst_skip inp 5) by exact H5.
  rewrite (rtst_reply inp 4) by (first [apply N; lia | right; reflexivity]).
  rewrite (rtst_reply inp 3) by (first [apply N; lia | left; reflexivity]).
  rewrite (rtst_else inp 2) by (first [apply N; lia | reflexivity]).
  rewrite (rtst_else inp 1) by (first [apply N; lia | reflexivity]).
  rewrite (rtst_else inp 0) by (first [apply N; lia | reflexivity]).
  cbn [rt_st fst snd].
  change (Z.of_nat 3) with 3. change (Z.of_nat 4) with 4.
  generalize (rt_g inp 4); intro gg4. generalize (rt_n inp 4); intro nn4.
  generalize (rt_g inp 3); intro gg3. generalize (rt_n inp 3); intro nn3.
  reflexivity.
Qed.

(* Two inputs with the same row have the same turn-6 identity record: the two reply turns read their frame only
   from byte 12 on, and from there the frame is the fixed header and the row's control block. *)
Lemma rid6_istar : forall inp inp', istar inp = istar inp' -> rt_n inp 6 = 0 -> rt_n inp' 6 = 0 ->
  RID inp 6 = RID inp' 6.
Proof.
  intros inp inp' He H6 H6'.
  rewrite (rid6_unfold inp H6), (rid6_unfold inp' H6').
  rewrite (rtn_istar inp inp' 3 He), (rtn_istar inp inp' 4 He).
  rewrite (rpid_12 (rt_g inp 3) (rt_g inp' 3)
             ltac:(rewrite !tg12, (rtX_istar inp inp' 3 He); reflexivity)).
  rewrite (rpid_12 (rt_g inp 4) (rt_g inp' 4)
             ltac:(rewrite !tg12, (rtX_istar inp inp' 4 He); reflexivity)).
  generalize (rt_g inp' 4); intro gg4. generalize (rt_n inp' 4); intro nn4.
  generalize (rt_g inp' 3); intro gg3. generalize (rt_n inp' 3); intro nn3.
  reflexivity.
Qed.

(* The ten conjuncts of r7t_rec_b, read off the one computation. *)
Lemma r7t_rec_parts : forall j, (j = 0 \/ j = 2 \/ j = 3) ->
  length (RID (canon j) 6) = 38%nat /\
  bv_unsigned (nth 2 (RID (canon j) 6) (Z_to_bv 8 0)) <> 0 /\
  bv_unsigned (nth 36 (RID (canon j) 6) (Z_to_bv 8 0)) <> 0 /\
  firstn 2 (RID (canon j) 6) = firstn 2 (skipn 266 (rowb j)) /\
  firstn 2 (skipn 22 (RID (canon j) 6)) = firstn 2 (skipn 268 (rowb j)) /\
  firstn 2 (skipn 24 (RID (canon j) 6)) = firstn 2 (skipn 270 (rowb j)) /\
  firstn 2 (skipn 26 (RID (canon j) 6)) = firstn 2 (skipn 272 (rowb j)) /\
  firstn 4 (skipn 56 (rowb j)) = repeat (Z_to_bv 8 0) 4 /\
  istar (canon j) = j /\ rt_n (canon j) 6 = 0.
Proof.
  intros j Hj. pose proof (r7t_rec_true j Hj) as T. unfold r7t_rec_b in T.
  apply andb_true_iff in T as [T Hn6].
  apply andb_true_iff in T as [T Hist].
  apply andb_true_iff in T as [T H56].
  apply andb_true_iff in T as [T H26].
  apply andb_true_iff in T as [T H24].
  apply andb_true_iff in T as [T H22].
  apply andb_true_iff in T as [T H00].
  apply andb_true_iff in T as [T H36].
  apply andb_true_iff in T as [Hlen H02].
  split; [apply Nat.eqb_eq; exact Hlen|].
  split; [apply Z.eqb_neq; apply negb_true_iff in H02; exact H02|].
  split; [apply Z.eqb_neq; apply negb_true_iff in H36; exact H36|].
  split; [apply leqb_eq; exact H00|].
  split; [apply leqb_eq; exact H22|].
  split; [apply leqb_eq; exact H24|].
  split; [apply leqb_eq; exact H26|].
  split; [apply leqb_eq; exact H56|].
  split; [apply Z.eqb_eq; exact Hist | apply Z.eqb_eq; exact Hn6].
Qed.

Lemma canon_istar_val : forall j, (j = 0 \/ j = 2 \/ j = 3) -> istar (canon j) = j.
Proof. intros j Hj. apply (r7t_rec_parts j Hj). Qed.

Lemma canon_n6_val : forall j, (j = 0 \/ j = 2 \/ j = 3) -> rt_n (canon j) 6 = 0.
Proof. intros j Hj. apply (r7t_rec_parts j Hj). Qed.

(* The identity-record check of the b = 6, n_6 = 0 tail for the input the segment runs on: the turn-6 identity
   record is the one of canon (istar inp), and the catalogue row's own bytes match it. *)
Lemma r7t_model : forall inp, rt_n inp 6 = 0 ->
  length (RID inp 6) = 38%nat /\
  bv_unsigned (nth 2 (RID inp 6) (Z_to_bv 8 0)) <> 0 /\
  bv_unsigned (nth 36 (RID inp 6) (Z_to_bv 8 0)) <> 0 /\
  firstn 2 (RID inp 6) = firstn 2 (skipn 266 (rowb (istar inp))) /\
  firstn 2 (skipn 22 (RID inp 6)) = firstn 2 (skipn 268 (rowb (istar inp))) /\
  firstn 2 (skipn 24 (RID inp 6)) = firstn 2 (skipn 270 (rowb (istar inp))) /\
  firstn 2 (skipn 26 (RID inp 6)) = firstn 2 (skipn 272 (rowb (istar inp))) /\
  firstn 4 (skipn 56 (rowb (istar inp))) = repeat (Z_to_bv 8 0) 4 /\
  0 <= istar inp <= 10.
Proof.
  intros inp H6.
  pose proof (istar_range inp) as Hrange.
  assert (Hj : istar inp = 0 \/ istar inp = 2 \/ istar inp = 3)
    by exact (hid0_cases inp (n6_hid0 inp H6)).
  assert (Hrid : RID inp 6 = RID (canon (istar inp)) 6).
  { apply (rid6_istar inp (canon (istar inp))).
    - symmetry. apply canon_istar_val. exact Hj.
    - exact H6.
    - apply canon_n6_val. exact Hj. }
  destruct (r7t_rec_parts (istar inp) Hj) as (Hlen & H02 & H36 & H00 & H22 & H24 & H26 & H56 & _ & _).
  rewrite Hrid.
  split; [exact Hlen|]. split; [exact H02|]. split; [exact H36|].
  split; [exact H00|]. split; [exact H22|]. split; [exact H24|].
  split; [exact H26|]. split; [exact H56 | exact Hrange].
Qed.

(* ===== The instruction-level run of the tail =====
   Imports for the run and for the segment (the model section above needs none of them). *)
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac
  Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d
  YO09 YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_rt2_b2 Tac_rt_b2 Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_set_shadow_c asan_set_shadow memset
  reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcAsanLib.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import RoAdapt.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.

Lemma r7t_zxb_nz : forall h : byte, bv_unsigned h <> 0 -> negb (bv_eqb (zxb h) (Z_to_bv 64 0)) = true.
Proof.
  intros h H. unfold zxb, bv_eqb. pose proof (bv_unsigned_in_range 8 h) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. rewrite !MState.unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. exact H.
Qed.
Lemma r7t_eqb_refl : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.
Lemma r7t_le1_m8 : le1 (Z_to_bv 64 (-8)) = [Z_to_bv 8 248].
Proof. unfold le1, Z_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.

(* A branch whose condition is decided by computation, by reflexivity of bv_eqb (a comparison of a register with
   itself) or by a byte known to be non-zero. *)
Ltac r7t_br := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true by
                (symmetry; first [apply r7t_eqb_refl | apply r7t_zxb_nz; assumption | reflexivity]); cbv iota
            | replace c with false by (symmetry; reflexivity); cbv iota ]
  | _ => idtac end.
Ltac r7t_st := step; r7t_br.
(* `srli rd,rs,3` of an address X in range: the shifted word is X / 8. *)
Ltac r7t_sr X := rewrite (MState.unsigned_lit X) by lia; rewrite rc_shr3.
(* `sb s2,off(s3)` with s2 = -8: the stored byte list is [248], which cell_of_bytes reads as a C1 cell. *)
Ltac r7t_sb := step;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 _)) _) => rewrite r7t_le1_m8; mem_after_store
  | _ => idtac end.

(* The b = 6, n_6 = 0 tail: 0x815ec -> 0x8194c -> 0x81990 .. 0x81abc (the has_identity_record checks of the
   round trip's identity record against the catalogue row, all taken; the row's s32 at + 56 is 0, so the name
   comparison at 0x81a80 .. 0x81abc is skipped) -> 0x81ac8 (14 frame-shadow stores of 0xf8) -> meta_fill_f8 over
   [S(fr) + 68, S(fr) + 255) -> the P2 cut 0x81b10.  s11 keeps the word loaded from [A + 144] at 0x81994 (no later
   instruction writes it, and meta_fill_f8 keeps it). *)
Lemma r7_tail_evt : asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A IDa row S3 : Z) (v128 v144 : word)
         (h2 h36 : byte) (w0 w1 w2 w3 : word) (j1 j2 jsh jfl : list byte),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 -> s5 = Z_to_bv 64 IDa -> s10 = Z_to_bv 64 2147450880 ->
    s3 = Z_to_bv 64 S3 -> s7 = Z_to_bv 64 6 ->
    0 <= A -> A + 416 <= 2 ^ 47 -> 0 <= IDa -> IDa + 38 <= 2 ^ 47 -> 0 <= row -> row + 296 <= 2 ^ 47 ->
    2147450880 <= S3 -> S3 + 392 <= 2 ^ 47 -> S3 + 392 <= A ->
    (forall i, 0 <= i < 187 -> in_shadow (S3 + 68 + i)) ->
    ro_cells rsegs m (A + 112) [C8 (Z_to_bv 64 row)] -> ro_cells rsegs m (A + 128) [C8 v128] ->
    ro_cells rsegs m (A + 144) [C8 v144] -> ro_cells rsegs m (A + 152) [C8 (Z_to_bv 64 (S3 + 68))] ->
    ro_cells rsegs m IDa [C2 w0; C1 h2; CB 19 j1; C2 w1; C2 w2; C2 w3; CB 8 j2; C1 h36] ->
    bv_unsigned h2 <> 0 -> bv_unsigned h36 <> 0 ->
    ro_cells rsegs m (row + 266) [C2 w0; C2 w1; C2 w2; C2 w3] ->
    ro_cells rsegs m (row + 56) [C4 (Z_to_bv 64 0)] ->
    ro_cells rsegs m ((row + 266) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m ((row + 268) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m ((row + 270) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m ((row + 272) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m ((row + 56) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m (S3 + 68) [CB 187 jsh] -> rw_cells rsegs m (S3 + 272) [CB 19 jfl] ->
    length jsh = 187%nat -> length jfl = 19%nat ->
    asan_cells m -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81b10) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 27 = v144 /\
         munch [(S3 + 68, S3 + 255); (S3 + 272, S3 + 291)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' (S3 + 68) [CB 187 (repeat (Z_to_bv 8 0xf8) 187)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)).
Proof.
  intros SSF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A IDa row S3 v128 v144 h2 h36 w0 w1 w2 w3 j1 j2 jsh jfl -> -> -> -> -> -> HA0 HA1 HI0 HI1 HR0 HR1
    HS0 HS1 HSA HSH CA CA128 CA144 CA152 CI Hh2 Hh36 CR CR56 S266 S268 S270 S272 S56 RWsh RWfl Ljsh Ljfl HAC HMI.
  unfold asan_set_shadow_f8_contract, asan_set_shadow_contract, ASAN_SET_SHADOW_F8 in SSF.
  pose proof (munch_refl [(S3 + 68, S3 + 255); (S3 + 272, S3 + 291)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  r7t_st. (* 815ec beqz a0 -> 8194c *)
  r7t_st. r7t_st. r7t_st. r7t_st. r7t_st. (* 8194c .. 8195c -> 81990 *)
  r7t_st. r7t_st. r7t_st. (* 81990 lbu a0,2(s5) ; 81994 ld s11,144(s1) ; 81998 bnez a0 -> 819a0 *)
  r7t_st. r7t_st. r7t_st. r7t_sr (row + 266). r7t_st. r7t_st. r7t_st. r7t_st. r7t_st. r7t_st. (* 819a0 .. -> 819cc *)
  r7t_st. r7t_st. (* 819cc lbu a0,36(s5) ; 819d0 bnez a0 -> 819d8 *)
  r7t_st. r7t_st. r7t_st. r7t_sr (row + 268). r7t_st. r7t_st. r7t_st. r7t_st. r7t_st. r7t_st. (* 819d8 .. -> 81a04 *)
  r7t_st. r7t_st. r7t_st. r7t_sr (row + 270). r7t_st. r7t_st. r7t_st. r7t_st. r7t_st. r7t_st. (* 81a04 .. -> 81a30 *)
  r7t_st. r7t_st. r7t_st. r7t_sr (row + 272). r7t_st. r7t_st. r7t_st. r7t_st. r7t_st. r7t_st. (* 81a30 .. -> 81a5c *)
  r7t_st. r7t_st. r7t_st. r7t_sr (row + 56). r7t_st. r7t_st. r7t_st. (* 81a5c .. 81a70 -> 81a78 *)
  r7t_st. r7t_st. (* 81a78 lw a0,0(a0) ; 81a7c beqz a0 -> 81ac8 *)
  r7t_st. do 14 r7t_sb. (* 81ac8 li s2,-8 ; 81acc .. 81b00 the 14 frame-shadow stores *)
  r7t_st. r7t_st. r7t_st. (* 81b04 li a1,187 ; 81b08 ld a0,152(s1) ; 81b0c jal meta_fill_f8 *)
  eapply evt_cut.
  { eapply SSF with (junk := jsh).
    - rewrite !MState.unsigned_lit by lia. exact HSH.
    - rewrite !MState.unsigned_lit by lia. change (Z.to_nat 187) with 187%nat. exact RWsh.
    - eapply fl_asan_cells; [exact HAC | exact MU |]. intros x Hx. unfold RT_LO, RT_HI in Hx.
      cbn. split; [lia | split; [lia | exact Logic.I]].
    - exact HMI. }
  intros ms' PO. unfold asan_set_shadow_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & RW2).
  rewrite !MState.unsigned_lit in MU2, RW2 by lia.
  replace (ret_pc (Z_to_bv 64 0x81b10)) with (Z_to_bv 64 0x81b10)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
    intros x Hx. cbn in Hx |- *. destruct Hx as (Hx1 & _). split; [lia | exact Logic.I]. }
  split; [eapply wmono_trans; [exact WM | exact WM2]|].
  split; [exact MI2|].
  change (Z.to_nat 187) with 187%nat in RW2. exact RW2.
Qed.

(* ===== What the segment reads off the state ===== *)

(* n readable bytes from a are some n-byte list at a (Seg/R7.v's r7_bytes_ex). *)
Lemma r7t_bytes_ex : forall (m : word -> option byte) (n : nat) a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> exists b, mbyte rsegs m x = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros a Ha Hn Hrd.
  - exists []. split; [|reflexivity]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (Hrd a ltac:(lia)) as (b0 & Hb0).
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply Hrd; lia)) as (bs & Hbs & Hl).
    exists (b0 :: bs). split; [|cbn [length]; rewrite Hl; reflexivity].
    destruct Hbs as (_ & _ & Hbs). split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi.
    + cbn [nth_error]. replace (a + Z.of_nat 0) with a by lia. exact Hb0.
    + cbn [nth_error]. cbn [length] in Hi. rewrite <- (Hbs i ltac:(lia)). f_equal. f_equal. lia.
Qed.

(* A q64 word as a read-only cell (Seg/R7.v's r7_q64_ro). *)
Lemma r7t_q64_ro : forall m A v, q64 m A v -> ro_cells rsegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v H. split; [split; [exact I | exact I] | cbn [cells_bytes]; rewrite app_nil_r; exact H].
Qed.

(* The image's bytes at an address the loader maps.  The step equation is written out so that the case split
   below is on the very term it names (a cbn in the hypothesis leaves a shape destruct does not bind). *)
Lemma r7t_img_step : forall A n, Image.image_bytes rsegs A (S n) =
  match seg_rom rsegs (wa A) with
  | Some b => match Image.image_bytes rsegs (A + 1) n with Some bs => Some (b :: bs) | None => None end
  | None => None
  end.
Proof. intros A n. reflexivity. Qed.

Lemma r7t_img_rom : forall n A bs, Image.image_bytes rsegs A n = Some bs ->
  forall i, (i < n)%nat -> seg_rom rsegs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros A bs H i Hi; [lia|].
  rewrite r7t_img_step in H.
  destruct (seg_rom rsegs (wa A)) as [b|] eqn:E1; [|discriminate H].
  destruct (Image.image_bytes rsegs (A + 1) n) as [bs'|] eqn:E2; [|discriminate H].
  injection H as <-. destruct i as [|i]; cbn [nth_error].
  - rewrite Z.add_0_r. exact E1.
  - replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia.
    apply (IH (A + 1) bs' E2 i). cbn in Hi. lia.
Qed.

(* A memory that agrees with the ROM over a mapped range holds the image's bytes there. *)
Lemma r7t_bytes_of_img : forall m A n bs, Image.image_bytes rsegs A n = Some bs ->
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> mrd rsegs m (wa (A + Z.of_nat i)) = seg_rom rsegs (wa (A + Z.of_nat i))) ->
  bytes_at rsegs m A bs.
Proof.
  intros m A n bs H HA Hn Hag.
  assert (L : length bs = n) by exact (Image.image_bytes_length rsegs n A bs H).
  split; [exact HA|]. split; [rewrite L; exact Hn|].
  intros i Hi. rewrite L in Hi. rewrite (Hag i Hi). exact (r7t_img_rom n A bs H i Hi).
Qed.

(* A point of a concrete block list L ((base, length) pairs, e.g. AF.frame_AG or AC.a_client): the block is found
   by computation over L, so the proof does not name the image's addresses (they are L's, whatever the build's).
   Goal: exists p n, In (p, n) L /\ p <= a < p + n, with the range of a in the context. *)
Ltac r7t_blk L :=
  let l := eval vm_compute in L in
  let rec go l :=
    lazymatch l with
    | (?lo, ?len) :: ?r =>
        first [ solve [ exists lo, len; split; [vm_compute; repeat (first [left; reflexivity | right]) | lia] ]
              | go r ]
    end in
  go l.

(* The catalogue (BOX_CATALOGUE, 0x9e800, 3256 bytes registered) is one registered global and lies in the image's
   RELRO range. *)
Lemma r7t_in_AG : forall a, 0x9e800 <= a < 0x9e800 + 3256 -> in_globals AF.frame_AG a.
Proof. intros a Ha. red. r7t_blk AF.frame_AG. Qed.

Lemma r7t_in_RELRO : forall a, 0x9e800 <= a < 0x9e800 + 3256 -> in_globals AF.frame_RELRO a.
Proof. intros a Ha. red. r7t_blk AF.frame_RELRO. Qed.

(* Eight catalogue bytes are addressable, so their granule's shadow byte is zero (AsanRTFacts.meta8: asking for
   eight bytes rules out the partial-granule case of shadow_ok). *)
Lemma r7t_cat_addr8 : forall mem p, (forall a, in_globals AF.frame_AG a -> addressable mem a 1) ->
  0x9e800 <= p -> p + 8 <= 0x9e800 + 3256 -> addressable mem p 8.
Proof.
  intros mem p HAG Hlo Hhi.
  split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
  intros i Hi.
  destruct (HAG (p + i) (r7t_in_AG (p + i) ltac:(lia))) as (_ & _ & _ & Hb).
  destruct (Hb 0 ltac:(lia)) as (Hap & b & Hrb & Hok).
  rewrite Z.add_0_r in Hap, Hrb, Hok. exact (conj Hap (ex_intro _ b (conj Hrb Hok))).
Qed.

Lemma r7t_cat_meta : forall mem p, (forall a, in_globals AF.frame_AG a -> addressable mem a 1) ->
  0x9e800 <= p -> p + 8 <= 0x9e800 + 3256 ->
  ro_cells rsegs mem (p / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
  intros mem p HAG Hlo Hhi.
  destruct (meta8 mem p (r7t_cat_addr8 mem p HAG Hlo Hhi)) as (R & _).
  replace (p / 8 + 2147450880) with (Z.shiftr p 3 + ASAN_K); [exact R|].
  unfold ASAN_K. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* A word built from a two-byte list, so that le2 of it is that list (A1.v's le8_of_bytes at width 2). *)
Definition r7t_w2 (bs : list byte) : word := Z_to_bv 64 (bytes_le_to_Z bs).

Lemma r7t_le2_w2 : forall bs : list byte, length bs = 2%nat -> le2 (r7t_w2 bs) = bs.
Proof.
  intros bs L. unfold le2, r7t_w2. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (bytes_le_to_Z bs)) with (bytes_le_to_Z bs mod 2 ^ 64).
  rewrite (Z_to_le_bytes_mod 2 _ 64) by lia. rewrite <- L. apply SF.Z_to_le_bytes_to_Z.
Qed.

(* A prefix of a byte list is at the same address. *)
Lemma r7t_nth_firstn : forall (l : list byte) k i, (i < k)%nat -> nth_error (firstn k l) i = nth_error l i.
Proof.
  induction l as [|x l IH]; intros k i Hi.
  - rewrite firstn_nil. reflexivity.
  - destruct k as [|k]; [lia|]. cbn [firstn]. destruct i as [|i]; [reflexivity|].
    cbn [nth_error]. apply IH. lia.
Qed.

Lemma r7t_bytes_firstn : forall m a bs k, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn k bs).
Proof.
  intros m a bs k (H0 & H1 & H). split; [exact H0|].
  split; [rewrite length_firstn; lia|].
  intros i Hi. rewrite length_firstn in Hi.
  rewrite (r7t_nth_firstn bs k i ltac:(lia)). apply H. lia.
Qed.

(* ===== Readers for the tail's run: the memory facts it asks for, on the real memory and on its normalization ===== *)

(* A byte at or above the image is in the memory when its write view is (no segment maps it). *)
Lemma r7t_wview_hi : forall (m : word -> option byte) (x : word), 6283264 <= bv_unsigned x ->
  wview rsegs m x <> None -> exists b, mrd rsegs m x = Some b.
Proof.
  intros m x Hx Hw. unfold mrd. destruct (m x) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. apply Hw. unfold wview. rewrite E.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:Es; [|reflexivity].
  destruct (ro_find_below rsegs 6283264 (bv_unsigned x) 1 s ro_rsegs_low Es ltac:(lia)) as [L|L];
    [lia | discriminate L].
Qed.

(* A spill read off register 9 is at the spill base A of the cut (Seg/R7.v's r7_spill_at). *)
Lemma r7t_spill_at : forall regs mem A off v, rg regs 9 A -> 0 <= A < 2 ^ 47 -> 0 <= off <= 2 ^ 47 ->
  spill regs mem off v -> q64 mem (A + off) v.
Proof.
  intros regs mem A off v Hr HA Hoff (A1 & Hr1 & Hq).
  pose proof (rg_eq64 regs 9 A1 A Hr1 Hr) as Hm.
  pose proof Hq as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
  assert (E : A1 = A).
  { revert Hm Hb HA Hoff. change (2 ^ 64) with 18446744073709551616. change (2 ^ 47) with 140737488355328.
    intros Hm Hb HA Hoff. Z.div_mod_to_equations. lia. }
  subst A1. exact Hq.
Qed.

(* bytes_at survives a memory change that keeps each byte of its range (Seg/R7.v's r7_bkeep). *)
Lemma r7t_bkeep : forall (mem mem' : word -> option byte) a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte rsegs mem' x = mbyte rsegs mem x) ->
  bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs.
Proof.
  intros mem mem' a bs HK (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi).
  change (mbyte rsegs mem' (a + Z.of_nat i) = mbyte rsegs mem (a + Z.of_nat i)).
  apply HK. lia.
Qed.

(* Every registered global of frame_AG lies in the image, below GT. *)
Definition r7t_AGb : bool :=
  forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 6283264)) AF.frame_AG.

Lemma r7t_AG_lt : forall a, in_globals AF.frame_AG a -> 0 <= a < 6283264.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (HB : r7t_AGb = true) by (vm_compute; reflexivity).
  unfold r7t_AGb in HB. rewrite forallb_forall in HB.
  specialize (HB (lo, len) Hin). cbn [fst snd] in HB.
  apply andb_true_iff in HB as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* Read-only cells cross to the normalized memory (MemNorm.bytes_at_normalize). *)
Lemma r7t_ro_norm : forall m A cs, ro_agree rsegs m -> ro_cells rsegs m A cs -> ro_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros m A cs Hro (Hwf & Hb). split; [exact Hwf | exact (bytes_at_normalize rsegs m A _ Hro Hb)].
Qed.

(* The four bytes of the zero word. *)
Lemma r7t_le4_0 : le4 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 4.
Proof.
  unfold le4. cbn [Z_to_le_bytes repeat].
  repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]). reflexivity.
Qed.

(* A sub-range of a byte run (R21.v's a_sub). *)
Lemma r7t_sub : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(* Eight bytes from k as four halfwords. *)
Lemma r7t_take8 : forall k (l : list byte),
  firstn 8 (skipn k l) = firstn 2 (skipn k l) ++ firstn 2 (skipn (k + 2) l) ++ firstn 2 (skipn (k + 4) l) ++
    firstn 2 (skipn (k + 6) l).
Proof.
  induction k as [|k IH]; intros l.
  - do 8 (destruct l as [|? l]; [reflexivity|]). reflexivity.
  - destruct l as [|x l]; [reflexivity|]. exact (IH l).
Qed.

(* The first 37 bytes of the 38-byte identity record, cut as the tail's loads read them. *)
Lemma r7t_rid_split : forall l : list byte, length l = 38%nat ->
  firstn 37 l = firstn 2 l ++ [nth 2 l (Z_to_bv 8 0)] ++ firstn 19 (skipn 3 l) ++ firstn 2 (skipn 22 l) ++
    firstn 2 (skipn 24 l) ++ firstn 2 (skipn 26 l) ++ firstn 8 (skipn 28 l) ++ [nth 36 l (Z_to_bv 8 0)].
Proof.
  intros l L. do 38 (destruct l as [|? l]; [cbn in L; discriminate L|]). reflexivity.
Qed.

(* The identity record's cells and the catalogue row's four halfwords, with the record's halfwords named by the
   row's (the model's equalities). *)
Lemma r7t_idrow_cells : forall m a row (l rb : list byte), length l = 38%nat -> length rb = 296%nat ->
  bytes_at rsegs m a l -> bytes_at rsegs m row rb ->
  firstn 2 l = firstn 2 (skipn 266 rb) -> firstn 2 (skipn 22 l) = firstn 2 (skipn 268 rb) ->
  firstn 2 (skipn 24 l) = firstn 2 (skipn 270 rb) -> firstn 2 (skipn 26 l) = firstn 2 (skipn 272 rb) ->
  ro_cells rsegs m a [C2 (r7t_w2 (firstn 2 (skipn 266 rb))); C1 (nth 2 l (Z_to_bv 8 0));
    CB 19 (firstn 19 (skipn 3 l)); C2 (r7t_w2 (firstn 2 (skipn 268 rb))); C2 (r7t_w2 (firstn 2 (skipn 270 rb)));
    C2 (r7t_w2 (firstn 2 (skipn 272 rb))); CB 8 (firstn 8 (skipn 28 l)); C1 (nth 36 l (Z_to_bv 8 0))] /\
  ro_cells rsegs m (row + 266) [C2 (r7t_w2 (firstn 2 (skipn 266 rb))); C2 (r7t_w2 (firstn 2 (skipn 268 rb)));
    C2 (r7t_w2 (firstn 2 (skipn 270 rb))); C2 (r7t_w2 (firstn 2 (skipn 272 rb)))].
Proof.
  intros m a row l rb Ll Lrb Hl Hrb E0 E1 E2 E3.
  assert (L2 : forall k, (k + 2 <= 296)%nat -> length (firstn 2 (skipn k rb)) = 2%nat).
  { intros k Hk. rewrite length_firstn, length_skipn, Lrb. lia. }
  split.
  - split.
    + cbn [cells_wf cell_wf]. rewrite !length_firstn, !length_skipn, Ll. repeat split; try reflexivity.
    + cbn [cells_bytes cbytes].
      rewrite !r7t_le2_w2 by (apply L2; lia).
      rewrite <- E0, <- E1, <- E2, <- E3, app_nil_r.
      rewrite <- (r7t_rid_split l Ll). apply r7t_bytes_firstn. exact Hl.
  - split.
    + cbn [cells_wf cell_wf]. repeat split.
    + cbn [cells_bytes cbytes].
      rewrite !r7t_le2_w2 by (apply L2; lia). rewrite app_nil_r.
      pose proof (r7t_sub m row rb 266 8 Hrb ltac:(lia)) as H.
      rewrite r7t_take8 in H. exact H.
Qed.

(* The row's word at + 56 is zero. *)
Lemma r7t_c56 : forall m row (rb : list byte), length rb = 296%nat -> bytes_at rsegs m row rb ->
  firstn 4 (skipn 56 rb) = repeat (Z_to_bv 8 0) 4 -> ro_cells rsegs m (row + 56) [C4 (Z_to_bv 64 0)].
Proof.
  intros m row rb L H E. split; [split; [exact I | exact I]|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r, r7t_le4_0, <- E.
  exact (r7t_sub m row rb 56 4 H ltac:(lia)).
Qed.

(* A run of shadow bytes, present in m, is a writable cell of the normalized memory. *)
Lemma r7t_sh_rw : forall m a (bs : list byte) n, ro_agree rsegs m -> bytes_at rsegs m a bs -> length bs = n ->
  shadow_rw m -> (forall i, 0 <= i < Z.of_nat n -> in_shadow (a + i)) ->
  rw_cells rsegs (normalize rsegs m) a [CB n bs].
Proof.
  intros m a bs n Hro Hb L HSW Hin.
  apply (rel_rw_norm m _ a _ (mem_rel_normalize rsegs m Hro)).
  - intros i Hi. cbn [cells_size csize] in Hi. apply ro_addr_false_shadow. apply Hin. lia.
  - pose proof (bytes_at_bound rsegs m a bs Hb) as Hbd. rewrite L in Hbd.
    split.
    + split; [split; [exact L | exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
    + split; [lia|]. split; [cbn [cells_size csize]; lia|].
      intros i Hi. cbn [cells_size csize] in Hi. exact (proj1 (HSW (a + i) (Hin i ltac:(lia)))).
Qed.

(* The frame's shadow byte at offset k is the shadow of the frame byte at offset 8 k (R21.v's r21_shadow_off). *)
Lemma r7t_shadow_off : forall fr k, 0 <= k -> shadow_addr (fr + k * 8) = Sfr fr + k.
Proof. intros fr k Hk. unfold Sfr, shadow_addr. rewrite Z.div_add by lia. lia. Qed.

(* The frame's FRAME_SHADOW shadow bytes are shadow memory. *)
Lemma r7t_fsh_in : forall fr, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr Happ x Hx. replace x with (shadow_addr (fr + (x - Sfr fr) * 8)) by (rewrite r7t_shadow_off by lia; lia).
  apply shadow_of_app. apply Happ. lia.
Qed.

(* Every side-stack metadata cell lies in [FS, FS + 36864) (R21.v's r21_fs_meta_range). *)
Lemma r7t_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* A readable and writable range off the one interval a run writes stays readable and writable after it. *)
Lemma r7t_rw_keep : forall (m m' : word -> option byte) lo hi X cs,
  LibFr.munch [(lo, hi)] m m' -> LibFr.wmono rsegs m m' ->
  X + Z.of_nat (cells_size cs) <= lo \/ hi <= X ->
  rw_cells rsegs m X cs -> rw_cells rsegs m' X cs.
Proof.
  intros m m' lo hi X cs MU WM Hd H.
  apply (LibFr.rw_cells_transport rsegs [(lo, hi)] m m' X cs H MU WM).
  cbn [LibFr.disjoint_from]. split; [exact Hd | exact Logic.I].
Qed.

(* A q64 word off the one interval a run writes is kept by it. *)
Lemma r7t_q64_keep : forall (m m' : word -> option byte) lo hi a v,
  LibFr.munch [(lo, hi)] m m' -> a + 8 <= lo \/ hi <= a -> q64 m a v -> q64 m' a v.
Proof.
  intros m m' lo hi a v MU Hd H. unfold q64 in *.
  apply (LibFr.bytes_at_transport rsegs [(lo, hi)] m m' a _ H MU).
  cbn [LibFr.disjoint_from]. rewrite length_le8. split; [lia | exact Logic.I].
Qed.

(* A frame range and a range of the frame's own shadow bytes are apart: the frame is application memory, its
   shadow is shadow memory, and each lies in one of the two contiguous arms of its map. *)
Lemma r7t_fr_sh_apart : forall fr, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  forall k n lo hi, 0 <= k -> 0 <= n -> k + n <= FRAME_BYTES -> 0 <= lo -> lo < hi -> hi <= FRAME_SHADOW ->
  fr + k + n <= Sfr fr + lo \/ Sfr fr + hi <= fr + k.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr Happ k n lo hi Hk Hn Hkn Hlo Hlh Hhi.
  pose proof (Happ fr ltac:(lia)) as P0. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as P1.
  pose proof (r7t_fsh_in fr Happ (Sfr fr + lo) ltac:(lia)) as Q0.
  pose proof (r7t_fsh_in fr Happ (Sfr fr + (hi - 1)) ltac:(lia)) as Q1.
  unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in P0, P1, Q0, Q1.
  lia.
Qed.

(* A byte off the one interval a run writes is kept by it. *)
Lemma r7t_mb_out : forall (m m' : word -> option byte) lo hi x, LibFr.munch [(lo, hi)] m m' ->
  0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> mbyte rsegs m' x = mbyte rsegs m x.
Proof.
  intros m m' lo hi x MU Hx Hn. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
  rewrite MState.unsigned_lit by exact Hx. cbn [LibFr.outside ULFr.outside]. split; [exact Hn | exact I].
Qed.

(* The shadow byte of a byte at least 8 bytes below fr + 8 lo, or at or above fr + 8 hi, is off the frame's shadow
   bytes S(fr) + lo .. S(fr) + hi - 1. *)
Lemma r7t_sh_out : forall fr x lo hi, x + 8 <= fr + 8 * lo \/ fr + 8 * hi <= x ->
  ~ (Sfr fr + lo <= shadow_addr x < Sfr fr + hi).
Proof. intros fr x lo hi H. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* PRO (push 13B, 14D; v1.9 appends [A + 32] = fr + 2880) moves to a new register file and memory when each of its
   parts does: the thirteen spills (all in the save area, offsets 32 .. 272), our[]'s 6 bytes addressable, and the
   input block's bytes and addressability. *)
Lemma r7t_pro_mk : forall g fr regs m regs' m',
  (forall off v, 0 <= off <= 408 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fr + 2624) 6 -> addressable m' (fr + 2624) 6) ->
  (bytes_at rsegs m (g_p g) (g_in g) -> bytes_at rsegs m' (g_p g) (g_in g)) ->
  (In (g_p g, g_n g) (g_H g) -> addressable m (g_p g) (g_n g) -> addressable m' (g_p g) (g_n g)) ->
  PRO g fr regs m -> PRO g fr regs' m'.
Proof.
  intros g fr regs m regs' m' SP AD BY AI
    (S40 & S120 & S136 & S160 & S168 & S176 & S208 & S248 & HA & HB & HI & S184 & S256 & S264 & S272 & S32).
  unfold PRO.
  split; [exact (SP 40 _ ltac:(lia) S40)|].
  split; [exact (SP 120 _ ltac:(lia) S120)|].
  split; [exact (SP 136 _ ltac:(lia) S136)|].
  split; [exact (SP 160 _ ltac:(lia) S160)|].
  split; [exact (SP 168 _ ltac:(lia) S168)|].
  split; [exact (SP 176 _ ltac:(lia) S176)|].
  split; [exact (SP 208 _ ltac:(lia) S208)|].
  split; [exact (SP 248 _ ltac:(lia) S248)|].
  split; [exact (AD HA)|].
  split; [exact (BY HB)|].
  split; [intros Hn; destruct (HI Hn) as (Hin & Had); split; [exact Hin | exact (AI Hin Had)]|].
  split; [exact (SP 184 _ ltac:(lia) S184)|].
  split; [exact (SP 256 _ ltac:(lia) S256)|].
  split; [exact (SP 264 _ ltac:(lia) S264)|].
  split; [exact (SP 272 _ ltac:(lia) S272)|].
  exact (SP 32 _ ltac:(lia) S32).
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Local Notation API := (APIf rc).

(* The heap law a_laws_blocks, taken apart once, here: a Theorem Labs lane's generations add conjuncts at every level, so a
   position of the law is read only in this lemma. *)
Lemma r7t_blocks : forall H mem md p n, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_img a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin. destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [_ _ X _ Y].
  split; [exact X|].
  intros a Ha. destruct (Y a Ha) as (Y1 & _ & Y3 & _ & Y5). split; [exact Y1 | split; [exact Y3 | exact Y5]].
Qed.

(* The address bounds the tail's run asks for, out of FRA.  The spill base A lies in the entry-anchored stack
   window, whose low end is at or above HIGHMEM_BEG (a_laws_stack_high), so A is about 2^44; the frame's
   FRAME_SHADOW shadow bytes start at fr / 8 + ASAN_K with fr <= A, hence far below A. *)
Lemma r7t_bounds : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md ->
  forall A, rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  0 <= A /\ A + 416 <= 2 ^ 47 /\ AC.GT <= fr /\ fr + FRAME_BYTES <= A /\
  2147450880 <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= 2 ^ 47 /\ Sfr fr + FRAME_SHADOW <= A.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA A Hr9 HAr.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT API) as ALAWS.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  pose proof HFRA as HF0.
  destruct HF0 as (A' & sp & s5v & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9f & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ ALAWS (hb ++ g_H g) mem md HAH).
  assert (Hsp0 : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; apply u64_range).
  assert (HSb : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; split; [apply (proj1 Hwin) | apply (proj1 (proj2 Hwin))]).
  assert (EA : A' = A).
  { unfold rg in Hr9, Hr9f. rewrite Hr9f in Hr9.
    apply (f_equal (@bv_unsigned 64)) in Hr9. rewrite !MState.unsigned_lit in Hr9 by lia. exact Hr9. }
  subst A'.
  assert (HSS : AF.SLOT_STACK = 0x100000) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HSfr : Sfr fr = fr / 8 + 0x7fff8000) by reflexivity.
  change (2 ^ 47) with 140737488355328.
  rewrite HSfr.
  assert (Hd1 : 0 <= fr / 8) by (apply Z.div_pos; lia).
  assert (Hd2 : 8 * (fr / 8) <= fr) by (apply Z.mul_div_le; lia).
  repeat split; lia.
Qed.

(* A byte of a live block of the cut (PRO's input block among them) is application memory off the image, below
   stklo, and not a frame byte: a_laws_blocks puts the block below stklo and off the side stack, while a frame byte
   is at or above stklo (FRA's real arm) or a side-stack byte (its side arm). *)
Lemma r7t_blk_not_fr : forall g fr hb regs mem md p n x,
  FRA B APIf ra g fr hb regs mem md -> In (p, n) (hb ++ g_H g) -> p <= x < p + n ->
  app_mem x /\ ~ AC.a_in_img x /\ x < AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md /\ ~ (fr <= x < fr + FRAME_BYTES).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md p n x HFRA Hin Hx.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & _).
  destruct (r7t_blocks _ mem md p n HAH Hin) as (Hend & Hall).
  destruct (Hall x Hx) as (Happ & Hnimg & Hnfs).
  split; [exact Happ|]. split; [exact Hnimg|]. split; [lia|].
  intros Hf. destruct Hloc as [(_ & _ & Hreal)|(_ & _ & Hfs & _)].
  - pose proof (Hreal x Hf). lia.
  - exact (Hnfs (Hfs x Hf)).
Qed.

(* FRA and ENT across a write of a range of the frame's own FRAME_SHADOW shadow bytes (R21.v's r21_fr_shadow): FRA by
   Tac_slot.sl_fr_meta, ENT by Tac_slot.ent_store. AH, the runtime-owned bytes, stklo and stkhi come from
   a_laws_store on the real-stack arm (the written bytes are shadows of real-stack bytes) and from a_fs_ok_store_AH
   on the side arm, where the frame record FSREC places the frame inside its FakeStack FS. *)
Lemma r7t_fr_shadow : forall g fr hb regs regs' mem mem' md (lo hi : Z),
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  0 <= lo -> lo <= hi -> hi <= FRAME_SHADOW ->
  Frame.munch [(Sfr fr + lo, Sfr fr + hi)] mem mem' ->
  Frame.wmono rsegs mem mem' ->
  (forall q, Sfr fr + lo <= q < Sfr fr + hi -> exists b, mrd rsegs mem' (wa q) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md /\ ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md lo hi HFRA HENT Hlo Hlh Hhi MU WM HPres E2 E3 E4 E8 E9 E19 E26.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  assert (HGTv : AC.GT = 6283264) by reflexivity.
  assert (Hfr0 : 0 <= fr) by lia.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS (hb ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HSfrlo : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 Hfr0 ltac:(lia)); lia).
  assert (HAlo : HIGHMEM_BEG <= A) by (unfold AF.SLOT_STACK in Hstklo; lia).
  assert (HAhi : A + 312 <= 2 ^ 64).
  { unfold q64 in Hspill. apply bytes_at_bound in Hspill. rewrite length_le8 in Hspill. lia. }
  (* every written address is the shadow of a frame byte, and so in the shadow map *)
  assert (Hinsh : forall x, Sfr fr + lo <= x < Sfr fr + hi -> in_shadow x).
  { intros x Hx. apply (r7t_fsh_in fr Happ). lia. }
  assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x).
  { intros x Hx Hwx. exact (WM (Z_to_bv 64 x) Hwx). }
  assert (Hout : forall x, 0 <= x < 2 ^ 64 -> ~ (Sfr fr + lo <= x < Sfr fr + hi) ->
                   mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { intros x Hx Hn. apply MU. rewrite MState.unsigned_lit by exact Hx.
    cbn [Frame.outside]. split; [exact Hn | exact I]. }
  assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
            exists b, mbyte rsegs mem' q = Some b).
  { intros q Hq Hb.
    destruct (Z_lt_le_dec q (Sfr fr + lo)) as [H1|H1].
    - unfold mbyte. rewrite (Hout q Hq ltac:(lia)). exact Hb.
    - destruct (Z_lt_le_dec q (Sfr fr + hi)) as [H2|H2].
      + exact (HPres q ltac:(lia)).
      + unfold mbyte. rewrite (Hout q Hq ltac:(lia)). exact Hb. }
  (* AH, the runtime-owned bytes, stklo and stkhi after the write, per frame-location arm *)
  assert (AHSTK : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
                  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a <->
                             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a) /\
                  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                    = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                    = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { destruct Hloc as [(Hs50 & Hspfr & Hreal)|(Hs5fr & HfsbS & Hfs & HREC)].
    - (* real arm: the written shadow bytes are shadows of real-stack bytes (a_store_ok) *)
      assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
                ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
      { intros x Hx Hnok.
        destruct (Z_lt_le_dec x (Sfr fr + lo)) as [H1|H1]; [exact (Hout x Hx ltac:(lia))|].
        destruct (Z_lt_le_dec x (Sfr fr + hi)) as [H2|H2]; [|exact (Hout x Hx ltac:(lia))].
        exfalso. apply Hnok. right. right. right. exists (fr + (x - Sfr fr) * 8).
        split; [symmetry; rewrite r7t_shadow_off by lia; lia|]. right. left.
        specialize (Hreal (fr + (x - Sfr fr) * 8) ltac:(lia)). lia. }
      exact (AC.a_laws_store _ _ _ _ _ ALAWS (hb ++ g_H g) mem mem' md HAH Hmc Hwrit).
    - (* side arm: the frame is slot j of class 6 of the FakeStack FS (FSREC), so the written shadow bytes are
         shadows of FakeStack bytes (a_fs_ok_store_AH) *)
      destruct HREC as (FS & j & HFSw & HFSr & Hj & Hfrj & _ & _).
      unfold SMC.fs_frame, SMC.fs_B in Hfrj. unfold SMC.fs_M in Hj.
      change (Z.of_nat 6 * 2 ^ 20) with 6291456 in Hfrj. change (64 * 2 ^ Z.of_nat 6) with 4096 in Hfrj.
      change (2 ^ (14 - Z.of_nat 6)) with 256 in Hj.
      assert (Happfr : app_mem fr) by (apply Happ; lia).
      apply (a_fs_ok_store_AH AC.ASYMS _ _ _ _ [(Sfr fr + lo, Sfr fr + hi)] (hb ++ g_H g) mem mem' md FS
               ALAWS HAH HFSw HFSr).
      + unfold AC.FS_SIZE. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happfr. lia.
      + exact MU.
      + exact Hwrit.
      + exact Hpres.
      + intros q Hq. pose proof (r7t_fs_meta_range _ _ Hq) as Hqr.
        cbn [Frame.outside]. split; [|exact I]. intros Hqt.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happfr.
        unfold Sfr, shadow_addr, ASAN_K in Hqt. lia.
      + intros x Hx Hnok Hnfs Hnsh.
        destruct (Z_lt_le_dec x (Sfr fr + lo)) as [H1|H1]; [exact (Hout x Hx ltac:(lia))|].
        destruct (Z_lt_le_dec x (Sfr fr + hi)) as [H2|H2]; [|exact (Hout x Hx ltac:(lia))].
        exfalso. apply Hnsh. exists (fr + (x - Sfr fr) * 8).
        split; [unfold AC.FS_SIZE; lia | symmetry; rewrite r7t_shadow_off by lia; lia]. }
  destruct AHSTK as (HAH' & HOWN' & HSTK' & HSHI').
  unfold rg in Hr9.
  assert (HA9 : forall A0, getr regs 9 = Z_to_bv 64 A0 -> A0 mod 2 ^ 64 = A).
  { intros A0 HA0.
    pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) HA0)) as E0.
    rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in E0.
    rewrite (Z.mod_small A (2 ^ 64)) in E0 by (unfold HIGHMEM_BEG in HAlo; lia).
    symmetry; exact E0. }
  assert (HshiHi : Sfr fr + hi <= HIGHMEM_BEG \/ lo = hi).
  { destruct (Z.eq_dec lo hi) as [E|Hne]; [right; exact E|left].
    pose proof (Hinsh (Sfr fr + (hi - 1)) ltac:(lia)) as IS.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in IS |- *. lia. }
  (* the new FRAME_SHADOW shadow bytes *)
  destruct Hsh as (sh0 & Hb0 & HL0).
  pose proof (bytes_at_bound rsegs mem (Sfr fr) sh0 Hb0) as Hb0r. rewrite HL0 in Hb0r.
  assert (Hsh' : exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
  { apply (r7t_bytes_ex mem' (Z.to_nat FRAME_SHADOW) (Sfr fr)); [lia | lia |].
    intros x Hx.
    destruct (Z_lt_le_dec x (Sfr fr + lo)) as [H1|H1].
    - pose proof (proj2 (proj2 Hb0) (Z.to_nat (x - Sfr fr)) ltac:(lia)) as Hb0k.
      replace (Sfr fr + Z.of_nat (Z.to_nat (x - Sfr fr))) with x in Hb0k by lia.
      destruct (nth_error sh0 (Z.to_nat (x - Sfr fr))) as [b|] eqn:Ek; [|exfalso; apply nth_error_None in Ek; lia].
      exists b. unfold mbyte. rewrite (Hout x ltac:(lia) ltac:(lia)). exact Hb0k.
    - destruct (Z_lt_le_dec x (Sfr fr + hi)) as [H2|H2].
      + exact (HPres x ltac:(lia)).
      + pose proof (proj2 (proj2 Hb0) (Z.to_nat (x - Sfr fr)) ltac:(lia)) as Hb0k.
        replace (Sfr fr + Z.of_nat (Z.to_nat (x - Sfr fr))) with x in Hb0k by lia.
        destruct (nth_error sh0 (Z.to_nat (x - Sfr fr))) as [b|] eqn:Ek; [|exfalso; apply nth_error_None in Ek; lia].
        exists b. unfold mbyte. rewrite (Hout x ltac:(lia) ltac:(lia)). exact Hb0k. }
  assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
  { intros a Ha. apply (addr1_munch _ mem mem' a MU); [|exact (HAG a Ha)].
    pose proof (r7t_AG_lt a Ha) as Hal. cbn [Frame.outside]. split; [|exact I].
    unfold Sfr, shadow_addr. lia. }
  split.
  { apply (sl_fr_meta B APIf ra empty FF g fr hb regs regs' mem mem'
             md [(Sfr fr + lo, Sfr fr + hi)] HFRA MU WM); try assumption.
    - apply (ro_agree_munch [(Sfr fr + lo, Sfr fr + hi)] mem mem' Hro MU). intros x Hx. apply ro_addr_false_w.
      cbn [LibFr.outside ULFr.outside] in Hx. unfold ASAN_K in HSfrlo. lia.
    - unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
        RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI,
        RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN. cbn [disjoint_from]. unfold ASAN_K in HSfrlo.
      repeat split; (lia || exact I).
    - intros x Hx Hnb Hnsh. cbn [Frame.outside]. split; [|exact I]. lia.
    - intros A0 HA0 HA0r x Hx. cbn [Frame.outside]. split; [|exact I].
      pose proof (HA9 A0 HA0) as HA0e. unfold HIGHMEM_BEG in HAlo.
      destruct HshiHi as [Hhx|Hhx]; unfold HIGHMEM_BEG in *; revert Hx HA0e; Z.div_mod_to_equations; lia.
    - intros x Hx. cbn [Frame.outside]. split; [|exact I].
      destruct HshiHi as [Hhx|Hhx]; unfold HIGHMEM_BEG in *; lia.
    - intros A0 HA0 HA0r x Hx. cbn [Frame.outside]. split; [|exact I].
      pose proof (HA9 A0 HA0) as HA0e. unfold HIGHMEM_BEG in HAlo.
      destruct HshiHi as [Hhx|Hhx]; unfold HIGHMEM_BEG in *; revert Hx HA0e; Z.div_mod_to_equations; lia.
    - intros x Hx. left. cbn [Frame.outside]. split; [|exact I].
      unfold AF.SLOT_STACK in *. unfold HIGHMEM_BEG in *.
      destruct HshiHi as [Hhx|Hhx]; lia. }
  assert (HWcase : forall x, 0 <= x < 2 ^ 64 -> Frame.outside [(Sfr fr + lo, Sfr fr + hi)] x \/
    (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
  { intros x Hx.
    destruct (Z_le_gt_dec (Sfr fr + lo) x) as [H1|H1];
      [ destruct (Z_lt_ge_dec x (Sfr fr + hi)) as [H2|H2];
        [ right; right; right; lia
        | left; cbn [Frame.outside]; split; [lia | exact I] ]
      | left; cbn [Frame.outside]; split; [lia | exact I] ]. }
  eapply ent_store;
    [ exact HENT | exact HFRA | exact MU | exact HWcase | exact HSTK' | exact HSHI'
    | intros a _ Hw; exact (proj2 (HOWN' a) Hw) ].
Qed.

(* n_6 = 0, b = 6: the tail runs 0x815ec -> 0x81b10 (r7_tail_evt) on the normalized memory, since the shadow fill
   asks for mem_inv and the cut carries ro_agree only (MemNorm.evt_normalize brings the run back); its premises are
   read off the cut (spills, identity record, frame-shadow pointer), FRA (the frame shadow, the registered globals,
   the RELRO image of the catalogue row) and RT (shadow_rw, asan_cells). After the run FRA and ENT move by
   r7t_fr_shadow (the run writes only frame-shadow bytes) and by sl_fra_move / ent_mat across the materialization,
   OURb by munch, and the P2 cut Inv_A81b10 closes the segment. Its push 7 conjunct: s11 = fr + 2688 is the cut's
   spill [A + 144] (0x81994 `ld s11,144(s1)`), the cell [A + 192] = fr + 2768 is the cut's spill made writable by
   FRA's stack window, and the two frame records are the cut's; all three are off the written frame-shadow bytes
   (munch) and stay writable (wmono). Its push 9 conjunct: the words [A + 280] = fr + 3040 and [A + 240] = fr + 3056
   are the cut's spills, and the 1-byte code cell at fr + 3040 and the 32-byte scratch at fr + 3056 are the cut's;
   all four are off the written frame-shadow bytes too. Its push 11A conjunct CUR g (c0 (g_in g)): the entry's
   CUR g 7 gives 7 <= g_n g, so c0 (g_in g) = 7, and the run keeps s6 / s9. Its push 12A conjunct [A + 144] and
   its push 13B / 14D conjunct PRO: the run keeps s1 and writes no byte of the save area [A, A + 416) (above the
   frame's shadow, r7t_bounds), so the thirteen spills are the entry's; our[]'s shadow bytes are S(fr) + 328 ..,
   past the written S(fr) + 68 .. 290; the input block is a live block of the cut (PRO's guard holds,
   7 <= g_n g), so its bytes are application memory and its shadow bytes are not the frame's (r7t_blk_not_fr,
   r7t_sh_out). Its 0x81ac0 cut, and so push 14A's bound Q + 187 <= Sfr fr + 328 there, is not reached on this
   arm; Inv_A81b10 has no Q bound. *)
Lemma r7_tail_run : Hcut B APIf ra (Inv_A81ac0 B APIf ra) -> Hcut B APIf ra (Inv_A81b10 B APIf ra) ->
  forall g c, Inv_A815ec_at B APIf ra g 6 c -> rnb g 6 = 0 -> SR (ms_segs B) c (Post B APIf ra g).
Proof.
  intros _ Hab g c HInv Hz.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof FF as (SEGS & _).
  destruct HInv as (regs & mem & md & fr & A & Ec & HFRA & HENT & Hgn & Hb6 & Hnb0 & Hsz & HA & Hr9 & Hr24 & Ha0 &
    Hm64 & H128 & HID & HFG & _ & Hr23 & Hour & Houta & Hcur & H112 & HPRO & H104 & H96 & H144 & H192 & HIDB &
    HJNK & H280 & H240 & HJY & HSCR & H152 & Hr21 & HA2176 & _).
  subst c.
  destruct (r7t_bounds g fr [] regs mem md HFRA A Hr9 HA)
    as (HA0 & HA47 & HGT & HfrA & HS3lo & HS347 & HS3A).
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (_ & Happ).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (Af & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9f & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HGTv : AC.GT = 6283264) by reflexivity.
  assert (Hsp0 : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; apply u64_range).
  assert (HSb : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; split; [apply (proj1 Hwin) | apply (proj1 (proj2 Hwin))]).
  assert (EA : Af = A).
  { pose proof Hr9 as X. unfold rg in X, Hr9f. rewrite Hr9f in X.
    apply (f_equal (@bv_unsigned 64)) in X. rewrite !MState.unsigned_lit in X by lia. exact X. }
  subst Af.
  (* the registers the run reads *)
  assert (Rs1 : getr regs 9 = Z_to_bv 64 A) by exact Hr9.
  assert (Ra0 : getr regs 10 = Z_to_bv 64 0) by (unfold a0v, rg in Ha0; rewrite Hz in Ha0; exact Ha0).
  assert (Rs5 : getr regs 21 = Z_to_bv 64 (fr + 2176)) by exact Hr21.
  assert (Rs10 : getr regs 26 = Z_to_bv 64 2147450880) by exact Hr26.
  assert (Rs3 : getr regs 19 = Z_to_bv 64 (Sfr fr)) by exact Hr19.
  assert (Rs7 : getr regs 23 = Z_to_bv 64 6) by exact Hr23.
  (* the model: the turn-6 identity record against the catalogue row *)
  assert (Hz6 : rt_n (g_in g) 6 = 0) by exact Hz.
  destruct (r7t_model (g_in g) Hz6) as (Hlen & H02 & H36 & M00 & M22 & M24 & M26 & M56 & Hist).
  assert (Hmr : mrow (g_in g) = CAT + CAT_ROW * istar (g_in g)) by reflexivity.
  assert (Hrow : 0x9e800 <= mrow (g_in g) /\ mrow (g_in g) + 296 <= 0x9e800 + 3256)
    by (rewrite Hmr; unfold CAT, CAT_ROW; lia).
  assert (NROW : bytes_at rsegs mem (mrow (g_in g)) (rowb (istar (g_in g)))).
  { rewrite Hmr. apply (r7t_bytes_of_img mem _ 296 _ (r7t_row_img _ Hist)); [unfold CAT, CAT_ROW; lia | unfold CAT, CAT_ROW; lia |].
    intros i Hi. unfold G_img_c in Hgimg. rewrite SEGS in Hgimg.
    exact (Hgimg (CAT + CAT_ROW * istar (g_in g) + Z.of_nat i)
             (r7t_in_RELRO (CAT + CAT_ROW * istar (g_in g) + Z.of_nat i) ltac:(unfold CAT, CAT_ROW; lia))). }
  unfold IDBr in HID.
  destruct (r7t_idrow_cells mem (fr + 2176) (mrow (g_in g)) (RID (g_in g) 6) (rowb (istar (g_in g)))
              Hlen (row_len _) HID NROW M00 M22 M24 M26) as (CI & CR).
  pose proof (r7t_c56 mem (mrow (g_in g)) (rowb (istar (g_in g))) (row_len _) NROW M56) as CR56.
  (* the row's shadow bytes *)
  assert (S266 := r7t_cat_meta mem (mrow (g_in g) + 266) HAG ltac:(lia) ltac:(lia)).
  assert (S268 := r7t_cat_meta mem (mrow (g_in g) + 268) HAG ltac:(lia) ltac:(lia)).
  assert (S270 := r7t_cat_meta mem (mrow (g_in g) + 270) HAG ltac:(lia) ltac:(lia)).
  assert (S272 := r7t_cat_meta mem (mrow (g_in g) + 272) HAG ltac:(lia) ltac:(lia)).
  assert (S56 := r7t_cat_meta mem (mrow (g_in g) + 56) HAG ltac:(lia) ltac:(lia)).
  (* the spills *)
  pose proof (r7t_spill_at regs mem A 112 _ Hr9 ltac:(lia) ltac:(lia) H112) as Q112.
  pose proof (r7t_spill_at regs mem A 128 _ Hr9 ltac:(lia) ltac:(lia) H128) as Q128.
  pose proof (r7t_spill_at regs mem A 152 _ Hr9 ltac:(lia) ltac:(lia) H152) as Q152.
  pose proof (r7t_spill_at regs mem A 144 _ Hr9 ltac:(lia) ltac:(lia) H144) as Q144.
  pose proof (r7t_spill_at regs mem A 192 _ Hr9 ltac:(lia) ltac:(lia) H192) as Q192.
  pose proof (r7t_spill_at regs mem A 280 _ Hr9 ltac:(lia) ltac:(lia) H280) as Q280.
  pose proof (r7t_spill_at regs mem A 240 _ Hr9 ltac:(lia) ltac:(lia) H240) as Q240.
  (* [A + 192] as a readable and writable cell: the spill's bytes, in FRA's stack window *)
  assert (RW192 : rw_cells rsegs mem (A + 192) [C8 (Z_to_bv 64 (fr + 2768))]).
  { split; [exact (r7t_q64_ro _ _ _ Q192)|]. cbn [cells_size csize].
    split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (proj2 (proj2 Hwin) (A + 192 + i) ltac:(lia))). }
  (* the frame shadow *)
  pose proof (AsanRTInv.RT_shadow_rw sp mem md HRT) as HSW.
  destruct Hsh as (sh & Bsh & Lsh).
  pose proof (r7t_sub mem (Sfr fr) sh 68 187 Bsh ltac:(lia)) as Bjsh.
  pose proof (r7t_sub mem (Sfr fr) sh 272 19 Bsh ltac:(lia)) as Bjfl.
  assert (Ljsh : length (firstn 187 (skipn 68 sh)) = 187%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (Ljfl : length (firstn 19 (skipn 272 sh)) = 19%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (RWsh : rw_cells rsegs (normalize rsegs mem) (Sfr fr + 68) [CB 187 (firstn 187 (skipn 68 sh))]).
  { apply (r7t_sh_rw mem _ _ _ Hro Bjsh Ljsh HSW). intros i Hi. apply (r7t_fsh_in fr Happ). lia. }
  assert (RWfl : rw_cells rsegs (normalize rsegs mem) (Sfr fr + 272) [CB 19 (firstn 19 (skipn 272 sh))]).
  { apply (r7t_sh_rw mem _ _ _ Hro Bjfl Ljfl HSW). intros i Hi. apply (r7t_fsh_in fr Happ). lia. }
  assert (HSH : forall i, 0 <= i < 187 -> in_shadow (Sfr fr + 68 + i)).
  { intros i Hi. apply (r7t_fsh_in fr Happ). lia. }
  pose proof (asan_set_shadow_f8_holds memset_holds) as SSF.
  rewrite SEGS.
  apply (sl_run_lib regs (Z_to_bv 64 0x815ec) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81b10 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26 /\ getr R 27 = Z_to_bv 64 (fr + 2688) /\
       LibFr.munch [(Sfr fr + 68, Sfr fr + 291)] mem mem' /\ LibFr.wmono rsegs mem mem')
    (Post B APIf ra g)).
  { exact Hhalt. }
  { unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    pose proof (mem_rel_normalize rsegs mem Hro) as REL.
    eapply evt_mono.
    - eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact Hro |].
      refine (r7_tail_evt SSF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                (normalize rsegs mem) A (fr + 2176) (mrow (g_in g)) (Sfr fr) _ _ _ _ _ _ _ _ _ _ _ _
                Rs1 Ra0 Rs5 Rs10 Rs3 Rs7 _ _ _ _ _ _ _ _ _ HSH
                (r7t_ro_norm _ _ _ Hro (r7t_q64_ro _ _ _ Q112)) (r7t_ro_norm _ _ _ Hro (r7t_q64_ro _ _ _ Q128))
                (r7t_ro_norm _ _ _ Hro (r7t_q64_ro _ _ _ Q144)) (r7t_ro_norm _ _ _ Hro (r7t_q64_ro _ _ _ Q152))
                (r7t_ro_norm _ _ _ Hro CI) H02 H36 (r7t_ro_norm _ _ _ Hro CR) (r7t_ro_norm _ _ _ Hro CR56)
                (r7t_ro_norm _ _ _ Hro S266) (r7t_ro_norm _ _ _ Hro S268) (r7t_ro_norm _ _ _ Hro S270)
                (r7t_ro_norm _ _ _ Hro S272) (r7t_ro_norm _ _ _ Hro S56) RWsh RWfl Ljsh Ljfl
                (rel_ac_norm mem _ REL (AsanRTInv.RT_cells sp mem md HRT)) (mem_inv_normalize rsegs mem));
        lia.
    - intros ms' (s0 & (R & m0' & -> & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K25 & K26 & K27 & MU0 & WM0 & MI0 &
                        RW0)
                  & RELs & ROS).
      destruct ms' as [regs1 fr1 pc1 svc1 rv1 fc1 m1 ro1].
      destruct RELs as (ER & EF & EPC & ESVC & ERES & EFC & EROM & RELm).
      cbn in ER, EF, EPC, ESVC, ERES, EFC, EROM, RELm, ROS. subst.
      exists R, (Z_to_bv 64 0x81b10), m1. split; [reflexivity|].
      split; [reflexivity|].
      split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|].
      split; [exact K9|]. split; [exact K19|]. split; [exact K22|]. split; [exact K25|].
      split; [exact K26|]. split; [exact K27|].
      split.
      + eapply munch_weaken; [|exact (munch_rel rsegs _ mem _ m1 _ REL RELm ROS MU0)].
        intros x Hx. cbn [LibFr.outside ULFr.outside] in Hx |- *. destruct Hx as (Hx & _).
        split; [lia | split; [lia | exact I]].
      + exact (wmono_rel rsegs mem _ m1 _ REL RELm ROS WM0). }
  intros R pc' mem' regs' md' (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K22 & K25 & K26 & K27 & MU & WM) Hreg Hmat.
  subst pc'.
  assert (E2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact K2).
  assert (E3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact K3).
  assert (E4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact K4).
  assert (E8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact K8).
  assert (E9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact K9).
  assert (E19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact K19).
  assert (E22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact K22).
  assert (E25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact K25).
  assert (E26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact K26).
  assert (E27 : getr regs' 27 = Z_to_bv 64 (fr + 2688)) by (rewrite Hreg; exact K27).
  (* the written frame-shadow bytes are present after the run: writable before (RT's shadow_rw), so after (wmono),
     and no segment maps them *)
  assert (HPres : forall q, Sfr fr + 68 <= q < Sfr fr + 291 -> exists b, mrd rsegs mem' (wa q) = Some b).
  { intros q Hq. assert (Hin : in_shadow q) by (apply (r7t_fsh_in fr Happ); lia).
    pose proof Hin as Hin'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin'.
    apply r7t_wview_hi; [rewrite Mem.wa_unsigned by lia; lia|].
    exact (WM (wa q) (proj1 (HSW q Hin))). }
  destruct (r7t_fr_shadow g fr [] regs regs' mem mem' md 68 291 HFRA HENT ltac:(lia) ltac:(lia) ltac:(lia)
              (proj1 (fr_munch_ul _ _ _) MU) WM HPres E2 E3 E4 E8 E9 E19 E26) as (HFRA1 & HENT1).
  assert (HFRA2 : FRA B APIf ra g fr [] regs' mem' md')
    by exact (sl_fra_move B APIf ra g fr [] regs' regs' mem' md md' HFRA1 eq_refl eq_refl eq_refl eq_refl eq_refl
                eq_refl eq_refl Hmat).
  assert (HENT2 : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENT1 | exact Hmat]).
  assert (Hour' : OURb g fr mem').
  { unfold OURb in *. apply (r7t_bkeep mem mem' (fr + 2624) (OUR (g_in g))); [|exact Hour].
    intros x Hx. rewrite OUR_length in Hx.
    assert (Hxa : app_mem x) by (apply Happ; cbn in Hx; lia).
    assert (Hx64 : 0 <= x < 2 ^ 64) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa; lia).
    unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by exact Hx64. cbn [LibFr.outside ULFr.outside]. split; [|exact I].
    intros Hxs. exact (AsanRTFacts.app_not_shadow x Hxa (r7t_fsh_in fr Happ x ltac:(lia))). }
  (* push 13B: PRO after the run (see the lemma's comment) *)
  assert (HPRO' : PRO g fr regs' mem').
  { pose proof Hcur as (Hc7 & _ & _).
    pose proof HPRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPI & _).
    destruct (HPI ltac:(lia)) as (Hin & _).
    apply (r7t_pro_mk g fr regs mem regs' mem'); [| | | | exact HPRO].
    - intros off v Hoff Hs. pose proof (r7t_spill_at regs mem A off v Hr9 ltac:(lia) ltac:(lia) Hs) as Q.
      exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      exact (r7t_q64_keep mem mem' (Sfr fr + 68) (Sfr fr + 291) (A + off) v MU ltac:(lia) Q).
    - intros Had. apply (addr_keep mem mem' _ _ Had). intros i Hi.
      pose proof (Happ (fr + 2624 + i) ltac:(lia)) as Hxa.
      destruct (in_shadow_range _ (shadow_of_app _ Hxa)) as (R1 & R2).
      apply (r7t_mb_out mem mem' (Sfr fr + 68) (Sfr fr + 291) _ MU); [lia|].
      apply r7t_sh_out. lia.
    - intros HB. apply (r7t_bkeep mem mem'); [|exact HB]. intros x Hx. rewrite <- g_n_len in Hx.
      destruct (r7t_blk_not_fr g fr [] regs mem md (g_p g) (g_n g) x HFRA Hin Hx) as (Hxa & _ & _ & _).
      assert (Hx64 : 0 <= x < 2 ^ 64) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa; lia).
      apply (r7t_mb_out mem mem' (Sfr fr + 68) (Sfr fr + 291) _ MU Hx64).
      intros Hxs. exact (AsanRTFacts.app_not_shadow x Hxa (r7t_fsh_in fr Happ x ltac:(lia))).
    - intros Hin' Had. apply (addr_keep mem mem' _ _ Had). intros i Hi.
      destruct (r7t_blk_not_fr g fr [] regs mem md (g_p g) (g_n g) (g_p g + i) HFRA Hin' ltac:(lia))
        as (Hxa & _ & _ & Hnf).
      destruct (in_shadow_range _ (shadow_of_app _ Hxa)) as (R1 & R2).
      apply (r7t_mb_out mem mem' (Sfr fr + 68) (Sfr fr + 291) _ MU); [lia|].
      apply r7t_sh_out. lia. }
  (* push 12A: [A + 144] = fr + 2688, in the save area, off the written frame-shadow bytes *)
  assert (S144' : spill regs' mem' 144 (fr + 2688)).
  { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
    exact (r7t_q64_keep mem mem' (Sfr fr + 68) (Sfr fr + 291) (A + 144) (fr + 2688) MU ltac:(lia) Q144). }
  rewrite <- SEGS. apply Hab.
  exists regs', mem', md', fr.
  split; [reflexivity|]. split; [exact HFRA2|]. split; [exact HENT2|].
  split; [exact Hgn|]. split; [exact Hour'|].
  (* push 11A: CUR g (c0 (g_in g)) regs'. The entry's CUR g 7 has range 7 <= g_n g, so c0 (g_in g) =
     min (g_n g) 7 = 7; the run keeps s6 / s9 (r7_tail_evt's post). *)
  split.
  { destruct Hcur as (Hc7 & Hc22 & Hc25).
    assert (E7 : c0 (g_in g) = 7) by (unfold c0; unfold g_n in Hc7; lia).
    unfold CUR, rg in *. rewrite E7.
    split; [exact Hc7|]. split; [rewrite E22; exact Hc22 | rewrite E25; exact Hc25]. }
  split; [exact HPRO'|].
  split; [exact S144'|].
  (* push 7: s11, the cell [A + 192] and the two frame records, off the written frame-shadow bytes *)
  destruct HIDB as (idb & Hidb). destruct HJNK as (junk & Hjk).
  exists A, idb, junk.
  split; [rewrite E9; exact Hr9|].
  split; [exact E27|].
  split; [exact HA|].
  split; [apply (r7t_rw_keep mem mem' _ _ _ _ MU WM); [cbn [cells_size csize]; lia | exact RW192]|].
  split.
  { apply (r7t_rw_keep mem mem' _ _ _ _ MU WM); [|exact Hidb]. cbn [cells_size csize].
    pose proof (r7t_fr_sh_apart fr Happ 2688 38 68 291 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as D.
    lia. }
  split.
  { apply (r7t_rw_keep mem mem' _ _ _ _ MU WM); [|exact Hjk]. cbn [cells_size csize].
    pose proof (r7t_fr_sh_apart fr Happ 2768 72 68 291 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as D.
    lia. }
  (* push 9: the words [A + 280] / [A + 240] and the code cell / scratch, off the written frame-shadow bytes *)
  split; [exact (r7t_q64_keep mem mem' (Sfr fr + 68) (Sfr fr + 291) (A + 280) (fr + 3040) MU ltac:(lia) Q280)|].
  split; [exact (r7t_q64_keep mem mem' (Sfr fr + 68) (Sfr fr + 291) (A + 240) (fr + 3056) MU ltac:(lia) Q240)|].
  destruct HJY as (jy & Hjy). destruct HSCR as (junk2 & Hsc).
  exists jy, junk2. split.
  - apply (r7t_rw_keep mem mem' _ _ _ _ MU WM); [|exact Hjy]. cbn [cells_size csize].
    pose proof (r7t_fr_sh_apart fr Happ 3040 1 68 291 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as D.
    lia.
  - apply (r7t_rw_keep mem mem' _ _ _ _ MU WM); [|exact Hsc]. cbn [cells_size csize].
    pose proof (r7t_fr_sh_apart fr Happ 3056 32 68 291 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as D.
    lia.
Qed.

End S.
