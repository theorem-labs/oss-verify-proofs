(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan): the PURE facts of segment B9 of reac_segconf_parse_file
   (the key line, reac_segconf.c:215-293; KEY 0x883f8 .. KREF 0x889a0). No machine state, no listing, no image:
   lemmas over SegModel's lists and over a reader.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: helper facts of segment B9, image B).
   A B9 sub-lane of the image-B G3 walk owner, 2026-10-30.
   ADAPTED from the image-A G3 walk owner's image-A file lib/A/Prog/pf_a9_f.v (commit e326ef3cdba9, an
   image-A segment lane): the same lemmas with the same proofs, a9_ renamed b9_; the module paths moved to image B (lib.B.Prog
   pf_pieces / SegPgBase / SegABase, lib.B.Rt RtSeg, the B kit copies YA0n YG0f YG0n YG0d YCbq of
   the B-kit name map). Every definition these lemmas read (pf_shb, PF_SC_LINE,
   pf_nm, pf_cur_ptr, pf_cur_ok, RtSeg.first_at, RtSeg.lc) has the same text in image B's pf_pieces.v / RtSeg.v as in
   image A's, so no proof changes. No Section hypothesis.

   What is here:
   - the bridge between the strchr interceptor's answer (RtSeg row 6, first_at / ~ In over the byte values) and
     SegModel.strchr (b9_strchr_none, b9_strchr_of_first, b9_strchr_lt): KEY's `jal strchr` 0x88400;
   - the bridge between the strcasecmp interceptor's answer (RtSeg row 10, map lc of the bytes with the NUL) and
     SegModel.strcasecmp = 0 (b9_lc_tolower, b9_strcasecmp_iff): the dispatch 0x88584 / 0x88598 / 0x885ac / 0x885c0;
   - r_key's branches once the '=' index and the four strcasecmp results are known (the b9_rkey lemmas): neither
     (0x88404 -> REF3), outside (0x88570 -> HREF), knock (0x88988 -> KREF), nokey (0x885c8 -> KREF);
   - unquote (R:78-86) on the trimmed value (b9_unq_short / b9_unq_strip / b9_unq_keep; 0x88440 .. 0x88570);
   - cur as a pointer (b9_cur_ptr_eq0, the `beqz a5` at 0x88570 on slot 0xc0), and cur_name's C string from pf_nm
     (b9_nm_str, the refusals' a3 = slot 0x40 = F + 0x20);
   - buf's 64 shadow cells under PF_SC_LINE and its addressability (b9_shb_buf, b9_buf_addr, b9_buf_hull): the checks
     B#9 (0x88414), B#10 (0x88450), B#11 (0x88488), B#13 (0x88538), B#14 (0x8855c) all read bytes of buf.
   The line account, trim and the counters are pfA_facts.v's (lib/Prog/pfA_facts.v, the unit owner's plain lane file):
   L_trim_holds, pf_cnt_refuse, pf_lctx_next, pf_next_gt, r_trim_len_le, pf_tline_nul. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(** ** Lists *)
Lemma b9_in_firstn : forall {A} n (l : list A) x, In x (firstn n l) -> In x l.
Proof.
intros A n. induction n as [|n IH]; intros l x H; [destruct H|].
destruct l as [|y l]; [destruct H|]. destruct H as [H|H]; [left; exact H | right; exact (IH l x H)].
Qed.

Lemma b9_in_skipn : forall {A} n (l : list A) x, In x (skipn n l) -> In x l.
Proof.
intros A n. induction n as [|n IH]; intros l x H; [exact H|].
destruct l as [|y l]; [destruct H|]. right. exact (IH l x H).
Qed.

(** ** strchr (RtSeg row 6 -> SegModel.strchr), on a NUL-free list and a nonzero byte *)
Lemma b9_strchr_none : forall l c, c <> 0 -> ~ In c l -> strchr l c = None.
Proof.
induction l as [|b l IH]; intros c Hc Hn; [reflexivity|]. cbn [strchr].
replace (b =? c) with false by (symmetry; apply Z.eqb_neq; intros ->; apply Hn; left; reflexivity).
destruct (b =? 0); [reflexivity|].
rewrite (IH c Hc ltac:(intros H; apply Hn; right; exact H)). reflexivity.
Qed.

Lemma b9_strchr_of_first : forall l c j, c <> 0 -> ~ In 0 l -> RtSeg.first_at l c j -> strchr l c = Some j.
Proof.
induction l as [|b l IH]; intros c j Hc Hz (Hj & Hnth & Hnot); [cbn [length] in Hj; lia|].
assert (Hb0 : b <> 0) by (intros ->; apply Hz; left; reflexivity).
cbn [strchr]. destruct j as [|j].
- cbn [nth] in Hnth. rewrite Hnth, Z.eqb_refl. reflexivity.
- cbn [nth] in Hnth. cbn [firstn] in Hnot.
  replace (b =? c) with false
    by (symmetry; apply Z.eqb_neq; intros ->; apply Hnot; left; reflexivity).
  replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb0).
  rewrite (IH c j Hc ltac:(intros H; apply Hz; right; exact H)).
  + reflexivity.
  + split; [cbn [length] in Hj; lia|]. split; [exact Hnth|].
    intros H. apply Hnot. right. exact H.
Qed.

Lemma b9_strchr_lt : forall l c i, strchr l c = Some i -> (i < length l)%nat /\ nth i l 0 = c.
Proof.
induction l as [|b l IH]; intros c i H; cbn [strchr] in H; [discriminate|].
destruct (Z.eqb_spec b c) as [E1|E1].
- injection H as <-. cbn [length nth]. split; [lia | exact E1].
- destruct (b =? 0); [discriminate|].
  destruct (strchr l c) as [j|] eqn:E2; cbn [option_map] in H; [|discriminate].
  injection H as <-. destruct (IH c j E2) as [H1 H2]. cbn [length nth]. split; [lia | exact H2].
Qed.

(** ** strcasecmp (RtSeg row 10 -> SegModel.strcasecmp) *)
(* sanitizer_common's ToLower and musl's tolower agree on every byte: on 'A'..'Z' the or with 32 is an add *)
Lemma b9_lc_tolower : forall c : Z, RtSeg.lc c = tolower c.
Proof.
intros c. unfold RtSeg.lc, tolower.
destruct ((65 <=? c) && (c <=? 90)) eqn:E; [|reflexivity].
apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
assert (H : c = 65 \/ c = 66 \/ c = 67 \/ c = 68 \/ c = 69 \/ c = 70 \/ c = 71 \/ c = 72 \/ c = 73 \/
            c = 74 \/ c = 75 \/ c = 76 \/ c = 77 \/ c = 78 \/ c = 79 \/ c = 80 \/ c = 81 \/ c = 82 \/
            c = 83 \/ c = 84 \/ c = 85 \/ c = 86 \/ c = 87 \/ c = 88 \/ c = 89 \/ c = 90) by lia.
repeat (destruct H as [H|H]); subst c; reflexivity.
Qed.

Lemma b9_map_lc : forall l, map RtSeg.lc l = map tolower l.
Proof.
induction l as [|x l IH]; [reflexivity|]. cbn [map]. rewrite b9_lc_tolower, IH. reflexivity.
Qed.

Lemma b9_tolower_0 : tolower 0 = 0.
Proof. reflexivity. Qed.

Lemma b9_tolower_nz : forall a, a <> 0 -> tolower a <> 0.
Proof.
intros a Ha. unfold tolower. destruct ((65 <=? a) && (a <=? 90)); [|exact Ha].
intros H. apply Z.lor_eq_0_iff in H as [_ H]. discriminate H.
Qed.

Lemma b9_strcasecmp_map : forall l w, ~ In 0 l -> ~ In 0 w ->
  (map tolower l = map tolower w <-> strcasecmp l w = 0).
Proof.
induction l as [|a l IH]; intros w Hl Hw.
- destruct w as [|b w]; cbn [map strcasecmp hd0].
  + rewrite b9_tolower_0. split; intros _; reflexivity.
  + assert (Hb : b <> 0) by (intros E; apply Hw; left; exact E).
    pose proof (b9_tolower_nz b Hb) as Pb. rewrite b9_tolower_0.
    split; [intros H; discriminate H | intros H; exfalso; lia].
- assert (Ha : a <> 0) by (intros E; apply Hl; left; exact E).
  destruct w as [|b w]; cbn [map strcasecmp hd0].
  + pose proof (b9_tolower_nz a Ha) as Pa. rewrite b9_tolower_0.
    split; [intros H; discriminate H | intros H; exfalso; lia].
  + assert (Hb : b <> 0) by (intros E; apply Hw; left; exact E).
    destruct (IH w ltac:(intros H; apply Hl; right; exact H)
                    ltac:(intros H; apply Hw; right; exact H)) as [F1 F2].
    replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha).
    replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb).
    cbn [negb andb].
    destruct (Z.eqb_spec (tolower a) (tolower b)) as [E|E].
    * rewrite orb_true_r. split.
      -- intros H. apply F1. congruence.
      -- intros H. rewrite E. f_equal. exact (F2 H).
    * replace (a =? b) with false
        by (symmetry; apply Z.eqb_neq; intros Eab; apply E; rewrite Eab; reflexivity).
      cbn [orb]. split.
      -- intros H. exfalso. apply E. congruence.
      -- intros H. exfalso. lia.
Qed.

(* two strings with their NUL agree exactly when the strings do *)
Lemma b9_app0_inv : forall (l1 l2 : list Z), l1 ++ [0] = l2 ++ [0] -> l1 = l2.
Proof.
induction l1 as [|a l1 IH]; intros [|b l2] H; cbn [app] in H.
- reflexivity.
- exfalso. injection H as _ H. destruct l2; cbn [app] in H; discriminate H.
- exfalso. injection H as _ H. destruct l1; cbn [app] in H; discriminate H.
- injection H as -> H. f_equal. exact (IH l2 H).
Qed.

(* the interceptor's answer, read as SegModel's: both strings NUL-free, compared with their NUL *)
Lemma b9_strcasecmp_iff : forall l w, ~ In 0 l -> ~ In 0 w ->
  (map RtSeg.lc (l ++ [0]) = map RtSeg.lc (w ++ [0]) <-> strcasecmp l w = 0).
Proof.
intros l w Hl Hw. rewrite !b9_map_lc, !map_app.
cbn [map]. rewrite b9_tolower_0.
rewrite <- (b9_strcasecmp_map l w Hl Hw).
split; [intros H; exact (b9_app0_inv _ _ H) | intros ->; reflexivity].
Qed.

(** ** r_key's branches (the plain lane's p5_rkey_* lemmas, reproved here) *)
Lemma b9_rkey_none : forall rc cur nm ln L, strchr L EQ = None ->
  r_key rc cur nm ln L = (refuse rc ln F_neither [AS L], cur, nm).
Proof. intros rc cur nm ln L H. unfold r_key. rewrite H. reflexivity. Qed.

Lemma b9_rkey_outs : forall rc nm ln L ei, strchr L EQ = Some ei ->
  r_key rc None nm ln L = (refuse rc ln F_outside [AS (r_trim (firstn ei L))], None, nm).
Proof. intros rc nm ln L ei H. unfold r_key. rewrite H. reflexivity. Qed.

Lemma b9_rkey_knock : forall rc gi nm ln L ei, strchr L EQ = Some ei ->
  strcasecmp (r_trim (firstn ei L)) S_role <> 0 -> strcasecmp (r_trim (firstn ei L)) S_model <> 0 ->
  strcasecmp (r_trim (firstn ei L)) S_ignore <> 0 -> strcasecmp (r_trim (firstn ei L)) S_knock = 0 ->
  r_key rc (Some gi) nm ln L =
    (refuse rc ln F_knock [AS nm; AS (r_unquote (r_trim (skipn (S ei) L)))], Some gi, nm).
Proof.
intros rc gi nm ln L ei H H1 H2 H3 H4. unfold r_key. rewrite H. cbv beta iota zeta.
apply Z.eqb_neq in H1, H2, H3. apply Z.eqb_eq in H4. rewrite H1, H2, H3, H4. reflexivity.
Qed.

Lemma b9_rkey_nokey : forall rc gi nm ln L ei, strchr L EQ = Some ei ->
  strcasecmp (r_trim (firstn ei L)) S_role <> 0 -> strcasecmp (r_trim (firstn ei L)) S_model <> 0 ->
  strcasecmp (r_trim (firstn ei L)) S_ignore <> 0 -> strcasecmp (r_trim (firstn ei L)) S_knock <> 0 ->
  r_key rc (Some gi) nm ln L = (refuse rc ln F_nokey [AS nm; AS (r_trim (firstn ei L))], Some gi, nm).
Proof.
intros rc gi nm ln L ei H H1 H2 H3 H4. unfold r_key. rewrite H. cbv beta iota zeta.
apply Z.eqb_neq in H1, H2, H3, H4. rewrite H1, H2, H3, H4. reflexivity.
Qed.

(** ** unquote (R:78-86) on the trimmed value V (NUL-free, so strlen V = length V) *)
Lemma b9_unq_short : forall V, ~ In 0 V -> (length V < 2)%nat -> r_unquote V = V.
Proof.
intros V H1 H2. unfold r_unquote, strlen. rewrite (cut_nul_id V H1).
replace ((2 <=? length V)%nat) with false by (symmetry; apply Nat.leb_gt; lia). cbn [andb].
reflexivity.
Qed.

Lemma b9_unq_strip : forall V q, ~ In 0 V -> (2 <= length V)%nat -> (q = DQ \/ q = SQ) ->
  nth 0 V 0 = q -> nth (length V - 1) V 0 = q -> r_unquote V = slice 1 (length V - 1) V.
Proof.
intros V q H1 H2 Hq H3 H4. unfold r_unquote, strlen. rewrite (cut_nul_id V H1), H3, H4.
replace ((2 <=? length V)%nat) with true by (symmetry; apply Nat.leb_le; lia).
destruct Hq as [-> | ->]; reflexivity.
Qed.

Lemma b9_unq_keep : forall V, ~ In 0 V -> (2 <= length V)%nat ->
  ~ ((nth 0 V 0 = DQ /\ nth (length V - 1) V 0 = DQ) \/ (nth 0 V 0 = SQ /\ nth (length V - 1) V 0 = SQ)) ->
  r_unquote V = V.
Proof.
intros V H1 H2 H3. unfold r_unquote, strlen. rewrite (cut_nul_id V H1).
replace ((2 <=? length V)%nat) with true by (symmetry; apply Nat.leb_le; lia). cbn [andb].
destruct (nth 0 V 0 =? DQ) eqn:E1, (nth (length V - 1) V 0 =? DQ) eqn:E2,
         (nth 0 V 0 =? SQ) eqn:E3, (nth (length V - 1) V 0 =? SQ) eqn:E4; cbn [andb orb];
  try reflexivity;
  exfalso; apply H3;
  repeat match goal with E : (_ =? _) = true |- _ => apply Z.eqb_eq in E end;
  tauto.
Qed.

(* the stripped value is NUL-free and no longer than V *)
Lemma b9_unq_nulfree : forall V, ~ In 0 V -> ~ In 0 (r_unquote V).
Proof.
intros V H. unfold r_unquote. destruct (_ && _).
- unfold slice. intros Hin. apply H. exact (b9_in_skipn 1 V 0 (b9_in_firstn _ _ _ Hin)).
- rewrite (cut_nul_id V H). exact H.
Qed.

Lemma b9_unq_len : forall V, (length (r_unquote V) <= length V)%nat.
Proof.
intros V. unfold r_unquote. destruct (_ && _).
- unfold slice. rewrite length_firstn, length_skipn. lia.
- pose proof (cut_nul_len V). lia.
Qed.

(** ** cur as a pointer: NULL exactly for None (c is a live block, so c > 0) *)
Lemma b9_cur_ptr_eq0 : forall c cf cur, 0 < c -> pf_cur_ok cf cur ->
  (pf_cur_ptr c cur = 0 <-> cur = None).
Proof.
intros c cf cur Hc Hok. unfold pf_cur_ptr, seg_spec.rseg_addr.
destruct cur as [i|]; [|split; [reflexivity | reflexivity]].
split; [intros H; exfalso; unfold seg_spec.RSEG_SIZE in H; lia | intros H; discriminate H].
Qed.

(* the i-th byte value of a byte list *)
Lemma b9_zs_nth : forall (f : list byte) i, nth i (seg_spec.zs f) 0 = bv_unsigned (nth i f ZB0).
Proof.
unfold seg_spec.zs, ZB0. induction f as [|b f IH]; intros i.
- destruct i; cbn [map nth]; vm_compute; reflexivity.
- destruct i as [|i]; cbn [map nth]; [reflexivity | apply IH].
Qed.

(** ** cur_name's C string: pf_nm gives the bytes and the NUL, and the 16-byte field gives the slack *)
Lemma b9_nm_str : forall rd a nm, a mod 8 = 0 -> pf_nm rd a nm -> sa_str rd a nm /\ (length nm < 16)%nat.
Proof.
intros rd a nm Ha (f & Hb & Hlen & Hlt & Hnz & Hpre).
assert (HV : forall i, (i < 16)%nat -> rd (a + Z.of_nat i) = Some (nth i (seg_spec.zs f) 0)).
{ intros i Hi. rewrite b9_zs_nth. apply Hb. rewrite Hlen. exact Hi. }
assert (HN : forall i, (i <= length nm)%nat -> nth i (seg_spec.zs f) 0 = nth i (nm ++ [0]) 0).
{ intros i Hi. rewrite <- Hpre, nth_firstn.
  replace ((i <? S (length nm))%nat) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
split; [|exact Hlt]. split; [split|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (HV i ltac:(lia)), (HN i ltac:(lia)). reflexivity.
- exact Hnz.
- intros x Hx.
  pose proof (Z.mod_pos_bound (a + Z.of_nat (length nm)) 8 ltac:(lia)) as HM.
  assert (HE : (a + Z.of_nat (length nm)) mod 8 = Z.of_nat (length nm) mod 8).
  { rewrite <- (Z.add_0_l (Z.of_nat (length nm))) at 2. rewrite <- Ha.
    symmetry. apply Z.add_mod_idemp_l. lia. }
  pose proof (Z.mod_pos_bound (Z.of_nat (length nm)) 8 ltac:(lia)) as HM2.
  assert (Hb8 : Z.of_nat (length nm) - Z.of_nat (length nm) mod 8 + 8 <= 16).
  { pose proof (Z.div_mod (Z.of_nat (length nm)) 8 ltac:(lia)) as HD. lia. }
  replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
  rewrite (HV (Z.to_nat (x - a)) ltac:(lia)). discriminate.
Qed.

(** ** The frame's buf at a cut of B9: PF_SC_LINE has buf IN scope, so its 64 shadow cells are 0 and every
    range inside [F + 0x40, F + 0x240) is addressable. This is what checks B#9, B#10, B#11, B#13 and B#14
    need, and what trim / strlen / strcasecmp / refuse ask of every buf string they read. *)
Lemma b9_shb_buf : forall i, 8 <= i < 72 -> pf_shb PF_SC_LINE i = 0.
Proof.
intros i Hi. unfold pf_shb.
replace (i <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 6) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
replace (i <? 72) with true by (symmetry; apply Z.ltb_lt; lia).
reflexivity.
Qed.

Lemma b9_sh_split : forall SH F x, SH = shadow_addr F -> F mod 8 = 0 ->
  SHADOW_OFF + x / 8 = SH + (x - F) / 8.
Proof.
intros SH F x -> HF. unfold shadow_addr.
replace x with ((x - F) + (F / 8) * 8) at 1 by (Z.div_mod_to_equations; lia).
rewrite Z.div_add by lia. lia.
Qed.

Lemma b9_buf_addr : forall (rd : reader) SH F q n,
  (forall j, 0 <= j < 144 -> rd (SH + j) = Some (pf_shb PF_SC_LINE j)) ->
  SH = shadow_addr F -> F mod 8 = 0 -> 0 <= F ->
  F + 0x40 <= q -> q + n <= F + 0x240 -> 0 <= n ->
  range_addressable rd SHADOW_OFF q n.
Proof.
intros rd SH F q n H ESH HF HF0 H1 H2 Hn x Hx.
exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. rewrite (b9_sh_split SH F x ESH HF).
rewrite (H ((x - F) / 8) ltac:(Z.div_mod_to_equations; lia)).
rewrite (b9_shb_buf ((x - F) / 8) ltac:(Z.div_mod_to_equations; lia)). reflexivity.
Qed.

Lemma b9_buf_hull : forall (rd : reader) SH F q n,
  (forall j, 0 <= j < 144 -> rd (SH + j) = Some (pf_shb PF_SC_LINE j)) ->
  SH = shadow_addr F -> F mod 8 = 0 -> 0 <= F ->
  F + 0x40 <= q -> q + n <= F + 0x240 -> 0 < n ->
  shadow_hull_vis rd q n.
Proof.
intros rd SH F q n H ESH HF HF0 H1 H2 Hn s Hs.
assert (HSH : SH = SHADOW_OFF + F / 8) by (rewrite ESH; reflexivity).
assert (HSH0 : 0 <= SH) by (unfold SHADOW_OFF in HSH; Z.div_mod_to_equations; lia).
unfold shadow_addr in Hs.
rewrite (b9_sh_split SH F q ESH HF), (b9_sh_split SH F (q + n - 1) ESH HF) in Hs.
assert (D1 : 8 <= (q - F) / 8) by (Z.div_mod_to_equations; lia).
assert (D2 : (q + n - 1 - F) / 8 <= 71) by (Z.div_mod_to_equations; lia).
assert (Hrng : 0 <= s - SH < 144) by (Z.div_mod_to_equations; lia).
replace s with (SH + (s - SH)) by lia.
rewrite (H (s - SH) Hrng). discriminate.
Qed.
