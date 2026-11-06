(* The pure part of the walk of cross_check on IMAGE B (reac-pw/fuzz_segconf, fuzz_segconf.asan-ubsan,
   pin c3796c0b38f3; cross_check at 0x897cc, 696 bytes, 174 instructions): facts about SegModel's
   cross_check / r_cross_seg / refuse and about seg_spec's record encoding read through a reader. No machine
   state and no instruction of the binary appear here; every lemma is about Gallina terms only. Because of
   that, this file is the same text on both images: it is ADAPTED from the image-A G3 walk owner's image-A
   lib/A/Prog/cross_check_f.v (commit 130284ff40f1) with the Requires moved to the image-B
   kit copies (lib.B, the unit owner's B-kit copy lane) and lib.B.Prog, the pc comments moved to image B's addresses, and
   cc_fold brought here from cross_check_d.v so that this file needs no listing and can be built before the
   image-B listing is switched to the B kit.

   The walk uses them like this. Its loop invariant says that the block at c holds `cc_at v i`, the record
   after i passes of the fold that SegModel.cross_check runs (cross_check_d.v). One pass at index i:
   - reads s = nth i (rc_seg (cc_at v i)) rseg_d through sa_rconf_fields;
   - picks the arm by rs_model_set s and `rs_role_set s && (rs_role s =? 4)` (r_cross_seg_model /
     r_cross_seg_box / r_cross_seg_keep);
   - on an arm, refuse's post gives the record `SegModel.refuse (cc_at v i) 0 F_* args`, and the two inline
     stores then give `r_upd ... i rs_drop_model` / `rs_drop_role` through sa_rconf_drop_model /
     sa_rconf_drop_role;
   - the latch reloads c->n, which cc_fold_len says is still n, and steps the index with cc_fold_S;
   - the exit at i = n is cc_fold_all. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the reader's record after the first i passes of the fold that SegModel.cross_check runs (image A keeps this
   in cross_check_d.v; here it is in the listing-free file so that section 1 builds before the listing) *)
Definition cc_fold (rcs : rconf) (i : Z) : rconf := fold_left r_cross_seg (seq 0 (Z.to_nat i)) rcs.

(* destruct every `if` of the goal *)
Ltac ccf_ifs := repeat match goal with |- context [if ?b then _ else _] => destruct b end.

(* ============================== 1. the fold SegModel.cross_check runs ============================== *)
Lemma cc_fold_0 : forall rcs, cc_fold rcs 0 = rcs.
Proof. intros rcs. reflexivity. Qed.
Lemma cc_fold_S : forall rcs i, 0 <= i -> cc_fold rcs (i + 1) = r_cross_seg (cc_fold rcs i) (Z.to_nat i).
Proof.
intros rcs i Hi. unfold cc_fold.
replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
rewrite seq_S, fold_left_app. reflexivity.
Qed.
Lemma cc_fold_all : forall rcs, cc_fold rcs (Z.of_nat (length (rc_seg rcs))) = SegModel.cross_check rcs.
Proof. intros rcs. unfold cc_fold, SegModel.cross_check. rewrite Nat2Z.id. reflexivity. Qed.
Lemma r_upd_seg_len : forall c i g, length (rc_seg (r_upd c i g)) = length (rc_seg c).
Proof. intros c i g. unfold r_upd, r_set_segs. cbn [rc_seg]. apply upd_nth_len. Qed.
Lemma refuse_seg : forall c ln f args, rc_seg (SegModel.refuse c ln f args) = rc_seg c.
Proof. intros c ln f args. unfold SegModel.refuse. cbv zeta. ccf_ifs; reflexivity. Qed.
Lemma refuse_refused : forall c ln f args, rc_refused (SegModel.refuse c ln f args) = rc_refused c + 1.
Proof. intros c ln f args. unfold SegModel.refuse. cbv zeta. ccf_ifs; reflexivity. Qed.
Lemma r_cross_seg_len : forall c i, length (rc_seg (r_cross_seg c i)) = length (rc_seg c).
Proof.
intros c i. unfold r_cross_seg. cbv zeta. ccf_ifs; rewrite ?r_upd_seg_len, ?refuse_seg; reflexivity.
Qed.
Lemma ccf_fold_len : forall l c, length (rc_seg (fold_left r_cross_seg l c)) = length (rc_seg c).
Proof.
induction l as [|x l IH]; intros c; cbn [fold_left]; [reflexivity|].
rewrite IH. apply r_cross_seg_len.
Qed.
Lemma cc_fold_len : forall rcs i, 0 <= i -> length (rc_seg (cc_fold rcs i)) = length (rc_seg rcs).
Proof. intros rcs i _. unfold cc_fold. apply ccf_fold_len. Qed.
Lemma ccf_upd_refused : forall c i g, rc_refused (r_upd c i g) = rc_refused c.
Proof. intros c i g. reflexivity. Qed.
Lemma r_cross_seg_refused : forall c i, rc_refused c <= rc_refused (r_cross_seg c i) <= rc_refused c + 1.
Proof.
intros c i. unfold r_cross_seg. cbv zeta. ccf_ifs; rewrite ?ccf_upd_refused, ?refuse_refused; lia.
Qed.
Lemma ccf_fold_refused : forall l c,
  rc_refused c <= rc_refused (fold_left r_cross_seg l c) <= rc_refused c + Z.of_nat (length l).
Proof.
induction l as [|x l IH]; intros c; cbn [fold_left length]; [lia|].
pose proof (r_cross_seg_refused c x) as H1. specialize (IH (r_cross_seg c x)). lia.
Qed.
Lemma cc_fold_refused : forall rcs i, 0 <= i ->
  rc_refused rcs <= rc_refused (cc_fold rcs i) <= rc_refused rcs + i.
Proof.
intros rcs i Hi. unfold cc_fold.
pose proof (ccf_fold_refused (seq 0 (Z.to_nat i)) rcs) as H. rewrite length_seq in H. lia.
Qed.

(* ===================== 2. which arm of a pass the two tested flags choose ===================== *)
(* the model-drop arm (image B's 0x8992c-0x89964, image A's 0x89338-0x8937c): model_set and not (role_set and role = BOX) *)
Lemma r_cross_seg_model : forall c i,
  rs_model_set (nth i (rc_seg c) rseg_d) = true ->
  rs_role_set (nth i (rc_seg c) rseg_d) && (rs_role (nth i (rc_seg c) rseg_d) =? 4) = false ->
  r_cross_seg c i =
    r_upd (SegModel.refuse c 0 F_xmodel
             [AS (rs_name (nth i (rc_seg c) rseg_d)); AS (rs_model (nth i (rc_seg c) rseg_d))])
          i rs_drop_model.
Proof. intros c i H1 H2. unfold r_cross_seg. cbv zeta. rewrite H1, H2. reflexivity. Qed.
(* the box arm (image B 0x898f0-0x89924, image A 0x8938c-0x893b4): role_set and role = BOX and not model_set *)
Lemma r_cross_seg_box : forall c i,
  rs_model_set (nth i (rc_seg c) rseg_d) = false ->
  rs_role_set (nth i (rc_seg c) rseg_d) && (rs_role (nth i (rc_seg c) rseg_d) =? 4) = true ->
  r_cross_seg c i =
    r_upd (SegModel.refuse c 0 F_xbox [AS (rs_name (nth i (rc_seg c) rseg_d))]) i rs_drop_role.
Proof. intros c i H1 H2. unfold r_cross_seg. cbv zeta. rewrite H1, H2. reflexivity. Qed.
(* straight to the latch: neither arm *)
Lemma r_cross_seg_keep : forall c i,
  (rs_model_set (nth i (rc_seg c) rseg_d) = false /\
   rs_role_set (nth i (rc_seg c) rseg_d) && (rs_role (nth i (rc_seg c) rseg_d) =? 4) = false) \/
  (rs_model_set (nth i (rc_seg c) rseg_d) = true /\
   rs_role_set (nth i (rc_seg c) rseg_d) && (rs_role (nth i (rc_seg c) rseg_d) =? 4) = true) ->
  r_cross_seg c i = c.
Proof.
intros c i [[H1 H2] | [H1 H2]]; unfold r_cross_seg; cbv zeta; rewrite H1, H2; reflexivity.
Qed.

(* ===================== byte lists, fields and the reader (helpers of sections 3-4) ===================== *)
Lemma ccf_nth_firstn : forall {A} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros A l n; revert l; induction n as [|n IH]; intros l i d Hi; [lia|].
destruct l as [|x l]; [destruct i; reflexivity|].
destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma ccf_nth_skipn : forall {A} (l : list A) off i d, nth i (skipn off l) d = nth (off + i) l d.
Proof.
intros A l off; revert l; induction off as [|off IH]; intros l i d; [reflexivity|].
destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma ccf_nth_fld : forall (bs : list byte) off n i d, (i < n)%nat ->
  nth i (seg_spec.fld off n bs) d = nth (off + i) bs d.
Proof. intros bs off n i d Hi. unfold seg_spec.fld. rewrite ccf_nth_firstn by exact Hi. apply ccf_nth_skipn. Qed.
Lemma ccf_len_fld : forall (bs : list byte) off n, (off + n <= length bs)%nat ->
  length (seg_spec.fld off n bs) = n.
Proof. intros bs off n H. unfold seg_spec.fld. rewrite length_firstn, length_skipn. lia. Qed.
Lemma ccf_zb0 : bv_unsigned ZB0 = 0.
Proof. reflexivity. Qed.

(* the 4 little-endian bytes of a value, as LPS's Z_to_le_bytes builds them (seg_spec.u32_enc's le4) *)
Fixpoint ccf_le (n : nat) (z : Z) : list byte :=
  match n with O => [] | S n' => Z_to_bv 8 z :: ccf_le n' (Z.shiftr z 8) end.
Lemma ccf_len_le : forall n z, length (ccf_le n z) = n.
Proof. induction n as [|n IH]; intros z; [reflexivity|]. cbn [ccf_le length]. rewrite IH. reflexivity. Qed.
Lemma ccf_nth_le : forall n z k, (k < n)%nat -> nth k (ccf_le n z) ZB0 = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
cbn [ccf_le]. destruct k as [|k].
- cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma ccf_w64 : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 v) = v.
Proof.
intros v Hv. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma ccf_u32_enc_le : forall v f, seg_spec.u32_enc v f -> 0 <= v < 2 ^ 32 /\ f = ccf_le 4 v.
Proof.
intros v f [Hv Hf]. split; [exact Hv|]. rewrite Hf.
transitivity (ccf_le 4 (bv_unsigned (Z_to_bv 64 v))); [reflexivity|].
rewrite ccf_w64 by lia. reflexivity.
Qed.
Lemma ccf_u32_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (ccf_le 4 v) ZB0) = le_byte v 4 k.
Proof.
intros v k Hv Hk. rewrite ccf_nth_le by exact Hk. rewrite Z_to_bv_unsigned. unfold le_byte, bv_wrap.
change (bv_modulus 8) with 256. change (8 * Z.of_nat 4) with 32.
rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.

(* a field of a byte block through the reader *)
Lemma ccf_sa_bytes_fld : forall rd a bs off n, sa_bytes rd a bs -> (off + n <= length bs)%nat ->
  sa_bytes rd (a + Z.of_nat off) (seg_spec.fld off n bs).
Proof.
intros rd a bs off n Hb Hl. unfold sa_bytes in *. intros k Hk.
rewrite ccf_len_fld in Hk by exact Hl. rewrite ccf_nth_fld by exact Hk.
replace (a + Z.of_nat off + Z.of_nat k) with (a + Z.of_nat (off + k)) by lia.
apply Hb. lia.
Qed.
Lemma ccf_sub_bytes : forall rd a g off n, sa_bytes rd a g -> 0 <= off -> 0 <= n ->
  off + n <= Z.of_nat (length g) -> sa_bytes rd (a + off) (seg_spec.fldz off n g).
Proof.
intros rd a g off n Hb H0 H1 H2. unfold seg_spec.fldz.
replace (a + off) with (a + Z.of_nat (Z.to_nat off)) by lia.
apply ccf_sa_bytes_fld; [exact Hb | lia].
Qed.
Lemma ccf_val_of_u32 : forall rd a f v, sa_bytes rd a f -> seg_spec.u32_enc v f -> sa_val rd a 4 v.
Proof.
intros rd a f v Hb Hu. apply ccf_u32_enc_le in Hu. destruct Hu as [Hv Hf]. subst f.
unfold sa_bytes in Hb. unfold sa_val. intros k Hk.
rewrite Hb by (rewrite ccf_len_le; exact Hk). f_equal. apply ccf_u32_byte; assumption.
Qed.
Lemma ccf_val_of_flag : forall rd a f (b : bool), sa_bytes rd a f -> seg_spec.flag_enc b f ->
  sa_val rd a 4 (if b then 1 else 0).
Proof.
intros rd a f b Hb Hf. apply (ccf_val_of_u32 rd a f); [exact Hb|].
unfold seg_spec.u32_enc. split; [destruct b; lia | exact Hf].
Qed.
Lemma ccf_strz_of_cstr : forall rd p cap s f, sa_bytes rd p f -> seg_spec.cstr_enc cap s f -> sa_strz rd p s.
Proof.
intros rd p cap s f Hb Hc. destruct Hc as (Hl & Hs & Hn & Hz).
unfold sa_strz, sa_zs. split; [|exact Hn].
unfold sa_bytes in Hb. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite <- Hz. rewrite ccf_nth_firstn by lia. unfold seg_spec.zs.
rewrite (nth_indep (map bv_unsigned f) 0 (bv_unsigned ZB0)) by (rewrite length_map; lia).
rewrite map_nth. apply Hb. lia.
Qed.
(* the fields of one entry the pass reads, from its 356 bytes *)
Lemma ccf_rseg_fields : forall rd a s g, sa_bytes rd a g -> seg_spec.rseg_enc s g ->
  sa_strz rd a (rs_name s) /\ (length (rs_name s) < 16)%nat /\
  sa_strz rd (a + seg_spec.RS_MODEL) (rs_model s) /\ (length (rs_model s) < 24)%nat /\
  sa_val rd (a + seg_spec.RS_ROLE) 4 (rs_role s) /\ 0 <= rs_role s < 2 ^ 31 /\
  sa_val rd (a + seg_spec.RS_ROLE_SET) 4 (if rs_role_set s then 1 else 0) /\
  sa_val rd (a + seg_spec.RS_MODEL_SET) 4 (if rs_model_set s then 1 else 0).
Proof.
intros rd a s g Hb Hs.
destruct Hs as (Hl & Hn & Hr & Hrs & _ & _ & Hm & Hms & _).
assert (Hlz : Z.of_nat (length g) = 356) by (rewrite Hl; reflexivity).
pose proof (ccf_sa_bytes_fld rd a g 0 16 Hb ltac:(lia)) as B0.
change (a + Z.of_nat 0) with (a + 0) in B0. rewrite Z.add_0_r in B0.
pose proof (ccf_sub_bytes rd a g seg_spec.RS_MODEL 24 Hb) as Bm.
pose proof (ccf_sub_bytes rd a g seg_spec.RS_ROLE 4 Hb) as Br.
pose proof (ccf_sub_bytes rd a g seg_spec.RS_ROLE_SET 4 Hb) as Brs.
pose proof (ccf_sub_bytes rd a g seg_spec.RS_MODEL_SET 4 Hb) as Bms.
unfold seg_spec.RS_MODEL, seg_spec.RS_ROLE, seg_spec.RS_ROLE_SET, seg_spec.RS_MODEL_SET in *.
specialize (Bm ltac:(lia) ltac:(lia) ltac:(lia)).
specialize (Br ltac:(lia) ltac:(lia) ltac:(lia)).
specialize (Brs ltac:(lia) ltac:(lia) ltac:(lia)).
specialize (Bms ltac:(lia) ltac:(lia) ltac:(lia)).
destruct Hr as [Hu Hr31].
split; [exact (ccf_strz_of_cstr rd a 16 _ _ B0 Hn)|].
split; [destruct Hn as (_ & Hn' & _); exact Hn'|].
split; [exact (ccf_strz_of_cstr rd _ 24 _ _ Bm Hm)|].
split; [destruct Hm as (_ & Hm' & _); exact Hm'|].
split; [exact (ccf_val_of_u32 rd _ _ _ Br Hu)|].
split; [destruct Hu as [[Hr0 _] _]; lia|].
split; [exact (ccf_val_of_flag rd _ _ _ Brs Hrs)|].
exact (ccf_val_of_flag rd _ _ _ Bms Hms).
Qed.

(* ===================== 3. what the record's bytes give the loop ===================== *)
(* every byte of the block is mapped: sa_rconf is a byte list of SEG_C_SIZE bytes at c *)
Lemma sa_rconf_mapped : forall rd c rcs a, sa_rconf rd c rcs -> 0 <= a < seg_spec.SEG_C_SIZE ->
  rd (c + a) <> None.
Proof.
intros rd c rcs a [bs [Hb He]] Ha. destruct He as [Hl _].
unfold sa_bytes in Hb. specialize (Hb (Z.to_nat a)).
rewrite Z2Nat.id in Hb by lia. rewrite Hb by lia. discriminate.
Qed.
(* c->n and the two list bounds the encoding fixes *)
Lemma sa_rconf_n : forall rd c rcs, sa_rconf rd c rcs ->
  sa_val rd (c + seg_spec.RC_N) 4 (Z.of_nat (length (rc_seg rcs))) /\
  (length (rc_seg rcs) <= 32)%nat /\ (length (rc_refusal rcs) <= 8)%nat.
Proof.
intros rd c rcs [bs [Hb He]].
destruct He as (Hl & H32 & _ & Hn & H8 & _).
split; [|split; assumption].
apply (ccf_val_of_u32 rd _ (seg_spec.fldz seg_spec.RC_N 4 bs)); [|exact Hn].
apply ccf_sub_bytes; [exact Hb | unfold seg_spec.RC_N; lia | lia |].
unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *. lia.
Qed.
(* the fields of seg[i] the pass reads and writes *)
Lemma sa_rconf_fields : forall rd c rcs i, sa_rconf rd c rcs -> (i < length (rc_seg rcs))%nat ->
  sa_strz rd (c + 356 * Z.of_nat i) (rs_name (nth i (rc_seg rcs) rseg_d)) /\
  (length (rs_name (nth i (rc_seg rcs) rseg_d)) < 16)%nat /\
  sa_strz rd (c + 356 * Z.of_nat i + seg_spec.RS_MODEL) (rs_model (nth i (rc_seg rcs) rseg_d)) /\
  (length (rs_model (nth i (rc_seg rcs) rseg_d)) < 24)%nat /\
  sa_val rd (c + 356 * Z.of_nat i + seg_spec.RS_ROLE) 4 (rs_role (nth i (rc_seg rcs) rseg_d)) /\
  0 <= rs_role (nth i (rc_seg rcs) rseg_d) < 2 ^ 31 /\
  sa_val rd (c + 356 * Z.of_nat i + seg_spec.RS_ROLE_SET) 4
    (if rs_role_set (nth i (rc_seg rcs) rseg_d) then 1 else 0) /\
  sa_val rd (c + 356 * Z.of_nat i + seg_spec.RS_MODEL_SET) 4
    (if rs_model_set (nth i (rc_seg rcs) rseg_d) then 1 else 0).
Proof.
intros rd c rcs i [bs [Hb He]] Hi.
destruct He as (Hl & H32 & Hseg & _).
assert (Hg : sa_bytes rd (c + 356 * Z.of_nat i) (seg_spec.fld (356 * i) 356 bs)).
{ replace (c + 356 * Z.of_nat i) with (c + Z.of_nat (356 * i)) by lia.
  apply ccf_sa_bytes_fld; [exact Hb|]. unfold seg_spec.SEG_C_SIZE in Hl. lia. }
exact (ccf_rseg_fields rd _ _ _ Hg (Hseg i Hi)).
Qed.

(* ===================== a block with some bytes replaced by zeros (helpers of section 4) ===================== *)
(* the bytes of bs with every index k where P k holds set to 0 *)
Definition ccf_zap (P : nat -> bool) (bs : list byte) : list byte :=
  map (fun k => if P k then ZB0 else nth k bs ZB0) (seq 0 (length bs)).
Lemma ccf_zap_len : forall P bs, length (ccf_zap P bs) = length bs.
Proof. intros P bs. unfold ccf_zap. rewrite length_map, length_seq. reflexivity. Qed.
Lemma ccf_zap_nth : forall P bs k, (k < length bs)%nat ->
  nth k (ccf_zap P bs) ZB0 = if P k then ZB0 else nth k bs ZB0.
Proof.
intros P bs k Hk. unfold ccf_zap.
set (h := fun k0 : nat => if P k0 then ZB0 else nth k0 bs ZB0).
rewrite (nth_indep (map h (seq 0 (length bs))) ZB0 (h 0%nat)) by (rewrite length_map, length_seq; exact Hk).
rewrite map_nth, seq_nth by exact Hk. reflexivity.
Qed.
Lemma ccf_nth_repeat : forall (a : byte) m k, nth k (repeat a m) a = a.
Proof. intros a m; induction m as [|m IH]; intros [|k]; cbn [repeat nth]; auto. Qed.
Lemma ccf_firstn1_zs : forall f, (0 < length f)%nat -> nth 0 f ZB0 = ZB0 -> firstn 1 (seg_spec.zs f) = [0].
Proof. intros [|b f] Hl Hb; cbn [length] in Hl; [lia|]. cbn [nth] in Hb. subst b. reflexivity. Qed.
Lemma ccf_fld_zap_keep : forall P bs off n, (forall k, (off <= k < off + n)%nat -> P k = false) ->
  seg_spec.fld off n (ccf_zap P bs) = seg_spec.fld off n bs.
Proof.
intros P bs off n HP. apply nth_ext with (d := ZB0) (d' := ZB0).
- unfold seg_spec.fld. rewrite !length_firstn, !length_skipn, ccf_zap_len. reflexivity.
- intros k Hk. unfold seg_spec.fld in *. rewrite length_firstn, length_skipn, ccf_zap_len in Hk.
  rewrite !ccf_nth_firstn by lia. rewrite !ccf_nth_skipn. rewrite ccf_zap_nth by lia.
  rewrite HP by lia. reflexivity.
Qed.
Lemma ccf_fld_zap_all : forall P bs off n, (off + n <= length bs)%nat ->
  (forall k, (off <= k < off + n)%nat -> P k = true) ->
  seg_spec.fld off n (ccf_zap P bs) = repeat ZB0 n.
Proof.
intros P bs off n Hl HP. apply nth_ext with (d := ZB0) (d' := ZB0).
- rewrite ccf_len_fld by (rewrite ccf_zap_len; exact Hl). rewrite repeat_length. reflexivity.
- intros k Hk. rewrite ccf_len_fld in Hk by (rewrite ccf_zap_len; exact Hl).
  rewrite ccf_nth_fld by exact Hk. rewrite ccf_zap_nth by lia. rewrite HP by lia.
  rewrite ccf_nth_repeat. reflexivity.
Qed.
Lemma ccf_fld_zap_shift : forall P bs off n, (off + n <= length bs)%nat ->
  seg_spec.fld off n (ccf_zap P bs) = ccf_zap (fun k => P (off + k)%nat) (seg_spec.fld off n bs).
Proof.
intros P bs off n Hl. apply nth_ext with (d := ZB0) (d' := ZB0).
- rewrite ccf_zap_len. rewrite !ccf_len_fld; rewrite ?ccf_zap_len; first [reflexivity | exact Hl].
- intros k Hk. rewrite ccf_len_fld in Hk by (rewrite ccf_zap_len; exact Hl).
  rewrite ccf_zap_nth by (rewrite ccf_len_fld by exact Hl; exact Hk).
  rewrite !ccf_nth_fld by exact Hk. rewrite ccf_zap_nth by lia. reflexivity.
Qed.
Lemma ccf_zap_bytes : forall (rd rd' : reader) a bs P, sa_bytes rd a bs ->
  (forall k, (k < length bs)%nat -> P k = true -> rd' (a + Z.of_nat k) = Some 0) ->
  (forall k, (k < length bs)%nat -> P k = false -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) ->
  sa_bytes rd' a (ccf_zap P bs).
Proof.
intros rd rd' a bs P Hb H1 H0. unfold sa_bytes in *. intros k Hk. rewrite ccf_zap_len in Hk.
rewrite ccf_zap_nth by exact Hk. destruct (P k) eqn:E.
- rewrite (H1 k Hk E). reflexivity.
- rewrite (H0 k Hk E). exact (Hb k Hk).
Qed.
Lemma ccf_nth_upd_eq : forall {A} i (f : A -> A) (l : list A) d, (i < length l)%nat ->
  nth i (upd_nth i f l) d = f (nth i l d).
Proof.
intros A i f l; revert i; induction l as [|x l IH]; intros [|i] d Hi; cbn in *; try lia; [reflexivity|].
apply IH. lia.
Qed.
Lemma ccf_nth_upd_ne : forall {A} i (f : A -> A) (l : list A) j d, j <> i ->
  nth j (upd_nth i f l) d = nth j l d.
Proof.
intros A i f l; revert i; induction l as [|x l IH]; intros [|i] [|j] d Hji; cbn; try reflexivity; try lia.
apply IH. lia.
Qed.
(* the record's encoding after entry i is rewritten by f, where the zeroed bytes lie inside entry i and turn the
   entry's encoding of s into one of f s *)
Lemma ccf_rconf_zap : forall rcs bs i f P,
  seg_spec.rconf_enc rcs bs -> (i < length (rc_seg rcs))%nat ->
  (forall k, P k = true -> (356 * i <= k < 356 * i + 356)%nat) ->
  (forall s g, seg_spec.rseg_enc s g -> seg_spec.rseg_enc (f s) (ccf_zap (fun k => P (356 * i + k)%nat) g)) ->
  seg_spec.rconf_enc (r_upd rcs i f) (ccf_zap P bs).
Proof.
intros rcs bs i f P He Hi HP Hf.
destruct He as (Hl & H32 & Hseg & Hn & H8 & Href & Hnr & Hrf & Hov & Hrd & Hgen).
assert (Hi32 : (i < 32)%nat) by lia.
assert (Hhi : forall off n, (356 * 32 <= off)%nat ->
  seg_spec.fld off n (ccf_zap P bs) = seg_spec.fld off n bs).
{ intros off n Ho. apply ccf_fld_zap_keep. intros k Hk.
  destruct (P k) eqn:E; [exfalso; apply HP in E; lia | reflexivity]. }
unfold seg_spec.rconf_enc, seg_spec.fldz in *. unfold r_upd, r_set_segs.
cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen].
rewrite !upd_nth_len.
split; [rewrite ccf_zap_len; exact Hl|].
split; [exact H32|].
split.
{ intros j Hj. destruct (Nat.eq_dec j i) as [->|Hji].
  - rewrite ccf_nth_upd_eq by exact Hi.
    rewrite ccf_fld_zap_shift by (unfold seg_spec.SEG_C_SIZE in Hl; lia).
    apply Hf. apply Hseg. exact Hi.
  - rewrite ccf_nth_upd_ne by exact Hji.
    rewrite ccf_fld_zap_keep; [apply Hseg; exact Hj|].
    intros k Hk. destruct (P k) eqn:E; [exfalso; apply HP in E; lia | reflexivity]. }
split; [rewrite Hhi; [exact Hn | unfold seg_spec.RC_N; lia]|].
split; [exact H8|].
split; [intros j Hj; rewrite Hhi; [apply Href; exact Hj | unfold seg_spec.RC_REFUSAL; lia]|].
split; [rewrite Hhi; [exact Hnr | unfold seg_spec.RC_NREF; lia]|].
split; [rewrite Hhi; [exact Hrf | unfold seg_spec.RC_REFUSED; lia]|].
split; [rewrite Hhi; [exact Hov | unfold seg_spec.RC_OVERFLOW; lia]|].
split; [rewrite Hhi; [exact Hrd | unfold seg_spec.RC_READING; lia]|].
rewrite Hhi; [exact Hgen | unfold seg_spec.RC_GEN; lia].
Qed.
(* one entry after the model arm's two stores: model[0] = 0 (offset 0x24) and model_set = 0 (0x3c .. 0x40) *)
Lemma ccf_rseg_drop_model : forall s g P, seg_spec.rseg_enc s g ->
  P 36%nat = true -> (forall k, (60 <= k < 64)%nat -> P k = true) ->
  (forall k, k <> 36%nat -> ~ (60 <= k < 64)%nat -> P k = false) ->
  seg_spec.rseg_enc (rs_drop_model s) (ccf_zap P g).
Proof.
intros s g P Hs H36 H60 Hout.
destruct Hs as (Hl & Hn & Hr & Hrs & Hi & His & Hm & Hms & Hmf & Hrf & Hif & Hsg).
unfold seg_spec.rseg_enc, seg_spec.fldz in *.
unfold seg_spec.RS_ROLE, seg_spec.RS_ROLE_SET, seg_spec.RS_IGNORE, seg_spec.RS_IGNORE_SET, seg_spec.RS_MODEL,
  seg_spec.RS_MODEL_SET, seg_spec.RS_MODEL_FILE, seg_spec.RS_ROLE_FILE, seg_spec.RS_IGNORE_FILE,
  seg_spec.RS_SEEN_GEN in *.
cbn [rs_drop_model rs_name rs_role rs_role_set rs_ignore rs_ignore_set rs_model rs_model_set rs_model_file
  rs_role_file rs_ignore_file rs_seen_gen].
assert (K : forall off n, (forall k, (off <= k < off + n)%nat -> k <> 36%nat /\ ~ (60 <= k < 64)%nat) ->
  seg_spec.fld off n (ccf_zap P g) = seg_spec.fld off n g).
{ intros off n Hk. apply ccf_fld_zap_keep. intros k Hk'. destruct (Hk k Hk') as [K1 K2]. apply Hout; assumption. }
split; [rewrite ccf_zap_len; exact Hl|].
split; [rewrite K; [exact Hn | intros k Hk; lia]|].
split; [rewrite K; [exact Hr | intros k Hk; lia]|].
split; [rewrite K; [exact Hrs | intros k Hk; lia]|].
split; [rewrite K; [exact Hi | intros k Hk; lia]|].
split; [rewrite K; [exact His | intros k Hk; lia]|].
split.
{ unfold seg_spec.cstr_enc.
  assert (Hlf : length (seg_spec.fld (Z.to_nat 36) (Z.to_nat 24) (ccf_zap P g)) = 24%nat).
  { rewrite ccf_len_fld; [reflexivity | rewrite ccf_zap_len; lia]. }
  split; [exact Hlf|]. split; [cbn [length]; lia|]. split; [intros []|].
  cbn [length app]. apply ccf_firstn1_zs; [lia|].
  rewrite ccf_nth_fld by lia. rewrite ccf_zap_nth by lia.
  change (Z.to_nat 36 + 0)%nat with 36%nat. rewrite H36. reflexivity. }
split.
{ rewrite ccf_fld_zap_all; [exact seg_spec.flag_enc_false_zero | lia | intros k Hk; apply H60; lia]. }
split; [rewrite K; [exact Hmf | intros k Hk; lia]|].
split; [rewrite K; [exact Hrf | intros k Hk; lia]|].
split; [rewrite K; [exact Hif | intros k Hk; lia]|].
rewrite K; [exact Hsg | intros k Hk; lia].
Qed.
(* one entry after the box arm's two stores: role = 0 and role_set = 0, the 8 bytes 0x10 .. 0x18 *)
Lemma ccf_rseg_drop_role : forall s g P, seg_spec.rseg_enc s g ->
  (forall k, (16 <= k < 24)%nat -> P k = true) ->
  (forall k, ~ (16 <= k < 24)%nat -> P k = false) ->
  seg_spec.rseg_enc (rs_drop_role s) (ccf_zap P g).
Proof.
intros s g P Hs H16 Hout.
destruct Hs as (Hl & Hn & Hr & Hrs & Hi & His & Hm & Hms & Hmf & Hrf & Hif & Hsg).
unfold seg_spec.rseg_enc, seg_spec.fldz in *.
unfold seg_spec.RS_ROLE, seg_spec.RS_ROLE_SET, seg_spec.RS_IGNORE, seg_spec.RS_IGNORE_SET, seg_spec.RS_MODEL,
  seg_spec.RS_MODEL_SET, seg_spec.RS_MODEL_FILE, seg_spec.RS_ROLE_FILE, seg_spec.RS_IGNORE_FILE,
  seg_spec.RS_SEEN_GEN in *.
cbn [rs_drop_role rs_name rs_role rs_role_set rs_ignore rs_ignore_set rs_model rs_model_set rs_model_file
  rs_role_file rs_ignore_file rs_seen_gen].
assert (K : forall off n, (forall k, (off <= k < off + n)%nat -> ~ (16 <= k < 24)%nat) ->
  seg_spec.fld off n (ccf_zap P g) = seg_spec.fld off n g).
{ intros off n Hk. apply ccf_fld_zap_keep. intros k Hk'. apply Hout. apply Hk. exact Hk'. }
split; [rewrite ccf_zap_len; exact Hl|].
split; [rewrite K; [exact Hn | intros k Hk; lia]|].
split.
{ rewrite ccf_fld_zap_all; [|lia | intros k Hk; apply H16; lia].
  unfold seg_spec.role_enc. split; [exact seg_spec.u32_enc_zero | lia]. }
split.
{ rewrite ccf_fld_zap_all; [exact seg_spec.flag_enc_false_zero | lia | intros k Hk; apply H16; lia]. }
split; [rewrite K; [exact Hi | intros k Hk; lia]|].
split; [rewrite K; [exact His | intros k Hk; lia]|].
split; [rewrite K; [exact Hm | intros k Hk; lia]|].
split; [rewrite K; [exact Hms | intros k Hk; lia]|].
split; [rewrite K; [exact Hmf | intros k Hk; lia]|].
split; [rewrite K; [exact Hrf | intros k Hk; lia]|].
split; [rewrite K; [exact Hif | intros k Hk; lia]|].
rewrite K; [exact Hsg | intros k Hk; lia].
Qed.
(* the byte indices of the block each arm zeroes *)
Definition ccf_Pm (i k : nat) : bool :=
  (k =? 356 * i + 36)%nat || ((356 * i + 60 <=? k)%nat && (k <? 356 * i + 64)%nat).
Definition ccf_Pr (i k : nat) : bool := (356 * i + 16 <=? k)%nat && (k <? 356 * i + 24)%nat.
Ltac ccf_dec := cbv beta; unfold ccf_Pm, ccf_Pr;
  repeat match goal with
  | |- context [Nat.eqb ?x ?y] => destruct (Nat.eqb_spec x y)
  | |- context [Nat.leb ?x ?y] => destruct (Nat.leb_spec x y)
  | |- context [Nat.ltb ?x ?y] => destruct (Nat.ltb_spec x y)
  end; cbn [orb andb]; first [reflexivity | exfalso; lia].

(* ===================== 4. the two inline stores of a pass, through the encoding ===================== *)
(* `sw zero, 60(s4)` (image B 0x89950, model_set = 0) and `sb zero, 0(s5)` (image B 0x89964, model[0] = 0): every other byte
   of the block is as it was *)
Lemma sa_rconf_drop_model : forall (rd rd' : reader) c rcs i,
  sa_rconf rd c rcs -> (i < length (rc_seg rcs))%nat ->
  (forall k, 0 <= k < 4 -> rd' (c + 356 * Z.of_nat i + seg_spec.RS_MODEL_SET + k) = Some 0) ->
  rd' (c + 356 * Z.of_nat i + seg_spec.RS_MODEL) = Some 0 ->
  (forall a, 0 <= a < seg_spec.SEG_C_SIZE ->
     a <> 356 * Z.of_nat i + seg_spec.RS_MODEL ->
     ~ (356 * Z.of_nat i + seg_spec.RS_MODEL_SET <= a < 356 * Z.of_nat i + seg_spec.RS_MODEL_SET + 4) ->
     rd' (c + a) = rd (c + a)) ->
  sa_rconf rd' c (r_upd rcs i rs_drop_model).
Proof.
intros rd rd' c rcs i [bs [Hb He]] Hi Hms Hm Hfr.
assert (Hlen : Z.of_nat (length bs) = seg_spec.SEG_C_SIZE) by (destruct He as [Hl _]; exact Hl).
exists (ccf_zap (ccf_Pm i) bs). split.
- apply (ccf_zap_bytes rd); [exact Hb| |].
  + intros k Hk E. unfold ccf_Pm in E. apply orb_true_iff in E. destruct E as [E|E].
    * apply Nat.eqb_eq in E. rewrite <- Hm. f_equal. unfold seg_spec.RS_MODEL. lia.
    * apply andb_true_iff in E. destruct E as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
      rewrite <- (Hms (Z.of_nat k - (356 * Z.of_nat i + seg_spec.RS_MODEL_SET)))
        by (unfold seg_spec.RS_MODEL_SET; lia).
      f_equal. lia.
  + intros k Hk E. unfold ccf_Pm in E. apply orb_false_iff in E. destruct E as [E1 E2].
    apply Nat.eqb_neq in E1.
    assert (E3 : ~ (356 * i + 60 <= k < 356 * i + 64)%nat).
    { apply andb_false_iff in E2. destruct E2 as [E2|E2]; [apply Nat.leb_gt in E2 | apply Nat.ltb_ge in E2]; lia. }
    apply Hfr; unfold seg_spec.RS_MODEL, seg_spec.RS_MODEL_SET; lia.
- apply (ccf_rconf_zap rcs bs i rs_drop_model (ccf_Pm i) He Hi).
  + intros k E. unfold ccf_Pm in E. apply orb_true_iff in E. destruct E as [E|E].
    * apply Nat.eqb_eq in E. lia.
    * apply andb_true_iff in E. destruct E as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2. lia.
  + intros s g Hs. apply ccf_rseg_drop_model; [exact Hs | ccf_dec | intros k Hk; ccf_dec | intros k K1 K2; ccf_dec].
Qed.
(* `sw zero, 20(s4)` (image B 0x8990c, role_set = 0) and `sw zero, 16(s4)` (image B 0x89924, role = AUTO): the two fields
   are the 8 bytes [RS_ROLE, RS_ROLE + 8) of the entry *)
Lemma sa_rconf_drop_role : forall (rd rd' : reader) c rcs i,
  sa_rconf rd c rcs -> (i < length (rc_seg rcs))%nat ->
  (forall k, 0 <= k < 8 -> rd' (c + 356 * Z.of_nat i + seg_spec.RS_ROLE + k) = Some 0) ->
  (forall a, 0 <= a < seg_spec.SEG_C_SIZE ->
     ~ (356 * Z.of_nat i + seg_spec.RS_ROLE <= a < seg_spec.RS_ROLE + 356 * Z.of_nat i + 8) ->
     rd' (c + a) = rd (c + a)) ->
  sa_rconf rd' c (r_upd rcs i rs_drop_role).
Proof.
intros rd rd' c rcs i [bs [Hb He]] Hi Hr Hfr.
assert (Hlen : Z.of_nat (length bs) = seg_spec.SEG_C_SIZE) by (destruct He as [Hl _]; exact Hl).
exists (ccf_zap (ccf_Pr i) bs). split.
- apply (ccf_zap_bytes rd); [exact Hb| |].
  + intros k Hk E. unfold ccf_Pr in E. apply andb_true_iff in E. destruct E as [E1 E2].
    apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
    rewrite <- (Hr (Z.of_nat k - (356 * Z.of_nat i + seg_spec.RS_ROLE))) by (unfold seg_spec.RS_ROLE; lia).
    f_equal. lia.
  + intros k Hk E. unfold ccf_Pr in E.
    assert (E3 : ~ (356 * i + 16 <= k < 356 * i + 24)%nat).
    { apply andb_false_iff in E. destruct E as [E|E]; [apply Nat.leb_gt in E | apply Nat.ltb_ge in E]; lia. }
    apply Hfr; unfold seg_spec.RS_ROLE; lia.
- apply (ccf_rconf_zap rcs bs i rs_drop_role (ccf_Pr i) He Hi).
  + intros k E. unfold ccf_Pr in E. apply andb_true_iff in E. destruct E as [E1 E2].
    apply Nat.leb_le in E1. apply Nat.ltb_lt in E2. lia.
  + intros s g Hs. apply ccf_rseg_drop_role; [exact Hs | intros k Hk; ccf_dec | intros k Hk; ccf_dec].
Qed.

(* ===================== 5. where seg[i]'s fields lie inside the block ===================== *)
(* every byte a %s argument of a refusal is read from lies in seg[0 .. 32), which ends before refusal[0]: this
   is what keeps the arguments apart from the three forbidden ranges of refuse_pre's sa_va_args (the slot
   refusal[n], the 4 bytes of c->refused, and the stack below sp) *)
Lemma cc_seg_span : forall i off sp, (i < 32)%nat -> 0 <= off -> 0 <= sp -> off + sp <= 356 ->
  0 <= 356 * Z.of_nat i + off /\
  356 * Z.of_nat i + off + sp <= 356 * 32 /\
  356 * 32 <= seg_spec.RC_REFUSAL /\
  356 * 32 <= seg_spec.RC_REFUSED.
Proof. intros i off sp Hi Hoff Hsp Hos. unfold seg_spec.RC_REFUSAL, seg_spec.RC_REFUSED. lia. Qed.

(* the post tail sa_noalloc (SegABase.v): reflexive and transitive, so a pass that changes only the
   side-stack frame state composes with the next *)
Lemma set_fs_id : forall S : astate, S = set_fs (st_fs S) S.
Proof. intros S. destruct S. reflexivity. Qed.
Lemma set_fs_set_fs : forall (f1 f2 : fakestack) (S : astate), set_fs f2 (set_fs f1 S) = set_fs f2 S.
Proof. intros f1 f2 S. reflexivity. Qed.
Lemma sa_noalloc_refl : forall (B : asyms) ly S, sa_noalloc B ly S ly S.
Proof.
intros B ly S. unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|].
exists (st_fs S). apply set_fs_id.
Qed.
Lemma sa_noalloc_trans : forall (B : asyms) ly S ly1 S1 ly2 S2,
  sa_noalloc B ly S ly1 S1 -> sa_noalloc B ly1 S1 ly2 S2 -> sa_noalloc B ly S ly2 S2.
Proof.
intros B ly S ly1 S1 ly2 S2 H1 H2. unfold sa_noalloc in *.
destruct H1 as (P1 & L1 & f1 & E1). destruct H2 as (P2 & L2 & f2 & E2).
split; [exact (Permutation_trans P2 P1)|]. split; [congruence|].
exists f2. rewrite E2, E1. apply set_fs_set_fs.
Qed.
