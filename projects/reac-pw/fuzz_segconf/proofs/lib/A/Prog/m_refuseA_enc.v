(* reac-pw/fuzz_segconf, image A: pure byte, encoding and printf-text lemmas for the walk of m_refuse
   (fuzz_segconf.c:101-111). No machine state and no function of the binary is proved here: the walk (lane
   the m_refuse walk lane) uses these lemmas at its return to prove the mconf post.
   - mr_text: the text m_refuse keeps, SegModel's snprintf_s of the two formats.
   - mr_reading_at: the reading field of a struct mconf through the reader, with its byte bounds.
   - mr_text_ok: the kept text is NUL-free and at most 111 bytes.
   - mr_pf_line / mr_pf_noline: RtPFPf's parser and renderer give SegModel's fmt text for the two formats.
   - mr_sn_text: the bytes snprintf(d, 112, F, ...) leaves at d are the kept text and its NUL.
   - mr_enc_lt8 / mr_enc_ge8: the struct mconf after m_refuse, from the bytes the walk wrote.
   New text, written for the m_refuse walk lane (brief m_refuse-enc.md (sha256 95b4e5b05414)). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YN2e.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFPf RtPFShared RtPFCmd.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================ list and byte helpers ================================ *)
Lemma mr_in_firstn : forall (A : Type) n (l : list A) x, In x (firstn n l) -> In x l.
Proof.
intros A n; induction n as [|n IH]; intros l x H; [destruct H|].
destruct l as [|y l]; [destruct H|]. cbn [firstn In] in H.
destruct H as [H|H]; [left; exact H | right; exact (IH l x H)].
Qed.

Lemma mr_len_fld : forall off n bs, (off + n <= length bs)%nat -> length (seg_spec.fld off n bs) = n.
Proof. intros off n bs H. unfold seg_spec.fld. rewrite length_firstn, length_skipn. lia. Qed.

Lemma mr_nth_fld : forall off n bs i (d : byte), (i < n)%nat ->
  nth i (seg_spec.fld off n bs) d = nth (off + i) bs d.
Proof.
intros off n bs i d H. unfold seg_spec.fld. rewrite nth_firstn.
destruct (Nat.ltb_spec i n); [|lia]. apply nth_skipn.
Qed.

Lemma mr_len_zs : forall l, length (seg_spec.zs l) = length l.
Proof. intros l. unfold seg_spec.zs. apply length_map. Qed.

Lemma mr_nth_zs : forall l k, nth k (seg_spec.zs l) 0 = bv_unsigned (nth k l ZB0).
Proof.
intros l k. unfold seg_spec.zs.
transitivity (nth k (map bv_unsigned l) (bv_unsigned ZB0)); [reflexivity | apply map_nth].
Qed.

Lemma mr_bv8 : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof. intros x H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma mr_bv_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.

Lemma mr_nth_range : forall (l : list Z) k, (forall x, In x l -> 0 <= x < 256) -> 0 <= nth k l 0 < 256.
Proof.
intros l k H. destruct (Nat.lt_ge_cases k (length l)) as [Hk|Hk].
- apply H, nth_In, Hk.
- rewrite nth_overflow by exact Hk. lia.
Qed.

Lemma mr_le4_len : forall v, length (Mem.le4 v) = 4%nat.
Proof. intros v. reflexivity. Qed.

(* the k-th byte of a u32 field's encoding has unsigned value YG0f.le_byte v 4 k *)
Lemma mr_le4_nth : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold Mem.le4.
pose proof (YN2e.Z_to_le_bytes_nth 4 (bv_unsigned (Z_to_bv 64 v)) k Hk) as E.
apply nth_error_nth with (d := ZB0) in E. rewrite E.
rewrite (Z_to_bv_unsigned 64 v), (bv_wrap_small 64 v) by (change (bv_modulus 64) with (2 ^ 64); lia).
rewrite Z_to_bv_unsigned. unfold le_byte.
rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 4))) by (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia).
change (bv_wrap 8 ?x) with (x mod 2 ^ 8). reflexivity.
Qed.

(* ================================ decimal text ================================ *)
Lemma mr_dec_pf : forall n x acc f g, 0 <= x < 10 ^ Z.of_nat (S n) -> (n <= f)%nat -> (n <= g)%nat ->
  dec_go (S f) x acc = RtPFPf.pf_digits (S g) x acc.
Proof.
induction n as [|n IH]; intros x acc f g Hx Hf Hg.
- change (10 ^ Z.of_nat 1) with 10 in Hx. cbn [dec_go RtPFPf.pf_digits].
  destruct (Z.ltb_spec x 10); [|lia]. rewrite Z.mod_small by lia. reflexivity.
- cbn [dec_go RtPFPf.pf_digits]. destruct (Z.ltb_spec x 10).
  + rewrite Z.mod_small by lia. reflexivity.
  + destruct f as [|f]; [lia|]. destruct g as [|g]; [lia|].
    apply IH; [|lia|lia]. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia. lia.
Qed.

Lemma mr_dec_eq : forall line, 0 <= line <= 65536 -> dec line = RtPFPf.pf_dec line.
Proof.
intros line H. unfold dec, RtPFPf.pf_dec. destruct (Z.ltb_spec line 0); [lia|].
apply (mr_dec_pf 4); [change (10 ^ Z.of_nat 5) with 100000; lia | lia | lia].
Qed.

Lemma mr_dec_go_range : forall f n acc x, (forall y, In y acc -> 0 <= y < 256) ->
  In x (dec_go f n acc) -> 0 <= x < 256.
Proof.
induction f as [|f IH]; intros n acc x Hacc Hx; cbn [dec_go] in Hx; [auto|].
assert (Hacc' : forall y, In y ((48 + n mod 10) :: acc) -> 0 <= y < 256).
{ intros y [<-|Hy]; [pose proof (Z.mod_pos_bound n 10); lia | auto]. }
revert Hx. destruct (n <? 10); intros Hx; [exact (Hacc' x Hx) | exact (IH _ _ x Hacc' Hx)].
Qed.

Lemma mr_dec_range : forall z x, In x (dec z) -> 0 <= x < 256.
Proof.
intros z x. unfold dec. destruct (z <? 0); intros Hx.
- destruct Hx as [<-|Hx]; [lia|]. eapply mr_dec_go_range; [|exact Hx]. intros y [].
- eapply mr_dec_go_range; [|exact Hx]. intros y [].
Qed.

Lemma mr_nulfree_dec : forall l, forallb (fun x => negb (x =? 0)) l = true -> nulfree l.
Proof. intros l H Hin. rewrite forallb_forall in H. specialize (H 0 Hin). cbn in H. discriminate H. Qed.

(* ================================ the kept text ================================ *)
Definition mr_text (mc : mconf) (line : Z) : list Z :=
  if 0 <? line then snprintf_s 112 F_addr_line [AS (mc_reading mc); AI line]
  else snprintf_s 112 F_addr [AS (mc_reading mc)].

(* the reading field: its bytes and NUL through the reader, nonzero bytes, shorter than 96 *)
Lemma mr_reading_at : forall (rd : reader) c bs knock mc,
  sa_bytes rd c bs -> seg_spec.mconf_encp knock mc bs ->
  (forall i, 0 <= i <= Z.of_nat (length (mc_reading mc)) ->
     rd (c + seg_spec.MC_READING + i) = Some (nth (Z.to_nat i) (mc_reading mc ++ [0]) 0)) /\
  Forall (fun x => 0 < x < 256) (mc_reading mc) /\ (length (mc_reading mc) < 96)%nat.
Proof.
intros rd c bs knock mc Hb Henc.
destruct Henc as (Hlen & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrd).
destruct Hrd as (Hfl & Hsl & Hs0 & Hsf).
assert (Hnth : forall k, (k < S (length (mc_reading mc)))%nat ->
  nth k (mc_reading mc ++ [0]) 0 = bv_unsigned (nth (Z.to_nat seg_spec.MC_READING + k) bs ZB0)).
{ intros k Hk. rewrite <- Hsf. rewrite nth_firstn.
  destruct (Nat.ltb_spec k (S (length (mc_reading mc)))); [|lia].
  rewrite mr_nth_zs. unfold seg_spec.fldz. rewrite mr_nth_fld by lia. reflexivity. }
split; [|split; [|exact Hsl]].
- intros i Hi. rewrite (Hnth (Z.to_nat i)) by lia.
  assert (Hj : (Z.to_nat seg_spec.MC_READING + Z.to_nat i < length bs)%nat).
  { unfold seg_spec.SEG_M_SIZE in Hlen. unfold seg_spec.MC_READING. lia. }
  rewrite <- (Hb _ Hj). f_equal. unfold seg_spec.MC_READING. lia.
- apply Forall_forall. intros x Hx.
  assert (Hin : In x (seg_spec.zs (seg_spec.fldz seg_spec.MC_READING 96 bs))).
  { apply (mr_in_firstn _ (S (length (mc_reading mc)))). rewrite Hsf. apply in_or_app. left. exact Hx. }
  unfold seg_spec.zs in Hin. apply in_map_iff in Hin. destruct Hin as (b & Hbx & _).
  pose proof (mr_bv_range b). assert (x <> 0) by (intros ->; contradiction). lia.
Qed.

(* the kept text: NUL-free, at most 111 bytes *)
Lemma mr_text_ok : forall bs knock mc line, seg_spec.mconf_encp knock mc bs ->
  ~ In 0 (mr_text mc line) /\ (length (mr_text mc line) <= 111)%nat.
Proof.
intros bs knock mc line _. unfold mr_text. destruct (0 <? line); split.
- refine (snprintf_nulfree _ _ _ _). apply mr_nulfree_dec. vm_compute. reflexivity.
- unfold snprintf_s. rewrite length_firstn. change (Z.to_nat (112 - 1)) with 111%nat. lia.
- refine (snprintf_nulfree _ _ _ _). apply mr_nulfree_dec. vm_compute. reflexivity.
- unfold snprintf_s. rewrite length_firstn. change (Z.to_nat (112 - 1)) with 111%nat. lia.
Qed.

(* every byte of the kept text and its NUL is below 256 *)
Lemma mr_text_range : forall mc line, Forall (fun x => 0 < x < 256) (mc_reading mc) ->
  forall x, In x (mr_text mc line ++ [0]) -> 0 <= x < 256.
Proof.
intros mc line Hr x Hx. apply in_app_or in Hx. destruct Hx as [Hx|[<-|[]]]; [|lia].
rewrite Forall_forall in Hr.
assert (Hnr : ~ In 0 (mc_reading mc)) by (intros H0; specialize (Hr 0 H0); lia).
unfold mr_text, snprintf_s in Hx. revert Hx. destruct (0 <? line); intros Hx; apply mr_in_firstn in Hx.
- rewrite fmt_addr_line, cut_nul_id in Hx by exact Hnr.
  rewrite !in_app_iff in Hx. destruct Hx as [Hx|[Hx|[Hx|Hx]]].
  + specialize (Hr x Hx). lia.
  + destruct Hx as [<-|[]]. lia.
  + exact (mr_dec_range _ _ Hx).
  + destruct Hx as [<-|[<-|[]]]; lia.
- rewrite fmt_addr, cut_nul_id in Hx by exact Hnr. rewrite !in_app_iff in Hx.
  destruct Hx as [Hx|Hx]; [specialize (Hr x Hx); lia|].
  destruct Hx as [<-|[<-|[]]]; lia.
Qed.

(* the snprintf contract's text for the two formats (RtPFPf's parser and renderer), as SegModel's fmt *)
Lemma mr_pf_line : forall (r : list Z) line, ~ In 0 r -> 0 < line <= 65536 ->
  exists ps, RtPFPf.pf_parse F_addr_line = Some ps /\ Forall RtPFCmd.pf_cmd_piece ps /\
  RtPFShared.pf_prec_pos ps [RtPFPf.APtr r; RtPFPf.AInt line] /\
  RtPFPf.pf_text ps [RtPFPf.APtr r; RtPFPf.AInt line] = Some (fmt F_addr_line [AS r; AI line]).
Proof.
intros r line Hr Hl.
exists [RtPFPf.Ps; RtPFPf.PLit 58; RtPFPf.Pd; RtPFPf.PLit 58; RtPFPf.PLit 32].
split; [vm_compute; reflexivity|]. split; [apply RtPFCmd.pf_cmd_piece_all|]. split; [exact I|].
rewrite fmt_addr_line, cut_nul_id by exact Hr. rewrite (mr_dec_eq line) by lia. reflexivity.
Qed.
Lemma mr_pf_noline : forall (r : list Z), ~ In 0 r ->
  exists ps, RtPFPf.pf_parse F_addr = Some ps /\ Forall RtPFCmd.pf_cmd_piece ps /\
  RtPFShared.pf_prec_pos ps [RtPFPf.APtr r] /\
  RtPFPf.pf_text ps [RtPFPf.APtr r] = Some (fmt F_addr [AS r]).
Proof.
intros r Hr.
exists [RtPFPf.Ps; RtPFPf.PLit 58; RtPFPf.PLit 32].
split; [vm_compute; reflexivity|]. split; [apply RtPFCmd.pf_cmd_piece_all|]. split; [exact I|].
rewrite fmt_addr, cut_nul_id by exact Hr. reflexivity.
Qed.
(* what snprintf(d, 112, F, ...) leaves at d, as the kept text and its NUL *)
Lemma mr_sn_text : forall mc line,
  RtPFShared.sn_bytes (112 - 1) (if 0 <? line then fmt F_addr_line [AS (mc_reading mc); AI line]
                                  else fmt F_addr [AS (mc_reading mc)]) = mr_text mc line ++ [0] /\
  RtPFShared.sn_len (112 - 1) (if 0 <? line then fmt F_addr_line [AS (mc_reading mc); AI line]
                                else fmt F_addr [AS (mc_reading mc)]) = Z.of_nat (length (mr_text mc line)) + 1.
Proof.
intros mc line. unfold RtPFShared.sn_len, RtPFShared.sn_bytes, mr_text, snprintf_s.
destruct (0 <? line); cbv beta iota; (split; [reflexivity|]); rewrite length_app; cbn [length]; lia.
Qed.

(* ================================ the struct after m_refuse ================================ *)
Lemma mr_m_refuse_lt8 : forall mc line knock, Z.of_nat (length (mc_kept mc)) < 8 ->
  m_refuse mc line knock = MConf (mc_seg mc) (mc_overflow mc) (mc_refused mc + 1)
    (mc_kept mc ++ [(mr_text mc line, knock)]) (mc_gen mc) (mc_reading mc).
Proof. intros mc line knock H. unfold m_refuse, mr_text. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.

Lemma mr_m_refuse_ge8 : forall mc line knock, 8 <= Z.of_nat (length (mc_kept mc)) ->
  m_refuse mc line knock = MConf (mc_seg mc) (mc_overflow mc) (mc_refused mc + 1)
    (mc_kept mc) (mc_gen mc) (mc_reading mc).
Proof. intros mc line knock H. unfold m_refuse. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.

(* the byte list after a write: g z is the new byte at offset z, None where the old byte stays *)
Definition mr_upd (bs : list byte) (g : Z -> option byte) : list byte :=
  map (fun j => match g (Z.of_nat j) with Some b => b | None => nth j bs ZB0 end) (seq 0 (length bs)).

Lemma mr_upd_len : forall bs g, length (mr_upd bs g) = length bs.
Proof. intros bs g. unfold mr_upd. rewrite length_map, length_seq. reflexivity. Qed.

Lemma mr_nth_map_seq : forall (f : nat -> byte) m j, (j < m)%nat -> nth j (map f (seq 0 m)) ZB0 = f j.
Proof.
intros f m j H.
assert (E : nth j (map f (seq 0 m)) ZB0 = nth j (map f (seq 0 m)) (f 0%nat))
  by (apply nth_indep; rewrite length_map, length_seq; exact H).
rewrite E.
rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Lemma mr_upd_nth : forall bs g j, (j < length bs)%nat ->
  nth j (mr_upd bs g) ZB0 = match g (Z.of_nat j) with Some b => b | None => nth j bs ZB0 end.
Proof.
intros bs g j H. unfold mr_upd.
exact (mr_nth_map_seq (fun j => match g (Z.of_nat j) with Some b => b | None => nth j bs ZB0 end)
         (length bs) j H).
Qed.

Lemma mr_upd_keep : forall bs g off n, (off + n <= length bs)%nat ->
  (forall j, (off <= j < off + n)%nat -> g (Z.of_nat j) = None) ->
  seg_spec.fld off n (mr_upd bs g) = seg_spec.fld off n bs.
Proof.
intros bs g off n Hn Hg. apply nth_ext with (d := ZB0) (d' := ZB0).
- rewrite !mr_len_fld by (rewrite ?mr_upd_len; lia). reflexivity.
- intros k Hk. rewrite mr_len_fld in Hk by (rewrite mr_upd_len; lia).
  rewrite !mr_nth_fld by exact Hk. rewrite mr_upd_nth by lia. rewrite Hg by lia. reflexivity.
Qed.

Lemma mr_upd_set : forall bs g off l, (off + length l <= length bs)%nat ->
  (forall k, (k < length l)%nat -> g (Z.of_nat (off + k)) = Some (nth k l ZB0)) ->
  seg_spec.fld off (length l) (mr_upd bs g) = l.
Proof.
intros bs g off l Hn Hg. apply nth_ext with (d := ZB0) (d' := ZB0).
- rewrite mr_len_fld by (rewrite mr_upd_len; lia). reflexivity.
- intros k Hk. rewrite mr_len_fld in Hk by (rewrite mr_upd_len; lia).
  rewrite mr_nth_fld by exact Hk. rewrite mr_upd_nth by lia. rewrite Hg by exact Hk. reflexivity.
Qed.

Lemma mr_range_b : forall lo hi z, ((lo <=? z) && (z <? hi)) = true <-> lo <= z < hi.
Proof. intros lo hi z. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. reflexivity. Qed.

Ltac mr_case :=
  match goal with
  | |- context [if (?lo <=? ?z) && (?z <? ?hi) then _ else _] =>
      let E := fresh "E" in
      destruct ((lo <=? z) && (z <? hi)) eqn:E; cbv beta iota;
      [apply mr_range_b in E
      |let N := fresh "N" in
       assert (N : ~ (lo <= z < hi)) by (let H := fresh in intro H; apply mr_range_b in H; congruence);
       clear E]
  end.

Ltac mr_lia :=
  unfold seg_spec.MC_N, seg_spec.MC_OVERFLOW, seg_spec.MC_REFUSED, seg_spec.MC_KEPT, seg_spec.MC_KNOCK,
    seg_spec.MC_NKEPT, seg_spec.MC_GEN, seg_spec.MC_READING, seg_spec.SEG_M_SIZE, seg_spec.kept_addr,
    seg_spec.MC_KEPT_LEN in *; lia.

(* the new bytes of refused (refused + 1) *)
Definition mr_gref (ref z : Z) : option byte :=
  if (seg_spec.MC_REFUSED <=? z) && (z <? seg_spec.MC_REFUSED + 4)
  then Some (nth (Z.to_nat (z - seg_spec.MC_REFUSED)) (Mem.le4 (Z_to_bv 64 (ref + 1))) ZB0) else None.

(* the new bytes when n_kept = n < 8: the text T at kept[n], n_kept = n + 1, refused + 1 *)
Definition mr_g8 (n : nat) (T : list Z) (ref z : Z) : option byte :=
  if (seg_spec.MC_KEPT + 112 * Z.of_nat n <=? z) && (z <? seg_spec.MC_KEPT + 112 * Z.of_nat n + Z.of_nat (length T))
  then Some (Z_to_bv 8 (nth (Z.to_nat (z - (seg_spec.MC_KEPT + 112 * Z.of_nat n))) T 0))
  else if (seg_spec.MC_NKEPT <=? z) && (z <? seg_spec.MC_NKEPT + 4)
  then Some (nth (Z.to_nat (z - seg_spec.MC_NKEPT)) (Mem.le4 (Z_to_bv 64 (Z.of_nat n + 1))) ZB0)
  else mr_gref ref z.

Lemma mr_gref_some : forall ref k, (k < 4)%nat ->
  mr_gref ref (seg_spec.MC_REFUSED + Z.of_nat k) = Some (nth k (Mem.le4 (Z_to_bv 64 (ref + 1))) ZB0).
Proof. intros ref k Hk. unfold mr_gref. mr_case; [|lia]. f_equal. f_equal. lia. Qed.

Lemma mr_g8_text : forall n T ref k, (k < length T)%nat ->
  mr_g8 n T ref (seg_spec.MC_KEPT + 112 * Z.of_nat n + Z.of_nat k) = Some (Z_to_bv 8 (nth k T 0)).
Proof. intros n T ref k Hk. unfold mr_g8. mr_case; [|lia]. f_equal. f_equal. f_equal. lia. Qed.

Lemma mr_g8_nk : forall n T ref k, (n < 8)%nat -> (length T <= 112)%nat -> (k < 4)%nat ->
  mr_g8 n T ref (seg_spec.MC_NKEPT + Z.of_nat k) =
  Some (nth k (Mem.le4 (Z_to_bv 64 (Z.of_nat n + 1))) ZB0).
Proof.
intros n T ref k Hn HT Hk. unfold mr_g8. mr_case; [mr_lia|]. mr_case; [|lia]. f_equal. f_equal. lia.
Qed.

Lemma mr_g8_ref : forall n T ref k, (n < 8)%nat -> (length T <= 112)%nat -> (k < 4)%nat ->
  mr_g8 n T ref (seg_spec.MC_REFUSED + Z.of_nat k) = Some (nth k (Mem.le4 (Z_to_bv 64 (ref + 1))) ZB0).
Proof.
intros n T ref k Hn HT Hk. unfold mr_g8. mr_case; [mr_lia|]. mr_case; [mr_lia|].
apply mr_gref_some. exact Hk.
Qed.

Lemma mr_keep8 : forall bs n T ref off len,
  (off + len <= length bs)%nat ->
  (Z.of_nat (off + len) <= seg_spec.MC_KEPT + 112 * Z.of_nat n \/
   seg_spec.MC_KEPT + 112 * Z.of_nat n + Z.of_nat (length T) <= Z.of_nat off) ->
  (Z.of_nat (off + len) <= seg_spec.MC_NKEPT \/ seg_spec.MC_NKEPT + 4 <= Z.of_nat off) ->
  (Z.of_nat (off + len) <= seg_spec.MC_REFUSED \/ seg_spec.MC_REFUSED + 4 <= Z.of_nat off) ->
  seg_spec.fld off len (mr_upd bs (mr_g8 n T ref)) = seg_spec.fld off len bs.
Proof.
intros bs n T ref off len H0 H1 H2 H3. apply mr_upd_keep; [exact H0|].
intros j Hj. unfold mr_g8, mr_gref. mr_case; [lia|]. mr_case; [lia|]. mr_case; [lia|]. reflexivity.
Qed.

Lemma mr_keepref : forall bs ref off len,
  (off + len <= length bs)%nat ->
  (Z.of_nat (off + len) <= seg_spec.MC_REFUSED \/ seg_spec.MC_REFUSED + 4 <= Z.of_nat off) ->
  seg_spec.fld off len (mr_upd bs (mr_gref ref)) = seg_spec.fld off len bs.
Proof.
intros bs ref off len H0 H1. apply mr_upd_keep; [exact H0|].
intros j Hj. unfold mr_gref. mr_case; [lia|]. reflexivity.
Qed.

(* the block after m_refuse, n_kept < 8: the text and its NUL at kept[n_kept], n_kept + 1, refused + 1, every
   other byte of the 9236 kept; the knock flag of kept[n_kept] was the pending one *)
Lemma mr_enc_lt8 : forall (rd rd' : reader) c bs knock mc line,
  sa_bytes rd c bs -> seg_spec.mconf_encp knock mc bs ->
  mc_refused mc + 1 < 2 ^ 32 -> Z.of_nat (length (mc_kept mc)) < 8 ->
  (forall i, 0 <= i <= Z.of_nat (length (mr_text mc line)) ->
     rd' (seg_spec.kept_addr c (length (mc_kept mc)) + i) = Some (nth (Z.to_nat i) (mr_text mc line ++ [0]) 0)) ->
  sa_val rd' (c + seg_spec.MC_NKEPT) 4 (Z.of_nat (length (mc_kept mc)) + 1) ->
  sa_val rd' (c + seg_spec.MC_REFUSED) 4 (mc_refused mc + 1) ->
  (forall a, c <= a < c + seg_spec.SEG_M_SIZE ->
     ~ (seg_spec.kept_addr c (length (mc_kept mc)) <= a <=
        seg_spec.kept_addr c (length (mc_kept mc)) + Z.of_nat (length (mr_text mc line))) ->
     ~ (c + seg_spec.MC_NKEPT <= a < c + seg_spec.MC_NKEPT + 4) ->
     ~ (c + seg_spec.MC_REFUSED <= a < c + seg_spec.MC_REFUSED + 4) -> rd' a = rd a) ->
  sa_mconf rd' c (m_refuse mc line knock).
Proof.
intros rd rd' c bs knock mc line Hb Henc Hrf Hn8 Htext Hnk Href Hfr.
destruct (mr_text_ok bs knock mc line Henc) as [Hnz Hle].
destruct (mr_reading_at rd c bs knock mc Hb Henc) as (_ & Hrdr & _).
pose proof (mr_text_range mc line Hrdr) as HTr.
assert (HTl : length (mr_text mc line ++ [0]) = S (length (mr_text mc line)))
  by (rewrite length_app; cbn [length]; lia).
destruct Henc as (Hlen & Hsl & Hseg & HN & HO & HR & Hkl & Hkept & Hrest & HNK & HG & HRD).
destruct HR as [HR0 HR].
unfold sa_val in Hnk, Href.
rewrite mr_m_refuse_lt8 by exact Hn8.
unfold sa_mconf, sa_mconfp.
exists (mr_upd bs (mr_g8 (length (mc_kept mc)) (mr_text mc line ++ [0]) (mc_refused mc))). split.
- intros i Hi. rewrite mr_upd_len in Hi. rewrite mr_upd_nth by exact Hi. unfold mr_g8, mr_gref.
  mr_case; [|mr_case; [|mr_case]].
  + replace (c + Z.of_nat i) with (seg_spec.kept_addr c (length (mc_kept mc)) +
      (Z.of_nat i - (seg_spec.MC_KEPT + 112 * Z.of_nat (length (mc_kept mc)))))
      by (unfold seg_spec.kept_addr, seg_spec.MC_KEPT_LEN; lia).
    rewrite Htext by lia.
    rewrite mr_bv8; [reflexivity|]. apply mr_nth_range. exact HTr.
  + replace (c + Z.of_nat i) with (c + seg_spec.MC_NKEPT + Z.of_nat (Z.to_nat (Z.of_nat i - seg_spec.MC_NKEPT)))
      by lia.
    rewrite Hnk by lia. rewrite mr_le4_nth by lia. reflexivity.
  + replace (c + Z.of_nat i) with (c + seg_spec.MC_REFUSED + Z.of_nat (Z.to_nat (Z.of_nat i - seg_spec.MC_REFUSED)))
      by lia.
    rewrite Href by lia. rewrite mr_le4_nth by lia. reflexivity.
  + rewrite Hfr; [exact (Hb i Hi) | | | |].
    * lia.
    * unfold seg_spec.kept_addr, seg_spec.MC_KEPT_LEN. lia.
    * lia.
    * lia.
- unfold seg_spec.mconf_encp. cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  split. { rewrite mr_upd_len. exact Hlen. }
  split. { exact Hsl. }
  split. { intros i Hi. rewrite mr_keep8 by mr_lia. apply Hseg. exact Hi. }
  split. { unfold seg_spec.fldz. rewrite mr_keep8 by mr_lia. exact HN. }
  split. { unfold seg_spec.fldz. rewrite mr_keep8 by mr_lia. exact HO. }
  split.
  { split; [lia|]. unfold seg_spec.fldz.
    change (Z.to_nat 4) with (length (Mem.le4 (Z_to_bv 64 (mc_refused mc + 1)))).
    apply mr_upd_set; rewrite ?mr_le4_len; [mr_lia|].
    intros k Hk. replace (Z.of_nat (Z.to_nat seg_spec.MC_REFUSED + k)) with (seg_spec.MC_REFUSED + Z.of_nat k)
      by mr_lia.
    apply mr_g8_ref; lia. }
  split. { rewrite length_app. cbn [length]. lia. }
  split.
  { intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i (length (mc_kept mc))) as [Hlt|Hge].
    - rewrite app_nth1 by exact Hlt. rewrite !mr_keep8 by mr_lia. apply Hkept. exact Hlt.
    - assert (Hi' : i = length (mc_kept mc)) by lia. subst i. rewrite nth_middle. cbn [fst snd]. split.
      + split; [rewrite mr_len_fld; [reflexivity | rewrite mr_upd_len; mr_lia]|].
        split; [lia|]. split; [exact Hnz|].
        apply nth_ext with (d := 0) (d' := 0).
        * rewrite length_firstn, mr_len_zs, mr_len_fld by (rewrite mr_upd_len; mr_lia).
          rewrite length_app. cbn [length]. lia.
        * intros k Hk. rewrite length_firstn, mr_len_zs, mr_len_fld in Hk by (rewrite mr_upd_len; mr_lia).
          rewrite nth_firstn. destruct (Nat.ltb_spec k (S (length (mr_text mc line)))) as [Hk'|Hk']; [|lia].
          rewrite mr_nth_zs, mr_nth_fld by lia. rewrite mr_upd_nth by mr_lia.
          replace (Z.of_nat (Z.to_nat seg_spec.MC_KEPT + 112 * length (mc_kept mc) + k))
            with (seg_spec.MC_KEPT + 112 * Z.of_nat (length (mc_kept mc)) + Z.of_nat k) by mr_lia.
          rewrite mr_g8_text by lia. apply mr_bv8. apply mr_nth_range. exact HTr.
      + rewrite mr_keep8 by mr_lia. specialize (Hrest (length (mc_kept mc)) ltac:(lia)).
        rewrite Nat.eqb_refl, andb_true_r in Hrest. exact Hrest. }
  split.
  { intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. cbn [andb].
    rewrite mr_keep8 by mr_lia. specialize (Hrest i ltac:(lia)).
    replace (i =? length (mc_kept mc))%nat with false in Hrest by (symmetry; apply Nat.eqb_neq; lia).
    rewrite andb_false_r in Hrest. exact Hrest. }
  split.
  { rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
    split; [lia|]. unfold seg_spec.fldz.
    change (Z.to_nat 4) with (length (Mem.le4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc)) + 1)))).
    apply mr_upd_set; rewrite ?mr_le4_len; [mr_lia|].
    intros k Hk. replace (Z.of_nat (Z.to_nat seg_spec.MC_NKEPT + k)) with (seg_spec.MC_NKEPT + Z.of_nat k)
      by mr_lia.
    apply mr_g8_nk; lia. }
  split. { unfold seg_spec.fldz. rewrite mr_keep8 by mr_lia. exact HG. }
  { unfold seg_spec.fldz. rewrite mr_keep8 by mr_lia. exact HRD. }
Qed.

(* the block after m_refuse, n_kept = 8: refused + 1, every other byte kept *)
Lemma mr_enc_ge8 : forall (rd rd' : reader) c bs knock mc line,
  sa_bytes rd c bs -> seg_spec.mconf_encp knock mc bs ->
  mc_refused mc + 1 < 2 ^ 32 -> 8 <= Z.of_nat (length (mc_kept mc)) ->
  sa_val rd' (c + seg_spec.MC_REFUSED) 4 (mc_refused mc + 1) ->
  (forall a, c <= a < c + seg_spec.SEG_M_SIZE ->
     ~ (c + seg_spec.MC_REFUSED <= a < c + seg_spec.MC_REFUSED + 4) -> rd' a = rd a) ->
  sa_mconf rd' c (m_refuse mc line knock).
Proof.
intros rd rd' c bs knock mc line Hb Henc Hrf Hn8 Href Hfr.
destruct Henc as (Hlen & Hsl & Hseg & HN & HO & HR & Hkl & Hkept & Hrest & HNK & HG & HRD).
destruct HR as [HR0 HR].
unfold sa_val in Href.
rewrite mr_m_refuse_ge8 by exact Hn8.
unfold sa_mconf, sa_mconfp.
exists (mr_upd bs (mr_gref (mc_refused mc))). split.
- intros i Hi. rewrite mr_upd_len in Hi. rewrite mr_upd_nth by exact Hi. unfold mr_gref.
  mr_case.
  + replace (c + Z.of_nat i) with (c + seg_spec.MC_REFUSED + Z.of_nat (Z.to_nat (Z.of_nat i - seg_spec.MC_REFUSED)))
      by lia.
    rewrite Href by lia. rewrite mr_le4_nth by lia. reflexivity.
  + rewrite Hfr; [exact (Hb i Hi) | lia | lia].
- unfold seg_spec.mconf_encp. cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  split. { rewrite mr_upd_len. exact Hlen. }
  split. { exact Hsl. }
  split. { intros i Hi. rewrite mr_keepref by mr_lia. apply Hseg. exact Hi. }
  split. { unfold seg_spec.fldz. rewrite mr_keepref by mr_lia. exact HN. }
  split. { unfold seg_spec.fldz. rewrite mr_keepref by mr_lia. exact HO. }
  split.
  { split; [lia|]. unfold seg_spec.fldz.
    change (Z.to_nat 4) with (length (Mem.le4 (Z_to_bv 64 (mc_refused mc + 1)))).
    apply mr_upd_set; rewrite ?mr_le4_len; [mr_lia|].
    intros k Hk. replace (Z.of_nat (Z.to_nat seg_spec.MC_REFUSED + k)) with (seg_spec.MC_REFUSED + Z.of_nat k)
      by mr_lia.
    apply mr_gref_some. exact Hk. }
  split. { exact Hkl. }
  split. { intros i Hi. rewrite !mr_keepref by mr_lia. apply Hkept. exact Hi. }
  split. { intros i Hi. exfalso. lia. }
  split. { unfold seg_spec.fldz. rewrite mr_keepref by mr_lia. exact HNK. }
  split. { unfold seg_spec.fldz. rewrite mr_keepref by mr_lia. exact HG. }
  { unfold seg_spec.fldz. rewrite mr_keepref by mr_lia. exact HRD. }
Qed.

Print Assumptions mr_enc_lt8.
Print Assumptions mr_enc_ge8.
Print Assumptions mr_pf_line.
Print Assumptions mr_pf_noline.
Print Assumptions mr_sn_text.
Print Assumptions mr_reading_at.
Print Assumptions mr_text_ok.
