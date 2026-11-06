(* Modified by Theorem Labs, 2026-10-30: copied for image B (fuzz_segconf.asan-ubsan) from lib/A/Prog/refuse_f.v at commit 781e28832d34 (a sub-lane, commit 31d252516fb7) by the image-B refuse walk lane of the image-B G3 walk owner: Require paths only: image B's kit copies lib/B/YG0f, YG0n and contract base lib/B/Prog/SegABase.v (the unit owner 694f3575dda2, name map the B-kit name map); the file names no image number. *)
(* reac-pw/fuzz_segconf, ASan image A: the functional lemmas of refuse's walk (a sub-lane of the image-A refuse walk lane,
   the image-A G3 walk owner, 2026-10-30). Proves no function of the binary: these are facts of the model (lib/Spec/SegModel.v
   refuse, r_where, r_addr_fmt, r_addr_args, fmt) and of the encoding (lib/Prog/seg_spec.v rconf_enc, cstr_enc,
   u32_enc) read through a reader (lib/A/Prog/SegABase.v sa_rconf, sa_bytes, sa_zs, sa_str), stated over an
   abstract `rd : reader` so that refuse's symbolic walk (the image-A refuse walk lane) instantiates them at each state.

   Sources. refuse is reac_segconf.c:30-48: refused++; n_refusals >= 8 returns; dst = c->refusal[n]
   (c + 0x2e88 + 200 n); where = c->reading[0] ? c->reading : "reac-pw.conf"; k = snprintf(dst, 200,
   line > 0 ? "%s:%d: " : "%s: ", where[, line]); (unsigned) k > 199 returns; vsnprintf(dst + k, 200 - k, fmt, ap);
   n_refusals++. The arguments are those of the unit owner's plain walk of refuse (enc_refd, enc_kept, reading_facts,
   where_facts, dec_len10, fmt_addr_facts, KP_facts, refuse_kept, refuse_formats_ok, fmt_byte_n),
   restated here over readers and pure lists. The written bytes of a struct are read back as a list through
   [rf_view] (the bytes the new reader holds at c .. c + 16616), so each update lemma is a pointwise argument.

   What the file gives:
   - rf_nref_le, rf_rd_nref, rf_rd_refd, rf_rd_rd0, rf_rd_byte: what refuse loads of c;
   - rf_reading, rf_where: the C string `where` that the address snprintf reads;
   - rf_upd_refd, rf_upd_slot: sa_rconf after `refused++` alone, and after the slot, n_refusals and refused;
   - rf_refuse_ge8, rf_T1, rf_refuse_lt8: SegModel.refuse's two cases, with the address prefix T1;
   - rf_txt: the text facts of the vsnprintf text of each of refuse's 19 formats;
   - rf_sw_inc: the low four bytes of `lw` + 1 stored with `sw`. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Local Notation BYTE := (fun x : Z => 0 <= x < 256).
Local Notation PBYTE := (fun x : Z => 0 < x < 256).
(* the address prefix refuse's first snprintf prints *)
Local Notation T1 rcs ln := (SegModel.fmt (SegModel.r_addr_fmt ln) (SegModel.r_addr_args rcs ln)).

(* refusal_addr first: its body names RC_REFUSAL and RC_REFUSAL_LEN, which the later names then unfold *)
Ltac rf_lia :=
  unfold seg_spec.refusal_addr, seg_spec.SEG_C_SIZE, seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN,
    seg_spec.RC_NREF, seg_spec.RC_REFUSED, seg_spec.RC_OVERFLOW, seg_spec.RC_READING, seg_spec.RC_GEN in *;
  lia.

(* ===================================== lists and bytes ===================================== *)
Lemma rf_nth_firstn : forall {A} n (l : list A) k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  intros A n. induction n as [|n IH]; intros l k d Hk; [lia|].
  destruct l as [|x l]; [destruct k; reflexivity|]. cbn [firstn].
  destruct k as [|k]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

Lemma rf_nth_skipn : forall {A} m (l : list A) k d, nth k (skipn m l) d = nth (m + k) l d.
Proof.
  intros A m. induction m as [|m IH]; intros l k d; [reflexivity|].
  destruct l as [|x l]; [destruct k; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma rf_nth_fld : forall (l : list byte) off n k d, (k < n)%nat -> nth k (fld off n l) d = nth (off + k) l d.
Proof. intros l off n k d Hk. unfold fld. rewrite rf_nth_firstn by exact Hk. apply rf_nth_skipn. Qed.

Lemma rf_len_fld : forall (l : list byte) off n, (off + n <= length l)%nat -> length (fld off n l) = n.
Proof. intros l off n H. unfold fld. rewrite length_firstn, length_skipn. lia. Qed.

Lemma rf_nth_map_seq : forall {A} (f : nat -> A) k n d, (k < n)%nat -> nth k (map f (seq 0 n)) d = f k.
Proof.
  intros A f k n d Hk. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma rf_Forall_firstn : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n. induction n as [|n IH]; intros l H; [constructor|].
  destruct l as [|x l]; [constructor|]. inversion H; subst. cbn [firstn]. constructor; auto.
Qed.

Lemma rf_byte_rt : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply Z_to_bv_bv_unsigned. Qed.

Lemma rf_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.

Lemma rf_unsigned_small : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small, Hz. Qed.

Lemma rf_le_byte_range : forall v w k, 0 <= le_byte v w k < 256.
Proof. intros v w k. unfold le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma rf_nth_byte : forall l k, Forall BYTE l -> 0 <= nth k l 0 < 256.
Proof.
  intros l k H. destruct (nth_in_or_default k l 0) as [Hin|Hd].
  - exact (proj1 (Forall_forall _ _) H _ Hin).
  - rewrite Hd. lia.
Qed.

Lemma rf_pos : forall l, Forall BYTE l -> ~ In 0 l -> Forall PBYTE l.
Proof.
  intros l H Hn. apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ l) H x Hx) as Hb.
  cbv beta in Hb. assert (x <> 0) by (intros ->; exact (Hn Hx)). lia.
Qed.

Lemma rf_byte_forallb : forall l, forallb (fun x => (0 <=? x) && (x <? 256)) l = true -> Forall BYTE l.
Proof.
  induction l as [|x l IH]; intros H; [constructor|]. cbn [forallb] in H.
  apply andb_true_iff in H as [H1 H2]. apply andb_true_iff in H1 as [H0 H1].
  constructor; [apply Z.leb_le in H0; apply Z.ltb_lt in H1; lia | exact (IH H2)].
Qed.

Lemma rf_pos_forallb : forall l, forallb (fun x => (0 <? x) && (x <? 256)) l = true -> Forall PBYTE l.
Proof.
  induction l as [|x l IH]; intros H; [constructor|]. cbn [forallb] in H.
  apply andb_true_iff in H as [H1 H2]. apply andb_true_iff in H1 as [H0 H1].
  constructor; [apply Z.ltb_lt in H0; apply Z.ltb_lt in H1; lia | exact (IH H2)].
Qed.

Lemma rf_in_dec : forall lo hi x : Z, {lo <= x < hi} + {~ (lo <= x < hi)}.
Proof.
  intros lo hi x. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); [left; lia | right; lia ..].
Qed.

(* the four little-endian bytes of a u32 field *)
Lemma rf_nth_Zle : forall n z k, (k < n)%nat -> nth k (Z_to_le_bytes n z) ZB0 = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|]. cbn [Z_to_le_bytes].
  destruct k as [|k]; cbn [nth].
  - replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma rf_le4_nth : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4.
  rewrite rf_nth_Zle by exact Hk.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small v (2 ^ 64)) by lia. unfold le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.

(* ================================ reading a struct through a reader ================================ *)
Lemma rf_rd_fld : forall rd c bs off n k, sa_bytes rd c bs -> 0 <= off ->
  (Z.to_nat off + Z.to_nat n <= length bs)%nat -> (k < Z.to_nat n)%nat ->
  rd (c + off + Z.of_nat k) = Some (bv_unsigned (nth k (fldz off n bs) ZB0)).
Proof.
  intros rd c bs off n k HB Ho Hl Hk. replace (c + off + Z.of_nat k) with (c + Z.of_nat (Z.to_nat off + k)) by lia.
  rewrite HB by lia. unfold fldz. rewrite rf_nth_fld by exact Hk. reflexivity.
Qed.

Lemma rf_rd32_fld : forall rd c bs off v, sa_bytes rd c bs -> 0 <= off -> (Z.to_nat off + 4 <= length bs)%nat ->
  u32_enc v (fldz off 4 bs) -> rd32 rd (c + off) v.
Proof.
  intros rd c bs off v HB Ho Hl [Hv Hf] k Hk.
  rewrite (rf_rd_fld rd c bs off 4 k HB Ho) by lia. f_equal.
  rewrite <- (rf_le4_nth v k Hv Hk), <- Hf. reflexivity.
Qed.

Lemma rf_cstr_nth : forall cap s f k, cstr_enc cap s f -> (k <= length s)%nat ->
  bv_unsigned (nth k f ZB0) = nth k (s ++ [0]) 0.
Proof.
  intros cap s f k (Hl & Hs & Hn & Hf) Hk. rewrite <- Hf. rewrite rf_nth_firstn by lia. unfold zs.
  rewrite (nth_indep (map bv_unsigned f) 0 (bv_unsigned ZB0)) by (rewrite length_map; lia).
  rewrite map_nth. reflexivity.
Qed.

Lemma rf_cstr_pos : forall cap s f, cstr_enc cap s f -> Forall PBYTE s.
Proof.
  intros cap s f (Hl & Hs & Hn & Hf).
  assert (Hz : Forall BYTE (s ++ [0])).
  { rewrite <- Hf. apply rf_Forall_firstn. unfold zs. apply Forall_forall. intros x Hx.
    apply in_map_iff in Hx as (b & <- & _). apply rf_byte_range. }
  apply Forall_app in Hz as [Hz _]. apply rf_pos; assumption.
Qed.

(* 1. *)
Lemma rf_nref_le : forall rcs bs, seg_spec.rconf_enc rcs bs -> (length (rc_refusal rcs) <= 23)%nat.
Proof. intros rcs bs HE. destruct HE as (_ & _ & _ & _ & Hrl & _). lia. Qed.

(* 2. *)
Lemma rf_rd_nref : forall rd c rcs, sa_rconf rd c rcs ->
  rd32 rd (c + seg_spec.RC_NREF) (Z.of_nat (length (rc_refusal rcs))).
Proof.
  intros rd c rcs (bs & HB & HE). destruct HE as (HL & _ & _ & _ & _ & _ & Hnref & _).
  apply (rf_rd32_fld rd c bs); [exact HB | rf_lia | rf_lia | exact Hnref].
Qed.

Lemma rf_rd_refd : forall rd c rcs, sa_rconf rd c rcs -> rd32 rd (c + seg_spec.RC_REFUSED) (rc_refused rcs).
Proof.
  intros rd c rcs (bs & HB & HE). destruct HE as (HL & _ & _ & _ & _ & _ & _ & Hrefd & _).
  apply (rf_rd32_fld rd c bs); [exact HB | rf_lia | rf_lia | exact Hrefd].
Qed.

Lemma rf_rd_rd0 : forall rd c rcs, sa_rconf rd c rcs ->
  rd (c + seg_spec.RC_READING) = Some (SegModel.hd0 (rc_reading rcs)).
Proof.
  intros rd c rcs (bs & HB & HE). destruct HE as (HL & _ & _ & _ & _ & _ & _ & _ & _ & Hrd & _).
  replace (c + RC_READING) with (c + RC_READING + Z.of_nat 0) by lia.
  rewrite (rf_rd_fld rd c bs RC_READING 96 0 HB) by rf_lia. f_equal.
  rewrite (rf_cstr_nth 96 (rc_reading rcs) _ 0 Hrd) by lia. destruct (rc_reading rcs); reflexivity.
Qed.

Lemma rf_rd_byte : forall rd c rcs i, sa_rconf rd c rcs -> 0 <= i < seg_spec.SEG_C_SIZE ->
  exists v, rd (c + i) = Some v /\ 0 <= v < 256.
Proof.
  intros rd c rcs i (bs & HB & HE) Hi. destruct HE as (HL & _).
  exists (bv_unsigned (nth (Z.to_nat i) bs ZB0)). split; [|apply rf_byte_range].
  replace (c + i) with (c + Z.of_nat (Z.to_nat i)) by lia. apply HB. rf_lia.
Qed.

(* 3. *)
Lemma rf_reading : forall rd c rcs, sa_rconf rd c rcs -> c mod 8 = 0 -> SegModel.hd0 (rc_reading rcs) <> 0 ->
  sa_str rd (c + seg_spec.RC_READING) (rc_reading rcs) /\ (length (rc_reading rcs) <= 95)%nat /\
  Forall (fun x => 0 < x < 256) (rc_reading rcs).
Proof.
  intros rd c rcs (bs & HB & HE) Hc _. destruct HE as (HL & _ & _ & _ & _ & _ & _ & _ & _ & Hrd & _).
  pose proof (rf_cstr_pos _ _ _ Hrd) as Hpos. pose proof Hrd as (Hl & Hs & Hn & _).
  split; [|split; [lia | exact Hpos]].
  split; [split; [|exact Hn]|].
  - intros k Hk. rewrite length_app in Hk. cbn [length] in Hk.
    rewrite (rf_rd_fld rd c bs RC_READING 96 k HB) by rf_lia. f_equal.
    apply (rf_cstr_nth 96 _ _ k Hrd). lia.
  - intros x Hx.
    assert (Hx' : 0 <= x - c < SEG_C_SIZE).
    { unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *. Z.div_mod_to_equations. lia. }
    replace x with (c + Z.of_nat (Z.to_nat (x - c))) by lia. rewrite HB by rf_lia. discriminate.
Qed.

Lemma rf_where : forall rcs bs, seg_spec.rconf_enc rcs bs -> (length (SegModel.r_where rcs) <= 95)%nat /\
  ~ In 0 (SegModel.r_where rcs) /\ Forall (fun x => 0 < x < 256) (SegModel.r_where rcs).
Proof.
  intros rcs bs HE. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrd & _).
  pose proof (rf_cstr_pos _ _ _ Hrd) as Hb. destruct Hrd as (_ & Hs & Hn & _).
  unfold r_where. destruct (hd0 (rc_reading rcs) =? 0).
  - split; [apply Nat.leb_le; vm_compute; reflexivity|].
    split; [apply (nulfree_forallb S_base); vm_compute; reflexivity | apply rf_pos_forallb; vm_compute; reflexivity].
  - split; [lia|]. split; assumption.
Qed.

(* ============================== writing a struct: the bytes read back ============================== *)
Definition rf_o0 (o : option Z) : Z := match o with Some v => v | None => 0 end.
(* the n bytes the reader rd holds at c .. c + n, as a list *)
Definition rf_view (rd : reader) (c : Z) (n : nat) : list byte :=
  map (fun i => Z_to_bv 8 (rf_o0 (rd (c + Z.of_nat i)))) (seq 0 n).

Lemma rf_view_len : forall rd c n, length (rf_view rd c n) = n.
Proof. intros. unfold rf_view. rewrite length_map, length_seq. reflexivity. Qed.

Lemma rf_view_nth : forall rd c n i, (i < n)%nat ->
  nth i (rf_view rd c n) ZB0 = Z_to_bv 8 (rf_o0 (rd (c + Z.of_nat i))).
Proof. intros rd c n i Hi. unfold rf_view. rewrite rf_nth_map_seq by exact Hi. reflexivity. Qed.

Lemma rf_view_bytes : forall rd c n, (forall i, (i < n)%nat -> exists v, rd (c + Z.of_nat i) = Some v /\ 0 <= v < 256) ->
  sa_bytes rd c (rf_view rd c n).
Proof.
  intros rd c n H i Hi. rewrite rf_view_len in Hi. rewrite rf_view_nth by exact Hi.
  destruct (H i Hi) as (v & Hv & Hr). rewrite Hv. cbn [rf_o0]. rewrite rf_unsigned_small by exact Hr. reflexivity.
Qed.

Lemma rf_view_keep : forall rd rd' c bs i, sa_bytes rd c bs -> (i < length bs)%nat ->
  rd' (c + Z.of_nat i) = rd (c + Z.of_nat i) -> nth i (rf_view rd' c (length bs)) ZB0 = nth i bs ZB0.
Proof.
  intros rd rd' c bs i HB Hi E. rewrite rf_view_nth by exact Hi. rewrite E, HB by exact Hi. cbn [rf_o0].
  apply rf_byte_rt.
Qed.

Lemma rf_fld_ext : forall (l l' : list byte) off n, (off + n <= length l)%nat -> length l' = length l ->
  (forall i, (off <= i < off + n)%nat -> nth i l' ZB0 = nth i l ZB0) -> fld off n l' = fld off n l.
Proof.
  intros l l' off n Hl Hl' H. apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite !rf_len_fld by lia. reflexivity.
  - intros k Hk. rewrite rf_len_fld in Hk by lia. rewrite !rf_nth_fld by exact Hk. apply H. lia.
Qed.

Lemma rf_rd32_byte : forall rd a v k, rd32 rd a v -> (k < 4)%nat -> exists x, rd (a + Z.of_nat k) = Some x /\ 0 <= x < 256.
Proof. intros rd a v k H Hk. exists (le_byte v 4 k). split; [apply H, Hk | apply rf_le_byte_range]. Qed.

Lemma rf_view_u32 : forall rd' c N off v, rd32 rd' (c + off) v -> 0 <= v < 2 ^ 32 -> 0 <= off ->
  (Z.to_nat off + 4 <= N)%nat ->
  fld (Z.to_nat off) (Z.to_nat 4) (rf_view rd' c N) = OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4 (Z_to_bv 64 v).
Proof.
  intros rd' c N off v H Hv Ho Hl. change (Z.to_nat 4) with 4%nat.
  apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite rf_len_fld by (rewrite rf_view_len; lia). reflexivity.
  - intros k Hk. rewrite rf_len_fld in Hk by (rewrite rf_view_len; lia).
    rewrite rf_nth_fld by exact Hk. rewrite rf_view_nth by lia.
    replace (c + Z.of_nat (Z.to_nat off + k)) with (c + off + Z.of_nat k) by lia.
    rewrite (H k Hk). cbn [rf_o0]. apply bv_eq. rewrite (rf_le4_nth v k Hv Hk).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.

(* a new refusal slot: the text and its NUL, the rest of the slot free *)
Lemma rf_cstr_view : forall rd' c N off txt, (off + 200 <= N)%nat -> ~ In 0 txt -> Forall BYTE txt ->
  (length txt < 200)%nat -> sa_zs rd' (c + Z.of_nat off) (txt ++ [0]) -> cstr_enc 200 txt (fld off 200 (rf_view rd' c N)).
Proof.
  intros rd' c N off txt Hl Hn Hb Ht Hz.
  assert (Hb0 : Forall BYTE (txt ++ [0])) by (apply Forall_app; split; [exact Hb | constructor; [cbv beta; lia | constructor]]).
  assert (HF : length (fld off 200 (rf_view rd' c N)) = 200%nat) by (apply rf_len_fld; rewrite rf_view_len; lia).
  split; [exact HF|]. split; [exact Ht|]. split; [exact Hn|].
  apply nth_ext with (d := 0) (d' := 0).
  - rewrite length_firstn, length_app. unfold zs. rewrite length_map, HF. cbn [length]. lia.
  - intros k Hk. rewrite length_firstn in Hk. unfold zs in *. rewrite length_map, HF in Hk.
    rewrite rf_nth_firstn by lia.
    rewrite (nth_indep (map bv_unsigned (fld off 200 (rf_view rd' c N))) 0 (bv_unsigned ZB0))
      by (rewrite length_map, HF; lia).
    rewrite map_nth. rewrite rf_nth_fld by lia. rewrite rf_view_nth by lia.
    replace (c + Z.of_nat (off + k)) with (c + Z.of_nat off + Z.of_nat k) by lia.
    rewrite Hz by (rewrite length_app; cbn [length]; lia).
    cbn [rf_o0]. apply rf_unsigned_small. apply rf_nth_byte. exact Hb0.
Qed.

Ltac rf_keep HB Hk :=
  first [ apply rf_view_len
        | intros ?j ?Hj; apply (rf_view_keep _ _ _ _ _ HB); [rf_lia | apply Hk; rf_lia]
        | rf_lia ].

(* 4. *)
Lemma rf_upd_refd : forall rd rd' c rcs, sa_rconf rd c rcs -> rc_refused rcs + 1 < 2 ^ 32 ->
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_REFUSED <= i < seg_spec.RC_REFUSED + 4) ->
     rd' (c + i) = rd (c + i)) ->
  rd32 rd' (c + seg_spec.RC_REFUSED) (rc_refused rcs + 1) ->
  sa_rconf rd' c (RConf (rc_seg rcs) (rc_refusal rcs) (rc_refused rcs + 1) (rc_overflow rcs) (rc_reading rcs)
                        (rc_gen rcs)).
Proof.
  intros rd rd' c rcs (bs & HB & HE) Hr Hk H32.
  pose proof HE as (HL & Hsl & Hseg & Hn & Hrl & Hrf & Hnref & [Hr0 Hrefd] & Hov & Hrd & Hgen).
  exists (rf_view rd' c (length bs)). split.
  - apply rf_view_bytes. intros i Hi.
    destruct (rf_in_dec RC_REFUSED (RC_REFUSED + 4) (Z.of_nat i)) as [Ha|Ha].
    + replace (c + Z.of_nat i) with (c + RC_REFUSED + Z.of_nat (Z.to_nat (Z.of_nat i - RC_REFUSED))) by lia.
      apply (rf_rd32_byte _ _ _ _ H32). lia.
    + rewrite Hk by rf_lia. rewrite HB by exact Hi. eexists; split; [reflexivity | apply rf_byte_range].
  - unfold seg_spec.rconf_enc, seg_spec.fldz in *. cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen].
    split; [rewrite rf_view_len; exact HL|].
    split; [exact Hsl|].
    split; [intros i Hi; specialize (Hseg i Hi); rewrite (rf_fld_ext bs (rf_view rd' c (length bs))) by rf_keep HB Hk;
            exact Hseg|].
    split; [rewrite (rf_fld_ext bs (rf_view rd' c (length bs))) by rf_keep HB Hk; exact Hn|].
    split; [exact Hrl|].
    split; [intros i Hi; specialize (Hrf i Hi); rewrite (rf_fld_ext bs (rf_view rd' c (length bs))) by rf_keep HB Hk;
            exact Hrf|].
    split; [rewrite (rf_fld_ext bs (rf_view rd' c (length bs))) by rf_keep HB Hk; exact Hnref|].
    split; [split; [lia | apply rf_view_u32; [exact H32 | lia | rf_lia | rf_lia]]|].
    split; [rewrite (rf_fld_ext bs (rf_view rd' c (length bs))) by rf_keep HB Hk; exact Hov|].
    split; [rewrite (rf_fld_ext bs (rf_view rd' c (length bs))) by rf_keep HB Hk; exact Hrd|].
    rewrite (rf_fld_ext bs (rf_view rd' c (length bs))) by rf_keep HB Hk; exact Hgen.
Qed.

(* 5. *)
Lemma rf_upd_slot : forall rd rd' c rcs txt, sa_rconf rd c rcs -> rc_refused rcs + 1 < 2 ^ 32 ->
  (length (rc_refusal rcs) < 8)%nat -> ~ In 0 txt -> Forall (fun x => 0 <= x < 256) txt -> (length txt < 200)%nat ->
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_REFUSED <= i < seg_spec.RC_REFUSED + 4) ->
     ~ (seg_spec.RC_NREF <= i < seg_spec.RC_NREF + 4) ->
     ~ (seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) <= i <
        seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) + Z.of_nat (length txt) + 1) ->
     rd' (c + i) = rd (c + i)) ->
  rd32 rd' (c + seg_spec.RC_REFUSED) (rc_refused rcs + 1) ->
  rd32 rd' (c + seg_spec.RC_NREF) (Z.of_nat (length (rc_refusal rcs)) + 1) ->
  sa_zs rd' (seg_spec.refusal_addr c (length (rc_refusal rcs))) (txt ++ [0]) ->
  sa_rconf rd' c (RConf (rc_seg rcs) (rc_refusal rcs ++ [txt]) (rc_refused rcs + 1) (rc_overflow rcs)
                        (rc_reading rcs) (rc_gen rcs)).
Proof.
  intros rd rd' c rcs txt (bs & HB & HE) Hr Hn8 Htz Htb Htl Hk H32 H32n Hzs.
  pose proof HE as (HL & Hsl & Hseg & Hn & Hrl & Hrf & Hnref & [Hr0 Hrefd] & Hov & Hrd & Hgen).
  assert (Htb0 : Forall BYTE (txt ++ [0])) by (apply Forall_app; split; [exact Htb | constructor; [cbv beta; lia | constructor]]).
  exists (rf_view rd' c (length bs)). split.
  - apply rf_view_bytes. intros i Hi.
    destruct (rf_in_dec RC_REFUSED (RC_REFUSED + 4) (Z.of_nat i)) as [Ha|Ha].
    { replace (c + Z.of_nat i) with (c + RC_REFUSED + Z.of_nat (Z.to_nat (Z.of_nat i - RC_REFUSED))) by lia.
      apply (rf_rd32_byte _ _ _ _ H32). lia. }
    destruct (rf_in_dec RC_NREF (RC_NREF + 4) (Z.of_nat i)) as [Hb|Hb].
    { replace (c + Z.of_nat i) with (c + RC_NREF + Z.of_nat (Z.to_nat (Z.of_nat i - RC_NREF))) by lia.
      apply (rf_rd32_byte _ _ _ _ H32n). lia. }
    destruct (rf_in_dec (RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)))
                (RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) + Z.of_nat (length txt) + 1) (Z.of_nat i))
      as [Hc|Hc].
    { replace (c + Z.of_nat i) with (refusal_addr c (length (rc_refusal rcs)) +
        Z.of_nat (Z.to_nat (Z.of_nat i - (RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs))))))
        by (unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL_LEN; lia).
      rewrite Hzs by (rewrite length_app; cbn [length]; lia).
      eexists; split; [reflexivity | apply rf_nth_byte; exact Htb0]. }
    rewrite Hk by rf_lia. rewrite HB by exact Hi. eexists; split; [reflexivity | apply rf_byte_range].
  - unfold seg_spec.rconf_enc, seg_spec.fldz in *. cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen].
    split; [rewrite rf_view_len; exact HL|].
    split; [exact Hsl|].
    split; [intros i Hi; specialize (Hseg i Hi); rewrite (rf_fld_ext bs (rf_view rd' c (length bs))) by rf_keep HB Hk;
            exact Hseg|].
    split; [rewrite (rf_fld_ext bs (rf_view rd' c (length bs))) by rf_keep HB Hk; exact Hn|].
    split; [rewrite length_app; cbn [length]; lia|].
    split.
    { intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
      destruct (Nat.lt_ge_cases i (length (rc_refusal rcs))) as [Hlt|Hge].
      - rewrite app_nth1 by exact Hlt. specialize (Hrf i Hlt).
        rewrite (rf_fld_ext bs (rf_view rd' c (length bs))) by rf_keep HB Hk. exact Hrf.
      - assert (Ei : i = length (rc_refusal rcs)) by lia. subst i.
        rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
        apply rf_cstr_view; [rf_lia | exact Htz | exact Htb | exact Htl|].
        replace (c + Z.of_nat (Z.to_nat RC_REFUSAL + 200 * length (rc_refusal rcs)))
          with (refusal_addr c (length (rc_refusal rcs))) by rf_lia.
        exact Hzs. }
    split.
    { replace (Z.of_nat (length (rc_refusal rcs ++ [txt]))) with (Z.of_nat (length (rc_refusal rcs)) + 1)
        by (rewrite length_app; cbn [length]; lia).
      split; [lia | apply rf_view_u32; [exact H32n | lia | rf_lia | rf_lia]]. }
    split; [split; [lia | apply rf_view_u32; [exact H32 | lia | rf_lia | rf_lia]]|].
    split; [rewrite (rf_fld_ext bs (rf_view rd' c (length bs))) by rf_keep HB Hk; exact Hov|].
    split; [rewrite (rf_fld_ext bs (rf_view rd' c (length bs))) by rf_keep HB Hk; exact Hrd|].
    rewrite (rf_fld_ext bs (rf_view rd' c (length bs))) by rf_keep HB Hk; exact Hgen.
Qed.

(* ======================================= printf text ======================================= *)
Definition rf_argb (a : arg) : Prop := match a with AS s => Forall BYTE s | AI _ => True end.
(* the arguments refuse's callers give (seg_spec.va_arg_ok, SegABase.sa_va_arg) *)
Definition rf_argok (x : arg) : Prop :=
  match x with
  | AS s => ~ In 0 s /\ Forall (fun v => 0 <= v < 256) s /\ (length s <= 65535)%nat
  | AI z => 0 <= z < 2 ^ 31
  end.

Lemma rf_cut_nul_byte : forall s, Forall BYTE s -> Forall BYTE (cut_nul s).
Proof.
  induction s as [|x s IH]; intros H; cbn [cut_nul]; [constructor|]. inversion H; subst.
  destruct (x =? 0); [constructor | constructor; auto].
Qed.

Lemma rf_dec_go_byte : forall fu n acc, Forall BYTE acc -> Forall BYTE (dec_go fu n acc).
Proof.
  induction fu as [|fu IH]; intros n acc H; cbn [dec_go]; [exact H|].
  assert (Hd : Forall BYTE ((48 + n mod 10) :: acc)).
  { constructor; [|exact H]. pose proof (Z.mod_pos_bound n 10). cbv beta. lia. }
  destruct (n <? 10); [exact Hd | apply IH, Hd].
Qed.

Lemma rf_dec_byte : forall z, Forall BYTE (dec z).
Proof.
  intros z. unfold dec. destruct (z <? 0); [constructor; [cbv beta; lia|]|]; apply rf_dec_go_byte; constructor.
Qed.

Lemma rf_dec_len10 : forall z, 0 <= z < 2 ^ 31 -> (length (dec z) <= 10)%nat.
Proof.
  intros z H. unfold dec. destruct (Z.ltb_spec z 0); [lia|].
  pose proof (dec_go_len 9 20 z [] ltac:(cbn; lia) ltac:(lia)) as Hd. cbn [length] in Hd. lia.
Qed.

Lemma rf_arg_s_byte : forall x, rf_argb x -> Forall BYTE (arg_s x).
Proof. intros [s|z] H; cbn [arg_s rf_argb] in *; [apply rf_cut_nul_byte, H | constructor]. Qed.

Lemma rf_argok_b : forall x, rf_argok x -> rf_argb x.
Proof. intros [s|z] H; cbn [rf_argok rf_argb] in *; [exact (proj1 (proj2 H)) | exact I]. Qed.

Lemma rf_arg_s_len : forall x, rf_argok x -> Z.of_nat (length (arg_s x)) <= 65535.
Proof.
  intros [s|z] H; cbn [arg_s].
  - destruct H as (_ & _ & H). apply Nat2Z.inj_le in H. change (Z.of_nat 65535) with 65535 in H.
    pose proof (cut_nul_len s) as Hc. apply Nat2Z.inj_le in Hc. lia.
  - cbn [length]. lia.
Qed.

Lemma rf_dec_arg_len : forall x, rf_argok x -> Z.of_nat (length (dec (arg_i x))) <= 65535.
Proof.
  intros [s|z] H; cbn [arg_i].
  - pose proof (rf_dec_len10 0 ltac:(lia)). lia.
  - pose proof (rf_dec_len10 z H). lia.
Qed.

Lemma rf_fmt_byte_n : forall n f a, (length f <= n)%nat -> Forall BYTE f -> Forall rf_argb a -> Forall BYTE (fmt f a).
Proof.
  induction n as [|n IH]; intros f a Hl Hf Ha.
  - destruct f; [constructor | cbn in Hl; lia].
  - destruct f as [|c f1]; [constructor|]. inversion Hf as [|? ? Hc Hf1]; subst. cbn [length] in Hl.
    cbn [fmt].
    match goal with |- context [if negb ?b then _ else _] => destruct (negb b) end; cbv beta iota.
    + constructor; [exact Hc | apply IH; auto; lia].
    + destruct f1 as [|c1 f2]; cbv beta iota; [constructor|].
      inversion Hf1 as [|? ? Hc1 Hf2]; subst. cbn [length] in Hl.
      destruct (c1 =? 115); cbv beta iota.
      { destruct a as [|x a']; cbv beta iota; [constructor|]. inversion Ha; subst.
        apply Forall_app; split; [apply rf_arg_s_byte; assumption | apply IH; auto; lia]. }
      destruct ((c1 =? 100) || (c1 =? 117)); cbv beta iota.
      { destruct a as [|x a']; cbv beta iota; [constructor|]. inversion Ha; subst.
        apply Forall_app; split; [apply rf_dec_byte | apply IH; auto; lia]. }
      destruct (c1 =? 122); cbv beta iota.
      { destruct f2 as [|c2 f3]; cbv beta iota; [constructor|].
        inversion Hf2 as [|? ? _ Hf3]; subst. cbn [length] in Hl.
        destruct (c2 =? 117); cbv beta iota; [|constructor].
        destruct a as [|x a']; cbv beta iota; [constructor|]. inversion Ha; subst.
        apply Forall_app; split; [apply rf_dec_byte | apply IH; auto; lia]. }
      destruct (c1 =? 46); cbv beta iota; [|constructor].
      destruct f2 as [|d1 [|d2 [|c3 f4]]]; cbv beta iota; try constructor.
      inversion Hf2 as [|? ? _ Hf2a]; subst. inversion Hf2a as [|? ? _ Hf2b]; subst.
      inversion Hf2b as [|? ? _ Hf4]; subst. cbn [length] in Hl.
      destruct (isdigit d1 && isdigit d2 && (c3 =? 115)); cbv beta iota; [|constructor].
      destruct a as [|x a']; cbv beta iota; [constructor|]. inversion Ha; subst.
      apply Forall_app; split; [apply rf_Forall_firstn, rf_arg_s_byte; assumption | apply IH; auto; lia].
Qed.

(* each conversion consumes at least two format bytes and one argument, and prints at most 65535 bytes *)
Lemma rf_fmt_len : forall n f a, (length f <= n)%nat -> Forall rf_argok a ->
  Z.of_nat (length (fmt f a)) <= Z.of_nat (length f) + 65535 * Z.of_nat (length a).
Proof.
  induction n as [|n IH]; intros f a Hl Ha.
  - destruct f; [cbn [fmt length]; lia | cbn in Hl; lia].
  - destruct f as [|c f1]; [cbn [fmt length]; lia|]. cbn [length] in Hl.
    cbn [fmt].
    match goal with |- context [if negb ?b then _ else _] => destruct (negb b) end; cbv beta iota.
    + cbn [length]. specialize (IH f1 a ltac:(lia) Ha). lia.
    + destruct f1 as [|c1 f2]; cbv beta iota; [cbn [length]; lia|]. cbn [length] in Hl.
      destruct (c1 =? 115); cbv beta iota.
      { destruct a as [|x a']; cbv beta iota; [cbn [length]; lia|]. inversion Ha as [|? ? Hx Ha']; subst.
        pose proof (rf_arg_s_len x Hx). specialize (IH f2 a' ltac:(lia) Ha').
        rewrite length_app. cbn [length]. lia. }
      destruct ((c1 =? 100) || (c1 =? 117)); cbv beta iota.
      { destruct a as [|x a']; cbv beta iota; [cbn [length]; lia|]. inversion Ha as [|? ? Hx Ha']; subst.
        pose proof (rf_dec_arg_len x Hx). specialize (IH f2 a' ltac:(lia) Ha').
        rewrite length_app. cbn [length]. lia. }
      destruct (c1 =? 122); cbv beta iota.
      { destruct f2 as [|c2 f3]; cbv beta iota; [cbn [length]; lia|]. cbn [length] in Hl.
        destruct (c2 =? 117); cbv beta iota; [|cbn [length]; lia].
        destruct a as [|x a']; cbv beta iota; [cbn [length]; lia|]. inversion Ha as [|? ? Hx Ha']; subst.
        pose proof (rf_dec_arg_len x Hx). specialize (IH f3 a' ltac:(lia) Ha').
        rewrite length_app. cbn [length]. lia. }
      destruct (c1 =? 46); cbv beta iota; [|cbn [length]; lia].
      destruct f2 as [|d1 [|d2 [|c3 f4]]]; cbv beta iota; try (cbn [length]; lia).
      cbn [length] in Hl.
      destruct (isdigit d1 && isdigit d2 && (c3 =? 115)); cbv beta iota; [|cbn [length]; lia].
      destruct a as [|x a']; cbv beta iota; [cbn [length]; lia|]. inversion Ha as [|? ? Hx Ha']; subst.
      pose proof (rf_arg_s_len x Hx). specialize (IH f4 a' ltac:(lia) Ha').
      rewrite length_app, length_firstn. cbn [length]. lia.
Qed.

(* 6. *)
Lemma rf_refuse_ge8 : forall rcs ln f a, (8 <= length (rc_refusal rcs))%nat ->
  SegModel.refuse rcs ln f a =
  RConf (rc_seg rcs) (rc_refusal rcs) (rc_refused rcs + 1) (rc_overflow rcs) (rc_reading rcs) (rc_gen rcs).
Proof.
  intros rcs ln f a H. unfold SegModel.refuse. cbv zeta.
  rewrite (proj2 (Z.leb_le 8 (Z.of_nat (length (rc_refusal rcs))))) by lia. reflexivity.
Qed.

Lemma rf_T1 : forall rcs bs ln, seg_spec.rconf_enc rcs bs -> 0 <= ln < 2 ^ 31 ->
  (length (T1 rcs ln) <= 108)%nat /\ ~ In 0 (T1 rcs ln) /\ Forall (fun x => 0 < x < 256) (T1 rcs ln).
Proof.
  intros rcs bs ln HE Hln. destruct (rf_where rcs bs HE) as (Hl & Hn & Hb).
  pose proof (rf_dec_len10 ln Hln) as Hd.
  assert (Hdp : Forall PBYTE (dec ln)) by (apply rf_pos; [apply rf_dec_byte | apply dec_nulfree]).
  unfold r_addr_fmt, r_addr_args. destruct (0 <? ln).
  - rewrite fmt_addr_line, (cut_nul_id _ Hn).
    split; [rewrite !length_app; cbn [length]; lia|].
    split.
    + assert (Hz : nulfree (r_where rcs ++ [58] ++ dec ln ++ [58; 32])).
      { apply nulfree_app; split; [exact Hn|]. apply nulfree_app; split; [apply (nulfree_forallb [58]); reflexivity|].
        apply nulfree_app; split; [apply dec_nulfree | apply (nulfree_forallb [58; 32]); reflexivity]. }
      exact Hz.
    + apply Forall_app; split; [exact Hb|]. apply Forall_app; split; [apply rf_pos_forallb; reflexivity|].
      apply Forall_app; split; [exact Hdp | apply rf_pos_forallb; reflexivity].
  - rewrite fmt_addr, (cut_nul_id _ Hn).
    split; [rewrite !length_app; cbn [length]; lia|].
    split.
    + assert (Hz : nulfree (r_where rcs ++ [58; 32])).
      { apply nulfree_app; split; [exact Hn | apply (nulfree_forallb [58; 32]); reflexivity]. }
      exact Hz.
    + apply Forall_app; split; [exact Hb | apply rf_pos_forallb; reflexivity].
Qed.

Lemma rf_refuse_lt8 : forall rcs bs ln f a, seg_spec.rconf_enc rcs bs -> 0 <= ln < 2 ^ 31 ->
  (length (rc_refusal rcs) < 8)%nat ->
  SegModel.refuse rcs ln f a = RConf (rc_seg rcs)
    (rc_refusal rcs ++ [T1 rcs ln ++ firstn (Z.to_nat (199 - Z.of_nat (length (T1 rcs ln)))) (SegModel.fmt f a)])
    (rc_refused rcs + 1) (rc_overflow rcs) (rc_reading rcs) (rc_gen rcs).
Proof.
  intros rcs bs ln f a HE Hln Hn8. destruct (rf_T1 rcs bs ln HE Hln) as (Hl & _ & _).
  unfold SegModel.refuse, snprintf_r, snprintf_s. cbv zeta.
  rewrite (proj2 (Z.leb_gt 8 (Z.of_nat (length (rc_refusal rcs))))) by lia.
  set (T := fmt (r_addr_fmt ln) (r_addr_args rcs ln)) in *.
  rewrite (proj2 (Z.ltb_ge (Z.of_nat (length T)) 0)) by lia.
  rewrite (proj2 (Z.leb_gt 200 (Z.of_nat (length T)))) by lia.
  cbn [orb].
  replace (firstn (Z.to_nat (200 - 1)) T) with T by (symmetry; apply firstn_all2; lia).
  replace (Z.to_nat (200 - Z.of_nat (length T) - 1)) with (Z.to_nat (199 - Z.of_nat (length T))) by (f_equal; lia).
  reflexivity.
Qed.

(* 7. *)
Lemma rf_txt : forall f a, In f (SegModel.F_addr_line :: SegModel.F_addr :: seg_spec.REFUSE_FORMATS) ->
  seg_spec.conv_kinds f = map seg_spec.arg_is_s a -> Forall rf_argok a ->
  ~ In 0 (SegModel.fmt f a) /\ Forall (fun x => 0 < x < 256) (SegModel.fmt f a) /\
  Z.of_nat (length (SegModel.fmt f a)) < 2 ^ 31 - 1.
Proof.
  intros f a Hf Hck Ha.
  assert (HF : nulfree f /\ Forall BYTE f /\ (length f <= 200)%nat /\ (length (conv_kinds f) <= 3)%nat).
  { unfold REFUSE_FORMATS in Hf.
    repeat (destruct Hf as [<-|Hf];
      [split; [apply nulfree_forallb; vm_compute; reflexivity|];
       split; [apply rf_byte_forallb; vm_compute; reflexivity|];
       split; apply Nat.leb_le; vm_compute; reflexivity|]).
    destruct Hf. }
  destruct HF as (Hn & Hb & Hlf & Hlk).
  assert (Hla : length a = length (conv_kinds f)) by (rewrite Hck, length_map; reflexivity).
  assert (Hab : Forall rf_argb a).
  { apply Forall_forall. intros x Hx. apply rf_argok_b. exact (proj1 (Forall_forall _ _) Ha x Hx). }
  assert (Hfn : nulfree (fmt f a)) by (apply fmt_nulfree; exact Hn).
  split; [exact Hfn|].
  split; [apply rf_pos; [apply (rf_fmt_byte_n (length f)); auto | exact Hfn]|].
  pose proof (rf_fmt_len (length f) f a (le_n _) Ha) as HL. lia.
Qed.

(* 8. The walk loads c->refused with `lw` (sign-extending), adds 1 and stores the low word with `sw`: the four
   bytes stored are those of r + 1. *)
Lemma rf_sw_inc : forall r, 0 <= r < 2 ^ 32 -> forall k, (k < 4)%nat ->
  le_byte (bv_unsigned (Z_to_bv 64 (Z.land (r + 2 ^ 31) (2 ^ 32 - 1) - 2 ^ 31 + 1))) 4 k = le_byte (r + 1) 4 k.
Proof.
  intros r Hr k Hk. unfold le_byte. f_equal. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  change (2 ^ 32 - 1) with (Z.ones 32). rewrite Z.land_ones by lia.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.
