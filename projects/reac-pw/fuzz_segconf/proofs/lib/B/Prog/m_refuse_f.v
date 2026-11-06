(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan): the pure lemmas of m_refuse's walk.
   proves no function (kind: model lemma: the mconf encoding and printf-text lemmas of m_refuse's image-B walk,
   adapted from lib/U/Prog/m_refuse.v enc_new / enc_full).
   - mr_fields: the fields the walk reads, from the entry's sa_mconfp (n_kept, refused, the reading string, the
     block mapped);
   - mr_text, mr_text_len, mr_text_bytes, mr_sn: the text m_refuse stores into kept[n_kept] and the snprintf
     contract's written bytes for it (RtPFShared.sn_bytes / sn_len at n - 1 = 111);
   - mr_dec, mr_parse_al, mr_parse_a, mr_text_al, mr_text_a: the two formats as the snprintf contract's family
     (lib/B/Rt/RtPFSeg.v seg_parse / seg_text) parses and renders them;
   - mr_enc_kept (n_kept < 8) and mr_enc_full (n_kept = 8): the block after the call holds
     SegModel.m_refuse mc line knock (sa_mconf), from the bytes the walk wrote and the bytes it kept.
   Image-independent: no image number appears; the offsets are seg_spec's struct mconf layout. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtPFShared RtPFSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Module SM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegModel.
Module SP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.seg_spec.
(* the released printf pieces and renderer that RtPFSeg's PRel embeds (seg_step (PRel Pd) renders RtPFPf.pf_dec) *)
Module PF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt.RtPFPf.

(* ======================================= lists ======================================= *)
Lemma mr_nth_firstn : forall {A} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros A l. induction l as [|x l IH]; intros n i d H.
- destruct n; cbn [firstn]; reflexivity.
- destruct n as [|n]; [lia|]. destruct i as [|i]; cbn [firstn nth]; [reflexivity|]. apply IH. lia.
Qed.
Lemma mr_nth_skipn : forall {A} (l : list A) n i d, nth i (skipn n l) d = nth (n + i) l d.
Proof.
intros A l n. revert l. induction n as [|n IH]; intros l i d; [reflexivity|].
destruct l as [|x l].
- destruct i; cbn; reflexivity.
- cbn [skipn]. rewrite IH. reflexivity.
Qed.

(* the list l with w written at offset o *)
Definition mr_upd (l : list byte) (o : nat) (w : list byte) : list byte := firstn o l ++ w ++ skipn (o + length w) l.
Lemma mr_length_upd : forall l o w, (o + length w <= length l)%nat -> length (mr_upd l o w) = length l.
Proof. intros l o w H. unfold mr_upd. rewrite !length_app, length_firstn, length_skipn. lia. Qed.
Lemma mr_nth_upd_in : forall l o w i d, (o + length w <= length l)%nat -> (o <= i < o + length w)%nat ->
  nth i (mr_upd l o w) d = nth (i - o) w d.
Proof.
intros l o w i d H Hi. unfold mr_upd.
rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
replace (i - Nat.min o (length l))%nat with (i - o)%nat by lia.
rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma mr_nth_upd_out : forall l o w i d, (o + length w <= length l)%nat -> (i < o \/ o + length w <= i)%nat ->
  nth i (mr_upd l o w) d = nth i l d.
Proof.
intros l o w i d H Hi. unfold mr_upd. destruct Hi as [Hi|Hi].
- rewrite app_nth1 by (rewrite length_firstn; lia). apply mr_nth_firstn. exact Hi.
- rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  rewrite app_nth2 by lia. rewrite mr_nth_skipn. f_equal. lia.
Qed.

Lemma mr_fld_nth : forall (l : list byte) o k j d, (j < k)%nat -> nth j (SP.fld o k l) d = nth (o + j) l d.
Proof. intros l o k j d H. unfold SP.fld. rewrite mr_nth_firstn by lia. apply mr_nth_skipn. Qed.
Lemma mr_length_fld : forall (l : list byte) o k, (o + k <= length l)%nat -> length (SP.fld o k l) = k.
Proof. intros l o k H. unfold SP.fld. rewrite length_firstn, length_skipn. lia. Qed.
Lemma mr_firstn_fld : forall (l : list byte) o k m, (m <= k)%nat -> firstn m (SP.fld o k l) = SP.fld o m l.
Proof. intros l o k m H. unfold SP.fld. rewrite firstn_firstn. f_equal. lia. Qed.

Lemma mr_fld_upd_out : forall l o w fo k, (o + length w <= length l)%nat -> (fo + k <= length l)%nat ->
  (fo + k <= o \/ o + length w <= fo)%nat -> SP.fld fo k (mr_upd l o w) = SP.fld fo k l.
Proof.
intros l o w fo k H1 H2 H3.
assert (E : length (mr_upd l o w) = length l) by (apply mr_length_upd; exact H1).
apply nth_ext with (d := SP.ZERO) (d' := SP.ZERO).
- rewrite !mr_length_fld by lia. reflexivity.
- intros j Hj. rewrite mr_length_fld in Hj by lia.
  rewrite !mr_fld_nth by lia. apply mr_nth_upd_out; lia.
Qed.
Lemma mr_fld_upd_in : forall l o w fo k, (o + length w <= length l)%nat -> fo = o -> k = length w ->
  SP.fld fo k (mr_upd l o w) = w.
Proof.
intros l o w fo k H -> ->.
assert (E : length (mr_upd l o w) = length l) by (apply mr_length_upd; exact H).
apply nth_ext with (d := SP.ZERO) (d' := SP.ZERO).
- rewrite mr_length_fld by lia. reflexivity.
- intros j Hj. rewrite mr_length_fld in Hj by lia.
  rewrite mr_fld_nth by lia. rewrite mr_nth_upd_in by lia. f_equal. lia.
Qed.

(* three writes one after the other: kept[n_kept]'s refused cell, its text slot, its n_kept cell *)
Definition mr_upd3 (l w1 w2 w3 : list byte) (o1 o2 o3 : nat) : list byte :=
  mr_upd (mr_upd (mr_upd l o1 w1) o2 w2) o3 w3.
Lemma mr_length_upd3 : forall l w1 w2 w3 o1 o2 o3,
  (o1 + length w1 <= length l)%nat -> (o2 + length w2 <= length l)%nat -> (o3 + length w3 <= length l)%nat ->
  length (mr_upd3 l w1 w2 w3 o1 o2 o3) = length l.
Proof.
intros l w1 w2 w3 o1 o2 o3 H1 H2 H3. unfold mr_upd3.
assert (E1 : length (mr_upd l o1 w1) = length l) by (apply mr_length_upd; lia).
assert (E2 : length (mr_upd (mr_upd l o1 w1) o2 w2) = length l) by (rewrite mr_length_upd; lia).
rewrite mr_length_upd; lia.
Qed.
Lemma mr_nth3 : forall l w1 w2 w3 o1 o2 o3 i d,
  (o1 + length w1 <= length l)%nat -> (o2 + length w2 <= length l)%nat -> (o3 + length w3 <= length l)%nat ->
  ((o3 <= i < o3 + length w3)%nat -> nth i (mr_upd3 l w1 w2 w3 o1 o2 o3) d = nth (i - o3) w3 d) /\
  ((i < o3 \/ o3 + length w3 <= i)%nat -> (o2 <= i < o2 + length w2)%nat ->
     nth i (mr_upd3 l w1 w2 w3 o1 o2 o3) d = nth (i - o2) w2 d) /\
  ((i < o3 \/ o3 + length w3 <= i)%nat -> (i < o2 \/ o2 + length w2 <= i)%nat -> (o1 <= i < o1 + length w1)%nat ->
     nth i (mr_upd3 l w1 w2 w3 o1 o2 o3) d = nth (i - o1) w1 d) /\
  ((i < o3 \/ o3 + length w3 <= i)%nat -> (i < o2 \/ o2 + length w2 <= i)%nat -> (i < o1 \/ o1 + length w1 <= i)%nat ->
     nth i (mr_upd3 l w1 w2 w3 o1 o2 o3) d = nth i l d).
Proof.
intros l w1 w2 w3 o1 o2 o3 i d H1 H2 H3. unfold mr_upd3.
assert (E1 : length (mr_upd l o1 w1) = length l) by (apply mr_length_upd; lia).
assert (E2 : length (mr_upd (mr_upd l o1 w1) o2 w2) = length l) by (rewrite mr_length_upd; lia).
split; [intros; apply mr_nth_upd_in; lia|].
split; [intros; rewrite mr_nth_upd_out by lia; apply mr_nth_upd_in; lia|].
split; [intros; rewrite mr_nth_upd_out by lia; rewrite mr_nth_upd_out by lia; apply mr_nth_upd_in; lia|].
intros; rewrite mr_nth_upd_out by lia; rewrite mr_nth_upd_out by lia; apply mr_nth_upd_out; lia.
Qed.
Lemma mr_fld3_out : forall l w1 w2 w3 o1 o2 o3 fo k,
  (o1 + length w1 <= length l)%nat -> (o2 + length w2 <= length l)%nat -> (o3 + length w3 <= length l)%nat ->
  (fo + k <= length l)%nat ->
  (fo + k <= o1 \/ o1 + length w1 <= fo)%nat -> (fo + k <= o2 \/ o2 + length w2 <= fo)%nat ->
  (fo + k <= o3 \/ o3 + length w3 <= fo)%nat ->
  SP.fld fo k (mr_upd3 l w1 w2 w3 o1 o2 o3) = SP.fld fo k l.
Proof.
intros l w1 w2 w3 o1 o2 o3 fo k H1 H2 H3 H4 D1 D2 D3. unfold mr_upd3.
assert (E1 : length (mr_upd l o1 w1) = length l) by (apply mr_length_upd; lia).
assert (E2 : length (mr_upd (mr_upd l o1 w1) o2 w2) = length l) by (rewrite mr_length_upd; lia).
rewrite mr_fld_upd_out by lia. rewrite mr_fld_upd_out by lia. apply mr_fld_upd_out; lia.
Qed.
Lemma mr_fld3_in1 : forall l w1 w2 w3 o1 o2 o3 fo k,
  (o1 + length w1 <= length l)%nat -> (o2 + length w2 <= length l)%nat -> (o3 + length w3 <= length l)%nat ->
  (o1 + length w1 <= o2 \/ o2 + length w2 <= o1)%nat -> (o1 + length w1 <= o3 \/ o3 + length w3 <= o1)%nat ->
  fo = o1 -> k = length w1 -> SP.fld fo k (mr_upd3 l w1 w2 w3 o1 o2 o3) = w1.
Proof.
intros l w1 w2 w3 o1 o2 o3 fo k H1 H2 H3 D2 D3 -> ->. unfold mr_upd3.
assert (E1 : length (mr_upd l o1 w1) = length l) by (apply mr_length_upd; lia).
assert (E2 : length (mr_upd (mr_upd l o1 w1) o2 w2) = length l) by (rewrite mr_length_upd; lia).
rewrite mr_fld_upd_out by lia. rewrite mr_fld_upd_out by lia. apply mr_fld_upd_in; lia.
Qed.
Lemma mr_fld3_pre2 : forall l w1 w2 w3 o1 o2 o3 fo k m,
  (o1 + length w1 <= length l)%nat -> (o2 + length w2 <= length l)%nat -> (o3 + length w3 <= length l)%nat ->
  (o2 + k <= length l)%nat -> (o2 + k <= o3 \/ o3 + length w3 <= o2)%nat ->
  fo = o2 -> m = length w2 -> (m <= k)%nat ->
  firstn m (SP.fld fo k (mr_upd3 l w1 w2 w3 o1 o2 o3)) = w2.
Proof.
intros l w1 w2 w3 o1 o2 o3 fo k m H1 H2 H3 H4 D3 -> -> Hm. unfold mr_upd3.
assert (E1 : length (mr_upd l o1 w1) = length l) by (apply mr_length_upd; lia).
assert (E2 : length (mr_upd (mr_upd l o1 w1) o2 w2) = length l) by (rewrite mr_length_upd; lia).
rewrite mr_fld_upd_out by lia. rewrite mr_firstn_fld by lia. apply mr_fld_upd_in; lia.
Qed.
Lemma mr_fld3_in3 : forall l w1 w2 w3 o1 o2 o3 fo k,
  (o1 + length w1 <= length l)%nat -> (o2 + length w2 <= length l)%nat -> (o3 + length w3 <= length l)%nat ->
  fo = o3 -> k = length w3 -> SP.fld fo k (mr_upd3 l w1 w2 w3 o1 o2 o3) = w3.
Proof.
intros l w1 w2 w3 o1 o2 o3 fo k H1 H2 H3 -> ->. unfold mr_upd3.
assert (E1 : length (mr_upd l o1 w1) = length l) by (apply mr_length_upd; lia).
assert (E2 : length (mr_upd (mr_upd l o1 w1) o2 w2) = length l) by (rewrite mr_length_upd; lia).
apply mr_fld_upd_in; lia.
Qed.

(* ======================================= bytes ======================================= *)
Lemma mr_Z_to_le_bytes_nth : forall n z k, 0 <= z -> (k < n)%nat ->
  bv_unsigned (nth k (Z_to_le_bytes n z) ZB0) = Z.shiftr z (8 * Z.of_nat k) mod 256.
Proof.
induction n as [|n IH]; intros z k Hz Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k]; cbn [nth].
- rewrite Z_to_bv_unsigned. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (bv_wrap 8 z) with (z mod 2 ^ 8). reflexivity.
- rewrite IH by (try apply Z.shiftr_nonneg; lia).
  rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma mr_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold Mem.le4, le_byte. rewrite Z_to_bv_unsigned.
rewrite (bv_wrap_small 64 v) by (change (bv_modulus 64) with (2 ^ 64); lia).
rewrite mr_Z_to_le_bytes_nth by lia.
change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.
Lemma mr_zb_nth : forall l j, Forall (fun z => 0 <= z < 256) l -> (j < length l)%nat ->
  bv_unsigned (nth j (SP.zb l) ZB0) = nth j l 0.
Proof.
intros l j HF Hj. unfold SP.zb, ZB0. rewrite (map_nth (Z_to_bv 8) l 0 j).
rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256.
rewrite Forall_forall in HF. apply HF. apply nth_In. exact Hj.
Qed.
Lemma mr_rng_of_pos : forall l, Forall (fun b => 0 < b < 256) l -> Forall (fun z => 0 <= z < 256) l.
Proof. intros l H. induction H as [|x l Hx Hl IH]; [constructor | constructor; [lia | exact IH]]. Qed.
Lemma mr_zb_nul : forall T, Forall (fun b => 0 < b < 256) T -> SP.zb T ++ [SP.ZERO] = SP.zb (T ++ [0]).
Proof. intros T _. unfold SP.zb. rewrite map_app. reflexivity. Qed.

(* a u32 field of the block as sa_val *)
Lemma mr_sa_val_u32 : forall (rd : reader) c bs o v, sa_bytes rd c bs -> 0 <= o ->
  (Z.to_nat o + 4 <= length bs)%nat -> SP.u32_enc v (SP.fldz o 4 bs) -> sa_val rd (c + o) 4 v.
Proof.
intros rd c bs o v Hb Ho Hl [Hv Hf] k Hk.
assert (Hi : (Z.to_nat o + k < length bs)%nat) by lia.
pose proof (Hb _ Hi) as E.
replace (c + Z.of_nat (Z.to_nat o + k)) with (c + o + Z.of_nat k) in E by lia.
rewrite E. f_equal.
rewrite <- (mr_fld_nth bs (Z.to_nat o) 4 k ZB0) by exact Hk.
unfold SP.fldz in Hf. change (Z.to_nat 4) with 4%nat in Hf. rewrite Hf.
apply mr_le4_byte; assumption.
Qed.

(* ================================ the fields the walk reads ================================ *)
Lemma mr_fields : forall knock (rd : reader) c mc, sa_mconfp knock rd c mc ->
  (length (SM.mc_kept mc) <= 8)%nat /\
  sa_val rd (c + SP.MC_NKEPT) 4 (Z.of_nat (length (SM.mc_kept mc))) /\
  0 <= SM.mc_refused mc < 2 ^ 32 /\ sa_val rd (c + SP.MC_REFUSED) 4 (SM.mc_refused mc) /\
  (length (SM.mc_reading mc) < 96)%nat /\ Forall (fun b => 0 < b < 256) (SM.mc_reading mc) /\
  (forall i, (i <= length (SM.mc_reading mc))%nat ->
     rd (c + SP.MC_READING + Z.of_nat i) = Some (nth i (SM.mc_reading mc ++ [0]) 0)) /\
  (forall a, c <= a < c + SP.SEG_M_SIZE -> rd a <> None).
Proof.
intros knock rd c mc [bs [Hb HE]].
destruct HE as (HLb & _ & _ & _ & _ & Hrefd & HKL & _ & _ & Hnk & _ & Hrd).
unfold SP.SEG_M_SIZE in HLb.
destruct Hrd as (Hl96 & Hlt & Hn0 & Hf). unfold SP.fldz in Hl96, Hf.
assert (HrdF : forall i, (i <= length (SM.mc_reading mc))%nat ->
  nth i (SM.mc_reading mc ++ [0]) 0 = bv_unsigned (nth (Z.to_nat SP.MC_READING + i) bs ZB0)).
{ intros i Hi. rewrite <- Hf. unfold SP.zs. rewrite mr_nth_firstn by lia.
  rewrite nth_indep with (d' := bv_unsigned ZB0) by (rewrite length_map; lia).
  rewrite map_nth. rewrite mr_fld_nth by lia. reflexivity. }
split; [exact HKL|].
split; [apply (mr_sa_val_u32 rd c bs SP.MC_NKEPT); [exact Hb | unfold SP.MC_NKEPT; lia | unfold SP.MC_NKEPT; lia | exact Hnk]|].
split; [destruct Hrefd as [Hv _]; exact Hv|].
split; [apply (mr_sa_val_u32 rd c bs SP.MC_REFUSED); [exact Hb | unfold SP.MC_REFUSED; lia | unfold SP.MC_REFUSED; lia | exact Hrefd]|].
split; [exact Hlt|].
split.
{ apply Forall_forall. intros b Hin. destruct (In_nth _ _ 0 Hin) as [j [Hj Ej]].
  assert (Hb0 : b <> 0) by (intros ->; exact (Hn0 Hin)).
  assert (E2 : b = bv_unsigned (nth (Z.to_nat SP.MC_READING + j) bs ZB0)).
  { rewrite <- Ej. rewrite <- HrdF by lia. rewrite app_nth1 by lia. reflexivity. }
  pose proof (bv_unsigned_in_range _ (nth (Z.to_nat SP.MC_READING + j) bs ZB0)) as R.
  change (bv_modulus 8) with 256 in R. lia. }
split.
{ intros i Hi. rewrite HrdF by exact Hi.
  assert (Hi' : (Z.to_nat SP.MC_READING + i < length bs)%nat) by (unfold SP.MC_READING; lia).
  rewrite <- (Hb _ Hi'). f_equal. unfold SP.MC_READING; lia. }
intros a Ha. unfold SP.SEG_M_SIZE in Ha. assert (Hi : (Z.to_nat (a - c) < length bs)%nat) by lia.
replace a with (c + Z.of_nat (Z.to_nat (a - c))) by lia. rewrite (Hb _ Hi). discriminate.
Qed.

(* ================================ the text and its bytes ================================ *)
(* the text m_refuse stores into kept[n_kept] *)
Definition mr_text (mc : SM.mconf) (line : Z) : list Z :=
  if 0 <? line then SM.fmt SM.F_addr_line [SM.AS (SM.mc_reading mc); SM.AI line]
  else SM.fmt SM.F_addr [SM.AS (SM.mc_reading mc)].

Lemma mr_dec_len : forall z, 0 <= z <= 65536 -> (length (SM.dec z) <= 5)%nat.
Proof.
intros z H. unfold SM.dec. destruct (Z.ltb_spec z 0); [lia|].
pose proof (SM.dec_go_len 4 20 z [] ltac:(cbn; lia) ltac:(lia)) as Hd. cbn [length] in Hd. lia.
Qed.
Lemma mr_text_len : forall mc line, (length (SM.mc_reading mc) < 96)%nat -> 0 <= line <= 65536 ->
  (length (mr_text mc line) <= 104)%nat.
Proof.
intros mc line Hr Hl. pose proof (SM.cut_nul_len (SM.mc_reading mc)) as Hc. pose proof (mr_dec_len line Hl) as Hd.
unfold mr_text. destruct (0 <? line); [rewrite SM.fmt_addr_line | rewrite SM.fmt_addr];
  rewrite ?length_app; cbn [length]; lia.
Qed.

Lemma mr_Forall_cut_nul : forall (P : Z -> Prop) l, Forall P l -> Forall P (SM.cut_nul l).
Proof.
intros P l H. induction H as [|x l Hx Hl IH]; cbn [SM.cut_nul]; [constructor|].
destruct (x =? 0); [constructor | constructor; assumption].
Qed.
Lemma mr_dec_go_bytes : forall f n acc, Forall (fun b => 0 < b < 256) acc ->
  Forall (fun b => 0 < b < 256) (SM.dec_go f n acc).
Proof.
induction f as [|f IH]; intros n acc H; cbn [SM.dec_go]; [exact H|].
assert (Hd : Forall (fun b => 0 < b < 256) ((48 + n mod 10) :: acc)).
{ constructor; [pose proof (Z.mod_pos_bound n 10 ltac:(lia)); lia | exact H]. }
destruct (n <? 10); [exact Hd | apply IH, Hd].
Qed.
Lemma mr_dec_bytes : forall z, Forall (fun b => 0 < b < 256) (SM.dec z).
Proof.
intros z. unfold SM.dec. destruct (z <? 0); [constructor; [lia|]|]; apply mr_dec_go_bytes; constructor.
Qed.
Lemma mr_text_bytes : forall mc line, Forall (fun b => 0 < b < 256) (SM.mc_reading mc) -> 0 <= line <= 65536 ->
  Forall (fun b => 0 < b < 256) (mr_text mc line).
Proof.
intros mc line Hr Hl. pose proof (mr_Forall_cut_nul _ _ Hr) as Hc. pose proof (mr_dec_bytes line) as Hd.
unfold mr_text. destruct (0 <? line).
- rewrite SM.fmt_addr_line. apply Forall_app. split; [exact Hc|].
  apply Forall_app. split; [repeat constructor; lia|].
  apply Forall_app. split; [exact Hd | repeat constructor; lia].
- rewrite SM.fmt_addr. apply Forall_app. split; [exact Hc | repeat constructor; lia].
Qed.

Lemma mr_sn : forall T, (length T <= 104)%nat ->
  RtPFShared.sn_bytes 111 T = T ++ [0] /\ RtPFShared.sn_len 111 T = Z.of_nat (length T) + 1.
Proof.
intros T H.
assert (E : RtPFShared.sn_bytes 111 T = T ++ [0]).
{ unfold RtPFShared.sn_bytes. change (Z.to_nat 111) with 111%nat. rewrite firstn_all2 by lia. reflexivity. }
split; [exact E|]. unfold RtPFShared.sn_len. rewrite E, length_app. cbn [length]. lia.
Qed.

(* ============================ the two formats, as RtPFSeg reads them ============================ *)
Definition mr_qs_al : list RtPFSeg.seg_piece :=
  [RtPFSeg.PRel Ps; RtPFSeg.PRel (PLit 58); RtPFSeg.PRel Pd; RtPFSeg.PRel (PLit 58); RtPFSeg.PRel (PLit 32)].
Definition mr_qs_a : list RtPFSeg.seg_piece := [RtPFSeg.PRel Ps; RtPFSeg.PRel (PLit 58); RtPFSeg.PRel (PLit 32)].

(* pf_digits checks x < 10 first and conses 48 + x; dec_go conses 48 + x mod 10 and then checks x < 10 *)
Lemma mr_digits : forall k f g x acc, 0 <= x < 10 ^ (Z.of_nat k + 1) -> (k < f)%nat -> (k < g)%nat ->
  PF.pf_digits f x acc = SM.dec_go g x acc.
Proof.
induction k as [|k IH]; intros f g x acc Hx Hf Hg; (destruct f as [|f]; [lia|]); (destruct g as [|g]; [lia|]);
  cbn [PF.pf_digits SM.dec_go].
- change (10 ^ (Z.of_nat 0 + 1)) with 10 in Hx.
  destruct (Z.ltb_spec x 10); [|lia]. rewrite Z.mod_small by lia. reflexivity.
- destruct (Z.ltb_spec x 10) as [Hlt|Hge]; [rewrite Z.mod_small by lia; reflexivity|].
  apply IH; [|lia|lia]. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|].
  replace (Z.of_nat (S k) + 1) with (Z.succ (Z.of_nat k + 1)) in Hx by lia.
  rewrite Z.pow_succ_r in Hx by lia. lia.
Qed.
Lemma mr_dec : forall z, 0 <= z <= 65536 -> PF.pf_dec z = SM.dec z.
Proof.
intros z Hz. unfold PF.pf_dec, SM.dec. destruct (Z.ltb_spec z 0); [lia|].
apply (mr_digits 4); [cbn; lia | lia | lia].
Qed.
Lemma mr_parse_al : RtPFSeg.seg_parse SM.F_addr_line = Some mr_qs_al.
Proof. vm_compute. reflexivity. Qed.
Lemma mr_parse_a : RtPFSeg.seg_parse SM.F_addr = Some mr_qs_a.
Proof. vm_compute. reflexivity. Qed.
Lemma mr_text_al : forall r line, ~ In 0 r -> 0 <= line <= 65536 ->
  RtPFSeg.seg_text mr_qs_al [APtr r; AInt line] = Some (SM.fmt SM.F_addr_line [SM.AS r; SM.AI line]).
Proof.
intros r line Hr Hl. unfold mr_qs_al. cbn [RtPFSeg.seg_text RtPFSeg.seg_step option_map].
rewrite SM.fmt_addr_line, SM.cut_nul_id by exact Hr. rewrite mr_dec by exact Hl. reflexivity.
Qed.
Lemma mr_text_a : forall r, ~ In 0 r ->
  RtPFSeg.seg_text mr_qs_a [APtr r] = Some (SM.fmt SM.F_addr [SM.AS r]).
Proof.
intros r Hr. unfold mr_qs_a. cbn [RtPFSeg.seg_text RtPFSeg.seg_step option_map].
rewrite SM.fmt_addr, SM.cut_nul_id by exact Hr. reflexivity.
Qed.

(* ============================ the block after the call ============================ *)
Lemma mr_m_refuse_kept : forall mc line knock, (length (SM.mc_kept mc) < 8)%nat ->
  (length (mr_text mc line) <= 104)%nat ->
  SM.m_refuse mc line knock =
  SM.MConf (SM.mc_seg mc) (SM.mc_overflow mc) (SM.mc_refused mc + 1)
    (SM.mc_kept mc ++ [(mr_text mc line, knock)]) (SM.mc_gen mc) (SM.mc_reading mc).
Proof.
intros mc line knock H8 HTL. unfold SM.m_refuse, SM.snprintf_s.
replace (Z.of_nat (length (SM.mc_kept mc)) <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
unfold mr_text in HTL |- *. change (Z.to_nat (112 - 1)) with 111%nat.
revert HTL. destruct (0 <? line); cbv beta iota zeta; intros HTL; rewrite firstn_all2 by lia; reflexivity.
Qed.
Lemma mr_m_refuse_full : forall mc line knock, length (SM.mc_kept mc) = 8%nat ->
  SM.m_refuse mc line knock =
  SM.MConf (SM.mc_seg mc) (SM.mc_overflow mc) (SM.mc_refused mc + 1) (SM.mc_kept mc) (SM.mc_gen mc)
    (SM.mc_reading mc).
Proof.
intros mc line knock H8. unfold SM.m_refuse.
replace (Z.of_nat (length (SM.mc_kept mc)) <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
reflexivity.
Qed.

(* n_kept < 8: kept[n_kept] holds the text, n_kept and refused one more *)
Lemma mr_enc_kept : forall knock (rd rd' : reader) c mc line,
  sa_mconfp knock rd c mc -> (length (SM.mc_kept mc) < 8)%nat -> SM.mc_refused mc + 1 < 2 ^ 32 ->
  0 <= line <= 65536 ->
  (forall i, 0 <= i < RtPFShared.sn_len 111 (mr_text mc line) ->
     rd' (SP.kept_addr c (length (SM.mc_kept mc)) + i) =
     Some (nth (Z.to_nat i) (RtPFShared.sn_bytes 111 (mr_text mc line)) 0)) ->
  sa_val rd' (c + SP.MC_NKEPT) 4 (Z.of_nat (length (SM.mc_kept mc)) + 1) ->
  sa_val rd' (c + SP.MC_REFUSED) 4 (SM.mc_refused mc + 1) ->
  (forall a, c <= a < c + SP.SEG_M_SIZE ->
     ~ (SP.kept_addr c (length (SM.mc_kept mc)) <= a <
        SP.kept_addr c (length (SM.mc_kept mc)) + RtPFShared.sn_len 111 (mr_text mc line)) ->
     ~ (c + SP.MC_NKEPT <= a < c + SP.MC_NKEPT + 4) -> ~ (c + SP.MC_REFUSED <= a < c + SP.MC_REFUSED + 4) ->
     rd' a = rd a) ->
  sa_mconf rd' c (SM.m_refuse mc line knock).
Proof.
intros knock rd rd' c mc line HP Hlt Hrf Hline Hslot HnkV HrfV Hfr.
pose proof (mr_fields knock rd c mc HP) as (_ & _ & [Hr0 _] & _ & HrL & HrB & _ & _).
pose proof (mr_text_len mc line HrL Hline) as HTL.
pose proof (mr_text_bytes mc line HrB Hline) as HTB.
destruct (mr_sn (mr_text mc line) HTL) as [EsB EsL].
rewrite EsB, EsL in Hslot. rewrite EsL in Hfr.
rewrite (mr_m_refuse_kept mc line knock Hlt HTL).
destruct HP as [bs [Hb HE]].
unfold SP.mconf_encp, SP.fldz in HE.
destruct HE as (HLb & Hseg32 & Hsegs & Hn & Hov & Hrefd & HKL & Hkept & Hknock & Hnk & Hgen & Hrd).
set (T := mr_text mc line) in *.
set (w1 := Mem.le4 (Z_to_bv 64 (SM.mc_refused mc + 1))).
set (w2 := SP.zb T ++ [SP.ZERO]).
set (w3 := Mem.le4 (Z_to_bv 64 (Z.of_nat (length (SM.mc_kept mc)) + 1))).
assert (L1 : length w1 = 4%nat) by (unfold w1; apply Mem.length_le4).
assert (L2 : length w2 = S (length T)) by (unfold w2, SP.zb; rewrite length_app, length_map; cbn [length]; lia).
assert (L3 : length w3 = 4%nat) by (unfold w3; apply Mem.length_le4).
assert (HTF : Forall (fun z => 0 <= z < 256) (T ++ [0])).
{ apply Forall_app. split; [apply mr_rng_of_pos, HTB | repeat constructor; lia]. }
unfold SP.kept_addr, SP.MC_N, SP.MC_OVERFLOW, SP.MC_REFUSED, SP.MC_KEPT, SP.MC_KEPT_LEN, SP.MC_KNOCK, SP.MC_NKEPT,
  SP.MC_GEN, SP.MC_READING, SP.SEG_M_SIZE in *.
unfold sa_mconf, sa_mconfp.
exists (mr_upd3 bs w1 w2 w3 (Z.to_nat 8200) (Z.to_nat 8204 + 112 * length (SM.mc_kept mc)) (Z.to_nat 9132)).
assert (S1 : (Z.to_nat 8200 + length w1 <= length bs)%nat) by lia.
assert (S2 : (Z.to_nat 8204 + 112 * length (SM.mc_kept mc) + length w2 <= length bs)%nat) by lia.
assert (S3 : (Z.to_nat 9132 + length w3 <= length bs)%nat) by lia.
split.
- (* the bytes rd' gives on the block *)
  intros i Hi. rewrite mr_length_upd3 in Hi by assumption.
  destruct (mr_nth3 bs w1 w2 w3 (Z.to_nat 8200) (Z.to_nat 8204 + 112 * length (SM.mc_kept mc)) (Z.to_nat 9132)
    i ZB0 S1 S2 S3) as (N3 & N2 & N1 & N0).
  assert (Hc : (Z.to_nat 9132 <= i < Z.to_nat 9132 + 4 \/
                Z.to_nat 8204 + 112 * length (SM.mc_kept mc) <= i <
                  Z.to_nat 8204 + 112 * length (SM.mc_kept mc) + S (length T) \/
                Z.to_nat 8200 <= i < Z.to_nat 8200 + 4 \/
                ((i < Z.to_nat 9132 \/ Z.to_nat 9132 + 4 <= i) /\
                 (i < Z.to_nat 8204 + 112 * length (SM.mc_kept mc) \/
                  Z.to_nat 8204 + 112 * length (SM.mc_kept mc) + S (length T) <= i) /\
                 (i < Z.to_nat 8200 \/ Z.to_nat 8200 + 4 <= i)))%nat) by lia.
  destruct Hc as [Hc|[Hc|[Hc|Hc]]].
  + (* n_kept *)
    rewrite N3 by lia.
    pose proof (HnkV (i - Z.to_nat 9132)%nat ltac:(lia)) as E.
    replace (c + 9132 + Z.of_nat (i - Z.to_nat 9132)) with (c + Z.of_nat i) in E by lia.
    rewrite E. f_equal. unfold w3. rewrite mr_le4_byte by lia. reflexivity.
  + (* the text and its NUL *)
    rewrite N2 by lia.
    pose proof (Hslot (Z.of_nat (i - (Z.to_nat 8204 + 112 * length (SM.mc_kept mc)))) ltac:(lia)) as E.
    replace (c + 8204 + 112 * Z.of_nat (length (SM.mc_kept mc)) +
             Z.of_nat (i - (Z.to_nat 8204 + 112 * length (SM.mc_kept mc)))) with (c + Z.of_nat i) in E by lia.
    rewrite Nat2Z.id in E. rewrite E. f_equal.
    unfold w2. rewrite (mr_zb_nul T HTB). rewrite mr_zb_nth; [reflexivity | exact HTF |].
    rewrite length_app. cbn [length]. lia.
  + (* refused *)
    rewrite N1 by lia.
    pose proof (HrfV (i - Z.to_nat 8200)%nat ltac:(lia)) as E.
    replace (c + 8200 + Z.of_nat (i - Z.to_nat 8200)) with (c + Z.of_nat i) in E by lia.
    rewrite E. f_equal. unfold w1. rewrite mr_le4_byte by lia. reflexivity.
  + (* every other byte: rd's *)
    rewrite N0 by lia. rewrite Hfr by lia. exact (Hb i Hi).
- (* the encoding *)
  unfold SP.mconf_encp, SP.fldz.
  cbn [SM.mc_seg SM.mc_overflow SM.mc_refused SM.mc_kept SM.mc_gen SM.mc_reading].
  unfold SP.MC_N, SP.MC_OVERFLOW, SP.MC_REFUSED, SP.MC_KEPT, SP.MC_KNOCK, SP.MC_NKEPT, SP.MC_GEN, SP.MC_READING,
    SP.SEG_M_SIZE.
  split; [rewrite mr_length_upd3 by assumption; lia|].
  split; [exact Hseg32|].
  split; [intros i Hi; rewrite mr_fld3_out by lia; exact (Hsegs i Hi)|].
  split; [rewrite mr_fld3_out by lia; exact Hn|].
  split; [rewrite mr_fld3_out by lia; exact Hov|].
  split; [rewrite mr_fld3_in1 by lia; split; [lia | reflexivity]|].
  split; [rewrite length_app; cbn [length]; lia|].
  split.
  { intros i Hi. rewrite length_app in Hi; cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i (length (SM.mc_kept mc))) as [Hi1|Hi1].
    - rewrite app_nth1 by exact Hi1. destruct (Hkept i Hi1) as [Hcs Hfl].
      split; rewrite mr_fld3_out by lia; assumption.
    - assert (Ei : i = length (SM.mc_kept mc)) by lia. subst i.
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth fst snd].
      split.
      + unfold SP.cstr_enc.
        split; [apply mr_length_fld; rewrite mr_length_upd3 by assumption; lia|].
        split; [lia|].
        split; [intros H0; rewrite Forall_forall in HTB; specialize (HTB 0 H0); lia|].
        unfold SP.zs. rewrite firstn_map. rewrite mr_fld3_pre2 by lia.
        unfold w2. rewrite (mr_zb_nul T HTB). fold (SP.zs (SP.zb (T ++ [0]))).
        apply sa_zs_zb. exact HTF.
      + rewrite mr_fld3_out by lia.
        specialize (Hknock (length (SM.mc_kept mc)) ltac:(lia)).
        rewrite Nat.eqb_refl, andb_true_r in Hknock. exact Hknock. }
  split.
  { intros i Hi. rewrite length_app in Hi; cbn [length] in Hi. cbn [andb].
    rewrite mr_fld3_out by lia.
    specialize (Hknock i ltac:(lia)).
    rewrite (proj2 (Nat.eqb_neq i (length (SM.mc_kept mc)))) in Hknock by lia.
    rewrite andb_false_r in Hknock. exact Hknock. }
  split.
  { rewrite mr_fld3_in3 by lia. split; [rewrite length_app; cbn [length]; lia|].
    unfold w3. rewrite length_app. cbn [length].
    replace (Z.of_nat (length (SM.mc_kept mc) + 1)) with (Z.of_nat (length (SM.mc_kept mc)) + 1) by lia.
    reflexivity. }
  split; [rewrite mr_fld3_out by lia; exact Hgen|].
  rewrite mr_fld3_out by lia. exact Hrd.
Qed.

(* n_kept = 8: only refused one more *)
Lemma mr_enc_full : forall knock (rd rd' : reader) c mc line,
  sa_mconfp knock rd c mc -> length (SM.mc_kept mc) = 8%nat -> SM.mc_refused mc + 1 < 2 ^ 32 ->
  sa_val rd' (c + SP.MC_REFUSED) 4 (SM.mc_refused mc + 1) ->
  (forall a, c <= a < c + SP.SEG_M_SIZE -> ~ (c + SP.MC_REFUSED <= a < c + SP.MC_REFUSED + 4) -> rd' a = rd a) ->
  sa_mconf rd' c (SM.m_refuse mc line knock).
Proof.
intros knock rd rd' c mc line HP H8 Hrf HrfV Hfr.
pose proof (mr_fields knock rd c mc HP) as (_ & _ & [Hr0 _] & _ & _ & _ & _ & _).
rewrite (mr_m_refuse_full mc line knock H8).
destruct HP as [bs [Hb HE]].
unfold SP.mconf_encp, SP.fldz in HE.
destruct HE as (HLb & Hseg32 & Hsegs & Hn & Hov & Hrefd & HKL & Hkept & Hknock & Hnk & Hgen & Hrd).
set (w1 := Mem.le4 (Z_to_bv 64 (SM.mc_refused mc + 1))).
assert (L1 : length w1 = 4%nat) by (unfold w1; apply Mem.length_le4).
unfold SP.MC_N, SP.MC_OVERFLOW, SP.MC_REFUSED, SP.MC_KEPT, SP.MC_KNOCK, SP.MC_NKEPT, SP.MC_GEN, SP.MC_READING,
  SP.SEG_M_SIZE in *.
unfold sa_mconf, sa_mconfp.
exists (mr_upd bs (Z.to_nat 8200) w1).
assert (S1 : (Z.to_nat 8200 + length w1 <= length bs)%nat) by lia.
split.
- intros i Hi. rewrite mr_length_upd in Hi by exact S1.
  destruct (Nat.lt_ge_cases i (Z.to_nat 8200)) as [Hc|Hc];
    [|destruct (Nat.lt_ge_cases i (Z.to_nat 8200 + 4)) as [Hc'|Hc']].
  + rewrite mr_nth_upd_out by lia. rewrite Hfr by lia. exact (Hb i Hi).
  + rewrite mr_nth_upd_in by lia.
    pose proof (HrfV (i - Z.to_nat 8200)%nat ltac:(lia)) as E.
    replace (c + 8200 + Z.of_nat (i - Z.to_nat 8200)) with (c + Z.of_nat i) in E by lia.
    rewrite E. f_equal. unfold w1. rewrite mr_le4_byte by lia. reflexivity.
  + rewrite mr_nth_upd_out by lia. rewrite Hfr by lia. exact (Hb i Hi).
- unfold SP.mconf_encp, SP.fldz.
  cbn [SM.mc_seg SM.mc_overflow SM.mc_refused SM.mc_kept SM.mc_gen SM.mc_reading].
  unfold SP.MC_N, SP.MC_OVERFLOW, SP.MC_REFUSED, SP.MC_KEPT, SP.MC_KNOCK, SP.MC_NKEPT, SP.MC_GEN, SP.MC_READING,
    SP.SEG_M_SIZE.
  split; [rewrite mr_length_upd by exact S1; lia|].
  split; [exact Hseg32|].
  split; [intros i Hi; rewrite mr_fld_upd_out by lia; exact (Hsegs i Hi)|].
  split; [rewrite mr_fld_upd_out by lia; exact Hn|].
  split; [rewrite mr_fld_upd_out by lia; exact Hov|].
  split; [rewrite mr_fld_upd_in by lia; split; [lia | reflexivity]|].
  split; [exact HKL|].
  split.
  { intros i Hi. destruct (Hkept i Hi) as [Hcs Hfl]. split; rewrite mr_fld_upd_out by lia; assumption. }
  split; [intros i Hi; lia|].
  split; [rewrite mr_fld_upd_out by lia; exact Hnk|].
  split; [rewrite mr_fld_upd_out by lia; exact Hgen|].
  rewrite mr_fld_upd_out by lia. exact Hrd.
Qed.
