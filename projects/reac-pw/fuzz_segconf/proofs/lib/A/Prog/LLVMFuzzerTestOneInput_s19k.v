(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the kit of _s19 of the
   harness walk (segment S10, K8559c -> K856bc: check_refusals and the refusal loop 0x85630 <- 0x8568c with
   check_address and check_knock_refused). Reader-level facts of the two harness blocks c (struct reac_segconf,
   seg_spec.rconf_enc) and m (struct mconf, seg_spec.mconf_encp), and the model facts the three checks need
   (SegModel.segconf_agrees on the decoded payload). No function of the binary is proved here.
   rule 24: proves function LLVMFuzzerTestOneInput (reuse search: see the walk's shared brief; none: written new). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ============================== bytes through a reader ============================== *)
Lemma sk_nth_zs : forall (f : list byte) i, (i < length f)%nat ->
  nth i (seg_spec.zs f) 0 = bv_unsigned (nth i f ZB0).
Proof.
unfold seg_spec.zs. induction f as [|b f IH]; intros i Hi; cbn [length] in Hi; [lia|].
destruct i as [|i]; cbn [map nth]; [reflexivity|]. apply IH. lia.
Qed.
Lemma sk_le_nth : forall n z k (d : byte), (k < n)%nat ->
  nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma sk_le4_val : forall (rd : reader) a v, 0 <= v < 2 ^ 32 ->
  sa_bytes rd a (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 v))) -> sa_val rd a 4 v.
Proof.
intros rd a v Hv H. change (2 ^ 32) with 4294967296 in Hv. unfold sa_bytes in H. unfold sa_val. intros k Hk.
assert (Hl : length (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 v))) = 4%nat) by reflexivity.
rewrite H by (rewrite Hl; exact Hk).
f_equal. rewrite sk_le_nth by exact Hk.
rewrite !Z_to_bv_unsigned.
rewrite (bv_wrap_small 64 v) by (change (bv_modulus 64) with 18446744073709551616; lia).
unfold le_byte.
rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 4))) by (change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia).
change (bv_wrap 8 ?x) with (x mod 256). reflexivity.
Qed.
Lemma sk_bytes_fld : forall (rd : reader) a bs off n, sa_bytes rd a bs -> (off + n <= length bs)%nat ->
  sa_bytes rd (a + Z.of_nat off) (seg_spec.fld off n bs).
Proof.
intros rd a bs off n H Hle. unfold sa_bytes in *. intros i Hi.
assert (Hl : length (seg_spec.fld off n bs) = n)
  by (unfold seg_spec.fld; rewrite length_firstn, length_skipn; lia).
rewrite Hl in Hi.
unfold seg_spec.fld. rewrite nth_firstn.
replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
rewrite nth_skipn.
match goal with |- _ = Some (bv_unsigned (nth ?j bs ZB0)) =>
  replace (a + Z.of_nat off + Z.of_nat i) with (a + Z.of_nat j) by lia; apply H; lia end.
Qed.
Lemma sk_strz_of_cstr : forall (rd : reader) a cap s f, sa_bytes rd a f -> seg_spec.cstr_enc cap s f ->
  sa_strz rd a s /\ (length s < cap)%nat.
Proof.
intros rd a cap s f H Hc. unfold seg_spec.cstr_enc in Hc. destruct Hc as (Hlf & Hls & Hn0 & Hfs).
unfold sa_bytes in H. unfold sa_strz.
split; [|exact Hls]. split; [|exact Hn0].
unfold sa_zs. intros i Hi.
rewrite length_app in Hi. cbn [length] in Hi.
rewrite <- Hfs. rewrite nth_firstn.
replace (i <? S (length s))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite sk_nth_zs by lia.
apply H. lia.
Qed.
Lemma sk_val_of_u32 : forall (rd : reader) a v f, sa_bytes rd a f -> seg_spec.u32_enc v f ->
  sa_val rd a 4 v /\ 0 <= v < 2 ^ 32.
Proof.
intros rd a v f H Hu. unfold seg_spec.u32_enc in Hu. destruct Hu as [Hv Hf]. subst f.
split; [|exact Hv]. exact (sk_le4_val rd a v Hv H).
Qed.
Lemma sk_val_of_flag : forall (rd : reader) a b f, sa_bytes rd a f -> seg_spec.flag_enc b f ->
  sa_val rd a 4 (seg_spec.b2z b).
Proof.
intros rd a b f H Hf. unfold seg_spec.flag_enc in Hf. subst f.
apply sk_le4_val; [|exact H].
change (2 ^ 32) with 4294967296. destruct b; cbn [seg_spec.b2z]; lia.
Qed.
(* a C string whose NUL and the 8 bytes after it lie in a mapped range has its tail *)
Lemma sk_str_of_strz : forall (rd : reader) p s lo hi, sa_strz rd p s ->
  (forall x, lo <= x < hi -> exists v, rd x = Some v) -> lo <= p -> p + Z.of_nat (length s) + 8 <= hi ->
  sa_str rd p s.
Proof.
intros rd p s lo hi Hs Hm Hlo Hhi. unfold sa_str. split; [exact Hs|].
unfold sa_tail. intros x Hx.
pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as H8.
destruct (Hm x) as [v Hv]; [lia|]. rewrite Hv. congruence.
Qed.

(* ============================== the reader's block c ============================== *)
Lemma sk_rconf_refusal : forall (rd : reader) c rc i, sa_rconf rd c rc ->
  (i < length (SegModel.rc_refusal rc))%nat ->
  sa_strz rd (seg_spec.refusal_addr c i) (nth i (SegModel.rc_refusal rc) []) /\
  (length (nth i (SegModel.rc_refusal rc) []) < 200)%nat.
Proof.
intros rd c rc i Hc Hi. unfold sa_rconf in Hc. destruct Hc as (bs & Hb & Henc).
unfold seg_spec.rconf_enc in Henc. destruct Henc as (Hlen & _ & _ & _ & L8 & HR & _).
unfold seg_spec.SEG_C_SIZE in Hlen.
pose proof (HR i Hi) as Er.
set (kr := Z.to_nat seg_spec.RC_REFUSAL) in *. assert (Ekr : Z.of_nat kr = 11912) by reflexivity. clearbody kr.
destruct (sk_strz_of_cstr rd _ 200 _ _ (sk_bytes_fld rd c bs (kr + 200 * i) 200 Hb ltac:(lia)) Er) as [Hz Hl].
split; [|exact Hl].
replace (seg_spec.refusal_addr c i) with (c + Z.of_nat (kr + 200 * i))
  by (unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN; lia).
exact Hz.
Qed.
Lemma sk_rconf_nref : forall (rd : reader) c rc, sa_rconf rd c rc ->
  sa_val rd (c + seg_spec.RC_NREF) 4 (Z.of_nat (length (SegModel.rc_refusal rc))) /\
  (length (SegModel.rc_refusal rc) <= 8)%nat.
Proof.
intros rd c rc Hc. unfold sa_rconf in Hc. destruct Hc as (bs & Hb & Henc).
unfold seg_spec.rconf_enc in Henc. destruct Henc as (Hlen & _ & _ & _ & L8 & _ & HN & _).
split; [|exact L8].
unfold seg_spec.SEG_C_SIZE in Hlen. unfold seg_spec.fldz in HN.
set (kn := Z.to_nat seg_spec.RC_NREF) in *. assert (Ekn : Z.of_nat kn = 13512) by reflexivity. clearbody kn.
change (Z.to_nat 4) with 4%nat in HN.
destruct (sk_val_of_u32 rd _ _ _ (sk_bytes_fld rd c bs kn 4 Hb ltac:(lia)) HN) as [Hv _].
replace (c + seg_spec.RC_NREF) with (c + Z.of_nat kn) by (unfold seg_spec.RC_NREF; lia).
exact Hv.
Qed.
Lemma sk_rconf_mapped : forall (rd : reader) c rc x, sa_rconf rd c rc -> c <= x < c + seg_spec.SEG_C_SIZE ->
  exists v, rd x = Some v.
Proof.
intros rd c rc x Hc Hx. unfold sa_rconf in Hc. destruct Hc as (bs & Hb & Henc).
unfold seg_spec.rconf_enc in Henc. destruct Henc as (Hlen & _).
unfold seg_spec.SEG_C_SIZE in Hlen, Hx. unfold sa_bytes in Hb.
pose proof (Hb (Z.to_nat (x - c)) ltac:(lia)) as E.
rewrite Z2Nat.id in E by lia.
replace (c + (x - c)) with x in E by lia.
eexists; exact E.
Qed.

(* ============================== the model's block m ============================== *)
Lemma sk_mconf_kept : forall (rd : reader) m mc i, sa_mconf rd m mc -> (i < length (SegModel.mc_kept mc))%nat ->
  sa_strz rd (seg_spec.kept_addr m i) (fst (nth i (SegModel.mc_kept mc) ([], false))) /\
  (length (fst (nth i (SegModel.mc_kept mc) ([], false))) < 112)%nat /\
  sa_val rd (m + seg_spec.MC_KNOCK + 4 * Z.of_nat i) 4 (seg_spec.b2z (snd (nth i (SegModel.mc_kept mc) ([], false)))).
Proof.
intros rd m mc i Hm Hi. unfold sa_mconf, sa_mconfp in Hm. destruct Hm as (bs & Hb & Henc).
unfold seg_spec.mconf_encp in Henc. destruct Henc as (Hlen & _ & _ & _ & _ & _ & L8 & HK & _).
unfold seg_spec.SEG_M_SIZE in Hlen.
destruct (HK i Hi) as [Ek Fk].
set (kk := Z.to_nat seg_spec.MC_KEPT) in *. assert (Ekk : Z.of_nat kk = 8204) by reflexivity. clearbody kk.
set (kn := Z.to_nat seg_spec.MC_KNOCK) in *. assert (Ekn : Z.of_nat kn = 9100) by reflexivity. clearbody kn.
destruct (sk_strz_of_cstr rd _ 112 _ _ (sk_bytes_fld rd m bs (kk + 112 * i) 112 Hb ltac:(lia)) Ek) as [Hz Hl].
pose proof (sk_val_of_flag rd _ _ _ (sk_bytes_fld rd m bs (kn + 4 * i) 4 Hb ltac:(lia)) Fk) as Hv.
split; [|split; [exact Hl|]].
- replace (seg_spec.kept_addr m i) with (m + Z.of_nat (kk + 112 * i))
    by (unfold seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN; lia).
  exact Hz.
- replace (m + seg_spec.MC_KNOCK + 4 * Z.of_nat i) with (m + Z.of_nat (kn + 4 * i))
    by (unfold seg_spec.MC_KNOCK; lia).
  exact Hv.
Qed.
Lemma sk_mconf_nkept : forall (rd : reader) m mc, sa_mconf rd m mc ->
  sa_val rd (m + seg_spec.MC_NKEPT) 4 (Z.of_nat (length (SegModel.mc_kept mc))) /\
  (length (SegModel.mc_kept mc) <= 8)%nat.
Proof.
intros rd m mc Hm. unfold sa_mconf, sa_mconfp in Hm. destruct Hm as (bs & Hb & Henc).
unfold seg_spec.mconf_encp in Henc. destruct Henc as (Hlen & _ & _ & _ & _ & _ & L8 & _ & _ & HN & _).
split; [|exact L8].
unfold seg_spec.SEG_M_SIZE in Hlen. unfold seg_spec.fldz in HN.
set (kn := Z.to_nat seg_spec.MC_NKEPT) in *. assert (Ekn : Z.of_nat kn = 9132) by reflexivity. clearbody kn.
change (Z.to_nat 4) with 4%nat in HN.
destruct (sk_val_of_u32 rd _ _ _ (sk_bytes_fld rd m bs kn 4 Hb ltac:(lia)) HN) as [Hv _].
replace (m + seg_spec.MC_NKEPT) with (m + Z.of_nat kn) by (unfold seg_spec.MC_NKEPT; lia).
exact Hv.
Qed.
Lemma sk_mconf_mapped : forall (rd : reader) m mc x, sa_mconf rd m mc -> m <= x < m + seg_spec.SEG_M_SIZE ->
  exists v, rd x = Some v.
Proof.
intros rd m mc x Hm Hx. unfold sa_mconf, sa_mconfp in Hm. destruct Hm as (bs & Hb & Henc).
unfold seg_spec.mconf_encp in Henc. destruct Henc as (Hlen & _).
unfold seg_spec.SEG_M_SIZE in Hlen, Hx. unfold sa_bytes in Hb.
pose proof (Hb (Z.to_nat (x - m)) ltac:(lia)) as E.
rewrite Z2Nat.id in E by lia.
replace (m + (x - m)) with x in E by lia.
eexists; exact E.
Qed.

(* ============================== the model ============================== *)
(* the two checks of the refusal part of SegModel.harness_ok, on the decoded payload of any input *)
Lemma sk_harness_checks : forall pl : list byte,
  SegModel.check_refusals (seg_spec.seg_rc (SegModel.run (seg_spec.seg_pay pl)))
    (seg_spec.seg_mc (SegModel.run (seg_spec.seg_pay pl))) = true /\
  SegModel.check_kept_all (SegModel.rc_refusal (seg_spec.seg_rc (SegModel.run (seg_spec.seg_pay pl))))
    (SegModel.mc_kept (seg_spec.seg_mc (SegModel.run (seg_spec.seg_pay pl)))) = true.
Proof.
intros pl.
assert (Hr : Forall (fun b => 0 <= b < 256) (seg_spec.zs pl)).
{ unfold seg_spec.zs. apply Forall_forall. intros z Hz. apply in_map_iff in Hz. destruct Hz as [b [Eb _]].
  subst z. pose proof (bv_unsigned_in_range _ b) as R. change (bv_modulus 8) with 256 in R. lia. }
pose proof (SegModel.segconf_agrees (seg_spec.zs pl) Hr) as H.
unfold SegModel.harness_ok in H. unfold seg_spec.seg_pay, seg_spec.seg_in.
revert H. destruct (SegModel.run (SegModel.decode (seg_spec.zs pl))) as [[c m] ret]. intros H.
cbv beta iota in H. cbn [seg_spec.seg_rc seg_spec.seg_mc fst snd].
apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
apply andb_prop in H as [H HD]. apply andb_prop in H as [_ HC].
split; [exact HC | exact HD].
Qed.
Lemma sk_refusals_len : forall rc mc, SegModel.check_refusals rc mc = true ->
  length (SegModel.rc_refusal rc) = length (SegModel.mc_kept mc).
Proof.
intros rc mc H. unfold SegModel.check_refusals in H. apply andb_prop in H as [_ H2].
apply Nat.eqb_eq in H2. exact H2.
Qed.
Lemma sk_kept_nth : forall gs ws i, SegModel.check_kept_all gs ws = true -> (i < length gs)%nat ->
  (i < length ws)%nat -> SegModel.check_kept (nth i gs []) (nth i ws ([], false)) = true.
Proof.
induction gs as [|g gs IH]; intros [|w ws] i H Hg Hw; cbn [length] in Hg, Hw; try lia.
cbn [SegModel.check_kept_all] in H. apply andb_prop in H as [H1 H2].
destruct i as [|i]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.
