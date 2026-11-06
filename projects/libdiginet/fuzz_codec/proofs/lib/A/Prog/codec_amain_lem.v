(* Facts several segments of the image-A walk of LLVMFuzzerTestOneInput share (lib/A/Prog/codec_amain_inv.v), from
   its review (D3-D5):
   - the codes owe() and the encoders return, and the agreement of the encoder with owe() on a record of the cuts
     (enc_agreeZ, enc_kZ_rc_int), the length of the command the encoder leaves in k.out (enc_kZ_out_len);
   - the premises of the three record checks at CHK (amain_chk_facts);
   - the personality and spec-desk bytes the encoders, owe() and RD12 read, from the read-only image, and their
     marks in every state (adesk_bytes_of_pd, adesk_usable_of_pd, pers_argA_of_pdA).
   owe_codesA is lib/Prog/codec_main_owe_lib.v:125-137's owe_codes (the plain walk), restated here. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0s YK14 YK15 YK18 YP09 YI00 YI04 YI08 YI09 YI16 YN3v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACeh ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgSat CPgWalk CPgWalkImg.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ================================ the codes ================================ *)
Definition code_okA (r : Z) : Prop := r = 0 \/ r = -1 \/ r = -5 \/ r = -10 \/ r = -11.

Lemma owe_codesA : forall kind od a b c delta bytes n, code_okA (fst (owe_spec kind od a b c delta bytes n)).
Proof.
intros. unfold owe_spec, code_okA, E_ARG, E_RANGE, E_SPACE, E_REFUSED.
destruct od as [d|]; cbv beta iota zeta;
repeat (match goal with
        | |- context [if ?c then _ else _] => destruct c
        | |- context [match ?x with pair _ _ => _ end] => destruct x
        end; cbv beta iota);
cbn [fst]; lia.
Qed.

Lemma desk_ok_of_pdA : forall pv dv od, pd_okA pv dv od -> od_ok od.
Proof. intros pv dv od [(_ & _ & ->) | [(_ & _ & ->) | (_ & _ & ->)]]; unfold od_ok; tauto. Qed.

(* the encoder's code is owe()'s, and on success its command is owe()'s (codec_agree.agree_all) *)
Lemma enc_agreeZ : forall k od,
0 <= kz_kind k <= 11 -> pd_okA (kz_p k) (kz_desk k) od -> rdr_kZ k ->
fst (enc_kZ k od) = fst (owe_kZ k od) /\
(fst (enc_kZ k od) = 0 -> snd (enc_kZ k od) = Some (snd (owe_kZ k od))).
Proof.
intros k od Hk Hpd Hr.
pose proof (agree_all (kz_kind k) od (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k)
  Hk (desk_ok_of_pdA _ _ _ Hpd) Hr) as A.
unfold agrees in A. unfold enc_kZ, owe_kZ.
destruct (enc_of_call _ _ _ _ _ _ _ _) as [rc o]. cbn [fst snd] in *.
destruct A as [A1 A2]. split; [symmetry; exact A1 | exact A2].
Qed.

Lemma enc_kZ_code : forall k od,
0 <= kz_kind k <= 11 -> pd_okA (kz_p k) (kz_desk k) od -> rdr_kZ k -> code_okA (fst (enc_kZ k od)).
Proof.
intros k od Hk Hpd Hr. destruct (enc_agreeZ k od Hk Hpd Hr) as [E _]. rewrite E. apply owe_codesA.
Qed.

Lemma enc_kZ_rc_int : forall k od, enc_okZ k od -> - 2 ^ 31 <= fst (enc_kZ k od) < 2 ^ 31.
Proof.
intros k od (Hk & Hpd & Hr & _). pose proof (enc_kZ_code k od Hk Hpd Hr) as C. unfold code_okA in C. lia.
Qed.
Lemma rec_kZ_rc_int : forall k od, rec_okZ k od -> - 2 ^ 31 <= fst (enc_kZ k od) < 2 ^ 31.
Proof.
intros k od (Hk & Hpd & Hr & _). pose proof (enc_kZ_code k od Hk Hpd Hr) as C. unfold code_okA in C. lia.
Qed.

(* ================================ the command in k.out ================================ *)
Lemma fa5_len : length fa5 = 32%nat.
Proof. reflexivity. Qed.

Lemma cmdZ_pre_len : forall bs, (length bs <= 24)%nat ->
length (map u8 bs ++ skipn (length bs) (firstn 24 fa5)) = 24%nat.
Proof.
intros bs Hb. rewrite length_app, length_map, length_skipn, length_firstn, fa5_len. lia.
Qed.

Lemma cmd_outZ_some_len : forall bs key dp, (length bs <= 24)%nat ->
length (cmd_outZ fa5 (Some (bs, key, dp))) = 32%nat.
Proof.
intros bs key dp Hb. unfold cmd_outZ.
rewrite app_assoc. rewrite length_app, cmdZ_pre_len by exact Hb. reflexivity.
Qed.

Lemma enc_kZ_out_len_of : forall k od,
0 <= kz_kind k <= 11 -> pd_okA (kz_p k) (kz_desk k) od -> rdr_kZ k ->
length (cmd_outZ fa5 (snd (enc_kZ k od))) = 32%nat.
Proof.
intros k od Hk Hpd Hr. destruct (enc_agreeZ k od Hk Hpd Hr) as [E1 E2].
destruct (Z.eq_dec (fst (enc_kZ k od)) 0) as [H0 | Hne].
- rewrite (E2 H0).
  pose proof (owe_ok_wf (kz_kind k) od (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k)
    Hk (desk_ok_of_pdA _ _ _ Hpd) Hr) as W.
  change (owe_spec (kz_kind k) od (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k)) with (owe_kZ k od) in W.
  rewrite <- E1 in W. specialize (W H0).
  destruct (snd (owe_kZ k od)) as [[bs key] dp]. destruct W as (HL & _).
  apply cmd_outZ_some_len. exact HL.
- unfold enc_kZ in *. rewrite (enc_fail_none _ _ _ _ _ _ _ _ Hne). reflexivity.
Qed.

Lemma enc_kZ_out_len : forall k od, enc_okZ k od -> length (cmd_outZ fa5 (snd (enc_kZ k od))) = 32%nat.
Proof. intros k od (Hk & Hpd & Hr & _). exact (enc_kZ_out_len_of k od Hk Hpd Hr). Qed.

(* the fields of cmd_outZ fa5 on success *)
Lemma nth_app_offZ : forall (A B : list Z) (i n j : nat) d,
length A = n -> i = (j + n)%nat -> nth i (A ++ B) d = nth j B d.
Proof. intros A B i n j d HA Hi. subst i n. rewrite app_nth2 by lia. f_equal. lia. Qed.

Lemma skipn_app_offZ : forall (A B : list Z) (i n j : nat),
length A = n -> i = (j + n)%nat -> skipn i (A ++ B) = skipn j B.
Proof. intros A B i n j HA Hi. subst i n. rewrite skipn_app, skipn_all2 by lia. cbn [app]. f_equal. lia. Qed.

Lemma cmd_outZ_some : forall bs key dp,
cmd_outZ fa5 (Some (bs, key, dp)) =
(map u8 bs ++ skipn (length bs) (firstn 24 fa5)) ++
([u8 (Z.of_nat (length bs)); u8 dp] ++ firstn 2 (skipn 26 fa5) ++ le4Z key).
Proof. intros bs key dp. unfold cmd_outZ. rewrite <- !app_assoc. reflexivity. Qed.

Lemma u8_smallZ : forall x, 0 <= x < 256 -> u8 x = x.
Proof. intros x Hx. unfold u8. apply Z.mod_small. exact Hx. Qed.

Lemma cmd_outZ_len_field : forall bs key dp, (length bs <= 24)%nat ->
cmd_lenZ (cmd_outZ fa5 (Some (bs, key, dp))) = Z.of_nat (length bs).
Proof.
intros bs key dp Hb. unfold cmd_lenZ. rewrite cmd_outZ_some.
rewrite (nth_app_offZ _ _ 24%nat 24%nat 0%nat) by first [apply cmdZ_pre_len; exact Hb | reflexivity].
cbn [app nth]. apply u8_smallZ. lia.
Qed.

Lemma cmd_outZ_display_field : forall bs key dp, (length bs <= 24)%nat -> 0 <= dp < 256 ->
cmd_displayZ (cmd_outZ fa5 (Some (bs, key, dp))) = dp.
Proof.
intros bs key dp Hb Hd. unfold cmd_displayZ. rewrite cmd_outZ_some.
rewrite (nth_app_offZ _ _ 25%nat 24%nat 1%nat) by first [apply cmdZ_pre_len; exact Hb | reflexivity].
cbn [app nth]. apply u8_smallZ. exact Hd.
Qed.

Lemma le4Z_fold : forall k, 0 <= k < 2 ^ 32 ->
fold_right (fun b acc => b + 256 * acc) 0 (firstn 4 (le4Z k)) = k.
Proof.
intros k Hk. unfold le4Z. cbn [firstn fold_right].
assert (D1 : k / 65536 = k / 256 / 256) by (rewrite Z.div_div by lia; reflexivity).
assert (D2 : k / 16777216 = k / 256 / 256 / 256) by (rewrite !Z.div_div by lia; reflexivity).
rewrite D1, D2.
set (q1 := k / 256). set (q2 := q1 / 256). set (q3 := q2 / 256).
pose proof (Z.div_mod k 256 ltac:(lia)) as E0. pose proof (Z.mod_pos_bound k 256 ltac:(lia)) as B0.
pose proof (Z.div_mod q1 256 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound q1 256 ltac:(lia)) as B1.
pose proof (Z.div_mod q2 256 ltac:(lia)) as E2. pose proof (Z.mod_pos_bound q2 256 ltac:(lia)) as B2.
assert (Hq3 : 0 <= q3 < 256).
{ subst q3 q2 q1. rewrite !Z.div_div by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
rewrite (Z.mod_small q3 256) by exact Hq3.
fold q1 in E0. fold q2 in E1. fold q3 in E2. lia.
Qed.

Lemma cmd_outZ_key_field : forall bs key dp, (length bs <= 24)%nat -> 0 <= key < 2 ^ 32 ->
cmd_keyZ (cmd_outZ fa5 (Some (bs, key, dp))) = key.
Proof.
intros bs key dp Hb Hk. unfold cmd_keyZ. rewrite cmd_outZ_some.
rewrite (skipn_app_offZ _ _ 28%nat 24%nat 4%nat) by first [apply cmdZ_pre_len; exact Hb | reflexivity].
change (skipn 4 ([u8 (Z.of_nat (length bs)); u8 dp] ++ firstn 2 (skipn 26 fa5) ++ le4Z key)) with (le4Z key).
apply le4Z_fold. exact Hk.
Qed.

Lemma cmd_outZ_firstn : forall bs key dp,
firstn (length bs) (cmd_outZ fa5 (Some (bs, key, dp))) = map u8 bs.
Proof.
intros bs key dp. rewrite cmd_outZ_some, <- app_assoc.
rewrite <- (length_map u8 bs), firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r.
Qed.

(* ================================ the record checks at CHK ================================ *)
(* the premises of cdc_check_refusal_specX, cdc_check_range_specX and cdc_check_bytes_specX at the CHK cut *)
Lemma amain_chk_facts : forall k od, rec_okZ k od -> kz_rc k = fst (enc_kZ k od) -> owe_want_okZ k od ->
~ (kz_kind k = 11 /\ kz_b k = 0x70 /\ kz_rc k = 0) /\ (kz_rc k <> 0 -> kz_out k = kz_before k) /\
kz_rc k = kz_want_rc k /\
(kz_rc k = 0 -> kz_want_len k = cmd_lenZ (kz_out k) /\ kz_want_len k <= 24 /\
   firstn (Z.to_nat (kz_want_len k)) (kz_out k) = firstn (Z.to_nat (kz_want_len k)) (kz_want k) /\
   cmd_keyZ (kz_out k) = kz_want_key k /\ cmd_displayZ (kz_out k) = kz_want_display k).
Proof.
intros k od HR Hrc [Hwrc Hw].
pose proof HR as (Hk & Hpd & Hr & Hbe & Hout).
destruct (enc_agreeZ k od Hk Hpd Hr) as [A1 A2].
pose proof (owe_ok_wf (kz_kind k) od (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k)
  Hk (desk_ok_of_pdA _ _ _ Hpd) Hr) as OW.
change (owe_spec (kz_kind k) od (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k)) with (owe_kZ k od) in OW.
split; [|split; [|split]].
- intros (H11 & Hb & H0). rewrite Hrc in H0. unfold enc_kZ in H0. rewrite H11 in H0.
  exact (refusal od (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k) Hb H0).
- intros Hne. rewrite Hout, Hbe. rewrite Hrc in Hne. unfold enc_kZ in *.
  rewrite (enc_fail_none _ _ _ _ _ _ _ _ Hne). reflexivity.
- rewrite Hrc, Hwrc. exact A1.
- intros H0. rewrite Hrc in H0. pose proof (A2 H0) as ES.
  assert (W0 : fst (owe_kZ k od) = 0) by (rewrite <- A1; exact H0).
  specialize (OW W0). rewrite W0 in Hw. cbn [Z.eqb] in Hw.
  assert (EO : kz_out k = cmd_outZ fa5 (Some (snd (owe_kZ k od)))) by (rewrite Hout, ES; reflexivity).
  revert EO Hw OW. destruct (snd (owe_kZ k od)) as [[bs key] dp]. intros EO Hw OW.
  destruct Hw as (HL & HF & HKY & HDP). destruct OW as (OL & _ & OK & OD).
  rewrite EO, HL, HKY, HDP, Nat2Z.id, HF.
  split; [symmetry; apply cmd_outZ_len_field; exact OL|].
  split; [lia|].
  split; [apply cmd_outZ_firstn|].
  split; [apply cmd_outZ_key_field; [exact OL | exact OK]|].
  apply cmd_outZ_display_field; [exact OL | lia].
Qed.

(* ================================ the personality and spec-desk bytes ================================ *)
(* the image's bytes: personalities[0] + 16 = Control|24's four fields, + 40 = ProControl's; SPEC_C24 + 8 and
   SPEC_PC + 8 the same four *)
Lemma pers_img_bytes : forall pv dv d i, pd_okA pv dv (Some d) -> 0 <= i < 4 ->
option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 (pv + 16 + i))) =
Some (nth (Z.to_nat i) [d_dev d; d_strips d; d_chars d; d_counter d] 0) /\
option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 (dv + 8 + i))) =
Some (nth (Z.to_nat i) [d_dev d; d_strips d; d_chars d; d_counter d] 0).
Proof.
intros pv dv d i [(_ & _ & H) | [(-> & -> & H) | (-> & -> & H)]] Hi; [discriminate H | injection H as -> ..];
assert (Ei : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia;
destruct Ei as [-> | [-> | [-> | ->]]]; split; vm_compute; reflexivity.
Qed.

Lemma pd_range_A : forall pv dv d, pd_okA pv dv (Some d) ->
(pv = CA_PERS \/ pv = CA_PERS + 24) /\ (dv = CM_SPEC_C24 \/ dv = CM_SPEC_PC) /\
0 <= d_dev d < 256 /\ 0 <= d_strips d < 256 /\ 0 <= d_chars d < 256 /\ 0 <= d_counter d < 256.
Proof.
intros pv dv d [(_ & _ & H) | [(-> & -> & H) | (-> & -> & H)]]; [discriminate H | injection H as -> ..];
(split; [tauto|]); (split; [tauto|]); vm_compute; repeat split; discriminate.
Qed.

Lemma in_ro_pers : forall pv dv d i, pd_okA pv dv (Some d) -> 0 <= i < 4 ->
in_ro_tfa (pv + 16 + i) /\ in_ro_tfa (dv + 8 + i) /\ lib_const_addr (pv + 16 + i) /\ lib_const_addr (dv + 8 + i).
Proof.
intros pv dv d i H Hi. destruct (pd_range_A pv dv d H) as (Hp & Hd & _).
unfold in_ro_tfa, lib_const_addr, CA_PERS, CM_SPEC_C24, CM_SPEC_PC in *.
destruct Hp as [-> | ->]; destruct Hd as [-> | ->]; repeat split; try (right; lia); lia.
Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TfibLib B.

(* one byte of the image's read-only data, as the walk's readers see it *)
Lemma adesk_bytes_of_pd : forall (W : world tfibsegs) mem pv dv d i,
arodata_ok B (aview tfibsegs (w_H W) mem) -> pd_okA pv dv (Some d) -> 0 <= i < 4 ->
aview tfibsegs (w_H W) mem (dv + 8 + i) = Some (nth (Z.to_nat i) [d_dev d; d_strips d; d_chars d; d_counter d] 0).
Proof.
intros W mem pv dv d i HR H Hi. destruct (in_ro_pers pv dv d i H Hi) as (_ & Hro & _ & Hlc).
destruct (tl_lib_consts B TL _ Hlc) as [Ho He].
rewrite (HR _ Hro Ho He). exact (proj2 (pers_img_bytes pv dv d i H Hi)).
Qed.
Lemma apers_bytes_of_pd : forall (W : world tfibsegs) mem pv dv d i,
arodata_ok B (aview tfibsegs (w_H W) mem) -> pd_okA pv dv (Some d) -> 0 <= i < 4 ->
aview tfibsegs (w_H W) mem (pv + 16 + i) = Some (nth (Z.to_nat i) [d_dev d; d_strips d; d_chars d; d_counter d] 0).
Proof.
intros W mem pv dv d i HR H Hi. destruct (in_ro_pers pv dv d i H Hi) as (Hro & _ & Hlc & _).
destruct (tl_lib_consts B TL _ Hlc) as [Ho He].
rewrite (HR _ Hro Ho He). exact (proj1 (pers_img_bytes pv dv d i H Hi)).
Qed.

(* the four bytes are marked usable in every AR state (globs_marked of the rows SPEC_C24 / SPEC_PC /
   personalities) *)
Lemma adesk_usable_of_pd : forall pv dv d,
globs_marked tfibsegs B CODEC_GLOBS -> img_shadow_vis tfibsegs B -> pd_okA pv dv (Some d) ->
cimg_usable tfibsegs B (dv + 8) 4 /\ cimg_usable tfibsegs B (pv + 16) 4.
Proof.
intros pv dv d GM IV H. destruct (pd_range_A pv dv d H) as (Hp & Hd & _).
split.
- destruct Hd as [-> | ->].
  + apply (sat_img_usable tfibsegs B CODEC_GLOBS CM_SPEC_C24 16); [exact GM | exact cg_SPEC_C24 | exact IV | ..];
    cbv [IMG_LO IMG_HI IMG_TOP CM_SPEC_C24]; lia.
  + apply (sat_img_usable tfibsegs B CODEC_GLOBS CM_SPEC_PC 16); [exact GM | exact cg_SPEC_PC | exact IV | ..];
    cbv [IMG_LO IMG_HI IMG_TOP CM_SPEC_PC]; lia.
- apply (sat_img_usable tfibsegs B CODEC_GLOBS CA_PERS 48); [exact GM | exact cg_PERS | exact IV | ..];
  destruct Hp as [-> | ->]; cbv [IMG_LO IMG_HI IMG_TOP CA_PERS]; lia.
Qed.

(* a byte the image holds is readable through the restricted memory as the value aview gives *)
Lemma val_mem1_of_aviewA : forall H (m : word -> option byte) a v, aview tfibsegs H m a = Some v ->
val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv. destruct (aview_byte tfibsegs H m a v Hv) as (b & Hb & -> & _).
pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
apply cpg_val_mem1; [exact Rb|]. rewrite Hb, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* the encoders' personality premise (lib/A/Prog/CPgBase.v pers_argA) from the record's pair *)
Lemma pers_argA_of_pdA : forall (W : world tfibsegs) mem sp T pv dv od,
globs_marked tfibsegs B CODEC_GLOBS -> img_shadow_vis tfibsegs B ->
arodata_ok B (aview tfibsegs (w_H W) mem) -> pd_okA pv dv od -> CA_RHI <= sp - T ->
pers_argA tfibsegs B W mem sp T pv od.
Proof.
intros W mem sp T pv dv od GM IV HR H Hwin.
destruct od as [d|]; [| destruct H as [(-> & _) | [(_ & _ & Hd) | (_ & _ & Hd)]]; [reflexivity | discriminate Hd ..]].
destruct (pd_range_A pv dv d H) as (Hp & _ & R1 & R2 & R3 & R4).
unfold pers_argA.
split; [destruct Hp as [-> | ->]; unfold CA_PERS; lia|].
split; [destruct Hp as [-> | ->]; unfold CA_PERS; lia|].
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
split.
- intros j Hj. cbn [length] in Hj.
  assert (Ej : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3)%nat) by lia.
  pose proof (apers_bytes_of_pd W mem pv dv d (Z.of_nat j) HR H ltac:(lia)) as Hb.
  rewrite Nat2Z.id in Hb.
  split; [apply val_mem1_of_aviewA; exact Hb|].
  destruct Ej as [-> | [-> | [-> | ->]]]; cbn [nth]; lia.
- destruct (adesk_usable_of_pd pv dv d GM IV H) as [_ HU].
  split; [destruct Hp as [-> | ->]; unfold CA_PERS; lia|].
  split; [lia|]. split; [destruct Hp as [-> | ->]; unfold CA_PERS; lia|].
  split; [left; destruct Hp as [-> | ->]; unfold CA_PERS, kLowMemEnd; lia|].
  split; [left; unfold CA_RHI in Hwin; destruct Hp as [-> | ->]; unfold CA_PERS; lia|].
  split; [|exact HU].
  intros a Ha. destruct (in_ro_pers pv dv d (a - pv - 16) H ltac:(lia)) as (_ & _ & Hlc & _).
  replace (pv + 16 + (a - pv - 16)) with a in Hlc by lia.
  split; [|exact (tl_lib_consts B TL a Hlc)].
  unfold in_img. eexists. split; [right; right; left; reflexivity|].
  match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
  change lo with l; change sz with h end.
  destruct Hp as [-> | ->]; unfold CA_PERS in *; lia.
Qed.
End p.

(* ================================ the read-only image at a cut ================================ *)
Lemma arodata_ok_of_P : forall B rd, arodata_okP tfibsegs CA_RLO CA_RHI B rd -> arodata_ok B rd.
Proof. intros B rd H a Ha. apply H. exact Ha. Qed.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
(* the entry's read-only image, kept along the walk's journal to any state of a cut *)
Lemma arodata_ok_at : forall (g : ectx) own ly2 S2 W2 mem2 md2 k,
e_pre B MT K XM_LIB g ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) own ly2 S2 W2 mem2 md2 k ->
arodata_ok B (aview tfibsegs (w_H W2) mem2).
Proof.
intros g own ly2 S2 W2 mem2 md2 k HP HJ.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
exact (arodata_ok_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ (arodata_ok_of_P B _ HRO)).
Qed.
End r.
