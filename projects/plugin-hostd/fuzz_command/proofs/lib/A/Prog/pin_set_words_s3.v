(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of descriptors_get on plugin-hostd/fuzz_command.asan, after
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v and ACh1.v .. ACh8.v (the segment walk of cgif_close) over
   fuzz_command's listing: the entry segment to record()'s join (descriptors_get_s4.v) composed with the walk from
   the join through the tail jump into answer (descriptors_get_s3.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/descriptors_get.v, with its module paths and module names changed; 168 of its 191 lines of code are new or changed and 39 lines of the source are left out. *)
(* The structural facts the ASan walk of pin_set_words (lib/A/Prog/pin_set_words_c.v) uses at its two recorder
   calls: each word of verbs_receive's token array (atoks_atA, lib/A/Prog/CmdRep.v:42-46), and its tail after the
   8-byte prefix "verdict=", is a string argument pins_set may take (astr_argA, CmdRep.v:139-150); the meter, live
   bytes and events of pins_set (lib/A/Prog/pins_set_c.v:54-69) and lv2_refusals_forget
   (lib/A/Prog/lv2_refusals_forget_c.v:47-56) fit in pin_set_words' own (pin_set_words_c.v:61-80).
   The word's block is a live block of the allocator that the recorder does not own, so it is apart from each of
   the recorder's blocks O (sep_blocks, lib/Reusable/YCbq.v:456-458). The answer text "resp <code>" has at most
   16 bytes for every code: dec writes at most 10 digits (lib/Prog/RecFacts.v:68-77). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c hand_back_c answer_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import pins_set_c lv2_refusals_forget_c pin_set_words_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.
Module PVR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.VerbsRun.

(* the string at p + 1 is the tail of the string at p *)
Lemma psw3_astr_tl : forall rd p a w, astr_atR rd p (a :: w) -> astr_atR rd (p + 1) w.
Proof.
  intros rd p a w [Hb Hn]. split.
  - unfold abytes_atR in Hb |- *. intros i Hi. specialize (Hb (S i)). cbn [app length nth] in Hb.
    rewrite Nat2Z.inj_succ in Hb. replace (p + Z.succ (Z.of_nat i)) with (p + 1 + Z.of_nat i) in Hb by lia.
    apply Hb. lia.
  - intros H. apply Hn. right. exact H.
Qed.

(* the string at p + k is the k-byte tail of the string at p (PaArt.v's astr_atR_skipn) *)
Lemma psw3_astr_skipn : forall rd k p w, (k <= length w)%nat -> astr_atR rd p w ->
  astr_atR rd (p + Z.of_nat k) (skipn k w).
Proof.
  intros rd k. induction k as [|k IH]; intros p w Hk H.
  - replace (p + Z.of_nat 0) with p by lia. exact H.
  - destruct w as [|a w]; [cbn [length] in Hk; lia|].
    cbn [skipn length] in Hk |- *.
    replace (p + Z.of_nat (S k)) with (p + 1 + Z.of_nat k) by lia.
    apply IH; [lia | exact (psw3_astr_tl rd p a w H)].
Qed.

Lemma psw3_len_skipn : forall k (w : list byte), (k <= length w)%nat ->
  Z.of_nat (length (skipn k w)) = Z.of_nat (length w) - Z.of_nat k.
Proof. intros k w H. rewrite length_skipn. rewrite Nat2Z.inj_sub by exact H. reflexivity. Qed.

Lemma psw3_req_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); cbv beta iota; lia. Qed.

(* a large nat literal is Nat.of_num_uint of its digits, which lia does not read: move the bound to Z *)
Lemma psw3_nat8192 : forall n, (n <= 8192)%nat -> Z.of_nat n <= 8192.
Proof.
  intros n H. pose proof (proj1 (Nat2Z.inj_le n 8192) H) as H'.
  assert (E : Z.of_nat 8192 = 8192) by (vm_compute; reflexivity).
  rewrite E in H'. exact H'.
Qed.

(* the converse, for a caller that holds the Z bound of atoks_atA and applies psw_xm_bound / psw_live_bound *)
Lemma psw3_z8192 : forall n, Z.of_nat n <= 8192 -> (n <= 8192)%nat.
Proof.
  intros n H. apply (proj2 (Nat2Z.inj_le n 8192)).
  assert (E : Z.of_nat 8192 = 8192) by (vm_compute; reflexivity).
  rewrite E. exact H.
Qed.

(* the answer text has at most 16 bytes, for every code (RecFacts.v:68-77, :122) *)
Lemma psw3_digits_len : forall k n acc, (length (digits k n acc) <= k + length acc)%nat.
Proof.
  induction k as [|k IH]; intros n acc; cbn [digits]; [lia|].
  destruct (n <? 10); [cbn [length]; lia|].
  specialize (IH (n / 10) (Z_to_bv 8 (48 + n mod 10) :: acc)). cbn [length] in IH. lia.
Qed.

Lemma psw3_resp_len : forall c, (length (resp c) <= 16)%nat.
Proof.
  intros c. unfold resp, dec. rewrite !length_app.
  pose proof (psw3_digits_len 10 (Z.abs c) []) as L. cbn [length] in L.
  change (length (bstr "resp "%string)) with 5%nat.
  destruct (c <? 0); cbn [length]; lia.
Qed.

Lemma psw3_len_dash : length (bstr "-"%string) = 1%nat.
Proof. reflexivity. Qed.

Lemma psw3_len_star : length (darg None (bstr "*"%string)) = 1%nat.
Proof. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI : Z.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.

(* a string inside a live block that the recorder does not own is a string argument the recorder may take *)
Lemma psw3_argA_at : forall ly S (W : world SEGS) mem md (O : list (Z * Z)) cb ncb p x,
  AR SEGS B ly S W mem md ->
  In (cb, ncb) (ablocks B ly S) -> ~ In (cb, ncb) O ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  astr_atR (rdW W mem) p x -> Z.of_nat (length x) <= 8192 ->
  cb <= p -> p + Z.of_nat (length x) + 1 <= cb + ncb ->
  astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p (Some x).
Proof.
  intros ly S W mem md O cb ncb p x HAR Hin Hno HO Hs Hl Hlo Hhi.
  destruct (al_blocks SEGS B LAWS ly S W mem md cb ncb HAR Hin) as (_ & H4096 & _).
  unfold astr_argA. cbv beta iota zeta.
  split; [lia|]. split; [exact Hs|]. split; [unfold LMAX; lia|].
  left. split.
  - unfold in_blockA. exists cb, ncb. split; [exact Hin | lia].
  - apply Forall_forall. intros [q k] Hqk. cbn [fst snd].
    assert (Hne : (cb, ncb) <> (q, k)) by (intros E; apply Hno; rewrite E; exact Hqk).
    pose proof (sep_blocks SEGS B LAWS ly S W mem md cb ncb q k HAR Hin (HO _ Hqk) Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    pose proof (psw3_req_ge ncb). pose proof (psw3_req_ge k).
    unfold iv_apart. lia.
Qed.

(* 1. a word of verbs_receive's token array is a string argument the recorder may take *)
Lemma psw_argA_tok : forall ly S (W : world SEGS) mem md (O : list (Z * Z)) tok ptrs tks cb ncb i p w,
  AR SEGS B ly S W mem md ->
  atoks_atA (rdW W mem) tok ptrs tks cb ncb ->
  In (cb, ncb) (ablocks B ly S) -> ~ In (cb, ncb) O ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  nth_error ptrs i = Some p -> nth_error tks i = Some w ->
  astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p (Some w).
Proof.
  intros ly S W mem md O tok ptrs tks cb ncb i p w HAR Htok Hin Hno HO Hp Hw.
  destruct Htok as (_ & _ & _ & Hk).
  destruct (Hk i p w Hp Hw) as (Hs & Hl & Hlo & Hhi).
  exact (psw3_argA_at ly S W mem md O cb ncb p w HAR Hin Hno HO Hs Hl Hlo Hhi).
Qed.

(* 2. and so is its tail from the 8th byte (the "verdict=" prefix the caller skips) *)
Lemma psw_argA_skipn : forall ly S (W : world SEGS) mem md (O : list (Z * Z)) tok ptrs tks cb ncb i p w,
  AR SEGS B ly S W mem md ->
  atoks_atA (rdW W mem) tok ptrs tks cb ncb ->
  In (cb, ncb) (ablocks B ly S) -> ~ In (cb, ncb) O ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  nth_error ptrs i = Some p -> nth_error tks i = Some w -> (8 <= length w)%nat ->
  astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O (p + 8) (Some (skipn 8 w)).
Proof.
  intros ly S W mem md O tok ptrs tks cb ncb i p w HAR Htok Hin Hno HO Hp Hw H8.
  destruct Htok as (_ & _ & _ & Hk).
  destruct (Hk i p w Hp Hw) as (Hs & Hl & Hlo & Hhi).
  pose proof (psw3_len_skipn 8 w H8) as Ls. change (Z.of_nat 8) with 8 in Ls.
  apply (psw3_argA_at ly S W mem md O cb ncb (p + 8) (skipn 8 w) HAR Hin Hno HO).
  - exact (psw3_astr_skipn (rdW W mem) 8 p w H8 Hs).
  - lia.
  - lia.
  - lia.
Qed.

(* 3. the meter: the two recorder calls fit in pin_set_words' own bound (7 mallocs of at most 8194 bytes, and
   its events as frees) *)
Lemma psw_xm_bound : forall (R R1 : rstate) (u f l : list byte) (v : option (list byte)) (r : Z) T args,
  PV.pin_set_words_m T args = PV.SPinSet u f l v ->
  pins_set_m R (Some u) (Some f) (Some l) v = (R1, r) ->
  (length u <= 8192)%nat -> (length f <= 8192)%nat -> (length l <= 8192)%nat ->
  (forall x, v = Some x -> (length x <= 8192)%nat) ->
  rec_spill_frees R = 0 -> rec_spill_frees R1 = 0 ->
  XM_PINS_SET MT R (Some u) (Some f) (Some l) v
    + (if r =? 0 then XM_LV2_REFUSALS_FORGET MT R1 None else 0)
  <= XM_PIN_SET_WORDS MT R T args.
Proof.
  intros R R1 u f l v r T args H HS Hu Hf Hl Hv H0 H1.
  apply psw3_nat8192 in Hu. apply psw3_nat8192 in Hf. apply psw3_nat8192 in Hl.
  assert (Hb : forall x : list byte, Z.of_nat (length x) <= 8192 -> XM_XSTRDUP MT x <= mo_malloc MT 8194).
  { intros x Hx. unfold XM_XSTRDUP. apply (mo_malloc_mono MT MTL). lia. }
  pose proof (mo_malloc_nonneg MT MTL 8194 ltac:(lia)) as Hm0.
  pose proof (mo_free_nonneg MT MTL) as Hf0.
  assert (Hd : Z.of_nat (length (darg v (bstr "-"%string))) <= 8192).
  { destruct v as [x|]; cbn [darg]; [exact (psw3_nat8192 _ (Hv x eq_refl)) | rewrite psw3_len_dash; lia]. }
  pose proof (Hb (sarg (Some u)) Hu) as B1. pose proof (Hb (sarg (Some f)) Hf) as B2.
  pose proof (Hb (sarg (Some l)) Hl) as B3. pose proof (Hb (darg v (bstr "-"%string)) Hd) as B4.
  pose proof (Hb (resp r) ltac:(pose proof (psw3_resp_len r); lia)) as B5.
  pose proof (Hb (darg None (bstr "*"%string)) ltac:(rewrite psw3_len_star; lia)) as B6.
  unfold XM_PIN_SET_WORDS, EV_PIN_SET_WORDS, XM_PINS_SET.
  rewrite H. cbv beta iota. rewrite HS. cbv beta iota. cbn [snd].
  unfold XM_LV2_REFUSALS_FORGET, XM_ANSWER_CODE, XM_HAND_BACK, EV_PINS_SET, EV_LV2_REFUSALS_FORGET,
    EV_ANSWER_CODE, EV_HAND_BACK, EV_XSTRDUP, PIN_SET_WORDS_MALLOCS, PIN_SET_WORDS_REQ.
  rewrite H0, H1.
  destruct (r =? 0); lia.
Qed.

(* 4. the live bytes: pins_set's peak fits in pin_set_words' own bound *)
Lemma psw_live_bound : forall (R : rstate) (u f l : list byte) (v : option (list byte)) T args,
  PV.pin_set_words_m T args = PV.SPinSet u f l v ->
  (length u <= 8192)%nat -> (length f <= 8192)%nat -> (length l <= 8192)%nat ->
  (forall x, v = Some x -> (length x <= 8192)%nat) ->
  LIVE_PINS_SET R (Some u) (Some f) (Some l) v <= LIVE_PIN_SET_WORDS.
Proof.
  intros R u f l v T args _ Hu Hf Hl Hv.
  apply psw3_nat8192 in Hu. apply psw3_nat8192 in Hf. apply psw3_nat8192 in Hl.
  unfold LIVE_PINS_SET, LIVE_PIN_SET_WORDS, LIVE_ANSWER_CODE, LIVE_HAND_BACK, LIVE_XSTRDUP,
    PIN_SET_WORDS_MALLOCS, PIN_SET_WORDS_REQ.
  match goal with |- context [resp ?c] => pose proof (psw3_resp_len c) as Hr end.
  assert (Hd : Z.of_nat (length (darg v (bstr "-"%string))) <= 8192).
  { destruct v as [x|]; cbn [darg]; [exact (psw3_nat8192 _ (Hv x eq_refl)) | rewrite psw3_len_dash; lia]. }
  cbn [sarg]. lia.
Qed.

(* 5. the events, straight from the definitions *)
Lemma psw_ev_split : forall (R R1 : rstate) (u f l : list byte) (v : option (list byte)) (r : Z) T args,
  PV.pin_set_words_m T args = PV.SPinSet u f l v ->
  pins_set_m R (Some u) (Some f) (Some l) v = (R1, r) ->
  EV_PIN_SET_WORDS R T args = EV_PINS_SET R + (if r =? 0 then EV_LV2_REFUSALS_FORGET R1 else 0).
Proof.
  intros R R1 u f l v r T args H HS.
  unfold EV_PIN_SET_WORDS. rewrite H. cbv beta iota. rewrite HS. reflexivity.
Qed.

End e.
End f.
End d.
