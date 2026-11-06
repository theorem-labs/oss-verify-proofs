(* The pure facts the ASan+UBSan walk of pin_set_words (lib/B/Prog/pin_set_words_c.v) uses: the arity test the
   program compiles to, the strncmp against "verdict=" (the read-only bytes of .str.28 at 0x22900, lib/B/Prog/CmdRo.v),
   and the glue from the words to Verbs.pin_set_words_m (lib/Spec/Verbs.v) and VerbsRun.pin_set_run
   (lib/Spec/VerbsRun.v). The strncmp fact reuses sw_prefix of the plain proof (lib/Prog/pin_set_words.v:87-114).
   The B twin of a Theorem Labs lane's A file lib/A/Prog/pin_set_words_s1.v: only the literal's name differs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require pin_set_words.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.
Module PVR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.VerbsRun.
Module PSF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.StrFun.
Module PP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.pin_set_words.

(* Masking a count with -2 gives 4 exactly for the counts 4 and 5. *)
Lemma psw_land_m2 : forall n, 0 <= n -> (Z.land n (-2) = 4 <-> (n = 4 \/ n = 5)).
Proof.
  intros n Hn.
  assert (E : Z.land n (-2) = n / 2 * 2).
  { change (-2) with (Z.lnot (Z.ones 1)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite E. split.
  - intros H. Z.div_mod_to_equations. lia.
  - intros [-> | ->]; reflexivity.
Qed.

(* strncmp_walk stops within the first k + 1 bytes of its right argument. *)
Lemma psw_walk_app_r : forall k (l r s : list byte), (k < length r)%nat ->
  PSF.strncmp_walk l (r ++ s) k = PSF.strncmp_walk l r k.
Proof.
  intros k l. revert k. induction l as [|a l IH]; intros k r s Hk; [reflexivity|].
  destruct r as [|b r]; [cbn [length] in Hk; lia|].
  cbn [app PSF.strncmp_walk].
  match goal with |- (if ?c then _ else _) = _ => destruct c; [reflexivity|] end.
  destruct k as [|k]; [reflexivity|].
  apply IH. cbn [length] in Hk. lia.
Qed.

Lemma psw_verdict_lit : RO_lit_22900 = PV.Lit.word_verdict ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Lemma psw_verdict_len : length PV.Lit.word_verdict = 8%nat.
Proof. reflexivity. Qed.

(* A word with no NUL byte has no byte of value 0. *)
Lemma psw_nonzero : forall w : list byte, ~ In (Z_to_bv 8 0) w -> Forall (fun c => bv_unsigned c <> 0) w.
Proof.
  intros w H. apply Forall_forall. intros c Hc E. apply H.
  replace (Z_to_bv 8 0) with c; [exact Hc|]. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma psw_verdict_nz : Forall (fun c => bv_unsigned c <> 0) PV.Lit.word_verdict.
Proof.
  apply Forall_forall. intros c Hc.
  assert (B : forallb (fun c => negb (bv_unsigned c =? 0)) PV.Lit.word_verdict = true) by reflexivity.
  rewrite forallb_forall in B. specialize (B c Hc). apply negb_true_iff, Z.eqb_neq in B. exact B.
Qed.

Lemma psw_verdict : forall w : list byte, ~ In (Z_to_bv 8 0) w ->
  exists v, PSF.strncmp_model (w ++ [Z_to_bv 8 0]) (PV.Lit.word_verdict ++ [Z_to_bv 8 0]) 8 = Some v /\
    -256 < v < 256 /\ (v = 0 <-> PV.has_prefix PV.Lit.word_verdict w = true).
Proof.
  intros w Hw.
  change (PSF.strncmp_model ?l ?r 8) with (PSF.strncmp_walk l r 7).
  rewrite psw_walk_app_r by (rewrite psw_verdict_len; lia).
  exact (PP.sw_prefix 7 PV.Lit.word_verdict w psw_verdict_len psw_verdict_nz (psw_nonzero w Hw)).
Qed.

(* The model glue; the arguments are the words after the verb. *)
Lemma psw_ltb_false : forall ln : list byte, Z.of_nat (length ln) <= PV.line_max ->
  (PV.line_max <? Z.of_nat (length ln)) = false.
Proof. intros ln H. apply Z.ltb_ge. exact H. Qed.

Lemma psw_m_len3 : forall ln u f l, Z.of_nat (length ln) <= PV.line_max ->
  PV.list_eqb l PV.Lit.word_layout_unknown = false -> PV.pin_set_words_m ln [u; f; l] = PV.SPinSet u f l None.
Proof.
  intros ln u f l HL HD. unfold PV.pin_set_words_m. cbv beta iota.
  rewrite (psw_ltb_false ln HL), HD. reflexivity.
Qed.

Lemma psw_m_len4 : forall ln u f l vd, Z.of_nat (length ln) <= PV.line_max ->
  PV.list_eqb l PV.Lit.word_layout_unknown = false -> PV.has_prefix PV.Lit.word_verdict vd = true ->
  PV.pin_set_words_m ln [u; f; l; vd] = PV.SPinSet u f l (Some (skipn 8 vd)).
Proof.
  intros ln u f l vd HL HD HV. unfold PV.pin_set_words_m. cbv beta iota.
  rewrite (psw_ltb_false ln HL), HD, HV. reflexivity.
Qed.

Lemma psw_m_bad4 : forall ln u f l vd, PV.has_prefix PV.Lit.word_verdict vd = false ->
  PV.pin_set_words_m ln [u; f; l; vd] = PV.reject.
Proof.
  intros ln u f l vd HV. unfold PV.pin_set_words_m. cbv beta iota. rewrite HV.
  match goal with |- (if ?c then _ else _) = _ => destruct c end; reflexivity.
Qed.

Lemma psw_m_dash3 : forall ln u f l, PV.list_eqb l PV.Lit.word_layout_unknown = true ->
  PV.pin_set_words_m ln [u; f; l] = PV.reject.
Proof.
  intros ln u f l HD. unfold PV.pin_set_words_m. cbv beta iota. rewrite HD, orb_true_r. reflexivity.
Qed.

Lemma psw_m_dash4 : forall ln u f l vd, PV.list_eqb l PV.Lit.word_layout_unknown = true ->
  PV.pin_set_words_m ln [u; f; l; vd] = PV.reject.
Proof.
  intros ln u f l vd HD. unfold PV.pin_set_words_m. cbv beta iota. rewrite HD, orb_true_r. reflexivity.
Qed.

Lemma psw_m_long : forall ln args, PV.line_max < Z.of_nat (length ln) -> PV.pin_set_words_m ln args = PV.reject.
Proof.
  intros ln args H. pose proof (proj2 (Z.ltb_lt _ _) H) as HL.
  destruct args as [|a [|b [|c [|d [|e args]]]]]; unfold PV.pin_set_words_m; cbv beta iota;
    rewrite ?HL; reflexivity.
Qed.

Lemma psw_m_arity : forall ln args, (length args <> 3)%nat -> (length args <> 4)%nat ->
  PV.pin_set_words_m ln args = PV.reject.
Proof.
  intros ln args H3 H4.
  destruct args as [|a [|b [|c [|d [|e args]]]]]; cbn [length] in H3, H4; try lia; reflexivity.
Qed.

(* The run glue. *)
Lemma psw_run_reject : forall R ln args, PV.pin_set_words_m ln args = PV.reject ->
  PVR.pin_set_run R ln args = (R, PV.err_invalid_operation).
Proof. intros R ln args H. unfold PVR.pin_set_run. rewrite H. reflexivity. Qed.

Lemma psw_run_set : forall R ln args u f l v R1 r, PV.pin_set_words_m ln args = PV.SPinSet u f l v ->
  pins_set_m R (Some u) (Some f) (Some l) v = (R1, r) ->
  PVR.pin_set_run R ln args = ((if r =? 0 then lv2_refusals_forget_m R1 None else R1), r).
Proof.
  intros R ln args u f l v R1 r H HS. unfold PVR.pin_set_run. rewrite H. cbv beta iota. rewrite HS. reflexivity.
Qed.

(* The token list of a given length. *)
Lemma psw_list3 : forall {A} (l : list A), length l = 3%nat -> exists a b c, l = [a; b; c].
Proof.
  intros A l H. destruct l as [|a [|b [|c [|d l]]]]; cbn [length] in H; try lia.
  exists a, b, c. reflexivity.
Qed.

Lemma psw_list4 : forall {A} (l : list A), length l = 4%nat -> exists a b c d, l = [a; b; c; d].
Proof.
  intros A l H. destruct l as [|a [|b [|c [|d [|e l]]]]]; cbn [length] in H; try lia.
  exists a, b, c, d. reflexivity.
Qed.
