(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvKit InflateInvArms1.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.

Section Arms.
  Variables (iv : ivariant) (flush : Z) (NI NO WN TOT0 : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Local Notation pinv := (pinv NI NO WN TOT0).
  Local Notation apost := (apost NI NO WN TOT0).


  Lemma P_HCRC : forall w, pinv w -> is_mode (w_s w) = HCRC -> apost w (arm_HCRC w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    unfold arm_HCRC. wred.
    destruct (Z.eqb_spec (Z.land f_flags 512) 0) as [HF|HF]; bsimp; wred.
    1:{ cbn [apost]. arun_post. }
    needbits_run 16 RIr NI32 NO32 ClNI Cinb.
    2:{ needbits_aleave NB r1 RI1. cbn [apost w_s]. leave_post. }
    needbits_arun NB r1 RI1. wred. rinv_open RI1.
    destruct (negb (Z.land f_wrap 4 =? 0) && negb (ho1 =? Z.land f_check 65535)); wred; cbn [apost]; arun_post.
  Qed.

  Lemma P_COMMENT : forall w, pinv w -> is_mode (w_s w) = COMMENT -> apost w (arm_COMMENT w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    unfold arm_COMMENT, name_like. wred.
    destruct (negb (Z.land f_flags 4096 =? 0)); wred.
    2:{ chain_tail P_HCRC. }
    destruct (Z.eqb_spec r_have 0) as [Hz|Hz]; wred; [cbn [apost w_s]; leave_post|].
    assert (Hh1 : 0 < r_have < 2 ^ 32) by glia. pose proof (scan_zero_bound c_input r_next r_have Hh1) as SB.
    destruct (scan_zero c_input r_next r_have) as [copy len]. cbn [fst] in SB. wred.
    assert (BY : Forall (fun b => 0 <= b < 256) (arr_slice c_input r_next copy)).
    { apply (slice_bytes c_input NI); [exact Cinb | glia | glia | glia]. }
    pose proof (icrc32_upd_range f_check _ BY) as CKR.
    destruct (negb (Z.land f_flags 512 =? 0) && negb (Z.land f_wrap 4 =? 0)); wred;
      rewrite (wrap32_id (r_have - copy)) by glia;
      (destruct (negb (len =? 0)); wred; [cbn [apost w_s]; leave_post | chain_tail P_HCRC]).
  Qed.

  Lemma P_NAME : forall w, pinv w -> is_mode (w_s w) = NAME -> apost w (arm_NAME w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    unfold arm_NAME, name_like. wred.
    destruct (negb (Z.land f_flags 2048 =? 0)); wred.
    2:{ chain_tail P_COMMENT. }
    destruct (Z.eqb_spec r_have 0) as [Hz|Hz]; wred; [cbn [apost w_s]; leave_post|].
    assert (Hh1 : 0 < r_have < 2 ^ 32) by glia. pose proof (scan_zero_bound c_input r_next r_have Hh1) as SB.
    destruct (scan_zero c_input r_next r_have) as [copy len]. cbn [fst] in SB. wred.
    assert (BY : Forall (fun b => 0 <= b < 256) (arr_slice c_input r_next copy)).
    { apply (slice_bytes c_input NI); [exact Cinb | glia | glia | glia]. }
    pose proof (icrc32_upd_range f_check _ BY) as CKR.
    destruct (negb (Z.land f_flags 512 =? 0) && negb (Z.land f_wrap 4 =? 0)); wred;
      rewrite (wrap32_id (r_have - copy)) by glia;
      (destruct (negb (len =? 0)); wred; [cbn [apost w_s]; leave_post | chain_tail P_COMMENT]).
  Qed.

  Lemma P_EXTRA : forall w, pinv w -> is_mode (w_s w) = EXTRA -> apost w (arm_EXTRA w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    unfold arm_EXTRA. wred.
    destruct (negb (Z.land f_flags 1024 =? 0)); wred.
    2:{ chain_tail P_NAME. }
    set (copy := if r_have <? f_length then r_have else f_length).
    assert (Hcp : 0 <= copy <= r_have /\ copy <= f_length) by (subst copy; destruct (Z.ltb_spec r_have f_length); glia).
    assert (BY : Forall (fun b => 0 <= b < 256) (arr_slice c_input r_next copy)).
    { apply (slice_bytes c_input NI); [exact Cinb | glia | glia | glia]. }
    pose proof (icrc32_upd_range f_check _ BY) as CKR.
    pose proof (wrap32_range (f_length - copy)) as WL.
    destruct (negb (copy =? 0)); wred.
    - destruct (negb (Z.land f_flags 512 =? 0) && negb (Z.land f_wrap 4 =? 0)); wred;
        rewrite (wrap32_id (r_have - copy)) by glia;
        (destruct (negb (wrap32 (f_length - copy) =? 0)); wred; [cbn [apost w_s]; leave_post | chain_tail P_NAME]).
    - destruct (negb (f_length =? 0)); wred; [cbn [apost w_s]; leave_post | chain_tail P_NAME].
  Qed.

  Lemma P_EXLEN : forall w, pinv w -> is_mode (w_s w) = EXLEN -> apost w (arm_EXLEN w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    unfold arm_EXLEN. wred.
    destruct (Z.eqb_spec (Z.land f_flags 1024) 0) as [HF|HF]; bsimp; wred.
    1:{ chain_tail P_EXTRA. }
    needbits_run 16 RIr NI32 NO32 ClNI Cinb.
    2:{ needbits_aleave NB r1 RI1. cbn [apost w_s]. leave_post. }
    needbits_arun NB r1 RI1. wred. pose proof (RINV_init _ _ NI32 NO32 _ RI1) as [RI2 _]. rinv_open RI2.
    pose proof (wrap32_range ho1) as WL.
    destruct (negb (Z.land f_flags 512 =? 0) && negb (Z.land f_wrap 4 =? 0)); wred;
      (chain_tail P_EXTRA).
  Qed.

  Lemma P_OS : forall w, pinv w -> is_mode (w_s w) = OS -> apost w (arm_OS w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    unfold arm_OS. wred.
    needbits_run 16 RIr NI32 NO32 ClNI Cinb.
    2:{ needbits_aleave NB r1 RI1. cbn [apost w_s]. leave_post. }
    needbits_arun NB r1 RI1. wred. pose proof (RINV_init _ _ NI32 NO32 _ RI1) as [RI2 _]. rinv_open RI2.
    destruct (negb (Z.land f_flags 512 =? 0) && negb (Z.land f_wrap 4 =? 0)); wred;
      (chain_tail P_EXLEN).
  Qed.

  Lemma P_TIME : forall w, pinv w -> is_mode (w_s w) = TIME -> apost w (arm_TIME w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    unfold arm_TIME. wred.
    needbits_run 32 RIr NI32 NO32 ClNI Cinb.
    2:{ needbits_aleave NB r1 RI1. cbn [apost w_s]. leave_post. }
    needbits_arun NB r1 RI1. wred. pose proof (RINV_init _ _ NI32 NO32 _ RI1) as [RI2 _]. rinv_open RI2.
    destruct (negb (Z.land f_flags 512 =? 0) && negb (Z.land f_wrap 4 =? 0)); wred;
      (chain_tail P_OS).
  Qed.

  Lemma P_FLAGS : forall w, pinv w -> is_mode (w_s w) = FLAGS -> apost w (arm_FLAGS w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    unfold arm_FLAGS. wred.
    needbits_run 16 RIr NI32 NO32 ClNI Cinb.
    2:{ needbits_aleave NB r1 RI1. cbn [apost w_s]. leave_post. }
    needbits_arun NB r1 RI1. wred. rinv_open RI1. pose proof (RINV_init _ _ NI32 NO32 _ RI1) as [RI2 _]. rinv_open RI2.
    pose proof (swrap32_range ho1) as SW.
    destruct (negb (Z.land (swrap32 ho1) 255 =? Z_DEFLATED)); wred; [cbn [apost]; arun_post|].
    destruct (negb (Z.land (swrap32 ho1) 57344 =? 0)); wred; [cbn [apost]; arun_post|].
    destruct (negb (Z.land (swrap32 ho1) 512 =? 0) && negb (Z.land f_wrap 4 =? 0)); wred;
      (chain_tail P_TIME).
  Qed.


  Lemma P_HEAD : forall w, pinv w -> is_mode (w_s w) = HEAD -> apost w (arm_HEAD iv w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    unfold arm_HEAD. wred.
    destruct (Z.eqb_spec f_wrap 0) as [HW|HW]; wred.
    { cbn [apost]. arun_post. }
    needbits_run 16 RIr NI32 NO32 ClNI Cinb.
    2:{ needbits_aleave NB r1 RI1. cbn [apost w_s]. leave_post. }
    needbits_arun NB r1 RI1. wred. rinv_open RI1. pose proof (RINV_init _ _ NI32 NO32 _ RI1) as [RI2 _]. rinv_open RI2.
    destruct (negb (Z.land f_wrap 2 =? 0) && (ho1 =? 35615)); wred.
    - destruct (Z.eqb_spec f_wbits 0); [glia|]. wred. cbn [apost]. arun_post.
    - destruct ((Z.land f_wrap 1 =? 0) || negb (wrap64 (shl32 (BITSv ho1 8) 8 + Z.shiftr ho1 8) mod 31 =? 0)); wred; [cbn [apost]; arun_post|].
      destruct (negb (BITSv ho1 4 =? Z_DEFLATED)); wred; [cbn [apost]; arun_post|].
      dropbits 4%Z RI1 RI3 NI32 NO32. rinv_open RI3. wred.
      destruct (Z.eqb_spec f_wbits 0); [glia|]. wred.
      destruct ((15 <? BITSv (Z.shiftr ho1 4) 4 + 8) || (f_wbits <? BITSv (Z.shiftr ho1 4) 4 + 8)); wred; [cbn [apost]; arun_post|].
      pose proof (wrap32_range (Z.shiftl 1 (BITSv (Z.shiftr ho1 4) 4 + 8))) as DM.
      destruct (iv_aux iv); wred; cbn [apost]; destruct (negb (Z.land (Z.shiftr ho1 4) 512 =? 0)); wred; (split; [pinv_auto | phi_auto]); try (unfold shl32; exact DM);
        first [glia | sinv_easy | xinv_auto | (binv_close; binv_auto) | (kinv_close; kinv_auto)].
  Qed.


  Lemma tables_ok_fixed : forall nx codes, tables_okf CLenfix CDistfix 9 5 nx codes = true.
  Proof. intros. Transparent tables_okf. reflexivity. Qed.
  Lemma tables_rep_fixed : forall codes, rep_ok (cat codes CLenfix) 9 /\ rep_ok (cat codes CDistfix) 5.
  Proof. intros. split; [exact lenfix_rep | exact distfix_rep]. Qed.

  Ltac phi_m MR := unfold PHI; cbn [w_r w_s ir_have ir_bits ir_left is_mode]; rewrite MR; phi_red; glia.

  Lemma P_TYPEDO : forall w, pinv w -> (is_mode (w_s w) = TYPEDO \/ is_mode (w_s w) = TYPE) -> apost w (arm_TYPEDO iv flush w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI.
    assert (PM : codes_live f_mode = false /\ f_mode <> LENLENS /\ f_mode <> CODELENS /\ f_mode <> LENEXT /\ f_mode <> DIST
                 /\ f_mode <> DISTEXT /\ f_mode <> MATCH /\ f_mode <> COPY_ /\ f_mode <> COPY /\ TYPE <= f_mode < CHECK).
    { destruct Hm as [-> | ->]; (split; [reflexivity | mlia]). }
    assert (MR : mrank f_mode = 2) by (destruct Hm as [-> | ->]; reflexivity).
    assert (BI8 : r_bits < 8).
    { binv_use. destruct Hm as [Hm | Hm]; rewrite Hm in BI; pend_red_in BI; (destruct BI as [X | X]; [exact X | destruct X]). }
    clear BI Hm. destruct PM as (PM0 & PM1 & PM2 & PM3 & PM4 & PM5 & PM6 & PM7 & PM8 & PM9).
    clear PM1 PM2 PM3 PM4 PM5 PM6 PM7 PM8.
    clear Qtab Qlenlens Qcodelens Qlenext Qdist Qdistext Qmatch Qcopy Qrep Qcrep.
    unfold arm_TYPEDO. wred.
    destruct (negb (f_last =? 0)); wred.
    {
      assert (Hb7 : 0 <= r_bits) by glia. pose proof (land7_le r_bits Hb7) as [L7 L8].
      dropbits (Z.land r_bits 7) RIr RI3 NI32 NO32.
      rinv_open RI3. cbn [apost]. split; [pinv_auto | phi_m MR]. }
    needbits_run 3 RIr NI32 NO32 ClNI Cinb.
    2:{ needbits_aleave NB r1 RI1. cbn [apost w_s]. leave_post. }
    needbits_arun NB r1 RI1. wred. rinv_open RI1.
    dropbits 1%Z RI1 RI2 NI32 NO32. rinv_open RI2.
    pose proof (BITSv_bound ho1 1 ltac:(lia)) as B1. cbn in B1.
    set (t := BITSv (Z.shiftr ho1 1) 2).
    destruct (t =? 0); wred.
    { dropbits 2%Z RI2 RI3 NI32 NO32. rinv_open RI3. cbn [apost]. split; [pinv_auto | phi_m MR]. }
    destruct (t =? 1); wred.
    { destruct (iv_flush_exits iv && (flush =? Z_TREES)); wred; dropbits 2%Z RI2 RI3 NI32 NO32; rinv_open RI3.
      - cbn [apost w_s]. leave_post. all: try (intros _; apply tables_ok_fixed). all: try (intros _; apply tables_rep_fixed).
      - cbn [apost]. split; [pinv_auto | phi_m MR]. all: try (intros _; apply tables_ok_fixed). all: try (intros _; apply tables_rep_fixed). }
    destruct (t =? 2); wred; dropbits 2%Z RI2 RI3 NI32 NO32; rinv_open RI3; cbn [apost]; (split; [pinv_auto | phi_m MR]).
  Qed.

  Lemma P_TYPE : forall w, pinv w -> is_mode (w_s w) = TYPE -> apost w (arm_TYPE iv flush w).
  Proof.
    intros w PI Hm. unfold arm_TYPE.
    destruct (iv_flush_exits iv && _).
    - dworld w. cbn [apost w_s]. destruct PI as (_ & LR & SI & _ & BI & KI). exact (conj LR (conj SI (conj BI (proj1 KI)))).
    - apply P_TYPEDO; [exact PI | right; exact Hm].
  Qed.


  Lemma P_DICT : forall w, pinv w -> is_mode (w_s w) = DICT -> apost w (arm_DICT iv flush w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    unfold arm_DICT, RESTORE. wred.
    destruct (f_havedict =? 0); wred.
    - cbn [apost w_s]. leave_post.
    - chain_tail P_TYPE.
  Qed.

  Lemma P_DICTID : forall w, pinv w -> is_mode (w_s w) = DICTID -> apost w (arm_DICTID iv flush w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    unfold arm_DICTID. wred.
    needbits_run 32 RIr NI32 NO32 ClNI Cinb.
    2:{ needbits_aleave NB r1 RI1. cbn [apost w_s]. leave_post. }
    needbits_arun NB r1 RI1. wred. pose proof (RINV_init _ _ NI32 NO32 _ RI1) as [RI2 _]. rinv_open RI2.
    pose proof (ZSWAP32_range ho1) as ZR.
    chain_tail P_DICT.
  Qed.


  Lemma P_COPY : forall w, pinv w -> is_mode (w_s w) = COPY -> gCOPY w = true /\ apost w (arm_COPY w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    split.
    { unfold gCOPY, roomok, olen. cbn [w_r w_c w_s ir_put ir_left ir_have is_length ic_outbuf].
      repeat (apply andb_true_intro; split); apply Z.leb_le; glia. }
    unfold arm_COPY. wred.
    destruct (negb (f_length =? 0)) eqn:EL; wred.
    2:{ cbn [apost]. arun_post. }
    set (copy0 := if r_have <? f_length then r_have else f_length).
    set (copy := if r_left <? copy0 then r_left else copy0).
    assert (Hcp0 : 0 <= copy0 <= r_have /\ copy0 <= f_length) by (subst copy0; destruct (Z.ltb_spec r_have f_length); glia).
    assert (Hcp : 0 <= copy <= r_have /\ copy <= f_length /\ copy <= r_left) by (subst copy; destruct (Z.ltb_spec r_left copy0); glia).
    destruct (Z.eqb_spec copy 0) as [C0|C0]; wred.
    { cbn [apost w_s]. leave_post. }
    rewrite (wrap32_id (r_have - copy)), (wrap32_id (r_left - copy)), (wrap32_id (f_length - copy)) by glia.
    cbn [apost]. arun_post.
    - rewrite arr_len_blit. exact ClNO.
    - apply (blit_bytes c_outbuf c_input NO NI); try assumption; glia.
    - cross_close. replace (c_total_out + (r_out - (r_left - copy))) with (c_total_out + (r_out - r_left) + copy) by lia.
      rewrite (Z.add_assoc TOT0 r_put copy). apply wrap64_add_eq. exact CR.
  Qed.

  Lemma P_COPY_ : forall w, pinv w -> is_mode (w_s w) = COPY_ -> gCOPY_ w = true /\ apost w (arm_COPY_ w).
  Proof.
    intros w PI Hm.
    assert (PI1 : pinv (wset_s w (iset_mode (w_s w) COPY))).
    { dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage. wred. pinv_auto. }
    destruct (P_COPY _ PI1 ltac:(destruct w as [[] c r]; reflexivity)) as [G A].
    split.
    - unfold gCOPY_. unfold gCOPY, roomok, olen in G |- *. destruct w as [[] c r]. exact G.
    - unfold arm_COPY_. destruct w as [s c r]. eapply apost_mono; [| exact A]. cbn [w_s is_mode] in Hm. destruct s; cbn in Hm; subst. phi_auto.
  Qed.

  Lemma P_STORED : forall w, pinv w -> is_mode (w_s w) = STORED -> gSTORED w = true /\ apost w (arm_STORED iv flush w).
  Proof.
    intros w PI Hm. dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage.
    split.
    { unfold gSTORED, roomok, olen. cbn [w_r w_c ir_put ir_left ir_have ic_outbuf].
      repeat (apply andb_true_intro; split); apply Z.leb_le; glia. }
    unfold arm_STORED. wred.
    assert (Hb7 : 0 <= r_bits) by glia. pose proof (land7_le r_bits Hb7) as [L7 L8].
    dropbits (Z.land r_bits 7) RIr RI0 NI32 NO32.
    needbits_run 32 RI0 NI32 NO32 ClNI Cinb.
    2:{ needbits_aleave NB r1 RI1. cbn [apost w_s]. leave_post. }
    needbits_arun NB r1 RI1. wred. rinv_open RI1.
    destruct (negb (Z.land ho1 65535 =? Z.lxor (Z.shiftr ho1 16) 65535)); wred.
    { cbn [apost]. arun_post. }
    pose proof (RINV_init _ _ NI32 NO32 _ RI1) as [RI2 _]. rinv_open RI2.
    pose proof (land_65535_range (wrap32 ho1)) as HL.
    destruct (iv_flush_exits iv && (flush =? Z_TREES)); wred.
    - cbn [apost w_s]. leave_post.
    - match goal with |- apost _ (arm_COPY_ ?w) => unshelve epose proof (P_COPY_ w _ eq_refl) as [_ A]; [pinv_auto | eapply apost_mono; [| exact A]; phi_auto] end.
  Qed.
End Arms.
