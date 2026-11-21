(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb ModelRel
  InflateInv InflateInvRun InflateInvTab InflateInvKit InflateInvApi InflateInvLoop InflateInvCall
  HarnessKit HarnessFacts InflateLeave InflateCall InflateFirst2 InflateSync InflateSyncPost.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma restore_fields : forall s h b, let s' := iset_bits (iset_hold s h) b in
  is_bits s' = b /\ is_hold s' = h /\ is_have s' = is_have s /\ is_wrap s' = is_wrap s /\ is_wbits s' = is_wbits s
  /\ is_havedict s' = is_havedict s /\ is_flags s' = is_flags s /\ is_mode s' = is_mode s /\ is_wsize s' = is_wsize s.
Proof. intros [] h b; repeat split; reflexivity. Qed.
Lemma fin_s_fields : forall s tt ck, let s' := fin_s s tt ck in
  is_bits s' = is_bits s /\ is_hold s' = is_hold s /\ is_have s' = is_have s /\ is_wrap s' = is_wrap s /\ is_wbits s' = is_wbits s
  /\ is_havedict s' = is_havedict s /\ is_flags s' = is_flags s /\ is_mode s' = is_mode s.
Proof. intros [] tt ck; repeat split; reflexivity. Qed.
Lemma zr_rc_of_icall : forall c rc, zr_rc (zret_of_icall c rc) = rc.
Proof. intros [] rc; reflexivity. Qed.

Section S.
  Variable iv : ivariant.
  Ltac modesel :=
    cbn [Z.eqb Pos.eqb BAD HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE
         LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE MEM SYNC].
  Ltac next_dispatch := rewrite (iterK_gstep_S iv Z_NO_FLUSH); unfold dispatch; wred; modesel.
  Ltac finst :=
    repeat match goal with |- _ /\ _ => split end;
    first [ reflexivity | lia
          | (left; split; reflexivity)
          | (right; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
             first [left; reflexivity | right; reflexivity]) ].
  Ltac bad_tail := wred; next_dispatch; unfold arm_BAD; wred; finst.

  Lemma head2_loop_st : forall s c,
    is_mode s = HEAD -> is_wrap s = 5 -> is_hold s = 0 -> is_bits s = 0 -> is_wbits s = 15 -> is_last s = 0 ->
    ic_next_in c = 0 -> ic_avail_in c = 2 -> 0 <= ic_avail_out c ->
    let '(stop, w') := inf_loop iv Z_NO_FLUSH (W1M s c) in
    stop = SLeave /\ ir_out (w_r w') = ir_left (w_r w') /\ ir_in (w_r w') = 2 /\ ir_have (w_r w') = 0
    /\ 0 <= ir_bits (w_r w') <= 16 /\ 0 <= ir_hold (w_r w') < 2 ^ 64
    /\ is_wsize (w_s w') = is_wsize s /\ is_window_blk (w_s w') = is_window_blk s
    /\ is_have (w_s w') = is_have s /\ is_wrap (w_s w') = 5 /\ is_wbits (w_s w') = 15 /\ is_havedict (w_s w') = is_havedict s
    /\ ((is_mode (w_s w') = BAD /\ ir_ret (w_r w') = Z_DATA_ERROR)
        \/ (ir_ret (w_r w') = Z_OK /\ is_flags (w_s w') = 0 /\ ir_bits (w_r w') = 0 /\ ir_hold (w_r w') = 0
            /\ (is_mode (w_s w') = TYPE \/ is_mode (w_s w') = DICTID))).
  Proof.
    intros s c Hm Hw Hh Hb Hwb Hl Hni Hai Hao.
    rewrite (inf_loop_iter iv Z_NO_FLUSH).
    assert (HF : exists n, Z.to_nat (gfuel (W1M s c)) = S (S (S n))).
    { unfold gfuel, W1M. cbn [w_c]. rewrite Hai. exists (Z.to_nat (64 * (2 + ic_avail_out c + 64) - 3)). lia. }
    destruct HF as [n ->].
    ds s. destruct c as [ci cni cai cob cno cao cti cto cad cdt cmsg]. cbn in Hm, Hw, Hh, Hb, Hwb, Hl, Hni, Hai, Hao. subst.
    unfold W1M, s_entryM. cbn [is_mode Z.eqb Pos.eqb HEAD TYPE]. cbn [is_hold is_bits ic_next_in ic_avail_in ic_next_out ic_avail_out].
    next_dispatch. unfold arm_HEAD. wred.
    rewrite NEEDBITS16_2. cbn [ic_input]. set (h := wrap64 _).
    assert (Rh : 0 <= h < 2 ^ 64) by (subst h; apply wrap64_range). clearbody h.
    assert (Rh4 : 0 <= Z.shiftr h 4 < 2 ^ 64).
    { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    wred.
    change (Z.land 5 2) with 0. change (Z.land 5 1) with 1. bsimp. wred.
    destruct (wrap64 (shl32 (BITSv h 8) 8 + Z.shiftr h 8) mod 31 =? 0); bsimp; [| bad_tail].
    wred. destruct (BITSv h 4 =? Z_DEFLATED); bsimp; [| bad_tail].
    wred. change (wrap32 (16 - 4)) with 12.
    destruct (15 <? BITSv (Z.shiftr h 4) 4 + 8); bsimp; [bad_tail|].
    wred. destruct (iv_aux iv); wred.
    all: destruct (Z.land (Z.shiftr h 4) 512 =? 0); bsimp; next_dispatch.
    1,3: unfold arm_TYPE; change ((Z_NO_FLUSH =? Z_BLOCK) || (Z_NO_FLUSH =? Z_TREES)) with false; rewrite Bool.andb_false_r;
         unfold arm_TYPEDO; wred; rewrite NEEDBITS_noinput by lia; wred; finst.
    all: unfold arm_DICTID; wred; rewrite NEEDBITS_noinput by lia; wred; finst.
  Qed.

  Theorem inflate1_shape : forall ans s zc,
    is_mode s = HEAD -> is_wrap s = 5 -> is_hold s = 0 -> is_bits s = 0 -> is_wbits s = 15 -> is_last s = 0 -> is_wsize s = 0 ->
    zlength (zc_input zc) = 2 -> 0 <= zc_avail_out zc ->
    let '(p, _) := inflate_p iv ans s zc Z_NO_FLUSH in
    let s1 := fst p in let r1 := snd p in
    0 <= is_bits s1 <= 16 /\ 0 <= is_hold s1 < 2 ^ 64 /\ is_have s1 = is_have s /\ is_wrap s1 = 5 /\ is_wbits s1 = 15
    /\ is_havedict s1 = is_havedict s
    /\ (zr_rc r1 = Z_OK -> is_flags s1 = 0 /\ is_bits s1 = 0 /\ is_hold s1 = 0 /\ (is_mode s1 = TYPE \/ is_mode s1 = DICTID)).
  Proof.
    intros ans s zc Hm Hw Hh Hb Hwb Hl Hws Hlen Hao.
    assert (CK : inflateStateCheck s = false) by (unfold inflateStateCheck; rewrite Hm; reflexivity).
    rewrite (inflate_p_W1M iv ans s zc Z_NO_FLUSH CK).
    pose proof (head2_loop_st s (icall_of_zcall zc) Hm Hw Hh Hb Hwb Hl eq_refl ltac:(cbn; exact Hlen) ltac:(cbn; exact Hao)) as L.
    destruct (inf_loop iv Z_NO_FLUSH (W1M s (icall_of_zcall zc))) as [stop [s' c' r']].
    cbn [w_s w_r] in L. destruct L as (-> & Ho & Hin & Hhv & Bb & Bh & Hws' & _ & Hhave & Hwrap & Hwbits & Hhd & CASES).
    unfold inf_leave_p. rewrite RESTORE_eq. cbn [w_s w_c w_r].
    pose proof (restore_fields s' (ir_hold r') (ir_bits r')) as RF. cbv zeta in RF.
    destruct RF as (Fb & Fh & Fhv & Fw & Fwb & Fhd & Ff & Fm & Fws).
    set (s0 := iset_bits (iset_hold s' (ir_hold r')) (ir_bits r')) in *.
    replace (leave_need Z_NO_FLUSH s0 (cRest c' r') r') with false.
    2:{ unfold leave_need. rewrite Fws, Hws', Hws. replace (ic_avail_out (cRest c' r')) with (ir_left r') by (destruct c'; reflexivity).
        rewrite Ho, !Z.eqb_refl. reflexivity. }
    rewrite (leave_tail_eq Z_NO_FLUSH s0 c' r') by (unfold lv_out, lv_in; lia).
    cbn [fst snd].
    pose proof (fin_s_fields s0 (wrap64 (is_total s0 + lv_out r')) (lv_ck c' r' s0)) as GF. cbv zeta in GF.
    destruct GF as (Gb & Gh & Ghv & Gw & Gwb & Ghd & Gf & Gm).
    rewrite Gb, Gh, Ghv, Gw, Gwb, Ghd, Gf, Gm, Fb, Fh, Fhv, Fw, Fwb, Fhd, Ff, Fm.
    split; [exact Bb|]. split; [exact Bh|]. split; [exact Hhave|]. split; [exact Hwrap|]. split; [exact Hwbits|]. split; [exact Hhd|].
    rewrite zr_rc_of_icall. unfold lv_rc, lv_in, lv_out. rewrite Hin, Hhv, Ho, Z.sub_diag. cbn [Z.sub Z.eqb andb orb Z_NO_FLUSH Z_FINISH Z.pos_sub].
    change ((0 =? 4)) with false. cbn [andb orb].
    destruct CASES as [[Mb Rb] | (Rok & Fl0 & B0 & H0 & Md)].
    - rewrite Rb. intros X. discriminate X.
    - rewrite Rok. intros _. split; [exact Fl0|]. split; [exact B0|]. split; [exact H0 | exact Md].
  Qed.

  Lemma sync_drain_keep : forall fuel s acc, let s' := fst (sync_drain fuel s acc) in
    is_flags s' = is_flags s /\ is_wrap s' = is_wrap s /\ is_wbits s' = is_wbits s /\ is_mode s' = is_mode s.
  Proof.
    induction fuel as [|f IH]; intros s acc; cbn [sync_drain fst]; [repeat split; reflexivity|].
    destruct (8 <=? is_bits s); [| repeat split; reflexivity].
    specialize (IH (iset_bits (iset_hold s (Z.shiftr (is_hold s) 8)) (is_bits (iset_hold s (Z.shiftr (is_hold s) 8)) - 8)) (acc ++ [Z.land (is_hold s) 255])).
    cbv zeta in IH. destruct (sync_drain f _ _) as [s' acc']. cbn [fst] in IH |- *.
    destruct IH as (A & B & C & D). rewrite A, B, C, D. destruct s; repeat split; reflexivity.
  Qed.

  Lemma sync_entry_keep : forall s, let s1 := sync_entry s in
    is_flags s1 = is_flags s /\ is_wrap s1 = is_wrap s /\ is_wbits s1 = is_wbits s /\ is_mode s1 = SYNC.
  Proof.
    intros s. cbv zeta. unfold sync_entry.
    set (s2 := iset_bits _ _).
    pose proof (sync_drain_keep (S (Z.to_nat (Z.shiftr (is_bits s2) 3))) s2 []) as K. cbv zeta in K.
    destruct (sync_drain _ s2 []) as [s3 buf]. cbn [fst] in K. destruct K as (A & B & C & D).
    destruct (syncsearch _ buf) as [got len].
    assert (E2 : is_flags s2 = is_flags s /\ is_wrap s2 = is_wrap s /\ is_wbits s2 = is_wbits s /\ is_mode s2 = SYNC) by (subst s2; destruct s; repeat split; reflexivity).
    destruct E2 as (A2 & B2 & C2 & D2).
    destruct s3; cbn in A, B, C, D |- *. subst. repeat split; assumption.
  Qed.

  Lemma reset_keep : forall s z, inflateStateCheck s = false ->
    let '(s', z', rc) := inflateReset iv s z in
    is_wrap s' = is_wrap s /\ is_wbits s' = is_wbits s /\ is_havedict s' = 0 /\ zs_msg z' = MSG_NULL.
  Proof.
    intros s z CK. unfold inflateReset, inflateResetKeep, auxp. rewrite CK.
    replace (inflateStateCheck (iset_wnext (iset_whave (iset_wsize s 0) 0) 0)) with false by (rewrite <- CK; destruct s; reflexivity).
    destruct s; destruct z; cbn -[Z.eqb Z.land].
    destruct (iv_aux iv); destruct (negb (_ =? 0)); cbn -[Z.land]; repeat split; reflexivity.
  Qed.

  Theorem sync_ok_shape : forall s zc,
    let '(s', r) := inflateSync_m iv s zc in
    zr_rc r = Z_OK ->
    is_mode s' = TYPE /\ is_flags s' = is_flags s /\ is_wbits s' = is_wbits s /\ is_havedict s' = 0
    /\ is_wrap s' = (if is_flags s =? -1 then 0 else Z.land (is_wrap s) (Z.lnot 4)) /\ zs_msg (zr_strm r) = MSG_NULL.
  Proof.
    intros s zc. unfold inflateSync_m.
    destruct (inflateStateCheck s) eqn:CK; [intros X; discriminate X|].
    destruct ((zlength (zc_input zc) =? 0) && (is_bits s <? 8)); [intros X; discriminate X|].
    change (if negb (is_mode s =? SYNC) then _ else s) with (if negb (is_mode s =? SYNC) then sync_entry s else s).
    assert (S1 : exists s1, (if negb (is_mode s =? SYNC) then sync_entry s else s) = s1
                 /\ is_flags s1 = is_flags s /\ is_wrap s1 = is_wrap s /\ is_wbits s1 = is_wbits s /\ is_mode s1 = SYNC).
    { destruct (Z.eqb_spec (is_mode s) SYNC) as [E|NE]; cbn [negb].
      - exists s. repeat split; try reflexivity. exact E.
      - exists (sync_entry s). split; [reflexivity|]. exact (sync_entry_keep s). }
    destruct S1 as (s1 & -> & F1 & W1 & B1 & M1).
    destruct (syncsearch (is_have s1) (zc_input zc)) as [got len].
    cbn [fst snd].
    replace (is_have (iset_have s1 got)) with got by (destruct s1; reflexivity).
    destruct (negb (got =? 4)); [intros X; discriminate X|].
    set (s3 := if is_flags (iset_have s1 got) =? -1 then _ else _).
    assert (E3 : is_flags s3 = is_flags s /\ is_wbits s3 = is_wbits s /\ is_mode s3 = SYNC
                 /\ is_wrap s3 = (if is_flags s =? -1 then 0 else Z.land (is_wrap s) (Z.lnot 4))).
    { subst s3. replace (is_flags (iset_have s1 got)) with (is_flags s) by (destruct s1; cbn in F1 |- *; congruence).
      replace (is_wrap (iset_have s1 got)) with (is_wrap s) by (destruct s1; cbn in W1 |- *; congruence).
      destruct (is_flags s =? -1); destruct s1; cbn in F1, W1, B1, M1 |- *; subst; repeat split; reflexivity. }
    destruct E3 as (F3 & B3 & M3 & W3).
    assert (CK3 : inflateStateCheck s3 = false) by (unfold inflateStateCheck; rewrite M3; reflexivity).
    pose proof (reset_keep s3 (zs_set_total_in (wrap64 (zs_total_in (zc_strm zc) + len)) (zc_strm zc)) CK3) as RK.
    destruct (inflateReset iv s3 _) as [[s4 z4] rc4]. destruct RK as (W4 & B4 & HD4 & MSG4).
    intros _. cbn [fst snd zr_strm].
    destruct s4; destruct z4; cbn in W4, B4, HD4, MSG4 |- *. subst.
    repeat split; try reflexivity; try assumption.
  Qed.
End S.
