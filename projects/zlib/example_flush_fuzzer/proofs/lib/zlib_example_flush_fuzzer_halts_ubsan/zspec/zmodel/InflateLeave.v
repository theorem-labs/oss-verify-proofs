(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb ModelRel
  FillWinModel InflateInv InflateInvRun InflateInvTab InflateInvKit InflateInvApi InflateInvLoop InflateInvCall InflateIeqApi
  HarnessKit HarnessFacts.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition WCH (s s' : inflate_state) : Prop :=
  exists ws wh wn w, s' = iset_whave (iset_wnext (iset_window (iset_wsize s ws) w) wn) wh.
Lemma WCH_refl : forall s, WCH s s.
Proof. intros s. exists (is_wsize s), (is_whave s), (is_wnext s), (is_window s). destruct s; reflexivity. Qed.
Lemma WCH_whave : forall s s' v, WCH s s' -> WCH s (iset_whave s' v).
Proof. intros s s' v (ws & wh & wn & w & ->). exists ws, v, wn, w. destruct s; reflexivity. Qed.
Lemma WCH_wnext : forall s s' v, WCH s s' -> WCH s (iset_wnext s' v).
Proof. intros s s' v (ws & wh & wn & w & ->). exists ws, wh, v, w. destruct s; reflexivity. Qed.
Lemma WCH_window : forall s s' v, WCH s s' -> WCH s (iset_window s' v).
Proof. intros s s' v (ws & wh & wn & w & ->). exists ws, wh, wn, v. destruct s; reflexivity. Qed.
Lemma WCH_wsize : forall s s' v, WCH s s' -> WCH s (iset_wsize s' v).
Proof. intros s s' v (ws & wh & wn & w & ->). exists v, wh, wn, w. destruct s; reflexivity. Qed.

Lemma uw_core_shape : forall s src e c,
  exists ws wh wn w, uw_core s src e c = iset_whave (iset_wnext (iset_window (iset_wsize s ws) w) wn) wh.
Proof.
  intros s src e c. change (WCH s (uw_core s src e c)). unfold uw_core.
  destruct (is_wsize s =? 0);
  repeat (match goal with |- context [if ?cnd then _ else _] => destruct cnd end);
  repeat first [ apply WCH_whave | apply WCH_wnext | apply WCH_window | apply WCH_wsize | apply WCH_refl ].
Qed.

Definition uwA (s : inflate_state) : inflate_state :=
  if is_wsize s =? 0 then iset_whave (iset_wnext (iset_wsize s (shl32 1 (is_wbits s))) 0) 0 else s.

Lemma uw_core_uwA : forall s src e c,
  uw_core s src e c =
  (let s := uwA s in
   if is_wsize s <=? c then
     let s := iset_window s (arr_blit (is_window s) 0 src (e - is_wsize s) (is_wsize s)) in
     iset_whave (iset_wnext s 0) (is_wsize s)
   else
     let dist := wrap32 (is_wsize s - is_wnext s) in
     let dist := if c <? dist then c else dist in
     let s := iset_window s (arr_blit (is_window s) (is_wnext s) src (e - c) dist) in
     let c := wrap32 (c - dist) in
     if negb (c =? 0) then
       let s := iset_window s (arr_blit (is_window s) 0 src (e - c) c) in
       iset_whave (iset_wnext s c) (is_wsize s)
     else
       let s := iset_wnext s (wrap32 (is_wnext s + dist)) in
       let s := if is_wnext s =? is_wsize s then iset_wnext s 0 else s in
       let s := if is_whave s <? is_wsize s then iset_whave s (wrap32 (is_whave s + dist)) else s in
       s).
Proof. reflexivity. Qed.

Lemma uw_core_wfacts : forall s src e c,
  8 <= is_wbits s <= 15 -> arr_len (is_window s) = 2 ^ is_wbits s ->
  (is_wsize s = 0 \/ is_wsize s = arr_len (is_window s)) ->
  0 <= is_whave s < 2 ^ 32 -> 0 <= is_wnext s < 2 ^ 32 ->
  (is_wsize s <> 0 -> is_wnext s <= is_wsize s /\ is_whave s <= is_wsize s) ->
  (is_wsize s <> 0 -> is_whave s < is_wsize s -> is_wnext s = is_whave s) ->
  0 <= c < 2 ^ 32 ->
  let s' := uw_core s src e c in
  is_wsize s' = arr_len (is_window s) /\ 0 <= is_wnext s' <= arr_len (is_window s) /\ 0 <= is_whave s' <= arr_len (is_window s)
  /\ (is_whave s' < arr_len (is_window s) -> is_wnext s' = is_whave s')
  /\ arr_len (is_window s') = arr_len (is_window s).
Proof.
  intros s src e c Hwb HWN Hwsz Hwh Hwn Hwhn Hinv Hc. cbv zeta.
  assert (HWN0 : 256 <= arr_len (is_window s) <= 32768).
  { rewrite HWN. split; [change 256 with (2 ^ 8) | change 32768 with (2 ^ 15)]; apply Z.pow_le_mono_r; lia. }
  set (WN := arr_len (is_window s)) in *.
  assert (Hsh : shl32 1 (is_wbits s) = WN) by (rewrite shl32_wbits by lia; subst WN; rewrite HWN; reflexivity).
  rewrite uw_core_uwA.
  assert (SA : is_wsize (uwA s) = WN /\ 0 <= is_wnext (uwA s) <= WN /\ 0 <= is_whave (uwA s) <= WN
               /\ (is_whave (uwA s) < WN -> is_wnext (uwA s) = is_whave (uwA s))
               /\ is_window (uwA s) = is_window s).
  { unfold uwA. destruct (Z.eqb_spec (is_wsize s) 0) as [Hw0|Hw0].
    - cbn [is_wsize is_wnext is_whave is_window iset_whave iset_wnext iset_wsize]. rewrite Hsh. repeat split; try reflexivity; lia.
    - specialize (Hwhn Hw0). specialize (Hinv Hw0). destruct Hwsz as [?|Hws]; [contradiction|]. rewrite <- Hws. repeat split; try reflexivity; try lia. }
  cbv zeta. set (s1 := uwA s) in *. clearbody s1. destruct SA as (W1 & W2 & W3 & W4 & W5).
  destruct (Z.leb_spec (is_wsize s1) c) as [Hle|Hgt].
  - cbn [is_wsize is_wnext is_whave is_window iset_whave iset_wnext iset_window]. rewrite W1.
    rewrite arr_len_blit, W5. repeat split; lia.
  - rewrite W1 in Hgt |- *.
    assert (Hd0 : wrap32 (WN - is_wnext s1) = WN - is_wnext s1) by (apply wrap32_id; lia).
    rewrite Hd0.
    set (dist := if c <? WN - is_wnext s1 then c else WN - is_wnext s1).
    assert (Hdist : 0 <= dist <= c /\ dist <= WN - is_wnext s1 /\ (dist = c \/ dist = WN - is_wnext s1)).
    { subst dist. destruct (Z.ltb_spec c (WN - is_wnext s1)); lia. }
    clearbody dist.
    assert (Hcd : wrap32 (c - dist) = c - dist) by (apply wrap32_id; lia). rewrite Hcd.
    destruct (Z.eqb_spec (c - dist) 0) as [Hz|Hz]; cbn [negb].
    + assert (Hnd : wrap32 (is_wnext s1 + dist) = is_wnext s1 + dist) by (apply wrap32_id; lia).
      cbn [is_wnext is_wsize is_whave is_window iset_wnext iset_window iset_whave]. rewrite ?Hnd, ?W1.
      destruct (Z.eqb_spec (is_wnext s1 + dist) WN) as [Heq|Heq];
        cbn [is_whave is_wsize is_wnext is_window iset_wnext iset_window iset_whave]; rewrite ?W1;
        destruct (Z.ltb_spec (is_whave s1) WN) as [Hlt|Hlt];
        cbn [is_whave is_wsize is_wnext is_window iset_wnext iset_window iset_whave]; rewrite ?W1;
        rewrite ?arr_len_blit, ?W5.
      * specialize (W4 Hlt). rewrite (wrap32_id (is_whave s1 + dist)) by lia. repeat split; lia.
      * repeat split; lia.
      * specialize (W4 Hlt). rewrite (wrap32_id (is_whave s1 + dist)) by lia. repeat split; lia.
      * repeat split; lia.
    + cbn [is_whave is_wsize is_wnext is_window iset_wnext iset_window iset_whave].
      rewrite !arr_len_blit, W5. repeat split; lia.
Qed.

Lemma uw_core_bytes : forall s src e c,
  8 <= is_wbits s <= 15 -> arr_len (is_window s) = 2 ^ is_wbits s ->
  (is_wsize s = 0 \/ is_wsize s = arr_len (is_window s)) ->
  0 <= is_whave s < 2 ^ 32 -> 0 <= is_wnext s < 2 ^ 32 ->
  (is_wsize s <> 0 -> is_wnext s <= is_wsize s /\ is_whave s <= is_wsize s) ->
  0 <= c < 2 ^ 32 ->
  (forall i, 0 <= i < arr_len (is_window s) -> 0 <= arr_get (is_window s) i < 256) ->
  (forall i, 0 <= i < c -> 0 <= arr_get src (e - c + i) < 256) ->
  forall i, 0 <= i < arr_len (is_window (uw_core s src e c)) -> 0 <= arr_get (is_window (uw_core s src e c)) i < 256.
Proof.
  intros s src e c Hwb HWN Hwsz Hwh Hwn Hwhn Hc Hwinb Hsrc.
  assert (HWN0 : 256 <= arr_len (is_window s) <= 32768).
  { rewrite HWN. split; [change 256 with (2 ^ 8) | change 32768 with (2 ^ 15)]; apply Z.pow_le_mono_r; lia. }
  set (WN := arr_len (is_window s)) in *.
  assert (Hsh : shl32 1 (is_wbits s) = WN) by (rewrite shl32_wbits by lia; subst WN; rewrite HWN; reflexivity).
  rewrite uw_core_uwA.
  assert (SA : is_wsize (uwA s) = WN /\ 0 <= is_wnext (uwA s) <= WN /\ is_window (uwA s) = is_window s).
  { unfold uwA. destruct (Z.eqb_spec (is_wsize s) 0) as [Hw0|Hw0].
    - cbn [is_wsize is_wnext is_whave is_window iset_whave iset_wnext iset_wsize]. rewrite Hsh. repeat split; try reflexivity; lia.
    - specialize (Hwhn Hw0). destruct Hwsz as [?|Hws]; [contradiction|]. rewrite <- Hws. repeat split; try reflexivity; try lia. }
  cbv zeta. set (s1 := uwA s) in *. clearbody s1. destruct SA as (W1 & W2 & W5).
  assert (SRC : forall k, e - c <= k < e -> 0 <= arr_get src k < 256).
  { intros k Hk. replace k with (e - c + (k - (e - c))) by lia. apply Hsrc. lia. }
  destruct (Z.leb_spec (is_wsize s1) c) as [Hle|Hgt].
  - cbn [is_wsize is_wnext is_whave is_window iset_whave iset_wnext iset_window]. rewrite W1, W5.
    rewrite arr_len_blit. intros i Hi. rewrite arr_get_blit.
    match goal with |- context [if ?cnd then _ else _] => destruct cnd eqn:Ec end; [| apply Hwinb; exact Hi].
    apply SRC. apply andb_prop in Ec as [Ec _]. apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite W1 in Hle. lia.
  - rewrite W1 in Hgt |- *.
    assert (Hd0 : wrap32 (WN - is_wnext s1) = WN - is_wnext s1) by (apply wrap32_id; lia).
    rewrite Hd0.
    set (dist := if c <? WN - is_wnext s1 then c else WN - is_wnext s1).
    assert (Hdist : 0 <= dist <= c /\ dist <= WN - is_wnext s1 /\ (dist = c \/ dist = WN - is_wnext s1)).
    { subst dist. destruct (Z.ltb_spec c (WN - is_wnext s1)); lia. }
    clearbody dist.
    assert (Hcd : wrap32 (c - dist) = c - dist) by (apply wrap32_id; lia). rewrite Hcd.
    rewrite W5.
    assert (B1 : forall i, 0 <= i < WN -> 0 <= arr_get (arr_blit (is_window s) (is_wnext s1) src (e - c) dist) i < 256).
    { intros i Hi. rewrite arr_get_blit.
      match goal with |- context [if ?cnd then _ else _] => destruct cnd eqn:Ec end; [| apply Hwinb; exact Hi].
      apply SRC. apply andb_prop in Ec as [Ec _]. apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia. }
    destruct (Z.eqb_spec (c - dist) 0) as [Hz|Hz]; cbn [negb].
    + cbn [is_wnext is_wsize is_whave is_window iset_wnext iset_window iset_whave].
      destruct (wrap32 (is_wnext s1 + dist) =? is_wsize s1);
        cbn [is_whave is_wsize is_wnext is_window iset_wnext iset_window iset_whave];
        match goal with |- context [if ?cnd then _ else _] => destruct cnd | _ => idtac end;
        cbn [is_whave is_wsize is_wnext is_window iset_wnext iset_window iset_whave];
        rewrite arr_len_blit; exact B1.
    + cbn [is_whave is_wsize is_wnext is_window iset_wnext iset_window iset_whave].
      rewrite !arr_len_blit. intros i Hi. rewrite arr_get_blit.
      match goal with |- context [if ?cnd then _ else _] => destruct cnd eqn:Ec end; [| apply B1; exact Hi].
      apply SRC. apply andb_prop in Ec as [Ec _]. apply andb_prop in Ec as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.


Definition cRest (c : icall) (r : iregs) : icall :=
  icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r).
Lemma RESTORE_eq : forall s c r, RESTORE (mkW s c r) = mkW (iset_bits (iset_hold s (ir_hold r)) (ir_bits r)) (cRest c r) r.
Proof. reflexivity. Qed.

Definition lv_out (r : iregs) : Z := ir_out r - ir_left r.
Definition lv_in (r : iregs) : Z := ir_in r - ir_have r.
Definition lv_upd (r : iregs) (s0 : inflate_state) : bool := negb (Z.land (is_wrap s0) 4 =? 0) && negb (lv_out r =? 0).
Definition lv_bytes (c : icall) (r : iregs) : list Z := arr_slice (ic_outbuf c) (ir_put r - lv_out r) (lv_out r).
Definition lv_ck (c : icall) (r : iregs) (s0 : inflate_state) : Z :=
  if lv_upd r s0 then UPDATE_CHECK_bytes s0 (is_check s0) (lv_bytes c r) else is_check s0.
Definition lv_ad (c : icall) (r : iregs) (s0 : inflate_state) : Z :=
  if lv_upd r s0 then UPDATE_CHECK_bytes s0 (is_check s0) (lv_bytes c r) else ic_adler c.
Definition lv_rc (flush : Z) (r : iregs) : Z :=
  if (((lv_in r =? 0) && (lv_out r =? 0)) || (flush =? Z_FINISH)) && (ir_ret r =? Z_OK) then Z_BUF_ERROR else ir_ret r.
Definition dtv (s0 : inflate_state) : Z :=
  is_bits s0 + (if negb (is_last s0 =? 0) then 64 else 0) + (if is_mode s0 =? TYPE then 128 else 0)
  + (if (is_mode s0 =? LEN_) || (is_mode s0 =? COPY_) then 256 else 0).
Definition fin_s (s0 : inflate_state) (tt ck : Z) : inflate_state := iset_check (iset_total s0 tt) ck.
Definition fin_c (c : icall) (ti to ad dt : Z) : icall := icset_data_type (icset_adler (icset_total_out (icset_total_in c ti) to) ad) dt.

Transparent UPDATE_CHECK_bytes.
Lemma leave_tail_eq : forall flush s0 c r,
  0 <= lv_out r < 2 ^ 32 -> 0 <= lv_in r < 2 ^ 32 ->
  leave_tail flush s0 (cRest c r) r =
  (fin_s s0 (wrap64 (is_total s0 + lv_out r)) (lv_ck c r s0),
   zret_of_icall (fin_c (cRest c r) (wrap64 (ic_total_in c + lv_in r)) (wrap64 (ic_total_out c + lv_out r)) (lv_ad c r s0) (dtv s0))
                 (lv_rc flush r)).
Proof.
  intros flush s0 c r Ho Hi. unfold leave_tail, lv_ck, lv_ad, lv_rc, lv_upd, lv_bytes, dtv, fin_s, fin_c, UPDATE_CHECK_bytes.
  destruct c; cbn -[Z.add Z.sub Z.mul Z.eqb Z.land Z.ltb wrap64 wrap32 iadler32_upd icrc32_upd arr_slice Z.pow lv_out lv_in Z_FINISH Z_OK Z_BUF_ERROR].
  change (ir_out r - ir_left r) with (lv_out r). change (ir_in r - ir_have r) with (lv_in r).
  rewrite !(wrap32_id (lv_out r)) by lia. rewrite !(wrap32_id (lv_in r)) by lia.
  destruct s0; cbn -[Z.add Z.sub Z.mul Z.eqb Z.land Z.ltb wrap64 wrap32 iadler32_upd icrc32_upd arr_slice Z.pow lv_out lv_in Z_FINISH Z_OK Z_BUF_ERROR].
  destruct (negb (Z.land is_wrap 4 =? 0) && negb (lv_out r =? 0));
    cbn -[Z.add Z.sub Z.mul Z.eqb Z.land Z.ltb wrap64 wrap32 iadler32_upd icrc32_upd arr_slice Z.pow lv_out lv_in Z_FINISH Z_OK Z_BUF_ERROR]; reflexivity.
Qed.
Opaque UPDATE_CHECK_bytes.


Lemma icore_fin : forall s tt ck, icore (fin_s s tt ck) = icore s.
Proof. intros []; reflexivity. Qed.
Lemma sinv_fin : forall s tt ck, sinv s -> sinv (fin_s s tt ck).
Proof.
  intros s tt ck SI. pose proof SI as (W1 & W2 & _).
  apply (sinv_core s (fin_s s tt ck) (icore_fin s tt ck)); [destruct s; exact W1 | destruct s; exact W2 | exact SI].
Qed.
Lemma binv_saved_fin : forall s tt ck, binv_saved s -> binv_saved (fin_s s tt ck).
Proof.
  intros s tt ck BI. apply (binv_saved_core s (fin_s s tt ck) (icore_fin s tt ck)); [destruct s; reflexivity | destruct s; reflexivity | exact BI].
Qed.
Lemma sinv_mem : forall s, sinv s -> sinv (iset_mode s MEM).
Proof.
  intros s SI. destruct SI as (W1 & W2 & AL & REST).
  unfold sinv. destruct s; cbn -[Z.le Z.lt Z.add Z.shiftl arr_len arr_get tables_ok ctab_ok tables_rep ctab_rep codes_live] in *.
  split; [exact W1|]. split; [exact W2|]. split; [exact AL|].
  repeat match goal with |- _ /\ _ => split end.
  all: intros HM; first [discriminate HM | destruct HM as [HM|HM]; discriminate HM].
Qed.
Lemma binv_saved_mem : forall s, binv_saved (iset_mode s MEM).
Proof. intros s. unfold binv_saved. destruct s; cbn -[Z.lt PEND]. right. exact I. Qed.
Lemma cks_mem : forall s, cks (iset_mode s MEM).
Proof. intros s. unfold cks. destruct s. cbn -[Z.le Z.land ck_adl]. intros HX. exfalso. unfold MEM, TYPE, CHECK in HX. lia. Qed.
Lemma cks_fin : forall s tt ck,
  cks s -> (TYPE <= is_mode s <= CHECK -> Z.land (is_wrap s) 4 <> 0 -> is_flags s = 0 -> ck = is_check s \/ ck_adl ck) ->
  cks (fin_s s tt ck).
Proof.
  intros s tt ck CK H. unfold cks in *. destruct s; cbn -[Z.le Z.land ck_adl] in *. intros Hm Hw Hf.
  destruct (H Hm Hw Hf) as [-> | X]; [exact (CK Hm Hw Hf) | exact X].
Qed.
Lemma cks_fin_lv : forall c r s0, cks s0 -> cks (fin_s s0 (wrap64 (is_total s0 + lv_out r)) (lv_ck c r s0)).
Proof.
  intros c r s0 CK. apply cks_fin; [exact CK|]. intros _ _ Hf0. unfold lv_ck.
  destruct (lv_upd r s0); [right; apply ck_adl_UPD; exact Hf0 | left; reflexivity].
Qed.

Lemma SRNGq_restore : forall s h b, SRNGq s -> 0 <= h < 2 ^ 64 -> 0 <= b < 2 ^ 32 -> SRNGq (iset_bits (iset_hold s h) b).
Proof.
  intros s h b H Hh Hb. destruct s. unfold SRNGq in *. cbn -[Z.pow Z.le Z.lt arr_get arr_len ARRB] in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
Qed.
Lemma SRNGq_mode : forall s m, SRNGq s -> HEAD <= m <= SYNC -> SRNGq (iset_mode s m).
Proof.
  intros s m H Hm. destruct s. unfold SRNGq in *. cbn -[Z.pow Z.le Z.lt arr_get arr_len ARRB] in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
Qed.
Lemma SRNGq_fin : forall s tt ck, SRNGq s -> 0 <= tt < 2 ^ 64 -> 0 <= ck < 2 ^ 64 -> SRNGq (fin_s s tt ck).
Proof.
  intros s tt ck H Ht Hc. destruct s. unfold fin_s, SRNGq in *. cbn -[Z.pow Z.le Z.lt arr_get arr_len ARRB] in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
Qed.
Lemma SRNGq_wset : forall s ws wh wn w,
  SRNGq s -> 0 <= ws < 2 ^ 32 -> 0 <= wh < 2 ^ 32 -> 0 <= wn < 2 ^ 32 ->
  (forall i, 0 <= i < arr_len w -> 0 <= arr_get w i < 256) ->
  (ws <> 0 -> wn <= ws /\ wh <= ws) -> (ws <> 0 -> wh < ws -> wn = wh) ->
  SRNGq (iset_whave (iset_wnext (iset_window (iset_wsize s ws) w) wn) wh).
Proof.
  intros s ws wh wn w H H1 H2 H3 H4 H5 H6. destruct s. unfold SRNGq in *. cbn -[Z.pow Z.le Z.lt arr_get arr_len ARRB] in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
Qed.
Lemma SRNGq_wblk : forall s b w, SRNGq s -> (forall i, 0 <= i < arr_len w -> 0 <= arr_get w i < 256) ->
  SRNGq (iset_window (iset_window_blk s (Some b)) w).
Proof.
  intros s b w H Hw. destruct s. unfold SRNGq in *. cbn -[Z.pow Z.le Z.lt arr_get arr_len ARRB] in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
Qed.

Lemma wset_facts : forall s ws wh wn w,
  let s' := iset_whave (iset_wnext (iset_window (iset_wsize s ws) w) wn) wh in
  is_wsize s' = ws /\ is_whave s' = wh /\ is_wnext s' = wn /\ is_window s' = w
  /\ icore s' = icore s /\ is_hold s' = is_hold s /\ is_bits s' = is_bits s /\ is_check s' = is_check s
  /\ is_window_blk s' = is_window_blk s /\ is_wbits s' = is_wbits s.
Proof. intros [] ws wh wn w; cbn; repeat split; reflexivity. Qed.

Lemma fin_facts : forall s tt ck,
  is_hold (fin_s s tt ck) = is_hold s /\ is_bits (fin_s s tt ck) = is_bits s
  /\ is_window_blk (fin_s s tt ck) = is_window_blk s /\ is_window (fin_s s tt ck) = is_window s
  /\ is_wbits (fin_s s tt ck) = is_wbits s /\ is_wsize (fin_s s tt ck) = is_wsize s.
Proof. intros [] tt ck; cbn; repeat split; reflexivity. Qed.

Lemma mem_facts : forall s,
  is_hold (iset_mode s MEM) = is_hold s /\ is_bits (iset_mode s MEM) = is_bits s
  /\ is_window_blk (iset_mode s MEM) = is_window_blk s /\ is_window (iset_mode s MEM) = is_window s
  /\ is_wbits (iset_mode s MEM) = is_wbits s /\ is_wsize (iset_mode s MEM) = is_wsize s.
Proof. intros []; cbn; repeat split; reflexivity. Qed.

Lemma hb_facts : forall s h b,
  let s' := iset_bits (iset_hold s h) b in
  is_hold s' = h /\ is_bits s' = b /\ is_window_blk s' = is_window_blk s /\ is_window s' = is_window s
  /\ is_wbits s' = is_wbits s /\ is_wsize s' = is_wsize s /\ is_whave s' = is_whave s /\ is_wnext s' = is_wnext s
  /\ icore s' = icore s /\ is_check s' = is_check s.
Proof. intros [] h b; cbn; repeat split; reflexivity. Qed.

Lemma fresh_facts : forall s b g,
  let s1 := uw_fresh s b g in
  is_window_blk s1 = Some b /\ is_window s1 = iarr_u8_of g 0 (shl32 1 (is_wbits s)) /\ is_wbits s1 = is_wbits s /\ is_wsize s1 = is_wsize s
  /\ is_whave s1 = is_whave s /\ is_wnext s1 = is_wnext s /\ is_hold s1 = is_hold s /\ is_bits s1 = is_bits s
  /\ icore s1 = icore s /\ is_check s1 = is_check s.
Proof. intros [] b g; cbn; repeat split; reflexivity. Qed.

Lemma fin_c_facts : forall c2 ti to ad dt,
  let c := fin_c c2 ti to ad dt in
  ic_next_in c = ic_next_in c2 /\ ic_avail_in c = ic_avail_in c2 /\ ic_next_out c = ic_next_out c2 /\ ic_avail_out c = ic_avail_out c2
  /\ ic_total_in c = ti /\ ic_total_out c = to /\ ic_adler c = ad /\ ic_data_type c = dt /\ ic_outbuf c = ic_outbuf c2
  /\ ic_msg c = ic_msg c2 /\ ic_input c = ic_input c2.
Proof. intros [] ti to ad dt; cbn; repeat split; reflexivity. Qed.

Lemma cRest_facts : forall c r,
  ic_next_in (cRest c r) = ir_next r /\ ic_avail_in (cRest c r) = ir_have r /\ ic_next_out (cRest c r) = ir_put r
  /\ ic_avail_out (cRest c r) = ir_left r /\ ic_total_in (cRest c r) = ic_total_in c /\ ic_total_out (cRest c r) = ic_total_out c
  /\ ic_adler (cRest c r) = ic_adler c /\ ic_data_type (cRest c r) = ic_data_type c /\ ic_outbuf (cRest c r) = ic_outbuf c.
Proof. intros [] r; cbn; repeat split; reflexivity. Qed.

Transparent UPDATE_CHECK_bytes.
Lemma UPDATE_CHECK_range : forall s ck bs, Forall (fun b => 0 <= b < 256) bs -> 0 <= UPDATE_CHECK_bytes s ck bs < 2 ^ 64.
Proof.
  intros s ck bs Hb. unfold UPDATE_CHECK_bytes. destruct (negb (is_flags s =? 0)); [apply icrc32_upd_range; exact Hb | apply iadler32_upd_range].
Qed.
Opaque UPDATE_CHECK_bytes.

Lemma lv_bytes_ok : forall NO c r, CINV (arr_len (ic_input c)) NO c -> RINV (arr_len (ic_input c)) NO r ->
  Forall (fun b => 0 <= b < 256) (lv_bytes c r).
Proof.
  intros NO c r CI RI. unfold lv_bytes, lv_out.
  destruct CI as (_ & ClNO & _ & _ & _ & _ & _ & _ & _ & Coutb & _). destruct RI as (_ & _ & _ & Rpt & Rlf & Rpl & _ & Rout & Rol & _).
  apply Forall_forall. intros b Hb. apply (arr_slice_In _ _ _ b) in Hb; [exact Hb|]. intros i Hi. apply Coutb. lia.
Qed.

Lemma dtv_range : forall s0, 0 <= is_bits s0 < 64 -> - 2 ^ 31 <= dtv s0 < 2 ^ 31.
Proof.
  intros s0 Hb. unfold dtv.
  destruct (negb (is_last s0 =? 0)); destruct (is_mode s0 =? TYPE); destruct ((is_mode s0 =? LEN_) || (is_mode s0 =? COPY_)); lia.
Qed.


Definition LVPOST (flush : Z) (c : icall) (r : iregs) (z : ZRet) : Prop :=
  zr_consumed z = ir_next r /\ zlength (zr_output z) = ir_put r
  /\ ((zr_rc z = lv_rc flush r /\ zs_total_out (zr_strm z) = wrap64 (ic_total_out c + lv_out r)
       /\ zs_total_in (zr_strm z) = wrap64 (ic_total_in c + lv_in r))
      \/ zr_rc z = Z_MEM_ERROR).

Theorem leave_p_ui : forall ans flush NI NO WN TOT0 s c r,
  0 <= NI < 2 ^ 32 -> 0 <= NO < 2 ^ 32 -> XPOST NI NO WN TOT0 (mkW s c r) ->
  let '(p, asked) := inf_leave_p ans flush (mkW s c r) in
  UI (fst p) /\ zret_ok (snd p) /\ LVPOST flush c r (snd p).
Proof.
  intros ans flush NI NO WN TOT0 s c r HNI HNO (LR & SI & BI & CK). cbn [w_s] in SI, CK.
  pose proof LR as LR0. apply LRNGq_iff in LR. destruct LR as (SR & CI & RI & WI & CR).
  pose proof SR as SR0. unfold SRNGq in SR.
  destruct SR as (Smode & Slast & Swrap & Shd & Sflags & Sdmax & Scheck & Stotal & Swbits & Swsize & Swhave & Swnext & Shold & Sbits & _).
  pose proof CI as CI0. unfold CINV in CI. destruct CI as (ClNI & ClNO & Cni & Cai & Cnai & Cno & Cao & Cnao & Cinb & Coutb & Cti & Cto & Cad & Cdt).
  pose proof RI as RI0. unfold RINV in RI. destruct RI as (Rnx & Rhv & Rnh & Rpt & Rlf & Rpl & Rin & Rout & Rol & Rbits & Rhold).
  unfold WINV in WI. destruct WI as (WL & WP & WNiff & Wsz).
  assert (Hhold64 : 0 <= ir_hold r < 2 ^ 64).
  { split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Rhold)|]. apply Z.pow_le_mono_r; lia. }
  assert (Hout : 0 <= lv_out r < 2 ^ 32) by (unfold lv_out; lia). assert (Hin : 0 <= lv_in r < 2 ^ 32) by (unfold lv_in; lia).
  unfold inf_leave_p. rewrite RESTORE_eq. cbn [w_s w_c w_r].
  set (sR := iset_bits (iset_hold s (ir_hold r)) (ir_bits r)).
  pose proof (hb_facts s (ir_hold r) (ir_bits r)) as (Qhold & Qbits & Qwblk & Qwin & Qwbits & Qwsize & Qwhave & Qwnext & Qcore & Qcheck).
  fold sR in Qhold, Qbits, Qwblk, Qwin, Qwbits, Qwsize, Qwhave, Qwnext, Qcore, Qcheck.
  assert (SRr : SRNGq sR) by (apply SRNGq_restore; [exact SR0 | exact Hhold64 | lia]).
  assert (SIr : sinv sR) by (exact (sinv_restore s (ir_hold r) (ir_bits r) SI)).
  assert (BIr : binv_saved sR) by (exact (binv_saved_restore s c r BI)).
  assert (CKr : cks sR) by (exact (cks_restore s (ir_hold r) (ir_bits r) CK)).
  pose proof (cRest_facts c r) as (Kni & Kai & Kno & Kao & Kti & Kto & Kad & Kdt & Kob).
  set (GOOD := fun s0 : inflate_state =>
         SRNGq s0 /\ sinv s0 /\ binv_saved s0 /\ cks s0
         /\ is_hold s0 = ir_hold r /\ is_bits s0 = ir_bits r
         /\ match is_window_blk s0 with
            | Some _ => arr_len (is_window s0) = 2 ^ is_wbits s0 /\ (is_wsize s0 = 0 \/ is_wsize s0 = 2 ^ is_wbits s0)
            | None => arr_len (is_window s0) = 0 /\ is_wsize s0 = 0
            end).
  assert (GR : GOOD sR).
  { subst GOOD. cbv beta. split; [exact SRr|]. split; [exact SIr|]. split; [exact BIr|]. split; [exact CKr|].
    split; [exact Qhold|]. split; [exact Qbits|]. rewrite Qwblk, Qwin, Qwbits, Qwsize.
    destruct (is_window_blk s) as [b|].
    - assert (Hn : WN <> 0) by (intros X; pose proof (proj1 WNiff X) as Y; discriminate Y).
      destruct WP as [P|P]; [exfalso; exact (Hn P)|]. rewrite WL. split; [exact P | rewrite <- P; exact Wsz].
    - assert (E0 : WN = 0) by (apply (proj2 WNiff); reflexivity). rewrite WL, E0. split; [reflexivity|].
      rewrite E0 in Wsz. destruct Wsz as [X|X]; exact X. }
  assert (KONT : forall so : option inflate_state,
            match so with None => True | Some s0 => GOOD s0 end ->
            let p := match so with
                     | None => (iset_mode sR MEM, zret_of_icall (cRest c r) Z_MEM_ERROR)
                     | Some s' => leave_tail flush s' (cRest c r) r
                     end in
            UI (fst p) /\ zret_ok (snd p) /\ LVPOST flush c r (snd p)).
  { intros [s0|] G; cbv zeta.
    - subst GOOD. cbv beta in G. destruct G as (G1 & G2 & G3 & G4 & Gh & Gb & Gw).
      rewrite (leave_tail_eq flush s0 c r Hout Hin). cbn [fst snd].
      pose proof (fin_facts s0 (wrap64 (is_total s0 + lv_out r)) (lv_ck c r s0)) as (Fhold & Fbits & Fwblk & Fwin & Fwbits & Fwsize).
      assert (Hck0 : 0 <= is_check s0 < 2 ^ 64) by (unfold SRNGq in G1; destruct G1 as (_ & _ & _ & _ & _ & _ & X & _); exact X).
      pose proof (lv_bytes_ok NO c r ltac:(rewrite ClNI; exact CI0) ltac:(rewrite ClNI; exact RI0)) as BY.
      assert (Hck : 0 <= lv_ck c r s0 < 2 ^ 64) by (unfold lv_ck; destruct (lv_upd r s0); [apply UPDATE_CHECK_range; exact BY | exact Hck0]).
      assert (Had : 0 <= lv_ad c r s0 < 2 ^ 64) by (unfold lv_ad; destruct (lv_upd r s0); [apply UPDATE_CHECK_range; exact BY | exact Cad]).
      assert (Htt : 0 <= wrap64 (is_total s0 + lv_out r) < 2 ^ 64) by (apply wrap64_range).
      split.
      + split.
        { split; [apply SRNGq_fin; [exact G1 | exact Htt | exact Hck]|].
          rewrite Fhold, Fbits, Fwblk, Fwin, Fwbits, Fwsize, Gh, Gb. split; [exact (conj Rbits Rhold) | exact Gw]. }
        split; [apply sinv_fin; exact G2|]. split; [apply binv_saved_fin; exact G3|]. apply cks_fin_lv. exact G4.
      + pose proof (fin_c_facts (cRest c r) (wrap64 (ic_total_in c + lv_in r)) (wrap64 (ic_total_out c + lv_out r)) (lv_ad c r s0) (dtv s0)) as CF.
        cbv zeta in CF. destruct CF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
        pose proof (dtv_range s0 ltac:(rewrite Gb; exact Rbits)) as Hdt.
        unfold zret_ok, LVPOST, zret_of_icall, zstrm_of_icall.
        cbn [zr_consumed zr_output zr_strm zr_rc zs_total_in zs_total_out zs_adler zs_data_type].
        rewrite E1, E3, E5, E6, E7, E8, E9, Kni, Kno, Kob. rewrite arr_slice_length.
        pose proof (wrap64_range (ic_total_in c + lv_in r)). pose proof (wrap64_range (ic_total_out c + lv_out r)).
        split; [repeat split; lia|]. split; [reflexivity|]. split; [lia|]. left. repeat split; reflexivity.
    - cbn [fst snd]. pose proof (mem_facts sR) as (Mh & Mb & Mwblk & Mwin & Mwbits & Mwsize).
      split.
      + split.
        { split; [apply SRNGq_mode; [exact SRr | unfold HEAD, MEM, SYNC; lia]|].
          rewrite Mh, Mb, Mwblk, Mwin, Mwbits, Mwsize, Qhold, Qbits. split; [exact (conj Rbits Rhold)|].
          subst GOOD. cbv beta in GR. destruct GR as (_ & _ & _ & _ & _ & _ & Gw). exact Gw. }
        split; [apply sinv_mem; exact SIr|]. split; [apply binv_saved_mem | apply cks_mem].
      + unfold zret_ok, LVPOST, zret_of_icall, zstrm_of_icall.
        cbn [zr_consumed zr_output zr_strm zr_rc zs_total_in zs_total_out zs_adler zs_data_type].
        rewrite Kni, Kno, Kob, Kti, Kto, Kad, Kdt, arr_slice_length.
        split; [repeat split; lia|]. split; [reflexivity|]. split; [lia|]. right. reflexivity. }
  pose proof (hb_facts s (ir_hold r) (ir_bits r)) as HB. cbv zeta in HB.
  replace (wrap32 (ir_out r - ic_avail_out (cRest c r))) with (lv_out r) by (rewrite Kao; symmetry; apply wrap32_id; exact Hout).
  rewrite Kob, Kno.
  destruct (leave_need flush sR (cRest c r) r).
  -
    assert (UW : forall s1, GOOD s1 -> is_window_blk s1 <> None -> GOOD (uw_core s1 (ic_outbuf c) (ir_put r) (lv_out r))).
    { intros s1 G1 Hsome. subst GOOD. cbv beta in G1 |- *. destruct G1 as (G1 & G2 & G3 & G4 & Gh & Gb & Gw).
      destruct (is_window_blk s1) as [b|] eqn:Eb; [| exfalso; exact (Hsome eq_refl)]. destruct Gw as [GL GS].
      pose proof G1 as G1'. unfold SRNGq in G1'.
      destruct G1' as (_ & _ & _ & _ & _ & _ & _ & _ & Ywbits & Ywsize & Ywhave & Ywnext & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ywinb & Ywhn & Ywnh).
      pose proof (uw_core_wfacts s1 (ic_outbuf c) (ir_put r) (lv_out r) Ywbits GL (ltac:(destruct GS as [X|X]; [left; exact X | right; rewrite X, GL; reflexivity]))
                    Ywhave Ywnext Ywhn Ywnh Hout) as WF. cbv zeta in WF. destruct WF as (F1 & F2 & F3 & F4 & F5).
      pose proof (uw_core_bytes s1 (ic_outbuf c) (ir_put r) (lv_out r) Ywbits GL (ltac:(destruct GS as [X|X]; [left; exact X | right; rewrite X, GL; reflexivity]))
                    Ywhave Ywnext Ywhn Hout Ywinb ltac:(intros i Hi; apply Coutb; unfold lv_out in *; lia)) as WB.
      destruct (uw_core_shape s1 (ic_outbuf c) (ir_put r) (lv_out r)) as (ws & wh & wn & w & EQ).
      rewrite EQ in F1, F2, F3, F4, F5, WB |- *.
      pose proof (wset_facts s1 ws wh wn w) as X. cbv zeta in X.
      destruct X as (Xws & Xwh & Xwn & Xw & Xcore & Xhold & Xbits & Xcheck & Xwblk & Xwbits).
      rewrite Xws in F1. rewrite Xwn in F2, F4. rewrite Xwh in F3, F4. rewrite Xw in F5, WB.
      assert (HWNb : 256 <= arr_len (is_window s1) <= 32768).
      { rewrite GL. split; [change 256 with (2 ^ 8) | change 32768 with (2 ^ 15)]; apply Z.pow_le_mono_r; lia. }
      split.
      { apply SRNGq_wset; [exact G1 | lia | lia | lia | exact WB | intros _; lia | intros _ Hlt; apply F4; lia]. }
      split; [apply (sinv_core s1); [exact Xcore | rewrite Xwh, Xws; lia | rewrite Xwn, Xws; lia | exact G2]|].
      split; [apply (binv_saved_core s1); [exact Xcore | exact Xhold | exact Xbits | exact G3]|].
      split; [apply (cks_core s1); [exact Xcore | exact Xcheck | exact G4]|].
      split; [rewrite Xhold; exact Gh|]. split; [rewrite Xbits; exact Gb|].
      rewrite Xwblk, Eb, Xw, Xwbits, Xws, F5, F1. split; [exact GL | right; exact GL]. }
    rewrite Qwblk. destruct (is_window_blk s) as [b|] eqn:Ewb.
    +
      exact (KONT (Some _) (UW sR GR ltac:(rewrite Qwblk; intros X; discriminate X))).
    + destruct ans as [[b g]|].
      *
        apply (KONT (Some _)). apply UW; [| cbn [uw_fresh is_window_blk iset_window iset_window_blk]; destruct sR; cbn; intros X; discriminate X].
        assert (E0 : WN = 0) by (apply (proj2 WNiff); reflexivity).
        subst GOOD. cbv beta in GR |- *. destruct GR as (G1 & G2 & G3 & G4 & Gh & Gb & Gw).
        pose proof (fresh_facts sR b g) as X. cbv zeta in X.
        destruct X as (Xwblk & Xw & Xwbits & Xws & Xwh & Xwn & Xhold & Xbits & Xcore & Xcheck).
        assert (WB : forall i, 0 <= i < arr_len (is_window (uw_fresh sR b g)) -> 0 <= arr_get (is_window (uw_fresh sR b g)) i < 256).
        { intros i _. rewrite Xw. unfold iarr_u8_of. rewrite arr_get_init. unfold init_u8. pose proof (wrap8_range (g (0 + i))). lia. }
        split; [unfold uw_fresh; apply SRNGq_wblk; [exact G1 | intros i Hi; apply WB; rewrite Xw; exact Hi]|].
        split; [apply (sinv_core sR); [exact Xcore | rewrite Xwh, Xws, Qwhave, Qwsize; unfold sinv in SI; lia | rewrite Xwn, Xws, Qwnext, Qwsize; unfold sinv in SI; lia | exact G2]|].
        split; [apply (binv_saved_core sR); [exact Xcore | exact Xhold | exact Xbits | exact G3]|].
        split; [apply (cks_core sR); [exact Xcore | exact Xcheck | exact G4]|].
        split; [rewrite Xhold; exact Gh|]. split; [rewrite Xbits; exact Gb|].
        rewrite Xwblk, Xw, Xwbits, Xws, Qwbits, Qwsize. unfold iarr_u8_of. rewrite arr_len_init, shl32_wbits by lia.
        split; [reflexivity|]. left. rewrite E0 in Wsz. destruct Wsz as [X|X]; exact X.
      * exact (KONT None Logic.I).
  -
    exact (KONT (Some sR) GR).
Qed.
