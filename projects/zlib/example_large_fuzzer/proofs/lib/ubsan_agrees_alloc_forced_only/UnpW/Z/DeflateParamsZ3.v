(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel FlushBlockModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflateRel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL1 RefDeflSafeZ. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeG. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored1 RefDeflStored2 RefDeflStored3 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI3 RefDeflSafeI4 RefDeflSafeL0.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import DeflateParamsDD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zt (s : deflate_state) :=
  (ds_match_length s, ds_level s, ds_strategy s, ds_last_flush s, ds_lookahead s, (ds_head s, ds_prev s, ds_hash_size s, ds_w_size s, ds_w_mask s)).
(* [comment removed for export] *)
Definition zk (s : deflate_state) := (zt s, ds_strstart s, ds_matches s).

Lemma keeps_zk : keeps zk true false.
Proof. constructor; intros; try discriminate; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.

Lemma zk_fields : forall a b, zk b = zk a -> zt b = zt a /\ ds_strstart b = ds_strstart a /\ ds_matches b = ds_matches a.
Proof. intros a b E. unfold zk in E. apply pair_equal_spec in E. destruct E as [E E3]. apply pair_equal_spec in E. destruct E as [E1 E2]. auto. Qed.

Lemma zt_fields : forall a b, zt b = zt a ->
  ds_match_length b = ds_match_length a /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a /\ ds_last_flush b = ds_last_flush a /\ ds_lookahead b = ds_lookahead a
  /\ ds_head b = ds_head a /\ ds_prev b = ds_prev a /\ ds_hash_size b = ds_hash_size a /\ ds_w_size b = ds_w_size a /\ ds_w_mask b = ds_w_mask a.
Proof.
  intros a b E. unfold zt in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Definition SINV (s : deflate_state) : Prop :=
  0 <= ds_matches s
  /\ (ds_matches s = 0 -> CHAIN s (ds_strstart s - 1) (ds_strstart s - 1))
  /\ (ds_matches s = 1 -> CHAIN s (ds_strstart s + ds_w_size s - 1) (ds_strstart s + ds_w_size s - 1)).

Lemma SINV_same : forall a b, zt b = zt a -> ds_strstart b = ds_strstart a -> ds_matches b = ds_matches a -> SINV a -> SINV b.
Proof.
  intros a b E Es Em (H0 & H1 & H2). pose proof (zt_fields a b E) as (_ & _ & _ & _ & _ & Eh & Ep & Ehs & Ews & Ewm).
  unfold SINV. rewrite Es, Em, Ews. split; [exact H0|].
  split; intros M; apply (CHAIN_same a b); try assumption; [apply H1 | apply H2]; exact M.
Qed.

Lemma SINV_zk : forall a b, zk b = zk a -> SINV a -> SINV b.
Proof. intros a b E H. destruct (zk_fields a b E) as (E1 & E2 & E3). exact (SINV_same a b E1 E2 E3 H). Qed.

Lemma SINV_grow : forall a b, zt b = zt a -> ds_strstart a <= ds_strstart b -> ds_matches b = ds_matches a -> SINV a -> SINV b.
Proof.
  intros a b E Es Em (H0 & H1 & H2). pose proof (zt_fields a b E) as (_ & _ & _ & _ & _ & Eh & Ep & Ehs & Ews & Ewm).
  unfold SINV. rewrite Em, Ews. split; [exact H0|].
  split; intros M; apply (CHAIN_same a b); try assumption.
  - apply (CHAIN_mono a (ds_strstart a - 1) (ds_strstart a - 1)); [lia | lia | exact (H1 M)].
  - apply (CHAIN_mono a (ds_strstart a + ds_w_size a - 1) (ds_strstart a + ds_w_size a - 1)); [lia | lia | exact (H2 M)].
Qed.

Lemma SINV_slide : forall a b, zt b = zt a -> ds_strstart b = ds_strstart a - ds_w_size a ->
  ds_matches b = (if ds_matches a <? 2 then ds_matches a + 1 else ds_matches a) -> SINV a -> SINV b.
Proof.
  intros a b E Es Em (H0 & H1 & H2). pose proof (zt_fields a b E) as (_ & _ & _ & _ & _ & Eh & Ep & Ehs & Ews & Ewm).
  unfold SINV. rewrite Em, Es, Ews. destruct (Z.ltb_spec (ds_matches a) 2) as [L|L].
  - split; [lia|]. split; intros M; [exfalso; lia|].
    apply (CHAIN_same a b); try assumption. replace (ds_strstart a - ds_w_size a + ds_w_size a - 1) with (ds_strstart a - 1) by lia. apply H1. lia.
  - split; [lia|]. split; intros M; exfalso; lia.
Qed.

Lemma SINV_supplant : forall b, ds_matches b = 2 -> SINV b.
Proof. intros b Em. unfold SINV. rewrite Em. split; [lia|]. split; intros M; discriminate M. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zk_flush_pending : forall s, zk (flush_pending s) = zk s.
Proof.
  intros s. rewrite flush_pending_eq. cbv zeta.
  pose proof (k_bi_flush zk true false keeps_zk eq_refl s) as EB. unfold tr_flush_bits.
  destruct (fp_len _ =? 0); [exact EB|].
  unfold fp_tail. destruct (_ =? 0); (etransitivity; [|exact EB]); reflexivity.
Qed.

Lemma zk_read_buf : forall s dst n, zk (fst (read_buf s dst n)) = zk s.
Proof.
  intros s dst n. unfold read_buf. cbv zeta. destruct (_ =? 0); [reflexivity|].
  destruct dst; destruct (ds_wrap s =? 1); [|destruct (ds_wrap s =? 2)| |destruct (ds_wrap _ =? 2)]; reflexivity.
Qed.

Lemma zk_rdo : forall x len, zk (st_rdo x len) = zk x.
Proof.
  intros x len. unfold st_rdo. destruct (negb (len =? 0)); [|reflexivity].
  pose proof (zk_read_buf x RB_next_out len) as H.
  destruct (read_buf x RB_next_out len) as [x' k]. cbn [fst] in H. etransitivity; [|exact H]. reflexivity.
Qed.

Lemma zk_copy : forall x left len, zk (fst (st_copy x left len)) = zk x.
Proof. intros x left len. unfold st_copy. destruct (negb (left =? 0)); reflexivity. Qed.

Lemma zk_emit1 : forall x fl, zk (st_emit1 x fl) = zk x.
Proof.
  intros x fl. unfold st_emit1. rewrite zk_flush_pending. unfold sb_patch. cbv zeta.
  rewrite (k_pending_buf zk true false keeps_zk eq_refl). apply (k_tr_stored_block zk true false keeps_zk eq_refl).
Qed.

Lemma zk_trip : forall s flush, zk (st_trip s flush) = zk s.
Proof. intros s flush. unfold st_trip. rewrite zk_rdo, zk_copy. apply zk_emit1. Qed.

Lemma zk_loop : forall fuel s flush mb, zk (fst (deflate_stored_loop fuel s flush mb)) = zk s.
Proof.
  induction fuel as [|f IH]; intros s flush mb; [reflexivity|].
  rewrite sloop_S'. destruct (sb_broke s flush mb); [reflexivity|].
  destruct (sb_lastv s flush =? 0); [rewrite IH|cbn [fst]]; apply zk_trip.
Qed.

Lemma zk_hw : forall s, zk (hw_st s) = zk s.
Proof. intros s. unfold hw_st. destruct (_ <? _); reflexivity. Qed.

Lemma zk_final : forall s flush, zk (fst (st_final s flush)) = zk s.
Proof.
  intros s flush. unfold st_final. cbv zeta. destruct (_ || _); [|reflexivity]. cbn [fst].
  rewrite zk_flush_pending. etransitivity; [|apply (k_tr_stored_block zk true false keeps_zk eq_refl)]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wupd_SINV : forall s used, 0 <= used -> SINV s ->
  zt (st_wupd s used) = zt s /\ SINV (st_wupd s used).
Proof.
  intros s used Hu HS. unfold st_wupd.
  destruct (negb (used =? 0)); [|split; [reflexivity | exact HS]].
  destruct (Z.leb_spec (ds_w_size s) used) as [C1|C1].
  - split; [reflexivity|]. apply SINV_supplant. reflexivity.
  - set (a := set_matches (set_strstart s (ds_strstart s - ds_w_size s)) (if ds_matches s <? 2 then ds_matches s + 1 else ds_matches s)).
    assert (SL : SINV a) by (apply (SINV_slide s); [reflexivity | reflexivity | reflexivity | exact HS]).
    destruct (Z.leb_spec (ds_window_size s - ds_strstart s) used) as [C2|C2].
    + dsred. destruct (ds_matches s <? 2) eqn:Em; dsred; destruct (ds_strstart s - ds_w_size s <? ds_insert s); dsred.
      all: split; [reflexivity|].
      all: apply (SINV_grow a); [reflexivity | subst a; dsred; clear - Hu; lia | subst a; dsred; rewrite ?Em; reflexivity | exact SL].
    + dsred. split; [reflexivity|]. apply (SINV_grow s); [reflexivity | dsred; clear - Hu; lia | reflexivity | exact HS].
Qed.

Lemma slide3_SINV : forall s have, SINV s ->
  zt (fst (st_slide3 s have)) = zt s /\ SINV (fst (st_slide3 s have)).
Proof.
  intros s have HS. unfold st_slide3. destruct (_ && _); cbn [fst]; [|split; [reflexivity | exact HS]].
  set (a := set_matches (set_strstart s (ds_strstart s - ds_w_size s)) (if ds_matches s <? 2 then ds_matches s + 1 else ds_matches s)).
  assert (SL : SINV a) by (apply (SINV_slide s); [reflexivity | reflexivity | reflexivity | exact HS]).
  dsred. destruct (ds_matches s <? 2) eqn:Em; dsred; destruct (ds_strstart s - ds_w_size s <? ds_insert s); dsred.
  all: split; [reflexivity|].
  all: apply (SINV_same a); [reflexivity | subst a; dsred; reflexivity | subst a; dsred; rewrite ?Em; reflexivity | exact SL].
Qed.

Lemma fillw_SINV : forall s have, 0 <= have -> SINV s ->
  zt (st_fillw s have) = zt s /\ SINV (st_fillw s have).
Proof.
  intros s have Hh HS. unfold st_fillw. destruct (negb (have =? 0)); [|split; [reflexivity | exact HS]].
  pose proof (zk_read_buf s (RB_window (ds_strstart s)) have) as ER.
  destruct (read_buf s (RB_window (ds_strstart s)) have) as [x k]. cbn [fst] in ER.
  destruct (zk_fields _ _ ER) as (E1 & E2 & E3).
  split; [etransitivity; [|exact E1]; reflexivity|].
  apply (SINV_grow s); [etransitivity; [|exact E1]; reflexivity | dsred; rewrite E2; lia | dsred; exact E3 | exact HS].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ZLS0 (s : deflate_state) : Prop :=
  ds_match_length s = 2
  /\ (ds_matches s = 0 -> CHAIN s (ds_strstart s - 1) (ds_strstart s - 1))
  /\ (ds_matches s = 1 -> CHAIN s (ds_strstart s + ds_w_size s - 1) (ds_strstart s + ds_w_size s - 1)).

Theorem stored_ZLS0 : forall c0 s flush, BFPRE c0 s flush -> dmode s = 0 -> ZLS0 s ->
  let s' := fst (deflate_stored s flush) in zt s' = zt s /\ ZLS0 s'.
Proof.
  intros c0 s flush (HC0 & HDC & Hp & Hst & Hfl) Hm (Eml & C0 & C1) s'. subst s'. pose proof (c0'_ok _ HC0) as HC0w.
  assert (HS : SI c0 s s).
  { split; [exact HDC|]. split; [reflexivity|]. split; [exact Hm|]. split; [exact Hst|]. split; [apply OUTLE_refl | exact Hp]. }
  pose proof HDC as [[D X] V].
  pose proof (SI_facts c0 s HC0 s HS) as (_ & _ & _ & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & _).
  assert (HS0 : SINV s) by (split; [clear - Hmt; lia | exact (conj C0 C1)]).
  assert (GOAL : forall s', zt s' = zt s -> SINV s' -> zt s' = zt s /\ ZLS0 s').
  { intros t Et (_ & T0 & T1). split; [exact Et|]. split; [| exact (conj T0 T1)]. destruct (zt_fields _ _ Et) as (E1 & _). rewrite E1. exact Eml. }
  rewrite deflate_stored_eq. cbv zeta.
  set (mb := wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s))). clearbody mb.
  set (fuel := Z.to_nat (cs_avail_out (ds_strm s) + 1)). clearbody fuel.
  destruct (loop_stage c0 s flush HC0 fuel s mb HS) as [HSL HaiL].
  pose proof (zk_loop fuel s flush mb) as EKL.
  assert (EX : exists x, x = fst (deflate_stored_loop fuel s flush mb)) by (eexists; reflexivity). destruct EX as [sL EsL]. rewrite <- EsL in *.
  assert (EX : exists x, x = snd (deflate_stored_loop fuel s flush mb)) by (eexists; reflexivity). destruct EX as [last Elast]. rewrite <- Elast in *.
  pose proof (SINV_zk _ _ EKL HS0) as HSL'. destruct (zk_fields _ _ EKL) as (EtL & _ & _).
  pose proof (SI_facts c0 s HC0 sL HSL) as (DL & XL & VL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HaiL2 & _).
  assert (Eused : wrap32 (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL)) = cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL))
    by (apply wrap32_id; clear - HaiL Hai HaiL2; lia).
  rewrite Eused.
  pose proof (sv_inlen _ _ V) as Il. pose proof (sv_inlen _ _ VL) as IlL. pose proof (sv_nin _ _ V) as Ni.
  pose proof (wupd_stage c0 s HC0 sL (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL)) HSL ltac:(clear - HaiL Il IlL Ni; lia)) as W. cbv zeta in W.
  destruct W as (HSW & EstrmW & HbsW).
  destruct (wupd_SINV sL (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL)) ltac:(clear - HaiL; lia) HSL') as [EtW HSW'].
  assert (EX : exists x, x = st_wupd sL (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL))) by (eexists; reflexivity). destruct EX as [sW EsW]. rewrite <- EsW in *.
  pose proof (hw_stage c0 s HC0 sW HSW) as (HS2 & Estrm2 & Estr2 & Ebs2 & Ewsz2 & Ews2 & _).
  pose proof (SINV_zk _ _ (zk_hw sW) HSW') as HS2'. destruct (zk_fields _ _ (zk_hw sW)) as (Et2 & _ & _).
  assert (EX : exists x, x = hw_st sW) by (eexists; reflexivity). destruct EX as [s2 Es2]. rewrite <- Es2 in *.
  pose proof HS2 as (HDC2 & HK2 & Hm2 & Hst2 & Ho2 & Hp2).
  pose proof (SI_facts c0 s HC0 s2 HS2) as (D2 & X2 & V2 & Sw2 & _ & _ & Hl02 & Hbs2 & _ & _ & Hstr2 & Ewsz2' & _ & _ & _ & _ & _ & Hai2 & _).
  assert (Et2s : zt s2 = zt s) by (rewrite Et2, EtW; exact EtL).
  destruct (negb (last =? 0)); [cbn [fst]; exact (GOAL s2 Et2s HS2')|].
  match goal with |- context [if ?c then (s2, block_done) else _] => destruct c eqn:Hcond end; [cbn [fst]; exact (GOAL s2 Et2s HS2')|].
  assert (Ehave : wrap32 (ds_window_size s2 - ds_strstart s2) = 2 * ds_w_size s2 - ds_strstart s2) by (rewrite Ewsz2'; apply wrap32_id; clear - Hstr2 Hbs2 Sw2; lia).
  rewrite Ehave.
  pose proof (slide3_stage c0 s HC0 s2 _ HS2 eq_refl) as SL3. cbv zeta in SL3. destruct SL3 as (HS3 & Estrm3 & Ehave3 & Ews3).
  destruct (slide3_SINV s2 (2 * ds_w_size s2 - ds_strstart s2) HS2') as [Et3 HS3'].
  destruct (st_slide3 s2 (2 * ds_w_size s2 - ds_strstart s2)) as [s3 have]. cbn [fst snd] in *.
  pose proof (SI_facts c0 s HC0 s3 HS3) as (_ & _ & _ & _ & _ & _ & _ & Hbs3 & _ & _ & Hstr3 & _ & _ & _ & _ & _ & _ & Hai3 & _).
  assert (Hfm : 0 <= fmin have (cs_avail_in (ds_strm s3)) <= cs_avail_in (ds_strm s3) /\ fmin have (cs_avail_in (ds_strm s3)) <= 2 * ds_w_size s3 - ds_strstart s3).
  { unfold fmin. rewrite Ehave3, Ews3. destruct (Z.ltb_spec (cs_avail_in (ds_strm s3)) (2 * ds_w_size s2 - ds_strstart s3)) as [l|l]; clear - l Hai3 Hstr3 Hbs3 Ews3; lia. }
  pose proof (fillw_stage c0 s HC0 s3 (fmin have (cs_avail_in (ds_strm s3))) HS3 (proj1 Hfm) (proj2 Hfm)) as FW. cbv zeta in FW. destruct FW as (HS4 & _).
  destruct (fillw_SINV s3 (fmin have (cs_avail_in (ds_strm s3))) ltac:(clear - Hfm; lia) HS3') as [Et4 HS4'].
  assert (EX : exists x, x = st_fillw s3 (fmin have (cs_avail_in (ds_strm s3)))) by (eexists; reflexivity). destruct EX as [s4 Es4]. rewrite <- Es4 in *.
  pose proof (hw_stage c0 s HC0 s4 HS4) as (HS5 & _).
  pose proof (SINV_zk _ _ (zk_hw s4) HS4') as HS5'. destruct (zk_fields _ _ (zk_hw s4)) as (Et5 & _ & _).
  assert (EX : exists x, x = hw_st s4) by (eexists; reflexivity). destruct EX as [s5 Es5]. rewrite <- Es5 in *.
  pose proof (SINV_zk _ _ (zk_final s5 flush) HS5') as HSf. destruct (zk_fields _ _ (zk_final s5 flush)) as (Etf & _ & _).
  assert (EX : exists x, x = fst (st_final s5 flush)) by (eexists; reflexivity). destruct EX as [sf Esf]. rewrite <- Esf in *.
  apply (GOAL sf); [| exact HSf]. rewrite Etf, Et5, Et4, Et3. exact Et2s.
Qed.
