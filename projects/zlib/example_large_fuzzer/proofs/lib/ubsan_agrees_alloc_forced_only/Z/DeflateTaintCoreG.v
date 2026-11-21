(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeE1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL0.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintTrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintRelG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintBitsG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintLzG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintTallyG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintBlkG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintSlowG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintStored.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintStoredG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintCallG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma DREL_clean s1 s2 : DREL s1 s2 -> clean s1 = clean s2.
Proof. intros (W & C & B & bnd & ms & pm & R & _). exact (r_clean _ _ _ _ _ _ _ _ R). Qed.

(* [comment removed for export] *)
Lemma DQ_set_strm s1 s2 c : DQ s1 s2 -> DQ (set_strm s1 c) (set_strm s2 c).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_strm; exact R|]. unfold WHI, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.
Lemma DQ_set_last_flush s1 s2 v : DQ s1 s2 -> DQ (set_last_flush s1 v) (set_last_flush s2 v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_last_flush; exact R|]. unfold WHI, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.
Lemma DQ_err_return s1 s2 e : DQ s1 s2 -> snd (err_return s1 e) = snd (err_return s2 e) /\ DQ (fst (err_return s1 e)) (fst (err_return s2 e)).
Proof.
  intros D. pose proof (DQ_clean _ _ D) as EC. unfold err_return. cbn [fst snd]. split; [reflexivity|].
  rewrite <- (clean_eq_fieldT ds_strm _ _ EC ltac:(reflexivity)). apply DQ_set_strm. exact D.
Qed.
Lemma DREL_set_status s1 s2 v : DREL s1 s2 -> DREL (set_status s1 v) (set_status s2 v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_status; exact R|]. unfold WHI, PBC, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.
Lemma DREL_set_last_flush s1 s2 v : DREL s1 s2 -> DREL (set_last_flush s1 v) (set_last_flush s2 v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_last_flush; exact R|]. unfold WHI, PBC, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.
Lemma DREL_set_wrap s1 s2 v : DREL s1 s2 -> DREL (set_wrap s1 v) (set_wrap s2 v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_wrap; exact R|]. unfold WHI, PBC, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.
Lemma INVG_err_return s e : INVG s -> INVG (fst (err_return s e)).
Proof. intros I. unfold err_return. cbn [fst]. apply INVG_set_strm; [dsr; exact (ig_ain s I)|dsr; exact (ig_aout s I)|exact I]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bi_flush_noop s : ds_bi_valid s <= 7 -> ds_pending (bi_flush s) = ds_pending s.
Proof.
  intros H. rewrite bi_flush_pending. destruct (Z.eqb_spec (ds_bi_valid s) 16); [lia|]. destruct (Z.leb_spec 8 (ds_bi_valid s)); [lia|reflexivity].
Qed.

Lemma flush_pending_DREL W C B bnd ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 ->
  (forall i, i < WHI s1 -> W i) -> (ds_level s1 <> 0 -> bnd <= ds_strstart s1) -> SYMB B s1 -> HWI s1 ->
  0 <= ds_pending_out s1 -> (forall i, ds_pending_out s1 <= i < ds_pending_out s1 + ds_pending s1 -> B i) ->
  (ds_pending_out s1 = 0 \/ ds_pending (bi_flush s1) = ds_pending s1) ->
  ds_pending_out s1 + ds_pending (bi_flush s1) <= 65536 ->
  DREL (flush_pending s1) (flush_pending s2) /\ INVG (flush_pending s1) /\ INVG (flush_pending s2)
  /\ lzm (flush_pending s1) = lzm s1 /\ ds_sym_next (flush_pending s1) = ds_sym_next s1
  /\ cs_avail_in (ds_strm (flush_pending s1)) = cs_avail_in (ds_strm s1).
Proof.
  intros R I1 I2 HW Hb HS HH PO0 PB PZ HL.
  pose proof (ig_bl s1 I1) as BL1.
  pose proof (flush_pending_rel _ _ _ _ _ _ _ _ R I1 I2 PO0 ltac:(rewrite BL1; exact HL) PB PZ) as (R' & K1 & K2).
  pose proof (bi_flush_pending_le s1) as BFL.
  pose proof (flush_pending_shape s1 (ig_aout s1 I1) (ig_pend s1 I1) ltac:(lia)) as SH.
  cbv zeta in SH. destruct SH as (po & st & E & Ei & En & Ea & Eo & El & Hlen & Hpo & _).
  pose proof (k_bi_flush lzv true true keeps_lzv eq_refl s1) as L3.
  pose proof (k_bi_flush ds_sym_next true false keeps_sym_next eq_refl s1) as SN3.
  pose proof (ig_po _ K1) as PO'.
  revert R' K1 K2 PO'. rewrite E. set (s9 := bi_flush s1) in *. clearbody s9. set (t2 := flush_pending s2). clearbody t2. intros R' K1 K2 PO'.
  assert (LL : lzm s9 = lzm s1) by (apply lzm_of_lzv; exact L3).
  split; [|split; [exact K1|]; split; [exact K2|]; dsr; lzm_rw LL; split; [reflexivity|]; split; [exact SN3|rewrite Ea; reflexivity]].
  exists W, C, (Bx B (ds_pending s1) (ds_pending s9)), bnd, ms, pm. split; [exact R'|].
  revert PO'. unfold WHI, PBC, SYMB, HWI, Bx in *. lzm_rw LL. intros PO'.
  split; [exact HW|]. split; [exact Hb|]. split.
  { rewrite Eo. destruct Hpo as [[A1 A2]|[[A1 [A2 A3]]|[A1 A2]]].
    - left. split; [exact A2|intros; lia].
    - right. split; [lia|]. intros i Hi. destruct PZ as [PZ|PZ]; [|left; apply PB; lia].
      rewrite PZ in *. destruct (Z_lt_le_dec i (ds_pending s1)); [left; apply PB; lia|right; lia].
    - rewrite A1 in *. destruct (Z.eq_dec (ds_pending s9) 0) as [Z0|Z0].
      + left. split; [apply PO'; lia|intros; lia].
      + right. split; [lia|]. intros i Hi. destruct PZ as [PZ|PZ]; [|left; apply PB; lia].
        rewrite PZ in *. destruct (Z_lt_le_dec i (ds_pending s1)); [left; apply PB; lia|right; lia]. }
  rewrite ?SN3. split; [intros i Hi; left; apply HS; exact Hi|exact HH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma CFGG_lzv s t : lzv t = lzv s -> CFGG s -> CFGG t.
Proof.
  intros E (C1 & C2 & C3 & C4). pose proof (lzv_fields _ _ E) as F. repeat match type of F with _ /\ _ => destruct F as [? F] end.
  unfold CFGG. repeat match goal with H : ?f t = ?f s |- context [?f t] => rewrite H end. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Definition WRUN (s1 t1 t2 : deflate_state) : Prop :=
  exists W C B bnd ms pm,
    REL W C (Bx B 0 (ds_pending t1)) bnd ms pm t1 t2
    /\ (forall i, i < WHI s1 -> W i) /\ (ds_level s1 <> 0 -> bnd <= ds_strstart s1) /\ SYMB B s1 /\ HWI s1
    /\ lzm t1 = lzm s1 /\ ds_sym_next t1 = ds_sym_next s1 /\ ds_pending_out t1 = 0 /\ 0 <= ds_pending t1
    /\ cs_avail_in (ds_strm t1) = cs_avail_in (ds_strm s1) /\ cs_avail_out (ds_strm t1) = cs_avail_out (ds_strm s1).

Lemma WRUN_start s1 s2 : DREL s1 s2 -> INVG s1 -> ds_pending s1 = 0 -> WRUN s1 s1 s2.
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH) I1 Hp. pose proof (ig_po s1 I1 Hp) as Hpo.
  exists W, C, B, bnd, ms, pm. split; [rewrite Hp; apply rel_Bx_same; exact R|].
  split; [exact HW|]. split; [exact Hb|]. split; [exact HS|]. split; [exact HH|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hpo|]. split; [lia|]. split; reflexivity.
Qed.

Lemma WRUN_put_byte s1 t1 t2 c : WRUN s1 t1 t2 -> WRUN s1 (put_byte t1 c) (put_byte t2 c).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HS & HH & L & Esn & Hpo & Hp & Eai & Eao). exists W, C, B, bnd, ms, pm.
  split.
  { pose proof (put_byte_rel _ _ _ _ _ _ _ _ c R) as R1. rewrite put_byte_pending in *.
    apply (rel_weaken _ _ _ _ _ _ _ _ _ _ _ R1); [auto| |apply Z.le_refl]. unfold Bx. intros i [X|X]; [left; left; exact X|]. destruct (Z_lt_le_dec i (ds_pending t1)); [left; right; lia|right; lia]. }
  split; [exact HW|]. split; [exact Hb|]. split; [exact HS|]. split; [exact HH|].
  split; [rewrite <- L; reflexivity|]. unfold put_byte. dsr. split; [exact Esn|]. split; [exact Hpo|]. split; [lia|]. split; [exact Eai|exact Eao].
Qed.
Lemma WRUN_putShortMSB s1 t1 t2 b : WRUN s1 t1 t2 -> WRUN s1 (putShortMSB t1 b) (putShortMSB t2 b).
Proof. intros H. unfold putShortMSB. apply WRUN_put_byte, WRUN_put_byte, H. Qed.
Lemma WRUN_set_strm s1 t1 t2 st1 st2 :
  WRUN s1 t1 t2 -> st1 = st2 -> cs_avail_in st1 = cs_avail_in (ds_strm t1) -> cs_avail_out st1 = cs_avail_out (ds_strm t1) ->
  WRUN s1 (set_strm t1 st1) (set_strm t2 st2).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HS & HH & L & Esn & Hpo & Hp & Eai & Eao) <- E1 E2. exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_strm; exact R|]. split; [exact HW|]. split; [exact Hb|]. split; [exact HS|]. split; [exact HH|].
  split; [rewrite <- L; reflexivity|]. dsr. split; [exact Esn|]. split; [exact Hpo|]. split; [lia|]. rewrite E1, E2. split; [exact Eai|exact Eao].
Qed.
Lemma WRUN_set_status s1 t1 t2 v : WRUN s1 t1 t2 -> WRUN s1 (set_status t1 v) (set_status t2 v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HS & HH & L & Esn & Hpo & Hp & Eai & Eao). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_status; exact R|]. split; [exact HW|]. split; [exact Hb|]. split; [exact HS|]. split; [exact HH|].
  split; [rewrite <- L; reflexivity|]. dsr. split; [exact Esn|]. split; [exact Hpo|]. split; [lia|]. split; [exact Eai|exact Eao].
Qed.

(* [comment removed for export] *)
Lemma WRUN_flush s1 t1 t2 : WRUN s1 t1 t2 -> INVG t1 -> INVG t2 -> ds_bi_valid t1 <= 7 -> ds_pending t1 <= 65536 ->
  DREL (flush_pending t1) (flush_pending t2) /\ INVG (flush_pending t1) /\ INVG (flush_pending t2)
  /\ lzm (flush_pending t1) = lzm s1 /\ ds_sym_next (flush_pending t1) = ds_sym_next s1
  /\ cs_avail_in (ds_strm (flush_pending t1)) = cs_avail_in (ds_strm s1).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HS & HH & L & Esn & Hpo & Hp & Eai & Eao) K1 K2 Hbv Hpl.
  pose proof (bi_flush_noop t1 Hbv) as NB.
  assert (Lf : lzm t1 = lzm s1) by exact L.
  pose proof (lzm_fields _ _ L) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  pose proof (flush_pending_DREL W C (Bx B 0 (ds_pending t1)) bnd ms pm t1 t2 R K1 K2) as X.
  unfold WHI, SYMB, HWI in X, HW, HS, HH. rewrite E1, E2, E3, E4, E10, Esn, Hpo, NB in X.
  specialize (X HW Hb ltac:(intros i Hi; left; apply HS; exact Hi) HH ltac:(lia) ltac:(intros i Hi; right; lia) ltac:(left; reflexivity) ltac:(lia)).
  destruct X as (D & J1 & J2 & L' & Esn' & Eai'). split; [exact D|]. split; [exact J1|]. split; [exact J2|].
  rewrite L', Esn', Eai'. split; [exact Lf|]. split; [reflexivity|exact Eai].
Qed.

(* [comment removed for export] *)
Lemma putShortMSB_strstart s b : ds_strstart (putShortMSB s b) = ds_strstart s. Proof. reflexivity. Qed.
Lemma putShortMSB_strm s b : ds_strm (putShortMSB s b) = ds_strm s. Proof. reflexivity. Qed.

Lemma zhdr_WRUN s1 s2 : DREL s1 s2 -> INVG s1 -> ds_pending s1 = 0 ->
  WRUN s1 (zhdr_st s1) (zhdr_st s2) /\ ds_pending (zhdr_st s1) <= 6.
Proof.
  intros D I1 Hp. pose proof (WRUN_start s1 s2 D I1 Hp) as W0. pose proof (DREL_clean _ _ D) as EC.
  unfold zhdr_st. cbv zeta. rewrite !putShortMSB_strstart, !putShortMSB_strm. eqc_fields EC.
  match goal with |- context [putShortMSB s1 ?h] => set (hdr := h) end.
  pose proof (WRUN_putShortMSB _ _ _ hdr W0) as W1.
  destruct (Z.eqb_spec (ds_strstart s1) 0); cbn [negb]; rewrite !putShortMSB_strm; eqc_fields EC.
  - split; [|unfold putShortMSB, put_byte; dsr; lia].
    apply WRUN_set_status. eapply WRUN_set_strm; [exact W1|reflexivity|dsr; reflexivity|dsr; reflexivity].
  - set (a := cs_adler (ds_strm s1)).
    pose proof (WRUN_putShortMSB _ _ _ (Z.land a 65535) (WRUN_putShortMSB _ _ _ (wrap32 (Z.shiftr a 16)) W1)) as W3.
    split; [|unfold putShortMSB, put_byte; dsr; lia].
    apply WRUN_set_status. eapply WRUN_set_strm; [exact W3|reflexivity|dsr; reflexivity|dsr; reflexivity].
Qed.

Lemma put_byte_level s c : ds_level (put_byte s c) = ds_level s. Proof. reflexivity. Qed.
Lemma put_byte_strategy s c : ds_strategy (put_byte s c) = ds_strategy s. Proof. reflexivity. Qed.

Lemma set_strm_level s v : ds_level (set_strm s v) = ds_level s. Proof. reflexivity. Qed.
Lemma set_strm_strategy s v : ds_strategy (set_strm s v) = ds_strategy s. Proof. reflexivity. Qed.
Lemma set_strm_pending s v : ds_pending (set_strm s v) = ds_pending s. Proof. reflexivity. Qed.
Lemma set_status_pending s v : ds_pending (set_status s v) = ds_pending s. Proof. reflexivity. Qed.

Lemma cset_adler_avail_in c v : cs_avail_in (cset_adler c v) = cs_avail_in c. Proof. reflexivity. Qed.
Lemma cset_adler_avail_out c v : cs_avail_out (cset_adler c v) = cs_avail_out c. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma gzhdr_WRUN s1 s2 : DREL s1 s2 -> INVG s1 -> ds_pending s1 = 0 ->
  WRUN s1 (gzhdr_st s1) (gzhdr_st s2) /\ ds_pending (gzhdr_st s1) <= 10.
Proof.
  intros D I1 Hp. pose proof (WRUN_start s1 s2 D I1 Hp) as W0. pose proof (DREL_clean _ _ D) as EC.
  unfold gzhdr_st. cbv zeta. rewrite !put_byte_level, !put_byte_strategy, !set_strm_level, !set_strm_strategy. eqc_fields EC.
  split; [|rewrite set_status_pending, !put_byte_pending, set_strm_pending; lia].
  apply WRUN_set_status. repeat apply WRUN_put_byte.
  eapply WRUN_set_strm; [exact W0|reflexivity|rewrite cset_adler_avail_in; reflexivity|rewrite cset_adler_avail_out; reflexivity].
Qed.

Lemma trailer_WRUN s1 s2 : DREL s1 s2 -> INVG s1 -> ds_pending s1 = 0 ->
  WRUN s1 (trailer_st s1) (trailer_st s2) /\ ds_pending (trailer_st s1) <= 8.
Proof.
  intros D I1 Hp. pose proof (WRUN_start s1 s2 D I1 Hp) as W0. pose proof (DREL_clean _ _ D) as EC.
  unfold trailer_st. cbv zeta. eqc_fields EC.
  destruct (ds_wrap s1 =? 2).
  - split; [|rewrite !put_byte_pending; lia]. repeat apply WRUN_put_byte. exact W0.
  - split; [|rewrite !putShortMSB_pending; lia]. apply WRUN_putShortMSB, WRUN_putShortMSB. exact W0.
Qed.

Lemma INVG_zhdr s : INVG s -> INVG (zhdr_st s).
Proof.
  intros I. unfold zhdr_st. cbv zeta. rewrite !putShortMSB_strstart, !putShortMSB_strm. apply INVG_set_status.
  destruct (negb _); rewrite ?putShortMSB_strm;
    (apply INVG_set_strm; [rewrite cset_adler_avail_in; exact (ig_ain s I) | rewrite cset_adler_avail_out; exact (ig_aout s I) |]);
    repeat apply INVG_putShortMSB; exact I.
Qed.
Lemma INVG_gzhdr s : INVG s -> INVG (gzhdr_st s).
Proof.
  intros I. unfold gzhdr_st. cbv zeta. apply INVG_set_status. repeat apply INVG_put_byte.
  apply INVG_set_strm; [rewrite cset_adler_avail_in; exact (ig_ain s I)|rewrite cset_adler_avail_out; exact (ig_aout s I)|exact I].
Qed.
Lemma INVG_trailer s : INVG s -> INVG (trailer_st s).
Proof. intros I. unfold trailer_st. cbv zeta. destruct (_ =? 2); [repeat apply INVG_put_byte | repeat apply INVG_putShortMSB]; exact I. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Notation Hst := stored_bf_spec.
Local Notation Hhf := (huff_bf_spec FB_CALL_ok).
Local Notation Hrl := (rle_bf_spec FB_CALL_ok).
Local Notation Hfa := (fast_bf_spec FB_CALL_ok).
Local Notation Hsl := (slow_bf_spec FB_CALL_ok).

(* [comment removed for export] *)
Ltac eqc_goal EC :=
  lazymatch type of EC with clean ?s1 = clean ?s2 =>
  repeat match goal with
  | |- context [?f s2] =>
        lazymatch f with
        | ds_status => idtac | ds_pending_buf_size => idtac | ds_pending_out => idtac | ds_pending => idtac
        | ds_wrap => idtac | ds_gzhead => idtac | ds_method => idtac | ds_last_flush => idtac
        | ds_w_size => idtac | ds_w_bits => idtac | ds_w_mask => idtac | ds_window_size => idtac
        | ds_ins_h => idtac | ds_hash_size => idtac | ds_hash_bits => idtac | ds_hash_mask => idtac | ds_hash_shift => idtac
        | ds_block_start => idtac | ds_match_length => idtac | ds_match_available => idtac | ds_strstart => idtac
        | ds_lookahead => idtac | ds_prev_length => idtac | ds_max_chain_length => idtac | ds_max_lazy_match => idtac
        | ds_level => idtac | ds_strategy => idtac | ds_good_match => idtac | ds_nice_match => idtac
        | ds_lit_bufsize => idtac | ds_sym_next => idtac | ds_sym_end => idtac | ds_opt_len => idtac | ds_static_len => idtac
        | ds_matches => idtac | ds_insert => idtac | ds_bi_buf => idtac | ds_bi_valid => idtac | ds_high_water => idtac
        | ds_self_blk => idtac | ds_window_blk => idtac | ds_prev_blk => idtac | ds_head_blk => idtac | ds_pending_buf_blk => idtac
        | ds_strm => idtac
        end;
        let H := fresh in
        assert (H : f s2 = f s1) by (symmetry; apply (clean_eq_fieldT f s1 s2 EC); intros; reflexivity);
        rewrite H; clear H
  end end.

Lemma dmode_clean s1 s2 : clean s1 = clean s2 -> dmode s2 = dmode s1.
Proof. intros EC. unfold dmode. eqc_fields EC. reflexivity. Qed.

Section Core.
  Variable c0 : cstrm.
Variable s01 : deflate_state.
Variable s02 : deflate_state.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis Hs01 : ds_strm s01 = c0.
  Hypothesis Hs02 : ds_strm s02 = c0.
  Hypothesis D01 : dwf s01.
  Hypothesis D02 : dwf s02.

  Local Notation ST1 := (ST c0 s01).
  Local Notation ST2 := (ST c0 s02).

  (* [comment removed for export] *)
  Lemma rcf_rel s1 s2 flush :
    ST1 s1 -> ST2 s2 -> DREL s1 s2 -> INVG s1 -> INVG s2 -> ds_pending s1 = 0 -> ds_status s1 <> FINISH_STATE -> 0 <= flush <= 5 ->
    snd (run_compress_func s1 flush) = snd (run_compress_func s2 flush)
    /\ DREL (fst (run_compress_func s1 flush)) (fst (run_compress_func s2 flush))
    /\ INVG (fst (run_compress_func s1 flush)) /\ INVG (fst (run_compress_func s2 flush)).
  Proof.
    intros [H1 K1] [H2 K2] D I1 I2 Hp Hst0 Hfl. pose proof (DREL_clean _ _ D) as EC.
    assert (Hp2 : ds_pending s2 = 0) by (rewrite <- (clean_eq_fieldT ds_pending _ _ EC ltac:(reflexivity)); exact Hp).
    assert (Hst2 : ds_status s2 <> FINISH_STATE) by (rewrite <- (clean_eq_fieldT ds_status _ _ EC ltac:(reflexivity)); exact Hst0).
    assert (PRE1 : BFPRE c0 s1 flush) by (split; [exact HC0|]; split; [exact H1|]; split; [exact Hp|]; split; [exact Hst0|exact Hfl]).
    assert (PRE2 : BFPRE c0 s2 flush) by (split; [exact HC0|]; split; [exact H2|]; split; [exact Hp2|]; split; [exact Hst2|exact Hfl]).
    pose proof (dmode_clean _ _ EC) as Em.
    rewrite !run_compress_func_dmode, Em.
    pose proof (dmode_range s1) as Hm. pose proof (ig_strat s1 I1) as Sg.
    assert (NH : dmode s1 <> 1 /\ dmode s1 <> 2).
    { unfold dmode. destruct Sg as [Sg2 Sg3]. unfold Z_HUFFMAN_ONLY, Z_RLE.
      destruct (Z.eqb_spec (ds_strategy s1) 2); [lia|]. destruct (Z.eqb_spec (ds_strategy s1) 3); [lia|].
      destruct (ds_level s1 =? 0); [lia|]. destruct (ds_level s1 <=? 3); lia. }
    destruct (Z.eq_dec (dmode s1) 0) as [E0|E0].
    { rewrite E0. pose proof (SI_intro c0 s1 flush PRE1 E0) as G1. pose proof (SI_intro c0 s2 flush PRE2 ltac:(rewrite Em; exact E0)) as G2.
      pose proof (deflate_stored_relG c0 s1 s2 flush HC0 G1 G2 (DREL_FREL0 _ _ D (dmode0_level _ E0)) I1 I2) as (E & R & J1 & J2).
      split; [exact E|]. split; [exact (FREL0_DREL _ _ R)|]. split; [exact J1|exact J2]. }
    destruct (Z.eq_dec (dmode s1) 3) as [E3|E3].
    { rewrite E3.
      assert (G1 : FTI c0 s1 s1) by (split; [exact H1|]; split; [reflexivity|]; split; [exact Hp|]; split; [exact E3|]; split; [exact Hst0|apply OUTLE_refl]).
      assert (G2 : FTI c0 s2 s2) by (split; [exact H2|]; split; [reflexivity|]; split; [exact Hp2|]; split; [rewrite Em; exact E3|]; split; [exact Hst2|apply OUTLE_refl]).
      pose proof (deflate_fast_rel c0 s1 s2 flush HC0 FB_CALL_ok flush_block_rel_blk G1 G2 (DREL_FREL _ _ D (dmode3_level _ E3)) I1 I2 Hfl) as (E & R & J1 & J2).
      split; [exact E|]. split; [exact (FREL_DREL _ _ R)|]. split; [exact J1|exact J2]. }
    assert (E4 : dmode s1 = 4) by lia. rewrite E4.
    assert (G1 : STI c0 s1 s1) by (split; [exact H1|]; split; [reflexivity|]; split; [exact Hp|]; split; [exact E4|]; split; [exact Hst0|apply OUTLE_refl]).
    assert (G2 : STI c0 s2 s2) by (split; [exact H2|]; split; [reflexivity|]; split; [exact Hp2|]; split; [rewrite Em; exact E4|]; split; [exact Hst2|apply OUTLE_refl]).
    pose proof (deflate_slow_rel c0 s1 s2 flush HC0 FB_CALL_ok flush_block_rel_blk G1 G2 (DREL_FREL _ _ D (dmode4_level _ E4)) I1 I2 Hfl) as (E & R & J1 & J2).
    split; [exact E|]. split; [exact (FREL_DREL _ _ R)|]. split; [exact J1|exact J2].
  Qed.

  (* [comment removed for export] *)
  Lemma bdone_st_0 s : bdone_st s 0 = tr_stored_block s None 0 0.
  Proof. reflexivity. Qed.

  Lemma tsb0_pending_range s : 0 <= ds_pending s -> ds_pending s <= ds_pending (tr_stored_block s None 0 0) <= ds_pending s + 8.
  Proof.
    intros Hp. rewrite tr_stored_block_pending. pose proof (bi_windup_pending_mono (send_bits s (Z.shiftl STORED_BLOCK 1 + 0) 3)) as A.
    pose proof (send_bits_pending_mono s (Z.shiftl STORED_BLOCK 1 + 0) 3) as B0. lia.
  Qed.

  Lemma WRUN_tsb0 s1 s2 : DREL s1 s2 -> INVG s1 -> ds_pending s1 = 0 ->
    WRUN s1 (tr_stored_block s1 None 0 0) (tr_stored_block s2 None 0 0).
  Proof.
    intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH) I1 Hp. pose proof (ig_po s1 I1 Hp) as Hpo.
    pose proof (tr_stored_block_rel0 W C bnd ms pm B s1 s2 None 0 0 R ltac:(lia) ltac:(intros _; reflexivity) ltac:(intros off HH0; discriminate HH0)) as R1.
    rewrite Hp in R1.
    pose proof (k_tr_stored_block lzv true true keeps_lzv eq_refl s1 None 0 0) as L.
    pose proof (k_tr_stored_block ds_sym_next true false keeps_sym_next eq_refl s1 None 0 0) as Esn.
    pose proof (k_tr_stored_block ds_strm true true keeps_strm eq_refl s1 None 0 0) as Est.
    pose proof (tsb0_pending_range s1 (ig_pend s1 I1)) as PR.
    pose proof (lzv_fields _ _ L) as F. destruct F as (_ & _ & Epo & _).
    exists W, C, B, bnd, ms, pm. split; [exact R1|].
    split; [exact HW|]. split; [exact Hb|]. split; [exact HS|]. split; [exact HH|].
    split; [exact (lzm_of_lzv _ _ L)|]. split; [exact Esn|]. split; [rewrite Epo; exact Hpo|]. split; [lia|]. rewrite Est. split; reflexivity.
  Qed.

  Lemma bdone0_rel s1 s2 :
    ST1 s1 -> ST2 s2 -> DREL s1 s2 -> INVG s1 -> INVG s2 -> ds_pending s1 = 0 -> ds_match_available s1 = 0 ->
    let t1 := flush_pending (tr_stored_block s1 None 0 0) in let t2 := flush_pending (tr_stored_block s2 None 0 0) in
    DREL t1 t2 /\ INVG t1 /\ INVG t2.
  Proof.
    intros [H1 K1] [H2 K2] D I1 I2 Hp Hma. pose proof (DREL_clean _ _ D) as EC.
    assert (Hp2 : ds_pending s2 = 0) by (rewrite <- (clean_eq_fieldT ds_pending _ _ EC ltac:(reflexivity)); exact Hp).
    assert (Hma2 : ds_match_available s2 = 0) by (rewrite <- (clean_eq_fieldT ds_match_available _ _ EC ltac:(reflexivity)); exact Hma).
    pose proof (bdone_facts c0 s1 0 H1 Hp Hma) as X1. pose proof (bdone_facts c0 s2 0 H2 Hp2 Hma2) as X2.
    cbv zeta in X1, X2. rewrite !bdone_st_0 in X1, X2.
    destruct X1 as (G1 & _ & _ & P1 & _). destruct X2 as (G2 & _).
    pose proof (WRUN_tsb0 s1 s2 D I1 Hp) as WR.
    pose proof (k_tr_stored_block lzv true true keeps_lzv eq_refl s1 None 0 0) as L1.
    pose proof (k_tr_stored_block lzv true true keeps_lzv eq_refl s2 None 0 0) as L2.
    assert (J1 : INVG (tr_stored_block s1 None 0 0)) by (apply (INVG_of_DC c0); [exact G1|apply (CFGG_lzv s1); [exact L1|exact (CFGG_of_INV _ I1)]]).
    assert (J2 : INVG (tr_stored_block s2 None 0 0)) by (apply (INVG_of_DC c0); [exact G2|apply (CFGG_lzv s2); [exact L2|exact (CFGG_of_INV _ I2)]]).
    pose proof (dx_biv _ (proj2 (proj1 G1))) as BV.
    pose proof (WRUN_flush s1 _ _ WR J1 J2 BV ltac:(lia)) as (DR & Q1 & Q2 & _).
    cbv zeta. split; [exact DR|]. split; [exact Q1|exact Q2].
  Qed.

  (* [comment removed for export] *)
  Lemma blocks_rel s1 s2 flush :
    ST1 s1 -> ST2 s2 -> DREL s1 s2 -> INVG s1 -> INVG s2 -> ds_pending s1 = 0 -> (flush = 0 \/ flush = 4 \/ flush = 5) ->
    (ds_status s1 = FINISH_STATE -> cs_avail_in (ds_strm s1) = 0) ->
    snd (deflate_blocks s1 flush) = snd (deflate_blocks s2 flush)
    /\ DQ (fst (deflate_blocks s1 flush)) (fst (deflate_blocks s2 flush))
    /\ INVG (fst (deflate_blocks s1 flush)) /\ INVG (fst (deflate_blocks s2 flush)).
  Proof.
    intros HS1 HS2 D I1 I2 Hp Hfl Hfin. pose proof HS1 as [H1 K1]. pose proof HS2 as [H2 K2]. pose proof H1 as [[DW1 X1] V1].
    pose proof (DREL_clean _ _ D) as EC.
    unfold deflate_blocks. eqc_fields EC.
    match goal with |- context [if ?c then _ else (s1, None)] => destruct c eqn:Hcond end.
    2:{ cbn [fst snd]. split; [reflexivity|]. split; [exact (DREL_DQ _ _ D)|]. split; [exact I1|exact I2]. }
    assert (Hst0 : ds_status s1 <> FINISH_STATE).
    { intros Ef. rewrite (Hfin Ef), (dx_fin _ X1 Ef), Ef in Hcond. cbn in Hcond. rewrite andb_false_r in Hcond. discriminate Hcond. }
    assert (Hp2 : ds_pending s2 = 0) by (rewrite <- (clean_eq_fieldT ds_pending _ _ EC ltac:(reflexivity)); exact Hp).
    assert (Hst2 : ds_status s2 <> FINISH_STATE) by (rewrite <- (clean_eq_fieldT ds_status _ _ EC ltac:(reflexivity)); exact Hst0).
    pose proof (rcf_rel s1 s2 flush HS1 HS2 D I1 I2 Hp Hst0 ltac:(lia)) as (Eb & Dr & J1 & J2).
    destruct (bf_call _ _ _ _ Hst Hhf Hrl Hfa Hsl c0 s01 HC0 s1 flush HS1 Hp Hst0 ltac:(lia)) as [_ P1].
    destruct (bf_call _ _ _ _ Hst Hhf Hrl Hfa Hsl c0 s02 HC0 s2 flush HS2 Hp2 Hst2 ltac:(lia)) as [_ P2].
    destruct (run_compress_func s1 flush) as [t1 b1]. destruct (run_compress_func s2 flush) as [t2 b2]. cbn [fst snd] in Eb, Dr, J1, J2, P1, P2. subst b2.
    unfold BFPOST in P1, P2. cbn [fst snd] in P1, P2. destruct P1 as (Ht1 & Kt1 & _ & Pbd1 & Pfin1 & Pfd1). destruct P2 as (Ht2 & Kt2 & _ & Pbd2 & Pfin2 & Pfd2).
    cbv zeta.
    set (u1 := if block_state_eqb b1 finish_started || block_state_eqb b1 finish_done then set_status t1 FINISH_STATE else t1).
    set (u2 := if block_state_eqb b1 finish_started || block_state_eqb b1 finish_done then set_status t2 FINISH_STATE else t2).
    assert (HU : DREL u1 u2 /\ INVG u1 /\ INVG u2 /\ (block_state_eqb b1 finish_started || block_state_eqb b1 finish_done = false -> u1 = t1 /\ u2 = t2)).
    { subst u1 u2. destruct (block_state_eqb b1 finish_started || block_state_eqb b1 finish_done).
      - split; [apply DREL_set_status; exact Dr|]. split; [apply INVG_set_status; exact J1|]. split; [apply INVG_set_status; exact J2|]. intros X; discriminate X.
      - split; [exact Dr|]. split; [exact J1|]. split; [exact J2|]. intros _; split; reflexivity. }
    clearbody u1 u2. destruct HU as (Du & Ku1 & Ku2 & Eu). pose proof (DREL_clean _ _ Du) as ECu.
    rewrite <- (clean_eq_fieldT ds_strm _ _ ECu ltac:(reflexivity)).
    destruct (block_state_eqb b1 need_more || block_state_eqb b1 finish_started) eqn:Enm.
    { cbn [fst snd]. split; [reflexivity|]. destruct (cs_avail_out (ds_strm u1) =? 0).
      - split; [apply DREL_DQ, DREL_set_last_flush; exact Du|]. split; apply INVG_set_last_flush; assumption.
      - split; [apply DREL_DQ; exact Du|]. split; assumption. }
    destruct (block_state_eqb b1 block_done) eqn:Ebd.
    - assert (E1 : b1 = block_done) by (destruct b1; cbn in Ebd; try discriminate Ebd; reflexivity). subst b1.
      destruct (Pbd1 eq_refl) as (Hpt1 & Hnf & Hma1). cbn in Eu. destruct (Eu eq_refl) as [-> ->].
      assert (St1 : ST1 t1) by (split; [exact Ht1|rewrite Kt1; exact K1]). assert (St2 : ST2 t2) by (split; [exact Ht2|rewrite Kt2; exact K2]).
      destruct (Z.eq_dec flush 5) as [F5|F5].
      { (* [comment removed for export] *)
        subst flush. change (5 =? Z_PARTIAL_FLUSH) with false. change (negb (5 =? Z_BLOCK)) with false. cbv iota.
        pose proof Du as (W & C & B & bnd & ms & pm & R & HW & Hb & HPB & HSY & HH).
        pose proof Ht1 as [[DWt1 Xt1] Vt1].
        pose proof (df_pend _ DWt1) as (PO0 & _ & _).
        pose proof (bi_flush_noop t1 (dx_biv _ Xt1)) as NB.
        pose proof (bi_flush_pending_le t1) as BFL.
        pose proof (flush_pending_DREL W C B bnd ms pm t1 t2 R Ku1 Ku2 HW Hb HSY HH PO0
                      ltac:(intros i Hi; exfalso; clear - Hi Hpt1; lia) (or_intror NB) ltac:(rewrite NB, Hpt1; clear - PO0 Hpt1 Ku1; pose proof (ig_po t1 Ku1 Hpt1); lia))
          as (Df & Kf1 & Kf2 & _).
        set (f1 := flush_pending t1) in *. set (f2 := flush_pending t2) in *. clearbody f1 f2.
        rewrite <- (clean_eq_fieldT ds_strm _ _ (DREL_clean _ _ Df) ltac:(reflexivity)).
        destruct (cs_avail_out (ds_strm f1) =? 0); cbn [fst snd].
        + split; [reflexivity|]. split; [apply DREL_DQ, DREL_set_last_flush; exact Df|]. split; apply INVG_set_last_flush; assumption.
        + split; [reflexivity|]. split; [apply DREL_DQ; exact Df|]. split; assumption. }
      assert (F0 : flush = 0) by (unfold Z_FINISH in Hnf; lia). subst flush.
      change (0 =? Z_PARTIAL_FLUSH) with false. change (negb (0 =? Z_BLOCK)) with true. change (0 =? Z_FULL_FLUSH) with false. cbv iota.
      pose proof (bdone0_rel t1 t2 St1 St2 Du Ku1 Ku2 Hpt1 Hma1) as (Df & Kf1 & Kf2). cbv zeta in Df, Kf1, Kf2.
      set (f1 := flush_pending (tr_stored_block t1 None 0 0)) in *. set (f2 := flush_pending (tr_stored_block t2 None 0 0)) in *. clearbody f1 f2.
      rewrite <- (clean_eq_fieldT ds_strm _ _ (DREL_clean _ _ Df) ltac:(reflexivity)).
      destruct (cs_avail_out (ds_strm f1) =? 0); cbn [fst snd].
      + split; [reflexivity|]. split; [apply DREL_DQ, DREL_set_last_flush; exact Df|]. split; apply INVG_set_last_flush; assumption.
      + split; [reflexivity|]. split; [apply DREL_DQ; exact Df|]. split; assumption.
    - cbn [fst snd]. split; [reflexivity|]. split; [apply DREL_DQ; exact Du|]. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma zhdr_rel s1 s2 :
    ST1 s1 -> DREL s1 s2 -> INVG s1 -> INVG s2 -> ds_pending s1 = 0 -> ds_status s1 = INIT_STATE ->
    let t1 := flush_pending (zhdr_st s1) in let t2 := flush_pending (zhdr_st s2) in
    DREL t1 t2 /\ INVG t1 /\ INVG t2.
  Proof.
    intros [H1 K1] D I1 I2 Hp Hst. pose proof (zhdr_WRUN s1 s2 D I1 Hp) as [WR PL].
    pose proof (zhdr_facts c0 s1 H1 Hp Hst) as X1. cbv zeta in X1. destruct X1 as ((G1 & _ & _) & _).
    pose proof (dx_biv _ (proj2 (proj1 G1))) as BV.
    pose proof (WRUN_flush s1 _ _ WR (INVG_zhdr _ I1) (INVG_zhdr _ I2) BV ltac:(lia)) as (DR & Q1 & Q2 & _).
    cbv zeta. split; [exact DR|]. split; [exact Q1|exact Q2].
  Qed.
  Lemma gzhdr_rel s1 s2 :
    ST1 s1 -> DREL s1 s2 -> INVG s1 -> INVG s2 -> ds_pending s1 = 0 -> ds_status s1 = GZIP_STATE ->
    let t1 := flush_pending (gzhdr_st s1) in let t2 := flush_pending (gzhdr_st s2) in
    DREL t1 t2 /\ INVG t1 /\ INVG t2.
  Proof.
    intros [H1 K1] D I1 I2 Hp Hst. pose proof (gzhdr_WRUN s1 s2 D I1 Hp) as [WR PL].
    pose proof (gzhdr_facts c0 s1 H1 Hp Hst) as X1. cbv zeta in X1. destruct X1 as ((G1 & _ & _) & _).
    pose proof (dx_biv _ (proj2 (proj1 G1))) as BV.
    pose proof (WRUN_flush s1 _ _ WR (INVG_gzhdr _ I1) (INVG_gzhdr _ I2) BV ltac:(lia)) as (DR & Q1 & Q2 & _).
    cbv zeta. split; [exact DR|]. split; [exact Q1|exact Q2].
  Qed.
  Lemma trailer_rel0 s1 s2 :
    ST1 s1 -> DREL s1 s2 -> INVG s1 -> INVG s2 -> ds_pending s1 = 0 ->
    let t1 := flush_pending (trailer_st s1) in let t2 := flush_pending (trailer_st s2) in
    DREL t1 t2 /\ INVG t1 /\ INVG t2.
  Proof.
    intros [H1 K1] D I1 I2 Hp. pose proof (trailer_WRUN s1 s2 D I1 Hp) as [WR PL].
    pose proof (trailer_facts c0 s1 H1 Hp) as X1. cbv zeta in X1. destruct X1 as ((G1 & _ & _) & _).
    pose proof (dx_biv _ (proj2 (proj1 G1))) as BV.
    pose proof (WRUN_flush s1 _ _ WR (INVG_trailer _ I1) (INVG_trailer _ I2) BV ltac:(lia)) as (DR & Q1 & Q2 & _).
    cbv zeta. split; [exact DR|]. split; [exact Q1|exact Q2].
  Qed.

  (* [comment removed for export] *)
  Definition RQ {A} (r1 r2 : deflate_state * A) : Prop := snd r1 = snd r2 /\ DQ (fst r1) (fst r2) /\ INVG (fst r1) /\ INVG (fst r2).
  Lemma RQ_I {A} a1 a2 (x : A) : DQ a1 a2 -> INVG a1 -> INVG a2 -> RQ (a1, x) (a2, x).
  Proof. intros D I1 I2. split; [reflexivity|]. split; [exact D|]. split; [exact I1|exact I2]. Qed.
  Lemma RQ_err a1 a2 e : DQ a1 a2 -> INVG a1 -> INVG a2 -> RQ (err_return a1 e) (err_return a2 e).
  Proof.
    intros D I1 I2. destruct (DQ_err_return a1 a2 e D) as [E D']. split; [exact E|]. split; [exact D'|]. split; apply INVG_err_return; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma trailer_rel s1 s2 :
    ST1 s1 -> DREL s1 s2 -> INVG s1 -> INVG s2 -> ds_pending s1 = 0 ->
    RQ (deflate_trailer s1) (deflate_trailer s2).
  Proof.
    intros HS1 D I1 I2 Hp. rewrite !deflate_trailer_eq. cbv zeta.
    pose proof (trailer_rel0 s1 s2 HS1 D I1 I2 Hp) as (Df & J1 & J2). cbv zeta in Df, J1, J2.
    set (f1 := flush_pending (trailer_st s1)) in *. set (f2 := flush_pending (trailer_st s2)) in *. clearbody f1 f2.
    pose proof (DREL_clean _ _ Df) as EC. eqc_fields EC.
    destruct (0 <? ds_wrap f1).
    - pose proof (DREL_set_wrap _ _ (- ds_wrap f1) Df) as Dw. pose proof (DREL_clean _ _ Dw) as ECw.
      split; [cbn [snd]; dsr; eqc_fields EC; reflexivity|]. cbn [fst]. split; [apply DREL_DQ; exact Dw|]. split; apply INVG_set_wrap; assumption.
    - split; [cbn [snd]; eqc_fields EC; reflexivity|]. cbn [fst]. split; [apply DREL_DQ; exact Df|]. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition core_fin (s : deflate_state) (flush : Z) : deflate_state * Z :=
    let '(s, r) := deflate_blocks s flush in
    match r with Some rc => (s, rc) | None =>
    if negb (Z.eqb flush Z_FINISH) then (s, Z_OK)
    else if Z.leb (ds_wrap s) 0 then (s, Z_STREAM_END)
    else deflate_trailer s
    end.

  Lemma fin_rel s1 s2 flush :
    ST1 s1 -> ST2 s2 -> DREL s1 s2 -> INVG s1 -> INVG s2 -> ds_pending s1 = 0 -> (flush = 0 \/ flush = 4 \/ flush = 5) ->
    (ds_status s1 = FINISH_STATE -> cs_avail_in (ds_strm s1) = 0) ->
    RQ (core_fin s1 flush) (core_fin s2 flush).
  Proof.
    intros HS1 HS2 D I1 I2 Hp Hfl Hfin. pose proof (DREL_clean _ _ D) as EC.
    assert (Hp2 : ds_pending s2 = 0) by (rewrite <- (clean_eq_fieldT ds_pending _ _ EC ltac:(reflexivity)); exact Hp).
    assert (Hfin2 : ds_status s2 = FINISH_STATE -> cs_avail_in (ds_strm s2) = 0).
    { rewrite <- (clean_eq_fieldT ds_status _ _ EC ltac:(reflexivity)), <- (clean_eq_fieldT ds_strm _ _ EC ltac:(reflexivity)). exact Hfin. }
    pose proof (blocks_rel s1 s2 flush HS1 HS2 D I1 I2 Hp Hfl Hfin) as (Eb & Db & Jb1 & Jb2).
    destruct (blocks_stage _ _ _ _ Hst Hhf Hrl Hfa Hsl c0 s01 HC0 Hs01 D01 s1 flush HS1 Hp ltac:(lia) Hfin) as (_ & HSr1 & Hr1).
    destruct (blocks_stage _ _ _ _ Hst Hhf Hrl Hfa Hsl c0 s02 HC0 Hs02 D02 s2 flush HS2 Hp2 ltac:(lia) Hfin2) as (_ & HSr2 & Hr2).
    unfold core_fin.
    destruct (deflate_blocks s1 flush) as [b1 r1]. destruct (deflate_blocks s2 flush) as [b2 r2]. cbn [fst snd] in Eb, Db, Jb1, Jb2, HSr1, Hr1, HSr2, Hr2. subst r2.
    destruct r1 as [rc|]; [apply RQ_I; assumption|].
    destruct (Hr1 eq_refl) as [Hpb1 _].
    pose proof (DQ_clean _ _ Db) as ECb. eqc_fields ECb.
    destruct (negb (flush =? Z_FINISH)); [apply RQ_I; assumption|].
    destruct (ds_wrap b1 <=? 0); [apply RQ_I; assumption|].
    pose proof HSr1 as [[[_ Xb1] _] _].
    apply trailer_rel; [exact HSr1|apply DQ_DREL; [exact Db|exact Hpb1|exact (dx_pout0 _ Xb1 Hpb1)]|exact Jb1|exact Jb2|exact Hpb1].
  Qed.

  (* [comment removed for export] *)
  Definition core_tail (s : deflate_state) (flush : Z) : deflate_state * Z :=
    if Z.eqb (ds_status s) FINISH_STATE && negb (Z.eqb (cs_avail_in (ds_strm s)) 0)
    then err_return s Z_BUF_ERROR
    else
    let s := if Z.eqb (ds_status s) INIT_STATE && Z.eqb (ds_wrap s) 0 then set_status s BUSY_STATE else s in
    let '(s, r) := if Z.eqb (ds_status s) INIT_STATE then deflate_zlib_header s else (s, None) in
    match r with Some rc => (s, rc) | None =>
    let '(s, r) := if Z.eqb (ds_status s) GZIP_STATE then deflate_gzip_header s else (s, None) in
    match r with Some rc => (s, rc) | None =>
    core_fin s flush
    end end.

  Lemma core_tail_rel s1 s2 flush :
    ST1 s1 -> ST2 s2 -> DREL s1 s2 -> INVG s1 -> INVG s2 -> ds_pending s1 = 0 -> (flush = 0 \/ flush = 4 \/ flush = 5) ->
    RQ (core_tail s1 flush) (core_tail s2 flush).
  Proof.
    intros HS1 HS2 D I1 I2 Hp Hfl. pose proof HS1 as [H1 K1]. pose proof HS2 as [H2 K2]. pose proof (DREL_clean _ _ D) as EC.
    assert (Hp2 : ds_pending s2 = 0) by (rewrite <- (clean_eq_fieldT ds_pending _ _ EC ltac:(reflexivity)); exact Hp).
    unfold core_tail. eqc_fields EC.
    destruct ((ds_status s1 =? FINISH_STATE) && negb (cs_avail_in (ds_strm s1) =? 0)) eqn:Efa; [apply RQ_err; [apply DREL_DQ; exact D|exact I1|exact I2]|].
    assert (Hnf : ~ (ds_status s1 = FINISH_STATE /\ cs_avail_in (ds_strm s1) <> 0)).
    { intros [A1 A2]. rewrite A1 in Efa. cbn in Efa. destruct (Z.eqb_spec (cs_avail_in (ds_strm s1)) 0); [exact (A2 ltac:(assumption))|discriminate Efa]. }
    cbv zeta.
    set (v1 := if (ds_status s1 =? INIT_STATE) && (ds_wrap s1 =? 0) then set_status s1 BUSY_STATE else s1).
    set (v2 := if (ds_status s1 =? INIT_STATE) && (ds_wrap s1 =? 0) then set_status s2 BUSY_STATE else s2).
    assert (HV : ST1 v1 /\ ST2 v2 /\ DREL v1 v2 /\ INVG v1 /\ INVG v2 /\ ds_pending v1 = 0
                 /\ cs_avail_in (ds_strm v1) = cs_avail_in (ds_strm s1) /\ (ds_status v1 = FINISH_STATE -> ds_status s1 = FINISH_STATE)).
    { subst v1 v2. destruct ((ds_status s1 =? INIT_STATE) && (ds_wrap s1 =? 0)) eqn:E.
      - apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
        assert (E1' : ds_status s2 = INIT_STATE) by (rewrite <- (clean_eq_fieldT ds_status _ _ EC ltac:(reflexivity)); exact E1).
        assert (E2' : ds_wrap s2 = 0) by (rewrite <- (clean_eq_fieldT ds_wrap _ _ EC ltac:(reflexivity)); exact E2).
        destruct (DC_set_status c0 s1 BUSY_STATE H1 ltac:(unfold BUSY_STATE; lia) ltac:(intros; exfalso; lia) ltac:(unfold BUSY_STATE, FINISH_STATE; intros; lia)) as (G1 & KG1 & _).
        destruct (DC_set_status c0 s2 BUSY_STATE H2 ltac:(unfold BUSY_STATE; lia) ltac:(intros; exfalso; lia) ltac:(unfold BUSY_STATE, FINISH_STATE; intros; lia)) as (G2 & KG2 & _).
        split; [split; [exact G1|rewrite KG1; exact K1]|]. split; [split; [exact G2|rewrite KG2; exact K2]|].
        split; [apply DREL_set_status; exact D|]. split; [apply INVG_set_status; exact I1|]. split; [apply INVG_set_status; exact I2|].
        dsr. split; [exact Hp|]. split; [reflexivity|]. unfold BUSY_STATE, FINISH_STATE. intros; lia.
      - split; [exact HS1|]. split; [exact HS2|]. split; [exact D|]. split; [exact I1|]. split; [exact I2|]. split; [exact Hp|]. split; [reflexivity|]. intros X; exact X. }
    clearbody v1 v2. destruct HV as (HSv1 & HSv2 & Dv & Iv1 & Iv2 & Hpv & Aiv & Finv).
    pose proof (DREL_clean _ _ Dv) as ECv. eqc_fields ECv.
    assert (Hpv2 : ds_pending v2 = 0) by (rewrite <- (clean_eq_fieldT ds_pending _ _ ECv ltac:(reflexivity)); exact Hpv).
    (* [comment removed for export] *)
    destruct (Z.eqb_spec (ds_status v1) INIT_STATE) as [Ei|Ei].
    - assert (Ei2 : ds_status v2 = INIT_STATE) by (rewrite <- (clean_eq_fieldT ds_status _ _ ECv ltac:(reflexivity)); exact Ei).
      rewrite !deflate_zlib_header_eq. cbv zeta.
      pose proof (zhdr_rel v1 v2 HSv1 Dv Iv1 Iv2 Hpv Ei) as (Dz & Kz1 & Kz2). cbv zeta in Dz, Kz1, Kz2.
      destruct (hdr_zlib c0 s01 HC0 Hs01 D01 v1 HSv1 Hpv Ei) as (_ & HSz1 & Stz1 & Horz1 & Aiz1 & _).
      destruct (hdr_zlib c0 s02 HC0 Hs02 D02 v2 HSv2 Hpv2 Ei2) as (_ & HSz2 & _).
      set (z1 := flush_pending (zhdr_st v1)) in *. set (z2 := flush_pending (zhdr_st v2)) in *. clearbody z1 z2.
      pose proof (DREL_clean _ _ Dz) as ECz. eqc_fields ECz.
      destruct (Z.eqb_spec (ds_pending z1) 0) as [Pz|Pz]; cbn [negb]; eqc_fields ECz.
      + rewrite Stz1. change (BUSY_STATE =? GZIP_STATE) with false. cbn [negb].
        apply fin_rel; [exact HSz1|exact HSz2|exact Dz|exact Kz1|exact Kz2|exact Pz|exact Hfl|].
        rewrite Stz1. unfold BUSY_STATE, FINISH_STATE. intros; lia.
      + apply RQ_I; [apply DREL_DQ, DREL_set_last_flush; exact Dz|apply INVG_set_last_flush; exact Kz1|apply INVG_set_last_flush; exact Kz2].
    - cbn [negb]. eqc_fields ECv.
      (* [comment removed for export] *)
      destruct (Z.eqb_spec (ds_status v1) GZIP_STATE) as [Eg|Eg].
      + assert (Eg2 : ds_status v2 = GZIP_STATE) by (rewrite <- (clean_eq_fieldT ds_status _ _ ECv ltac:(reflexivity)); exact Eg).
        rewrite !deflate_gzip_header_eq. cbv zeta.
        pose proof (gzhdr_rel v1 v2 HSv1 Dv Iv1 Iv2 Hpv Eg) as (Dz & Kz1 & Kz2). cbv zeta in Dz, Kz1, Kz2.
        destruct (hdr_gzip c0 s01 HC0 Hs01 D01 v1 HSv1 Hpv Eg) as (_ & HSz1 & Stz1 & Horz1 & Aiz1 & _).
        destruct (hdr_gzip c0 s02 HC0 Hs02 D02 v2 HSv2 Hpv2 Eg2) as (_ & HSz2 & _).
        set (z1 := flush_pending (gzhdr_st v1)) in *. set (z2 := flush_pending (gzhdr_st v2)) in *. clearbody z1 z2.
        pose proof (DREL_clean _ _ Dz) as ECz. eqc_fields ECz.
        destruct (Z.eqb_spec (ds_pending z1) 0) as [Pz|Pz]; cbn [negb]; eqc_fields ECz.
        * apply fin_rel; [exact HSz1|exact HSz2|exact Dz|exact Kz1|exact Kz2|exact Pz|exact Hfl|].
          rewrite Stz1. unfold BUSY_STATE, FINISH_STATE. intros; lia.
        * apply RQ_I; [apply DREL_DQ, DREL_set_last_flush; exact Dz|apply INVG_set_last_flush; exact Kz1|apply INVG_set_last_flush; exact Kz2].
      + cbn [negb]. apply fin_rel; [exact HSv1|exact HSv2|exact Dv|exact Iv1|exact Iv2|exact Hpv|exact Hfl|].
        intros Ef. rewrite Aiv. destruct (Z.eq_dec (cs_avail_in (ds_strm s1)) 0) as [A|A]; [exact A|]. exfalso. apply Hnf. split; [exact (Finv Ef)|exact A].
  Qed.

  (* [comment removed for export] *)
  Lemma core_rel flush :
    ST1 s01 -> ST2 s02 -> DQ s01 s02 -> INVG s01 -> INVG s02 -> (flush = 0 \/ flush = 4 \/ flush = 5) ->
    RQ (deflate_core s01 flush) (deflate_core s02 flush).
  Proof.
    intros HS1 HS2 D I1 I2 Hfl. pose proof HS1 as [H1 K1]. pose proof HS2 as [H2 K2].
    pose proof (DQ_clean _ _ D) as EC.
    unfold deflate_core. rewrite <- (clean_eq_fieldT deflateStateCheck _ _ EC ltac:(intros; reflexivity)). eqc_goal EC.
    destruct (deflateStateCheck s01 || (Z_BLOCK <? flush) || (flush <? 0)) eqn:Echk; [apply RQ_I; assumption|].
    destruct ((ds_status s01 =? FINISH_STATE) && negb (flush =? Z_FINISH)); [apply RQ_err; assumption|].
    destruct (Z.eqb_spec (cs_avail_out (ds_strm s01)) 0) as [Hao|Hao]; [apply RQ_err; assumption|].
    cbv zeta.
    pose proof (ST_set_last_flush c0 s01 s01 flush HS1 ltac:(lia)) as HSu1.
    pose proof (ST_set_last_flush c0 s02 s02 flush HS2 ltac:(lia)) as HSu2.
    pose proof (DQ_set_last_flush _ _ flush D) as Du. pose proof (INVG_set_last_flush s01 flush I1) as Iu1. pose proof (INVG_set_last_flush s02 flush I2) as Iu2.
    set (u1 := set_last_flush s01 flush) in *. set (u2 := set_last_flush s02 flush) in *. clearbody u1 u2.
    pose proof HSu1 as [Hu1 Ku1]. pose proof Hu1 as [[DWu1 Xu1] Vu1].
    pose proof (DQ_clean _ _ Du) as ECu. eqc_fields ECu.
    destruct (Z.eqb_spec (ds_pending u1) 0) as [Ep|Ep]; cbn [negb].
    - (* [comment removed for export] *)
      destruct ((cs_avail_in (ds_strm u1) =? 0) && (RANK flush <=? RANK (ds_last_flush s01)) && negb (flush =? Z_FINISH)).
      + unfold err_return. cbn [negb]. apply RQ_err; assumption.
      + apply core_tail_rel; [exact HSu1|exact HSu2|apply DQ_DREL; [exact Du|exact Ep|exact (dx_pout0 _ Xu1 Ep)]|exact Iu1|exact Iu2|exact Ep|exact Hfl].
    - (* [comment removed for export] *)
      destruct Du as (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH).
      pose proof (df_pend _ DWu1) as (PO0 & _ & PLE). rewrite (ig_lbs _ Iu1) in PLE.
      pose proof (bi_flush_noop u1 (dx_biv _ Xu1)) as NB.
      pose proof (flush_pending_DREL W C B bnd ms pm u1 u2 R Iu1 Iu2 HW Hb HS HH PO0 HP (or_intror NB) ltac:(rewrite NB; lia)) as (Df & Jf1 & Jf2 & _).
      destruct (ST_flush_pending c0 s01 HC0 u1 HSu1) as (HSf1 & _ & Hor1 & _).
      destruct (ST_flush_pending c0 s02 HC0 u2 HSu2) as (HSf2 & _).
      set (f1 := flush_pending u1) in *. set (f2 := flush_pending u2) in *. clearbody f1 f2.
      pose proof (DREL_clean _ _ Df) as ECf. eqc_fields ECf.
      destruct (Z.eqb_spec (cs_avail_out (ds_strm f1)) 0) as [Ea|Ea]; cbn [negb].
      + apply RQ_I; [apply DREL_DQ, DREL_set_last_flush; exact Df|apply INVG_set_last_flush; exact Jf1|apply INVG_set_last_flush; exact Jf2].
      + assert (Hpf : ds_pending f1 = 0) by (destruct Hor1 as [X|X]; [exact X|exfalso; exact (Ea X)]).
        apply core_tail_rel; [exact HSf1|exact HSf2|exact Df|exact Jf1|exact Jf2|exact Hpf|exact Hfl].
  Qed.
End Core.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cstrm_of_call_avail_in zc : cs_avail_in (cstrm_of_call zc) = zlength (zc_input zc).
Proof. reflexivity. Qed.
Lemma cstrm_of_call_avail_out zc : cs_avail_out (cstrm_of_call zc) = zc_avail_out zc.
Proof. reflexivity. Qed.

Theorem deflate_m_rel : DEFLATE_M_REL.
Proof.
  intros s1 s2 zc flush (D & I1 & I2 & R1 & R2) Hzc Hfl.
  assert (Hfl' : flush = 0 \/ flush = 4 \/ flush = 5) by (unfold Z_NO_FLUSH, Z_FINISH, Z_BLOCK in Hfl; exact Hfl).
  pose proof (deflate_m_DD _ _ _ _ Hst Hhf Hrl Hfa Hsl s1 zc flush R1 Hzc ltac:(clear - Hfl'; lia)) as R1'.
  pose proof (deflate_m_DD _ _ _ _ Hst Hhf Hrl Hfa Hsl s2 zc flush R2 Hzc ltac:(clear - Hfl'; lia)) as R2'.
  revert R1' R2'. unfold deflate_m.
  set (c0 := cstrm_of_call zc).
  pose proof (C0OK'_of_call zc Hzc) as HC0. fold c0 in HC0.
  pose proof R1 as DD1. pose proof R2 as DD2.
  assert (G1 : DC c0 (set_strm s1 c0)) by (split; [apply DD_set_strm; exact DD1 | subst c0; apply SV_entry; exact Hzc]).
  assert (G2 : DC c0 (set_strm s2 c0)) by (split; [apply DD_set_strm; exact DD2 | subst c0; apply SV_entry; exact Hzc]).
  assert (HS1 : ST c0 (set_strm s1 c0) (set_strm s1 c0)) by (split; [exact G1|reflexivity]).
  assert (HS2 : ST c0 (set_strm s2 c0) (set_strm s2 c0)) by (split; [exact G2|reflexivity]).
  pose proof (DQ_set_strm s1 s2 c0 D) as Du.
  assert (Ain : 0 <= cs_avail_in c0) by (subst c0; rewrite cstrm_of_call_avail_in; unfold zlength; lia).
  assert (Aout : 0 <= cs_avail_out c0) by (subst c0; rewrite cstrm_of_call_avail_out; destruct Hzc as (_ & Hao & _); lia).
  pose proof (INVG_set_strm s1 c0 Ain Aout I1) as Iu1. pose proof (INVG_set_strm s2 c0 Ain Aout I2) as Iu2.
  pose proof (core_rel c0 (set_strm s1 c0) (set_strm s2 c0) HC0 eq_refl eq_refl (proj1 (proj1 G1)) (proj1 (proj1 G2)) flush HS1 HS2 Du Iu1 Iu2 Hfl') as (E & Dq & J1 & J2).
  destruct (deflate_core (set_strm s1 c0) flush) as [t1 rc1]. destruct (deflate_core (set_strm s2 c0) flush) as [t2 rc2].
  cbn [fst snd] in E, Dq, J1, J2 |- *. subst rc2. intros R1' R2'.
  split; [rewrite (clean_eq_fieldT ds_strm _ _ (DQ_clean _ _ Dq) ltac:(reflexivity)); reflexivity|].
  split; [exact Dq|]. split; [exact J1|]. split; [exact J2|]. split; [exact R1'|exact R2'].
Qed.
