(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflStored5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflStored5.RefDeflStored2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflStored7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflStored7.RefDeflStored6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeL2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeL2.RefDeflSafeL0.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintBits.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateTaintBits.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateTaintBits.DeflateTaintLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintTrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma flush_pending_rel0 W C B bnd ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 ->
  0 <= cs_avail_out (ds_strm s1) -> 0 <= ds_pending s1 -> ds_pending (bi_flush s1) < 2 ^ 32 ->
  ds_pending_out s1 + ds_pending (bi_flush s1) <= arr_len (ds_pending_buf s1) ->
  (cs_avail_out (ds_strm s1) = 0 \/ (ds_pending_out s1 = 0 /\ forall i, 0 <= i < ds_pending s1 -> B i)) ->
  REL W C (Bx B (ds_pending s1) (ds_pending (bi_flush s1))) bnd ms pm (flush_pending s1) (flush_pending s2).
Proof.
  intros R A0 P0 P32 HL PB.
  pose proof (bi_flush_rel _ _ _ _ _ _ _ _ R) as R'.
  pose proof (bi_flush_pending_le s1) as PL1.
  pose proof (k_bi_flush ds_strm true true keeps_strm eq_refl s1) as Est.
  pose proof (k_bi_flush ds_pending_out true true keeps_pending_out eq_refl s1) as Epo.
  pose proof (bi_flush_len s1) as Ebl.
  unfold flush_pending, tr_flush_bits.
  set (s1' := bi_flush s1) in *. clearbody s1'. set (s2' := bi_flush s2) in *. clearbody s2'.
  rel_fields R'. rewrite Est, Epo in *.
  rewrite (wrap32_id (ds_pending s1')) by lia.
  set (len := if cs_avail_out (ds_strm s1) <? ds_pending s1' then cs_avail_out (ds_strm s1) else ds_pending s1').
  assert (Hlen : len = Z.min (cs_avail_out (ds_strm s1)) (ds_pending s1')) by (subst len; destruct (Z.ltb_spec (cs_avail_out (ds_strm s1)) (ds_pending s1')); lia).
  clearbody len.
  destruct (Z.eqb_spec len 0) as [L0|L0]; [exact R'|].
  assert (ES : arr_slice (ds_pending_buf s2') (ds_pending_out s1) len = arr_slice (ds_pending_buf s1') (ds_pending_out s1) len).
  { destruct PB as [A00|[PO HB]]; [exfalso; lia|]. rewrite PO.
    symmetry. apply (aeq_slice _ _ _ _ _ (r_pb _ _ _ _ _ _ _ _ R')); try lia.
    intros k Hk. unfold Bx. destruct (Z_lt_le_dec (0 + k) (ds_pending s1)); [left; apply HB; lia|right; lia]. }
  rewrite ES. unfold cs_emit. dsr. rel_fields R'.
  destruct (Z.eqb_spec (ds_pending s1' - len) 0); dsr; rel_fields R'.
  - match goal with |- REL _ _ _ _ _ _ (set_pending_out (set_pending (set_strm (set_pending_out s1' ?a) ?st) ?p) ?po) _ =>
      pose proof (rel_upd3 _ _ _ _ _ _ _ _ st p po (rel_set_pending_out _ _ _ _ _ _ _ _ a R')) as RR end.
    exact RR.
  - match goal with |- REL _ _ _ _ _ _ (set_pending (set_strm (set_pending_out s1' ?a) ?st) ?p) _ =>
      pose proof (rel_set_pending _ _ _ _ _ _ _ _ p (rel_set_strm _ _ _ _ _ _ _ _ st (rel_set_pending_out _ _ _ _ _ _ _ _ a R'))) as RR end.
    exact RR.
Qed.

Lemma read_buf_window_rel0 W C B bnd ms pm s1 s2 off n :
  REL W C B bnd ms pm s1 s2 -> 0 <= cs_avail_in (ds_strm s1) -> 0 <= n ->
  let r1 := read_buf s1 (RB_window off) n in let r2 := read_buf s2 (RB_window off) n in
  snd r1 = snd r2 /\ ds_strm (fst r1) = ds_strm (fst r2)
  /\ REL (fun i => W i \/ off <= i < off + snd r1) C B bnd ms pm (fst r1) (fst r2).
Proof.
  intros R AIN Hn. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC.
  unfold read_buf, cs_emit. cbv zeta. dsr. rel_fields R.
  set (len := if n <? cs_avail_in (ds_strm s1) then n else cs_avail_in (ds_strm s1)).
  destruct (Z.eqb_spec len 0) as [L0|L0].
  - cbn [fst snd]. split; [reflexivity|]. split; [rel_fields R; reflexivity|].
    eapply rel_weaken; [exact R| intros i [Hi|Hi]; [exact Hi|lia] | auto | lia].
  - cbn [fst snd]. dsr. set (bytes := arr_slice _ _ len).
    assert (Hlen : 0 <= len <= n) by (unfold len; destruct (Z.ltb_spec n (cs_avail_in (ds_strm s1))); lia).
    split; [reflexivity|]. split; [reflexivity|].
    assert (BL : zlength bytes = len) by (unfold bytes; rewrite arr_slice_length; lia).
    set (st' := cset_total_in _ _). clearbody st'.
    apply rel_set_strm. eapply rel_set_window; [exact R|].
    eapply aeq_mono; [apply aeq_upd; exact (r_win _ _ _ _ _ _ _ _ R)|]. intros i [Hi|Hi]; [left; exact Hi|right; rewrite BL; exact Hi].
Qed.

Lemma read_buf_next_out_shape s s' n : ds_strm s' = ds_strm s -> ds_wrap s' = ds_wrap s ->
  exists st k, read_buf s RB_next_out n = (set_strm s st, k) /\ read_buf s' RB_next_out n = (set_strm s' st, k).
Proof.
  intros E1 E2. unfold read_buf. cbv zeta. rewrite E1, E2.
  destruct (_ =? 0).
  - exists (ds_strm s), 0. split; [destruct s; reflexivity|]. rewrite <- E1. destruct s'; reflexivity.
  - eexists _, _. split; reflexivity.
Qed.


Section CleanScalars.
  Variable W : Z -> Prop.
Variable C : Z -> Prop.
Variable B : Z -> Prop.
Variable bnd : Z.
Variable ms : bool.
Variable pm : bool.
Variable s1 : deflate_state.
Variable s2 : deflate_state.
  Hypothesis R : REL W C B bnd ms pm s1 s2.
  Let EC := r_clean _ _ _ _ _ _ _ _ R.
  Lemma rel_sb_hdr : sb_hdr s2 = sb_hdr s1. Proof. symmetry. apply (clean_eq_fieldT sb_hdr _ _ EC). reflexivity. Qed.
  Lemma rel_sb_left : sb_left s2 = sb_left s1. Proof. symmetry. apply (clean_eq_fieldT sb_left _ _ EC). reflexivity. Qed.
  Lemma rel_sb_len1 : sb_len1 s2 = sb_len1 s1. Proof. symmetry. apply (clean_eq_fieldT sb_len1 _ _ EC). reflexivity. Qed.
  Lemma rel_sb_len : sb_len s2 = sb_len s1. Proof. symmetry. apply (clean_eq_fieldT sb_len _ _ EC). reflexivity. Qed.
  Lemma rel_sb_lastv f : sb_lastv s2 f = sb_lastv s1 f. Proof. symmetry. apply (clean_eq_fieldT (fun s => sb_lastv s f) _ _ EC). reflexivity. Qed.
  Lemma rel_sb_brk f mb : sb_brk s2 f mb = sb_brk s1 f mb. Proof. symmetry. apply (clean_eq_fieldT (fun s => sb_brk s f mb) _ _ EC). reflexivity. Qed.
  Lemma rel_sb_broke f mb : sb_broke s2 f mb = sb_broke s1 f mb. Proof. symmetry. apply (clean_eq_fieldT (fun s => sb_broke s f mb) _ _ EC). reflexivity. Qed.
  Lemma rel_t_have : t_have s2 = t_have s1. Proof. symmetry. apply (clean_eq_fieldT t_have _ _ EC). reflexivity. Qed.
  Lemma rel_t_mb : t_mb s2 = t_mb s1. Proof. symmetry. apply (clean_eq_fieldT t_mb _ _ EC). reflexivity. Qed.
  Lemma rel_w_size : ds_w_size s2 = ds_w_size s1. Proof. symmetry. apply (clean_eq_fieldT ds_w_size _ _ EC). reflexivity. Qed.
  Lemma rel_window_size : ds_window_size s2 = ds_window_size s1. Proof. symmetry. apply (clean_eq_fieldT ds_window_size _ _ EC). reflexivity. Qed.
  Lemma rel_high_water : ds_high_water s2 = ds_high_water s1. Proof. symmetry. apply (clean_eq_fieldT ds_high_water _ _ EC). reflexivity. Qed.
  Lemma rel_matches : ds_matches s2 = ds_matches s1. Proof. symmetry. apply (clean_eq_fieldT ds_matches _ _ EC). reflexivity. Qed.
  Lemma rel_pending_buf_size : ds_pending_buf_size s2 = ds_pending_buf_size s1. Proof. symmetry. apply (clean_eq_fieldT ds_pending_buf_size _ _ EC). reflexivity. Qed.
  Lemma rel_WHI : WHI s2 = WHI s1. Proof. symmetry. apply (clean_eq_fieldT WHI _ _ EC). reflexivity. Qed.
End CleanScalars.

Lemma WHI_eq3 a b : ds_high_water b = ds_high_water a -> ds_strstart b = ds_strstart a -> ds_lookahead b = ds_lookahead a -> WHI b = WHI a.
Proof. intros E1 E2 E3. unfold WHI. rewrite E1, E2, E3. reflexivity. Qed.

Lemma dmode0_level s : dmode s = 0 -> ds_level s = 0.
Proof.
  unfold dmode. destruct (Z.eqb_spec (ds_level s) 0); [intros _; assumption|].
  destruct (_ =? _); [intros X; discriminate X|]. destruct (_ =? _); [intros X; discriminate X|]. destruct (_ <=? _); intros X; discriminate X.
Qed.

Lemma WHI_SF_LZS a b : SF b = SF a -> LZS b = LZS a -> WHI b = WHI a.
Proof.
  intros E1 E2. pose proof (SF_fields _ _ E1) as (_ & (_ & _ & _ & _ & _ & _ & Elook & _) & _).
  pose proof (LZS_fields _ _ E2) as (_ & Estr & _ & _ & Ehw). unfold WHI. rewrite Elook, Estr, Ehw. reflexivity.
Qed.


Section StoredRel.
  Variable c0 : cstrm.
Variable s01 : deflate_state.
Variable s02 : deflate_state.
Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Variable C : Z -> Prop.
Variable bnd : Z.
Variable ms : bool.
Variable pm : bool.

  Definition HWc (W : Z -> Prop) (t : deflate_state) : Prop := forall i, i < WHI t -> W i.

  Local Ltac si_facts HS D X V Sw Sl Epbs Hl0 Hbs Hsn Hmt Hstr Ewsz Hwr Hpo Hbv Hbb Hao Hai Hins Hinsw Hhw :=
    pose proof (SI_facts c0 _ HC0 _ HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).

  Lemma tsb_none_facts t lastv : 0 <= ds_bi_valid t <= 16 -> 0 <= ds_bi_buf t < 2 ^ 16 ->
    ds_pending (tr_stored_block t None 0 lastv) = tsb_hP t + 1 + 1 + 1 + 1 + 0
    /\ ds_pending_out (tr_stored_block t None 0 lastv) = ds_pending_out t
    /\ ds_strm (tr_stored_block t None 0 lastv) = ds_strm t
    /\ arr_len (ds_pending_buf (tr_stored_block t None 0 lastv)) = arr_len (ds_pending_buf t).
  Proof.
    intros Hbv Hbb. rewrite (tr_stored_block_eq t None 0 lastv Hbv Hbb). unfold tsb_tail. cbn [negb Z.eqb].
    rewrite upd4_pending, upd4_pending_buf. split; [reflexivity|].
    split; [unfold upd4; reflexivity|]. split; [unfold upd4; reflexivity|].
    unfold tsb_lenA. rewrite !arr_len_set. apply tsb_hA_len.
  Qed.

  Lemma sb_patch_facts a len :
    ds_pending (sb_patch a len) = ds_pending a /\ ds_pending_out (sb_patch a len) = ds_pending_out a
    /\ ds_strm (sb_patch a len) = ds_strm a /\ arr_len (ds_pending_buf (sb_patch a len)) = arr_len (ds_pending_buf a).
  Proof.
    unfold sb_patch. cbv zeta. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    cbn [ds_pending_buf set_pending_buf]. rewrite !arr_len_set. reflexivity.
  Qed.

  Lemma sb_patch_rel W B a1 a2 len :
    REL W C B bnd ms pm a1 a2 -> REL W C B bnd ms pm (sb_patch a1 len) (sb_patch a2 len).
  Proof.
    intros R1. unfold sb_patch. cbv zeta. rewrite (rel_pending _ _ _ _ _ _ _ _ R1).
    eapply rel_set_pending_buf; [exact R1|]. repeat apply aeq_set_keep. exact (r_pb _ _ _ _ _ _ _ _ R1).
  Qed.

  Lemma emit1_rel W B t1 t2 :
    REL W C B bnd ms pm t1 t2 -> SI c0 s01 t1 -> sb_hdr t1 <= cs_avail_out (ds_strm t1) ->
    exists B', REL W C B' bnd ms pm (st_emit1 t1 flush) (st_emit1 t2 flush).
  Proof.
    intros R HS Hroom.
    si_facts HS D X V Sw Sl Epbs Hl0 Hbs Hsn Hmt Hstr Ewsz Hwr Hpo Hbv Hbb Hao Hai Hins Hinsw Hhw.
    pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp). pose proof (df_bl _ D) as Hbl.
    unfold st_emit1. rewrite (rel_sb_lastv _ _ _ _ _ _ _ _ R flush), (rel_sb_len _ _ _ _ _ _ _ _ R).
    set (lastv := sb_lastv t1 flush). set (len := sb_len t1). clearbody lastv len.
    pose proof (tr_stored_block_rel0 W C bnd ms pm B t1 t2 None 0 lastv R ltac:(lia) ltac:(intros _; reflexivity)
                  ltac:(intros off HH; discriminate HH)) as R1.
    pose proof (tsb_none_facts t1 lastv ltac:(clear - Hbv; lia) Hbb) as (Fp & Fpo & Fst & Fbl).
    pose proof (tsb_hP_range t1) as HP. rewrite Hp in HP.
    set (a1 := tr_stored_block t1 None 0 lastv) in *. set (a2 := tr_stored_block t2 None 0 lastv) in *.
    clearbody a1 a2. rewrite Hp in R1.
    pose proof (sb_patch_rel W _ a1 a2 len R1) as R2.
    pose proof (sb_patch_facts a1 len) as (Gp & Gpo & Gst & Gbl).
    set (b1 := sb_patch a1 len) in *. set (b2 := sb_patch a2 len) in *. clearbody b1 b2.
    exists (Bx (Bx B 0 (ds_pending a1)) (ds_pending b1) (ds_pending (bi_flush b1))).
    pose proof (bi_flush_pending_le b1) as BFL.
    apply (flush_pending_rel0 _ _ _ _ _ _ _ _ R2).
    - rewrite Gst, Fst. exact (proj1 Hao).
    - rewrite Gp, Fp. clear - HP. lia.
    - rewrite Gp, Fp in BFL. clear - HP BFL. lia.
    - rewrite Gpo, Fpo, Hpo, Gbl, Fbl, Hbl. rewrite Gp, Fp in BFL. clear - HP Sl BFL. lia.
    - right. split; [rewrite Gpo, Fpo; exact Hpo|]. intros i Hi. unfold Bx. right. rewrite Gp in Hi. exact Hi.
  Qed.

  Lemma lcopy_rel W B t1 t2 l :
    REL W C B bnd ms pm t1 t2 -> HWc W t1 ->
    0 <= l -> 0 <= ds_block_start t1 -> ds_block_start t1 + l <= ds_strstart t1 ->
    ds_strstart t1 + ds_lookahead t1 <= arr_len (ds_window t1) -> 0 <= ds_lookahead t1 ->
    REL W C B bnd ms pm (st_lcopy t1 l) (st_lcopy t2 l).
  Proof.
    intros R HW Hl Hb0 Hbl Hwl Hlk. unfold st_lcopy.
    rewrite (rel_strm _ _ _ _ _ _ _ _ R), (rel_block_start _ _ _ _ _ _ _ _ R).
    assert (ES : arr_slice (ds_window t2) (ds_block_start t1) l = arr_slice (ds_window t1) (ds_block_start t1) l).
    { symmetry. apply (aeq_slice _ _ _ _ _ (r_win _ _ _ _ _ _ _ _ R)); [exact Hb0 | exact Hl | lia |].
      intros k Hk. apply HW. unfold WHI. lia. }
    rewrite ES. apply rel_set_block_start. apply rel_set_strm. exact R.
  Qed.

  Lemma rdo_rel W B t1 t2 n :
    REL W C B bnd ms pm t1 t2 -> REL W C B bnd ms pm (st_rdo t1 n) (st_rdo t2 n).
  Proof.
    intros R. unfold st_rdo. destruct (negb (n =? 0)); [|exact R].
    destruct (read_buf_next_out_shape t1 t2 n (rel_strm _ _ _ _ _ _ _ _ R) (rel_wrap _ _ _ _ _ _ _ _ R)) as (st & k & E1 & E2).
    rewrite E1, E2. dsr. apply rel_set_strm, rel_set_strm. exact R.
  Qed.

  Lemma trip_rel W B t1 t2 mb :
    REL W C B bnd ms pm t1 t2 -> HWc W t1 -> SI c0 s01 t1 -> sb_broke t1 flush mb = false ->
    (exists B', REL W C B' bnd ms pm (st_trip t1 flush) (st_trip t2 flush))
    /\ WHI (st_trip t1 flush) = WHI t1 /\ SF (st_trip t1 flush) = SF t1.
  Proof.
    intros R HW HS Hb.
    si_facts HS D X V Sw Sl Epbs Hl0 Hbs Hsn Hmt Hstr Ewsz Hwr Hpo Hbv Hbb Hao Hai Hins Hinsw Hhw.
    pose proof Hb as Hb'. unfold sb_broke in Hb. apply Bool.orb_false_iff in Hb. destruct Hb as [Hb _]. apply Z.ltb_ge in Hb.
    pose proof (sb_len_range t1 ltac:(clear - Hai; lia) Hb) as (Rl1 & Rl2 & Rl3).
    pose proof (sb_len1_eq t1 ltac:(clear - Hai; lia)) as (_ & _ & Rl4).
    assert (Eleft : sb_left t1 = ds_strstart t1 - ds_block_start t1) by (unfold sb_left; apply wrap32_id; clear - Hbs Hstr Sw; lia).
    unfold st_trip. rewrite (rel_sb_left _ _ _ _ _ _ _ _ R), (rel_sb_len _ _ _ _ _ _ _ _ R).
    pose proof (emit_stage c0 s01 flush HC0 t1 HS Hb) as E. cbv zeta in E. destruct E as (HS3 & ESF3 & ELZ3 & Ebs3 & Eao3 & Eai3 & Eni3 & Ein3).
    pose proof (LZS_fields _ _ ELZ3) as (Ew3 & Estr3 & _).
    pose proof (WHI_SF_LZS _ _ ESF3 ELZ3) as EW3.
    destruct (emit1_rel W B t1 t2 R HS Hb) as [B3 R3].
    pose proof (SI_facts c0 _ HC0 _ HS3) as (D3 & _ & _ & _ & _ & _ & Hl03 & _).
    set (t3 := st_emit1 t1 flush) in *. set (t3' := st_emit1 t2 flush) in *. clearbody t3 t3'.
    unfold st_copy. rewrite Eleft in Rl4 |- *.
    destruct (Z.eqb_spec (ds_strstart t1 - ds_block_start t1) 0) as [L0|L0]; cbn [negb fst snd].
    - split; [exists B3; apply rdo_rel; exact R3|].
      destruct (Z.eq_dec (sb_len t1) 0) as [N0|N0].
      + rewrite N0. unfold st_rdo. cbn [negb Z.eqb]. exact (conj EW3 ESF3).
      + pose proof (rdo_stage c0 s01 HC0 t3 (sb_len t1) HS3 ltac:(rewrite Eai3; clear - Rl1 Rl3 Rl4 L0 N0; lia) ltac:(rewrite Eao3; exact Rl2)) as RS. cbv zeta in RS.
        destruct RS as (_ & ESF5 & ELZ5 & _). rewrite (WHI_SF_LZS _ _ ESF5 ELZ5), ESF5. exact (conj EW3 ESF3).
    - set (l := lc_len (ds_strstart t1 - ds_block_start t1) (sb_len t1)).
      assert (Hl : 0 <= l <= sb_len t1 /\ l <= ds_strstart t1 - ds_block_start t1 /\ sb_len t1 - l <= cs_avail_in (ds_strm t1)).
      { subst l. unfold lc_len. destruct (Z.ltb_spec (sb_len t1) (ds_strstart t1 - ds_block_start t1)) as [l0|l0]; clear - l0 Rl1 Rl3 Rl4 Hbs Hai; lia. }
      pose proof (lcopy_stage c0 s01 HC0 t3 l HS3 ltac:(clear - Hl; lia) ltac:(rewrite Ebs3, Estr3; clear - Hl; lia) ltac:(rewrite Eao3; clear - Hl Rl2; lia)) as CS. cbv zeta in CS.
      destruct CS as (HS4 & ESF4 & ELZ4 & _ & Eao4 & Eai4 & _).
      pose proof (lcopy_rel W B3 t3 t3' l R3 ltac:(unfold HWc; rewrite EW3; exact HW) ltac:(clear - Hl; lia) ltac:(rewrite Ebs3; clear - Hbs; lia)
                    ltac:(rewrite Ebs3, Estr3; clear - Hl; lia) ltac:(rewrite Estr3, Ew3, Hl03, (df_wl _ D); clear - Hstr; lia) ltac:(rewrite Hl03; lia)) as R4.
      pose proof (WHI_SF_LZS _ _ ESF4 ELZ4) as EW4.
      set (t4 := st_lcopy t3 l) in *. set (t4' := st_lcopy t3' l) in *. clearbody t4 t4'.
      split; [exists B3; apply rdo_rel; exact R4|].
      destruct (Z.eq_dec (sb_len t1 - l) 0) as [N0|N0].
      + rewrite N0. unfold st_rdo. cbn [negb Z.eqb]. rewrite EW4, ESF4. exact (conj EW3 ESF3).
      + pose proof (rdo_stage c0 s01 HC0 t4 (sb_len t1 - l) HS4 ltac:(rewrite Eai4, Eai3; clear - Hl N0; lia) ltac:(rewrite Eao4, Eao3; clear - Hl Rl2; lia)) as RS. cbv zeta in RS.
        destruct RS as (_ & ESF5 & ELZ5 & _). rewrite (WHI_SF_LZS _ _ ESF5 ELZ5), EW4, ESF5, ESF4. exact (conj EW3 ESF3).
  Qed.

  Lemma loop_rel fuel : forall W B t1 t2 mb,
    REL W C B bnd ms pm t1 t2 -> HWc W t1 -> SI c0 s01 t1 -> SI c0 s02 t2 ->
    let r1 := deflate_stored_loop fuel t1 flush mb in let r2 := deflate_stored_loop fuel t2 flush mb in
    snd r1 = snd r2 /\ (exists B', REL W C B' bnd ms pm (fst r1) (fst r2)) /\ HWc W (fst r1)
    /\ SI c0 s01 (fst r1) /\ SI c0 s02 (fst r2) /\ SF (fst r1) = SF t1.
  Proof.
    induction fuel as [|f IH]; intros W B t1 t2 mb R HW HS1 HS2.
    - cbn [deflate_stored_loop fst snd]. split; [reflexivity|]. split; [exists B; exact R|]. split; [exact HW|]. split; [exact HS1|]. split; [exact HS2|reflexivity].
    - cbv zeta. rewrite !sloop_S'. rewrite (rel_sb_broke _ _ _ _ _ _ _ _ R), (rel_sb_lastv _ _ _ _ _ _ _ _ R).
      destruct (sb_broke t1 flush mb) eqn:Hb.
      { cbn [fst snd]. split; [reflexivity|]. split; [exists B; exact R|]. split; [exact HW|]. split; [exact HS1|]. split; [exact HS2|reflexivity]. }
      pose proof (trip_rel W B t1 t2 mb R HW HS1 Hb) as [[B' R'] [EW ESF]].
      pose proof (trip_stage c0 s01 flush HC0 t1 mb HS1 Hb) as T1. cbv zeta in T1. destruct T1 as [HS1' _].
      pose proof (trip_stage c0 s02 flush HC0 t2 mb HS2 ltac:(rewrite (rel_sb_broke _ _ _ _ _ _ _ _ R); exact Hb)) as T2. cbv zeta in T2. destruct T2 as [HS2' _].
      assert (HW' : HWc W (st_trip t1 flush)) by (unfold HWc; rewrite EW; exact HW).
      destruct (sb_lastv t1 flush =? 0).
      + specialize (IH W B' _ _ mb R' HW' HS1' HS2'). cbv zeta in IH. rewrite ESF in IH. exact IH.
      + cbn [fst snd]. split; [reflexivity|]. split; [exists B'; exact R'|]. split; [exact HW'|]. split; [exact HS1'|]. split; [exact HS2'|exact ESF].
  Qed.

  Lemma wupd_rel W B t1 t2 used :
    REL W C B bnd ms pm t1 t2 -> HWc W t1 -> SI c0 s01 t1 -> 0 <= used <= cs_next_in (ds_strm t1) ->
    exists W', REL W' C B bnd ms pm (st_wupd t1 used) (st_wupd t2 used) /\ HWc W' (st_wupd t1 used).
  Proof.
    intros R HW HS Hu.
    si_facts HS D X V Sw Sl Epbs Hl0 Hbs Hsn Hmt Hstr Ewsz Hwr Hpo Hbv Hbb Hao Hai Hins Hinsw Hhw.
    pose proof (df_wl _ D) as Hwl. pose proof (r_win _ _ _ _ _ _ _ _ R) as AW.
    assert (HWi : forall i, i < Z.max (ds_high_water t1) (ds_strstart t1) -> W i).
    { intros i Hi. apply HW. unfold WHI. rewrite Hl0, Z.add_0_r. exact Hi. }
    unfold st_wupd. dsr. rel_fields R.
    destruct (Z.eqb_spec used 0) as [U0|U0]; cbn [negb].
    { exists W. split; [exact R | exact HW]. }
    destruct (Z.leb_spec (ds_w_size t1) used) as [C1|C1].
    -
      eexists. split.
      + apply rel_set_block_start, rel_set_insert, rel_set_strstart. eapply rel_set_window; [apply rel_set_matches; exact R|].
        apply aeq_upd. exact AW.
      + unfold HWc, WHI. dsr. rewrite arr_slice_length' by (clear - Sw; lia). rewrite Hl0.
        intros i Hi. destruct (Z_lt_le_dec i (Z.max (ds_high_water t1) (ds_strstart t1))) as [L|L]; [left; apply HWi; exact L | right; clear - L Hi Hhw; lia].
    - rewrite Ewsz. destruct (Z.leb_spec (2 * ds_w_size t1 - ds_strstart t1) used) as [C2|C2].
      +
        assert (BL : forall P : Z -> Prop, aeq P (ds_window t1) (ds_window t2) -> (forall k, 0 <= k < ds_strstart t1 - ds_w_size t1 -> P (ds_w_size t1 + k)) ->
                  aeq (fun j => P j \/ 0 <= j < 0 + (ds_strstart t1 - ds_w_size t1))
                      (arr_blit (ds_window t1) 0 (ds_window t1) (ds_w_size t1) (ds_strstart t1 - ds_w_size t1))
                      (arr_blit (ds_window t2) 0 (ds_window t2) (ds_w_size t1) (ds_strstart t1 - ds_w_size t1))).
        { intros P HP HK. apply aeq_blit_self; [exact HP | clear - C1 C2 Hu; lia | clear - Sw; lia | rewrite Hwl; clear - Hstr; lia | exact HK]. }
        specialize (BL W AW ltac:(intros k Hk; apply HWi; clear - Hk; lia)).
        destruct (Z.ltb_spec (ds_matches t1) 2) as [C3|C3]; dsr; rel_fields R;
          destruct (Z.ltb_spec (ds_strstart t1 - ds_w_size t1) (ds_insert t1)) as [C4|C4]; dsr; rel_fields R.
        all: eexists; split;
          [ apply rel_set_block_start, rel_set_insert, rel_set_strstart; eapply rel_set_window;
            [ try apply rel_set_insert; try apply rel_set_matches; eapply rel_set_window; [apply rel_set_strstart; exact R | exact BL]
            | apply aeq_upd; exact BL ]
          | unfold HWc, WHI; dsr; rewrite arr_slice_length' by (clear - Hu; lia); rewrite Hl0;
            intros i Hi; destruct (Z_lt_le_dec i (Z.max (ds_high_water t1) (ds_strstart t1))) as [L|L];
            [ left; left; apply HWi; exact L
            | destruct (Z_lt_le_dec i (ds_strstart t1 - ds_w_size t1)); [left; right; clear - L Hi Hhw l; lia | right; clear - L Hi Hhw l; lia] ] ].
      +
        dsr. rel_fields R. eexists. split.
        * apply rel_set_block_start, rel_set_insert, rel_set_strstart. eapply rel_set_window; [exact R|]. apply aeq_upd. exact AW.
        * unfold HWc, WHI. dsr. rewrite arr_slice_length' by (clear - Hu; lia). rewrite Hl0.
          intros i Hi. destruct (Z_lt_le_dec i (Z.max (ds_high_water t1) (ds_strstart t1))) as [L|L]; [left; apply HWi; exact L | right; clear - L Hi Hhw; lia].
  Qed.

  Lemma hw_rel W B t1 t2 :
    REL W C B bnd ms pm t1 t2 -> REL W C B bnd ms pm (hw_st t1) (hw_st t2).
  Proof.
    intros R. unfold hw_st. rel_fields R. destruct (_ <? _); [apply rel_set_high_water|]; exact R.
  Qed.
  Lemma WHI_hw_st t : 0 <= ds_lookahead t -> WHI (hw_st t) = WHI t.
  Proof. intros H. unfold hw_st, WHI. destruct (Z.ltb_spec (ds_high_water t) (ds_strstart t)); dsr; lia. Qed.

  Lemma slide3_rel W B t1 t2 have :
    REL W C B bnd ms pm t1 t2 -> HWc W t1 -> SI c0 s01 t1 -> have = 2 * ds_w_size t1 - ds_strstart t1 ->
    let r1 := st_slide3 t1 have in let r2 := st_slide3 t2 have in
    snd r1 = snd r2 /\ exists W', REL W' C B bnd ms pm (fst r1) (fst r2) /\ HWc W' (fst r1).
  Proof.
    intros R HW HS Hhave.
    si_facts HS D X V Sw Sl Epbs Hl0 Hbs Hsn Hmt Hstr Ewsz Hwr Hpo Hbv Hbb Hao Hai Hins Hinsw Hhw.
    pose proof (df_wl _ D) as Hwl. pose proof (r_win _ _ _ _ _ _ _ _ R) as AW.
    assert (HWi : forall i, i < Z.max (ds_high_water t1) (ds_strstart t1) -> W i).
    { intros i Hi. apply HW. unfold WHI. rewrite Hl0, Z.add_0_r. exact Hi. }
    cbv zeta. unfold st_slide3. dsr. rel_fields R.
    destruct (Z.ltb_spec have (cs_avail_in (ds_strm t1))) as [C1|C1]; cbn [andb]; [| split; [reflexivity | exists W; split; [exact R | exact HW]]].
    destruct (Z.leb_spec (ds_w_size t1) (ds_block_start t1)) as [C2|C2]; [| cbn [fst snd]; split; [reflexivity | exists W; split; [exact R | exact HW]]].
    assert (BL : aeq (fun j => W j \/ 0 <= j < 0 + (ds_strstart t1 - ds_w_size t1))
                     (arr_blit (ds_window t1) 0 (ds_window t1) (ds_w_size t1) (ds_strstart t1 - ds_w_size t1))
                     (arr_blit (ds_window t2) 0 (ds_window t2) (ds_w_size t1) (ds_strstart t1 - ds_w_size t1))).
    { apply aeq_blit_self; [exact AW | clear - C2 Hbs; lia | clear - Sw; lia | rewrite Hwl; clear - Hstr; lia | intros k Hk; apply HWi; clear - Hk; lia]. }
    destruct (Z.ltb_spec (ds_matches t1) 2) as [C3|C3]; dsr; rel_fields R;
      destruct (Z.ltb_spec (ds_strstart t1 - ds_w_size t1) (ds_insert t1)) as [C4|C4]; dsr; rel_fields R; cbn [fst snd].
    all: split; [reflexivity|]; eexists; split;
      [ try apply rel_set_insert; try apply rel_set_matches; eapply rel_set_window; [apply rel_set_strstart, rel_set_block_start; exact R | exact BL]
      | unfold HWc, WHI; dsr; rewrite Hl0;
        intros i Hi; destruct (Z_lt_le_dec i (Z.max (ds_high_water t1) (ds_strstart t1))) as [L|L];
        [ left; apply HWi; exact L | right; clear - L Hi Hhw; lia ] ].
  Qed.

  Lemma read_buf_snd s dst n : 0 < n <= cs_avail_in (ds_strm s) -> snd (read_buf s dst n) = n.
  Proof.
    intros Hn. unfold read_buf. cbv zeta. rewrite (rb_len_eq n (cs_avail_in (ds_strm s)) Hn).
    destruct (Z.eqb_spec n 0); [lia|]. destruct dst; dsr; destruct (ds_wrap s =? 1); [|destruct (ds_wrap s =? 2)| |destruct (ds_wrap s =? 2)]; reflexivity.
  Qed.

  Lemma fillw_rel W B t1 t2 n :
    REL W C B bnd ms pm t1 t2 -> HWc W t1 -> SI c0 s01 t1 -> 0 <= n <= cs_avail_in (ds_strm t1) ->
    exists W', REL W' C B bnd ms pm (st_fillw t1 n) (st_fillw t2 n) /\ HWc W' (st_fillw t1 n).
  Proof.
    intros R HW HS Hn.
    si_facts HS D X V Sw Sl Epbs Hl0 Hbs Hsn Hmt Hstr Ewsz Hwr Hpo Hbv Hbb Hao Hai Hins Hinsw Hhw.
    unfold st_fillw. destruct (Z.eqb_spec n 0) as [N0|N0]; cbn [negb].
    { exists W. split; [exact R | exact HW]. }
    rewrite (rel_strstart _ _ _ _ _ _ _ _ R).
    pose proof (read_buf_window_rel0 _ _ _ _ _ _ _ _ (ds_strstart t1) n R ltac:(clear - Hai; lia) ltac:(clear - Hn; lia)) as RB. cbv zeta in RB.
    destruct RB as (Ek & Est & R').
    pose proof (read_buf_snd t1 (RB_window (ds_strstart t1)) n ltac:(clear - Hn N0; lia)) as Hk.
    pose proof (lz5_eq _ _ (read_buf_lz5 t1 (RB_window (ds_strstart t1)) n)) as (Estr & Elook & Ehw & _ & _).
    destruct (read_buf t1 _ n) as [u1 k1]. destruct (read_buf t2 _ n) as [u2 k2]. cbn [fst snd] in *. subst k2 k1.
    exists (fun i => W i \/ ds_strstart t1 <= i < ds_strstart t1 + n). split.
    - dsr. rel_fields R'. apply rel_set_insert, rel_set_strstart. exact R'.
    - unfold HWc, WHI in *. dsr. rewrite Estr, Elook, Ehw, Hl0 in *.
      intros i Hi. destruct (Z_lt_le_dec i (Z.max (ds_high_water t1) (ds_strstart t1 + 0))) as [L|L]; [left; apply HW; exact L | right; clear - L Hi Hhw; lia].
  Qed.

  Definition wv (s : deflate_state) := (ds_high_water s, ds_strstart s, ds_lookahead s).
  Lemma wv_fp_tail s len : wv (fp_tail s len) = wv s.
  Proof. unfold fp_tail. destruct (_ =? 0); reflexivity. Qed.
  Lemma wv_tr_flush_bits s : wv (tr_flush_bits s) = wv s.
  Proof. destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E; reflexivity. Qed.
  Lemma wv_flush_pending s : wv (flush_pending s) = wv s.
  Proof. rewrite flush_pending_eq. cbv zeta. destruct (_ =? 0); rewrite ?wv_fp_tail; apply wv_tr_flush_bits. Qed.
  Lemma wv_bi_flush s : wv (bi_flush s) = wv s.
  Proof. exact (k_bi_flush wv true true ltac:(constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end) eq_refl s). Qed.
  Lemma WHI_wv a b : wv b = wv a -> WHI b = WHI a.
  Proof. intros E. unfold wv in E. injection E as E1 E2 E3. unfold WHI. rewrite E1, E2, E3. reflexivity. Qed.

  Lemma tsb_some_facts t off len lastv : 0 <= ds_bi_valid t <= 16 -> 0 <= ds_bi_buf t < 2 ^ 16 ->
    let a := tr_stored_block t (Some off) len lastv in
    ds_pending a = tsb_hP t + 1 + 1 + 1 + 1 + len /\ ds_pending_out a = ds_pending_out t /\ ds_strm a = ds_strm t
    /\ arr_len (ds_pending_buf a) = arr_len (ds_pending_buf t) /\ ds_bi_valid a = 0
    /\ SF a = SF t /\ wv a = wv t.
  Proof.
    intros Hbv Hbb. cbv zeta. rewrite (tr_stored_block_eq t (Some off) len lastv Hbv Hbb). unfold tsb_tail. cbv zeta.
    rewrite upd4_pending, upd4_pending_buf, upd4_bi_valid. split; [reflexivity|].
    split; [unfold upd4; reflexivity|]. split; [unfold upd4; reflexivity|].
    split; [| split; [reflexivity | split; [apply SF_upd4 | unfold upd4; reflexivity]]].
    destruct (negb (len =? 0)); rewrite ?arr_len_blit; unfold tsb_lenA; rewrite !arr_len_set; apply tsb_hA_len.
  Qed.

  Lemma SF_tr_flush_bits s : SF (tr_flush_bits s) = SF s.
  Proof. destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E; reflexivity. Qed.
  Lemma SF_flush_pending s : SF (flush_pending s) = SF s.
  Proof. rewrite flush_pending_eq. cbv zeta. destruct (_ =? 0); rewrite ?SF_fp_tail; apply SF_tr_flush_bits. Qed.

  Lemma final_rel W B t1 t2 :
    REL W C B bnd ms pm t1 t2 -> HWc W t1 -> SI c0 s01 t1 ->
    let r1 := st_final t1 flush in let r2 := st_final t2 flush in
    snd r1 = snd r2
    /\ (exists B', REL W C B' bnd ms pm (fst r1) (fst r2) /\ PBC B' (fst r1))
    /\ WHI (fst r1) = WHI t1 /\ SF (fst r1) = SF t1.
  Proof.
    intros R HW HS.
    si_facts HS D X V Sw Sl Epbs Hl0 Hbs Hsn Hmt Hstr Ewsz Hwr Hpo Hbv Hbb Hao Hai Hins Hinsw Hhw.
    pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp). pose proof (df_bl _ D) as Hbl. pose proof (df_wl _ D) as Hwl.
    cbv zeta. unfold st_final. cbv zeta.
    rewrite (rel_t_have _ _ _ _ _ _ _ _ R), (rel_t_mb _ _ _ _ _ _ _ _ R). rel_fields R.
    assert (PBC0 : PBC B t1) by (left; split; [exact Hpo | intros i Hi; exfalso; clear - Hi Hp; lia]).
    match goal with |- context [if ?c then _ else (t1, need_more)] => destruct c eqn:Hcond end.
    2:{ cbn [fst snd]. split; [reflexivity|]. split; [exists B; split; [exact R | exact PBC0]|]. split; reflexivity. }
    pose proof (t_have_eq t1 ltac:(clear - Hbv; lia) ltac:(rewrite Epbs; clear - Sl; lia)) as (Eh & Rh & Rhdr).
    assert (Hleft : wrap32 (ds_strstart t1 - ds_block_start t1) = ds_strstart t1 - ds_block_start t1) by (apply wrap32_id; clear - Hbs Hstr Sw; lia).
    rewrite Hleft in *.
    assert (Hhv : t_have t1 <= ds_pending_buf_size t1 - (ds_bi_valid t1 + 42) / 2 ^ 3).
    { rewrite Eh. destruct (Z.ltb_spec (ds_pending_buf_size t1 - (ds_bi_valid t1 + 42) / 2 ^ 3) 65536) as [l|l]; clear - l Rhdr Epbs Sl; lia. }
    set (len := MIN (ds_strstart t1 - ds_block_start t1) (t_have t1)) in *.
    assert (Hlen : 0 <= len <= t_have t1 /\ len <= ds_strstart t1 - ds_block_start t1).
    { subst len. unfold MIN. destruct (Z.ltb_spec (t_have t1) (ds_strstart t1 - ds_block_start t1)) as [l|l]; clear - l Rh Hbs; lia. }
    clearbody len.
    set (last := if (flush =? Z_FINISH) && (cs_avail_in (ds_strm t1) =? 0) && (len =? ds_strstart t1 - ds_block_start t1) then 1 else 0). clearbody last.
    cbn [fst snd]. split; [reflexivity|].
    pose proof (tsb_hP_range t1) as HP. rewrite Hp in HP.
    pose proof (sb_hdr_eq' t1 ltac:(clear - Hbv; lia)) as EP. rewrite Hp in EP. pose proof (proj1 (sb_hdr_eq t1 ltac:(clear - Hbv; lia))) as Ehdr.
    pose proof (tr_stored_block_rel0 W C bnd ms pm B t1 t2 (Some (ds_block_start t1)) len last R (proj1 (proj1 Hlen)) ltac:(intros HH; discriminate HH)
                  ltac:(intros off Eo _; injection Eo as <-; split; [clear - Hbs; lia|]; split; [rewrite Hwl; clear - Hlen Hstr; lia|];
                        intros i Hi; apply HW; unfold WHI; clear - Hi Hlen Hl0; lia)) as R1.
    rewrite Hp in R1.
    pose proof (tsb_some_facts t1 (ds_block_start t1) len last ltac:(clear - Hbv; lia) Hbb) as Fa. cbv zeta in Fa.
    destruct Fa as (Fp & Fpo & Fst & Fbl & Fbv & FSF & Flzv).
    set (a1 := tr_stored_block t1 _ len last) in *. set (a2 := tr_stored_block t2 _ len last) in *. clearbody a1 a2.
    rewrite (rel_block_start _ _ _ _ _ _ _ _ R1).
    pose proof (rel_set_block_start _ _ _ _ _ _ _ _ (ds_block_start a1 + len) R1) as R2.
    assert (Fb : ds_pending (set_block_start a1 (ds_block_start a1 + len)) = ds_pending a1
                 /\ ds_pending_out (set_block_start a1 (ds_block_start a1 + len)) = ds_pending_out a1
                 /\ ds_strm (set_block_start a1 (ds_block_start a1 + len)) = ds_strm a1
                 /\ ds_pending_buf (set_block_start a1 (ds_block_start a1 + len)) = ds_pending_buf a1
                 /\ ds_bi_valid (set_block_start a1 (ds_block_start a1 + len)) = ds_bi_valid a1
                 /\ SF (set_block_start a1 (ds_block_start a1 + len)) = SF a1
                 /\ WHI (set_block_start a1 (ds_block_start a1 + len)) = WHI a1) by (repeat split; reflexivity).
    set (b1 := set_block_start a1 _) in *. set (b2 := set_block_start a2 _) in *. clearbody b1 b2.
    destruct Fb as (Gp & Gpo & Gst & Gpb & Gbv & GSF & GWHI).
    assert (Epf : ds_pending (bi_flush b1) = ds_pending b1) by (rewrite bi_flush_pending, Gbv, Fbv; reflexivity).
    assert (Hpb : 0 <= ds_pending b1 <= ds_lit_bufsize t1 * 4).
    { rewrite Gp, Fp. rewrite Ehdr in EP. clear - HP Hlen Hhv Epbs EP Rhdr. lia. }
    pose proof (flush_pending_rel0 _ _ _ _ _ _ _ _ R2 ltac:(rewrite Gst, Fst; exact (proj1 Hao)) ltac:(clear - Hpb; lia) ltac:(rewrite Epf; clear - Hpb Sl; lia)
                  ltac:(rewrite Epf, Gpo, Fpo, Hpo, Gpb, Fbl, Hbl; clear - Hpb; lia)
                  ltac:(right; split; [rewrite Gpo, Fpo; exact Hpo | intros i Hi; unfold Bx; right; rewrite Gp in Hi; exact Hi])) as R3.
    pose proof (flush_pending_shape b1 ltac:(rewrite Gst, Fst; exact (proj1 Hao)) ltac:(clear - Hpb; lia) ltac:(clear - Hpb Sl; lia)) as SH.
    cbv zeta in SH. destruct SH as (po & st & E & Ei & En & Ea & Eo & El & Hlen' & Hpo' & _).
    pose proof (wv_flush_pending b1) as L3. pose proof (SF_flush_pending b1) as S3.
    rewrite E in *. rewrite Epf in *.
    set (s9 := bi_flush b1) in *. clearbody s9.
    split.
    - exists (Bx (Bx B 0 (ds_pending a1)) (ds_pending b1) (ds_pending b1)). split; [exact R3|].
      unfold PBC. dsr. rewrite Eo, Gpo, Fpo, Hpo in *.
      destruct Hpo' as [[A1 A2]|[[A1 [A2 A3]]|[A1 A2]]].
      + left. split; [exact A2 | intros i Hi; exfalso; clear - Hi A1; lia].
      + right. split; [clear - Ea A2; lia|]. intros i Hi. unfold Bx. left. right. rewrite <- Gp. clear - Hi Hlen' A2 A3 Hpb. lia.
      + left. split; [exact A2|]. intros i Hi. unfold Bx. left. right. rewrite <- Gp. clear - Hi Hlen' A1. lia.
    - split; [| rewrite S3, GSF; exact FSF]. rewrite (WHI_wv _ _ L3), GWHI. apply WHI_wv. exact Flzv.
  Qed.

  Lemma SF_st_wupd t used : SF (st_wupd t used) = SF t.
  Proof.
    unfold st_wupd. destruct (used =? 0); cbn [negb]; [reflexivity|].
    destruct (_ <=? used); [reflexivity|]. destruct (_ <=? used); [|reflexivity].
    destruct (_ <? 2); destruct (_ <? _); reflexivity.
  Qed.
  Lemma SF_hw_st t : SF (hw_st t) = SF t.
  Proof. unfold hw_st. destruct (_ <? _); reflexivity. Qed.
  Lemma SF_st_slide3 t have : SF (fst (st_slide3 t have)) = SF t.
  Proof. unfold st_slide3. destruct (_ && _); [|reflexivity]. destruct (_ <? 2); destruct (_ <? _); reflexivity. Qed.
  Lemma SF_read_buf_window t off n : SF (fst (read_buf t (RB_window off) n)) = SF t.
  Proof. unfold read_buf. cbv zeta. destruct (_ =? 0); [reflexivity|]. destruct (ds_wrap t =? 1); [|destruct (ds_wrap t =? 2)]; reflexivity. Qed.
  Lemma SF_st_fillw t n : SF (st_fillw t n) = SF t.
  Proof.
    unfold st_fillw. destruct (negb _); [|reflexivity].
    pose proof (SF_read_buf_window t (ds_strstart t) n) as E. destruct (read_buf t _ n) as [u k]. cbn [fst] in E. exact E.
  Qed.

  Theorem deflate_stored_rel_core W B :
    let s1 := s01 in let s2 := s02 in
    REL W C B bnd ms pm s1 s2 -> HWc W s1 -> SI c0 s01 s1 -> SI c0 s02 s2 ->
    let r1 := deflate_stored s1 flush in let r2 := deflate_stored s2 flush in
    snd r1 = snd r2
    /\ (exists W' B', REL W' C B' bnd ms pm (fst r1) (fst r2) /\ HWc W' (fst r1) /\ PBC B' (fst r1))
    /\ DC c0 (fst r1) /\ DC c0 (fst r2) /\ SF (fst r1) = SF s1 /\ dmode (fst r1) = 0.
  Proof.
    cbv zeta. set (s1 := s01). set (s2 := s02). intros R HW HS1 HS2.
    assert (PB0 : forall t B0, SI c0 s01 t -> PBC B0 t).
    { intros t B0 HS. pose proof HS as (_ & _ & _ & _ & _ & Hp).
      pose proof (SI_facts c0 _ HC0 _ HS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpo & _).
      left. split; [exact Hpo | intros i Hi; exfalso; clear - Hi Hp; lia]. }
    assert (DONE : forall W' B' t1 t2 (b : block_state), REL W' C B' bnd ms pm t1 t2 -> HWc W' t1 -> SI c0 s01 t1 -> SI c0 s02 t2 -> SF t1 = SF s1 ->
              snd (t1, b) = snd (t2, b)
              /\ (exists W'' B'', REL W'' C B'' bnd ms pm (fst (t1, b)) (fst (t2, b)) /\ HWc W'' (fst (t1, b)) /\ PBC B'' (fst (t1, b)))
              /\ DC c0 (fst (t1, b)) /\ DC c0 (fst (t2, b)) /\ SF (fst (t1, b)) = SF s1 /\ dmode (fst (t1, b)) = 0).
    { intros W' B' t1 t2 b R' HW' G1 G2 ESF. cbn [fst snd]. split; [reflexivity|].
      split; [exists W', B'; split; [exact R' | split; [exact HW' | exact (PB0 _ _ G1)]]|].
      split; [exact (proj1 G1)|]. split; [exact (proj1 G2)|]. split; [exact ESF | exact (proj1 (proj2 (proj2 G1)))]. }
    pose proof (SI_facts c0 _ HC0 _ HS1) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & _).
    rewrite (deflate_stored_eq s1 flush), (deflate_stored_eq s2 flush). cbv zeta. rel_fields R.
    set (mb := wrap32 (MIN (ds_pending_buf_size s1 - 5) (ds_w_size s1))). clearbody mb.
    set (fuel := Z.to_nat (cs_avail_out (ds_strm s1) + 1)). clearbody fuel.
    pose proof (loop_rel fuel W B s1 s2 mb R HW HS1 HS2) as LR. cbv zeta in LR.
    pose proof (proj2 (loop_stage c0 s01 flush HC0 fuel s1 mb HS1)) as HaiL. revert LR HaiL.
    destruct (deflate_stored_loop fuel s1 flush mb) as [sL1 last1]. destruct (deflate_stored_loop fuel s2 flush mb) as [sL2 last2]. cbn [fst snd].
    intros (Elast & [BL RL] & HWL & HSL1 & HSL2 & SFL) HaiL. subst last2.
    rewrite (rel_strm _ _ _ _ _ _ _ _ RL).
    pose proof (SI_facts c0 _ HC0 _ HSL1) as (DL & XL & VL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HaiL2 & _).
    assert (Eused : wrap32 (cs_avail_in (ds_strm s1) - cs_avail_in (ds_strm sL1)) = cs_avail_in (ds_strm s1) - cs_avail_in (ds_strm sL1))
      by (apply wrap32_id; clear - HaiL Hai HaiL2; lia).
    rewrite Eused.
    pose proof (sv_inlen _ _ V) as Il. pose proof (sv_inlen _ _ VL) as IlL. pose proof (sv_nin _ _ V) as Ni.
    set (used := cs_avail_in (ds_strm s1) - cs_avail_in (ds_strm sL1)) in *.
    assert (Hu : 0 <= used <= cs_next_in (ds_strm sL1)) by (subst used; clear - HaiL Il IlL Ni; lia). clearbody used.
    destruct (wupd_rel W BL sL1 sL2 used RL HWL HSL1 Hu) as [W2 [R2 HW2]].
    pose proof (wupd_stage c0 s01 HC0 sL1 used HSL1 Hu) as WS1. cbv zeta in WS1. destruct WS1 as (HSW1 & _ & _).
    pose proof (wupd_stage c0 s02 HC0 sL2 used HSL2 ltac:(rewrite (rel_strm _ _ _ _ _ _ _ _ RL); exact Hu)) as WS2. cbv zeta in WS2. destruct WS2 as (HSW2 & _ & _).
    pose proof (SF_st_wupd sL1 used) as SFW.
    set (sW1 := st_wupd sL1 used) in *. set (sW2 := st_wupd sL2 used) in *. clearbody sW1 sW2.
    pose proof (hw_rel W2 BL sW1 sW2 R2) as R3.
    pose proof (SI_facts c0 _ HC0 _ HSW1) as (_ & _ & _ & _ & _ & _ & Hl0W & _).
    assert (HW3 : HWc W2 (hw_st sW1)) by (unfold HWc; rewrite (WHI_hw_st sW1) by (rewrite Hl0W; lia); exact HW2).
    pose proof (proj1 (hw_stage c0 s01 HC0 sW1 HSW1)) as HS3. pose proof (proj1 (hw_stage c0 s02 HC0 sW2 HSW2)) as HS3'.
    pose proof (SF_hw_st sW1) as SF3.
    set (t1 := hw_st sW1) in *. set (t2 := hw_st sW2) in *. clearbody t1 t2.
    assert (SFt : SF t1 = SF s1) by (rewrite SF3, SFW; exact SFL).
    destruct (negb (last1 =? 0)); [exact (DONE W2 BL t1 t2 finish_done R3 HW3 HS3 HS3' SFt)|].
    rel_fields R3.
    match goal with |- context [if ?c then (t1, block_done) else _] => destruct c end; [exact (DONE W2 BL t1 t2 block_done R3 HW3 HS3 HS3' SFt)|].
    pose proof (SI_facts c0 _ HC0 _ HS3) as (_ & _ & _ & Sw3 & _ & _ & _ & Hbs3 & _ & _ & Hstr3 & Ewsz3 & _ & _ & _ & _ & _ & Hai3 & _).
    assert (Ehave : wrap32 (ds_window_size t1 - ds_strstart t1) = 2 * ds_w_size t1 - ds_strstart t1) by (rewrite Ewsz3; apply wrap32_id; clear - Hstr3 Hbs3 Sw3; lia).
    rewrite Ehave.
    pose proof (slide3_rel W2 BL t1 t2 _ R3 HW3 HS3 eq_refl) as SL. cbv zeta in SL.
    pose proof (slide3_stage c0 s01 HC0 t1 _ HS3 eq_refl) as SL1. cbv zeta in SL1.
    pose proof (slide3_stage c0 s02 HC0 t2 (2 * ds_w_size t1 - ds_strstart t1) HS3' ltac:(rewrite <- (rel_w_size _ _ _ _ _ _ _ _ R3), <- (rel_strstart _ _ _ _ _ _ _ _ R3); reflexivity)) as SL2. cbv zeta in SL2.
    pose proof (SF_st_slide3 t1 (2 * ds_w_size t1 - ds_strstart t1)) as SF4.
    revert SL SL1 SL2 SF4.
    destruct (st_slide3 t1 _) as [u1 have1]. destruct (st_slide3 t2 _) as [u2 have2]. cbn [fst snd].
    intros (Ehv & [W4 [R4 HW4]]) (HS4 & _ & Ehave4 & Ews4) (HS4' & _) SF4. subst have2.
    rewrite (rel_strm _ _ _ _ _ _ _ _ R4).
    pose proof (SI_facts c0 _ HC0 _ HS4) as (_ & _ & _ & _ & _ & _ & _ & Hbs4 & _ & _ & Hstr4 & _ & _ & _ & _ & _ & _ & Hai4 & _).
    assert (Hfm : 0 <= fmin have1 (cs_avail_in (ds_strm u1)) <= cs_avail_in (ds_strm u1) /\ fmin have1 (cs_avail_in (ds_strm u1)) <= 2 * ds_w_size u1 - ds_strstart u1).
    { unfold fmin. rewrite Ehave4, Ews4. destruct (Z.ltb_spec (cs_avail_in (ds_strm u1)) (2 * ds_w_size t1 - ds_strstart u1)) as [l|l]; clear - l Hai4 Hstr4 Hbs4 Ews4; lia. }
    set (n := fmin have1 (cs_avail_in (ds_strm u1))) in *. clearbody n.
    destruct (fillw_rel W4 BL u1 u2 n R4 HW4 HS4 (proj1 Hfm)) as [W5 [R5 HW5]].
    pose proof (proj1 (fillw_stage c0 s01 HC0 u1 n HS4 (proj1 Hfm) (proj2 Hfm))) as HS5.
    pose proof (proj1 (fillw_stage c0 s02 HC0 u2 n HS4' ltac:(rewrite (rel_strm _ _ _ _ _ _ _ _ R4); exact (proj1 Hfm))
                  ltac:(rewrite (rel_strstart _ _ _ _ _ _ _ _ R4), (rel_w_size _ _ _ _ _ _ _ _ R4); exact (proj2 Hfm)))) as HS5'.
    pose proof (SF_st_fillw u1 n) as SF5.
    set (v1 := st_fillw u1 n) in *. set (v2 := st_fillw u2 n) in *. clearbody v1 v2.
    pose proof (hw_rel W5 BL v1 v2 R5) as R6.
    pose proof (SI_facts c0 _ HC0 _ HS5) as (_ & _ & _ & _ & _ & _ & Hl05 & _).
    assert (HW6 : HWc W5 (hw_st v1)) by (unfold HWc; rewrite (WHI_hw_st v1) by (rewrite Hl05; lia); exact HW5).
    pose proof (proj1 (hw_stage c0 s01 HC0 v1 HS5)) as HS6. pose proof (proj1 (hw_stage c0 s02 HC0 v2 HS5')) as HS6'.
    pose proof (SF_hw_st v1) as SF6.
    set (x1 := hw_st v1) in *. set (x2 := hw_st v2) in *. clearbody x1 x2.
    pose proof (final_rel W5 BL x1 x2 R6 HW6 HS6) as FR. cbv zeta in FR. destruct FR as (Eb & [B7 [R7 P7]] & EW7 & SF7).
    pose proof (final_stage c0 s01 flush HC0 x1 HS6) as FN1. cbv zeta in FN1. destruct FN1 as (DC7 & _).
    pose proof (final_stage c0 s02 flush HC0 x2 HS6') as FN2. cbv zeta in FN2. destruct FN2 as (DC7' & _).
    split; [exact Eb|]. split; [exists W5, B7; split; [exact R7 | split; [unfold HWc; rewrite EW7; exact HW6 | exact P7]]|].
    split; [exact DC7|]. split; [exact DC7'|].
    assert (SFf : SF (fst (st_final x1 flush)) = SF s1) by (rewrite SF7, SF6, SF5, SF4, SF3, SFW; exact SFL).
    split; [exact SFf|]. rewrite (dmode_SF _ _ SFf). exact (proj1 (proj2 (proj2 HS1))).
  Qed.
End StoredRel.


Lemma CFG_of_INV s : INV s -> CFG s.
Proof. intros I. exact (conj (iv_wbits s I) (conj (iv_hbits s I) (iv_strat s I))). Qed.
Lemma CFG_SF a b : SF b = SF a -> CFG a -> CFG b.
Proof.
  intros E (C1 & C2 & C3). pose proof (SF_fields _ _ E) as ((_ & _ & _ & _ & _ & Esy) & _ & _ & _ & _ & (Ewb & Ehb & _)).
  unfold CFG. rewrite Esy, Ewb, Ehb. exact (conj C1 (conj C2 C3)).
Qed.
Lemma CFG_clean a b : clean a = clean b -> CFG a -> CFG b.
Proof.
  intros E (C1 & C2 & C3). unfold CFG.
  rewrite <- (clean_eq_fieldT ds_w_bits a b E ltac:(reflexivity)), <- (clean_eq_fieldT ds_hash_bits a b E ltac:(reflexivity)),
    <- (clean_eq_fieldT ds_strategy a b E ltac:(reflexivity)).
  exact (conj C1 (conj C2 C3)).
Qed.

Lemma SI_intro c0 s flush : BFPRE c0 s flush -> dmode s = 0 -> SI c0 s s.
Proof.
  intros (HC0 & HDC & Hp & Hst & Hfl) Hm.
  split; [exact HDC|]. split; [reflexivity|]. split; [exact Hm|]. split; [exact Hst|]. split; [apply OUTLE_refl | exact Hp].
Qed.

Theorem deflate_stored_rel c0 s1 s2 flush :
  C0OK' c0 -> SI c0 s1 s1 -> SI c0 s2 s2 -> FREL0 s1 s2 -> INV s1 -> INV s2 ->
  let r1 := deflate_stored s1 flush in let r2 := deflate_stored s2 flush in
  snd r1 = snd r2 /\ FREL0 (fst r1) (fst r2) /\ INV (fst r1) /\ INV (fst r2).
Proof.
  intros HC0 HS1 HS2 (W & C & B & bnd & ms & pm & R & HW & HP & HSY & HL) I1 I2.
  pose proof (deflate_stored_rel_core c0 s1 s2 flush HC0 C bnd ms pm W B R HW HS1 HS2) as XX. cbv zeta in XX.
  destruct XX as (E & (W' & B' & R' & HW' & P') & D1 & D2 & ESF & Hm).
  cbv zeta. split; [exact E|].
  assert (G1 : CFG (fst (deflate_stored s1 flush))) by (apply (CFG_SF s1); [exact ESF | apply CFG_of_INV; exact I1]).
  split.
  - exists W', C, B', bnd, ms, pm. split; [exact R'|]. split; [exact HW'|]. split; [exact P'|]. split.
    + intros i Hi. exfalso. pose proof (proj1 (proj2 (proj2 (dx_st0 _ (proj2 (proj1 D1)) Hm)))) as Hsn. clear - Hi Hsn. lia.
    + apply dmode0_level. exact Hm.
  - split; [apply (INV_of_DC c0); [exact D1 | exact G1]|].
    apply (INV_of_DC c0); [exact D2 | apply (CFG_clean (fst (deflate_stored s1 flush))); [exact (r_clean _ _ _ _ _ _ _ _ R') | exact G1]].
Qed.
