(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemFill.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefAdler_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateInitLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateKZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateKZ.RefDeflateEnd1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateKZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateKZ.RefDeflateDict1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateKZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateKZ.RefDeflateDict2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe.RefDeflateDictM.

Module RefDeflateDict3.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemFill.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFillWin4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFillWin4.RefFillWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFillWin4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefInflateKZ.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefInflateKZ.RefDeflateDict2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe.RefDeflateDictM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Loop.
Variable S : Z.
Variable sp : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ws : Z.
Variable hs : Z.
Variable INP : arr.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation strm := (p_strm p).
Local Notation DIN := (zp_in zp).
Local Notation n := (arr_len INP).
Hypothesis Lsp : 176 <= sp /\ sp + 80 <= 2 ^ 63.
Hypothesis LS : 0 < S /\ S + 5952 <= 2 ^ 63.
Hypothesis LW : 0 < W /\ W + 2 * ws <= 2 ^ 63.
Hypothesis LPV : 0 < PV /\ PV + 2 * ws <= 2 ^ 63.
Hypothesis LHD : 0 < HD /\ HD + 2 * hs <= 2 ^ 63.
Hypothesis Lstrm : 0 < strm /\ strm + 112 <= 2 ^ 63.
Hypothesis LIN : 0 < DIN /\ DIN + n < 2 ^ 63.
Hypothesis Lws : 256 <= ws <= 32768.
Hypothesis Lhs : 256 <= hs <= 65536.
Hypothesis Ln : 0 <= n <= ws.
Hypothesis AP : apart_all [(sp - 176, 176); (S, 5952); (W, 2 * ws); (PV, 2 * ws); (HD, 2 * hs); (strm, 112); (DIN, n)].

Definition FP : franges :=
  [(sp - 176, 176); (S, 212); (S + 5888, 64); (W, 2 * ws); (PV, 2 * ws); (HD, 2 * hs); (strm, 24); (strm + 96, 8)].

Hypothesis FP_rod : forall x, in_franges FP x -> ~ (0x2f550 <= x < 0x2f9d0 + 4096).

Definition KC (t : deflate_state) : Prop :=
  ds_w_size t = ws /\ ds_hash_size t = hs /\ cs_input (ds_strm t) = INP /\ ds_wrap t = 0.

Local Ltac apart i j :=
  let H := fresh "AP" in
  pose proof (apart_get _ i j (0, 0) AP ltac:(lia) ltac:(cbn; lia)) as H;
  cbn [nth] in H; unfold apart in H; cbn [fst snd] in H.

Lemma in_LF_FP : forall t x, KC t -> in_franges (LF S sp p t) x -> in_franges FP x.
Proof.
  intros t x (Kws & Khs & _ & _) Hx. unfold LF in Hx. rewrite Kws, Khs in Hx. unfold FP. cbn [in_franges] in *. lia.
Qed.


Lemma update_hash_mod32 : forall s h h' c, 0 <= ds_hash_shift s ->
  h mod 2 ^ 32 = h' mod 2 ^ 32 -> update_hash s h c = update_hash s h' c.
Proof.
  intros s h h' c Hsh E. unfold update_hash. f_equal. f_equal.
  rewrite !wrap32_mod, !Z.shiftl_mul_pow2 by lia.
  rewrite <- (Z.mul_mod_idemp_l h), <- (Z.mul_mod_idemp_l h') by lia. rewrite E. reflexivity.
Qed.

Definition il_h (t : deflate_state) (str : Z) : Z :=
  update_hash t (ds_ins_h t) (arr_get (ds_window t) (str + (MIN_MATCH - 1))).
Definition il_s1 (t : deflate_state) (str : Z) : deflate_state := set_ins_h t (il_h t str).
Definition il_s2 (t : deflate_state) (str : Z) : deflate_state :=
  set_prev (il_s1 t str) (arr_set (ds_prev (il_s1 t str)) (Z.land str (ds_w_mask (il_s1 t str))) (arr_get (ds_head (il_s1 t str)) (il_h t str))).
Definition il_s3 (t : deflate_state) (str : Z) : deflate_state :=
  set_head (il_s2 t str) (arr_set (ds_head (il_s2 t str)) (il_h t str) (wrap16 str)).

Lemma setdict_inner_S : forall k t str m,
  setdict_inner (Datatypes.S k) t str m =
  (if negb (m - 1 =? 0) then setdict_inner k (il_s3 t str) (str + 1) (m - 1) else (il_s3 t str, str + 1)).
Proof. intros. reflexivity. Qed.

Definition fuel_ok (f : nat) (t : deflate_state) : Prop :=
  AI t + 1 + (if MIN_MATCH <=? ds_lookahead t then 1 else 0) <= Z.of_nat f.

Lemma sdput3_strm : forall t u, ds_strm (sdput3 t u) = ds_strm t.
Proof. intros. reflexivity. Qed.
Lemma sdput3_lookahead : forall t u, ds_lookahead (sdput3 t u) = ds_lookahead t.
Proof. intros. reflexivity. Qed.
Lemma sdput3_insert : forall t u, ds_insert (sdput3 t u) = ds_insert t.
Proof. intros. reflexivity. Qed.


Definition sd_fin7 (t : deflate_state) (wrap : Z) : deflate_state :=
  set_wrap (set_match_available (set_match_length (set_prev_length (set_lookahead (set_insert (set_block_start
    (set_strstart t (ds_strstart t + ds_lookahead t)) (ds_strstart t + ds_lookahead t)) (ds_lookahead t)) 0)
    (MIN_MATCH - 1)) (MIN_MATCH - 1)) 0) wrap.
End Loop.
End RefDeflateDict3.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflateDict_run.RefDeflateDict3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma znth_zskipn : forall (l : list Z) k i, 0 <= k -> 0 <= i -> ZIface.znth 0 (zskipn k l) i = ZIface.znth 0 l (i + k).
Proof.
  intros l k i Hk Hi. unfold ZIface.znth, zskipn.
  replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i + k <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite nth_skipn. f_equal. lia.
Qed.

Lemma zlength_zskipn : forall (l : list Z) k, 0 <= k <= zlength l -> zlength (zskipn k l) = zlength l - k.
Proof. intros l k Hk. unfold zlength, zskipn in *. rewrite length_skipn. lia. Qed.

Lemma arr_get_of_list : forall l i, 0 <= i < zlength l -> arr_get (arr_of_list l) i = ZIface.znth 0 l i.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  unfold arr_inb, arr_make. rewrite arr_len_init.
  replace ((0 <=? i) && (i <? 0 + zlength l) && ((0 <=? i) && (i <? zlength l))) with true
    by (symmetry; rewrite !andb_true_iff; rewrite !Z.leb_le, !Z.ltb_lt; lia).
  unfold ZIface.znth. rewrite (proj2 (Z.ltb_ge i 0)) by lia. rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma bytes_ok_znth : forall l i, bytes_ok l -> 0 <= ZIface.znth 0 l i < 256.
Proof.
  intros l i H. unfold ZIface.znth. destruct (i <? 0); [lia|].
  unfold bytes_ok in H. rewrite Forall_forall in H.
  destruct (nth_in_or_default (Z.to_nat i) l 0) as [Hin| ->]; [exact (H _ Hin) | lia].
Qed.

Lemma dwf_set_strm : forall s st, dwf s -> dwf (set_strm s st).
Proof. intros s st H. destruct H; constructor; assumption. Qed.

Lemma dwf_fin : forall ds t wrap saved,
  dwf ds -> SDK ds t -> fw_wf (ds_w_size ds) (ds_hash_size ds) t -> ds_lookahead t < MIN_MATCH -> - 2 <= wrap <= 2 ->
  dwf (fst (sd_fin wrap saved t)).
Proof.
  intros ds t wrap saved Hd Hk HW Hlook Hwrap.
  pose proof (wf_wsr _ _ _ HW) as Lws. unfold MIN_MATCH in Hlook.
  unfold sd_fin. cbv zeta. cbn [fst]. unfold SDK in Hk. rewrite Hk.
  destruct Hd; destruct HW; constructor; unfold sdput; dsred; try assumption; try (unfold MIN_MATCH; lia).
Qed.

Lemma dblocks_SDK : forall ds t, SDK ds t -> dblocks t = dblocks ds.
Proof. intros ds t Hk. unfold SDK in Hk. rewrite Hk. reflexivity. Qed.


Section SD.
  Variable ds : deflate_state.
Variable zc : ZCall.
Variable aout : Z.
Variable dict : list Z.
  Definition sd_cs : cstrm := cstrm_of_call (zc_ao zc aout).
  Definition sd_s0 : deflate_state := set_strm ds sd_cs.
  Definition sd_s3 : deflate_state := fst (sd_split (ds_wrap ds) (sd_s2 sd_s0 dict) dict).
  Definition sd_dict : list Z := snd (sd_split (ds_wrap ds) (sd_s2 sd_s0 dict) dict).
  Definition sd_clr : bool := (ds_w_size ds <=? zlength dict) && (ds_wrap ds =? 0).
  Definition sd_cs3 : cstrm := if ds_wrap ds =? 1 then cset_adler sd_cs (adler32_upd (cs_adler sd_cs) dict) else sd_cs.

  Lemma sd_s3_facts : 0 <= ds_w_size ds ->
    SDK ds sd_s3 /\ ds_wrap sd_s3 = 0 /\ ds_lookahead sd_s3 = ds_lookahead ds /\ ds_window sd_s3 = ds_window ds
    /\ ds_prev sd_s3 = ds_prev ds /\ ds_ins_h sd_s3 = ds_ins_h ds /\ ds_match_start sd_s3 = ds_match_start ds
    /\ ds_high_water sd_s3 = ds_high_water ds /\ ds_strm sd_s3 = sd_cs3
    /\ ds_strstart sd_s3 = (if sd_clr then 0 else ds_strstart ds)
    /\ ds_block_start sd_s3 = (if sd_clr then 0 else ds_block_start ds)
    /\ ds_insert sd_s3 = (if sd_clr then 0 else ds_insert ds)
    /\ ds_head sd_s3 = (if sd_clr then arr_fill (arr_set (ds_head ds) (ds_hash_size ds - 1) NIL) 0 (ds_hash_size ds - 1) 0 else ds_head ds)
    /\ sd_dict = (if ds_w_size ds <=? zlength dict then zskipn (zlength dict - ds_w_size ds) dict else dict)
    /\ zlength sd_dict = sd_n (ds_w_size ds) (zlength dict).
  Proof.
    intros Hws. unfold sd_s3, sd_dict, sd_clr, sd_cs3, sd_split, sd_s2, sd_s0, sd_clear, clear_hash, sd_n, SDK, sdput.
    assert (Hl : 0 <= zlength dict) by (unfold zlength; lia).
    change (ds_wrap (set_strm ds sd_cs)) with (ds_wrap ds).
    destruct (Z.eqb_spec (ds_wrap ds) 1) as [W1|W1];
      [rewrite W1 | replace (ds_wrap ds =? 0) with (0 =? ds_wrap ds) by apply Z.eqb_sym; destruct (Z.eqb_spec 0 (ds_wrap ds)) as [W0|W0]];
      cbn [Z.eqb Pos.eqb andb]; dsred;
      destruct (Z.leb_spec (ds_w_size ds) (zlength dict)); cbn [andb fst snd]; cbv zeta; dsred;
      first [ replace (zlength dict <? ds_w_size ds) with false by (symmetry; apply Z.ltb_ge; lia)
            | replace (zlength dict <? ds_w_size ds) with true by (symmetry; apply Z.ltb_lt; lia) ];
      repeat split; try reflexivity; rewrite ?zlength_zskipn by lia; try lia.
  Qed.

  Lemma sd_cs3_facts :
    cs_input sd_cs3 = arr_of_list (zc_input zc) /\ cs_next_in sd_cs3 = 0 /\ cs_out_rev sd_cs3 = []
    /\ cs_avail_out sd_cs3 = aout /\ cs_total_in sd_cs3 = zs_total_in (zc_strm zc) /\ cs_total_out sd_cs3 = zs_total_out (zc_strm zc)
    /\ cs_msg sd_cs3 = zs_msg (zc_strm zc) /\ cs_data_type sd_cs3 = zs_data_type (zc_strm zc)
    /\ cs_adler sd_cs3 = (if ds_wrap ds =? 1 then adler32_upd (zs_adler (zc_strm zc)) dict else zs_adler (zc_strm zc)).
  Proof. unfold sd_cs3, sd_cs. destruct (ds_wrap ds =? 1); repeat split; reflexivity. Qed.

  Lemma sd_s3_w1 : ds_wrap ds = 1 ->
    sd_s3 = set_wrap (set_strm sd_s0 (cset_adler (ds_strm sd_s0) (adler32_upd (cs_adler (ds_strm sd_s0)) dict))) 0.
  Proof.
    intros W1. unfold sd_s3, sd_split, sd_s2. change (ds_wrap sd_s0) with (ds_wrap ds). rewrite W1. cbn [Z.eqb Pos.eqb].
    destruct (_ <=? _); reflexivity.
  Qed.
  Lemma sd_s3_plain : ds_wrap ds <> 1 -> (zlength dict < ds_w_size ds \/ ds_wrap ds <> 0) -> sd_s3 = set_wrap sd_s0 0.
  Proof.
    intros W1 H. unfold sd_s3, sd_split, sd_s2. change (ds_wrap sd_s0) with (ds_wrap ds).
    replace (ds_wrap ds =? 1) with false by (symmetry; apply Z.eqb_neq; exact W1).
    change (ds_w_size (set_wrap sd_s0 0)) with (ds_w_size ds).
    destruct (Z.leb_spec (ds_w_size ds) (zlength dict)); [|reflexivity].
    replace (ds_wrap ds =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  Qed.
  Lemma sd_s3_clr : ds_wrap ds = 0 -> ds_w_size ds <= zlength dict -> sd_s3 = sd_clear (set_wrap sd_s0 0).
  Proof.
    intros W0 H. unfold sd_s3, sd_split, sd_s2. change (ds_wrap sd_s0) with (ds_wrap ds). rewrite W0. cbn [Z.eqb].
    change (ds_w_size (set_wrap sd_s0 0)) with (ds_w_size ds).
    destruct (Z.leb_spec (ds_w_size ds) (zlength dict)); [reflexivity | lia].
  Qed.

  Lemma sd_model : deflateStateCheck sd_s0 = false -> sd_bad sd_s0 = false ->
    deflateSetDictionary_m ds (zc_ao zc aout) dict = sd_tail (ds_wrap ds) sd_s3 sd_dict.
  Proof.
    intros Hc Hb. rewrite sdm_unfold. cbv zeta. change (set_strm ds (cstrm_of_call (zc_ao zc aout))) with sd_s0.
    rewrite Hc, Hb. change (ds_wrap sd_s0) with (ds_wrap ds). unfold sd_s3, sd_dict.
    destruct (sd_split _ _ _); reflexivity.
  Qed.
End SD.


Section Proofs.

  Section Call.
  Variable sp : Z.
Variable ZP : Z.
Variable nin : Z.
Variable ain : Z.
Variable nout : Z.
Variable aout : Z.
Variable S : Z.
Variable ds : deflate_state.
Variable zc : ZCall.
Variable pd : Z.
Variable dict : list Z.
Variable ra : Z.
  Hypothesis Hzok : zstrm_ok (zc_strm zc).
  Hypothesis Hdok : bytes_ok dict.
  Hypothesis Hdl : 0 < zlength dict < 2 ^ 32.
  Hypothesis HAP : ZP + ZS_SIZE <= pd \/ pd + zlength dict <= ZP.
  Local Notation ws := (ds_w_size ds).
  Local Notation hs := (ds_hash_size ds).
  Local Notation dl := (zlength dict).

  Local Notation SL := 192320. Local Notation SD' := 192352. Local Notation SB := 192384.

  Ltac rcs_via Hfr Hprev :=
    let r := fresh "r" in let Hr := fresh "Hr" in
    intros r Hr; rewrite <- (Hprev r Hr); apply Hfr; revert Hr; clear; intros Hr; cbn in Hr;
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; reflexivity.
  End Call.
End Proofs.


Section Api.
End Api.
