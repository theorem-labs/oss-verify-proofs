(** * Bridge.DEmit.BrCompress — pair D31 of PAIRS.md: [compress_block], S5 vs RT.

    Group R's [RiskIface.ov_emit_dyn] / [ov_emit_stat] show that at a flush
    S5's [compress_block], reading its symbols out of the overlaid
    [pending_buf], equals [sbs_run] over the send_bits calls computed from
    the PRISTINE symbols ([OvKit.cb_all]).  This file shows those calls are
    exactly what RT's [compress_block] emits from its separate [ts_symbuf]:
    [cb_all_rt] (RT's bit writer run over the calls = RT's
    [compress_block]), given that the pristine symbol bytes are RT's
    ([sym_rel]) and the code tables agree on the codes in use.  With
    [BrSbs.br_sbs_run] this relates the two emissions ([br_cb_body]). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees CompressModel DeflateOverlay SendModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsOut Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs BrSbs BrTally.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Risk Require OvKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module CM := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.CompressModel.
Module SM := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.SendModel.

(* ------------------------------------------------------------------------- *)
(* 1.  Tables                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma extra_lbits_agree : forall i, 0 <= i -> arr_get DS.extra_lbits_a i = RT.extra_lbits i.
Proof. intros i Hi. unfold DS.extra_lbits_a, RT.extra_lbits. rewrite arr_of_list_zlist by exact Hi. reflexivity. Qed.
Lemma extra_dbits_agree : forall i, 0 <= i -> arr_get DS.extra_dbits_a i = RT.extra_dbits i.
Proof. intros i Hi. unfold DS.extra_dbits_a, RT.extra_dbits. rewrite arr_of_list_zlist by exact Hi. reflexivity. Qed.
Lemma base_length_agree : forall i, 0 <= i -> arr_get DS.base_length_a i = RT.base_length i.
Proof. intros i Hi. unfold DS.base_length_a, RT.base_length. rewrite arr_of_list_zlist by exact Hi. reflexivity. Qed.
Lemma base_dist_agree : forall i, 0 <= i -> arr_get DS.base_dist_a i = RT.base_dist i.
Proof. intros i Hi. unfold DS.base_dist_a, RT.base_dist. rewrite arr_of_list_zlist by exact Hi. reflexivity. Qed.

(** The static trees as related arrays. *)
Lemma static_ltree_rel :
  arr_rel DS.static_ltree_fc (RT.tr_fc RT.static_ltree) 0 286 /\ arr_rel DS.static_ltree_dl (RT.tr_dl RT.static_ltree) 0 286.
Proof.
  split; intros i Hi; cbn [RT.tr_fc RT.tr_dl RT.static_ltree];
    [unfold DS.static_ltree_fc | unfold DS.static_ltree_dl]; rewrite arr_of_list_zlist by lia; reflexivity.
Qed.

Lemma static_dtree_rel :
  arr_rel DS.static_dtree_fc (RT.tr_fc RT.static_dtree) 0 30 /\ arr_rel DS.static_dtree_dl (RT.tr_dl RT.static_dtree) 0 30.
Proof.
  split; intros i Hi; cbn [RT.tr_fc RT.tr_dl RT.static_dtree];
    [unfold DS.static_dtree_fc | unfold DS.static_dtree_dl]; rewrite arr_of_list_zlist by lia; reflexivity.
Qed.

Lemma bw_send_bits_u16 : forall v l b, ZBitsOut.bw_send_bits (Base.u16 v) l b = ZBitsOut.bw_send_bits v l b.
Proof.
  intros v l b. unfold ZBitsOut.bw_send_bits. cbv zeta.
  assert (E : Base.u16 (Base.u16 v) = Base.u16 v) by (unfold Base.u16; apply Z.mod_mod; lia).
  rewrite E. reflexivity.
Qed.

Lemma u16_wrap32 : forall v, Base.u16 (wrap32 v) = Base.u16 v.
Proof.
  intros v. rewrite <- !BrBits.wrap16_u16. rewrite !wrap16_mod, wrap32_mod.
  change (2 ^ 32) with (2 ^ 16 * 2 ^ 16). rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_mod by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  One symbol                                                            *)
(* ------------------------------------------------------------------------- *)

(** RT's emission for the symbol at [sx] (verbatim [cb_step]'s [b']). *)
Definition rt_sym_emit (sym : Base.zarr) (lt dt : RT.Tree) (sx : Z) (b : ZBitsOut.BW) : ZBitsOut.BW :=
  let dist := Z.land (sym sx) 255 + Z.shiftl (Z.land (sym (sx + 1)) 255) 8 in
  let lc   := sym (sx + 2) in
  if Z.eqb dist 0 then RT.send_code lc lt b
  else
    let code := RT.length_code lc in
    let b1   := RT.send_code (code + RT.LITERALS + 1) lt b in
    let ex   := RT.extra_lbits code in
    let b2   := if Z.eqb ex 0 then b1 else ZBitsOut.bw_send_bits (lc - RT.base_length code) ex b1 in
    let d1   := dist - 1 in
    let dc   := RT.d_code d1 in
    let b3   := RT.send_code dc dt b2 in
    let ex2  := RT.extra_dbits dc in
    if Z.eqb ex2 0 then b3 else ZBitsOut.bw_send_bits (d1 - RT.base_dist dc) ex2 b3.

Lemma cb_step_eq : forall sym symnext lt dt st,
  RT.cb_step sym symnext lt dt st
  = let st' := {| RT.c_sx := RT.c_sx st + 3; RT.c_bw := rt_sym_emit sym lt dt (RT.c_sx st) (RT.c_bw st) |} in
    if RT.c_sx st + 3 <? symnext then RT.CbCont st' else RT.CbDone st'.
Proof. reflexivity. Qed.

Section Sym.
Variables (s0 : DS.deflate_state) (lfc ldl dfc ddl : arr) (lt dt : RT.Tree) (sym : Base.zarr) (N : Z).
Hypothesis Hsym : forall i, 0 <= i < 3 * N -> DS.sym_buf_get s0 i = sym i.
Hypothesis Hok : forall j, 0 <= j < N -> DO.sym_okb s0 j.
Hypothesis Hlfc : arr_rel lfc (RT.tr_fc lt) 0 286.
Hypothesis Hldl : arr_rel ldl (RT.tr_dl lt) 0 286.
Hypothesis Hdfc : arr_rel dfc (RT.tr_fc dt) 0 30.
Hypothesis Hddl : arr_rel ddl (RT.tr_dl dt) 0 30.

Lemma sym_calls_rt : forall k b, 0 <= k < N ->
  rt_sbs b (CM.sym_calls s0 lfc ldl dfc ddl (3 * k)) = rt_sym_emit sym lt dt (3 * k) b.
Proof.
  intros k b Hk. destruct (Hok k Hk) as [Hlc Hd].
  unfold CM.sym_calls, rt_sym_emit. cbv zeta.
  assert (ED : CM.sym_dist s0 (3 * k) = Z.land (sym (3 * k)) 255 + Z.shiftl (Z.land (sym (3 * k + 1)) 255) 8).
  { unfold CM.sym_dist, CM.sym_d0, CM.sym_d1. rewrite !Hsym by lia. reflexivity. }
  assert (EL : CM.sym_lc s0 (3 * k) = sym (3 * k + 2)).
  { unfold CM.sym_lc. replace (3 * k + 1 + 1) with (3 * k + 2) by lia. apply Hsym. lia. }
  rewrite ED, EL. rewrite ED in Hd. rewrite EL in Hlc.
  set (dist := Z.land (sym (3 * k)) 255 + Z.shiftl (Z.land (sym (3 * k + 1)) 255) 8) in *.
  set (lc := sym (3 * k + 2)) in *.
  unfold RT.send_code, RT.t_code, RT.t_len.
  destruct (Z.eqb_spec dist 0) as [D0|D0].
  - cbn [rt_sbs]. rewrite (Hlfc lc), (Hldl lc) by lia. reflexivity.
  - rewrite length_code_agree by lia.
    pose proof (TT.length_code_bound lc) as LB. rewrite length_code_agree in LB by lia.
    set (code := RT.length_code lc) in *.
    rewrite extra_lbits_agree, base_length_agree by lia.
    rewrite d_code_agree by lia.
    assert (DC : 0 <= RT.d_code (dist - 1) < 30).
    { rewrite <- d_code_agree by lia. unfold DS.d_code. destruct (_ <? 256); apply TT.dist_code_bound. }
    set (dc := RT.d_code (dist - 1)) in *.
    rewrite extra_dbits_agree, base_dist_agree by lia.
    rewrite !rt_sbs_app. cbn [rt_sbs].
    rewrite (Hlfc (code + DS.LITERALS + 1)), (Hldl (code + DS.LITERALS + 1)) by (unfold DS.LITERALS; lia).
    rewrite (Hdfc dc), (Hddl dc) by lia.
    change DS.LITERALS with RT.LITERALS.
    destruct (Z.eqb_spec (RT.extra_lbits code) 0) as [X0|X0]; cbn [negb rt_sbs app];
      destruct (Z.eqb_spec (RT.extra_dbits dc) 0) as [Y0|Y0]; cbn [negb rt_sbs app];
      rewrite ?(Z.eqb_refl), ?X0, ?Y0; try reflexivity;
      rewrite <- bw_send_bits_u16, u16_wrap32, bw_send_bits_u16; reflexivity.
Qed.

Lemma cb_loop_rt : forall f k b, 0 <= k < N -> (Z.to_nat (N - k) <= f)%nat ->
  RT.cb_loop f sym (3 * N) lt dt {| RT.c_sx := 3 * k; RT.c_bw := b |}
  = Some {| RT.c_sx := 3 * N; RT.c_bw := rt_sbs b (OvKit.cb_calls_from s0 lfc ldl dfc ddl k (Z.to_nat (N - k))) |}.
Proof.
  induction f as [|f IH]; intros k b Hk Hf; [lia|].
  cbn [RT.cb_loop]. rewrite cb_step_eq. cbv zeta. cbn [RT.c_sx RT.c_bw].
  replace (Z.to_nat (N - k)) with (S (Z.to_nat (N - (k + 1)))) by lia. cbn [OvKit.cb_calls_from].
  rewrite rt_sbs_app, sym_calls_rt by exact Hk.
  destruct (Z.ltb_spec (3 * k + 3) (3 * N)) as [Lt|Ge].
  - replace (3 * k + 3) with (3 * (k + 1)) by lia. apply IH; lia.
  - replace (Z.to_nat (N - (k + 1))) with 0%nat by lia. cbn [OvKit.cb_calls_from rt_sbs].
    replace (3 * k + 3) with (3 * N) by lia. reflexivity.
Qed.

Theorem cb_all_rt : forall b, 0 <= N ->
  rt_sbs b (OvKit.cb_all s0 lfc ldl dfc ddl N) = RT.compress_block sym (3 * N) lt dt b.
Proof.
  intros b HN. unfold OvKit.cb_all, OvKit.cb_calls, RT.compress_block. rewrite rt_sbs_app.
  assert (EE : rt_sbs (rt_sbs b (OvKit.cb_calls_from s0 lfc ldl dfc ddl 0 (Z.to_nat N)))
                      [(arr_get lfc DS.END_BLOCK, arr_get ldl DS.END_BLOCK)]
               = RT.send_code RT.END_BLOCK lt (rt_sbs b (OvKit.cb_calls_from s0 lfc ldl dfc ddl 0 (Z.to_nat N)))).
  { cbn [rt_sbs]. unfold RT.send_code, RT.t_code, RT.t_len.
    rewrite (Hlfc DS.END_BLOCK), (Hldl DS.END_BLOCK) by (unfold DS.END_BLOCK; lia). reflexivity. }
  rewrite EE. f_equal.
  destruct (Z.eqb_spec (3 * N) 0) as [Z0|NZ].
  - replace (Z.to_nat N) with 0%nat by lia. reflexivity.
  - pose proof (cb_loop_rt (Z.to_nat (3 * N) + 1) 0 b ltac:(lia) ltac:(lia)) as E.
    replace (3 * 0) with 0 in E by lia. replace (N - 0) with N in E by lia.
    rewrite E. reflexivity.
Qed.

End Sym.

(* ------------------------------------------------------------------------- *)
(* 3.  The block body as a pair                                              *)
(* ------------------------------------------------------------------------- *)

(** S5's block body (the pristine calls, [sbs_run]) against RT's
    [compress_block], under S5's room for the whole run ([sbs_ok]). *)
Theorem br_cb_body : forall y b s0 lfc ldl dfc ddl lt dt (sym : Base.zarr) N,
  bw_rel y b -> DS.ds_pending_out y = 0 -> 0 <= N ->
  (forall i, 0 <= i < 3 * N -> DS.sym_buf_get s0 i = sym i) ->
  (forall j, 0 <= j < N -> DO.sym_okb s0 j) ->
  arr_rel lfc (RT.tr_fc lt) 0 286 -> arr_rel ldl (RT.tr_dl lt) 0 286 ->
  arr_rel dfc (RT.tr_fc dt) 0 30 -> arr_rel ddl (RT.tr_dl dt) 0 30 ->
  SM.sbs_ok (arr_len (DS.ds_pending_buf y)) y (OvKit.cb_all s0 lfc ldl dfc ddl N) ->
  bw_rel (SM.sbs_run y (OvKit.cb_all s0 lfc ldl dfc ddl N)) (RT.compress_block sym (3 * N) lt dt b)
  /\ DS.ds_pending_out (SM.sbs_run y (OvKit.cb_all s0 lfc ldl dfc ddl N)) = 0
  /\ arr_len (DS.ds_pending_buf (SM.sbs_run y (OvKit.cb_all s0 lfc ldl dfc ddl N))) = arr_len (DS.ds_pending_buf y).
Proof.
  intros y b s0 lfc ldl dfc ddl lt dt sym N Hb Hpo HN Hsym Hok H1 H2 H3 H4 Hsbs.
  rewrite <- (cb_all_rt s0 lfc ldl dfc ddl lt dt sym N Hsym Hok H1 H2 H3 H4 b HN).
  exact (br_sbs_run _ y b Hb Hpo Hsbs).
Qed.

Print Assumptions br_cb_body.
