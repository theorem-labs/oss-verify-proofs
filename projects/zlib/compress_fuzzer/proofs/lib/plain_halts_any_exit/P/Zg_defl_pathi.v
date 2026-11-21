(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay RefDeflSlow6 RefDeflSafeS.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel RefDeflSafeG RefDeflSafeFB RefDeflSafeLF RefDeflSafeF RefDeflSafeL0 RefDeflSafeL5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI3 RefDeflSafeI4 RefDeflSafeI6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel FlushBlockModel RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflFast6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BoundFw BoundSlow BoundPat.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_defl_model Z_defl_path Zg_defl_path.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Record PATG (s : deflate_state) : Prop := {
  pg_mode : dmode s = 0 \/ dmode s = 4;
  pg_strat : ds_strategy s = 0 \/ ds_strategy s = 1;
  pg_wrap : ds_wrap s = 1 \/ (ds_wrap s = -1 /\ ds_status s = FINISH_STATE);
  pg_st : ds_status s = INIT_STATE \/ ds_status s = BUSY_STATE \/ ds_status s = FINISH_STATE }.

Lemma keeps_CF : keeps CF true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.

Lemma CF_read_buf : forall s dst n, CF (fst (read_buf s dst n)) = CF s.
Proof. intros s dst n. apply CF_split; [apply CF4_read_buf | apply fwT_read_buf]. Qed.

Lemma CF_rdo : forall x len, CF (st_rdo x len) = CF x.
Proof.
  intros x len. unfold st_rdo. destruct (negb (len =? 0)); [|reflexivity].
  pose proof (CF_read_buf x RB_next_out len) as H.
  destruct (read_buf x RB_next_out len) as [x' k]. cbn [fst] in H. etransitivity; [|exact H]. reflexivity.
Qed.

Lemma CF_copy : forall x left len, CF (fst (st_copy x left len)) = CF x.
Proof. intros x left len. unfold st_copy. destruct (negb (left =? 0)); reflexivity. Qed.

Lemma CF_emit1 : forall x fl, CF (st_emit1 x fl) = CF x.
Proof.
  intros x fl. unfold st_emit1. rewrite CF_flush_pending. unfold sb_patch. cbv zeta.
  rewrite (k_pending_buf CF true true keeps_CF eq_refl). apply (k_tr_stored_block CF true true keeps_CF eq_refl).
Qed.

Lemma CF_trip : forall s flush, CF (st_trip s flush) = CF s.
Proof. intros s flush. unfold st_trip. rewrite CF_rdo, CF_copy. apply CF_emit1. Qed.

Lemma CF_sloop : forall fuel s flush mb, CF (fst (deflate_stored_loop fuel s flush mb)) = CF s.
Proof.
  induction fuel as [|f IH]; intros s flush mb; [reflexivity|].
  rewrite sloop_S'. destruct (sb_broke s flush mb); [reflexivity|].
  destruct (sb_lastv s flush =? 0); [rewrite IH|cbn [fst]]; apply CF_trip.
Qed.

Lemma CF_hw : forall s, CF (hw_st s) = CF s.
Proof. intros s. unfold hw_st. destruct (_ <? _); reflexivity. Qed.

Lemma CF_wupd : forall s used, CF (st_wupd s used) = CF s.
Proof.
  intros s used. unfold st_wupd.
  destruct (negb (used =? 0)); [|reflexivity].
  destruct (ds_w_size s <=? used); [reflexivity|].
  destruct (ds_window_size s - ds_strstart s <=? used); [|reflexivity].
  dsred. destruct (ds_matches s <? 2); dsred; destruct (ds_strstart s - ds_w_size s <? ds_insert s); dsred; reflexivity.
Qed.

Lemma CF_slide3 : forall s have, CF (fst (st_slide3 s have)) = CF s.
Proof.
  intros s have. unfold st_slide3. destruct (_ && _); cbn [fst]; [|reflexivity].
  dsred. destruct (ds_matches s <? 2); dsred; destruct (ds_strstart s - ds_w_size s <? ds_insert s); dsred; reflexivity.
Qed.

Lemma CF_fillw : forall s have, CF (st_fillw s have) = CF s.
Proof.
  intros s have. unfold st_fillw. destruct (negb (have =? 0)); [|reflexivity].
  pose proof (CF_read_buf s (RB_window (ds_strstart s)) have) as ER.
  destruct (read_buf s (RB_window (ds_strstart s)) have) as [x k]. cbn [fst] in ER.
  etransitivity; [|exact ER]. reflexivity.
Qed.

Lemma CF_final : forall s flush, CF (fst (st_final s flush)) = CF s.
Proof.
  intros s flush. unfold st_final. cbv zeta. destruct (_ || _); [|reflexivity]. cbn [fst].
  rewrite CF_flush_pending. etransitivity; [|apply (k_tr_stored_block CF true true keeps_CF eq_refl)]. reflexivity.
Qed.

Lemma st_final_bstate : forall s flush, snd (st_final s flush) = finish_started \/ snd (st_final s flush) = need_more.
Proof.
  intros s flush. unfold st_final. cbv zeta. destruct (_ || _); cbn [snd]; [|right; reflexivity].
  destruct (negb (_ =? 0)); [left | right]; reflexivity.
Qed.

Theorem CF_stored : forall s flush, CF (fst (deflate_stored s flush)) = CF s.
Proof.
  intros s flush. rewrite deflate_stored_eq. cbv zeta.
  generalize (fst (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm s) + 1)) s flush (wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s)))))
    (CF_sloop (Z.to_nat (cs_avail_out (ds_strm s) + 1)) s flush (wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s)))).
  generalize (snd (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm s) + 1)) s flush (wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s))))).
  intros last sL EL.
  destruct (negb (last =? 0)); [cbn [fst]; rewrite CF_hw, CF_wupd; exact EL|].
  destruct (_ && _); [cbn [fst]; rewrite CF_hw, CF_wupd; exact EL|].
  rewrite CF_final, CF_hw, CF_fillw, CF_slide3, CF_hw, CF_wupd. exact EL.
Qed.

Theorem sto_bstate : forall s flush, snd (deflate_stored s flush) = block_done -> flush <> Z_NO_FLUSH /\ flush <> Z_FINISH.
Proof.
  intros s flush. rewrite deflate_stored_eq. cbv zeta.
  generalize (fst (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm s) + 1)) s flush (wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s))))).
  generalize (snd (deflate_stored_loop (Z.to_nat (cs_avail_out (ds_strm s) + 1)) s flush (wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s))))).
  intros last sL.
  destruct (negb (last =? 0)); [cbn [snd]; intros E; discriminate E|].
  match goal with |- context [st_final ?a flush] => pose proof (st_final_bstate a flush) as SB; revert SB; generalize (st_final a flush) end.
  intros [u b] SB. cbn [snd] in SB.
  match goal with |- context [if ?c then (_, block_done) else _] => destruct c eqn:C end.
  - cbn [snd]. intros _. apply andb_prop in C as [C _]. apply andb_prop in C as [C _]. apply andb_prop in C as [C1 C2].
    split; intros F; rewrite F in C1, C2; cbn in C1, C2; first [discriminate C1 | discriminate C2].
  - cbn [snd]. intros E. exfalso. destruct SB as [SB|SB]; rewrite SB in E; discriminate E.
Qed.

Theorem slow_frames5 : forall c0 s flush, FB_CALL -> BFPRE c0 s flush -> dmode s = 4 -> ds_w_size s = 32768 ->
  flush = Z_NO_FLUSH \/ flush = Z_FINISH \/ flush = Z_BLOCK ->
  let r := deflate_slow s flush in
  CF (fst r) = CF s /\ (snd r = block_done -> flush = Z_BLOCK).
Proof.
  intros c0 s flush HFB (HC0 & HDC & Hp & Hst & Hfl) Hm HW HFL.
  assert (HF : STI c0 s s).
  { split; [exact HDC|]. split; [reflexivity|]. split; [exact Hp|]. split; [exact Hm|]. split; [exact Hst | apply OUTLE_refl]. }
  pose proof HDC as [[D X] V].
  assert (Hmz : 0 <= lz_meas s) by (unfold lz_meas; pose proof (df_look _ D); pose proof (sv_ain _ _ V); lia).
  destruct (sloop c0 s flush HC0 HFB (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as [_ HR].
  pose proof (loop_noflush_some c0 s flush HC0 HFB (lz_fuel s) s) as NS.
  pose proof (cfloop c0 s flush HC0 HFB (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as CL.
  cbv zeta. rewrite deflate_slow_eq.
  set (lp := deflate_slow_loop (lz_fuel s) s flush) in *. clearbody lp. destruct lp as [s1 o]. cbn [fst snd] in *.
  destruct o as [bs|].
  - cbn [fst snd]. destruct HR as (_ & _ & _ & ->). split; [exact CL| intros HH; discriminate HH].
  - destruct HFL as [F0|F45]; [exfalso; exact (NS F0 HF (lz_fuel_meas s Hmz) eq_refl)|].
    assert (CU' : CF (if negb (ds_match_available s1 =? 0) then break1_st s1 else s1) = CF s)
      by (destruct (negb _); [rewrite CF_break1|]; exact CL).
    cbv zeta.
    set (u := if negb (ds_match_available s1 =? 0) then break1_st s1 else s1) in *. clearbody u.
    destruct F45 as [F4|F5]; subst flush.
    + destruct (deflate_tail_finish (tail_st u)) as (E1 & E2 & E3).
      rewrite E1. split; [rewrite CF_flush_block_only, CF_tail_st; exact CU'|].
      intros HH. exfalso. rewrite HH in E3. destruct E3 as [E3|E3]; discriminate E3.
    + unfold deflate_tail. change (Z_BLOCK =? Z_FINISH) with false. cbv iota.
      destruct (negb (ds_sym_next (tail_st u) =? 0)).
      * rewrite flush_block_eq'. destruct (cs_avail_out _ =? 0); cbn [fst snd negb Z.eqb].
        -- split; [rewrite CF_flush_block_only, CF_tail_st; exact CU'| intros HH; discriminate HH].
        -- split; [rewrite CF_flush_block_only, CF_tail_st; exact CU'| intros _; reflexivity].
      * cbn [fst snd]. split; [rewrite CF_tail_st; exact CU'| intros _; reflexivity].
Qed.

Lemma fwT_of_CF : forall a b, CF b = CF a -> fwT b = fwT a.
Proof. intros a b E. exact (proj2 (proj2 (proj2 (proj2 (CF_fields _ _ E))))). Qed.

Lemma fwT_put_byte : forall u c, fwT (put_byte u c) = fwT u. Proof. reflexivity. Qed.
Lemma fwT_putShortMSB : forall u h, fwT (putShortMSB u h) = fwT u.
Proof. intros u h. unfold putShortMSB. rewrite !fwT_put_byte. reflexivity. Qed.

Lemma fwT_zhdr_g : forall s, fwT (zhdr_st s) = fwT s.
Proof.
  intros s. unfold zhdr_st. cbv zeta.
  match goal with |- context [putShortMSB s ?hd] => generalize hd end. intros hdr.
  destruct (negb (ds_strstart (putShortMSB s hdr) =? 0)).
  - etransitivity; [| exact (fwT_putShortMSB s hdr)].
    etransitivity; [| exact (fwT_putShortMSB (putShortMSB s hdr) (wrap32 (Z.shiftr (cs_adler (ds_strm (putShortMSB s hdr))) 16)))].
    etransitivity; [| exact (fwT_putShortMSB _ (Z.land (cs_adler (ds_strm (putShortMSB s hdr))) 65535))].
    reflexivity.
  - etransitivity; [| exact (fwT_putShortMSB s hdr)]. reflexivity.
Qed.

Section PathProofG.
  Variables (inp : list Z) (flush : Z).
  Variable c0 : cstrm.
  Variable s0 : deflate_state.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis Hs0 : ds_strm s0 = c0.
  Hypothesis D0 : dwf s0.
  Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH \/ flush = Z_BLOCK.
  Hypothesis HAO : cs_avail_out c0 < 2^31.
  Hypothesis HIN : cs_input c0 = arr_of_list inp.
  Hypothesis HIL : zlength inp < 2^31.
  Hypothesis HIB : Forall (fun b => 0 <= b < 256) inp.
  Hypothesis HWS : ds_w_size s0 = 32768.
  Hypothesis HHS : ds_hash_size s0 = 32768.
  Hypothesis HLBS : ds_lit_bufsize s0 = 16384.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.
  Local Abbreviation ST := (RefDeflSafeI4.ST c0 s0).

  Definition P2g (s : deflate_state) : Prop := ST s /\ PATG s.

End PathProofG.

Section Api.
  Variables (ds : deflate_state) (zc : ZCall) (flush : Z).
  Hypothesis HDD : DD ds.
  Hypothesis Hzc : dcall_wf zc.
  Hypothesis P : PATG ds.
  Hypothesis HWS : ds_w_size ds = 32768.
  Hypothesis HHS : ds_hash_size ds = 32768.
  Hypothesis HLBS : ds_lit_bufsize ds = 16384.
  Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH \/ flush = Z_BLOCK.
  Hypothesis HIL : zlength (zc_input zc) < 2^31.
  Hypothesis HAO : zc_avail_out zc < 2^31.

  Let c0 := cstrm_of_call zc.
  Let d0 := set_strm ds c0.

End Api.

