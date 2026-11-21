(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay RefDeflSlow6 RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateRel RefDeflSafeG RefDeflSafeFB RefDeflSafeLF RefDeflSafeF RefDeflSafeL0 RefDeflSafeL5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI3 RefDeflSafeI4 RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel FlushBlockModel RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflFast6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BoundFw BoundSlow BoundPat.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_defl_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_defl_iface Z_defl_path Zg_defl_path.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Record PATG (s : deflate_state) : Prop := {
  pg_mode : dmode s = 0 \/ dmode s = 4;
  pg_strat : ds_strategy s = 0 \/ ds_strategy s = 1;
  pg_wrap : ds_wrap s = 1 \/ (ds_wrap s = -1 /\ ds_status s = FINISH_STATE);
  pg_st : ds_status s = INIT_STATE \/ ds_status s = BUSY_STATE \/ ds_status s = FINISH_STATE }.

Lemma CF4_fields : forall a b, CF4 b = CF4 a ->
  ds_level b = ds_level a /\ ds_strategy b = ds_strategy a /\ ds_wrap b = ds_wrap a /\ ds_status b = ds_status a.
Proof. intros a b E. unfold CF4 in E. injection E as E1 E2 E3 E4. auto. Qed.

Lemma dmode_CF4 : forall a b, CF4 b = CF4 a -> dmode b = dmode a.
Proof. intros a b E. destruct (CF4_fields a b E) as (E1 & E2 & _). unfold dmode. rewrite E1, E2. reflexivity. Qed.

Lemma PATG_CF4 : forall a b, CF4 b = CF4 a -> PATG a -> PATG b.
Proof.
  intros a b E [P1 P2 P3 P4]. destruct (CF4_fields a b E) as (E1 & E2 & E3 & E4).
  constructor; rewrite ?(dmode_CF4 a b E), ?E2, ?E3, ?E4; assumption.
Qed.

Lemma CF4_of_CF : forall a b, CF b = CF a -> CF4 b = CF4 a.
Proof. intros a b E. destruct (CF_fields a b E) as (E1 & E2 & E3 & E4 & _). unfold CF4. rewrite E1, E2, E3, E4. reflexivity. Qed.

Lemma PATG_CF : forall a b, CF b = CF a -> PATG a -> PATG b.
Proof. intros a b E P. exact (PATG_CF4 a b (CF4_of_CF a b E) P). Qed.

Lemma PATG_slf : forall s v, PATG s -> PATG (set_last_flush s v).
Proof. intros s v [P1 P2 P3 P4]. constructor; assumption. Qed.
Lemma PATG_set_strm : forall s c, PATG s -> PATG (set_strm s c).
Proof. intros s c [P1 P2 P3 P4]. constructor; assumption. Qed.
Lemma PATG_err : forall s e, PATG s -> PATG (fst (err_return s e)).
Proof. intros s e P. rewrite err_return_fst. apply PATG_set_strm. exact P. Qed.
Lemma PATG_busy : forall s, PATG s -> ds_status s = INIT_STATE -> PATG (set_status s BUSY_STATE).
Proof.
  intros s [P1 P2 P3 P4] E.
  assert (W : ds_wrap s = 1) by (destruct P3 as [W|[_ F]]; [exact W | rewrite E in F; discriminate F]).
  constructor; try assumption. - left. exact W. - right. left. reflexivity.
Qed.
Lemma PATG_finish : forall s, PATG s -> ds_status s <> FINISH_STATE -> PATG (set_status s FINISH_STATE).
Proof.
  intros s [P1 P2 P3 P4] N.
  assert (W : ds_wrap s = 1) by (destruct P3 as [W|[_ F]]; [exact W | contradiction]).
  constructor; try assumption. - left. exact W. - right. right. reflexivity.
Qed.
Lemma PATG_wrapneg : forall s, PATG s -> ds_status s = FINISH_STATE -> PATG (set_wrap s (-1)).
Proof. intros s [P1 P2 P3 P4] F. constructor; try assumption. right. split; [reflexivity | exact F]. Qed.

Lemma PATG_level : forall s, dwf s -> PATG s -> ds_level s = 0 \/ 4 <= ds_level s <= 9.
Proof.
  intros s D P. pose proof (df_level _ D) as L. destruct (pg_mode _ P) as [M|M]; unfold dmode in M.
  - destruct (Z.eqb_spec (ds_level s) 0) as [E|E]; [left; exact E|].
    exfalso. destruct (ds_strategy s =? Z_HUFFMAN_ONLY); [discriminate M|]. destruct (ds_strategy s =? Z_RLE); [discriminate M|].
    destruct (ds_level s <=? 3); discriminate M.
  - destruct (Z.eqb_spec (ds_level s) 0) as [E|E]; [discriminate M|].
    destruct (ds_strategy s =? Z_HUFFMAN_ONLY); [discriminate M|]. destruct (ds_strategy s =? Z_RLE); [discriminate M|].
    destruct (Z.leb_spec (ds_level s) 3) as [E3|E3]; [discriminate M|]. right. lia.
Qed.

Lemma PATG_strategy : forall s, PATG s -> 0 <= ds_strategy s <= 1.
Proof. intros s P. destruct (pg_strat _ P) as [E|E]; rewrite E; lia. Qed.

Lemma PATG_wrap2 : forall s, PATG s -> ds_wrap s <> 2.
Proof. intros s P. destruct (pg_wrap _ P) as [W|[W _]]; rewrite W; discriminate. Qed.
Lemma PATG_wrap0 : forall s, PATG s -> ds_wrap s <> 0 /\ - 2 <= ds_wrap s <= 2.
Proof. intros s P. destruct (pg_wrap _ P) as [W|[W _]]; rewrite W; lia. Qed.


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


Lemma PATG_PF : forall a b, PF b = PF a -> PATG a -> PATG b.
Proof.
  intros a b E P.
  pose proof (PF_fields _ _ E) as ((_ & _ & _ & _ & El & Es) & (_ & _ & _ & _ & _ & _ & _ & Ew) & (Est & _) & _).
  apply (PATG_CF4 a b); [| exact P]. unfold CF4. rewrite El, Es, Ew, Est. reflexivity.
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

Lemma dblk_run : forall X flush, PATG X ->
  run_compress_func X flush = dblk X flush /\ (dmode X = 0 <-> ds_level X = 0).
Proof.
  intros X flush P. rewrite run_compress_func_dmode. unfold dblk.
  assert (IFF : dmode X = 0 <-> ds_level X = 0).
  { unfold dmode. destruct (Z.eqb_spec (ds_level X) 0) as [E|E]; [tauto|].
    split; [| intros C; contradiction]. intros M. exfalso.
    destruct (ds_strategy X =? Z_HUFFMAN_ONLY); [discriminate M|]. destruct (ds_strategy X =? Z_RLE); [discriminate M|].
    destruct (ds_level X <=? 3); discriminate M. }
  split; [| exact IFF].
  destruct (pg_mode _ P) as [M|M]; rewrite M.
  - replace (ds_level X =? 0) with true by (symmetry; apply Z.eqb_eq; apply IFF; exact M). reflexivity.
  - replace (ds_level X =? 0) with false; [reflexivity|]. symmetry. apply Z.eqb_neq. intros C. apply IFF in C. rewrite M in C. discriminate C.
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

  Lemma Hfl5 : 0 <= flush <= 5.
  Proof. destruct HFL as [-> | [-> | ->]]; unfold Z_NO_FLUSH, Z_FINISH, Z_BLOCK; lia. Qed.

  Lemma P2g_slf : forall s v, P2g s -> - 2 <= v <= 5 -> P2g (set_last_flush s v).
  Proof. intros s v [H P] Hv. split; [exact (ST_set_last_flush c0 s0 s v H Hv) | exact (PATG_slf s v P)]. Qed.
  Lemma P2g_err : forall s e, P2g s -> P2g (fst (err_return s e)).
  Proof. intros s e [H P]. split; [exact (ST_err_return c0 s0 s e H) | exact (PATG_err s e P)]. Qed.
  Lemma P2g_fp : forall s, P2g s -> P2g (flush_pending s) /\ (ds_pending (flush_pending s) = 0 \/ cs_avail_out (ds_strm (flush_pending s)) = 0).
  Proof.
    intros s [H P]. destruct (ST_flush_pending c0 s0 HC0 s H) as (H' & _ & Hor & _).
    split; [split; [exact H' | exact (PATG_CF _ _ (CF_flush_pending s) P)] | exact Hor].
  Qed.

  Lemma P2g_facts : forall X, P2g X ->
    0 <= cs_avail_in (ds_strm X) < 2^31 /\ 0 <= cs_avail_out (ds_strm X) < 2^31 /\ din_tieg inp X
    /\ ds_hash_size X = 32768 /\ ds_w_bits X = 15 /\ 0 <= ds_lookahead X < 2^31 /\ 0 <= ds_strstart X < 2^31
    /\ ds_w_size X = 32768 /\ ds_lit_bufsize X = 16384.
  Proof.
    intros X [[[[D XX] V] K] P].
    pose proof (sv_ain _ _ V) as A1. pose proof (sv_inlen _ _ V) as A2. pose proof (sv_nin _ _ V) as A3.
    rewrite HIN, arr_len_of_list in A2. unfold zlength in HIL, A2.
    pose proof (sv_out _ _ V) as O1. pose proof (sv_aout _ _ V) as O2. rewrite (c0_out _ HC0w) in O1. unfold zlen in O1. cbn [length Z.of_nat] in O1.
    pose proof (KV_fields _ _ K) as (Kw & Kh & Kl & _). rewrite HWS in Kw. rewrite HHS in Kh. rewrite HLBS in Kl.
    pose proof (df_wsize _ D) as E1. pose proof (df_wbits _ D) as Rw. rewrite Kw in E1.
    assert (WB : ds_w_bits X = 15) by (symmetry; apply pow2_inj_small; [lia | lia | exact E1]).
    pose proof (df_look _ D) as L1. pose proof (df_sl _ D) as L2. pose proof (df_strstart _ D) as L3. rewrite Kw in L2.
    split; [lia|]. split; [lia|]. split; [split; [rewrite (sv_input _ _ V); exact HIN| exact HIB]|].
    split; [exact Kh|]. split; [exact WB|]. split; [lia|]. split; [lia|]. split; [exact Kw| exact Kl].
  Qed.

  Lemma fin_pathg_ok : forall X, P2g X -> ds_pending X = 0 -> (flush = Z_FINISH -> ds_status X = FINISH_STATE) ->
    fin_path flush (dc_fin X flush) X.
  Proof.
    intros X PP Hp Hfin. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    pose proof (df_wrap _ D) as RW.
    pose proof (PATG_wrap2 X P) as W2. pose proof (PATG_wrap0 X P) as [W0 WRG].
    destruct (P2g_facts X PP) as (_ & RAO & _ & _ & _ & _ & _ & _ & LBS).
    destruct (trailer_facts c0 X H Hp) as ((H1 & Po1 & P1) & K1 & O1 & St1 & Wr1 & Lk1).
    assert (HS1 : ST (trailer_st X)) by (split; [exact H1| rewrite K1; exact K]).
    destruct (ST_flush_pending c0 s0 HC0 (trailer_st X) HS1) as (HS2 & Hfp & Hor & Hp2 & St2 & Wr2 & Lk2 & Ai2).
    destruct (DC_flush_pending c0 (trailer_st X) HC0w H1) as (_ & _ & O2 & _).
    pose proof HS2 as [[[D2 _] _] _]. pose proof (df_pend _ D2) as Pd2. pose proof (dwf_sizes _ D2) as (_ & _ & Sl2 & _).
    pose proof (sv_adler _ _ V) as RAD.
    rewrite (trailer_st_put_adler X W2) in *.
    unfold fin_path, dc_fin.
    destruct (Z.eq_dec flush Z_FINISH) as [F4|NF4].
    2:{ replace (negb (flush =? Z_FINISH)) with true by (symmetry; destruct (Z.eqb_spec flush Z_FINISH); [contradiction| reflexivity]). cbv iota.
        split; [apply ole_strm; reflexivity|]. split; [exact RW|]. split; [exact W2|].
        split; [intros _; reflexivity|]. split; [intros F4; contradiction|]. intros F4; contradiction. }
    rewrite F4. change (negb (Z_FINISH =? Z_FINISH)) with false. cbv iota.
    split.
    {
      destruct (ds_wrap X <=? 0); [apply ole_strm; reflexivity|].
      rewrite deflate_trailer_eq, (trailer_st_put_adler X W2). cbv zeta.
      apply (ole_step _ X (flush_pending (put_adler X))); [exact (OUTLE_trans _ _ _ O1 O2)| rewrite fwT_flush_pending; apply fwT_put_adler|].
      generalize (flush_pending (put_adler X)). intros s2. apply ole_strm. cbn [fst]. destruct (0 <? ds_wrap s2); [apply strm_set_wrap| reflexivity]. }
    split; [exact RW|]. split; [exact W2|].
    split; [intros C; contradiction|].
    split.
    { intros _ WN. replace (ds_wrap X <=? 0) with true by (symmetry; apply Z.leb_le; exact WN). reflexivity. }
    intros _ WP. cbv zeta.
    split; [lia|]. split; [lia|]. split; [exact RAD|]. split; [exact LBS|]. split; [exact RAO|]. split; [exact Hfp|].
    split; [rewrite Wr2; exact Wr1|]. split; [lia|].
    replace (ds_wrap X <=? 0) with false by (symmetry; apply Z.leb_gt; exact WP).
    rewrite deflate_trailer_eq, (trailer_st_put_adler X W2). cbv zeta.
    assert (W2' : 0 < ds_wrap (flush_pending (put_adler X))) by (rewrite Wr2, Wr1; exact WP).
    revert W2'. generalize (flush_pending (put_adler X)). intros s2 W2'.
    replace (0 <? ds_wrap s2) with true by (symmetry; apply Z.ltb_lt; exact W2').
    rewrite pending_set_wrap.
    split; [apply ole_strm; apply strm_set_wrap|]. split.
    - intros E. rewrite E. reflexivity.
    - intros E. replace (ds_pending s2 =? 0) with false by (symmetry; apply Z.eqb_neq; exact E). reflexivity.
  Qed.

  Lemma bf_g : forall X, P2g X -> ds_pending X = 0 -> ds_status X <> FINISH_STATE ->
    let r := dblk X flush in
    run_compress_func X flush = r
    /\ BFPOST c0 X flush r /\ CF (fst r) = CF X /\ (snd r = block_done -> flush = Z_BLOCK)
    /\ (ds_level X = 0 -> st_entry X /\ ds_pending_buf_size X = 65536)
    /\ (ds_level X <> 0 -> slow_safe X flush /\ Z_defl_iface.sbs_ok (lz_fuel X) X flush /\ slow_fe X flush).
  Proof.
    intros X PP Hp Hst0. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    destruct (P2g_facts X PP) as (_ & _ & _ & _ & _ & _ & _ & WS & LBS).
    destruct (dblk_run X flush P) as [ER IFF].
    assert (PRE : BFPRE c0 X flush) by (split; [exact HC0|]; split; [exact H|]; split; [exact Hp|]; split; [exact Hst0 | exact Hfl5]).
    cbv zeta. rewrite <- ER. rewrite run_compress_func_dmode.
    destruct (pg_mode _ P) as [M|M]; rewrite M.
    -
      destruct (stored_bf_spec c0 X flush PRE M) as [_ POST].
      assert (L0 : ds_level X = 0) by (apply IFF; exact M).
      split; [reflexivity|]. split; [exact POST|]. split; [apply CF_stored|].
      split.
      { intros BD. destruct (sto_bstate X flush BD) as [N0 N4]. destruct HFL as [F|[F|F]]; [contradiction| contradiction| exact F]. }
      split; [| intros C; contradiction].
      intros _. split.
      + apply (SI_st_entry c0 X HC0 X). split; [exact H|]. split; [reflexivity|]. split; [exact M|]. split; [exact Hst0|]. split; [apply OUTLE_refl| exact Hp].
      + rewrite (df_pbs _ D), LBS. reflexivity.
    -
      destruct (slow_bf_spec FB_CALL_ok c0 X flush PRE M) as [SAFE POST].
      assert (LN : ds_level X <> 0) by (intros C; apply IFF in C; rewrite M in C; discriminate C).
      pose proof (slow_frames5 c0 X flush FB_CALL_ok PRE M WS HFL) as [ECF BD]. 
      split; [reflexivity|]. split; [exact POST|]. split; [exact ECF|]. split; [exact BD|].
      split; [intros C; contradiction| intros _].
      assert (HF : RefDeflSafeL5.STI c0 X X).
      { split; [exact H|]. split; [reflexivity|]. split; [exact Hp|]. split; [exact M|]. split; [exact Hst0 | apply OUTLE_refl]. }
      split; [exact SAFE|]. split; [exact (sbs_of_STI c0 X flush HC0 (lz_fuel X) X HF)| exact (slow_fe_of_STI c0 X flush HC0 X HF)].
  Qed.

  Lemma deflate_blocks_unfold : forall X,
    deflate_blocks X flush =
      if blk_cond X flush then
        (let '(s, bstate) := run_compress_func X flush in
         let s := if block_state_eqb bstate finish_started || block_state_eqb bstate finish_done then set_status s FINISH_STATE else s in
         if block_state_eqb bstate need_more || block_state_eqb bstate finish_started then
           (if Z.eqb (cs_avail_out (ds_strm s)) 0 then set_last_flush s (-1) else s, Some Z_OK)
         else if block_state_eqb bstate block_done then
           (let s' := if Z.eqb flush Z_PARTIAL_FLUSH then tr_align s
                      else if negb (Z.eqb flush Z_BLOCK) then
                        let s := tr_stored_block s None 0 0 in
                        if Z.eqb flush Z_FULL_FLUSH then
                          let s := clear_hash s in
                          if Z.eqb (ds_lookahead s) 0 then set_insert (set_block_start (set_strstart s 0) 0) 0 else s
                        else s
                      else s in
            let s' := flush_pending s' in
            if Z.eqb (cs_avail_out (ds_strm s')) 0 then (set_last_flush s' (-1), Some Z_OK) else (s', None))
         else (s, None))
      else (X, None).
  Proof. intros X. reflexivity. Qed.

  Lemma P2g_blocks : forall X, P2g X -> ds_pending X = 0 ->
    (ds_status X = FINISH_STATE -> cs_avail_in (ds_strm X) = 0) ->
    let r := deflate_blocks X flush in
    P2g (fst r) /\ (snd r = None -> ds_pending (fst r) = 0 /\ (flush = Z_FINISH -> ds_status (fst r) = FINISH_STATE)).
  Proof.
    intros X PP Hp Hfin. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    rewrite deflate_blocks_unfold.
    destruct (blk_cond X flush) eqn:Hcond.
    2:{ cbn [fst snd]. split; [exact PP|]. intros _. split; [exact Hp|]. intros Hf.
        unfold blk_cond in Hcond. apply orb_false_iff in Hcond as [Hcond C3]. apply andb_false_iff in C3. destruct C3 as [C3|C3].
        - exfalso. rewrite Hf in C3. cbn in C3. discriminate C3.
        - destruct (Z.eqb_spec (ds_status X) FINISH_STATE); [assumption | discriminate C3]. }
    assert (Hst0 : ds_status X <> FINISH_STATE).
    { intros Ef. unfold blk_cond in Hcond. rewrite (Hfin Ef), (dx_fin _ XX Ef), Ef in Hcond. cbn in Hcond. rewrite andb_false_r in Hcond. discriminate Hcond. }
    clear Hcond.
    destruct (bf_g X PP Hp Hst0) as (ER & POST & ECF & BD & _). rewrite ER.
    revert POST ECF BD. generalize (dblk X flush). intros [s1 bst] POST ECF BD. cbn [fst snd] in POST, ECF, BD. cbv beta iota zeta.
    unfold BFPOST in POST. cbn [fst snd] in POST. destruct POST as (H1 & K1 & O1 & Pbd & Pfin & Pfd).
    assert (HS1 : ST s1) by (split; [exact H1 | rewrite K1; exact K]).
    pose proof (PATG_CF _ _ ECF P) as P1.
    assert (Est1 : ds_status s1 = ds_status X) by exact (proj1 (proj2 (proj2 (proj2 (CF_fields _ _ ECF))))).
    assert (P1f : PATG (set_status s1 FINISH_STATE)) by (apply PATG_finish; [exact P1| rewrite Est1; exact Hst0]).
    destruct bst; cbn [block_state_eqb orb]; cbv iota.
    -
      destruct (cs_avail_out (ds_strm s1) =? 0); cbn [fst snd].
      + split; [apply P2g_slf; [exact (conj HS1 P1) | lia] | intros E; discriminate E].
      + split; [exact (conj HS1 P1) | intros E; discriminate E].
    -
      pose proof (BD eq_refl) as F5. rewrite F5. change (Z_BLOCK =? Z_PARTIAL_FLUSH) with false. change (negb (Z_BLOCK =? Z_BLOCK)) with false. cbv iota.
      destruct (P2g_fp s1 (conj HS1 P1)) as [PPf Hor].
      destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_pending s1))) 0) as [Ea|Ea]; cbn [fst snd].
      + split; [apply P2g_slf; [exact PPf | lia] | intros E; discriminate E].
      + split; [exact PPf|]. intros _. split; [destruct Hor as [X0|X0]; [exact X0 | contradiction]|].
        intros F4. exfalso. unfold Z_FINISH, Z_BLOCK in F4. discriminate F4.
    -
      destruct (DC_set_status c0 s1 FINISH_STATE H1 ltac:(unfold FINISH_STATE; lia) ltac:(intros; reflexivity)
                  ltac:(intros _; exact (Pfin (or_introl eq_refl)))) as (H2 & K2 & S2).
      assert (HS2 : ST (set_status s1 FINISH_STATE)) by (split; [exact H2 | rewrite K2, K1; exact K]).
      revert HS2 P1f. generalize (set_status s1 FINISH_STATE). intros s2 HS2 PP2.
      destruct (cs_avail_out (ds_strm s2) =? 0); cbn [fst snd].
      + split; [apply P2g_slf; [exact (conj HS2 PP2) | lia] | intros E; discriminate E].
      + split; [exact (conj HS2 PP2) | intros E; discriminate E].
    -
      destruct (DC_set_status c0 s1 FINISH_STATE H1 ltac:(unfold FINISH_STATE; lia) ltac:(intros; reflexivity)
                  ltac:(intros _; exact (Pfin (or_intror eq_refl)))) as (H2 & K2 & S2).
      assert (HS2 : ST (set_status s1 FINISH_STATE)) by (split; [exact H2 | rewrite K2, K1; exact K]).
      assert (Pd2 : ds_pending (set_status s1 FINISH_STATE) = ds_pending s1) by reflexivity.
      assert (St2 : ds_status (set_status s1 FINISH_STATE) = FINISH_STATE) by reflexivity.
      revert HS2 P1f Pd2 St2. generalize (set_status s1 FINISH_STATE). intros s2 HS2 PP2 Pd2 St2.
      cbn [fst snd]. split; [exact (conj HS2 PP2)|]. intros _. split; [rewrite Pd2; exact (Pfd eq_refl) | intros _; exact St2].
  Qed.

  Lemma blocks_pathg_ok : forall X, P2g X -> ds_pending X = 0 -> (ds_status X = FINISH_STATE -> cs_avail_in (ds_strm X) = 0) ->
    blocks_pathg inp flush (dc_blocks X flush) X.
  Proof.
    intros X PP Hp Hfin. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    destruct (P2g_facts X PP) as (RAI & RAO & TIE & HSZ & WB & RLA & RSS & WS & LBS).
    assert (RST : 0 <= ds_status X < 1000) by (destruct (pg_st _ P) as [E|[E|E]]; rewrite E; unfold INIT_STATE, BUSY_STATE, FINISH_STATE; lia).
    pose proof (P2g_blocks X PP Hp Hfin) as PB. cbv zeta in PB.
    unfold blocks_pathg, dc_blocks.
    rewrite deflate_blocks_unfold in PB |- *.
    destruct (blk_cond X flush) eqn:Hcond.
    2:{
        cbn [fst snd] in PB. destruct PB as [_ PB2]. destruct (PB2 eq_refl) as [_ Hf].
        pose proof (fin_pathg_ok X PP Hp Hf) as FP.
        split; [exact (proj1 FP)|]. split; [exact RAI|]. split; [exact RLA|]. split; [exact RST|].
        split; [intros HH; discriminate HH| intros _; exact FP]. }
    assert (Hst0 : ds_status X <> FINISH_STATE).
    { intros Ef. unfold blk_cond in Hcond. rewrite (Hfin Ef), (dx_fin _ XX Ef), Ef in Hcond. cbn in Hcond. rewrite andb_false_r in Hcond. discriminate Hcond. }
    destruct (bf_g X PP Hp Hst0) as (ER & POST & ECF & BD & SAFE0 & SAFE4). rewrite ER in PB |- *.
    pose proof (PATG_level X D P) as LV. pose proof (PATG_strategy X P) as SG. pose proof (PATG_wrap2 X P) as W2. pose proof (PATG_wrap0 X P) as [W0 WRG].
    revert POST ECF BD PB. generalize (dblk X flush). intros [s1 bst] POST ECF BD PB.
    cbn [fst snd] in POST, ECF, BD, PB |- *. cbv beta iota zeta in PB |- *.
    unfold BFPOST in POST. cbn [fst snd] in POST. destruct POST as (H1 & K1 & O1 & Pbd & Pfin & Pfd).
    assert (HS1 : ST s1) by (split; [exact H1 | rewrite K1; exact K]).
    pose proof (PATG_CF _ _ ECF P) as P1. pose proof (fwT_of_CF _ _ ECF) as FT1.
    destruct (P2g_facts s1 (conj HS1 P1)) as (_ & RAO1 & _ & _ & _ & _ & _ & _ & LBS1).
    split.
    { apply (ole_step _ X s1 O1 FT1).
      destruct bst; cbn [block_state_eqb orb] in PB |- *; cbv iota in PB |- *.
      - apply ole_strm. destruct (cs_avail_out (ds_strm s1) =? 0); reflexivity.
      - rewrite (BD eq_refl). change (Z_BLOCK =? Z_PARTIAL_FLUSH) with false. change (negb (Z_BLOCK =? Z_BLOCK)) with false. cbv iota.
        destruct (DC_flush_pending c0 s1 HC0w H1) as (_ & _ & O2 & _).
        apply (ole_step _ s1 (flush_pending s1) O2 (fwT_flush_pending s1)).
        apply ole_strm. destruct (cs_avail_out (ds_strm (flush_pending s1)) =? 0); cbn [fst]; [apply strm_set_last_flush|].
        unfold dc_fin. change (negb (Z_BLOCK =? Z_FINISH)) with true. reflexivity.
      - apply ole_strm. rewrite strm_set_status. destruct (cs_avail_out (ds_strm s1) =? 0); reflexivity.
      - cbn [fst snd] in PB. destruct PB as [PP2 PB2]. destruct (PB2 eq_refl) as [Hp2 Hf2].
        exact (ole_step _ s1 (set_status s1 FINISH_STATE) (OUTLE_strm _ _ eq_refl) eq_refl (proj1 (fin_pathg_ok _ PP2 Hp2 Hf2))). }
    split; [exact RAI|]. split; [exact RLA|]. split; [exact RST|].
    split; [|intros HH; discriminate HH]. intros _.
    split; [exact LV|]. split; [exact SG|]. split; [exact TIE|].
    split; [exact WS|]. split; [exact HSZ|]. split; [exact LBS|]. split; [exact W2|]. split; [exact W0|]. split; [exact WRG|]. split; [exact RAO|].
    split; [exact SAFE0|]. split; [exact SAFE4|].
    destruct bst; cbn [block_state_eqb orb] in PB |- *; cbv iota in PB |- *.
    -
      split; [apply ole_strm; destruct (cs_avail_out (ds_strm s1) =? 0); reflexivity|].
      split; [exact RAO1|].
      split; [intros _ E; rewrite E; reflexivity|].
      split; [intros _ E; replace (cs_avail_out (ds_strm s1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact E); reflexivity|].
      split; [intros E; discriminate E|]. split; [intros E; discriminate E|]. split; [intros E; discriminate E|]. intros E; discriminate E.
    -
      pose proof (BD eq_refl) as F5. rewrite F5. change (Z_BLOCK =? Z_PARTIAL_FLUSH) with false. change (negb (Z_BLOCK =? Z_BLOCK)) with false. cbv iota.
      unfold dc_fin. change (negb (Z_BLOCK =? Z_FINISH)) with true. cbv iota.
      destruct (DC_flush_pending c0 s1 HC0w H1) as (_ & _ & O2 & _).
      destruct (ST_flush_pending c0 s0 HC0 s1 HS1) as (HSf & FPOK & _).
      pose proof (PATG_CF _ _ (CF_flush_pending s1) P1) as Pf.
      destruct (P2g_facts (flush_pending s1) (conj HSf Pf)) as (_ & RAOf & _).
      pose proof (df_wrap _ (proj1 (proj1 (proj1 HSf)))) as RWf. pose proof (PATG_wrap2 _ Pf) as W2f.
      split.
      { apply (ole_step _ s1 (flush_pending s1) O2 (fwT_flush_pending s1)). apply ole_strm.
        destruct (cs_avail_out (ds_strm (flush_pending s1)) =? 0); cbn [fst]; [apply strm_set_last_flush| reflexivity]. }
      split; [exact RAO1|].
      split; [intros E; discriminate E|]. split; [intros E; discriminate E|]. split; [intros E; discriminate E|]. split; [intros E; discriminate E|].
      split; [intros E; discriminate E|].
      intros _. split; [reflexivity|]. split; [exact FPOK|]. split; [exact LBS1|].
      revert RAOf RWf W2f. generalize (flush_pending s1). intros s2 RAOf RWf W2f.
      split; [apply ole_strm; destruct (cs_avail_out (ds_strm s2) =? 0); cbn [fst]; [apply strm_set_last_flush| reflexivity]|].
      split; [exact RAOf|].
      split; [intros E; rewrite E; reflexivity|].
      intros E. replace (cs_avail_out (ds_strm s2) =? 0) with false by (symmetry; apply Z.eqb_neq; exact E). cbn [fst].
      unfold fin_path. split; [apply ole_strm; reflexivity|]. split; [exact RWf|]. split; [exact W2f|].
      split; [intros _; reflexivity|]. split; [intros F4; discriminate F4|]. intros F4; discriminate F4.
    -
      rewrite ?strm_set_status. split; [apply ole_strm; destruct (cs_avail_out (ds_strm s1) =? 0); reflexivity|].
      split; [exact RAO1|].
      split; [intros E; discriminate E|]. split; [intros E; discriminate E|].
      split; [intros _ E; rewrite E; reflexivity|].
      split; [intros _ E; replace (cs_avail_out (ds_strm s1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact E); reflexivity|].
      split; [intros E; discriminate E|]. intros E; discriminate E.
    -
      cbn [fst snd] in PB. destruct PB as [PP2 PB2]. destruct (PB2 eq_refl) as [Hp2 Hf2].
      pose proof (fin_pathg_ok _ PP2 Hp2 Hf2) as FP.
      rewrite ?strm_set_status. split; [exact (ole_step _ s1 (set_status s1 FINISH_STATE) (OUTLE_strm _ _ eq_refl) eq_refl (proj1 FP))|].
      split; [exact RAO1|].
      split; [intros E; discriminate E|]. split; [intros E; discriminate E|]. split; [intros E; discriminate E|]. split; [intros E; discriminate E|].
      split; [intros _; exact FP|]. intros E; discriminate E.
  Qed.

  Lemma dc_hdr_skip : forall X, ds_status X <> INIT_STATE -> ds_status X <> GZIP_STATE -> dc_hdr X flush = dc_blocks X flush.
  Proof.
    intros X E1 E2. unfold dc_hdr, dc_gz.
    replace (ds_status X =? INIT_STATE) with false by (symmetry; apply Z.eqb_neq; exact E1).
    replace (ds_status X =? GZIP_STATE) with false by (symmetry; apply Z.eqb_neq; exact E2). reflexivity.
  Qed.

  Lemma body_pathg_ok : forall X, P2g X -> ds_pending X = 0 -> body_pathg inp flush (dc_body X flush) X.
  Proof.
    intros X PP Hp. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    destruct (P2g_facts X PP) as (RAI & RAO & TIE & HSZ & WB & RLA & RSS & WS & LBS).
    assert (HST : ds_status X = 42 \/ ds_status X = 113 \/ ds_status X = 666) by exact (pg_st _ P).
    assert (E4 : ((ds_status X =? INIT_STATE) && (ds_wrap X =? 0)) = false).
    { destruct (Z.eqb_spec (ds_status X) INIT_STATE) as [E|E]; [| reflexivity].
      destruct (pg_wrap _ P) as [W|[_ F]]; [rewrite W; reflexivity | rewrite E in F; discriminate F]. }
    unfold body_pathg, dc_body. rewrite E4.
    destruct (Z.eq_dec (ds_status X) 666) as [E6|N6].
    -
      destruct (Z.eq_dec (cs_avail_in (ds_strm X)) 0) as [A0|AN].
      + replace ((ds_status X =? FINISH_STATE) && negb (cs_avail_in (ds_strm X) =? 0)) with false
          by (rewrite A0; cbn; rewrite andb_false_r; reflexivity).
        rewrite (dc_hdr_skip X ltac:(rewrite E6; discriminate) ltac:(rewrite E6; discriminate)).
        pose proof (blocks_pathg_ok X PP Hp (fun _ => A0)) as BP.
        split; [exact (proj1 BP)|]. split; [exact HST|]. split; [exact RAI|].
        split; [intros _ C; contradiction|]. split; [intros _ _; exact BP|].
        split; [intros C; rewrite E6 in C; discriminate C|]. intros C; rewrite E6 in C; discriminate C.
      + replace ((ds_status X =? FINISH_STATE) && negb (cs_avail_in (ds_strm X) =? 0)) with true
          by (rewrite E6; replace (cs_avail_in (ds_strm X) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AN); reflexivity).
        split; [apply (ole_err X Z_BUF_ERROR Z_BUF_ERROR)|]. split; [exact HST|]. split; [exact RAI|].
        split; [intros _ _; reflexivity|]. split; [intros _ C; contradiction|].
        split; [intros C; rewrite E6 in C; discriminate C|]. intros C; rewrite E6 in C; discriminate C.
    - replace ((ds_status X =? FINISH_STATE) && negb (cs_avail_in (ds_strm X) =? 0)) with false
        by (replace (ds_status X =? FINISH_STATE) with false by (symmetry; apply Z.eqb_neq; exact N6); reflexivity).
      destruct (Z.eq_dec (ds_status X) 113) as [E1|N1].
      + rewrite (dc_hdr_skip X ltac:(rewrite E1; discriminate) ltac:(rewrite E1; discriminate)).
        pose proof (blocks_pathg_ok X PP Hp (fun C => False_ind _ (N6 C))) as BP.
        split; [exact (proj1 BP)|]. split; [exact HST|]. split; [exact RAI|].
        split; [intros C; contradiction|]. split; [intros C; contradiction|].
        split; [intros _; exact BP|]. intros C; rewrite E1 in C; discriminate C.
      +
        assert (E : ds_status X = INIT_STATE) by (unfold INIT_STATE; lia).
        destruct (hdr_zlib c0 s0 HC0 Hs0 D0 X HS Hp E) as (HOK & HSz & Stz & Horz & Aiz & Lkz & Wrz).
        destruct (zhdr_facts c0 X H Hp E) as ((H1 & _ & _) & K1 & O1 & _).
        destruct (DC_flush_pending c0 (zhdr_st X) HC0w H1) as (_ & _ & O2 & _).
        assert (Pz : PATG (flush_pending (zhdr_st X))).
        { apply (PATG_CF _ _ (CF_flush_pending (zhdr_st X))). destruct (PF_zhdr_pre X) as (t & Et & Pt). rewrite Et.
          apply PATG_busy; [exact (PATG_PF _ _ Pt P)|].
          pose proof (PF_fields _ _ Pt) as (_ & _ & (Est & _) & _). rewrite Est. exact E. }
        destruct HOK as (_ & _ & _ & FPOK & HOK2). cbv zeta in HOK2. destruct HOK2 as (_ & RP5 & _).
        assert (W1 : ds_wrap X = 1) by (destruct (pg_wrap _ P) as [W|[_ F]]; [exact W| rewrite E in F; discriminate F]).
        pose proof (sv_adler _ _ V) as RAD. pose proof (df_level _ D) as RLV. pose proof (PATG_strategy X P) as RSG.
        unfold dc_hdr. replace (ds_status X =? INIT_STATE) with true by (symmetry; apply Z.eqb_eq; exact E).
        rewrite deflate_zlib_header_eq. cbv zeta.
        assert (BPK : ds_pending (flush_pending (zhdr_st X)) = 0 -> blocks_pathg inp flush (dc_blocks (flush_pending (zhdr_st X)) flush) (flush_pending (zhdr_st X))).
        { intros P0. apply (blocks_pathg_ok _ (conj HSz Pz) P0). intros C. rewrite Stz in C. discriminate C. }
        assert (EGZ : dc_gz (flush_pending (zhdr_st X)) flush = dc_blocks (flush_pending (zhdr_st X)) flush).
        { unfold dc_gz. rewrite Stz. reflexivity. }
        assert (FW5 : fwT (flush_pending (zhdr_st X)) = fwT X) by (rewrite fwT_flush_pending; apply fwT_zhdr_g).
        revert O2 Stz RP5 BPK EGZ FPOK FW5. generalize (flush_pending (zhdr_st X)). intros X5 O2 Stz RP5 BPK EGZ FPOK FW5.
        assert (OL5 : ole (if negb (ds_pending X5 =? 0) then (set_last_flush X5 (-1), Z_OK) else dc_blocks X5 flush) X5).
        { destruct (Z.eqb_spec (ds_pending X5) 0) as [P0|PN]; cbn [negb].
          - exact (proj1 (BPK P0)).
          - apply ole_strm. reflexivity. }
        assert (ER : (let '(s, r) := if negb (ds_pending X5 =? 0) then (set_last_flush X5 (-1), Some Z_OK) else (X5, None) in
                      match r with Some rc => (s, rc) | None => dc_gz s flush end)
                     = (if negb (ds_pending X5 =? 0) then (set_last_flush X5 (-1), Z_OK) else dc_blocks X5 flush)).
        { destruct (negb (ds_pending X5 =? 0)); [reflexivity| exact EGZ]. }
        rewrite ER.
        split; [exact (ole_step _ X X5 (OUTLE_trans _ _ _ O1 O2) FW5 OL5)|].
        split; [exact HST|]. split; [exact RAI|].
        split; [intros C; contradiction|]. split; [intros C; contradiction|]. split; [intros C; contradiction|].
        intros _.
        split; [exact W1|]. split; [exact WB|]. split; [exact RLV|]. split; [exact RSG|]. split; [exact RSS|].
        split; [lia|]. split; [lia|]. split; [exact LBS|]. split; [exact RAD|]. split; [exact RAO|]. split; [exact FPOK|].
        split; [exact Stz|]. split; [exact RP5|]. split; [exact OL5|].
        split.
        * intros PN. replace (ds_pending X5 =? 0) with false by (symmetry; apply Z.eqb_neq; exact PN). reflexivity.
        * intros P0. rewrite P0. cbn [negb Z.eqb]. exact (BPK P0).
  Qed.

  Theorem defl_pathg_ok : P2g s0 -> defl_pathg inp flush (deflate_core s0 flush) s0.
  Proof.
    intros PP. pose proof PP as [HS P]. pose proof HS as [H K]. pose proof H as [[D XX] V].
    destruct (P2g_facts s0 PP) as (RAI & RAO & TIE & HSZ & WB & RLA & RSS & WS & LBS).
    pose proof Hfl5 as Hfl.
    pose proof (sv_nin _ _ V) as N1. pose proof (sv_inlen _ _ V) as N2. rewrite HIN, arr_len_of_list in N2. unfold zlength in N2.
    pose proof (df_lf _ D) as RLF. pose proof (df_pend _ D) as (Pd1 & Pd2 & Pd3). rewrite LBS in Pd3.
    unfold defl_pathg. cbv zeta. rewrite deflate_core_eq.
    replace (deflateStateCheck s0 || (Z_BLOCK <? flush) || (flush <? 0)) with false
      by (rewrite (df_status _ D); destruct HFL as [-> | [-> | ->]]; reflexivity).
    match goal with |- _ /\ ?T => assert (REST : T) end.
    2:{ split; [|exact REST]. destruct REST as (_ & _ & _ & PERR & POK).
        destruct (Z.eq_dec (ds_status s0) 666) as [E6|N6]; [destruct (Z.eq_dec flush 4) as [F4|F4]|].
        2:{ rewrite (PERR (conj E6 F4)). apply ole_err. }
        all: (assert (NE : ~ (ds_status s0 = 666 /\ flush <> 4)) by (intros [C1 C2]; first [exact (C2 F4)| exact (N6 C1)]));
             destruct (POK NE) as (_ & _ & _ & _ & EBUF & PGO);
             (destruct (Z.eq_dec (cs_avail_out (ds_strm s0)) 0) as [A0|AN]; [rewrite (EBUF A0); apply ole_err|]);
             destruct (PGO AN) as [PG1 PG2];
             (destruct (Z.eq_dec (ds_pending s0) 0) as [P0|PN];
              [ destruct (PG2 P0) as [RK1 RK2];
                destruct ((cs_avail_in (ds_strm s0) =? 0) && (RANK flush <=? RANK (ds_last_flush s0)) && negb (flush =? Z_FINISH)) eqn:ERK;
                [ assert (RK : rank_err s0 flush)
                    by (apply andb_true_iff in ERK as [ERK E3]; apply andb_true_iff in ERK as [E1 E2];
                        split; [apply Z.eqb_eq; exact E1|]; split; [apply Z.leb_le; exact E2|]; intros F; rewrite F in E3; discriminate E3);
                  rewrite (RK1 RK); exact (ole_step _ s0 (set_last_flush s0 flush) (OUTLE_strm _ _ eq_refl) eq_refl (ole_err _ _ _))
                | assert (NRK : ~ rank_err s0 flush)
                    by (intros (R1 & R2 & R3); apply andb_false_iff in ERK; destruct ERK as [ERK|E3];
                        [ apply andb_false_iff in ERK; destruct ERK as [E1|E2]; [apply Z.eqb_neq in E1; contradiction| apply Z.leb_gt in E2; lia]
                        | destruct (Z.eqb_spec flush Z_FINISH) as [F|F]; [contradiction| discriminate E3] ]);
                  exact (ole_step _ s0 (set_last_flush s0 flush) (OUTLE_strm _ _ eq_refl) eq_refl (proj1 (RK2 NRK))) ]
              | pose proof (PG1 PN) as PG; cbv zeta in PG; destruct PG as (_ & _ & OL2 & _);
                destruct (DC_flush_pending c0 (set_last_flush s0 flush) HC0w (proj1 (proj1 (P2g_slf s0 flush PP ltac:(lia))))) as (_ & _ & O2 & _);
                exact (ole_step _ s0 (flush_pending (set_last_flush s0 flush)) (OUTLE_trans _ _ _ (OUTLE_strm _ _ eq_refl) O2)
                         (eq_trans (fwT_flush_pending _) eq_refl) OL2) ]). }
    split; [exact (pg_st _ P)|]. split; [exact RAI|]. split; [lia|].
    split.
    { intros [E6 F4]. replace ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH)) with true; [reflexivity|].
      rewrite E6. destruct (Z.eqb_spec flush Z_FINISH) as [F|F]; [exfalso; exact (F4 F)| reflexivity]. }
    intros NE.
    replace ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH)) with false.
    2:{ symmetry. apply andb_false_iff. destruct (Z.eqb_spec (ds_status s0) FINISH_STATE) as [E|E]; [right|left; reflexivity].
        destruct (Z.eqb_spec flush Z_FINISH) as [F|F]; [reflexivity|]. exfalso. apply NE. split; [exact E| exact F]. }
    split; [exact RAO|]. split; [exact RLF|]. split; [lia|]. split; [exact LBS|].
    split.
    { intros A0. rewrite A0. reflexivity. }
    intros AN. replace (cs_avail_out (ds_strm s0) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AN).
    pose proof (P2g_slf s0 flush PP ltac:(lia)) as PP1.
    unfold dc_pend. cbv zeta.
    change (ds_pending (set_last_flush s0 flush)) with (ds_pending s0).
    change (cs_avail_in (ds_strm (set_last_flush s0 flush))) with (cs_avail_in (ds_strm s0)).
    split.
    -
      intros PN. replace (ds_pending s0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact PN). cbn [negb].
      destruct (P2g_fp _ PP1) as [PPf Hor].
      destruct (ST_flush_pending c0 s0 HC0 _ (proj1 PP1)) as (_ & FPOK & _).
      assert (RST2 : 0 <= ds_status (flush_pending (set_last_flush s0 flush)) < 1000)
        by (destruct (pg_st _ (proj2 PPf)) as [E|[E|E]]; rewrite E; unfold INIT_STATE, BUSY_STATE, FINISH_STATE; lia).
      assert (BPK : cs_avail_out (ds_strm (flush_pending (set_last_flush s0 flush))) <> 0 ->
                    body_pathg inp flush (dc_body (flush_pending (set_last_flush s0 flush)) flush) (flush_pending (set_last_flush s0 flush))).
      { intros A2. apply (body_pathg_ok _ PPf). destruct Hor as [X0|X0]; [exact X0| contradiction]. }
      revert RST2 BPK. generalize (flush_pending (set_last_flush s0 flush)). intros s2 RST2 BPK.
      split; [exact FPOK|]. split; [exact RST2|].
      destruct (Z.eqb_spec (cs_avail_out (ds_strm s2)) 0) as [A2|A2].
      + split; [apply ole_strm; reflexivity|].
        split; [intros _; reflexivity| intros C; contradiction].
      + split; [exact (proj1 (BPK A2))|]. split; [intros C; contradiction| intros _; exact (BPK A2)].
    -
      intros P0. rewrite P0. cbn [Z.eqb negb].
      destruct ((cs_avail_in (ds_strm s0) =? 0) && (RANK flush <=? RANK (ds_last_flush s0)) && negb (flush =? Z_FINISH)) eqn:ERK.
      + split; [intros _; reflexivity|]. intros NR. exfalso. apply NR.
        apply andb_true_iff in ERK as [ERK E3]. apply andb_true_iff in ERK as [E1 E2].
        split; [apply Z.eqb_eq; exact E1|]. split; [apply Z.leb_le; exact E2|].
        intros F. rewrite F in E3. discriminate E3.
      + split.
        * intros (R1 & R2 & R3). exfalso.
          apply andb_false_iff in ERK. destruct ERK as [ERK|E3].
          -- apply andb_false_iff in ERK. destruct ERK as [E1|E2]; [apply Z.eqb_neq in E1; contradiction| apply Z.leb_gt in E2; lia].
          -- destruct (Z.eqb_spec flush Z_FINISH) as [F|F]; [contradiction| discriminate E3].
        * intros _. apply (body_pathg_ok _ PP1). exact P0.
  Qed.

  Theorem patg_core : P2g s0 -> P2g (fst (deflate_core s0 flush)).
  Proof.
    intros PP0. pose proof PP0 as [HS0 P0]. pose proof Hfl5 as Hfl.
    unfold deflate_core.
    destruct (deflateStateCheck s0 || (Z_BLOCK <? flush) || (flush <? 0)); [cbn [fst]; exact PP0|].
    destruct ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH)); [apply P2g_err; exact PP0|].
    destruct (cs_avail_out (ds_strm s0) =? 0); [apply P2g_err; exact PP0|].
    cbv zeta.
    pose proof (P2g_slf s0 flush PP0 ltac:(lia)) as PP1.
    assert (Pd1 : ds_pending (set_last_flush s0 flush) = ds_pending s0) by reflexivity.
    revert PP1 Pd1. generalize (set_last_flush s0 flush). intros s1 PP1 Pd1.
    match goal with |- P2g (fst (let '(s, r) := ?head in _)) => destruct head as [s2 r2] eqn:Ehead end.
    assert (H2 : P2g s2 /\ (r2 = None -> ds_pending s2 = 0)).
    { destruct (negb (ds_pending s1 =? 0)) eqn:Ep.
      - destruct (P2g_fp s1 PP1) as [PPf Hor].
        destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_pending s1))) 0) as [Ea|Ea]; inversion Ehead; subst s2 r2.
        + split; [apply P2g_slf; [exact PPf | lia] | intros HH; discriminate HH].
        + split; [exact PPf | intros _; destruct Hor as [X0|X0]; [exact X0 | contradiction]].
      - destruct ((cs_avail_in (ds_strm s1) =? 0) && (RANK flush <=? RANK (ds_last_flush s0)) && negb (flush =? Z_FINISH)).
        + unfold err_return in Ehead. inversion Ehead; subst s2 r2. split; [exact (P2g_err s1 Z_BUF_ERROR PP1) | intros HH; discriminate HH].
        + inversion Ehead; subst s2 r2. split; [exact PP1|]. intros _. destruct (Z.eqb_spec (ds_pending s1) 0); [assumption | discriminate Ep]. }
    clear Ehead. destruct H2 as [PP2 Hp2].
    destruct r2 as [rc|]; [cbn [fst]; exact PP2|]. specialize (Hp2 eq_refl).
    destruct ((ds_status s2 =? FINISH_STATE) && negb (cs_avail_in (ds_strm s2) =? 0)) eqn:Efa; [apply P2g_err; exact PP2|].
    pose proof PP2 as [HS2 P2'].
    assert (E4 : ((ds_status s2 =? INIT_STATE) && (ds_wrap s2 =? 0)) = false).
    { destruct (Z.eqb_spec (ds_status s2) INIT_STATE) as [E|E]; [| reflexivity].
      destruct (pg_wrap _ P2') as [W|[_ F]]; [rewrite W; reflexivity | rewrite E in F; discriminate F]. }
    rewrite E4.
    rewrite deflate_zlib_header_eq.
    match goal with |- P2g (fst (let '(s, r) := ?head in _)) => destruct head as [s5 r5] eqn:Ehead end.
    assert (H5 : P2g s5 /\ (r5 = None -> ds_pending s5 = 0 /\ cs_avail_in (ds_strm s5) = cs_avail_in (ds_strm s2)
                                        /\ (ds_status s5 = FINISH_STATE -> ds_status s2 = FINISH_STATE))).
    { destruct (Z.eqb_spec (ds_status s2) INIT_STATE) as [E|E].
      - destruct (hdr_zlib c0 s0 HC0 Hs0 D0 s2 HS2 Hp2 E) as (_ & HSz & Stz & Horz & Aiz & _).
        assert (Pz : PATG (flush_pending (zhdr_st s2))).
        { apply (PATG_CF _ _ (CF_flush_pending (zhdr_st s2))). destruct (PF_zhdr_pre s2) as (t & Et & Pt). rewrite Et.
          apply PATG_busy; [exact (PATG_PF _ _ Pt P2')|].
          pose proof (PF_fields _ _ Pt) as (_ & _ & (Est & _) & _). rewrite Est. exact E. }
        cbv zeta in Ehead. destruct (negb (ds_pending (flush_pending (zhdr_st s2)) =? 0)) eqn:Ep; inversion Ehead; subst s5 r5.
        + split; [apply P2g_slf; [exact (conj HSz Pz) | lia] | intros HH; discriminate HH].
        + split; [exact (conj HSz Pz)|]. intros _. rewrite Aiz, Stz.
          split; [destruct (Z.eqb_spec (ds_pending (flush_pending (zhdr_st s2))) 0); [assumption | discriminate Ep]|].
          split; [reflexivity | unfold BUSY_STATE, FINISH_STATE; intros; lia].
      - inversion Ehead; subst s5 r5. split; [exact PP2|]. intros _. split; [exact Hp2|]. split; [reflexivity | intros X; exact X]. }
    clear Ehead. destruct H5 as [PP5 Hr5].
    destruct r5 as [rc|]; [cbn [fst]; exact PP5|]. destruct (Hr5 eq_refl) as (Hp5 & Ai5 & Fin5).
    assert (E6 : (ds_status s5 =? GZIP_STATE) = false).
    { destruct (pg_st _ (proj2 PP5)) as [E|[E|E]]; rewrite E; reflexivity. }
    rewrite E6.
    assert (Hfin5 : ds_status s5 = FINISH_STATE -> cs_avail_in (ds_strm s5) = 0).
    { intros E. rewrite Ai5. pose proof (Fin5 E) as E2. rewrite E2 in Efa. cbn in Efa.
      destruct (Z.eqb_spec (cs_avail_in (ds_strm s2)) 0); [assumption | discriminate Efa]. }
    destruct (P2g_blocks s5 PP5 Hp5 Hfin5) as [PP7 Hr7]. cbv zeta in PP7, Hr7.
    destruct (deflate_blocks s5 flush) as [s7 r7]. cbn [fst snd] in PP7, Hr7.
    destruct r7 as [rc|]; [cbn [fst]; exact PP7|]. destruct (Hr7 eq_refl) as [Hp7 Hfin7].
    destruct (negb (flush =? Z_FINISH)) eqn:Ef; [cbn [fst]; exact PP7|].
    assert (Hf : flush = Z_FINISH) by (destruct (Z.eqb_spec flush Z_FINISH); [assumption | discriminate Ef]).
    destruct (Z.leb_spec (ds_wrap s7) 0) as [Hw|Hw]; [cbn [fst]; exact PP7|].
    destruct PP7 as [HS7 P7].
    pose proof (proj2 (finish_stage c0 s0 HC0 Hs0 D0 s7 flush HS7 Hp7 Hfl Hfin7) Hf Hw) as HT.
    revert HT. rewrite deflate_trailer_eq. cbv zeta.
    assert (Pt : PATG (flush_pending (trailer_st s7))) by (apply (PATG_CF _ _ (CF_flush_pending (trailer_st s7))); exact (PATG_PF _ _ (PF_trailer s7) P7)).
    assert (St : ds_status (flush_pending (trailer_st s7)) = FINISH_STATE).
    { pose proof (PF_fields _ _ (PF_flush_pending (trailer_st s7))) as (_ & _ & (E1 & _) & _).
      pose proof (PF_fields _ _ (PF_trailer s7)) as (_ & _ & (E2 & _) & _). rewrite E1, E2. exact (Hfin7 Hf). }
    assert (Wt : ds_wrap (flush_pending (trailer_st s7)) = 1).
    { destruct (pg_wrap _ Pt) as [W|[W _]]; [exact W|].
      pose proof (PF_fields _ _ (PF_flush_pending (trailer_st s7))) as (_ & (_ & _ & _ & _ & _ & _ & _ & E1) & _).
      pose proof (PF_fields _ _ (PF_trailer s7)) as (_ & (_ & _ & _ & _ & _ & _ & _ & E2) & _). rewrite E1, E2 in W. lia. }
    revert Pt St Wt. generalize (flush_pending (trailer_st s7)). intros s8 Pt St Wt.
    rewrite Wt. change (0 <? 1) with true. cbv iota. change (Z.opp 1) with (-1). cbn [fst]. intros HT.
    split; [exact HT | exact (PATG_wrapneg s8 Pt St)].
  Qed.
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

  Lemma api_HC0 : C0OK' c0. Proof. exact (C0OK'_of_call zc Hzc). Qed.
  Lemma api_DC0 : DC c0 d0. Proof. split; [apply DD_set_strm; exact HDD | subst d0 c0; apply SV_entry; exact Hzc]. Qed.
  Lemma api_P2g : P2g c0 d0 d0. Proof. split; [split; [exact api_DC0| reflexivity]| exact (PATG_set_strm ds c0 P)]. Qed.

  Theorem defl_pathg_intro : defl_pathg (zc_input zc) flush (deflate_core d0 flush) d0.
  Proof.
    destruct Hzc as (_ & _ & _ & HB).
    apply (defl_pathg_ok (zc_input zc) flush c0 d0 api_HC0 eq_refl (proj1 (proj1 api_DC0)) HFL).
    - exact HAO. - reflexivity. - exact HIL. - exact HB. - exact HWS. - exact HHS. - exact HLBS. - exact api_P2g.
  Qed.

  Theorem deflate_core_P2g : PATG (fst (deflate_core d0 flush)) /\ RefDeflSafeI4.ST c0 d0 (fst (deflate_core d0 flush)).
  Proof.
    destruct Hzc as (_ & _ & _ & HB).
    destruct (patg_core (zc_input zc) flush c0 d0 api_HC0 eq_refl (proj1 (proj1 api_DC0)) HFL HAO eq_refl HIL HB HWS HHS HLBS api_P2g) as [A B].
    split; [exact B| exact A].
  Qed.
End Api.


