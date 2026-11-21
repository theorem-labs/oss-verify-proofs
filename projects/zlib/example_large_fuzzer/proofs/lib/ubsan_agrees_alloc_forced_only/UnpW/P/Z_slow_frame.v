(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_slow_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk DeflateOverlay FlushBlockModel FillWinModel SendModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefFlushBlk13 RefDeflFast1. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow5 RefDeflSlow6. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeW RefDeflSafeLW. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeLF RefDeflSafeI2. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflateDictM BoundFw. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import BoundSlow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition din_tieP (inp : list Z) (d : deflate_state) : Prop :=
  cs_input (ds_strm d) = arr_of_list inp /\ Forall (fun b => 0 <= b < 256) inp.

Record SCFG (inp : list Z) (s : deflate_state) : Prop := mkSCFG {
  c_ws : ds_w_size s = 32768;
  c_hs : ds_hash_size s = 32768;
  c_lbs : ds_lit_bufsize s = 16384;
  c_ins : ds_insert s = 0;
  c_wrap : ds_wrap s <> 2;
  c_ain : cs_avail_in (ds_strm s) <= 1;
  c_aout : 0 <= cs_avail_out (ds_strm s) < 2^31;
  c_tie : din_tieP inp s }.

Definition SF (s : deflate_state) := (ds_w_size s, ds_hash_size s, ds_lit_bufsize s, ds_insert s, ds_wrap s, ds_strm s).

Definition OUT (s : deflate_state) : nat := length (cs_out_rev (ds_strm s)).
Lemma OUT_SF : forall s s', SF s' = SF s -> OUT s' = OUT s.
Proof. intros s s' E. unfold OUT. assert (E6 : ds_strm s' = ds_strm s) by (unfold SF in E; congruence). rewrite E6. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma SF_prev_st : forall s, SF (prev_st s) = SF s. Proof. reflexivity. Qed.
Lemma SF_hash_st : forall s, SF (hash_st s) = SF s. Proof. reflexivity. Qed.

Lemma SF_slit1 : forall s, SF (slit1 s) = SF s. Proof. reflexivity. Qed.
Lemma SF_ltail_st : forall s, SF (ltail_st s) = SF s. Proof. reflexivity. Qed.
Lemma SF_avail0_st : forall s, SF (avail0_st s) = SF s. Proof. reflexivity. Qed.
Lemma SF_break1_st : forall s, SF (break1_st s) = SF s. Proof. reflexivity. Qed.

Lemma SF_insl_st : forall s mi, SF (insl_st s mi) = SF s.
Proof. intros s mi. unfold insl_st. destruct (_ <=? mi); reflexivity. Qed.

Lemma SF_slow_insert : forall n s mi, SF (deflate_slow_insert n s mi) = SF s.
Proof.
  induction n as [|n IH]; intros s mi; [reflexivity|].
  rewrite deflate_slow_insert_step. cbv zeta. destruct (negb _); [rewrite IH|]; apply SF_insl_st.
Qed.

Lemma SF_st_lm : forall s hh, SF (st_lm s hh) = SF s.
Proof.
  intros s hh. unfold st_lm. destruct (sl_lm_cond s hh); [|reflexivity].
  destruct (longest_match_ms s hh) as (ms & E). cbv zeta. rewrite E. destruct (sl_filter _); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fbo_strm_keep : forall X last,
  cs_input (ds_strm (flush_block_only X last)) = cs_input (ds_strm X)
  /\ cs_avail_in (ds_strm (flush_block_only X last)) = cs_avail_in (ds_strm X).
Proof.
  intros X last. rewrite fbo_eq.
  assert (E1 : cs_input (ds_strm (fbo3 X last)) = cs_input (ds_strm X) /\ cs_avail_in (ds_strm (fbo3 X last)) = cs_avail_in (ds_strm X)).
  { rewrite fbo3_strm. unfold fbo1. rewrite tr_flush_block_strm. destruct (_ && _); [destruct (ds_strm X)|]; split; reflexivity. }
  destruct (fp_len (fbo3 X last) =? 0); [exact E1|].
  (* [comment removed for export] *)
  set (Y := fbo3 X last) in *. clearbody Y.
  destruct E1 as [Ea Eb]. rewrite <- Ea, <- Eb. unfold fp_tail.
  destruct Y; cbn -[Z.sub Z.add Z.eqb wrap64 wrap32 arr_slice cs_emit Z.ltb fp_len].
  destruct ds_strm; cbn -[Z.sub Z.add Z.eqb wrap64 wrap32 arr_slice Z.ltb fp_len rev_append].
  destruct (_ - _ =? 0); split; reflexivity.
Qed.

Lemma fbo_avail_out : forall X last, flush_ok X last -> ds_lit_bufsize X = 16384 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  0 <= cs_avail_out (ds_strm (flush_block_only X last)) <= cs_avail_out (ds_strm X).
Proof.
  intros X last F LB RA. destruct (flush_ok_fbo X last F LB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RP & _).
  destruct (tfb_keep X last) as (_ & _ & _ & EAO). pose proof (fbo3_strm X last) as ES.
  rewrite fbo_eq.
  assert (EL : fp_len (fbo3 X last) = if cs_avail_out (ds_strm X) <? ds_pending (fbo3 X last) then cs_avail_out (ds_strm X) else ds_pending (fbo3 X last)).
  { unfold fp_len. rewrite ES, EAO, wrap32_id by lia. reflexivity. }
  destruct (fp_len (fbo3 X last) =? 0) eqn:E0; [rewrite ES, EAO; lia|].
  unfold fp_tail. cbv zeta.
  assert (EA : forall c l v w, cs_avail_out (cset_total_out (cset_avail_out (cs_emit c l) v) w) = v) by (intros [] l v w; reflexivity).
  destruct (_ - _ =? 0); dsred; rewrite ?EA, ?ES, ?EAO, ?EL; destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending (fbo3 X last))); lia.
Qed.

Lemma PF_fbo : forall X last, PF (flush_block_only X last) = PF X.
Proof. intros X last. unfold flush_block_only. cbv zeta. rewrite PF_flush_pending, PF_set_block_start, PF_tfb. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma SF_tally_dist : forall s d l, SF (fst (tr_tally_dist s d l)) = SF s.
Proof. reflexivity. Qed.

Lemma SF_st_sdist' : forall s, SF (fst (st_sdist s)) = SF s.
Proof.
  intros s. unfold st_sdist.
  pose proof (SF_tally_dist s (wrap32 (ds_strstart s - 1 - ds_prev_match s)) (ds_prev_length s - 3)) as ET.
  destruct (tr_tally_dist s _ _) as [s1 b]. cbn [fst] in ET. rewrite <- ET. clear ET. cbv zeta. cbn [fst].
  match goal with |- SF (set_strstart (set_match_length (set_match_available ?U 0) 2) _) = _ => transitivity (SF U); [generalize U; intros U0; reflexivity|] end.
  rewrite SF_slow_insert. reflexivity.
Qed.

Lemma flush_block_fst' : forall s last, fst (flush_block s last) = flush_block_only s last.
Proof. intros s last. unfold flush_block. destruct (_ =? 0); reflexivity. Qed.

Lemma st_bflush_fst : forall s b, fst (st_bflush s b) = if b then flush_block_only s 0 else s.
Proof.
  intros s b. unfold st_bflush. destruct b; [|reflexivity].
  rewrite <- flush_block_fst'. destruct (flush_block s 0) as [s' [bs|]]; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition slow_tailres (s1 : deflate_state) (flush : Z) : deflate_state * block_state :=
  deflate_tail (tail_st (if negb (ds_match_available s1 =? 0) then break1_st s1 else s1)) flush.

Definition slow_res (flush : Z) (f : nat) (X : deflate_state) : deflate_state * block_state :=
  match snd (deflate_slow_loop f X flush) with
  | Some bs => (fst (deflate_slow_loop f X flush), bs)
  | None => slow_tailres (fst (deflate_slow_loop f X flush)) flush
  end.

Lemma deflate_slow_res : forall s flush, deflate_slow s flush = slow_res flush (lz_fuel s) s.
Proof. intros s flush. rewrite deflate_slow_eq. unfold slow_res, slow_tailres. destruct (snd _); reflexivity. Qed.

Lemma slow_res_S : forall flush f X,
  slow_res flush (S f) X = match snd (st_sbody X flush) with
                           | LCont => slow_res flush f (fst (st_sbody X flush))
                           | LBreak => slow_tailres (fst (st_sbody X flush)) flush
                           | LRet bs => (fst (st_sbody X flush), bs)
                           end.
Proof. intros flush f X. unfold slow_res. rewrite sloop_step'. destruct (snd (st_sbody X flush)); reflexivity. Qed.

Definition tail_safe (flush : Z) (f : nat) (X : deflate_state) : Prop :=
  match snd (deflate_slow_loop f X flush) with Some _ => True | None => stail_ok 32768 (fst (deflate_slow_loop f X flush)) flush end.

Lemma tail_safe_S : forall flush f X,
  tail_safe flush (S f) X = match snd (st_sbody X flush) with
                            | LCont => tail_safe flush f (fst (st_sbody X flush))
                            | LBreak => stail_ok 32768 (fst (st_sbody X flush)) flush
                            | LRet bs => True
                            end.
Proof. intros flush f X. unfold tail_safe. rewrite sloop_step'. destruct (snd (st_sbody X flush)); reflexivity. Qed.

Lemma OUT_tailres : forall s1 flush, (OUT s1 <= OUT (fst (slow_tailres s1 flush)))%nat.
Proof.
  intros s1 flush. unfold slow_tailres.
  set (s2 := if negb (ds_match_available s1 =? 0) then break1_st s1 else s1).
  assert (E2 : OUT (tail_st s2) = OUT s1) by (unfold s2; destruct (negb _); reflexivity).
  rewrite <- E2. generalize (tail_st s2). intros t. unfold deflate_tail.
  destruct (flush =? Z_FINISH).
  - pose proof (fbo_out_mono t 1) as M. rewrite <- flush_block_fst' in M. destruct (flush_block t 1) as [s' [bs|]]; exact M.
  - destruct (negb (ds_sym_next t =? 0)); [|apply le_n].
    pose proof (fbo_out_mono t 0) as M. rewrite <- flush_block_fst' in M. destruct (flush_block t 0) as [s' [bs|]]; exact M.
Qed.

(* [comment removed for export] *)
Lemma sbody_break_flush : forall X flush, snd (st_sbody X flush) = LBreak -> flush <> Z_NO_FLUSH.
Proof. intros X flush H E. exact (BoundSlow.sbody_nobreak flush X E H). Qed.
