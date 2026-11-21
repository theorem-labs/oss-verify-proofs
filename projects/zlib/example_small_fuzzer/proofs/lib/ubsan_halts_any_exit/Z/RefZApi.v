(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import String.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateSafe.

Module DeflateCongr.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ModelRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma read_buf_strm_out : forall s dst n,
  cs_total_out (ds_strm (fst (read_buf s dst n))) = cs_total_out (ds_strm s).
Proof.
  intros s dst n. unfold read_buf.
  destruct (Z.eqb _ 0); [reflexivity|].
  destruct dst as [off|]; cbn -[Z.ltb Z.eqb Z.sub Z.add arr_slice arr_upd adler32_upd crc32_upd wrap64 List.rev_append];
    destruct (ds_wrap s =? 1); cbn -[Z.ltb Z.eqb Z.sub Z.add arr_slice arr_upd adler32_upd crc32_upd wrap64 List.rev_append];
    try reflexivity;
    destruct (ds_wrap s =? 2); cbn -[Z.ltb Z.eqb Z.sub Z.add arr_slice arr_upd adler32_upd crc32_upd wrap64 List.rev_append];
    reflexivity.
Qed.

Lemma fill_window_insert_strm : forall k s str, ds_strm (fill_window_insert k s str) = ds_strm s.
Proof.
  induction k as [|k IH]; intros s str; cbn [fill_window_insert]; [reflexivity|].
  destruct (negb _); [|reflexivity].
  destruct (Z.ltb _ _); [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma slide_hash_strm : forall s, ds_strm (slide_hash s) = ds_strm s.
Proof. intros s. reflexivity. Qed.

Definition fw_slide (s : deflate_state) (wsize : Z) : deflate_state * Z :=
  let more := wrap32 (ds_window_size s - ds_lookahead s - ds_strstart s) in
  if Z.leb (wsize + (ds_w_size s - MIN_LOOKAHEAD)) (ds_strstart s) then
    let s := set_window s (arr_blit (ds_window s) 0 (ds_window s) wsize (wrap32 (wsize - more))) in
    let s := set_match_start s (wrap32 (ds_match_start s - wsize)) in
    let s := set_strstart s (ds_strstart s - wsize) in
    let s := set_block_start s (ds_block_start s - wsize) in
    let s := if Z.ltb (ds_strstart s) (ds_insert s) then set_insert s (ds_strstart s) else s in
    let s := slide_hash s in
    (s, wrap32 (more + wsize))
  else (s, more).

Definition fw_read (s : deflate_state) (more : Z) : deflate_state * bool :=
  if Z.eqb (cs_avail_in (ds_strm s)) 0 then (s, true)
  else
    let '(s, n) := read_buf s (RB_window (ds_strstart s + ds_lookahead s)) more in
    let s := set_lookahead s (ds_lookahead s + n) in
    let s :=
      if Z.leb MIN_MATCH (ds_lookahead s + ds_insert s) then
        let str := ds_strstart s - ds_insert s in
        let s := set_ins_h s (arr_get (ds_window s) str) in
        let s := set_ins_h s (update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + 1))) in
        fill_window_insert (Z.to_nat (ds_insert s)) s str
      else s in
    (s, false).

Lemma fill_window_body_eq : forall s w,
  fill_window_body s w = (let '(s1, more) := fw_slide s w in fw_read s1 more).
Proof. intros s w. unfold fill_window_body, fw_slide, fw_read. destruct (Z.leb _ _); reflexivity. Qed.

Lemma fw_slide_strm : forall s w, ds_strm (fst (fw_slide s w)) = ds_strm s.
Proof.
  intros s w. unfold fw_slide. destruct (Z.leb _ _); [|reflexivity].
  cbn [fst]. rewrite slide_hash_strm.
  match goal with |- ds_strm (if ?c then _ else _) = _ => destruct c; reflexivity end.
Qed.

Lemma fw_read_out : forall s more, cs_total_out (ds_strm (fst (fw_read s more))) = cs_total_out (ds_strm s).
Proof.
  intros s more. unfold fw_read. destruct (Z.eqb _ 0); [reflexivity|].
  pose proof (read_buf_strm_out s (RB_window (ds_strstart s + ds_lookahead s)) more) as Hr.
  destruct (read_buf s _ more) as [s2 m]. cbn [fst] in Hr |- *.
  match goal with |- cs_total_out (ds_strm (if ?c then _ else _)) = _ => destruct c end.
  - rewrite fill_window_insert_strm. cbn [ds_strm set_ins_h set_lookahead]. exact Hr.
  - cbn [ds_strm set_lookahead]. exact Hr.
Qed.

Lemma fill_window_body_out : forall s w,
  cs_total_out (ds_strm (fst (fill_window_body s w))) = cs_total_out (ds_strm s).
Proof.
  intros s w. rewrite fill_window_body_eq.
  pose proof (fw_slide_strm s w) as Hs. destruct (fw_slide s w) as [s1 more]. cbn [fst] in Hs.
  rewrite fw_read_out, Hs. reflexivity.
Qed.

Lemma fill_window_loop_out : forall k s w,
  cs_total_out (ds_strm (fill_window_loop k s w)) = cs_total_out (ds_strm s).
Proof.
  induction k as [|k IH]; intros s w; cbn [fill_window_loop]; [reflexivity|].
  pose proof (fill_window_body_out s w) as Hb. destruct (fill_window_body s w) as [s1 brk]. cbn [fst] in Hb.
  destruct brk; [exact Hb|]. destruct (_ && _); [rewrite IH|]; exact Hb.
Qed.

Lemma fill_window_high_strm : forall s, ds_strm (fill_window_high s) = ds_strm s.
Proof.
  intros s. unfold fill_window_high.
  destruct (Z.ltb _ _); [|reflexivity]. destruct (Z.ltb _ _); [reflexivity|]. destruct (Z.ltb _ _); reflexivity.
Qed.

Lemma fill_window_out : forall s, cs_total_out (ds_strm (fill_window s)) = cs_total_out (ds_strm s).
Proof. intros s. unfold fill_window. rewrite fill_window_high_strm. apply fill_window_loop_out. Qed.

Lemma setdict_inner_strm : forall k s str n, ds_strm (fst (setdict_inner k s str n)) = ds_strm s.
Proof.
  induction k as [|k IH]; intros s str n; cbn [setdict_inner]; [reflexivity|].
  destruct (negb _); [rewrite IH|]; reflexivity.
Qed.

Lemma setdict_outer_out : forall k s, cs_total_out (ds_strm (setdict_outer k s)) = cs_total_out (ds_strm s).
Proof.
  induction k as [|k IH]; intros s; cbn [setdict_outer]; [reflexivity|].
  destruct (Z.leb _ _); [|reflexivity].
  pose proof (setdict_inner_strm (Z.to_nat (ds_lookahead s - (MIN_MATCH - 1))) s (ds_strstart s) (ds_lookahead s - (MIN_MATCH - 1))) as Hi.
  destruct (setdict_inner _ s _ _) as [s1 str]. cbn [fst] in Hi.
  rewrite IH, fill_window_out. cbn [ds_strm set_lookahead set_strstart]. rewrite Hi. reflexivity.
Qed.

Lemma clear_hash_strm : forall s, ds_strm (clear_hash s) = ds_strm s.
Proof. reflexivity. Qed.

Definition sd_prep (s : deflate_state) (wrap : Z) (dictionary : list Z) : deflate_state * list Z :=
  let dictLength := zlength dictionary in
  let s := if Z.eqb wrap 1
           then set_strm s (cset_adler (ds_strm s) (adler32_upd (cs_adler (ds_strm s)) dictionary))
           else s in
  let s := set_wrap s 0 in
  if Z.leb (ds_w_size s) dictLength then
    let s := if Z.eqb wrap 0 then
               let s := clear_hash s in
               let s := set_strstart s 0 in
               let s := set_block_start s 0 in
               set_insert s 0
             else s in
    (s, zskipn (dictLength - ds_w_size s) dictionary)
  else (s, dictionary).

Definition sd_run (s : deflate_state) (dict : list Z) (wrap : Z) : deflate_state :=
  let saved := ds_strm s in
  let s := set_strm s (cset_avail_in (cset_next_in (cset_input saved (arr_of_list dict)) 0) (zlength dict)) in
  let s := fill_window s in
  let s := setdict_outer (Z.to_nat (zlength dict + 2)) s in
  let s := set_strstart s (ds_strstart s + ds_lookahead s) in
  let s := set_block_start s (ds_strstart s) in
  let s := set_insert s (ds_lookahead s) in
  let s := set_lookahead s 0 in
  let s := set_prev_length s (MIN_MATCH - 1) in
  let s := set_match_length s (MIN_MATCH - 1) in
  let s := set_match_available s 0 in
  let st := ds_strm s in
  let st := cset_input (cset_next_in (cset_avail_in st (cs_avail_in saved)) (cs_next_in saved)) (cs_input saved) in
  let s := set_strm s st in
  set_wrap s wrap.

Lemma deflateSetDictionary_eq : forall s zc dictionary,
  deflateSetDictionary_m s zc dictionary =
  (let cs := cstrm_of_call zc in
   let s := set_strm s cs in
   if deflateStateCheck s then (s, zret_of_cs cs Z_STREAM_ERROR)
   else
     let wrap := ds_wrap s in
     if (wrap =? 2) || ((wrap =? 1) && negb (ds_status s =? INIT_STATE)) || negb (ds_lookahead s =? 0)
     then (s, zret_of_cs cs Z_STREAM_ERROR)
     else
       let '(s1, dict) := sd_prep s wrap dictionary in
       let s2 := sd_run s1 dict wrap in
       (s2, zret_of_cs (ds_strm s2) Z_OK)).
Proof.
  intros s zc dictionary. unfold deflateSetDictionary_m, sd_prep, sd_run.
  destruct (deflateStateCheck _); [reflexivity|].
  destruct (_ || _); [reflexivity|].
  destruct (Z.leb _ _); reflexivity.
Qed.

Lemma sd_prep_out : forall s wrap d, cs_total_out (ds_strm (fst (sd_prep s wrap d))) = cs_total_out (ds_strm s).
Proof.
  intros s wrap d. unfold sd_prep.
  destruct (wrap =? 1); destruct (Z.leb _ _); try (destruct (wrap =? 0)); reflexivity.
Qed.

Lemma sd_run_out : forall s d wrap, cs_total_out (ds_strm (sd_run s d wrap)) = cs_total_out (ds_strm s).
Proof.
  intros s d wrap. unfold sd_run. cbn [ds_strm set_wrap set_strm set_match_available set_match_length set_prev_length
    set_lookahead set_insert set_block_start set_strstart cset_input cset_next_in cset_avail_in cs_total_out].
  match goal with |- cs_total_out (ds_strm (setdict_outer ?k ?s1)) = _ => rewrite (setdict_outer_out k s1) end.
  rewrite fill_window_out. reflexivity.
Qed.

Lemma HDSD_deflate : forall ds zc dict,
  zs_total_out (zr_strm (snd (da_deflateSetDictionary deflate_model ds zc dict))) = zs_total_out (zc_strm zc).
Proof.
  intros ds zc dict. cbn [da_deflateSetDictionary deflate_model]. rewrite deflateSetDictionary_eq.
  cbv zeta. destruct (deflateStateCheck _); [reflexivity|].
  destruct (_ || _); [reflexivity|].
  match goal with |- context [sd_prep ?s ?w ?d] =>
    pose proof (sd_prep_out s w d) as Hp; destruct (sd_prep s w d) as [s1 d1] end.
  cbn [fst] in Hp. cbn [snd zret_of_cs zr_strm zstrm_of_cs zs_total_out].
  rewrite sd_run_out, Hp. reflexivity.
Qed.


Lemma deflateResetKeep_total0 : forall s s' rc,
  deflateResetKeep s = (s', rc) -> rc = Z_OK -> cs_total_out (ds_strm s') = 0.
Proof.
  intros s s' rc H Hrc. unfold deflateResetKeep in H.
  destruct (deflateStateCheck s); [injection H; intros <- <-; discriminate Hrc|].
  injection H; intros <- <-. cbn. destruct (ds_wrap s <? 0); reflexivity.
Qed.

Lemma lm_init_strm : forall s, ds_strm (lm_init s) = ds_strm s.
Proof.
  intros s. unfold lm_init. destruct (configuration_table (ds_level (clear_hash (set_window_size s (2 * ds_w_size s))))) as [[[g l] n] c].
  reflexivity.
Qed.

Lemma deflateReset_total0 : forall s s' rc,
  deflateReset s = (s', rc) -> rc = Z_OK -> cs_total_out (ds_strm s') = 0.
Proof.
  intros s s' rc H Hrc. unfold deflateReset in H.
  destruct (deflateResetKeep s) as [s1 r1] eqn:E.
  destruct (r1 =? Z_OK) eqn:E1.
  - injection H; intros <- <-. rewrite lm_init_strm. eapply deflateResetKeep_total0; [exact E|]. apply Z.eqb_eq; exact E1.
  - injection H; intros <- <-. apply Z.eqb_neq in E1. contradiction.
Qed.

Section Init.
  Context {St : Type}.
  Variable hooks : zhooks St.

  Ltac mhnf := lazymatch goal with |- mall ?P ?tg => let t' := eval hnf in tg in change (mall P t') end.

  Ltac mlet :=
    lazymatch goal with
    | |- mall ?P ((let x := ?E in ?B) ?g) =>
        let T := type of E in let K := constr:(fun x : T => B g) in
        change (mall P (K E)); generalize E; intros ?; cbv beta
    | |- mall ?P (let x := ?E in ?B) =>
        let T := type of E in let K := constr:(fun x : T => B) in
        change (mall P (K E)); generalize E; intros ?; cbv beta
    end.

  Ltac mstep :=
    first [ mlet
          | refine (mall_sbind_any _ _ _ _ _); intros ? ?
          | lazymatch goal with
            | |- mall _ (mbind _ _) => refine (mall_bind (fun _ => True) _ _ _ (mall_true _) _); intros ? _
            | |- mall _ ((if ?c then _ else _) _) => destruct c eqn:?
            | |- mall _ (if ?c then _ else _) => destruct c eqn:?
            | |- mall _ ((match ?c with _ => _ end) _) => destruct c eqn:?
            | |- mall _ (match ?c with _ => _ end) => destruct c eqn:?
            end
          | progress mhnf ].

  Lemma HDI0_gen : forall zc lv me wb ml st g,
    mall (fun p => zr_rc (snd (fst p)) = Z_OK -> zs_total_out (zr_strm (snd (fst p))) = 0)
         (deflateInit2_m hooks zc lv me wb ml st g).
  Proof.
    intros zc lv me wb ml st g. cbv beta delta [deflateInit2_m].
    repeat mstep.
    all: cbn [mall fst snd zret_of_cs zr_rc zr_strm zstrm_of_cs zs_total_out].
    all: first [intros H; discriminate H | idtac].
    all: match goal with E : deflateReset _ = (?s, ?rc) |- _ => intros Hrc; exact (deflateReset_total0 _ _ _ E Hrc) end.
  Qed.
End Init.
End DeflateCongr.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.


Definition pc_deflateInit2 : Z := 0x17e04.
Definition pc_deflateInit : Z := 0x181b0.
Definition pc_deflateSetDictionary : Z := 0x151ac.
Definition pc_deflateBound : Z := 0x15c4c.
Definition pc_deflate : Z := 0x15e14.
Definition pc_deflateEnd : Z := 0x17ca8.
Definition pc_inflateInit2 : Z := 0x18c14.
Definition pc_inflateInit : Z := 0x18dcc.
Definition pc_inflate : Z := 0x18fe4.
Definition pc_inflateEnd : Z := 0x1b74c.
Definition pc_inflateSetDictionary : Z := 0x1b8d8.
Definition pc_compress2 : Z := 0x1f764.
Definition pc_compressBound : Z := 0x1f8a8.
Definition pc_uncompress : Z := 0x1fa94.
Definition pc_zalloc : Z := 0x10b28.
Definition pc_zfree : Z := 0x10cd0.
Definition pc_zcalloc : Z := 0x1f74c.
Definition pc_zcfree : Z := 0x1f75c.
Definition a_zlib_version : Z := 0x2cf70.
Definition ZS_SIZE : Z := 112.
Definition bytes_ok (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.

Definition zstrm_ok (z : zstrm) : Prop :=
  0 <= zs_total_in z < 2 ^ 64 /\ 0 <= zs_total_out z < 2 ^ 64 /\ 0 <= zs_adler z < 2 ^ 64
  /\ - 2 ^ 31 <= zs_data_type z < 2 ^ 31.
Definition zs_delta (zc : ZCall) (r : ZRet) : Prop :=
  zs_total_out (zr_strm r) = wrap64 (zs_total_out (zc_strm zc) + zlength (zr_output r))
  \/ (zr_rc r = Z_MEM_ERROR /\ zs_total_out (zr_strm r) = zs_total_out (zc_strm zc)).

Definition CH : Type := option (blk * (Z -> Z)).
Definition hooks_pure : zhooks CH :=
  mkHooks (fun _ _ => fun ch : CH => MRet (ch, ch)) (fun _ => fun ch : CH => MRet (tt, ch)).
Definition ipure {A} (m : SM CH A) (ch : CH) : option A :=
  match m ch with MRet p => Some (fst p) | _ => None end.

Section ZApi.

  Variable DS : Type.
Variable IS : Type.
Variable D : deflate_api DS.
Variable I : inflate_api IS.
  Variable garb : blk -> Z -> Z.
  Variable dblocks : DS -> list (blk * Z).
  Variable iblocks : IS -> list (blk * Z).
  Definition HOOK_DEPTH : Z := 65536.

  Definition Wstrm (strm : Z) : Z -> Prop := fun z => strm <= z < strm + ZS_SIZE.
  Definition Wstrm_out (strm pout n : Z) : Z -> Prop :=
    fun z => (strm <= z < strm + ZS_SIZE) \/ (pout <= z < pout + n).

  Definition Wc2 (pdl dest n : Z) : Z -> Prop :=
    fun z => (pdl <= z < pdl + 8) \/ (dest <= z < dest + n).
  Variable draw : DS -> list blk.
  Variable iraw : IS -> list blk.
  Variable DEQ : DS -> DS -> Prop.
  Variable IEQ : IS -> IS -> Prop.

  Definition deflate_deq_stmt : Prop :=
    forall ds1 ds2 zc f, DEQ ds1 ds2 ->
      snd (da_deflate D ds1 zc f) = snd (da_deflate D ds2 zc f)
      /\ DEQ (fst (da_deflate D ds1 zc f)) (fst (da_deflate D ds2 zc f)).

End ZApi.
