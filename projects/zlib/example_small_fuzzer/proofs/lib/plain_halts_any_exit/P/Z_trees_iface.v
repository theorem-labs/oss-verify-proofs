(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.

Module Z_fw_model.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation b0 := (Z_to_bv 8 0).


Lemma av8_fill0 : forall a N ofs n, 0 <= ofs -> 0 <= n -> ofs + n <= N -> N <= arr_len a ->
  av8 (arr_fill a ofs n 0) N = firstn (Z.to_nat ofs) (av8 a N) ++ repeat b0 (Z.to_nat n) ++ skipn (Z.to_nat (ofs + n)) (av8 a N).
Proof.
  intros a N ofs n Ho Hn HN HL. apply list_ext_nth.
  - rewrite !length_app, length_firstn, repeat_length, length_skipn, !av8_length. lia.
  - intros k Hk. rewrite av8_length in Hk.
    replace k with (Z.to_nat (Z.of_nat k)) at 1 by lia. rewrite av8_nth by lia. rewrite arr_get_fill. unfold arr_inb.
    destruct (Z_lt_le_dec (Z.of_nat k) ofs) as [C1|C1].
    + replace ((ofs <=? Z.of_nat k) && (Z.of_nat k <? ofs + Z.max 0 n) && ((0 <=? Z.of_nat k) && (Z.of_nat k <? arr_len a))) with false
        by (symmetry; rewrite !andb_false_iff, !Z.leb_gt; lia).
      rewrite nth_error_app1 by (rewrite length_firstn, av8_length; lia).
      rewrite nth_error_firstn. destruct (Nat.ltb_spec k (Z.to_nat ofs)); [|lia].
      replace k with (Z.to_nat (Z.of_nat k)) at 2 by lia. rewrite av8_nth by lia. reflexivity.
    + rewrite nth_error_app2 by (rewrite length_firstn, av8_length; lia).
      rewrite length_firstn, av8_length. replace (Init.Nat.min (Z.to_nat ofs) (Z.to_nat N)) with (Z.to_nat ofs) by lia.
      destruct (Z_lt_le_dec (Z.of_nat k) (ofs + n)) as [C2|C2].
      * replace ((ofs <=? Z.of_nat k) && (Z.of_nat k <? ofs + Z.max 0 n) && ((0 <=? Z.of_nat k) && (Z.of_nat k <? arr_len a))) with true
          by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
        rewrite nth_error_app1 by (rewrite repeat_length; lia).
        rewrite (nth_error_nth' _ b0) by (rewrite repeat_length; lia). rewrite nth_repeat. reflexivity.
      * replace ((ofs <=? Z.of_nat k) && (Z.of_nat k <? ofs + Z.max 0 n) && ((0 <=? Z.of_nat k) && (Z.of_nat k <? arr_len a))) with false
          by (symmetry; rewrite !andb_false_iff, !Z.leb_gt, !Z.ltb_ge; lia).
        rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length, nth_error_skipn.
        replace (Z.to_nat (ofs + n) + (k - Z.to_nat ofs - Z.to_nat n))%nat with (Z.to_nat (Z.of_nat k)) by lia. rewrite av8_nth by lia. reflexivity.
Qed.

Lemma arr_upd_1 : forall (a : arr) i v, arr_upd a i [v] = arr_set a i v.
Proof. intros. reflexivity. Qed.


Definition fw_more0 (d : deflate_state) : Z := ds_window_size d - ds_lookahead d - ds_strstart d.
Definition slide_cond (d : deflate_state) : bool := 65274 <=? ds_strstart d.
Definition fwA (d : deflate_state) : deflate_state := if slide_cond d then fw_slide d 32768 (fw_more d) else d.
Definition moreA (d : deflate_state) : Z := if slide_cond d then fw_more0 d + 32768 else fw_more0 d.
Definition fwB (s1 : deflate_state) (more : Z) : deflate_state :=
  if cs_avail_in (ds_strm s1) =? 0 then s1
  else let r := read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) more in
       fw_insert (set_lookahead (fst r) (ds_lookahead (fst r) + snd r)).

Definition rb_len (s : deflate_state) (more : Z) : Z :=
  let len := cs_avail_in (ds_strm s) in if more <? len then more else len.

Lemma read_buf_small : forall s off more, let r := read_buf s (RB_window off) more in
  snd r = rb_len s more /\ cs_avail_in (ds_strm (fst r)) = cs_avail_in (ds_strm s) - rb_len s more
  /\ ds_lookahead (fst r) = ds_lookahead s /\ ds_strstart (fst r) = ds_strstart s /\ ds_insert (fst r) = ds_insert s
  /\ ds_high_water (fst r) = ds_high_water s /\ ds_window_size (fst r) = ds_window_size s.
Proof.
  intros s off more. cbv zeta. unfold read_buf, rb_len. cbv zeta.
  destruct ((if more <? cs_avail_in (ds_strm s) then more else cs_avail_in (ds_strm s)) =? 0) eqn:E.
  - apply Z.eqb_eq in E. rewrite E. cbn [fst snd]. repeat split; try reflexivity. lia.
  - dsred. destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; dsred; repeat split; reflexivity.
Qed.

Definition fw_ins0 (s : deflate_state) : deflate_state :=
  if MIN_MATCH <=? ds_lookahead s + ds_insert s then
    let str := ds_strstart s - ds_insert s in
    set_ins_h (set_ins_h s (arr_get (ds_window s) str)) (update_hash (set_ins_h s (arr_get (ds_window s) str)) (arr_get (ds_window s) str) (arr_get (ds_window s) (str + 1)))
  else s.
Lemma fw_insert_0 : forall s, ds_insert s = 0 -> fw_insert s = fw_ins0 s.
Proof.
  intros s INS. unfold fw_insert, fw_ins0. destruct (MIN_MATCH <=? ds_lookahead s + ds_insert s); [| reflexivity].
  dsred. rewrite INS. cbn [Z.to_nat fill_window_insert]. reflexivity.
Qed.

Section ONE.
  Variable d : deflate_state.
  Hypothesis FW : fw_wf 32768 32768 d.
  Hypothesis INS : ds_insert d = 0.
  Hypothesis AI : cs_avail_in (ds_strm d) <= 1.

  Lemma fw_more_eq : fw_more d = fw_more0 d /\ 0 <= fw_more0 d <= 65536.
  Proof.
    pose proof (wf_wsz _ _ _ FW) as W2. pose proof (wf_sl _ _ _ FW) as SL. pose proof (wf_look _ _ _ FW) as LK. pose proof (wf_ins _ _ _ FW) as IN.
    unfold fw_more, fw_more0. rewrite W2 in *. split; [apply wrap32_id; lia| lia].
  Qed.

  Lemma fwA_facts : fw_wf 32768 32768 (fwA d) /\ ds_insert (fwA d) = 0 /\ ds_wrap (fwA d) = ds_wrap d /\ ds_strm (fwA d) = ds_strm d
    /\ ds_high_water (fwA d) = ds_high_water d
    /\ moreA d = ds_window_size (fwA d) - ds_lookahead (fwA d) - ds_strstart (fwA d) /\ 0 <= moreA d < 2 ^ 32
    /\ (moreA d = 0 -> 262 < ds_lookahead (fwA d)).
  Proof.
    destruct fw_more_eq as [EM RM].
    pose proof (wf_wsz _ _ _ FW) as W2. pose proof (wf_sl _ _ _ FW) as SL. pose proof (wf_look _ _ _ FW) as LK. pose proof (wf_ins _ _ _ FW) as IN.
    unfold fwA, moreA, slide_cond. destruct (Z.leb_spec 65274 (ds_strstart d)) as [C|C].
    - destruct (fw_slide_wf 32768 32768 d (fw_more d) FW ltac:(lia) ltac:(rewrite EM; unfold fw_more0; lia)) as (W' & (C1 & C2 & C3 & C4) & EL & ES).
      pose proof (wf_wsz _ _ _ W') as W2'.
      assert (EI : ds_insert (fw_slide d 32768 (fw_more d)) = 0).
      { unfold fw_slide. cbv zeta. unfold slide_hash. dsred. rewrite INS.
        destruct (Z.ltb_spec (ds_strstart d - 32768) 0); dsred; [lia| exact INS]. }
      assert (EZ : ds_strm (fw_slide d 32768 (fw_more d)) = ds_strm d /\ ds_high_water (fw_slide d 32768 (fw_more d)) = ds_high_water d).
      { unfold fw_slide. cbv zeta. unfold slide_hash. destruct (_ <? _); dsred; split; reflexivity. }
      destruct EZ as [EZ EH].
      split; [exact W'|]. split; [exact EI|]. split; [exact C2|]. split; [exact EZ|]. split; [exact EH|].
      rewrite W2', EL, ES. unfold fw_more0 in *. rewrite W2 in *. split; [lia|]. split; [lia|]. intros; lia.
    - split; [exact FW|]. split; [exact INS|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      unfold fw_more0 in *. rewrite W2 in *. split; [lia|]. split; [lia|]. intros; lia.
  Qed.

  Theorem fill_window_eq1 : fill_window d = fill_window_high (fwB (fwA d) (moreA d)).
  Proof.
    destruct fw_more_eq as [EM RM]. destruct fwA_facts as (W' & I' & _ & EZ & _ & EMA & RMA & ZLA).
    pose proof (wf_ws _ _ _ FW) as W1. pose proof (wf_ai _ _ _ W') as RA.
    unfold fill_window. rewrite W1. change 263%nat with (S 262). rewrite fill_window_loop_step, fill_window_body_eq.
    rewrite W1. change (32768 + (32768 - MIN_LOOKAHEAD)) with 65274.
    assert (E1 : (if 65274 <=? ds_strstart d then (fw_slide d 32768 (fw_more d), wrap32 (fw_more d + 32768)) else (d, fw_more d)) = (fwA d, moreA d)).
    { unfold fwA, moreA, slide_cond. destruct (65274 <=? ds_strstart d); rewrite EM; [| reflexivity].
      f_equal. apply wrap32_id. pose proof (wf_sl _ _ _ FW). pose proof (wf_wsz _ _ _ FW). unfold fw_more0 in *. lia. }
    rewrite E1. unfold fwB. f_equal.
    destruct (Z.eqb_spec (cs_avail_in (ds_strm (fwA d))) 0) as [A0|A1]; [reflexivity|].
    destruct (read_buf_small (fwA d) (ds_strstart (fwA d) + ds_lookahead (fwA d)) (moreA d)) as (R1 & R2 & R3 & R4 & R5 & _).
    destruct (read_buf (fwA d) (RB_window (ds_strstart (fwA d) + ds_lookahead (fwA d))) (moreA d)) as [s2 n]. cbn [fst snd] in *.
    rewrite (fw_insert_0 (set_lookahead s2 (ds_lookahead s2 + n))) by (dsred; rewrite R5; exact I').
    assert (EL2 : ds_lookahead (fw_ins0 (set_lookahead s2 (ds_lookahead s2 + n))) = ds_lookahead s2 + n
                  /\ cs_avail_in (ds_strm (fw_ins0 (set_lookahead s2 (ds_lookahead s2 + n)))) = cs_avail_in (ds_strm s2)).
    { unfold fw_ins0. lazymatch goal with |- context [if ?c then _ else _] => destruct c end; dsred; split; reflexivity. }
    destruct EL2 as [EL2 EA2]. rewrite EL2, EA2, R2, R3, R1.
    assert (A1' : cs_avail_in (ds_strm (fwA d)) = 1) by (rewrite EZ in *; lia).
    unfold rb_len. rewrite A1'.
    destruct (Z.ltb_spec (moreA d) 1) as [M0|M1].
    - specialize (ZLA ltac:(lia)). replace (ds_lookahead (fwA d) + moreA d <? MIN_LOOKAHEAD) with false by (symmetry; apply Z.ltb_ge; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; lia).
      reflexivity.
    - rewrite Z.sub_diag. cbn [Z.eqb negb andb]. rewrite andb_false_r. reflexivity.
  Qed.
End ONE.


Lemma arr_slice_1 : forall (a : arr) i, arr_slice a i 1 = [arr_get a i].
Proof. intros. reflexivity. Qed.

Definition rb1_strm (s : deflate_state) (b : Z) : cstrm :=
  let st := ds_strm s in
  let st1 := cset_avail_in st (cs_avail_in st - 1) in
  let st2 := if ds_wrap s =? 1 then cset_adler st1 (adler32_len1 (cs_adler st) b) else st1 in
  cset_total_in (cset_next_in st2 (cs_next_in st + 1)) (wrap64 (cs_total_in st + 1)).

Lemma read_buf_eq1 : forall s off more, cs_avail_in (ds_strm s) = 1 -> 1 <= more -> ds_wrap s <> 2 ->
  read_buf s (RB_window off) more
  = (set_strm (set_window s (arr_set (ds_window s) off (arr_get (cs_input (ds_strm s)) (cs_next_in (ds_strm s)))))
              (rb1_strm s (arr_get (cs_input (ds_strm s)) (cs_next_in (ds_strm s)))), 1).
Proof.
  intros s off more A1 M1 W2. unfold read_buf, rb1_strm. rewrite A1.
  replace (more <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.eqb Pos.eqb].
  dsred. rewrite arr_slice_1, arr_upd_1. cbn [adler32_upd].
  destruct (Z.eqb_spec (ds_wrap s) 1) as [E1|E1]; [reflexivity|].
  replace (ds_wrap s =? 2) with false by (symmetry; apply Z.eqb_neq; exact W2). reflexivity.
Qed.

Lemma fwB_0 : forall s1 more, cs_avail_in (ds_strm s1) = 0 -> fwB s1 more = s1.
Proof. intros s1 more A0. unfold fwB. rewrite A0. reflexivity. Qed.

Lemma fwB_n : forall s1 more, cs_avail_in (ds_strm s1) = 1 -> more = 0 -> ds_insert s1 = 0 ->
  fwB s1 more = fw_ins0 (set_lookahead s1 (ds_lookahead s1 + 0)).
Proof.
  intros s1 more A1 M0 I0. unfold fwB. rewrite A1. cbn [Z.eqb Pos.eqb]. subst more.
  unfold read_buf. rewrite A1. cbn [Z.ltb Z.eqb fst snd]. apply fw_insert_0. dsred. exact I0.
Qed.

Lemma fwB_1 : forall s1 more, cs_avail_in (ds_strm s1) = 1 -> 1 <= more -> ds_insert s1 = 0 -> ds_wrap s1 <> 2 ->
  fwB s1 more
  = fw_ins0 (set_lookahead
      (set_strm (set_window s1 (arr_set (ds_window s1) (ds_strstart s1 + ds_lookahead s1) (arr_get (cs_input (ds_strm s1)) (cs_next_in (ds_strm s1)))))
                (rb1_strm s1 (arr_get (cs_input (ds_strm s1)) (cs_next_in (ds_strm s1)))))
      (ds_lookahead s1 + 1)).
Proof.
  intros s1 more A1 M1 I0 W2. unfold fwB. rewrite A1. cbn [Z.eqb Pos.eqb].
  rewrite (read_buf_eq1 s1 _ more A1 M1 W2). cbn [fst snd]. rewrite fw_insert_0 by (dsred; exact I0). dsred. reflexivity.
Qed.

Definition fwh_init_a (s : deflate_state) : Z :=
  let curr := ds_strstart s + ds_lookahead s in let init := ds_window_size s - curr in if WIN_INIT <? init then WIN_INIT else init.
Definition fwh_init_b (s : deflate_state) : Z :=
  let curr := ds_strstart s + ds_lookahead s in let init := curr + WIN_INIT - ds_high_water s in
  if ds_window_size s - ds_high_water s <? init then ds_window_size s - ds_high_water s else init.

Lemma fwh_none : forall s, ds_window_size s <= ds_high_water s -> fill_window_high s = s.
Proof. intros s H. unfold fill_window_high. replace (ds_high_water s <? ds_window_size s) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma fwh_a : forall s, ds_high_water s < ds_window_size s -> ds_high_water s < ds_strstart s + ds_lookahead s -> 0 <= fwh_init_a s < 2 ^ 32 ->
  fill_window_high s = set_high_water (set_window s (arr_fill (ds_window s) (ds_strstart s + ds_lookahead s) (fwh_init_a s) 0))
                                       (ds_strstart s + ds_lookahead s + fwh_init_a s).
Proof.
  intros s H1 H2 H3. unfold fill_window_high, fwh_init_a in *.
  replace (ds_high_water s <? ds_window_size s) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (ds_high_water s <? ds_strstart s + ds_lookahead s) with true by (symmetry; apply Z.ltb_lt; lia).
  cbv zeta. rewrite wrap32_id by lia. reflexivity.
Qed.

Lemma fwh_b : forall s, ds_high_water s < ds_window_size s -> ds_strstart s + ds_lookahead s <= ds_high_water s ->
  ds_high_water s < ds_strstart s + ds_lookahead s + WIN_INIT -> 0 <= fwh_init_b s < 2 ^ 32 ->
  fill_window_high s = set_high_water (set_window s (arr_fill (ds_window s) (ds_high_water s) (fwh_init_b s) 0)) (ds_high_water s + fwh_init_b s).
Proof.
  intros s H1 H2 H3 H4. unfold fill_window_high, fwh_init_b in *.
  replace (ds_high_water s <? ds_window_size s) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (ds_high_water s <? ds_strstart s + ds_lookahead s) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (ds_high_water s <? ds_strstart s + ds_lookahead s + WIN_INIT) with true by (symmetry; apply Z.ltb_lt; lia).
  cbv zeta. rewrite wrap32_id by lia. reflexivity.
Qed.

Lemma fwh_c : forall s, ds_high_water s < ds_window_size s -> ds_strstart s + ds_lookahead s + WIN_INIT <= ds_high_water s -> fill_window_high s = s.
Proof.
  intros s H1 H2. unfold fill_window_high.
  replace (ds_high_water s <? ds_window_size s) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (ds_high_water s <? ds_strstart s + ds_lookahead s) with false by (symmetry; apply Z.ltb_ge; unfold WIN_INIT, MAX_MATCH in H2; lia).
  replace (ds_high_water s <? ds_strstart s + ds_lookahead s + WIN_INIT) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End Z_fw_model.

Module Z_tr_bt_iface.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require GenBitlenModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).

Definition Z_BUILD_TREE : Z := 0x1b8d0.
Definition Z_BT_STACK : Z := 144.
Definition bt_desc (t : tree_id) : Z := match t with TL => 2904 | TD => 2928 | TB => 2952 end.

Definition build_tree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (t : tree_id) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (dl_As L + 212, dl_As L + DS_SIZE)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ DST m' L (build_tree s t).

Definition build_tree_stmt : Prop :=
  forall (L : dlay) (s : deflate_state) (t : tree_id) (lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv psegs m -> relro_clean m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_BT_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) ->
  bt_safe s t ->
  a0 = wz (dl_As L) -> a1 = wz (dl_As L + bt_desc t) ->
  evt psegs (build_tree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s t lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_BUILD_TREE) fc None m (seg_rom psegs)).
End Z_tr_bt_iface.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).

Definition Z_TR_INIT : Z := 0x1a9d4.
Definition Z_TR_FLUSH_BITS : Z := 0x1ad18.
Definition Z_TR_FLUSH_BLOCK : Z := 0x1af1c.
Definition Z_TRFB_STACK : Z := 512.


Definition tr_init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L, dl_As L + DS_SIZE)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ DST m' L (tr_init s).

Definition tr_init_stmt : Prop :=
  forall (L : dlay) (s : deflate_state)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DSTi m L s -> mem_inv psegs m ->
  a0 = wz (dl_As L) ->
  evt psegs (tr_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_TR_INIT) fc None m (seg_rom psegs)).


Definition tr_flush_bits_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ DST m' L (tr_flush_bits s).

Definition tr_flush_bits_stmt : Prop :=
  forall (L : dlay) (s : deflate_state)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv psegs m ->
  BINV DS_PEND s -> ds_pending (tr_flush_bits s) <= DS_PEND ->
  a0 = wz (dl_As L) ->
  evt psegs (tr_flush_bits_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_TR_FLUSH_BITS) fc None m (seg_rom psegs)).


Definition fb_buf_ok (buf : option Z) (len : Z) : Prop :=
  match buf with Some off => 0 <= off /\ off + len <= 65536 | None => True end.

Definition tr_flush_block_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (buf : option Z) (len last : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ DREP m' L (tr_flush_block s buf len last).

Definition tr_flush_block_stmt : Prop :=
  forall (L : dlay) (s : deflate_state) (buf : option Z) (len last lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DREP m L s -> mem_inv psegs m -> relro_clean m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_TRFB_STACK -> bv_unsigned sp mod 16 = 0 ->
  dlay_below L lo (bv_unsigned sp) ->
  BINV DS_PEND s -> fb_safe s buf len last -> fb_buf_ok buf len -> 0 <= len < 2^64 -> 0 <= last <= 1 ->
  a0 = wz (dl_As L) -> a1 = wz (match buf with Some off => dl_Aw L + off | None => 0 end) -> a2 = wz len -> a3 = wz last ->
  evt psegs (tr_flush_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s buf len last lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_TR_FLUSH_BLOCK) fc None m (seg_rom psegs)).
