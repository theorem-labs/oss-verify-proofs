(** * Bridge.DEmit.DStTrip — pair D13 ([deflate_stored]), part 2: one trip of the loop at [Z_FINISH].

    S5's [deflate_stored_body] (split by its own [RefDeflStored6] as
    header check, break test, [st_emit1], [st_copy], [st_rdo]) against RT's
    [dst_step]: the same break flag and [last], [sti] kept, and a trip that
    does not break spends at least the five header bytes of output (the
    measure the loop file aligns the two fuels with).

    The three phases each keep [sti]:
    - [sti_emit]: the empty stored block, its patched length bytes, the flush;
    - [sti_lcopy]: the bytes still in the window go straight to the output;
    - [sti_rdo]: the rest is read from the input straight to the output
      (group M's [dm_read_buf_next_out]).

    Ownership: a worker (group D).  Reviewer: a worker. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees DeflateLz DeflateBlk
  RefDeflStored2 RefDeflStored4 RefDeflStored6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits BrFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs BrDFlush DTrStored DZHeader DStKit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require MReadBuf DMatchIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module B6 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored6.

(* ------------------------------------------------------------------------- *)
(* 1.  Small facts                                                           *)
(* ------------------------------------------------------------------------- *)

Lemma fin_eq_rt : (Z_FINISH =? Base.Z_FINISH) = true. Proof. reflexivity. Qed.
Lemma fin_nf_rt : (Z_FINISH =? Base.Z_NO_FLUSH) = false. Proof. reflexivity. Qed.
Lemma fin_eq_s5 : (Z_FINISH =? Z_FINISH) = true. Proof. reflexivity. Qed.
Lemma fin_nf_s5 : (Z_FINISH =? Z_NO_FLUSH) = false. Proof. reflexivity. Qed.

Lemma zlen_done_rel : forall s t po pi, dst_rel s t po pi ->
  RC.zlen (RD.zs_done (RD.d_strm t)) = RC.zlen pi + DS.cs_next_in (DS.ds_strm s).
Proof.
  intros s t po pi (_ & _ & _ & _ & _ & H). unfold strm_rel in H. cbv zeta in H.
  destruct H as (Hni & _ & _ & _ & _ & Hd & _). rewrite Hd.
  change RC.zlen with (@zlength Z). rewrite zlength_app, arr_slice_length. lia.
Qed.

(** Case on every [a <? b] of the goal, innermost first (a comparison whose
    sides hold an [if] waits until those are resolved). *)
Ltac ltb_cases :=
  repeat match goal with
  | |- context [?a <? ?b] =>
      lazymatch a with context [if _ then _ else _] => fail | _ =>
      lazymatch b with context [if _ then _ else _] => fail | _ =>
        destruct (Z.ltb_spec a b); cbv beta iota end end
  end.

Lemma min3_eq : forall X H,
  (if H <? (if X <? 65535 then X else 65535) then H else (if X <? 65535 then X else 65535))
  = RD.zmin RD.MAX_STORED (RD.zmin X H).
Proof. intros X H. unfold RD.zmin, RD.MAX_STORED. ltb_cases; lia. Qed.

Lemma zmin_facts : forall X H, 0 <= X -> 0 <= H ->
  0 <= RD.zmin RD.MAX_STORED (RD.zmin X H) <= 65535
  /\ RD.zmin RD.MAX_STORED (RD.zmin X H) <= X /\ RD.zmin RD.MAX_STORED (RD.zmin X H) <= H.
Proof.
  intros X H HX HH. unfold RD.zmin, RD.MAX_STORED. ltb_cases; lia.
Qed.

Lemma rt_counters_eq : forall t st o n,
  RD.setD_strm (RD.setZ_availout (RD.zs_availout (RD.d_strm (RD.setD_strm (RD.setZ_out o st) t)) - n)
                  (RD.setZ_totalout (RD.zs_totalout (RD.d_strm (RD.setD_strm (RD.setZ_out o st) t)) + n)
                     (RD.d_strm (RD.setD_strm (RD.setZ_out o st) t))))
               (RD.setD_strm (RD.setZ_out o st) t)
  = RD.setD_strm (RD.setZ_out o (RD.setZ_availout (RD.zs_availout st - n)
                                  (RD.setZ_totalout (RD.zs_totalout st + n) st))) t.
Proof. intros t st o n. destruct t, st. reflexivity. Qed.

Ltac rt_view :=
  cbn [RD.d_cfg RD.d_status RD.d_wrap RD.d_lastflush RD.d_ts RD.d_ls RD.d_strm RD.setD_ls RD.setD_strm
       RD.setD_ts RD.setL_blockstart RD.ls_windowsize RD.ls_blockstart RD.ls_strstart RD.ls_window
       RD.ls_insert RD.ls_highwater RD.setZ_out RD.setZ_availout RD.setZ_totalout RD.zs_done RD.zs_in
       RD.zs_totalin].
Ltac rt_view_in H :=
  cbn [RD.d_cfg RD.d_status RD.d_wrap RD.d_lastflush RD.d_ts RD.d_ls RD.d_strm RD.setD_ls RD.setD_strm
       RD.setD_ts RD.setL_blockstart RD.ls_windowsize RD.ls_blockstart RD.ls_strstart RD.ls_window
       RD.ls_insert RD.ls_highwater RD.setZ_out RD.setZ_availout RD.setZ_totalout RD.zs_done RD.zs_in
       RD.zs_totalin] in H.

(* ------------------------------------------------------------------------- *)
(* 2.  The three phases                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma sti_emit : forall s t pre_out pre_in last len,
  sti s t pre_out pre_in -> 5 <= DS.cs_avail_out (DS.ds_strm s) ->
  let ts1 := RT.tr_stored_block [] 0 last (RD.d_ts t) in
  let x := DL.flush_pending (B2.sb_patch (DT.tr_stored_block s None 0 last) len) in
  let t1 := RD.flush_pending
              (RD.setD_ts (RT.set_bw {| ZBitsOut.bw_out := RD.patch_len4 len (ZBitsOut.bw_out (RT.ts_bw ts1));
                                        ZBitsOut.bw_buf := ZBitsOut.bw_buf (RT.ts_bw ts1);
                                        ZBitsOut.bw_valid := ZBitsOut.bw_valid (RT.ts_bw ts1) |} ts1) t) in
  sti x t1 pre_out pre_in
  /\ RD.d_ls t1 = RD.d_ls t
  /\ DS.cs_avail_out (DS.ds_strm x) = DS.cs_avail_out (DS.ds_strm s) - 5
  /\ DS.cs_input (DS.ds_strm x) = DS.cs_input (DS.ds_strm s)
  /\ DS.cs_next_in (DS.ds_strm x) = DS.cs_next_in (DS.ds_strm s)
  /\ DS.cs_avail_in (DS.ds_strm x) = DS.cs_avail_in (DS.ds_strm s).
Proof.
  intros s t pre_out pre_in last len Si Ha. cbv zeta.
  destruct Si as [Hrel Hp Hpo Hbv Hsn Hao Hto Hroom Hc Hrb Hwsz Hbs Hss Hdone Hinl Hwin Hins].
  destruct (rel_view _ _ _ _ Hrel Hc) as (_ & _ & Epbl & _).
  destruct (tsb_hdr s last Hbv Hp) as (P1 & V1).
  pose proof (bw4_tr_stored_block s None 0 last ltac:(lia)) as F1.
  destruct (bw4_proj _ _ F1) as (_ & Est1 & _ & _).
  assert (L1 : arr_len (DS.ds_pending_buf (DT.tr_stored_block s None 0 last)) = 65536)
    by (destruct F1 as (_ & L & _); lia).
  destruct (pair_tr_stored_block s t pre_out pre_in None 0 last [] Hrel Hsn Hpo ltac:(lia) ltac:(lia)
              (conj eq_refl eq_refl)) as (H1 & Hpo1 & Hsn1).
  clear F1.
  revert H1 Hpo1 Hsn1 P1 V1 Est1 L1.
  generalize (DT.tr_stored_block s None 0 last) as x1.
  generalize (RT.tr_stored_block [] 0 last (RD.d_ts t)) as ts1.
  intros ts1 x1 H1 Hpo1 Hsn1 P1 V1 Est1 L1.
  pose proof (dst_patch x1 t ts1 len pre_out pre_in H1 Hsn1 Hpo1 ltac:(lia)) as H2.
  destruct (patch_frame x1 len) as (Pp & Ppo & Pbv & Psn & Pst & Plen).
  revert H2 Pp Ppo Pbv Psn Pst Plen.
  generalize (B2.sb_patch x1 len) as x2.
  generalize (RT.set_bw {| ZBitsOut.bw_out := RD.patch_len4 len (ZBitsOut.bw_out (RT.ts_bw ts1));
                           ZBitsOut.bw_buf := ZBitsOut.bw_buf (RT.ts_bw ts1);
                           ZBitsOut.bw_valid := ZBitsOut.bw_valid (RT.ts_bw ts1) |} ts1) as ts2.
  intros ts2 x2 H2 Pp Ppo Pbv Psn Pst Plen.
  assert (Hst2 : DS.ds_strm x2 = DS.ds_strm s) by congruence.
  assert (Hok2 : fp_ok x2) by (unfold fp_ok; rewrite Hst2, Plen, L1; lia).
  assert (Hfr2 : flush_room x2) by (left; lia).
  assert (Hsn2 : DS.ds_sym_next x2 = 0) by congruence.
  pose proof (dst_flush_pending x2 _ pre_out pre_in H2 Hsn2 Hfr2 Hok2) as H3.
  destruct (s5_flush_all x2 ltac:(lia) ltac:(congruence) ltac:(lia) ltac:(rewrite Hst2; lia))
    as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  destruct (flush_pending_strm_in x2) as (I1 & I2 & I3 & _).
  destruct (rt_flush_pending_frame (RD.setD_ts ts2 t)) as (G1 & _ & _ & G4 & G5 & G6 & G7 & G8 & _).
  cbn [RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.setD_ts] in G1, G4, G5, G6, G7, G8.
  revert H3 Q1 Q2 Q3 Q4 Q5 Q6 Q7 I1 I2 I3 G1 G4 G5 G6 G7 G8.
  generalize (DL.flush_pending x2) as x3. generalize (RD.flush_pending (RD.setD_ts ts2 t)) as t3.
  intros t3 x3 H3 Q1 Q2 Q3 Q4 Q5 Q6 Q7 I1 I2 I3 G1 G4 G5 G6 G7 G8.
  rewrite Hst2, Pp, P1 in Q5. rewrite Hst2, Pp, P1 in Q6. rewrite wrap64_id in Q6 by lia.
  rewrite Hst2 in I1, I2, I3.
  split; [|split; [exact G5|split; [lia|split; [exact I1|split; [exact I2|exact I3]]]]].
  constructor.
  - exact H3.
  - exact Q1.
  - exact Q2.
  - lia.
  - congruence.
  - lia.
  - lia.
  - rewrite Q5, Q6, Q7, Plen, L1. lia.
  - rewrite G1. exact Hc.
  - apply (rb_ok_frame t t3); [exact G4 | exact G6 | exact G8 | exact Hrb].
  - rewrite G5. exact Hwsz.
  - rewrite G5. exact Hbs.
  - rewrite G5. exact Hss.
  - rewrite G5, G7. exact Hdone.
  - rewrite G7, G6. exact Hinl.
  - rewrite G5. exact Hwin.
  - rewrite G5. exact Hins.
Qed.

Lemma sti_lcopy : forall s t pre_out pre_in k,
  sti s t pre_out pre_in -> 0 <= k <= RD.ls_strstart (RD.d_ls t) - RD.ls_blockstart (RD.d_ls t) ->
  k <= DS.cs_avail_out (DS.ds_strm s) ->
  let t' := RD.setD_ls (RD.setL_blockstart (RD.ls_blockstart (RD.d_ls t) + k) (RD.d_ls t))
              (RD.setD_strm (RD.setZ_out (RD.zs_out (RD.d_strm t)
                                          ++ RD.win_take (RD.ls_window (RD.d_ls t)) (RD.ls_blockstart (RD.d_ls t)) k)
                               (RD.setZ_availout (RD.zs_availout (RD.d_strm t) - k)
                                  (RD.setZ_totalout (RD.zs_totalout (RD.d_strm t) + k) (RD.d_strm t)))) t) in
  sti (B4.st_lcopy s k) t' pre_out pre_in
  /\ RD.ls_strstart (RD.d_ls t') = RD.ls_strstart (RD.d_ls t)
  /\ RD.ls_blockstart (RD.d_ls t') = RD.ls_blockstart (RD.d_ls t) + k
  /\ DS.cs_avail_out (DS.ds_strm (B4.st_lcopy s k)) = DS.cs_avail_out (DS.ds_strm s) - k
  /\ DS.cs_input (DS.ds_strm (B4.st_lcopy s k)) = DS.cs_input (DS.ds_strm s)
  /\ DS.cs_next_in (DS.ds_strm (B4.st_lcopy s k)) = DS.cs_next_in (DS.ds_strm s)
  /\ DS.cs_avail_in (DS.ds_strm (B4.st_lcopy s k)) = DS.cs_avail_in (DS.ds_strm s).
Proof.
  intros s t pre_out pre_in k Si Hk Hka. cbv zeta.
  destruct Si as [Hrel Hp Hpo Hbv Hsn Hao Hto Hroom Hc Hrb Hwsz Hbs Hss Hdone Hinl Hwin Hins].
  destruct (rel_view _ _ _ _ Hrel Hc) as (_ & _ & Epbl & _).
  pose proof (dst_lcopy s t pre_out pre_in k Hrel ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as H1.
  assert (Ex : DS.ds_pending (B4.st_lcopy s k) = 0 /\ DS.ds_pending_out (B4.st_lcopy s k) = 0
               /\ DS.ds_bi_valid (B4.st_lcopy s k) = 0 /\ DS.ds_sym_next (B4.st_lcopy s k) = 0
               /\ arr_len (DS.ds_pending_buf (B4.st_lcopy s k)) = arr_len (DS.ds_pending_buf s)
               /\ DS.cs_avail_out (DS.ds_strm (B4.st_lcopy s k)) = DS.cs_avail_out (DS.ds_strm s) - k
               /\ DS.cs_total_out (DS.ds_strm (B4.st_lcopy s k)) = DS.cs_total_out (DS.ds_strm s) + k
               /\ DS.cs_input (DS.ds_strm (B4.st_lcopy s k)) = DS.cs_input (DS.ds_strm s)
               /\ DS.cs_next_in (DS.ds_strm (B4.st_lcopy s k)) = DS.cs_next_in (DS.ds_strm s)
               /\ DS.cs_avail_in (DS.ds_strm (B4.st_lcopy s k)) = DS.cs_avail_in (DS.ds_strm s)).
  { unfold B4.st_lcopy. autorewrite with s5f_block_start s5f_strm s5c_total_out s5c_avail_out s5c_emit.
    unfold DS.cs_emit. autorewrite with s5c_out_rev. rewrite wrap64_id by lia.
    and_goal; first [assumption | reflexivity | lia]. }
  destruct Ex as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  split; [|split; [reflexivity|split; [reflexivity|split; [exact X6|split; [exact X8|split; [exact X9|exact X10]]]]]].
  apply mkSti; [exact H1 | rt_view; try first [assumption | lia
    | apply (rb_ok_frame t); [reflexivity | reflexivity | reflexivity | exact Hrb]] ..].
Qed.

Lemma sti_rdo : forall s t pre_out pre_in n,
  sti s t pre_out pre_in -> 0 < n <= DS.cs_avail_out (DS.ds_strm s) -> n <= DS.cs_avail_in (DS.ds_strm s) ->
  let r := RD.read_buf (RD.d_wrap t) n (RD.d_strm t) in
  let t' := RD.setD_strm (RD.setZ_out (RD.zs_out (snd r) ++ fst r)
                           (RD.setZ_availout (RD.zs_availout (snd r) - n)
                              (RD.setZ_totalout (RD.zs_totalout (snd r) + n) (snd r)))) t in
  sti (B6.st_rdo s n) t' pre_out pre_in
  /\ RD.d_ls t' = RD.d_ls t
  /\ DS.cs_avail_out (DS.ds_strm (B6.st_rdo s n)) = DS.cs_avail_out (DS.ds_strm s) - n
  /\ DS.cs_input (DS.ds_strm (B6.st_rdo s n)) = DS.cs_input (DS.ds_strm s)
  /\ DS.cs_next_in (DS.ds_strm (B6.st_rdo s n)) + DS.cs_avail_in (DS.ds_strm (B6.st_rdo s n))
     = DS.cs_next_in (DS.ds_strm s) + DS.cs_avail_in (DS.ds_strm s)
  /\ DS.cs_next_in (DS.ds_strm (B6.st_rdo s n)) = DS.cs_next_in (DS.ds_strm s) + n.
Proof.
  intros s t pre_out pre_in n Si Hn Hni. cbv zeta.
  destruct Si as [Hrel Hp Hpo Hbv Hsn Hao Hto Hroom Hc Hrb Hwsz Hbs Hss Hdone Hinl Hwin Hins].
  destruct (rel_view _ _ _ _ Hrel Hc) as (_ & _ & Epbl & _).
  pose proof (zlen_done_rel _ _ _ _ Hrel) as D0.
  destruct (DMatchIface.dm_read_buf_next_out s t pre_out pre_in n Hrel Hrb ltac:(lia)) as (_ & A2 & A3 & _).
  pose proof (MReadBuf.m_s5_read_buf_next_out_eq s n) as E5. cbv zeta in E5.
  replace (Z.min n (DS.cs_avail_in (DS.ds_strm s))) with n in E5 by lia.
  specialize (E5 ltac:(lia)). rewrite E5 in A2. cbn [fst] in A2.
  destruct (rel_view _ _ _ _ Hrel Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & Eai0 & _).
  destruct (MReadBuf.m_s5_rb_strm_fields (DS.ds_strm s) (DS.ds_wrap s) n
              (arr_slice (DS.cs_input (DS.ds_strm s)) (DS.cs_next_in (DS.ds_strm s)) n))
    as (R1 & R2 & R3 & _ & R5 & _ & R7 & _).
  assert (Er : B6.st_rdo s n
               = (let x5 := DS.set_strm s (MReadBuf.s5_rb_strm (DS.ds_strm s) (DS.ds_wrap s) n
                                 (arr_slice (DS.cs_input (DS.ds_strm s)) (DS.cs_next_in (DS.ds_strm s)) n)) in
                  DS.set_strm x5 (DS.cset_total_out (DS.cset_avail_out (DS.ds_strm x5) (DS.cs_avail_out (DS.ds_strm x5) - n))
                                   (wrap64 (DS.cs_total_out (DS.ds_strm x5) + n))))).
  { unfold B6.st_rdo. replace (negb (n =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
    rewrite E5. reflexivity. }
  rewrite Er. cbv zeta. clear Er E5.
  pose proof (dst_counters _ _ pre_out pre_in n A2) as H4.
  specialize (H4 ltac:(autorewrite with s5f_strm; rewrite R7; lia)).
  rewrite rt_counters_eq in H4.
  assert (Hrb' : rb_ok (RD.setD_strm (RD.setZ_out (RD.zs_out (snd (RD.read_buf (RD.d_wrap t) n (RD.d_strm t)))
                                                   ++ fst (RD.read_buf (RD.d_wrap t) n (RD.d_strm t)))
                          (RD.setZ_availout (RD.zs_availout (snd (RD.read_buf (RD.d_wrap t) n (RD.d_strm t))) - n)
                             (RD.setZ_totalout (RD.zs_totalout (snd (RD.read_buf (RD.d_wrap t) n (RD.d_strm t))) + n)
                                (snd (RD.read_buf (RD.d_wrap t) n (RD.d_strm t)))))) t)).
  { apply (rb_ok_frame _ _ eq_refl eq_refl eq_refl A3). }
  pose proof (zlen_done_rel _ _ _ _ H4) as D1.
  pose proof (rel_view _ _ _ _ H4) as V4. rt_view_in V4. specialize (V4 Hc).
  destruct V4 as (_ & _ & _ & _ & _ & _ & _ & _ & Eai1 & _).
  rt_view_in D1. rt_view_in Eai1.
  autorewrite with s5f_strm s5c_total_out s5c_avail_out in D1, Eai1 |- *.
  rewrite R2 in D1. rewrite R3 in Eai1.
  split; [|split; [reflexivity|split; [rewrite R5; lia|split; [exact R1|split; [rewrite R2, R3; lia|rewrite R2; reflexivity]]]]].
  apply mkSti; [exact H4 | autorewrite with s5f_strm s5c_total_out s5c_avail_out; rewrite ?R5, ?R7;
                           rewrite ?wrap64_id by lia; rt_view; try first [assumption | lia | exact Hrb'] ..].
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  One trip                                                              *)
(* ------------------------------------------------------------------------- *)

Ltac trip_brk Si :=
  cbn [fst snd]; split; [reflexivity|]; split; [reflexivity|]; split; [exact Si|];
  split; [intros _; reflexivity|]; split; [intros Hf; discriminate Hf|];
  repeat split; try (symmetry; assumption); try lia.

Theorem st_trip : forall s t pre_out pre_in mb,
  sti s t pre_out pre_in ->
  let r5 := DB.deflate_stored_body s Z_FINISH mb in
  let rR := RD.dst_step Z_FINISH mb t in
  snd r5 = fst (fst rR) /\ snd (fst r5) = snd (fst rR)
  /\ sti (fst (fst r5)) (snd rR) pre_out pre_in
  /\ (snd r5 = true -> snd (fst r5) = 0)
  /\ (snd r5 = false -> DS.cs_avail_out (DS.ds_strm (fst (fst r5))) + 5 <= DS.cs_avail_out (DS.ds_strm s))
  /\ DS.cs_input (DS.ds_strm (fst (fst r5))) = DS.cs_input (DS.ds_strm s)
  /\ DS.cs_next_in (DS.ds_strm (fst (fst r5))) + DS.cs_avail_in (DS.ds_strm (fst (fst r5)))
     = DS.cs_next_in (DS.ds_strm s) + DS.cs_avail_in (DS.ds_strm s)
  /\ RD.ls_strstart (RD.d_ls (snd rR)) = RD.ls_strstart (RD.d_ls t)
  /\ DS.cs_next_in (DS.ds_strm s) <= DS.cs_next_in (DS.ds_strm (fst (fst r5))).
Proof.
  intros s t pre_out pre_in mb Si. cbv zeta.
  pose proof Si as [Hrel Hp Hpo Hbv Hsn Hao Hto Hroom Hc Hrb Hwsz Hbs Hss Hdone Hinl Hwin Hins].
  destruct (rel_view _ _ _ _ Hrel Hc)
    as (_ & _ & _ & _ & _ & Ess & Ebs & _ & Eai & Eao & _ & _ & _ & _ & Ebv).
  rewrite B6.deflate_stored_body_eq. unfold RD.dst_step. cbv zeta.
  assert (Eh5 : B2.sb_hdr s = 5) by (unfold B2.sb_hdr; rewrite Hbv; reflexivity).
  rewrite Eh5, <- Ebv, Hbv, <- Eao. change (Z.shiftr (0 + 42) 3) with 5.
  destruct (Z.ltb_spec (DS.cs_avail_out (DS.ds_strm s)) 5) as [Hlt|Hge]; [trip_brk Si|].
  rewrite <- Ess, <- Ebs, <- Eai.
  assert (HV : 0 <= DS.cs_avail_in (DS.ds_strm s)) by (rewrite Eai; unfold RC.zlen; lia).
  assert (HLV : DS.ds_strstart s - DS.ds_block_start s + DS.cs_avail_in (DS.ds_strm s) < 2 ^ 32) by lia.
  assert (Eleft : B2.sb_left s = DS.ds_strstart s - DS.ds_block_start s)
    by (unfold B2.sb_left; apply wrap32_id; lia).
  assert (Elen : B2.sb_len s = RD.zmin RD.MAX_STORED
                   (RD.zmin (DS.ds_strstart s - DS.ds_block_start s + DS.cs_avail_in (DS.ds_strm s))
                            (DS.cs_avail_out (DS.ds_strm s) - 5))).
  { unfold B2.sb_len, B2.sb_len1. cbv zeta. rewrite Eleft, Eh5.
    rewrite (wrap32_id (DS.ds_strstart s - DS.ds_block_start s + DS.cs_avail_in (DS.ds_strm s))) by lia.
    apply min3_eq. }
  unfold B2.sb_brk, B6.st_emit1, B6.sb_lastv. rewrite !Elen, !Eleft.
  rewrite (wrap32_id (DS.ds_strstart s - DS.ds_block_start s + DS.cs_avail_in (DS.ds_strm s))) by lia.
  rewrite ?fin_eq_rt, ?fin_nf_rt, ?fin_eq_s5, ?fin_nf_s5.
  destruct (zmin_facts (DS.ds_strstart s - DS.ds_block_start s + DS.cs_avail_in (DS.ds_strm s))
              (DS.cs_avail_out (DS.ds_strm s) - 5) ltac:(lia) ltac:(lia)) as (LN1 & LN2 & LN3).
  remember (RD.zmin RD.MAX_STORED
              (RD.zmin (DS.ds_strstart s - DS.ds_block_start s + DS.cs_avail_in (DS.ds_strm s))
                       (DS.cs_avail_out (DS.ds_strm s) - 5))) as LEN eqn:HLEN.
  match goal with |- context [if ?c then (true, 0, t) else _] => destruct c end; [trip_brk Si|].
  remember (if true && (LEN =? DS.ds_strstart s - DS.ds_block_start s + DS.cs_avail_in (DS.ds_strm s))
            then 1 else 0) as LAST eqn:HLAST.
  destruct (sti_emit s t pre_out pre_in LAST LEN Si Hge) as (S1 & G1 & A1 & I1 & N1 & V1).
  revert S1 G1 A1 I1 N1 V1.
  generalize (DL.flush_pending (B2.sb_patch (DT.tr_stored_block s None 0 LAST) LEN)) as x3.
  generalize (RD.flush_pending
                (RD.setD_ts (RT.set_bw
                   {| ZBitsOut.bw_out := RD.patch_len4 LEN (ZBitsOut.bw_out (RT.ts_bw (RT.tr_stored_block [] 0 LAST (RD.d_ts t))));
                      ZBitsOut.bw_buf := ZBitsOut.bw_buf (RT.ts_bw (RT.tr_stored_block [] 0 LAST (RD.d_ts t)));
                      ZBitsOut.bw_valid := ZBitsOut.bw_valid (RT.ts_bw (RT.tr_stored_block [] 0 LAST (RD.d_ts t))) |}
                   (RT.tr_stored_block [] 0 LAST (RD.d_ts t))) t)) as t1.
  intros t1 x3 S1 G1 A1 I1 N1 V1.
  unfold B6.st_copy, B2.lc_len, RD.zmin.
  destruct (Z.eqb_spec (DS.ds_strstart s - DS.ds_block_start s) 0) as [L0|L0]; cbn [negb fst snd].
  - destruct (Z.eqb_spec LEN 0) as [E0|E0].
    + replace (B6.st_rdo x3 LEN) with x3 by (unfold B6.st_rdo; rewrite E0; reflexivity).
      split; [reflexivity|]. split; [reflexivity|]. split; [exact S1|].
      split; [intros Hf; discriminate Hf|]. split; [intros _; lia|]. split; [exact I1|].
      split; [lia|]. split; [rewrite G1; exact (eq_sym Ess)|lia].
    + destruct (sti_rdo x3 t1 pre_out pre_in LEN S1 ltac:(lia) ltac:(lia)) as (S2 & Gr & A2 & I2 & N2 & M2).
      split; [reflexivity|]. split; [reflexivity|]. split; [exact S2|].
      split; [intros Hf; discriminate Hf|]. split; [intros _; lia|]. split; [congruence|].
      split; [lia|]. split; [rewrite Gr, G1; exact (eq_sym Ess)|lia].
  - assert (HK : 0 <= (if LEN <? DS.ds_strstart s - DS.ds_block_start s then LEN
                       else DS.ds_strstart s - DS.ds_block_start s) <= LEN
                 /\ (if LEN <? DS.ds_strstart s - DS.ds_block_start s then LEN
                     else DS.ds_strstart s - DS.ds_block_start s) <= DS.ds_strstart s - DS.ds_block_start s
                 /\ (LEN - (if LEN <? DS.ds_strstart s - DS.ds_block_start s then LEN
                            else DS.ds_strstart s - DS.ds_block_start s) = 0
                     \/ LEN - (if LEN <? DS.ds_strstart s - DS.ds_block_start s then LEN
                               else DS.ds_strstart s - DS.ds_block_start s) <= DS.cs_avail_in (DS.ds_strm s))).
    { destruct (Z.ltb_spec LEN (DS.ds_strstart s - DS.ds_block_start s)); lia. }
    remember (if LEN <? DS.ds_strstart s - DS.ds_block_start s then LEN
              else DS.ds_strstart s - DS.ds_block_start s) as K eqn:EK.
    destruct (sti_lcopy x3 t1 pre_out pre_in K S1 ltac:(rewrite G1, <- Ess, <- Ebs; lia) ltac:(lia))
      as (S2 & Gs & _ & A2 & I2 & N2 & V2).
    revert S2 Gs A2 I2 N2 V2.
    generalize (B4.st_lcopy x3 K) as x4.
    generalize (RD.setD_ls (RD.setL_blockstart (RD.ls_blockstart (RD.d_ls t1) + K) (RD.d_ls t1))
                  (RD.setD_strm (RD.setZ_out (RD.zs_out (RD.d_strm t1)
                                              ++ RD.win_take (RD.ls_window (RD.d_ls t1)) (RD.ls_blockstart (RD.d_ls t1)) K)
                                   (RD.setZ_availout (RD.zs_availout (RD.d_strm t1) - K)
                                      (RD.setZ_totalout (RD.zs_totalout (RD.d_strm t1) + K) (RD.d_strm t1)))) t1)) as t2.
    intros t2 x4 S2 Gs A2 I2 N2 V2.
    destruct (Z.eqb_spec (LEN - K) 0) as [E0|E0].
    + replace (B6.st_rdo x4 (LEN - K)) with x4 by (unfold B6.st_rdo; rewrite E0; reflexivity).
      split; [reflexivity|]. split; [reflexivity|]. split; [exact S2|].
      split; [intros Hf; discriminate Hf|]. split; [intros _; lia|]. split; [congruence|].
      split; [lia|]. split; [rewrite Gs, G1; exact (eq_sym Ess)|lia].
    + destruct (sti_rdo x4 t2 pre_out pre_in (LEN - K) S2 ltac:(lia) ltac:(lia)) as (S3 & Gr & A3 & I3 & N3 & M3).
      split; [reflexivity|]. split; [reflexivity|]. split; [exact S3|].
      split; [intros Hf; discriminate Hf|]. split; [intros _; lia|]. split; [congruence|].
      split; [lia|]. split; [rewrite Gr, Gs, G1; exact (eq_sym Ess)|lia].
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  The loop: the two fuels both suffice                                  *)
(* ------------------------------------------------------------------------- *)

(** A trip that does not break spends five output bytes, so [avail_out / 5 + 1]
    trips reach a break or the last block; S5 runs [avail_out + 1], RT
    [avail_out / 5 + 3]. *)
Theorem st_loop : forall f5 fR s t pre_out pre_in mb,
  sti s t pre_out pre_in ->
  DS.cs_avail_out (DS.ds_strm s) / 5 + 1 <= Z.of_nat f5 ->
  DS.cs_avail_out (DS.ds_strm s) / 5 + 1 <= Z.of_nat fR ->
  let r5 := DB.deflate_stored_loop f5 s Z_FINISH mb in
  let rR := RD.dst_loop fR Z_FINISH mb t in
  snd r5 = fst rR /\ sti (fst r5) (snd rR) pre_out pre_in
  /\ DS.cs_input (DS.ds_strm (fst r5)) = DS.cs_input (DS.ds_strm s)
  /\ DS.cs_next_in (DS.ds_strm (fst r5)) + DS.cs_avail_in (DS.ds_strm (fst r5))
     = DS.cs_next_in (DS.ds_strm s) + DS.cs_avail_in (DS.ds_strm s)
  /\ RD.ls_strstart (RD.d_ls (snd rR)) = RD.ls_strstart (RD.d_ls t)
  /\ DS.cs_next_in (DS.ds_strm s) <= DS.cs_next_in (DS.ds_strm (fst r5)).
Proof.
  induction f5 as [|f IH]; intros fR s t pre_out pre_in mb Si H5 HR; cbv zeta.
  - pose proof (si_aout _ _ _ _ Si). pose proof (Z.div_pos (DS.cs_avail_out (DS.ds_strm s)) 5). lia.
  - destruct fR as [|g].
    + pose proof (si_aout _ _ _ _ Si). pose proof (Z.div_pos (DS.cs_avail_out (DS.ds_strm s)) 5). lia.
    + rewrite B6.sloop_S. cbn [RD.dst_loop].
      pose proof (st_trip s t pre_out pre_in mb Si) as T. cbv zeta in T.
      destruct (DB.deflate_stored_body s Z_FINISH mb) as [[s1 last] broke].
      destruct (RD.dst_step Z_FINISH mb t) as [[brokeR lastR] t1].
      cbn [fst snd] in T. destruct T as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9). subst brokeR lastR.
      destruct broke.
      * cbn [fst snd]. rewrite (T4 eq_refl).
        split; [reflexivity|]. split; [exact T3|]. split; [exact T6|]. split; [exact T7|].
        split; [exact T8|exact T9].
      * specialize (T5 eq_refl). pose proof (si_aout _ _ _ _ T3) as Ha1.
        destruct (Z.eqb_spec last 0) as [L0|L0]; cbn [fst snd].
        -- destruct (IH g s1 t1 pre_out pre_in mb T3 ltac:(lia) ltac:(lia)) as (U1 & U2 & U3 & U4 & U5 & U6).
           split; [exact U1|]. split; [exact U2|]. split; [congruence|]. split; [lia|].
           split; [congruence|lia].
        -- split; [reflexivity|]. split; [exact T3|]. split; [exact T6|]. split; [exact T7|].
           split; [exact T8|exact T9].
Qed.
