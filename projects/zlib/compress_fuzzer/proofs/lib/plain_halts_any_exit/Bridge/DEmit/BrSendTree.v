(** * Bridge.DEmit.BrSendTree — pair D29 (second half) of PAIRS.md: [send_tree], S5 vs RT.

    Both walk the code lengths [0 .. max_code] in runs and emit each run's
    bit-length codes.  S5's [SendModel.send_loop_S] already writes each run
    as [sbs_run] over the calls [st_calls]; RT's [send_go] emits the same
    calls through [send_rep]/[send_code]/[bw_send_bits] ([rt_emit]).  S5's
    safety predicate [send_tree_safe] gives [sbs_ok] for every run, which is
    the room [BrSbs.br_sbs_run] needs.

    As for [scan_tree] ([BrScanTree.scan_cex]), RT's loop fuel is
    [L_CODES + 3], so the statement here adds [max_code < L_CODES] to the
    DTreeIface statement's hypotheses. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel ScanModel SendModel RefSendTree3
  RefSendTree4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Trees ZBitsOut.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs BrSbs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SCM := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.ScanModel.

(* ------------------------------------------------------------------------- *)
(* 1.  One run's calls on RT's side                                          *)
(* ------------------------------------------------------------------------- *)

Definition rblc (bl : RT.Tree) (c : Z) : Z * Z := (RT.t_code bl c, RT.t_len bl c).

(** [SendModel.st_calls] with RT's bit-length tree. *)
Definition rt_calls (bl : RT.Tree) (mn curlen prevlen count : Z) : list (Z * Z) :=
  if count <? mn then repeat (rblc bl curlen) (Z.to_nat count)
  else if negb (curlen =? 0) then
    (if negb (curlen =? prevlen) then [rblc bl curlen] else [])
      ++ [rblc bl RT.REP_3_6; ((if negb (curlen =? prevlen) then count - 1 else count) - 3, 2)]
  else if count <=? 10 then [rblc bl RT.REPZ_3_10; (count - 3, 3)]
  else [rblc bl RT.REPZ_11_138; (count - 11, 7)].

Lemma send_rep_eq : forall k fuel c bl b, (1 <= k)%nat -> (k <= fuel)%nat ->
  RT.send_rep fuel c bl (Z.of_nat k) b = rt_sbs b (repeat (rblc bl c) k).
Proof.
  induction k as [|k IH]; intros fuel c bl b H1 H2; [lia|].
  destruct fuel as [|fuel]; [lia|]. cbn [RT.send_rep].
  destruct k as [|k'].
  - replace (Z.of_nat 1 - 1 =? 0) with true by reflexivity. reflexivity.
  - replace (Z.of_nat (S (S k')) - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.of_nat (S (S k')) - 1) with (Z.of_nat (S k')) by lia.
    rewrite IH by lia. reflexivity.
Qed.

(** RT's emission of one run, verbatim from [send_go]. *)
Definition rt_run (bl : RT.Tree) (mn curlen prevlen count : Z) (b : ZBitsOut.BW) : ZBitsOut.BW :=
  if Z.ltb count mn then RT.send_rep 140%nat curlen bl count b
  else if negb (Z.eqb curlen 0) then
    let p := if negb (Z.eqb curlen prevlen)
             then (RT.send_code curlen bl b, count - 1) else (b, count) in
    let b1 := fst p in let c1 := snd p in
    ZBitsOut.bw_send_bits (c1 - 3) 2 (RT.send_code RT.REP_3_6 bl b1)
  else if Z.leb count 10 then
    ZBitsOut.bw_send_bits (count - 3) 3 (RT.send_code RT.REPZ_3_10 bl b)
  else ZBitsOut.bw_send_bits (count - 11) 7 (RT.send_code RT.REPZ_11_138 bl b).

Lemma rt_emit : forall bl mn curlen prevlen count b, (count < mn -> 1 <= count <= 140) ->
  rt_run bl mn curlen prevlen count b = rt_sbs b (rt_calls bl mn curlen prevlen count).
Proof.
  intros bl mn curlen prevlen count b Hc. unfold rt_run, rt_calls.
  destruct (Z.ltb_spec count mn) as [Hlt|Hge].
  - specialize (Hc Hlt). rewrite <- (Z2Nat.id count) at 1 by lia. apply send_rep_eq; lia.
  - destruct (negb (curlen =? 0)).
    + destruct (negb (curlen =? prevlen)); reflexivity.
    + destruct (count <=? 10); reflexivity.
Qed.

Section Codes.
Variable s0 : DS.deflate_state.
Variable B : RT.Tree.
Hypothesis Hbl : forall c, 0 <= c < 19 -> DS.Code s0 DS.TB c = RT.t_code B c /\ DS.Len s0 DS.TB c = RT.t_len B c.

Lemma blc_eq : forall c, 0 <= c < 19 -> SendModel.blc s0 c = rblc B c.
Proof. intros c Hc. unfold SendModel.blc, rblc. destruct (Hbl c Hc) as [E1 E2]. rewrite E1, E2. reflexivity. Qed.

Lemma calls_eq : forall mn curlen prevlen count, 0 <= curlen <= 15 ->
  SendModel.st_calls s0 mn curlen prevlen count = rt_calls B mn curlen prevlen count.
Proof.
  intros mn curlen prevlen count Hc. unfold SendModel.st_calls, rt_calls.
  destruct (count <? mn); [rewrite blc_eq by lia; reflexivity|].
  destruct (negb (curlen =? 0)).
  - rewrite (blc_eq DS.REP_3_6) by (unfold DS.REP_3_6; lia).
    destruct (negb (curlen =? prevlen)); [rewrite blc_eq by lia|]; reflexivity.
  - destruct (count <=? 10); [rewrite (blc_eq DS.REPZ_3_10) by (unfold DS.REPZ_3_10; lia)
                            | rewrite (blc_eq DS.REPZ_11_138) by (unfold DS.REPZ_11_138; lia)]; reflexivity.
Qed.

End Codes.

(* ------------------------------------------------------------------------- *)
(* 2.  The loops                                                             *)
(* ------------------------------------------------------------------------- *)

Section Loop.
Variable t : DS.tree_id.
Variable s0 : DS.deflate_state.
Variable T B : RT.Tree.
Variable mc PBL : Z.
Hypothesis Hag : forall i, 0 <= i <= mc + 1 -> DS.Len s0 t i = RT.t_len T i.
Hypothesis H15 : forall i, 0 <= i <= mc -> 0 <= DS.Len s0 t i <= 15.
Hypothesis Hbl : forall c, 0 <= c < 19 -> DS.Code s0 DS.TB c = RT.t_code B c /\ DS.Len s0 DS.TB c = RT.t_len B c.

Lemma send_loop_rel : forall f g n p q c mx mn s b,
  n + Z.of_nat f = mc + 1 -> (f < g)%nat -> 0 <= n -> q = DS.Len s0 t n -> 0 <= c -> 1 <= mn <= 4 ->
  (forall t' i, DS.Len s t' i = DS.Len s0 t' i) -> (forall t' i, DS.Code s t' i = DS.Code s0 t' i) ->
  bw_rel s b -> DS.ds_pending_out s = 0 -> arr_len (DS.ds_pending_buf s) = PBL ->
  SendModel.send_tree_ok PBL f s t mc n p q c mx mn ->
  bw_rel (DT.send_tree_loop f s t mc n p q c mx mn) (RT.send_go g T mc n p q c mx mn B b)
  /\ DS.ds_pending_out (DT.send_tree_loop f s t mc n p q c mx mn) = 0
  /\ arr_len (DS.ds_pending_buf (DT.send_tree_loop f s t mc n p q c mx mn)) = PBL.
Proof.
  induction f as [|f IH]; intros g n p q c mx mn s b Hnf Hfg Hn Hq Hc Hmn HL HC Hb Hpo Hpl Hok.
  - destruct g as [|g]; [lia|]. rewrite SendModel.send_loop_0. cbn [RT.send_go].
    replace (mc <? n) with true by (symmetry; apply Z.ltb_lt; lia).
    split; [exact Hb|]. split; [exact Hpo | exact Hpl].
  - destruct g as [|g]; [lia|]. rewrite SendModel.send_loop_S by lia. cbn [RT.send_go].
    cbn [SendModel.send_tree_ok] in Hok.
    replace (n <=? mc) with true in Hok |- * by (symmetry; apply Z.leb_le; lia).
    replace (mc <? n) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv zeta in Hok |- *. rewrite (HL t (n + 1)), (Hag (n + 1)) in Hok |- * by lia.
    assert (Hq' : RT.t_len T (n + 1) = DS.Len s0 t (n + 1)) by (rewrite (Hag (n + 1)) by lia; reflexivity).
    destruct ((c + 1 <? mx) && (q =? RT.t_len T (n + 1))).
    + apply IH; try assumption; lia.
    + assert (Hq15 : 0 <= q <= 15) by (rewrite Hq; apply H15; lia).
      assert (Hcs : SendModel.st_calls s mn q p (c + 1) = rt_calls B mn q p (c + 1)).
      { unfold SendModel.st_calls, SendModel.blc. rewrite !HC, !HL. fold (SendModel.blc s0).
        change (SendModel.st_calls s0 mn q p (c + 1) = rt_calls B mn q p (c + 1)).
        apply calls_eq; assumption. }
      assert (Hrun : rt_run B mn q p (c + 1) b = rt_sbs b (rt_calls B mn q p (c + 1)))
        by (apply rt_emit; lia).
      rewrite Hcs in Hok |- *.
      assert (HL' : forall t' i, DS.Len (SendModel.sbs_run s (rt_calls B mn q p (c + 1))) t' i = DS.Len s0 t' i)
        by (intros; rewrite SendModel.sbs_Len; apply HL).
      assert (HC' : forall t' i, DS.Code (SendModel.sbs_run s (rt_calls B mn q p (c + 1))) t' i = DS.Code s0 t' i)
        by (intros; rewrite SendModel.sbs_Code; apply HC).
      unfold DT.tree_counts in *.
      destruct (RT.t_len T (n + 1) =? 0); [|destruct (q =? RT.t_len T (n + 1))];
        (destruct Hok as [Hsb Hok']; rewrite <- Hpl in Hsb;
         destruct (br_sbs_run _ s b Hb Hpo Hsb) as (R1 & R2 & R3);
         assert (Hb' : bw_rel (SendModel.sbs_run s (rt_calls B mn q p (c + 1))) (rt_run B mn q p (c + 1) b))
           by (rewrite Hrun; exact R1);
         assert (Hpl' : arr_len (DS.ds_pending_buf (SendModel.sbs_run s (rt_calls B mn q p (c + 1)))) = PBL)
           by (rewrite R3; exact Hpl);
         apply IH; [lia | lia | lia | exact Hq' | lia | lia | exact HL' | exact HC' | exact Hb' | exact R2
                   | exact Hpl' | exact Hok']).
Qed.

End Loop.

(* ------------------------------------------------------------------------- *)
(* 3.  The pair                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem br_send_tree' : forall s b ts t mc,
  bw_rel s b -> trel s ts -> TM.tree_lens s -> scan_ok s t mc -> mc < DS.L_CODES -> bl_lens_ok s ->
  DS.ds_pending_out s = 0 ->
  ST4.send_tree_safe (arr_len (DS.ds_pending_buf s)) s t mc ->
  bw_rel (DT.send_tree s t mc) (RT.send_tree (RT.ts_trees ts (tk_of t)) mc (RT.ts_trees ts RT.TK_BL) b)
  /\ DS.ds_pending_out (DT.send_tree s t mc) = 0
  /\ arr_len (DS.ds_pending_buf (DT.send_tree s t mc)) = arr_len (DS.ds_pending_buf s).
Proof.
  intros s b ts t mc Hb H Hl (Htb & Hmc0 & Hmc1 & H15) HmcL _ Hpo Hsafe.
  set (T := RT.ts_trees ts (tk_of t)).
  set (B := RT.ts_trees ts RT.TK_BL).
  destruct H as (T1 & T2 & T3 & T4 & T5 & T6 & _).
  assert (HlenT : forall i, 0 <= i < TM.tsize t -> DS.Len s t i = RT.t_len T i).
  { intros i Hi. subst T. unfold DS.Len, RT.t_len. destruct t; cbn [DS.tree_dl tk_of TM.tsize] in *;
      [apply T2 | apply T4 | congruence]; unfold DS.HEAP_SIZE, DS.D_CODES; lia. }
  assert (Hag : forall i, 0 <= i <= mc + 1 -> DS.Len s t i = RT.t_len T i) by (intros; apply HlenT; lia).
  assert (Hbl : forall c, 0 <= c < 19 -> DS.Code s DS.TB c = RT.t_code B c /\ DS.Len s DS.TB c = RT.t_len B c).
  { intros c Hc. unfold DS.Code, DS.Len, RT.t_code, RT.t_len. cbn [DS.tree_fc DS.tree_dl].
    split; [apply T5 | apply T6]; unfold DS.BL_CODES; lia. }
  unfold ST4.send_tree_safe, ST4.OK, RefSendTree3.cnts0 in Hsafe. replace (mc + 1 - 0) with (mc + 1) in Hsafe by lia.
  unfold DT.send_tree, RT.send_tree. cbv zeta. fold T B.
  rewrite <- (Hag 0) by lia.
  destruct (DS.Len s t 0 =? 0); cbn [fst snd] in Hsafe |- *;
    (apply (send_loop_rel t s T B mc (arr_len (DS.ds_pending_buf s)) Hag H15 Hbl);
     [unfold RT.L_CODES, DS.L_CODES in *; lia | unfold RT.L_CODES, DS.L_CODES in *; lia | lia | reflexivity
     | lia | lia | reflexivity | reflexivity | exact Hb | exact Hpo | reflexivity | exact Hsafe]).
Qed.

Print Assumptions br_send_tree'.
