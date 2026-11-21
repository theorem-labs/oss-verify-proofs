(** * Bridge.DEmit.BrScanTree — pair D29 (first half) of PAIRS.md: [scan_tree], S5 vs RT.

    Both write the [0xffff] guard at [tree[max_code + 1]] and then walk the
    code lengths [0 .. max_code] in runs, bumping [bl_tree] frequencies.
    S5's loop keeps its state as [set_bl_tree_fc s1 b] ([ScanModel]); RT's
    carries the [bl_tree] alone.  [scan_loop_rel] relates the two loops by
    induction on S5's fuel.

    The DTreeIface statement [br_scan_tree] needs one hypothesis more than
    [scan_ok]: [max_code < L_CODES].  RT's loop has fuel [L_CODES + 3] while
    [scan_ok] admits a literal tree's [max_code] up to 571; [scan_cex] below
    is a related pair, [scan_ok] at [max_code = 400], where the two
    [bl_tree] frequencies of [REP_3_6] come out 67 (S5) and 48 (RT).  At
    every real call [max_code < elems <= L_CODES] ([build_tree]'s result). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel ScanModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Trees ZBitsOut.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SCM := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.ScanModel.

(* ------------------------------------------------------------------------- *)
(* 1.  One run's bl_tree update                                              *)
(* ------------------------------------------------------------------------- *)

Lemma tsf_fc : forall t i v, RT.tr_fc (RT.t_setfreq t i v) = Base.zset (RT.tr_fc t) i (Base.u16 v).
Proof. reflexivity. Qed.
Lemma tsf_dl : forall t i v, RT.tr_dl (RT.t_setfreq t i v) = RT.tr_dl t.
Proof. reflexivity. Qed.

(** RT's update, verbatim from [scan_go]. *)
Definition rt_upd (mn : Z) (bl : RT.Tree) (curlen prevlen count : Z) : RT.Tree :=
  if Z.ltb count mn then RT.t_setfreq bl curlen (RT.t_freq bl curlen + count)
  else if negb (Z.eqb curlen 0) then
    let b1 := if negb (Z.eqb curlen prevlen)
              then RT.t_setfreq bl curlen (RT.t_freq bl curlen + 1) else bl in
    RT.t_setfreq b1 RT.REP_3_6 (RT.t_freq b1 RT.REP_3_6 + 1)
  else if Z.leb count 10 then RT.t_setfreq bl RT.REPZ_3_10 (RT.t_freq bl RT.REPZ_3_10 + 1)
  else RT.t_setfreq bl RT.REPZ_11_138 (RT.t_freq bl RT.REPZ_11_138 + 1).

Lemma bumpd_rel : forall (b : arr) (bl : RT.Tree) i d,
  arr_rel b (RT.tr_fc bl) 0 39 -> arr_len b = 39 -> 0 <= i < 39 ->
  arr_rel (arr_set b i (wrap16 (arr_get b i + d))) (RT.tr_fc (RT.t_setfreq bl i (RT.t_freq bl i + d))) 0 39
  /\ RT.tr_dl (RT.t_setfreq bl i (RT.t_freq bl i + d)) = RT.tr_dl bl
  /\ arr_len (arr_set b i (wrap16 (arr_get b i + d))) = 39.
Proof.
  intros b bl i d H Hl Hi. rewrite tsf_fc, tsf_dl, arr_len_set. split; [|split; [reflexivity | exact Hl]].
  unfold RT.t_freq. rewrite <- (H i Hi), <- wrap16_u16. apply arr_rel_set; [exact H | lia].
Qed.

Lemma st_upd_rel : forall mn b bl c p k,
  arr_rel b (RT.tr_fc bl) 0 39 -> arr_len b = 39 -> 0 <= c <= 15 ->
  arr_rel (SCM.st_upd mn b c p k) (RT.tr_fc (rt_upd mn bl c p k)) 0 39
  /\ RT.tr_dl (rt_upd mn bl c p k) = RT.tr_dl bl
  /\ arr_len (SCM.st_upd mn b c p k) = 39.
Proof.
  intros mn b bl c p k H Hl Hc. unfold SCM.st_upd, rt_upd.
  destruct (k <? mn); [apply bumpd_rel; auto; lia|].
  destruct (negb (c =? 0)).
  - cbv zeta. destruct (negb (c =? p)).
    + destruct (bumpd_rel b bl c 1 H Hl ltac:(lia)) as (H1 & D1 & L1).
      destruct (bumpd_rel _ _ RT.REP_3_6 1 H1 L1 ltac:(unfold RT.REP_3_6; lia)) as (H2 & D2 & L2).
      unfold DS.REP_3_6. change RT.REP_3_6 with 16 in *.
      split; [exact H2|]. split; [rewrite D2; exact D1 | exact L2].
    + apply bumpd_rel; auto. unfold DS.REP_3_6; lia.
  - destruct (k <=? 10); apply bumpd_rel; auto; [unfold DS.REPZ_3_10 | unfold DS.REPZ_11_138]; lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The loops                                                             *)
(* ------------------------------------------------------------------------- *)

Section Loop.
Variable t : DS.tree_id.
Variable s1 : DS.deflate_state.
Variable tg : RT.Tree.
Variable mc : Z.
Hypothesis Hag : forall i, 0 <= i <= mc + 1 -> DS.Len s1 t i = RT.t_len tg i.
Hypothesis H15 : forall i, 0 <= i <= mc -> 0 <= DS.Len s1 t i <= 15.

Lemma scan_loop_rel : forall f g n p q c mx mn b bl,
  n + Z.of_nat f = mc + 1 -> (f < g)%nat -> 0 <= n -> q = DS.Len s1 t n ->
  arr_rel b (RT.tr_fc bl) 0 39 -> arr_len b = 39 ->
  exists b', DT.scan_tree_loop f (DS.set_bl_tree_fc s1 b) t mc n p q c mx mn = DS.set_bl_tree_fc s1 b'
    /\ arr_rel b' (RT.tr_fc (RT.scan_go g tg mc n p q c mx mn bl)) 0 39
    /\ RT.tr_dl (RT.scan_go g tg mc n p q c mx mn bl) = RT.tr_dl bl
    /\ arr_len b' = 39.
Proof.
  induction f as [|f IH]; intros g n p q c mx mn b bl Hnf Hfg Hn Hq Hb Hl.
  - destruct g as [|g]; [lia|]. rewrite SCM.scan_loop_0. cbn [RT.scan_go].
    replace (mc <? n) with true by (symmetry; apply Z.ltb_lt; lia).
    exists b. split; [reflexivity|]. split; [exact Hb|]. split; [reflexivity | exact Hl].
  - destruct g as [|g]; [lia|]. rewrite SCM.scan_loop_S. cbn [RT.scan_go].
    replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia).
    replace (mc <? n) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv zeta. rewrite (Hag (n + 1)) by lia.
    destruct ((c + 1 <? mx) && (q =? RT.t_len tg (n + 1))).
    + apply IH; try assumption; try lia. rewrite (Hag (n + 1)) by lia. reflexivity.
    + assert (Hq15 : 0 <= q <= 15) by (rewrite Hq; apply H15; lia).
      destruct (st_upd_rel mn b bl q p (c + 1) Hb Hl Hq15) as (U1 & U2 & U3).
      assert (Hq' : RT.t_len tg (n + 1) = DS.Len s1 t (n + 1)) by (rewrite (Hag (n + 1)) by lia; reflexivity).
      unfold DT.tree_counts.
      destruct (RT.t_len tg (n + 1) =? 0); [|destruct (q =? RT.t_len tg (n + 1))].
      * destruct (IH g (n + 1) q (RT.t_len tg (n + 1)) 0 138 3 _ _ ltac:(lia) ltac:(lia) ltac:(lia) Hq' U1 U3)
          as (b' & E & R & D & L).
        exists b'. split; [exact E|]. split; [exact R|]. split; [exact (eq_trans D U2) | exact L].
      * destruct (IH g (n + 1) q (RT.t_len tg (n + 1)) 0 6 3 _ _ ltac:(lia) ltac:(lia) ltac:(lia) Hq' U1 U3)
          as (b' & E & R & D & L).
        exists b'. split; [exact E|]. split; [exact R|]. split; [exact (eq_trans D U2) | exact L].
      * destruct (IH g (n + 1) q (RT.t_len tg (n + 1)) 0 7 4 _ _ ltac:(lia) ltac:(lia) ltac:(lia) Hq' U1 U3)
          as (b' & E & R & D & L).
        exists b'. split; [exact E|]. split; [exact R|]. split; [exact (eq_trans D U2) | exact L].
Qed.

End Loop.

(* ------------------------------------------------------------------------- *)
(* 3.  The pair                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma tsl_dl : forall tr i v, RT.tr_dl (RT.t_setlen tr i v) = Base.zset (RT.tr_dl tr) i (Base.u16 v).
Proof. reflexivity. Qed.
Lemma tsl_fc : forall tr i v, RT.tr_fc (RT.t_setlen tr i v) = RT.tr_fc tr.
Proof. reflexivity. Qed.

Lemma set_tree_get : forall k tr ts j,
  RT.ts_trees (RT.set_tree k tr ts) j = if Z.eqb j k then tr else RT.ts_trees ts j.
Proof. reflexivity. Qed.

Ltac rt_frame :=
  cbn [RT.ts_maxcode RT.ts_blcount RT.ts_heap RT.ts_heaplen RT.ts_heapmax RT.ts_depth
       RT.ts_optlen RT.ts_statlen RT.ts_matches RT.set_tree RT.set_trees].

Theorem br_scan_tree' : forall s ts t mc,
  trel s ts -> TM.tree_lens s -> scan_ok s t mc -> mc < DS.L_CODES ->
  trel (DT.scan_tree s t mc) (scan_ts (tk_of t) mc ts).
Proof.
  intros s ts t mc H Hl (Htb & Hmc0 & Hmc1 & H15) HmcL.
  set (T := RT.ts_trees ts (tk_of t)).
  set (B := RT.ts_trees ts RT.TK_BL).
  set (tg := RT.t_setlen T (mc + 1) 65535).
  set (s1 := DS.set_Len s t (mc + 1) 65535).
  destruct H as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17).
  destruct Hl as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  assert (Hdl : arr_len (DS.tree_dl s t) = TM.tsize t) by (destruct t; cbn; assumption).
  assert (HlenT : forall i, 0 <= i < TM.tsize t -> DS.Len s t i = RT.t_len T i).
  { intros i Hi. subst T. unfold DS.Len, RT.t_len. destruct t; cbn [DS.tree_dl tk_of TM.tsize] in *;
      [apply T2 | apply T4 | congruence]; unfold DS.HEAP_SIZE, DS.D_CODES; lia. }
  assert (Hag : forall i, 0 <= i <= mc + 1 -> DS.Len s1 t i = RT.t_len tg i).
  { intros i Hi. subst s1 tg. rewrite SCM.Len_set_Len by lia. unfold RT.t_len. rewrite tsl_dl. unfold Base.zset.
    destruct (Z.eqb_spec (mc + 1) i) as [E|E].
    - subst i. rewrite Z.eqb_refl, wrap16_u16. reflexivity.
    - replace (i =? mc + 1) with false by (symmetry; apply Z.eqb_neq; lia). apply HlenT. lia. }
  assert (H15' : forall i, 0 <= i <= mc -> 0 <= DS.Len s1 t i <= 15).
  { intros i Hi. subst s1. rewrite SCM.Len_set_Len by lia.
    replace (mc + 1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). apply H15. exact Hi. }
  assert (HL0 : DS.Len s t 0 = DS.Len s1 t 0).
  { subst s1. rewrite SCM.Len_set_Len by lia. replace (mc + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    reflexivity. }
  assert (HL0' : DS.Len s t 0 = RT.t_len T 0) by (apply HlenT; destruct t; cbn [TM.tsize]; lia).
  assert (HB : arr_rel (DS.ds_bl_tree_fc s1) (RT.tr_fc B) 0 39).
  { subst s1. destruct t; [| | congruence]; unfold DS.set_Len, DS.set_Dad; cbn [DS.set_tree_dl DS.tree_dl];
      autorewrite with s5f_dyn_ltree_dl s5f_dyn_dtree_dl; exact T5. }
  assert (HBl : arr_len (DS.ds_bl_tree_fc s1) = 39).
  { subst s1. destruct t; [| | congruence]; unfold DS.set_Len, DS.set_Dad; cbn [DS.set_tree_dl DS.tree_dl];
      autorewrite with s5f_dyn_ltree_dl s5f_dyn_dtree_dl; exact L5. }
  destruct (scan_loop_rel t s1 tg mc Hag H15' (Z.to_nat (mc + 1)) (Z.to_nat RT.L_CODES + 3) 0 (-1)
              (DS.Len s t 0) 0 (if DS.Len s t 0 =? 0 then 138 else 7) (if DS.Len s t 0 =? 0 then 3 else 4)
              (DS.ds_bl_tree_fc s1) B ltac:(lia) ltac:(unfold RT.L_CODES, DS.L_CODES in *; lia) ltac:(lia)
              HL0 HB HBl) as (b' & E & R & D & Lb).
  assert (ES : DT.scan_tree s t mc = DS.set_bl_tree_fc s1 b').
  { unfold DT.scan_tree. cbv zeta. fold s1. rewrite <- E, SCM.sbf_self.
    destruct (DS.Len s t 0 =? 0); reflexivity. }
  assert (ER : scan_ts (tk_of t) mc ts
               = RT.set_tree RT.TK_BL (RT.scan_go (Z.to_nat RT.L_CODES + 3) tg mc 0 (-1) (DS.Len s t 0) 0
                    (if DS.Len s t 0 =? 0 then 138 else 7) (if DS.Len s t 0 =? 0 then 3 else 4) B)
                  (RT.set_tree (tk_of t) tg ts)).
  { unfold scan_ts, RT.scan_tree. fold T B tg. rewrite HL0'. reflexivity. }
  rewrite ES, ER. clear ES ER E.
  set (bl' := RT.scan_go _ tg mc 0 (-1) (DS.Len s t 0) 0 _ _ B) in *.
  unfold trel. cbv zeta. rewrite !set_tree_get. rt_frame.
  subst s1. destruct t; [| | congruence]; cbn [tk_of] in *;
    unfold DS.set_Len, DS.set_Dad in *; cbn [DS.set_tree_dl DS.tree_dl] in *;
    autorewrite with s5f_bl_tree_fc s5f_dyn_ltree_dl s5f_dyn_dtree_dl;
    cbn [Z.eqb RT.TK_L RT.TK_D RT.TK_BL Pos.eqb];
    subst tg T; rewrite ?tsl_dl, ?tsl_fc, ?D.
  - split; [exact T1|]. split.
    + rewrite <- wrap16_u16. apply arr_rel_set; [exact T2 | unfold DS.HEAP_SIZE, TM.tsize in *; lia].
    + exact (conj T3 (conj T4 (conj R (conj T6 (conj T7 (conj T8 (conj T9 (conj T10 (conj T11 (conj T12
               (conj T13 (conj T14 (conj T15 (conj T16 T17)))))))))))))).
  - split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split.
    + rewrite <- wrap16_u16. apply arr_rel_set; [exact T4 | unfold DS.D_CODES, TM.tsize in *; lia].
    + split; [exact R|]. repeat (split; [assumption|]). assumption.
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  Why [max_code < L_CODES] is needed                                    *)
(* ------------------------------------------------------------------------- *)

Definition cex_s0 : DS.deflate_state :=
  DS.ds_of_oracle (fun _ => 0) 0%N (DS.cstrm_of_call (mkZCall [] 0 zstrm0)).
Fixpoint cex_setlens (n : nat) (s : DS.deflate_state) : DS.deflate_state :=
  match n with O => s | S k => cex_setlens k (DS.set_Len s DS.TL (Z.of_nat k) 1) end.
Fixpoint cex_rsetlens (n : nat) (t : RT.Tree) : RT.Tree :=
  match n with O => t | S k => cex_rsetlens k (RT.t_setlen t (Z.of_nat k) 1) end.
Definition cex_s := cex_setlens 401 cex_s0.
Definition cex_ts := RT.set_tree RT.TK_L (cex_rsetlens 401 (RT.ts_trees RT.ts_new RT.TK_L)) RT.ts_new.

(** [cex_s]/[cex_ts]: every tree array zero except literal code lengths
    0..400 = 1 on both sides (so [trel] holds, checked entrywise by
    [arr_relb]), and [scan_ok cex_s TL 400] holds ([401 < 573], lengths 1).
    The scans disagree on [bl_tree[REP_3_6]]. *)
Example scan_cex :
  arr_relb (DS.ds_dyn_ltree_dl cex_s) (RT.tr_dl (RT.ts_trees cex_ts RT.TK_L)) 0 573 = true
  /\ arr_relb (DS.ds_dyn_ltree_fc cex_s) (RT.tr_fc (RT.ts_trees cex_ts RT.TK_L)) 0 573 = true
  /\ arr_relb (DS.ds_bl_tree_fc cex_s) (RT.tr_fc (RT.ts_trees cex_ts RT.TK_BL)) 0 39 = true
  /\ (DS.Len cex_s DS.TL 400, DS.Len cex_s DS.TL 401) = (1, 0)
  /\ (arr_get (DS.ds_bl_tree_fc (DT.scan_tree cex_s DS.TL 400)) 16,
      RT.tr_fc (RT.ts_trees (scan_ts RT.TK_L 400 cex_ts) RT.TK_BL) 16) = (67, 48).
Proof. vm_compute. repeat split; reflexivity. Qed.

Print Assumptions br_scan_tree'.
