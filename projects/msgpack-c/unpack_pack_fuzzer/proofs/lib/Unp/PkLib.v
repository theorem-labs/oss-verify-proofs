(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem State MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree PkOps Cost.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem St MemP UB HeapOp TR PK.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PKL.

Ltac unfT := unfold T_NIL, T_BOOLEAN, T_POSINT, T_NEGINT, T_FLOAT64, T_STR, T_BIN, T_ARRAY, T_MAP, T_EXT, T_FLOAT32 in *.

Lemma levels_cons : forall o c s rest, levels_ok o ((c, s) :: rest) ->
  c = o /\ is_cont o = true /\ 0 <= s /\
  ((exists k, nth_error (okids o) (Z.to_nat s) = Some k /\ levels_ok k rest)
   \/ (nth_error (okids o) (Z.to_nat s) = None /\ rest = [] /\ okids o = [] /\ s = 0)).
Proof.
  intros o c s rest H. cbn [levels_ok] in H. destruct H as (C & IC & S & H).
  split; [exact C|]. split; [exact IC|]. split; [exact S|].
  destruct (nth_error (okids o) (Z.to_nat s)) as [k|]; [left; exists k; auto| right]. destruct H as (A & B & D). auto.
Qed.

Lemma levels_cons_intro : forall o s k rest, is_cont o = true -> 0 <= s -> nth_error (okids o) (Z.to_nat s) = Some k ->
  levels_ok k rest -> levels_ok o ((o, s) :: rest).
Proof. intros o s k rest IC S NK H. cbn [levels_ok]. rewrite NK. auto. Qed.

Lemma obj_depth_pos : forall o, (1 <= Cost.obj_depth o)%nat.
Proof. intros o. destruct o; cbn [Cost.obj_depth]; lia. Qed.
Lemma kid_depth_lt : forall o k, is_cont o = true -> In k (okids o) -> (S (Cost.obj_depth k) <= Cost.obj_depth o)%nat.
Proof.
  intros o k IC Hk.
  assert (G : forall kids, In k kids -> (Cost.obj_depth k <= Cost.objs_depth kids)%nat).
  { induction kids as [|x l IH]; intros H; [destruct H|]. unfold Cost.objs_depth in *. cbn [fold_right].
    destruct H as [<-|H]; [lia| pose proof (IH H); lia]. }
  destruct o; cbn [is_cont] in IC; try discriminate IC; cbn [okids] in Hk.
  - rewrite Cost.obj_depth_arr. pose proof (G _ Hk). lia.
  - rewrite Cost.obj_depth_map. pose proof (G _ Hk). lia.
Qed.
Lemma levels_depth : forall ls o, levels_ok o ls -> (length ls <= Cost.obj_depth o)%nat.
Proof.
  induction ls as [|[c s] rest IH]; intros o H; [cbn [length]; lia|].
  apply levels_cons in H as (-> & IC & S0 & [(k & NK & HK)|(NK & -> & _)]).
  - pose proof (IH k HK) as A. pose proof (kid_depth_lt o k IC (nth_error_In _ _ NK)) as B. cbn [length]. lia.
  - cbn [length]. pose proof (obj_depth_pos o). lia.
Qed.
Lemma pow2_le_1001 : forall c, pow2_b c = true -> c <= 1001 -> 2 * c <= 1024.
Proof.
  intros c H L. apply pow2_b_spec in H as (k & Hk & ->).
  destruct (Z_le_gt_dec k 9) as [A|A].
  - assert (2 ^ k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9) with 512 in *. lia.
  - exfalso. assert (2 ^ 10 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). change (2 ^ 10) with 1024 in *. lia.
Qed.
Lemma cap_double_ok : forall t ls c, pow2_b c = true -> levels_ok t ls -> (Cost.obj_depth t <= 1001)%nat ->
  c = Z.of_nat (length ls) -> 2 * c <= 1024.
Proof. intros t ls c HP LV TD EQ. apply pow2_le_1001; [exact HP|]. pose proof (levels_depth ls t LV). lia. Qed.

Lemma levels_forall : forall o ls, levels_ok o ls -> Forall (fun l => is_cont (fst l) = true /\ 0 <= snd l) ls.
Proof.
  intros o ls. revert o. induction ls as [|[c s] rest IH]; intros o H; [constructor|].
  destruct (levels_cons o c s rest H) as (-> & IC & S & [(k & NK & LK)|(NK & -> & OK & ->)]).
  - constructor; [cbn; auto| exact (IH k LK)].
  - constructor; [cbn; split; [exact IC| lia]| constructor].
Qed.

Lemma levels_last : forall o ls l, levels_ok o (ls ++ [l]) ->
  (exists fo, lev_node l = Some fo) \/ (okids (fst l) = [] /\ snd l = 0).
Proof.
  intros o ls. revert o. induction ls as [|[c s] rest IH]; intros o l H.
  - cbn [app] in H. destruct l as [c s]. destruct (levels_cons o c s [] H) as (-> & IC & S & [(k & NK & _)|(NK & _ & OK & ->)]).
    + left. exists k. unfold lev_node. cbn [fst snd]. exact NK.
    + right. cbn [fst snd]. auto.
  - cbn [app] in H. destruct (levels_cons o c s (rest ++ [l]) H) as (-> & IC & S & [(k & NK & LK)|(NK & E & OK & ->)]).
    + exact (IH k l LK).
    + destruct rest; discriminate E.
Qed.

Lemma levels_snoc : forall o ls c s, levels_ok o (ls ++ [(c, s)]) <->
  levels_ok o ls /\ focus_node o ls = Some c /\ is_cont c = true /\ 0 <= s /\
  ((exists k, nth_error (okids c) (Z.to_nat s) = Some k) \/ (okids c = [] /\ s = 0)).
Proof.
  intros o ls. revert o. induction ls as [|[c0 s0] rest IH]; intros o c s.
  - cbn [app]. unfold focus_node. cbn [last_opt rev]. split.
    + intros H. destruct (levels_cons o c s [] H) as (-> & IC & S & [(k & NK & _)|(NK & _ & OK & ->)]); repeat split; auto.
      left. exists k. exact NK.
    + intros (_ & CO & IC & S & ALT). injection CO as ->. cbn [levels_ok]. split; [reflexivity|]. split; [exact IC|]. split; [exact S|].
      destruct ALT as [[k NK]|[OK ->]]; [rewrite NK; exact I|]. rewrite OK. cbn. repeat split; reflexivity.
  - cbn [app]. split.
    + intros H. destruct (levels_cons o c0 s0 (rest ++ [(c, s)]) H) as (-> & IC & S & [(k & NK & LK)|(NK & E & OK & ->)]); [| destruct rest; discriminate E].
      apply (IH k c s) in LK as (L1 & L2 & L3 & L4 & L5).
      split; [exact (levels_cons_intro o s0 k rest IC S NK L1)|]. split; [| auto].
      unfold focus_node in *. unfold last_opt in *. cbn [rev]. destruct (rev rest) as [|x r] eqn:RR; cbn [app].
      * assert (rest = []) by (rewrite <- (rev_involutive rest), RR; reflexivity). subst rest. cbn in L2. injection L2 as <-.
        unfold lev_node. cbn [fst snd]. exact NK.
      * exact L2.
    + intros (L1 & L2 & L3 & L4 & L5). destruct (levels_cons o c0 s0 rest L1) as (-> & IC & S & [(k & NK & LK)|(NK & -> & OK & ->)]).
      * apply (levels_cons_intro o s0 k _ IC S NK). apply (proj2 (IH k c s)). split; [exact LK|]. split; [| auto].
        unfold focus_node in *. unfold last_opt in *. cbn [rev] in L2. destruct (rev rest) as [|x r] eqn:RR; cbn [app] in L2.
        -- assert (rest = []) by (rewrite <- (rev_involutive rest), RR; reflexivity). subst rest. cbn. unfold lev_node in L2. cbn [fst snd] in L2.
           rewrite NK in L2. exact L2.
        -- exact L2.
      * exfalso. unfold focus_node in L2. cbn in L2. unfold lev_node in L2. cbn [fst snd] in L2. rewrite NK in L2. discriminate L2.
Qed.

Lemma levels_nodes : forall o ls l, levels_ok o (ls ++ [l]) -> Forall (fun x => exists k, lev_node x = Some k) ls.
Proof.
  intros o ls. revert o. induction ls as [|[c s] rest IH]; intros o l H; [constructor|].
  cbn [app] in H. destruct (levels_cons o c s (rest ++ [l]) H) as (-> & IC & S & [(k & NK & LK)|(NK & E & OK & ->)]); [| destruct rest; discriminate E].
  constructor; [exists k; unfold lev_node; cbn [fst snd]; exact NK| exact (IH k l LK)].
Qed.

Lemma focus_obj_at : forall bm o ls l fo,
  kids_at bm o -> levels_ok o (ls ++ [l]) -> lev_node l = Some fo -> obj_at bm (lev_addr l) fo.
Proof.
  intros bm o ls. revert o. induction ls as [|[c s] rest IH]; intros o l fo KA H HN.
  - cbn [app] in H. destruct l as [c s]. destruct (levels_cons o c s [] H) as (-> & IC & S & _).
    unfold lev_node in HN. cbn [fst snd] in HN. unfold lev_addr. cbn [fst snd].
    unfold kids_at in KA. unfold okids in HN. destruct o; try discriminate IC; cbn [obj_ptr];
      rewrite <- (Z2Nat.id s) at 1 by lia; exact (proj1 (objs_at_nth bm _ _) KA (Z.to_nat s) fo HN).
  - cbn [app] in H. destruct (levels_cons o c s (rest ++ [l]) H) as (-> & IC & S & [(k & NK & LK)|(NK & E & OK & ->)]); [| destruct rest; discriminate E].
    apply (IH k l fo); [| exact LK| exact HN].
    assert (OK : obj_at bm (obj_ptr o + OBJ_SIZE * s) k).
    { unfold kids_at in KA. unfold okids in NK. destruct o; try discriminate IC; cbn [obj_ptr];
        rewrite <- (Z2Nat.id s) at 1 by lia; exact (proj1 (objs_at_nth bm _ _) KA (Z.to_nat s) k NK). }
    apply (proj2 (proj1 (obj_at_split bm _ _) OK)).
Qed.

Lemma kid_tree_wf : forall bm z o s k, is_cont o = true -> tree_wf bm z o -> nth_error (okids o) (Z.to_nat s) = Some k -> tree_wf bm z k.
Proof.
  intros bm z o s k IC TW NK. unfold okids in NK. destruct o; try discriminate IC.
  - apply tree_wf_arr in TW. destruct TW as (_ & _ & _ & T4). exact (proj1 (trees_wf_forall _ _ _) T4 k (nth_error_In _ _ NK)).
  - apply tree_wf_map in TW. destruct TW as (_ & _ & _ & _ & T4). exact (proj1 (trees_wf_forall _ _ _) T4 k (nth_error_In _ _ NK)).
Qed.

Lemma levels_wf : forall bm z o ls, tree_wf bm z o -> levels_ok o ls -> Forall (fun l => tree_wf bm z (fst l)) ls.
Proof.
  intros bm z o ls. revert o. induction ls as [|[c s] rest IH]; intros o TW H; [constructor|].
  destruct (levels_cons o c s rest H) as (-> & IC & S & [(k & NK & LK)|(NK & -> & OK & ->)]).
  - constructor; [exact TW| exact (IH k (kid_tree_wf bm z o s k IC TW NK) LK)].
  - constructor; [exact TW| constructor].
Qed.

Lemma focus_tree_wf : forall bm z o ls l fo,
  tree_wf bm z o -> levels_ok o (ls ++ [l]) -> lev_node l = Some fo -> tree_wf bm z fo.
Proof.
  intros bm z o ls l fo TW H HN.
  pose proof (proj1 (Forall_forall _ _) (levels_wf bm z o _ TW H) l ltac:(apply in_app_iff; right; left; reflexivity)) as TL.
  pose proof (proj1 (Forall_forall _ _) (levels_forall o _ H) l ltac:(apply in_app_iff; right; left; reflexivity)) as [IC S].
  exact (kid_tree_wf bm z (fst l) (snd l) fo IC TL HN).
Qed.

Lemma kid_cells : forall root o s k c, is_cont o = true -> 0 <= s -> nth_error (okids o) (Z.to_nat s) = Some k ->
  In c (obj_cells (obj_ptr o + OBJ_SIZE * s) k) -> In c (tl (obj_cells root o)).
Proof.
  intros root o s k c IC S NK Hc. unfold okids in NK. rewrite <- (Z2Nat.id s) in Hc by lia.
  destruct o; try discriminate IC; cbn [obj_ptr] in Hc; [rewrite obj_cells_arr| rewrite obj_cells_map]; cbn [tl]; apply in_kids_cells; eauto.
Qed.

Lemma focus_cells : forall root o ls l fo c,
  levels_ok o (ls ++ [l]) -> lev_node l = Some fo -> In c (obj_cells (lev_addr l) fo) -> In c (tl (obj_cells root o)).
Proof.
  intros root o ls. revert root o. induction ls as [|[c0 s0] rest IH]; intros root o l fo c H HN Hc.
  - cbn [app] in H. destruct l as [c1 s]. destruct (levels_cons o c1 s [] H) as (-> & IC & S & _).
    unfold lev_node in HN. cbn [fst snd] in HN. unfold lev_addr in Hc. cbn [fst snd] in Hc. exact (kid_cells root o s fo c IC S HN Hc).
  - cbn [app] in H. destruct (levels_cons o c0 s0 (rest ++ [l]) H) as (-> & IC & S & [(k & NK & LK)|(NK & E & OK & ->)]); [| destruct rest; discriminate E].
    pose proof (IH (obj_ptr o + OBJ_SIZE * s0) k l fo c LK HN Hc) as IN.
    apply (kid_cells root o s0 k c IC S NK). destruct k; cbn [obj_cells tl] in IN |- *; try (destruct IN); auto; right; exact IN.
Qed.

Lemma elem_of_obj : forall l, 0 <= snd l -> pe_obj (elem_of l) = lev_addr l.
Proof.
  intros [o s] Hs. cbn [snd] in Hs. unfold pe_obj, elem_of, lev_addr. cbn [fst snd].
  destruct o; cbn [pe_ptr pe_map pe_key obj_ptr andb negb]; unfold OBJ_SIZE; try lia.
  pose proof (Z.div_mod s 2 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound s 2 ltac:(lia)) as MB.
  destruct (Z.even s) eqn:EV; cbn [negb andb].
  - rewrite Zeven_mod in EV. apply Z.eqb_eq in EV. lia.
  - assert (s mod 2 <> 0) by (intros X; rewrite Zeven_mod, X in EV; discriminate EV). lia.
Qed.

Lemma rest_pos_node : forall o ls l, levels_ok o (ls ++ [l]) -> 0 < pe_rest (elem_of l) -> exists fo, lev_node l = Some fo.
Proof.
  intros o ls l H R. destruct (levels_last o ls l H) as [X|[OK S0]]; [exact X| exfalso].
  destruct l as [lo s]. cbn [fst snd] in OK, S0. subst s. unfold elem_of in R. unfold okids in OK.
  destruct lo; cbn [pe_rest obj_ptr okids] in R; try (cbn in OK; subst; cbn in R; lia).
Qed.

End PKL.
