(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout OpsBridge.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module UG.

Fixpoint take_windows (n : nat) (l : list sv) : option (list (sv * sv * sv) * list sv) :=
  match n with
  | O => Some ([], l)
  | S n' => match l with
            | a :: b :: c :: r => match take_windows n' r with
                                  | Some (ws, rest) => Some ((a, b, c) :: ws, rest)
                                  | None => None
                                  end
            | _ => None
            end
  end.

Fixpoint flat_windows (ws : list (sv * sv * sv)) : list sv :=
  match ws with [] => [] | (a, b, c) :: ws' => a :: b :: c :: flat_windows ws' end.

Definition lit (v : sv) : option int := match v with VL x => if wt x then None else Some (wl x) | _ => None end.

Definition parse_args (args : list sv) : option (int * sv * list (sv * sv * sv) * list sv) :=
  match args with
  | md :: aw :: nw :: rest =>
      match lit md, lit nw with
      | Some mdi, Some nwi =>
          match take_windows (Z.to_nat (to_Z nwi)) rest with
          | Some (ws, ca) => Some (mdi, aw, ws, ca)
          | None => None
          end
      | _, _ => None
      end
  | _ => None
  end.

Definition is_heap (o : opinst) : bool := PrimInt63.eqb (op_id o) OPID.
Fixpoint pick_op (os : list opinst) : option (list opinst * opinst * list opinst) :=
  match os with
  | [] => None
  | o :: os' => if is_heap o then (if forallb (fun o' => negb (is_heap o')) os' then Some ([], o, os') else None)
                else match pick_op os' with
                     | Some (pre, x, post) => Some (o :: pre, x, post)
                     | None => None
                     end
  end.

Definition the_op (st : sstate) : option (int * sv * list (sv * sv * sv) * list sv) :=
  match pick_op (s_ops st) with
  | Some (_, o, _) => parse_args (op_args o)
  | None => None
  end.

Fixpoint set_op (args : list sv) (os : list opinst) : list opinst :=
  match os with
  | [] => []
  | o :: os' => if is_heap o then OpI OPID args :: os' else o :: set_op args os'
  end.

Definition op_in (st : sstate) (o : opinst) : Prop :=
  exists pre post, s_ops st = pre ++ o :: post /\ Forall (fun o' => op_id o' <> OPID) (pre ++ post).

Lemma pick_op_sound : forall os pre o post, pick_op os = Some (pre, o, post) ->
  os = pre ++ o :: post /\ op_id o = OPID /\ Forall (fun o' => op_id o' <> OPID) (pre ++ post).
Proof.
  induction os as [|x os IH]; intros pre o post H; cbn [pick_op] in H; [discriminate|].
  destruct (is_heap x) eqn:HX.
  - destruct (forallb (fun o' => negb (is_heap o')) os) eqn:FA; [|discriminate]. injection H as <- <- <-.
    split; [reflexivity|]. split; [exact (Uint63.eqb_correct _ _ HX)|]. cbn [app].
    apply Forall_forall. intros o' Ho'. pose proof (proj1 (forallb_forall _ _) FA o' Ho') as Q. cbn beta in Q.
    apply negb_true_iff in Q. exact (Uint63.eqb_false_correct _ _ Q).
  - destruct (pick_op os) as [[[pre0 x0] post0]|] eqn:P; [|discriminate]. injection H as <- <- <-.
    destruct (IH pre0 x0 post0 eq_refl) as (E1 & E2 & E3). split; [cbn [app]; rewrite E1; reflexivity|]. split; [exact E2|].
    cbn [app]. constructor; [exact (Uint63.eqb_false_correct _ _ HX)| exact E3].
Qed.

Lemma op_in_In : forall st o, op_in st o -> In o (s_ops st).
Proof. intros st o (pre & post & E & _). rewrite E. apply in_elt. Qed.

Lemma set_op_split : forall args pre o post, op_id o = OPID -> Forall (fun o' => op_id o' <> OPID) (pre ++ post) ->
  set_op args (pre ++ o :: post) = pre ++ OpI OPID args :: post.
Proof.
  intros args pre o post HO HF. induction pre as [|x pre IH]; cbn [set_op app].
  - unfold is_heap. rewrite HO, Uint63.eqb_refl. reflexivity.
  - cbn [app] in HF. inversion HF as [|x' l NX HF']; subst.
    unfold is_heap at 1. rewrite (proj2 (Uint63.eqb_false_spec _ _) NX). rewrite (IH HF'). reflexivity.
Qed.

Definition mk_args (md : int) (aw : sv) (ws : list (sv * sv * sv)) (ca : list sv) : list sv :=
  VL (wlit md) :: aw :: VL (wlit (Uint63.of_Z (Z.of_nat (length ws)))) :: flat_windows ws ++ ca.
Definition mk_op (md : int) (aw : sv) (ws : list (sv * sv * sv)) (ca : list sv) : opinst := OpI OPID (mk_args md aw ws ca).

Definition wden (E : env) (w : sv * sv * sv) : window :=
  match w with (a, b, c) => Win (bv_unsigned (den E a)) (bv_unsigned (den E b)) (bv_unsigned (den E c)) end.

Lemma lit_sound : forall E v i, lit v = Some i -> bv_unsigned (den E v) = to_Z i.
Proof.
  intros E v i H. unfold lit in H. destruct v; try discriminate. destruct (wt w) eqn:T; [discriminate|].
  injection H as <-. cbn [den]. rewrite wbv_unsigned. unfold w2Z. rewrite T. lia.
Qed.

Lemma take_windows_sound : forall E n l ws ca, take_windows n l = Some (ws, ca) ->
  decode_windows n (map (den E) l) = Some (map (wden E) ws, map (den E) ca) /\ length ws = n.
Proof.
  intros E n. induction n as [|n IH]; intros l ws ca H; cbn [take_windows] in H.
  - injection H as <- <-. split; reflexivity.
  - destruct l as [|a [|b [|c r]]]; try discriminate.
    destruct (take_windows n r) as [[ws0 rest]|] eqn:T; [|discriminate]. injection H as <- <-.
    destruct (IH r ws0 rest T) as [D L]. cbn [map decode_windows]. rewrite D. cbn [map length]. rewrite L. split; reflexivity.
Qed.

Lemma parse_sound : forall E args mdi aw ws ca, parse_args args = Some (mdi, aw, ws, ca) ->
  decode (map (den E) args) = Some (to_Z mdi, den E aw, map (wden E) ws, map (den E) ca) /\ Z.of_nat (length ws) < two63.
Proof.
  intros E args mdi aw ws ca H. unfold parse_args in H.
  destruct args as [|md [|aw0 [|nw rest]]]; try discriminate.
  destruct (lit md) as [mi|] eqn:LM; [|discriminate]. destruct (lit nw) as [ni|] eqn:LN; [|discriminate].
  destruct (take_windows (Z.to_nat (to_Z ni)) rest) as [[ws0 ca0]|] eqn:T; [|discriminate]. injection H as <- <- <- <-.
  destruct (take_windows_sound E _ rest ws0 ca0 T) as [D L].
  cbn [map]. unfold decode. rewrite (lit_sound E nw ni LN), D, (lit_sound E md mi LM). split; [reflexivity|].
  rewrite L. pose proof (int_range ni). rewrite Z2Nat.id by lia. lia.
Qed.

Lemma the_op_sound : forall E st mdi aw ws ca, the_op st = Some (mdi, aw, ws, ca) ->
  exists o, op_in st o /\ op_id o = OPID /\
    decode (map (den E) (op_args o)) = Some (to_Z mdi, den E aw, map (wden E) ws, map (den E) ca) /\ Z.of_nat (length ws) < two63.
Proof.
  intros E st mdi aw ws ca H. unfold the_op in H. destruct (pick_op (s_ops st)) as [[[pre o] post]|] eqn:P; [|discriminate].
  destruct (pick_op_sound _ _ _ _ P) as (E1 & E2 & E3).
  exists o. split; [exists pre, post; auto|]. split; [exact E2|]. exact (parse_sound E _ _ _ _ _ H).
Qed.

Lemma take_flat : forall ws ca, take_windows (length ws) (flat_windows ws ++ ca) = Some (ws, ca).
Proof.
  induction ws as [|[[a b] c] ws IH]; intros ca; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma mk_args_sound : forall E md aw ws ca, Z.of_nat (length ws) < two63 ->
  decode (map (den E) (mk_args md aw ws ca)) = Some (to_Z md, den E aw, map (wden E) ws, map (den E) ca).
Proof.
  intros E md aw ws ca Hl. unfold mk_args. cbn [map]. unfold decode. cbn [den]. rewrite !wbv_unsigned, !wlit_ok.
  rewrite Uint63.of_Z_spec, Z.mod_small by (rewrite wB_two63; lia). rewrite Nat2Z.id.
  destruct (take_windows_sound E (length ws) (flat_windows ws ++ ca) ws ca (take_flat ws ca)) as [D _]. rewrite D. reflexivity.
Qed.

Lemma take_windows_split : forall n l ws ca, take_windows n l = Some (ws, ca) -> l = flat_windows ws ++ ca.
Proof.
  induction n as [|n IH]; intros l ws ca H; cbn [take_windows] in H.
  - injection H as <- <-. reflexivity.
  - destruct l as [|a [|b [|c r]]]; try discriminate.
    destruct (take_windows n r) as [[ws0 rest]|] eqn:T; [|discriminate]. injection H as <- <-.
    cbn [flat_windows]. rewrite (IH r ws0 rest T). reflexivity.
Qed.

Lemma the_op_split : forall st mdi aw ws ca, the_op st = Some (mdi, aw, ws, ca) ->
  exists o md nw, op_in st o /\ op_id o = OPID /\ op_args o = md :: aw :: nw :: flat_windows ws ++ ca.
Proof.
  intros st mdi aw ws ca H. unfold the_op in H. destruct (pick_op (s_ops st)) as [[[pre o] post]|] eqn:P; [|discriminate].
  destruct (pick_op_sound _ _ _ _ P) as (E1 & Q & E3).
  unfold parse_args in H. destruct (op_args o) as [|md [|aw0 [|nw rest]]] eqn:OA; try discriminate.
  destruct (lit md) as [mi|]; [|discriminate]. destruct (lit nw) as [ni|]; [|discriminate].
  destruct (take_windows (Z.to_nat (to_Z ni)) rest) as [[ws0 ca0]|] eqn:T; [|discriminate]. injection H as <- <- <- <-.
  exists o, md, nw. split; [exists pre, post; auto|]. split; [exact Q|]. rewrite OA, (take_windows_split _ _ _ _ T). reflexivity.
Qed.

Lemma the_op_full : forall st mdi aw ws ca, the_op st = Some (mdi, aw, ws, ca) ->
  exists o md nw, op_in st o /\ op_id o = OPID /\ op_args o = md :: aw :: nw :: flat_windows ws ++ ca /\
    (forall E, decode (map (den E) (op_args o)) = Some (to_Z mdi, den E aw, map (wden E) ws, map (den E) ca)) /\
    Z.of_nat (length ws) < two63.
Proof.
  intros st mdi aw ws ca H. pose proof H as H0. unfold the_op in H. destruct (pick_op (s_ops st)) as [[[pre o] post]|] eqn:P; [|discriminate].
  destruct (pick_op_sound _ _ _ _ P) as (E1 & Q & E3).
  pose proof H as PA. unfold parse_args in H. destruct (op_args o) as [|md [|aw0 [|nw rest]]] eqn:OA; try discriminate.
  destruct (lit md) as [mi|]; [|discriminate]. destruct (lit nw) as [ni|]; [|discriminate].
  destruct (take_windows (Z.to_nat (to_Z ni)) rest) as [[ws0 ca0]|] eqn:T; [|discriminate]. injection H as <- <- <- <-.
  exists o, md, nw. split; [exists pre, post; auto|]. split; [exact Q|]. split; [rewrite OA, (take_windows_split _ _ _ _ T); reflexivity|].
  split; [| exact (proj2 (parse_sound (Env (fun _ => Z_to_bv 64 0) (fun _ => []) (fun _ _ => Z_to_bv 8 0)) _ _ _ _ _ PA))].
  intros E. rewrite OA. exact (proj1 (parse_sound E _ _ _ _ _ PA)).
Qed.

Lemma in_flat_windows : forall ws a b c, In (a, b, c) ws -> In a (flat_windows ws) /\ In b (flat_windows ws) /\ In c (flat_windows ws).
Proof.
  induction ws as [|[[x y] z] ws IH]; intros a b c H; [destruct H|].
  cbn [flat_windows]. destruct H as [H|H].
  - injection H as <- <- <-. cbn; tauto.
  - destruct (IH a b c H) as (A & B & C). cbn. tauto.
Qed.

Lemma ops_vars_below : forall n st o, st_vars_below n st = true -> In o (s_ops st) ->
  forall v, In v (op_args o) -> sv_vars_below n v = true.
Proof.
  intros n st o H Ho v Hv. unfold st_vars_below in H. apply andb_prop in H as [_ H].
  pose proof (proj1 (forallb_forall _ _) H o Ho) as Q. cbn beta in Q. exact (proj1 (forallb_forall _ _) Q v Hv).
Qed.

Lemma ops_hold_in : forall OPS E os m mo o, ops_hold OPS E os m mo -> In o os ->
  op_holds OPS (op_id o) (map (den E) (op_args o)) m mo.
Proof. intros OPS E os m mo o H Ho. unfold ops_hold in H. exact (proj1 (Forall_forall _ _) H o Ho). Qed.

Definition cover_law (segs : list Segment) (OPS : optable) : Prop :=
  (forall a, (exists seg, find_segment segs a 1 = Some seg) -> op_cov0 OPS a) /\
  (forall args m mo a, op_holds OPS OPID args m mo -> 0 <= a < two64 ->
     ~ Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS OPID args) -> op_cov OPS [(OPID, args)] a).

Lemma plain_cover_law : forall segs OPS, plain_table OPS -> cover_law segs OPS.
Proof. intros segs OPS PL. split; [intros a _| intros args m mo a _ _ _]; [| apply plain_cover; exact PL].
  destruct (plain_cover OPS [] a PL) as [H|H]; [exact H| inversion H]. Qed.

Lemma cover_of_apart : forall segs OPS E os R priv m mo args,
  cover_law segs OPS -> ops_apart segs OPS E os R priv -> ops_hold OPS E os m mo -> In (OpI OPID args) os ->
  (forall k r, IMap.find k R = Some r -> PrimInt63.eqb k 0%uint63 = false ->
     0 <= bv_unsigned (ev E k) + loZ r /\ bv_unsigned (ev E k) + hiZ E r < two64) ->
  forall a, fx_acc segs E R a -> op_cov OPS (insts E os) a.
Proof.
  intros segs OPS E os R priv m mo args [CI CN] AP OH IN RNG a [B|S]; [| left; exact (CI a S)].
  pose proof (proj1 (Forall_forall _ _) AP _ IN) as AP1. cbn [op_id op_args] in AP1.
  pose proof (proj1 (Forall_forall _ _) OH _ IN) as OH1. cbn [op_id op_args] in OH1.
  assert (RA : 0 <= a < two64).
  { destruct B as (k & r & F & K & Ha). destruct (RNG k r F K). lia. }
  assert (NFP : ~ Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS OPID (map (den E) args))).
  { intros FPa. exact (proj1 (AP1 a FPa) B). }
  apply (op_cov_mono OPS [(OPID, map (den E) args)]); [| exact (CN _ m mo a OH1 RA NFP)].
  intros o [<-|[]]. unfold insts. apply in_map_iff. exists (OpI OPID args). split; [reflexivity| exact IN].
Qed.

Definition userb (segs : list Segment) (IMGX : list iv) (AW : alloc_world segs IMGX)
    (os : list oinst) (m : word -> option byte) (mo : Model) (z : Z) : Prop :=
  exists args md aw ws ca LB, In (OPID, args) os /\ decode args = Some (md, aw, ws, ca) /\ aw_holds segs IMGX AW aw LB ws m mo /\ in_user LB z.
Definition chg_user (segs : list Segment) (IMGX : list iv) (AW : alloc_world segs IMGX) (OPS : optable)
    (os : list oinst) (m : word -> option byte) (mo : Model) (z : Z) : Prop := op_cov OPS os z \/ userb segs IMGX AW os m mo z.
Definition acc_user_law (segs : list Segment) (IMGX : list iv) (AW : alloc_world segs IMGX) (OPS : optable) : Prop :=
  forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
    op_minv OPS mo -> Forall (fun o => op_holds OPS (fst o) (snd o) m mo) os ->
    (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> chg_user segs IMGX AW OPS os m mo (bv_unsigned a + j)) ->
    exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPS mo' /\
                Forall (fun o => op_holds OPS (fst o) (snd o) m mo') os.
Lemma plain_acc_user_law : forall segs IMGX AW OPS, plain_table OPS -> acc_user_law segs IMGX AW OPS.
Proof.
  intros segs IMGX AW OPS PL os m mo acc MI HO _. exists mo.
  split; [apply mfacts_acc; exact (plain_mf _ _ PL MI)|]. split; assumption.
Qed.

Record heap_ops (segs : list Segment) (IMGX : list iv) (AW : alloc_world segs IMGX) (CW : client_world) (OPS : optable) : Prop := HO {
  ho_holds : forall args m mo, op_holds OPS OPID args m mo = heap_holds segs IMGX AW CW args m mo;
  ho_fp : forall args, op_fp OPS OPID args = heap_fp IMGX args;

  ho_other_z : forall id args a, id <> OPID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
               (exists seg, find_segment segs a 1 = Some seg) \/ in_ivs IMGX a;

  ho_cover : cover_law segs OPS;
  ho_acc_user : acc_user_law segs IMGX AW OPS }.

Lemma ho_other : forall segs IMGX AW CW OPS, heap_ops segs IMGX AW CW OPS ->
  forall id args a, id <> OPID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  (exists seg, find_segment segs a 1 = Some seg) \/ (forall hargs, ~ Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS OPID hargs)).
Proof.
  intros segs IMGX AW CW OPS H id args a NE EX. destruct (ho_other_z _ _ _ _ _ H id args a NE EX) as [S|I]; [left; exact S| right].
  intros hargs FPh. rewrite (ho_fp _ _ _ _ _ H) in FPh.
  destruct (decode hargs) as [[[[md aw] ws] ca]|] eqn:D.
  - apply (proj1 (fp_spec IMGX hargs md aw ws ca a D)) in FPh. exact (proj1 (proj2 FPh) I).
  - unfold heap_fp in FPh. rewrite D in FPh. inversion FPh.
Qed.

Lemma heap_ops_self : forall segs IMGX AW CW, heap_ops segs IMGX AW CW (heap_optable segs IMGX AW CW).
Proof.
  intros segs IMGX AW CW. constructor.
  - intros args m mo. cbn [op_holds heap_optable plain_optable]. rewrite Uint63.eqb_refl. reflexivity.
  - intros args. cbn [op_fp heap_optable plain_optable]. rewrite Uint63.eqb_refl. reflexivity.
  - intros id args a NE EX. cbn [op_fp heap_optable plain_optable] in EX. rewrite (proj2 (Uint63.eqb_false_spec _ _) NE) in EX. inversion EX.
  - apply plain_cover_law. apply plain_table_plain.
  - apply plain_acc_user_law. apply plain_table_plain.
Qed.

Definition win3_eqb (a b : sv * sv * sv) : bool :=
  match a, b with (a1, a2, a3), (b1, b2, b3) => sv_eqb a1 b1 && sv_eqb a2 b2 && sv_eqb a3 b3 end.

Lemma win3_eqb_eq : forall a b, win3_eqb a b = true -> a = b.
Proof.
  intros [[a1 a2] a3] [[b1 b2] b3] H. cbn [win3_eqb] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_eq in H1. apply sv_eqb_eq in H2. apply sv_eqb_eq in H3. congruence.
Qed.

Lemma win3_eqb_refl : forall a, win3_eqb a a = true.
Proof. intros [[a1 a2] a3]. cbn [win3_eqb]. rewrite !sv_eqb_refl. reflexivity. Qed.

Definition kind_of (w : sv * sv * sv) : option Z :=
  match w with (_, _, VL kd) => if wt kd then None else Some (to_Z (wl kd)) | _ => None end.

Lemma kind_of_sound : forall E w kd, kind_of w = Some kd -> w_kind (wden E w) = kd.
Proof.
  intros E [[a b] c] kd H. cbn [kind_of] in H. destruct c; try discriminate. destruct (wt w) eqn:T; [discriminate|].
  injection H as <-. cbn [wden w_kind den]. rewrite wbv_unsigned. unfold w2Z. rewrite T. lia.
Qed.

Lemma kind_ne : forall E w k, (match kind_of w with Some kd => negb (kd =? k) | None => false end) = true -> w_kind (wden E w) <> k.
Proof.
  intros E w k H. destruct (kind_of w) as [kd|] eqn:KO; [|discriminate]. rewrite (kind_of_sound E w kd KO).
  apply negb_true_iff in H. apply Z.eqb_neq in H. exact H.
Qed.

Lemma heap_fp_iff : forall IMGX dargs md aw ws ca a, decode dargs = Some (md, aw, ws, ca) ->
  (Exists (fun p => fst p <= a < snd p) (heap_fp IMGX dargs) <-> (0 <= a < two64 /\ ~ in_ivs IMGX a /\ ~ in_ws ws a)).
Proof. intros. apply fp_spec with (md := md) (aw := aw) (ca := ca). assumption. Qed.

Lemma in_ws_map_iff : forall E ws a, in_ws (map (wden E) ws) a <-> exists w, In w ws /\ in_iv (w_iv (wden E w)) a.
Proof.
  intros E ws a. unfold in_ws. rewrite in_ivs_In. split.
  - intros (v & Hv & Ha). apply in_map_iff in Hv as (w' & <- & Hw'). apply in_map_iff in Hw' as (w & <- & Hw). exists w. auto.
  - intros (w & Hw & Ha). exists (w_iv (wden E w)). split; [|exact Ha]. apply in_map. apply in_map. exact Hw.
Qed.

Lemma in_iv_dec : forall v a, {in_iv v a} + {~ in_iv v a}.
Proof. intros [lo n] a. unfold in_iv. cbn [fst snd]. destruct (Z_le_dec lo a); destruct (Z_lt_dec a (lo + n)); [left; lia| right; lia| right; lia| right; lia]. Qed.

Lemma in_ws_dec : forall ws a, {in_ws ws a} + {~ in_ws ws a}.
Proof. intros ws a. unfold in_ws, in_ivs. apply Exists_dec. intros v. apply in_iv_dec. Qed.

Fixpoint find_cell (idx w : int) (s : slot) : option sv :=
  match s with
  | [] => None
  | c :: s' => if PrimInt63.eqb (c_idx c) idx && PrimInt63.eqb (c_w c) w then Some (c_v c) else find_cell idx w s'
  end.

Definition cell_at (r : region) (off : Z) (w : int) : option sv :=
  match IMap.find (Uint63.of_Z (off / 8)) (rg_cells r) with
  | Some gr => find_cell (Uint63.of_Z (off mod 8)) w (g_cells gr)
  | None => None
  end.

Lemma find_cell_In : forall idx w s v, find_cell idx w s = Some v -> In (Cell idx w v) s.
Proof.
  induction s as [|c s IH]; intros v H; cbn [find_cell] in H; [discriminate|].
  destruct (PrimInt63.eqb (c_idx c) idx && PrimInt63.eqb (c_w c) w) eqn:Q.
  - injection H as <-. apply andb_prop in Q as [Q1 Q2]. apply Uint63.eqb_correct in Q1. apply Uint63.eqb_correct in Q2.
    left. destruct c; cbn in *; subst; reflexivity.
  - right. exact (IH v H).
Qed.

Lemma of_Z_small : forall z, 0 <= z < two63 -> to_Z (Uint63.of_Z z) = z.
Proof. intros z Hz. rewrite Uint63.of_Z_spec. apply Z.mod_small. rewrite wB_two63. exact Hz. Qed.

Lemma keyZ_small : forall z, 0 <= z < two62Z -> keyZ (Uint63.of_Z z) = z.
Proof.
  intros z Hz. unfold two62Z in Hz.
  destruct (keyZ_cases (Uint63.of_Z z)) as [[R K]|[R K]]; rewrite of_Z_small in * by (unfold two63; lia); [exact K| lia].
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma cell_at_ok : forall priv E m k r off w v,
  region_ok segs priv E m k r -> 0 <= off -> off < two62Z -> cell_at r off w = Some v ->
  let c := Cell (Uint63.of_Z (off mod 8)) w v in
  cell_ok segs E m (bv_unsigned (ev E k) + 8 * (off / 8)) c /\ to_Z (c_idx c) = off mod 8 /\
  (PrimInt63.eqb k 0%uint63 = false -> forall i, 0 <= i < to_Z w -> loZ r <= off + i < hiZ E r).
Proof.
  intros priv E m k r off w v RO H0 H62 CA. unfold cell_at in CA.
  destruct (IMap.find (Uint63.of_Z (off / 8)) (rg_cells r)) as [gr|] eqn:F; [|discriminate].
  apply find_cell_In in CA.
  assert (KZ : keyZ (Uint63.of_Z (off / 8)) = off / 8) by (apply keyZ_small; unfold two62Z in *; lia).
  assert (IX : to_Z (Uint63.of_Z (off mod 8)) = off mod 8) by (apply of_Z_small; unfold two63; pose proof (Z.mod_pos_bound off 8); lia).
  destruct (ro_cells _ _ _ _ _ _ RO _ _ F) as [_ FC]. rewrite KZ in FC.
  pose proof (proj1 (Forall_forall _ _) FC _ CA) as CO.
  cbv zeta. split; [exact CO|]. split; [exact IX|].
  intros K i Hi. destruct (ro_cells_in _ _ _ _ _ _ RO _ gr _ i F CA Hi) as [IN _]. specialize (IN K).
  cbn [c_idx] in IN. rewrite KZ, IX in IN. pose proof (Z.div_mod off 8 ltac:(lia)). lia.
Qed.

Lemma cell_at_u64 : forall priv E m k r off v,
  region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> 0 <= off -> off < two62Z ->
  cell_at r off 8%uint63 = Some v ->
  u64_at (bmem_of segs m) (bv_unsigned (ev E k) + off) (bv_unsigned (den E v)) /\ loZ r <= off /\ off + 8 <= hiZ E r.
Proof.
  intros priv E m k r off v RO K H0 H62 CA.
  destruct (cell_at_ok priv E m k r off 8%uint63 v RO H0 H62 CA) as (CO & IX & IN). specialize (IN K). cbn [c_idx] in IX.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [R1 R2].
  assert (L1 := IN 0 ltac:(change (to_Z 8%uint63) with 8; lia)). assert (L2 := IN 7 ltac:(change (to_Z 8%uint63) with 8; lia)).
  split; [| lia].
  pose proof (u64_at_of_cell segs E m (bv_unsigned (ev E k) + 8 * (off / 8)) _ CO eq_refl) as U. cbn [c_idx c_v] in U. rewrite IX in U.
  replace (bv_unsigned (ev E k) + 8 * (off / 8) + off mod 8) with (bv_unsigned (ev E k) + off) in U by (pose proof (Z.div_mod off 8 ltac:(lia)); lia).
  apply U; lia.
Qed.

Lemma cell_at_u32 : forall priv E m k r off v,
  region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> 0 <= off -> off < two62Z ->
  cell_at r off 4%uint63 = Some v ->
  u32_at (bmem_of segs m) (bv_unsigned (ev E k) + off) (bv_unsigned (den E v) mod 2 ^ 32) /\ loZ r <= off /\ off + 4 <= hiZ E r.
Proof.
  intros priv E m k r off v RO K H0 H62 CA.
  destruct (cell_at_ok priv E m k r off 4%uint63 v RO H0 H62 CA) as (CO & IX & IN). specialize (IN K). cbn [c_idx] in IX.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [R1 R2].
  assert (L1 := IN 0 ltac:(change (to_Z 4%uint63) with 4; lia)). assert (L2 := IN 3 ltac:(change (to_Z 4%uint63) with 4; lia)).
  split; [| lia].
  pose proof (u32_at_of_cell segs E m (bv_unsigned (ev E k) + 8 * (off / 8)) _ CO eq_refl) as U. cbn [c_idx c_v] in U. rewrite IX in U.
  replace (bv_unsigned (ev E k) + 8 * (off / 8) + off mod 8) with (bv_unsigned (ev E k) + off) in U by (pose proof (Z.div_mod off 8 ltac:(lia)); lia).
  apply U; lia.
Qed.

Lemma cell_at_u8 : forall priv E m k r off v,
  region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> 0 <= off -> off < two62Z ->
  cell_at r off 1%uint63 = Some v ->
  u8_at (bmem_of segs m) (bv_unsigned (ev E k) + off) (bv_unsigned (den E v) mod 2 ^ 8) /\ loZ r <= off /\ off + 1 <= hiZ E r.
Proof.
  intros priv E m k r off v RO K H0 H62 CA.
  destruct (cell_at_ok priv E m k r off 1%uint63 v RO H0 H62 CA) as (CO & IX & IN). specialize (IN K). cbn [c_idx] in IX.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [R1 R2].
  assert (L1 := IN 0 ltac:(change (to_Z 1%uint63) with 1; lia)).
  split; [| lia].
  pose proof (u8_at_of_cell segs E m (bv_unsigned (ev E k) + 8 * (off / 8)) _ CO eq_refl) as U. cbn [c_idx c_v] in U. rewrite IX in U.
  replace (bv_unsigned (ev E k) + 8 * (off / 8) + off mod 8) with (bv_unsigned (ev E k) + off) in U by (pose proof (Z.div_mod off 8 ltac:(lia)); lia).
  apply U; lia.
Qed.

Definition set_cell8 (r : region) (g : int) (d : bool) (v : sv) : region :=
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r) (IMap.add g (Gran d [Cell 0%uint63 8%uint63 v]) (rg_cells r)).

Definition gran8 (r : region) (g : int) : option (bool * sv) :=
  match IMap.find g (rg_cells r) with
  | Some (Gran d [Cell i w v]) => if PrimInt63.eqb i 0%uint63 && PrimInt63.eqb w 8%uint63 then Some (d, v) else None
  | _ => None
  end.

Lemma gran8_find : forall r g d v, gran8 r g = Some (d, v) -> IMap.find g (rg_cells r) = Some (Gran d [Cell 0%uint63 8%uint63 v]).
Proof.
  intros r g d v H. unfold gran8 in H. destruct (IMap.find g (rg_cells r)) as [[d0 [|[i w v0] [|? ?]]]|]; try discriminate.
  destruct (PrimInt63.eqb i 0) eqn:I0; [|discriminate]. destruct (PrimInt63.eqb w 8) eqn:W8; [|discriminate].
  apply Uint63.eqb_correct in I0. apply Uint63.eqb_correct in W8. subst. cbn [andb] in H. injection H as <- <-. reflexivity.
Qed.

Lemma gran8_cell_at : forall r g d v, gran8 r g = Some (d, v) -> 0 <= keyZ g -> cell_at r (8 * keyZ g) 8%uint63 = Some v.
Proof.
  intros r g d v H HK. unfold cell_at. rewrite Z.mul_comm, Z.div_mul, Z.mod_mul by lia.
  replace (Uint63.of_Z (keyZ g)) with g.
  - rewrite (gran8_find r g d v H). cbn. reflexivity.
  - apply keyZ_inj. rewrite keyZ_small; [reflexivity|]. pose proof (keyZ_range g). unfold two62Z. lia.
Qed.

Lemma region_ok_set_cell8 : forall priv E m k r g d v v',
  region_ok segs priv E m k r -> IMap.find g (rg_cells r) = Some (Gran d [Cell 0%uint63 8%uint63 v]) -> den E v' = den E v ->
  region_ok segs priv E m k (set_cell8 r g d v').
Proof.
  intros priv E m k r g d v v' RO F DV. pose proof (ro_bst _ _ _ _ _ _ RO) as B.
  assert (HI : forall E0, hiZ E0 (set_cell8 r g d v') = hiZ E0 r) by (intros; reflexivity).
  assert (LO : loZ (set_cell8 r g d v') = loZ r) by reflexivity.
  assert (FIND : forall g0 gr, IMap.find g0 (rg_cells (set_cell8 r g d v')) = Some gr ->
            (g0 = g /\ gr = Gran d [Cell 0%uint63 8%uint63 v']) \/ (g0 <> g /\ IMap.find g0 (rg_cells r) = Some gr)).
  { intros g0 gr F0. cbn [set_cell8 rg_cells] in F0. destruct (Uint63.eqb g g0) eqn:GG.
    - apply Uint63.eqb_correct in GG. subst g0. rewrite IMap.find_add_same in F0 by exact B. injection F0 as <-. left. auto.
    - apply Uint63.eqb_false_correct in GG. rewrite IMap.find_add_other in F0 by (exact B || exact GG). right. auto. }
  constructor.
  - cbn [set_cell8 rg_cells]. apply IMap.bst_add. exact B.
  - rewrite HI, LO. exact (ro_range _ _ _ _ _ _ RO).
  - rewrite HI, LO. cbn [set_cell8 rg_w]. exact (ro_valid _ _ _ _ _ _ RO).
  - intros g0 gr F0. destruct (FIND g0 gr F0) as [[-> ->]|[NE F1]]; [| exact (ro_cells _ _ _ _ _ _ RO g0 gr F1)].
    cbn [g_cells]. pose proof (ro_cells _ _ _ _ _ _ RO g _ F) as [SS FC]. cbn [g_cells] in SS, FC. split; [exact SS|].
    constructor; [|constructor]. apply Forall_inv in FC. destruct FC as (C1 & C2 & C3 & C4). cbn [c_idx c_w c_v] in *.
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. intros i Hi. cbn [c_idx c_w c_v] in Hi |- *. rewrite DV. exact (C4 i Hi).
  - intros g0 gr c i F0 Hc Hi. rewrite HI, LO. destruct (FIND g0 gr F0) as [[-> ->]|[NE F1]].
    + cbn [g_cells] in Hc. destruct Hc as [<-|[]].
      exact (ro_cells_in _ _ _ _ _ _ RO g _ (Cell 0%uint63 8%uint63 v) i F ltac:(left; reflexivity) Hi).
    + exact (ro_cells_in _ _ _ _ _ _ RO g0 gr c i F1 Hc Hi).
  - intros o H1 H2 UC. rewrite HI, LO in H1.
    assert (UC' : uncovered r o).
    { intros g0 gr K0 F0. destruct (Uint63.eqb g g0) eqn:GG.
      - apply Uint63.eqb_correct in GG. subst g0. rewrite F in F0. injection F0 as <-.
        destruct (UC g (Gran d [Cell 0%uint63 8%uint63 v']) K0 ltac:(cbn [set_cell8 rg_cells]; rewrite IMap.find_add_same by exact B; reflexivity)) as [D1 D2].
        split; [exact D1|]. cbn [g_cells] in D2 |- *. constructor; [|constructor]. apply Forall_inv in D2. exact D2.
      - apply Uint63.eqb_false_correct in GG. apply (UC g0 gr K0). cbn [set_cell8 rg_cells]. rewrite IMap.find_add_other by (exact B || exact GG). exact F0. }
    pose proof (ro_bg _ _ _ _ _ _ RO o H1 H2 UC') as BG. unfold bg_byte in BG |- *. cbn [set_cell8 rg_bg]. exact BG.
Qed.

End WithSegs.

Fixpoint remove_keys (ks : list int) (R : IMap.t region) : IMap.t region :=
  match ks with [] => R | k :: ks' => remove_keys ks' (IMap.remove k R) end.
Fixpoint add_regions (nr : list (int * region)) (R : IMap.t region) : IMap.t region :=
  match nr with [] => R | kr :: nr' => add_regions nr' (IMap.add (fst kr) (snd kr) R) end.

Lemma remove_keys_bst : forall ks R, IMap.bst R -> IMap.bst (remove_keys ks R).
Proof. induction ks as [|k ks IH]; intros R B; cbn; [exact B| apply IH; apply IMap.bst_remove; exact B]. Qed.
Lemma add_regions_bst : forall nr R, IMap.bst R -> IMap.bst (add_regions nr R).
Proof. induction nr as [|[k r] nr IH]; intros R B; cbn; [exact B| apply IH; apply IMap.bst_add; exact B]. Qed.

Lemma find_remove_keys : forall ks R k r, IMap.bst R ->
  (IMap.find k (remove_keys ks R) = Some r <-> (~ In k ks /\ IMap.find k R = Some r)).
Proof.
  induction ks as [|k0 ks IH]; intros R k r B; cbn [remove_keys In].
  - tauto.
  - rewrite (IH (IMap.remove k0 R) k r (IMap.bst_remove _ _ B)).
    destruct (Uint63.eqb k0 k) eqn:Q.
    + apply Uint63.eqb_correct in Q. subst k0. rewrite IMap.find_remove_same by exact B. split; [intros [_ H]; discriminate| intros [H _]; exfalso; tauto].
    + apply Uint63.eqb_false_correct in Q. rewrite (IMap.find_remove_other k0 k R B Q). tauto.
Qed.

Lemma find_add_regions : forall nr R k r, IMap.bst R -> List.NoDup (map fst nr) ->
  (IMap.find k (add_regions nr R) = Some r <-> (In (k, r) nr \/ (~ In k (map fst nr) /\ IMap.find k R = Some r))).
Proof.
  induction nr as [|[k0 r0] nr IH]; intros R k r B ND; cbn [add_regions map fst snd In].
  - tauto.
  - inversion ND as [|x l N1 N2]; subst.
    rewrite (IH (IMap.add k0 r0 R) k r (IMap.bst_add _ _ _ B) N2).
    destruct (Uint63.eqb k0 k) eqn:Q.
    + apply Uint63.eqb_correct in Q. subst k0. rewrite IMap.find_add_same by exact B.
      split.
      * intros [H|[H1 H2]]; [left; right; exact H|]. injection H2 as <-. left; left; reflexivity.
      * intros [[H|H]|[H1 H2]]; [injection H as <-; right; split; [exact N1| reflexivity]| left; exact H| exfalso; tauto].
    + apply Uint63.eqb_false_correct in Q. rewrite (IMap.find_add_other k0 k r0 R B Q).
      split.
      * intros [H|[H1 H2]]; [left; right; exact H| right; split; [| exact H2]]. intros [X|X]; [congruence| tauto].
      * intros [[H|H]|[H1 H2]]; [congruence| left; exact H| right; split; [tauto| exact H2]].
Qed.

Section Surgery.
Variable segs : list Segment.
Variable OPS : optable.
Variable E : env.

Definition inR (k : int) (r : region) (a : Z) : Prop :=
  bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r.
Definition FP (args : list sv) (a : Z) : Prop :=
  Exists (fun p => fst p <= a < snd p) (op_fp OPS OPID (map (den E) args)).

Hypothesis HFPO : forall id args a, id <> OPID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  (exists seg, find_segment segs a 1 = Some seg) \/ (forall hargs, ~ Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS OPID hargs)).
Hypothesis HPL : cover_law segs OPS.
Variables (st : sstate) (ms : machine_state) (mo : Model) (o : opinst).
Hypothesis HS : st_ok segs OPS E st ms mo.
Variables (pre post : list opinst).
Hypothesis HOPS : s_ops st = pre ++ o :: post.
Hypothesis HID : op_id o = OPID.
Hypothesis HOTH : Forall (fun o' => op_id o' <> OPID) (pre ++ post).
Variables (KS : list int) (NR : list (int * region)) (args' : list sv) (nf : list fact) (next' : int).
Hypothesis HKS : forall k, In k KS -> PrimInt63.eqb k 0%uint63 = false /\ exists r, IMap.find k (s_regs st) = Some r /\ rg_w r = true.
Hypothesis HND : List.NoDup (map fst NR).
Hypothesis HNRnew : forall k r, In (k, r) NR -> PrimInt63.eqb k 0%uint63 = false.
Hypothesis HNRok : forall k r, In (k, r) NR -> region_ok segs (s_priv st) E (ms_mem ms) k r.

Hypothesis HNRfp : forall k r a, In (k, r) NR -> inR k r a ->
  FP (op_args o) a \/ exists k0 r0, In k0 KS /\ IMap.find k0 (s_regs st) = Some r0 /\ inR k0 r0 a.
Hypothesis HNRdisj : forall k1 r1 k2 r2 a, In (k1, r1) NR -> In (k2, r2) NR -> k1 <> k2 -> ~ (inR k1 r1 a /\ inR k2 r2 a).
Hypothesis HHOLD : op_holds OPS OPID (map (den E) args') (ms_mem ms) mo.
Hypothesis HFPnew : forall a, FP args' a ->
  (FP (op_args o) a \/ exists k r, In k KS /\ IMap.find k (s_regs st) = Some r /\ inR k r a) /\
  (forall k r, In (k, r) NR -> ~ inR k r a).
Hypothesis HNF : Forall (fact_holds E) nf.

Definition surg : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (add_regions NR (remove_keys KS (s_regs st))) (nf ++ s_facts st)
     (set_op args' (s_ops st)) (s_priv st) next'.

Lemma surg_ops : s_ops surg = pre ++ OpI OPID args' :: post.
Proof. cbn [surg s_ops]. rewrite HOPS. exact (set_op_split args' pre o post HID HOTH). Qed.

Lemma surg_find : forall k r, IMap.find k (s_regs surg) = Some r ->
  In (k, r) NR \/ (~ In k (map fst NR) /\ ~ In k KS /\ IMap.find k (s_regs st) = Some r).
Proof.
  intros k r H. cbn [surg s_regs] in H. pose proof (so_bst _ _ _ _ _ _ HS) as B.
  apply (proj1 (find_add_regions NR _ k r (remove_keys_bst KS _ B) HND)) in H as [H|[H1 H2]]; [left; exact H| right].
  apply (proj1 (find_remove_keys KS _ k r B)) in H2 as [H2 H3]. auto.
Qed.

Lemma old_apart : forall a, FP (op_args o) a ->
  ~ in_based E (s_regs st) a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv (s_priv st) a).
Proof.
  intros a Ha. pose proof (so_apart _ _ _ _ _ _ HS) as AP. unfold ops_apart in AP. rewrite HOPS in AP.
  pose proof (proj1 (Forall_forall _ _) AP o (in_elt o pre post)) as AP1. cbn beta in AP1. rewrite HID in AP1. exact (AP1 a Ha).
Qed.

Lemma other_apart : forall o', In o' (pre ++ post) -> forall a,
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o') (map (den E) (op_args o'))) ->
  ~ in_based E (s_regs st) a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv (s_priv st) a) /\
  ((exists seg, find_segment segs a 1 = Some seg) \/ (forall hargs, ~ Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS OPID hargs))).
Proof.
  intros o' Ho' a Ha. pose proof (so_apart _ _ _ _ _ _ HS) as AP. unfold ops_apart in AP. rewrite HOPS in AP.
  assert (IN : In o' (pre ++ o :: post)) by (apply in_app_iff in Ho' as [H|H]; apply in_app_iff; [left; exact H| right; right; exact H]).
  pose proof (proj1 (Forall_forall _ _) AP o' IN) as AP1. cbn beta in AP1. destruct (AP1 a Ha) as [A B].
  split; [exact A|]. split; [exact B|].
  exact (HFPO (op_id o') _ a (proj1 (Forall_forall _ _) HOTH o' Ho') Ha).
Qed.

Theorem surgery_sound : st_ok segs OPS E surg ms mo.
Proof.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (APART : ops_apart segs OPS E (set_op args' (s_ops st)) (add_regions NR (remove_keys KS (s_regs st))) (s_priv st)).
  { assert (OTHER : forall o', In o' (pre ++ post) -> forall a,
              Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o') (map (den E) (op_args o'))) ->
              ~ in_based E (add_regions NR (remove_keys KS (s_regs st))) a /\
              ((exists seg, find_segment segs a 1 = Some seg) -> in_priv (s_priv st) a)).
    { intros o' Ho' a Ha. destruct (other_apart o' Ho' a Ha) as (A & B & ZZ). split; [| exact B].
      intros (k & r & Hf & K & Rg). destruct (surg_find k r Hf) as [N|(NN & NK & O)].
      - destruct ZZ as [(seg & SEG)|NFP].
        + destruct (ro_valid _ _ _ _ _ _ (HNRok k r N) (HNRnew k r N) a Rg) as (_ & _ & NS). rewrite NS in SEG. discriminate.
        + destruct (HNRfp k r a N Rg) as [FPo|(k0 & r0 & I0 & F0 & R0)]; [exact (NFP _ FPo)|].
          apply A. destruct (HKS k0 I0) as (K0 & _). exists k0, r0. auto.
      - apply A. exists k, r. auto. }
    pose proof surg_ops as SO. cbn [surg s_ops] in SO. rewrite SO.
    unfold ops_apart. apply Forall_app. split.
    { apply Forall_forall. intros o' Ho'. exact (OTHER o' ltac:(apply in_app_iff; left; exact Ho')). }
    constructor.
    2: { apply Forall_forall. intros o' Ho'. exact (OTHER o' ltac:(apply in_app_iff; right; exact Ho')). }
    cbn [op_id op_args]. intros a Ha.
    destruct (HFPnew a Ha) as [OLD NEW]. split.
    + intros (k & r & Hf & K & Rg). destruct (surg_find k r Hf) as [N|(NN & NK & O)]; [exact (NEW k r N Rg)|].
      destruct OLD as [FPo|(k0 & r0 & I0 & F0 & R0)].
      * apply (proj1 (old_apart a FPo)). exists k, r. auto.
      * destruct (HKS k0 I0) as (K0 & r0' & F0' & W0). rewrite F0 in F0'. injection F0' as <-.
        assert (NE0 : k0 <> k) by (intros ->; exact (NK I0)).
        exact (Pdisj k0 r0 k r F0 O NE0 K0 K (or_introl W0) a (conj R0 Rg)).
    + intros SEG. destruct OLD as [FPo|(k0 & r0 & I0 & F0 & R0)]; [exact (proj2 (old_apart a FPo) SEG)|].
      destruct (HKS k0 I0) as (K0 & _). destruct SEG as [seg SEG].
      destruct (ro_valid _ _ _ _ _ _ (Preg k0 r0 F0) K0 a R0) as (_ & _ & NS). rewrite NS in SEG. discriminate. }
  constructor; cbn [surg s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply add_regions_bst. apply remove_keys_bst. exact Pbst.
  - intros k r Hf. destruct (surg_find k r Hf) as [H|(_ & _ & H)]; [exact (HNRok k r H)| exact (Preg k r H)].
  - assert (NEWOLD : forall k1 r1 k2 r2 a, In (k1, r1) NR -> ~ In k2 KS -> IMap.find k2 (s_regs st) = Some r2 ->
              PrimInt63.eqb k2 0%uint63 = false -> inR k1 r1 a -> inR k2 r2 a -> False).
    { intros k1 r1 k2 r2 a N1 NK2 O2 K2 A1 A2. destruct (HNRfp k1 r1 a N1 A1) as [FPo|(k0 & r0 & I0 & F0 & R0)].
      - apply (proj1 (old_apart a FPo)). exists k2, r2. auto.
      - destruct (HKS k0 I0) as (K0 & r0' & F0' & W0). rewrite F0 in F0'. injection F0' as <-.
        assert (NE0 : k0 <> k2) by (intros ->; exact (NK2 I0)).
        exact (Pdisj k0 r0 k2 r2 F0 O2 NE0 K0 K2 (or_introl W0) a (conj R0 A2)). }
    intros k1 r1 k2 r2 H1 H2 NE K1 K2 W a [A1 A2].
    destruct (surg_find k1 r1 H1) as [N1|(_ & NK1 & O1)]; destruct (surg_find k2 r2 H2) as [N2|(_ & NK2 & O2)].
    + exact (HNRdisj k1 r1 k2 r2 a N1 N2 NE (conj A1 A2)).
    + exact (NEWOLD k1 r1 k2 r2 a N1 NK2 O2 K2 A1 A2).
    + exact (NEWOLD k2 r2 k1 r1 a N2 NK1 O1 K1 A2 A1).
    + exact (Pdisj k1 r1 k2 r2 O1 O2 NE K1 K2 W a (conj A1 A2)).
  - intros r g gr c F0. destruct (surg_find _ r F0) as [N|(_ & _ & O)].
    + pose proof (HNRnew _ r N) as X. rewrite Uint63.eqb_refl in X. discriminate.
    + exact (Ppub r g gr c O).
  - unfold facts_hold. apply Forall_app. split; [exact HNF| exact Pfacts].
  - pose proof surg_ops as SO. cbn [surg s_ops] in SO. rewrite SO.
    unfold ops_hold in *. rewrite HOPS in Pops. apply Forall_app in Pops as [P1 P2]. apply Forall_app. split; [exact P1|].
    constructor; [| exact (Forall_inv_tail P2)]. cbn [op_id op_args]. exact HHOLD.
  -
    pose proof surg_ops as SO. cbn [surg s_ops] in SO.
    apply (cover_of_apart segs OPS E _ _ (s_priv st) (ms_mem ms) mo args' HPL APART).
    + rewrite SO. unfold ops_hold in *. rewrite HOPS in Pops. apply Forall_app in Pops as [P1 P2]. apply Forall_app. split; [exact P1|].
      constructor; [| exact (Forall_inv_tail P2)]. cbn [op_id op_args]. exact HHOLD.
    + rewrite SO. apply in_elt.
    + intros k r Hf K. destruct (surg_find k r Hf) as [N|(_ & _ & O)].
      * exact (ro_range _ _ _ _ _ _ (HNRok k r N) K).
      * exact (ro_range _ _ _ _ _ _ (Preg k r O) K).
Qed.
End Surgery.

Section Fresh.
Variable segs : list Segment.

Lemma rdZ_nonneg : forall bm n a v, (forall x y, bm x = Some y -> 0 <= y < 256) -> rdZ bm a n = Some v -> 0 <= v < 2 ^ (8 * Z.of_nat n).
Proof.
  intros bm n. induction n as [|n IH]; intros a v BR H; cbn [rdZ] in H.
  - injection H as <-. cbn. lia.
  - destruct (bm a) as [b|] eqn:Hb; [|discriminate]. destruct (rdZ bm (a + 1) n) as [r|] eqn:Hr; [|discriminate].
    injection H as <-. pose proof (BR _ _ Hb). pose proof (IH _ _ BR Hr).
    rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat n)) with (8 + 8 * Z.of_nat n) by lia. rewrite Z.pow_add_r by lia.
    change (2 ^ 8) with 256. nia.
Qed.

Lemma rdZ_bytes : forall bm n a v, (forall x y, bm x = Some y -> 0 <= y < 256) -> rdZ bm a n = Some v ->
  forall i, 0 <= i < Z.of_nat n -> bm (a + i) = Some (zbyte v i).
Proof.
  intros bm n. induction n as [|n IH]; intros a v BR H i Hi; cbn [rdZ] in H.
  - cbn in Hi. lia.
  - destruct (bm a) as [b|] eqn:Hb; [|discriminate]. destruct (rdZ bm (a + 1) n) as [r|] eqn:Hr; [|discriminate].
    injection H as <-. pose proof (BR _ _ Hb) as Rb. pose proof (rdZ_nonneg bm n (a + 1) r BR Hr) as Rr.
    destruct (Z.eq_dec i 0) as [->|NZ].
    + rewrite Z.add_0_r, Hb. f_equal. unfold zbyte. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
      replace ((b + 256 * r) mod 256) with (b mod 256) by (rewrite <- (Z_mod_plus_full b r 256); f_equal; lia).
      symmetry. apply Z.mod_small. lia.
    + replace (a + i) with (a + 1 + (i - 1)) by lia. rewrite (IH (a + 1) r BR Hr (i - 1)) by (rewrite Nat2Z.inj_succ in Hi; lia).
      f_equal. unfold zbyte. replace (8 * i) with (8 + 8 * (i - 1)) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
      rewrite <- Z.div_div by (try apply Z.pow_pos_nonneg; lia).
      replace ((b + 256 * r) / 256) with r; [reflexivity|].
      replace (b + 256 * r) with (r * 256 + b) by lia. rewrite Z_div_plus_full_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma bmem_of_bytes_range : forall m x y, bmem_of segs m x = Some y -> 0 <= y < 256.
Proof. intros m x y H. exact (proj2 (bmem_of_range segs m x y H)). Qed.

Lemma zbyte_mod : forall u n i, 0 <= i -> i < n -> zbyte (u mod 2 ^ (8 * n)) i = zbyte u i.
Proof.
  intros u n i Hi Hn. apply Z.bits_inj'. intros r Hr. destruct (Z.lt_ge_cases r 8).
  - rewrite !zbyte_testbit by lia. apply Z.mod_pow2_bits_low. lia.
  - unfold zbyte. replace 256 with (2 ^ 8) by reflexivity. rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma cell_ok_of_rdZ : forall E m B idx (n : int) (v : sv) z,
  0 <= to_Z idx -> 0 < to_Z n -> to_Z idx + to_Z n <= 8 ->
  rdZ (bmem_of segs m) (B + to_Z idx) (Z.to_nat (to_Z n)) = Some z ->
  bv_unsigned (den E v) mod 2 ^ (8 * to_Z n) = z ->
  cell_ok segs E m B (Cell idx n v).
Proof.
  intros E m B idx n v z Hi Hn H8 RD HV. unfold cell_ok. cbn [c_idx c_w c_v].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact H8|].
  intros i Hri.
  pose proof (rdZ_bytes (bmem_of segs m) (Z.to_nat (to_Z n)) (B + to_Z idx) z (bmem_of_bytes_range m) RD i ltac:(rewrite Z2Nat.id by lia; exact Hri)) as BY.
  unfold bmem_of in BY.
  destruct ((0 <=? B + to_Z idx + i) && (B + to_Z idx + i <? two64)); [|discriminate].
  destruct (rb segs m (B + to_Z idx + i)) as [b|] eqn:RB; [|discriminate]. cbn [option_map] in BY. injection BY as BY.
  f_equal. apply bv_eq. rewrite BY, byte_of_zbyte by lia. rewrite <- HV. apply zbyte_mod; lia.
Qed.

Lemma cell_ok_of_u64 : forall E m B idx v z,
  0 <= to_Z idx -> to_Z idx + 8 <= 8 -> u64_at (bmem_of segs m) (B + to_Z idx) z -> bv_unsigned (den E v) = z ->
  cell_ok segs E m B (Cell idx 8%uint63 v).
Proof.
  intros E m B idx v z Hi H8 U HV. apply (cell_ok_of_rdZ E m B idx 8%uint63 v z Hi ltac:(change (to_Z 8%uint63) with 8; lia) H8 U).
  change (8 * to_Z 8%uint63) with 64. rewrite HV. apply Z.mod_small.
  pose proof (rdZ_nonneg _ _ _ _ (bmem_of_bytes_range m) U) as R. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul] in R. lia.
Qed.

Lemma cell_ok_of_u32 : forall E m B idx v z,
  0 <= to_Z idx -> to_Z idx + 4 <= 8 -> u32_at (bmem_of segs m) (B + to_Z idx) z -> bv_unsigned (den E v) mod 2 ^ 32 = z ->
  cell_ok segs E m B (Cell idx 4%uint63 v).
Proof.
  intros E m B idx v z Hi H8 U HV. exact (cell_ok_of_rdZ E m B idx 4%uint63 v z Hi ltac:(change (to_Z 4%uint63) with 4; lia) H8 U HV).
Qed.

Lemma cell_ok_of_u8 : forall E m B idx v z,
  0 <= to_Z idx -> to_Z idx + 1 <= 8 -> u8_at (bmem_of segs m) (B + to_Z idx) z -> bv_unsigned (den E v) mod 2 ^ 8 = z ->
  cell_ok segs E m B (Cell idx 1%uint63 v).
Proof.
  intros E m B idx v z Hi H8 U HV. exact (cell_ok_of_rdZ E m B idx 1%uint63 v z Hi ltac:(change (to_Z 1%uint63) with 1; lia) H8 U HV).
Qed.

Lemma region_ok_fresh : forall priv E m k r,
  PrimInt63.eqb k 0%uint63 = false ->
  IMap.bst (rg_cells r) -> rg_bg r = BGNone ->
  0 <= bv_unsigned (ev E k) + loZ r -> bv_unsigned (ev E k) + hiZ E r < two64 ->
  (forall a, bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r ->
     m (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None) ->
  (forall g gr, IMap.find g (rg_cells r) = Some gr ->
     slot_ok segs E m (bv_unsigned (ev E k) + 8 * keyZ g) (g_cells gr) /\
     (forall c i, In c (g_cells gr) -> 0 <= i < to_Z (c_w c) -> loZ r <= 8 * keyZ g + to_Z (c_idx c) + i < hiZ E r)) ->
  region_ok segs priv E m k r.
Proof.
  intros priv E m k r K B BG R1 R2 BY CE. constructor.
  - exact B.
  - intros _. split; [exact R1| exact R2].
  - intros _ a Ha. destruct (BY a Ha) as [M NS]. split; [| split; [| exact NS]].
    + unfold rb. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Mb; [discriminate| contradiction].
    + intros _. unfold wb, wview. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Mb; [reflexivity| contradiction].
  - intros g gr F. exact (proj1 (CE g gr F)).
  - intros g gr c i F Hc Hi. cbv zeta. split; [intros _; exact (proj2 (CE g gr F) c i Hc Hi)|]. intros K'. rewrite K in K'. discriminate.
  - intros o _ _ _. unfold bg_byte. rewrite BG. exact I.
Qed.

End Fresh.

Definition mterm : Type := list (sv * w64).

Fixpoint madd1 (t : mterm) (a : sv) (c : w64) : mterm :=
  match t with
  | [] => if weqb c wzero then [] else [(a, c)]
  | (a', c') :: t' =>
      if sv_eqb a' a then (let c2 := wadd c' c in if weqb c2 wzero then t' else (a', c2) :: t')
      else (a', c') :: madd1 t' a c
  end.
Fixpoint madd (t u : mterm) : mterm := match u with [] => t | (a, c) :: u' => madd (madd1 t a c) u' end.
Definition mneg (t : mterm) : mterm := map (fun p => (fst p, W64.wneg (snd p))) t.

Fixpoint mlin (v : sv) : mterm * w64 :=
  match v with
  | VL c => ([], c)
  | VP k o => ([(VP k wzero, wone)], o)
  | VAlu ALU_ADD a b => let (ta, ca) := mlin a in let (tb, cb) := mlin b in (madd ta tb, wadd ca cb)
  | VAlu ALU_SUB a b => let (ta, ca) := mlin a in let (tb, cb) := mlin b in (madd ta (mneg tb), wsub ca cb)
  | _ => ([(v, wone)], wzero)
  end.

Definition msame (a b : sv) : bool :=
  let (t, c) := mlin (VAlu ALU_SUB a b) in match t with [] => weqb c wzero | _ => false end.

Section MLin.
Variable E : env.
Definition U (v : sv) : Z := bv_unsigned (den E v).
Fixpoint meval (t : mterm) : Z := match t with [] => 0 | (a, c) :: t' => w2Z c * U a + meval t' end.

Lemma mod_ex : forall x, exists q, x mod two64 = x + q * two64.
Proof. intros x. exists (- (x / two64)). pose proof (Z.div_mod x two64 ltac:(unfold two64; lia)). lia. Qed.

Lemma madd1_ok : forall t a c, exists q, meval (madd1 t a c) = meval t + w2Z c * U a + q * two64.
Proof.
  induction t as [|[a' c'] t IH]; intros a c; cbn [madd1 meval].
  - destruct (weqb c wzero) eqn:Z0.
    + apply (proj1 (weqb_ok _ _)) in Z0. subst c. exists 0. cbn [meval]. rewrite wzero_ok. lia.
    + exists 0. cbn [meval]. lia.
  - destruct (sv_eqb a' a) eqn:EQ.
    + apply sv_eqb_eq in EQ. subst a'. pose proof (wadd_ok c' c) as W. destruct (mod_ex (w2Z c' + w2Z c)) as [q Hq]. rewrite Hq in W.
      destruct (weqb (wadd c' c) wzero) eqn:Z0.
      * apply (proj1 (weqb_ok _ _)) in Z0. rewrite Z0, wzero_ok in W. exists (q * U a).
        assert (X : (w2Z c' + w2Z c + q * two64) * U a = 0) by (rewrite <- W; reflexivity). nia.
      * cbn [meval]. rewrite W. exists (q * U a). nia.
    + destruct (IH a c) as [q Hq]. cbn [meval]. rewrite Hq. exists q. lia.
Qed.

Lemma madd_ok : forall u t, exists q, meval (madd t u) = meval t + meval u + q * two64.
Proof.
  induction u as [|[a c] u IH]; intros t; cbn [madd meval].
  - exists 0. lia.
  - destruct (IH (madd1 t a c)) as [q1 H1]. destruct (madd1_ok t a c) as [q2 H2]. rewrite H1, H2. exists (q1 + q2). lia.
Qed.

Lemma mneg_ok : forall t, exists q, meval (mneg t) = - meval t + q * two64.
Proof.
  induction t as [|[a c] t IH]; cbn [mneg map meval fst snd].
  - exists 0. lia.
  - destruct IH as [q Hq]. unfold mneg in Hq. rewrite Hq. pose proof (wneg_ok c) as W. destruct (mod_ex (- w2Z c)) as [q2 H2].
    rewrite H2 in W. rewrite W. exists (q + q2 * U a). nia.
Qed.

Lemma mlin_ok : forall v, exists q, U v = meval (fst (mlin v)) + w2Z (snd (mlin v)) + q * two64.
Proof.
  assert (UR : forall v, 0 <= U v < two64) by (intros v; unfold U; pose proof (bv_unsigned_in_range _ (den E v)) as R; rewrite bv_modulus_64 in R; exact R).
  induction v; try (exists 0; cbn [mlin fst snd meval]; rewrite wzero_ok, wone_ok; lia).
  - exists 0. cbn [mlin fst snd meval]. unfold U. cbn [den]. rewrite wbv_unsigned. lia.
  - cbn [mlin fst snd meval]. unfold U at 1. rewrite den_VPu. destruct (mod_ex (bv_unsigned (ev E k) + w2Z off)) as [q Hq]. rewrite Hq.
    unfold U. rewrite (den_VP0 E k wzero (weqb_refl _)), wone_ok. exists q. lia.
  - destruct op; try (exists 0; cbn [mlin fst snd meval]; rewrite wzero_ok, wone_ok; lia).
    +   cbn [mlin]. destruct (mlin v1) as [ta ca]. destruct (mlin v2) as [tb cb]. cbn [fst snd] in *.
      destruct IHv1 as [qa Ha]. destruct IHv2 as [qb Hb]. destruct (madd_ok tb ta) as [qm Hm]. rewrite Hm.
      pose proof (wadd_ok ca cb) as W. destruct (mod_ex (w2Z ca + w2Z cb)) as [qc Hc]. rewrite Hc in W. rewrite W.
      unfold U at 1. cbn [den alu64 alu]. rewrite bv_add_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
      fold (U v1) (U v2). change (2 ^ 64) with two64. destruct (mod_ex (U v1 + U v2)) as [q0 H0]. rewrite H0, Ha, Hb.
      exists (qa + qb + q0 - qm - qc). lia.
    +   cbn [mlin]. destruct (mlin v1) as [ta ca]. destruct (mlin v2) as [tb cb]. cbn [fst snd] in *.
      destruct IHv1 as [qa Ha]. destruct IHv2 as [qb Hb]. destruct (madd_ok (mneg tb) ta) as [qm Hm]. rewrite Hm.
      destruct (mneg_ok tb) as [qn Hn]. rewrite Hn.
      pose proof (wsub_ok ca cb) as W. destruct (mod_ex (w2Z ca - w2Z cb)) as [qc Hc]. rewrite Hc in W. rewrite W.
      unfold U at 1. cbn [den alu64 alu]. rewrite bv_sub_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
      fold (U v1) (U v2). change (2 ^ 64) with two64. destruct (mod_ex (U v1 - U v2)) as [q0 H0]. rewrite H0, Ha, Hb.
      exists (qa - qb + q0 - qm - qn - qc). lia.
Qed.

Lemma msame_sound : forall a b, msame a b = true -> den E a = den E b.
Proof.
  intros a b H. unfold msame in H. destruct (mlin (VAlu ALU_SUB a b)) as [t c] eqn:ML.
  destruct t; [|discriminate]. apply (proj1 (weqb_ok _ _)) in H. subst c.
  destruct (mlin_ok (VAlu ALU_SUB a b)) as [q Hq]. rewrite ML in Hq. cbn [fst snd meval] in Hq. rewrite wzero_ok in Hq.
  pose proof (bv_unsigned_in_range _ (den E a)) as RA. pose proof (bv_unsigned_in_range _ (den E b)) as RB. rewrite bv_modulus_64 in RA, RB.
  unfold U in Hq. cbn [den alu64 alu] in Hq. rewrite bv_sub_unsigned in Hq. unfold bv_wrap in Hq. rewrite bv_modulus_64 in Hq.
  pose proof (Z.mod_pos_bound (bv_unsigned (den E a) - bv_unsigned (den E b)) (2 ^ 64) ltac:(lia)) as MB.
  apply bv_eq. unfold two64 in *.
  assert (q = 0 \/ q = 1 \/ q = -1) by nia.
  pose proof (Z.div_mod (bv_unsigned (den E a) - bv_unsigned (den E b)) (2 ^ 64) ltac:(lia)) as DM. nia.
Qed.
End MLin.

End UG.
