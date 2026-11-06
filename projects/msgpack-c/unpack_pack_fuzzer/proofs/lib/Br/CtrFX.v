(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia Permutation.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB PlanS CtrLib CtrA HeapOp.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module CtrFX.

Definition not_id (id : int) (o : opinst) : Prop := PrimInt63.eqb (op_id o) id = false.

Lemma Forall_app3 : forall {A} (P : A -> Prop) l1 x l2, Forall P (l1 ++ x :: l2) <-> Forall P l1 /\ P x /\ Forall P l2.
Proof. intros A P l1 x l2. rewrite Forall_app, Forall_cons_iff. tauto. Qed.

Lemma count_op_app : forall id l1 l2, count_op id (l1 ++ l2) = (count_op id l1 + count_op id l2)%nat.
Proof. induction l1 as [|o l1 IH]; intros l2; cbn [count_op app]; [reflexivity|]. rewrite IH. destruct (PrimInt63.eqb _ _); reflexivity. Qed.

Lemma count_op_zero : forall id l, count_op id l = O <-> Forall (not_id id) l.
Proof.
  induction l as [|o l IH]; cbn [count_op].
  - split; [intros; constructor| reflexivity].
  - unfold not_id at 1. destruct (PrimInt63.eqb (op_id o) id) eqn:E.
    + split; [discriminate|]. intros F. inversion F; subst. unfold not_id in H1. rewrite E in H1. discriminate.
    + rewrite IH. split; [intros F; constructor; assumption| intros F; inversion F; assumption].
Qed.

Lemma find_op_unique : forall id os args, find_op id os = Some args -> count_op id os = 1%nat ->
  exists l1 l2, os = l1 ++ OpI id args :: l2 /\ Forall (not_id id) l1 /\ Forall (not_id id) l2.
Proof.
  induction os as [|o os IH]; intros args H C; cbn [find_op count_op] in H, C; [discriminate|].
  destruct (PrimInt63.eqb (op_id o) id) eqn:E.
  - injection H as <-. apply Uint63.eqb_correct in E. injection C as C. exists [], os.
    split; [destruct o; cbn in E |- *; subst; reflexivity|]. split; [constructor|]. apply count_op_zero. exact C.
  - destruct (IH args H C) as (l1 & l2 & -> & F1 & F2). exists (o :: l1), l2.
    split; [reflexivity|]. split; [constructor; [exact E| exact F1]| exact F2].
Qed.

Lemma set_op_split : forall id args' l1 l2 args, Forall (not_id id) l1 ->
  set_op id args' (l1 ++ OpI id args :: l2) = l1 ++ OpI id args' :: l2.
Proof.
  induction l1 as [|o l1 IH]; intros l2 args F; cbn [set_op app].
  - cbn [op_id]. rewrite Uint63.eqb_refl. reflexivity.
  - inversion F; subst. unfold not_id in H1. rewrite H1. f_equal. apply IH. assumption.
Qed.

Lemma find_op_split : forall id os args, find_op id os = Some args ->
  exists l1 l2, os = l1 ++ OpI id args :: l2 /\ Forall (not_id id) l1.
Proof.
  induction os as [|o os IH]; intros args H; cbn [find_op] in H; [discriminate|].
  destruct (PrimInt63.eqb (op_id o) id) eqn:E.
  - injection H as <-. apply Uint63.eqb_correct in E. exists [], os.
    split; [destruct o; cbn in E |- *; subst; reflexivity| constructor].
  - destruct (IH args H) as (l1 & l2 & -> & F1). exists (o :: l1), l2. split; [reflexivity| constructor; [exact E| exact F1]].
Qed.

Lemma ops_hold_set_op1 : forall OPS E os id args args' m mo,
  find_op id os = Some args -> ops_hold OPS E os m mo ->
  op_holds OPS id (map (den E) args') m mo ->
  ops_hold OPS E (set_op id args' os) m mo.
Proof.
  intros OPS E os id args args' m mo Hf H Hnew.
  destruct (find_op_split id os args Hf) as (l1 & l2 & E0 & F1). rewrite E0 in H |- *. rewrite (set_op_split id args' l1 l2 args F1).
  unfold ops_hold in *. apply Forall_app3 in H as (H1 & H2 & H3). apply Forall_app3. auto.
Qed.

Lemma ops_apart_set_op1 : forall segs OPS E os id args args' R priv,
  find_op id os = Some args -> ops_apart segs OPS E os R priv ->
  op_fp OPS id (map (den E) args') = op_fp OPS id (map (den E) args) ->
  ops_apart segs OPS E (set_op id args' os) R priv.
Proof.
  intros segs OPS E os id args args' R priv Hf H Hfp.
  destruct (find_op_split id os args Hf) as (l1 & l2 & E0 & F1). rewrite E0 in H |- *. rewrite (set_op_split id args' l1 l2 args F1).
  unfold ops_apart in *. apply Forall_app3 in H as (H1 & H2 & H3). apply Forall_app3. split; [exact H1|]. split; [| exact H3].
  cbn [op_id op_args] in *. rewrite Hfp. exact H2.
Qed.

Lemma find_op_In : forall id os args, find_op id os = Some args -> In (OpI id args) os.
Proof.
  induction os as [|o os IH]; intros args H; cbn [find_op] in H; [discriminate|].
  destruct (PrimInt63.eqb (op_id o) id) eqn:E.
  - injection H as <-. apply Uint63.eqb_correct in E. left. destruct o; cbn in E |- *. subst. reflexivity.
  - right. apply IH. exact H.
Qed.

Lemma ops_hold_set_op : forall OPS E E' os id args args' m m' mo mo',
  find_op id os = Some args -> count_op id os = 1%nat ->
  ops_hold OPS E os m mo ->
  (forall o, In o os -> not_id id o -> op_holds OPS (op_id o) (map (den E) (op_args o)) m mo ->
             op_holds OPS (op_id o) (map (den E') (op_args o)) m' mo') ->
  op_holds OPS id (map (den E') args') m' mo' ->
  ops_hold OPS E' (set_op id args' os) m' mo'.
Proof.
  intros OPS E E' os id args args' m m' mo mo' Hf Hc H Hother Hnew.
  destruct (find_op_unique id os args Hf Hc) as (l1 & l2 & E0 & F1 & F2). rewrite E0 in H |- *.
  rewrite (set_op_split id args' l1 l2 args F1).
  unfold ops_hold in *. apply Forall_app3 in H as (H1 & H2 & H3). apply Forall_app3. split; [|split; [exact Hnew|]].
  - apply Forall_forall. intros o Ho. apply Hother; [rewrite E0; apply in_app_iff; left; exact Ho| |].
    + exact (proj1 (Forall_forall _ _) F1 o Ho). + exact (proj1 (Forall_forall _ _) H1 o Ho).
  - apply Forall_forall. intros o Ho. apply Hother; [rewrite E0; apply in_app_iff; right; right; exact Ho| |].
    + exact (proj1 (Forall_forall _ _) F2 o Ho). + exact (proj1 (Forall_forall _ _) H3 o Ho).
Qed.

Lemma ops_apart_set_op : forall segs OPS E E' os id args args' R R' priv,
  find_op id os = Some args -> count_op id os = 1%nat ->
  ops_apart segs OPS E os R priv ->
  (forall o a, In o os -> not_id id o ->
      (Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))) ->
       ~ in_based E R a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv priv a)) ->
      Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E') (op_args o))) ->
      ~ in_based E' R' a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv priv a)) ->
  (forall a, Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id (map (den E') args')) ->
      ~ in_based E' R' a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv priv a)) ->
  ops_apart segs OPS E' (set_op id args' os) R' priv.
Proof.
  intros segs OPS E E' os id args args' R R' priv Hf Hc H Hother Hnew.
  destruct (find_op_unique id os args Hf Hc) as (l1 & l2 & E0 & F1 & F2). rewrite E0 in H |- *.
  rewrite (set_op_split id args' l1 l2 args F1).
  unfold ops_apart in *. apply Forall_app3 in H as (H1 & H2 & H3). apply Forall_app3. split; [|split; [exact Hnew|]].
  - apply Forall_forall. intros o Ho a. apply Hother; [rewrite E0; apply in_app_iff; left; exact Ho| |].
    + exact (proj1 (Forall_forall _ _) F1 o Ho). + exact (proj1 (Forall_forall _ _) H1 o Ho a).
  - apply Forall_forall. intros o Ho a. apply Hother; [rewrite E0; apply in_app_iff; right; right; exact Ho| |].
    + exact (proj1 (Forall_forall _ _) F2 o Ho). + exact (proj1 (Forall_forall _ _) H3 o Ho a).
Qed.

Lemma ops_hold_find : forall OPS E os m mo id args, ops_hold OPS E os m mo -> find_op id os = Some args ->
  op_holds OPS id (map (den E) args) m mo.
Proof.
  intros OPS E os m mo id args H Hf. exact (proj1 (Forall_forall _ _) H _ (find_op_In id os args Hf)).
Qed.

Lemma ops_apart_find : forall segs OPS E os R priv id args a, ops_apart segs OPS E os R priv -> find_op id os = Some args ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id (map (den E) args)) ->
  ~ in_based E R a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv priv a).
Proof.
  intros segs OPS E os R priv id args a H Hf. exact (proj1 (Forall_forall _ _) H _ (find_op_In id os args Hf) a).
Qed.

Fixpoint wins_of (E : env) (n : nat) (ws : list sv) : list window :=
  match n, ws with
  | S n', lo :: len :: kd :: ws' => Win (bv_unsigned (den E lo)) (bv_unsigned (den E len)) (bv_unsigned (den E kd)) :: wins_of E n' ws'
  | _, _ => []
  end.

Lemma wins_of_cons : forall E n lo len kd ws,
  wins_of E (S n) (lo :: len :: kd :: ws) = Win (bv_unsigned (den E lo)) (bv_unsigned (den E len)) (bv_unsigned (den E kd)) :: wins_of E n ws.
Proof. reflexivity. Qed.

Lemma decode_windows_map : forall E n ws, (3 * n <= length ws)%nat ->
  decode_windows n (map (den E) ws) = Some (wins_of E n ws, map (den E) (skipn (3 * n) ws)).
Proof.
  intros E n. induction n as [|n IH]; intros ws Hl.
  - cbn. reflexivity.
  - destruct ws as [|lo [|len [|kd ws']]]; cbn [length] in Hl; try lia.
    cbn [map decode_windows wins_of]. rewrite (IH ws') by lia.
    replace (3 * S n)%nat with (S (S (S (3 * n)))) by lia. reflexivity.
Qed.

Lemma den_VL : forall E w, den E (VL w) = wbv w.
Proof. reflexivity. Qed.
Lemma unsigned_VL : forall E w, bv_unsigned (den E (VL w)) = w2Z w.
Proof. intros. rewrite den_VL. apply wbv_unsigned. Qed.
Lemma w2Z_nowt : forall w, wt w = false -> w2Z w = to_Z (wl w).
Proof. intros [t l] H. cbn in H |- *. subst. unfold w2Z. cbn. lia. Qed.

Lemma heap_nwin_shape : forall hargs n, heap_nwin hargs = Some n ->
  exists md A nw rest, hargs = VL md :: A :: VL nw :: rest /\ wt nw = false /\ n = Z.to_nat (to_Z (wl nw)) /\ (3 * n <= length rest)%nat.
Proof.
  intros hargs n H. unfold heap_nwin in H.
  destruct hargs as [|[md| | | | | | | | | |] [|A [|[nw| | | | | | | | | |] rest]]]; try discriminate.
  destruct (wt nw) eqn:T; [discriminate|].
  destruct (Nat.leb (3 * Z.to_nat (to_Z (wl nw))) (length rest)) eqn:L; [|discriminate].
  injection H as <-. apply Nat.leb_le in L. exists md, A, nw, rest. auto.
Qed.

Lemma decode_hargs : forall E md A nw rest n,
  wt nw = false -> n = Z.to_nat (to_Z (wl nw)) -> (3 * n <= length rest)%nat ->
  decode (map (den E) (VL md :: A :: VL nw :: rest)) =
    Some (w2Z md, den E A, wins_of E n rest, map (den E) (skipn (3 * n) rest)).
Proof.
  intros E md A nw rest n T N L. cbn [map decode]. rewrite !unsigned_VL, (w2Z_nowt nw T), <- N.
  rewrite (decode_windows_map E n rest L). reflexivity.
Qed.

Lemma decode_set_A : forall E x a a' y rest md aw ws ca,
  decode (map (den E) (x :: a :: y :: rest)) = Some (md, aw, ws, ca) ->
  decode (map (den E) (x :: a' :: y :: rest)) = Some (md, den E a', ws, ca) /\ aw = den E a.
Proof.
  intros E x a a' y rest md aw ws ca H. cbn [map decode] in H |- *.
  destruct (decode_windows _ _) as [[ws' ca']|]; [|discriminate]. injection H as <- <- <- <-. auto.
Qed.

Lemma heap_set_A_shape : forall hargs a hargs', heap_set_A hargs a = Some hargs' ->
  exists md A nw rest, hargs = VL md :: A :: VL nw :: rest /\ hargs' = VL md :: a :: VL nw :: rest.
Proof.
  intros hargs a hargs' H. unfold heap_set_A in H.
  destruct hargs as [|[md| | | | | | | | | |] [|A [|[nw| | | | | | | | | |] rest]]]; try discriminate.
  injection H as <-. exists md, A, nw, rest. auto.
Qed.

Lemma heap_set_A_eq : forall md A nw rest a,
  heap_set_A (VL md :: A :: VL nw :: rest) a = Some (VL md :: a :: VL nw :: rest).
Proof. reflexivity. Qed.
Lemma heap_A_eq : forall md A nw rest, heap_A (VL md :: A :: VL nw :: rest) = Some A.
Proof. reflexivity. Qed.

Lemma heap_add_window_eq : forall md A nw rest n lo len kd,
  heap_nwin (VL md :: A :: VL nw :: rest) = Some n ->
  heap_add_window (VL md :: A :: VL nw :: rest) lo len kd =
    Some (VL md :: A :: VL (wadd nw wone) :: firstn (3 * n) rest ++ [lo; len; kd] ++ skipn (3 * n) rest).
Proof. intros md A nw rest n lo len kd H. unfold heap_add_window. rewrite H. reflexivity. Qed.

Lemma wins_of_firstn : forall E n ws tail, (3 * n <= length ws)%nat -> wins_of E n (firstn (3 * n) ws ++ tail) = wins_of E n ws.
Proof.
  intros E n. induction n as [|n IH]; intros ws tail L; [reflexivity|].
  destruct ws as [|lo [|len [|kd ws']]]; cbn [length] in L; try lia.
  replace (3 * S n)%nat with (S (S (S (3 * n)))) by lia. cbn [firstn app]. rewrite !wins_of_cons, (IH ws' tail) by lia. reflexivity.
Qed.

Lemma wins_of_app1 : forall E n ws lo len kd tail, length ws = (3 * n)%nat ->
  wins_of E (S n) (ws ++ lo :: len :: kd :: tail) =
    wins_of E n ws ++ [Win (bv_unsigned (den E lo)) (bv_unsigned (den E len)) (bv_unsigned (den E kd))].
Proof.
  intros E n. induction n as [|n IH]; intros ws lo len kd tail L.
  - destruct ws; [reflexivity| cbn in L; lia].
  - destruct ws as [|a [|b [|c ws']]]; cbn [length] in L; try lia.
    cbn [app]. rewrite !wins_of_cons, (IH ws' lo len kd tail) by lia. reflexivity.
Qed.

Lemma skipn_app_exact : forall {T} (l1 l2 : list T) n, length l1 = n -> skipn n (l1 ++ l2) = l2.
Proof. intros T l1 l2 n <-. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.

Lemma wadd_one_small : forall nw, wt nw = false -> to_Z (wl nw) + 1 < two63 ->
  wt (wadd nw wone) = false /\ to_Z (wl (wadd nw wone)) = to_Z (wl nw) + 1.
Proof.
  intros nw T B.
  assert (E2 : w2Z (wadd nw wone) = w2Z nw + 1).
  { rewrite wadd_ok, (w2Z_nowt nw T). change (w2Z wone) with 1. unfold two64, two63 in *. rewrite Z.mod_small; [reflexivity|].
    pose proof (Uint63.to_Z_bounded (wl nw)). lia. }
  pose proof (w2Z_wt (wadd nw wone)) as WT. rewrite E2, (w2Z_nowt nw T) in WT.
  assert (T' : wt (wadd nw wone) = false) by (rewrite WT; apply Z.leb_gt; unfold two63 in *; lia).
  split; [exact T'|]. pose proof (w2Z_nowt _ T') as E3. rewrite E2, (w2Z_nowt nw T) in E3. lia.
Qed.

Lemma decode_add_window : forall E md A nw rest n lo len kd,
  wt nw = false -> n = Z.to_nat (to_Z (wl nw)) -> (3 * n <= length rest)%nat -> to_Z (wl nw) + 1 < two63 ->
  decode (map (den E) (VL md :: A :: VL (wadd nw wone) :: firstn (3 * n) rest ++ [lo; len; kd] ++ skipn (3 * n) rest)) =
    Some (w2Z md, den E A,
          wins_of E n rest ++ [Win (bv_unsigned (den E lo)) (bv_unsigned (den E len)) (bv_unsigned (den E kd))],
          map (den E) (skipn (3 * n) rest)).
Proof.
  intros E md A nw rest n lo len kd T N L B. cbn [app].
  destruct (wadd_one_small nw T B) as [T' E'].
  rewrite (decode_hargs E md A (wadd nw wone) _ (S n) T'); [| rewrite E', N; pose proof (Uint63.to_Z_bounded (wl nw)); lia |].
  2:{ rewrite app_length, firstn_length_le by lia. cbn [length]. rewrite skipn_length. lia. }
  f_equal. f_equal; [f_equal|].
  - rewrite (wins_of_app1 E n (firstn (3 * n) rest) lo len kd (skipn (3 * n) rest)); [| rewrite firstn_length_le; lia].
    rewrite <- (app_nil_r (firstn (3 * n) rest)) at 1. rewrite (wins_of_firstn E n rest []) by lia. reflexivity.
  - replace (3 * S n)%nat with (3 * n + 3)%nat by lia. rewrite skipn_app, firstn_length_le by lia.
    rewrite skipn_all2; [| rewrite firstn_length_le; lia]. replace (3 * n + 3 - 3 * n)%nat with 3%nat by lia. reflexivity.
Qed.

Fixpoint addn (n : int) (k : nat) : int :=
  match k with O => n | S k' => PrimInt63.add (addn n k') 1%uint63 end.

Lemma addn_Z : forall n k, to_Z n + Z.of_nat k < wB -> to_Z (addn n k) = to_Z n + Z.of_nat k.
Proof.
  intros n k. induction k as [|k IH]; intros B; cbn [addn]; [lia|].
  rewrite Uint63.add_spec, IH by lia. change (to_Z 1%uint63) with 1. rewrite Z.mod_small; [lia|].
  pose proof (Uint63.to_Z_bounded n). lia.
Qed.

Lemma add_Z : forall n (i : int), to_Z n + to_Z i < wB -> to_Z (PrimInt63.add n i) = to_Z n + to_Z i.
Proof.
  intros n i B. rewrite Uint63.add_spec, Z.mod_small; [lia|].
  pose proof (Uint63.to_Z_bounded n). pose proof (Uint63.to_Z_bounded i). lia.
Qed.

Definition env_above (E : env) (n : int) (F : Z -> word) (G : Z -> Z -> byte) : env :=
  Env (fun k => if to_Z k <? to_Z n then ev E k else F (to_Z k - to_Z n)) (eb E)
      (fun k => if to_Z k <? to_Z n then eg E k else G (to_Z k - to_Z n)).

Lemma env_above_ext : forall E n F G, env_ext n E (env_above E n F G).
Proof.
  intros E n F G. split; [reflexivity|]. intros k Hk. cbn [env_above ev eg].
  destruct (Z.ltb_spec (to_Z k) (to_Z n)); [auto| lia].
Qed.
Lemma ev_above : forall E n F G k, to_Z n <= to_Z k -> ev (env_above E n F G) k = F (to_Z k - to_Z n).
Proof. intros. cbn [env_above ev]. destruct (Z.ltb_spec (to_Z k) (to_Z n)); [lia| reflexivity]. Qed.
Lemma eg_above : forall E n F G k, to_Z n <= to_Z k -> eg (env_above E n F G) k = G (to_Z k - to_Z n).
Proof. intros. cbn [env_above eg]. destruct (Z.ltb_spec (to_Z k) (to_Z n)); [lia| reflexivity]. Qed.
Lemma ev_below : forall E n F G k, to_Z k < to_Z n -> ev (env_above E n F G) k = ev E k.
Proof. intros. cbn [env_above ev]. destruct (Z.ltb_spec (to_Z k) (to_Z n)); [reflexivity| lia]. Qed.
Lemma eb_above : forall E n F G, eb (env_above E n F G) = eb E.
Proof. reflexivity. Qed.

Lemma den_VP0_above : forall E n F G k, to_Z n <= to_Z (addn n k) -> to_Z n + Z.of_nat k < wB ->
  den (env_above E n F G) (VP (addn n k) wzero) = F (Z.of_nat k).
Proof.
  intros E n F G k Hn B. cbn [den]. rewrite (ev_above E n F G) by exact Hn. rewrite addn_Z by exact B.
  replace (to_Z n + Z.of_nat k - to_Z n) with (Z.of_nat k) by lia.
  apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, w2Z_wzero, Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Definition clob_pos (r : r5) : option nat :=
  match r with
  | X1 => Some 0 | X5 => Some 1 | X6 => Some 2 | X7 => Some 3 | X11 => Some 4 | X12 => Some 5 | X13 => Some 6 | X14 => Some 7
  | X15 => Some 8 | X16 => Some 9 | X17 => Some 10 | X28 => Some 11 | X29 => Some 12 | X30 => Some 13 | X31 => Some 14
  | _ => None
  end%nat.

Lemma getr_clobber : forall st r,
  getr (clobber st) r = match clob_pos r with Some i => VP (addn (s_next st) i) wzero | None => getr st r end.
Proof. intros [pc x ff rv R fs os pv nx] r. destruct r; reflexivity. Qed.

Lemma clobber_fields : forall st,
  s_pc (clobber st) = s_pc st /\ s_ff (clobber st) = s_ff st /\ s_resv (clobber st) = s_resv st /\ s_regs (clobber st) = s_regs st
  /\ s_facts (clobber st) = s_facts st /\ s_ops (clobber st) = s_ops st /\ s_priv (clobber st) = s_priv st
  /\ s_next (clobber st) = PrimInt63.add (s_next st) 15%uint63.
Proof. intros [pc x ff rv R fs os pv nx]. repeat split; reflexivity. Qed.

Lemma addn_lit : forall n k (i : int), to_Z i = Z.of_nat k -> to_Z n + Z.of_nat k < wB -> addn n k = PrimInt63.add n i.
Proof.
  intros n k i Hi B. apply Uint63.to_Z_inj. rewrite addn_Z by exact B. rewrite add_Z by lia. lia.
Qed.

Section Regions.
Variable segs : list Segment.

Definition claimed (E : env) (k : int) (r : region) (o : Z) : Prop :=
  (exists g gr c, IMap.find g (rg_cells r) = Some gr /\ In c (g_cells gr) /\ keyZ g = o / 8 /\ covers c (o mod 8))
  \/ (uncovered r o /\ bg_byte segs E k r o <> None).

Lemma region_ok_fine_frame : forall priv E m m' k r,
  ev E 0%uint63 = Z_to_bv 64 0 ->
  region_ok segs priv E m k r ->
  (forall o, (PrimInt63.eqb k 0%uint63 = false -> loZ r <= o < hiZ E r) ->
             (PrimInt63.eqb k 0%uint63 = true -> 0 <= o < two63 / 2 /\ (exists seg, find_segment segs o 1 = Some seg) /\ ~ in_priv priv o) ->
             claimed E k r o ->
             rb segs m' (bv_unsigned (ev E k) + o) = rb segs m (bv_unsigned (ev E k) + o)) ->
  (PrimInt63.eqb k 0%uint63 = false -> forall a, bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r ->
      rb segs m' a <> None /\ (rg_w r = true -> wb segs m' a = true)) ->
  region_ok segs priv E m' k r.
Proof.
  intros priv E m m' k r Hz RO FR VA.
  destruct RO as [Rbst Rrange Rvalid Rcells Rin Rbg].
  assert (HB0 : PrimInt63.eqb k 0%uint63 = true -> bv_unsigned (ev E k) = 0).
  { intros K. apply Uint63.eqb_correct in K. subst k. apply ev0_zero. exact Hz. }
  constructor.
  - exact Rbst.
  - exact Rrange.
  - intros K a Ha. destruct (VA K a Ha) as [V1 V2]. split; [exact V1|]. split; [exact V2|]. exact (proj2 (proj2 (Rvalid K a Ha))).
  - intros g gr Hf. destruct (Rcells g gr Hf) as [Ss Fc]. split; [exact Ss|].
    apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Fc c Hc) as (C1 & C2 & C3 & C4).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. intros i Hi.
    pose proof (Rin g gr c i Hf Hc Hi) as [P1 P2]. cbv zeta in P1, P2.
    transitivity (rb segs m (bv_unsigned (ev E k) + 8 * keyZ g + to_Z (c_idx c) + i)); [| apply C4; exact Hi].
    replace (bv_unsigned (ev E k) + 8 * keyZ g + to_Z (c_idx c) + i) with (bv_unsigned (ev E k) + (8 * keyZ g + to_Z (c_idx c) + i)) by lia.
    apply FR; [exact P1 | exact P2|].
    left. exists g, gr, c. split; [exact Hf|]. split; [exact Hc|]. split.
    + rewrite <- Z.add_assoc, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
    + unfold covers. rewrite <- Z.add_assoc, Z.add_comm, Z.mul_comm, Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
  - exact Rin.
  - intros o H1 H2 U. pose proof (Rbg o H1 H2 U) as G.
    destruct (bg_byte segs E k r o) as [b|] eqn:Hb; [|exact I].
    rewrite FR; [exact G| exact H1| |].
    + intros K. destruct (H2 K) as (Q1 & [bs Q2] & Q3). split; [exact Q1|]. split; [| exact Q3].
      eapply memory_read_find_segment; [| exact Q2]. rewrite half63 in Q1. unfold two64. lia.
    + right. split; [exact U|]. rewrite Hb. discriminate.
Qed.

Lemma dirty_range_spec : forall glo n cs, IMap.bst cs -> to_Z glo + Z.of_nat n < wB ->
  IMap.bst (Mem.dirty_range glo n cs)
  /\ forall g, IMap.find g (Mem.dirty_range glo n cs) =
        if (to_Z glo <=? to_Z g) && (to_Z g <? to_Z glo + Z.of_nat n) then Some (Gran true []) else IMap.find g cs.
Proof.
  intros glo n. revert glo. induction n as [|n IH]; intros glo cs B Hn; cbn [Mem.dirty_range].
  - split; [exact B|]. intros g. destruct (Z.leb_spec (to_Z glo) (to_Z g)), (Z.ltb_spec (to_Z g) (to_Z glo + Z.of_nat 0)); cbn; try reflexivity. lia.
  - assert (E1 : to_Z (PrimInt63.add glo 1%uint63) = to_Z glo + 1).
    { apply add_Z. change (to_Z 1%uint63) with 1. lia. }
    destruct (IH (PrimInt63.add glo 1%uint63) (IMap.add glo (Gran true []) cs) (IMap.bst_add _ _ _ B) ltac:(rewrite E1; lia)) as [B' F].
    split; [exact B'|]. intros g. rewrite F, E1.
    destruct (Uint63.eqb g glo) eqn:EQ.
    + apply Uint63.eqb_correct in EQ. subst g. rewrite IMap.find_add_same by exact B.
      destruct (Z.leb_spec (to_Z glo + 1) (to_Z glo)); [lia|]. cbn.
      destruct (Z.leb_spec (to_Z glo) (to_Z glo)); [|lia]. destruct (Z.ltb_spec (to_Z glo) (to_Z glo + Z.of_nat (S n))); [reflexivity| lia].
    + apply Uint63.eqb_false_spec in EQ. rewrite IMap.find_add_other; [| exact B| intros X; apply EQ; rewrite X; reflexivity].
      assert (to_Z g <> to_Z glo) by (intros X; apply EQ, Uint63.to_Z_inj; exact X).
      destruct (Z.leb_spec (to_Z glo + 1) (to_Z g)), (Z.leb_spec (to_Z glo) (to_Z g)),
               (Z.ltb_spec (to_Z g) (to_Z glo + 1 + Z.of_nat n)), (Z.ltb_spec (to_Z g) (to_Z glo + Z.of_nat (S n))); cbn; try reflexivity; lia.
Qed.

Lemma region_dirty_sound : forall priv E m k r glo n,
  to_Z glo + Z.of_nat n < wB ->
  region_ok segs priv E m k r ->
  region_ok segs priv E m k (Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r) (Mem.dirty_range glo n (rg_cells r))).
Proof.
  intros priv E m k r glo n Hn RO. destruct RO as [Rbst Rrange Rvalid Rcells Rin Rbg].
  destruct (dirty_range_spec glo n (rg_cells r) Rbst Hn) as [B' F].
  constructor; cbn [rg_cells rg_lo rg_hi rg_w rg_bg].
  - exact B'.
  - exact Rrange.
  - exact Rvalid.
  - intros g gr. rewrite F. destruct (_ && _); [intros X; injection X as <-; apply slot_ok_nil| apply Rcells].
  - intros g gr c i. rewrite F. destruct (_ && _); [intros X; injection X as <-; intros H; destruct H| apply Rin].
  - intros o H1 H2 U. unfold bg_byte. cbn [rg_bg]. fold (bg_byte segs E k r o). apply Rbg; [exact H1| exact H2|].
    intros g gr Hg Hf. unfold uncovered in U. cbn [rg_cells] in U. specialize (U g). rewrite F in U.
    destruct (_ && _); [destruct (U (Gran true []) Hg eq_refl) as [D _]; discriminate D| apply U; assumption].
Qed.

End Regions.

End CtrFX.
