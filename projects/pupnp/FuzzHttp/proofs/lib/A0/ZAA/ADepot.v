(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs.
Import ListNotations.
Open Scope Z_scope.

Notation DT := 1660888%Z.
Notation DNI := 5855192%Z.
Notation DM1 := 5855208%Z.
Notation SSA := 1595336%Z.
Notation SSD := 1595352%Z.

Definition M64 : Z := 2^64.
Notation MM_M := 14313749767032793493%Z.
Notation MM_M8 := 3829533694005038248%Z.
Notation MM_SEED := 10900877739976798860%Z.
Definition mm_add (v k : Z) : Z :=
  let k1 := (k * MM_M) mod M64 in
  let k2 := Z.lxor (Z.shiftr k1 47) k1 in
  let k3 := (k2 * MM_M) mod M64 in
  ((Z.lxor k3 v) * MM_M) mod M64.
Definition mm_init (n : Z) : Z := Z.lxor ((n * MM_M8) mod M64) MM_SEED.
Definition mm_fin (v : Z) : Z :=
  let v1 := (v * MM_M) mod M64 in
  let x := Z.lxor (Z.shiftr v1 47) v1 in let x2 := (x * MM_M) mod M64 in Z.lxor (Z.shiftr x2 47) x2.
Definition depot_hash (tr : list Z) : Z := mm_fin (fold_left mm_add tr (mm_init (Z.of_nat (length tr)))).

Lemma M64_eq : M64 = 2^64. Proof. reflexivity. Qed.
Lemma lxor_range : forall a b, 0 <= a < M64 -> 0 <= b < M64 -> 0 <= Z.lxor a b < M64.
Proof. rewrite M64_eq. intros. apply PropExec.Z_lxor_range; assumption. Qed.
Lemma shiftr_range : forall a k, 0 <= a < M64 -> 0 <= k -> 0 <= Z.shiftr a k < M64.
Proof. rewrite M64_eq. intros. apply PropExec.Z_shiftr_range; lia. Qed.
Lemma mod_range : forall a, 0 <= a mod M64 < M64. Proof. intros. rewrite M64_eq. apply Z.mod_pos_bound. lia. Qed.
Lemma mm_add_range : forall v k, 0 <= mm_add v k < M64. Proof. intros. unfold mm_add. apply mod_range. Qed.
Lemma mm_init_range : forall n, 0 <= mm_init n < M64.
Proof. intros. unfold mm_init. apply lxor_range; [apply mod_range| rewrite M64_eq; cbn; lia]. Qed.
Lemma mm_fin_range : forall v, 0 <= mm_fin v < M64.
Proof. intros. unfold mm_fin. apply lxor_range; [apply shiftr_range; [apply mod_range|lia] | apply mod_range]. Qed.
Lemma fold_mm_add_range : forall tr v, 0 <= v < M64 -> 0 <= fold_left mm_add tr v < M64.
Proof. induction tr as [|k tr IH]; intros v Hv; cbn; [exact Hv|]. apply IH. apply mm_add_range. Qed.
Lemma depot_hash_range : forall tr, 0 <= depot_hash tr < 2^64.
Proof. intros. unfold depot_hash. pose proof (mm_fin_range (fold_left mm_add tr (mm_init (Z.of_nat (length tr))))). rewrite M64_eq in H. lia. Qed.

Definition bkt (h : Z) : Z := h mod 2^20.
Lemma bkt_range : forall h, 0 <= bkt h < 2^20. Proof. intros. unfold bkt. apply Z.mod_pos_bound. lia. Qed.

Fixpoint head_from (hs : list Z) (i b cur : Z) : Z :=
  match hs with
  | [] => cur
  | h :: hs' => head_from hs' (i + 1) b (if bkt h =? b then i else cur)
  end.
Definition head_of (hs : list Z) (b : Z) : Z := head_from hs 1 b 0.
Definition zlen {X} (l : list X) : Z := Z.of_nat (length l).
Definition hnth (hs : list Z) (i : Z) : Z := nth (Z.to_nat (i - 1)) hs 0.
Definition lnk (hs : list Z) (i : Z) : Z := head_of (firstn (Z.to_nat (i - 1)) hs) (bkt (hnth hs i)).

Lemma head_from_app : forall l1 l2 i b cur, head_from (l1 ++ l2) i b cur = head_from l2 (i + zlen l1) b (head_from l1 i b cur).
Proof.
  induction l1 as [|h l1 IH]; intros; cbn -[Z.add]. { unfold zlen. cbn. rewrite Z.add_0_r. reflexivity. }
  rewrite IH. f_equal. unfold zlen. cbn [length]. lia.
Qed.
Lemma head_from_bound : forall hs i b cur, (cur = 0 \/ (1 <= cur < i)) -> 1 <= i ->
  head_from hs i b cur = 0 \/ 1 <= head_from hs i b cur < i + zlen hs.
Proof.
  induction hs as [|h hs IH]; intros i b cur Hc Hi; cbn -[Z.add].
  - unfold zlen; cbn. lia.
  - destruct (IH (i + 1) b (if bkt h =? b then i else cur)) as [E|E]; [destruct (bkt h =? b); lia| lia| left; exact E| right].
    unfold zlen in *. cbn [length]. lia.
Qed.
Lemma head_of_bound : forall hs b, head_of hs b = 0 \/ 1 <= head_of hs b <= zlen hs.
Proof. intros. unfold head_of. destruct (head_from_bound hs 1 b 0 ltac:(lia) ltac:(lia)); lia. Qed.
Lemma head_of_snoc : forall hs h b, head_of (hs ++ [h]) b = if bkt h =? b then zlen hs + 1 else head_of hs b.
Proof. intros. unfold head_of. rewrite head_from_app. cbn. destruct (bkt h =? b); [lia| reflexivity]. Qed.
Lemma head_of_nil : forall b, head_of [] b = 0. Proof. reflexivity. Qed.

Lemma head_from_bkt : forall hs i b cur s, (cur = 0 \/ 1 <= cur < i) -> 1 <= i ->
  head_from hs i b cur = s -> s <> 0 -> s = cur \/ (i <= s < i + zlen hs /\ bkt (nth (Z.to_nat (s - i)) hs 0) = b).
Proof.
  induction hs as [|h hs IH]; intros i b cur s Hc Hi Hs Hs0; cbn -[Z.add] in Hs.
  - left. congruence.
  - destruct (IH (i + 1) b (if bkt h =? b then i else cur) s ltac:(destruct (bkt h =? b); lia) ltac:(lia) Hs Hs0) as [E|[R E]].
    + destruct (bkt h =? b) eqn:EB; [| left; exact E]. right. rewrite E. replace (Z.to_nat (i - i)) with 0%nat by lia. cbn [nth].
      unfold zlen; cbn [length]. split; [lia|]. apply Z.eqb_eq. exact EB.
    + right. unfold zlen in *; cbn [length]. split; [lia|]. replace (Z.to_nat (s - i)) with (S (Z.to_nat (s - (i + 1)))) by lia. cbn [nth]. exact E.
Qed.
Lemma head_of_bkt : forall hs b, head_of hs b <> 0 -> bkt (hnth hs (head_of hs b)) = b.
Proof.
  intros hs b H. unfold head_of in *. destruct (head_from_bkt hs 1 b 0 _ ltac:(lia) ltac:(lia) eq_refl H) as [E|[R E]]; [congruence|].
  unfold hnth. exact E.
Qed.

Lemma firstn_firstn_le : forall {X} (l : list X) a b, (a <= b)%nat -> firstn a (firstn b l) = firstn a l.
Proof. intros. rewrite firstn_firstn. f_equal. lia. Qed.
Lemma head_of_prefix : forall hs k b, (k <= length hs)%nat ->
  let s := head_of (firstn k hs) b in s <> 0 -> 1 <= s <= Z.of_nat k /\ lnk hs s = head_of (firstn (Z.to_nat (s - 1)) hs) b /\ hnth (firstn k hs) s = hnth hs s.
Proof.
  intros hs k b Hk s Hs.
  pose proof (head_of_bound (firstn k hs) b) as B. unfold zlen in B. rewrite firstn_length_le in B by lia.
  assert (R : 1 <= s <= Z.of_nat k) by (subst s; lia). split; [exact R|].
  assert (HN : hnth (firstn k hs) s = hnth hs s).
  { unfold hnth. rewrite <- (firstn_skipn k hs) at 2. rewrite app_nth1 by (rewrite firstn_length_le; lia). reflexivity. }
  split; [| exact HN].
  unfold lnk. rewrite <- HN. pose proof (head_of_bkt (firstn k hs) b Hs) as E. fold s in E. rewrite E. reflexivity.
Qed.

Fixpoint find_fuel (fuel : nat) (hs : list Z) (k : nat) (b h : Z) : Z :=
  match fuel with
  | O => 0
  | S f => let s := head_of (firstn k hs) b in
           if s =? 0 then 0 else if hnth hs s =? h then s else find_fuel f hs (Z.to_nat (s - 1)) b h
  end.
Definition dfind (hs : list Z) (h : Z) : Z := find_fuel (S (length hs)) hs (length hs) (bkt h) h.

Lemma find_fuel_bound : forall fuel hs k b h, (k <= length hs)%nat ->
  find_fuel fuel hs k b h = 0 \/ (1 <= find_fuel fuel hs k b h <= Z.of_nat k /\ hnth hs (find_fuel fuel hs k b h) = h).
Proof.
  induction fuel as [|f IH]; intros hs k b h Hk; cbn -[Z.sub]; [lia|].
  destruct (head_of (firstn k hs) b =? 0) eqn:E0; [lia|]. apply Z.eqb_neq in E0.
  destruct (head_of_prefix hs k b Hk E0) as (R & _ & _).
  destruct (hnth hs (head_of (firstn k hs) b) =? h) eqn:E1.
  - right. split; [lia|]. apply Z.eqb_eq. exact E1.
  - destruct (IH hs (Z.to_nat (head_of (firstn k hs) b - 1)) b h ltac:(lia)) as [E|[R2 E]]; [lia|]. right. split; [lia| exact E].
Qed.
Lemma dfind_bound : forall hs h, dfind hs h = 0 \/ (1 <= dfind hs h <= zlen hs /\ hnth hs (dfind hs h) = h).
Proof. intros. unfold dfind, zlen. apply find_fuel_bound. lia. Qed.

Lemma head_from_ge_cur : forall hs i b cur, 0 <= cur -> cur < i -> cur <= head_from hs i b cur.
Proof.
  induction hs as [|x hs IH]; intros i b cur H1 H2; cbn -[Z.add]; [lia|].
  destruct (bkt x =? b); (eapply Z.le_trans; [| apply IH; lia]); lia.
Qed.
Lemma head_of_ge : forall hs b j, (j < length hs)%nat -> bkt (nth j hs 0) = b -> Z.of_nat j + 1 <= head_of hs b.
Proof.
  intros hs b j Hj Hb. unfold head_of. rewrite <- (firstn_skipn j hs). rewrite head_from_app.
  destruct (skipn j hs) as [|x tl] eqn:ES. { exfalso. apply (f_equal (@length Z)) in ES. rewrite skipn_length in ES. cbn in ES. lia. }
  assert (X : x = nth j hs 0). { rewrite <- (firstn_skipn j hs). rewrite app_nth2 by (rewrite firstn_length_le; lia). rewrite firstn_length_le by lia. rewrite Nat.sub_diag, ES. reflexivity. }
  cbn -[Z.add]. rewrite X, Hb, Z.eqb_refl. unfold zlen. rewrite firstn_length_le by lia.
  pose proof (head_from_bound (firstn j hs) 1 b 0 ltac:(lia) ltac:(lia)) as B0. unfold zlen in B0. rewrite firstn_length_le in B0 by lia.
  eapply Z.le_trans; [| apply head_from_ge_cur; lia]. lia.
Qed.
Lemma find_fuel_complete : forall fuel hs k b h j, (k <= length hs)%nat -> (j < k)%nat -> (k <= fuel)%nat ->
  nth j hs 0 = h -> bkt h = b -> find_fuel fuel hs k b h <> 0.
Proof.
  induction fuel as [|f IH]; intros hs k b h j Hk Hj Hf Hn Hb; [lia|]. cbn -[Z.sub].
  pose proof (head_of_ge (firstn k hs) b j ltac:(rewrite firstn_length_le; lia)) as G.
  rewrite nth_firstn in G. destruct (Nat.ltb_spec j k); [|lia].
  specialize (G ltac:(rewrite Hn; exact Hb)).
  destruct (head_of (firstn k hs) b =? 0) eqn:E0. { apply Z.eqb_eq in E0. lia. }
  apply Z.eqb_neq in E0. destruct (head_of_prefix hs k b Hk E0) as (R & _ & HN).
  destruct (hnth hs (head_of (firstn k hs) b) =? h) eqn:E1; [lia|]. apply Z.eqb_neq in E1.

  assert (NE : head_of (firstn k hs) b <> Z.of_nat j + 1). { intros E. apply E1. rewrite E. unfold hnth. replace (Z.to_nat (Z.of_nat j + 1 - 1)) with j by lia. exact Hn. }
  apply (IH hs _ b h j); try lia; assumption.
Qed.
Lemma dfind_complete : forall hs h, In h hs -> dfind hs h <> 0.
Proof.
  intros hs h HIn. destruct (In_nth hs h 0 HIn) as (j & Hj & Hn). unfold dfind.
  apply (find_fuel_complete _ hs (length hs) (bkt h) h j); [lia| lia| lia| exact Hn| reflexivity].
Qed.

Record dlayout := mkDL { DN0 : Z; SS0 : Z; SWIN : Z }.

Section R.
Context {HC : HasCeiling}.
Variable L : dlayout.

Definition dl_ok : Prop :=
  (((0x609000 <= DN0 L /\ DN0 L + 2^20 <= 0x7fff7000) \/ 0x10007fff8000 <= DN0 L) /\ 0x10007fff8000 <= alloc_ceiling) /\ DN0 L + 2^20 <= alloc_ceiling /\ DN0 L mod 4096 = 0 /\
  (((0x609000 <= SS0 L /\ SS0 L + SWIN L <= 0x7fff7000) \/ 0x10007fff8000 <= SS0 L) /\ 0x10007fff8000 <= alloc_ceiling) /\ SS0 L + SWIN L <= alloc_ceiling /\ SS0 L mod 4096 = 0 /\
  0 <= SWIN L /\ SWIN L mod 8 = 0 /\
  (DN0 L + 2^20 <= SS0 L \/ SS0 L + SWIN L <= DN0 L).

Definition tabrep (m : mem) (hs : list Z) : Prop :=
  forall b, 0 <= b < 2^20 -> rw_cells asegs m (DT + 4 * b) [C4 (wz (head_of hs b))].

Definition tabrep_x (m : mem) (hs : list Z) (bx : Z) : Prop :=
  forall b, 0 <= b < 2^20 -> b <> bx -> rw_cells asegs m (DT + 4 * b) [C4 (wz (head_of hs b))].
Definition nodesrep (m : mem) (hs : list Z) : Prop :=
  forall i, 1 <= i <= zlen hs -> exists sid : word, rw_cells asegs m (DN0 L + 16 * i) [C8 (wz (hnth hs i)); C4 (wz (lnk hs i)); C4 sid].

Definition RDEPOT (hs : list Z) (total : Z) (m : mem) : Prop :=
  tabrep m hs
  /\ rw_cells asegs m DNI [C4 (wz (zlen hs))]
  /\ rw_cells asegs m DM1 [C8 (wz (DN0 L))]
  /\ nodesrep m hs
  /\ (exists junk, rw_cells asegs m (DN0 L + 16 * (zlen hs + 1)) [CB (Z.to_nat (2^20 - 16 * (zlen hs + 1))) junk])
  /\ rw_cells asegs m SSA [C8 (wz total)]
  /\ rw_cells asegs m SSD [C8 (wz (SS0 L)); C4 (wz total)]
  /\ (exists junk, rw_cells asegs m (SS0 L + 8 * total) [CB (Z.to_nat (SWIN L - 8 * total)) junk])
  /\ Forall (fun h => 0 <= h < 2^64) hs /\ 0 <= total /\ 8 * total <= SWIN L /\ 16 * (zlen hs + 1) <= 2^20.

#[using="Type"] Lemma tabrep_split : forall m hs bx, tabrep m hs -> 0 <= bx < 2^20 ->
  rw_cells asegs m (DT + 4 * bx) [C4 (wz (head_of hs bx))] /\ tabrep_x m hs bx.
Proof. intros m hs bx T Hb. split; [apply T; exact Hb|]. intros b H1 H2. apply T. exact H1. Qed.
#[using="Type"] Lemma tabrep_join : forall m hs hs' bx v, tabrep_x m hs bx -> 0 <= bx < 2^20 ->
  rw_cells asegs m (DT + 4 * bx) [C4 (wz v)] -> (forall b, 0 <= b < 2^20 -> head_of hs' b = (if b =? bx then v else head_of hs b)) ->
  tabrep m hs'.
Proof.
  intros m hs hs' bx v TX Hb C E b Hb'. rewrite (E b Hb'). destruct (b =? bx) eqn:EB.
  - apply Z.eqb_eq in EB. subst b. exact C.
  - apply Z.eqb_neq in EB. apply TX; assumption.
Qed.

#[using="Type"] Lemma tabrep_x_transport : forall m m' hs bx W, tabrep_x m hs bx -> munch W m m' -> wmono asegs m m' ->
  (forall b, 0 <= b < 2^20 -> b <> bx -> disjoint_from W (DT + 4 * b) 4) -> tabrep_x m' hs bx.
Proof. intros m m' hs bx W TX MU WM D b H1 H2. eapply rw_cells_transport; [apply TX; assumption| exact MU| exact WM| apply D; assumption]. Qed.
#[using="Type"] Lemma tabrep_transport : forall m m' hs W, tabrep m hs -> munch W m m' -> wmono asegs m m' ->
  (forall b, 0 <= b < 2^20 -> disjoint_from W (DT + 4 * b) 4) -> tabrep m' hs.
Proof. intros m m' hs W T MU WM D b H1. eapply rw_cells_transport; [apply T; assumption| exact MU| exact WM| apply D; assumption]. Qed.

#[using="Type"] Lemma tabrep_x_frame : forall m hs bx a bs, tabrep_x m hs bx -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall b, 0 <= b < 2^20 -> b <> bx -> DT + 4 * b + 4 <= a \/ a + Z.of_nat (length bs) <= DT + 4 * b) ->
  tabrep_x (write_to_mem m (wa a) bs) hs bx.
Proof. intros m hs bx a bs TX H0 H1 D b Hb Hx. apply rw_cells_frame; [apply TX; assumption| exact H0| exact H1|]. cbn [cells_size csize Nat.add]. destruct (D b Hb Hx); lia. Qed.
#[using="Type"] Lemma nodesrep_transport : forall m m' hs W, nodesrep m hs -> munch W m m' -> wmono asegs m m' ->
  (forall i, 1 <= i <= zlen hs -> disjoint_from W (DN0 L + 16 * i) 16) -> nodesrep m' hs.
Proof.
  intros m m' hs W NR MU WM D i Hi. destruct (NR i Hi) as [sid C]. exists sid.
  eapply rw_cells_transport; [exact C| exact MU| exact WM| apply D; exact Hi].
Qed.
#[using="Type"] Lemma nodesrep_frame : forall m hs a bs, nodesrep m hs -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall i, 1 <= i <= zlen hs -> DN0 L + 16 * i + 16 <= a \/ a + Z.of_nat (length bs) <= DN0 L + 16 * i) ->
  nodesrep (write_to_mem m (wa a) bs) hs.
Proof.
  intros m hs a bs NR H0 H1 D i Hi. destruct (NR i Hi) as [sid C]. exists sid.
  apply rw_cells_frame; [exact C| exact H0| exact H1|]. cbn [cells_size csize Nat.add]. destruct (D i Hi); lia.
Qed.

#[using="Type"] Lemma hnth_snoc_old : forall hs h i, 1 <= i <= zlen hs -> hnth (hs ++ [h]) i = hnth hs i.
Proof. intros. unfold hnth, zlen in *. rewrite app_nth1 by lia. reflexivity. Qed.
#[using="Type"] Lemma hnth_snoc_new : forall hs h, hnth (hs ++ [h]) (zlen hs + 1) = h.
Proof. intros. unfold hnth, zlen. rewrite app_nth2 by lia. replace (Z.to_nat _ - length hs)%nat with 0%nat by lia. reflexivity. Qed.
#[using="Type"] Lemma lnk_snoc_old : forall hs h i, 1 <= i <= zlen hs -> lnk (hs ++ [h]) i = lnk hs i.
Proof. intros. unfold lnk. rewrite hnth_snoc_old by assumption. unfold zlen in *. rewrite firstn_app. replace (Z.to_nat (i - 1) - length hs)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity. Qed.
#[using="Type"] Lemma lnk_snoc_new : forall hs h, lnk (hs ++ [h]) (zlen hs + 1) = head_of hs (bkt h).
Proof. intros. unfold lnk. rewrite hnth_snoc_new. unfold zlen. rewrite firstn_app. replace (Z.to_nat (Z.of_nat (length hs) + 1 - 1) - length hs)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r, firstn_all2 by lia. reflexivity. Qed.
#[using="Type"] Lemma zlen_snoc : forall {X} (l : list X) x, zlen (l ++ [x]) = zlen l + 1.
Proof. intros. unfold zlen. rewrite length_app. cbn. lia. Qed.
#[using="Type"] Lemma nodesrep_snoc : forall m hs h sid, nodesrep m hs ->
  rw_cells asegs m (DN0 L + 16 * (zlen hs + 1)) [C8 (wz h); C4 (wz (head_of hs (bkt h))); C4 sid] ->
  nodesrep m (hs ++ [h]).
Proof.
  intros m hs h sid NR C i Hi. rewrite zlen_snoc in Hi.
  destruct (Z.eq_dec i (zlen hs + 1)) as [->|NE].
  - exists sid. rewrite hnth_snoc_new, lnk_snoc_new. exact C.
  - destruct (NR i ltac:(lia)) as [sid' C']. exists sid'. rewrite hnth_snoc_old, lnk_snoc_old by lia. exact C'.
Qed.

Definition depot_apart (W : list ivl) : Prop :=
  Forall (fun iv => (DM1 + 8 <= fst iv \/ snd iv <= SSA) /\ (DN0 L + 2^20 <= fst iv \/ snd iv <= DN0 L) /\ (SS0 L + SWIN L <= fst iv \/ snd iv <= SS0 L)) W.
#[using="Type"] Lemma depot_apart_disjoint : forall W A n, depot_apart W ->
  ((SSA <= A /\ A + n <= DM1 + 8) \/ (DN0 L <= A /\ A + n <= DN0 L + 2^20) \/ (SS0 L <= A /\ A + n <= SS0 L + SWIN L)) ->
  disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros A n HW HA; cbn; [exact I|].
  inversion HW as [|x l H1 H2]; subst. cbn in H1. split; [lia| apply IH; assumption].
Qed.
#[using="Type"] Lemma RDEPOT_frame : forall hs total m m' W, RDEPOT hs total m -> munch W m m' -> wmono asegs m m' -> depot_apart W ->
  RDEPOT hs total m'.
Proof.
  unfold RDEPOT. intros hs total m m' W (T & NI & M1 & NR & FS & SA & SD & FF & B) MU WM AP.
  destruct FS as [j1 FS]. destruct FF as [j2 FF]. pose proof B as B'. destruct B' as (RG & T0 & TS & NB). unfold zlen in *.
  assert (D : forall A n, ((SSA <= A /\ A + n <= DM1 + 8) \/ (DN0 L <= A /\ A + n <= DN0 L + 2^20) \/ (SS0 L <= A /\ A + n <= SS0 L + SWIN L)) -> disjoint_from W A n).
  { intros. apply depot_apart_disjoint; assumption. }
  pose proof (head_of_bound hs) as HB. unfold zlen in HB.
  split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
  - eapply tabrep_transport; [exact T| exact MU| exact WM|]. intros b Hb. apply D. left. lia.
  - eapply rw_cells_transport; [exact NI| exact MU| exact WM|]. apply D. left. cbn. lia.
  - eapply rw_cells_transport; [exact M1| exact MU| exact WM|]. apply D. left. cbn. lia.
  - eapply nodesrep_transport; [exact NR| exact MU| exact WM|]. intros i Hi. unfold zlen in Hi. apply D. right; left. lia.
  - exists j1. eapply rw_cells_transport; [exact FS| exact MU| exact WM|]. apply D. right; left. cbn [cells_size csize].
    rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
  - eapply rw_cells_transport; [exact SA| exact MU| exact WM|]. apply D. left. cbn. lia.
  - eapply rw_cells_transport; [exact SD| exact MU| exact WM|]. apply D. left. cbn. lia.
  - exists j2. eapply rw_cells_transport; [exact FF| exact MU| exact WM|]. apply D. right; right. cbn [cells_size csize].
    rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
  - exact B.
Qed.

#[using="Type"] Lemma tab_read : forall m hs b, tabrep m hs -> 0 <= b < 2^20 ->
  ov_read_bytes asegs m (wa (DT + 4 * b)) 4 = Some (le4 (wz (head_of hs b))).
Proof.
  intros m hs b T Hb. pose proof (T b Hb) as C.
  replace (wa (DT + 4 * b)) with (wa (DT + 4 * b + Z.of_nat 0)) by (f_equal; lia).
  exact (rw_cells_read asegs m _ _ 0 (C4 (wz (head_of hs b))) C eq_refl).
Qed.
End R.
