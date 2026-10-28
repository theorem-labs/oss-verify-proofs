(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel AtpModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition ATP_SPLITINTO : Z := 0x3c550.
Definition ATP_SPLIT : Z := 0x3e244.
Definition ATP_FIND : Z := 0x3e34c.
Definition ATP_PUSH1 : Z := 0x3e4c4.
Definition ATP_PUSH2 : Z := 0x3e8c4.
Definition ATP_SBDTOR : Z := 0x3e784.
Definition ATP_ALLOCATE : Z := 0x3e7ec.
Definition ATP_MOVEASSIGN : Z := 0x3e9fc.
Definition ATP_OPNEW : Z := 0xd56e4.
Definition ATP_SEP : Z := 0x1264d.
Definition ATP_GROW : Z := 0x3e5fc.
Definition ATP_RELOC : Z := 0x3e6a4.
Definition ATP_EMPL : Z := 0x3c628.
Definition ATP_VDTOR : Z := 0x40d54.
Definition ATP_SUBSTR : Z := 0x3e478.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Fixpoint velts (els : list (Z * Z)) : list cell :=
  match els with [] => [] | e :: r => C8 (Z_to_bv 64 (fst e)) :: C8 (Z_to_bv 64 (snd e)) :: velts r end.

Lemma velts_app : forall a b, velts (a ++ b) = velts a ++ velts b.
Proof. induction a as [|e a IH]; intros b; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma velts_size : forall els, cells_size (velts els) = (16 * length els)%nat.
Proof. induction els as [|e r IH]; cbn -[Nat.mul]; [reflexivity|]. rewrite IH. lia. Qed.
Lemma velts_wf : forall els, cells_wf (velts els).
Proof. induction els as [|e r IH]; cbn; [exact I|]. repeat split; try exact I. exact IH. Qed.
Lemma velts_bytes_length : forall els, length (cells_bytes (velts els)) = (16 * length els)%nat.
Proof. intros. rewrite cells_bytes_length by apply velts_wf. apply velts_size. Qed.

Definition vblocks (blk : option bptr) (A cap : Z) : list block :=
  match blk with Some b => [(b, A, 16 * cap)] | None => [] end.

Definition vblk (m : mem) (A cap size : Z) (blk : option bptr) (els : list (Z * Z)) (jr : list byte) : Prop :=
  match blk with
  | None => A = 0 /\ cap = 0
  | Some _ => rw_cells usegs m A (velts els) /\ rw_cells usegs m (A + 16 * size) [CB (Z.to_nat (16 * (cap - size))) jr]
              /\ rblock_range A (16 * cap) /\ 1 <= cap
  end.

Definition vrep (m : mem) (V A : Z) (v : @vec bptr) (els : list (Z * Z)) (jr : list byte) : Prop :=
  let '(cs, blk) := v in let '(cap, size) := cs in
  size = zlength els /\ 0 <= size <= cap /\
  rw_cells usegs m V [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * size)); C8 (Z_to_bv 64 (A + 16 * cap))] /\
  vblk m A cap size blk els jr.

Lemma vrep_struct : forall m V A cap size blk els jr, vrep m V A (cap, size, blk) els jr ->
  rw_cells usegs m V [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * size)); C8 (Z_to_bv 64 (A + 16 * cap))].
Proof. intros m V A cap size blk els jr H. exact (proj1 (proj2 (proj2 H))). Qed.

Lemma vblk_agree : forall P m m' A cap size blk els jr,
  agree_on P m m' -> (forall a, blk <> None -> A <= a < A + 16 * cap -> P a) -> size = zlength els -> 0 <= size <= cap ->
  vblk m A cap size blk els jr -> vblk m' A cap size blk els jr.
Proof.
  intros P m m' A cap size blk els jr AG HA E R B.
  destruct blk as [b|]; [| exact B]. destruct B as (BE & BJ & BR & C1). split; [| split; [| split; [exact BR| exact C1]]].
  - eapply rw_cells_agree; [exact AG| exact BE|]. intros a Ha. rewrite velts_size in Ha. apply HA; [discriminate|]. unfold zlength in E. lia.
  - eapply rw_cells_agree; [exact AG| exact BJ|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply HA; [discriminate|]. lia.
Qed.

Lemma vrep_agree : forall P m m' V A cap size blk els jr,
  agree_on P m m' -> (forall a, V <= a < V + 24 -> P a) -> (forall a, blk <> None -> A <= a < A + 16 * cap -> P a) ->
  vrep m V A (cap, size, blk) els jr -> vrep m' V A (cap, size, blk) els jr.
Proof.
  intros P m m' V A cap size blk els jr AG HV HA (E & R & SV & B). split; [exact E|]. split; [exact R|]. split.
  - eapply rw_cells_agree; [exact AG| exact SV|]. intros a Ha. cbn in Ha. apply HV. lia.
  - eapply vblk_agree; [exact AG| exact HA| exact E| exact R| exact B].
Qed.

Fixpoint poffs_go (fuel : nat) (o : nat) (all : list Z) : list (nat * nat) :=
  match fuel with
  | O => [(o, length all)]
  | S f => match find_sep all with
           | None => [(o, length all)]
           | Some pos => (o, pos) :: poffs_go f (o + pos + 4)%nat (skipn (pos + 4) all)
           end
  end.
Definition poffs (d : list Z) : list (nat * nat) := match d with [] => [] | _ => poffs_go (S (length d)) 0 d end.

Lemma poffs_go_parts : forall fuel o all d, skipn o d = all ->
  map (fun e => firstn (snd e) (skipn (fst e) d)) (poffs_go fuel o all) = split_go fuel all.
Proof.
  induction fuel as [|f IH]; intros o all d Ho; cbn.
  - rewrite Ho. rewrite firstn_all. reflexivity.
  - destruct (find_sep all) as [pos|] eqn:E.
    + cbn [map fst snd]. rewrite Ho. f_equal. apply IH. rewrite <- Ho. rewrite skipn_skipn. f_equal. lia.
    + cbn [map fst snd]. rewrite Ho, firstn_all. reflexivity.
Qed.
Lemma poffs_parts : forall d, map (fun e => firstn (snd e) (skipn (fst e) d)) (poffs d) = atp_parts d.
Proof. intros [|c d]; [reflexivity|]. unfold poffs, atp_parts. apply poffs_go_parts. reflexivity. Qed.
Lemma poffs_length : forall d, length (poffs d) = length (atp_parts d).
Proof. intros d. rewrite <- poffs_parts, length_map. reflexivity. Qed.

Lemma poffs_go_bound : forall fuel o all e, In e (poffs_go fuel o all) -> (o <= fst e /\ fst e + snd e <= o + length all)%nat.
Proof.
  induction fuel as [|f IH]; intros o all e H; cbn in H.
  - destruct H as [<-|[]]. cbn. lia.
  - destruct (find_sep all) as [pos|] eqn:E.
    + pose proof (find_sep_spec _ _ E) as HP. destruct H as [<-|H]; [cbn; lia|].
      apply IH in H. rewrite length_skipn in H. lia.
    + destruct H as [<-|[]]. cbn. lia.
Qed.
Lemma poffs_bound : forall d e, In e (poffs d) -> (fst e + snd e <= length d)%nat.
Proof. intros [|c d] e H; [destruct H|]. unfold poffs in H. apply poffs_go_bound in H. cbn in H |- *. lia. Qed.

Definition pview (D : Z) (e : nat * nat) : Z * Z := (D + Z.of_nat (fst e), Z.of_nat (snd e)).

Definition poffs_of (o : nat) (all : list Z) : list (nat * nat) := poffs_go (S (length all)) o all.

Lemma poffs_go_enough : forall f g o all, (length all < 4 * f)%nat -> (length all < 4 * g)%nat -> poffs_go f o all = poffs_go g o all.
Proof.
  induction f as [|f IH]; intros g o all Hf Hg; [lia|]. destruct g as [|g]; [lia|]. cbn.
  destruct (find_sep all) as [pos|] eqn:E; [|reflexivity]. f_equal.
  pose proof (find_sep_spec _ _ E). apply IH; rewrite length_skipn; lia.
Qed.

Lemma poffs_of_unfold : forall o all,
  poffs_of o all = match find_sep all with
                   | None => [(o, length all)]
                   | Some pos => (o, pos) :: poffs_of (o + pos + 4)%nat (skipn (pos + 4) all)
                   end.
Proof.
  intros o all. unfold poffs_of at 1. cbn [poffs_go]. destruct (find_sep all) as [pos|] eqn:E; [|reflexivity]. f_equal.
  unfold poffs_of. pose proof (find_sep_spec _ _ E). apply poffs_go_enough; rewrite ?length_skipn; lia.
Qed.

Lemma poffs_eq : forall d, poffs d = match d with [] => [] | _ => poffs_of 0 d end.
Proof. intros [|c d]; reflexivity. Qed.

Lemma poffs_of_length : forall o all, length (poffs_of o all) = length (parts_of all).
Proof.
  intros o all. remember (length all) as n eqn:En. revert o all En.
  induction n as [n IHn] using (well_founded_induction Wf_nat.lt_wf); intros o all En.
  rewrite poffs_of_unfold, parts_of_unfold. destruct (find_sep all) as [pos|] eqn:E; [|reflexivity]. cbn [length]. f_equal.
  pose proof (find_sep_spec _ _ E). apply (IHn (length (skipn (pos + 4) all))); [| reflexivity]. rewrite length_skipn. lia.
Qed.

Lemma poffs_of_nonnil : forall o all, poffs_of o all <> [].
Proof. intros o all. rewrite poffs_of_unfold. destruct (find_sep all); discriminate. Qed.

Lemma poffs_of_bound : forall o all e, In e (poffs_of o all) -> (o <= fst e /\ fst e + snd e <= o + length all)%nat.
Proof. intros o all e H. unfold poffs_of in H. apply poffs_go_bound in H. exact H. Qed.

Lemma rw_cells_CB_split2 : forall m A (n1 n2 : nat) (bs : list byte), rw_cells usegs m A [CB (n1 + n2) bs] ->
  rw_cells usegs m A [CB n1 (firstn n1 bs)] /\ rw_cells usegs m (A + Z.of_nat n1) [CB n2 (skipn n1 bs)].
Proof.
  intros m A n1 n2 bs H.
  assert (L : length bs = (n1 + n2)%nat) by (destruct H as [[[HL _] _] _]; exact HL).
  assert (H2 : rw_cells usegs m A ([CB n1 (firstn n1 bs)] ++ [CB n2 (skipn n1 bs)])).
  { eapply rw_cells_recast; [exact H| | |].
    - cbn. rewrite firstn_length, skipn_length. repeat split; lia.
    - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. apply firstn_skipn.
    - cbn. lia. }
  apply (proj1 (Sj_stage1_kit.rw_cells_app usegs m A _ _)) in H2. cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

Lemma rw_cells_join : forall m A cs1 A' cs2, rw_cells usegs m A cs1 -> rw_cells usegs m A' cs2 -> A' = A + Z.of_nat (cells_size cs1) ->
  rw_cells usegs m A (cs1 ++ cs2).
Proof. intros m A cs1 A' cs2 H1 H2 ->. apply Sj_stage1_kit.rw_cells_app. split; assumption. Qed.

End WithCeiling0.
