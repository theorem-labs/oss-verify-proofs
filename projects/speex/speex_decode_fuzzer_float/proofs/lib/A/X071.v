(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition lupd (l : list byte) (k : nat) (b : byte) : list byte := firstn k l ++ b :: skipn (S k) l.
Lemma lupd_length : forall l k b, (k < length l)%nat -> length (lupd l k b) = length l.
Proof. intros l k b H. unfold lupd. rewrite length_app, firstn_length_le by lia. cbn [length]. rewrite length_skipn. lia. Qed.
Lemma rw_cells_CB_store : forall segs (m : word -> option byte) A n cs (k : Z) bs,
rw_cells segs m A [CB n cs] -> 0 <= k -> (Z.to_nat k + length bs <= n)%nat ->
rw_cells segs (write_to_mem m (wa (A + k)) bs) A [CB n (upd_bytes cs (Z.to_nat k) bs)].
Proof.
intros segs m A n cs k bs [[Hwf Hb] Hw] K0 KN. cbn [cells_wf cell_wf cells_bytes cbytes] in Hwf, Hb. destruct Hwf as (Hl & _).
rewrite app_nil_r in Hb. split; [split|].
- cbn [cells_wf cell_wf]. rewrite upd_bytes_length by lia. split; [exact Hl| exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_write_inside; [exact Hb| exact K0| lia].
- cbn [cells_size csize] in *. apply wr_at_write. exact Hw.
Qed.
Lemma mem_inv_CB_store : forall segs (m : word -> option byte) A n cs (k : Z) (b : byte),
rw_cells segs m A [CB n cs] -> 0 <= k -> (Z.to_nat k + 1 <= n)%nat -> mem_inv segs m ->
mem_inv segs (write_to_mem m (wa (A + k)) [b]).
Proof.
intros segs m A n cs k b H K0 KN MI. change [b] with (cbytes (C1 b)).
apply (mem_inv_store_cbytes segs m (wa (A + k)) (C1 b) MI I).
destruct H as [_ Hw]. cbn [cells_size csize] in Hw. cbn [csize].
apply (wr_at_store_ok segs m A (Z.of_nat (n + 0)) k 1 Hw K0). lia.
Qed.
Lemma rw_cells_CB_store_nat : forall segs (m : word -> option byte) A n cs (kn : nat) bs,
rw_cells segs m A [CB n cs] -> (kn + length bs <= n)%nat ->
rw_cells segs (write_to_mem m (wa (A + Z.of_nat kn)) bs) A [CB n (upd_bytes cs kn bs)].
Proof. intros segs m A n cs kn bs H K. rewrite <- (Nat2Z.id kn) at 2. apply rw_cells_CB_store; [exact H| lia| rewrite Nat2Z.id; exact K]. Qed.
Lemma mem_inv_CB_store_nat : forall segs (m : word -> option byte) A n cs (kn : nat) (b : byte),
rw_cells segs m A [CB n cs] -> (kn + 1 <= n)%nat -> mem_inv segs m ->
mem_inv segs (write_to_mem m (wa (A + Z.of_nat kn)) [b]).
Proof. intros segs m A n cs kn b H K MI. apply (mem_inv_CB_store segs m A n cs (Z.of_nat kn) b H); [lia| rewrite Nat2Z.id; exact K| exact MI]. Qed.

Lemma mem_inv_CB_store_nat' : forall segs (m : word -> option byte) A n cs (kn : nat) bs,
rw_cells segs m A [CB n cs] -> (kn + length bs <= n)%nat -> mem_inv segs m ->
mem_inv segs (write_to_mem m (wa (A + Z.of_nat kn)) bs).
Proof.
intros segs m A n cs kn bs H K MI. change bs with (cbytes (CB (length bs) bs)).
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) (CB (length bs) bs) MI eq_refl).
destruct H as [_ Hw]. cbn [cells_size csize] in Hw. cbn [csize].
apply (wr_at_store_ok segs m A (Z.of_nat (n + 0)) (Z.of_nat kn) (length bs) Hw); lia.
Qed.

Fixpoint zruns (l : list (Z * nat)) : list Z := match l with [] => [] | (v, n) :: l' => repeat v n ++ zruns l' end.

Definition upd1 (l : list byte) (w : nat * list byte) : list byte := upd_bytes l (fst w) (snd w).
Definition upd_all (l : list byte) (ws : list (nat * list byte)) : list byte := fold_left upd1 ws l.
Definition wcovers (ws : list (nat * list byte)) (i : nat) : bool := existsb (fun w => (fst w <=? i)%nat && (i <? fst w + length (snd w))%nat) ws.
Definition wbounds (ws : list (nat * list byte)) (n : nat) : Prop := Forall (fun w => (fst w + length (snd w) <= n)%nat) ws.

Lemma nth_upd_bytes : forall (l : list byte) k bs i d, (k + length bs <= length l)%nat ->
nth i (upd_bytes l k bs) d = if (k <=? i)%nat && (i <? k + length bs)%nat then nth (i - k) bs d else nth i l d.
Proof.
intros l k bs i d H. unfold upd_bytes.
destruct (Nat.leb_spec k i); destruct (Nat.ltb_spec i (k + length bs)); cbn [andb].
- rewrite app_nth2 by (rewrite firstn_length_le; lia). rewrite firstn_length_le by lia. rewrite app_nth1 by lia. reflexivity.
- rewrite app_nth2 by (rewrite firstn_length_le; lia). rewrite firstn_length_le by lia. rewrite app_nth2 by lia.
rewrite nth_skipn. f_equal. lia.
- rewrite app_nth1 by (rewrite firstn_length_le; lia). rewrite nth_firstn. destruct (Nat.ltb_spec i k); [reflexivity| lia].
- lia.
Qed.

Lemma upd_all_agree : forall ws (l1 l2 : list byte) d, length l1 = length l2 -> wbounds ws (length l1) ->
forall i, (i < length l1)%nat -> (nth i l1 d = nth i l2 d \/ wcovers ws i = true) -> nth i (upd_all l1 ws) d = nth i (upd_all l2 ws) d.
Proof.
induction ws as [|w ws IH]; intros l1 l2 d LEN WB i Hi H.
- cbn in *. destruct H as [H|H]; [exact H| discriminate H].
- cbn [upd_all fold_left] in *. inversion WB as [|w' ws' Hw WB']. subst.
unfold upd_all in IH. apply IH.
+ unfold upd1. rewrite !upd_bytes_length by lia. exact LEN.
+ unfold upd1. rewrite upd_bytes_length by lia. exact WB'.
+ unfold upd1. rewrite upd_bytes_length by lia. exact Hi.
+ unfold upd1. rewrite !nth_upd_bytes by lia. cbn [wcovers existsb] in H.
destruct ((fst w <=? i)%nat && (i <? fst w + length (snd w))%nat) eqn:E; [left; reflexivity|].
cbn [orb] in H. exact H.
Qed.

Lemma upd_all_cover : forall ws (l1 l2 : list byte), length l1 = length l2 -> wbounds ws (length l1) ->
forallb (wcovers ws) (seq 0 (length l1)) = true -> upd_all l1 ws = upd_all l2 ws.
Proof.
intros ws l1 l2 LEN WB COV.
assert (L1 : length (upd_all l1 ws) = length l1).
{ clear COV LEN l2. revert l1 WB. induction ws as [|w ws IH]; intros l1 WB; [reflexivity|].
inversion WB; subst. cbn [upd_all fold_left]. unfold upd_all in IH. rewrite IH; unfold upd1; rewrite ?upd_bytes_length by lia; [reflexivity|]. exact H2. }
assert (L2 : length (upd_all l2 ws) = length l2).
{ rewrite LEN in WB. clear COV LEN L1 l1. revert l2 WB. induction ws as [|w ws IH]; intros l2 WB; [reflexivity|].
inversion WB; subst. cbn [upd_all fold_left]. unfold upd_all in IH. rewrite IH; unfold upd1; rewrite ?upd_bytes_length by lia; [reflexivity|]. exact H2. }
apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [congruence|].
intros i Hi. rewrite L1 in Hi. apply (upd_all_agree ws l1 l2 _ LEN WB i Hi). right.
rewrite forallb_forall in COV. apply COV. apply in_seq. lia.
Qed.

Lemma rw_cells_CB_store_all : forall segs (m : word -> option byte) A n base ws (kn : nat) bs,
rw_cells segs m A [CB n (upd_all base ws)] -> (kn + length bs <= n)%nat ->
rw_cells segs (write_to_mem m (wa (A + Z.of_nat kn)) bs) A [CB n (upd_all base (ws ++ [(kn, bs)]))].
Proof.
intros segs m A n base ws kn bs H K. unfold upd_all. rewrite fold_left_app. cbn [fold_left]. unfold upd1 at 1. cbn [fst snd].
apply rw_cells_CB_store_nat; [exact H| exact K].
Qed.

Definition zw (w : Z * list byte) : nat * list byte := (Z.to_nat (fst w), snd w).
Inductive hsh_hist (c base : list byte) (ws : list (Z * list byte)) : Prop := HSH (E : c = upd_all base (rev (map zw ws))).
Lemma hsh_hist_start : forall c, hsh_hist c c [].
Proof. intros c. constructor. reflexivity. Qed.
Lemma hsh_hist_step : forall c base ws kz bs, hsh_hist c base ws -> hsh_hist (upd_bytes c (Z.to_nat kz) bs) base ((kz, bs) :: ws).
Proof. intros c base ws kz bs [H]. constructor. cbn [rev map]. unfold upd_all. rewrite fold_left_app. cbn [fold_left]. rewrite H. reflexivity. Qed.
Lemma hsh_hist_eq : forall c base ws, hsh_hist c base ws -> c = upd_all base (rev (map zw ws)).
Proof. intros c base ws [H]. exact H. Qed.
Ltac hsh_store1 :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
lazymatch goal with
| H : rw_cells segs m A [CB ?n ?c] |- _ =>
lazymatch goal with
| HH : hsh_hist c ?base ?ws |- _ =>
let KN := fresh "KN" in assert (KN : (kn + length bs <= n)%nat) by (apply Nat.leb_le; vm_compute; reflexivity);
let HB := fresh "HB" in pose proof (rw_cells_bound segs m A _ H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with HI : mem_inv segs m |- _ => apply (mem_inv_CB_store_nat' segs m A n c kn bs H KN) in HI end;
let kz := eval vm_compute in (Z.of_nat kn) in
let c' := fresh "c" in
pose (c' := upd_bytes c kn bs);
let H' := fresh "CH" in
pose proof (rw_cells_CB_store_nat segs m A n c kn bs H KN : rw_cells segs (write_to_mem m (wa (A + Z.of_nat kn)) bs) A [CB n c']) as H';
let HH' := fresh "HH" in
pose proof (hsh_hist_step c base ws kz bs HH : hsh_hist c' base ((kz, bs) :: ws)) as HH';
clearbody c';
clear H KN HH;
store_facts (A + Z.of_nat kn)%Z bs ltac:(fun n' Hn Ha Hl =>
transport_chunks_with segs m (A + Z.of_nat kn)%Z bs n' Hn Ha Hl;
footprint_after_store_with segs m (A + Z.of_nat kn)%Z bs n' Hn Ha Hl);
let m' := fresh "m" in gen_mem (write_to_mem m (wa (A + Z.of_nat kn)) bs) m'; clear HB; try clear m; try clear c;
rename H' into H; rename HH' into HH
end
end
end.

Ltac hsh_store :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let ln := eval vm_compute in (length bs) in
lazymatch ln with 1%nat => idtac end;

try lazymatch bs with le1 (Z_to_bv 64 ?z) => rewrite (le1_lit z) end;
hsh_store1
end.
Definition wbounds_b (ws : list (nat * list byte)) (n : nat) : bool := forallb (fun w => (fst w + length (snd w) <=? n)%nat) ws.
Lemma wbounds_of_b : forall ws n, wbounds_b ws n = true -> wbounds ws n.
Proof.
intros ws n H. unfold wbounds_b in H. rewrite forallb_forall in H. apply Forall_forall. intros w Hw. specialize (H w Hw). apply Nat.leb_le in H. exact H.
Qed.

Ltac hsh_reify e acc :=
lazymatch e with
| upd_bytes ?l ?k ?bs => hsh_reify l (cons (k, bs) acc)
| _ => constr:((e, acc))
end.
Lemma upd_all_snoc : forall (l : list byte) ws k bs, upd_all l (ws ++ [(k, bs)]) = upd_bytes (upd_all l ws) k bs.
Proof. intros. unfold upd_all. rewrite fold_left_app. reflexivity. Qed.

Ltac hsh_reify_eq e :=
lazymatch e with
| upd_bytes ?l ?k ?bs =>
let p := hsh_reify_eq l in
lazymatch type of p with _ = upd_all ?base ?ws =>
constr:(eq_trans (f_equal (fun x => upd_bytes x k bs) p) (eq_sym (upd_all_snoc base ws k bs)))
end
| _ => constr:(eq_refl e : e = upd_all e nil)
end.
Lemma rw_cells_CB_eq : forall segs (m : word -> option byte) A n (l1 l2 : list byte), rw_cells segs m A [CB n l1] -> l1 = l2 -> rw_cells segs m A [CB n l2].
Proof. intros segs m A n l1 l2 H <-. exact H. Qed.

Ltac hsh_start H :=
lazymatch type of H with rw_cells ?segs ?m ?A [CB ?n ?js] =>
let LB := fresh "LB" in pose proof (proj1 (proj1 (proj1 H))) as LB; cbn [csize] in LB;
let HH := fresh "HH" in pose proof (hsh_hist_start js) as HH
end.

Ltac hsh_lit H LIT :=
lazymatch type of H with
| rw_cells ?segs ?m ?A [CB ?n ?c] =>
lazymatch goal with
| HH : hsh_hist c ?base ?ws |- _ =>
let LB := fresh "LB" in assert (LB : length base = n) by assumption;
let H' := fresh "H" in
assert (H' : rw_cells segs m A [CB n LIT]);
[ apply (rw_cells_CB_eq segs m A n c LIT H);
rewrite (hsh_hist_eq c base ws HH);
let wn := eval cbv [rev map zw app fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in (rev (map zw ws)) in
change (rev (map zw ws)) with wn;
transitivity (upd_all (repeat (Z_to_bv 8 0) n) wn);
[ apply upd_all_cover;
[ rewrite repeat_length; exact LB
| rewrite LB; apply wbounds_of_b; vm_compute; reflexivity
| rewrite LB; vm_compute; reflexivity ]
| cbv [upd_all fold_left upd1 upd_bytes firstn skipn app repeat length fst snd Nat.add Nat.sub rev]; reflexivity ]
| clear H HH LB; rename H' into H ]
end
end.

Ltac hsh_lit0 H LIT UNF :=
lazymatch type of H with
| rw_cells ?segs ?m ?A [CB ?n ?c] =>
lazymatch goal with
| HH : hsh_hist c ?base ?ws |- _ =>
let H' := fresh "H" in
assert (H' : rw_cells segs m A [CB n LIT]);
[ apply (rw_cells_CB_eq segs m A n c LIT H);
rewrite (hsh_hist_eq c base ws HH); UNF;
cbv [upd_all fold_left upd1 upd_bytes firstn skipn app repeat length fst snd Nat.add Nat.sub rev map zw Z.to_nat Pos.to_nat Pos.iter_op zruns];
reflexivity
| clear H HH; try match goal with LB : length base = _ |- _ => clear LB end; rename H' into H ]
end
end.
