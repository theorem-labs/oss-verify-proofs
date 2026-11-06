(* Image B (asan-ubsan) twin of lib/A/W6/QSlot.v (a Theorem Labs lane's per-class quarantine slot bound, as image A carries it at
   a working branch 0b6b7fff89f), verbatim except lane names and that it Requires lib/B's ClassConsDef / ClassRoomLow (
   ClassConsDef is image A's text; ClassRoomLow's code is image A's apart from the Require, the name crl_prim_class_in for prim_class_in, and the place of the bc_row .. a_class_bytes_out block) instead of lib/A's. Seg/Tac_cls.v reads no_request_in_classes_0_5_31 from it. *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
(* The per-class quarantine slot bound QSLOT c (a Theorem Labs lane).

   a Theorem Labs lane ruled (2026-10-28 03:58Z) that the class-full side condition must be PER CLASS: one constant for every
   class is either unsound or excludes real units (fuzz_preset needs 3.22 GiB live in class 17). This file gives the
   per-class constants that the allocator _cf contracts cite, and the lemmas that make them usable.

   - qmin_of_class c: the smallest primary request n (1 .. 64512, the range where is_primary n = true) with
     class_id (needed_size n) = c. It is a bounded search (List.find over AsanCtrlProps.zseq), not a typed table.
     qmin_of_class_in (it is in class c) and qmin_of_class_min (no smaller request is in class c) are checked by
     vm_compute, in the forallb / zseq idiom of fuzz_preset's lib/A/Prog/PresetPlainRoomC.v every_class_ok. When no
     request of 1 .. 64512 is in class c, the search returns 64513, one past the range. That is true for classes 0, 5
     and 31 (no_request_in_classes_0_5_31). fuzz_preset's CLASS_TAB finds the same three gaps independently. So
     qmin_of_class_in excludes c = 5, and QSLOT 5 = 831520 is sound because qprim_bytes st 5 is always 0.
   - QSLOT_of Q c = (Q * Q_BATCH / (qmin_of_class c * Q_BATCH + Q_BATCH_BYTES) + Q_BATCH) * size_of_class c, and
     QSLOT c = QSLOT_of (Q_MAX + Q_CACHE) c. BC_MAX c = K_FREEARR_OFF - (QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP)
     is the most live slot bytes class c can hold while class_room still holds. qslot_table gives every class's row,
     and QSLOT_1 .. BC_MAX_29 give the three rows real units use. A change to a constant breaks these Examples.
   - quar_slots_of_bytes_c (lib/B/ClassRoomLow.v, with the counting lemmas quar_count_bound and
     quar_count_batches_bound): from a_quar_wf and a byte bound Q <= Q_MAX + Q_CACHE on quar_sum, the quarantined slots
     of every class c (0 <= c < K_NUM_CLASSES, classes 0, 5 and 31 included) are at most QSLOT_of Q c. The argument:
     a batch of k <= Q_BATCH class-c chunks costs at least k * qmin_of_class c + Q_BATCH_BYTES bytes of quar_sum,
     because a_quar_wf ties each quarantined CPrim c n to its request (1 <= n, c = class_id (needed_size n)). The
     ratio k / (k * qmin + Q_BATCH_BYTES) is greatest at k = Q_BATCH. So for ANY mix of full and partial batches,
     qprim_count * (qmin * Q_BATCH + Q_BATCH_BYTES) <= Q_BATCH * quar_sum (quar_count_bound). For c <> K_BATCH_CLASS,
     the + Q_BATCH term of QSLOT_of is slack. Class K_BATCH_CLASS also counts one metadata slot per batch
     (qbatch_bytes). There (k + 1) * (qmin * Q_BATCH + Q_BATCH_BYTES) <= (Q_BATCH + 1) * (batch cost), because
     (Q_BATCH - k) * (Q_BATCH_BYTES - qmin) >= 0 (quar_count_batches_bound). The surplus over the stated form is
     Q / (qmin * Q_BATCH + Q_BATCH_BYTES) slots, and the + Q_BATCH term covers it only while
     Q <= 1020 * 6020861. The premise Q <= Q_MAX + Q_CACHE gives this.
   - The two refutations below show that the premises are necessary. Each one compiles:
     * zero_size_breaks_qslot_1: if a quarantined primary chunk could have n = 0 (the clause of a_quar_wf before
       this lane), 32896 batches of 1021 zero-byte class-1 chunks would hold quar_sum = Q_MAX + Q_CACHE and
       1074778112 slot bytes of class 1, which is more than QSLOT 1 = 955702080. ClassConsDef.v's qchunk_wf now
       states 1 <= n (the model never quarantines a zero-size chunk: AInstanceM.v AHI_block gives 1 <= n, and
       QuarWf.v proves the clause).
     * qslot_of_needs_q_cap: without Q <= Q_MAX + Q_CACHE, 1022 full batches of CPrim 24 5889 have a_quar_wf,
       quar_sum = 6153319942 and 8556412928 slot bytes of class 24, which is more than
       QSLOT_of 6153319942 24 = 8556404736.
   - class_room_of_live_per_class (lib/B/ClassRoomLow.v): class_room from class_cons with a per-class live bound
     Bc c and the per-class quarantine bound QSLOT c.

   The definitions (in_class, qmin_of_class, QSLOT_of, QSLOT, BC_MAX) are in lib/B/ClassConsDef.v and the pure lemmas
   (qmin_of_class_lb, quar_slots_of_bytes_c, class_room_of_live_per_class, ...) in lib/B/ClassRoomLow.v, below the W6
   heap field. This file keeps the vm_compute checks (qmin_of_class_min, the table and the per-class Examples), whose
   cost must not move into the low files, and the two refutations. It Requires only the low files.

   Before defining a new identifier in this family, grep lib/** for it: a_class_room was defined in two places
   (ClassFullDead.v:482 and SlotAgree.v:302) before anyone noticed.

   No allocator function is proved here: these are constants checked by vm_compute and counting lemmas over the
   allocator model's quarantine. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AZ.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AZ.Spec Require AsanCtrlProps.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ClassConsDef ClassRoomLow.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------- qmin_of_class: the smallest request of a class ---------- *)

(* in_class, qmin_of_class, QSLOT_of, QSLOT and BC_MAX are defined in lib/B/ClassConsDef.v (below the W6 heap field,
   so that Contract.v can cite them); their properties and the build-breaking Examples are here. *)

(* Every request of 1 .. 64512 is primary. *)
Example primary_sizes_primary : forallb is_primary (AsanCtrlProps.zseq 1 (Z.to_nat 64512)) = true.
Proof. vm_compute. reflexivity. Qed.

(* One pass over the classes 1 .. 30: the search result is a request of the class (class 5 has none). *)
Definition qmin_in_chk (c : Z) : bool :=
  let q := qmin_of_class c in (c =? 5) || (is_primary q && (class_id (needed_size q) =? c)).

Example every_qmin_in : forallb qmin_in_chk (AsanCtrlProps.zseq 1 (Z.to_nat 30)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma qmin_of_class_in : forall c, 1 <= c <= 30 -> c <> 5 ->
  is_primary (qmin_of_class c) = true /\ class_id (needed_size (qmin_of_class c)) = c.
Proof.
  intros c Hc H5.
  pose proof (AsanCtrlProps.forallb_zseq qmin_in_chk 1 (Z.to_nat 30) every_qmin_in c
                ltac:(rewrite Z2Nat.id; lia)) as H.
  unfold qmin_in_chk in H. cbv zeta in H.
  apply orb_true_iff in H as [H | H]; [apply Z.eqb_eq in H; lia |].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H2. split; assumption.
Qed.

(* One pass over all 32 classes: no request of 1 .. 64512 in class c is below the search result. *)
Definition qmin_min_chk (c : Z) : bool :=
  let q := qmin_of_class c in
  forallb (fun n => negb (is_primary n && (class_id (needed_size n) =? c)) || (q <=? n))
          (AsanCtrlProps.zseq 1 (Z.to_nat 64512)).

Example every_qmin_min : forallb qmin_min_chk (AsanCtrlProps.zseq 0 (Z.to_nat 32)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma qmin_of_class_min : forall c, 0 <= c < K_NUM_CLASSES ->
  forallb (fun n => negb (is_primary n && (class_id (needed_size n) =? c)) || (qmin_of_class c <=? n))
          (AsanCtrlProps.zseq 1 (Z.to_nat 64512)) = true.
Proof.
  intros c Hc.
  pose proof (AsanCtrlProps.forallb_zseq qmin_min_chk 0 (Z.to_nat 32) every_qmin_min c
                ltac:(unfold K_NUM_CLASSES in Hc; rewrite Z2Nat.id; lia)) as H.
  unfold qmin_min_chk in H. cbv zeta in H. exact H.
Qed.

(* ---------- The table ---------- *)

(* Per class: (c, qmin_of_class c, QSLOT c, BC_MAX c). *)
Example qslot_table :
  map (fun c => (c, qmin_of_class c, QSLOT c, BC_MAX c)) (AsanCtrlProps.zseq 0 (Z.to_nat 32)) =
  [ (0, 64513, 0, 3757047808); (1, 1, 955702080, 2801345728);
    (2, 17, 689296384, 3067751424); (3, 49, 453778752, 3303269056);
    (4, 65, 472498432, 3284549376); (5, 64513, 831520, 3756216288);
    (6, 97, 492856512, 3264191296); (7, 129, 440769280, 3316278528);
    (8, 161, 408417024, 3348630784); (9, 193, 386375040, 3370672768);
    (10, 225, 370396160, 3386651648); (11, 257, 358283552, 3398764256);
    (12, 289, 348787968, 3408259840); (13, 321, 341145792, 3415902016);
    (14, 353, 334864320, 3422183488); (15, 385, 329610720, 3427437088);
    (16, 417, 325153792, 3431894016); (17, 449, 453635328, 3303412480);
    (18, 641, 426224640, 3330823168); (19, 897, 458933760, 3298114048);
    (20, 1409, 391571456, 3365476352); (21, 1921, 432291840, 3324755968);
    (22, 2945, 377966592, 3379081216); (23, 3969, 422590464, 3334457344);
    (24, 5889, 382722048, 3374325760); (25, 7937, 429330432, 3327717376);
    (26, 12033, 383401984, 3373645824); (27, 16129, 435486720, 3321561088);
    (28, 24065, 400261120, 3356786688); (29, 32257, 460701696, 3296346112);
    (30, 48129, 433782784, 3323265024); (31, 64513, 332608, 3756715200) ].
Proof. vm_compute. reflexivity. Qed.

(* The three classes real units use (fuzz_preset: class 17). *)
Example QSLOT_1 : QSLOT 1 = 955702080.
Proof. vm_compute. reflexivity. Qed.
Example BC_MAX_1 : BC_MAX 1 = 2801345728.
Proof. vm_compute. reflexivity. Qed.
Example QSLOT_17 : QSLOT 17 = 453635328.
Proof. vm_compute. reflexivity. Qed.
Example BC_MAX_17 : BC_MAX 17 = 3303412480.
Proof. vm_compute. reflexivity. Qed.
Example QSLOT_29 : QSLOT 29 = 460701696.
Proof. vm_compute. reflexivity. Qed.
Example BC_MAX_29 : BC_MAX 29 = 3296346112.
Proof. vm_compute. reflexivity. Qed.

(* The empty searches. Separate Examples: injection on a tuple of qmin_of_class terms reduces the searches lazily
   and does not finish. *)
Example qmin_of_class_0 : qmin_of_class 0 = 64513.
Proof. vm_compute. reflexivity. Qed.
Example qmin_of_class_5 : qmin_of_class 5 = 64513.
Proof. vm_compute. reflexivity. Qed.
Example qmin_of_class_31 : qmin_of_class 31 = 64513.
Proof. vm_compute. reflexivity. Qed.

(* No request of 1 .. 64512 maps to class 0, 5 or 31. *)
Lemma no_request_in_classes_0_5_31 : forall n, 1 <= n <= 64512 ->
  class_id (needed_size n) <> 0 /\ class_id (needed_size n) <> 5 /\ class_id (needed_size n) <> 31.
Proof.
  intros n Hn. pose proof qmin_of_class_0 as E0. pose proof qmin_of_class_5 as E5.
  pose proof qmin_of_class_31 as E31.
  split; [| split]; intros Hc.
  - pose proof (qmin_of_class_lb 0 ltac:(unfold K_NUM_CLASSES; lia) n Hn Hc). lia.
  - pose proof (qmin_of_class_lb 5 ltac:(unfold K_NUM_CLASSES; lia) n Hn Hc). lia.
  - pose proof (qmin_of_class_lb 31 ltac:(unfold K_NUM_CLASSES; lia) n Hn Hc). lia.
Qed.

(* ---------- The two refutations ---------- *)

Lemma Forall_repeat_of : forall {A} (P : A -> Prop) (x : A) k, P x -> Forall P (List.repeat x k).
Proof. intros A P x k Hx. induction k as [|k IH]; cbn [List.repeat]; constructor; assumption. Qed.

Lemma Forall_repeat_head : forall {A} (P : A -> Prop) (x : A) k, (0 < k)%nat -> Forall P (List.repeat x k) -> P x.
Proof.
  intros A P x [|k] Hk H; [lia |]. cbn [List.repeat] in H. apply Forall_cons_iff in H as [H _]. exact H.
Qed.

Lemma qsum_repeat : forall b k,
  qsum (List.repeat b k) = Z.of_nat k * (fold_right Z.add 0 (map chunk_size (b_chunks b)) + Q_BATCH_BYTES).
Proof.
  intros b k. induction k as [|k IH]; [unfold qsum; cbn [List.repeat map fold_right]; lia |].
  cbn [List.repeat]. rewrite qsum_cons, IH, Nat2Z.inj_succ. unfold Z.succ. ring.
Qed.

Lemma cntP_repeat : forall c b k,
  cfd_cntP c (cfd_qchunks (List.repeat b k)) = Z.of_nat k * cfd_cntP c (b_chunks b).
Proof.
  intros c b k. induction k as [|k IH]; [reflexivity |].
  cbn [List.repeat]. rewrite cfd_qchunks_cons, cfd_cntP_app, IH, Nat2Z.inj_succ. unfold Z.succ. ring.
Qed.

(* The chunk clause of a_quar_wf as it stood before this lane: a primary chunk's request could be 0. *)
Definition qchunk_wf0 (ch : achunk) : Prop :=
  match ch with
  | CPrim c n => 0 <= n <= 64512 /\ c = class_id (needed_size n)
  | CSec _ _ n => 0 <= n
  end.

Definition zero_batch : abatch :=
  mkABatch Q_BATCH Q_BATCH_BYTES (List.repeat (CPrim 1 0) (Z.to_nat Q_BATCH)).

(* With n = 0 allowed, the quarantine at exactly Q_MAX + Q_CACHE bytes holds more class-1 slots than QSLOT 1.
   ClassConsDef.qchunk_wf (1 <= n) excludes it. *)
Lemma zero_size_breaks_qslot_1 : forall st,
  a_qloc st = List.repeat zero_batch (Z.to_nat 32896) -> a_qglob st = [] ->
  Forall (fun b => Z.of_nat (List.length (b_chunks b)) <= Q_BATCH /\ Forall qchunk_wf0 (b_chunks b))
         (a_qloc st ++ a_qglob st)
  /\ ~ a_quar_wf st
  /\ quar_sum st = Q_MAX + Q_CACHE
  /\ QSLOT 1 < qprim_bytes st 1 + qbatch_bytes st 1.
Proof.
  intros st Hl Hg.
  assert (Hc : qchunk_wf0 (CPrim 1 0)) by (cbn [qchunk_wf0]; split; [lia | vm_compute; reflexivity]).
  assert (Hb : Z.of_nat (List.length (b_chunks zero_batch)) <= Q_BATCH /\ Forall qchunk_wf0 (b_chunks zero_batch)).
  { unfold zero_batch. cbn [b_chunks]. rewrite List.repeat_length, Z2Nat.id by (unfold Q_BATCH; lia).
    split; [lia | apply Forall_repeat_of; exact Hc]. }
  split; [rewrite Hl, Hg, app_nil_r; apply Forall_repeat_of; exact Hb |].
  split.
  - unfold a_quar_wf. rewrite Hl, Hg, app_nil_r. intros HW.
    pose proof (Forall_repeat_head _ zero_batch (Z.to_nat 32896) ltac:(lia) HW) as [_ HW1].
    unfold zero_batch in HW1. cbn [b_chunks] in HW1.
    pose proof (Forall_repeat_head _ (CPrim 1 0) (Z.to_nat Q_BATCH) ltac:(unfold Q_BATCH; lia) HW1) as HW2.
    cbn [qchunk_wf] in HW2. lia.
  - assert (U : fold_right Z.add 0 (map chunk_size (b_chunks zero_batch)) = 0) by (vm_compute; reflexivity).
    assert (C : cfd_cntP 1 (b_chunks zero_batch) = 1021) by (vm_compute; reflexivity).
    split.
    + unfold quar_sum. rewrite Hl, Hg, app_nil_r, qsum_repeat, U, Z2Nat.id by lia.
      unfold Q_BATCH_BYTES, Q_MAX, Q_CACHE. lia.
    + unfold qprim_bytes, qbatch_bytes. rewrite qprim_count_cntP, Hl, Hg, app_nil_r, cntP_repeat, C.
      apply Z.ltb_lt. vm_compute. reflexivity.
Qed.

Definition full24_batch : abatch :=
  mkABatch Q_BATCH (5889 * Q_BATCH + Q_BATCH_BYTES) (List.repeat (CPrim K_BATCH_CLASS 5889) (Z.to_nat Q_BATCH)).

(* Without Q <= Q_MAX + Q_CACHE, quar_slots_of_bytes_c is false at the batch class. *)
Lemma qslot_of_needs_q_cap : forall st,
  a_qloc st = List.repeat full24_batch (Z.to_nat 1022) -> a_qglob st = [] ->
  a_quar_wf st
  /\ quar_sum st = 6153319942
  /\ QSLOT_of 6153319942 K_BATCH_CLASS < qprim_bytes st K_BATCH_CLASS + qbatch_bytes st K_BATCH_CLASS.
Proof.
  intros st Hl Hg.
  assert (Hc : qchunk_wf (CPrim K_BATCH_CLASS 5889)) by (cbn [qchunk_wf]; split; [lia | vm_compute; reflexivity]).
  assert (Hb : qbatch_wf full24_batch).
  { unfold qbatch_wf, full24_batch. cbn [b_chunks]. rewrite List.repeat_length, Z2Nat.id by (unfold Q_BATCH; lia).
    split; [lia | apply Forall_repeat_of; exact Hc]. }
  split; [unfold a_quar_wf; rewrite Hl, Hg, app_nil_r; apply Forall_repeat_of; exact Hb |].
  assert (U : fold_right Z.add 0 (map chunk_size (b_chunks full24_batch)) = 5889 * Q_BATCH)
    by (vm_compute; reflexivity).
  assert (C : cfd_cntP K_BATCH_CLASS (b_chunks full24_batch) = Q_BATCH) by (vm_compute; reflexivity).
  split.
  - unfold quar_sum. rewrite Hl, Hg, app_nil_r, qsum_repeat, U, Z2Nat.id by lia.
    unfold Q_BATCH, Q_BATCH_BYTES. lia.
  - unfold qprim_bytes, qbatch_bytes. rewrite qprim_count_cntP, Hl, Hg, app_nil_r, cntP_repeat, C, Z.eqb_refl.
    rewrite List.repeat_length. apply Z.ltb_lt. vm_compute. reflexivity.
Qed.
