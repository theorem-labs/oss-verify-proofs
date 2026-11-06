(* The definitions of the ASan class-accounting family (a Theorem Labs lane): the per-class conservation invariant class_cons and
   its accounting terms, the quarantine's well-formedness a_quar_wf, and the per-class quarantine slot constants.
   Definitions only, no theorems.

   Why this file exists, and why it is outside W6: a Theorem Labs lane adds class_cons H st to the W6 heap field. The field lives
   in W6/AHDef.v (not in this delivery) and W6/MallocCloseDef.v (not in this delivery), which W6/ClassCons.v (not in this delivery) imports for its preservation proofs, so the field
   cannot cite ClassCons.v (not in this delivery) (an import cycle). These definitions have no proof content and depend only on the
   allocator model (AZ/Spec/AsanCtrl.v, and AsanCtrlProps.v for zseq), so they sit below the field, and outside W6 so
   that Contract.v can Require this file without pointing into W6. NOTHING IN THIS FILE MAY EVER IMPORT THE HEAP
   FIELD (W6/AHDef.v, W6/MallocCloseDef.v, or anything that imports them).

   The pure theorems over these definitions (an astate and the model's own functions only) are in the sibling low
   file lib/A/ClassRoomLow.v, so that the W6 sites, which cannot see the field, can use them as theorems. The theorems
   that mention the field stay above it: class_cons_at_main, class_cons_post_malloc, _asize and class_cons_post_free
   in W6/ClassCons.v; a_quar_wf's theorems in W6/QuarWf.v; qmin_of_class's minimality proof and the build-breaking
   vm_compute Examples in W6/QSlot.v (their cost must not move into a file that many files import).

   - a_class_count H c, a_class_bytes H c: the live primary blocks of H in class c, and their slot bytes.
   - qbatch_chunks, qprim_count, qprim_bytes: the quarantined primary chunks of class c, and their slot bytes.
   - qbatch_bytes: one K_BATCH_CLASS slot per quarantine batch (its metadata slot).
   - c_reserved_user: the class's free-listed and cached slots.
   - class_cons H st: per class, c_allocated_user is at most the live, quarantined, batch and reserved slots, and
     c_mapped_user is at most c_allocated_user plus one slot (POP_SLACK, the refill's carve tail).
     class_cons_mapped_bound: the bound on c_mapped_user that class_cons gives.
   - qchunk_wf, qbatch_wf, a_quar_wf: the quarantine's well-formedness.
   - QCAP = Q_MAX + Q_CACHE, the quarantine's byte cap at every state of the heap field (W6/QuarCap.v).
   - in_class, qmin_of_class, QSLOT_of, QSLOT, BC_MAX: the per-class quarantine slot constants (W6/QSlot.v).
   - a_class_req_fits Bc H n: the contract's per-class fit of the live slots of H plus the slot of a request n
     under a per-class bound Bc (W6/QuarCap.v class_room_of_req_fits reads class_room from it).
   - The terms of the pure lemmas in lib/A/ClassRoomLow.v: am_all (every leaf of an allocator tree), pop_ums,
     pop_leaf, mu_eq (one refill's user map), class_room (room for the next refill), a_class_live_bytes,
     a_quar_slots, qsum, quar_sum, the cfd_* list counts, and the vm_compute checkers size_chk and crl_size2n_chk.
     crl_size2n_chk is a deliberate local copy of AZ/Spec/AsanBudget.v size2n_chk: the low files must not Require
     AsanBudget (see ClassRoomLow.v's header).
   - a_slot_of, a_slot_bytes, a_user_bytes: the slot bytes of one block, and the total slot bytes and user bytes of
     the live blocks H (ClassRoomLow.v a_class_bytes_le_total, a_slot_bytes_le_user, a_class_bytes_le_user).
     a_user_bytes is Contract.v a_live_bytes under another name; the comment at its definition says why both exist.

   The low files Require AZ/Spec/STree (for am_all's SRet / SVis) as well as AsanCtrl and AsanCtrlProps. AsanCtrl
   already Requires STree, so it adds no dependency; do not prune it. *)
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AZ.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AZ.Spec Require AsanCtrlProps.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------- class_cons ---------- *)

Definition a_class_count (H : list (Z * Z)) (c : Z) : Z :=
  Z.of_nat (List.length (List.filter (fun qm => is_primary (snd qm) && (class_id (needed0 (snd qm)) =? c)) H)).

Definition a_class_bytes (H : list (Z * Z)) (c : Z) : Z := a_class_count H c * size_of_class c.

Definition qbatch_chunks (st : astate) : list achunk :=
  List.concat (List.map b_chunks (a_qloc st ++ a_qglob st)).

Definition qprim_count (st : astate) (c : Z) : Z :=
  Z.of_nat (List.length
    (List.filter (fun ch => match ch with CPrim c' _ => c' =? c | CSec _ _ _ => false end)
      (qbatch_chunks st))).

(* Slot-based: a quarantined primary chunk of class c occupies one full slot (size_of_class c) of the class's
   mapped user region, like a live / free-listed / cached chunk, independent of the user request. Summing the
   user request (chunk_size) breaks preservation by free of an under-full block (ClassConsDisproof). *)
Definition qprim_bytes (st : astate) (c : Z) : Z := qprim_count st c * size_of_class c.

(* Each live quarantine batch holds one metadata slot of class K_BATCH_CLASS (Q_BATCH_BYTES = size_of_class
   K_BATCH_CLASS = 8192), carved from that class but recorded in no chunk list; so class K_BATCH_CLASS must count
   one slot per batch (ClassConsBatchChk: new_batch free breaks class_cons at 24 without this). *)
Definition qbatch_bytes (st : astate) (c : Z) : Z :=
  (if c =? K_BATCH_CLASS then Z.of_nat (List.length (a_qloc st ++ a_qglob st)) else 0) * size_of_class c.

Definition POP_SLACK (c : Z) : Z := size_of_class c.

Definition c_reserved_user (st : astate) (c : Z) : Z :=
  (c_num_freed (get_cls st c) + c_count (get_cls st c)) * size_of_class c.

Definition class_cons (H : list (Z * Z)) (st : astate) : Prop :=
  forall c, 0 <= c < K_NUM_CLASSES ->
    c_allocated_user (get_cls st c)
      <= a_class_bytes H c + qprim_bytes st c + qbatch_bytes st c + c_reserved_user st c
    /\ c_mapped_user (get_cls st c) <= c_allocated_user (get_cls st c) + POP_SLACK c.

Definition class_cons_mapped_bound : Prop :=
  forall H st c, class_cons H st -> 0 <= c < K_NUM_CLASSES ->
    0 <= qprim_bytes st c -> 0 <= qbatch_bytes st c -> 0 <= c_reserved_user st c ->
    c_mapped_user (get_cls st c)
      <= a_class_bytes H c + qprim_bytes st c + qbatch_bytes st c + c_reserved_user st c + POP_SLACK c.

(* ---------- a_quar_wf ---------- *)

(* A quarantined chunk as the allocator made it: a primary chunk's request is 1 .. 64512 bytes (the freed block's
   user size, 1 <= n <= AREQMAX, AInstanceM.v AHI_block; W6/QuarWf.v derives it), its class is the class of its
   request (the class clause of AZ/AsanW/ARep.v awf's BLive and BQuar branches, W6/LivePrimClass.v live_prim_class
   and awf_busy_class), and a secondary chunk's size is not negative. The lower bound 1 <= n is needed: with n = 0
   allowed, class 1 (class_id (needed_size 0) = 1) could hold 1021 zero-byte chunks per 8192-byte batch, which breaks
   the per-class slot bound QSLOT (W6/QSlot.v zero_size_breaks_qslot_1). *)
Definition qchunk_wf (ch : achunk) : Prop :=
  match ch with
  | CPrim c n => 1 <= n <= 64512 /\ c = class_id (needed_size n)
  | CSec _ _ n => 0 <= n
  end.

(* A quarantine batch holds at most Q_BATCH chunks, each well formed. *)
Definition qbatch_wf (b : abatch) : Prop :=
  Z.of_nat (List.length (b_chunks b)) <= Q_BATCH /\ Forall qchunk_wf (b_chunks b).

Definition a_quar_wf (st : astate) : Prop := Forall qbatch_wf (a_qloc st ++ a_qglob st).

(* ---------- The per-class quarantine slot constants (W6/QSlot.v proves their properties) ---------- *)

(* The quarantine's byte cap at every state of the heap field (W6/QuarCap.v a_quar_bytes_inv). *)
Definition QCAP : Z := Q_MAX + Q_CACHE.

Definition in_class (c n : Z) : bool := is_primary n && (class_id (needed_size n) =? c).

(* The contract's per-class fit: the live slot bytes of H plus, for a primary request n of class c, its one slot
   (size_of_class c, because a_class_bytes counts slot bytes) are at most Bc c. *)
Definition a_class_req_fits (Bc : Z -> Z) (H : list (Z * Z)) (n : Z) : Prop :=
  forall c, 0 <= c < K_NUM_CLASSES ->
    a_class_bytes H c + (if in_class c n then size_of_class c else 0) <= Bc c.

(* The first n of 1 .. 64512 in class c; 64513 (one past the range) when there is none. *)
Definition qmin_of_class (c : Z) : Z :=
  match List.find (in_class c) (AsanCtrlProps.zseq 1 (Z.to_nat 64512)) with
  | Some n => n
  | None => 64513
  end.

Definition QSLOT_of (Q : Z) (c : Z) : Z :=
  (Q * Q_BATCH / (qmin_of_class c * Q_BATCH + Q_BATCH_BYTES) + Q_BATCH) * size_of_class c.

Definition QSLOT (c : Z) : Z := QSLOT_of (Q_MAX + Q_CACHE) c.

Definition BC_MAX (c : Z) : Z := K_FREEARR_OFF - (QSLOT c + 8 * K_MAX_SIZE + 2 * K_USER_MAP).

(* ---------- The terms of the pure lemmas (lib/A/ClassRoomLow.v) ---------- *)

(* Checked by vm_compute in ClassRoomLow.v size_of_class_le. *)
Definition size_chk (c : Z) : bool := (0 <=? size_of_class c) && (size_of_class c <=? K_MAX_SIZE).

(* The user map one refill of req slots of class c makes at st (AsanCtrl.v:301, ums). *)
Definition pop_ums (st : astate) (c req : Z) : Z :=
  rup (c_allocated_user (get_cls st c) + req * size_of_class c - c_mapped_user (get_cls st c)) K_USER_MAP.

(* Every leaf value of s meets P, for every answer to every call; AUndef ends a path. *)
Fixpoint am_all {R} (P : R -> Prop) (s : AM R) {struct s} : Prop :=
  match s with
  | SRet v => P v
  | SVis e k => match e with AUndef _ => True | _ => forall x, am_all P (k x) end
  end.

(* The user maps of all classes, kept. *)
Definition mu_eq (st st' : astate) : Prop :=
  forall c, c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c).

(* A leaf of populate_free_array st c req: the user map of every other class is kept; the user map of class c is
   kept, or (on the mapping branch, AsanCtrl.v:305-308) grows by pop_ums st c req. *)
Definition pop_leaf (st : astate) (c req : Z) (st' : astate) : Prop :=
  (forall c', c' <> c -> c_mapped_user (get_cls st' c') = c_mapped_user (get_cls st c')) /\
  (c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c)
   \/ (c_mapped_user (get_cls st c) < c_allocated_user (get_cls st c) + req * size_of_class c
       /\ c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) + pop_ums st c req)).

(* Every class whose refill cache_alloc can start at st (an empty cache and fewer than max_cached c / 2 free slots,
   AsanCtrl.v:315 and :323) has room for one more refill's user map below its free array. *)
Definition class_room (st : astate) : Prop :=
  forall c, 0 <= c < K_NUM_CLASSES ->
    c_count (get_cls st c) <= 0 -> c_num_freed (get_cls st c) < max_cached c / 2 ->
    c_mapped_user (get_cls st c) + 2 * K_USER_MAP <= K_FREEARR_OFF.

(* Every class's live blocks weigh at most B slot bytes (a_class_bytes). *)
Definition a_class_live_bytes (H : list (Z * Z)) (B : Z) : Prop :=
  forall c, 0 <= c < K_NUM_CLASSES -> a_class_bytes H c <= B.

(* The quarantine, slot-weighted per class: the slots of class c its primary chunks hold and its batches' metadata
   slots (qprim_bytes, qbatch_bytes). *)
Definition a_quar_slots (st : astate) (QS : Z) : Prop :=
  forall c, 0 <= c < K_NUM_CLASSES -> qprim_bytes st c + qbatch_bytes st c <= QS.

(* Deliberate local copy of AZ/Spec/AsanBudget.v size2n_chk; vm_compute checks it in ClassRoomLow.v crl_size2n_range. *)
Definition crl_size2n_chk (n : Z) : bool := size_of_class (class_id (needed_size n)) <=? 2 * n + 32.

(* Per batch, the right side of MallocCloseDef.v ah_batch_cov: its chunks' user bytes plus one batch overhead. *)
Definition qsum (bs : list abatch) : Z :=
  fold_right Z.add 0 (map (fun b => fold_right Z.add 0 (map chunk_size (b_chunks b)) + Q_BATCH_BYTES) bs).

Definition quar_sum (st : astate) : Z := qsum (a_qloc st ++ a_qglob st).

(* List-level counts for the ported AsanBudget.v lemmas. These are the same definitions as lib/A/Acct/AHeapInv.v's (not in this delivery)
   is_prim_of, zlen, cntP, qchunks and zsumc (and its lemmas zlen_app, zlen_cons, zlen_nonneg, cntP_cons, cntP_app,
   qchunks_cons), copied here because AHeapInv.v (not in this delivery) is a file of a Theorem Labs lane's A arms line only: it is not on the B side
   (lib/B/Acct does not exist) nor on the integration line, so this file must not import it. qbatch_chunks and
   qprim_count above count over a state, not a list, so they do not serve the list inductions of ClassRoomLow.v;
   ClassRoomLow.v qprim_count_cntP links the two. *)
Definition cfd_is_prim_of (c : Z) (ch : achunk) : bool :=
  match ch with CPrim c' _ => c' =? c | CSec _ _ _ => false end.
Definition cfd_zlen {A} (l : list A) : Z := Z.of_nat (List.length l).
Definition cfd_cntP (c : Z) (l : list achunk) : Z := cfd_zlen (List.filter (cfd_is_prim_of c) l).
Definition cfd_qchunks (bs : list abatch) : list achunk := flat_map b_chunks bs.
Fixpoint cfd_zsumc (l : list achunk) : Z := match l with [] => 0 | ch :: l' => chunk_size ch + cfd_zsumc l' end.

(* ---------- The live blocks' total slot bytes and user bytes ---------- *)

(* The slot bytes of one live block of n bytes: its class's slot for a primary request, 0 for a secondary one. *)
Definition a_slot_of (n : Z) : Z := if is_primary n then size_of_class (class_id (needed_size n)) else 0.

(* The total slot bytes of the live blocks H. *)
Fixpoint a_slot_bytes (H : list (Z * Z)) : Z := match H with [] => 0 | (_, n) :: H' => a_slot_of n + a_slot_bytes H' end.

(* The total user bytes of the live blocks H. This is line for line the same Fixpoint as Contract.v a_live_bytes. It is
   defined here because the class lemmas (ClassRoomLow.v) sit below Contract.v and cannot Require it. The two are
   linked by one equation, a_live_bytes H = ClassConsDef.a_user_bytes H (induction H; reflexivity), not yet stated; a Theorem Labs lane is to put it
   in Contract.v (it Requires this file), the one place where both are visible.
   Do NOT make Contract.a_live_bytes an alias of this definition (or this one an alias of it), and do not delete either
   one as a duplicate: the proofs of every unit rely on a_live_bytes's own Fixpoint shape for simpl and induction, and
   a change of its definition during a generation moves goal shapes in every unit (a Theorem Labs lane, 2026-10-28 08:51Z). *)
Fixpoint a_user_bytes (H : list (Z * Z)) : Z := match H with [] => 0 | (_, n) :: H' => n + a_user_bytes H' end.
