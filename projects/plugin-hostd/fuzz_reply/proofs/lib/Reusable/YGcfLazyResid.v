(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfLazyResid.v, sha256 3451971d9497fe16919d0613a5d2910740ff1b7a02b3ceb6e0c281ef628f64b3 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30: the lazy-residue argument at cgif's types, ported from the fuzz_manifest kit
   (omx-clap-core/fuzz_manifest lib/A/LazyResid.v, LazyResidPf.v, LazyResidPf2.v, LazyEvictPf.v on
   a working branch 7bb12afd3646; owner a Theorem Labs lane, a Theorem Labs lane 05:00Z / 05:09Z).
   The world keeps every dead secondary's shadow hull in w_A, so MInv's mat <= A_bytes (w_A W) grows by a hull
   per recycle. The materialized pages are bounded here instead by a CANONICAL set read from the allocator state:
   the base (the at-main allowance A0, the whole primary reservation, the pointer-array reservation and every
   mapped secondary with its shadow hull) plus the RESIDUE, the materialized pages outside the base. An eviction
   leaves at most its two edge shadow pages as residue (the madvise drops the hull's interior, the munmap the map),
   so the residue is at most 2 pages per evicted secondary (resid_inv_cf), and
     |mat| * page_size <= Cker A0 ly S (k - qsec_cf S)
   with k the secondary frees so far (mat_canon_of_resid_cf).
   The one premise a step supplies is step_mat_in_cf (every page materialized after the step was materialized
   before, or lies in the new base, or in the step's P; and every old-base page still materialized lies in the new
   base or in P). The engine does not supply it today (a Theorem Labs lane 05:04Z: YA0n.SRr_step forgets the accounting
   equation); that is VERIFY's E1 / E2 item, not a premise of this file's lemmas. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Madvise.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YK0v YA06 YFfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0f YG0n YG01 YGcfNames YG0ncf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The residue over any base B.                                              *)

Definition resid_pg_cf (B : list (Z * Z)) (md : Model) : list word :=
  List.filter (fun p => negb (page_allowedb B p)) (m_vm_materialized md).

Definition nresid_cf (B : list (Z * Z)) (md : Model) : Z := Z.of_nat (length (resid_pg_cf B md)).

(* THE per-step premise (resid_delta's two inclusion clauses). P is the step's new residue: [] for a step whose
   new materialized pages lie in the base, evict_edges_cf for a secondary eviction. *)
Definition step_mat_in_cf (B B' : list (Z * Z)) (P : list word) (md md' : Model) : Prop :=
  (forall p, In p (m_vm_materialized md') ->
     In p (m_vm_materialized md) \/ page_allowedb B' p = true \/ In p P) /\
  (forall p, page_allowedb B p = true -> In p (m_vm_materialized md') ->
     page_allowedb B' p = true \/ In p P).

(* The residue plus 2 pages per secondary still queued is at most 2 pages per secondary freed so far. *)
Definition resid_inv_cf (B : list (Z * Z)) (md : Model) (q k : Z) : Prop :=
  nresid_cf B md + 2 * q <= 2 * k.

Lemma in_resid_cf : forall B md p,
  In p (resid_pg_cf B md) <-> In p (m_vm_materialized md) /\ page_allowedb B p = false.
Proof. intros B md p. unfold resid_pg_cf. rewrite filter_In, negb_true_iff. reflexivity. Qed.

Lemma nodup_resid_cf : forall B md, List.NoDup (m_vm_materialized md) -> List.NoDup (resid_pg_cf B md).
Proof. intros B md ND. unfold resid_pg_cf. apply NoDup_filter. exact ND. Qed.

Lemma resid_delta_cf : forall B B' P md md',
  List.NoDup (m_vm_materialized md') -> step_mat_in_cf B B' P md md' ->
  nresid_cf B' md' <= nresid_cf B md + Z.of_nat (length P).
Proof.
  intros B B' P md md' ND [H1 H2]. unfold nresid_cf.
  assert (HI : incl (resid_pg_cf B' md') (resid_pg_cf B md ++ P)).
  { intros p Hp. apply in_resid_cf in Hp as [Hin Hneg]. apply in_or_app.
    destruct (H1 p Hin) as [Hmd | [Hb | HP]].
    - destruct (page_allowedb B p) eqn:E.
      + destruct (H2 p E Hin) as [Hb' | HP]; [rewrite Hb' in Hneg; discriminate | right; exact HP].
      + left. apply in_resid_cf. split; [exact Hmd | exact E].
    - rewrite Hb in Hneg. discriminate.
    - right. exact HP. }
  pose proof (List.NoDup_incl_length (nodup_resid_cf B' md' ND) HI) as L.
  rewrite List.length_app in L. lia.
Qed.

Lemma resid_at_main_cf : forall B md,
  (forall p, In p (m_vm_materialized md) -> page_allowedb B p = true) -> nresid_cf B md = 0.
Proof.
  intros B md H. unfold nresid_cf, resid_pg_cf.
  assert (E : List.filter (fun p => negb (page_allowedb B p)) (m_vm_materialized md) = []).
  { induction (m_vm_materialized md) as [|x l IH]; [reflexivity|]. cbn [List.filter].
    rewrite (H x (or_introl eq_refl)). cbn [negb]. apply IH. intros p Hp. apply H. right. exact Hp. }
  rewrite E. reflexivity.
Qed.

Lemma resid_inv_at_main_cf : forall B md,
  (forall p, In p (m_vm_materialized md) -> page_allowedb B p = true) -> resid_inv_cf B md 0 0.
Proof. intros B md H. unfold resid_inv_cf. rewrite (resid_at_main_cf B md H). lia. Qed.

(* One step that frees f secondaries and adds the residue P, where each queued secondary that leaves pays 2 pages. *)
Lemma resid_inv_step_cf : forall B B' P md md' q q' k f,
  List.NoDup (m_vm_materialized md') -> step_mat_in_cf B B' P md md' ->
  0 <= f -> Z.of_nat (length P) + 2 * q' <= 2 * q + 2 * f ->
  resid_inv_cf B md q k -> resid_inv_cf B' md' q' (k + f).
Proof.
  intros B B' P md md' q q' k f ND HS Hf HP INV. unfold resid_inv_cf in *.
  pose proof (resid_delta_cf B B' P md md' ND HS) as D. lia.
Qed.

Lemma resid_inv_le_cf : forall B md q k, resid_inv_cf B md q k -> 0 <= q -> nresid_cf B md <= 2 * (k - q).
Proof. intros B md q k INV Hq. unfold resid_inv_cf in INV. lia. Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The count: the materialized pages are the base's pages plus the residue.  *)

Lemma length_filter_split : forall (f : word -> bool) (l : list word),
  length l = (length (List.filter f l) + length (List.filter (fun x => negb (f x)) l))%nat.
Proof. intros f l. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter]. destruct (f x); cbn; lia. Qed.

Lemma mat_count_cf : forall B md,
  A_wf B -> List.NoDup (m_vm_materialized md) ->
  (forall p, In p (m_vm_materialized md) -> bv_unsigned p mod page_size = 0) ->
  Z.of_nat (length (m_vm_materialized md)) * page_size <= A_bytes B + page_size * nresid_cf B md.
Proof.
  intros B md WF ND AL. unfold nresid_cf, resid_pg_cf.
  rewrite (length_filter_split (page_allowedb B) (m_vm_materialized md)).
  assert (IN : Z.of_nat (length (List.filter (page_allowedb B) (m_vm_materialized md))) * page_size <= A_bytes B).
  { apply allowed_pages_bound; [exact WF | apply NoDup_filter; exact ND | |].
    - intros p Hp. apply filter_In in Hp as [Hp _]. exact (AL p Hp).
    - intros p Hp. apply filter_In in Hp as [_ Hp]. exact Hp. }
  rewrite Nat2Z.inj_add. lia.
Qed.

Lemma mat_canon_of_resid_gen_cf : forall B md q k,
  A_wf B -> List.NoDup (m_vm_materialized md) ->
  (forall p, In p (m_vm_materialized md) -> bv_unsigned p mod page_size = 0) ->
  resid_inv_cf B md q k -> 0 <= q ->
  Z.of_nat (length (m_vm_materialized md)) * page_size <= A_bytes B + 2 * page_size * (k - q).
Proof.
  intros B md q k WF ND AL INV Hq.
  pose proof (mat_count_cf B md WF ND AL) as C. pose proof (resid_inv_le_cf B md q k INV Hq) as R.
  assert (page_size * nresid_cf B md <= page_size * (2 * (k - q))) by (apply Z.mul_le_mono_nonneg_l; [unfold page_size; lia | exact R]).
  lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The canonical base at cgif's allocator state, and Cker.                    *)

(* The whole primary reservation (it contains the space and its region-info page, layout_ok lo_space_in) and the
   pointer-array reservation, each with its shadow hull (cgif's shull rounding, YG0n.v:383). *)
Definition prim_rs_cf (ly : alayout) : list (Z * Z) :=
  [(ly_prim ly, ly_prim ly + kPrimResvSize); shull (ly_prim ly, kPrimResvSize)].
Definition ptr_rs_cf (ly : alayout) : list (Z * Z) :=
  [(ly_Q ly, ly_Q ly + kPtrArrayResv); shull (ly_Q ly, kPtrArrayResv)].

(* Every mapped secondary (live or queued: sec_extents reads st_chunks) with its shadow hull. *)
Definition sec_rs_cf (ly : alayout) (S : astate) : list (Z * Z) :=
  flat_map (fun e => [(fst e, fst e + snd e); shull e]) (sec_extents ly S).

(* A0: the at-main allowance (the cf layer's). *)
Definition base_cf (A0 : list (Z * Z)) (ly : alayout) (S : astate) : list (Z * Z) :=
  A0 ++ prim_rs_cf ly ++ ptr_rs_cf ly ++ sec_rs_cf ly S.

(* The secondaries freed and not yet evicted: the quarantined secondary chunks of st_chunks. Not q_items: a recycle
   evicts a chunk the drain already took out of the queue (YGcfInstRcSec.rc_sec_step_cf's premise
   ~ In (ck_beg k) (map ck_beg (q_items X))), so q_items drops before the eviction's two pages appear, while this
   count drops at the eviction itself (the chunk leaves st_chunks). Review 05:3xZ D2. *)
Definition is_qsec (k : chunk) : bool :=
  match ck_beg k, ck_state k with PSec _ _, CQuarantined => true | _, _ => false end.
Definition qsec_cf (S : astate) : Z := Z.of_nat (length (List.filter is_qsec (st_chunks S))).

(* The canonical allowance: the base's bytes and 2 pages per evicted secondary (nev = frees - queued). *)
Definition Cker (A0 : list (Z * Z)) (ly : alayout) (S : astate) (nev : Z) : Z :=
  A_bytes A0 + A_bytes (prim_rs_cf ly) + A_bytes (ptr_rs_cf ly) + A_bytes (sec_rs_cf ly S) + 2 * page_size * nev.

(* Closed bounds of the fixed reservations (no layout premise: shull's bytes are <= len / 8 + 8190 for any start). *)
Definition PRIM_SPACE_cf : Z := kPrimResvSize + kPrimResvSize / 8 + 8192.
Definition PTR_SPACE_cf : Z := kPtrArrayResv + kPtrArrayResv / 8 + 8192.

Lemma PRIM_SPACE_cf_val : PRIM_SPACE_cf = 154618909184.
Proof. vm_compute. reflexivity. Qed.
Lemma PTR_SPACE_cf_val : PTR_SPACE_cf = 9445376.
Proof. vm_compute. reflexivity. Qed.

Lemma A_bytes_app_cf : forall A1 A2, A_bytes (A1 ++ A2) = A_bytes A1 + A_bytes A2.
Proof. intros A1 A2. induction A1 as [|iv A1 IH]; cbn [app A_bytes]; [reflexivity | rewrite IH; lia]. Qed.

Lemma shull_bytes_le : forall lo len, snd (shull (lo, len)) - fst (shull (lo, len)) <= len / 8 + 8190.
Proof.
  intros lo len. unfold shull. cbn [fst snd].
  set (a := shadow_addr lo). set (b := len / 8).
  pose proof (Z.div_mod a 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound a 4096 ltac:(lia)) as B1.
  pose proof (Z.div_mod (a + b + 4095) 4096 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (a + b + 4095) 4096 ltac:(lia)) as B2.
  lia.
Qed.

Lemma prim_rs_bytes_le : forall ly, A_bytes (prim_rs_cf ly) <= PRIM_SPACE_cf.
Proof.
  intros ly. unfold prim_rs_cf, PRIM_SPACE_cf. cbn [A_bytes fst snd].
  pose proof (shull_bytes_le (ly_prim ly) kPrimResvSize). lia.
Qed.

Lemma ptr_rs_bytes_le : forall ly, A_bytes (ptr_rs_cf ly) <= PTR_SPACE_cf.
Proof.
  intros ly. unfold ptr_rs_cf, PTR_SPACE_cf. cbn [A_bytes fst snd].
  pose proof (shull_bytes_le (ly_Q ly) kPtrArrayResv). lia.
Qed.

Lemma sec_rs_bytes_le : forall ly S, A_bytes (sec_rs_cf ly S) <= sec_live_bytes S + sec_live_hulls S.
Proof.
  intros ly S. unfold sec_rs_cf, sec_extents, sec_live_bytes, sec_live_hulls.
  induction (st_chunks S) as [|k t IH]; [cbn; lia|].
  cbn [flat_map fold_right]. destruct (ck_beg k) as [| |r o|]; cbn [app]; try exact IH.
  cbn [flat_map app A_bytes fst snd].
  pose proof (shull_bytes_le (ly_sec ly r) (sec_map_size (ck_req k))) as H.
  pose proof (Z.le_max_r 0 (sec_map_size (ck_req k) / 8 + 8192)). lia.
Qed.

Lemma Cker_le : forall A0 ly S nev,
  Cker A0 ly S nev <= A_bytes A0 + PRIM_SPACE_cf + PTR_SPACE_cf + sec_live_bytes S + sec_live_hulls S + 2 * page_size * nev.
Proof.
  intros A0 ly S nev. unfold Cker.
  pose proof (prim_rs_bytes_le ly). pose proof (ptr_rs_bytes_le ly). pose proof (sec_rs_bytes_le ly S). lia.
Qed.

(* The base is well formed when A0 is and every secondary map is page aligned with a page-multiple size. *)
Lemma shull_wf : forall lo len, 0 <= len ->
  fst (shull (lo, len)) <= snd (shull (lo, len)) /\ fst (shull (lo, len)) mod page_size = 0 /\
  snd (shull (lo, len)) mod page_size = 0.
Proof.
  intros lo len Hl. pose proof (shull_bounds lo len Hl) as (B1 & B2 & B3 & B4).
  pose proof (Z.div_pos len 8 Hl ltac:(lia)). unfold page_size. repeat split; [lia | exact B3 | exact B4].
Qed.

Lemma base_cf_wf : forall A0 ly S,
  A_wf A0 -> ly_prim ly mod page_size = 0 -> ly_Q ly mod page_size = 0 ->
  Forall (fun e => fst e mod page_size = 0 /\ 0 <= snd e /\ snd e mod page_size = 0) (sec_extents ly S) ->
  A_wf (base_cf A0 ly S).
Proof.
  intros A0 ly S W0 HP HQ HS. unfold base_cf, A_wf in *.
  assert (KP : kPrimResvSize mod page_size = 0) by (vm_compute; reflexivity).
  assert (KQ : kPtrArrayResv mod page_size = 0) by (vm_compute; reflexivity).
  repeat (apply Forall_app; split); [exact W0 | | |].
  - unfold prim_rs_cf. pose proof (shull_wf (ly_prim ly) kPrimResvSize ltac:(unfold kPrimResvSize; lia)) as SH.
    repeat constructor; cbn [fst snd]; try (apply SH); unfold kPrimResvSize, page_size in *; try lia.
    rewrite Z.add_mod by lia. rewrite HP, KP. reflexivity.
  - unfold ptr_rs_cf. pose proof (shull_wf (ly_Q ly) kPtrArrayResv ltac:(unfold kPtrArrayResv; lia)) as SH.
    repeat constructor; cbn [fst snd]; try (apply SH); unfold kPtrArrayResv, page_size in *; try lia.
    rewrite Z.add_mod by lia. rewrite HQ, KQ. reflexivity.
  - unfold sec_rs_cf. apply Forall_forall. intros iv Hiv. apply in_flat_map in Hiv as (e & He & Hiv).
    pose proof (proj1 (Forall_forall _ _) HS e He) as (E1 & E2 & E3).
    destruct e as [lo len]. cbn [fst snd] in *. pose proof (shull_wf lo len E2) as SH.
    destruct Hiv as [<- | [<- | []]]; cbn [fst snd]; [| exact SH].
    split; [lia|]. split; [exact E1|]. rewrite Z.add_mod by (unfold page_size; lia). rewrite E1, E3. reflexivity.
Qed.

(* THE conclusion the cf room reads (a Theorem Labs lane's mat_canon_cf with C := Cker A0 ly S (k - qsec_cf S)). *)
Theorem mat_canon_of_resid_cf : forall A0 ly S md k,
  A_wf (base_cf A0 ly S) -> List.NoDup (m_vm_materialized md) ->
  (forall p, In p (m_vm_materialized md) -> bv_unsigned p mod page_size = 0) ->
  resid_inv_cf (base_cf A0 ly S) md (qsec_cf S) k ->
  Z.of_nat (length (m_vm_materialized md)) * page_size <= Cker A0 ly S (k - qsec_cf S).
Proof.
  intros A0 ly S md k WF ND AL INV.
  assert (Hq : 0 <= qsec_cf S) by (unfold qsec_cf; lia).
  pose proof (mat_canon_of_resid_gen_cf _ md _ k WF ND AL INV Hq) as H.
  unfold base_cf in H. rewrite !A_bytes_app_cf in H. unfold Cker.
  lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The secondary eviction: madvise of the hull's interior [sb, se), then munmap of the map [mb, mb + ms).   *)

Definition evict_model_cf (md : Model) (mb ms sb se : Z) : Model :=
  munmap_model (Z_to_bv 64 mb) (Z_to_bv 64 ms)
    (if sb <? se then madvise_dontneed_next md (Z_to_bv 64 sb) (Z_to_bv 64 (se - sb)) else md).

(* The two pages of the hull h the madvise leaves: its first page and the page at se. *)
Definition evict_edges_cf (h : Z * Z) (se : Z) : list word := [Z_to_bv 64 (fst h); Z_to_bv 64 se].

(* The base shrinks only by the evicted map and its hull. *)
Definition evict_shrink_cf (B B' : list (Z * Z)) (mb ms : Z) (h : Z * Z) : Prop :=
  forall p, page_allowedb B p = true -> page_allowedb B' p = false ->
    (mb <= bv_unsigned p /\ bv_unsigned p + page_size <= mb + ms) \/
    (fst h <= bv_unsigned p /\ bv_unsigned p + page_size <= snd h).

Lemma u64_cf : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

Lemma mat_evict_cf : forall md mb ms sb se p,
  0 <= mb -> 0 <= ms -> mb + ms < 2 ^ 64 -> (sb < se -> 0 <= sb /\ se < 2 ^ 64) ->
  In p (m_vm_materialized (evict_model_cf md mb ms sb se)) <->
  In p (m_vm_materialized md) /\ ~ (mb <= bv_unsigned p < mb + ms) /\ ~ (sb <= bv_unsigned p < se).
Proof.
  intros md mb ms sb se p Hmb Hms Hhi Hs. unfold evict_model_cf. rewrite munmap_materialized, filter_In.
  rewrite (u64_cf mb) by lia. rewrite (u64_cf ms) by lia.
  assert (O : forall lo hi, page_outside_range lo hi p = true <-> ~ (lo <= bv_unsigned p < hi)).
  { intros lo hi. unfold page_outside_range. rewrite negb_true_iff, andb_false_iff, Z.leb_gt, Z.ltb_ge. lia. }
  rewrite O. destruct (sb <? se) eqn:E.
  - apply Z.ltb_lt in E. destruct (Hs E) as [S0 S1].
    rewrite madvise_next_materialized, filter_In, O. rewrite (u64_cf sb) by lia. rewrite (u64_cf (se - sb)) by lia.
    replace (sb + (se - sb)) with se by lia. tauto.
  - apply Z.ltb_ge in E. split; [intros [H1 H2]; repeat split; [exact H1 | exact H2 | lia] | tauto].
Qed.

(* The eviction gives step_mat_in_cf with P = the two edge pages, when the madvise interval lies inside the hull
   up to one page at each end (fst h <= sb <= fst h + page_size, snd h <= se + page_size) and the materialized pages
   are page aligned. *)
Lemma resid_evict_cf : forall B B' md mb ms sb se (h : Z * Z),
  0 <= mb -> 0 <= ms -> mb + ms < 2 ^ 64 -> (sb < se -> 0 <= sb /\ se < 2 ^ 64) ->
  0 <= fst h -> fst h mod page_size = 0 -> fst h <= sb <= fst h + page_size -> snd h <= se + page_size ->
  0 <= se < 2 ^ 64 ->
  List.NoDup (m_vm_materialized md) ->
  (forall p, In p (m_vm_materialized md) -> bv_unsigned p mod page_size = 0) ->
  evict_shrink_cf B B' mb ms h ->
  List.NoDup (m_vm_materialized (evict_model_cf md mb ms sb se)) /\
  step_mat_in_cf B B' (evict_edges_cf h se) md (evict_model_cf md mb ms sb se).
Proof.
  intros B B' md mb ms sb se h Hmb Hms Hhi Hs H0 Hal Hsb Hse Hse0 ND AL SH.
  split.
  - unfold evict_model_cf. rewrite munmap_materialized. apply NoDup_filter.
    destruct (sb <? se); [rewrite madvise_next_materialized; apply NoDup_filter|]; exact ND.
  - split.
    + intros p Hp. left. apply (mat_evict_cf md mb ms sb se p Hmb Hms Hhi Hs) in Hp. exact (proj1 Hp).
    + intros p HB Hp. apply (mat_evict_cf md mb ms sb se p Hmb Hms Hhi Hs) in Hp as (Hin & Nm & Ns).
      destruct (page_allowedb B' p) eqn:E; [left; reflexivity | right].
      pose proof (AL p Hin) as Ap. pose proof (bv_unsigned_in_range 64 p) as Rp. unfold bv_modulus in Rp.
      destruct (SH p HB E) as [[M1 M2] | [M1 M2]].
      * exfalso. apply Nm. unfold page_size in M2. lia.
      * unfold evict_edges_cf. cbn [In].
        assert (Pz : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned p = z -> Z_to_bv 64 z = p).
        { intros z Hz Ez. apply bv_eq. rewrite (u64_cf z Hz). symmetry. exact Ez. }
        unfold page_size in *.
        destruct (Z_lt_le_dec (bv_unsigned p) sb) as [Lt | Ge].
        -- left. apply Pz; [lia|].
           pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)) as D1. pose proof (Z.div_mod (fst h) 4096 ltac:(lia)) as D2.
           rewrite Ap in D1. rewrite Hal in D2. lia.
        -- assert (se <= bv_unsigned p) by lia. right. left. apply Pz; [lia | lia].
Qed.

(* The base at the post state of a recycle: the post state may carry a rebuilt layout and a larger at-main part
   (review 05:3xZ D3), as long as the primary and pointer-array parts are the same and every other secondary is kept. *)
Lemma evict_base_cf : forall A0 A0' ly ly' S S' e,
  incl A0 A0' -> prim_rs_cf ly' = prim_rs_cf ly -> ptr_rs_cf ly' = ptr_rs_cf ly ->
  (forall e', In e' (sec_extents ly S) -> e' <> e -> In e' (sec_extents ly' S')) ->
  evict_shrink_cf (base_cf A0 ly S) (base_cf A0' ly' S') (fst e) (snd e) (shull e).
Proof.
  intros A0 A0' ly ly' S S' e HA HP HQ HK p HB HB'. unfold page_allowedb in HB, HB'.
  apply existsb_exists in HB as (iv & Hiv & Hb). apply andb_true_iff in Hb as [Hb1 Hb2].
  apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
  assert (NOT : ~ In iv (base_cf A0' ly' S')).
  { intros Hin. assert (T : existsb (fun iv0 => (fst iv0 <=? bv_unsigned p) && (bv_unsigned p + page_size <=? snd iv0))
                             (base_cf A0' ly' S') = true).
    { apply existsb_exists. exists iv. split; [exact Hin|]. apply andb_true_iff. split; apply Z.leb_le; assumption. }
    rewrite T in HB'. discriminate. }
  unfold base_cf in Hiv, NOT. rewrite !in_app_iff in Hiv, NOT. rewrite HP, HQ in NOT.
  destruct Hiv as [Hiv | [Hiv | [Hiv | Hiv]]].
  - exfalso. apply NOT. left. exact (HA iv Hiv).
  - exfalso. apply NOT. right. left. exact Hiv.
  - exfalso. apply NOT. right. right. left. exact Hiv.
  - unfold sec_rs_cf in Hiv. apply in_flat_map in Hiv as (e' & He' & Hiv).
    destruct (prod_eq_dec e' e) as [-> | Ne].
    + destruct Hiv as [<- | [<- | []]]; cbn [fst snd] in *; [left | right]; split; assumption.
    + exfalso. apply NOT. right. right. right.
      unfold sec_rs_cf. apply in_flat_map. exists e'. split; [exact (HK e' He' Ne) | exact Hiv].
Qed.

(* The recycle in resid_inv_cf form: the evicted secondary leaves the queue (q' = q - 1) and pays its two edge
   pages, no new free (f = 0). *)
Lemma resid_inv_evict_cf : forall B B' md mb ms sb se h q k,
  0 <= mb -> 0 <= ms -> mb + ms < 2 ^ 64 -> (sb < se -> 0 <= sb /\ se < 2 ^ 64) ->
  0 <= fst h -> fst h mod page_size = 0 -> fst h <= sb <= fst h + page_size -> snd h <= se + page_size ->
  0 <= se < 2 ^ 64 ->
  List.NoDup (m_vm_materialized md) ->
  (forall p, In p (m_vm_materialized md) -> bv_unsigned p mod page_size = 0) ->
  evict_shrink_cf B B' mb ms h ->
  resid_inv_cf B md q k -> resid_inv_cf B' (evict_model_cf md mb ms sb se) (q - 1) k.
Proof.
  intros B B' md mb ms sb se h q k Hmb Hms Hhi Hs H0 Hal Hsb Hse Hse0 ND AL SH INV.
  destruct (resid_evict_cf B B' md mb ms sb se h Hmb Hms Hhi Hs H0 Hal Hsb Hse Hse0 ND AL SH) as [ND' HS].
  replace k with (k + 0) by lia.
  apply (resid_inv_step_cf B B' (evict_edges_cf h se) md _ q (q - 1) k 0 ND' HS); [lia | cbn; lia | exact INV].
Qed.
