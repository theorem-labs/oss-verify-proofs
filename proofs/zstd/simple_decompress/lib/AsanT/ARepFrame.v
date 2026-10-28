(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode Tac InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ABytes ACanary AModelFacts ARep ALayout AHeapP ARepKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma get_cls_put_cls_eq : forall c r st, get_cls (put_cls c r st) c = r.
Proof. intros. unfold get_cls, put_cls, set_cls. cbn. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma get_cls_put_cls_ne : forall c c' r st, c' <> c -> get_cls (put_cls c r st) c' = get_cls st c'.
Proof. intros. unfold get_cls, put_cls, set_cls. cbn. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma get_cls_set_next : forall v st c, get_cls (set_next v st) c = get_cls st c. Proof. reflexivity. Qed.
Lemma get_cls_set_live : forall v st c, get_cls (set_live v st) c = get_cls st c. Proof. reflexivity. Qed.
Lemma max_count_eq : forall st st' c, a_cinit st' = a_cinit st -> max_count st' c = max_count st c.
Proof. intros st st' c E. unfold max_count. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Definition st_fast (st : astate) (c n cnt : Z) : astate :=
  set_next (N.succ (a_next st)) (set_live (<[ a_next st := CPrim c n ]> (a_live st))
    (put_cls c (cls_set_count (cnt - 1) (get_cls st c)) st)).

Lemma st_fast_fields : forall st c n cnt,
     a_space_beg (st_fast st c n cnt) = a_space_beg st /\ a_ptr_array (st_fast st c n cnt) = a_ptr_array st
  /\ a_nres (st_fast st c n cnt) = a_nres st /\ a_nsec (st_fast st c n cnt) = a_nsec st
  /\ a_cinit (st_fast st c n cnt) = a_cinit st
  /\ a_live (st_fast st c n cnt) = <[ a_next st := CPrim c n ]> (a_live st)
  /\ a_next (st_fast st c n cnt) = N.succ (a_next st)
  /\ a_qloc (st_fast st c n cnt) = a_qloc st /\ a_qloc_bytes (st_fast st c n cnt) = a_qloc_bytes st
  /\ a_qglob (st_fast st c n cnt) = a_qglob st /\ a_qglob_bytes (st_fast st c n cnt) = a_qglob_bytes st.
Proof. intros. repeat split; reflexivity. Qed.

Lemma st_fast_cls : forall st c n cnt c',
  get_cls (st_fast st c n cnt) c' = if c' =? c then cls_set_count (cnt - 1) (get_cls st c) else get_cls st c'.
Proof.
  intros. unfold st_fast. rewrite get_cls_set_next, get_cls_set_live.
  destruct (Z.eqb_spec c' c) as [->|NE]; [apply get_cls_put_cls_eq | apply get_cls_put_cls_ne; exact NE].
Qed.

Lemma st_fast_counters : forall st c n cnt c',
     c_mapped_user (get_cls (st_fast st c n cnt) c') = c_mapped_user (get_cls st c')
  /\ c_allocated_user (get_cls (st_fast st c n cnt) c') = c_allocated_user (get_cls st c')
  /\ c_num_freed (get_cls (st_fast st c n cnt) c') = c_num_freed (get_cls st c')
  /\ c_mapped_free_array (get_cls (st_fast st c n cnt) c') = c_mapped_free_array (get_cls st c')
  /\ c_count (get_cls (st_fast st c n cnt) c') = (if c' =? c then cnt - 1 else c_count (get_cls st c')).
Proof. intros. rewrite st_fast_cls. destruct (Z.eqb_spec c' c) as [->|NE]; repeat split; reflexivity. Qed.

Lemma st_fast_max_count : forall st c n cnt c', max_count (st_fast st c n cnt) c' = max_count st c'.
Proof. intros. apply max_count_eq. reflexivity. Qed.
Lemma st_fast_ndist : forall st c n cnt c', ndist (st_fast st c n cnt) c' = ndist st c'.
Proof. intros. unfold ndist. rewrite (proj1 (proj2 (st_fast_counters st c n cnt c'))). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma size_of_class_facts : forall c, 1 <= c < K_NUM_CLASSES ->
  16 <= size_of_class c <= 65536 /\ size_of_class c mod 16 = 0.
Proof.
  intros c Hc. unfold K_NUM_CLASSES in Hc.
  enough (B : (16 <=? size_of_class c) && (size_of_class c <=? 65536) && (size_of_class c mod 16 =? 0) = true).
  { apply andb_prop in B. destruct B as [B B3]. apply andb_prop in B. destruct B as [B1 B2].
    apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.eqb_eq in B3. lia. }
  assert (E : exists i, (0 <= i < 31)%nat /\ c = Z.of_nat i + 1).
  { exists (Z.to_nat (c - 1)). split; lia. }
  destruct E as (i & Hi & ->).
  do 31 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma shlen_div : forall d, shlen d = d / 8.
Proof. intros. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shad_div : forall a, shad a = a / 8 + ASHOFF.
Proof. intros. unfold shad. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.
Lemma shad_add : forall a d, a mod 8 = 0 -> shad (a + d) = shad a + d / 8.
Proof. intros a d H. rewrite !shad_div. Z.div_mod_to_equations. lia. Qed.
Lemma shad_add_shlen : forall a d, a mod 8 = 0 -> shad (a + d) = shad a + shlen d.
Proof. intros. rewrite shlen_div. apply shad_add. assumption. Qed.
(* [comment removed for export] *)
Lemma shad_sep : forall a1 n1 a2, a1 + n1 <= a2 -> a1 mod 8 = 0 -> shad a1 + shlen n1 <= shad a2.
Proof. intros a1 n1 a2 H M. rewrite !shad_div, shlen_div. Z.div_mod_to_equations. lia. Qed.
Lemma shlen_mono : forall a b, a <= b -> shlen a <= shlen b.
Proof. intros. rewrite !shlen_div. apply Z.div_le_mono; lia. Qed.
Lemma shlen_nonneg : forall a, 0 <= a -> 0 <= shlen a.
Proof. intros. rewrite shlen_div. apply Z.div_pos; lia. Qed.
Lemma shlen_mul8 : forall q, shlen (8 * q) = q.
Proof. intros. rewrite shlen_div. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.
Lemma granules_eq : forall n, 0 <= n -> granules n = shlen (n - n mod 8) + (if n mod 8 =? 0 then 0 else 1).
Proof. intros n H. unfold granules. rewrite !shlen_div. destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia. Qed.
Lemma shlen_floor : forall n, shlen (n - n mod 8) = shlen n.
Proof. intros n. rewrite !shlen_div. Z.div_mod_to_equations. lia. Qed.

Lemma aregion_mod : forall L c, al_space_beg L mod K_ALIGN = 0 -> aregion L c mod 65536 = 0.
Proof. intros L c H. unfold aregion, K_REGION, K_ALIGN in *. change (2^32) with (65536 * 65536). Z.div_mod_to_equations. lia. Qed.

Lemma regions_sep : forall L c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2.
Proof. intros L c1 c2 H. unfold aregion, K_REGION. nia. Qed.

Lemma slots_sep : forall L c k1 k2, 0 <= k1 -> k1 < k2 -> 0 <= size_of_class c ->
  aslot_addr L c k1 + size_of_class c <= aslot_addr L c k2.
Proof. intros L c k1 k2 H1 H2 HS. unfold aslot_addr. nia. Qed.

Lemma slots_disjoint : forall L c k1 k2, 0 <= k1 -> 0 <= k2 -> k1 <> k2 -> 0 <= size_of_class c ->
  aslot_addr L c k1 + size_of_class c <= aslot_addr L c k2 \/ aslot_addr L c k2 + size_of_class c <= aslot_addr L c k1.
Proof.
  intros L c k1 k2 H1 H2 NE HS. destruct (Z.lt_ge_cases k1 k2).
  - left. apply slots_sep; lia.
  - right. apply slots_sep; lia.
Qed.

(* [comment removed for export] *)
Lemma slot_in_region : forall L st c k, let r := get_cls st c in let S := size_of_class c in
  0 < S -> 0 <= c_allocated_user r -> 0 <= k < ndist st c ->
  aregion L c <= aslot_addr L c k /\ aslot_addr L c k + S <= aregion L c + c_allocated_user r /\ 0 <= k * S.
Proof.
  intros L st c k r S HS HA HK. unfold ndist in HK. subst r S. unfold aslot_addr.
  set (A := c_allocated_user (get_cls st c)) in *. set (S := size_of_class c) in *.
  assert (P0 : 0 <= k * S) by (apply Z.mul_nonneg_nonneg; lia).
  assert (M1 : (k + 1) * S <= A / S * S) by (apply Z.mul_le_mono_nonneg_r; lia).
  pose proof (Z.mul_div_le A S ltac:(lia)) as M2. rewrite Z.mul_comm in M2.
  split; [lia|]. split; [| exact P0]. rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. lia.
Qed.

Lemma slot_aligned : forall L c k, al_space_beg L mod K_ALIGN = 0 -> 1 <= c < K_NUM_CLASSES ->
  aslot_addr L c k mod 16 = 0.
Proof.
  intros L c k H Hc. pose proof (size_of_class_facts c Hc) as [_ M]. pose proof (aregion_mod L c H) as R.
  unfold aslot_addr. set (S := size_of_class c) in *. set (R0 := aregion L c) in *.
  replace (k * S) with ((k * (S / 16)) * 16) by (Z.div_mod_to_equations; nia).
  rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xcons (b : xbusy) (upd : Z -> xclass -> xclass) (X : aconc) : aconc :=
  mkAConc (fun c => if c =? xb_class b then upd c (x_cls X c) else x_cls X c) (b :: x_busy X).

Lemma busy_of_cons : forall b bs X c k,
  busy_of (mkAConc X (b :: bs)) c k =
    if (xb_class b =? c) && (xb_slot b =? k) then Some b else busy_of (mkAConc X bs) c k.
Proof. intros. unfold busy_of. cbn. destruct ((xb_class b =? c) && (xb_slot b =? k)); reflexivity. Qed.

Lemma busy_slots_cons : forall b bs X c,
  busy_slots (mkAConc X (b :: bs)) c = (if xb_class b =? c then [xb_slot b] else []) ++ busy_slots (mkAConc X bs) c.
Proof. intros. unfold busy_slots. cbn. destruct (xb_class b =? c); reflexivity. Qed.

Lemma busy_of_x_cls : forall X X' bs c k, busy_of (mkAConc X bs) c k = busy_of (mkAConc X' bs) c k.
Proof. reflexivity. Qed.
Lemma busy_slots_x_cls : forall X X' bs c, busy_slots (mkAConc X bs) c = busy_slots (mkAConc X' bs) c.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cache_split_last : forall (l : list Z) k,
  nth_error l (length l - 1) = Some k -> l = removelast l ++ [k].
Proof.
  intros l k H. destruct l as [|a l'] eqn:E; [cbn in H; discriminate|]. rewrite <- E in *.
  assert (NE : l <> []) by (subst; discriminate).
  rewrite (app_removelast_last k NE) at 1. f_equal. f_equal.
  rewrite (app_removelast_last k NE) in H.
  rewrite length_app in H. cbn [length] in H. rewrite nth_error_app2 in H by lia.
  replace (length (removelast l) + 1 - 1 - length (removelast l))%nat with 0%nat in H by lia. cbn in H. congruence.
Qed.

Lemma length_removelast : forall {A} (l : list A), l <> [] -> length (removelast l) = (length l - 1)%nat.
Proof.
  intros A l NE. induction l as [|a l IH]; [congruence|]. destruct l as [|b l'].
  - reflexivity.
  - cbn [removelast length]. cbn [removelast length] in IH. rewrite IH by discriminate. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
  disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2 H3; cbn in *; [exact I|].
  destruct H as [D H]. split; [lia|]. eapply IH; eauto.
Qed.

Lemma junk_frame : forall W m m' A n, junk_at m A n -> munch W m m' -> wmono bsegs m m' ->
  (0 < n -> disjoint_from W A n) -> junk_at m' A n.
Proof.
  intros W m m' A n [bs H] MU WM D. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transport; [exact H | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma fill_frame : forall W m m' A n v, fill_at m A n v -> munch W m m' -> wmono bsegs m m' ->
  (0 < n -> disjoint_from W A n) -> fill_at m' A n v.
Proof.
  intros W m m' A n v H MU WM D. unfold fill_at in *.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transport; [exact H | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - pose proof H as HH. destruct HH as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
    replace (Z.to_nat n) with 0%nat in * by lia. cbn [repeat] in *.
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma cells_frame : forall W m m' A cs, rw_cells bsegs m A cs -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells bsegs m' A cs.
Proof. intros. eapply rw_cells_transport; eauto. Qed.

Lemma u64arr_frame : forall W m m' A ws, u64arr bsegs m A ws -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr bsegs m' A ws.
Proof. intros. eapply u64arr_transport; eauto. Qed.
Lemma u32arr_frame : forall W m m' A ws, u32arr bsegs m A ws -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr bsegs m' A ws.
Proof. intros. eapply u32arr_transport; eauto. Qed.

(* [comment removed for export] *)
Lemma fill_cons : forall m A n v, 0 <= v < 256 -> 0 <= n ->
  rw_cells bsegs m A [C1 (Z_to_bv 8 v)] -> fill_at m (A + 1) n v -> fill_at m A (1 + n) v.
Proof.
  intros m A n v Hv Hn H1 H2. apply (fill_merge m A 1 n v); [| exact H2 | lia | lia].
  unfold fill_at. cbn [Z.to_nat Pos.to_nat repeat Pos.iter_op].
  eapply rw_cells_recast; [exact H1 | cbn; tauto | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma cb_app : forall m A n1 bs1 n2 bs2,
  rw_cells bsegs m A [CB n1 bs1] -> rw_cells bsegs m (A + Z.of_nat n1) [CB n2 bs2] ->
  rw_cells bsegs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
  intros m A n1 bs1 n2 bs2 H1 H2.
  assert (H : rw_cells bsegs m A ([CB n1 bs1] ++ [CB n2 bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
  pose proof (rw_cells_merge bsegs m A [] ([CB n1 bs1] ++ [CB n2 bs2]) []) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes app] in M.
  rewrite app_nil_r, Nat.add_0_r in M. exact M.
Qed.

Lemma cb_of_C1 : forall m A (b : byte), rw_cells bsegs m A [C1 b] -> rw_cells bsegs m A [CB 1 [b]].
Proof. intros m A b H. eapply rw_cells_recast; [exact H | cbn; tauto | reflexivity | reflexivity]. Qed.

Lemma cb_of_fill : forall m A n v, fill_at m A n v ->
  rw_cells bsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))].
Proof. intros m A n v H. exact H. Qed.

Lemma cb_nil : forall m A n bs, rw_cells bsegs m A [CB n bs] -> rw_cells bsegs m (A + Z.of_nat n) [CB 0 []].
Proof.
  intros m A n bs H. pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 _]]] [W0 [W1 _]]]. cbn in L, B1, W1.
  rewrite app_nil_r in B1. rewrite L in B1. rewrite Nat.add_0_r in W1.
  split; [split; [cbn; tauto|]|]; unfold bytes_at, wr_at; cbn.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Ltac dforall H :=
  lazymatch type of H with
  | Forall _ (_ :: _) => let A := fresh "D" in pose proof (Forall_inv H) as A; cbn [fst snd] in A;
                         apply Forall_inv_tail in H; dforall H
  | _ => clear H
  end.

Section CANSEC2. Context {rc : runConstT}.
Section Frames.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.

Ltac xcell := eapply cells_frame; [eassumption | exact MU | exact WM | cbn -[Z.add Z.mul]; assumption].

(* [comment removed for export] *)
Definition rt_hulls : list (Z * Z) :=
  [(0xc72e8, 8); (0xc72f8, 48); (0xc7328, 8); (0xc7e70, 8); (0xc7f60, 8); (0xc91b0, 16);
   (0xcd4b8, 13); (0xcd4f8, 20); (0xcd524, 12); (0xcd54d, 1); (0xcfcf8, 8); (0xcf55c, 1);
   (0xcf560, 1); (0xcf564, 4); (0xd09d8, 2); (0xd09e0, 24); (0xd09fc, 4); (0x151f60, 3);
   (0x15f7a0, 8); (0x1617c0, 16); (0x161848, 8); (0x16184a, 1); (0x1618a0, 8); (ATP88, 8); (ATSD, 8);
   (0x602cc0, 4); (al_ctx L + 8, 4); (al_ctx L + 152, 8)]%Z.

Lemma arep_rt_frame : arep_rt L m -> Forall (fun p => disjoint_from W (fst p) (snd p)) rt_hulls -> arep_rt L m'.
Proof.
  intros RT CLR. unfold rt_hulls in CLR. dforall CLR.
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18
                  & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28).
  unfold arep_rt. repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
Lemma arelro_frame : arelro m -> disjoint_from W ARELRO_LO (ARELRO_HI - ARELRO_LO) -> arelro m'.
Proof.
  intros R D i Hi. unfold arelro in R. rewrite <- (R i Hi).
  pose proof (MU (wa i)) as E. rewrite wa_unsigned in E by (unfold ARELRO_LO, ARELRO_HI in Hi; lia).
  apply E. eapply disjoint_outside; [exact D| lia].
Qed.

(* [comment removed for export] *)
Lemma azero_frame : forall A n, azero m A n -> munch W m m' -> wmono bsegs m m' ->
  (0 < n -> disjoint_from W A n) -> azero m' A n.
Proof.
  intros A n [Z0 WR] MU' WM' D. split.
  - intros i Hi. rewrite <- (Z0 i Hi). pose proof WR as (W0 & W1 & _).
    pose proof (MU' (wa (A + i))) as E. rewrite wa_unsigned in E by lia. apply E.
    eapply disjoint_outside; [apply D; lia | lia].
  - eapply wr_at_transport; [exact WR | exact WM'].
Qed.

Lemma ashadow_avail_frame : forall st st' c,
  ashadow_avail L st m c ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  (0 < shlen (K_FREEARR_OFF - c_mapped_user (get_cls st c)) ->
     disjoint_from W (shad (aregion L c + c_mapped_user (get_cls st c))) (shlen (K_FREEARR_OFF - c_mapped_user (get_cls st c)))) ->
  (0 < shlen (K_FREEARR_MAX - c_mapped_free_array (get_cls st c)) ->
     disjoint_from W (shad (afreearr L c + c_mapped_free_array (get_cls st c))) (shlen (K_FREEARR_MAX - c_mapped_free_array (get_cls st c)))) ->
  ashadow_avail L st' m' c.
Proof.
  intros st st' c [Z1 Z2] E1 E2 D1 D2. unfold ashadow_avail. cbv zeta. rewrite E1, E2.
  split; [eapply azero_frame; [exact Z1 | exact MU | exact WM | exact D1] | eapply azero_frame; [exact Z2 | exact MU | exact WM | exact D2]].
Qed.

Lemma arep_rt2_frame : arep_rt2 m -> disjoint_from W 0x16192c 1 -> disjoint_from W 0x1618b8 8 -> disjoint_from W 0xc9160 8 -> arep_rt2 m'.
Proof. intros (R1 & R2 & R3) D1 D2 D3. split; [xcell|]. split; xcell. Qed.

(* [comment removed for export] *)
Definition rt3_hulls : list (Z * Z) :=
  [(0xc90a8, 16); (0xc9088, 8); (0xc9090, 8); (0xc9160, 8); (0xc9078, 8); (0x161878, 8); (0x161920, 8);
   (0xcfd00, 4); (0xcd558, 1); (0x15f798, 4);
   (0xc72e8, 16); (0xc91f0, 8); (0x15f7a0, 8); (0x161900, 8); (0x161918, 8); (0x622f70, 8)]%Z.   (* [comment removed for export] *)
Lemma arep_rt3_frame : arep_rt3 m -> Forall (fun p => disjoint_from W (fst p) (snd p)) rt3_hulls -> arep_rt3 m'.
Proof.
  intros RT CLR. unfold rt3_hulls in CLR. dforall CLR.
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17).
  unfold arep_rt3. repeat lazymatch goal with |- _ /\ _ => split end; first [apply premap_canary_any | xcell].
Qed.

(* [comment removed for export] *)
Lemma ainstance_frame : forall st st',
  ainstance L st m -> a_nres st' = a_nres st -> a_nsec st' = a_nsec st ->
  disjoint_from W (AINSTANCE + 32) 96 -> disjoint_from W (AINSTANCE + 680) 1 -> disjoint_from W (AINSTANCE + 984) 1 ->
  ainstance L st' m'.
Proof.
  intros st st' (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9) E1 E2 D1 D2 D3. unfold ainstance. rewrite E1, E2.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 40) 4 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Df.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 56) 1 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dg.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 32) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 48) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 64) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 72) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 112) 16 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
Lemma aregion_cells_frame : forall st st' c,
  aregion_cells L st m c ->
  c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  disjoint_from W (aregion_info L c) 128 ->
  aregion_cells L st' m' c.
Proof.
  intros st st' c RC E1 E2 E3 E4 D. unfold aregion_cells in *. cbv zeta in *. rewrite E1, E2, E3, E4.
  destruct RC as (A1 & A2 & A3 & A4 & A5).
  pose proof (disjoint_from_sub W _ _ (aregion_info L c) 16 D ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 16) 48 D ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 64) 4 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 68) 1 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 72) 56 D ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  split; [xcell|]. split; [xcell|]. split; [eapply junk_frame; [exact A3 | exact MU | exact WM | intros _; exact Dc]|].
  split; [xcell|]. eapply junk_frame; [exact A5 | exact MU | exact WM | intros _; exact De].
Qed.

(* [comment removed for export] *)
Lemma afreearray_frame : forall st st' X X' c,
  afreearray L st X m c ->
  c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
  c_mapped_free_array (get_cls st' c) = c_mapped_free_array (get_cls st c) ->
  xc_free (x_cls X' c) = xc_free (x_cls X c) ->
  Z.of_nat (length (xc_free (x_cls X c))) = c_num_freed (get_cls st c) -> 0 <= c_num_freed (get_cls st c) ->
  disjoint_from W (afreearr L c) (c_mapped_free_array (get_cls st c)) ->
  4 * c_num_freed (get_cls st c) <= c_mapped_free_array (get_cls st c) ->
  disjoint_from W (shad (afreearr L c)) (shlen (c_mapped_free_array (get_cls st c))) ->
  afreearray L st' X' m' c.
Proof.
  intros st st' X X' c FA E1 E2 E3 LEN POS D LE DS. unfold afreearray in *. cbv zeta in *. rewrite E1, E2, E3.
  destruct FA as (A1 & A2 & A3).
  split; [| split].
  - eapply u32arr_frame; [exact A1 | exact MU | exact WM |]. rewrite length_map.
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frame; [exact A2 | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frame; [exact A3 | exact MU | exact WM | intros _; exact DS].
Qed.

(* [comment removed for export] *)
Lemma acache_cells_frame : forall st st' X X' c,
  acache_cells L st X m c ->
  c_count (get_cls st' c) = c_count (get_cls st c) -> a_cinit st' = a_cinit st ->
  xc_cache (x_cls X' c) = xc_cache (x_cls X c) ->
  disjoint_from W (acache_addr L c) 80 ->
  acache_cells L st' X' m' c.
Proof.
  intros st st' X X' c [tail (A1 & A2 & A3)] E1 E2 E3 D. unfold acache_cells. cbv zeta.
  rewrite E1, E3, (max_count_eq st st' c E2), E2. exists tail.
  split; [| split; [| exact A3]].
  - eapply cells_frame; [exact A1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
    eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply u32arr_frame; [exact A2 | exact MU | exact WM |]. rewrite length_app, length_map.
    eapply disjoint_from_sub; [exact D | unfold acache_addr; lia | lia | lia].
Qed.

(* [comment removed for export] *)
Definition xb_fits (b : xbusy) : Prop :=
  match xb_st b with
  | BBatch => True
  | _ => 0 <= xb_n b /\ 16 <= rz_size (xb_n b) /\ rz_size (xb_n b) + xb_n b <= size_of_class (xb_class b)
  end.

Lemma aslot_busy_frame : forall b,
  aslot_busy L m b -> xb_fits b ->
  disjoint_from W (xb_alloc L b) (size_of_class (xb_class b)) ->
  aslot_busy L m' b.
Proof.
  intros b SB FIT D. unfold aslot_busy, xb_fits in *. cbv zeta in *. unfold xb_hdr, xb_user in *.
  set (AB := xb_alloc L b) in *. set (S := size_of_class (xb_class b)) in *. set (n := xb_n b) in *. set (rz := rz_size n) in *.
  destruct (xb_st b).
  - destruct FIT as (N & RZ & FIT). destruct SB as (LH & [stb [E HDR]] & UJ). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frame; [exact LC | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frame; [exact J | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frame; [exact HDR | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frame; [exact UJ | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - destruct FIT as (N & RZ & FIT). destruct SB as (LH & [stb [E HDR]] & UJ). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frame; [exact LC | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | lia | lia | lia].
      * eapply junk_frame; [exact J | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + exists stb. split; [exact E|]. eapply cells_frame; [exact HDR | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D | lia | lia | lia].
    + eapply junk_frame; [exact UJ | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frame; [exact SB | exact MU | exact WM | intros _; exact D].
Qed.

(* [comment removed for export] *)
Lemma aslots_update : forall st st' X X' c k0,
  aslots L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c -> k <> k0 ->
       busy_of X' c k = busy_of X c k /\ disjoint_from W (aslot_addr L c k) (size_of_class c)
    /\ (forall b, busy_of X c k = Some b -> xb_class b = c /\ xb_slot b = k /\ xb_fits b)) ->
  (0 < c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c) ->
   disjoint_from W (aregion L c + c_allocated_user (get_cls st c)) (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c))) ->
  (0 <= k0 < ndist st c ->
     match busy_of X' c k0 with None => junk_at m' (aslot_addr L c k0) (size_of_class c) | Some b => aslot_busy L m' b end) ->
  aslots L st' X' m' c.
Proof.
  intros st st' X X' c k0 [SL UND] E0 E1 E2 OTH DU NEW. unfold aslots. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (Z.eq_dec k k0) as [->|NE]; [exact (NEW Hk)|].
    destruct (OTH k Hk NE) as (EB & D & WFB). rewrite EB. specialize (SL k Hk).
    destruct (busy_of X c k) as [b|].
    + destruct (WFB b eq_refl) as (C1' & K1 & FIT1).
      eapply aslot_busy_frame; [exact SL | exact FIT1 |].
      unfold xb_alloc. rewrite C1', K1. exact D.
    + eapply junk_frame; [exact SL | exact MU | exact WM | intros _; exact D].
  - eapply junk_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.

(* [comment removed for export] *)
Lemma aslot_shadow_update : forall st st' X X' c k0,
  aslot_shadow L st X m c ->
  ndist st' c = ndist st c ->
  c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
  c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
  (forall k, 0 <= k < ndist st c -> k <> k0 ->
       busy_of X' c k = busy_of X c k /\ disjoint_from W (shad (aslot_addr L c k)) (shlen (size_of_class c))) ->
  (0 < shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)) ->
   disjoint_from W (shad (aregion L c + c_allocated_user (get_cls st c))) (shlen (c_mapped_user (get_cls st c) - c_allocated_user (get_cls st c)))) ->
  (0 <= k0 < ndist st c ->
     rw_cells bsegs m' (shad (aslot_addr L c k0)) [CB (Z.to_nat (shlen (size_of_class c))) (slot_shadow_bytes (size_of_class c) (busy_of X' c k0))]) ->
  0 <= shlen (size_of_class c) ->
  aslot_shadow L st' X' m' c.
Proof.
  intros st st' X X' c k0 [SL UND] E0 E1 E2 OTH DU NEW POS. unfold aslot_shadow. cbv zeta. rewrite E0, E1, E2. split.
  - intros k Hk. destruct (Z.eq_dec k k0) as [->|NE]; [exact (NEW Hk)|].
    destruct (OTH k Hk NE) as [EB D]. rewrite EB. specialize (SL k Hk).
    eapply cells_frame; [exact SL | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact POS. exact D.
  - eapply fill_frame; [exact UND | exact MU | exact WM | exact DU].
Qed.
End Frames.

(* [comment removed for export] *)
Lemma azero_cb : forall m A n k, azero m A n -> 0 <= k <= n ->
  rw_cells bsegs m A [CB (Z.to_nat k) (repeat (Z_to_bv 8 0) (Z.to_nat k))].
Proof.
  intros m A n k [Z0 (W0 & W1 & WR)] Hk. split; [split|].
  - cbn. split; [apply repeat_length| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. rewrite repeat_length. split; [lia|].
    intros i Hi. unfold mrd. rewrite Z0 by lia. symmetry. apply nth_error_repeat. exact Hi.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros i Hi. apply WR. lia.
Qed.
Lemma azero_split : forall m A n k, azero m A n -> 0 <= k <= n -> azero m (A + k) (n - k).
Proof.
  intros m A n k [Z0 (W0 & W1 & WR)] Hk. split.
  - intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply Z0. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply WR. lia.
Qed.

(* [comment removed for export] *)
Lemma busy_of_Some_facts : forall X c k b, busy_of X c k = Some b -> In b (x_busy X) /\ xb_class b = c /\ xb_slot b = k.
Proof.
  intros X c k b Hb. unfold busy_of in Hb. apply find_some in Hb. destruct Hb as [HIn HP].
  apply andb_true_iff in HP. destruct HP as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.

Lemma rz_size_ge16 : forall n, 16 <= rz_size n.
Proof.
  intros n. rewrite rz_size_eq. assert (0 <= rz_log n) by (unfold rz_log; repeat (destruct (_ <=? _)); lia).
  assert (1 <= 2 ^ rz_log n) by (apply Z.pow_le_mono_r with (a := 2) in H; [| lia]; rewrite Z.pow_0_r in H; lia). lia.
Qed.

Lemma rounded_size_ge : forall n, n <= rounded_size n.
Proof. intros n. rewrite rounded_size_eq. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma awf_fits : forall L st X b, awf L st X -> In b (x_busy X) -> xb_fits b.
Proof.
  intros L st X b WF Hb. destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY b Hb) as [_ M]. unfold xb_fits.
  pose proof (rz_size_ge16 (xb_n b)) as R. pose proof (rounded_size_ge (xb_n b)) as RS.
  destruct (xb_st b); [| | exact I]; destruct M as (N & FIT & _); (split; [clear -N; lia|]); split; clear -R RS FIT; lia.
Qed.

Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. rewrite !shad_div. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

Lemma mod16_of_class : forall a s, a mod s = 0 -> s mod 16 = 0 -> 0 < s -> a mod 8 = 0.
Proof.
  intros a s H1 H2 Hs. apply Z.mod_divide in H1; [|lia]. apply Z.mod_divide in H2; [|lia]. apply Z.mod_divide; [lia|].
  eapply Z.divide_trans; [| exact H1]. eapply Z.divide_trans; [| exact H2]. exists 2. reflexivity.
Qed.

End CANSEC2.
(* [comment removed for export] *)
