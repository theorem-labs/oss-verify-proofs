(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode Tac InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase ABytes ACanary AModelFacts ARep ALayout AHeapP ARepKit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma get_cls_put_cls_eq : forall c r st, get_cls (put_cls c r st) c = r.
Proof. intros. unfold get_cls, put_cls, set_cls. cbn. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma get_cls_put_cls_ne : forall c c' r st, c' <> c -> get_cls (put_cls c r st) c' = get_cls st c'.
Proof. intros. unfold get_cls, put_cls, set_cls. cbn. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma get_cls_set_next : forall v st c, get_cls (set_next v st) c = get_cls st c. Proof. reflexivity. Qed.
#[using="Type"] Lemma get_cls_set_live : forall v st c, get_cls (set_live v st) c = get_cls st c. Proof. reflexivity. Qed.
#[using="Type"] Lemma max_count_eq : forall st st' c, a_cinit st' = a_cinit st -> max_count st' c = max_count st c.
Proof. intros st st' c E. unfold max_count. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Definition st_fast (st : astate) (c n cnt : Z) : astate :=
  set_next (N.succ (a_next st)) (set_live (<[ a_next st := CPrim c n ]> (a_live st))
    (put_cls c (cls_set_count (cnt - 1) (get_cls st c)) st)).

#[using="Type"] Lemma st_fast_fields : forall st c n cnt,
     a_space_beg (st_fast st c n cnt) = a_space_beg st /\ a_ptr_array (st_fast st c n cnt) = a_ptr_array st
  /\ a_nres (st_fast st c n cnt) = a_nres st /\ a_nsec (st_fast st c n cnt) = a_nsec st
  /\ a_cinit (st_fast st c n cnt) = a_cinit st
  /\ a_live (st_fast st c n cnt) = <[ a_next st := CPrim c n ]> (a_live st)
  /\ a_next (st_fast st c n cnt) = N.succ (a_next st)
  /\ a_qloc (st_fast st c n cnt) = a_qloc st /\ a_qloc_bytes (st_fast st c n cnt) = a_qloc_bytes st
  /\ a_qglob (st_fast st c n cnt) = a_qglob st /\ a_qglob_bytes (st_fast st c n cnt) = a_qglob_bytes st.
Proof. intros. repeat split; reflexivity. Qed.

#[using="Type"] Lemma st_fast_cls : forall st c n cnt c',
  get_cls (st_fast st c n cnt) c' = if c' =? c then cls_set_count (cnt - 1) (get_cls st c) else get_cls st c'.
Proof.
  intros. unfold st_fast. rewrite get_cls_set_next, get_cls_set_live.
  destruct (Z.eqb_spec c' c) as [->|NE]; [apply get_cls_put_cls_eq | apply get_cls_put_cls_ne; exact NE].
Qed.

#[using="Type"] Lemma st_fast_counters : forall st c n cnt c',
     c_mapped_user (get_cls (st_fast st c n cnt) c') = c_mapped_user (get_cls st c')
  /\ c_allocated_user (get_cls (st_fast st c n cnt) c') = c_allocated_user (get_cls st c')
  /\ c_num_freed (get_cls (st_fast st c n cnt) c') = c_num_freed (get_cls st c')
  /\ c_mapped_free_array (get_cls (st_fast st c n cnt) c') = c_mapped_free_array (get_cls st c')
  /\ c_count (get_cls (st_fast st c n cnt) c') = (if c' =? c then cnt - 1 else c_count (get_cls st c')).
Proof. intros. rewrite st_fast_cls. destruct (Z.eqb_spec c' c) as [->|NE]; repeat split; reflexivity. Qed.

#[using="Type"] Lemma st_fast_max_count : forall st c n cnt c', max_count (st_fast st c n cnt) c' = max_count st c'.
Proof. intros. apply max_count_eq. reflexivity. Qed.
#[using="Type"] Lemma st_fast_ndist : forall st c n cnt c', ndist (st_fast st c n cnt) c' = ndist st c'.
Proof. intros. unfold ndist. rewrite (proj1 (proj2 (st_fast_counters st c n cnt c'))). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma size_of_class_facts : forall c, 1 <= c < K_NUM_CLASSES ->
  16 <= size_of_class c <= 65536 /\ size_of_class c mod 16 = 0.
Proof.
  intros c Hc. unfold K_NUM_CLASSES in Hc.
  enough (B : (16 <=? size_of_class c) && (size_of_class c <=? 65536) && (size_of_class c mod 16 =? 0) = true).
  { apply andb_prop in B. destruct B as [B B3]. apply andb_prop in B. destruct B as [B1 B2].
    apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.eqb_eq in B3. Local Ltac2 Set LiaHints.tbl := fun () => "0040=28566435596.450690068739.359377706216.664638636135.300000700;00E00IS2Hc2HiS2HcS2B12B22B3S2Hc".
lia. }
  assert (E : exists i, (0 <= i < 31)%nat /\ c = Z.of_nat i + 1).
  { exists (Z.to_nat (c - 1)). split; lia. }
  destruct E as (i & Hi & ->).
  do 31 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma shlen_div : forall d, shlen d = d / 8.
Proof. intros. unfold shlen. Local Ltac2 Set LiaHints.tbl := fun () => "0010=29781772426.2000001S".
rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shad_div : forall a, shad a = a / 8 + ASHOFF.
Proof. intros. unfold shad. Local Ltac2 Set LiaHints.tbl := fun () => "0020=10124398177.229781691149.2000001002SS".
rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shad_add : forall a d, a mod 8 = 0 -> shad (a + d) = shad a + d / 8.
Proof. intros a d H. rewrite !shad_div. Local Ltac2 Set LiaHints.tbl := fun () => "0010=33033167587.4000003S1H".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shad_add_shlen : forall a d, a mod 8 = 0 -> shad (a + d) = shad a + shlen d.
Proof. intros. rewrite shlen_div. apply shad_add. assumption. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma shad_sep : forall a1 n1 a2, a1 + n1 <= a2 -> a1 mod 8 = 0 -> shad a1 + shlen n1 <= shad a2.
Proof. intros a1 n1 a2 H M. rewrite !shad_div, shlen_div. Local Ltac2 Set LiaHints.tbl := fun () => "0010=38101617581.6000005S1H1M".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shlen_mono : forall a b, a <= b -> shlen a <= shlen b.
Proof. intros. rewrite !shlen_div. apply Z.div_le_mono; lia. Qed.
#[using="Type"] Lemma shlen_nonneg : forall a, 0 <= a -> 0 <= shlen a.
Proof. intros. rewrite shlen_div. apply Z.div_pos; lia. Qed.
#[using="Type"] Lemma shlen_mul8 : forall q, shlen (8 * q) = q.
Proof. intros. rewrite shlen_div. Local Ltac2 Set LiaHints.tbl := fun () => "0010=61034932151.2000001S".
rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma granules_eq : forall n, 0 <= n -> granules n = shlen (n - n mod 8) + (if n mod 8 =? 0 then 0 else 1).
Proof. intros n H. unfold granules. rewrite !shlen_div. Local Ltac2 Set LiaHints.tbl := fun () => "0020=36439401513.449560089866.4000003007S1eS2n0".
destruct (Z.eqb_spec (n mod 8) 0); OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shlen_floor : forall n, shlen (n - n mod 8) = shlen n.
Proof. intros n. rewrite !shlen_div. Local Ltac2 Set LiaHints.tbl := fun () => "0010=33387702357.2000001S".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma aregion_mod : forall L c, al_space_beg L mod K_ALIGN = 0 -> aregion L c mod 65536 = 0.
Proof. intros L c H. unfold aregion, K_REGION, K_ALIGN in *. change (2^32) with (65536 * 65536). Local Ltac2 Set LiaHints.tbl := fun () => "0010=42130722670.4000003S1H".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma regions_sep : forall L c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2.
Proof. intros L c1 c2 H. unfold aregion, K_REGION. nia. Qed.

#[using="Type"] Lemma slots_sep : forall L c k1 k2, 0 <= k1 -> k1 < k2 -> 0 <= size_of_class c ->
  aslot_addr L c k1 + size_of_class c <= aslot_addr L c k2.
Proof. intros L c k1 k2 H1 H2 HS. unfold aslot_addr. nia. Qed.

#[using="Type"] Lemma slots_disjoint : forall L c k1 k2, 0 <= k1 -> 0 <= k2 -> k1 <> k2 -> 0 <= size_of_class c ->
  aslot_addr L c k1 + size_of_class c <= aslot_addr L c k2 \/ aslot_addr L c k2 + size_of_class c <= aslot_addr L c k1.
Proof.
  intros L c k1 k2 H1 H2 NE HS. destruct (Z.lt_ge_cases k1 k2).
  - left. apply slots_sep; lia.
  - right. apply slots_sep; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_in_region : forall L st c k, let r := get_cls st c in let S := size_of_class c in
  0 < S -> 0 <= c_allocated_user r -> 0 <= k < ndist st c ->
  aregion L c <= aslot_addr L c k /\ aslot_addr L c k + S <= aregion L c + c_allocated_user r /\ 0 <= k * S.
Proof.
  intros L st c k r S HS HA HK. unfold ndist in HK. subst r S. unfold aslot_addr.
  set (A := c_allocated_user (get_cls st c)) in *. set (S := size_of_class c) in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "0070>35822748441.1347385638455.1151794595714.1056760250468.139689993751.11 9690338196.12 9690393770.10 00000700;00?00C00G00K00OS2M12M2S2HKS2HKS2P0S2HSS2HSS2HS".
assert (P0 : 0 <= k * S) by (apply Z.mul_nonneg_nonneg; lia).
  assert (M1 : (k + 1) * S <= A / S * S) by (apply Z.mul_le_mono_nonneg_r; lia).
  pose proof (Z.mul_div_le A S ltac:(lia)) as M2. rewrite Z.mul_comm in M2.
  split; [lia|]. split; [| exact P0]. rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma slot_aligned : forall L c k, al_space_beg L mod K_ALIGN = 0 -> 1 <= c < K_NUM_CLASSES ->
  aslot_addr L c k mod 16 = 0.
Proof.
  intros L c k H Hc. pose proof (size_of_class_facts c Hc) as [_ M]. pose proof (aregion_mod L c H) as R.
  unfold aslot_addr. set (S := size_of_class c) in *. set (R0 := aregion L c) in *.
  replace (k * S) with ((k * (S / 16)) * 16) by (Z.div_mod_to_equations; nia).
  Local Ltac2 Set LiaHints.tbl := fun () => "0020>22560535091.1024897047766.10000005006S1H1RS".
rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xcons (b : xbusy) (upd : Z -> xclass -> xclass) (X : aconc) : aconc :=
  mkAConc (fun c => if c =? xb_class b then upd c (x_cls X c) else x_cls X c) (b :: x_busy X).

#[using="Type"] Lemma busy_of_cons : forall b bs X c k,
  busy_of (mkAConc X (b :: bs)) c k =
    if (xb_class b =? c) && (xb_slot b =? k) then Some b else busy_of (mkAConc X bs) c k.
Proof. intros. unfold busy_of. cbn. destruct ((xb_class b =? c) && (xb_slot b =? k)); reflexivity. Qed.

#[using="Type"] Lemma busy_slots_cons : forall b bs X c,
  busy_slots (mkAConc X (b :: bs)) c = (if xb_class b =? c then [xb_slot b] else []) ++ busy_slots (mkAConc X bs) c.
Proof. intros. unfold busy_slots. cbn. destruct (xb_class b =? c); reflexivity. Qed.

#[using="Type"] Lemma busy_of_x_cls : forall X X' bs c k, busy_of (mkAConc X bs) c k = busy_of (mkAConc X' bs) c k.
Proof. reflexivity. Qed.
#[using="Type"] Lemma busy_slots_x_cls : forall X X' bs c, busy_slots (mkAConc X bs) c = busy_slots (mkAConc X' bs) c.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cache_split_last : forall (l : list Z) k,
  nth_error l (length l - 1) = Some k -> l = removelast l ++ [k].
Proof.
  intros l k H. destruct l as [|a l'] eqn:E; [cbn in H; discriminate|]. rewrite <- E in *.
  assert (NE : l <> []) by (subst; discriminate).
  rewrite (app_removelast_last k NE) at 1. f_equal. f_equal.
  rewrite (app_removelast_last k NE) in H.
  rewrite length_app in H. cbn [length] in H. Local Ltac2 Set LiaHints.tbl := fun () => "0020=30581536076.848892750891.8000001002SS".
rewrite nth_error_app2 in H by lia.
  replace (length (removelast l) + 1 - 1 - length (removelast l))%nat with 0%nat in H by lia. cbn in H. congruence.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma length_removelast : forall {A} (l : list A), l <> [] -> length (removelast l) = (length l - 1)%nat.
Proof.
  intros A l NE. induction l as [|a l IH]; [congruence|]. destruct l as [|b l'].
  - reflexivity.
  - cbn [removelast length]. cbn [removelast length] in IH. rewrite IH by discriminate. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010=23308752414.7000001S".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
  disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2 H3; cbn in *; [exact I|].
  destruct H as [D H]. Local Ltac2 Set LiaHints.tbl := fun () => "0010=1540107796.14000009S1D2H12H2".
split; [lia|]. eapply IH; eauto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma junk_frame : forall W m m' A n, junk_at m A n -> munch W m m' -> wmono bsegs m m' ->
  (0 < n -> disjoint_from W A n) -> junk_at m' A n.
Proof.
  intros W m m' A n [bs H] MU WM D. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transport; [exact H | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    Local Ltac2 Set LiaHints.tbl := fun () => "0080>1312051727.18 14229248646.2020742173918.202424953696.19 24931798969.1840669651581.1859647939808.1868686216788.2000000600?00H00Q00Z00c00l018S1L2W1S1L2W12H0S1L2W12HiS1L2W12H0S1L2B02W1S1L2W12H0S1L2W12H0S1L2W12H02Hi".
rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma fill_frame : forall W m m' A n v, fill_at m A n v -> munch W m m' -> wmono bsegs m m' ->
  (0 < n -> disjoint_from W A n) -> fill_at m' A n v.
Proof.
  intros W m m' A n v H MU WM D. unfold fill_at in *.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transport; [exact H | exact MU | exact WM |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    Local Ltac2 Set LiaHints.tbl := fun () => "0070>20742173918.2123121635500.192424953696.12 24931663515.1925166272120.1940669959007.1968686216788.2100000700;00?00F00O00S00ZS2W12HiS2W1S2H0S2B02W1S2H01L2W1S2W1S2W12Hi".
rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - pose proof H as HH. destruct HH as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
    replace (Z.to_nat n) with 0%nat in * by lia. cbn [repeat] in *.
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma cells_frame : forall W m m' A cs, rw_cells bsegs m A cs -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells bsegs m' A cs.
Proof. intros. eapply rw_cells_transport; eauto. Qed.

#[using="Type"] Lemma u64arr_frame : forall W m m' A ws, u64arr bsegs m A ws -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr bsegs m' A ws.
Proof. intros. eapply u64arr_transport; eauto. Qed.
#[using="Type"] Lemma u32arr_frame : forall W m m' A ws, u32arr bsegs m A ws -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr bsegs m' A ws.
Proof. intros. eapply u32arr_transport; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fill_cons : forall m A n v, 0 <= v < 256 -> 0 <= n ->
  rw_cells bsegs m A [C1 (Z_to_bv 8 v)] -> fill_at m (A + 1) n v -> fill_at m A (1 + n) v.
Proof.
  intros m A n v Hv Hn H1 H2. apply (fill_merge m A 1 n v); [| exact H2 | lia | lia].
  unfold fill_at. cbn [Z.to_nat Pos.to_nat repeat Pos.iter_op].
  eapply rw_cells_recast; [exact H1 | cbn; tauto | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cb_app : forall m A n1 bs1 n2 bs2,
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

#[using="Type"] Lemma cb_of_C1 : forall m A (b : byte), rw_cells bsegs m A [C1 b] -> rw_cells bsegs m A [CB 1 [b]].
Proof. intros m A b H. eapply rw_cells_recast; [exact H | cbn; tauto | reflexivity | reflexivity]. Qed.

#[using="Type"] Lemma cb_of_fill : forall m A n v, fill_at m A n v ->
  rw_cells bsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))].
Proof. intros m A n v H. exact H. Qed.

#[using="Type"] Lemma cb_nil : forall m A n bs, rw_cells bsegs m A [CB n bs] -> rw_cells bsegs m (A + Z.of_nat n) [CB 0 []].
Proof.
  intros m A n bs H. pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 _]]] [W0 [W1 _]]]. cbn in L, B1, W1.
  rewrite app_nil_r in B1. rewrite L in B1. rewrite Nat.add_0_r in W1.
  split; [split; [cbn; tauto|]|]; unfold bytes_at, wr_at; cbn.
  - Local Ltac2 Set LiaHints.tbl := fun () => "0040>20988269697.1122766053480.1328202052267.1141283725690.1300000600<00B00HS1L2W0S1L2HiS1L2B1S1L2Hi".
split; [lia|]. split; [lia|]. intros i Hi. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

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
  [(0x98ff0, 8); (0x99000, 48); (0x99030, 8); (0x99b78, 8); (0x99c68, 8); (0x9ae90, 16);
   (0x9e7f8, 13); (0x9e838, 20); (0x9e864, 12); (0x9e88d, 1); (0xa1038, 8); (0xa089c, 1);
   (0xa08a0, 1); (0xa08a4, 4); (0xa1d18, 2); (0xa1d20, 24); (0xa1d3c, 4); (0x1232a0, 3);
   (0x130ae0, 8); (0x132b00, 16); (0x132b88, 8); (0x132b8a, 1); (0x132be0, 8); (ATP88, 8); (ATSD, 8);
   (0x5d3fe0, 4); (al_ctx L + 8, 4); (al_ctx L + 152, 8)]%Z.

#[using="MU WM"] Lemma arep_rt_frame : arep_rt L m -> Forall (fun p => disjoint_from W (fst p) (snd p)) rt_hulls -> arep_rt L m'.
Proof.
  intros RT CLR. unfold rt_hulls in CLR. dforall CLR.
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18
                  & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28).
  unfold arep_rt. repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed.

(* [comment removed for export] *)
#[using="MU"] Lemma arelro_frame : arelro m -> disjoint_from W ARELRO_LO (ARELRO_HI - ARELRO_LO) -> arelro m'.
Proof.
  intros R D i Hi. unfold arelro in R. rewrite <- (R i Hi).
  pose proof (MU (wa i)) as E. Local Ltac2 Set LiaHints.tbl := fun () => "0020>60737237913.1266259835913.12000004008S2HiS2Hi".
rewrite wa_unsigned in E by (unfold ARELRO_LO, ARELRO_HI in Hi; lia).
  apply E. eapply disjoint_outside; [exact D| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma azero_frame : forall A n, azero m A n -> munch W m m' -> wmono bsegs m m' ->
  (0 < n -> disjoint_from W A n) -> azero m' A n.
Proof.
  intros A n [Z0 WR] MU' WM' D. split.
  - intros i Hi. rewrite <- (Z0 i Hi). pose proof WR as (W0 & W1 & _).
    pose proof (MU' (wa (A + i))) as E. Local Ltac2 Set LiaHints.tbl := fun () => "0030>2431295703.19 33621940781.1951694454947.1900000400>00BS2HiS2Hi2W02W1S2Hi".
rewrite wa_unsigned in E by lia. apply E.
    eapply disjoint_outside; [apply D; lia | lia].
  - eapply wr_at_transport; [exact WR | exact WM'].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="MU WM"] Lemma ashadow_avail_frame : forall st st' c,
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

#[using="MU WM"] Lemma arep_rt2_frame : arep_rt2 m -> disjoint_from W 0x132c6c 1 -> disjoint_from W 0x132bf8 8 -> disjoint_from W 0x9ae40 8 -> arep_rt2 m'.
Proof. intros (R1 & R2 & R3) D1 D2 D3. split; [xcell|]. split; xcell. Qed.

(* [comment removed for export] *)
Definition rt3_hulls : list (Z * Z) :=
  [(0x9ad88, 16); (0x9ad68, 8); (0x9ad70, 8); (0x9ae40, 8); (0x9ad58, 8); (0x132bb8, 8); (0x132c60, 8);
   (0xa1040, 4); (0x9e898, 1); (0x130ad8, 4);
   (0x98ff0, 16); (0x9aed0, 8); (0x130ae0, 8); (0x132c40, 8); (0x132c58, 8); (0x5f4290, 8)]%Z.   (* [comment removed for export] *)
#[using="MU WM"] Lemma arep_rt3_frame : arep_rt3 m -> Forall (fun p => disjoint_from W (fst p) (snd p)) rt3_hulls -> arep_rt3 m'.
Proof.
  intros RT CLR. unfold rt3_hulls in CLR. dforall CLR.
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17).
  unfold arep_rt3. repeat lazymatch goal with |- _ /\ _ => split end; first [apply premap_canary_any | xcell].
Qed.

(* [comment removed for export] *)
#[using="MU WM"] Lemma ainstance_frame : forall st st',
  ainstance L st m -> a_nres st' = a_nres st -> a_nsec st' = a_nsec st ->
  disjoint_from W (AINSTANCE + 32) 96 -> disjoint_from W (AINSTANCE + 680) 1 -> disjoint_from W (AINSTANCE + 984) 1 ->
  ainstance L st' m'.
Proof.
  intros st st' (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9) E1 E2 D1 D2 D3. unfold ainstance. rewrite E1, E2.
  Local Ltac2 Set LiaHints.tbl := fun () => "00E0>12579371064.2714652522566.2726688814656.2932654103983.2334608857534.2940825481067.2341235038402.2447248134599.2653275776017.2359284393933.2560910078899.2563368129527.2563368130043.2863368130172.2763368130301.2663631290540.2465432518073.2665502224634.296755717096.24 8178255679.28 8624911937.28 00000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00D00ESSSSSSSSSSSSSSSSSSSSS".
pose proof (disjoint_from_sub W _ _ (AINSTANCE + 40) 4 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Df.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 56) 1 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dg.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 32) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 48) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 64) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 72) 8 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (AINSTANCE + 112) 16 D1 ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  repeat lazymatch goal with |- _ /\ _ => split end; xcell.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="MU WM"] Lemma aregion_cells_frame : forall st st' c,
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
  Local Ltac2 Set LiaHints.tbl := fun () => "00?0>12868766841.2222412167258.2022538334589.21272470207.24  32126274421.2436367736846.2338137140979.2240825474236.225541661042.21 65504325786.206755716715.23 67642619514.246787166132.23 704350264.21  9514155476.20 00000100200300400500600700800900:00;00<00=00>00?SSSSSSSSSSSSSSS".
pose proof (disjoint_from_sub W _ _ (aregion_info L c) 16 D ltac:(lia) ltac:(lia) ltac:(lia)) as Da.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 16) 48 D ltac:(lia) ltac:(lia) ltac:(lia)) as Db.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 64) 4 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dc.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 68) 1 D ltac:(lia) ltac:(lia) ltac:(lia)) as Dd.
  pose proof (disjoint_from_sub W _ _ (aregion_info L c + 72) 56 D ltac:(lia) ltac:(lia) ltac:(lia)) as De.
  split; [xcell|]. split; [xcell|]. split; [eapply junk_frame; [exact A3 | exact MU | exact WM | intros _; exact Dc]|].
  split; [xcell|]. eapply junk_frame; [exact A5 | exact MU | exact WM | intros _; exact De].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="MU WM"] Lemma afreearray_frame : forall st st' X X' c,
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
    Local Ltac2 Set LiaHints.tbl := fun () => "0060>1265473548.24 22410068171.2348174440242.2350754708754.2355035626894.2467946769644.2400000100200300;00?00DSSSS3LEN2LES2LES3LEN".
eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frame; [exact A2 | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply junk_frame; [exact A3 | exact MU | exact WM | intros _; exact DS].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="MU WM"] Lemma acache_cells_frame : forall st st' X X' c,
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
    Local Ltac2 Set LiaHints.tbl := fun () => "0060>22412167258.2023494567476.2033666907028.2048168146851.2064825191880.20785946533.20  00000400800<00@00D00HS2A3S2A3S2A3S2A3S2A3S2A3".
eapply disjoint_from_sub; [exact D | lia | lia | lia].
  - eapply u32arr_frame; [exact A2 | exact MU | exact WM |]. rewrite length_app, length_map.
    eapply disjoint_from_sub; [exact D | unfold acache_addr; lia | lia | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition xb_fits (b : xbusy) : Prop :=
  match xb_st b with
  | BBatch => True
  | _ => 0 <= xb_n b /\ 16 <= rz_size (xb_n b) /\ rz_size (xb_n b) + xb_n b <= size_of_class (xb_class b)
  end.

#[using="MU WM"] Lemma aslot_busy_frame : forall b,
  aslot_busy L m b -> xb_fits b ->
  disjoint_from W (xb_alloc L b) (size_of_class (xb_class b)) ->
  aslot_busy L m' b.
Proof.
  intros b SB FIT D. unfold aslot_busy, xb_fits in *. cbv zeta in *. unfold xb_hdr, xb_user in *.
  set (AB := xb_alloc L b) in *. set (S := size_of_class (xb_class b)) in *. set (n := xb_n b) in *. set (rz := rz_size n) in *.
  destruct (xb_st b).
  - destruct FIT as (N & RZ & FIT). destruct SB as (LH & [stb [E HDR]] & UJ). split; [| split].
    + intros H16. destruct (LH H16) as [LC J]. split.
      * eapply cells_frame; [exact LC | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. Local Ltac2 Set LiaHints.tbl := fun () => "00H0>10188958544.2410188958544.2512812391175.2512812391175.2616047938856.2416047938856.2519068320167.2519068320167.2628036194900.2128036194900.2233666907028.2133666907028.2233667136666.2433667136666.2535330812690.2235330812690.2343965138777.2543965138777.264438252287.21 4438252287.22 47682883527.2247682883527.2357191407900.2257191407900.2300000100200600:00E00P00W00^00b00f00g00h00i00j00n01201301401;01B01F01J01K01LSSS2HpS2HpS1N3FIT3H16S1N3FIT3H16S1N3FITS1N3FITS2RZS2RZSSSSS2HpS2HpSSS1N3FITS1N3FITS2RZS2RZSS".
eapply disjoint_from_sub; [exact D | lia | lia | lia].
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
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="MU WM"] Lemma aslots_update : forall st st' X X' c k0,
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
#[using="MU WM"] Lemma aslot_shadow_update : forall st st' X X' c k0,
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
#[using="Type"] Lemma azero_cb : forall m A n k, azero m A n -> 0 <= k <= n ->
  rw_cells bsegs m A [CB (Z.to_nat k) (repeat (Z_to_bv 8 0) (Z.to_nat k))].
Proof.
  intros m A n k [Z0 (W0 & W1 & WR)] Hk. split; [split|].
  - cbn. split; [apply repeat_length| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. Local Ltac2 Set LiaHints.tbl := fun () => "0060>1312062674.10 24931803492.1051442752977.1051794599906.10548305750.12  62280508270.1200000700;00B00F00M00TS2W12HkS2W0S2W12HkS2HkS2Hk2HiS2Hk2Hi".
split; [lia|]. rewrite repeat_length. split; [lia|].
    intros i Hi. unfold mrd. rewrite Z0 by lia. symmetry. apply nth_error_repeat. exact Hi.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros i Hi. apply WR. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma azero_split : forall m A n k, azero m A n -> 0 <= k <= n -> azero m (A + k) (n - k).
Proof.
  intros m A n k [Z0 (W0 & W1 & WR)] Hk. split.
  - intros i Hi. Local Ltac2 Set LiaHints.tbl := fun () => "0040>10648610022.104062776908.10 42133566526.1257921984173.1200000400;00B00CS2W1S2W02HkS2Hk2HiS".
replace (A + k + i) with (A + (k + i)) by lia. apply Z0. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply WR. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma busy_of_Some_facts : forall X c k b, busy_of X c k = Some b -> In b (x_busy X) /\ xb_class b = c /\ xb_slot b = k.
Proof.
  intros X c k b Hb. unfold busy_of in Hb. apply find_some in Hb. destruct Hb as [HIn HP].
  apply andb_true_iff in HP. destruct HP as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.

#[using="Type"] Lemma rz_size_ge16 : forall n, 16 <= rz_size n.
Proof.
  intros n. rewrite rz_size_eq. assert (0 <= rz_log n) by (unfold rz_log; repeat (destruct (_ <=? _)); lia).
  assert (1 <= 2 ^ rz_log n) by (apply Z.pow_le_mono_r with (a := 2) in H; [| lia]; rewrite Z.pow_0_r in H; lia). lia.
Qed.

#[using="Type"] Lemma rounded_size_ge : forall n, n <= rounded_size n.
Proof. intros n. rewrite rounded_size_eq. Local Ltac2 Set LiaHints.tbl := fun () => "0010=20504331982.2000001S".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma awf_fits : forall L st X b, awf L st X -> In b (x_busy X) -> xb_fits b.
Proof.
  intros L st X b WF Hb. destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY b Hb) as [_ M]. unfold xb_fits.
  pose proof (rz_size_ge16 (xb_n b)) as R. pose proof (rounded_size_ge (xb_n b)) as RS.
  destruct (xb_st b); [| | exact I]; destruct M as (N & FIT & _); (split; [clear -N; lia|]); split; clear -R RS FIT; lia.
Qed.

#[using="Type"] Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. rewrite !shad_div. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

#[using="Type"] Lemma mod16_of_class : forall a s, a mod s = 0 -> s mod 16 = 0 -> 0 < s -> a mod 8 = 0.
Proof.
  intros a s H1 H2 Hs. Local Ltac2 Set LiaHints.tbl := fun () => "0030=13901226085.724897143244.761028787377.6000004005006S2HsSS".
apply Z.mod_divide in H1; [|lia]. apply Z.mod_divide in H2; [|lia]. apply Z.mod_divide; [lia|].
  eapply Z.divide_trans; [| exact H1]. eapply Z.divide_trans; [| exact H2]. exists 2. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

End CANSEC2.
(* [comment removed for export] *)
