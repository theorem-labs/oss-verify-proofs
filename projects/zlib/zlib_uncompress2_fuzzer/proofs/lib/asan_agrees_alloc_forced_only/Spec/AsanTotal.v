(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.FO.P04 Require Import Mmap Mprotect.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import AcctCore.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import STree AsanCtrl AsanCtrlProps SizeHist Gap AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanPlace.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanVol.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* port727 candidate (2026-11-15): Spec/Gap's walk, keeping the base it finds. At the anonymous grant
   is Linux's placement, which a free gap in the bottom-up window [task_unmapped_base, alloc_top) admits
   (Checks/Placement.linux_place_exists, its right disjunct); Gap's walk finds a free gap at or above FLOOR and below
   CEIL, so the window holds (FLOOR > task_unmapped_base, CEIL <= alloc_top). The walk below is Gap's walk_step /
   walk with the region_free arm returned as the base itself. *)
Section WalkW.
Variable h : VmMaps.
Variable nZ : Z.
Let maps := vm_reserved h ++ vm_maps h.
Hypothesis HnZ : 0 < nZ.

Lemma walkw_step : forall c,
  c mod 4096 = 0 -> FLOOR <= c -> c + nZ + pot nZ c maps <= CEIL ->
  region_free maps (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true
  \/ (exists e, In e maps /\ above c e = true /\ glo e < c + nZ).
Proof.
  intros c Hal Hfl Hinv. pose proof FLOOR_val as FV. pose proof CEIL_val as CV.
  assert (Hpot : 0 <= pot nZ c maps) by (unfold pot; pose proof (sum_sz_nonneg (List.filter (above c) maps)); nia).
  assert (Hc64 : 0 <= c < 2^64) by (unfold FLOOR, CEIL in *; lia).
  assert (HnZ64 : 0 <= nZ < 2^64) by (unfold FLOOR, CEIL in *; lia).
  destruct (region_free maps (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree; [left; reflexivity|].
  right. destruct (region_free_false_inv _ _ _ Hfree) as (e & Hin & Hov). exists e.
  unfold iv_overlap in Hov. rewrite !unsigned_lit in Hov by assumption. apply andb_prop in Hov as [O1 O2].
  apply Z.ltb_lt in O1. apply Z.ltb_lt in O2.
  split; [exact Hin|]. split; [| unfold glo; lia].
  unfold above, in_band_b, ghi, glo, gsz. unfold CEIL, FLOOR in *.
  rewrite (proj2 (Z.ltb_lt (bv_unsigned (fst e)) _)) by lia.
  rewrite (proj2 (Z.ltb_lt 0x2aaaaaaab000 _)) by lia.
  rewrite (proj2 (Z.ltb_lt c _)) by lia. reflexivity.
Qed.

Lemma walkw : forall k c,
  (length (List.filter (above c) maps) <= k)%nat ->
  c mod 4096 = 0 -> FLOOR <= c -> c + nZ + pot nZ c maps <= CEIL ->
  exists g, g mod 4096 = 0 /\ FLOOR <= g /\ g + nZ <= CEIL /\ region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
  induction k as [|k IH]; intros c Hk Hal Hfl Hinv;
    (assert (Hpot : 0 <= pot nZ c maps) by (unfold pot; pose proof (sum_sz_nonneg (List.filter (above c) maps)); nia)).
  - destruct (walkw_step c Hal Hfl Hinv) as [Hok|(e & Hin & Hab & Hlo)]; [exists c; repeat split; auto; lia|].
    exfalso. assert (HinF : In e (List.filter (above c) maps)) by (apply filter_In; auto).
    destruct (List.filter (above c) maps); [destruct HinF| cbn in Hk; lia].
  - destruct (walkw_step c Hal Hfl Hinv) as [Hok|(e & Hin & Hab & Hlo)]; [exists c; repeat split; auto; lia|].
    set (c' := page_round_up_Z (ghi e)).
    pose proof (page_round_up_Z_bounds (ghi e)) as [R1 R2]. fold c' in R1, R2.
    assert (Hhi : c < ghi e). { unfold above in Hab. apply andb_prop in Hab as [_ Hab]. apply Z.ltb_lt in Hab. exact Hab. }
    assert (Hcc : c <= c') by lia.
    destruct (filter_above_drop c c' maps e Hcc Hin Hab R1) as [D1 D2].
    apply (IH c').
    + lia.
    + apply page_round_up_Z_aligned'.
    + lia.
    + unfold pot in *. unfold ghi in *. pose proof (gsz_nonneg e).
      pose proof (sum_sz_nonneg (List.filter (above c') maps)). nia.
Qed.
End WalkW.

(* The grant's two gap facts at once: P04's first fit (vm_gap_available) and 's placement window. *)
Lemma gap_window_intro_N : forall mo nZ N R T,
  0 < nZ <= R -> CEIL <= alloc_top (m_vmmaps mo) ->
  let maps := vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo) in
  Z.of_nat (length (List.filter in_band_b maps)) <= N ->
  live_bytes maps <= T ->
  (N + 1) * (R + 4095) + T <= CEIL - FLOOR ->
  Mmap.vm_gap_available (m_vmmaps mo) nZ = true /\ AsanNodeSem.grant_window mo nZ.
Proof.
  intros mo nZ N R T HnZ Htop maps HN HT HB. split.
  - exact (vm_gap_available_intro_N (m_vmmaps mo) nZ N R T HnZ Htop HN HT HB).
  - unfold AsanNodeSem.grant_window. fold maps.
    set (L := Z.of_nat (length (List.filter in_band_b maps))) in *.
    assert (M1 : (L + 1) * (nZ + 4095) <= (N + 1) * (nZ + 4095)) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (M2 : (N + 1) * (nZ + 4095) <= (N + 1) * (R + 4095)) by (apply Z.mul_le_mono_nonneg_l; subst L; lia).
    assert (Hb : (L + 1) * (nZ + 4095) + live_bytes maps <= CEIL - FLOOR) by lia.
    assert (Hinv : FLOOR + nZ + pot nZ FLOOR maps <= CEIL).
    { unfold pot. rewrite <- sum_sz_live_bytes in Hb.
      assert (L1 : (length (List.filter (above FLOOR) maps) <= length (List.filter in_band_b maps))%nat).
      { unfold above. clear. induction maps as [|e l IH]; cbn; [lia|]. destruct (in_band_b e); cbn; [destruct (_ <? _); cbn; lia| lia]. }
      pose proof (sum_sz_filter_le (above FLOOR) maps). pose proof (sum_sz_nonneg maps).
      assert (M : Z.of_nat (length (List.filter (above FLOOR) maps)) * (nZ + 4095)
                  <= Z.of_nat (length (List.filter in_band_b maps)) * (nZ + 4095)) by (apply Z.mul_le_mono_nonneg_r; lia).
      subst L. lia. }
    destruct (walkw (m_vmmaps mo) nZ ltac:(lia) (length (List.filter (above FLOOR) maps)) FLOOR (le_n _) FLOOR_aligned
                (Z.le_refl _) Hinv) as (g & G1 & G2 & G3 & G4).
    assert (TUB : LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.task_unmapped_base = 0x2aaaaab000) by (vm_compute; reflexivity).
    exists g. unfold LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.gap_fits. rewrite page_size_4096, TUB.
    rewrite FLOOR_val in G2. split; [exact G1|]. split; [lia|]. split; [lia| exact G4].
Qed.

Section WithResv.
Context {RESV : list (Z * Z)} {ATOP : Z}.
Local Notation INV := (AsanInv.INV RESV ATOP).
Local Notation AMI := (AsanInv.AMI RESV ATOP).
Local Notation AINV := (AsanInv.AINV ATOP).
Local Notation aok := (AsanNodeSem.aok ATOP).
Local Notation apost := (AsanNodeSem.apost ATOP).
Local Notation atot := (atotal aok apost).
Local Notation chunk_wf := (AsanInv.chunk_wf ATOP).

Lemma INV_atop : forall pc pb st mo, INV pc pb st mo -> atop_ok ATOP /\ alloc_top (m_vmmaps mo) = ATOP.
Proof. intros pc pb st mo [_ HM]. exact (AMI_atop _ _ _ HM). Qed.

Lemma region_free_sub : forall l (a n a' n' : Z),
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  0 <= a -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> a + n < 2^64 ->
  region_free l (Z_to_bv 64 a') (Z_to_bv 64 n') = true.
Proof.
  induction l as [|[b sz] l IH]; intros a n a' n' H Ha Haa Hn Hsub Htop; [reflexivity|].
  cbn [region_free] in H |- *. apply andb_prop in H as [H1 H2]. rewrite (IH _ _ _ _ H2 Ha Haa Hn Hsub Htop), andb_true_r.
  unfold iv_overlap in *. rewrite !unsigned_lit in H1 |- * by lia.
  apply negb_true_iff in H1. apply negb_true_iff. apply andb_false_iff in H1. apply andb_false_iff.
  destruct H1 as [H1|H1]; apply Z.ltb_ge in H1; [left|right]; apply Z.ltb_ge; lia.
Qed.

Definition same_but (c : Z) (st st' : astate) : Prop :=
  a_space_beg st' = a_space_beg st /\ a_ptr_array st' = a_ptr_array st /\ a_nres st' = a_nres st /\ a_nsec st' = a_nsec st
  /\ a_cinit st' = a_cinit st /\ a_live st' = a_live st /\ a_next st' = a_next st
  /\ a_qloc st' = a_qloc st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob st' = a_qglob st /\ a_qglob_bytes st' = a_qglob_bytes st
  /\ (forall c', c' <> c -> get_cls st' c' = get_cls st c').

Lemma same_but_refl : forall c st, same_but c st st.
Proof. intros. unfold same_but. repeat split; reflexivity. Qed.
Lemma same_but_put : forall c st r, same_but c st (put_cls c r st).
Proof. intros. unfold same_but. repeat split; try reflexivity. intros c' Hc'. apply get_put_ne. congruence. Qed.
Lemma same_but_trans : forall c st1 st2 st3, same_but c st1 st2 -> same_but c st2 st3 -> same_but c st1 st3.
Proof.
  intros c st1 st2 st3 A B. unfold same_but in *.
  destruct A as (?&?&?&?&?&?&?&?&?&?&?&HA). destruct B as (?&?&?&?&?&?&?&?&?&?&?&HB).
  repeat split; try congruence. intros c' Hc'. rewrite HB, HA; auto.
Qed.

Definition CLSOK (pc : list achunk) (pb : list abatch) (st : astate) (c : Z) (r : aclass) : Prop :=
  0 <= c_allocated_user r /\ c_allocated_user r <= c_mapped_user r /\ c_mapped_user r <= K_FREEARR_OFF
  /\ c_mapped_user r - c_allocated_user r <= 2 * K_USER_MAP
  /\ c_mapped_user r mod K_USER_MAP = 0
  /\ 0 <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0
  /\ 0 <= c_num_freed r /\ 0 <= c_count r <= max_count st c
  /\ c_allocated_user r = size_of_class c * (cntP c (all_chunks pc pb st) + nbatch c (qbatches pb st) + c_count r + c_num_freed r)
  /\ size_of_class c * (c_count r + c_num_freed r) <= UNUSED_MAX
  /\ c_mapped_free_array r <= K_FREEARR_MAP.

Lemma AINV_cls : forall pc pb st c, AINV pc pb st -> 1 <= c <= 31 -> CLSOK pc pb st c (get_cls st c).
Proof. intros pc pb st c (H & _) Hc. exact (H c Hc). Qed.

Lemma AINV_put_cls : forall pc pb st c r, AINV pc pb st -> 1 <= c <= 31 -> CLSOK pc pb st c r -> AINV pc pb (put_cls c r st).
Proof.
  intros pc pb st c r H Hc HR. unfold AINV in *. rewrite !all_chunks_put, !qbatches_put, !CH_put.
  destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array put_cls set_cls] in *.
  split; [| repeat (split; [assumption|]); assumption].
  intros c' Hc'. unfold cls_inv. rewrite max_count_put, all_chunks_put, qbatches_put.
  destruct (Z.eq_dec c' c) as [->|Hne].
  - rewrite get_put_eq. exact HR.
  - rewrite get_put_ne by congruence. exact (HC c' Hc').
Qed.

Lemma csum_bound : forall f st b, (forall c, 1 <= c <= 31 -> f (get_cls st c) <= b) -> csum f st <= 31 * b.
Proof.
  intros f st b H. unfold csum.
  assert (G : forall l, (forall c, In c l -> 1 <= c <= 31) -> fold_right (fun c acc => f (get_cls st c) + acc) 0 l <= zlen l * b).
  { induction l as [|c l IH]; intros Hl; unfold zlen in *; cbn [fold_right length]; [lia|]. rewrite Nat2Z.inj_succ.
    pose proof (H c (Hl c (or_introl eq_refl))). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
  specialize (G CLASSES ltac:(intros c Hc; apply In_CLASSES; exact Hc)). change (zlen CLASSES) with 31 in G. exact G.
Qed.
Lemma csum_nonneg : forall f st, (forall c, 1 <= c <= 31 -> 0 <= f (get_cls st c)) -> 0 <= csum f st.
Proof.
  intros f st H. unfold csum.
  assert (G : forall l, (forall c, In c l -> 1 <= c <= 31) -> 0 <= fold_right (fun c acc => f (get_cls st c) + acc) 0 l).
  { induction l as [|c l IH]; intros Hl; cbn [fold_right]; [lia|].
    pose proof (H c (Hl c (or_introl eq_refl))). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
  apply G. intros c Hc; apply In_CLASSES; exact Hc.
Qed.

Definition CBMAX : Z := 31 * (K_FREEARR_OFF + K_FREEARR_MAX) + 8 * K_CHUNKS_BLOCK.
Lemma commit_bytes_bound : forall pc pb st, AINV pc pb st -> 0 <= commit_bytes st <= CBMAX.
Proof.
  intros pc pb st H. pose proof H as (HC & _ & _ & _ & _ & _ & Hres & _).
  unfold commit_bytes, CBMAX.
  pose proof (csum_bound cls_mapped_bytes' st (K_FREEARR_OFF + K_FREEARR_MAX)) as B1.
  pose proof (csum_nonneg cls_mapped_bytes' st) as B0.
  assert (A : forall c, 1 <= c <= 31 -> 0 <= cls_mapped_bytes' (get_cls st c) <= K_FREEARR_OFF + K_FREEARR_MAX).
  { intros c Hc. destruct (HC c Hc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10). unfold cls_mapped_bytes'. lia. }
  specialize (B1 ltac:(intros c Hc; apply A; exact Hc)). specialize (B0 ltac:(intros c Hc; apply A; exact Hc)).
  unfold K_CHUNKS_BLOCK in *. destruct Hres as [-> | ->]; lia.
Qed.

Lemma mmap_len_id : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof.
  intros l Hl Hm. unfold mmap_len, page_round_up_Z, page_size.
  pose proof (Z.div_mod l 4096 ltac:(lia)). rewrite Hm in H.
  replace (l + 4096 - 1) with (l / 4096 * 4096 + 4095) by lia.
  rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
Qed.

Lemma region_free_above : forall l (a n : Z) R,
  Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= R) l -> R <= a -> 0 <= a -> a + n < 2^64 -> 0 <= n ->
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
Proof.
  induction l as [|[b s] l IH]; intros a n R Hf HR Ha Han Hn; [reflexivity|].
  apply Forall_cons_iff in Hf as [H1 Hf]. cbn [region_free]. rewrite (IH a n R Hf HR Ha Han Hn).
  unfold iv_overlap. rewrite !unsigned_lit by lia. cbn [fst snd] in H1.
  replace (a <? bv_unsigned b + bv_unsigned s) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* port727 candidate: a range inside a map that is apart from every entry of l is free in l (AsanInv's AMI now
   carries "every map is apart from every reserved range" in place of the RES_HI bound) *)
Lemma region_free_inside_wsep : forall l (e : word * word) (a n : Z),
  Forall (wsep e) l -> bv_unsigned (fst e) <= a -> a + n <= bv_unsigned (fst e) + bv_unsigned (snd e) ->
  0 <= a -> a + n < 2^64 -> 0 <= n ->
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
Proof.
  induction l as [|[b s] l IH]; intros e a n Hf H1 H2 Ha Han Hn; [reflexivity|].
  apply Forall_cons_iff in Hf as [Hw Hf]. cbn [region_free]. rewrite (IH e a n Hf H1 H2 Ha Han Hn).
  unfold iv_overlap. rewrite !unsigned_lit by lia. unfold wsep in Hw. cbn [fst snd] in Hw.
  destruct Hw as [Hw|Hw].
  - replace (bv_unsigned b <? a + n) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity.
  - replace (a <? bv_unsigned b + bv_unsigned s) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma CH_wf : forall pc pb st, AINV pc pb st -> Forall (fun e => 0 <= snd e < 2^64) (CH pc pb st).
Proof.
  intros pc pb st (_ & Hwf & _). unfold CH. induction (all_chunks pc pb st) as [|ch l IH]; [constructor|].
  apply Forall_cons_iff in Hwf as [H1 Hwf]. rewrite secs_cons. apply Forall_app. split; [|apply IH; exact Hwf].
  destruct ch as [c n|mb ms n]; cbn [sec_of]; [constructor|]. constructor; [|constructor]. cbn [snd].
  cbn [chunk_wf] in H1. destruct H1 as (Hn & -> & _). pose proof (sec_map_size_bounds n ltac:(lia)). lia.
Qed.

Lemma INV_backing_bound : forall pc pb st mo, INV pc pb st mo ->
  vm_backing_used mo <= EAGER0 + CBMAX + zsum2 (CH pc pb st).
Proof.
  intros pc pb st mo [HA HM]. pose proof (AMI_nonlazy_bound _ _ _ HM (CH_wf _ _ _ HA)).
  pose proof (commit_bytes_bound _ _ _ HA). rewrite vm_backing_used_split. destruct HM as (-> & _). cbn [length Z.of_nat]. lia.
Qed.

Lemma INV_backing_vol : forall pc pb st mo, INV pc pb st mo ->
  vm_backing_used mo <= EAGER0 + W pc pb st + VOL_CONST.
Proof.
  intros pc pb st mo [HA HM]. pose proof (AMI_nonlazy_bound _ _ _ HM (CH_wf _ _ _ HA)).
  pose proof (VOL_W ATOP _ _ _ HA). rewrite vm_backing_used_split. destruct HM as (-> & _). cbn [length Z.of_nat]. lia.
Qed.
Lemma vroom_CH35 : forall pc pb st, AINV pc pb st -> vroomL pc pb st -> zsum2 (CH pc pb st) <= 2^35.
Proof.
  intros pc pb st HA HV. pose proof (VOL_W ATOP _ _ _ HA) as V. pose proof (commit_bytes_bound _ _ _ HA) as [C0 _].
  unfold vroomL, WCAP in HV. rewrite VOL_CONST_val in V. lia.
Qed.

Lemma INV_fixed_aok : forall pc pb st mo E a len,
  INV pc pb st mo -> In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + len <= B E + S E ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true -> 0 < a ->
  a mod 4096 = 0 -> len mod 4096 = 0 -> 0 < len <= 2^30 -> vroomL pc pb st ->
  aok (AMmap a len PROT_RW F_FIXED) mo.
Proof.
  intros pc pb st mo E a len HI HinE HE1 HE2 HR Ha0 Hal Hll Hlen HSB.
  pose proof HI as [HA HM]. pose proof (AMI_ivs_wf _ _ _ HM) as Hwf.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & _).
  assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
  unfold RES_HI, ACEIL, ATOP_MAX in *. unfold B, S in *. pose proof (bv_unsigned_in_range 64 (fst E)) as HE0.
  assert (ML : mmap_len len = len) by (apply mmap_len_id; lia).
  cbn [AsanNodeSem.aok]. split; [reflexivity|]. split; [lia|]. split; [exact T3|].
  replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite ML. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|split].
  - exact HR.
  - apply (map_contains_In _ E); auto; rewrite !unsigned_lit by lia; lia.
  - apply mmap_fixed_rw_budget_ok_commit_intro; [reflexivity| exact Hwf|].
    rewrite !unsigned_lit by lia. apply Z.le_trans with HLIMIT; [| exact M2]. unfold HLIMIT.
    pose proof (INV_backing_vol _ _ _ _ HI) as BV. unfold vroomL, WCAP in HSB. rewrite VOL_CONST_val in BV.
    pose proof (overlap_sum_contained (vm_maps (m_vmmaps mo)) E a (a + len) M9 HinE ltac:(unfold B; lia) ltac:(unfold B, S; lia) ltac:(lia)).
    unfold EAGER0, CBMAX, K_FREEARR_OFF, K_FREEARR_MAX, K_CHUNKS_BLOCK in *. lia.
Qed.

(* port727 candidate: INV_resv_hi is LEFT OUT. *)

Lemma INV_fixed_aok_high : forall pc pb st mo E a len,
  INV pc pb st mo -> In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + len <= B E + S E -> RES_HI <= a ->
  a mod 4096 = 0 -> len mod 4096 = 0 -> 0 < len <= 2^30 -> vroomL pc pb st ->
  aok (AMmap a len PROT_RW F_FIXED) mo.
Proof.
  intros pc pb st mo E a len HI HinE HE1 HE2 HR Hal Hll Hlen HSB.
  pose proof HI as [HA HM]. pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & _).
  assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
  unfold ACEIL, ATOP_MAX in T1, T2. unfold B, S in HE1, HE2. unfold RES_HI in HR.
  apply (INV_fixed_aok pc pb st mo E a len HI HinE); unfold B, S; auto; try lia.
  (* port727 candidate: from "E is apart from every reserved range" (AMI) in place of the RES_HI bound *)
  pose proof (bv_unsigned_in_range 64 (fst E)) as HE0.
  apply (region_free_inside_wsep _ E a len (proj1 (Forall_forall _ _) M3 E HinE)); lia.
Qed.

Lemma INV_recommit_aok : forall pc pb st mo E a len,
  INV pc pb st mo -> In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + len <= B E + S E -> RES_HI <= a ->
  a mod 4096 = 0 -> len mod 4096 = 0 -> 0 < len <= 2^30 -> vroomL pc pb st ->
  aok (AMmap a len PROT_RW F_FIXNORES) mo.
Proof.
  intros pc pb st mo E a len HI HinE HE1 HE2 HR Hal Hll Hlen HSB.
  pose proof HI as [HA HM]. pose proof (AMI_ivs_wf _ _ _ HM) as Hwf.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & _).
  assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
  unfold RES_HI, ACEIL, ATOP_MAX in *. unfold B, S in *. pose proof (bv_unsigned_in_range 64 (fst E)) as HE0.
  assert (ML : mmap_len len = len) by (apply mmap_len_id; lia).
  cbn [AsanNodeSem.aok]. split; [reflexivity|]. split; [lia|]. split; [exact T3|].
  replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite ML. split; [right; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|split].
  - (* port727 candidate: as INV_fixed_aok_high *)
    apply (region_free_inside_wsep _ E a len (proj1 (Forall_forall _ _) M3 E HinE)); lia.
  - apply (map_contains_In _ E); auto; rewrite !unsigned_lit by lia; lia.
  - apply mmap_fixed_rw_budget_ok_recommit_intro; [reflexivity| exact Hwf| | | | |];
      rewrite ?unsigned_lit by lia; unfold page_size; try lia.
    apply Z.le_trans with HLIMIT; [| exact M2]. unfold HLIMIT. pose proof (INV_backing_vol _ _ _ _ HI) as BV. unfold vroomL, WCAP in HSB. rewrite VOL_CONST_val in BV. unfold EAGER0 in *. lia.
Qed.

Lemma INV_munmap_aok : forall pc pb st mo mb ms,
  INV pc pb st mo -> In (mb, ms) (CH pc pb st) ->
  0 < mb -> mb mod 4096 = 0 -> 0 < ms <= 2^31 -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  aok (AMunmap mb ms) mo.
Proof.
  intros pc pb st mo mb ms [HA HM] Hin Hmb Hal Hms Hml Hce.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HP & HS & HB).
  assert (ML : mmap_len ms = ms) by (apply mmap_len_id; lia).
  cbn [AsanNodeSem.aok]. rewrite ML. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [| split; [exact M9| exact M6]].   (* port727 candidate: AMI's seps and entry_ok, for aok's AMunmap arm *)
  apply map_has_In. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. right.
  change (Z_to_bv 64 mb, Z_to_bv 64 ms) with (went (mb, ms)). apply in_map. exact Hin.
Qed.

Lemma live_bytes_perm' : forall l l', Permutation l l' -> live_bytes l = live_bytes l'.
Proof. intros. rewrite !live_bytes_sum_count. apply sum_count_perm. assumption. Qed.
Lemma live_bytes_app' : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. intros. apply BackingAlgebra.live_bytes_app. Qed.

Lemma INV_grant_aok : forall pc pb st mo n,
  INV pc pb st mo -> 64512 < n <= 2^30 -> vroomL pc pb st -> zlen (CH pc pb st) <= 16000 ->
  aok (AMmap 0 (sec_map_size n) PROT_RW F_ANON) mo.
Proof.
  intros pc pb st mo n HI Hn HV HSL.
  pose proof HI as [HA HM]. pose proof (AMI_ivs_wf _ _ _ HM) as Hwf. pose proof (vroom_CH35 _ _ _ HA HV) as HSB.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & L0 & HP & HS & HB).
  pose proof (sec_map_size_bounds n ltac:(lia)) as SB.
  assert (ML : mmap_len (sec_map_size n) = sec_map_size n).
  { apply mmap_len_id; [lia|]. unfold sec_map_size, rup, PG.
    match goal with |- ?x mod 4096 = 0 => replace x with ((((needed_size n + 4096 - 1) / 4096) + 1) * 4096) by lia end.
    apply Z_mod_mult. }
  cbn [AsanNodeSem.aok]. rewrite Z.eqb_refl. rewrite ML. split; [reflexivity|]. split; [lia|]. split; [exact T3|]. split; [reflexivity|]. split.
  - apply Z.le_trans with HLIMIT; [| exact M2]. unfold HLIMIT. pose proof (INV_backing_vol _ _ _ _ HI) as BV. unfold vroomL, WCAP in HV. rewrite VOL_CONST_val in BV. unfold EAGER0 in *. lia.
  - (* port727 candidate: both gap facts (P04's first fit and 's placement window) *)
    apply (gap_window_intro_N _ _ (LEN0 + LEN0 + 16000) (2^30 + 2^20) (RTOT0 + TOT0 + 2^35)); [lia| | | |].
    + rewrite T3. unfold ACEIL in T1. rewrite CEIL_val. exact T1.
    + eapply Z.le_trans. { apply inj_le. apply length_filter_le. }
      rewrite length_app, Nat2Z.inj_add. fold (zlen (vm_reserved (m_vmmaps mo))). fold (zlen (vm_maps (m_vmmaps mo))).
      unfold zlen at 2. rewrite (Permutation_length HP). fold (zlen (L0 ++ map went (CH pc pb st))). rewrite zlen_app.
      unfold zlen at 3. rewrite length_map. fold (zlen (CH pc pb st)). destruct HS as (_ & _ & _ & _ & _ & _ & _ & HL & _). lia.
    + rewrite live_bytes_app'. rewrite (live_bytes_perm' _ _ HP).
      rewrite live_bytes_app', (live_bytes_went _ (CH_wf _ _ _ HA)). destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HT & _). lia.
    + rewrite CEIL_val, FLOOR_val. unfold LEN0, RTOT0, TOT0. lia.
Qed.

Lemma INV_prim : forall pc pb st mo, INV pc pb st mo ->
  exists pb0, In (went (pb0, PRIM_SZ)) (vm_maps (m_vmmaps mo)) /\ pb0 <= a_space_beg st /\ a_space_beg st + 2^37 + 2^12 <= pb0 + PRIM_SZ
              /\ KHIGH <= pb0 /\ pb0 + PRIM_SZ <= ATOP.
Proof.
  intros pc pb st mo [_ HM]. destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HP & HS & _).
  destruct HS as ((pb0 & Hin & H1 & H2 & H3 & H4) & _). exists pb0. split; [|repeat split; assumption].
  eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hin.
Qed.
Lemma INV_ptr : forall pc pb st mo, INV pc pb st mo ->
  In (went (a_ptr_array st, PTR_SZ)) (vm_maps (m_vmmaps mo)) /\ a_ptr_array st + PTR_SZ <= ATOP
  /\ region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 (a_ptr_array st)) (Z_to_bv 64 PTR_SZ) = true.
Proof.
  intros pc pb st mo [_ HM]. destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HP & HS & _).
  destruct HS as (_ & Hin & H1 & H2 & _). split; [|split; assumption].
  eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hin.
Qed.
Lemma INV_shadows : forall pc pb st mo, INV pc pb st mo ->
  In (went (LS_LO, LS_SZ)) (vm_maps (m_vmmaps mo)) /\ In (went (GAP_LO, GAP_SZ)) (vm_maps (m_vmmaps mo)) /\ In (went (HS_LO, HS_SZ)) (vm_maps (m_vmmaps mo)).
Proof.
  intros pc pb st mo [_ HM]. destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HP & HS & _).
  destruct HS as (_ & _ & _ & _ & H1 & H2 & H3 & _).
  repeat split; (eapply Permutation_in; [apply Permutation_sym; exact HP|]; apply in_app_iff; left; assumption).
Qed.

Lemma AINV_geom : forall pc pb st, AINV pc pb st -> a_space_beg st mod 65536 = 0 /\ 0 < a_space_beg st /\ a_ptr_array st mod 4096 = 0 /\ 0 < a_ptr_array st.
Proof. intros pc pb st H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _). auto. Qed.

Lemma rup_mod : forall x a, 0 < a -> rup x a mod a = 0.
Proof. intros. unfold rup. apply Z_mod_mult. Qed.
Lemma rup_ge' : forall x a, 0 < a -> x <= rup x a. Proof. exact rup_ge. Qed.

Lemma is_err_small : forall a, 0 <= a <= TWO64 - 4096 -> is_err a = false.
Proof. intros. unfold is_err. apply Z.ltb_ge. lia. Qed.


Lemma mod0_divide : forall x m, 0 < m -> x mod m = 0 -> (m | x).
Proof. intros. apply Z.mod_divide; lia. Qed.
Lemma divide_mod0 : forall x m, 0 < m -> (m | x) -> x mod m = 0.
Proof. intros. apply Z.mod_divide; [lia| assumption]. Qed.
Lemma div4096_of_mod : forall x m, (4096 | m) -> 0 < m -> x mod m = 0 -> (4096 | x).
Proof. intros x m Hm Hp Hx. eapply Z.divide_trans; [exact Hm|]. apply mod0_divide; assumption. Qed.
Lemma div_65536 : (4096 | 65536). Proof. exists 16. reflexivity. Qed.
Lemma div_262144 : (4096 | 262144). Proof. exists 64. reflexivity. Qed.
Lemma div_lit : forall k, (4096 | k * 4096). Proof. intros. exists k. reflexivity. Qed.

Lemma ensure_ok : forall R (P : R -> Model -> Prop) pc pb st c nf (k : astate -> bool -> AM R) mo,
  INV pc pb st mo -> 1 <= c <= 31 -> 0 <= nf ->
  4 * nf <= K_FREEARR_MAP ->
  vroom pc pb st ->
  (forall st' mo', INV pc pb st' mo' -> same_but c st st' ->
     c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
     c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
     c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
     c_count (get_cls st' c) = c_count (get_cls st c) ->
     nf * 4 <= c_mapped_free_array (get_cls st' c) ->
     atot (k st' true) mo' P) ->
  atot (ensure_free_array st c nf k) mo P.
Proof.
  intros R P pc pb st c nf k mo HI Hc Hnf Hroom HSB Hk.
  pose proof HI as [HA HM]. pose proof (AINV_cls _ _ _ _ HA Hc) as HC.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
  destruct (AINV_geom _ _ _ HA) as (G1 & G2 & G3 & G4).
  destruct (INV_prim _ _ _ _ HI) as (pb0 & HinP & P1 & P2 & P3 & P4).
  unfold ensure_free_array. cbv zeta.
  destruct (Z.leb_spec (nf * 4) (c_mapped_free_array (get_cls st c))) as [Hle|Hgt].
  { apply (Hk st mo HI (same_but_refl c st)); auto. }
  pose proof (rup_ge (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as R1.
  pose proof (rup_le (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as R2.
  pose proof (rup_mod (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as R3.
  pose proof (rup_small (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia) ltac:(lia)) as R4.
  destruct (Z.ltb_spec K_FREEARR_MAX (rup (nf * 4) K_FREEARR_MAP)) as [Hbig|Hok]; [unfold K_FREEARR_MAP, K_FREEARR_MAX in *; lia|].
  set (len := rup (nf * 4) K_FREEARR_MAP - c_mapped_free_array (get_cls st c)).
  set (a := region_beg st c + K_FREEARR_OFF + c_mapped_free_array (get_cls st c)).
  assert (Hlen : 0 < len <= 2^30) by (unfold len, K_FREEARR_MAX in *; lia).
  assert (Dmfa : (4096 | c_mapped_free_array (get_cls st c))) by (apply (div4096_of_mod _ 262144); [apply div_262144| lia| unfold K_FREEARR_MAP in C7; exact C7]).
  assert (Drup : (4096 | rup (nf * 4) K_FREEARR_MAP)) by (apply (div4096_of_mod _ 262144); [apply div_262144| lia| unfold K_FREEARR_MAP in *; exact R3]).
  assert (Dsb : (4096 | a_space_beg st)) by (apply (div4096_of_mod _ 65536); [apply div_65536| lia| exact G1]).
  assert (Hlm : len mod 4096 = 0).
  { apply divide_mod0; [lia|]. unfold len. apply Z.divide_sub_r; assumption. }
  assert (Ham : a mod 4096 = 0).
  { apply divide_mod0; [lia|]. unfold a, region_beg, K_REGION, K_FREEARR_OFF.
    apply Z.divide_add_r; [|exact Dmfa]. apply Z.divide_add_r; [| exists 917504; reflexivity].
    apply Z.divide_add_r; [exact Dsb|]. replace (c * 2 ^ 32) with ((c * 2^20) * 4096) by lia. apply div_lit. }
  assert (Hc32 : 0 <= c * 2^32 <= 31 * 2^32) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
  assert (HE1 : pb0 <= a) by (unfold a, region_beg, K_REGION, K_FREEARR_OFF; lia).
  assert (HE2 : a + len <= pb0 + PRIM_SZ).
  { unfold a, len, region_beg, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX, PRIM_SZ in *. lia. }
  assert (HBS : B (went (pb0, PRIM_SZ)) = pb0 /\ S (went (pb0, PRIM_SZ)) = PRIM_SZ).
  { unfold B, S, went. cbn [fst snd]. unfold ACEIL, PRIM_SZ, KHIGH in *. rewrite !unsigned_lit by lia. lia. }
  destruct HBS as [HB1 HS1].
  unfold ev. apply atotal_vis.
  - pose proof (vroom_L _ _ _ HSB) as HSBL. apply (INV_fixed_aok_high pc pb st mo (went (pb0, PRIM_SZ))); auto; try lia. unfold RES_HI, KHIGH in *. lia.
  - intros z mo' Hpost. cbn [apost] in Hpost.
    assert (Hanz : (a =? 0) = false) by (apply Z.eqb_neq; unfold KHIGH in *; lia).
    rewrite Hanz in Hpost. destruct Hpost as [-> ->].
    rewrite fixed_answer_ok_self. cbn [negb].
    rewrite is_err_small by (unfold TWO64, ACEIL, KHIGH, PRIM_SZ in *; lia).
    assert (ML : mmap_len len = len) by (apply mmap_len_id; lia). rewrite ML.
    apply Hk.
    + split.
      * apply AINV_put_cls; [exact HA| exact Hc|]. unfold CLSOK. cbn [c_allocated_user c_mapped_user c_mapped_free_array c_num_freed c_count cls_set_mapped_free_array].
        unfold K_FREEARR_MAP in *. repeat split; try lia.
      * rewrite CH_put. apply (AMI_commit _ st _ _ (went (pb0, PRIM_SZ))); auto; try lia; try reflexivity.
        rewrite commit_bytes_put by exact Hc. unfold cls_mapped_bytes'. cbn [c_mapped_user c_mapped_free_array cls_set_mapped_free_array]. unfold len. lia.
    + apply same_but_put.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. cbn [c_mapped_free_array cls_set_mapped_free_array]. lia.
Qed.

Local Ltac cproj := cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count
                         cls_set_allocated_user cls_set_num_freed cls_set_mapped_free_array cls_set_mapped_user cls_set_count negb].

Lemma populate_ok : forall R (P : R -> Model -> Prop) pc pb st c req (k : astate -> bool -> AM R) mo,
  INV pc pb st mo -> 1 <= c <= 31 -> 32 <= size_of_class c <= 65536 -> 0 < req -> req * size_of_class c <= K_USER_MAP ->
  c_allocated_user (get_cls st c) + 2^20 <= K_FREEARR_OFF ->
  vroom pc pb st ->
  size_of_class c * (c_count (get_cls st c) + c_num_freed (get_cls st c)) <= K_USER_MAP ->
  (forall st' mo', INV pc pb st' mo' -> same_but c st st' ->
     c_count (get_cls st' c) = c_count (get_cls st c) ->
     c_num_freed (get_cls st c) + req <= c_num_freed (get_cls st' c) ->
     atot (k st' true) mo' P) ->
  atot (populate_free_array st c req k) mo P.
Proof.
  intros R P pc pb st c req k mo HI Hc Hsz Hreq Hrs Hroom HSB Hhalf Hk.
  pose proof HI as [HA HM]. pose proof (AINV_cls _ _ _ _ HA Hc) as HC.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
  destruct (AINV_geom _ _ _ HA) as (G1 & G2 & G3 & G4).
  destruct (INV_prim _ _ _ _ HI) as (pb0 & HinP & P1 & P2 & P3 & P4).
  remember (size_of_class c) as size eqn:Hsize.
  assert (TAIL : forall st1 mo1,
    INV pc pb st1 mo1 -> same_but c st st1 -> c_count (get_cls st1 c) = c_count (get_cls st c) -> c_num_freed (get_cls st1 c) = c_num_freed (get_cls st c) ->
    c_allocated_user (get_cls st1 c) = c_allocated_user (get_cls st c) ->
    c_allocated_user (get_cls st c) + req * size <= c_mapped_user (get_cls st1 c) -> vroom pc pb st1 ->
    atot (let r1 := get_cls st1 c in
          let new_cnt := (c_mapped_user r1 - c_allocated_user r1) / size in
          let total_freed := c_num_freed r1 + new_cnt in
          ensure_free_array st1 c total_freed (fun st2 ok =>
            if negb ok then k st2 false else
            k (put_cls c (cls_set_allocated_user (c_allocated_user (get_cls st2 c) + new_cnt * size) (cls_set_num_freed total_freed (get_cls st2 c))) st2) true)) mo1 P).
  { intros st1 mo1 HI1 HSB1 Hcnt1 Hnf1 Hal1 Hen1 HSB2. cbv zeta.
    pose proof HI1 as [HA1 HM1]. pose proof (AINV_cls _ _ _ _ HA1 Hc) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12). rewrite <- Hsize in D10, D11.
    pose proof (carve_facts (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) size ltac:(lia) ltac:(lia)) as (Q0 & Qcv & Qrest).
    pose proof (carve_enough_nomap (c_mapped_user (get_cls st1 c)) (c_allocated_user (get_cls st1 c)) size req ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hcarve.
    set (q := (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size) in *. set (cv := q * size) in *.
    assert (Hcnt0 : 0 <= cntP c (all_chunks pc pb st1) + nbatch c (qbatches pb st1)).
    { pose proof (cntP_nonneg c (all_chunks pc pb st1)). unfold nbatch. destruct (c =? K_BATCH_CLASS); [pose proof (zlen_nonneg (qbatches pb st1))|]; lia. }
    assert (HV2 : size * (c_count (get_cls st1 c) + (c_num_freed (get_cls st1 c) + q)) <= UNUSED_MAX).
    { rewrite Hcnt1, Hnf1. replace (size * (c_count (get_cls st c) + (c_num_freed (get_cls st c) + q)))
        with (size * (c_count (get_cls st c) + c_num_freed (get_cls st c)) + cv) by (unfold cv; ring).
      unfold UNUSED_MAX. lia. }
    assert (Hnf' : 4 * (c_num_freed (get_cls st1 c) + q) <= K_FREEARR_MAP).
    { assert (H0 : 0 <= size * c_count (get_cls st1 c)) by (apply Z.mul_nonneg_nonneg; lia).
      assert (H1 : size * (c_num_freed (get_cls st1 c) + q) <= UNUSED_MAX).
      { replace (size * (c_count (get_cls st1 c) + (c_num_freed (get_cls st1 c) + q)))
          with (size * c_count (get_cls st1 c) + size * (c_num_freed (get_cls st1 c) + q)) in HV2 by ring. lia. }
      assert (H2 : 32 * (c_num_freed (get_cls st1 c) + q) <= UNUSED_MAX).
      { apply Z.le_trans with (size * (c_num_freed (get_cls st1 c) + q)); [apply Z.mul_le_mono_nonneg_r; lia| lia]. }
      unfold UNUSED_MAX, K_USER_MAP, K_FREEARR_MAP in *. lia. }
    assert (Hcv : cv = q * size) by reflexivity. clearbody cv q.
    apply (ensure_ok R P pc pb st1 c (c_num_freed (get_cls st1 c) + q) _ mo1 HI1 Hc ltac:(lia) Hnf' HSB2).
    intros st2 mo2 HI2 HSB12 E1 E2 E3 E4 E5. cproj.
    pose proof HI2 as [HA2 HM2].
    assert (AC : all_chunks pc pb st2 = all_chunks pc pb st1 /\ qbatches pb st2 = qbatches pb st1).
    { destruct HSB12 as (_&_&_&_&_&Hl&_&Hq1&_&Hq2&_&_). unfold all_chunks, qbatches, live_chunks. rewrite Hl, Hq1, Hq2. split; reflexivity. }
    destruct AC as [AC1 AC2].
    apply Hk.
    - split.
      + apply AINV_put_cls; [exact HA2| exact Hc|].
        pose proof (AINV_cls _ _ _ _ HA2 Hc) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
        unfold CLSOK. cproj. rewrite <- Hsize. rewrite AC1, AC2. rewrite E1, E2, E3, E4 in *.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact D5|]. split; [exact F6|]. split; [exact F7|].
        split; [lia|]. split; [exact F9|]. rewrite <- Hsize in F10. rewrite AC1, AC2 in F10.
        split; [rewrite F10, Hcv; ring|]. split; [exact HV2| exact F12].
      + rewrite CH_put. apply (AMI_mono _ st2); auto. rewrite commit_bytes_put by exact Hc. unfold cls_mapped_bytes'. cproj. lia.
    - eapply same_but_trans; [exact HSB1|]. eapply same_but_trans; [exact HSB12| apply same_but_put].
    - rewrite get_put_eq. cproj. congruence.
    - rewrite get_put_eq. cproj. lia. }
  unfold populate_free_array. rewrite <- Hsize. cbv zeta.
  destruct (Z.leb_spec (c_allocated_user (get_cls st c) + req * size) (c_mapped_user (get_cls st c))) as [Hen|Hmap].
  { apply (TAIL st mo HI (same_but_refl c st)); auto. }
  assert (Hums : rup (c_allocated_user (get_cls st c) + req * size - c_mapped_user (get_cls st c)) K_USER_MAP = K_USER_MAP).
  { apply rup_small; unfold K_USER_MAP in *; lia. }
  rewrite Hums.
  destruct (Z.ltb_spec K_FREEARR_OFF (c_mapped_user (get_cls st c) + K_USER_MAP)) as [Hex|Hok]; [unfold K_USER_MAP, K_FREEARR_OFF in *; lia|].
  destruct (Z.ltb_spec UWIN (c_mapped_user (get_cls st c) + K_USER_MAP + 64)) as [Hwin|Hwin].
  { exfalso. pose proof (cls_user_W ATOP pc pb st c HA Hc) as CW. unfold vroom, WPCAP in HSB.
    unfold CLS_SLACK, UNUSED_MAX, K_USER_MAP, K_FREEARR_MAP, UWIN in *. change (2 ^ 30) with 1073741824 in HSB. change (2 ^ 22) with 4194304 in HSB. lia. }
  pose proof (vroom_L _ _ _ HSB) as HSBL.
  set (a := region_beg st c + c_mapped_user (get_cls st c)).
  assert (Hc32 : 0 <= c * 2^32 <= 31 * 2^32) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
  assert (Dsb : (4096 | a_space_beg st)) by (apply (div4096_of_mod _ 65536); [apply div_65536| lia| exact G1]).
  assert (Dmu : (4096 | c_mapped_user (get_cls st c))) by (apply (div4096_of_mod _ 262144); [apply div_262144| lia| unfold K_USER_MAP in C5; exact C5]).
  assert (Ham : a mod 4096 = 0).
  { apply divide_mod0; [lia|]. unfold a, region_beg, K_REGION. apply Z.divide_add_r; [|exact Dmu]. apply Z.divide_add_r; [exact Dsb|].
    replace (c * 2 ^ 32) with ((c * 2^20) * 4096) by lia. apply div_lit. }
  assert (HE1 : pb0 <= a) by (unfold a, region_beg, K_REGION; lia).
  assert (HE2 : a + K_USER_MAP <= pb0 + PRIM_SZ) by (unfold a, region_beg, K_REGION, K_FREEARR_OFF, K_USER_MAP, PRIM_SZ in *; lia).
  assert (HBS : B (went (pb0, PRIM_SZ)) = pb0 /\ S (went (pb0, PRIM_SZ)) = PRIM_SZ).
  { unfold B, S, went. cbn [fst snd]. unfold ACEIL, PRIM_SZ, KHIGH in *. rewrite !unsigned_lit by lia. lia. }
  destruct HBS as [HB1 HS1].
  unfold ev. apply atotal_vis.
  - apply (INV_fixed_aok_high pc pb st mo (went (pb0, PRIM_SZ))); auto; try lia; [unfold RES_HI, KHIGH in *; lia| unfold K_USER_MAP; lia].
  - intros z mo' Hpost. cbn [apost] in Hpost.
    assert (Hanz : (a =? 0) = false) by (apply Z.eqb_neq; unfold KHIGH in *; lia).
    rewrite Hanz in Hpost. destruct Hpost as [-> ->].
    rewrite fixed_answer_ok_self. cbn [negb].
    rewrite is_err_small by (unfold TWO64, ACEIL, KHIGH, PRIM_SZ, K_USER_MAP in *; lia).
    assert (ML : mmap_len K_USER_MAP = K_USER_MAP) by reflexivity. rewrite ML.
    set (st1 := put_cls c (cls_set_mapped_user (c_mapped_user (get_cls st c) + K_USER_MAP) (get_cls st c)) st).
    assert (HI1 : INV pc pb st1 (fixed_model mo F_FIXED a K_USER_MAP)).
    { split.
      + apply AINV_put_cls; [exact HA| exact Hc|]. unfold CLSOK. cproj. rewrite <- Hsize. repeat split; try (unfold K_USER_MAP in *; lia).
        all: unfold K_USER_MAP in *; rewrite <- Zplus_mod_idemp_l, C5; reflexivity.
      + unfold st1. rewrite CH_put. apply (AMI_commit _ st _ _ (went (pb0, PRIM_SZ))); auto; try lia; try reflexivity.
        all: try (unfold K_USER_MAP; lia).
        all: rewrite commit_bytes_put by exact Hc; unfold cls_mapped_bytes'; cproj; unfold K_USER_MAP; lia. }
    assert (Er1 : get_cls st1 c = cls_set_mapped_user (c_mapped_user (get_cls st c) + K_USER_MAP) (get_cls st c)) by (unfold st1; apply get_put_eq).
    apply (TAIL st1 (fixed_model mo F_FIXED a K_USER_MAP) HI1); try (rewrite Er1; cproj; lia).
    + unfold st1. apply same_but_put.
    + unfold st1. apply vroom_put. exact HSB.
Qed.

Lemma max_count_same_but : forall c st1 st2 c', same_but c st1 st2 -> max_count st2 c' = max_count st1 c'.
Proof. intros c st1 st2 c' H. destruct H as (_&_&_&_&Hci&_). unfold max_count. rewrite Hci. reflexivity. Qed.

Lemma all_chunks_cons : forall ch pc pb st, all_chunks (ch :: pc) pb st = ch :: all_chunks pc pb st. Proof. reflexivity. Qed.
Lemma qbatches_cons : forall b pb st, qbatches (b :: pb) st = b :: qbatches pb st. Proof. reflexivity. Qed.
Lemma CH_cons : forall ch pc pb st, CH (ch :: pc) pb st = sec_of ch ++ CH pc pb st. Proof. reflexivity. Qed.

Lemma CH_repc : forall pc pc' pb st, secs pc' = secs pc -> CH pc' pb st = CH pc pb st.
Proof. intros. unfold CH, all_chunks. rewrite !secs_app, H. reflexivity. Qed.

Lemma AINV_repc : forall pc pc' pb st c r',
  AINV pc pb st -> 1 <= c <= 31 ->
  Forall chunk_wf pc' ->
  (forall c', 1 <= c' <= 31 -> c' <> c -> cntP c' pc' = cntP c' pc) -> secs pc' = secs pc ->
  CLSOK pc' pb st c r' -> AINV pc' pb (put_cls c r' st).
Proof.
  intros pc pc' pb st c r' H Hc Hwf Hcnt Hsec HR. unfold AINV in *.
  destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array put_cls set_cls] in *.
  rewrite (CH_put pc' pb c r' st), (CH_repc pc pc' pb st Hsec).
  split.
  { intros c' Hc'. unfold cls_inv. rewrite max_count_put, all_chunks_put, qbatches_put.
    destruct (Z.eq_dec c' c) as [->|Hne].
    - rewrite get_put_eq. exact HR.
    - rewrite get_put_ne by congruence. pose proof (HC c' Hc') as X. unfold cls_inv in X.
      unfold all_chunks in *. rewrite !cntP_app in *. rewrite (Hcnt c' Hc' Hne). exact X. }
  split.
  { rewrite all_chunks_put. unfold all_chunks in *. apply Forall_app in H2 as [_ H2]. apply Forall_app. split; assumption. }
  rewrite qbatches_put. repeat (split; [assumption|]). assumption.
Qed.

Lemma INV_repc : forall pc pc' pb st c r' mo,
  INV pc pb st mo -> 1 <= c <= 31 ->
  Forall chunk_wf pc' ->
  (forall c', 1 <= c' <= 31 -> c' <> c -> cntP c' pc' = cntP c' pc) -> secs pc' = secs pc ->
  CLSOK pc' pb st c r' -> cls_mapped_bytes' (get_cls st c) <= cls_mapped_bytes' r' ->
  INV pc' pb (put_cls c r' st) mo.
Proof.
  intros pc pc' pb st c r' mo [HA HM] Hc Hwf Hcnt Hsec HR Hmono. split.
  - apply AINV_repc with (pc := pc); assumption.
  - rewrite CH_put, (CH_repc pc pc' pb st Hsec). apply (AMI_mono _ st); auto. rewrite commit_bytes_put by exact Hc. lia.
Qed.

Lemma AINV_init_cache : forall pc pb st, AINV pc pb st -> AINV pc pb (init_cache st).
Proof.
  intros pc pb st H. unfold init_cache. destruct (a_cinit st) eqn:E; [exact H|].
  unfold AINV in *. destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_cinit a_cinit] in *.
  split; [| repeat (split; [assumption|]); assumption].
  intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold max_count in *. cbn [a_cinit set_cinit] in *. rewrite E in X.
  unfold get_cls in *. cbn [a_cls set_cinit] in *.
  unfold all_chunks, qbatches, live_chunks in *. cbn [a_live a_qloc a_qglob set_cinit] in *.
  pose proof (primary_class_facts 0 ltac:(lia) eq_refl) as _.
  assert (0 <= max_cached c) by (unfold max_cached; lia). lia.
Qed.

Lemma INV_init_cache : forall pc pb st mo, INV pc pb st mo -> INV pc pb (init_cache st) mo.
Proof.
  intros pc pb st mo [HA HM]. split; [apply AINV_init_cache; exact HA|].
  rewrite CH_init_cache. apply (AMI_mono _ st); auto.
  - unfold init_cache; destruct (a_cinit st); reflexivity.
  - unfold init_cache; destruct (a_cinit st); reflexivity.
  - rewrite commit_bytes_init_cache. lia.
Qed.

Lemma same_but_init_cache : forall c st, same_but c (init_cache st) st \/ True. Proof. intros. right. exact I. Qed.

Lemma cache_alloc_ok : forall R (P : R -> Model -> Prop) pc pb st c n (k : astate -> bool -> AM R) mo,
  INV pc pb st mo -> 0 <= n -> is_primary n = true -> c = class_id (needed_size n) ->
  size_of_class c * (cntP c (all_chunks pc pb st) + nbatch c (qbatches pb st) + 8) + 2^20 <= K_FREEARR_OFF ->
  vroom pc pb st ->
  (forall st' mo', INV (CPrim c n :: pc) pb st' mo' -> (same_but c st st' \/ same_but c (init_cache st) st') ->
     atot (k st' true) mo' P) ->
  atot (cache_alloc st c k) mo P.
Proof.
  intros R P pc pb st c n k mo HI Hn Hp Hcl Hroom HSB Hk.
  pose proof (primary_class_facts n Hn Hp) as F. cbv zeta in F. rewrite <- Hcl in F. destruct F as (F1 & F2 & F3 & F4 & F5 & F6).
  assert (Hc : 1 <= c <= 31) by lia.
  assert (Hwf : chunk_wf (CPrim c n)).
  { cbn. split; [|exact Hcl]. split; [lia|]. destruct (Z_lt_dec 64512 n) as [Hlt|]; [|lia]. rewrite (large_not_primary n Hlt) in Hp. discriminate. }
  pose proof HI as [HA HM]. pose proof (AINV_cls _ _ _ _ HA Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
  assert (Hcnt0 : 0 <= cntP c (all_chunks pc pb st) /\ 0 <= nbatch c (qbatches pb st)).
  { split; [apply cntP_nonneg|]. unfold nbatch. destruct (c =? K_BATCH_CLASS); [apply zlen_nonneg| lia]. }
  assert (REPC : forall st0 r', INV pc pb st0 mo -> all_chunks pc pb st0 = all_chunks pc pb st -> qbatches pb st0 = qbatches pb st ->
            CLSOK (CPrim c n :: pc) pb st0 c r' -> cls_mapped_bytes' (get_cls st0 c) <= cls_mapped_bytes' r' ->
            INV (CPrim c n :: pc) pb (put_cls c r' st0) mo).
  { intros st0 r' HI0 E1 E2 HR Hm. apply (INV_repc pc); auto.
    - constructor; [exact Hwf|]. destruct HA as (_ & Hall & _). unfold all_chunks in Hall. apply Forall_app in Hall as [Hpc _]. exact Hpc.
    - intros c' Hc' Hne. rewrite cntP_cons. cbn [is_prim_of]. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; lia). lia. }
  unfold cache_alloc. cbv zeta.
  destruct (Z.ltb_spec 0 (c_count (get_cls st c))) as [Hpos|Hz].
  -
    apply Hk; [|left; apply same_but_put].
    apply REPC; auto. all: try (unfold cls_mapped_bytes'; cproj; lia).
    unfold CLSOK. cproj. rewrite all_chunks_cons, cntP_cons. cbn [is_prim_of]. rewrite Z.eqb_refl. repeat split; try lia.
  - rewrite max_count_init_cache, get_cls_init_cache.
    assert (Hhalf : 1 <= max_cached c / 2 <= 8 /\ 2 * (max_cached c / 2) <= max_cached c).
    { split. split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; lia. apply Z.mul_div_le; lia. }
    set (m := max_cached c / 2) in *. clearbody m.
    pose proof (INV_init_cache _ _ _ _ HI) as HI1.
    assert (Hcz : c_count (get_cls st c) = 0) by lia. rewrite Hcz in C11.
    destruct (Z.leb_spec m (c_num_freed (get_cls st c))) as [Hen|Hlt].
    +
      destruct (Z.ltb_spec (c_num_freed (get_cls st c)) m); [lia|].
      apply Hk; [|right; apply same_but_put].
      apply REPC; auto; rewrite ?all_chunks_init_cache, ?qbatches_init_cache, ?get_cls_init_cache; try reflexivity.
      all: try (unfold cls_mapped_bytes'; cproj; lia).
      unfold CLSOK. cproj. rewrite max_count_init_cache, all_chunks_init_cache, qbatches_init_cache, all_chunks_cons, cntP_cons. cbn [is_prim_of]. rewrite Z.eqb_refl. repeat split; try lia.
    +
      apply (populate_ok R P pc pb (init_cache st) c (m - c_num_freed (get_cls st c)) _ mo HI1 Hc ltac:(lia) ltac:(lia)).
      * rewrite get_cls_init_cache || idtac. apply Z.le_trans with (m * size_of_class c); [apply Z.mul_le_mono_nonneg_r; lia| lia].
      * rewrite get_cls_init_cache. rewrite C10.
        assert (size_of_class c * c_num_freed (get_cls st c) <= size_of_class c * 8) by (apply Z.mul_le_mono_nonneg_l; lia).
        assert (size_of_class c * c_count (get_cls st c) = 0) by (replace (c_count (get_cls st c)) with 0 by lia; ring).
        first [clear - Hroom H H0; lia | nia || lia].
      * apply vroom_init_cache. exact HSB.
      * rewrite get_cls_init_cache, Hcz.
        apply Z.le_trans with (size_of_class c * m); [apply Z.mul_le_mono_nonneg_l; lia| lia].
      * intros st2 mo2 HI2 HSB2 Ecnt Enf. rewrite get_cls_init_cache in Ecnt, Enf.
        destruct (Z.ltb_spec (c_num_freed (get_cls st2 c)) m); [lia|].
        pose proof HI2 as [HA2 HM2]. pose proof (AINV_cls _ _ _ _ HA2 Hc) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12).
        rewrite Ecnt, Hcz in D11.
        assert (AC : all_chunks pc pb st2 = all_chunks pc pb st /\ qbatches pb st2 = qbatches pb st).
        { destruct HSB2 as (_&_&_&_&_&Hl&_&Hq1&_&Hq2&_&_). unfold all_chunks, qbatches, live_chunks. unfold init_cache in Hl, Hq1, Hq2.
          destruct (a_cinit st); cbn in Hl, Hq1, Hq2; rewrite Hl, Hq1, Hq2; split; reflexivity. }
        destruct AC as [AC1 AC2].
        apply Hk. 2:{ right. eapply same_but_trans; [exact HSB2| apply same_but_put]. }
        apply (INV_repc pc); auto.
        -- constructor; [exact Hwf|]. destruct HA as (_ & Hall & _). unfold all_chunks in Hall. apply Forall_app in Hall as [Hpc _]. exact Hpc.
        -- intros c' Hc' Hne. rewrite cntP_cons. cbn [is_prim_of]. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; first [exact (not_eq_sym Hne) | lia]). lia.
        -- unfold CLSOK. cproj. rewrite all_chunks_cons, cntP_cons. cbn [is_prim_of]. rewrite Z.eqb_refl. rewrite AC1, AC2 in D10. rewrite AC1, AC2.
           rewrite (max_count_same_but _ _ _ c HSB2), max_count_init_cache in *. repeat split; try lia.
        -- unfold cls_mapped_bytes'. cproj. lia.
Qed.

Lemma AMI_perm : forall ch ch' st mo, Permutation ch ch' -> AMI ch st mo -> AMI ch' st mo.
Proof.
  intros ch ch' st mo HP H. destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HPm & HS & HB).
  unfold AsanInv.AMI. repeat (split; [assumption|]). exists L0. split; [|split; assumption].
  eapply Permutation_trans; [exact HPm|]. apply Permutation_app_head. apply Permutation_map. exact HP.
Qed.

Lemma AINV_live_perm : forall pc pc' pb st lv nx,
  AINV pc pb st ->
  Permutation (all_chunks pc' pb (set_next nx (set_live lv st))) (all_chunks pc pb st) ->
  (forall id ch, lv !! id = Some ch -> (id < nx)%N) ->
  live_budget (set_next nx (set_live lv st)) ->
  AINV pc' pb (set_next nx (set_live lv st)).
Proof.
  intros pc pc' pb st lv nx H HP Hid HLB. unfold AINV in *.
  destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_next set_live a_cinit] in *.
  assert (Hq : qbatches pb (set_next nx (set_live lv st)) = qbatches pb st) by reflexivity.
  assert (HCH : zlen (CH pc' pb (set_next nx (set_live lv st))) = zlen (CH pc pb st)).
  { unfold CH, zlen. f_equal. apply Permutation_length. apply secs_perm. exact HP. }
  split.
  { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_next set_live] in *.
    rewrite Hq, (cntP_perm c _ _ HP). exact X. }
  split. { eapply Permutation_Forall; [apply Permutation_sym; exact HP| exact H2]. }
  rewrite Hq, HCH. repeat (split; [assumption|]). exact HLB.
Qed.

Lemma INV_hand_to_live : forall ch pc pb st mo,
  INV (ch :: pc) pb st mo ->
  live_budget_list (ch :: live_chunks st) ->
  INV pc pb (set_next (N.succ (a_next st)) (set_live (<[a_next st := ch]> (a_live st)) st)) mo.
Proof.
  intros ch pc pb st mo [HA HM] HLB.
  assert (Hnone : (a_live st) !! (a_next st) = None).
  { destruct ((a_live st) !! (a_next st)) as [ch0|] eqn:E; [|reflexivity]. exfalso.
    destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). specialize (Hid _ _ E). lia. }
  pose proof (live_chunks_insert st (a_next st) ch Hnone) as HPl.
  assert (HP : Permutation (all_chunks pc pb (set_next (N.succ (a_next st)) (set_live (<[a_next st := ch]> (a_live st)) st))) (all_chunks (ch :: pc) pb st)).
  { unfold all_chunks. cbn [app]. unfold live_chunks in *. cbn [a_live set_next set_live] in *.
    change (qbatches pb (set_next (N.succ (a_next st)) (set_live (<[a_next st:=ch]> (a_live st)) st))) with (qbatches pb st).
    eapply Permutation_trans. { apply Permutation_app_head. apply Permutation_app_tail. exact HPl. }
    rewrite app_comm_cons. apply Permutation_sym. cbn. apply Permutation_middle. }
  split.
  - apply (AINV_live_perm (ch :: pc)); auto.
    + intros id ch0 Hl. destruct (N.eq_dec id (a_next st)) as [->|Hne]; [lia|].
      rewrite lookup_insert_ne in Hl by congruence. destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). specialize (Hid _ _ Hl). lia.
    + apply live_budget_list_iff. unfold live_chunks. cbn [a_live set_next set_live]. unfold live_chunks in HPl. cbn [a_live set_live] in HPl.
      destruct HLB as (B1 & B2 & B3). split; [|split].
      * intros c Hc. rewrite (cntP_perm c _ _ HPl). apply B1. exact Hc.
      * unfold zlen in *. rewrite (Permutation_length (secs_perm _ _ HPl)). exact B2.
      * assert (E : forall l l', Permutation l l' -> secbytes l = secbytes l').
        { intros l l' P0. induction P0; cbn; try lia. - destruct x; lia. - destruct x, y; lia. }
        rewrite (E _ _ HPl). exact B3.
  - apply (AMI_perm (CH (ch :: pc) pb st)).
    + unfold CH. apply secs_perm. apply Permutation_sym. exact HP.
    + apply (AMI_mono _ st); auto. apply Z.le_refl || (unfold commit_bytes, csum, get_cls; cbn; lia).
Qed.

Lemma rdn_le : forall x a, 0 < a -> rdn x a <= x. Proof. intros. unfold rdn. rewrite Z.mul_comm. apply Z.mul_div_le. lia. Qed.
Lemma rdn_mod : forall x a, 0 < a -> rdn x a mod a = 0. Proof. intros. unfold rdn. apply Z_mod_mult. Qed.

Lemma poison0_ok : forall R (P : R -> Model -> Prop) pc pb st (k : AM R) mo a s,
  INV pc pb st mo -> 0 <= a -> 0 <= s <= 2^31 ->
  (a + s <= LS_LO \/ (KHIGH <= a /\ a + s <= ATOP)) ->
  zsum2 (CH pc pb st) <= 2^35 ->
  (forall mo', INV pc pb st mo' -> atot k mo' P) ->
  atot (poison0 a s k) mo P.
Proof.
  intros R P pc pb st k mo a s HI Ha Hs Hrange HSB Hk. unfold poison0. apply Hk. exact HI.
Qed.

Lemma grant_range : forall pc pb st mo z n,
  INV pc pb st mo -> 0 < z -> 0 < n -> z + n <= ATOP ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 n) = true ->
  z + n <= LS_LO \/ (KHIGH <= z /\ z + n <= ATOP).
Proof.
  intros pc pb st mo z n HI Hz Hn Hce Hrf.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  destruct (INV_shadows _ _ _ _ HI) as (HinLS & HinGAP & HinHS).
  rewrite region_free_app in Hrf. apply andb_true_iff in Hrf as [_ Hrf].
  pose proof (region_free_wsep _ _ _ Hrf) as HW. rewrite Forall_forall in HW.
  pose proof (HW _ HinLS) as W1. pose proof (HW _ HinGAP) as W2. pose proof (HW _ HinHS) as W3.
  unfold wsep, went in W1, W2, W3. cbn [fst snd] in W1, W2, W3.
  unfold ACEIL, LS_LO, LS_SZ, GAP_LO, GAP_SZ, HS_LO, HS_SZ, KHIGH in *. rewrite !unsigned_lit in W1, W2, W3 by lia. lia.
Qed.

Lemma filter_perm : forall {A} (f : A -> bool) l l', Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros A f l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn.
  - constructor.
  - destruct (f x); [apply perm_skip|]; exact IH.
  - destruct (f y), (f x); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.
Lemma zsizes_perm : forall l l', Permutation l l' -> zsizes l = zsizes l'.
Proof. intros l l' HP. induction HP; cbn; lia. Qed.
Lemma zsizes_filter_le : forall f l, Forall (fun e => 0 <= snd e) l -> zsizes (List.filter f l) <= zsizes l.
Proof. induction l as [|e l IH]; intros HF; cbn; [lia|]. apply Forall_cons_iff in HF as [He HF]. specialize (IH HF). destruct (f e); cbn; lia. Qed.
Lemma filter_none : forall {A} (f : A -> bool) l, Forall (fun x => f x = false) l -> List.filter f l = [].
Proof. induction l as [|x l IH]; intros HF; cbn; [reflexivity|]. apply Forall_cons_iff in HF as [Hx HF]. rewrite Hx. apply IH. exact HF. Qed.
Lemma zsizes_zent_went : forall ch, Forall (fun e => 0 <= snd e < 2^64) ch -> Forall (fun e => 0 <= fst e < 2^64) ch ->
  zsizes (map zent (map went ch)) = zsum2 ch.
Proof.
  induction ch as [|[mb ms] ch IH]; intros H1 H2; cbn -[Z_to_bv bv_unsigned Z.pow]; [reflexivity|].
  apply Forall_cons_iff in H1 as [A1 H1]. apply Forall_cons_iff in H2 as [A2 H2]. cbn [fst snd] in A1, A2.
  rewrite unsigned_lit by lia. rewrite (IH H1 H2). reflexivity.
Qed.

Lemma achunks_all_chunks : forall pc pb st ch, In ch (achunks st) -> In ch (all_chunks pc pb st).
Proof.
  intros pc pb st ch Hin. unfold achunks, all_chunks, live_chunks, qchunks, qbatches in *.
  apply in_app_iff. right. apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; exact Hin| right].
  apply in_flat_map in Hin as (b & Hb & Hin). apply in_flat_map. exists b. split; [|exact Hin]. apply in_app_iff. right. exact Hb.
Qed.

Lemma grant_avoids : forall pc pb st mo z len,
  INV pc pb st mo -> 0 < z -> 0 < len -> z + len <= ATOP ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 len) = true ->
  avoids_all z len (RESV ++ asec_ranges st) = true.
Proof.
  intros pc pb st mo z len HI Hz Hlen Hce Hrf.
  pose proof HI as [HA HM]. pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HPm & HS & HB).
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRC).
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  assert (ZL : 0 <= z < 2^64 /\ 0 <= len < 2^64) by lia.
  assert (RF : forall e, In e (vm_reserved (m_vmmaps mo) ++ L0 ++ map went (CH pc pb st)) ->
               z + len <= bv_unsigned (fst e) \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= z).
  { intros [b sz] He. pose proof (region_free_In _ _ _ b sz Hrf) as X. rewrite !unsigned_lit in X by lia. cbn [fst snd]. apply X.
    apply in_app_iff in He as [He|He]; apply in_app_iff; [left; exact He| right].
    eapply Permutation_in; [apply Permutation_sym; exact HPm| exact He]. }
  unfold avoids_all. apply forallb_forall. intros [lo hi] Hin. unfold iv_clear. cbn [fst snd].
  apply in_app_iff in Hin as [Hin|Hin].
  -
    destruct (proj1 (Forall_forall _ _) HRC _ Hin) as (e & He & C1 & C2). cbn [fst snd] in C1, C2.
    specialize (RF e ltac:(rewrite app_assoc; apply in_app_iff; left; exact He)).
    apply orb_true_iff. destruct RF as [X|X]; [left| right]; apply Z.leb_le; lia.
  -
    unfold asec_ranges in Hin. apply in_flat_map in Hin as (ch & Hch & Hin).
    destruct ch as [c n|mb ms n]; cbn in Hin; [destruct Hin|]. destruct Hin as [E|[]]. injection E as <- <-.
    pose proof (achunks_all_chunks pc pb st _ Hch) as Hall.
    assert (HinCH : In (mb, ms) (CH pc pb st)).
    { unfold CH, secs. apply in_flat_map. exists (CSec mb ms n). split; [exact Hall| cbn; left; reflexivity]. }
    destruct HA as (_ & HW & _). pose proof (proj1 (Forall_forall _ _) HW _ Hall) as Hwf. cbn in Hwf.
    destruct Hwf as (Hn' & Hms & Hwf). pose proof (sec_map_size_bounds n ltac:(lia)). unfold LS_LO, KHIGH, ACEIL in Hwf.
    specialize (RF (went (mb, ms)) ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_map; exact HinCH)).
    unfold went in RF. cbn [fst snd] in RF. rewrite !unsigned_lit in RF by lia.
    apply orb_true_iff. destruct RF as [X|X]; [left| right]; apply Z.leb_le; lia.
Qed.

Lemma large_alloc_ok : forall R (P : R -> Model -> Prop) pc pb st n (k : astate -> option achunk -> AM R) mo,
  INV pc pb st mo -> 64512 < n <= 2^29 ->
  W pc pb st + 2 * n + 128 <= WCAP -> zlen (CH pc pb st) <= 5330 ->
  (forall st' mo' mb, INV (CSec mb (sec_map_size n) n :: pc) pb st' mo' ->
      (st' = set_nsec (a_nsec st + 1) st \/ st' = set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) ->
      atot (k st' (Some (CSec mb (sec_map_size n) n))) mo' P) ->
  atot (large_alloc ATOP RESV st n k) mo P.
Proof.
  intros R P pc pb st n k mo HI Hn HSB HSL Hk.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  pose proof (sec_map_size_bounds n ltac:(lia)) as SB.
  assert (MSA : sec_map_size n mod 4096 = 0).
  { unfold sec_map_size, rup, PG. match goal with |- ?x mod 4096 = 0 => replace x with ((((needed_size n + 4096 - 1) / 4096) + 1) * 4096) by lia end. apply Z_mod_mult. }
  unfold large_alloc. unfold ev. apply atotal_vis.
  { apply (INV_grant_aok pc pb st mo n HI ltac:(lia)); [unfold vroomL; lia| lia]. }
  intros z mo' Hpost. cbn [apost] in Hpost. rewrite Z.eqb_refl in Hpost.
  assert (ML : mmap_len (sec_map_size n) = sec_map_size n) by (apply mmap_len_id; lia). rewrite ML in Hpost.
  destruct Hpost as (Z1 & Z2 & Z3 & Z4 & ->).
  assert (RUP : rup (sec_map_size n) PG = sec_map_size n).
  { unfold rup, PG. pose proof (Z.div_mod (sec_map_size n) 4096 ltac:(lia)) as Hd. rewrite MSA in Hd.
    replace (sec_map_size n + 4096 - 1) with (sec_map_size n / 4096 * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. change (4095/4096) with 0. lia. }
  assert (Hok : mmap_answer_ok ATOP (sec_map_size n) z = true).
  { unfold mmap_answer_ok. rewrite RUP. apply orb_true_iff. right. unfold TWO64, PG.
    rewrite (proj2 (Z.ltb_lt 0 z)) by lia. rewrite Z1. cbn [Z.eqb andb]. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  rewrite Hok. cbn [negb]. rewrite is_err_small by (unfold TWO64; lia).
  pose proof (grant_range pc pb st mo z (sec_map_size n) HI Z2 ltac:(lia) Z3 Z4) as Hrange.
  pose proof (grant_avoids pc pb st mo z (sec_map_size n) HI Z2 ltac:(lia) Z3 Z4) as HAV.
  rewrite HAV. cbn [andb negb].
  set (ch := CSec z (sec_map_size n) n).
  set (st1 := set_nsec (a_nsec st + 1) st).
  assert (HI1 : INV (ch :: pc) pb st1 (grant_model mo z (sec_map_size n))).
  { destruct HI as [HA HM]. split.
    - unfold AINV in *. destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
      unfold st1. cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_nsec a_cinit] in *.
      rewrite all_chunks_set_nsec, all_chunks_cons.
      change (qbatches pb (set_nsec (a_nsec st + 1) st)) with (qbatches pb st).
      change (CH (ch :: pc) pb (set_nsec (a_nsec st + 1) st)) with (sec_of ch ++ CH pc pb st).
      split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_nsec] in *.
               rewrite all_chunks_set_nsec, all_chunks_cons, cntP_cons. cbn [is_prim_of]. change (qbatches pb (set_nsec (a_nsec st + 1) st)) with (qbatches pb st). rewrite Z.add_0_l. exact X. }
      split. { constructor; [|exact H2]. cbn. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. exact Hrange. }
      split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
      split. { unfold ch. cbn [sec_of app]. rewrite zlen_cons. lia. }
      split; [exact H7|]. split; [exact H8|]. unfold live_budget, live_chunks in *. cbn [a_live set_nsec]. exact H9.
    - unfold st1. change (CH (ch :: pc) pb (set_nsec (a_nsec st + 1) st)) with ((z, sec_map_size n) :: CH pc pb st).
      apply (AMI_mono _ st); try reflexivity; try (unfold commit_bytes, csum, get_cls; cbn; lia).
      apply AMI_grant; auto; lia. }
  destruct (Z.eqb_spec (a_nsec st) (a_nres st)) as [Heq|Hne].
  2:{ apply Hk; [exact HI1| left; reflexivity]. }
  destruct HI as [HA HM]. pose proof HA as (_ & _ & _ & _ & _ & Hnsec & Hres & _).
  assert (Hres0 : a_nres st = 0) by (destruct Hres as [?|E]; [assumption|]; rewrite E in Heq; unfold K_CHUNKS_BLOCK in Heq; lia).
  rewrite Hres0 in Hk |- *. destruct (Z.ltb_spec K_PTRARR_RESERVE (8 * (0 + K_CHUNKS_BLOCK))) as [X|_]; [unfold K_PTRARR_RESERVE, K_CHUNKS_BLOCK in X; lia|].
  destruct (INV_ptr _ _ _ _ HI1) as (HinP & P2 & PRF). unfold st1 in HinP, P2, PRF. cbn [a_ptr_array set_nsec] in HinP, P2, PRF.
  destruct (AINV_geom _ _ _ HA) as (_ & _ & G3 & G4).
  rewrite Z.mul_0_r, Z.add_0_r.
  assert (HBS : B (went (a_ptr_array st, PTR_SZ)) = a_ptr_array st /\ S (went (a_ptr_array st, PTR_SZ)) = PTR_SZ).
  { unfold B, S, went. cbn [fst snd]. unfold ACEIL, PTR_SZ, KHIGH in *. rewrite !unsigned_lit by lia. lia. }
  destruct HBS as [HB1 HS1].
  apply atotal_vis.
  { apply (INV_fixed_aok _ _ _ _ (went (a_ptr_array st, PTR_SZ)) _ _ HI1); auto; try lia.
    - rewrite HB1, HS1. unfold K_PTRARR_COMMIT, PTR_SZ. lia.
    -
      apply (region_free_sub _ (a_ptr_array st) PTR_SZ); [exact PRF| | | | |]; unfold K_PTRARR_COMMIT, PTR_SZ in *; lia.
    - unfold K_PTRARR_COMMIT. lia.
    - unfold vroomL. rewrite (W_same (ch :: pc) pb st st1) by reflexivity. rewrite W_cons. unfold ch. cbn [chunk_size]. lia. }
  intros z2 mo2 Hpost2. cbn [apost] in Hpost2.
  assert (Hpz : (a_ptr_array st =? 0) = false) by (apply Z.eqb_neq; lia). rewrite Hpz in Hpost2. destruct Hpost2 as [-> ->].
  rewrite fixed_answer_ok_self. cbn [negb]. rewrite is_err_small by (unfold TWO64, ACEIL, KHIGH, PTR_SZ in *; lia).
  apply Hk; [| right; reflexivity].
  assert (ML2 : mmap_len K_PTRARR_COMMIT = K_PTRARR_COMMIT) by reflexivity. rewrite ML2.
  destruct HI1 as [HA1 HM1]. split.
  - unfold AINV in *. destruct HA1 as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
    unfold st1 in *. cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_nsec set_nres a_cinit] in *.
    change (all_chunks (ch :: pc) pb (set_nres (0 + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))) with (all_chunks (ch :: pc) pb (set_nsec (a_nsec st + 1) st)).
    change (qbatches pb (set_nres (0 + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))) with (qbatches pb (set_nsec (a_nsec st + 1) st)).
    change (CH (ch :: pc) pb (set_nres (0 + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))) with (CH (ch :: pc) pb (set_nsec (a_nsec st + 1) st)).
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_nsec set_nres] in *. exact X. }
    repeat (split; [assumption|]). split; [right; lia|]. split; [exact H8|]. unfold live_budget, live_chunks in *. cbn [a_live set_nsec set_nres] in *. exact H9.
  - change (CH (ch :: pc) pb (set_nres (0 + K_CHUNKS_BLOCK) st1)) with (CH (ch :: pc) pb st1).
    apply (AMI_commit _ st1 _ _ (went (a_ptr_array st, PTR_SZ))); auto; try lia.
    + rewrite HB1, HS1. unfold K_PTRARR_COMMIT, PTR_SZ. lia.
    + unfold K_PTRARR_COMMIT. lia.
    + unfold st1, commit_bytes, csum, get_cls. cbn. unfold K_CHUNKS_BLOCK, K_PTRARR_COMMIT. lia.
Qed.

Definition mkch (n mb ms : Z) : achunk := if is_primary n then CPrim (class_id (needed_size n)) n else CSec mb ms n.

Definition csig (ch : achunk) : Z + Z := match ch with CPrim c _ => inl c | CSec _ _ n => inr n end.
Lemma live_budget_list_sig : forall ch ch' L, csig ch = csig ch' -> live_budget_list (ch :: L) -> live_budget_list (ch' :: L).
Proof.
  intros ch ch' L Hs (B1 & B2 & B3). unfold live_budget_list.
  destruct ch as [c n|mb ms n], ch' as [c' n'|mb' ms' n']; cbn in Hs; try discriminate; injection Hs as E; subst.
  - split; [|split; assumption]. intros c Hc. specialize (B1 c Hc). rewrite cntP_cons in *. cbn [is_prim_of] in *. exact B1.
  - split; [|split]. { intros c Hc. specialize (B1 c Hc). rewrite cntP_cons in *. cbn [is_prim_of] in *. exact B1. }
    { rewrite secs_cons, zlen_app in *. cbn [sec_of] in *. unfold zlen in *. cbn [length] in *. lia. }
    { cbn [secbytes] in *. lia. }
Qed.

Lemma sec_map_size_ge : forall n, 64512 < n -> n + 8192 <= sec_map_size n.
Proof.
  intros n Hn. unfold sec_map_size, needed_size. rewrite large_not_primary by lia. unfold needed0, rounded_size.
  assert (Hr : rz_size n = 2048) by (unfold rz_size, rz_log; repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia); reflexivity). rewrite Hr.
  pose proof (rup_ge (Z.max n 8) 8 ltac:(lia)). pose proof (rup_ge (rup (Z.max n 8) 8 + 2048 + 2048) PG ltac:(unfold PG; lia)). unfold PG in *. lia.
Qed.

Lemma not_primary_large : forall n, 0 <= n -> is_primary n = false -> 64512 < n.
Proof.
  intros n Hn Hp. destruct (Z_lt_dec 64512 n); [lia|]. rewrite is_primary_iff in Hp by lia. apply Z.leb_gt in Hp. lia.
Qed.

Definition malloc_post (st : astate) (n : Z) (r : astate * option AsanCtrl.aptr) (mo' : Model) : Prop :=
  exists ch, snd r = Some (a_next st) /\ INV [] [] (fst r) mo' /\ a_live (fst r) = <[a_next st := ch]> (a_live st)
  /\ (a_live st) !! (a_next st) = None /\ chunk_size ch = n
  /\ a_qloc_bytes (fst r) = a_qloc_bytes st /\ a_qglob_bytes (fst r) = a_qglob_bytes st /\ a_qloc (fst r) = a_qloc st /\ a_qglob (fst r) = a_qglob st.

Theorem amalloc_core : forall st mo n,
  INV [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> 0 <= n <= 2^29 ->
  (forall mb ms, live_budget_list (mkch n mb ms :: live_chunks st)) ->
  W [] [] st + 2 * n + 128 <= WCAP ->
  vroom [] [] st ->
  atot (amalloc ATOP RESV st n) mo (malloc_post st n).
Proof.
  intros st mo n HI Hql Hqg Hn HLB HWR HVR.
  pose proof HI as [HA HM].
  assert (Hnone : (a_live st) !! (a_next st) = None).
  { destruct ((a_live st) !! (a_next st)) as [ch0|] eqn:E; [|reflexivity]. exfalso.
    destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). specialize (Hid _ _ E). lia. }
  assert (HQB : bsum (qbatches [] st) <= 2^28 + 2^22).
  { unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA as (_ & _ & _ & Hq1 & Hq2 & _). unfold Q_CACHE, Q_MAX in *. lia. }
  destruct (CH_bounds [] [] st HA ltac:(lia) ltac:(unfold zlen; cbn; lia) ltac:(cbn; lia)) as [HCL HCS].
  assert (HCL2 : zlen (CH [] [] st) <= 5330).
  { destruct (CH_bounds_gen [] [] st (2^28 + 2^22) HA HQB ltac:(lia) ltac:(unfold zlen; cbn; lia) ltac:(cbn; lia)) as [X _]. lia. }
  assert (Hns : needed_size n <= 2^40).
  { unfold needed_size, needed0, rounded_size. pose proof (rup_le (Z.max n 8) 8 ltac:(lia)).
    pose proof (rz_log_range n) as Hrl.
    assert (0 <= rz_size n <= 2048).
    { unfold rz_size. rewrite Z.shiftl_mul_pow2 by lia. change 2048 with (16 * 2^7).
      split. apply Z.mul_nonneg_nonneg; [lia|apply Z.pow_nonneg; lia]. apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]. }
    destruct (is_primary n); lia. }
  unfold amalloc. destruct (Z.ltb_spec (2^40) n); [lia|]. destruct (Z.ltb_spec (2^40) (needed_size n)); [lia|]. cbn [orb].
  destruct (is_primary n) eqn:Hp.
  -
    pose proof (primary_class_facts n ltac:(lia) Hp) as F. cbv zeta in F. destruct F as (F1 & F2 & F3 & F4 & F5 & F6).
    set (c := class_id (needed_size n)) in *.
    apply (cache_alloc_ok _ _ [] [] st c n _ mo HI ltac:(lia) Hp eq_refl).
    + eapply room_of_AINV; eauto; try lia. unfold cntP, zlen. cbn. lia.
    + exact HVR.
    + intros st' mo' HI' HSB'.
      assert (HF : a_live st' = a_live st /\ a_next st' = a_next st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob_bytes st' = a_qglob_bytes st /\ a_qloc st' = a_qloc st /\ a_qglob st' = a_qglob st).
      { destruct HSB' as [X|X]; destruct X as (_&_&_&_&_&Hl&Hnx&Hq1&Hqb1&Hq2&Hqb2&_); [repeat split; assumption|].
        unfold init_cache in *; destruct (a_cinit st); cbn in *; repeat split; assumption. }
      destruct HF as (E1 & E2 & E3 & E4 & E5 & E6).
      cbv beta iota. apply atotal_ret. exists (CPrim c n). cbn [fst snd]. rewrite E2, E1.
      split; [reflexivity|]. split.
      { rewrite <- E1, <- E2. apply INV_hand_to_live; [exact HI'|]. unfold live_chunks. rewrite E1. specialize (HLB 0 0). unfold mkch in HLB. rewrite Hp in HLB. exact HLB. }
      repeat split; auto.
  -
    pose proof (not_primary_large n ltac:(lia) Hp) as Hbig. pose proof (sec_map_size_bounds n ltac:(lia)) as SB. pose proof (sec_map_size_ge n Hbig) as SG.
    apply (large_alloc_ok _ _ [] [] st n _ mo HI ltac:(lia) ltac:(lia) HCL2).
    intros st' mo' mb HI' Hst'.
    assert (HF : a_live st' = a_live st /\ a_next st' = a_next st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob_bytes st' = a_qglob_bytes st /\ a_qloc st' = a_qloc st /\ a_qglob st' = a_qglob st).
    { destruct Hst' as [-> | ->]; repeat split; reflexivity. }
    destruct HF as (E1 & E2 & E3 & E4 & E5 & E6).
    cbv beta iota. cbn [chunk_user_beg].
    pose proof HI' as [HA' HM']. pose proof HA' as (_ & HW' & _). rewrite all_chunks_cons in HW'. apply Forall_cons_iff in HW' as [Hwf _].
    cbn in Hwf. destruct Hwf as (_ & _ & Hal & Hmb & Hrange).
    assert (Hland : 0 <= Z.land n (Z.lnot 7) <= n).
    { rewrite <- Z.ldiff_land. change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
      rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. pose proof (Z.div_mod n (2^3) ltac:(lia)). pose proof (Z.mod_pos_bound n (2^3) ltac:(lia)). lia. }
    assert (Hrz : rz_size n = 2048) by (unfold rz_size, rz_log; repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia); reflexivity).
    rewrite Hrz. unfold PG.
    apply (poison0_ok _ _ [CSec mb (sec_map_size n) n] [] st' _ mo'); auto; try lia.
    + rewrite CH_cons. cbn [sec_of app zsum2 snd].
      replace (CH [] [] st') with (CH [] [] st) by (unfold CH, all_chunks, live_chunks, qbatches; rewrite E1, E5, E6; reflexivity). lia.
    + intros mo'' HI''. apply atotal_ret. exists (CSec mb (sec_map_size n) n). cbn [fst snd]. rewrite E2, E1.
      split; [reflexivity|]. split.
      { rewrite <- E1, <- E2. apply INV_hand_to_live; [exact HI''|]. unfold live_chunks. rewrite E1. specialize (HLB mb (sec_map_size n)). unfold mkch in HLB. rewrite Hp in HLB. exact HLB. }
      repeat split; auto.
Qed.

End WithResv.
