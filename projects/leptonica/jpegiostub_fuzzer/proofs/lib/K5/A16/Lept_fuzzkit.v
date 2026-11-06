(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import Tac Mem Frame Cells Step RzCPS.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface D_kit Lept_kit D_iface D_defs Lept_iface.
Import ListNotations.
Open Scope Z_scope.

Section FKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma live_apart : forall Σ m p n q k, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> In (q, k) (rt_live RT Σ) -> p <> q ->
  p + n <= q \/ q + k <= p.
Proof using AF.
  intros Σ m p n q k HA H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
  apply (af_live_disj RT AF Σ m p n q k l1 l2 HA E). rewrite E in H2. apply in_app_or in H2. apply in_or_app.
  destruct H2 as [X|[X|X]]; [left; exact X| injection X as X1 X2; congruence | right; exact X].
Qed.

(* [comment removed for export] *)
Definition pixv_spec (v : pixv) (w : Z) : pixv :=
  mkPixv (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) (p_xres v) (p_yres v) (p_inf v) w (p_cmap v) (p_data v).

(* [comment removed for export] *)
Lemma pix_obj_spec : forall Σ (m m' : mem) pix v cv w W,
  ART RT Σ m -> pix_obj (rt_live RT Σ) m pix v cv -> munch W m m' ->
  (forall q k a, In (q, k) (rt_live RT Σ) -> q <> pix -> q <= a < q + k -> outside W a) ->
  rw_cells asegs m' pix (pix_cells (pixv_spec v w)) ->
  pix_obj (rt_live RT Σ) m' pix (pixv_spec v w) cv.
Proof using AF.
  intros Σ m m' pix v cv w W HA (PXC & PCH & HOK & PDATA & PCMAP) MU OUT PXC'.
  split; [exact PXC'|]. split; [exact PCH|]. split; [exact HOK|]. split; [exact PDATA|].
  cbn [pixv_spec p_cmap p_data]. destruct PCMAP as [Z0|(((pad & CMC) & CCH & ACH & COK & CNE) & N1 & N2 & N3 & N4)]; [left; exact Z0| right].
  split; [| exact (conj N1 (conj N2 (conj N3 N4)))]. split; [| exact (conj CCH (conj ACH (conj COK CNE)))].
  exists pad. apply (rw_cells_agree_nw asegs m m' _ _ CMC). intros a Ha. apply MU.
  destruct CCH as (CIN & _). cbn [cells_size cmap_cells csize Nat.add] in Ha. apply (OUT (p_cmap v) 24 _ CIN N1). lia.
Qed.

(* [comment removed for export] *)
Lemma live_outside_walk : forall Σ (m : mem) pix fr usp slo q n a,
  ART RT Σ m -> In (pix, 64) (rt_live RT Σ) -> In (fr, 0%nat) (rt_frames RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= slo ->
  In (q, n) (rt_live RT Σ) -> q <> pix -> q <= a < q + n ->
  outside [(slo, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (pix, pix + 64)] a.
Proof using AF.
  intros Σ m pix fr usp slo q n a HA PIN FIN SLO QIN NE Ha.
  pose proof (af_live_range RT AF Σ m q n HA QIN) as (_ & R1 & _).
  pose proof (live_apart Σ m q n pix 64 HA QIN PIN NE) as R2.
  pose proof (af_frames_range RT AF Σ m fr 0%nat HA FIN) as (_ & _ & _ & FLV). specialize (FLV q n QIN).
  pose proof (af_fshadow_apart RT AF Σ m fr 0%nat HA FIN) as (SA1 & _). specialize (SA1 q n QIN).
  change (fs_size 0) with 64 in *. unfold shad, SHB in SA1.
  cbn [outside]. repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].
Qed.

(* [comment removed for export] *)
Lemma inner_chunk_apart : forall Σ' (m : mem) p n live0 frs usp a,
  ART RT Σ' m -> In (p, n) (rt_live RT Σ') ->
  (forall e, In e live0 -> In e (rt_live RT Σ') /\ fst e <> p) -> (forall e, In e frs -> In e (rt_frames RT Σ')) ->
  rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ' m p n live0 frs usp a HA INL SUBL SUBF SPL Ha.
  pose proof (af_live_range RT AF Σ' m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp). destruct (SUBL _ Hin) as [Hin' NE]. cbn [fst] in NE.
    pose proof (live_apart Σ' m p n p' n' HA INL Hin' ltac:(congruence)) as D. lia.
  - destruct H as (f & k & Hin & Hf). apply SUBF in Hin.
    pose proof (af_frames_range RT AF Σ' m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf). apply SUBF in Hin.
    pose proof (af_fshadow_apart RT AF Σ' m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.
End FKit.

Lemma live_remove_in : forall (l : list (Z * Z)) p e, In e (live_remove p l) -> In e l /\ fst e <> p.
Proof.
  intros l p e He. split; [exact (live_remove_sub l p e He)|]. unfold live_remove in He. apply stdpp.base.list_elem_of_In in He.
  apply stdpp.list_basics.list.list_elem_of_filter in He. destruct He as [Hb _].
  destruct (fst e =? p) eqn:E; [cbn in Hb; contradiction| apply Z.eqb_neq in E; exact E].
Qed.
Lemma rm_opt_sub : forall p (l : list (Z * Z)) e, In e (rm_opt p l) -> In e l.
Proof. intros p l e He. unfold rm_opt in He. destruct (p =? 0); [exact He| exact (live_remove_sub l p e He)]. Qed.
Lemma live_destroy_in : forall pix v cv (l : list (Z * Z)) e, In e (live_destroy pix v cv l) -> In e l /\ fst e <> pix.
Proof.
  intros pix v cv l e He. unfold live_destroy in He. apply live_remove_in in He as [He NE]. split; [| exact NE].
  apply rm_opt_sub in He. apply rm_opt_sub in He. apply rm_opt_sub in He. exact He.
Qed.

(* [comment removed for export] *)
Definition pixv_data (v : pixv) (w : Z) : pixv :=
  mkPixv (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) (p_xres v) (p_yres v) (p_inf v) (p_spec v) (p_cmap v) w.

Section FKit22.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma pix_obj_data0 : forall Σ (m m' : mem) pix v cv W,
  ART RT Σ m -> pix_obj (rt_live RT Σ) m pix v cv -> munch W m m' ->
  (forall q k a, In (q, k) (rt_live RT Σ) -> q <> pix -> q <= a < q + k -> outside W a) ->
  rw_cells asegs m' pix (pix_cells (pixv_data v 0)) ->
  pix_obj (rt_live RT Σ) m' pix (pixv_data v 0) cv.
Proof using AF.
  intros Σ m m' pix v cv W HA (PXC & PCH & HOK & PDATA & PCMAP) MU OUT PXC'.
  split; [exact PXC'|]. split; [exact PCH|]. split; [exact HOK|]. split; [left; reflexivity|].
  cbn [pixv_data p_cmap p_data]. destruct PCMAP as [Z0|(((pad & CMC) & CCH & ACH & COK & CNE) & N1 & N2 & N3 & N4)]; [left; exact Z0| right].
  assert (CM' : cmap_obj (rt_live RT Σ) m' (p_cmap v) cv).
  { split; [| exact (conj CCH (conj ACH (conj COK CNE)))].
    exists pad. apply (rw_cells_agree_nw asegs m m' _ _ CMC). intros a Ha. apply MU.
    destruct CCH as (CIN & _). cbn [cells_size cmap_cells csize Nat.add] in Ha. apply (OUT (p_cmap v) 24 _ CIN N1). lia. }
  split; [exact CM'|]. split; [exact N1|]. split; [exact N2|].
  destruct CCH as (_ & C0 & _). destruct ACH as (_ & A0 & _). split; lia.
Qed.

(* [comment removed for export] *)
Lemma pix_obj_free : forall (live : list (Z * Z)) frs sp (m m' : mem) pix v cv d,
  pix_obj live m pix v cv -> p_data v = 0 -> d <> pix -> (p_cmap v = 0 \/ (d <> p_cmap v /\ d <> c_arr cv)) ->
  rt_pres (live_remove d live) frs sp m m' ->
  pix_obj (live_remove d live) m' pix v cv.
Proof.
  intros live frs sp m m' pix v cv d (PXC & (PIN & PR) & HOK & PDATA & PCMAP) DZ NP NC PRES.
  assert (KEEP : forall q k, In (q, k) live -> q <> d -> forall cs, Z.of_nat (cells_size cs) <= k -> rw_cells asegs m q cs -> rw_cells asegs m' q cs).
  { intros q k Hin NE cs Hsz H. apply (rw_cells_agree_nw asegs m m' _ _ H). intros a Ha. apply PRES.
    right. right. left. exists q, k. split; [apply live_remove_keep; [exact Hin| cbn [fst]; exact NE]| lia]. }
  split; [apply (KEEP pix 64 PIN ltac:(congruence)); [cbn; lia| exact PXC]|].
  split; [split; [apply live_remove_keep; [exact PIN| cbn [fst]; congruence]| exact PR]|].
  split; [exact HOK|]. split; [left; exact DZ|].
  destruct PCMAP as [Z0|(((pad & CMC) & (CIN & CR) & (AIN & AR) & COK & CNE) & N1 & N2 & N3 & N4)]; [left; exact Z0| right].
  destruct NC as [NC|[NC1 NC2]]; [congruence|].
  split; [| exact (conj N1 (conj N2 (conj N3 N4)))].
  split; [exists pad; apply (KEEP (p_cmap v) 24 CIN ltac:(congruence)); [cbn; lia| exact CMC]|].
  split; [split; [apply live_remove_keep; [exact CIN| cbn [fst]; congruence]| exact CR]|].
  split; [split; [apply live_remove_keep; [exact AIN| cbn [fst]; congruence]| exact AR]|].
  exact (conj COK CNE).
Qed.
End FKit22.

(* [comment removed for export] *)
Lemma live_destroy_data0 : forall pix v cv (l : list (Z * Z)), p_data v <> 0 ->
  live_destroy pix (pixv_data v 0) cv (live_remove (p_data v) l) = live_destroy pix v cv l.
Proof.
  intros pix v cv l H. unfold live_destroy, rm_opt. cbn [pixv_data p_cmap p_data].
  replace (p_data v =? 0) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity.
Qed.
Lemma live_remove_length : forall p (l : list (Z * Z)), (length (live_remove p l) <= length l)%nat.
Proof. intros p l. unfold live_remove. apply stdpp.list_basics.list.length_filter. Qed.
