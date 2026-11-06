(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape HeapIface HeapIfaceA L5Defs L5Core L5LazyA
  PmHeapIfaceA DecIface DecIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutCertA CutHeapA CutL5A CutBridgeA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FLA.
Section S.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.

Lemma rng : forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V -> CHA.rng_facts L ar LB FF.
Proof. intros LB FF LK cr A M V HH. exact (CHA.rng_of_wf L ar _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)). Qed.

Lemma stk_vis : forall LB FF LK cr A M model a, ri_inv HI LB FF LK cr A M (vml_of model) -> ahl_ceil ar <= a < 2 ^ 47 -> ahid A model (Z_to_bv 64 a) = false.
Proof.
  intros LB FF LK cr A M model a HH Ha. pose proof (rng _ _ _ _ _ _ _ HH) as RFx. destruct (CHA.rf_ceil L ar _ _ RFx) as [CL _].
  apply (CHA.client_vis L ar C HI HIok LB FF LK cr A M model (ahl_ceil ar) 0 a HH); [lia | right; left; lia |].
  apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). unfold BIGSHADOW_HI. lia.
Qed.
Lemma stk_visr : forall LB FF LK cr A M model a n, ri_inv HI LB FF LK cr A M (vml_of model) -> ahl_ceil ar <= a -> a + n <= 2 ^ 47 -> CL5A.visr (ahid A model) a n.
Proof. intros LB FF LK cr A M model a n HH H1 H2 i Hi. apply (stk_vis _ _ _ _ _ _ _ _ HH). lia. Qed.

Lemma blk_facts : forall LB FF LK cr A M V b, ri_inv HI LB FF LK cr A M V -> In b LB ->
  4096 <= fst b /\ fst b + snd b <= ahl_ceil ar /\ (fst b + snd b <= hl_img_lo L \/ hl_img_hi L <= fst b) /\ (fst b + snd b <= BIGSHADOW_LO \/ BIGSHADOW_HI <= fst b) /\ 0 < snd b /\ fst b + snd b <= 2 ^ 47.
Proof.
  intros LB FF LK cr A M V b HH Hb. destruct (CHA.rf_blk L ar _ _ (rng _ _ _ _ _ _ _ HH) b Hb) as (B1 & B2 & B3 & B4 & B5 & (A1 & A2 & A3)). lia.
Qed.
Lemma blk_vis : forall LB FF LK cr A M model b a, ri_inv HI LB FF LK cr A M (vml_of model) -> In b LB -> fst b <= a < fst b + snd b -> ahid A model (Z_to_bv 64 a) = false.
Proof.
  intros LB FF LK cr A M model b a HH Hb Ha. pose proof (rng _ _ _ _ _ _ _ HH) as RFx. destruct (blk_facts _ _ _ _ _ _ _ b HH Hb) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (CHA.rf_ceil L ar _ _ RFx) as [CL _].
  apply (CHA.client_vis L ar C HI HIok LB FF LK cr A M model (ahl_ceil ar) 0 a HH); [unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia | left; exists b; split; [exact Hb | exact Ha] |].
  apply (CL5A.not_stk_shadow_app L ar LB FF a RFx). lia.
Qed.
Lemma txt_visr : forall LB FF LK cr A M model Q n, ri_inv HI LB FF LK cr A M (vml_of model) -> PDCA.textblk LB Q n -> CL5A.visr (ahid A model) Q n.
Proof. intros LB FF LK cr A M model Q n HH (b & Hb & H1 & H2) i Hi. apply (blk_vis _ _ _ _ _ _ _ b _ HH Hb). lia. Qed.

Lemma txt_kept : forall LB FF LK cr A M V Q n sp scr W a, ri_inv HI LB FF LK cr A M V -> PDCA.textblk LB Q n -> ahl_ceil ar <= sp - scr ->
  (forall w, In w W -> fst w + snd w <= Q \/ Q + n <= fst w) -> Q <= a < Q + n -> CHA.akept L ar LB FF sp scr W a.
Proof.
  intros LB FF LK cr A M V Q n sp scr W a HH (b & Hb & H1 & H2) Hsp HW Ha. destruct (blk_facts _ _ _ _ _ _ _ b HH Hb) as (B1 & B2 & B3 & B4 & B5 & B6).
  split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia|]. split; [left; exists b; split; [exact Hb | lia]|].
  intros w Hw. specialize (HW w Hw). unfold L5.in_rng. lia.
Qed.
Lemma txt_facts : forall LB FF LK cr A M V Q n, ri_inv HI LB FF LK cr A M V -> PDCA.textblk LB Q n ->
  4096 <= Q /\ Q + n <= ahl_ceil ar /\ (Q + n <= hl_img_lo L \/ hl_img_hi L <= Q) /\ (Q + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= Q) /\ Q + n <= 2 ^ 47.
Proof.
  intros LB FF LK cr A M V Q n HH (b & Hb & H1 & H2). destruct (blk_facts _ _ _ _ _ _ _ b HH Hb) as (B1 & B2 & B3 & B4 & B5 & B6). lia.
Qed.

Lemma txt_home_mono : forall LB FF sp Q n sp' Q' n', PDCA.txt_home ar LB FF sp Q n -> sp' <= sp -> Q <= Q' -> Q' + n' <= Q + n -> PDCA.txt_home ar LB FF sp' Q' n'.
Proof.
  intros LB FF sp Q n sp' Q' n' [(b & Hb & B1 & B2)|[Hf|[H1 H2]]] Hs HQ1 HQ2.
  - left. exists b. split; [exact Hb | lia].
  - right. left. exact (CL5A.ainfr_sub FF Q n Q' n' Hf HQ1 HQ2).
  - right. right. lia.
Qed.
Lemma txt_facts_h : forall LB FF LK cr A M V sp Q n, ri_inv HI LB FF LK cr A M V -> ahl_ceil ar <= sp -> PDCA.txt_home ar LB FF sp Q n -> 0 < n ->
  0 <= Q /\ Q + n <= 2 ^ 47 /\ (Q + n <= ahl_ceil ar \/ sp <= Q) /\ (Q + n <= hl_img_lo L \/ hl_img_hi L <= Q) /\ (Q + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= Q).
Proof.
  intros LB FF LK cr A M V sp Q n HH Hsp [Hb|Ho] Hn.
  - destruct (txt_facts _ _ _ _ _ _ _ Q n HH Hb) as (T1 & T2 & T3 & T4 & T5). lia.
  - pose proof (rng _ _ _ _ _ _ _ HH) as RFx. pose proof (CL5A.acobj_rng L ar LB FF sp Q n RFx Hsp Ho Hn) as (O1 & O2 & O3 & O4 & O5).
    split; [lia|]. split; [lia|]. split; [exact O5|]. split; [|exact O3].
    destruct Ho as [Hf|[H1 H2]]; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (CL5A.infr_rng L ar LB FF Q n RFx Hf Hn))))))) |].
    right. destruct (CHA.rf_ceil L ar _ _ RFx) as [CL _]. unfold BIGSHADOW_LO in LY_img. lia.
Qed.

Lemma txt_aclient_h : forall LB FF LK cr A M V sp scr Q n a, ri_inv HI LB FF LK cr A M V -> ahl_ceil ar <= sp -> PDCA.txt_home ar LB FF sp Q n -> Q <= a < Q + n ->
  aclient L ar LB FF sp scr a.
Proof.
  intros LB FF LK cr A M V sp scr Q n a HH Hsp [(b & Hb & B1 & B2)|[(f & Hf & F1 & F2)|[H1 H2]]] Ha.
  - left. exists b. split; [exact Hb | lia].
  - right. right. right. left. exists f. split; [exact Hf | lia].
  - right. left. pose proof (rng _ _ _ _ _ _ _ HH) as RFx. destruct (CHA.rf_sptop L ar _ _ RFx) as (SP1 & _). lia.
Qed.
Lemma txt_visr_h : forall LB FF LK cr A M model sp Q n, ri_inv HI LB FF LK cr A M (vml_of model) -> ahl_ceil ar <= sp -> PDCA.txt_home ar LB FF sp Q n ->
  CL5A.visr (ahid A model) Q n.
Proof.
  intros LB FF LK cr A M model sp Q n HH Hsp Hh i Hi. destruct (Z.le_gt_cases n 0) as [Hn|Hn]; [lia|].
  destruct (txt_facts_h LB FF LK cr A M (vml_of model) sp Q n HH Hsp Hh Hn) as (T1 & T2 & T3 & T4 & T5).
  pose proof (rng _ _ _ _ _ _ _ HH) as RFx.
  apply (CHA.client_vis L ar C HI HIok LB FF LK cr A M model sp 0 (Q + i) HH); [lia | exact (txt_aclient_h LB FF LK cr A M _ sp 0 Q n (Q + i) HH Hsp Hh ltac:(lia)) |].
  apply (CL5A.not_stk_shadow_app L ar LB FF (Q + i) RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
Qed.
Lemma txt_kept_h : forall LB FF LK cr A M V sp Q n scr W a, ri_inv HI LB FF LK cr A M V -> ahl_ceil ar <= sp - scr -> 0 <= scr -> PDCA.txt_home ar LB FF sp Q n ->
  (forall w, In w W -> fst w + snd w <= Q \/ Q + n <= fst w) -> Q <= a < Q + n -> CHA.akept L ar LB FF sp scr W a.
Proof.
  intros LB FF LK cr A M V sp Q n scr W a HH Hsp Hscr Hh HW Ha. destruct (Z.le_gt_cases n 0) as [Hn|Hn]; [lia|].
  destruct (txt_facts_h LB FF LK cr A M V sp Q n HH ltac:(lia) Hh Hn) as (T1 & T2 & T3 & T4 & T5).
  split; [lia|]. split; [exact (txt_aclient_h LB FF LK cr A M V sp scr Q n a HH ltac:(lia) Hh Ha)|].
  intros w Hw. specialize (HW w Hw). unfold L5.in_rng. lia.
Qed.

Lemma txt_lo_h : forall LB FF LK cr A M V sp Q n, ri_inv HI LB FF LK cr A M V -> ahl_ceil ar <= sp -> hl_img_lo L < FS_BYTES -> 4096 <= hl_img_hi L ->
  PDCA.txt_home ar LB FF sp Q n -> 0 < n -> 4096 <= Q.
Proof.
  intros LB FF LK cr A M V sp Q n HH Hsp HI1 HI2 [(b & Hb & B1 & B2)|[Hf|[H1 H2]]] Hn.
  - destruct (blk_facts _ _ _ _ _ _ _ b HH Hb) as (X1 & _). lia.
  - pose proof (rng _ _ _ _ _ _ _ HH) as RFx. destruct (CL5A.infr_rng L ar LB FF Q n RFx Hf Hn) as (F1 & _).
    destruct (CHA.rf_fs L ar _ _ RFx) as ((A0 & _ & _) & _ & A3). unfold FS_BYTES in *. lia.
  - pose proof (rng _ _ _ _ _ _ _ HH) as RFx. destruct (CHA.rf_ceil L ar _ _ RFx) as [CL _]. destruct (CHA.rf_sptop L ar _ _ RFx) as (SP1 & _). lia.
Qed.
End S.
End FLA.
