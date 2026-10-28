(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ARep ARepFrame ALayout AHeapP ASecFacts ASec ARepExt.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma su_disjoint : forall L W A k,
  sec_untouched L W -> Forall (fun iv => fst iv < snd iv) W -> 0 < k ->
  (forall a, A <= a < A + k -> aknown L a -> False) ->
  disjoint_from W A k.
Proof.
  intros L W A k SU NE Hk CL. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  inversion SU as [|x l Hx Hl]; subst. inversion NE as [|x' l' Hn Hnl]; subst. split; [| apply IH; [exact Hl| exact Hnl]].
  cbn [fst snd] in Hx, Hn.
  destruct (Z_lt_le_dec lo (A + k)) as [L1|L1]; [| left; lia].
  destruct (Z_lt_le_dec A hi) as [L2|L2]; [| right; lia].
  exfalso. apply (CL (Z.max A lo)); [lia|]. apply Hx. lia.
Qed.

Lemma sec_untouched_filter : forall L W, sec_untouched L W -> sec_untouched L (List.filter nonempty W).
Proof. intros L W SU. unfold sec_untouched in *. rewrite Forall_forall in SU |- *. intros iv Hin. apply SU. apply List.filter_In in Hin. tauto. Qed.
Lemma nonempty_filter : forall W, Forall (fun iv : Z * Z => fst iv < snd iv) (List.filter nonempty W).
Proof. intros W. rewrite Forall_forall. intros [lo hi] Hin. apply List.filter_In in Hin. destruct Hin as [_ NE]. unfold nonempty in NE. cbn [fst snd] in *. apply Z.ltb_lt. exact NE. Qed.

Section Geo.
Variable L : alayout.
Hypothesis ALO : alayout_ok L.

(* [comment removed for export] *)
Local Ltac layout :=
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & _); pose proof (ao_space L ALO) as RSP; pose proof (ao_res_hi L ALO) as ORH;
  pose proof (ao_t L ALO) as (_ & OT1 & OT2 & OTs & OTi);
  let OC := fresh in pose proof (ao_ctx L ALO) as OC; pose proof (aobj_img _ _ OC ltac:(lia)) as OCI; destruct OC as (_ & OC1 & OC2 & OCs & _);
  pose proof (ao_res L ALO) as (_ & OR1 & OR2 & _ & _);
  let ON := fresh in pose proof (ao_nodes L ALO) as ON; pose proof (aobj_img _ _ ON ltac:(lia)) as ONI; destruct ON as (_ & ON1 & ON2 & ONs & _);
  let OS := fresh in pose proof (ao_store L ALO) as OS; pose proof (aobj_img _ _ OS ltac:(lia)) as OSI; destruct OS as (_ & OS1 & OS2 & OSs & _);
  let OFK := fresh in pose proof (ao_fake L ALO) as OFK; pose proof (aobj_img _ _ OFK ltac:(lia)) as OFI; destruct OFK as (OF0 & OF1 & OF2 & OFs & _);
  pose proof (ao_dtls L ALO) as (_ & OD1 & OD2 & ODs & ODi);
  let OP := fresh in pose proof (ao_ptr L ALO) as OP; pose proof (aobj_img _ _ OP ltac:(lia)) as OPI; destruct OP as (_ & OP1 & OP2 & OPs & _);
  pose proof atop_range as ATR; pose proof ATOP_al16 as ATA;
  unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in SP2, SP3; change (2^37) with 137438953472 in SP2;
  unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in *.

(* [comment removed for export] *)
Lemma clear_inst : forall a, AINSTANCE + 72 <= a < AINSTANCE + 728 -> aknown L a -> False.
Proof.
  intros a Ha K. layout.
  unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE in *. rewrite !shad_div in K. unfold ASHOFF in K.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha OF1 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha OTi OCI OR1 ORH ONI OSI OFI ODi ATR ATA SP1 SP2. lia.
Qed.

(* [comment removed for export] *)
Lemma clear_ptr : forall a, al_ptr_array L <= a < al_ptr_array L + 8388608 -> aknown L a -> False.
Proof.
  intros a Ha K. layout.
  pose proof (ad_t_ptr L ALO) as X1. pose proof (ad_ctx_ptr L ALO) as X2. pose proof (ad_ptr_res L ALO) as X3. pose proof (ad_nodes_ptr L ALO) as X4.
  pose proof (ad_store_ptr L ALO) as X5. pose proof (ad_fake_ptr L ALO) as X6. pose proof (ad_dtls_ptr L ALO) as X7.
  unfold adisj, aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. rewrite !shad_div in K. unfold ASHOFF in K.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Ha OPI OPs SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 OPs OP2 ATR SP2. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    clear -K Ha OF1 OF2 OPs ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha OPs OP2 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha OP2 X1 X2 X3 X4 X5 X6 X7 RSP SP1 SP2 ATR ATA. lia.
Qed.

(* [comment removed for export] *)
Lemma clear_chunk : forall mb ms n a, sec_wf1 L (CSec mb ms n) -> mb <= a < mb + ms -> aknown L a -> False.
Proof.
  intros mb ms n a WF1 Ha K. cbn [sec_wf1] in WF1. destruct WF1 as (G1 & G2 & G3 & G4 & G5 & G6 & (Qt & Qc & Qr & Qp & Qn & Qs & Qf & Qd)).
  layout. unfold ablk in G2.
  unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. rewrite !shad_div in K. unfold ASHOFF in K.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Ha G2 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 G2 G3 ATR SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha OF1 OF2 G2 G3 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha G2 G3 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha G3 Qt Qc Qr Qn Qs Qf Qd RSP SP1 SP2 ATR ATA. lia.
Qed.

(* [comment removed for export] *)
Lemma clear_chunk_shadow : forall mb ms n a, sec_wf1 L (CSec mb ms n) -> shad mb <= a < shad mb + ms / 8 -> aknown L a -> False.
Proof.
  intros mb ms n a WF1 Ha K. cbn [sec_wf1] in WF1. destruct WF1 as (G1 & G2 & G3 & G4 & G5 & G6 & (Qt & Qc & Qr & Qp & Qn & Qs & Qf & Qd)).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & _ & _ & _ & _ & _ & _ & MSM & MSB). rewrite <- G4 in MSM, MSB.
  layout. unfold ablk in G2.
  assert (MB8 : mb mod 8 = 0) by (clear -G1; Z.div_mod_to_equations; lia).
  assert (MS8 : ms mod 8 = 0) by (clear -MSM; Z.div_mod_to_equations; lia).
  unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. rewrite !shad_div in K. rewrite !shad_div in Ha. unfold ASHOFF in K, Ha.
  destruct K as [K|[K|[K|[K|K]]]].
  - (* [comment removed for export] *)
    clear -K Ha G2 G3 MSB ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    clear -K Ha MB8 MS8 MSB Qr RSP SP3 OR1 ORH G2 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha MB8 MS8 MSB Qf OF0 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha MB8 MS8 MSB G3 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    clear -K Ha G2 G3 MSB MB8 MS8 ATR OTs OT2 OCs OC2 OR1 ORH ONs ON2 OSs OS2 OFs OF2 ODs OD2 SP1 SP2. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma clear_prim0 : forall a, shad (al_space_beg L) <= a < shad (al_space_beg L) + shlen K_REGION -> aknown L a -> False.
Proof.
  intros a Ha K. layout. pose proof (ad_fake_res L ALO) as DFR.
  unfold adisj, aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, K_REGION in *. change (2^32) with 4294967296 in Ha.
  rewrite !shad_div, shlen_div in Ha. rewrite !shad_div in K. unfold ASHOFF in K, Ha.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha DFR RSP OF0 SP3 OR1 ORH SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP2 SP1 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 SP2 OTs OT2 OCs OC2 OR1 ORH ONs ON2 OSs OS2 OFs OF2 ODs OD2 ATR ATA. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma clear_free_shadow : forall x,
  (AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) ->
  Forall (fun iv => ~ (fst iv <= x < snd iv)) (astartup_hulls L) ->
  aknown L (shad x) -> False.
Proof.
  intros x Hx HF K. unfold astartup_hulls in HF.
  repeat (apply Forall_cons_iff in HF; destruct HF as [?H HF]). cbn [fst snd] in *.
  layout. unfold K_HIGH_MEM in Hx.
  unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. rewrite !shad_div in K. unfold ASHOFF in K.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Hx ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Hx H8 RSP SP3 OR1 ORH ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Hx H3 OF0 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Hx ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Hx OTs OT2 OCs OC2 OR1 ORH ONs ON2 OSs OS2 OFs OF2 ODs OD2 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
Qed.
End Geo.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frame.
Variables (L : alayout) (W0 : list (Z * Z)) (m m' : amem).
Hypothesis MU0 : munch W0 m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis SU0 : sec_untouched L W0.
Let W := List.filter nonempty W0.
Let MU : munch W m m' := munch_filter_nonempty W0 m m' MU0.
Let SU : sec_untouched L W := sec_untouched_filter L W0 SU0.
Let NE : Forall (fun iv => fst iv < snd iv) W := nonempty_filter W0.

Section WithLayout.
Hypothesis ALO : alayout_ok L.
Lemma D_inst : forall A k, AINSTANCE + 72 <= A -> A + k <= AINSTANCE + 728 -> 0 < k -> disjoint_from W A k.
Proof. intros A k H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. apply (clear_inst L ALO). lia. Qed.
Lemma D_ptr : forall A k, al_ptr_array L <= A -> A + k <= al_ptr_array L + 8388608 -> 0 < k -> disjoint_from W A k.
Proof. intros A k H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. apply (clear_ptr L ALO). lia. Qed.
Lemma D_chunk : forall mb ms n A k, sec_wf1 L (CSec mb ms n) -> mb <= A -> A + k <= mb + ms -> 0 < k -> disjoint_from W A k.
Proof. intros mb ms n A k WF1 H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. apply (clear_chunk L ALO mb ms n); [exact WF1| lia]. Qed.
Lemma D_shadow : forall mb ms n A k, sec_wf1 L (CSec mb ms n) -> shad mb <= A -> A + k <= shad mb + ms / 8 -> 0 < k -> disjoint_from W A k.
Proof. intros mb ms n A k WF1 H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. apply (clear_chunk_shadow L ALO mb ms n); [exact WF1| lia]. Qed.

(* [comment removed for export] *)
Lemma asec_chunk_frame : forall mb ms n idx lv,
  sec_wf1 L (CSec mb ms n) -> asec_chunk m (CSec mb ms n) idx lv -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros mb ms n idx lv WF1 CH. pose proof WF1 as WF0. cbn [sec_wf1] in WF0. destruct WF0 as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & _). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  destruct GR as (GR1 & GR2 & GR3).
  cbn [asec_chunk] in CH |- *. destruct CH as (H1 & H2 & H3 & H4 & (b1 & ctx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in *.
  split; [eapply cells_frame; [exact H1| exact MU| exact WM| cbn; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H2| exact MU| exact WM| intros _; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frame; [exact H3| exact MU| exact WM| cbn; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H4| exact MU| exact WM| intros _; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frame; [exact H5| exact MU| exact WM| cbn; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frame; [exact H6| exact MU| exact WM| intros _; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; eapply D_shadow; [exact WF1| | |]; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frame; [exact S2| exact MU| exact WM| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; eapply D_shadow; [exact WF1| | |]; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2; eapply D_shadow; [exact WF1| | |]; clear -GR3 GR1 POS; lia].
Qed.
End WithLayout.

Theorem asec_frame : forall st st' X X',
  ASEC_of L st X m -> sec_same st st' -> ASEC_of L st' X' m'.
Proof.
  intros st st' X X' (WFS & ARR & INST & PZ & SHZ) (EN & ER & EP & EL & PERM).
  unfold ASEC_of, ASECc.
  pose proof WFS as (ALO & WP & WR & WL & WB & WF1 & WD).
  assert (ALLSEC : forall ch, In ch (sec_chunks_of st) -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n)).
  { intros ch Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1. destruct ch as [c n|mb ms n]; [destruct W1|].
    exists mb, ms, n. split; [reflexivity| exact W1]. }
  split; [| split; [| split; [| split]]].
  - (* [comment removed for export] *)
    unfold asec_wf. rewrite EP, ER, EN. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|]. split; [| split; [exact WB| split]].
    + rewrite (Permutation_length PERM). exact WL.
    + rewrite Forall_forall in WF1 |- *. intros ch Hin. apply WF1. eapply Permutation_in; [exact PERM| exact Hin].
    + eapply sec_disjoint_perm; [apply Permutation_sym; exact PERM| exact WD].
  - (* [comment removed for export] *)
    destruct ARR as (order & PO & U64 & JK & PER). exists order.
    assert (LEN : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
    split; [eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PERM]|].
    split; [| split].
    + destruct order as [|o0 order'].
      * destruct U64 as [[B0 [B1 _]] [V0 [V1 _]]]. split; [split; [exact B0| split; [exact B1| cbn; intros; lia]] | split; [exact V0| split; [exact V1| cbn; intros; lia]]].
      * eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. apply (D_ptr ALO); cbn [length] in LEN |- *; clear -LEN WB WR; lia.
    + rewrite EN, ER. eapply junk_frame; [exact JK| exact MU| exact WM|]. intros POS. apply (D_ptr ALO); clear -POS WB WR; lia.
    + intros i ch Hi. destruct (PER i ch Hi) as (lv & LV & CH).
      assert (Hin : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
      destruct (ALLSEC ch Hin) as (mb & ms & n & -> & W1).
      exists lv. split; [| eapply asec_chunk_frame; [exact ALO| exact W1| exact CH]].
      rewrite LV. unfold sec_live. split; intros [p Hp]; exists p; [apply (proj2 (EL p mb ms n)); exact Hp| apply (proj1 (EL p mb ms n)); exact Hp].
  - (* [comment removed for export] *)
    destruct INST as (I1 & [srt I2] & I3 & I4 & I5 & I6). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    split; [exists srt; eapply cells_frame; [exact I2| exact MU| exact WM| cbn; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    split; [eapply junk_frame; [exact I3| exact MU| exact WM| intros _; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    split; [eapply junk_frame; [exact I4| exact MU| exact WM| intros _; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    split; [eapply cells_frame; [exact I5| exact MU| exact WM| cbn; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    eapply junk_frame; [exact I6| exact MU| exact WM| intros _; apply (D_inst ALO); unfold AINSTANCE; lia].
  - (* [comment removed for export] *)
    unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM|]. intros POS.
    apply (su_disjoint L); [exact SU| exact NE| exact POS|]. intros a Ha. apply (clear_prim0 L ALO). exact Ha.
  - (* [comment removed for export] *)
    intros x Hx HF HC.
    assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM, AIMG_HI, KLS in *; pose proof atop_range as ATR; clear -Hx ATR; Z.div_mod_to_equations; lia).
    assert (HC0 : Forall (fun ch => ~ (sec_mb ch <= x < sec_mb ch + sec_ms ch)) (sec_chunks_of st)).
    { rewrite Forall_forall in HC |- *. intros ch Hin. apply HC. eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]. }
    rewrite <- (SHZ x Hx HF HC0). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia].
    apply (su_disjoint L); [exact SU| exact NE| clear; lia|]. intros a Ha K. apply (clear_free_shadow L ALO x Hx HF). replace (shad x) with a by (clear -Ha; lia). exact K.
Qed.
End Frame.

(* [comment removed for export] *)
Theorem asec_hs_frame : forall L st st' X X' m m' W,
  ASEC_of L st X m -> munch W m m' -> wmono bsegs m m' -> sec_untouched L W -> sec_same st st' -> ASEC_of L st' X' m'.
Proof. intros L st st' X X' m m' W HS MU WM SU SS. eapply (asec_frame L W m m' MU WM SU); [exact HS| exact SS]. Qed.
End CANSEC1.
