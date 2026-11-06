(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ARep ARepFrame ALayout AHeapP ASecFacts ASec ARepExt AMalloc_iface AFrameD ASecFrame. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ASF_kit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_kit.ASF_kit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AExh ARefillP_x.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.

Definition sprot (RESV : list (Z * Z)) (st : astate) (A k : Z) : Prop :=
     (exists lo hi, pcov RESV lo hi /\ lo <= A /\ A + k <= hi)
  \/ (exists iv, In iv (flat_map sec_iv (achunks st)) /\ fst iv <= A /\ A + k <= snd iv).

Lemma suD_disjoint : forall L RESV st W A k,
  sec_untouchedD L RESV st W -> Forall (fun iv => fst iv < snd iv) W -> 0 < k ->
  (forall a, A <= a < A + k -> aknown L a -> False) -> sprot RESV st A k ->
  disjoint_from W A k.
Proof.
  intros L RESV st W A k SU NE Hk CL PR. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  inversion SU as [|x l Hx Hl]; subst. inversion NE as [|x' l' Hn Hnl]; subst. split; [| apply IH; [exact Hl| exact Hnl]].
  cbn [fst snd] in Hx, Hn.
  destruct (Z_lt_le_dec lo (A + k)) as [L1|L1]; [| left; lia].
  destruct (Z_lt_le_dec A hi) as [L2|L2]; [| right; lia].
  exfalso. destruct Hx as [KN|[_ AV]].
  - apply (CL (Z.max A lo)); [lia|]. apply KN. lia.
  - unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV1 AV2].
    destruct PR as [(l0 & h0 & PC & P1 & P2)|(iv & Hiv & P1 & P2)].
    + pose proof (pcov_clear _ _ _ _ _ PC AV1 ltac:(lia) ltac:(lia)) as D. lia.
    + pose proof (proj1 (forallb_forall _ _) AV2 iv Hiv) as D. unfold iv_clear in D. apply orb_prop in D as [D|D]; apply Z.leb_le in D; lia.
Qed.

Lemma sec_untouchedD_filter : forall L RESV st W, sec_untouchedD L RESV st W -> sec_untouchedD L RESV st (List.filter nonempty W).
Proof. intros L RESV st W SU. unfold sec_untouchedD in *. rewrite Forall_forall in SU |- *. intros iv Hin. apply SU. apply List.filter_In in Hin. tauto. Qed.

Lemma sec_chunk_flat : forall st mb ms n, In (CSec mb ms n) (sec_chunks_of st) -> In (mb, mb + ms) (flat_map sec_iv (achunks st)).
Proof.
  intros st mb ms n H. unfold sec_chunks_of in H. apply List.filter_In in H. destruct H as [H _].
  apply in_flat_map. exists (CSec mb ms n). split; [exact H| left; reflexivity].
Qed.

Lemma chunk_shadow_band : forall L mb ms n, sec_wf1 L (CSec mb ms n) -> 0x7fff7000 <= shad mb /\ shad mb + ms / 8 <= 0x10007fff8000.
Proof.
  intros L mb ms n WF1. cbn [sec_wf1] in WF1. destruct WF1 as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & _ & _ & _ & _ & _ & _ & MSM & MSB). rewrite <- G4 in MSM, MSB.
  pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in G2. rewrite shad_div. unfold ASHOFF.
  clear -G1 G2 G3 MSM MSB ATR. Z.div_mod_to_equations. lia.
Qed.

Section Put.
Variables (L : alayout) (RESV : list (Z * Z)) (W0 : list (Z * Z)) (m m' : amem) (st : astate).
Hypothesis ARV : aresv_ok L RESV.
Hypothesis MU0 : munch W0 m m'.
Hypothesis SU0 : sec_untouchedD L RESV st W0.
Hypothesis ALO : alayout_ok L.
Let W := List.filter nonempty W0.
Let MU : munch W m m' := munch_filter_nonempty W0 m m' MU0.
Let SU : sec_untouchedD L RESV st W := sec_untouchedD_filter L RESV st W0 SU0.
Let NE : Forall (fun iv => fst iv < snd iv) W := nonempty_filter W0.

Lemma DD_img : forall A k, 0x10000 <= A -> A + k <= AIMG_HI -> 0 < k -> (forall a, A <= a < A + k -> aknown L a -> False) -> disjoint_from W A k.
Proof.
  intros A k H1 H2 H3 CL. apply (suD_disjoint L RESV st); [exact SU| exact NE| exact H3| exact CL|].
  left. destruct ARV as (PCI & _). exists 0x10000, AIMG_HI. split; [exact PCI| lia].
Qed.
Lemma DD_inst : forall A k, AINSTANCE + 72 <= A -> A + k <= AINSTANCE + 728 -> 0 < k -> disjoint_from W A k.
Proof. intros A k H1 H2 H3. apply DD_img; [unfold AINSTANCE in *; lia| unfold AINSTANCE, AIMG_HI in *; lia| exact H3|]. intros a Ha. apply (clear_inst L ALO). lia. Qed.
Lemma DD_ptr : forall A k, al_ptr_array L <= A -> A + k <= al_ptr_array L + 8388608 -> 0 < k -> disjoint_from W A k.
Proof.
  intros A k H1 H2 H3. apply (suD_disjoint L RESV st); [exact SU| exact NE| exact H3| |].
  - intros a Ha. apply (clear_ptr L ALO). lia.
  - left. destruct ARV as (_ & _ & _ & PCP & _). exists (al_ptr_array L), (al_ptr_array L + 0x800000). split; [exact PCP| lia].
Qed.
Lemma DD_band : forall A k, 0x7fff7000 <= A -> A + k <= 0x10007fff8000 -> 0 < k -> (forall a, A <= a < A + k -> aknown L a -> False) -> disjoint_from W A k.
Proof.
  intros A k H1 H2 H3 CL. apply (suD_disjoint L RESV st); [exact SU| exact NE| exact H3| exact CL|].
  left. destruct ARV as (_ & PCSH & _). exists 0x7fff7000, 0x10007fff8000. split; [exact PCSH| lia].
Qed.
Lemma DD_chunk : forall mb ms n A k, In (CSec mb ms n) (sec_chunks_of st) -> sec_wf1 L (CSec mb ms n) -> mb <= A -> A + k <= mb + ms -> 0 < k -> disjoint_from W A k.
Proof.
  intros mb ms n A k Hin WF1 H1 H2 H3. apply (suD_disjoint L RESV st); [exact SU| exact NE| exact H3| |].
  - intros a Ha. apply (clear_chunk L ALO mb ms n); [exact WF1| lia].
  - right. exists (mb, mb + ms). split; [exact (sec_chunk_flat st mb ms n Hin)| cbn [fst snd]; lia].
Qed.
Lemma DD_shadow : forall mb ms n A k, sec_wf1 L (CSec mb ms n) -> shad mb <= A -> A + k <= shad mb + ms / 8 -> 0 < k -> disjoint_from W A k.
Proof.
  intros mb ms n A k WF1 H1 H2 H3. destruct (chunk_shadow_band L mb ms n WF1) as [B1 B2].
  apply DD_band; [lia| lia| exact H3|]. intros a Ha. apply (clear_chunk_shadow L ALO mb ms n); [exact WF1| lia].
Qed.

Theorem asec_put : forall st' X X',
  ASEC_of L st X m -> sec_sameX st st' -> AEXH L st' m' -> ASEC_of L st' X' m'.
Proof.
  intros st' X X' (WFS & ARR & INST & PZ & SHZ & _) (EN & ER & EP & EL & PERM) AXH'.
  unfold ASEC_of, ASECc.
  pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  assert (ALLSEC : forall ch, In ch (sec_chunks_of st) -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n)).
  { intros ch Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1. destruct ch as [c n|mb ms n]; [destruct W1|].
    exists mb, ms, n. split; [reflexivity| exact W1]. }
  split; [| split; [| split; [| split; [| split]]]].
  6: exact (proj1 (AEXHc_of L st' m') AXH').
  -
    unfold asec_wf. rewrite EP, ER, EN. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|]. split; [| split; [exact WB| split]].
    + rewrite (Permutation_length PERM). exact WL.
    + rewrite Forall_forall in WF1 |- *. intros ch Hin. apply WF1. eapply Permutation_in; [exact PERM| exact Hin].
    + eapply sec_disjoint_perm; [apply Permutation_sym; exact PERM| exact WD].
  -
    destruct ARR as (order & PO & U64 & JK & PER). exists order.
    assert (LEN : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
    split; [eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PERM]|].
    split; [| split].
    + destruct order as [|o0 order'].
      * destruct U64 as [[B0 [B1 _]] [V0 [V1 _]]]. split; [split; [exact B0| split; [exact B1| cbn; intros; lia]] | split; [exact V0| split; [exact V1| cbn; intros; lia]]].
      * eapply u64arr_frameD; [exact U64| exact MU|]. rewrite length_map. apply DD_ptr; cbn [length] in LEN |- *; clear -LEN WB WR; lia.
    + rewrite EN, ER. eapply junk_frameD; [exact JK| exact MU|]. intros POS. apply DD_ptr; clear -POS WB WR; lia.
    + intros i ch Hi. destruct (PER i ch Hi) as (lv & LV & CH).
      assert (Hin : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
      destruct (ALLSEC ch Hin) as (mb & ms & n & -> & W1).
      exists lv. split.
      * rewrite LV. unfold sec_live. split; intros [p Hp]; exists p; [apply (proj2 (EL p mb ms n)); exact Hp| apply (proj1 (EL p mb ms n)); exact Hp].
      * pose proof W1 as W0'. cbn [sec_wf1] in W0'. destruct W0' as (G1 & G2 & G3 & G4 & G5 & G6 & _).
        pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MSB). rewrite <- G4 in MSB.
        eapply (asec_chunk_frameD' L W m m' mb ms n (Z.of_nat i) lv MU W1).
        -- intros A k H1 H2 H3. apply (DD_chunk mb ms n); [exact Hin| exact W1| lia| lia| lia].
        -- intros A k H1 H2 H3. apply (DD_shadow mb ms n); [exact W1| lia| lia| lia].
        -- pose proof CH as CH0. cbn [asec_chunk] in CH0. destruct CH0 as (Hh & _).
           eapply cells_frameD; [exact Hh| exact MU|]. cbn [cells_size csize Nat.add]. apply (DD_chunk mb ms n); [exact Hin| exact W1| lia| clear -MSB; lia| lia].
        -- exists (Z.of_nat i). exact CH.
  -
    destruct INST as (I1 & [srt I2] & I3 & I4 & I5 & I6). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frameD; [exact I1| exact MU| cbn; apply DD_inst; unfold AINSTANCE; lia]|].
    split; [exists srt; eapply cells_frameD; [exact I2| exact MU| cbn; apply DD_inst; unfold AINSTANCE; lia]|].
    split; [eapply junk_frameD; [exact I3| exact MU| intros _; apply DD_inst; unfold AINSTANCE; lia]|].
    split; [eapply junk_frameD; [exact I4| exact MU| intros _; apply DD_inst; unfold AINSTANCE; lia]|].
    split; [eapply cells_frameD; [exact I5| exact MU| cbn; apply DD_inst; unfold AINSTANCE; lia]|].
    eapply junk_frameD; [exact I6| exact MU| intros _; apply DD_inst; unfold AINSTANCE; lia].
  -
    unfold aprim0 in *. eapply azero_frameD; [exact PZ| exact MU|]. intros POS.
    pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_space L ALO) as RSP. pose proof atop_range as ATR.
    apply DD_band; [| | exact POS| intros a Ha; apply (clear_prim0 L ALO); exact Ha].
    + rewrite shad_div. unfold ASHOFF. clear -ORH RSP. Z.div_mod_to_equations. lia.
    + unfold K_REGION. change (2^32) with 4294967296. rewrite shad_div, shlen_div. unfold ASHOFF. clear -ORS ORH RSP ATR. Z.div_mod_to_equations. lia.
  -
    intros x Hx HF HC.
    assert (SX : 0x7fff7000 <= shad x /\ shad x + 1 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM, AIMG_HI, KLS in *; pose proof atop_range as ATR; clear -Hx ATR; Z.div_mod_to_equations; lia).
    assert (HC0 : Forall (fun ch => ~ (sec_mb ch <= x < sec_mb ch + sec_ms ch)) (sec_chunks_of st)).
    { rewrite Forall_forall in HC |- *. intros ch Hin. apply HC. eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]. }
    rewrite <- (SHZ x Hx HF HC0). apply MU. rewrite wa_unsigned by (clear -SX; lia).
    eapply (disjoint_outside W (shad x) 1); [| clear; lia].
    apply DD_band; [lia| lia| clear; lia|]. intros a Ha K. apply (clear_free_shadow L ALO x Hx HF). replace (shad x) with a by (clear -Ha; lia). exact K.
Qed.
End Put.

Theorem asec_hx_get : forall L st X m, ASEC_of L st X m -> AEXH L st m.
Proof. intros L st X m (_ & _ & _ & _ & _ & AX). exact (proj2 (AEXHc_of L st m) AX). Qed.
Theorem asec_hsD : forall L RESV st st' X X' m m' W,
  aresv_ok L RESV -> ASEC_of L st X m -> munch W m m' -> sec_untouchedD L RESV st W -> sec_sameX st st' -> AEXH L st' m' -> ASEC_of L st' X' m'.
Proof.
  intros L RESV st st' X X' m m' W ARV HS MU SU SS AX. pose proof HS as ((ALO & _) & _).
  exact (asec_put L RESV W m m' st ARV MU SU ALO st' X X' HS SS AX).
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ARep.TwinB ARepFrame.TwinB ALayout.TwinB AHeapP.TwinB ASecFacts.TwinB ASec.TwinB ARepExt.TwinB AMalloc_iface.TwinB AFrameD.TwinB ASecFrame.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_kit.TwinB.ASF_kit.
Import AExh.TwinB ARefillP_x.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.

Definition sprot (RESV : list (Z * Z)) (st : astate) (A k : Z) : Prop :=
     (exists lo hi, pcov RESV lo hi /\ lo <= A /\ A + k <= hi)
  \/ (exists iv, In iv (flat_map sec_iv (achunks st)) /\ fst iv <= A /\ A + k <= snd iv).

Lemma suD_disjoint : forall L RESV st W A k,
  sec_untouchedD L RESV st W -> Forall (fun iv => fst iv < snd iv) W -> 0 < k ->
  (forall a, A <= a < A + k -> aknown L a -> False) -> sprot RESV st A k ->
  disjoint_from W A k.
Proof.
  intros L RESV st W A k SU NE Hk CL PR. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  inversion SU as [|x l Hx Hl]; subst. inversion NE as [|x' l' Hn Hnl]; subst. split; [| apply IH; [exact Hl| exact Hnl]].
  cbn [fst snd] in Hx, Hn.
  destruct (Z_lt_le_dec lo (A + k)) as [L1|L1]; [| left; lia].
  destruct (Z_lt_le_dec A hi) as [L2|L2]; [| right; lia].
  exfalso. destruct Hx as [KN|[_ AV]].
  - apply (CL (Z.max A lo)); [lia|]. apply KN. lia.
  - unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV1 AV2].
    destruct PR as [(l0 & h0 & PC & P1 & P2)|(iv & Hiv & P1 & P2)].
    + pose proof (pcov_clear _ _ _ _ _ PC AV1 ltac:(lia) ltac:(lia)) as D. lia.
    + pose proof (proj1 (forallb_forall _ _) AV2 iv Hiv) as D. unfold iv_clear in D. apply orb_prop in D as [D|D]; apply Z.leb_le in D; lia.
Qed.

Lemma sec_untouchedD_filter : forall L RESV st W, sec_untouchedD L RESV st W -> sec_untouchedD L RESV st (List.filter nonempty W).
Proof. intros L RESV st W SU. unfold sec_untouchedD in *. rewrite Forall_forall in SU |- *. intros iv Hin. apply SU. apply List.filter_In in Hin. tauto. Qed.

Lemma sec_chunk_flat : forall st mb ms n, In (CSec mb ms n) (sec_chunks_of st) -> In (mb, mb + ms) (flat_map sec_iv (achunks st)).
Proof.
  intros st mb ms n H. unfold sec_chunks_of in H. apply List.filter_In in H. destruct H as [H _].
  apply in_flat_map. exists (CSec mb ms n). split; [exact H| left; reflexivity].
Qed.

Lemma chunk_shadow_band : forall L mb ms n, sec_wf1 L (CSec mb ms n) -> 0x7fff7000 <= shad mb /\ shad mb + ms / 8 <= 0x10007fff8000.
Proof.
  intros L mb ms n WF1. cbn [sec_wf1] in WF1. destruct WF1 as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & _ & _ & _ & _ & _ & _ & MSM & MSB). rewrite <- G4 in MSM, MSB.
  pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in G2. rewrite shad_div. unfold ASHOFF.
  clear -G1 G2 G3 MSM MSB ATR. Z.div_mod_to_equations. lia.
Qed.

Section Put.
Variables (L : alayout) (RESV : list (Z * Z)) (W0 : list (Z * Z)) (m m' : amem) (st : astate).
Hypothesis ARV : aresv_ok L RESV.
Hypothesis MU0 : munch W0 m m'.
Hypothesis SU0 : sec_untouchedD L RESV st W0.
Hypothesis ALO : alayout_ok L.
Let W := List.filter nonempty W0.
Let MU : munch W m m' := munch_filter_nonempty W0 m m' MU0.
Let SU : sec_untouchedD L RESV st W := sec_untouchedD_filter L RESV st W0 SU0.
Let NE : Forall (fun iv => fst iv < snd iv) W := nonempty_filter W0.

Lemma DD_img : forall A k, 0x10000 <= A -> A + k <= AIMG_HI -> 0 < k -> (forall a, A <= a < A + k -> aknown L a -> False) -> disjoint_from W A k.
Proof.
  intros A k H1 H2 H3 CL. apply (suD_disjoint L RESV st); [exact SU| exact NE| exact H3| exact CL|].
  left. destruct ARV as (PCI & _). exists 0x10000, AIMG_HI. split; [exact PCI| lia].
Qed.
Lemma DD_inst : forall A k, AINSTANCE + 72 <= A -> A + k <= AINSTANCE + 728 -> 0 < k -> disjoint_from W A k.
Proof. intros A k H1 H2 H3. apply DD_img; [unfold AINSTANCE in *; lia| unfold AINSTANCE, AIMG_HI in *; lia| exact H3|]. intros a Ha. apply (clear_inst L ALO). lia. Qed.
Lemma DD_ptr : forall A k, al_ptr_array L <= A -> A + k <= al_ptr_array L + 8388608 -> 0 < k -> disjoint_from W A k.
Proof.
  intros A k H1 H2 H3. apply (suD_disjoint L RESV st); [exact SU| exact NE| exact H3| |].
  - intros a Ha. apply (clear_ptr L ALO). lia.
  - left. destruct ARV as (_ & _ & _ & PCP & _). exists (al_ptr_array L), (al_ptr_array L + 0x800000). split; [exact PCP| lia].
Qed.
Lemma DD_band : forall A k, 0x7fff7000 <= A -> A + k <= 0x10007fff8000 -> 0 < k -> (forall a, A <= a < A + k -> aknown L a -> False) -> disjoint_from W A k.
Proof.
  intros A k H1 H2 H3 CL. apply (suD_disjoint L RESV st); [exact SU| exact NE| exact H3| exact CL|].
  left. destruct ARV as (_ & PCSH & _). exists 0x7fff7000, 0x10007fff8000. split; [exact PCSH| lia].
Qed.
Lemma DD_chunk : forall mb ms n A k, In (CSec mb ms n) (sec_chunks_of st) -> sec_wf1 L (CSec mb ms n) -> mb <= A -> A + k <= mb + ms -> 0 < k -> disjoint_from W A k.
Proof.
  intros mb ms n A k Hin WF1 H1 H2 H3. apply (suD_disjoint L RESV st); [exact SU| exact NE| exact H3| |].
  - intros a Ha. apply (clear_chunk L ALO mb ms n); [exact WF1| lia].
  - right. exists (mb, mb + ms). split; [exact (sec_chunk_flat st mb ms n Hin)| cbn [fst snd]; lia].
Qed.
Lemma DD_shadow : forall mb ms n A k, sec_wf1 L (CSec mb ms n) -> shad mb <= A -> A + k <= shad mb + ms / 8 -> 0 < k -> disjoint_from W A k.
Proof.
  intros mb ms n A k WF1 H1 H2 H3. destruct (chunk_shadow_band L mb ms n WF1) as [B1 B2].
  apply DD_band; [lia| lia| exact H3|]. intros a Ha. apply (clear_chunk_shadow L ALO mb ms n); [exact WF1| lia].
Qed.

Theorem asec_put : forall st' X X',
  ASEC_of L st X m -> sec_sameX st st' -> AEXH L st' m' -> ASEC_of L st' X' m'.
Proof.
  intros st' X X' (WFS & ARR & INST & PZ & SHZ & _) (EN & ER & EP & EL & PERM) AXH'.
  unfold ASEC_of, ASECc.
  pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  assert (ALLSEC : forall ch, In ch (sec_chunks_of st) -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n)).
  { intros ch Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1. destruct ch as [c n|mb ms n]; [destruct W1|].
    exists mb, ms, n. split; [reflexivity| exact W1]. }
  split; [| split; [| split; [| split; [| split]]]].
  6: exact (proj1 (AEXHc_of L st' m') AXH').
  -
    unfold asec_wf. rewrite EP, ER, EN. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|]. split; [| split; [exact WB| split]].
    + rewrite (Permutation_length PERM). exact WL.
    + rewrite Forall_forall in WF1 |- *. intros ch Hin. apply WF1. eapply Permutation_in; [exact PERM| exact Hin].
    + eapply sec_disjoint_perm; [apply Permutation_sym; exact PERM| exact WD].
  -
    destruct ARR as (order & PO & U64 & JK & PER). exists order.
    assert (LEN : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
    split; [eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PERM]|].
    split; [| split].
    + destruct order as [|o0 order'].
      * destruct U64 as [[B0 [B1 _]] [V0 [V1 _]]]. split; [split; [exact B0| split; [exact B1| cbn; intros; lia]] | split; [exact V0| split; [exact V1| cbn; intros; lia]]].
      * eapply u64arr_frameD; [exact U64| exact MU|]. rewrite length_map. apply DD_ptr; cbn [length] in LEN |- *; clear -LEN WB WR; lia.
    + rewrite EN, ER. eapply junk_frameD; [exact JK| exact MU|]. intros POS. apply DD_ptr; clear -POS WB WR; lia.
    + intros i ch Hi. destruct (PER i ch Hi) as (lv & LV & CH).
      assert (Hin : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
      destruct (ALLSEC ch Hin) as (mb & ms & n & -> & W1).
      exists lv. split.
      * rewrite LV. unfold sec_live. split; intros [p Hp]; exists p; [apply (proj2 (EL p mb ms n)); exact Hp| apply (proj1 (EL p mb ms n)); exact Hp].
      * pose proof W1 as W0'. cbn [sec_wf1] in W0'. destruct W0' as (G1 & G2 & G3 & G4 & G5 & G6 & _).
        pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MSB). rewrite <- G4 in MSB.
        eapply (asec_chunk_frameD' L W m m' mb ms n (Z.of_nat i) lv MU W1).
        -- intros A k H1 H2 H3. apply (DD_chunk mb ms n); [exact Hin| exact W1| lia| lia| lia].
        -- intros A k H1 H2 H3. apply (DD_shadow mb ms n); [exact W1| lia| lia| lia].
        -- pose proof CH as CH0. cbn [asec_chunk] in CH0. destruct CH0 as (Hh & _).
           eapply cells_frameD; [exact Hh| exact MU|]. cbn [cells_size csize Nat.add]. apply (DD_chunk mb ms n); [exact Hin| exact W1| lia| clear -MSB; lia| lia].
        -- exists (Z.of_nat i). exact CH.
  -
    destruct INST as (I1 & [srt I2] & I3 & I4 & I5 & I6). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frameD; [exact I1| exact MU| cbn; apply DD_inst; unfold AINSTANCE; lia]|].
    split; [exists srt; eapply cells_frameD; [exact I2| exact MU| cbn; apply DD_inst; unfold AINSTANCE; lia]|].
    split; [eapply junk_frameD; [exact I3| exact MU| intros _; apply DD_inst; unfold AINSTANCE; lia]|].
    split; [eapply junk_frameD; [exact I4| exact MU| intros _; apply DD_inst; unfold AINSTANCE; lia]|].
    split; [eapply cells_frameD; [exact I5| exact MU| cbn; apply DD_inst; unfold AINSTANCE; lia]|].
    eapply junk_frameD; [exact I6| exact MU| intros _; apply DD_inst; unfold AINSTANCE; lia].
  -
    unfold aprim0 in *. eapply azero_frameD; [exact PZ| exact MU|]. intros POS.
    pose proof (ao_res L ALO) as (_ & _ & ORS & _). pose proof (ao_res_hi L ALO) as ORH. pose proof (ao_space L ALO) as RSP. pose proof atop_range as ATR.
    apply DD_band; [| | exact POS| intros a Ha; apply (clear_prim0 L ALO); exact Ha].
    + rewrite shad_div. unfold ASHOFF. clear -ORH RSP. Z.div_mod_to_equations. lia.
    + unfold K_REGION. change (2^32) with 4294967296. rewrite shad_div, shlen_div. unfold ASHOFF. clear -ORS ORH RSP ATR. Z.div_mod_to_equations. lia.
  -
    intros x Hx HF HC.
    assert (SX : 0x7fff7000 <= shad x /\ shad x + 1 <= 0x10007fff8000) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM, AIMG_HI, KLS in *; pose proof atop_range as ATR; clear -Hx ATR; Z.div_mod_to_equations; lia).
    assert (HC0 : Forall (fun ch => ~ (sec_mb ch <= x < sec_mb ch + sec_ms ch)) (sec_chunks_of st)).
    { rewrite Forall_forall in HC |- *. intros ch Hin. apply HC. eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]. }
    rewrite <- (SHZ x Hx HF HC0). apply MU. rewrite wa_unsigned by (clear -SX; lia).
    eapply (disjoint_outside W (shad x) 1); [| clear; lia].
    apply DD_band; [lia| lia| clear; lia|]. intros a Ha K. apply (clear_free_shadow L ALO x Hx HF). replace (shad x) with a by (clear -Ha; lia). exact K.
Qed.
End Put.

Theorem asec_hx_get : forall L st X m, ASEC_of L st X m -> AEXH L st m.
Proof. intros L st X m (_ & _ & _ & _ & _ & AX). exact (proj2 (AEXHc_of L st m) AX). Qed.
Theorem asec_hsD : forall L RESV st st' X X' m m' W,
  aresv_ok L RESV -> ASEC_of L st X m -> munch W m m' -> sec_untouchedD L RESV st W -> sec_sameX st st' -> AEXH L st' m' -> ASEC_of L st' X' m'.
Proof.
  intros L RESV st st' X X' m m' W ARV HS MU SU SS AX. pose proof HS as ((ALO & _) & _).
  exact (asec_put L RESV W m m' st ARV MU SU ALO st' X X' HS SS AX).
Qed.
End CANSEC1.
End TwinB.
