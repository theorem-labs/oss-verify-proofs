(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCHuff BzCMtf BzR5a.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzR5cW.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Fixpoint wapp (b : bw) (ws : list (Z * Z)) : bw :=
  match ws with [] => b | (n, v) :: ws' => wapp (bsW b n v) ws' end.

Lemma wapp_app : forall ws1 ws2 b, wapp b (ws1 ++ ws2) = wapp (wapp b ws1) ws2.
Proof. induction ws1 as [|[n v] ws1 IH]; intros; cbn [wapp app]; [reflexivity| apply IH]. Qed.
(* [comment removed for export] *)

Theorem wapp_abs : forall ws b, wlegal ws -> bw_clean b ->
  bw_abs (wapp b ws) = bapp (bw_abs b) (wbits ws) /\ bw_clean (wapp b ws).
Proof.
  induction ws as [|[n v] ws IH]; intros b W C; cbn [wapp wbits].
  - rewrite bapp_bnil_r. split; [reflexivity| exact C].
  - apply wlegal_cons in W as [[Wn Wv] W].
    destruct (bsW_abs b n v C Wn Wv) as [E C1]. destruct (IH (bsW b n v) W C1) as [E2 C2].
    rewrite E2, E. split; [| exact C2]. apply bapp_assoc; [cbn; lia| apply wbits_len; exact W].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bit01 (x : Z) : Z := if negb (x =? 0) then 1 else 0.

Fixpoint ws_in16 (n : nat) (in16 : zarr) (i : Z) : list (Z * Z) :=
  match n with O => [] | S n' => (1, bit01 (zget in16 i)) :: ws_in16 n' in16 (i + 1) end.
Lemma sm_put_in16_wapp : forall n b in16 i, sm_put_in16 n b in16 i = wapp b (ws_in16 n in16 i).
Proof. induction n as [|n IH]; intros; cbn [sm_put_in16 ws_in16 wapp]; [reflexivity| apply IH]. Qed.

Fixpoint ws_inuse_row (n : nat) (inUse : zarr) (i j : Z) : list (Z * Z) :=
  match n with O => [] | S n' => (1, bit01 (zget inUse (i * 16 + j))) :: ws_inuse_row n' inUse i (j + 1) end.
Lemma sm_put_inuse_row_wapp : forall n b inUse i j, sm_put_inuse_row n b inUse i j = wapp b (ws_inuse_row n inUse i j).
Proof. induction n as [|n IH]; intros; cbn [sm_put_inuse_row ws_inuse_row wapp]; [reflexivity| apply IH]. Qed.
Fixpoint ws_inuse (n : nat) (in16 inUse : zarr) (i : Z) : list (Z * Z) :=
  match n with
  | O => []
  | S n' => (if negb (zget in16 i =? 0) then ws_inuse_row 16 inUse i 0 else []) ++ ws_inuse n' in16 inUse (i + 1)
  end.
Lemma sm_put_inuse_wapp : forall n b in16 inUse i, sm_put_inuse n b in16 inUse i = wapp b (ws_inuse n in16 inUse i).
Proof.
  induction n as [|n IH]; intros; cbn [sm_put_inuse ws_inuse]; [reflexivity|].
  rewrite wapp_app, IH. destruct (negb (zget in16 i =? 0)); [rewrite sm_put_inuse_row_wapp|]; reflexivity.
Qed.

Lemma sm_put_ones_wapp : forall n b, sm_put_ones n b = wapp b (repeat (1, 1) n).
Proof. induction n as [|n IH]; intros; cbn [sm_put_ones repeat wapp]; [reflexivity| apply IH]. Qed.
Fixpoint ws_sels (n : nat) (selMtf : zarr) (i : Z) : list (Z * Z) :=
  match n with O => [] | S n' => (repeat (1, 1) (Z.to_nat (zget selMtf i)) ++ [(1, 0)]) ++ ws_sels n' selMtf (i + 1) end.
Lemma sm_put_sels_wapp : forall n b selMtf i, sm_put_sels n b selMtf i = wapp b (ws_sels n selMtf i).
Proof.
  induction n as [|n IH]; intros; cbn [sm_put_sels ws_sels]; [reflexivity|].
  rewrite !wapp_app, <- sm_put_ones_wapp. cbn [wapp]. apply IH.
Qed.

(* [comment removed for export] *)
Fixpoint ws_up (f : nat) (curr tgt : Z) : list (Z * Z) :=
  match f with O => [] | S f' => if curr <? tgt then (2, 2) :: ws_up f' (curr + 1) tgt else [] end.
Fixpoint up_end (f : nat) (curr tgt : Z) : Z :=
  match f with O => curr | S f' => if curr <? tgt then up_end f' (curr + 1) tgt else curr end.
Lemma sm_put_up_wapp : forall f b curr tgt, sm_put_up f b curr tgt = (wapp b (ws_up f curr tgt), up_end f curr tgt).
Proof.
  induction f as [|f IH]; intros; cbn [sm_put_up ws_up up_end wapp]; [reflexivity|].
  destruct (curr <? tgt); [apply IH| reflexivity].
Qed.
Fixpoint ws_down (f : nat) (curr tgt : Z) : list (Z * Z) :=
  match f with O => [] | S f' => if tgt <? curr then (2, 3) :: ws_down f' (curr - 1) tgt else [] end.
Fixpoint down_end (f : nat) (curr tgt : Z) : Z :=
  match f with O => curr | S f' => if tgt <? curr then down_end f' (curr - 1) tgt else curr end.
Lemma sm_put_down_wapp : forall f b curr tgt, sm_put_down f b curr tgt = (wapp b (ws_down f curr tgt), down_end f curr tgt).
Proof.
  induction f as [|f IH]; intros; cbn [sm_put_down ws_down down_end wapp]; [reflexivity|].
  destruct (tgt <? curr); [apply IH| reflexivity].
Qed.
(* [comment removed for export] *)
Lemma up_end_reach : forall f curr tgt, curr <= tgt -> tgt - curr <= Z.of_nat f -> up_end f curr tgt = tgt.
Proof.
  induction f as [|f IH]; intros curr tgt H1 H2; cbn [up_end]; [lia|].
  destruct (Z.ltb_spec curr tgt); [apply IH; lia| lia].
Qed.
Lemma down_end_reach : forall f curr tgt, tgt <= curr -> curr - tgt <= Z.of_nat f -> down_end f curr tgt = tgt.
Proof.
  induction f as [|f IH]; intros curr tgt H1 H2; cbn [down_end]; [lia|].
  destruct (Z.ltb_spec tgt curr); [apply IH; lia| lia].
Qed.
Lemma up_end_id : forall f curr tgt, tgt <= curr -> up_end f curr tgt = curr.
Proof. intros [|f] curr tgt H; cbn [up_end]; [reflexivity|]. destruct (Z.ltb_spec curr tgt); [lia| reflexivity]. Qed.
Lemma ws_up_nil : forall f curr tgt, tgt <= curr -> ws_up f curr tgt = [].
Proof. intros [|f] curr tgt H; cbn [ws_up]; [reflexivity|]. destruct (Z.ltb_spec curr tgt); [lia| reflexivity]. Qed.
Lemma ws_down_nil : forall f curr tgt, curr <= tgt -> ws_down f curr tgt = [].
Proof. intros [|f] curr tgt H; cbn [ws_down]; [reflexivity|]. destruct (Z.ltb_spec tgt curr); [lia| reflexivity]. Qed.
Lemma down_end_id : forall f curr tgt, curr <= tgt -> down_end f curr tgt = curr.
Proof. intros [|f] curr tgt H; cbn [down_end]; [reflexivity|]. destruct (Z.ltb_spec tgt curr); [lia| reflexivity]. Qed.

(* [comment removed for export] *)
Definition ws_delta (curr tgt : Z) : list (Z * Z) :=
  (if curr <? tgt then repeat (2, 2) (Z.to_nat (tgt - curr)) else repeat (2, 3) (Z.to_nat (curr - tgt))) ++ [(1, 0)].
Lemma ws_up_repeat : forall f curr tgt, tgt - curr <= Z.of_nat f -> ws_up f curr tgt = repeat (2, 2) (Z.to_nat (tgt - curr)).
Proof.
  induction f as [|f IH]; intros curr tgt H; cbn [ws_up].
  - replace (Z.to_nat (tgt - curr)) with 0%nat by lia. reflexivity.
  - destruct (Z.ltb_spec curr tgt).
    + rewrite IH by lia. replace (Z.to_nat (tgt - curr)) with (S (Z.to_nat (tgt - (curr + 1)))) by lia. reflexivity.
    + replace (Z.to_nat (tgt - curr)) with 0%nat by lia. reflexivity.
Qed.
Lemma ws_down_repeat : forall f curr tgt, curr - tgt <= Z.of_nat f -> ws_down f curr tgt = repeat (2, 3) (Z.to_nat (curr - tgt)).
Proof.
  induction f as [|f IH]; intros curr tgt H; cbn [ws_down].
  - replace (Z.to_nat (curr - tgt)) with 0%nat by lia. reflexivity.
  - destruct (Z.ltb_spec tgt curr).
    + rewrite IH by lia. replace (Z.to_nat (curr - tgt)) with (S (Z.to_nat (curr - 1 - tgt))) by lia. reflexivity.
    + replace (Z.to_nat (curr - tgt)) with 0%nat by lia. reflexivity.
Qed.

Fixpoint ws_lens_row (n : nat) (len : zarr) (t i curr : Z) : list (Z * Z) :=
  match n with
  | O => []
  | S n' => let tgt := zget len (258 * t + i) in ws_delta curr tgt ++ ws_lens_row n' len t (i + 1) tgt
  end.
Lemma sm_put_lens_row_wapp : forall n b len t i curr,
  (forall j, i <= j < i + Z.of_nat n -> 1 <= zget len (258 * t + j) <= 20) -> 1 <= curr <= 20 ->
  fst (sm_put_lens_row n b len t i curr) = wapp b (ws_lens_row n len t i curr).
Proof.
  induction n as [|n IH]; intros b len t i curr H Hc; cbn [sm_put_lens_row ws_lens_row]; [reflexivity|].
  rewrite sm_put_up_wapp, sm_put_down_wapp.
  set (tgt := zget len (258 * t + i)) in *. pose proof (H i ltac:(lia)) as A1. fold tgt in A1.
  unfold ws_delta. cbn [fst].
  destruct (Z.ltb_spec curr tgt) as [LT|GE].
  - rewrite (up_end_reach 40 curr tgt) by (cbn; lia). rewrite ws_down_nil, down_end_id by lia.
    rewrite (ws_up_repeat 40) by (cbn; lia). rewrite !wapp_app. cbn [wapp]. apply IH; [intros; apply H; lia| lia].
  - rewrite up_end_id, ws_up_nil by lia. rewrite (ws_down_repeat 40) by (cbn; lia).
    rewrite (down_end_reach 40) by (cbn; lia). rewrite !wapp_app. cbn [wapp]. apply IH; [intros; apply H; lia| lia].
Qed.

Fixpoint ws_lens (n : nat) (len : zarr) (alphaSize t : Z) : list (Z * Z) :=
  match n with
  | O => []
  | S n' => let curr := zget len (258 * t + 0) in
            ((5, curr) :: ws_lens_row (Z.to_nat alphaSize) len t 0 curr) ++ ws_lens n' len alphaSize (t + 1)
  end.
Lemma sm_put_lens_wapp : forall n b len alphaSize t,
  (forall t' v, t <= t' < t + Z.of_nat n -> 0 <= v < alphaSize -> 1 <= zget len (258 * t' + v) <= 20) -> 1 <= alphaSize ->
  sm_put_lens n b len alphaSize t = wapp b (ws_lens n len alphaSize t).
Proof.
  induction n as [|n IH]; intros b len alphaSize t H HA; cbn [sm_put_lens ws_lens]; [reflexivity|].
  rewrite wapp_app. cbn [wapp app].
  pose proof (sm_put_lens_row_wapp (Z.to_nat alphaSize) (bsW b 5 (zget len (258 * t + 0))) len t 0 (zget len (258 * t + 0))) as R.
  destruct (sm_put_lens_row _ _ _ _ _ _) as [b1 c1]. cbn [fst] in R. rewrite R.
  - apply IH; [intros; apply H; lia| lia].
  - intros j Hj. apply H; lia.
  - apply H; lia.
Qed.

(* [comment removed for export] *)
Fixpoint ws_syms (n : nat) (len code arr1 : zarr) (sel i : Z) : list (Z * Z) :=
  match n with
  | O => []
  | S n' => let v := mtfv_at arr1 i in (zget len (258 * sel + v), zget code (258 * sel + v)) :: ws_syms n' len code arr1 sel (i + 1)
  end.
Lemma sm_put_syms_wapp : forall n b len code arr1 sel i, sm_put_syms n b len code arr1 sel i = wapp b (ws_syms n len code arr1 sel i).
Proof. induction n as [|n IH]; intros; cbn [sm_put_syms ws_syms wapp]; [reflexivity| apply IH]. Qed.
Fixpoint ws_data (fuel : nat) (len code arr1 sel : zarr) (nMTF gs selCtr : Z) : list (Z * Z) :=
  match fuel with
  | O => []
  | S f => if nMTF <=? gs then [] else
           let ge := gs + BZ_G_SIZE - 1 in
           let ge := if nMTF <=? ge then nMTF - 1 else ge in
           ws_syms (Z.to_nat (ge - gs + 1)) len code arr1 (zget sel selCtr) gs ++ ws_data f len code arr1 sel nMTF (ge + 1) (selCtr + 1)
  end.
Lemma sm_put_data_wapp : forall fuel b len code arr1 sel nMTF gs selCtr,
  fst (sm_put_data fuel b len code arr1 sel nMTF gs selCtr) = wapp b (ws_data fuel len code arr1 sel nMTF gs selCtr).
Proof.
  induction fuel as [|f IH]; intros; cbn [sm_put_data ws_data]; [reflexivity|].
  destruct (nMTF <=? gs); [reflexivity|]. rewrite wapp_app, <- sm_put_syms_wapp. apply IH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ws_send (inUse in16 selMtf len code arr1 sel : zarr) (nGroups nSelectors alphaSize nMTF : Z) : list (Z * Z) :=
  ws_in16 16 in16 0 ++ ws_inuse 16 in16 inUse 0 ++ [(3, nGroups); (15, nSelectors)] ++
  ws_sels (Z.to_nat nSelectors) selMtf 0 ++ ws_lens (Z.to_nat nGroups) len alphaSize 0 ++
  ws_data (Z.to_nat (nMTF + 1)) len code arr1 sel nMTF 0 0.

Theorem sendMTFValues_wapp : forall e cost0 fave0 pos0 in160 heap0 weight0 parent0,
  let alphaSize := e_nInUse e + 2 in
  let nMTF := e_nMTF e in
  let nGroups := sm_nGroups nMTF in
  let len := sm_len_init 6 (e_len e) alphaSize 0 in
  let ip := sm_init_tables 8 (e_mtfFreq e) nGroups alphaSize (SIP len nGroups nMTF 0) in
  let it := sm_iters BZ_N_ITERS (e_arr1 e) nGroups alphaSize nMTF
              (SITS (ip_len ip) (e_rfreq e) (e_len_pack e) (e_selector e) cost0 fave0 0 heap0 weight0 parent0) in
  let nSelectors := it_nSel it in
  let pos := yy_init (Z.to_nat nGroups) pos0 0 in
  let selMtf := snd (sm_selmtf (Z.to_nat nSelectors) pos (it_sel it) (e_selectorMtf e) 0) in
  let code := sm_assign (Z.to_nat nGroups) (e_code e) (it_len it) alphaSize 0 in
  let in16 := sm_in16 16 in160 (e_inUse e) 0 in
  (forall t v, 0 <= t < nGroups -> 0 <= v < alphaSize -> 1 <= zget (it_len it) (258 * t + v) <= 20) -> 0 <= e_nInUse e ->
  e_bw (fst (sendMTFValues e cost0 fave0 pos0 in160 heap0 weight0 parent0)) =
  wapp (e_bw e) (ws_send (e_inUse e) in16 selMtf (it_len it) code (e_arr1 e) (it_sel it) nGroups nSelectors alphaSize nMTF).
Proof.
  intros e cost0 fave0 pos0 in160 heap0 weight0 parent0. cbv zeta. intros HL HN.
  unfold sendMTFValues. cbv zeta.
  destruct (sm_selmtf _ _ _ _ _) as [pos selMtf]. cbn [snd].
  destruct (sm_put_data _ _ _ _ _ _ _ _ _) as [b selCtr] eqn:PD. cbn [fst e_bw].
  pose proof (f_equal fst PD) as PD1. cbn [fst] in PD1. rewrite sm_put_data_wapp in PD1. subst b.
  unfold ws_send. rewrite !wapp_app. cbn [wapp app].
  rewrite sm_put_in16_wapp, sm_put_inuse_wapp, sm_put_sels_wapp.
  rewrite sm_put_lens_wapp; [reflexivity| | lia].
  intros t' v Ht Hv. apply HL; lia.
Qed.
