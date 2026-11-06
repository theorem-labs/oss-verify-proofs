(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset (both images; plain-free and image-free): THE LIVE-SET COUNTS at a position of the run,
   moved here VERBATIM from the #102 interface lib/A/PresetCfnA.v / lib/AU/PresetCfnB.v (section 3b) by the interface
   owner's decision (19:0xZ): citing them from the interface pulled the PLAIN image into image-A' / B' closures
   (PresetCfnA Requires lib/ZTraceSpec.v, whose closure reaches lib/ZImage.v - red with the old-pin ZImage). This leaf
   Requires only what the statements need: lib/Spec PresetRoomPos / PresetRun / PresetReqAt / PresetReqAtNoMiss /
   PresetRoom / PresetLiveSec / PresetLiveBounds / PresetGate / PjGrammar / PjRoundTrip / PjCharge, lib/Reusable
   YGcfRoom / YGcfRoomLive, lib/A CfRoomLivePreset / CfParamsPreset - NOT ZTraceSpec, YI5c, YH00 / YH01 or ZImage
   (checked on the import closure; the lib/Spec files added for the tail lemmas are already in PresetLiveSec's
   closure). The interface Requires this file and cites it qualified; nothing is re-exported or aliased. The PEAK
   bounds at the end are new model lemmas here: peak_sec_of_room_pos / peak_c24_of_room_pos (the kit owner's ask for
   PRH_FnCheck.tparse_noting_specX's two pkR premises) and peak_sec_at_tail / peak_c24_at_tail / peak_sec_after_rt /
   peak_c24_after_rt (the same bounds for the batch kit's tcheck_reject_clean_starved_specX, at call_tail's position).
   rule 24: proves no function (kind: moved lemmas and model lemmas about the room counts; no program walk). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetReqAt PresetRun PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetLiveSec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAtNoMiss PresetGate PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjCharge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset CfRoomLivePreset.
Import ListNotations.
Local Open Scope Z_scope.
Notation iface_room_pos := PresetRoomPos.iface_room_pos.

(* THE LIVE-SET BOUNDS at a position of the run (h-hpreset-7's ruling 07:56Z for K0's live-set hole): P8's live-set
   premise in iface_room_pos (the instance's live requests = the model's live requests plus at most 3 of the driver's)
   bounds the live SECONDARY requests by LSEC + DRV = 9,524 and the live class-24 requests by L24 + DRV = 146,222
   (PresetLiveSec.live_sec_state / live_c24_state). Those take |x| <= MAXB; above MAXB the model run is empty
   (iface_hruns_big), so the driver's at most 3 blocks are the only live ones. counts_of_room_pos_rl states the same
   in a Theorem Labs lane's state names (YGcfRoomLive.sec_cnt / ccnt24, through CfRoomLivePreset.rs_live_blocks), in the exact form
   (lib/A/PRH_FnAlloc.v), and counts_of_room_pos_ok gives the live-set premises of a Theorem Labs lane's keeps, rl_sec_ok and
   rl_b24_ok (CfRoomLivePreset.preset_rl_sec_ok / preset_ccnt24 / preset_rl_b24_ok). LSEC / L24 / DRV are the leaf
   lib/Spec/PresetLiveBounds.v's names (PresetLiveSec / PresetGate re-export them as notations for the same terms). *)
Lemma iface_hruns_big : forall sm x os, PresetReqAt.MAXB < Z.of_nat (length x) -> PresetRun.hruns sm x os = [].
Proof.
intros sm x os Hx. induction os as [|[[o1 o2] o0] os IH]; [reflexivity|].
rewrite PresetRun.hruns_cons, IH, app_nil_r. unfold PresetRun.call_evs. cbv zeta.
rewrite (proj2 (Z.ltb_lt _ _) Hx). reflexivity.
Qed.
Lemma counts_of_room_pos : forall sm x os i H0 hist S, iface_room_pos sm x os i H0 hist S ->
Z.of_nat (PresetReqAt.cnt PresetLiveSec.sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))) <=
  PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls 24) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))) <=
  PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros sm x os i H0 hist S ((d & Hd & Hp) & _).
destruct (Z_le_gt_dec (Z.of_nat (length x)) PresetReqAt.MAXB) as [Hx|Hx].
- exact (conj (PresetLiveSec.live_sec_state sm x os i _ d Hx Hd Hp) (PresetLiveSec.live_c24_state sm x os i _ d Hx Hd Hp)).
- rewrite (iface_hruns_big sm x os ltac:(lia)), List.firstn_nil in Hp.
  pose proof (PresetLiveSec.cnt_state PresetLiveSec.sec_req _ _ d Hd Hp) as C1.
  pose proof (PresetLiveSec.cnt_state (PresetRoom.in_cls 24) _ _ d Hd Hp) as C2.
  assert (Z0 : forall f, PresetReqAt.cnt f (PresetReqAt.hlive []) = 0%nat) by reflexivity.
  rewrite Z0 in C1, C2. rewrite PresetLiveBounds.LSEC_value, PresetLiveBounds.L24_value. unfold PresetLiveBounds.DRV.
  lia.
Qed.
Lemma counts_of_room_pos_rl : forall sm x os i H0 hist S, iface_room_pos sm x os i H0 hist S ->
YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros sm x os i H0 hist S H. destruct (counts_of_room_pos sm x os i H0 hist S H) as [C1 C2].
exact (conj (proj1 (CfRoomLivePreset.preset_rl_sec_ok S C1)) (CfRoomLivePreset.preset_ccnt24 S C2)).
Qed.
Lemma counts_of_room_pos_ok : forall sm x os i H0 hist S, iface_room_pos sm x os i H0 hist S ->
YGcfRoomLive.rl_sec_ok (cp := CfParamsPreset.CfParams_preset) (PresetLiveBounds.LSEC + PresetLiveBounds.DRV) S /\
YGcfRoomLive.rl_b24_ok (PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1) S.
Proof.
intros sm x os i H0 hist S H. destruct (counts_of_room_pos sm x os i H0 hist S H) as [C1 C2].
exact (conj (CfRoomLivePreset.preset_rl_sec_ok S C1)
  (CfRoomLivePreset.preset_rl_b24_ok S (CfRoomLivePreset.preset_ccnt24 S C2))).
Qed.

(* THE PEAK BOUNDS along the run's next events (the kit owner's ask, a Theorem Labs lane, for the two pkR premises of
   lib/A/PRH_FnCheck.v tparse_noting_specX): the lemmas above bound the live set at ONE position; these bound its PEAK
   (PresetRun.pkR) over the events es that follow position i in the model run. The premise on es is
   PRH_Base.prh_run_at sm x os i es UNFOLDED (its definition, word for word: the kit file is not Required here), so a
   caller passes its prh_run_at hypothesis unchanged. WHY IT HOLDS: iface_room_pos makes S's live set the model's
   live set at i plus at most DRV = 3 driver blocks (pkR_mono, pkR_base); the model's live set after j more events is
   the one at position i + j (pkR_run_window), which live_sec / live_c24 bound at EVERY position for |x| <= MAXB;
   above MAXB the run is empty (iface_hruns_big). No premise beyond the caller's own two: the outcome clause's
   prh_cons_from window and sm = ReaderRes.jr_strtod are not needed, and every sm, x, os, i and es is covered. *)
Lemma firstn_add_rc : forall (A : Type) n m (l : list A), firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
intros A n. induction n as [|n IH]; intros m l; [reflexivity|].
destruct l as [|a l]; [destruct m; reflexivity|]. cbn [Nat.add firstn skipn app]. f_equal. apply IH.
Qed.
Lemma pkR_run_window : forall (f : Z -> bool) (B : Z) (H : list PresetReqAt.hev) i es,
  (forall p, Z.of_nat (PresetReqAt.cnt f (PresetReqAt.hlive (firstn p H))) <= B) ->
  firstn (length es) (skipn i H) = es ->
  Z.of_nat (PresetRun.pkR f (PresetReqAt.hlive (firstn i H)) es) <= B.
Proof.
intros f B H i es HB. revert i. induction es as [|e r IH]; intros i; cbn [PresetRun.pkR]; [intros _; apply HB|].
destruct (skipn i H) as [|e' t] eqn:Es; intro Hr; cbn [length firstn] in Hr; [discriminate Hr|].
injection Hr as -> Ht.
assert (E1 : firstn (S i) H = firstn i H ++ [e]) by (rewrite <- Nat.add_1_r, firstn_add_rc, Es; reflexivity).
assert (E2 : skipn (S i) H = t) by (rewrite <- Nat.add_1_l, <- skipn_skipn, Es; reflexivity).
assert (E3 : PresetReqAt.hstep (PresetReqAt.hlive (firstn i H)) e = PresetReqAt.hlive (firstn (S i) H)).
{ rewrite E1. unfold PresetReqAt.hlive. rewrite PresetReqAt.hlive_from_app. reflexivity. }
rewrite Nat2Z.inj_max. apply Z.max_lub; [apply HB|]. rewrite E3. apply IH. rewrite E2. exact Ht.
Qed.
Lemma peak_of_room_pos : forall (f : Z -> bool) (B : Z) sm x os i H0 hist S es, 0 <= B ->
  (Z.of_nat (length x) <= PresetReqAt.MAXB -> forall p,
     Z.of_nat (PresetReqAt.cnt f (PresetReqAt.hlive (firstn p (PresetRun.hruns sm x os)))) <= B) ->
  iface_room_pos sm x os i H0 hist S ->
  firstn (length es) (skipn i (PresetRun.hruns sm x os)) = es ->
  Z.of_nat (PresetRun.pkR f (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) es) <= B + PresetLiveBounds.DRV.
Proof.
intros f B sm x os i H0 hist S es B0 HB ((d & Hd & Hp) & _) Hr.
assert (HB' : forall p, Z.of_nat (PresetReqAt.cnt f (PresetReqAt.hlive (firstn p (PresetRun.hruns sm x os)))) <= B).
{ intros p. destruct (Z_le_gt_dec (Z.of_nat (length x)) PresetReqAt.MAXB) as [Hx|Hx]; [exact (HB Hx p)|].
  rewrite (iface_hruns_big sm x os ltac:(lia)), firstn_nil.
  change (PresetReqAt.cnt f (PresetReqAt.hlive [])) with 0%nat. lia. }
pose proof (PresetRun.pkR_mono f es _ _ (PresetReqAt.subm_perm _ _ (Permutation_sym Hp))) as M.
pose proof (PresetRun.pkR_base f es (PresetReqAt.hlive (firstn i (PresetRun.hruns sm x os))) d) as Bs.
pose proof (PresetLiveSec.cnt_le_len f d) as Cd.
pose proof (pkR_run_window f B _ i es HB' Hr) as W.
unfold PresetLiveBounds.DRV. lia.
Qed.
(* (S1) the secondaries, in tparse_noting_specX's spelling *)
Lemma peak_sec_of_room_pos : forall sm x os i H0 hist S es, iface_room_pos sm x os i H0 hist S ->
  firstn (length es) (skipn i (PresetRun.hruns sm x os)) = es ->
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) es) <=
    PresetLiveBounds.LSEC + PresetLiveBounds.DRV.
Proof.
intros sm x os i H0 hist S es Hpos Hr.
refine (peak_of_room_pos YGcfRoomLive.rl_sec_req PresetLiveBounds.LSEC sm x os i H0 hist S es _ _ Hpos Hr).
- rewrite PresetLiveBounds.LSEC_value. lia.
- intros Hx p. exact (PresetLiveSec.live_sec sm x os p Hx).
Qed.
(* (S2) the batch class 24, in tparse_noting_specX's spelling *)
Lemma peak_c24_of_room_pos : forall sm x os i H0 hist S es, iface_room_pos sm x os i H0 hist S ->
  firstn (length es) (skipn i (PresetRun.hruns sm x os)) = es ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) es) <=
    PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros sm x os i H0 hist S es Hpos Hr.
refine (peak_of_room_pos (PresetRoom.in_cls YG00.kBatchClass) PresetLiveBounds.L24 sm x os i H0 hist S es _ _ Hpos Hr).
- rewrite PresetLiveBounds.L24_value. lia.
- intros Hx p. exact (PresetLiveSec.live_c24 sm x os p Hx).
Qed.

(* THE ALL-GRANTED READING'S PEAK AT CALL_TAIL'S POSITION (the batch kit's lib/A/PRH_FnCheck.v tcheck_reject_clean_starved_specX,
   c43483a61171 :1121-1124, consumers a Theorem Labs lane's crcs and LLVMFuzzerTestOneInput's lanes L4 / L5c): that text takes
   the two pkR bounds over parse_evs .. tb [] (the ALL-GRANTED reading), but its run holds only the STARVED reading,
   so peak_sec_of_room_pos does not apply. At LLVMFuzzerTestOneInput's two calls of check_reject_clean_starved the
   model's live set is known: the earlier calls and check_no_overread's piece leave nothing (PresetRun.call_ok,
   p1_ok, tfrees_ok), parse_noting's reading leaves its tree pacc .. [] (PresetReqAtNoMiss.parse_ok), expected ()'s
   scratch cancels, and the accepted arm's round trip keeps the tree (round_trip_ok, seg_step). From that live set
   plus the at most DRV = 3 driver blocks the all-granted reading peaks at 2 A + 3 (pkR_le, the reading's requests
   <= A for every grant list: PresetLiveSec.w_reads; the tree's count <= A: PresetRun.cnt_pacc), A = 3,072
   secondaries / 47,664 class-24 requests, below LSEC + DRV = 9,524 / L24 + DRV = 146,222.
   THE PREMISES, each one a fact LLVMFuzzerTestOneInput's walk holds at the call (lib/A/Ent102CutsA.v /
   Ent102PosA.v at a working branch b2d92e71d7be), after `destruct trp as [[o1 o2] o0]`:
   - the split `call_evs sm x o1 o2 o0 = C ++ call_rest sm x`: Ent102PosA.ec_call_evs_ranout_false E trp with
     C := ec_cno_evs E trp (from the cut's ec_ranout E trp = false and e_n E <= EC_NMAX = 0x300000 = MAXB with
     ec_pre's e_n E = Z.of_nat (length (e_pl E)));
   - the ranout flags: the cut's `ec_ranout E trp = false` (the same term after the destruct);
   - the room position: ec_inv's `iface_room_pos (e_sm E) (e_x E) (e_os E ++ [trp]) i_c (e_H0 E) hist S` of cut_caw
     (refused arm, before check_reject_clean_starved (data, size, took, NULL): i_c = e_i0 E + length (ec_cno_evs E trp
     ++ ec_pn E ++ ec_sc E), the _at_tail lemmas) or of cut_crt (accepted arm, before the call with &doc: the same
     ++ ec_rt E t, the _after_rt lemmas), with ec_pre's e_i0 E = length (hruns (e_sm E) (e_x E) (e_os E)); ec_pn E
     and ec_sc E unfold to the parse_evs and the scratch pair written below;
   - the accepted arm only: `fst (PjGrammar.jr_run sm x []) = Some t`, from the cut's ck_read (e_x E) = Some t by
     Ent102PosA.ec_rd_ck_read (ec_pre's e_sm E = ReaderRes.jr_strtod).
   The conclusions are over sm; the caller rewrites ec_pre's e_sm E = ReaderRes.jr_strtod to reach the batch kit's spelling. *)
Lemma hruns_snoc_rc : forall sm x os o1 o2 o0,
  PresetRun.hruns sm x (os ++ [(o1, o2, o0)]) = PresetRun.hruns sm x os ++ PresetRun.call_evs sm x o1 o2 o0.
Proof.
intros sm x os o1 o2 o0. unfold PresetRun.hruns. rewrite map_app, concat_app. cbn [map concat].
rewrite app_nil_r. reflexivity.
Qed.
Lemma hlive_hruns_rc : forall sm x os, PresetReqAt.hlive_from [] (PresetRun.hruns sm x os) = [].
Proof.
intros sm x os. induction os as [|[[o1 o2] o0] os IH]; [reflexivity|].
rewrite PresetRun.hruns_cons, PresetReqAt.hlive_from_app.
pose proof (proj2 (PresetRun.call_ok sm x o1 o2 o0)) as E. unfold PresetReqAt.hlive in E. rewrite E. exact IH.
Qed.
Lemma tail_guard_rc : forall sm x o1 o2 o0 C,
  PresetRun.call_evs sm x o1 o2 o0 = C ++ PresetRun.call_rest sm x -> Z.of_nat (length x) <= PresetReqAt.MAXB.
Proof.
intros sm x o1 o2 o0 C HC. destruct (Z_le_gt_dec (Z.of_nat (length x)) PresetReqAt.MAXB) as [Hx|Hx]; [exact Hx|].
exfalso. unfold PresetRun.call_evs in HC. cbv zeta in HC.
rewrite (proj2 (Z.ltb_lt PresetReqAt.MAXB (Z.of_nat (length x))) ltac:(lia)) in HC.
apply (f_equal (@length PresetReqAt.hev)) in HC. rewrite length_app in HC. cbn [length] in HC.
assert (L : (2 <= length (PresetRun.call_rest sm x))%nat).
{ unfold PresetRun.call_rest. cbv zeta. rewrite !length_app. cbn [length]. lia. }
lia.
Qed.
Lemma cno_live_rc : forall sm x o1 o2 o0 C,
  PresetRun.call_evs sm x o1 o2 o0 = C ++ PresetRun.call_rest sm x ->
  (PresetRun.ranout sm x o1 || PresetRun.ranout sm x o2 || PresetRun.ranout sm x o0)%bool = false ->
  PresetReqAt.hlive_from [] C = [].
Proof.
intros sm x o1 o2 o0 C HC Hr. pose proof (tail_guard_rc sm x o1 o2 o0 C HC) as Hx.
apply Bool.orb_false_iff in Hr as [Hr H0]. apply Bool.orb_false_iff in Hr as [H1 H2].
rewrite PresetRun.call_evs_blocks, (proj2 (Z.ltb_ge _ _) Hx), H1, H2, H0 in HC. cbv iota in HC.
set (CP := Z.of_nat (length x) + PresetReqAt.FUZZ_PAD) in HC.
assert (HX : C = [PresetReqAt.HMal CP; PresetReqAt.HMal CP; PresetReqAt.HMal CP] ++
  (PresetReqAt.parse_evs sm x (PresetRun.okof o1) ++ PresetReqAt.parse_evs sm x (PresetRun.okof o2) ++
   PresetReqAt.parse_evs sm x (PresetRun.okof o0)) ++
  (PresetRun.p1_tfree sm x o1 ++ PresetRun.p1_tfree sm x o2 ++ PresetRun.p1_tfree sm x o0 ++
   [PresetReqAt.HFr CP; PresetReqAt.HFr CP; PresetReqAt.HFr CP])).
{ apply (app_inv_tail (PresetRun.call_rest sm x)). rewrite <- HC, <- !app_assoc. reflexivity. }
assert (HC3 : PresetReqAt.hlive_from [] [PresetReqAt.HMal CP; PresetReqAt.HMal CP; PresetReqAt.HMal CP] = [CP; CP; CP])
  by reflexivity.
destruct (PresetRun.p1_ok sm x o1 o2 o0 [CP; CP; CP]) as [_ Q2].
destruct (PresetRun.tfrees_ok sm x o1 o2 o0 CP) as [_ T2].
rewrite HX, PresetReqAt.hlive_from_app, HC3, PresetReqAt.hlive_from_app, Q2. exact T2.
Qed.
(* the model's live set at call_tail's start (R = []) or after the accepted arm's round trip: the reading's tree *)
Lemma tail_pos_live_rc : forall sm x os o1 o2 o0 C R,
  PresetRun.call_evs sm x o1 o2 o0 = C ++ PresetRun.call_rest sm x ->
  (PresetRun.ranout sm x o1 || PresetRun.ranout sm x o2 || PresetRun.ranout sm x o0)%bool = false ->
  (R = [] \/ exists t, fst (PjGrammar.jr_run sm x []) = Some t /\ R = PresetReqAt.round_trip sm t) ->
  Permutation
    (PresetReqAt.hlive (firstn (length (PresetRun.hruns sm x os) + length (C ++ PresetReqAt.parse_evs sm x [] ++
       [PresetReqAt.HMal (Z.of_nat (length x) + 1)%Z; PresetReqAt.HFr (Z.of_nat (length x) + 1)%Z] ++ R))%nat
       (PresetRun.hruns sm x (os ++ [(o1, o2, o0)]))))
    (PresetReqAtNoMiss.pacc sm x []).
Proof.
intros sm x os o1 o2 o0 C R HC Hr HR.
set (SC := [PresetReqAt.HMal (Z.of_nat (length x) + 1); PresetReqAt.HFr (Z.of_nat (length x) + 1)]).
assert (Ht : exists T, PresetRun.call_tail sm x = R ++ T).
{ destruct HR as [->|(t & Et & ->)]; [exists (PresetRun.call_tail sm x); reflexivity|].
  unfold PresetRun.call_tail. rewrite Et. eexists. reflexivity. }
destruct Ht as [T Ht].
assert (EH : PresetRun.hruns sm x (os ++ [(o1, o2, o0)]) =
  (PresetRun.hruns sm x os ++ C ++ PresetReqAt.parse_evs sm x [] ++ SC ++ R) ++ T).
{ rewrite hruns_snoc_rc, HC.
  change (PresetRun.call_rest sm x) with (PresetReqAt.parse_evs sm x [] ++ SC ++ PresetRun.call_tail sm x).
  rewrite Ht, <- !app_assoc. reflexivity. }
rewrite EH, <- (length_app (PresetRun.hruns sm x os)), firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
unfold PresetReqAt.hlive.
rewrite (PresetReqAt.hlive_from_app [] (PresetRun.hruns sm x os)), hlive_hruns_rc.
rewrite (PresetReqAt.hlive_from_app [] C), (cno_live_rc sm x o1 o2 o0 C HC Hr).
rewrite (PresetReqAt.hlive_from_app [] (PresetReqAt.parse_evs sm x [])).
rewrite (proj2 (PresetReqAtNoMiss.parse_ok sm x [] [])), app_nil_r.
rewrite (PresetReqAt.hlive_from_app (PresetReqAtNoMiss.pacc sm x []) SC).
assert (ESC : forall s, PresetReqAt.hlive_from s SC = s).
{ intros s. unfold SC. cbn [PresetReqAt.hlive_from fold_left PresetReqAt.hstep]. apply PresetReqAt.rm1_cons_eq. }
rewrite ESC.
destruct HR as [->|(t & Et & ->)]; [apply Permutation_refl|].
assert (Hw : PjRoundTrip.pj_wf sm t) by exact (PjRoundTrip.wf_read sm x t Et).
destruct (PresetReqAtNoMiss.round_trip_ok sm t Hw) as [R1 R2].
destruct (PresetReqAtNoMiss.seg_step [] (PresetReqAt.round_trip sm t) (PresetReqAtNoMiss.pacc sm x [])
  (PresetReqAtNoMiss.pacc sm x []) R1 (Permutation_refl _)) as [_ R4].
fold (PresetReqAt.hlive (PresetReqAt.round_trip sm t)) in R4.
apply (Permutation_trans R4). exact (Permutation_app_tail _ R2).
Qed.
(* from a position whose model live set is the tree: the all-granted reading peaks at 2 A + DRV *)
Lemma peak_from_live_rc : forall (f : Z -> bool) (A : Z) sm x os i H0 hist S,
  (forall ok, Z.of_nat (PresetRun.nprodR f (PresetReqAt.rd_hevs (PresetReqAt.rtr sm ok x))) <= A) ->
  Permutation (PresetReqAt.hlive (firstn i (PresetRun.hruns sm x os))) (PresetReqAtNoMiss.pacc sm x []) ->
  iface_room_pos sm x os i H0 hist S ->
  Z.of_nat (PresetRun.pkR f (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetReqAt.parse_evs sm x [])) <=
    2 * A + PresetLiveBounds.DRV.
Proof.
intros f A sm x os i H0 hist S HA Hl ((d & Hd & Hp) & _).
assert (HA' : forall ok, (PresetRun.nprodR f (PresetReqAt.rd_hevs (PresetReqAt.rtr sm ok x)) <= Z.to_nat A)%nat)
  by (intros ok; specialize (HA ok); lia).
pose proof (PresetRun.pkR_le f (PresetReqAt.parse_evs sm x []) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))) as P1.
rewrite PresetRun.nprodR_parse in P1.
pose proof (HA []) as N1.
pose proof (PresetLiveSec.cnt_state f _ _ d Hd Hp) as C1.
rewrite (PresetReqAt.cnt_perm f _ _ Hl) in C1.
pose proof (PresetRun.cnt_pacc sm f x [] (Z.to_nat A) HA') as C2.
unfold PresetLiveBounds.DRV. lia.
Qed.
(* a reading's requests, under any grants: at most 3,072 secondaries and 47,664 class-24 requests
   (PresetLiveSec.w_reads at live_sec's / live_c24's weights) *)
Lemma reads_sec_rc : forall sm x, Z.of_nat (length x) <= PresetReqAt.MAXB -> forall ok,
  Z.of_nat (PresetRun.nprodR YGcfRoomLive.rl_sec_req (PresetReqAt.rd_hevs (PresetReqAt.rtr sm ok x))) <= 3072.
Proof.
intros sm x Hx ok.
assert (HS : forall e, PjCharge.ev_shape e -> PjCharge.is_grow e = false ->
  match PjCharge.req_ev e with
  | Some r => PresetLiveSec.sec_req (Z.of_nat r) = true -> (Z.to_nat 64496 <= PjCharge.chg_ev e)%nat
  | None => True
  end).
{ intros e _ Hg. destruct e as [n|m n|n|n]; cbn [PjCharge.req_ev PjCharge.is_grow] in *; try discriminate;
    try exact I.
  intros Hq. rewrite PresetLiveSec.sec_req_iff in Hq. apply Z.leb_le in Hq. cbn [PjCharge.chg_ev]. lia. }
destruct (PresetLiveSec.w_reads PresetLiveSec.JT_SEC sm x PresetLiveSec.sec_req 1024 (Z.to_nat 64496) 1024 Hx
  ltac:(lia) ltac:(lia) ltac:(lia) (fun e He _ => PresetLiveSec.sec_min e He) HS) as [WA _].
pose proof (WA ok) as W. replace ((PresetReqAt.MAXB + 96) / Z.of_nat 1024) with 3072 in W by reflexivity. exact W.
Qed.
Lemma reads_c24_rc : forall sm x, Z.of_nat (length x) <= PresetReqAt.MAXB -> forall ok,
  Z.of_nat (PresetRun.nprodR (PresetRoom.in_cls YG00.kBatchClass) (PresetReqAt.rd_hevs (PresetReqAt.rtr sm ok x)))
    <= 47664.
Proof.
intros sm x Hx ok.
assert (Hm : (Z.to_nat 5872 <= Nat.max (Z.to_nat (PresetRoom.lo 24) - 17) 1)%nat) by (rewrite PresetLiveSec.lo24; lia).
destruct (PresetLiveSec.w_reads PresetLiveSec.JT_24 sm x (PresetRoom.in_cls 24) 66 (Z.to_nat 5872) 66 Hx
  ltac:(lia) ltac:(lia) ltac:(lia)
  (PresetLiveSec.wchk_minG_ok PresetLiveSec.JT_24 (PresetGate.g_pcl 24) 66 PresetGate.g_hi 9 PresetLiveSec.c24_tab
     (PresetLiveSec.g_pcl_hi 24))
  (PresetGate.g_minS 24 (PresetRoom.lo 24) (Z.to_nat 5872) (PresetRoom.lo_le 24) Hm)) as [WA _].
pose proof (WA ok) as W. replace ((PresetReqAt.MAXB + 96) / Z.of_nat 66) with 47664 in W by reflexivity. exact W.
Qed.
(* (T1) / (T2) at call_tail's start: the refused arm's check_reject_clean_starved (data, size, took, NULL) *)
Lemma peak_sec_at_tail : forall sm x os o1 o2 o0 C H0 hist S,
  PresetRun.call_evs sm x o1 o2 o0 = C ++ PresetRun.call_rest sm x ->
  (PresetRun.ranout sm x o1 || PresetRun.ranout sm x o2 || PresetRun.ranout sm x o0)%bool = false ->
  iface_room_pos sm x (os ++ [(o1, o2, o0)])
    (length (PresetRun.hruns sm x os) + length (C ++ PresetReqAt.parse_evs sm x [] ++
       [PresetReqAt.HMal (Z.of_nat (length x) + 1)%Z; PresetReqAt.HFr (Z.of_nat (length x) + 1)%Z]))%nat H0 hist S ->
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs sm x [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV.
Proof.
intros sm x os o1 o2 o0 C H0 hist S HC Hr Hpos.
pose proof (tail_guard_rc sm x o1 o2 o0 C HC) as Hx.
pose proof (tail_pos_live_rc sm x os o1 o2 o0 C [] HC Hr (or_introl eq_refl)) as Hl.
pose proof (peak_from_live_rc YGcfRoomLive.rl_sec_req 3072 sm x _ _ H0 hist S (reads_sec_rc sm x Hx) Hl Hpos) as P.
rewrite PresetLiveBounds.LSEC_value. lia.
Qed.
Lemma peak_c24_at_tail : forall sm x os o1 o2 o0 C H0 hist S,
  PresetRun.call_evs sm x o1 o2 o0 = C ++ PresetRun.call_rest sm x ->
  (PresetRun.ranout sm x o1 || PresetRun.ranout sm x o2 || PresetRun.ranout sm x o0)%bool = false ->
  iface_room_pos sm x (os ++ [(o1, o2, o0)])
    (length (PresetRun.hruns sm x os) + length (C ++ PresetReqAt.parse_evs sm x [] ++
       [PresetReqAt.HMal (Z.of_nat (length x) + 1)%Z; PresetReqAt.HFr (Z.of_nat (length x) + 1)%Z]))%nat H0 hist S ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs sm x [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros sm x os o1 o2 o0 C H0 hist S HC Hr Hpos.
pose proof (tail_guard_rc sm x o1 o2 o0 C HC) as Hx.
pose proof (tail_pos_live_rc sm x os o1 o2 o0 C [] HC Hr (or_introl eq_refl)) as Hl.
pose proof (peak_from_live_rc (PresetRoom.in_cls YG00.kBatchClass) 47664 sm x _ _ H0 hist S (reads_c24_rc sm x Hx)
  Hl Hpos) as P.
rewrite PresetLiveBounds.L24_value. lia.
Qed.
(* (T1) / (T2) after the accepted arm's round trip: check_reject_clean_starved (data, size, took, &doc) *)
Lemma peak_sec_after_rt : forall sm x os o1 o2 o0 C t H0 hist S,
  PresetRun.call_evs sm x o1 o2 o0 = C ++ PresetRun.call_rest sm x ->
  (PresetRun.ranout sm x o1 || PresetRun.ranout sm x o2 || PresetRun.ranout sm x o0)%bool = false ->
  fst (PjGrammar.jr_run sm x []) = Some t ->
  iface_room_pos sm x (os ++ [(o1, o2, o0)])
    (length (PresetRun.hruns sm x os) + length (C ++ PresetReqAt.parse_evs sm x [] ++
       [PresetReqAt.HMal (Z.of_nat (length x) + 1)%Z; PresetReqAt.HFr (Z.of_nat (length x) + 1)%Z] ++
       PresetReqAt.round_trip sm t))%nat H0 hist S ->
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs sm x [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV.
Proof.
intros sm x os o1 o2 o0 C t H0 hist S HC Hr Et Hpos.
pose proof (tail_guard_rc sm x o1 o2 o0 C HC) as Hx.
pose proof (tail_pos_live_rc sm x os o1 o2 o0 C (PresetReqAt.round_trip sm t) HC Hr
  (or_intror (ex_intro _ t (conj Et eq_refl)))) as Hl.
pose proof (peak_from_live_rc YGcfRoomLive.rl_sec_req 3072 sm x _ _ H0 hist S (reads_sec_rc sm x Hx) Hl Hpos) as P.
rewrite PresetLiveBounds.LSEC_value. lia.
Qed.
Lemma peak_c24_after_rt : forall sm x os o1 o2 o0 C t H0 hist S,
  PresetRun.call_evs sm x o1 o2 o0 = C ++ PresetRun.call_rest sm x ->
  (PresetRun.ranout sm x o1 || PresetRun.ranout sm x o2 || PresetRun.ranout sm x o0)%bool = false ->
  fst (PjGrammar.jr_run sm x []) = Some t ->
  iface_room_pos sm x (os ++ [(o1, o2, o0)])
    (length (PresetRun.hruns sm x os) + length (C ++ PresetReqAt.parse_evs sm x [] ++
       [PresetReqAt.HMal (Z.of_nat (length x) + 1)%Z; PresetReqAt.HFr (Z.of_nat (length x) + 1)%Z] ++
       PresetReqAt.round_trip sm t))%nat H0 hist S ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs sm x [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros sm x os o1 o2 o0 C t H0 hist S HC Hr Et Hpos.
pose proof (tail_guard_rc sm x o1 o2 o0 C HC) as Hx.
pose proof (tail_pos_live_rc sm x os o1 o2 o0 C (PresetReqAt.round_trip sm t) HC Hr
  (or_intror (ex_intro _ t (conj Et eq_refl)))) as Hl.
pose proof (peak_from_live_rc (PresetRoom.in_cls YG00.kBatchClass) 47664 sm x _ _ H0 hist S (reads_c24_rc sm x Hx)
  Hl Hpos) as P.
rewrite PresetLiveBounds.L24_value. lia.
Qed.
