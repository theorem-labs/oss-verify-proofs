(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102 pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994): the B' twin of lib/A/Ent102PaySat.v (made on the
   lane llvm102-sat3, taken by path into the seam line: lib/AU/Prog/Ent102SeamB.v imports it for ec_pay) (blob efe80985b1f8): the same proof over lib/AU/Ent102CutsB.v's ecx /
   ec_ccut_ok / ec_lcut_ok / ec_pay (blob a74a7497b9d0; their text is Ent102CutsA's, port/a2b.py). Made as the lane
   llvm102-sat2 made it (port/a2b.py, which maps nothing in this generic file) with ONE edit: the cut module
   Ent102CutsA -> Ent102CutsB (a2b does not map module names). Every line below the header is Ent102PaySat.v's.
   The budget hypotheses of every segment statement (ec_ccut_ok, ec_lcut_ok, ec_pay of
   lib/AU/Ent102CutsB.v) are SATISFIABLE: ec_pay_sat exhibits the two budgets and proves the three records AS STATED there.
   rule 24: proves no function (kind: segment lemma - a pure fact about the two budget functions).

   THE CHOICE: each budget is the REMAINING WORST CASE from cut i to the exit, as a function of the entry context E
   and of i, and 0 for an input longer than EC_NMAX (where no field asks anything). A term is "gated" at the index of
   the cut whose field asks it (sat_gate i k v = max 0 v for i <= k, else 0), so both budgets are antitone by
   construction.
   - count (sat_ccut): the sum of the five allocating lanes' bounds still ahead: L1 3 * ck_ncalls x (cut 1), L2
     2 |x| + 2 (cut 2; every reading makes at most that many calls, PjGrammar.G7_4, at ANY failure oracle), L4
     ck_crcs_max x (ck_ncalls x) 0 JNull (cut 4), L5b ck_crt_count t 3 (cut 7; cset <= 3 and the count grows with
     cset), L5c ck_crcs_max x (ck_ncalls x) 1 t (cut 8); the tree terms at t = the reading `ck_read x` (0 when it
     fails). Each is at most linear in |x| (section 2), so the sum is at most 15 |x| + 244 <= 47,186,164 < LCNT.
   - live (sat_lcut): the max over the calls still ahead of the callee's LIVE_<f> (check_no_overread at cut 1,
     parse_noting at 2, check_as_written at 3, the starved check at JNull at 4, check_round_trip at 7, the starved
     check at t at 8) and, up to cut 2, the bytes the reading still adds (sat_l_held: hpeak bound 224 |x| + 16384
     plus a head per live block, cf_head * (2 |x| + 2)) on top of the max after it. Its largest value is
     805,322,784 + 9,017,853,504 = 9,823,176,288 <= LIVE_LIB = 12,884,901,888.

   PROVED HERE OR CITED (no sat_* input premise is left):
   - the LIVE bounds: a Theorem Labs lane's lib/Spec/PjLiveBound.v (blob 91ccec38b4d0, a working branch
     cc743fba411, taken BY PATH with lib/Prog/PackTreeTight.v 1add21fa18a6): live_pj_parse_maxb,
     live_check_no_overread_maxb, live_check_reject_clean_starved_maxb, live_check_round_trip_maxb, hpeak_rd; the kit's
     LIVE_* are its live_* at cf_head / prh_jr_strtod by conversion (sat_live_*_eq); LIVE_check_reject_clean_starved
     at JNull is bounded here (the writer's first buffer, PjReqBoundW.newcap0_le);
   - the counts: PjGrammar.G7_4 (calls of any reading), PackTraceR.wcalls_read30 / wcalls_le / wlen_read / crt_wlen /
     tcalls_rtw / rtw_crt and PackReparse.rtw_read (the writer's and the read-back's calls), ck_pick's range.
   THE ONE SECTION PREMISE, a PARAMETER fact (not an input bound): sat_head : cf_head <= 16. It is NECESSARY, not a
   convenience: ecov_pno asks PRH_FnPj.LIVE_pj_parse (e_x E) <= ec_lcut E 2 <= LIVE_LIB, and LIVE_pj_parse x >=
   cf_head for every x, so at a CfParams with cf_head > LIVE_LIB the records are refutable; CfParams bounds cf_head
   only below (cf_head_nonneg). ec_pay_sat_preset discharges it at CfParams_preset (cf_head = 16) and is CLOSED.

   THE OLD ecov_caw (blobs 7af9d0fe1491 / e9a447dec8c0, before 3b0db38483cf) is kept as a record:
   sat_ecov_caw_old_refuted proves that its form - LIVE_check_as_written (e_n E) <= ec_lcut E 3 under the length guard
   alone - refutes ec_lcut_ok at ANY budget for every inhabited ecx (e_n := LIVE_LIB, e_pl := []), which is why the
   field now also asks e_n E <= EC_NMAX. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YM05 YGcfNames YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip PjLiveBound PjReqBoundW PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterSpec WriterValue PjWriteHyp
  PackReparse PackTraceR check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader PRH_FnPj PRH_FnWriter CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import Ent102CutsB.
Import ListNotations.
Local Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".

(* ---------------------------------------------------------------------- *)
(* 1. The reader model: the run's peak and live blocks, the model's call count. *)

Lemma sat_hpeak_eq : forall tr, ReaderRes.hpeak tr = PjLiveBound.hpeak_r tr.
Proof.
  induction tr as [|e r IH]; [reflexivity|]. cbn [ReaderRes.hpeak PjLiveBound.hpeak_r]. rewrite IH. reflexivity.
Qed.

Lemma sat_nlive_calls : forall tr, ReaderRes.nlive tr <= Z.of_nat (PjGrammar.calls tr).
Proof.
  induction tr as [|e r IH]; [cbn; lia|].
  destruct e as [n|[|m] n|n|n]; cbn [ReaderRes.nlive ReaderRes.nlive_ev PjGrammar.calls PjGrammar.is_call]; lia.
Qed.

(* any reading of x, at any failure oracle *)
Lemma sat_hpeak_run : forall x ok res tr, PjGrammar.jr_run ReaderRes.jr_strtod x ok = (res, tr) ->
  ReaderRes.hpeak tr <= 224 * Z.of_nat (length x) + 16384.
Proof.
  intros x ok res tr H. rewrite sat_hpeak_eq.
  pose proof (PjLiveBound.hpeak_rd ReaderRes.jr_strtod x ok) as P. rewrite H in P. exact P.
Qed.

Lemma sat_calls_run : forall x ok res tr, PjGrammar.jr_run ReaderRes.jr_strtod x ok = (res, tr) ->
  Z.of_nat (PjGrammar.calls tr) <= 2 * Z.of_nat (length x) + 2.
Proof.
  intros x ok res tr H. pose proof (PjGrammar.G7_4 ReaderRes.jr_strtod x ok) as C. rewrite H in C.
  cbn [snd] in C. lia.
Qed.

Lemma sat_ncalls_le : forall x : list Z, 0 <= ck_ncalls x <= 2 * Z.of_nat (length x) + 2.
Proof.
  intros x. unfold ck_ncalls, PjGrammar.ncalls. pose proof (PjGrammar.G7_4 ReaderRes.jr_strtod x []). lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The count terms, each linear in |x| for |x| <= EC_NMAX. *)

Lemma sat_took_le : forall x n, 0 <= n -> 0 <= (if n =? 0 then 0 else ck_pick x n + 1) <= n.
Proof.
  intros x n Hn. unfold ck_pick. destruct (Z.eqb_spec n 0) as [E|E]; cbv beta iota; [lia|].
  pose proof (Z.mod_pos_bound (ck_djb2 5381 x) n ltac:(lia)). lia.
Qed.

Lemma sat_crcs0_le : forall x : list Z, 0 <= ck_crcs_max x (ck_ncalls x) 0 PjTree.JNull <= 2 * Z.of_nat (length x) + 2.
Proof.
  intros x. unfold ck_crcs_max. rewrite Z.eqb_refl. cbv beta iota.
  pose proof (sat_ncalls_le x) as N. pose proof (sat_took_le x (ck_ncalls x) ltac:(lia)). lia.
Qed.

Lemma sat_crt_eq : forall t, ck_crt_tree t = check_round_trip_c.crt_tree t.
Proof. intros t. destruct t; reflexivity. Qed.

Lemma sat_crt_count_mono : forall t cset, cset <= 3 -> ck_crt_count t cset <= ck_crt_count t 3.
Proof. intros t cset H. unfold ck_crt_count. destruct t; lia. Qed.

Lemma sat_crt_count_le : forall x t, ck_read x = Some t -> Z.of_nat (length x) <= EC_NMAX ->
  0 <= ck_crt_count t 3 <= 3 * Z.of_nat (length x) + 112.
Proof.
  intros x t H HX.
  assert (HN : Z.of_nat (length x) <= 3 * 2 ^ 20) by (change (3 * 2 ^ 20) with 3145728; unfold EC_NMAX in HX; lia).
  pose proof (PackTraceR.wcalls_read30 x t false H HN) as Wf.
  pose proof (PackTraceR.wcalls_read30 x t true H HN) as Wt.
  pose proof (PackTraceR.tcalls_rtw t) as T1.
  pose proof (PackReparse.rtw_read ReaderRes.jr_strtod x t H) as T2.
  pose proof (PackTraceR.tcalls_rtw (check_round_trip_c.crt_tree t)) as T3.
  pose proof (PackTraceR.rtw_crt t) as T4.
  pose proof (PackTraceR.crt_wlen t true) as L1.
  pose proof (PackTraceR.wlen_read x t true H) as L2.
  assert (L3 : PjWriteHyp.wlen (check_round_trip_c.crt_tree t) true <= 268435456)
    by (unfold EC_NMAX in HX; lia).
  pose proof (PackTraceR.wcalls_le (check_round_trip_c.crt_tree t) true L3) as Wc.
  unfold ck_crt_count. rewrite sat_crt_eq.
  destruct t; cbv beta iota; lia.
Qed.

Lemma sat_crcs1_le : forall x t, ck_read x = Some t -> Z.of_nat (length x) <= EC_NMAX ->
  0 <= ck_crcs_max x (ck_ncalls x) 1 t <= 2 * Z.of_nat (length x) + 122.
Proof.
  intros x t H HX.
  assert (HN : Z.of_nat (length x) <= 3 * 2 ^ 20) by (change (3 * 2 ^ 20) with 3145728; unfold EC_NMAX in HX; lia).
  pose proof (PackTraceR.wcalls_read30 x t false H HN) as Wf.
  pose proof (PackTraceR.wcalls_read30 x t true H HN) as Wt.
  pose proof (sat_ncalls_le x) as N. pose proof (sat_took_le x (ck_ncalls x) ltac:(lia)) as P.
  unfold ck_crcs_max. assert (E1 : (1 =? 0) = false) by reflexivity. rewrite E1. cbv beta iota. lia.
Qed.

(* the writer's text of JNull fits its first buffer *)
Lemma sat_wdoc_null : forall p, (length (WriterValue.wdoc PjTree.JNull p) <= 5)%nat.
Proof. intros p. destruct p; vm_compute; lia. Qed.

Lemma sat_newcap_null : forall p,
  WriterSpec.newcap 0 (Z.of_nat (length (WriterValue.wdoc PjTree.JNull p)) + 1) <= 4096.
Proof.
  intros p. pose proof (sat_wdoc_null p) as W.
  pose proof (PjReqBoundW.newcap0_le (Z.of_nat (length (WriterValue.wdoc PjTree.JNull p)) + 1)). lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The gate: a term asked at cut k, still ahead at cut i. *)

Definition sat_gate (i k : nat) (v : Z) : Z := if Nat.leb i k then Z.max 0 v else 0.

Lemma sat_gate_nn : forall i k v, 0 <= sat_gate i k v.
Proof. intros. unfold sat_gate. destruct (Nat.leb i k); lia. Qed.

Lemma sat_gate_anti : forall i j k v, (i <= j)%nat -> sat_gate j k v <= sat_gate i k v.
Proof.
  intros i j k v H. unfold sat_gate.
  destruct (Nat.leb_spec j k), (Nat.leb_spec i k); lia.
Qed.

Lemma sat_gate_ge : forall i k v, (i <= k)%nat -> v <= sat_gate i k v.
Proof. intros i k v H. unfold sat_gate. destruct (Nat.leb_spec i k); lia. Qed.

Lemma sat_gate_le : forall i k v b, 0 <= b -> v <= b -> sat_gate i k v <= b.
Proof. intros. unfold sat_gate. destruct (Nat.leb i k); lia. Qed.

Lemma sat_max_l : forall a b c, a <= b -> a <= Z.max b c.
Proof. intros. lia. Qed.

Lemma sat_max_r : forall a b c, a <= c -> a <= Z.max b c.
Proof. intros. lia. Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The budgets. *)

Section S.
Context {rc : YM05.RunCeil} {cp : YGcfNames.CfParams} {L : YP0b.ptable YPsym.asym} {PA : @YC4aP.PAImg rc L}.
Local Notation ECX := (@ecx rc L PA).

(* THE ONE SECTION PREMISE (header): a fact of the CfParams instance, 16 at CfParams_preset *)
Hypothesis sat_head : YGcfNames.cf_head <= 16.

Lemma sat_hd : 0 <= YGcfNames.cf_head <= 16.
Proof. pose proof (@YGcfNames.cf_head_nonneg cp). pose proof sat_head. lia. Qed.

(* The kit's LIVE_* are a Theorem Labs lane's live_* at cf_head and the strtod oracle (prh_jr_strtod = ReaderRes.jr_strtod) *)
Lemma sat_live_pj_parse_eq : forall x,
  PRH_FnPj.LIVE_pj_parse x = PjLiveBound.live_pj_parse YGcfNames.cf_head ReaderRes.jr_strtod x.
Proof. reflexivity. Qed.
Lemma sat_live_cno_eq : forall x,
  LIVE_check_no_overread x = PjLiveBound.live_check_no_overread YGcfNames.cf_head ReaderRes.jr_strtod x.
Proof. reflexivity. Qed.
Lemma sat_live_crs_eq : forall (x : list Z) (t : jv),
  LIVE_check_reject_clean_starved x t =
  PjLiveBound.live_check_reject_clean_starved YGcfNames.cf_head ReaderRes.jr_strtod x t.
Proof. reflexivity. Qed.
Lemma sat_live_crt_eq : forall t,
  LIVE_check_round_trip t = PjLiveBound.live_check_round_trip YGcfNames.cf_head ReaderRes.jr_strtod t.
Proof. reflexivity. Qed.

Lemma sat_maxb : forall x : list Z, Z.of_nat (length x) <= EC_NMAX -> Z.of_nat (length x) <= PresetReqAt.MAXB.
Proof. intros x H. unfold PresetReqAt.MAXB, EC_NMAX in *. lia. Qed.

Lemma sat_live_pj_parse : forall x : list Z, Z.of_nat (length x) <= EC_NMAX -> PRH_FnPj.LIVE_pj_parse x <= 1509982256.
Proof.
  intros x HX. rewrite sat_live_pj_parse_eq. exact (PjLiveBound.live_pj_parse_maxb _ _ x sat_hd (sat_maxb x HX)).
Qed.

Lemma sat_live_cno : forall x : list Z, Z.of_nat (length x) <= EC_NMAX -> LIVE_check_no_overread x <= 4539384000.
Proof.
  intros x HX. rewrite sat_live_cno_eq.
  exact (PjLiveBound.live_check_no_overread_maxb _ _ x sat_hd (sat_maxb x HX)).
Qed.

Lemma sat_live_crs : forall (x : list Z) (t : jv), Z.of_nat (length x) <= EC_NMAX -> ck_read x = Some t ->
  LIVE_check_reject_clean_starved x t <= 2252373912.
Proof.
  intros x t HX H. rewrite sat_live_crs_eq.
  exact (PjLiveBound.live_check_reject_clean_starved_maxb _ ReaderRes.jr_strtod x t sat_hd H (sat_maxb x HX)).
Qed.

Lemma sat_live_crt : forall (x : list Z) (t : jv), Z.of_nat (length x) <= EC_NMAX -> ck_read x = Some t ->
  LIVE_check_round_trip t <= 9017853504.
Proof.
  intros x t HX H. rewrite sat_live_crt_eq.
  exact (PjLiveBound.live_check_round_trip_maxb _ ReaderRes.jr_strtod x t sat_hd H (sat_maxb x HX)).
Qed.

(* the starved check at the refused arm's tree JNull: the reading plus two writer first buffers *)
Lemma sat_live_crs_null : forall x : list Z, Z.of_nat (length x) <= EC_NMAX ->
  LIVE_check_reject_clean_starved x PjTree.JNull <= 1509998704.
Proof.
  intros x HX. unfold LIVE_check_reject_clean_starved, PRH_FnWriter.LIVE_pj_write.
  pose proof (sat_live_pj_parse x HX). pose proof (sat_newcap_null true). pose proof (sat_newcap_null false).
  pose proof sat_hd. lia.
Qed.

Definition sat_X (E : ECX) : Z := Z.of_nat (length (e_x E)).
Definition sat_in (E : ECX) : bool := sat_X E <=? EC_NMAX.
(* a term of the reading's tree, 0 when the reading fails *)
Definition sat_tree (E : ECX) (f : jv -> Z) : Z := match ck_read (e_x E) with Some t => f t | None => 0 end.

Lemma sat_tree_some : forall E f t, ck_read (e_x E) = Some t -> sat_tree E f = f t.
Proof. intros E f t H. unfold sat_tree. rewrite H. reflexivity. Qed.

(* the count lanes' bounds, at the cut where each lane starts *)
Definition sat_c_cno (E : ECX) : Z := 3 * ck_ncalls (e_x E).
Definition sat_c_pno (E : ECX) : Z := 2 * sat_X E + 2.
Definition sat_c_crs0 (E : ECX) : Z := ck_crcs_max (e_x E) (ck_ncalls (e_x E)) 0 PjTree.JNull.
Definition sat_c_crt (E : ECX) : Z := sat_tree E (fun t => ck_crt_count t 3).
Definition sat_c_crs1 (E : ECX) : Z := sat_tree E (ck_crcs_max (e_x E) (ck_ncalls (e_x E)) 1).

Definition sat_ccut (E : ECX) (i : nat) : Z :=
  if sat_in E then
    sat_gate i 1 (sat_c_cno E) + sat_gate i 2 (sat_c_pno E) + sat_gate i 4 (sat_c_crs0 E) +
    sat_gate i 7 (sat_c_crt E) + sat_gate i 8 (sat_c_crs1 E)
  else 0.

(* the callees' live needs, at the cut whose cover asks each, and what the reading adds *)
Definition sat_l_cno (E : ECX) : Z := LIVE_check_no_overread (e_x E).
Definition sat_l_pno (E : ECX) : Z := PRH_FnPj.LIVE_pj_parse (e_x E).
Definition sat_l_held (E : ECX) : Z := 224 * sat_X E + 16384 + YGcfNames.cf_head * (2 * sat_X E + 2).
Definition sat_l_caw (E : ECX) : Z := if e_n E <=? EC_NMAX then LIVE_check_as_written (e_n E) else 0.
Definition sat_l_crs0 (E : ECX) : Z := LIVE_check_reject_clean_starved (e_x E) PjTree.JNull.
Definition sat_l_crs (E : ECX) : Z := sat_tree E (LIVE_check_reject_clean_starved (e_x E)).
Definition sat_l_crt (E : ECX) : Z := sat_tree E LIVE_check_round_trip.
(* the most the calls after the reading hold at once (cuts 3 .. 8) *)
Definition sat_l_tail (E : ECX) : Z :=
  Z.max 0 (Z.max (sat_l_caw E) (Z.max (sat_l_crs0 E) (Z.max (sat_l_crs E) (sat_l_crt E)))).

Definition sat_lraw (E : ECX) (i : nat) : Z :=
  Z.max (sat_gate i 1 (sat_l_cno E))
 (Z.max (sat_gate i 2 (sat_l_pno E))
 (Z.max (sat_gate i 2 (sat_l_held E + sat_l_tail E))
 (Z.max (sat_gate i 3 (sat_l_caw E))
 (Z.max (sat_gate i 4 (sat_l_crs0 E))
 (Z.max (sat_gate i 8 (sat_l_crs E))
        (sat_gate i 7 (sat_l_crt E))))))).

Definition sat_lcut (E : ECX) (i : nat) : Z := if sat_in E then sat_lraw E i else 0.

(* ---- the weights' bounds ---- *)

Lemma sat_in_true : forall E, Z.of_nat (length (e_x E)) <= EC_NMAX -> sat_in E = true.
Proof. intros E H. unfold sat_in, sat_X. apply Z.leb_le. exact H. Qed.

Lemma sat_lcut_in : forall E i, Z.of_nat (length (e_x E)) <= EC_NMAX -> sat_lcut E i = sat_lraw E i.
Proof. intros E i H. unfold sat_lcut. rewrite (sat_in_true E H). reflexivity. Qed.

Lemma sat_lcut_out : forall E i, EC_NMAX < sat_X E -> sat_lcut E i = 0.
Proof. intros E i H. unfold sat_lcut, sat_in. rewrite (proj2 (Z.leb_gt _ _) H). reflexivity. Qed.

Lemma sat_ccut_in : forall E i, Z.of_nat (length (e_x E)) <= EC_NMAX ->
  sat_ccut E i = sat_gate i 1 (sat_c_cno E) + sat_gate i 2 (sat_c_pno E) + sat_gate i 4 (sat_c_crs0 E) +
                 sat_gate i 7 (sat_c_crt E) + sat_gate i 8 (sat_c_crs1 E).
Proof. intros E i H. unfold sat_ccut. rewrite (sat_in_true E H). reflexivity. Qed.

Lemma sat_ccut_out : forall E i, EC_NMAX < sat_X E -> sat_ccut E i = 0.
Proof. intros E i H. unfold sat_ccut, sat_in. rewrite (proj2 (Z.leb_gt _ _) H). reflexivity. Qed.

Lemma sat_c_bounds : forall E, sat_X E <= EC_NMAX ->
  0 <= sat_c_cno E <= 6 * sat_X E + 6 /\ 0 <= sat_c_pno E <= 2 * sat_X E + 2 /\
  0 <= sat_c_crs0 E <= 2 * sat_X E + 2 /\ 0 <= sat_c_crt E <= 3 * sat_X E + 112 /\
  0 <= sat_c_crs1 E <= 2 * sat_X E + 122.
Proof.
  intros E HX. unfold sat_X in *.
  pose proof (sat_ncalls_le (e_x E)). pose proof (sat_crcs0_le (e_x E)).
  assert (Ct : 0 <= sat_c_crt E <= 3 * Z.of_nat (length (e_x E)) + 112).
  { unfold sat_c_crt, sat_tree. destruct (ck_read (e_x E)) as [t|] eqn:Ht; [|lia].
    exact (sat_crt_count_le (e_x E) t Ht HX). }
  assert (C1 : 0 <= sat_c_crs1 E <= 2 * Z.of_nat (length (e_x E)) + 122).
  { unfold sat_c_crs1, sat_tree. destruct (ck_read (e_x E)) as [t|] eqn:Ht; [|lia].
    exact (sat_crcs1_le (e_x E) t Ht HX). }
  unfold sat_c_cno, sat_c_pno, sat_c_crs0, sat_X. lia.
Qed.

Lemma sat_l_held_le : forall E, sat_X E <= EC_NMAX -> 0 <= sat_l_held E <= 1000000000.
Proof.
  intros E HX. unfold sat_l_held. pose proof sat_hd as Hd.
  assert (0 <= sat_X E) by (unfold sat_X; lia).
  assert (YGcfNames.cf_head * (2 * sat_X E + 2) <= 16 * (2 * sat_X E + 2))
    by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (0 <= YGcfNames.cf_head * (2 * sat_X E + 2)) by (apply Z.mul_nonneg_nonneg; lia).
  unfold EC_NMAX in HX. lia.
Qed.

Lemma sat_l_tail_le : forall E, sat_X E <= EC_NMAX -> 0 <= sat_l_tail E <= 9017853504.
Proof.
  intros E HX. unfold sat_X in HX.
  assert (Ca : sat_l_caw E <= 3145729).
  { unfold sat_l_caw, LIVE_check_as_written.
    destruct (Z.leb_spec (e_n E) EC_NMAX); cbv beta iota; unfold EC_NMAX in *; lia. }
  pose proof (sat_live_crs_null (e_x E) HX) as C0.
  assert (Cs : sat_l_crs E <= 2252373912).
  { unfold sat_l_crs, sat_tree. destruct (ck_read (e_x E)) as [t|] eqn:Ht; [|lia].
    exact (sat_live_crs (e_x E) t HX Ht). }
  assert (Ct : sat_l_crt E <= 9017853504).
  { unfold sat_l_crt, sat_tree. destruct (ck_read (e_x E)) as [t|] eqn:Ht; [|lia].
    exact (sat_live_crt (e_x E) t HX Ht). }
  unfold sat_l_tail, sat_l_crs0 in *. lia.
Qed.

(* ---- the live budget: nonnegative, antitone, within LIVE_LIB ---- *)

Lemma sat_lraw_nn : forall E i, 0 <= sat_lraw E i.
Proof. intros E i. unfold sat_lraw. apply sat_max_l. apply sat_gate_nn. Qed.

Lemma sat_lraw_anti : forall E i j, (i <= j)%nat -> sat_lraw E j <= sat_lraw E i.
Proof.
  intros E i j H. unfold sat_lraw.
  repeat apply Z.max_le_compat; apply sat_gate_anti; exact H.
Qed.

Lemma sat_lraw_le : forall E i, sat_X E <= EC_NMAX -> sat_lraw E i <= LIVE_LIB.
Proof.
  intros E i HX. change LIVE_LIB with 12884901888.
  pose proof (sat_l_held_le E HX) as Hh. pose proof (sat_l_tail_le E HX) as Ht.
  assert (Hc : sat_l_cno E <= 4539384000) by exact (sat_live_cno (e_x E) HX).
  assert (Hp : sat_l_pno E <= 1509982256) by exact (sat_live_pj_parse (e_x E) HX).
  assert (Ha : sat_l_caw E <= sat_l_tail E) by (unfold sat_l_tail; lia).
  assert (H0 : sat_l_crs0 E <= sat_l_tail E) by (unfold sat_l_tail; lia).
  assert (Hs : sat_l_crs E <= sat_l_tail E) by (unfold sat_l_tail; lia).
  assert (Hr : sat_l_crt E <= sat_l_tail E) by (unfold sat_l_tail; lia).
  unfold sat_lraw. repeat apply Z.max_lub; apply sat_gate_le; lia.
Qed.

Lemma sat_lcut_ok : @ec_lcut_ok rc L PA sat_lcut.
Proof.
  unfold ec_lcut_ok. intros E i j.
  destruct (Z.leb_spec (sat_X E) EC_NMAX) as [HX|HX].
  - rewrite (sat_lcut_in E i HX), (sat_lcut_in E j HX).
    split; [split|].
    + apply sat_lraw_nn.
    + apply sat_lraw_le. exact HX.
    + apply sat_lraw_anti.
  - rewrite (sat_lcut_out E i HX), (sat_lcut_out E j HX). change LIVE_LIB with 12884901888. lia.
Qed.

(* ---- the count budget: nonnegative, antitone, within LCNT ---- *)

Lemma sat_ccut_ok : @ec_ccut_ok rc L PA sat_ccut.
Proof.
  unfold ec_ccut_ok. intros E i j.
  destruct (Z.leb_spec (sat_X E) EC_NMAX) as [HX|HX].
  - rewrite (sat_ccut_in E i HX), (sat_ccut_in E j HX).
    destruct (sat_c_bounds E HX) as (B1 & B2 & B3 & B4 & B5).
    assert (X0 : 0 <= sat_X E) by (unfold sat_X; lia).
    split; [split|].
    + pose proof (sat_gate_nn i 1 (sat_c_cno E)). pose proof (sat_gate_nn i 2 (sat_c_pno E)).
      pose proof (sat_gate_nn i 4 (sat_c_crs0 E)). pose proof (sat_gate_nn i 7 (sat_c_crt E)).
      pose proof (sat_gate_nn i 8 (sat_c_crs1 E)). lia.
    + pose proof (sat_gate_le i 1 (sat_c_cno E) (6 * sat_X E + 6) ltac:(lia) ltac:(lia)).
      pose proof (sat_gate_le i 2 (sat_c_pno E) (2 * sat_X E + 2) ltac:(lia) ltac:(lia)).
      pose proof (sat_gate_le i 4 (sat_c_crs0 E) (2 * sat_X E + 2) ltac:(lia) ltac:(lia)).
      pose proof (sat_gate_le i 7 (sat_c_crt E) (3 * sat_X E + 112) ltac:(lia) ltac:(lia)).
      pose proof (sat_gate_le i 8 (sat_c_crs1 E) (2 * sat_X E + 122) ltac:(lia) ltac:(lia)).
      change LCNT with 4294967296. unfold EC_NMAX in HX. lia.
    + intros Hij.
      pose proof (sat_gate_anti i j 1 (sat_c_cno E) Hij). pose proof (sat_gate_anti i j 2 (sat_c_pno E) Hij).
      pose proof (sat_gate_anti i j 4 (sat_c_crs0 E) Hij). pose proof (sat_gate_anti i j 7 (sat_c_crt E) Hij).
      pose proof (sat_gate_anti i j 8 (sat_c_crs1 E) Hij). lia.
  - rewrite (sat_ccut_out E i HX), (sat_ccut_out E j HX). change LCNT with 4294967296. lia.
Qed.

(* ---- the pay and cover fields ---- *)

(* the live budget at cut 3 is the tail, and at cut 2 it holds the reading's bytes on top of it *)
Lemma sat_lraw3 : forall E, sat_lraw E 3 <= sat_l_tail E.
Proof.
  intros E. unfold sat_lraw, sat_gate. cbn [Nat.leb]. unfold sat_l_tail.
  repeat apply Z.max_lub; lia.
Qed.

Lemma sat_lraw2 : forall E, sat_l_held E + sat_l_tail E <= sat_lraw E 2.
Proof.
  intros E. unfold sat_lraw. apply sat_max_r, sat_max_r, sat_max_l, sat_gate_ge. lia.
Qed.

(* the bytes one reading adds, at any failure oracle *)
Lemma sat_held_run : forall E ok res tr, PjGrammar.jr_run ReaderRes.jr_strtod (e_x E) ok = (res, tr) ->
  ReaderRes.hpeak tr + YGcfNames.cf_head * ReaderRes.nlive tr <= sat_l_held E.
Proof.
  intros E ok res tr H. unfold sat_l_held, sat_X.
  pose proof (sat_hpeak_run (e_x E) ok res tr H) as P. pose proof (sat_calls_run (e_x E) ok res tr H) as C.
  pose proof (sat_nlive_calls tr) as N. pose proof sat_hd as Hd.
  assert (YGcfNames.cf_head * ReaderRes.nlive tr <=
          YGcfNames.cf_head * (2 * Z.of_nat (length (e_x E)) + 2)) by (apply Z.mul_le_mono_nonneg_l; lia).
  lia.
Qed.

Lemma sat_epay_cno : forall E : ECX, Z.of_nat (length (e_x E)) <= EC_NMAX ->
  3 * ck_ncalls (e_x E) + sat_ccut E 2 <= sat_ccut E 1 /\ sat_lcut E 2 <= sat_lcut E 1.
Proof.
  intros E HX. split.
  - rewrite (sat_ccut_in E 2 HX), (sat_ccut_in E 1 HX). unfold sat_gate. cbn [Nat.leb]. unfold sat_c_cno. lia.
  - rewrite (sat_lcut_in E 2 HX), (sat_lcut_in E 1 HX). apply sat_lraw_anti. lia.
Qed.

Lemma sat_epay_pno : forall (E : ECX) ok res tr, Z.of_nat (length (e_x E)) <= EC_NMAX ->
  PjGrammar.jr_run ReaderRes.jr_strtod (e_x E) ok = (res, tr) ->
  Z.of_nat (PjGrammar.calls tr) + sat_ccut E 3 <= sat_ccut E 2 /\
  ReaderRes.hpeak tr + YGcfNames.cf_head * ReaderRes.nlive tr + sat_lcut E 3 <= sat_lcut E 2.
Proof.
  intros E ok res tr HX H. split.
  - pose proof (sat_calls_run (e_x E) ok res tr H) as C.
    rewrite (sat_ccut_in E 3 HX), (sat_ccut_in E 2 HX). unfold sat_gate. cbn [Nat.leb]. unfold sat_c_pno, sat_X. lia.
  - rewrite (sat_lcut_in E 3 HX), (sat_lcut_in E 2 HX).
    pose proof (sat_held_run E ok res tr H). pose proof (sat_lraw3 E). pose proof (sat_lraw2 E). lia.
Qed.

Lemma sat_epay_crs0 : forall E : ECX, Z.of_nat (length (e_x E)) <= EC_NMAX ->
  ck_crcs_max (e_x E) (ck_ncalls (e_x E)) 0 PjTree.JNull + sat_ccut E 5 <= sat_ccut E 4 /\
  sat_lcut E 5 <= sat_lcut E 4.
Proof.
  intros E HX. split.
  - rewrite (sat_ccut_in E 5 HX), (sat_ccut_in E 4 HX). unfold sat_gate. cbn [Nat.leb]. unfold sat_c_crs0. lia.
  - rewrite (sat_lcut_in E 5 HX), (sat_lcut_in E 4 HX). apply sat_lraw_anti. lia.
Qed.

Lemma sat_epay_crt : forall (E : ECX) (t : jv) (cset : Z), Z.of_nat (length (e_x E)) <= EC_NMAX ->
  ck_read (e_x E) = Some t -> 0 <= cset <= 3 ->
  ck_crt_count t cset + sat_ccut E 8 <= sat_ccut E 7 /\ sat_lcut E 8 <= sat_lcut E 7.
Proof.
  intros E t cset HX Ht Hc. split.
  - pose proof (sat_crt_count_mono t cset ltac:(lia)) as M.
    rewrite (sat_ccut_in E 8 HX), (sat_ccut_in E 7 HX). unfold sat_gate. cbn [Nat.leb].
    unfold sat_c_crt. rewrite (sat_tree_some E _ t Ht). cbv beta. lia.
  - rewrite (sat_lcut_in E 8 HX), (sat_lcut_in E 7 HX). apply sat_lraw_anti. lia.
Qed.

Lemma sat_epay_crs1 : forall (E : ECX) (t : jv), Z.of_nat (length (e_x E)) <= EC_NMAX ->
  ck_read (e_x E) = Some t ->
  ck_crcs_max (e_x E) (ck_ncalls (e_x E)) 1 t + sat_ccut E 9 <= sat_ccut E 8 /\ sat_lcut E 9 <= sat_lcut E 8.
Proof.
  intros E t HX Ht. split.
  - rewrite (sat_ccut_in E 9 HX), (sat_ccut_in E 8 HX). unfold sat_gate. cbn [Nat.leb].
    unfold sat_c_crs1. rewrite (sat_tree_some E _ t Ht). lia.
  - rewrite (sat_lcut_in E 9 HX), (sat_lcut_in E 8 HX). apply sat_lraw_anti. lia.
Qed.

Lemma sat_ecov_cno : forall E : ECX, Z.of_nat (length (e_x E)) <= EC_NMAX ->
  LIVE_check_no_overread (e_x E) <= sat_lcut E 1.
Proof.
  intros E HX. rewrite (sat_lcut_in E _ HX). unfold sat_lraw.
  apply sat_max_l, sat_gate_ge. lia.
Qed.

Lemma sat_ecov_pno : forall E : ECX, Z.of_nat (length (e_x E)) <= EC_NMAX ->
  PRH_FnPj.LIVE_pj_parse (e_x E) <= sat_lcut E 2.
Proof.
  intros E HX. rewrite (sat_lcut_in E _ HX). unfold sat_lraw.
  apply sat_max_r, sat_max_l, sat_gate_ge. lia.
Qed.

Lemma sat_ecov_caw : forall E : ECX, Z.of_nat (length (e_x E)) <= EC_NMAX -> e_n E <= EC_NMAX ->
  LIVE_check_as_written (e_n E) <= sat_lcut E 3.
Proof.
  intros E HX Hn. rewrite (sat_lcut_in E _ HX). unfold sat_lraw.
  apply sat_max_r, sat_max_r, sat_max_r, sat_max_l.
  eapply Z.le_trans; [|apply sat_gate_ge; lia].
  unfold sat_l_caw. rewrite (proj2 (Z.leb_le (e_n E) EC_NMAX) Hn). cbv beta iota. lia.
Qed.

Lemma sat_ecov_crs0 : forall E : ECX, Z.of_nat (length (e_x E)) <= EC_NMAX ->
  LIVE_check_reject_clean_starved (e_x E) PjTree.JNull <= sat_lcut E 4.
Proof.
  intros E HX. rewrite (sat_lcut_in E _ HX). unfold sat_lraw.
  apply sat_max_r, sat_max_r, sat_max_r, sat_max_r, sat_max_l, sat_gate_ge. lia.
Qed.

Lemma sat_ecov_crt : forall (E : ECX) (t : jv), Z.of_nat (length (e_x E)) <= EC_NMAX ->
  ck_read (e_x E) = Some t -> LIVE_check_round_trip t <= sat_lcut E 7.
Proof.
  intros E t HX Ht. rewrite (sat_lcut_in E _ HX). unfold sat_lraw.
  apply sat_max_r, sat_max_r, sat_max_r, sat_max_r, sat_max_r, sat_max_r.
  eapply Z.le_trans; [|apply sat_gate_ge; lia].
  unfold sat_l_crt. rewrite (sat_tree_some E _ t Ht). lia.
Qed.

Lemma sat_ecov_crs1 : forall (E : ECX) (t : jv), Z.of_nat (length (e_x E)) <= EC_NMAX ->
  ck_read (e_x E) = Some t -> LIVE_check_reject_clean_starved (e_x E) t <= sat_lcut E 8.
Proof.
  intros E t HX Ht. rewrite (sat_lcut_in E _ HX). unfold sat_lraw.
  apply sat_max_r, sat_max_r, sat_max_r, sat_max_r, sat_max_r, sat_max_l.
  eapply Z.le_trans; [|apply sat_gate_ge; lia].
  unfold sat_l_crs. rewrite (sat_tree_some E _ t Ht). lia.
Qed.

Lemma sat_pay : @ec_pay rc cp L PA sat_ccut sat_lcut.
Proof.
  exact {| epay_cno := sat_epay_cno; epay_pno := sat_epay_pno; epay_crs0 := sat_epay_crs0;
           epay_crt := sat_epay_crt; epay_crs1 := sat_epay_crs1;
           ecov_cno := sat_ecov_cno; ecov_pno := sat_ecov_pno; ecov_caw := sat_ecov_caw;
           ecov_crs0 := sat_ecov_crs0; ecov_crt := sat_ecov_crt; ecov_crs1 := sat_ecov_crs1 |}.
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. THE THEOREM: the budget hypotheses of every segment statement hold together. *)
Theorem ec_pay_sat : exists ccut lcut : ECX -> nat -> Z,
  @ec_ccut_ok rc L PA ccut /\ @ec_lcut_ok rc L PA lcut /\ @ec_pay rc cp L PA ccut lcut.
Proof. exists sat_ccut, sat_lcut. exact (conj sat_ccut_ok (conj sat_lcut_ok sat_pay)). Qed.

(* ---------------------------------------------------------------------- *)
(* 6. THE RECORD OF THE OLD ecov_caw (statement blobs 7af9d0fe1491 / e9a447dec8c0): under the length guard alone,
      LIVE_check_as_written (e_n E) <= ec_lcut E 3 refutes ec_lcut_ok at ANY live budget as soon as one entry
      context exists: e_n is free in ecx, so E0 with e_pl := [] and e_n := LIVE_LIB passes the guard and asks
      LIVE_LIB + 1 <= ec_lcut E 3 <= LIVE_LIB. Hence ecov_caw's second guard e_n E <= EC_NMAX (3b0db38483cf). *)
Definition sat_ecov_caw_old (lcut : ECX -> nat -> Z) : Prop :=
  forall E : ECX, Z.of_nat (length (e_x E)) <= EC_NMAX -> LIVE_check_as_written (e_n E) <= lcut E 3%nat.

Lemma sat_ecov_caw_old_refuted : forall (lcut : ECX -> nat -> Z) (E0 : ECX),
  @ec_lcut_ok rc L PA lcut -> sat_ecov_caw_old lcut -> False.
Proof.
  intros lcut E0 Hl Hc.
  set (E := @MkEcx rc L PA (e_ly E0) (e_S E0) (e_W E0) (e_regs E0) (e_mem E0) (e_md E0) (e_p E0) LIVE_LIB []
              (e_cnt E0) (e_ran E0) (e_sm E0) (e_os E0) (e_i0 E0) (e_H0 E0) (e_hist0 E0)).
  assert (HX : Z.of_nat (length (e_x E)) <= EC_NMAX) by (change (e_x E) with (@nil Z); cbn; unfold EC_NMAX; lia).
  pose proof (Hc E HX) as H. destruct (Hl E 3%nat 3%nat) as [[_ Hle] _].
  change (e_n E) with LIVE_LIB in H. unfold LIVE_check_as_written in H. lia.
Qed.

End S.

(* AT THE PRESET'S PARAMETERS (cf_head = 16): CLOSED *)
Theorem ec_pay_sat_preset : forall (rc : YM05.RunCeil) (L : YP0b.ptable YPsym.asym) (PA : @YC4aP.PAImg rc L),
  exists ccut lcut : @ecx rc L PA -> nat -> Z,
    @ec_ccut_ok rc L PA ccut /\ @ec_lcut_ok rc L PA lcut /\
    @ec_pay rc CfParamsPreset.CfParams_preset L PA ccut lcut.
Proof.
  intros rc L PA. apply (@ec_pay_sat rc CfParamsPreset.CfParams_preset L PA).
  change (@YGcfNames.cf_head CfParamsPreset.CfParams_preset) with 16. lia.
Qed.

About ec_pay_sat.
Print Assumptions ec_pay_sat.
Print Assumptions ec_pay_sat_preset.
Print Assumptions sat_ecov_caw_old_refuted.
