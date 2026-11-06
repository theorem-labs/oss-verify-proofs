(* omx-clap-core/fuzz_preset, Spec: the SECONDARY requests of the model run, counted (nsec) and weighed by their mapped
   size (tsec), and the closing arithmetic of the count meter. Row A17 of a Theorem Labs lane's Part 4 plan (owner a Theorem Labs lane).
   Nothing here is a function's proof (rule 24); kind: model bound.

   WHAT IT SAYS.
   - nsec evs: the HMal r / HRe _ r events of evs whose request r is secondary (PresetLiveSec.sec_req r, i.e.
     negb (PresetRoom.is_primary r); r >= 64,513). tsec evs: the sum of YG00.sec_map_size r over the same events.
     A free asks for nothing (it re-tags st_secs in place), so it counts nothing.
   - nsec_prefix_le / tsec_prefix_le: a prefix of an event list counts at most the whole list (the meter is needed at
     every allocator call's entry and post, i.e. at every prefix of the run).
   - NCALL / TCALL: the per-call bounds that Spec/PresetSecTotalRun.v proves over PresetRun.call_evs (nsec_call,
     tsec_call) for every input x (above MAXB a call makes no event), and per run of at most 4 calls (nsec_run,
     tsec_run, and their prefix forms). NCALL = 25,127 and TCALL = 10,520,122,619 (NCALL_value, TCALL_value).
   - sec_n_fits / sec_t_fits: with the driver's non-errbuf base NB (secondaries) and TB (their mapped bytes),
     NB <= NB_MAX_ALLOWED = 30,564 and TB <= TB_MAX_ALLOWED = 25,028,373,524 give NB + 4 NCALL <= 2 ^ 17 and
     TB + 4 TCALL + 12,288 (NB + 4 NCALL) <= 2 ^ 36; sec_t_fits_exact drops the per-entry term (sm_len is
     sec_map_size exactly): TB <= TB_MAX_EXACT = 26,638,986,260 gives TB + 4 TCALL <= 2 ^ 36. The _cap forms conclude
     <= any cap at least SEC_N_CAP / SEC_T_CAP.

   CLOSURE: the kit's PresetRoomPos.v Requires this leaf for nsec / tsec. It Requires only PresetReqAt, PresetRun,
   PresetRoom and YG00, all already in PresetRoomPos's closure. The run bounds are in PresetSecTotalRun.v, which
   Requires PresetLiveSec / PresetGate (lib/Prog/SlotSizes.v and its plain lib/Prog/*_c.v files) and
   PresetLiveBytes (which Requires PresetRoomPos): neither may enter this file's closure. *)
From Stdlib Require Import ZArith List Lia Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ the meter over an event list *)

(* the secondary requests an event list makes: PresetRun.nprodR of PresetLiveSec.sec_req (whose body is
   negb (PresetRoom.is_primary r); PresetLiveSec.v is not Required here, see CLOSURE) *)
Definition nsec (evs : list hev) : nat := nprodR (fun r => negb (PresetRoom.is_primary r)) evs.

(* the mapped size of one event's secondary (YG00.sec_map_size: the request, its two red zones, page-rounded, plus
   a page), 0 for a primary request or a free *)
Definition sec_mapped (e : hev) : Z :=
  match e with
  | HMal r | HRe _ r => if negb (PresetRoom.is_primary r) then YG00.sec_map_size r else 0
  | _ => 0
  end.

Fixpoint tsec (evs : list hev) : Z :=
  match evs with
  | [] => 0
  | e :: es => sec_mapped e + tsec es
  end.

Lemma nsec_app : forall a b, nsec (a ++ b) = (nsec a + nsec b)%nat.
Proof. intros a b. unfold nsec. apply nprodR_app. Qed.

Lemma tsec_app : forall a b, tsec (a ++ b) = tsec a + tsec b.
Proof. induction a as [|e a IH]; intros b; cbn [app tsec]; [lia|]. rewrite IH. lia. Qed.

(* the allocator's own test: a request is from the primary iff PresetRoom.is_primary (the same text) *)
Lemma from_primary_is_primary : forall r, YG00.from_primary r = PresetRoom.is_primary r.
Proof. intros r. reflexivity. Qed.

Lemma round_up_nn : forall x a, 0 <= x -> 0 < a -> 0 <= YG00.round_up x a.
Proof. intros x a Hx Ha. unfold YG00.round_up. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia. Qed.

Lemma rz_size_nn : forall r, 0 <= YG00.rz_size r.
Proof. intros r. unfold YG00.rz_size. rewrite Z.shiftl_nonneg. lia. Qed.

Lemma sec_map_size_pos : forall r, 0 < YG00.sec_map_size r.
Proof.
  intros r. unfold YG00.sec_map_size, YG00.needed_size, YG00.needed_primary, YG00.rounded_size, YG00.kPage.
  pose proof (rz_size_nn r) as Hz.
  pose proof (round_up_nn (Z.max r 8) 8 ltac:(lia) ltac:(lia)) as Hs.
  destruct (YG00.from_primary r).
  - pose proof (round_up_nn (YG00.round_up (Z.max r 8) 8 + YG00.rz_size r) 4096 ltac:(lia) ltac:(lia)). lia.
  - pose proof (round_up_nn (YG00.round_up (Z.max r 8) 8 + YG00.rz_size r + YG00.rz_size r) 4096
                  ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma sec_mapped_nn : forall e, 0 <= sec_mapped e.
Proof.
  intros [r | m r | r | L]; cbn [sec_mapped]; try lia;
    destruct (negb (PresetRoom.is_primary r)); pose proof (sec_map_size_pos r); lia.
Qed.

Lemma tsec_nn : forall evs, 0 <= tsec evs.
Proof. induction evs as [|e es IH]; cbn [tsec]; [lia|]. pose proof (sec_mapped_nn e). lia. Qed.

(* a prefix counts at most the whole list *)
Lemma nsec_prefix_le : forall evs i, (nsec (firstn i evs) <= nsec evs)%nat.
Proof.
  intros evs i. rewrite <- (firstn_skipn i evs) at 2. rewrite nsec_app. lia.
Qed.

Lemma tsec_prefix_le : forall evs i, tsec (firstn i evs) <= tsec evs.
Proof.
  intros evs i. rewrite <- (firstn_skipn i evs) at 2. rewrite tsec_app. pose proof (tsec_nn (skipn i evs)). lia.
Qed.

(* ================================================================ the per-call constants
   (PresetSecTotalRun.v proves them; each piece names the segment of PresetRun.call_evs it bounds) *)

(* secondaries of one reading of x under any grants: PresetLiveSec.w_reads, weights JT_SEC, m_A = 1024 *)
Definition RD_N : Z := (MAXB + 96) / 1024.
(* of one read-back of the file's tree (its grows are the reading's; its other events those of the compact text,
   <= 3 MAXB bytes, each charging >= 64,496) *)
Definition RB_N : Z := (MAXB + 96) / 1024 + (3 * MAXB + 96) / 64496.
(* of one writer or rendered () chain: the capacities at least double and stay below 112 MAXB (pretty text) or
   6 MAXB + 2 (compact text), and 64,497 * 2 ^ 13 > 112 MAXB, 64,497 * 2 ^ 9 > 6 MAXB + 2 *)
Definition CH_P : Z := 13.
Definition CH_C : Z := 9.

(* one call: the 3 padded copies and expected ()'s scratch (4), 5 readings (3 check_no_overread readings, the main
   parse, the starved parse), 3 read-backs (compact, pretty, the rewritten copy, which has at most 4 more:
   PresetGate.g_nprod_copy), pj_string / pj_set (4: PresetRun.set_evs_nprodR), 5 pretty chains (the writer twice,
   its starved prefix, the copy's writer, rendered (pretty)) and 4 compact chains (the writer twice, its starved
   prefix, rendered (compact)) *)
Definition NCALL : Z := 4 + 5 * RD_N + 3 * RB_N + 4 + 4 + 5 * CH_P + 4 * CH_C.

(* YG00.sec_map_size r <= r + SEC_MAP_OVH for r >= 8: 7 of rounding, two 2048-byte red zones, 4095 of page rounding,
   the extra page *)
Definition SEC_MAP_OVH : Z := 12294.
(* the secondary request bytes of one reading: each secondary reader event asks for at most 225 times its JT_SEC
   weight, and a reading weighs at most |x| + 96 (PresetLiveSec.jr_run_wcharge) *)
Definition RD_T : Z := 225 * (MAXB + 96).
(* of one read-back: its grows as a reading of x, its other events at most twice their charge (compact text) *)
Definition RB_T : Z := RD_T + 2 * (3 * MAXB + 96).
(* the top object's one extra grow (kids 56 c + 16 and keys 8 c + 16, c <= 2 (MAXB + 8) + 8): pj_set's grow, and the
   rewritten copy's appended member *)
Definition TOP_GROW_T : Z := 128 * (MAXB + 8) + 544.
(* one chain: a doubling list below U sums to at most 2 U, plus the head (16) of each secondary capacity *)
Definition CHP_T : Z := 2 * (112 * MAXB) + 16 * CH_P.
Definition CHC_T : Z := 2 * (6 * MAXB + 2) + 16 * CH_C.

(* one call's secondary request bytes: copies and scratch (4 MAXB + 49), the readings, the read-backs, the two top
   grows, the chains *)
Definition TREQ_CALL : Z := 4 * MAXB + 49 + 5 * RD_T + 3 * RB_T + 2 * TOP_GROW_T + 5 * CHP_T + 4 * CHC_T.
Definition TCALL : Z := TREQ_CALL + SEC_MAP_OVH * NCALL.

Lemma NCALL_value : NCALL = 25127.
Proof. vm_compute. reflexivity. Qed.

Lemma TREQ_CALL_value : TREQ_CALL = 10211211281.
Proof. vm_compute. reflexivity. Qed.

Lemma TCALL_value : TCALL = 10520122619.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ the closing arithmetic *)

(* a Theorem Labs lane's caps: SEC_N_CAP must equal cf_kmax CfParams_preset (2 ^ 17, a Theorem Labs lane's round 6) and SEC_T_CAP must equal
   cf_T_max CfParams_preset (2 ^ 36; not yet in the tree). The _cap lemmas take any cap at least these, so the
   switch to a Theorem Labs lane's names is one rewrite. *)
Definition SEC_N_CAP : Z := 2 ^ 17.
Definition SEC_T_CAP : Z := 2 ^ 36.
(* a Theorem Labs lane's per-entry term of the byte budget *)
Definition SEC_T_PER : Z := 12288.

(* the driver's largest allowed base: NB non-errbuf secondaries (A18, a Theorem Labs lane's drv102) and TB their mapped bytes *)
Definition NB_MAX_ALLOWED : Z := SEC_N_CAP - 4 * NCALL.
Definition TB_MAX_ALLOWED : Z := SEC_T_CAP - 4 * TCALL - SEC_T_PER * SEC_N_CAP.

Lemma NB_MAX_ALLOWED_value : NB_MAX_ALLOWED = 30564.
Proof. vm_compute. reflexivity. Qed.

Lemma TB_MAX_ALLOWED_value : TB_MAX_ALLOWED = 25028373524.
Proof. vm_compute. reflexivity. Qed.

Lemma sec_n_fits_cap : forall cap NB, SEC_N_CAP <= cap -> NB <= NB_MAX_ALLOWED -> NB + 4 * NCALL <= cap.
Proof. intros cap NB Hc HN. unfold NB_MAX_ALLOWED in HN. lia. Qed.

Lemma sec_n_fits : forall NB, NB <= NB_MAX_ALLOWED -> NB + 4 * NCALL <= SEC_N_CAP.
Proof. intros NB HN. apply sec_n_fits_cap; [lia | exact HN]. Qed.

Lemma sec_t_fits_cap : forall cap NB TB, SEC_T_CAP <= cap -> NB <= NB_MAX_ALLOWED -> TB <= TB_MAX_ALLOWED ->
  TB + 4 * TCALL + SEC_T_PER * (NB + 4 * NCALL) <= cap.
Proof.
  intros cap NB TB Hc HN HT. unfold NB_MAX_ALLOWED in HN. unfold TB_MAX_ALLOWED in HT.
  unfold SEC_T_PER in *. lia.
Qed.

Lemma sec_t_fits : forall NB TB, NB <= NB_MAX_ALLOWED -> TB <= TB_MAX_ALLOWED ->
  TB + 4 * TCALL + SEC_T_PER * (NB + 4 * NCALL) <= SEC_T_CAP.
Proof. intros NB TB HN HT. apply sec_t_fits_cap; [lia | exact HN | exact HT]. Qed.

(* the tight form: a new secondary entry's sm_len is sec_map_size n exactly (YG00.v:352 / :360), which tsec already
   counts, so no per-entry term is owed; TB may then be up to TB_MAX_EXACT = 26,638,986,260 *)
Definition TB_MAX_EXACT : Z := SEC_T_CAP - 4 * TCALL.

Lemma TB_MAX_EXACT_value : TB_MAX_EXACT = 26638986260.
Proof. vm_compute. reflexivity. Qed.

Lemma sec_t_fits_exact_cap : forall cap TB, SEC_T_CAP <= cap -> TB <= TB_MAX_EXACT -> TB + 4 * TCALL <= cap.
Proof. intros cap TB Hc HT. unfold TB_MAX_EXACT in HT. lia. Qed.

Lemma sec_t_fits_exact : forall TB, TB <= TB_MAX_EXACT -> TB + 4 * TCALL <= SEC_T_CAP.
Proof. intros TB HT. apply sec_t_fits_exact_cap; [lia | exact HT]. Qed.
