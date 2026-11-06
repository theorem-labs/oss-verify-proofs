(* omx-clap-core/fuzz_preset, Spec: iface_room_pos, P8's premises at a position of the model run, and NOTHING else.
   WHY THIS FILE EXISTS (the driver-contract owner's ruling, owner of lib/A/PresetCfnA.v, and the kit owner's, 2026-10-29): the kit's contract
   texts (lib/A/PRH_Fn*.v) carry iface_room_pos at entry and in every post arm. The definition lived in
   lib/A/PresetCfnA.v (f346344fe450 :438-445), the interface, which Requires the kit (PRH_Base / PRH_Img), so the kit
   could not Require it without inverting the layering, and through PresetLiveSec / PresetGate -> lib/Prog/SlotSizes.v
   it would pull six plain lib/Prog/*_c.v files into the kit's closure. This leaf adds four files to the kit's Require closure
   (Reusable/YGcfFrees.v, Spec/PresetRun.v, Spec/PresetReqAtNoMiss.v, and the ASan owner's Spec/PresetRunQ.v for the fifth
   conjunct) and NO lib/Prog/*_c.v (measured before PresetRunQ.v; PresetRunQ.v Requires only YG00, PresetReqAt and
   PresetRun).
   ONE HOME: PresetCfnA.v / PresetCfnB.v re-export it as `Notation iface_room_pos := PresetRoomPos.iface_room_pos.`
   (the same term, the PresetLiveBounds pattern), so counts_of_room_pos / _rl / _ok, run_allocs_follow,
   iface_room_pos_entry and the rest apply unchanged. DO NOT define it a second time; the lemmas over it stay in
   PresetCfnA.v (they need PresetLiveSec).
   The definition below is VERBATIM from PresetCfnA.v f346344fe450 :438-445, with its comment :432-437, except its
   fifth conjunct (the free history) and its comment's free_cf clause (two cases now, :76-78, PresetRoomPosKeep.rp_free_parts_big), plus the A15 conjunct below (the last one). *)
(* Modified by Theorem Labs, 2026-10-30, for the kit: the free history is
   PresetRunQ.hfrees_q, the frees that enter the quarantine (free_cf's size test, Quarantine::Put), not hfrees. *)
(* A15 (2026-10-30, ADOPTED by the kit owner in the kit's Step-1 text; PART4 row A15, the COUNT meter): the
   last conjunct of iface_room_pos, rp_count (firstn i run) S, bounds the allocator's secondary map entries at every
   run position by the model prefix: nsec_cf S <= rp_NB + nsec prefix and sec_T_cf S <= rp_TB + tsec prefix, under
   the closed premise secs_steps_cf. The state counts nsec_cf / sec_T_cf are the cf layer's (lib/Reusable/YGcfNames.v,
   Z-valued folds over st_secs under sec_user_cf); the closed premise is A14's lib/Reusable/YGcfSecsStep.v
   (secs_steps_cf: the per-call steps of malloc_cf / free_cf / the realloc trees; secs_steps_cf_holds proves it, so a
   top discharges it once); sec_user_cf keeps the entries with sm_size >= 0,
   so the error buffer's control entries (YG00cf.v :96, :128; sm_size < 0) count in neither: a class-full report,
   which happens only inside a REFUSED primary malloc_cf (no model event), adds nothing. The model counts nsec /
   tsec are the S1 owner's A17 lib/Spec/PresetSecTotal.v (the HMal r / HRe _ r events with a secondary request, and
   the sum of their sec_map_size). rp_NB / rp_TB bound the driver's own entries before the first harness call
   (A18's base, rp_base below); A17's sec_n_fits / sec_t_fits allow rp_NB <= 30,564 and rp_TB <= 25,028,373,524.
   The keeps are lib/Spec/PresetRoomPosKeep.v; the interface's iface_room_at (lib/A/PresetCfnA.v,
   lib/AU/PresetCfnB.v) carries the same conjunct at the whole prefix. YGcfSecsStep adds Reusable files to this
   leaf's Require closure (its own, YGcfNames' and YGcfRoomStep's); still no lib/Prog/*_c.v. *)
From Stdlib Require Import ZArith List Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfFrees YGcfNames YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetReqAt PresetRun PresetRunQ PresetSecTotal.
Import ListNotations.
Local Open Scope Z_scope.

(* A15: the base (the driver's own secondary entries before the first harness call, A18) and the meter, over
   Z. rp_nsec is the ONE place the state count's name shows: the cf layer's nsec_cf (YGcfNames.v, a Z over
   sec_user_cf). *)
Definition rp_nsec (S : astate) : Z := YGcfNames.nsec_cf S.
(* rp_NB / rp_TB are ROUND bounds, chosen above the driver's measured base at the loop entry (the image-A driver-count walk / the image-B driver-count walk,
   both images: rp_nsec <= 12, sec_T_cf <= 201,363,462) and within A17's allowed bases (rp_NB <= 30,564,
   rp_TB <= 25,028,373,524). *)
Definition rp_NB : Z := 64.
Definition rp_TB : Z := 2 ^ 30.
(* Two sources: rp_nsec / sec_T_cf are STATE counts over st_secs (the cf layer's, YGcfNames.v); PresetSecTotal.nsec
   / tsec are EVENT-LIST counts over hev (A17). The suffix is not cosmetic. *)
Definition rp_count (es : list PresetReqAt.hev) (S : astate) : Prop :=
  YGcfSecsStep.secs_steps_cf ->
  rp_nsec S <= rp_NB + Z.of_nat (PresetSecTotal.nsec es) /\
  YGcfNames.sec_T_cf S <= rp_TB + PresetSecTotal.tsec es.
Definition rp_base (S : astate) : Prop :=
  YGcfSecsStep.secs_steps_cf -> rp_nsec S <= rp_NB /\ YGcfNames.sec_T_cf S <= rp_TB.

(* THE LAYER'S NAMES ONLY: the conversions, so a downstream statement names YGcfNames.nsec_cf / sec_T_cf and no rp_
   wrapper. sec_T_cf has no wrapper (rp_count and rp_base name YGcfNames.sec_T_cf itself); its twin is the
   unfolded meter, rp_count_layer / rp_base_layer, both by conversion. *)
Lemma rp_nsec_layer : forall S, rp_nsec S = YGcfNames.nsec_cf S.
Proof. reflexivity. Qed.
Lemma rp_count_layer : forall es S, rp_count es S <->
  (YGcfSecsStep.secs_steps_cf ->
   YGcfNames.nsec_cf S <= rp_NB + Z.of_nat (PresetSecTotal.nsec es) /\
   YGcfNames.sec_T_cf S <= rp_TB + PresetSecTotal.tsec es).
Proof. intros es S. split; intro H; exact H. Qed.
Lemma rp_base_layer : forall S, rp_base S <->
  (YGcfSecsStep.secs_steps_cf -> YGcfNames.nsec_cf S <= rp_NB /\ YGcfNames.sec_T_cf S <= rp_TB).
Proof. intros S. split; intro H; exact H. Qed.

(* P8's premises at ANY position i of the model run (iface_room_at is the case of a call's entry,
   iface_room_pos_entry), and the walk's fact that one malloc_cf is made at a consumer allocation of the run with
   these premises in its state: run_allocs_follow, a NAMED PREMISE of preset_no_refusal, owner the slot's walk (the
   PROGRAM-WALKS row of LLVMFuzzerTestOneInput). The walk carries iface_room_pos from the entry
   (run_allocs_follow_entry) to each of its malloc_cf calls: a malloc_cf adds its request to the live set, a free_cf
   of a chunk the quarantine takes (req_size r <= kQuarantineMax) moves the history by YGcfFrees.cf_frees_step_free,
   a larger chunk is recycled at once and moves neither hist nor hfrees_q (PresetRoomPosKeep.rp_free_parts_big), and
   each call must be the next event of hruns. *)
Definition iface_room_pos (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
  (i : nat) (H0 : list Z) (hist : list YG00.chunk) (S : astate) : Prop :=
(exists d : list Z, (length d <= 3)%nat /\
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.hlive (firstn i (PresetRun.hruns sm x os)) ++ d)) /\
YGcfRoom.room_inv_cf S /\
YGcfRoom.quar_fifo_cf hist S /\ YGcfFrees.cf_hist_ok hist /\
YGcfFrees.cf_frees_follow H0 (PresetRunQ.hfrees_q (firstn i (PresetRun.hruns sm x os))) hist /\
rp_count (firstn i (PresetRun.hruns sm x os)) S.

(* the count at a state with no secondary map entry (the allocator's start state) *)
Lemma rp_count_start : forall S, st_secs S = [] -> rp_count [] S.
Proof.
intros S E _. unfold rp_nsec, YGcfNames.nsec_cf, YGcfNames.sec_T_cf. rewrite E.
split; apply Z.leb_le; reflexivity.
Qed.

(* the count before any model event is the base (A18 gives rp_base at the driver's loop entry) *)
Lemma rp_count_of_base : forall S, rp_base S -> rp_count [] S.
Proof.
intros S H A. destruct (H A) as (N & T).
change (Z.of_nat (PresetSecTotal.nsec [])) with 0. change (PresetSecTotal.tsec []) with 0.
rewrite !Z.add_0_r. split; assumption.
Qed.
