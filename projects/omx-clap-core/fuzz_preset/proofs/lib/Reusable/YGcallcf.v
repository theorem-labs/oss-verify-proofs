(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (route (B''): the call memory in the call rules): the cf forms are YGcallx's at
   QMm := QMm_cf, acall_pre_cf's trailing conjuncts verbatim (since the cf layer's field round 3 they end with
   cf_hull_ok S /\ arodata_ok_cf segs B mem; part 3c took memnorm out), so acall_pre_cf_x / afree_realizes_cf_x stay BY
   REFLEXIVITY; QM := QM_cf, their STATE part (the new FA_GROW headroom + FA_GROW_MAX / 8, and cf_hull_ok), for the model
   laws; QMQ_cf (QMm_cf S mem -> QM_cf S) is a projection. QM_cf_of_room takes cf_hull_ok, as the layer's
   acall_pre_cf_intro does (abudget_room_cf and mroom_cf_of_live need it); QMm_cf_of_room adds the memory fact. *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): the cf call post under the re-hide
   (YGcfRehidePost.acall_post_cf_rh, the post of the primed free and realloc rows) as the generic rules' callee post
   APOST_cf, with its two laws POST_AR_cf / POST_J_cf (YGcallx's apost_ar_law / apost_j_law) at the world relation
   wle' segs RZ_cf; ajournal_x_of_rh_off is the fact POST_J_cf rests on: a call's dead set misses each view-frame
   domain of a journal around the call. Additive: no existing statement changes. *)
(* Modified by Theorem Labs, 2026-10-30 (the call memory's RELRO fact): arodata_ok_cf_of_journal carries the call
   memory's arodata_ok_cf (QMm_cf's last conjunct) across a journal at any world relation R; arodata_ok_cf_of_journal_P
   starts it from a walk entry's reader form arodata_okP (YGcfAroBridge.arodata_ok_cf_of_P). Additive. *)
(* Modified by Theorem Labs, 2026-10-31 (field round 3 part 3c: aro_addr_cf covers the RELRO range and cf_ro_reads):
   arodata_ok_cf_of_journal and arodata_ok_cf_of_journal_P take YGcfAroBridge.ro_reads_nw_t (a segment inside 2^64
   holds each cf_ro_reads range), as YGcfAroBridge.arodata_ok_cf_of_P does, and their PST premise covers every
   aro_addr_cf address. *)
(* Theorem Labs, 2026-10: the cf BRIDGE. Each call form of the second allocator instance (YG0dcf.v) IS the generic
   form of YGcallx.v at
     ARx  := fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md,
     QMm  := QMm_cf below, acall_pre_cf's trailing conjuncts (qmeter_cf, the live-secondary bound, ERRB_ROOM, the
             free-array headroom, batch_room_cf, cf_hull_ok and arodata_ok_cf on the call memory), in their
             order; QM := QM_cf, the same without the memory fact (the model laws' state predicate),
     mt   := malloc_cf, nmax := cf_malloc_max, ft := free_cf, WFx := Wf_cf (as_universe B), XS := xs_cf (YG0ncf.v).
   The equations below hold by unfolding (reflexivity) where the cf form has no extra conjunct; malloc_leaf_cf ends
   with `xs_placed_cf ly' (snd r)` (YG0dcf.v), so the malloc forms are related at the relation ARcf /\ xs_placed_cf
   (malloc_leaf_cf_xs, an iff), not at plain ARcf.
   The laws: AR_laws_x at ARcf (hl := cf_head) follows from AR_laws_cf alone (AR_laws_x_cf): the one law AR_laws_cf
   lacks, the extra-area law, is h-mani-a8's YGcfExtra.ARx_extra_law_ok_ARcf (cgif's AR_extra_law_ok, YG0p.v:39, over
   ARcf); the harness-block shadow law (field 14) is h-mani-a8's YGcfHeadSh.ARx_hshadow_law_cf_ok at cf_head; the
   tail-granule law (field 15) is h-mani-a8's YGcfTail.amalloc_tail_vis_end_cf; the const cells (field 16) are
   ARmcf's amc_const (YG0ncf.v); the image law (field 17) is ALedger_cf's alc_img and, for the frames, frame_facts_cf
   with layout_ok's lo_img; the layout law (field 18) is ARmcf's amc_layout; the depot law (field 25) is ARmcf's amc_wf's
   wfc_depot, depot_fits' first conjunct (ARcf_depot_nodup). ARx_owned_low_law is AR_laws_cf's alc_owned_low;
   ARx_wf_law is ARmcf's amc_wf.
   The model laws: alloc_model_laws_x at cf follows from universe_ok (as_universe B) by YG0ucf.v's model_laws_cf_ok
   (alloc_model_laws_x_cf). YGcfAmx.v's amx_malloc_cf / amx_free_cf are not used: their posts bound st_nev from
   ABOVE only, and the rules' journal count k + (st_nev S2 - st_nev Sc) needs the lower bound malloc_post_cf /
   free_post_ycf give (st_nev s + 1 <= st_nev s', resp. =).
   The room: QM_cf follows from ARcf, qtight, ROOM_cf and cf_hull_ok (QM_cf_of_room, YGcfRoomPre.v's ingredients);
   QMm_cf adds arodata_ok_cf on the call memory (QMm_cf_of_room).
   ecall_pre_cf_x targets the frame-class lane's ecall_pre_x (FCiface.v).
   Uses the shared cf instance classes CfImg / CfParams only; no preset name, no address, no ledger, no numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfTok YG08cf YGcfRoomPre FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG06bcf YG07cf YG03cf YG0ucf YGcfXs.
(* Required, not Imported: YGcfExtra restates YCbqG's ARx_extra_law under the same name (convertible). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfExtra.
(* Required, not Imported: the cf proofs of AR_laws_x's fields 14 and 15, cited by qualified name. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfHeadSh YGcfTail.
(* the re-hide layer: the relation wle' (YA0nH), the dead set and the primed call post (YGcfRehidePost) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YG0dH YGcfRehidePost YG0dcfR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI16 YCbq.
(* the RELRO bridge from the reader form (YGcfAroBridge) and the reader form itself (PresetRodata), by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRodata.
Import ListNotations.
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* acall_pre_cf's trailing STATE conjuncts (YG0dcf.v acall_pre_cf, field round 3), as one predicate: the generic rules'
   QM at cf, the model laws' state predicate. *)
Definition QM_cf (S : astate) : Prop :=
qmeter_cf S /\ Z.of_nat (length (st_sec_arr S)) < cf_sec_live_max /\ ERRB_ROOM S /\
abudget_cf S + FA_GROW_MAX + FA_GROW_MAX / 8 <= CF_MAX /\ batch_room_cf S /\ cf_hull_ok S.

Section J.
Variable segs : list Segment.
Variable B : asyms.

(* acall_pre_cf's trailing conjuncts verbatim, the state ones and the one on the call memory (field round 3; part 3c
   took memnorm out): the generic rules' QMm at cf. *)
Definition QMm_cf (S : astate) (mem : word -> option byte) : Prop :=
qmeter_cf S /\ Z.of_nat (length (st_sec_arr S)) < cf_sec_live_max /\ ERRB_ROOM S /\
abudget_cf S + FA_GROW_MAX + FA_GROW_MAX / 8 <= CF_MAX /\ batch_room_cf S /\ cf_hull_ok S /\
arodata_ok_cf segs B mem.

Lemma QMQ_cf : forall S mem, QMm_cf S mem -> QM_cf S.
Proof. intros S mem (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _). exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 Q6))))). Qed.

(* ---------------------------------------------------------------------------- *)
(* The forms.                                                                     *)
Lemma acall_pre_cf_x :
acall_pre_cf segs B = acall_pre_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) QMm_cf.
Proof. reflexivity. Qed.

Lemma acall_post_cf_x :
acall_post_cf segs B = acall_post_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md).
Proof. reflexivity. Qed.

Lemma ecall_pre_cf_x :
ecall_pre_cf segs B = ecall_pre_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md).
Proof. reflexivity. Qed.

Lemma free_leaf_cf_x :
free_leaf_cf segs B = free_leaf_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md).
Proof. reflexivity. Qed.

Lemma afree_realizes_cf_x :
afree_realizes_cf segs B =
afree_realizes_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) QMm_cf free_cf.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------- *)
(* The laws the generic rules take, at ARcf.                                      *)
Lemma ARx_owned_low_law_cf_x : AR_laws_cf segs B ->
ARx_owned_low_law segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md).
Proof. intros L. destruct L; assumption. Qed.

Lemma ARx_wf_law_cf_x :
ARx_wf_law segs (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) (Wf_cf (as_universe B)).
Proof. intros ly S Hp W mem md (M & _). destruct M. assumption. Qed.

(* AR_laws_x's field 25 at ARcf: the depot holds no repeat, ARmcf's amc_wf (Wf_cf's wfc_depot, YG01.v depot_fits'
   first conjunct). *)
Lemma ARcf_depot_nodup : forall ly S Hp W mem md, ARcf segs B ly S Hp W mem md -> List.NoDup (st_depot S).
Proof. intros ly S Hp W mem md H. exact (proj1 (wfc_depot _ _ _ _ _ (amc_wf _ _ _ _ _ (proj1 H)))). Qed.

Lemma AR_laws_x_of_cf : AR_laws_cf segs B ->
ARx_extra_law segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) ->
AR_laws_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) cf_head.
Proof.
intros L X. assert (Lb : AR_blocks_law_cf segs B) by (destruct L; assumption).
assert (Lsh : AR_shadow_law_cf segs B) by (destruct L; assumption).
assert (Lz : AR_zshadow_law_cf segs B) by (destruct L; assumption).
constructor; try (destruct L; assumption).
- intros ly S Hp W mem md p n HAR Hin. destruct (Lb ly S Hp W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6 & _).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
- (* YCbqG's ARx_shadow_law (no hidden head inside the block) from AR_shadow_law_cf: with p not in Hp, hd_skip is 0. *)
intros ly S Hp W mem md p n HAR Hin Hh.
destruct (Lb ly S Hp W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
assert (E0 : hd_skip Hp p = 0).
{ unfold hd_skip. destruct (existsb (Z.eqb p) Hp) eqn:Ex; [|reflexivity].
exfalso. apply existsb_exists in Ex as (h & Hin' & Heq). apply Z.eqb_eq in Heq. subst h.
apply (Hh p Hin'). pose proof (req_size_bounds n ltac:(lia)) as (_ & R1 & _). lia. }
destruct (Lsh ly S Hp W mem md p n HAR Hin) as [Hb Hv]. rewrite E0, Z.add_0_r, Z.sub_0_r in Hb. exact (conj Hb Hv).
- (* YCbqG's per-byte zero-shadow law from AR_zshadow_law_cf at the real stack (the head of zero_shadow_ranges), with
     both stack bounds page aligned (layout_ok's lo_top); the proof is YCbqG.v AR_laws_x_of_AR's last bullet. *)
intros ly S Hp W mem md a HAR Ha. pose proof HAR as (M & _).
pose proof (lo_top _ (amc_layout _ _ _ _ _ M)) as (_ & _ & _ & _ & Plo & Phi & _).
unfold page_aligned in Plo, Phi.
assert (Elo : ly_stk_lo ly mod 8 = 0).
{ apply Z.mod_divide in Plo as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with ((q * 512) * 8) by lia. apply Z.mod_mul. lia. }
assert (Ehi : ly_stk_hi ly mod 8 = 0).
{ apply Z.mod_divide in Phi as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with ((q * 512) * 8) by lia. apply Z.mod_mul. lia. }
pose proof (Lz ly S Hp W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
cbn [fst snd] in HZ. unfold zero_shadow in HZ.
assert (Hdlo : ly_stk_lo ly = 8 * (ly_stk_lo ly / 8)) by (apply Z.div_exact; [lia | exact Elo]).
assert (Hdhi : ly_stk_hi ly = 8 * (ly_stk_hi ly / 8)) by (apply Z.div_exact; [lia | exact Ehi]).
assert (Hi1 : ly_stk_lo ly / 8 <= a / 8) by (apply Z.div_le_mono; lia).
assert (Hi2 : a / 8 < ly_stk_hi ly / 8) by (apply Z.div_lt_upper_bound; [lia | rewrite <- Hdhi at 1; lia]).
specialize (HZ (a / 8 - ly_stk_lo ly / 8)).
unfold shadow_of_addr in HZ.
replace (SHADOW_OFF + ly_stk_lo ly / 8 + (a / 8 - ly_stk_lo ly / 8)) with (SHADOW_OFF + a / 8) in HZ by lia.
apply HZ. split; [lia|].
replace (ly_stk_hi ly - ly_stk_lo ly) with (8 * (ly_stk_hi ly / 8 - ly_stk_lo ly / 8)) by lia.
rewrite (Z.mul_comm 8), Z.div_mul by lia. lia.
- (* field 14: the harness-block shadow law at hl = cf_head *)
exact (YGcfHeadSh.ARx_hshadow_law_cf_ok segs B L).
- (* field 15: the tail granule, up to the end of the block's last granule *)
intros ly S Hp W mem md p n a HAR Hin Ha. exact (YGcfTail.amalloc_tail_vis_end_cf segs B ly S Hp W mem md p n a HAR Hin Ha).
- (* field 16: the image's const cells, ARmcf's amc_const *)
intros ly S Hp W mem md (M & _). exact (amc_const _ _ _ _ _ M).
- (* field 17: ly_img covers every segment (ALedger_cf's alc_img, as FCifaceCf.v:136), and a live fake frame lies
     at or above the image's top: the fake stack is disjoint from ly_img (frame_facts_cf), starts at or above 4096
     and is longer than kImgLo (= fst (ly_img ly), layout_ok's lo_img), so it cannot start below the image's end *)
intros ly S Hp W mem md HAR. pose proof HAR as (M & LG & _). split.
+ intros sg Hsg. exact (alc_img _ _ _ _ LG sg Hsg).
+ intros cid pos Hin. pose proof (lo_img _ (amc_layout _ _ _ _ _ M)) as (I1 & I2 & _).
destruct (frame_facts_cf B ly S Hp _ cid pos M Hin) as (C1 & _ & [F1 _] & D & _ & P1 & _).
assert (HF : fst (ly_img ly) + snd (ly_img ly) <= ly_F ly).
{ destruct (Z_lt_le_dec (ly_F ly) (fst (ly_img ly) + snd (ly_img ly))) as [Hlt|Hge]; [|exact Hge].
exfalso. apply D. exists (Z.max (ly_F ly) (fst (ly_img ly))). unfold in_zr. cbn [fst snd].
unfold kImgLo, kFakeStackSize in *. split; [lia | left; lia]. }
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)) as CN.
unfold frame_addr, kFakeFramesOff in *. lia.
- (* field 18: the layout is layout_ok, ARmcf's amc_layout (as FCifaceCf.v:135) *)
intros ly S Hp W mem md HAR. exact (amc_layout _ _ _ _ _ (proj1 HAR)).
- (* field 19: frame_facts_cf's first conjunct *)
intros ly S Hp W mem md cid pos (M & _) Hin. exact (proj1 (frame_facts_cf B ly S Hp _ cid pos M Hin)).
- (* field 20: ahs_pres off the client bytes (YG0qcf.client_band_vis_cf), and YG0q.aview_band *)
intros ly S Hp W mem md a (M & LG & _ & _ & [HP _]) Ha Hh Hv AV.
assert (IMG : forall sg, In sg segs ->
  4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd).
{ intros sg Hsg. eapply YG0qcf.al_img_env_cf; [exact (amc_layout _ _ _ _ _ M) | exact LG | exact Hsg]. }
assert (NC : ~ aclient_byte B ly S a).
{ intros HCB. assert (VIS : aview segs (w_H W) mem a <> None)
    by (eapply YG0qcf.client_band_vis_cf; [exact M | exact Ha | exact HCB]). exact (VIS AV). }
apply (proj2 (YG0q.aview_band segs (w_H W) mem a IMG Ha Hh)); [| exact AV].
exact (HP a Ha NC (or_intror Hv)).
- (* field 21: a live block is an allocated chunk's user range, ck_base + ck_rz with 16 <= ck_rz, and its extent
     lies on one arm (chunk_facts_cf) *)
intros ly S Hp W mem md p n (M & _) Hin Hhi.
unfold ablocks, blocks in Hin. rewrite map_map in Hin.
apply in_map_iff in Hin as (k & Ek & Hk). apply filter_In in Hk as [Hk _].
cbn [fst snd] in Ek. injection Ek as Ep _.
pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & _ & _ & G4 & G5 & _ & G7 & G8 & _).
assert (R1 : 1 <= req_size (ck_req k)) by (unfold req_size; destruct (Z.eqb_spec (ck_req k) 0); lia).
rewrite G4 in Ep. subst p. destruct G1 as [_ [Lo | [Hi _]]]; unfold kLowShadowBeg, kHighMemBeg in *; lia.
- (* field 22 at cf_head: a hidden head's shadow is 0xf7 (a Theorem Labs lane's YGcfHeadSh.AR_head_shadow_cf), the block base
     16-aligned and cf_head 8-aligned, so every head byte is in a fully poisoned granule *)
intros ly S Hp W mem md b n a HAR Hb Hin Ha.
destruct (YGcfHeadSh.AR_head_shadow_cf segs B ly S Hp W mem md b n L HAR Hb Hin) as [_ HH].
destruct (alc_blocks _ _ L ly S Hp W mem md b n HAR Hb) as (B16 & _).
pose proof cf_head_al as A8.
assert (Hb8 : b mod 8 = 0).
{ apply Z.mod_divide in B16 as [q Hq]; [|lia]. rewrite Hq. replace (q * 16) with ((q * 2) * 8) by lia. apply Z.mod_mul. lia. }
assert (Hi : 0 <= (a - b) / 8 < cf_head / 8).
{ split; [apply Z.div_pos; lia|]. apply Z.mod_divide in A8 as [c Hc]; [|lia]. rewrite Hc, Z.div_mul by lia.
  apply Z.div_lt_upper_bound; lia. }
specialize (HH _ Hi).
replace (shadow_addr a) with (shadow_addr b + (a - b) / 8); [exact HH|].
pose proof (shadow_of_addr_aligned_off SHADOW_OFF b (a - b) Hb8) as E. unfold shadow_of_addr in E.
replace (b + (a - b)) with a in E by lia. unfold shadow_addr. lia.
- (* field 24 (F21b): the chunk's extent, by its kind (chunk_facts_cf): a primary chunk's region ends far below the
     ceiling (region_in_prim, class bound kFreeArrayOffset); a secondary chunk's map keeps the right redzone above the
     block (amc_placed). Field 23 is alc_flag, closed by the constructor line. *)
intros ly S Hp W mem md p n (M & _) Hin.
unfold ablocks, blocks in Hin. rewrite map_map in Hin.
apply in_map_iff in Hin as (k & Ek & Hk). apply filter_In in Hk as [Hk _].
cbn [fst snd] in Ek. injection Ek as Ep En. subst n.
pose proof (amc_layout _ _ _ _ _ M) as LO. pose proof (amc_placed _ _ _ _ _ M) as [PL _].
pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & G7 & G8 & GG).
rewrite G4 in Ep. subst p.
destruct (ck_beg k) as [|off|r o|c q] eqn:Eb; try solve [destruct GG].
+ cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
  pose proof (region_in_prim ly (prim_class off) LO ltac:(lia)) as (_ & _ & _ & _ & R5).
  unfold ASAN_CEIL, kFreeArrayOffset in *. lia.
+ destruct GG as (-> & Hfp & Gbase & Gext & Gin & _).
  pose proof (proj1 (Forall_forall _ _) PL _ Gin) as (_ & _ & I3). cbn [fst snd] in I3.
  unfold sec_map_size, needed_size in Gext, I3. rewrite Hfp in Gext, I3. cbv beta iota in Gext, I3.
  unfold needed_primary in Gext, I3.
  pose proof (round_up_ge_x (rounded_size (ck_req k) + rz_size (ck_req k) + rz_size (ck_req k)) kPage
    ltac:(unfold kPage; lia)) as RU.
  assert (RS : req_size (ck_req k) <= rounded_size (ck_req k)).
  { unfold rounded_size. pose proof (round_up_ge_x (Z.max (ck_req k) 8) 8 ltac:(lia)).
    unfold req_size. destruct (Z.eqb_spec (ck_req k) 0); lia. }
  unfold ck_rz in *. unfold kPage in *. lia.
- (* field 25: the depot holds no repeat (ARcf_depot_nodup) *)
intros ly S Hp W mem md HAR. exact (ARcf_depot_nodup ly S Hp W mem md HAR).
Qed.

(* cgif YG0q.v:91 extent_zone over ARmcf: a chunk's extent is in the primary reserve or right after the guard page
   of its secondary map. chunk_facts_cf (YG0scf.v) keeps cgif's conjunct order, so cgif's proof carries over; the
   class bound is kFreeArrayOffset (cfacts_cf) where cgif's is 2 ^ 31, both below a region's 2 ^ 32. *)
Lemma extent_zone_cf : forall ly S Hp rd k, ARmcf B ly S Hp rd -> In k (st_chunks S) ->
(ly_prim ly <= ck_base B ly k /\ ck_base B ly k + ck_extent k <= ly_prim ly + kPrimResvSize) \/
(exists m len, In (m, len) (sec_extents ly S) /\ m + kPage = ck_base B ly k /\ len = ck_extent k + kPage).
Proof.
intros ly S Hp rd k M Hk. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG].
- left. cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
pose proof (region_in_prim ly (prim_class o) (amc_layout _ _ _ _ _ M) ltac:(lia)) as (R1 & R2 & _). lia.
- right. destruct GG as (_ & _ & Gbase & Gext & Gin & _). exists (ly_sec ly r), (sec_map_size (ck_req k)).
unfold kPage in *. split; [exact Gin | split; lia].
Qed.

(* AR_laws_x at ARcf from AR_laws_cf alone. *)
Lemma AR_laws_x_cf : AR_laws_cf segs B ->
AR_laws_x segs B (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md) cf_head.
Proof. intros L. exact (AR_laws_x_of_cf L (YGcfExtra.ARx_extra_law_ok_ARcf segs B)). Qed.

(* ---------------------------------------------------------------------------- *)
(* The model laws at cf, from YG0ucf.v's model_laws_cf_ok: its malloc / free fields are atok_cf tokens; the four   *)
(* facts the generic rules read are atok_cf_asafe, atok_cf_agprog, atok_cf_nospin and atok_cf_apath, and          *)
(* malloc_post_cf / free_post_ycf imply malloc_post_x / free_post_x. QM_cf carries the fields' room premises. The  *)
(* depot laws: model_laws_cf_ok holds at EVERY universe, so it is run again at YGcallx.v's univ_at (the call's     *)
(* depot plus its trace); the post's Wf_cf there bounds the new depot (univ_at_step).                              *)
(* Wf_cf names its universe only in wfc_depot. *)
Lemma Wf_cf_univ : forall U V s, Wf_cf U s -> depot_fits V (st_depot s) -> Wf_cf V s.
Proof. intros U V s W Hd. unfold Wf_cf in *. destruct W. constructor; assumption. Qed.
Lemma alloc_model_laws_x_cf : universe_ok (as_universe B) ->
alloc_model_laws_x B QM_cf malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)).
Proof.
intros HU. pose proof (model_laws_cf_ok (as_universe B) HU) as ML. constructor.
- intros s n tr W0 HQ Hn Hl Ht. destruct HQ as (_ & R1 & R2 & _ & R3 & _).
pose proof (mlr_malloc_cf _ ML s n tr W0 Hn Hl Ht R1 R2 R3) as T.
split; [exact (atok_cf_asafe _ _ _ T)|]. split; [exact (atok_cf_agprog _ _ _ T)|]. split; [exact (atok_cf_nospin _ _ T)|].
intros tr' [p s'] Hp. destruct (atok_cf_apath _ _ _ tr' _ T Hp) as (ns & HQ').
destruct HQ' as (_ & Hnev & [Hlen _] & Hfr & Hbl & _).
split; [lia|]. split; [exact Hlen|]. split; [exact Hfr|].
destruct p; first [exact Hbl | exact (proj1 Hbl)].
- intros s p n tr W0 HQ Hp Ht. destruct HQ as (_ & _ & _ & _ & R3 & _).
pose proof (mlr_free_cf _ ML s p n tr W0 R3 Hp Ht) as T.
split; [exact (atok_cf_asafe _ _ _ T)|]. split; [exact (atok_cf_agprog _ _ _ T)|]. split; [exact (atok_cf_nospin _ _ T)|].
intros tr' r Hp'. destruct (atok_cf_apath _ _ _ tr' r T Hp') as (ns & HQ').
destruct HQ' as (_ & Hnev & Hse & Hfr & Hbl & _).
split; [lia|]. split; [exact (proj1 (secs_ext_cf_of_secs_ext _ _ Hse))|]. split; [exact Hfr | exact Hbl].
- intros s n tr W0 HQ Hn Hl Ht tr' r Hp. destruct HQ as (_ & R1 & R2 & _ & R3 & _).
pose proof (wfc_depot _ _ _ _ _ W0) as Hd.
pose proof (model_laws_cf_ok _ (univ_at_ok _ _ _ HU Hd Ht)) as MLV.
pose proof (mlr_malloc_cf _ MLV s n tr (Wf_cf_univ _ _ _ W0 (univ_at_fits _ _ tr Hd)) Hn Hl (univ_at_admits _ _ _ Ht)
  R1 R2 R3) as T.
destruct r as [p s']. destruct (atok_cf_apath _ _ _ tr' _ T Hp) as (ns & WV & _).
exact (univ_at_step _ _ _ (wfc_depot _ _ _ _ _ WV)).
- intros s p n tr W0 HQ Hp Ht tr' r Hp'. destruct HQ as (_ & _ & _ & _ & R3 & _).
pose proof (wfc_depot _ _ _ _ _ W0) as Hd.
pose proof (model_laws_cf_ok _ (univ_at_ok _ _ _ HU Hd Ht)) as MLV.
pose proof (mlr_free_cf _ MLV s p n tr (Wf_cf_univ _ _ _ W0 (univ_at_fits _ _ tr Hd)) R3 Hp (univ_at_admits _ _ _ Ht))
  as T.
destruct (atok_cf_apath _ _ _ tr' r T Hp') as (ns & WV & _).
exact (univ_at_step _ _ _ (wfc_depot _ _ _ _ _ WV)).
Qed.

(* The universe premise of alloc_model_laws_x_cf, from ARcf (ARmcf's amc_universe). *)
Lemma universe_ok_of_ARcf : forall ly S Hp W mem md, ARcf segs B ly S Hp W mem md -> universe_ok (as_universe B).
Proof. intros ly S Hp W mem md (M & _). exact (amc_universe _ _ _ _ _ M). Qed.

(* ---------------------------------------------------------------------------- *)
(* The room: QM_cf from ARcf, qtight, ROOM_cf and the driver's hull admission cf_hull_ok. qmeter_cf's room and the   *)
(* free-array headroom are derived as acall_pre_cf_intro (YGcfRoomPre.v) derives them: mroom_cf_of_live and          *)
(* abudget_room_cf (YG08cf.v), each of which takes cf_hull_ok since field round 3 / the hull round.                  *)
Lemma QM_cf_of_room : forall ly S Hp W mem md,
ARcf segs B ly S Hp W mem md -> qtight S -> ROOM_cf S -> cf_hull_ok S -> QM_cf S.
Proof.
intros ly S Hp W mem md HAR HQ [R1 [R2 R3]] HO.
pose proof (amc_wf _ _ _ _ _ (proj1 HAR)) as W0. unfold Wf_cf in W0.
pose proof (qtight_qloose S HQ) as QL.
assert (FA : abudget_cf S + (FA_GROW_MAX + FA_GROW_MAX / 8) <= CF_MAX)
  by exact (abudget_room_cf _ _ _ _ _ _ W0 QL HO FA_GROW_MAX_le).
rewrite Z.add_assoc in FA.
exact (conj (conj HQ (mroom_cf_of_live _ _ _ _ _ W0 QL HO)) (conj R1 (conj R2 (conj FA (conj R3 HO))))).
Qed.

(* QMm_cf adds the call memory's fact (field round 3; part 3c). *)
Lemma QMm_cf_of_room : forall ly S Hp W mem md,
ARcf segs B ly S Hp W mem md -> qtight S -> ROOM_cf S -> cf_hull_ok S ->
arodata_ok_cf segs B mem -> QMm_cf S mem.
Proof.
intros ly S Hp W mem md HAR HQ HR HO AD.
destruct (QM_cf_of_room ly S Hp W mem md HAR HQ HR HO) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 AD)))))).
Qed.

(* ---------------------------------------------------------------------------- *)
(* The cf instance's relation for the generic rules: ARcf with the error-message buffer placed (ARxs below).     *)
Local Abbreviation ARxs := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S).

(* Any AR_laws_x survives conjoining a state predicate, which the frame law leaves alone. *)
Lemma AR_laws_x_and : forall {hl : Z} (AR0 : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
(P : alayout -> astate -> Prop),
AR_laws_x segs B AR0 hl -> AR_laws_x segs B (fun ly S Hp W mem md => AR0 ly S Hp W mem md /\ P ly S) hl.
Proof.
intros hl AR0 P L. constructor.
- intros ly S Hp W mem md p n [H _]. exact (alx_blocks _ _ _ L ly S Hp W mem md p n H).
- intros ly S Hp W mem md mem' md' [H HP] H1 H2 H3 H4 H5 H6. exact (conj (alx_frame _ _ _ L ly S Hp W mem md mem' md' H H1 H2 H3 H4 H5 H6) HP).
- intros ly S Hp W mem md cid pos [H _]. exact (alx_frames _ _ _ L ly S Hp W mem md cid pos H).
- intros ly S Hp W mem md a [H _]. exact (alx_stack _ _ _ L ly S Hp W mem md a H).
- intros ly S Hp W mem md a [H _]. exact (alx_owned_image _ _ _ L ly S Hp W mem md a H).
- intros ly S Hp W mem md [H _]. exact (alx_sep _ _ _ L ly S Hp W mem md H).
- intros ly S Hp W mem md ly' [H _]. exact (alx_layout _ _ _ L ly S Hp W mem md ly' H).
- intros ly S Hp W mem md a [H _]. exact (alx_client_img _ _ _ L ly S Hp W mem md a H).
- intros ly S Hp W mem md a [H _]. exact (alx_extra _ _ _ L ly S Hp W mem md a H).
- intros ly S Hp W mem md [H _]. exact (alx_const _ _ _ L ly S Hp W mem md H).
- intros ly S Hp W mem md p n [H _]. exact (alx_shadow _ _ _ L ly S Hp W mem md p n H).
- intros ly S Hp W mem md r [H _]. exact (alx_zshadow _ _ _ L ly S Hp W mem md r H).
- intros ly S Hp W mem md a [H _]. exact (alx_zshadow_byte _ _ _ L ly S Hp W mem md a H).
- intros ly S Hp W mem md b n [H _]. exact (alx_hshadow _ _ _ L ly S Hp W mem md b n H).
- intros ly S Hp W mem md p n a [H _]. exact (alx_blocks_tail _ _ _ L ly S Hp W mem md p n a H).
- intros ly S Hp W mem md [H _]. exact (alx_const_cells _ _ _ L ly S Hp W mem md H).
- intros ly S Hp W mem md [H _]. exact (alx_img _ _ _ L ly S Hp W mem md H).
- intros ly S Hp W mem md [H _]. exact (alx_layout_ok _ _ _ L ly S Hp W mem md H).
- intros ly S Hp W mem md cid pos [H _]. exact (alx_frames_cid _ _ _ L ly S Hp W mem md cid pos H).
- intros ly S Hp W mem md a [H _]. exact (alx_band_pres _ _ _ L ly S Hp W mem md a H).
- intros ly S Hp W mem md p n [H _]. exact (alx_blocks_hi _ _ _ L ly S Hp W mem md p n H).
- intros ly S Hp W mem md b n a [H _]. exact (alx_hhead _ _ _ L ly S Hp W mem md b n a H).
- intros ly S Hp W mem md cid pos [H _]. exact (alx_flag _ _ _ L ly S Hp W mem md cid pos H).
- intros ly S Hp W mem md p n [H _]. exact (alx_blocks_ceil8 _ _ _ L ly S Hp W mem md p n H).
- intros ly S Hp W mem md [H _]. exact (alx_depot_nodup _ _ _ L ly S Hp W mem md H).
Qed.

Lemma AR_laws_x_xs : AR_laws_cf segs B -> AR_laws_x segs B ARxs cf_head.
Proof. intros L. exact (AR_laws_x_and _ xs_placed_cf (AR_laws_x_cf L)). Qed.

Lemma ARx_owned_low_law_xs : AR_laws_cf segs B -> ARx_owned_low_law segs B ARxs.
Proof. intros L ly S Hp W mem md a [H _]. exact (ARx_owned_low_law_cf_x L ly S Hp W mem md a H). Qed.

Lemma ARx_wf_law_xs : ARx_wf_law segs ARxs (Wf_cf (as_universe B)).
Proof. intros ly S Hp W mem md [H _]. exact (ARx_wf_law_cf_x ly S Hp W mem md H). Qed.

(* The generic rules' extents law at XS := xs_cf: every fact comes from xs_placed_cf (the separation from the
   secondary, static and extra extents, alignment and ceiling) and ARcf's chunk / frame / image placement
   (chunk_facts_cf, frame_facts_cf, YG0scf.v; alc_img). *)
Lemma ARx_xs_law_xs : ARx_xs_law segs B ARxs xs_cf.
Proof.
intros ly S Hp W mem md a [HAR HX] Ha. pose proof HAR as (M & L & _).
apply Exists_exists in Ha as (e & He & Hae). unfold in_zr in Hae.
pose proof (proj1 (Forall_forall _ _) HX e He) as (Hal & Happ & Hce & HD).
assert (DZ : forall z, In z (sec_extents ly S ++ static_extents ly ++ ly_extra ly) -> ~ (fst z <= a < fst z + snd z)).
{ intros z Hz Hin. pose proof (proj1 (Forall_forall _ _) HD z Hz) as D. unfold zdisjoint in D. lia. }
assert (ST : forall z, In z (static_extents ly) -> ~ (fst z <= a < fst z + snd z)).
{ intros z Hz. apply DZ. apply in_or_app. right. apply in_or_app. left. exact Hz. }
assert (OW : forall z, In z (owned_extents ly) -> In z (static_extents ly)).
{ intros z Hz. unfold static_extents. apply in_or_app. left. exact Hz. }
split; [lia|]. split; [exact (in_app_addr _ _ _ Happ Hae)|].
split.
{ intros (sg & Hsg & Hr). pose proof (alc_img _ _ _ _ L sg Hsg) as [I1 I2].
apply (ST (ly_img ly)); [unfold static_extents; apply in_or_app; right; right; left; reflexivity | lia]. }
split.
{ intros p n Hin Hr. apply (In_ablocks B) in Hin as (k & Hk & Hst & Hu & Hn). subst p n.
pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (HE : ck_base B ly k <= a < ck_base B ly k + ck_extent k) by (rewrite G4 in Hr; lia).
destruct (extent_zone_cf ly S Hp _ k M Hk) as [[P1 P2] | (m & len & Hin & Hm & Hl)].
- apply (ST (ly_prim ly, kPrimResvSize)); [apply OW; unfold owned_extents; cbn; tauto | cbn [fst snd]; lia].
- apply (DZ (m, len)); [apply in_or_app; left; exact Hin | cbn [fst snd]; unfold kPage in *; lia]. }
split.
{ intros cid pos Hf Hr. pose proof (frame_facts_cf B ly S Hp _ cid pos M Hf) as (C1 & C2 & F1 & F2 & F3 & P1 & P2 & _).
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)) as CNN.
apply (ST (ly_F ly, kFakeStackSize)); [apply OW; unfold owned_extents; cbn; tauto | cbn [fst snd]].
unfold frame_addr, kFakeFramesOff in *. lia. }
intros HXa. apply Exists_exists in HXa as (z & Hz & Hza). unfold in_zr in Hza.
apply (DZ z); [apply in_or_app; right; apply in_or_app; right; exact Hz | exact Hza].
Qed.

(* The call forms at ARxs are the cf forms with xs_placed_cf at the call's state. *)
Lemma acall_pre_x_xs : forall ly S Hp W regs mem md ch,
acall_pre_x segs B ARxs QMm_cf ly S Hp W regs mem md ch <->
acall_pre_cf segs B ly S Hp W regs mem md ch /\ xs_placed_cf ly S.
Proof.
intros ly S Hp W regs mem md ch. split.
- intros ([HAR HX] & R). exact (conj (conj HAR R) HX).
- intros ((HAR & R) & HX). exact (conj (conj HAR HX) R).
Qed.

Lemma ecall_pre_x_xs : forall ly S Hp W regs mem md,
ecall_pre_x segs B ARxs ly S Hp W regs mem md <-> ecall_pre_cf segs B ly S Hp W regs mem md /\ xs_placed_cf ly S.
Proof.
intros ly S Hp W regs mem md. split.
- intros ([HAR HX] & R). exact (conj (conj HAR R) HX).
- intros ((HAR & R) & HX). exact (conj (conj HAR HX) R).
Qed.

(* The malloc leaf: malloc_leaf_cf ends with xs_placed_cf at the post, so it IS malloc_leaf_x at ARxs. *)
Lemma malloc_leaf_cf_xs : forall ly S Hp W regs mem md n r W' c',
malloc_leaf_cf segs B ly S Hp W regs mem md n r W' c' <-> malloc_leaf_x segs B ARxs xs_cf ly S Hp W regs mem md n r W' c'.
Proof.
intros ly S Hp W regs mem md n r W' c'. split.
- intros (ly' & regs' & mem' & md' & Hc & (A1 & R) & Hg & Hq & He & HX & HE & HR).
exists ly', regs', mem', md'. exact (conj Hc (conj (conj (conj A1 HX) R) (conj Hg (conj Hq (conj He (conj HE HR)))))).
- intros (ly' & regs' & mem' & md' & Hc & ((A1 & HX) & R) & Hg & Hq & He & HE & HR).
exists ly', regs', mem', md'. exact (conj Hc (conj (conj A1 R) (conj Hg (conj Hq (conj He (conj HX (conj HE HR))))))).
Qed.

(* The free leaf at ARxs, from the cf leaf, xs_placed_cf at the call and free_cf's state frame (h-mani-a8's
   free_leaf_cf_xs_keep, YGcfXs.v, restated at the leaf's own layout). *)
Lemma free_leaf_cf_xs : forall ly S Hp W regs mem md ch p n r W' c',
acall_pre_cf segs B ly S Hp W regs mem md ch -> xs_placed_cf ly S -> free_frame_cf S (snd r) ->
free_leaf_cf segs B ly S Hp W regs mem md p n r W' c' -> free_leaf_x segs B ARxs ly S Hp W regs mem md p n r W' c'.
Proof.
intros ly S Hp W regs mem md ch p n r W' c' Hpre HP (FX & FS) (ly' & regs' & mem' & md' & Hc & (A1 & A2 & R) & HQ).
pose proof (amc_wf _ _ _ _ _ (proj1 (proj1 Hpre))) as W0. unfold Wf_cf in W0.
pose proof (xs_placed_cf_layout _ _ _ _ ly ly' S W0 A2 HP) as HP'.
assert (HX : xs_placed_cf ly' (snd r)).
{ apply (xs_placed_cf_mono ly' S (snd r)); [exact (FX ly') | intros z Hz; left; exact (FS ly' z Hz) | exact HP']. }
exists ly', regs', mem', md'. exact (conj Hc (conj (conj (conj A1 HX) (conj A2 R)) HQ)).
Qed.

(* amreal keeps any property every return of the tree has (cfx_ipost, YGcfXs.v). *)
Lemma amreal_ipost {R} : forall (t : itree astate R) (P : R -> Prop) W c (Q : R -> world segs -> config -> Prop),
cfx_ipost t P -> amreal segs t W c Q -> amreal segs t W c (fun r W' c' => Q r W' c' /\ P r).
Proof.
induction t as [r | q s k IH | pc | f]; intros P W c Q HP H; cbn in *.
- eapply SRr_mono; [exact H | intros W' c' _ H'; exact (conj H' HP)].
- eapply SRr_mono; [exact H |]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; intros i Hi; apply IH; [apply HP | apply Hc, Hi]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. apply IH; [apply HP | exact Hc].
- exact H.
- exact I.
Qed.

(* The cf texts, lifted to ARxs; no premise beyond the cf text. *)
Lemma amalloc_realizes_x_xs : amalloc_realizes_cf segs B ->
amalloc_realizes_x segs B ARxs QMm_cf malloc_cf cf_malloc_max xs_cf.
Proof.
intros AM ly S Hp W regs mem md n ch Hpre H1 H2 H3 H4.
destruct (proj1 (acall_pre_x_xs ly S Hp W regs mem md ch) Hpre) as [Hpc _].
exact (amreal_mono segs _ _ _ _ _ (fun r W' c' Hl => proj1 (malloc_leaf_cf_xs ly S Hp W regs mem md n r W' c') Hl)
(AM ly S Hp W regs mem md n ch Hpc H1 H2 H3 H4)).
Qed.

Lemma afree_realizes_x_xs : afree_realizes_cf segs B -> afree_realizes_x segs B ARxs QMm_cf free_cf.
Proof.
intros AF ly S Hp W regs mem md p n ch Hpre H1 H2 H3 H4.
destruct (proj1 (acall_pre_x_xs ly S Hp W regs mem md ch) Hpre) as [Hpc HX].
pose proof (amreal_ipost _ _ _ _ _ (cfx_fr_free_cf p (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S)
(AF ly S Hp W regs mem md p n ch Hpc H1 H2 H3 H4)) as HR.
exact (amreal_mono segs _ _ _ _ _ (fun r W' c' Hl => free_leaf_cf_xs ly S Hp W regs mem md ch p n r W' c' Hpc HX
(free_frame_cf_of_state S (snd r) (proj1 (proj2 Hl)) (proj2 (proj2 Hl))) (proj1 Hl)) HR).
Qed.

(* Projections from the ARxs forms to the cf forms (drop xs_placed_cf): what the cf room / null-post lemmas take. *)
Lemma acall_pre_x_xs_cf : forall ly S Hp W regs mem md ch,
acall_pre_x segs B ARxs QMm_cf ly S Hp W regs mem md ch -> acall_pre_cf segs B ly S Hp W regs mem md ch.
Proof. intros ly S Hp W regs mem md ch H. exact (proj1 (proj1 (acall_pre_x_xs ly S Hp W regs mem md ch) H)). Qed.

Lemma malloc_leaf_x_xs_cf : forall ly S Hp W regs mem md n r W' c',
malloc_leaf_x segs B ARxs xs_cf ly S Hp W regs mem md n r W' c' -> malloc_leaf_cf segs B ly S Hp W regs mem md n r W' c'.
Proof. intros ly S Hp W regs mem md n r W' c'. exact (proj2 (malloc_leaf_cf_xs ly S Hp W regs mem md n r W' c')). Qed.

Lemma free_leaf_x_xs_cf : forall ly S Hp W regs mem md p n r W' c',
free_leaf_x segs B ARxs ly S Hp W regs mem md p n r W' c' -> free_leaf_cf segs B ly S Hp W regs mem md p n r W' c'.
Proof.
intros ly S Hp W regs mem md p n r W' c' (ly' & regs' & mem' & md' & Hc & ((HAR & _) & R) & Rest).
exists ly', regs', mem', md'. exact (conj Hc (conj (conj HAR R) Rest)).
Qed.

(* ---------------------------------------------------------------------------- *)
(* The call post under the re-hide as the generic rules' callee post, and its two laws at wle' segs RZ_cf.      *)
(* APOST_cf: acall_post_cf_rh (a re-hiding free or realloc's post) with the error-message buffer placed at the post *)
(* state, ARxs's state part, as the plain bridge adds it. POST_AR_cf: the invariant, the layout step and the saved   *)
(* registers. POST_J_cf: the call's journal at wle' segs RZ_cf. The post's world step wle_in (dead_shadow_new lyc   *)
(* Sc S2) lies in wle' RZ_cf (wle_in_mono, dead_shadow_new_RZ); its frame excepts the same set, which misses each    *)
(* view-frame domain of the call's journal (ajournal_x_of_rh_off), so call_effect_journal_xwR gives the journal.     *)
(* POST_J_cf takes no premise beyond the call state's ARxs (a premise of apost_j_law) and the engine laws that      *)
(* POST_J_x takes.                                                                                                 *)
Definition APOST_cf (stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) : Prop :=
acall_post_cf_rh segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' /\ xs_placed_cf ly' S'.

Lemma POST_AR_cf : apost_ar_law segs ARxs APOST_cf.
Proof.
intros stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ((H1 & H2 & _ & H4 & _) & HX).
exact (conj (conj H1 HX) (conj H2 H4)).
Qed.

(* The shadow of an 8-aligned range inside the fake stack misses a call's dead set: dead_shadow_new_off at the static
   extent (ly_F lyc, kFakeStackSize), which is no dead slot's extent, since sec_placed's pairwise list would make it
   disjoint from itself. *)
Lemma dsn_frame_shadow_off : forall lyc Sc S2 fa fb a,
  sec_placed lyc Sc -> live_slots_placed lyc Sc ->
  ly_F lyc <= fa -> fa + fb <= ly_F lyc + kFakeStackSize ->
  fa mod 8 = 0 -> 0 <= fa -> 0 <= fb ->
  shadow_addr fa <= a < shadow_addr fa + fb / 8 ->
  ~ dead_shadow_new lyc Sc S2 a.
Proof.
intros lyc Sc S2 fa fb a HP LP F1 F2 M8 H0 Hb Ha.
set (x := fa + 8 * (a - shadow_addr fa)).
assert (Ex : shadow_addr x = a).
{ unfold x, shadow_addr in *. pose proof (Z.div_mod fa 8 ltac:(lia)) as D. rewrite M8 in D.
  replace (fa + 8 * (a - (SHADOW_OFF + fa / 8))) with ((a - SHADOW_OFF) * 8) by lia.
  rewrite Z.div_mul by lia. lia. }
assert (Hx : fa <= x < fa + fb).
{ unfold x, shadow_addr in *. pose proof (Z.div_mod fb 8 ltac:(lia)). pose proof (Z.mod_pos_bound fb 8 ltac:(lia)). lia. }
rewrite <- Ex.
assert (Hs : In (ly_F lyc, kFakeStackSize) (static_extents lyc)).
{ unfold static_extents. apply in_or_app. left. unfold owned_extents. cbn. tauto. }
apply (dead_shadow_new_off lyc Sc S2 (ly_F lyc, kFakeStackSize) x HP LP).
- apply in_or_app. right. exact Hs.
- cbn [snd]. unfold kFakeStackSize. lia.
- cbn [fst snd]. lia.
- intros r sm _ Hin Eq. rewrite <- Eq in Hin.
  pose proof (pairwise_In zdisjoint _ _ _ (sec_extents lyc Sc) (static_extents lyc) eq_refl (proj2 HP) Hin Hs) as Z.
  unfold zdisjoint in Z. cbn [fst snd] in Z. unfold kFakeStackSize in Z. lia.
Qed.

Section off.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* A call (lyc, Sc) -> S2 inside a journal from (ly, S) to (ly', S'): ARcf at the call, the call's layout and frames
   reached from the journal's start, ARx at the end. The call's dead set misses each view-frame domain of the
   journal: above the ceiling (dead_shadow_new_below_ceiling); the bytes of the blocks live at the end (application
   memory by AR_laws_x's blocks law; dead_shadow_new_app); the image (segs_low; dead_shadow_new_not_low); the start's
   frames, whose bytes lie in the fake stack (frame_facts_cf at the call; dead_shadow_new_app) and whose shadow is
   off the set (dsn_frame_shadow_off, with sec_placed and live_slots_placed from ARcf at the call); and the extra
   areas (YGcfExtra's law at ARcf; dead_shadow_new_app). *)
Theorem ajournal_x_of_rh_off : forall n lyc Sc Hpc Wc memc mdc S2 ly S ly' S' Hp' W' mem' md',
  ARcf segs B lyc Sc Hpc Wc memc mdc ->
  layout_le n ly lyc ->
  (forall f, In f (frames S) -> In f (frames Sc)) ->
  ARx ly' S' Hp' W' mem' md' ->
  (forall a, YM05.alloc_ceiling <= a -> ~ dead_shadow_new lyc Sc S2 a) /\
  (forall p n' i, In (p, n') (ablocks B ly' S') -> 0 <= i < req_size n' -> ~ dead_shadow_new lyc Sc S2 (p + i)) /\
  (forall a, in_img segs a -> ~ dead_shadow_new lyc Sc S2 a) /\
  (forall cid pos a, In (cid, pos) (frames S) ->
     (in_zr a (YCbq.frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
     ~ dead_shadow_new lyc Sc S2 a) /\
  (forall a, Exists (in_zr a) (ly_extra ly) -> ~ dead_shadow_new lyc Sc S2 a).
Proof.
intros n lyc Sc Hpc Wc memc mdc S2 ly S ly' S' Hp' W' mem' md' HC Hly Hfr HAR.
pose proof HC as [Mc _].
pose proof (amc_wf _ _ _ _ _ Mc) as WF.
pose proof (live_slots_placed_of_wf_cf lyc Sc (wfc_secondary _ _ _ _ _ WF) (wfc_chunks _ _ _ _ _ WF)) as LP.
destruct Hly as (_ & _ & _ & _ & _ & Fc & _ & _ & _ & _ & _ & _ & _ & Xc & _).
split; [|split; [|split; [|split]]].
- intros a Ha Hd. pose proof (dead_shadow_new_below_ceiling lyc Sc S2 a Hd). lia.
- intros p n' i Hin Hi. pose proof (alx_blocks segs B ARx LAWS ly' S' Hp' W' mem' md' p n' HAR Hin) as (_ & _ & _ & IA & _).
  apply dead_shadow_new_app. exact (in_app_addr p (req_size n') (p + i) IA ltac:(lia)).
- intros a Hi Hd. pose proof (segs_low a Hi). pose proof (dead_shadow_new_not_low lyc Sc S2 a Hd). lia.
- intros cid pos a Hin Hr. pose proof (Hfr _ Hin) as Hin'.
  pose proof (frame_facts_cf B lyc Sc Hpc _ cid pos Mc Hin') as (C1 & C2 & [IA1 IA2] & _ & PA & A1 & A2 & A3 & A4 & A5 & _).
  rewrite Fc in IA1, IA2, PA. change (2 ^ 20) with 1048576 in A1. unfold YG0f.page_aligned in PA.
  unfold in_zr, YCbq.frame_rng in Hr. cbn [fst snd] in Hr. unfold frame_addr in *.
  destruct Hr as [Hr | Hr].
  + apply dead_shadow_new_app. apply (in_app_addr (ly_F ly) kFakeStackSize a (conj IA1 IA2)).
    unfold kFakeFramesOff in *. lia.
  + assert (O0 : 0 <= fs_frame_off cid pos) by (unfold kFakeFramesOff in A1; lia).
    assert (M8 : (ly_F ly + fs_frame_off cid pos) mod 8 = 0).
    { apply Z.mod_divide in PA as [q1 E1]; [|lia]. apply Z.mod_divide in A3 as [q2 E2]; [|lia].
      rewrite E1, E2. replace (q1 * 4096 + q2 * 64) with ((q1 * 512 + q2 * 8) * 8) by lia.
      apply Z.mod_mul. lia. }
    apply (dsn_frame_shadow_off lyc Sc S2 (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) a
      (amc_placed _ _ _ _ _ Mc) LP).
    * rewrite Fc. lia.
    * rewrite Fc. lia.
    * exact M8.
    * lia.
    * lia.
    * exact Hr.
- intros a HX. rewrite <- Xc in HX.
  pose proof (YGcfExtra.ARx_extra_law_ok_ARcf segs B lyc Sc Hpc Wc memc mdc a HC HX) as (_ & _ & _ & _ & _ & _ & APP).
  apply dead_shadow_new_app. exact APP.
Qed.
End off.

Section postj.
Context {SK : YI16.sink_head}.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARxs HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : YCbq.api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law segs B ARxs.

Lemma POST_J_cf : apost_j_law (SK := SK) segs B ARxs (wle' segs RZ_cf) APOST_cf.
Proof.
intros lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 regs2 mem2 md2 Eb XW FP1 k1 WS
  ((HAR2 & Hly2 & Hwin & _ & Hio2 & Hfr & Hpres2) & HX2) HAR Hstk Hfrs Hnev Hk1 Hsecs XWP HE Hgone HQT2 HW.
assert (HARx2 : ARxs ly2 S2 Hp2 W2 mem2 md2) by exact (conj HAR2 HX2).
exact (call_effect_journal_xwR (SK := SK) segs B ARxs LAWS segs_low errno_low OWNLOW (wle' segs RZ_cf)
  (dead_shadow_new lyc Sc S2) ASTACK lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 Eb XW FP1 [] k1 WS HARx2 Hly2
  (wle_in_mono segs _ _ W W2 (dead_shadow_new_RZ lyc Sc S2) Hwin) Hio2 Hfr Hpres2 HAR Hstk Hfrs Hnev Hk1 Hsecs XWP HE
  Hgone HQT2 HW
  (ajournal_x_of_rh_off ARxs LAWS segs_low (length (st_secs Sc)) lyc Sc Hpc W memc mdc S2 lyc Sc ly2 S2 Hp2 W2 mem2 md2
     (proj1 HAR) (layout_le_refl _ _) (fun f H => H) HARx2)).
Qed.
End postj.

(* ---------------------------------------------------------------------------- *)
(* The primed free row (YG0dcfR.afree_realizes_cf_rh) as YGcallx's text afree_realizes_xR at R := wle' segs RZ_cf and  *)
(* APOST := APOST_cf (afree_realizes_x_cf_rh). Its leaf has no xs_placed_cf of its own: the post's comes from          *)
(* xs_placed_cf at the call and free_cf's state frame (free_leaf_cf_xA, as free_leaf_cf_xs), carried through the      *)
(* realization by amrealG_ipost (amreal_ipost over amrealG).                                                          *)
Lemma free_leaf_cf_xA : forall ly S Hp W regs mem md ch p n r W' c',
acall_pre_cf segs B ly S Hp W regs mem md ch -> xs_placed_cf ly S -> free_frame_cf S (snd r) ->
free_leaf_cf_rh segs B ly S Hp W regs mem md p n r W' c' -> free_leaf_xA segs B APOST_cf ly S Hp W regs mem md p n r W' c'.
Proof.
intros ly S Hp W regs mem md ch p n r W' c' Hpre HP (FX & FS) (ly' & regs' & mem' & md' & Hc & HPO & HQ).
pose proof HPO as (_ & A2 & _).
pose proof (amc_wf _ _ _ _ _ (proj1 (proj1 Hpre))) as W0. unfold Wf_cf in W0.
pose proof (xs_placed_cf_layout _ _ _ _ ly ly' S W0 A2 HP) as HP'.
assert (HX : xs_placed_cf ly' (snd r)).
{ apply (xs_placed_cf_mono ly' S (snd r)); [exact (FX ly') | intros z Hz; left; exact (FS ly' z Hz) | exact HP']. }
exists ly', regs', mem', md'. exact (conj Hc (conj (conj HPO HX) HQ)).
Qed.

Lemma amrealG_ipost {R} : forall (Rel : world segs -> world segs -> Prop) (t : itree astate R) (P : R -> Prop) W c
(Q : R -> world segs -> config -> Prop),
cfx_ipost t P -> amrealG segs Rel t W c Q -> amrealG segs Rel t W c (fun r W' c' => Q r W' c' /\ P r).
Proof.
intros Rel t. induction t as [r | q s k IH | pc | f]; intros P W c Q HP H; cbn in *.
- eapply (SRrG_mono segs Rel); [exact H | intros W' c' _ H'; exact (conj H' HP)].
- eapply (SRrG_mono segs Rel); [exact H |]. intros W1 c1 _ Hk. destruct q;
try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
split; [exact Hz|]; intros i Hi; apply IH; [apply HP | apply Hc, Hi]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. apply IH; [apply HP | exact Hc].
- exact H.
- exact I.
Qed.

Lemma afree_realizes_x_cf_rh : afree_realizes_cf_rh segs B ->
afree_realizes_xR segs B ARxs QMm_cf free_cf (wle' segs RZ_cf) APOST_cf.
Proof.
intros AF ly S Hp W regs mem md p n ch Hpre H1 H2 H3 H4.
destruct (proj1 (acall_pre_x_xs ly S Hp W regs mem md ch) Hpre) as [Hpc HX].
pose proof (amrealG_ipost (wle' segs RZ_cf) _ _ _ _ _ (cfx_fr_free_cf p (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S)
(AF ly S Hp W regs mem md p n ch Hpc H1 H2 H3 H4)) as HR.
exact (amrealG_mono segs (wle' segs RZ_cf) _ _ _ _ _ (fun r W' c' Hl => free_leaf_cf_xA ly S Hp W regs mem md ch p n r W' c'
Hpc HX (free_frame_cf_of_state S (snd r) (proj1 (proj2 Hl)) (proj2 (proj2 Hl))) (proj1 Hl)) HR).
Qed.

(* ---------------------------------------------------------------------------- *)
(* The call memory's arodata_ok_cf across a walk segment: a journal at any world relation R keeps it. Its image clause *)
(* keeps the view of every image byte outside the owned statics, errno and PST while the footprint opens no sink; each *)
(* aro_addr_cf address lies in a segment (relro_seg_t for the RELRO range, ro_reads_nw_t for cf_ro_reads), which the *)
(* hidden set never meets (w_Hoff), so its view is its raw byte, or the image's byte when the memory holds none.     *)
(* arodata_ok_cf_of_journal_P starts from the walk entry's reader form arodata_okP (fpre's), through               *)
(* YGcfAroBridge.arodata_ok_cf_of_P at the entry.                                                                  *)
Section aro.
Context {SK : YI16.sink_head}.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.

Lemma arodata_ok_cf_of_journal : forall (R : world segs -> world segs -> Prop)
  STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS,
  ajournal_xwR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
  relro_seg_t segs -> errno_relro_t B -> cf_relro_hi <= 2 ^ 64 -> YGcfAroBridge.ro_reads_nw_t segs ->
  (forall a, aro_addr_cf a -> ~ Exists (in_zr a) PST) ->
  ~ YI16.sink_open_fp FP ->
  arodata_ok_cf segs B mem -> arodata_ok_cf segs B mem'.
Proof.
intros R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS HJ RS HE HTOP RONW HPST Hsk AR
  a b Hm Ha HO.
assert (SG : exists sg, In sg segs /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg) /\
  0 <= a < 2 ^ 64 /\ ~ (as_errno B <= a < as_errno B + 4)).
{ destruct RS as [(sg & Hsg & L1 & L2) _]. destruct HE as [HE1 HE2]. destruct Ha as [Ha | Ha].
  - exists sg. split; [exact Hsg | lia].
  - apply Exists_exists in Ha as (r & Hr & Hra). unfold in_zr in Hra.
    unfold YGcfAroBridge.ro_reads_nw_t in RONW. rewrite Forall_forall in RONW, HE2.
    destruct (RONW r Hr) as (T & sg' & Hsg' & _ & L1' & L2').
    pose proof (HE2 r Hr) as E. cbv beta in E. exists sg'. split; [exact Hsg' | lia]. }
destruct SG as (sg & Hin & Hsg & A0 & NE).
assert (Ua : bv_unsigned (Z_to_bv 64 a) = a)
  by (apply Z_to_bv_small; change (bv_modulus 64) with (2 ^ 64); lia).
assert (HN' : w_H W' (Z_to_bv 64 a) = false).
{ destruct (w_H W' (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (w_Hoff W' _ E) as F. rewrite Ua in F.
  exact (find_segment_none_spec segs a 1 F sg Hin ltac:(split; lia)). }
assert (HN : w_H W (Z_to_bv 64 a) = false).
{ destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (w_Hoff W _ E) as F. rewrite Ua in F.
  exact (find_segment_none_spec segs a 1 F sg Hin ltac:(split; lia)). }
assert (HI : in_img segs a) by (exists sg; split; [exact Hin | lia]).
pose proof (ajxR_img HJ a HI HO NE (HPST a Ha) (YCbq.fp_spares_closed FP a Hsk)) as F3.
unfold aview, mbyte, mrestrict in F3. rewrite HN', HN, Hm in F3. cbn [option_map] in F3.
destruct (mem (Z_to_bv 64 a)) as [b0|] eqn:E0.
- cbn [option_map] in F3. injection F3 as F3. rewrite (AR a b0 E0 Ha HO). f_equal. apply bv_eq. symmetry. exact F3.
- destruct (seg_rom segs (Z_to_bv 64 a)) as [b'|] eqn:Er; cbn [option_map] in F3; [|discriminate F3].
  injection F3 as F3. f_equal. apply bv_eq. symmetry. exact F3.
Qed.

Lemma arodata_ok_cf_of_journal_P : forall (R : world segs -> world segs -> Prop)
  STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS,
  ajournal_xwR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
  relro_seg_t segs -> errno_relro_t B -> cf_relro_hi <= 2 ^ 64 -> YGcfAroBridge.ro_reads_nw_t segs ->
  (forall a, aro_addr_cf a -> ~ Exists (in_zr a) PST) ->
  ~ YI16.sink_open_fp FP ->
  PresetRodata.arodata_okP segs cf_relro_lo cf_relro_hi B (aview segs (w_H W) mem) ->
  arodata_ok_cf segs B mem'.
Proof.
intros R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS HJ RS HE HTOP RONW HPST Hsk HP.
exact (arodata_ok_cf_of_journal R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS HJ RS HE HTOP RONW HPST
  Hsk (YGcfAroBridge.arodata_ok_cf_of_P segs B W mem RS HE HTOP RONW HP)).
Qed.
End aro.

End J.
End G.
