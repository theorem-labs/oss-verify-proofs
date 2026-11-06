(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* CARRIED from this tree's proofs/plugin-hostd/fuzz_reply/lib/Reusable/YGcallcf.v, sha256 8f47cfc3ee075a764e7d26f11827e5856db5a6fa1b6cb7ce9bd5351f7c74f908
   (that file is carried from commit a0fed4266a1b18b1453af093bfe2ee477dcbe241, proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallcf.v).
   Re-pointed for lib/B (fuzz_reply.asan-ubsan): each Require of a module that lib/B instantiates now names lib/B's
   module (lib/B/YCbqG.v, this carry's own lib/B copy; lib/B/YGcallx.v, this carry's own lib/B copy).
   The exact changes (`lib.` is OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.; each source line is replaced
   by the lines after `->`, in that order):
   - line 42: `From lib.Reusable Require Import YCbqG YGcallx.` -> `From lib.B Require Import YCbqG YGcallx.`
   Nothing else changes: below this comment the bytes are the source's.
   DO NOT EDIT: change the source file on its branch, carry it again, and re-point it again. *)
(* CARRIED from commit a0fed4266a1b18b1453af093bfe2ee477dcbe241,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallcf.v, sha256 f26843de34bf8209d3b0733f995d869c8436f477f7f80e8473ab8926ba82e675.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib. *)
(* Modified by Theorem Labs, 2026-10-30 (a Theorem Labs lane, round 6g; a Theorem Labs lane's approval (B'')): the cf forms are YGcallx's at
   QMm := QMm_cf, acall_pre_cf's trailing conjuncts verbatim (since the cf layer's field round 3 they end with
   cf_hull_ok S /\ arodata_ok_cf segs B mem; part 3c: no memnorm), so acall_pre_cf_x / afree_realizes_cf_x stay BY
   REFLEXIVITY; QM := QM_cf, their STATE part (the new FA_GROW headroom + FA_GROW_MAX / 8, and cf_hull_ok), for the model
   laws; QMQ_cf (QMm_cf S mem -> QM_cf S) is a projection. QM_cf_of_room takes cf_hull_ok, as the layer's
   acall_pre_cf_intro does (abudget_room_cf and mroom_cf_of_live need it); QMm_cf_of_room adds the two memory facts. *)
(* Theorem Labs, 2026-10: the cf BRIDGE. Each call form of the second allocator instance (YG0dcf.v) IS the generic
   form of YGcallx.v at
     ARx  := fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md,
     QMm  := QMm_cf below, acall_pre_cf's trailing conjuncts (qmeter_cf, the live-secondary bound, ERRB_ROOM, the
             free-array headroom, batch_room_cf, cf_hull_ok and arodata_ok_cf on the call memory), in their
             order; QM := QM_cf, the same without the two memory facts (the model laws' state predicate),
     mt   := malloc_cf, nmax := cf_malloc_max, ft := free_cf, WFx := Wf_cf (as_universe B), XS := xs_cf (YG0ncf.v).
   The equations below hold by unfolding (reflexivity) where the cf form has no extra conjunct; malloc_leaf_cf ends
   with `xs_placed_cf ly' (snd r)` (YG0dcf.v), so the malloc forms are related at the relation ARcf /\ xs_placed_cf
   (malloc_leaf_cf_xs, an iff), not at plain ARcf.
   The laws: AR_laws_x at ARcf (hl := cf_head) follows from AR_laws_cf alone (AR_laws_x_cf): the one law AR_laws_cf
   lacks, the extra-area law, is h-mani-a8's YGcfExtra.ARx_extra_law_ok_ARcf (cgif's AR_extra_law_ok, YG0p.v:39, over
   ARcf); the harness-block shadow law (field 14) is h-mani-a8's YGcfHeadSh.ARx_hshadow_law_cf_ok at cf_head; the
   tail-granule law (field 15) is h-mani-a8's YGcfTail.amalloc_tail_vis_end_cf; the const cells (field 16) are
   ARmcf's amc_const (YG0ncf.v); the image law (field 17) is ALedger_cf's alc_img and, for the frames, frame_facts_cf
   with layout_ok's lo_img; the layout law (field 18) is ARmcf's amc_layout. ARx_owned_low_law is AR_laws_cf's
   alc_owned_low; ARx_wf_law is ARmcf's amc_wf.
   The model laws: alloc_model_laws_x at cf follows from universe_ok (as_universe B) by YG0ucf.v's model_laws_cf_ok
   (alloc_model_laws_x_cf). YGcfAmx.v's amx_malloc_cf / amx_free_cf are not used: their posts bound st_nev from
   ABOVE only, and the rules' journal count k + (st_nev S2 - st_nev Sc) needs the lower bound malloc_post_cf /
   free_post_ycf give (st_nev s + 1 <= st_nev s', resp. =).
   The room: QM_cf follows from ARcf, qtight, ROOM_cf and cf_hull_ok (QM_cf_of_room, YGcfRoomPre.v's ingredients);
   QMm_cf adds arodata_ok_cf on the call memory (QMm_cf_of_room).
   ecall_pre_cf_x targets the frame-class lane's ecall_pre_x (FCiface.v).
   Uses the shared cf instance classes CfImg / CfParams only; no preset name, no address, no ledger, no numeral. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok YG08cf YGcfRoomPre FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG06bcf YG07cf YG03cf YG0ucf YGcfXs.
(* Required, not Imported: YGcfExtra restates YCbqG's ARx_extra_law under the same name (convertible). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfExtra.
(* Required, not Imported: the cf proofs of AR_laws_x's fields 14 and 15, cited by qualified name. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfHeadSh YGcfTail.
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

(* acall_pre_cf's trailing conjuncts verbatim, the state ones and the read-only one on the call memory (field round 3): the
   generic rules' QMm at cf. *)
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
- (* the frame law: ARcf's own frame law; the kept-bytes premise of YCbqG's law is not needed here (QMm W0) *)
intros ly S Hp W mem md mem' md' HAR H1 H2 H3 H4 H5 H6 _.
exact (alc_frame segs B L ly S Hp W mem md mem' md' HAR H1 H2 H3 H4 H5 H6).
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
(* malloc_post_cf / free_post_ycf imply malloc_post_x / free_post_x. QM_cf carries the fields' room premises.       *)
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

(* QMm_cf adds the call memory's read-only fact (field round 3; part 3c: memnorm is gone). *)
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
- intros ly S Hp W mem md mem' md' [H HP] H1 H2 H3 H4 H5 H6 H7. exact (conj (alx_frame _ _ _ L ly S Hp W mem md mem' md' H H1 H2 H3 H4 H5 H6 H7) HP).
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
Qed.

(* QMm W1 (a Theorem Labs lane, 2026-10-30): the twin of AR_laws_x_and for a MEMORY predicate. The frame law's kept-bytes
   premise (QMm W0', YCbqG.ARx_frame_law) is exactly what a predicate over the image's kept bytes needs, so a
   relation may carry such a predicate and keep every law. The caller gives the keep: Q at mem and the kept bytes
   unchanged give Q at mem'. *)
Lemma AR_laws_x_and_mem : forall {hl : Z} (AR0 : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
(Q : (word -> option byte) -> Prop),
(forall mem mem', Q mem -> (forall a, 0 <= a < 2 ^ 64 -> kept_x segs B a -> mem' (w64 a) = mem (w64 a)) -> Q mem') ->
AR_laws_x segs B AR0 hl -> AR_laws_x segs B (fun ly S Hp W mem md => AR0 ly S Hp W mem md /\ Q mem) hl.
Proof.
intros hl AR0 Q HQ L. constructor.
- intros ly S Hp W mem md p n [H _]. exact (alx_blocks _ _ _ L ly S Hp W mem md p n H).
- intros ly S Hp W mem md mem' md' [H HP] H1 H2 H3 H4 H5 H6 H7.
  exact (conj (alx_frame _ _ _ L ly S Hp W mem md mem' md' H H1 H2 H3 H4 H5 H6 H7) (HQ mem mem' HP H7)).
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
Qed.
(* QMm W1: arodata_ok_cf IS such a predicate. Its bytes are the non-owned RELRO, and the image fact HR says those
   are kept bytes (reply: AF0m.Tfib_kept's first range is [cf_relro_lo, cf_relro_hi); the proof is a vm_compute at
   the instance). So a step that keeps the kept bytes keeps arodata_ok_cf. *)
Lemma arodata_kept :
(forall a, aro_addr_cf a -> ~ Exists (in_zr a) (as_owned_static B) -> 0 <= a < 2 ^ 64 /\ kept_x segs B a) ->
forall mem mem', arodata_ok_cf segs B mem ->
(forall a, 0 <= a < 2 ^ 64 -> kept_x segs B a -> mem' (w64 a) = mem (w64 a)) ->
arodata_ok_cf segs B mem'.
Proof.
intros HR mem mem' HA HK a b Hm Hrel Hno.
destruct (HR a Hrel Hno) as [Hb Hk].
replace (mem' (Z_to_bv 64 a)) with (mem (Z_to_bv 64 a)) in Hm by (symmetry; exact (HK a Hb Hk)).
exact (HA a b Hm Hrel Hno).
Qed.
(* QMm W1: AR_laws_x transports along a pointwise iff of the relation. Used to re-associate the conjuncts that
   AR_laws_x_and_hp and AR_laws_x_and_mem build, so the instance may state its relation in the reading its
   consumers use (`A /\ Hp = [] /\ Q mem`, not `(A /\ Hp = []) /\ Q mem`). *)
Lemma AR_laws_x_iff : forall {hl : Z} (R1 R2 : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop),
(forall ly S Hp W mem md, R1 ly S Hp W mem md <-> R2 ly S Hp W mem md) ->
AR_laws_x segs B R1 hl -> AR_laws_x segs B R2 hl.
Proof.
intros hl R1 R2 E L. constructor.
- intros ly S Hp W mem md p n H. exact (alx_blocks _ _ _ L ly S Hp W mem md p n (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md mem' md' H H1 H2 H3 H4 H5 H6 H7.
  apply (proj1 (E _ _ _ _ _ _)).
  exact (alx_frame _ _ _ L ly S Hp W mem md mem' md' (proj2 (E _ _ _ _ _ _) H) H1 H2 H3 H4 H5 H6 H7).
- intros ly S Hp W mem md cid pos H. exact (alx_frames _ _ _ L ly S Hp W mem md cid pos (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md a H. exact (alx_stack _ _ _ L ly S Hp W mem md a (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md a H. exact (alx_owned_image _ _ _ L ly S Hp W mem md a (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md H. exact (alx_sep _ _ _ L ly S Hp W mem md (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md ly' H. exact (alx_layout _ _ _ L ly S Hp W mem md ly' (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md a H. exact (alx_client_img _ _ _ L ly S Hp W mem md a (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md a H. exact (alx_extra _ _ _ L ly S Hp W mem md a (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md H. exact (alx_const _ _ _ L ly S Hp W mem md (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md p n H. exact (alx_shadow _ _ _ L ly S Hp W mem md p n (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md r H. exact (alx_zshadow _ _ _ L ly S Hp W mem md r (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md a H. exact (alx_zshadow_byte _ _ _ L ly S Hp W mem md a (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md b n H. exact (alx_hshadow _ _ _ L ly S Hp W mem md b n (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md p n a H. exact (alx_blocks_tail _ _ _ L ly S Hp W mem md p n a (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md H. exact (alx_const_cells _ _ _ L ly S Hp W mem md (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md H. exact (alx_img _ _ _ L ly S Hp W mem md (proj2 (E _ _ _ _ _ _) H)).
- intros ly S Hp W mem md H. exact (alx_layout_ok _ _ _ L ly S Hp W mem md (proj2 (E _ _ _ _ _ _) H)).
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

End J.
End G.
