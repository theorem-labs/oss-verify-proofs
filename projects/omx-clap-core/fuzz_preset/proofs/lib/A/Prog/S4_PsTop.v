(* fuzz_preset lib/A, slice S4 (parse_string): THE COMPOSITION. The stretches of the walk (each Qed in its own file,
   each ending in the SAME goal ps_post and taking the other cuts as Section hypotheses) are applied to each other
   here, and the composed entry stretch is the KIT TEXT, by S4_PsBase.ps_K0_of_entry.
     entry    S4_PsEntry.ps_entry_holds    (needs scan, ret0)
     scan     S4_PsScan.ps_seg_scan_cnt     (needs ret0, dec; the malloc call's counts, ps_sc_cnt)
     dec      S4_PsDec.ps_seg_dec_holds     (needs retok, free, u)
     free     S4_PsFree.ps_seg_free_cnt     (needs ret0; the free call's count, ps_free_cnt)
     retok    S4_PsRet.ps_retok_walk
     ret0     S4_PsRet.ps_ret0_walk
   THE TOP: ps_K0_of_counts : tparse_string_specX B ARx SK CTX CW, the KIT TEXT of THE KIT'S CUT
   a working branch 7cdbb61b5fa0 (PRH_FnReader.v f1ae32e3b2cd :517-681) itself. The change from
   the earlier statement DRAFT_tparse_string_specX (deleted) was NOT a conversion: the kit's refused arm adds the outcome-exclusion conjunct
   (:624-629) and counts ((cnt + 1) mod 2 ^ 64) (:634-635) where the earlier statement had (cnt + 1); its g_peak and
   g_ran_out are the earlier statement's (fuzz_malloc's prh_alloc_post values). The walk proves both: the exclusion
   from fuzz_malloc's outcome
   clause (S4_PsBase.ps_excl_of_malloc), the mod from prh_alloc_post's refusal arm, which carries it. The text is
   POST-IMPLICATION and BUDGETED at the cursor set CW (prh_cw_ok, the wild room at entry, the post at wbudget CW 0).
   The two live counts at the inner calls are the text's own peak premises (S4_PsBase.ps_cnts), and the room at the
   malloc is the text's per-event live premise at its first event (prh_live_evs, S4_PsBase.ps_live_bb): ps_sc_cnt reads the
   malloc call's off them at the entry state, ps_free_cnt the free call's at the cut (the block list after the malloc,
   Permutation-invariant counts). The position transfer after each allocator call, the callee memnorm keeps and the
   \u stretch are CITATIONS of the kit texts.
   NO NAMED OPEN FACT: the cursor free's admission needs the depot to hold each trace once (a Theorem Labs lane PsRebindA's
   countermodel); it is AR_laws_x's FIELD 25 alx_depot_nodup (in the cut's set: YCbqG.v 219748197d6b, YCbqGwild.v
   0c63874858e4, YGcallcf.v 8645fa6a514f), read off LAWS in S4_PsFree. THE CURSOR SET: the walk consumes prh_cw_ok
   (the text's entry premise, unchanged at the cut); the cut's pin (MIGRATION 26a) is on prh_cw_pj, the caller's side.
   FILE SET (image A' asan 1be0f53d): the cut preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) merged forward into the row's prep head preset-tree-at-2026-10-30T03-26-38Z.tsv (sha256 9eaa45cdfc48; internal record), every
   path but the lane files at the cut's blob (PRW_CallerJ 473f33abadbc, CfParamsPreset b60d0f63c926, PALibA
   88c72c8175cf, PRH_Img 934516a622e8, A' listing PAImg_prog 505a51ff7d08, PRH_FnAlloc 4d8aeba047e5, PRH_Base
   ef7c8ca98529); the lane files relocated from walk-S4 preset-tree-at-2026-10-29T15-36-18Z.tsv (sha256 88f8a644e245; internal record) (alreloc c4338d099cfb8025). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
(* YK06 is NOT imported: its plain constant alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0p YCbqG YGcfNames YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos PresetRoom PresetRun
  PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_HShadow S4_PsBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import
  S4_PsDecKit S4_PsEntry S4_PsRet S4_PsDec S4_PsFree S4_PsScan S4_PsU.
(* the re-hiding move's wle' and its laws (YA0nH) at preset's zone YGcfRehidePost.RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PS_PAImg).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable CTX : list (list Z).
Variable CW : list (list Z).
(* the journal's laws at the second instance's head length (field 14 is the harness-block shadow law) *)
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
(* the program listing's library facts, over the PROGRAM instance *)
Hypothesis TL : @PALib _ A_prog_listing PS_PAImg B.
Hypothesis PST_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
(* The kit's head width (PRH_Base.v prh_head_wide): a Theorem Labs lane's preset_head_wide at the preset instance *)
Hypothesis HW : prh_head_wide.
(* the two allocator callee texts (the kit, PRH_FnAlloc.v) *)
Hypothesis HMALLOC : tfuzz_malloc_specX B ARx SK.
Hypothesis HFREE : tfuzz_free_specX B ARx SK.
(* the two leaf callee texts of the \u stretch (the kit, PRH_FnReader.v) *)
Hypothesis HHEX4 : thex4_specX B ARx SK.
Hypothesis HPUTU : tput_utf8_specX B ARx SK.
(* S4_PsSrc.v's two image facts: the instance's asyms_ok (aso_zshadow) and a Theorem Labs lane's img_shadow_vis_cf *)
Hypothesis ZSA : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0.
Hypothesis IMGV : ARx_img_shadow_vis segs ARx.

(* ---- THE LIVE COUNTS AT THE TWO ALLOCATOR CALLS, from the text's own peak premises (S4_PsBase.ps_cnts: the counts at
   every state along the all-granted events prhPs_evs x []). The bridge to the leaves' sec_cnt / ccnt24 is conversion
   (YGcfRoomLive.v: sec_cnt filters rl_sec_req, ccnt24 is PresetRoom.ccnt kBatchClass, both over the block sizes, which
   are YGcfRoom.room_of_cf's rs_live; PresetReqAt.cnt is the length of a filter). ---- *)
(* the malloc call: the entry state is the list's first state (PresetRun.pkR_prefix at 0) *)
Lemma ps_sc_cnt : forall D, ps_pre B ARx CTX CW D -> sc_cnt D.
Proof.
intros D HPRE. destruct (ps_cnts_of_pre B ARx CTX CW D HPRE) as [HSEC H24].
pose proof (PresetRun.pkR_prefix YGcfRoomLive.rl_sec_req (prhPs_evs (ps_x D) [])
  (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D))) 0) as P1.
pose proof (PresetRun.pkR_prefix (PresetRoom.in_cls YG00.kBatchClass) (prhPs_evs (ps_x D) [])
  (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D))) 0) as P2.
cbn [firstn] in P1, P2. rewrite PresetReqAt.hlive_from_nil in P1, P2.
unfold sc_cnt.
change (YGcfRoomLive.sec_cnt (pi_S D)) with
  (Z.of_nat (PresetReqAt.cnt YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D))))).
change (YGcfRoomLive.ccnt24 (pi_S D)) with
  (Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D))))).
split; lia.
Qed.
(* the free call (the bad escape): its state is the list's second state, the entry's live requests and the malloc's
   block (pkR_prefix at 1; the cut's ablocks append gives the live requests up to Permutation, ps_live_app) *)
Lemma ps_free_cnt : forall (P : (word -> option byte) -> Prop) D ly S Hp W regs mem md out Q,
  ps_pre B ARx CTX CW D -> ps_at_freeP B ARx SK P D ly S Hp W regs mem md out Q ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros P D ly S Hp W regs mem md out Q HPRE (_ & HAL & _ & _ & _ & HSC & HDN & _).
destruct HAL as (_ & _ & _ & _ & Eab & _).
destruct (ps_cnts_of_pre B ARx CTX CW D HPRE) as [_ H24].
pose proof (PresetRun.pkR_prefix (PresetRoom.in_cls YG00.kBatchClass) (prhPs_evs (ps_x D) [])
  (PresetRoom.rs_live (YGcfRoom.room_of_cf (pi_S D))) 1) as P2.
assert (Hev : prhPs_evs (ps_x D) [] =
  [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head); PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head)])
  by (unfold prhPs_evs; rewrite HSC, HDN; reflexivity).
rewrite Hev in P2, H24. cbn [firstn] in P2.
unfold PresetReqAt.hlive_from in P2. cbn [fold_left PresetReqAt.hstep] in P2.
pose proof (ps_live_app B D ly S _ _ Eab) as HL. unfold ps_live in HL.
unfold PresetReqAt.hlive_from in HL. cbn [fold_left PresetReqAt.hstep] in HL.
rewrite <- (ps_cnt_perm (PresetRoom.in_cls YG00.kBatchClass) _ _ HL) in P2.
change (YGcfRoomLive.ccnt24 S) with
  (Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S)))).
lia.
Qed.

(* ==== THE WALK OVER A GENERIC INVARIANT P (a Theorem Labs lane 12:18Z / 12:22Z): parse_string's whole body, composed from
   its Qed generic-P stretches. P crosses the four kit calls by srr_inv_call. ==== *)
Section topP.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
Hypothesis PCALL : srr_inv_call segs P.
Theorem ps_entryP_of_counts : ps_seg_entryP B ARx SK P CTX CW.
Proof.
pose proof (ps_ret0_walkP B ARx SK CTX CW LAWS P PLAW) as HRET0.
(* the NULL return after the bad escape's fuzz_free: the ret0 stretch over the relation wle' segs RZ_cf *)
pose proof (ps_ret0_walkPR B ARx SK CTX CW LAWS P PLAW (wle' segs YGcfRehidePost.RZ_cf)
  (wle'_refl segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf) (wle_wle' segs YGcfRehidePost.RZ_cf))
  as HRET0R.
pose proof (ps_retok_walkP B ARx SK CTX CW LAWS P PLAW PST_ok HW) as HRETOK.
assert (HFREEC : ps_seg_freeP B ARx SK P CTX CW).
{ intros D ly S Hp W regs mem md out Q HPRE HAT.
  exact (ps_seg_free_cntP B ARx SK CTX CW LAWS HFREE ZSA IMGV P PLAW PCALL HRET0R
           D ly S Hp W regs mem md out Q HPRE HAT (ps_free_cnt P D ly S Hp W regs mem md out Q HPRE HAT)). }
pose proof (ps_u_segP B ARx SK CTX CW LAWS P PLAW PCALL HW PST_ok ZSA IMGV HHEX4 HPUTU HFREEC) as HU.
pose proof (ps_seg_dec_holdsP B ARx SK P CTX CW LAWS HW PST_ok PLAW HRETOK HFREEC HU) as HDEC.
assert (HSCAN : ps_seg_scanP B ARx SK P CTX CW).
{ intros D ly S Hp W regs mem md x HPRE HAT.
  exact (ps_seg_scan_cntP B ARx SK LAWS TL PST_ok HMALLOC CTX CW ZSA IMGV P PLAW PCALL HRET0 HDEC
           D HPRE (ps_sc_cnt D HPRE) ly S Hp W regs mem md x HAT). }
exact (ps_entry_holdsP B ARx SK CTX CW LAWS TL P PLAW HSCAN HRET0).
Qed.
End topP.

(* ---- THE INSTANCE, P := ps_mn D: the kit text (the kit's cut 7cdbb61b5fa0, PRH_FnReader f1ae32e3b2cd) is m-form and
   budgeted, fpostWbm .. (wbudget CW 0) .. (fQmn mem Q), and ps_postP (ps_mn D) CW D IS that post
   (S4_PsBase.ps_postm_is_K0). THE TOP: the KIT TEXT itself; its premises beyond the text are the Section hypotheses
   (the callee texts and the image facts; no named open fact). ---- *)
Theorem ps_K0_of_counts : tparse_string_specX B ARx SK CTX CW.
Proof.
apply ps_K0_of_entry. intros D HPRE.
exact (ps_entryP_of_counts (ps_mn D) (ps_mn_laws D) (ps_mn_call D) D HPRE (ps_mn_entry D)).
Qed.
End top.
