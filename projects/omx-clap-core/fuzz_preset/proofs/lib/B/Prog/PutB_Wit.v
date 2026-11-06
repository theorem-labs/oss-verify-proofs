(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (asan-ubsan #102 pin d663f82d7f48, twin c90d4fa54d43), the walk of put:
   the WITNESSES of the image premises of the walk's premise bundle putb_env
   (lib/B/Prog/PutB_Base.v :162-204), at the B' instance. Proves no function (rule 24 is PutB_Base.v's: put).
   Each lemma putb_wit_<field> states that field's type at the instance, verbatim from the Record with the Section
   variables instantiated; putb_wit_env assembles the Record (mkPutBEnv, every instance argument named) from them and
   the two premises that are not image facts (pe_real: the callee text tfuzz_realloc_specX; pe_amc: the runtime row of
   __asan_memcpy), so the build checks that every statement here is the field's own type. The file ends with the
   Print Assumptions of each lemma.
   INSTANCE (the internal file bprime-pivot.md item 6):
     PA  := PAImg_prog.PI_prog_B (the B' whole-program listing, lib/B/PAImg_prog.v :404-408),
     B   := YD2l.TfibB (lib/Reusable/YD2l.v :13-36),
     ARx := ARcfx = fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S, the B' walks'
            relation (lib/B/Prog/FuzzFreeB.v :296, OwnB.v :186; YGcallcf.v :214 ARxs, whose laws are
            YGcallcf.AR_laws_x_xs :242). ARcfx, not ARcf: its laws lemma exists (AR_laws_x_xs), it is the relation
            the callee texts are proved at (fuzz_free / own / fuzz_realloc B'), and every field below holds at it
            (each ARcf fact is read through the first conjunct).
     cp  := CfParamsPreset.CfParams_preset, RL := PRH_Base.prh_room_live_a8, ci := CfImgB.CfImg_B (lib/AU/CfImgB.v);
     fx, rc, SK stay generic (the walk's Section variables; no field fixes them).
   WHAT EACH LEMMA CITES:
     pe_laws  YGcallcf.AR_laws_x_xs over YG0lawscf.AR_laws_ok_cf (PALibB.exvi_eh_laws is the same at plain ARcf).
     pe_tl    PALibB.exvi_eh_palib.
     pe_ent   vm_compute over PI_prog_B's sigma and PutB_Base.PUT_K.
     pe_obj   S1ImgCheck.in_img_b / pst_allb (image-free checkers) by vm_compute over the two 8-byte objects.
     pe_imgsh YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover at B's lists YF0m.Tfib_zero_shadow / Tfib_const_shadow
              (as_zero_shadow TfibB and a tail of as_const TfibB ly), read at ARcf (first conjunct of ARcfx); its cover
              check putb_wit_imgsh_cover by vm_compute at PI_prog_B's pa_lo / pa_hi (= YImgTop.IMG_LO_B / IMG_TOP_B).
     pe_frsh  YGcfFsVis.ARx_frame_hull_vis_cf_ok (at ARcf, first conjunct).
     pe_pst   S1ImgB.pst_in_img_B.
     pe_hw    CfParamsPreset.preset_head_wide (= PALibB.exvi_eh_head).
     pe_pstro S1ImgB.pst_not_ro_B (PI_prog_B's relro range is B_prog_relro_lo / B_prog_relro_hi).
     pe_zsa   vm_compute over as_zero_shadow TfibB.
     pe_cnt   PresetRoomCounts.counts_of_room_pos_rl (the interface at lib/Spec/PresetRoomCounts.v blob 8a4dfa84e8be: moved
              verbatim from lib/AU/PresetCfnB.v into the image-free leaf lib/Spec/PresetRoomCounts.v :54).
     pe_fcid  YG0scf.frame_facts_cf (ARmcf's frame table: 0 <= cid <= 10), at ARcf's ARmcf.
     pe_hull  PresetHullPay.hull_budget_of_room_pos with hull_nt_one_mal / hull_nt_one_re (the hull budget of the one
              fuzz_realloc call from put's run position; the request is below cf_malloc_max = 2 ^ 28 + 2 ^ 27 at
              CfParams_preset, inside the one-call bound 2 ^ 30).
   Numerals: 8 (LENGTH: a word; the alignment of a shadow granule), 0 / 12 (the Record's listing object indices);
   2 ^ 28 + 2 ^ 27 (DERIVED: CfParams_preset's cf_malloc_max), 2 ^ 30 (DERIVED: PresetHullPay's one-call request bound).
   No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC81.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop YK1g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YGcallMx YSRrMemnorm YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YG0dcf YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PresetRoomPos PresetLiveBounds PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterSpecFacts WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PutB_Kit PutB_Base.
(* the instance and the cited witnesses: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0lawscf YGcallcf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgShadowCover YImgShadowCoverCf YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomCounts PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require S1ImgB.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {ci : CfImg}.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance PRH_Base.prh_room_live_a8.
#[local] Abbreviation PA := (@PI_prog_B rc).
#[local] Abbreviation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val rc B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val rc B_prog_listing PA A_TEXT).
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
(* the B' walks' allocator relation (FuzzFreeB.v :296; YGcallcf.v :214 ARxs) *)
#[local] Abbreviation ARcfx :=
  (fun ly S Hp (W : world SEGS) mem md => YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

(* pe_laws *)
Lemma putb_wit_pe_laws : AR_laws_x SEGS TB ARcfx (@cf_head CP).
Proof. exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)). Qed.

(* pe_tl *)
Lemma putb_wit_pe_tl : PALib (L := B_prog_listing) (PI := PA) TB.
Proof. exact PALibB.exvi_eh_palib. Qed.

(* pe_ent *)
Lemma putb_wit_pe_ent : SIGMA AS_put = BASE + PUT_K.
Proof. vm_compute. reflexivity. Qed.

(* pe_obj *)
Lemma putb_wit_pe_obj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
Proof.
assert (C : S1ImgCheck.pst_allb (S1ImgCheck.in_img_b SEGS) [(VAL (A_OBJ 0), 8); (VAL (A_OBJ 12), 8)] = true)
  by (vm_compute; reflexivity).
intros i Hi. split; apply S1ImgCheck.in_img_b_sound; apply (S1ImgCheck.pst_allb_sound _ _ _ C).
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. clear - Hi; lia.
- apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. clear - Hi; lia.
Qed.

(* pe_imgsh: the cover check of B's own lists at PI_prog_B's image bounds *)
Lemma putb_wit_imgsh_cover :
  YImgShadowCover.img_shadow_cover YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow
    (@pa_lo rc B_prog_listing PA) (@pa_hi rc B_prog_listing PA) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma putb_wit_pe_imgsh : ARx_img_shadow_vis_r SEGS ARcfx (@pa_lo rc B_prog_listing PA) (@pa_hi rc B_prog_listing PA).
Proof.
intros ly S Hp W mem md a [HA _] Ha.
refine (YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover SEGS TB YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow
  (@pa_lo rc B_prog_listing PA) (@pa_hi rc B_prog_listing PA) putb_wit_imgsh_cover _ _ ly S Hp W mem md a HA Ha).
- exact (List.incl_refl YF0m.Tfib_zero_shadow).
- intros ly0. change (as_const TB ly0) with (YF0m.Tfib_const ly0). unfold YF0m.Tfib_const.
  apply List.incl_appr, List.incl_appr, List.incl_refl.
Qed.

(* pe_frsh *)
Lemma putb_wit_pe_frsh : ARx_frame_hull_vis SEGS ARcfx.
Proof.
intros ly S Hp W mem md cid pos [HA _] Hin.
exact (YGcfFsVis.ARx_frame_hull_vis_cf_ok SEGS TB (YG0lawscf.AR_laws_ok_cf SEGS TB) ly S Hp W mem md cid pos HA Hin).
Qed.

(* pe_pst *)
Lemma putb_wit_pe_pst : forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> in_img SEGS a.
Proof. exact S1ImgB.pst_in_img_B. Qed.

(* pe_hw *)
Lemma putb_wit_pe_hw : prh_head_wide (cp := CP).
Proof. exact CfParamsPreset.preset_head_wide. Qed.

(* pe_pstro *)
Lemma putb_wit_pe_pstro : forall a,
  in_roP SEGS (@pa_relro_lo rc B_prog_listing PA) (@pa_relro_hi rc B_prog_listing PA) a ->
  ~ Exists (in_zr a) (@prh_pst prh_img_B).
Proof. intros a Hro Hx. exact (S1ImgB.pst_not_ro_B a Hx Hro). Qed.

(* pe_zsa *)
Lemma putb_wit_pe_zsa : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow TB).
Proof.
assert (C : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) (as_zero_shadow TB) = true)
  by (vm_compute; reflexivity).
apply List.Forall_forall. intros r Hr. pose proof (proj1 (List.forallb_forall _ _) C r Hr) as Hb. cbv beta in Hb.
apply andb_prop in Hb as [H1 H2]. split; apply Z.eqb_eq; assumption.
Qed.

(* pe_cnt *)
Lemma putb_wit_pe_cnt : forall sm x os i H0 hist S, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof. exact PresetRoomCounts.counts_of_room_pos_rl. Qed.

(* pe_fcid *)
Lemma putb_wit_pe_fcid : forall ly S Hp (W : world SEGS) mem md cid pos, ARcfx ly S Hp W mem md ->
  In (cid, pos) (frames S) -> 0 <= cid.
Proof.
intros ly S Hp W mem md cid pos [(M & _) _] Hin.
exact (proj1 (proj1 (YG0scf.frame_facts_cf TB ly S Hp _ cid pos M Hin))).
Qed.

(* pe_hull: room for one call's event of a request below cf_malloc_max, at a position of a run of at most 4 calls *)
Lemma putb_wit_pe_hull : forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
    (i : nat) (H0 : list Z) (hist : list YG00.chunk) S m r,
  (length os <= 4)%nat -> PresetRoomPos.iface_room_pos sm x os i H0 hist S -> 0 <= r < cf_malloc_max ->
  PresetHullBudget.hull_budget S [PresetReqAt.HMal r] /\ PresetHullBudget.hull_budget S [PresetReqAt.HRe m r].
Proof.
intros sm x os i H0 hist S m r Hl HP Hr.
assert (Hr30 : 0 <= r <= 2 ^ 30) by (change (@cf_malloc_max CP) with (2 ^ 28 + 2 ^ 27) in Hr; lia).
destruct (PresetHullPay.hull_nt_one_mal r Hr30) as (N1 & T1).
destruct (PresetHullPay.hull_nt_one_re m r Hr30) as (N2 & T2).
split; [exact (PresetHullPay.hull_budget_of_room_pos sm x os i H0 hist S _ Hl HP N1 T1)
       | exact (PresetHullPay.hull_budget_of_room_pos sm x os i H0 hist S _ Hl HP N2 T2)].
Qed.

(* the Record from the witnesses and the two premises that are not image facts: the build checks that each
   statement above is its field's type at the instance *)
Lemma putb_wit_env :
  tfuzz_realloc_specX (ci := CfImgB.CfImg_B) (cp := CP) (RL := @PRH_Base.prh_room_live_a8 CP) (PI := prh_img_B)
    (L := B_prog_listing) (PA := PA) TB ARcfx SK ->
  YGcallMxmn.aintrin_realizes_xm SEGS TB ARcfx OCpy (SIGMA AS___asan_memcpy) ->
  putb_env (fx := fx) (rc := rc) (ci := CfImgB.CfImg_B) (cp := CP) (RL := @PRH_Base.prh_room_live_a8 CP) (SK := SK)
    (PA := PA) TB ARcfx.
Proof.
intros REAL AMC. constructor.
- exact putb_wit_pe_laws.
- exact putb_wit_pe_tl.
- exact putb_wit_pe_ent.
- exact putb_wit_pe_obj.
- exact REAL.
- exact putb_wit_pe_hull.
- exact AMC.
- exact putb_wit_pe_imgsh.
- exact putb_wit_pe_frsh.
- exact putb_wit_pe_pst.
- exact putb_wit_pe_hw.
- exact putb_wit_pe_pstro.
- exact putb_wit_pe_zsa.
- exact putb_wit_pe_cnt.
- exact putb_wit_pe_fcid.
Qed.
End w.

Print Assumptions putb_wit_pe_laws.
Print Assumptions putb_wit_pe_tl.
Print Assumptions putb_wit_pe_ent.
Print Assumptions putb_wit_pe_obj.
Print Assumptions putb_wit_imgsh_cover.
Print Assumptions putb_wit_pe_imgsh.
Print Assumptions putb_wit_pe_frsh.
Print Assumptions putb_wit_pe_pst.
Print Assumptions putb_wit_pe_hw.
Print Assumptions putb_wit_pe_pstro.
Print Assumptions putb_wit_pe_zsa.
Print Assumptions putb_wit_pe_cnt.
Print Assumptions putb_wit_pe_hull.
Print Assumptions putb_wit_pe_fcid.
Print Assumptions putb_wit_env.
