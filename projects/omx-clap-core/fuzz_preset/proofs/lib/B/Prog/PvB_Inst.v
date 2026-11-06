(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (asan-ubsan #102 pin d663f82d7f48, unstripped twin c90d4fa54d43),
   parse_value 0x8637c: the walk AT THE INSTANCE. Segments A (PvB_A.v pvA_holds), D (PvB_D.v
   pvD_holds), N (PvB_N.v pvN_seg), X (PvB_X.v pvX_holds) and the composition (PvB_Top.v pvTop_compose, the record
   text tparse_value_specX d CTX CTX0 CW in the POST-IMPLICATION form, lib/A/PRH_FnParse.v:274, of this tree's
   kit) are proved generic in (fx0 rc ci cp RL SK PA B ARx) with Section hypotheses; here every
   closed image fact and every instance law among those hypotheses is DISCHARGED at the instance:
     B := TfibB (lib/Reusable/YD2l.v 95803a8b9493, TfibB'), PA := PI_prog_B (lib/B/Listing_prog.v c97cc46b3e13,
     lib/B/PAImg_prog.v 15fab93fe702), ARx := ARcfx = (ARcf rsegs TfibB /\ xs_placed_cf) (lib/Reusable/YG0ncf.v;
     YGcallcf.v ARxs), RL := prh_room_live_a8 (lib/A/PRH_Base.v), ci := CfImg_B (lib/AU/CfImgB.v),
     cp := CfParams_preset (lib/A/CfParamsPreset.v);
   PAL by citation of lib/B/PALibB.v (5baa19c890f7) exvi_eh_palib; the laws at ARcfx are YGcallcf.v AR_laws_x_xs of
   YG0lawscf.v AR_laws_ok_cf, whose ARcf half is PALibB.exvi_eh_laws (cited where an ARcf law is read: pvI_hzs,
   pvI_fs_hi, PvB_ImgFacts.pvi_litcs). fx0, rc, SK stay parameters. Every image premise is re-witnessed at B' by
   vm_compute over the closed record (image bounds YImgTop.IMG_LO_B / IMG_TOP_B, never image A's).
   What stays a Section hypothesis here is a callee's text, each with its owner: TLIT / TPSTR / FMALLOC (the literal /
   literal / parse_string / fuzz_malloc texts at the batch kit's tip 240b06ed4fd4, at ARcfx); parse_items' text is the PREMISE
   at ARcfx); parse_items' text is the PREMISE of pvInst_step_PV at one depth (the pair's step, closed by lib/A/VrdUnit.v);
   ASM0 (frame class 0's contract in the engine's m-form at ARcf, YGcallMxmn.astack_malloc_realizes_xm, lifted here to ARcfx by
   astack_malloc_realizes_xm_conj) and CPY (__asan_memcpy's row in the m-form at ARcf, YGcallMxmn.aintrin_realizes_xm,
   lifted by aintrin_realizes_xm_conj). The f97c-era interim premises K0_OKS_REFUSAL_RAN / _PEAK are gone: the batch kit's
   re-keyed prh_oks and prh_refused_peak close the number arm's refusal (PvB_NQ.v). skip_ws's text is the proved
   lib/B/Prog/skip_ws_mn.v skip_ws_holds at ARcfx (pvI_skipws). strtod's row is the proved
   lib/B/Prog/strtod_row.v strtod_row_B (765c9aac6416) with strtod_row_sat.v (d7092e38f1c7) strtod_sat_tp_B /
   strtod_sat_errno_B / strtod_sat_owned_B.
   Rule 24: proves no function (kind: instance discharge). Numerals: 0, 10, 12, 64 are LENGTH / class numbers of the
   hypothesis texts; 169 is the index of the strtod guard's GOT cell in B' YF0m.v Tfib_const_abs (YF0m.v:202 = 33 +
   169); no address is written (every image value is computed by vm_compute on the closed record). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_D_Call.
(* the segments and the composition: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_A PvB_D PvB_N PvB_X PvB_Top.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_A_Home PvB_ND strtod_c strtod_row strtod_row_sat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require skip_ws_mn PvB_NCut.
(* the instance and its proved facts: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0scf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallScf YImgShadowCover YImgShadowCoverCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require S1ImgB PvB_ImgFacts.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

(* lib/B/Prog/strtod_c.v / strtod_row.v / strtod_row_sat.v (image B's strtod constants and row), by full name *)
#[local] Abbreviation STRTOD_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_c.STRTOD.
#[local] Abbreviation STRTOD_ERRNO_B :=
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_c.STRTOD_ERRNO.
#[local] Abbreviation STRTOD_GOT_GUARD_B :=
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_c.STRTOD_GOT_GUARD.
#[local] Abbreviation STRTOD_GUARD_B :=
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_c.STRTOD_GUARD.
#[local] Abbreviation strtod_model_B :=
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_c.strtod_model.
#[local] Abbreviation strtod_img_B :=
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_row.strtod_img_B.

(* [lo, hi) is covered by the segments, decided by a cursor that jumps to the end of a segment holding it (one step
   per segment is enough) *)
Fixpoint pvI_cov (segs : list Segment) (k : nat) (lo hi : Z) : bool :=
  match k with
  | O => hi <=? lo
  | S k' => ((hi <=? lo) || existsb (fun s => (Z.of_N (seg_base s) <=? lo) &&
      (lo <? Z.of_N (seg_base s) + Z.of_N (seg_size s)) &&
      pvI_cov segs k' (Z.of_N (seg_base s) + Z.of_N (seg_size s)) hi) segs)%bool
  end.

Lemma pvI_cov_sound : forall segs k lo hi, pvI_cov segs k lo hi = true -> forall a, lo <= a < hi -> in_img segs a.
Proof.
intros segs k. induction k as [|k IH]; intros lo hi H a Ha; cbn [pvI_cov] in H.
- apply Z.leb_le in H. clear - H Ha; lia.
- apply orb_true_iff in H as [H|H]; [apply Z.leb_le in H; clear - H Ha; lia|].
  apply existsb_exists in H as (s & Hs & H). apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct (Z_lt_le_dec a (Z.of_N (seg_base s) + Z.of_N (seg_size s))) as [L|L].
  + unfold in_img. exists s. split; [exact Hs | clear - H1 L Ha; lia].
  + exact (IH _ hi H3 a ltac:(clear - L Ha; lia)).
Qed.

Section i. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance prh_room_live_a8.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PI_prog_B).
#[local] Abbreviation PSTX := (@prh_pst prh_img_B).
(* the allocator relation ARcf, and the relation ARcfx: ARcf with the error-buffer extents placed
   (YGcallcf.v ARxs) *)
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) rsegs TB).
#[local] Abbreviation ARIX := (fun ly S Hp (W : world SEGS) mem md =>
  YG0ncf.ARcf (cp := CP) rsegs TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

(* ---- (a) the KEPT hypotheses: callee texts, the kit's at the batch kit's tip 240b06ed4fd4
   (PRH_FnReader.v 9f0031c87f00, PRH_FnParse.v ed236011cf99, PRH_FnAlloc.v 4d8aeba047e5) and the engine's
   YGcallMxmn.v rows ---- *)
(* the kit's literal text (lib/A/PRH_FnReader.v tliteral_specX; PvB_D.v TLIT); owner: literal's walk *)
Hypothesis TLIT : tliteral_specX (fx := fx0) (PI := prh_img_B) (PA := PI_prog_B) TB ARIX SK.
(* The parse_items text (lib/A/PRH_FnParse.v tparse_items_specX) is NOT kept here: it is pvInst_D's / pvInst_step_PV's
   premise at ONE depth (the entry's), so the pair with parse_items closes by lib/A/VrdUnit.v's depth induction
   (the close is in lib/B/Prog/PItems_PvPair.v) *)
(* the kit's parse_string text (lib/A/PRH_FnReader.v tparse_string_specX; PvB_D.v TPSTR); owner: parse_string's walk *)
Hypothesis TPSTR : forall CTX0 CW, tparse_string_specX (fx := fx0) (PI := prh_img_B) (PA := PI_prog_B) TB ARIX SK CTX0 CW.
(* frame class 0's contract in the m-form at ARcf (lib/Reusable/YGcallMxmn.v astack_malloc_realizes_xm; PvB_A.v ASM0
   after the ARcfx lift pvI_asm0 below); owner: the frame-class walk (stack_malloc0_contract_xm in its
   per-image leaf, YGcallMxmn.v header family 2) *)
Hypothesis ASM0 : YGcallMxmn.astack_malloc_realizes_xm (fx := fx0) SEGS TB ARI 0.
(* The fuzz_malloc text (lib/A/PRH_FnAlloc.v tfuzz_malloc_specX; PvB_N.v FMALLOC); owner: fuzz_malloc's walk
   (lib/B/Prog/FuzzMallocB.v, at ARcfx) *)
Hypothesis FMALLOC : PRH_FnAlloc.tfuzz_malloc_specX (fx := fx0) (cp := CP) (PI := prh_img_B) (PA := PI_prog_B) TB ARIX SK.
(* __asan_memcpy's row in the m-form at ARcf (lib/Reusable/YGcallMxmn.v aintrin_realizes_xm; PvB_N.v CPY after the
   ARcfx lift pvI_cpy below); owner: the engine (po_asan_memcpy_cf = YG0d2cf.aintrin_realizes_cf, with its keep) *)
Hypothesis CPY : forall fx1 : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fx1) SEGS TB ARI OCpy (SIGMA AS___asan_memcpy).
(* ---- (b) the DISCHARGED hypotheses; each lemma states its hypothesis's text at the instance (the segment
   applications in pvInst_A / _D / _N / _X check each by type). PAL is PALibB.exvi_eh_palib, HHEAD / HEAD8
   PALibB.exvi_eh_head, LITCS PvB_ImgFacts.pvi_litcs_x ---- *)

(* LAWS (A, D, N at hl := cf_head, X): YGcallcf.v AR_laws_x_xs of YG0lawscf.v AR_laws_ok_cf *)
Lemma pvI_laws : AR_laws_x SEGS TB ARIX (@cf_head CP).
Proof. exact (YGcallcf.AR_laws_x_xs (cp := CP) rsegs TB (YG0lawscf.AR_laws_ok_cf (cp := CP) rsegs TB)). Qed.

(* OWNLOW (A): YGcallcf.v ARx_owned_low_law_xs of YG0lawscf.v AR_laws_ok_cf *)
Lemma pvI_ownlow : ARx_owned_low_law SEGS TB ARIX.
Proof. exact (YGcallcf.ARx_owned_low_law_xs (cp := CP) rsegs TB (YG0lawscf.AR_laws_ok_cf (cp := CP) rsegs TB)). Qed.

(* SKIPWS (A): the kit's skip_ws text (lib/A/PRH_FnReader.v tskip_ws_specX) PROVED at the instance: the
   B' acceptance theorem lib/B/Prog/skip_ws_mn.v skip_ws_holds (generic in ARx; the tree's skip_ws_inst.v c69f680618b2
   instantiates it at ARcf, here at ARcfx), LAWS by pvI_laws, its PALibCore by YC1fP.palib_core of
   PALibB.exvi_eh_palib *)
Lemma pvI_skipws : tskip_ws_specX (fx := fx0) (PI := prh_img_B) (PA := PI_prog_B) TB ARIX SK.
Proof.
exact (skip_ws_mn.skip_ws_holds (fx := fx0) (HL := @cf_head CP) SK TB ARIX pvI_laws
  (YC1fP.palib_core TB PALibB.exvi_eh_palib)).
Qed.

(* SMX (A): YGcallScf.v stack_malloc_x_any, at any relation *)
Lemma pvI_smx : forall ly S Hp W mem md cid, ARIX ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
Proof. exact (YGcallScf.stack_malloc_x_any SEGS ARIX). Qed.

(* ASM0 at ARcfx (A): the kept ARcf text lifted by YGcallMxmn.v astack_malloc_realizes_xm_conj (xs_placed_cf is kept by
   set_fs: YGcallScf.v xs_placed_cf_set_fs) *)
Lemma pvI_asm0 : YGcallMxmn.astack_malloc_realizes_xm (fx := fx0) SEGS TB ARIX 0.
Proof.
exact (YGcallMxmn.astack_malloc_realizes_xm_conj (fx := fx0) SEGS TB ARI (fun ly S => YG0ncf.xs_placed_cf ly S)
  0 YGcallScf.xs_placed_cf_set_fs ASM0).
Qed.

(* CPY at ARcfx (N): the kept ARcf row lifted by YGcallMxmn.v aintrin_realizes_xm_conj (FuzzStrdupB.v's lift) *)
Lemma pvI_cpy : forall fx1 : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fx1) SEGS TB ARIX OCpy (SIGMA AS___asan_memcpy).
Proof.
intros fx1.
exact (YGcallMxmn.aintrin_realizes_xm_conj (fx := fx1) SEGS TB ARI (fun ly S => YG0ncf.xs_placed_cf ly S)
  OCpy (SIGMA AS___asan_memcpy) (CPY fx1)).
Qed.

(* Hent (A): parse_value's entry is its listing slot (closed, vm_compute) *)
Lemma pvI_hent : SIGMA AS_parse_value = VAL A_TEXT + AF_pv.
Proof. apply Z.eqb_eq. vm_compute. reflexivity. Qed.

(* Hsm0 (A): the class-0 frame-area entry is the listing's __asan_stack_malloc_0 (closed, vm_compute) *)
Lemma pvI_hsm0 : pc_stack_malloc (as_code TB) 0 = SIGMA AS___asan_stack_malloc_0.
Proof. apply Z.eqb_eq. vm_compute. reflexivity. Qed.

(* Huarc (A): the use-after-return flag cell is the word after the shadow-base cell (closed, vm_compute) *)
Lemma pvI_huarc : as_uar_cell TB = VAL (A_OBJ 12) + 8.
Proof. apply Z.eqb_eq. vm_compute. reflexivity. Qed.

(* HHD (D, N): the instance's harness head is the model's HEAD (lib/A/CfParamsPreset.v cf_head = 16, preset source
   alloc.c:31; lib/Spec/PresetReqAt.v HEAD = 16, fuzz/alloc.c:28; closed, by conversion) *)
Lemma pvI_hhd : @cf_head CP = PresetReqAt.HEAD.
Proof. reflexivity. Qed.

(* Hobjd (A): the two GOT words lie below the cell pair, apart, all in low memory (closed, vm_compute) *)
Lemma pvI_hobjd : VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 1) /\ VAL (A_OBJ 1) + 8 <= VAL (A_OBJ 12) /\
  VAL (A_OBJ 12) + 12 <= kLowMemEnd.
Proof. split; [|split]; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* PSTOK (A, D: three parts; N, X: the first two): alloc.c's statics are image bytes (S1ImgB.v pst_in_img_B), off the
   runtime's owned statics and off errno (PvB_ImgFacts.v pvi_disj_b over the closed lists, vm_compute) *)
Lemma pvI_pstok : forall a, Exists (in_zr a) PSTX ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static TB) /\ ~ (as_errno TB <= a < as_errno TB + 4).
Proof.
intros a Ha. split; [exact (S1ImgB.pst_in_img_B a Ha)|]. split.
- assert (D : PvB_ImgFacts.pvi_disj_b PSTX (as_owned_static TB) = true) by (vm_compute; reflexivity).
  exact (PvB_ImgFacts.pvi_disj_b_sound _ _ D a Ha).
- intros He. assert (D : PvB_ImgFacts.pvi_disj_b PSTX [(as_errno TB, 4)] = true) by (vm_compute; reflexivity).
  apply (PvB_ImgFacts.pvi_disj_b_sound _ _ D a Ha). apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. clear - He; lia.
Qed.

Lemma pvI_pstok2 : forall a, Exists (in_zr a) PSTX ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static TB).
Proof. intros a Ha. destruct (pvI_pstok a Ha) as (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

(* RONP (A, D): no read-only byte is one of alloc.c's statics (S1ImgB.v pst_not_ro_B); PSTRO (N) is that lemma *)
Lemma pvI_ronp : forall a, in_roP SEGS (@pa_relro_lo _ B_prog_listing PI_prog_B) (@pa_relro_hi _ B_prog_listing PI_prog_B) a ->
  ~ Exists (in_zr a) PSTX.
Proof. intros a Hro Hx. exact (S1ImgB.pst_not_ro_B a Hx Hro). Qed.

(* pvh_zs_al (A, D): the image's zero-shadow ranges are whole granules (closed, vm_compute) *)
Lemma pvI_zs_al : forall r, In r (as_zero_shadow TB) -> fst r mod 8 = 0 /\ snd r mod 8 = 0.
Proof.
assert (H : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0))%bool (as_zero_shadow TB) = true)
  by (vm_compute; reflexivity).
intros r Hr. rewrite forallb_forall in H. specialize (H r Hr).
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. split; [exact H1 | exact H2].
Qed.

(* PA_BOX (A, D, N): the kit's kept_img / kept_at bounds pa_lo / pa_hi are the B' image box (PAImg_prog.v: pa_lo :=
   IMG_LO_B, pa_hi := IMG_TOP_B; closed, by conversion) *)
Lemma pvI_pa_box : YImgTop.IMG_LO_B <= @pa_lo _ B_prog_listing PI_prog_B /\
  @pa_hi _ B_prog_listing PI_prog_B <= YImgTop.IMG_TOP_B.
Proof. split; apply Z.le_refl. Qed.

(* pvh_img_vis (A, D): the image's shadow is mapped in every ARcf state: YImgShadowCoverCf.v
   img_shadow_vis_cf_at_of_cover on B's generated lists (YF0m.v Tfib_zero_shadow, Tfib_const_shadow), whose cover
   check over [IMG_LO_B, IMG_TOP_B) is decided by vm_compute (as A/AImgShadowVis.v tfib_img_shadow_cover for image A) *)
Lemma pvI_cover :
  YImgShadowCover.img_shadow_cover YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow YImgTop.IMG_LO_B YImgTop.IMG_TOP_B = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pvI_const_incl : forall ly, incl YF0m.Tfib_const_shadow (as_const TB ly).
Proof.
intros ly. change (as_const TB ly) with (YF0m.Tfib_const ly). unfold YF0m.Tfib_const.
apply incl_appr, incl_appr, incl_refl.
Qed.

Lemma pvI_img_vis_cf : forall ly S Hp (W : world SEGS) mem md a, ARI ly S Hp W mem md ->
  YImgTop.IMG_LO_B <= a < YImgTop.IMG_TOP_B -> aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof.
exact (YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover (cp := CP) rsegs TB YF0m.Tfib_zero_shadow
  YF0m.Tfib_const_shadow YImgTop.IMG_LO_B YImgTop.IMG_TOP_B pvI_cover (incl_refl _) pvI_const_incl).
Qed.

Lemma pvI_img_vis : forall ly S Hp (W : world SEGS) mem md a, ARIX ly S Hp W mem md ->
  YImgTop.IMG_LO_B <= a < YImgTop.IMG_TOP_B -> aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof. intros ly S Hp W mem md a [HA _]. exact (pvI_img_vis_cf ly S Hp W mem md a HA). Qed.

(* ASFX (X): YGcallScf.v astack_free_x_xs (YG0tcf.v astack_free_law_ok_cf, xs_placed_cf kept by stack_free_state) *)
Lemma pvI_asfx : forall ly S Hp W mem md mem' md' cid pos,
  ARIX ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned TB ly S a -> a <> flag_addr ly cid pos ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARIX ly (stack_free_state cid pos S) Hp W mem' md'.
Proof. exact (YGcallScf.astack_free_x_xs (cp := CP) rsegs TB). Qed.

(* FFLX (X): YGcallScf.v frame_flag_x_xs (YG0scf.v AR_flag_law_ok_cf and AR_client_img_law_ok_cf, flag arm) *)
Lemma pvI_fflx : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARIX ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned TB ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Proof. exact (YGcallScf.frame_flag_x_xs (cp := CP) rsegs TB). Qed.

(* SFX (X): YGcallScf.v stack_free_x_any, at any relation *)
Lemma pvI_sfx : forall ly S Hp W mem md cid pos, ARIX ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Proof. exact (YGcallScf.stack_free_x_any SEGS ARIX). Qed.

(* FLAGP (X): YG0scf.v AR_flag_law_ok_cf (its statement YG0dcf.v AR_flag_law_cf is the hypothesis at ARcf) *)
Lemma pvI_flagp : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARIX ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos) /\ aowned TB ly S (flag_addr ly cid pos) /\
  in_app (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md cid pos [HA _] Hin.
exact (YG0scf.AR_flag_law_ok_cf (cp := CP) rsegs TB ly S Hp W mem md cid pos HA Hin).
Qed.

(* ---- SEG_N's (PvB_N.v) closed image facts and instance laws. LAWS (hl := cf_head), HEAD8, PSTOK (pvI_pstok2), HHD
   (pvI_hhd) and PSTRO (S1ImgB.v pst_not_ro_B) are as above; HSHD is field 14 of the laws at ARcfx (YCbqG.v
   alx_hshadow of pvI_laws); IMG_GOTV is strtod_row.v strtod_got_B ---- *)
(* IMG_COVER: the image's four segments cover [IMG_LO_B, IMG_TOP_B) without a gap (closed, vm_compute) *)
Lemma pvI_img_cover : forall a, YImgTop.IMG_LO_B <= a < YImgTop.IMG_TOP_B -> in_img SEGS a.
Proof.
intros a Ha.
apply (pvI_cov_sound rsegs (length rsegs) YImgTop.IMG_LO_B YImgTop.IMG_TOP_B); [vm_compute; reflexivity | exact Ha].
Qed.

(* B_errno: errno is strtod's cell (closed, vm_compute) *)
Lemma pvI_errno : as_errno TB = STRTOD_ERRNO_B.
Proof. apply Z.eqb_eq. vm_compute. reflexivity. Qed.

(* IMG_GOTC: the strtod guard's GOT word is a const cell of TfibB: B' YF0m.v Tfib_const_abs index 169 (YF0m.v:202) *)
Lemma pvI_gotc : forall ly, In (z8 (ANum STRTOD_GOT_GUARD_B) STRTOD_GUARD_B) (as_const TB ly).
Proof.
intros ly. change (as_const TB ly) with (YF0m.Tfib_const ly). unfold YF0m.Tfib_const.
apply in_or_app. right. apply in_or_app. left.
apply (nth_error_In _ 169). vm_compute. reflexivity.
Qed.

(* HZS: an in_zs range 64 bytes inside the image: its shadow is zero (YCbqG.v alx_zshadow of PALibB.exvi_eh_laws on the
   granule-aligned as_zero_shadow range that holds it, pvI_zs_al), and its shadow hull is image shadow (PvB_A_Home.v
   pvh_hull_img, pvI_img_vis_cf); FuzzStrdupB.v sd_src_shadow's in_zs arm *)
Lemma pvI_hzs : forall ly S Hp (W : world SEGS) mem md p n, ARIX ly S Hp W mem md -> in_zs TB p n ->
  YImgTop.IMG_LO_B + 64 <= p -> p + n + 64 <= YImgTop.IMG_TOP_B ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\ (0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) p n).
Proof.
intros ly S Hp W mem md p n [HA _] (q & m & Hin & Hq & Hqm) Hlo Hhi.
destruct (pvI_zs_al (q, m) Hin) as [Z3 Z4]. cbn [fst snd] in Z3, Z4.
pose proof (alx_zshadow _ _ _ PALibB.exvi_eh_laws ly S Hp W mem md (q, m) HA
  ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
cbn [fst snd] in Hz.
split.
- apply (range_addressable_sub (aview SEGS (w_H W) mem) SHADOW_OFF q m p n); [|exact Hq | exact Hqm].
  exact (zero_shadow_range (aview SEGS (w_H W) mem) SHADOW_OFF q m Z3 Z4 Hz).
- intros Hn s0 Hs. destruct (PvB_A_Home.pvh_hull_img p n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
  exact (pvI_img_vis_cf ly S Hp W mem md _ HA Hr).
Qed.

(* HKIMG: a kept image string lies 64 bytes inside pa_lo / pa_hi (= IMG_LO_B / IMG_TOP_B at PI_prog_B, by conversion),
   so its shadow hull is image shadow *)
Lemma pvI_hkimg : forall ly S Hp (W : world SEGS) mem md p n, ARIX ly S Hp W mem md ->
  kept_img (PA := PI_prog_B) TB p n -> 0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md p n [HA _] (Hlo & Hhi & _) Hn s0 Hs.
destruct (PvB_A_Home.pvh_hull_img p n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
exact (pvI_img_vis_cf ly S Hp W mem md _ HA Hr).
Qed.

(* FS_HI: a live fake frame lies at or above IMG_TOP_B: ly_img holds an image range that ends at IMG_TOP_B (YG0ncf.v
   amc_static_img, a closed existsb over TfibB's lists) and every live fake frame lies above ly_img (YCbqG.v field 17
   alx_img of PALibB.exvi_eh_laws) *)
Lemma pvI_fs_hi : forall ly S Hp (W : world SEGS) mem md cid pos, ARIX ly S Hp W mem md -> In (cid, pos) (frames S) ->
  YImgTop.IMG_TOP_B <= frame_addr ly cid pos.
Proof.
intros ly S Hp W mem md cid pos [HA _] Hin.
assert (E : existsb (fun r => YImgTop.IMG_TOP_B <=? fst r + snd r) (as_owned_static TB ++ as_zero_shadow TB) = true)
  by (vm_compute; reflexivity).
apply existsb_exists in E as (r & Hr & Hle). apply Z.leb_le in Hle.
pose proof (proj1 (Forall_forall _ _) (YG0ncf.amc_static_img _ _ _ _ _ (proj1 HA)) r Hr) as [_ S2].
pose proof (proj2 (alx_img _ _ _ PALibB.exvi_eh_laws ly S Hp W mem md HA) cid pos Hin) as F.
clear - Hle S2 F; lia.
Qed.

(* STR: the B' strtod row at the instance, strtod_row.v strtod_row_B with strtod_row_sat.v's three closed
   premises at TfibB (strtod_sat_tp_B, strtod_sat_errno_B, strtod_sat_owned_B): the listing's strtod entry is
   strtod_c.v's STRTOD (closed, vm_compute), the stack need STK_RT_STRTOD covers STRTOD_K (closed), and PvB_ND.v's
   pnd_txt_ok is the row's text condition verbatim *)
Lemma pvI_str : YStrtodRowX.astrtod_realizes_x SEGS TB ARIX strtod_img_B (SIGMA AS_strtod) STK_RT_STRTOD
  strtod_model_B PvB_ND.pnd_txt_ok.
Proof.
assert (ES : SIGMA AS_strtod = STRTOD_B) by (apply Z.eqb_eq; vm_compute; reflexivity).
rewrite ES.
apply (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_row.strtod_row_B TB ARIX pvI_laws
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_row_sat.strtod_sat_tp_B
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_row_sat.strtod_sat_errno_B
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_row_sat.strtod_sat_owned_B).
- apply Z.leb_le. vm_compute. reflexivity.
- intros txt H. exact H.
- intros txt bits c _ H. exact H.
Qed.

(* ---- the segments at the instance: each a plain run to the continuation post pv_FINK (PvB_Defs.v: the final post
   in the record's relation YA0nH.SRr' segs RZ_cf) ---- *)
Lemma pvInst_A : forall en, pv_pre TB ARIX en ->
  (forall W2 ms2 md2, pv_at_C1 TB ARIX en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK TB ARIX en)) ->
  SRr SEGS (pe_W en) (cfg_at (fx := fx0) SEGS (SIGMA AS_parse_value) (pe_regs en) (pe_mem en) (pe_md en))
    (pv_FINK TB ARIX en).
Proof.
exact (PvB_A.pvA_holds TB ARIX pvI_laws pvI_ownlow pvI_smx pvI_asm0 pvI_skipws PALibB.exvi_eh_palib pvI_hent
  pvI_hsm0 pvI_huarc pvI_hobjd PALibB.exvi_eh_head pvI_pstok pvI_ronp pvI_img_vis pvI_zs_al pvI_pa_box).
Qed.

Lemma pvInst_D : forall en W' ms mdc, pv_pre TB ARIX en ->
  (forall CTX CTX0 CW,
     tparse_items_specX (fx := fx0) (PI := prh_img_B) (PA := PI_prog_B) TB ARIX SK (pe_d en) CTX CTX0 CW) ->
  pv_at_C1 TB ARIX en W' ms mdc ->
  (forall W2 ms2 md2, pv_at_N TB ARIX en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK TB ARIX en)) ->
  (forall W2 ms2 md2, pv_at_exit TB ARIX en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK TB ARIX en)) ->
  SRr SEGS W' (mkCfg ms mdc) (pv_FINK TB ARIX en).
Proof.
exact (PvB_D.pvD_holds TB ARIX pvI_laws TLIT pvI_ronp PvB_ImgFacts.pvi_litcs_x TPSTR
  PALibB.exvi_eh_head pvI_pstok pvI_img_vis pvI_zs_al pvI_pa_box pvI_hhd).
Qed.

Lemma pvInst_N : forall en W' ms mdc, pv_pre TB ARIX en -> pv_at_N TB ARIX en W' ms mdc ->
  (forall W2 ms2 md2, pv_at_exit TB ARIX en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK TB ARIX en)) ->
  SRr SEGS W' (mkCfg ms mdc) (pv_FINK TB ARIX en).
Proof.
exact (PvB_N.pvN_seg TB ARIX pvI_laws FMALLOC pvI_cpy pvI_str (alx_hshadow _ _ _ pvI_laws)
  pvI_hzs pvI_hkimg pvI_pa_box S1ImgB.pst_not_ro_B pvI_pstok2 pvI_img_cover pvI_errno
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_row.strtod_got_B pvI_gotc
  PALibB.exvi_eh_head pvI_fs_hi pvI_hhd).
Qed.

Lemma pvInst_X : forall en W' ms mdc, pv_pre TB ARIX en -> pv_at_exit TB ARIX en W' ms mdc ->
  SRr SEGS W' (mkCfg ms mdc) (pv_FINK TB ARIX en).
Proof.
exact (PvB_X.pvX_holds TB ARIX pvI_laws pvI_asfx pvI_fflx pvI_sfx pvI_flagp pvI_pstok2
  PALibB.exvi_eh_head).
Qed.

(* ---- the composition at the instance: the record text (PvB_Top.v pvTop_compose_step), its instance
   arguments written out (ci := CfImg_B, cp := CfParams_preset, PI := prh_img_B, RL := prh_room_live_a8,
   PA := PI_prog_B, B := TfibB, ARx := ARcfx). THE STEP of the parse_value / parse_items pair: parse_value at depth d
   from parse_items at the SAME depth d (lib/A/VrdUnit.v vrd_unit_closed's step_PV) ---- *)
Theorem pvInst_step_PV : forall d,
  (forall CTX CTX0 CW,
     @tparse_items_specX fx0 rc CfImgB.CfImg_B CP prh_img_B (@prh_room_live_a8 CP) B_prog_listing PI_prog_B TB ARIX SK
       d CTX CTX0 CW) ->
  forall CTX CTX0 CW,
  @tparse_value_specX fx0 rc CfImgB.CfImg_B CP prh_img_B (@prh_room_live_a8 CP) B_prog_listing PI_prog_B TB ARIX SK
    d CTX CTX0 CW.
Proof. exact (PvB_Top.pvTop_compose_step TB ARIX pvInst_A pvInst_D pvInst_N pvInst_X). Qed.

(* the same at every depth, from parse_items' text at every depth *)
Theorem pvInst_compose : forall d CTX CTX0 CW,
  (forall d' CTX' CTX0' CW',
     @tparse_items_specX fx0 rc CfImgB.CfImg_B CP prh_img_B (@prh_room_live_a8 CP) B_prog_listing PI_prog_B TB ARIX SK
       d' CTX' CTX0' CW') ->
  @tparse_value_specX fx0 rc CfImgB.CfImg_B CP prh_img_B (@prh_room_live_a8 CP) B_prog_listing PI_prog_B TB ARIX SK
    d CTX CTX0 CW.
Proof. intros d CTX CTX0 CW TPI. exact (pvInst_step_PV d (TPI d) CTX CTX0 CW). Qed.

End i.

Set Printing Implicit. Unset Printing Notations.
About pvInst_step_PV.
About pvInst_compose.
Print Assumptions pvInst_A.
Print Assumptions pvInst_D.
Print Assumptions pvInst_X.
Print Assumptions pvInst_N.
Print Assumptions pvInst_compose.
Print Assumptions pvInst_step_PV.
