(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module names changed; 61 of its 100 lines of code are new or changed and 475 lines of the source are left out. *)
(* fuzz_preset, slice S8a EX-VALUE, image A' (asan #102, pin 1be0f53d, unstripped twin bff8519b): PIECES 7 + 8 INSTANTIATED.
   The one file that Requires the piece-7 sub-lanes' segment files (S8aP7a: SEG 2 and p7a_mid_call, S8aP7b: SEG 3,
   S8aP7c: SEG 1) together with S8aItemsWalk.v (FRAME kit, SEG 4, the array path, the composition ev7_step_of, piece 8),
   so that each of those builds on its own. Numerals: none.
   #102 RELOCATION (words equal up to pc-relative fields, but the frame string loaded at +0xa8 / +0xc4 CHANGED
   between the pins): pieces 7 + 8 move from image A (ex_value 0x82f30) to image A' BY SYMBOL (A' ex_value 0x832a4, same offsets;
   listing position 6628 -> 7364 on int102's Listing_prog.v 7ed1529926bd). The kit's ledger gains #102's g_most / g_own_ran_out
   (PRH_Base.v 3004a98fe2d9), which every ledger helper and keep below carries. No statement or Section hypothesis changed.
   SECTION HYPOTHESES AND PREMISES (name: meaning; OWNER; status), every one a stand-in until its owner's text lands:
   - LAWS: AR_laws_x SEGS B ARx cf_head, the allocator invariant's laws at the harness head length; h-mani-a8 /
     c-omx-alloc; at ARx := ARcf discharged by YGcallcf.v's AR_laws_x_cf (from AR_laws_cf).
   - WS = ev_ws_loop_spec_FIX: the inlined whitespace loop with its raw-frame conjunct; WalkS8a; CLOSED: proved in
     each file as `WS` by S8aWs.ev_ws_loop (ws-rawframe 91e4dffbfb7, Qed, its only hypothesis LAWS).
   - PSTI: alloc.c's statics (prh_pst) are image bytes; a Theorem Labs lane; true at prh_img_A, open as a text.
   - STR: the ex_string text tex_string_specX at every float state; S8b; open (the ex_string walk).
   - SCMP: the strcmp row at __wrap_strcmp, every float state, in its xrom form YGcallMxmn.astrcmp_realizes_xrom
     (arodata_okP premise, memnorm keep last); c-libc-stdio. HYPOTHESIS CHANGE (stronger: adds the memnorm keep;
     arodata_okP form; was YGcallMx.astrcmp_realizes_x). Supplier ps_strcmp_xrom_A @ c-libc-stdio-presetstr-ro
     45e489ec67c7 (lib/A/PSstrRo.v:64). ONE arodata_okP HOME: the engine of record (s1b bb085d091bbe, YGcallMxmn blob
     b47cf7942c3d) and the supplier both cite PresetRodata.arodata_okP (lib/Spec/PresetRodata.v 4eb7e95e7e93). LINKS:
     ps_strcmp_xrom_A type-checks at SCMP's text at ARx := ARcf SEGS B (a scratch lemma, Qed, over the OLD-PIN tree
     with the supplier's files by path; not re-run on #102 here). The walk feeds SCMP's arodata_okP premise from
     ev_pre's PRH_Base.arodata_okP by S8aItems.aro_prh_to_mxmn (conversion; on #102 PRH_Base.arodata_okP is the
     kit's abbreviation of PresetRodata.arodata_okP itself).
   - GONE (S8aP7a.v, this memnorm adaptation): ROM (the strcmp row's read-only fact is now its arodata_okP premise,
     fed from ev_pre: S8aP7a.v p7a_aro) and BLK32 (keys[n]'s `kx + 1 < 2 ^ 32` is in the kit's pj_cstrR,
     PRH_Reader.v:113).
   - BLKAM8 = S8aNumE's CUTFIX_blk_amem8 verbatim: a live block is a region of the string rows' amem_range8; h-mani-a8;
     at the instance block_amem_range8_cf (YGcfBlockRange.v:46).
   - MEMNORM (S8aIface: ev_pre's and ev_mid's last conjunct): no hypothesis; every segment keeps it by YC1fPx's
     *_inv runners and across ex_string / strcmp / the recursive ex_value by each callee's m-form keep.
   - IH premise of ev_item_step_A / ev_item_holds_A: forall fxd, tex_value_specX (fx := fxd) .. n' (the recursion at
     nesting n'); WalkS8a; discharged by its ev_items_loop induction.
   - GONE (c-omx-hpreset 10:43Z): HSH (derived: AR_laws_x's field alx_hshadow at cf_head, S8aItems.v
     ev_hshadow_of_laws) and HULL (false as stated; replaced by alx_blocks / alx_blocks_tail, S8aP7a.v
     p7a_tail_present). GONE (S8a memnorm brief): HFHULL and HSTK64, derived from AR_laws_x field 18 (alx_layout_ok)
     in S8aP7a.v the way S8aEntry.v's eve_frame_hull / eve_stk64 derive them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK0o YCbqG.
(* The caller-window call rule is YCbqGcallW.v's aj_call_xWF (the engine set of walkkit b77223726823; WalkS4's
   PRW_CallerJ.v, landed in Reusable, over YCbqG's own fp_sub_x). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG0dcf YGcallMx FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aItems.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S8aWs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S8aItemsWalk S8aP7a S8aP7b S8aP7c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
(* the walk is at image A's PrhImg (frames, statics), as at its listing *)
#[local] Existing Instance prh_img_A.
#[local] Notation PI := prh_img_A.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := PI)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {RL : PrhRoomLive}.
(* the kit's allocator laws at ARx, at the harness head length cf_head (YCbqG.v journal 83da015952be; at ARx := ARcf
   this is YGcallcf.v's AR_laws_x_cf) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the shared whitespace loop, PROVED (no longer a stand-in): WalkS8a's S8aWs.ev_ws_loop (ws-rawframe 91e4dffbfb7),
   whose only Section hypothesis is LAWS *)
Lemma WS : ev_ws_loop_spec_FIX (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof. exact (S8aWs.ev_ws_loop B ARx SK LAWS). Qed.
(* (HSH is not a hypothesis: S8aItems.v ev_hshadow_of_laws derives it from LAWS's field alx_hshadow) *)
(* STAND-IN: a Theorem Labs lane, the image binding of PrhImg: alloc.c's statics (prh_pst) are image bytes (true at prh_img_A: PRH_Img.v,
   below kLowMemEnd by pa_segs_low, so apart from the stack); without it a generic PrhImg could put them in `struct ex` *)
Hypothesis PSTI : forall z, Exists (in_zr z) PST -> in_img SEGS z.
(* (HFHULL / HSTK64 are not hypotheses: S8aP7a.v derives them from LAWS's field 18 alx_layout_ok) *)
(* SEG 2's callee rows and image facts (a sub-lane's Section hypotheses, texts verbatim from S8aP7a.v):
   STAND-IN, owner slice S8b: the ex_string text at every float state *)
Hypothesis STR : forall fxc : YK11.FPState,
  tex_string_specX (fx := fxc) (cp := cp) (L := A_prog_listing) (PA := PA) B ARx SK.
(* STAND-IN, owner c-libc-stdio: the strcmp row at __wrap_strcmp, at every float state, in its xrom form (arodata_okP
   premise, memnorm keep). HYPOTHESIS CHANGE (stronger: adds the memnorm keep; arodata_okP form). Supplier
   ps_strcmp_xrom_A @ c-libc-stdio-presetstr-ro 45e489ec67c7; it and the engine of record (s1b bb085d091bbe, YGcallMxmn
   blob b47cf7942c3d) cite the one home PresetRodata.arodata_okP; it type-checks at this text at ARx := ARcf SEGS B. *)
Hypothesis SCMP : forall fxc : YK11.FPState, YGcallMxmn.astrcmp_realizes_xrom (fx := fxc) SEGS B ARx
  (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA) (SIGMA AS___wrap_strcmp).
(* (ROM and BLK32 are not hypotheses any more: S8aP7a.v no longer uses them) *)
(* STAND-IN, owner h-mani-a8 / c-omx-alloc: S8aNumE's CUTFIX_blk_amem8, verbatim (block_amem_range8_cf at the instance) *)
Hypothesis BLKAM8 : forall ly S Hp W mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> YGcallMx.amem_range8 p (req_size n).

(* SEG 1, sub-lane S8aP7c, with lane FRAME's ev_mid_frame / ev_bounds for its MIDF / BNDS *)
Lemma ev7_seg1 : ev7_seg1_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof.
eapply S8aP7c.ev7_seg1_A with (LAWS := LAWS);
  first [exact (S8aItemsWalk.ev_mid_frame B ARx SK LAWS PSTI) | eapply S8aItemsWalk.ev_bounds | eassumption].
Qed.

(* SEG 3, sub-lane S8aP7b *)
Lemma ev7_seg3 : ev7_seg3_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof.
eapply S8aP7b.ev7_seg3_A with (LAWS := LAWS);
  first [exact (S8aItemsWalk.ev_mid_frame B ARx SK LAWS PSTI) | eapply S8aItemsWalk.ev_bounds | eassumption].
Qed.

(* ev_mid across the recursive call: sub-lane S8aP7a's p7a_mid_call *)
Lemma ev7_midcall : S8aItemsWalk.ev7_midcall_stmt (fx := fx) B ARx SK.
Proof.
intros a ly S Hp W mem md k p dep dl STK1 e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 p' dep' dl'.
eapply S8aP7a.p7a_mid_call with (LAWS := LAWS); eassumption.
Qed.

(* pieces 7 + 8 as one item: S8aIface's ev_item_spec, from SEG 2 (sub-lane S8aP7a), ev_mid across the recursive call
   (S8aP7a's p7a_mid_call) and the IH at every float state *)
Lemma ev_item_holds_A_of : ev7_seg2_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK ->
  S8aItemsWalk.ev7_midcall_stmt (fx := fx) B ARx SK ->
  forall n', (forall fxd : YK11.FPState, tex_value_specX (fx := fxd) (cp := cp) (L := A_prog_listing) (PA := PA) B ARx SK n') ->
  ev_item_spec (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK n'.
Proof.
intros H2 MIDC n' IH. apply ev_item_holds_of.
- apply (S8aItemsWalk.ev7_step_of B ARx SK LAWS); [exact ev7_seg1 | exact H2 | exact ev7_seg3 |].
  exact (S8aItemsWalk.ev7_seg4_A B ARx SK LAWS MIDC n' IH).
- eapply S8aItemsWalk.ev_item_next_A with (LAWS := LAWS); eassumption.
Qed.

(* with ev_mid across the call instantiated: only SEG 2 (in progress, sub-lane S8aP7a) and the IH remain *)
Lemma ev_item_holds_A_of2 : ev7_seg2_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK ->
  forall n', (forall fxd : YK11.FPState, tex_value_specX (fx := fxd) (cp := cp) (L := A_prog_listing) (PA := PA) B ARx SK n') ->
  ev_item_spec (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK n'.
Proof. intros H2. exact (ev_item_holds_A_of H2 ev7_midcall). Qed.

(* SEG 2, sub-lane S8aP7a *)
Lemma ev7_seg2 : ev7_seg2_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof. eapply S8aP7a.ev7_seg2_A with (LAWS := LAWS); eassumption. Qed.

(* ======== PIECE 7: ev_item_step_A (0x837ec-0x83a50); with piece 8, one item (S8aIface's ev_item_spec) ======== *)
Lemma ev_item_step_A : forall n',
  (forall fxd : YK11.FPState, tex_value_specX (fx := fxd) (cp := cp) (L := A_prog_listing) (PA := PA) B ARx SK n') ->
  ev_item_step_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK n'.
Proof.
intros n' IH.
apply (S8aItemsWalk.ev7_step_of B ARx SK LAWS); [exact ev7_seg1 | exact ev7_seg2 | exact ev7_seg3 |].
exact (S8aItemsWalk.ev7_seg4_A B ARx SK LAWS ev7_midcall n' IH).
Qed.

Lemma ev_item_holds_A : forall n',
  (forall fxd : YK11.FPState, tex_value_specX (fx := fxd) (cp := cp) (L := A_prog_listing) (PA := PA) B ARx SK n') ->
  ev_item_spec (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK n'.
Proof. intros n' IH. exact (ev_item_holds_A_of2 ev7_seg2 n' IH). Qed.

End t.
