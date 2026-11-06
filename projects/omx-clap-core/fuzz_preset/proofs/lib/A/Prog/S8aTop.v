(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aTop.v, with its module paths changed; 45 of its 177 lines of code are new or changed and 12 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane; assigned by a Theorem Labs lane 11:04Z for a Theorem Labs lane's driver top; slice S8a owner
   a Theorem Labs lane / the kit owner). fuzz_preset, image A' (asan #102): the CLOSING COMPOSITION of ex_value into the kit's text
   tex_value_specX (lib/A/PRH_FnEx.v), on the batch kit's cut.

   WHY A NEW INDUCTION. S8aCompose.ex_value_compose proves `forall n, tex_value_specX n` at ONE float state fx, from
   HITEM : forall n', tex_value_specX n' -> ev_item_spec n' at that same fx. The item piece of record,
   S8aItemsTop.ev_item_holds_A, needs the inner IH at EVERY float state (`forall fxd, tex_value_specX (fx := fxd) n'`:
   the recursive call runs at the piece's fxc, S8aItemsWalk.v:1687). So this file proves
   `forall n fx, tex_value_specX (fx := fx) n` by one induction on n, at every fx at once. It reuses
   S8aCompose.ex_value_from_stepok and S8aCompose.ev_step_ok_0 as they are. S8aCompose's ev_items_loop and
   ev_step_ok_S are re-stated here (items_loop_at / step_ok_S_at), with the item fact at the one nesting n' in place
   of HITEM; their scripts are S8aCompose's.

   Section top: the composition over the piece specs, each at every fx (generic in CfParams). Section closed, at
   preset's CfParams (pieces 6 / 9 / 10 are stated there): the pieces with a proof on the cut are discharged by their
   theorems; every other piece stays a NAMED hypothesis, with its owner. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx PRH_Img Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S8aCompose S8aEntry S8aNumber S8aNumCut S8aItemsTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S8aOpen S8aClose S8aExit S8aStr ExsA_Discharge ExwA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
Import ListNotations.
Local Open Scope Z_scope.

Section top. Context {rc : YM05.RunCeil} {cp : CfParams} {RL : PrhRoomLive}.
(* the walk is at image A's PrhImg (frames, statics), as at its listing (S8aItemsTop.v) *)
#[local] Existing Instance prh_img_A.
#[local] Notation PI := prh_img_A.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

#[local] Notation TEX fx n := (@tex_value_specX fx rc cp PI RL A_prog_listing PA B ARx SK n).

(* the pieces, each at every float state *)
Hypothesis P_ENTRY : forall fx, @ev_entry_spec fx rc cp PI RL A_prog_listing PA B ARx SK.
Hypothesis P_DISP  : forall fx, @ev_disp_spec fx rc cp PI RL A_prog_listing PA B ARx SK.
Hypothesis P_NUM   : forall fx, @ev_number_spec fx rc cp PI RL A_prog_listing PA B ARx SK.
Hypothesis P_OPEN  : forall fx, @ev_items_open_spec fx rc cp PI RL A_prog_listing PA B ARx SK.
Hypothesis P_ITEM  : forall fx n', (forall fxd, TEX fxd n') -> @ev_item_spec fx rc cp PI RL A_prog_listing PA B ARx SK n'.
Hypothesis P_CLOSE : forall fx, @ev_items_close_spec fx rc cp PI RL A_prog_listing PA B ARx SK.
Hypothesis P_END   : forall fx, @ev_items_end_spec fx rc cp PI RL A_prog_listing PA B ARx SK.
Hypothesis P_EXIT  : forall fx, @ev_exit_spec fx rc cp PI RL A_prog_listing PA B ARx SK.

(* S8aCompose.ev_items_loop with the item fact at the one nesting n' (HIT) in place of HITEM *)
Lemma items_loop_at : forall (fx : YK11.FPState) n',
  @ev_item_spec fx rc cp PI RL A_prog_listing PA B ARx SK n' ->
  forall (fuel : nat) a fxc W regs mem md ly S Hp k o nn cap acc i dln,
  ea_n a = Nat.succ n' ->
  (length (ea_x a) - i <= fuel)%nat ->
  @ev_pre fx rc cp PI A_prog_listing PA B ARx a -> @ev_fx fx fxc ->
  @ev_at_step rc cp PI RL A_prog_listing PA B ARx SK a W regs mem md ly S Hp k o nn cap acc i dln ->
  SRr SEGS W (@ev_cfg rc A_prog_listing PA fxc regs EV_STEP mem md) (@ev_to_exit fx rc cp PI RL A_prog_listing PA B ARx SK a).
Proof.
  intros fx n' HIT. pose proof (P_CLOSE fx) as HCLOSE.
  induction fuel as [|fuel IH]; intros a fxc W regs mem md ly S Hp k o nn cap acc i dln En Hfu Hpre Hfxc Hstep.
  - eapply SRr_bind; [exact (HIT a fxc W regs mem md ly S Hp k o nn cap acc i dln En Hpre Hfxc Hstep)|].
    cbv beta. intros Wb cb Hwle Hpost.
    destruct Hpost as [Hex | Hr]; [apply SRr_ret; exact Hex|].
    destruct Hr as (fxb & regsb & memb & mdb & lyb & Sb & Hpb & kb & ib & dlnb & nmb & ub & Hrest). destruct Hrest as (Hfxb & Hltb & Hcase).
    destruct Hcase as [(capb & Hceq & Hstepb) | (Hceq & Hcloseb)]; subst cb.
    { exfalso. apply S8aCompose.step_ile in Hstepb. lia. }
    { exact (HCLOSE a fxb Wb regsb memb mdb lyb Sb Hpb kb o ((nmb, ub) :: acc) ib dlnb Hpre Hfxb Hcloseb). }
  - eapply SRr_bind; [exact (HIT a fxc W regs mem md ly S Hp k o nn cap acc i dln En Hpre Hfxc Hstep)|].
    cbv beta. intros Wb cb Hwle Hpost.
    destruct Hpost as [Hex | Hr]; [apply SRr_ret; exact Hex|].
    destruct Hr as (fxb & regsb & memb & mdb & lyb & Sb & Hpb & kb & ib & dlnb & nmb & ub & Hrest). destruct Hrest as (Hfxb & Hltb & Hcase).
    destruct Hcase as [(capb & Hceq & Hstepb) | (Hceq & Hcloseb)]; subst cb.
    { eapply (IH a fxb Wb regsb memb mdb lyb Sb Hpb kb o (Nat.succ nn) capb ((nmb, ub) :: acc) ib dlnb);
        [exact En | | exact Hpre | exact Hfxb | exact Hstepb].
      apply S8aCompose.step_ile in Hstepb. lia. }
    { exact (HCLOSE a fxb Wb regsb memb mdb lyb Sb Hpb kb o ((nmb, ub) :: acc) ib dlnb Hpre Hfxb Hcloseb). }
Qed.

(* S8aCompose.ev_step_ok_S with the IH at every float state *)
Lemma step_ok_S_at : forall fx n', (forall fxd, TEX fxd n') ->
  @S8aCompose.ev_step_ok fx rc cp PI RL A_prog_listing PA B ARx SK (Nat.succ n').
Proof.
  intros fx n' IH a fxc W regs mem md ly S Hp k o nn cap acc i dln Hn Hpre Hfxc Hstep.
  eapply (items_loop_at fx n' (P_ITEM fx n' IH) (length (ea_x a) - i) a fxc W regs mem md ly S Hp k o nn cap acc i dln);
    [exact Hn | apply Nat.le_refl | exact Hpre | exact Hfxc | exact Hstep].
Qed.

(* ex_value at every nesting and every float state *)
Theorem ex_value_top : forall n fx, TEX fx n.
Proof.
  induction n as [|n' IHn']; intros fx.
  - exact (@S8aCompose.ex_value_from_stepok fx rc cp PI RL A_prog_listing PA B ARx SK
      (P_ENTRY fx) (P_DISP fx) (P_NUM fx) (P_OPEN fx) (P_END fx) (P_EXIT fx) 0
      (@S8aCompose.ev_step_ok_0 fx rc cp PI RL A_prog_listing PA B ARx SK)).
  - exact (@S8aCompose.ex_value_from_stepok fx rc cp PI RL A_prog_listing PA B ARx SK
      (P_ENTRY fx) (P_DISP fx) (P_NUM fx) (P_OPEN fx) (P_END fx) (P_EXIT fx) (Nat.succ n')
      (step_ok_S_at fx n' IHn')).
Qed.
End top.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The pieces with a proof on the cut, discharged. The others stay named hypotheses with their owners.             *)
Section closed. Context {rc : YM05.RunCeil} {RL : PrhRoomLive}.
(* at preset's CfParams: pieces 6 / 9 / 10 (S8aOpen.v, S8aClose.v) are stated at cp := CfParams_preset (ev_mid's ledger
   reads the harness heads at cf_head = 16) *)
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Notation cp := CfParamsPreset.CfParams_preset.
(* the walk is at image A's PrhImg (frames, statics), as at its listing (S8aItemsTop.v) *)
#[local] Existing Instance prh_img_A.
#[local] Notation PI := prh_img_A.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

(* ---- the premises of the discharged pieces (texts verbatim from their files) ---- *)
(* the kit's allocator laws at ARx, at the harness head length (S8aEntry.v LAWS, S8aNumber.v LAWS) *)
(* PREMISE LAWS: S8aEntry.v:122. OWNER none named. AT THE BINDING: PROVED, YGcallcf.AR_laws_x_xs
   (Reusable/YGcallcf.v:336) of YG0lawscf.AR_laws_ok_cf (:22). *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* S8aEntry.v (piece 1) premises *)
(* PREMISE errno_low: S8aEntry.v:125. OWNER the image instance (PALib pal_env). AT THE BINDING: PROVED,
   PALibA.palib_errno_A (A/PALibA.v:46). *)
Hypothesis errno_low : api_env SEGS B.
(* PREMISE OWNLOW: S8aEntry.v:126. OWNER a Theorem Labs lane. AT THE BINDING: PROVED, YGcallcf.ARx_owned_low_law_xs
   (Reusable/YGcallcf.v:339) of AR_laws_ok_cf. *)
Hypothesis OWNLOW : YGcallx.ARx_owned_low_law SEGS B ARx.
(* ASM1 at every float state: S8aEntry.v states it at its section's fx *)
(* PREMISE ASM1: S8aEntry.v:135. OWNER a Theorem Labs lane's frame-class lane. AT THE BINDING: PROVED BY COMPOSITION, not
   yet written at A': YGcallMxmn.astack_malloc_realizes_xm_conj (:792) with YGcallScf.xs_placed_cf_set_fs (:139)
   over A/FCm01xm.v:32 stack_malloc1_contract_xm, fs_iface from FCifaceCf.fs_iface_ARcf (:131); the image-B wrapper
   is AU/FCxmCfxB.v:69. *)
Hypothesis ASM1 : forall fx1 : YK11.FPState, @YGcallMxmn.astack_malloc_realizes_xm fx1 SEGS B ARx 1.
(* PREMISE SMX: S8aEntry.v:137. OWNER a Theorem Labs lane. AT THE BINDING: PROVED, YGcallScf.stack_malloc_x_any
   (Reusable/YGcallScf.v:100). *)
Hypothesis SMX : forall ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
(* PREMISE TS: S8aEntry.v:144. OWNER the final image instance. AT THE BINDING: PROVED, AD2l.TfibB_syms
   (A/AD2l.v:73). *)
Hypothesis TS : AF0m.TfibSyms B.
(* PREMISE GOT_SHADOW: S8aEntry.v:147. OWNER the kit / the final image instance. AT THE BINDING: PROVED, pal_got_shadow
   (YC1fP.v:332) of PALibA.palib_A (A/PALibA.v:56). *)
Hypothesis GOT_SHADOW : as_got_shadow B = VAL (A_OBJ 0).
(* PREMISE GOT_UAR: S8aEntry.v:148. OWNER the kit / the final image instance. AT THE BINDING: PROVED, pal_got_uar
   (YC1fP.v:339) of palib_A. *)
Hypothesis GOT_UAR : as_got_uar B = VAL (A_OBJ 1).
(* PREMISE CELL_SHADOW: S8aEntry.v:149. OWNER the kit / the final image instance. AT THE BINDING: PROVED, pal_cell
   (YC1fP.v:333) of palib_A. *)
Hypothesis CELL_SHADOW : as_shadow_cell B = VAL (A_OBJ 12).
(* PREMISE UAR_CELL: S8aEntry.v:153. OWNER the kit / the final image instance. AT THE BINDING: OPEN: no A' lemma (the
   image-B one is B/Prog/ExvB_ImgFacts.v:159 exvi_eh_uar_cell, vm_compute + lia; as_uar_cell TfibB = 0xaaec0,
   A/AD2l.v:22). *)
Hypothesis UAR_CELL :
  4096 <= as_uar_cell B /\ as_uar_cell B + 4 <= kLowMemEnd /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= as_uar_cell B) /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= as_uar_cell B) /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= as_uar_cell B).
(* PREMISE HW: S8aEntry.v:160. OWNER a Theorem Labs lane. AT THE BINDING: PROVED, CfParamsPreset.preset_head_wide
   (A/CfParamsPreset.v:103). *)
Hypothesis HW : prh_head_wide.
(* S8aNumber.v (piece 5) premises *)
(* PREMISE HIMG: S8aNumber.v:65. OWNER none named. AT THE BINDING: PROVED, S8aNumberW.w_himg
   (A/Prog/S8aNumberW.v:35). *)
Hypothesis HIMG : S8aNumCut.ev_img_ok.
(* S8aNumber's HHEAD, closed at preset's CfParams (cf_head = 16) *)
Lemma HHEAD : 8 <= cf_head.
Proof. change (@cf_head CfParamsPreset.CfParams_preset) with 16. lia. Qed.
(* PREMISE HPST: S8aNumber.v:67. OWNER none named. AT THE BINDING: PROVED, S8aNumberW.w_hpst TfibB TfibB_syms
   (A/Prog/S8aNumberW.v:57). *)
Hypothesis HPST : forall z, Exists (in_zr z) (prh_pst (PI := PI)) -> in_img SEGS z /\ ~ (as_errno B <= z < as_errno B + 4).
(* PREMISE Htp: S8aNumber.v:69. OWNER none named. AT THE BINDING: PROVED, S8aNumberW.w_htp
   (A/Prog/S8aNumberW.v:45). *)
Hypothesis Htp : as_tp B = strtod_c.STRTOD_TP.
(* PREMISE Herrno: S8aNumber.v:70. OWNER none named. AT THE BINDING: PROVED, S8aNumberW.w_herrno
   (A/Prog/S8aNumberW.v:48). *)
Hypothesis Herrno : as_errno B = strtod_c.STRTOD_ERRNO.
(* PREMISE Hown: S8aNumber.v:71. OWNER none named. AT THE BINDING: PROVED, S8aNumberW.w_hown
   (A/Prog/S8aNumberW.v:51). *)
Hypothesis Hown : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
(* PREMISE HOFFB: S8aNumber.v:74. OWNER none named. AT THE BINDING: PROVED, FuzzFree.ff_blk_off_img
   (A/Prog/FuzzFree.v:423, on ARcf /\ xs_placed_cf; its IMG_LO / IMG_TOP are strtod_img_A's bounds by unfolding). *)
Hypothesis HOFFB : S8aNumCut.ev_blk_offimg B ARx strtod_row.strtod_img_A.
(* PREMISE HOFFF: S8aNumber.v:75. OWNER none named. AT THE BINDING: OPEN: no A' lemma puts a fake frame above the
   image band (route: YCbqG.frm_above_band_x :574; the image-B one is B/Prog/PvB_Inst.v:367 pvI_fs_hi). *)
Hypothesis HOFFF : S8aNumCut.ev_frm_offimg ARx strtod_row.strtod_img_A.
(* PREMISE HGOTC: S8aNumber.v:81. OWNER the image-A binding of B. AT THE BINDING: PROVED, S8aNumberW.w_hgotc
   (A/Prog/S8aNumberW.v:67) of AE22.canary_cell_in (A/AE22.v:33). *)
Hypothesis HGOTC : forall ly, In (z8 (ANum strtod_c.STRTOD_GOT_GUARD) strtod_c.STRTOD_GUARD) (as_const B ly).
(* the listing's sigma and relro bounds are written at PA explicitly: with image B's instance PI_prog_B also loaded
   (ExsA_Discharge / ExwA Require B modules), a bare `pa_sigma` resolves to image B's *)
#[local] Notation SIG := (@pa_sigma _ A_prog_listing PA).
(* PREMISE CPY: S8aNumber.v:82. OWNER the memcpy row's owner. AT THE BINDING: PROVED, PRowCpy.prow_asan_memcpy_xm_A
   (A/PRowCpy.v:29; pc 0x523e4 = SIG AS___asan_memcpy). *)
Hypothesis CPY : forall fx1, @YGcallMxmn.aintrin_realizes_xm fx1 SEGS B ARx OCpy (SIG AS___asan_memcpy).
(* PREMISE CMP: S8aNumber.v:83 (S8aStr.v:128 SCMP). OWNER a Theorem Labs lane. AT THE BINDING: PROVED,
   PSstrRo.ps_strcmp_xrom_xs_A (A/PSstrRo.v:68; pc 0x42d20 = SIG AS___wrap_strcmp). *)
Hypothesis CMP : forall fx1, @YGcallMxmn.astrcmp_realizes_xrom fx1 SEGS B ARx
  (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA) (SIG AS___wrap_strcmp).
(* PREMISE BCMP: S8aNumber.v:84 (ExwA.v:1382 BCMPm). OWNER the bcmp row's owner. AT THE BINDING: PROVED,
   PRowCmp.pr_bcmp_xm_A (A/PRowCmp.v:1297; pc 0x42d2c = SIG AS___wrap_bcmp). *)
Hypothesis BCMP : forall fx1, @YGcallMxmn.abcmp_realizes_xm fx1 SEGS B ARx (SIG AS___wrap_bcmp).
(* PREMISE HBLK32: S8aNumber.v:90. OWNER none named (comment: ARcf's AR_blocks_law_cf). AT THE BINDING: OPEN: no A'
   wrapper (route: YGcfBlockRange.ablock_n_lt_max_cf :70 of YG0scf.AR_blocks_law_ok_cf :532, cf_malloc_max < 2 ^
   32; the image-B one is B/Prog/ExvB_ImgFacts.v:200 exvi_eh_blk32). *)
Hypothesis HBLK32 : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> n < 2 ^ 32.
(* PREMISE HAMEM8: S8aNumber.v:94. OWNER two Theorem Labs lanes. AT THE BINDING: PROVED, no wrapper yet:
   YGcfBlockRange.block_amem_range8_cf (:46) / _k (:60) after unfolding ablocks (k := n; n = 0 by k := 0). *)
Hypothesis HAMEM8 : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  YGcallMx.amem_range8 p (req_size n).

(* ---- the pieces NOT YET discharged on the cut: NAMED, with their owners ---- *)
(* S8aStr.v (pieces 2 + 3 + 4, S8aStr.ev_disp) premises, texts verbatim; its STRX is STR below, its SCMP is CMP above *)
(* OWNER a Theorem Labs lane (cf layer): a live block's shadow and hull (S8aStr.v HSHD; at the instance AR_shadow_law_ok_cf) *)
(* PREMISE HSHD: S8aStr.v:97. OWNER a Theorem Labs lane (cf layer). AT THE BINDING: PROVED, YG0sshcf.AR_shadow_law_ok_cf
   (Reusable/YG0sshcf.v:160) on ARcf. *)
Hypothesis HSHD : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  block_shadow (aview SEGS (w_H W) mem) SHADOW_OFF (p + YG0dcf.hd_skip Hp p) (req_size n - YG0dcf.hd_skip Hp p) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) p (req_size n).
(* OWNER a Theorem Labs lane (block_amem_range8_cf's k-form): strcmp's amem_range8 for a live block (S8aStr.v HAM8) *)
(* PREMISE HAM8: S8aStr.v:133. OWNER a Theorem Labs lane. AT THE BINDING: PROVED, no wrapper yet:
   YGcfBlockRange.block_amem_range8_cf (:46) after unfolding ablocks (the image-B wrapper is
   B/Prog/ExvB_ImgFacts.v:206). *)
Hypothesis HAM8 : forall ly S Hp W mem md p n k, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= k <= n ->
  YGcallMx.amem_range8 p (k + 1).
(* the A' ex_string / ex_word walks' premises (the kit's working branch 4356951853dd, ExsA_Discharge.v /
   ExwA.v), texts verbatim: the listing's library cells (PALib; OWNER the kit / the final image instance, palib_A) and
   the strlen row in its xrom form at every float state (OWNER a Theorem Labs lane, as SCMP / CMP). ex_word's BCMPm is BCMP
   above. *)
(* PREMISE PAL: ExsA_Discharge.v:73 / ExwA.v:1379. OWNER the kit / the final image instance. AT THE BINDING: PROVED,
   PALibA.palib_A (A/PALibA.v:56). *)
Hypothesis PAL : YC1fP.PALib (L := A_prog_listing) (PI := PA) B.
(* PREMISE STRLENm: ExwA.v:1380. OWNER a Theorem Labs lane. AT THE BINDING: PROVED, PSstrRo.ps_strlen_xrom_xs_A
   (A/PSstrRo.v:77; rlo / rhi := A_prog_relro_lo / hi; pc 0x42d18). *)
Hypothesis STRLENm : forall fx : YK11.FPState, @YGcallMxmn.astrlen_realizes_xrom fx SEGS B ARx
  A_prog_relro_lo A_prog_relro_hi (A_prog_sigma AS___wrap_strlen).
(* piece 11 (exit), S8aExit.ev_exit_holds (a Theorem Labs lane, a working branch cb0b2fbcb4d, against the kit's ev_mid with the
   run-position keep, b45af6155b94), takes two Section premises beyond LAWS: HW (above) and
   ASFX, OWNER two Theorem Labs lanes: YGcallSx.v's frame-free law in ARx form, verbatim from S8aExit.v. At the cf
   instance it is Reusable/YGcallScf.v astack_free_x_xs (ARx := ARcf .. /\ xs_placed_cf ..). *)
(* PREMISE ASFX: S8aExit.v:411. OWNER two Theorem Labs lanes. AT THE BINDING: PROVED, YGcallScf.astack_free_x_xs
   (Reusable/YGcallScf.v:161). *)
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.

(* the ex_string walk at A', at every float state: STR for pieces 7 + 8 and STRX for pieces 2-4 *)
Lemma STR : forall fxc : YK11.FPState, @tex_string_specX fxc rc cp PI RL A_prog_listing PA B ARx SK.
Proof. exact (ExsA_Discharge.ex_string_holds_A_all (cp := cp) (RL := RL) B ARx SK LAWS HHEAD PAL). Qed.
(* the ex_word walk at A' (the cut's text, range premise ExwA.v:229), at every float state: WORDX for pieces 2-4 *)
Lemma WORDX : forall fx1 : YK11.FPState, @tex_word_specX fx1 rc cp PI RL A_prog_listing PA B ARx SK.
Proof. exact (ExwA.ex_word_holds_A_all (cp := cp) (RL := RL) B ARx SK LAWS PAL STRLENm BCMP). Qed.

(* piece 1, S8aEntry.ev_entry_holds, at every float state *)
Lemma P_ENTRY : forall fx, @ev_entry_spec fx rc cp PI RL A_prog_listing PA B ARx SK.
Proof.
intros fx. exact (@S8aEntry.ev_entry_holds fx rc cp RL SK B ARx LAWS errno_low OWNLOW (ASM1 fx) SMX TS
  GOT_SHADOW GOT_UAR CELL_SHADOW UAR_CELL HW).
Qed.
(* piece 5, S8aNumber.ev_number (a working branch deae66a28f58), at every float state *)
Lemma P_NUM : forall fx, @ev_number_spec fx rc cp PI RL A_prog_listing PA B ARx SK.
Proof.
intros fx. exact (@S8aNumber.ev_number fx rc cp PI RL B ARx SK LAWS HIMG HHEAD HPST Htp Herrno Hown HOFFB HOFFF
  HGOTC CPY CMP BCMP HBLK32 HAMEM8).
Qed.

(* pieces 7 + 8, S8aItemsTop.ev_item_holds_A (on the cut with the kit's re-fit f1dc92ee783b), at every float state *)
Lemma P_ITEM : forall fx n',
  (forall fxd, @tex_value_specX fxd rc cp PI RL A_prog_listing PA B ARx SK n') ->
  @ev_item_spec fx rc cp PI RL A_prog_listing PA B ARx SK n'.
Proof.
intros fx n' IH. exact (@S8aItemsTop.ev_item_holds_A fx rc cp B ARx SK RL LAWS
  (fun z Hz => proj1 (HPST z Hz)) STR CMP HAMEM8 n' IH).
Qed.

(* piece 6, S8aOpen.ev_items_open_holds (the kit's working branch), at every float state *)
Lemma P_OPEN : forall fx, @ev_items_open_spec fx rc cp PI RL A_prog_listing PA B ARx SK.
Proof. intros fx. exact (S8aOpen.ev_items_open_holds (fx := fx) (RL := RL) B ARx SK LAWS). Qed.
(* pieces 9 + 10, S8aClose.ev_items_close_holds, at every float state *)
Lemma P_CLOSE : forall fx, @ev_items_close_spec fx rc cp PI RL A_prog_listing PA B ARx SK.
Proof. intros fx. exact (S8aClose.ev_items_close_holds (fx := fx) (RL := RL) B ARx SK LAWS). Qed.
(* piece 10, S8aClose.ev_items_end_holds, at every float state *)
Lemma P_END : forall fx, @ev_items_end_spec fx rc cp PI RL A_prog_listing PA B ARx SK.
Proof. intros fx. exact (S8aClose.ev_items_end_holds (fx := fx) (RL := RL) B ARx SK LAWS). Qed.

(* pieces 2 + 3 + 4, S8aStr.ev_disp (a working branch 9ecaa8c58bc6, merged), at every float state *)
Lemma P_DISP : forall fx, @ev_disp_spec fx rc cp PI RL A_prog_listing PA B ARx SK.
Proof.
intros fx. eapply (S8aStr.ev_disp (fx := fx) (cp := cp) (RL := RL) B ARx SK); first [exact LAWS | exact HSHD | exact STR | exact CMP | exact HAM8 | exact WORDX | exact TS].
Qed.

(* piece 11, S8aExit.ev_exit_holds, at every float state *)
Lemma P_EXIT : forall fx, @ev_exit_spec fx rc cp PI RL A_prog_listing PA B ARx SK.
Proof. intros fx. exact (S8aExit.ev_exit_holds (fx := fx) (RL := RL) (SK := SK) B ARx LAWS ASFX HW). Qed.

(* ex_value on image A', at every nesting and every float state *)
Theorem ex_value_A : forall n fx, @tex_value_specX fx rc cp PI RL A_prog_listing PA B ARx SK n.
Proof. exact (ex_value_top B ARx SK P_ENTRY P_DISP P_NUM P_OPEN P_ITEM P_CLOSE P_END P_EXIT). Qed.
End closed.
