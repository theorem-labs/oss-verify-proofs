(* fuzz_preset image B' (asan-ubsan pin d663f82d7f48, #102), parse_value SEGMENT N (the number arm, B 0x86598 -> exit
   0x8664c): SEG_N's statement (PvB_Top.v's SEG_N) PROVED, from the eight segment lemmas (PvB_NA pnA, PvB_NB pnB, PvB_NC
   pnC_holds, PvB_ND pnD_holds, PvB_NE pnE, PvB_NF pnF, PvB_NTX pvn_TX, PvB_NQ pnQ) composed by PvB_NWalk.pvN_of_pieces,
   over the batch kit a working branch 240b06ed4fd4 (the CW / wild-room form of the cut, the
   budgeted exit body pv_body_x, the batch kit's post: the outcome pv_outc over the grant-all run, rd_ledger_move with g_most /
   run, rd_ledger_move with g_most / the grant-all trace / the refused peak, the free-order tie pv_ftie, pj_ncapR).
   rule 24: no function proved
   rule 24: proves no function (kind: composition of proved segment lemmas).
   The Section hypotheses are ARGUMENTS, each an instance, kit, call-row or image fact with a named source:
     LAWS        AR_laws_x at the instance (hl the head length)
     FMALLOC     the kit's fuzz_malloc call text tfuzz_malloc_specX at the batch kit's tip (lib/A/PRH_FnAlloc.v 240b06ed4fd4):
                 post-implication form, no position at entry, per-call byte premise guarded `cnt <> fail -> ..`; its
                 premises sec_cnt / ccnt24 at the call come from pv_pre's two live-count premises (PvB_NC.v), its post
                 gives the two position implications and the OUTCOME clause (a consumed granted request with no
                 injected failure returns no NULL: PvB_NCut.v pn_null_off), and prh_alloc_post's blocks give the live
                 list; m-form post via fpostm = apost_base_xm (keeps memnorm); its BODY is on the harness-fix hold list
    CPY STR     the __asan_memcpy text in its class-B memnorm-keeping form (YGcallMxmn.aintrin_realizes_xm; the row owner
                pays it from its run) and the strtod row (YStrtodRowX 10e84e44e24e, keeps aj_memnorm)
    MEMNORM is NOT a hypothesis: memnorm is a STATE fact, seeded by pv_at_N's last conjunct, carried by every internal cut
                (PvB_NCut.v) through YSRrMemnorm's runner / step twins and the calls' keeps
     HSHD        a block's shadow past its hidden head -> AR_laws_x field 14 alx_hshadow (ARx_hshadow_law_cf_ok at ARcf)
     HZS HKIMG   the shadow / hull of a read-only global and of an image string -> ARcf AR_zshadow_law_cf + aso_zshadow +
                 img_shadow_vis_cf (as FuzzStrdupB.v sd_src_shadow / :288)
     PA_BOX      the kit's kept_img / kept_at bounds pa_lo / pa_hi (per instance) lie inside the B' image box HZS is stated
                 over (MARKED instance fact, PvB_Inst.v pvI_pa_box; PvB_A_Home.v's PA_BOX, same text)
     PSTRO PSTOK the alloc.c statics are image bytes, not relro, not runtime-owned (MARKED image facts, PI_prog_B;
                 S1ImgB.v pst_not_ro_B)
    IMG_COVER B_errno  image facts at PI_prog_B (strtod row's site)
    IMG_GOTV IMG_GOTC  the strtod guard's GOT cell: srx_got_b (strtod_row.strtod_got_B at PI_prog_B) and its const cell
                (YE22.v canary_cell_in, Tfib_const_abs idx 169); replace the FALSE IMG_GOT (this walk's audit, 10:11Z)
     HEAD8       8 <= cf_head (CfParams_preset: 16)
     FS_HI       a live fake frame lies at or above IMG_TOP_B -> AR_laws_x field 17 alx_img's frm_above_band_x
                 (lib/Reusable/YCbqG.v, landing on the engine trunk)
     HHD         cf_head = PresetReqAt.HEAD (CfParams_preset: 16 = fuzz/alloc.c's HEAD): the number arm's fuzz_malloc
                 request is rd_hev's HMal event of the model's EAlloc (PvB_NC.v, M's room post)
   The interim K0_OKS_REFUSAL_RAN / _PEAK are DELETED and PvB_NOks.v is no longer used (no file Requires it): the refusal arm closes by the batch kit's re-keyed prh_oks
   and prh_refused_peak (PvB_NQ.v pnq_move_fail).
   No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP YGcallMx YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep YStrtodRowX YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_NCut PvB_NWalk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require strtod_c strtod_row.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require
  PvB_NA PvB_NB PvB_NC PvB_ND PvB_NE PvB_NF PvB_NTX PvB_NQ.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Instance PIBn : PrhImg := prh_img_B.

Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis FMALLOC : tfuzz_malloc_specX (fx := fx0) (cp := cp) (PI := prh_img_B) (PA := PA) B ARx SK.
Hypothesis CPY : forall fx1 : YK11.FPState, aintrin_realizes_xm (fx := fx1) SEGS B ARx OCpy (pa_sigma AS___asan_memcpy).
Hypothesis STR : astrtod_realizes_x SEGS B ARx strtod_row.strtod_img_B (pa_sigma AS_strtod) STK_RT_STRTOD
  strtod_c.strtod_model PvB_ND.pnd_txt_ok.
Hypothesis HSHD : forall ly S Hp W mem md b n, ARx ly S Hp W mem md -> In (b, n) (ablocks B ly S) -> In b Hp ->
  block_shadow (aview SEGS (w_H W) mem) SHADOW_OFF (b + cf_head) (req_size n - cf_head) /\
  (cf_head < req_size n -> shadow_hull_vis (aview SEGS (w_H W) mem) (b + cf_head) (req_size n - cf_head)).
Hypothesis HZS : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> in_zs B p n -> IMG_LO_B + 64 <= p ->
  p + n + 64 <= IMG_TOP_B ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\ (0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) p n).
Hypothesis HKIMG : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> kept_img B p n -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Hypothesis PA_BOX : IMG_LO_B <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA <= IMG_TOP_B.
Hypothesis PSTRO : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis PSTOK : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis IMG_COVER : forall a, IMG_LO_B <= a < IMG_TOP_B -> in_img SEGS a.
Hypothesis B_errno : as_errno B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_c.STRTOD_ERRNO.
Hypothesis IMG_GOTV : srx_got_b SEGS OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_c.STRTOD_GOT_GUARD OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_c.STRTOD_GUARD = true.
Hypothesis IMG_GOTC : forall ly, In (z8 (ANum OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_c.STRTOD_GOT_GUARD) OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.strtod_c.STRTOD_GUARD) (as_const B ly).
Hypothesis HEAD8 : 8 <= cf_head.
Hypothesis FS_HI : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  IMG_TOP_B <= frame_addr ly cid pos.
Hypothesis HHD : cf_head = PresetReqAt.HEAD.

(* SEG_N, as PvB_Top.v states it *)
Theorem pvN_seg : forall en W' ms mdc, pv_pre B ARx en -> pv_at_N B ARx en W' ms mdc ->
  (forall W2 ms2 md2, pv_at_exit B ARx en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK (SK := SK) B ARx en)) ->
  SRr SEGS W' (mkCfg ms mdc) (pv_FINK (SK := SK) B ARx en).
Proof.
  apply pvN_of_pieces.
  - eapply PvB_NA.pnA; eassumption.
  - eapply PvB_NB.pnB; eassumption.
  - eapply PvB_NC.pnC_holds; eassumption.
  - eapply PvB_ND.pnD_holds; eassumption.
  - eapply PvB_NE.pnE; eassumption.
  - eapply PvB_NF.pnF; eassumption.
  - eapply PvB_NTX.pvn_TX; [eassumption|]. eapply PvB_NQ.pnQ; eassumption.
Qed.
End c.

(* the brief's checks (the internal file bprime-pivot.md section 8): the statement and the cut definitions it reads, implicit arguments
   shown (the entry float state fx0 is pv_pre's / pv_FINAL's first implicit), and the axioms *)
Set Printing Implicit. Unset Printing Notations.
Check @pvN_seg.
Print pv_pre. Print pv_at_N. Print pv_at_exit. Print pv_Qm. Print pv_FINAL. Print pv_FINK. Print rp_post. Print rp_pos.
Print pv_outc. Print pv_ftie. Print pv_body_x.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions pvN_seg.
