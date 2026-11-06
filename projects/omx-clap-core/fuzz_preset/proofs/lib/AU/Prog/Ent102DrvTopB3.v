(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/AU/Prog/Ent102DrvTopB3.v, with its module paths and module names changed; 215 of its 321 lines of code are new or changed and 46 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102 pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa54d43160b): THE THIRD
   COMPOSED TOP of the B' driver. The second composed top Ent102DrvTopB2.TFIB_T_closed_B_walked2
   (lib/AU/Prog/Ent102DrvTopB2.v) with its Section hypotheses DISCHARGED BY CITATION of theorems already proved on
   the kit's cut 7cdbb61b5fa0, on the named branch of a file taken by path, or in the int102 base this line merges
   (a working branch 26d8d53a1503) - nothing re-proved - and its two Section
   variables instantiated, all in ONE composition, TFIB_T_room_all_B_walked3 (section 2): the driver's room form with
   walked2's citations and walked's values, from which walked3 and the halts top both follow. Every statement passes
   the B' instance explicitly (PA := PI_prog_B, B := YD2l.TfibB).
     H_txt_check_no_overread_B        a Theorem Labs lane's Cno102B_TopInst.cnb_B_top_inst (lib/B/Prog/Cno102B_TopInst.v:51;
                                      lib/B/Prog/Cno102B_*.v and lib/A/Prog/Cno102_FKit.v taken BY PATH from
                                      a working branch 811af66ffba2) at CTX0 := iface_ctx0: ASM3
                                      FCm3xm.stack_malloc3_contract_xm (lib/AU/FCm3xm.v:22) at ARcf, AMEMSET drv3_memset_B
                                      below (PRowSet.prow_asan_memset_xm_B, lib/AU/PRowSet.v:4361), HPN walked2's
                                      parse_noting walk at the shared drv3_pj_parse_B, HRO the driver's ran_out citation,
                                      HSAME drv3_same_B below, AFREE the shared drv3_afree_B, HPJF drv3_pj_free_B
                                      below, ASETSH FCxmCfxB.set_shadow_f5_contract_xm_cfx_B (lib/AU/FCxmCfxB.v:51); HPAD
                                      below;
     H_txt_check_as_written_B         a Theorem Labs lane's Caw102B_Img.caw_B_top_inst (lib/B/Prog/Caw102B_Img.v:185; Caw102B*.v and
                                      lib/A/Prog/S1ImgCheck.v taken BY PATH from a working branch
                                      03f709620169) at CTX0 := iface_ctx0: TEXV a Theorem Labs lane's ExvB_Inst.ex_value_holds_B_closed
                                      (lib/B/Prog/ExvB_Inst.v:174; its re-fitted closure, 19 files, taken BY PATH from
                                      a working branch da06c7c893b3, ExwB.v the blob of
                                      a working branch 66eac2b9522a), TEXWS a Theorem Labs lane's ex_ws_cf.ex_ws_holds_B
                                      (lib/B/Prog/ex_ws_cf.v:54, on the cut), TRO the driver's ran_out citation, AFREE the shared
                                      drv3_afree_B; AMALLOC below;
     H_txt_check_reject_clean_starved_B
                                      a Theorem Labs lane's CrsTopBp.crs_holds_Bp (lib/B/Prog/CrsTopBp.v:542; its files taken BY PATH
                                      from a working branch d664902eef28) at CTX0 := iface_ctx0: check_reject_clean
                                      and fuzz_alloc_live by walked2's citations, ran_out by the driver's, fuzz_alloc_count
                                      / fail by
                                      a Theorem Labs lane's FuzzAllocAccInstB102.fuzz_alloc_count_holds_B_inst / _fail_holds_B_inst
                                      (lib/B/Prog/FuzzAllocAccInstB102.v:59, :63), pj_parse by the shared drv3_pj_parse_B,
                                      HX_asmr FCxmCfxB.stack_malloc1_contract_xm_cfx_B (lib/AU/FCxmCfxB.v:69), fuzz_pick
                                      a Theorem Labs lane's FuzzPickB.fuzz_pick_holds_B (lib/B/Prog/FuzzPickB.v:859, taken BY PATH from
                                      a working branch 4e84fe3d6492), pj_write drv3_pj_write_B below;
                                      fuzz_free drv3_fuzz_free_B and fuzz_free_null drv3_fuzz_free_null_B below;
     H_txt_pj_free_B                  a Theorem Labs lane's pj_free_iface.tpj_free_specX_B_preset_iface (lib/B/Prog/pj_free_iface.v:68;
                                      lib/B/Prog/pj_free_*.v taken BY PATH from a working branch
                                      6cd31bea25de): XMS drv3_memset_B, XFF drv3_fuzz_free_B below;
     XM_LIB, XN_LIB                   := fun _ => 0: they occur neither in TFIB_T_closed_B nor in any remaining hypothesis.
   drv3_same_B (tsame_specX at DOC_D for cnb_B_top_inst's HSAME) is a Theorem Labs lane's SameB_final.same_holds_B_TfibBx
   (lib/B/Prog/SameB_final.v:62; SameB_defs.v, SameB_final.v, SameB_walk.v taken BY PATH from
   a working branch e95b6ce78e87), its strcmp row PSstrRo.ps_strcmp_xrom_xs_B (lib/AU/PSstrRo.v:69) at
   the B' relro bounds, its bcmp row the driver's PRowCmp citation (PresetD2pBPf.crc_bcmp_B_holds).
   drv3_pj_write_B (crs_holds_Bp's HT_pj_write) is a Theorem Labs lane's PRW_pj_writeB_Inst.pj_write_holds_B_inst
   (lib/B/Prog/PRW_pj_writeB_Inst.v:73; PRW_pj_writeB*.v taken BY PATH from a working branch
   0ff9ad9d007d, its lib/A/Prog/S7a_* closure from a working branch f75b9f6e6fa6, the same blobs) at
   CTX0 := iface_ctx0, n := DOC_D: HFREE drv3_fuzz_free_B; its argument pjw_ARGCNT by a Theorem Labs lane's
   PresetRoomCounts.counts_of_room_pos_rl (lib/Spec/PresetRoomCounts.v:60); HWV drv3_write_value_B and HPUT drv3_put_B
   below.
   drv3_put_B is a Theorem Labs lane's PutB.put_holds_B (lib/B/Prog/PutB.v:108; PutB*.v taken BY PATH from
   a working branch 6311be2a6bc0; that branch's S1ImgA.v / S1ImgB.v are NOT taken: the cut's stay,
   because cited files on this line name S1ImgA's checkers qualified, and PutB_Wit.v needs only S1ImgCheck.v, already
   here) with its memcpy row H_amc drv3_memcpy_B (PRowCpy.prow_asan_memcpy_xm_B) and H_real drv3_fuzz_realloc_B below;
   drv3_indent_B is a Theorem Labs lane's
   IndentB_Top.indent_holds_B (IndentB*.v taken BY PATH from a working branch 0638d3f403b4) with H_put
   drv3_put_B; drv3_write_value_B is a Theorem Labs lane's WriteValueB_Inst.write_value_holds_B (WriteValueB_*.v taken BY PATH
   from a working branch b42bebdaa929) with PUT drv3_put_B, INDENT drv3_indent_B, PUTSTR
   drv3_put_string_B; drv3_put_string_B is a Theorem Labs lane's PutStringB_SnpWit.put_string_holds_B_owner (PutStringB*.v taken
   BY PATH from a working branch 965ffedc8984) with PUT drv3_put_B, ASM0 drv3_asmr0_B (FCm01xm class 0),
   AMCPY drv3_memcpy_B, K := STK_RT_PRINTF and the snprintf row drv3_snprintf_B below; drv3_fuzz_free_B is a Theorem Labs lane's
   FuzzFreeB.fuzz_free_holds_B (lib/B/Prog/FuzzFreeB.v:910, on the cut) with AFREE the shared drv3_afree_B,
   PAL PALibB.exvi_eh_palib, pal_pst_ok FuzzAllocAccInstB102.acc_pal_pst_ok_B, pal_unpoison drv3_unpoison_pc_B and the
   unpoison row drv3_aunpoison_B below.
   THE UNPOISON / POISON ROWS drv3_aunpoison_B / drv3_apoison_B are a Theorem Labs lane's CfPoisonB102.preset_aunpoison_cf_B102 /
   preset_apoison_cf_B102 (lib/AU/CfPoisonB102.v, int102's POISONSWAP blob 7fda7f2b8c56 = a working branch
   415c6c3e2969, which cites a Theorem Labs lane's image-generic lemma CfApiPreset.poison_next_vis_cf INSIDE the file and has NO
   poison_next_vis_cf Section hypothesis), at the ARcf laws YG0lawscf.AR_laws_ok_cf and YD2l.TfibB_syms (two args, no
   stand-in). int102 carries poisonswap for both images.
   drv3_fuzz_realloc_B (put_holds_B's H_real) is a Theorem Labs lane's FuzzReallocB_p102.fuzz_realloc_holds_B'
   (lib/B/Prog/FuzzReallocB_p102.v:3003, taken BY PATH from a working branch 22328a9a605c) at
   B := TfibB, ARcfx = iface_ARx: OWN drv3_own_B, MALLOC drv3_fuzz_malloc_B, AUNPOISON drv3_aunpoison_B, PAL
   PALibB.exvi_eh_palib, pal_pst_ok FuzzAllocAccInstB102.acc_pal_pst_ok_B, pal_errno_relro
   CfAroPresetB.errno_relro_preset_AU, AREAL_cf drv3_arealloc_B below (the keep _k form).
   drv3_fuzz_malloc_B is a Theorem Labs lane's FuzzMallocB_p102_holds.fuzz_malloc_holds_B (row AL2; taken BY PATH from
   a working branch 21e4c03967d6: the cut's blob predates the kit's outcome conjunct): PAL, pal_pst_ok as
   above, AMALLOC the shared drv3_amalloc_B, OWN drv3_own_B. drv3_own_B is a Theorem Labs lane's OwnB_p102.own_holds_B
   (row AL6, lib/B/Prog/OwnB_p102.v:410, on the cut): PAL, pal_pst_ok as above, pal_poison by computation, APOISON
   drv3_apoison_B. (The composition is a Theorem Labs lane's lib/AU/HaltsClosedB.v own_B / fuzz_malloc_B / fuzz_realloc_B,
   a working branch dfa330bb66f0, a file not on this line.)
   drv3_snprintf_B (put_string_holds_B_owner's snprintf row) is a Theorem Labs lane's PSnpRowB.snprintf_row_B_inst
   (lib/B/Prog/PSnpRowB.v:57, taken BY PATH from a working branch 57c38d3b9706) at
   K := STK_RT_PRINTF (8160 <= K by computation); its cr snr_cr is PutStringB_SnpWit.psn_cr's body.
   drv3_aread_check_B (walked2's H_aread_check_stmt_cf_B) is a Theorem Labs lane's YD2mcfh.tfib_ARDCHK at TfibB (its TfibSyms by
   YD2l.TfibB_syms; the cfh set taken BY PATH from a working branch eb2778ca6e2f).
   THE SECTION HYPOTHESES OF THIS TOP: none. walked2's pj_parse text is drv3_pj_parse_B, Crt102TopInstB.ctiB_pjparse
   (cited, no premise).
   walked2's check_round_trip text is drv3_check_round_trip_B, Crt102TopInstB.crt102_topB_TfibB_inst (cited, no
   premise). cnb_B_top_inst's HPAD is drv3_padded_B, Padded102B_Inst.padded_B_at_PI_prog_B at TfibB
   (cited; its premises by this file's rows). fuzz_realloc_holds_B''s AREAL_cf is drv3_arealloc_B,
   AllocAssembleB.arealloc_realizes_cf_B (the same statement, cited). walked2's free row is drv3_afree_B,
   CfFreeKeepB.afree_realizes_cf_rh_keep_B (the same statement, cited). walked2's malloc row, at every float state,
   is drv3_amalloc_B, CfMallocKeepB.amalloc_realizes_cf_keep_closed_B (the same statement, cited).
   The live real stack (#102) is no premise: walked2 has none (the driver walk proves it from main's entry).
   rule 24: no function proved (kind: composition by citation). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK11 YM05 YG0d YG0f YGcfNames YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC4aP YPsym YCbqG YD2l YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn FCifaceCf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallScf YGcfHp YE22 YGcallSnp YGcallSnpCk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Listing_prog PAImg_prog PRH_ImgB PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset PRH_Base PRH_FnAlloc PRH_FnCheck PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnEx PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB PresetCfnB PresetD1preB PresetD1pB PresetD2pB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetD2pBPf PresetDrvTopBStmt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Ent102InstB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require Ent102DrvTopB2 Ent102SeamB.
(* the cited theorems' files (Required; cited by full path below) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PRowSet PRowCpy FCm01xm FCm3xm FCxmCfxB PSstrRo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Cno102B_TopInst Caw102B_Img CrsTopBp pj_free_iface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require SameB_defs SameB_final ex_ws_cf ExvB_Inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require FuzzAllocAccInstB102 PwPstUnownedB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require FuzzPickB PRW_pj_writeB PRW_pj_writeB_Inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PutB IndentB_Top WriteValueB_Inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PutStringB_SnpWit FuzzFreeB FuzzFreeNullB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfPoisonB102 CfAroPresetB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfApiPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require OwnB_p102 FuzzMallocB_p102_holds FuzzReallocB_p102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PSnpRowB Padded102B_Inst Crt102TopInstB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocKKeep YD2mcfh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AllocAssembleB CfFreeKeepB CfMallocKeepB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation PIc := PresetCfnB.preset_prh_img.
#[local] Abbreviation RLc := (@PRH_Base.prh_room_live_a8 CfParamsPreset.CfParams_preset).
#[local] Abbreviation SKc := PresetCfnB.preset_sink_head.
#[local] Abbreviation C0 := PresetCfnB.iface_ctx0.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation LB := Listing_prog.B_prog_listing.
#[local] Abbreviation PAr rc := (@PAImg_prog.PI_prog_B rc).
#[local] Abbreviation ARi rc :=
  (@PresetCfnB.iface_ARx rc Listing_prog.B_prog_listing (@PAImg_prog.PI_prog_B rc) CfImgB.CfImg_B YD2l.TfibB).
(* the driver's instances (lib/AU/PresetD2pBPf.v: ci := CfImg_B, cp := CfParams_preset, RL := prh_room_live_a8), so the
   callee texts below elaborate at them *)
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance PRH_Base.prh_room_live_a8.

(* pjw_ARGCNT, pj_write's one ruled argument (lib/B/Prog/PRW_pj_writeB.v, the A' text's twin): at every state pj_write's
   journal reaches with a model-run position, the class-24 live count is at most L24 + DRV. That is the second
   conjunct of PresetRoomCounts.counts_of_room_pos_rl at that position. *)
Ltac drv3_argcnt :=
  intros; hnf; intros;
  lazymatch goal with |- YGcfRoomLive.ccnt24 ?S' <= _ =>
    match goal with Hp : PresetRoomPos.iface_room_pos _ _ _ _ _ _ S' |- _ =>
      exact (proj2 (PresetRoomCounts.counts_of_room_pos_rl _ _ _ _ _ _ _ Hp)) end end.

(* ---------------------------------------------------------------------- *)
(* 1. The discharges that need no Section hypothesis. *)

(* the __asan_memset row at PI_prog_B's pc (cnb_B_top_inst's AMEMSET, tpj_free_specX_B_preset_iface's XMS):
   a Theorem Labs lane's PRowSet.prow_asan_memset_xm_B at the code record's pc, which is the listing's by computation on the
   closed terms (as lib/A/Prog/S6ImgWit.v s6w_aim does at A') *)
Lemma drv3_memset_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState) ARx (hl : Z),
  YCbqG.AR_laws_x (@YC4aP.pa_segs rc LB (PAr rc)) TB ARx hl ->
  YGcallMxmn.aintrin_realizes_xm (fx := fz) (@YC4aP.pa_segs rc LB (PAr rc)) TB ARx YG0d.OSet
    (@YC4aP.pa_sigma rc LB (PAr rc) YPsym.AS___asan_memset).
Proof.
intros rc fz ARx hl HL.
assert (E : @YC4aP.pa_sigma rc LB (PAr rc) YPsym.AS___asan_memset = YG0f.pc_asan_memset (YG0f.as_code TB))
  by (vm_compute; reflexivity).
rewrite E. exact (PRowSet.prow_asan_memset_xm_B (fx := fz) TB ARx hl HL YD2l.TfibB_syms).
Qed.

(* the __asan_memcpy row at PI_prog_B's pc (put_holds_B's H_amc): a Theorem Labs lane's PRowCpy.prow_asan_memcpy_xm_B
   (lib/AU/PRowCpy.v:31) at the code record's pc, the listing's by computation on the closed terms, as drv3_memset_B *)
Lemma drv3_memcpy_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState) ARx (hl : Z),
  YCbqG.AR_laws_x (@YC4aP.pa_segs rc LB (PAr rc)) TB ARx hl ->
  YGcallMxmn.aintrin_realizes_xm (fx := fz) (@YC4aP.pa_segs rc LB (PAr rc)) TB ARx YG0d.OCpy
    (@YC4aP.pa_sigma rc LB (PAr rc) YPsym.AS___asan_memcpy).
Proof.
intros rc fz ARx hl HL.
assert (E : @YC4aP.pa_sigma rc LB (PAr rc) YPsym.AS___asan_memcpy = YG0f.pc_asan_memcpy (YG0f.as_code TB))
  by (vm_compute; reflexivity).
rewrite E. exact (PRowCpy.prow_asan_memcpy_xm_B (fx := fz) TB ARx hl HL YD2l.TfibB_syms).
Qed.

(* tsame_specX at DOC_D (cnb_B_top_inst's HSAME) *)
Lemma drv3_same_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnEx.tsame_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TB (ARi rc) SKc PRH_Base.DOC_D.
Proof.
intros rc fx.
refine (SameB_final.same_holds_B_TfibBx (fx := fx) (rc := rc) SKc _ _ PRH_Base.DOC_D).
- pose proof (PSstrRo.ps_strcmp_xrom_xs_B (fx := fx) (rc := rc) (cp := CP) TB YD2l.TfibB_syms
    PAImg_prog.B_prog_relro_lo PAImg_prog.B_prog_relro_hi) as H.
  match type of H with YGcallMxmn.astrcmp_realizes_xrom _ _ _ _ _ ?p =>
    replace SameB_defs.SMB_STRCMP with p; [exact H | apply Z.eqb_eq; vm_compute; reflexivity] end.
- exact (PresetD2pBPf.crc_bcmp_B_holds rc fx).
Qed.

(* tex_ws_specX (caw_B_top_inst's TEXWS) *)
Lemma drv3_ex_ws_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnEx.tex_ws_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TB (ARi rc) SKc.
Proof. intros rc fx. exact (ex_ws_cf.ex_ws_holds_B (fx := fx) (rc := rc) SKc). Qed.

(* tex_value_specX at DOC_D (caw_B_top_inst's TEXV) *)
Lemma drv3_ex_value_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnEx.tex_value_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TB (ARi rc) SKc PRH_Base.DOC_D.
Proof. intros rc fx. exact (ExvB_Inst.ex_value_holds_B_closed (rc := rc) SKc PRH_Base.DOC_D fx). Qed.

(* tfuzz_pick_specX (crs_holds_Bp's HT_fuzz_pick) *)
Lemma drv3_fuzz_pick_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnCheck.tfuzz_pick_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TB (ARi rc) SKc.
Proof. intros rc fx. exact (FuzzPickB.fuzz_pick_holds_B rc fx). Qed.

(* crs_holds_Bp's HT_fuzz_alloc_count / HT_fuzz_alloc_fail *)
Lemma drv3_fuzz_alloc_count_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.tfuzz_alloc_count_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TB (ARi rc) SKc.
Proof. intros rc fx. exact (FuzzAllocAccInstB102.fuzz_alloc_count_holds_B_inst (fx := fx) (rc := rc) (SK := SKc)). Qed.
Lemma drv3_fuzz_alloc_fail_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.tfuzz_alloc_fail_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TB (ARi rc) SKc.
Proof. intros rc fx. exact (FuzzAllocAccInstB102.fuzz_alloc_fail_holds_B_inst (fx := fx) (rc := rc) (SK := SKc)). Qed.

(* the class-0 frame-area row at ARcf /\ xs_placed_cf (put_string_holds_B_owner's ASM0): a Theorem Labs lane's
   FCm01xm.stack_malloc0_contract_xm (lib/AU/FCm01xm.v:25) at ARcf, kept across the conjunct by
   YGcallMxmn.astack_malloc_realizes_xm_conj, as the A' top's drv3_asmr0_A *)
Lemma drv3_asmr0_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.astack_malloc_realizes_xm (fx := fx) YB1v.tfibsegs TB
    (fun ly S Hp W mem md => YG0ncf.ARcf (rc := rc) (cp := CP) YB1v.tfibsegs TB ly S Hp W mem md /\
       YG0ncf.xs_placed_cf (rc := rc) ly S) 0.
Proof.
intros rc fx.
exact (YGcallMxmn.astack_malloc_realizes_xm_conj (fx := fx) YB1v.tfibsegs TB (YG0ncf.ARcf (rc := rc) (cp := CP) YB1v.tfibsegs TB)
  (fun ly S => YG0ncf.xs_placed_cf (rc := rc) ly S) 0 YGcallScf.xs_placed_cf_set_fs
  (FCm01xm.stack_malloc0_contract_xm (fx := fx) TB (YG0ncf.ARcf (rc := rc) (cp := CP) YB1v.tfibsegs TB)
    (FCifaceCf.fs_iface_ARcf (cp := CP) YB1v.tfibsegs TB (YG0lawscf.AR_laws_ok_cf (cp := CP) YB1v.tfibsegs TB))
    YD2l.TfibB_syms)).
Qed.

(* fuzz_free_holds_B's pal_unpoison: the listing's __asan_unpoison_memory_region is CfImg_B's unpoison pc, by
   computation on the closed terms (as lib/B/Prog/PItems_inst.v pii_unpoison states it) *)
Lemma drv3_unpoison_pc_B : forall rc : YM05.RunCeil,
  @YC4aP.pa_sigma rc LB (PAr rc) YPsym.AS___asan_unpoison_memory_region = @YGcfNames.cf_pc_unpoison CfImgB.CfImg_B.
Proof. intros rc. vm_compute. reflexivity. Qed.

(* the unpoison / poison rows at TfibB (header): CfPoisonB102's rows, poison_next_vis_cf by CfApiPreset's lemma *)
Lemma drv3_aunpoison_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @YGcfHp.aunpoison_realizes_cf fx rc CfImgB.CfImg_B CfParamsPreset.CfParams_preset YB1v.tfibsegs YD2l.TfibB.
Proof.
intros rc fx.
exact (CfPoisonB102.preset_aunpoison_cf_B102 (fx := fx) (rc := rc) TB
  (YG0lawscf.AR_laws_ok_cf (cp := CP) YB1v.tfibsegs TB) YD2l.TfibB_syms).
Qed.
Lemma drv3_apoison_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @YGcfHp.apoison_realizes_cf fx rc CfImgB.CfImg_B CfParamsPreset.CfParams_preset YB1v.tfibsegs YD2l.TfibB.
Proof.
intros rc fx.
exact (CfPoisonB102.preset_apoison_cf_B102 (fx := fx) (rc := rc) TB
  (YG0lawscf.AR_laws_ok_cf (cp := CP) YB1v.tfibsegs TB) YD2l.TfibB_syms).
Qed.

(* fuzz_malloc_holds_B's and fuzz_realloc_holds_B''s OWN (header): a Theorem Labs lane's OwnB_p102.own_holds_B at TfibB *)
Lemma drv3_own_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.town_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (L := LB) (PA := PAr rc) TB (ARi rc) SKc.
Proof.
intros rc fx.
eapply (OwnB_p102.own_holds_B (fx := fx) (rc := rc) (ci := CfImgB.CfImg_B) (SK := SKc) TB);
  first [ exact PALibB.exvi_eh_palib | exact FuzzAllocAccInstB102.acc_pal_pst_ok_B | exact (drv3_apoison_B rc fx)
        | (apply Z.eqb_eq; vm_compute; reflexivity) ].
Qed.

(* put_string_holds_B_owner's snprintf row (header): a Theorem Labs lane's PSnpRowB.snprintf_row_B_inst at K := STK_RT_PRINTF *)
Lemma drv3_snprintf_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallSnp.asnprintf_realizes_xrom (fx := fx) (@YC4aP.pa_segs rc LB (PAr rc)) TB (ARi rc)
    (@YC4aP.pa_relro_lo rc LB (PAr rc)) (@YC4aP.pa_relro_hi rc LB (PAr rc))
    (YGcallSnpCk.FF_esc (@YC4aP.pa_lo rc LB (PAr rc)) YE22.A_GOT_CANARY) PRH_Base.STK_RT_PRINTF
    YE22.A_GOT_CANARY YE22.V_GOT_CANARY (@YC4aP.pa_lo rc LB (PAr rc)) (@YC4aP.pa_hi rc LB (PAr rc))
    (PutStringB_SnpWit.psn_cr (rc := rc)) (@YC4aP.pa_sigma rc LB (PAr rc) YPsym.AS___wrap_snprintf).
Proof.
intros rc fx.
exact (PSnpRowB.snprintf_row_B_inst (rc := rc) PRH_Base.STK_RT_PRINTF ltac:(apply Z.leb_le; vm_compute; reflexivity) fx).
Qed.

(* THE READ INTERCEPTOR'S CHECK (walked2's H_aread_check_stmt_cf_B): a Theorem Labs lane's YD2mcfh.tfib_ARDCHK
   (lib/Reusable/YD2mcfh.v, the cfh set taken BY PATH from a working branch eb2778ca6e2f) at TfibB, its
   one Section hypothesis TfibSyms by YD2l.TfibB_syms; its aread_check_stmt is PresetD1preB.aread_check_stmt_cf by
   conversion, at fx := YK11.fx0, cp := CfParams_preset *)
Lemma drv3_aread_check_B : forall rc : YM05.RunCeil,
  PresetD1preB.aread_check_stmt_cf (fx := YK11.fx0) (rc := rc) (ci := CfImgB.CfImg_B)
    (cp := CfParamsPreset.CfParams_preset) YD2l.TfibB.
Proof. intros rc. exact (YD2mcfh.tfib_ARDCHK YD2l.TfibB YD2l.TfibB_syms). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE THIRD COMPOSED TOP. *)
Section walked3.

(* the allocator rows, malloc and free in their keep forms (free primed, under the re-hide); amalloc at every float
   state, as walked2 states it. Each callee here (FuzzFreeB, FuzzMallocB_p102_holds, Cno102B_TopInst, Caw102B_Img)
   takes the keep rows themselves, so each gets the row as it is. *)
(* the malloc row: CfMallocKeepB.amalloc_realizes_cf_keep_closed_B, the same statement *)
Lemma drv3_amalloc_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fx) (rc := rc) (ci := CfImgB.CfImg_B)
    (cp := CfParamsPreset.CfParams_preset) YB1v.tfibsegs YD2l.TfibB.
Proof. intros rc fx. exact (CfMallocKeepB.amalloc_realizes_cf_keep_closed_B (fx := fx) (rc := rc)). Qed.
(* the free row: CfFreeKeepB.afree_realizes_cf_rh_keep_B, the same statement *)
Lemma drv3_afree_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fx) (rc := rc) (ci := CfImgB.CfImg_B)
    (cp := CfParamsPreset.CfParams_preset) YB1v.tfibsegs YD2l.TfibB.
Proof. intros rc fx. exact (CfFreeKeepB.afree_realizes_cf_rh_keep_B (fx := fx) (rc := rc)). Qed.
(* (the read interceptor's check is now cited: drv3_aread_check_B above) *)
(* walked2's pj_parse text at every cursor set: Crt102TopInstB.ctiB_pjparse, the pj_parse walk at the instance
   (CTX0 := iface_ctx0), with no premise *)
Lemma drv3_pj_parse_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CW : list (list Z)),
  PRH_FnPj.tpj_parse_specX (fx := fx) (cp := CP) (PI := PIc) (RL := RLc) (PA := PAr rc) TB (ARi rc) SKc C0 CW.
Proof. intros rc fx CW. exact (@Crt102TopInstB.ctiB_pjparse rc fx CW). Qed.
(* walked2's check_round_trip text: Crt102TopInstB.crt102_topB_TfibB_inst, the round-trip corollary at the instance
   (CTX0 := iface_ctx0, the literals Ent102InstB.ia_mod_at / ia_stamp), with no premise *)
Lemma drv3_check_round_trip_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pBPf.txt_check_round_trip_B fx rc Ent102InstB.ia_mod_at Ent102InstB.ia_stamp.
Proof. intros rc fx. exact (@Crt102TopInstB.crt102_topB_TfibB_inst rc fx). Qed.
(* THE CITED WALKS' OPEN CALLEE TEXTS AND ROWS, each once, at the driver's instance *)
(* cnb_B_top_inst's HPAD: the kit's tpadded_specX at the instance, Padded102B_Inst.padded_B_at_PI_prog_B at TfibB, its
   premises TB YD2l.TfibB_syms, AMALLOC drv3_amalloc_B, the memcpy / memset rows drv3_memcpy_B / drv3_memset_B at the
   instance's relation, and the read-only link Padded102B_Inst.pdi_aro_link_B at CfImg_B *)
Lemma drv3_padded_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnCheck.tpadded_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TB (ARi rc) SKc C0.
Proof.
intros rc fx.
exact (Padded102B_Inst.padded_B_at_PI_prog_B (fx := fx) (rc := rc) (ci := CfImgB.CfImg_B) (SK := SKc) TB
  YD2l.TfibB_syms (drv3_amalloc_B rc fx)
  (drv3_memcpy_B rc fx _ _ (YGcallcf.AR_laws_x_xs (cp := CP) _ TB (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TB)))
  (drv3_memset_B rc fx _ _ (YGcallcf.AR_laws_x_xs (cp := CP) _ TB (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TB)))
  (Padded102B_Inst.pdi_aro_link_B (rc := rc) TB YD2l.TfibB_syms) C0).
Qed.
(* fuzz_realloc_holds_B''s AREAL_cf: the realloc wrapper's row at the second allocator in its keep _k form
   (YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep, the leaf's memnorm keep and the room at k), at the instance:
   AllocAssembleB.arealloc_realizes_cf_B, the same statement *)
Lemma drv3_arealloc_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (Hp : list Z) (k : nat),
  YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (fx := fx) (rc := rc) (ci := CfImgB.CfImg_B) (cp := CP)
    (@YC4aP.pa_segs rc LB (PAr rc)) YD2l.TfibB Hp (@YC4aP.pa_sigma rc LB (PAr rc) YPsym.AS___wrap_realloc) k.
Proof. exact AllocAssembleB.arealloc_realizes_cf_B. Qed.

(* tfuzz_free_specX (crs_holds_Bp's HT_fuzz_free, tpj_free_specX_B_preset_iface's XFF, pj_write_holds_B_inst's HFREE):
   a Theorem Labs lane's FuzzFreeB.fuzz_free_holds_B (lib/B/Prog/FuzzFreeB.v:910, on the cut) at ARcfx = iface_ARx: AFREE the
   shared drv3_afree_B, AUNPOISON drv3_aunpoison_B, PAL PALibB.exvi_eh_palib, pal_pst_ok
   FuzzAllocAccInstB102.acc_pal_pst_ok_B, pal_unpoison drv3_unpoison_pc_B (as lib/B/Prog/PItems_compose.v:222 cites it),
   TS YD2l.TfibB_syms *)
Lemma drv3_fuzz_free_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.tfuzz_free_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TB (ARi rc) SKc.
Proof.
intros rc fx.
exact (FuzzFreeB.fuzz_free_holds_B (fx := fx) (rc := rc) (SK := SKc) TB
  (drv3_afree_B rc fx)
  (drv3_aunpoison_B rc fx) PALibB.exvi_eh_palib
  FuzzAllocAccInstB102.acc_pal_pst_ok_B (drv3_unpoison_pc_B rc) YD2l.TfibB_syms).
Qed.

(* tfuzz_free_null_specX (crs_holds_Bp's HT_fuzz_free_null): the kit's FuzzFreeNullB.fuzz_free_null_holds_B at TfibB, its
   rows AUNPOISON drv3_aunpoison_B, PAL PALibB.exvi_eh_palib and pal_pst_ok FuzzAllocAccInstB102.acc_pal_pst_ok_B *)
Lemma drv3_fuzz_free_null_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.tfuzz_free_null_specX (fx := fx) (PI := PIc) (PA := PAr rc) TB (ARi rc) SKc.
Proof.
intros rc fx.
eapply (FuzzFreeNullB.fuzz_free_null_holds_B (fx := fx) (rc := rc) (SK := SKc) TB);
  first [ exact (drv3_aunpoison_B rc fx) | exact PALibB.exvi_eh_palib | exact FuzzAllocAccInstB102.acc_pal_pst_ok_B
        | exact (drv3_unpoison_pc_B rc) | exact YD2l.TfibB_syms ].
Qed.

(* fuzz_realloc_holds_B''s MALLOC (header): a Theorem Labs lane's FuzzMallocB_p102_holds.fuzz_malloc_holds_B at TfibB *)
Lemma drv3_fuzz_malloc_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.tfuzz_malloc_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (L := LB) (PA := PAr rc) TB (ARi rc) SKc.
Proof.
intros rc fx.
eapply (FuzzMallocB_p102_holds.fuzz_malloc_holds_B (fx := fx) (rc := rc) (SK := SKc) TB);
  first [ exact PALibB.exvi_eh_palib | exact FuzzAllocAccInstB102.acc_pal_pst_ok_B
        | exact (drv3_amalloc_B rc fx)
        | exact (drv3_own_B rc fx) | exact YD2l.TfibB_syms ].
Qed.

(* put_holds_B's H_real (header): a Theorem Labs lane's FuzzReallocB_p102.fuzz_realloc_holds_B' at TfibB; its pal_errno_relro
   (errno_relro_t at CfImg_B) is CfAroPresetB.errno_relro_preset_AU, as Caw102B_Img.v cites it *)
Lemma drv3_fuzz_realloc_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.tfuzz_realloc_specX (fx := fx) (rc := rc) (ci := CfImgB.CfImg_B) (cp := CP) (RL := RLc) (PI := PIc) (L := LB)
    (PA := PAr rc) TB (ARi rc) SKc.
Proof.
intros rc fx.
eapply (FuzzReallocB_p102.fuzz_realloc_holds_B' (fx := fx) (rc := rc) (SK := SKc) TB);
  first [ exact (drv3_own_B rc fx) | exact (drv3_fuzz_malloc_B rc fx) | exact (drv3_aunpoison_B rc fx)
        | exact (drv3_arealloc_B rc fx) | exact PALibB.exvi_eh_palib
        | exact FuzzAllocAccInstB102.acc_pal_pst_ok_B | exact (CfAroPresetB.errno_relro_preset_AU TB YD2l.TfibB_syms) ].
Qed.

(* pj_write_holds_B_inst's HPUT, IndentB_Top's H_put and write_value_holds_B's PUT: a Theorem Labs lane's PutB.put_holds_B
   (lib/B/Prog/PutB.v:108; PutB*.v taken BY PATH from a working branch 6311be2a6bc0), its H_real
   drv3_fuzz_realloc_B and H_amc drv3_memcpy_B *)
Lemma drv3_put_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CTX0 : list (list Z)),
  PRH_FnWriter.tput_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TB (ARi rc) SKc CTX0.
Proof.
intros rc fx CTX0.
exact (PutB.put_holds_B (fx := fx) (rc := rc) (SK := SKc) (drv3_fuzz_realloc_B rc fx)
  (drv3_memcpy_B rc fx _ _ (YGcallcf.AR_laws_x_xs (cp := CP) _ TB (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TB))) CTX0).
Qed.

(* write_value_holds_B's INDENT: a Theorem Labs lane's IndentB_Top.indent_holds_B (lib/B/Prog/IndentB_Top.v:76; IndentB*.v taken
   BY PATH from a working branch 0638d3f403b4), its H_put drv3_put_B at every universe closure *)
Lemma drv3_indent_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnWriter.tindent_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TB (ARi rc) SKc C0.
Proof.
intros rc fx.
exact (IndentB_Top.indent_holds_B (fx := fx) (rc := rc) (SK := SKc) (fun CTX0 => drv3_put_B rc fx CTX0) C0).
Qed.

(* write_value_holds_B's PUTSTR: a Theorem Labs lane's PutStringB_SnpWit.put_string_holds_B_owner (lib/B/Prog/PutStringB_SnpWit.v:186;
   PutStringB*.v taken BY PATH from a working branch 965ffedc8984) at CTX0 := iface_ctx0: PUT drv3_put_B,
   ASM0 drv3_asmr0_B, AMCPY drv3_memcpy_B, K := STK_RT_PRINTF; the snprintf row drv3_snprintf_B *)
Lemma drv3_put_string_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnWriter.tput_string_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TB (ARi rc) SKc C0.
Proof.
intros rc fx.
exact (PutStringB_SnpWit.put_string_holds_B_owner (rc := rc) (SK := SKc) C0 (fun fz => drv3_put_B rc fz C0)
  (fun fz => drv3_asmr0_B rc fz)
  (fun fz => drv3_memcpy_B rc fz _ _ (YGcallcf.AR_laws_x_xs (cp := CP) _ TB (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TB)))
  PRH_Base.STK_RT_PRINTF (Z.le_refl _) (fun fz => drv3_snprintf_B rc fz) fx).
Qed.

(* pj_write_holds_B_inst's HWV: a Theorem Labs lane's WriteValueB_Inst.write_value_holds_B (lib/B/Prog/WriteValueB_Inst.v:71;
   WriteValueB_*.v taken BY PATH from a working branch b42bebdaa929) at every depth *)
Lemma drv3_write_value_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (n : nat),
  PRH_FnWriter.twrite_value_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TB (ARi rc) SKc C0 n.
Proof.
intros rc fx n.
exact (WriteValueB_Inst.write_value_holds_B (fx := fx) (rc := rc) SKc C0 (fun fx' => drv3_put_B rc fx' C0)
  (fun fx' => drv3_put_string_B rc fx') (fun fx' => drv3_indent_B rc fx') n).
Qed.

(* H_txt_pj_free_B *)
Lemma drv3_pj_free_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState), PresetD2pBPf.txt_pj_free_B fx rc.
Proof.
intros rc fx.
exact (pj_free_iface.tpj_free_specX_B_preset_iface (fx := fx) (rc := rc) (ci := CfImgB.CfImg_B) (RL := RLc) (SK := SKc)
  (drv3_fuzz_free_B rc fx)
  (drv3_memset_B rc fx _ _ (YGcallcf.AR_laws_x_xs (cp := CP) _ TB (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TB)))
  C0 PRH_Base.DOC_D).
Qed.

(* crs_holds_Bp's HT_pj_write *)
Lemma drv3_pj_write_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnWriter.tpj_write_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TB (ARi rc) SKc C0
    PRH_Base.DOC_D.
Proof.
intros rc fx.
refine (PRW_pj_writeB_Inst.pj_write_holds_B_inst (fx := fx) (rc := rc) SKc C0
  (fun n => drv3_write_value_B rc fx n) (fun fx0 => drv3_put_B rc fx0 C0) (fun fx0 => drv3_fuzz_free_B rc fx0)
  PRH_Base.DOC_D _).
drv3_argcnt.
Qed.

(* H_txt_check_no_overread_B *)
Lemma drv3_check_no_overread_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pBPf.txt_check_no_overread_B fx rc.
Proof.
intros rc fx.
exact (Cno102B_TopInst.cnb_B_top_inst (fx := fx) (rc := rc) (SK := SKc) C0
  (fun fz => FCm3xm.stack_malloc3_contract_xm (fx := fz) TB (YG0ncf.ARcf (rc := rc) (cp := CP) YB1v.tfibsegs TB)
     (FCifaceCf.fs_iface_ARcf (cp := CP) YB1v.tfibsegs TB (YG0lawscf.AR_laws_ok_cf (cp := CP) YB1v.tfibsegs TB))
     YD2l.TfibB_syms)
  (fun fz => drv3_memset_B rc fz _ _ (YGcallcf.AR_laws_x_xs (cp := CP) _ TB (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TB)))
  (fun fz => drv3_padded_B rc fz)
  (fun fz => Ent102DrvTopB2.drv2_parse_noting_B drv3_pj_parse_B rc fz)
  (fun fz => PresetD2pBPf.txt_fuzz_alloc_ran_out_B_holds rc fz)
  (fun fz => drv3_same_B rc fz)
  (fun fz => drv3_afree_B rc fz)
  (fun fz => drv3_pj_free_B rc fz)
  (fun fz => FCxmCfxB.set_shadow_f5_contract_xm_cfx_B (rc := rc) TB YD2l.TfibB_syms fz)).
Qed.

(* H_txt_check_as_written_B *)
Lemma drv3_check_as_written_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pBPf.txt_check_as_written_B fx rc.
Proof.
intros rc fx.
exact (Caw102B_Img.caw_B_top_inst (fx := fx) (rc := rc) (SK := SKc)
  (fun fz => drv3_ex_value_B rc fz) (fun fz => drv3_ex_ws_B rc fz)
  (fun fz => PresetD2pBPf.txt_fuzz_alloc_ran_out_B_holds rc fz)
  (fun fz => drv3_afree_B rc fz)
  (fun fz => drv3_amalloc_B rc fz) C0).
Qed.

(* H_txt_check_reject_clean_starved_B *)
Lemma drv3_check_reject_clean_starved_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pBPf.txt_check_reject_clean_starved_B fx rc.
Proof.
intros rc fx.
exact (CrsTopBp.crs_holds_Bp (fx := fx) (rc := rc) (ci := CfImgB.CfImg_B) (RL := RLc) (SK := SKc) C0
  (fun fy => Ent102DrvTopB2.drv2_check_reject_clean_B rc fy) (fun fy => drv3_fuzz_alloc_count_B rc fy)
  (fun fy => drv3_fuzz_alloc_fail_B rc fy) (fun fy => Ent102DrvTopB2.drv2_fuzz_alloc_live_B rc fy)
  (fun fy => PresetD2pBPf.txt_fuzz_alloc_ran_out_B_holds rc fy) (fun fy => drv3_fuzz_free_B rc fy)
  (fun fy => drv3_fuzz_free_null_B rc fy)
  (fun fy CW => drv3_pj_parse_B rc fy CW) (fun fy => drv3_fuzz_pick_B rc fy) (fun fy => drv3_pj_write_B rc fy)
  (FCxmCfxB.stack_malloc1_contract_xm_cfx_B (rc := rc) fx)).
Qed.

(* THE ONE COMPOSITION of this file's discharges: the driver's ROOM form (lib/AU/PresetD2pBPf.v
   TFIB_T_room_all_B_closed) at the walk's values (sm := ReaderRes.jr_strtod; XM_LIB / XN_LIB := fun _ => 0, which
   occur in no statement here; PAYLOAD_ROOM := fun _ => True; a_mod_at / a_stamp := Ent102InstB.ia_mod_at / ia_stamp;
   the harness slot by the seam Ent102SeamB.preset_lib_x_stmt_B_holds), with the rows and callee texts above and
   walked2's citations (drv2_aintrin_cpy_B, drv2_aintrin_set_B, drv2_stack_malloc_cfm_B, and drv2_parse_noting_B at
   drv3_pj_parse_B). walked3 below and the halts top (lib/AU/PresetClosedTopsB.v) both take it, so the list of
   discharges is written once. *)
Lemma TFIB_T_room_all_B_walked3 : PresetDrvTopBStmt.TFIB_T_room_all_concl_B (fun _ => True).
Proof.
exact (PresetD2pBPf.TFIB_T_room_all_B_closed drv3_amalloc_B drv3_afree_B
  Ent102DrvTopB2.drv2_aintrin_cpy_B Ent102DrvTopB2.drv2_aintrin_set_B Ent102DrvTopB2.drv2_stack_malloc_cfm_B
  drv3_aread_check_B
  ReaderRes.jr_strtod (fun _ => 0) (fun _ => 0) (fun _ => True) Ent102InstB.ia_mod_at Ent102InstB.ia_stamp
  drv3_check_no_overread_B (Ent102DrvTopB2.drv2_parse_noting_B drv3_pj_parse_B) drv3_check_as_written_B
  drv3_check_reject_clean_starved_B drv3_check_round_trip_B drv3_pj_free_B
  (fun rc fx => Ent102SeamB.preset_lib_x_stmt_B_holds rc fx (fun _ => 0) (fun _ => 0) (fun _ => True))).
Qed.

(* walked3 from the room form: at PAYLOAD_ROOM := fun _ => True the payload's room is I, so TFIB_T_AU's plain
   no-refusal premise is not used *)
Theorem TFIB_T_closed_B_walked3 : PresetD2pB.TFIB_T_closed_B.
Proof.
intros sp brk mbase rnd inp en_p Hsp Hbrk Hmb Hfit Hinp _.
exact (TFIB_T_room_all_B_walked3 sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp (fun _ _ _ _ _ => I)).
Qed.

(* inside the Section: the remaining hypotheses by name, and the allowed axioms *)
Print Assumptions TFIB_T_room_all_B_walked3.
Print Assumptions TFIB_T_closed_B_walked3.
End walked3.

(* the elaborated statement (implicit arguments shown, notations off): its Section names are now its binders, every
   one at PI_prog_B / YD2l.TfibB *)
Set Printing Implicit. Unset Printing Notations.
Check TFIB_T_closed_B_walked3.
Unset Printing Implicit. Set Printing Notations.
