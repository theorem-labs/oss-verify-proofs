(* fuzz_preset, image A' (asan, #102 pin 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): check_round_trip's
   contract AT THE D2p INSTANCE. rule 24: proves no function (kind: statement text, the instance corollary of
   Crt102Top.crt102_top_TfibA).
   THE STATEMENT of crt102_top_TfibA_inst is the body of txt_check_round_trip_A (lib/A/PresetD2pAPf.v:128-130), the
   text of the premise H_txt_check_round_trip_A (:267-268), at the binding lib/A/Prog/Ent102DrvTopA.v gives the D2p
   Variables: a_mod_at := Ent102InstA.ia_mod_at, a_stamp := Ent102InstA.ia_stamp. Given the carried item below, the
   premise can cite it directly: `fun rc fx => crt102_top_TfibA_inst (rc := rc) .. fx` has the type
   `txt_check_round_trip_A fx rc ia_mod_at ia_stamp` by unfolding txt_check_round_trip_A. This file does not Require
   PresetD2pAPf.v or the D2p drivers.
   THE BINDING (cti_mod_at / cti_stamp, by reflexivity): Ent102InstA.ia_mod_at / ia_stamp are Crt102Img.v's
   CRT_MOD_AT_A / CRT_STAMP_A, the literal addresses crt102_top_TfibA is stated at: pa_val of PI_prog_A is A_prog_val
   (PAImg_prog.v), and Crt102Img.v's offsets CRT_MOD_AT_OFF / CRT_STAMP_OFF are the numerals Ent102InstA.v adds to it.
   THE INSTANCE: B := AD2l.TfibB, ARx := PresetCfnA.iface_ARx at CfImg_A, RL := prh_room_live_a8,
   SK := PresetCfnA.preset_sink_head, CTX0 := PresetCfnA.iface_ctx0, exactly the arguments of txt_check_round_trip_A.
   DISCHARGED (all twenty-one of crt102_top_TfibA's Section hypotheses), each by a cited theorem:
     LAWS YGcallcf.AR_laws_x_xs; OWNLOW YGcallcf.ARx_owned_low_law_xs; ASM3 FCxmCfx.stack_malloc3_contract_xm_cfx;
     AMS Cno102A_Mset.cn_memset_A; ASFX YGcallScf.astack_free_x_xs; FFLX YGcallScf.frame_flag_x_xs;
     SFX YGcallScf.stack_free_x_any; FFLP YG0scf.AR_flag_law_ok_cf (its first conjunct); SETSH
     FCxmCfx.set_shadow_f5_contract_xm_cfx; img_shadow_vis_x AImgShadowVisCf.img_shadow_vis_xs_A; RANOUT
     FuzzAllocAccInst102.fuzz_alloc_ran_out_holds_inst; STRLEN PSstrRo.ps_strlen_xrom_xs_A (pc: cti_strlen_pc);
     STRCMP SameAp_inst.sai_hstr; SAME SameAp_inst.same_holds_Ap_HSAME_fit_s;
     PJSTR (cti_pjstr) S6PjString.pj_string_holds: LAWS cti_laws, TL PALibA.palib_A, Hent / Hobj / PAB
       S6ImgWit.s6w_ent_pj_string / s6w_obj / s6w_pab, AIM cti_ams, pal_pst_img S1ImgA.pst_in_img_A, pal_lit
       S6PalLitRefute.pal_lit_A, pal_lit_sh cti_isv, STRDUP (cti_strdup) FuzzStrdup.fuzz_strdup_holds_TfibB with
       FMALLOC (cti_fmalloc) FuzzMalloc.fuzz_malloc_holds (PAL PALibA.palib_A, pal_pst_ok
       FuzzAllocAccInst102.acc_pal_pst_ok_A, AMALLOC cti_amalloc, APOISON cti_apoison
       CfPoison102.preset_apoison_cf102, TB AD2l.TfibB_syms), AI (cti_amcpy_cf) PRowCpy.prow_asan_memcpy_xm_A at ARcf
       (fuzz_strdup's AI is at ARcf alone; laws YGcallcf.AR_laws_x_cf), PAL PALibA.palib_A;
     FFREE (cti_ffree) FuzzFree.fuzz_free_holds: AFREE cti_afree, AUNPOISON cti_aunpoison
       CfPoison102.preset_aunpoison_cf102, PAL PALibA.palib_A, pal_pst_ok FuzzAllocAccInst102.acc_pal_pst_ok_A,
       TB AD2l.TfibB_syms;
     RTT (cti_rtt) Rtt102InstA.rtt_iface_A at CTX0 := iface_ctx0: TSAME cti_same, TPJF cti_pjfree, AFK
       cti_afree, TFF cti_ffree, TPN cti_pnoting, LITNL cti_litnl (read_members_inst.rmA_kept_b_ok, its boolean check
       by vm_compute at Rtt102TA.RTT_LITNL_A), TXPUT cti_txput, TXVAL the carried H_txt_tx_value_A, TPJW cti_pjwrite;
     PJFREE (cti_pjfree) S6PjFreeTop.pj_free_holds at CTX0 := iface_ctx0, n := DOC_D: LAWS cti_laws, TL PALibA.palib_A,
       VISF cti_visf (YGcfFsVis.ARx_frame_hull_vis_cf_ok through the first conjunct), the image facts S6ImgWit.s6w_*,
       AIM cti_ams, FREE cti_ffree;
     PJSET (cti_pjset) pj_setA_iface.tpj_set_specX_A_of_callees at CTX0 := iface_ctx0, dd := DOC_D (memcpy, memset,
       LAWS, VIS, PAL and the hull discharged inside it): GET (cti_get) S6PjGet.pj_get_holds (LAWS cti_laws, TL
       PALibA.palib_A, Hent / Hobj / PAB S6ImgWit.s6w_ent_pj_get / s6w_obj / s6w_pab, ASCR cti_strcmp), FREE
       cti_pjfree, STRDUP cti_strdup, GROW (cti_grow) PwGrow.grow_holds_Aprime (ARcf /\ xs_placed_cf is iface_ARx by
       conversion) with HREALLOC (cti_freal) FuzzReallocAp.fuzz_realloc_holds_Ap: PAL PALibA.palib_A, PST
       FuzzReallocAp.ra_cells (PST_cells FuzzReallocAp.ra_cell_in; PST_ok / PST_errno / MOST_ok / OWN_ok / PST_sub /
       PST_own_out / PST_most_out / PST_aro by computation, cti_ra_*, copied from the D2p driver's drv3_ra_* lemmas),
       FMALLOC cti_fmalloc, AUNPOISON / APOISON cti_aunpoison / cti_apoison, CF_unpoison / CF_poison and the RELRO range
       equation by computation, RELRO_SEG / ERRNO_RELRO / RELRO_TOP / RO_READS_NW CfAroPresetA.relro_seg_preset_A /
       errno_relro_preset_A / relro_top_preset_A / ro_reads_nw_preset_A, AREAL_cf cti_areal;
     PJWRITE (cti_pjwrite) PRW_pj_write.pjw_holds_lc at CTX0 := iface_ctx0, n := DOC_D: LAWS cti_laws, segs_low the
       class field pa_segs_low, AMS cti_ams, the image facts PRW_S7bWit.s7bw_pjw_* / s7bw_pstro_A / s7bw_pst_ok_pjw and
       PRW_S7bLitWit.s7bl_pjw_hlit, S9_CF the first conjunct, HHCAP by reflexivity, HFREE cti_ffree, pjw_ARGCNT the
       second conjunct of PresetRoomCounts.counts_of_room_pos_rl at the call's model-run position; HPUT (cti_put)
       S7a_put.put_holds (HREAL cti_freal, AMC cti_amcpy, HIMGSH cti_imgsh, HFRSH cti_visf, the image facts
       S7a_put_wit.s7p_*, HCAP by reflexivity); HWV (cti_wval) PRW_write_value.write_value_holds (PUT cti_put, PUTSTR
       (cti_putstr) PRW_put_string.put_string_holds, INDENT (cti_indent) S7a_indent.indent_holds, STRLEN cti_strlen, the
       image facts PRW_S7bWit.s7bw_* / PRW_S7bLitWit.s7bl_* / S7a_indent_wit.s7w_*, HJT cti_wv_hjt by one closed
       boolean per table word over the checkers cti_vm_b / cti_ro_byte_b, copied from the image B twin's
       WriteValueB_Wit.v, not Required: this file Requires no image-B module; put_string's SNP
       PSnpRowA.snprintf_row_A_inst,
       ASM0 cti_asmr0 (FCm01xm.stack_malloc0_contract_xm kept by xs_placed_cf));
     PNOTING (cti_pnoting) PN102Top.tparse_noting_specX_A_iface: HLIVE PwAllocSurf.fuzz_alloc_live_holds, HRO
       cti_ranout, HCRC Crc102InstLive.check_reject_clean_holds_A102_inst_live with the bcmp row PRowCmp.pr_bcmp_xm_A
       (PresetD2pAPf.v:203 crc_bcmp_A_holds, copied), HPJ (cti_pjparse) PjParseA_top.pj_parse_holds_A_tpv (parse_value
       by VrdTop.vrd_parse_value_holds inside it) at the rows cti_areal / cti_amalloc / cti_afree and the unpoison row
       cti_aunpoison;
     TXPUT (cti_txput) TxPut102A_Inst.tx_put_holds_A: TB AD2l.TfibB_syms, AI cti_amcpy_cf, AREAL cti_areal
       (TxPut102A_Base.tp_AREAL is its _k keep form), AREALN cti_arealn; its depot row is the lemma
       TxPut102A_Inst.tp_arx_depot_A (TxPut102A_Inst.v:80), proved there.
   THE SECOND ALLOCATOR'S ROWS, each at the instance and every float state, are cited BY NAME (no Section hypothesis):
     malloc's keep row (cti_amalloc) CfMallocKeepA.amalloc_realizes_cf_keep_closed_A, free's primed keep row
     (cti_afree) CfFreeKeepA.afree_realizes_cf_rh_keep_A, realloc's keep _k row (cti_areal)
     AllocAssembleA.arealloc_realizes_cf_A (AllocAssembleA.v:60), realloc(NULL)'s keep row (cti_arealn)
     AllocAssembleA.arealloc_null_realizes_cf_A (:93). The driver states the first three as its premises of the same
     names (Ent102DrvTopA3.v:426-431, :443-446); D2p states malloc and free as its premises H_amalloc_realizes_cf_A /
     H_afree_realizes_cf_A (PresetD2pAPf.v:222-225; its malloc row at the entry float state only).
   CARRIED (Section hypothesis below), at the instance, at CTX0 := iface_ctx0 and every float state:
     H_txt_tx_value_A tx_value: written as the D2p record writes its texts (owner: the tx rows' owner). On this head,
       no theorem in lib/A concludes PRH_FnTx.ttx_value_specX (the text, PRH_FnTx.v:975; elsewhere it is
       a premise, e.g. TXVAL of Rtt102InstA.v:195, or a check); the one walk here is image B's BTxValue.tx_value_B_holds (lib/B/Prog/BTxValue.v:5887).
   Image-side modules are cited FULLY QUALIFIED. The numerals in the code are the ones the restated texts carry:
   ASM3's frame class 3, ASFX's flag value 0 and address range 0 .. 2 ^ 64, SETSH's shadow value 245, the newline
   literal's length 1 (Rtt102InstA.v's LITNL); in the realloc walk's copied stand-ins the listing atoms 13 / 14
   (g_own_ran_out / g_most), their widths 1 / 8 and the errno cell's width 4; in the copied write_value checks the
   table's seven words of width 4, the listing atoms 0 / 2 / 12, the cell width 8 and the bound 2 ^ 31 - 1. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YCbqGcallW YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YGcallcf YG0lawscf YGcallScf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc PRH_FnEx PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB1v AF0m AD2l FCxmCfx AImgShadowVisCf PSstrRo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetCfnA Ent102InstA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Cno102A_Mset FuzzAllocAccInst102 SameAp_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Img Crt102Top.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YGcfMallocComposeKeep YGcfHp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PALibA PRowCpy CfPoison102 PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgA FuzzMalloc FuzzFree FuzzStrdup.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S6PjString S6ImgWit S6PalLitRefute.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require read_members_inst Rtt102TA Rtt102InstA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf YGcfInstReallocKKeep YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfAroPresetA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgCheck FuzzReallocAp PwGrow S6PjGet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require pj_setA_iface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomCounts PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfFsVis YGcfReallocComposeKeep FCifaceCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP08 YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require FCm01xm PRowCmp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AllocAssembleA CfFreeKeepA CfMallocKeepA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_pj_write PRW_write_value PRW_put_string.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_put_string_e PRW_HShadow PSnpRowA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S7a_put S7a_put_wit S7a_indent S7a_indent_wit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_S7bWit PRW_S7bLitWit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S6PjFreeTop TxPut102A_Inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PwAllocSurf Crc102InstA Crc102InstLive PN102Top.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PjParseA_top.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Module CTA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.Crt102Top.
Module CIA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.Crt102Img.
Module CFA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Module EIA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Ent102InstA.
Module ADA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AD2l.
Module ABA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AB1v.
Module FCA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.FCxmCfx.
Module ISA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AImgShadowVisCf.
Module PSA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSstrRo.
Module MSA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.Cno102A_Mset.
Module FAA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.FuzzAllocAccInst102.
Module SMA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.SameAp_inst.
Module PLA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PALibA.
Module PCA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PRowCpy.
Module CPA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.CfPoison102.
Module S1A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.S1ImgA.
Module FMA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.FuzzMalloc.
Module FFA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.FuzzFree.
Module FDA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.FuzzStrdup.
Module PSS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.S6PjString.
Module SWA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.S6ImgWit.
Module SLA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.S6PalLitRefute.
Module RMA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.read_members_inst.
Module RTA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.Rtt102TA.
Module RIA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.Rtt102InstA.
Module SCA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.S1ImgCheck.
Module CAA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.CfAroPresetA.
Module FRA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.FuzzReallocAp.
Module PGA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.PwGrow.
Module PJG := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.S6PjGet.
Module PSI := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.pj_setA_iface.
Module PJW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.PRW_pj_write.
Module PFT := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.S6PjFreeTop.
Module TPA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.TxPut102A_Inst.
Module S7P := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.S7a_put.
Module S7PW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.S7a_put_wit.
Module S7I := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.S7a_indent.
Module S7IW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.S7a_indent_wit.
Module PPS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.PRW_put_string.
Module PWV := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.PRW_write_value.
Module S7BW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.PRW_S7bWit.
Module S7BL := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.PRW_S7bLitWit.
Module PSR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.PSnpRowA.
Module FC01 := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.FCm01xm.
Module PHS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.PRW_HShadow.
Module PAS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.PwAllocSurf.
Module CRA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.Crc102InstA.
Module CRL := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.Crc102InstLive.
Module PRC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PRowCmp.
Module PNT := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.PN102Top.
Module PPT := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.PjParseA_top.
Module AAA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AllocAssembleA.
Module CFK := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.CfFreeKeepA.
Module CMK := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.CfMallocKeepA.

(* the strlen trampoline of CfImg_A is the listing's __wrap_strlen (closed computation) *)
Lemma cti_strlen_pc : A_prog_sigma AS___wrap_strlen = @cf_pc_strlen CfImg_A.
Proof. vm_compute. reflexivity. Qed.

(* ---- fuzz_realloc_holds_Ap's static-set stand-ins at TfibB, by computation (the D2p driver's drv3_ra_* in
   Ent102DrvTopA3.v, copied): PST := FuzzReallocAp.ra_cells; the image-free checkers S1ImgCheck.pst_allb (a range
   list inside another) and FuzzAllocAccInst102.acc_dj (a range list off a range), each with its soundness lemma.
   g_own_ran_out is the listing's atom 13 (one byte), g_most its atom 14 (eight bytes) ---- *)
Definition cti_mem_b (a : Z) (P : list (Z * Z)) : bool :=
  List.existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) P.
Lemma cti_mem_b_sound : forall a P, cti_mem_b a P = true -> List.Exists (YG0n.in_zr a) P.
Proof.
intros a P H. unfold cti_mem_b in H. apply List.existsb_exists in H as [r [Hr Hb]].
apply List.Exists_exists. exists r. split; [exact Hr|]. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold YG0n.in_zr. lia.
Qed.
Lemma cti_sub_ok : forall P Q, SCA.pst_allb (fun a => cti_mem_b a Q) P = true ->
  forall a, List.Exists (YG0n.in_zr a) P -> List.Exists (YG0n.in_zr a) Q.
Proof. intros P Q H a Ha. apply cti_mem_b_sound. exact (SCA.pst_allb_sound _ _ a H Ha). Qed.
Lemma cti_out_ok : forall P s, List.forallb (fun r => FAA.acc_dj r s) P = true ->
  forall a, YG0n.in_zr a s -> ~ List.Exists (YG0n.in_zr a) P.
Proof.
intros P s H a Hs HP. apply List.Exists_exists in HP as [r [Hr Har]]. rewrite List.forallb_forall in H.
exact (FAA.acc_dj_ok r s a (H r Hr) Har Hs).
Qed.
Lemma cti_ra_pst_sub : forall a, List.Exists (YG0n.in_zr a) FRA.ra_cells ->
  List.Exists (YG0n.in_zr a) (@PRH_Base.prh_pst CFA.preset_prh_img).
Proof. apply cti_sub_ok. vm_compute. reflexivity. Qed.
Lemma cti_ra_own_pst : forall a, List.Exists (YG0n.in_zr a) [(A_prog_val (A_OBJ 13), 1)] ->
  List.Exists (YG0n.in_zr a) (@PRH_Base.prh_pst CFA.preset_prh_img).
Proof. apply cti_sub_ok. vm_compute. reflexivity. Qed.
Lemma cti_ra_most_pst : forall a, List.Exists (YG0n.in_zr a) [(A_prog_val (A_OBJ 14), 8)] ->
  List.Exists (YG0n.in_zr a) (@PRH_Base.prh_pst CFA.preset_prh_img).
Proof. apply cti_sub_ok. vm_compute. reflexivity. Qed.
Lemma cti_ra_own_out : ~ List.Exists (YG0n.in_zr (A_prog_val (A_OBJ 13))) FRA.ra_cells.
Proof.
apply (cti_out_ok FRA.ra_cells (A_prog_val (A_OBJ 13), 1)); [vm_compute; reflexivity | unfold YG0n.in_zr; cbn [fst snd]; lia].
Qed.
Lemma cti_ra_most_out : forall o, 0 <= o < 8 -> ~ List.Exists (YG0n.in_zr (A_prog_val (A_OBJ 14) + o)) FRA.ra_cells.
Proof.
intros o Ho. apply (cti_out_ok FRA.ra_cells (A_prog_val (A_OBJ 14), 8));
  [vm_compute; reflexivity | unfold YG0n.in_zr; cbn [fst snd]; lia].
Qed.

(* ---- write_value's jump-table premise (its HJT): the image-free checkers of the image B twin's witness file
   WriteValueB_Wit.v (wvw_zr_b / wvw_ro_byte_b / wvw_vm_b and their soundness), copied: this file Requires no
   image-B module. Numerals: 4 (errno's width), 8 and 256
   (a byte) ---- *)
Definition cti_zr_b (l : list (Z * Z)) (a : Z) : bool := existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l.
Lemma cti_zr_b_sound : forall l a, cti_zr_b l a = false -> ~ Exists (in_zr a) l.
Proof.
intros l a H HE. apply List.Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
assert (E : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l = true).
{ apply List.existsb_exists. exists r. split; [exact Hr|]. apply Bool.andb_true_iff.
  split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
unfold cti_zr_b in H. rewrite E in H. discriminate H.
Qed.
Lemma cti_in_ro_b_sound : forall segs rlo rhi a, SCA.in_ro_b segs rlo rhi a = true -> in_roP segs rlo rhi a.
Proof.
intros segs rlo rhi a H. unfold SCA.in_ro_b in H. apply Bool.orb_true_iff in H as [H|H].
- left. apply List.existsb_exists in H as (s & Hs & Hb). apply andb_prop in Hb as [Hb H3].
  apply andb_prop in Hb as [H1 H2].
  apply Bool.negb_true_iff in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  exists s. split; [exact Hs|]. split; [exact H1|]. lia.
- right. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Definition cti_ro_byte_b (segs : list Segment) (rlo rhi : Z) (B : asyms) (x : Z) : bool :=
  SCA.in_img_b segs x && SCA.in_ro_b segs rlo rhi x && negb (cti_zr_b (as_owned_static B) x) &&
  negb ((as_errno B <=? x) && (x <? as_errno B + 4)).
Lemma cti_ro_byte_sound : forall segs rlo rhi B x, cti_ro_byte_b segs rlo rhi B x = true ->
  in_img segs x /\ in_roP segs rlo rhi x /\ ~ Exists (in_zr x) (as_owned_static B) /\
  ~ (as_errno B <= x < as_errno B + 4).
Proof.
intros segs rlo rhi B x H. unfold cti_ro_byte_b in H.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
split; [exact (SCA.in_img_b_sound _ _ H1)|].
split; [exact (cti_in_ro_b_sound _ _ _ _ H2)|].
split; [apply Bool.negb_true_iff in H3; exact (cti_zr_b_sound _ _ H3)|].
apply Bool.negb_true_iff in H4. intros [E1 E2].
apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite E1, E2 in H4. discriminate H4.
Qed.
Lemma cti_ro_range_sound : forall segs rlo rhi B a n, YP08.zallb (cti_ro_byte_b segs rlo rhi B) a n = true ->
  forall i, 0 <= i < Z.of_nat n ->
  in_img segs (a + i) /\ in_roP segs rlo rhi (a + i) /\ ~ Exists (in_zr (a + i)) (as_owned_static B) /\
  ~ (as_errno B <= a + i < as_errno B + 4).
Proof.
intros segs rlo rhi B a n H i Hi. apply cti_ro_byte_sound. apply (YP08.zallb_sound _ n a); [exact H | lia].
Qed.
Definition cti_vm_b (segs : list Segment) (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun j => match mbyte segs (fun _ => None) (a + Z.of_nat j) with
                    | Some b => bv_unsigned b =? YO0f.le_byte v n j
                    | None => false
                    end) (seq 0 n).
Lemma cti_vm_sound : forall segs a n v, cti_vm_b segs a n v = true -> val_mem segs (fun _ => None) a n v.
Proof.
intros segs a n v H j Hj. unfold cti_vm_b in H. rewrite List.forallb_forall in H.
specialize (H j ltac:(apply List.in_seq; lia)).
destruct (mbyte segs (fun _ => None) (a + Z.of_nat j)) as [b|] eqn:E; [|discriminate H].
apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- H.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by exact Hr. reflexivity.
Qed.

Section i. Context {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
(* the room invariant of the D2p instance (RLA), so a callee text that reads it elaborates there *)
#[local] Existing Instance PRH_Base.prh_room_live_a8.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation SEGS := (@pa_segs rc A_prog_listing (@PI_prog_A rc)).
#[local] Notation SIGMA := (@pa_sigma rc A_prog_listing (@PI_prog_A rc)).
#[local] Notation RLO := (@pa_relro_lo rc A_prog_listing (@PI_prog_A rc)).
#[local] Notation RHI := (@pa_relro_hi rc A_prog_listing (@PI_prog_A rc)).
#[local] Notation TA := ADA.TfibB.
#[local] Notation CP := CfParams_preset.
#[local] Notation RLA := (@PRH_Base.prh_room_live_a8 CfParams_preset).
#[local] Notation ARI := (@CFA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImg_A ADA.TfibB).
#[local] Notation SKA := CFA.preset_sink_head.
#[local] Notation PIA := CFA.preset_prh_img.
#[local] Notation CTXA := CFA.iface_ctx0.

(* ---- the binding: the D2p Variables at Ent102DrvTopA.v's values are crt102_top_TfibA's literal addresses ---- *)
Lemma cti_mod_at : CIA.CRT_MOD_AT_A (rc := rc) = EIA.ia_mod_at.
Proof. reflexivity. Qed.
Lemma cti_stamp : CIA.CRT_STAMP_A (rc := rc) = EIA.ia_stamp.
Proof. reflexivity. Qed.

(* ---- the fourteen discharges, each at the instance ---- *)
Lemma cti_laws : AR_laws_x SEGS TA ARI cf_head.
Proof. exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TA (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TA)). Qed.

Lemma cti_ownlow : ARx_owned_low_law SEGS TA ARI.
Proof. exact (YGcallcf.ARx_owned_low_law_xs (cp := CP) SEGS TA (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TA)). Qed.

Lemma cti_asm3 : forall fy : YK11.FPState, YGcallMxmn.astack_malloc_realizes_xm (fx := fy) SEGS TA ARI 3.
Proof. intros fy. exact (FCA.stack_malloc3_contract_xm_cfx (fx := fy) (rc := rc) (cp := CP) TA ADA.TfibB_syms). Qed.

Lemma cti_ams : forall fy : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fy) SEGS TA ARI OSet (SIGMA AS___asan_memset).
Proof. intros fy. exact (MSA.cn_memset_A (rc := rc) (cp := CP) TA ARI cti_laws ADA.TfibB_syms fy). Qed.

Lemma cti_asfx : forall ly S Hp W mem md mem' md' cid pos,
  ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned TA ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARI ly (stack_free_state cid pos S) Hp W mem' md'.
Proof. exact (YGcallScf.astack_free_x_xs (rc := rc) (cp := CP) SEGS TA). Qed.

Lemma cti_fflx : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned TA ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Proof. exact (YGcallScf.frame_flag_x_xs (rc := rc) (cp := CP) SEGS TA). Qed.

Lemma cti_sfx : forall ly S Hp W mem md cid pos, ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Proof. exact (YGcallScf.stack_free_x_any SEGS ARI). Qed.

Lemma cti_fflp : forall ly S Hp (W : world SEGS) mem md cid pos, ARI ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos).
Proof.
intros ly S Hp W mem md cid pos [HAR _] Hin.
exact (proj1 (YG0scf.AR_flag_law_ok_cf (rc := rc) (cp := CP) SEGS TA ly S Hp W mem md cid pos HAR Hin)).
Qed.

Lemma cti_setsh : forall fxk : YK11.FPState,
  YGcallMxmn.aset_shadow_realizes_xm (fx := fxk) SEGS TA ARI (SIGMA AS___asan_set_shadow_f5) 245.
Proof. exact (FCA.set_shadow_f5_contract_xm_cfx (rc := rc) (cp := CP) TA ADA.TfibB_syms). Qed.

Lemma cti_isv : forall ly S Hp W mem md a, ARI ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof. exact (ISA.img_shadow_vis_xs_A (rc := rc) (cp := CP) SEGS TA ADA.TfibB_syms). Qed.

Lemma cti_ranout : forall fxk : YK11.FPState,
  @PRH_FnAlloc.tfuzz_alloc_ran_out_specX fxk rc CP PIA RLA A_prog_listing PA TA ARI SKA.
Proof. intros fxk. exact (FAA.fuzz_alloc_ran_out_holds_inst (fx := fxk) (rc := rc) (SK := SKA)). Qed.

Lemma cti_strlen : forall fxq : YK11.FPState,
  @YGcallMxmn.astrlen_realizes_xrom fxq SEGS TA ARI RLO RHI (SIGMA AS___wrap_strlen).
Proof.
intros fxq.
change (SIGMA AS___wrap_strlen) with (A_prog_sigma AS___wrap_strlen). rewrite cti_strlen_pc.
change SEGS with ABA.tfibsegs.
exact (PSA.ps_strlen_xrom_xs_A (fx := fxq) (rc := rc) (cp := CP) TA ADA.TfibB_syms RLO RHI).
Qed.

Lemma cti_strcmp : forall fxq : YK11.FPState,
  @YGcallMxmn.astrcmp_realizes_xrom fxq SEGS TA ARI RLO RHI (SIGMA AS___wrap_strcmp).
Proof. intros fxq. exact (SMA.sai_hstr (fx := fxq) (rc := rc)). Qed.

Lemma cti_same : forall fxq : YK11.FPState, @PRH_FnEx.tsame_specX fxq rc CP PIA RLA A_prog_listing PA TA ARI SKA DOC_D.
Proof. intros fxq. exact (SMA.same_holds_Ap_HSAME_fit_s (rc := rc) SKA DOC_D fxq). Qed.

(* ---- GET: S6PjGet.pj_get_holds at the instance (as read_members_Ap4.v cites it): LAWS cti_laws, TL
   PALibA.palib_A, Hent / Hobj / PAB S6ImgWit.s6w_ent_pj_get / s6w_obj / s6w_pab, ASCR cti_strcmp ---- *)
Lemma cti_get : forall fxk : YK11.FPState,
  PRH_FnPj.tpj_get_specX (fx := fxk) (rc := rc) (cp := CP) (PI := PIA) (L := A_prog_listing) (PA := PA) TA ARI SKA.
Proof.
intros fxk.
eapply (PJG.pj_get_holds (fx := fxk) (rc := rc) (PA := PA) SKA TA ARI).
all: first
  [ exact cti_laws | exact PLA.palib_A | exact (SWA.s6w_ent_pj_get (rc := rc)) | exact (SWA.s6w_obj (rc := rc))
  | exact (SWA.s6w_pab (rc := rc)) | exact (cti_strcmp fxk) ].
Qed.

(* ---- the realloc walk's static-set and image facts at the listing (the D2p driver's Section ra in
   Ent102DrvTopA3.v, copied): the statics are image bytes no allocator owns and not errno (S1ImgA.pst_in_img_A,
   FuzzAllocAccInst102.acc_pal_pst_ok_A), CfImg_A's two runtime call targets are the listing's entries (computation),
   and no static is a byte the call memory's arodata_ok_cf covers (S1ImgA.pst_not_ro_A, CfAroPresetA.ro_reads_nw_preset_A,
   as FuzzFree.v ff_pst_aro) ---- *)
Lemma cti_ra_pst_ok : forall a, List.Exists (YG0n.in_zr a) FRA.ra_cells ->
  YG0d.in_img SEGS a /\ ~ List.Exists (YG0n.in_zr a) (YG0f.as_owned_static TA).
Proof.
intros a H. pose proof (cti_ra_pst_sub a H) as Hp.
exact (conj (S1A.pst_in_img_A a Hp) (proj1 (FAA.acc_pal_pst_ok_A a Hp))).
Qed.
Lemma cti_ra_pst_errno : forall a, List.Exists (YG0n.in_zr a) FRA.ra_cells ->
  ~ (YG0f.as_errno TA <= a < YG0f.as_errno TA + 4).
Proof. intros a H. exact (proj2 (FAA.acc_pal_pst_ok_A a (cti_ra_pst_sub a H))). Qed.
Lemma cti_ra_most_ok : forall o, 0 <= o < 8 ->
  YG0d.in_img SEGS (A_prog_val (A_OBJ 14) + o) /\
  ~ List.Exists (YG0n.in_zr (A_prog_val (A_OBJ 14) + o)) (YG0f.as_owned_static TA) /\
  ~ (YG0f.as_errno TA <= A_prog_val (A_OBJ 14) + o < YG0f.as_errno TA + 4).
Proof.
intros o Ho. assert (Hp : List.Exists (YG0n.in_zr (A_prog_val (A_OBJ 14) + o)) (@PRH_Base.prh_pst PIA)).
{ apply cti_ra_most_pst. apply List.Exists_cons_hd. unfold YG0n.in_zr. cbn [fst snd]. lia. }
destruct (FAA.acc_pal_pst_ok_A _ Hp) as [H1 H2].
exact (conj (S1A.pst_in_img_A _ Hp) (conj H1 H2)).
Qed.
Lemma cti_ra_own_ok :
  YG0d.in_img SEGS (A_prog_val (A_OBJ 13)) /\
  ~ List.Exists (YG0n.in_zr (A_prog_val (A_OBJ 13))) (YG0f.as_owned_static TA) /\
  ~ (YG0f.as_errno TA <= A_prog_val (A_OBJ 13) < YG0f.as_errno TA + 4).
Proof.
assert (Hp : List.Exists (YG0n.in_zr (A_prog_val (A_OBJ 13))) (@PRH_Base.prh_pst PIA)).
{ apply cti_ra_own_pst. apply List.Exists_cons_hd. unfold YG0n.in_zr. cbn [fst snd]. lia. }
destruct (FAA.acc_pal_pst_ok_A _ Hp) as [H1 H2].
exact (conj (S1A.pst_in_img_A _ Hp) (conj H1 H2)).
Qed.
Lemma cti_ra_cf_unpoison : @YGcfNames.cf_pc_unpoison CfImg_A = SIGMA YPsym.AS___asan_unpoison_memory_region.
Proof. vm_compute. reflexivity. Qed.
Lemma cti_ra_cf_poison : @YGcfNames.cf_pc_poison CfImg_A = SIGMA YPsym.AS___asan_poison_memory_region.
Proof. vm_compute. reflexivity. Qed.
Lemma cti_ra_pst_aro : forall a, YG0dcf.aro_addr_cf (ci := CfImg_A) a -> ~ List.Exists (YG0n.in_zr a) FRA.ra_cells.
Proof.
intros a Ha Hx. apply (S1A.pst_not_ro_A a (cti_ra_pst_sub a Hx)). destruct Ha as [Ha | Ha].
- right. unfold PAImg_prog.A_prog_relro_lo, PAImg_prog.A_prog_relro_hi.
  cbv [YGcfNames.cf_relro_lo YGcfNames.cf_relro_hi CfImg_A] in Ha. exact Ha.
- left. pose proof CAA.ro_reads_nw_preset_A as RONW.
  unfold YGcfAroBridge.ro_reads_nw_t in RONW. rewrite List.Forall_forall in RONW.
  apply List.Exists_exists in Ha as (r & Hr & Hra). unfold YG0n.in_zr in Hra.
  destruct (RONW r Hr) as (_ & sg & Hin & NW & L & R). exists sg. split; [exact Hin|]. split; [exact NW | lia].
Qed.

(* ---- the second allocator's rows at the instance, each at every float state, BY NAME: malloc's keep row
   CfMallocKeepA.amalloc_realizes_cf_keep_closed_A, free's primed keep row CfFreeKeepA.afree_realizes_cf_rh_keep_A,
   realloc's keep _k row AllocAssembleA.arealloc_realizes_cf_A, realloc(NULL)'s keep row
   AllocAssembleA.arealloc_null_realizes_cf_A; each is the form its callee walk takes (fuzz_malloc's AMALLOC,
   fuzz_free's AFREE, fuzz_realloc's AREAL_cf, tx_put's AREAL / AREALN) ---- *)
Lemma cti_amalloc : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset)
    ABA.tfibsegs ADA.TfibB.
Proof.
intros rc0 fx.
first [ exact (CMK.amalloc_realizes_cf_keep_closed_A (fx := fx) (rc := rc0)) | exact CMK.amalloc_realizes_cf_keep_closed_A ].
Qed.
Lemma cti_afree : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset)
    ABA.tfibsegs ADA.TfibB.
Proof.
intros rc0 fx.
first [ exact (CFK.afree_realizes_cf_rh_keep_A (fx := fx) (rc := rc0)) | exact CFK.afree_realizes_cf_rh_keep_A ].
Qed.
Lemma cti_areal : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (Hp : list Z) (k : nat),
  YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset)
    (@YC4aP.pa_segs rc A_prog_listing (@PI_prog_A rc)) ADA.TfibB Hp
    (@YC4aP.pa_sigma rc A_prog_listing (@PI_prog_A rc) YPsym.AS___wrap_realloc) k.
Proof. exact AAA.arealloc_realizes_cf_A. Qed.
Lemma cti_arealn : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (Hp : list Z),
  YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep (fx := fx) (rc := rc)
    (@YC4aP.pa_segs rc A_prog_listing (@PI_prog_A rc)) ADA.TfibB Hp
    (@YC4aP.pa_sigma rc A_prog_listing (@PI_prog_A rc) YPsym.AS___wrap_realloc).
Proof. exact AAA.arealloc_null_realizes_cf_A. Qed.

(* ---- the unpoison / poison rows at TfibB: the allocator engine's CfPoison102 rows at the ARcf laws (the D2p driver's
   Ent102DrvTopA3.v drv3_aunpoison_A / drv3_apoison_A, copied) ---- *)
Lemma cti_aunpoison : forall fy : YK11.FPState,
  @YGcfHp.aunpoison_realizes_cf fy rc CfImg_A CP ABA.tfibsegs TA.
Proof.
intros fy. exact (CPA.preset_aunpoison_cf102 (fx := fy) (rc := rc) TA (YG0lawscf.AR_laws_ok_cf (cp := CP) ABA.tfibsegs TA)
  ADA.TfibB_syms).
Qed.
Lemma cti_apoison : forall fy : YK11.FPState,
  @YGcfHp.apoison_realizes_cf fy rc CfImg_A CP ABA.tfibsegs TA.
Proof.
intros fy. exact (CPA.preset_apoison_cf102 (fx := fy) (rc := rc) TA (YG0lawscf.AR_laws_ok_cf (cp := CP) ABA.tfibsegs TA)
  ADA.TfibB_syms).
Qed.

(* ---- FFREE: the allocator engine's FuzzFree.fuzz_free_holds at TfibB, AFREE the keep row ---- *)
Lemma cti_ffree : forall fxk : YK11.FPState,
  @PRH_FnAlloc.tfuzz_free_specX fxk rc CP PIA RLA A_prog_listing PA TA ARI SKA.
Proof.
intros fxk.
eapply (FFA.fuzz_free_holds (fx := fxk) (rc := rc) (SK := SKA) TA);
  first [ exact (cti_afree rc fxk) | exact (cti_aunpoison fxk) | exact PLA.palib_A
        | exact FAA.acc_pal_pst_ok_A | exact ADA.TfibB_syms ].
Qed.

(* ---- PJSTR's callees: fuzz_malloc (the allocator engine's FuzzMalloc.fuzz_malloc_holds, AMALLOC the keep row), the
   __asan_memcpy row at ARcf (fuzz_strdup's AI: the libc stdio row PRowCpy.prow_asan_memcpy_xm_A, the listing's pc by
   computation), fuzz_strdup (the allocator engine's FuzzStrdup.fuzz_strdup_holds_TfibB) ---- *)
Lemma cti_fmalloc : forall fxk : YK11.FPState,
  PRH_FnAlloc.tfuzz_malloc_specX (fx := fxk) (rc := rc) (cp := CP) (PI := PIA) (RL := RLA) (L := A_prog_listing)
    (PA := PA) TA ARI SKA.
Proof.
intros fxk.
eapply (FMA.fuzz_malloc_holds (fx := fxk) (rc := rc) (SK := SKA) TA);
  first [ exact (cti_amalloc rc fxk) | exact (cti_apoison fxk) | exact PLA.palib_A
        | exact FAA.acc_pal_pst_ok_A | exact ADA.TfibB_syms ].
Qed.

(* ---- THE REALLOC WALK at the instance: FuzzReallocAp.fuzz_realloc_holds_Ap at TfibB, ARcfx = iface_ARx
   (the D2p driver's Ent102DrvTopA3.v drv3_fuzz_realloc_A, copied): PAL PALibA.palib_A; PST := FuzzReallocAp.ra_cells with
   PST_cells FuzzReallocAp.ra_cell_in and the static facts cti_ra_* above; FMALLOC cti_fmalloc; AUNPOISON / APOISON
   cti_aunpoison / cti_apoison; CF_unpoison / CF_poison by computation; the RELRO rows CfAroPresetA.* and the range
   equation by computation; AREAL_cf the realloc keep row cti_areal ---- *)
Lemma cti_freal : forall fxk : YK11.FPState,
  PRH_FnAlloc.tfuzz_realloc_specX (fx := fxk) (rc := rc) (ci := CfImg_A) (cp := CP) (RL := RLA) (PI := PIA)
    (L := A_prog_listing) (PA := PA) TA ARI SKA.
Proof.
intros fxk.
eapply (FRA.fuzz_realloc_holds_Ap (fx := fxk) (rc := rc) (ci := CfImg_A) (SK := SKA) TA PLA.palib_A FRA.ra_cells).
all: first
  [ exact cti_ra_pst_ok | exact FRA.ra_cell_in | exact cti_ra_pst_errno | exact cti_ra_most_ok
  | exact cti_ra_own_ok | exact cti_ra_pst_sub | exact cti_ra_own_out | exact cti_ra_most_out
  | exact (cti_fmalloc fxk) | exact (cti_aunpoison fxk) | exact (cti_apoison fxk)
  | exact (cti_areal rc fxk) | exact cti_ra_cf_unpoison | exact cti_ra_cf_poison
  | exact CAA.relro_seg_preset_A | exact (CAA.errno_relro_preset_A TA ADA.TfibB_syms)
  | exact CAA.relro_top_preset_A | exact CAA.ro_reads_nw_preset_A | exact cti_ra_pst_aro
  | (split; vm_compute; reflexivity) ].
Qed.

Lemma cti_amcpy_cf : forall fy : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fy) SEGS TA
    (fun ly S Hp W mem md => YG0ncf.ARcf (cp := CP) SEGS TA ly S Hp W mem md) OCpy (SIGMA AS___asan_memcpy).
Proof.
intros fy. assert (E : SIGMA AS___asan_memcpy = pc_asan_memcpy (as_code TA)) by (vm_compute; reflexivity).
rewrite E.
exact (PCA.prow_asan_memcpy_xm_A (fx := fy) TA _ _
  (YGcallcf.AR_laws_x_cf (cp := CP) SEGS TA (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TA)) ADA.TfibB_syms).
Qed.

Lemma cti_strdup : forall fxk : YK11.FPState,
  PRH_FnAlloc.tfuzz_strdup_specX (fx := fxk) (rc := rc) (cp := CP) (PI := PIA) (RL := RLA) (L := A_prog_listing)
    (PA := PA) TA ARI SKA.
Proof.
intros fxk.
eapply (FDA.fuzz_strdup_holds_TfibB (fx := fxk) (rc := rc) (ci := CfImg_A) (SK := SKA));
  first [ exact (cti_fmalloc fxk) | exact (cti_amcpy_cf fxk) | exact PLA.palib_A ].
Qed.

(* ---- PJSTR: S6PjString.pj_string_holds at the instance, its image facts S6ImgWit's / S1ImgA's /
   S6PalLitRefute's ---- *)
Lemma cti_pjstr : forall fxk : YK11.FPState,
  @PRH_FnPj.tpj_string_specX fxk rc CfImg_A CP PIA RLA A_prog_listing PA TA ARI SKA CTXA.
Proof.
intros fxk.
eapply (PSS.pj_string_holds (fx := fxk) (rc := rc) (ci := CfImg_A) (RL := RLA) (PA := PA) SKA TA ARI).
all: first
  [ exact cti_laws | exact PLA.palib_A | exact (SWA.s6w_ent_pj_string (rc := rc)) | exact (SWA.s6w_obj (rc := rc))
  | exact (SWA.s6w_pab (rc := rc)) | exact (cti_ams fxk) | exact (cti_strdup fxk) | exact S1A.pst_in_img_A
  | exact (SLA.pal_lit_A (rc := rc)) | exact cti_isv ].
Qed.

(* ---- round_trip_text's newline literal is a kept image literal: read_members_inst's checker, by computation ---- *)
Lemma cti_litnl : @kept_img rc A_prog_listing PA TA (@RTA.RTT_LITNL_A rc) 1.
Proof. apply RMA.rmA_kept_b_ok. vm_compute. reflexivity. Qed.

(* ---- PJFREE: S6PjFreeTop.pj_free_holds at the instance, CTX0 := iface_ctx0, n := DOC_D (the D2p driver's
   Ent102DrvTopA3.v drv3_pj_free_A, adapted): LAWS cti_laws, TL PALibA.palib_A, VISF cti_visf (the cf instance's
   frame-hull visibility through the first conjunct), the image facts S6ImgWit.s6w_*, AIM cti_ams, FREE cti_ffree ---- *)
Lemma cti_visf : YGcfFsVis.ARx_frame_hull_vis SEGS TA ARI.
Proof.
intros ly S Hp W mem md cid pos [HA _] Hin.
exact (YGcfFsVis.ARx_frame_hull_vis_cf_ok _ TA (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TA) ly S Hp W mem md cid pos HA Hin).
Qed.
Lemma cti_pjfree : forall fxk : YK11.FPState,
  @PRH_FnPj.tpj_free_specX fxk rc CfImg_A CP PIA RLA A_prog_listing PA TA ARI SKA CTXA PRH_Base.DOC_D.
Proof.
intros fxk.
eapply (PFT.pj_free_holds (fx := fxk) (rc := rc) (PA := PA) SKA TA ARI).
all: first
  [ exact cti_laws | exact PLA.palib_A | exact cti_visf | exact (SWA.s6w_ent_pj_free (rc := rc))
  | exact (SWA.s6w_obj (rc := rc)) | exact (SWA.s6w_pab (rc := rc)) | exact (SWA.s6w_pst_img (rc := rc))
  | exact (SWA.s6w_pst_ro (rc := rc)) | exact (SWA.s6w_ret_free (rc := rc)) | exact (cti_ams fxk)
  | exact (cti_ffree fxk) ].
Qed.

(* ---- TXPUT: TxPut102A_Inst.tx_put_holds_A at the instance, CTX0 := iface_ctx0 (its relation ARcfx is iface_ARx by
   conversion): TB AD2l.TfibB_syms, AI cti_amcpy_cf (the memcpy row at ARcf), AREAL the named realloc row
   cti_areal (TxPut102A_Base.tp_AREAL is its _k keep form), AREALN the null keep row cti_arealn; the depot row is
   proved inside TxPut102A_Inst (tp_arx_depot_A) ---- *)
Lemma cti_txput : forall fxk : YK11.FPState,
  @PRH_FnTx.ttx_put_specX fxk rc CfImg_A CP PIA RLA A_prog_listing PA TA ARI SKA CTXA.
Proof.
intros fxk.
first
  [ (eapply (TPA.tx_put_holds_A (fx := fxk) (rc := rc) TA SKA CTXA);
     first [ exact ADA.TfibB_syms | exact (cti_amcpy_cf fxk) | exact (cti_areal rc fxk)
           | exact (cti_arealn rc fxk) ])
  | (pose proof (TPA.tx_put_holds_A (fx := fxk) (rc := rc) TA SKA CTXA ADA.TfibB_syms (cti_amcpy_cf fxk)
       (cti_areal rc fxk) (cti_arealn rc fxk)) as HTX; exact HTX) ].
Qed.

(* ---- PJWRITE's callee walks at the instance (the D2p driver's Ent102DrvTopA3.v drv3_imgsh_A / drv3_asmr0_A /
   drv3_wv_hjt_A / drv3_put_A / drv3_indent_A / drv3_put_string_A / drv3_write_value_A, adapted): the image facts of
   the witness files S7a_put_wit / S7a_indent_wit / PRW_S7bWit / PRW_S7bLitWit, the frame laws above, the memcpy row at
   iface_ARx, the strlen row cti_strlen, the snprintf row PSnpRowA.snprintf_row_A_inst; put's HREAL the realloc walk
   cti_freal ---- *)
Lemma cti_imgsh : PHS.ARx_img_shadow_vis SEGS ARI.
Proof.
intros ly S Hp W mem md a [HA _] Ha.
exact (ISA.tfib_img_shadow_vis_cf (cp := CP) _ TA ADA.TfibB_syms ly S Hp W mem md a HA Ha).
Qed.
Lemma cti_asmr0 : forall fy : YK11.FPState,
  YGcallMxmn.astack_malloc_realizes_xm (fx := fy) ABA.tfibsegs TA
    (fun ly S Hp W mem md => YG0ncf.ARcf (rc := rc) (cp := CP) ABA.tfibsegs TA ly S Hp W mem md /\
       YG0ncf.xs_placed_cf (rc := rc) ly S) 0.
Proof.
intros fy.
exact (YGcallMxmn.astack_malloc_realizes_xm_conj (fx := fy) ABA.tfibsegs TA
  (YG0ncf.ARcf (rc := rc) (cp := CP) ABA.tfibsegs TA) (fun ly S => YG0ncf.xs_placed_cf (rc := rc) ly S) 0
  YGcallScf.xs_placed_cf_set_fs
  (FC01.stack_malloc0_contract_xm (fx := fy) TA (YG0ncf.ARcf (rc := rc) (cp := CP) ABA.tfibsegs TA)
    (FCifaceCf.fs_iface_ARcf (cp := CP) ABA.tfibsegs TA (YG0lawscf.AR_laws_ok_cf (cp := CP) ABA.tfibsegs TA))
    ADA.TfibB_syms)).
Qed.
Lemma cti_amcpy : forall fy : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fy) SEGS TA ARI OCpy (SIGMA AS___asan_memcpy).
Proof.
intros fy. assert (E : SIGMA AS___asan_memcpy = pc_asan_memcpy (as_code TA)) by (vm_compute; reflexivity).
rewrite E. exact (PCA.prow_asan_memcpy_xm_A (fx := fy) TA ARI _ cti_laws ADA.TfibB_syms).
Qed.
(* write_value's HJT: the seven table words of the tag switch, one closed boolean each, over the checkers above *)
Definition cti_wv_ja (k : nat) : Z := @pa_val rc A_prog_listing PA (A_OBJ 2) + PWV.WV_JT + 4 * Z.of_nat k.
Definition cti_wv_jt_b (k : nat) : bool :=
  cti_vm_b SEGS (cti_wv_ja k) 4 (PWV.WV_JTW (rc := rc) (PA := PA) k) &&
  (0 <=? PWV.WV_JTW (rc := rc) (PA := PA) k) && (PWV.WV_JTW (rc := rc) (PA := PA) k <=? 2 ^ 31 - 1) &&
  (0 <=? cti_wv_ja k) && (cti_wv_ja k + 4 <=? YG0f.kLowMemEnd) &&
  ((cti_wv_ja k + 4 <=? @pa_val rc A_prog_listing PA (A_OBJ 0)) ||
   (@pa_val rc A_prog_listing PA (A_OBJ 0) + 8 <=? cti_wv_ja k)) &&
  ((cti_wv_ja k + 4 <=? @pa_val rc A_prog_listing PA (A_OBJ 12)) ||
   (@pa_val rc A_prog_listing PA (A_OBJ 12) + 8 <=? cti_wv_ja k)) &&
  YP08.zallb (cti_ro_byte_b SEGS RLO RHI TA) (cti_wv_ja k) 4.
Lemma cti_wv_jt_all : forallb cti_wv_jt_b (seq 0 7) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cti_wv_hjt : forall k : nat, (k < 7)%nat ->
  YI04.val_mem SEGS (fun _ => None) (cti_wv_ja k) 4 (PWV.WV_JTW (rc := rc) (PA := PA) k) /\
  0 <= PWV.WV_JTW (rc := rc) (PA := PA) k <= 2 ^ 31 - 1 /\ 0 <= cti_wv_ja k /\
  cti_wv_ja k + 4 <= YG0f.kLowMemEnd /\
  (cti_wv_ja k + 4 <= @pa_val rc A_prog_listing PA (A_OBJ 0) \/
   @pa_val rc A_prog_listing PA (A_OBJ 0) + 8 <= cti_wv_ja k) /\
  (cti_wv_ja k + 4 <= @pa_val rc A_prog_listing PA (A_OBJ 12) \/
   @pa_val rc A_prog_listing PA (A_OBJ 12) + 8 <= cti_wv_ja k) /\
  (forall i, 0 <= i < 4 -> YG0d.in_img SEGS (cti_wv_ja k + i) /\ in_roP SEGS RLO RHI (cti_wv_ja k + i) /\
     ~ Exists (YG0n.in_zr (cti_wv_ja k + i)) (YG0f.as_owned_static TA) /\
     ~ (YG0f.as_errno TA <= cti_wv_ja k + i < YG0f.as_errno TA + 4)).
Proof.
intros k Hk.
assert (H : cti_wv_jt_b k = true).
{ pose proof cti_wv_jt_all as A. rewrite List.forallb_forall in A. apply A. apply List.in_seq. lia. }
unfold cti_wv_jt_b in H.
apply andb_prop in H as [H Hro]. apply andb_prop in H as [H Hd12]. apply andb_prop in H as [H Hd0].
apply andb_prop in H as [H Hlow]. apply andb_prop in H as [H Ha0]. apply andb_prop in H as [H Hv1].
apply andb_prop in H as [Hvm Hv0].
apply Z.leb_le in Hv0. apply Z.leb_le in Hv1. apply Z.leb_le in Ha0. apply Z.leb_le in Hlow.
split; [exact (cti_vm_sound _ _ _ _ Hvm)|].
split; [split; [exact Hv0 | exact Hv1]|].
split; [exact Ha0|]. split; [exact Hlow|].
split; [apply Bool.orb_true_iff in Hd0 as [D|D]; apply Z.leb_le in D; [left|right]; exact D|].
split; [apply Bool.orb_true_iff in Hd12 as [D|D]; apply Z.leb_le in D; [left|right]; exact D|].
exact (cti_ro_range_sound _ _ _ _ _ 4 Hro).
Qed.
(* put: S7a_put.put_holds, HREAL the realloc walk cti_freal *)
Lemma cti_put : forall fxk : YK11.FPState,
  PRH_FnWriter.tput_specX (fx := fxk) (rc := rc) (cp := CP) (PI := PIA) (RL := RLA) (L := A_prog_listing) (PA := PA)
    TA ARI SKA CTXA.
Proof.
intros fxk.
eapply (S7P.put_holds (fx := fxk) (rc := rc) (cp := CP) (SK := SKA) (PA := PA) TA ARI).
all: first
  [ exact cti_laws | exact PLA.palib_A | exact S7PW.s7p_ent_A | exact S7PW.s7p_obj_A
  | exact (cti_freal fxk) | exact (cti_amcpy fxk) | exact cti_imgsh | exact cti_visf | exact S7PW.s7p_pst_A
  | exact S7PW.s7p_head_wide | exact S7PW.s7p_pstro_A | exact S7PW.s7p_zs_aligned_A
  | exact S7PW.s7p_pab_A | exact (conj (Z.le_refl _) (Z.le_refl _)) ].
Qed.
(* indent: S7a_indent.indent_holds, its HPUT cti_put *)
Lemma cti_indent : forall fxk : YK11.FPState,
  PRH_FnWriter.tindent_specX (fx := fxk) (rc := rc) (cp := CP) (PI := PIA) (L := A_prog_listing) (PA := PA)
    TA ARI SKA CTXA.
Proof.
intros fxk.
eapply (S7I.indent_holds (fx := fxk) (rc := rc) (cp := CP) (SK := SKA) (PA := PA) TA ARI _ cti_laws PLA.palib_A
  S7IW.s7w_ent_A CTXA).
all: first [ exact (cti_put fxk) | exact (S7IW.s7w_hlit_A ARI _ cti_laws) | exact S7IW.s7w_pstro_A ].
Qed.
(* put_string: PRW_put_string.put_string_holds, its PUT cti_put *)
Lemma cti_putstr : forall fxk : YK11.FPState,
  PRH_FnWriter.tput_string_specX (fx := fxk) (rc := rc) (cp := CP) (PI := PIA) (L := A_prog_listing) (PA := PA)
    TA ARI SKA CTXA.
Proof.
intros fxk.
eapply (PPS.put_string_holds (fx := fxk) (rc := rc) (cp := CP) (SK := SKA) (PA := PA) TA ARI).
all: first
  [ exact cti_laws | exact PLA.palib_A | exact S7BW.s7bw_ps_ent | exact S7BW.s7bw_uar
  | exact S7BW.s7bw_obj | exact S7BW.s7bw_objs_disj | exact S7BW.s7bw_uarc
  | exact (@YC4aP.pa_segs_low _ _ PA) | exact PLA.palib_errno_A | exact cti_ownlow
  | exact (YGcallScf.stack_malloc_x_any _ ARI) | exact (cti_asmr0 fxk) | exact S7BW.s7bw_sm0
  | exact S7PW.s7p_head_wide | exact ADA.TfibB_ok | exact cti_imgsh | exact cti_visf
  | exact S7BW.s7bw_hpab | exact S7BW.s7bw_pst_ok_ps | exact S7BW.s7bw_pstro_A
  | exact cti_put | exact (S7BL.s7bl_ps_hlit17 ARI _ cti_laws)
  | exact (S7BL.s7bl_ps_hlit85 ARI _ cti_laws) | exact (S7BL.s7bl_ps_hlit87 ARI _ cti_laws)
  | exact (S7BL.s7bl_ps_hlit91 ARI _ cti_laws) | exact (S7BL.s7bl_ps_hlit93 ARI _ cti_laws)
  | exact (S7BL.s7bl_ps_hlit89 ARI _ cti_laws) | exact cti_strlen
  | exact cti_amcpy | exact S7BW.s7bw_ps_snp_img
  | exact (fun fx0 => PSR.snprintf_row_A_inst rc fx0)
  | exact cti_asfx | exact cti_fflx | exact cti_sfx ].
Qed.
(* write_value at every depth: PRW_write_value.write_value_holds, PUT / PUTSTR / INDENT the three walks above *)
Lemma cti_wval : forall (fxk : YK11.FPState) (n : nat),
  PRH_FnWriter.twrite_value_specX (fx := fxk) (rc := rc) (cp := CP) (PI := PIA) (RL := RLA) (L := A_prog_listing)
    (PA := PA) TA ARI SKA CTXA n.
Proof.
intros fxk n.
eapply (PWV.write_value_holds (rc := rc) (cp := CP) (SK := SKA) (PA := PA) TA ARI).
all: first
  [ exact cti_laws | exact PLA.palib_A | exact S7BW.s7bw_wv_ent | exact S7BW.s7bw_wv_obj
  | exact cti_wv_hjt | exact (S7BL.s7bl_wv_hlit ARI _ cti_laws) | exact S7BW.s7bw_pstro_A
  | exact cti_put | exact cti_putstr | exact cti_indent | exact S7PW.s7p_head_wide | exact cti_strlen ].
Qed.

(* ---- CARRIED callee text (owner in the header): tx_value's, at the instance, at CTX0 := iface_ctx0 and every float
   state, written as the D2p record writes its texts ---- *)
Hypothesis H_txt_tx_value_A : forall fxk : YK11.FPState,
  @PRH_FnTx.ttx_value_specX fxk rc CfImg_A CP PIA RLA A_prog_listing PA TA ARI SKA CTXA PRH_Base.DOC_D.

(* ---- GROW: PwGrow.grow_holds_Aprime at the instance (its relation ARcf /\ xs_placed_cf is iface_ARx by
   conversion), HREALLOC the realloc walk cti_freal, so the named realloc row reaches GROW ---- *)
Lemma cti_grow : forall fxk : YK11.FPState,
  PRH_FnReader.tgrow_specX (fx := fxk) (rc := rc) (cp := CP) (PI := PIA) (L := A_prog_listing) (PA := PA) TA ARI SKA
    CTXA.
Proof.
intros fxk.
first
  [ exact (PGA.grow_holds_Aprime (fx := fxk) (rc := rc) (ci := CfImg_A) (RL := RLA) SKA (cti_freal fxk) CTXA)
  | (apply (PGA.grow_holds_Aprime SKA); exact (cti_freal fxk)) ].
Qed.

(* ---- PJSET: pj_setA_iface.tpj_set_specX_A_of_callees at CTX0 := iface_ctx0, dd := DOC_D (its memcpy,
   memset, LAWS, VIS, PAL and hull discharged inside it): GET cti_get, FREE cti_pjfree, GROW cti_grow, STRDUP
   cti_strdup ---- *)
Lemma cti_pjset : forall fxk : YK11.FPState,
  @PRH_FnPj.tpj_set_specX fxk rc CfImg_A CP PIA RLA A_prog_listing PA TA ARI SKA CTXA PRH_Base.DOC_D.
Proof.
intros fxk.
eapply (PSI.tpj_set_specX_A_of_callees CTXA PRH_Base.DOC_D).
all: first [ exact cti_get | exact cti_pjfree | exact cti_grow | exact cti_strdup ].
Qed.

(* ---- PJWRITE: PRW_pj_write.pjw_holds_lc at the instance, CTX0 := iface_ctx0, n := DOC_D (the D2p driver's
   Ent102DrvTopA3.v drv3_pj_write_A, adapted): LAWS cti_laws, segs_low the class field pa_segs_low, AMS cti_ams, the
   image facts PRW_S7bWit.s7bw_pjw_* / s7bw_pstro_A / s7bw_pst_ok_pjw and PRW_S7bLitWit.s7bl_pjw_hlit, S9_CF the first
   conjunct, HHCAP by reflexivity; HWV cti_wval, HPUT cti_put, HFREE cti_ffree; pjw_ARGCNT is the second conjunct of
   PresetRoomCounts.counts_of_room_pos_rl at the call's model-run position (drv3_argcnt, inlined) ---- *)
Lemma cti_pjwrite : forall fxk : YK11.FPState,
  @PRH_FnWriter.tpj_write_specX fxk rc CfImg_A CP PIA RLA A_prog_listing PA TA ARI SKA CTXA PRH_Base.DOC_D.
Proof.
intros fxk.
eapply (PJW.pjw_holds_lc (fx := fxk) (rc := rc) (cp := CP) (SK := SKA) (PA := PA) TA ARI).
all: first
  [ exact cti_laws | exact (@YC4aP.pa_segs_low _ _ PA) | exact S7BW.s7bw_pjw_ent | exact (cti_ams fxk)
  | exact (cti_wval fxk) | exact cti_put | exact cti_ffree | exact S7BW.s7bw_pjw_ret | exact S7BW.s7bw_pstro_A
  | exact S7BW.s7bw_pst_ok_pjw | exact (S7BL.s7bl_pjw_hlit ARI _ cti_laws) | exact S7BW.s7bw_pjw_nl_img
  | exact (conj (Z.le_refl _) (Z.le_refl _))
  | exact (fun ly S Hp W mem md (H : ARI ly S Hp W mem md) => proj1 H)
  | (intros; hnf; intros;
     lazymatch goal with |- YGcfRoomLive.ccnt24 ?S' <= _ =>
       match goal with Hp : PresetRoomPos.iface_room_pos _ _ _ _ _ _ S' |- _ =>
         exact (proj2 (PresetRoomCounts.counts_of_room_pos_rl _ _ _ _ _ _ _ Hp)) end end) ].
Qed.

(* ---- PNOTING: PN102Top.tparse_noting_specX_A_iface from its four callee texts (the D2p driver's
   Ent102DrvTopA2.v drv2_parse_noting_A, adapted): fuzz_alloc_live PwAllocSurf.fuzz_alloc_live_holds, ran_out
   cti_ranout, check_reject_clean Crc102InstLive.check_reject_clean_holds_A102_inst_live with its bcmp row
   PRowCmp.pr_bcmp_xm_A (PresetD2pAPf.v crc_bcmp_A_holds, copied), and pj_parse by
   PjParseA_top.pj_parse_holds_A_tpv (parse_value by VrdTop.vrd_parse_value_holds inside it) at the rows cti_areal /
   cti_amalloc / cti_afree and the unpoison row cti_aunpoison ---- *)
Lemma cti_pjparse : forall (fxk : YK11.FPState) (CW : list (list Z)),
  PRH_FnPj.tpj_parse_specX (fx := fxk) (cp := CP) (PI := PIA) (RL := RLA) (PA := PA) TA ARI SKA CTXA CW.
Proof.
intros fxk CW.
exact (PPT.pj_parse_holds_A_tpv (fx := fxk) (rc := rc) (SK := SKA) (cti_areal rc) (cti_amalloc rc) (cti_afree rc)
  cti_aunpoison CTXA CW).
Qed.
Lemma cti_live : forall fxk : YK11.FPState,
  PRH_FnAlloc.tfuzz_alloc_live_specX (fx := fxk) (cp := CP) (PI := PIA) (RL := RLA) (PA := PA) TA ARI SKA.
Proof. intros fxk. exact (PAS.fuzz_alloc_live_holds (fx := fxk) (rc := rc) (SK := SKA) TA). Qed.
Lemma cti_crc : forall fxk : YK11.FPState,
  PRH_FnCheck.tcheck_reject_clean_specX (fx := fxk) (cp := CP) (PI := PIA) (RL := RLA) (PA := PA) TA ARI SKA.
Proof.
intros fxk.
exact (CRL.check_reject_clean_holds_A102_inst_live (fx := fxk) (rc := rc) (RL := RLA)
  (PRC.pr_bcmp_xm_A TA (@CRA.c102_ARx rc CfImg_A) _
    (YGcallcf.AR_laws_x_xs (cp := CP) OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs TA
       (YG0lawscf.AR_laws_ok_cf (cp := CP) OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs TA))
    ADA.TfibB_syms)).
Qed.
Lemma cti_pnoting : forall fxk : YK11.FPState,
  @PRH_FnCheck.tparse_noting_specX fxk rc CfImg_A CP PIA RLA A_prog_listing PA TA ARI SKA CTXA.
Proof.
intros fxk.
exact (PNT.tparse_noting_specX_A_iface (fx := fxk) (rc := rc) (cti_live fxk) (cti_pjparse fxk) cti_ranout cti_crc).
Qed.

(* ---- RTT: round_trip_text's walk at the D2p interface relation, Rtt102InstA.rtt_iface_A at CTX0 := iface_ctx0 ---- *)
Lemma cti_rtt : forall fxk : YK11.FPState,
  @PRH_FnCheck.tround_trip_text_specX fxk rc CfImg_A CP PIA RLA A_prog_listing PA TA ARI SKA CTXA.
Proof.
intros fxk.
exact (@RIA.rtt_iface_A fxk rc CTXA cti_same cti_pjfree (fun fy => cti_afree rc fy) cti_ffree cti_pnoting
  cti_litnl cti_txput H_txt_tx_value_A cti_pjwrite).
Qed.

(* ---- THE INSTANCE: the body of PresetD2pAPf.v's txt_check_round_trip_A at Ent102DrvTopA.v's binding ---- *)
Corollary crt102_top_TfibA_inst : forall fy : YK11.FPState,
  @PRH_FnCheck.tcheck_round_trip_specX fy rc CfImg_A CP PIA RLA A_prog_listing PA TA ARI SKA CTXA
    EIA.ia_mod_at EIA.ia_stamp.
Proof.
intros fy. rewrite <- cti_mod_at, <- cti_stamp.
apply @CTA.crt102_top_TfibA with (fx := fy) (rc := rc) (SK := SKA) (RL := RLA) (ARx := ARI)
  (LAWS := cti_laws) (ASM3 := cti_asm3 fy) (OWNLOW := cti_ownlow) (AMS := cti_ams fy) (CTX0 := CTXA)
  (RTT := cti_rtt) (ASFX := cti_asfx) (FFLX := cti_fflx) (SFX := cti_sfx) (FFLP := cti_fflp) (SETSH := cti_setsh)
  (PJFREE := cti_pjfree) (img_shadow_vis_x := cti_isv) (PJSTR := cti_pjstr) (PJSET := cti_pjset) (RANOUT := cti_ranout)
  (PJWRITE := cti_pjwrite) (PNOTING := cti_pnoting) (STRLEN := cti_strlen) (STRCMP := cti_strcmp) (SAME := cti_same)
  (FFREE := cti_ffree).
Qed.
End i.

Set Printing Implicit.
Unset Printing Notations.
Check @crt102_top_TfibA_inst.
About crt102_top_TfibA_inst.
Set Printing Notations.
Unset Printing Implicit.
Print Assumptions crt102_top_TfibA_inst.
