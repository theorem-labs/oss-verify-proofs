(* fuzz_preset, image B' (asan-ubsan, #102 pin d663f82d7f488d30, unstripped twin c90d4fa54d43160b): check_round_trip's
   contract AT THE D2p INSTANCE. rule 24: proves no function (kind: statement text, the instance corollary of Crt102TopB.crt102_topB_TfibB).
   THE STATEMENT of crt102_topB_TfibB_inst is the body of txt_check_round_trip_B (lib/AU/PresetD2pBPf.v:130-132), the
   text of the premise H_txt_check_round_trip_B (:280-281), at the binding lib/AU/Prog/Ent102DrvTopB.v gives the D2p
   Variables: a_mod_at := Ent102InstB.ia_mod_at, a_stamp := Ent102InstB.ia_stamp. It has no premise, so the D2p
   premise can cite it directly by unfolding txt_check_round_trip_B. This file does not Require PresetD2pBPf.v.
   THE BINDING (ctiB_mod_at / ctiB_stamp, by reflexivity): Ent102InstB.ia_mod_at / ia_stamp are Crt102ImgB.v's
   CRT_MOD_AT_B / CRT_STAMP_B at PA := PI_prog_B, the addresses crt102_topB_TfibB is stated at: pa_val of PI_prog_B is
   B_prog_val, and Crt102ImgB.v's offsets CRT_MOD_AT_OFF_B / CRT_STAMP_OFF_B are the numerals Ent102InstB.v adds to it.
   THE INSTANCE: B := YD2l.TfibB, ARx := PresetCfnB.iface_ARx at CfImg_B, RL := prh_room_live_a8,
   SK := PresetCfnB.preset_sink_head, CTX0 := PresetCfnB.iface_ctx0, exactly the arguments of txt_check_round_trip_B.
   T1's four image stand-ins and BOK are discharged inside crt102_topB_TfibB by their witnesses.
   DISCHARGED: all twenty-one of crt102_topB_TfibB's Section hypotheses, each at the instance, CTX0 := iface_ctx0 and
   every float state. The recipes of lib/AU/Prog/Ent102DrvTopB2.v / Ent102DrvTopB3.v (their drv2_ / drv3_ lemmas)
   are copied as local ctiB_ lemmas, not Required, so that the drivers can cite this corollary for their H_txt_check_round_trip_B (Ent102DrvTopB.v:80, Ent102DrvTopB2.v:171, Ent102DrvTopB3.v:315) without a Require cycle.
     LAWS YGcallcf.AR_laws_x_xs; OWNLOW YGcallcf.ARx_owned_low_law_xs; ASM3 FCxmCfxB.stack_malloc3_contract_xm_cfx_B;
     AMS AU/PRowSet.prow_asan_memset_xm_B (pc: ctiB_memset_pc); ASFX YGcallScf.astack_free_x_xs; FFLX
     YGcallScf.frame_flag_x_xs; SFX YGcallScf.stack_free_x_any; FFLP YG0scf.AR_flag_law_ok_cf (its first conjunct);
     SETSH FCxmCfxB.set_shadow_f5_contract_xm_cfx_B; IMGVIS YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover with the
     cover check ctiB_img_cover (the method of CrsTopBp.v crs_Bp_img_shadow, at CfImg_B's bounds); RANOUT
     FuzzAllocAccInstB102.fuzz_alloc_ran_out_holds_B_inst; STRLEN AU/PSstrRo.ps_strlen_xrom_xs_B (pc:
     ctiB_strlen_pc); STRCMP AU/PSstrRo.ps_strcmp_xrom_xs_B (pc: ctiB_strcmp_pc); SAME
     SameB_final.same_holds_B_TfibBx with STRCMP and CrcBInstBcmp.cbi_bcmp;
     PJSTR  ctiB_pjstr, pj_string_iface.tpj_string_B_preset_iface: MEMSET ctiB_ams; STRDUP ctiB_strdup,
            FuzzStrdupB.fuzz_strdup_holds_B at TfibB (TS YD2l.TfibB_syms; PAL PALibB.exvi_eh_palib; AI ctiB_amcpy_cf,
            PRowCpy.prow_asan_memcpy_xm_B at ARcf with the laws YGcallcf.AR_laws_x_cf; FMALLOC ctiB_fmalloc,
            FuzzMallocB_p102_holds.fuzz_malloc_holds_B with AMALLOC ctiB_amalloc (CfMallocKeepB.
            amalloc_realizes_cf_keep_closed_B, the malloc row in its keep form at every float state), pal_pst_ok
            FuzzAllocAccInstB102.acc_pal_pst_ok_B and OWN ctiB_own, OwnB_p102.own_holds_B with APOISON ctiB_apoison
            (CfPoisonB102.preset_apoison_cf_B102) and pal_poison ctiB_poison_pc);
     FFREE  ctiB_ffree, FuzzFreeB.fuzz_free_holds_B: AFREE ctiB_afree (CfFreeKeepB.afree_realizes_cf_rh_keep_B, the free
            row in its keep form at every float state), AUNPOISON ctiB_aunpoison (CfPoisonB102.preset_aunpoison_cf_B102),
            pal_unpoison ctiB_unpoison_pc, PAL / pal_pst_ok as above;
     PJFREE ctiB_pjfree, pj_free_iface.tpj_free_specX_B_preset_iface at DOC_D: XFF ctiB_ffree, XMS ctiB_ams;
     PJSET  ctiB_pjset, pj_set_iface.tpj_set_specX_B_preset_iface at dd := DOC_D, its six texts pjs_texts: GET
            ctiB_get, PjGetB.pj_get_holds_B_K0 at iface_ARx (LAWS ctiB_laws, PALib PALibB.exvi_eh_palib, ASC
            ctiB_strcmp); FREE ctiB_pjfree; GROW ctiB_grow, PwGrowBTop.grow_holds_B_inst with HREALLOC ctiB_freal;
            STRDUP ctiB_strdup; memcpy ctiB_amcpy (PRowCpy.prow_asan_memcpy_xm_B at iface_ARx, laws ctiB_laws); memset
            ctiB_ams. REALLOC ctiB_freal is FuzzReallocB_p102.fuzz_realloc_holds_B' at iface_ARx (Ent102DrvTopB3.v
            drv3_fuzz_realloc_B): OWN ctiB_own, MALLOC ctiB_fmalloc, AUNPOISON ctiB_aunpoison, AREAL_cf ctiB_areal
            (AllocAssembleB.arealloc_realizes_cf_B, the realloc wrapper's keep _k row), PAL PALibB.exvi_eh_palib,
            pal_pst_ok FuzzAllocAccInstB102.acc_pal_pst_ok_B, pal_errno_relro CfAroPresetB.errno_relro_preset_AU;
     PJW    ctiB_pjw, PRW_pj_writeB_Inst.pj_write_holds_B_inst at n := DOC_D: HPUT ctiB_put (PutB.put_holds_B, H_real
            ctiB_freal, H_amc ctiB_amcpy; Ent102DrvTopB3.v drv3_put_B), HFREE ctiB_ffree, pjw_ARGCNT by
            PresetRoomCounts.counts_of_room_pos_rl (Ent102DrvTopB3.v drv3_argcnt, inlined); HWV ctiB_wval,
            WriteValueB_Inst.write_value_holds_B at every depth (Ent102DrvTopB3.v drv3_write_value_B; it cites
            WriteValueB_Wit.v's image witnesses itself): PUT ctiB_put, INDENT ctiB_indent (IndentB_Top.indent_holds_B),
            PUTSTR ctiB_pstr (PutStringB_SnpWit.put_string_holds_B_owner: ASM0 ctiB_asm0x, AMCPY ctiB_amcpy,
            K := STK_RT_PRINTF, the snprintf row ctiB_snprintf, PSnpRowB.snprintf_row_B_inst);
     PNOTING ctiB_pnoting, PN102BTop.tparse_noting_specX_TfibB (Ent102DrvTopB2.v drv2_parse_noting_B): HLIVE
            FuzzAllocAccInstB102.fuzz_alloc_live_holds_B_inst, HRO ctiB_ranout, HCRC ctiB_crc
            (CrcBInstBcmp.check_reject_clean_holds_B_inst_bcmp with the image shadow
            AImgShadowVisCfB.tfib_img_shadow_vis_cf_B), HPJ ctiB_pjparse (pj_parse_top.pj_parse_holds_Bp: AMS
            ctiB_ams, TGR grow_holds_B_inst with ctiB_freal, TPS ctiB_pstring (PSB_Inst.parse_string_holds_B_inst with
            ctiB_fmalloc and ctiB_afree), AF ctiB_afree, AU ctiB_aunpoison, TLIT ctiB_lit (literal_bridge.literal_holds
            at iface_ARx: ctiB_laws, PALibB.exvi_eh_palib, ctiB_strlen, CrcBInstBcmp.cbi_bcmp), ASM0 ctiB_asm0
            (FCm01xm.stack_malloc0_contract_xm at ARcf), CPY ctiB_amcpy_cf, FMALLOC ctiB_fmalloc);
     RTT    ctiB_rtt, Rtt102InstB.rtt_iface_B at CTX0 := iface_ctx0: TSAME ctiB_same, TPJF ctiB_pjfree, AFK ctiB_afree,
            TFF ctiB_ffree, TPN ctiB_pnoting, LITNL ctiB_litnl (by computation at TfibB, the method of BTxLine.v's
            tl_lit_img_TfibB for the same literal Rtt102TB.RTT_LITNL_B, its value pinned by ctiB_litnl_pin), TXPUT
            ctiB_txput, TXVAL ctiB_txval, TPJW ctiB_pjw. Its two tx texts:
            TXPUT ctiB_txput, TxPut102B_Inst.tx_put_holds_B_inst at TfibB: TB YD2l.TfibB_syms, AREAL ctiB_areal
            (tp_AREAL is the keep _k row), AREALN ctiB_arealn (AllocAssembleB.arealloc_null_realizes_cf_B, the NULL
            row tp_AREALN), AI ctiB_amcpy;
            TXVAL ctiB_txval, BTxValue.tx_value_B_holds at TfibB and iface_ARx, n := DOC_D: LAWS ctiB_laws, PAL
            PALibB.exvi_eh_palib, tv_jt_own BTxValue.tv_jt_own_TfibB, ASx ctiB_strlen, TXPUT ctiB_txput, TXSTR
            ctiB_txstr, zs_aligned BTxLine.tl_zs_aligned_TfibB, img_shadow_vis_x ctiB_imgvis, tv_img_cf_box
            BTxLine.tl_img_cf_box_B, tl_lit_img BTxLine.tl_lit_img_TfibB, tv_lit_img BTxValue.tv_lit_img_TfibB (tx_line
            is discharged inside it by BTxLine.tx_line_B_holds). TXSTR ctiB_txstr is BTxString.tx_string_B_holds at
            TfibB and iface_ARx: LAWS ctiB_laws, PAL PALibB.exvi_eh_palib, ASM0 ctiB_asm0x (ctiB_asm0 kept across
            xs_placed_cf; Ent102DrvTopB3.v drv3_asmr0_B), OWNLOW ctiB_ownlow, SMX YGcallScf.stack_malloc_x_any,
            img_shadow_vis_x ctiB_imgvis, TXPUT ctiB_txput, ASFX / FFLX / SFX / FFLP ctiB_asfx / ctiB_fflx / ctiB_sfx /
            ctiB_fflp, FAL64 ctiB_fal64 (YG0scf.frame_facts_cf's page-aligned fake stack, the proof of SameB_walk.v
            SMB_FR64), and the image facts pal_stack_malloc0 / pal_uar_img / cf_img_ok / img_cf_box / zs_aligned /
            pal_pst_static / ts_lit_img_B / ts_hex_img_B by BTxStrWitB.v's tsw_* witnesses at TfibB.
   CARRIED: nothing. The four allocator rows the walks take are proved on this head and cited by name at every float
   state (ctiB_amalloc, ctiB_afree, ctiB_areal, ctiB_arealn). D2p's own allocator premises (PresetD2pBPf.v:235-238;
   its H_amalloc is `forall rc` only, inside a Section under `Existing Instance YK11.fx0`, :168) are not needed here.
   Image-side modules are cited FULLY QUALIFIED; no image-A module. The numerals in the code are the ones the restated
   texts carry: ASM3's frame class 3, ASFX's flag value 0 and address range 0 .. 2 ^ 64, SETSH's shadow value 245, and
   the newline literal's length 1 (Rtt102InstB.v's LITNL); and, in ctiB_litnl's proof only, the terms of kept_img
   (PRH_Base.v): its margin 64 and the errno word's width 4, with the literal's const-shadow cell value 2 that the
   proof checks by computation; and ctiB_litnl_pin's 0x211e0, the newline literal's address in the image B'
   (asan-ubsan, pin d663f82d7f48), which pins RTT_LITNL_B. ctiB_asm0 / ctiB_asm0x add ASM0's frame class 0 and
   ctiB_fal64 the alignment 64 / 4096 of frame_facts_cf, the numbers those texts carry. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YF0m YB1v YImgShadowCover YImgShadowCoverCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require FCxmCfxB PRowSet PSstrRo PresetCfnB Ent102InstB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require FuzzAllocAccInstB102 SameB_final CrcBInstBcmp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Crt102ImgB Crt102TopB.
(* stage 1: the cited walks of pj_string, fuzz_strdup, fuzz_malloc, own, fuzz_free and round_trip_text at the instance *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YGcfHp YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PRowCpy CfPoisonB102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require pj_string_iface FuzzStrdupB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require FuzzMallocB_p102_holds OwnB_p102 FuzzFreeB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Rtt102TB Rtt102InstB.
(* stage 2: the cited walks of pj_get, grow, fuzz_realloc, pj_set, pj_free, put, pj_write, parse_noting (pj_parse,
   parse_string, literal, check_reject_clean), tx_put, tx_string and tx_value at the instance *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocKKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfAroPresetB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PjGetB PwGrowBTop FuzzReallocB_p102 pj_set_iface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PRW_pj_writeB_Inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfReallocComposeKeep FCifaceCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require FCm01xm AImgShadowVisCfB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require pj_free_iface PutB PSB_Inst literal_bridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require pj_parse_top PN102BTop TxPut102B_Inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require BTxLine BTxString BTxValue BTxStrWitB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AllocAssembleB CfFreeKeepB CfMallocKeepB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallSnp YGcallSnpCk YE22.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require IndentB_Top PutStringB_SnpWit PSnpRowB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require WriteValueB_Inst.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Module CTB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.Crt102TopB.
Module CIB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.Crt102ImgB.
Module CFB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Module EIB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Ent102InstB.
Module DLB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YD2l.
Module FMB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YF0m.
Module BVB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YB1v.
Module FCB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.FCxmCfxB.
Module RSB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PRowSet.
Module PSB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSstrRo.
Module FAB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.FuzzAllocAccInstB102.
Module SMB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.SameB_final.
Module CBB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.CrcBInstBcmp.
Module RCB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PRowCpy.
Module CPB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.CfPoisonB102.
Module PLB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PALibB.
Module PJB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.pj_string_iface.
Module SDB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.FuzzStrdupB.
Module MLB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.FuzzMallocB_p102_holds.
Module OWB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.OwnB_p102.
Module FFB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.FuzzFreeB.
Module RTB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.Rtt102TB.
Module RIB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.Rtt102InstB.
Module PGB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.PjGetB.
Module GRB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.PwGrowBTop.
Module RAB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.FuzzReallocB_p102.
Module PSI := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.pj_set_iface.
Module PWB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.PRW_pj_writeB_Inst.
Module CAB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.CfAroPresetB.
Module PFI := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.pj_free_iface.
Module PTB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.PutB.
Module PSS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.PSB_Inst.
Module LTB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.literal_bridge.
Module PPT := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.pj_parse_top.
Module PNB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.PN102BTop.
Module TPI := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.TxPut102B_Inst.
Module F01 := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.FCm01xm.
Module ISV := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.AImgShadowVisCfB.
Module BTL := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.BTxLine.
Module BTS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.BTxString.
Module BTV := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.BTxValue.
Module TSW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.BTxStrWitB.
Module AAB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.AllocAssembleB.
Module CFK := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.CfFreeKeepB.
Module CMK := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.CfMallocKeepB.
Module IDB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.IndentB_Top.
Module PSW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.PutStringB_SnpWit.
Module SRB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.PSnpRowB.
Module WVB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.WriteValueB_Inst.

(* ---- closed checks (vm_compute on closed goals) ---- *)
(* the __asan_memset entry of TfibB's code record is the listing's symbol *)
Lemma ctiB_memset_pc : B_prog_sigma AS___asan_memset = pc_asan_memset (as_code DLB.TfibB).
Proof. vm_compute. reflexivity. Qed.
(* the strlen / strcmp trampolines of CfImg_B are the listing's __wrap_strlen / __wrap_strcmp *)
Lemma ctiB_strlen_pc : B_prog_sigma AS___wrap_strlen = @cf_pc_strlen CfImg_B.
Proof. vm_compute. reflexivity. Qed.
Lemma ctiB_strcmp_pc : B_prog_sigma AS___wrap_strcmp = @cf_pc_strcmp CfImg_B.
Proof. vm_compute. reflexivity. Qed.
(* the B' image's shadow cover over CfImg_B's [cf_img_lo, cf_img_top) *)
Lemma ctiB_img_cover :
  YImgShadowCover.img_shadow_cover FMB.Tfib_zero_shadow FMB.Tfib_const_shadow
    (@cf_img_lo CfImg_B) (@cf_img_top CfImg_B) = true.
Proof. vm_compute. reflexivity. Qed.

Section i. Context {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Notation PB := (@PI_prog_B rc).
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation SIGMA := (@pa_sigma rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation RLO := (@pa_relro_lo rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation RHI := (@pa_relro_hi rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation TB := DLB.TfibB.
#[local] Notation CP := CfParams_preset.
#[local] Notation RLB := (@PRH_Base.prh_room_live_a8 CfParams_preset).
#[local] Notation ARIB := (@CFB.iface_ARx rc B_prog_listing (@PI_prog_B rc) CfImg_B DLB.TfibB).
#[local] Notation SKB := CFB.preset_sink_head.
#[local] Notation PIB := CFB.preset_prh_img.
#[local] Notation CTXB := CFB.iface_ctx0.

(* ---- the binding: the D2p Variables at Ent102DrvTopB.v's values are crt102_topB_TfibB's literal addresses ---- *)
Lemma ctiB_mod_at : CIB.CRT_MOD_AT_B (PA := @PI_prog_B rc) = EIB.ia_mod_at.
Proof. reflexivity. Qed.
Lemma ctiB_stamp : CIB.CRT_STAMP_B (PA := @PI_prog_B rc) = EIB.ia_stamp.
Proof. reflexivity. Qed.

(* ---- the fourteen discharges, each at the instance ---- *)
Lemma ctiB_laws : AR_laws_x SEGS TB ARIB cf_head.
Proof. exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)). Qed.

Lemma ctiB_ownlow : ARx_owned_low_law SEGS TB ARIB.
Proof. exact (YGcallcf.ARx_owned_low_law_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)). Qed.

Lemma ctiB_asm3 : forall fy : YK11.FPState, YGcallMxmn.astack_malloc_realizes_xm (fx := fy) SEGS TB ARIB 3.
Proof. intros fy. exact (FCB.stack_malloc3_contract_xm_cfx_B (fx := fy) (rc := rc) (cp := CP) TB DLB.TfibB_syms). Qed.

Lemma ctiB_ams : forall fy : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fy) SEGS TB ARIB OSet (SIGMA AS___asan_memset).
Proof.
intros fy.
change (SIGMA AS___asan_memset) with (B_prog_sigma AS___asan_memset). rewrite ctiB_memset_pc.
change SEGS with BVB.tfibsegs.
exact (RSB.prow_asan_memset_xm_B TB ARIB cf_head ctiB_laws DLB.TfibB_syms).
Qed.

Lemma ctiB_asfx : forall ly S Hp W mem md mem' md' cid pos,
  ARIB ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned TB ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARIB ly (stack_free_state cid pos S) Hp W mem' md'.
Proof. exact (YGcallScf.astack_free_x_xs (rc := rc) (cp := CP) SEGS TB). Qed.

Lemma ctiB_fflx : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARIB ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned TB ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Proof. exact (YGcallScf.frame_flag_x_xs (rc := rc) (cp := CP) SEGS TB). Qed.

Lemma ctiB_sfx : forall ly S Hp W mem md cid pos, ARIB ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Proof. exact (YGcallScf.stack_free_x_any SEGS ARIB). Qed.

Lemma ctiB_fflp : forall ly S Hp (W : world SEGS) mem md cid pos, ARIB ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos).
Proof.
intros ly S Hp W mem md cid pos [HAR _] Hin.
exact (proj1 (YG0scf.AR_flag_law_ok_cf (rc := rc) (cp := CP) SEGS TB ly S Hp W mem md cid pos HAR Hin)).
Qed.

Lemma ctiB_setsh : forall fxk : YK11.FPState,
  YGcallMxmn.aset_shadow_realizes_xm (fx := fxk) SEGS TB ARIB (SIGMA AS___asan_set_shadow_f5) 245.
Proof. exact (FCB.set_shadow_f5_contract_xm_cfx_B (rc := rc) (cp := CP) TB DLB.TfibB_syms). Qed.

Lemma ctiB_imgvis : forall ly S Hp (W : world SEGS) mem md a,
  ARIB ly S Hp W mem md -> @cf_img_lo CfImg_B <= a < @cf_img_top CfImg_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof.
intros ly S Hp W mem md a [HAR _] Ha.
refine (YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover SEGS TB FMB.Tfib_zero_shadow FMB.Tfib_const_shadow
  (@cf_img_lo CfImg_B) (@cf_img_top CfImg_B) ctiB_img_cover _ _ ly S Hp W mem md a HAR Ha).
- rewrite (FMB.ts_zsh TB DLB.TfibB_syms). apply incl_refl.
- intros ly0. rewrite (FMB.ts_const TB DLB.TfibB_syms). unfold FMB.Tfib_const. apply incl_appr, incl_appr, incl_refl.
Qed.

Lemma ctiB_ranout : forall fxk : YK11.FPState,
  @PRH_FnAlloc.tfuzz_alloc_ran_out_specX fxk rc CP PIB RLB B_prog_listing PB TB ARIB SKB.
Proof. intros fxk. exact (FAB.fuzz_alloc_ran_out_holds_B_inst (fx := fxk) (rc := rc) (SK := SKB)). Qed.

Lemma ctiB_strlen : forall fxq : YK11.FPState,
  YGcallMxmn.astrlen_realizes_xrom (fx := fxq) SEGS TB ARIB RLO RHI (SIGMA AS___wrap_strlen).
Proof.
intros fxq.
change (SIGMA AS___wrap_strlen) with (B_prog_sigma AS___wrap_strlen). rewrite ctiB_strlen_pc.
change SEGS with BVB.tfibsegs.
exact (PSB.ps_strlen_xrom_xs_B (fx := fxq) (rc := rc) (cp := CP) TB DLB.TfibB_syms RLO RHI).
Qed.

Lemma ctiB_strcmp : forall fxq : YK11.FPState,
  YGcallMxmn.astrcmp_realizes_xrom (fx := fxq) SEGS TB ARIB RLO RHI (SIGMA AS___wrap_strcmp).
Proof.
intros fxq.
change (SIGMA AS___wrap_strcmp) with (B_prog_sigma AS___wrap_strcmp). rewrite ctiB_strcmp_pc.
change SEGS with BVB.tfibsegs.
exact (PSB.ps_strcmp_xrom_xs_B (fx := fxq) (rc := rc) (cp := CP) TB DLB.TfibB_syms RLO RHI).
Qed.

Lemma ctiB_same : forall fxk : YK11.FPState,
  @PRH_FnEx.tsame_specX fxk rc CP PIB RLB B_prog_listing PB TB ARIB SKB DOC_D.
Proof.
intros fxk.
exact (SMB.same_holds_B_TfibBx (fx := fxk) (rc := rc) SKB (ctiB_strcmp fxk) (CBB.cbi_bcmp (fx := fxk) (rc := rc)) DOC_D).
Qed.

(* ---- the allocator rows the cited walks take, in their keep forms at the D2p arguments (ci := CfImg_B,
   cp := CfParams_preset, tfibsegs / the listing's segments, TfibB), each at every float state (fuzz_malloc's and
   fuzz_free's texts take their row at their own call's float state) and each PROVED on this head, cited by name:
   ctiB_amalloc (CfMallocKeepB.amalloc_realizes_cf_keep_closed_B), ctiB_afree (CfFreeKeepB.afree_realizes_cf_rh_keep_B),
   ctiB_areal (AllocAssembleB.arealloc_realizes_cf_B, the realloc row fuzz_realloc's AREAL_cf and tx_put's AREAL take)
   and ctiB_arealn (AllocAssembleB.arealloc_null_realizes_cf_B, tx_put's AREALN). ---- *)
Lemma ctiB_amalloc : forall fy : YK11.FPState,
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fy) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset)
    BVB.tfibsegs DLB.TfibB.
Proof. intros fy. exact CMK.amalloc_realizes_cf_keep_closed_B. Qed.
Lemma ctiB_afree : forall fy : YK11.FPState,
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fy) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset)
    BVB.tfibsegs DLB.TfibB.
Proof. intros fy. exact CFK.afree_realizes_cf_rh_keep_B. Qed.
Lemma ctiB_areal : forall (fy : YK11.FPState) (Hp : list Z) (k : nat),
  YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (fx := fy) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset)
    (@YC4aP.pa_segs rc B_prog_listing (@PI_prog_B rc)) YD2l.TfibB Hp
    (@YC4aP.pa_sigma rc B_prog_listing (@PI_prog_B rc) YPsym.AS___wrap_realloc) k.
Proof. intros fy Hp k. exact (AAB.arealloc_realizes_cf_B rc fy Hp k). Qed.
Lemma ctiB_arealn : forall (fy : YK11.FPState) (Hp : list Z),
  YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep (fx := fy) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset)
    (@YC4aP.pa_segs rc B_prog_listing (@PI_prog_B rc)) YD2l.TfibB Hp
    (@YC4aP.pa_sigma rc B_prog_listing (@PI_prog_B rc) YPsym.AS___wrap_realloc).
Proof. intros fy Hp. exact (AAB.arealloc_null_realizes_cf_B rc fy Hp). Qed.

(* ---- STAGE 1: the image rows the cited walks take, at the instance ---- *)
(* the listing's __asan_poison_memory_region / __asan_unpoison_memory_region are CfImg_B's, by computation *)
Lemma ctiB_poison_pc : SIGMA AS___asan_poison_memory_region = @cf_pc_poison CfImg_B.
Proof. vm_compute. reflexivity. Qed.
Lemma ctiB_unpoison_pc : SIGMA AS___asan_unpoison_memory_region = @cf_pc_unpoison CfImg_B.
Proof. vm_compute. reflexivity. Qed.
(* the poison / unpoison rows at TfibB: CfPoisonB102's, at the ARcf laws *)
Lemma ctiB_apoison : forall fy : YK11.FPState, @YGcfHp.apoison_realizes_cf fy rc CfImg_B CP BVB.tfibsegs TB.
Proof.
intros fy.
exact (CPB.preset_apoison_cf_B102 (fx := fy) (rc := rc) TB (YG0lawscf.AR_laws_ok_cf (cp := CP) BVB.tfibsegs TB)
  DLB.TfibB_syms).
Qed.
Lemma ctiB_aunpoison : forall fy : YK11.FPState, @YGcfHp.aunpoison_realizes_cf fy rc CfImg_B CP BVB.tfibsegs TB.
Proof.
intros fy.
exact (CPB.preset_aunpoison_cf_B102 (fx := fy) (rc := rc) TB (YG0lawscf.AR_laws_ok_cf (cp := CP) BVB.tfibsegs TB)
  DLB.TfibB_syms).
Qed.
(* __asan_memcpy at ARcf (fuzz_strdup's AI): PRowCpy's row at the code record's pc, the listing's by computation *)
Lemma ctiB_amcpy_cf : forall fy : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fy) SEGS TB
    (fun ly S Hp W mem md => YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md) OCpy (SIGMA AS___asan_memcpy).
Proof.
intros fy.
assert (E : SIGMA AS___asan_memcpy = pc_asan_memcpy (as_code TB)) by (vm_compute; reflexivity).
rewrite E.
exact (RCB.prow_asan_memcpy_xm_B (fx := fy) TB _ _
  (YGcallcf.AR_laws_x_cf (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)) DLB.TfibB_syms).
Qed.

(* ---- STAGE 1: the callee walks at the instance ---- *)
(* own (fuzz_malloc's OWN): OwnB_p102.own_holds_B *)
Lemma ctiB_own : forall fy : YK11.FPState,
  PRH_FnAlloc.town_specX (fx := fy) (rc := rc) (cp := CP) (PI := PIB) (RL := RLB) (L := B_prog_listing) (PA := PB)
    TB ARIB SKB.
Proof.
intros fy.
eapply (OWB.own_holds_B (fx := fy) (rc := rc) (SK := SKB) TB);
  first [ exact PLB.exvi_eh_palib | exact FAB.acc_pal_pst_ok_B | exact (ctiB_apoison fy) | exact ctiB_poison_pc ].
Qed.
(* fuzz_malloc (fuzz_strdup's FMALLOC): FuzzMallocB_p102_holds.fuzz_malloc_holds_B, its AMALLOC the cited row ctiB_amalloc *)
Lemma ctiB_fmalloc : forall fy : YK11.FPState,
  PRH_FnAlloc.tfuzz_malloc_specX (fx := fy) (rc := rc) (cp := CP) (PI := PIB) (RL := RLB) (L := B_prog_listing)
    (PA := PB) TB ARIB SKB.
Proof.
intros fy.
eapply (MLB.fuzz_malloc_holds_B (fx := fy) (rc := rc) (SK := SKB) TB);
  first [ exact PLB.exvi_eh_palib | exact FAB.acc_pal_pst_ok_B | exact (ctiB_amalloc fy)
        | exact (ctiB_own fy) | exact DLB.TfibB_syms ].
Qed.
(* fuzz_strdup (pj_string's STRDUP): FuzzStrdupB.fuzz_strdup_holds_B *)
Lemma ctiB_strdup : forall fy : YK11.FPState,
  PRH_FnAlloc.tfuzz_strdup_specX (fx := fy) (rc := rc) (cp := CP) (PI := PIB) (RL := RLB) (L := B_prog_listing)
    (PA := PB) TB ARIB SKB.
Proof.
intros fy.
eapply (SDB.fuzz_strdup_holds_B (fx := fy) (rc := rc) (SK := SKB) TB);
  first [ exact DLB.TfibB_syms | exact (ctiB_fmalloc fy) | exact (ctiB_amcpy_cf fy) | exact PLB.exvi_eh_palib ].
Qed.
(* PJSTR: pj_string_iface.tpj_string_B_preset_iface at CTX0 := iface_ctx0 *)
Lemma ctiB_pjstr : forall fxq : YK11.FPState,
  @PRH_FnPj.tpj_string_specX fxq rc CfImg_B CP PIB RLB B_prog_listing PB TB ARIB SKB CTXB.
Proof.
intros fxq.
exact (PJB.tpj_string_B_preset_iface (fx := fxq) (rc := rc) (ci := CfImg_B) (RL := RLB) (SK := SKB) (ctiB_ams fxq)
  (ctiB_strdup fxq) CTXB).
Qed.
(* FFREE: FuzzFreeB.fuzz_free_holds_B, its AFREE the cited free row ctiB_afree *)
Lemma ctiB_ffree : forall fxk : YK11.FPState,
  @PRH_FnAlloc.tfuzz_free_specX fxk rc CP PIB RLB B_prog_listing PB TB ARIB SKB.
Proof.
intros fxk.
eapply (FFB.fuzz_free_holds_B (fx := fxk) (rc := rc) (SK := SKB) TB);
  first [ exact (ctiB_afree fxk) | exact (ctiB_aunpoison fxk) | exact PLB.exvi_eh_palib
        | exact FAB.acc_pal_pst_ok_B | exact ctiB_unpoison_pc | exact DLB.TfibB_syms ].
Qed.

(* ---- STAGE 2: the cited walks of pj_free, pj_set, put, pj_write, parse_noting, tx_put, tx_string and tx_value at the
   instance; fuzz_realloc's AREAL_cf is ctiB_areal, so every lemma that cites ctiB_freal (GROW, PUT, and through them
   PJSET, PJW, PNOTING) uses that row, and ctiB_txput passes it as tx_put's AREAL. The recipes are
   lib/AU/Prog/Ent102DrvTopB2.v's / Ent102DrvTopB3.v's drv2_* / drv3_* (copied, not Required, so that those drivers can
   cite this corollary without a Require cycle), with fuzz_malloc's and fuzz_free's keep rows passed directly, as the walks take them on this head ---- *)
(* PJFREE: pj_free_iface.tpj_free_specX_B_preset_iface at CTX0 := iface_ctx0, DOC_D: XFF ctiB_ffree, XMS ctiB_ams *)
Lemma ctiB_pjfree : forall fxk : YK11.FPState,
  @PRH_FnPj.tpj_free_specX fxk rc CfImg_B CP PIB RLB B_prog_listing PB TB ARIB SKB CTXB PRH_Base.DOC_D.
Proof.
intros fxk.
exact (PFI.tpj_free_specX_B_preset_iface (fx := fxk) (rc := rc) (ci := CfImg_B) (RL := RLB) (SK := SKB) (ctiB_ffree fxk)
  (ctiB_ams fxk) CTXB PRH_Base.DOC_D).
Qed.
(* __asan_memcpy at iface_ARx (pjs_texts' memcpy row, put's H_amc, tx_put's AI): PRowCpy's row at the code record's
   pc, the listing's by computation, the laws ctiB_laws *)
Lemma ctiB_amcpy : forall fy : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fy) SEGS TB ARIB OCpy (SIGMA AS___asan_memcpy).
Proof.
intros fy.
assert (E : SIGMA AS___asan_memcpy = pc_asan_memcpy (as_code TB)) by (vm_compute; reflexivity).
rewrite E. change SEGS with BVB.tfibsegs.
exact (RCB.prow_asan_memcpy_xm_B (fx := fy) TB ARIB cf_head ctiB_laws DLB.TfibB_syms).
Qed.
(* fuzz_realloc (grow's HREALLOC, put's H_real): FuzzReallocB_p102.fuzz_realloc_holds_B' at iface_ARx, its AREAL_cf
   the cited realloc row ctiB_areal (the recipe of Ent102DrvTopB3.v drv3_fuzz_realloc_B) *)
Lemma ctiB_freal : forall fy : YK11.FPState,
  PRH_FnAlloc.tfuzz_realloc_specX (fx := fy) (rc := rc) (ci := CfImg_B) (cp := CP) (RL := RLB) (PI := PIB)
    (L := B_prog_listing) (PA := PB) TB ARIB SKB.
Proof.
intros fy.
eapply (RAB.fuzz_realloc_holds_B' (fx := fy) (rc := rc) (SK := SKB) TB);
  first [ exact (ctiB_own fy) | exact (ctiB_fmalloc fy) | exact (ctiB_aunpoison fy)
        | exact (ctiB_areal fy) | exact PLB.exvi_eh_palib | exact FAB.acc_pal_pst_ok_B
        | exact (CAB.errno_relro_preset_AU TB DLB.TfibB_syms) ].
Qed.
(* pj_get (pjs_texts' GET): PjGetB.pj_get_holds_B_K0 at iface_ARx *)
Lemma ctiB_get : forall fxq : YK11.FPState,
  PRH_FnPj.tpj_get_specX (fx := fxq) (rc := rc) (cp := CP) (PI := PIB) (RL := RLB) (L := B_prog_listing) (PA := PB)
    TB ARIB SKB.
Proof.
intros fxq.
exact (PGB.pj_get_holds_B_K0 (fx := fxq) (rc := rc) SKB TB ARIB ctiB_laws PLB.exvi_eh_palib (ctiB_strcmp fxq)).
Qed.
(* grow (pjs_texts' GROW, pj_parse's TGR): PwGrowBTop.grow_holds_B_inst at every context, HREALLOC ctiB_freal *)
Lemma ctiB_grow : forall (fxq : YK11.FPState) (CTX0 : list (list Z)),
  PRH_FnReader.tgrow_specX (fx := fxq) (rc := rc) (ci := CfImg_B) (cp := CP) (PI := PIB) (RL := RLB)
    (L := B_prog_listing) (PA := PB) TB ARIB SKB CTX0.
Proof. intros fxq CTX0. exact (GRB.grow_holds_B_inst (fx := fxq) (rc := rc) SKB (ctiB_freal fxq) CTX0). Qed.
(* PJSET: pj_set_iface.tpj_set_specX_B_preset_iface at CTX0 := iface_ctx0, dd := DOC_D; pjs_texts' six conjuncts *)
Lemma ctiB_pjset : forall fxq : YK11.FPState,
  @PRH_FnPj.tpj_set_specX fxq rc CfImg_B CP PIB RLB B_prog_listing PB TB ARIB SKB CTXB PRH_Base.DOC_D.
Proof.
intros fxq.
exact (PSI.tpj_set_specX_B_preset_iface (fx := fxq) (rc := rc) (ci := CfImg_B) (RL := RLB) (SK := SKB) CTXB
  PRH_Base.DOC_D (conj (ctiB_get fxq) (conj (ctiB_pjfree fxq) (conj (ctiB_grow fxq CTXB) (conj (ctiB_strdup fxq)
    (conj (ctiB_amcpy fxq) (ctiB_ams fxq))))))).
Qed.
(* put (pj_write's HPUT): PutB.put_holds_B, H_real ctiB_freal, H_amc ctiB_amcpy (Ent102DrvTopB3.v drv3_put_B) *)
Lemma ctiB_put : forall (fy : YK11.FPState) (CTX0 : list (list Z)),
  PRH_FnWriter.tput_specX (fx := fy) (rc := rc) (cp := CP) (PI := PIB) (RL := RLB) (L := B_prog_listing) (PA := PB)
    TB ARIB SKB CTX0.
Proof.
intros fy CTX0.
exact (PTB.put_holds_B (fx := fy) (rc := rc) (SK := SKB) (ctiB_freal fy) (ctiB_amcpy fy) CTX0).
Qed.
(* the class-0 frame-area row at plain ARcf (pj_parse's ASM0): FCm01xm.stack_malloc0_contract_xm *)
Lemma ctiB_asm0 : forall fy : YK11.FPState,
  YGcallMxmn.astack_malloc_realizes_xm (fx := fy) SEGS TB (YG0ncf.ARcf (rc := rc) (cp := CP) SEGS TB) 0.
Proof.
intros fy. change SEGS with BVB.tfibsegs.
exact (F01.stack_malloc0_contract_xm (fx := fy) TB (YG0ncf.ARcf (rc := rc) (cp := CP) BVB.tfibsegs TB)
  (FCifaceCf.fs_iface_ARcf (cp := CP) BVB.tfibsegs TB (YG0lawscf.AR_laws_ok_cf (cp := CP) BVB.tfibsegs TB))
  DLB.TfibB_syms).
Qed.
(* the class-0 frame-area row at iface_ARx (tx_string's ASM0): ctiB_asm0 kept across xs_placed_cf by
   YGcallMxmn.astack_malloc_realizes_xm_conj (Ent102DrvTopB3.v drv3_asmr0_B) *)
Lemma ctiB_asm0x : forall fy : YK11.FPState, YGcallMxmn.astack_malloc_realizes_xm (fx := fy) SEGS TB ARIB 0.
Proof.
intros fy.
exact (YGcallMxmn.astack_malloc_realizes_xm_conj (fx := fy) SEGS TB (YG0ncf.ARcf (rc := rc) (cp := CP) SEGS TB)
  (fun ly S => YG0ncf.xs_placed_cf (rc := rc) ly S) 0 YGcallScf.xs_placed_cf_set_fs (ctiB_asm0 fy)).
Qed.
(* write_value (pj_write's HWV): WriteValueB_Inst.write_value_holds_B at every depth (Ent102DrvTopB3.v
   drv3_write_value_B); it cites WriteValueB_Wit.v's image witnesses itself. Its callees: put ctiB_put, indent
   ctiB_indent, put_string ctiB_pstr *)
(* indent (write_value's INDENT): IndentB_Top.indent_holds_B, H_put ctiB_put (Ent102DrvTopB3.v drv3_indent_B) *)
Lemma ctiB_indent : forall fy : YK11.FPState,
  PRH_FnWriter.tindent_specX (fx := fy) (rc := rc) (cp := CP) (PI := PIB) (RL := RLB) (L := B_prog_listing) (PA := PB)
    TB ARIB SKB CTXB.
Proof. intros fy. exact (IDB.indent_holds_B (fx := fy) (rc := rc) (SK := SKB) (fun C => ctiB_put fy C) CTXB). Qed.
(* the snprintf row (put_string's): PSnpRowB.snprintf_row_B_inst at K := STK_RT_PRINTF (Ent102DrvTopB3.v
   drv3_snprintf_B); its cr snr_cr is PutStringB_SnpWit.psn_cr's body *)
Lemma ctiB_snprintf : forall fy : YK11.FPState,
  YGcallSnp.asnprintf_realizes_xrom (fx := fy) SEGS TB ARIB RLO RHI
    (YGcallSnpCk.FF_esc (@YC4aP.pa_lo rc B_prog_listing PB) YE22.A_GOT_CANARY) PRH_Base.STK_RT_PRINTF
    YE22.A_GOT_CANARY YE22.V_GOT_CANARY (@YC4aP.pa_lo rc B_prog_listing PB) (@YC4aP.pa_hi rc B_prog_listing PB)
    (PSW.psn_cr (rc := rc)) (SIGMA AS___wrap_snprintf).
Proof.
intros fy.
exact (SRB.snprintf_row_B_inst (rc := rc) PRH_Base.STK_RT_PRINTF ltac:(apply Z.leb_le; vm_compute; reflexivity) fy).
Qed.
(* put_string (write_value's PUTSTR): PutStringB_SnpWit.put_string_holds_B_owner at CTX0 := iface_ctx0: PUT ctiB_put,
   ASM0 ctiB_asm0x, AMCPY ctiB_amcpy, K := STK_RT_PRINTF, the snprintf row ctiB_snprintf (Ent102DrvTopB3.v
   drv3_put_string_B) *)
Lemma ctiB_pstr : forall fy : YK11.FPState,
  PRH_FnWriter.tput_string_specX (fx := fy) (rc := rc) (cp := CP) (PI := PIB) (RL := RLB) (L := B_prog_listing)
    (PA := PB) TB ARIB SKB CTXB.
Proof.
intros fy.
exact (PSW.put_string_holds_B_owner (rc := rc) (SK := SKB) CTXB (fun fz => ctiB_put fz CTXB) ctiB_asm0x ctiB_amcpy
  PRH_Base.STK_RT_PRINTF (Z.le_refl _) ctiB_snprintf fy).
Qed.
Lemma ctiB_wval : forall (fy : YK11.FPState) (n : nat),
  PRH_FnWriter.twrite_value_specX (fx := fy) (rc := rc) (cp := CP) (PI := PIB) (RL := RLB) (L := B_prog_listing)
    (PA := PB) TB ARIB SKB CTXB n.
Proof.
intros fy n.
exact (WVB.write_value_holds_B (fx := fy) (rc := rc) SKB CTXB (fun fz => ctiB_put fz CTXB) ctiB_pstr ctiB_indent n).
Qed.
(* PJW: PRW_pj_writeB_Inst.pj_write_holds_B_inst at CTX0 := iface_ctx0, n := DOC_D: HWV ctiB_wval, HPUT ctiB_put,
   HFREE ctiB_ffree; pjw_ARGCNT is the second conjunct of PresetRoomCounts.counts_of_room_pos_rl at the call's
   model-run position (Ent102DrvTopB3.v drv3_argcnt, inlined) *)
Lemma ctiB_pjw : forall fxk : YK11.FPState,
  @PRH_FnWriter.tpj_write_specX fxk rc CfImg_B CP PIB RLB B_prog_listing PB TB ARIB SKB CTXB PRH_Base.DOC_D.
Proof.
intros fxk.
refine (PWB.pj_write_holds_B_inst (fx := fxk) (rc := rc) SKB CTXB (ctiB_wval fxk) (fun fz => ctiB_put fz CTXB) ctiB_ffree
  PRH_Base.DOC_D _).
intros; hnf; intros.
lazymatch goal with |- YGcfRoomLive.ccnt24 ?S' <= _ =>
  match goal with Hp : PresetRoomPos.iface_room_pos _ _ _ _ _ _ S' |- _ =>
    exact (proj2 (PresetRoomCounts.counts_of_room_pos_rl _ _ _ _ _ _ _ Hp)) end end.
Qed.
(* ---- PNOTING: PN102BTop.tparse_noting_specX_TfibB (Ent102DrvTopB2.v drv2_parse_noting_B), its pj_parse text by
   pj_parse_top.pj_parse_holds_Bp ---- *)
(* parse_string (pj_parse's TPS): PSB_Inst.parse_string_holds_B_inst, FMALLOC ctiB_fmalloc, AF the cited free row *)
Lemma ctiB_pstring : forall (fy : YK11.FPState) (CTX CW : list (list Z)),
  PRH_FnReader.tparse_string_specX (fx := fy) (rc := rc) (ci := CfImg_B) (cp := CP) (RL := RLB) (PI := PIB)
    (L := B_prog_listing) (PA := PB) TB ARIB SKB CTX CW.
Proof.
intros fy CTX CW.
exact (PSS.parse_string_holds_B_inst (fx := fy) (rc := rc) SKB (ctiB_fmalloc fy) ctiB_afree
  CTX CW).
Qed.
(* literal (pj_parse's TLIT): literal_bridge.literal_holds at iface_ARx: LAWS ctiB_laws, PAL PALibB.exvi_eh_palib,
   ASTRLEN ctiB_strlen, ABCMP CrcBInstBcmp.cbi_bcmp *)
Lemma ctiB_lit : forall fy : YK11.FPState,
  PRH_FnReader.tliteral_specX (fx := fy) (rc := rc) (cp := CP) (PI := PIB) (RL := RLB) (L := B_prog_listing) (PA := PB)
    TB ARIB SKB.
Proof.
intros fy.
exact (LTB.literal_holds (fx := fy) (rc := rc) (HL := @cf_head CP) SKB TB ARIB ctiB_laws PLB.exvi_eh_palib
  (ctiB_strlen fy) (CBB.cbi_bcmp (fx := fy) (rc := rc))).
Qed.
(* pj_parse (parse_noting's HPJ): pj_parse_top.pj_parse_holds_Bp at every cursor set *)
Lemma ctiB_pjparse : forall (fy : YK11.FPState) (CW : list (list Z)),
  PRH_FnPj.tpj_parse_specX (fx := fy) (rc := rc) (ci := CfImg_B) (cp := CP) (PI := PIB) (RL := RLB)
    (L := B_prog_listing) (PA := PB) TB ARIB SKB CTXB CW.
Proof.
intros fy CW.
exact (PPT.pj_parse_holds_Bp (fx := fy) (rc := rc) (SK := SKB) ctiB_ams ctiB_grow ctiB_pstring
  ctiB_afree ctiB_aunpoison ctiB_lit ctiB_asm0 ctiB_amcpy_cf ctiB_fmalloc CTXB CW).
Qed.
(* check_reject_clean (parse_noting's HCRC): CrcBInstBcmp.check_reject_clean_holds_B_inst_bcmp, the image shadow
   AImgShadowVisCfB.tfib_img_shadow_vis_cf_B (Ent102DrvTopB2.v drv2_check_reject_clean_B) *)
Lemma ctiB_crc : forall fy : YK11.FPState,
  PRH_FnCheck.tcheck_reject_clean_specX (fx := fy) (rc := rc) (cp := CP) (PI := PIB) (RL := RLB) (L := B_prog_listing)
    (PA := PB) TB ARIB SKB.
Proof.
intros fy.
exact (CBB.check_reject_clean_holds_B_inst_bcmp (fx := fy) (rc := rc) SKB
  (ISV.tfib_img_shadow_vis_cf_B (rc := rc) (cp := CP) SEGS TB DLB.TfibB_syms)).
Qed.
(* PNOTING: PN102BTop.tparse_noting_specX_TfibB at CTX0 := iface_ctx0: HLIVE
   FuzzAllocAccInstB102.fuzz_alloc_live_holds_B_inst, HPJ ctiB_pjparse, HRO ctiB_ranout, HCRC ctiB_crc *)
Lemma ctiB_pnoting : forall fxk : YK11.FPState,
  @PRH_FnCheck.tparse_noting_specX fxk rc CfImg_B CP PIB RLB B_prog_listing PB TB ARIB SKB CTXB.
Proof.
intros fxk.
exact (PNB.tparse_noting_specX_TfibB (fx := fxk) (rc := rc) (ci := CfImg_B) (SK := SKB) CTXB
  (FAB.fuzz_alloc_live_holds_B_inst (fx := fxk) (rc := rc) (SK := SKB)) (ctiB_pjparse fxk)
  ctiB_ranout ctiB_crc).
Qed.
(* TXPUT: TxPut102B_Inst.tx_put_holds_B_inst at TfibB: TB YD2l.TfibB_syms, AREAL ctiB_areal (tp_AREAL is the keep _k
   row), AREALN ctiB_arealn (the NULL row tp_AREALN), AI ctiB_amcpy *)
Lemma ctiB_txput : forall fxk : YK11.FPState,
  @PRH_FnTx.ttx_put_specX fxk rc CfImg_B CP PIB RLB B_prog_listing PB TB ARIB SKB CTXB.
Proof.
intros fxk.
exact (TPI.tx_put_holds_B_inst (fx := fxk) (rc := rc) TB SKB CTXB DLB.TfibB_syms
  (ctiB_areal fxk) (ctiB_arealn fxk)
  (ctiB_amcpy fxk)).
Qed.
(* ---- TXVAL: BTxValue.tx_value_B_holds, its tx_string text by BTxString.tx_string_B_holds ---- *)
(* tx_string's FAL64: every live fake frame is 64-aligned at ARcf (YG0scf.frame_facts_cf's page-aligned fake stack and
   64-aligned frame offset; the proof of SameB_walk.v SMB_FR64) *)
Lemma ctiB_fal64 : forall ly S Hp (W : world SEGS) mem md cid pos, ARIB ly S Hp W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0.
Proof.
intros ly S Hp W mem md cid pos [(M & _) _] Hin.
destruct (YG0scf.frame_facts_cf TB ly S Hp _ cid pos M Hin) as (_ & _ & _ & _ & FA & _ & _ & Hoff & _).
unfold page_aligned in FA. apply Z.mod_divide in FA as [qF HqF]; [|lia].
apply Z.mod_divide in Hoff as [qO HqO]; [|lia].
unfold frame_addr. rewrite HqF, HqO. replace (qF * 4096 + qO * 64) with ((qF * 64 + qO) * 64) by ring.
apply Z_mod_mult.
Qed.
(* tx_string (tx_value's TXSTR): BTxString.tx_string_B_holds at TfibB and iface_ARx; its image facts by BTxStrWitB.v *)
Lemma ctiB_txstr : forall fxk : YK11.FPState,
  PRH_FnTx.ttx_string_specX (fx := fxk) (rc := rc) (cp := CP) (PI := PIB) (RL := RLB) (L := B_prog_listing) (PA := PB)
    TB ARIB SKB CTXB.
Proof.
intros fxk.
eapply (BTS.tx_string_B_holds (fx := fxk) (rc := rc) TB ARIB);
  first [ exact ctiB_laws | exact PLB.exvi_eh_palib | exact TSW.tsw_pal_stack_malloc0_TfibB
        | exact TSW.tsw_pal_uar_img_cf_TfibB | exact TSW.tsw_cf_img_ok_B | exact TSW.tsw_img_cf_box_B
        | exact (ctiB_asm0x fxk) | exact ctiB_ownlow | exact (YGcallScf.stack_malloc_x_any SEGS ARIB)
        | exact TSW.tsw_zs_aligned_TfibB | exact ctiB_imgvis | exact (ctiB_txput fxk)
        | exact TSW.tsw_pal_pst_static_TfibB | exact ctiB_asfx | exact ctiB_fflx | exact ctiB_sfx | exact ctiB_fflp
        | exact ctiB_fal64 | exact TSW.tsw_lit_img_TfibB | exact TSW.tsw_hex_img_TfibB ].
Qed.
(* TXVAL: BTxValue.tx_value_B_holds at TfibB and iface_ARx, n := DOC_D; its image facts by BTxValue.v's / BTxLine.v's
   TfibB witnesses *)
Lemma ctiB_txval : forall fxk : YK11.FPState,
  @PRH_FnTx.ttx_value_specX fxk rc CfImg_B CP PIB RLB B_prog_listing PB TB ARIB SKB CTXB PRH_Base.DOC_D.
Proof.
intros fxk.
eapply (BTV.tx_value_B_holds (fx := fxk) (rc := rc) TB ARIB);
  first [ exact ctiB_laws | exact PLB.exvi_eh_palib | exact BTV.tv_jt_own_TfibB | exact (ctiB_strlen fxk)
        | exact (ctiB_txput fxk) | exact (ctiB_txstr fxk) | exact BTL.tl_zs_aligned_TfibB | exact ctiB_imgvis
        | exact BTL.tl_img_cf_box_B | exact BTL.tl_lit_img_TfibB | exact BTV.tv_lit_img_TfibB ].
Qed.
(* round_trip_text's newline literal (Rtt102TB.RTT_LITNL_B, "\n", length 1) is a kept image literal at TfibB, by
   computation (the method of BTxLine.v's tl_lit_img_TfibB): inside the image's margins, read-only, not runtime-owned,
   not errno, and its granule's const-shadow cell in TfibB's as_const is 2 *)
#[local] Notation LITNL := (@RTB.RTT_LITNL_B rc).
Lemma ctiB_litnl : @kept_img rc B_prog_listing PB TB LITNL 1.
Proof.
unfold kept_img.
assert (HB : @pa_lo _ _ PB + 64 <= LITNL /\ LITNL + 1 + 64 <= @pa_hi _ _ PB)
  by (vm_compute; split; intro H; discriminate H).
destruct HB as [HB1 HB2].
split; [lia|]. split; [lia|]. intros a Ha.
assert (Ea : a = LITNL) by lia. subst a.
split; [|split; [|split]].
- red.
  assert (Hb : existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? LITNL)
                 && (LITNL <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) SEGS
               || ((RLO <=? LITNL) && (LITNL <? RHI)) = true) by (vm_compute; reflexivity).
  apply orb_prop in Hb as [Hb|Hb].
  + left. apply existsb_exists in Hb as (s & Hs & Hb). apply andb_prop in Hb as [Hb H2].
    apply andb_prop in Hb as [H0 H1]. apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    exists s. split; [exact Hs|]. split; [exact H0 | lia].
  + right. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
- intros HE. apply Exists_exists in HE as (r & Hin & Hr). unfold in_zr in Hr.
  assert (Hf : existsb (fun r => (fst r <=? LITNL) && (LITNL <? fst r + snd r)) (as_owned_static TB) = false)
    by (vm_compute; reflexivity).
  assert (Ht : existsb (fun r => (fst r <=? LITNL) && (LITNL <? fst r + snd r)) (as_owned_static TB) = true).
  { apply existsb_exists. exists r. split; [exact Hin|].
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  congruence.
- assert (Herr : (as_errno TB <=? LITNL) && (LITNL <? as_errno TB + 4) = false) by (vm_compute; reflexivity).
  intros [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. rewrite H1, H2 in Herr. discriminate Herr.
- right. exists 2. split; [|right; split; vm_compute; reflexivity].
  intros ly. cbn [as_const DLB.TfibB]. unfold FMB.Tfib_const.
  apply in_or_app. right. apply in_or_app. right.
  vm_compute. repeat (first [left; reflexivity | right]).
Qed.
(* THE PIN of the literal's address: ctiB_litnl computes on the value RTT_LITNL_B has (lib/B/Prog/Rtt102TB.v:105,
   B_prog_val (A_OBJ 2) + 70112). This check states that value, 0x211e0, the image B' (asan-ubsan, pin
   d663f82d7f48) address of `.str.19 "\n"` in .rodata (B_prog_val (A_OBJ 2) is 0x10000, lib/B/PAImg_prog.v:193), so a
   definition of RTT_LITNL_B with another value fails here *)
Lemma ctiB_litnl_pin : @RTB.RTT_LITNL_B rc = 0x211e0.
Proof. vm_compute. reflexivity. Qed.
(* RTT: Rtt102InstB.rtt_iface_B at CTX0 := iface_ctx0 *)
Lemma ctiB_rtt : forall fxk : YK11.FPState,
  @PRH_FnCheck.tround_trip_text_specX fxk rc CfImg_B CP PIB RLB B_prog_listing PB TB ARIB SKB CTXB.
Proof.
intros fxk.
exact (@RIB.rtt_iface_B fxk rc CTXB ctiB_same ctiB_pjfree ctiB_afree ctiB_ffree
  ctiB_pnoting ctiB_litnl ctiB_txput ctiB_txval ctiB_pjw).
Qed.

(* ---- THE INSTANCE: the body of PresetD2pBPf.v's txt_check_round_trip_B at Ent102DrvTopB.v's binding ---- *)
Corollary crt102_topB_TfibB_inst : forall fy : YK11.FPState,
  @PRH_FnCheck.tcheck_round_trip_specX fy rc CfImg_B CP PIB RLB B_prog_listing PB TB ARIB SKB CTXB
    EIB.ia_mod_at EIB.ia_stamp.
Proof.
intros fy. rewrite <- ctiB_mod_at, <- ctiB_stamp.
apply @CTB.crt102_topB_TfibB with (fx := fy) (rc := rc) (SK := SKB) (RL := RLB) (ARx := ARIB)
  (LAWS := ctiB_laws) (ASM3 := ctiB_asm3 fy) (OWNLOW := ctiB_ownlow) (AMS := ctiB_ams fy) (CTX0 := CTXB)
  (RTT := ctiB_rtt) (ASFX := ctiB_asfx) (FFLX := ctiB_fflx) (SFX := ctiB_sfx) (FFLP := ctiB_fflp) (SETSH := ctiB_setsh)
  (PJFREE := ctiB_pjfree) (IMGVIS := ctiB_imgvis) (PJSTR := ctiB_pjstr) (PJSET := ctiB_pjset) (RANOUT := ctiB_ranout)
  (STRLEN := ctiB_strlen) (STRCMP := ctiB_strcmp) (SAME := ctiB_same) (FFREE := ctiB_ffree) (PJW := ctiB_pjw)
  (PNOTING := ctiB_pnoting).
Qed.
End i.

(* the allocator rows' signatures: is the float state fx an argument of each? (the malloc and free rows cited here) *)
About YGcfMallocComposeKeep.amalloc_realizes_cf_keep.
About YGcfMallocComposeKeep.afree_realizes_cf_rh_keep.
About CMK.amalloc_realizes_cf_keep_closed_B.
About CFK.afree_realizes_cf_rh_keep_B.
Set Printing Implicit.
Unset Printing Notations.
Check @crt102_topB_TfibB_inst.
About crt102_topB_TfibB_inst.
Set Printing Notations.
Unset Printing Implicit.
Print Assumptions crt102_topB_TfibB_inst.
