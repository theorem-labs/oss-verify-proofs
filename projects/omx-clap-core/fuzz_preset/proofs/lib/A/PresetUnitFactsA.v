(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyUnitFactsA.v (commit eb934de95d13, blob c3c5e5be00b3) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them); the two dep_keep fields take the layer's depot_fits premise. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YP0m YP0e YP09 YP02 YP0l YP0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP06 YP03 YP04 YP0g YP01 YP0i YP0j YN3v YI04 YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YM05 YK0s YO0d YA0p YG04 YG03 YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0q YG06 YG07 YGcfNames YK07 YO0f YK00 YK0g YK0c YK0d YK0e YK0f YK09 YA01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0c YA0e YA0d YA02 YA0j YG0r YG0b YD1h YI00 YE00 YE01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGImgA ADIfaceA AFl0 AD2l CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoApart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ErrnoApartpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGImgSA AB13 AB12 AB1h AB01 AD1g AD2i AE2k AB03 AB1t AFff.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AGif4.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DMiface CLdepot.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AGis DGgi AFfl AB1w AGjm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFiacf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetImg_hoom PresetImg_herr PresetImg_errnoimg PresetImg_errnoseg PresetImg_errnonst PresetImg_errnoimgs PresetImg_errnoword PresetImg_hshb PresetImg_hdzo PresetImg_depfp PresetImg_depkeep PresetImg_instok PresetImg_instcells PresetImgRowsA PresetImg_errbapart PresetImg_oomowned PresetImg_oomconst PresetImg_fqconst PresetImg_sbconst PresetImg_constapart PresetImg_qapart PresetImg_fvzones PresetImg_vis PresetImg_zone3 PresetImg_relro PresetImg_su_tool PresetImg_su_printf PresetImg_su_syslog PresetImg_su_errb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetImg_hdzx PresetImg_hcw PresetImg_dhash CfInstImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0p.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
Open Scope Z_scope.

Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Record PresetUnitFactsA (B : asyms) : Prop := MkPresetUnitFactsA {

  uf_TS : @im_syms AImg_A B;

  uf_HTSD : as_tsd B = @im_tsd AImg_A;

  uf_HOOM : as_oom_byte B = @im_oom AImg_A;

  uf_HERR : as_errno B = @im_errno AImg_A;

  uf_IMG_COVER : forall ly S md, ALedger_cf tfibsegs ly S md -> img_cover ly;

  uf_ErrnoImgCf : errno_in_img (IM := AImg_A) /\ errno_unhidden (IM := AImg_A) /\ errno_apart_dzone_ag (IM := AImg_A) (AG := AGImg_A) /\ errno_apart_shadow_ag (IM := AImg_A) (AG := AGImg_A) /\ errno_apart_inst_ag (IM := AImg_A) (AG := AGImg_A) /\ errno_apart_dzone_d (IM := AImg_A) (DI := DImg_A) /\ errno_apart_izone (IM := AImg_A) (DI := DImg_A) /\ errno_apart_zone3_d (IM := AImg_A) (DI := DImg_A) /\ errno_apart_inst_d (IM := AImg_A) (DI := DImg_A);

  uf_errno_seg_t : forall a, as_errno B <= a < as_errno B + 4 -> seg_rom (@im_segs AImg_A) (Z_to_bv 64 a) <> None;

  uf_errno_nstatic_t : forall a, as_errno TfibB <= a < as_errno TfibB + 4 -> ~ Exists (in_zr a) (as_owned_static TfibB);

  uf_errno_apart_dzone_s : forall ly a, layout_ok ly -> im_img_cover ly -> ims_dzone ly a -> ~ (as_errno B <= a < as_errno B + 4);

  uf_errno_apart_shadow_s : forall a, ImgBaseAGS.SHBv <= a -> ~ (as_errno B <= a < as_errno B + 4);

  uf_errno_apart_zone3_s : forall x sz a, ims_zone3 x sz -> x <= a < x + sz -> ~ (as_errno B <= a < as_errno B + 4);

  uf_errno_word_cf : 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64;

  uf_HSHB : @ImgBaseAG.ag_shadow AImg_A AGImg_A = SHADOW_OFF;

  uf_HDZO : forall ly' a, @ImgBaseAG.ag_dzone AImg_A AGImgA.AGImg_A ly' a -> Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize);

  uf_HDZX : forall ly' a, layout_ok ly' -> @im_img_cover AImg_A ly' ->
    @ImgBaseAG.ag_dzone AImg_A AGImgA.AGImg_A ly' a ->
    ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
    ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2);

  uf_HCW : forall ly' c j cl', layout_ok ly' -> @im_img_cover AImg_A ly' -> ly_tsd ly' = as_tsd B ->
    In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
    ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j);

  uf_dhash_img : forall t : list Z, as_dhash TfibB t = YF0p.tfib_dhash t;

  uf_dep_fp_img_ag : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> CLdepot.depot_footprint B ly a -> ag_dzone ly a;

  uf_dep_fp_img_dg : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> CLdepot.depot_footprint B ly a -> dg_dzone ly a;

  uf_dep_keep_img_ag : forall ly S (W : world (@im_segs AImg_A)) (mem0 mem : word -> option byte), layout_ok ly -> @im_img_cover AImg_A ly -> ly_tsd ly = as_tsd B -> depot_fits (as_universe B) (st_depot S) -> Forall (cell_holds B ly (aview (@im_segs AImg_A) (w_H W) mem0)) (as_const B ly) -> CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_A) (w_H W) mem0) -> (forall x : word, ImgBaseAG.ag_dzone ly (bv_unsigned x) \/ ImgBaseAG.ag_czone ly (bv_unsigned x) -> mem x = mem0 x) -> Forall (cell_holds B ly (aview (@im_segs AImg_A) (w_H W) mem)) (as_const B ly) /\ CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_A) (w_H W) mem);

  uf_dep_keep_img_dg : forall ly S (W : world (@im_segs AImg_A)) (mem0 mem : word -> option byte), layout_ok ly -> @im_img_cover AImg_A ly -> ly_tsd ly = as_tsd B -> depot_fits (as_universe B) (st_depot S) -> Forall (cell_holds B ly (aview (@im_segs AImg_A) (w_H W) mem0)) (as_const B ly) -> CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_A) (w_H W) mem0) -> (forall x : word, ImgBaseDG.dg_dzone ly (bv_unsigned x) \/ (ImgBaseDG.dg_czone ly (bv_unsigned x) /\ ~ ImgBaseDG.dg_izone (bv_unsigned x)) -> mem x = mem0 x) -> Forall (cell_holds B ly (aview (@im_segs AImg_A) (w_H W) mem)) (as_const B ly) /\ CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_A) (w_H W) mem);

  uf_universe_ok : universe_ok (as_universe B);

  uf_ag_inst_ok : @ImgBaseAG.ag_inst_ok AImg_A AGImgA.AGImg_A (as_inst B);

  uf_dg_inst_ok : ImgBaseDG.dg_inst_ok (DImg := ADIfaceA.DImg_A) (as_inst B);

  uf_INST_CELLS_t : forall ly (H : word -> bool) (mem : word -> option byte), layout_ok ly -> ly_tsd ly = as_tsd B -> Forall (cell_holds B ly (aview im_segs H mem)) (as_const B ly) -> val_mem im_segs (mrestrict H mem) (as_inst B + o_space) 8 (ly_space ly) /\ val_mem im_segs (mrestrict H mem) (as_inst B + 0xe20) 8 0x10000000000 /\ val_mem im_segs (mrestrict H mem) (as_inst B + 0xe28) 8 0x108000010 /\ val_mem im_segs (mrestrict H mem) (as_inst B + o_sec) 8 4096 /\ val_mem im_segs (mrestrict H mem) (as_inst B + o_sec_chunks) 8 (ly_Q ly) /\ val_mem im_segs (mrestrict H mem) (as_inst B + 80) 8 (ly_Q ly) /\ val_mem im_segs (mrestrict H mem) (as_inst B + 88) 8 kPtrArrayResv /\ val_mem im_segs (mrestrict H mem) (as_inst B + o_sec_mutex + 1) 3 0;

  uf_errb_obj_owned_t : forall a, @cf_errbuf_obj CfImg_A <= a < @cf_errbuf_obj CfImg_A + 56 -> Exists (in_zr a) (as_owned_static B);

  uf_ERRB_APART : forall a, @cf_errbuf_obj CfImg_A <= a < @cf_errbuf_obj CfImg_A + 56 -> ~ dg_izone a /\ (forall ly, ((layout_ok ly /\ ly_tsd ly = as_tsd TfibB /\ Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static TfibB ++ as_zero_shadow TfibB)) /\ im_img_cover ly /\ asyms_ok TfibB) -> ~ dg_dzone ly a);

  uf_oom_owned_img : ~ (as_inst B <= as_oom_byte B < as_inst B + 3632) /\ ~ (as_depot B <= as_oom_byte B < as_depot B + (4 * 2 ^ 20 + 32)) /\ ~ (as_store B <= as_oom_byte B < as_store B + 32) /\ ~ (as_ialloc_lo B <= as_oom_byte B < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= as_oom_byte B < as_ialloc_flag B + 2);

  uf_oom_const_img : forall ly c k, (layout_ok ly /\ ly_tsd ly = as_tsd B /\ Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B)) -> In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> Exists (in_zr (aeval B ly (c_at c) + k)) (as_owned_static B) -> aeval B ly (c_at c) + k <> as_oom_byte B;

  uf_FQ_CONST : forall ly, (exists e, In (ACell e 8 (AV (ANum kQuarantineMax))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_max) /\ (exists e, In (ACell e 8 (AV (ANum kQuarantineCacheMax))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_maxcache) /\ (exists e, In (ACell e 8 (AV (ANum kQuarantineMin))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_min) /\ (exists e, In (ACell e 2 (AV (ANum 0))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_cmutex + 2);

  uf_SB_CONST : forall ly, In (ACell (AInst o_space) 8 (AV (ASp 0))) (@im_const AImg_A ly);

  uf_CONST_APART : forall ly c, (layout_ok ly /\ ly_tsd ly = as_tsd B /\ Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B)) -> In c (@im_const AImg_A ly) -> (aeval B ly (c_at c) = as_inst B + o_q_cmutex + 2 /\ c_w c = 2%nat /\ c_val c = AV (ANum 0)) \/ (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> ~ DMiface.qhdr (as_inst B) ly (aeval B ly (c_at c) + k) /\ ~ (ly_prim ly <= aeval B ly (c_at c) + k < ly_prim ly + kPrimResvSize));

  uf_IMG_QAPART : forall a, ((as_inst B + o_quar + 152 <= a < as_inst B + o_quar + 156) \/ (as_inst B + o_quar + 160 <= a < as_inst B + o_quar + 192)) -> ~ (as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32) /\ ~ (as_store B <= a < as_store B + 32) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2);

  uf_FV_IAL : forall (W : world im_segs) (m : word -> option byte), @dg_ial_post AImg_A DImg_A W m <-> (let m' := mrestrict (w_H W) m in val_mem im_segs m' (as_ialloc_flag B) 1 1 /\ val_mem im_segs m' (as_ialloc_flag B + 1) 1 0 /\ val_mem im_segs m' (as_ialloc_w B) 8 4096 /\ val_mem im_segs m' (as_ialloc_w B + 8) 8 (as_ialloc_w B + 16) /\ (forall a, as_ialloc_lo B <= a < as_ialloc_w B \/ as_ialloc_w B + 16 <= a < as_ialloc_hi B -> mbyte im_segs m' a = Some (Z_to_bv 8 0)));

  uf_FV_ZONE3 : forall ly x sz, @im_img_cover AImg_A ly -> 0 <= sz -> in_app x sz -> zdisjoint (x, sz) (ly_img ly) -> @dg_zone3 AImg_A DImg_A x sz;

  uf_DZONE_OWNED : forall ly a, @dg_dzone AImg_A DImg_A ly a -> Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize);

  uf_IZONE_OWNED : forall a, @dg_izone AImg_A DImg_A a -> (as_ialloc_lo B <= a < as_ialloc_hi B) \/ Exists (in_zr a) (as_owned_static B);

  uf_COMB_VIS : forall (H : word -> bool) (mem : word -> option byte) a, as_inst B + o_comb_stats <= a < as_inst B + o_comb_stats + 40 -> aview im_segs H mem a <> None;

  uf_ERRNO_VIS : forall (H : word -> bool) (mem : word -> option byte) a, as_errno B <= a < as_errno B + 4 -> aview im_segs H mem a <> None;

  uf_DEP_UNHID : forall (W : world im_segs) a, (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (as_store B <= a < as_store B + 64) -> w_H W (Z_to_bv 64 a) = false;

  uf_ZONE3 : forall ly x sz, @im_img_cover AImg_A ly -> 0 <= sz -> in_app x sz -> zdisjoint (x, sz) (ly_img ly) -> ims_zone3 (AImgS := AImgS_A) x sz;

  uf_CONST_KEEP_S : forall ly (H : word -> bool) (mem0 mem : word -> option byte), layout_ok ly -> @im_img_cover AImg_A ly -> ly_tsd ly = as_tsd B -> Forall (cell_holds B ly (aview (@im_segs AImg_A) H mem0)) (as_const B ly) -> (forall x : word, ims_dzone (AImgS := AImgS_A) ly (bv_unsigned x) \/ CZS (IM := AImg_A) (IMS := AImgS_A) ly (as_inst B) (bv_unsigned x) -> mem x = mem0 x) -> (forall k, 1 <= k < 4 -> aview (@im_segs AImg_A) H mem (as_inst B + o_sec_mutex + k) = Some 0) -> Forall (cell_holds B ly (aview (@im_segs AImg_A) H mem)) (as_const B ly);

  uf_CONST_NOT_JUNK : forall ly (regs0 : bvmap 5 word) n c k, layout_ok ly -> @im_img_cover AImg_A ly -> ly_tsd ly = as_tsd B -> bv_unsigned (getr regs0 11) = as_inst B -> 64513 <= n < @cf_malloc_max CfParams_preset -> In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> ~ ((ly_T ly + 2768 <= aeval B ly (c_at c) + k < ly_T ly + 2824) \/ (ly_T ly + 2872 <= aeval B ly (c_at c) + k < ly_T ly + 2888) \/ (ly_T ly + 2904 <= aeval B ly (c_at c) + k < ly_T ly + 2912) \/ (as_inst B + o_sec_sorted <= aeval B ly (c_at c) + k < as_inst B + o_sec_sorted + 1) \/ (as_inst B + o_sec_stats <= aeval B ly (c_at c) + k < as_inst B + o_sec_stats + 32) \/ (ImgBaseAGS.BSLv regs0 n <= aeval B ly (c_at c) + k < ImgBaseAGS.BSLv regs0 n + 8) \/ (as_inst B + o_comb_stats <= aeval B ly (c_at c) + k < as_inst B + o_comb_stats + 40) \/ aeval B ly (c_at c) + k = as_oom_byte B);

  uf_AREAS_DISJ : pairwise zdisjoint (asyms_areas B);

  uf_IMG_SAPART : forall a, ((as_inst B + 680 <= a < as_inst B + 684) \/ (as_inst B + 120 <= a < as_inst B + 129) \/ (as_inst B + 144 <= a < as_inst B + 160) \/ (as_inst B + 704 <= a < as_inst B + 720)) -> ~ (as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32) /\ ~ (as_store B <= a < as_store B + 32) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2);

  uf_IMG_JUNK : forall ly r0, layout_ok ly -> In r0 (as_junk B ly) -> forall j, 0 <= j < snd r0 -> exists sg, In sg (@im_segs AImg_A) /\ Z.of_N (seg_base sg) <= aeval B ly (fst r0) + j < Z.of_N (seg_base sg) + Z.of_N (seg_size sg);

  uf_ERRB_SEP : (forall B, @im_syms AImg_A B -> forall a, @cf_errbuf_obj CfImg_A <= a < @cf_errbuf_obj CfImg_A + 56 -> ~ (as_inst B <= a < as_inst B + 3632)) /\
    forall ly a, layout_ok ly -> @im_img_cover AImg_A ly -> ly_tsd ly = as_tsd B -> @cf_errbuf_obj CfImg_A <= a < @cf_errbuf_obj CfImg_A + 56 ->
    a <> as_oom_byte B /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ ims_dzone ly a /\ ~ ag_dzone ly a;

  uf_EXH_OFF : @cf_exh_off CfImg_A = 68;

  uf_RELRO_silent : val_mem tfibsegs (fun _ => None) PresetImg_relro.C_SILENT_A 8 1;

  uf_su_tool : (forall h ch, HS_tfib h = Some ch -> kn_read tfibsegs ch (ELit 0) PresetImg_su_tool.RA_TOOL_NAME_CELL 8 = Some (ELit PresetImg_su_tool.RA_TOOL_NAME_STR)) /\ kn_read tfibsegs JS_tfib_band (ELit 0) PresetImg_su_tool.RA_TOOL_NAME_CELL 8 = Some (ELit PresetImg_su_tool.RA_TOOL_NAME_STR) /\ (forall k, (k < 17)%nat -> seg_rom tfibsegs (Z_to_bv 64 (PresetImg_su_tool.RA_TOOL_NAME_STR + Z.of_nat k)) = Some (Z_to_bv 8 (nth k PresetImg_su_tool.asan_tool_name 0)));

  uf_su_printf : (forall s, In s AB01.HS_tfib_list -> In (KWord {| a_base := ELit 0; a_off := PresetImg_su_printf.presetA_printf_cb_cell |} 8 (ELit PresetImg_su_printf.presetA_printf_cb_fn)) (s_know (a_ss s))) /\ In (KWord {| a_base := ELit 0; a_off := PresetImg_su_printf.presetA_printf_cb_cell |} 8 (ELit PresetImg_su_printf.presetA_printf_cb_fn)) (s_know (a_ss AB03.JS_tfib_band));

  uf_su_syslog : forall (ly : alayout), In (z8 (ANum PresetImg_su_syslog.preseta_log_to_syslog_addr) 0) (@im_const AImg_A ly);

  uf_su_errb_obj_zero : ltac:(let t := type of (@PresetImg_su_errb.errb_obj_zero_start) in exact t);

  uf_su_exh_bytes_zero : ltac:(let t := type of (@PresetImg_su_errb.exh_bytes_zero_start) in exact t)
}.

Theorem preset_unit_facts_A : forall B, TfibSyms B -> PresetUnitFactsA B.
Proof.
intros B TS.
exact {|
  uf_TS := TS;
  uf_HTSD := AF0m.ts_tsd B TS;
  uf_HOOM := PresetImg_hoom.hoom_A B TS;
  uf_HERR := PresetImg_herr.herr_A B TS;
  uf_IMG_COVER := AFiacf.img_cover_of_ledger_cf;
  uf_ErrnoImgCf := PresetImg_errnoimg.errno_img_cf_A;
  uf_errno_seg_t := PresetImg_errnoseg.errno_seg_A B TS;
  uf_errno_nstatic_t := PresetImg_errnonst.errno_nstatic_A;
  uf_errno_apart_dzone_s := fun ly a => PresetImg_errnoimgs.errno_apart_dzone_s_A B ly a TS;
  uf_errno_apart_shadow_s := fun a => PresetImg_errnoimgs.errno_apart_shadow_s_A B a TS;
  uf_errno_apart_zone3_s := fun x sz a => PresetImg_errnoimgs.errno_apart_zone3_s_A B x sz a TS;
  uf_errno_word_cf := PresetImg_errnoword.errno_word_cf_A B TS;
  uf_HSHB := PresetImg_hshb.HSHB_A;
  uf_HDZO := PresetImg_hdzo.hdzo_A B TS;
  uf_HDZX := PresetImg_hdzx.hdzx_A B TS;
  uf_HCW := PresetImg_hcw.hcw_A B TS;
  uf_dhash_img := PresetImg_dhash.dhash_img_A;
  uf_dep_fp_img_ag := PresetImg_depfp.dep_fp_a_A B TS;
  uf_dep_fp_img_dg := PresetImg_depfp.dep_fp_d_A B TS;
  uf_dep_keep_img_ag := PresetImg_depkeep.dep_keep_a_A B TS;
  uf_dep_keep_img_dg := PresetImg_depkeep.dep_keep_d_A B TS;
  uf_universe_ok := AF0m.ts_universe B TS;
  uf_ag_inst_ok := PresetImg_instok.inst_ag_A B TS;
  uf_dg_inst_ok := PresetImg_instok.fm_inst_ok_A B TS;
  uf_INST_CELLS_t := PresetImg_instcells.inst_cells_A B TS;
  uf_errb_obj_owned_t := PresetImgRowsA.errb_obj_owned_A B TS;
  uf_ERRB_APART := PresetImg_errbapart.ERRB_APART_A;
  uf_oom_owned_img := PresetImg_oomowned.oom_owned_img_A B TS;
  uf_oom_const_img := PresetImg_oomconst.oom_const_img_A B TS;
  uf_FQ_CONST := PresetImg_fqconst.FQ_CONST_A B TS;
  uf_SB_CONST := PresetImg_sbconst.SB_CONST_A;
  uf_CONST_APART := fun ly c => PresetImg_constapart.CONST_APART_A B ly c TS;
  uf_IMG_QAPART := PresetImg_qapart.IMG_QAPART_A B TS;
  uf_FV_IAL := PresetImg_fvzones.fv_ial_img B TS;
  uf_FV_ZONE3 := PresetImg_fvzones.fv_zone3_img;
  uf_DZONE_OWNED := PresetImg_fvzones.dzone_owned_img B TS;
  uf_IZONE_OWNED := PresetImg_fvzones.izone_owned_img B TS;
  uf_COMB_VIS := PresetImg_vis.comb_vis_A B TS;
  uf_ERRNO_VIS := PresetImg_vis.errno_vis_A B TS;
  uf_DEP_UNHID := PresetImg_vis.dep_unhid_A B TS;
  uf_ZONE3 := PresetImg_zone3.zone3_A;
  uf_CONST_KEEP_S := PresetImg_zone3.const_keep_s_A B TS;
  uf_CONST_NOT_JUNK := PresetImg_zone3.const_not_junk_A (cp := CfParams_preset) B TS;
  uf_AREAS_DISJ := PresetImg_zone3.areas_disj_A B TS;
  uf_IMG_SAPART := PresetImgRowsA.img_sapart_A B TS;
  uf_IMG_JUNK := fun ly r0 => PresetImgRowsA.img_junk_A B ly r0 TS;
  uf_ERRB_SEP := conj CfInstImgA.ERRB_QAPART_A (fun ly a LY IC HT Ha => proj2 (PresetImgRowsA.errb_sep_A B TS ly a LY IC HT Ha));
  uf_EXH_OFF := PresetImgRowsA.exh_off_A;
  uf_RELRO_silent := PresetImg_relro.silent_img_A;
  uf_su_tool := PresetImg_su_tool.su_tool_A;
  uf_su_printf := PresetImg_su_printf.presetA_su_printf;
  uf_su_syslog := fun ly => PresetImg_su_syslog.su_syslog_A B ly TS;
  uf_su_errb_obj_zero := @PresetImg_su_errb.errb_obj_zero_start;
  uf_su_exh_bytes_zero := @PresetImg_su_errb.exh_bytes_zero_start
|}.
Qed.

End u.
