(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyUnitFactsB.v (commit 4d286b2e618d, file sha256 107ffaa7aff0) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets and list indices by the same stage map), 0 list indices re-picked, and 0 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, for a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply): reply's UNIT FACTS at
   image B (fuzz_reply.asan-ubsan, pin 10ffb5f9202a).
   rule 24: no function proved (kind: statement text; the unit-hypothesis rows of the cf layer, wired from their proved
   row lemmas into one record).

   PresetUnitFactsB B bundles, as fields uf_<row name>, every image / start-up row of the layer's unit-hypothesis table
   (the internal file CF-UNIT-HYPS.md Table 1 and Table 4) that is proved at this image, each field's statement the row lemma's
   own statement (the layer text at reply's instances AImg_cgif, AGImg_cgif, AImgS_cgif, DImg_cgif, CfImg_B).
   preset_unit_facts_B gives the record for every B with the image's symbol facts (TfibSyms B), each field closed by
   `exact` from its row lemma (lib/B/ReplyImg_*.v and lib/B/PresetImgRowsB.v at lane W's head 6f1cb063e69).  The record
   holds ONLY proved rows; a row that is not proved at this image is in the gap list below, never a field.
   Notes on single fields:
   - uf_HTSD (`as_tsd B = im_tsd`) and uf_universe_ok (`universe_ok (as_universe B)`, the tree's universe_ok) are
     TfibSyms fields (ts_tsd, ts_universe of B/YF0m.v).
   - uf_errno_nstatic_t and uf_ERRB_APART are the row lemmas' statements at TfibB (the unit's one symbol record); ERRB_APART
     carries the layer's LGUARD shape ly_img_ok B ly /\ im_img_cover ly /\ asyms_ok B with ly_img_ok unfolded.
   - uf_su_errb_obj_zero / uf_su_exh_bytes_zero are the start-up rows' own statements (the row file's start-run Section
     context generalized); their type is the row lemma's, taken by `type of`.
   - Tfib_const_qmax is FQ_CONST's first conjunct (one name, FQ_CONST).
   OPEN ROWS (no field here; none is a premise of this record):
   - IOK_ok (`forall i, IOK i -> i = as_inst B`): a unit CHOICE, not an image fact; lane W's instance states it with
     IOK := (fun i => i = as_inst B).
   OBSOLETE (no field, no gap): NOROM (WalkB1's drain header ROM row): its use, the drain header's ROM bytes, was removed
   by the dmem_q narrowing and WalkB1's HDRW / HPH deletion.  HIOK: replaced by IOK_ok + ag_inst_ok in the table. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YP0m YP0e YP09 YP02 YP0l YP0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP06 YP03 YP04 YP0g YP01 YP0i YP0j YN3v YI04 YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YM05 YK0s YO0d YA0p YG04 YG06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG07 YG03 YG0q YGcfNames YO0f YK00 YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0e YA0d YA02 YA0j YG0r YG0b YD1h YI00 YE00 YK07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif0cgif DGif0cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFl0 YD2l. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoApart. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import ErrnoApartcgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAGS. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif4cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB13 YB12 YB1h YB01 YD1g YD2i YE01 YE2k YB03 YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AGif4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DMiface. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGis DGgi. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot YFfl YFi5 YFff. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGjm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YFiacf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetImg_hoom PresetImg_herr PresetImg_errnoimg PresetImg_errnoseg PresetImg_errnonst PresetImg_errnoimgs ErrnoWordB PresetImg_hshb PresetImg_hdzo PresetImg_depfp PresetImg_depkeep PresetImg_instok PresetImg_instcells PresetImgRowsB PresetImg_errbapart PresetImg_oomowned PresetImg_oomconst PresetImg_fqconst PresetImg_sbconst PresetImg_constapart PresetImg_qapart PresetImg_fvzones PresetImg_vis PresetImg_zone3 PresetImg_relro PresetImg_su_tool PresetImg_su_printf PresetImg_su_syslog PresetImg_su_errb.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetImg_hdzx PresetImg_dhash PresetImg_hcw PresetImg_errbqapart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0p.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
(* the walk core last, so its names (layout_ok, ...) win over the start-up modules' homonyms *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMrcSecCf.
Open Scope Z_scope.

Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Record PresetUnitFactsB (B : asyms) : Prop := MkPresetUnitFactsB {
  (* the hypothesis *)
  uf_TS : @im_syms AImg_cgif B;
  (* YF0m.ts_tsd *)
  uf_HTSD : as_tsd B = @im_tsd AImg_cgif;
  (* PresetImg_hoom.hoom_B *)
  uf_HOOM : as_oom_byte B = @im_oom AImg_cgif;
  (* PresetImg_herr.herr_B *)
  uf_HERR : as_errno B = @im_errno AImg_cgif;
  (* YFiacf.img_cover_of_ledger_cf *)
  uf_IMG_COVER : forall ly S md, ALedger_cf tfibsegs ly S md -> img_cover ly;
  (* PresetImg_errnoimg.errno_img_cf_B *)
  uf_ErrnoImgCf : errno_in_img (IM := AImg_cgif) /\ errno_unhidden (IM := AImg_cgif) /\ errno_apart_dzone_ag (IM := AImg_cgif) (AG := AGImg_cgif) /\ errno_apart_shadow_ag (IM := AImg_cgif) (AG := AGImg_cgif) /\ errno_apart_inst_ag (IM := AImg_cgif) (AG := AGImg_cgif) /\ errno_apart_dzone_d (IM := AImg_cgif) (DI := DImg_cgif) /\ errno_apart_izone (IM := AImg_cgif) (DI := DImg_cgif) /\ errno_apart_zone3_d (IM := AImg_cgif) (DI := DImg_cgif) /\ errno_apart_inst_d (IM := AImg_cgif) (DI := DImg_cgif);
  (* PresetImg_errnoseg.errno_seg_B *)
  uf_errno_seg_t : forall a, as_errno B <= a < as_errno B + 4 -> seg_rom (@im_segs AImg_cgif) (Z_to_bv 64 a) <> None;
  (* PresetImg_errnonst.errno_nstatic_B *)
  uf_errno_nstatic_t : forall a, as_errno TfibB <= a < as_errno TfibB + 4 -> ~ Exists (in_zr a) (as_owned_static TfibB);
  (* PresetImg_errnoimgs.errno_apart_dzone_s_B *)
  uf_errno_apart_dzone_s : forall ly a, layout_ok ly -> im_img_cover ly -> ims_dzone ly a -> ~ (as_errno B <= a < as_errno B + 4);
  (* PresetImg_errnoimgs.errno_apart_shadow_s_B *)
  uf_errno_apart_shadow_s : forall a, ImgBaseAGS.SHBv <= a -> ~ (as_errno B <= a < as_errno B + 4);
  (* PresetImg_errnoimgs.errno_apart_zone3_s_B *)
  uf_errno_apart_zone3_s : forall x sz a, ims_zone3 x sz -> x <= a < x + sz -> ~ (as_errno B <= a < as_errno B + 4);
  (* PresetImg_errnoword.errno_word_cf_B *)
  uf_errno_word_cf : 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64;
  (* PresetImg_hshb.HSHB_B *)
  uf_HSHB : @ImgBaseAG.ag_shadow AImg_cgif AGImg_cgif = SHADOW_OFF;
  (* PresetImg_hdzo.hdzo_B *)
  uf_HDZO : forall ly' a, @ImgBaseAG.ag_dzone AImg_cgif AGif0cgif.AGImg_cgif ly' a -> Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize);
  (* PresetImg_hdzx.hdzx_B: HDZX (YGcfInstHit.v:154-155 at commit ee95275bccbf) *)
  uf_HDZX : forall ly' a, layout_ok ly' -> @im_img_cover AImg_cgif ly' ->
    @ImgBaseAG.ag_dzone AImg_cgif AGif0cgif.AGImg_cgif ly' a ->
    ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
    ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2);
  (* PresetImg_hcw.hcw_B: HCW (YGcfInstHit.v:160-162 at commit ee95275bccbf) *)
  uf_HCW : forall ly' c j cl', layout_ok ly' -> @im_img_cover AImg_cgif ly' -> ly_tsd ly' = as_tsd B ->
    In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
    ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j);
  (* PresetImg_dhash.dhash_img_B: dhash_img at TfibB, the unit's dhash tfib_dhash (Reusable/YF0p.v) *)
  uf_dhash_img : forall t : list Z, as_dhash TfibB t = YF0p.tfib_dhash t;
  (* PresetImg_depfp.dep_fp_a_B *)
  uf_dep_fp_img_ag : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> CLdepot.depot_footprint B ly a -> @ImgBaseAG.ag_dzone AImg_cgif AGif0cgif.AGImg_cgif ly a;
  (* PresetImg_depfp.dep_fp_d_B *)
  uf_dep_fp_img_dg : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> CLdepot.depot_footprint B ly a -> @ImgBaseDG.dg_dzone AImg_cgif DGif0cgif.DImg_cgif ly a;
  (* PresetImg_depkeep.dep_keep_a_B *)
  uf_dep_keep_img_ag : forall ly S (W : world (@im_segs AImg_cgif)) (mem0 mem : word -> option byte), layout_ok ly -> @im_img_cover AImg_cgif ly -> ly_tsd ly = as_tsd B -> depot_fits (as_universe B) (st_depot S) -> Forall (cell_holds B ly (aview (@im_segs AImg_cgif) (w_H W) mem0)) (as_const B ly) -> CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_cgif) (w_H W) mem0) -> (forall x : word, ImgBaseAG.ag_dzone ly (bv_unsigned x) \/ ImgBaseAG.ag_czone ly (bv_unsigned x) -> mem x = mem0 x) -> Forall (cell_holds B ly (aview (@im_segs AImg_cgif) (w_H W) mem)) (as_const B ly) /\ CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_cgif) (w_H W) mem);
  (* PresetImg_depkeep.dep_keep_d_B *)
  uf_dep_keep_img_dg : forall ly S (W : world (@im_segs AImg_cgif)) (mem0 mem : word -> option byte), layout_ok ly -> @im_img_cover AImg_cgif ly -> ly_tsd ly = as_tsd B -> depot_fits (as_universe B) (st_depot S) -> Forall (cell_holds B ly (aview (@im_segs AImg_cgif) (w_H W) mem0)) (as_const B ly) -> CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_cgif) (w_H W) mem0) -> (forall x : word, ImgBaseDG.dg_dzone ly (bv_unsigned x) \/ (ImgBaseDG.dg_czone ly (bv_unsigned x) /\ ~ ImgBaseDG.dg_izone (bv_unsigned x)) -> mem x = mem0 x) -> Forall (cell_holds B ly (aview (@im_segs AImg_cgif) (w_H W) mem)) (as_const B ly) /\ CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_cgif) (w_H W) mem);
  (* YF0m.ts_universe *)
  uf_universe_ok : universe_ok (as_universe B);
  (* PresetImg_instok.inst_ag_B *)
  uf_ag_inst_ok : @ag_inst_ok AImg_cgif AGImg_cgif (as_inst B);
  (* PresetImg_instok.fm_inst_ok_B *)
  uf_dg_inst_ok : dg_inst_ok (as_inst B);
  (* PresetImg_instcells.inst_cells_B *)
  uf_INST_CELLS_t : forall ly (H : word -> bool) (mem : word -> option byte), layout_ok ly -> ly_tsd ly = as_tsd B -> Forall (cell_holds B ly (aview im_segs H mem)) (as_const B ly) -> val_mem im_segs (mrestrict H mem) (as_inst B + o_space) 8 (ly_space ly) /\ val_mem im_segs (mrestrict H mem) (as_inst B + 0xe20) 8 0x10000000000 /\ val_mem im_segs (mrestrict H mem) (as_inst B + 0xe28) 8 0x108000010 /\ val_mem im_segs (mrestrict H mem) (as_inst B + o_sec) 8 4096 /\ val_mem im_segs (mrestrict H mem) (as_inst B + o_sec_chunks) 8 (ly_Q ly) /\ val_mem im_segs (mrestrict H mem) (as_inst B + 80) 8 (ly_Q ly) /\ val_mem im_segs (mrestrict H mem) (as_inst B + 88) 8 kPtrArrayResv /\ val_mem im_segs (mrestrict H mem) (as_inst B + o_sec_mutex + 1) 3 0;
  (* PresetImgRowsB.errb_obj_owned_B *)
  uf_errb_obj_owned_t : forall a, @cf_errbuf_obj CfImg_B <= a < @cf_errbuf_obj CfImg_B + 56 -> Exists (in_zr a) (as_owned_static B);
  (* PresetImg_errbapart.ERRB_APART_B *)
  uf_ERRB_APART : forall a, @cf_errbuf_obj CfImg_B <= a < @cf_errbuf_obj CfImg_B + 56 -> ~ dg_izone a /\ (forall ly, ((layout_ok ly /\ ly_tsd ly = as_tsd TfibB /\ Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static TfibB ++ as_zero_shadow TfibB)) /\ im_img_cover ly /\ asyms_ok TfibB) -> ~ dg_dzone ly a);
  (* PresetImg_oomowned.oom_owned_img_B *)
  uf_oom_owned_img : ~ (as_inst B <= as_oom_byte B < as_inst B + 3632) /\ ~ (as_depot B <= as_oom_byte B < as_depot B + (4 * 2 ^ 20 + 32)) /\ ~ (as_store B <= as_oom_byte B < as_store B + 32) /\ ~ (as_ialloc_lo B <= as_oom_byte B < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= as_oom_byte B < as_ialloc_flag B + 2);
  (* PresetImg_oomconst.oom_const_img_B *)
  uf_oom_const_img : forall ly c k, (layout_ok ly /\ ly_tsd ly = as_tsd B /\ Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B)) -> In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> Exists (in_zr (aeval B ly (c_at c) + k)) (as_owned_static B) -> aeval B ly (c_at c) + k <> as_oom_byte B;
  (* PresetImg_fqconst.FQ_CONST_B *)
  uf_FQ_CONST : forall ly, (exists e, In (ACell e 8 (AV (ANum kQuarantineMax))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_max) /\ (exists e, In (ACell e 8 (AV (ANum kQuarantineCacheMax))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_maxcache) /\ (exists e, In (ACell e 8 (AV (ANum kQuarantineMin))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_min) /\ (exists e, In (ACell e 2 (AV (ANum 0))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_cmutex + 2);
  (* PresetImg_sbconst.SB_CONST_B *)
  uf_SB_CONST : forall ly, In (ACell (AInst o_space) 8 (AV (ASp 0))) (@im_const AImg_cgif ly);
  (* PresetImg_constapart.CONST_APART_B *)
  uf_CONST_APART : forall ly c, (layout_ok ly /\ ly_tsd ly = as_tsd B /\ Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B)) -> In c (@im_const AImg_cgif ly) -> (aeval B ly (c_at c) = as_inst B + o_q_cmutex + 2 /\ c_w c = 2%nat /\ c_val c = AV (ANum 0)) \/ (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> ~ DMiface.qhdr (as_inst B) ly (aeval B ly (c_at c) + k) /\ ~ (ly_prim ly <= aeval B ly (c_at c) + k < ly_prim ly + kPrimResvSize));
  (* PresetImg_qapart.IMG_QAPART_B: IMG_QAPART, four clauses (YGcfInstDrainX.v:65-68 at commit 8b12df2b772) *)
  uf_IMG_QAPART : forall a, ((as_inst B + o_quar + 152 <= a < as_inst B + o_quar + 156) \/ (as_inst B + o_quar + 160 <= a < as_inst B + o_quar + 192)) -> ~ (as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32) /\ ~ (as_store B <= a < as_store B + 32) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2);
  (* PresetImg_fvzones.fv_ial_img *)
  uf_FV_IAL : forall (W : world im_segs) (m : word -> option byte), @dg_ial_post AImg_cgif DImg_cgif W m <-> (let m' := mrestrict (w_H W) m in val_mem im_segs m' (as_ialloc_flag B) 1 1 /\ val_mem im_segs m' (as_ialloc_flag B + 1) 1 0 /\ val_mem im_segs m' (as_ialloc_w B) 8 4096 /\ val_mem im_segs m' (as_ialloc_w B + 8) 8 (as_ialloc_w B + 16) /\ (forall a, as_ialloc_lo B <= a < as_ialloc_w B \/ as_ialloc_w B + 16 <= a < as_ialloc_hi B -> mbyte im_segs m' a = Some (Z_to_bv 8 0)));
  (* PresetImg_fvzones.fv_zone3_img *)
  uf_FV_ZONE3 : forall ly x sz, @im_img_cover AImg_cgif ly -> 0 <= sz -> in_app x sz -> zdisjoint (x, sz) (ly_img ly) -> @dg_zone3 AImg_cgif DImg_cgif x sz;
  (* PresetImg_fvzones.dzone_owned_img *)
  uf_DZONE_OWNED : forall ly a, @dg_dzone AImg_cgif DImg_cgif ly a -> Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize);
  (* PresetImg_fvzones.izone_owned_img *)
  uf_IZONE_OWNED : forall a, @dg_izone AImg_cgif DImg_cgif a -> (as_ialloc_lo B <= a < as_ialloc_hi B) \/ Exists (in_zr a) (as_owned_static B);
  (* PresetImg_vis.comb_vis_B *)
  uf_COMB_VIS : forall (H : word -> bool) (mem : word -> option byte) a, as_inst B + o_comb_stats <= a < as_inst B + o_comb_stats + 40 -> aview (@im_segs AImg_cgif) H mem a <> None;
  (* PresetImg_vis.errno_vis_B *)
  uf_ERRNO_VIS : forall (H : word -> bool) (mem : word -> option byte) a, as_errno B <= a < as_errno B + 4 -> aview (@im_segs AImg_cgif) H mem a <> None;
  (* PresetImg_vis.dep_unhid_B *)
  uf_DEP_UNHID : forall (W : world (@im_segs AImg_cgif)) a, (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (as_store B <= a < as_store B + 64) -> w_H W (Z_to_bv 64 a) = false;
  (* PresetImg_zone3.zone3_B *)
  uf_ZONE3 : forall ly x sz, @im_img_cover AImg_cgif ly -> 0 <= sz -> in_app x sz -> zdisjoint (x, sz) (ly_img ly) -> ims_zone3 (AImgS := AImgS_cgif) x sz;
  (* PresetImg_zone3.const_keep_s_B *)
  uf_CONST_KEEP_S : forall ly (H : word -> bool) (mem0 mem : word -> option byte), layout_ok ly -> @im_img_cover AImg_cgif ly -> ly_tsd ly = as_tsd B -> Forall (cell_holds B ly (aview (@im_segs AImg_cgif) H mem0)) (as_const B ly) -> (forall x : word, ims_dzone (AImgS := AImgS_cgif) ly (bv_unsigned x) \/ CZS (IM := AImg_cgif) (IMS := AImgS_cgif) ly (as_inst B) (bv_unsigned x) -> mem x = mem0 x) -> (forall k, 1 <= k < 4 -> aview (@im_segs AImg_cgif) H mem (as_inst B + o_sec_mutex + k) = Some 0) -> Forall (cell_holds B ly (aview (@im_segs AImg_cgif) H mem)) (as_const B ly);
  (* PresetImg_zone3.const_not_junk_B *)
  uf_CONST_NOT_JUNK : forall ly (regs0 : bvmap 5 word) n c k, layout_ok ly -> @im_img_cover AImg_cgif ly -> ly_tsd ly = as_tsd B -> bv_unsigned (getr regs0 11) = as_inst B -> 64513 <= n < @cf_malloc_max CfParams_preset -> In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> ~ ((ly_T ly + 2768 <= aeval B ly (c_at c) + k < ly_T ly + 2824) \/ (ly_T ly + 2872 <= aeval B ly (c_at c) + k < ly_T ly + 2888) \/ (ly_T ly + 2904 <= aeval B ly (c_at c) + k < ly_T ly + 2912) \/ (as_inst B + o_sec_sorted <= aeval B ly (c_at c) + k < as_inst B + o_sec_sorted + 1) \/ (as_inst B + o_sec_stats <= aeval B ly (c_at c) + k < as_inst B + o_sec_stats + 32) \/ (ImgBaseAGS.BSLv regs0 n <= aeval B ly (c_at c) + k < ImgBaseAGS.BSLv regs0 n + 8) \/ (as_inst B + o_comb_stats <= aeval B ly (c_at c) + k < as_inst B + o_comb_stats + 40) \/ aeval B ly (c_at c) + k = as_oom_byte B);
  (* PresetImg_zone3.areas_disj_B *)
  uf_AREAS_DISJ : pairwise zdisjoint (asyms_areas B);
  (* PresetImgRowsB.img_sapart_B *)
  uf_IMG_SAPART : forall a, ((as_inst B + 680 <= a < as_inst B + 684) \/ (as_inst B + 120 <= a < as_inst B + 129) \/ (as_inst B + 144 <= a < as_inst B + 160) \/ (as_inst B + 704 <= a < as_inst B + 720)) -> ~ (as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32) /\ ~ (as_store B <= a < as_store B + 32) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2);
  (* PresetImgRowsB.img_junk_B *)
  uf_IMG_JUNK : forall ly r0, layout_ok ly -> In r0 (as_junk B ly) -> forall j, 0 <= j < snd r0 -> exists sg, In sg (@im_segs AImg_cgif) /\ Z.of_N (seg_base sg) <= aeval B ly (fst r0) + j < Z.of_N (seg_base sg) + Z.of_N (seg_size sg);
  (* ERRB_SEP_t (YGcfErrbSep.v:25-28 at commit 76362ece943) = ERRB_QAPART (YGcfImgRows.v:22-23) /\ the rest:
     PresetImg_errbqapart.ERRB_QAPART_B and the last four conjuncts of PresetImgRowsB.errb_sep_B *)
  uf_ERRB_SEP : (forall B, @im_syms AImg_cgif B -> forall a, @cf_errbuf_obj CfImg_B <= a < @cf_errbuf_obj CfImg_B + 56 -> ~ (as_inst B <= a < as_inst B + 3632)) /\
    forall ly a, layout_ok ly -> @im_img_cover AImg_cgif ly -> ly_tsd ly = as_tsd B -> @cf_errbuf_obj CfImg_B <= a < @cf_errbuf_obj CfImg_B + 56 ->
    a <> as_oom_byte B /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ ims_dzone ly a /\ ~ ag_dzone ly a;
  (* PresetImgRowsB.exh_off_B: EXH_OFF_t (YGcfImgRows.v:25 at commit 76362ece943) *)
  uf_EXH_OFF : @cf_exh_off CfImg_B = 68;
  (* PresetImg_relro.silent_img_B *)
  uf_RELRO_silent : val_mem tfibsegs (fun _ => None) PresetImg_relro.C_SILENT_B 8 1;
  (* PresetImg_su_tool.su_tool_B *)
  uf_su_tool : (forall h ch, HS_tfib h = Some ch -> kn_read tfibsegs ch (ELit 0) PresetImg_su_tool.RB_TOOL_NAME_CELL 8 = Some (ELit PresetImg_su_tool.RB_TOOL_NAME_STR)) /\ kn_read tfibsegs JS_tfib_band (ELit 0) PresetImg_su_tool.RB_TOOL_NAME_CELL 8 = Some (ELit PresetImg_su_tool.RB_TOOL_NAME_STR) /\ (forall k, (k < 17)%nat -> seg_rom tfibsegs (Z_to_bv 64 (PresetImg_su_tool.RB_TOOL_NAME_STR + Z.of_nat k)) = Some (Z_to_bv 8 (nth k PresetImg_su_tool.asan_tool_name 0)));
  (* PresetImg_su_printf.presetB_su_printf *)
  uf_su_printf : (forall s, In s YB01.HS_tfib_list -> In (KWord {| a_base := ELit 0; a_off := PresetImg_su_printf.presetB_printf_cb_cell |} 8 (ELit PresetImg_su_printf.presetB_printf_cb_fn)) (s_know (a_ss s))) /\ In (KWord {| a_base := ELit 0; a_off := PresetImg_su_printf.presetB_printf_cb_cell |} 8 (ELit PresetImg_su_printf.presetB_printf_cb_fn)) (s_know (a_ss YB03.JS_tfib_band));
  (* PresetImg_su_syslog.su_syslog_B *)
  uf_su_syslog : forall (ly : alayout), In (z8 (ANum PresetImg_su_syslog.presetb_log_to_syslog_addr) 0) (@im_const AImg_cgif ly);
  (* PresetImg_su_errb.errb_obj_zero_start *)
  uf_su_errb_obj_zero : ltac:(let t := type of (@PresetImg_su_errb.errb_obj_zero_start) in exact t);
  (* PresetImg_su_errb.exh_bytes_zero_start *)
  uf_su_exh_bytes_zero : ltac:(let t := type of (@PresetImg_su_errb.exh_bytes_zero_start) in exact t)
}.

Theorem preset_unit_facts_B : forall B, TfibSyms B -> PresetUnitFactsB B.
Proof.
intros B TS.
exact {|
  uf_TS := TS;
  uf_HTSD := YF0m.ts_tsd B TS;
  uf_HOOM := PresetImg_hoom.hoom_B B TS;
  uf_HERR := PresetImg_herr.herr_B B TS;
  uf_IMG_COVER := YFiacf.img_cover_of_ledger_cf;
  uf_ErrnoImgCf := PresetImg_errnoimg.errno_img_cf_B;
  uf_errno_seg_t := PresetImg_errnoseg.errno_seg_B B TS;
  uf_errno_nstatic_t := PresetImg_errnonst.errno_nstatic_B;
  uf_errno_apart_dzone_s := fun ly a => PresetImg_errnoimgs.errno_apart_dzone_s_B B ly a TS;
  uf_errno_apart_shadow_s := fun a => PresetImg_errnoimgs.errno_apart_shadow_s_B B a TS;
  uf_errno_apart_zone3_s := fun x sz a => PresetImg_errnoimgs.errno_apart_zone3_s_B B x sz a TS;
  uf_errno_word_cf := ErrnoWordB.errno_word_cf_B B TS;
  uf_HSHB := PresetImg_hshb.HSHB_B;
  uf_HDZO := PresetImg_hdzo.hdzo_B B TS;
  uf_HDZX := PresetImg_hdzx.hdzx_B B TS;
  uf_HCW := PresetImg_hcw.hcw_B B TS;
  uf_dhash_img := PresetImg_dhash.dhash_img_B;
  uf_dep_fp_img_ag := PresetImg_depfp.dep_fp_a_B B TS;
  uf_dep_fp_img_dg := PresetImg_depfp.dep_fp_d_B B TS;
  uf_dep_keep_img_ag := PresetImg_depkeep.dep_keep_a_B B TS;
  uf_dep_keep_img_dg := PresetImg_depkeep.dep_keep_d_B B TS;
  uf_universe_ok := YF0m.ts_universe B TS;
  uf_ag_inst_ok := PresetImg_instok.inst_ag_B B TS;
  uf_dg_inst_ok := PresetImg_instok.fm_inst_ok_B B TS;
  uf_INST_CELLS_t := PresetImg_instcells.inst_cells_B B TS;
  uf_errb_obj_owned_t := PresetImgRowsB.errb_obj_owned_B B TS;
  uf_ERRB_APART := PresetImg_errbapart.ERRB_APART_B;
  uf_oom_owned_img := PresetImg_oomowned.oom_owned_img_B B TS;
  uf_oom_const_img := PresetImg_oomconst.oom_const_img_B B TS;
  uf_FQ_CONST := PresetImg_fqconst.FQ_CONST_B B TS;
  uf_SB_CONST := PresetImg_sbconst.SB_CONST_B;
  uf_CONST_APART := fun ly c => PresetImg_constapart.CONST_APART_B B ly c TS;
  uf_IMG_QAPART := PresetImg_qapart.IMG_QAPART_B B TS;
  uf_FV_IAL := PresetImg_fvzones.fv_ial_img B TS;
  uf_FV_ZONE3 := PresetImg_fvzones.fv_zone3_img;
  uf_DZONE_OWNED := PresetImg_fvzones.dzone_owned_img B TS;
  uf_IZONE_OWNED := PresetImg_fvzones.izone_owned_img B TS;
  uf_COMB_VIS := PresetImg_vis.comb_vis_B B TS;
  uf_ERRNO_VIS := PresetImg_vis.errno_vis_B B TS;
  uf_DEP_UNHID := PresetImg_vis.dep_unhid_B B TS;
  uf_ZONE3 := PresetImg_zone3.zone3_B;
  uf_CONST_KEEP_S := PresetImg_zone3.const_keep_s_B B TS;
  uf_CONST_NOT_JUNK := PresetImg_zone3.const_not_junk_B B TS;
  uf_AREAS_DISJ := PresetImg_zone3.areas_disj_B B TS;
  uf_IMG_SAPART := DMrcSecCf.img_sapart_preset B TS;
  uf_IMG_JUNK := fun ly r0 => DMrcSecCf.img_junk_preset B ly r0 TS;
  uf_ERRB_SEP := conj PresetImg_errbqapart.ERRB_QAPART_B (fun ly a LY IC HT Ha => proj2 (PresetImgRowsB.errb_sep_B B TS ly a LY IC HT Ha));
  uf_EXH_OFF := PresetImgRowsB.exh_off_B;
  uf_RELRO_silent := PresetImg_relro.silent_img_B;
  uf_su_tool := PresetImg_su_tool.su_tool_B;
  uf_su_printf := PresetImg_su_printf.presetB_su_printf;
  uf_su_syslog := fun ly => PresetImg_su_syslog.su_syslog_B B ly TS;
  uf_su_errb_obj_zero := @PresetImg_su_errb.errb_obj_zero_start;
  uf_su_exh_bytes_zero := @PresetImg_su_errb.exh_bytes_zero_start
|}.
Qed.

End u.
