(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, for a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply): reply's UNIT FACTS at
   image B (fuzz_reply.asan-ubsan, pin 10ffb5f9202a).
   rule 24: no function proved (kind: statement text; the unit-hypothesis rows of the cf layer, wired from their proved
   row lemmas into one record).

   ReplyUnitFactsB B bundles, as fields uf_<row name>, every image / start-up row of the layer's unit-hypothesis table
   (CF-UNIT-HYPS.md (sha256 77b3f94c95d2; internal record) Table 1 and Table 4) that is proved at this image, each field's statement the row lemma's
   own statement (the layer text at reply's instances AImg_reply, AGImg_reply, AImgS_reply, DImg_reply, CfImg_B).
   reply_unit_facts_B gives the record for every B with the image's symbol facts (TfibSyms B), each field closed by
   `exact` from its row lemma (lib/B/ReplyImg_*.v and lib/B/ReplyImgRowsB.v at lane W's head 6f1cb063e69).  The record
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YP0m YP0e YP09 YP02 YP0l YP0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP06 YP03 YP04 YP0g YP01 YP0i YP0j YN3v YI04 YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YM05 YK0s YO0d YA0p YG04 YG06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG07 YG03 YG0q YGcfNames YO0f YK00 YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0e YA0d YA02 YA0j YG0r YG0b YD1h YI00 YE00 YK07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply ImgBaseAG ImgBaseDG AGif0reply DGif0reply YFl0 YD2l CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ErrnoApart ErrnoApartreply ImgBaseAGS AGif4reply YB13 YB12 YB1h YB01 YD1g YD2i YE01 YE2k YB03 YB1w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif4.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMiface AGis DGgi CLdepot YFfl YFi5 YFff AGjm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YFiacf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyImg_hoom ReplyImg_herr ReplyImg_errnoimg ReplyImg_errnoseg ReplyImg_errnonst ReplyImg_errnoimgs ReplyImg_errnoword ReplyImg_hshb ReplyImg_hdzo ReplyImg_depfp ReplyImg_depkeep ReplyImg_instok ReplyImg_instcells ReplyImgRowsB ReplyImg_errbapart ReplyImg_oomowned ReplyImg_oomconst ReplyImg_fqconst ReplyImg_sbconst ReplyImg_constapart ReplyImg_qapart ReplyImg_fvzones ReplyImg_vis ReplyImg_zone3 ReplyImg_relro ReplyImg_su_tool ReplyImg_su_printf ReplyImg_su_syslog ReplyImg_su_errb.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyImg_hdzx ReplyImg_dhash ReplyImg_hcw ReplyImg_errbqapart.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YF0p.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
(* the walk core last, so its names (layout_ok, ...) win over the start-up modules' homonyms *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply.
Open Scope Z_scope.

Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Record ReplyUnitFactsB (B : asyms) : Prop := MkReplyUnitFactsB {
  (* the hypothesis *)
  uf_TS : @im_syms AImg_reply B;
  (* YF0m.ts_tsd *)
  uf_HTSD : as_tsd B = @im_tsd AImg_reply;
  (* ReplyImg_hoom.hoom_B *)
  uf_HOOM : as_oom_byte B = @im_oom AImg_reply;
  (* ReplyImg_herr.herr_B *)
  uf_HERR : as_errno B = @im_errno AImg_reply;
  (* YFiacf.img_cover_of_ledger_cf *)
  uf_IMG_COVER : forall ly S md, ALedger_cf tfibsegs ly S md -> img_cover ly;
  (* ReplyImg_errnoimg.errno_img_cf_B *)
  uf_ErrnoImgCf : errno_in_img (IM := AImg_reply) /\ errno_unhidden (IM := AImg_reply) /\ errno_apart_dzone_ag (IM := AImg_reply) (AG := AGImg_reply) /\ errno_apart_shadow_ag (IM := AImg_reply) (AG := AGImg_reply) /\ errno_apart_inst_ag (IM := AImg_reply) (AG := AGImg_reply) /\ errno_apart_dzone_d (IM := AImg_reply) (DI := DImg_reply) /\ errno_apart_izone (IM := AImg_reply) (DI := DImg_reply) /\ errno_apart_zone3_d (IM := AImg_reply) (DI := DImg_reply) /\ errno_apart_inst_d (IM := AImg_reply) (DI := DImg_reply);
  (* ReplyImg_errnoseg.errno_seg_B *)
  uf_errno_seg_t : forall a, as_errno B <= a < as_errno B + 4 -> seg_rom (@im_segs AImg_reply) (Z_to_bv 64 a) <> None;
  (* ReplyImg_errnonst.errno_nstatic_B *)
  uf_errno_nstatic_t : forall a, as_errno TfibB <= a < as_errno TfibB + 4 -> ~ Exists (in_zr a) (as_owned_static TfibB);
  (* ReplyImg_errnoimgs.errno_apart_dzone_s_B *)
  uf_errno_apart_dzone_s : forall ly a, layout_ok ly -> im_img_cover ly -> ims_dzone ly a -> ~ (as_errno B <= a < as_errno B + 4);
  (* ReplyImg_errnoimgs.errno_apart_shadow_s_B *)
  uf_errno_apart_shadow_s : forall a, ImgBaseAGS.SHBv <= a -> ~ (as_errno B <= a < as_errno B + 4);
  (* ReplyImg_errnoimgs.errno_apart_zone3_s_B *)
  uf_errno_apart_zone3_s : forall x sz a, ims_zone3 x sz -> x <= a < x + sz -> ~ (as_errno B <= a < as_errno B + 4);
  (* ReplyImg_errnoword.errno_word_cf_B *)
  uf_errno_word_cf : 0 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64;
  (* ReplyImg_hshb.HSHB_B *)
  uf_HSHB : @ImgBaseAG.ag_shadow AImg_reply AGImg_reply = SHADOW_OFF;
  (* ReplyImg_hdzo.hdzo_B *)
  uf_HDZO : forall ly' a, @ImgBaseAG.ag_dzone AImg_reply AGif0reply.AGImg_reply ly' a -> Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize);
  (* ReplyImg_hdzx.hdzx_B: HDZX (YGcfInstHit.v:154-155 at commit ee95275bccbf) *)
  uf_HDZX : forall ly' a, layout_ok ly' -> @im_img_cover AImg_reply ly' ->
    @ImgBaseAG.ag_dzone AImg_reply AGif0reply.AGImg_reply ly' a ->
    ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
    ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2);
  (* ReplyImg_hcw.hcw_B: HCW (YGcfInstHit.v:160-162 at commit ee95275bccbf) *)
  uf_HCW : forall ly' c j cl', layout_ok ly' -> @im_img_cover AImg_reply ly' -> ly_tsd ly' = as_tsd B ->
    In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
    ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j);
  (* ReplyImg_dhash.dhash_img_B: dhash_img at TfibB, the unit's dhash tfib_dhash (Reusable/YF0p.v) *)
  uf_dhash_img : forall t : list Z, as_dhash TfibB t = YF0p.tfib_dhash t;
  (* ReplyImg_depfp.dep_fp_a_B *)
  uf_dep_fp_img_ag : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> CLdepot.depot_footprint B ly a -> @ImgBaseAG.ag_dzone AImg_reply AGif0reply.AGImg_reply ly a;
  (* ReplyImg_depfp.dep_fp_d_B *)
  uf_dep_fp_img_dg : forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> CLdepot.depot_footprint B ly a -> @ImgBaseDG.dg_dzone AImg_reply DGif0reply.DImg_reply ly a;
  (* ReplyImg_depkeep.dep_keep_a_B *)
  uf_dep_keep_img_ag : forall ly S (W : world (@im_segs AImg_reply)) (mem0 mem : word -> option byte), layout_ok ly -> @im_img_cover AImg_reply ly -> ly_tsd ly = as_tsd B -> List.NoDup (st_depot S) -> incl (st_depot S) (as_universe B) -> Forall (cell_holds B ly (aview (@im_segs AImg_reply) (w_H W) mem0)) (as_const B ly) -> CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_reply) (w_H W) mem0) -> (forall x : word, ImgBaseAG.ag_dzone ly (bv_unsigned x) \/ ImgBaseAG.ag_czone ly (bv_unsigned x) -> mem x = mem0 x) -> Forall (cell_holds B ly (aview (@im_segs AImg_reply) (w_H W) mem)) (as_const B ly) /\ CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_reply) (w_H W) mem);
  (* ReplyImg_depkeep.dep_keep_d_B *)
  uf_dep_keep_img_dg : forall ly S (W : world (@im_segs AImg_reply)) (mem0 mem : word -> option byte), layout_ok ly -> @im_img_cover AImg_reply ly -> ly_tsd ly = as_tsd B -> List.NoDup (st_depot S) -> incl (st_depot S) (as_universe B) -> Forall (cell_holds B ly (aview (@im_segs AImg_reply) (w_H W) mem0)) (as_const B ly) -> CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_reply) (w_H W) mem0) -> (forall x : word, ImgBaseDG.dg_dzone ly (bv_unsigned x) \/ (ImgBaseDG.dg_czone ly (bv_unsigned x) /\ ~ ImgBaseDG.dg_izone (bv_unsigned x)) -> mem x = mem0 x) -> Forall (cell_holds B ly (aview (@im_segs AImg_reply) (w_H W) mem)) (as_const B ly) /\ CLdepot.depot_mem_ok B ly S (aview (@im_segs AImg_reply) (w_H W) mem);
  (* YF0m.ts_universe *)
  uf_universe_ok : universe_ok (as_universe B);
  (* ReplyImg_instok.inst_ag_B *)
  uf_ag_inst_ok : @ag_inst_ok AImg_reply AGImg_reply (as_inst B);
  (* ReplyImg_instok.fm_inst_ok_B *)
  uf_dg_inst_ok : dg_inst_ok (as_inst B);
  (* ReplyImg_instcells.inst_cells_B *)
  uf_INST_CELLS_t : forall ly (H : word -> bool) (mem : word -> option byte), layout_ok ly -> ly_tsd ly = as_tsd B -> Forall (cell_holds B ly (aview im_segs H mem)) (as_const B ly) -> val_mem im_segs (mrestrict H mem) (as_inst B + o_space) 8 (ly_space ly) /\ val_mem im_segs (mrestrict H mem) (as_inst B + 0xe20) 8 0x10000000000 /\ val_mem im_segs (mrestrict H mem) (as_inst B + 0xe28) 8 0x108000010 /\ val_mem im_segs (mrestrict H mem) (as_inst B + o_sec) 8 4096 /\ val_mem im_segs (mrestrict H mem) (as_inst B + o_sec_chunks) 8 (ly_Q ly) /\ val_mem im_segs (mrestrict H mem) (as_inst B + 80) 8 (ly_Q ly) /\ val_mem im_segs (mrestrict H mem) (as_inst B + 88) 8 kPtrArrayResv /\ val_mem im_segs (mrestrict H mem) (as_inst B + o_sec_mutex + 1) 3 0;
  (* ReplyImgRowsB.errb_obj_owned_B *)
  uf_errb_obj_owned_t : forall a, @cf_errbuf_obj CfImg_B <= a < @cf_errbuf_obj CfImg_B + 56 -> Exists (in_zr a) (as_owned_static B);
  (* ReplyImg_errbapart.ERRB_APART_B *)
  uf_ERRB_APART : forall a, @cf_errbuf_obj CfImg_B <= a < @cf_errbuf_obj CfImg_B + 56 -> ~ dg_izone a /\ (forall ly, ((layout_ok ly /\ ly_tsd ly = as_tsd TfibB /\ Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static TfibB ++ as_zero_shadow TfibB)) /\ im_img_cover ly /\ asyms_ok TfibB) -> ~ dg_dzone ly a);
  (* ReplyImg_oomowned.oom_owned_img_B *)
  uf_oom_owned_img : ~ (as_inst B <= as_oom_byte B < as_inst B + 3632) /\ ~ (as_depot B <= as_oom_byte B < as_depot B + (4 * 2 ^ 20 + 32)) /\ ~ (as_store B <= as_oom_byte B < as_store B + 32) /\ ~ (as_ialloc_lo B <= as_oom_byte B < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= as_oom_byte B < as_ialloc_flag B + 2);
  (* ReplyImg_oomconst.oom_const_img_B *)
  uf_oom_const_img : forall ly c k, (layout_ok ly /\ ly_tsd ly = as_tsd B /\ Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B)) -> In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> Exists (in_zr (aeval B ly (c_at c) + k)) (as_owned_static B) -> aeval B ly (c_at c) + k <> as_oom_byte B;
  (* ReplyImg_fqconst.FQ_CONST_B *)
  uf_FQ_CONST : forall ly, (exists e, In (ACell e 8 (AV (ANum kQuarantineMax))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_max) /\ (exists e, In (ACell e 8 (AV (ANum kQuarantineCacheMax))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_maxcache) /\ (exists e, In (ACell e 8 (AV (ANum kQuarantineMin))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_min) /\ (exists e, In (ACell e 2 (AV (ANum 0))) (as_const B ly) /\ aeval B ly e = as_inst B + o_q_cmutex + 2);
  (* ReplyImg_sbconst.SB_CONST_B *)
  uf_SB_CONST : forall ly, In (ACell (AInst o_space) 8 (AV (ASp 0))) (@im_const AImg_reply ly);
  (* ReplyImg_constapart.CONST_APART_B *)
  uf_CONST_APART : forall ly c, (layout_ok ly /\ ly_tsd ly = as_tsd B /\ Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B)) -> In c (@im_const AImg_reply ly) -> (aeval B ly (c_at c) = as_inst B + o_q_cmutex + 2 /\ c_w c = 2%nat /\ c_val c = AV (ANum 0)) \/ (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> ~ DMiface.qhdr (as_inst B) ly (aeval B ly (c_at c) + k) /\ ~ (ly_prim ly <= aeval B ly (c_at c) + k < ly_prim ly + kPrimResvSize));
  (* ReplyImg_qapart.IMG_QAPART_B: IMG_QAPART, four clauses (YGcfInstDrainX.v:65-68 at commit 8b12df2b772) *)
  uf_IMG_QAPART : forall a, ((as_inst B + o_quar + 152 <= a < as_inst B + o_quar + 156) \/ (as_inst B + o_quar + 160 <= a < as_inst B + o_quar + 192)) -> ~ (as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32) /\ ~ (as_store B <= a < as_store B + 32) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2);
  (* ReplyImg_fvzones.fv_ial_img *)
  uf_FV_IAL : forall (W : world im_segs) (m : word -> option byte), @dg_ial_post AImg_reply DImg_reply W m <-> (let m' := mrestrict (w_H W) m in val_mem im_segs m' (as_ialloc_flag B) 1 1 /\ val_mem im_segs m' (as_ialloc_flag B + 1) 1 0 /\ val_mem im_segs m' (as_ialloc_w B) 8 4096 /\ val_mem im_segs m' (as_ialloc_w B + 8) 8 (as_ialloc_w B + 16) /\ (forall a, as_ialloc_lo B <= a < as_ialloc_w B \/ as_ialloc_w B + 16 <= a < as_ialloc_hi B -> mbyte im_segs m' a = Some (Z_to_bv 8 0)));
  (* ReplyImg_fvzones.fv_zone3_img *)
  uf_FV_ZONE3 : forall ly x sz, @im_img_cover AImg_reply ly -> 0 <= sz -> in_app x sz -> zdisjoint (x, sz) (ly_img ly) -> @dg_zone3 AImg_reply DImg_reply x sz;
  (* ReplyImg_fvzones.dzone_owned_img *)
  uf_DZONE_OWNED : forall ly a, @dg_dzone AImg_reply DImg_reply ly a -> Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize);
  (* ReplyImg_fvzones.izone_owned_img *)
  uf_IZONE_OWNED : forall a, @dg_izone AImg_reply DImg_reply a -> (as_ialloc_lo B <= a < as_ialloc_hi B) \/ Exists (in_zr a) (as_owned_static B);
  (* ReplyImg_vis.comb_vis_B *)
  uf_COMB_VIS : forall (H : word -> bool) (mem : word -> option byte) a, as_inst B + o_comb_stats <= a < as_inst B + o_comb_stats + 40 -> aview (@im_segs AImg_reply) H mem a <> None;
  (* ReplyImg_vis.errno_vis_B *)
  uf_ERRNO_VIS : forall (H : word -> bool) (mem : word -> option byte) a, as_errno B <= a < as_errno B + 4 -> aview (@im_segs AImg_reply) H mem a <> None;
  (* ReplyImg_vis.dep_unhid_B *)
  uf_DEP_UNHID : forall (W : world (@im_segs AImg_reply)) a, (as_depot B <= a < as_depot B + d_map1 + 8 * 32768) \/ (as_store B <= a < as_store B + 64) -> w_H W (Z_to_bv 64 a) = false;
  (* ReplyImg_zone3.zone3_B *)
  uf_ZONE3 : forall ly x sz, @im_img_cover AImg_reply ly -> 0 <= sz -> in_app x sz -> zdisjoint (x, sz) (ly_img ly) -> ims_zone3 (AImgS := AImgS_reply) x sz;
  (* ReplyImg_zone3.const_keep_s_B *)
  uf_CONST_KEEP_S : forall ly (H : word -> bool) (mem0 mem : word -> option byte), layout_ok ly -> @im_img_cover AImg_reply ly -> ly_tsd ly = as_tsd B -> Forall (cell_holds B ly (aview (@im_segs AImg_reply) H mem0)) (as_const B ly) -> (forall x : word, ims_dzone (AImgS := AImgS_reply) ly (bv_unsigned x) \/ CZS (IM := AImg_reply) (IMS := AImgS_reply) ly (as_inst B) (bv_unsigned x) -> mem x = mem0 x) -> (forall k, 1 <= k < 4 -> aview (@im_segs AImg_reply) H mem (as_inst B + o_sec_mutex + k) = Some 0) -> Forall (cell_holds B ly (aview (@im_segs AImg_reply) H mem)) (as_const B ly);
  (* ReplyImg_zone3.const_not_junk_B *)
  uf_CONST_NOT_JUNK : forall ly (regs0 : bvmap 5 word) n c k, layout_ok ly -> @im_img_cover AImg_reply ly -> ly_tsd ly = as_tsd B -> bv_unsigned (getr regs0 11) = as_inst B -> 64513 <= n < @cf_malloc_max CfParams_reply -> In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> ~ ((ly_T ly + 2768 <= aeval B ly (c_at c) + k < ly_T ly + 2824) \/ (ly_T ly + 2872 <= aeval B ly (c_at c) + k < ly_T ly + 2888) \/ (ly_T ly + 2904 <= aeval B ly (c_at c) + k < ly_T ly + 2912) \/ (as_inst B + o_sec_sorted <= aeval B ly (c_at c) + k < as_inst B + o_sec_sorted + 1) \/ (as_inst B + o_sec_stats <= aeval B ly (c_at c) + k < as_inst B + o_sec_stats + 32) \/ (ImgBaseAGS.BSLv regs0 n <= aeval B ly (c_at c) + k < ImgBaseAGS.BSLv regs0 n + 8) \/ (as_inst B + o_comb_stats <= aeval B ly (c_at c) + k < as_inst B + o_comb_stats + 40) \/ aeval B ly (c_at c) + k = as_oom_byte B);
  (* ReplyImg_zone3.areas_disj_B *)
  uf_AREAS_DISJ : pairwise zdisjoint (asyms_areas B);
  (* ReplyImgRowsB.img_sapart_B *)
  uf_IMG_SAPART : forall a, ((as_inst B + 680 <= a < as_inst B + 684) \/ (as_inst B + 120 <= a < as_inst B + 129) \/ (as_inst B + 144 <= a < as_inst B + 160) \/ (as_inst B + 704 <= a < as_inst B + 720)) -> ~ (as_depot B <= a < as_depot B + 4 * 2 ^ 20 + 32) /\ ~ (as_store B <= a < as_store B + 32) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2);
  (* ReplyImgRowsB.img_junk_B *)
  uf_IMG_JUNK : forall ly r0, layout_ok ly -> In r0 (as_junk B ly) -> forall j, 0 <= j < snd r0 -> exists sg, In sg (@im_segs AImg_reply) /\ Z.of_N (seg_base sg) <= aeval B ly (fst r0) + j < Z.of_N (seg_base sg) + Z.of_N (seg_size sg);
  (* ERRB_SEP_t (YGcfErrbSep.v:25-28 at commit 76362ece943) = ERRB_QAPART (YGcfImgRows.v:22-23) /\ the rest:
     ReplyImg_errbqapart.ERRB_QAPART_B and the last four conjuncts of ReplyImgRowsB.errb_sep_B *)
  uf_ERRB_SEP : (forall B, @im_syms AImg_reply B -> forall a, @cf_errbuf_obj CfImg_B <= a < @cf_errbuf_obj CfImg_B + 56 -> ~ (as_inst B <= a < as_inst B + 3632)) /\
    forall ly a, layout_ok ly -> @im_img_cover AImg_reply ly -> ly_tsd ly = as_tsd B -> @cf_errbuf_obj CfImg_B <= a < @cf_errbuf_obj CfImg_B + 56 ->
    a <> as_oom_byte B /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ ims_dzone ly a /\ ~ ag_dzone ly a;
  (* ReplyImgRowsB.exh_off_B: EXH_OFF_t (YGcfImgRows.v:25 at commit 76362ece943) *)
  uf_EXH_OFF : @cf_exh_off CfImg_B = 68;
  (* ReplyImg_relro.silent_img_B *)
  uf_RELRO_silent : val_mem tfibsegs (fun _ => None) ReplyImg_relro.C_SILENT_B 8 1;
  (* ReplyImg_su_tool.su_tool_B *)
  uf_su_tool : (forall h ch, HS_tfib h = Some ch -> kn_read tfibsegs ch (ELit 0) ReplyImg_su_tool.RB_TOOL_NAME_CELL 8 = Some (ELit ReplyImg_su_tool.RB_TOOL_NAME_STR)) /\ kn_read tfibsegs JS_tfib_band (ELit 0) ReplyImg_su_tool.RB_TOOL_NAME_CELL 8 = Some (ELit ReplyImg_su_tool.RB_TOOL_NAME_STR) /\ (forall k, (k < 17)%nat -> seg_rom tfibsegs (Z_to_bv 64 (ReplyImg_su_tool.RB_TOOL_NAME_STR + Z.of_nat k)) = Some (Z_to_bv 8 (nth k ReplyImg_su_tool.asan_tool_name 0)));
  (* ReplyImg_su_printf.replyB_su_printf *)
  uf_su_printf : (forall s, In s YB01.HS_tfib_list -> In (KWord {| a_base := ELit 0; a_off := ReplyImg_su_printf.replyB_printf_cb_cell |} 8 (ELit ReplyImg_su_printf.replyB_printf_cb_fn)) (s_know (a_ss s))) /\ In (KWord {| a_base := ELit 0; a_off := ReplyImg_su_printf.replyB_printf_cb_cell |} 8 (ELit ReplyImg_su_printf.replyB_printf_cb_fn)) (s_know (a_ss YB03.JS_tfib_band));
  (* ReplyImg_su_syslog.su_syslog_B *)
  uf_su_syslog : forall (ly : alayout), In (z8 (ANum ReplyImg_su_syslog.replyb_log_to_syslog_addr) 0) (@im_const AImg_reply ly);
  (* ReplyImg_su_errb.errb_obj_zero_start *)
  uf_su_errb_obj_zero : ltac:(let t := type of (@ReplyImg_su_errb.errb_obj_zero_start) in exact t);
  (* ReplyImg_su_errb.exh_bytes_zero_start *)
  uf_su_exh_bytes_zero : ltac:(let t := type of (@ReplyImg_su_errb.exh_bytes_zero_start) in exact t)
}.

Theorem reply_unit_facts_B : forall B, TfibSyms B -> ReplyUnitFactsB B.
Proof.
intros B TS.
exact {|
  uf_TS := TS;
  uf_HTSD := YF0m.ts_tsd B TS;
  uf_HOOM := ReplyImg_hoom.hoom_B B TS;
  uf_HERR := ReplyImg_herr.herr_B B TS;
  uf_IMG_COVER := YFiacf.img_cover_of_ledger_cf;
  uf_ErrnoImgCf := ReplyImg_errnoimg.errno_img_cf_B;
  uf_errno_seg_t := ReplyImg_errnoseg.errno_seg_B B TS;
  uf_errno_nstatic_t := ReplyImg_errnonst.errno_nstatic_B;
  uf_errno_apart_dzone_s := fun ly a => ReplyImg_errnoimgs.errno_apart_dzone_s_B B ly a TS;
  uf_errno_apart_shadow_s := fun a => ReplyImg_errnoimgs.errno_apart_shadow_s_B B a TS;
  uf_errno_apart_zone3_s := fun x sz a => ReplyImg_errnoimgs.errno_apart_zone3_s_B B x sz a TS;
  uf_errno_word_cf := ReplyImg_errnoword.errno_word_cf_B B TS;
  uf_HSHB := ReplyImg_hshb.HSHB_B;
  uf_HDZO := ReplyImg_hdzo.hdzo_B B TS;
  uf_HDZX := ReplyImg_hdzx.hdzx_B B TS;
  uf_HCW := ReplyImg_hcw.hcw_B B TS;
  uf_dhash_img := ReplyImg_dhash.dhash_img_B;
  uf_dep_fp_img_ag := ReplyImg_depfp.dep_fp_a_B B TS;
  uf_dep_fp_img_dg := ReplyImg_depfp.dep_fp_d_B B TS;
  uf_dep_keep_img_ag := ReplyImg_depkeep.dep_keep_a_B B TS;
  uf_dep_keep_img_dg := ReplyImg_depkeep.dep_keep_d_B B TS;
  uf_universe_ok := YF0m.ts_universe B TS;
  uf_ag_inst_ok := ReplyImg_instok.inst_ag_B B TS;
  uf_dg_inst_ok := ReplyImg_instok.fm_inst_ok_B B TS;
  uf_INST_CELLS_t := ReplyImg_instcells.inst_cells_B B TS;
  uf_errb_obj_owned_t := ReplyImgRowsB.errb_obj_owned_B B TS;
  uf_ERRB_APART := ReplyImg_errbapart.ERRB_APART_B;
  uf_oom_owned_img := ReplyImg_oomowned.oom_owned_img_B B TS;
  uf_oom_const_img := ReplyImg_oomconst.oom_const_img_B B TS;
  uf_FQ_CONST := ReplyImg_fqconst.FQ_CONST_B B TS;
  uf_SB_CONST := ReplyImg_sbconst.SB_CONST_B;
  uf_CONST_APART := fun ly c => ReplyImg_constapart.CONST_APART_B B ly c TS;
  uf_IMG_QAPART := ReplyImg_qapart.IMG_QAPART_B B TS;
  uf_FV_IAL := ReplyImg_fvzones.fv_ial_img B TS;
  uf_FV_ZONE3 := ReplyImg_fvzones.fv_zone3_img;
  uf_DZONE_OWNED := ReplyImg_fvzones.dzone_owned_img B TS;
  uf_IZONE_OWNED := ReplyImg_fvzones.izone_owned_img B TS;
  uf_COMB_VIS := ReplyImg_vis.comb_vis_B B TS;
  uf_ERRNO_VIS := ReplyImg_vis.errno_vis_B B TS;
  uf_DEP_UNHID := ReplyImg_vis.dep_unhid_B B TS;
  uf_ZONE3 := ReplyImg_zone3.zone3_B;
  uf_CONST_KEEP_S := ReplyImg_zone3.const_keep_s_B B TS;
  uf_CONST_NOT_JUNK := ReplyImg_zone3.const_not_junk_B B TS;
  uf_AREAS_DISJ := ReplyImg_zone3.areas_disj_B B TS;
  uf_IMG_SAPART := ReplyImgRowsB.img_sapart_B B TS;
  uf_IMG_JUNK := fun ly r0 => ReplyImgRowsB.img_junk_B B ly r0 TS;
  uf_ERRB_SEP := conj ReplyImg_errbqapart.ERRB_QAPART_B (fun ly a LY IC HT Ha => proj2 (ReplyImgRowsB.errb_sep_B B TS ly a LY IC HT Ha));
  uf_EXH_OFF := ReplyImgRowsB.exh_off_B;
  uf_RELRO_silent := ReplyImg_relro.silent_img_B;
  uf_su_tool := ReplyImg_su_tool.su_tool_B;
  uf_su_printf := ReplyImg_su_printf.replyB_su_printf;
  uf_su_syslog := fun ly => ReplyImg_su_syslog.su_syslog_B B ly TS;
  uf_su_errb_obj_zero := @ReplyImg_su_errb.errb_obj_zero_start;
  uf_su_exh_bytes_zero := @ReplyImg_su_errb.exh_bytes_zero_start
|}.
Qed.

End u.
