(* The reply image B twin of cgif's YGcfInstHitcgif.v: the image premises of YGcfInstHit.v (Section b) and the two
   cf rows of YGcfErrbSep.v / YGcfImgRows.v at reply B's instances (CfImg_B, AImg_reply, AGImg_reply, AImgS_reply;
   B with im_syms).  Each holds by the reply image row of the same fact (REPLY-IMG-ROWS.md sha256 a33a582e3ffd; internal record), by name:
   - [hit_hshb_B]        HSHB       ReplyImg_hshb.HSHB_B
   - [hit_hdzo_B]        HDZO       ReplyImg_hdzo.hdzo_B
   - [hit_hdzx_B]        HDZX       ReplyImg_hdzx.hdzx_B
   - [hit_hcw_B]         HCW        ReplyImg_hcw.hcw_B
   - [hit_inst_ag_B]     INST_AG    ReplyImg_instok.inst_ag_B
   - [hit_errb_qapart_B] YGcfImgRows.ERRB_QAPART   ReplyImg_errbqapart.ERRB_QAPART_B
   - [hit_errb_sep_B]    YGcfErrbSep.ERRB_SEP_t    ERRB_QAPART_B and ReplyImgRowsB.errb_sep_B's last four clauses
   - [hit_errb_ag_B]     ERRB_AG    YGcfErrbSep.ERRB_SEP_ag of hit_errb_sep_B
   - [hit_exh_off_B]     YGcfImgRows.EXH_OFF_t     ReplyImgRowsB.exh_off_B
   rule 24: no function proved (instance discharge at reply B from its image rows). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply CfImgB ImgBaseAG ImgBaseAGS AGif0reply AGif4reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfImgRows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfErrbSep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyImg_hshb ReplyImg_hdzo ReplyImg_hdzx ReplyImg_hcw.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyImg_instok ReplyImg_errbqapart ReplyImgRowsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGis ReplyRelroGeoB.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TS : @im_syms AImg_reply B.

Theorem hit_hshb_B : @ag_shadow AImg_reply AGImg_reply = SHADOW_OFF.
Proof. exact ReplyImg_hshb.HSHB_B. Qed.

Theorem hit_hdzo_B : forall ly' a, @ag_dzone AImg_reply AGImg_reply ly' a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
Proof. exact (ReplyImg_hdzo.hdzo_B B TS). Qed.

Theorem hit_hdzx_B : forall ly' a, layout_ok ly' -> @im_img_cover AImg_reply ly' -> @ag_dzone AImg_reply AGImg_reply ly' a ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof. exact (ReplyImg_hdzx.hdzx_B B TS). Qed.

Theorem hit_hcw_B : forall ly' c j cl', layout_ok ly' -> @im_img_cover AImg_reply ly' -> ly_tsd ly' = as_tsd B ->
  In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
  ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j).
Proof. exact (ReplyImg_hcw.hcw_B B TS). Qed.

Theorem hit_inst_ag_B : @ag_inst_ok AImg_reply AGImg_reply (as_inst B).
Proof. exact (ReplyImg_instok.inst_ag_B B TS). Qed.

Theorem hit_errb_qapart_B : YGcfImgRows.ERRB_QAPART (ci := CfImg_B) (IM := AImg_reply).
Proof. exact ReplyImg_errbqapart.ERRB_QAPART_B. Qed.

Theorem hit_errb_sep_B : YGcfErrbSep.ERRB_SEP_t (ci := CfImg_B) (IM := AImg_reply) (AG := AGImg_reply) (IMS := AImgS_reply) B.
Proof.
split; [exact hit_errb_qapart_B|].
intros ly a LY IC HT Ha. exact (proj2 (ReplyImgRowsB.errb_sep_B B TS ly a LY IC HT Ha)).
Qed.

Theorem hit_errb_ag_B : forall ly' a, layout_ok ly' -> @im_img_cover AImg_reply ly' -> ly_tsd ly' = as_tsd B ->
  @ag_dzone AImg_reply AGImg_reply ly' a -> ~ (@cf_errbuf_obj CfImg_B <= a < @cf_errbuf_obj CfImg_B + 56).
Proof. exact (YGcfErrbSep.ERRB_SEP_ag (ci := CfImg_B) (IM := AImg_reply) (AG := AGImg_reply) (IMS := AImgS_reply) B hit_errb_sep_B). Qed.

Theorem hit_exh_off_B : YGcfImgRows.EXH_OFF_t (ci := CfImg_B).
Proof. exact ReplyImgRowsB.exh_off_B. Qed.

(* PF_AG (YGcfInstHit.v's local premise, field round 3) at reply B: the projection of the layer row pf_cells_apart_t
   (reply B's proof ReplyRelroGeoB.pf_cells_apart_reply_B) through reply B's depot zone ag_dzone := AGis.DZONE
   (B/AGis.v:231), whose static part starts at 0x178508 = TFIB_STORE = as_store B (B/YF0m.v:17, ts_store); its node
   and store blocks lie off the image window by lo_disj (static extents 4 / 5 vs 9; ReplyImg_hdzx.static_disj_r),
   which covers the image, and the two cells (0x9fe38 / 0x138350, B/CfImgB.v:74 / :78) lie in it. *)
Theorem hit_pf_ag_B : forall ly' a, layout_ok ly' -> @im_img_cover AImg_reply ly' -> ly_tsd ly' = as_tsd B ->
  @ag_dzone AImg_reply AGImg_reply ly' a ->
  ~ (@cf_toolname_cell CfImg_B <= a < @cf_toolname_cell CfImg_B + 8 \/ @cf_pfcb_cell CfImg_B <= a < @cf_pfcb_cell CfImg_B + 8).
Proof.
intros ly a LY IMG HT Hd Ha.
pose proof TS as TS'. change (TfibSyms B) in TS'.
pose proof (ReplyRelroGeoB.pf_cells_apart_reply_B B TS') as PA. unfold YG0ncf.pf_cells_apart_t in PA.
destruct (PA a Ha) as [LS _]. rewrite (ts_store B TS') in LS. unfold TFIB_STORE in LS.
change (img_cover ly) in IMG. destruct IMG as [I1 I2].
change (AGis.DZONE ly a) in Hd. unfold AGis.DZONE in Hd.
destruct Hd as [Hs|Hb]; [lia|].
pose proof (ReplyImg_hdzx.static_disj_r ly LY 4 9 _ _ eq_refl eq_refl ltac:(lia)) as D4.
pose proof (ReplyImg_hdzx.static_disj_r ly LY 5 9 _ _ eq_refl eq_refl ltac:(lia)) as D5.
unfold zdisjoint in D4, D5. cbn [fst snd] in D4, D5.
cbn [cf_toolname_cell cf_pfcb_cell CfImg_B] in Ha. unfold TFIB_IMG_LO, TFIB_IMG_END in *. lia.
Qed.
End a.
