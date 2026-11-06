(* The reply image A twin of cgif's YGcfInstHitcgif.v: the image premises of YGcfInstHit.v (Section b) and the two
   cf rows of YGcfErrbSep.v / YGcfImgRows.v at reply A's instances (CfImg_A, AImg_reply, AGImg_reply, AImgS_reply;
   B with im_syms).  Each holds by the reply image row of the same fact (REPLY-IMG-ROWS.md sha256 a33a582e3ffd; internal record), by name:
   - [hit_hshb_A]        HSHB       ReplyImg_hshb.HSHB_A
   - [hit_hdzo_A]        HDZO       ReplyImg_hdzo.hdzo_A
   - [hit_hdzx_A]        HDZX       ReplyImg_hdzx.hdzx_A
   - [hit_hcw_A]         HCW        ReplyImg_hcw.hcw_A
   - [hit_inst_ag_A]     INST_AG    ReplyImg_instok.inst_ag_A
   - [hit_errb_qapart_A] YGcfImgRows.ERRB_QAPART   ReplyImg_errbqapart.ERRB_QAPART_A
   - [hit_errb_sep_A]    YGcfErrbSep.ERRB_SEP_t    ERRB_QAPART_A and ReplyImgRowsA.errb_sep_A's last four clauses
   - [hit_errb_ag_A]     ERRB_AG    YGcfErrbSep.ERRB_SEP_ag of hit_errb_sep_A
   - [hit_exh_off_A]     YGcfImgRows.EXH_OFF_t     ReplyImgRowsA.exh_off_A
   rule 24: no function proved (instance discharge at reply A from its image rows). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply CfImgA ImgBaseAG ImgBaseAGS AGif0reply AGif4reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfImgRows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfErrbSep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyImg_hshb ReplyImg_hdzo ReplyImg_hdzx ReplyImg_hcw.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyImg_instok ReplyImg_errbqapart ReplyImgRowsA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AGis ReplyRelroGeoA.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TS : @im_syms AImg_reply B.

Theorem hit_hshb_A : @ag_shadow AImg_reply AGImg_reply = SHADOW_OFF.
Proof. exact ReplyImg_hshb.HSHB_A. Qed.

Theorem hit_hdzo_A : forall ly' a, @ag_dzone AImg_reply AGImg_reply ly' a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
Proof. exact (ReplyImg_hdzo.hdzo_A B TS). Qed.

Theorem hit_hdzx_A : forall ly' a, layout_ok ly' -> @im_img_cover AImg_reply ly' -> @ag_dzone AImg_reply AGImg_reply ly' a ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
Proof. exact (ReplyImg_hdzx.hdzx_A B TS). Qed.

Theorem hit_hcw_A : forall ly' c j cl', layout_ok ly' -> @im_img_cover AImg_reply ly' -> ly_tsd ly' = as_tsd B ->
  In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
  ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j).
Proof. exact (ReplyImg_hcw.hcw_A B TS). Qed.

Theorem hit_inst_ag_A : @ag_inst_ok AImg_reply AGImg_reply (as_inst B).
Proof. exact (ReplyImg_instok.inst_ag_A B TS). Qed.

Theorem hit_errb_qapart_A : YGcfImgRows.ERRB_QAPART (ci := CfImg_A) (IM := AImg_reply).
Proof. exact ReplyImg_errbqapart.ERRB_QAPART_A. Qed.

Theorem hit_errb_sep_A : YGcfErrbSep.ERRB_SEP_t (ci := CfImg_A) (IM := AImg_reply) (AG := AGImg_reply) (IMS := AImgS_reply) B.
Proof.
split; [exact hit_errb_qapart_A|].
intros ly a LY IC HT Ha. exact (proj2 (ReplyImgRowsA.errb_sep_A B TS ly a LY IC HT Ha)).
Qed.

Theorem hit_errb_ag_A : forall ly' a, layout_ok ly' -> @im_img_cover AImg_reply ly' -> ly_tsd ly' = as_tsd B ->
  @ag_dzone AImg_reply AGImg_reply ly' a -> ~ (@cf_errbuf_obj CfImg_A <= a < @cf_errbuf_obj CfImg_A + 56).
Proof. exact (YGcfErrbSep.ERRB_SEP_ag (ci := CfImg_A) (IM := AImg_reply) (AG := AGImg_reply) (IMS := AImgS_reply) B hit_errb_sep_A). Qed.

Theorem hit_exh_off_A : YGcfImgRows.EXH_OFF_t (ci := CfImg_A).
Proof. exact ReplyImgRowsA.exh_off_A. Qed.

(* PF_AG (YGcfInstHit.v's local premise, field round 3) at reply A: the projection of the layer row pf_cells_apart_t
   (reply A's proof ReplyRelroGeoA.pf_cells_apart_reply_A) through reply A's depot zone ag_dzone := AGis.DZONE
   (A/AGis.v:230), whose static part starts at 0x177f88 = TFIB_STORE = as_store B (A/AF0m.v:18, ts_store); its node
   and store blocks lie off the image window (ReplyImg_hdzx.hdzx_blocks_off_img_A), and the two cells (0x9f8b8 /
   0x137dd0, A/CfImgA.v:74 / :78) lie in it. *)
Theorem hit_pf_ag_A : forall ly' a, layout_ok ly' -> @im_img_cover AImg_reply ly' -> ly_tsd ly' = as_tsd B ->
  @ag_dzone AImg_reply AGImg_reply ly' a ->
  ~ (@cf_toolname_cell CfImg_A <= a < @cf_toolname_cell CfImg_A + 8 \/ @cf_pfcb_cell CfImg_A <= a < @cf_pfcb_cell CfImg_A + 8).
Proof.
intros ly a LY IMG HT Hd Ha.
pose proof TS as TS'. change (TfibSyms B) in TS'.
pose proof (ReplyRelroGeoA.pf_cells_apart_reply_A B TS') as PA. unfold YG0ncf.pf_cells_apart_t in PA.
destruct (PA a Ha) as [LS _]. rewrite (ts_store B TS') in LS. unfold TFIB_STORE in LS.
change (img_cover ly) in IMG.
change (AGis.DZONE ly a) in Hd. unfold AGis.DZONE in Hd.
destruct Hd as [Hs|Hb]; [lia|].
pose proof (ReplyImg_hdzx.hdzx_blocks_off_img_A ly LY IMG a Hb) as Off.
cbn [cf_toolname_cell cf_pfcb_cell CfImg_A] in Ha. unfold TFIB_IMG_LO, TFIB_IMG_END in Off. lia.
Qed.
End a.
