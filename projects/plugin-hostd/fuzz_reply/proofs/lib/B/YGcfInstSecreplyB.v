(* The reply image B discharges of 11 of the cf layer's YGcfInstSec.v Section b rows (part B; the image-B twin of
   lib/A/YGcfInstSecreplyB.v and of cgif's YGcfInstSeccgifB.v): each lemma states the row's text at reply's image-B instances (B/AGif2reply.v
   AImg_reply, B/AGif0reply.v AGImg_reply, B/AGif4reply.v AImgS_reply), with `forall B, @im_syms AImg_reply B ->` in
   front where the text names B, so the layer's hypothesis takes it by conversion.
   rule 24: no function proved (image rows: closed facts over reply B's segments, symbol table and class fields). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply ImgBaseAGS AGif4reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YM03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGif0reply AGjm AGis AGhy CLdepot YGcfInstDepot YFib.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyImg_depfp ReplyImg_hdzo ReplyImg_hdzx.
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* plain linear arithmetic: this lib's lia is YM05's *)
Local Ltac zl := YM03.lf_lia_orig.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* SYM_TSD (YGcfInstSec.v:368): the symbol table's TSD is the image class's (TfibSyms.ts_tsd). *)
Lemma SYM_TSD_B : forall B, @im_syms AImg_reply B -> as_tsd B = im_tsd.
Proof. intros B TS. change (TfibSyms B) in TS. exact (ts_tsd B TS). Qed.

(* SHB_EQ (YGcfInstSec.v:1679): AImgS_reply's shadow base AGjm.SHBv = 0x7fff8000 = SHADOW_OFF. *)
Lemma SHB_EQ_B : ImgBaseAGS.SHBv = SHADOW_OFF.
Proof. reflexivity. Qed.

(* WFRAME_SP (YGcfInstSec.v:765): the first conjunct of AGif0reply.wframe (its AFSTACK, AGhy.AFSTACK, is 4096, as
   ImgBaseAGS's). *)
Lemma WFRAME_SP_B : forall W ly regs0 mem0 tr, ims_wframe W ly regs0 mem0 tr ->
  ly_stk_lo ly + ImgBaseAGS.AFSTACK <= bv_unsigned (getr regs0 2) <= ly_stk_hi ly.
Proof.
intros W ly regs0 mem0 tr H. change (AGif0reply.wframe W ly regs0 mem0 tr) in H. destruct H as ((H1 & _ & H3 & _) & _).
unfold ImgBaseAGS.AFSTACK. unfold AGhy.AFSTACK in H1. zl.
Qed.

(* DEP_FP (YGcfInstSec.v:389): ReplyImg_depfp.dep_fp_a_B, which is at ag_dzone = AGis.DZONE; ims_dzone is AGjm.DZONE,
   the same body (B/AGis.v:231-232, B/AGjm.v:573-574), so the proof is a conversion. *)
Lemma DEP_FP_B : forall B, @im_syms AImg_reply B -> YGcfInstDepot.dep_fp_img B ims_dzone.
Proof.
intros B TS ly a LY IMG TSD FP. change (TfibSyms B) in TS. change (AGjm.DZONE ly a).
exact (ReplyImg_depfp.dep_fp_a_B B TS ly a LY IMG TSD FP).
Qed.

(* DZ_LOC (YGcfInstSec.v:1682): the block cases are DZONE's second and third disjuncts; for the image part, the three
   exclusions are ReplyImg_hdzx.hdzx_B (its ag_dzone, AGis.DZONE, is AGjm.DZONE by conversion) and the byte is in the image window
   by img_cover (the image part lies in [TFIB_IMG_LO, TFIB_IMG_END)). *)
Lemma DZ_LOC_B : forall B, @im_syms AImg_reply B -> forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  ims_dzone ly a ->
  (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) \/
  (in_zr a (ly_img ly) /\ ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
   ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2)).
Proof.
intros B TS ly a LY IMG _ Hd. change (AGjm.DZONE ly a) in Hd.
pose proof (ReplyImg_hdzx.hdzx_B B TS ly a LY IMG Hd) as X.
change (img_cover ly) in IMG. destruct IMG as [I1 I2].
unfold AGjm.DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]]; [|left; exact Hd|right; left; exact Hd].
right; right. split; [|exact X].
unfold in_zr, TFIB_IMG_LO, TFIB_IMG_END in *. zl.
Qed.

Lemma zr_dec_B : forall lo hi a : Z, (lo <= a < hi) \/ ~ (lo <= a < hi).
Proof. intros lo hi a. zl. Qed.

(* DZ_DEC (YGcfInstSec.v:1687): AGjm.DZONE is three integer ranges, each decided by zr_dec_B. *)
Lemma DZ_DEC_B : forall ly a, ims_dzone ly a \/ ~ ims_dzone ly a.
Proof.
intros ly a. change (AGjm.DZONE ly a \/ ~ AGjm.DZONE ly a). unfold AGjm.DZONE.
match goal with |- (?l1 <= a < ?h1 \/ ?l2 <= a < ?h2 \/ ?l3 <= a < ?h3) \/ _ =>
  destruct (zr_dec_B l1 h1 a), (zr_dec_B l2 h2 a), (zr_dec_B l3 h3 a); tauto end.
Qed.

(* DZ_OWN (YGcfInstSec.v:1706): ReplyImg_hdzo.hdzo_B gives the owned-static entry or one of the depot's two blocks;
   the blocks (static extents 4 and 5) are apart from the image window (extent 9, lo_disj), which holds a. *)
Lemma DZ_OWN_B : forall B, @im_syms AImg_reply B -> forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  ims_dzone ly a -> in_zr a (ly_img ly) -> Exists (in_zr a) (as_owned_static B).
Proof.
intros B TS ly a LY _ _ Hd Hi. change (AGjm.DZONE ly a) in Hd.
destruct (ReplyImg_hdzo.hdzo_B B TS ly a Hd) as [E|Hb]; [exact E|exfalso].
pose proof (lo_disj ly LY) as HD.
pose proof (AGis.pairwise_ij _ _ 4 4 _ _ HD eq_refl eq_refl) as DNB.
pose proof (AGis.pairwise_ij _ _ 5 3 _ _ HD eq_refl eq_refl) as DSB.
unfold zdisjoint, in_zr in DNB, DSB, Hi. cbn [fst snd] in DNB, DSB.
destruct Hb as [Hb|Hb]; zl.
Qed.

(* CONST_LY (YGcfInstSec.v:1690) *)
Lemma CONST_LY_B : forall B, @im_syms AImg_reply B -> forall ly1 ly2, as_const B ly1 = as_const B ly2.
Proof. intros B TS ly1 ly2. change (TfibSyms B) in TS. rewrite !(ts_const B TS). reflexivity. Qed.

(* CONST_LT (YGcfInstSec.v:1691) *)
Lemma CONST_LT_B : forall B, @im_syms AImg_reply B -> forall ly nn, Forall (YFib.cell_lt nn) (as_const B ly).
Proof.
intros B TS ly nn. change (TfibSyms B) in TS. rewrite (ts_const B TS ly). clear.
unfold Tfib_const, Tfib_const_sym, Tfib_const_abs, Tfib_const_shadow. cbn [app].
repeat (apply Forall_cons; [exact (conj I I)|]). apply Forall_nil.
Qed.

(* JUNK_LY (YGcfInstSec.v:1692) *)
Lemma JUNK_LY_B : forall B, @im_syms AImg_reply B -> forall ly1 ly2, as_junk B ly1 = as_junk B ly2.
Proof. intros B TS ly1 ly2. change (TfibSyms B) in TS. exact (ts_junk_ly B TS ly2 ly1). Qed.

(* JUNK_LT (YGcfInstSec.v:1693) *)
Lemma JUNK_LT_B : forall B, @im_syms AImg_reply B -> forall ly nn, Forall (fun r => YFib.asec_lt nn (fst r)) (as_junk B ly).
Proof.
intros B TS ly nn. change (TfibSyms B) in TS. apply Forall_forall. intros r Hr.
destruct (ts_junk B TS ly r Hr) as (zz & -> & _). exact I.
Qed.

End a.
