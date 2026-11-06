(* The reply image A discharges of 11 of the cf layer's YGcfInstSec.v Section b rows (part B; the image-A twin of
   cgif's YGcfInstSeccgifB.v): each lemma states the row's text at reply's image-A instances (A/AGif2reply.v
   AImg_reply, A/AGif0reply.v AGImg_reply, A/AGif4reply.v AImgS_reply), with `forall B, @im_syms AImg_reply B ->` in
   front where the text names B, so the layer's hypothesis takes it by conversion.
   rule 24: no function proved (image rows: closed facts over reply A's segments, symbol table and class fields). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply ImgBaseAGS AGif4reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YM03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AGif0reply AGjm AGis AGhy AFib CLdepot YGcfInstDepot.
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
Lemma SYM_TSD_A : forall B, @im_syms AImg_reply B -> as_tsd B = im_tsd.
Proof. intros B TS. change (TfibSyms B) in TS. exact (ts_tsd B TS). Qed.

(* SHB_EQ (YGcfInstSec.v:1679): AImgS_reply's shadow base AGjm.SHBv = 0x7fff8000 = SHADOW_OFF. *)
Lemma SHB_EQ_A : ImgBaseAGS.SHBv = SHADOW_OFF.
Proof. reflexivity. Qed.

(* WFRAME_SP (YGcfInstSec.v:765): the first conjunct of AGif0reply.wframe (its AFSTACK, AGhy.AFSTACK, is 4096, as
   ImgBaseAGS's). *)
Lemma WFRAME_SP_A : forall W ly regs0 mem0 tr, ims_wframe W ly regs0 mem0 tr ->
  ly_stk_lo ly + ImgBaseAGS.AFSTACK <= bv_unsigned (getr regs0 2) <= ly_stk_hi ly.
Proof.
intros W ly regs0 mem0 tr H. change (AGif0reply.wframe W ly regs0 mem0 tr) in H. destruct H as ((H1 & _ & H3 & _) & _).
unfold ImgBaseAGS.AFSTACK. unfold AGhy.AFSTACK in H1. zl.
Qed.

(* DEP_FP (YGcfInstSec.v:389): what StackDepotPut writes is in AGjm.DZONE: the depot table [0x187f98, + d_map1 +
   8 * 32768) and its store [0x177f88, + 64) lie in DZONE's image range [0x177f88, 0x5c8710). *)
Lemma DEP_FP_A : forall B, @im_syms AImg_reply B -> YGcfInstDepot.dep_fp_img B ims_dzone.
Proof.
intros B TS ly a _ _ _ FP. change (TfibSyms B) in TS. change (AGjm.DZONE ly a).
unfold CLdepot.depot_footprint, AGjm.DZONE in *. rewrite (ts_depot B TS), (ts_store B TS) in FP.
unfold TFIB_DEPOT, TFIB_STORE, d_map1 in FP. zl.
Qed.

(* DZ_LOC (YGcfInstSec.v:1682): AGjm.DZONE's image part [0x177f88, 0x5c8710) is in the image window and above the
   instance object (0xa2a58 + 3632), the internal allocator [0xa72c0, 0x1282f0) and its flag (0x135b48 + 2). *)
Lemma DZ_LOC_A : forall B, @im_syms AImg_reply B -> forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  ims_dzone ly a ->
  (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) \/
  (in_zr a (ly_img ly) /\ ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\
   ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2)).
Proof.
intros B TS ly a _ IMG _ Hd. change (TfibSyms B) in TS. change (img_cover ly) in IMG. change (AGjm.DZONE ly a) in Hd.
destruct IMG as [I1 I2].
unfold AGjm.DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]]; [|left; exact Hd|right; left; exact Hd].
right; right. rewrite (ts_inst B TS), (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS).
unfold in_zr, TFIB_INST, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END in *.
split; [zl | split; [zl | split; zl]].
Qed.

Lemma zr_dec_A : forall lo hi a : Z, (lo <= a < hi) \/ ~ (lo <= a < hi).
Proof. intros lo hi a. zl. Qed.

(* DZ_DEC (YGcfInstSec.v:1687): AGjm.DZONE is three integer ranges. *)
Lemma DZ_DEC_A : forall ly a, ims_dzone ly a \/ ~ ims_dzone ly a.
Proof.
intros ly a. change (AGjm.DZONE ly a \/ ~ AGjm.DZONE ly a). unfold AGjm.DZONE.
destruct (zr_dec_A 0x177f88 0x5c8710 a); [left; left; assumption|].
destruct (zr_dec_A (ly_NB ly) (ly_NB ly + kNodesBlockSize) a); [left; right; left; assumption|].
destruct (zr_dec_A (ly_SB ly) (ly_SB ly + kStoreBlockSize) a); [left; right; right; assumption|].
right. tauto.
Qed.

(* DZ_OWN (YGcfInstSec.v:1706): an image byte of AGjm.DZONE is in Tfib_owned_static's (0xa5910, 0x5c8710 - 0xa5910)
   entry; the node and store blocks (static extents 4 and 5) are apart from the image window (extent 9, lo_disj). *)
Lemma DZ_OWN_A : forall B, @im_syms AImg_reply B -> forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
  ims_dzone ly a -> in_zr a (ly_img ly) -> Exists (in_zr a) (as_owned_static B).
Proof.
intros B TS ly a LY _ _ Hd Hi. change (TfibSyms B) in TS. change (AGjm.DZONE ly a) in Hd. unfold AGjm.DZONE in Hd.
pose proof (lo_disj ly LY) as HD.
pose proof (AGis.pairwise_ij _ _ 4 4 _ _ HD eq_refl eq_refl) as DNB.
pose proof (AGis.pairwise_ij _ _ 5 3 _ _ HD eq_refl eq_refl) as DSB.
unfold zdisjoint, in_zr in DNB, DSB, Hi. cbn [fst snd] in DNB, DSB.
rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
exists (0xa5910, 0x5c8710 - 0xa5910). split; [cbn; tauto|]. unfold in_zr. cbn [fst snd].
destruct Hd as [Hd|[Hd|Hd]]; zl.
Qed.

(* CONST_LY (YGcfInstSec.v:1690) *)
Lemma CONST_LY_A : forall B, @im_syms AImg_reply B -> forall ly1 ly2, as_const B ly1 = as_const B ly2.
Proof. intros B TS ly1 ly2. change (TfibSyms B) in TS. rewrite !(ts_const B TS). reflexivity. Qed.

(* CONST_LT (YGcfInstSec.v:1691) *)
Lemma CONST_LT_A : forall B, @im_syms AImg_reply B -> forall ly nn, Forall (AFib.cell_lt nn) (as_const B ly).
Proof.
intros B TS ly nn. change (TfibSyms B) in TS. rewrite (ts_const B TS ly). clear.
unfold Tfib_const, Tfib_const_sym, Tfib_const_abs, Tfib_const_shadow. cbn [app].
repeat (apply Forall_cons; [exact (conj I I)|]). apply Forall_nil.
Qed.

(* JUNK_LY (YGcfInstSec.v:1692) *)
Lemma JUNK_LY_A : forall B, @im_syms AImg_reply B -> forall ly1 ly2, as_junk B ly1 = as_junk B ly2.
Proof. intros B TS ly1 ly2. change (TfibSyms B) in TS. exact (ts_junk_ly B TS ly2 ly1). Qed.

(* JUNK_LT (YGcfInstSec.v:1693) *)
Lemma JUNK_LT_A : forall B, @im_syms AImg_reply B -> forall ly nn,
  Forall (fun r => AFib.asec_lt nn (fst r)) (as_junk B ly).
Proof.
intros B TS ly nn. change (TfibSyms B) in TS. apply Forall_forall. intros r Hr.
destruct (ts_junk B TS ly r Hr) as (zz & -> & _). exact I.
Qed.

End a.
