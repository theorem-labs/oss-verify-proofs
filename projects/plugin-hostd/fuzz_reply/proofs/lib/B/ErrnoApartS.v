(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* errno lies apart from the zones the secondary Allocate path frames out (AGif4: sfin, ifs_depot, ifs_post_grant).

   Moved here from ErrnoApart.v, names and statements unchanged: the secondary path's image facts
   [errno_apart_dzone_s] (ims_dzone), [errno_apart_shadow_s] (the shadow map above ImgBaseAGS.SHBv) and
   [errno_apart_zone3_s] (ims_zone3: a granted map), and the lemmas over sfin's and ifs_post_grant's zone expressions:
   errno_apart_wint_s (ImgBaseAGS.WINT), errno_apart_dx (DXz), errno_apart_qr (QRz), errno_apart_blk_s (the block
   [Uv mb, + req_size n)), errno_apart_wini_s (WINI), errno_apart_win_s (WIN).  The family is in one file because
   DXz and QRz are AGif4's, and the secondary arms that use the rest Require AGif4 anyway; ErrnoApart.v's Require
   closure stays free of AGif4 and of the files below.  The frame lines each serves, and the base lemmas they use
   (errno_in_img, errno_apart_stack / _thread / _Q, errno_apart_inst_ag), are in ErrnoApart.v.  The cgif discharges
   of the three Props are in ErrnoApartScgif.v.

   The file is image-free: it takes the image classes as AGif4 does ([Context {IM : AImg} {IMS : AImgS}], and
   {AG : AGImg} for the instance window).

   Require hazard: the Require closure reaches YA08 / YA09 / YA0e through AGif4 (ErrnoApartS -> AGif4 -> YA09, AGif4 ->
   YG0b -> YA08 / YA0e), whose non-local
   Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false) (last at YA08.v:1311, YA09.v:3348,
   YA0e.v:3762) escapes Require: a file that Requires this one has lia's conversion of Z.div / Z.modulo to euclidean
   equations switched off, even when it had switched it on.  Consumer fix, one line after its Require block:
   #[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0b YG0g YG0h YG0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0v YK13 YP0n YA05 YA09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG ImgBaseAGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2 AGif4.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ErrnoApart.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The secondary path (AImgS): sfin (AGif4.v:84-89) and ifs_post_grant's block (AGif4.v:313, :318).                *)
Section s. Context {IMS : AImgS}.

(* Image fact: the secondary walk's depot zone. *)
Definition errno_apart_dzone_s : Prop :=
forall B ly a, im_syms B -> layout_ok ly -> im_img_cover ly -> ims_dzone ly a -> ~ (as_errno B <= a < as_errno B + 4).
(* Image fact: the shadow map, at and above its offset. *)
Definition errno_apart_shadow_s : Prop :=
forall B a, im_syms B -> ImgBaseAGS.SHBv <= a -> ~ (as_errno B <= a < as_errno B + 4).
(* Image fact: an application zone (a kernel grant: AGif4.ifs_apart, AGif4.v:282). *)
Definition errno_apart_zone3_s : Prop :=
forall B x sz a, im_syms B -> ims_zone3 x sz -> x <= a < x + sz -> ~ (as_errno B <= a < as_errno B + 4).

Lemma errno_apart_wint_s : errno_in_img -> forall B ly a, im_syms B -> layout_ok ly -> im_img_cover ly ->
ImgBaseAGS.WINT ly a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI B ly a TS LY IMG Hw. apply (errno_apart_thread HI B ly a TS LY IMG).
unfold ImgBaseAGS.WINT in Hw. unfold kThreadObjSize, t_unwinding in *. lia.
Qed.

(* sfin's depot window DXz (AGif4.v:88). *)
Lemma errno_apart_dx : errno_in_img -> errno_apart_dzone_s -> forall B ly sp0 a, im_syms B -> layout_ok ly ->
im_img_cover ly -> ly_stk_lo ly + ImgBaseAGS.AFSTACK <= sp0 -> DXz ly sp0 a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI HD B ly sp0 a TS LY IMG HSP Hw. unfold DXz in Hw. destruct Hw as [Hw|Hw].
- refine (errno_apart_stack HI B ly _ _ a TS LY IMG _ Hw). unfold ImgBaseAGS.AFSTACK, ImgBaseAGS.DEP_STK in *. lia.
- exact (HD B ly a TS LY IMG Hw).
Qed.

(* sfin's pointer-array commit QRz (grow arm, AGif4.v:88). *)
Lemma errno_apart_qr : errno_in_img -> forall B ly res a, im_syms B -> layout_ok ly -> im_img_cover ly ->
0 <= res -> QRz ly res a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI B ly res a TS LY IMG Hr Hq. apply (errno_apart_Q HI B ly a TS LY IMG). unfold QRz in Hq. lia.
Qed.

(* ifs_post_grant's block [Uv mb, + req_size n) (AGif4.v:313, :318), inside the granted map [mb, mb + MSv n). *)
Lemma errno_apart_blk_s : errno_apart_zone3_s -> forall B n mb a, im_syms B -> ims_zone3 mb (ImgBaseAGS.MSv n) ->
0 <= n -> ImgBaseAGS.Uv mb <= a < ImgBaseAGS.Uv mb + req_size n -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HZ B n mb a TS Hz Hn Ha. apply (HZ B mb (ImgBaseAGS.MSv n) a TS Hz).
assert (RQ : req_size n <= n + 1) by (unfold req_size; destruct (n =? 0); lia).
pose proof (div_bounds_e (n + 7) 8 ltac:(lia)) as D1.
pose proof (div_bounds_e (ImgBaseAGS.NDv n + 4095) 4096 ltac:(lia)) as D2.
unfold ImgBaseAGS.Uv in Ha. unfold ImgBaseAGS.MSv. unfold ImgBaseAGS.NDv, ImgBaseAGS.R8v in *. lia.
Qed.
End s.

(* The secondary path's instance windows (AImgS's geometry, AGImg's instance window). *)
Section gs. Context {AG : AGImg} {IMS : AImgS}.

(* sfin's instance windows WINI (AGif4.v:87 via WIN). *)
Lemma errno_apart_wini_s : errno_apart_inst_ag -> forall B regs0 n a, im_syms B ->
ag_inst_ok (bv_unsigned (getr regs0 11)) -> 0 <= n <= MALLOC_MAX ->
ImgBaseAGS.WINI regs0 n a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HN B regs0 n a TS HO Hn Hw. apply (HN B (bv_unsigned (getr regs0 11)) a TS HO).
unfold MALLOC_MAX in Hn. change (2 ^ 28) with 268435456 in Hn.
pose proof (div_bounds_e (n + 7) 8 ltac:(lia)) as D1.
pose proof (div_bounds_e (ImgBaseAGS.NDv n + 4095) 4096 ltac:(lia)) as D2.
pose proof (div_bounds_e (ImgBaseAGS.MSv n) 4096 ltac:(lia)) as D3.
assert (Hp : ImgBaseAGS.MSv n / 4096 <= 131071).
{ unfold ImgBaseAGS.MSv in *. unfold ImgBaseAGS.NDv, ImgBaseAGS.R8v in *. lia. }
pose proof (Z.log2_le_mono (ImgBaseAGS.MSv n / 4096) 131071 Hp) as L2.
rewrite (eq_refl : Z.log2 131071 = 16) in L2.
pose proof (Z.log2_nonneg (ImgBaseAGS.MSv n / 4096)) as L0.
unfold ImgBaseAGS.WINI, ImgBaseAGS.BSLv, ImgBaseAGS.LGv in Hw.
unfold o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in Hw. lia.
Qed.

(* sfin's window WIN (AGif4.v:87). *)
Lemma errno_apart_win_s : errno_in_img -> errno_apart_shadow_s -> errno_apart_zone3_s -> errno_apart_inst_ag ->
forall B ly regs0 n idx mb a, im_syms B -> layout_ok ly -> im_img_cover ly ->
ly_stk_lo ly + ImgBaseAGS.AFSTACK <= bv_unsigned (getr regs0 2) ->
ag_inst_ok (bv_unsigned (getr regs0 11)) -> 0 <= n <= MALLOC_MAX -> 0 <= idx -> 0 <= mb ->
ims_zone3 mb (ImgBaseAGS.MSv n) ->
ImgBaseAGS.WIN ly regs0 n idx mb a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros HI HS HZ HN B ly regs0 n idx mb a TS LY IMG HSP HO Hn Hidx Hmb Hz Hw.
unfold ImgBaseAGS.WIN in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
- refine (errno_apart_stack HI B ly _ _ a TS LY IMG _ Hw). lia.
- exact (errno_apart_wint_s HI B ly a TS LY IMG Hw).
- exact (errno_apart_wini_s HN B regs0 n a TS HO Hn Hw).
- unfold ImgBaseAGS.WINM in Hw. destruct Hw as [Hw|[Hw|Hw]].
  + apply (errno_apart_Q HI B ly a TS LY IMG). unfold ImgBaseAGS.QSv in Hw. lia.
  + exact (HZ B mb (ImgBaseAGS.MSv n) a TS Hz Hw).
  + apply (HS B a TS). unfold ImgBaseAGS.SMv in Hw. pose proof (Z.div_pos mb 8 Hmb ltac:(lia)). lia.
Qed.
End gs.

End a.
