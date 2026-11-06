(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (lane M of the generic cf instance layer, CfInstSec; integrator ReallocPrimary).
   The reply image B twin of lib/A/YGcfInstSecreply.v: YGcfInstSec.v's three secondary Allocate interfaces
   (ifaceS_cf / ifaceSw_cf / ifaceSE_cf) at reply B's image classes (CfImg_B, AImg_reply, AGImg_reply, AImgS_reply of
   lib/B), with every image row of YGcfInstSec.v's Section b discharged:
   - by the reply image row of the same fact, by name (REPLY-IMG-ROWS.md sha256 a33a582e3ffd; internal record): SYM_OOM hoom_B, SYM_ERRNO herr_B,
     INST_AG inst_ag_B, INST_CELLS inst_cells_B, COMB_VIS / ERRNO_VIS / DEP_UNHID comb_vis_B / errno_vis_B /
     dep_unhid_B, ZONE3 zone3_B, CONST_KEEP_S const_keep_s_B, ERR_SEG errno_seg_B,
     EDZ / ESH / EZ3 errno_apart_*_s_B, EIMG / EUNH / EINST ErrnoApartreply's errno_in_img_reply /
     errno_unhidden_reply / errno_apart_inst_ag_reply, ERRB_SEP CfInstHit's hit_errb_sep_B, HD CfF1's
     depot_spec_a_reply;
   - by a Theorem Labs lane's lib/B/YGcfInstSecreplyB.v: SYM_TSD, SHB_EQ, WFRAME_SP, DEP_FP, DZ_LOC, DZ_DEC, DZ_OWN, CONST_LY,
     CONST_LT, JUNK_LY, JUNK_LT;
   - here: CONST_APART (CONST_APART_B, a table scan: no const byte in the secondary walk's written words gwj),
     CONST_NOT_JUNK (CONST_NOT_JUNK_B, at every CfParams; reply B's row const_not_junk_B is at CfParams_reply),
     AREAS_DISJ (the first six areas, from areas_disj_B over all of them), ERR_NST (errno_nstatic_B at TfibB, moved to
     any B with TfibSyms) and PF_SEP (the projection of the layer row pf_cells_apart_t, reply B's
     ReplyRelroGeoB.pf_cells_apart_reply_B, and CfInstHit's hit_pf_ag_B: reply B's ims_dzone AGjm.DZONE and ag_dzone
     AGis.DZONE are the same three ranges).
   What stays a premise: the symbol table (@im_syms AImg_reply B), the unit's IOK, the ledger's image window
   (YGcfDIface.IMG_COVER) and the depot hash (as_dhash B = tfib_dhash; at B := TfibB it is ReplyImg_dhash's row).
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply CfImgB ImgBaseAG ImgBaseAGS AGif0reply AGif4reply AGif4.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YM03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGjm AGis ErrnoGS ErrnoApart ErrnoApartS ErrnoApartreply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfDIface YGcfInstErrno YGcfErrbSep YGcfInstDepotWreply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyImg_hoom ReplyImg_herr ReplyImg_instok ReplyImg_instcells.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyImg_vis ReplyImg_zone3 ReplyImg_errnoseg ReplyImg_errnonst.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyImg_errnoimgs ReplyRelroGeoB YGcfInstHitreply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfInstSec YGcfInstSecreplyB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00cf YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfRmodel YGcfInstBase YGcfInstHit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfAbudget YF0p.
(* stdpp, through the LPS modules, shadows several list names; the list lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Ltac zl := YM03.lf_lia_orig.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* CONST_APART's table scan: each absolute cell of Tfib_const lies in the image apart from the secondary walk's written
   instance words (the reserved / count / sorted words, the stats words, the by_size_log words a request below 2 ^ 30
   can select, the mutex's first byte, the combined stats), or in the band between the low shadow's start and the high
   memory. *)
Definition gwj_ok (c : acell) : bool :=
match c_at c with
| ANum a => let e := a + Z.max 1 (Z.of_nat (c_w c)) in
  ((TFIB_IMG_LO <=? a) && (e <=? TFIB_IMG_END) &&
   ((e <=? TFIB_INST + o_sec_reserved) || (TFIB_INST + o_sec_sorted + 1 <=? a)) &&
   ((e <=? TFIB_INST + o_sec_stats) || (TFIB_INST + o_sec_stats + 32 <=? a)) &&
   ((e <=? TFIB_INST + 296) || (TFIB_INST + 416 <=? a)) &&
   ((e <=? TFIB_INST + o_sec_mutex) || (TFIB_INST + o_sec_mutex + 1 <=? a)) &&
   ((e <=? TFIB_INST + o_comb_stats) || (TFIB_INST + o_comb_stats + 40 <=? a)))
  || ((kLowShadowBeg <=? a) && (e <=? kHighMemBeg))
| _ => false
end.
Lemma gwj_oks : forallb gwj_ok (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.

(* A pairwise fact of a list holds of its prefixes. *)
Lemma pairwise_firstn {X : Type} (R : X -> X -> Prop) : forall n l, pairwise R l -> pairwise R (firstn n l).
Proof.
induction n as [|n IH]; intros l H; [cbn; exact I|]. destruct l as [|x t]; [cbn; exact I|].
cbn [firstn pairwise] in *. destruct H as [F P]. split; [|exact (IH t P)].
apply Forall_forall. intros y Hy. apply (proj1 (Forall_forall _ _) F).
rewrite <- (firstn_skipn n t). apply in_or_app. left. exact Hy.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Section c.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

(* Q / T / C / D are owned extents: apart from the image window (owned_not_img and img_cover) and from the shadow band
   (layout_ok's lo_app). *)
Lemma own_off_img_B : forall ly, layout_ok ly -> img_cover ly ->
  forall e a, In e [(ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize); (ly_C ly, 256); (ly_D ly, 4096)] ->
  fst e <= a < fst e + snd e -> ~ (TFIB_IMG_LO <= a < TFIB_IMG_END) /\ ~ (kLowShadowBeg <= a < kHighMemBeg).
Proof.
intros ly LY [I1 I2] e a He Ha.
assert (EO : In e (owned_extents ly)) by (unfold owned_extents; cbn in He |- *; tauto).
pose proof (YGcfInstSec.owned_not_img ly e a LY EO ltac:(unfold in_zr; exact Ha)) as NI.
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) e EO) as A.
unfold in_zr, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, TFIB_IMG_LO, TFIB_IMG_END in *. cbn [fst snd] in *. zl.
Qed.

(* CONST_APART (YGcfInstSec.v Section b) at reply B: no const byte is in the secondary walk's written words. *)
Lemma CONST_APART_B : forall ly c k, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> In c (as_const B ly) ->
  0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> ~ YGcfInstSec.gwj B ly (aeval B ly (c_at c) + k).
Proof.
intros ly c k LY IMGC HTSD Hin Hk. change (img_cover ly) in IMGC. rewrite (ts_tsd B TS) in HTSD.
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN.
unfold YGcfInstSec.gwj. rewrite EIN.
pose proof (fun a => own_off_img_B ly LY IMGC (ly_Q ly, kPtrArrayResv) a ltac:(cbn; tauto)) as OQ.
pose proof (fun a => own_off_img_B ly LY IMGC (ly_T ly, kThreadObjSize) a ltac:(cbn; tauto)) as OT.
pose proof (fun a => own_off_img_B ly LY IMGC (ly_C ly, 256) a ltac:(cbn; tauto)) as OC.
pose proof (fun a => own_off_img_B ly LY IMGC (ly_D ly, 4096) a ltac:(cbn; tauto)) as OD.
cbn [fst snd] in OQ, OT, OC, OD.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 1 0 _ _ (lo_disj ly LY) eq_refl eq_refl) as DQT.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 1 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as DQC.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 1 5 _ _ (lo_disj ly LY) eq_refl eq_refl) as DQD.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 2 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as DTC.
pose proof (YGcfInstSec.pw_ij zdisjoint (static_extents ly) 2 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as DTD.
unfold zdisjoint in DQT, DQC, DQD, DTC, DTD. cbn [fst snd] in DQT, DQC, DQD, DTC, DTD.
rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfib_const_sym in Hin. cbn [In] in Hin.
  repeat match type of Hin with
  | _ \/ _ => destruct Hin as [<-|Hin];
      [cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?HTSD;
       match goal with |- ~ ((_ <= ?x < _) \/ _) =>
         pose proof (OQ x) as Q1; pose proof (OT x) as T1; pose proof (OC x) as C1; pose proof (OD x) as D1 end;
       unfold TFIB_TP, TFIB_INST, TFIB_TSD, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize,
         kPtrArrayResv, kPtrArrayEntriesPerCommit, o_space, o_rinfo, o_sec_chunks, o_sec_reserved, o_sec_sorted,
         o_sec_stats, o_sec_mutex, o_comb_stats in *;
       zl |]
  | False => destruct Hin
  end.
- pose proof (proj1 (forallb_forall _ _) gwj_oks c Hin) as Hc. unfold gwj_ok in Hc.
  destruct (c_at c) eqn:Ea; try discriminate Hc. cbn [aeval]. cbv zeta in Hc.
  rewrite Bool.orb_true_iff, !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in Hc.
  pose proof (OQ (z + k)) as Q1. pose proof (OT (z + k)) as T1.
  clear OQ OT OC OD DQC DQD DTC DTD.
  unfold TFIB_INST, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize, kPtrArrayResv,
    kPtrArrayEntriesPerCommit, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *.
  zl.
Qed.

(* ERR_NST (YGcfInstErrno.errno_nstatic_t) at any B with TfibSyms: reply B's row errno_nstatic_B is stated at
   TfibB, and both read the same two table entries (ts_errno, ts_owned). *)
Lemma ERR_NST_B : YGcfInstErrno.errno_nstatic_t B.
Proof.
intros a Ha. rewrite (ts_errno B TS) in Ha. rewrite (ts_owned B TS).
pose proof (ReplyImg_errnonst.errno_nstatic_B a) as X.
rewrite (ts_errno _ TfibB_syms), (ts_owned _ TfibB_syms) in X. exact (X Ha).
Qed.

(* CONST_NOT_JUNK (YGcfInstSec.v Section b) at reply B for EVERY CfParams.  Reply B's row const_not_junk_B is stated
   at CfParams_reply only (its by_size_log word below inst + 408); here the request bound of any CfParams
   (YG08cf.cf_malloc_max_bound: n < 2 ^ 30) puts that word in [inst + 296, inst + 416) (ReplyImg_zone3.bsl_bounds),
   and CONST_APART_B already keeps every const byte out of it, out of the thread object's tail and out of the
   instance's sorted / stats / combined-stats words; the oom byte is image B's TFIB_OOM inside the image, and
   ReplyImg_zone3.const_loc_B places a const byte either in the image apart from it or off the image. *)
Lemma CONST_NOT_JUNK_B {cp : CfParams} : forall ly (regs0 : bvmap 5 word) n c k, layout_ok ly -> im_img_cover ly ->
  ly_tsd ly = as_tsd B -> bv_unsigned (getr regs0 11) = as_inst B -> 64513 <= n < cf_malloc_max ->
  In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
  ~ YGcfInstSec.snull_junk B ly regs0 n (aeval B ly (c_at c) + k).
Proof.
intros ly regs0 n c k LY IMGC HTSD Hinst Hn Hin Hk.
pose proof (CONST_APART_B ly c k LY IMGC HTSD Hin Hk) as G. unfold YGcfInstSec.gwj in G.
pose proof (ReplyImg_zone3.const_loc_B B ly TS HTSD c Hin k Hk) as L. unfold ReplyImg_zone3.const_loc in L.
pose proof (@YG08cf.cf_malloc_max_bound cp) as CB.
pose proof (ReplyImg_zone3.bsl_bounds regs0 n ltac:(zl)) as BS. rewrite Hinst in BS.
change (img_cover ly) in IMGC.
pose proof (own_off_img_B ly LY IMGC (ly_T ly, kThreadObjSize) (aeval B ly (c_at c) + k) ltac:(cbn; tauto)) as OT.
pose proof (own_off_img_B ly LY IMGC (ly_C ly, 256) (aeval B ly (c_at c) + k) ltac:(cbn; tauto)) as OC.
pose proof (own_off_img_B ly LY IMGC (ly_D ly, 4096) (aeval B ly (c_at c) + k) ltac:(cbn; tauto)) as OD.
cbn [fst snd] in OT, OC, OD.
unfold YGcfInstSec.snull_junk. rewrite (ts_inst B TS) in BS, G |- *. rewrite (ts_oom B TS).
set (a := aeval B ly (c_at c) + k) in *. clearbody a.
unfold AGjm.SHBv, TFIB_INST, TFIB_OOM, TFIB_IMG_LO, TFIB_IMG_END, o_sec_reserved, o_sec_sorted, o_sec_stats,
  o_sec_mutex, o_comb_stats, kThreadObjSize, kLowShadowBeg, kHighMemBeg in *.
zl.
Qed.
End c.

(* AREAS_DISJ (YGcfInstSec.v Section b): the first six areas, from reply B's row over all of them. *)
Lemma AREAS_DISJ_B : forall B, @im_syms AImg_reply B -> pairwise zdisjoint (firstn 6 (asyms_areas B)).
Proof. intros B TS. exact (pairwise_firstn zdisjoint 6 _ (ReplyImg_zone3.areas_disj_B B TS)). Qed.

(* PF_SEP (YGcfInstSec.v Section a, Definition PF_SEP_t) at reply B: the oom byte from pf_cells_apart_t's second
   conjunct (ReplyRelroGeoB.pf_cells_apart_reply_B); the depot zone from CfInstHit's hit_pf_ag_B, since reply B's
   ims_dzone (AGjm.DZONE, B/AGif4reply.v) and ag_dzone (AGis.DZONE, B/AGif0reply.v) are the same three ranges. *)
Lemma PF_SEP_B : forall B, @im_syms AImg_reply B -> YGcfInstSec.PF_SEP_t (ci := CfImg_B) B.
Proof.
intros B TS ly a LY IMG HT Ha. pose proof TS as TS'. change (TfibSyms B) in TS'.
pose proof (ReplyRelroGeoB.pf_cells_apart_reply_B B TS') as PA. unfold YG0ncf.pf_cells_apart_t in PA.
split; [exact (proj1 (proj2 (PA a Ha)))|].
intros Hd.
assert (Hd' : @ag_dzone AImg_reply AGImg_reply ly a).
{ change (AGis.DZONE ly a). unfold AGis.DZONE. change (AGjm.DZONE ly a) in Hd. unfold AGjm.DZONE in Hd. exact Hd. }
exact (YGcfInstHitreply.hit_pf_ag_B B TS ly a LY IMG HT Hd' Ha).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The closing theorems. *)
Section close.
Context {cp : CfParams}.
#[local] Existing Instance CfImg_B.
Variable B : asyms.
Variable IOK : Z -> Prop.
Hypothesis TS : @im_syms AImg_reply B.
Hypothesis IOK_inst : YGcfInstBase.IOK_ok B IOK.
Hypothesis HIMG : YGcfDIface.IMG_COVER.
Hypothesis HDH : forall t, as_dhash B t = YF0p.tfib_dhash t.
Let TS' : TfibSyms B := TS.

Local Ltac rows :=
  first [ exact TS | exact IOK_inst | exact HIMG
  | exact (ReplyImg_hoom.hoom_B B TS) | exact (ReplyImg_herr.herr_B B TS) | exact (ReplyImg_instok.inst_ag_B B TS)
  | exact (ReplyImg_instcells.inst_cells_B B TS') | exact (ReplyImg_vis.comb_vis_B B TS)
  | exact (ReplyImg_vis.errno_vis_B B TS) | exact (ReplyImg_vis.dep_unhid_B B TS) | exact ReplyImg_zone3.zone3_B
  | exact (ReplyImg_zone3.const_keep_s_B B TS) | exact (CONST_NOT_JUNK_B B TS')
  | exact (ReplyImg_errnoseg.errno_seg_B B TS) | exact (ERR_NST_B B TS')
  | exact ReplyImg_errnoimgs.errno_apart_dzone_s_B | exact ReplyImg_errnoimgs.errno_apart_shadow_s_B
  | exact ReplyImg_errnoimgs.errno_apart_zone3_s_B | exact ErrnoApartreply.errno_in_img_reply
  | exact ErrnoApartreply.errno_unhidden_reply | exact ErrnoApartreply.errno_apart_inst_ag_reply
  | exact (YGcfInstHitreply.hit_errb_sep_B B TS) | exact (YGcfInstDepotWreply.depot_spec_a_reply B TS' HDH)
  | exact (CONST_APART_B B TS') | exact (AREAS_DISJ_B B TS) | exact (PF_SEP_B B TS)
  | exact (YGcfInstSecreplyB.SYM_TSD_B B TS) | exact YGcfInstSecreplyB.SHB_EQ_B | exact YGcfInstSecreplyB.WFRAME_SP_B
  | exact (YGcfInstSecreplyB.DEP_FP_B B TS) | exact (YGcfInstSecreplyB.DZ_LOC_B B TS) | exact YGcfInstSecreplyB.DZ_DEC_B
  | exact (YGcfInstSecreplyB.DZ_OWN_B B TS) | exact (YGcfInstSecreplyB.CONST_LY_B B TS)
  | exact (YGcfInstSecreplyB.CONST_LT_B B TS) | exact (YGcfInstSecreplyB.JUNK_LY_B B TS)
  | exact (YGcfInstSecreplyB.JUNK_LT_B B TS) ].

Theorem ifaceS_B : forall Hp, AGif4.AIfaceS B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow.
Proof. intros Hp. eapply YGcfInstSec.ifaceS_cf; rows. Qed.

Theorem ifaceSw_B : forall Hp, AGif4.AIfaceSw B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow cf_malloc_max cf_nob (2 ^ 32).
Proof.
intros Hp. eapply YGcfInstSec.ifaceSw_cf; [rows ..|].
unfold YGcfAbudget.CF_HEAD. apply Z.leb_le. vm_compute. reflexivity.
Qed.

Theorem ifaceSE_B : forall Hp, ErrnoGS.AIfaceSE B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B)
  cf_malloc_max LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow.
Proof. intros Hp. eapply YGcfInstSec.ifaceSE_cf; rows. Qed.
End close.
End a.
