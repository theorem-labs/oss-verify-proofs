(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropKit.v at a529a88a618 (the plumbing of
   the property loop's block lemmas: pa_chunk8, pa_keep, pa_kwr_ro, pa_run, pa_runb, pa_branch, pa_reg, pa_leaf),
   proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at a529a88a618 (kept_run) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v
   at a529a88a618 (its section g and its tactics: the (location, value) facts of a cut, the journal-and-frame step,
   the segment's write set, the first block's bounds and pod_put, the model of a shape-7 property, the start facts
   and the input at a cut) for reac-pw/fuzz_headamp's image B: rs_ / rl_ / rm_ -> hsu_ / hd_ / hm_, role's image A
   record and code -> fuzz_headamp.asan-ubsan's (lib/AU/Img0U.v rsegs, HPgImgB.headamp_himg_B: class-4 frame of
   1024 bytes, real frame of 0x220 bytes, write set [F+0x20, F+0x278) / 116 shadow bytes / [R, R+0x198)), the block
   post HPgSteps.hdu_blk_postE in place of pa_post, one table over the four pieces of image B. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropKit.v, with its module paths and module names changed; 156 of its 202 lines of code are new or changed and 365 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Odd.v at 97ea9c9eafa; image B of
   fuzz_headamp (lib/AU/HPgSeg.v hsu_* in place of RPgSeg.rs_*, lib/AU/HPgE0Def.v e0_* in place of RPgEnt0Def.r7_*,
   lib/A/HPgMem.v prefix hm_ in place of RPgMem's rm_), the frame of class 4 and image B's own registers and
   R-cells, the
   allocator laws taken from the kernel theorem AR_laws_ok instead of a Section hypothesis, and t1 (kept across the
   two calls in s5) added to the cut's locations. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): lib/AU/HPgE0Def.v
   e0_odd_stmt, the ODD block of ent_build's case 0 (pod.h:247-248,
   `const char *o = odd_ch[c % 14]; memcpy(ch, o, strlen(o) + 1);`), from the cut e0_cut_ODD at 0x82318 to the cut
   HPgSeg.hsu_cut_G at G = 0x81afc. Proves no function (kind: segment lemma).

   HOW. lib/AU/HPgE0OddC.v o_at_cut carries the start state's image facts (rom_view, the odd_ch table entry's shadow
   bytes and cell, the string's HPgBase.hd_cstr) to the cut's memory; lib/AU/HPgE0OddW.v o_walk walks the block over
   the journal (one engine run to the UBSan pointer-overflow test, one through that test and the table entry's
   shadow check, one to the strlen call, the strlen wrapper, one to the __asan_memcpy call, the intrinsic, one run
   to G). This file builds hsu_cut_G from o_walk's post: the journal-and-frame part (the cut's layout and state
   unchanged; the walk writes only the callees' stack below R and ch, which lies in the frame's objects of
   HPgImgB hi_w1), the (location, value) facts (the callee-saved registers, t1 and the real-frame cells kept), the
   frame's shadow, the first block and e62 unchanged, ch holding odd_ch[c mod 14] and its NUL, and the model's text
   by HPgE0Def.e0_g_of_cp.

   The registers and R-cells it names are image B's: s0 = S (8), s1 = R (9), s3 = (F >> 3) + K (19), s11 = K (27),
   s8 = the `/ 10` multiplier (24), s6 = &r (22), s9 = &t (25), s2 = &ch (18), s10 = p (26), t1 = what is left of
   the input (6), a3 = c (13), s4 (20) and s5 (21) the two registers the block itself uses; the R-cells are
   HPgSeg.hsu_L_Dc's (R+0x8 .. R+0x158) and R+0x110. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgMem HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgE0Def HPgE0Base HPgE0OddB HPgE0OddC HPgE0OddW HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* membership in a concrete location list *)
Ltac oa_in := cbn [e0_L_arm hsu_L_Dc hsu_Rc0 hsu_Kc app In fst snd]; repeat (first [left; reflexivity | right]).

(* the first block's image at a pod-loop cut has the block's size *)
Lemma oa_pc_len : forall sh ps es, hsu_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat ->
Z.of_nat (length (pc_image (PbCut sh ps (Some es)))) = Layout.PP_SIZE.
Proof.
intros sh ps es (_ & Hk & He & Hl3) Hes Hl. unfold pc_image.
assert (Hk' : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hk]; intros kv [_ H]; exact H).
destruct (pc_buf_len_open sh ps es Hk' He Hes) as [Hb _].
assert (HE : (length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat /\ Forall ent_wf (pc_ents (PbCut sh ps (Some es)))).
{ unfold pc_ents. cbn [pc_props pc_open].
  destruct (first_params ps) as [[iv|es']|] eqn:E.
  - split; [cbn; lia | constructor].
  - unfold first_params in E. destruct (find _ _) as [kv|] eqn:F; [|discriminate]. cbn in E. injection E as E.
    apply find_some in F as [Hin _]. split.
    + rewrite Forall_forall in Hk'. specialize (Hk' kv Hin). rewrite E in Hk'. exact Hk'.
    + apply all_ents_Forall in He. rewrite Forall_forall in He. specialize (He kv Hin). rewrite E in He. exact He.
  - split; [lia | exact Hes]. }
destruct HE as [HE1 HE2].
apply Layout.length_pp_image.
- lia.
- exact HE1.
- eapply Forall_impl; [|exact HE2]. intros e (_ & Hbd & Hs). lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma oa_at_get : forall H mem regs e L l v,
hsu_at rsegs H mem regs e L -> In (l, v) L -> hd_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HL Hin. unfold hsu_at in HL. rewrite Forall_forall in HL. exact (HL (l, v) Hin). Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis ASTRLEN : astrlen_realizes rsegs B E0_STRLEN.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy E0_MEMCPY.

Lemma e0_odd : e0_odd_stmt B MT.
Proof using ASTRLEN AMEMCPY.
unfold e0_odd_stmt, e0_from_ODD.
intros cx POST rest i k Hst HG ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb Hli Hlk Hcut.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct Hcut as (Hbase & Hat & Hfsh & Hpp & Hz & Hkd & Hcp & Hc & Hpb).
pose proof Hbase as (Hcore & _ & _ & _ & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hesw & Hes32 & _).
pose proof Hcore as (HJ2 & Hr234 & Hfr & Hperm & Hio & Hmo & Hkeep).
pose proof Hst as (Hpre & _ & _ & _).
pose proof Hpre as (HJc & _ & H2 & H3 & H4 & HeS & HR32 & HRS & HRSTK & Hown & HF & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & Hfresh).
cbn [hi_rsz hi_cid headamp_himg_B] in HRS, Hown, HF.
destruct Hfresh as (_ & Hppin & _).
(* the bounds of R, F and pp *)
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _).
destruct Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Hts : T_SEG_STK = 16384) by reflexivity.
assert (HRlo : alloc_ceiling + 16384 <= e_R (x_e cx)) by (rewrite Hts in HRSTK; lia).
assert (HRhi : e_R (x_e cx) + 0x220 <= 2 ^ 47) by lia.
assert (HR16 : e_R (x_e cx) mod 16 = 0).
{ pose proof HR32 as HR32'. apply Z.mod_divide in HR32'; [|lia]. destruct HR32' as [zz Hzz]. rewrite Hzz.
  replace (zz * 32) with (zz * 2 * 16) by lia. apply Z.mod_mul. lia. }
assert (HFa : e_F (x_e cx) = frame_addr ly2 4 (x_pos cx)).
{ rewrite HF. unfold frame_addr. f_equal.
  destruct Hly2 as (_ & _ & _ & _ & _ & E2 & _). destruct Hlyc as (_ & _ & _ & _ & _ & Ec & _). congruence. }
assert (Hin4 : In (4, x_pos cx) (frames S2)) by (rewrite Hfr, Hfrsc; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 4 (x_pos cx) HAR2 Hin4) as (HF32 & HFapp & _ & _).
destruct (frames_bounds rsegs B LAWS ly2 S2 W2 mem2 md2 4 (x_pos cx) HAR2 Hin4) as (HF4096 & HFceil & _).
rewrite <- HFa in HF32, HFapp, HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in HFapp, HFceil.
assert (HFd : 8 * (e_F (x_e cx) / 8) <= e_F (x_e cx)) by (apply Z.mul_div_le; lia).
assert (HFd0 : 0 <= e_F (x_e cx) / 8) by (apply Z.div_pos; lia).
assert (Hsp : spZ (x_regs cx) = e_R (x_e cx))
  by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; lia).
(* pp: the first block, below the allocator ceiling and apart from the frame for locals *)
assert (Hpp2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppin]).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hpp2) as (_ & Hpp4096 & Hppceil & _).
pose proof (sep_block_frame rsegs B LAWS ly2 S2 W2 mem2 md2 _ _ 4 (x_pos cx) HAR2 Hpp2 Hin4) as Hsep.
rewrite <- HFa in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hppceil, Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. unfold Layout.PP_SIZE in Hppceil, Hsep.
(* the cut's registers *)
unfold hsu_at_cx in Hat.
assert (HatA : hsu_at rsegs (w_H W2) mem2 regs2 (x_e cx) (e0_L_arm cx sh np ps cnt es rest r pb))
  by (unfold hsu_at in *; apply Forall_app in Hat as [Hat1 _]; exact Hat1).
pose proof (oa_at_get _ _ _ _ _ (LReg 27) SHADOW_OFF HatA ltac:(oa_in)) as R27. cbn [hd_at] in R27.
pose proof (oa_at_get _ _ _ _ _ (LReg 18) (e_F (x_e cx) + HSU_CH) HatA ltac:(oa_in)) as R18. cbn [hd_at] in R18.
pose proof (oa_at_get _ _ _ _ _ (LReg 13) c Hat
  ltac:(apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right]))) as R13.
cbn [hd_at] in R13.
(* the start facts at the cut's memory *)
destruct (o_at_cut B MT cx rest ly2 S2 W2 regs2 mem2 md2 Hst Hcore Hfsh) as (Hrom2 & Hodd).
assert (Hm : 0 <= c mod 14 < 14) by (apply Z.mod_pos_bound; lia).
destruct (Hodd (c mod 14) Hm) as (Hra2 & Hcell2 & Hcs2).
pose proof Hfsh as Hfsh'. unfold hsu_fsh_at in Hfsh'. rewrite e0_PG_sh in Hfsh'.
(* ---- the walk ---- *)
eapply SRr_bind.
{ exact (o_walk B ASTRLEN AMEMCPY (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
    (x_md0 cx) (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 (e_R (x_e cx)) (e_F (x_e cx)) (x_pos cx) c HJ2
    (eq_trans (Hr234 2 (or_introl eq_refl)) H2) (eq_trans (Hr234 3 (or_intror (or_introl eq_refl))) H3)
    (eq_trans (Hr234 4 (or_intror (or_intror eq_refl))) H4) R27 R13 R18 Hc HR16 ltac:(lia) HRSTK Hown HFa
    Hfsh' Hrom2 Hra2 Hcell2 Hcs2). }
intros W3 c3 _ (-> & regsG & memG & mdG & -> & HJG & HioG & HregG & H6G0 & HkG & HchG).
pose proof (o_len_le (c mod 14) Hm) as Hol. unfold cb_kept, o_len in HkG.
assert (Hkg : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - 2 * ESTACK <= a < e_R (x_e cx)) ->
  ~ (e_F (x_e cx) + 0xa0 <= a < e_F (x_e cx) + 0xa0 + Z.of_nat (length (o_str (c mod 14))) + 1) ->
  aview rsegs (w_H W2) memG a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H1'. apply HkG; [exact Ha|]. intros [X|X]; [exact (H1 X) | exact (H1' X)]. }
clear HkG.
assert (H6G : getr regsG (Z_to_bv 5 6) = getr regs2 (Z_to_bv 5 6)).
{ replace (Z_to_bv 5 6) with (6%bv : bv 5) by (apply bv_eq; reflexivity). exact H6G0. }
apply (HG ly2 S2 W2 regsG memG mdG sh np ps cnt es rr r pb (o_str (c mod 14)) Hli Hlk).
split; [split; [|exact (proj2 Hbase)]|].
{ (* the journal-and-frame part *)
  unfold hsu_core, hsu_mid.
  split; [exact HJG|].
  split; [intros q Hq; rewrite (HregG q ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia));
          exact (Hr234 q Hq)|].
  split; [exact Hfr|]. split; [exact Hperm|].
  split; [eapply same_io_trans; [exact Hio | exact HioG]|].
  split; [exact Hmo|].
  intros a Ha Hs HE. rewrite <- (Hkeep a Ha Hs HE). rewrite Hsp in Hs.
  apply Hkg; [exact Ha | lia |].
  intros X. apply HE. left. unfold hd_inw. cbn [hi_w1 headamp_himg_B]. apply Exists_cons_hd.
  cbn [hd_xv fst snd]. lia. }
split.
{ (* the (location, value) facts *)
  unfold hsu_at_cx, hsu_at.
  replace (hsu_L_Dc rsegs cx sh np ps cnt es ++
    [(LCell XR 0x110, hsu_cur rsegs cx rest r); (LReg 6, Z.of_nat (length r));
     (LReg 18, e_F (x_e cx) + HSU_CH); (LReg 26, pb)])
    with (e0_L_arm cx sh np ps cnt es rest r pb) by reflexivity.
  apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memG regs2 regsG); [exact HatA|].
  intros f Hf. unfold e0_L_arm, hsu_L_Dc, hsu_Rc0, hsu_Kc in Hf. cbn [app In] in Hf.
  repeat (destruct Hf as [<-|Hf];
    [ cbn [fst hm_keeps hd_xv];
      first [ exact H6G
            | apply HregG; [unfold acallee_saved; lia | lia | lia]
            | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply Hkg; lia ]
    |]).
  destruct Hf. }
split.
{ (* the frame's shadow *)
  unfold hsu_fsh_at in *. eapply hm_fsh_kept; [exact Hfsh|]. rewrite e0_PG_sh, hmu_sh_len. intros j Hj.
  unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp.
  apply Hkg; unfold shadow_addr, SHADOW_OFF; lia. }
split.
{ (* the first block *)
  unfold hsu_pp_at in *. eapply (hm_bytes_kept rsegs); [exact Hpp|]. intros x Hx.
  rewrite (oa_pc_len sh ps es Hwf Hesw Hes32) in Hx. unfold Layout.PP_SIZE in Hx.
  apply Hkg; lia. }
split.
{ (* ch *) unfold hsu_obj_at, HSU_CH. exact HchG. }
split.
{ (* e62, zeros *)
  unfold hsu_obj_at, HSU_E62 in *. eapply (hm_bytes_kept rsegs); [exact Hz|]. intros x Hx.
  assert (L104 : Z.of_nat (length (zeros 104)) = 104) by (rewrite length_zeros; reflexivity).
  rewrite L104 in Hx. apply Hkg; lia. }
split; [exact Hkd|].
split.
{ rewrite (e0_g_of_cp rr c pb r Hcp). destruct (Z.ltb_spec c 200); [lia | reflexivity]. }
split; [exact Hol | exact Hpb].
Qed.
End d.
End b.

Print Assumptions e0_odd.
