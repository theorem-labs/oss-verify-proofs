(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 (pa_i_memset_at, as
   hbp_i_memset_at; pa_i_bv5_cases, pa_i_cs, pa_i_pres and pa_i_mod16_sub, as hbp_i_*; pa_int7's route, one engine state
   up to each call and a fresh one after it) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618
   (pa_piece_int7, as hbp_piece_int7) for reac-pw/fuzz_headamp's image B: the block walked new against image B's own
   instructions (the scope stores of e, __asan_memset of e's body, the two header words, the out-of-line pod_write_ent
   under PweSpec.pod_write_ent_specX, the restores of the loop's three values), the cut states of lib/AU/HPgSeg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropInt.v; 148 of its 204 lines of code are new or changed and 905 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Dig.v at 97ea9c9eafa (r7_dig, dga_kept,
   dga_not_shr) and proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Odd.v at 97ea9c9eafa (oa_pc_len, oa_at_get as dg_pc_len,
   dg_at_get); restated for image B: HPgE0Def.e0_dig_stmt from e0_cut_DIG to HPgSeg.hsu_cut_G at headamp_himg_B /
   headamp_bld_B, image B's registers, R-cells, frame of class 4 and its write ranges hi_w1, and the allocator laws
   from the kernel theorem AR_laws_ok in place of a Section hypothesis. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): lib/AU/HPgE0Def.v
   e0_dig_stmt, the DIG block of ent_build's case 0 (pod.h:237-246: the decimal text of c mod 64 into ch with its
   NUL, through r[4]) in LLVMFuzzerTestOneInput 0x80c40, from the cut e0_cut_DIG at DIG 0x81a1c to the cut
   HPgSeg.hsu_cut_G at G = 0x81afc. Proves no function (kind: segment lemma).

   HOW. lib/AU/HPgE0DigW.v dg_walk walks the block over the journal (r into scope, the digits and the reverse into
   ch, the pointer-overflow test against R+0xc0, the NUL, r out of scope again). This file builds hsu_cut_G from
   dg_walk's post: the journal-and-frame part (the cut's layout and state unchanged; the walk writes only ch
   [F+0xa0, F+0xb8), r [F+0xe0, F+0xe4) and r's shadow byte (granule 0x1c of shadow_addr F), which lie in the
   frame's objects and its shadow row of HPgImgB hi_w1), the (location, value) facts (HPgE0Def.e0_L_arm, which is
   hsu_cut_G's list: every register but a0 .. a7 and every real-frame cell kept), the frame's shadow (r's byte back
   to 0xf8, so the row is hsu_PG again), the first block and e62 unchanged, ch holding dec64 (c mod 64) and its
   NUL, and the model's text by HPgE0Def.e0_g_of_cp.
   Registers and R-cells read from e0_cut_DIG: s3 (19) = shadow_addr F, s11 (27) = K, s6 (22) = F+0xe0,
   s2 (18) = F+0xa0, s8 (24) = HSU_MULT10, s1 (9) = R, a3 (13) = c, t0 (5) = 4, t3 (28) = 9, t2 (7) = 10,
   s7 (23) = -8, R+0xc0 = -(F+0xa0)-1. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgMem HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgE0Def HPgE0Base HPgE0DigK HPgE0DigW.
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
Ltac dg_in := cbn [e0_L_arm hsu_L_Dc hsu_Rc0 hsu_Kc app In fst snd]; repeat (first [left; reflexivity | right]).
Ltac dg_in_tl := apply in_or_app; right; cbn [In]; repeat (first [left; reflexivity | right]).

(* the first block's image at a pod-loop cut has the block's size *)
Lemma dg_pc_len : forall sh ps es, hsu_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat ->
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

Lemma dg_at_get : forall H mem regs e L l v,
hsu_at rsegs H mem regs e L -> In (l, v) L -> hd_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v HL Hin. unfold hsu_at in HL. rewrite Forall_forall in HL. exact (HL (l, v) Hin). Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma e0_dig : e0_dig_stmt B MT.
Proof.
unfold e0_dig_stmt, e0_from_DIG.
intros cx POST rest i k Hst HG ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb Hli Hlk Hcut.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
destruct Hcut as (Hbase & Hat & Hfsh & Hpp & Hz & Hkd & Hcp & Hc & Hpb).
pose proof Hbase as (Hcore & _ & _ & _ & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hesw & Hes32 & _).
pose proof Hcore as (HJ2 & Hr234 & Hfr & Hperm & Hio & Hmo & Hkeep).
pose proof Hst as (Hpre & _ & _ & _).
pose proof Hpre as (HJc & _ & H2 & H3 & H4 & HeS & HR32 & HRS & HRSTK & Hown & HF & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & Hfresh).
destruct Hfresh as (_ & Hppin & _).
cbn [hi_rsz hi_cid headamp_himg_B] in HRS, Hown, HF.
(* the bounds of R, F and pp *)
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _).
destruct Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hts : T_SEG_STK = 16384) by reflexivity.
assert (HRlo : alloc_ceiling + 16384 <= e_R (x_e cx)) by (rewrite Hts in HRSTK; lia).
assert (HRhi : e_R (x_e cx) + 0x220 <= 2 ^ 47) by lia.
assert (HFa : e_F (x_e cx) = frame_addr ly2 4 (x_pos cx)).
{ rewrite HF. unfold frame_addr. f_equal.
  destruct Hly2 as (_ & _ & _ & _ & _ & E2 & _). destruct Hlyc as (_ & _ & _ & _ & _ & Ec & _). congruence. }
assert (Hin4 : In (4, x_pos cx) (frames S2)) by (rewrite Hfr, Hfrsc; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 4 (x_pos cx) HAR2 Hin4) as (HF32 & HFapp & _ & _).
destruct (frames_bounds rsegs B LAWS ly2 S2 W2 mem2 md2 4 (x_pos cx) HAR2 Hin4) as (HF4096 & HFceil & _).
rewrite <- HFa in HF32, HFapp, HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in HFapp, HFceil.
assert (HFhi : e_F (x_e cx) + 1024 <= DG_FHI) by (unfold DG_FHI; lia).
pose proof (dg_sh_bounds _ HF4096 HFhi) as (SB0 & SB1).
assert (Hpp2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hppin]).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hpp2) as (_ & Hpp4096 & Hppceil & Hppapp & _).
pose proof (sep_block_frame rsegs B LAWS ly2 S2 W2 mem2 md2 _ _ 4 (x_pos cx) HAR2 Hpp2 Hin4) as Hsep.
rewrite <- HFa in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hppceil, Hsep, Hppapp.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. unfold Layout.PP_SIZE in Hppceil, Hsep, Hppapp.
set (F := e_F (x_e cx)) in *.
set (R := e_R (x_e cx)) in *.
assert (HshR : shadow_addr F + 128 <= R)
  by (clear - SB1 C1 HRlo; unfold SHADOW_OFF in *; change (2 ^ 44) with 17592186044416 in SB1; lia).
(* the cut's registers and its R-cell R+0xc0 *)
unfold hsu_at_cx in Hat.
assert (HatA : hsu_at rsegs (w_H W2) mem2 regs2 (x_e cx) (e0_L_arm cx sh np ps cnt es rest r pb))
  by (unfold hsu_at in *; apply Forall_app in Hat as [Hat1 _]; exact Hat1).
pose proof (dg_at_get _ _ _ _ _ (LReg 19) (shadow_addr F) HatA ltac:(dg_in)) as R19.
pose proof (dg_at_get _ _ _ _ _ (LReg 27) SHADOW_OFF HatA ltac:(dg_in)) as R27.
pose proof (dg_at_get _ _ _ _ _ (LReg 22) (F + HSU_R4) HatA ltac:(dg_in)) as R22.
pose proof (dg_at_get _ _ _ _ _ (LReg 24) HSU_MULT10 HatA ltac:(dg_in)) as R24.
pose proof (dg_at_get _ _ _ _ _ (LReg 9) R HatA ltac:(dg_in)) as R9.
pose proof (dg_at_get _ _ _ _ _ (LReg 18) (F + HSU_CH) HatA ltac:(dg_in)) as R18.
pose proof (dg_at_get _ _ _ _ _ (LCell XR 0xc0) (- F - HSU_CH - 1) HatA ltac:(dg_in)) as Rc0.
pose proof (dg_at_get _ _ _ _ _ (LReg 13) c Hat ltac:(dg_in_tl)) as R13.
pose proof (dg_at_get _ _ _ _ _ (LReg 5) 4 Hat ltac:(dg_in_tl)) as R5.
pose proof (dg_at_get _ _ _ _ _ (LReg 28) 9 Hat ltac:(dg_in_tl)) as R28.
pose proof (dg_at_get _ _ _ _ _ (LReg 7) 10 Hat ltac:(dg_in_tl)) as R7.
pose proof (dg_at_get _ _ _ _ _ (LReg 23) (-8) Hat ltac:(dg_in_tl)) as R23.
cbn [hd_at hd_xv] in R19, R27, R22, R24, R9, R18, Rc0, R13, R5, R28, R7, R23.
fold R in Rc0.
pose proof Hfsh as Hfsh'. unfold hsu_fsh_at in Hfsh'.
(* ---- the walk ---- *)
eapply SRr_bind.
{ exact (dg_walk B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
    (x_md0 cx) (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) regs2 F (x_pos cx) R c HJ2 Hown HFa
    R19 R27 R22 R18 R24 R13 R5 R28 R7 R23 R9 HRlo HRhi Rc0 ltac:(lia) Hfsh'). }
intros W3 c3 _ (-> & regsG & memG & mdG & -> & HJG & HioG & HregG & HkG & _ & HchG & HshG).
assert (Hkg : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0xa0 <= a < F + 0xb8) -> ~ (F + 0xe0 <= a < F + 0xe4) ->
  a <> shadow_addr F + 0x1c -> aview rsegs (w_H W2) memG a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 H2' H3'. apply HkG; [exact Ha|]. intros [X|[X|X]]; [exact (H1 X) | exact (H2' X) | exact (H3' X)]. }
clear HkG.
apply (HG ly2 S2 W2 regsG memG mdG sh np ps cnt es rr r pb (dec64 (c mod 64)) Hli Hlk).
split; [split; [|exact (proj2 Hbase)]|].
{ (* the journal-and-frame part *)
  unfold hsu_core, hsu_mid.
  split; [exact HJG|].
  split; [intros q Hq; rewrite (dg_kept_reg regs2 regsG HregG q ltac:(lia)); exact (Hr234 q Hq)|].
  split; [exact Hfr|]. split; [exact Hperm|].
  split; [eapply same_io_trans; [exact Hio | exact HioG]|].
  split; [exact Hmo|].
  intros a Ha Hs HE. rewrite <- (Hkeep a Ha Hs HE).
  destruct (Z.eq_dec a (shadow_addr F + 0x1c)) as [Ea|Ea].
  - exfalso. apply HE. left. unfold hd_inw. cbn [hi_w1 headamp_himg_B]. apply Exists_cons_tl. apply Exists_cons_hd.
    cbn [hd_xv fst snd]. fold F. lia.
  - destruct (Z_lt_le_dec a (F + 0x20)) as [La|La]; [apply Hkg; [exact Ha | lia | lia | exact Ea]|].
    destruct (Z_lt_le_dec a (F + 0x278)) as [Lb|Lb]; [|apply Hkg; [exact Ha | lia | lia | exact Ea]].
    exfalso. apply HE. left. unfold hd_inw. cbn [hi_w1 headamp_himg_B]. apply Exists_cons_hd.
    cbn [hd_xv fst snd]. fold F. lia. }
split.
{ (* the (location, value) facts: hsu_cut_G's list is e0_L_arm *)
  unfold hsu_at_cx, hsu_at.
  apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) memG regs2 regsG); [exact HatA|].
  intros f Hf. unfold hsu_L_Dc, hsu_Rc0, hsu_Kc in Hf. cbn [app In] in Hf.
  repeat (destruct Hf as [<-|Hf];
    [ cbn [fst hm_keeps hd_xv]; fold R;
      first [ apply (dg_kept_reg regs2 regsG HregG); lia
            | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply Hkg; lia ]
    |]).
  destruct Hf. }
split.
{ (* the frame's shadow: r's byte back to 0xf8 *)
  unfold hsu_fsh_at. rewrite e0_PG_sh in Hfsh' |- *.
  rewrite <- (hmu_sh_r_out true true false false false true false false).
  apply (hm_fsh_set rsegs (w_H W2) mem2 (w_H W2) memG F _ 28 1 0xf8 Hfsh').
  - intros j Hj. replace j with 0x1c by lia. exact HshG.
  - intros j Hj Hn. rewrite hmu_sh_len in Hj.
    assert (Hj' : j <> 0x1c) by (intros ->; apply Hn; lia).
    apply Hkg; [unfold SHADOW_OFF in *; lia | | | lia].
    + intros X. apply (dg_app_not_shr F 1024 (shadow_addr F + j) F HFapp); [lia | exact HF4096 | exact HFhi | lia].
    + intros X. apply (dg_app_not_shr F 1024 (shadow_addr F + j) F HFapp); [lia | exact HF4096 | exact HFhi | lia]. }
split.
{ (* the first block *)
  unfold hsu_pp_at in *. eapply (hm_bytes_kept rsegs); [exact Hpp|]. intros x Hx.
  rewrite (dg_pc_len sh ps es Hwf Hesw Hes32) in Hx. unfold Layout.PP_SIZE in Hx.
  apply Hkg; [lia | lia | lia |].
  apply (dg_app_not_sh (e_pp (x_e cx)) 0x4d20 x F Hppapp); [lia | exact HF4096 | exact HFhi]. }
split; [exact HchG|].
split.
{ (* e62, zeros *)
  unfold hsu_obj_at in *. eapply (hm_bytes_kept rsegs); [exact Hz|]. intros x Hx.
  assert (L104 : Z.of_nat (length (zeros 104)) = 104) by (rewrite length_zeros; reflexivity).
  rewrite L104 in Hx. unfold HSU_E62 in Hx. apply Hkg; [lia | lia | lia |].
  apply (dg_app_not_sh F 1024 x F HFapp); [lia | exact HF4096 | exact HFhi]. }
split; [exact Hkd|].
split.
{ rewrite (e0_g_of_cp rr c pb r Hcp). destruct (Z.ltb_spec c 200); [reflexivity | lia]. }
split; [pose proof (dec64_len (c mod 64)); lia | exact Hpb].
Qed.
End d.
End b.

Print Assumptions e0_dig.
