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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropKit.v; 151 of its 194 lines of code are new or changed and 368 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): what the cut J 0x82618 of
   the builder piece W8 of LLVMFuzzerTestOneInput (0x80c40) gives the piece's blocks and calls, the statement
   hw8_J_facts_stmt of lib/AU/HPgW8BKit.v, proved from the segment's start (lib/AU/HPgSeg.v hsu_start_M01, at the
   image's record headamp_himg_B) and the cut J (hsu_cut_J). Proves no function (kind: segment lemma).

   WHAT IT READS. From the start: the journal from the harness's entry, sp / gp / tp, R = e_R (32-aligned, the real
   frame of 0x220 bytes below the entry sp, the callees' stack inside the journal's window), the frame for locals F
   = the class-4 side-stack frame (4, pos) the harness holds (1024 bytes, 128 shadow bytes), and the first block pp
   (live, made since the journal's start). From the cut J: the journal at J, sp / gp / tp kept, the frames and
   blocks as at the segment's start, the cut list (registers s1 = R (x9), s2 = pp + 0x4000 (x18), s3 = the frame's
   shadow base (x19), s4 = F + 0x210 (x20), s7 = pp (x23), s11 = K (x27); R-cells R+0x150 the shadow address of
   pp + 0x4000, R+0x140 first, R+0x158 the pod index, R+0x128 cnt, R+0xe0 (pp + 0x4d14) >> 3, R+0x120 pp + 0x4d14,
   R+0xd8 ~(pp + 0x4014), R+0xd0 pp + 0x4014), the frame's shadow hsu_PJ (e62 in scope), pp's image, e62's bytes
   and the model's bounds. The geometry comes from the allocator laws (YG0q.AR_laws_ok): al_blocks, al_frames,
   frames_bounds, sep_block_frame. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgW8Model.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgW8BKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
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
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ======================================== the record's pods ======================================== *)
(* ent[] at a cut inside the params Struct: at most 32 pods, each well formed *)
Lemma wj_pc_ents : forall sh ps es,
  Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) -> Forall ent_wf es ->
  (length es <= 32)%nat ->
  (length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat /\ Forall ent_wf (pc_ents (PbCut sh ps (Some es))).
Proof.
intros sh ps es Hp Ha He Hl. unfold pc_ents, first_params. cbn [pc_props pc_open].
destruct (find _ ps) as [[k v]|] eqn:E; cbn [option_map snd].
- apply find_some in E as [Hin _].
  destruct v as [z|es'].
  + split; [cbn; lia | constructor].
  + split.
    * exact (proj1 (Forall_forall _ _) Hp _ Hin).
    * apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) Ha). unfold all_ents.
      apply in_flat_map. exists (k, PStruct es'). split; [exact Hin | exact Hx].
- split; assumption.
Qed.

(* ent[] is the open Struct's pods when no params property is among ps *)
Lemma wj_pc_ents_first : forall sh ps es, hsu_first ps = 1 -> pc_ents (PbCut sh ps (Some es)) = es.
Proof.
intros sh ps es H1. unfold hsu_first in H1. destruct (existsb _ ps) eqn:Ex; [cbn in H1; discriminate H1|].
unfold pc_ents, first_params. cbn [pc_props pc_open].
destruct (find _ ps) as [kv|] eqn:E; [|reflexivity].
exfalso. apply find_some in E as [Hin Hk].
pose proof (proj2 (existsb_exists (fun kv : Z * pval => fst kv =? POD_PROP_PARAMS) ps)
  (ex_intro _ kv (conj Hin Hk))) as Ex'. congruence.
Qed.

Lemma wj_first_range : forall ps, hsu_first ps = 0 \/ hsu_first ps = 1.
Proof. intros ps. unfold hsu_first. destruct (negb _); [right | left]; reflexivity. Qed.

Lemma wj_small : forall v, 0 <= v <= 32 -> v mod 2 ^ 64 = v.
Proof. intros v Hv. apply Z.mod_small. lia. Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* a register / an R-relative cell of a cut list, by membership *)
Lemma wj_reg : forall H mem (regs : bvmap 5 word) e (L : list (hd_loc * Z)) r v,
  Forall (fun f => hd_at rsegs H mem regs e (fst f) (snd f)) L -> In (LReg r, v) L ->
  getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HF Hin. exact (proj1 (Forall_forall _ _) HF _ Hin). Qed.
Lemma wj_cell : forall H mem (regs : bvmap 5 word) e (L : list (hd_loc * Z)) o v,
  Forall (fun f => hd_at rsegs H mem regs e (fst f) (snd f)) L -> In (LCell XR o, v) L ->
  val_mem rsegs (mrestrict H mem) (e_R e + o) 8 (v mod 2 ^ 64).
Proof. intros H mem regs e L o v HF Hin. exact (proj1 (Forall_forall _ _) HF _ Hin). Qed.
Ltac wj_in := cbn [hsu_L_Dc hsu_Rc0 hsu_Kc app In fst snd];
  repeat (first [left; reflexivity | right]); fail.

(* ===================================== what the cut J gives ===================================== *)
Lemma hw8_J_facts : hw8_J_facts_stmt B MT.
Proof.
unfold hw8_J_facts_stmt.
intros cx rest sh np ps cnt es rr r ed ly2 S2 W2 regs2 mem2 md2 HS HJ.
cbv zeta.
destruct HS as (Hpre & _ & _ & _).
unfold hsu_pre, hd_seg_pre in Hpre.
destruct Hpre as (HJ0 & Hev & Hr2 & Hr3 & Hr4 & HeS & HR32 & HRsz & HRstk & Hown & HeF & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & (_ & Hppc & Hppn)).
unfold hsu_cut_J, hsu_pod_base, hsu_core, hsu_mid in HJ.
destruct HJ as (((HJ2 & Hregs & Hfr & Hperm & _ & _ & _) & _ & _ & _ & Hwfs & _ & _ & _ & _ & _ & _ & _ & _ &
  Hps2 & Hcnt & Hes & Hes32 & Hescnt) & Hat & Hfsh & Hpp & He & _ & Hwf).
destruct HJ0 as (_ & Hly0 & _ & _ & _ & Hfr0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof HJ2 as (HAR2 & Hly2 & _).
unfold hsu_at_cx, hsu_at in Hat.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
assert (Hpp2 : In (e_pp (x_e cx), PP_SIZE) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm) Hppc).
assert (Hown4 : In (4, x_pos cx) (x_own cx)) by exact Hown.
assert (Hfr2 : In (4, x_pos cx) (frames S2)) by (rewrite Hfr, Hfr0; apply in_or_app; left; exact Hown4).
assert (HFeq : frame_addr ly2 4 (x_pos cx) = e_F (x_e cx)).
{ rewrite HeF. unfold frame_addr. destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
  destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _). rewrite EF2, EF0. reflexivity. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hpp2) as (Bal & B4096 & Bceil & Bapp & _).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hfr2) as (Fal & Fapp & _).
destruct (frames_bounds rsegs B LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hfr2) as (F4096 & Fceil & _).
pose proof (sep_block_frame rsegs B LAWS ly2 S2 W2 mem2 md2 _ _ _ _ HAR2 Hpp2 Hfr2) as Hdis.
rewrite HFeq in Fal, Fapp, F4096, Fceil, Hdis.
change (req_size PP_SIZE) with 19744 in Bceil, Bapp, Hdis.
change (fs_frame_bytes 4) with 1024 in Fapp, Fceil, Hdis.
unfold zdisjoint in Hdis. cbn [fst snd] in Hdis.
destruct Hstk as (Ssp & _ & Slo & Slosp & Shi & Shi47 & _).
change (hi_rsz headamp_himg_B) with 0x220 in HRsz.
destruct Hwfs as (_ & Hpsw & Hall & _).
assert (Hpw : Forall (fun kv => pval_wf (snd kv)) ps)
  by (eapply Forall_impl; [|exact Hpsw]; intros kv [_ Hk]; exact Hk).
destruct (wm_L0 sh ps es Hpw Hall Hes Hps2 Hes32) as [HL HL8].
destruct (wj_pc_ents sh ps es Hpw Hall Hes (Nat.lt_le_incl _ _ Hes32)) as [Hent32 Hentwf].
assert (Hbody : Forall (fun e => (length (e_body e) <= 96)%nat) (pc_ents (PbCut sh ps (Some es))))
  by (eapply Forall_impl; [|exact Hentwf]; intros x (_ & Hx1 & Hx2); clear - Hx1 Hx2; lia).
assert (Hb : Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) <= POD_BUF_MAX)
  by (unfold POD_BUF_MAX; clear - HL; lia).
assert (Hpp' : hm_bytes rsegs (w_H W2) mem2 (e_pp (x_e cx)) (pc_image (PbCut sh ps (Some es)))) by exact Hpp.
unfold pc_image in Hpp'.
pose proof (wj_first_range ps) as Hfs.
assert (Hfs32 : 0 <= hsu_first ps <= 32) by (clear - Hfs; lia).
assert (Hk32 : 0 <= Z.of_nat (length es) <= 32) by (clear - Hes32; lia).
(* the journal, the first block and the frame for locals *)
split; [exact HJ2|].
split; [exact Hev|].
split; [exact Hpp2|].
split; [exact Hppn|].
split; [exact Hown4|].
split; [exact Hfr2|].
split; [exact HFeq|].
(* the registers *)
split; [exact (eq_trans (Hregs 2 (or_introl eq_refl)) Hr2)|].
split; [exact (eq_trans (Hregs 3 (or_intror (or_introl eq_refl))) Hr3)|].
split; [exact (eq_trans (Hregs 4 (or_intror (or_intror eq_refl))) Hr4)|].
split; [apply (wj_reg _ _ _ _ _ 9 _ Hat); wj_in|].
split; [apply (wj_reg _ _ _ _ _ 18 _ Hat); wj_in|].
split; [apply (wj_reg _ _ _ _ _ 19 _ Hat); wj_in|].
split; [apply (wj_reg _ _ _ _ _ 20 _ Hat); wj_in|].
split; [apply (wj_reg _ _ _ _ _ 23 _ Hat); wj_in|].
split; [apply (wj_reg _ _ _ _ _ 27 _ Hat); wj_in|].
(* the R-cells *)
split; [apply (wj_cell _ _ _ _ _ 0x150 _ Hat); wj_in|].
split.
{ pose proof (wj_cell _ _ _ _ _ 0x140 (hsu_first ps) Hat ltac:(wj_in)) as X.
  rewrite (wj_small _ Hfs32) in X. exact X. }
split.
{ pose proof (wj_cell _ _ _ _ _ 0x158 (Z.of_nat (length es)) Hat ltac:(wj_in)) as X.
  rewrite (wj_small _ Hk32) in X. exact X. }
split.
{ pose proof (wj_cell _ _ _ _ _ 0x128 cnt Hat ltac:(wj_in)) as X.
  rewrite (wj_small _ Hcnt) in X. exact X. }
split; [apply (wj_cell _ _ _ _ _ 0xe0 _ Hat); wj_in|].
split; [apply (wj_cell _ _ _ _ _ 0x120 _ Hat); wj_in|].
(* R+0xd8: the cut list states ~(pp + 0x4014) as - pp - 0x4015 *)
split.
{ pose proof (wj_cell _ _ _ _ _ 0xd8 (- e_pp (x_e cx) - 0x4015) Hat ltac:(wj_in)) as X.
  replace (- e_pp (x_e cx) - 0x4015) with (- e_pp (x_e cx) - 0x4014 - 1) in X by ring. exact X. }
split; [apply (wj_cell _ _ _ _ _ 0xd0 _ Hat); wj_in|].
(* e62's bytes, pp's image with its len and n_ent cells, the frame's shadow *)
split; [exact He|].
split; [exact Hpp|].
split; [exact (hm_pp_len rsegs _ _ _ _ _ _ Hb Hent32 Hbody _ _ _ Hpp')|].
split.
{ intros H1. pose proof (hm_pp_n_ent rsegs _ _ _ _ _ _ Hb Hent32 Hbody _ _ _ Hpp') as X.
  rewrite (wj_pc_ents_first sh ps es H1) in X. exact X. }
split; [rewrite <- hw8_PJ; exact Hfsh|].
(* the geometry *)
split; [exact Bal|]. split; [exact Bapp|]. split; [exact B4096|]. split; [exact Bceil|].
split; [exact Fal|]. split; [exact Fapp|]. split; [exact F4096|]. split; [exact Fceil|].
split; [exact Hdis|].
split; [clear - Slo Slosp HRstk; lia|].
split; [exact HR32|].
split; [rewrite <- HeS; exact HRsz|].
split; [exact Ssp|].
split; [clear - Shi Shi47; lia|].
split; [exact HRstk|].
(* the model's bounds *)
split; [split; [apply Nat2Z.is_nonneg | exact HL]|].
split; [exact HL8|].
split; [exact Hwf|].
split; [exact Hes32|].
split; [exact Hescnt|].
split; [exact (proj2 Hcnt)|].
split; [exact Hfs|].
split; [reflexivity|].
split; [exact Hpw|]. split; [exact Hall|]. split; [exact Hes|]. exact Hps2.
Qed.
End w.

Print Assumptions wj_pc_ents.
Print Assumptions wj_pc_ents_first.
Print Assumptions wj_first_range.
Print Assumptions wj_small.
Print Assumptions wj_reg.
Print Assumptions wj_cell.
Print Assumptions hw8_J_facts.
