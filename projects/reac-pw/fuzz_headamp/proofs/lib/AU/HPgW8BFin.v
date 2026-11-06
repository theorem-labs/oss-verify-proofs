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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropKit.v; 215 of its 267 lines of code are new or changed and 359 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the end of the builder
   piece W8 of LLVMFuzzerTestOneInput (0x80c40), the statement hw8_finish_stmt of lib/AU/HPgW8BKit.v: from a state
   after the call of pod_write_ent, the record copy and the scope closers, the cut C 0x81888 (the pod loop's next
   turn) or, when the count is reached, the cut CL 0x82a18 (lib/AU/HPgSeg.v hsu_cut_C / hsu_cut_CL at the image's
   record headamp_himg_B), handed to their continuations hsu_from_C / hsu_from_CL. Proves no function (kind:
   segment lemma).

   HOW. The segment frame (hsu_core) moves from J's state (world W2) to the end state (world W3): the journal, the
   frames, the blocks, the I/O state and the meter (its transitivity, the law MTL) as the end state gives them, sp /
   gp / tp kept, and every byte outside the callees' stack [R - T_SEG_STK, R), the first block pp and e62's 13
   shadow granules shF + [66, 79) as at J, hence as at the segment's start outside M01's write set (hsu_E1, whose
   image range list holds the frame's 116 shadow bytes). The frame's shadow becomes hsu_P0 (J's hsu_PJ with
   granules 66 .. 78 := 0xf8, lib/AU/HPgMem.v hmu_sh_e62_out). J's location list moves to the end state because the
   registers it keeps are those of hw8_keepF (s0 x8, s1 = R x9, s2 x18, s3 x19, s4 x20, s6 x22, s8 x24, s9 x25,
   s11 x27) and every R-cell R + [0, 0x198) lies outside the changed set; the C list adds s7 = x23 = -8, s5 = x21 =
   J's a3 (x13, the cursor), s10 = x26 = J's t1 (x6, what is left) and a1 = x11 = the next pod index, the CL list
   s2 = x18 = pp + 0x4000. The pods written grow by J's pod (Model.ents_loop_S_end). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
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

(* the locations the piece leaves alone: a register of hw8_keepF, or an 8-byte cell of the real frame inside
   R + [0, 0x198) *)
Definition wf_okb (l : hd_loc) : bool :=
  match l with
  | LReg r => existsb (Z.eqb r) [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 25; 27]
  | LCell XR o => (0 <=? o) && (o <=? 0x190)
  | _ => false
  end.

Lemma wf_reg_keep : forall r, existsb (Z.eqb r) [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 25; 27] = true ->
  In (Z_to_bv 5 r) hw8_keepF.
Proof.
intros r Hr. apply existsb_exists in Hr. destruct Hr as (x & Hx & Hrx). apply Z.eqb_eq in Hrx. subst x.
unfold hw8_keepF. cbn [In] in Hx |- *.
repeat destruct Hx as [<-|Hx]; try contradiction;
repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

(* a fact of a list from two lists that cover it *)
Lemma wf_at_incl : forall (P : hd_loc * Z -> Prop) L1 L2 L, Forall P L1 -> Forall P L2 ->
  (forall x, In x L -> In x L1 \/ In x L2) -> Forall P L.
Proof.
intros P L1 L2 L H1 H2 Hi. apply Forall_forall. intros x Hx.
destruct (Hi x Hx) as [Hx'|Hx'];
[exact (proj1 (Forall_forall _ _) H1 x Hx') | exact (proj1 (Forall_forall _ _) H2 x Hx')].
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* a register named by Z_to_bv 5 r (hd_at's form) is the register named by the literal *)
Lemma wf_getr5 : forall (regs : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z -> getr regs (Z_to_bv 5 z) = getr regs r.
Proof.
intros regs r z H. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. subst z.
unfold bv_wrap. apply Z.mod_small. pose proof (bv_unsigned_in_range 5 r) as Hr. exact Hr.
Qed.

(* a register of a cut list, by membership *)
Lemma wf_reg : forall H mem (regs : bvmap 5 word) e (L : list (hd_loc * Z)) r v,
  Forall (fun f => hd_at rsegs H mem regs e (fst f) (snd f)) L -> In (LReg r, v) L ->
  getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HF Hin. exact (proj1 (Forall_forall _ _) HF _ Hin). Qed.

(* the facts of a list whose locations the piece leaves alone, from one state to the next *)
Lemma wf_at_move : forall (H H' : word -> bool) mem2 mem3 regs2 regs3 e L,
  (forall r0, In r0 hw8_keepF -> getr regs3 r0 = getr regs2 r0) ->
  (forall o j, 0 <= o <= 0x190 -> 0 <= j < 8 ->
     aview rsegs H' mem3 (e_R e + o + j) = aview rsegs H mem2 (e_R e + o + j)) ->
  forallb (fun f => wf_okb (fst f)) L = true ->
  Forall (fun f => hd_at rsegs H mem2 regs2 e (fst f) (snd f)) L ->
  Forall (fun f => hd_at rsegs H' mem3 regs3 e (fst f) (snd f)) L.
Proof.
intros H H' mem2 mem3 regs2 regs3 e L Hk Hc Hb HL.
induction L as [|[l v] L IH]; [constructor|].
cbn [forallb] in Hb. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2].
apply Forall_cons_iff in HL. destruct HL as [H1 H2].
constructor; [|exact (IH Hb2 H2)].
cbn [fst snd] in Hb1, H1 |- *. destruct l as [r|b o].
- cbn [wf_okb] in Hb1. cbn [hd_at] in H1 |- *. rewrite Hk by (apply wf_reg_keep; exact Hb1). exact H1.
- destruct b; cbn [wf_okb] in Hb1; try discriminate Hb1.
  apply andb_prop in Hb1. destruct Hb1 as [Ho1 Ho2]. apply Z.leb_le in Ho1. apply Z.leb_le in Ho2.
  apply (hm_at_kept rsegs H mem2 H' mem3 regs2 regs3 e (LCell XR o) v H1).
  cbn [hm_keeps hd_xv]. intros j Hj. apply Hc; lia.
Qed.

(* the separation facts of the segment's start: R above the allocator's ceiling, the first block and the frame's
   shadow bytes below it, and the first block apart from the frame's shadow bytes (both application memory) *)
Lemma wf_bounds : forall cx sh, hsu_pre rsegs B headamp_himg_B cx sh ->
  spZ (x_regs cx) = e_R (x_e cx) /\
  alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ e_R (x_e cx) + 0x220 <= 2 ^ 47 /\
  e_pp (x_e cx) + PP_SIZE <= alloc_ceiling /\
  0 <= shadow_addr (e_F (x_e cx)) /\ shadow_addr (e_F (x_e cx)) + 128 <= alloc_ceiling /\
  (e_pp (x_e cx) + PP_SIZE <= shadow_addr (e_F (x_e cx)) \/
   shadow_addr (e_F (x_e cx)) + 128 <= e_pp (x_e cx)).
Proof.
intros cx sh HP. unfold hsu_pre, hd_seg_pre in HP.
destruct HP as (HJ0 & _ & Hsp & _ & _ & HS & _ & HRsz & HRstk & Hown & HF & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & (_ & Hppin & _)).
destruct HJ0 as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
destruct Hastk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (al_blocks rsegs B (YG0q.AR_laws_ok rsegs B) _ _ _ _ _ _ _ HAR Hppin) as (_ & _ & Hpceil & Hpapp & _).
assert (Hin : In (hi_cid headamp_himg_B, x_pos cx) (frames (x_Sc cx)))
  by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (al_frames rsegs B (YG0q.AR_laws_ok rsegs B) _ _ _ _ _ _ _ HAR Hin) as (_ & Hfapp & _).
rewrite <- HF in Hfapp. change (fs_frame_bytes (hi_cid headamp_himg_B)) with 1024 in Hfapp.
change (req_size PP_SIZE) with 19744 in Hpceil, Hpapp.
change (hi_rsz headamp_himg_B) with 0x220 in HRsz.
pose proof YM05.alloc_ceiling_value as [Hc _].
assert (HT : T_SEG_STK = 16384) by reflexivity.
split.
{ apply (f_equal (@bv_unsigned 64)) in Hsp. unfold spZ. etransitivity; [exact Hsp|].
  apply unsigned_lit_small. lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp, Hfapp. unfold shadow_addr, SHADOW_OFF, PP_SIZE.
destruct Hpapp as (Hp1 & [Hp2 | (Hp3 & Hp4)]); destruct Hfapp as (Hf1 & [Hf2 | (Hf3 & Hf4)]);
  (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [lia|]);
  first [left; lia | right; lia].
Qed.

(* the segment frame at the end, from J's and the end state's facts *)
Lemma wf_core : forall cx sh ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
  hsu_pre rsegs B headamp_himg_B cx sh ->
  hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly3 S3 W3 mem3 md3 (x_k cx) ->
  frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 ->
  mo_le MT S2 S3 0 ->
  (forall r0 : bv 5, In r0 hw8_keepF -> getr regs3 r0 = getr regs2 r0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) ->
     ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + PP_SIZE) ->
     ~ (shadow_addr (e_F (x_e cx)) + 66 <= a < shadow_addr (e_F (x_e cx)) + 79) ->
     aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly3 S3 W3 regs3 mem3 md3.
Proof using MTL.
intros cx sh ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HP HC HAJ Hfr3 Hperm3 Hio3 Hmo3 Hkeep Hmem3.
pose proof (wf_bounds cx sh HP) as (Hsp & _).
unfold hsu_core, hsu_mid in HC |- *.
destruct HC as (_ & Hr234 & Hfrm & Hperm & Hio2 & Hmo & Hmem).
split; [exact HAJ|]. split.
{ intros r0 Hr0. rewrite <- (Hr234 r0 Hr0). apply Hkeep.
  destruct Hr0 as [ -> | [ -> | -> ] ]; unfold hw8_keepF; cbn [In];
    repeat (first [left; apply bv_eq; reflexivity | right]). }
split; [rewrite Hfr3; exact Hfrm|].
split; [eapply Permutation_trans; [exact Hperm3 | exact Hperm]|].
split; [exact (same_io_trans _ _ _ Hio2 Hio3)|].
split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
intros a Ha Hstk HE1. rewrite <- (Hmem a Ha Hstk HE1). apply Hmem3; [exact Ha | | |].
- intros Hx. apply Hstk. rewrite Hsp. lia.
- intros Hx. apply HE1. unfold hsu_E1. right. exact Hx.
- intros Hx. apply HE1. unfold hsu_E1. left. unfold hd_inw.
  change (hi_w1 headamp_himg_B) with [(XF 0, 0x20, 0x258); (XShF, 0, 116); (XR, 0, 0x198)].
  apply Exists_cons_tl, Exists_cons_hd. cbn [fst snd hd_xv]. lia.
Qed.

(* the frame's shadow bytes at the end: e62's 13 granules closed again (0xf8), the others as at J *)
Lemma wf_fsh : forall cx sh (W2 W3 : world rsegs) mem2 mem3,
  hsu_pre rsegs B headamp_himg_B cx sh ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) ->
     ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + PP_SIZE) ->
     ~ (shadow_addr (e_F (x_e cx)) + 66 <= a < shadow_addr (e_F (x_e cx)) + 79) ->
     aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  (forall o, 66 <= o < 79 -> aview rsegs (w_H W3) mem3 (shadow_addr (e_F (x_e cx)) + o) = Some 248) ->
  hd_fsh rsegs (w_H W2) mem2 (e_F (x_e cx)) (hmu_sh false false false false false true false false) ->
  hd_fsh rsegs (w_H W3) mem3 (e_F (x_e cx)) (hmu_sh false false false false false false false false).
Proof.
intros cx sh W2 W3 mem2 mem3 HP Hfr Hsh HJ.
pose proof (wf_bounds cx sh HP) as (_ & HB1 & HB2 & HB3 & HB4 & HB5 & HB6).
pose proof YM05.alloc_ceiling_value as [HAC _].
assert (HT : T_SEG_STK = 16384) by reflexivity.
rewrite <- (hmu_sh_e62_out false false false false false true false false).
apply (hm_fsh_set rsegs (w_H W2) mem2 (w_H W3) mem3 _ _ 66 13 248 HJ).
- intros j Hj. change (Z.of_nat 66) with 66 in Hj. change (Z.of_nat (66 + 13)) with 79 in Hj. apply Hsh. lia.
- intros j Hj Hn. rewrite hmu_sh_len in Hj. change (Z.of_nat 116) with 116 in Hj.
  change (Z.of_nat 66) with 66 in Hn. change (Z.of_nat (66 + 13)) with 79 in Hn.
  apply Hfr; clear - Hj Hn HB1 HB2 HB3 HB4 HB5 HB6 HAC HT; unfold PP_SIZE in *; lia.
Qed.

(* ===================================== the piece's end ===================================== *)
Lemma hw8_finish : hw8_finish_stmt B MT.
Proof using MTL.
unfold hw8_finish_stmt.
intros cx POST rest i k ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r ed ly3 S3 W3 regs3 mem3 md3 last
  HS Hi Hk HJ HC HCL Hlast HAJ3 Hfr3 Hperm3 Hio3 Hmo3 Hkeep H21 H26 H11 H23 Hmem3 Hsh3 Hpp3.
destruct HS as (HP & _ & _ & _).
pose proof (wf_bounds cx _ HP) as (_ & HB1 & HB2 & HB3 & HB4 & HB5 & _).
pose proof YM05.alloc_ceiling_value as [HAC _].
assert (HT : T_SEG_STK = 16384) by reflexivity.
destruct HJ as (Hbase & HJat & HJsh & _ & _ & Hed & Hedwf).
destruct Hbase as (Hcore & Hin & Hsr & _ & Hwf & Hlen & Hps & Htie & Hsh0 & Hnp & Hpsnp & Hnp3 & Hsh7 & Hps2
  & Hcnt & Hes & _ & Hescnt).
(* the segment frame and the frame's shadow at the end *)
pose proof (wf_core cx _ ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HP Hcore HAJ3 Hfr3 Hperm3 Hio3 Hmo3
  Hkeep Hmem3) as Hcore3.
assert (Hfsh3 : hd_fsh rsegs (w_H W3) mem3 (e_F (x_e cx)) (hsu_P0 headamp_himg_B)).
{ rewrite hw8_P0. apply (wf_fsh cx _ W2 W3 mem2 mem3 HP Hmem3 Hsh3). rewrite <- hw8_PJ. exact HJsh. }
(* J's locations the piece leaves alone, at the end state *)
assert (Hcell : forall o j, 0 <= o <= 0x190 -> 0 <= j < 8 ->
  aview rsegs (w_H W3) mem3 (e_R (x_e cx) + o + j) = aview rsegs (w_H W2) mem2 (e_R (x_e cx) + o + j)).
{ intros o j Ho Hj. apply Hmem3; clear - Ho Hj HB1 HB2 HB3 HB5 HAC HT; unfold PP_SIZE in *; lia. }
unfold hsu_at_cx, hsu_at in HJat.
assert (HLk : Forall (fun f => hd_at rsegs (w_H W2) mem2 regs2 (x_e cx) (fst f) (snd f))
  (hsu_L_Dc rsegs cx sh np ps cnt es
   ++ [(LReg 18, e_pp (x_e cx) + Layout.OFF_LEN); (LReg 20, e_F (x_e cx) + HSU_E62)])).
{ eapply incl_Forall; [|exact HJat]. intros x Hx. rewrite !in_app_iff in Hx. rewrite !in_app_iff.
  cbn [In] in Hx |- *. tauto. }
pose proof (fun Hb => wf_at_move (w_H W2) (w_H W3) mem2 mem3 regs2 regs3 (x_e cx) _ Hkeep Hcell Hb HLk) as HLk3.
specialize (HLk3 eq_refl).
(* the registers the piece sets *)
assert (E13 : getr regs2 (Z_to_bv 5 13) = w64 (hsu_cur rsegs cx rest r))
  by (apply (wf_reg _ _ _ _ _ 13 _ HJat); apply in_or_app; right; left; reflexivity).
assert (E6 : getr regs2 (Z_to_bv 5 6) = w64 (Z.of_nat (length r)))
  by (apply (wf_reg _ _ _ _ _ 6 _ HJat); apply in_or_app; right; right; left; reflexivity).
assert (HL : length (es ++ [ed]) = S k) by (rewrite length_app, Hk; cbn [length]; lia).
assert (HNew : Forall (fun f => hd_at rsegs (w_H W3) mem3 regs3 (x_e cx) (fst f) (snd f))
  [(LReg 23, -8); (LReg 21, hsu_cur rsegs cx rest r); (LReg 26, Z.of_nat (length r));
   (LReg 11, Z.of_nat (length (es ++ [ed])))]).
{ repeat apply Forall_cons; cbn [fst snd hd_at]; try apply Forall_nil.
  - rewrite (wf_getr5 regs3 23%bv 23) by reflexivity. exact H23.
  - rewrite (wf_getr5 regs3 21%bv 21) by reflexivity. rewrite <- E13.
    rewrite (wf_getr5 regs2 13%bv 13) by reflexivity. exact H21.
  - rewrite (wf_getr5 regs3 26%bv 26) by reflexivity. rewrite <- E6.
    rewrite (wf_getr5 regs2 6%bv 6) by reflexivity. exact H26.
  - rewrite HL. rewrite (wf_getr5 regs3 11%bv 11) by reflexivity. exact H11. }
(* the record with one more pod, and its tie to the input *)
assert (Htie' : hsu_pod_tie sh ps cnt (es ++ [ed]) rest r).
{ destruct Htie as (sel & c & r1 & r2 & T1 & T2 & T3 & T4 & T5 & T6).
  exists sel, c, r1, r2. refine (conj T1 (conj T2 (conj T3 (conj T4 (conj T5 _))))).
  replace (length (es ++ [ed])) with (S (length es)) by (rewrite length_app; cbn [length]; lia).
  rewrite ents_loop_S_end, T6. cbv beta iota. rewrite <- Hed. reflexivity. }
assert (Hes' : Forall ent_wf (es ++ [ed]))
  by (apply Forall_app; split; [exact Hes | constructor; [exact Hedwf | constructor]]).
destruct last.
- (* the count is reached: CL *)
  apply Z.eqb_eq in Hlast.
  change (if true then HW8_CL else HW8_C) with (bi_CL headamp_bld_B).
  refine (HCL ly3 S3 W3 regs3 mem3 md3 sh np ps cnt (es ++ [ed]) r Hi _).
  unfold hsu_cut_CL.
  split; [exact Hcore3|]. split.
  { unfold hsu_at_cx, hsu_at. apply (wf_at_incl _ _ _ _ HLk3 HNew).
    intros x Hx. unfold hsu_L_Dc. rewrite !in_app_iff in Hx. rewrite !in_app_iff. cbn [In] in Hx |- *. tauto. }
  split; [exact Hfsh3|]. split; [exact Hpp3|].
  split; [exact Hin|]. split; [exact Hsr|]. split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hps|].
  split; [exact Htie'|]. split; [exact Hsh0|]. split; [exact Hnp|]. split; [exact Hpsnp|]. split; [exact Hnp3|].
  split; [exact Hsh7|]. split; [exact Hps2|]. split; [exact Hcnt|]. split; [exact Hes'|].
  rewrite HL. exact Hlast.
- (* the next turn: C *)
  apply Z.eqb_neq in Hlast.
  change (if false then HW8_CL else HW8_C) with (bi_C headamp_bld_B).
  refine (HC ly3 S3 W3 regs3 mem3 md3 sh np ps cnt (es ++ [ed]) r Hi HL _).
  unfold hsu_cut_C, hsu_pod_base.
  split.
  { split; [exact Hcore3|]. split; [exact Hin|]. split; [exact Hsr|]. split; [exact Hsr|]. split; [exact Hwf|].
    split; [exact Hlen|]. split; [exact Hps|]. split; [exact Htie'|]. split; [exact Hsh0|]. split; [exact Hnp|].
    split; [exact Hpsnp|]. split; [exact Hnp3|]. split; [exact Hsh7|]. split; [exact Hps2|].
    split; [exact Hcnt|]. split; [exact Hes'|].
    rewrite HL. clear - Hk Hescnt Hlast Hcnt. split; lia. }
  split.
  { unfold hsu_at_cx, hsu_at. apply (wf_at_incl _ _ _ _ HLk3 HNew).
    intros x Hx. unfold hsu_L_pod in Hx. unfold hsu_L_Dc. rewrite !in_app_iff in Hx. rewrite !in_app_iff.
    cbn [In] in Hx |- *. tauto. }
  split; [exact Hfsh3 | exact Hpp3].
Qed.
End w.

Print Assumptions wf_reg_keep.
Print Assumptions wf_at_incl.
Print Assumptions wf_getr5.
Print Assumptions wf_reg.
Print Assumptions wf_at_move.
Print Assumptions wf_bounds.
Print Assumptions wf_core.
Print Assumptions wf_fsh.
Print Assumptions hw8_finish.
