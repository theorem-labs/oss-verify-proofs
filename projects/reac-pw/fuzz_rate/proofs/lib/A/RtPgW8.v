(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v; 344 of its 419 lines of code are new or changed and 515 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5CloseP.v at ada533759b23 for
   reac-pw/fuzz_rate image A: the piece is rate's W8 instead of role's Struct close, so the cut it starts from
   is RtPgSeg's J and the two cuts it ends at are C and CL; the block it runs is lib/A/RtPgW8Core.v's rw8_core
   instead of a single engine run; the first block's new image comes from lib/A/RtPgW8Img.v's rw8_img_step. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a): the piece lemma of "write + record",
   J 0x81e00 -> C 0x8127c / CL 0x82484, as lib/A/RtPgSeg.v states it (rs_piece_W8_stmt). Proves no function
   (kind: segment lemma).

   HOW. The cut J gives the code's facts (the registers and the real frame's cells of RtPgSeg's rs_L_Dc, the
   first block's image, the frame object e and the frame's shadow with e in scope); rw8_core runs the whole
   piece from them to C or to CL, by the pod loop's latch `bne a1,a0`; the end cut is rebuilt from its post:
   the journal and frame part (RtPgSeg's rs_core, whose write set contains the piece's), the (location, value)
   facts (kept, and the three the piece sets), the frame's shadow back to the prologue's pattern, the first
   block's image one pod further on (Model.pc_buf_pod, Model.pc_ents_pod and rw8_img_step) and the model
   facts (Model.ents_loop's step). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgMem RtPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgSeg RtPgW8Kit RtPgW8Img RtPgW8Core.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

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

(* ======================================== the model at the write ======================================== *)
(* the first block's length at a pod-loop cut, and its lower bound *)
Lemma rw8_buf_open_len : forall sh ps es,
Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) =
Z.of_nat (length (pc_buf (PbCut sh ps None))) + 16 + Z.of_nat (length (flat_map enc_pod es)).
Proof.
intros sh ps es. unfold pc_buf, open_bytes. cbn [pc_shape pc_props pc_open].
rewrite app_nil_r, !zlen_app, !zlen_le32. lia.
Qed.
Lemma rw8_plen_lo : forall sh ps, sh <> 7 -> 16 <= Z.of_nat (length (pc_buf (PbCut sh ps None))).
Proof.
intros sh ps Hsh. unfold pc_buf, body_bytes, hdr_bytes, open_bytes. cbn [pc_shape pc_props pc_open].
replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact Hsh).
rewrite !app_nil_r, !zlen_app, !zlen_le32. pose proof (Zle_0_nat (length (flat_map (prop_bytes sh) ps))). lia.
Qed.
(* one more pod of the open Struct: the bytes, the recorded pods and the model's step *)
Lemma rw8_ents_step : forall sh ps cnt es ed rest rr r,
rs_pod_tie sh ps cnt es rest rr -> (ed, r) = ent_build rr ->
rs_pod_tie sh ps cnt (es ++ [ed]) rest r.
Proof.
intros sh ps cnt es ed rest rr r (sel & c & r1 & r2 & Hs1 & Hc & Hcnt & Hm4 & Hb4 & He) Hed.
exists sel, c, r1, r2. split; [exact Hs1|]. split; [exact Hc|]. split; [exact Hcnt|].
split; [exact Hm4|]. split; [exact Hb4|].
rewrite length_app. cbn [length]. rewrite Nat.add_1_r, ents_loop_S_end, He, <- Hed. reflexivity.
Qed.
Lemma rw8_first_ents : forall sh ps es, rs_first ps = 1 -> pc_ents (PbCut sh ps (Some es)) = es.
Proof.
intros sh ps es H. unfold rs_first in H. unfold pc_ents, first_params. cbn [pc_props pc_open].
destruct (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps) eqn:E; cbn in H; [discriminate|].
assert (Hf : find (fun kv => fst kv =? POD_PROP_PARAMS) ps = None).
{ clear H. induction ps as [|x l IH]; cbn in *; [reflexivity|].
  apply orb_false_iff in E as [E1 E2]. rewrite E1. exact (IH E2). }
rewrite Hf. reflexivity.
Qed.
Lemma rw8_notfirst_ents : forall sh ps es ed, rs_first ps <> 1 ->
pc_ents (PbCut sh ps (Some (es ++ [ed]))) = pc_ents (PbCut sh ps (Some es)).
Proof.
intros sh ps es ed H. apply pc_ents_pod_other. unfold pc_first. cbn [pc_props].
unfold rs_first in H. destruct (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps); cbn in *; [reflexivity|lia].
Qed.
Lemma rw8_first_pod : forall sh ps es ed, rs_first ps = 1 ->
pc_ents (PbCut sh ps (Some (es ++ [ed]))) = pc_ents (PbCut sh ps (Some es)) ++ [ed].
Proof.
intros sh ps es ed H. apply pc_ents_pod. unfold pc_first. cbn [pc_props].
unfold rs_first in H. destruct (existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps); cbn in *; [lia|reflexivity].
Qed.
Lemma rw8_ents_wf : forall sh ps es, rs_wf sh ps -> Forall ent_wf es ->
Forall ent_wf (pc_ents (PbCut sh ps (Some es))).
Proof.
intros sh ps es (_ & Hk & He & _) Hes. unfold pc_ents. cbn [pc_props pc_open].
destruct (first_params ps) as [[i|es0]|] eqn:E; try constructor; [|exact Hes].
unfold first_params in E. destruct (find _ _) as [kv|] eqn:Ef; [|discriminate]. cbn in E.
apply find_some in Ef as [Hin _]. apply all_ents_Forall in He. rewrite Forall_forall in He.
specialize (He kv Hin). injection E as E. rewrite E in He. cbn [ents_of] in He. exact He.
Qed.
Lemma rw8_ents_len : forall sh ps es, rs_wf sh ps -> (length es <= 32)%nat ->
(length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat.
Proof.
intros sh ps es (_ & Hk & _ & _) Hes. unfold pc_ents. cbn [pc_props pc_open].
destruct (first_params ps) as [[i|es0]|] eqn:E; cbn [length]; try lia.
unfold first_params in E. destruct (find _ _) as [kv|] eqn:Ef; [|discriminate]. cbn in E.
apply find_some in Ef as [Hin _]. rewrite Forall_forall in Hk. destruct (Hk kv Hin) as [_ Hv].
injection E as E. rewrite E in Hv. exact Hv.
Qed.
Lemma rw8_body96 : forall es, Forall ent_wf es -> Forall (fun e => (length (e_body e) <= 96)%nat) es.
Proof.
intros es H. eapply Forall_impl; [|exact H]. intros e (_ & Hb & Hs). rewrite Hb. lia.
Qed.

(* ======================================== reading a cut's facts ======================================== *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma rw8_at_reg : forall H mem regs e (L : list (rt_loc * Z)) r v,
rs_at rsegs H mem regs e L -> In (LReg r, v) L -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros H mem regs e L r v HL Hin. exact (proj1 (Forall_forall _ _) HL _ Hin). Qed.
Lemma rw8_at_cell : forall H mem regs e (L : list (rt_loc * Z)) o v,
rs_at rsegs H mem regs e L -> In (LCell XR o, v) L ->
val_mem rsegs (mrestrict H mem) (q_R e + o) 8 (v mod 2 ^ 64).
Proof. intros H mem regs e L o v HL Hin. exact (proj1 (Forall_forall _ _) HL _ Hin). Qed.
Lemma rw8_getr5 : forall (regs : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z ->
getr regs (Z_to_bv 5 z) = getr regs r.
Proof.
intros regs r z H. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. subst z.
unfold bv_wrap. apply Z.mod_small. pose proof (bv_unsigned_in_range 5 r) as Hr. exact Hr.
Qed.
End r.

(* membership in the cut J's list, and in the end cuts' lists *)
Ltac rw8_notin :=
  try unfold rw8_clobJ;
  let H := fresh "H" in intros H; cbn [In] in H;
  repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; vm_compute in H; discriminate H|]);
  exact H.
Ltac rw8_nz := vm_compute; lia.
Ltac rw8_inJ :=
cbn [rs_L_Dc rs_L_Dc0 rs_Rc0 rs_Kc rs_Hc rs_podc rs_L_pod rs_Rc rs_cur2 app In fst snd];
repeat (first [left; reflexivity | right]).
Ltac rw8_kept Hat Hkeep Kc := lazymatch goal with |- rt_at _ _ _ _ _ ?l ?v =>
  apply (rtm_at_kept rsegs _ _ _ _ _ _ _ l v (proj1 (Forall_forall _ _) Hat (l, v) ltac:(rw8_inJ)));
  cbn [rtm_keeps rt_xv];
  first [ apply Hkeep; [rw8_nz | rw8_notin]
        | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply Kc; lia ] end.

(* ======================================== the segment's start ======================================== *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Lemma rw8_pre_facts : forall cx, rs_pre rsegs B cx ->
  rw8_geo (x_STK cx) (x_sp0 cx) (x_own cx) (x_lyc cx) (q_R (x_e cx)) (q_F (x_e cx)) (x_pos cx) /\
  getr (x_regs cx) 2 = w64 (q_R (x_e cx)) /\ getr (x_regs cx) 3 = w64 (as_gp B) /\
  getr (x_regs cx) 4 = w64 (as_tp B) /\
  In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx)) /\
  ~ In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_ly cx) (x_S cx)) /\
  4096 <= q_pp (x_e cx) /\ q_pp (x_e cx) + Layout.PP_SIZE <= alloc_ceiling /\
  4096 <= q_F (x_e cx) /\ q_F (x_e cx) + 512 <= alloc_ceiling /\
  in_app (q_pp (x_e cx)) Layout.PP_SIZE.
Proof using LAWS.
intros cx Hpre. unfold rs_pre, rt_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & HR16 & HRs & HRstk & Hown & HF & Hpp0 & Hpp & Hhdr & Hro &
  Hglobs & Hrz & Hstrs & Hcells & Hrom & Hout & Hi32 & Hu64).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HST0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
cbn [hi_cid hi_rsz rate_himg_A] in *.
assert (Hin3 : In (3, x_pos cx) (frames (x_Sc cx)))
  by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (x_pos cx) HAR Hin3) as (Hal32 & HappF & _ & _).
change (fs_frame_bytes 3) with 512 in HappF. rewrite <- HF in Hal32, HappF.
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 3 (x_pos cx) HAR Hin3) as (HF4096 & HFceil & _).
change (fs_frame_bytes 3) with 512 in HFceil. rewrite <- HF in HF4096, HFceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (q_pp (x_e cx)) Layout.PP_SIZE HAR Hpp)
  as (_ & Hp4096 & Hpceil & Happ & _ & _).
change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hpceil, Happ.
unfold T_SEG_STK, ASTACK in HRstk.
split.
{ unfold rw8_geo. split; [exact HR16|]. split; [unfold T_SEG_STK, ASTACK; lia|].
  split; [lia|]. split; [unfold T_SEG_STK, ASTACK, kHighMemBeg; lia|].
  split; [exact Hown|]. split; [exact HF|]. split; [exact HappF | exact Hal32]. }
split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact Hpp|]. split; [exact Hout|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact Happ].
Qed.
End s.

(* ======================================== the piece ======================================== *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis CORE : rw8_core_stmt B MT.

Lemma rw8_piece : rs_piece_W8_stmt rsegs B MT.
Proof using MTL LAWS CORE.
unfold rs_piece_W8_stmt. intros cx POST rest i k Hst HC HCL.
unfold rs_from_J. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r ed Hi Hk Hcut.
pose proof Hst as (Hpre & HfshS & HcutS & HlenS & HinS).
destruct (rw8_pre_facts B LAWS cx Hpre)
  as (HG & P2 & P3 & P4 & Hpp & Hfresh & Hp4096 & Hpceil & HF4096 & HFceil & Happ).
destruct Hcut as (Hbase & Hat & Hfsh & Hppat & Hent & Hed & Hwfed).
pose proof Hbase as (Hcore & Hin & Hsuf & Hsufrr & Hwf & Hlen0 & Hps & Htie & Hsh & Hnp & Hpsnp & Hnp3 &
  Hsh7 & Hps2 & Hcnt & Hesw & Hesl & Hescnt).
pose proof Hcore as (HJ & Hr234 & Hfr & Hperm & Hio & Hmo & Hmem).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown3 & HFeq & HFapp & HF32).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
unfold T_SEG_STK, ASTACK, kHighMemBeg in HSTK, HRk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hcl.
assert (HPS : Layout.PP_SIZE = 19744) by reflexivity. rewrite HPS in Hpceil.
(* the model's lengths *)
set (len := Z.of_nat (length (pc_buf (PbCut sh ps (Some es))))) in *.
pose proof Hwf as (Hsh8 & Hkw & Haew & Hpsl).
assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps)
  by (eapply Forall_impl; [|exact Hkw]; intros kv [_ X]; exact X).
destruct (pc_buf_len_open sh ps es Hv Haew Hesw) as [Hblen Hbdiv].
fold len in Hblen, Hbdiv.
assert (Hlen8 : len mod 8 = 0) by (destruct Hbdiv as [q Hq]; rewrite Hq; apply Z_mod_mult).
assert (Hlenlo : 32 <= len).
{ pose proof (rw8_buf_open_len sh ps es) as E. fold len in E.
  pose proof (rw8_plen_lo sh ps Hsh7) as Hp.
  pose proof (Zle_0_nat (length (flat_map enc_pod es))). lia. }
assert (Hlenhi : len + 56 <= 5440) by lia.
assert (Henc_pod_len : Z.of_nat (length (enc_pod ed)) = 8 + e_size ed + pad8 (e_size ed))
  by (apply zlen_enc_pod; exact Hwfed).
pose proof Hwfed as (Htyw & Hblw & Hszw).
assert (Hpd : 0 <= pad8 (e_size ed) < 8) by apply pad8_bound.
assert (Hmod : forall v, 0 <= v < 2 ^ 64 -> v mod 2 ^ 64 = v) by (intros; apply Z.mod_small; lia).
assert (Hfr01 : rs_first ps = 0 \/ rs_first ps = 1)
  by (unfold rs_first; destruct (negb _); cbn; lia).
assert (HsFb : 2147450880 <= shadow_addr (q_F (x_e cx)) /\ shadow_addr (q_F (x_e cx)) + 64 <= 17594332446784).
{ unfold shadow_addr.
  assert (HFd : 0 <= q_F (x_e cx) / 8 <= 17592184995840)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold SHADOW_OFF. lia. }
assert (Hshd : forall i, 0 <= i < 64 ->
  ~ (q_pp (x_e cx) <= shadow_addr (q_F (x_e cx)) + i < q_pp (x_e cx) + 19744)).
{ intros ii Hii. unfold shadow_addr.
  assert (HFd : 0 <= q_F (x_e cx) / 8 <= 17592184995840)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold in_app in Happ. rewrite HPS in Happ. rewrite C3 in *.
  unfold kLowShadowBeg, SHADOW_OFF, kLowMemEnd in *. lia. }
assert (Hshr : 0 <= Z.shiftr (q_pp (x_e cx) + 0x4d14) 3 < 2 ^ 64).
{ rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; lia. }
assert (Hrlen : 0 <= Z.of_nat (length r) < 2 ^ 64).
{ destruct Hin as (Hl & _ & _ & _ & _ & Hs0 & Hs63 & _). destruct Hsuf as (j & Hj & ->).
  rewrite length_skipn. lia. }
(* ---- the cut's registers and real-frame cells ---- *)
unfold rs_at_cx in Hat.
pose proof (rw8_at_reg _ _ _ _ _ 9 (q_R (x_e cx)) Hat ltac:(rw8_inJ)) as A9.
pose proof (rw8_at_reg _ _ _ _ _ 18 SHADOW_OFF Hat ltac:(rw8_inJ)) as A18.
pose proof (rw8_at_reg _ _ _ _ _ 19 (q_F (x_e cx) + 0xe0) Hat ltac:(rw8_inJ)) as A19.
pose proof (rw8_at_reg _ _ _ _ _ 20 (shadow_addr (q_F (x_e cx))) Hat ltac:(rw8_inJ)) as A20.
pose proof (rw8_at_reg _ _ _ _ _ 23 (q_pp (x_e cx) + 0x4000) Hat ltac:(rw8_inJ)) as A23.
pose proof (rw8_at_reg _ _ _ _ _ 27 (q_pp (x_e cx)) Hat ltac:(rw8_inJ)) as A27.
pose proof (rw8_at_reg _ _ _ _ _ 22 (shadow_addr (q_pp (x_e cx) + 0x4000)) Hat ltac:(rw8_inJ)) as A22.
pose proof (rw8_at_reg _ _ _ _ _ 24 (Z.of_nat (length r)) Hat ltac:(rw8_inJ)) as A24.
pose proof (rw8_at_reg _ _ _ _ _ 26 (- 0x4001) Hat ltac:(rw8_inJ)) as A26.
assert (A26' : getr regs2 26 = w64 ((- 0x4001) mod 2 ^ 64)).
{ rewrite <- (rw8_getr5 regs2 (26%bv) 26 eq_refl), A26. unfold w64. rewrite Z_to_bv_mod64. reflexivity. }
pose proof (rw8_at_cell _ _ _ _ _ 0xa0 (q_pp (x_e cx) + 0x4014) Hat ltac:(rw8_inJ)) as Va0.
pose proof (rw8_at_cell _ _ _ _ _ 0xa8 (Z.shiftr (q_pp (x_e cx) + 0x4d14) 3) Hat ltac:(rw8_inJ)) as Va8.
pose proof (rw8_at_cell _ _ _ _ _ 0xb8 (q_pp (x_e cx) + 0x4d14) Hat ltac:(rw8_inJ)) as Vb8.
pose proof (rw8_at_cell _ _ _ _ _ 0xf0 cnt Hat ltac:(rw8_inJ)) as Vf0.
pose proof (rw8_at_cell _ _ _ _ _ 0x108 (q_F (x_e cx) + 0xf8) Hat ltac:(rw8_inJ)) as V108.
pose proof (rw8_at_cell _ _ _ _ _ 0x110 (rs_first ps) Hat ltac:(rw8_inJ)) as V110.
pose proof (rw8_at_cell _ _ _ _ _ 0x118 (- 0x4001) Hat ltac:(rw8_inJ)) as V118.
pose proof (rw8_at_cell _ _ _ _ _ 0x128 (Z.of_nat (length es)) Hat ltac:(rw8_inJ)) as V128.
pose proof (rw8_at_cell _ _ _ _ _ 0x130 (- 0x3ffd) Hat ltac:(rw8_inJ)) as V130.
pose proof (rw8_at_cell _ _ _ _ _ 0x138 (q_F (x_e cx) + 0xf0) Hat ltac:(rw8_inJ)) as V138.
rewrite Hmod in Va0, Va8, Vb8, Vf0, V108, V110, V128, V138 by lia.
assert (R2_2 : getr regs2 2 = w64 (q_R (x_e cx))).
{ rewrite <- (rw8_getr5 regs2 (2%bv) 2 eq_refl), (Hr234 2 (or_introl eq_refl)),
    (rw8_getr5 (x_regs cx) (2%bv) 2 eq_refl). exact P2. }
assert (R2_3 : getr regs2 3 = w64 (as_gp B)).
{ rewrite <- (rw8_getr5 regs2 (3%bv) 3 eq_refl), (Hr234 3 (or_intror (or_introl eq_refl))),
    (rw8_getr5 (x_regs cx) (3%bv) 3 eq_refl). exact P3. }
assert (R2_4 : getr regs2 4 = w64 (as_tp B)).
{ rewrite <- (rw8_getr5 regs2 (4%bv) 4 eq_refl), (Hr234 4 (or_intror (or_intror eq_refl))),
    (rw8_getr5 (x_regs cx) (4%bv) 4 eq_refl). exact P4. }
assert (HG2 : rw8_geo (x_STK cx) (x_sp0 cx) (x_own cx) ly2 (q_R (x_e cx)) (q_F (x_e cx)) (x_pos cx)).
{ assert (Hpre' := Hpre). unfold rs_pre, rt_seg_pre in Hpre'. destruct Hpre' as (HJ0 & _).
  pose proof HJ0 as (_ & Hlyc & _). pose proof HJ as (_ & Hly2 & _).
  exact (rw8_geo_step (x_STK cx) (x_sp0 cx) (x_own cx) (x_lyc cx) ly2 (q_R (x_e cx)) (q_F (x_e cx))
    (x_pos cx) _ (x_ly cx) HG Hlyc Hly2). }
assert (Hpp2 : In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm) Hpp).
assert (Hsp : spZ (x_regs cx) = q_R (x_e cx))
  by (unfold spZ; rewrite P2; unfold w64; apply unsigned_lit_small; lia).
(* ---- the first block's two fields the piece reads ---- *)
assert (Hes32 : (length es <= 32)%nat) by lia.
assert (Hesb : Forall (fun e => (length (e_body e) <= 96)%nat) (pc_ents (PbCut sh ps (Some es))))
  by (apply rw8_body96; apply rw8_ents_wf; assumption).
assert (Hentl : (length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat)
  by (apply rw8_ents_len; assumption).
assert (Hbmax : len <= Layout.POD_BUF_MAX) by (unfold Layout.POD_BUF_MAX; lia).
unfold rs_pp_at in Hppat. unfold pc_image in Hppat.
assert (Vlen : val_mem rsegs (mrestrict (w_H W2) mem2) (q_pp (x_e cx) + 0x4000) 8 len)
  by exact (rtm_pp_len rsegs _ _ _ _ _ false Hbmax Hentl Hesb _ _ _ Hppat).
assert (Vnent : rs_first ps = 1 ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (q_pp (x_e cx) + 0x4d14) 4 (Z.of_nat (length es))).
{ intros Hf1. rewrite <- (rw8_first_ents sh ps es Hf1).
  exact (rtm_pp_n_ent rsegs _ _ _ _ _ false Hbmax Hentl Hesb _ _ _ Hppat). }
(* ---- the piece, as one block ---- *)
eapply SRr_bind.
{ exact (CORE (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem2 md2 (x_k cx) regs2 (q_R (x_e cx)) (q_pp (x_e cx)) (q_F (x_e cx)) (x_pos cx)
    len cnt (Z.of_nat (length es)) (Z.of_nat (length r)) (rs_first ps) ed
    HJ HG2 Hpp2 Hfresh R2_2 R2_3 R2_4 A9 A18 A19 A20 A22 A23 A24 A26' A27
    Va0 Va8 Vb8 Vf0 V108 V110 V118 V128 V130 V138 Vlen Vnent Hent Hfsh
    Hwfed Hlenlo Hlenhi Hlen8 ltac:(lia) ltac:(lia) Hfr01 Hrlen). }
cbv beta. intros W7 c7 Hw7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & Hk7 & Hfr7 & Hperm7 & Hio7 & Hmo7 & Hm7
  & (D11 & D24 & D26 & Dlen & Denc & Drec & Dfsh)).
(* ---- the frame part of the end cut ---- *)
assert (Kc : forall a, q_R (x_e cx) <= a < q_R (x_e cx) + 0x140 ->
  aview rsegs (w_H W7) mem7 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply Hm7; [lia|].
  intros [X|[X|[[_ X]|[[_ X]|[X|X]]]]]; lia. }
assert (Hcore7 : rs_core rsegs B MT cx (rs_E1 rsegs cx) ly7 S7 W7 regs7 mem7 md7).
{ unfold rs_core, rs_mid. split; [exact HJ7|].
  split.
  { intros rr' Hrr'. destruct Hrr' as [-> | [-> | ->]].
    - rewrite (rw8_getr5 regs7 (2%bv) 2 eq_refl), (Hk7 (2%bv) ltac:(rw8_nz) ltac:(rw8_notin)),
        <- (rw8_getr5 regs2 (2%bv) 2 eq_refl). apply Hr234. lia.
    - rewrite (rw8_getr5 regs7 (3%bv) 3 eq_refl), (Hk7 (3%bv) ltac:(rw8_nz) ltac:(rw8_notin)),
        <- (rw8_getr5 regs2 (3%bv) 3 eq_refl). apply Hr234. lia.
    - rewrite (rw8_getr5 regs7 (4%bv) 4 eq_refl), (Hk7 (4%bv) ltac:(rw8_nz) ltac:(rw8_notin)),
        <- (rw8_getr5 regs2 (4%bv) 4 eq_refl). apply Hr234. lia. }
  split; [rewrite Hfr7; exact Hfr|].
  split; [eapply Permutation_trans; [exact Hperm7 | exact Hperm]|].
  split; [eapply same_io_trans; [exact Hio | exact Hio7]|].
  split; [pose proof (mle_station MT (x_Sc cx) S2 S7 0 0 MTL Hmo Hmo7) as HM; rewrite Z.add_0_r in HM; exact HM|].
  intros a Ha Hstkw HE. rewrite Hsp in Hstkw.
  rewrite (Hm7 a Ha ltac:(intros [X|[X|[[_ X]|[[_ X]|[X|X]]]]];
    [ apply HE; right; unfold Layout.PP_SIZE; lia
    | apply HE; right; unfold Layout.PP_SIZE; lia
    | apply HE; right; unfold Layout.PP_SIZE; lia
    | apply HE; right; unfold Layout.PP_SIZE; lia
    | apply HE; left; apply Exists_cons_tl; apply Exists_cons_hd;
      cbn [fst snd rt_xv hi_w1 rate_himg_A]; lia
    | apply Hstkw; unfold T_SEG_STK, ASTACK in *; unfold ESTACK in X; lia ])).
  apply Hmem; [exact Ha | rewrite Hsp; exact Hstkw | exact HE]. }
(* ---- the first block's new image ---- *)
assert (Himg : rtm_bytes rsegs (w_H W7) mem7 (q_pp (x_e cx))
  (pc_image (PbCut sh ps (Some (es ++ [ed]))))).
{ unfold pc_image. cbn [pc_shape pc_props pc_open pc_buf].
  rewrite <- (pc_buf_pod sh ps es ed).
  set (fi := Z.eqb (rs_first ps) 1).
  assert (Hfi : (if fi then pc_ents (PbCut sh ps (Some es)) ++ [ed] else pc_ents (PbCut sh ps (Some es)))
    = pc_ents (PbCut sh ps (Some (es ++ [ed])))).
  { subst fi. destruct (Z.eqb_spec (rs_first ps) 1) as [E|E].
    - symmetry. apply rw8_first_pod. exact E.
    - symmetry. apply rw8_notfirst_ents. exact E. }
  rewrite <- Hfi.
  apply (rw8_img_step rsegs (w_H W2) mem2 (w_H W7) mem7 (q_pp (x_e cx)) (pc_buf (PbCut sh ps (Some es)))
    (enc_pod ed) (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
    (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps (Some es))) ed fi).
  - unfold Layout.POD_BUF_MAX. fold len. lia.
  - rewrite Nat2Z.inj_add. unfold Layout.POD_BUF_MAX. fold len. rewrite Henc_pod_len. lia.
  - exact Hentl.
  - intros Hf. subst fi. apply Z.eqb_eq in Hf. rewrite (rw8_first_ents sh ps es Hf). lia.
  - exact Hesb.
  - destruct Hwfed as (_ & Hb & _). rewrite Hb. lia.
  - exact Hppat.
  - fold len. exact Denc.
  - rewrite Nat2Z.inj_add, Henc_pod_len. fold len. unfold Layout.OFF_LEN.
    replace (len + (8 + e_size ed + pad8 (e_size ed))) with (len + Z.of_nat (length (enc_pod ed)))
      by (rewrite Henc_pod_len; lia). exact Dlen.
  - intros Hf. subst fi. apply Z.eqb_eq in Hf.
    rewrite (rw8_first_ents sh ps es Hf). unfold Layout.OFF_ENT, Layout.ENT_SIZE, Layout.OFF_N_ENT.
    destruct (Drec Hf) as [Hr1 Hr2].
    split; [replace (q_pp (x_e cx) + 16404 + 104 * Z.of_nat (length es))
              with (q_pp (x_e cx) + 0x4014 + 104 * Z.of_nat (length es)) by lia; exact Hr1
           | replace (q_pp (x_e cx) + 19732) with (q_pp (x_e cx) + 0x4d14) by lia; exact Hr2].
  - intros y Hy U1 U2 U3 U4. apply Hm7; [unfold Layout.PP_SIZE in *; lia|].
    intros [X|[X|[[E X]|[[E X]|[X|X]]]]].
    + apply U1. rewrite Nat2Z.inj_add, Henc_pod_len. fold len. lia.
    + apply U2. unfold Layout.OFF_LEN. lia.
    + apply U4. subst fi. split; [apply Z.eqb_eq; exact E|]. unfold Layout.OFF_N_ENT. lia.
    + apply U3. subst fi. split; [apply Z.eqb_eq; exact E|].
      rewrite (rw8_first_ents sh ps es E). unfold Layout.OFF_ENT, Layout.ENT_SIZE. lia.
    + exfalso. apply (Hshd (y - shadow_addr (q_F (x_e cx))) ltac:(lia)).
      unfold Layout.PP_SIZE in *. lia.
    + unfold Layout.PP_SIZE in *. unfold ESTACK in X. lia. }
(* ---- the model's step and the facts both end cuts share ---- *)
assert (Htie' : rs_pod_tie sh ps cnt (es ++ [ed]) rest r)
  by exact (rw8_ents_step sh ps cnt es ed rest rr r Htie Hed).
assert (Hesw' : Forall ent_wf (es ++ [ed]))
  by (apply Forall_app; split; [exact Hesw | apply Forall_cons; [exact Hwfed | apply Forall_nil]]).
assert (Hlen' : Z.of_nat (length (es ++ [ed])) = Z.of_nat (length es) + 1)
  by (rewrite length_app; cbn [length]; lia).
(* ---- the end cut, by the pod loop's latch ---- *)
destruct (Z.eqb_spec (Z.of_nat (length es) + 1) cnt) as [Ecl|Ecl].
- (* k + 1 = cnt: the params Struct's close *)
  apply (HCL ly7 S7 W7 regs7 mem7 md7 sh np ps cnt (es ++ [ed]) r Hi).
  split; [exact Hcore7|].
  split.
  { unfold rs_at_cx, rs_at. cbn [rs_Rc rs_Rc0 rs_Kc rs_Hc app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: first
      [ (cbn [rt_at]; rewrite (rw8_getr5 regs7 (24%bv) 24 eq_refl); exact D24)
      | (cbn [rt_at]; rewrite (rw8_getr5 regs7 (26%bv) 26 eq_refl), D26; unfold w64;
         rewrite Z_to_bv_mod64; reflexivity)
      | rw8_kept Hat Hk7 Kc ]. }
  split; [exact Dfsh|]. split; [exact Himg|].
  split; [exact Hin|]. split; [exact Hsuf|]. split; [exact Hwf|]. split; [exact Hlen0|].
  split; [exact Hps|]. split; [exact Htie'|]. split; [exact Hsh|]. split; [exact Hnp|].
  split; [exact Hpsnp|]. split; [exact Hnp3|]. split; [exact Hsh7|]. split; [exact Hps2|].
  split; [exact Hcnt|]. split; [exact Hesw' | rewrite Hlen'; exact Ecl].
- (* k + 1 <> cnt: the pod loop's head *)
  apply (HC ly7 S7 W7 regs7 mem7 md7 sh np ps cnt (es ++ [ed]) r Hi
    ltac:(rewrite length_app; cbn [length]; lia)).
  split.
  { split; [exact Hcore7|]. split; [exact Hin|]. split; [exact Hsuf|]. split; [exact Hsuf|].
    split; [exact Hwf|]. split; [exact Hlen0|]. split; [exact Hps|]. split; [exact Htie'|].
    split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hpsnp|]. split; [exact Hnp3|].
    split; [exact Hsh7|]. split; [exact Hps2|]. split; [exact Hcnt|]. split; [exact Hesw'|].
    split; [rewrite length_app; cbn [length]; lia | rewrite Hlen'; lia]. }
  split.
  { unfold rs_at_cx, rs_at. cbn [rs_L_pod rs_Rc rs_Rc0 rs_Kc rs_Hc app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: first
      [ (cbn [rt_at]; rewrite (rw8_getr5 regs7 (11%bv) 11 eq_refl), D11; f_equal; rewrite Hlen'; lia)
      | (cbn [rt_at]; rewrite (rw8_getr5 regs7 (24%bv) 24 eq_refl); exact D24)
      | (cbn [rt_at]; rewrite (rw8_getr5 regs7 (26%bv) 26 eq_refl), D26; unfold w64;
         rewrite Z_to_bv_mod64; reflexivity)
      | rw8_kept Hat Hk7 Kc ]. }
  split; [exact Dfsh | exact Himg].
Qed.
End p.

Print Assumptions rw8_piece.
