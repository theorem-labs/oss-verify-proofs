(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgLib.v at origin/ossv/recipes 6ebe35ba632
   (lines 132-146 ajournal_fp_nil and 156-159 ajournal_nil_io, from cgif ACfh.v; lines 207-239, the leaf of
   knock_lib_x_body: the contract's post from the walk's return state) for reac-pw/fuzz_role image A: the walk is
   role's chain of five segments over the harness-level cuts of lib/A/RPgHarn.v, with lib/A/RPgCSpec.v's two
   middle contracts in the middle and the malloc(pod) step between them; the leaf is unchanged but for the
   exists-fx' form of RPgCSpec.rl_lib_contract_x. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgTop.v at 3c7e900fc63 for reac-pw/fuzz_headamp
   image A: module paths changed, rh_ renamed to hq_; role's five segments become headamp's eleven (E01, the five
   middle contracts of lib/A/HPgCSpec.v, the three malloc steps, X01's two parts) over the cuts of lib/A/HPgE01D.v,
   lib/A/HPgSegC23.v, lib/A/HPgM24Out.v and lib/A/HPgSegM.v; the class-4 frame (1024 bytes, flag word F + 0x3f8),
   the real frame 0x1e0, the three float saves and the errno cell (api_env) in the separations; the cut-to-premise
   and post-to-cut steps stated once for any cut (hq_pre_of_cut, hq_cut_post) and instantiated per segment; the
   float state carried as each contract states it (M03 and M04b change it; M04a, M04b, X01 run at the state the
   segment before returns at); the parse's answer fixed in the run's quantities at C2; the leaf at the
   exists-fx' post of HPgSegM.hq_ret. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): THE WHOLE RUN of LLVMFuzzerTestOneInput
   (0x80c40), chained.

     headamp_lib_x : hd_lib_contract_x segs B ameter_triv K XM_LIB XN_LIB RLO RHI A_LLVMF RA_LLVMF ...

   from its segments, each a Section hypothesis:
     E01    HPgE01D.hqu_S_E01_stmt                ENTRY 0x80c40 -> C1 0x80fcc
     M01    HPgCSpec.headamp_build_contract (HPgMainL.headamp_build_holds over the build's pieces)  C1 -> C2 0x82efc
     C23    HPgSegM.hqu_S_C23_stmt                C2 -> C3 0x82f00, the malloc(pod) call
     M02    HPgCSpec.headamp_dup_contract         C3 -> C4 0x82f34
     C45    HPgSegM.hqu_S_C45_stmt                C4 -> C5 0x82f38, the malloc(out) call
     M03    HPgCSpec.headamp_check_contract (HPgSegM.headamp_check_holds over M03's pieces)        C5 -> C6 0x83900
     C67    HPgSegM.hqu_S_C67_stmt                C6 -> C7 0x83904, the malloc(first) call
     M04a   HPgCSpec.headamp_first_contract       C7 -> C8 0x83920
     M04b   HPgCSpec.headamp_plain_contract       C8 -> C9 0x83950
     X01    HPgSegM.hqu_S_X01f_stmt / hqu_S_X01r_stmt  C9 -> J 0x83980 -> the return to RA_LLVMF
   (all of lib/AU, image B's cut texts) and two facts of the symbols: lib/AU/HPgHarn.hqu_static_law (the
   start-up's const cells and zero-shadow ranges) and YCbq.api_env (the errno cell lies in the image, low). The
   middle contracts are lib/A/HPgCSpec.v's image-free texts at image B's record headamp_himg_B. The chaining
   (this file) is image A's lib/A/HPgTop.v over image B's texts and does the same three kinds of work:
   - at each middle contract's start it builds hd_seg_pre from the harness cut (hqu_pre_of_cut): the journal and
     the cut's values as they are; the geometry (R mod 32, R + 0x220 <= S, sp0 - LLVMF_STK <= R - ASTACK) from the
     entry's astk_ok and HQU_RSZ + 32 + ASTACK <= LLVMF_STK; the read-only agreement through the journal
     (HPgBase.arodata_ok_journalP); the globals', strings', cells', guard and read-only facts from hqu_static_law at
     the cut's AR; the real frame's checked cell R+0x180 from the stack's zero shadow (HPgMem.hmu_B_rz); the
     blocks made since the entry fresh (the cut's freshness clause); and the contract's own premises from the cut;
   - it carries what the segments after a cut need and the middle contracts do not restate (the 13 callee-saved
     words and 4 float saves at [S - 0x88, S) and the frame's flag word at F + 0x3f8: HPgSegM.hqu_kept; the
     blocks' bytes; the errno cell readable) through each contract's "outside the write set" clause (hqu_cut_post),
     by the separations: the stack lies above alloc_ceiling, the frame and the blocks below it and apart
     (AR_sep_law), the shadow bytes of an application address are not application addresses, the blocks and the
     frame are outside the image and the errno cell inside it (AR_client_img_law, api_env), two blocks of one list
     apart (sep_blocks, sep_blocks_pos at the malloc steps' appended lists). Image B's M01 writes [R, R + 0x198)
     and its real frame is 0x220 bytes, so the saves at [S - 0x88, S) lie just above the build's cells;
   - it turns X01's return state into hd_lib_post_x (knock's leaf: the journal at FP = [] weakened to the sink's
     footprint, I/O and file system kept, the sink and the meta table kept by the core's laws, the input bytes kept
     by the journal's block clause).
   Image B's cuts C2 and C3 do not carry the parse's answer (image A's do); the chaining fixes it in the run's
   quantities at C2 (hqu_env_rc) and gives it to C4's record by computation (hqu_C4_cut's premise Hrc). Image B's
   C5 carries the pod / out apartness that image A's malloc(out) step states beside its cut.
   Proves no function of its own (kind: merge). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgE01D HPgHarn HPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ===================================== numbers ===================================== *)
Lemma hqu_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia. Qed.

Lemma hqu_fs4 : fs_frame_bytes HQU_CID = 1024.
Proof. reflexivity. Qed.

Lemma hqu_frame_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos H. unfold frame_addr. destruct H as (_ & _ & _ & _ & _ & HF & _). rewrite HF. reflexivity. Qed.

Lemma hqu_stk_le : forall n ly ly', layout_le n ly ly' -> ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly.
Proof. intros n ly ly' H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & _). split; assumption. Qed.

(* The real frame's base: R = 32 * floor((S - 0x220) / 32). *)
Lemma hqu_R_facts : forall S R, R = 32 * ((S - HQU_RSZ) / 32) ->
  R mod 32 = 0 /\ R + 0x220 <= S /\ S - 0x220 - 32 < R.
Proof.
intros S R ->. unfold HQU_RSZ.
pose proof (Z.div_mod (S - 0x220) 32 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound (S - 0x220) 32 ltac:(lia)) as Hm.
set (q := (S - 0x220) / 32) in *. set (r := (S - 0x220) mod 32) in *.
split; [|lia]. rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.

Lemma hqu_mod16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 16 ltac:(lia)) as Hd. rewrite H, Z.add_0_r in Hd. rewrite Hd.
replace (16 * (x / 16)) with ((2 * (x / 16)) * 8) by lia. apply Z.mod_mul. lia.
Qed.

(* hqu_hcx's projections, with the segments implicit in this file *)
Local Arguments hu_ly {segs} _.
Local Arguments hu_S {segs} _.
Local Arguments hu_W {segs} _.
Local Arguments hu_regs {segs} _.
Local Arguments hu_mem {segs} _.
Local Arguments hu_md {segs} _.
Local Arguments hu_p {segs} _.
Local Arguments hu_n {segs} _.
Local Arguments hu_pl {segs} _.

(* the cells the chaining carries (hqu_kept): the 13 saves and 4 float saves at [S - 0x88, S), the flag word *)
Definition hqu_carried (e : hd_env) (a : Z) : Prop :=
  e_S e - 0x88 <= a < e_S e \/ e_F e + HQU_FLAG <= a < e_F e + HQU_FLAG + 8.

Section n. Context {rc : YM05.RunCeil}.
(* image B's write sets, the real frame 0x220 bytes below S: hi_w1 = F + [0x20, 0x278), its 116 shadow bytes,
   R + [0, 0x198); hi_w3 = F + [0x2a0, 0x348), shadow bytes [0x54, 0x69), R + [0, 0x160) *)
Lemma hqu_carried_off : forall S R F a,
  alloc_ceiling + ASTACK <= S - 0x220 - 32 -> R + 0x220 <= S -> S - 0x220 - 32 < R ->
  4096 <= F -> F + 1024 <= alloc_ceiling -> in_app F 1024 -> S <= 2 ^ 47 ->
  (S - 0x88 <= a < S \/ F + HQU_FLAG <= a < F + HQU_FLAG + 8) ->
  0 <= a < 2 ^ 64 /\ ~ (R - ASTACK <= a < R) /\
  ~ (F + 0x20 <= a < F + 0x278) /\ ~ (shadow_addr F <= a < shadow_addr F + 116) /\ ~ (R <= a < R + 0x198) /\
  ~ (F + 0x2a0 <= a < F + 0x348) /\ ~ (shadow_addr F + 0x54 <= a < shadow_addr F + 0x69) /\ ~ (R <= a < R + 0x160).
Proof.
intros S R F a Hst HR1 HR2 HF1 HF2 Happ HS Ha.
pose proof ASAN_CEIL_range as ((Hc1 & Hc2) & _). unfold ASAN_CEIL in Hc1, Hc2.
unfold shadow_addr, SHADOW_OFF, ASTACK, HQU_FLAG in *. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof (Z.div_mod F 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as Hm.
set (q := F / 8) in *. set (r := F mod 8) in *.
repeat split; lia.
Qed.

(* A frame's shadow byte is not an application address (HPgMem.hm_shadow_not_app at x = F + 8 i). *)
Lemma hqu_shadow_off_app : forall F i p m, in_app F 1024 -> 0 <= i < 128 -> in_app p m -> ~ (p <= shadow_addr F + i < p + m).
Proof.
intros F i p m HF Hi Hp.
replace (shadow_addr F + i) with (shadow_of_addr SHADOW_OFF (F + 8 * i)) by (rewrite shadow_of_addr_add8; reflexivity).
apply (hm_shadow_not_app _ p m); [|exact Hp].
pose proof ASAN_CEIL_range as ((Hc1 & Hc2) & _). unfold ASAN_CEIL in Hc1, Hc2.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HF. unfold kHighMemEnd. lia.
Qed.
End n.

Lemma hqu_inw1 : forall e a, hd_inw e (hi_w1 headamp_himg_B) a ->
  (e_F e + 0x20 <= a < e_F e + 0x278) \/ (shadow_addr (e_F e) <= a < shadow_addr (e_F e) + 116) \/
  (e_R e <= a < e_R e + 0x198).
Proof.
intros e a H. unfold hd_inw in H. cbn [hi_w1 headamp_himg_B] in H.
rewrite !Exists_cons, Exists_nil in H. cbn [hd_xv fst snd] in H. lia.
Qed.

Lemma hqu_inw3 : forall e a, hd_inw e (hi_w3 headamp_himg_B) a ->
  (e_F e + 0x2a0 <= a < e_F e + 0x348) \/ (shadow_addr (e_F e) + 0x54 <= a < shadow_addr (e_F e) + 0x69) \/
  (e_R e <= a < e_R e + 0x160).
Proof.
intros e a H. unfold hd_inw in H. cbn [hi_w3 headamp_himg_B] in H.
rewrite !Exists_cons, Exists_nil in H. cbn [hd_xv fst snd] in H. lia.
Qed.

Lemma hqu_inw_nil : forall e a, ~ hd_inw e [] a.
Proof. intros e a H. unfold hd_inw in H. apply Exists_nil in H. exact H. Qed.

(* the parse's answer: -1 <= rc <= cap, and its cells are max(rc, 0) *)
Lemma hqu_ans_ok : forall props cap, 0 <= cap -> answer_ok cap (Headamp.parse_props props cap).
Proof.
intros [bs|] cap H; cbn [Headamp.parse_props].
- apply parse_model_total. exact H.
- unfold answer_ok. cbv beta iota. split; [left; repeat split | apply Forall_nil].
Qed.

Lemma hqu_ans_rc : forall props cap, 0 <= cap ->
  -1 <= ans_rc (Headamp.parse_props props cap) <= cap /\
  Z.of_nat (length (ans_cells (Headamp.parse_props props cap))) = Z.max (ans_rc (Headamp.parse_props props cap)) 0.
Proof.
intros props cap H. destruct (answer_ok_parts cap _ (hqu_ans_ok props cap H)) as [[(E1 & E2 & _)|(H1 & H2 & _)] _].
- rewrite E1, E2. cbn. lia.
- lia.
Qed.

(* the run's quantities with the parse's answer filled in (no cut list of C1 .. C5 reads it) *)
Definition hqu_env_rc (e : hd_env) (rc0 : Z) : hd_env :=
  HDEnv (e_S e) (e_R e) (e_F e) (e_pp e) (e_pod e) (e_out e) (e_first e) (e_len e) (e_cap e) (e_null e) rc0
        (e_src e) (e_left e).

(* ============================ journal facts [knock APgLib.v:132-159, cgif ACfh.v] ============================ *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Lemma hqu_ajournal_fp_nil : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (sink_closed_nil Ho)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi _; apply (F2 p n i H1 H2 Hi); apply inFP_nil|].
split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply fp_spares_closed; intros Ho; exact (sink_closed_nil Ho)|].
split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply inFP_nil|].
split; [intros p n i H1 H2 Hi; exfalso; exact (inFP_nil _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.
Lemma hqu_ajournal_nil_io : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ. pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed [] md md' sink_closed_nil Hos) as (Efd & Efsys & _ & _).
unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.
End d.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Let LAWS : AR_laws segs B := AR_laws_ok segs B.

(* ============================ cells, bytes and cuts across a kept clause ============================ *)
Lemma hqu_cell_kept : forall H mem H' mem' regs regs' e b o v,
  hd_at segs H mem regs e (LCell b o) v ->
  (forall i, 0 <= i < 8 -> aview segs H' mem' (hd_xv e b + o + i) = aview segs H mem (hd_xv e b + o + i)) ->
  hd_at segs H' mem' regs' e (LCell b o) v.
Proof.
intros H mem H' mem' regs regs' e b o v Hv Hk. cbn [hd_at] in *. intros k Hlt.
rewrite (mbyte_of_aview segs H H' mem mem'); [exact (Hv k Hlt) | apply Hk; lia].
Qed.

Lemma hqu_kept_tr : forall (hx : hqu_hcx segs) pos e (W W' : world segs) mem mem' regs regs',
  hqu_kept segs hx pos e W mem regs ->
  (forall a, hqu_carried e a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  hqu_kept segs hx pos e W' mem' regs'.
Proof.
intros hx pos e W W' mem mem' regs regs' Hk0 Hkeep. unfold hqu_kept, hqu_fsaves in *.
destruct Hk0 as (Hc & (v0 & v1 & v2 & v3 & F0 & F1 & F2 & F3)).
split.
- rewrite Forall_forall in Hc |- *. intros f Hf. pose proof (Hc f Hf) as Hv.
  unfold hqu_cells, hqu_saves_L in Hf. apply in_app_iff in Hf as [Hf|Hf].
  + apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj. cbn [fst snd] in *.
    apply (hqu_cell_kept _ _ _ _ regs regs' e XS _ _ Hv). intros i Hi. apply Hkeep. unfold hqu_carried.
    cbn [hd_xv]. lia.
  + destruct Hf as [<-|[]]. cbn [fst snd] in *.
    apply (hqu_cell_kept _ _ _ _ regs regs' e (XF 0) _ _ Hv). intros i Hi. apply Hkeep. unfold hqu_carried.
    cbn [hd_xv]. lia.
- exists v0, v1, v2, v3.
  split; [|split; [|split]].
  + apply (hqu_cell_kept _ _ _ _ regs regs' e XS _ _ F0). intros i Hi. apply Hkeep. unfold hqu_carried.
    cbn [hd_xv]. lia.
  + apply (hqu_cell_kept _ _ _ _ regs regs' e XS _ _ F1). intros i Hi. apply Hkeep. unfold hqu_carried.
    cbn [hd_xv]. lia.
  + apply (hqu_cell_kept _ _ _ _ regs regs' e XS _ _ F2). intros i Hi. apply Hkeep. unfold hqu_carried.
    cbn [hd_xv]. lia.
  + apply (hqu_cell_kept _ _ _ _ regs regs' e XS _ _ F3). intros i Hi. apply Hkeep. unfold hqu_carried.
    cbn [hd_xv]. lia.
Qed.

Lemma hqu_garr8_kept : forall H mem H' mem' a l,
  garr8 segs (mrestrict H mem) a l ->
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' mem' (a + j) = aview segs H mem (a + j)) ->
  garr8 segs (mrestrict H' mem') a l.
Proof.
intros H mem H' mem' a l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
intros k Hlt.
rewrite (mbyte_of_aview segs H H' mem mem'); [exact (Hv k Hlt)|].
rewrite <- Z.add_assoc. apply Hk. lia.
Qed.

Lemma hqu_rd32_kept : forall H mem H' mem' a v,
  rd32 (aview segs H mem) a v ->
  (forall i, 0 <= i < 4 -> aview segs H' mem' (a + i) = aview segs H mem (a + i)) ->
  rd32 (aview segs H' mem') a v.
Proof. intros H mem H' mem' a v Hr Hk k Hlt. rewrite Hk by lia. exact (Hr k Hlt). Qed.

Lemma hqu_cut_L_env : forall H mem regs e e' L,
  (forall f, In f L -> hd_at segs H mem regs e (fst f) (hd_xv e (snd f)) ->
   hd_at segs H mem regs e' (fst f) (hd_xv e' (snd f))) ->
  hd_cut segs H mem regs e L -> hd_cut segs H mem regs e' L.
Proof.
intros H mem regs e e' L Hf HL. unfold hd_cut in *. rewrite Forall_forall in *.
intros f Hin. exact (Hf f Hin (HL f Hin)).
Qed.

(* no entry of image B's C2 list reads the parse's answer *)
Lemma hqu_L2_rc : forall H mem regs e rc0,
  hd_cut segs H mem regs e (hi_L2 headamp_himg_B) -> hd_cut segs H mem regs (hqu_env_rc e rc0) (hi_L2 headamp_himg_B).
Proof.
intros H mem regs e rc0. apply hqu_cut_L_env. intros f Hf.
cbn [hi_L2 headamp_himg_B headamp_B_L23 In] in Hf.
repeat match type of Hf with _ \/ _ => destruct Hf as [<-|Hf]; [intros Hx; exact Hx|] end.
contradiction.
Qed.

(* the environment of a cut changed only in rc, at C2's list *)
Lemma hqu_cut_rc : forall LLVMF_STK (hx : hqu_hcx segs) pos e rc0 k bls sh ly S W regs mem md,
  hqu_at_cut segs B LLVMF_STK hx pos e k bls (hi_L2 headamp_himg_B) sh ly S W regs mem md ->
  hqu_at_cut segs B LLVMF_STK hx pos (hqu_env_rc e rc0) k bls (hi_L2 headamp_himg_B) sh ly S W regs mem md.
Proof.
intros LLVMF_STK hx pos e rc0 k bls sh ly S W regs mem md (HJ & Hp & Hf & H2 & H3 & H4 & Hg & HL & Hsh & Hk).
split; [exact HJ|]. split; [exact Hp|]. split; [exact Hf|]. split; [exact H2|]. split; [exact H3|].
split; [exact H4|].
split; [exact (hqu_geo_env segs hx pos e (hqu_env_rc e rc0) eq_refl eq_refl eq_refl Hg)|].
split; [exact (hqu_L2_rc _ _ _ e rc0 HL)|].
split; [exact Hsh|].
exact (hqu_kept_env segs hx pos e (hqu_env_rc e rc0) W mem regs eq_refl eq_refl Hk).
Qed.

(* a block of a cut's list is a live block, made since the entry *)
Lemma hqu_cut_in : forall LLVMF_STK (hx : hqu_hcx segs) pos e k bls L sh ly S W regs mem md b,
  hqu_at_cut segs B LLVMF_STK hx pos e k bls L sh ly S W regs mem md -> In b bls -> In b (ablocks B ly S).
Proof.
intros LLVMF_STK hx pos e k bls L sh ly S W regs mem md b HC Hb. destruct HC as (_ & Hperm & _).
apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hb.
Qed.

Lemma hqu_fresh_of_cut : forall LLVMF_STK (hx : hqu_hcx segs) pos e k bls L sh ly S W regs mem md p n,
  hqu_at_cut segs B LLVMF_STK hx pos e k bls L sh ly S W regs mem md -> In (p, n) bls ->
  hd_fresh_block (ablocks B (hu_ly hx) (hu_S hx)) (ablocks B ly S) p n.
Proof.
intros LLVMF_STK hx pos e k bls L sh ly S W regs mem md p n HC Hb.
pose proof (hqu_cut_in LLVMF_STK hx pos e k bls L sh ly S W regs mem md _ HC Hb) as Hin.
destruct HC as (_ & _ & Hfr & _). rewrite Forall_forall in Hfr. destruct (Hfr _ Hb) as [Hnin Hnz].
split; [exact Hnz|]. split; [exact Hin | exact Hnin].
Qed.

(* ============================ the harness's geometry and its frame and blocks ============================ *)
Section c.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : HQU_RSZ + 32 + ASTACK <= LLVMF_STK.
Hypothesis HEV : HQU_EV <= EV_LIB.
Hypothesis HRELRO : forall a, RLO <= a < RHI -> in_img segs a.
Context {RO : ro_below_ofl segs RLO RHI}.
Hypothesis HSTAT : hqu_static_law segs B RLO RHI.
Hypothesis HAPI : api_env segs B.

Local Notation BASE := (hqu_base segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK).
Local Notation J := (hqu_j segs B LLVMF_STK).
Local Notation CUT := (hqu_at_cut segs B LLVMF_STK).

Lemma hqu_geo_facts : forall hx pos e, BASE hx -> hqu_geo segs hx pos e ->
  alloc_ceiling + ASTACK <= e_S e - 0x220 - 32 /\ e_S e mod 16 = 0 /\
  alloc_ceiling <= ly_stk_lo (hu_ly hx) /\ ly_stk_lo (hu_ly hx) + LLVMF_STK <= e_S e /\
  e_S e <= ly_stk_hi (hu_ly hx) /\ ly_stk_hi (hu_ly hx) <= 2 ^ 47 /\
  e_R e mod 32 = 0 /\ e_R e + 0x220 <= e_S e /\ e_S e - 0x220 - 32 < e_R e /\
  e_S e - LLVMF_STK <= e_R e - ASTACK /\ ly_stk_lo (hu_ly hx) <= e_R e.
Proof.
intros hx pos e HB (HS & HR & _). destruct HB as ((_ & _ & _ & _ & _ & Hstk & _) & _).
destruct Hstk as (H16 & _ & Hlo & Hlos & Hhi & H47 & _). rewrite <- HS in *.
destruct (hqu_R_facts (e_S e) (e_R e) HR) as (HR32 & HR1 & HR2).
unfold HQU_RSZ, ASTACK in *. repeat split; lia.
Qed.

(* the frame for locals at a state of the journal that holds it *)
Lemma hqu_frame_facts : forall hx pos e own ly' S' W' mem' md' k,
  BASE hx -> hqu_geo segs hx pos e -> J hx own ly' S' W' mem' md' k -> In (HQU_CID, pos) (frames S') ->
  e_F e = frame_addr ly' HQU_CID pos /\ 4096 <= e_F e /\ e_F e + 1024 <= alloc_ceiling /\ in_app (e_F e) 1024 /\
  (forall x, e_F e <= x < e_F e + 1024 -> ~ in_img segs x).
Proof.
intros hx pos e own ly' S' W' mem' md' k HB (_ & _ & HF) HJ Hin.
pose proof HJ as (HAR & Hly & _).
assert (EF : e_F e = frame_addr ly' HQU_CID pos) by (rewrite HF; symmetry; exact (hqu_frame_addr_le _ _ _ _ _ Hly)).
destruct (frames_bounds segs B LAWS ly' S' W' mem' md' HQU_CID pos HAR Hin) as (H1 & H2 & H3).
rewrite hqu_fs4, <- EF in H2, H3. rewrite <- EF in H1.
split; [exact EF|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
intros x Hx.
assert (Hc : exists cid pos0, In (cid, pos0) (frames S') /\
  frame_addr ly' cid pos0 <= x < frame_addr ly' cid pos0 + fs_frame_bytes cid).
{ exists HQU_CID, pos. split; [exact Hin|]. rewrite hqu_fs4, <- EF. exact Hx. }
exact (proj2 (al_client_img _ _ LAWS ly' S' W' mem' md' x HAR (or_intror (or_introl Hc)))).
Qed.

(* a block at a state of the journal *)
Lemma hqu_block_facts : forall hx own ly' S' W' mem' md' k p n,
  J hx own ly' S' W' mem' md' k -> In (p, n) (ablocks B ly' S') ->
  p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\ 0 <= n /\
  (forall x, p <= x < p + req_size n -> ~ in_img segs x).
Proof.
intros hx own ly' S' W' mem' md' k p n HJ Hin. pose proof HJ as (HAR & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (H16 & H4 & H1 & H2 & _ & _ & H3).
split; [exact H16|]. split; [exact H4|]. split; [exact H1|]. split; [exact H2|]. split; [lia|].
intros x Hx.
assert (Hc : exists p0 n0, In (p0, n0) (ablocks B ly' S') /\ p0 <= x < p0 + req_size n0).
{ exists p, n. split; [exact Hin | exact Hx]. }
exact (proj2 (al_client_img _ _ LAWS ly' S' W' mem' md' x HAR (or_introl Hc))).
Qed.

Lemma hqu_spR : forall (regs : bvmap 5 word) R, getr regs 2 = w64 R -> 0 <= R < 2 ^ 64 -> spZ regs = R.
Proof. intros regs R H HR. unfold spZ. rewrite H. unfold w64. apply hqu_u64. exact HR. Qed.

(* what any harness cut gives: the geometry, sp = R, the frame *)
Lemma hqu_cut_facts : forall hx pos e k bls L sh ly S W regs mem md,
  BASE hx -> CUT hx pos e k bls L sh ly S W regs mem md ->
  alloc_ceiling + ASTACK <= e_S e - 0x220 - 32 /\ e_S e <= 2 ^ 47 /\
  e_R e + 0x220 <= e_S e /\ e_S e - 0x220 - 32 < e_R e /\ spZ regs = e_R e /\
  e_F e = frame_addr ly HQU_CID pos /\ 4096 <= e_F e /\ e_F e + 1024 <= alloc_ceiling /\ in_app (e_F e) 1024 /\
  (forall x, e_F e <= x < e_F e + 1024 -> ~ in_img segs x) /\ In (HQU_CID, pos) (frames S) /\
  AR segs B ly S W mem md.
Proof.
intros hx pos e k bls L sh ly S W regs mem md HB HC.
destruct HC as (HJ & _ & _ & Hr2 & _ & _ & Hgeo & _).
pose proof (hqu_geo_facts hx pos e HB Hgeo) as (Hst & HS16 & Hlo & Hlos & Hhi & H47 & HR32 & HR1 & HR2 & HRs & HRlo).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin4 : In (HQU_CID, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (hqu_frame_facts hx pos e _ _ _ _ _ _ _ HB Hgeo HJ Hin4) as (EF & HF1 & HF2 & HFapp & HFimg).
pose proof ASAN_CEIL_range as ((Hc1 & Hc2) & _). unfold ASAN_CEIL in Hc1, Hc2.
split; [exact Hst|]. split; [lia|]. split; [exact HR1|]. split; [exact HR2|].
split; [apply hqu_spR; [exact Hr2 | unfold ASTACK in *; lia]|].
split; [exact EF|]. split; [exact HF1|]. split; [exact HF2|]. split; [exact HFapp|]. split; [exact HFimg|].
split; [exact Hin4 | exact HAR].
Qed.

(* the carried cells lie off the callees' stack and off every write set of the middle segments *)
Lemma hqu_cut_carried : forall hx pos e k bls L sh ly S W regs mem md a,
  BASE hx -> CUT hx pos e k bls L sh ly S W regs mem md -> hqu_carried e a ->
  0 <= a < 2 ^ 64 /\ ~ (spZ regs - T_SEG_STK <= a < spZ regs) /\
  ~ hd_inw e (hi_w1 headamp_himg_B) a /\ ~ hd_inw e (hi_w3 headamp_himg_B) a /\
  ~ (as_errno B <= a < as_errno B + 4) /\
  (forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n)).
Proof.
intros hx pos e k bls L sh ly S W regs mem md a HB HC Ha.
pose proof (hqu_cut_facts hx pos e k bls L sh ly S W regs mem md HB HC)
  as (Hst & HS47 & HR1 & HR2 & EspR & EF & HF1 & HF2 & HFapp & HFimg & Hin4 & HAR).
destruct (hqu_carried_off (e_S e) (e_R e) (e_F e) a Hst HR1 HR2 HF1 HF2 HFapp HS47 Ha)
  as (Ha64 & HaR & Hw1a & Hw1b & Hw1c & Hw3a & Hw3b & Hw3c).
destruct HAPI as ((He0 & He1) & Heimg & _).
pose proof ASAN_CEIL_range as ((Hc1 & Hc2) & _). unfold ASAN_CEIL in Hc1, Hc2.
split; [exact Ha64|].
split; [unfold T_SEG_STK; rewrite EspR; exact HaR|].
split; [intros Hw; apply hqu_inw1 in Hw; tauto|].
split; [intros Hw; apply hqu_inw3 in Hw; tauto|].
split.
{ intros Hae. destruct Ha as [Ha|Ha].
  - unfold kLowMemEnd, ASTACK in *. lia.
  - apply (HFimg a); [unfold HQU_FLAG in Ha; lia | exact (Heimg a Hae)]. }
intros p n Hpn Hpa.
pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR Hpn Hin4) as Hsep. rewrite hqu_fs4, <- EF in Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
pose proof HC as (HJ & _).
destruct (hqu_block_facts hx _ _ _ _ _ _ _ _ _ HJ Hpn) as (_ & _ & Hpc & _).
unfold hqu_carried, HQU_FLAG, ASTACK in *. lia.
Qed.

(* a byte of a live block lies off the callees' stack, the carried cells, the image, the frame for locals and its
   shadow bytes, and the real frame *)
Lemma hqu_cut_block : forall hx pos e k bls L sh ly S W regs mem md p n,
  BASE hx -> CUT hx pos e k bls L sh ly S W regs mem md -> In (p, n) (ablocks B ly S) ->
  p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\ 0 <= n /\
  (forall a, p <= a < p + req_size n ->
   0 <= a < 2 ^ 64 /\ ~ (spZ regs - T_SEG_STK <= a < spZ regs) /\ ~ hqu_carried e a /\ ~ in_img segs a /\
   ~ hd_inw e (hi_w1 headamp_himg_B) a /\ ~ hd_inw e (hi_w3 headamp_himg_B) a /\
   ~ (as_errno B <= a < as_errno B + 4)).
Proof.
intros hx pos e k bls L sh ly S W regs mem md p n HB HC Hpn.
pose proof (hqu_cut_facts hx pos e k bls L sh ly S W regs mem md HB HC)
  as (Hst & HS47 & HR1 & HR2 & EspR & EF & HF1 & HF2 & HFapp & HFimg & Hin4 & HAR).
pose proof HC as (HJ & _).
destruct (hqu_block_facts hx _ _ _ _ _ _ _ _ _ HJ Hpn) as (H16 & H4 & Hpc & Happ & Hn & Himg).
pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR Hpn Hin4) as Hsep. rewrite hqu_fs4, <- EF in Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
destruct HAPI as ((He0 & He1) & Heimg & _).
pose proof ASAN_CEIL_range as ((Hc1 & Hc2) & _). unfold ASAN_CEIL in Hc1, Hc2.
split; [exact H16|]. split; [exact H4|]. split; [exact Hpc|]. split; [exact Happ|]. split; [exact Hn|].
intros a Ha.
assert (Hsh : forall i, 0 <= i < 128 -> shadow_addr (e_F e) + i <> a).
{ intros i Hi E. apply (hqu_shadow_off_app (e_F e) i p (req_size n) HFapp Hi Happ). lia. }
split; [unfold ASTACK in *; lia|].
split; [unfold T_SEG_STK; rewrite EspR; unfold ASTACK in *; lia|].
split; [unfold hqu_carried, HQU_FLAG, ASTACK in *; lia|].
split; [exact (Himg a Ha)|].
split.
{ intros Hw. apply hqu_inw1 in Hw. destruct Hw as [Hw|[Hw|Hw]]; [lia| |unfold ASTACK in *; lia].
  apply (Hsh (a - shadow_addr (e_F e))); lia. }
split.
{ intros Hw. apply hqu_inw3 in Hw. destruct Hw as [Hw|[Hw|Hw]]; [lia| |unfold ASTACK in *; lia].
  apply (Hsh (a - shadow_addr (e_F e))); lia. }
intros Hae. exact (Himg a Ha (Heimg a Hae)).
Qed.

(* the errno cell lies off the callees' stack *)
Lemma hqu_cut_errno : forall hx pos e k bls L sh ly S W regs mem md a,
  BASE hx -> CUT hx pos e k bls L sh ly S W regs mem md -> as_errno B <= a < as_errno B + 4 ->
  0 <= a < 2 ^ 64 /\ ~ (spZ regs - T_SEG_STK <= a < spZ regs).
Proof.
intros hx pos e k bls L sh ly S W regs mem md a HB HC Ha.
pose proof (hqu_cut_facts hx pos e k bls L sh ly S W regs mem md HB HC)
  as (Hst & HS47 & HR1 & HR2 & EspR & _).
destruct HAPI as ((He0 & He1) & _).
pose proof ASAN_CEIL_range as ((Hc1 & Hc2) & _). unfold ASAN_CEIL in Hc1, Hc2.
unfold T_SEG_STK. rewrite EspR. unfold kLowMemEnd, ASTACK in *. split; lia.
Qed.

(* a block's bytes across a segment whose write set misses the block *)
Lemma hqu_blk_kept : forall hx pos e k bls L sh ly S W regs mem md p n (E : Z -> Prop) (W2 : world segs) mem2,
  BASE hx -> CUT hx pos e k bls L sh ly S W regs mem md -> In (p, n) (ablocks B ly S) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_SEG_STK <= a < spZ regs) -> ~ E a ->
   aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, p <= a < p + req_size n -> ~ E a) ->
  forall l, Z.of_nat (length l) <= req_size n ->
  garr8 segs (mrestrict (w_H W) mem) p l -> garr8 segs (mrestrict (w_H W2) mem2) p l.
Proof.
intros hx pos e k bls L sh ly S W regs mem md p n E W2 mem2 HB HC Hpn Hkeep HE l Hl Hg.
apply (hqu_garr8_kept _ _ _ _ _ _ Hg). intros j Hj.
destruct (hqu_cut_block hx pos e k bls L sh ly S W regs mem md p n HB HC Hpn) as (_ & _ & _ & _ & _ & Hb).
destruct (Hb (p + j) ltac:(lia)) as (Ha64 & HaR & _).
apply Hkeep; [exact Ha64 | exact HaR | apply HE; lia].
Qed.

(* the errno cell across a segment whose write set misses it *)
Lemma hqu_errno_kept : forall hx pos e k bls L sh ly S W regs mem md (E : Z -> Prop) (W2 : world segs) mem2 ev,
  BASE hx -> CUT hx pos e k bls L sh ly S W regs mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_SEG_STK <= a < spZ regs) -> ~ E a ->
   aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, as_errno B <= a < as_errno B + 4 -> ~ E a) ->
  rd32 (aview segs (w_H W) mem) (as_errno B) ev -> rd32 (aview segs (w_H W2) mem2) (as_errno B) ev.
Proof.
intros hx pos e k bls L sh ly S W regs mem md E W2 mem2 ev HB HC Hkeep HE Hr.
apply (hqu_rd32_kept _ _ _ _ _ _ Hr). intros i Hi.
destruct (hqu_cut_errno hx pos e k bls L sh ly S W regs mem md (as_errno B + i) HB HC ltac:(lia)) as (Ha64 & HaR).
apply Hkeep; [exact Ha64 | exact HaR | apply HE; lia].
Qed.

(* ============================ a contract's start, from a harness cut ============================ *)
Lemma hqu_pre_of_cut : forall hx pos e k bls L sh ly S W regs mem md,
  BASE hx -> CUT hx pos e k bls L sh ly S W regs mem md -> 0 <= k <= HQU_EV ->
  In (e_pp e, Layout.PP_SIZE) bls -> 0 <= e_cap e <= 9 -> 0 <= e_null e <= 1 ->
  hd_seg_pre segs B LLVMF_STK (spZ (hu_regs hx)) [] (hu_ly hx) (hu_S hx) (hu_W hx) (hu_mem hx) (hu_md hx)
    [(HQU_CID, pos)] k regs ly S W mem md headamp_himg_B sh RLO RHI e pos.
Proof.
intros hx pos e k bls L sh ly S W regs mem md HB HC Hk Hpp Hcap Hnull.
pose proof (hqu_fresh_of_cut LLVMF_STK hx pos e k bls L sh ly S W regs mem md _ _ HC Hpp) as Hfresh.
pose proof HB as HB'. destruct HB' as (_ & _ & _ & _ & _ & _ & _ & Hfr0 & Hev & _ & HROS).
destruct HC as (HJ & Hperm & Hfr & Hr2 & Hr3 & Hr4 & Hgeo & HL & Hfsh & _).
pose proof (hqu_geo_facts hx pos e HB Hgeo) as (Hst & HS16 & Hlo & Hlos & Hhi & H47 & HR32 & HR1 & HR2 & HRs & HRlo).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
destruct (hqu_stk_le _ _ _ Hly) as [Elo Ehi].
assert (Hin4 : In (HQU_CID, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (hqu_frame_facts hx pos e _ _ _ _ _ _ _ HB Hgeo HJ Hin4) as (EF & _).
assert (Haro : arodata_okP segs RLO RHI B (aview segs (w_H W) mem)).
{ exact (arodata_ok_journalP segs RLO RHI HRELRO B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROS). }
destruct (HSTAT ly S W mem md HAR Haro) as (Hg & Hs & Hc & Hgd & Hrom).
destruct Hgeo as (HS & _ & _).
unfold hd_seg_pre.
split; [exact HJ|].
split; [lia|].
split; [exact Hr2|]. split; [exact Hr3|]. split; [exact Hr4|].
split; [exact HS|]. split; [exact HR32|].
split; [change (hi_rsz headamp_himg_B) with 0x220; lia|].
split; [unfold T_SEG_STK; rewrite <- HS; lia|].
split; [left; reflexivity|].
split; [exact EF|].
split; [exact Hfsh|].
split; [exact Hcap|]. split; [exact Hnull|].
split; [exact Haro|].
split; [exact Hg|].
split.
{ apply (hmu_B_rz segs B ly S W mem md (e_R e) (e_S e) HAR);
  [rewrite Elo; lia | lia | rewrite Ehi; lia | exact (hqu_mod16_8 _ HS16)]. }
split; [exact Hs|]. split; [exact Hc|]. split; [exact Hgd|]. split; [exact Hrom|].
exact Hfresh.
Qed.

(* ============================ a harness cut, from a contract's post ============================ *)
Lemma hqu_cut_post : forall hx pos e k bls L sh ly S W regs mem md L' sh' ly2 S2 W2 regs2 mem2 md2 (E : Z -> Prop),
  BASE hx -> CUT hx pos e k bls L sh ly S W regs mem md ->
  J hx [(HQU_CID, pos)] ly2 S2 W2 mem2 md2 k ->
  (forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_SEG_STK <= a < spZ regs) -> ~ E a ->
   aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, hqu_carried e a -> ~ E a) ->
  hd_cut segs (w_H W2) mem2 regs2 e L' -> hd_fsh segs (w_H W2) mem2 (e_F e) sh' ->
  CUT hx pos e k bls L' sh' ly2 S2 W2 regs2 mem2 md2.
Proof.
intros hx pos e k bls L sh ly S W regs mem md L' sh' ly2 S2 W2 regs2 mem2 md2 E HB HC HJ2 Hr Hperm Hkeep Hoff HL' Hsh'.
pose proof HC as HC'.
destruct HC' as (HJ & Hperm1 & Hfr & Hr2 & Hr3 & Hr4 & Hgeo & _ & _ & Hkept).
split; [exact HJ2|].
split; [exact (Permutation_trans Hperm Hperm1)|].
split; [exact Hfr|].
split; [rewrite <- Hr2; exact (Hr 2 (or_introl eq_refl))|].
split; [rewrite <- Hr3; exact (Hr 3 (or_intror (or_introl eq_refl)))|].
split; [rewrite <- Hr4; exact (Hr 4 (or_intror (or_intror eq_refl)))|].
split; [exact Hgeo|]. split; [exact HL'|]. split; [exact Hsh'|].
apply (hqu_kept_tr hx pos e W W2 mem mem2 regs regs2 Hkept).
intros a Ha.
destruct (hqu_cut_carried hx pos e k bls L sh ly S W regs mem md a HB HC Ha) as (Ha64 & HaR & _).
exact (Hkeep a Ha64 HaR (Hoff a Ha)).
Qed.

(* ============================ the eleven steps ============================ *)
(* ---- C1 -> M01's start ---- *)
Lemma hqu_C1_pre : forall hx pos e rest ly1 S1 W1 regs1 mem1 md1,
  BASE hx -> hqu_cut_C1 segs B LLVMF_STK hx pos e rest ly1 S1 W1 regs1 mem1 md1 ->
  hd_seg_pre segs B LLVMF_STK (spZ (hu_regs hx)) [] (hu_ly hx) (hu_S hx) (hu_W hx) (hu_mem hx) (hu_md hx)
    [(HQU_CID, pos)] 1 regs1 ly1 S1 W1 mem1 md1 headamp_himg_B (hi_shA headamp_himg_B) RLO RHI e pos.
Proof.
intros hx pos e rest ly1 S1 W1 regs1 mem1 md1 HB (HC & (_ & _ & _ & Hcap & Hnull) & _).
apply (hqu_pre_of_cut hx pos e 1 _ _ _ ly1 S1 W1 regs1 mem1 md1 HB HC);
  [unfold HQU_EV; lia | left; reflexivity | exact Hcap | exact Hnull].
Qed.

(* ---- M01's post -> C2, with the parse's answer fixed in the run's quantities ---- *)
Definition hqu_rc_of (e : hd_env) (r : Model.pod_rec) : Z :=
  ans_rc (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e)).

Lemma hqu_C2_cut : forall hx pos e rest ly1 S1 W1 regs1 mem1 md1 ly2 S2 W2 regs2 mem2 md2,
  BASE hx -> hqu_cut_C1 segs B LLVMF_STK hx pos e rest ly1 S1 W1 regs1 mem1 md1 ->
  YK0o.frm_zero (@fp_csr fx) ->
  J hx [(HQU_CID, pos)] ly2 S2 W2 mem2 md2 1 ->
  (forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
  Permutation (ablocks B ly2 S2) (ablocks B ly1 S1) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs1 - T_SEG_STK <= a < spZ regs1) ->
   ~ (hd_inw e (hi_w1 headamp_himg_B) a \/ e_pp e <= a < e_pp e + Layout.PP_SIZE) ->
   aview segs (w_H W2) mem2 a = aview segs (w_H W1) mem1 a) ->
  hd_cut segs (w_H W2) mem2 regs2 e (hi_L2 headamp_himg_B) ->
  hd_fsh segs (w_H W2) mem2 (e_F e) (hi_shA headamp_himg_B) ->
  garr8 segs (mrestrict (w_H W2) mem2) (e_pp e) (hd_zbytes (Layout.pp_bytes (fst (Model.pod_build rest)))) ->
  hqu_cut_C2 segs B LLVMF_STK hx fx pos (hqu_env_rc e (hqu_rc_of e (fst (Model.pod_build rest))))
    (fst (Model.pod_build rest)) ly2 S2 W2 regs2 mem2 md2.
Proof.
intros hx pos e rest ly1 S1 W1 regs1 mem1 md1 ly2 S2 W2 regs2 mem2 md2 HB HC1 HFRM HJ2 Hr Hperm Hkeep HL2 Hfsh2 Hpp2.
destruct HC1 as (HC & (_ & _ & _ & Hcap & Hnull) & (_ & Hlen & _)).
assert (Hpp : In (e_pp e, Layout.PP_SIZE) (ablocks B ly1 S1))
  by exact (hqu_cut_in LLVMF_STK hx pos e 1 _ _ _ ly1 S1 W1 regs1 mem1 md1 _ HC (or_introl eq_refl)).
assert (HCUT : CUT hx pos e 1 [(e_pp e, Layout.PP_SIZE)] (hi_L2 headamp_himg_B) (hi_shA headamp_himg_B)
  ly2 S2 W2 regs2 mem2 md2).
{ apply (hqu_cut_post hx pos e 1 _ _ _ ly1 S1 W1 regs1 mem1 md1 _ _ ly2 S2 W2 regs2 mem2 md2 _ HB HC HJ2 Hr Hperm Hkeep);
  [|exact HL2 | exact Hfsh2].
  intros a Ha [Hw|Hw].
  - destruct (hqu_cut_carried hx pos e 1 _ _ _ ly1 S1 W1 regs1 mem1 md1 a HB HC Ha) as (_ & _ & Hn & _). exact (Hn Hw).
  - destruct (hqu_cut_carried hx pos e 1 _ _ _ ly1 S1 W1 regs1 mem1 md1 a HB HC Ha) as (_ & _ & _ & _ & _ & Hb).
    apply (Hb _ _ Hpp). change (req_size Layout.PP_SIZE) with Layout.PP_SIZE. exact Hw. }
assert (Hwf : Model.pod_rec_wf (fst (Model.pod_build rest)))
  by exact (Model.pod_build_wf rest _ (snd (Model.pod_build rest)) (surjective_pairing _)).
assert (Hlen' : e_len e = Z.of_nat (length (Model.buf (fst (Model.pod_build rest))))) by (rewrite Hlen; reflexivity).
assert (Hb : 8 <= hd_len rest <= 5440) by exact (hd_len_bounds rest).
split; [exact (hqu_cut_rc LLVMF_STK hx pos e _ 1 _ _ ly2 S2 W2 regs2 mem2 md2 HCUT)|].
split; [exact HFRM|].
cbn [e_len e_pp e_cap e_null e_rc hqu_env_rc].
split; [exact Hwf|]. split; [exact Hlen'|]. split; [lia|]. split; [exact Hpp2|].
split; [exact Hcap | exact Hnull].
Qed.

(* ---- C3 -> M02 ---- *)
Lemma hqu_M02 : forall hx pos e r ly S W regs mem md,
  headamp_dup_contract (fx := fx) segs B ameter_triv headamp_himg_B RLO RHI ->
  BASE hx -> hqu_cut_C3 segs B LLVMF_STK hx fx pos e r ly S W regs mem md ->
  SRr segs W (@cfg_at fx segs (hi_c3 headamp_himg_B) regs mem md)
    (hd_seg_post segs B ameter_triv LLVMF_STK (spZ (hu_regs hx)) [] (hu_ly hx) (hu_S hx) (hu_W hx) (hu_mem hx)
      (hu_md hx) [(HQU_CID, pos)] 2 regs ly S W mem md (hi_c4 headamp_himg_B) (fun f => f = fx)
      (fun a => hd_inw e (hi_w2 headamp_himg_B) a \/ e_pod e <= a < e_pod e + e_len e)
      (fun W2 regs2 mem2 =>
       hd_cut segs (w_H W2) mem2 regs2 e (hi_L4 headamp_himg_B) /\
       hd_fsh segs (w_H W2) mem2 (e_F e) (hi_shA headamp_himg_B) /\
       garr8 segs (mrestrict (w_H W2) mem2) (e_pod e) (hd_zbytes (Model.buf r)))).
Proof.
intros hx pos e r ly S W regs mem md HDUP HB (HC & _ & Hwf & Hlen & _ & Hpp & _ & _ & _ & Hra & Hcap & Hnull).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & HL3 & _).
apply (HDUP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e pos r).
- apply (hqu_pre_of_cut hx pos e 2 _ _ _ ly S W regs mem md HB HC);
  [unfold HQU_EV; lia | left; reflexivity | exact Hcap | exact Hnull].
- exact HL3.
- exact Hwf.
- exact Hlen.
- exact Hpp.
- exact (hqu_fresh_of_cut LLVMF_STK hx pos e 2 _ _ _ ly S W regs mem md _ _ HC (or_intror (or_introl eq_refl))).
- exact Hra.
Qed.

(* ---- M02's post -> C4: the parse's answer, fixed at C2, enters the record here (Hrc) ---- *)
Lemma hqu_C4_cut : forall hx pos e r ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4,
  BASE hx -> hqu_cut_C3 segs B LLVMF_STK hx fx pos e r ly3 S3 W3 regs3 mem3 md3 ->
  e_rc e = ans_rc (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e)) ->
  J hx [(HQU_CID, pos)] ly4 S4 W4 mem4 md4 2 ->
  (forall rr : Z, rr = 2 \/ rr = 3 \/ rr = 4 -> getr regs4 (Z_to_bv 5 rr) = getr regs3 (Z_to_bv 5 rr)) ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs3 - T_SEG_STK <= a < spZ regs3) ->
   ~ (hd_inw e (hi_w2 headamp_himg_B) a \/ e_pod e <= a < e_pod e + e_len e) ->
   aview segs (w_H W4) mem4 a = aview segs (w_H W3) mem3 a) ->
  hd_cut segs (w_H W4) mem4 regs4 e (hi_L4 headamp_himg_B) ->
  hd_fsh segs (w_H W4) mem4 (e_F e) (hi_shA headamp_himg_B) ->
  garr8 segs (mrestrict (w_H W4) mem4) (e_pod e) (hd_zbytes (Model.buf r)) ->
  hqu_cut_C4 segs B LLVMF_STK hx fx pos e r ly4 S4 W4 regs4 mem4 md4.
Proof.
intros hx pos e r ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 HB HC3 Hrc HJ4 Hr Hperm Hkeep HL4 Hfsh4 Hpod4.
destruct HC3 as (HC & Hfrm & Hwf & Hlen & Hlb & Hpp & H16 & _ & Hamem & _ & Hcap & Hnull).
pose proof (hqu_cut_in LLVMF_STK hx pos e 2 _ _ _ ly3 S3 W3 regs3 mem3 md3 _ HC (or_introl eq_refl)) as Hpp3.
pose proof (hqu_cut_in LLVMF_STK hx pos e 2 _ _ _ ly3 S3 W3 regs3 mem3 md3 _ HC (or_intror (or_introl eq_refl))) as Hpod3.
pose proof (hqu_cut_facts hx pos e 2 _ _ _ ly3 S3 W3 regs3 mem3 md3 HB HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAR3).
assert (Hne : (e_pp e, Layout.PP_SIZE) <> (e_pod e, e_len e)) by (intros E; injection E as _ E; unfold Layout.PP_SIZE in E; lia).
pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hpp3 Hpod3 Hne) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
assert (Rl : req_size (e_len e) = e_len e) by (unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia).
change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hsep. rewrite Rl in Hsep.
assert (HCUT : CUT hx pos e 2 (hqu_blocks3 e) (hi_L4 headamp_himg_B) (hi_shA headamp_himg_B) ly4 S4 W4 regs4 mem4 md4).
{ apply (hqu_cut_post hx pos e 2 _ _ _ ly3 S3 W3 regs3 mem3 md3 _ _ ly4 S4 W4 regs4 mem4 md4 _ HB HC HJ4 Hr Hperm Hkeep);
  [|exact HL4 | exact Hfsh4].
  intros a Ha [Hw|Hw]; [exact (hqu_inw_nil e a Hw)|].
  destruct (hqu_cut_carried hx pos e 2 _ _ _ ly3 S3 W3 regs3 mem3 md3 a HB HC Ha) as (_ & _ & _ & _ & _ & Hb).
  apply (Hb _ _ Hpod3). rewrite Rl. exact Hw. }
pose proof (hqu_cut_facts hx pos e 2 _ _ _ ly4 S4 W4 regs4 mem4 md4 HB HCUT) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAR4).
pose proof (hqu_cut_in LLVMF_STK hx pos e 2 _ _ _ ly4 S4 W4 regs4 mem4 md4 _ HCUT (or_intror (or_introl eq_refl))) as Hpod4in.
destruct (hm_blk_ra segs B _ _ _ _ _ _ _ (e_pod e) (e_len e) HAR4 Hpod4in ltac:(lia) ltac:(rewrite Rl; lia)) as (Hra4 & Hhull4).
split; [exact HCUT|]. split; [exact Hfrm|].
split.
{ split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hlb|].
  split.
  { apply (hqu_blk_kept hx pos e 2 _ _ _ ly3 S3 W3 regs3 mem3 md3 _ _ _ W4 mem4 HB HC Hpp3 Hkeep).
    - intros a Ha [Hw|Hw]; [exact (hqu_inw_nil e a Hw)|].
      change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Ha. lia.
    - unfold hd_zbytes. rewrite length_map, (Layout.length_pp_bytes _ Hwf). change (req_size Layout.PP_SIZE) with Layout.PP_SIZE. lia.
    - exact Hpp. }
  split; [exact Hpod4|]. split; [exact H16|]. split; [apply Hhull4; lia|]. split; [exact Hamem|].
  split; [exact Hcap|]. split; [exact Hnull | exact Hrc]. }
exact Hra4.
Qed.

(* ---- C5 -> M03 ---- *)
Lemma hqu_M03 : forall hx pos e r ev ly S W regs mem md,
  headamp_check_contract segs B ameter_triv headamp_himg_B RLO RHI ->
  BASE hx -> hqu_cut_C5 segs B LLVMF_STK hx fx pos e r ev ly S W regs mem md ->
  SRr segs W (cfg_at segs (hi_c5 headamp_himg_B) regs mem md)
    (hd_seg_post segs B ameter_triv LLVMF_STK (spZ (hu_regs hx)) [] (hu_ly hx) (hu_S hx) (hu_W hx) (hu_mem hx)
      (hu_md hx) [(HQU_CID, pos)] 3 regs ly S W mem md (hi_c6 headamp_himg_B) (hd_fxk [8; 9; 10; 14; 15; 18; 19] fx)
      (fun a => hd_inw e (hi_w3 headamp_himg_B) a \/ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) \/
                (as_errno B <= a < as_errno B + 4))
      (fun W2 regs2 mem2 =>
       hd_cut segs (w_H W2) mem2 regs2 e (hi_L6 headamp_himg_B) /\
       hd_fsh segs (w_H W2) mem2 (e_F e) (hi_shB headamp_himg_B) /\
       garr8 segs (mrestrict (w_H W2) mem2) (e_out e)
         (hd_zbytes (ha_cells_bytes (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))) /\
       (exists ev', rd32 (aview segs (w_H W2) mem2) (as_errno B) ev'))).
Proof.
intros hx pos e r ev ly S W regs mem md HCHECK HB (HC & Hfrm & Hrec & Hrap & Hrao & Hap & Herr).
destruct Hrec as (Hwf & Hlen & _ & Hpp & Hpod & H16 & Hhull & Hamem & Hcap & Hnull & Hrc).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & HL5 & _).
apply (HCHECK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e pos ev r).
- apply (hqu_pre_of_cut hx pos e 3 _ _ _ ly S W regs mem md HB HC);
  [unfold HQU_EV; lia | left; reflexivity | exact Hcap | exact Hnull].
- exact HL5.
- exact Hwf.
- exact Hlen.
- exact Hpp.
- exact Hpod.
- exact (hqu_fresh_of_cut LLVMF_STK hx pos e 3 _ _ _ ly S W regs mem md _ _ HC (or_intror (or_introl eq_refl))).
- exact Hrap.
- exact Hhull.
- exact Hamem.
- exact H16.
- exact (hqu_fresh_of_cut LLVMF_STK hx pos e 3 _ _ _ ly S W regs mem md _ _ HC (or_intror (or_intror (or_introl eq_refl)))).
- exact Hrao.
- exact Hap.
- exact Hrc.
- exact Herr.
- exact Hfrm.
Qed.

(* ---- M03's post -> C6 ---- *)
Lemma hqu_C6_cut : forall hx pos e r ev ly5 S5 W5 regs5 mem5 md5 (fx3 : YK11.FPState) ly6 S6 W6 regs6 mem6 md6,
  BASE hx -> hqu_cut_C5 segs B LLVMF_STK hx fx pos e r ev ly5 S5 W5 regs5 mem5 md5 ->
  hd_fxk [8; 9; 10; 14; 15; 18; 19] fx fx3 ->
  J hx [(HQU_CID, pos)] ly6 S6 W6 mem6 md6 3 ->
  (forall rr : Z, rr = 2 \/ rr = 3 \/ rr = 4 -> getr regs6 (Z_to_bv 5 rr) = getr regs5 (Z_to_bv 5 rr)) ->
  Permutation (ablocks B ly6 S6) (ablocks B ly5 S5) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs5 - T_SEG_STK <= a < spZ regs5) ->
   ~ (hd_inw e (hi_w3 headamp_himg_B) a \/ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) \/
      (as_errno B <= a < as_errno B + 4)) ->
   aview segs (w_H W6) mem6 a = aview segs (w_H W5) mem5 a) ->
  hd_cut segs (w_H W6) mem6 regs6 e (hi_L6 headamp_himg_B) ->
  hd_fsh segs (w_H W6) mem6 (e_F e) (hi_shB headamp_himg_B) ->
  garr8 segs (mrestrict (w_H W6) mem6) (e_out e)
    (hd_zbytes (ha_cells_bytes (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))) ->
  (exists ev', rd32 (aview segs (w_H W6) mem6) (as_errno B) ev') ->
  hqu_cut_C6 segs B LLVMF_STK hx fx3 pos e r ly6 S6 W6 regs6 mem6 md6.
Proof.
intros hx pos e r ev ly5 S5 W5 regs5 mem5 md5 fx3 ly6 S6 W6 regs6 mem6 md6 HB HC5 Hfxk HJ6 Hr Hperm Hkeep
  HL6 Hfsh6 Hout6 Hev6.
destruct HC5 as (HC & _ & Hrec & _ & _ & Hap & _).
destruct Hrec as (Hwf & Hlen & Hlb & Hpp & Hpod & H16 & _ & Hamem & Hcap & Hnull & Hrc).
pose proof (hqu_cut_in LLVMF_STK hx pos e 3 _ _ _ ly5 S5 W5 regs5 mem5 md5 _ HC (or_introl eq_refl)) as Hpp5.
pose proof (hqu_cut_in LLVMF_STK hx pos e 3 _ _ _ ly5 S5 W5 regs5 mem5 md5 _ HC (or_intror (or_introl eq_refl))) as Hpod5.
pose proof (hqu_cut_in LLVMF_STK hx pos e 3 _ _ _ ly5 S5 W5 regs5 mem5 md5 _ HC (or_intror (or_intror (or_introl eq_refl)))) as Hout5.
pose proof (hqu_cut_facts hx pos e 3 _ _ _ ly5 S5 W5 regs5 mem5 md5 HB HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAR5).
assert (Rl : req_size (e_len e) = e_len e) by (unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia).
assert (Ro : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1)) by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
assert (Hne : (e_pp e, Layout.PP_SIZE) <> (e_out e, 3 * (e_cap e + 1))) by (intros E; injection E as _ E; unfold Layout.PP_SIZE in E; lia).
pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR5 Hpp5 Hout5 Hne) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hsep. rewrite Ro in Hsep.
assert (HCUT : CUT hx pos e 3 (hqu_blocks5 e) (hi_L6 headamp_himg_B) (hi_shB headamp_himg_B) ly6 S6 W6 regs6 mem6 md6).
{ apply (hqu_cut_post hx pos e 3 _ _ _ ly5 S5 W5 regs5 mem5 md5 _ _ ly6 S6 W6 regs6 mem6 md6 _ HB HC HJ6 Hr Hperm Hkeep);
  [|exact HL6 | exact Hfsh6].
  intros a Ha Hw.
  destruct (hqu_cut_carried hx pos e 3 _ _ _ ly5 S5 W5 regs5 mem5 md5 a HB HC Ha) as (_ & _ & _ & Hn3 & Hne3 & Hb).
  destruct Hw as [Hw|[Hw|Hw]]; [exact (Hn3 Hw) | apply (Hb _ _ Hout5); rewrite Ro; exact Hw | exact (Hne3 Hw)]. }
pose proof (hqu_cut_facts hx pos e 3 _ _ _ ly6 S6 W6 regs6 mem6 md6 HB HCUT) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAR6).
pose proof (hqu_cut_in LLVMF_STK hx pos e 3 _ _ _ ly6 S6 W6 regs6 mem6 md6 _ HCUT (or_intror (or_introl eq_refl))) as Hpod6.
pose proof (hqu_cut_in LLVMF_STK hx pos e 3 _ _ _ ly6 S6 W6 regs6 mem6 md6 _ HCUT (or_intror (or_intror (or_introl eq_refl)))) as Hout6in.
destruct (hm_blk_ra segs B _ _ _ _ _ _ _ (e_pod e) (e_len e) HAR6 Hpod6 ltac:(lia) ltac:(rewrite Rl; lia)) as (Hra6 & Hhull6).
destruct (hm_blk_ra segs B _ _ _ _ _ _ _ (e_out e) (3 * (e_cap e + 1)) HAR6 Hout6in ltac:(lia) ltac:(rewrite Ro; lia)) as (Hrao6 & _).
(* M03's write set misses the pp and the pod block *)
assert (HEb : forall p n, In (p, n) (ablocks B ly5 S5) -> (p + req_size n <= e_out e \/ e_out e + 3 * (e_cap e + 1) <= p) ->
  forall a, p <= a < p + req_size n ->
  ~ (hd_inw e (hi_w3 headamp_himg_B) a \/ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) \/
     (as_errno B <= a < as_errno B + 4))).
{ intros p n Hpn Hapart a Ha.
  destruct (hqu_cut_block hx pos e 3 _ _ _ ly5 S5 W5 regs5 mem5 md5 p n HB HC Hpn) as (_ & _ & _ & _ & _ & Hb).
  destruct (Hb a Ha) as (_ & _ & _ & _ & _ & Hw3 & Hwe).
  intros [Hw|[Hw|Hw]]; [exact (Hw3 Hw) | lia | exact (Hwe Hw)]. }
split; [exact HCUT|]. split; [exact (proj2 Hfxk)|].
split.
{ split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hlb|].
  split.
  { apply (hqu_blk_kept hx pos e 3 _ _ _ ly5 S5 W5 regs5 mem5 md5 _ _ _ W6 mem6 HB HC Hpp5 Hkeep).
    - apply (HEb _ _ Hpp5). change (req_size Layout.PP_SIZE) with Layout.PP_SIZE. lia.
    - unfold hd_zbytes. rewrite length_map, (Layout.length_pp_bytes _ Hwf). change (req_size Layout.PP_SIZE) with Layout.PP_SIZE. lia.
    - exact Hpp. }
  split.
  { apply (hqu_blk_kept hx pos e 3 _ _ _ ly5 S5 W5 regs5 mem5 md5 _ _ _ W6 mem6 HB HC Hpod5 Hkeep).
    - apply (HEb _ _ Hpod5). rewrite Rl. exact Hap.
    - unfold hd_zbytes. rewrite length_map, Rl. lia.
    - exact Hpod. }
  split; [exact H16|]. split; [apply Hhull6; lia|]. split; [exact Hamem|].
  split; [exact Hcap|]. split; [exact Hnull | exact Hrc]. }
split; [exact Hra6|]. split; [exact Hrao6|]. split; [exact Hout6 | exact Hev6].
Qed.

(* ---- C7 -> M04a (at the float state M03 returned at) ---- *)
Lemma hqu_M04a : forall (fx3 : YK11.FPState) hx pos e r ly S W regs mem md,
  headamp_first_contract (fx := fx3) segs B ameter_triv headamp_himg_B RLO RHI ->
  BASE hx -> hqu_cut_C7 segs B LLVMF_STK hx fx3 pos e r ly S W regs mem md ->
  SRr segs W (@cfg_at fx3 segs (hi_c7 headamp_himg_B) regs mem md)
    (hd_seg_post segs B ameter_triv LLVMF_STK (spZ (hu_regs hx)) [] (hu_ly hx) (hu_S hx) (hu_W hx) (hu_mem hx)
      (hu_md hx) [(HQU_CID, pos)] 4 regs ly S W mem md (hi_c8 headamp_himg_B) (fun f => f = fx3)
      (fun a => hd_inw e (hi_w4 headamp_himg_B) a \/ e_first e <= a < e_first e + hd_xv e XRc3NZ)
      (fun W2 regs2 mem2 =>
       hd_cut segs (w_H W2) mem2 regs2 e (hi_L8 headamp_himg_B) /\
       hd_fsh segs (w_H W2) mem2 (e_F e) (hi_shB headamp_himg_B) /\
       garr8 segs (mrestrict (w_H W2) mem2) (e_first e)
         (hd_zbytes (ha_cells_bytes (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))))).
Proof.
intros fx3 hx pos e r ly S W regs mem md HFIRST HB (HC & _ & Hrec & _ & Hrao & Hraf & Hout & _).
destruct Hrec as (_ & _ & _ & _ & _ & _ & _ & _ & Hcap & Hnull & Hrc).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & HL7 & _).
destruct (hqu_ans_rc (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as (Hrcb & Hcs).
rewrite <- Hrc in Hrcb, Hcs.
apply (HFIRST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e pos
  (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e)))).
- apply (hqu_pre_of_cut hx pos e 4 _ _ _ ly S W regs mem md HB HC);
  [unfold HQU_EV; lia | left; reflexivity | exact Hcap | exact Hnull].
- exact HL7.
- exact Hrcb.
- exact Hcs.
- exact Hout.
- exact Hrao.
- exact (hqu_fresh_of_cut LLVMF_STK hx pos e 4 _ _ _ ly S W regs mem md _ _ HC (or_intror (or_intror (or_introl eq_refl)))).
- exact (hqu_fresh_of_cut LLVMF_STK hx pos e 4 _ _ _ ly S W regs mem md _ _ HC
    (or_intror (or_intror (or_intror (or_introl eq_refl))))).
- exact Hraf.
Qed.

(* ---- M04a's post -> C8 ---- *)
Lemma hqu_C8_cut : forall (fx3 : YK11.FPState) hx pos e r ly7 S7 W7 regs7 mem7 md7 ly8 S8 W8 regs8 mem8 md8,
  BASE hx -> hqu_cut_C7 segs B LLVMF_STK hx fx3 pos e r ly7 S7 W7 regs7 mem7 md7 ->
  (e_pod e + e_len e <= e_first e \/ e_first e + hd_xv e XRc3NZ <= e_pod e) ->
  J hx [(HQU_CID, pos)] ly8 S8 W8 mem8 md8 4 ->
  (forall rr : Z, rr = 2 \/ rr = 3 \/ rr = 4 -> getr regs8 (Z_to_bv 5 rr) = getr regs7 (Z_to_bv 5 rr)) ->
  Permutation (ablocks B ly8 S8) (ablocks B ly7 S7) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs7 - T_SEG_STK <= a < spZ regs7) ->
   ~ (hd_inw e (hi_w4 headamp_himg_B) a \/ e_first e <= a < e_first e + hd_xv e XRc3NZ) ->
   aview segs (w_H W8) mem8 a = aview segs (w_H W7) mem7 a) ->
  hd_cut segs (w_H W8) mem8 regs8 e (hi_L8 headamp_himg_B) ->
  hd_fsh segs (w_H W8) mem8 (e_F e) (hi_shB headamp_himg_B) ->
  garr8 segs (mrestrict (w_H W8) mem8) (e_first e)
    (hd_zbytes (ha_cells_bytes (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))) ->
  hqu_cut_C8 segs B LLVMF_STK hx fx3 pos e r ly8 S8 W8 regs8 mem8 md8.
Proof.
intros fx3 hx pos e r ly7 S7 W7 regs7 mem7 md7 ly8 S8 W8 regs8 mem8 md8 HB HC7 Hapf HJ8 Hr Hperm Hkeep HL8 Hfsh8 Hfirst8.
destruct HC7 as (HC & Hfrm & Hrec & _ & _ & _ & _ & (ev & Hev)).
destruct Hrec as (Hwf & Hlen & Hlb & Hpp & Hpod & H16 & _ & Hamem & Hcap & Hnull & Hrc).
pose proof (hqu_cut_in LLVMF_STK hx pos e 4 _ _ _ ly7 S7 W7 regs7 mem7 md7 _ HC (or_introl eq_refl)) as Hpp7.
pose proof (hqu_cut_in LLVMF_STK hx pos e 4 _ _ _ ly7 S7 W7 regs7 mem7 md7 _ HC (or_intror (or_introl eq_refl))) as Hpod7.
pose proof (hqu_cut_in LLVMF_STK hx pos e 4 _ _ _ ly7 S7 W7 regs7 mem7 md7 _ HC
  (or_intror (or_intror (or_intror (or_introl eq_refl))))) as Hfst7.
pose proof (hqu_cut_facts hx pos e 4 _ _ _ ly7 S7 W7 regs7 mem7 md7 HB HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAR7).
assert (Rl : req_size (e_len e) = e_len e) by (unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia).
destruct (hqu_ans_rc (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as (Hrcb & _).
rewrite <- Hrc in Hrcb.
pose proof (proj1 (headamp_A_site_malloc_first e Hrcb Hcap)) as Hq.
assert (Rq : req_size (hd_xv e XRc3NZ) = hd_xv e XRc3NZ) by (unfold req_size; destruct (Z.eqb_spec (hd_xv e XRc3NZ) 0); lia).
assert (Hne : (e_pp e, Layout.PP_SIZE) <> (e_first e, hd_xv e XRc3NZ)).
{ intros E. assert (E2 : Layout.PP_SIZE = hd_xv e XRc3NZ) by exact (f_equal snd E).
  unfold Layout.PP_SIZE in E2. lia. }
pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR7 Hpp7 Hfst7 Hne) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hsep. rewrite Rq in Hsep.
assert (HE : forall p n, In (p, n) (ablocks B ly7 S7) -> (p + req_size n <= e_first e \/ e_first e + hd_xv e XRc3NZ <= p) ->
  forall a, p <= a < p + req_size n -> ~ (hd_inw e (hi_w4 headamp_himg_B) a \/ e_first e <= a < e_first e + hd_xv e XRc3NZ)).
{ intros p n Hpn Hapart a Ha [Hw|Hw]; [exact (hqu_inw_nil e a Hw) | lia]. }
assert (HCUT : CUT hx pos e 4 (hqu_blocks7 e) (hi_L8 headamp_himg_B) (hi_shB headamp_himg_B) ly8 S8 W8 regs8 mem8 md8).
{ apply (hqu_cut_post hx pos e 4 _ _ _ ly7 S7 W7 regs7 mem7 md7 _ _ ly8 S8 W8 regs8 mem8 md8 _ HB HC HJ8 Hr Hperm Hkeep);
  [|exact HL8 | exact Hfsh8].
  intros a Ha [Hw|Hw]; [exact (hqu_inw_nil e a Hw)|].
  destruct (hqu_cut_carried hx pos e 4 _ _ _ ly7 S7 W7 regs7 mem7 md7 a HB HC Ha) as (_ & _ & _ & _ & _ & Hb).
  apply (Hb _ _ Hfst7). rewrite Rq. exact Hw. }
pose proof (hqu_cut_facts hx pos e 4 _ _ _ ly8 S8 W8 regs8 mem8 md8 HB HCUT) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAR8).
pose proof (hqu_cut_in LLVMF_STK hx pos e 4 _ _ _ ly8 S8 W8 regs8 mem8 md8 _ HCUT (or_intror (or_introl eq_refl))) as Hpod8.
pose proof (hqu_cut_in LLVMF_STK hx pos e 4 _ _ _ ly8 S8 W8 regs8 mem8 md8 _ HCUT (or_intror (or_intror (or_introl eq_refl)))) as Hout8.
pose proof (hqu_cut_in LLVMF_STK hx pos e 4 _ _ _ ly8 S8 W8 regs8 mem8 md8 _ HCUT
  (or_intror (or_intror (or_intror (or_introl eq_refl))))) as Hfst8.
destruct (hm_blk_ra segs B _ _ _ _ _ _ _ (e_pod e) (e_len e) HAR8 Hpod8 ltac:(lia) ltac:(rewrite Rl; lia)) as (Hra8 & Hhull8).
assert (Ro : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1)) by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
destruct (hm_blk_ra segs B _ _ _ _ _ _ _ (e_out e) (3 * (e_cap e + 1)) HAR8 Hout8 ltac:(lia) ltac:(rewrite Ro; lia)) as (Hrao8 & _).
destruct (hm_blk_ra segs B _ _ _ _ _ _ _ (e_first e) (hd_xv e XRc3NZ) HAR8 Hfst8 ltac:(lia) ltac:(rewrite Rq; lia)) as (Hraf8 & _).
split; [exact HCUT|]. split; [exact Hfrm|].
split.
{ split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hlb|].
  split.
  { apply (hqu_blk_kept hx pos e 4 _ _ _ ly7 S7 W7 regs7 mem7 md7 _ _ _ W8 mem8 HB HC Hpp7 Hkeep).
    - apply (HE _ _ Hpp7). change (req_size Layout.PP_SIZE) with Layout.PP_SIZE. lia.
    - unfold hd_zbytes. rewrite length_map, (Layout.length_pp_bytes _ Hwf). change (req_size Layout.PP_SIZE) with Layout.PP_SIZE. lia.
    - exact Hpp. }
  split.
  { apply (hqu_blk_kept hx pos e 4 _ _ _ ly7 S7 W7 regs7 mem7 md7 _ _ _ W8 mem8 HB HC Hpod7 Hkeep).
    - apply (HE _ _ Hpod7). rewrite Rl. exact Hapf.
    - unfold hd_zbytes. rewrite length_map, Rl. lia.
    - exact Hpod. }
  split; [exact H16|]. split; [apply Hhull8; lia|]. split; [exact Hamem|].
  split; [exact Hcap|]. split; [exact Hnull | exact Hrc]. }
split; [exact Hra8|]. split; [exact Hrao8|]. split; [exact Hraf8|]. split; [exact Hfirst8|].
exists ev.
apply (hqu_errno_kept hx pos e 4 _ _ _ ly7 S7 W7 regs7 mem7 md7 _ W8 mem8 ev HB HC Hkeep); [|exact Hev].
intros a Ha [Hw|Hw]; [exact (hqu_inw_nil e a Hw)|].
destruct (hqu_cut_block hx pos e 4 _ _ _ ly7 S7 W7 regs7 mem7 md7 _ _ HB HC Hfst7) as (_ & _ & _ & _ & _ & Hb).
destruct (Hb a ltac:(rewrite Rq; lia)) as (_ & _ & _ & _ & _ & _ & Hne'). exact (Hne' Ha).
Qed.

(* ---- C8 -> M04b (at the float state M03 returned at) ---- *)
Lemma hqu_M04b : forall (fx3 : YK11.FPState) hx pos e r ly S W regs mem md,
  headamp_plain_contract (fx := fx3) segs B ameter_triv headamp_himg_B RLO RHI ->
  BASE hx -> hqu_cut_C8 segs B LLVMF_STK hx fx3 pos e r ly S W regs mem md ->
  (e_pod e + e_len e <= e_out e \/ e_out e + 3 * (e_cap e + 1) <= e_pod e) ->
  SRr segs W (@cfg_at fx3 segs (hi_c8 headamp_himg_B) regs mem md)
    (hd_seg_post segs B ameter_triv LLVMF_STK (spZ (hu_regs hx)) [] (hu_ly hx) (hu_S hx) (hu_W hx) (hu_mem hx)
      (hu_md hx) [(HQU_CID, pos)] 4 regs ly S W mem md (hi_c9 headamp_himg_B) (hd_fxk [14; 15] fx3)
      (fun a => hd_inw e (hi_w5 headamp_himg_B) a \/ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) \/
                (as_errno B <= a < as_errno B + 4))
      (fun W2 regs2 mem2 =>
       hd_cut segs (w_H W2) mem2 regs2 e (hi_L9 headamp_himg_B) /\
       hd_fsh segs (w_H W2) mem2 (e_F e) (hi_shB headamp_himg_B) /\
       (exists ev', rd32 (aview segs (w_H W2) mem2) (as_errno B) ev'))).
Proof.
intros fx3 hx pos e r ly S W regs mem md HPLAIN HB (HC & Hfrm & Hrec & Hrap & Hrao & Hraf & Hfirst & (ev & Hev)) Hap.
destruct Hrec as (Hwf & Hlen & _ & _ & Hpod & H16 & Hhull & Hamem & Hcap & Hnull & Hrc).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & HL8 & _).
apply (HPLAIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e pos ev r).
- apply (hqu_pre_of_cut hx pos e 4 _ _ _ ly S W regs mem md HB HC);
  [unfold HQU_EV; lia | left; reflexivity | exact Hcap | exact Hnull].
- exact HL8.
- exact Hwf.
- exact Hlen.
- exact Hpod.
- exact (hqu_fresh_of_cut LLVMF_STK hx pos e 4 _ _ _ ly S W regs mem md _ _ HC (or_intror (or_introl eq_refl))).
- exact Hrap.
- exact Hhull.
- exact Hamem.
- exact H16.
- exact (hqu_fresh_of_cut LLVMF_STK hx pos e 4 _ _ _ ly S W regs mem md _ _ HC (or_intror (or_intror (or_introl eq_refl)))).
- exact Hrao.
- exact Hap.
- exact (hqu_fresh_of_cut LLVMF_STK hx pos e 4 _ _ _ ly S W regs mem md _ _ HC
    (or_intror (or_intror (or_intror (or_introl eq_refl))))).
- exact Hraf.
- exact Hfirst.
- exact Hrc.
- exact Hev.
- exact Hfrm.
Qed.

(* ---- M04b's post -> C9 ---- *)
Lemma hqu_C9_cut : forall (fx3 fx4 : YK11.FPState) hx pos e r ly8 S8 W8 regs8 mem8 md8 ly9 S9 W9 regs9 mem9 md9,
  BASE hx -> hqu_cut_C8 segs B LLVMF_STK hx fx3 pos e r ly8 S8 W8 regs8 mem8 md8 ->
  hd_fxk [14; 15] fx3 fx4 ->
  J hx [(HQU_CID, pos)] ly9 S9 W9 mem9 md9 4 ->
  (forall rr : Z, rr = 2 \/ rr = 3 \/ rr = 4 -> getr regs9 (Z_to_bv 5 rr) = getr regs8 (Z_to_bv 5 rr)) ->
  Permutation (ablocks B ly9 S9) (ablocks B ly8 S8) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs8 - T_SEG_STK <= a < spZ regs8) ->
   ~ (hd_inw e (hi_w5 headamp_himg_B) a \/ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) \/
      (as_errno B <= a < as_errno B + 4)) ->
   aview segs (w_H W9) mem9 a = aview segs (w_H W8) mem8 a) ->
  hd_cut segs (w_H W9) mem9 regs9 e (hi_L9 headamp_himg_B) ->
  hd_fsh segs (w_H W9) mem9 (e_F e) (hi_shB headamp_himg_B) ->
  hqu_cut_C9 segs B LLVMF_STK hx fx4 pos e ly9 S9 W9 regs9 mem9 md9.
Proof.
intros fx3 fx4 hx pos e r ly8 S8 W8 regs8 mem8 md8 ly9 S9 W9 regs9 mem9 md9 HB HC8 Hfxk HJ9 Hr Hperm Hkeep HL9 Hfsh9.
destruct HC8 as (HC & _ & Hrec & _).
destruct Hrec as (_ & _ & Hlb & _ & _ & _ & _ & _ & Hcap & _).
pose proof (hqu_cut_in LLVMF_STK hx pos e 4 _ _ _ ly8 S8 W8 regs8 mem8 md8 _ HC (or_intror (or_intror (or_introl eq_refl)))) as Hout8.
assert (Ro : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1)) by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
split.
{ apply (hqu_cut_post hx pos e 4 _ _ _ ly8 S8 W8 regs8 mem8 md8 _ _ ly9 S9 W9 regs9 mem9 md9 _ HB HC HJ9 Hr Hperm Hkeep);
  [|exact HL9 | exact Hfsh9].
  intros a Ha Hw.
  destruct (hqu_cut_carried hx pos e 4 _ _ _ ly8 S8 W8 regs8 mem8 md8 a HB HC Ha) as (_ & _ & _ & _ & Hne & Hb).
  destruct Hw as [Hw|[Hw|Hw]]; [exact (hqu_inw_nil e a Hw) | apply (Hb _ _ Hout8); rewrite Ro; exact Hw | exact (Hne Hw)]. }
split; [exact (proj2 Hfxk)|]. split; [exact Hcap | exact Hlb].
Qed.

(* ---- the malloc steps' appended block lies apart from an older block ---- *)
Lemma hqu_app_apart : forall ly S W mem md (l : list (Z * Z)) p n q m,
  AR segs B ly S W mem md -> ablocks B ly S = l ++ [(q, m)] -> In (p, n) l ->
  p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros ly S W mem md l p n q m HAR E Hin.
apply in_split in Hin as (l1 & l2 & ->).
assert (E' : ablocks B ly S = l1 ++ (p, n) :: l2 ++ (q, m) :: []) by (rewrite E, <- app_assoc; reflexivity).
pose proof (sep_blocks_pos segs B LAWS ly S W mem md (p, n) (q, m) l1 l2 [] HAR E') as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.

(* first, the block the malloc(first) step appends, lies apart from the pod block *)
Lemma hqu_first_apart : forall (fx3 : YK11.FPState) hx pos e r ly6 S6 W6 regs6 mem6 md6 first ly7 S7 W7 regs7 mem7 md7,
  BASE hx -> hqu_cut_C6 segs B LLVMF_STK hx fx3 pos e r ly6 S6 W6 regs6 mem6 md6 ->
  ablocks B ly7 S7 = ablocks B ly6 S6 ++ [(first, hd_xv e XRc3NZ)] ->
  hqu_cut_C7 segs B LLVMF_STK hx fx3 pos (hqu_env_first e first) r ly7 S7 W7 regs7 mem7 md7 ->
  e_pod e + e_len e <= first \/ first + hd_xv e XRc3NZ <= e_pod e.
Proof.
intros fx3 hx pos e r ly6 S6 W6 regs6 mem6 md6 first ly7 S7 W7 regs7 mem7 md7 HB HC6 Hab HC7.
destruct HC6 as (HC6c & _ & Hrec6 & _). destruct Hrec6 as (_ & _ & Hlb & _ & _ & _ & _ & _ & Hcap & _ & Hrc).
destruct HC7 as (HC7c & _).
pose proof (hqu_cut_facts hx pos _ 4 _ _ _ ly7 S7 W7 regs7 mem7 md7 HB HC7c)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAR7).
pose proof (hqu_cut_in LLVMF_STK hx pos e 3 _ _ _ ly6 S6 W6 regs6 mem6 md6 (e_pod e, e_len e) HC6c
  (or_intror (or_introl eq_refl))) as Hpod6.
pose proof (hqu_app_apart ly7 S7 W7 mem7 md7 _ _ _ _ _ HAR7 Hab Hpod6) as Hd.
destruct (hqu_ans_rc (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as (Hrcb & _). rewrite <- Hrc in Hrcb.
pose proof (proj1 (headamp_A_site_malloc_first e Hrcb Hcap)) as Hq.
assert (R1 : req_size (e_len e) = e_len e) by (unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia).
assert (R2 : req_size (hd_xv e XRc3NZ) = hd_xv e XRc3NZ)
  by (unfold req_size; destruct (Z.eqb_spec (hd_xv e XRc3NZ) 0); lia).
rewrite R1, R2 in Hd. exact Hd.
Qed.

(* ============================ the whole run ============================ *)
Variable K : asink_syms.
Variables XM_LIB XN_LIB : Z -> Z.
Variable A_LLVMF : Z.
Context {LS : lib_shape}.
(* the harness's entry (image B: the core's YCfn.A_LLVMF; by computation) *)
Hypothesis HA : A_LLVMF = HQU_ENTRY.
(* the core's sink laws at the symbols (knock: AD1u.tfib_AIL) *)
Hypothesis AIL : asink_img_laws segs B K.
(* the lib shape's one-leaf law (headamp_lib_x_all_stmt's first premise) *)
Hypothesis LEAF : forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs []).
(* E01: ENTRY -> C1 *)
Hypothesis HE01 : hqu_S_E01_stmt segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* M01: HPgMainL.headamp_build_holds *)
Hypothesis HBUILD : headamp_build_contract segs B ameter_triv headamp_himg_B RLO RHI.
(* the malloc(pod) step: C2 -> C3 *)
Hypothesis HC23 : hqu_S_C23_stmt segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* M02 *)
Hypothesis HDUP : headamp_dup_contract segs B ameter_triv headamp_himg_B RLO RHI.
(* the malloc(out) step: C4 -> C5 *)
Hypothesis HC45 : hqu_S_C45_stmt segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* M03: HPgSegM.headamp_check_holds *)
Hypothesis HCHECK : headamp_check_contract segs B ameter_triv headamp_himg_B RLO RHI.
(* the malloc(first) step: C6 -> C7 *)
Hypothesis HC67 : hqu_S_C67_stmt segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* M04a and M04b, at every float state (they run at the state M03 returns at) *)
Hypothesis HFIRST : forall fx' : YK11.FPState, headamp_first_contract (fx := fx') segs B ameter_triv headamp_himg_B RLO RHI.
Hypothesis HPLAIN : forall fx' : YK11.FPState, headamp_plain_contract (fx := fx') segs B ameter_triv headamp_himg_B RLO RHI.
(* X01: the four frees, then the frame's release and the epilogue *)
Hypothesis HX01f : hqu_S_X01f_stmt segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Hypothesis HX01r : hqu_S_X01r_stmt segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.

Theorem headamp_lib_x : hd_lib_contract_x segs B ameter_triv K XM_LIB XN_LIB RLO RHI
  A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros ly S W regs mem md p n pl M Kl HAI HPRE HK.
rewrite LEAF.
destruct HPRE as (HPRE0 & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK & HFD & HSORT
  & HAM & HMOK & HFRM).
set (hx := {| hu_ly := ly; hu_S := S; hu_W := W; hu_regs := regs; hu_mem := mem; hu_md := md; hu_p := p; hu_n := n;
  hu_pl := pl |} : hqu_hcx segs).
assert (HB : hqu_base segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx).
{ exact (conj HPRE0 (conj Hra (conj Hp (conj Hn (conj Hpn (conj Hnpl (conj HPL (conj Hfr0 (conj Hev
    (conj Hlive HROS)))))))))). }
eapply SRr_srealizes; [| exact HAI |].
2: { intros W' c' Hle HAI' HQ. apply (HK _ W' c' Hle HAI'). exact HQ. }
rewrite HA.
(* E01 *)
eapply SRr_bind; [exact (HE01 hx HB)|].
intros W1 c1 _ (pos & e & rest & ly1 & S1 & regs1 & mem1 & md1 & -> & HC1).
pose proof (hqu_C1_pre hx pos e rest ly1 S1 W1 regs1 mem1 md1 HB HC1) as HPRE1.
pose proof HC1 as (HC1c & _ & Hin).
pose proof HC1c as (_ & _ & _ & _ & _ & _ & _ & HL1 & _).
pose proof Hin as (Hleft & Hlen & Harr & Hra1 & Hsrc & Hhi & Hamem & Hhull & Hdis).
(* M01 *)
eapply SRr_bind; [exact (HBUILD LLVMF_STK (spZ regs) [] ly S W mem md [(HQU_CID, pos)] ly1 S1 W1 mem1 md1 1 regs1
  e pos rest HPRE1 HL1 Hleft Hlen Harr Hra1 Hsrc Hhi Hamem Hhull Hdis)|].
intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & Ec2 & Efx & HJ2 & Hr2 & Hfr2 & Hperm2 & Hio2 & Hmo2 & Hkept2
  & HL2 & Hfsh2 & Hpp2).
subst fx2. subst c2.
pose proof (hqu_C2_cut hx pos e rest ly1 S1 W1 regs1 mem1 md1 ly2 S2 W2 regs2 mem2 md2 HB HC1 HFRM HJ2 Hr2 Hperm2
  Hkept2 HL2 Hfsh2 Hpp2) as HC2.
set (r := fst (Model.pod_build rest)) in HC2.
set (e2 := hqu_env_rc e (hqu_rc_of e r)) in HC2.
(* the malloc(pod) step *)
eapply SRr_bind; [exact (HC23 hx fx pos e2 r ly2 S2 W2 regs2 mem2 md2 HB HC2)|].
intros W3 c3 _ (pod & ly3 & S3 & regs3 & mem3 & md3 & -> & _ & _ & _ & _ & _ & _ & HC3).
set (e3 := hqu_env_pod e2 pod) in HC3.
(* M02 *)
eapply SRr_bind; [exact (hqu_M02 hx pos e3 r ly3 S3 W3 regs3 mem3 md3 HDUP HB HC3)|].
intros W4 c4 _ (fx4 & ly4 & S4 & regs4 & mem4 & md4 & Ec4 & Efx4 & HJ4 & Hr4 & Hfr4 & Hperm4 & Hio4 & Hmo4 & Hkept4
  & HL4 & Hfsh4 & Hpod4).
subst fx4. subst c4.
(* the parse's answer, fixed at C2: e3's rc, null flag and cap are e's *)
assert (Hrc3 : e_rc e3 = ans_rc (Headamp.parse_props (hd_props (e_null e3) (Model.buf r)) (e_cap e3)))
  by reflexivity.
pose proof (hqu_C4_cut hx pos e3 r ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 HB HC3 Hrc3 HJ4 Hr4 Hperm4
  Hkept4 HL4 Hfsh4 Hpod4) as HC4.
(* the malloc(out) step *)
eapply SRr_bind; [exact (HC45 hx fx pos e3 r ly4 S4 W4 regs4 mem4 md4 HB HC4)|].
intros W5 c5 _ (out & ev5 & ly5 & S5 & regs5 & mem5 & md5 & -> & _ & _ & _ & _ & _ & _ & HC5).
set (e5 := hqu_env_out e3 out) in HC5.
pose proof HC5 as (_ & _ & _ & _ & _ & Hap & _).
(* M03 *)
eapply SRr_bind; [exact (hqu_M03 hx pos e5 r ev5 ly5 S5 W5 regs5 mem5 md5 HCHECK HB HC5)|].
intros W6 c6 _ (fx3 & ly6 & S6 & regs6 & mem6 & md6 & -> & Hfxk3 & HJ6 & Hr6 & Hfr6 & Hperm6 & Hio6 & Hmo6 & Hkept6
  & HL6 & Hfsh6 & Hout6 & Hev6).
pose proof (hqu_C6_cut hx pos e5 r ev5 ly5 S5 W5 regs5 mem5 md5 fx3 ly6 S6 W6 regs6 mem6 md6 HB HC5 Hfxk3 HJ6
  Hr6 Hperm6 Hkept6 HL6 Hfsh6 Hout6 Hev6) as HC6.
(* the malloc(first) step *)
eapply SRr_bind; [exact (HC67 hx fx3 pos e5 r ly6 S6 W6 regs6 mem6 md6 HB HC6)|].
intros W7 c7 _ (first & ly7 & S7 & regs7 & mem7 & md7 & -> & _ & _ & _ & _ & Hab7 & _ & HC7).
set (e7 := hqu_env_first e5 first) in HC7.
(* first lies apart from pod (the block the malloc(first) step appends) *)
assert (Hapf : e_pod e7 + e_len e7 <= e_first e7 \/ e_first e7 + hd_xv e7 XRc3NZ <= e_pod e7)
  by exact (hqu_first_apart fx3 hx pos e5 r ly6 S6 W6 regs6 mem6 md6 first ly7 S7 W7 regs7 mem7 md7 HB HC6 Hab7 HC7).
(* M04a *)
eapply SRr_bind; [exact (hqu_M04a fx3 hx pos e7 r ly7 S7 W7 regs7 mem7 md7 (HFIRST fx3) HB HC7)|].
intros W8 c8 _ (fx8 & ly8 & S8 & regs8 & mem8 & md8 & Ec8 & Efx8 & HJ8 & Hr8 & Hfr8 & Hperm8 & Hio8 & Hmo8 & Hkept8
  & HL8 & Hfsh8 & Hfst8).
subst fx8. subst c8.
pose proof (hqu_C8_cut fx3 hx pos e7 r ly7 S7 W7 regs7 mem7 md7 ly8 S8 W8 regs8 mem8 md8 HB HC7 Hapf HJ8 Hr8 Hperm8
  Hkept8 HL8 Hfsh8 Hfst8) as HC8.
(* M04b *)
eapply SRr_bind; [exact (hqu_M04b fx3 hx pos e7 r ly8 S8 W8 regs8 mem8 md8 (HPLAIN fx3) HB HC8 Hap)|].
intros W9 c9 _ (fx9 & ly9 & S9 & regs9 & mem9 & md9 & -> & Hfxk9 & HJ9 & Hr9 & Hfr9 & Hperm9 & Hio9 & Hmo9 & Hkept9
  & HL9 & Hfsh9 & _).
pose proof (hqu_C9_cut fx3 fx9 hx pos e7 r ly8 S8 W8 regs8 mem8 md8 ly9 S9 W9 regs9 mem9 md9 HB HC8 Hfxk9 HJ9 Hr9
  Hperm9 Hkept9 HL9 Hfsh9) as HC9.
(* X01 *)
eapply SRr_bind; [exact (HX01f hx fx9 pos e7 ly9 S9 W9 regs9 mem9 md9 HB HC9)|].
intros WJ cJ _ (lyJ & SJ & regsJ & memJ & mdJ & kJ & -> & HCJ).
eapply SRr_mono; [exact (HX01r hx fx9 pos e7 kJ lyJ SJ WJ regsJ memJ mdJ HB HCJ)|].
intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & k' & -> & Hfrm' & HJ' & Hk' & HPR & Ha0 & HPerm).
(* the leaf [knock APgLib.v:216-239] *)
exists fx', ly', S', regs', mem', md', k'. split; [reflexivity|]. split; [exact Hfrm'|].
destruct (hqu_ajournal_nil_io segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ') as [Efds Efs].
unfold hd_lib_post_x. cbn [ll_fs ll_ret ll_out].
split; [apply hqu_ajournal_fp_nil; exact HJ'|].
split; [unfold HQU_EV in *; lia|]. split; [exact HPR|]. split; [exact Ha0|]. split; [exact HPerm|].
split; [intros fd; rewrite Efds; reflexivity|].
split; [exact Efs|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT|].
split; [eapply (asink_none_kept segs B K AIL); [exact HJ' | intros Ho; exact (sink_closed_nil Ho) | exact HSNK]|].
split; [exact (ameta_inv_kept segs B K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' HAM)|].
split; [exact I|].
intros i Hi. destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; lia|].
pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hpin).
- eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. exact Hpin.
- unfold req_size. destruct (Z.eqb_spec n 0) as [Heq0|Hne0]; [exfalso; lia | exact Hi].
- apply inFP_nil.
Qed.
End c.
End g.

Print Assumptions headamp_lib_x.
