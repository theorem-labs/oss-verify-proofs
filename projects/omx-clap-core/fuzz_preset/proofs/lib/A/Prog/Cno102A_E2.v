(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 1292 of its 1364 lines of code are new or changed and 442 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c): segment CA2 of the re-walk of check_no_overread
   (cno): the FIRST PADDED COPY, CN_COPY1 (+388) to CN_COPY2 (+460). FREE-PIECES-102 Part 7
   row R7-3.
   rule 24: proves no function (kind: segment lemma).
   THE CODE (DERIVED offsets from cno's entry):
     +388 .. +392  s3 = size + 16; a0 = s3;         +396 jal __wrap_malloc
     +400 .. +408  s5 = a0 (r1); s8 = the hi of g_own_ran_out (PHi 9); beqz a0 -> +452 (the refused arm)
     +412 .. +428  beqz s4 (size = 0) -> +432; a0 = s5, a1 = s7 (data), a2 = s4; jal __asan_memcpy
     +432 .. +444  a0 = s5 + s4; a1 = 0x31; a2 = 16; jal __asan_memset (the padding's magic)
     +448          j +12 -> +460
     +452 .. +456  (refused) a0 = 1; sb a0, -0x558(s8): g_own_ran_out := 1; falls to +460
   THE RELATION: this segment is proved at ARx := ARcfx (ARcf /\ xs_placed_cf), the lane's cf instance
   (Cno102A_F.v:109-122, Caw102A_WA0's ruling 13:5xZ): the malloc call rule, the room keep and the room position are
   cf-level. CA0 / CA1 are proved at a generic ARx, so the five compose at ARcfx (Cno102A_EC.v cn_E, by
   cn_seg_E_of_segs).
   SECTION HYPOTHESES (owners): IMG : cn_img B, PAL : PALib B, IMGSH (the image's shadow is mapped in every ARcf
   state) (the image binding); AMALLOC : YGcfMallocComposeKeep.amalloc_realizes_cf_keep (the malloc row's keep twin); ACPY / ASET :
   YGcallMxmn.aintrin_realizes_xm at this image's __asan_memcpy / __asan_memset (the runtime rows of the A' pin);
   HW : prh_head_wide. The room law is prh_room_malloc_a8 (Cno102A_Base.v), a local instance.
   Numerals: offsets (DERIVED); 16 (LENGTH: the pad); 0x31 (LENGTH: the pad's fill byte); register numbers (WORD);
   the seven PST cell addresses 6149472 / 6149504 / 6149536 / 681408 / 6149568 / 681440 / 6149440 (ADDRESS:
   PRH_Img.v's pi_g_live / pi_g_peak / pi_g_count / pi_g_fail / pi_g_ran_out / pi_g_most / pi_g_own_ran_out at
   prh_img_A, written as Cno102A_R5.v :923-949 writes them, each only inside a `change` that names the field). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YImgTop YG00cf YG01cf YG0ncf YG0dcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcallx YGcallcf YGcallSx YGcallMx YGcallMxmn FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveSec PresetLiveBounds PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Cno102A_Base Cno102A_Ro
  Cno102A_E Cno102A_E0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Refute.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmnKeep YGcfMallocComposeKeep.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the unwinder's trace of a call state is prh_trace of the state's ra and the chain's spine (YG00.v:376
   unwind_of_chain, PRH_Base.v:1034 prh_trace: the same filter, the same cut) *)
Lemma e2_trace_eq : forall pc0 regs ch, call_trace0 pc0 regs ch = prh_trace pc0 (raZ regs) (spine ch).
Proof.
intros pc0 regs ch. unfold call_trace0, unwind_of_chain, prh_trace, spine.
cbn [flat_map]. do 3 f_equal.
induction ch as [|[[sp ra] s0] t IH]; cbn [flat_map map fst snd]; [reflexivity | rewrite IH; reflexivity].
Qed.

Section e2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
(* the allocator parameters and the room of the instance (the lane's ruling, 13:5xZ: RL_malloc_step's bounds are
   CfParams_preset's; the malloc law is prh_room_malloc_a8 (Cno102A_Base.v)) *)
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_room_live_a8.
#[local] Existing Instance prh_room_malloc_a8.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Existing Instance PL_cno_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable B : asyms.
Variable CTX0 : list (list Z).
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Hypothesis IMG : cn_img B.
Hypothesis PAL : PALib (rc := rc) (L := A_prog_listing) (PI := PA) B.
Hypothesis HW : prh_head_wide.
(* the image's shadow is mapped in every ARcf state (lib/A/AImgShadowVisCf.v tfib_img_shadow_vis_cf at the instance;
   an image binding, as PAL is): the hull of a range 64 bytes inside the image band *)
Hypothesis IMGSH : forall ly S Hp W mem md a, ARcf SEGS B ly S Hp W mem md -> pa_lo <= a < pa_hi ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* the keep form: part 3c took the memnorm keep out of the plain contract's post, and this walk carries P across the
   call with it (PCALL below), so it cites the keep twin *)
Hypothesis AMALLOC : forall fz : YK11.FPState, YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fz) SEGS B.
Hypothesis ACPY : forall fz : YK11.FPState, aintrin_realizes_xm (fx := fz) SEGS B ARcfx OCpy (SIGMA AS___asan_memcpy).
Hypothesis ASET : forall fz : YK11.FPState, aintrin_realizes_xm (fx := fz) SEGS B ARcfx OSet (SIGMA AS___asan_memset).
Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B LAWS_cf.
Let OWNLOW := ARx_owned_low_law_xs SEGS B LAWS_cf.
Let WFL := ARx_wf_law_xs SEGS B.
Let XSL := ARx_xs_law_xs SEGS B.

(* cno keeps a frame pointer, and +400 is its first __wrap_malloc return site *)
Lemma e2_fp : pi_fp F_check_no_overread = true.
Proof. vm_compute. reflexivity. Qed.
Lemma e2_site : In (cn_pc 400) (pi_ret_sites F_check_no_overread RT_malloc).
Proof. unfold cn_pc. rewrite (cni_base B IMG). vm_compute. tauto. Qed.

(* the chain at a cno call state, WITH its spine (Cno102A_Ro.v cn_chain's proof, which hides the case) *)
Lemma e2_chain : forall D fxk ly S Hp W regs mem md k,
  cn_pre (fx := fx) B ARcfx CTX0 D -> cn_base (fx := fx) B ARcfx D fxk ly S Hp W regs mem md k 0 ->
  exists ch1, achain ly (aview SEGS (w_H W) mem) (cn_S1 D) (cn_sp0 D) ch1 /\
    (spine ch1 = raZ (ci_regs D) :: spine (ci_ch D) \/ ch1 = []).
Proof.
intros D fxk ly S Hp W regs mem md k HPRE HB.
destruct (cn_entry_facts B ARcfx CTX0 D HPRE)
  as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _ & _ & Hra40 & Hch0 & _).
pose proof cn_stk_val as HSTKv.
destruct (cn_S1_facts D Hal16) as (HS1a & HS1b).
destruct HB as (_ & _ & HJ & _ & HSV & _).
apply e_J0 in HJ.
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_hi HJ) as F1. clear HJ.
assert (Etop : ly_top ly = ly_top (ci_ly D)) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
destruct (Z_lt_le_dec (cn_sp0 D) (ly_top (ci_ly D) - 16)) as [Hlt|Hge].
- exists ((cn_sp0 D, raZ (ci_regs D), s0Z (ci_regs D)) :: ci_ch D). split; [|left; reflexivity].
  apply (achain_ly_top (ci_ly D) ly); [exact Etop|].
  pose proof (proj1 (Forall_forall _ _) HSV (184, 1%bv) ltac:(ro_in)) as V1.
  pose proof (proj1 (Forall_forall _ _) HSV (176, 8%bv) ltac:(ro_in)) as V8.
  cbn [fst snd] in V1, V8.
  apply (achain_push (ci_ly D) (aview SEGS (w_H (ci_W D)) (ci_mem D)) (aview SEGS (w_H W) mem) (cn_sp0 D)
    (s0Z (ci_regs D)) (raZ (ci_regs D)) (ci_ch D) (cn_S1 D) Hch0).
  + lia.
  + intros a Ha. apply F1; lia.
  + replace (cn_sp0 D - 8) with (cn_sp0 D - 192 + 184) by lia. exact V1.
  + replace (cn_sp0 D - 16) with (cn_sp0 D - 192 + 176) by lia. exact V8.
  + exact Hra40.
  + lia.
  + lia.
  + exact Hlt.
  + lia.
- exists []. split; [|right; reflexivity]. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* the universe holds the trace of a cno allocator call at the return site ret *)
Lemma e2_univ : forall D regs ch1 rt ret,
  prh_univ_closure B CTX0 -> prh_ctx CTX0 F_check_no_overread (raZ (ci_regs D) :: spine (ci_ch D)) ->
  In ret (pi_ret_sites F_check_no_overread rt) -> raZ regs = ret ->
  (spine ch1 = raZ (ci_regs D) :: spine (ci_ch D) \/ ch1 = []) ->
  In (call_trace0 (prh_pc0 B rt) regs ch1) (as_universe B).
Proof.
intros D regs ch1 rt ret HU HCTX Hsite Hra [Hsp | ->]; rewrite e2_trace_eq, Hra.
- rewrite Hsp. eapply prh_univ_closure_site; [exact HU | exact HCTX | exact e2_fp | exact Hsite].
- cbn [spine map]. eapply prh_univ_closure_lit; [exact HU | exact Hsite].
Qed.
(* THE LIVE COUNTS at a cut, from cn_pre's position-free peaks (this tree's Cno102A_Base.v, THE ROOM POSITION) and the cut's cn_prog: the copies'
   events are a prefix of the text's event list (its head C3 is three HMal of the same size), and cnt at a prefix is
   at most the peak (PresetRun.pkR_prefix / pkR_app) *)
Lemma e2_firstn3 : forall (A : Type) (c : A) (l : list (Z * Z)), (length l <= 3)%nat ->
  map (fun _ => c) l = firstn (length l) [c; c; c].
Proof.
intros A c l H. destruct l as [|a [|b [|c0 [|d l]]]].
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- exfalso. cbn [length] in H. lia.
Qed.

Lemma e2_cevsl_prefix : forall D rs, (length (flat_map (cn_cblk D) rs) <= 3)%nat ->
  cn_cevsl D rs = firstn (length (flat_map (cn_cblk D) rs)) (ck_cno_evs ReaderRes.jr_strtod (ci_x D) None None None).
Proof.
intros D rs Hle. unfold cn_cevsl, ck_cno_evs. cbv zeta. unfold cn_size.
set (n := Z.of_nat (length (ci_x D))).
set (j := length (flat_map (cn_cblk D) rs)) in *.
assert (E3 : map (fun _ : Z * Z => PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD)) (flat_map (cn_cblk D) rs) =
  firstn j [PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD); PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD);
            PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD)]).
{ unfold j. exact (e2_firstn3 _ _ (flat_map (cn_cblk D) rs) Hle). }
rewrite E3.
assert (KEY : forall tl : list PresetReqAt.hev,
  firstn j ([PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD); PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD);
             PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD)] ++ tl) =
  firstn j [PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD); PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD);
            PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD)]).
{ intros tl. rewrite firstn_app. replace (j - length [PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD);
    PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD); PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD)])%nat with 0%nat
    by (cbn [length]; lia).
  cbn [firstn]. rewrite app_nil_r. reflexivity. }
destruct (PresetRun.ranout ReaderRes.jr_strtod (ci_x D) None); [symmetry; apply KEY|].
destruct (PresetRun.ranout ReaderRes.jr_strtod (ci_x D) None); symmetry; apply KEY.
Qed.

Lemma e2_counts_at : forall D ly S Hp W mem rs own,
  cn_pre (fx := fx) B ARcfx CTX0 D -> cn_early B D ly S Hp W mem rs own ->
  (length (flat_map (cn_cblk D) rs) <= 3)%nat ->
  YGcfRoomLive.rl_sec_ok (PresetLiveSec.LSEC + PresetGate.DRV) S /\
  YGcfRoomLive.rl_b24_ok (PresetLiveSec.L24 + PresetGate.DRV + 1) S.
Proof.
intros D ly S Hp W mem rs own HPRE HE Hle.
assert (EL : PresetLiveSec.LSEC + PresetGate.DRV = PresetLiveBounds.LSEC + PresetLiveBounds.DRV)
  by (vm_compute; reflexivity).
assert (E24 : PresetLiveSec.L24 + PresetGate.DRV = PresetLiveBounds.L24 + PresetLiveBounds.DRV)
  by (vm_compute; reflexivity).
assert (ES : PresetLiveSec.sec_req = YGcfRoomLive.rl_sec_req) by reflexivity.
assert (EC : PresetRoom.in_cls 24 = PresetRoom.in_cls YG00.kBatchClass) by reflexivity.
pose proof (cn_pre_pksec B ARcfx CTX0 D HPRE) as HPKS. pose proof (cn_pre_pk24 B ARcfx CTX0 D HPRE) as HPK24.
destruct HE as (_ & _ & _ & _ & _ & (HPerm & _) & _).
rewrite (e2_cevsl_prefix D rs Hle) in HPerm.
assert (C1 : (PresetReqAt.cnt YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) <=
  PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (ci_S D)))
    (ck_cno_evs ReaderRes.jr_strtod (ci_x D) None None None))%nat).
{ rewrite (PresetReqAt.cnt_perm _ _ _ HPerm). apply PresetRun.pkR_prefix. }
assert (C2 : (PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) <=
  PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (ci_S D)))
    (ck_cno_evs ReaderRes.jr_strtod (ci_x D) None None None))%nat).
{ rewrite (PresetReqAt.cnt_perm _ _ _ HPerm). apply PresetRun.pkR_prefix. }
split.
- apply CfRoomLivePreset.preset_rl_sec_ok. rewrite ?ES, ?EL. lia.
- apply CfRoomLivePreset.preset_rl_b24_ok. apply CfRoomLivePreset.preset_ccnt24. rewrite ?EC, ?E24. lia.
Qed.

(* CNO-COPY's refused arm, DEAD at a consumer run (cn_cdead): a copy's __wrap_malloc returned NULL on a granted
   path at the cut's own state S, after the granted copies the cut's cn_prog names (fewer than three). The run position
   after them is a position of S (cn_prog), the refused copy is the next event of ck_cno_copies, a consumer allocation
   by the run hypothesis, and PRH_Refute.prh_refute_window refutes the refusal there. *)
Lemma e2_cdead : forall D rs S, cn_prog D (cn_cevsl D rs) S -> (length (flat_map (cn_cblk D) rs) < 3)%nat ->
  Wf_cf (as_universe B) S -> PRH_Refute.prh_granted_null S -> cn_cdead D.
Proof.
intros D rs S HPr Hm W N. destruct HPr as (_ & HP). intros sm x0 os i H0 hist Hpos Hrun Hcons.
unfold cn_cevsl in HP.
set (h := PresetReqAt.HMal (cn_size D + PresetReqAt.FUZZ_PAD)) in HP.
assert (EC : ck_cno_copies (ci_x D) = [h; h; h]) by reflexivity.
rewrite EC in Hrun, Hcons.
revert HP Hm.
destruct (flat_map (cn_cblk D) rs) as [|a [|b [|c l]]]; cbn [map length]; intros HP Hm; [| | | lia].
- destruct (HP sm x0 os i H0 hist Hpos ltac:(unfold PRH_Base.prh_run_at; reflexivity)) as (hist' & Hpos').
  exact (PRH_Refute.prh_refute_window _ sm x0 os i [h; h; h] 0 h H0 hist' S Hrun Hcons eq_refl eq_refl Hpos' W N).
- destruct (HP sm x0 os i H0 hist Hpos (proj1 (proj1 (PRH_Base.prh_run_at_app_iff sm x0 os i [h] [h; h]) Hrun)))
    as (hist' & Hpos').
  exact (PRH_Refute.prh_refute_window _ sm x0 os i [h; h; h] 1 h H0 hist' S Hrun Hcons eq_refl eq_refl Hpos' W N).
- destruct (HP sm x0 os i H0 hist Hpos (proj1 (proj1 (PRH_Base.prh_run_at_app_iff sm x0 os i [h; h] [h]) Hrun)))
    as (hist' & Hpos').
  exact (PRH_Refute.prh_refute_window _ sm x0 os i [h; h; h] 2 h H0 hist' S Hrun Hcons eq_refl eq_refl Hpos' W N).
Qed.

Lemma e2_addi : forall a i, 0 <= a < 2 ^ 64 -> 0 <= a + i < 2 ^ 64 -> v_addi (w64 a) i = w64 (a + i).
Proof. intros a i Ha Hai. unfold v_addi, w64. rewrite unsigned_lit_small by lia. reflexivity. Qed.
Lemma e2_hpeak_nonneg : forall tr, 0 <= hpeakR tr.
Proof. intros [|e r]; cbn [hpeakR]; lia. Qed.
Lemma e2_live_pj_nonneg : forall x, 0 <= PRH_FnPj.LIVE_pj_parse x.
Proof.
intros x. unfold PRH_FnPj.LIVE_pj_parse. pose proof (e2_hpeak_nonneg (PRH_FnPj.prhPj_ptrace x)).
pose proof cf_head_nonneg. nia.
Qed.

(* ---- THE MEMCPY SOURCE's SHADOW at a later state. cno's data home is prhReader_home: kept_at (a Lam block, a
   registered global, an image string) or a live block of the entry state outside Hp. Each arm gives the shadow from
   an ARx law. COPIED and merged, at THIS file's abstract PA, from lib/A/Prog/FuzzStrdup.v (blob 2e9d1f0ab25c)
   :113-138 sd_hull_sub / sd_hull_img and :428-482 sd_src_shadow, and lib/A/Prog/Caw102A_WA2.v (blob 0b1a30f1b8d1)
   :270-294 wa2_sh_blk; those files fix PA := PI_prog_A, this walk is parametric over PA. ---- *)
Lemma e2_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma e2_hull_img : forall a n s, 0 < n -> pa_lo + 64 <= a -> a + n + 64 <= pa_hi ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ pa_lo <= 8 * (s - SHADOW_OFF) < pa_hi.
Proof.
intros a n s Hn Hlo Hhi Hs. unfold shadow_addr in *.
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.
Lemma e2_req_ge : forall n, 0 <= n -> n <= req_size n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

(* no head of Hp lies inside a live block whose base is not a head (Caw102A_WA2.v wa2_hp_apart, at the new ledger
   arity): the heads are the Lam bases, and two live blocks are disjoint *)
Lemma e2_hp_apart : forall lyc Sc Hpc Wc memc mdc Lam pk cnt fl rn mo ow b m,
  ARcfx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lam pk cnt fl rn mo ow ->
  In (b, m) (ablocks B lyc Sc) -> ~ In b Hpc ->
  forall h, In h Hpc -> ~ (b <= h < b + req_size m).
Proof.
intros lyc Sc Hpc Wc memc mdc Lam pk cnt fl rn mo ow b m HAR HLG Hin Hbn h Hh Hr.
pose proof (prh_ledger_heads B lyc Sc Hpc Wc memc Lam pk cnt fl rn mo ow HLG) as HP.
apply (Permutation_in _ HP) in Hh. apply in_map_iff in Hh as ([a k] & Eh & Hak). cbn [fst] in Eh.
destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lam pk cnt fl rn a k mo ow HLG Hak) as (Hk0 & Hblk & Hinp & _ & _).
rewrite Eh in Hblk, Hinp.
pose proof cf_head_nonneg as CH0.
assert (Hne : (b, m) <> (h, k + cf_head)) by (intros E; injection E as -> _; exact (Hbn Hinp)).
pose proof (sep_blocks_x SEGS B ARcfx LAWS lyc Sc Hpc Wc memc mdc b m h (k + cf_head) HAR Hin Hblk Hne) as Hd.
assert (Hk1 : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma e2_src_shadow : forall lyc Sc Hpc Wc memc mdc Lam pk cnt fl rn mo ow s n,
  ARcfx lyc Sc Hpc Wc memc mdc -> prh_ledger B lyc Sc Hpc Wc memc Lam pk cnt fl rn mo ow -> 0 < n ->
  (kept_at B Lam s n \/
   (exists b m, In (b, m) (ablocks B lyc Sc) /\ ~ In b Hpc /\ b <= s /\ s + n <= b + m)) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF s n /\ shadow_hull_vis (aview SEGS (w_H Wc) memc) s n.
Proof.
intros lyc Sc Hpc Wc memc mdc Lam pk cnt fl rn mo ow s n HAR HLG Hn
  [[(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & _) | (Hlo & Hhi & Hro)]] | (b & m & Hin & Hbn & Hb & Hm)].
- (* a Lam head block: the user range past the hidden head (alx_hshadow) *)
  destruct (prh_ledger_hblock B lyc Sc Hpc Wc memc Lam pk cnt fl rn b m mo ow HLG Hin) as (Hm0 & Hab & Hhp & _ & _).
  pose proof cf_head_nonneg as CH0.
  destruct (alx_hshadow SEGS B ARcfx LAWS lyc Sc Hpc Wc memc mdc (b - cf_head) (m + cf_head) HAR Hab Hhp) as [Hbs Hhu].
  assert (Hge : 0 <= m + cf_head) by lia.
  pose proof (e2_req_ge (m + cf_head) Hge) as Hrq.
  replace (b - cf_head + cf_head) with b in Hbs, Hhu by lia.
  split.
  + eapply block_shadow_range; [exact Hbs | lia | lia].
  + apply (e2_hull_sub _ b (req_size (m + cf_head) - cf_head) s n); [apply Hhu; lia | lia | lia | lia].
- (* a registered global: its shadow is zero in every state, its hull is image shadow *)
  destruct Hzs as (q & m & Hinz & Hq & Hqm).
  pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ (proj1 (proj1 HAR)))) (q, m) Hinz)
    as (Z1 & Z2 & Z3 & Z4 & Z5). cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
  pose proof (alx_zshadow SEGS B ARcfx LAWS lyc Sc Hpc Wc memc mdc (q, m) HAR
    ltac:(unfold zero_shadow_ranges; right; exact Hinz)) as Hz. cbn [fst snd] in Hz.
  split.
  + apply (range_addressable_sub (aview SEGS (w_H Wc) memc) SHADOW_OFF q m s n); [|exact Hq|exact Hqm].
    exact (zero_shadow_range (aview SEGS (w_H Wc) memc) SHADOW_OFF q m Z3 Z4 Hz).
  + intros s0 Hs. destruct (e2_hull_img s n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
    exact (IMGSH lyc Sc Hpc Wc memc mdc _ (proj1 HAR) Hr).
- (* an image string (route (a)): per granule a zero-shadow granule or a const-shadow cell kept by alx_const_cells *)
  split.
  + intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzg | (v & Hcell & Hv)]).
    * destruct Hzg as (q & m & Hinz & Hq & Hqm).
      pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ (proj1 (proj1 HAR)))) (q, m) Hinz)
        as (Z1 & Z2 & Z3 & Z4 & Z5). cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
      pose proof (alx_zshadow SEGS B ARcfx LAWS lyc Sc Hpc Wc memc mdc (q, m) HAR
        ltac:(unfold zero_shadow_ranges; right; exact Hinz)) as Hz. cbn [fst snd] in Hz.
      pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
      exact (zero_shadow_range (aview SEGS (w_H Wc) memc) SHADOW_OFF q m Z3 Z4 Hz x ltac:(lia)).
    * pose proof (proj1 (Forall_forall _ _) (alx_const_cells SEGS B ARcfx LAWS lyc Sc Hpc Wc memc mdc HAR) _ (Hcell lyc))
        as Hc.
      unfold cell_holds, z1, c1 in Hc. cbn [c_at c_w c_val aeval] in Hc.
      specialize (Hc 0%nat ltac:(lia)). rewrite Z.add_0_r in Hc.
      pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
      assert (Hb : YG0f.le_byte v 1 0 = v).
      { unfold YG0f.le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity.
        replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
        change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
      exists v. split; [|exact Hv].
      change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). rewrite Hc, Hb. reflexivity.
  + intros s0 Hs. destruct (e2_hull_img s n s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
    exact (IMGSH lyc Sc Hpc Wc memc mdc _ (proj1 HAR) Hr).
- (* a live block of the state, outside Hp: the plain block shadow (alx_shadow) *)
  destruct (alx_shadow SEGS B ARcfx LAWS lyc Sc Hpc Wc memc mdc b m HAR Hin
    (e2_hp_apart lyc Sc Hpc Wc memc mdc Lam pk cnt fl rn mo ow b m HAR HLG Hin Hbn)) as [Hbs Hhu].
  assert (Hm0 : 0 <= m) by (destruct Hbs as (_ & Hmm & _); unfold req_size in Hmm; destruct (Z.eqb_spec m 0); lia).
  pose proof (e2_req_ge m Hm0) as Hrq.
  split.
  + eapply block_shadow_range; [exact Hbs | lia | lia].
  + apply (e2_hull_sub _ b (req_size m) s n Hhu); lia.
Qed.

(* the own byte is a program static, visible and writable in every memory (Cno102A_R5.v r5_own_pst / r5_own_wr,
   blob f2aa165bbe8a :574-578, :989-1010, copied) *)
Lemma e2_own_pst : Exists (in_zr (VAL (A_OBJ 13))) prh_pst.
Proof.
rewrite (cni_own B IMG). unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd.
unfold in_zr. cbn [fst snd]. change (Z.of_nat pi_gz_own_ran_out) with 1. lia.
Qed.
Lemma e2_own_wr : forall (W : world SEGS) (m : word -> option byte),
  w_H W (Z_to_bv 64 (VAL (A_OBJ 13))) = false /\ writable_at SEGS (mrestrict (w_H W) m) (VAL (A_OBJ 13)).
Proof.
intros W m. set (x := Z_to_bv 64 (VAL (A_OBJ 13))).
pose proof (cni_pst_seg B IMG _ e2_own_pst) as Hseg. fold x in Hseg.
unfold YK11.seg_rom, memory_read in Hseg.
destruct (find_segment SEGS (bv_unsigned x) (Z.of_N 1)) as [sg|] eqn:Hf; [|exfalso; apply Hseg; reflexivity].
change (Z.of_N 1) with 1 in Hf.
assert (Hh : w_H W x = false).
{ destruct (w_H W x) eqn:Eh; [|reflexivity]. pose proof (w_Hoff W x Eh) as Hn. rewrite Hn in Hf. discriminate. }
split; [exact Hh|].
unfold writable_at, wview, mrestrict. fold x. rewrite Hh.
destruct (m x) as [b|]; [discriminate|]. rewrite Hf.
destruct (seg_writable sg) eqn:Ew.
- destruct (seg_readable sg); [|exfalso; apply Hseg; reflexivity].
  change (N.to_nat 1) with 1%nat in Hseg. cbn [segment_read_bytes] in Hseg.
  destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned x - Z.of_N (seg_base sg)))) as [b|] eqn:Eb;
    [discriminate | exfalso; apply Hseg; reflexivity].
- exfalso. apply (cni_pst_rw B IMG _ e2_own_pst). left. destruct (find_segment_hit _ _ _ _ Hf) as (Hin & Hlo & Hhi).
  exists sg. split; [exact Hin|]. split; [exact Ew|].
  pose proof (@pa_val_range _ _ PA (A_OBJ 13)). unfold x in Hlo, Hhi. rewrite unsigned_lit_small in Hlo, Hhi by lia. lia.
Qed.

(* ---- THE LEDGER AT A LATER MEMORY WITH A NEW OWN BYTE (Cno102A_R5.v r5_exit's ledger step, blob f2aa165bbe8a
   :916-962, restated as a lemma): the six other PST cells and Lam's heads are kept, the own cell holds own'.
   The cells' addresses are never typed here: each disjointness is decided by vm_compute after cni_own turns
   VAL (A_OBJ 13) into pi_g_own_ran_out. ---- *)
Lemma e2_cell_pst : forall a w q, (forall kk, (kk < w)%nat -> Exists (in_zr (a + Z.of_nat kk)) prh_pst) ->
  0 <= q < Z.of_nat w -> Exists (in_zr (a + q)) prh_pst.
Proof.
intros a w q H Hq. replace q with (Z.of_nat (Z.to_nat q)) by lia. exact (H (Z.to_nat q) ltac:(lia)).
Qed.

Lemma e2_glob_own : forall (W : world SEGS) mem (W' : world SEGS) mem' live peak cnt fail ran most own own',
  prh_glob W mem live peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) prh_pst -> a <> VAL (A_OBJ 13) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  prh_own W' mem' own' ->
  prh_glob W' mem' live peak cnt fail ran most own'.
Proof.
intros W mem W' mem' live peak cnt fail ran most own own' (H1 & H2 & H3 & H4 & H5 & (H6 & M) & _ & R) KI HO.
unfold prh_glob. split; [|split; [|split; [|split; [|split; [|split; [|split; [exact HO | exact R]]]]]]].
- apply (val_mem_kept SEGS (w_H W) (w_H W') mem mem'); [|exact H1].
  intros q Hq. apply KI; [exact (e2_cell_pst _ _ q prh_pst_live Hq)|].
  change (Z.of_nat pi_gz_live) with 8 in Hq.
  rewrite (cni_own B IMG). change pi_g_live with 6149472. change pi_g_own_ran_out with 6149440. lia.
- apply (val_mem_kept SEGS (w_H W) (w_H W') mem mem'); [|exact H2].
  intros q Hq. apply KI; [exact (e2_cell_pst _ _ q prh_pst_peak Hq)|].
  change (Z.of_nat pi_gz_peak) with 8 in Hq.
  rewrite (cni_own B IMG). change pi_g_peak with 6149504. change pi_g_own_ran_out with 6149440. lia.
- apply (val_mem_kept SEGS (w_H W) (w_H W') mem mem'); [|exact H3].
  intros q Hq. apply KI; [exact (e2_cell_pst _ _ q prh_pst_count Hq)|].
  change (Z.of_nat pi_gz_count) with 8 in Hq.
  rewrite (cni_own B IMG). change pi_g_count with 6149536. change pi_g_own_ran_out with 6149440. lia.
- apply (val_mem_kept SEGS (w_H W) (w_H W') mem mem'); [|exact H4].
  intros q Hq. apply KI; [exact (e2_cell_pst _ _ q prh_pst_fail Hq)|].
  change (Z.of_nat pi_gz_fail) with 8 in Hq.
  rewrite (cni_own B IMG). change pi_g_fail with 681408. change pi_g_own_ran_out with 6149440. lia.
- apply (val_mem_kept SEGS (w_H W) (w_H W') mem mem'); [|exact H5].
  intros q Hq. apply KI; [exact (e2_cell_pst _ _ q prh_pst_ran Hq)|].
  change (Z.of_nat pi_gz_ran_out) with 1 in Hq.
  rewrite (cni_own B IMG). change pi_g_ran_out with 6149568. change pi_g_own_ran_out with 6149440. lia.
- split; [|exact M]. apply (val_mem_kept SEGS (w_H W) (w_H W') mem mem'); [|exact H6].
  intros q Hq. apply KI; [exact (e2_cell_pst _ _ q prh_pst_most Hq)|].
  change (Z.of_nat pi_gz_most) with 8 in Hq.
  rewrite (cni_own B IMG). change pi_g_most with 681440. change pi_g_own_ran_out with 6149440. lia.
Qed.

Lemma e2_ledger_own : forall ly S Hp W mem ly' S' Hp' (W' : world SEGS) mem' Lam peak cnt fail ran most own own',
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) prh_pst -> a <> VAL (A_OBJ 13) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  prh_own W' mem' own' ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 ->
     mbyte SEGS (mrestrict (w_H W') mem') (a - cf_head + i) = mbyte SEGS (mrestrict (w_H W) mem) (a - cf_head + i)) ->
  (forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly S) ->
     In (a - cf_head, k + cf_head) (ablocks B ly' S')) ->
  Permutation Hp' Hp ->
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own'.
Proof.
intros ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran most own own' HL KI HO Hh Hb Hpp.
apply prh_ledger_iff in HL as [HG HB]. apply prh_ledger_iff. split.
- exact (e2_glob_own W mem W' mem' _ _ _ _ _ _ _ own' HG KI HO).
- exact (prh_lblocks_kept B ly S Hp W mem ly' S' Hp' W' mem' Lam HB Hh Hb Hpp).
Qed.

(* ---- THE GRANTED ARM's kit. A register `add` hand step (Cno102A_Ro.v cn_hs_addi0's form, over YK11.step_add). ---- *)
Definition e2_is_add (off : Z) (rd rs1 rs2 : bv 5) : bool :=
  match cn_dec off with
  | Some (Op ALU_ADD rd' rs1' rs2', sz) => (sz =? 4) && bv_eqb rd' rd && bv_eqb rs1' rs1 && bv_eqb rs2' rs2
  | _ => false end.
Lemma e2_hs_add : forall (W : world SEGS) fxk regs mem md Q off off' rd rs1 rs2,
  e2_is_add off rd rs1 rs2 = true -> bv_eqb rd 0%bv = false -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off') (regupd regs rd (v_add (getr regs rs1) (getr regs rs2))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' rd rs1 rs2 H Hrd Ho -> HK.
unfold e2_is_add, cn_dec in H.
destruct (plookup A_prog_tpi_cno (CN_OFF + off)) as [e|] eqn:Hpl; [|discriminate H].
destruct e; try (cbv beta iota in H; discriminate H).
lazymatch type of H with context [decode_any ?x] => destruct (decode_any x) as [[ii sz]|] eqn:Hdec; [|discriminate H] end.
destruct ii; try (cbv beta iota in H; discriminate H).
lazymatch type of Hdec with decode_any _ = Some (Op ?o _ _ _, _) => destruct o; try (cbv beta iota in H; discriminate H) end.
cbv beta iota in H.
repeat match goal with
  | H' : _ && _ = true |- _ => apply andb_prop in H' as [? ?]
  | H' : bv_eqb _ _ = true |- _ => apply ro_bv_eqb_eq in H'
  | H' : (_ =? _) = true |- _ => apply Z.eqb_eq in H'
  end; subst.
apply (cn_step W fxk regs mem md (regupd regs rd (v_add (getr regs rs1) (getr regs rs2))) off (off + 4) Q
  ltac:(lia) ltac:(lia)); [|exact HK].
rewrite (@step_add fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd rs1 rs2
  (@pa_fetch_pw _ _ PL_cno_A PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
rewrite Hrd, (cn_pc4 off ltac:(lia)). reflexivity.
Qed.
Lemma e2_vadd : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a + b < 2 ^ 64 -> v_add (w64 a) (w64 b) = w64 (a + b).
Proof. intros a b Ha Hb Hab. unfold v_add, w64. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

(* the journal from the entry frees nothing (FP = []): every entry block of non-negative size is still live *)
Lemma e2_blocks_in : forall D ly' S' Hp' W' mem' md' k' p n, cn_J B ARcfx D ly' S' Hp' W' mem' md' k' 0 ->
  In (p, n) (ablocks B (ci_ly D) (ci_S D)) -> 0 <= n -> In (p, n) (ablocks B ly' S').
Proof.
intros D ly' S' Hp' W' mem' md' k' p n HJ Hin Hn. apply e_J0 in HJ.
pose proof (ajx_gone HJ) as F5.
destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B ly' S')) as [H|H];
  [exact H|].
exfalso. assert (Hr : 0 < req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
exact (inFP_nil _ (F5 p n 0 Hin H ltac:(lia))).
Qed.

(* the source's bytes at a later state are the entry's: its home (prhReader_home) is a Lam block or a live entry block
   (the journal's block clause; nothing is freed) or read-only image bytes that the runtime does not own (the image
   clause; the program statics are writable, cni_pst_rw). FuzzStrdup.v (blob 2e9d1f0ab25c) :400-419 sd_src_kept's
   route, with cno's fourth arm. *)
Lemma e2_src_kept : forall D ly' S' Hp' W' mem' md' k' s n,
  cn_J B ARcfx D ly' S' Hp' W' mem' md' k' 0 ->
  prh_ledger B (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D)
    (ci_most D) 0 ->
  PRH_FnReader.prhReader_home B (ci_ly D) (ci_S D) (ci_Hp D) (ci_Lam D) s n ->
  forall a, s <= a < s + n -> aview SEGS (w_H W') mem' a = aview SEGS (w_H (ci_W D)) (ci_mem D) a.
Proof.
intros D ly' S' Hp' W' mem' md' k' s n HJ HL HH a Ha.
pose proof HJ as HJc. apply e_J0 in HJc.
pose proof (ajx_blk HJc) as F2. pose proof (ajx_img HJc) as F3.
pose proof cf_head_nonneg as CH0.
assert (RO : in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H (ci_W D)) (ci_mem D) a).
{ intros Hr Hno Her. apply F3; [| exact Hno | exact Her | exact (fun Hx => cni_pst_rw B IMG a Hx Hr) |].
  - destruct Hr as [(sg & Hsg & _ & Hsa) | Hr]; [exists sg; split; [exact Hsg | exact Hsa] | exact (@pa_relro_img _ _ PA a Hr)].
  - apply fp_spares_closed. exact sink_closed_nil. }
destruct HH as [[(b & m & Hin & Hb & Hm) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hin & _ & Hb & Hm)].
- destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ b m _ _ HL Hin) as (Hm0 & Hab & _).
  assert (Hmc : 0 <= m + cf_head) by lia.
  pose proof (e2_req_ge (m + cf_head) Hmc) as Hge.
  replace a with (b - cf_head + (a - (b - cf_head))) by lia.
  apply (F2 (b - cf_head) (m + cf_head) (a - (b - cf_head)) Hab
    (e2_blocks_in D ly' S' Hp' W' mem' md' k' _ _ HJ Hab Hmc)); [lia | apply inFP_nil].
- destruct (Hro a Ha) as (Hr & Hno & Her). exact (RO Hr Hno Her).
- destruct (Hro a Ha) as (Hr & Hno & Her & _). exact (RO Hr Hno Her).
- assert (Hm0 : 0 <= m) by lia. pose proof (e2_req_ge m Hm0) as Hge.
  replace a with (b + (a - b)) by lia.
  apply (F2 b m (a - b) Hin (e2_blocks_in D ly' S' Hp' W' mem' md' k' _ _ HJ Hin Hm0)); [lia | apply inFP_nil].
Qed.

(* the ledger across a write confined to one live block outside Hp (below the ceiling): the program statics are image
   bytes, which no block holds (alx_client_img); Lam's heads lie in the other blocks, apart (sep_blocks_x) *)
Lemma e2_ledger_blk : forall ly S Hp W m md m' Lam pk cnt fl rn mo ow r n,
  ARcfx ly S Hp W m md -> prh_ledger B ly S Hp W m Lam pk cnt fl rn mo ow ->
  In (r, n) (ablocks B ly S) -> ~ In r Hp ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> ~ (r <= a < r + req_size n) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  prh_ledger B ly S Hp W m' Lam pk cnt fl rn mo ow.
Proof.
intros ly S Hp W m md m' Lam pk cnt fl rn mo ow r n HAR HL Hin Hrn K.
pose proof alloc_ceiling_val as [AC _].
assert (Hbr : forall a, r <= a < r + req_size n -> ~ in_img SEGS a).
{ intros a Ha. exact (proj2 (alx_client_img SEGS B ARcfx LAWS ly S Hp W m md a HAR
    (or_introl (ex_intro _ r (ex_intro _ n (conj Hin Ha)))))). }
assert (KP : forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a).
{ intros a Hp0. pose proof (proj1 (cni_pst_ok B IMG a Hp0)) as Hi.
  pose proof (@pa_segs_low _ _ PA _ Hi) as Hlow. unfold kLowMemEnd in Hlow.
  apply K; [lia | intros Hr; exact (Hbr a Hr Hi)]. }
pose proof HL as HLc. apply prh_ledger_iff in HLc as [HG _].
destruct HG as (_ & _ & _ & _ & _ & _ & HO & _).
apply (e2_ledger_own ly S Hp W m ly S Hp W m' Lam pk cnt fl rn mo ow ow HL).
- intros a Hp0 _. exact (KP a Hp0).
- destruct HO as (HOv & HOr). split; [|exact HOr].
  apply (val_mem_kept SEGS (w_H W) (w_H W) m m'); [|exact HOv].
  intros q Hq. apply KP. exact (e2_cell_pst _ _ q prh_pst_own Hq).
- intros a k i Hak Hi. apply prh_mbyte_of_aview.
  destruct (prh_ledger_hblock B ly S Hp W m Lam pk cnt fl rn a k mo ow HL Hak) as (Hk0 & Hblk & Hinp & _).
  pose proof cf_head_nonneg. unfold prh_head_wide in HW.
  assert (Hne : (a - cf_head, k + cf_head) <> (r, n)).
  { intros E. injection E as E1 _. apply Hrn. rewrite <- E1. exact Hinp. }
  pose proof (sep_blocks_x SEGS B ARcfx LAWS ly S Hp W m md _ _ _ _ HAR Hblk Hin Hne) as Hd.
  destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W m md _ _ HAR Hblk) as (_ & Hb4096 & Hbtop & _).
  assert (Hkc : 0 <= k + cf_head) by lia. pose proof (e2_req_ge _ Hkc) as Hge.
  apply K; [lia | unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia].
- intros a k _ Hb. exact Hb.
- apply Permutation_refl.
Qed.

Lemma e2_mbyte_of_aview2 : forall (H H' : word -> bool) (m m' : word -> option byte) (a a' : Z),
  aview SEGS H' m' a' = aview SEGS H m a -> mbyte SEGS (mrestrict H' m') a' = mbyte SEGS (mrestrict H m) a.
Proof.
intros H H' m m' a a'. unfold aview.
destruct (mbyte SEGS (mrestrict H' m') a') as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|];
cbn [option_map]; intros E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma e2_garr8_some : forall (H : word -> bool) (m : word -> option byte) p l a, garr8 SEGS (mrestrict H m) p l ->
  p <= a < p + Z.of_nat (length l) -> aview SEGS H m a <> None.
Proof.
intros H m p l a HG Ha. destruct (HG (Z.to_nat (a - p)) ltac:(lia)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)). replace (p + Z.of_nat (Z.to_nat (a - p)) + Z.of_nat 0) with a in Hv by lia.
unfold aview. rewrite Hv. discriminate.
Qed.

(* ======== CA2 ======== *)
Theorem cn_CA2 : @cn_seg_CA2 fx rc ci CfParams_preset prh_room_live_a8 SK PA B ARcfx CTX0.
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k HPRE HAT HPM.
destruct HAT as (HB & HR & HSL & HE).
(* the entry cut's LAST conjunct (the hull stages): the stage budget, kept apart so HE is cn_early as before *)
destruct HE as [HE HHULL].
pose proof (cn_pre_fpre B ARcfx CTX0 D HPRE) as HFPRE. pose proof (cn_pre_mn B ARcfx CTX0 D HPRE) as HMN.
pose proof (cn_pre_univ B ARcfx CTX0 D HPRE) as HUNIV. pose proof (cn_pre_ctx B ARcfx CTX0 D HPRE) as HCTX.
pose proof (cn_pre_r10 B ARcfx CTX0 D HPRE) as Ha0. pose proof (cn_pre_r11 B ARcfx CTX0 D HPRE) as Ha1.
pose proof (cn_pre_size B ARcfx CTX0 D HPRE) as Hsz. pose proof (cn_pre_src B ARcfx CTX0 D HPRE) as HSRC.
pose proof (cn_pre_home B ARcfx CTX0 D HPRE) as HHOME. pose proof (cn_pre_ledger B ARcfx CTX0 D HPRE) as HLED.
pose proof (cn_pre_cnt B ARcfx CTX0 D HPRE) as HCNT. pose proof (cn_pre_ran B ARcfx CTX0 D HPRE) as HRAN.
pose proof (cn_pre_most B ARcfx CTX0 D HPRE) as HRQ. pose proof (cn_pre_live B ARcfx CTX0 D HPRE) as HLIVE.
pose proof (cn_pre_max16 B ARcfx CTX0 D HPRE) as HMAX1. pose proof (cn_pre_maxpj B ARcfx CTX0 D HPRE) as HMAX2.
pose proof (cn_pre_frames B ARcfx CTX0 D HPRE) as HFRS. pose proof (cn_pre_room B ARcfx CTX0 D HPRE) as HROOM.
pose proof (cn_pre_frm0 B ARcfx CTX0 D HPRE) as HFRM. pose proof (cn_pre_wild B ARcfx CTX0 D HPRE) as HWILD.
pose proof (cn_pre_pksec B ARcfx CTX0 D HPRE) as HPKS. pose proof (cn_pre_pk24 B ARcfx CTX0 D HPRE) as HPK24.
destruct (cn_entry_facts B ARcfx CTX0 D HPRE)
  as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & Hgp0 & Htp0 & Hra40 & Hch0 & HAR0).
pose proof (e5_S1 D Hal16) as [HS1mod HS1b].
pose proof cn_stk_val as HSTK.
pose proof HB as (Hfz & Hfk & HJ & HFR & HSV & G3 & G4 & HROD).
pose proof HFR as (Hfrs & Hnin & Hflag & Hfpr & Hshp).
pose proof HJ as HJ'. apply e_J0 in HJ'.
pose proof (ajx_ar HJ') as HAR. pose proof (ajx_ly HJ') as Hly. pose proof (ajx_pres HJ') as Hpres.
pose proof (ajx_qt HJ') as HQT.
pose proof HE as HEc. destruct HEc as (HHp & HLG & _ & HPERM & HROOMc & HRP & HBUD & _ & Hown & _).
assert (RG : forall r v, In (r, v) (cn_core D ++ [(20%bv, cn_size D); (23%bv, ci_data D)]) -> getr regs r = w64 v)
  by (intros r v Hin'; exact (proj1 (Forall_forall _ _) HR (r, v) Hin')).
pose proof (cni_base B IMG) as HBASE. pose proof cn_off_val as HOFF.
pose proof alloc_ceiling_val as [AC _]. pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
(* +388 addi s3, s4, 16; +392 mv a0, s3; +396 jal __wrap_malloc *)
apply (cn_hs_addi W fxk regs mem md _ 388 392 19%bv 20%bv 16); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X1.
apply (cn_hs_addi W fxk _ mem _ _ 392 396 10%bv 19%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X2.
apply (cn_hs_call W fxk _ mem _ _ 396 400 AS___wrap_malloc); [vm_compute; reflexivity | lia | reflexivity |].
intros X3.
lazymatch goal with |- SRr _ _ (@cn_cfg _ _ _ ?rg _ ?mo) _ => set (regsT := rg); set (mdT := mo) end.
(* the registers at the call *)
assert (RT : forall r v, In (r, v) (cn_core D ++ [(20%bv, cn_size D); (23%bv, ci_data D)]) ->
  r <> 1%bv -> r <> 10%bv -> r <> 19%bv -> getr regsT r = w64 v).
{ intros r v Hin' H1 H10 H19. unfold regsT. rewrite !getr_other by (intros E; subst; contradiction).
  exact (RG r v Hin'). }
assert (T10 : getr regsT 10%bv = w64 (cn_size D + 16)).
{ unfold regsT. ro_getr. rewrite (RG 20%bv (cn_size D) ltac:(ro_in)).
  rewrite e2_addi by (unfold cn_size in *; lia). rewrite e2_addi by (unfold cn_size in *; lia). f_equal. lia. }
assert (T19 : getr regsT 19%bv = w64 (cn_size D + 16)).
{ unfold regsT. ro_getr. rewrite (RG 20%bv (cn_size D) ltac:(ro_in)).
  rewrite e2_addi by (unfold cn_size in *; lia). reflexivity. }
assert (T2 : getr regsT 2%bv = w64 (cn_S1 D)) by (apply RT; [ro_in | discriminate | discriminate | discriminate]).
assert (T8 : getr regsT 8%bv = w64 (cn_sp0 D)) by (apply RT; [ro_in | discriminate | discriminate | discriminate]).
assert (T1 : getr regsT 1%bv = w64 (cn_pc 400)) by (unfold regsT; ro_getr; reflexivity).
assert (T3 : getr regsT 3%bv = getr (ci_regs D) 3%bv) by (unfold regsT; ro_getr; exact G3).
assert (T4 : getr regsT 4%bv = getr (ci_regs D) 4%bv) by (unfold regsT; ro_getr; exact G4).
assert (HSPT : spZ regsT = cn_S1 D) by (unfold spZ; rewrite T2; unfold w64; apply unsigned_lit_small; unfold cn_sp0 in *; lia).
assert (Hpc400 : 4096 <= cn_pc 400 < 2 ^ 40).
{ unfold cn_pc. rewrite HBASE, HOFF. unfold A_prog_base. lia. }
assert (HRAT : raZ regsT = cn_pc 400) by (unfold raZ; rewrite T1; unfold w64; apply unsigned_lit_small; lia).
(* the journal at the call *)
pose proof (cn_base_mat B ARcfx LAWS D fxk ly S Hp W regs regs mem md k 0 X1 HB eq_refl eq_refl) as HB1.
pose proof (cn_base_mat B ARcfx LAWS D fxk ly S Hp W regs (regupd regs 19%bv (v_addi (getr regs 20%bv) 16)) mem _ k 0 X2 HB1
  ltac:(ro_getr; reflexivity) ltac:(ro_getr; reflexivity)) as HB2.
pose proof (cn_base_mat B ARcfx LAWS D fxk ly S Hp W _ regsT mem _ k 0 X3 HB2
  ltac:(unfold regsT; ro_getr; reflexivity) ltac:(unfold regsT; ro_getr; reflexivity)) as HB3.
pose proof HB3 as (_ & _ & HJT & _). apply e_J0 in HJT.
(* the chain and the universe *)
destruct (e2_chain D fxk ly S Hp W regs mem md k HPRE HB) as (ch1 & Hach & Hsp1).
assert (HCH : chain_pre ly (aview SEGS (w_H W) mem) regsT ch1).
{ apply (achain_chain_pre ly _ (cn_S1 D) (cn_sp0 D) ch1 regsT Hach).
  - rewrite HSPT. unfold cn_sp0 in *. rewrite HSTK in *. lia.
  - unfold s0Z. rewrite T8. unfold w64. apply unsigned_lit_small. unfold cn_sp0 in *. lia.
  - rewrite HRAT. lia. }
assert (HTR : In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch1) (as_universe B))
  by exact (e2_univ D regsT ch1 RT_malloc (cn_pc 400) HUNIV HCTX e2_site HRAT Hsp1).
(* the malloc's trace is a FIXED one of the universe (P'' set: the call rule asks `admits`, YG01.admits_fix, and its
   post carries the trace in the journal's wild budget, which ajournal_xw_fix1 drops again) *)
assert (HTRc : In (call_trace ly (pc_malloc_ra0 (as_code B)) regsT ch1) (as_universe B)).
{ apply YCbq.call_trace_in; [exact (proj1 HUNIV RT_malloc) | exact HTR]. }
pose proof (alloc_model_laws_x_cf B (universe_ok_of_ARcf SEGS B _ _ _ _ _ _ (proj1 HAR))) as AMX.
pose proof (e2_live_pj_nonneg (ci_x D)) as HLP.
unfold cn_cfg. rewrite (pal_malloc B PAL). unfold w64 at 1.
eapply SRr_bind.
{ eapply (YGcallMxmnKeep.aj_malloc_at_x_m_keep (fx := fxk) (SK := SK) SEGS B prh_pst ARcfx QM_cf (QMm_cf SEGS B) malloc_cf cf_malloc_max
    free_cf (Wf_cf (as_universe B)) xs_cf LAWS (@pa_segs_low _ _ PA) (pal_env B PAL) OWNLOW WFL AMX (QMQ_cf SEGS B) XSL
    (YGcallMxmnKeep.amalloc_realizes_x_xs_keep (fx := fxk) SEGS B (AMALLOC fxk))
    W regsT mem STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
    [(CN_CID, ci_fpos D)] ly S Hp mdT k (cn_size D + 16) (cn_S1 D - cn_sp0 D) (w64 (cn_pc 400)) ch1).
  - exact HJT.
  - exact T10.
  - unfold cn_size in *. lia.
  - cbn [flat_map length] in HBUD. unfold cn_size in *. lia.
  - rewrite HSPT. lia.
  - exact HS1mod.
  - lia.
  - unfold ASTACK. rewrite HSTK. lia.
  - rewrite T3. exact Hgp0.
  - rewrite T4. exact Htp0.
  - exact T1.
  - unfold cn_pc. rewrite <- Z.add_assoc. apply ret_ok_codeptr_v; rewrite HOFF; [lia | reflexivity].
  - (* the QMm guard's two facts at the call: the hull admission from this cut's stage budget, and the call memory's
       arodata through cn_img's relro facts. Part 3c removed the guard's third, memnorm. *)
    apply (QMm_cf_of_room SEGS B _ _ _ _ _ _ (proj1 HAR) HQT (YGcfRoomLive.room_live_room _ HROOMc));
      [ (* the hull admission at the call: the copy1 cut's stage budget (PresetHullPay.hull_ok_of_budget) *)
        exact (PresetHullPay.hull_ok_of_budget _ _ HHULL)
      | (* arodata_ok_cf at the call memory: cn_img's relro facts through the bridge *)
        destruct (cni_relro_eq B IMG) as [EL EH];
        exact (YGcfAroBridge.arodata_ok_cf_of_P SEGS B W mem (cni_relro_seg B IMG) (cni_errno_relro B IMG)
          (cni_relro_top B IMG) (cni_ro_reads_nw B IMG) ltac:(rewrite EL, EH; exact HROD)) ].
  - exact HCH.
  - exact (admits_fix _ _ _ (universe_ok_of_ARcf SEGS B _ _ _ _ _ _ (proj1 HAR)) HTR). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HPR2 & Hres & Hfrs2 & HPREc & Htrc
  & (p & trc & Hpath & Hgf & Hleaf & Hpn & Hpa) & HARMS & HMNK).
(* the hull: the call uses one padded copy's malloc (PresetHullBudget.hull_used_of_call, any return value), and the
   copy1 stage's budget pays it to cpy1's (cn_hpay_copy) *)
pose proof (PresetHullBudget.hull_used_of_call _ _ _ _ (YGcfSecsStep.secs_malloc_step _ _ _ _ _ Hpath)) as HUSED.
pose proof HHULL as HH1. rewrite cn_hrest_cpy1_split in HH1.
destruct (cn_hpay_copy _ _ _ HH1) as [_ HNEXT].
assert (HHULL2 : PresetHullBudget.hull_budget S2 (cn_hrest_cpy1 (ci_x D))) by (apply HNEXT; exact HUSED).
(* the journal after the call: the fixed trace leaves the budget (YCbqG.v ajournal_xw_fix1) *)
pose proof (ajournal_xw_fix1 HTRc HJ2) as HJ2f. clear HJ2. rename HJ2f into HJ2.
assert (HPM2 : P mem2) by exact (PCALL _ _ HMNK HPM).
pose proof (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREc) as HPREcf.
destruct (e2_counts_at D ly S Hp W mem [] 0 HPRE HE ltac:(cbn [flat_map length]; lia)) as (CSEC & C24).
assert (HROOM2 : room_live_cf S2)
  by exact (@RM_malloc _ _ prh_room_malloc_a8 fxk rc ci SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ (p, S2) HPREcf CSEC C24 HROOMc Hpath).
(* ---- +400 mv s5, a0; +404 auipc s8 (PHi 9): ONE engine run (the auipc's value is the listing's hi) ---- *)
assert (HEI4 : img_env VAL A_LIM (e0_E1 regs2)) by (unfold e0_E1; apply Eimg_env).
assert (SHOK4 : sh_ok SEGS e0_Bx [] (e0_E1 regs2) (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (HS4 : st_ok_pi SEGS VAL (e0_E1 regs2) (mkSS (CN_OFF + 400) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (@mkst fxk regs2 (Z_to_bv 64 (BASE + (CN_OFF + 400))) mem2 (seg_rom SEGS)))).
{ rewrite (@restrict_mkst_fx fxk). unfold e0_E1. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I|]. split; exact I. }
pose (RUNTO := @paj_run_to_x_inv fxk rc SK A_prog_listing PL_cno_A PA B prh_pst ARcfx cf_head LAWS P PLAW).
unfold cn_pc. replace (BASE + CN_OFF + 400) with (BASE + (CN_OFF + 400)) by lia.
paj_run_to_tok_x_inv RUNTO HS4 HJ2 SHOK4 HPM2 e0_Bspan (CN_OFF + 408).
{ intros a (r & Hr & Ha). cbn [ss_mem In] in Hr. destruct Hr. }
pmkst HS4.
prreg HS4 (21%bv : bv 5) U21. prreg HS4 (24%bv : bv 5) U24. prreg HS4 (10%bv : bv 5) U10.
prreg HS4 (2%bv : bv 5) U2. prreg HS4 (3%bv : bv 5) U3. prreg HS4 (4%bv : bv 5) U4.
prreg HS4 (8%bv : bv 5) U8. prreg HS4 (9%bv : bv 5) U9. prreg HS4 (18%bv : bv 5) U18.
prreg HS4 (19%bv : bv 5) U19. prreg HS4 (20%bv : bv 5) U20. prreg HS4 (23%bv : bv 5) U23.
prreg HS4 (27%bv : bv 5) U27.
(* the two registers the cut names, and a0 at the branch *)
assert (EW4 : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (e0_E1 regs2) n = getr regs2 r).
{ intros n r Hn Hr. unfold e0_E1. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs2 _ n r Hr). }
assert (V21 : getr (ms_regs ms) 21%bv = w64 res)
  by (rewrite U21, (EW4 10%nat 10%bv ltac:(lia) eq_refl); exact Hres).
assert (V10 : getr (ms_regs ms) 10%bv = w64 res)
  by (rewrite U10, (EW4 10%nat 10%bv ltac:(lia) eq_refl); exact Hres).
assert (V24 : getr (ms_regs ms) 24%bv = w64 (VAL (A_HI 9))).
{ rewrite U24. unfold w64. rewrite <- (HEI4 (A_HI 9) ltac:(unfold A_TEXT, A_OBJ, A_HI, A_LIM; lia)).
  symmetry. apply Z_to_bv_bv_unsigned. }
assert (V3 : getr (ms_regs ms) 3%bv = getr (ci_regs D) 3%bv).
{ rewrite U3, (EW4 3%nat 3%bv ltac:(lia) eq_refl),
    (e5_pres _ _ 3%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)). exact T3. }
assert (V4 : getr (ms_regs ms) 4%bv = getr (ci_regs D) 4%bv).
{ rewrite U4, (EW4 4%nat 4%bv ltac:(lia) eq_refl),
    (e5_pres _ _ 4%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)). exact T4. }
assert (V2 : getr (ms_regs ms) 2%bv = w64 (cn_S1 D)).
{ rewrite U2, (EW4 2%nat 2%bv ltac:(lia) eq_refl),
    (e5_pres _ _ 2%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)). exact (RT 2%bv (cn_S1 D) ltac:(ro_in) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)). }
assert (V8 : getr (ms_regs ms) 8%bv = w64 (cn_sp0 D)).
{ rewrite U8, (EW4 8%nat 8%bv ltac:(lia) eq_refl),
    (e5_pres _ _ 8%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)). exact (RT 8%bv (cn_sp0 D) ltac:(ro_in) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)). }
assert (V9 : getr (ms_regs ms) 9%bv = w64 (cn_S1 D)).
{ rewrite U9, (EW4 9%nat 9%bv ltac:(lia) eq_refl),
    (e5_pres _ _ 9%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)). exact (RT 9%bv (cn_S1 D) ltac:(ro_in) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)). }
assert (V18 : getr (ms_regs ms) 18%bv = w64 (shadow_addr (cn_F D))).
{ rewrite U18, (EW4 18%nat 18%bv ltac:(lia) eq_refl),
    (e5_pres _ _ 18%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)). exact (RT 18%bv (shadow_addr (cn_F D)) ltac:(ro_in) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)). }
assert (V27 : getr (ms_regs ms) 27%bv = w64 (cn_F D)).
{ rewrite U27, (EW4 27%nat 27%bv ltac:(lia) eq_refl),
    (e5_pres _ _ 27%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)). exact (RT 27%bv (cn_F D) ltac:(ro_in) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)). }
assert (V20 : getr (ms_regs ms) 20%bv = w64 (cn_size D)).
{ rewrite U20, (EW4 20%nat 20%bv ltac:(lia) eq_refl),
    (e5_pres _ _ 20%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)). exact (RT 20%bv (cn_size D) ltac:(ro_in) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)). }
assert (V23 : getr (ms_regs ms) 23%bv = w64 (ci_data D)).
{ rewrite U23, (EW4 23%nat 23%bv ltac:(lia) eq_refl),
    (e5_pres _ _ 23%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)). exact (RT 23%bv (ci_data D) ltac:(ro_in) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)). }
assert (V19 : getr (ms_regs ms) 19%bv = w64 (cn_size D + 16)).
{ rewrite U19, (EW4 19%nat 19%bv ltac:(lia) eq_refl),
    (e5_pres _ _ 19%bv HPR2 ltac:(apply e5_cs; vm_compute; reflexivity)). exact T19. }
assert (Hres64 : 0 <= res < 2 ^ 64).
{ destruct HARMS as [HA | HA].
  - destruct HA as [E _]. rewrite E. lia.
  - destruct HA as (H4096 & Hab2 & _).
    destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ res (cn_size D + 16) (ajx_ar HJ2)
      ltac:(rewrite Hab2; apply in_or_app; right; left; reflexivity)) as (_ & _ & Hce & _).
    assert (Hsz16 : 0 <= cn_size D + 16) by (unfold cn_size; lia).
    pose proof (e2_req_ge (cn_size D + 16) Hsz16) as Hrq. lia. }
(* +408 beqz a0 -> +452 (refused) / +412 (granted) *)
replace (BASE + 1212) with (BASE + CN_OFF + 408) by lia.
change (mkCfg (@mkst fxk (ms_regs ms) (Z_to_bv 64 (BASE + CN_OFF + 408)) (ms_mem ms) (seg_rom SEGS))
  (with_vm_backing (m_vm_lazy md2) mat md2))
  with (@cn_cfg SEGS fxk (cn_pc 408) (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2)).
apply (cn_hs_beqz W2 fxk _ (ms_mem ms) _ _ 408 10%bv 44 452 412 (res =? 0));
  [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity | |].
{ rewrite ro_getr0, V10. apply ro_c_eq0. lia. }
intros X4.
destruct (Z.eqb_spec res 0) as [Hz | Hnz].
{ (* ---- THE REFUSED COPY: +452 li a0, 1; +456 sb a0, -1368(s8) (g_own_ran_out := 1); falls to +460 ---- *)
  apply (cn_hs_addi W2 fxk _ (ms_mem ms) _ _ 452 456 10%bv 0%bv 1);
    [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X5.
  destruct (e2_own_wr W2 (ms_mem ms)) as [Hoh How].
  pose proof (@pa_val_range _ _ PA (A_OBJ 13)) as HV13.
  unfold cn_cfg, cn_pc. replace (BASE + CN_OFF + 456) with (BASE + 1260) by lia.
  pose proof (@pa_val_range _ _ PA (A_HI 9)) as HV9.
  apply (e5s_sb P PLAW W2 _ (ms_mem ms) _ _ 1260 1264 24%bv 10%bv (-1368) (VAL (A_OBJ 13)));
    [vm_compute; reflexivity | lia | lia | reflexivity
    | ro_getr; rewrite V24; unfold v_addi, w64; rewrite unsigned_lit_small by lia;
      rewrite <- (cni_hi9 B IMG); f_equal; lia
    | lia | exact Hoh | exact How | exact HPM2 |].
  intros md5 mem5 Hs5 Hfr5 Hgr5 Hhid5 Hv5 HP5.
  (* the memory at the cut: the call's keeps, then the run (which wrote nothing), then the own byte *)
  destruct HARMS as [(Eres & Eab2 & KEPT & Herr & Hoom) | (H4096 & _)]; [|lia].
  destruct KEPT as (KA & KB & KC & KD & KE & KF).
  assert (KRUN : forall a, aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
  { intros a. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
    intros (r & Hr & _). cbn [ss_mem In] in Hr. destruct Hr. }
  assert (KSB : forall a, 0 <= a < 2 ^ 64 -> a <> VAL (A_OBJ 13) ->
    aview SEGS (w_H W2) mem5 a = aview SEGS (w_H W2) (ms_mem ms) a).
  { intros a Ha Hne. unfold aview, mbyte. rewrite (Hfr5 (Z_to_bv 64 a)); [reflexivity|].
    rewrite unsigned_lit_small by exact Ha. exact Hne. }
  assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> a <> VAL (A_OBJ 13) ->
    aview SEGS (w_H W2) mem5 a = aview SEGS (w_H W) mem a).
  { intros a Hi Hno Her Hne. pose proof (@pa_segs_low _ _ PA _ Hi) as Hlow. unfold kLowMemEnd in Hlow.
    rewrite (KSB a ltac:(lia) Hne), KRUN. exact (KC a Hi Hno Her). }
  assert (KHI : forall a, alloc_ceiling <= a < 2 ^ 64 ->
    ~ (cn_S1 D - ASTACK <= a < cn_S1 D) -> a <> VAL (A_OBJ 13) ->
    aview SEGS (w_H W2) mem5 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hw Hne. rewrite (KSB a ltac:(lia) Hne), KRUN. apply KA; [exact Ha | unfold cn_sp0 in *; lia]. }
  assert (KFRM : forall a, (in_zr a (frame_rng ly (CN_CID, ci_fpos D)) \/
      in_zr a (shadow_addr (frame_addr ly CN_CID (ci_fpos D)), fs_frame_bytes CN_CID / 8)) ->
    0 <= a < 2 ^ 64 -> a <> VAL (A_OBJ 13) ->
    aview SEGS (w_H W2) mem5 a = aview SEGS (w_H W) mem a).
  { intros a Hin Ha Hne. rewrite (KSB a Ha Hne), KRUN.
    apply (KD CN_CID (ci_fpos D) a); [rewrite Hfrs; left; reflexivity | exact Hin | intros []]. }
  (* ---- THE CUT CN_COPY2 on the refused arm: r1 = 0, own = 1 ---- *)
  replace (BASE + 1264) with (BASE + CN_OFF + 460) by lia.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst ?f ?rg ?pc ?mm ?rom) ?mo) _ =>
    change (mkCfg (@YK11.mkst f rg pc mm rom) mo) with (@cn_cfg SEGS f (cn_pc 460) rg mm mo);
    set (regsE := rg); set (mdE := mo) end.
  apply SRr_ret. split; [|exact HP5].
  exists fxk, ly2, S2, Hp, regsE, mem5, mdE, (k + (st_nev S2 - st_nev S)), 0, 1.
  split; [reflexivity|].
  (* the journal: the call's, then the run's (no write), then the own byte's store *)
  assert (HJ5 : cn_J B ARcfx D ly2 S2 Hp W2 mem5 mdE (k + (st_nev S2 - st_nev S)) 0).
  { apply cn_J_of_x. unfold mdE.
    apply (ajournal_x_pst_write SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) (cni_pst_ok B IMG)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); [| exact Hgr5 | exact Hhid5 | exact Hs5].
    intros x Hx. apply Hfr5. intros E. apply Hx. rewrite E. exact e2_own_pst. }
  split.
  { (* cn_base *)
    split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ5|].
    split.
    { (* cn_frame at (ly2, S2): the frames are the call's, the flag word and the presence are kept *)
      unfold cn_frame. rewrite Hfrs2. split; [exact Hfrs|]. split; [exact Hnin|].
      assert (EF : ly_F ly2 = ly_F ly).
      { pose proof (ajx_ly HJ2) as HL2.
        destruct HL2 as (_ & _ & _ & _ & _ & EF2 & _).
        destruct Hly as (_ & _ & _ & _ & _ & EF1 & _). rewrite EF2, EF1. reflexivity. }
      assert (Eframe : frame_addr ly2 CN_CID (ci_fpos D) = frame_addr ly CN_CID (ci_fpos D))
        by (unfold frame_addr; rewrite EF; reflexivity).
      assert (Eflag : flag_addr ly2 CN_CID (ci_fpos D) = flag_addr ly CN_CID (ci_fpos D))
        by (unfold flag_addr, frame_addr; rewrite EF; reflexivity).
      pose proof (e5_geo_of_base B ARcfx LAWS D fxk ly S Hp W regs mem md k HB) as [G HARc].
      pose proof G as (EFa & Fa0 & Fa1 & Fa32 & Fapp & S16g & Hacg & Hkbg & Hlog & H47g).
      destruct (e5_S1 D S16g) as [_ HS1c]. pose proof alloc_ceiling_val as [AC2 _].
      pose proof (e5_own_img B IMG) as [Hoi Hol]. unfold kLowMemEnd in Hol.
      assert (HFB : fs_frame_bytes CN_CID = 512) by (vm_compute; reflexivity).
      assert (Hfa : frame_addr ly CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F in *; congruence).
      assert (KFR : forall a, cn_F D <= a < cn_F D + fs_frame_bytes CN_CID ->
        aview SEGS (w_H W2) mem5 a = aview SEGS (w_H W) mem a).
      { intros a Ha. rewrite HFB in Ha. apply KFRM.
        - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFB. unfold cn_F in *. lia.
        - unfold cn_F in *. lia.
        - intros Heq. apply (frm_img_x SEGS B ARcfx LAWS ly S Hp W mem md CN_CID (ci_fpos D) (VAL (A_OBJ 13)) HARc
            ltac:(rewrite Hfrs; left; reflexivity)); [| exact Hoi].
          rewrite Hfa, HFB, <- Heq. exact Ha. }
      assert (KSH : forall a, shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + fs_frame_bytes CN_CID / 8 ->
        aview SEGS (w_H W2) mem5 a = aview SEGS (w_H W) mem a).
      { intros a Ha. rewrite HFB in Ha.
        assert (HF0 : 0 <= cn_F D) by (unfold cn_F in *; lia).
        assert (Hd8 : 0 <= cn_F D / 8) by (apply Z.div_pos; [exact HF0 | lia]).
        assert (Hdle : cn_F D / 8 <= cn_F D) by (apply Z.div_le_upper_bound; [lia | unfold cn_F in *; lia]).
        assert (Hsh : 2147450880 <= shadow_addr (cn_F D) /\ shadow_addr (cn_F D) + 64 < 2 ^ 64).
        { unfold shadow_addr, SHADOW_OFF. unfold cn_F in *. lia. }
        apply KFRM; [right; unfold in_zr; cbn [fst snd]; rewrite Hfa, HFB; lia | lia |].
        intros ->. unfold shadow_addr, SHADOW_OFF in *. lia. }
      split.
      { rewrite Eflag. rewrite <- Hflag. apply rdword_ext. intros q Hq.
        apply KFR. unfold cn_F in *. lia. }
      (* the frame's bytes and shadow are present in every ARx state (alx_frames at the cut's own state) *)
      destruct (alx_frames SEGS B ARcfx LAWS ly2 S2 Hp W2 mem5 mdE CN_CID (ci_fpos D) (ajx_ar (e_J0 B ARcfx _ _ _ _ _ _ _ _ HJ5))
        ltac:(rewrite Hfrs2, Hfrs; left; reflexivity)) as (_ & _ & HFPR & HFSH).
      split.
      - intros a Ha. destruct (HFPR a ltac:(rewrite Eframe, Hfa; exact Ha)) as [Hpr _]. exact Hpr.
      - intros a Ha. destruct (HFSH (a - shadow_addr (cn_F D)) ltac:(lia)) as [Hpr _].
        replace (shadow_addr (frame_addr ly2 CN_CID (ci_fpos D)) + (a - shadow_addr (cn_F D))) with a in Hpr
          by (rewrite Eframe, Hfa; lia).
        exact Hpr. }
    split.
    { (* cn_saved: the saved words are above the ceiling and above the call's window *)
      unfold cn_saved in *.
      repeat (let H := fresh "Hs" in apply Forall_cons_iff in HSV as [H HSV]; apply Forall_cons;
        [cbn [fst snd] in H |- *; rewrite <- H; apply rdword_ext; intros q Hq;
         apply KHI; [unfold cn_sp0 in *; lia | unfold ASTACK; unfold cn_sp0 in *; lia |
           intros Heq; pose proof (e5_own_img B IMG) as [_ Hol2]; unfold kLowMemEnd in Hol2;
           pose proof alloc_ceiling_val as [AC3 _]; unfold cn_sp0 in *; lia] |]).
      apply Forall_nil. }
    split; [unfold regsE; ro_getr; exact V3|]. split; [unfold regsE; ro_getr; exact V4|].
    intros a Hro Hno Herr2.
    assert (Hi : in_img SEGS a)
      by (destruct Hro as [(sg & Hsg & _ & Ha) | Hr]; [exists sg; split; [exact Hsg | exact Ha] | exact (@pa_relro_img _ _ PA a Hr)]).
    rewrite (KIMG a Hi Hno Herr2 ltac:(intros ->; exact (cni_pst_rw B IMG _ e2_own_pst Hro))).
    exact (HROD a Hro Hno Herr2). }
  split.
  { unfold cn_regsat, cn_core, cn_s8. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold regsE; ro_getr.
    - exact V2.
    - exact V8.
    - exact V9.
    - exact V18.
    - exact V27.
    - exact V24.
    - exact V19.
    - exact V20.
    - rewrite V21, Eres. reflexivity.
    - exact V23. }
  split.
  { (* the two slots: above the call's window and above the ceiling, and not the own byte *)
    unfold cn_slotsL in *.
    repeat (let H := fresh "Hsl" in apply Forall_cons_iff in HSL as [H HSL]; apply Forall_cons;
      [cbn [fst snd] in H |- *; rewrite <- H; apply rdword_ext; intros q Hq;
       apply KHI; [unfold cn_sp0 in *; lia | unfold ASTACK; unfold cn_sp0 in *; lia |
         intros Heq; pose proof (e5_own_img B IMG) as [_ Hol2]; unfold kLowMemEnd in Hol2;
         pose proof alloc_ceiling_val as [AC3 _]; unfold cn_sp0 in *; lia] |]).
    apply Forall_nil. }
  (* ---- cn_early with the refused copy: rs = [0], own = 1 ---- *)
  assert (HOWN1 : prh_own W2 mem5 1).
  { split; [|right; reflexivity]. change pi_gz_own_ran_out with 1%nat. rewrite <- (cni_own B IMG).
    apply e5_val_mem1_of_aview; [| lia].
    rewrite Hv5. f_equal. unfold regsE. ro_getr. rewrite ro_getr0. vm_compute. reflexivity. }
  assert (ERS : PresetRoom.rs_live (YGcfRoom.room_of_cf S2) = PresetRoom.rs_live (YGcfRoom.room_of_cf S)).
  { change (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) with (map snd (blocks S2)).
    change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)).
    pose proof (f_equal (map snd) Eab2) as E. unfold ablocks in E. rewrite !map_map in E. cbn [snd] in E. exact E. }
  split; [|exact HHULL2].
  unfold cn_early. split; [exact HHp|].
  split.
  { apply (e2_ledger_own ly S Hp W mem ly2 S2 Hp W2 mem5 (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D)
      (ci_most D) 0 1 HLG).
    - intros a Hpst Hne. apply KIMG;
        [exact (proj1 (cni_pst_ok B IMG a Hpst)) | exact (proj2 (cni_pst_ok B IMG a Hpst))
        | exact (cni_pst_errno B IMG a Hpst) | exact Hne].
    - exact HOWN1.
    - intros a kk i Hin Hi. apply prh_mbyte_of_aview.
      destruct (prh_ledger_hblock B ly S Hp W mem _ _ _ _ _ a kk _ _ HLG Hin) as (Hk0 & Hblk & _).
      pose proof cf_head_nonneg. unfold prh_head_wide in HW.
      assert (Hrq : 0 < req_size (kk + cf_head))
        by (unfold req_size; destruct (kk + cf_head =? 0) eqn:E; [lia | apply Z.eqb_neq in E; lia]).
      destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hblk)
        as (_ & Hb4096 & Hbtop & _ & _ & _).
      assert (Hrng : a - cf_head <= a - cf_head + i < a - cf_head + req_size (kk + cf_head)).
      { assert (Hkc : 0 <= kk + cf_head) by lia.
        pose proof (e2_req_ge (kk + cf_head) Hkc) as Hge. lia. }
      assert (Himg : ~ in_img SEGS (a - cf_head + i)).
      { exact (proj2 (alx_client_img SEGS B ARcfx LAWS ly S Hp W mem md (a - cf_head + i) HAR
          (or_introl (ex_intro _ (a - cf_head) (ex_intro _ (kk + cf_head) (conj Hblk Hrng)))))). }
      assert (Hne13 : a - cf_head + i <> VAL (A_OBJ 13)).
      { intros E. apply Himg. rewrite E, (cni_own B IMG).
        assert (HW1 : (0 < pi_gz_own_ran_out)%nat) by (cbn; lia).
        pose proof (prh_pst_own 0%nat HW1) as Hp0.
        rewrite Z.add_0_r in Hp0. exact (proj1 (cni_pst_ok B IMG _ Hp0)). }
      assert (Hin64 : 0 <= a - cf_head + i < 2 ^ 64).
      { pose proof alloc_ceiling_val as AC4. destruct AC4 as [AC4a AC4b]. lia. }
      rewrite (KSB (a - cf_head + i) Hin64 Hne13), KRUN.
      apply (KB (a - cf_head) (kk + cf_head) i Hblk); [| intros []].
      unfold req_size. destruct (kk + cf_head =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia].
    - intros a kk Hin Hb. rewrite Eab2. exact Hb.
    - apply Permutation_refl. }
  split; [apply Forall_cons; [left; reflexivity | apply Forall_nil]|].
  split.
  { unfold cn_cblk. cbn [flat_map app]. rewrite Eab2.
    unfold cn_cblk in HPERM. cbn [flat_map app] in HPERM. exact HPERM. }
  split; [exact HROOM2|].
  split.
  { unfold cn_prog, cn_cevsl, cn_cblk in *. cbn [flat_map map app] in *.
    destruct HRP as [HRP1 HRP2]. split; [rewrite ERS; exact HRP1|].
    intros sm x0 os i H0 hist Hpos Hrun.
    destruct (HRP2 sm x0 os i H0 hist Hpos Hrun) as (hist' & Hpos').
    exists hist'. rewrite Nat.add_0_r in Hpos' |- *.
    exact (PresetRoomPosKeep.room_pos_keep_alloc_null SEGS B ly S Hp W regsT mem mdT ch1 sm x0 os i H0 hist'
      (cn_size D + 16) _ trc S2 HPREcf ltac:(unfold cn_size in *; lia) ltac:(cbn [flat_map length] in HBUD;
        unfold cn_size in *; lia) HTRc ltac:(rewrite <- Eres in Hpn; rewrite (proj2 Hpn eq_refl) in Hpath; exact Hpath)
      Hpos'). }
  split.
  { pose proof (blocks_bytes_bsum B ly2 S2) as EB2. pose proof (blocks_bytes_bsum B ly S) as EB.
    rewrite EB2, Eab2, <- EB. cbn [length] in HBUD |- *.
    assert (Hsz0 : 0 <= cn_size D + 16) by (unfold cn_size in *; lia). lia. }
  split; [right; reflexivity|].
  split; [rewrite (cni_own B IMG); exact (proj1 HOWN1)|].
  split; [intros Hc; discriminate Hc|].
  (* the refused copy: CNO-COPY's refusal is dead at a consumer run. Copy 1's __wrap_malloc returned NULL on a
     granted path (the rule's apath / gflag) at the cut's own state S, after no granted copy (cn_prog over []) *)
  intros _.
  apply (e2_cdead D [] S HRP ltac:(cbn [flat_map length]; lia) (WFL _ _ _ _ _ _ HAR)).
  left. exists (cn_size D + 16), (call_trace ly (pc_malloc_ra0 (as_code B)) regsT ch1), trc, S2.
  split; [|exact Hgf]. rewrite <- (proj2 Hpn Eres). exact Hpath. }
(* ---- THE GRANTED COPY: res <> 0, the new block (res, size + 16); +412 beqz s4 (skip the copy when size = 0), +416..428
   the memcpy (ACPY), +432..444 the 16-byte 0x31 padding (ASET), +448 j to the cut ---- *)
destruct HARMS as [(Eres & _) | (H4096 & Eab2 & KEPT)]; [exfalso; exact (Hnz Eres)|].
destruct KEPT as (KA & KB & KC & KD & KE & KF).
pose proof alloc_ceiling_val as [AC2 _].
pose proof (e5_S1 D Hal16) as [_ HS1c].
assert (Hsz0 : 0 <= cn_size D) by (unfold cn_size; lia).
assert (HinNB : In (res, cn_size D + 16) (ablocks B ly2 S2))
  by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks SEGS B ARcfx LAWS _ _ _ _ _ _ res (cn_size D + 16) (ajx_ar HJ2) HinNB)
  as (_ & Hr4096 & Hrtop & Hrapp & _ & Hpw).
assert (Hsz16 : 0 <= cn_size D + 16) by lia.
pose proof (e2_req_ge (cn_size D + 16) Hsz16) as Hrq.
assert (Hrq1 : 1 <= req_size (cn_size D + 16))
  by (unfold req_size; destruct (Z.eqb_spec (cn_size D + 16) 0); lia).
(* every block of S is apart from the new one *)
assert (HAPART : forall b m, In (b, m) (ablocks B ly S) ->
  zdisjoint (b, req_size m) (res, req_size (cn_size D + 16))).
{ intros b m Hbm. rewrite Eab2, map_app in Hpw. apply pairwise_app_inv in Hpw as (_ & _ & Hx).
  apply (Hx (b, req_size m) (res, req_size (cn_size D + 16))).
  - apply in_map_iff. exists (b, m). split; [reflexivity | exact Hbm].
  - left. reflexivity. }
assert (HNEW : ~ In (res, cn_size D + 16) (ablocks B ly S)).
{ intros Hc. pose proof (HAPART _ _ Hc) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HNEW0 : ~ In (res, cn_size D + 16) (ablocks B (ci_ly D) (ci_S D))).
{ intros Hc. apply HNEW. exact (e2_blocks_in D ly S Hp W mem md k _ _ HJ Hc Hsz16). }
assert (HresHp : ~ In res Hp).
{ intros Hh. pose proof (prh_ledger_heads B ly S Hp W mem _ _ _ _ _ _ _ HLG) as HPh.
  apply (Permutation_in _ HPh) in Hh. apply in_map_iff in Hh as ([a kk] & Eh & Hak). cbn [fst] in Eh.
  destruct (prh_ledger_hblock B ly S Hp W mem _ _ _ _ _ a kk _ _ HLG Hak) as (Hk0 & Hblk & _).
  rewrite Eh in Hblk. pose proof (HAPART _ _ Hblk) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  pose proof cf_head_nonneg.
  assert (1 <= req_size (kk + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia). lia. }
(* the run from +400 wrote nothing *)
assert (KRUN : forall a, aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hr & _). cbn [ss_mem In] in Hr. destruct Hr. }
(* the ledger at the run's memory, own still 0 *)
assert (KI1 : forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Hp0. rewrite KRUN.
  exact (KC a (proj1 (cni_pst_ok B IMG a Hp0)) (proj2 (cni_pst_ok B IMG a Hp0)) (cni_pst_errno B IMG a Hp0)). }
assert (L1 : prh_ledger B ly2 S2 Hp W2 (ms_mem ms) (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) 0).
{ apply (e2_ledger_own ly S Hp W mem ly2 S2 Hp W2 (ms_mem ms) (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D)
    (ci_most D) 0 0 HLG).
  - intros a Hp0 _. exact (KI1 a Hp0).
  - split; [|left; reflexivity]. rewrite <- (cni_own B IMG).
    apply (val_mem_kept SEGS (w_H W) (w_H W2) mem (ms_mem ms)); [|exact Hown].
    intros q Hq. apply KI1. rewrite (cni_own B IMG). exact (e2_cell_pst _ _ q prh_pst_own Hq).
  - intros a kk i Hin Hi. apply prh_mbyte_of_aview. rewrite KRUN.
    destruct (prh_ledger_hblock B ly S Hp W mem _ _ _ _ _ a kk _ _ HLG Hin) as (Hk0 & Hblk & _).
    pose proof cf_head_nonneg. unfold prh_head_wide in HW.
    assert (Hkc : 0 <= kk + cf_head) by lia. pose proof (e2_req_ge _ Hkc) as Hge.
    pose proof (HAPART _ _ Hblk) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    apply (KB (a - cf_head) (kk + cf_head) i Hblk); [lia | cbv beta; lia].
  - intros a kk Hin Hb. rewrite Eab2. apply in_or_app. left. exact Hb.
  - apply Permutation_refl. }
(* the source: its bytes at the run's memory are the entry's, it is apart from the new block, its shadow is usable *)
pose proof HSRC as (HSby & HS4096 & HSce & HSam & _ & _).
assert (SRCK : forall a, ci_data D <= a < ci_data D + cn_size D ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H (ci_W D)) (ci_mem D) a).
{ intros a Ha. assert (Hs0 : 0 < cn_size D) by lia.
  exact (e2_src_kept D ly2 S2 Hp W2 (ms_mem ms) _ _ (ci_data D) (cn_size D)
    (cn_J_of_x B ARcfx _ _ _ _ _ _ _ _ 0 HJ2) HLED (HHOME Hs0) a Ha). }
assert (SRCD : 0 < cn_size D -> res + cn_size D <= ci_data D \/ ci_data D + cn_size D <= res).
{ intros Hs0. pose proof cf_head_nonneg as CH0.
  assert (BLK : forall b m, In (b, m) (ablocks B ly S) -> b <= ci_data D -> ci_data D + cn_size D <= b + req_size m ->
    res + cn_size D <= ci_data D \/ ci_data D + cn_size D <= res).
  { intros b m Hbm Hb Hm. pose proof (HAPART _ _ Hbm) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (IMGc : (forall a, ci_data D <= a < ci_data D + cn_size D -> in_img SEGS a) ->
    res + cn_size D <= ci_data D \/ ci_data D + cn_size D <= res).
  { intros Hi. destruct (Z_le_gt_dec (res + cn_size D) (ci_data D)) as [h|h]; [left; exact h|].
    destruct (Z_le_gt_dec (ci_data D + cn_size D) res) as [h'|h']; [right; exact h'|]. exfalso.
    destruct (Z_le_gt_dec res (ci_data D)) as [hz|hz].
    - assert (Hz1 : res <= ci_data D < res + req_size (cn_size D + 16)) by lia.
      assert (Hz2 : ci_data D <= ci_data D < ci_data D + cn_size D) by lia.
      exact (proj2 (alx_client_img SEGS B ARcfx LAWS ly2 S2 Hp W2 _ _ (ci_data D) (ajx_ar HJ2)
        (or_introl (ex_intro _ res (ex_intro _ (cn_size D + 16) (conj HinNB Hz1))))) (Hi _ Hz2)).
    - assert (Hz1 : res <= res < res + req_size (cn_size D + 16)) by lia.
      assert (Hz2 : ci_data D <= res < ci_data D + cn_size D) by lia.
      exact (proj2 (alx_client_img SEGS B ARcfx LAWS ly2 S2 Hp W2 _ _ res (ajx_ar HJ2)
        (or_introl (ex_intro _ res (ex_intro _ (cn_size D + 16) (conj HinNB Hz1))))) (Hi _ Hz2)). }
  assert (ROI : forall a, in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a -> in_img SEGS a).
  { intros a Hr. destruct Hr as [(sg & Hsg & _ & Hsa) | Hr];
      [exists sg; split; [exact Hsg | exact Hsa] | exact (@pa_relro_img _ _ PA a Hr)]. }
  destruct (HHOME Hs0) as [[(b & m & Hin & Hb & Hm) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hin & _ & Hb & Hm)].
  - destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ b m _ _ HLED Hin) as (Hm0 & Hab & _).
    assert (Hmc : 0 <= m + cf_head) by lia. pose proof (e2_req_ge _ Hmc).
    apply (BLK (b - cf_head) (m + cf_head) (e2_blocks_in D ly S Hp W mem md k _ _ HJ Hab Hmc)); lia.
  - apply IMGc. intros a Ha. exact (ROI a (proj1 (Hro a Ha))).
  - apply IMGc. intros a Ha. exact (ROI a (proj1 (Hro a Ha))).
  - assert (Hm0 : 0 <= m) by lia. pose proof (e2_req_ge m Hm0).
    apply (BLK b m (e2_blocks_in D ly S Hp W mem md k _ _ HJ Hin Hm0)); lia. }
assert (SRCH : forall Wc memc mdc pk cnt fl rn mo ow, ARcfx ly2 S2 Hp Wc memc mdc ->
  prh_ledger B ly2 S2 Hp Wc memc (ci_Lam D) pk cnt fl rn mo ow -> 0 < cn_size D ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (ci_data D) (cn_size D) /\
  shadow_hull_vis (aview SEGS (w_H Wc) memc) (ci_data D) (cn_size D)).
{ intros Wc memc mdc pk cnt fl rn mo ow HARc HLc Hs0.
  apply (e2_src_shadow ly2 S2 Hp Wc memc mdc (ci_Lam D) pk cnt fl rn mo ow _ _ HARc HLc Hs0).
  destruct (HHOME Hs0) as [Hk | (b & m & Hin & Hbn & Hb & Hm)]; [left; exact Hk | right].
  exists b, m. split; [|split; [rewrite HHp; exact Hbn | lia]].
  apply (e2_blocks_in D ly2 S2 Hp W2 (ms_mem ms) _ _ _ _ (cn_J_of_x B ARcfx _ _ _ _ _ _ _ _ 0 HJ2) Hin). lia. }
(* the destination: writable (a temporary block of the journal), apart from the window, application memory, shadowed *)
assert (DSTH : forall Wc memc mdc pk cnt fl rn mo ow d n, ARcfx ly2 S2 Hp Wc memc mdc ->
  prh_ledger B ly2 S2 Hp Wc memc (ci_Lam D) pk cnt fl rn mo ow -> 0 < n -> res <= d -> d + n <= res + (cn_size D + 16) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF d n /\ shadow_hull_vis (aview SEGS (w_H Wc) memc) d n).
{ intros Wc memc mdc pk cnt fl rn mo ow d n HARc HLc Hn Hd1 Hd2.
  apply (e2_src_shadow ly2 S2 Hp Wc memc mdc (ci_Lam D) pk cnt fl rn mo ow d n HARc HLc Hn).
  right. exists res, (cn_size D + 16). split; [exact HinNB|]. split; [exact HresHp|]. lia. }
assert (HWIN : YM05.alloc_ceiling + 8 <= cn_S1 D - ESTACK) by (unfold ESTACK; rewrite HSTK in Hslo; lia).
assert (AWR : forall a, res <= a < res + (cn_size D + 16) ->
  awr_byte STK_check_no_overread (cn_sp0 D) [] (ablocks B (ci_ly D) (ci_S D)) (ablocks B ly2 S2) ly2
    [(CN_CID, ci_fpos D)] a /\
  ~ (cn_sp0 D + (cn_S1 D - cn_sp0 D) - ESTACK <= a < cn_sp0 D + (cn_S1 D - cn_sp0 D))).
{ intros a Ha. split; [|lia].
  right; right; left. exists res, (cn_size D + 16). split; [exact HinNB|]. split; [exact HNEW0|]. lia. }
assert (AMR : forall d n, res <= d -> d + n <= res + (cn_size D + 16) -> 0 <= n -> amem_range d n).
{ intros d n Hd1 Hd2 Hn. unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, ASAN_CEIL in *. lia. }
assert (TAIL : forall regsX memX mdX,
  cn_J B ARcfx D ly2 S2 Hp W2 memX mdX (k + (st_nev S2 - st_nev S)) 0 -> P memX ->
  (forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 23%bv; 24%bv; 27%bv] ->
     getr regsX r = getr (ms_regs ms) r) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + cn_size D) -> ~ (cn_S1 D - ESTACK <= a < cn_S1 D) ->
     aview SEGS (w_H W2) memX a = aview SEGS (w_H W2) (ms_mem ms) a) ->
  (forall i, 0 <= i < cn_size D ->
     aview SEGS (w_H W2) memX (res + i) = aview SEGS (w_H W2) (ms_mem ms) (ci_data D + i)) ->
  SRr SEGS W2 (@cn_cfg SEGS fxk (cn_pc 432) regsX memX mdX)
    (fun W' c' => cn_ex_copy2 (fx := fx) B ARcfx D W' c' /\ P (ms_mem (cfg_ms c')))).
{ intros regsX memX mdX HJX HPX RX KX CX.
  pose proof HJX as HJXc. apply e_J0 in HJXc.
  assert (LX : prh_ledger B ly2 S2 Hp W2 memX (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) 0).
  { apply (e2_ledger_blk ly2 S2 Hp W2 (ms_mem ms) _ memX _ _ _ _ _ _ _ res (cn_size D + 16) (ajx_ar HJ2) L1 HinNB HresHp).
    intros a Ha Hn. apply KX; lia. }
  (* +432 add a0, s5, s4; +436 li a1, 0x31; +440 li a2, 16; +444 jal __asan_memset *)
  apply (e2_hs_add W2 fxk regsX memX mdX _ 432 436 10%bv 21%bv 20%bv);
    [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X10.
  apply (cn_hs_addi W2 fxk _ memX _ _ 436 440 11%bv 0%bv 49); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X11.
  apply (cn_hs_addi W2 fxk _ memX _ _ 440 444 12%bv 0%bv 16); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X12.
  apply (cn_hs_call W2 fxk _ memX _ _ 444 448 AS___asan_memset); [vm_compute; reflexivity | lia | reflexivity |].
  intros X13.
  lazymatch goal with |- SRr _ _ (@cn_cfg _ _ _ ?rg _ ?mo) _ => set (regsS := rg); set (mdS := mo) end.
  assert (S10 : getr regsS 10%bv = w64 (res + cn_size D)).
  { unfold regsS. ro_getr. rewrite (RX 21%bv ltac:(ro_in)), (RX 20%bv ltac:(ro_in)), V21, V20.
    apply e2_vadd; lia. }
  assert (S11 : getr regsS 11%bv = w64 49) by (unfold regsS; ro_getr; rewrite ro_getr0; apply (e2_addi 0 49); lia).
  assert (S12 : getr regsS 12%bv = w64 16) by (unfold regsS; ro_getr; rewrite ro_getr0; apply (e2_addi 0 16); lia).
  assert (SR1 : getr regsS 1%bv = w64 (cn_pc 448)) by (unfold regsS; ro_getr; reflexivity).
  assert (SR3 : getr regsS 3%bv = w64 (as_gp B))
    by (unfold regsS; ro_getr; rewrite (RX 3%bv ltac:(ro_in)), V3; exact Hgp0).
  assert (SR4 : getr regsS 4%bv = w64 (as_tp B))
    by (unfold regsS; ro_getr; rewrite (RX 4%bv ltac:(ro_in)), V4; exact Htp0).
  assert (SSP : spZ regsS = cn_sp0 D + (cn_S1 D - cn_sp0 D)).
  { unfold spZ, regsS. ro_getr. rewrite (RX 2%bv ltac:(ro_in)), V2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  pose proof (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X13
    (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X12
    (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X11
    (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X10 HJXc))))
    as HJS.
  destruct (DSTH W2 memX _ _ _ _ _ _ _ (res + cn_size D) 16 (ajx_ar HJS) LX ltac:(lia) ltac:(lia) ltac:(lia))
    as [DRA2 DHV2].
  unfold cn_cfg. unfold w64 at 1.
  eapply SRr_bind.
  { apply (aj_intrin_at_xm (fx := fxk) (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) OSet
      (SIGMA AS___asan_memset) (ASET fxk)
      W2 regsS memX STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
      [(CN_CID, ci_fpos D)] ly2 S2 Hp mdS (k + (st_nev S2 - st_nev S)) (res + cn_size D) 49 16
      (cn_S1 D - cn_sp0 D) (w64 (cn_pc 448))).
    - exact HJS.
    - exact S10.
    - exact S11.
    - exact S12.
    - lia.
    - lia.
    - lia.
    - exact SSP.
    - exact HS1mod.
    - lia.
    - unfold ESTACK. rewrite HSTK. lia.
    - exact SR3.
    - exact SR4.
    - exact SR1.
    - unfold cn_pc. rewrite <- Z.add_assoc. apply ret_ok_codeptr_v; rewrite HOFF; [lia | reflexivity].
    - intros a Ha. apply AWR. lia.
    - apply AMR; lia.
    - exact DRA2.
    - intros _. exact DHV2.
    - exact I. }
  cbv beta. intros W4 c4 Hwle4 (-> & regs3 & mem3 & md3 & -> & HJ3 & HPR3 & H310 & HBY3 & HKP3 & HGR3 & HMN3).
  change (mkCfg (@YK11.mkst fxk regs3 (w64 (cn_pc 448)) mem3 (YK11.seg_rom SEGS)) md3)
    with (@cn_cfg SEGS fxk (cn_pc 448) regs3 mem3 md3).
  (* +448 j 0xc -> +460, the cut *)
  apply (cn_hs_j W2 fxk regs3 mem3 md3 _ 448 460 12); [vm_compute; reflexivity | lia | reflexivity | lia |].
  intros X14.
  set (mdE := with_vm_backing (m_vm_lazy md3) X14 md3).
  apply SRr_ret. split; [|exact (PCALL _ _ HMN3 HPX)].
  exists fxk, ly2, S2, Hp, regs3, mem3, mdE, (k + (st_nev S2 - st_nev S)), res, 0.
  split; [reflexivity|].
  assert (HJE : cn_J B ARcfx D ly2 S2 Hp W2 mem3 mdE (k + (st_nev S2 - st_nev S)) 0).
  { apply cn_J_of_x. unfold mdE.
    exact (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X14 HJ3). }
  (* the memory at the cut against the CA2 entry: the padding, the copy, the run, the call's keeps *)
  assert (KE3 : forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + (cn_size D + 16)) ->
    ~ (cn_S1 D - ESTACK <= a < cn_S1 D) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) (ms_mem ms) a).
  { intros a Ha Hn Hw. rewrite (HKP3 a Ha ltac:(lia) ltac:(lia)). apply KX; lia. }
  assert (KHI3 : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (cn_S1 D - ASTACK <= a < cn_S1 D) ->
    aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hw. rewrite (KE3 a ltac:(lia) ltac:(lia) ltac:(unfold ASTACK, ESTACK in *; lia)), KRUN.
    apply KA; [exact Ha | unfold cn_sp0 in *; lia]. }
  assert (KIMG3 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W) mem a).
  { intros a Hi Hno Her. pose proof (@pa_segs_low _ _ PA _ Hi) as Hlow. unfold kLowMemEnd in Hlow.
    assert (Hnb : ~ (res <= a < res + (cn_size D + 16))).
    { intros Hr. assert (Hr' : res <= a < res + req_size (cn_size D + 16)) by lia.
      exact (proj2 (alx_client_img SEGS B ARcfx LAWS ly2 S2 Hp W2 _ _ a (ajx_ar HJ2)
        (or_introl (ex_intro _ res (ex_intro _ (cn_size D + 16) (conj HinNB Hr'))))) Hi). }
    rewrite (KE3 a ltac:(lia) Hnb ltac:(lia)), KRUN. exact (KC a Hi Hno Her). }
  (* the frame geometry (as on the refused arm) *)
  assert (EF : ly_F ly2 = ly_F ly).
  { pose proof (ajx_ly HJ2) as HL2.
    destruct HL2 as (_ & _ & _ & _ & _ & EF2 & _).
    destruct Hly as (_ & _ & _ & _ & _ & EF1 & _). rewrite EF2, EF1. reflexivity. }
  assert (Eframe : frame_addr ly2 CN_CID (ci_fpos D) = frame_addr ly CN_CID (ci_fpos D))
    by (unfold frame_addr; rewrite EF; reflexivity).
  assert (Eflag : flag_addr ly2 CN_CID (ci_fpos D) = flag_addr ly CN_CID (ci_fpos D))
    by (unfold flag_addr, frame_addr; rewrite EF; reflexivity).
  pose proof (e5_geo_of_base B ARcfx LAWS D fxk ly S Hp W regs mem md k HB) as [G HARc].
  pose proof G as (EFa & Fa0 & Fa1 & Fa32 & Fapp & S16g & Hacg & Hkbg & Hlog & H47g).
  assert (HFB : fs_frame_bytes CN_CID = 512) by (vm_compute; reflexivity).
  assert (Hfa : frame_addr ly CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F in *; congruence).
  assert (KFR3 : forall a, cn_F D <= a < cn_F D + fs_frame_bytes CN_CID ->
    aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W) mem a).
  { intros a Ha. rewrite HFB in Ha.
    destruct (alx_sep SEGS B ARcfx LAWS ly2 S2 Hp W2 _ _ (ajx_ar HJ2)) as [Hsep Hfb].
    apply pairwise_app_inv in Hsep as (_ & _ & Hsx).
    assert (HFin : In (CN_CID, ci_fpos D) (frames S2)) by (rewrite Hfrs2, Hfrs; left; reflexivity).
    pose proof (Hsx (res, req_size (cn_size D + 16)) (frame_addr ly2 CN_CID (ci_fpos D), fs_frame_bytes CN_CID)
      ltac:(apply in_map_iff; exists (res, cn_size D + 16); split; [reflexivity | exact HinNB])
      ltac:(apply in_map_iff; exists (CN_CID, ci_fpos D); split; [reflexivity | exact HFin])) as HdF.
    pose proof (proj1 (Forall_forall _ _) Hfb _ HFin) as (HF4096 & HFtop). cbn [fst snd] in HdF, HF4096, HFtop.
    rewrite Eframe, Hfa in HF4096. rewrite Eframe, Hfa, HFB in HFtop. rewrite Eframe, Hfa, HFB in HdF.
    unfold zdisjoint in HdF. cbn [fst snd] in HdF.
    rewrite (KE3 a ltac:(lia) ltac:(lia) ltac:(lia)), KRUN.
    apply (KD CN_CID (ci_fpos D) a); [rewrite Hfrs; left; reflexivity | | cbv beta; lia].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa, HFB. lia. }
  (* the ledger at the cut *)
  assert (L3 : prh_ledger B ly2 S2 Hp W2 mem3 (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) (ci_most D) 0).
  { apply (e2_ledger_blk ly2 S2 Hp W2 memX _ mem3 _ _ _ _ _ _ _ res (cn_size D + 16) (ajx_ar HJXc) LX HinNB HresHp).
    intros a Ha Hn. apply HKP3; lia. }
  assert (G3R : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 23%bv; 24%bv; 27%bv] ->
    getr regs3 r = getr (ms_regs ms) r).
  { intros r Hr. rewrite <- (RX r Hr). cbn in Hr.
    repeat (destruct Hr as [<- | Hr];
      [lazymatch goal with |- getr _ ?r = _ =>
         rewrite (e5_pres _ _ r HPR3 ltac:(apply e5_cs; vm_compute; reflexivity)) end;
       unfold regsS; ro_getr; reflexivity |]).
    destruct Hr. }
  split.
  { (* cn_base *)
    split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJE|].
    split.
    { unfold cn_frame. rewrite Hfrs2. split; [exact Hfrs|]. split; [exact Hnin|].
      split.
      { rewrite Eflag. rewrite <- Hflag. apply rdword_ext. intros q Hq.
        apply KFR3. unfold cn_F in *. lia. }
      destruct (alx_frames SEGS B ARcfx LAWS ly2 S2 Hp W2 mem3 mdE CN_CID (ci_fpos D) (ajx_ar (e_J0 B ARcfx _ _ _ _ _ _ _ _ HJE))
        ltac:(rewrite Hfrs2, Hfrs; left; reflexivity)) as (_ & _ & HFPR & HFSH).
      split.
      - intros a Ha. destruct (HFPR a ltac:(rewrite Eframe, Hfa; exact Ha)) as [Hpr _]. exact Hpr.
      - intros a Ha. destruct (HFSH (a - shadow_addr (cn_F D)) ltac:(lia)) as [Hpr _].
        replace (shadow_addr (frame_addr ly2 CN_CID (ci_fpos D)) + (a - shadow_addr (cn_F D))) with a in Hpr
          by (rewrite Eframe, Hfa; lia).
        exact Hpr. }
    split.
    { unfold cn_saved in *.
      repeat (let H := fresh "Hs" in apply Forall_cons_iff in HSV as [H HSV]; apply Forall_cons;
        [cbn [fst snd] in H |- *; rewrite <- H; apply rdword_ext; intros q Hq;
         apply KHI3; [unfold cn_sp0 in *; lia | unfold ASTACK; unfold cn_sp0 in *; lia] |]).
      apply Forall_nil. }
    split; [rewrite (G3R 3%bv ltac:(ro_in)); exact V3|].
    split; [rewrite (G3R 4%bv ltac:(ro_in)); exact V4|].
    intros a Hro Hno Herr2.
    assert (Hi : in_img SEGS a)
      by (destruct Hro as [(sg & Hsg & _ & Ha) | Hr]; [exists sg; split; [exact Hsg | exact Ha] | exact (@pa_relro_img _ _ PA a Hr)]).
    rewrite (KIMG3 a Hi Hno Herr2).
    exact (HROD a Hro Hno Herr2). }
  split.
  { unfold cn_regsat, cn_core, cn_s8. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; rewrite G3R by ro_in.
    - exact V2.
    - exact V8.
    - exact V9.
    - exact V18.
    - exact V27.
    - exact V24.
    - exact V19.
    - exact V20.
    - exact V21.
    - exact V23. }
  split.
  { unfold cn_slotsL in *.
    repeat (let H := fresh "Hsl" in apply Forall_cons_iff in HSL as [H HSL]; apply Forall_cons;
      [cbn [fst snd] in H |- *; rewrite <- H; apply rdword_ext; intros q Hq;
       apply KHI3; [unfold cn_sp0 in *; lia | unfold ASTACK; unfold cn_sp0 in *; lia] |]).
    apply Forall_nil. }
  (* ---- cn_early with the granted copy: rs = [res], own = 0 ---- *)
  pose proof L3 as L3c. apply prh_ledger_iff in L3c as [HG3 _].
  destruct HG3 as (_ & _ & _ & _ & _ & _ & HO3 & _).
  split; [|exact HHULL2].
  unfold cn_early. split; [exact HHp|].
  split; [exact L3|].
  split.
  { apply Forall_cons; [|apply Forall_nil]. right.
    split; [exact HinNB|]. split; [exact HresHp|].
    unfold src_rd. split.
    - intros j Hj. destruct (HSby j Hj) as [Hv Hr]. split; [|exact Hr].
      intros q Hq. etransitivity; [|exact (Hv q Hq)]. apply e2_mbyte_of_aview2.
      assert (Eq : q = 0%nat) by lia. subst q. cbn [Z.of_nat]. rewrite !Z.add_0_r.
      assert (Hj' : 0 <= Z.of_nat j < cn_size D) by (unfold cn_size; lia).
      rewrite (HKP3 (res + Z.of_nat j) ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite (CX (Z.of_nat j) Hj'). apply SRCK. lia.
    - split; [lia|]. split; [unfold cn_size in *; lia|].
      split; [apply AMR; unfold cn_size in *; lia|].
      destruct (Z.eq_dec (cn_size D) 0) as [E0 | E0].
      + split; [apply range_addressable_nil; unfold cn_size in *; lia | intros Hl; unfold cn_size in *; lia].
      + destruct (DSTH W2 mem3 mdE _ _ _ _ _ _ res (cn_size D) (ajx_ar (e_J0 B ARcfx _ _ _ _ _ _ _ _ HJE)) L3 ltac:(lia) ltac:(lia) ltac:(lia))
          as [RA3 HV3].
        unfold cn_size in RA3, HV3. split; [exact RA3 | intros _; exact HV3]. }
  split.
  { unfold cn_cblk. cbn [flat_map]. rewrite (proj2 (Z.eqb_neq res 0) Hnz). cbn [app]. rewrite Eab2.
    unfold cn_cblk in HPERM. cbn [flat_map app] in HPERM.
    apply Permutation_trans with (ablocks B (ci_ly D) (ci_S D) ++ [(res, cn_size D + 16)]).
    - apply Permutation_app_tail. exact HPERM.
    - apply Permutation_sym. apply Permutation_cons_append. }
  split; [exact HROOM2|].
  split.
  { unfold cn_prog, cn_cevsl, cn_cblk in *. cbn [flat_map] in *. rewrite (proj2 (Z.eqb_neq res 0) Hnz).
    cbn [map app flat_map] in *. unfold PresetReqAt.FUZZ_PAD.
    destruct HRP as [HRP1 HRP2]. split.
    - rewrite PresetReqAt.hlive_from_cons, PresetReqAt.hlive_from_nil. cbn [PresetReqAt.hstep].
      rewrite PresetReqAt.hlive_from_nil in HRP1.
      change (PresetRoom.rs_live (YGcfRoom.room_of_cf S2)) with (map snd (blocks S2)).
      change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)) in HRP1.
      assert (EM : map snd (blocks S2) = map snd (blocks S) ++ [cn_size D + 16]).
      { pose proof (f_equal (map snd) Eab2) as E. unfold ablocks in E. rewrite !map_app, !map_map in E.
        cbn [snd map] in E. exact E. }
      rewrite EM.
      apply Permutation_trans with (cn_size D + 16 :: map snd (blocks S));
        [apply Permutation_sym, Permutation_cons_append | apply perm_skip; exact HRP1].
    - intros sm x0 os i H0 hist Hpos Hrun.
      destruct (HRP2 sm x0 os i H0 hist Hpos ltac:(reflexivity)) as (hist' & Hpos').
      exists hist'. cbn [length]. rewrite Nat.add_0_r in Hpos'. rewrite Nat.add_1_r.
      apply (PresetRoomPosKeep.room_pos_keep_alloc SEGS B ly S Hp W regsT mem mdT ch1 sm x0 os i H0 hist'
        (cn_size D + 16) _ trc p S2 HPREcf ltac:(unfold cn_size in *; lia)
        ltac:(cbn [flat_map length] in HBUD; unfold cn_size in *; lia) HTRc Hpath
        (fun E => Hnz (proj1 Hpn E)) Hpos').
      apply (proj1 (prh_run_at_one sm x0 os i _)). exact Hrun. }
  split.
  { pose proof (blocks_bytes_bsum B ly2 S2) as EB2. pose proof (blocks_bytes_bsum B ly S) as EB.
    rewrite EB2, Eab2, bsum_app, <- EB. change (bsum [(res, cn_size D + 16)]) with (cn_size D + 16 + 0).
    cbn [length] in HBUD |- *. lia. }
  split; [left; reflexivity|].
  split; [rewrite (cni_own B IMG); exact (proj1 HO3)|].
  split; [intros _; apply Forall_cons; [exact Hnz | apply Forall_nil] | intros Hne; exfalso; exact (Hne eq_refl)]. }
(* +412 beqz s4 -> +432 (size = 0) / +416 *)
apply (cn_hs_beqz W2 fxk _ (ms_mem ms) _ _ 412 20%bv 20 432 416 (cn_size D =? 0));
  [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity | |].
{ rewrite ro_getr0, V20. apply ro_c_eq0. lia. }
intros X5.
destruct (Z.eqb_spec (cn_size D) 0) as [Hs0 | Hs0].
{ (* size = 0: no copy *)
  apply (TAIL (ms_regs ms) (ms_mem ms) _).
  - apply cn_J_of_x. exact (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X5
      (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X4 HJ2)).
  - exact HPM2.
  - intros r _. reflexivity.
  - intros a _ _ _. reflexivity.
  - intros i Hi. lia. }
(* +416 mv a0, s5; +420 mv a1, s7; +424 mv a2, s4; +428 jal __asan_memcpy *)
assert (Hs1 : 0 < cn_size D) by lia.
apply (cn_hs_addi W2 fxk _ (ms_mem ms) _ _ 416 420 10%bv 21%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X6.
apply (cn_hs_addi W2 fxk _ (ms_mem ms) _ _ 420 424 11%bv 23%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X7.
apply (cn_hs_addi W2 fxk _ (ms_mem ms) _ _ 424 428 12%bv 20%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X8.
apply (cn_hs_call W2 fxk _ (ms_mem ms) _ _ 428 432 AS___asan_memcpy); [vm_compute; reflexivity | lia | reflexivity |].
intros X9.
lazymatch goal with |- SRr _ _ (@cn_cfg _ _ _ ?rg _ ?mo) _ => set (regsC := rg); set (mdC := mo) end.
assert (C10 : getr regsC 10%bv = w64 res).
{ unfold regsC. ro_getr. rewrite V21, e2_addi by lia. rewrite Z.add_0_r. reflexivity. }
assert (C11 : getr regsC 11%bv = w64 (ci_data D)).
{ unfold regsC. ro_getr. rewrite V23, e2_addi by lia. rewrite Z.add_0_r. reflexivity. }
assert (C12 : getr regsC 12%bv = w64 (cn_size D)).
{ unfold regsC. ro_getr. rewrite V20, e2_addi by lia. rewrite Z.add_0_r. reflexivity. }
assert (CR1 : getr regsC 1%bv = w64 (cn_pc 432)) by (unfold regsC; ro_getr; reflexivity).
assert (CR3 : getr regsC 3%bv = w64 (as_gp B)) by (unfold regsC; ro_getr; rewrite V3; exact Hgp0).
assert (CR4 : getr regsC 4%bv = w64 (as_tp B)) by (unfold regsC; ro_getr; rewrite V4; exact Htp0).
assert (CSP : spZ regsC = cn_sp0 D + (cn_S1 D - cn_sp0 D)).
{ unfold spZ, regsC. ro_getr. rewrite V2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
pose proof (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X9
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X8
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X7
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X6
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X5
  (ajournal_x_materialize SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X4 HJ2))))))
  as HJC.
destruct (SRCH W2 (ms_mem ms) _ _ _ _ _ _ _ (ajx_ar HJC) L1 Hs1) as [SRA SHV].
destruct (DSTH W2 (ms_mem ms) _ _ _ _ _ _ _ res (cn_size D) (ajx_ar HJC) L1 Hs1 ltac:(lia) ltac:(lia)) as [DRA DHV].
unfold cn_cfg. unfold w64 at 1.
eapply SRr_bind.
{ apply (aj_intrin_at_xm (fx := fxk) (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) OCpy
    (SIGMA AS___asan_memcpy) (ACPY fxk)
    W2 regsC (ms_mem ms) STK_check_no_overread (cn_sp0 D) [] (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
    [(CN_CID, ci_fpos D)] ly2 S2 Hp mdC (k + (st_nev S2 - st_nev S)) res (ci_data D) (cn_size D)
    (cn_S1 D - cn_sp0 D) (w64 (cn_pc 432))).
  - exact HJC.
  - exact C10.
  - exact C11.
  - exact C12.
  - lia.
  - lia.
  - lia.
  - exact CSP.
  - exact HS1mod.
  - lia.
  - unfold ESTACK. rewrite HSTK. lia.
  - exact CR3.
  - exact CR4.
  - exact CR1.
  - unfold cn_pc. rewrite <- Z.add_assoc. apply ret_ok_codeptr_v; rewrite HOFF; [lia | reflexivity].
  - intros a Ha. apply AWR. lia.
  - apply AMR; lia.
  - exact DRA.
  - intros _. exact DHV.
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - rewrite (SRCK a Ha). apply (e2_garr8_some _ _ (ci_data D) (ci_x D) a HSby). unfold cn_size in Ha. exact Ha.
      - rewrite CSP. unfold cn_size in *. lia. }
    split; [exact (SRCD Hs1)|]. split; [exact HSam|]. split; [exact SRA | intros _; exact SHV]. }
cbv beta. intros W3 c3 Hwle3 (-> & regsP & memP & mdP & -> & HJP & HPRP & HP10 & HBYP & HKPP & HGRP & HMNP).
change (mkCfg (@YK11.mkst fxk regsP (w64 (cn_pc 432)) memP (YK11.seg_rom SEGS)) mdP)
  with (@cn_cfg SEGS fxk (cn_pc 432) regsP memP mdP).
apply (TAIL regsP memP mdP).
- apply cn_J_of_x. exact HJP.
- exact (PCALL _ _ HMNP HPM2).
- intros r Hr. cbn in Hr.
  repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- getr _ ?r = _ =>
       rewrite (e5_pres _ _ r HPRP ltac:(apply e5_cs; vm_compute; reflexivity)) end;
     unfold regsC; ro_getr; reflexivity |]).
  destruct Hr.
- intros a Ha Hn Hw. apply HKPP; [exact Ha | exact Hn | lia].
- intros i Hi. exact (HBYP i Hi).
Qed.

End e2.
