(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/TopxRelayFacts.v, with its module paths and module names changed; 519 of its 613 lines of code are new or changed and 71 lines of the source are left out. *)
(* Four Section hypotheses of ReplyBTop (image B = fuzz_reply.asan-ubsan, route R at R := wle' tfibsegs RZ_cf,
   MT := ReplyKfMeterB.MT_sec nsec_cf cf_kmax), each as a lemma whose statement is that hypothesis's text: RR_R,
   CNL_rm_R, CSHE_R, RIG_R.  Each is the route-R walk of its function at top_x's instance (B := TfibB, PST := [],
   ARx := top_x's ARX, RP := RP_cf, MMAX := fr_MMAX, RG := fr_RG, CTX_AFREE := K0's):
     RR_R      W_relay_remove.pb_relay_remove_xR
     CNL_rm_R  W_check_no_loss.pb_check_no_loss_rm_xR
     CSHE_R    W_check_shape_ends.pb_check_shape_ends_xR
     RIG_R     W_relay_instance_gone.pb_relay_instance_gone_xR
   with their callees at R where an R walk exists: gesture_model (W_gesture_model_g.pb_gesture_model_g_xR),
   gestures_end (W_gestures_end_top.pb_gestures_end_closed_xR), free and free(NULL) at R (CfRBridgeRulesFreeRhB's
   AFREE_x_kf_rh / AFREEN_x_kf_rh from the composed theorem's premise AF, as ReplyBTop closes AFREE_R).  Each walk
   premise no existing lemma closes is a Section hypothesis below, quantified over rc, fx as ReplyBTop's rows are: the
   ReplyBTop rows LP_R, DRAIN_R (verbatim), and LDROP_R, HP_x, GE_R (each named for the walk hypothesis it closes).
   The instance facts are top_x's own proofs, restated.
   rule 24: no function proved (instantiation of proved walks); proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf YGcfNames YCbqG YG0lawscf YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp YM05 YG0dcf YGcfRoomLive.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn YCeg YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn_cf YD1w_cf YD1w_cf_fp YD1w_cf_br.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTFIB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD1mcf YD1pcf ReplyTFIBBcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_top_x ReplyLSB ReplyRINVB.
(* the zify flag as this file's own proofs expect it, whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance YE2k.tfib_sink_head.
#[local] Existing Instance checksum_shape.

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyDriverCfB ReplyRINVB ReplyLSBo ReplyLSBDrainPre.
Import ReplyDriverCfB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyLS3B_inst ReplyB3LScap ReplyB3LScnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_G YD1u YD1ucf W_palib
  W_check_bounded W_check_shape_done W_check_no_loss_read ReplyRINVB_add W_rg_place W_relay_src_c ReplyRINVBHead
  ReplyRINVB_write ReplyRINVB_exit ReplyRINVB_gone ReplyRINVB_rm_a12 ReplyBTopLsiCnt ReplyBTopLsi ReplyB3TrPeakCnlW8.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKfMeterB ReplyLSBSec ReplyKfCB ReplyBTopLsiSec
  ReplyRINVB_rmsrc ReplyBTopRiRmRr ReplyBTopCntRm ReplyBTopCntDr TopX_LIT ReplyAllocTargetsB TopX_INTRIN_memcpy.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require TopxImageB2 TopxTLFB W_ERRL_x TopX_RELAY TopX_SNP TopX_CSE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyRINVB_gone_ls TopxEntry TopX_RT_B2 ReplyClosedB
  CfRBridgeRulesB CfRStrndup CfRBridgeRulesRhTopB CfRBridgeRulesFreeRhB W_frame_flag_cf ReplyInstFactsB YD1vcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRoomLive YGcfNames YGcfNsec YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost.

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx YG01cf YG05cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_frame W_frame_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0scf YG05cf YG0tcf YG08cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_relay_remove W_relay_instance_gone
  W_check_no_loss W_check_shape_ends W_cshe_epi TopxDrainLitB W_LLVMFuzzerTestOneInput_gone_inst W_sites W_relay_remove_cx W_next_line W_list_find W_list_drop W_gesture_model_g
  W_drain_cx_x W_drain_pb SnpNarrowSites TopX_RT3 TopX_RT4 TopX_MEMCPYS TopX_RT_lock TopxImageB TopxImageB2
  W_img_x AsmTopX W_contract_xR W_contract_xR_g6 W_contract_xR_g3 W_contract_xR_relayB W_contract_leaf_xR
  W_relay_instance_gone_cx ReplyKeptAroB YF0m.
(* the zify flag as this file's own proofs expect it, whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance YE2k.tfib_sink_head.
#[local] Existing Instance checksum_shape.
Local Notation RLV := (@room_live_cf CfParams_reply).
Local Notation NSEC := YGcfNames.nsec_cf.
Local Notation KMAX := (@YGcfNames.cf_kmax CfParams_reply).
Local Notation XS := (ReplyLSBSec.SEC_CALL ReplyKfCB.KF_KC).
Local Notation MT := (ReplyKfMeterB.MT_sec NSEC KMAX).
Local Notation LSs rc := (@ReplyLS3B_inst.LSI rc YD2l.TfibB ReplyLSBo.OUT_MAX4
  (fun cx t m ly S => @ReplyB3LScap.fr_CAP rc cx t m ly S /\ ReplyLSBSec.fr_SEC NSEC KMAX ReplyKfCB.KF_KC cx t m ly S)).
Local Notation RR rc := (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).

(* ================================================================ the instance's facts *)
Section facts.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation ARX := (@W_LLVMFuzzerTestOneInput_top_x.ARX rc).

Lemma rl_laws : AR_laws_x segs TfibB ARX (@cf_head CfParams_reply).
Proof. exact W_LLVMFuzzerTestOneInput_top_x.ARX_laws. Qed.
Lemma rl_hp0 : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md -> Hp = [].
Proof. exact W_LLVMFuzzerTestOneInput_top_x.ARX_hp0. Qed.
Lemma rl_HEV : as_errno TfibB = TFIB_ERRNO_B.
Proof. exact W_LLVMFuzzerTestOneInput_top_x.top_HEV. Qed.
Lemma rl_imgc : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Proof. exact (W_img_x.fr_img_cover_x TfibB ARX rl_laws). Qed.
(* a live cf block's size (top_x's BLKR) *)
Lemma rl_blkr : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
  0 <= n < 2 ^ 30.
Proof.
  intros ly S Hp W mem md p n H Hin.
  destruct (YG0dcf.alc_blocks _ _ (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB) ly S Hp W mem md p n (proj1 H) Hin)
    as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (YG08cf.cf_malloc_max_bound (cp := CfParams_reply)) as Hb. lia.
Qed.
Lemma rl_blkn : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
  0 <= n.
Proof. intros ly S Hp W mem md p n H Hin. exact (proj1 (rl_blkr ly S Hp W mem md p n H Hin)). Qed.
Lemma rl_ownlow : ARx_owned_low_law segs TfibB ARX.
Proof.
  intros ly S Hp W mem md a H Ho.
  exact (ARx_owned_low_law_cf_x (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)
    ly S Hp W mem md a (proj1 H) Ho).
Qed.
Lemma rl_wfl : ARx_wf_law segs ARX (Wf_cf (cp := CfParams_reply) (as_universe TfibB)).
Proof. intros ly S Hp W mem md H. exact (ARx_wf_law_cf_x (cp := CfParams_reply) segs TfibB ly S Hp W mem md (proj1 H)). Qed.
Lemma rl_smalloc : forall s cid, Wf_cf (cp := CfParams_reply) (as_universe TfibB) s -> 0 <= cid <= 10 ->
  count_cid cid (frames s) < fs_frames cid ->
  exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
  frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
Proof.
  intros s cid HWF Hcid Hcnt.
  destruct (stack_malloc_progress_cf (cp := CfParams_reply) _ s cid HWF Hcid Hcnt) as (pos & s' & Hpath).
  pose proof (stack_malloc_ok_cf (cp := CfParams_reply) _ s cid HWF Hcid) as HTOK.
  destruct (atok_apath _ _ _ [] (PFake cid pos, s') HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post_cf in HQ.
  destruct HQ as (_ & Hf & _ & _ & Hfrs & Hfresh).
  exists pos, s'. split; [exact Hpath|]. split; [exact Hf|]. split; [exact Hfrs | exact Hfresh].
Qed.
Lemma rl_sfree : forall s cid pos, Wf_cf (cp := CfParams_reply) (as_universe TfibB) s -> In (cid, pos) (frames s) ->
  exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Proof. intros s cid pos HWF Hin. exact (proj2 (stack_free_ok_cf (cp := CfParams_reply) _ s cid pos HWF Hin)). Qed.
Lemma rl_asf : astack_free_law_x segs TfibB ARX.
Proof.
  intros ly S Hp W mem md mem' md' cid pos H Hin HF HO HV Hvm Hlz He HK HKEPT.
  unfold W_LLVMFuzzerTestOneInput_top_x.ARX in H |- *.
  split; [|split; [exact (proj1 (proj2 H)) |
    exact (ReplyKeptAroB.arodata_kept_B mem mem' (proj2 (proj2 H)) HKEPT)]].
  exact (YG0tcf.astack_free_law_ok_cf (cp := CfParams_reply) segs TfibB ly S Hp W mem md mem' md' cid pos (proj1 H)
    Hin HF HO HV Hvm Hlz He HK).
Qed.
Lemma rl_ffl : frame_flag_lawP_x segs TfibB ARX.
Proof.
  exact (fun ly S Hp W mem md cid pos H => W_frame_flag_cf.frame_flag_lawP_x_ARX ly S Hp W mem md cid pos
    (conj (proj1 H) (proj1 (proj2 H)))).
Qed.
Lemma rl_frmf : forall ly S Hp (W : world segs) mem md cid pos, ARX ly S Hp W mem md -> In (cid, pos) (frames S) ->
  ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
Proof.
  intros ly S Hp W mem md cid pos [[M _] _] Hin.
  destruct (YG0scf.frame_facts_cf (cp := CfParams_reply) TfibB ly S Hp _ cid pos M Hin)
    as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & H64 & Hb & _).
  split; [exact Hpg|]. split; [exact Hoff|]. split; [exact H64 | exact Hb].
Qed.
Lemma rl_asm0 : astack_malloc_pres_x segs TfibB ARX 0.
Proof. exact AsmTopX.asm0_pres_ARX. Qed.
Lemma rl_asm1 : astack_malloc_pres_x segs TfibB ARX 1.
Proof. exact AsmTopX.asm1_pres_ARX. Qed.
Lemma rl_ro : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md ->
  @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem.
Proof. intros ly S Hp W mem md H. exact (proj2 (proj2 H)). Qed.
Lemma rl_pst_rom : forall a, in_rom segs a -> ~ Exists (in_zr a) ([] : list (Z * Z)).
Proof. intros a _ H. inversion H. Qed.
Lemma rl_pst_img : forall a, in_img segs a -> ~ Exists (in_zr a) ([] : list (Z * Z)).
Proof. intros a _ H. inversion H. Qed.

(* ---- gx_ok / gx_rt of a concrete list of ranges, decided (the image's segments, YF0m's owned statics and kept
   ranges, errno and the two shadow cells) ---- *)
Lemma rl_gx_ok_b : forall G, forallb (rng_all (segin segs)) G = true ->
  forallb (fun r => forallb (fun o => (fst o + snd o <=? fst r) || (fst r + snd r <=? fst o))
    YF0m.Tfib_owned_static) G = true ->
  forallb (fun r => forallb (fun o => (fst o + snd o <=? fst r) || (fst r + snd r <=? fst o))
    YF0m.Tfib_kept) G = true ->
  gx_ok segs TfibB G.
Proof.
  intros G Hi Ho Hk a Ha. split; [apply segin_ok; exact (rng_all_in _ G a Hi Ha)|].
  split.
  - rewrite (YF0m.ts_owned TfibB TfibB_syms). intros Hex.
    unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz). rewrite forallb_forall in Ho.
    exact (W_LLVMFuzzerTestOneInput_G.apart_of_b YF0m.Tfib_owned_static (fst r) (snd r) (Ho r Hr) a Hex Hz).
  - rewrite (YF0m.ts_kept TfibB TfibB_syms). intros Hex.
    unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz). rewrite forallb_forall in Hk.
    exact (W_LLVMFuzzerTestOneInput_G.apart_of_b YF0m.Tfib_kept (fst r) (snd r) (Hk r Hr) a Hex Hz).
Qed.
Lemma rl_gx_rt_b : forall G,
  forallb (fun r => (fst r + snd r <=? TFIB_ERRNO_B) || (TFIB_ERRNO_B + 4 <=? fst r)) G = true ->
  forallb (fun r => (fst r + snd r <=? VAL (A_OBJ 0)) || (VAL (A_OBJ 0) + 8 <=? fst r)) G = true ->
  forallb (fun r => (fst r + snd r <=? VAL (A_OBJ 30)) || (VAL (A_OBJ 30) + 8 <=? fst r)) G = true ->
  gx_rt (PI := PB_fr) TfibB G.
Proof.
  intros G He H0 H30 a Ha. rewrite rl_HEV.
  exact (conj (W_LLVMFuzzerTestOneInput_G.apart_of_b G _ _ He a Ha)
    (conj (W_LLVMFuzzerTestOneInput_G.apart_of_b G _ _ H0 a Ha) (W_LLVMFuzzerTestOneInput_G.apart_of_b G _ _ H30 a Ha))).
Qed.

(* ---- the read-only bytes: rom_out at G_fr_c (W_LLVMFuzzerTestOneInput_G.c_rom_out) and its parts ---- *)
Lemma rl_rom_out_c : rom_out segs TfibB (G_fr_c TfibB).
Proof. exact (W_LLVMFuzzerTestOneInput_G.c_rom_out TfibB TfibB_syms rl_HEV). Qed.
Lemma rl_ROMNS : forall a, in_rom segs a -> ~ (as_errno TfibB <= a < as_errno TfibB + 4) /\
  (Exists (in_zr a) (as_owned_static TfibB) -> rom_pinned segs TfibB a).
Proof. intros a Ha. destruct (rl_rom_out_c a Ha) as (_ & H2 & H3 & _). exact (conj H3 H2). Qed.

(* ---- check_no_loss's placement (W_check_no_loss Section rm) ---- *)
Lemma rl_cnl_HGR : gx_ok segs TfibB (cnl_ro (PI := PB_fr)).
Proof. apply rl_gx_ok_b; vm_compute; reflexivity. Qed.
Lemma rl_cnl_HGRR : gx_rt (PI := PB_fr) TfibB (cnl_ro (PI := PB_fr)).
Proof. apply rl_gx_rt_b; vm_compute; reflexivity. Qed.
Lemma rl_cnl_HRO : rom_out segs TfibB [(VAL A_g_s, 384)].
Proof.
  apply (W_drain_pb.rom_out_incl segs TfibB _ (G_fr_c TfibB)); [|exact rl_rom_out_c].
  intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr in Ha. cbn [fst snd] in Ha.
  apply (W_LLVMFuzzerTestOneInput_G.obj_c TfibB).
  exact (W_LLVMFuzzerTestOneInput_G.rng_cover (VAL A_g_s) 384 W_LLVMFuzzerTestOneInput_G.G_fr_obj
    ltac:(vm_compute; reflexivity) a Ha).
Qed.

(* ---- check_shape_ends' placement (W_check_shape_ends Section c) ---- *)
Lemma rl_cshe_HGR : gx_ok segs TfibB (W_cshe_epi.cshe_ro_B (PI := PB_fr)).
Proof. apply rl_gx_ok_b; vm_compute; reflexivity. Qed.
Lemma rl_cshe_HGRR : gx_rt (PI := PB_fr) TfibB (W_cshe_epi.cshe_ro_B (PI := PB_fr)).
Proof. apply rl_gx_rt_b; vm_compute; reflexivity. Qed.
Lemma rl_LCC : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md ->
  Forall (cell_holds TfibB ly (aview segs (w_H W) mem)) (as_const TfibB ly).
Proof. intros ly S Hp W mem md HAR. exact (alx_const_cells _ _ _ rl_laws ly S Hp W mem md HAR). Qed.
Lemma rl_LZS : forall ly S Hp (W : world segs) mem md r, ARX ly S Hp W mem md ->
  In r (YG0n.zero_shadow_ranges TfibB ly) -> zero_shadow (aview segs (w_H W) mem) SHADOW_OFF (fst r) (snd r).
Proof. intros ly S Hp W mem md r HAR Hr. exact (alx_zshadow _ _ _ rl_laws ly S Hp W mem md r HAR Hr). Qed.
Lemma rl_HEND5S : W_contract_x.ashp_x (PI := PB_fr) ARX (VAL A_lit_end5) 4.
Proof. apply (TopxImageB.tfib_shp_x TfibB TfibB_syms ARX rl_LCC rl_LZS). vm_compute. reflexivity. Qed.
Lemma rl_HGS : forall a, VAL (A_OBJ 19) <= a < VAL (A_OBJ 19) + 384 -> in_img segs a /\ ~ in_rom segs a /\
  ~ (VAL A_g_gone <= a < VAL A_g_gone + 1) /\ ~ (VAL A_g_nout <= a < VAL A_g_nout + 8) /\
  ~ (VAL A_g_out <= a < VAL A_g_out + 8).
Proof.
  intros a Ha.
  assert (Hg : inG (G_fr_c TfibB) a).
  { apply (W_LLVMFuzzerTestOneInput_G.obj_c TfibB).
    exact (W_LLVMFuzzerTestOneInput_G.rng_cover (VAL (A_OBJ 19)) 384 W_LLVMFuzzerTestOneInput_G.G_fr_obj
      ltac:(vm_compute; reflexivity) a Ha). }
  split; [exact (W_LLVMFuzzerTestOneInput_G.c_img TfibB rl_HEV a Hg)|].
  split; [intros Hr; exact (W_LLVMFuzzerTestOneInput_G.c_rom_apart TfibB rl_HEV a Hr Hg)|].
  let v := eval vm_compute in (VAL (A_OBJ 19)) in change (VAL (A_OBJ 19)) with v in Ha.
  repeat match goal with |- context [@pa_val ?T ?L PB_fr ?n] =>
    let v := eval vm_compute in (@pa_val T L PB_fr n) in change (@pa_val T L PB_fr n) with v end.
  repeat split; lia.
Qed.
(* ---- relay_remove's and relay_instance_gone's instance facts: TopxRelayFacts' lemmas and proofs, restated at top_x's
   ARX (TopxRelayFacts' own relation lacks top_x's arodata conjunct, so its three literal lemmas do not check against
   TopxDrainLitB.topx_dlit_ashp_b) ---- *)
Definition rl_rom_someb (lo n : Z) : bool :=
  forallb (fun j => match seg_rom frsegs (Z_to_bv 64 (lo + Z.of_nat j)) with Some _ => true | None => false end)
    (seq 0 (Z.to_nat n)).
Lemma rl_rom_someb_ok : forall lo n, rl_rom_someb lo n = true ->
  forall x, lo <= x < lo + n -> seg_rom frsegs (Z_to_bv 64 x) <> None.
Proof.
  intros lo n H x Hx. unfold rl_rom_someb in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (x - lo)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  replace (lo + (x - lo)) with x in H by lia.
  destruct (seg_rom frsegs (Z_to_bv 64 x)); [discriminate | discriminate H].
Qed.
Lemma rl_rom_tail_ok : forall base len,
  rl_rom_someb (base + len) (base + len - 1 - (base + len - 1) mod 8 + 8 - (base + len)) = true ->
  forall x, base + len <= x < base + len - 1 - (base + len - 1) mod 8 + 8 -> seg_rom frsegs (Z_to_bv 64 x) <> None.
Proof. intros base len H x Hx. apply (rl_rom_someb_ok _ _ H). lia. Qed.
Lemma rl_rr_Gin : forall a, inG (G_RR TfibB fr_RG) a -> inG (G_fr_c TfibB) a.
Proof.
  intros a Ha. unfold G_RR in Ha.
  apply inG_cons in Ha as [Ha|Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha;
    exact (W_LLVMFuzzerTestOneInput_G.c_HGlock TfibB a Ha)|].
  apply inG_cons in Ha as [Ha|Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha;
    exact (W_LLVMFuzzerTestOneInput_G.c_HGnsrc TfibB a Ha)|].
  exact (W_LLVMFuzzerTestOneInput_G.c_HG_DR TfibB a Ha).
Qed.
Lemma rl_rr_HG : gx_ok segs TfibB (G_RR TfibB fr_RG).
Proof. apply (W_drain_pb.gx_ok_incl _ _ _ _ rl_rr_Gin). exact W_LLVMFuzzerTestOneInput_top_x.GX_ok. Qed.
Lemma rl_rr_HROMO : rom_out segs TfibB (G_RR TfibB fr_RG).
Proof. exact (W_drain_pb.rom_out_incl _ _ _ _ rl_rr_Gin rl_rom_out_c). Qed.
Lemma rl_rig_HGRIG : gx_ok segs TfibB (G_RIG TfibB fr_RG).
Proof.
  apply (W_drain_pb.gx_ok_incl _ _ _ _ (W_LLVMFuzzerTestOneInput_gone_inst.gi_HG_RIG TfibB)).
  exact W_LLVMFuzzerTestOneInput_top_x.GX_ok.
Qed.
Lemma rl_rig_HROMO : rom_out segs TfibB (G_RIG TfibB fr_RG).
Proof. exact (W_drain_pb.rom_out_incl _ _ _ _ (W_LLVMFuzzerTestOneInput_gone_inst.gi_HG_RIG TfibB) rl_rom_out_c). Qed.
Lemma rl_HH53 : VAL (A_HI 53) = rg_nsrc fr_RG + W_relay_remove_cx.RR_HI_NSRC.
Proof. vm_compute. reflexivity. Qed.
Lemma rl_HH54 : VAL (A_HI 54) = rg_src fr_RG + W_relay_remove_cx.RR_HI_SRC.
Proof. vm_compute. reflexivity. Qed.
Lemma rl_HH41 : VAL (A_HI 41) = rg_nsrc fr_RG + W_relay_instance_gone_cx.RIG_HI_NSRC.
Proof. vm_compute. reflexivity. Qed.
Lemma rl_HH42 : VAL (A_HI 42) = rg_src fr_RG + W_relay_instance_gone_cx.RIG_HI_SRC.
Proof. vm_compute. reflexivity. Qed.
Lemma rl_HV8 : VAL (A_OBJ 8) = rg_wake fr_RG.
Proof. vm_compute. reflexivity. Qed.
Lemma rl_HWK : forall a, rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8 ->
  in_img segs a /\ ~ Exists (in_zr a) (as_owned_static TfibB) /\ ~ (as_errno TfibB <= a < as_errno TfibB + 4).
Proof.
  intros a Ha.
  pose proof (W_LLVMFuzzerTestOneInput_G.rng_cover (rg_wake fr_RG + 4) 4 W_LLVMFuzzerTestOneInput_G.G_fr_obj
    ltac:(vm_compute; reflexivity) a ltac:(lia)) as Ho.
  pose proof (W_LLVMFuzzerTestOneInput_G.obj_c TfibB a Ho) as Hg.
  split; [exact (W_LLVMFuzzerTestOneInput_G.c_img TfibB W_drain_pb.drain_HEV a Hg)|].
  split; [exact (W_drain_pb.drain_HOWN a Hg)|].
  exact (W_LLVMFuzzerTestOneInput_G.c_obj_noerr TfibB W_drain_pb.drain_HEV a Ho).
Qed.
Lemma rl_HERRS : forall a, as_errno TfibB <= a < as_errno TfibB + 4 -> ~ Exists (in_zr a) (as_owned_static TfibB).
Proof. intros a Ha. exact (W_drain_pb.drain_HOWN a (W_LLVMFuzzerTestOneInput_G.err_c TfibB a Ha)). Qed.
Lemma rl_HRGP : zpairwise_disjoint
[(rg_lock fr_RG, rg_lock fr_RG + 12); (rg_s fr_RG, rg_s fr_RG + 4 * ASRC); (rg_src fr_RG, rg_src fr_RG + 8);
 (rg_nsrc fr_RG, rg_nsrc fr_RG + 4); (rg_capsrc fr_RG, rg_capsrc fr_RG + 4);
 (rg_send_max fr_RG, rg_send_max fr_RG + 8); (rg_nout fr_RG, rg_nout fr_RG + 8);
 (rg_capout fr_RG, rg_capout fr_RG + 8); (rg_out fr_RG, rg_out fr_RG + 8); (rg_client fr_RG, rg_client fr_RG + 4);
 (rg_client_broken fr_RG, rg_client_broken fr_RG + 1); (rg_send_dead fr_RG, rg_send_dead fr_RG + 1);
 (rg_send_eintr fr_RG, rg_send_eintr fr_RG + 1); (rg_wake fr_RG + 4, rg_wake fr_RG + 8);
 (as_errno TfibB, as_errno TfibB + 4)].
Proof. apply W_drain_pb.zpairwise_disjb_ok. vm_compute. reflexivity. Qed.
Lemma rl_HRGI : forall a,
  (rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4 \/ rg_send_max fr_RG <= a < rg_send_max fr_RG + 8 \/
   rg_client fr_RG <= a < rg_client fr_RG + 4 \/ rg_send_dead fr_RG <= a < rg_send_dead fr_RG + 1) ->
  in_img segs a /\ ~ Exists (in_zr a) (as_owned_static TfibB).
Proof.
  intros a Ha.
  assert (Hg : inG (G_fr_c TfibB) a).
  { destruct Ha as [Ha | [Ha | [Ha | Ha]]].
    - exact (W_LLVMFuzzerTestOneInput_G.obj_c TfibB a (W_LLVMFuzzerTestOneInput_G.rng_cover (rg_capsrc fr_RG) 4
        W_LLVMFuzzerTestOneInput_G.G_fr_obj ltac:(vm_compute; reflexivity) a Ha)).
    - exact (W_LLVMFuzzerTestOneInput_G.c_HG_smax TfibB a Ha).
    - exact (W_LLVMFuzzerTestOneInput_G.c_HG_client TfibB a Ha).
    - exact (W_LLVMFuzzerTestOneInput_G.c_HG_sdead TfibB a Ha). }
  exact (conj (W_LLVMFuzzerTestOneInput_G.c_img TfibB W_drain_pb.drain_HEV a Hg) (W_drain_pb.drain_HOWN a Hg)).
Qed.
Lemma rl_HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom segs (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom segs (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
Proof.
  intros k Hk.
  destruct (TopxDrainLitB.dlit_romb_ok (VAL A_lit_end5) ([32; 101; 110; 100] ++ [0]) ltac:(vm_compute; reflexivity))
    as [Hb Hr].
  split.
  - apply Hr. change (Z.of_nat (length ([32; 101; 110; 100] ++ [0]))) with 5. lia.
  - transitivity (option_map (Z_to_bv 8) (nth_error ([32; 101; 110; 100] ++ [0]) k)).
    + exact (Hb k ltac:(cbn [length app]; lia)).
    + unfold END5. rewrite nth_error_map. reflexivity.
Qed.
Lemma rl_HCANR : forall a, W_sites.FR_GUARD <= a < W_sites.FR_GUARD + 8 -> seg_rom segs (Z_to_bv 64 a) <> None.
Proof. intros a Ha. exact (rl_rom_someb_ok W_sites.FR_GUARD 8 ltac:(vm_compute; reflexivity) a Ha). Qed.
Lemma rl_HLIT17 : W_relay_instance_gone_cx.glit_at_x (PI := PB_fr) ARX 17 (W_relay_instance_gone_cx.RIG_FMT ++ [0]).
Proof.
  unfold W_relay_instance_gone_cx.glit_at_x.
  destruct (TopxDrainLitB.dlit_romb_ok (VAL (A_OBJ 17)) (W_relay_instance_gone_cx.RIG_FMT ++ [0])
    ltac:(vm_compute; reflexivity)) as [Hb Hr].
  split; [exact Hb|]. split; [exact Hr|]. split.
  - apply TopxDrainLitB.topx_dlit_ashp_b. vm_compute. reflexivity.
  - exact (rl_rom_tail_ok (VAL (A_OBJ 17)) (Z.of_nat (length (W_relay_instance_gone_cx.RIG_FMT ++ [0])))
      ltac:(vm_compute; reflexivity)).
Qed.
Lemma rl_HLIT18 : W_relay_instance_gone_cx.glit_at_x (PI := PB_fr) ARX 18 (RelayModel.K_GESTURE ++ [0]).
Proof.
  unfold W_relay_instance_gone_cx.glit_at_x.
  destruct (TopxDrainLitB.dlit_romb_ok (VAL (A_OBJ 18)) (RelayModel.K_GESTURE ++ [0])
    ltac:(vm_compute; reflexivity)) as [Hb Hr].
  split; [exact Hb|]. split; [exact Hr|]. split.
  - apply TopxDrainLitB.topx_dlit_ashp_b. vm_compute. reflexivity.
  - exact (rl_rom_tail_ok (VAL (A_OBJ 18)) (Z.of_nat (length (RelayModel.K_GESTURE ++ [0])))
      ltac:(vm_compute; reflexivity)).
Qed.
Lemma rl_HLIT28 : W_relay_instance_gone_cx.glit_at_x (PI := PB_fr) ARX 28 ([32; 101; 110; 100] ++ [0]).
Proof.
  unfold W_relay_instance_gone_cx.glit_at_x.
  destruct (TopxDrainLitB.dlit_romb_ok (VAL (A_OBJ 28)) ([32; 101; 110; 100] ++ [0])
    ltac:(vm_compute; reflexivity)) as [Hb Hr].
  split; [exact Hb|]. split; [exact Hr|]. split.
  - apply TopxDrainLitB.topx_dlit_ashp_b. vm_compute. reflexivity.
  - exact (rl_rom_tail_ok (VAL (A_OBJ 28)) (Z.of_nat (length ([32; 101; 110; 100] ++ [0])))
      ltac:(vm_compute; reflexivity)).
Qed.
Lemma rl_HEND5R : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_rom segs a.
Proof.
  intros a Ha.
  destruct (rl_HEND5L (Z.to_nat (a - VAL A_lit_end5)) ltac:(lia)) as [Hr _].
  rewrite Z2Nat.id in Hr by lia. replace (VAL A_lit_end5 + (a - VAL A_lit_end5)) with a in Hr by lia. exact Hr.
Qed.
(* __asan_memcpy with d = s at top_x's relation: TopX_MEMCPYS.topx_AMEMCPYS (at ARX_rt) carried to the W1 relation as
   TopX_RT_lock's topx_ALOCK_W does (aentry_post_x_rtW; the write set is empty) *)
Lemma rl_AMEMCPYS : amemcpy_same_realizes_x TfibB ARX (@pa_sigma _ fr_prog_listing PB_fr WS_asan_memcpy).
Proof.
  intros ly S Hp W regs mem md d n HPRE H10 H11 H12 Hn Hd Hdn HDEST HSRC HCHK HROM HAM HNI.
  destruct (TopX_RT_lock.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
  eapply SRr_mono;
    [exact (TopX_MEMCPYS.topx_AMEMCPYS ly S Hp W regs mem md d n HPRE0 H10 H11 H12 Hn Hd Hdn HDEST HSRC HCHK HROM HAM
      HNI)|].
  intros W' c' _ HP.
  apply (TopX_RT_lock.aentry_post_x_rtW _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HPRE0) HQ); [| | intros a [] | exact HP].
  - destruct HPRE0 as (_ & _ & _ & Hlo & _). unfold ESTACK in Hlo. lia.
  - unfold ESTACK. lia.
Qed.
End facts.

(* ================================================================ the rows *)
Section brelay.
(* ---- the composed theorem's own premise (ReplyBTop's replyb_TFIB_B_T_composed takes it): the cf free realizer ---- *)
Context (AF : ReplyAllocTargetsB.afree_target_replyB).
(* ---- explicit premises: other ReplyBTop rows, verbatim ---- *)
Context (LP_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_xR.lp_spec_g_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf W_LLVMFuzzerTestOneInput_write.WR_MMAX (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_list_push)).
Context (DRAIN_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_xR.dr_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX fr_RG (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_drain)).
(* ---- explicit premises that are no ReplyBTop row (each named for its walk's Section hypothesis) ---- *)
(* has_prefix's strict contract at top_x's relation (check_shape_ends' HP) *)
Context (HP_x : forall (rc : YM05.RunCeil) (fx : YK11.FPState), W_contract_x.hp_spec_x (PI := @PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_has_prefix)).
(* gesture_end at R (relay_instance_gone's and gestures_end's GE_R) *)
Context (GE_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_xR.ge_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX fr_RG (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_gesture_end)).


(* free and free(NULL) at R from AF: ReplyBTop's AFREE_R closer (CfRBridgeRulesFreeRhB.AFREE_x_kf_rh) and its free(NULL)
   twin AFREEN_x_kf_rh, with ReplyBTop's discharge list *)
Lemma rl_AFREE_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_cf_rule_c_xR fx rc tfib_sink_head (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) MT CfRBridgeRulesB.RP_cf (@YG0dcf.arodata_ok_cf CfImg_B (@pa_segs rc fr_prog_listing (@PB_fr rc)) YD2l.TfibB) YCk0.CTX_AFREE (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
Proof.
  intros rc fx.
  first [ solve [eapply CfRBridgeRulesFreeRhB.AFREE_x_kf_rh; first [ exact (AF fx rc) | exact (ReplyClosedB.reply_amalloc_target_B fx rc) | exact (ReplyClosedB.reply_astrndup_cf_B_all fx rc) | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB) | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env | exact YGcfNsec.nsec_malloc_cf | exact YGcfNsec.nsec_free_cf | exact ReplyRelroGeoB.relro_seg_reply_B | exact (YD1vcf.aro_errno TfibB TfibB_syms ReplyDriverCfB.relro_ok_B) | exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX) | (intros; reflexivity) | (intros; apply iff_refl) | assumption ]]
        | solve [unshelve eapply CfRBridgeRulesFreeRhB.AFREE_x_kf_rh; first [ exact (AF fx rc) | exact (ReplyClosedB.reply_amalloc_target_B fx rc) | exact (ReplyClosedB.reply_astrndup_cf_B_all fx rc) | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB) | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env | exact YGcfNsec.nsec_malloc_cf | exact YGcfNsec.nsec_free_cf | exact ReplyRelroGeoB.relro_seg_reply_B | exact (YD1vcf.aro_errno TfibB TfibB_syms ReplyDriverCfB.relro_ok_B) | exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX) | (intros; reflexivity) | (intros; apply iff_refl) | assumption ]] ].
Qed.
Lemma rl_AFREEN_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_null_cf_rule_c_xR fx rc tfib_sink_head (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) MT CfRBridgeRulesB.RP_cf (@YG0dcf.arodata_ok_cf CfImg_B (@pa_segs rc fr_prog_listing (@PB_fr rc)) YD2l.TfibB) YCk0.CTX_AFREE (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
Proof.
  intros rc fx.
  first [ solve [eapply CfRBridgeRulesFreeRhB.AFREEN_x_kf_rh; first [ exact (AF fx rc) | exact (ReplyClosedB.reply_amalloc_target_B fx rc) | exact (ReplyClosedB.reply_astrndup_cf_B_all fx rc) | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB) | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env | exact YGcfNsec.nsec_malloc_cf | exact YGcfNsec.nsec_free_cf | exact ReplyRelroGeoB.relro_seg_reply_B | exact (YD1vcf.aro_errno TfibB TfibB_syms ReplyDriverCfB.relro_ok_B) | exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX) | (intros; reflexivity) | (intros; apply iff_refl) | assumption ]]
        | solve [unshelve eapply CfRBridgeRulesFreeRhB.AFREEN_x_kf_rh; first [ exact (AF fx rc) | exact (ReplyClosedB.reply_amalloc_target_B fx rc) | exact (ReplyClosedB.reply_astrndup_cf_B_all fx rc) | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB) | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env | exact YGcfNsec.nsec_malloc_cf | exact YGcfNsec.nsec_free_cf | exact ReplyRelroGeoB.relro_seg_reply_B | exact (YD1vcf.aro_errno TfibB TfibB_syms ReplyDriverCfB.relro_ok_B) | exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX) | (intros; reflexivity) | (intros; apply iff_refl) | assumption ]] ].
Qed.

(* the section premises and instance facts every walk below takes, in the proof context *)
Ltac rl_pose :=
  pose proof rl_laws as LAWS; pose proof rl_hp0 as HP0; pose proof rl_imgc as IMGC;
  pose proof rl_blkn as BLKN; pose proof rl_ownlow as OWNLOW; pose proof rl_wfl as WFL;
  pose proof rl_smalloc as SMALLOC; pose proof rl_sfree as SFREE; pose proof rl_asf as ASF;
  pose proof rl_ffl as FFL; pose proof rl_frmf as FRMF; pose proof rl_ro as RO_ARx;
  pose proof rl_pst_rom as PSTR; pose proof rl_pst_img as HPST; pose proof rl_HEV as HEV;
  pose proof W_palib.pb_palib_tfib as TL; pose proof TopxTLFB.topx_TLF_B as TLF;
  pose proof (ReplyKfMeterB.MT_sec_laws NSEC KMAX) as MLAW;
  pose proof (fun s f => ReplyKfMeterB.MT_sec_set_fs NSEC KMAX (fun f0 s0 => eq_refl) f s) as MO_FR.
Ltac rl_poseR rc :=
  pose proof (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc)) as R_refl;
  pose proof (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc)) as R_trans;
  pose proof (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) as WLE_R.

(* list_drop at R at every G' with list_drop's own conditions (W_check_shape_ends' LDROP_R, W_list_drop Section d's
   ROMS form); its rom_out form, which check_no_loss and gesture_model take, follows below *)
Context (LDROP_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (G' : list (Z * Z)),
  gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G' -> gx_rt (PI := @PB_fr rc) TfibB G' ->
  (forall a, in_rom (@pa_segs rc fr_prog_listing (@PB_fr rc)) a ->
    (Exists (in_zr a) (as_owned_static TfibB) -> rom_pinned (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB a) /\
    ~ (as_errno TfibB <= a < as_errno TfibB + 4) /\ ~ inG G' a) ->
  @W_contract_xR_g3.ldrop_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf G'
    (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_list_drop)).

(* gesture_model at R (W_gesture_model_g.pb_gesture_model_g_xR) at top_x's relation: list_push at R is the
   LP_R row (its WR_MMAX is fr_MMAX's value), list_drop at R the lemma above (rom_out gives its conditions), list_find
   W_list_find.pb_list_find_x, bcmp TopX_CSE.topx_ABCMP_W, the three literals' shadow by TopxImageB.tfib_shp_x *)
Lemma rl_GM_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @W_contract_xR_g6.gm_spec_g_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX
    (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_gesture_model).
Proof.
  intros rc fx. rl_pose. rl_poseR rc.
  assert (ABCMP : abcmp_realizes_x (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_sigma rc fr_prog_listing (@PB_fr rc) WS_bcmp)) by exact TopX_CSE.topx_ABCMP_W.
  assert (HLITG : W_contract_x.ashp_x (PI := @PB_fr rc) (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_val rc fr_prog_listing (@PB_fr rc) A_lit_gesture) 13)
    by (apply (TopxImageB.tfib_shp_x TfibB TfibB_syms _ rl_LCC rl_LZS); vm_compute; reflexivity).
  assert (HLITB : W_contract_x.ashp_x (PI := @PB_fr rc) (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_val rc fr_prog_listing (@PB_fr rc) A_lit_begin) 5)
    by (apply (TopxImageB.tfib_shp_x TfibB TfibB_syms _ rl_LCC rl_LZS); vm_compute; reflexivity).
  assert (HLITE : W_contract_x.ashp_x (PI := @PB_fr rc) (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end) 3)
    by (apply (TopxImageB.tfib_shp_x TfibB TfibB_syms _ rl_LCC rl_LZS); vm_compute; reflexivity).
  assert (LFIND_G : W_contract_x.lfind_spec_g_x (PI := @PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_list_find)).
  { intros G0 _ _. eapply W_list_find.pb_list_find_x; eassumption. }
  assert (EW : W_LLVMFuzzerTestOneInput_write.WR_MMAX = fr_MMAX) by (vm_compute; reflexivity).
  pose proof (LP_R rc fx) as LPUSH_G_R. rewrite EW in LPUSH_G_R.
  assert (LDROP_RO_R : forall G0, gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G0 ->
    gx_rt (PI := @PB_fr rc) TfibB G0 -> rom_out (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G0 ->
    @W_contract_xR_g3.ldrop_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
      (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf G0
      (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_list_drop)).
  { intros G0 H1 H2 H3. apply (LDROP_R rc fx G0 H1 H2).
    intros a Ha. destruct (H3 a Ha) as (Hn & Hp & He & _). exact (conj Hp (conj He Hn)). }
  eapply W_gesture_model_g.pb_gesture_model_g_xR; eassumption.
Qed.

(* ---------------------------------------------------------------- CNL_rm_R *)
(* W_check_no_loss.pb_check_no_loss_rm_xR (Section rm, wR) at top_x's instance: gesture_model and list_drop
   at R (above); next_line W_next_line.pb_next_line_x; the placement facts above *)
Lemma btr_CNL_rm_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), ∀ G : list (Z * Z), gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G → @W_contract_xR_g6.cnl_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf G fr_MMAX (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_check_no_loss).
Proof.
  intros rc fx G HG. rl_pose. rl_poseR rc.
  assert (ABCMP : abcmp_realizes_x (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_sigma rc fr_prog_listing (@PB_fr rc) WS_bcmp)) by exact TopX_CSE.topx_ABCMP_W.
  pose proof W_next_line.nl_objs_apart_fr as NLAP. pose proof W_next_line.nl_crom_fr as HCROM.
  assert (AMEMCHR : W_next_line.amemchr_realizesM_x (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB
    (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) 0x10350 0x10370 (@pa_sigma rc fr_prog_listing (@PB_fr rc) WS_memchr))
    by exact TopX_RT3.topx_AMEMCHR_W.
  assert (NL : W_contract_x.nl_spec_x (PI := @PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_next_line))
    by (eapply W_next_line.pb_next_line_x; eassumption).
  pose proof W_check_no_loss.cnl_objs_apart_fr as CNLAP.
  pose proof rl_cnl_HGR as HGR. pose proof rl_cnl_HGRR as HGRR. pose proof rl_ROMNS as ROMNS.
  pose proof rl_cnl_HRO as HRO.
  pose proof (rl_GM_R rc fx) as GM_R.
  assert (LDROP_RO_R : forall G0, gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G0 ->
    gx_rt (PI := @PB_fr rc) TfibB G0 -> rom_out (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G0 ->
    @W_contract_xR_g3.ldrop_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
      (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf G0
      (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_list_drop)).
  { intros G0 H1 H2 H3. apply (LDROP_R rc fx G0 H1 H2).
    intros a Ha. destruct (H3 a Ha) as (Hn & Hp & He & _). exact (conj Hp (conj He Hn)). }
  eapply W_check_no_loss.pb_check_no_loss_rm_xR; eassumption.
Qed.

(* ---------------------------------------------------------------- CSHE_R *)
(* W_check_shape_ends.pb_check_shape_ends_xR (Section c, wR) at top_x's instance, at every gx_ok G: list_drop
   at R (above), has_prefix's strict contract (HP_x), next_line / list_find / bcmp strict, the placement facts above *)
Lemma btr_CSHE_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), ∀ G : list (Z * Z), gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB G → @W_contract_xR_g6.cshe_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf G (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_check_shape_ends).
Proof.
  intros rc fx G HG. rl_pose. rl_poseR rc.
  assert (ABCMP : abcmp_realizes_x (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_sigma rc fr_prog_listing (@PB_fr rc) WS_bcmp)) by exact TopX_CSE.topx_ABCMP_W.
  pose proof W_next_line.nl_objs_apart_fr as NLAP. pose proof W_next_line.nl_crom_fr as HCROM.
  assert (AMEMCHR : W_next_line.amemchr_realizesM_x (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB
    (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) 0x10350 0x10370 (@pa_sigma rc fr_prog_listing (@PB_fr rc) WS_memchr))
    by exact TopX_RT3.topx_AMEMCHR_W.
  assert (NL : W_contract_x.nl_spec_x (PI := @PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_next_line))
    by (eapply W_next_line.pb_next_line_x; eassumption).
  assert (LFIND : W_contract_x.lfind_spec_x (PI := @PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) G
    (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_list_find)) by (eapply W_list_find.pb_list_find_x; eassumption).
  pose proof (HP_x rc fx) as HP.
  pose proof (LDROP_R rc fx) as LDROP_R'.
  pose proof rl_cshe_HGR as HGR. pose proof rl_cshe_HGRR as HGRR. pose proof rl_ROMNS as ROMNS.
  pose proof rl_HEND5R as HEND5R. pose proof rl_HEND5S as HEND5S. pose proof rl_HGS as HGS.
  eapply W_check_shape_ends.pb_check_shape_ends_xR; eassumption.
Qed.

(* gestures_end at R (W_gestures_end_top.pb_gestures_end_closed_xR) at top_x's instance, from GE_R, AFREE_R,
   AFREEN_R and the facts top_x's strict GSE_x block proves (its proofs, here at R) *)
Lemma rl_GSE_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @W_contract_xR.gse_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX fr_RG
    (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_gestures_end).
Proof.
  intros rc fx. rl_pose. rl_poseR rc.
  pose proof (GE_R rc fx) as GE_R'. pose proof (rl_AFREE_R rc fx) as AFREE_R'. pose proof (rl_AFREEN_R rc fx) as AFREEN_R'.
  assert (HG0 : gx_ok (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB (G_SL TfibB fr_RG)).
  { apply (W_journal.gx_ok_sub _ TfibB _ (G_fr_c TfibB)); [exact (W_LLVMFuzzerTestOneInput_G.c_HG_SL TfibB) |
      exact W_LLVMFuzzerTestOneInput_top_x.GX_ok]. }
  assert (HROMO0 : rom_out (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB (G_SL TfibB fr_RG)).
  { intros a Ha. destruct (rl_rom_out_c a Ha) as (H1 & H2 & H3 & H4).
    split; [intros HGa; exact (H1 (W_LLVMFuzzerTestOneInput_G.c_HG_SL TfibB a HGa))|]. exact (conj H2 (conj H3 H4)). }
  assert (HEND5P : forall a, @pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5 <= a <
    @pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5 + 5 -> ~ Exists (in_zr a) (@nil (Z * Z)))
    by (intros a _ H; inversion H).
  assert (HCL : In [@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_gestures_end + 0x114] YCk0.CTX_AFREE)
    by (vm_compute; repeat (first [left; reflexivity | right])).
  assert (HCT : In [@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_gestures_end + 0x150] YCk0.CTX_AFREE)
    by (vm_compute; repeat (first [left; reflexivity | right])).
  assert (HEND5I0 : forall a, @pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5 <= a <
    @pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5 + 5 -> in_img (@pa_segs rc fr_prog_listing (@PB_fr rc)) a).
  { intros a Ha. change (@pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5) with 134912 in Ha. apply segin_ok.
    assert (E : a = 134912 \/ a = 134913 \/ a = 134914 \/ a = 134915 \/ a = 134916) by lia.
    destruct E as [E|[E|[E|[E|E]]]]; subst a; vm_compute; reflexivity. }
  assert (HEND5G0 : forall a, @pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5 <= a <
    @pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5 + 5 ->
    ~ inG (G_SL TfibB fr_RG) a /\ ~ Exists (in_zr a) (as_owned_static TfibB) /\
    ~ (as_errno TfibB <= a < as_errno TfibB + 4)).
  { intros a Ha. change (@pa_val rc fr_prog_listing (@PB_fr rc) A_lit_end5) with 134912 in Ha.
    split; [|split].
    - intros H. apply (W_LLVMFuzzerTestOneInput_G.c_HG_SL TfibB) in H.
      rewrite (W_LLVMFuzzerTestOneInput_G.G_fr_c_val TfibB rl_HEV) in H.
      exact (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok 134912 5
        (W_LLVMFuzzerTestOneInput_G.G_fr_obj ++ [(TFIB_ERRNO_B, 4)]) ltac:(vm_compute; reflexivity) a H Ha).
    - rewrite (YF0m.ts_owned TfibB TfibB_syms). intros H.
      exact (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok 134912 5 YF0m.Tfib_owned_static ltac:(vm_compute; reflexivity)
        a H Ha).
    - rewrite rl_HEV. intros He.
      apply (W_LLVMFuzzerTestOneInput_top_x.top_apart_ok 134912 5 [(TFIB_ERRNO_B, 4)] ltac:(vm_compute; reflexivity) a);
        [|exact Ha].
      apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact He. }
  assert (HOUTG0 : forall r a, In r (aout_fp TfibB fr_RG 0 0) -> fst r <= a < snd r ->
    ~ (as_errno TfibB <= a < as_errno TfibB + 4) ->
    in_img (@pa_segs rc fr_prog_listing (@PB_fr rc)) a /\ ~ in_rom (@pa_segs rc fr_prog_listing (@PB_fr rc)) a /\
    ~ Exists (in_zr a) (as_owned_static TfibB)).
  { intros r a Hin Ha Hne.
    assert (HGa : inG (G_fr_c TfibB) a).
    { unfold aout_fp in Hin. cbn [In] in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; subst r; cbn [fst snd] in Ha;
        first [ match type of Ha with ?lo <= _ < ?hi =>
                  apply (W_LLVMFuzzerTestOneInput_G.obj_c TfibB);
                  apply (W_LLVMFuzzerTestOneInput_G.rng_cover lo (hi - lo) W_LLVMFuzzerTestOneInput_G.G_fr_obj);
                  [vm_compute; reflexivity | lia] end
              | exfalso; apply Hne; lia ]. }
    split; [|split].
    - exact (W_LLVMFuzzerTestOneInput_G.c_img TfibB rl_HEV a HGa).
    - intros Hr. exact (W_LLVMFuzzerTestOneInput_G.c_rom_apart TfibB rl_HEV a Hr HGa).
    - exact (W_LLVMFuzzerTestOneInput_top_x.top_HOWN a HGa). }
  eapply W_gestures_end_top.pb_gestures_end_closed_xR with (CTX_AFREE := YCk0.CTX_AFREE); eassumption.
Qed.

(* ---------------------------------------------------------------- RR_R *)
(* W_relay_remove.pb_relay_remove_xR (Section c, wR) at top_x's instance: drain at R (DRAIN_R), gestures_end
   at R (above), free / free(NULL) at R (AFREE_R / AFREEN_R), wake's and the relay's facts above *)
Lemma btr_RR_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_xR_relayB.rr_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX fr_RG YCk0.CTX_AFREE (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_relay_remove).
Proof.
  intros rc fx. rl_pose. rl_poseR rc.
  pose proof rl_asm0 as ASMP.
  pose proof (rl_AFREE_R rc fx) as AFREE_R'. pose proof (rl_AFREEN_R rc fx) as AFREEN_R'. pose proof (DRAIN_R rc fx) as DRAIN_R'.
  pose proof (rl_GSE_R rc fx) as GSE_R.
  pose proof rl_rr_HG as HG. pose proof rl_rr_HROMO as HROMO.
  pose proof rl_HH53 as HH53. pose proof rl_HH54 as HH54.
  pose proof rl_HV8 as HV8. pose proof rl_HWK as HWK.
  pose proof rl_HERRS as HERRS. pose proof rl_HRGP as HRGP.
  pose proof rl_HRGI as HRGI. pose proof rl_HEND5L as HEND5L.
  assert (ALOCK : alock_realizes_x (PI := @PB_fr rc) TfibB (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_sigma rc fr_prog_listing (@PB_fr rc) WS_pthread_mutex_lock)) by exact TopX_RT_lock.topx_ALOCK_W.
  assert (AUNLOCK : aunlock_realizes_x (PI := @PB_fr rc) TfibB (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_sigma rc fr_prog_listing (@PB_fr rc) WS_pthread_mutex_unlock)) by exact TopX_RT_lock.topx_AUNLOCK_W.
  assert (AMEMCPY : aintrin_realizes_x (@pa_segs rc fr_prog_listing (@PB_fr rc)) TfibB (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    OCpy (@pa_sigma rc fr_prog_listing (@PB_fr rc) WS_asan_memcpy)) by exact TopX_INTRIN_memcpy.topx_AMEMCPY_W.
  pose proof rl_AMEMCPYS as AMEMCPYS.
  assert (PSTG : forall a, Exists (fun r => fst r <= a < snd r) (W_relay_remove_cx.rr_gcells TfibB fr_RG) ->
    ~ Exists (in_zr a) (@nil (Z * Z))) by (intros a _ H; inversion H).
  eapply W_relay_remove.pb_relay_remove_xR; eassumption.
Qed.

(* ---------------------------------------------------------------- RIG_R *)
(* W_relay_instance_gone.pb_relay_instance_gone_xR (Section c, wR) at top_x's instance: drain at R
   (DRAIN_R), gesture_end at R (GE_R), free at R (AFREE_R), the runtime rows TopX_RT_lock / TopX_SNP / TopX_RT_B2 /
   TopX_RT4, the relay's facts above *)
Lemma btr_RIG_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_xR_relayB.rig_spec_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf fr_MMAX fr_RG YCk0.CTX_AFREE (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_relay_instance_gone).
Proof.
  intros rc fx. rl_pose. rl_poseR rc.
  pose proof rl_asm1 as ASMP.
  pose proof (rl_AFREE_R rc fx) as AFREE_R'. pose proof (DRAIN_R rc fx) as DRAIN_R'. pose proof (GE_R rc fx) as GE_R'.
  pose proof rl_rig_HGRIG as HGRIG. pose proof rl_rig_HROMO as HROMO.
  pose proof rl_HH41 as HH41. pose proof rl_HH42 as HH42.
  pose proof rl_HRGP as HRGP. pose proof rl_HRGI as HRGI.
  pose proof rl_HEND5L as HEND5L. pose proof rl_HCANR as HCANR.
  pose proof rl_HLIT17 as HLIT17.
  pose proof rl_HLIT18 as HLIT18.
  pose proof rl_HLIT28 as HLIT28.
  pose proof SnpNarrowSites.HLITGOT_PB_fr as HLITGOT.
  pose proof (W_drain_cx_x.alloc_tail_x _ TfibB _ LAWS) as ALLOC_TAIL.
  pose proof TopxImageB2.topx_HGOTG_x_B as HGOTG.
  assert (ALOCK : alock_realizes_x (PI := @PB_fr rc) TfibB (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_sigma rc fr_prog_listing (@PB_fr rc) WS_pthread_mutex_lock)) by exact TopX_RT_lock.topx_ALOCK_W.
  assert (AUNLOCK : aunlock_realizes_x (PI := @PB_fr rc) TfibB (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_sigma rc fr_prog_listing (@PB_fr rc) WS_pthread_mutex_unlock)) by exact TopX_RT_lock.topx_AUNLOCK_W.
  assert (ASNPRINTF : asnprintf_realizes_x (PI := @PB_fr rc) TfibB (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_sigma rc fr_prog_listing (@PB_fr rc) WS_snprintf) W_sites.FR_GOT_GUARD W_sites.FR_GUARD)
    by exact TopX_SNP.topx_SNP_W.
  assert (ASTRLEN : astrlen_realizes_x (PI := @PB_fr rc) TfibB (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_sigma rc fr_prog_listing (@PB_fr rc) WS_strlen)) by exact TopX_RT_B2.topx_ASTRLEN_B_W.
  assert (ASTRNCMP : astrncmp_realizes_x (PI := @PB_fr rc) TfibB (@W_LLVMFuzzerTestOneInput_top_x.ARX rc)
    (@pa_sigma rc fr_prog_listing (@PB_fr rc) WS_strncmp)) by exact TopX_RT4.topx_ASTRNCMP_W.
  assert (PSTG : forall a,
    (inG (G_RIG TfibB fr_RG) a \/ rg_src fr_RG <= a < rg_src fr_RG + 8 \/ rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 \/
     rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4 \/ rg_send_max fr_RG <= a < rg_send_max fr_RG + 8 \/
     rg_client fr_RG <= a < rg_client fr_RG + 4 \/ rg_send_dead fr_RG <= a < rg_send_dead fr_RG + 1) ->
    ~ Exists (in_zr a) (@nil (Z * Z))) by (intros a _ H; inversion H).
  eapply W_relay_instance_gone.pb_relay_instance_gone_xR; eassumption.
Qed.
End brelay.
