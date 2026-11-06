(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (G-BRA, B top_x row 21 RA_x): the B top's RA_x at its cf instance.

   fr_relay_add_x is the B top's RA_x (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:220, with the room record RP after MT as
   the room kit's ra_spec_g_x states it, lib/B/W_contract_x.v Section w5g) at B := TfibB, PST := [], ARx := ARX_ra
   (top_x.v:154-155's ARX, the same body), RG := fr_globals, CTX := YCk0.CTX_AREALLOC, from lib/B/W_relay_add_x.v's
   pb_relay_add_x.  Its Section hypotheses are top_x's own texts (TL, TLF, MLAW, FFL, HRO, ALOCK, AUNLOCK, the realloc
   rule at a ceiling MMAX with ATABLE < MMAX), the meter law MO_FR, and two callee laws of the instance the top did not
   state: AMEMSET_x (the memset intrinsic at ARX) and ASM0 (__asan_stack_malloc_0, for wake's class-0 fake frame at
   0x824d0).  Every other walk premise is discharged here: the cf laws as top_x.v:610-648 derives them, wake by
   lib/B/W_wake_x.v pb_wake_x, the placement facts by lib/B/W_relay_add_cut.v Section fr / W_wake_x.v wk_hv8_fr, and
   the image facts by computation at TfibB.  It holds at any meter MT with MLAW and MO_FR (top_x's meter Variable). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_relay_add_fr_x.v, with its module paths and module names changed; 178 of its 229 lines of code are new or changed and 120 lines of the source are left out. *)
(* ReplyBTop's row OA_R (op_add's contract at route R, at the top's instance) as a lemma.
   btr_OA_R's statement is the row's Context type in ReplyBTop, for every rc and fx.  Its proof instantiates the proved
   route-R walk W_op_add.pb_op_add_g_xR at the instance (PI := PB_fr, B := TfibB, PST := [], ARx := top_x's ARX,
   R := wle' tfibsegs RZ_cf, MT := MT_sec nsec_cf cf_kmax, RP := RP_cf) and discharges its premises:
   - R's laws: YA0nH.wle'_refl / wle'_trans / wle_wle';
   - RO := arodata_ok_cf, RO_ARx: ARX's last conjunct; the laws ARX_laws, PALib, the meter laws MT_sec_laws, rp_RMM;
   - the placement facts HGS / HNFD / HHI87 / HOAD, the two caller contexts at YCk0's tables and MMAX: as top_x's
     strict OA proof decides them; HWK / HERRS (op_add's, relay_add's and wake's): g_wake[1] and errno are bytes of
     G_fr_c (W_LLVMFuzzerTestOneInput_G's rng_cover / err_c), so image bytes, not owned, and g_wake[1] is not errno;
   - malloc at R: CfRBridgeRulesRhTopB.AMA_x_kf_rh over ReplyClosedB.reply_amalloc_target_B (as ReplyBTop closes its
     AMALLOC_R obligation);
   - relay_add at R: the proved walk W_relay_add_x.pb_relay_add_xR at the same instance, with realloc at R by
     CfRBridgeRulesRhTopB.ARE_x_kf_rh over ReplyAreallocTargetB's two realizers, the hull admission by
     ReplyHullAdm.hull_adm_of_mo_reply, wake by W_wake_x.pb_wake_x, the mutex contracts TopX_RT_lock.topx_ALOCK_W /
     topx_AUNLOCK_W, __asan_memset by btr_oa_AMEMSET_W below, and its placement facts by W_relay_add_cut's Section fr;
   - source_reset at R: the row SR_R of ReplyBTop, kept as this Section's one Context (no closed instance of
     W_source_reset's R walk at the top's instance is in the tree).
   btr_oa_AMEMSET_W lifts TopX_INTRIN_memset.topx_AMEMSET_x (proved at ARX_rt) to top_x's ARX (ARX_rt with arodata_ok_cf
   on the memory), as TopX_RT_lock lifts its mutex contracts: the write set holds no kept byte (the rule's premise) and
   the stack window lies above the image, so TopX_RT_lock.aro_keep_view keeps arodata_ok_cf.
   proves no function (kind: segment lemma). *)
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
(* the frame and site kit the relay_add instance facts name (top_x's own imports for them) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx YG01cf YG05cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_frame W_frame_x W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0tcf YGcfNsec YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyLSBo ReplyLS3B_inst ReplyB3LScap ReplyLSBSec
  ReplyKfMeterB ReplyKfCB CfRBridgeRulesB CfRBridgeRulesRhTopB ReplyClosedB ReplyInstFactsB YD1vcf ReplyDriverCfB
  YGcfRehidePost W_frame_flag_cf W_palib TopxTLFB YD25cf ReplyRelroGeoB ReplyKeptAroB YCk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_op_add W_contract_srlf_xR W_relay_add_cut
  W_relay_add_x W_wake_x W_img_x TopX_RT_lock TopX_INTRIN_memset AsmTopXEq ReplyAreallocTargetB W_drain_pb.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyHullAdm.
(* the zify flag as this file's own proofs expect it, whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Existing Instance YE2k.tfib_sink_head.
#[local] Existing Instance checksum_shape.

(* ReplyBTop's notations, verbatim *)
Local Notation RLV := (@room_live_cf CfParams_reply).
Local Notation NSEC := YGcfNames.nsec_cf.
Local Notation KMAX := (@YGcfNames.cf_kmax CfParams_reply).
Local Notation XS := (ReplyLSBSec.SEC_CALL ReplyKfCB.KF_KC).
Local Notation MT := (ReplyKfMeterB.MT_sec NSEC KMAX).
Local Notation LSs rc := (@ReplyLS3B_inst.LSI rc YD2l.TfibB ReplyLSBo.OUT_MAX4
  (fun cx t m ly S => @ReplyB3LScap.fr_CAP rc cx t m ly S /\ ReplyLSBSec.fr_SEC NSEC KMAX ReplyKfCB.KF_KC cx t m ly S)).
Local Notation RR rc := (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
(* this file's: top_x's relation and segments, at the RunCeil in scope *)
#[local] Abbreviation TARX := W_LLVMFuzzerTestOneInput_top_x.ARX.
#[local] Abbreviation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* ---- __asan_memset at top_x's ARX: TopX_INTRIN_memset's contract at ARX_rt, with arodata_ok_cf carried ---- *)
Section amemset_w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma btr_oa_AMEMSET_W : aintrin_realizes_x segs TfibB TopX_RT_lock.ARX_rtW OSet (SIGMA WS_asan_memset).
Proof.
intros ly S Hp W regs mem md d x n HPRE H10 H11 H12 Hn Hd Hdn HDST HAM HKW HRA HHULL HOP.
destruct (TopX_RT_lock.ecall_pre_rtW _ _ _ _ _ _ _ HPRE) as (HPRE0 & HQ).
eapply SRr_mono; [exact (TopX_INTRIN_memset.topx_AMEMSET_x ly S Hp W regs mem md d x n HPRE0 H10 H11 H12 Hn Hd Hdn
  HDST HAM HKW HRA HHULL HOP)|].
intros W' c' _ (EW & regs' & mem' & md' & Hc & HA' & Hpost).
split; [exact EW|]. exists regs', mem', md'. split; [exact Hc|]. split; [|exact Hpost].
pose proof (TopX_RT_lock.stk_above_img _ _ _ _ _ _ (proj1 HPRE0)) as HI.
destruct HPRE0 as (HA0 & _ & _ & Hlo & _).
destruct Hpost as (_ & _ & _ & _ & HV & _).
refine (conj (proj1 HA') (conj (proj2 HA') _)).
apply (TopX_RT_lock.aro_keep_view ly S Hp W mem md mem' (fun a => d <= a < d + n)
  (fun a => spZ regs - ESTACK <= a < spZ regs) HA0 HKW); [| exact HV | exact HQ].
intros a Ha. cbv beta in Ha. pose proof (Z.pow_nonneg 2 40 ltac:(lia)). lia.
Qed.
End amemset_w.

Section btr_oa.
(* ReplyBTop's row SR_R, verbatim: source_reset's contract at R, the one premise this file does not close *)
Context (SR_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_contract_srlf_xR.sr_spec_g_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_source_reset)).

Lemma btr_OA_R : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_op_add.oa_spec_g_xR fx rc tfib_sink_head (@PB_fr rc) TfibB [] (@W_LLVMFuzzerTestOneInput_top_x.ARX rc) (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) MT CfRBridgeRulesB.RP_cf (@pa_val rc fr_prog_listing (@PB_fr rc) A_TEXT + AF_fr_op_add).
Proof.
  intros rc fx.
  pose proof W_LLVMFuzzerTestOneInput_top_x.top_HEV as HEV.
  (* ---- R's laws ---- *)
  assert (R_refl : forall W, RR rc W W)
    by first [exact (YA0nH.wle'_refl tfibsegs (@YGcfRehidePost.RZ_cf rc)) | exact YA0nH.wle'_refl].
  assert (R_trans : forall W1 W2 W3, RR rc W1 W2 -> RR rc W2 W3 -> RR rc W1 W3)
    by first [exact (YA0nH.wle'_trans tfibsegs (@YGcfRehidePost.RZ_cf rc)) | exact YA0nH.wle'_trans].
  assert (WLE_R : forall W W', @wle segs W W' -> RR rc W W')
    by first [exact (YA0nH.wle_wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)) | exact YA0nH.wle_wle'].
  (* ---- top_x's relation: its laws and the facts read off it (top_x's own proofs) ---- *)
  pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_laws as LAWS.
  pose proof W_LLVMFuzzerTestOneInput_top_x.ARX_hp0 as HP0.
  pose proof W_palib.pb_palib_tfib as TL.
  pose proof (TopxTLFB.topx_TLF_B_all rc fx) as TLF.
  pose proof (ReplyKfMeterB.MT_sec_laws NSEC KMAX) as MLAW.
  assert (MO_FR : forall s f, mo_le MT s (set_fs f s) 0)
    by exact (fun s f => ReplyKfMeterB.MT_sec_set_fs NSEC KMAX (fun f0 s0 => eq_refl) f s).
  assert (RO_ARx : forall ly S Hp (W : world segs) mem md, TARX ly S Hp W mem md ->
    @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem)
    by (intros ly S Hp W mem md H; exact (proj2 (proj2 H))).
  assert (HPST : forall a, in_img segs a -> ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ H; inversion H).
  assert (BLKN : forall ly S Hp (W : world segs) mem md p n, TARX ly S Hp W mem md ->
    In (p, n) (ablocks TfibB ly S) -> 0 <= n).
  { intros ly S Hp W mem md p n H Hin.
    destruct (YG0dcf.alc_blocks _ _ (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB) ly S Hp W mem md p n (proj1 H) Hin)
      as (_ & _ & _ & _ & _ & _ & Hn). lia. }
  assert (OWNLOW : ARx_owned_low_law segs TfibB TARX).
  { intros ly S Hp W mem md a H Ho.
    exact (ARx_owned_low_law_cf_x (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)
      ly S Hp W mem md a (proj1 H) Ho). }
  assert (WFL : ARx_wf_law segs TARX (Wf_cf (cp := CfParams_reply) (as_universe TfibB))).
  { intros ly S Hp W mem md H. exact (ARx_wf_law_cf_x (cp := CfParams_reply) segs TfibB ly S Hp W mem md (proj1 H)). }
  assert (SMALLOC : forall s cid, Wf_cf (cp := CfParams_reply) (as_universe TfibB) s -> 0 <= cid <= 10 ->
    count_cid cid (frames s) < fs_frames cid ->
    exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
    frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s)).
  { intros s cid HWF Hcid Hcnt.
    destruct (stack_malloc_progress_cf (cp := CfParams_reply) _ s cid HWF Hcid Hcnt) as (pos & s' & Hpath).
    pose proof (stack_malloc_ok_cf (cp := CfParams_reply) _ s cid HWF Hcid) as HTOK.
    destruct (atok_apath _ _ _ [] (PFake cid pos, s') HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post_cf in HQ.
    destruct HQ as (_ & Hf & _ & _ & Hfrs & Hfresh).
    exists pos, s'. split; [exact Hpath|]. split; [exact Hf|]. split; [exact Hfrs | exact Hfresh]. }
  assert (ASF : astack_free_law_x segs TfibB TARX).
  { intros ly S Hp W mem md mem' md' cid pos H Hin HF HO HV Hvm Hlz He HK HKEPT.
    unfold W_LLVMFuzzerTestOneInput_top_x.ARX in H |- *.
    split; [|split; [exact (proj1 (proj2 H)) |
      exact (ReplyKeptAroB.arodata_kept_B mem mem' (proj2 (proj2 H)) HKEPT)]].
    exact (YG0tcf.astack_free_law_ok_cf (cp := CfParams_reply) segs TfibB ly S Hp W mem md mem' md' cid pos (proj1 H)
      Hin HF HO HV Hvm Hlz He HK). }
  assert (SFREE : forall s cid pos, Wf_cf (cp := CfParams_reply) (as_universe TfibB) s -> In (cid, pos) (frames s) ->
    exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2).
  { intros s cid pos HWF Hin. exact (proj2 (stack_free_ok_cf (cp := CfParams_reply) _ s cid pos HWF Hin)). }
  pose proof (W_img_x.fr_img_cover_x TfibB _ LAWS) as IMGC.
  pose proof AsmTopXEq.ASM0_topx as ASM0.
  assert (FFL : frame_flag_lawP_x segs TfibB TARX)
    by exact (fun ly S Hp W mem md cid pos H => W_frame_flag_cf.frame_flag_lawP_x_ARX ly S Hp W mem md cid pos
      (conj (proj1 H) (proj1 (proj2 H)))).
  (* ---- g_wake[1] and errno (wake's and op_add's / relay_add's HWK, wake's HERRS) ---- *)
  assert (HWK0 : forall a, rg_wake fr_globals + 4 <= a < rg_wake fr_globals + 8 ->
    in_img segs a /\ ~ Exists (in_zr a) (as_owned_static TfibB) /\ ~ (as_errno TfibB <= a < as_errno TfibB + 4)).
  { intros a Ha.
    pose proof (rng_cover (rg_wake fr_globals + 4) 4 G_fr_obj ltac:(vm_compute; reflexivity) a ltac:(lia)) as Ho.
    pose proof (obj_c TfibB a Ho) as Hg.
    split; [exact (c_img TfibB HEV a Hg)|].
    split; [exact (W_drain_pb.drain_HOWN a Hg)|].
    exact (c_obj_noerr TfibB HEV a Ho). }
  assert (HERRS : forall a, as_errno TfibB <= a < as_errno TfibB + 4 -> ~ Exists (in_zr a) (as_owned_static TfibB))
    by (intros a Ha; exact (W_drain_pb.drain_HOWN a (err_c TfibB a Ha))).
  (* ---- op_add's walk at R ---- *)
  refine (W_op_add.pb_op_add_g_xR TfibB [] TARX (RR rc) R_refl R_trans WLE_R _ MT CfRBridgeRulesB.RP_cf
    (@YG0dcf.arodata_ok_cf CfImg_B segs TfibB) RO_ARx LAWS HPST TL MLAW (rp_RMM CfRBridgeRulesB.RP_cf) fr_MMAX
    ?[o_mmax] ?[o_hgs] ?[o_hnfd] ?[o_hhi87] ?[o_hoad] HWK0 YCk0.CTX_AMALLOC ?[o_ctxm] ?[o_ama] (SR_R rc fx)
    YCk0.CTX_AREALLOC ?[o_ctxra] ?[o_ra]).
  (* its image facts and caller contexts, as top_x's strict OA proof decides them *)
  [o_mmax]: (unfold APARTIAL; apply Z.ltb_lt; vm_compute; reflexivity).
  [o_hgs]: (vm_compute; reflexivity).
  [o_hnfd]: (vm_compute; reflexivity).
  [o_hhi87]: (vm_compute; reflexivity).
  [o_hoad]: (vm_compute; repeat split; first [left; discriminate | right; discriminate |
    left; let H := fresh in intro H; discriminate H | right; let H := fresh in intro H; discriminate H]).
  [o_ctxm]: (vm_compute; repeat (first [left; reflexivity | right])).
  [o_ctxra]: (vm_compute; repeat (first [left; reflexivity | right])).
  (* malloc at R: as ReplyBTop closes its AMALLOC_R obligation, over the closed malloc target *)
  [o_ama]: (first [ solve [eapply CfRBridgeRulesRhTopB.AMA_x_kf_rh; first [
      exact (ReplyClosedB.reply_amalloc_target_B fx rc) | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB)
    | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env | exact YGcfNsec.nsec_malloc_cf
    | exact YGcfNsec.nsec_free_cf | exact ReplyRelroGeoB.relro_seg_reply_B
    | exact (YD1vcf.aro_errno TfibB TfibB_syms ReplyDriverCfB.relro_ok_B) | exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX)
    | (intros; reflexivity) | (intros; apply iff_refl) | assumption ]]
    | solve [unshelve eapply CfRBridgeRulesRhTopB.AMA_x_kf_rh; first [
      exact (ReplyClosedB.reply_amalloc_target_B fx rc) | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB)
    | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env | exact YGcfNsec.nsec_malloc_cf
    | exact YGcfNsec.nsec_free_cf | exact ReplyRelroGeoB.relro_seg_reply_B
    | exact (YD1vcf.aro_errno TfibB TfibB_syms ReplyDriverCfB.relro_ok_B) | exact (ReplyKfMeterB.MT_sec_laws NSEC KMAX)
    | exact YGcfNames.nsec_cf | (intros; reflexivity) | (intros; apply iff_refl) | assumption ]] ]).
  (* relay_add at R: its proved walk at the same instance *)
  [o_ra]: {
    intros G _ _.
    pose proof (W_LLVMFuzzerTestOneInput_G.c_rom_out TfibB TfibB_syms HEV) as HRO.
    (* relay_add's globals are four of G_fr_c's objects *)
    assert (RAGin : forall a, inG (RA_G fr_globals) a -> inG (G_fr_c TfibB) a).
    { apply inG_sub. unfold RA_G.
      repeat (apply Forall_cons; [intros a Ha; apply obj_c; revert a Ha; apply rng_cover_zr; vm_compute; reflexivity|]).
      apply Forall_nil. }
    pose proof (W_drain_pb.gx_ok_incl _ _ _ _ RAGin W_LLVMFuzzerTestOneInput_top_x.GX_ok) as HG.
    pose proof (W_drain_pb.rom_out_incl _ _ _ _ RAGin HRO) as HROMO.
    destruct W_relay_add_cut.ra_hv_fr as (HV3 & HV4 & HV5 & HV13 & HH28 & HH29 & HH30).
    Set Generate Goal Names.
    eapply W_relay_add_x.pb_relay_add_xR.
    (* realloc at R first: it fixes MMAX, RO and the admission HAD *)
    all: try (only [AREALLOC_R]: solve [eapply CfRBridgeRulesRhTopB.ARE_x_kf_rh; first [
        exact (ReplyAreallocTargetB.arealloc_realizes_cf_k_replyB_rc 0%nat)
      | exact ReplyAreallocTargetB.arealloc_null_realizes_cf_replyB_rc
      | exact (YG0lawscf.AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB)
      | exact YD25cf.tfib_segs_low | exact ReplyInstFactsB.replyb_api_env | exact YGcfNsec.nsec_malloc_cf
      | exact YGcfNsec.nsec_free_cf | exact ReplyRelroGeoB.relro_seg_reply_B
      | exact (YD1vcf.aro_errno TfibB TfibB_syms ReplyDriverCfB.relro_ok_B)
      | (intros; reflexivity) | (intros; apply iff_refl) | assumption ]]).
    all: try (only [HA_ra]: exact (ReplyHullAdm.hull_adm_of_mo_reply MT ltac:(intros; apply iff_refl)
      ltac:(intros; reflexivity) eq_refl)).
    all: try (only [LAWS]: exact LAWS).
    all: try (only [HP0]: exact HP0).
    all: try (only [TL]: exact TL).
    all: try (only [MTL]: exact MLAW).
    all: try (only [HG]: exact HG).
    all: try (only [HWK]: exact HWK0).
    all: try (only [HNROM]: exact W_relay_add_cut.ra_nrom_fr).
    all: try (only [HROMO]: exact HROMO).
    all: try (only [MO_FR]: exact MO_FR).
    all: try (only [HV3]: exact HV3).
    all: try (only [HV4]: exact HV4).
    all: try (only [HV5]: exact HV5).
    all: try (only [HV13]: exact HV13).
    all: try (only [HH28]: exact HH28).
    all: try (only [HH29]: exact HH29).
    all: try (only [HH30]: exact HH30).
    all: try (only [HRGA]: exact W_relay_add_cut.ra_aligned_fr).
    all: try (only [HRGP]: exact W_relay_add_cut.ra_cells_fr).
    all: try (only [HMMAX]: (unfold ATABLE; apply Z.ltb_lt; vm_compute; reflexivity)).
    all: try (only [HPST]: exact HPST).
    all: try (only [IMGC]: exact IMGC).
    all: try (only [BLKN]: exact BLKN).
    all: try (only [ALOCK]: exact TopX_RT_lock.topx_ALOCK_W).
    all: try (only [AUNLOCK]: exact TopX_RT_lock.topx_AUNLOCK_W).
    all: try (only [AMEMSET]: exact btr_oa_AMEMSET_W).
    all: try (only [WAKE]: exact (W_wake_x.pb_wake_x TfibB [] _ fr_globals LAWS TL TLF _ WFL SFREE SMALLOC OWNLOW IMGC
      ASM0 ASF FFL W_wake_x.wk_hv8_fr HWK0 HERRS)).
    all: try (only [R_refl]: exact R_refl).
    all: try (only [R_trans]: exact R_trans).
    all: try (only [WLE_R]: exact WLE_R).
    all: try (only [RO_ARx]: exact RO_ARx).
  }
Qed.
End btr_oa.
