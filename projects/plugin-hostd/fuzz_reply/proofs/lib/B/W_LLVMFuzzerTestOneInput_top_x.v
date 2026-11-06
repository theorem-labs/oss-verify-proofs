(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The ARx-generic entry composition of fuzz_reply.asan-ubsan's LLVMFuzzerTestOneInput (image B) AT THE cf INSTANCE:
   lib/B's twin of lib/A/W_LLVMFuzzerTestOneInput_top_x.v (a working branch 44de651f71b), the link the
   image-B cf driver consumes through lib/B/W_asm.v's DRIVER_CF_B.  fr_contract_top_x is B's cut_x
   (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v, a working branch 9409d4da51f) fr_lib_contract_cf_x at
     B   := TfibB (lib/B/YD2l.v, the start-up instance, TfibB_syms : TfibSyms TfibB);
     ARx := ARX, the cf live state CONJOINED with an empty ghost poisoned-head set,
            fun ly S Hp W mem md => ARcf (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []
            (as on A: fuzz_reply calls no poison routine, so every cf leaf keeps Hp = [] and HP0 is the second
            projection); laws by lib/B/W_journal_x.AR_laws_x_and_hp over Reusable/YGcallcf.AR_laws_x_cf
            (Reusable/YG0lawscf.AR_laws_ok_cf), hl := cf_head.  CfParams_reply is the one parameter record of both
            images (lib/A/CfParamsReply.v: no field is an image address);
     PST := [] (every walk writes its globals through the G overlay);
     G_fr := G_fr_c TfibB (lib/B/W_LLVMFuzzerTestOneInput_G.v), HG by c_gx_ok from TfibB_syms (HEV: ts_errno; HOWN:
            ts_owned, G_fr_c's 21 ranges apart from Tfib_owned_static by computation).
   The segments are Section hypotheses in cut_x's text at that instance (SEG_JT is walked inside cut_x); each is
   replaced by its ARx proof as the arms convert (a Theorem Labs lane's step 7).  PLUGGED: SEG_HEAD (LatchX,
   lib/B/W_LLVMFuzzerTestOneInput_head_x.v from image B's lf_seg_head_b; its instance facts c_HGnout / c_HERRNO /
   c_HZS from lib/B/W_LLVMFuzzerTestOneInput_G.v, its four model rules verbatim hypotheses below); SEG_LATCH (LatchX,
   lib/B/W_LLVMFuzzerTestOneInput_latch_x.v 01ea050cd51 from a Theorem Labs lane's B lf_seg_latch); SEG_PRO (LatchX,
   lib/B/W_LLVMFuzzerTestOneInput_pro_x.v 56789d2bc7a from a Theorem Labs lane's B lf_seg_pro); SEG_EXIT (a Theorem Labs lane's
   lib/B/W_LLVMFuzzerTestOneInput_exit_x.v lf_seg_exit_x_all, 947f295128a); ARM_close / ARM_eintr / ARM_sendmax / ARM_default
   (lib/B/W_LLVMFuzzerTestOneInput_small_x.v, commit 0fc78fa1870, the conversion of
   lib/B/W_LLVMFuzzerTestOneInput_small.v's lf_arm_close .. lf_arm_default); ARM_drain (HeadX's
   lib/B/W_LLVMFuzzerTestOneInput_drain_x.v lf_arm_drain_x, a working branch 4097b0f7b25).  Their instance facts come from B _G.v,
   lib/B/W_bx_inst.v / W_bx_inst_x.v (a12's witnesses) and the cf laws; every other premise is a hypothesis below in
   its segment file's text at the instance.
   fr_live_pre / fr_live_post / fr_surv / LIBROOM
   / NP / fr_FP / LS / RINV stay Variables: the driver instantiates them (lib/B/YCfn_cf.v holds fr_live_pre_b,
   fr_live_post_b, fr_surv_b and fr_FP_b; at LS := ReplyLSB.fr_LS, RINV := ReplyRINVB.fr_RINV the four head rules are
   B _G.v's c_RI_head_nout / c_LS_head_nout / c_RI_head_skip / c_LS_head_skip, checked at the end of this file).
   WHY NOT THE DONOR'S TLLVMF: lib/B/YCfn.v's tfib_lib_contract_x is FALSE for fuzz_reply (its post keeps the live
   blocks equal and k <= 2000, while g_out and g_src's table survive every call and one write makes about 131,128
   allocator calls; ENTRY-FINDING.txt (sha256 2fea03396e1e; internal record)), so image B mirrors image A and takes the cf contract. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
(* route R (a Theorem Labs lane): the R contract texts topxR cites (lp_spec_g_xR) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
(* RelocB's sink-instance guard: no sink class is inferred below; the sink head is the Section's Context *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
(* the generic carries are the Reusable ones, as the B kit's generated W_kit_x / W_journal_x take them (a working branch
   bkit-cand11 fb28b53a2b8; cut_x the same at a working branch a38906f5dd8); lib/B's re-pointed copies
   are not Required *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x.
(* the room kit's count model (cand13's generated lib/B/ReplyCnt.v: acnt / xcnt_ok / tr_peakP, cited qualified as
   image A's top step does), drain_defs_x's msz_ok / dr3_* / ls3_* premises (the B drain arm's own, a Theorem Labs lane; after the #6 cutover no B TX_*
   definition is cited, every LS row is stated at its own text), and drain_calls' model
   functions (dr_dfun / dr_cap1).  A's ReplyLScnt.pk_gone has no B twin: it is the Variable gn_pk; A's ReplyTrPeakCnl.cnl_pk term is ReplyB3TrPeakCnl.dr_cnl_pk_B; see the rows
   that name them *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
ReplyCnt W_LLVMFuzzerTestOneInput_drain_defs_x W_LLVMFuzzerTestOneInput_drain_calls TopxEntry
W_img_x W_gesture_end W_gestures_end_top AsmTopX CfRBridgeRulesB TopX_RT_lock TopX_RT_B2
TopX_RT3 TopX_RT4 TopxDrainLitB W_drain_pb YCej.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3TrPeakCnl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_send_line_x TopX_RT4 W_errno_azs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require RTx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallcf.
(* SEG_HEAD: the AR file's model functions (lm_clear_O / lm_set_k / hd_kb / hd_k', cited qualified), LatchX's
   conversion, and a Theorem Labs lane's model invariants for the check at the end; Require only, so none of their names shadows
   a name used here *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_head_x ReplyLSB ReplyRINVB.
(* SEG_LATCH / SEG_PRO / SEG_EXIT: the generic kit their premises name (W_contract_x's callee specs, W_frame_x's frame
   laws, YGcallx's laws, YG01cf / YG05cf's Wf_cf and stack_malloc / stack_free facts, YG0tcf's stack_free law), and the
   segment files Required without Import (their names cited qualified), with the AR files whose model functions the
   rules name (_pro.v's pro_m / pro_G, W_op_add's oa_cost, W_bx_defs' lx_* / xr_GM / AX_lit_empty), a12's instance
   witnesses W_bx_inst / W_bx_inst_x, and the K0 table YCk0.CTX_AFREE *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx YG01cf YG05cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_frame W_frame_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0tcf YG0dcf YG08cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_op_add W_LLVMFuzzerTestOneInput_pro W_LLVMFuzzerTestOneInput_pro_x W_LLVMFuzzerTestOneInput_latch_x
W_bx_defs W_LLVMFuzzerTestOneInput_exit_x W_bx_inst W_bx_inst_x YCk0.
(* ARM_drain: the kit's mutex contracts (W_sites_x), the drain conversion (Required, cited qualified), and LAST the
   model the drain rules name (Prog's CheckRep / RelayKeys / RelayModel, drain_b_c, the AR file's _drain_defs.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_drain_x.
(* the four small arms: their conversion and the AR file's model functions (sm_close / sm_eintr / sm_sendmax /
   sm_default / sm_dg), cited qualified; Require only *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_small_x.
(* ARM_add / ARM_write: their conversions and the AR files' model functions (ad_at_op / ad_os / ad_open / ad_none;
   wr_* / WR_MMAX / set_pending), cited qualified, and list_push's ARx contract (lib/B/W_list_push.v
   pb_list_push_g_x); Require only *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_add W_LLVMFuzzerTestOneInput_add_x W_LLVMFuzzerTestOneInput_write W_LLVMFuzzerTestOneInput_write_x
W_list_push.
(* ARM_remove / ARM_event: their conversions, the AR files' model functions (cited qualified) and .str.3's shadow facts
   at ARX (lib/B/TopxImageB.v ashp_str3_1_fr_cf, taken by path from commit 5929e8e16314); Require only *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_remove W_LLVMFuzzerTestOneInput_remove_x W_LLVMFuzzerTestOneInput_arm_event
W_LLVMFuzzerTestOneInput_event_x TopxImageB.
(* ARM_gone: its conversion, the AR base's model obligations and the AR walk's instance facts at G_fr_c (cited
   qualified); Require only *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_gone_x W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_base_x
W_LLVMFuzzerTestOneInput_gone_inst.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0scf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
(* QMm W1 (B): image B's kept-bytes facts (arodata_kept_B, arodata_none_B), Require without Import *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKeptAroB.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* no range of G meets [lo, lo + n) (lib/A/W_LLVMFuzzerTestOneInput_add.v:105 ad_apart, A's zz_HOWN) *)
Definition top_apart (lo n : Z) (G : list (Z * Z)) : bool :=
  forallb (fun r => (fst r + snd r <=? lo) || (lo + n <=? fst r)) G.
Lemma top_apart_ok : forall lo n G, top_apart lo n G = true -> forall a, inG G a -> ~ (lo <= a < lo + n).
Proof.
  intros lo n G H a Ha Hr. unfold top_apart in H. rewrite forallb_forall in H.
  unfold inG in Ha. apply Exists_exists in Ha as (r & Hin & Hz). specialize (H r Hin).
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; unfold in_zr in Hz; lia.
Qed.

(* the instance facts of G_fr_c at TfibB (A's zz_HEV / zz_HOWN, lib/A/W_LLVMFuzzerTestOneInput_addI.v) *)
Lemma top_HEV : as_errno TfibB = TFIB_ERRNO_B.
Proof. rewrite (ts_errno TfibB TfibB_syms). reflexivity. Qed.
Lemma top_HOWN : forall a, inG (G_fr_c TfibB) a -> ~ Exists (in_zr a) (as_owned_static TfibB).
Proof.
  intros a Ha. rewrite (ts_owned TfibB TfibB_syms). rewrite (G_fr_c_val TfibB top_HEV) in Ha. intros Hex.
  assert (Hb : forallb (fun r => top_apart (fst r) (snd r) (G_fr_obj ++ [(TFIB_ERRNO_B, 4)])) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  apply Exists_exists in Hex as (r & Hr & Hz). rewrite forallb_forall in Hb.
  destruct r as [lo n]. exact (top_apart_ok lo n _ (Hb (lo, n) Hr) a Ha Hz).
Qed.

Section topx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

(* ---- the instance ---- *)
(* QMm W1 (B) (a Theorem Labs lane; the twin of a Theorem Labs lane's lib/A top_x at 787ba93d6df4, a Theorem Labs lane 23:17Z): ARX carries
   arodata_ok_cf, the value fact the allocator rules read at the call memory (QMm_cf; part 3c widens arodata_ok_cf
   to cover the refill report's five read-only reads too). It is a conjunct of the RELATION, so every walk hands it
   to the next call. ARX_laws still holds because QMm W0' gave YCbqG.ARx_frame_law its kept-bytes premise and
   reply B's RELRO is inside YF0m.Tfib_kept (ReplyKeptAroB.arodata_kept_B). At the driver's entry it comes from
   ReplyKeptAroB.arodata_none_B. *)
Definition ARX : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [] /\
    @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem.
Lemma ARX_laws : AR_laws_x segs TfibB ARX (@cf_head CfParams_reply).
Proof.
  apply (AR_laws_x_iff segs TfibB (fun ly S Hp W mem md =>
           (ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []) /\
           @YG0dcf.arodata_ok_cf CfImg_B segs TfibB mem)).
  { intros ly S Hp W mem md. unfold ARX. split.
    - intros ((H1 & H2) & H3). exact (conj H1 (conj H2 H3)).
    - intros (H1 & H2 & H3). exact (conj (conj H1 H2) H3). }
  apply (AR_laws_x_and_mem segs TfibB _ (@YG0dcf.arodata_ok_cf CfImg_B segs TfibB) ReplyKeptAroB.arodata_kept_B).
  apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
Qed.
(* cut_x's HP0 at the instance *)
Lemma ARX_hp0 : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md -> Hp = [].
Proof. intros ly S Hp W mem md H. exact (proj1 (proj2 H)). Qed.
Lemma GX_ok : gx_ok segs TfibB (G_fr_c TfibB).
Proof. exact (c_gx_ok TfibB top_HEV top_HOWN (c_HKEPT TfibB TfibB_syms top_HEV)). Qed.

(* ---- the driver's parameters ---- *)
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variables LIBROOM NP : astate -> Prop.
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* the room record (an internal work row): a Theorem Labs lane's G-BCF B RP_cf (lib/B/CfRBridgeRulesB.v:683, a working branch room merge on
   W8's B room branch 2e33f1270a5), as image A's top step has `Local Notation RPi := CfRBridgeRules.RP_cf`.  Its rp_RM is
   fun S _ => room_live_cf S; B keeps NP a Variable, so RP_NP / NPF below stay hypotheses (the instance, at
   NP := room_live_cf, closes them by iff_refl / room_live_set_fs, as A's top does in its proof) *)
Local Notation RPi := CfRBridgeRulesB.RP_cf.
(* the re-fit arms' room premises at RPi (A's top proves both in its proof: RP_NP by iff_refl at
   NP := room_live_cf, NPF by YGcfRoomLive.room_live_set_fs; top_x.v:869-871 at 14fbe276057).  B's NP is a Variable,
   so they are hypotheses here, discharged at the instance *)
Hypothesis RP_NP : forall S k, rp_RM RPi S k <-> NP S.
Hypothesis NPF : forall S f, NP S -> NP (set_fs f S).
(* the drain arm's held-list peak: s5-r9's B twin of A's ReplyTrPeakCnl.cnl_pk term, lib/B/ReplyB3TrPeakCnl.v:1261
   dr_cnl_pk_B h P := cnl_pk (hs_held h) (map (map (Z_to_bv 8)) (dr_lines h)) P (G-BCNL, f11c18c29ef on the window),
   exactly A's top-step term; a Theorem Labs lane's drain arm takes it as its Section Variable dr_cnl_pk *)
Local Notation dr_cnl_pk := ReplyB3TrPeakCnl.dr_cnl_pk_B.
(* the gone arm's count peak: A passes s5-r1d's ReplyLScnt.pk_gone, which has no B twin; a Theorem Labs lane's B gone arm keeps
   it a Section Variable (gone_x.v:166 / gone_base_x.v:406), so top_x does too and states CNT_gone_rig / LS_cnt_gone /
   CNT_gone_step over it *)
Variable gn_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat.

Local Notation G := (G_fr_c TfibB).
Local Notation BASEx cx Hp := (lf_base_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp).
Local Notation IH := (INV_H_x TfibB NP G fr_FP [] ARX LSx RINV).
Local Notation ID := (INV_D_x TfibB NP G fr_FP [] ARX LSx RINV).
Local Notation IA := (INV_A_x TfibB NP G fr_FP [] ARX LSx RINV).
Local Notation IK := (INV_K_x TfibB NP G fr_FP [] ARX LSx RINV).
Local Notation IX := (INV_X_x TfibB NP G fr_FP [] ARX LSx RINV).
Local Notation POST := (lf_post_x TfibB MT XN_LIB fr_live_post fr_surv NP G fr_FP [] ARX).

(* ---- SEG_HEAD's four model rules (lib/B/W_LLVMFuzzerTestOneInput_head_x.v), verbatim; the AR file's model
   functions qualified ---- *)
Hypothesis RI_head_nout : forall cx t m, RINV cx t m -> RINV cx t (W_LLVMFuzzerTestOneInput_head.lm_clear_O m).
Hypothesis LS_head_nout : forall cx t m ly S, LSx cx t m ly S -> LSx cx t (W_LLVMFuzzerTestOneInput_head.lm_clear_O m) ly S.
Hypothesis RI_head_skip : forall cx t m, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (W_LLVMFuzzerTestOneInput_head.hd_kb cx m) = None -> RINV cx t m -> RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_head.lm_set_k m (W_LLVMFuzzerTestOneInput_head.hd_k' cx m)).
Hypothesis LS_head_skip : forall cx t m ly S, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (W_LLVMFuzzerTestOneInput_head.hd_kb cx m) = None -> LSx cx t m ly S -> LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_head.lm_set_k m (W_LLVMFuzzerTestOneInput_head.hd_k' cx m)) ly S.

(* ---- the allocator instance's facts no lib/B lemma states at TfibB / ARX yet (the segment files' texts) ---- *)
Hypothesis TL : PALib TfibB.
Hypothesis TLF : PALibF TfibB.
Hypothesis MLAW : ameter_laws MT.
Hypothesis FFL : frame_flag_lawP_x segs TfibB ARX.
Hypothesis ERRL_x : errno_law_x TfibB ARX.
(* rom_out at the Section's sink head SK: B _G.v's c_rom_out proves it at YE2k.tfib_sink_head, the instance's head
   (_pro.v's HRO and _exit_x.v's XRF_ROM_OUT, one text) *)
Hypothesis HRO : rom_out segs TfibB G.
(* the stdio sink's image laws at SK (_exit_x.v's AIL; YD1u.v's tfib_AIL proves them at YE2k.tfib_sink_head) *)
Hypothesis AIL : asink_img_laws segs TfibB tfib_K.
(* ---- callee contracts at ARX that no _x proof gives on this base (the segment files' texts) ---- *)
(* check_bounded (_latch_x.v's W1_check_bounded) *)
Hypothesis CB_x : cb_spec_x (PI := PB_fr) TfibB [] ARX (BASE + AF_fr_check_bounded).
(* malloc and relay_add at their K0 tables (lib/B/YCk0.v), the premises W2's pb_op_add_g_x takes beside SR_x
   (lib/B/W_op_add.v:1889, W2's B W_op_add.v of record, a working branch 11fb7104fb5) *)
(* B restatement (an internal work row): image A's top step (W8 14fbe276057 :234) room text, RPi after the MMAX *)
Hypothesis AMA_x : amalloc_cf_rule_c_x segs TfibB [] ARX MT CfParamsReply.fr_MMAX RPi YCk0.CTX_AMALLOC.
(* B restatement (an internal work row): RPi after MT, the room kit's signature (A's top step 14fbe276057 builds RA_x at RPi in its proof) *)
Hypothesis RA_x : ra_spec_g_x TfibB [] ARX MT RPi fr_globals YCk0.CTX_AREALLOC (BASE + AF_fr_relay_add).
(* realloc at its K0 table and the memcpy intrinsic, over ARX: the premises lib/B/W_list_push.v pb_list_push_g_x
   takes beside AMA_x (list_push's contract for ARM_write's LP), at WR_MMAX = cf_malloc_max *)
(* B restatement (an internal work row): image A's top step (14fbe276057 :235) room text, RPi after the MMAX; B keeps its WR_MMAX
   (= CfParamsReply.fr_MMAX by reflexivity, ReplyB3LS3Peak.pk_fr_MMAX) *)
Hypothesis ARE_x : W_journal_x.arealloc_cf_rule_c_x segs TfibB [] ARX MT W_LLVMFuzzerTestOneInput_write.WR_MMAX RPi
  YCk0.CTX_AREALLOC (pa_sigma WS_realloc).
Hypothesis AMEMCPY_x : aintrin_realizes_x segs TfibB ARX OCpy (pa_sigma WS_asan_memcpy).
(* check_shape_done, source_reset, check_shape_ends, relay_finish (_exit_x.v's CSD / SR / CSHE / RFg) *)
Hypothesis CSD_x : csd_spec_x TfibB [] ARX (BASE + AF_fr_check_shape_done).
(* B restatement (an internal work row): image A's top step (W8 14fbe276057) room text - RPi after MT (A: at RP := RPi) *)
Hypothesis SR_x : sr_spec_g_x TfibB [] ARX MT RPi (BASE + AF_fr_source_reset).
(* NEW from image A's top step (14fbe276057 :245). MO_FR: the meter's frame law (B owner: s5-r9 offered; A: a8's
   TopxLawMeter.topx_MO_FR at MT := ameter_triv, add64d407fd).  ASM0 / ASM1 (asan_stack_malloc classes 0 / 1; class 0
   is B's wake fake frame 0x824d0) are built in the proof by a Theorem Labs lane's AsmTopX.asm0_pres_ARX / asm1_pres_ARX, as A's
   top does *)
(* KF-COUNT #4 (a Theorem Labs lane 09:32Z, the same line in every A and B file): the meter's set_fs law; s5-r9's
   lib/B/TopxLawMeterB.v topx_MO_FR_gen proves it at any meter with ameter_laws + mo_fs_inv, and topx_MO_FR at
   ameter_triv (A's names, a Theorem Labs lane 12:27Z; a working branch); the instance plugs it *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* B restatement (an internal work row): RPi after MT, the room kit's signature (A's top step 14fbe276057 builds CSHE_x at RPi in its proof) *)
Hypothesis CSHE_x : forall Gc, gx_ok segs TfibB Gc -> cshe_spec_x TfibB [] ARX MT RPi Gc (BASE + AF_fr_check_shape_ends).
(* B restatement (an internal work row): RPi after MT, the room kit's signature (A's top step 14fbe276057 builds RF_x at RPi in its proof) *)
Hypothesis RF_x : rf_spec_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX (RF_G fr_RG AG_LISTEN ++ G_SL TfibB fr_RG) fr_RG
  AG_THREAD_UP AG_LISTEN YCk0.CTX_AFREE (BASE + AF_fr_relay_finish).
(* NEW from image A's top step (14fbe276057 :624-625): SEG_EXIT's callee contracts at ARX - free(NULL) at the free
   table (B owner: none yet, a Theorem Labs lane places it) and gestures_end's _x contract at the room (B owner a Theorem Labs lane, row
   an internal work row, pb_gestures_end_closed_x on 52dbc390dc6) *)
Hypothesis AFREE0_x : afree_null_cf_rule_c_x segs TfibB [] ARX MT RPi YCk0.CTX_AFREE.
(* GSE_x is built in the proof (A: top_x.v:1019 at 3d17f490d56), from a Theorem Labs lane's pb_gestures_end_closed_x and a Theorem Labs lane's
   pb_gesture_end_x by a Theorem Labs lane's scratch proof; gesture_end's strlen (ASTRLEN_x) is built there too, by a Theorem Labs lane's
   TopX_RT_B2.topx_ASTRLEN_B_W (TRL.ARX_rt is top_x's ARX) *)
(* ---- shadow facts over ARX: op_add's G (_pro_x.v's GSHV) and the "" literal (_exit_x.v's XE_LIT_S) ---- *)
Hypothesis GSHV_x : forall ly S Hp (W : world segs) mem md a n, ARX ly S Hp W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> inG W_LLVMFuzzerTestOneInput_pro.pro_G x) -> shadow_hull_vis (aview segs (w_H W) mem) a n.
Hypothesis XE_LIT_S_x : ashp_x ARX (VAL W_bx_defs.AX_lit_empty) 1.
(* ---- SEG_PRO's model rules (_pro_x.v), verbatim at the instance ---- *)
(* NEW from image A's top step (14fbe276057 :397): the driver's FP cover of the hand-off blocks.  It replaces the
   HFP_pro hypothesis: HFP_pro is built in the proof by a Theorem Labs lane's lib/B/TopxEntry.hfp_pro_x
   (a working branch 48eff67880c, A's twin a2 f6fc8c0f078), and FPCOV is discharged at the B driver by
   TopxEntry.fr_FP_b_cov (at fr_FP := YCfn_cf.fr_FP_b) *)
Hypothesis FPCOV : forall regs ly S (W : world segs) mem b, In b (W_LLVMFuzzerTestOneInput_cut.fr_hblks W mem) ->
  In (fst b, fst b + snd b) (fr_FP regs ly S W mem).
(* KF-COUNT F2 (A f937a8adaa8): `mo_le MT (c_S cx) S2 0 ->` after the blocks_bytes line *)
Hypothesis LS_pro_oa : forall cx Hp (S2 : astate) pos,
  lf_base_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  mo_le MT (c_S cx) S2 0 ->
  blocks_bytes S2 + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok MT S2 (W_op_add.oa_cost MT).
Hypothesis RI_pro : forall cx Hp q T' pj c O cap out,
  lf_base_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp ->
  (exists c0 mx0, aout_at TfibB fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  RINV cx 0 (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out).
(* LS_pro at the PROPOSED text (W8Add's fr_LS_pro; _pro.v:687 / _pro_x.v) *)
(* B restatement (an internal work row): image A's top step text (W8 a working branch 14fbe276057), B names *)
(* KF-COUNT F2 (A f937a8adaa8): `mo_le MT (c_S cx) S2 0 ->` after the blocks_bytes line *)
Hypothesis LS_pro : forall cx Hp q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp ->
  (exists c0 mx0, aout_at TfibB fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 ->
  mo_le MT S2 S (W_op_add.oa_cost MT) ->
  (exists T0 rest0, Permutation (ablocks TfibB (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ReplyCnt.xcnt_ok TfibB (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks TfibB ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks TfibB ly S) ((q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))))) ->
  LSx cx 0 (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) ly S.
(* B twin to come: lib/B/W_op_add.v:215 oa_peak on a working branch 24341ca6749 (an internal work row, not yet on this base). Text = image A's top step (W8 a working branch 14fbe276057) verbatim, B names *)
Hypothesis LS_cnt_pro : forall cx T0 cap out (S2 : astate),
  ReplyCnt.xcnt_ok TfibB (c_S cx) (c_ly cx) (input_blks cx) T0 cap out ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) ->
  cnt_ok_pk RPi W_op_add.oa_peak (ablocks TfibB (c_ly cx) S2).
(* ---- SEG_EXIT's model rules (_exit_x.v), verbatim at the instance, MMAX := fr_MMAX; W_bx_defs' model functions
   qualified ---- *)
(* B restatement (an internal work row): image A's top step text (W8 14fbe276057 :640), = a Theorem Labs lane's B exit arm
   (a working branch afc7ac89f0f (= 570c903d342's texts), lib/B/W_LLVMFuzzerTestOneInput_exit_x.v Section lxx).  NOT s5's TX_LS_rf_room (ReplyLSI.v:185 /
   B's ReplyLS3B_inst): that one is over lx_rf_room_p (gse_room_p / B gse_room_c3), a different Fixpoint from
   W_bx_defs.lx_rf_room (gse_room); the instance plug bridges them, as on A.  W_bx_defs.lx_rf_room's `- cap`
   threading comes with a12's exit head (W_bx_defs.v:167-173 at 492d1f33ceb) *)
Hypothesis LS_rf_room : forall cx t m ly S,
  LSx cx t m ly S -> 0 <= t <= OPS_MAX ->
  W_bx_defs.lx_rf_room CfParamsReply.fr_MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m)
    (lm_es m).
(* KF-COUNT F8 (A aacecd50fed): lregs_X's t bound and the relay entries' non-empty key texts (the exit arm's
   exit_keys_nonempty, from amodel_at's aentry_ok) *)
Hypothesis LS_exit_budget : forall cx t m ly S, LSx cx t m ly S ->
  0 <= t <= OPS_MAX ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  mo_ok MT S (W_bx_defs.lx_exit_cost MT m).
Hypothesis RI_exit_slots : forall cx t m, RINV cx t m ->
  forall j, (j < 4)%nat -> W_bx_defs.lx_ends_slot_ok (nth j (lm_hs m) None).
(* B restatement (an internal work row): image A's RIRS text 3f40808c334, taken by pin from a Theorem Labs lane's B SEG_EXIT
   a working branch 0b7cfc03df3 (lib/B/W_LLVMFuzzerTestOneInput_exit.v:162), qualified for top_x;
   plugged by a Theorem Labs lane's ReplyRINVB_exit.RI_exit_ends_btop_restated (713767bda40) *)
Hypothesis RI_exit_ends : forall cx t m, RINV cx t m -> (0 < length (lm_es m))%nat ->
  0 <= lm_gn m <= 1 ->
  (forall i h, nth i (lm_hs m) None = Some h -> Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs (hs_held h))) ->
  W_bx_defs.lx_ends_run (lm_gn m) (W_bx_defs.lx_rf_O m)
    (W_bx_defs.lx_norder m) (W_bx_defs.lx_ord m) (lm_hs m) 0 =
  Some (Z.of_nat (length (W_bx_defs.lx_rf_O m))).
(* B restatement (an internal work row): image A's official top_x text after the #6 cutover (window 1f8fb3038b5), B names; it
   equals the B TX_* duplicate it used to cite, up to unfolding *)
(* KF-COUNT F8: the start model's non-empty key texts, last *)
Hypothesis LS_exit_end : forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_bx_defs.lx_exit_cost MT m ->
  ajournal_gx_x segs TfibB [] ARX G 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks TfibB ly' S') ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
(* NEW from image A's top step (W8 14fbe276057), B names *)
Hypothesis LS_exit_cnt : forall cx t m ly3 S3 rest (ly' : alayout) (S' : astate) cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall p n, In (p, n) (ablocks TfibB ly' S') -> 4096 <= p) ->
  ReplyCnt.xcnt_ok TfibB S' ly' (input_blks cx) (lm_G m) cap out.
(* NEW from image A's top step (W8 14fbe276057), B names *)
Hypothesis LS_exit_cap : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> 0 <= t <= OPS_MAX ->
  gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) <= CAPOUT_MAX.
(* NEW from image A's top step (W8 14fbe276057), B names *)
Hypothesis LS_cnt_exit : forall cx t m ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> amodel_at TfibB ly S W mem m -> 0 <= t <= OPS_MAX ->
  cnt_ok_pk RPi rf_pk (ablocks TfibB ly S).
Hypothesis FP_SINK : forall cx Hp, BASEx cx Hp -> ~ YI16.sink_open_fp (lf_FP fr_FP cx).

(* ---- ARM_drain's callee contracts (_drain_x.v's RSRC_x / DRAIN / ALOCK / AUNLOCK / CNLR / CNL; its CSD is CSD_x
   above, the same text), and its model rules, verbatim at the instance, MMAX := fr_MMAX ---- *)
Hypothesis RSRC_x : forall W ly S Hp (regs : bvmap 5 word) mem md ch T es fd,
  afn_pre_x segs TfibB ARX RSRC_STK ly S Hp W regs mem md ch ->
  getr regs 10 = w64 fd -> 0 <= fd < 2 ^ 32 ->
  arelay_at TfibB fr_RG ly S W mem T es -> rom_view segs W mem ->
  SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_source) regs mem md)
    (aleafx_post_x TfibB [] ARX RSRC_STK regs ly S Hp W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = fd /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> fd) /\
            a0 = w64 (T + AENT * Z.of_nat j)) \/
         ((forall e, In e es -> re_fd e <> fd) /\ a0 = w64 0))).
(* B restatement (an internal work row): image A's top step (W8 14fbe276057) room text - RPi after MT (A: at RP := RPi) *)
(* DR_x is built in the proof by a Theorem Labs lane's B W_drain_pb.pb_drain_x (A: W8's fb66907d92b top_x.v:1181), which takes
   the allocator rules at their caller contexts; strndup's is this hypothesis, at YCej.CTX_strndup (A's ACej.CTX_strndup),
   discharged at the instance by a Theorem Labs lane's lib/B/CfRStrndup.ASTRNDUP_x_kf *)
Hypothesis ASTRNDUP_x : astrndup_cf_rule_c_x segs TfibB [] ARX MT CfParamsReply.fr_MMAX RPi YCej.CTX_strndup
  (@pa_sigma _ fr_prog_listing PB_fr WS_strndup).
(* ALOCK / AUNLOCK are built in the proof by a Theorem Labs lane's lib/B/TopX_RT_lock.topx_ALOCK / topx_AUNLOCK (G-BLOCK,
   a working branch e1fae7037354), as image A's top does by TopX_RT *)
Hypothesis CNLR_x : cnlr_spec_x (PI := PB_fr) TfibB [] ARX (BASE + AF_fr_check_no_loss_read).
(* B restatement (an internal work row): RPi after MT, the room kit's signature (A's top step 14fbe276057 builds CNL_x at RPi in its proof) *)
Hypothesis CNL_x : forall Gc, gx_ok segs TfibB Gc -> gx_rt (PI := PB_fr) TfibB Gc -> rom_out segs TfibB Gc ->
  cnl_spec_x (PI := PB_fr) TfibB [] ARX MT RPi Gc CfParamsReply.fr_MMAX (BASE + AF_fr_check_no_loss).
Hypothesis RI_drain_skip : forall cx t m si h,
  RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
   (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
      re_eof (nth j (lm_es m) dr_e0) = 1)) ->
  RINV cx (t + 1) (dr_skip m (dr_k' cx m)).
(* B restatement: a Theorem Labs lane's RI_drain_step_btop_restated (a working branch 713767bda40,
   lib/B/ReplyRINVB_exit.v:788-798 at RINV): A's text plus the paddings and the held capacity that B's dr_step_ok
   (drain_defs.v:224-249) lacks; the B arm holds all four at drain_calls_x.v:3415 *)
Hypothesis RI_drain_step : forall cx t m si h j e' h' c' O' cap' out' ev' LB E' H',
  RINV cx t m -> 0 <= t < OPS_MAX ->
  hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h'))) < 2 ^ 22 ->
  dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr_step_ok cx m si h j e' h' c' O' cap' out' ev' LB E' H' ->
  length (re_pad1 e') = 4%nat -> length (re_pad2 e') = 4%nat ->
  hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h'))
    (2 * (hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h')))))) ->
  RINV cx (t + 1) (dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' c' O' cap' out').
(* B twin to come: none (msz_ok is a Theorem Labs lane's lib/B/W_LLVMFuzzerTestOneInput_drain_defs_x.v:92). Text = image A's top step (W8 a working branch 14fbe276057) verbatim, B names *)
Hypothesis DR_CNT_grow : forall cx t m si h j e' h' LB out' (P : Z -> bool),
  RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.msz_ok m -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_kh (nth j (lm_es m) dr_e0) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpre h -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_hn h -> 0 <= lm_cap m ->
  W_LLVMFuzzerTestOneInput_drain_calls.dr_dfun m si h j e' h' LB ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epost (nth j (lm_es m) dr_e0) e' h ->
  (* added: the held-array clause of the entry drain leaves (aentry_ok e', W_rep.v:133-134); A's ReplyCntArms.v:104-105,
     lib/B/W_LLVMFuzzerTestOneInput_drain_defs_x.v / _drain_x.v of this tree, lib/B/ReplyBTopCntDr.v btcnt_DR_CNT_grow_kh *)
  ((re_hp e' = 0 /\ re_keys e' = []) \/ (re_hp e' <> 0 /\ 8 <= re_kh e')) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpost h h' ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_dpost m j h e' h' ->
  (ReplyCnt.acnt P (aentry_blks e' ++ asrc_blks h' ++ aout_blks (W_LLVMFuzzerTestOneInput_drain_calls.dr_cap1 m j h) out') <=
   ReplyCnt.acnt P (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) +
   Z.to_nat (ReplyCnt.tr_peakP P
     (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)))%nat.
Hypothesis RI_src : forall cx t m si h,
  RINV cx t m -> dr_pick cx m si h ->
  hl_recs (hs_expected h) = [] /\ NoDup (texts (hs_held h)) /\ 0 <= hs_fd h < 2 ^ 31.
Hypothesis RI_fds : forall cx t m i1 i2 h1 h2,
  RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
Hypothesis RI_pair : forall cx t m si h j,
  RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
  re_skip (nth j (lm_es m) dr_e0) = hs_overlong h /\
  (re_skip (nth j (lm_es m) dr_e0) = 0 -> bzs (re_U (nth j (lm_es m) dr_e0)) = bzs (hs_W h)) /\
  length (re_pad1 (nth j (lm_es m) dr_e0)) = 4%nat /\ length (re_pad2 (nth j (lm_es m) dr_e0)) = 4%nat.
Hypothesis RI_gone : forall cx t m,
  RINV cx t m ->
  (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
  (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1).
(* B restatement (an internal work row): image A's official top_x text after the #6 cutover (window 1f8fb3038b5), B names; it
   equals the B TX_* duplicate it used to cite, up to unfolding *)
Hypothesis LS_drain_pre : forall cx t m ly S si h j,
  LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < CfParamsReply.fr_MMAX /\
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX /\
  mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
(* B restatement (an internal work row): image A's official top_x text after the #6 cutover (window 1f8fb3038b5), B names; it
   equals the B TX_* duplicate it used to cite, up to unfolding *)
Hypothesis LS_cnl_pre : forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
  LSx cx t m ly S -> RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  0 <= t < OPS_MAX -> lm_O m = [] ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpre h -> 0 <= lm_cap m ->
  (exists rest,
     Permutation (ablocks TfibB ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly' S') (aentry_blks e' ++ asrc_blks h'' ++ aout_blks cap' out' ++ rest)) ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epost (nth j (lm_es m) dr_e0) e' h -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpost h h'' ->
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h'')) (hl_recs (hs_expected h'')) /\
  mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h'')) /\
  W_rep.AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.
Hypothesis LS_drain_skip : forall cx t m ly S,
  LSx cx t m ly S -> LSx cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
(* B restatement (an internal work row): image A's official top_x text after the #6 cutover (window 1f8fb3038b5), B names; it
   equals the B TX_* duplicate it used to cite, up to unfolding *)
Hypothesis LS_drain_step : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  LSx cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  (exists rest,
     Permutation (ablocks TfibB ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks TfibB ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks TfibB ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_kh (nth j (lm_es m) dr_e0) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpre h -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epost (nth j (lm_es m) dr_e0) e' h -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_hpost h h1 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_dpost m j h e' h1 -> W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_cpost h1 E' H' ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
(* B twin to come: none: A's ReplyTrPeakCnl.cnl_pk term is dr_cnl_pk := ReplyB3TrPeakCnl.dr_cnl_pk_B. Text = image A's top step (W8 a working branch 14fbe276057) verbatim, B names *)
Hypothesis DR_CNT_cnl : forall (h h'' : hsrc) (P : Z -> bool),
  hl_recs (hs_expected h) = [] ->
  map snd (hl_recs (hs_expected h'')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  (Z.to_nat (ReplyCnt.tr_peakP P (cnl_tr (hs_expected h'') (hs_held h''))) <= dr_cnl_pk h P)%nat.
(* B twin to come: none (msz_ok is a Theorem Labs lane's lib/B/W_LLVMFuzzerTestOneInput_drain_defs_x.v:92); none: A's ReplyTrPeakCnl.cnl_pk term is dr_cnl_pk := ReplyB3TrPeakCnl.dr_cnl_pk_B. Text = image A's top step (W8 a working branch 14fbe276057) verbatim, B names *)
Hypothesis LS_cnt_drain : forall cx t m ly S si h j,
  LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.msz_ok m -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  cnt_ok_pk RPi
    (fun P => (Z.to_nat (ReplyCnt.tr_peakP P
       (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)) +
       (dr_cnl_pk h P + 2))%nat)
    (ablocks TfibB ly S).

(* ---- the four small arms' model rules (_small_x.v), verbatim at the instance; the AR file's model functions
   qualified ---- *)
Hypothesis RI_close : forall cx t m i, RINV cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_close cx m i).
Hypothesis RI_eintr : forall cx t m i, RINV cx t m ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_eintr cx m i).
Hypothesis RI_sendmax : forall cx t m, RINV cx t m ->
  RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)).
Hypothesis RI_default : forall cx t m, RINV cx t m -> RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_default cx m (W_LLVMFuzzerTestOneInput_small.sm_dg cx m)).
Hypothesis LS_close : forall cx t m i ly S, LSx cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_close cx m i) ly S.
Hypothesis LS_eintr : forall cx t m i ly S, LSx cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_eintr cx m i) ly S.
Hypothesis LS_sendmax : forall cx t m ly S, LSx cx t m ly S ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Hypothesis LS_default : forall cx t m ly S, LSx cx t m ly S -> LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_default cx m (W_LLVMFuzzerTestOneInput_small.sm_dg cx m)) ly S.

(* ---- ARM_add's model rules (lib/B/W_LLVMFuzzerTestOneInput_add_x.v), verbatim at the instance; the AR files'
   model functions qualified ---- *)
Hypothesis RI_add_pre : forall cx t m,
  RINV cx t m -> 0 <= t < OPS_MAX -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m -> W_op_add.oa_first (W_LLVMFuzzerTestOneInput_add.ad_os (lm_hs m)) <> None ->
  (length (lm_es m) < 4)%nat /\ ~ In (100 + lm_nfd m) (map re_fd (lm_es m)) /\ lm_nfd m < OPS_MAX.
Hypothesis RI_add_open : forall cx t m i q pj ev,
  RINV cx t m -> 0 <= t < OPS_MAX -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m -> W_op_add.oa_first (W_LLVMFuzzerTestOneInput_add.ad_os (lm_hs m)) = Some i ->
  Z.of_nat (length pj) = APARTIAL -> 0 <= ev < 2 ^ 32 ->
  RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_add.ad_open m i q pj ev).
Hypothesis RI_add_none : forall cx t m,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m -> W_op_add.oa_first (W_LLVMFuzzerTestOneInput_add.ad_os (lm_hs m)) = None -> RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_add.ad_none m).
Hypothesis LS_add_room : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m ->
  blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok MT S (W_op_add.oa_cost MT).
Hypothesis LS_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m -> W_op_add.oa_first (W_LLVMFuzzerTestOneInput_add.ad_os (lm_hs m)) = Some i ->
  mo_le MT S S' (W_op_add.oa_cost MT) -> Permutation (ablocks TfibB ly' S') ((q, APARTIAL) :: ablocks TfibB ly S) ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_add.ad_open m i q pj ev) ly' S'.
Hypothesis LS_add_none : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m -> W_op_add.oa_first (W_LLVMFuzzerTestOneInput_add.ad_os (lm_hs m)) = None ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_add.ad_none m) ly S.
(* B twin to come: lib/B/W_op_add.v:215 oa_peak on a working branch 24341ca6749 (an internal work row, not yet on this base). Text = image A's top step (W8 a working branch 14fbe276057) verbatim, B names *)
Hypothesis LS_cnt_add : forall cx t m ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_add.ad_at_op cx m -> amodel_at TfibB ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RPi W_op_add.oa_peak (ablocks TfibB ly S).
(* ---- ARM_write's model rules (lib/B/W_LLVMFuzzerTestOneInput_write_x.v), verbatim at the instance; the AR files'
   model functions qualified ---- *)
Hypothesis RI_write_skip : forall cx t m,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  (pick (lm_hs m) (W_LLVMFuzzerTestOneInput_write.wr_kb cx m) = None \/ W_LLVMFuzzerTestOneInput_write.wr_n cx m = 0) ->
  RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_skip m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m)).
Hypothesis LS_write_skip : forall cx t m ly S,
  LSx cx t m ly S -> LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_skip m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m)) ly S.
Hypothesis RI_write_push : forall cx t m si h l' d ev,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> in_byte cx (lm_k m) mod 10 = 1 ->
  W_LLVMFuzzerTestOneInput_write.wr_pick cx m si h -> 0 < W_LLVMFuzzerTestOneInput_write.wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, W_LLVMFuzzerTestOneInput_write.wr_x cx m)] ->
  hl_cap l' = ListRep.grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  0 <= ev < 2 ^ 32 ->
  RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_push m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m) si (W_LLVMFuzzerTestOneInput_write.set_pending h l') ev).
Hypothesis LS_write_room : forall cx t m si h ly S,
  LSx cx t m ly S -> W_LLVMFuzzerTestOneInput_write.wr_pick cx m si h -> 0 < W_LLVMFuzzerTestOneInput_write.wr_n cx m ->
  (W_contract.lp_grow (hs_pending h) = true -> W_contract.lp_vbytes (hs_pending h) < W_LLVMFuzzerTestOneInput_write.WR_MMAX) /\
  blocks_bytes S + (if W_contract.lp_grow (hs_pending h) then W_contract.lp_vbytes (hs_pending h) else 0) + (W_LLVMFuzzerTestOneInput_write.wr_n cx m + 1) <= LIVE_MAX /\
  mo_ok MT S (W_contract.lp_cost MT (hs_pending h) (W_LLVMFuzzerTestOneInput_write.wr_n cx m)).
(* KF-COUNT F5 (A 00c059c932f): `0 <= t < OPS_MAX` last *)
Hypothesis LS_write_push : forall cx t m si h (l' : hlist) d ev ly S ly' S',
  LSx cx t m ly S -> W_LLVMFuzzerTestOneInput_write.wr_pick cx m si h -> 0 < W_LLVMFuzzerTestOneInput_write.wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, W_LLVMFuzzerTestOneInput_write.wr_x cx m)] ->
  hl_cap l' = ListRep.grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (W_contract.lp_grow (hs_pending h) = false -> HarnessRep.hl_v l' = HarnessRep.hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks TfibB ly S)
       ((if W_contract.lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(HarnessRep.hl_v (hs_pending h), W_rep.AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks TfibB ly' S')
       ((d, Z.of_nat (length (W_LLVMFuzzerTestOneInput_write.wr_x cx m)) + 1) ::
        (if W_contract.lp_grow (hs_pending h) then [(HarnessRep.hl_v l', W_rep.AREC * hl_cap l')] else []) ++ rest)) ->
  mo_le MT S S' (W_contract.lp_cost MT (hs_pending h) (W_LLVMFuzzerTestOneInput_write.wr_n cx m)) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_push m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m) si (W_LLVMFuzzerTestOneInput_write.set_pending h l') ev) ly' S'.
(* NEW from image A's top step (W8 14fbe276057), B names *)
Hypothesis LS_cnt_write : forall cx t m si h ly S (W : world segs) mem,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_write.wr_pick cx m si h -> 0 < W_LLVMFuzzerTestOneInput_write.wr_n cx m -> amodel_at TfibB ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RPi (lp_peak (hs_pending h) (W_LLVMFuzzerTestOneInput_write.wr_n cx m)) (ablocks TfibB ly S).

(* ---- ARM_remove's callee contracts and instance facts no lib/B lemma gives at ARX, and its model rules
   (lib/B/W_LLVMFuzzerTestOneInput_remove_x.v), verbatim at the instance, MMAX := fr_MMAX; the AR file's model functions
   qualified.  Its CNL is the plain gx_ok form (no gx_rt / rom_out premise), unlike ARM_drain's CNL_x. ---- *)
Hypothesis RRDS_x : forall W ly S Hp (regs : bvmap 5 word) mem md ch T es HA h,
  afn_pre_x segs TfibB ARX RRDS_STK ly S Hp W regs mem md ch ->
  getr regs 10 = w64 HA -> 0 < HA -> HA mod 8 = 0 -> azs TfibB HA 4 ->
  asrc_at TfibB ly S W mem HA h ->
  arelay_at TfibB fr_RG ly S W mem T es -> rom_view segs W mem ->
  SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_reads) regs mem md)
    (aleafx_post_x TfibB [] ARX RRDS_STK regs ly S Hp W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = hs_fd h /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> hs_fd h) /\
            a0 = w64 (if re_eof e =? 0 then 1 else 0)) \/
         ((forall e, In e es -> re_fd e <> hs_fd h) /\ a0 = w64 0))).
(* B restatement (an internal work row): image A's top step (W8 14fbe276057) room text - RPi after MT (A: at RP := RPi) *)
Hypothesis RR_x : rr_spec_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG YCk0.CTX_AFREE (BASE + AF_fr_relay_remove).
(* B restatement (an internal work row): RPi after MT, the room kit's signature (A's top step 14fbe276057 builds CNL_rm_x at RPi in its proof) *)
Hypothesis CNL_rm_x : forall G, gx_ok segs TfibB G -> cnl_spec_x TfibB [] ARX MT RPi G CfParamsReply.fr_MMAX (BASE + AF_fr_check_no_loss).
Hypothesis RGP_x : rg_place TfibB fr_RG.
Hypothesis RI_rm_found : forall cx t m si h,
  RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 4 ->
  pick (lm_hs m) (W_LLVMFuzzerTestOneInput_remove.rm_kb cx m) = Some si -> nth si (lm_hs m) None = Some h ->
  exists j, (j < length (lm_es m))%nat /\ re_fd (W_LLVMFuzzerTestOneInput_remove.rm_ent m j) = hs_fd h.
Hypothesis RI_rm_rr_pair : forall cx t m si h j0,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 ->
  re_skip (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = hs_overlong h /\ (re_skip (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 -> bzs (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) = bzs (hs_W h)).
(* B-only (a Theorem Labs lane's B remove arm, a working branch f42b3777c7b remove_x.v:194-195): the picked slot's
   expected list is empty at remove's entry *)
Hypothesis RI_rm_src : forall cx t m si h j0,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> hl_recs (hs_expected h) = [].
(* B restatement (an internal work row): image A's top step text (W8 a working branch 14fbe276057), B names *)
Hypothesis LS_rm_rr_pre : forall cx t m ly S si h j0,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  (re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= LIVE_MAX /\
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h) /\ lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) + 4 * Z.max (lm_cap m) (tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) <= LIVE_MAX.
(* B restatement: A's RIRS text (3f40808c334) = a Theorem Labs lane's RI_rm_cnl_pre_K14_holds (a working branch
   b85392ed89c, lib/B/ReplyRINVB_rm_a12.v:1144) *)
Hypothesis RI_rm_cnl_pre : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  Forall (fun e => Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys e)) (lm_es m) ->
  NoDup (texts (hs_held h1)) /\ hl_n (hs_expected h1) < 2 ^ 26 /\
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 /\
  W_rep.AREC * capb (hs_held h1) (hs_expected h1) < 2 ^ 32 /\ Z.of_nat (length O2) < 2 ^ 32 /\
  (lm_gn m = 0 -> exists rest, O2 = bstream (hs_expected h1) ++ rest).
(* B restatement (an internal work row): image A's official top_x text after the #6 cutover (window 1f8fb3038b5), B names; it
   equals the B TX_* duplicate it used to cite, up to unfolding *)
(* KF-COUNT F9 (A aacecd50fed): after rm_rr_ok, the arm's t bound and the removed entry's partial-line bound
   (rm3_pre); the same for LS_rm_cshe_pre / LS_rm_sr_pre, and LS_rm_step takes the partial-line bound after LSx *)
Hypothesis LS_rm_cnl_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  LSx cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S) (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) /\
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1)).
(* B restatement: = a Theorem Labs lane's RI_rm_cshe_pre_nz_holds (b85392ed89c, ReplyRINVB_rm_a12.v:1157) *)
Hypothesis RI_rm_cshe_pre : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  lm_gn m = 0 ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H') ->
  W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1 <= Z.of_nat (length O2) /\
  ends_run [] (hl_recs H') (skipn (Z.to_nat (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1)) O2) (want_of [] (hl_recs H')) <> None.
Hypothesis LS_rm_cshe_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  LSx cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1)) ->
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H').
(* B restatement: = a Theorem Labs lane's RI_rm_csd_gn_holds (b85392ed89c, ReplyRINVB_rm_a12.v:1169) *)
Hypothesis RI_rm_csd : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  0 <= lm_gn m <= 1 ->
  W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1 + cc = Z.of_nat (length O2).
Hypothesis LS_rm_sr_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  LSx cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' -> W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H') ->
  mo_ok MT S (sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))).
Hypothesis RI_rm_step : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2).
(* B restatement (an internal work row): image A's official top_x text after the #6 cutover (window 1f8fb3038b5), B names; it
   equals the B TX_* duplicate it used to cite, up to unfolding *)
Hypothesis LS_rm_step : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  LSx cx t m ly0 S0 ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S)
       (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S.
(* B twin to come: lib/B/W_LLVMFuzzerTestOneInput_remove_x.v's rm_pk (an internal work row, a Theorem Labs lane). Text = image A's top step (W8 a working branch 14fbe276057) verbatim, B names *)
Hypothesis LS_cnt_remove : forall cx t m ly S (W : world segs) mem si h j0,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> amodel_at TfibB ly S W mem m -> 0 <= t < OPS_MAX ->
  cnt_ok_pk RPi (W_LLVMFuzzerTestOneInput_remove_x.rm_pk m h j0) (ablocks TfibB ly S).
(* B twin to come: lib/B/W_LLVMFuzzerTestOneInput_remove_x.v's rm_pk (an internal work row, a Theorem Labs lane). Text = image A's top step (W8 a working branch 14fbe276057) verbatim, B names *)
(* B arm's text (weaker than A's: its extra premises are B-forced), adopted from the arm of record *)
Hypothesis RM_CNT_cnl : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 (P : Z -> bool),
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_mfacts m ->
  W_LLVMFuzzerTestOneInput_remove_x.rm3_pre (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2)) +
     W_contract_x.cnl_pk (hs_expected h1) (hs_held h1) P <= ReplyCnt.acnt P (model_blks m) + W_LLVMFuzzerTestOneInput_remove_x.rm_pk m h j0 P)%nat.
(* B twin to come: lib/B/W_LLVMFuzzerTestOneInput_remove_x.v's rm_pk (an internal work row, a Theorem Labs lane). Text = image A's top step (W8 a working branch 14fbe276057) verbatim, B names *)
(* B arm's text (weaker than A's: its extra premises are B-forced), adopted from the arm of record *)
Hypothesis RM_CNT_cshe : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' (P : Z -> bool),
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_mfacts m -> W_LLVMFuzzerTestOneInput_remove_x.rm3_pre (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some (set_exp_held h1 E' H')) j0 c2 O2 cap2 out2)) +
     W_contract_x.cshe_pk P <= ReplyCnt.acnt P (model_blks m) + W_LLVMFuzzerTestOneInput_remove_x.rm_pk m h j0 P)%nat.
(* B twin to come: lib/B/W_LLVMFuzzerTestOneInput_remove_x.v's rm_pk (an internal work row, a Theorem Labs lane). Text = image A's top step (W8 a working branch 14fbe276057) verbatim, B names *)
(* B arm's text (weaker than A's: its extra premises are B-forced), adopted from the arm of record *)
Hypothesis RM_CNT_sr : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc (P : Z -> bool),
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc -> W_LLVMFuzzerTestOneInput_remove.rm_mfacts m ->
  W_LLVMFuzzerTestOneInput_remove_x.rm3_pre (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) h -> hl_recs (hs_expected h) = [] ->
  (ReplyCnt.acnt P (model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some (set_held (set_exp_held h1 E' H') H'')) j0 c2 O2 cap2 out2)) +
     W_contract_x.sr_pk P <= ReplyCnt.acnt P (model_blks m) + W_LLVMFuzzerTestOneInput_remove_x.rm_pk m h j0 P)%nat.
(* ---- ARM_event's callee contracts and model rules (lib/B/W_LLVMFuzzerTestOneInput_event_x.v), verbatim at the
   instance, MMAX := fr_MMAX; ASTRNLEN_x is lib/Rt/RTx.v:155 astrnlen_whole_realizes_x (a Theorem Labs lane's event arm cites it in
   place of its old local et_strnlen_spec_x, the same body; a Theorem Labs lane's B RT base);
   RI_event_live is RI_gone's text and is not restated ---- *)
(* B restatement (an internal work row): image A's top step (W8 14fbe276057) room text - RPi after MT (A: at RP := RPi) *)
Hypothesis AFREE_x : afree_cf_rule_c_x segs TfibB [] ARX MT RPi YCk0.CTX_AFREE.
(* SL_x is built in the proof from a Theorem Labs lane's lib/B/W_send_line_x.pb_send_line_x (a working branch
   44b8b79e165f), by a1-a2's paste block (a working branch 721fe29b1f24, ZZSlTopxScratch.v:128-186) *)
Hypothesis ASTRNLEN_x : RTx.astrnlen_whole_realizes_x segs TfibB ARX (pa_sigma WS_strnlen).
(* B restatement (an internal work row): RPi after MT, the room kit's signature (A's top step 14fbe276057 builds RE_x at RPi in its proof) *)
Hypothesis RE_x : re_spec_x (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX (W_LLVMFuzzerTestOneInput_arm_event.et_GRE TfibB) fr_RG (BASE + AF_fr_relay_event).
Hypothesis CSE_x : cse_spec_x (PI := PB_fr) TfibB [] ARX (BASE + AF_fr_check_shape_event).
Hypothesis RI_event_step : forall cx t m e v out',
  RINV cx t m -> 0 <= lm_k m < c_n cx -> lm_O m = [] -> in_byte cx (lm_k m) mod 10 = 7 ->
  W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e -> 0 <= v < 2 ^ 32 ->
  RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_arm_event.ev_step cx m e v out').
Hypothesis LS_event_malloc : forall cx t m ly S e,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  re_len e < CfParamsReply.fr_MMAX /\ blocks_bytes S + re_len e <= LIVE_MAX /\ mo_ok MT S (mo_malloc MT (re_len e)).
(* B restatement (an internal work row): image A's top step text (W8 a working branch 14fbe276057), B names *)
Hypothesis LS_event_relay : forall cx t m ly S (S1 : astate) e (ly1 : alayout) q,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  lm_O m = [] ->
  ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
  sl_maxr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) < CfParamsReply.fr_MMAX /\
  blocks_bytes S1 + sl_alloc (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= LIVE_MAX /\
  mo_ok MT S1 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)).
(* KF-COUNT F7 (a Theorem Labs lane 11:17Z, s5-r1d): `lm_O m = [] ->` after ev_evt, as LS_event_relay; the event arm holds it
   (event_x.v:2228, the HO it passes to LS_event_step) *)
Hypothesis LS_event_free : forall cx t m ly S (S1 S2 : astate) e,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e -> lm_O m = [] ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_ok MT S2 (mo_free MT).
(* KF-COUNT F5 (A 00c059c932f): s5's TX_LS_event_step (ReplyB3LS3cTopxPost.v:122) plus `0 <= t < OPS_MAX` last,
   inline since the TX definition has no t premise *)
Hypothesis LS_event_step : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  LSx cx t m ly S -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks TfibB ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks TfibB ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks TfibB ly3 S3 = l1 ++ l2) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_arm_event.ev_step cx m e v out') ly3 S3.
(* NEW from image A's top step (W8 14fbe276057), B names *)
Hypothesis LS_cnt_event : forall cx t m ly S e,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  Forall (fun e0 => 0 <= re_cap e0 <= 16384 /\
    Forall (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e0)) (lm_es m) /\
  Forall (fun o => match o with
                   | Some h => Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs (hs_expected h)) /\
                               Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs (hs_held h))
                   | None => True end) (lm_hs m) ->
  0 <= t < OPS_MAX ->
  (ReplyCnt.acnt (rp_Psec RPi) (ablocks TfibB ly S) + ((if rp_Psec RPi (re_len e) then 1 else 0) + 2) <= rp_Lsec RPi)%nat /\
  (ReplyCnt.acnt (rp_P24 RPi) (ablocks TfibB ly S) + ((if rp_P24 RPi (re_len e) then 1 else 0) + 2) <= rp_L24 RPi)%nat /\
  (forall c, 1 <= c <= 30 ->
     (ReplyCnt.acnt (rp_Pcls RPi c) (ablocks TfibB ly S) + ((if rp_Pcls RPi c (re_len e) then 1 else 0) + 2)
        <= rp_LPRIM RPi c)%nat).

(* ---- ARM_gone's callee contracts, instance facts at ARX and model obligations
   (lib/B/W_LLVMFuzzerTestOneInput_gone_x.v), verbatim at the instance, MMAX := fr_MMAX; the base's definitions
   qualified ---- *)
Hypothesis SNP_x : asnprintf_realizes_x TfibB ARX (pa_sigma WS_snprintf) W_sites.FR_GOT_GUARD W_sites.FR_GUARD.
Hypothesis HGOTG_x : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md ->
  rdword (aview segs (w_H W) mem) W_sites.FR_GOT_GUARD = Some W_sites.FR_GUARD.
Hypothesis GN_LIT_GES_x : ashp_x (PI := PB_fr) ARX (VAL W_contract.A_lit_gesture) 14.
Hypothesis GN_LIT_FMT_x : ashp_x (PI := PB_fr) ARX (VAL (A_OBJ 17)) 7.
(* B restatement (an internal work row): image A's top step (W8 14fbe276057) room text - RPi after MT (A: at RP := RPi) *)
Hypothesis RIG_x : rig_spec_x (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG YCk0.CTX_AFREE
  (BASE + AF_fr_relay_instance_gone).
Hypothesis GN_RI_pairs_x : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_pairs RINV.
Hypothesis GN_RI_read_x : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_read RINV.
Hypothesis GN_RI_step_x : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step TfibB MT LSx RINV CfParamsReply.fr_MMAX.
Hypothesis GN_RI_end_x : W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end TfibB MT LSx RINV.
(* Image A's top step text (W8 14fbe276057), B names: GN_CNT_rig is a Theorem Labs lane's B gone_base's; A's ReplyLScnt.pk_gone is the Variable gn_pk *)
Hypothesis CNT_gone_rig : W_LLVMFuzzerTestOneInput_gone_base.GN_CNT_rig gn_pk (fun cx m hs =>
  rig_pk (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (W_LLVMFuzzerTestOneInput_gone_base.gn_id cx m)
    (lm_es m) hs)).
(* Image A's top step text (W8 14fbe276057), B names: GN_LS_cnt_x is a Theorem Labs lane's B gone_base_x's; A's ReplyLScnt.pk_gone is the Variable gn_pk *)
Hypothesis LS_cnt_gone : W_LLVMFuzzerTestOneInput_gone_base_x.GN_LS_cnt_x TfibB LSx RINV RPi gn_pk.
(* Image A's top step text (W8 14fbe276057), B names: GN_CNT_step is a Theorem Labs lane's B gone_base's; A's ReplyLScnt.pk_gone is the Variable gn_pk *)
Hypothesis CNT_gone_step : W_LLVMFuzzerTestOneInput_gone_base.GN_CNT_step RINV gn_pk
  (fun h => cnl_pk (hs_expected h) (hs_held h)).
(* B restatement (an internal work row): image A's top step text (W8 a working branch 14fbe276057), B names *)
Hypothesis GN_LS_rig_x : forall cx t m ly S hs,
  LSx cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_gone_base.gn_pairs m hs ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
              (W_LLVMFuzzerTestOneInput_gone_base.gn_id cx m) (lm_es m) hs in
  tr_max tr < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak tr <= LIVE_MAX /\ mo_ok MT S (tr_cost MT tr) /\
  lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak tr + 4 * Z.max (lm_cap m) (tr_max tr) <= LIVE_MAX.

(* ---- the segments still at the instance, cut_x's text (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v Section w) ---- *)

Theorem fr_contract_top_x :
  @fr_lib_contract_cf_x fx rc SK checksum_shape TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv
    LIBROOM NP G fr_FP [] ARX.
Proof.
  pose proof top_HEV as HEV.
  pose proof (c_HZS TfibB TfibB_syms) as HZS.
  assert (HPST : forall a, in_img segs a -> ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ H; inversion H).
  (* SEG_PRO's HFP_pro from the FP cover (A: lib/B/W_LLVMFuzzerTestOneInput_top_x.v's plug of a2's TopxEntry.hfp_pro_x; B: a Theorem Labs lane 48eff67880c) *)
  pose proof (TopxEntry.hfp_pro_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP (G_fr_c TfibB) ARX fr_FP
    (fun ly S Hp W mem md p n (H : ARX ly S Hp W mem md) =>
       TopxEntry.arcf_blk ly S Hp W mem md p n (conj (proj1 H) (proj1 (proj2 H)))) FPCOV) as HFP_pro.
  (* ASM0 / ASM1 at top_x's relation: a Theorem Labs lane's lib/B/AsmTopX.v:174 asm0_pres_ARX and :115 asm1_pres_ARX
     (a working branch ed305db9fb3; ARX_asm is ARX over tfibsegs, AsmTopX.v:169), by conversion as A's top *)
  assert (ASM0 : astack_malloc_pres_x segs TfibB ARX 0) by exact AsmTopX.asm0_pres_ARX.
  assert (ASM1 : astack_malloc_pres_x segs TfibB ARX 1) by exact AsmTopX.asm1_pres_ARX.
  (* the pthread mutex contracts at ARX: a Theorem Labs lane's TopX_RT_lock.v:70 / :74 (G-BLOCK e1fae7037354; ARX_rt is ARX
     over segs, :57), by conversion as A's top (TopX_RT.topx_ALOCK / topx_AUNLOCK) *)
  assert (ALOCK : alock_realizes_x (PI := PB_fr) TfibB ARX (SIGMA WS_pthread_mutex_lock)) by exact TopX_RT_lock.topx_ALOCK_W.
  assert (AUNLOCK : aunlock_realizes_x (PI := PB_fr) TfibB ARX (SIGMA WS_pthread_mutex_unlock))
    by exact TopX_RT_lock.topx_AUNLOCK_W.
  assert (ASTRLEN_x : astrlen_realizes_x TfibB ARX (SIGMA WS_strlen)) by exact TopX_RT_B2.topx_ASTRLEN_B_W.
  (* a live cf block's size: AR_blocks_law_cf's last conjunct (0 <= n < cf_malloc_max) and YG08cf's bound (a12's
     W_bx_inst_x.v bxi_BLK_cf, at the instance) *)
  assert (BLKR : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
    0 <= n < 2 ^ 30).
  { intros ly S Hp W mem md p n H Hin.
    destruct (YG0dcf.alc_blocks _ _ (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB) ly S Hp W mem md p n (proj1 H) Hin)
      as (_ & _ & _ & _ & _ & _ & Hn).
    pose proof (YG08cf.cf_malloc_max_bound (cp := CfParams_reply)) as Hb. lia. }
  assert (BLKN : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
    0 <= n) by (intros ly S Hp W mem md p n H Hin; exact (proj1 (BLKR ly S Hp W mem md p n H Hin))).
  assert (BLKM : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
    n < 2 ^ 30) by (intros ly S Hp W mem md p n H Hin; exact (proj2 (BLKR ly S Hp W mem md p n H Hin))).
  (* SEG_PRO's stack_malloc facts at ARX, from the cf laws (image A's top_x, the same proofs): YGcallcf.v's owned-low
     and Wf laws (WFx := Wf_cf, ARX's first projection), and YG05cf.v's stack_malloc progress and post *)
  assert (OWNLOW : ARx_owned_low_law segs TfibB ARX).
  { intros ly S Hp W mem md a H Ho.
    exact (ARx_owned_low_law_cf_x (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)
      ly S Hp W mem md a (proj1 H) Ho). }
  assert (WFL : ARx_wf_law segs ARX (Wf_cf (cp := CfParams_reply) (as_universe TfibB))).
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
  (* SEG_EXIT's instance facts (image A's top_x, the same proofs): the stack_free law over ARX (YG0tcf.v), the frame
     split after stack_free (YG05cf.v), the g_s slots' shadow hull (GSHV_x: g_s is pro_G's first range), and the stdio
     cells apart from G_fr_c (tfib_K's six ranges against G_fr_c's objects and errno, decided) *)
  assert (ASF : astack_free_law_x segs TfibB ARX).
  { intros ly S Hp W mem md mem' md' cid pos H Hin HF HO HV Hvm Hlz He HK HKEPT. unfold ARX in H |- *.
    (* W1: the arodata conjunct at mem' from the law's kept-bytes frame (a Theorem Labs lane's engine) *)
    split; [|split; [exact (proj1 (proj2 H)) |
      exact (ReplyKeptAroB.arodata_kept_B mem mem' (proj2 (proj2 H)) HKEPT)]].
    exact (YG0tcf.astack_free_law_ok_cf (cp := CfParams_reply) segs TfibB ly S Hp W mem md mem' md' cid pos (proj1 H)
      Hin HF HO HV Hvm Hlz He HK). }
  assert (SFREE : forall s cid pos, Wf_cf (cp := CfParams_reply) (as_universe TfibB) s -> In (cid, pos) (frames s) ->
    exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2).
  { intros s cid pos HWF Hin. exact (proj2 (stack_free_ok_cf (cp := CfParams_reply) _ s cid pos HWF Hin)). }
  assert (XR_GSHV : forall ly S Hp (W : world segs) mem md a n, ARX ly S Hp W mem md -> 0 < n ->
    (forall x, a <= x < a + n -> rg_s fr_RG <= x < rg_s fr_RG + 4 * ASRC) ->
    shadow_hull_vis (aview segs (w_H W) mem) a n).
  { intros ly S Hp W mem md a n H Hn Hx. apply (GSHV_x ly S Hp W mem md a n H Hn).
    intros x Hx'. unfold W_LLVMFuzzerTestOneInput_pro.pro_G. cbn [app]. apply inG_cons. left. unfold in_zr.
    cbn [fst snd]. exact (Hx x Hx'). }
  assert (HG_K : forall a, aenv_addr tfib_K a \/ ak_meta_ptr tfib_K <= a < ak_meta_ptr tfib_K + 8 \/
    ak_meta_mem tfib_K <= a < ak_meta_mem tfib_K + 8 -> 0 <= a < 2 ^ 64 /\ ~ inG G a).
  { intros a Ha.
    assert (HK : inG [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 16); (FF_canary, 8); (FF_meta_ptr, 8);
        (FF_meta_mem, 8)] a).
    { unfold aenv_addr in Ha. cbn [tfib_K ak_threaded ak_need_locks ak_ofl_lock ak_canary ak_meta_ptr ak_meta_mem] in Ha.
      unfold inG. rewrite Exists_exists.
      destruct Ha as [[-> | [-> | [Ha | Ha]]] | [Ha | Ha]];
        [ exists (A_threaded, 1) | exists (A_need_locks, 1) | exists (A_ofl_lock, 16) | exists (FF_canary, 8)
        | exists (FF_meta_ptr, 8) | exists (FF_meta_mem, 8) ];
        (split; [cbn [In]; repeat (first [left; reflexivity | right]) | unfold in_zr; cbn [fst snd]; lia]). }
    assert (Hd : forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? 2 ^ 64) &&
        forallb (fun g => (fst r + snd r <=? fst g) || (fst g + snd g <=? fst r)) (G_fr_obj ++ [(TFIB_ERRNO_B, 4)]))
      [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 16); (FF_canary, 8); (FF_meta_ptr, 8); (FF_meta_mem, 8)] = true)
      by (vm_compute; reflexivity).
    unfold inG in HK. apply Exists_exists in HK as (r & Hr & Hz). rewrite forallb_forall in Hd. specialize (Hd r Hr).
    apply andb_prop in Hd as [Eb Hd]. apply andb_prop in Eb as [E0 E1]. apply Z.leb_le in E0, E1. unfold in_zr in Hz.
    split; [lia|].
    intros HinG. unfold G_fr_c in HinG. rewrite HEV in HinG. unfold inG in HinG.
    apply Exists_exists in HinG as (g & Hg & Hzg). rewrite forallb_forall in Hd. specialize (Hd g Hg).
    unfold in_zr in Hzg. apply orb_prop in Hd as [Hd | Hd]; apply Z.leb_le in Hd; lia. }
  (* op_add at the instance (a Theorem Labs lane's ruling): W2's pb_op_add_g_x, its image facts by vm_compute at PB_fr and the
     start-up table, its two caller contexts by vm_compute at YCk0's tables (image A's top_x OA, the same proof) *)
  assert (HMMAX : APARTIAL < CfParamsReply.fr_MMAX) by (unfold APARTIAL; apply Z.ltb_lt; vm_compute; reflexivity).
  (* op_add at RPi (a Theorem Labs lane's room-form W_op_add.pb_op_add_g_x, a working branch 24341ca6749
     W_op_add.v:1949-1967): RP after MT, its RMM := rp_RMM RPi (A: lib/B/W_LLVMFuzzerTestOneInput_top_x.v at 14fbe276057 `(rp_RMM RPi)`) *)
  assert (OA : W_op_add.oa_spec_g_x (PI := PB_fr) TfibB [] ARX MT RPi (BASE + AF_fr_op_add)).
  { refine (W_op_add.pb_op_add_g_x (PI := PB_fr) TfibB [] ARX _ MT RPi ARX_laws HPST TL MLAW (rp_RMM RPi)
      CfParamsReply.fr_MMAX HMMAX
      _ _ _ _ _ YCk0.CTX_AMALLOC _ AMA_x SR_x YCk0.CTX_AREALLOC _ RA_x).
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_compute. repeat split; first [left; discriminate | right; discriminate |
        left; let H := fresh in intro H; discriminate H | right; let H := fresh in intro H; discriminate H].
    - intros a Ha. split; [|split].
      + apply (segin_ok segs). apply (rng_all_in (segin segs) [(rg_wake fr_globals + 4, 4)]); [vm_compute; reflexivity|].
        apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
      + rewrite (ts_owned TfibB TfibB_syms). intros Hex.
        assert (Hb : forallb (fun r => top_apart (fst r) (snd r) [(rg_wake fr_globals + 4, 4)]) Tfib_owned_static = true)
          by (vm_compute; reflexivity).
        apply Exists_exists in Hex as (r & Hr & Hz). rewrite forallb_forall in Hb. destruct r as [lo n].
        exact (top_apart_ok lo n _ (Hb (lo, n) Hr) a ltac:(apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia) Hz).
      + rewrite HEV. cbn [fr_globals rg_wake] in Ha. unfold TFIB_ERRNO_B. lia.
    - vm_compute. repeat (first [left; reflexivity | right]).
    - vm_compute. repeat (first [left; reflexivity | right]). }
  (* ARM_remove's instance facts: source_reset's G at each slot over ARX (B _G.v c_HGP's five plain conjuncts and the
     g_s shadow hull XR_GSHV), and the PST facts at PST = [] *)
  assert (HGP : forall si, (si < 4)%nat ->
    gx_prog_x (PI := PB_fr) TfibB ARX [(W_LLVMFuzzerTestOneInput_remove.rm_HA si, ASRC)]).
  { intros si Hsi. destruct (c_HGP TfibB TfibB_syms HEV si Hsi) as (G1 & G2 & _ & G4 & G5 & _).
    (* rom_out at the Section's sink head SK: from HRO, the slot being part of g_s, which is in G *)
    assert (Hsub : forall a, inG [(W_LLVMFuzzerTestOneInput_remove.rm_HA si, ASRC)] a -> inG G a).
    { intros a Ha. apply (c_HGs TfibB). apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
      unfold in_zr, W_LLVMFuzzerTestOneInput_remove.rm_HA in Ha. cbn [fst snd] in Ha. clear - Ha Hsi.
      unfold ASRC in *. lia. }
    split; [exact G1|]. split; [exact G2|].
    split; [intros a Ha; destruct (HRO a Ha) as (Hn & Hrest); split; [intros Hin; exact (Hn (Hsub a Hin)) | exact Hrest]|].
    split; [exact G4|]. split; [exact G5|].
    intros ly S Hp W mem md a n HAR Hn Hx. apply (XR_GSHV ly S Hp W mem md a n HAR Hn).
    intros x Hx'. specialize (Hx x Hx'). apply inG_cons in Hx as [Hx | Hx]; [|exfalso; exact (inG_nil x Hx)].
    unfold in_zr, W_LLVMFuzzerTestOneInput_remove.rm_HA in Hx. cbn [fst snd] in Hx. clear - Hx Hsi. unfold ASRC in *.
    lia. }
  assert (PST_ROM : forall a, in_rom segs a -> ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ H; inversion H).
  assert (PST_IMG : forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static TfibB) ->
    ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ _ H; inversion H).
  (* ARM_event's G facts: every range of the tail's carried globals (the AR file's et_GL) is one of G_fr_c's objects,
     and none holds errno's cell (decided) *)
  assert (HG_carry : forall a, inG W_LLVMFuzzerTestOneInput_arm_event.et_GL a -> inG G a).
  { apply inG_sub. unfold W_LLVMFuzzerTestOneInput_arm_event.et_GL.
    repeat (apply Forall_cons; [intros a Ha; apply obj_c; revert a Ha; apply rng_cover_zr; vm_compute; reflexivity|]).
    apply Forall_nil. }
  assert (HERR_AP : forall a, inG W_LLVMFuzzerTestOneInput_arm_event.et_GL a -> ~ (as_errno TfibB <= a < as_errno TfibB + 4)).
  { rewrite HEV. apply W_LLVMFuzzerTestOneInput_G.apart_of_b. vm_compute. reflexivity. }
  (* ARM_gone's instance facts over ARX: check_no_loss / check_shape_ends at each slot's own G (gn_Gs j, inside g_s, so
     in G: CNL_rm_x / CSHE_x through gx_ok_sub), and the fake frames' alignment (YG0scf.v frame_facts_cf on ARX's ARmcf) *)
  assert (HGN : forall j, (j < 4)%nat -> gx_ok segs TfibB (W_LLVMFuzzerTestOneInput_gone_base.gn_Gs j)).
  { intros j Hj. apply (W_journal.gx_ok_sub segs TfibB _ G); [|exact GX_ok].
    intros a Ha. apply (c_HGs TfibB). unfold W_LLVMFuzzerTestOneInput_gone_base.gn_Gs in Ha.
    apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)]. unfold in_zr in Ha. cbn [fst snd] in Ha.
    clear - Ha Hj. unfold ASRC in *. lia. }
  assert (GN_CNL : W_LLVMFuzzerTestOneInput_gone_base_x.GN_CNL_x TfibB MT [] ARX CfParamsReply.fr_MMAX RPi)
    by (intros j Hj; exact (CNL_rm_x _ (HGN j Hj))).
  assert (GN_CSHE : W_LLVMFuzzerTestOneInput_gone_base_x.GN_CSHE_x TfibB MT [] ARX RPi)
    by (intros j Hj; exact (CSHE_x _ (HGN j Hj))).
  assert (FRMF : forall ly S Hp (W : world segs) mem md cid pos, ARX ly S Hp W mem md -> In (cid, pos) (frames S) ->
    ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0).
  { intros ly S Hp W mem md cid pos [[M _] _] Hin.
    destruct (YG0scf.frame_facts_cf (cp := CfParams_reply) TfibB ly S Hp _ cid pos M Hin)
      as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & H64 & Hb & _).
    split; [exact Hpg|]. split; [exact Hoff|]. split; [exact H64 | exact Hb]. }
  (* ARM_drain's G fact no _G.v lemma states in its form: every range of its global list is one of G_fr_c's 20
     objects (image A's top_x HG_GK proof) *)
  assert (HG_GK : forall a, inG [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4);
    (rg_send_max fr_RG, 8); (rg_client fr_RG, 4); (rg_send_dead fr_RG, 1); (rg_gone fr_RG, 1);
    (rg_wake fr_RG, 8); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] a -> inG G a).
  { apply inG_sub.
    repeat (apply Forall_cons; [intros a Ha; apply obj_c; revert a Ha; apply rng_cover_zr; vm_compute; reflexivity|]).
    apply Forall_nil. }
  (* list_push at the instance as a named fact (A: lib/B/W_LLVMFuzzerTestOneInput_top_x.v:1171 at fb66907d92b), a Theorem Labs lane's B
     W_list_push.pb_list_push_g_x at WR_MMAX; the write arm and the drain contract take it *)
  assert (LP : lp_spec_g_x (PI := PB_fr) TfibB [] ARX MT RPi W_LLVMFuzzerTestOneInput_write.WR_MMAX
    (BASE + AF_fr_list_push)).
  { exact (W_list_push.pb_list_push_g_x TfibB [] ARX ARX_laws ARX_hp0 TL MT RPi MLAW W_LLVMFuzzerTestOneInput_write.WR_MMAX
           W_LLVMFuzzerTestOneInput_write.wr_HMMAX (W_img_x.fr_img_cover_x TfibB ARX ARX_laws) BLKN YCk0.CTX_AREALLOC ARE_x
           ltac:(vm_compute; repeat (first [left; reflexivity | right])) YCk0.CTX_AMALLOC AMA_x
           ltac:(vm_compute; repeat (first [left; reflexivity | right])) AMEMCPY_x). }
  (* ---- SL_x at RPi: lib/B/W_send_line_x.v pb_send_line_x, its Section premises (W_send_line_cx_x.v:90-137) closed
     from top_x's ARX facts, its hypotheses TL / MLAW / HRO / ARE_x / AMEMCPY_x, TopX_RT4 (errno_location),
     W_errno_azs (errno's zero shadow), _G.v's G_fr_c facts, and the placements decided at PB_fr / fr_RG / TfibB ---- *)
  assert (SL_x : sl_spec_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG (BASE + AF_fr_send_line)).
  { (* HG / HROMO: G_SL inside G_fr_c (top_x's GSE_x block, top_x.v:926-930) *)
    assert (HG0 : gx_ok segs TfibB (G_SL TfibB fr_RG)).
    { apply (W_journal.gx_ok_sub segs TfibB _ (G_fr_c TfibB)); [exact (c_HG_SL TfibB) | exact GX_ok]. }
    assert (HROMO0 : rom_out segs TfibB (G_SL TfibB fr_RG)).
    { intros a Ha. destruct (HRO a Ha) as (H1 & H2 & H3 & H4).
      split; [intros HGa; exact (H1 (c_HG_SL TfibB a HGa))|]. exact (conj H2 (conj H3 H4)). }
    (* HGR: no byte of G_SL is read-only (_G.v c_rom_apart through c_HG_SL) *)
    assert (HGR0 : forall a, inG (G_SL TfibB fr_RG) a -> ~ in_rom segs a).
    { intros a Hg Hr. exact (c_rom_apart TfibB HEV a Hr (c_HG_SL TfibB a Hg)). }
    (* HGO: the three entry cells are objects of G_fr_c (top_x's HG_GK proof, top_x.v:921-923) *)
    assert (HGO0 : gx_ok segs TfibB [(rg_client fr_RG, 4); (rg_send_dead fr_RG, 1); (rg_send_max fr_RG, 8)]).
    { apply (W_journal.gx_ok_sub segs TfibB _ (G_fr_c TfibB)); [|exact GX_ok].
      apply inG_sub.
      repeat (apply Forall_cons; [intros a Ha; apply obj_c; revert a Ha; apply rng_cover_zr; vm_compute; reflexivity|]).
      apply Forall_nil. }
    (* AERRNO: G-BRT4's errno_location at TopX_RT_lock.ARX_rt, top_x's ARX verbatim (by conversion, as top_x.v:775
       takes ALOCK from TopX_RT_lock) *)
    assert (AERRNO0 : aerrno_realizes_x (PI := PB_fr) TfibB ARX (SIGMA WS_errno_location))
      by exact TopX_RT4.topx_AERRNO_W.
    (* AREALLOC: ARE_x, whose WR_MMAX is CfParamsReply.fr_MMAX by conversion (ReplyB3LS3Peak.pk_fr_MMAX) *)
    assert (AREALLOC0 : W_journal_x.arealloc_cf_rule_c_x segs TfibB [] ARX MT CfParamsReply.fr_MMAX RPi
      YCk0.CTX_AREALLOC (pa_sigma WS_realloc)) by exact ARE_x.
    (* HCTX_slr: send_line's realloc returns to 0x829f4, CTX_AREALLOC's first row (YCk0.v:35) *)
    assert (HCTX_slr0 : In [BASE + AF_fr_send_line + 0x1a0] YCk0.CTX_AREALLOC)
      by (vm_compute; repeat (first [left; reflexivity | right])).
    (* errno: tp - 164, its zero shadow (YF0m's range, W_errno_azs), its four bytes writable (G_fr_c holds them: _G.v
       err_c / c_glob_wr at the empty hidden set), 4-aligned *)
    assert (HERRNO0 : as_errno TfibB = as_tp TfibB - 164) by (vm_compute; reflexivity).
    pose proof (W_errno_azs.errno_azs TfibB TfibB_syms) as HERRZ0.
    assert (HERRW0 : forall i, 0 <= i < 4 -> writable_at segs (fun _ => None) (as_errno TfibB + i)).
    { intros i Hi.
      exact (c_glob_wr TfibB HEV (fun _ => false) (fun _ => None) (as_errno TfibB + i)
        (err_c TfibB (as_errno TfibB + i) ltac:(lia))). }
    assert (HERRAL0 : as_errno TfibB mod 4 = 0) by (vm_compute; reflexivity).
    (* the placements: listing objects and kept auipc values against fr_RG, decided *)
    assert (HV9 : VAL (A_OBJ 9) = rg_client fr_RG) by (vm_compute; reflexivity).
    assert (HV10 : VAL (A_OBJ 10) = rg_client_broken fr_RG) by (vm_compute; reflexivity).
    assert (HV11 : VAL (A_OBJ 11) = rg_send_eintr fr_RG) by (vm_compute; reflexivity).
    assert (HV12 : VAL (A_OBJ 12) = rg_nout fr_RG) by (vm_compute; reflexivity).
    assert (HH18 : VAL (A_HI 18) + 1212 = rg_client_broken fr_RG) by (vm_compute; reflexivity).
    assert (HH20 : VAL (A_HI 20) + 1372 = rg_send_eintr fr_RG) by (vm_compute; reflexivity).
    assert (HH21 : VAL (A_HI 21) + 1328 = rg_send_dead fr_RG) by (vm_compute; reflexivity).
    assert (HH22 : VAL (A_HI 22) + 1252 = rg_send_max fr_RG) by (vm_compute; reflexivity).
    assert (HH23 : VAL (A_HI 23) + 1372 = rg_nout fr_RG) by (vm_compute; reflexivity).
    assert (HH24 : VAL (A_HI 24) + 1976 = rg_capout fr_RG) by (vm_compute; reflexivity).
    assert (HH25 : VAL (A_HI 25) + 2000 = rg_out fr_RG) by (vm_compute; reflexivity).
    assert (HRGD : zpairwise_disjoint
      [(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
       (rg_client fr_RG, rg_client fr_RG + 4); (rg_client_broken fr_RG, rg_client_broken fr_RG + 1);
       (rg_send_eintr fr_RG, rg_send_eintr fr_RG + 1); (rg_send_dead fr_RG, rg_send_dead fr_RG + 1);
       (rg_send_max fr_RG, rg_send_max fr_RG + 8); (rg_nout fr_RG, rg_nout fr_RG + 8);
       (rg_capout fr_RG, rg_capout fr_RG + 8); (rg_out fr_RG, rg_out fr_RG + 8);
       (as_errno TfibB, as_errno TfibB + 4)]).
    { vm_compute; repeat split; first [left; discriminate | right; discriminate |
        left; let H := fresh in intro H; discriminate H | right; let H := fresh in intro H; discriminate H]. }
    pose proof ARX_laws as LAWS. pose proof ARX_hp0 as HP0.
    eapply (W_send_line_x.pb_send_line_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG)
      with (CTX_R := YCk0.CTX_AREALLOC); eassumption. }
  (* ---- DR_x at RPi, as image A's top (W8 fb66907d92b :1181-1199): a Theorem Labs lane's B pb_drain_x from top_x's own facts
     (MLAW, ARE_x / AFREE_x / ASTRNDUP_x at their contexts, SL_x, LP, BLKN, BLKM), a Theorem Labs lane's B TopX_RT3 (AMEMMOVE,
     AMEMCHR), TopX_RT4 (AERRNO, ASTRRCHR, ASTRNCMP, ASTRCMP), TopxDrainLitB (HLIT5-7) and W_drain_pb's instance facts ---- *)
  assert (DR_x : dr_spec_x (PI := PB_fr) TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG (BASE + AF_fr_drain)).
  { pose proof ARX_laws. pose proof ARX_hp0.
    pose proof TopX_RT3.topx_AMEMMOVE_W. pose proof TopX_RT3.topx_AMEMCHR_W.
    pose proof TopX_RT4.topx_AERRNO_W. pose proof TopX_RT4.topx_ASTRRCHR_W.
    pose proof TopX_RT4.topx_ASTRNCMP_W. pose proof TopX_RT4.topx_ASTRCMP_W.
    pose proof (fun S k k' H => rp_RMM RPi S k' k H).
    pose proof TopxDrainLitB.topx_HLIT5_x. pose proof TopxDrainLitB.topx_HLIT6_x. pose proof TopxDrainLitB.topx_HLIT7_x.
    pose proof W_drain_pb.drain_hctx_re1. pose proof W_drain_pb.drain_hctx_re2.
    pose proof W_drain_pb.drain_hctx_fr2. pose proof W_drain_pb.drain_hctx_sd. pose proof W_drain_pb.drain_hctx_ld.
    pose proof W_drain_pb.drain_HCROM. pose proof W_drain_pb.drain_HVS.
    pose proof W_drain_pb.drain_HV9. pose proof W_drain_pb.drain_HSD.
    pose proof W_drain_pb.drain_HGSB. pose proof W_drain_pb.drain_HSM.
    pose proof W_drain_pb.drain_HRGD. pose proof W_drain_pb.drain_HERRW.
    pose proof W_drain_pb.drain_HG. pose proof W_drain_pb.drain_HGO.
    pose proof W_drain_pb.drain_HGR.
    (* G_DR's rom_out at top_x's sink head from HRO (W_drain_pb.drain_HROMO is stated at tfib_sink_head), and MMAX's
       bound at fr_MMAX *)
    assert (rom_out segs TfibB (G_DR TfibB fr_RG)).
    { intros a Ha. destruct (HRO a Ha) as (Hdr1 & Hdr2 & Hdr3 & Hdr4).
      split; [intros HGa; exact (Hdr1 (c_HG_DR TfibB a HGa))|]. exact (conj Hdr2 (conj Hdr3 Hdr4)). }
    assert (0 < CfParamsReply.fr_MMAX <= 2 ^ 30) by (split; [apply Z.ltb_lt | apply Z.leb_le]; vm_compute; reflexivity).
    pose proof W_drain_pb.drain_HERRNO. pose proof W_drain_pb.drain_HERRAL. pose proof W_drain_pb.drain_HERRZ.
    pose proof W_drain_pb.drain_HGSZ.
    pose proof W_drain_pb.drain_PSTR. pose proof W_drain_pb.drain_PSTG. pose proof W_drain_pb.drain_PSTO.
    eapply W_drain_pb.pb_drain_x; eassumption. }
  (* ---- GSE_x at RPi (a Theorem Labs lane's scratch, ZZGseTopxScratch.v:106-196, its lemmas as asserts) ---- *)
  assert (GSE_x : gse_spec_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG (BASE + AF_fr_gestures_end)).
  { assert (HG0 : gx_ok segs TfibB (G_SL TfibB fr_RG)).
    { apply (W_journal.gx_ok_sub segs TfibB _ (G_fr_c TfibB)); [exact (c_HG_SL TfibB) | exact GX_ok]. }
    assert (HROMO0 : rom_out segs TfibB (G_SL TfibB fr_RG)).
    { intros a Ha. destruct (HRO a Ha) as (H1 & H2 & H3 & H4).
      split; [intros HGa; exact (H1 (c_HG_SL TfibB a HGa))|]. exact (conj H2 (conj H3 H4)). }
    assert (IMGC0 : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md ->
      fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly))
      by exact (W_img_x.fr_img_cover_x TfibB ARX ARX_laws).
    assert (PSTR : forall a, in_rom segs a -> ~ Exists (in_zr a) (@nil (Z * Z))) by (intros a _ H; inversion H).
    assert (HEND5P : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> ~ Exists (in_zr a) (@nil (Z * Z)))
      by (intros a _ H; inversion H).
    assert (HCL : In [BASE + AF_fr_gestures_end + 0x114] YCk0.CTX_AFREE)
      by (vm_compute; repeat (first [left; reflexivity | right])).
    assert (HCT : In [BASE + AF_fr_gestures_end + 0x150] YCk0.CTX_AFREE)
      by (vm_compute; repeat (first [left; reflexivity | right])).
    assert (HEND5I0 : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 -> in_img segs a).
    { intros a Ha. change (VAL A_lit_end5) with 134912 in Ha. apply (segin_ok segs).
      assert (E : a = 134912 \/ a = 134913 \/ a = 134914 \/ a = 134915 \/ a = 134916) by lia.
      destruct E as [E|[E|[E|[E|E]]]]; subst a; vm_compute; reflexivity. }
    assert (HEND5G0 : forall a, VAL A_lit_end5 <= a < VAL A_lit_end5 + 5 ->
      ~ inG (G_SL TfibB fr_RG) a /\ ~ Exists (in_zr a) (as_owned_static TfibB) /\
      ~ (as_errno TfibB <= a < as_errno TfibB + 4)).
    { intros a Ha. change (VAL A_lit_end5) with 134912 in Ha.
      split; [|split].
      - intros H. apply (c_HG_SL TfibB) in H. rewrite (G_fr_c_val TfibB top_HEV) in H.
        exact (top_apart_ok 134912 5 (G_fr_obj ++ [(TFIB_ERRNO_B, 4)]) ltac:(vm_compute; reflexivity) a H Ha).
      - rewrite (ts_owned TfibB TfibB_syms). intros H.
        exact (top_apart_ok 134912 5 Tfib_owned_static ltac:(vm_compute; reflexivity) a H Ha).
      - rewrite top_HEV. intros He.
        apply (top_apart_ok 134912 5 [(TFIB_ERRNO_B, 4)] ltac:(vm_compute; reflexivity) a); [|exact Ha].
        apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact He. }
    assert (HEND5S0 : ashp_x ARX (VAL A_lit_end5) 5).
    { apply (TopxImageB.tfib_shp_x TfibB TfibB_syms ARX).
      - intros ly S Hp W mem md HAR. exact (alx_const_cells _ _ _ ARX_laws ly S Hp W mem md HAR).
      - intros ly S Hp W mem md r HAR Hr. exact (alx_zshadow _ _ _ ARX_laws ly S Hp W mem md r HAR Hr).
      - vm_compute. reflexivity. }
    assert (cov_pair : forall lo hi a, rng_inb lo (hi - lo) G_fr_obj = true -> lo <= a < hi -> inG (G_fr_c TfibB) a)
      by (intros lo hi a H Ha; apply (obj_c TfibB); apply (rng_cover lo (hi - lo) G_fr_obj H a); lia).
    assert (HOUTG0 : forall r a, In r (aout_fp TfibB fr_RG 0 0) -> fst r <= a < snd r ->
      ~ (as_errno TfibB <= a < as_errno TfibB + 4) ->
      in_img segs a /\ ~ in_rom segs a /\ ~ Exists (in_zr a) (as_owned_static TfibB)).
    { intros r a Hin Ha Hne.
      assert (HGa : inG (G_fr_c TfibB) a).
      { unfold aout_fp in Hin. cbn [In] in Hin.
        destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; subst r; cbn [fst snd] in Ha;
          first [ match type of Ha with ?lo <= _ < ?hi => apply (cov_pair lo hi a); [vm_compute; reflexivity | exact Ha] end
                | exfalso; apply Hne; lia ]. }
      split; [|split].
      - first [exact (c_img TfibB top_HEV a HGa) | exact (c_img TfibB a HGa)].
      - intros Hr. first [exact (c_rom_apart TfibB top_HEV a Hr HGa) | exact (c_rom_apart TfibB a Hr HGa)].
      - exact (top_HOWN a HGa). }
    assert (HOUTLO0 : forall r, In r (aout_fp TfibB fr_RG 0 0) -> 0 <= fst r /\ snd r <= 0x5fc000).
    { intros r Hin. unfold aout_fp in Hin. cbn [In] in Hin.
      destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; subst r; split; apply Z.leb_le; vm_compute; reflexivity. }
    pose proof ARX_laws as LAWS. pose proof ARX_hp0 as HP0.
    assert (GE : ge_spec_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG (BASE + AF_fr_gesture_end))
      by (eapply (W_gesture_end.pb_gesture_end_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG); eassumption).
    eapply (W_gestures_end_top.pb_gestures_end_closed_x TfibB [] ARX MT RPi CfParamsReply.fr_MMAX fr_RG)
      with (CTX_AFREE := YCk0.CTX_AFREE); eassumption. }
  exact (lf_contract_of_segments_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP []
    ARX ARX_laws GX_ok LSx RINV
    (* a Theorem Labs lane's B pro arm (an internal work row; KF-COUNT F2 a working branch 3e5f3fa4742): RPi RP_NP NPF MO_FR after RINV,
       LS_cnt_pro after LS_pro (A: top_x.v:1236-1239 at 14fbe276057) *)
    (W_LLVMFuzzerTestOneInput_pro_x.lf_seg_pro_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM
       NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV RPi RP_NP NPF MO_FR OA TL TLF OWNLOW
       (Wf_cf (cp := CfParams_reply) (as_universe TfibB)) WFL SMALLOC ASM1 FFL (c_glob_wr TfibB HEV) ERRL_x HEV HZS
       (obj_c TfibB) HRO GSHV_x HFP_pro LS_pro_oa RI_pro LS_pro LS_cnt_pro BLKN HPST)
    (W_LLVMFuzzerTestOneInput_head_x.lf_seg_head_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX
       ARX_laws ARX_hp0 GX_ok LSx RINV (c_HGnout TfibB) (c_HERRNO TfibB top_HEV)
       (c_HZS TfibB TfibB_syms) RI_head_nout LS_head_nout RI_head_skip LS_head_skip)
    (* a Theorem Labs lane's B add arm (an internal work row, a working branch 7e3a32ed245): RPi RP_NP before OA, LS_cnt_add last
       (A: top_x.v:1242-1244 at 14fbe276057) *)
    (W_LLVMFuzzerTestOneInput_add_x.lf_arm_add_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM
       NP G fr_FP [] ARX ARX_laws GX_ok LSx RINV RPi RP_NP OA HEV HZS (obj_c TfibB) ERRL_x HRO GSHV_x HPST BLKN RI_add_pre
       RI_add_open RI_add_none LS_add_room LS_add_open LS_add_none LS_cnt_add)
    (* a Theorem Labs lane's B write arm (an internal work row, a working branch 514d7e9bda3): RPi RP_NP after RINV, LS_cnt_write last;
       list_push at RP := RPi (a Theorem Labs lane's F1B, W_list_push.v:2364 Variable RP after MT, merged on the room branch) *)
    (W_LLVMFuzzerTestOneInput_write_x.lf_arm_write_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv
       LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV RPi RP_NP TL
       LP
       (c_glob_wr TfibB HEV) ERRL_x (c_HGs TfibB) HZS TfibB_syms (c_HGW TfibB) BLKN HPST RI_write_skip LS_write_skip
       RI_write_push LS_write_room LS_write_push LS_cnt_write)
    (* a Theorem Labs lane's B drain arm (an internal work row, a working branch dd77d602fd8; A HeadX 13a792ebbad): RP RP_NP
       after TL, DR_CNT_grow after RI_drain_step, then dr_cnl_pk (the Variable above), DR_CNT_cnl,
       LS_cnt := LS_cnt_drain last *)
    (W_LLVMFuzzerTestOneInput_drain_x.lf_arm_drain_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv
       LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV CfParamsReply.fr_MMAX RSRC_x TL RPi RP_NP DR_x ALOCK AUNLOCK
       CNLR_x CSD_x CNL_x (c_HGs TfibB) (c_HG_DR TfibB) (c_HGlock TfibB) HG_GK (c_HERRHI TfibB HEV) ERRL_x
       (c_glob_wr TfibB HEV) HRO HZS c_HAP HPST BLKR RI_drain_skip RI_drain_step DR_CNT_grow RI_src RI_fds RI_pair RI_gone
       LS_drain_pre LS_cnl_pre LS_drain_skip LS_drain_step
       dr_cnl_pk DR_CNT_cnl LS_cnt_drain)
    (W_LLVMFuzzerTestOneInput_small_x.lf_arm_close_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP []
       ARX ARX_laws GX_ok LSx RINV (c_HGs TfibB) HZS TL (c_HERRHI TfibB HEV) RI_close LS_close)
    (* a Theorem Labs lane's B remove arm (an internal work row, a working branch f42b3777c7b; A RiRestate 5a9b16eac9e):
       fr_live_post / fr_surv before LIBROOM, RPi RP_NP after RINV, its LS_cnt = LS_cnt_remove and RM_CNT_*; its
       RI_rm_rr_fds is RI_fds (as A's top) *)
    (W_LLVMFuzzerTestOneInput_remove_x.lf_arm_remove_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv
       LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV RPi RP_NP CfParamsReply.fr_MMAX TL MLAW RRDS_x RR_x
       CSD_x CNLR_x CNL_rm_x CSHE_x SR_x HGP ERRL_x RGP_x (c_HGs TfibB) (c_HGlock TfibB) (c_HGnsrc TfibB) (c_HG_DR TfibB)
       HZS c_HAP HRO (c_HMG TfibB TfibB_syms HEV) RI_rm_found RI_fds RI_rm_rr_pair RI_rm_src LS_rm_rr_pre RI_rm_cnl_pre
       LS_rm_cnl_pre RI_rm_cshe_pre LS_rm_cshe_pre RI_rm_csd LS_rm_sr_pre RI_rm_step LS_rm_step LS_cnt_remove RM_CNT_cnl
       RM_CNT_cshe RM_CNT_sr (fun ly S Hp W mem md (H : ARX ly S Hp W mem md) => TopxImageB.ashp_str3_1_fr_cf ly S Hp W mem md (conj (proj1 H) (proj1 (proj2 H)))) BLKR PST_ROM PST_IMG)
    (* a Theorem Labs lane's B gone arm (an internal work row, a working branch 5024fade6020): RP := RPi after the MMAX;
       gn_pk := gn_pk (no B twin yet), RPNP := RP_NP, CNTRIG / LSCNT / CNTSTEP := CNT_gone_rig / LS_cnt_gone /
       CNT_gone_step after HLSRIG, as A's gone plug (top_x.v:1333-1338 at 3d17f490d56) *)
    (W_LLVMFuzzerTestOneInput_gone_x.lf_arm_gone_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws
       ARX_hp0 GX_ok LSx RINV (c_glob_wr TfibB HEV) ERRL_x RRDS_x TL MLAW SNP_x HGOTG_x GN_LIT_GES_x GN_LIT_FMT_x
       CfParamsReply.fr_MMAX RPi RIG_x RGP_x HRO GN_CNL GN_CSHE (c_ERRNO_LOW TfibB HEV) HZS (c_HGs TfibB)
       (W_LLVMFuzzerTestOneInput_gone_inst.gi_HG_RIG TfibB) (W_LLVMFuzzerTestOneInput_gone_inst.gi_HGcells TfibB)
       (W_LLVMFuzzerTestOneInput_gone_inst.gi_CELLS_ERRNO TfibB HEV) (c_rom_pinned TfibB TfibB_syms) GN_RI_pairs_x RI_fds
       GN_RI_read_x GN_RI_step_x GN_RI_end_x GN_LS_rig_x gn_pk RP_NP CNT_gone_rig LS_cnt_gone CNT_gone_step BLKN HPST FRMF)
    (W_LLVMFuzzerTestOneInput_small_x.lf_arm_eintr_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP []
       ARX ARX_laws GX_ok LSx RINV (c_HGs TfibB) HZS TL (c_HERRHI TfibB HEV) RI_eintr LS_eintr)
    (* a Theorem Labs lane's B event arm (an internal work row, a working branch 3ed6377ae1a2; checked by its scratch exact,
       ZZEventTopx.v (sha256 0abcbdbc7a96; internal record) rc=0): fr_live_post / fr_surv before LIBROOM, RPi RP_NP after fr_MMAX,
       LS_cnt_event last *)
    (W_LLVMFuzzerTestOneInput_event_x.lf_arm_event_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv
       LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV CfParamsReply.fr_MMAX RPi RP_NP TL (c_glob_wr TfibB HEV)
       ERRL_x HRO (c_HGlock TfibB) (c_HG_SL TfibB) HG_carry HERR_AP AMA_x AFREE_x AMEMCPY_x ASTRNLEN_x RE_x CSE_x BLKN HPST
       RI_gone RI_event_step LS_event_malloc LS_event_relay LS_event_free LS_event_step LS_cnt_event)
    (W_LLVMFuzzerTestOneInput_small_x.lf_arm_sendmax_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP []
       ARX ARX_laws ARX_hp0 GX_ok LSx RINV (c_HG_smax TfibB) (c_HG_seintr TfibB) TL (c_HERRHI TfibB HEV) RI_sendmax
       LS_sendmax)
    (W_LLVMFuzzerTestOneInput_small_x.lf_arm_default_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP []
       ARX ARX_laws ARX_hp0 GX_ok LSx RINV (c_HG_sdead TfibB) (c_HG_gone TfibB) (c_HG_client TfibB) (c_HGlock TfibB)
       TL (c_HERRHI TfibB HEV) ALOCK AUNLOCK RI_default LS_default)
    (W_LLVMFuzzerTestOneInput_latch_x.lf_seg_latch_x TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv
       LIBROOM NP G fr_FP [] ARX ARX_laws GX_ok LSx RINV CB_x (c_ERRNO_LOW TfibB HEV))
    (* a Theorem Labs lane's B exit arm (an internal work row, a working branch afc7ac89f0f (= 570c903d342's texts), Section lxx; its LS_exit_end in
       TX_LS_exit_end_e's premise order): RP RP_NP after AZS_s (here HZS), LS_exit_cnt LS_exit_cap LS_cnt (= LS_cnt_exit)
       after LS_exit_end *)
    (W_LLVMFuzzerTestOneInput_exit_x.lf_seg_exit_x_all TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv
       LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV TL MLAW ASF FFL ERRL_x
       (Wf_cf (cp := CfParams_reply) (as_universe TfibB)) WFL SFREE CfParamsReply.fr_MMAX (c_HG_SL TfibB) HZS RPi RP_NP
       CSD_x SR_x CSHE_x RF_x (W_bx_inst.bxi_XRF_ERRNO TfibB HEV) HRO LS_rf_room LS_exit_budget
       (W_bx_inst.bxi_XR_HGM TfibB) XR_GSHV (c_glob_wr TfibB HEV) XE_LIT_S_x RI_exit_slots RI_exit_ends
       LS_exit_end LS_exit_cnt LS_exit_cap LS_cnt_exit FP_SINK AIL HG_K HPST BLKN BLKM)).
Qed.
(* ---- route R, IMAGE B (a Theorem Labs lane, the one writer of B top_x at R; a Theorem Labs lane / a Theorem Labs lane 2026-10-31 01:08Z), the twin of A's Section topxR (a Theorem Labs lane).  A free inside a call re-hides the dead
   shadow, so at the re-hiding instance R := wle' pa_segs RZ_cf a call step gives only `R W W'`, and the entry contract is
   cut_x's fr_lib_contract_cf_xR (a Theorem Labs lane).  The statement at top_x's instance, by cut_x's
   lf_contract_of_segments_xR over the fifteen segment steps at R, each the segment / arm lemma's R twin (route-R
   in-place form: the strict arguments the twin uses, then R R_refl R_trans WLE_R, then its R callee premises), applied as
   in fr_contract_top_x above: lane 1 (pro, head, add, write, close, eintr, sendmax, default, latch) and lane 2 (drain,
   remove, gone, event, exit), each lemma in this tree.
   The Section hypotheses below are the twins' R callee specs at the top's instance (op_add, list_push, drain,
   check_no_loss, check_shape_ends, relay_remove, source_reset, relay_instance_gone, relay_event, the allocator rules at
   R, the relay_finish site block LXRF_R) and the exit-end model rule at R (LS_exit_end_R).  They are discharged where
   the top is instantiated; LXRF_R has no R block lemma in lib/B yet.
   The proof builds none of fr_contract_top_x's strict callee contracts (OA, LP, SL_x, DR_x, GSE_x, GN_CNL, GN_CSHE):
   each twin takes its R spec, so this theorem takes neither strict free rule (AFREE_x, AFREE0_x) nor Section topx's
   AMA_x / ARE_x / RA_x / SR_x / CSHE_x / CNL_rm_x / ASTRNDUP_x (2026-10-31: no proof discharges the strict free rule any
   more; image A's topxR uses no strict allocator rule either).
   At R := wle each hypothesis is the strict step above, so fr_contract_top_x is this theorem's wle instance. *)
Section topxR.
Variable R : YA0n.world W_kit.pa_segs -> YA0n.world W_kit.pa_segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Local Notation BR cx Hp := (lf_base_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp).
Local Notation IHR := (INV_H_xR TfibB NP G fr_FP [] ARX LSx RINV R).
Local Notation IDR := (INV_D_xR TfibB NP G fr_FP [] ARX LSx RINV R).
Local Notation IAR := (INV_A_xR TfibB NP G fr_FP [] ARX LSx RINV R).
Local Notation IKR := (INV_K_xR TfibB NP G fr_FP [] ARX LSx RINV R).
Local Notation IXR := (INV_X_xR TfibB NP G fr_FP [] ARX LSx RINV R).
(* the R callee specs of a Theorem Labs lane's lane-1 twins (a8's A text, B names): op_add and list_push at R *)
Hypothesis OA_R : W_op_add.oa_spec_g_xR (PI := PB_fr) TfibB [] ARX R MT RPi (BASE + AF_fr_op_add).
Hypothesis LP_R : W_contract_xR.lp_spec_g_xR (PI := PB_fr) TfibB [] ARX R MT RPi W_LLVMFuzzerTestOneInput_write.WR_MMAX
  (BASE + AF_fr_list_push).
(* the event arm twin's R callee premises at the top's instance (a Theorem Labs lane 2, Section evxR) *)
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world segs) mem md, ARX ly S Hp W mem md -> RO mem.
Hypothesis AMALLOC_R : amalloc_cf_rule_c_xR segs TfibB [] ARX MT CfParamsReply.fr_MMAX RPi RO YCk0.CTX_AMALLOC R.
Hypothesis AFREE_R : afree_cf_rule_c_xR segs TfibB [] ARX MT RPi RO YCk0.CTX_AFREE R.
Hypothesis RE_R : W_contract_xR.re_spec_xR (PI := PB_fr) TfibB [] ARX R MT RPi CfParamsReply.fr_MMAX
  (W_LLVMFuzzerTestOneInput_arm_event.et_GRE TfibB) fr_RG (BASE + AF_fr_relay_event).
(* the lane-2 arm twins' R callee premises at the top's instance (Sections drxR / wrxR / gxxR / lxxR of the lane-2 files,
   their texts with the strict bullets' values) *)
Hypothesis DRAIN_R : W_contract_xR.dr_spec_xR (PI := PB_fr) TfibB [] ARX R MT RPi CfParamsReply.fr_MMAX fr_RG (BASE + AF_fr_drain).
Hypothesis CNL_dr_R : forall G, gx_ok segs TfibB G -> gx_rt (PI := PB_fr) TfibB G -> rom_out segs TfibB G ->
  W_contract_xR_g6.cnl_spec_xR (PI := PB_fr) TfibB [] ARX R MT RPi G CfParamsReply.fr_MMAX (BASE + AF_fr_check_no_loss).
Hypothesis RR_R : W_contract_xR_relayB.rr_spec_xR TfibB [] ARX R MT RPi CfParamsReply.fr_MMAX fr_RG YCk0.CTX_AFREE
  (BASE + AF_fr_relay_remove).
Hypothesis CNL_rm_R : forall G, gx_ok segs TfibB G ->
  W_contract_xR_g6.cnl_spec_xR TfibB [] ARX R MT RPi G CfParamsReply.fr_MMAX (BASE + AF_fr_check_no_loss).
Hypothesis CSHE_R : forall G, gx_ok segs TfibB G ->
  W_contract_xR_g6.cshe_spec_xR TfibB [] ARX R MT RPi G (BASE + AF_fr_check_shape_ends).
Hypothesis SR_R : W_contract_srlf_xR.sr_spec_g_xR TfibB [] ARX R MT RPi (BASE + AF_fr_source_reset).
Hypothesis RIG_R : W_contract_xR_relayB.rig_spec_xR (PI := PB_fr) TfibB [] ARX R MT RPi CfParamsReply.fr_MMAX fr_RG
  YCk0.CTX_AFREE (BASE + AF_fr_relay_instance_gone).
Hypothesis GN_CNL_R : W_LLVMFuzzerTestOneInput_gone_base_x.GN_CNL_xR TfibB MT [] ARX CfParamsReply.fr_MMAX RPi R.
Hypothesis GN_CSHE_R : W_LLVMFuzzerTestOneInput_gone_base_x.GN_CSHE_xR TfibB MT [] ARX RPi R.
(* the relay_finish site block at R (lib/B/W_bx_defs_x.v lx_rf_site_S_xR; no R block lemma in lib/B yet) *)
Hypothesis LXRF_R : W_bx_defs_x.lx_rf_site_S_xR TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX LSx RPi R.
(* the exit-end model rule with its journal at R (exit_x Section lxxR LS_exit_end_R; at the instance:
   lib/B/ReplyLSIexitB_xR.v lsi_LS_exit_end_xR) *)
Hypothesis LS_exit_end_R : forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_bx_defs.lx_exit_cost MT m ->
  ajournal_gx_xR segs TfibB [] ARX R G 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks TfibB ly' S') ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  fr_live_post (c_S cx) (stack_free_state 1 fpos S') k' /\
  fr_surv (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
Theorem fr_contract_top_xR :
  @fr_lib_contract_cf_xR fx rc SK checksum_shape TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP
    G fr_FP [] ARX R.
Proof.
  pose proof top_HEV as HEV.
  pose proof (c_HZS TfibB TfibB_syms) as HZS.
  assert (HPST : forall a, in_img segs a -> ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ H; inversion H).
  (* SEG_PRO's HFP_pro from the FP cover (A: lib/B/W_LLVMFuzzerTestOneInput_top_x.v's plug of a2's TopxEntry.hfp_pro_x; B: a Theorem Labs lane 48eff67880c) *)
  pose proof (TopxEntry.hfp_pro_x TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP (G_fr_c TfibB) ARX fr_FP
    (fun ly S Hp W mem md p n (H : ARX ly S Hp W mem md) =>
       TopxEntry.arcf_blk ly S Hp W mem md p n (conj (proj1 H) (proj1 (proj2 H)))) FPCOV) as HFP_pro.
  (* ASM1 at top_x's relation: a Theorem Labs lane's lib/B/AsmTopX.v:115 asm1_pres_ARX (a working branch ed305db9fb3;
     ARX_asm is ARX over tfibsegs, AsmTopX.v:169), by conversion as A's top *)
  assert (ASM1 : astack_malloc_pres_x segs TfibB ARX 1) by exact AsmTopX.asm1_pres_ARX.
  (* the pthread mutex contracts at ARX: a Theorem Labs lane's TopX_RT_lock.v:70 / :74 (G-BLOCK e1fae7037354; ARX_rt is ARX
     over segs, :57), by conversion as A's top (TopX_RT.topx_ALOCK / topx_AUNLOCK) *)
  assert (ALOCK : alock_realizes_x (PI := PB_fr) TfibB ARX (SIGMA WS_pthread_mutex_lock)) by exact TopX_RT_lock.topx_ALOCK_W.
  assert (AUNLOCK : aunlock_realizes_x (PI := PB_fr) TfibB ARX (SIGMA WS_pthread_mutex_unlock))
    by exact TopX_RT_lock.topx_AUNLOCK_W.
  (* a live cf block's size: AR_blocks_law_cf's last conjunct (0 <= n < cf_malloc_max) and YG08cf's bound (a12's
     W_bx_inst_x.v bxi_BLK_cf, at the instance) *)
  assert (BLKR : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
    0 <= n < 2 ^ 30).
  { intros ly S Hp W mem md p n H Hin.
    destruct (YG0dcf.alc_blocks _ _ (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB) ly S Hp W mem md p n (proj1 H) Hin)
      as (_ & _ & _ & _ & _ & _ & Hn).
    pose proof (YG08cf.cf_malloc_max_bound (cp := CfParams_reply)) as Hb. lia. }
  assert (BLKN : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
    0 <= n) by (intros ly S Hp W mem md p n H Hin; exact (proj1 (BLKR ly S Hp W mem md p n H Hin))).
  assert (BLKM : forall ly S Hp (W : world segs) mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
    n < 2 ^ 30) by (intros ly S Hp W mem md p n H Hin; exact (proj2 (BLKR ly S Hp W mem md p n H Hin))).
  (* SEG_PRO's stack_malloc facts at ARX, from the cf laws (image A's top_x, the same proofs): YGcallcf.v's owned-low
     and Wf laws (WFx := Wf_cf, ARX's first projection), and YG05cf.v's stack_malloc progress and post *)
  assert (OWNLOW : ARx_owned_low_law segs TfibB ARX).
  { intros ly S Hp W mem md a H Ho.
    exact (ARx_owned_low_law_cf_x (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)
      ly S Hp W mem md a (proj1 H) Ho). }
  assert (WFL : ARx_wf_law segs ARX (Wf_cf (cp := CfParams_reply) (as_universe TfibB))).
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
  (* SEG_EXIT's instance facts (image A's top_x, the same proofs): the stack_free law over ARX (YG0tcf.v), the frame
     split after stack_free (YG05cf.v), the g_s slots' shadow hull (GSHV_x: g_s is pro_G's first range), and the stdio
     cells apart from G_fr_c (tfib_K's six ranges against G_fr_c's objects and errno, decided) *)
  assert (ASF : astack_free_law_x segs TfibB ARX).
  { intros ly S Hp W mem md mem' md' cid pos H Hin HF HO HV Hvm Hlz He HK HKEPT. unfold ARX in H |- *.
    (* W1: the arodata conjunct at mem' from the law's kept-bytes frame (a Theorem Labs lane's engine) *)
    split; [|split; [exact (proj1 (proj2 H)) |
      exact (ReplyKeptAroB.arodata_kept_B mem mem' (proj2 (proj2 H)) HKEPT)]].
    exact (YG0tcf.astack_free_law_ok_cf (cp := CfParams_reply) segs TfibB ly S Hp W mem md mem' md' cid pos (proj1 H)
      Hin HF HO HV Hvm Hlz He HK). }
  assert (SFREE : forall s cid pos, Wf_cf (cp := CfParams_reply) (as_universe TfibB) s -> In (cid, pos) (frames s) ->
    exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2).
  { intros s cid pos HWF Hin. exact (proj2 (stack_free_ok_cf (cp := CfParams_reply) _ s cid pos HWF Hin)). }
  assert (XR_GSHV : forall ly S Hp (W : world segs) mem md a n, ARX ly S Hp W mem md -> 0 < n ->
    (forall x, a <= x < a + n -> rg_s fr_RG <= x < rg_s fr_RG + 4 * ASRC) ->
    shadow_hull_vis (aview segs (w_H W) mem) a n).
  { intros ly S Hp W mem md a n H Hn Hx. apply (GSHV_x ly S Hp W mem md a n H Hn).
    intros x Hx'. unfold W_LLVMFuzzerTestOneInput_pro.pro_G. cbn [app]. apply inG_cons. left. unfold in_zr.
    cbn [fst snd]. exact (Hx x Hx'). }
  assert (HG_K : forall a, aenv_addr tfib_K a \/ ak_meta_ptr tfib_K <= a < ak_meta_ptr tfib_K + 8 \/
    ak_meta_mem tfib_K <= a < ak_meta_mem tfib_K + 8 -> 0 <= a < 2 ^ 64 /\ ~ inG G a).
  { intros a Ha.
    assert (HK : inG [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 16); (FF_canary, 8); (FF_meta_ptr, 8);
        (FF_meta_mem, 8)] a).
    { unfold aenv_addr in Ha. cbn [tfib_K ak_threaded ak_need_locks ak_ofl_lock ak_canary ak_meta_ptr ak_meta_mem] in Ha.
      unfold inG. rewrite Exists_exists.
      destruct Ha as [[-> | [-> | [Ha | Ha]]] | [Ha | Ha]];
        [ exists (A_threaded, 1) | exists (A_need_locks, 1) | exists (A_ofl_lock, 16) | exists (FF_canary, 8)
        | exists (FF_meta_ptr, 8) | exists (FF_meta_mem, 8) ];
        (split; [cbn [In]; repeat (first [left; reflexivity | right]) | unfold in_zr; cbn [fst snd]; lia]). }
    assert (Hd : forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? 2 ^ 64) &&
        forallb (fun g => (fst r + snd r <=? fst g) || (fst g + snd g <=? fst r)) (G_fr_obj ++ [(TFIB_ERRNO_B, 4)]))
      [(A_threaded, 1); (A_need_locks, 1); (A_ofl_lock, 16); (FF_canary, 8); (FF_meta_ptr, 8); (FF_meta_mem, 8)] = true)
      by (vm_compute; reflexivity).
    unfold inG in HK. apply Exists_exists in HK as (r & Hr & Hz). rewrite forallb_forall in Hd. specialize (Hd r Hr).
    apply andb_prop in Hd as [Eb Hd]. apply andb_prop in Eb as [E0 E1]. apply Z.leb_le in E0, E1. unfold in_zr in Hz.
    split; [lia|].
    intros HinG. unfold G_fr_c in HinG. rewrite HEV in HinG. unfold inG in HinG.
    apply Exists_exists in HinG as (g & Hg & Hzg). rewrite forallb_forall in Hd. specialize (Hd g Hg).
    unfold in_zr in Hzg. apply orb_prop in Hd as [Hd | Hd]; apply Z.leb_le in Hd; lia. }
  (* ARM_remove's instance facts: source_reset's G at each slot over ARX (B _G.v c_HGP's five plain conjuncts and the
     g_s shadow hull XR_GSHV), and the PST facts at PST = [] *)
  assert (HGP : forall si, (si < 4)%nat ->
    gx_prog_x (PI := PB_fr) TfibB ARX [(W_LLVMFuzzerTestOneInput_remove.rm_HA si, ASRC)]).
  { intros si Hsi. destruct (c_HGP TfibB TfibB_syms HEV si Hsi) as (G1 & G2 & _ & G4 & G5 & _).
    (* rom_out at the Section's sink head SK: from HRO, the slot being part of g_s, which is in G *)
    assert (Hsub : forall a, inG [(W_LLVMFuzzerTestOneInput_remove.rm_HA si, ASRC)] a -> inG G a).
    { intros a Ha. apply (c_HGs TfibB). apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
      unfold in_zr, W_LLVMFuzzerTestOneInput_remove.rm_HA in Ha. cbn [fst snd] in Ha. clear - Ha Hsi.
      unfold ASRC in *. lia. }
    split; [exact G1|]. split; [exact G2|].
    split; [intros a Ha; destruct (HRO a Ha) as (Hn & Hrest); split; [intros Hin; exact (Hn (Hsub a Hin)) | exact Hrest]|].
    split; [exact G4|]. split; [exact G5|].
    intros ly S Hp W mem md a n HAR Hn Hx. apply (XR_GSHV ly S Hp W mem md a n HAR Hn).
    intros x Hx'. specialize (Hx x Hx'). apply inG_cons in Hx as [Hx | Hx]; [|exfalso; exact (inG_nil x Hx)].
    unfold in_zr, W_LLVMFuzzerTestOneInput_remove.rm_HA in Hx. cbn [fst snd] in Hx. clear - Hx Hsi. unfold ASRC in *.
    lia. }
  assert (PST_ROM : forall a, in_rom segs a -> ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ H; inversion H).
  assert (PST_IMG : forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static TfibB) ->
    ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ _ H; inversion H).
  (* ARM_event's G facts: every range of the tail's carried globals (the AR file's et_GL) is one of G_fr_c's objects,
     and none holds errno's cell (decided) *)
  assert (HG_carry : forall a, inG W_LLVMFuzzerTestOneInput_arm_event.et_GL a -> inG G a).
  { apply inG_sub. unfold W_LLVMFuzzerTestOneInput_arm_event.et_GL.
    repeat (apply Forall_cons; [intros a Ha; apply obj_c; revert a Ha; apply rng_cover_zr; vm_compute; reflexivity|]).
    apply Forall_nil. }
  assert (HERR_AP : forall a, inG W_LLVMFuzzerTestOneInput_arm_event.et_GL a -> ~ (as_errno TfibB <= a < as_errno TfibB + 4)).
  { rewrite HEV. apply W_LLVMFuzzerTestOneInput_G.apart_of_b. vm_compute. reflexivity. }
  (* ARM_gone's instance fact over ARX: the fake frames' alignment (YG0scf.v frame_facts_cf on ARX's ARmcf) *)
  assert (FRMF : forall ly S Hp (W : world segs) mem md cid pos, ARX ly S Hp W mem md -> In (cid, pos) (frames S) ->
    ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0).
  { intros ly S Hp W mem md cid pos [[M _] _] Hin.
    destruct (YG0scf.frame_facts_cf (cp := CfParams_reply) TfibB ly S Hp _ cid pos M Hin)
      as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & H64 & Hb & _).
    split; [exact Hpg|]. split; [exact Hoff|]. split; [exact H64 | exact Hb]. }
  (* ARM_drain's G fact no _G.v lemma states in its form: every range of its global list is one of G_fr_c's 20
     objects (image A's top_x HG_GK proof) *)
  assert (HG_GK : forall a, inG [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4);
    (rg_send_max fr_RG, 8); (rg_client fr_RG, 4); (rg_send_dead fr_RG, 1); (rg_gone fr_RG, 1);
    (rg_wake fr_RG, 8); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] a -> inG G a).
  { apply inG_sub.
    repeat (apply Forall_cons; [intros a Ha; apply obj_c; revert a Ha; apply rng_cover_zr; vm_compute; reflexivity|]).
    apply Forall_nil. }
  exact (lf_contract_of_segments_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G
    fr_FP [] ARX ARX_laws GX_ok LSx RINV R R_refl R_trans WLE_R
    (W_LLVMFuzzerTestOneInput_pro_x.lf_seg_pro_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV RPi RP_NP NPF MO_FR TL TLF OWNLOW (Wf_cf (cp := CfParams_reply) (as_universe TfibB)) WFL SMALLOC ASM1 FFL (c_glob_wr TfibB HEV) ERRL_x HEV HZS (obj_c TfibB) HRO GSHV_x HFP_pro LS_pro_oa RI_pro LS_pro LS_cnt_pro BLKN HPST R R_refl R_trans WLE_R OA_R)
    (W_LLVMFuzzerTestOneInput_head_x.lf_seg_head_xR TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV (c_HGnout TfibB) (c_HERRNO TfibB top_HEV) (c_HZS TfibB TfibB_syms) RI_head_nout LS_head_nout RI_head_skip LS_head_skip R R_refl R_trans WLE_R)
    (W_LLVMFuzzerTestOneInput_add_x.lf_arm_add_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX ARX_laws GX_ok LSx RINV RPi RP_NP HEV HZS (obj_c TfibB) ERRL_x HRO GSHV_x HPST BLKN RI_add_pre RI_add_open RI_add_none LS_add_room LS_add_open LS_add_none LS_cnt_add R R_refl R_trans WLE_R OA_R)
    (W_LLVMFuzzerTestOneInput_write_x.lf_arm_write_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV RPi RP_NP TL (c_glob_wr TfibB HEV) ERRL_x (c_HGs TfibB) HZS TfibB_syms (c_HGW TfibB) BLKN HPST RI_write_skip LS_write_skip RI_write_push LS_write_room LS_write_push LS_cnt_write R R_refl R_trans WLE_R LP_R)
    (W_LLVMFuzzerTestOneInput_drain_x.lf_arm_drain_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV CfParamsReply.fr_MMAX RSRC_x TL RPi RP_NP ALOCK AUNLOCK CNLR_x CSD_x (c_HGs TfibB) (c_HG_DR TfibB) (c_HGlock TfibB) HG_GK (c_HERRHI TfibB HEV) ERRL_x (c_glob_wr TfibB HEV) HRO HZS c_HAP HPST BLKR RI_drain_skip RI_drain_step DR_CNT_grow RI_src RI_fds RI_pair RI_gone LS_drain_pre LS_cnl_pre LS_drain_skip LS_drain_step dr_cnl_pk DR_CNT_cnl LS_cnt_drain R R_refl R_trans WLE_R DRAIN_R CNL_dr_R)
    (W_LLVMFuzzerTestOneInput_small_x.lf_arm_close_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws GX_ok LSx RINV (c_HGs TfibB) HZS TL (c_HERRHI TfibB HEV) RI_close LS_close R R_refl R_trans WLE_R)
    (W_LLVMFuzzerTestOneInput_remove_x.lf_arm_remove_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV RPi RP_NP CfParamsReply.fr_MMAX TL MLAW RRDS_x CSD_x CNLR_x HGP ERRL_x RGP_x (c_HGs TfibB) (c_HGlock TfibB) (c_HGnsrc TfibB) (c_HG_DR TfibB) HZS c_HAP HRO (c_HMG TfibB TfibB_syms HEV) RI_rm_found RI_fds RI_rm_rr_pair RI_rm_src LS_rm_rr_pre RI_rm_cnl_pre LS_rm_cnl_pre RI_rm_cshe_pre LS_rm_cshe_pre RI_rm_csd LS_rm_sr_pre RI_rm_step LS_rm_step LS_cnt_remove RM_CNT_cnl RM_CNT_cshe RM_CNT_sr (fun ly S Hp W mem md (H : ARX ly S Hp W mem md) => TopxImageB.ashp_str3_1_fr_cf ly S Hp W mem md (conj (proj1 H) (proj1 (proj2 H)))) BLKR PST_ROM PST_IMG R R_refl R_trans WLE_R RR_R CNL_rm_R CSHE_R SR_R)
    (W_LLVMFuzzerTestOneInput_gone_x.lf_arm_gone_xR TfibB MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV (c_glob_wr TfibB HEV) ERRL_x RRDS_x TL MLAW SNP_x HGOTG_x GN_LIT_GES_x GN_LIT_FMT_x CfParamsReply.fr_MMAX RPi RGP_x HRO (c_ERRNO_LOW TfibB HEV) HZS (c_HGs TfibB) (W_LLVMFuzzerTestOneInput_gone_inst.gi_HG_RIG TfibB) (W_LLVMFuzzerTestOneInput_gone_inst.gi_HGcells TfibB) (W_LLVMFuzzerTestOneInput_gone_inst.gi_CELLS_ERRNO TfibB HEV) (c_rom_pinned TfibB TfibB_syms) GN_RI_pairs_x RI_fds GN_RI_read_x GN_RI_step_x GN_RI_end_x GN_LS_rig_x gn_pk RP_NP CNT_gone_rig LS_cnt_gone CNT_gone_step BLKN HPST FRMF R R_refl R_trans WLE_R RIG_R GN_CNL_R GN_CSHE_R)
    (W_LLVMFuzzerTestOneInput_small_x.lf_arm_eintr_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws GX_ok LSx RINV (c_HGs TfibB) HZS TL (c_HERRHI TfibB HEV) RI_eintr LS_eintr R R_refl R_trans WLE_R)
    (W_LLVMFuzzerTestOneInput_event_x.lf_arm_event_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV CfParamsReply.fr_MMAX RPi RP_NP TL (c_glob_wr TfibB HEV) ERRL_x HRO (c_HGlock TfibB) (c_HG_SL TfibB) HG_carry HERR_AP AMEMCPY_x ASTRNLEN_x CSE_x BLKN HPST RI_gone RI_event_step LS_event_malloc LS_event_relay LS_event_free LS_event_step LS_cnt_event R R_refl R_trans WLE_R RO RO_ARx AMALLOC_R AFREE_R RE_R)
    (W_LLVMFuzzerTestOneInput_small_x.lf_arm_sendmax_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV (c_HG_smax TfibB) (c_HG_seintr TfibB) TL (c_HERRHI TfibB HEV) RI_sendmax LS_sendmax R R_refl R_trans WLE_R)
    (W_LLVMFuzzerTestOneInput_small_x.lf_arm_default_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV (c_HG_sdead TfibB) (c_HG_gone TfibB) (c_HG_client TfibB) (c_HGlock TfibB) TL (c_HERRHI TfibB HEV) ALOCK AUNLOCK RI_default LS_default R R_refl R_trans WLE_R)
    (W_LLVMFuzzerTestOneInput_latch_x.lf_seg_latch_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX ARX_laws GX_ok LSx RINV CB_x (c_ERRNO_LOW TfibB HEV) R R_refl R_trans WLE_R)
    (W_LLVMFuzzerTestOneInput_exit_x.lf_seg_exit_x_all_xR TfibB MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G fr_FP [] ARX ARX_laws ARX_hp0 GX_ok LSx RINV TL MLAW ASF FFL ERRL_x (Wf_cf (cp := CfParams_reply) (as_universe TfibB)) WFL SFREE (c_HG_SL TfibB) HZS RPi RP_NP CSD_x (W_bx_inst.bxi_XRF_ERRNO TfibB HEV) HRO LS_exit_budget (W_bx_inst.bxi_XR_HGM TfibB) XR_GSHV (c_glob_wr TfibB HEV) XE_LIT_S_x RI_exit_slots RI_exit_ends LS_exit_cnt LS_exit_cap LS_cnt_exit FP_SINK AIL HG_K HPST BLKN BLKM R R_refl R_trans WLE_R SR_R CSHE_R LS_exit_end_R LXRF_R)).
Qed.
End topxR.
End topx.

(* ---- THE CHECK at the B cf top's model invariants (a Theorem Labs lane's ruling): at LSx := ReplyLSB.fr_LS TfibB CR and
   RINV := ReplyRINVB.fr_RINV, B _G.v's c_RI_head_nout / c_LS_head_nout / c_RI_head_skip / c_LS_head_skip plug the
   four head-rule hypotheses above by `exact` (their texts restated here with that substitution) ---- *)
Section hchk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable CR : Z.
Local Notation LSx := (ReplyLSB.fr_LS TfibB CR).
Local Notation RINV := ReplyRINVB.fr_RINV.
Lemma top_RI_head_nout_fr : forall cx t m, RINV cx t m -> RINV cx t (W_LLVMFuzzerTestOneInput_head.lm_clear_O m).
Proof. exact c_RI_head_nout. Qed.
Lemma top_LS_head_nout_fr : forall cx t m ly S, LSx cx t m ly S ->
  LSx cx t (W_LLVMFuzzerTestOneInput_head.lm_clear_O m) ly S.
Proof. exact (c_LS_head_nout TfibB CR). Qed.
Lemma top_RI_head_skip_fr : forall cx t m, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (W_LLVMFuzzerTestOneInput_head.hd_kb cx m) = None -> RINV cx t m ->
  RINV cx (t + 1) (W_LLVMFuzzerTestOneInput_head.lm_set_k m (W_LLVMFuzzerTestOneInput_head.hd_k' cx m)).
Proof. exact c_RI_head_skip. Qed.
Lemma top_LS_head_skip_fr : forall cx t m ly S, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (W_LLVMFuzzerTestOneInput_head.hd_kb cx m) = None -> LSx cx t m ly S ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_head.lm_set_k m (W_LLVMFuzzerTestOneInput_head.hd_k' cx m)) ly S.
Proof. exact (c_LS_head_skip TfibB CR). Qed.
End hchk.
