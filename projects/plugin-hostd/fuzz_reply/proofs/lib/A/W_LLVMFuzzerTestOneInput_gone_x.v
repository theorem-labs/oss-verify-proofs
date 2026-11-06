(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC conversion of ARM_gone of fuzz_reply's LLVMFuzzerTestOneInput
   (lib/A/W_LLVMFuzzerTestOneInput_gone.v, a Theorem Labs lane's lf_arm_gone, 312c6aa4c95, adapted to integ at
   commit 95cae0d4740) to the cut invariants of lib/A/W_LLVMFuzzerTestOneInput_cut_x.v
   (a Theorem Labs lane's route (b), step 7).  lf_arm_gone_x is exactly cut_x's Section w hypothesis ARM_gone.  No AR file and
   no kit file is edited.
   THIS FILE IS THE ARM'S COMPOSITION, as _gone.v's: lf_arm_gone_x from the seven phase lemmas, by SRr_bind.  The
   phases are converted in lib/A/W_LLVMFuzzerTestOneInput_gone_p<n>_x.v over the cut points of
   W_LLVMFuzzerTestOneInput_gone_base_x.v (the AR cut points with the journal over ARx at the ghost list [] and LS ->
   LSx) and the transport kit W_LLVMFuzzerTestOneInput_gone_tk_x.v.  cut_x's HP0 makes every ghost list of the walk
   empty: the entry's Hp is [] (from lf_base_x's ARx), and each phase runs at [].
   Section hypotheses beyond cut_x's Section w header (B .. RINV, verbatim):
     _gone.v's, in its order: the AR-free ones verbatim (HERR, TL, HZS, RIR, RGP, HGRIG, HPAIRS, HFDS, HGCELLS, GWR,
       HROMPIN, HCE, HERRROM, HGs, ML; HLSRIG / RIstep / RIend with LS -> LSx); the callee contracts at their kit forms
       (SNP asnprintf_realizes_x, W_sites_x.v:392; RIG rig_spec_x at K0's ACk0.CTX_AFREE, W_contract_x.v:857 of the kit
       of record 628b62f1a9e; CNL cnl_spec_x :1186; CSHE cshe_spec_x :1086; CNLR cnlr_spec_x :353; CSD csd_spec_x :118);
       HGOTG and GN_LITS over ARx;
     OWED: BLKN (kit _x twin of al_blocks' last conjunct; W_kit_x.v's text, as add_x / pro_x / event_x);
     forced by the generic relation and placement: HPST (the image is off PST; add_x's text) and FRMF (W_frame_x.v:105,
       the fake frames' 64-alignment frame_al64_x and shadow_hull_vis_of_frame_x read). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
(* _gone.v's own imports, AFTER the generic kit's *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_contract W_sites W_frame W_rebase W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_tk W_LLVMFuzzerTestOneInput_gone_p0
W_LLVMFuzzerTestOneInput_gone_p1 W_LLVMFuzzerTestOneInput_gone_p2 W_LLVMFuzzerTestOneInput_gone_p4
W_LLVMFuzzerTestOneInput_gone_p3 W_LLVMFuzzerTestOneInput_gone_p5 W_LLVMFuzzerTestOneInput_gone_p6.
(* K0's caller-context tables (rig_spec's CTX_AFREE is ACk0.CTX_AFREE at the instance) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p0_x
W_LLVMFuzzerTestOneInput_gone_p1_x W_LLVMFuzzerTestOneInput_gone_p2_x W_LLVMFuzzerTestOneInput_gone_p3_x
W_LLVMFuzzerTestOneInput_gone_p4_x W_LLVMFuzzerTestOneInput_gone_p5_x W_LLVMFuzzerTestOneInput_gone_p6_x.
(* route R: the R contract texts of the three callees that free (relay_instance_gone, check_no_loss, check_shape_ends)
   and SRrG's rules *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR_relay W_contract_xR_g6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section gxx.
(* cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:191-235) *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* the instance's ghost poisoned-head set stays empty (a Theorem Labs lane's HP0 ruling, W_journal_x at 0c4d57d9bf1;
   fuzz_reply calls no poison routine): the driver reads the post's Hp' = [] from the journal's ARx through it *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
(* ---------------------------------------------------------------- ARM_gone's own hypotheses, in _gone.v's order *)
(* errno's place; phase 0 takes it to carry the stream's cells across its two stack stores *)
Hypothesis HERR : GN_ERRNO_LOW B.
(* the allocator instance (W_kit.v); phase 1 (snprintf's interceptor) and phase 6 (errno's place, pal_env) take it *)
Hypothesis TL : PALib B.
(* g_s lies in the instance's zero-shadow ranges *)
Hypothesis HZS : GN_HZS B.
(* the slots check_no_loss_read is called on have no pending record *)
Hypothesis RIR : GN_RI_read RINV.
(* snprintf, the pf chain's interceptor contract: W_sites_x.v:392 asnprintf_realizes_x, the twin of _gone.v's SNP *)
Hypothesis SNP : asnprintf_realizes_x B ARx (SIGMA WS_snprintf) FR_GOT_GUARD FR_GUARD.
(* _gone.v's HGOTG and GN_LITS over ARx (Hp after S) *)
Hypothesis HGOTG : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md ->
  rdword (aview segs (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
Hypothesis GN_LITS : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 20)) 7 /\
  shadow_hull_vis (aview segs (w_H W) mem) (VAL (A_OBJ 20)) 7 /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 21)) 14 /\
  shadow_hull_vis (aview segs (w_H W) mem) (VAL (A_OBJ 21)) 14.
(* ---- relay_instance_gone (phase 3) ---- *)
Variable MMAX : Z.                                   (* W6's / W7's request bound *)
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c) / (d)): the room record the callees are taken at.  At the instance
   RM := fun S _ => NP S, so RPNP below holds by conversion *)
Variable RP : roomp.
(* W6's contract over ARx: W_contract_x.v rig_spec_x at CTX_AFREE := K0's table ACk0.CTX_AFREE (the kit of record
   628b62f1a9e); rg_place verbatim *)
Hypothesis RIG : rig_spec_x B PST ARx MT RP MMAX fr_RG ACk0.CTX_AFREE (BASE + AF_fr_relay_instance_gone).
Hypothesis RGP : rg_place B fr_RG.
(* the base's model obligations phase 3 takes *)
Hypothesis HGRIG : GN_HG_RIG B G_fr.
Hypothesis HPAIRS : GN_RI_pairs RINV.
Hypothesis HFDS : GN_RI_fds RINV.
Hypothesis HLSRIG : GN_LS_rig MT LSx RINV MMAX.
(* the room round's count row and model count rules (top_x's rows): gn_pk is the arm's peak (s5-r1d's pk_gone at the
   instance); LSCNT is GN_LS_cnt_x (_gone_base_x.v); CNTRIG is GN_CNT_rig at relay_instance_gone's premise peak
   rig_pk (W_contract_x.v:312) of its trace; CNTSTEP (phase 5, below) is GN_CNT_step at check_no_loss's cnl_pk *)
Variable gn_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat.
Hypothesis RPNP : forall S k, rp_RM RP S k <-> NP S.
Hypothesis CNTRIG : GN_CNT_rig gn_pk (fun cx m hs =>
  rig_pk (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs)).
Hypothesis LSCNT : GN_LS_cnt_x B LSx RINV RP gn_pk.
Hypothesis HGCELLS : GN_HGcells G_fr.
Hypothesis GWR : glob_wr_law G_fr.
Hypothesis HROMPIN : GN_ROM_PIN B.
(* errno is none of the model's cells (base GN_CELLS_ERRNO) and no read-only byte; both proved for the
   instance in lib/A/W_LLVMFuzzerTestOneInput_G.v (c_CELLS_ERRNO, c_ROM_ERR) *)
Hypothesis HCE : GN_CELLS_ERRNO B.
Hypothesis HERRROM : forall a, in_rom segs a -> ~ (as_errno B <= a < as_errno B + 4).
(* phase 3's own GP3_ERRNO_APART, derived from those two: _gone.v's gx_errno_apart (AR-free), cited *)
Let gx_errno_apart := W_LLVMFuzzerTestOneInput_gone.gx_errno_apart B HCE HERRROM.
(* ---- the table-order loop (phase 5): W3's check_no_loss / check_shape_ends over ARx (W_contract_x.v cnl_spec_x /
   cshe_spec_x), G-generic as _gone.v takes them *)
Hypothesis CNL : forall G, gx_ok segs B G -> gx_rt B G -> cnl_spec_x B PST ARx MT RP G MMAX (BASE + AF_fr_check_no_loss).
Hypothesis CSHE : forall G, gx_ok segs B G -> gx_rt B G -> cshe_spec_x B PST ARx MT RP G (BASE + AF_fr_check_shape_ends).
(* the base's model obligations phase 5 takes *)
Hypothesis HGs : GN_HGs G_fr.
Hypothesis RIstep : GN_RI_step B MT LSx RINV MMAX.
Hypothesis RIend : GN_RI_end B MT LSx RINV.
Hypothesis CNTSTEP : GN_CNT_step RINV gn_pk (fun h => cnl_pk (hs_expected h) (hs_held h)).
(* the allocator instance's meter laws (Reusable/YC5d.v:26) *)
Hypothesis ML : ameter_laws MT.
(* check_no_loss_read (phase 4) and check_shape_done (phase 6) over ARx: W_contract_x.v cnlr_spec_x / csd_spec_x *)
Hypothesis CNLR : cnlr_spec_x B PST ARx (BASE + AF_fr_check_no_loss_read).
Hypothesis CSD : csd_spec_x B PST ARx (BASE + AF_fr_check_shape_done).
(* ---- forced by the generic relation and the placement PST ---- *)
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX, YG0d.v:441; ARx_blocks_law has no size
   conjunct).  The text is W_kit_x.v's BLKN (add_x's). *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST): the callee journals' image clause and the ROM-view lemma take it *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* W_frame_x.v:105's Section hypothesis FRMF (the generic counterpart of YG0s.v:442 frame_facts' fake-frame
   alignment), which frame_al64_x and shadow_hull_vis_of_frame_x take (phases 1 and 5) *)
Hypothesis FRMF : forall ly S Hp (W : world segs) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.

(* ---- the phases: all seven are Qed lemmas (lib/A/W_LLVMFuzzerTestOneInput_gone_p<n>_x.v), at this Section's
   variables ---- *)
Let GP0 := gp0_entry_join_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV HERR BLKN.
Let GP1 := gp1_join_l1_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV TL SNP HGOTG GN_LITS BLKN FRMF.
Let GP2 := gp2_l1_rig_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV HZS HERR BLKN.
Let GP3 := gp3_rig_c1_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV MMAX RP RIG RGP HGRIG HPAIRS HFDS HLSRIG gn_pk RPNP CNTRIG LSCNT HGCELLS GWR HROMPIN gx_errno_apart BLKN
  HPST.
Let GP4 := gp4_c1_t0_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV HZS RIR CNLR HGCELLS HROMPIN HPST.
Let GP5 := gp5_t0_csd_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV MMAX RP CNL CSHE HGs HGCELLS HROMPIN HZS HCE RIstep RIend gn_pk RPNP LSCNT CNTSTEP GWR ML HERR HERRROM
  BLKN HPST FRMF.
Let GP6 := gp6_csd_latch_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV TL CSD HGCELLS HROMPIN BLKN HPST.

(* ---- ARM_gone (cut_x Section w) ---- *)
Theorem lf_arm_gone_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 5 cx Hp t W c -> SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof.
  intros cx Hp t W c HB HA.
  (* the entry's ghost list is empty (HP0 on the pre's ARx): the walk runs at [] *)
  assert (EHp : Hp = []) by (pose proof HB as (_ & HPRE); exact (HP0 _ _ _ _ _ _ (proj1 (proj1 HPRE)))).
  subst Hp.
  eapply SRr_bind; [exact (GP0 cx t W c HB HA)|].
  intros W0 c0 _ (m & HJN).
  eapply SRr_bind; [exact (GP1 cx t m W0 c0 HB HJN)|].
  intros W1 c1 _ HL1.
  eapply SRr_bind; [exact (GP2 0%nat cx t m W1 c1 HB HL1)|].
  intros W2 c2 _ HRG.
  eapply SRr_bind; [exact (GP3 cx t m W2 c2 HB HRG)|].
  intros W3 c3 _ (m1 & HC1).
  eapply SRr_bind; [exact (GP4 0%nat cx t m m1 W3 c3 HB HC1)|].
  intros W4 c4 _ HT0.
  eapply SRr_bind; [exact (GP5 cx t m m1 W4 c4 HB HT0)|].
  intros W5 c5 _ (mc & HCSD).
  exact (GP6 cx t m mc W5 c5 HB HCSD).
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0; brief-lfR.md (sha256 e81dbd85a137; internal record)): ARM_gone at a world relation R, cut_x's Section wR hypothesis
   ARM_gone_R.  The cut journal runs from the operation's entry (INV_A_xR .. INV_K_xR), and three callees of the arm
   free (relay_instance_gone at +0x288, check_no_loss through gesture_model, check_shape_ends in its loops 2 / 3), so
   they are taken at their R contract texts: RIG_R (W_contract_xR_relay.v rig_spec_xR), CNL_R / CSHE_R
   (W_contract_xR_g6.v cnl_spec_xR / cshe_spec_xR), in the strict order RIG, CNL, CSHE.  snprintf (SNP),
   check_no_loss_read (CNLR) and check_shape_done (CSD) cannot free: they stay at their strict specs, which the phase
   twins lift into the R journal (ajournal_gx_xR_mono WLE_R).  The phases are the seven R twins
   (W_LLVMFuzzerTestOneInput_gone_p<n>_x.v Sections gp<n>_xR, over the base's R cut points); phases 0, 2, 4, 6 are
   straight-line or strict-callee steps (strict SRr over the R journal, lifted by SRr_SRrG), phases 1, 3, 5 step at
   SRrG pa_segs R; the composition is SRrG_bind (R_trans), closed by SRrG_ret (R_refl).  At R := wle every premise is
   the strict hypothesis of the same name (rig_spec_x_wle, cnl_spec_x_wle, cshe_spec_x_wle) and the statement is
   lf_arm_gone_x's. *)
Section gxxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Hypothesis RIG_R : rig_spec_xR B PST ARx R MT RP MMAX fr_RG ACk0.CTX_AFREE (BASE + AF_fr_relay_instance_gone).
Hypothesis CNL_R : forall G, gx_ok segs B G -> gx_rt B G ->
  cnl_spec_xR B PST ARx R MT RP G MMAX (BASE + AF_fr_check_no_loss).
Hypothesis CSHE_R : forall G, gx_ok segs B G -> gx_rt B G ->
  cshe_spec_xR B PST ARx R MT RP G (BASE + AF_fr_check_shape_ends).
Let GP0R := gp0_entry_join_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV HERR
  BLKN R.
Let GP1R := gp1_join_l1_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV TL SNP HGOTG
  GN_LITS BLKN FRMF R R_trans WLE_R.
Let GP2R := gp2_l1_rig_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV HZS HERR
  BLKN R.
Let GP3R := gp3_rig_c1_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV MMAX RP RGP
  HGRIG HPAIRS HFDS HLSRIG gn_pk RPNP CNTRIG LSCNT HGCELLS GWR HROMPIN gx_errno_apart BLKN HPST R R_trans WLE_R RIG_R.
Let GP4R := gp4_c1_t0_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV HZS RIR CNLR
  HGCELLS HROMPIN HPST R R_trans WLE_R.
Let GP5R := gp5_t0_csd_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV MMAX RP HGs
  HGCELLS HROMPIN HZS HCE RIstep RIend gn_pk RPNP LSCNT CNTSTEP GWR ML HERR HERRROM BLKN HPST FRMF R R_refl R_trans WLE_R
  CNL_R CSHE_R.
Let GP6R := gp6_csd_latch_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV TL CSD HGCELLS
  HROMPIN BLKN HPST R R_trans WLE_R.
(* ---- ARM_gone_R (cut_x Section wR) ---- *)
Theorem lf_arm_gone_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 5 cx Hp t W c ->
  SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  intros cx Hp t W c HB HA.
  (* the entry's ghost list is empty (HP0 on the pre's ARx): the walk runs at [] *)
  assert (EHp : Hp = []) by (pose proof HB as (_ & HPRE); exact (HP0 _ _ _ _ _ _ (proj1 (proj1 HPRE)))).
  subst Hp.
  eapply (SRrG_bind segs R R_trans); [exact (SRr_SRrG segs R WLE_R _ _ _ (GP0R cx t W c HB HA))|].
  intros W0 c0 _ (m & HJN).
  eapply (SRrG_bind segs R R_trans); [exact (GP1R cx t m W0 c0 HB HJN)|].
  intros W1 c1 _ HL1.
  eapply (SRrG_bind segs R R_trans); [exact (SRr_SRrG segs R WLE_R _ _ _ (GP2R 0%nat cx t m W1 c1 HB HL1))|].
  intros W2 c2 _ HRG.
  eapply (SRrG_bind segs R R_trans); [exact (GP3R cx t m W2 c2 HB HRG)|].
  intros W3 c3 _ (m1 & HC1).
  eapply (SRrG_bind segs R R_trans); [exact (SRr_SRrG segs R WLE_R _ _ _ (GP4R 0%nat cx t m m1 W3 c3 HB HC1))|].
  intros W4 c4 _ HT0.
  eapply (SRrG_bind segs R R_trans); [exact (GP5R cx t m m1 W4 c4 HB HT0)|].
  intros W5 c5 _ (mc & HCSD).
  eapply (SRrG_bind segs R R_trans); [exact (SRr_SRrG segs R WLE_R _ _ _ (GP6R cx t m mc W5 c5 HB HCSD))|].
  intros W6 c6 _ HK. exact (SRrG_ret segs R R_refl W6 c6 _ HK).
Qed.
End gxxR.
End gxx.

(* ---------------------------------------------------------------- THE CHECK
   In cut_x's scope (its Section w header and this piece's hypotheses): lf_arm_gone_x's type is cut_x's Section w
   hypothesis ARM_gone (W_LLVMFuzzerTestOneInput_cut_x.v:557), restated and closed by `exact`, and it fills that slot
   of cut_x's composition lf_contract_of_segments_x. *)
Section chk.
(* cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:191-235) *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* the instance's ghost poisoned-head set stays empty (a Theorem Labs lane's HP0 ruling, W_journal_x at 0c4d57d9bf1;
   fuzz_reply calls no poison routine): the driver reads the post's Hp' = [] from the journal's ARx through it *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
(* errno's place; phase 0 takes it to carry the stream's cells across its two stack stores *)
Hypothesis HERR : GN_ERRNO_LOW B.
(* the allocator instance (W_kit.v); phase 1 (snprintf's interceptor) and phase 6 (errno's place, pal_env) take it *)
Hypothesis TL : PALib B.
(* g_s lies in the instance's zero-shadow ranges *)
Hypothesis HZS : GN_HZS B.
(* the slots check_no_loss_read is called on have no pending record *)
Hypothesis RIR : GN_RI_read RINV.
(* snprintf, the pf chain's interceptor contract: W_sites_x.v:392 asnprintf_realizes_x, the twin of _gone.v's SNP *)
Hypothesis SNP : asnprintf_realizes_x B ARx (SIGMA WS_snprintf) FR_GOT_GUARD FR_GUARD.
(* _gone.v's HGOTG and GN_LITS over ARx (Hp after S) *)
Hypothesis HGOTG : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md ->
  rdword (aview segs (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
Hypothesis GN_LITS : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 20)) 7 /\
  shadow_hull_vis (aview segs (w_H W) mem) (VAL (A_OBJ 20)) 7 /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 21)) 14 /\
  shadow_hull_vis (aview segs (w_H W) mem) (VAL (A_OBJ 21)) 14.
(* ---- relay_instance_gone (phase 3) ---- *)
Variable MMAX : Z.                                   (* W6's / W7's request bound *)
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c) / (d)): the room record the callees are taken at.  At the instance
   RM := fun S _ => NP S, so RPNP below holds by conversion *)
Variable RP : roomp.
(* W6's contract over ARx: W_contract_x.v rig_spec_x at CTX_AFREE := K0's table ACk0.CTX_AFREE (the kit of record
   628b62f1a9e); rg_place verbatim *)
Hypothesis RIG : rig_spec_x B PST ARx MT RP MMAX fr_RG ACk0.CTX_AFREE (BASE + AF_fr_relay_instance_gone).
Hypothesis RGP : rg_place B fr_RG.
(* the base's model obligations phase 3 takes *)
Hypothesis HGRIG : GN_HG_RIG B G_fr.
Hypothesis HPAIRS : GN_RI_pairs RINV.
Hypothesis HFDS : GN_RI_fds RINV.
Hypothesis HLSRIG : GN_LS_rig MT LSx RINV MMAX.
(* the room round's count row and model count rules (top_x's rows): gn_pk is the arm's peak (s5-r1d's pk_gone at the
   instance); LSCNT is GN_LS_cnt_x (_gone_base_x.v); CNTRIG is GN_CNT_rig at relay_instance_gone's premise peak
   rig_pk (W_contract_x.v:312) of its trace; CNTSTEP (phase 5, below) is GN_CNT_step at check_no_loss's cnl_pk *)
Variable gn_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat.
Hypothesis RPNP : forall S k, rp_RM RP S k <-> NP S.
Hypothesis CNTRIG : GN_CNT_rig gn_pk (fun cx m hs =>
  rig_pk (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs)).
Hypothesis LSCNT : GN_LS_cnt_x B LSx RINV RP gn_pk.
Hypothesis HGCELLS : GN_HGcells G_fr.
Hypothesis GWR : glob_wr_law G_fr.
Hypothesis HROMPIN : GN_ROM_PIN B.
(* errno is none of the model's cells (base GN_CELLS_ERRNO) and no read-only byte; both proved for the
   instance in lib/A/W_LLVMFuzzerTestOneInput_G.v (c_CELLS_ERRNO, c_ROM_ERR) *)
Hypothesis HCE : GN_CELLS_ERRNO B.
Hypothesis HERRROM : forall a, in_rom segs a -> ~ (as_errno B <= a < as_errno B + 4).
(* ---- the table-order loop (phase 5): W3's check_no_loss / check_shape_ends over ARx (W_contract_x.v cnl_spec_x /
   cshe_spec_x), G-generic as _gone.v takes them *)
Hypothesis CNL : forall G, gx_ok segs B G -> gx_rt B G -> cnl_spec_x B PST ARx MT RP G MMAX (BASE + AF_fr_check_no_loss).
Hypothesis CSHE : forall G, gx_ok segs B G -> gx_rt B G -> cshe_spec_x B PST ARx MT RP G (BASE + AF_fr_check_shape_ends).
(* the base's model obligations phase 5 takes *)
Hypothesis HGs : GN_HGs G_fr.
Hypothesis RIstep : GN_RI_step B MT LSx RINV MMAX.
Hypothesis RIend : GN_RI_end B MT LSx RINV.
Hypothesis CNTSTEP : GN_CNT_step RINV gn_pk (fun h => cnl_pk (hs_expected h) (hs_held h)).
(* the allocator instance's meter laws (Reusable/YC5d.v:26) *)
Hypothesis ML : ameter_laws MT.
(* check_no_loss_read (phase 4) and check_shape_done (phase 6) over ARx: W_contract_x.v cnlr_spec_x / csd_spec_x *)
Hypothesis CNLR : cnlr_spec_x B PST ARx (BASE + AF_fr_check_no_loss_read).
Hypothesis CSD : csd_spec_x B PST ARx (BASE + AF_fr_check_shape_done).
(* ---- forced by the generic relation and the placement PST ---- *)
(* OWED: kit _x twin of al_blocks' last conjunct (AR's 0 <= n < MALLOC_MAX, YG0d.v:441; ARx_blocks_law has no size
   conjunct).  The text is W_kit_x.v's BLKN (add_x's). *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST): the callee journals' image clause and the ROM-view lemma take it *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* W_frame_x.v:105's Section hypothesis FRMF (the generic counterpart of YG0s.v:442 frame_facts' fake-frame
   alignment), which frame_al64_x and shadow_hull_vis_of_frame_x take (phases 1 and 5) *)
Hypothesis FRMF : forall ly S Hp (W : world segs) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.
Local Notation BASEx cx Hp := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp).
Local Notation IA := (INV_A_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation IK := (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV).
Lemma lf_arm_gone_x_check : forall cx Hp t W c, BASEx cx Hp -> IA 5 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Proof.
  exact (lf_arm_gone_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV
    HERR TL HZS RIR SNP HGOTG GN_LITS MMAX RP RIG RGP HGRIG HPAIRS HFDS HLSRIG gn_pk RPNP CNTRIG LSCNT HGCELLS GWR
    HROMPIN HCE HERRROM CNL CSHE HGs RIstep RIend CNTSTEP ML CNLR CSD BLKN HPST FRMF).
Qed.
Definition gone_x_slot :=
  fun SEG_PRO SEG_HEAD ARM_add ARM_write ARM_drain ARM_close ARM_remove ARM_eintr ARM_event ARM_sendmax ARM_default
    SEG_LATCH SEG_EXIT =>
  lf_contract_of_segments_x B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx
    LAWS HG LSx RINV SEG_PRO SEG_HEAD ARM_add ARM_write ARM_drain ARM_close ARM_remove lf_arm_gone_x_check ARM_eintr
    ARM_event ARM_sendmax ARM_default SEG_LATCH SEG_EXIT.
(* ---- route R: lf_arm_gone_xR's type is cut_x's Section wR hypothesis ARM_gone_R (W_LLVMFuzzerTestOneInput_cut_x.v:461),
   restated and closed by `exact`, and it fills that slot of cut_x's composition lf_contract_of_segments_xR. *)
Section chkR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Hypothesis RIG_R : rig_spec_xR B PST ARx R MT RP MMAX fr_RG ACk0.CTX_AFREE (BASE + AF_fr_relay_instance_gone).
Hypothesis CNL_R : forall G, gx_ok segs B G -> gx_rt B G ->
  cnl_spec_xR B PST ARx R MT RP G MMAX (BASE + AF_fr_check_no_loss).
Hypothesis CSHE_R : forall G, gx_ok segs B G -> gx_rt B G ->
  cshe_spec_xR B PST ARx R MT RP G (BASE + AF_fr_check_shape_ends).
Local Notation IAR := (INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation IKR := (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R).
Lemma lf_arm_gone_xR_check : forall cx Hp t W c, BASEx cx Hp -> IAR 5 cx Hp t W c -> SRrG segs R W c (IKR cx Hp t).
Proof.
  exact (lf_arm_gone_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV
    HERR TL HZS RIR SNP HGOTG GN_LITS MMAX RP RGP HGRIG HPAIRS HFDS HLSRIG gn_pk RPNP CNTRIG LSCNT HGCELLS GWR
    HROMPIN HCE HERRROM HGs RIstep RIend CNTSTEP ML CNLR CSD BLKN HPST FRMF R R_refl R_trans WLE_R RIG_R CNL_R CSHE_R).
Qed.
Definition gone_x_slotR :=
  fun SEG_PRO_R SEG_HEAD_R ARM_add_R ARM_write_R ARM_drain_R ARM_close_R ARM_remove_R ARM_eintr_R ARM_event_R
    ARM_sendmax_R ARM_default_R SEG_LATCH_R SEG_EXIT_R =>
  lf_contract_of_segments_xR B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx
    LAWS HG LSx RINV R R_refl R_trans WLE_R SEG_PRO_R SEG_HEAD_R ARM_add_R ARM_write_R ARM_drain_R ARM_close_R
    ARM_remove_R lf_arm_gone_xR_check ARM_eintr_R ARM_event_R ARM_sendmax_R ARM_default_R SEG_LATCH_R SEG_EXIT_R.
End chkR.
End chk.
