(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: ARM_gone (op 5) of the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's
   LLVMFuzzerTestOneInput over the GENERIC allocator relation ARx - THE ARM'S COMPOSITION: lf_arm_gone_x, whose statement
   is the text of the Section hypothesis ARM_gone of lib/B/W_LLVMFuzzerTestOneInput_cut_x.v Section w (:410), checked at
   the end (lf_arm_gone_x_check).
   The AR proof is a Theorem Labs lane's (a working branch 4118c28f01e: lib/B/W_LLVMFuzzerTestOneInput_gone.v
   lf_arm_gone over _gone_base / _tk / _p0 .. _p6), with our two adaptations to the current kit and cut, which change
   no Theorem line (4c35818d04c: gone_base's HB-clause `& _`; gone_p3 / gone's RIG at the kit's CTX_AFREE rig_spec, as
   image A's 95cae0d4740).  No AR file and no kit file is edited here.  Template: SmallX's image-A conversion
   lib/A/W_LLVMFuzzerTestOneInput_gone*_x.v (a working branch 95a5de32ab2), merged per item into B's
   files (3-way: A's AR item, SmallX's ARx item, B's AR item) and finished by hand.
   Proves no function (kind: segment walk - a segment of the entry function; its callees are named contracts).
   THIS FILE IS THE ARM'S COMPOSITION, as _gone.v's: lf_arm_gone_x from the seven phase lemmas, by SRr_bind.  The phases
   are converted in lib/B/W_LLVMFuzzerTestOneInput_gone_p<n>_x.v (p5 as _p5a_x / _p5b_x / _p5_x, as B splits it) over
   the cut points of _gone_base_x.v and the transport kit _gone_tk_x.v.  cut_x's HP0 makes every ghost list of the walk
   empty: the entry's Hp is [] (from lf_base_x's ARx), and each phase runs at [].
   Section hypotheses beyond cut_x's Section w header (B .. RINV, verbatim), in _gone.v's order:
     the AR-free ones verbatim (GWR, TL, ML, RGP, HRO, HERR, HZS, HGs, HGRIG, HGCELLS, HCE, HROMPIN, HPAIRS, HFDS, RIR;
       RIstep / RIend / HLSRIG with LS -> LSx; MMAX);
     the callee contracts in their kit _x forms: SNP asnprintf_realizes_x (W_sites_x.v), RIG rig_spec_x at image B's
       K0 table YCk0.CTX_AFREE (W_contract_x.v), CNL / CSHE base_x's GN_CNL_x / GN_CSHE_x (cnl_spec_x / cshe_spec_x per
       slot), RRDS_x cut_x's (a Theorem Labs lane proves it); ERRL cut_x's errno_law_x; HGOTG and GN_LIT_GES / GN_LIT_FMT over
       ARx (W_contract_x.v ashp_x for W_shadow_pin.v's ashp);
     the generic relation's facts, as on image A: BLKN (W_kit_x.v's text), HPST (add_x's text), FRMF (W_frame_x.v's);
     the room round's items (image A's re-fit d3a30b1562c..6e8e0f9f8148, ported at B's names): the room record RP that
       RIG / CNL / CSHE are taken at, the arm's peak gn_pk, RPNP (RM is NP at the instance), CNTRIG (_gone_base.v's
       GN_CNT_rig at rig_pk), LSCNT (_gone_base_x.v's GN_LS_cnt_x) and CNTSTEP (_gone_base.v's GN_CNT_step at
       cnl_pk).  INV_A_x / INV_K_x take NP (cut_x's lcut_x carries NP S3 since the room cut). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_kit_xb W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img_x.
(* W_LLVMFuzzerTestOneInput_gone.v's own imports, AFTER the generic kit's: the converted proofs see the names they were written against *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_p0 W_LLVMFuzzerTestOneInput_gone_p1
W_LLVMFuzzerTestOneInput_gone_p2 W_LLVMFuzzerTestOneInput_gone_p3 W_LLVMFuzzerTestOneInput_gone_p4
W_LLVMFuzzerTestOneInput_gone_p5 W_LLVMFuzzerTestOneInput_gone_p6.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_contract_xR_relayB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p0_x W_LLVMFuzzerTestOneInput_gone_p1_x W_LLVMFuzzerTestOneInput_gone_p2_x W_LLVMFuzzerTestOneInput_gone_p3_x W_LLVMFuzzerTestOneInput_gone_p4_x W_LLVMFuzzerTestOneInput_gone_p5a_x W_LLVMFuzzerTestOneInput_gone_p5b_x W_LLVMFuzzerTestOneInput_gone_p5_x W_LLVMFuzzerTestOneInput_gone_p6_x W_LLVMFuzzerTestOneInput_gone.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag as W_LLVMFuzzerTestOneInput_gone.v's proofs see it (true: its imports' last setting), whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* @@ SECTION gxx *)
Section gxx.
(* cut_x's Section w header (W_LLVMFuzzerTestOneInput_cut_x.v:199-244), verbatim *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
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
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---------------------------------------------------------------- ARM_gone's own hypotheses, in _gone.v's order *)
(* the cut's two laws (_cut.v:316, :318): glob_wr_law verbatim, errno_law as cut_x's errno_law_x *)
Hypothesis GWR : glob_wr_law G_fr.
Hypothesis ERRL : errno_law_x B ARx.
(* relay_reads (0x864e8), phase 2: cut_x's Section hypothesis RRDS_x (W_LLVMFuzzerTestOneInput_cut_x.v:580), verbatim
   (a Theorem Labs lane proves it, 72c71080dd0) *)
Hypothesis RRDS_x : forall W ly S Hp (regs : bvmap 5 word) mem md ch T es HA h,
  afn_pre_x segs B ARx RRDS_STK ly S Hp W regs mem md ch ->
  getr regs 10 = w64 HA -> 0 < HA -> HA mod 8 = 0 -> azs B HA 4 ->
  asrc_at B ly S W mem HA h ->
  arelay_at B fr_RG ly S W mem T es -> rom_view segs W mem ->
  SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_reads) regs mem md)
    (aleafx_post_x B PST ARx RRDS_STK regs ly S Hp W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = hs_fd h /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> hs_fd h) /\
            a0 = w64 (if re_eof e =? 0 then 1 else 0)) \/
         ((forall e, In e es -> re_fd e <> hs_fd h) /\ a0 = w64 0))).
(* ---- the allocator instance (W_kit.v PALib; Reusable/YC5d.v ameter_laws) ---- *)
Hypothesis TL : PALib B.
Hypothesis ML : ameter_laws MT.
(* ---- snprintf (phase 1): the kit's asnprintf_realizes_x (W_sites_x.v), and p1's instance facts over ARx ---- *)
Hypothesis SNP : asnprintf_realizes_x B ARx (SIGMA WS_snprintf) FR_GOT_GUARD FR_GUARD.
Hypothesis HGOTG : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md ->
  rdword (aview segs (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
Hypothesis GN_LIT_GES : ashp_x (PI := PB_fr) ARx (VAL A_lit_gesture) 14.
Hypothesis GN_LIT_FMT : ashp_x (PI := PB_fr) ARx (VAL (A_OBJ 17)) 7.
(* ---- relay_instance_gone (phase 3): the kit's rig_spec_x at image B's K0 table YCk0.CTX_AFREE / rg_place ---- *)
Variable MMAX : Z.
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c) / (d)): the room record the callees are taken at.  At the instance
   RM := fun S _ => NP S, so RPNP below holds by conversion *)
Variable RP : roomp.
Hypothesis RIG : rig_spec_x (PI := PB_fr) B PST ARx MT RP MMAX fr_RG YCk0.CTX_AFREE (BASE + AF_fr_relay_instance_gone).
Hypothesis RGP : rg_place (PI := PB_fr) B fr_RG.
Hypothesis HRO : rom_out segs B G_fr.
(* ---- check_no_loss / check_shape_ends (phase 5): base_x's GN_CNL_x / GN_CSHE_x (the kit's cnl_spec_x / cshe_spec_x
   per slot, at RP) ---- *)
Hypothesis CNL : GN_CNL_x B MT PST ARx MMAX RP.
Hypothesis CSHE : GN_CSHE_x B MT PST ARx RP.
(* ---- the base's instance facts ---- *)
Hypothesis HERR : GN_ERRNO_LOW B.
Hypothesis HZS : GN_HZS B.
Hypothesis HGs : GN_HGs G_fr.
Hypothesis HGRIG : GN_HG_RIG B G_fr.
Hypothesis HGCELLS : GN_HGcells G_fr.
Hypothesis HCE : GN_CELLS_ERRNO B.
Hypothesis HROMPIN : GN_ROM_PIN B.
(* ---- the base's model obligations (LSx -> cut_x's LSx) ---- *)
Hypothesis HPAIRS : GN_RI_pairs RINV.
Hypothesis HFDS : GN_RI_fds RINV.
Hypothesis RIR : GN_RI_read RINV.
Hypothesis RIstep : GN_RI_step B MT LSx RINV MMAX.
Hypothesis RIend : GN_RI_end B MT LSx RINV.
Hypothesis HLSRIG : GN_LS_rig MT LSx RINV MMAX.
(* the room round's count row and model count rules (top_x's rows): gn_pk is the arm's peak (s5-r1d's pk_gone at the
   instance); LSCNT is GN_LS_cnt_x (_gone_base_x.v); CNTRIG is GN_CNT_rig at relay_instance_gone's premise peak
   rig_pk (W_contract_x.v:307) of its trace; CNTSTEP (phase 5) is GN_CNT_step at check_no_loss's cnl_pk *)
Variable gn_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat.
Hypothesis RPNP : forall S k, rp_RM RP S k <-> NP S.
Hypothesis CNTRIG : GN_CNT_rig gn_pk (fun cx m hs =>
  rig_pk (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs)).
Hypothesis LSCNT : GN_LS_cnt_x B LSx RINV RP gn_pk.
Hypothesis CNTSTEP : GN_CNT_step RINV gn_pk (fun h => cnl_pk (hs_expected h) (hs_held h)).
(* ---- the generic relation's facts (as on image A, SmallX's gone_x) ---- *)
(* a live block's request is non-negative: W_kit_x.v's BLKN (AR's al_blocks carries it, AR_laws_x's alx_blocks does
   not; the cf instance has 0 <= n as AR_blocks_law_cf's last conjunct) *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST; trivial at the instance's PST := []) *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.
(* W_frame_x.v's Section hypothesis FRMF (the generic counterpart of YG0s.v frame_facts' fake-frame alignment), which
   frame_al64_x reads (phases 1 and 5) *)
Hypothesis FRMF : forall ly S Hp (W : world segs) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  ly_F ly mod 4096 = 0 /\ fs_frame_off cid pos mod 64 = 0 /\ 64 <= fs_frame_bytes cid /\ fs_frame_bytes cid mod 64 = 0.

(* ---- the phases: all seven are Qed lemmas (lib/B/W_LLVMFuzzerTestOneInput_gone_p<n>_x.v), at this Section's
   variables ---- *)
Let GP0 := gp0_entry_join_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV HERR BLKN.
Let GP1 := gp1_join_l1_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV TL SNP HGOTG
  GN_LIT_GES GN_LIT_FMT BLKN FRMF.
Let GP2 := gp2_l1_rig_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV HZS HERR RRDS_x BLKN.
Let GP3 := gp3_rig_c1_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV MMAX RP RIG RGP
  HGRIG HPAIRS HFDS HLSRIG gn_pk RPNP CNTRIG LSCNT HERR HGCELLS GWR HCE HRO BLKN HPST.
Let GP4 := gp4_c1_t0_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV TL HZS HERR RIR BLKN.
Let GP5 := gp5_t0_csd_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV HGs HGCELLS
  HROMPIN HZS HCE RIend GWR ERRL HERR MMAX RP CNL CSHE RIstep gn_pk RPNP LSCNT CNTSTEP ML BLKN HPST FRMF.
Let GP6 := gp6_csd_latch_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV TL BLKN.

(* ---- ARM_gone: the text of cut_x's Section w hypothesis (W_LLVMFuzzerTestOneInput_cut_x.v:630) ---- *)
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

(* CHECK (cut_x's scope): lf_arm_gone_x's type is the Section w hypothesis ARM_gone of
   W_LLVMFuzzerTestOneInput_cut_x.v:630, restated with the generic invariants at this Section's variables *)
Lemma lf_arm_gone_x_check : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_x B NP G_fr fr_FP PST ARx LSx RINV 5 cx Hp t W c -> SRr segs W c (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t).
Proof. exact lf_arm_gone_x. Qed.
(* @@ END gxx *)
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): lf_arm_gone_xR, the R twin of lf_arm_gone_x, concluding cut_x's
   ARM_gone_R, from the seven phase twins (lib/B/W_LLVMFuzzerTestOneInput_gone_p<n>_x.v Sections gp<n>R) over
   gone_base_x's R cut points.  relay_instance_gone, check_no_loss and check_shape_ends take their R specs; snprintf,
   relay_reads, check_no_loss_read and check_shape_done keep their strict specs, lifted inside the phases.  Strict text
   above unchanged. ---- *)
Section gxxR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
(* the freeing callees at R, in the strict order RIG, CNL, CSHE: relay_instance_gone (lib/B/W_contract_xR_relayB.v
   rig_spec_xR), check_no_loss / check_shape_ends per slot (gone_base_x's GN_CNL_xR / GN_CSHE_xR) *)
Hypothesis RIG_R : W_contract_xR_relayB.rig_spec_xR (PI := PB_fr) B PST ARx R MT RP MMAX fr_RG YCk0.CTX_AFREE
  (BASE + AF_fr_relay_instance_gone).
Hypothesis CNL_R : GN_CNL_xR B MT PST ARx MMAX RP R.
Hypothesis CSHE_R : GN_CSHE_xR B MT PST ARx RP R.
Let GP0R := gp0_entry_join_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV HERR BLKN R R_refl.
Let GP1R := gp1_join_l1_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV TL SNP HGOTG GN_LIT_GES GN_LIT_FMT BLKN FRMF R R_refl R_trans WLE_R.
Let GP2R := gp2_l1_rig_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV HZS HERR RRDS_x BLKN R R_refl R_trans WLE_R.
Let GP3R := gp3_rig_c1_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV MMAX RP RGP HGRIG HPAIRS HFDS HLSRIG gn_pk RPNP CNTRIG LSCNT HERR HGCELLS GWR HCE HRO BLKN HPST R R_refl R_trans RIG_R.
Let GP4R := gp4_c1_t0_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV TL HZS HERR RIR BLKN R R_refl R_trans WLE_R.
Let GP5R := gp5_t0_csd_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HP0 HG LSx RINV HGs HGCELLS HROMPIN HZS HCE RIend GWR ERRL HERR MMAX RP RIstep gn_pk RPNP LSCNT CNTSTEP ML BLKN HPST FRMF R R_refl R_trans CNL_R CSHE_R.
Let GP6R := gp6_csd_latch_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS HG LSx RINV TL BLKN R R_refl R_trans WLE_R.

Theorem lf_arm_gone_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R 5 cx Hp t W c ->
  YA0nH.SRrG segs R W c (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t).
Proof.
  intros cx Hp t W c HB HA.
  assert (EHp : Hp = []) by (pose proof HB as (_ & HPRE); exact (HP0 _ _ _ _ _ _ (proj1 (proj1 HPRE)))).
  subst Hp.
  eapply (YA0nH.SRrG_bind segs R R_trans); [exact (GP0R cx t W c HB HA)|].
  intros W0 c0 _ (m & HJN).
  eapply (YA0nH.SRrG_bind segs R R_trans); [exact (GP1R cx t m W0 c0 HB HJN)|].
  intros W1 c1 _ HL1.
  eapply (YA0nH.SRrG_bind segs R R_trans); [exact (GP2R 0%nat cx t m W1 c1 HB HL1)|].
  intros W2 c2 _ HRG.
  eapply (YA0nH.SRrG_bind segs R R_trans); [exact (GP3R cx t m W2 c2 HB HRG)|].
  intros W3 c3 _ (m1 & HC1).
  eapply (YA0nH.SRrG_bind segs R R_trans); [exact (GP4R 0%nat cx t m m1 W3 c3 HB HC1)|].
  intros W4 c4 _ HT0.
  eapply (YA0nH.SRrG_bind segs R R_trans); [exact (GP5R cx t m m1 W4 c4 HB HT0)|].
  intros W5 c5 _ (mc & HCSD).
  exact (GP6R cx t m mc W5 c5 HB HCSD).
Qed.

End gxxR.

End gxx.
