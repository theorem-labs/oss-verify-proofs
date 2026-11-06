(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput on image B
   (fuzz_reply.asan-ubsan 0x849a0-0x849d0, 0x84a9c-0x84cb4, 0x84da4-0x84dac, 0x84e30-0x84e38; fuzz_reply.c:633-655 and
   :718-720), over the cut invariants of lib/B/W_LLVMFuzzerTestOneInput_cut.v (a working branch
   61da015af91, with a working branch 990666444ab).
   THIS FILE IS THE ARM'S COMPOSITION: lf_arm_gone (= _cut.v's ARM_gone, :762) from the seven phase lemmas, by SRr_bind,
   in the shape of image A's lib/A/W_LLVMFuzzerTestOneInput_gone.v:154 (a working branch e8dddfa51f7).
   The arm's cut points, model and obligation texts are in lib/B/W_LLVMFuzzerTestOneInput_gone_base.v; the phases are
   proved in lib/B/W_LLVMFuzzerTestOneInput_gone_p<n>.v:
     p0  INV_A 5  -> GJN    0x849a0 -> 0x84aa8   the id byte (or not), the cursor slots
     p1  GJN      -> GL1 0  0x84aa8 -> 0x84af8   the prefix's unpoison, at = 0, snprintf (0x84ae0)
     p2  GL1 q    -> GRG    0x84af8 -> 0x84b40   the reads[] loop, relay_reads (0x84b0c) through the cut's RRDS
     p3  GRG      -> GC1 0  0x84b40 -> 0x84b5c   relay_instance_gone(id) (0x84b48)
     p4  GC1 q    -> GT0    0x84b5c -> 0x84b78   the check_no_loss_read loop (0x84b68, walked inline)
     p5  GT0      -> GCSD   0x84b78 -> 0x84c84   the table-order loop: check_no_loss (0x84c14), check_shape_ends (0x84c24)
     p6  GCSD     -> INV_K  0x84c84 -> 0x84804   check_shape_done (0x84c88, walked inline), the re-poison, the latch
   Every phase is a Qed lemma of its file; GP0 .. GP6 below are those lemmas at this Section's variables.  The
   Section hypotheses are the cut's Section w context (LAWS, HG, glob_wr_law, errno_law, RRDS), the kit's callee
   contracts (asnprintf_realizes, rig_spec / rg_place, cnl_spec / cshe_spec per slot), the allocator instance (PALib,
   ameter_laws) and the base's instance facts and model obligations (its GN_ texts); none is a phase.  The instance
   facts decided at the real instance (G_fr := G_fr_c B, YF0m.TfibSyms B, errno at 0x5d994c) are the gi_* lemmas of
   lib/B/W_LLVMFuzzerTestOneInput_gone_inst.v, each of exactly one hypothesis's type. *)
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
(* The sink-instance guard (MERGE.md (sha256 0694aca87ccd; internal record) rule 3): every sink argument is passed with @ or from the Context *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
(* K0's caller-context tables (rig_spec's CTX_AFREE is image B's YCk0.CTX_AFREE at the instance) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCk0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section gx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- the cut's Section w context (_cut.v:302-312, :428, :431) ---- *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* the cut's two laws (_cut.v:316, :318), discharged at integration *)
Hypothesis GWR : glob_wr_law G_fr.
Hypothesis ERRL : errno_law B.
(* relay_reads (0x864e8), phase 2: the cut's RRDS (_cut.v:707 at 61da015af91), text verbatim (a Theorem Labs lane's) *)
Hypothesis RRDS : forall W ly S (regs : bvmap 5 word) mem md ch T es HA h,
  afn_pre segs B RRDS_STK ly S W regs mem md ch ->
  getr regs 10 = w64 HA -> 0 < HA -> HA mod 8 = 0 -> azs B HA 4 ->
  asrc_at B ly S W mem HA h ->
  arelay_at B fr_RG ly S W mem T es -> rom_view segs W mem ->
  SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_reads) regs mem md)
    (aleafx_post B RRDS_STK regs ly S W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = hs_fd h /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> hs_fd h) /\
            a0 = w64 (if re_eof e =? 0 then 1 else 0)) \/
         ((forall e, In e es -> re_fd e <> hs_fd h) /\ a0 = w64 0))).
(* ---- the allocator instance (W_kit.v PALib; Reusable/YC5d.v ameter_laws) ---- *)
Hypothesis TL : PALib B.
Hypothesis ML : ameter_laws MT.
(* ---- snprintf (phase 1): W_sites.v:308 asnprintf_realizes at B's stack-protector cells, and p1's instance facts ---- *)
Hypothesis SNP : asnprintf_realizes B (SIGMA WS_snprintf) FR_GOT_GUARD FR_GUARD.
Hypothesis HGOTG : forall ly S W mem md, AR segs B ly S W mem md ->
  rdword (aview segs (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
Hypothesis GN_LIT_GES : ashp (PI := PB_fr) B (VAL A_lit_gesture) 14.
Hypothesis GN_LIT_FMT : ashp (PI := PB_fr) B (VAL (A_OBJ 17)) 7.
(* ---- relay_instance_gone (phase 3): W_contract.v rig_spec at image B's K0 table YCk0.CTX_AFREE / rg_place,
   verbatim (the CTX_AFREE adaptation is image A's, 95cae0d4740) ---- *)
Variable MMAX : Z.
Hypothesis RIG : rig_spec (PI := PB_fr) B MT MMAX fr_RG YCk0.CTX_AFREE (BASE + AF_fr_relay_instance_gone).
Hypothesis RGP : rg_place (PI := PB_fr) B fr_RG.
Hypothesis HRO : rom_out segs B G_fr.
(* ---- check_no_loss / check_shape_ends (phase 5): the kit's cnl_spec / cshe_spec per slot (base GN_CNL / GN_CSHE) ---- *)
Hypothesis CNL : GN_CNL B MT MMAX.
Hypothesis CSHE : GN_CSHE B MT.
(* ---- the base's instance facts ---- *)
Hypothesis HERR : GN_ERRNO_LOW B.
Hypothesis HZS : GN_HZS B.
Hypothesis HGs : GN_HGs G_fr.
Hypothesis HGRIG : GN_HG_RIG B G_fr.
Hypothesis HGCELLS : GN_HGcells G_fr.
Hypothesis HCE : GN_CELLS_ERRNO B.
Hypothesis HROMPIN : GN_ROM_PIN B.
(* ---- the base's model obligations ---- *)
Hypothesis HPAIRS : GN_RI_pairs RINV.
Hypothesis HFDS : GN_RI_fds RINV.
Hypothesis RIR : GN_RI_read RINV.
Hypothesis RIstep : GN_RI_step B MT LS RINV MMAX.
Hypothesis RIend : GN_RI_end B MT LS RINV.
Hypothesis HLSRIG : GN_LS_rig MT LS RINV MMAX.

(* ---- the phases: all seven are Qed lemmas (lib/B/W_LLVMFuzzerTestOneInput_gone_p<n>.v) ---- *)
Definition GP0 := gp0_entry_join B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG LS RINV HERR.
Definition GP1 := gp1_join_l1 B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG LS RINV TL SNP HGOTG
  GN_LIT_GES GN_LIT_FMT.
Definition GP2 := gp2_l1_rig B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG LS RINV HZS HERR RRDS.
Definition GP3 := gp3_rig_c1 B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG LS RINV MMAX RIG RGP HGRIG
  HPAIRS HFDS HLSRIG HERR HGCELLS GWR HCE HRO.
Definition GP4 := gp4_c1_t0 B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG LS RINV TL HZS HERR RIR.
Definition GP5 := gp5_t0_csd B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG LS RINV HGs HGCELLS HROMPIN HZS
  HCE RIend GWR ERRL HERR MMAX CNL CSHE RIstep ML.
Definition GP6 := gp6_csd_latch B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG LS RINV TL.

(* ---- ARM_gone (_cut.v:762) ---- *)
Theorem lf_arm_gone : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> INV_A B G_fr fr_FP LS RINV 5 cx t W c ->
  SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t W c HB HA.
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

End gx.
