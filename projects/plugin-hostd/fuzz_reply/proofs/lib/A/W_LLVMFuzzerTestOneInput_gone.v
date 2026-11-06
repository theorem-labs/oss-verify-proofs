(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput
   (fuzz_reply.asan 0x845e4-0x84610 and 0x846e0-0x84980, fuzz_reply.c:633-655 and :718-720), in the form of the cgif
   entry walk's arms (proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v: a segment is an SRr from one cut point's invariant to
   the next) over the cut invariants of W_LLVMFuzzerTestOneInput_cut.v.
   THIS FILE IS THE ARM'S COMPOSITION: lf_arm_gone (= _cut.v:580's ARM_gone) from the seven phase lemmas, by
   SRr_bind, in the shape of W_LLVMFuzzerTestOneInput_drain.v's lf_arm_drain (:1884).
   The arm's building blocks, its cut points and the texts of everything the other lanes owe are in
   lib/A/W_LLVMFuzzerTestOneInput_gone_base.v; the phases are proved in lib/A/W_LLVMFuzzerTestOneInput_gone_p<n>.v:
     p0  INV_A 5         -> GJN   0x845e4 -> 0x846f0   the id byte (or not), both in.n cases
     p1  GJN             -> GL1 0        0x846f0 -> 0x84738   the prefix's unpoison, at = 0, snprintf
     p2  GL1 q           -> GRG          0x84738 -> 0x84834   the reads[] loop, relay_source inlined
     p3  GRG             -> GC1 0        0x84834 -> 0x84848   relay_instance_gone(id)
     p4  GC1 q           -> GT0          0x84848 -> 0x84864   the check_no_loss_read loop
     p5  GT0             -> GCSD         0x84864 -> 0x8494c   the table-order loop (check_no_loss / check_shape_ends)
     p6  GCSD            -> INV_K        0x8494c -> 0x84490   check_shape_done, the re-poison, the latch
   Every phase is a Qed lemma of its file; GP0 .. GP6 below are those lemmas applied to this Section's
   variables.  The Section hypotheses are the callee contracts and the model obligations named in the base;
   none is a phase. *)
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
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section gx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
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
(* errno's place; phase 0 takes it to carry the stream's cells across its two stack stores *)
Hypothesis HERR : GN_ERRNO_LOW B.
(* the allocator instance (W_kit.v); phase 1 (snprintf's interceptor) and phase 6 (errno's place, pal_env) take it *)
Hypothesis TL : PALib B.
(* g_s lies in the instance's zero-shadow ranges *)
Hypothesis HZS : GN_HZS B.
(* the slots check_no_loss_read is called on have no pending record *)
Hypothesis RIR : GN_RI_read RINV.
(* snprintf, the pf chain's interceptor contract: W_sites.v:305, verbatim (a callee contract) *)
Hypothesis SNP : asnprintf_realizes B (SIGMA WS_snprintf) FR_GOT_GUARD FR_GUARD.
(* the GOT word of __stack_chk_guard, readable at every AR state: W6's HGOTG, verbatim
   (commit 6a1bcf9f403, lib/A/W_relay_instance_gone_cx.v:202); TRUE at the pin from AF0m's const
   cell `z8 (ANum 0x9e658) 0x5f94b0` through am_const *)
Hypothesis HGOTG : forall ly S W mem md, AR segs B ly S W mem md ->
  rdword (aview segs (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
(* the shadow checks snprintf makes of its two .rodata literals pass at every AR state; TRUE at the pin
   from AF0m's partial-granule shadow cells and its zero-shadow ranges (the azs form is FALSE there) *)
Hypothesis GN_LITS : forall ly S (W : world segs) mem md, AR segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 20)) 7 /\
  shadow_hull_vis (aview segs (w_H W) mem) (VAL (A_OBJ 20)) 7 /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 21)) 14 /\
  shadow_hull_vis (aview segs (w_H W) mem) (VAL (A_OBJ 21)) 14.
(* ---- relay_instance_gone (phase 3) ---- *)
Variable MMAX : Z.                                   (* W6's / W7's request bound *)
(* W6's contract and its placement premise, verbatim (W_contract.v Section s6 rig_spec at CTX_AFREE := K0's table
   ACk0.CTX_AFREE, W6 fc80eaecde5; rg_place); callee contracts *)
Hypothesis RIG : rig_spec B MT MMAX fr_RG ACk0.CTX_AFREE (BASE + AF_fr_relay_instance_gone).
Hypothesis RGP : rg_place B fr_RG.
(* the base's model obligations phase 3 takes *)
Hypothesis HGRIG : GN_HG_RIG B G_fr.
Hypothesis HPAIRS : GN_RI_pairs RINV.
Hypothesis HFDS : GN_RI_fds RINV.
Hypothesis HLSRIG : GN_LS_rig MT LS RINV MMAX.
Hypothesis HGCELLS : GN_HGcells G_fr.
Hypothesis GWR : glob_wr_law G_fr.
Hypothesis HROMPIN : GN_ROM_PIN B.
(* errno is none of the model's cells (base GN_CELLS_ERRNO) and no read-only byte; both proved for the
   instance in lib/A/W_LLVMFuzzerTestOneInput_G.v (c_CELLS_ERRNO, c_ROM_ERR) *)
Hypothesis HCE : GN_CELLS_ERRNO B.
Hypothesis HERRROM : forall a, in_rom segs a -> ~ (as_errno B <= a < as_errno B + 4).
(* phase 3's own GP3_ERRNO_APART, DERIVED from those two: its four cells are cells of gn_cells *)
Lemma gx_errno_apart : forall a, gp3_g4 a \/ in_rom segs a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a [Hg | Hr]; [|exact (HERRROM a Hr)].
  apply HCE. unfold gp3_g4 in Hg. unfold gn_cells, inG.
  destruct Hg as [H|[H|[H|H]]];
    repeat (first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]).
Qed.
(* ---- the table-order loop (phase 5): W3's check_no_loss / check_shape_ends ---- *)
(* callee contracts, W_contract.v's own texts on the W8 lane head a3c72093c22: cnl_spec (:1968) and cshe_spec
   (:1812), G-generic as W_LLVMFuzzerTestOneInput_remove.v:408 takes check_no_loss (W3 proves both at any G with
   gx_ok: pb_check_no_loss W_check_no_loss.v:6097, pb_check_shape_ends W_cshe_top.v:614).  Phase 5 takes each at
   the call's own G, gn_Gs j. *)
Hypothesis CNL : forall G, gx_ok segs B G -> gx_rt B G -> cnl_spec B MT G MMAX (BASE + AF_fr_check_no_loss).
Hypothesis CSHE : forall G, gx_ok segs B G -> gx_rt B G -> cshe_spec B MT G (BASE + AF_fr_check_shape_ends).
(* the base's model obligations phase 5 takes *)
Hypothesis HGs : GN_HGs G_fr.
Hypothesis RIstep : GN_RI_step B MT LS RINV MMAX.
Hypothesis RIend : GN_RI_end B MT LS RINV.
(* the allocator instance's meter laws (Reusable/YC5d.v:26) *)
Hypothesis ML : ameter_laws MT.
(* check_no_loss_read (phase 4) and check_shape_done (phase 6): W_contract.v's cnlr_spec (:454) and csd_spec (:130)
   on a3c72093c22, verbatim (the texts _remove.v:405 / :403 take) *)
Hypothesis CNLR : cnlr_spec B (BASE + AF_fr_check_no_loss_read).
Hypothesis CSD : csd_spec B (BASE + AF_fr_check_shape_done).

(* ---- the phases: all seven are Qed lemmas (lib/A/W_LLVMFuzzerTestOneInput_gone_p<n>.v) ---- *)
Definition GP0 := gp0_entry_join B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG LS RINV HERR.
Definition GP1 := gp1_join_l1 B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG LS RINV TL SNP HGOTG GN_LITS.
Definition GP2 := gp2_l1_rig B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG LS RINV HZS HERR.
Definition GP3 := gp3_rig_c1 B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG LS RINV MMAX RIG RGP HGRIG
  HPAIRS HFDS HLSRIG HGCELLS GWR HROMPIN gx_errno_apart.
Definition GP4 := gp4_c1_t0 B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG LS RINV HZS RIR CNLR HGCELLS
  HROMPIN.
Definition GP5 := gp5_t0_csd B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG LS RINV MMAX CNL CSHE HGs HGCELLS
  HROMPIN HZS HCE RIstep RIend GWR ML HERR HERRROM.
Definition GP6 := gp6_csd_latch B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS HG LS RINV TL CSD HGCELLS HROMPIN.

(* ---- ARM_gone (_cut.v:580) ---- *)
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
