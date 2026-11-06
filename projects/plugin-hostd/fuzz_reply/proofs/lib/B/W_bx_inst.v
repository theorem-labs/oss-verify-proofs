(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: satisfiability witnesses, at image B's concrete global set, for the Section hypotheses of
   lib/B/W_LLVMFuzzerTestOneInput_exit.v (B SEG_EXIT) that are facts about G_fr, errno and the image: the method of
   lib/B/W_LLVMFuzzerTestOneInput_G.v (one concrete witness G_fr := G_fr_c B, as_errno B = TFIB_ERRNO_B = 0x5d994c, the
   start-up table YF0m.TfibSyms B), so the hypotheses below hold together at one model.  Each lemma's statement is the
   exit file's hypothesis text with G_fr := G_fr_c B (and the sink head YE2k.tfib_sink_head):
     XR_HGM, XRF_ERRNO          proved here (vm_compute over B's tables);
     HG_SL, GWR, XRF_ROM_OUT,
     AZS_s                      _G.v's c_HG_SL, c_glob_wr, c_rom_out, c_HZS, restated at the exit file's text.
   Witnesses outside this base (another lane's files): XE_LIT_S = ashp B (VAL (A_OBJ 25)) 1 is
   f11434cea58 lib/B/W_shadow_pin_fr.v:48 ashp_str2_1_fr (and _remove.v:371 rm_ashp_str3); XR_GSHV's
   ranges lie in g_s, whose ashp is the same commit's _G.v:464 c_gs_ashp.  Not witnessed here (as in _G.v): the LS /
   RINV rules (LS_rf_room, LS_exit_budget, LS_exit_end, RI_exit_slots, RI_exit_ends: Section variables, the W8Add LS
   lane's obligations), the callee specs (CSD, SR, CSHE, RFg: each proved in its own walk file), and the kit /
   instance laws the A donor takes unchanged (LAWS, HG, TL, ML, MLM, ASF, FFL, ERR, FP_SINK, AIL, HG_K). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_G W_bx_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section inst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Hypothesis TS : YF0m.TfibSyms B.
Hypothesis HEV : as_errno B = TFIB_ERRNO_B.

(* XR_HGM: every global amodel_at reads lies in G_fr_c (its 20 objects; one forallb by vm_compute) *)
Lemma bxi_XR_HGM : forall a, inG xr_GM a -> inG (G_fr_c B) a.
Proof.
  intros a Ha. apply obj_c.
  assert (Hc : forallb (fun r => existsb (fun g => (fst g <=? fst r) && (fst r + snd r <=? fst g + snd g)) G_fr_obj)
    xr_GM = true) by (vm_compute; reflexivity).
  unfold inG in *. apply Exists_exists in Ha as (r & Hr & Hz).
  rewrite forallb_forall in Hc. pose proof (Hc r Hr) as Hg. apply existsb_exists in Hg as (g & Hgin & Hg).
  apply andb_prop in Hg as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply Exists_exists. exists g. split; [exact Hgin|]. unfold in_zr in *. lia.
Qed.
(* XRF_ERRNO: errno (0x5d994c) lies above g_out + 8 (0x5d90c8) *)
Lemma bxi_XRF_ERRNO : rg_out fr_RG + 8 <= as_errno B /\ as_errno B + 4 <= 2 ^ 64.
Proof. rewrite HEV. unfold TFIB_ERRNO_B. vm_compute. split; discriminate. Qed.
(* HG_SL, GWR, XRF_ROM_OUT, AZS_s: _G.v's lemmas at the exit file's text *)
Lemma bxi_HG_SL : forall a, inG (G_SL B fr_RG) a -> inG (G_fr_c B) a.
Proof. eapply c_HG_SL; eassumption. Qed.
Lemma bxi_GWR : glob_wr_law (G_fr_c B).
Proof. eapply c_glob_wr; try eassumption. Qed.
Lemma bxi_XRF_ROM_OUT : @rom_out YE2k.tfib_sink_head segs B (G_fr_c B).
Proof. eapply c_rom_out; eassumption. Qed.
Lemma bxi_AZS_s : azs B (rg_s fr_RG) (4 * ASRC).
Proof. eapply c_HZS; eassumption. Qed.
End inst.
