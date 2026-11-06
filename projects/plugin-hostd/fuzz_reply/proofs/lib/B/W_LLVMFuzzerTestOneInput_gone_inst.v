(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput on image B:
   THE INSTANCE FACTS of lf_arm_gone (lib/B/W_LLVMFuzzerTestOneInput_gone.v) DECIDED at the real instance.  Each
   gi_* lemma below has exactly the type of one of lf_arm_gone's Section hypotheses, at the entry's G := G_fr_c B
   (lib/B/W_LLVMFuzzerTestOneInput_G.v), for every B with B's start-up instance (YF0m.TfibSyms B) and errno at
   TFIB_ERRNO_B (0x5d994c, _G.v's HEV); the B top holds both (they are _G.v's own Section hypotheses).
     GN_HGs                     gi_HGs           _G.v c_HGs
     GN_HG_RIG                  gi_HG_RIG        _G.v c_HGlock + c_HG_DR (G_RIG = lock :: G_DR)
     GN_HGcells                 gi_HGcells       vm_compute: every gn_cells range inside one range of G_fr_obj
     GN_CELLS_ERRNO             gi_CELLS_ERRNO   vm_compute: every gn_cells range apart from [0x5d994c, +4)
     GN_ERRNO_LOW               gi_ERRNO_LOW     _G.v c_ERRNO_LOW
     GN_ROM_PIN                 gi_ROM_PIN       _G.v c_rom_pinned
     GN_HZS                     gi_HZS           _G.v c_HZS (YF0m Tfib_zero_shadow (0x5d8e60, 0x180))
     HGOTG                      gi_HGOTG         YE22.got_canary_of_AR (the const cell z8 0x9ebd8 0x5f9a30)
     GN_LIT_GES                 gi_LIT_GES       W_shadow_pin.shp_ashp over YF0m's const / zero shadow, vm_compute
                                                 (the same statement as ashp_gesture_14_fr of lib/B/W_shadow_pin_fr.v
                                                 on a working branch d4427280250, not merged here)
     GN_LIT_FMT                 gi_LIT_FMT       the same method at the format .str.9 "%s %d " (A_OBJ 17, 7 bytes) *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YF0m YE22.
(* The sink-instance guard (MERGE.md (sha256 0694aca87ccd; internal record) rule 3): every sink argument is passed with @ or from the Context *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section gi.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
Variable B : asyms.
(* B's start-up instance and errno's place: _G.v's own Section hypotheses TS / HEV *)
Hypothesis TS : YF0m.TfibSyms B.
Hypothesis HEV : as_errno B = TFIB_ERRNO_B.

(* ---- the G-coverage facts at G_fr_c ---- *)
Lemma gi_HGs : GN_HGs (G_fr_c B).
Proof. exact (c_HGs B). Qed.
Lemma gi_HG_RIG : GN_HG_RIG B (G_fr_c B).
Proof.
  intros a Ha. unfold G_RIG in Ha. apply inG_cons in Ha as [Ha | Ha]; [| exact (c_HG_DR B a Ha)].
  apply (c_HGlock B a). unfold in_zr in Ha. cbn [fst snd] in Ha. exact Ha.
Qed.
Lemma gi_HGcells : GN_HGcells (G_fr_c B).
Proof.
  intros a Ha. apply (obj_c B).
  assert (Hb : forallb (fun r => rng_inb (fst r) (snd r) G_fr_obj) gn_cells = true) by (vm_compute; reflexivity).
  unfold inG in Ha. apply Exists_exists in Ha as ([lo n] & Hr & Hz).
  rewrite forallb_forall in Hb. exact (rng_cover_zr lo n G_fr_obj (Hb _ Hr) a Hz).
Qed.
(* ---- errno ---- *)
Lemma gi_CELLS_ERRNO : GN_CELLS_ERRNO B.
Proof.
  intros a Ha He. rewrite HEV in He.
  assert (Hb : forallb (fun r => (fst r + snd r <=? TFIB_ERRNO_B) || (TFIB_ERRNO_B + 4 <=? fst r)) gn_cells = true)
    by (vm_compute; reflexivity).
  unfold inG in Ha. apply Exists_exists in Ha as ([lo n] & Hr & Hz).
  rewrite forallb_forall in Hb. specialize (Hb _ Hr). cbn [fst snd] in Hb. unfold in_zr in Hz. cbn [fst snd] in Hz.
  apply orb_true_iff in Hb as [Hb | Hb]; apply Z.leb_le in Hb; lia.
Qed.
Lemma gi_ERRNO_LOW : GN_ERRNO_LOW B.
Proof. exact (c_ERRNO_LOW B HEV). Qed.
(* ---- the read-only image and g_s's shadow ---- *)
Lemma gi_ROM_PIN : GN_ROM_PIN B.
Proof. exact (c_rom_pinned B TS). Qed.
Lemma gi_HZS : GN_HZS B.
Proof. exact (c_HZS B TS). Qed.
(* ---- snprintf's stack-protector GOT word: the const cell z8 0x9ebd8 0x5f9a30 of B's start-up table ---- *)
Lemma gi_HGOTG : forall ly S W mem md, AR segs B ly S W mem md ->
  rdword (aview segs (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
Proof.
  intros ly S W mem md HAR.
  apply (rdword_of_val_mem segs (w_H W) mem); [exact (YE22.got_canary_of_AR B TS ly S W mem md HAR) |].
  unfold FR_GUARD. lia.
Qed.
(* ---- snprintf's two literals: shp_ashp over B's const shadow cells and zero-shadow ranges ---- *)
Lemma gi_tfib_shp : forall a n,
  shp_check YF0m.Tfib_const_shadow YF0m.Tfib_zero_shadow a n = true -> ashp (PI := PB_fr) B a n.
Proof.
  intros a n H. apply (shp_ashp B YF0m.Tfib_const_shadow YF0m.Tfib_zero_shadow); [| | exact H].
  - intros ly c Hc. rewrite (YF0m.ts_const _ TS ly). unfold YF0m.Tfib_const.
    apply in_or_app. right. apply in_or_app. right. exact Hc.
  - intros r Hr. rewrite (YF0m.ts_zsh _ TS). exact Hr.
Qed.
(* .str.5 "param_gesture\0", A_OBJ 18 = 0x20f20, 14 bytes *)
Lemma gi_LIT_GES : ashp (PI := PB_fr) B (VAL A_lit_gesture) 14.
Proof. apply gi_tfib_shp. vm_compute. reflexivity. Qed.
(* .str.9 "%s %d \0", A_OBJ 17 = 0x20f80, 7 bytes *)
Lemma gi_LIT_FMT : ashp (PI := PB_fr) B (VAL (A_OBJ 17)) 7.
Proof. apply gi_tfib_shp. vm_compute. reflexivity. Qed.
(* the two addresses, on image B's placement *)
Example gi_lit_addrs : VAL A_lit_gesture = 0x20f20 /\ VAL (A_OBJ 17) = 0x20f80.
Proof. vm_compute. split; reflexivity. Qed.
End gi.
