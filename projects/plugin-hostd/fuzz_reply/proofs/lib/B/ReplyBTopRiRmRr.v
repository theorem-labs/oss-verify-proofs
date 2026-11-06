(* proves no function (kind: invariant lemma -- a projection of the B run invariant fr_RINV, not a whole function).
   btri_RI_rm_rr_pair: the remove arm's model rule RI_rm_rr_pair at RINV := ReplyRINVB.fr_RINV (image B), stated as
   the Context RI_rm_rr_pair of lib/B/ReplyBTop.v:171, binder for binder, so that it closes ReplyBTop.v:369's
   `exact (RI_rm_rr_pair rc fx)` as `exact (btri_RI_rm_rr_pair rc fx)`.
   Image-A twin: lib/A/ReplyTopXRI.v:301 topx_RI_rm_rr_pair, by lib/A/ReplyRINV_a12.v:137 RI_rm_rr_pair_holds.
   Proof: lib/B/ReplyRINVB_rm_a12.v:796 fr_rm_pair (the B relocation of that A proof's argument: the relay entry j0
   that has slot si's fd is fr_relay's pair of slot si's source h) gives fr_pair_ok m t (rm_ent m j0) (h, si), and
   fr_pair_ok's relay / splitter clause (lib/B/ReplyRINVB.v:148, from lib/Prog/SlotInv.v:258) at re_eof = 0 is the
   conclusion. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
W_LLVMFuzzerTestOneInput_remove ReplyRINVB ReplyRINVB_rm_a12.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma btri_RI_rm_rr_pair : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  forall (cx : @lfcx rc) (t : Z) (m : lmod) (si : nat) (h : hsrc) (j0 : nat),
  @ReplyRINVB.fr_RINV rc cx t m -> @W_LLVMFuzzerTestOneInput_remove.rm_at rc cx m si h j0 ->
  re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 ->
  re_skip (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = hs_overlong h /\
  (re_skip (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 ->
   bzs (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) = bzs (hs_W h)).
Proof.
  intros rc fx cx t m si h j0 HRI Hat Heof.
  destruct (ReplyRINVB_rm_a12.fr_rm_pair cx t m si h j0 HRI Hat) as ((_ & _ & _ & Hpr & _) & _).
  exact (Hpr Heof).
Qed.
