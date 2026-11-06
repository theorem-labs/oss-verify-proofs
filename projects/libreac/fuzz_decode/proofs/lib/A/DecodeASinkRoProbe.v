(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: a probe for lib/A/DecodeClose.v (a working branch
   45061c42804) row HB_SINK_KEPT (DecodeClose.v:334-337), at image A's instance: segs = decodesegs0, B = GrantB
   (lib/A/AD2l.v), asink_none = Reusable/YE00.v:126 asink_none, KS = lib/A/AE2k.v:44 tfib_K (the sink names
   lib/A/ACfn.v:46 / :59 fixes for the driver).
   proves no function (kind: probe): it shows that HB_SINK_KEPT, as stated, is FALSE at every entry state of a call.
   The statement asks asink_none to survive EVERY journal step, with no `~ YI16.sink_open_fp FP` premise. For the
   sink-opening footprint FP = [YI16.sink_token], aos_step (Reusable/YCbq.v:37-42) lets the model's fd table gain an
   `FdFileW sink_path` entry (Reusable/YI16.v:51 fds_rel), and AR (Reusable/YG0n.v:490) does not read the fd table;
   so from any afn_pre state (Reusable/YCbq.v:336) with asink_none and one free fd, the step that only adds that fd is
   a journal step (Reusable/YCbq.v:350-372), after which asink_none's last conjunct (YE00.v:128) fails. Every entry of
   LLVMFuzzerTestOneInput has such a state: lib/A/Prog/LLVMFuzzerTestOneInput_cg.v:105-120 dec_lib_pre_x carries
   afn_pre (:107), asink_none (:115) and the free fd alloc_fd (:116). The Theorem Labs lane lemma that keeps asink_none,
   Reusable/YE01.v:85 asink_none_kept, takes `~ YI16.sink_open_fp FP` (:87); so does a Theorem Labs lane's SinkInert
   (a working branch add754d0ac8, lib/Reusable/SinkInert.v:52 asink_none_os_kept). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YM05 YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YE00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require AE2k AD2l.
Import ListNotations.
Open Scope Z_scope.

Module YI16 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI16.
Module YE00 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YE00.
Module AE2k := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.AE2k.
Module AD2l := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.AD2l.

(* Image A's instance of DecodeClose.v's Section variables (segs, B, asink_none, KS). *)
Local Abbreviation segs := decodesegs0.
Local Abbreviation B := AD2l.GrantB.
Local Abbreviation asink_none := YE00.asink_none.
Local Abbreviation KS := AE2k.tfib_K.

(* DecodeClose.v:334-337 HB_SINK_KEPT, verbatim, at the instance above. *)
Definition HB_SINK_KEPT_stmt : Prop :=
  forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
    @ajournal rc dec_A_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    asink_none segs KS (mrestrict (w_H W0) mem0) md0 -> asink_none segs KS (mrestrict (w_H W') mem') md'.

(* The model after a step that only adds the descriptor fd, open for writing on the sink's path. *)
Definition sink_fd_model (fd : word) (md : Model) : Model :=
  YI16.os_upd (m_vmmaps md) ((fd, FdFileW YI16.sink_path (Z_to_bv 64 0)) :: m_fds md) (m_fs md) (m_statpins md) md.

Lemma sink_fd_proc : forall fd md, proc_but_pins md (sink_fd_model fd md).
Proof. intros fd [[t p] [v l z] io [fs] [h ti c ss sm ch u sa k sp at_ pins] li tm]. reflexivity. Qed.

(* aos_step at the sink-opening footprint [YI16.sink_token] allows that step (YCbq.v:37-42, YI16.v:51). *)
Lemma sink_fd_aos : forall fd md, fd_lookup (m_fds md) fd = None ->
  aos_step [YI16.sink_token] md (sink_fd_model fd md).
Proof.
intros fd md Hfree. unfold aos_step.
split; [reflexivity|]. split; [reflexivity|].
split.
{ unfold YI16.fds_rel. intros fd0. unfold sink_fd_model. rewrite YI16.os_upd_fds. cbn [fd_lookup].
  destruct (bv_eqb fd fd0) eqn:E.
  - right. apply bv_eqb_eq in E. subst fd0. rewrite Hfree.
    split; [left; reflexivity | right; exists (Z_to_bv 64 0); reflexivity].
  - left. reflexivity. }
split; [unfold YI16.fs_rel; intros p _; reflexivity|].
split; [intros H; exact H|].
split; [apply sink_fd_proc|].
intros Hc. exfalso. apply Hc. apply YI16.sink_open_token. left. reflexivity.
Qed.

(* AR does not read the fd table (YG0n.v:490-491: ALedger and amwf read the VM state only). *)
Lemma sink_fd_AR : forall (rc : YM05.RunCeil) fd ly S W mem md,
  AR (rc := rc) segs B ly S W mem md -> AR (rc := rc) segs B ly S W mem (sink_fd_model fd md).
Proof.
intros rc fd ly S W mem md (M & L & B0 & MW & HS).
assert (Hvm : m_vmmaps (sink_fd_model fd md) = m_vmmaps md) by reflexivity.
assert (Hlz : m_vm_lazy (sink_fd_model fd md) = m_vm_lazy md) by reflexivity.
refine (conj M (conj _ (conj B0 (conj _ HS)))).
- eapply ALedger_same; [exact L | exact Hvm | exact Hlz |]. unfold eager_used. rewrite Hvm, Hlz. reflexivity.
- eapply amwf_same; [exact Hvm | exact Hlz | exact MW].
Qed.

(* The refutation: from any afn_pre state with asink_none and a free descriptor, HB_SINK_KEPT gives False. *)
Lemma HB_SINK_KEPT_false : forall (rc : YM05.RunCeil) STK ly S W regs mem md ch (fd : word),
  @afn_pre rc segs B STK ly S W regs mem md ch ->
  asink_none segs KS (mrestrict (w_H W) mem) md ->
  fd_lookup (m_fds md) fd = None ->
  ~ HB_SINK_KEPT_stmt.
Proof.
intros rc STK ly S W regs mem md ch fd Hpre Hsink Hfree HK.
destruct Hpre as (HAR & _ & _ & _ & _ & Hstk & Hpres & _ & Hq).
assert (HJ : @ajournal rc dec_A_sink_head segs B STK (spZ regs) [YI16.sink_token] ly S W mem md []
  ly S W mem (sink_fd_model fd md) 0).
{ unfold ajournal.
  split; [exact (sink_fd_AR rc fd ly S W mem md HAR)|].
  split; [apply layout_le_refl|].
  split; [apply Nat.le_refl|].
  split; [apply wle_refl|].
  split; [exact (sink_fd_aos fd md Hfree)|].
  split; [reflexivity|].
  split; [lia|].
  split; [lia|].
  split; [intros; reflexivity|].
  split; [intros; reflexivity|].
  split; [intros; reflexivity|].
  split; [intros; reflexivity|].
  split; [intros p n i H1 H2 _; exfalso; exact (H2 H1)|].
  split; [exact Hpres|].
  split; [exact Hstk|].
  split; [intros; reflexivity|].
  exact Hq. }
pose proof (HK rc STK (spZ regs) [YI16.sink_token] ly S W mem md [] ly S W mem (sink_fd_model fd md) 0 HJ Hsink)
  as (_ & _ & Hn).
unfold sink_fd_model in Hn. rewrite YI16.os_upd_fds in Hn. cbn [Namei.fd_names_path] in Hn.
apply Bool.orb_false_iff in Hn as [Hp _]. vm_compute in Hp. discriminate Hp.
Qed.

Print Assumptions HB_SINK_KEPT_false.
