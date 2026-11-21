(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revision's launch (CONFIG_RSEQ-sized auxv, execfn, group id, launch premises); the input-owned, top-anchored launch stack; the start-up certificate per CONFIG_RSEQ flag with states computed in the build); internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-10-31, QMm W1 entry, image B (asan-ubsan) twin of lib/A/ReplyKeptAroStart.v (a Theorem Labs lane,
   a working branch), by a Theorem Labs lane: the same text with image B's modules (YB01's HS_tfib_list,
   YF0m.Tfib_kept, CfImg_B, ReplyKeptAroB). arodata_ok_cf (Reusable/YG0dcf.v) at the cf driver's first state, main's
   hand-off, whose memory is the FULL start-up memory.
   - kept_none_ho_B: at every hand-off state of YB01.v with cs_ok, FULL holds NO byte at any address of the image's
     kept ranges as_kept TfibB (YF0m.Tfib_kept), owned or not: every hand-off state carries a KImg over each kept
     range (kept_img_all, one vm_compute), cs_ok's co_know (YA0j.v ho_know) reads a KImg as "the read memory holds no
     byte there", and hid is false there (image hull, below TOP).
   - arodata_ho_B: ReplyKeptAroB.arodata_none_B, at an address that aro_kept_B puts in as_kept.
   rule 24: proves no function (kind: start-up facts). 
   LPS 727298f3: both facts are stated over the start of B/YD1q.v's drv_mainX_stmt, as lib/A/ReplyKeptAroStart.v
   (B/YB01r.v's hand-off state of the run's own CONFIG_RSEQ flag, the invariant abstract with SINV_sp0, the mmap base
   and the launch premises), and the KImg check runs over both flags' hand-off states. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB12 YB1h YB13 YB01r.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YD2l CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyKeptAroB.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.

(* Every kept range lies in the image hull [img_lo TFIB, img_hi TFIB), and the hull lies below the stack ceiling. *)
Definition kept_hull_ok (G : list (Z * Z)) : bool :=
  (0 <=? img_lo TFIB) && (img_hi TFIB <=? APC.CEIL) &&
  forallb (fun r => (img_lo TFIB <=? fst r) && (fst r + snd r <=? img_hi TFIB)) G.
Lemma kept_hull_B : kept_hull_ok Tfib_kept = true.
Proof. vm_compute. reflexivity. Qed.

(* Every hand-off state of both CONFIG_RSEQ flags carries a KImg over each kept range. *)
Definition kept_img_ok (ch : acs) : bool := forallb (fun r => kn_img ch (fst r) (snd r)) Tfib_kept.
Lemma kept_img_all : forallb kept_img_ok HS_tfib_list_all = true.
Proof. vm_compute. reflexivity. Qed.

#[local] Notation ARGH sp rdraw inp := (YA02.argH0 sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp)
  (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp)
  (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)).

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The start-up fact, at an arbitrary kept address: the hand-off memory FULL holds no byte there. *)
Lemma kept_none_ho_B : forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs)
  (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop),
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
  (forall E' M, SINV E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608) ->
  cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp) SINV (ARGH sp rdraw inp) (in_fs inp) E ch R FULL model ->
  forall a, Exists (in_zr a) (as_kept TfibB) -> FULL (Z_to_bv 64 a) = None.
Proof.
intros sp rdraw brk mbase inp h ch E R FULL model SINV Hsp Hva Hve Hfit Hinp Hlau Hch SP0 HC a Ha.
rewrite (@ts_kept TfibB TfibB_syms) in Ha.
apply Exists_exists in Ha as ([s n] & Hr & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
(* the kept range lies in the image hull, below TOP *)
pose proof kept_hull_B as HB. unfold kept_hull_ok in HB.
apply andb_prop in HB as [HB HG]. apply andb_prop in HB as [HB0 HB1].
apply Z.leb_le in HB0. apply Z.leb_le in HB1.
rewrite forallb_forall in HG. specialize (HG _ Hr). cbn [fst snd] in HG.
apply andb_prop in HG as [HG0 HG1]. apply Z.leb_le in HG0. apply Z.leb_le in HG1.
pose proof (YA02.top_ok0 sp Hsp) as T. unfold top_ok in T. destruct T as [T _]. unfold APC.CEIL in T.
unfold APC.CEIL in HB1.
assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
(* a KImg of ch covers the kept range, so the read memory holds no byte at a *)
pose proof (proj1 (forallb_forall _ _) kept_img_all ch (HS_tfib_r_In _ h ch Hch)) as K. unfold kept_img_ok in K.
rewrite forallb_forall in K. specialize (K _ Hr). cbn [fst snd] in K.
unfold kn_img in K. apply existsb_exists in K as (Kn & HK & HKb).
destruct Kn as [| | |lo hi| | | | | |]; try discriminate HKb.
apply andb_prop in HKb as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
pose proof (proj1 (Forall_forall _ _)
  (ho_know TSEGS TFIB YA02.LIMIT (YA02.TOP sp) SINV (ARGH sp rdraw inp) (in_fs inp) E ch R FULL model HC)
  _ HK) as (_ & _ & Hnone).
specialize (Hnone a ltac:(lia)).
(* the hand-off hides nothing at a: argH lies at or above TOP, and a is in the image hull *)
assert (HA : ARGH sp rdraw inp E (Z_to_bv 64 a) = false).
{ destruct (ARGH sp rdraw inp E (Z_to_bv 64 a)) eqn:EA; [|reflexivity].
  assert (X : YA02.TOP sp <= bv_unsigned (Z_to_bv 64 a)).
  { unshelve eapply (YA02.argH0_high sp rdraw (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp)
      (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp)
      (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp));
      try exact EA; try exact Hva; try exact Hsp; try exact 0%N. }
  rewrite (u64_lit a Ha64) in X. lia. }
assert (HH : hid TFIB (YA02.TOP sp) (ARGH sp rdraw inp) E ch model (Z_to_bv 64 a) = false).
{ unfold hid. rewrite HA. cbn [orb]. unfold vis. cbv zeta. rewrite (u64_lit a Ha64). unfold in_hull.
  rewrite (proj2 (Z.leb_le (img_lo TFIB) a)) by lia. rewrite (proj2 (Z.ltb_lt a (img_hi TFIB))) by lia.
  reflexivity. }
unfold Mr, mrestrict in Hnone. rewrite HH in Hnone. exact Hnone.
Qed.

(* A/AD1pcf.v start_aro_ho_t at CfImg_B / TfibB, its binders and premises *)
Theorem arodata_ho_B : forall (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput) (h : nat) (ch : acs)
  (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) (SINV : env -> (word -> option byte) -> Prop),
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
  HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch ->
  (forall E' M, SINV E' M -> uE E' e_sp0 = YA02.TOP sp + 8388608) ->
  cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp) SINV (ARGH sp rdraw inp) (in_fs inp) E ch R FULL model ->
  @arodata_ok_cf CfImg_B TSEGS TfibB FULL.
Proof.
intros sp rdraw brk mbase inp h ch E R FULL model SINV Hsp Hva Hve Hfit Hinp Hlau Hch SP0 HC.
apply (ReplyKeptAroB.arodata_none_B FULL). intros a Ha Hno.
apply (kept_none_ho_B sp rdraw brk mbase inp h ch E R FULL model SINV Hsp Hva Hve Hfit Hinp Hlau Hch SP0 HC a).
destruct (ReplyKeptAroB.aro_kept_B a Ha Hno) as (_ & _ & Hk & _). exact Hk.
Qed.

End s.
