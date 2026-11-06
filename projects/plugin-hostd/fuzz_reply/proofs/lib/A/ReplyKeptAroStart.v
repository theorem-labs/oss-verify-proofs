(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31, QMm W1 entry (a Theorem Labs lane; owner a Theorem Labs lane / ReallocPrimary): arodata_ok_cf (Reusable/YG0dcf.v)
   at the cf driver's first state, main's hand-off, whose memory is the FULL start-up memory. The cf driver
   (A/AD1pcf.v) took it as the Section hypothesis HSTART_ARO; arodata_ho_A states it in the shape of
   A/ReplyStartWitA.v start_cells_ho_t / start_pf_ho_t (same binders, same premises).
   - kept_none_ho_A: at every hand-off state of AB01.v with cs_ok, FULL holds NO byte at any address of the image's
     kept ranges as_kept TfibB (AF0m.Tfib_kept: the RELRO [cf_relro_lo, cf_relro_hi) and the five read-only read
     ranges), owned or not. Route, as A/ReplyImg_su_errb.v errb_obj_zero_start: every hand-off state carries a KImg
     over each kept range (kept_img_all, one vm_compute), and cs_ok's co_know (YA0j.v ho_know) reads a KImg as "the
     read memory Mr = mrestrict hid FULL holds no byte there" (YK0e.v kentry_ok); hid is false at those addresses,
     since they lie in the image hull (YA0e.v vis) and below TOP, where argH is false (YA02.v argH0_high, top_ok0).
   - arodata_ho_A: ReplyKeptAroA.arodata_none_A, at an address that relro_kept_A puts in as_kept.
   rule 24: proves no function (kind: start-up facts). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB12 AB1h AB13 AB01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AD2l CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyKeptAroA.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.

(* Every kept range lies in the image hull [img_lo TFIB, img_hi TFIB), and the hull lies below the stack ceiling. *)
Definition kept_hull_ok (G : list (Z * Z)) : bool :=
  (0 <=? img_lo TFIB) && (img_hi TFIB <=? APC.CEIL) &&
  forallb (fun r => (img_lo TFIB <=? fst r) && (fst r + snd r <=? img_hi TFIB)) G.
Lemma kept_hull_A : kept_hull_ok Tfib_kept = true.
Proof. vm_compute. reflexivity. Qed.

(* Every hand-off state carries a KImg over each kept range. *)
Definition kept_img_ok (ch : acs) : bool := forallb (fun r => kn_img ch (fst r) (snd r)) Tfib_kept.
Lemma kept_img_all : forallb kept_img_ok HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The start-up fact, at an arbitrary kept address: the hand-off memory FULL holds no byte there. *)
Lemma kept_none_ho_A : forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs)
  (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
  valid_sp sp -> valid_argv (in_argv inp) -> HS_tfib h = Some ch ->
  cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
    (YA02.SINV0 TSEGS TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
  forall a, Exists (in_zr a) (as_kept TfibB) -> FULL (Z_to_bv 64 a) = None.
Proof.
intros sp rdraw brk inp h ch E R FULL model Hsp Hva Hch HC a Ha.
rewrite (@ts_kept TfibB TfibB_syms) in Ha.
apply Exists_exists in Ha as ([s n] & Hr & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
(* the kept range lies in the image hull, below TOP *)
pose proof kept_hull_A as HB. unfold kept_hull_ok in HB.
apply andb_prop in HB as [HB HG]. apply andb_prop in HB as [HB0 HB1].
apply Z.leb_le in HB0. apply Z.leb_le in HB1.
rewrite forallb_forall in HG. specialize (HG _ Hr). cbn [fst snd] in HG.
apply andb_prop in HG as [HG0 HG1]. apply Z.leb_le in HG0. apply Z.leb_le in HG1.
pose proof (YA02.top_ok0 sp Hsp) as T. unfold top_ok in T. destruct T as [T _]. unfold APC.CEIL in T.
unfold APC.CEIL in HB1.
assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
(* a KImg of ch covers the kept range, so the read memory holds no byte at a *)
pose proof (proj1 (forallb_forall _ _) kept_img_all ch (HS_tfib_In h ch Hch)) as K. unfold kept_img_ok in K.
rewrite forallb_forall in K. specialize (K _ Hr). cbn [fst snd] in K.
unfold kn_img in K. apply existsb_exists in K as (Kn & HK & HKb).
destruct Kn as [| | |lo hi| | | | | |]; try discriminate HKb.
apply andb_prop in HKb as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
pose proof (proj1 (Forall_forall _ _)
  (ho_know TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
     (YA02.SINV0 TSEGS TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
     (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model HC)
  _ HK) as (_ & _ & Hnone).
specialize (Hnone a ltac:(lia)).
(* the hand-off hides nothing at a: argH lies at or above TOP, and a is in the image hull *)
assert (HA : YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E (Z_to_bv 64 a) = false).
{ destruct (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E (Z_to_bv 64 a)) eqn:EA;
    [|reflexivity].
  pose proof (YA02.argH0_high TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) Hsp Hva E _ EA) as X.
  rewrite (u64_lit a Ha64) in X. lia. }
assert (HH : hid TFIB (YA02.TOP sp) (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
               E ch model (Z_to_bv 64 a) = false).
{ unfold hid. rewrite HA. cbn [orb]. unfold vis. cbv zeta. rewrite (u64_lit a Ha64). unfold in_hull.
  rewrite (proj2 (Z.leb_le (img_lo TFIB) a)) by lia. rewrite (proj2 (Z.ltb_lt a (img_hi TFIB))) by lia.
  reflexivity. }
unfold Mr, mrestrict in Hnone. rewrite HH in Hnone. exact Hnone.
Qed.

Theorem arodata_ho_A : forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (ch : acs)
  (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
  valid_sp sp -> valid_argv (in_argv inp) -> HS_tfib h = Some ch ->
  cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
    (YA02.SINV0 TSEGS TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
  @arodata_ok_cf CfImg_A TSEGS TfibB FULL.
Proof.
intros sp rdraw brk inp h ch E R FULL model Hsp Hva Hch HC.
apply (ReplyKeptAroA.arodata_none_A FULL). intros a Ha Hno.
apply (kept_none_ho_A sp rdraw brk inp h ch E R FULL model Hsp Hva Hch HC a).
destruct (ReplyKeptAroA.aro_kept_A a Ha Hno) as (_ & _ & Hk & _). exact Hk.
Qed.

End s.

Check arodata_ho_A.
Print Assumptions arodata_ho_A.
