(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30, QMm W1 (a Theorem Labs lane; owner a Theorem Labs lane / ReallocPrimary): image A's side of the kept-bytes
   carry. QMm W0' gave YCbqG.ARx_frame_law a premise that the image's KEPT bytes (YCbqG.kept_x, the non-owned
   as_kept ranges) are unchanged, and YGcallcf.AR_laws_x_and_mem turns any memory predicate those bytes decide into
   a conjunct a relation may carry. This file supplies, for image A (TfibB of lib/A/AD2l.v, CfImg_A of
   lib/A/CfImgA.v):
   - relro_kept_A: every non-owned byte of [cf_relro_lo, cf_relro_hi) = [0x9d438, 0x9f000) is a kept byte and lies
     in 64 bits. AF0m.Tfib_kept's FIRST range is that interval, so the as_kept half is one Exists_cons_hd, and
     in_img is W_LLVMFuzzerTestOneInput_G.segin_ok by vm_compute over the segment list.
   - arodata_kept_A: arodata_ok_cf survives a step that keeps the kept bytes (YGcallcf.arodata_kept at the A fact).
     This is the hypothesis AR_laws_x_and_mem takes, so `ARX := ARcf .. /\ Hp = [] /\ arodata_ok_cf segs TfibB mem`
     keeps every law of AR_laws_x.
   - arodata_none_A: arodata_ok_cf holds of any memory whose OVERLAY holds no byte at a non-owned RELRO address.
     This is the driver's ENTRY form (a Theorem Labs lane 23:18Z): the loader's overlay holds bytes only at or above
     sp - stack_max_size (YAkMemnorm.memnorm_wrap_mem's support step), which is far above the image, so the start
     state meets it and ARX holds there.
   rule 24: proves no function (kind: invariant lemma). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m AD2l CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_G.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := AB1v.tfibsegs.

(* QMm W1 / part 3c: every non-owned byte of ANY of the image's kept ranges is a kept byte, and lies in 64 bits.
   Stated over the whole of as_kept, not only RELRO, so part 3c's widening of arodata_ok_cf's address side from
   [cf_relro_lo, cf_relro_hi) to aro_addr_cf (that interval OR a cf_ro_reads range) needs no new computation here:
   AF0m.Tfib_kept already holds the five read ranges, and the one rng_all_in below ranges over all six. *)
Lemma kept_mem_A : forall a, Exists (in_zr a) (as_kept TfibB) ->
  ~ Exists (in_zr a) (as_owned_static TfibB) -> 0 <= a < 2 ^ 64 /\ kept_x segs TfibB a.
Proof.
intros a Hk Hno.
assert (Himg : W_LLVMFuzzerTestOneInput_G.segin segs a = true).
{ apply (W_LLVMFuzzerTestOneInput_G.rng_all_in (W_LLVMFuzzerTestOneInput_G.segin segs)
           Tfib_kept a ltac:(vm_compute; reflexivity)). exact Hk. }
assert (Hb : 0 <= a < 2 ^ 64).
{ unfold as_kept, TfibB, Tfib_kept in Hk. repeat (apply Exists_cons in Hk as [Hz|Hk];
    [unfold in_zr in Hz; cbn [fst snd] in Hz; lia|]). inversion Hk. }
split; [exact Hb|]. split; [exact (W_LLVMFuzzerTestOneInput_G.segin_ok segs a Himg)|].
split; [exact Hk | exact Hno].
Qed.
(* part 3c: the address side of arodata_ok_cf is aro_addr_cf, the RELRO interval OR one of the image's five
   read-only read ranges. Both are entries of AF0m.Tfib_kept, so both go through kept_mem_A and nothing is
   recomputed: RELRO is its head, the five are its tail and are CfImg_A's cf_ro_reads word for word. *)
Lemma aro_kept_A : forall a, @aro_addr_cf CfImg_A a ->
  ~ Exists (in_zr a) (as_owned_static TfibB) -> 0 <= a < 2 ^ 64 /\ kept_x segs TfibB a.
Proof.
intros a Ha Hno. apply kept_mem_A; [| exact Hno].
unfold as_kept, TfibB, Tfib_kept. destruct Ha as [Hr | Hro].
- cbn [cf_relro_lo cf_relro_hi CfImg_A] in Hr. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl. cbn [cf_ro_reads CfImg_A] in Hro. exact Hro.
Qed.
(* the RELRO case alone, kept for the callers that name the interval *)
Lemma relro_kept_A : forall a, @cf_relro_lo CfImg_A <= a < @cf_relro_hi CfImg_A ->
  ~ Exists (in_zr a) (as_owned_static TfibB) -> 0 <= a < 2 ^ 64 /\ kept_x segs TfibB a.
Proof. intros a Ha Hno. exact (aro_kept_A a (or_introl Ha) Hno). Qed.

(* arodata_ok_cf is kept by a step that keeps the kept bytes: the hypothesis AR_laws_x_and_mem takes *)
Lemma arodata_kept_A : forall mem mem', @arodata_ok_cf CfImg_A segs TfibB mem ->
  (forall a, 0 <= a < 2 ^ 64 -> kept_x segs TfibB a -> mem' (w64 a) = mem (w64 a)) ->
  @arodata_ok_cf CfImg_A segs TfibB mem'.
Proof. exact (@arodata_kept CfImg_A segs TfibB aro_kept_A). Qed.

(* the ENTRY form: an overlay with no byte at a non-owned aro_addr_cf address meets arodata_ok_cf *)
Lemma arodata_none_A : forall mem,
  (forall a, @aro_addr_cf CfImg_A a -> ~ Exists (in_zr a) (as_owned_static TfibB) ->
     mem (Z_to_bv 64 a) = None) ->
  @arodata_ok_cf CfImg_A segs TfibB mem.
Proof.
intros mem HN a b Hm Ha Hno. rewrite (HN a Ha Hno) in Hm. discriminate Hm.
Qed.

End a.
