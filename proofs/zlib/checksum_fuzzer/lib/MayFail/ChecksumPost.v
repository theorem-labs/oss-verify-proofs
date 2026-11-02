(** Driver postcondition for the actual fuzzer plus its child CRC frames.
    This memory bridge does not prove the intervening fuzzer execution. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI5b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI5c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import ZImage.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import ZFuzzerBounds.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Frame.
Module CF := OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Frame.
Section Pure.
Context {fx : FPState} {rc : RunCeil}.
Variable API : AllocAPI src0_msyms.
Let MR := aa_MR API.
Lemma checksum192_frame_raw : forall regs mem mem' a,
  CF.munch [(spZ regs-192,spZ regs)] mem mem' ->
  0 <= a < 2^64 ->
  (a < spZ regs - 192 \/ spZ regs <= a) ->
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
  intros regs mem mem' a HF Ha Hout. apply HF.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 a) with (a mod 2^64).
  rewrite Z.mod_small by lia. cbn [CF.outside]. split; [lia|exact I].
Qed.
Lemma checksum192_frame_low : forall regs mem mem' a,
  alloc_ceiling + LIB_STACK <= spZ regs ->
  CF.munch [(spZ regs-192,spZ regs)] mem mem' ->
  0 <= a < alloc_ceiling -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
  intros regs mem mem' a Hsp HF Ha. apply (checksum192_frame_raw regs); [exact HF| |left];
    unfold LIB_STACK in *; pose proof alloc_ceiling_lt; lia.
Qed.
Lemma checksum192_mbyte : forall regs mem mem' a,
  alloc_ceiling + LIB_STACK <= spZ regs ->
  CF.munch [(spZ regs-192,spZ regs)] mem mem' ->
  0 <= a < alloc_ceiling -> mbyte zsegs mem' a = mbyte zsegs mem a.
Proof.
  intros regs mem mem' a Hsp HF Ha. unfold mbyte.
  rewrite (checksum192_frame_low regs mem mem' a Hsp HF Ha). reflexivity.
Qed.
Lemma checksum192_writable_eq : forall mem mem' a,
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) ->
  (writable_at zsegs mem' a <-> writable_at zsegs mem a).
Proof. intros mem mem' a H. unfold writable_at, wview. rewrite H. reflexivity. Qed.
Lemma checksum192_MR : forall L A regs mem mem' md,
  MR L A mem md -> alloc_ceiling + LIB_STACK <= spZ regs ->
  CF.munch [(spZ regs-192,spZ regs)] mem mem' -> MR L A mem' md.
Proof.
  intros L A regs mem mem' md HM Hsp HF.
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as [Hh [Hl Hmat]].
  eapply (mr_frame _ _ (aa_laws API)); [exact HM| | | |reflexivity|exact Hh|exact Hl|exact Hmat].
  - intros a Ha. apply (checksum192_mbyte regs); [exact Hsp|exact HF|].
    eapply mr_owned_low; eassumption || apply aa_laws.
  - intros a Ha [b Hb]. exists b. rewrite (checksum192_frame_low regs mem mem'); [exact Hb|exact Hsp|exact HF|].
    eapply mr_owned_low; eassumption || apply aa_laws.
  - intros p n i Hin Hi.
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hin Hi) as [[b Hb] [Hp [Hn Howned]]].
    exists b. rewrite (checksum192_frame_low regs mem mem'); [exact Hb|exact Hsp|exact HF|]. lia.
Qed.
Lemma checksum192_block_bytes : forall L A regs mem mem' md p n i,
  MR L A mem md -> alloc_ceiling + LIB_STACK <= spZ regs ->
  CF.munch [(spZ regs-192,spZ regs)] mem mem' ->
  In (p,n) (user_blocks A) -> 0 <= i < n ->
  mbyte zsegs mem' (ptr_addr L p+i) = mbyte zsegs mem (ptr_addr L p+i).
Proof.
  intros L A regs mem mem' md p n i HM Hsp HF Hin Hi.
  destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hin Hi) as [Hpresent [Hp [Hn Howned]]].
  apply (checksum192_mbyte regs); [exact Hsp|exact HF|lia].
Qed.
Lemma checksum192_checksum_post : forall L A regs mem md p n pl b regs' mem',
  lib_pre_x src0_msyms API LIB_STACK EMPTY L A regs mem md RA_LIB p n pl b ->
  getr regs' (Z_to_bv 5 10) = Z_to_bv 64 0 ->
  regs_preserved regs regs' ->
  CF.munch [(spZ regs-192,spZ regs)] mem mem' ->
  (forall a, lib_scratch src0_msyms LIB_STACK regs a -> writable_at zsegs mem' a) ->
  lib_post_x src0_msyms API LIB_STACK L A regs mem md p n b
    (LL 0 (m_fs md) []) L A regs' mem' md.
Proof.
  intros L A regs mem md p n pl b regs' mem' HP Hr Hregs HF HWnew.
  destruct HP as [HP [Hlen [HD [Hres [Hroom [HSink [Hfd [Hsorted Hsp47]]]]]]]].
  destruct HP as [HM [HW [HB [Hid [Hra [Hal [Hsp [HspHi [HWstack [Htp [HWerrno
    [Hptr [Hsize [Hlive Hro]]]]]]]]]]]]]].
  unfold lib_post_x. cbn [ll_ret ll_fs ll_out].
  split; [eapply checksum192_MR; eassumption|].
  split; [exact HW|]. split; [exact HB|]. split; [exact Hid|].
  split; [exact Hr|]. split; [exact Hregs|].
  split.
  { exists (m_vmmaps md), (m_fds md), (m_statpins md).
    split; [apply os_upd_self|]. intros k. reflexivity. }
  split.
  { intros q k Hin. exists q. auto. }
  split.
  { intros a Ha Hnot.
    assert (Hout : a < spZ regs - 192 \/ spZ regs <= a).
    { destruct (Z_lt_le_dec a (spZ regs-192)); [auto|]. right.
      destruct (Z_le_gt_dec (spZ regs) a); [assumption|]. exfalso. apply Hnot.
      unfold lib_scratch. left. unfold LIB_STACK in *. lia. }
    assert (HR : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a))
      by (eapply (checksum192_frame_raw regs); eassumption || (pose proof alloc_ceiling_val; lia)).
    split; [unfold mbyte; rewrite HR; reflexivity|].
    apply iff_sym; apply checksum192_writable_eq. exact HR. }
  split.
  { intros a Himg Hstatic Hctx Herr.
    pose proof (so_img_hi _ src0_syms_ok a Himg) as Ha.
    split; [eapply (checksum192_mbyte regs); eassumption|]. apply iff_sym; apply checksum192_writable_eq.
    eapply (checksum192_frame_low regs); eassumption. }
  split.
  { intros q k i Hin Hneq Hi. eapply checksum192_block_bytes; eassumption. }
  split; [exact HWnew|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hsorted|]. split.
  { eapply sink_none_frame; [|exact HSink]. intros a Ha.
    pose proof (src0_env_addr_range a Ha) as Har.
    apply (checksum192_mbyte regs); [exact Hsp|exact HF|]. pose proof alloc_ceiling_val. lia. }
  split.
  { change (res_ok A b). exact Hres. }
  intros i Hi. destruct Hlive as [[-> Hempty]|[Hpos [q [Hin Hq]]]].
  - lia.
  - rewrite <- Hq. eapply checksum192_block_bytes; eassumption.
Qed.

End Pure.
