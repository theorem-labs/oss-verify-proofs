(* pcap_source_next (0x8181c) on the ASan build of libreac v1.9.0: helpers of the fit-A phase
   (PcapSourceNextFitA.v) and of its __asan_memmove call (PcapSourceNextFitACall.v), kept here so both
   Require them: the memmove contract inside the caller's journal (overlapping ranges), and facts on
   the caller's bytes kept across a call. *)
(* Modified by Theorem Labs, 2026-10: aj_memmove_atS (Section mm) MOVED unchanged to the image-free
   PcapSourceNextFitAShared.v, which lib/B/Prog/PcapSourceNextFitA.v Requires instead of its own copy; this file
   Require Exports it, so PcapSourceNextFitA.v and PcapSourceNextFitACall.v see the same names. fa_ra_kept (a copy
   of lib/A/Prog/PcapSourceCloseSpec.v's ra_frame) deleted; its uses name that ra_frame. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Rt Require Import MemmoveDef.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextFitAModel.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Export PcapSourceNextFitAShared.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import YC4b YC81 YC1g YC1h YC85 YC88 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSourceMeta.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The caller's bytes across a call                                                                 *)
(* ---------------------------------------------------------------------------------------------- *)

Section k. Context {rc : YM05.RunCeil}.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

Lemma fa_garr8_present : forall (H : word -> bool) (m : word -> option byte) p n,
  0 <= n -> (forall i, 0 <= i < n -> apresent H m (p + i)) ->
  exists l, garr8 SEGS (mrestrict H m) p l /\ Z.of_nat (length l) = n /\
    (forall i, (i < length l)%nat -> aview SEGS H m (p + Z.of_nat i) = Some (nth i l 0)).
Proof.
  intros H m p n Hn Hp.
  set (f := fun i : nat => match aview SEGS H m (p + Z.of_nat i) with Some v => v | None => 0 end).
  exists (map f (seq 0 (Z.to_nat n))).
  assert (Hl : length (map f (seq 0 (Z.to_nat n))) = Z.to_nat n) by (rewrite length_map, length_seq; reflexivity).
  assert (Hv : forall i, (i < Z.to_nat n)%nat -> aview SEGS H m (p + Z.of_nat i) = Some (nth i (map f (seq 0 (Z.to_nat n))) 0)).
  { intros i Hi. rewrite (nth_indep _ _ (f 0%nat)) by (rewrite Hl; exact Hi).
    rewrite map_nth, seq_nth by exact Hi. cbn [Nat.add]. unfold f.
    pose proof (aview_some_of_apresent SEGS H m (p + Z.of_nat i) (Hp (Z.of_nat i) ltac:(lia))) as Hs.
    destruct (aview SEGS H m (p + Z.of_nat i)); [reflexivity | contradiction]. }
  split; [|split; [rewrite Hl; lia | rewrite Hl; exact Hv]].
  intros j Hj. rewrite Hl in Hj. exact (val_mem1_of_aview SEGS H m _ _ (Hv j Hj)).
Qed.

Lemma fa_pres : forall regs regs', aregs_preserved regs regs' ->
  forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' HP r Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.

Lemma fa_vm_kept : forall (W3 W2 : world SEGS) (m3 m2 : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W2) m2 x = aview SEGS (w_H W3) m3 x) ->
  val_mem SEGS (rdW W3 m3) a n v -> val_mem SEGS (rdW W2 m2) a n v.
Proof.
  intros W3 W2 m3 m2 a n v HK Hv k Hk. rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W2) m3 m2 (a + Z.of_nat k)).
  - exact (Hv k Hk).
  - apply HK. lia.
Qed.

Lemma fa_garr8_kept : forall (W3 W2 : world SEGS) (m3 m2 : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W2) m2 x = aview SEGS (w_H W3) m3 x) ->
  garr8 SEGS (rdW W3 m3) a l -> garr8 SEGS (rdW W2 m2) a l.
Proof.
  intros W3 W2 m3 m2 a l HK Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  apply (fa_vm_kept W3 W2 m3 m2 _ 1 _); [|exact Hv]. intros x Hx. apply HK. lia.
Qed.

(* Two byte arrays at the same place in the same memory agree on their common prefix. *)
Lemma fa_garr8_prefix : forall (m : word -> option byte) a l l',
  garr8 SEGS m a l -> garr8 SEGS m a l' -> (length l' <= length l)%nat -> firstn (length l') l = l'.
Proof.
  intros m a l l' Hl Hl' Hle. apply nth_ext with (d := 0) (d' := 0).
  - rewrite length_firstn. lia.
  - intros j Hj. rewrite length_firstn in Hj. rewrite nth_firstn.
    destruct (Nat.ltb_spec j (length l')) as [Hj'|Hj']; [|lia].
    destruct (Hl j ltac:(lia)) as [V1 B1]. destruct (Hl' j Hj') as [V2 B2].
    specialize (V1 0%nat ltac:(lia)). specialize (V2 0%nat ltac:(lia)). rewrite V1 in V2.
    injection V2 as V2. rewrite !le_byte_1_0 in V2 by lia.
    change (bv_unsigned (Z_to_bv 8 (nth j l 0)) = bv_unsigned (Z_to_bv 8 (nth j l' 0))) in V2.
    rewrite !fa_u8 in V2 by lia. exact V2.
Qed.

End k.
