(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool Ring.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require Import ZSysLite ZCall ZCallL TSet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Section Rom.
Variables (lo hi : Z).

Definition rom_okG (M : mem) : Prop :=
  forall x : word, lo <= bv_unsigned x < hi -> M x = None.

Lemma rom_okG_frame : forall M a bs,
  rom_okG M -> 0 <= a -> a + Z.of_nat (length bs) <= two64 ->
  zdisj a (Z.of_nat (length bs)) lo (hi - lo) ->
  rom_okG (wbytes M (w64 a) bs).
Proof.
  intros M a bs H Ha Hn Hd x Hx. unfold zdisj in *.
  rewrite wbytes_out; [apply H; exact Hx | lia | lia | lia].
Qed.

Lemma rom_isG : forall segs M a bs,
  rom_okG M -> 0 <= lo -> hi <= two64 -> lo <= a -> a + Z.of_nat (length bs) <= hi ->
  rdn segs (fun _ => None) (w64 a) (length bs) = Some bs ->
  mem_is segs M a bs.
Proof.
  intros segs M a bs H Hlo Hhi Ha Hb Hr.
  apply (mem_is_of_rom segs M a (length bs) bs); [lia | lia | | exact Hr].
  intros x Hx. apply H. lia.
Qed.

Lemma rom_okG_magree : forall M0 M lo1 hi1 lo2 hi2,
  rom_okG M0 -> magree M0 M lo1 hi1 lo2 hi2 -> (hi <= lo1 \/ hi1 <= lo) -> (hi <= lo2 \/ hi2 <= lo) -> rom_okG M.
Proof.
  intros M0 M lo1 hi1 lo2 hi2 HR HA H1 H2 x Hx. rewrite (HA x); [apply HR; exact Hx | lia | lia].
Qed.

Lemma rom_okG_magreeL : forall M0 M rs,
  rom_okG M0 -> magreeL M0 M rs -> disj_all lo (hi - lo) rs -> rom_okG M.
Proof.
  intros M0 M rs HR HA Hd x Hx. rewrite (HA x); [apply HR; exact Hx |].
  eapply disj_outside; [exact Hd | lia].
Qed.

Lemma rom_okG_zzero : forall M a n,
  rom_okG M -> 0 <= a -> a + n < two64 -> 0 <= n -> (a + n <= lo \/ hi <= a) -> rom_okG (zzero M a n).
Proof.
  intros M a n HR Ha Han Hn Hd x Hx. rewrite zzero_out; [apply HR; exact Hx | lia | lia | lia | lia].
Qed.

Lemma rom_okG_zunmap : forall M a n,
  rom_okG M -> 0 <= a -> a + n < two64 -> 0 <= n -> (a + n <= lo \/ hi <= a) -> rom_okG (zunmap M a n).
Proof.
  intros M a n HR Ha Han Hn Hd x Hx. rewrite zunmap_out'; [apply HR; exact Hx | lia | lia | lia | lia].
Qed.

Lemma rom_okG_of_hyp : forall M,
  0 <= lo -> hi <= two64 ->
  (forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None) -> rom_okG M.
Proof.
  intros M Hlo Hhi H x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply H. exact Hx.
Qed.

Lemma rom_okG_agree : forall M M',
  (forall x : word, lo <= bv_unsigned x < hi -> M' x = M x) -> rom_okG M -> rom_okG M'.
Proof. intros M M' HA H x Hx. rewrite (HA x Hx). apply H. exact Hx. Qed.
End Rom.

Lemma mem_zero_lo : forall segs M a len cut,
  mem_zero segs M a len -> cut - a <= len -> mem_zero segs M a (cut - a).
Proof. intros segs M a len cut Hz Hc i Hi. apply Hz. lia. Qed.

Lemma mem_zero_hi : forall segs M a len cut,
  mem_zero segs M a len -> a <= cut -> mem_zero segs M cut (a + len - cut).
Proof. intros segs M a len cut Hz Hc i Hi. replace (cut + i) with (a + (cut - a + i)) by lia. apply Hz. lia. Qed.

Lemma mem_zero_within : forall segs M a len a' n,
  mem_zero segs M a len -> a <= a' -> a' + n <= a + len -> mem_zero segs M a' n.
Proof. intros segs M a len a' n Hz H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply Hz. lia. Qed.

End FXG.
Ltac zmem_zero_solve :=
  match goal with
  | H : mem_zero ?segs ?M _ _ |- mem_zero ?segs ?M _ _ => apply (mem_zero_within _ _ _ _ _ _ H); zlia
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Lemma mem_zero_split_store : forall segs M a bs a' len,
  mem_zero segs M a' len ->
  a' <= a -> a + Z.of_nat (length bs) <= a' + len ->
  0 <= a' -> a' + len < two64 -> 0 < Z.of_nat (length bs) ->
  mem_zero segs (wbytes M (w64 a) bs) a' (a - a') /\
  mem_zero segs (wbytes M (w64 a) bs) (a + Z.of_nat (length bs)) (a' + len - (a + Z.of_nat (length bs))).
Proof.
  intros segs M a bs a' len Hz H1 H2 H3 H4 H5. split.
  - apply mem_zero_frame; [apply (mem_zero_lo _ _ _ _ a Hz); lia | unfold zdisj; lia].
  - apply mem_zero_frame; [apply (mem_zero_hi _ _ _ _ (a + Z.of_nat (length bs)) Hz); lia | unfold zdisj; lia].
Qed.

Lemma bytes_le_to_Z_zeros : forall k, bytes_le_to_Z (repeat (Z_to_bv 8 0) k) = 0.
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat bytes_le_to_Z]. rewrite IH.
  replace (bv_unsigned (Z_to_bv 8 0)) with 0 by reflexivity. reflexivity.
Qed.

End FXG.
Ltac zzeros :=
  rewrite ?bytes_le_to_Z_zeros;
  repeat match goal with
  | |- context [bv_swrap ?n ?k] =>
      lazymatch isZcst k with true => let v := eval vm_compute in (bv_swrap n k) in change (bv_swrap n k) with v end
  | |- context [bv_unsigned (Z_to_bv ?n ?k)] =>
      lazymatch isZcst k with true => let v := eval vm_compute in (bv_unsigned (Z_to_bv n k)) in change (bv_unsigned (Z_to_bv n k)) with v end
  | |- context [bytes_le_to_Z (Z_to_le_bytes ?n ?k)] =>
      lazymatch isZcst k with true => let v := eval vm_compute in (bytes_le_to_Z (Z_to_le_bytes n k)) in change (bytes_le_to_Z (Z_to_le_bytes n k)) with v end
  end.
Ltac znorm_zero_len H :=
  try lazymatch type of H with
  | mem_zero ?s ?M ?b ?n =>
      let E := fresh "E" in
      eassert (E : n = _) by (ring_simplify; reflexivity);
      lazymatch type of E with
      | n = n => clear E
      | _ => rewrite E in H; clear E
      end
  end.
Ltac znat_lits_in H :=
  repeat match type of H with
  | context [Z.of_nat ?n] =>
      lazymatch n with
      | S _ => idtac | O => idtac
      end;
      let v := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with v in H
  end.
