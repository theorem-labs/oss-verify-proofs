(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP09 YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0l AF0m AF0x AE2y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma tfib_trailer_shadow : forall B, TfibSyms B -> forall ly S (W : world tfibsegs) mem md,
AR tfibsegs B ly S W mem md ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (ak_trailer tfib_K) 1 /\
shadow_hull_vis (aview tfibsegs (w_H W) mem) (ak_trailer tfib_K) 1.
Proof.
intros B TB ly S W mem md HAR. set (rd := aview tfibsegs (w_H W) mem).
pose proof (proj1 HAR) as HM.
assert (C1 : forall a v, const_chk ly a 1%N v = true -> rd a = Some (le_byte v 1 0)).
{ intros a v Hc. pose proof (const_chk_sound _ _ _ _ Hc) as E.
assert (X : cell_holds B ly rd (ACell (ANum a) (N.to_nat 1) (AV (ANum v)))).
{ apply (proj1 (Forall_forall (cell_holds B ly rd) (as_const B ly)) (am_const B ly S _ HM)).
rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ E). }
unfold cell_holds in X. cbn [c_at c_val c_w aeval N.to_nat] in X.
specialize (X 0%nat ltac:(lia)). rewrite Z.add_0_r in X. exact X. }
assert (ZS : forall lo len i, In (lo, len) Tfib_zero_shadow -> 0 <= i < len / 8 -> rd (SHADOW_OFF + lo / 8 + i) = Some 0).
{ intros lo len i Hin Hi.
exact (AR_zshadow_law_ok tfibsegs B ly S W mem md (lo, len) HAR ltac:(right; rewrite (ts_zsh B TB); exact Hin) i Hi). }
assert (HT : ak_trailer tfib_K = 0x20ea0) by reflexivity. rewrite HT.
assert (SB : SHADOW_OFF = 0x7fff8000) by reflexivity.
split.
- intros x Hx. assert (Ex : x = 0x20ea0) by lia. subst x.
exists (le_byte 0x2 1 0). split.
+ unfold shadow_of_addr. rewrite SB. apply C1. vm_compute. reflexivity.
+ right. vm_compute. split; reflexivity.
- intros s Hs. unfold shadow_addr in Hs. rewrite SB in Hs.
assert (Hs' : 0x7fffc1d0 <= s < 0x7fffc1d0 + 8) by (clear - Hs; split; [apply (proj1 Hs) |]; cbn in Hs; lia).
assert (C : s = 0x7fffc1d4 \/ s = 0x7fffc1d5 \/ s = 0x7fffc1d6 \/ s = 0x7fffc1d7 \/ (exists i, 0 <= i < 4 /\ s = 0x7fff8000 + 0x20e80 / 8 + i)).
{ destruct (Z_lt_le_dec s 0x7fffc1d4) as [L|G]; [right; right; right; right; exists (s - 0x7fffc1d0); split; [lia | cbn; lia] | lia]. }
destruct C as [-> | [-> | [-> | [-> | (i & Hi & ->)]]]].
+ rewrite (C1 0x7fffc1d4 0x2); [discriminate | vm_compute; reflexivity].
+ rewrite (C1 0x7fffc1d5 0xf9); [discriminate | vm_compute; reflexivity].
+ rewrite (C1 0x7fffc1d6 0xf9); [discriminate | vm_compute; reflexivity].
+ rewrite (C1 0x7fffc1d7 0xf9); [discriminate | vm_compute; reflexivity].
+ rewrite <- SB. rewrite (ZS 0x20e80 (0x20ea0 - 0x20e80) i); [discriminate | cbn; tauto | cbn; lia].
Qed.
End b.
