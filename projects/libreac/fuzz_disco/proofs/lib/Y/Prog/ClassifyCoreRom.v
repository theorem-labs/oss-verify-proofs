(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of kind_of_link1 on fuzz_grant.asan, written for libreac/fuzz_grant: the entry seat, the walk loop and the return are adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v and proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v; the contract and the branch lemmas are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/KindOfLink1.v, with its module paths and module names changed; 58 of its 174 lines of code are new or changed and 53 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/KindOfLink1.v; 47 of its 73 lines of code are new or changed and 148 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v YCbj YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ClassifyCore ClassifyCoreSeg.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Definition ro_span (lo hi : Z) : bool :=
existsb (fun s : Segment => negb (seg_writable s) && (Z.of_N (seg_base s) <=? lo) &&
  (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs.

Lemma ro_span_in : forall lo hi rlo rhi, ro_span lo hi = true ->
forall a, lo <= a < hi -> in_roP tfibsegs rlo rhi a.
Proof.
intros lo hi rlo rhi Hs a Ha. unfold ro_span in Hs. apply existsb_exists in Hs as (s & Hin & Hb).
apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [H0 H1].
apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
left. exists s. split; [exact Hin|]. split; [exact H0 | lia].
Qed.

Lemma rom_val_mem : forall (B : asyms) (H : word -> bool) mem a (n : nat) v rlo rhi,
arodata_okP tfibsegs rlo rhi B (aview tfibsegs H mem) ->
(forall k, (k < n)%nat -> in_roP tfibsegs rlo rhi (a + Z.of_nat k) /\
  ~ Exists (in_zr (a + Z.of_nat k)) (as_owned_static B) /\ ~ (as_errno B <= a + Z.of_nat k < as_errno B + 4)) ->
(forall k, (k < n)%nat -> seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte v n k))) ->
val_mem tfibsegs (mrestrict H mem) a n v.
Proof.
intros B H mem a n v rlo rhi HR Hin Hb k Hk.
destruct (Hin k Hk) as (Hro & Ho & He).
pose proof (HR _ Hro Ho He) as E. rewrite (Hb k Hk) in E. cbn [option_map] in E.
unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Em; [|discriminate].
cbn [option_map] in E. injection E as E.
f_equal. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma cls_rom_tfib : forall B : asyms, tfib_ro_unowned B -> cls_rom_ok (PI := PB_tfib) B.
Proof.
intros B TRO.
assert (U35 : ro_unowned B (tfib_val0 (A_OBJ 35)) 36).
{ apply tfib_ro_unowned_at; [exact TRO|]. unfold tfib_ro_ranges. apply in_or_app. right. left. vm_compute. reflexivity. }
assert (U36 : ro_unowned B (tfib_val0 (A_OBJ 36)) 8).
{ apply tfib_ro_unowned_at; [exact TRO|]. unfold tfib_ro_ranges. apply in_or_app. right. right. left. vm_compute. reflexivity. }
assert (HB : forall a, (tfib_val0 (A_OBJ 35) <= a < tfib_val0 (A_OBJ 35) + 36 \/
  tfib_val0 (A_OBJ 36) <= a < tfib_val0 (A_OBJ 36) + 8) ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a [Ha|Ha]; [exact (U35 a Ha) | exact (U36 a Ha)]).
intros H mem HR. cbn [pa_segs pa_val pa_relro_lo pa_relro_hi PB_tfib] in *.
assert (R35 : ro_span (tfib_val0 (A_OBJ 35)) (tfib_val0 (A_OBJ 35) + 36) = true) by (vm_compute; reflexivity).
assert (R36 : ro_span (tfib_val0 (A_OBJ 36)) (tfib_val0 (A_OBJ 36) + 8) = true) by (vm_compute; reflexivity).
split.
- apply (rom_val_mem B H mem _ 8 _ _ _ HR).
  + intros k Hk. split; [apply (ro_span_in _ _ _ _ R36); lia | apply HB; lia].
  + intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
- intros i Hi. apply (rom_val_mem B H mem _ 4 _ _ _ HR).
  + intros k Hk. split; [apply (ro_span_in _ _ _ _ R35); lia | apply HB; lia].
  + intros k Hk.
    do 9 (destruct i as [|i]; [do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|]). lia.
Qed.

End d.
