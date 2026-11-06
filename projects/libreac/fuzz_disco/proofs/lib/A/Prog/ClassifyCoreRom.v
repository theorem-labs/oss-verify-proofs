(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_family_of.v, with its module paths, module names and numbers changed; 807 of its 905 lines of code are new or changed and 749 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/CheckTable.v; 352 of its 384 lines of code are new or changed and 873 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ClassifyCoreSeg.v; 49 of its 74 lines of code are new or changed and 359 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoFrame DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoImg DiscoRo ClassifyCore ClassifyCoreSeg.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Definition ro_span (lo hi : Z) : bool :=
existsb (fun s : Segment => negb (seg_writable s) && (Z.of_N (seg_base s) <=? lo) &&
  (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) disco_segs.

Lemma ro_span_in : forall lo hi, ro_span lo hi = true ->
forall a, lo <= a < hi -> in_roP disco_segs disco_relro_lo disco_relro_hi a.
Proof.
intros lo hi Hs a Ha. unfold ro_span in Hs. apply existsb_exists in Hs as (s & Hin & Hb).
apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [H0 H1].
apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
left. exists s. split; [exact Hin|]. split; [exact H0 | lia].
Qed.

Lemma rom_val_mem : forall (B : asyms) (H : word -> bool) mem a (n : nat) v,
arodata_okP disco_segs disco_relro_lo disco_relro_hi B (aview disco_segs H mem) ->
(forall k, (k < n)%nat -> in_roP disco_segs disco_relro_lo disco_relro_hi (a + Z.of_nat k) /\
  ~ Exists (in_zr (a + Z.of_nat k)) (as_owned_static B) /\ ~ (as_errno B <= a + Z.of_nat k < as_errno B + 4)) ->
(forall k, (k < n)%nat -> seg_rom disco_segs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte v n k))) ->
val_mem disco_segs (mrestrict H mem) a n v.
Proof.
intros B H mem a n v HR Hin Hb k Hk.
destruct (Hin k Hk) as (Hro & Ho & He).
pose proof (HR _ Hro Ho He) as E. rewrite (Hb k Hk) in E. cbn [option_map] in E.
unfold aview in E.
destruct (mbyte disco_segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Em; [|discriminate].
cbn [option_map] in E. injection E as E.
f_equal. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma cls_rom_disco : forall B : asyms, disco_ro_unowned B -> cls_rom_ok (PI := PB_disco) B.
Proof.
intros B DRO.
assert (U35 : ro_unowned B (disco_obj 35) 36).
{ apply disco_ro_unowned_at; [exact DRO|]. unfold disco_ro_ranges. apply in_or_app. right. left. vm_compute. reflexivity. }
assert (U36 : ro_unowned B (disco_obj 36) 8).
{ apply disco_ro_unowned_at; [exact DRO|]. unfold disco_ro_ranges. apply in_or_app. right. right. left. vm_compute. reflexivity. }
assert (HB : forall a, (disco_obj 35 <= a < disco_obj 35 + 36 \/ disco_obj 36 <= a < disco_obj 36 + 8) ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a [Ha|Ha]; [exact (U35 a Ha) | exact (U36 a Ha)]).
intros H mem HR. cbn [pa_segs pa_val pa_relro_lo pa_relro_hi PB_disco] in *.
rewrite (disco_obj_val 35) by (unfold disco_nobj; lia).
rewrite (disco_obj_val 36) by (unfold disco_nobj; lia).
assert (R35 : ro_span (disco_obj 35) (disco_obj 35 + 36) = true) by (vm_compute; reflexivity).
assert (R36 : ro_span (disco_obj 36) (disco_obj 36 + 8) = true) by (vm_compute; reflexivity).
split.
- apply (rom_val_mem B H mem _ 8 _ HR).
  + intros k Hk. split; [apply (ro_span_in _ _ R36); lia | apply HB; lia].
  + intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
- intros i Hi. apply (rom_val_mem B H mem _ 4 _ HR).
  + intros k Hk. split; [apply (ro_span_in _ _ R35); lia | apply HB; lia].
  + intros k Hk.
    do 9 (destruct i as [|i]; [do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|]). lia.
Qed.

End d.
