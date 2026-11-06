(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
Import ListNotations.
Open Scope Z_scope.

Definition K066 : Z := 0x3FE51EB851EB851F.

Definition lf_test (md : rmode) (S c : Z) : bool :=
fle_d (fmul_d md (fcvt_d_w md (Z_to_bv 64 S)) (Z_to_bv 64 K066)) (fcvt_d_w md (Z_to_bv 64 c)).

Definition lf_sizes : list Z :=
[16; 32; 64; 128; 256; 512; 1024; 2048; 4096; 8192; 16384; 32768; 65536; 131072; 262144;
524288; 1048576; 2097152; 4194304; 8388608; 16777216; 33554432; 67108864; 134217728;
268435456; 536870912; 1073741824; 2147483647].

Definition lf_thr (S : Z) : Z :=
match S with
| 16 => 11
| 32 => 22
| 64 => 43
| 128 => 85
| 256 => 169
| 512 => 338
| 1024 => 676
| 2048 => 1352
| 4096 => 2704
| 8192 => 5407
| 16384 => 10814
| 32768 => 21627
| 65536 => 43254
| 131072 => 86508
| 262144 => 173016
| 524288 => 346031
| 1048576 => 692061
| 2097152 => 1384121
| 4194304 => 2768241
| 8388608 => 5536482
| 16777216 => 11072963
| 33554432 => 22145926
| 67108864 => 44291851
| 134217728 => 88583701
| 268435456 => 177167401
| 536870912 => 354334802
| 1073741824 => 708669604
| 2147483647 => 1417339208
| _ => 0
end.

Definition lf_test_spec : Prop :=
forall S c, In S lf_sizes -> 0 <= c < 2^31 -> lf_test RNE S c = (lf_thr S <=? c).

Lemma lf_sizes_shape : forall S, In S lf_sizes <-> (exists e : nat, (e <= 26)%nat /\ S = 16 * 2 ^ Z.of_nat e) \/ S = 2147483647.
Proof.
intros S. split.
- intros H. cbn in H.
repeat match goal with
| H : ?a = S \/ ?r |- _ => destruct H as [<-|H]
| H : False |- _ => destruct H
end.
all: first [ right; reflexivity
| left; match goal with |- exists e, _ /\ ?a = _ =>
let n := eval vm_compute in (Z.to_nat (Z.log2 (a / 16))) in exists n; split; [lia| reflexivity] end ].
- intros [(e & He & ->) | ->]; [| cbn; tauto]. do 27 (destruct e as [|e]; [cbn; tauto|]). lia.
Qed.

Lemma lf_size_range : forall S, In S lf_sizes -> 16 <= S <= 2147483647.
Proof.
intros S H.
assert (C : forallb (fun S => (16 <=? S) && (S <=? 2147483647)) lf_sizes = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C S H). apply andb_prop in C as [C1 C2].
apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
Qed.

Lemma lf_thr_lt : forall S, In S lf_sizes -> 0 < lf_thr S < S.
Proof.
intros S H.
assert (C : forallb (fun S => (0 <? lf_thr S) && (lf_thr S <? S)) lf_sizes = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C S H). apply andb_prop in C as [C1 C2].
apply Z.ltb_lt in C1. apply Z.ltb_lt in C2. lia.
Qed.

Lemma lf_thr_step : forall S, In S lf_sizes -> S <= 2^29 -> In (2 * S) lf_sizes /\ lf_thr S + 1 <= lf_thr (2 * S).
Proof.
intros S H HS.
assert (C : forallb (fun S => (2^29 <? S) || (existsb (Z.eqb (2 * S)) lf_sizes && (lf_thr S + 1 <=? lf_thr (2 * S)))) lf_sizes = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C S H). apply orb_prop in C as [C|C]; [apply Z.ltb_lt in C; lia|].
apply andb_prop in C as [C1 C2]. apply Z.leb_le in C2. split; [|exact C2].
apply existsb_exists in C1 as (x & Hx & Ex). apply Z.eqb_eq in Ex. rewrite Ex. exact Hx.
Qed.

Lemma lf_thr_top : lf_thr 1073741824 + 1 <= lf_thr 2147483647.
Proof. cbn. lia. Qed.

Example lf_test_16_10 : lf_test RNE 16 10 = false. Proof. vm_compute. reflexivity. Qed.
Example lf_test_16_11 : lf_test RNE 16 11 = true. Proof. vm_compute. reflexivity. Qed.
Example lf_test_1024_675 : lf_test RNE 1024 675 = false. Proof. vm_compute. reflexivity. Qed.
Example lf_test_1024_676 : lf_test RNE 1024 676 = true. Proof. vm_compute. reflexivity. Qed.
Example lf_test_big : lf_test RNE 1073741824 708669603 = false /\ lf_test RNE 1073741824 708669604 = true.
Proof. split; vm_compute; reflexivity. Qed.
Example lf_test_intmax : lf_test RNE 2147483647 1417339207 = false /\ lf_test RNE 2147483647 1417339208 = true.
Proof. split; vm_compute; reflexivity. Qed.
