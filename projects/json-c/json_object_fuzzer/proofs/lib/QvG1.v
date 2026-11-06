(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq0.
From OSSVerify.json_c.json_object_fuzzer.images Require Export Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition asegs : list Segment := Asan.M.loaded_segments.

Definition a_ro_lo   : Z := 0x10000.
Definition a_text_lo : Z := 0x3d000.
Definition a_data_lo : Z := 0x0e2000.
Definition a_data2_lo : Z := 0x0e7000.
Definition a_data_hi : Z := 0x645000.

Definition A_SHADOW_OFS : Z := 0x7fff8000.
Definition KHI : Z := 0x10007fff8000.

Definition kLowEnd : Z := 0x7fff7000.

Notation lowhigh A n := ((0 < A /\ A + n <= 0x7fff7000) \/ 0x10007fff8000 <= A) (only parsing).

Notation off_hull A n := (A + n <= 0x10000 \/ 0x645000 <= A) (only parsing).

Notation appr A n := (lowhigh A n /\ off_hull A n) (only parsing).

Definition zhigh (A : Z) : Z := Z.b2z (0x10007fff8000 <=? A).
Definition zhull (A : Z) : Z := Z.b2z (0x645000 <=? A).
Arguments zhigh : simpl never.
Arguments zhull : simpl never.
Notation lowhigh_lia A n := (0 < A /\ 0 <= zhigh A <= 1 /\ A + n <= 0x7fff7000 + zhigh A * 0x10000000000000000
/\ 0x10007fff8000 * zhigh A <= A) (only parsing).
Notation appr_lia A n := (lowhigh_lia A n /\ 0 <= zhull A <= 1 /\ zhigh A <= zhull A
/\ A + n <= 0x10000 + zhull A * 0x10000000000000000 /\ 0x645000 * zhull A <= A) (only parsing).

Lemma appr_to_lia A n : 0 <= n -> A + n <= 2^64 -> appr A n -> appr_lia A n.
Proof.
intros Hn Hb [H1 H2]. unfold zhull, zhigh.
destruct (Z.leb_spec 0x645000 A); destruct (Z.leb_spec 0x10007fff8000 A); cbn [Z.b2z]; lia.
Qed.

Lemma appr_of_lia A n : appr_lia A n -> appr A n.
Proof. unfold zhull, zhigh. destruct (Z.leb_spec 0x645000 A); destruct (Z.leb_spec 0x10007fff8000 A); cbn [Z.b2z]; intros; lia. Qed.
Definition A_SHADOW_GOT : Z := 0x0e5db8.
Definition A_SHADOW_CELL : Z := 0x0efaf8.

Definition a_report_load1 : Z := 0x69be8.
Definition a_report_load2 : Z := 0x69c88.
Definition a_report_load4 : Z := 0x69d28.
Definition a_report_store4 : Z := 0x6a048.
