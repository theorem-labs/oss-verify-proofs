(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN1q.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN20.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition t0_e (k : Z) : Z := Z.log2 (k + 1).
Definition t0_t1 (k : Z) : Z := znth (4 * t0_e k - 3) size_classes.
Definition t0_b1 (k : Z) : bool := k <? t0_t1 k.
Definition t0_i3 (k : Z) : Z := if t0_b1 k then 4 * t0_e k - 4 else 4 * t0_e k - 2.
Definition t0_env (k : Z) : list (nat * Z) :=
[(aK, k); (aE, t0_e k); (aP, 2 ^ t0_e k); (aTQ1, DEB + dbj_idx (2 ^ t0_e k)); (aT1, t0_t1 k);
(aTQ2, SCT + 2 * (4 * t0_e k - 3)); (aT2, znth (t0_i3 k) size_classes); (aTQ3, SCT + 2 * t0_i3 k)].
Definition andx_f (kraw : Z) : Z :=
let x := zcanon (zcanon kraw + 1) in
let s1 := zalu64 ALU_OR (zalu64 ALU_OR (zalu32 ALU_SRL x (zcanon 2)) x) (zalu32 ALU_SRL x (zcanon 1)) in
let s2 := zalu64 ALU_OR (zalu32 ALU_SRL s1 (zcanon 2)) (zalu32 ALU_SRL x (zcanon 1)) in
let s3 := zalu64 ALU_OR (zalu64 ALU_SRL s2 (zcanon 4)) s2 in
let s4 := zalu64 ALU_OR (zalu64 ALU_SRL s3 (zcanon 8)) s3 in
let s5 := zalu64 ALU_OR (zalu64 ALU_SRL (zalu64 ALU_SLL s4 (zcanon 33)) (zcanon 49)) s4 in
zalu64 ALU_AND (zalu64 ALU_ADD s5 (zcanon 1)) (zalu64 ALU_XOR s5 (zcanon (-1))).
Lemma andx_f_ok xv : UZ xv ANDX = andx_f (xv aK).
Proof. unfold andx_f, ANDX; cbv zeta. cbn [UZ]. reflexivity. Qed.
Definition t0_chk (k : Z) : bool :=
let l := t0_env k in let e := t0_e k in
(andx_f k =? 2 ^ e) && (UZof l TQ1X =? DEB + dbj_idx (2 ^ e)) && (UZof l TQ2X =? SCT + 2 * (4 * e - 3))
&& (UZof l (TQ3X (t0_b1 k)) =? SCT + 2 * t0_i3 k) && (UZof l (RESX (t0_b1 k)) =? class_of_units k)
&& (3 <=? e) && (e <=? 12) && (znth (dbj_idx (2 ^ e)) DEBRUIJN =? e).
Lemma t0_chk_all : forallb t0_chk (zseq 10 8181) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma t0_chk_sound k : t0_chk k = true ->
andx_f k = 2 ^ t0_e k /\ UZof (t0_env k) TQ1X = DEB + dbj_idx (2 ^ t0_e k) /\ UZof (t0_env k) TQ2X = SCT + 2 * (4 * t0_e k - 3) /\
UZof (t0_env k) (TQ3X (t0_b1 k)) = SCT + 2 * t0_i3 k /\ UZof (t0_env k) (RESX (t0_b1 k)) = class_of_units k /\
3 <= t0_e k <= 12 /\ znth (dbj_idx (2 ^ t0_e k)) DEBRUIJN = t0_e k.
Proof.
unfold t0_chk. cbv zeta. intros C. repeat (apply andb_prop in C as [C ?H]).
apply Z.eqb_eq in C. apply Z.eqb_eq in H5. apply Z.eqb_eq in H4. apply Z.eqb_eq in H3. apply Z.eqb_eq in H2.
apply Z.leb_le in H1. apply Z.leb_le in H0. apply Z.eqb_eq in H.
split; [exact C|]. split; [exact H5|]. split; [exact H4|]. split; [exact H3|]. split; [exact H2|].
split; [clear - H1 H0; lia | exact H].
Qed.
Lemma t0_facts k : 10 <= k <= 8190 ->
andx_f k = 2 ^ t0_e k /\ UZof (t0_env k) TQ1X = DEB + dbj_idx (2 ^ t0_e k) /\ UZof (t0_env k) TQ2X = SCT + 2 * (4 * t0_e k - 3) /\
UZof (t0_env k) (TQ3X (t0_b1 k)) = SCT + 2 * t0_i3 k /\ UZof (t0_env k) (RESX (t0_b1 k)) = class_of_units k /\
3 <= t0_e k <= 12 /\ znth (dbj_idx (2 ^ t0_e k)) DEBRUIJN = t0_e k.
Proof. intros Hk. apply t0_chk_sound. exact (proj1 (forallb_zseq_iff t0_chk 10 8181) t0_chk_all k ltac:(lia)). Qed.
End a.
