(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare BnModel BnMath BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Abbreviation KHI := 17594333495296.      (* [comment removed for export] *)
Abbreviation HIE := 140737488355328.      (* [comment removed for export] *)
Abbreviation SHA := 2147450880.          (* [comment removed for export] *)
Abbreviation IMG := 6848512.             (* [comment removed for export] *)
Abbreviation LOSH := 2147446784.         (* [comment removed for export] *)
Abbreviation LSLO := 2148290560.         (* [comment removed for export] *)
Abbreviation LSHI := 2415881728.         (* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation APP x n := (IMG <= x /\ (x + n <= LOSH \/ KHI <= x)).

(* [comment removed for export] *)
Definition shcells (m : word -> option byte) : Prop :=
  cellN SEGS_A m 0x129ea8 8 0x132278 /\ cellN SEGS_A m 0x132278 8 SHA.

(* [comment removed for export] *)
Definition objsh (m : word -> option byte) (o : Z) : Prop :=
  forall g, 0 <= g < 64 -> cellN SEGS_A m (SHA + o / 8 + g) 1 0.

Lemma shcells_unch : forall m m' rs,
  unch m m' rs -> (forall r, In r rs -> KHI <= fst r \/ (IMG <= fst r /\ snd r <= LOSH)) -> shcells m -> shcells m'.
Proof.
  intros m m' rs Hu Hrs [A B]. split.
  all: eapply cellN_unch; [exact Hu | lia | cbn; lia | intros r Hr; specialize (Hrs r Hr); cbn; lia | assumption].
Qed.

Lemma objsh_unch : forall m m' rs o,
  unch m m' rs -> (forall r, In r rs -> KHI <= fst r \/ (IMG <= fst r /\ snd r <= LOSH)) -> 0 <= o -> o + 516 <= HIE -> objsh m o -> objsh m' o.
Proof.
  intros m m' rs o Hu Hrs Ho1 Ho2 H g Hg.
  eapply cellN_unch; [exact Hu | lia | cbn; lia | intros r Hr; specialize (Hrs r Hr); cbn; lia | apply H; exact Hg].
Qed.

(* [comment removed for export] *)
Ltac kcsh OSH g := kc1 (OSH g ltac:(lia)).

(* [comment removed for export] *)
Definition five_tbl : list Z := [5; 25; 125; 625; 3125; 15625; 78125; 390625; 1953125; 9765625; 48828125; 244140625].
Definition tblsh (m : word -> option byte) : Prop := forall g, 0 <= g < 6 -> cellN SEGS_A m (SHA + 18168 + g) 1 0.
