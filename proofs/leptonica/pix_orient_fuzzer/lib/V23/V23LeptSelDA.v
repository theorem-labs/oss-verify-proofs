(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRoom LeptExec LeptExecW LeptExecT LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section SelDA.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Local Open Scope Z_scope.

Lemma sd_frm_above : forall C s m m' (a : word), Cok C -> FRM C s m m' -> c_top C - LSTK <= s -> s <= u a -> m' a = m a.
Proof.
  intros C s m m' a CK F Hlo Hs. pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  apply F.
  - apply above_not_gap. lia.
  - intros G. apply pin_glob in G. unfold inZ in G. lia.
  - intros G. apply pin_errno in G. unfold inZ in G. lia.
  - unfold hcell. lia.
  - unfold scratch. lia.
Qed.

Lemma sd_win_cell : forall C A Ar m md E log (rb pb : expr) (s F p : Z),
  Cok C -> W C A m md -> sub_live Ar A -> log_flat E log ->
  ex_in_regions [(rb, - F, 0); (pb, 0, 8)] log = true -> edenot E rb = Z_to_bv 64 s -> edenot E pb = Z_to_bv 64 p ->
  0 <= F -> c_top C - LSTK <= s - F -> s <= p -> p + 8 <= c_top C ->
  W C A (mem_denot E m log) md /\ POSTM C Ar (p + 8) m (mem_denot E m log) /\
  (forall a : word, s <= u a < p -> mem_denot E m log a = m a).
Proof.
  intros C A Ar m md E log rb pb s F p CK HW SUB LF IR Erb Epb HF Hlo Hsp Hhi.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof (u64_range (c_sp0 C)) as RSP.
  assert (CH : forall a : word, mem_denot E m log a <> m a -> (s - F <= u a < s \/ p <= u a < p + 8)%Z).
  { intros a NE. pose proof (ex_changed E m log _ LF IR a NE) as EX.
    apply Exists_cons in EX. destruct EX as [EX|EX].
    - cbv beta iota in EX. rewrite Erb, u_Z2bv in EX by lia. lia.
    - apply Exists_cons in EX. destruct EX as [EX|EX]; [|apply Exists_nil in EX; contradiction].
      cbv beta iota in EX. rewrite Epb, u_Z2bv in EX by lia. lia. }
  split; [|split].
  - apply (W_local C A m md _ (p + 8) CK HW ltac:(lia)); [| apply mem_denot_grows].
    intros a NE. left. unfold scratch. pose proof (CH a NE). lia.
  - apply (POSTM_local C Ar A m md _ (p + 8) CK HW SUB). intros a NE. left. unfold scratch. pose proof (CH a NE). lia.
  - intros a Ha. destruct (omem_eq_dec (mem_denot E m log a) (m a)) as [EQ|NE]; [exact EQ|]. pose proof (CH a NE). lia.
Qed.

(* [comment removed for export] *)
Lemma sd_kept_cell : forall C (s' p : Z) M M' E (pb : expr),
  Cok C -> FRM C s' M M' -> c_top C - LSTK <= s' -> s' <= p -> 0 <= p < 2 ^ 64 -> edenot E pb = Z_to_bv 64 p ->
  ex_region_kept E M M' (pb, 0, 8).
Proof.
  intros C s' p M M' E pb CK F Hlo Hs Hp Epb. unfold ex_region_kept. cbv beta iota.
  intros x Hx. rewrite Epb, u_Z2bv in Hx by lia. apply (sd_frm_above C s' M M' x CK F Hlo). lia.
Qed.

(* [comment removed for export] *)
Lemma sd_pmx_free : forall C A A' s s' (m0 M m' : word -> option byte),
  (forall Af, sub_live Af A -> POSTM C Af s m0 M) -> sub_live A' A -> POSTM C A' s' M m' -> s' <= s ->
  forall Af, sub_live Af A' -> POSTM C Af s m0 m'.
Proof.
  intros C A A' s s' m0 M m' H SUB PM Hs Af SUBf.
  apply (POSTM_trans C Af s m0 M m').
  - apply H. exact (sub_live_trans _ _ _ SUBf SUB).
  - apply (POSTM_mono C Af s' s M m' Hs). exact (POSTM_sub C Af A' s' M m' SUBf PM).
Qed.
End SelDA.
