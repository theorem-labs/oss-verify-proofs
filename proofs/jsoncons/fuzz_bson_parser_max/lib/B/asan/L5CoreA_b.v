(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx
     L5Defs L5Core L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5CA.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition amodel_ok (A : list (Z * Z)) (model : Model) : Prop := m_halted model = None /\ MInv A model.

Definition astk (ar : asan_run) (M : word -> option byte) (sp scr : Z) : Prop :=
  sp mod 16 = 0 /\ ahl_ceil ar + 4096 + scr <= sp /\ sp <= ar_sptop ar /\ (0x7fff80000000 <= ar_sptop ar <= 2 ^ 47) /\
  L5.defined M (sp - scr) scr /\ L5.defined M sp (ar_stack_top ar - sp).

Definition ffr (FF LK : list fframe) (d : Z) : Prop := Z.of_nat (ff_count 1 (FF ++ LK)) + d <= ff_cap 1.
Definition ffrs (FF : list fframe) (sp : Z) : Prop := forall f, In f FF -> sp + 32 <= ff_rs f.

Definition aobj (FF : list fframe) (o sz : Z) : Prop :=
  exists f, In f FF /\ ff_addr f + 32 <= o /\ o + sz <= ff_addr f + ff_bytes (ff_class f) - 8 /\ o mod 8 = 0.

Definition akept (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (W : list L5.range) (a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ aclient L ar LB FF sp scr a /\ L5.outside W a.
Definition ahpres (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (W : list L5.range)
           (M M' : word -> option byte) : Prop :=
  (forall a, akept L ar LB FF sp scr W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ L5.defined M' (sp - scr) scr
  /\ (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None).

Definition afresh (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (M' : word -> option byte) (A n : Z) : Prop :=
  ablock_range L ar A n /\ blocks_apart A n LB /\ fframes_apart A n FF /\ L5.defined M' A n /\ shadow_blk M' A n.

(* [comment removed for export] *)
Inductive growth : Type := Same | Grown (A : Z) (cap : Z).
End SCFG_1.
End L5CA.
