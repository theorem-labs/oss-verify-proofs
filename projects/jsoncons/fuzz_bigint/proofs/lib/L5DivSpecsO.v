(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreSpecs L5DivSpecs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5DSO.
Import L5CS. Import L5DS.
Abbreviation RSEGS := Plain.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Statics.
Variable XS : Type.
Variable xs_pre : XS -> (word -> option byte) -> Prop.
Variable xs_av : XS -> Z.

Definition xs_preL (L : heap_layout) (st : XS) (M : word -> option byte) : Prop := xs_pre st M /\ hl_sptop L <= xs_av st.

(* [comment removed for export] *)
Definition xdom (av a : Z) : Prop :=
  ((0x10000 <= a < 0x5f608) \/ (0x5f630 <= a < 0x5f650) \/ (0x5f660 <= a < 0x5f668)) \/ (0x6f8f8 <= a < 0x6f904) \/ (0x6fb20 <= a < 0x6fb22) \/ (0x70361 <= a < 0x70367)
  \/ (0x70408 <= a < 0x70410) \/ (0x906a8 <= a < 0x906b0) \/ (0x906d0 <= a < 0x906d8) \/ (0x90728 <= a < 0x90730)
  \/ (av <= a < av + 160).

Definition xs_agree_hyp : Prop :=
  forall st M M', xs_pre st M -> (forall a, xdom (xs_av st) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> xs_pre st M'.
Definition xs_av_hyp : Prop :=
  forall st M, xs_pre st M -> xs_av st mod 8 = 0 /\ 2 ^ 40 <= xs_av st /\ xs_av st + 160 <= 2 ^ 47.
End Statics.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CHAIN_SP_OFF : Z := 896.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition assert_throw_regs (R0 R : bvmap 5 word) (S : Z) : Prop :=
     getr R 2%bv = Z_to_bv 64 (S - 896)
  /\ getr R 3%bv = getr R0 3%bv
  /\ getr R 4%bv = getr R0 4%bv
  /\ getr R 10%bv = Z_to_bv 64 16
  /\ getr R 8%bv = Z_to_bv 64 (S + 64).
(* [comment removed for export] *)
Definition assert_throw_regs_tmpl (R : bvmap 5 word) (S : Z) : Prop :=
     getr R 20%bv = Z_to_bv 64 (S - 584)   (* [comment removed for export] *).
(* [comment removed for export] *)
Definition assert_throw_frames (R0 : bvmap 5 word) (M : word -> option byte) (S d1 d2 d3 d4 qx : Z) : Prop :=
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24,
     L5.u64_at RSEGS M (S - 872) w0
  /\ L5.u64_at RSEGS M (S - 864) w1
  /\ L5.u64_at RSEGS M (S - 856) w2
  /\ L5.u64_at RSEGS M (S - 848) (S + 64)
  /\ L5.u64_at RSEGS M (S - 840) 0x210e0
  /\ L5.u64_at RSEGS M (S - 800) (S + 64)
  /\ L5.u64_at RSEGS M (S - 792) (S + 64)
  /\ L5.u64_at RSEGS M (S - 784) w3
  /\ L5.u64_at RSEGS M (S - 776) 0x22100
  /\ L5.u8_at RSEGS M (S - 696) w4 /\ 0 <= w4 < 256 /\ Z.testbit w4 0 = false
  /\ L5.u8_at RSEGS M (S - 664) w5 /\ 0 <= w5 < 256 /\ Z.testbit w5 0 = true
  /\ L5.u64_at RSEGS M (S - 648) 8
  /\ L5.u64_at RSEGS M (S - 640) d1
  /\ L5.u8_at RSEGS M (S - 632) w6 /\ 0 <= w6 < 256 /\ Z.testbit w6 0 = true
  /\ L5.u64_at RSEGS M (S - 616) 8
  /\ L5.u64_at RSEGS M (S - 608) d2
  /\ L5.u8_at RSEGS M (S - 600) w7 /\ 0 <= w7 < 256 /\ Z.testbit w7 0 = false
  /\ L5.u64_at RSEGS M (S - 568) w8
  /\ L5.u64_at RSEGS M (S - 560) w9
  /\ L5.u64_at RSEGS M (S - 552) w10
  /\ L5.u64_at RSEGS M (S - 544) w11
  /\ L5.u64_at RSEGS M (S - 536) w12
  /\ L5.u64_at RSEGS M (S - 528) w13
  /\ L5.u64_at RSEGS M (S - 520) w14
  /\ L5.u64_at RSEGS M (S - 512) w15
  /\ L5.u64_at RSEGS M (S - 504) w16
  /\ L5.u64_at RSEGS M (S - 496) (S + 64)
  /\ L5.u64_at RSEGS M (S - 488) w17
  /\ L5.u64_at RSEGS M (S - 480) (S + 64)
  /\ L5.u64_at RSEGS M (S - 472) 0x22b38
  /\ L5.u8_at RSEGS M (S - 464) w18 /\ 0 <= w18 < 256 /\ Z.testbit w18 0 = false
  /\ L5.u64_at RSEGS M (S - 432) (S + 64)
  /\ L5.u64_at RSEGS M (S - 424) 0x227d0
  /\ L5.u8_at RSEGS M (S - 408) w19 /\ 0 <= w19 < 256 /\ Z.testbit w19 0 = false
  /\ L5.u64_at RSEGS M (S - 376) (S - 48)
  /\ L5.u64_at RSEGS M (S - 368) (S + 64)
  /\ L5.u64_at RSEGS M (S - 360) 0x22280
  /\ L5.u8_at RSEGS M (S - 280) w20 /\ 0 <= w20 < 256 /\ Z.testbit w20 0 = false
  /\ L5.u8_at RSEGS M (S - 248) w21 /\ 0 <= w21 < 256 /\ Z.testbit w21 0 = false
  /\ L5.u8_at RSEGS M (S - 216) w22 /\ 0 <= w22 < 256 /\ Z.testbit w22 0 = true
  /\ L5.u64_at RSEGS M (S - 200) 8
  /\ L5.u64_at RSEGS M (S - 192) d3
  /\ L5.u8_at RSEGS M (S - 184) w23 /\ 0 <= w23 < 256 /\ Z.testbit w23 0 = true
  /\ L5.u64_at RSEGS M (S - 168) 8
  /\ L5.u64_at RSEGS M (S - 160) d4
  /\ L5.u64_at RSEGS M (S - 152) (U R0 27)
  /\ L5.u64_at RSEGS M (S - 144) (U R0 26)
  /\ L5.u64_at RSEGS M (S - 136) (U R0 25)
  /\ L5.u64_at RSEGS M (S - 128) (U R0 24)
  /\ L5.u64_at RSEGS M (S - 120) (U R0 23)
  /\ L5.u64_at RSEGS M (S - 112) (U R0 22)
  /\ L5.u64_at RSEGS M (S - 104) (U R0 21)
  /\ L5.u64_at RSEGS M (S - 96) (U R0 20)
  /\ L5.u64_at RSEGS M (S - 88) (U R0 19)
  /\ L5.u64_at RSEGS M (S - 80) (U R0 18)
  /\ L5.u64_at RSEGS M (S - 72) (U R0 9)
  /\ L5.u64_at RSEGS M (S - 64) (S + 64)
  /\ L5.u64_at RSEGS M (S - 56) 0x21d20
  /\ L5.u8_at RSEGS M (S - 48) w24 /\ 0 <= w24 < 256 /\ Z.testbit w24 0 = false
  /\ L5.u64_at RSEGS M (S - 16) (U R0 8)
  /\ L5.u64_at RSEGS M (S - 8) 0x20600.

Definition assert_throw_at (L : heap_layout) (LBT LB1 : list (Z * Z)) (R0 : bvmap 5 word) (M0 : word -> option byte)
           (R : bvmap 5 word) (M : word -> option byte) (S : Z) : Prop :=
  exists d1 d2 d3 d4 qx,
     LBT = [(d1, 64); (d2, 64); (d3, 64); (d4, 64)]      (* [comment removed for export] *)
  /\ In (qx, 64) LB1                                    (* [comment removed for export] *)
  /\ assert_throw_regs R0 R S /\ assert_throw_regs_tmpl R S /\ assert_throw_frames R0 M S d1 d2 d3 d4 qx.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition EXC23_SZ : Z := 144.
Definition REF2_SZ : Z := 37.
Definition REF3_SZ : Z := 66.

Section Chains.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable XS : Type.
Variable xs_pre : XS -> (word -> option byte) -> Prop.
Variable xs_av : XS -> Z.
Variable xs_foot : list L5.range.
Variable e2_landed : XS -> list (Z * Z) -> credit -> Z -> (word -> option byte) -> bvmap 5 word -> list (Z * Z) -> credit -> Prop.
Variable e3_landed : XS -> list (Z * Z) -> credit -> Z -> (word -> option byte) -> bvmap 5 word -> list (Z * Z) -> credit -> Prop.

Definition e2_chain_hyp : Prop :=
  forall (fx : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
         (model : Model) (K : TSet) (LB : list (Z * Z)) (cr : credit) (S : Z) (st : XS),
    L5DS.zero_throw_at L LB R0 M0 R M S ->
    getr R0 1%bv = Z_to_bv 64 L5DS.OPMOD1_RET -> getr R0 2%bv = Z_to_bv 64 S -> getr R0 3%bv = Z_to_bv 64 GP -> getr R0 4%bv = Z_to_bv 64 TP ->
    xs_pre st M -> hl_sptop L <= xs_av st ->
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    L5C.stk (hl_sptop L) M S L5DS.SCR_OPMOD -> S + 240 <= hl_sptop L ->
    credit_ok L cr EXC23_SZ -> credit_ok L (debit L cr EXC23_SZ) REF2_SZ ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
        regs_preserved R0 R' ->
        e2_landed st LB cr S M' R' LB' cr' ->
        L5C.hpres L LB S L5DS.SCR_OPMOD xs_foot M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' TOP_PAD M' model') K) ->
    srealizes RSEGS SCFG (cfg R ZERO_THROW M model) K.

Definition e3_chain_hyp : Prop :=
  forall (fx : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
         (model : Model) (K : TSet) (LBT LB1 : list (Z * Z)) (cr : credit) (S : Z) (st : XS),
    assert_throw_at L LBT LB1 R0 M0 R M S ->
    getr R0 1%bv = Z_to_bv 64 L5DS.OPMOD1_RET -> getr R0 2%bv = Z_to_bv 64 S -> getr R0 3%bv = Z_to_bv 64 GP -> getr R0 4%bv = Z_to_bv 64 TP ->
    xs_pre st M -> hl_sptop L <= xs_av st ->
    hi_heap HI (LBT ++ LB1) cr M (m_vmmaps model) -> model_ok model -> K [] ->
    L5C.stk (hl_sptop L) M S L5DS.SCR_OPMOD -> S + 240 <= hl_sptop L ->
    credit_ok L cr EXC23_SZ -> credit_ok L (debit L cr EXC23_SZ) 48 -> credit_ok L (debit L (debit L cr EXC23_SZ) 48) REF3_SZ ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
        regs_preserved R0 R' ->
        e3_landed st LB1 cr S M' R' LB' cr' ->
        L5C.hpres L LB1 S L5DS.SCR_OPMOD xs_foot M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' TOP_PAD M' model') K) ->
    srealizes RSEGS SCFG (cfg R ASSERT_THROW M model) K.
End Chains.

(* [comment removed for export] *)
(* [comment removed for export] *)

End SCFG_1.
End L5DSO.
