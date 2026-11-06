(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreSpecsU L5DivSpecsU.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5DSOU.
Import L5CSU. Import L5DSU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
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
  ((0x10000 <= a < 0x60100) \/ (0x60128 <= a < 0x60148) \/ (0x60158 <= a < 0x60160)) \/ (0x703f8 <= a < 0x70404) \/ (0x70620 <= a < 0x70622) \/ (0x70e61 <= a < 0x70e67)
  \/ (0x70f08 <= a < 0x70f10) \/ (0x911a8 <= a < 0x911b0) \/ (0x911d0 <= a < 0x911d8) \/ (0x91228 <= a < 0x91230)
  \/ (av <= a < av + 160).

Definition xs_agree_hyp : Prop :=
  forall st M M', xs_pre st M -> (forall a, xdom (xs_av st) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> xs_pre st M'.
Definition xs_av_hyp : Prop :=
  forall st M, xs_pre st M -> xs_av st mod 8 = 0 /\ 2 ^ 40 <= xs_av st /\ xs_av st + 160 <= 2 ^ 47.
End Statics.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CHAIN_SP_OFF : Z := 1008.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition assert_throw_regs (R0 R : bvmap 5 word) (S : Z) : Prop :=
     getr R 2%bv = Z_to_bv 64 (S - 1008)
  /\ getr R 3%bv = getr R0 3%bv
  /\ getr R 4%bv = getr R0 4%bv
  /\ getr R 10%bv = Z_to_bv 64 16
  /\ getr R 9%bv = Z_to_bv 64 (S + 64).
(* [comment removed for export] *)
Definition assert_throw_regs_tmpl (R : bvmap 5 word) (S : Z) : Prop :=
     True.
(* [comment removed for export] *)
Definition assert_throw_frames (R0 : bvmap 5 word) (M : word -> option byte) (S d1 d2 d3 d4 qx : Z) : Prop :=
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22,
     L5.u64_at RSEGS M (S - 976) w0
  /\ L5.u64_at RSEGS M (S - 968) (S + 64)
  /\ L5.u64_at RSEGS M (S - 960) w1
  /\ L5.u64_at RSEGS M (S - 952) 0x21508
  /\ L5.u64_at RSEGS M (S - 912) (S + 64)
  /\ L5.u64_at RSEGS M (S - 904) (S + 64)
  /\ L5.u64_at RSEGS M (S - 896) (S - 528)
  /\ L5.u64_at RSEGS M (S - 888) 0x22800
  /\ L5.u8_at RSEGS M (S - 808) w2 /\ 0 <= w2 < 256 /\ Z.testbit w2 0 = false
  /\ L5.u8_at RSEGS M (S - 744) w3 /\ 0 <= w3 < 256 /\ Z.testbit w3 0 = true
  /\ L5.u64_at RSEGS M (S - 728) 8
  /\ L5.u64_at RSEGS M (S - 720) d1
  /\ L5.u8_at RSEGS M (S - 712) w4 /\ 0 <= w4 < 256 /\ Z.testbit w4 0 = true
  /\ L5.u64_at RSEGS M (S - 696) 8
  /\ L5.u64_at RSEGS M (S - 688) d2
  /\ L5.u8_at RSEGS M (S - 664) w5 /\ 0 <= w5 < 256 /\ Z.testbit w5 0 = false
  /\ L5.u64_at RSEGS M (S - 632) w6
  /\ L5.u64_at RSEGS M (S - 624) w7
  /\ L5.u64_at RSEGS M (S - 616) w8
  /\ L5.u64_at RSEGS M (S - 608) w9
  /\ L5.u64_at RSEGS M (S - 600) w10
  /\ L5.u64_at RSEGS M (S - 592) w11
  /\ L5.u64_at RSEGS M (S - 584) w12
  /\ L5.u64_at RSEGS M (S - 576) w13
  /\ L5.u64_at RSEGS M (S - 568) w14
  /\ L5.u64_at RSEGS M (S - 560) (S + 64)
  /\ L5.u64_at RSEGS M (S - 552) w15
  /\ L5.u64_at RSEGS M (S - 544) (S + 64)
  /\ L5.u64_at RSEGS M (S - 536) 0x235c4
  /\ L5.u8_at RSEGS M (S - 528) w16 /\ 0 <= w16 < 256 /\ Z.testbit w16 0 = false
  /\ L5.u64_at RSEGS M (S - 496) (S + 64)
  /\ L5.u64_at RSEGS M (S - 488) 0x2318c
  /\ L5.u8_at RSEGS M (S - 472) w17 /\ 0 <= w17 < 256 /\ Z.testbit w17 0 = false
  /\ L5.u64_at RSEGS M (S - 440) (S - 64)
  /\ L5.u64_at RSEGS M (S - 432) (S + 64)
  /\ L5.u64_at RSEGS M (S - 424) 0x22a20
  /\ L5.u8_at RSEGS M (S - 344) w18 /\ 0 <= w18 < 256 /\ Z.testbit w18 0 = false
  /\ L5.u8_at RSEGS M (S - 280) w19 /\ 0 <= w19 < 256 /\ Z.testbit w19 0 = false
  /\ L5.u8_at RSEGS M (S - 248) w20 /\ 0 <= w20 < 256 /\ Z.testbit w20 0 = true
  /\ L5.u64_at RSEGS M (S - 232) 8
  /\ L5.u64_at RSEGS M (S - 224) d3
  /\ L5.u8_at RSEGS M (S - 200) w21 /\ 0 <= w21 < 256 /\ Z.testbit w21 0 = true
  /\ L5.u64_at RSEGS M (S - 184) 8
  /\ L5.u64_at RSEGS M (S - 176) d4
  /\ L5.u64_at RSEGS M (S - 168) (U R0 27)
  /\ L5.u64_at RSEGS M (S - 160) (U R0 26)
  /\ L5.u64_at RSEGS M (S - 152) (U R0 25)
  /\ L5.u64_at RSEGS M (S - 144) (U R0 24)
  /\ L5.u64_at RSEGS M (S - 136) (U R0 23)
  /\ L5.u64_at RSEGS M (S - 128) (U R0 22)
  /\ L5.u64_at RSEGS M (S - 120) (U R0 21)
  /\ L5.u64_at RSEGS M (S - 112) (U R0 20)
  /\ L5.u64_at RSEGS M (S - 104) (U R0 19)
  /\ L5.u64_at RSEGS M (S - 96) (U R0 18)
  /\ L5.u64_at RSEGS M (S - 88) (U R0 9)
  /\ L5.u64_at RSEGS M (S - 80) (S + 64)
  /\ L5.u64_at RSEGS M (S - 72) 0x22494
  /\ L5.u8_at RSEGS M (S - 64) w22 /\ 0 <= w22 < 256 /\ Z.testbit w22 0 = false
  /\ L5.u64_at RSEGS M (S - 32) (S + 96)
  /\ L5.u64_at RSEGS M (S - 24) 0x20d10
  /\ L5.u64_at RSEGS M (S - 16) (U R0 8)
  /\ L5.u64_at RSEGS M (S - 8) 0x20854.
(* [comment removed for export] *)
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
    L5DSU.zero_throw_at L LB R0 M0 R M S ->
    getr R0 1%bv = Z_to_bv 64 L5DSU.OPMOD1_RET -> getr R0 2%bv = Z_to_bv 64 S -> getr R0 3%bv = Z_to_bv 64 GP -> getr R0 4%bv = Z_to_bv 64 TP ->
    xs_pre st M -> hl_sptop L <= xs_av st ->
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    L5C.stk (hl_sptop L) M S L5DSU.SCR_OPMOD -> S + 240 <= hl_sptop L ->
    credit_ok L cr EXC23_SZ -> credit_ok L (debit L cr EXC23_SZ) REF2_SZ ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
        regs_preserved R0 R' ->
        e2_landed st LB cr S M' R' LB' cr' ->
        L5C.hpres L LB S L5DSU.SCR_OPMOD xs_foot M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' TOP_PAD M' model') K) ->
    srealizes RSEGS SCFG (cfg R ZERO_THROW M model) K.

Definition e3_chain_hyp : Prop :=
  forall (fx : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
         (model : Model) (K : TSet) (LBT LB1 : list (Z * Z)) (cr : credit) (S : Z) (st : XS),
    assert_throw_at L LBT LB1 R0 M0 R M S ->
    getr R0 1%bv = Z_to_bv 64 L5DSU.OPMOD1_RET -> getr R0 2%bv = Z_to_bv 64 S -> getr R0 3%bv = Z_to_bv 64 GP -> getr R0 4%bv = Z_to_bv 64 TP ->
    xs_pre st M -> hl_sptop L <= xs_av st ->
    hi_heap HI (LBT ++ LB1) cr M (m_vmmaps model) -> model_ok model -> K [] ->
    L5C.stk (hl_sptop L) M S L5DSU.SCR_OPMOD -> S + 240 <= hl_sptop L ->
    credit_ok L cr EXC23_SZ -> credit_ok L (debit L cr EXC23_SZ) 48 -> credit_ok L (debit L (debit L cr EXC23_SZ) 48) REF3_SZ ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
        regs_preserved R0 R' ->
        e3_landed st LB1 cr S M' R' LB' cr' ->
        L5C.hpres L LB1 S L5DSU.SCR_OPMOD xs_foot M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' TOP_PAD M' model') K) ->
    srealizes RSEGS SCFG (cfg R ASSERT_THROW M model) K.
End Chains.

(* [comment removed for export] *)
(* [comment removed for export] *)

End SCFG_1.
End L5DSOU.
