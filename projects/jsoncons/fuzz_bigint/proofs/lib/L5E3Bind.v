(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg HeapIface LibIface
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5DivSpecsO L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2Kit L5E3Chain.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5E3BIND.
Import L5CS L5PS L5STRK L5E2K.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Lemma assert_throw_at_req L LBT LB1 R0 M0 R M S :
  L5DSO.assert_throw_at L LBT LB1 R0 M0 R M S -> L5E3C.assert_throw_req LBT LB1 R0 M0 R M S.
Proof.
  intros (d1 & d2 & d3 & d4 & qx & ELBT & INQ & (Q2 & Q3 & Q4 & Q10 & Q8) & Q20 & FR). red in Q20.
  destruct FR as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22 & w23 & w24
    & c872 & c864 & c856 & c848 & c840 & c800 & c792 & c784 & c776
    & c696 & [r696a r696b] & b696 & c664 & [r664a r664b] & b664 & c648 & c640 & c632 & [r632a r632b] & b632 & c616 & c608 & c600 & [r600a r600b] & b600
    & c568 & c560 & c552 & c544 & c536 & c528 & c520 & c512 & c504 & c496 & c488 & c480 & c472 & c464 & [r464a r464b] & b464
    & c432 & c424 & c408 & [r408a r408b] & b408 & c376 & c368 & c360
    & c280 & [r280a r280b] & b280 & c248 & [r248a r248b] & b248 & c216 & [r216a r216b] & b216 & c200 & c192 & c184 & [r184a r184b] & b184 & c168 & c160
    & c152 & c144 & c136 & c128 & c120 & c112 & c104 & c96 & c88 & c80 & c72 & c64 & c56 & c48 & [r48a r48b] & b48 & c16 & c8).
  (* [comment removed for export] *)
  exists d1, d2, d3, d4, w2, w1, w0, w3, w17, w16, w15, w14, w13, w12, w11, w10, w9, w8, w4, w5, w6, w7, w18, w19, w20, w21, w22, w23, w24.
  repeat split; assumption.
Qed.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis LYX : layoutx L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Theorem e3_chain : L5US.e3_chain_spec_of L (L5DSO.assert_throw_at L) HI.
Proof.
  intros fx R0 M0 R M model K LBT LB1 cr S st AT.
  exact (L5E3C.e3_chain L HI LY LYX HIok fx R0 M0 R M model K LBT LB1 cr S st (assert_throw_at_req L LBT LB1 R0 M0 R M S AT)).
Qed.
End WithHeap.
End SCFG_1.
End L5E3BIND.
