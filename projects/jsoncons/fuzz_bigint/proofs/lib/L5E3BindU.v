(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg HeapIface LibIface
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5DivSpecsU L5DivSpecsOU L5KnP L5ParseKit L5ParseSpecsU L5Bytes L5StrctorKitU L5UnwindSpecsU L5E2KitU L5E3UChain.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5E3BINDU.
Import L5CSU L5PSU L5STRKU L5E2KU.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Lemma assert_throw_at_req L LBT LB1 R0 M0 R M S :
  L5DSOU.assert_throw_at L LBT LB1 R0 M0 R M S -> L5E3CU.assert_throw_req LBT LB1 R0 M0 R M S.
Proof.
  intros (d1 & d2 & d3 & d4 & qx & ELBT & INQ & (Q2 & Q3 & Q4 & Q10 & Q9) & _ & FR).
  destruct FR as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21 & w22
    & c976 & c968 & c960 & c952 & c912 & c904 & c896 & c888
    & c808 & [r808a r808b] & b808 & c744 & [r744a r744b] & b744 & c728 & c720 & c712 & [r712a r712b] & b712 & c696 & c688 & c664 & [r664a r664b] & b664
    & c632 & c624 & c616 & c608 & c600 & c592 & c584 & c576 & c568 & c560 & c552 & c544 & c536 & c528 & [r528a r528b] & b528
    & c496 & c488 & c472 & [r472a r472b] & b472 & c440 & c432 & c424
    & c344 & [r344a r344b] & b344 & c280 & [r280a r280b] & b280 & c248 & [r248a r248b] & b248 & c232 & c224 & c200 & [r200a r200b] & b200 & c184 & c176
    & c168 & c160 & c152 & c144 & c136 & c128 & c120 & c112 & c104 & c96 & c88 & c80 & c72 & c64 & [r64a r64b] & b64 & c32 & c24 & c16 & c8).
  (* [comment removed for export] *)
  exists d1, d2, d3, d4, w1, w0, w15, w14, w13, w12, w11, w10, w9, w8, w7, w6, w2, w3, w4, w5, w16, w17, w18, w19, w20, w21, w22.
  repeat split; assumption.
Qed.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis LYX : layoutx L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Theorem e3_chain : L5USU.e3_chain_spec_of L (L5DSOU.assert_throw_at L) HI.
Proof.
  intros fx R0 M0 R M model K LBT LB1 cr S st AT.
  exact (L5E3CU.e3_chain L HI LY LYX HIok fx R0 M0 R M model K LBT LB1 cr S st (assert_throw_at_req L LBT LB1 R0 M0 R M S AT)).
Qed.
End WithHeap.
End SCFG_1.
End L5E3BINDU.
