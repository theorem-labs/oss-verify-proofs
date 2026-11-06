(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Export FseWalkKit FseWalkMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Export Shadow StepF StrwF.
Import ListNotations.
Open Scope Z_scope.
Ltac showpc ::= lazymatch goal with |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc | _ => idtac "showpc: not an evtF goal" end.
Ltac showreg r ::= let v := reg_val r in idtac "x" r "=" v.
Ltac call_pure_postF :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO; hnf in PO; destruct_exs PO; subst ms';
try (lazymatch goal with
| |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).
Tactic Notation "call_pureF" uconstr(SPEC) := eapply evtF_cut; [ eapply SPEC | call_pure_postF ].
Ltac u8_sok ARR i ::=
lazymatch type of ARR with u8arr ?segs ?mx ?A ?bs =>
let a := cur_mem_addr in
pose proof (u8arr_store_ok segs mx A bs i a ARR ltac:(rewrite ?length_map, ?Zupd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK
end.
Ltac u8_store ARR i v ::=
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mx ?a (le1 (Z_to_bv 64 ?x))) _) =>
lazymatch type of ARR with u8arr ?segs mx ?A (map (Z_to_bv 8) ?buf) =>
let E := addr_expr a in
let ARR' := fresh "ARR" in
assert (ARR' : u8arr segs (write_to_mem mx (wa E) (le1 (Z_to_bv 64 x))) A (map (Z_to_bv 8) (Zupd i v buf)));
[ replace (wa E) with (wa (A + i)) by (unfold wa; f_equal; lia);
apply (u8arr_sb segs mx A buf i x v ARR); [ rewrite ?Zupd_length; lia | ]
| clear ARR; store_done; rename ARR' into ARR ]
end
end.
