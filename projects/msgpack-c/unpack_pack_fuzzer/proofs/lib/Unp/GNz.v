(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import U32.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GFast.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS U32.
Open Scope Z_scope.
Unset Lia Cache.

Module GNz.
Section WithPc.
Variable NZ_PC : int.
Variable R : r5.

Definition gnz_apply (st : sstate) : option (list sstate) :=
  let c := getr st R in
  if GFast.GFast.nz_known_f (s_facts st) c then Some [addfact st (FNe c (VL wzero))] else None.

Definition gnz_contract : contract := Contract NZ_PC gnz_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Theorem gnz_sound : contract_sound segs OPS MP PB gnz_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gnz_contract c_apply] in HA. unfold gnz_apply in HA.
  rewrite GFast.GFast.nz_known_f_eq in HA. destruct (nz_known (s_facts st) (getr st R)) eqn:NZ; [|discriminate]. injection HA as <-.
  pose proof (nz_known_sound E (s_facts st) (getr st R) (so_facts _ _ _ _ _ _ HS) NZ) as NE.
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP _).
  apply addfact_sound; [exact HS|]. cbn [fact_holds den]. intros H. apply NE. rewrite H, wbv_unsigned. reflexivity.
Qed.

End Sound.
End WithPc.
End GNz.
