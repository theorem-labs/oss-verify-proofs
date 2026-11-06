(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS.
Open Scope Z_scope.
Unset Lia Cache.

Module CaseF.
Section WithPc.
Variable S_PC : int.
Variable SEL : sstate -> option (sv * sv).

Definition casef_apply (st : sstate) : option (list sstate) :=
  match SEL st with
  | Some (a, b) => Some [addfact st (FULt a b); addfact st (FULe b a)]
  | None => None
  end.

Definition casef_contract : contract := Contract S_PC casef_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Theorem casef_sound : contract_sound segs OPS MP PB casef_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [casef_contract c_apply] in HA. unfold casef_apply in HA.
  destruct (SEL st) as [[a b]|]; [|discriminate]. injection HA as <-.
  destruct (Z_lt_ge_dec (bv_unsigned (den E a)) (bv_unsigned (den E b))) as [D|D].
  - refine (Hk (addfact st (FULt a b)) _ E ms model (env_ext_refl (s_next st) E) HMP _); [left; reflexivity|].
    apply addfact_sound; [exact HS|]. cbn [fact_holds]. exact D.
  - refine (Hk (addfact st (FULe b a)) _ E ms model (env_ext_refl (s_next st) E) HMP _); [right; left; reflexivity|].
    apply addfact_sound; [exact HS|]. cbn [fact_holds]. lia.
Qed.
End Sound.
End WithPc.

Definition twin_sel (RS : r5) (OFF : w64) (st : sstate) : option (sv * sv) :=
  let a := sv_alu ALU_ADD (getr st RS) (VL OFF) in
  match addr_of a with
  | Some (k, o) =>
      if PrimInt63.eqb k 0%uint63 then None else
      match IMap.find k (s_regs st) with
      | Some r => match rg_bg r with BGZero => Some (VL o, rg_hi r) | _ => None end
      | None => None
      end
  | None =>
      match sym_addr_of (s_regs st) a with
      | Some (k, r, o) => match rg_bg r with BGZero => Some (o, rg_hi r) | _ => None end
      | None => None
      end
  end.
Definition twincase_contract (pc : int) (RS : r5) (OFF : w64) : contract := casef_contract pc (twin_sel RS OFF).
End CaseF.
