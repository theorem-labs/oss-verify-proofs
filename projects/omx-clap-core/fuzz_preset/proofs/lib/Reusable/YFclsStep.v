(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the fclass.d single step, in YK0o.v's fp_pipeline style (the sibling of YK0o.v's
   fp_step_fsd), for the one F instruction YK0o has no single-step lemma for. LPS Sem.v:651-652 (Fclass writes an
   INTEGER register) and Fpu.v:586-598 (the fclass bit mask). Proved first in fuzz_preset ex_value piece 5, lane D
   (lib/A/Prog/S8aNumD.v:253, cold/h-s8a-number-d 18f7e2272a9, built rc=0), moved here verbatim so parse_value's
   number arm and the writer chain Require it without the piece; WalkKitK0 adopts it into the kit as fp_step_fclass.
   No image constant; no numeral other than the register/format WORDs of the decode and the pc step 4 (LENGTH).
   SPELLING: `fmt_double` (Fpu.v) is THE one spelling of the double format in this family; `Fclass FMT_D` in the
   decode position is the instruction's own field and is convertible to it (fp_format FMT_D = fmt_double). There is
   ONE notion of the format, not two. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK0o.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma fp_step_fclass_d : forall (fx : YK11.FPState) segs regs pc mem rom w rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fclass FMT_D rd rs1, 4%Z) ->
  RiscvSemantics.step segs (@YK11.mkst fx regs pc mem rom) =
  MachineOk (@YK11.mkst fx (if bv_eqb rd 0 then regs
     else YK11.regupd regs rd (Z_to_bv 64 (fp_class fmt_double (bv_unsigned (reg_get (@YK11.fp_regs fx) rs1)))))
    (YK11.v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
  fp_pipeline Hf He Hd.
  destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; destruct fx; reflexivity.
Qed.
