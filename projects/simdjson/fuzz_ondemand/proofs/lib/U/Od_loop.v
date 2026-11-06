(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_defs Od_plus Od_head.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section Loop.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis OKU : od_oku E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Hypothesis ARM_STR  : arm_stmt E 0x27ab4.
  Hypothesis ARM_BOOL : arm_stmt E 0x27af4.
  Hypothesis ARM_ARR  : arm_stmt E 0x27884.
  Hypothesis ARM_I64  : arm_stmt E 0x27a74.
  Hypothesis ARM_DBL  : arm_stmt E 0x279b0.
  Hypothesis ARM_OBJ  : arm_stmt E 0x27a00.
  Hypothesis ARM_U64  : arm_stmt E 0x27b34.
  Hypothesis ARM_RAW  : arm_stmt E 0x27b74.
  Hypothesis ARM_NULL : arm_stmt E 0x27bb4.
  Hypothesis ARM_NEST : arm_stmt E 0x2793c.

  Theorem od_loop : forall (Q : machine_state -> Prop), od_exit_k E Q ->
    forall (fuel : nat) st0 st v216 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    (o_left idxs st <= Z.of_nat fuel)%Z -> od_head_pre E st0 st -> frm0 xfc -> ODINVv E v216 st m1 ->
    evt usegs Q (ODST E OD_HEAD xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 1) (Z_to_bv 64 1) xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU HLAST ARM_STR ARM_BOOL ARM_ARR ARM_I64 ARM_DBL ARM_OBJ ARM_U64 ARM_RAW ARM_NULL ARM_NEST.
    intros Q KX fuel. induction fuel as [|f IH]; intros st0 st v216 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HF PRE FRM INV.
    all: apply (od_head E OK OKU HLAST ARM_STR ARM_BOOL ARM_ARR ARM_I64 ARM_DBL ARM_OBJ ARM_U64 ARM_RAW ARM_NULL ARM_NEST
                        Q st0 st v216 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 PRE FRM INV KX).
    all: intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' AO F' I'.
    all: apply (od_plus_top E OK OKU HLAST Q st st' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' AO F' I').
    all: intros st'' v216' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m'' PRE'' F'' I''.
    all: destruct PRE'' as [NX|DEAD];
         [| eapply (od_head_exit E OK Q st'' v216'); [destruct DEAD as (_ & DD & _); lia| exact F''| exact I''| exact KX]].
    all: pose proof NX as (A1 & _); destruct AO as [AP _]; unfold o_left in *.
    - exfalso. lia.
    - apply (IH st' st'' v216'); [lia| left; exact NX| exact F''| exact I''].
  Qed.
End Loop.
