(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_defs Od_plus Od_head.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section Loop.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis HLAST : tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation n := (o_n E).

  Hypothesis ARM_STR  : arm_stmt E 0x27870.
  Hypothesis ARM_BOOL : arm_stmt E 0x27898.
  Hypothesis ARM_ARR  : arm_stmt E 0x276d4.
  Hypothesis ARM_I64  : arm_stmt E 0x27734.
  Hypothesis ARM_DBL  : arm_stmt E 0x277e0.
  Hypothesis ARM_OBJ  : arm_stmt E 0x27924.
  Hypothesis ARM_U64  : arm_stmt E 0x2794c.
  Hypothesis ARM_RAW  : arm_stmt E 0x27a64.
  Hypothesis ARM_NULL : arm_stmt E 0x27a04.
  Hypothesis ARM_NEST : arm_stmt E 0x27710.

  Theorem od_loop : forall (Q : machine_state -> Prop), od_exit_k E Q ->
    forall (fuel : nat) st0 st xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1,
    (o_left idxs st <= Z.of_nat fuel)%Z -> od_head_pre E st0 st -> frm0 xfc -> ODINV E st m1 ->
    evt psegs Q (ODST E OD_HEAD xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1).
  Proof using OK HLAST ARM_STR ARM_BOOL ARM_ARR ARM_I64 ARM_DBL ARM_OBJ ARM_U64 ARM_RAW ARM_NULL ARM_NEST.
    intros Q KX fuel. induction fuel as [|f IH]; intros st0 st xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1 HF PRE FRM INV.
    all: apply (od_head E OK HLAST ARM_STR ARM_BOOL ARM_ARR ARM_I64 ARM_DBL ARM_OBJ ARM_U64 ARM_RAW ARM_NULL ARM_NEST
                        Q st0 st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 PRE FRM INV KX).
    all: intros st' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' AO F' I'.
    all: apply (od_plus_top E OK HLAST Q st st' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' AO F' I').
    all: intros st'' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m'' PRE'' F'' I''.
    all: destruct PRE'' as [NX|DEAD];
         [| eapply (od_head_exit E OK Q st''); [destruct DEAD as (_ & DD & _); lia| exact F''| exact I''| exact KX]].
    all: pose proof NX as (A1 & _); destruct AO as [AP _]; unfold o_left in *.
    - exfalso. lia.
    - apply (IH st' st''); [lia| left; exact NX| exact F''| exact I''].
  Qed.
End Loop.
