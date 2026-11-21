(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateSafeS1 RefInflateSafeS2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section Loop.
Variable flush : Z.

Ltac disp_at := intros [s c r] H; cbn [w_s] in H; unfold dispatch, abind, gs; cbn [w_s]; rewrite H; reflexivity.

Hypothesis A_HEAD : arm_stmt flush HEAD PC_HEAD (arm_HEAD ivar_ref).
Hypothesis A_DICTID : arm_stmt flush DICTID PC_DICTID (arm_DICTID ivar_ref flush).
Hypothesis A_DICT : arm_stmt flush DICT PC_DICT (arm_DICT ivar_ref flush).
Hypothesis A_TYPE : arm_stmt flush TYPE PC_TYPE (arm_TYPE ivar_ref flush).
Hypothesis A_TYPEDO : arm_stmt flush TYPEDO PC_TYPEDO (arm_TYPEDO ivar_ref flush).
Hypothesis A_STORED : arm_stmt flush STORED PC_STORED (arm_STORED ivar_ref flush).
Hypothesis A_COPY_ : arm_stmt flush COPY_ PC_COPY_ arm_COPY_.
Hypothesis A_COPY : arm_stmt flush COPY PC_COPY arm_COPY.
Hypothesis A_TABLE : arm_stmt flush TABLE PC_TABLE (arm_TABLE ivar_ref flush).
Hypothesis A_LENLENS : arm_stmt flush LENLENS PC_LENLENS (arm_LENLENS ivar_ref flush).
Hypothesis A_CODELENS : arm_stmt flush CODELENS PC_CODELENS (arm_CODELENS ivar_ref flush).
Hypothesis A_LEN_ : arm_stmt flush LEN_ PC_LEN_ (arm_LEN_ ivar_ref).
Hypothesis A_LEN : arm_stmt flush LEN PC_LEN (arm_LEN ivar_ref).
Hypothesis A_LENEXT : arm_stmt flush LENEXT PC_LENEXT (arm_LENEXT ivar_ref).
Hypothesis A_DIST : arm_stmt flush DIST PC_DIST (arm_DIST ivar_ref).
Hypothesis A_DISTEXT : arm_stmt flush DISTEXT PC_DISTEXT (arm_DISTEXT ivar_ref).
Hypothesis A_MATCH : arm_stmt flush MATCH PC_MATCH (arm_MATCH ivar_ref).
Hypothesis A_LIT : arm_stmt flush LIT PC_LIT arm_LIT.
Hypothesis A_CHECK : arm_stmt flush CHECK PC_CHECK arm_CHECK.
Hypothesis A_LENGTH : arm_stmt flush LENGTH PC_LENGTH arm_LENGTH.
Hypothesis A_DONE : arm_stmt flush DONE PC_DONE arm_DONE.
Hypothesis A_BAD : arm_stmt flush BAD PC_BAD arm_BAD.
Hypothesis A_MEM : arm_stmt flush MEM PC_MEM arm_MEM.

Ltac disp_case HARM HDISP EM :=
  rewrite (HDISP _ EM); rewrite EM;
  match goal with |- context [wz ?M] => first [unfold M] end;
  do 2 zs; if_true; do 6 zs;
  eapply HARM; [ eassumption | eapply ILOOP_intro; try reflexivity; eassumption | eassumption | eassumption | eassumption | eassumption | exact EM ].

Definition LPOST (X : ictx) (res : istop * iw) : machine_state -> Prop :=
  fun ms => (match fst res with SLeave => ILEAVE X (snd res) ms | SRet rc => IRET X rc (snd res) ms end)
            /\ WINV (snd res) /\ ATY (w_s (snd res)) /\ PATI X (snd res).

Definition lstep (w : iw) : iw + (istop * iw) :=
  match dispatch ivar_ref flush w with
  | ARun _ w' => inl w'
  | ALeave w' => inr (SLeave, w')
  | ARet rc w' => inr (SRet rc, w')
  end.


End Loop.
