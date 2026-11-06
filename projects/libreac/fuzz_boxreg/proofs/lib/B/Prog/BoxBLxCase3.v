(* Case 3 of a loop turn of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput (op & 3 = 3, `rename`): from the cut LI_T
   (0x8034c) to the cut LI_K (0x80b08), composed from its four segments (BoxBLxCase3Defs.v c3_segA_ok .. c3_segD_ok):
     A  LI_T -> C3_RN    the switch, the inlined fuzz_u8, read_name             BoxBLxCase3SegA.v c3_segA  (at fx)
     B  C3_RN -> C3_SN   the name argument, reac_boxreg_set_name (cross-call)   BoxBLxCase3SegB.v c3_segB  (fx -> fx')
     C  C3_SN -> C3_FREE renamed, the UBSan checks, strncmp                     BoxBLxCase3SegC.v c3_segC  (at fx')
     D  C3_FREE -> LI_K  free (name), s8 = renamed, the jump to the join        BoxBLxCase3SegD.v c3_segD  (at fx')
   set_name may reach the snprintf wrapper, which returns at some FP state fx' with lx_fxr fx fx' (BoxBase.v
   apost_baseF), so segments C and D run at fx' and the walk's facts are taken as HYF at every FP state (a Theorem Labs lane,
   05:37Z: the glue passes `fun fx' => @lx_hyps_boxb fx'`). The statement is a Theorem Labs lane's, verbatim.
   rule 24: proves no function (kind: segment composition of the LLVMFuzzerTestOneInput walk; every callee is an
   lx_hyps field). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase3Defs
  BoxBLxCase3SegA BoxBLxCase3SegB BoxBLxCase3SegC BoxBLxCase3SegD.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HYF : forall fx' : YK11.FPState, lx_hyps (fx := fx') B MT.

Theorem lx_case3 : forall (POST : lxcx -> world SEGS -> config -> Prop) i,
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  (forall fx' : YK11.FPState, lx_fxr fx fx' -> lx_from B MT POST (LI_K (fx := fx') B MT i)) ->
  lx_from B MT POST (LI_T B MT 3 i).
Proof using HYF.
  intros POST i HRM HK.
  apply (@c3_segA fx rc SK PI B MT (HYF fx) POST i).
  apply (@c3_segB fx rc SK PI B MT (HYF fx) POST i HRM).
  intros fx' Hr.
  apply (@c3_segC fx' rc SK PI B MT (HYF fx') POST i).
  apply (@c3_segD fx' rc SK PI B MT (HYF fx') POST i).
  exact (HK fx' Hr).
Qed.

End a.
