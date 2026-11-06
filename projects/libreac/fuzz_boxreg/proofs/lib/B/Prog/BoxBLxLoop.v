(* The loop of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput (at most 64 turns, BoxBLxDefs.v's cuts): from the
   phase lemmas of the loop head (J -> X or a case entry T), the four cases (T -> K) and the turn's end (K -> the
   next head or X), every loop head reaches the post-condition, by induction on the turns left.
   A cut is taken at the FP state of the run (BoxBLxDefs.v lx_fxr): the cases that call reac_boxreg_declare (case 0)
   or reac_boxreg_set_name (case 3) reach K at some fx' with lx_fxr fx fx'; the loop carries lx_fxr fx0 fx from the
   entry's fx0. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK15 YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBLxDefs.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable POST : lxcx -> world (@pa_segs _ boxb_listing PI) -> config -> Prop.
Variable fx0 : YK11.FPState.
Hypothesis RTOP : forall (fx : YK11.FPState) i, lx_fxr fx0 fx ->
  (forall c, 0 <= c < 4 -> lx_from B MT POST (LI_T (fx := fx) B MT c i)) -> lx_from B MT POST (LI_J (fx := fx) B MT i).
Hypothesis RCASE : forall (fx : YK11.FPState) c i, lx_fxr fx0 fx -> 0 <= c < 4 ->
  (forall fx' : YK11.FPState, lx_fxr fx fx' -> lx_from B MT POST (LI_K (fx := fx') B MT i)) ->
  lx_from B MT POST (LI_T (fx := fx) B MT c i).
Hypothesis RJOIN : forall (fx : YK11.FPState) i, lx_fxr fx0 fx ->
  lx_from B MT POST (LI_J (fx := fx) B MT (S i)) -> lx_from B MT POST (LI_K (fx := fx) B MT i).

(* No loop head is past the 64th turn. *)
Lemma lx_J_past : forall (fx : YK11.FPState) i, (64 <= i)%nat -> lx_from B MT POST (LI_J (fx := fx) B MT i).
Proof.
  intros fx i Hi cx fp k acc ly3 S3 W3 ms3 md3 _ _ _ _ (pos & r & fab & bs & _ & Hlt & _). exfalso. lia.
Qed.

Theorem lx_loop : forall (fx : YK11.FPState) i, lx_fxr fx0 fx -> lx_from B MT POST (LI_J (fx := fx) B MT i).
Proof.
  assert (H : forall n (fx : YK11.FPState) i, lx_fxr fx0 fx -> (64 - n <= i)%nat ->
    lx_from B MT POST (LI_J (fx := fx) B MT i)).
  { induction n as [|n IH]; intros fx i Hfx Hi.
    - apply lx_J_past. lia.
    - destruct (Nat.le_gt_cases (64 - n) i) as [Hle | Hgt]; [exact (IH fx i Hfx Hle)|].
      apply (RTOP fx i Hfx). intros c Hc. apply (RCASE fx c i Hfx Hc). intros fx' Hfx'.
      pose proof (lx_fxr_trans fx0 fx fx' Hfx Hfx') as H0'.
      apply (RJOIN fx' i H0'). apply (IH fx' (S i) H0'). lia. }
  intros fx i Hfx. apply (H 64%nat fx i Hfx). lia.
Qed.

End a.
