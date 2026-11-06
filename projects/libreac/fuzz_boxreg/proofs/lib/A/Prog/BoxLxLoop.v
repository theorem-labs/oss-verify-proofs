(* The operation loop of fuzz_boxreg's LLVMFuzzerTestOneInput (ASan build), composed from its phases: from the
   phase lemmas of the head (J -> T / X), the four cases (T -> K), the join (K -> J / X) and the exit (X -> the
   post-condition), the loop head J holds for every turn i, by induction on the turns left (at most 64,
   fuzz_boxreg.c:204). The cuts are lib/A/Prog/BoxLxDefs.v's.
   The FP state: a case that calls reac_boxreg_declare or reac_boxreg_set_name (their posts are apost_baseF, the
   snprintf wrapper's FP-existential return) lands at a related FP state fx' (BoxLxDefs.v lx_fxr), so every phase
   lemma below is quantified over the FP state it runs at, and the loop carries lx_fxr from the entry's fx0. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK15 YK18 YK0s YP09 YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym BoxSyms BoxList BoxPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section a. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg box_listing}.
Variable fx0 : YK11.FPState.
Variable B : asyms.
Variable MT : ameter_ops.
Variable POST : bcx -> world pa_segs -> config -> Prop.

Hypothesis HEAD : forall (fx : YK11.FPState) i,
  (forall op3, 0 <= op3 < 4 -> gb_from B MT POST (GI_T (fx := fx) B MT op3 i)) ->
  gb_from B MT POST (GI_X (fx := fx) B MT) -> gb_from B MT POST (GI_J (fx := fx) B MT i).
(* A case runs at an FP state related to the entry's (it may need the entry's fcsr facts, kept by lx_fxr). *)
Hypothesis CASE : forall (fx : YK11.FPState) op3 i, lx_fxr fx0 fx -> 0 <= op3 < 4 ->
  (forall fx' : YK11.FPState, lx_fxr fx fx' -> gb_from B MT POST (GI_K (fx := fx') B MT i)) ->
  gb_from B MT POST (GI_T (fx := fx) B MT op3 i).
Hypothesis JOIN : forall (fx : YK11.FPState) i,
  (i + 1 < 64 -> gb_from B MT POST (GI_J (fx := fx) B MT (i + 1))) ->
  gb_from B MT POST (GI_X (fx := fx) B MT) -> gb_from B MT POST (GI_K (fx := fx) B MT i).
Hypothesis EXIT : forall fx : YK11.FPState, lx_fxr fx0 fx -> gb_from B MT POST (GI_X (fx := fx) B MT).

(* A loop head past the last turn is never reached: GI_J asks for i < 64. *)
Lemma gb_from_J_out : forall (fx : YK11.FPState) i, 64 <= i -> gb_from B MT POST (GI_J (fx := fx) B MT i).
Proof.
  intros fx i Hi cx fp k acc ly3 S3 W3 ms3 md3 _ _ _ _ (r & bs & pos & _ & Hi64 & _). lia.
Qed.

Lemma gb_loop_n : forall (m : nat) (fx : YK11.FPState) i, lx_fxr fx0 fx -> 64 - i <= Z.of_nat m ->
  gb_from B MT POST (GI_J (fx := fx) B MT i).
Proof.
  induction m as [|m IH]; intros fx i HR Hm.
  - apply gb_from_J_out. lia.
  - apply HEAD; [|exact (EXIT fx HR)].
    intros op3 Hop3. apply (CASE fx op3 i HR Hop3). intros fx' HR'.
    pose proof (lx_fxr_trans fx0 fx fx' HR HR') as HR0.
    apply JOIN; [|exact (EXIT fx' HR0)].
    intros _. apply IH; [exact HR0 | lia].
Qed.

Theorem gb_loop : forall i, gb_from B MT POST (GI_J (fx := fx0) B MT i).
Proof. intros i. apply (gb_loop_n (Z.to_nat (64 - i)) fx0 i (lx_fxr_refl fx0)). lia. Qed.

End a.
