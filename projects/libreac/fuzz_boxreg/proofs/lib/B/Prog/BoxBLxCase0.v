(* Case op & 3 = 0 (declare, fuzz_boxreg.c:213-286) of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput
   (fuzz_boxreg.asan-ubsan 0x8034c .. 0x80b08): the phase from the cut LI_T 0 to the cut LI_K of BoxBLxDefs.v,
   composed from the case's segments (cuts in BoxBLxCase0Defs.v):
     LI_T 0 --c0tn--> C0_N --c0_n--> { C0_RF --c0_rf--> C0_W ; C0_L 0 --c0_loop--> C0_W ; C0_W }
     C0_W --c0_w (reac_boxreg_declare, returns at some fx')--> C0_D at fx'
     C0_D --c0_d--> { C0_BC --c0_bc--> C0_SC --c0_sc--> C0_F ; C0_F } --c0_f--> C0_FR --c0_fr--> LI_K at fx'.
   reac_boxreg_declare reaches the snprintf wrapper, whose post returns at SOME FP state fx' with lx_fxr fx fx'
   (BoxBLxDefs.v); every segment after it is taken at fx' (c0_after_D), with the walk's hypotheses at fx' (HYF). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YM05 YI16 YA0n YG0f YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBList BoxBPa BoxBLxDefs BoxBLxCase0Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require BoxBLxCase0TN BoxBLxCase0N BoxBLxCase0RF
  BoxBLxCase0L BoxBLxCase0W BoxBLxCase0D BoxBLxCase0BC BoxBLxCase0SC BoxBLxCase0F BoxBLxCase0FR.

Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HYF : forall fx' : YK11.FPState, lx_hyps (fx := fx') B MT.

(* After reac_boxreg_declare returned, at any FP state fx': D -> (refused) F, or (placed) BC -> SC -> F; then
   F -> FR -> K. *)
Lemma c0_after_D : forall (fx' : YK11.FPState) (POST : lxcx -> world SEGS -> config -> Prop) i,
  lx_from B MT POST (LI_K (fx := fx') B MT i) -> lx_from B MT POST (C0_D (fx := fx') B MT i).
Proof.
  intros fx' POST i HK.
  pose proof (BoxBLxCase0FR.c0_fr (fx := fx') B MT (HYF fx') POST i HK) as HFR.
  pose proof (BoxBLxCase0F.c0_f (fx := fx') B MT (HYF fx') POST i HFR) as HF.
  pose proof (BoxBLxCase0SC.c0_sc (fx := fx') B MT (HYF fx') POST i HF) as HSC.
  pose proof (BoxBLxCase0BC.c0_bc (fx := fx') B MT (HYF fx') POST i HSC) as HBC.
  exact (BoxBLxCase0D.c0_d (fx := fx') B MT (HYF fx') POST i HF HBC).
Qed.

Theorem lx_case0 : forall (POST : lxcx -> world SEGS -> config -> Prop) i,
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  (forall fx' : YK11.FPState, lx_fxr fx fx' -> lx_from B MT POST (LI_K (fx := fx') B MT i)) ->
  lx_from B MT POST (LI_T B MT 0 i).
Proof.
  intros POST i HRM HK.
  pose proof (HYF fx) as HY.
  assert (HW : lx_from B MT POST (C0_W B MT i)).
  { apply (BoxBLxCase0W.c0_w B MT HY POST i HRM). intros fx' Hfx. exact (c0_after_D fx' POST i (HK fx' Hfx)). }
  apply (BoxBLxCase0TN.c0tn B MT HY POST i).
  exact (BoxBLxCase0N.c0_n B MT HY POST i HW (BoxBLxCase0RF.c0_rf B MT HY POST i HW)
           (BoxBLxCase0L.c0_loop B MT HY POST i HW 0)).
Qed.

End a.
