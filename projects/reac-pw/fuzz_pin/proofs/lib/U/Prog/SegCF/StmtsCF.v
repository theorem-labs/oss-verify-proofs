(* The segment statements of reac-pw/fuzz_pin LLVMFuzzerTestOneInput (UBSan) over the cut-free invariants
   U/Prog/SlotInvCF.v: Section Stmts of U/Prog/LLVMFuzzerTestOneInput_c.v, word for word (S_E01, S_M01, S_X01 at the
   cuts ENTRY -> K12d50 -> K12e24 -> RET, seg_lemmas), with Hcut and the cut invariants read from SlotInvCF (SR :=
   SRcf). The middle segment's evt (pin_mid_contract) and the other definitions of LLVMFuzzerTestOneInput_c.v do not
   mention SR and are used from there. Statement text only. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import SlotInvCF.
Import ListNotations.
Open Scope Z_scope.

Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Definition S_E01 : Prop :=
  Hcut B APIf ra (Inv_K12d50 B APIf ra empty) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Definition S_M01 : Prop :=
  Hcut B APIf ra (Inv_K12e24 B APIf ra empty) -> Hcut B APIf ra (Inv_K12d50 B APIf ra empty).
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K12e24 B APIf ra empty).

Definition seg_lemmas : Prop := S_E01 /\ S_M01 /\ S_X01.

End Stmts.
