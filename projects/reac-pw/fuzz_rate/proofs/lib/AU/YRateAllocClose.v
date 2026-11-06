(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RoleAllocClose.v at fa745625e7df, for reac-pw/fuzz_rate
   image A: fuzz_rate's descriptor count; names role_* -> rate_*; module paths changed. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import YB1v YF0m YD2l.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require YF0w YF0q YD2m.
Lemma rate_amalloc_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@YF0w.tfib_amalloc_realizes fx rc TfibB TfibB_syms (fun _ => eq_refl)). Qed.
Lemma rate_afree_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@YF0q.afree_realizes_closed fx rc TfibB TfibB_syms (fun _ => eq_refl)). Qed.
Lemma rate_aicpy_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc tfibsegs TfibB OCpy (pc_wrap_memcpy (as_code TfibB)).
Proof. intros rc fx. exact (YD2m.tfib_AICPY (fx:=fx) (rc:=rc) TfibB TfibB_syms). Qed.
