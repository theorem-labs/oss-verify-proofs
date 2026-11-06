(* Theorem Labs, 2026-10: the image-B twin of lib/A/RoleAllocClose.v of this library, for reac-pw/fuzz_role's
   asan-ubsan image: module names A.Axyz -> AU.Yxyz, lemma names role_* -> role_*_U, the same proofs. *)
(* The allocator and memcpy parts of fuzz_role's asan-ubsan image (image B), closed at the image's symbol table
   B_U := YD2l.TfibB: the slots H_ALLOC_MALLOC_U / H_ALLOC_FREE_U / H_RT_MEMCPY_U of lib/A/RoleClose.v (Section
   asan_ubsan). Image B's core (lib/AU, derived from image A's) carries the same depot-true texts as image A's: each
   lemma applied is `forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> ...` (lib/AU/YF0w.v
   tfib_amalloc_realizes, lib/AU/YF0q.v afree_realizes_closed) or `forall B, TfibSyms B -> ...` (lib/AU/YD2m.v
   tfib_AICPY), with TfibSyms TfibB from YD2l.TfibB_syms and the hash premise by eq_refl (TfibB's as_dhash field is
   tfib_dhash).
   The same malloc and free facts feed the entry function's program contract (lib/AU/RPgLibX.v role_lib_x_all),
   through RoleClose's H_DRIVER_U and lib/AU/YD2o.v's adapter.
   rule 24: proves no function (kind: assembly). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import YB1v YF0m YD2l.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require YF0w YF0q YD2m.
Lemma role_amalloc_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@YF0w.tfib_amalloc_realizes fx rc TfibB TfibB_syms (fun _ => eq_refl)). Qed.
Lemma role_afree_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@YF0q.afree_realizes_closed fx rc TfibB TfibB_syms (fun _ => eq_refl)). Qed.
Lemma role_aicpy_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc tfibsegs TfibB OCpy (pc_wrap_memcpy (as_code TfibB)).
Proof. intros rc fx. exact (YD2m.tfib_AICPY (fx:=fx) (rc:=rc) TfibB TfibB_syms). Qed.
