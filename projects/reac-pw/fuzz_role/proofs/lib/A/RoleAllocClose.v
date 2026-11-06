(* The allocator and memcpy parts of fuzz_role's ASan image (image A), closed at the image's symbol table
   B := AD2l.TfibB: the slots H_ALLOC_MALLOC / H_ALLOC_FREE / H_RT_MEMCPY of lib/A/RoleClose.v (Section asan). fuzz_role's
   start-up depot holds traces (49 registered globals; depot_has_trace = true), so the AF0w / AF0q / AD2l / AD2m these
   lemmas apply are the relocated depot-true texts (libreac/fuzz_scene's, origin/ossv/recipes 6ebe35ba632; the same
   applications as fuzz_scene's lib/A/SceneAlloc.v and libreac/fuzz_ctrl's lib/A/CtrlClose.v:144-146): each lemma is
   `forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> ...` (AF0w.v:45 tfib_amalloc_realizes,
   AF0q.v:13 afree_realizes_closed) or `forall B, TfibSyms B -> ...` (AD2m.v:17 tfib_AICPY), with TfibSyms TfibB from
   AD2l.TfibB_syms and the hash premise by eq_refl (TfibB's as_dhash field is tfib_dhash).
   The same malloc and free facts feed the entry function's program contract (lib/A/RPgLib.v role_lib_x_all), through
   RoleClose's H_DRIVER and lib/A/AD2o.v's adapter.
   rule 24: proves no function (kind: assembly). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import AB1v AF0m AD2l.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require AF0w AF0q AD2m.
Lemma role_amalloc_closed : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@AF0w.tfib_amalloc_realizes fx rc TfibB TfibB_syms (fun _ => eq_refl)). Qed.
Lemma role_afree_closed : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@AF0q.afree_realizes_closed fx rc TfibB TfibB_syms (fun _ => eq_refl)). Qed.
Lemma role_aicpy_closed : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc tfibsegs TfibB OCpy (pc_wrap_memcpy (as_code TfibB)).
Proof. intros rc fx. exact (AD2m.tfib_AICPY (fx:=fx) (rc:=rc) TfibB TfibB_syms). Qed.
