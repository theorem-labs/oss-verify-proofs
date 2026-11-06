(* The asan-ubsan twin of lib/A/HeadampAllocClose.v: the allocator and memcpy parts of fuzz_headamp's ASan+UBSan image
   (image B, fuzz_headamp.asan-ubsan), closed at that image's symbol table B := YD2l.TfibB: the slots
   H_ALLOC_MALLOC_U / H_ALLOC_FREE_U / H_RT_MEMCPY_U of lib/A/HeadampClose.v (Section asan_ubsan). Image B registers 43
   globals too (its asan_globals array holds 43 descriptors), so its start-up depot holds traces and its core
   (lib/AU, image A's core made into lib/AU by derive_y: YF0w, YF0q, YD2l, YD2m) is the depot-true text, as image A's.
   Each lemma is the core's theorem at TfibB, as in image A: YF0w.tfib_amalloc_realizes and YF0q.afree_realizes_closed
   (`forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> ...`) and YD2m.tfib_AICPY
   (`forall B, TfibSyms B -> ...`), with TfibSyms TfibB from YD2l.TfibB_syms and the hash premise by eq_refl.
   The same malloc and free facts feed image B's program contract (lib/AU/HPgLibU.v headamp_lib_x_all_stmt), through
   HeadampClose's H_DRIVER_U and lib/AU/YD2o.v's adapter.
   rule 24: proves no function (kind: assembly). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import YB1v YF0m YD2l.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require YF0w YF0q YD2m.
Lemma headamp_amalloc_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@YF0w.tfib_amalloc_realizes fx rc TfibB TfibB_syms (fun _ => eq_refl)). Qed.
Lemma headamp_afree_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@YF0q.afree_realizes_closed fx rc TfibB TfibB_syms (fun _ => eq_refl)). Qed.
Lemma headamp_aicpy_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc tfibsegs TfibB OCpy (pc_wrap_memcpy (as_code TfibB)).
Proof. intros rc fx. exact (YD2m.tfib_AICPY (fx:=fx) (rc:=rc) TfibB TfibB_syms). Qed.
