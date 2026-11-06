(* The allocator and memcpy parts of the image-A driver at the start-up record TfibB (lib/A/AD2l.v): the relocated core's
   theorems at TfibB, as projects/libreac/fuzz_knock/proofs/lib/A/KnockAllocClose.v states them. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 AF0m AD2l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AF0w AF0q AD2m.
Lemma codec_amalloc_closed : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@AF0w.tfib_amalloc_realizes fx rc TfibB (proj2 TfibB_pair) (fun t => eq_refl)). Qed.
Lemma codec_afree_closed : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@AF0q.afree_realizes_closed fx rc TfibB (proj2 TfibB_pair) (fun t => eq_refl)). Qed.
Lemma codec_aicpy_closed : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc tfibsegs TfibB OCpy (pc_wrap_memcpy (as_code TfibB)).
Proof. intros rc fx. exact (AD2m.tfib_AICPY (fx:=fx) (rc:=rc) TfibB (proj2 TfibB_pair)). Qed.
