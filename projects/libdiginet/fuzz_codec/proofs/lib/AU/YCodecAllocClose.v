(* The image-B twin of lib/A/CodecAllocClose.v, at lib/AU/YD2l.v's TfibB. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YM05 YG00 YG0f YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YF0m YD2l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YF0w YF0q YD2m.
Lemma codec_amalloc_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@YF0w.tfib_amalloc_realizes fx rc TfibB (proj2 TfibB_pair) (fun t => eq_refl)). Qed.
Lemma codec_afree_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc tfibsegs TfibB.
Proof. intros rc fx. exact (@YF0q.afree_realizes_closed fx rc TfibB (proj2 TfibB_pair) (fun t => eq_refl)). Qed.
Lemma codec_aicpy_closed_U : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc tfibsegs TfibB OCpy (pc_wrap_memcpy (as_code TfibB)).
Proof. intros rc fx. exact (YD2m.tfib_AICPY (fx:=fx) (rc:=rc) TfibB (proj2 TfibB_pair)). Qed.
