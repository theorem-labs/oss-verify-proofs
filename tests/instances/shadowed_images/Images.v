(* NEGATIVE CONTROL, with Instances/plain_halts.v: a file of the proof
   library with the name of the harness's Images.  The library is
   Control.shadowed_images, so this module is Control.shadowed_images.Images.
   Its plain is the plain image of the exit1 toy, not that of the exit0 toy.
   A wrapper that resolves Images.plain after it loads the lemma's library
   would take this plain, and the lemma about the exit1 image would pass. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Core Require Import Images.
From OSSVerify.Tests.toy.exit1 Require Images.

Definition plain : Image := OSSVerify.Tests.toy.exit1.Images.plain.

Lemma plain_wf : image_wf plain.
Proof. exact OSSVerify.Tests.toy.exit1.Images.plain_wf. Qed.
