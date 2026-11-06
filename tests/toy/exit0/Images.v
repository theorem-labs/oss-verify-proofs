(** * toy / exit0: the two images

    [images/Plain.v] and [images/Padded.v] are generated when this library is
    built, by the [elf-snapshot] tool of linux-process-semantics, from the ELF
    files that [../make_elf.py] writes and [exit0.plain.sha256] and
    [exit0.padded.sha256] pin.  They are not stored in this repository.  The
    [_wf] lemmas check by computation that each image is well formed
    ([OSSVerify.Core.Images]). *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Core Require Import Images.
From OSSVerify.Tests.toy.exit0.images Require Plain Padded.

Definition plain  : Image := mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs.
Definition padded : Image := mkImage Padded.M.loaded_segments Padded.M.init_pc Padded.M.phdrs.

Lemma plain_wf  : image_wf plain.   Proof. check_image_wf. Qed.
Lemma padded_wf : image_wf padded.  Proof. check_image_wf. Qed.
