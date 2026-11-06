(** * yoga / fuzz_layout: the two images

    Each [images/<Build>.v] is generated when this library is built, by the
    [elf-snapshot] tool of linux-process-semantics, from the ELF file that
    harness.yaml pins by SHA-256.  It is not stored in this repository.  The
    [_wf] lemmas check by computation that each image is well formed
    ([OSSVerify.Core.Images]), so that no statement about it holds only because
    the image has no valid entry. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Core Require Import Images.
From OSSVerify.yoga.fuzz_layout.images Require Plain Asan.

Definition plain : Image := mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs.
Definition asan : Image := mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.

Lemma plain_wf : image_wf plain.  Proof. check_image_wf. Qed.
Lemma asan_wf : image_wf asan.  Proof. check_image_wf. Qed.
