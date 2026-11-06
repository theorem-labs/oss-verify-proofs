(** * avahi / fuzz-domain: the two images

    Each [images/<Build>.v] is generated when this library is built, by the
    [elf-snapshot] tool of linux-process-semantics, from the ELF file that
    harness.yaml pins by SHA-256.  It is not stored in this repository.  The
    [_wf] lemmas check by computation that each image is well formed
    ([OSSVerify.Core.Images]), so that no statement about it holds only because
    the image has no valid entry. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Core Require Import Images.
From OSSVerify.avahi.fuzz_domain.images Require Plain Ubsan.

Definition plain : Image := mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs.
Definition ubsan : Image := mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs.

Lemma plain_wf : image_wf plain.  Proof. check_image_wf. Qed.
Lemma ubsan_wf : image_wf ubsan.  Proof. check_image_wf. Qed.
