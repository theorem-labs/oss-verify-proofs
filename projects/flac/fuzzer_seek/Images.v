(** * flac / fuzzer_seek: the four images

    Each [images/<Build>.v] is generated when this library is built, by the
    [elf-snapshot] tool of linux-process-semantics, from the ELF file that
    harness.yaml pins by SHA-256.  It is not stored in this repository.  The
    [_wf] lemmas check by computation that each image is well formed
    ([OSSVerify.Core.Images]), so that no statement about it holds only because
    the image has no valid entry. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Core Require Import Images.
From OSSVerify.flac.fuzzer_seek.images Require Plain Ubsan Asan AsanUbsan.

Definition plain : Image := mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs.
Definition ubsan : Image := mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs.
Definition asan : Image := mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Definition asan_ubsan : Image := mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.

Lemma plain_wf : image_wf plain.  Proof. check_image_wf. Qed.
Lemma ubsan_wf : image_wf ubsan.  Proof. check_image_wf. Qed.
Lemma asan_wf : image_wf asan.  Proof. check_image_wf. Qed.
Lemma asan_ubsan_wf : image_wf asan_ubsan.  Proof. check_image_wf. Qed.
