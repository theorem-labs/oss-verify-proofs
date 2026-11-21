(** * zlib / example_flush_fuzzer: the fourteen images

    Each [images/<Build>.v] is generated when this library is built, by the
    [elf-snapshot] tool of linux-process-semantics, from the ELF file that
    harness.yaml pins by SHA-256.  It is not stored in this repository.  The
    [_wf] lemmas check by computation that each image is well formed
    ([OSSVerify.Core.Images]), so that no statement about it holds only because
    the image has no valid entry. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Core Require Import Images.
From OSSVerify.zlib.example_flush_fuzzer.images Require Plain Ubsan Asan AsanUbsan PlainOriginal UbsanOriginal AsanOriginal AsanUbsanOriginal ClassifierAUbsan ClassifierBUbsan ClassifierAAsan ClassifierBAsan ClassifierAAsanUbsan ClassifierBAsanUbsan.

Definition plain : Image := mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs.
Definition ubsan : Image := mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs.
Definition asan : Image := mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Definition asan_ubsan : Image := mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Definition plain_original : Image := mkImage PlainOriginal.M.loaded_segments PlainOriginal.M.init_pc PlainOriginal.M.phdrs.
Definition ubsan_original : Image := mkImage UbsanOriginal.M.loaded_segments UbsanOriginal.M.init_pc UbsanOriginal.M.phdrs.
Definition asan_original : Image := mkImage AsanOriginal.M.loaded_segments AsanOriginal.M.init_pc AsanOriginal.M.phdrs.
Definition asan_ubsan_original : Image := mkImage AsanUbsanOriginal.M.loaded_segments AsanUbsanOriginal.M.init_pc AsanUbsanOriginal.M.phdrs.
Definition classifier_a_ubsan : Image := mkImage ClassifierAUbsan.M.loaded_segments ClassifierAUbsan.M.init_pc ClassifierAUbsan.M.phdrs.
Definition classifier_b_ubsan : Image := mkImage ClassifierBUbsan.M.loaded_segments ClassifierBUbsan.M.init_pc ClassifierBUbsan.M.phdrs.
Definition classifier_a_asan : Image := mkImage ClassifierAAsan.M.loaded_segments ClassifierAAsan.M.init_pc ClassifierAAsan.M.phdrs.
Definition classifier_b_asan : Image := mkImage ClassifierBAsan.M.loaded_segments ClassifierBAsan.M.init_pc ClassifierBAsan.M.phdrs.
Definition classifier_a_asan_ubsan : Image := mkImage ClassifierAAsanUbsan.M.loaded_segments ClassifierAAsanUbsan.M.init_pc ClassifierAAsanUbsan.M.phdrs.
Definition classifier_b_asan_ubsan : Image := mkImage ClassifierBAsanUbsan.M.loaded_segments ClassifierBAsanUbsan.M.init_pc ClassifierBAsanUbsan.M.phdrs.

Lemma plain_wf : image_wf plain.  Proof. check_image_wf. Qed.
Lemma ubsan_wf : image_wf ubsan.  Proof. check_image_wf. Qed.
Lemma asan_wf : image_wf asan.  Proof. check_image_wf. Qed.
Lemma asan_ubsan_wf : image_wf asan_ubsan.  Proof. check_image_wf. Qed.
Lemma plain_original_wf : image_wf plain_original.  Proof. check_image_wf. Qed.
Lemma ubsan_original_wf : image_wf ubsan_original.  Proof. check_image_wf. Qed.
Lemma asan_original_wf : image_wf asan_original.  Proof. check_image_wf. Qed.
Lemma asan_ubsan_original_wf : image_wf asan_ubsan_original.  Proof. check_image_wf. Qed.
Lemma classifier_a_ubsan_wf : image_wf classifier_a_ubsan.  Proof. check_image_wf. Qed.
Lemma classifier_b_ubsan_wf : image_wf classifier_b_ubsan.  Proof. check_image_wf. Qed.
Lemma classifier_a_asan_wf : image_wf classifier_a_asan.  Proof. check_image_wf. Qed.
Lemma classifier_b_asan_wf : image_wf classifier_b_asan.  Proof. check_image_wf. Qed.
Lemma classifier_a_asan_ubsan_wf : image_wf classifier_a_asan_ubsan.  Proof. check_image_wf. Qed.
Lemma classifier_b_asan_ubsan_wf : image_wf classifier_b_asan_ubsan.  Proof. check_image_wf. Qed.
