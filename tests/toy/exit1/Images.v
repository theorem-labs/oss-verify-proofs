(** * toy / exit1: the image

    [images/Plain.v] is generated when this library is built, by the
    [elf-snapshot] tool of linux-process-semantics, from the ELF file that
    [../make_elf.py] writes and [exit1.plain.sha256] pins.  It is not stored in
    this repository.  [plain_wf] checks by computation that the image is well
    formed ([OSSVerify.Core.Images]). *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Core Require Import Images.
From OSSVerify.Tests.toy.exit1.images Require Plain.

Definition plain : Image := mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs.

Lemma plain_wf : image_wf plain.  Proof. check_image_wf. Qed.
