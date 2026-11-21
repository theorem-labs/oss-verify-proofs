(** [X]: the memory image of the classifier program that the texts of this proof library use.
    It is an alias of the repository's image [OSSVerify.zlib.zlib_uncompress2_fuzzer.images.ClassifierAUbsan], which the build makes from the
    classifier ELF file that harness.yaml pins.  This file defines nothing new. *)
From OSSVerify.zlib.zlib_uncompress2_fuzzer.images Require ClassifierAUbsan.
Module M := ClassifierAUbsan.M.
Notation X_init_pc := ClassifierAUbsan.ClassifierAUbsan_init_pc (only parsing).
Notation X_loaded_segments := ClassifierAUbsan.ClassifierAUbsan_loaded_segments (only parsing).
Notation X_phdrs := ClassifierAUbsan.ClassifierAUbsan_phdrs (only parsing).
Notation X_seg_bytes_000 := ClassifierAUbsan.ClassifierAUbsan_seg_bytes_000 (only parsing).
Notation X_seg_bytes_001 := ClassifierAUbsan.ClassifierAUbsan_seg_bytes_001 (only parsing).
Notation X_seg_bytes_002 := ClassifierAUbsan.ClassifierAUbsan_seg_bytes_002 (only parsing).
Notation X_seg_bytes_003 := ClassifierAUbsan.ClassifierAUbsan_seg_bytes_003 (only parsing).
Notation X_segment_000 := ClassifierAUbsan.ClassifierAUbsan_segment_000 (only parsing).
Notation X_segment_001 := ClassifierAUbsan.ClassifierAUbsan_segment_001 (only parsing).
Notation X_segment_002 := ClassifierAUbsan.ClassifierAUbsan_segment_002 (only parsing).
Notation X_segment_003 := ClassifierAUbsan.ClassifierAUbsan_segment_003 (only parsing).
