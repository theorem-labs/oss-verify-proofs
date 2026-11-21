(** [X]: the memory image of the classifier program that the texts of this proof library use.
    It is an alias of the repository's image [OSSVerify.zlib.zlib_uncompress_fuzzer.images.ClassifierAAsanUbsan], which the build makes from the
    classifier ELF file that harness.yaml pins.  This file defines nothing new. *)
From OSSVerify.zlib.zlib_uncompress_fuzzer.images Require ClassifierAAsanUbsan.
Module M := ClassifierAAsanUbsan.M.
Notation X_init_pc := ClassifierAAsanUbsan.ClassifierAAsanUbsan_init_pc (only parsing).
Notation X_loaded_segments := ClassifierAAsanUbsan.ClassifierAAsanUbsan_loaded_segments (only parsing).
Notation X_phdrs := ClassifierAAsanUbsan.ClassifierAAsanUbsan_phdrs (only parsing).
Notation X_seg_bytes_000 := ClassifierAAsanUbsan.ClassifierAAsanUbsan_seg_bytes_000 (only parsing).
Notation X_seg_bytes_001 := ClassifierAAsanUbsan.ClassifierAAsanUbsan_seg_bytes_001 (only parsing).
Notation X_seg_bytes_002 := ClassifierAAsanUbsan.ClassifierAAsanUbsan_seg_bytes_002 (only parsing).
Notation X_seg_bytes_003 := ClassifierAAsanUbsan.ClassifierAAsanUbsan_seg_bytes_003 (only parsing).
Notation X_segment_000 := ClassifierAAsanUbsan.ClassifierAAsanUbsan_segment_000 (only parsing).
Notation X_segment_001 := ClassifierAAsanUbsan.ClassifierAAsanUbsan_segment_001 (only parsing).
Notation X_segment_002 := ClassifierAAsanUbsan.ClassifierAAsanUbsan_segment_002 (only parsing).
Notation X_segment_003 := ClassifierAAsanUbsan.ClassifierAAsanUbsan_segment_003 (only parsing).
