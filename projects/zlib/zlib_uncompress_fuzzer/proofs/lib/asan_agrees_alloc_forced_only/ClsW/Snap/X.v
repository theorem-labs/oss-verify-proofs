(** [X]: the memory image of the classifier program that the texts of this proof library use.
    It is an alias of the repository's image [OSSVerify.zlib.zlib_uncompress_fuzzer.images.ClassifierAAsan], which the build makes from the
    classifier ELF file that harness.yaml pins.  This file defines nothing new. *)
From OSSVerify.zlib.zlib_uncompress_fuzzer.images Require ClassifierAAsan.
Module M := ClassifierAAsan.M.
Notation X_init_pc := ClassifierAAsan.ClassifierAAsan_init_pc (only parsing).
Notation X_loaded_segments := ClassifierAAsan.ClassifierAAsan_loaded_segments (only parsing).
Notation X_phdrs := ClassifierAAsan.ClassifierAAsan_phdrs (only parsing).
Notation X_seg_bytes_000 := ClassifierAAsan.ClassifierAAsan_seg_bytes_000 (only parsing).
Notation X_seg_bytes_001 := ClassifierAAsan.ClassifierAAsan_seg_bytes_001 (only parsing).
Notation X_seg_bytes_002 := ClassifierAAsan.ClassifierAAsan_seg_bytes_002 (only parsing).
Notation X_seg_bytes_003 := ClassifierAAsan.ClassifierAAsan_seg_bytes_003 (only parsing).
Notation X_segment_000 := ClassifierAAsan.ClassifierAAsan_segment_000 (only parsing).
Notation X_segment_001 := ClassifierAAsan.ClassifierAAsan_segment_001 (only parsing).
Notation X_segment_002 := ClassifierAAsan.ClassifierAAsan_segment_002 (only parsing).
Notation X_segment_003 := ClassifierAAsan.ClassifierAAsan_segment_003 (only parsing).
