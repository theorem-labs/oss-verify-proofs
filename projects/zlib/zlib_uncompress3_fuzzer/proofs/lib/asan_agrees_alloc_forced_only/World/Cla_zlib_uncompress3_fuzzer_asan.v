(** [Cla_zlib_uncompress3_fuzzer_asan]: the names that the texts of this proof library use for the memory image of the ClassifierAAsan build.
    Each is an alias of the repository's image of that build, [OSSVerify.zlib.zlib_uncompress3_fuzzer.images.ClassifierAAsan], which the build makes
    from the ELF file that harness.yaml pins.  This file defines nothing new. *)
From OSSVerify.zlib.zlib_uncompress3_fuzzer.images Require ClassifierAAsan.
Module M := ClassifierAAsan.M.
Notation Cla_zlib_uncompress3_fuzzer_asan_init_pc := ClassifierAAsan.ClassifierAAsan_init_pc (only parsing).
Notation Cla_zlib_uncompress3_fuzzer_asan_loaded_segments := ClassifierAAsan.ClassifierAAsan_loaded_segments (only parsing).
Notation Cla_zlib_uncompress3_fuzzer_asan_phdrs := ClassifierAAsan.ClassifierAAsan_phdrs (only parsing).
Notation Cla_zlib_uncompress3_fuzzer_asan_seg_bytes_000 := ClassifierAAsan.ClassifierAAsan_seg_bytes_000 (only parsing).
Notation Cla_zlib_uncompress3_fuzzer_asan_seg_bytes_001 := ClassifierAAsan.ClassifierAAsan_seg_bytes_001 (only parsing).
Notation Cla_zlib_uncompress3_fuzzer_asan_seg_bytes_002 := ClassifierAAsan.ClassifierAAsan_seg_bytes_002 (only parsing).
Notation Cla_zlib_uncompress3_fuzzer_asan_seg_bytes_003 := ClassifierAAsan.ClassifierAAsan_seg_bytes_003 (only parsing).
Notation Cla_zlib_uncompress3_fuzzer_asan_segment_000 := ClassifierAAsan.ClassifierAAsan_segment_000 (only parsing).
Notation Cla_zlib_uncompress3_fuzzer_asan_segment_001 := ClassifierAAsan.ClassifierAAsan_segment_001 (only parsing).
Notation Cla_zlib_uncompress3_fuzzer_asan_segment_002 := ClassifierAAsan.ClassifierAAsan_segment_002 (only parsing).
Notation Cla_zlib_uncompress3_fuzzer_asan_segment_003 := ClassifierAAsan.ClassifierAAsan_segment_003 (only parsing).
