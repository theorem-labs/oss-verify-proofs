(** [Clb_zlib_uncompress2_fuzzer_asan]: the names that the texts of this proof library use for the memory image of the ClassifierBAsan build.
    Each is an alias of the repository's image of that build, [OSSVerify.zlib.zlib_uncompress2_fuzzer.images.ClassifierBAsan], which the build makes
    from the ELF file that harness.yaml pins.  This file defines nothing new. *)
From OSSVerify.zlib.zlib_uncompress2_fuzzer.images Require ClassifierBAsan.
Module M := ClassifierBAsan.M.
Notation Clb_zlib_uncompress2_fuzzer_asan_init_pc := ClassifierBAsan.ClassifierBAsan_init_pc (only parsing).
Notation Clb_zlib_uncompress2_fuzzer_asan_loaded_segments := ClassifierBAsan.ClassifierBAsan_loaded_segments (only parsing).
Notation Clb_zlib_uncompress2_fuzzer_asan_phdrs := ClassifierBAsan.ClassifierBAsan_phdrs (only parsing).
Notation Clb_zlib_uncompress2_fuzzer_asan_seg_bytes_000 := ClassifierBAsan.ClassifierBAsan_seg_bytes_000 (only parsing).
Notation Clb_zlib_uncompress2_fuzzer_asan_seg_bytes_001 := ClassifierBAsan.ClassifierBAsan_seg_bytes_001 (only parsing).
Notation Clb_zlib_uncompress2_fuzzer_asan_seg_bytes_002 := ClassifierBAsan.ClassifierBAsan_seg_bytes_002 (only parsing).
Notation Clb_zlib_uncompress2_fuzzer_asan_seg_bytes_003 := ClassifierBAsan.ClassifierBAsan_seg_bytes_003 (only parsing).
Notation Clb_zlib_uncompress2_fuzzer_asan_segment_000 := ClassifierBAsan.ClassifierBAsan_segment_000 (only parsing).
Notation Clb_zlib_uncompress2_fuzzer_asan_segment_001 := ClassifierBAsan.ClassifierBAsan_segment_001 (only parsing).
Notation Clb_zlib_uncompress2_fuzzer_asan_segment_002 := ClassifierBAsan.ClassifierBAsan_segment_002 (only parsing).
Notation Clb_zlib_uncompress2_fuzzer_asan_segment_003 := ClassifierBAsan.ClassifierBAsan_segment_003 (only parsing).
