(** [TgtO_zlib_uncompress_fuzzer_asan]: the names that the texts of this proof library use for the memory image of the AsanOriginal build.
    Each is an alias of the repository's image of that build, [OSSVerify.zlib.zlib_uncompress_fuzzer.images.AsanOriginal], which the build makes
    from the ELF file that harness.yaml pins.  This file defines nothing new. *)
From OSSVerify.zlib.zlib_uncompress_fuzzer.images Require AsanOriginal.
Module M := AsanOriginal.M.
Notation TgtO_zlib_uncompress_fuzzer_asan_init_pc := AsanOriginal.AsanOriginal_init_pc (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_asan_loaded_segments := AsanOriginal.AsanOriginal_loaded_segments (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_asan_phdrs := AsanOriginal.AsanOriginal_phdrs (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_asan_seg_bytes_000 := AsanOriginal.AsanOriginal_seg_bytes_000 (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_asan_seg_bytes_001 := AsanOriginal.AsanOriginal_seg_bytes_001 (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_asan_seg_bytes_002 := AsanOriginal.AsanOriginal_seg_bytes_002 (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_asan_seg_bytes_003 := AsanOriginal.AsanOriginal_seg_bytes_003 (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_asan_segment_000 := AsanOriginal.AsanOriginal_segment_000 (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_asan_segment_001 := AsanOriginal.AsanOriginal_segment_001 (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_asan_segment_002 := AsanOriginal.AsanOriginal_segment_002 (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_asan_segment_003 := AsanOriginal.AsanOriginal_segment_003 (only parsing).
