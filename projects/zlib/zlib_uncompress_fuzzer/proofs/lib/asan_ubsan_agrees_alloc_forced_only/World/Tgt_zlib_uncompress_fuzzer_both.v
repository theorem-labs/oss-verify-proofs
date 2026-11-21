(** [Tgt_zlib_uncompress_fuzzer_both]: the names that the texts of this proof library use for the memory image of the AsanUbsan build.
    Each is an alias of the repository's image of that build, [OSSVerify.zlib.zlib_uncompress_fuzzer.images.AsanUbsan], which the build makes
    from the ELF file that harness.yaml pins.  This file defines nothing new. *)
From OSSVerify.zlib.zlib_uncompress_fuzzer.images Require AsanUbsan.
Module M := AsanUbsan.M.
Notation Tgt_zlib_uncompress_fuzzer_both_init_pc := AsanUbsan.AsanUbsan_init_pc (only parsing).
Notation Tgt_zlib_uncompress_fuzzer_both_loaded_segments := AsanUbsan.AsanUbsan_loaded_segments (only parsing).
Notation Tgt_zlib_uncompress_fuzzer_both_phdrs := AsanUbsan.AsanUbsan_phdrs (only parsing).
Notation Tgt_zlib_uncompress_fuzzer_both_seg_bytes_000 := AsanUbsan.AsanUbsan_seg_bytes_000 (only parsing).
Notation Tgt_zlib_uncompress_fuzzer_both_seg_bytes_001 := AsanUbsan.AsanUbsan_seg_bytes_001 (only parsing).
Notation Tgt_zlib_uncompress_fuzzer_both_seg_bytes_002 := AsanUbsan.AsanUbsan_seg_bytes_002 (only parsing).
Notation Tgt_zlib_uncompress_fuzzer_both_seg_bytes_003 := AsanUbsan.AsanUbsan_seg_bytes_003 (only parsing).
Notation Tgt_zlib_uncompress_fuzzer_both_segment_000 := AsanUbsan.AsanUbsan_segment_000 (only parsing).
Notation Tgt_zlib_uncompress_fuzzer_both_segment_001 := AsanUbsan.AsanUbsan_segment_001 (only parsing).
Notation Tgt_zlib_uncompress_fuzzer_both_segment_002 := AsanUbsan.AsanUbsan_segment_002 (only parsing).
Notation Tgt_zlib_uncompress_fuzzer_both_segment_003 := AsanUbsan.AsanUbsan_segment_003 (only parsing).
