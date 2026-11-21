(** [TgtO_zlib_uncompress_fuzzer_both]: the names that the texts of this proof library use for the memory image of the AsanUbsanOriginal build.
    Each is an alias of the repository's image of that build, [OSSVerify.zlib.zlib_uncompress_fuzzer.images.AsanUbsanOriginal], which the build makes
    from the ELF file that harness.yaml pins.  This file defines nothing new. *)
From OSSVerify.zlib.zlib_uncompress_fuzzer.images Require AsanUbsanOriginal.
Module M := AsanUbsanOriginal.M.
Notation TgtO_zlib_uncompress_fuzzer_both_init_pc := AsanUbsanOriginal.AsanUbsanOriginal_init_pc (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_both_loaded_segments := AsanUbsanOriginal.AsanUbsanOriginal_loaded_segments (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_both_phdrs := AsanUbsanOriginal.AsanUbsanOriginal_phdrs (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_both_seg_bytes_000 := AsanUbsanOriginal.AsanUbsanOriginal_seg_bytes_000 (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_both_seg_bytes_001 := AsanUbsanOriginal.AsanUbsanOriginal_seg_bytes_001 (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_both_seg_bytes_002 := AsanUbsanOriginal.AsanUbsanOriginal_seg_bytes_002 (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_both_seg_bytes_003 := AsanUbsanOriginal.AsanUbsanOriginal_seg_bytes_003 (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_both_segment_000 := AsanUbsanOriginal.AsanUbsanOriginal_segment_000 (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_both_segment_001 := AsanUbsanOriginal.AsanUbsanOriginal_segment_001 (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_both_segment_002 := AsanUbsanOriginal.AsanUbsanOriginal_segment_002 (only parsing).
Notation TgtO_zlib_uncompress_fuzzer_both_segment_003 := AsanUbsanOriginal.AsanUbsanOriginal_segment_003 (only parsing).
