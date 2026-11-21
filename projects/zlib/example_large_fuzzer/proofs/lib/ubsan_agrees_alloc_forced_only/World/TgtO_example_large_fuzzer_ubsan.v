(** [TgtO_example_large_fuzzer_ubsan]: the names that the texts of this proof library use for the memory image of the UbsanOriginal build.
    Each is an alias of the repository's image of that build, [OSSVerify.zlib.example_large_fuzzer.images.UbsanOriginal], which the build makes
    from the ELF file that harness.yaml pins.  This file defines nothing new. *)
From OSSVerify.zlib.example_large_fuzzer.images Require UbsanOriginal.
Module M := UbsanOriginal.M.
Notation TgtO_example_large_fuzzer_ubsan_init_pc := UbsanOriginal.UbsanOriginal_init_pc (only parsing).
Notation TgtO_example_large_fuzzer_ubsan_loaded_segments := UbsanOriginal.UbsanOriginal_loaded_segments (only parsing).
Notation TgtO_example_large_fuzzer_ubsan_phdrs := UbsanOriginal.UbsanOriginal_phdrs (only parsing).
Notation TgtO_example_large_fuzzer_ubsan_seg_bytes_000 := UbsanOriginal.UbsanOriginal_seg_bytes_000 (only parsing).
Notation TgtO_example_large_fuzzer_ubsan_seg_bytes_001 := UbsanOriginal.UbsanOriginal_seg_bytes_001 (only parsing).
Notation TgtO_example_large_fuzzer_ubsan_seg_bytes_002 := UbsanOriginal.UbsanOriginal_seg_bytes_002 (only parsing).
Notation TgtO_example_large_fuzzer_ubsan_seg_bytes_003 := UbsanOriginal.UbsanOriginal_seg_bytes_003 (only parsing).
Notation TgtO_example_large_fuzzer_ubsan_segment_000 := UbsanOriginal.UbsanOriginal_segment_000 (only parsing).
Notation TgtO_example_large_fuzzer_ubsan_segment_001 := UbsanOriginal.UbsanOriginal_segment_001 (only parsing).
Notation TgtO_example_large_fuzzer_ubsan_segment_002 := UbsanOriginal.UbsanOriginal_segment_002 (only parsing).
Notation TgtO_example_large_fuzzer_ubsan_segment_003 := UbsanOriginal.UbsanOriginal_segment_003 (only parsing).
