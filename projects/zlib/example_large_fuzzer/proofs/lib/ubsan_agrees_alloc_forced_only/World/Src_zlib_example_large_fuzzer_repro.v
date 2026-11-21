(** [Src_zlib_example_large_fuzzer_repro]: the names that the texts of this proof library use for the memory image of the Plain build.
    Each is an alias of the repository's image of that build, [OSSVerify.zlib.example_large_fuzzer.images.Plain], which the build makes
    from the ELF file that harness.yaml pins.  This file defines nothing new. *)
From OSSVerify.zlib.example_large_fuzzer.images Require Plain.
Module M := Plain.M.
Notation Src_zlib_example_large_fuzzer_repro_init_pc := Plain.Plain_init_pc (only parsing).
Notation Src_zlib_example_large_fuzzer_repro_loaded_segments := Plain.Plain_loaded_segments (only parsing).
Notation Src_zlib_example_large_fuzzer_repro_phdrs := Plain.Plain_phdrs (only parsing).
Notation Src_zlib_example_large_fuzzer_repro_seg_bytes_000 := Plain.Plain_seg_bytes_000 (only parsing).
Notation Src_zlib_example_large_fuzzer_repro_seg_bytes_001 := Plain.Plain_seg_bytes_001 (only parsing).
Notation Src_zlib_example_large_fuzzer_repro_seg_bytes_002 := Plain.Plain_seg_bytes_002 (only parsing).
Notation Src_zlib_example_large_fuzzer_repro_seg_bytes_003 := Plain.Plain_seg_bytes_003 (only parsing).
Notation Src_zlib_example_large_fuzzer_repro_segment_000 := Plain.Plain_segment_000 (only parsing).
Notation Src_zlib_example_large_fuzzer_repro_segment_001 := Plain.Plain_segment_001 (only parsing).
Notation Src_zlib_example_large_fuzzer_repro_segment_002 := Plain.Plain_segment_002 (only parsing).
Notation Src_zlib_example_large_fuzzer_repro_segment_003 := Plain.Plain_segment_003 (only parsing).
