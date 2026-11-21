(** [Src_zlib_zlib_uncompress3_fuzzer_repro]: the names that the texts of this proof library use for the memory image of the Plain build.
    Each is an alias of this library's own copy of that image, [OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Plain], which holds
    the segment bytes as string literals equal to the release's segment text of the zlib_uncompress3_fuzzer Plain build (from the ELF file its harness.yaml pins).  This file defines nothing new. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Plain.
Module M := Plain.M.
Notation Src_zlib_zlib_uncompress3_fuzzer_repro_init_pc := Plain.Plain_init_pc (only parsing).
Notation Src_zlib_zlib_uncompress3_fuzzer_repro_loaded_segments := Plain.Plain_loaded_segments (only parsing).
Notation Src_zlib_zlib_uncompress3_fuzzer_repro_phdrs := Plain.Plain_phdrs (only parsing).
Notation Src_zlib_zlib_uncompress3_fuzzer_repro_seg_bytes_000 := Plain.Plain_seg_bytes_000 (only parsing).
Notation Src_zlib_zlib_uncompress3_fuzzer_repro_seg_bytes_001 := Plain.Plain_seg_bytes_001 (only parsing).
Notation Src_zlib_zlib_uncompress3_fuzzer_repro_seg_bytes_002 := Plain.Plain_seg_bytes_002 (only parsing).
Notation Src_zlib_zlib_uncompress3_fuzzer_repro_seg_bytes_003 := Plain.Plain_seg_bytes_003 (only parsing).
Notation Src_zlib_zlib_uncompress3_fuzzer_repro_segment_000 := Plain.Plain_segment_000 (only parsing).
Notation Src_zlib_zlib_uncompress3_fuzzer_repro_segment_001 := Plain.Plain_segment_001 (only parsing).
Notation Src_zlib_zlib_uncompress3_fuzzer_repro_segment_002 := Plain.Plain_segment_002 (only parsing).
Notation Src_zlib_zlib_uncompress3_fuzzer_repro_segment_003 := Plain.Plain_segment_003 (only parsing).
