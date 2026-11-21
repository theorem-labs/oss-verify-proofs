(** [Tgt_checksum_fuzzer_asan]: the names that the texts of this proof library use for the memory image of the Asan build.
    Each is an alias of the repository's image of that build, [OSSVerify.zlib.checksum_fuzzer.images.Asan], which the build makes
    from the ELF file that harness.yaml pins.  This file defines nothing new. *)
From OSSVerify.zlib.checksum_fuzzer.images Require Asan.
Module M := Asan.M.
Notation Tgt_checksum_fuzzer_asan_init_pc := Asan.Asan_init_pc (only parsing).
Notation Tgt_checksum_fuzzer_asan_loaded_segments := Asan.Asan_loaded_segments (only parsing).
Notation Tgt_checksum_fuzzer_asan_phdrs := Asan.Asan_phdrs (only parsing).
Notation Tgt_checksum_fuzzer_asan_seg_bytes_000 := Asan.Asan_seg_bytes_000 (only parsing).
Notation Tgt_checksum_fuzzer_asan_seg_bytes_001 := Asan.Asan_seg_bytes_001 (only parsing).
Notation Tgt_checksum_fuzzer_asan_seg_bytes_002 := Asan.Asan_seg_bytes_002 (only parsing).
Notation Tgt_checksum_fuzzer_asan_seg_bytes_003 := Asan.Asan_seg_bytes_003 (only parsing).
Notation Tgt_checksum_fuzzer_asan_segment_000 := Asan.Asan_segment_000 (only parsing).
Notation Tgt_checksum_fuzzer_asan_segment_001 := Asan.Asan_segment_001 (only parsing).
Notation Tgt_checksum_fuzzer_asan_segment_002 := Asan.Asan_segment_002 (only parsing).
Notation Tgt_checksum_fuzzer_asan_segment_003 := Asan.Asan_segment_003 (only parsing).
