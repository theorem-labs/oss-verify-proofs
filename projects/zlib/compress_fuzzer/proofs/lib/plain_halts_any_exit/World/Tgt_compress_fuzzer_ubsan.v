(** [Tgt_compress_fuzzer_ubsan]: the names that the texts of this proof library use for the memory image of the Ubsan build.
    Each is an alias of the repository's image of that build, [OSSVerify.zlib.compress_fuzzer.images.Ubsan], which the build makes
    from the ELF file that harness.yaml pins.  This file defines nothing new. *)
From OSSVerify.zlib.compress_fuzzer.images Require Ubsan.
Module M := Ubsan.M.
Notation Tgt_compress_fuzzer_ubsan_init_pc := Ubsan.Ubsan_init_pc (only parsing).
Notation Tgt_compress_fuzzer_ubsan_loaded_segments := Ubsan.Ubsan_loaded_segments (only parsing).
Notation Tgt_compress_fuzzer_ubsan_phdrs := Ubsan.Ubsan_phdrs (only parsing).
Notation Tgt_compress_fuzzer_ubsan_seg_bytes_000 := Ubsan.Ubsan_seg_bytes_000 (only parsing).
Notation Tgt_compress_fuzzer_ubsan_seg_bytes_001 := Ubsan.Ubsan_seg_bytes_001 (only parsing).
Notation Tgt_compress_fuzzer_ubsan_seg_bytes_002 := Ubsan.Ubsan_seg_bytes_002 (only parsing).
Notation Tgt_compress_fuzzer_ubsan_seg_bytes_003 := Ubsan.Ubsan_seg_bytes_003 (only parsing).
Notation Tgt_compress_fuzzer_ubsan_segment_000 := Ubsan.Ubsan_segment_000 (only parsing).
Notation Tgt_compress_fuzzer_ubsan_segment_001 := Ubsan.Ubsan_segment_001 (only parsing).
Notation Tgt_compress_fuzzer_ubsan_segment_002 := Ubsan.Ubsan_segment_002 (only parsing).
Notation Tgt_compress_fuzzer_ubsan_segment_003 := Ubsan.Ubsan_segment_003 (only parsing).
