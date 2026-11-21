(** [W_aefw2_zlib_example_large_fuzzer]: the names that the texts of this proof library use for the input distribution of
    this harness.  Each is an alias of the repository's [OSSVerify.zlib.example_large_fuzzer.Distribution], whose
    text is the same byte for byte.  This file defines nothing new. *)
From OSSVerify.zlib.example_large_fuzzer Require Distribution.
Notation M := Distribution.M (only parsing).
Notation M_is := Distribution.M_is (only parsing).
Notation M_nonneg := Distribution.M_nonneg (only parsing).
Notation argv_arity := Distribution.argv_arity (only parsing).
Notation argv_arity_entries := Distribution.argv_arity_entries (only parsing).
Notation argv_arity_nonneg := Distribution.argv_arity_nonneg (only parsing).
Notation base := Distribution.base (only parsing).
Notation base_half := Distribution.base_half (only parsing).
Notation base_half_le_1 := Distribution.base_half_le_1 (only parsing).
Notation base_half_nonneg := Distribution.base_half_nonneg (only parsing).
Notation cd := Distribution.cd (only parsing).
Notation components := Distribution.components (only parsing).
Notation envp0 := Distribution.envp0 (only parsing).
Notation fs0 := Distribution.fs0 (only parsing).
Notation hdr := Distribution.hdr (only parsing).
Notation m_argv_arity_each := Distribution.m_argv_arity_each (only parsing).
Notation m_base := Distribution.m_base (only parsing).
Notation m_base_nonneg := Distribution.m_base_nonneg (only parsing).
Notation m_missing_file := Distribution.m_missing_file (only parsing).
Notation m_payload := Distribution.m_payload (only parsing).
Notation m_payload_nonneg := Distribution.m_payload_nonneg (only parsing).
Notation missing_file := Distribution.missing_file (only parsing).
Notation missing_file_entries := Distribution.missing_file_entries (only parsing).
Notation missing_file_nonneg := Distribution.missing_file_nonneg (only parsing).
Notation p := Distribution.p (only parsing).
Notation p_le_1 := Distribution.p_le_1 (only parsing).
Notation p_nonneg := Distribution.p_nonneg (only parsing).
Notation path := Distribution.path (only parsing).
Notation payload := Distribution.payload (only parsing).
Notation prog := Distribution.prog (only parsing).
Notation stdin0 := Distribution.stdin0 (only parsing).
Notation w := Distribution.w (only parsing).
Notation w_core_blind := Distribution.w_core_blind (only parsing).
Notation w_nonneg := Distribution.w_nonneg (only parsing).
Module Ascription := Distribution.Ascription.
