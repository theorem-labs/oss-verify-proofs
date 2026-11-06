(** m_file (UBSan build, image 1696d6c34ffd): the piece S_MF_LINE of U/Prog/m_file_c.v (family F3),
    from the nine sub-pieces of U/Prog/mfu_cuts.v (mfu_line_from_parts) and their walks:
    mf_line_front.v (S_MFU_FRONT), mf_line_long.v (S_MFU_LONGP), mf_line_hdra.v (S_MFU_HDRA), mf_line_hdrb.v
    (S_MFU_HDRB), mf_line_keya.v (S_MFU_KEYA), mf_line_krole.v (S_MFU_KROLE), mf_line_kmodel.v (S_MFU_KMOD),
    mf_line_kign.v (S_MFU_KIGNP, S_MFU_KKNOCKP). The callee contracts are premises. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import
  m_file_c mfu_cuts strchr_c strlen_c memchr_c bcmp_c memcpy_c memset_c fuzz_catalogue_row_c ieq_c m_find_c
  m_refuse_c strip_c fold_c snprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require
  mf_line_front mf_line_long mf_line_hdra mf_line_hdrb mf_line_keya mf_line_krole mf_line_kmodel mf_line_kign.

Theorem mf_line_holds :
  strchr_contract -> strlen_contract -> memchr_contract -> bcmp_contract -> memcpy_contract -> memset_contract ->
  fuzz_catalogue_row_contract -> ieq_contract -> m_find_contract -> m_refuse_contract -> strip_contract ->
  fold_contract -> snprintf_contract -> S_MF_LINE.
Proof.
  intros HCHR HLEN HMCH HBCMP HMCPY HMSET HFCR HIEQ HFIND HREF HSTRIP HFOLD HSNP.
  apply mfu_line_from_parts.
  - apply mf_line_front.mfu_front_holds; assumption.
  - apply mf_line_long.mfu_longp_holds; assumption.
  - apply mf_line_hdra.mfu_hdra_holds; assumption.
  - apply mf_line_hdrb.mfu_hdrb_holds; assumption.
  - apply mf_line_keya.mfu_keya_holds; assumption.
  - apply mf_line_krole.mfu_krole_holds; assumption.
  - apply mf_line_kmodel.mfu_kmod_holds; assumption.
  - apply mf_line_kign.mfu_kignp_holds; assumption.
  - apply mf_line_kign.mfu_kknockp_holds; assumption.
Qed.
