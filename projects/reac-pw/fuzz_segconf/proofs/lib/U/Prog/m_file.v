(** m_file (UBSan build, image 1696d6c34ffd, 0x14268): proof of [m_file_contract] (U/Prog/m_file_c.v, family F3)
    from the contracts of its callees: the four pieces (mf_entry.v, mf_line.v, mf_tail.v, mf_exit.v)
    and their composition (m_file_pieces.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import
  m_file_c strchr_c strlen_c memchr_c bcmp_c memcpy_c memset_c fuzz_catalogue_row_c ieq_c m_find_c
  m_refuse_c strip_c fold_c snprintf_c m_file_pieces mf_exit mf_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require mf_entry mf_line.

Theorem m_file_holds :
  snprintf_contract -> strchr_contract -> strlen_contract -> memchr_contract -> bcmp_contract -> memcpy_contract ->
  memset_contract -> fuzz_catalogue_row_contract -> ieq_contract -> m_find_contract -> m_refuse_contract ->
  strip_contract -> fold_contract -> m_file_contract.
Proof.
  intros HSNP HCHR HLEN HMCH HBCMP HMCPY HMSET HFCR HIEQ HFIND HREF HSTRIP HFOLD.
  apply m_file_pieces_give_contract_holds.
  - exact mf_exit_holds.
  - exact mf_tail_holds.
  - apply mf_line.mf_line_holds; assumption.
  - apply mf_entry.mf_entry_holds; assumption.
Qed.
