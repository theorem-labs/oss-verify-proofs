(** m_file (plain build, image 3776ca44d75c, 0x13fb4): the whole contract from its four pieces.
    m_file_pieces_give_contract (Prog/m_file_c.v): H_MF_HEAD n for every n by induction on n (H_MF_HEAD 0 is empty:
    no text is shorter than 0 bytes; H_MF_HEAD (S n) by S_MF_LINE from H_MF_TAIL n, which S_MF_TAIL gives from
    H_MF_HEAD n and H_MF_EXIT), then S_MF_ENTRY. m_file_holds: the contract from the callee contracts its walk
    takes (m_file_c.v's header): the pieces are mf_exit.v, mf_tail.v, mf_entry.v and mf_line.v (S_MF_LINE from its
    nine sub-pieces, Prog/mf_cuts.v). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import strchr_c strlen_c memchr_c bcmp_c memcpy_c
  memset_c snprintf_c fuzz_catalogue_row_c ieq_c m_find_c m_refuse_c mf_exit mf_tail mf_entry mf_line.
Import ListNotations.
Open Scope Z_scope.

Lemma m_file_heads : S_MF_EXIT -> S_MF_TAIL -> S_MF_LINE -> forall n, H_MF_HEAD n.
Proof.
  intros EX TL LN n. induction n as [|n IH].
  - unfold H_MF_HEAD. intros * Hn. exfalso. lia.
  - apply LN. apply TL; [exact IH | exact EX].
Qed.

Lemma m_file_pieces_give_contract_holds : m_file_pieces_give_contract.
Proof.
  unfold m_file_pieces_give_contract. intros EX TL LN EN.
  apply EN; [exact (m_file_heads EX TL LN) | exact EX].
Qed.

Theorem m_file_holds :
  snprintf_contract -> strchr_contract -> strlen_contract -> memchr_contract -> bcmp_contract ->
  memcpy_contract -> memset_contract -> fuzz_catalogue_row_contract -> ieq_contract -> m_find_contract ->
  m_refuse_contract -> m_file_contract.
Proof.
  intros HSN HSC HSL HMC HBC HMY HMS HFC HIQ HMF HMR.
  exact (m_file_pieces_give_contract_holds mf_exit_holds mf_tail_holds
           (mf_line_holds HSN HSC HSL HMC HBC HMY HMS HFC HIQ HMF HMR) (mf_entry_holds HSN)).
Qed.
