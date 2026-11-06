(** m_file (UBSan build): m_file_pieces_give_contract of U/Prog/m_file_c.v (family F3). The head
    invariant holds for every bound n by induction on n: H_MF_HEAD 0 asks for a text shorter than 0 bytes, and
    H_MF_HEAD (S n) is S_MF_LINE of H_MF_TAIL n, which S_MF_TAIL gives from H_MF_HEAD n and H_MF_EXIT. S_MF_ENTRY
    then gives the contract. Logic only. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import m_file_c.

Lemma m_file_pieces_give_contract_holds : m_file_pieces_give_contract.
Proof.
  unfold m_file_pieces_give_contract, S_MF_EXIT, S_MF_TAIL, S_MF_LINE, S_MF_ENTRY.
  intros HX HT HL HE. apply HE; [|exact HX].
  intros n. induction n as [|n IH].
  - unfold H_MF_HEAD. intros. lia.
  - apply HL. apply HT; [exact IH | exact HX].
Qed.
