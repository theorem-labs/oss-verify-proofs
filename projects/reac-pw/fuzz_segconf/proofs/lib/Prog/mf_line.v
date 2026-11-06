(** m_file (plain build, image 3776ca44d75c): the piece S_MF_LINE (0x1407c-0x143d4 and 0x143e0-0x14748: one line)
    from its nine sub-pieces (Prog/mf_cuts.v, mf_line_from_parts) and their walks: the line
    driver and the long line (mf_line_front.v), the header before and after m_find (mf_line_hdra.v, mf_line_hdrb.v),
    the key before its word chain (mf_line_keya.v), "role" (mf_line_krole.v), "model" (mf_line_kmodel.v), "ignore"
    and "knock" (mf_line_kign.v). The callee contracts are the premises. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env m_file_c mf_cuts
  strchr_c strlen_c memchr_c bcmp_c memcpy_c memset_c snprintf_c fuzz_catalogue_row_c ieq_c m_find_c m_refuse_c
  mf_line_front mf_line_hdra mf_line_hdrb mf_line_keya mf_line_krole mf_line_kmodel mf_line_kign.
Import ListNotations.
Open Scope Z_scope.

Lemma mf_line_holds :
  snprintf_contract -> strchr_contract -> strlen_contract -> memchr_contract -> bcmp_contract ->
  memcpy_contract -> memset_contract -> fuzz_catalogue_row_contract -> ieq_contract -> m_find_contract ->
  m_refuse_contract -> S_MF_LINE.
Proof.
  intros HSN HSC HSL HMC HBC HMY HMS HFC HIQ HMF HMR.
  apply mf_line_from_parts.
  - exact (mf_front_holds HSC HSL).
  - exact (mf_longp_holds HMR).
  - exact (mf_hdra_holds HMC HIQ HMR).
  - exact (mf_hdrb_holds HMF HMS HMY HMR).
  - exact (mf_keya_holds HMC HMR).
  - exact (mf_krole_holds HIQ HSL HBC HSN HMR).
  - exact (mf_kmod_holds HIQ HFC HMY HMR).
  - exact (mf_kignp_holds HIQ HSN HMR).
  - exact (mf_kknockp_holds HIQ HMR).
Qed.
