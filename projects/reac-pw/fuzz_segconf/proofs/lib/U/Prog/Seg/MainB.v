(** Segments M02 and V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan image
    1696d6c34ffd): the evt-callee contracts of the two segments, the twin of lib/Prog/Seg/MainB.v.
    - K_M02, K_V01: U/Prog/SegEnd's K_<seg> of M02 (0x13c3c .. 0x13e8c) and V01 (0x13e90 .. 0x141e8), the
      conjunction of the UBSan contracts of the functions each segment calls inside its evt body (the same functions
      as the plain build).
    The walks deliver U/Prog/SegEnd.seg_M02_stmt CPseg K_M02 (U/Prog/Seg/M02.v) and seg_V01_stmt CPseg K_V01
    (U/Prog/Seg/V01.v), at the cut record every walk of main shares: U/Prog/Seg/SegWalkMainA.CPseg (over the
    U/Prog/seg_cuts.v predicates).
    Statement text of segment lemmas. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require check_segments_c reac_segconf_role_c check_role_c
  reac_segconf_model_c check_model_c reac_segconf_ignored_c check_ignore_c reac_segconf_role_file_c
  reac_segconf_ignore_file_c check_provenance_c check_refusals_c check_address_c check_knock_refused_c snprintf_c
  strlen_c m_find_c check_absent_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require memset_c memcpy_c strrchr_c strcmp_c
  reac_segconf_declared_c check_declared_c.

Definition K_M02 : Prop :=
  lib.U.Prog.check_segments_c.check_segments_contract /\
  lib.U.Prog.reac_segconf_role_c.reac_segconf_role_contract /\
  lib.U.Prog.check_role_c.check_role_contract /\
  lib.U.Prog.reac_segconf_model_c.reac_segconf_model_contract /\
  lib.U.Prog.check_model_c.check_model_contract /\
  lib.U.Prog.reac_segconf_ignored_c.reac_segconf_ignored_contract /\
  lib.U.Prog.check_ignore_c.check_ignore_contract /\
  lib.U.Prog.reac_segconf_role_file_c.reac_segconf_role_file_contract /\
  lib.U.Prog.reac_segconf_ignore_file_c.reac_segconf_ignore_file_contract /\
  lib.U.Prog.check_provenance_c.check_provenance_contract /\
  lib.U.Prog.check_refusals_c.check_refusals_contract /\
  lib.U.Prog.check_address_c.check_address_contract /\
  lib.U.Prog.check_knock_refused_c.check_knock_refused_contract /\
  lib.U.Prog.snprintf_c.snprintf_contract /\
  lib.U.Prog.strlen_c.strlen_contract /\
  lib.U.Prog.m_find_c.m_find_contract /\
  lib.U.Prog.check_absent_c.check_absent_contract.

Definition K_V01 : Prop :=
  lib.U.Prog.memset_c.memset_contract /\
  lib.U.Prog.memcpy_c.memcpy_contract /\
  lib.U.Prog.strrchr_c.strrchr_contract /\
  lib.U.Prog.strcmp_c.strcmp_contract /\
  lib.U.Prog.reac_segconf_declared_c.reac_segconf_declared_contract /\
  lib.U.Prog.check_declared_c.check_declared_contract.
