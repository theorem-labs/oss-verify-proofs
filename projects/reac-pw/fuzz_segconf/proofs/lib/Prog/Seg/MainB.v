(** Segments M02 and V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain image
    3776ca44d75c): the evt-callee contracts of the two segments.
    - K_M02, K_V01: SegEnd's K_<seg> of M02 and V01, the conjunction of the contracts of the functions each segment
      calls inside its evt body (calloc is seg_M02_stmt's separate premise):
        M02 (0x13ae0 .. 0x13ca8): check_segments, then per segment reac_segconf_role, check_role, reac_segconf_model,
          check_model, reac_segconf_ignored, check_ignore, reac_segconf_role_file, reac_segconf_ignore_file,
          check_provenance; check_refusals; per kept refusal check_address, check_knock_refused; per segment
          snprintf ("%sx"), strlen, m_find, check_absent; m_find and check_absent on "nosuch0".
        V01 (0x13cac .. 0x13f3c): memset (the guard), memcpy ("enp1s0", m_split's parent, the mvlan copy), strrchr,
          strcmp (m_declared's duplicate test), reac_segconf_declared, check_declared.
    The walks deliver SegEnd.seg_M02_stmt CPseg K_M02 (Prog/Seg/M02.v) and SegEnd.seg_V01_stmt CPseg K_V01
    (Prog/Seg/V01.v, from SegEvt.evt_V01 through SegEvt.seg_V01_of_evt), at the cut record every walk of main
    shares: SegWalkMainA.CPseg (Prog/Seg/SegWalkMainA.v, over the Prog/seg_cuts.v predicates).
    Statement text of segment lemmas. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require check_segments_c reac_segconf_role_c check_role_c
  reac_segconf_model_c check_model_c reac_segconf_ignored_c check_ignore_c reac_segconf_role_file_c
  reac_segconf_ignore_file_c check_provenance_c check_refusals_c check_address_c check_knock_refused_c snprintf_c
  strlen_c m_find_c check_absent_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require memset_c memcpy_c strrchr_c strcmp_c
  reac_segconf_declared_c check_declared_c.

Definition K_M02 : Prop :=
  lib.Prog.check_segments_c.check_segments_contract /\
  lib.Prog.reac_segconf_role_c.reac_segconf_role_contract /\
  lib.Prog.check_role_c.check_role_contract /\
  lib.Prog.reac_segconf_model_c.reac_segconf_model_contract /\
  lib.Prog.check_model_c.check_model_contract /\
  lib.Prog.reac_segconf_ignored_c.reac_segconf_ignored_contract /\
  lib.Prog.check_ignore_c.check_ignore_contract /\
  lib.Prog.reac_segconf_role_file_c.reac_segconf_role_file_contract /\
  lib.Prog.reac_segconf_ignore_file_c.reac_segconf_ignore_file_contract /\
  lib.Prog.check_provenance_c.check_provenance_contract /\
  lib.Prog.check_refusals_c.check_refusals_contract /\
  lib.Prog.check_address_c.check_address_contract /\
  lib.Prog.check_knock_refused_c.check_knock_refused_contract /\
  lib.Prog.snprintf_c.snprintf_contract /\
  lib.Prog.strlen_c.strlen_contract /\
  lib.Prog.m_find_c.m_find_contract /\
  lib.Prog.check_absent_c.check_absent_contract.

Definition K_V01 : Prop :=
  lib.Prog.memset_c.memset_contract /\
  lib.Prog.memcpy_c.memcpy_contract /\
  lib.Prog.strrchr_c.strrchr_contract /\
  lib.Prog.strcmp_c.strcmp_contract /\
  lib.Prog.reac_segconf_declared_c.reac_segconf_declared_contract /\
  lib.Prog.check_declared_c.check_declared_contract.
