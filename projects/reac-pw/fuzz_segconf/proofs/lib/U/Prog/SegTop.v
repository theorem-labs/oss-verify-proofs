(* ubsan_halts of reac-pw/fuzz_segconf (UBSan build): U/Prog/SegEnd.ubsan_halts_of_callees at the cut
   record CPseg, every premise discharged by a proved walk, and each walk's own callee contracts by the leaf proofs, as
   reac-pw/fuzz_pin's U/Prog/PinTop.v (commit aa56e9780de) does for pin. The twin of
   lib/Prog/SegTop.v over the UBSan walks and contracts (lib/U/Prog, same names). No premise is left.
   The composition tree (each contract premise of a _holds discharged by another _holds):
   - segments: E01, M01, L01, L03, X01 by U/Prog/Seg/<SEG>.seg_<SEG>_holds, M02 and V01 by
     U/Prog/Seg/M02.seg_M02 and U/Prog/Seg/V01.seg_V01, L02 by U/Prog/Seg/L02T.seg_L02;
   - K_M01 = reac_segconf_init_contract: reac_segconf_init_holds (memset_holds);
   - K_L01 = memchr_contract: memchr_holds;
   - K_L02 (U/Prog/Seg/L02D.K_L02): memcpy_holds, snprintf_m_holds, memset_holds, m_file_holds (snprintf, strchr,
     strlen, memchr, bcmp, memcpy, memset, fuzz_catalogue_row_holds (strlen, bcmp), ieq_holds (strlen), m_find,
     m_refuse, strip_holds, fold_holds), m_refuse_holds (snprintf_m_holds), reac_segconf_parse_file_holds (snprintf,
     strchr, strlen, memcpy, r2_closed.trim_contract_closed, strspn, r2_closed.refuse_contract_closed, strncasecmp,
     strcmp, memset, strcasecmp_holds (tolower_holds), bcmp, reac_box_catalogue_by_token_holds (strlen,
     fuzz_catalogue_row), reac_box_catalogue_holds), reac_segconf_parse_holds (reac_segconf_parse_file,
     r2_closed.cross_check_contract_closed: cross_check_holds over refuse_holds over snprintf_holds, vsnprintf_holds);
   - K_M02 (U/Prog/Seg/MainB.K_M02): check_segments_holds (strcmp_holds),
     reac_segconf_role/model/ignored/role_file/ignore_file_holds (each reac_segconf_find_holds (strcmp_holds)),
     check_role_holds, check_model_holds (strcmp), check_ignore_holds, check_provenance_holds (strcmp),
     check_refusals_holds, check_address_holds (strlen, strncmp), check_knock_refused_holds (strstr_holds:
     fourbyte_strstr, twoway_strstr), snprintf_holds, strlen_holds, m_find_holds (strlen, bcmp), check_absent_holds
     (find, role, ignored, model);
   - K_V01 (U/Prog/Seg/MainB.K_V01): memset_holds, memcpy_holds, strrchr_holds (strlen, memrchr), strcmp_holds,
     reac_segconf_declared_holds (reac_declared_vlan_split_holds (strrchr, strtol_null_holds (__shlim_holds,
     __intscan_holds (__errno_location_holds, __shlim_holds)), strlen, memcpy, name_ok_holds (isalnum_holds)),
     reac_declared_vlan_add_holds (strcmp, memset, strncpy_holds)), check_declared_holds (strcmp);
   - calloc_concrete: U/CallocHolds.calloc_holds.
   Proves no function by itself: the top composition of LLVMFuzzerTestOneInput's walk. *)
From OSSVerify.reac_pw.fuzz_segconf Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require CallocHolds.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require SegEnd r2_closed
  memset memcpy memchr memrchr strlen strcmp strncmp strrchr strstr bcmp snprintf snprintf_m m_find m_refuse
  m_file strchr fuzz_catalogue_row ieq reac_segconf_parse_file strspn strncasecmp strcasecmp tolower
  reac_box_catalogue_by_token reac_box_catalogue strip fold
  reac_segconf_init reac_segconf_find reac_segconf_role reac_segconf_model reac_segconf_ignored
  reac_segconf_role_file reac_segconf_ignore_file reac_segconf_parse
  check_segments check_role check_model check_ignore check_provenance check_refusals check_address
  check_knock_refused check_absent check_declared
  reac_segconf_declared reac_declared_vlan_split reac_declared_vlan_add name_ok isalnum strtol_null strncpy
  __shlim __intscan __errno_location.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require memchr_c reac_segconf_init_c reac_segconf_find_c
  m_find_c m_refuse_c m_file_c reac_segconf_parse_file_c reac_segconf_declared_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require SegWalkMainA E01 M01 L01 L03 X01 L02D MainB
  M02 V01 L02T.

Local Abbreviation CPseg := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg.SegWalkMainA.CPseg.

(* The callee contracts and the evt-callee bundles K_<SEG>, each closed down to the leaf proofs. *)
Lemma reac_segconf_find_closed : lib.U.Prog.reac_segconf_find_c.reac_segconf_find_contract.
Proof. exact (lib.U.Prog.reac_segconf_find.reac_segconf_find_holds lib.U.Prog.strcmp.strcmp_holds). Qed.

Lemma m_find_closed : lib.U.Prog.m_find_c.m_find_contract.
Proof. exact (lib.U.Prog.m_find.m_find_holds lib.U.Prog.strlen.strlen_holds lib.U.Prog.bcmp.bcmp_holds). Qed.

Lemma m_refuse_closed : lib.U.Prog.m_refuse_c.m_refuse_contract.
Proof. exact (lib.U.Prog.m_refuse.m_refuse_holds lib.U.Prog.snprintf_m.snprintf_m_holds). Qed.

Lemma m_file_closed : lib.U.Prog.m_file_c.m_file_contract.
Proof.
  exact (lib.U.Prog.m_file.m_file_holds lib.U.Prog.snprintf.snprintf_holds lib.U.Prog.strchr.strchr_holds
           lib.U.Prog.strlen.strlen_holds lib.U.Prog.memchr.memchr_holds lib.U.Prog.bcmp.bcmp_holds
           lib.U.Prog.memcpy.memcpy_holds lib.U.Prog.memset.memset_holds
           (lib.U.Prog.fuzz_catalogue_row.fuzz_catalogue_row_holds lib.U.Prog.strlen.strlen_holds
              lib.U.Prog.bcmp.bcmp_holds)
           (lib.U.Prog.ieq.ieq_holds lib.U.Prog.strlen.strlen_holds) m_find_closed m_refuse_closed
           lib.U.Prog.strip.strip_holds lib.U.Prog.fold.fold_holds).
Qed.

Lemma K_M01_holds : lib.U.Prog.reac_segconf_init_c.reac_segconf_init_contract.
Proof. exact (lib.U.Prog.reac_segconf_init.reac_segconf_init_holds lib.U.Prog.memset.memset_holds). Qed.

Lemma K_L01_holds : lib.U.Prog.memchr_c.memchr_contract.
Proof. exact lib.U.Prog.memchr.memchr_holds. Qed.

Lemma K_M02_holds : lib.U.Prog.Seg.MainB.K_M02.
Proof.
  pose proof reac_segconf_find_closed as FIND.
  unfold lib.U.Prog.Seg.MainB.K_M02.
  split; [exact (lib.U.Prog.check_segments.check_segments_holds lib.U.Prog.strcmp.strcmp_holds)|].
  split; [exact (lib.U.Prog.reac_segconf_role.reac_segconf_role_holds FIND)|].
  split; [exact lib.U.Prog.check_role.check_role_holds|].
  split; [exact (lib.U.Prog.reac_segconf_model.reac_segconf_model_holds FIND)|].
  split; [exact (lib.U.Prog.check_model.check_model_holds lib.U.Prog.strcmp.strcmp_holds)|].
  split; [exact (lib.U.Prog.reac_segconf_ignored.reac_segconf_ignored_holds FIND)|].
  split; [exact lib.U.Prog.check_ignore.check_ignore_holds|].
  split; [exact (lib.U.Prog.reac_segconf_role_file.reac_segconf_role_file_holds FIND)|].
  split; [exact (lib.U.Prog.reac_segconf_ignore_file.reac_segconf_ignore_file_holds FIND)|].
  split; [exact (lib.U.Prog.check_provenance.check_provenance_holds lib.U.Prog.strcmp.strcmp_holds)|].
  split; [exact lib.U.Prog.check_refusals.check_refusals_holds|].
  split; [exact (lib.U.Prog.check_address.check_address_holds lib.U.Prog.strlen.strlen_holds lib.U.Prog.strncmp.strncmp_holds)|].
  split; [exact (lib.U.Prog.check_knock_refused.check_knock_refused_holds lib.U.Prog.strstr.strstr_holds)|].
  split; [exact lib.U.Prog.snprintf.snprintf_holds|].
  split; [exact lib.U.Prog.strlen.strlen_holds|].
  split; [exact m_find_closed|].
  exact (lib.U.Prog.check_absent.check_absent_holds FIND (lib.U.Prog.reac_segconf_role.reac_segconf_role_holds FIND)
           (lib.U.Prog.reac_segconf_ignored.reac_segconf_ignored_holds FIND)
           (lib.U.Prog.reac_segconf_model.reac_segconf_model_holds FIND)).
Qed.

Lemma reac_segconf_declared_closed : lib.U.Prog.reac_segconf_declared_c.reac_segconf_declared_contract.
Proof.
  exact (lib.U.Prog.reac_segconf_declared.reac_segconf_declared_holds
           (lib.U.Prog.reac_declared_vlan_split.reac_declared_vlan_split_holds
              (lib.U.Prog.strrchr.strrchr_holds lib.U.Prog.strlen.strlen_holds lib.U.Prog.memrchr.memrchr_holds)
              (lib.U.Prog.strtol_null.strtol_null_holds lib.U.Prog.__shlim.__shlim_holds
                 (lib.U.Prog.__intscan.__intscan_holds lib.U.Prog.__errno_location.__errno_location_holds
                    lib.U.Prog.__shlim.__shlim_holds))
              lib.U.Prog.strlen.strlen_holds lib.U.Prog.memcpy.memcpy_holds
              (lib.U.Prog.name_ok.name_ok_holds lib.U.Prog.isalnum.isalnum_holds))
           (lib.U.Prog.reac_declared_vlan_add.reac_declared_vlan_add_holds lib.U.Prog.strcmp.strcmp_holds
              lib.U.Prog.memset.memset_holds lib.U.Prog.strncpy.strncpy_holds)).
Qed.

Lemma K_V01_holds : lib.U.Prog.Seg.MainB.K_V01.
Proof.
  unfold lib.U.Prog.Seg.MainB.K_V01.
  split; [exact lib.U.Prog.memset.memset_holds|].
  split; [exact lib.U.Prog.memcpy.memcpy_holds|].
  split; [exact (lib.U.Prog.strrchr.strrchr_holds lib.U.Prog.strlen.strlen_holds lib.U.Prog.memrchr.memrchr_holds)|].
  split; [exact lib.U.Prog.strcmp.strcmp_holds|].
  split; [exact reac_segconf_declared_closed|].
  exact (lib.U.Prog.check_declared.check_declared_holds lib.U.Prog.strcmp.strcmp_holds).
Qed.

Lemma calloc_concrete_holds : lib.U.Prog.SegEnd.calloc_concrete.
Proof. intros fx rc. exact (@lib.U.CallocHolds.calloc_holds fx rc). Qed.

Lemma reac_segconf_parse_file_closed : lib.U.Prog.reac_segconf_parse_file_c.reac_segconf_parse_file_contract.
Proof.
  exact (lib.U.Prog.reac_segconf_parse_file.reac_segconf_parse_file_holds lib.U.Prog.snprintf.snprintf_holds
           lib.U.Prog.strchr.strchr_holds lib.U.Prog.strlen.strlen_holds lib.U.Prog.memcpy.memcpy_holds
           lib.U.Prog.r2_closed.trim_contract_closed lib.U.Prog.strspn.strspn_holds lib.U.Prog.r2_closed.refuse_contract_closed
           lib.U.Prog.strncasecmp.strncasecmp_holds lib.U.Prog.strcmp.strcmp_holds lib.U.Prog.memset.memset_holds
           (lib.U.Prog.strcasecmp.strcasecmp_holds lib.U.Prog.tolower.tolower_holds) lib.U.Prog.bcmp.bcmp_holds
           (lib.U.Prog.reac_box_catalogue_by_token.reac_box_catalogue_by_token_holds lib.U.Prog.strlen.strlen_holds
              (lib.U.Prog.fuzz_catalogue_row.fuzz_catalogue_row_holds lib.U.Prog.strlen.strlen_holds
                 lib.U.Prog.bcmp.bcmp_holds))
           lib.U.Prog.reac_box_catalogue.reac_box_catalogue_holds).
Qed.

Lemma K_L02_holds : lib.U.Prog.Seg.L02D.K_L02.
Proof.
  unfold lib.U.Prog.Seg.L02D.K_L02.
  split; [exact lib.U.Prog.memcpy.memcpy_holds|].
  split; [exact lib.U.Prog.snprintf_m.snprintf_m_holds|].
  split; [exact lib.U.Prog.memset.memset_holds|].
  split; [exact m_file_closed|].
  split; [exact m_refuse_closed|].
  split; [exact reac_segconf_parse_file_closed|].
  exact (lib.U.Prog.reac_segconf_parse.reac_segconf_parse_holds reac_segconf_parse_file_closed
           lib.U.Prog.r2_closed.cross_check_contract_closed).
Qed.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof.
  exact (lib.U.Prog.SegEnd.ubsan_halts_of_callees CPseg _ _ _ _ _
           lib.U.Prog.Seg.E01.seg_E01_holds lib.U.Prog.Seg.M01.seg_M01_holds lib.U.Prog.Seg.L01.seg_L01_holds
           lib.U.Prog.Seg.L02T.seg_L02 lib.U.Prog.Seg.L03.seg_L03_holds lib.U.Prog.Seg.M02.seg_M02 lib.U.Prog.Seg.V01.seg_V01
           lib.U.Prog.Seg.X01.seg_X01_holds
           K_M01_holds K_L01_holds K_L02_holds K_M02_holds K_V01_holds calloc_concrete_holds).
Qed.
